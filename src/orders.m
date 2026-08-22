// Arithmetic input for the complementary-triples computations.
//
// `OneClassGenera` is supplied by data/smalltypenumber.m.  This file turns one
// table row (or an explicitly supplied quaternion order) into a uniform record
// containing the order, a principal basis, and exact representatives of its
// unit and normalizer quotients.  It also provides the ideal enumeration used
// by the classification and obstruction modules.


// index and label are provenance only; nothing in the pipeline reads them.
OrderDataFormat := recformat<
    index,
    label,
    base_field,
    integer_ring,
    quaternion_algebra,
    quaternion_order,
    order_discriminant,
    order_type,
    class_number,
    principal_basis,
    unit_group,
    unit_elements,
    unit_map,
    normalizer_group,
    normalizer_elements,
    normalizer_map
>;


// ---------------------------------------------------------------------------
// Table and coordinate helpers
// ---------------------------------------------------------------------------

function OneClassEntry(index)
    if Type(index) ne RngIntElt or index lt 1 or index gt #OneClassGenera then
        error "The OneClassGenera index is out of range.";
    end if;
    return OneClassGenera[index];
end function;


// The paper uses precisely the maximal orders of class number one in the
// external table; callers need not know the table's column numbering.
function ClassOneOrderIndices()
    return [
        index : index in [1..#OneClassGenera]
        | OneClassGenera[index][6] eq 4 and OneClassGenera[index][7] eq 1
    ];
end function;


procedure ord_require_class_number_one(integer_ring)
    if ClassNumber(integer_ring) ne 1 then
        error "The base field must have class number one.";
    end if;
end procedure;


function ord_principal_basis(quaternion_order)
    if Type(BaseRing(quaternion_order)) eq RngInt then
        return Basis(quaternion_order);
    end if;

    basis := [];
    for term in PseudoBasis(quaternion_order) do
        is_principal, generator := IsPrincipal(term[1]);
        if not is_principal then
            error "An order pseudo-basis coefficient is not principal.";
        end if;
        Append(~basis, term[2] * generator);
    end for;
    return basis;
end function;


function ord_coordinates_in_basis(field, algebra, basis, element)
    basis_matrix := Matrix(
        field,
        4,
        4,
        &cat([Eltseq(algebra!b) : b in basis])
    );
    vector := Vector(field, [field!c : c in Eltseq(algebra!element)]);
    is_consistent, coordinates := IsConsistent(basis_matrix, vector);
    if not is_consistent then
        error "The element is not in the span of the supplied order basis.";
    end if;
    return Eltseq(coordinates);
end function;


// Coordinates are row coordinates in the supplied four-element basis.
function OrderCoordinates(order_data, element)
    return ord_coordinates_in_basis(
        order_data`base_field,
        order_data`quaternion_algebra,
        order_data`principal_basis,
        element
    );
end function;


function OrderElement(order_data, coordinates)
    if #coordinates ne 4 then
        error "An order element requires four coordinates.";
    end if;
    return order_data`quaternion_algebra!
        &+[coordinates[i] * order_data`principal_basis[i] : i in [1..4]];
end function;


// A projective quaternion class is represented with first nonzero ambient
// coordinate equal to one.  This comparison is exact.
function ProjectiveRepresentative(quaternion_algebra, element)
    coordinates := Eltseq(quaternion_algebra!element);
    for coefficient in coordinates do
        if coefficient ne 0 then
            return quaternion_algebra![c / coefficient : c in coordinates];
        end if;
    end for;
    error "The zero quaternion has no projective class.";
end function;


// Scale a nonzero quaternion by a generator of its coordinate ideal so that
// its principal-basis coordinates become integral with trivial common ideal
// factor: a primitive integral representative of its projective class.  The
// class-number-one hypothesis makes the numerator and denominator ideals
// principal, so this normalization is exact and always succeeds.
function ord_integral_representative(field, integer_ring, algebra, basis, element)
    coordinates := ord_coordinates_in_basis(field, algebra, basis, element);
    coordinate_ideal := ideal<integer_ring | coordinates>;
    numerator := ideal<integer_ring | 1>;
    denominator := ideal<integer_ring | 1>;

    for factor in Factorization(coordinate_ideal) do
        if factor[2] gt 0 then
            numerator *:= factor[1]^factor[2];
        elif factor[2] lt 0 then
            denominator *:= factor[1]^(-factor[2]);
        end if;
    end for;

    numerator_is_principal, numerator_generator := IsPrincipal(numerator);
    denominator_is_principal, denominator_generator := IsPrincipal(denominator);
    if not numerator_is_principal or not denominator_is_principal then
        error "Cannot choose a primitive integral representative.";
    end if;

    scale := denominator_generator / numerator_generator;
    integral_coordinates := [];
    for coordinate in coordinates do
        scaled_coordinate := scale * coordinate;
        if not (scaled_coordinate in integer_ring) then
            error "Failed to clear a representative's denominators.";
        end if;
        Append(~integral_coordinates, integer_ring!scaled_coordinate);
    end for;
    return algebra!&+[integral_coordinates[i] * basis[i] : i in [1..4]];
end function;


function ord_primitive_integral_representative(order_data, element)
    return ord_integral_representative(
        order_data`base_field,
        order_data`integer_ring,
        order_data`quaternion_algebra,
        order_data`principal_basis,
        element
    );
end function;


function ord_group_data(order_data)
    units, unit_map := UnitGroup(order_data`quaternion_order);
    unit_elements := [];
    for unit in units do
        coordinates := OrderCoordinates(order_data, unit_map(unit));
        if exists{c : c in coordinates | not (c in order_data`integer_ring)} then
            error "A unit has nonintegral order coordinates.";
        end if;
        Append(
            ~unit_elements,
            OrderElement(order_data, [order_data`integer_ring!c : c in coordinates])
        );
    end for;

    normalizer, normalizer_map := Normalizer(order_data`quaternion_order);
    normalizer_elements := [
        ord_primitive_integral_representative(order_data, normalizer_map(g))
        : g in normalizer
    ];

    // Use the stored unit itself whenever a normalizer class is the same
    // projective class.  Downstream subgroup comparisons can then use exact
    // representatives rather than repeat scalar comparisons.
    unit_lookup := AssociativeArray();
    for unit in unit_elements do
        key := Sprint(Eltseq(ProjectiveRepresentative(order_data`quaternion_algebra, unit)));
        unit_lookup[key] := unit;
    end for;
    for i in [1..#normalizer_elements] do
        key := Sprint(Eltseq(ProjectiveRepresentative(
            order_data`quaternion_algebra,
            normalizer_elements[i]
        )));
        if IsDefined(unit_lookup, key) then
            normalizer_elements[i] := unit_lookup[key];
        end if;
    end for;

    normalizer_lookup := AssociativeArray();
    for element in normalizer_elements do
        key := Sprint(Eltseq(ProjectiveRepresentative(order_data`quaternion_algebra, element)));
        normalizer_lookup[key] := true;
    end for;
    for unit in unit_elements do
        key := Sprint(Eltseq(ProjectiveRepresentative(order_data`quaternion_algebra, unit)));
        if not IsDefined(normalizer_lookup, key) then
            error "The projective unit group is not contained in the computed normalizer.";
        end if;
    end for;

    return units, unit_elements, unit_map,
           normalizer, normalizer_elements, normalizer_map;
end function;


function ord_build_order_data(
    index,
    field,
    algebra,
    quaternion_order,
    order_type,
    class_number,
    label
)
    integers := RingOfIntegers(field);
    ord_require_class_number_one(integers);
    basis := ord_principal_basis(quaternion_order);

    // The group helper needs only the arithmetic fields and basis, so create
    // this record first and then return the completed immutable record.
    partial := rec<OrderDataFormat |
        index := index,
        label := label,
        base_field := field,
        integer_ring := integers,
        quaternion_algebra := algebra,
        quaternion_order := quaternion_order,
        order_discriminant := Discriminant(quaternion_order),
        order_type := order_type,
        class_number := class_number,
        principal_basis := basis
    >;
    units, unit_elements, unit_map,
    normalizer, normalizer_elements, normalizer_map := ord_group_data(partial);

    return rec<OrderDataFormat |
        index := index,
        label := label,
        base_field := field,
        integer_ring := integers,
        quaternion_algebra := algebra,
        quaternion_order := quaternion_order,
        order_discriminant := Discriminant(quaternion_order),
        order_type := order_type,
        class_number := class_number,
        principal_basis := basis,
        unit_group := units,
        unit_elements := unit_elements,
        unit_map := unit_map,
        normalizer_group := normalizer,
        normalizer_elements := normalizer_elements,
        normalizer_map := normalizer_map
    >;
end function;


// Construct the order stored in OneClassGenera[index].
function ClassOneOrder(index)
    entry := OneClassEntry(index);
    polynomial := Polynomial(entry[1]);
    field := (Degree(polynomial) eq 1)
        select RationalsAsNumberField()
        else NumberField(polynomial);
    algebra := QuaternionAlgebra<field | entry[3], entry[4]>;
    quaternion_order := Order(ChangeUniverse(entry[5], algebra));
    return ord_build_order_data(
        index,
        field,
        algebra,
        quaternion_order,
        entry[6],
        entry[7],
        "main"
    );
end function;


// Construct the same record for a caller-supplied quaternion order.
function ExplicitOrder(
    field,
    algebra,
    quaternion_order :
    Index := 0,
    Label := "explicit",
    OrderType := 4,
    ClassNumber := 0
)
    if Type(field) ne FldNum and Type(field) ne FldRat then
        error "The base field must be a number field or the rational field.";
    end if;
    if ClassNumber eq 0 then
        ClassNumber := #RightIdealClasses(quaternion_order);
    end if;
    return ord_build_order_data(
        Index,
        field,
        algebra,
        quaternion_order,
        OrderType,
        ClassNumber,
        Label
    );
end function;


// ---------------------------------------------------------------------------
// Canonical ideals and relevant primes
// ---------------------------------------------------------------------------

// The Hermite-normal-form lattice basis is intrinsic to the ideal.  In
// particular, unlike a principal generator returned by IsPrincipal, it does
// not depend on Magma's randomized unit choices.
function CanonicalIdealKey(ideal_x)
    if Type(ideal_x) eq RngInt then
        // An ideal of Z serializes as "n:[ n ]", the same shape a degree-one
        // number field produces from its 1x1 Hermite basis, so keys agree
        // between the RngInt and RationalsAsNumberField coordinate types.
        return Sprintf("%o:[ %o ]", Norm(ideal_x), Norm(ideal_x));
    end if;
    lattice_basis := HermiteForm(BasisMatrix(ideal_x));
    return Sprintf("%o:%o", Norm(ideal_x), Eltseq(lattice_basis));
end function;


function ord_ideal_less_than(left, right)
    if Norm(left) ne Norm(right) then
        return Norm(left) lt Norm(right);
    end if;
    return CanonicalIdealKey(left) lt CanonicalIdealKey(right);
end function;


// Sort ideals into the canonical order: by norm, with ties broken by the
// canonical key.  Every serialized ideal list passes through this order, so
// the published CSV rows are identical across runs and worker processes.
function SortIdeals(ideals)
    remaining := ideals;
    result := [];
    while #remaining gt 0 do
        least := 1;
        for i in [2..#remaining] do
            if ord_ideal_less_than(remaining[i], remaining[least]) then
                least := i;
            end if;
        end for;
        Append(~result, remaining[least]);
        Remove(~remaining, least);
    end while;
    return result;
end function;


procedure AppendIdeal(~ideals, ideal_x)
    key := CanonicalIdealKey(ideal_x);
    if forall{existing : existing in ideals | CanonicalIdealKey(existing) ne key} then
        Append(~ideals, ideal_x);
    end if;
end procedure;


// The finite primes at which the quaternion algebra ramifies: the prime
// divisors of the algebra (not order) discriminant, in canonical order.
// Over Z the integer prime factors are converted to ideals so both base
// rings return ideal sequences.
function RamifiedPrimes(order_data)
    discriminant := Discriminant(order_data`quaternion_algebra);
    integers := order_data`integer_ring;
    if Type(integers) eq RngInt then
        return SortIdeals([
            ideal<integers | factor[1]> : factor in Factorization(discriminant)
        ]);
    end if;
    return SortIdeals([factor[1] : factor in Factorization(discriminant)]);
end function;


// All finite split primes with norm at most norm_bound.  This is the finite
// prime set required by the paper's minimal-ideal classification.
function RelevantSplitPrimes(order_data, norm_bound)
    if Type(norm_bound) ne RngIntElt or norm_bound lt 0 then
        error "The norm bound must be a nonnegative integer.";
    end if;

    integers := order_data`integer_ring;
    discriminant := Discriminant(order_data`quaternion_algebra);
    primes := [];
    if Type(integers) eq RngInt then
        for p in [2..norm_bound] do
            if IsPrime(p) and discriminant mod p ne 0 then
                Append(~primes, ideal<integers | p>);
            end if;
        end for;
    elif norm_bound ge 2 then
        for prime in IdealsUpTo(norm_bound, integers) do
            if IsPrime(prime) and Valuation(discriminant, prime) eq 0 then
                Append(~primes, prime);
            end if;
        end for;
    end if;
    return SortIdeals(primes);
end function;


// Ramified primes together with the split primes of norm at most norm_bound:
// the finite candidate prime support over which the classification searches
// its divisibility poset.  The bound limits primes, not prime-power
// exponents.
function RelevantPrimes(order_data, norm_bound)
    primes := RelevantSplitPrimes(order_data, norm_bound);
    for prime in RamifiedPrimes(order_data) do
        AppendIdeal(~primes, prime);
    end for;
    return SortIdeals(primes);
end function;


// ---------------------------------------------------------------------------
// Private vocabulary shared by the other four modules
// ---------------------------------------------------------------------------

function normalize_quaternion_element(algebra, element)
    return ProjectiveRepresentative(algebra, element);
end function;

function ramified_primes(order_data)
    return RamifiedPrimes(order_data);
end function;
