// Order records built from Kirschmer's OneClassGenera table (data/smalltypenumber.m),
// a string form for ideals, and the primes that the classification searches.
//
// Public: JoinStrings, CanonicalIdealKey, SortIdeals, RamifiedPrimes,
// RelevantPrimes, ClassOneOrderIndices, ClassOneOrder, ExplicitOrder,
// OrderCoordinates, OrderElement, ProjectiveRepresentative,
// PrimitiveRepresentative, TwoSidedGenerator, TraceNormForms.


OrderDataFormat := recformat<
    base_field,
    integer_ring,
    quaternion_algebra,
    quaternion_order,
    order_type,          // Kirschmer's code: 4 for maximal orders, 2 or more for Eichler orders
    principal_basis,     // a basis of O over R (R has class number one)
    coordinate_matrix,   // sends standard coordinates in B to principal-basis coordinates
    unit_group,          // O^* / R^*, with unit_map into the algebra
    unit_map,
    normalizer_group,    // N(O) / K^*, with normalizer_map into the algebra
    normalizer_map,
    two_sided_generators // CanonicalIdealKey(P) -> TwoSidedGenerator for ramified P
>;


// ---------------------------------------------------------------------------
// Ideals and primes
// ---------------------------------------------------------------------------

function JoinStrings(strings, delimiter)
    result := "";
    for i in [1..#strings] do
        result cat:= (i eq 1 select "" else delimiter) cat strings[i];
    end for;
    return result;
end function;


// "norm:[ entries of the Hermite-form basis matrix ]". Equal ideals give equal
// strings. The CSV files write ideals this way, and it serves as a cache key.
function CanonicalIdealKey(ideal_x)
    entries := [Sprint(c) : c in Eltseq(HermiteForm(BasisMatrix(ideal_x)))];
    return Sprintf("%o:[ %o ]", Norm(ideal_x), JoinStrings(entries, ", "));
end function;


function SortIdeals(ideals)
    return Sort(ideals, func<x, y | Norm(x) lt Norm(y) select -1 else Norm(x) gt Norm(y) select 1 else 0>);
end function;


function is_ramified(order_data, prime_ideal)
    return Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) ne 0;
end function;


function is_locally_maximal(order_data, prime_ideal)
    return Valuation(Discriminant(order_data`quaternion_order), prime_ideal) eq
           Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal);
end function;


// Sorted prime ideals dividing the discriminant of the algebra (not the order).
function RamifiedPrimes(order_data)
    return SortIdeals([factor[1] : factor in Factorization(Discriminant(order_data`quaternion_algebra))]);
end function;


// The ramified primes and the split primes of norm at most norm_bound: the primes
// that may divide a minimal ideal C. The bound is on the primes, not on exponents.
function RelevantPrimes(order_data, norm_bound)
    split_primes := norm_bound lt 2 select [] else [
        prime_ideal : prime_ideal in IdealsUpTo(norm_bound, order_data`integer_ring)
        | IsPrime(prime_ideal) and not is_ramified(order_data, prime_ideal)
    ];
    return SortIdeals(split_primes cat RamifiedPrimes(order_data));
end function;


// ---------------------------------------------------------------------------
// Orders and their elements
// ---------------------------------------------------------------------------

function OneClassEntry(index)
    if index lt 1 or index gt #OneClassGenera then
        error "The OneClassGenera index is out of range.";
    end if;
    return OneClassGenera[index];
end function;


// Table rows of maximal orders (type 4) with class number one: the paper's 49 orders.
function ClassOneOrderIndices()
    return [
        index : index in [1..#OneClassGenera]
        | OneClassGenera[index][6] eq 4 and OneClassGenera[index][7] eq 1
    ];
end function;


// Coordinates of element in the principal basis.
function OrderCoordinates(order_data, element)
    return Eltseq(Vector(Eltseq(order_data`quaternion_algebra!element)) * order_data`coordinate_matrix);
end function;


function OrderElement(order_data, coordinates)
    return order_data`quaternion_algebra!
        &+[coordinates[i] * order_data`principal_basis[i] : i in [1..4]];
end function;


// Scale so that the first nonzero coordinate is 1. Two elements have equal
// outputs exactly when they differ by a nonzero scalar.
function ProjectiveRepresentative(quaternion_algebra, element)
    coordinates := Eltseq(quaternion_algebra!element);
    pivot := [c : c in coordinates | c ne 0][1];
    return quaternion_algebra![c / pivot : c in coordinates];
end function;


// The scalar multiple of element whose principal-basis coordinates are integral
// and generate the unit ideal. It exists because R has class number one.
function PrimitiveRepresentative(order_data, element)
    R := order_data`integer_ring;
    coordinates := OrderCoordinates(order_data, element);
    _, generator := IsPrincipal(ideal<R | coordinates>);
    return OrderElement(order_data, [R!(c / generator) : c in coordinates]);
end function;


// The generator a of the two-sided ideal of O above the ramified prime P, as a
// primitive normalizer element with Nrd(a) R = P; false if there is none.
function TwoSidedGenerator(order_data, prime_ideal)
    key := CanonicalIdealKey(prime_ideal);
    return IsDefined(order_data`two_sided_generators, key)
        select order_data`two_sided_generators[key] else false;
end function;


// Trd(x) = sum t_i x_i and Nrd(x) = sum_{i <= j} c_ij x_i x_j for x = sum x_i b_i
// in the principal basis. Returns [t_i] and [<i, j, c_ij>], all in R.
function TraceNormForms(order_data)
    R := order_data`integer_ring;
    b := order_data`principal_basis;
    trace := [R!Trace(x) : x in b];
    norm := [<i, j, R!(i eq j select Norm(b[i]) else Trace(b[i] * Conjugate(b[j])))>
             : j in [i..4], i in [1..4]];
    return trace, norm;
end function;


function build_order_data(field, algebra, quaternion_order, order_type)
    R := RingOfIntegers(field);
    if ClassNumber(R) ne 1 then
        error "The base field must have class number one.";
    end if;

    basis := [];
    for term in PseudoBasis(quaternion_order) do
        _, generator := IsPrincipal(term[1]);
        Append(~basis, algebra!(term[2] * generator));
    end for;
    units, unit_map := UnitGroup(quaternion_order);
    normalizer, normalizer_map := Normalizer(quaternion_order);
    order_data := rec<OrderDataFormat |
        base_field := field,
        integer_ring := R,
        quaternion_algebra := algebra,
        quaternion_order := quaternion_order,
        order_type := order_type,
        principal_basis := basis,
        coordinate_matrix := Matrix([Eltseq(b) : b in basis])^-1,
        unit_group := units,
        unit_map := unit_map,
        normalizer_group := normalizer,
        normalizer_map := normalizer_map,
        two_sided_generators := AssociativeArray()
    >;

    // A primitive normalizer element whose reduced norm is a ramified prime P
    // generates the two-sided ideal above P.
    for g in normalizer do
        a := PrimitiveRepresentative(order_data, normalizer_map(g));
        P := Norm(a) * R;
        if IsPrime(P) and is_ramified(order_data, P) and
           not IsDefined(order_data`two_sided_generators, CanonicalIdealKey(P)) then
            order_data`two_sided_generators[CanonicalIdealKey(P)] := a;
        end if;
    end for;
    return order_data;
end function;


// Order record for row index of OneClassGenera.
function ClassOneOrder(index)
    entry := OneClassEntry(index);
    polynomial := Polynomial(entry[1]);
    field := Degree(polynomial) eq 1
        select RationalsAsNumberField()
        else NumberField(polynomial);
    algebra := QuaternionAlgebra<field | entry[3], entry[4]>;
    return build_order_data(field, algebra, Order(ChangeUniverse(entry[5], algebra)), entry[6]);
end function;


// Order record for a given quaternion order of class number one, such as the
// Hurwitz order. field must be a number field (RationalsAsNumberField() for Q).
function ExplicitOrder(field, algebra, quaternion_order : OrderType := 4)
    return build_order_data(field, algebra, quaternion_order, OrderType);
end function;
