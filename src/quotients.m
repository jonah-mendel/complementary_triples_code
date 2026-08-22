// ============================================================================
// Exact projective unit groups modulo prime powers.
//
// Public API:
//     FiniteQuotient(order_data, prime_ideal, exponent : Print := 0)
//
// FiniteQuotient builds G = (O / P^k O)^* / (R / P^k)^* as an exact
// permutation group, choosing among four models: the natural PGL(2, F)
// action on P^1(F) at split locally maximal primes with k = 1, a kernel
// lift of the prime-level classes at split locally maximal primes with
// k = 2, an enumeration of unit points of P^3(F) at ramified locally
// maximal primes with k = 1, and full enumeration of (O / P^k O)^*
// otherwise.  Each model is certified against exact group-order formulas.
//
// For Eichler orders (order_type >= 2) the returned record also carries
// the image of the projective normalizer: inside G itself at split
// localization primes, and inside the doubled extension W = <G, t> with
// t^2 = [a^2] at ramified primes, where a is a normalizer element of odd
// P-valuation.
// ============================================================================
// Record storing one projective unit-group computation modulo P^k.
projective_unit_group_format := recformat<
    order_data,
    modulus_ideal,
    reduced_base_ring,
    reduced_algebra,
    reduction_map,
    reduced_units,
    scalars,
    reduced_unit_membership,
    class_representatives,
    class_index_by_key,
    class_key_data,
    reduced_to_permutation,
    permutation_to_reduced,
    projective_unit_group,
    normalizer_image_defined,
    normalizer_ambient_group,
    normalizer_image_map,
    ramified_extension_defined,
    ramified_generator,
    ramified_generator_permutation
>;


computed_complement_class_format := recformat<
    subgroup
>;


// Per-model data used to name the projective class of a reduced unit.  The
// mode field selects the model: "natural_split_prime" replaces class keys
// entirely by the PGL(2, F) action on P^1(F), and "split_prime_square" names
// a class by its prime-level class index together with a canonical kernel
// tuple.  The generic and ramified models pass class_key_data = false and
// key classes by canonical scalar-orbit representatives.
projective_class_key_data_format := recformat<
    mode,
    reduced_algebra,
    associative_algebra,
    split_map,
    split_basis_matrix,
    projective_group,
    projective_points,
    projective_point_index_by_key,
    order_data,
    prime_reduced_algebra,
    prime_reduction_map,
    reduction_map,
    prime_scalar_units,
    prime_scalars,
    prime_class_index_by_key,
    lifted_prime_representatives,
    lifted_prime_representative_inverses,
    scalar_fibers,
    scalar_kernel_tuples,
    reduced_identity
>;


// Unit-membership test data for O / P^k O.  Mode "explicit" consults the
// list of enumerated reduced units, "is_unit" defers to Magma over the
// residue field, and "prime_lift" tests the reduction modulo P, which
// suffices because the kernel ideal P O / P^k O is nilpotent.
reduced_unit_membership_format := recformat<
    mode,
    lookup,
    order_data,
    prime_reduced_algebra,
    prime_reduction_map,
    reduction_map,
    prime_unit_lookup
>;


// Validate the Print parameter shared by the projective-group routines.
function validate_print_level(Print)
    if Type(Print) ne RngIntElt or Print lt 0 or Print gt 2 then
        error "Print must be an integer in {0,1,2}.";
    end if;

    return Print;
end function;


// Test whether top-level diagnostics should be printed.
function print_is_concise(Print)
    return Print ge 1;
end function;


// Test whether detailed diagnostics should be printed.
function print_is_detailed(Print)
    return Print ge 2;
end function;


// Summarize an ideal by a generator when available and by its norm.
function ideal_summary(label, ideal_x)
    has_generator, generator := IsPrincipal(ideal_x);
    if has_generator then
        return Sprintf("%o_gen=%o | %o_norm=%o", label, generator, label, Norm(ideal_x));
    end if;

    return Sprintf("%o_ideal=%o | %o_norm=%o", label, ideal_x, label, Norm(ideal_x));
end function;


// Normalize the prime input to an actual prime ideal of the integer ring.
function normalize_prime_ideal(integer_ring, prime_data)
    if Type(prime_data) eq RngOrdIdl then
        prime_ideal := ideal<integer_ring | Generators(prime_data)>;
    else
        prime_ideal := ideal<integer_ring | prime_data>;
    end if;

    if not IsPrime(prime_ideal) then
        error "prime_ideal must be a prime ideal of the integer ring.";
    end if;

    return prime_ideal;
end function;


// Test whether O is locally maximal at the given prime.
function order_is_locally_maximal_at_prime(order_data, prime_ideal)
    prime_ideal := normalize_prime_ideal(order_data`integer_ring, prime_ideal);

    return Valuation(order_data`order_discriminant, prime_ideal) eq
           Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal);
end function;


// Exact size of (R / P^k)^*.
function expected_scalar_unit_order(prime_ideal, k)
    if Type(k) ne RngIntElt or k lt 1 then
        error "k must be an integer >= 1.";
    end if;

    residue_norm := Integers()!Norm(prime_ideal);
    return residue_norm^k - residue_norm^(k - 1);
end function;


// Exact size of G(R / P^k) = (O / P^k O)^* / (R / P^k)^* when O_P is maximal.
function expected_projective_group_order_data(order_data, prime_ideal, k)
    if Type(k) ne RngIntElt or k lt 1 then
        error "k must be an integer >= 1.";
    end if;

    prime_ideal := normalize_prime_ideal(order_data`integer_ring, prime_ideal);
    local_maximal_at_prime := order_is_locally_maximal_at_prime(order_data, prime_ideal);
    prime_ramified_in_algebra :=
        Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) ne 0;

    if not local_maximal_at_prime then
        return false, 0, "unknown";
    end if;

    residue_norm := Integers()!Norm(prime_ideal);
    if prime_ramified_in_algebra then
        return true,
               residue_norm^(3 * k - 1) * (residue_norm + 1),
               "ramified_maximal";
    end if;

    return true,
           residue_norm^(3 * k - 2) * (residue_norm^2 - 1),
           "split_maximal";
end function;


// Recover the underlying prime and exponent from a prime-power ideal.
function prime_power_data_from_ideal(modulus_ideal)
    factorization := Factorization(modulus_ideal);

    if #factorization ne 1 then
        error "modulus_ideal must be a prime power.";
    end if;

    return factorization[1][1], factorization[1][2];
end function;


// Build the reduced algebra O / P^k O together with the base-ring reduction map.
function build_reduced_algebra(order_data, modulus_ideal)
    integer_ring := order_data`integer_ring;
    principal_basis := order_data`principal_basis;
    _, k := prime_power_data_from_ideal(modulus_ideal);

    // At a prime modulus we can work over the residue field; for higher powers
    // we need the quotient ring R / P^k instead.
    if k eq 1 then
        reduced_base_ring, reduction_map := ResidueClassField(modulus_ideal);
    else
        reduced_base_ring, reduction_map := quo<integer_ring | modulus_ideal>;
    end if;

    multiplication_table := [
        OrderCoordinates(order_data, principal_basis[i] * principal_basis[j]) : i, j in [1..4]
    ];

    reduced_algebra := Algebra<reduced_base_ring, 4 | [[reduction_map(c) : c in row] : row in multiplication_table]>;
    return reduced_algebra, reduced_base_ring, reduction_map;
end function;


// Reduce the identity element of the order to the reduced algebra.
function reduced_order_identity(order_data, reduction_map, reduced_algebra)
    integer_ring := order_data`integer_ring;
    identity_coordinates := OrderCoordinates(order_data, order_data`quaternion_order!1);
    reduced_coordinates := [];

    for coefficient in identity_coordinates do
        if not (coefficient in integer_ring) then
            error "The identity element does not have integral principal-basis coordinates.";
        end if;

        Append(~reduced_coordinates, reduction_map(integer_ring!coefficient));
    end for;

    return reduced_algebra!reduced_coordinates;
end function;





// Build a lookup keyed by coordinate sequence for elements of a reduced algebra.
function element_sequence_lookup(elements)
    lookup := AssociativeArray();

    for element_x in elements do
        lookup[Eltseq(element_x)] := true;
    end for;

    return lookup;
end function;


// Reduce an element of O / P^k O to O / P O, using integral coordinate lifts.
function reduce_prime_power_element_to_prime(
    order_data,
    prime_reduced_algebra,
    prime_reduction_map,
    reduction_map,
    lifted_element
)
    integer_ring := order_data`integer_ring;
    prime_tuple := [];

    for coordinate in Eltseq(lifted_element) do
        integral_lift := integer_ring!(coordinate @@ reduction_map);
        Append(~prime_tuple, prime_reduction_map(integral_lift));
    end for;

    return prime_reduced_algebra!prime_tuple;
end function;


// Reduce an element of R / P^k to R / P.
function reduce_prime_power_scalar_to_prime(integer_ring, prime_reduction_map, reduction_map, lifted_scalar)
    integral_lift := integer_ring!(lifted_scalar @@ reduction_map);
    return prime_reduction_map(integral_lift);
end function;








// Build fibers of R / P^k over R / P.  This is used to lift units modulo P
// without scanning every element of O / P^k O.
function scalar_prime_reduction_fibers(
    integer_ring,
    reduced_base_ring,
    reduction_map,
    prime_reduced_base_ring,
    prime_reduction_map
)
    fibers := AssociativeArray();

    for prime_scalar in prime_reduced_base_ring do
        fibers[Sprint(Eltseq(prime_scalar))] := [];
    end for;

    for scalar in reduced_base_ring do
        prime_scalar := reduce_prime_power_scalar_to_prime(
            integer_ring,
            prime_reduction_map,
            reduction_map,
            scalar
        );
        key := Sprint(Eltseq(prime_scalar));
        fiber := fibers[key];
        Append(~fiber, scalar);
        fibers[key] := fiber;
    end for;

    return fibers;
end function;


function scalar_prime_fiber(fibers, prime_scalar)
    key := Sprint(Eltseq(prime_scalar));

    if not IsDefined(fibers, key) then
        error "Missing scalar reduction fiber.";
    end if;

    return fibers[key];
end function;


procedure append_lifted_algebra_elements(
    reduced_algebra,
    coordinate_fibers,
    coordinate_index,
    current_coordinates,
    ~lifted_elements
)
    if coordinate_index gt #coordinate_fibers then
        Append(~lifted_elements, reduced_algebra!current_coordinates);
        return;
    end if;

    for coordinate in coordinate_fibers[coordinate_index] do
        append_lifted_algebra_elements(
            reduced_algebra,
            coordinate_fibers,
            coordinate_index + 1,
            current_coordinates cat [coordinate],
            ~lifted_elements
        );
    end for;
end procedure;


procedure append_lifts_of_prime_unit(
    reduced_algebra,
    scalar_fibers,
    prime_unit,
    ~lifted_units
)
    coordinate_fibers := [
        scalar_prime_fiber(scalar_fibers, coordinate) :
        coordinate in Eltseq(prime_unit)
    ];

    append_lifted_algebra_elements(
        reduced_algebra,
        coordinate_fibers,
        1,
        [],
        ~lifted_units
    );
end procedure;


function lifted_prime_power_units(
    reduced_algebra,
    scalar_fibers,
    prime_reduced_units
)
    lifted_units := [];

    for prime_unit in prime_reduced_units do
        append_lifts_of_prime_unit(
            reduced_algebra,
            scalar_fibers,
            prime_unit,
            ~lifted_units
        );
    end for;

    return lifted_units;
end function;





function lifted_prime_power_scalar_units(
    scalar_fibers,
    prime_reduced_base_ring,
    prime_reduced_zero
)
    scalar_units := [];

    for prime_scalar in prime_reduced_base_ring do
        if prime_scalar eq prime_reduced_zero then
            continue;
        end if;

        scalar_units cat:= scalar_prime_fiber(scalar_fibers, prime_scalar);
    end for;

    return scalar_units;
end function;


function lift_prime_reduced_element_to_prime_square(reduced_algebra, scalar_fibers, prime_element)
    return reduced_algebra![
        scalar_prime_fiber(scalar_fibers, coordinate)[1] :
        coordinate in Eltseq(prime_element)
    ];
end function;


// Invert a lifted unit modulo P^2 by one nilpotent correction: if y lifts
// the inverse of x modulo P, then e := y x - 1 lies in P O / P^2 O, so
// e^2 = 0 and (1 - e) y is the exact inverse of x modulo P^2.
function lifted_prime_square_inverse(
    reduced_algebra,
    reduced_identity,
    scalar_fibers,
    lifted_element,
    prime_element
)
    prime_inverse_lift := lift_prime_reduced_element_to_prime_square(
        reduced_algebra,
        scalar_fibers,
        prime_element^-1
    );
    left_error := prime_inverse_lift * lifted_element - reduced_identity;

    return (reduced_identity - left_error) * prime_inverse_lift;
end function;


function tuple_key(tuple_x)
    return Sprint([Eltseq(entry) : entry in tuple_x]);
end function;


function canonical_scalar_kernel_tuple(tuple_x, scalar_kernel_tuples)
    is_first := true;
    best_tuple := tuple_x;
    best_key := "";

    for scalar_tuple in scalar_kernel_tuples do
        candidate := [tuple_x[i] + scalar_tuple[i] : i in [1..#tuple_x]];
        key := tuple_key(candidate);

        if is_first or key lt best_key then
            best_tuple := candidate;
            best_key := key;
            is_first := false;
        end if;
    end for;

    return best_tuple, best_key;
end function;


procedure append_kernel_tuples(
    zero_fiber,
    tuple_length,
    current_tuple,
    ~kernel_tuples
)
    if #current_tuple eq tuple_length then
        Append(~kernel_tuples, current_tuple);
        return;
    end if;

    for entry in zero_fiber do
        append_kernel_tuples(
            zero_fiber,
            tuple_length,
            current_tuple cat [entry],
            ~kernel_tuples
        );
    end for;
end procedure;


function scalar_kernel_tuples_for_prime_square(reduced_identity, zero_fiber)
    identity_coordinates := Eltseq(reduced_identity);

    return [
        [scalar * identity_coordinates[i] : i in [1..4]] :
        scalar in zero_fiber
    ];
end function;


// The kernel of G(R / P^2) -> G(R / P) consists of the classes of 1 + n
// with n in P O / P^2 O.  Enumerate one coordinate tuple per class by
// canonicalizing the N(P)^4 kernel tuples modulo the N(P) scalar tuples
// lambda * 1 with lambda in P / P^2, leaving N(P)^3 projective classes.
function projective_kernel_tuples_for_prime_square(reduced_identity, zero_fiber)
    all_tuples := [];
    append_kernel_tuples(zero_fiber, 4, [], ~all_tuples);
    scalar_kernel_tuples := scalar_kernel_tuples_for_prime_square(
        reduced_identity,
        zero_fiber
    );
    kernel_tuple_lookup := AssociativeArray();
    kernel_tuples := [];

    for tuple_x in all_tuples do
        canonical_tuple, canonical_key := canonical_scalar_kernel_tuple(
            tuple_x,
            scalar_kernel_tuples
        );

        if not IsDefined(kernel_tuple_lookup, canonical_key) then
            kernel_tuple_lookup[canonical_key] := true;
            Append(~kernel_tuples, canonical_tuple);
        end if;
    end for;

    return kernel_tuples;
end function;


// Use IsUnit in the field-quotient case and nilpotent lifting for higher powers.
function reduced_unit_data(
    order_data,
    modulus_ideal,
    reduced_base_ring,
    reduced_algebra,
    reduction_map :
    Print := 0,
    expected_scalar_unit_order := 0
)
    Print := validate_print_level(Print);
    prime_ideal, k := prime_power_data_from_ideal(modulus_ideal);
    one_algebra := reduced_order_identity(order_data, reduction_map, reduced_algebra);

    if k eq 1 then
        reduced_units := [u : u in reduced_algebra | IsUnit(u)];
        scalar_units := [a : a in reduced_base_ring | IsUnit(a)];
        if expected_scalar_unit_order ne 0 and #scalar_units ne expected_scalar_unit_order then
            error "Scalar-unit count did not match the expected size of (R / P^k)^*.";
        end if;
        scalars := {a * one_algebra : a in scalar_units};
        return reduced_units, scalar_units, scalars;
    end if;

    // The ideal P O / P^k O is nilpotent, so an element of O / P^k O is a
    // unit if and only if its reduction modulo P is a unit.
    prime_reduced_algebra, prime_reduced_base_ring, prime_reduction_map :=
        build_reduced_algebra(order_data, prime_ideal);
    prime_reduced_units := [u : u in prime_reduced_algebra | IsUnit(u)];

    scalar_fibers := scalar_prime_reduction_fibers(
        order_data`integer_ring,
        reduced_base_ring,
        reduction_map,
        prime_reduced_base_ring,
        prime_reduction_map
    );
    reduced_units := lifted_prime_power_units(
        reduced_algebra,
        scalar_fibers,
        prime_reduced_units
    );
    scalar_units := lifted_prime_power_scalar_units(
        scalar_fibers,
        prime_reduced_base_ring,
        prime_reduced_base_ring!0
    );
    if expected_scalar_unit_order ne 0 and #scalar_units ne expected_scalar_unit_order then
        error "Scalar-unit count did not match the expected size of (R / P^k)^*.";
    end if;
    scalars := {a * one_algebra : a in scalar_units};

    return reduced_units, scalar_units, scalars;
end function;


// Choose a canonical representative for the scalar orbit of a reduced unit.
function canonical_orbit_representative(x, scalars)
    is_first := true;
    best_key := "";

    for scalar in scalars do
        representative := Eltseq(x * scalar);
        key := Sprint(representative);

        if is_first or key lt best_key then
            best_rep := representative;
            best_key := key;
            is_first := false;
        end if;
    end for;

    if is_first then
        error "Scalar orbit is empty.";
    end if;

    return best_rep;
end function;


// The scalar action is central, so in an order basis it just scales every
// coefficient.  This avoids a full quotient-algebra multiplication in the
// large split-prime-square class construction.
function canonical_orbit_representative_from_scalar_units(x, scalar_units)
    coordinates := Eltseq(x);
    is_first := true;
    best_key := "";

    for scalar in scalar_units do
        representative := [coordinate * scalar : coordinate in coordinates];
        key := Sprint(representative);

        if is_first or key lt best_key then
            best_rep := representative;
            best_key := key;
            is_first := false;
        end if;
    end for;

    if is_first then
        error "Scalar orbit is empty.";
    end if;

    return best_rep;
end function;


function scalar_multiple_coordinates(coordinates, scalar)
    return [coordinate * scalar : coordinate in coordinates];
end function;


// Name the projective class of a unit u modulo P^2 by the serialized pair
// "prime_class_index|kernel_key": scale u so that its reduction modulo P is
// the stored canonical prime-level representative, multiply by the stored
// lifted inverse of that representative, and read off the canonical kernel
// tuple of the remaining class 1 + n with n in P O / P^2 O.
function split_prime_square_projective_class_key(reduced_element, class_key_data)
    prime_reduced_element := reduce_prime_power_element_to_prime(
        class_key_data`order_data,
        class_key_data`prime_reduced_algebra,
        class_key_data`prime_reduction_map,
        class_key_data`reduction_map,
        reduced_element
    );
    prime_coordinates := Eltseq(prime_reduced_element);
    prime_representative := canonical_orbit_representative_from_scalar_units(
        prime_reduced_element,
        class_key_data`prime_scalar_units
    );
    prime_key := Sprint(prime_representative);

    if not IsDefined(class_key_data`prime_class_index_by_key, prime_key) then
        error "The prime-level projective class was not found in the split prime-square model.";
    end if;

    prime_class_index := class_key_data`prime_class_index_by_key[prime_key];
    scalar_to_prime_representative := false;

    for scalar in class_key_data`prime_scalar_units do
        if scalar_multiple_coordinates(prime_coordinates, scalar) eq prime_representative then
            scalar_to_prime_representative := scalar;
            break;
        end if;
    end for;

    if Type(scalar_to_prime_representative) eq BoolElt then
        error "Could not normalize the prime-level representative by a scalar.";
    end if;

    lifted_scalar := scalar_prime_fiber(
        class_key_data`scalar_fibers,
        scalar_to_prime_representative
    )[1];
    normalized_element := Parent(reduced_element)!scalar_multiple_coordinates(
        Eltseq(reduced_element),
        lifted_scalar
    );
    kernel_unit :=
        class_key_data`lifted_prime_representative_inverses[prime_class_index] *
        normalized_element;
    kernel_tuple := Eltseq(kernel_unit - class_key_data`reduced_identity);
    canonical_tuple, canonical_key := canonical_scalar_kernel_tuple(
        kernel_tuple,
        class_key_data`scalar_kernel_tuples
    );

    return Sprintf("%o|%o", prime_class_index, canonical_key);
end function;


// Canonical key naming the scalar class of a reduced unit, dispatching on
// the class-key model.  Two reduced units receive equal keys exactly when
// they differ by a scalar in (R / P^k)^*.
function projective_class_key(reduced_element, scalars, class_key_data)
    if Type(class_key_data) eq Rec and assigned class_key_data`mode then
        if class_key_data`mode eq "split_prime_square" then
            return split_prime_square_projective_class_key(reduced_element, class_key_data);
        end if;

        if class_key_data`mode eq "natural_split_prime" then
            error "The natural split-prime model uses projective permutations, not class keys.";
        end if;

        error Sprintf("Unknown projective class-key mode %o.", class_key_data`mode);
    end if;

    return Sprint(canonical_orbit_representative(reduced_element, scalars));
end function;





// A deterministic priority order.  Algorithms using it continue through the
// remaining indices whenever the exact target has not yet been certified.
function priority_index_order(num_items)
    if num_items le 1 then
        return [];
    end if;

    max_base := Max(2, Floor(Log(2, num_items)));
    priority_indices := [];
    used_indices := AssociativeArray();

    for base in Reverse([2..max_base]) do
        index := base;
        while index le num_items do
            if not IsDefined(used_indices, index) then
                used_indices[index] := true;
                Append(~priority_indices, index);
            end if;
            index *:= base;
        end while;
    end for;

    return priority_indices;
end function;


// Enumerate every projective class, visiting a deterministic priority order
// first and then every remaining reduced unit when needed.
function projective_class_data(reduced_units, scalars, num_classes : Print := 0)
    Print := validate_print_level(Print);
    total_units := #reduced_units;
    priority_indices := priority_index_order(total_units);
    priority_index_set := AssociativeArray();
    class_representatives := [];
    class_index_by_key := AssociativeArray();
    for index in priority_indices do
        priority_index_set[index] := true;
        representative := canonical_orbit_representative(reduced_units[index], scalars);
        representative_key := Sprint(representative);

        if not IsDefined(class_index_by_key, representative_key) then
            Append(~class_representatives, representative);
            class_index_by_key[representative_key] := #class_representatives;
        end if;

        if #class_representatives eq num_classes then
            break;
        end if;
    end for;

    if #class_representatives ne num_classes then
        if print_is_detailed(Print) then
            print "[PUG classes] continuing through remaining reduced units";
        end if;

        for index in [1..total_units] do
            if IsDefined(priority_index_set, index) then
                continue;
            end if;

            representative := canonical_orbit_representative(reduced_units[index], scalars);
            representative_key := Sprint(representative);

            if not IsDefined(class_index_by_key, representative_key) then
                Append(~class_representatives, representative);
                class_index_by_key[representative_key] := #class_representatives;
            end if;

            if #class_representatives eq num_classes then
                break;
            end if;
        end for;
    elif print_is_detailed(Print) then
        print "[PUG classes] exact class count certified in priority order";
    end if;

    if #class_representatives ne num_classes then
        error Sprintf("Found %o projective classes, expected %o.",
                      #class_representatives, num_classes);
    end if;
    return class_representatives, class_index_by_key;
end function;


// At a ramified locally maximal prime with k = 1, enumerate the projective
// unit classes as unit points of P^3(F): each scalar orbit of reduced units
// contains exactly one pivoted point representative, so visiting the
// N^3 + N^2 + N + 1 points and keeping the units lists every class once
// without scanning all of (O / P O)^*.
function projective_point_class_data(
    reduced_algebra,
    reduced_base_ring,
    scalars,
    num_classes :
    Print := 0
)
    Print := validate_print_level(Print);
    base_elements := [entry : entry in reduced_base_ring];
    zero := reduced_base_ring!0;
    one := reduced_base_ring!1;
    total_projective_points := &+[ (#base_elements)^(4 - pivot_index) : pivot_index in [1..4] ];
    class_representatives := [];
    class_index_by_key := AssociativeArray();

    for pivot_index in [1..4] do
        suffix_tuples := [];
        append_kernel_tuples(base_elements, 4 - pivot_index, [], ~suffix_tuples);

        for suffix_tuple in suffix_tuples do
            coordinates := [zero : i in [1..4]];
            coordinates[pivot_index] := one;

            for j in [1..#suffix_tuple] do
                coordinates[pivot_index + j] := suffix_tuple[j];
            end for;

            reduced_element := reduced_algebra!coordinates;

            if IsUnit(reduced_element) then
                representative := canonical_orbit_representative(reduced_element, scalars);
                representative_key := projective_class_key(reduced_element, scalars, false);

                if not IsDefined(class_index_by_key, representative_key) then
                    Append(~class_representatives, representative);
                    class_index_by_key[representative_key] := #class_representatives;
                end if;
            end if;

        end for;
    end for;

    if #class_representatives ne num_classes then
        error Sprintf(
            "Projective-point class construction found %o classes, expected %o.",
            #class_representatives,
            num_classes
        );
    end if;

    return class_representatives, class_index_by_key;
end function;


// Canonical key for a point of projective space, using its first nonzero
// coordinate as pivot.
function natural_projective_point_key(point)
    coordinates := Eltseq(point);

    for coordinate in coordinates do
        if coordinate ne 0 then
            return Sprint([entry / coordinate : entry in coordinates]);
        end if;
    end for;

    error "The zero vector is not a projective point.";
end function;


// Natural action of a split quaternion unit on P^1(F).  Magma's PGL(2,F)
// already uses this degree-(#F+1) action.
function natural_split_prime_action_permutation(reduced_element, class_key_data)
    if Type(class_key_data) ne Rec or
       not assigned class_key_data`mode or
       class_key_data`mode ne "natural_split_prime" then
        error "Natural split-prime action data is required.";
    end if;

    associative_element := class_key_data`associative_algebra!
        (class_key_data`reduced_algebra!reduced_element);
    matrix_element := class_key_data`split_map(associative_element);
    permutation_entries := [];

    for point in class_key_data`projective_points do
        image_key := natural_projective_point_key(point * matrix_element);

        if not IsDefined(class_key_data`projective_point_index_by_key, image_key) then
            error "The split matrix action did not preserve the projective line.";
        end if;

        Append(
            ~permutation_entries,
            class_key_data`projective_point_index_by_key[image_key]
        );
    end for;

    permutation := Sym(#class_key_data`projective_points)!permutation_entries;
    if not (permutation in class_key_data`projective_group) then
        error "A split matrix did not induce an element of PGL(2,F).";
    end if;

    return class_key_data`projective_group!permutation;
end function;


// Recover a projective matrix from the images of [1,0], [0,1], and [1,1],
// then express it in the reduced quaternion basis.  This is the inverse of
// the natural action on projective classes, not a choice among scalar lifts.
function natural_split_prime_reduced_representative_from_data(
    class_key_data,
    group_element
)
    if Type(class_key_data) ne Rec or
       not assigned class_key_data`mode or
       class_key_data`mode ne "natural_split_prime" then
        error "Natural split-prime action data is required.";
    end if;

    projective_group := class_key_data`projective_group;
    if not (group_element in projective_group) then
        error "The permutation is not in the natural split-prime group.";
    end if;
    group_element := projective_group!group_element;
    points := class_key_data`projective_points;
    vector_space := Parent(points[1]);
    reference_points := [
        vector_space![1, 0],
        vector_space![0, 1],
        vector_space![1, 1]
    ];
    image_points := [];

    for reference_point in reference_points do
        reference_key := natural_projective_point_key(reference_point);
        if not IsDefined(class_key_data`projective_point_index_by_key, reference_key) then
            error "A reference point is missing from the natural projective line.";
        end if;
        reference_index := class_key_data`projective_point_index_by_key[reference_key];
        Append(~image_points, points[reference_index^group_element]);
    end for;

    u := image_points[1];
    v := image_points[2];
    w := image_points[3];
    determinant_uw := u[1] * w[2] - u[2] * w[1];
    determinant_vw := v[1] * w[2] - v[2] * w[1];
    if determinant_vw eq 0 then
        error "Three projective images did not determine a split matrix.";
    end if;
    relative_scale := -determinant_uw / determinant_vw;
    matrix_element := Matrix(
        BaseRing(class_key_data`split_basis_matrix),
        2,
        2,
        Eltseq(u) cat Eltseq(relative_scale * v)
    );
    is_consistent, coordinates := IsConsistent(
        class_key_data`split_basis_matrix,
        Vector(BaseRing(class_key_data`split_basis_matrix), Eltseq(matrix_element))
    );
    if not is_consistent then
        error "A projective matrix is not in the split quaternion algebra.";
    end if;

    reduced_element := class_key_data`reduced_algebra!Eltseq(coordinates);
    if not IsUnit(reduced_element) then
        error "A natural PGL element recovered a nonunit quaternion class.";
    end if;
    if natural_split_prime_action_permutation(reduced_element, class_key_data) ne
       group_element then
        error "Natural split-prime action recovery failed.";
    end if;

    return reduced_element;
end function;


// Test whether a FiniteQuotient record models G by the natural PGL(2, F)
// action on P^1(F) rather than by enumerated class representatives.
function UsesNaturalSplitPrimeModel(group_model)
    return assigned group_model`class_key_data and
           Type(group_model`class_key_data) eq Rec and
           assigned group_model`class_key_data`mode and
           group_model`class_key_data`mode eq "natural_split_prime";
end function;


// Recover a reduced quaternion unit whose natural action on P^1(F) equals
// the given permutation.  Stored unit and normalizer images use the inverse
// orientation (see cached_projective_permutation), so callers recovering a
// representative for a stored image pass its inverse.
function NaturalSplitPrimeReducedRepresentative(group_model, group_element)
    if not UsesNaturalSplitPrimeModel(group_model) then
        error "The quotient does not use the natural split-prime model.";
    end if;

    return natural_split_prime_reduced_representative_from_data(
        group_model`class_key_data,
        group_element
    );
end function;


// Identify a split four-dimensional algebra with M_2(F), and certify the
// resulting natural PGL(2,F) model without enumerating its group elements.
function natural_split_prime_model(
    reduced_algebra,
    reduced_base_ring,
    reduced_identity,
    expected_projective_group_order
)
    associative_algebra := AssociativeAlgebra(reduced_algebra);
    if not IsSimple(associative_algebra) then
        error "A locally split reduced quaternion algebra is not simple.";
    end if;

    minimal_right_ideals, complete := MinimalRightIdeals(associative_algebra);
    if not complete then
        error "The minimal-right-ideal computation was incomplete.";
    end if;
    degree_two_ideals := [
        ideal_x : ideal_x in minimal_right_ideals | Dimension(ideal_x) eq 2
    ];
    if #degree_two_ideals ne #reduced_base_ring + 1 then
        error "The split algebra does not have the expected projective line of minimal right ideals.";
    end if;

    matrix_algebra, split_map := MatrixAlgebra(
        associative_algebra,
        degree_two_ideals[1] :
        Side := "Right"
    );
    if Degree(matrix_algebra) ne 2 or BaseRing(matrix_algebra) ne reduced_base_ring then
        error "The split algebra did not produce M_2(F).";
    end if;
    if split_map(associative_algebra!1) ne Identity(matrix_algebra) or
       not &and[
           split_map(associative_algebra.i * associative_algebra.j) eq
           split_map(associative_algebra.i) * split_map(associative_algebra.j) :
           i, j in [1..4]
       ] then
        error "The matrix representation is not an algebra homomorphism.";
    end if;

    split_basis_matrix := Matrix(
        reduced_base_ring,
        4,
        4,
        &cat[
            Eltseq(split_map(associative_algebra.i)) : i in [1..4]
        ]
    );
    if Rank(split_basis_matrix) ne 4 then
        error "The split matrix representation is not an isomorphism.";
    end if;

    projective_group, projective_points := PGL(2, reduced_base_ring);
    if #projective_group ne expected_projective_group_order or
       Degree(projective_group) ne #reduced_base_ring + 1 or
       #projective_points ne #reduced_base_ring + 1 then
        error "The natural PGL(2,F) model has the wrong exact size or degree.";
    end if;
    projective_point_index_by_key := AssociativeArray();
    for i in [1..#projective_points] do
        key := natural_projective_point_key(projective_points[i]);
        if IsDefined(projective_point_index_by_key, key) then
            error "The natural projective-line points are not distinct.";
        end if;
        projective_point_index_by_key[key] := i;
    end for;

    class_key_data := rec<projective_class_key_data_format |
        mode := "natural_split_prime",
        reduced_algebra := reduced_algebra,
        associative_algebra := associative_algebra,
        split_map := split_map,
        split_basis_matrix := split_basis_matrix,
        projective_group := projective_group,
        projective_points := projective_points,
        projective_point_index_by_key := projective_point_index_by_key
    >;

    // Scalars must act trivially, and the three-point inverse must recover the
    // identity and every stored PGL generator exactly.
    for scalar in reduced_base_ring do
        if scalar ne 0 and
           natural_split_prime_action_permutation(
               scalar * reduced_identity,
               class_key_data
           ) ne Identity(projective_group) then
            error "A nonzero scalar acted nontrivially on the projective line.";
        end if;
    end for;
    test_elements := [Identity(projective_group)] cat
        [projective_group.i : i in [1..Ngens(projective_group)]] cat
        [projective_group.i^-1 : i in [1..Ngens(projective_group)]];
    for group_element in test_elements do
        _ := natural_split_prime_reduced_representative_from_data(
            class_key_data,
            group_element
        );
    end for;

    return projective_group, class_key_data;
end function;


function split_prime_square_projective_class_data(
    order_data,
    prime_ideal,
    reduced_algebra,
    reduced_base_ring,
    reduction_map,
    scalar_fibers,
    scalar_units,
    scalars,
    expected_projective_group_order :
    Print := 0
)
    Print := validate_print_level(Print);
    prime_reduced_algebra, prime_reduced_base_ring, prime_reduction_map :=
        build_reduced_algebra(order_data, prime_ideal);
    prime_reduced_identity := reduced_order_identity(
        order_data,
        prime_reduction_map,
        prime_reduced_algebra
    );
    prime_reduced_units := [unit_x : unit_x in prime_reduced_algebra | IsUnit(unit_x)];
    prime_scalar_units := [scalar_x : scalar_x in prime_reduced_base_ring | IsUnit(scalar_x)];
    prime_scalars := {scalar_x * prime_reduced_identity : scalar_x in prime_scalar_units};

    if (#prime_reduced_units mod #prime_scalars) ne 0 then
        error "Prime-level reduced-unit count is not divisible by scalar count.";
    end if;

    prime_num_classes := #prime_reduced_units div #prime_scalars;
    prime_class_representatives,
    prime_class_index_by_key := projective_class_data(
        prime_reduced_units,
        prime_scalars,
        prime_num_classes :
        Print := 0
    );

    reduced_identity := reduced_order_identity(order_data, reduction_map, reduced_algebra);
    zero_fiber := scalar_prime_fiber(
        scalar_fibers,
        prime_reduced_base_ring!0
    );
    scalar_kernel_tuples := scalar_kernel_tuples_for_prime_square(
        reduced_identity,
        zero_fiber
    );
    kernel_tuples := projective_kernel_tuples_for_prime_square(reduced_identity, zero_fiber);
    lifted_prime_representatives := [
        lift_prime_reduced_element_to_prime_square(
            reduced_algebra,
            scalar_fibers,
            prime_reduced_algebra!prime_representative
        ) :
        prime_representative in prime_class_representatives
    ];
    lifted_prime_representative_inverses := [
        lifted_prime_square_inverse(
            reduced_algebra,
            reduced_identity,
            scalar_fibers,
            lifted_prime_representatives[i],
            prime_reduced_algebra!prime_class_representatives[i]
        ) :
        i in [1..#prime_class_representatives]
    ];
    class_key_data := rec<projective_class_key_data_format |
        mode := "split_prime_square",
        order_data := order_data,
        prime_reduced_algebra := prime_reduced_algebra,
        prime_reduction_map := prime_reduction_map,
        reduction_map := reduction_map,
        prime_scalar_units := prime_scalar_units,
        prime_scalars := prime_scalars,
        prime_class_index_by_key := prime_class_index_by_key,
        lifted_prime_representatives := lifted_prime_representatives,
        lifted_prime_representative_inverses := lifted_prime_representative_inverses,
        scalar_fibers := scalar_fibers,
        scalar_kernel_tuples := scalar_kernel_tuples,
        reduced_identity := reduced_identity
    >;
    class_representatives := [];
    class_index_by_key := AssociativeArray();
    for prime_class_index in [1..#prime_class_representatives] do
        lifted_prime_representative := lifted_prime_representatives[prime_class_index];

        for kernel_tuple in kernel_tuples do
            kernel_unit := reduced_identity + reduced_algebra!kernel_tuple;
            representative := lifted_prime_representative * kernel_unit;
            class_key := Sprintf("%o|%o", prime_class_index, tuple_key(kernel_tuple));

            if not IsDefined(class_index_by_key, class_key) then
                Append(~class_representatives, Eltseq(representative));
                class_index_by_key[class_key] := #class_representatives;
            end if;
        end for;

    end for;

    if #class_representatives ne expected_projective_group_order then
        error Sprintf(
            "Split prime-square projective class construction found %o classes, expected %o.",
            #class_representatives,
            expected_projective_group_order
        );
    end if;

    return class_representatives, class_index_by_key, class_key_data;
end function;


// Compute the permutation induced by left multiplication on projective classes.
function left_action_permutation(
    g,
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data
)
    symmetric_group := Sym(#class_representatives);
    permutation_entries := [];

    for representative in class_representatives do
        product := reduced_algebra!g * reduced_algebra!representative;
        image_representative_key := projective_class_key(
            product,
            scalars,
            class_key_data
        );

        if not IsDefined(class_index_by_key, image_representative_key) then
            error "Left-action product not found in class representatives.";
        end if;

        Append(~permutation_entries, class_index_by_key[image_representative_key]);
    end for;

    return symmetric_group!permutation_entries;
end function;


// Cache the permutation attached to a whole scalar orbit at once.
procedure cache_orbit_permutation(
    reduced_algebra,
    scalars,
    representative,
    representative_permutation,
    ~reduced_to_permutation,
    ~permutation_to_reduced
)
    for scalar in scalars do
        reduced_to_permutation[Eltseq(reduced_algebra!representative * scalar)] := representative_permutation;
    end for;

    permutation_to_reduced[representative_permutation] := representative;
end procedure;





// Find generators in deterministic priority order.  The exact group-order
// check certifies when the selected permutations generate the full model.
function projective_generator_permutation_data(
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data,
    reduced_identity :
    Print := 0
)
    Print := validate_print_level(Print);
    num_classes := #class_representatives;
    symmetric_group := Sym(num_classes);
    priority_indices := priority_index_order(num_classes);
    reduced_to_permutation := AssociativeArray();
    permutation_to_reduced := AssociativeArray();
    generators := [];
    group_g := sub<symmetric_group | >;
    if num_classes eq 0 then
        return reduced_to_permutation, permutation_to_reduced, generators, group_g;
    end if;
    identity_key := projective_class_key(reduced_identity, scalars, class_key_data);
    if not IsDefined(class_index_by_key, identity_key) then
        error "The projective model does not contain the identity class.";
    end if;
    identity_representative := class_representatives[class_index_by_key[identity_key]];
    cache_orbit_permutation(
        reduced_algebra, scalars, identity_representative, Identity(symmetric_group),
        ~reduced_to_permutation, ~permutation_to_reduced
    );
    indices := priority_indices cat [i : i in [1..num_classes] | Index(priority_indices, i) eq 0];
    for index in indices do
        representative := class_representatives[index];
        permutation := left_action_permutation(
            representative, reduced_algebra, class_representatives,
            class_index_by_key, scalars, class_key_data
        );
        Append(~generators, permutation);
        group_g := sub<symmetric_group | generators>;
        cache_orbit_permutation(
            reduced_algebra, scalars, representative, permutation,
            ~reduced_to_permutation, ~permutation_to_reduced
        );
        if #group_g eq num_classes then break; end if;
    end for;
    if #group_g ne num_classes then
        error "The projective permutation generators do not generate every class.";
    end if;
    return reduced_to_permutation, permutation_to_reduced, generators, group_g;
end function;


// Reduce a stored order element modulo P^k using the principal basis of O.
function reduce_order_element_mod_modulus(order_data, element_x, reduction_map, reduced_algebra)
    integer_ring := order_data`integer_ring;
    coordinates := OrderCoordinates(order_data, element_x);
    reduced_coordinates := [];

    // The stored unit and normalizer representatives are elements of O, so
    // their principal-basis coefficients must already lie in the integer ring.
    for coefficient in coordinates do
        if not (coefficient in integer_ring) then
            return false, _, Sprintf(
                "Stored order element %o has non-integral coefficient %o in the principal basis.",
                element_x,
                coefficient
            );
        end if;

        Append(~reduced_coordinates, reduction_map(integer_ring!coefficient));
    end for;

    return true, reduced_algebra!reduced_coordinates, "";
end function;


// Build a fast lookup table for reduced units by coefficient sequence.
function reduced_unit_lookup(reduced_units)
    return rec<reduced_unit_membership_format |
        mode := "explicit",
        lookup := element_sequence_lookup(reduced_units)
    >;
end function;


function reduced_unit_isunit_lookup()
    return rec<reduced_unit_membership_format |
        mode := "is_unit"
    >;
end function;


// Test membership in the enumerated reduced unit group without calling IsUnit.
function reduced_element_is_unit(reduced_element, membership_data)
    if Type(membership_data) ne Rec or not assigned membership_data`mode then
        error "Invalid reduced-unit membership data.";
    end if;

    if membership_data`mode eq "explicit" then
        return IsDefined(membership_data`lookup, Eltseq(reduced_element));
    end if;

    if membership_data`mode eq "is_unit" then
        return IsUnit(reduced_element);
    end if;

    if membership_data`mode eq "prime_lift" then
        prime_reduced_element := reduce_prime_power_element_to_prime(
            membership_data`order_data,
            membership_data`prime_reduced_algebra,
            membership_data`prime_reduction_map,
            membership_data`reduction_map,
            reduced_element
        );
        return IsDefined(membership_data`prime_unit_lookup, Eltseq(prime_reduced_element));
    end if;

    error Sprintf("Unknown reduced-unit membership mode %o.", membership_data`mode);
end function;


// Convert one reduced projective class into its cached left-action permutation.
procedure cached_projective_permutation(
    order_data,
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data,
    reduced_element,
    source_element,
    label,
    ~cached_permutation,
    ~reduced_to_permutation,
    ~permutation_to_reduced
)
    reduced_key := Eltseq(reduced_element);

    if Type(class_key_data) eq Rec and
       assigned class_key_data`mode and
       class_key_data`mode eq "natural_split_prime" then
        if not IsDefined(reduced_to_permutation, reduced_key) then
            // Preserve the established interface: this routine returns the
            // inverse of the homomorphic projective action.
            representative_permutation :=
                natural_split_prime_action_permutation(
                    reduced_element,
                    class_key_data
                )^-1;
            reduced_to_permutation[reduced_key] := representative_permutation;
            permutation_to_reduced[representative_permutation] := reduced_key;
        end if;

        cached_permutation := reduced_to_permutation[reduced_key];
        return;
    end if;

    if not IsDefined(reduced_to_permutation, reduced_key) then
        source_coordinates := OrderCoordinates(order_data, source_element);
        representative_key := projective_class_key(
            reduced_element,
            scalars,
            class_key_data
        );

        if not IsDefined(class_index_by_key, representative_key) then
            print "[PUG debug] missing_label=", label;
            print "[PUG debug] source_element=", source_element;
            print "[PUG debug] source_coordinates=", source_coordinates;
            print "[PUG debug] reduced_coordinates=", reduced_key;
            print "[PUG debug] model_size=", #Keys(reduced_to_permutation);

            error Sprintf(
                "A reduced %o element did not land in the projective unit model. See [PUG debug] output above.",
                label
            );
        end if;

        representative := class_representatives[class_index_by_key[representative_key]];
        representative_permutation := left_action_permutation(
            representative,
            reduced_algebra,
            class_representatives,
            class_index_by_key,
            scalars,
            class_key_data
        );
        cache_orbit_permutation(
            reduced_algebra,
            scalars,
            representative,
            representative_permutation,
            ~reduced_to_permutation,
            ~permutation_to_reduced
        );
    end if;

    cached_permutation := reduced_to_permutation[reduced_key];
end procedure;


// At a ramified prime P the projective normalizer meets G in the classes of
// even reduced-norm valuation; odd valuation picks out the other coset,
// which generates the ramified Z/2Z extension.  These helpers locate one
// stored representative of that coset.
function normalizer_element_has_odd_valuation_at_prime(order_data, normalizer_element, prime_ideal)
    norm_ideal := Norm(normalizer_element) * order_data`integer_ring;
    return (Valuation(norm_ideal, prime_ideal) mod 2) ne 0;
end function;


function normalizer_representative_odd_at_prime(order_data, prime_ideal)
    for normalizer_element in order_data`normalizer_elements do
        if normalizer_element_has_odd_valuation_at_prime(order_data, normalizer_element, prime_ideal) then
            return true, normalizer_element;
        end if;
    end for;

    return false, false;
end function;


function normalizer_odd_representative_exists_at_prime(order_data, prime_ideal)
    found, representative := normalizer_representative_odd_at_prime(order_data, prime_ideal);
    return found;
end function;


// Recover a normalizer element with odd valuation above a ramified prime P.
// In the class-one case this is the unique principal two-sided generator.
// For non-class-one orders, a single ramified
// two-sided ideal need not be principal, so we fall back to any stored global
// normalizer representative with odd P-valuation; that is enough for the local
// ramified extension model.
function ramified_base_generator(order_data, prime_ideal)
    if order_data`order_type lt 2 then
        error "The ramified extension is only defined for Eichler orders.";
    end if;

    quaternion_order := order_data`quaternion_order;
    quaternion_algebra := order_data`quaternion_algebra;
    right_ideals := MaximalRightIdeals(quaternion_order, prime_ideal);
    candidate_generators := [];
    normalized_lookup := AssociativeArray();

    for right_ideal in right_ideals do
        if LeftOrder(right_ideal) ne quaternion_order then
            continue;
        end if;

        is_principal, generator := IsPrincipal(right_ideal);
        if not is_principal then
            continue;
        end if;

        generator := ord_primitive_integral_representative(order_data, generator);
        normalized_generator := normalize_quaternion_element(quaternion_algebra, generator);
        normalized_key := Sprint(Eltseq(normalized_generator));

        if not IsDefined(normalized_lookup, normalized_key) then
            normalized_lookup[normalized_key] := true;
            Append(~candidate_generators, generator);
        end if;
    end for;

    if #candidate_generators eq 0 then
        found_normalizer, normalizer_element :=
            normalizer_representative_odd_at_prime(order_data, prime_ideal);

        if found_normalizer then
            return ord_primitive_integral_representative(order_data, normalizer_element);
        end if;
    end if;

    if #candidate_generators ne 1 then
        error Sprintf(
            "Expected a principal two-sided generator or a stored odd-valuation normalizer representative above %o, but found %o principal candidates.",
            prime_ideal,
            #candidate_generators
        );
    end if;

    return candidate_generators[1];
end function;


// Reduce the basis-conjugation action x -> a x a^-1 to O / P^k O.
function ramified_conjugation_basis_images(order_data, conjugating_element, reduction_map)
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    principal_basis := order_data`principal_basis;
    inverse_element := (quaternion_algebra!conjugating_element)^-1;
    basis_images := [];

    for basis_element in principal_basis do
        conjugated_basis_element :=
            quaternion_algebra!conjugating_element *
            quaternion_algebra!basis_element *
            inverse_element;
        image_coordinates := OrderCoordinates(order_data, conjugated_basis_element);
        reduced_coordinates := [];

        for coordinate in image_coordinates do
            if not (coordinate in integer_ring) then
                error "The ramified conjugation action did not preserve the order basis integrally.";
            end if;

            Append(~reduced_coordinates, reduction_map(integer_ring!coordinate));
        end for;

        Append(~basis_images, reduced_coordinates);
    end for;

    return basis_images;
end function;


// Apply the reduced conjugation matrix determined by the ramified generator.
function ramified_conjugation_on_reduced_element(reduced_element, reduced_algebra, basis_images)
    coordinates := Eltseq(reduced_element);
    image_coordinates := [];

    for i in [1..#basis_images[1]] do
        Append(~image_coordinates, &+[coordinates[j] * basis_images[j][i] : j in [1..#coordinates]]);
    end for;

    return reduced_algebra!image_coordinates;
end function;


// Turn the conjugation action of a on G into a permutation of projective classes.
function ramified_conjugation_permutation(
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data,
    basis_images
)
    symmetric_group := Sym(#class_representatives);
    permutation_entries := [];

    for representative in class_representatives do
        conjugated_representative := ramified_conjugation_on_reduced_element(
            reduced_algebra!representative,
            reduced_algebra,
            basis_images
        );
        image_key := projective_class_key(
            conjugated_representative,
            scalars,
            class_key_data
        );

        if not IsDefined(class_index_by_key, image_key) then
            error "The ramified conjugation action did not preserve the projective unit classes.";
        end if;

        Append(~permutation_entries, class_index_by_key[image_key]);
    end for;

    return symmetric_group!permutation_entries;
end function;


// Return the projective-class index of the identity element.
function identity_class_index(reduced_identity, class_index_by_key, scalars, class_key_data)
    identity_key := projective_class_key(reduced_identity, scalars, class_key_data);

    if not IsDefined(class_index_by_key, identity_key) then
        error "The projective unit model does not contain the identity class.";
    end if;

    return class_index_by_key[identity_key];
end function;


// Compute left multiplication on the projective-class labels by one model-group element.
function left_label_multiplication_permutation(projective_unit_group, group_element, identity_index)
    num_classes := #projective_unit_group;
    symmetric_group := Sym(num_classes);
    permutation_entries := [0 : i in [1..num_classes]];
    filled_points := {};

    for model_element in projective_unit_group do
        point_index := identity_index^model_element;
        permutation_entries[point_index] :=
            identity_index^(group_element * model_element);
        Include(~filled_points, point_index);
    end for;

    if #filled_points ne num_classes then
        error "The projective unit model did not act regularly on its projective classes.";
    end if;

    return symmetric_group!permutation_entries;
end function;


// Recover the ramified generator a together with its square class in the model G.
procedure ramified_extension_data(
    order_data,
    prime_ideal,
    reduction_map,
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data,
    reduced_unit_lookup_data,
    ~ramified_generator_element,
    ~ramified_basis_images,
    ~ramified_conjugation_action,
    ~ramified_square_unit_permutation,
    ~ramified_generator_square_is_scalar,
    ~reduced_to_permutation,
    ~permutation_to_reduced
)
    quaternion_algebra := order_data`quaternion_algebra;
    ramified_generator_squared := false;
    ramified_generator_square_reduction_source := false;
    reduced_square_unit := false;
    message := "";

    ramified_generator_element := ramified_base_generator(order_data, prime_ideal);
    ramified_basis_images := ramified_conjugation_basis_images(
        order_data,
        ramified_generator_element,
        reduction_map
    );
    ramified_conjugation_action := ramified_conjugation_permutation(
        reduced_algebra,
        class_representatives,
        class_index_by_key,
        scalars,
        class_key_data,
        ramified_basis_images
    );

    ramified_generator_squared := (quaternion_algebra!ramified_generator_element)^2;
    ramified_generator_square_is_scalar := &and[
        OrderCoordinates(order_data, ramified_generator_squared)[i] eq 0 :
        i in [2..4]
    ];
    ramified_generator_square_reduction_source := ord_primitive_integral_representative(
        order_data,
        ramified_generator_squared
    );
    ok, reduced_square_unit, message := reduce_order_element_mod_modulus(
        order_data,
        ramified_generator_square_reduction_source,
        reduction_map,
        reduced_algebra
    );

    if not ok then
        error message;
    end if;

    if not reduced_element_is_unit(reduced_square_unit, reduced_unit_lookup_data) then
        error "The ramified generator square did not reduce to a projective unit.";
    end if;

    cached_projective_permutation(
        order_data,
        reduced_algebra,
        class_representatives,
        class_index_by_key,
        scalars,
        class_key_data,
        reduced_square_unit,
        ramified_generator_square_reduction_source,
        "ramified generator square unit",
        ~ramified_square_unit_permutation,
        ~reduced_to_permutation,
        ~permutation_to_reduced
    );
    ramified_square_unit_permutation := ramified_square_unit_permutation^-1;
end procedure;


// Lift one model-group element to the faithful doubled ramified extension.
function semidirect_unit_permutation(projective_permutation, num_classes)
    symmetric_group := Sym(2 * num_classes);
    permutation_entries := [];

    for layer in [0..1] do
        offset := layer * num_classes;
        for index in [1..num_classes] do
            Append(~permutation_entries, offset + (index^projective_permutation));
        end for;
    end for;

    return symmetric_group!permutation_entries;
end function;


// Realize the ramified generator t with relation t^2 = g0 in the doubled model.
function ramified_extension_generator_permutation(
    conjugation_inverse_permutation,
    square_left_label_permutation,
    num_classes
)
    symmetric_group := Sym(2 * num_classes);
    permutation_entries := [];

    for index in [1..num_classes] do
        Append(~permutation_entries, num_classes + (index^conjugation_inverse_permutation));
    end for;

    for index in [1..num_classes] do
        Append(~permutation_entries, index^(conjugation_inverse_permutation * square_left_label_permutation));
    end for;

    return symmetric_group!permutation_entries;
end function;


// Build the faithful doubled permutation model of W generated by G and one
// ramified normalizer element t with t^2 = g0.
function ramified_extension_group(
    projective_unit_group,
    conjugation_permutation,
    square_unit_permutation,
    identity_index,
    num_classes
)
    symmetric_group := Sym(2 * num_classes);
    square_left_label_permutation := left_label_multiplication_permutation(
        projective_unit_group,
        square_unit_permutation,
        identity_index
    );
    conjugation_inverse_permutation := conjugation_permutation^-1;
    lifted_generators := [semidirect_unit_permutation(projective_unit_group.i, num_classes) : i in [1..Ngens(projective_unit_group)]];
    ramified_generator_permutation := ramified_extension_generator_permutation(
        conjugation_inverse_permutation,
        square_left_label_permutation,
        num_classes
    );
    extension_group := sub<symmetric_group | lifted_generators cat [ramified_generator_permutation]>;

    return extension_group, ramified_generator_permutation;
end function;


// Emit detailed diagnostics when the ramified square relation fails in the model.
procedure print_ramified_extension_relation_failure(
    order_data,
    prime_ideal,
    ramified_generator_element,
    ramified_square_unit_permutation,
    ramified_conjugation_action,
    projective_unit_group,
    permutation_to_reduced
)
    quaternion_algebra := order_data`quaternion_algebra;
    ramified_generator_squared := (quaternion_algebra!ramified_generator_element)^2;
    ramified_generator_squared_coordinates := OrderCoordinates(
        order_data,
        ramified_generator_squared
    );
    ramified_generator_squared_is_scalar :=
        &and[ramified_generator_squared_coordinates[i] eq 0 : i in [2..#ramified_generator_squared_coordinates]];
    print "[PUG debug] ramified_extension_relation_failure |", ideal_summary("P", prime_ideal);
    print "[PUG debug] ramified_generator=", ramified_generator_element;
    print "[PUG debug] ramified_generator_squared=", ramified_generator_squared;
    print "[PUG debug] ramified_generator_squared_coords=", ramified_generator_squared_coordinates;
    print "[PUG debug] ramified_generator_squared_is_scalar=", ramified_generator_squared_is_scalar;
    print "[PUG debug] ramified_conjugation_order=", Order(ramified_conjugation_action);

    for generator_index in [1..Ngens(projective_unit_group)] do
        generator_image := projective_unit_group.generator_index;
        lhs := ramified_conjugation_action^2 * generator_image * (ramified_conjugation_action^-2);
        rhs := ramified_square_unit_permutation * generator_image * (ramified_square_unit_permutation^-1);

        if lhs ne rhs then
            print "[PUG debug] mismatch_generator_index=", generator_index;
            if IsDefined(permutation_to_reduced, generator_image) then
                print "[PUG debug] mismatch_generator_representative=", permutation_to_reduced[generator_image];
            end if;
            print "[PUG debug] lhs=", lhs;
            print "[PUG debug] rhs=", rhs;
            return;
        end if;
    end for;

    print "[PUG debug] No generator mismatch was found even though the square relation failed.";
end procedure;


// Convert one stored normalizer element into its image permutation.
procedure normalizer_image_permutation(
    order_data,
    normalizer_element,
    reduced_algebra,
    reduction_map,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data,
    reduced_unit_lookup_data,
    ramified_extension_defined,
    ramified_generator_element,
    ramified_generator_permutation,
    num_classes,
    ~image_permutation,
    ~reduced_to_permutation,
    ~permutation_to_reduced
)
    quaternion_algebra := order_data`quaternion_algebra;
    ok, reduced_element, message := reduce_order_element_mod_modulus(
        order_data,
        normalizer_element,
        reduction_map,
        reduced_algebra
    );

    if not ok then
        error message;
    end if;

    if reduced_element_is_unit(reduced_element, reduced_unit_lookup_data) then
        projective_permutation := false;
        cached_projective_permutation(
            order_data,
            reduced_algebra,
            class_representatives,
            class_index_by_key,
            scalars,
            class_key_data,
            reduced_element,
            normalizer_element,
            "normalizer",
            ~projective_permutation,
            ~reduced_to_permutation,
            ~permutation_to_reduced
        );
        projective_permutation := projective_permutation^-1;

        if ramified_extension_defined then
            image_permutation := semidirect_unit_permutation(projective_permutation, num_classes);
            return;
        end if;

        image_permutation := projective_permutation;
        return;
    end if;

    if not ramified_extension_defined then
        error "A split-prime normalizer representative did not reduce to a projective unit.";
    end if;

    unit_component := ord_primitive_integral_representative(
        order_data,
        quaternion_algebra!normalizer_element * (quaternion_algebra!ramified_generator_element)^-1
    );
    ok, reduced_unit_component, message := reduce_order_element_mod_modulus(
        order_data,
        unit_component,
        reduction_map,
        reduced_algebra
    );

    if not ok then
        error message;
    end if;

    if not reduced_element_is_unit(reduced_unit_component, reduced_unit_lookup_data) then
        error "The ramified normalizer coset failed to split as unit times the ramified generator.";
    end if;

    projective_permutation := false;
    cached_projective_permutation(
        order_data,
        reduced_algebra,
        class_representatives,
        class_index_by_key,
        scalars,
        class_key_data,
        reduced_unit_component,
        unit_component,
        "ramified normalizer unit part",
        ~projective_permutation,
        ~reduced_to_permutation,
        ~permutation_to_reduced
    );
    projective_permutation := projective_permutation^-1;

    image_permutation := semidirect_unit_permutation(projective_permutation, num_classes) * ramified_generator_permutation;
end procedure;


// Search in a faithful reduced-degree copy, then return the complements in
// the caller's group.  Conjugacy classes and intersections are preserved
// exactly by the isomorphism, and the smaller degree keeps Magma's
// Subgroups enumeration tractable.
function complement_classes(group_g, subgroup_k)
    group_order := #group_g;
    subgroup_order := #subgroup_k;

    if group_order mod subgroup_order ne 0 then
        return [];
    end if;

    if subgroup_order eq 1 then
        return [rec<computed_complement_class_format | subgroup := group_g>];
    end if;

    search_group, reduction_map := DegreeReduction(group_g);
    if #Kernel(reduction_map) ne 1 or #search_group ne group_order then
        error "Degree reduction did not give a faithful copy of the ambient group.";
    end if;
    search_subgroup := reduction_map(subgroup_k);
    if #search_subgroup ne subgroup_order then
        error "Degree reduction changed the localized image order.";
    end if;

    target_order := group_order div subgroup_order;
    subgroup_classes := Subgroups(search_group : OrderEqual := target_order);
    complements := [];

    for subgroup_class in subgroup_classes do
        complement_subgroup := subgroup_class`subgroup;

        // Keep the full subgroup-class record, but only when the representative
        // subgroup is actually a complement of subgroup_k.
        if #complement_subgroup * subgroup_order ne group_order then
            continue;
        end if;

        if #(complement_subgroup meet search_subgroup) eq 1 then
            original_subgroup := complement_subgroup @@ reduction_map;
            if #original_subgroup ne target_order or
               #(original_subgroup meet subgroup_k) ne 1 then
                error "A reduced complement did not pull back exactly.";
            end if;
            Append(
                ~complements,
                rec<computed_complement_class_format |
                    subgroup := original_subgroup
                >
            );
        end if;
    end for;

    return complements;
end function;


// Keep only the complement classes whose representative subgroup is normal.
function normal_complement_classes(group_g, complement_list)
    return [complement_class : complement_class in complement_list | IsNormal(group_g, complement_class`subgroup)];
end function;


// Build G = (O / P^k O)^* / (R / P^k)^* and, for Eichler orders, the image
// of the projective normalizer (inside G at split primes, inside the doubled
// extension W at ramified primes).
function FiniteQuotient(
    order_data,
    prime_ideal,
    k :
    Print := 0
)
    Print := validate_print_level(Print);
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    prime_ideal := normalize_prime_ideal(integer_ring, prime_ideal);
    if Type(k) ne RngIntElt or k lt 1 then
        error "k must be an integer >= 1.";
    end if;

    modulus_ideal := prime_ideal^k;
    algebra_discriminant := Discriminant(quaternion_algebra);
    order_discriminant := order_data`order_discriminant;
    prime_ramified_in_algebra := Valuation(algebra_discriminant, prime_ideal) ne 0;
    prime_divides_order_discriminant := Valuation(order_discriminant, prime_ideal) ne 0;
    local_maximal_at_prime := order_is_locally_maximal_at_prime(order_data, prime_ideal);
    projective_formula_known,
    expected_projective_group_order,
    formula_case := expected_projective_group_order_data(order_data, prime_ideal, k);
    expected_scalar_unit_count := expected_scalar_unit_order(prime_ideal, k);
    expected_reduced_unit_count := projective_formula_known select
        expected_projective_group_order * expected_scalar_unit_count else 0;

    if print_is_concise(Print) then
        print "";
        print "[PUG]", ideal_summary("P", prime_ideal),
              "| k=", k,
              "| modulus_norm=", Norm(modulus_ideal),
              "| ramified_in_B=", prime_ramified_in_algebra,
              "| divides_order_disc=", prime_divides_order_discriminant;
    end if;

    reduced_algebra, reduced_base_ring, reduction_map :=
        build_reduced_algebra(order_data, modulus_ideal);
    reduced_identity := reduced_order_identity(order_data, reduction_map, reduced_algebra);

    // Model selection: k = 1 split uses the natural PGL(2, F) action on
    // P^1(F); k = 2 split lifts prime-level classes through the reduction
    // kernel; k = 1 ramified enumerates classes as unit points of P^3(F);
    // every other case enumerates (O / P^k O)^* in full.
    use_split_prime_square_model :=
        k eq 2 and
        local_maximal_at_prime and
        (not prime_ramified_in_algebra);
    use_natural_split_prime_model :=
        k eq 1 and
        local_maximal_at_prime and
        (not prime_ramified_in_algebra);
    use_prime_projective_point_model :=
        k eq 1 and
        local_maximal_at_prime and
        prime_ramified_in_algebra;

    if use_natural_split_prime_model then
        if not projective_formula_known then
            error "The split prime quotient has no exact group-order formula.";
        end if;
        scalar_units := [a : a in reduced_base_ring | IsUnit(a)];
        if #scalar_units ne expected_scalar_unit_count then
            error "Scalar-unit count did not match the expected size of (R / P)^*.";
        end if;
        scalars := {a * reduced_identity : a in scalar_units};
        num_classes := expected_projective_group_order;
        reduced_units := [];
        reduced_unit_membership_data := reduced_unit_isunit_lookup();
        class_representatives := [];
        class_index_by_key := AssociativeArray();
        projective_unit_group, class_key_data := natural_split_prime_model(
            reduced_algebra,
            reduced_base_ring,
            reduced_identity,
            expected_projective_group_order
        );
    elif use_split_prime_square_model then
        prime_reduced_algebra, prime_reduced_base_ring, prime_reduction_map :=
            build_reduced_algebra(order_data, prime_ideal);
        prime_reduced_units := [unit_x : unit_x in prime_reduced_algebra | IsUnit(unit_x)];
        prime_unit_lookup := element_sequence_lookup(prime_reduced_units);
        scalar_fibers := scalar_prime_reduction_fibers(
            order_data`integer_ring,
            reduced_base_ring,
            reduction_map,
            prime_reduced_base_ring,
            prime_reduction_map
        );
        scalar_units := lifted_prime_power_scalar_units(
            scalar_fibers,
            prime_reduced_base_ring,
            prime_reduced_base_ring!0
        );
        one_algebra := reduced_order_identity(order_data, reduction_map, reduced_algebra);
        scalars := {a * one_algebra : a in scalar_units};
        reduced_units := [];
        reduced_unit_membership_data := rec<reduced_unit_membership_format |
            mode := "prime_lift",
            order_data := order_data,
            prime_reduced_algebra := prime_reduced_algebra,
            prime_reduction_map := prime_reduction_map,
            reduction_map := reduction_map,
            prime_unit_lookup := prime_unit_lookup
        >;

        if #scalar_units ne expected_scalar_unit_count then
            error "Scalar-unit count did not match the expected size of (R / P^2)^*.";
        end if;

        class_representatives,
        class_index_by_key,
        class_key_data := split_prime_square_projective_class_data(
            order_data,
            prime_ideal,
            reduced_algebra,
            reduced_base_ring,
            reduction_map,
            scalar_fibers,
            scalar_units,
            scalars,
            expected_projective_group_order :
            Print := Print
        );
        num_classes := projective_formula_known select expected_projective_group_order else #class_representatives;
    elif use_prime_projective_point_model then
        class_key_data := false;
        scalar_units := [a : a in reduced_base_ring | IsUnit(a)];
        if #scalar_units ne expected_scalar_unit_count then
            error "Scalar-unit count did not match the expected size of (R / P)^*.";
        end if;
        scalars := {a * reduced_identity : a in scalar_units};
        num_classes := expected_projective_group_order;
        reduced_units := [];
        reduced_unit_membership_data := reduced_unit_isunit_lookup();
        class_representatives,
        class_index_by_key := projective_point_class_data(
            reduced_algebra,
            reduced_base_ring,
            scalars,
            num_classes :
            Print := Print
        );
    else
        class_key_data := false;
        reduced_units, scalar_units, scalars := reduced_unit_data(
                order_data,
                modulus_ideal,
                reduced_base_ring,
                reduced_algebra,
                reduction_map :
                Print := Print,
                expected_scalar_unit_order := expected_scalar_unit_count
            );


        if (#reduced_units mod #scalars) ne 0 then
            error "Reduced-unit count is not divisible by scalar count.";
        end if;

        num_classes := #reduced_units div #scalars;
        if projective_formula_known and num_classes ne expected_projective_group_order then
            error "Projective group size did not match the expected maximal-local formula.";
        end if;
        if expected_reduced_unit_count ne 0 and #reduced_units ne expected_reduced_unit_count then
            error "Reduced-unit count did not match the expected maximal-local formula.";
        end if;
        reduced_unit_membership_data := reduced_unit_lookup(reduced_units);
        class_representatives, class_index_by_key := projective_class_data(
            reduced_units, scalars, num_classes : Print := Print
        );
    end if;


    if not use_natural_split_prime_model and
       #class_representatives ne num_classes then
        error "Failed to recover the expected number of projective classes.";
    end if;

    // Certify generators of the full projective model; cache additional class
    // permutations later only when unit or normalizer images require them.
    if use_natural_split_prime_model then
        reduced_to_permutation := AssociativeArray();
        permutation_to_reduced := AssociativeArray();
        generator_permutations := [
            projective_unit_group.i : i in [1..Ngens(projective_unit_group)]
        ];
    else
        reduced_to_permutation,
        permutation_to_reduced,
        generator_permutations,
        projective_unit_group := projective_generator_permutation_data(
            reduced_algebra,
            class_representatives,
            class_index_by_key,
            scalars,
            class_key_data,
            reduced_identity :
            Print := Print
        );
    end if;


    if #projective_unit_group ne num_classes then
        error "Generated projective group not of the correct size.";
    end if;

    reduced_unit_lookup_data := reduced_unit_membership_data;

    // At split primes the normalizer image is computed inside G. At ramified
    // primes of Eichler orders we enlarge the ambient group to the doubled
    // ramified extension generated by G and one ramified normalizer element.
    split_normalizer_image_defined :=
        (order_data`order_type ge 2) and
        (not prime_ramified_in_algebra) and
        (not prime_divides_order_discriminant);
    ramified_extension_defined :=
        (order_data`order_type ge 2) and
        prime_ramified_in_algebra and
        normalizer_odd_representative_exists_at_prime(order_data, prime_ideal);
    normalizer_image_defined := split_normalizer_image_defined or ramified_extension_defined;
    normalizer_ambient_group := false;
    normalizer_image_map := false;
    ramified_generator_element := false;
    ramified_generator_square_is_scalar := false;
    ramified_square_unit_permutation := false;
    ramified_conjugation_action := false;
    ramified_generator_action := false;

    if ramified_extension_defined then
        ramified_basis_images := false;
        identity_index := identity_class_index(
            reduced_identity,
            class_index_by_key,
            scalars,
            class_key_data
        );
        ramified_extension_data(
            order_data,
            prime_ideal,
            reduction_map,
            reduced_algebra,
            class_representatives,
            class_index_by_key,
            scalars,
            class_key_data,
            reduced_unit_lookup_data,
            ~ramified_generator_element,
            ~ramified_basis_images,
            ~ramified_conjugation_action,
            ~ramified_square_unit_permutation,
            ~ramified_generator_square_is_scalar,
            ~reduced_to_permutation,
            ~permutation_to_reduced
        );

        for generator_index in [1..Ngens(projective_unit_group)] do
            generator_image := projective_unit_group.generator_index;
            lhs := ramified_conjugation_action^2 * generator_image * (ramified_conjugation_action^-2);
            // ramified_square_unit_permutation is stored in the same orientation
            // as normalizer images, namely as the inverse left-action
            // permutation of the unit class of a^2.
            rhs := (ramified_square_unit_permutation^-1) * generator_image * ramified_square_unit_permutation;

            if lhs ne rhs then
                print_ramified_extension_relation_failure(
                    order_data,
                    prime_ideal,
                    ramified_generator_element,
                    ramified_square_unit_permutation,
                    ramified_conjugation_action,
                    projective_unit_group,
                    permutation_to_reduced
                );
                error "The ramified square relation alpha^2 = conjugation_by(a^2) failed on the projective model.";
            end if;
        end for;

        normalizer_ambient_group, ramified_generator_action := ramified_extension_group(
            projective_unit_group,
            ramified_conjugation_action,
            ramified_square_unit_permutation,
            identity_index,
            num_classes
        );

        if ramified_generator_action^2 ne semidirect_unit_permutation(ramified_square_unit_permutation, num_classes) then
            print_ramified_extension_relation_failure(
                order_data,
                prime_ideal,
                ramified_generator_element,
                ramified_square_unit_permutation,
                ramified_conjugation_action,
                projective_unit_group,
                permutation_to_reduced
            );
            error "The ramified generator square did not match the lifted image of a^2.";
        end if;

        if #normalizer_ambient_group ne 2 * #projective_unit_group then
            error "The ramified extension model did not double the size of the projective unit group.";
        end if;
    elif split_normalizer_image_defined then
        normalizer_ambient_group := projective_unit_group;
    end if;

    if normalizer_image_defined then
        normalizer_generator_images := [];
        for i in [1..Ngens(order_data`normalizer_group)] do
            if print_is_concise(Print) then
                print "[PUG] normalizer_generator_image", i, "/", Ngens(order_data`normalizer_group);
            end if;
            generator_element := ord_primitive_integral_representative(
                order_data,
                order_data`normalizer_map(order_data`normalizer_group.i)
            );
            generator_image := false;
            normalizer_image_permutation(
                order_data,
                generator_element,
                reduced_algebra,
                reduction_map,
                class_representatives,
                class_index_by_key,
                scalars,
                class_key_data,
                reduced_unit_lookup_data,
                ramified_extension_defined,
                ramified_generator_element,
                ramified_generator_action,
                num_classes,
                ~generator_image,
                ~reduced_to_permutation,
                ~permutation_to_reduced
            );
            Append(~normalizer_generator_images, generator_image);
        end for;

        normalizer_image_map := hom<order_data`normalizer_group -> normalizer_ambient_group | normalizer_generator_images>;
    end if;

    if print_is_concise(Print) then
        if normalizer_image_defined then
            print "[PUG] summary",
                  "| G_size=", #projective_unit_group,
                  "| ramified_generator_square_is_scalar=", ramified_generator_square_is_scalar,
                  "| normalizer_ambient_size=", #normalizer_ambient_group;
        else
            print "[PUG] summary",
                  "| G_size=", #projective_unit_group,
                  "| normalizer_image=not_applicable";
        end if;
    end if;

    return rec<projective_unit_group_format |
        order_data := order_data,
        modulus_ideal := modulus_ideal,
        reduced_base_ring := reduced_base_ring,
        reduced_algebra := reduced_algebra,
        reduction_map := reduction_map,
        reduced_unit_membership := reduced_unit_membership_data,
        reduced_units := reduced_units,
        scalars := scalars,
        class_representatives := class_representatives,
        class_index_by_key := class_index_by_key,
        class_key_data := class_key_data,
        reduced_to_permutation := reduced_to_permutation,
        permutation_to_reduced := permutation_to_reduced,
        projective_unit_group := projective_unit_group,
        normalizer_image_defined := normalizer_image_defined,
        normalizer_ambient_group := normalizer_ambient_group,
        normalizer_image_map := normalizer_image_map,
        ramified_extension_defined := ramified_extension_defined,
        ramified_generator := ramified_generator_element,
        ramified_generator_permutation := ramified_generator_action
    >;
end function;
