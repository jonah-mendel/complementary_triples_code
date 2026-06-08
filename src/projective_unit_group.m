// ============================================================================
// Projective unit groups modulo prime powers.
//
// Main API:
// - build_projective_unit_group(order_data, prime_ideal, k :
//       Print := 1,
//       time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0,
//       compute_complements := true)
// ============================================================================
// Record storing one projective unit-group computation modulo P^k.
projective_unit_group_format := recformat<
    order_data,
    prime_ideal,
    prime_power_exponent,
    modulus_ideal,
    elapsed_seconds,
    estimated_reduced_unit_seconds,
    estimated_permutation_seconds,
    prime_ramified_in_algebra,
    local_maximal_at_prime,
    formula_case,
    expected_projective_group_order,
    expected_scalar_unit_order,
    expected_reduced_unit_order,
    reduced_base_ring,
    reduced_algebra,
    reduction_map,
    reduced_units,
    scalar_units,
    scalars,
    reduced_unit_membership,
    class_representatives,
    class_index_by_key,
    class_key_data,
    reduced_to_permutation,
    permutation_to_reduced,
    reduced_unit_lifts,
    projective_unit_group,
    unit_image_permutations,
    unit_image_subgroup,
    unit_complements,
    normal_unit_complements,
    normalizer_image_defined,
    normalizer_ambient_group,
    normalizer_image_map,
    normalizer_reduced_lifts,
    normalizer_image_permutations,
    normalizer_image_subgroup,
    normalizer_complements,
    normal_normalizer_complements,
    ramified_extension_defined,
    ramified_generator,
    ramified_generator_square_is_scalar,
    ramified_square_unit_permutation,
    ramified_conjugation_permutation,
    ramified_generator_permutation,
    complements_computed,
    skipped_due_to_estimate,
    skipped_task_key,
    skipped_estimated_seconds
>;


projective_class_key_data_format := recformat<
    mode,
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


// Validate the optional estimated-runtime cutoff.
function validate_estimated_time_control(seconds, parameter_name)
    if Type(seconds) ne RngIntElt or seconds lt 0 then
        error Sprintf("%o must be an integer >= 0.", parameter_name);
    end if;

    return seconds;
end function;


// Validate the optional estimated-runtime cutoff.
function validate_time_limit_seconds(time_limit_seconds)
    return validate_estimated_time_control(time_limit_seconds, "time_limit_seconds");
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

    return Sprintf("%o_gen=unavailable | %o_norm=%o", label, Norm(ideal_x));
end function;


// Test whether an estimated runtime exceeds the chosen cutoff.
function time_limit_exceeded(time_limit_seconds, estimated_seconds)
    return (time_limit_seconds gt 0) and (estimated_seconds gt time_limit_seconds);
end function;


// Combine the enabled time controls relevant to one stage.
function effective_stage_time_limit_seconds(
    stage_key,
    k,
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds
)
    active_limits := [];

    if time_limit_seconds gt 0 then
        Append(~active_limits, time_limit_seconds);
    end if;

    if stage_key eq "projective_quotient" and max_projective_quotient_seconds gt 0 then
        Append(~active_limits, max_projective_quotient_seconds);
    end if;

    if stage_key eq "reduced_units" and k ge 2 and max_reduced_unit_seconds gt 0 then
        Append(~active_limits, max_reduced_unit_seconds);
    end if;

    return #active_limits eq 0 select 0 else Minimum(active_limits);
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


// Express an algebra element in the chosen principal basis of the order.
function coordinates_in_basis(base_field, quaternion_algebra, basis, element_x)
    basis_matrix := Matrix(base_field, 4, 4, &cat([Eltseq(quaternion_algebra!b) : b in basis]));
    x_vector := Vector(base_field, [base_field!c : c in Eltseq(quaternion_algebra!element_x)]);
    is_consistent, solution := IsConsistent(basis_matrix, x_vector);

    if not is_consistent then
        error "Element is not expressible in the chosen basis.";
    end if;

    return Eltseq(solution);
end function;


// Build the reduced algebra O / P^k O together with the base-ring reduction map.
function build_reduced_algebra(order_data, modulus_ideal)
    base_field := order_data`base_field;
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
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
        coordinates_in_basis(base_field, quaternion_algebra, principal_basis, principal_basis[i] * principal_basis[j]) : i, j in [1..4]
    ];

    reduced_algebra := Algebra<reduced_base_ring, 4 | [[reduction_map(c) : c in row] : row in multiplication_table]>;
    return reduced_algebra, reduced_base_ring, reduction_map;
end function;


// Reduce the identity element of the order to the reduced algebra.
function reduced_order_identity(order_data, reduction_map, reduced_algebra)
    base_field := order_data`base_field;
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    principal_basis := order_data`principal_basis;
    identity_coordinates := coordinates_in_basis(
        base_field,
        quaternion_algebra,
        principal_basis,
        order_data`quaternion_order!1
    );
    reduced_coordinates := [];

    for coefficient in identity_coordinates do
        if not (coefficient in integer_ring) then
            error "The identity element does not have integral principal-basis coordinates.";
        end if;

        Append(~reduced_coordinates, reduction_map(integer_ring!coefficient));
    end for;

    return reduced_algebra!reduced_coordinates;
end function;


// Estimate the cost of enumerating units with IsUnit.
function estimate_isunit_enumeration(structure_s, total_elements, label : Print := 0)
    Print := validate_print_level(Print);

    if total_elements eq 0 then
        return 0;
    end if;

    sample_size := Minimum(total_elements, 30);
    sample_checks := 0;
    sample_timer := Cputime();

    for x in structure_s do
        is_unit := IsUnit(x);
        sample_checks +:= 1;

        if sample_checks eq sample_size then
            break;
        end if;
    end for;

    sample_elapsed := Cputime(sample_timer);
    estimated_seconds := 0;

    if sample_checks gt 0 and sample_elapsed gt 0 then
        estimated_seconds := (total_elements * sample_elapsed) / sample_checks;
    end if;

    if print_is_concise(Print) then
        print "[PUG estimate]", label, "| elements=", total_elements, "| isunit_s=", estimated_seconds;
    end if;
    return estimated_seconds;
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


// Estimate the cost of filtering R / P^k by nonzero reduction modulo P.
function estimate_prime_lift_scalar_filter_workload(
    integer_ring,
    reduced_base_ring,
    reduction_map,
    prime_reduced_base_ring,
    prime_reduction_map,
    total_elements,
    label :
    Print := 0
)
    Print := validate_print_level(Print);

    if total_elements eq 0 then
        return 0;
    end if;

    sample_size := Minimum(total_elements, 30);
    sample_checks := 0;
    sample_timer := Cputime();

    for scalar in reduced_base_ring do
        reduction_scalar := reduce_prime_power_scalar_to_prime(
            integer_ring,
            prime_reduction_map,
            reduction_map,
            scalar
        );
        is_unit := reduction_scalar ne prime_reduced_base_ring!0;
        sample_checks +:= 1;

        if sample_checks eq sample_size then
            break;
        end if;
    end for;

    sample_elapsed := Cputime(sample_timer);
    estimated_seconds := 0;

    if sample_checks gt 0 and sample_elapsed gt 0 then
        estimated_seconds := (total_elements * sample_elapsed) / sample_checks;
    end if;

    if print_is_concise(Print) then
        print "[PUG estimate]", label, "| elements=", total_elements, "| prime_lift_filter_s=", estimated_seconds;
    end if;
    return estimated_seconds;
end function;


// Estimate the cost of filtering O / P^k O by unit reduction modulo P.
function estimate_prime_lift_unit_filter_workload(
    order_data,
    reduced_algebra,
    reduction_map,
    prime_reduced_algebra,
    prime_reduction_map,
    prime_unit_lookup,
    total_elements,
    label :
    Print := 0
)
    Print := validate_print_level(Print);

    if total_elements eq 0 then
        return 0;
    end if;

    sample_size := Minimum(total_elements, 30);
    sample_checks := 0;
    sample_timer := Cputime();

    for x in reduced_algebra do
        reduction_x := reduce_prime_power_element_to_prime(
            order_data,
            prime_reduced_algebra,
            prime_reduction_map,
            reduction_map,
            x
        );
        is_unit := IsDefined(prime_unit_lookup, Eltseq(reduction_x));
        sample_checks +:= 1;

        if sample_checks eq sample_size then
            break;
        end if;
    end for;

    sample_elapsed := Cputime(sample_timer);
    estimated_seconds := 0;

    if sample_checks gt 0 and sample_elapsed gt 0 then
        estimated_seconds := (total_elements * sample_elapsed) / sample_checks;
    end if;

    if print_is_concise(Print) then
        print "[PUG estimate]", label, "| elements=", total_elements, "| prime_lift_filter_s=", estimated_seconds;
    end if;
    return estimated_seconds;
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
    ~lifted_elements,
    max_elements
)
    if max_elements gt 0 and #lifted_elements ge max_elements then
        return;
    end if;

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
            ~lifted_elements,
            max_elements
        );

        if max_elements gt 0 and #lifted_elements ge max_elements then
            return;
        end if;
    end for;
end procedure;


procedure append_lifts_of_prime_unit(
    reduced_algebra,
    scalar_fibers,
    prime_unit,
    ~lifted_units,
    max_elements
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
        ~lifted_units,
        max_elements
    );
end procedure;


function lifted_prime_power_units(
    reduced_algebra,
    scalar_fibers,
    prime_reduced_units :
    max_elements := 0
)
    lifted_units := [];

    for prime_unit in prime_reduced_units do
        append_lifts_of_prime_unit(
            reduced_algebra,
            scalar_fibers,
            prime_unit,
            ~lifted_units,
            max_elements
        );

        if max_elements gt 0 and #lifted_units ge max_elements then
            break;
        end if;
    end for;

    return lifted_units;
end function;


function estimated_prime_power_unit_lift_seconds(
    reduced_algebra,
    scalar_fibers,
    prime_reduced_units,
    expected_lift_count :
    Print := 0,
    label := "O/P^kO lifted units"
)
    Print := validate_print_level(Print);

    if expected_lift_count eq 0 or #prime_reduced_units eq 0 then
        return 0;
    end if;

    sample_prime_unit_count := Minimum(#prime_reduced_units, 5);
    sample_lift_count := 0;
    sample_timer := Cputime();

    for i in [1..sample_prime_unit_count] do
        sample_units := [];
        append_lifts_of_prime_unit(
            reduced_algebra,
            scalar_fibers,
            prime_reduced_units[i],
            ~sample_units,
            0
        );
        sample_lift_count +:= #sample_units;
    end for;

    sample_elapsed := Cputime(sample_timer);
    estimated_seconds := 0;

    if sample_lift_count gt 0 and sample_elapsed gt 0 then
        estimated_seconds := (expected_lift_count * sample_elapsed) / sample_lift_count;
    end if;

    if print_is_concise(Print) then
        print "[PUG estimate]", label,
              "| elements=", expected_lift_count,
              "| lift_s=", estimated_seconds;
    end if;

    return estimated_seconds;
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
    time_limit_seconds := 300,
    expected_scalar_unit_order := 0
)
    Print := validate_print_level(Print);
    time_limit_seconds := validate_time_limit_seconds(time_limit_seconds);
    prime_ideal, k := prime_power_data_from_ideal(modulus_ideal);
    one_algebra := reduced_order_identity(order_data, reduction_map, reduced_algebra);

    if k eq 1 then
        estimated_seconds := estimate_isunit_enumeration(
            reduced_algebra,
            (#reduced_base_ring)^4,
            "O/P^kO (field quotient)" :
            Print := Print
        );
        if time_limit_exceeded(time_limit_seconds, estimated_seconds) then
            return false, false, false, estimated_seconds, true;
        end if;
        reduced_units := [u : u in reduced_algebra | IsUnit(u)];

        estimated_scalar_seconds := estimate_isunit_enumeration(
            reduced_base_ring,
            #reduced_base_ring,
            "(R/P^k)^*" :
            Print := Print
        );
        if time_limit_exceeded(time_limit_seconds, estimated_seconds + estimated_scalar_seconds) then
            return false, false, false, estimated_seconds + estimated_scalar_seconds, true;
        end if;
        scalar_units := [a : a in reduced_base_ring | IsUnit(a)];
        if expected_scalar_unit_order ne 0 and #scalar_units ne expected_scalar_unit_order then
            error "Scalar-unit count did not match the expected size of (R / P^k)^*.";
        end if;
        scalars := {a * one_algebra : a in scalar_units};
        return reduced_units, scalar_units, scalars, estimated_seconds + estimated_scalar_seconds, false;
    end if;

    // The ideal P O / P^k O is nilpotent, so an element of O / P^k O is a
    // unit if and only if its reduction modulo P is a unit.
    prime_reduced_algebra, prime_reduced_base_ring, prime_reduction_map :=
        build_reduced_algebra(order_data, prime_ideal);
    estimated_prime_unit_seconds := estimate_isunit_enumeration(
        prime_reduced_algebra,
        (#prime_reduced_base_ring)^4,
        "O/PO (unit test for P^k lift)" :
        Print := Print
    );
    if time_limit_exceeded(time_limit_seconds, estimated_prime_unit_seconds) then
        return false, false, false, estimated_prime_unit_seconds, true;
    end if;
    prime_reduced_units := [u : u in prime_reduced_algebra | IsUnit(u)];
    prime_unit_lookup := element_sequence_lookup(prime_reduced_units);

    scalar_fibers := scalar_prime_reduction_fibers(
        order_data`integer_ring,
        reduced_base_ring,
        reduction_map,
        prime_reduced_base_ring,
        prime_reduction_map
    );
    expected_lifts_per_prime_unit := #scalar_prime_fiber(
        scalar_fibers,
        prime_reduced_base_ring!0
    )^4;
    expected_reduced_unit_count_from_lifts := #prime_reduced_units * expected_lifts_per_prime_unit;
    estimated_order_seconds := estimated_prime_power_unit_lift_seconds(
        reduced_algebra,
        scalar_fibers,
        prime_reduced_units,
        expected_reduced_unit_count_from_lifts :
        Print := Print
    );
    estimated_scalar_seconds := 0;
    estimated_total_seconds := estimated_prime_unit_seconds + estimated_order_seconds + estimated_scalar_seconds;
    if time_limit_exceeded(time_limit_seconds, estimated_total_seconds) then
        return false, false, false, estimated_total_seconds, true;
    end if;

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

    return reduced_units, scalar_units, scalars, estimated_total_seconds, false;
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


function projective_class_key(reduced_element, scalars, class_key_data)
    if Type(class_key_data) eq Rec and assigned class_key_data`mode then
        if class_key_data`mode eq "split_prime_square" then
            return split_prime_square_projective_class_key(reduced_element, class_key_data);
        end if;

        error Sprintf("Unknown projective class-key mode %o.", class_key_data`mode);
    end if;

    return Sprint(canonical_orbit_representative(reduced_element, scalars));
end function;


// Report sampled progress often enough to be useful without flooding output.
function sampling_report_interval()
    return 20;
end function;


// Deterministic index sweep used before falling back to an exhaustive scan.
function sampled_index_order(num_items)
    if num_items le 1 then
        return [];
    end if;

    max_base := Max(2, Floor(Log(2, num_items)));
    sampled_indices := [];
    used_indices := AssociativeArray();

    for base in Reverse([2..max_base]) do
        index := base;
        while index le num_items do
            if not IsDefined(used_indices, index) then
                used_indices[index] := true;
                Append(~sampled_indices, index);
            end if;
            index *:= base;
        end while;
    end for;

    return sampled_indices;
end function;


// Extrapolate a total runtime from partial sampled work.
function estimated_seconds_from_progress(elapsed_seconds, completed_steps, total_steps)
    if completed_steps le 0 or elapsed_seconds le 0 then
        return 0;
    end if;

    return (total_steps * elapsed_seconds) / completed_steps;
end function;


// Build the projective classes with a sampled sweep before the full scan.
function projective_class_data(reduced_units, scalars, num_classes : Print := 0, time_limit_seconds := 300)
    Print := validate_print_level(Print);
    time_limit_seconds := validate_time_limit_seconds(time_limit_seconds);
    total_units := #reduced_units;
    report_interval := sampling_report_interval();
    sampled_indices := sampled_index_order(total_units);
    sampled_index_set := AssociativeArray();
    class_representatives := [];
    class_index_by_key := AssociativeArray();
    timer := Cputime();
    checked_units := 0;

    for index in sampled_indices do
        sampled_index_set[index] := true;
        checked_units +:= 1;
        representative := canonical_orbit_representative(reduced_units[index], scalars);
        representative_key := Sprint(representative);

        if not IsDefined(class_index_by_key, representative_key) then
            Append(~class_representatives, representative);
            class_index_by_key[representative_key] := #class_representatives;
        end if;

        if ((checked_units mod report_interval eq 0) or
            (#class_representatives eq num_classes) or
            (checked_units eq total_units)) then
            estimated_seconds := estimated_seconds_from_progress(Cputime(timer), checked_units, total_units);

            if print_is_concise(Print) then
                print "[PUG estimate] projective_classes | checked=", checked_units, "/", total_units,
                      "| found=", #class_representatives, "/", num_classes,
                      "| seconds=", estimated_seconds;
            end if;

            if time_limit_exceeded(time_limit_seconds, estimated_seconds) then
                return false, false, true, estimated_seconds;
            end if;
        end if;

        if #class_representatives eq num_classes then
            break;
        end if;
    end for;

    if #class_representatives ne num_classes then
        if print_is_detailed(Print) then
            print "[PUG sampled] projective_classes | fallback=exhaustive";
        end if;

        for index in [1..total_units] do
            if IsDefined(sampled_index_set, index) then
                continue;
            end if;

            checked_units +:= 1;
            representative := canonical_orbit_representative(reduced_units[index], scalars);
            representative_key := Sprint(representative);

            if not IsDefined(class_index_by_key, representative_key) then
                Append(~class_representatives, representative);
                class_index_by_key[representative_key] := #class_representatives;
            end if;

            if ((checked_units mod report_interval eq 0) or
                (#class_representatives eq num_classes) or
                (checked_units eq total_units)) then
                estimated_seconds := estimated_seconds_from_progress(Cputime(timer), checked_units, total_units);

                if print_is_concise(Print) then
                    print "[PUG estimate] projective_classes | checked=", checked_units, "/", total_units,
                          "| found=", #class_representatives, "/", num_classes,
                          "| seconds=", estimated_seconds;
                end if;

                if time_limit_exceeded(time_limit_seconds, estimated_seconds) then
                    return false, false, true, estimated_seconds;
                end if;
            end if;

            if #class_representatives eq num_classes then
                break;
            end if;
        end for;
    elif print_is_detailed(Print) then
        print "[PUG sampled] projective_classes | fallback=not_needed";
    end if;

    return class_representatives, class_index_by_key, false, 0;
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
    Print := 0,
    time_limit_seconds := 0
)
    Print := validate_print_level(Print);
    time_limit_seconds := validate_time_limit_seconds(time_limit_seconds);
    timer := Cputime();
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
    prime_class_index_by_key,
    prime_projective_class_skipped,
    prime_projective_class_estimated_seconds := projective_class_data(
        prime_reduced_units,
        prime_scalars,
        prime_num_classes :
        Print := 0,
        time_limit_seconds := time_limit_seconds
    );

    if prime_projective_class_skipped then
        return false, false, false, true, prime_projective_class_estimated_seconds;
    end if;

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
    report_interval := sampling_report_interval();
    checked_prime_classes := 0;

    for prime_class_index in [1..#prime_class_representatives] do
        checked_prime_classes +:= 1;
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

        if ((checked_prime_classes mod report_interval eq 0) or
            (checked_prime_classes eq #prime_class_representatives)) then
            estimated_seconds := estimated_seconds_from_progress(
                Cputime(timer),
                checked_prime_classes,
                #prime_class_representatives
            );

            if print_is_concise(Print) then
                print "[PUG estimate] split_prime_square_classes | prime_classes=",
                      checked_prime_classes, "/", #prime_class_representatives,
                      "| found=", #class_representatives, "/", expected_projective_group_order,
                      "| seconds=", estimated_seconds;
            end if;

            if time_limit_exceeded(time_limit_seconds, estimated_seconds) then
                return false, false, false, true, estimated_seconds;
            end if;
        end if;
    end for;

    if #class_representatives ne expected_projective_group_order then
        error Sprintf(
            "Split prime-square projective class construction found %o classes, expected %o.",
            #class_representatives,
            expected_projective_group_order
        );
    end if;

    return class_representatives,
           class_index_by_key,
           class_key_data,
           false,
           Cputime(timer);
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


function estimate_left_action_permutation_seconds(
    g,
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data :
    sample_size := 200
)
    num_classes := #class_representatives;

    if num_classes eq 0 then
        return 0;
    end if;

    sample_size := Minimum(sample_size, num_classes);
    timer := Cputime();

    for i in [1..sample_size] do
        product := reduced_algebra!g * reduced_algebra!class_representatives[i];
        image_key := projective_class_key(product, scalars, class_key_data);

        if not IsDefined(class_index_by_key, image_key) then
            error "Left-action sample product not found in class representatives.";
        end if;
    end for;

    sample_elapsed := Cputime(timer);

    if sample_elapsed eq 0 then
        return 0;
    end if;

    return (num_classes * sample_elapsed) / sample_size;
end function;


// Find generators of the projective model with the sampled sweep first.
// The returned maps are caches that start from sampled generators and grow as
// specific projective lifts are needed later on.
function sampled_generator_permutation_data(
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data,
    reduced_identity :
    Print := 0,
    time_limit_seconds := 300
)
    Print := validate_print_level(Print);
    time_limit_seconds := validate_time_limit_seconds(time_limit_seconds);
    num_classes := #class_representatives;
    symmetric_group := Sym(num_classes);
    report_interval := (num_classes ge 100000) select 1 else sampling_report_interval();
    sampled_indices := sampled_index_order(num_classes);
    sampled_index_set := AssociativeArray();
    reduced_to_permutation := AssociativeArray();
    permutation_to_reduced := AssociativeArray();
    generator_permutations := [];
    trial_group := sub<symmetric_group | >;
    checked_representatives := 0;
    timer := Cputime();

    if num_classes eq 0 then
        return reduced_to_permutation, permutation_to_reduced, generator_permutations, trial_group, 0, false;
    end if;

    one_key := projective_class_key(reduced_identity, scalars, class_key_data);
    if not IsDefined(class_index_by_key, one_key) then
        error "The projective unit model does not contain the identity class.";
    end if;
    one_representative := class_representatives[class_index_by_key[one_key]];
    one_permutation := Identity(symmetric_group);
    cache_orbit_permutation(
        reduced_algebra,
        scalars,
        one_representative,
        one_permutation,
        ~reduced_to_permutation,
        ~permutation_to_reduced
    );

    if #sampled_indices gt 0 then
        preflight_estimated_seconds := estimate_left_action_permutation_seconds(
            class_representatives[sampled_indices[1]],
            reduced_algebra,
            class_representatives,
            class_index_by_key,
            scalars,
            class_key_data
        );
        preflight_stage_estimated_seconds := 2 * preflight_estimated_seconds;

        if print_is_concise(Print) then
            print "[PUG estimate] permutation_model | one_action_seconds=",
                  preflight_estimated_seconds,
                  "| stage_seconds=", preflight_stage_estimated_seconds;
        end if;

        if time_limit_exceeded(time_limit_seconds, preflight_stage_estimated_seconds) then
            return reduced_to_permutation,
                   permutation_to_reduced,
                   generator_permutations,
                   trial_group,
                   preflight_stage_estimated_seconds,
                   true;
        end if;
    end if;

    for index in sampled_indices do
        sampled_index_set[index] := true;
        checked_representatives +:= 1;
        representative := class_representatives[index];
        representative_permutation := left_action_permutation(
            representative,
            reduced_algebra,
            class_representatives,
            class_index_by_key,
            scalars,
            class_key_data
        );
        Append(~generator_permutations, representative_permutation);
        trial_group := sub<symmetric_group | generator_permutations>;
        cache_orbit_permutation(
            reduced_algebra,
            scalars,
            representative,
            representative_permutation,
            ~reduced_to_permutation,
            ~permutation_to_reduced
        );

        if ((checked_representatives mod report_interval eq 0) or
            (#trial_group eq num_classes) or
            (checked_representatives eq num_classes)) then
            estimated_seconds := estimated_seconds_from_progress(Cputime(timer), checked_representatives, num_classes);

            if print_is_concise(Print) then
                print "[PUG estimate] permutation_model | checked=", checked_representatives, "/", num_classes,
                      "| G_try=", #trial_group, "/", num_classes,
                      "| seconds=", estimated_seconds;
            end if;

            if time_limit_exceeded(time_limit_seconds, estimated_seconds) then
                return reduced_to_permutation,
                       permutation_to_reduced,
                       generator_permutations,
                       trial_group,
                       estimated_seconds,
                       true;
            end if;
        end if;

        if #trial_group eq num_classes then
            break;
        end if;
    end for;

    if #trial_group ne num_classes then
        if print_is_detailed(Print) then
            print "[PUG sampled] permutation_model | fallback=exhaustive";
        end if;

        for index in [1..num_classes] do
            if IsDefined(sampled_index_set, index) then
                continue;
            end if;

            checked_representatives +:= 1;
            representative := class_representatives[index];
            representative_permutation := left_action_permutation(
                representative,
                reduced_algebra,
                class_representatives,
                class_index_by_key,
                scalars,
                class_key_data
            );
            Append(~generator_permutations, representative_permutation);
            trial_group := sub<symmetric_group | generator_permutations>;
            cache_orbit_permutation(
                reduced_algebra,
                scalars,
                representative,
                representative_permutation,
                ~reduced_to_permutation,
                ~permutation_to_reduced
            );

            if ((checked_representatives mod report_interval eq 0) or
                (#trial_group eq num_classes) or
                (checked_representatives eq num_classes)) then
                estimated_seconds := estimated_seconds_from_progress(Cputime(timer), checked_representatives, num_classes);

                if print_is_concise(Print) then
                    print "[PUG estimate] permutation_model | checked=", checked_representatives, "/", num_classes,
                          "| G_try=", #trial_group, "/", num_classes,
                          "| seconds=", estimated_seconds;
                end if;

                if time_limit_exceeded(time_limit_seconds, estimated_seconds) then
                    return reduced_to_permutation,
                           permutation_to_reduced,
                           generator_permutations,
                           trial_group,
                           estimated_seconds,
                           true;
                end if;
            end if;

            if #trial_group eq num_classes then
                break;
            end if;
        end for;
    elif print_is_detailed(Print) then
        print "[PUG sampled] permutation_model | fallback=not_needed";
    end if;

    return reduced_to_permutation,
           permutation_to_reduced,
           generator_permutations,
           trial_group,
           estimated_seconds_from_progress(Cputime(timer), checked_representatives, num_classes),
           false;
end function;


// Enforce the assumption that the order data was built over a number field.
procedure validate_number_field(base_field)
    if Type(base_field) ne FldNum and Type(base_field) ne FldRat then
        error "order_data`base_field must be a number field or the rational field. Build the order data with order_data_from_index or build_order_data_for_order.";
    end if;
end procedure;


// Reduce a stored order element modulo P^k using the principal basis of O.
function reduce_order_element_mod_modulus(order_data, element_x, reduction_map, reduced_algebra)
    base_field := order_data`base_field;
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    principal_basis := order_data`principal_basis;
    coordinates := coordinates_in_basis(base_field, quaternion_algebra, principal_basis, element_x);
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


// Replace an ambient algebra element by a primitive integral order representative.
function primitive_integral_order_representative(order_data, element_x)
    return integral_normalizer_representative(
        order_data`base_field,
        order_data`integer_ring,
        order_data`quaternion_algebra,
        order_data`quaternion_order,
        order_data`principal_basis,
        element_x
    );
end function;


// Build a fast lookup table for reduced units by coefficient sequence.
function reduced_unit_lookup(reduced_units)
    return rec<reduced_unit_membership_format |
        mode := "explicit",
        lookup := element_sequence_lookup(reduced_units)
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
    base_field := order_data`base_field;
    quaternion_algebra := order_data`quaternion_algebra;
    principal_basis := order_data`principal_basis;
    reduced_key := Eltseq(reduced_element);

    if not IsDefined(reduced_to_permutation, reduced_key) then
        source_coordinates := coordinates_in_basis(
            base_field,
            quaternion_algebra,
            principal_basis,
            source_element
        );
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


// Record projective lifts of unit-group generators.
function unit_lifts_in_projective_group(order_data, reduced_algebra, reduction_map, scalar_units)
    reduced_unit_lifts := AssociativeArray();

    for i in [1..Ngens(order_data`unit_group)] do
        unit_u := primitive_integral_order_representative(
            order_data,
            order_data`unit_map(order_data`unit_group.i)
        );
        ok, unit_reduced, message := reduce_order_element_mod_modulus(
            order_data,
            unit_u,
            reduction_map,
            reduced_algebra
        );

        if not ok then
            error message;
        end if;

        for scalar in scalar_units do
            reduced_unit_lifts[scalar * unit_reduced] := unit_u;
        end for;
    end for;

    return reduced_unit_lifts;
end function;


// Recover the unique principal two-sided O-ideal above a ramified prime P.
function ramified_base_generator(order_data, prime_ideal)
    if order_data`order_type lt 2 then
        error "The ramified extension is only defined for Eichler orders.";
    end if;

    if order_data`class_number ne 1 then
        error "The ramified extension is only implemented for class-number-one Eichler orders.";
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

        generator := primitive_integral_order_representative(order_data, generator);
        normalized_generator := normalize_quaternion_element(quaternion_algebra, generator);
        normalized_key := Sprint(Eltseq(normalized_generator));

        if not IsDefined(normalized_lookup, normalized_key) then
            normalized_lookup[normalized_key] := true;
            Append(~candidate_generators, generator);
        end if;
    end for;

    if #candidate_generators ne 1 then
        error Sprintf(
            "Expected exactly one principal two-sided generator above %o, but found %o candidates.",
            prime_ideal,
            #candidate_generators
        );
    end if;

    return candidate_generators[1];
end function;


// Reduce the basis-conjugation action x -> a x a^-1 to O / P^k O.
function ramified_conjugation_basis_images(order_data, conjugating_element, reduction_map)
    base_field := order_data`base_field;
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
        image_coordinates := coordinates_in_basis(
            base_field,
            quaternion_algebra,
            principal_basis,
            conjugated_basis_element
        );
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
    point_group_elements := [Identity(projective_unit_group) : i in [1..num_classes]];
    filled_points := {};

    for model_element in projective_unit_group do
        point_index := identity_index^model_element;
        point_group_elements[point_index] := model_element;
        Include(~filled_points, point_index);
    end for;

    if #filled_points ne num_classes then
        error "The projective unit model did not act regularly on its projective classes.";
    end if;

    permutation_entries := [];

    for point_index in [1..num_classes] do
        product_element := group_element * point_group_elements[point_index];
        Append(~permutation_entries, identity_index^product_element);
    end for;

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
    base_field := order_data`base_field;
    principal_basis := order_data`principal_basis;
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
        coordinates_in_basis(base_field, quaternion_algebra, principal_basis, ramified_generator_squared)[i] eq 0 :
        i in [2..4]
    ];
    ramified_generator_square_reduction_source := primitive_integral_order_representative(
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
    base_field := order_data`base_field;
    quaternion_algebra := order_data`quaternion_algebra;
    principal_basis := order_data`principal_basis;
    ramified_generator_squared := (quaternion_algebra!ramified_generator_element)^2;
    ramified_generator_squared_coordinates := coordinates_in_basis(
        base_field,
        quaternion_algebra,
        principal_basis,
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


// Record which reduced projective classes come from the stored normalizer.
function normalizer_lifts_in_projective_group(order_data, reduced_algebra, reduction_map, scalar_units)
    normalizer_reduced_lifts := AssociativeArray();

    for normalizer_element in order_data`normalizer_elements do
        ok, reduced_element, message := reduce_order_element_mod_modulus(
            order_data,
            normalizer_element,
            reduction_map,
            reduced_algebra
        );

        if not ok then
            error message;
        end if;

        for scalar in scalar_units do
            normalizer_reduced_lifts[scalar * reduced_element] := normalizer_element;
        end for;
    end for;

    return normalizer_reduced_lifts;
end function;


// Convert reduced projective lifts into permutations of the projective model.
procedure append_permutations_from_reduced_lifts(
    order_data,
    reduced_algebra,
    class_representatives,
    class_index_by_key,
    scalars,
    class_key_data,
    reduced_lifts,
    label,
    ~permutations,
    ~reduced_to_permutation,
    ~permutation_to_reduced
)
    for reduced_element in Keys(reduced_lifts) do
        cached_permutation := false;
        cached_projective_permutation(
            order_data,
            reduced_algebra,
            class_representatives,
            class_index_by_key,
            scalars,
            class_key_data,
            reduced_element,
            reduced_lifts[reduced_element],
            label,
            ~cached_permutation,
            ~reduced_to_permutation,
            ~permutation_to_reduced
        );
        Append(~permutations, cached_permutation);
    end for;
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

    unit_component := primitive_integral_order_representative(
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


// Store complement classes as the subgroup-class records returned by Magma.
function complement_classes(group_g, subgroup_k)
    group_order := #group_g;
    subgroup_order := #subgroup_k;

    if group_order mod subgroup_order ne 0 then
        return [];
    end if;

    target_order := group_order div subgroup_order;
    subgroup_classes := Subgroups(group_g : OrderEqual := target_order);
    complements := [];

    for subgroup_class in subgroup_classes do
        complement_subgroup := subgroup_class`subgroup;

        // Keep the full subgroup-class record, but only when the representative
        // subgroup is actually a complement of subgroup_k.
        if #complement_subgroup * subgroup_order ne group_order then
            continue;
        end if;

        if #(complement_subgroup meet subgroup_k) eq 1 then
            Append(~complements, subgroup_class);
        end if;
    end for;

    return complements;
end function;


// Keep only the complement classes whose representative subgroup is normal.
function normal_complement_classes(group_g, complement_list)
    return [complement_class : complement_class in complement_list | IsNormal(group_g, complement_class`subgroup)];
end function;


// Build G = (O / P^k O)^* / (R / P^k)^* together with the unit and normalizer images.
function build_projective_unit_group(
    order_data,
    prime_ideal,
    k :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    compute_complements := true
)
    Print := validate_print_level(Print);
    time_limit_seconds := validate_time_limit_seconds(time_limit_seconds);
    max_projective_quotient_seconds := validate_estimated_time_control(
        max_projective_quotient_seconds,
        "max_projective_quotient_seconds"
    );
    max_reduced_unit_seconds := validate_estimated_time_control(
        max_reduced_unit_seconds,
        "max_reduced_unit_seconds"
    );
    if Type(compute_complements) ne BoolElt then
        error "compute_complements must be true or false.";
    end if;
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    validate_number_field(order_data`base_field);

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
    reduced_unit_time_limit_seconds := effective_stage_time_limit_seconds(
        "reduced_units",
        k,
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );
    projective_quotient_time_limit_seconds := effective_stage_time_limit_seconds(
        "projective_quotient",
        k,
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );
    timer := Cputime();

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

    use_split_prime_square_model :=
        k eq 2 and
        local_maximal_at_prime and
        (not prime_ramified_in_algebra);

    if use_split_prime_square_model then
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
        class_key_data,
        projective_class_skipped,
        projective_class_estimated_seconds := split_prime_square_projective_class_data(
            order_data,
            prime_ideal,
            reduced_algebra,
            reduced_base_ring,
            reduction_map,
            scalar_fibers,
            scalar_units,
            scalars,
            expected_projective_group_order :
            Print := Print,
            time_limit_seconds := projective_quotient_time_limit_seconds
        );
        estimated_reduced_unit_seconds := 0;
        num_classes := projective_formula_known select expected_projective_group_order else #class_representatives;
    else
        class_key_data := false;
        reduced_units, scalar_units, scalars, estimated_reduced_unit_seconds, reduced_unit_skipped :=
            reduced_unit_data(
                order_data,
                modulus_ideal,
                reduced_base_ring,
                reduced_algebra,
                reduction_map :
                Print := Print,
                time_limit_seconds := reduced_unit_time_limit_seconds,
                expected_scalar_unit_order := expected_scalar_unit_count
            );

        if reduced_unit_skipped then
            if print_is_concise(Print) then
                print "[PUG skip]", ideal_summary("modulus", modulus_ideal),
                      "| task=reduced_units",
                      "| estimated_seconds=", estimated_reduced_unit_seconds;
            end if;

            return rec<projective_unit_group_format |
                order_data := order_data,
                prime_ideal := prime_ideal,
                prime_power_exponent := k,
                modulus_ideal := modulus_ideal,
                elapsed_seconds := Cputime(timer),
                estimated_reduced_unit_seconds := estimated_reduced_unit_seconds,
                estimated_permutation_seconds := 0,
                prime_ramified_in_algebra := prime_ramified_in_algebra,
                local_maximal_at_prime := local_maximal_at_prime,
                formula_case := formula_case,
                expected_projective_group_order := expected_projective_group_order,
                expected_scalar_unit_order := expected_scalar_unit_count,
                expected_reduced_unit_order := expected_reduced_unit_count,
                reduced_base_ring := reduced_base_ring,
                reduced_algebra := reduced_algebra,
                reduction_map := reduction_map,
                normalizer_image_defined := false,
                ramified_extension_defined := false,
                complements_computed := false,
                skipped_due_to_estimate := true,
                skipped_task_key := "reduced_units",
                skipped_estimated_seconds := estimated_reduced_unit_seconds
            >;
        end if;

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
        class_representatives, class_index_by_key, projective_class_skipped, projective_class_estimated_seconds := projective_class_data(
            reduced_units,
            scalars,
            num_classes :
            Print := Print,
            time_limit_seconds := projective_quotient_time_limit_seconds
        );
    end if;

    if projective_class_skipped then
        if print_is_concise(Print) then
            print "[PUG skip]", ideal_summary("modulus", modulus_ideal),
                  "| task=projective_classes",
                  "| estimated_seconds=", projective_class_estimated_seconds;
        end if;

        return rec<projective_unit_group_format |
            order_data := order_data,
            prime_ideal := prime_ideal,
            prime_power_exponent := k,
            modulus_ideal := modulus_ideal,
            elapsed_seconds := Cputime(timer),
            estimated_reduced_unit_seconds := estimated_reduced_unit_seconds,
            estimated_permutation_seconds := 0,
            prime_ramified_in_algebra := prime_ramified_in_algebra,
            local_maximal_at_prime := local_maximal_at_prime,
            formula_case := formula_case,
            expected_projective_group_order := expected_projective_group_order,
            expected_scalar_unit_order := expected_scalar_unit_count,
            expected_reduced_unit_order := expected_reduced_unit_count,
            reduced_base_ring := reduced_base_ring,
            reduced_algebra := reduced_algebra,
            reduction_map := reduction_map,
            reduced_unit_membership := reduced_unit_membership_data,
            reduced_units := reduced_units,
            scalar_units := scalar_units,
            scalars := scalars,
            class_index_by_key := class_index_by_key,
            class_key_data := class_key_data,
            normalizer_image_defined := false,
            ramified_extension_defined := false,
            complements_computed := false,
            skipped_due_to_estimate := true,
            skipped_task_key := "projective_classes",
            skipped_estimated_seconds := projective_class_estimated_seconds
        >;
    end if;

    if #class_representatives ne num_classes then
        error "Failed to recover the expected number of projective classes.";
    end if;

    // Seed the projective model from sampled generators and enlarge the cache
    // later only for unit and normalizer classes that we actually use.
    reduced_to_permutation,
    permutation_to_reduced,
    generator_permutations,
    projective_unit_group,
    estimated_permutation_seconds,
    permutation_model_skipped := sampled_generator_permutation_data(
        reduced_algebra,
        class_representatives,
        class_index_by_key,
        scalars,
        class_key_data,
        reduced_identity :
        Print := Print,
        time_limit_seconds := projective_quotient_time_limit_seconds
    );

    if permutation_model_skipped then
        if print_is_concise(Print) then
            print "[PUG skip]", ideal_summary("modulus", modulus_ideal),
                  "| task=permutation_model",
                  "| estimated_seconds=", estimated_permutation_seconds;
        end if;

        return rec<projective_unit_group_format |
            order_data := order_data,
            prime_ideal := prime_ideal,
            prime_power_exponent := k,
            modulus_ideal := modulus_ideal,
            elapsed_seconds := Cputime(timer),
            estimated_reduced_unit_seconds := estimated_reduced_unit_seconds,
            estimated_permutation_seconds := estimated_permutation_seconds,
            prime_ramified_in_algebra := prime_ramified_in_algebra,
            local_maximal_at_prime := local_maximal_at_prime,
            formula_case := formula_case,
            expected_projective_group_order := expected_projective_group_order,
            expected_scalar_unit_order := expected_scalar_unit_count,
            expected_reduced_unit_order := expected_reduced_unit_count,
            reduced_base_ring := reduced_base_ring,
            reduced_algebra := reduced_algebra,
            reduction_map := reduction_map,
            reduced_unit_membership := reduced_unit_membership_data,
            reduced_units := reduced_units,
            scalar_units := scalar_units,
            scalars := scalars,
            class_representatives := class_representatives,
            class_index_by_key := class_index_by_key,
            class_key_data := class_key_data,
            normalizer_image_defined := false,
            ramified_extension_defined := false,
            complements_computed := false,
            skipped_due_to_estimate := true,
            skipped_task_key := "permutation_model",
            skipped_estimated_seconds := estimated_permutation_seconds
        >;
    end if;

    if #projective_unit_group ne num_classes then
        error "Generated projective group not of the correct size.";
    end if;

    reduced_unit_lifts := unit_lifts_in_projective_group(
        order_data,
        reduced_algebra,
        reduction_map,
        scalar_units
    );

    unit_image_permutations := [];
    append_permutations_from_reduced_lifts(
        order_data,
        reduced_algebra,
        class_representatives,
        class_index_by_key,
        scalars,
        class_key_data,
        reduced_unit_lifts,
        "unit",
        ~unit_image_permutations,
        ~reduced_to_permutation,
        ~permutation_to_reduced
    );
    unit_image_subgroup := sub<projective_unit_group | unit_image_permutations>;
    if compute_complements then
        unit_complements := complement_classes(projective_unit_group, unit_image_subgroup);
        normal_unit_complements := normal_complement_classes(projective_unit_group, unit_complements);
    else
        unit_complements := [];
        normal_unit_complements := [];
    end if;

    reduced_unit_lookup_data := reduced_unit_membership_data;

    // At split primes the normalizer image is computed inside G. At ramified
    // primes of class-number-one Eichler orders we enlarge the ambient group to
    // the doubled ramified extension generated by G and one ramified normalizer
    // element.
    split_normalizer_image_defined :=
        (order_data`order_type ge 2) and
        (not prime_ramified_in_algebra) and
        (not prime_divides_order_discriminant);
    ramified_extension_defined :=
        (order_data`order_type ge 2) and
        prime_ramified_in_algebra and
        (order_data`class_number eq 1);
    normalizer_image_defined := split_normalizer_image_defined or ramified_extension_defined;
    normalizer_ambient_group := false;
    normalizer_image_map := false;
    normalizer_reduced_lifts := AssociativeArray();
    normalizer_image_permutations := [];
    normalizer_image_subgroup := false;
    normalizer_complements := [];
    normal_normalizer_complements := [];
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
        normalizer_reduced_lifts := normalizer_lifts_in_projective_group(
            order_data,
            reduced_algebra,
            reduction_map,
            scalar_units
        );
    end if;

    if normalizer_image_defined then
        normalizer_generator_images := [];
        for i in [1..Ngens(order_data`normalizer_group)] do
            if print_is_concise(Print) then
                print "[PUG] normalizer_generator_image", i, "/", Ngens(order_data`normalizer_group);
            end if;
            generator_element := primitive_integral_order_representative(
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

        normalizer_image_permutations := normalizer_generator_images;
        normalizer_image_subgroup := sub<normalizer_ambient_group | normalizer_image_permutations>;
        if compute_complements then
            normalizer_complements := complement_classes(normalizer_ambient_group, normalizer_image_subgroup);
            normal_normalizer_complements := normal_complement_classes(normalizer_ambient_group, normalizer_complements);
        else
            normalizer_complements := [];
            normal_normalizer_complements := [];
        end if;

        normalizer_image_map := hom<order_data`normalizer_group -> normalizer_ambient_group | normalizer_generator_images>;
    end if;

    elapsed_seconds := Cputime(timer);

    if print_is_concise(Print) then
        if normalizer_image_defined then
            print "[PUG] summary | elapsed_s=", elapsed_seconds,
                  "| G_size=", #projective_unit_group,
                  "| unit_image_size=", #unit_image_subgroup,
                  "| unit_complements=", #unit_complements,
                  "| normal_unit_complements=", #normal_unit_complements,
                  "| ramified_generator_square_is_scalar=", ramified_generator_square_is_scalar,
                  "| normalizer_ambient_size=", #normalizer_ambient_group,
                  "| normalizer_image_size=", #normalizer_image_subgroup,
                  "| normalizer_complements=", #normalizer_complements,
                  "| normal_normalizer_complements=", #normal_normalizer_complements;
        else
            print "[PUG] summary | elapsed_s=", elapsed_seconds,
                  "| G_size=", #projective_unit_group,
                  "| unit_image_size=", #unit_image_subgroup,
                  "| unit_complements=", #unit_complements,
                  "| normal_unit_complements=", #normal_unit_complements,
                  "| normalizer_image=undefined";
        end if;
    end if;

    return rec<projective_unit_group_format |
        order_data := order_data,
        prime_ideal := prime_ideal,
        prime_power_exponent := k,
        modulus_ideal := modulus_ideal,
        elapsed_seconds := elapsed_seconds,
        estimated_reduced_unit_seconds := estimated_reduced_unit_seconds,
        estimated_permutation_seconds := estimated_permutation_seconds,
        prime_ramified_in_algebra := prime_ramified_in_algebra,
        local_maximal_at_prime := local_maximal_at_prime,
        formula_case := formula_case,
        expected_projective_group_order := expected_projective_group_order,
        expected_scalar_unit_order := expected_scalar_unit_count,
        expected_reduced_unit_order := expected_reduced_unit_count,
        reduced_base_ring := reduced_base_ring,
        reduced_algebra := reduced_algebra,
        reduction_map := reduction_map,
        reduced_unit_membership := reduced_unit_membership_data,
        reduced_units := reduced_units,
        scalar_units := scalar_units,
        scalars := scalars,
        class_representatives := class_representatives,
        class_index_by_key := class_index_by_key,
        class_key_data := class_key_data,
        reduced_to_permutation := reduced_to_permutation,
        permutation_to_reduced := permutation_to_reduced,
        reduced_unit_lifts := reduced_unit_lifts,
        projective_unit_group := projective_unit_group,
        unit_image_permutations := unit_image_permutations,
        unit_image_subgroup := unit_image_subgroup,
        unit_complements := unit_complements,
        normal_unit_complements := normal_unit_complements,
        normalizer_image_defined := normalizer_image_defined,
        normalizer_ambient_group := normalizer_ambient_group,
        normalizer_image_map := normalizer_image_map,
        normalizer_reduced_lifts := normalizer_reduced_lifts,
        normalizer_image_permutations := normalizer_image_permutations,
        normalizer_image_subgroup := normalizer_image_subgroup,
        normalizer_complements := normalizer_complements,
        normal_normalizer_complements := normal_normalizer_complements,
        ramified_extension_defined := ramified_extension_defined,
        ramified_generator := ramified_generator_element,
        ramified_generator_square_is_scalar := ramified_generator_square_is_scalar,
        ramified_square_unit_permutation := ramified_square_unit_permutation,
        ramified_conjugation_permutation := ramified_conjugation_action,
        ramified_generator_permutation := ramified_generator_action,
        complements_computed := compute_complements,
        skipped_due_to_estimate := false,
        skipped_task_key := "",
        skipped_estimated_seconds := 0
    >;
end function;
