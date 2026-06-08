// Verification test for split-prime injectivity when Gamma_emptyset is C_2.
//
// Claim checked:
//     if Gamma_emptyset is isomorphic to C_2, then
//     Gamma_emptyset -> G[P] is injective for every split prime P.
//
// The verification is finite.  For the nontrivial element of Gamma_emptyset,
// the script computes the finite set of split primes P at which a quaternion
// representative could become scalar modulo P.  Only these primes can cause
// non-injectivity.  Each candidate is then confirmed using the ordinary
// finite-quotient reduction machinery.  No CSV files are written.
//
// Run from the repository root:
//     magma tests/verify_gamma_emptyset_C2_split_injectivity.m

load "load.m";

// ========================================================================
// Edit inputs here.
// ========================================================================

if not assigned index_start then
    index_start := 1;
end if;

if not assigned index_stop then
    index_stop := #OneClassGenera;
end if;

if not assigned calculation_Print then
    calculation_Print := 0;
end if;

if not assigned progress_Print then
    progress_Print := 1;
end if;

if not assigned max_reduced_unit_seconds then
    max_reduced_unit_seconds := 1000;
end if;


procedure assert_true(condition, message)
    if not condition then
        error message;
    end if;
end procedure;


function vgec2_group_type_string(group_g)
    try
        return Sprint(IdentifyGroup(group_g));
    catch error_object
        return "";
    end try;
end function;


function vgec2_is_target_empty_group(localized_group)
    return localized_group`subgroup_order eq 2 and
           vgec2_group_type_string(localized_group`subgroup) eq "<2, 1>";
end function;


function vgec2_ideal_less_than(ideal_a, ideal_b)
    norm_a := Norm(ideal_a);
    norm_b := Norm(ideal_b);

    if norm_a ne norm_b then
        return norm_a lt norm_b;
    end if;

    return Sprint(ideal_a) lt Sprint(ideal_b);
end function;


function vgec2_sorted_ideals_by_norm(ideal_list)
    remaining := complementary_sorted_ideals(ideal_list);
    sorted_ideals := [];

    while #remaining gt 0 do
        minimal_index := 1;

        for i in [2..#remaining] do
            if vgec2_ideal_less_than(remaining[i], remaining[minimal_index]) then
                minimal_index := i;
            end if;
        end for;

        Append(~sorted_ideals, remaining[minimal_index]);
        Remove(~remaining, minimal_index);
    end while;

    return sorted_ideals;
end function;


function vgec2_ideal_sequence_string(ideal_list)
    return bct_ideal_sequence_string(vgec2_sorted_ideals_by_norm(ideal_list));
end function;


function vgec2_prime_ramifies(order_data, prime_ideal)
    return Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) ne 0;
end function;


function vgec2_coordinates_in_order_basis(order_data, element_x)
    coordinates := order_coordinates_in_basis(
        order_data`base_field,
        order_data`quaternion_algebra,
        order_data`principal_basis,
        element_x
    );

    integer_coordinates := [];
    for coefficient in coordinates do
        assert_true(
            coefficient in order_data`integer_ring,
            "Expected an integral order-basis coordinate."
        );
        Append(~integer_coordinates, order_data`integer_ring!coefficient);
    end for;

    return integer_coordinates;
end function;


function vgec2_scalar_collision_primes_for_element(order_data, element_x)
    integer_ring := order_data`integer_ring;
    one_coordinates := vgec2_coordinates_in_order_basis(
        order_data,
        order_data`quaternion_order!1
    );
    element_coordinates := vgec2_coordinates_in_order_basis(order_data, element_x);
    minors := [];

    for i in [1..#one_coordinates] do
        for j in [i + 1..#one_coordinates] do
            minor := one_coordinates[i] * element_coordinates[j] -
                     one_coordinates[j] * element_coordinates[i];
            if minor ne integer_ring!0 then
                Append(~minors, minor);
            end if;
        end for;
    end for;

    if #minors eq 0 then
        return [], true;
    end if;

    collision_ideal := ideal<integer_ring | minors>;

    if collision_ideal eq ideal<integer_ring | 1> then
        return [], false;
    end if;

    return vgec2_sorted_ideals_by_norm(
        [factor[1] : factor in Factorization(collision_ideal)]
    ), false;
end function;


procedure vgec2_add_candidate_prime(~candidate_primes, ~candidate_lookup, prime_ideal)
    key := Sprint(prime_ideal);

    if IsDefined(candidate_lookup, key) then
        return;
    end if;

    candidate_lookup[key] := true;
    Append(~candidate_primes, prime_ideal);
end procedure;


function vgec2_candidate_split_primes_for_group(order_data, context, localized_group)
    candidate_primes := [];
    candidate_lookup := AssociativeArray();
    scalar_representative_count := 0;
    nonidentity_element_count := 0;

    for group_element in localized_group`subgroup do
        if group_element eq Identity(localized_group`subgroup) then
            continue;
        end if;

        nonidentity_element_count +:= 1;
        representative := complementary_normalizer_representative(context, group_element);
        collision_primes, representative_is_scalar :=
            vgec2_scalar_collision_primes_for_element(order_data, representative);

        if representative_is_scalar then
            scalar_representative_count +:= 1;
            continue;
        end if;

        for prime_ideal in collision_primes do
            if not vgec2_prime_ramifies(order_data, prime_ideal) then
                vgec2_add_candidate_prime(~candidate_primes, ~candidate_lookup, prime_ideal);
            end if;
        end for;
    end for;

    return vgec2_sorted_ideals_by_norm(candidate_primes),
           scalar_representative_count,
           nonidentity_element_count;
end function;


procedure vgec2_confirm_candidate(
    ~context,
    localized_group,
    test_prime,
    ~pass_count,
    ~failure_count,
    ~skipped_count,
    ~error_count
)
    try
        local_result := false;
        complementary_local_reduction_image(
            ~context,
            localized_group,
            test_prime,
            1,
            ~local_result :
            Print := calculation_Print,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );

        if local_result`skipped_due_to_estimate then
            skipped_count +:= 1;
            print Sprintf(
                "  SKIP: P=%o, estimated_seconds=%o",
                bct_ideal_string(test_prime),
                local_result`skipped_estimated_seconds
            );
        elif local_result`injective then
            pass_count +:= 1;
            print Sprintf(
                "  pass: P=%o, image_order=%o",
                bct_ideal_string(test_prime),
                #local_result`image_subgroup
            );
        else
            failure_count +:= 1;
            print Sprintf(
                "  FAIL: P=%o, image_order=%o, source_order=%o",
                bct_ideal_string(test_prime),
                #local_result`image_subgroup,
                localized_group`subgroup_order
            );
        end if;
    catch error_object
        error_count +:= 1;
        print Sprintf(
            "  ERROR: P=%o, message=%o",
            bct_ideal_string(test_prime),
            Sprint(error_object`Object)
        );
    end try;
end procedure;


print "";
print "============================================================";
print "Verify Gamma_emptyset = C_2 Split-Prime Injectivity";
print "============================================================";
print "target Gamma_emptyset type:", "C_2";
print "prime filter:", "split primes only";
print "writes CSV:", "false";
print "";

orders_tested := 0;
target_order_count := 0;
candidate_prime_count := 0;
nonidentity_element_count := 0;
scalar_representative_count := 0;
pass_count := 0;
failure_count := 0;
skipped_count := 0;
error_count := 0;

for idx in [index_start..Min(index_stop, #OneClassGenera)] do
    entry := one_class_genera_entry(idx);

    if entry[6] ne 4 or entry[7] ne 1 then
        continue;
    end if;

    order_data := order_data_from_index(idx);
    orders_tested +:= 1;
    context := complementary_build_context(order_data);
    gamma_emptyset := false;
    complementary_localized_unit_group_from_subset(~context, [], ~gamma_emptyset);

    if not vgec2_is_target_empty_group(gamma_emptyset) then
        continue;
    end if;

    target_order_count +:= 1;
    candidate_primes, scalar_count_for_order, nonidentity_count_for_order :=
        vgec2_candidate_split_primes_for_group(order_data, context, gamma_emptyset);

    candidate_prime_count +:= #candidate_primes;
    scalar_representative_count +:= scalar_count_for_order;
    nonidentity_element_count +:= nonidentity_count_for_order;

    if progress_Print ge 1 then
        print Sprintf(
            "idx=%o | n=%o | dK=%o | D=%o | candidate split primes=%o",
            idx,
            Degree(order_data`base_field),
            Discriminant(order_data`integer_ring),
            bct_ideal_string(Discriminant(order_data`quaternion_algebra)),
            #candidate_primes
        );
        if #candidate_primes gt 0 then
            print "  candidates:", vgec2_ideal_sequence_string(candidate_primes);
        end if;
    end if;

    for test_prime in candidate_primes do
        vgec2_confirm_candidate(
            ~context,
            gamma_emptyset,
            test_prime,
            ~pass_count,
            ~failure_count,
            ~skipped_count,
            ~error_count
        );
    end for;
end for;

print "";
print "============================================================";
print "Gamma_emptyset = C_2 Split-Prime Injectivity Verification Complete";
print "============================================================";
print "orders tested:", orders_tested;
print "orders with Gamma_emptyset = C_2:", target_order_count;
print "nonidentity elements checked:", nonidentity_element_count;
print "scalar representatives:", scalar_representative_count;
print "candidate split primes:", candidate_prime_count;
print "confirmed passes:", pass_count;
print "failures:", failure_count;
print "skipped:", skipped_count;
print "errors:", error_count;

assert_true(target_order_count gt 0, "No maximal class-one orders had Gamma_emptyset = C_2.");
assert_true(scalar_representative_count eq 0, "A nonidentity Gamma_emptyset element had a scalar representative.");
assert_true(failure_count eq 0, "A split-prime injectivity failure was found.");
assert_true(skipped_count eq 0, "A split-prime injectivity test was skipped.");
assert_true(error_count eq 0, "A split-prime injectivity test errored.");

print "PASS: every candidate split prime was injective; all other split primes are excluded by the scalar-collision criterion.";
