// Verification test for split-prime injectivity in the single-T case with
// trivial Gamma_emptyset.
//
// Default claim checked:
//     if Gamma_emptyset = 1, #T = 1, and Gamma_T is isomorphic to C_2,
//     then Gamma_T -> G[P] is injective for every split prime P.
//
// The verification is finite.  For each matching Gamma_T, the script computes
// the finite set of split primes P for which some nontrivial element of
// Gamma_T could reduce to a scalar modulo P.  Only these primes can cause a
// failure of injectivity.  Each candidate is then confirmed using the ordinary
// finite-quotient reduction machinery.  No CSV files are written.
//
// Run from the repository root:
//     magma tests/verify_single_T_trivial_gamma_split_injectivity.m
//
// To run the vacuous Gamma_T = 1 check instead, run:
//     target_gamma_order := 1;
//     target_gamma_type := "";
//     load "tests/verify_single_T_trivial_gamma_split_injectivity.m";

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

if not assigned target_T_size then
    target_T_size := 1;
end if;

if not assigned target_empty_gamma_order then
    target_empty_gamma_order := 1;
end if;

if not assigned target_empty_gamma_type then
    target_empty_gamma_type := "";
end if;

if not assigned target_gamma_order then
    target_gamma_order := 2;
end if;

// Leave empty to filter only by order.  For C_2, use "<2, 1>".
if not assigned target_gamma_type then
    target_gamma_type := "<2, 1>";
end if;

if not assigned include_primes_in_T then
    include_primes_in_T := false;
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


function vstgi_group_type_string(group_g)
    try
        return Sprint(IdentifyGroup(group_g));
    catch error_object
        return "";
    end try;
end function;


function vstgi_group_matches_target(localized_group)
    if #localized_group`ramified_subset ne target_T_size then
        return false;
    end if;

    if localized_group`subgroup_order ne target_gamma_order then
        return false;
    end if;

    if target_gamma_type ne "" and
       vstgi_group_type_string(localized_group`subgroup) ne target_gamma_type then
        return false;
    end if;

    return true;
end function;


function vstgi_empty_group_matches_target(empty_group)
    if empty_group`subgroup_order ne target_empty_gamma_order then
        return false;
    end if;

    if target_empty_gamma_type ne "" and
       vstgi_group_type_string(empty_group`subgroup) ne target_empty_gamma_type then
        return false;
    end if;

    return true;
end function;


function vstgi_ideal_less_than(ideal_a, ideal_b)
    norm_a := Norm(ideal_a);
    norm_b := Norm(ideal_b);

    if norm_a ne norm_b then
        return norm_a lt norm_b;
    end if;

    return Sprint(ideal_a) lt Sprint(ideal_b);
end function;


function vstgi_sorted_ideals_by_norm(ideal_list)
    remaining := complementary_sorted_ideals(ideal_list);
    sorted_ideals := [];

    while #remaining gt 0 do
        minimal_index := 1;

        for i in [2..#remaining] do
            if vstgi_ideal_less_than(remaining[i], remaining[minimal_index]) then
                minimal_index := i;
            end if;
        end for;

        Append(~sorted_ideals, remaining[minimal_index]);
        Remove(~remaining, minimal_index);
    end while;

    return sorted_ideals;
end function;


function vstgi_ideal_sequence_string(ideal_list)
    return bct_ideal_sequence_string(vstgi_sorted_ideals_by_norm(ideal_list));
end function;


function vstgi_prime_ramifies(order_data, prime_ideal)
    return Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) ne 0;
end function;


function vstgi_prime_in_T(localized_group, prime_ideal)
    return Index(localized_group`ramified_subset, prime_ideal) ne 0;
end function;


function vstgi_prime_allowed(order_data, localized_group, prime_ideal)
    if vstgi_prime_ramifies(order_data, prime_ideal) then
        return false;
    end if;

    if (not include_primes_in_T) and vstgi_prime_in_T(localized_group, prime_ideal) then
        return false;
    end if;

    return true;
end function;


function vstgi_coordinates_in_order_basis(order_data, element_x)
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


function vstgi_scalar_collision_primes_for_element(order_data, element_x)
    integer_ring := order_data`integer_ring;
    one_coordinates := vstgi_coordinates_in_order_basis(
        order_data,
        order_data`quaternion_order!1
    );
    element_coordinates := vstgi_coordinates_in_order_basis(order_data, element_x);
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

    return vstgi_sorted_ideals_by_norm(
        [factor[1] : factor in Factorization(collision_ideal)]
    ), false;
end function;


procedure vstgi_add_candidate_prime(
    ~candidate_primes,
    ~candidate_lookup,
    ~source_count_lookup,
    prime_ideal
)
    key := Sprint(prime_ideal);

    if IsDefined(candidate_lookup, key) then
        source_count_lookup[key] := source_count_lookup[key] + 1;
        return;
    end if;

    candidate_lookup[key] := true;
    source_count_lookup[key] := 1;
    Append(~candidate_primes, prime_ideal);
end procedure;


function vstgi_candidate_split_primes_for_group(order_data, context, localized_group)
    candidate_primes := [];
    candidate_lookup := AssociativeArray();
    source_count_lookup := AssociativeArray();
    scalar_representative_count := 0;
    nonidentity_element_count := 0;

    for group_element in localized_group`subgroup do
        if group_element eq Identity(localized_group`subgroup) then
            continue;
        end if;

        nonidentity_element_count +:= 1;
        representative := complementary_normalizer_representative(context, group_element);
        collision_primes, representative_is_scalar :=
            vstgi_scalar_collision_primes_for_element(order_data, representative);

        if representative_is_scalar then
            scalar_representative_count +:= 1;
            continue;
        end if;

        for prime_ideal in collision_primes do
            if vstgi_prime_allowed(order_data, localized_group, prime_ideal) then
                vstgi_add_candidate_prime(
                    ~candidate_primes,
                    ~candidate_lookup,
                    ~source_count_lookup,
                    prime_ideal
                );
            end if;
        end for;
    end for;

    return vstgi_sorted_ideals_by_norm(candidate_primes),
           source_count_lookup,
           scalar_representative_count,
           nonidentity_element_count;
end function;


procedure vstgi_confirm_candidate(
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
                "  SKIP: T=%o, P=%o, estimated_seconds=%o",
                bct_ramified_subset_summary(localized_group`ramified_subset),
                bct_ideal_string(test_prime),
                local_result`skipped_estimated_seconds
            );
        elif local_result`injective then
            pass_count +:= 1;
            print Sprintf(
                "  pass: T=%o, P=%o, image_order=%o",
                bct_ramified_subset_summary(localized_group`ramified_subset),
                bct_ideal_string(test_prime),
                #local_result`image_subgroup
            );
        else
            failure_count +:= 1;
            print Sprintf(
                "  FAIL: T=%o, P=%o, image_order=%o, source_order=%o",
                bct_ramified_subset_summary(localized_group`ramified_subset),
                bct_ideal_string(test_prime),
                #local_result`image_subgroup,
                localized_group`subgroup_order
            );
        end if;
    catch error_object
        error_count +:= 1;
        print Sprintf(
            "  ERROR: T=%o, P=%o, message=%o",
            bct_ramified_subset_summary(localized_group`ramified_subset),
            bct_ideal_string(test_prime),
            Sprint(error_object`Object)
        );
    end try;
end procedure;


print "";
print "============================================================";
print "Verify Single-T Split-Prime Injectivity";
print "============================================================";
print "target #Gamma_emptyset:", target_empty_gamma_order;
print "target Gamma_emptyset type:", target_empty_gamma_type;
print "target #T:", target_T_size;
print "target #Gamma_T:", target_gamma_order;
print "target Gamma_T type:", target_gamma_type;
print "prime filter:", "split primes only";
print "writes CSV:", "false";
print "";

orders_tested := 0;
orders_with_matching_T := 0;
matching_T_count := 0;
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
    context, localized_groups := complementary_context_with_all_U_T(order_data);
    empty_group := false;
    complementary_localized_unit_group_from_subset(~context, [], ~empty_group);

    if not vstgi_empty_group_matches_target(empty_group) then
        continue;
    end if;

    order_matching_T_count := 0;
    order_candidate_count := 0;

    for localized_group in localized_groups do
        if not vstgi_group_matches_target(localized_group) then
            continue;
        end if;

        order_matching_T_count +:= 1;
        matching_T_count +:= 1;

        candidate_primes, source_count_lookup, scalar_count_for_T, nonidentity_count_for_T :=
            vstgi_candidate_split_primes_for_group(order_data, context, localized_group);

        order_candidate_count +:= #candidate_primes;
        candidate_prime_count +:= #candidate_primes;
        scalar_representative_count +:= scalar_count_for_T;
        nonidentity_element_count +:= nonidentity_count_for_T;

        if progress_Print ge 2 or #candidate_primes gt 0 then
            print Sprintf(
                "idx=%o | n=%o | dK=%o | T=%o | #Gamma_T=%o | nonidentity=%o | candidate split primes=%o",
                idx,
                Degree(order_data`base_field),
                Discriminant(order_data`integer_ring),
                bct_ramified_subset_summary(localized_group`ramified_subset),
                localized_group`subgroup_order,
                nonidentity_count_for_T,
                #candidate_primes
            );
            if #candidate_primes gt 0 then
                print "  candidates:", vstgi_ideal_sequence_string(candidate_primes);
            end if;
        end if;

        for test_prime in candidate_primes do
            vstgi_confirm_candidate(
                ~context,
                localized_group,
                test_prime,
                ~pass_count,
                ~failure_count,
                ~skipped_count,
                ~error_count
            );
        end for;
    end for;

    if order_matching_T_count gt 0 then
        orders_with_matching_T +:= 1;
        if progress_Print ge 1 then
            print Sprintf(
                "idx=%o | matching T=%o | candidate split primes=%o",
                idx,
                order_matching_T_count,
                order_candidate_count
            );
        end if;
    end if;
end for;

print "";
print "============================================================";
print "Single-T Split-Prime Injectivity Verification Complete";
print "============================================================";
print "orders tested:", orders_tested;
print "orders with matching T:", orders_with_matching_T;
print "matching T count:", matching_T_count;
print "nonidentity elements checked:", nonidentity_element_count;
print "scalar representatives:", scalar_representative_count;
print "candidate split primes:", candidate_prime_count;
print "confirmed passes:", pass_count;
print "failures:", failure_count;
print "skipped:", skipped_count;
print "errors:", error_count;

assert_true(failure_count eq 0, "A split-prime injectivity failure was found.");
assert_true(skipped_count eq 0, "A split-prime injectivity test was skipped.");
assert_true(error_count eq 0, "A split-prime injectivity test errored.");

if matching_T_count eq 0 then
    print "PASS: no localized groups matched the target conditions, so the statement is vacuous for this target.";
else
    print "PASS: every candidate split prime was injective; all other split primes are excluded by the scalar-collision criterion.";
end if;
