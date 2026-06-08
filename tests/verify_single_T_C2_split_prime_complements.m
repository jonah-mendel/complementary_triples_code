// Verification script for split-prime complementary triples in the single-T,
// order-two case.
//
// The script scans class-one maximal orders with Gamma_emptyset = 1, #T = 1,
// and Gamma_T isomorphic to C_2.  For each split prime P in the chosen norm
// range, it computes complements in G[P] and checks agreement with the
// criterion from Lemma triv-2:
//   - if Norm(P) is odd, a complement exists exactly when the reduced norm of
//     the nontrivial element of Gamma_T is a nonsquare modulo P;
//   - if Norm(P) is even, a complement exists exactly when Norm(P) = 2.
//
// Run from the repository root:
//     magma tests/verify_single_T_C2_split_prime_complements.m

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

if not assigned split_prime_norm_bound then
    split_prime_norm_bound := 17;
end if;

if not assigned calculation_Print then
    calculation_Print := 0;
end if;

if not assigned progress_Print then
    progress_Print := 1;
end if;

if not assigned max_reduced_unit_seconds then
    max_reduced_unit_seconds := 0;
end if;

if not assigned max_projective_quotient_seconds then
    max_projective_quotient_seconds := 0;
end if;


procedure assert_true(condition, message)
    if not condition then
        error message;
    end if;
end procedure;


function vcsp_group_type_string(group_g)
    try
        return Sprint(IdentifyGroup(group_g));
    catch error_object
        return "";
    end try;
end function;


function vcsp_is_target_localized_group(localized_group)
    return #localized_group`ramified_subset eq 1 and
           localized_group`subgroup_order eq 2 and
           vcsp_group_type_string(localized_group`subgroup) eq "<2, 1>";
end function;


function vcsp_sorted_ideals_by_norm(ideal_list)
    remaining := complementary_sorted_ideals(ideal_list);
    sorted_ideals := [];

    while #remaining gt 0 do
        minimal_index := 1;

        for i in [2..#remaining] do
            if Norm(remaining[i]) lt Norm(remaining[minimal_index]) then
                minimal_index := i;
            elif Norm(remaining[i]) eq Norm(remaining[minimal_index]) and
                  Sprint(remaining[i]) lt Sprint(remaining[minimal_index]) then
                minimal_index := i;
            end if;
        end for;

        Append(~sorted_ideals, remaining[minimal_index]);
        Remove(~remaining, minimal_index);
    end while;

    return sorted_ideals;
end function;


function vcsp_nontrivial_representative(context, localized_group)
    for group_element in localized_group`subgroup do
        if group_element ne Identity(localized_group`subgroup) then
            return complementary_normalizer_representative(context, group_element);
        end if;
    end for;

    error "Expected a nontrivial element of Gamma_T.";
end function;


function vcsp_square_status_mod_prime(order_data, prime_ideal, value)
    integer_ring := order_data`integer_ring;

    assert_true(
        value in integer_ring,
        "Expected the reduced norm representative to be integral."
    );

    residue_field, reduction_map := ResidueClassField(prime_ideal);
    residue_value := reduction_map(integer_ring!value);

    assert_true(
        residue_value ne residue_field!0,
        "Reduced norm should be nonzero modulo a split prime outside T."
    );

    return IsSquare(residue_value);
end function;


function vcsp_expected_complement_exists(order_data, representative, prime_ideal)
    prime_norm := Integers()!Norm(prime_ideal);

    if prime_norm mod 2 eq 0 then
        return prime_norm eq 2, "even norm";
    end if;

    reduced_norm := Norm(representative);
    is_square := vcsp_square_status_mod_prime(order_data, prime_ideal, reduced_norm);
    return not is_square, is_square select "odd square norm" else "odd nonsquare norm";
end function;


procedure vcsp_check_prime(
    ~context,
    order_data,
    localized_group,
    representative,
    prime_ideal,
    ~tested_count,
    ~expected_count,
    ~actual_count,
    ~failure_count,
    ~skipped_count,
    ~error_count
)
    tested_count +:= 1;

    try
        expected_exists, reason :=
            vcsp_expected_complement_exists(order_data, representative, prime_ideal);

        complementary_result := false;
        complementary_pairs_at_ideal_with_context(
            ~context,
            localized_group,
            prime_ideal,
            ~complementary_result :
            Print := calculation_Print,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );

        if complementary_result`skipped_due_to_estimate then
            skipped_count +:= 1;
            print Sprintf(
                "  SKIP: idx=%o | T=%o | P=%o | reason=estimated runtime",
                order_data`index,
                bct_ramified_subset_summary(localized_group`ramified_subset),
                bct_ideal_string(prime_ideal)
            );
            return;
        end if;

        actual_exists :=
            complementary_result`injective and
            complementary_result`complements_computed and
            #complementary_result`complement_classes gt 0;

        if expected_exists then
            expected_count +:= 1;
        end if;

        if actual_exists then
            actual_count +:= 1;
        end if;

        if expected_exists ne actual_exists then
            failure_count +:= 1;
            print Sprintf(
                "  FAIL: idx=%o | T=%o | P=%o | %o | expected=%o | actual=%o | injective=%o | complements=%o",
                order_data`index,
                bct_ramified_subset_summary(localized_group`ramified_subset),
                bct_ideal_string(prime_ideal),
                reason,
                expected_exists,
                actual_exists,
                complementary_result`injective,
                #complementary_result`complement_classes
            );
        elif progress_Print ge 2 then
            print Sprintf(
                "  pass: idx=%o | T=%o | P=%o | %o | complements=%o",
                order_data`index,
                bct_ramified_subset_summary(localized_group`ramified_subset),
                bct_ideal_string(prime_ideal),
                reason,
                #complementary_result`complement_classes
            );
        end if;
    catch error_object
        error_count +:= 1;
        print Sprintf(
            "  ERROR: idx=%o | T=%o | P=%o | message=%o",
            order_data`index,
            bct_ramified_subset_summary(localized_group`ramified_subset),
            bct_ideal_string(prime_ideal),
            Sprint(error_object`Object)
        );
    end try;
end procedure;


print "";
print "============================================================";
print "Verify Single-T C2 Split-Prime Complement Existence";
print "============================================================";
print "conditions:", "Gamma_emptyset = 1, #T = 1, Gamma_T = C_2";
print "split prime norm bound:", split_prime_norm_bound;
print "writes CSV:", "false";
print "";

orders_tested := 0;
orders_with_matching_T := 0;
matching_T_count := 0;
split_prime_count := 0;
expected_complement_count := 0;
actual_complement_count := 0;
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
    gamma_emptyset := false;
    complementary_localized_unit_group_from_subset(~context, [], ~gamma_emptyset);

    if gamma_emptyset`subgroup_order ne 1 then
        continue;
    end if;

    matching_T_for_order := 0;
    split_primes_for_order := 0;
    split_primes := vcsp_sorted_ideals_by_norm(split_primes_up_to(order_data, split_prime_norm_bound));

    for localized_group in localized_groups do
        if not vcsp_is_target_localized_group(localized_group) then
            continue;
        end if;

        matching_T_for_order +:= 1;
        matching_T_count +:= 1;
        representative := vcsp_nontrivial_representative(context, localized_group);

        for prime_ideal in split_primes do
            split_primes_for_order +:= 1;
            vcsp_check_prime(
                ~context,
                order_data,
                localized_group,
                representative,
                prime_ideal,
                ~split_prime_count,
                ~expected_complement_count,
                ~actual_complement_count,
                ~failure_count,
                ~skipped_count,
                ~error_count
            );
        end for;
    end for;

    if matching_T_for_order gt 0 then
        orders_with_matching_T +:= 1;

        if progress_Print ge 1 then
            print Sprintf(
                "idx=%o | n=%o | dK=%o | matching T=%o | split-prime tests=%o",
                idx,
                Degree(order_data`base_field),
                Discriminant(order_data`integer_ring),
                matching_T_for_order,
                split_primes_for_order
            );
        end if;
    end if;
end for;

print "";
print "============================================================";
print "Single-T C2 Split-Prime Complement Verification Complete";
print "============================================================";
print "orders tested:", orders_tested;
print "orders with matching T:", orders_with_matching_T;
print "matching T count:", matching_T_count;
print "split-prime tests:", split_prime_count;
print "expected complements:", expected_complement_count;
print "actual complements:", actual_complement_count;
print "failures:", failure_count;
print "skipped:", skipped_count;
print "errors:", error_count;

assert_true(failure_count eq 0, "A split-prime complement-existence mismatch was found.");
assert_true(skipped_count eq 0, "A split-prime complement-existence test was skipped.");
assert_true(error_count eq 0, "A split-prime complement-existence test errored.");

if matching_T_count eq 0 then
    print "PASS: no localized groups matched the target conditions.";
else
    print "PASS: direct complement computations agree with the split-prime criterion.";
end if;
