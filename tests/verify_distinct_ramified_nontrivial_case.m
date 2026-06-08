// Regression test for the nontrivial distinct-ramified singleton case.
//
// If two distinct primes P and Q ramify and Gamma_emptyset is trivial, then
// ({P}, Q, H) can still give a nontrivial complementary triple.  This verifies
// the representative case used in the paper.
//
// Run from the repository root:
//     magma tests/verify_distinct_ramified_nontrivial_case.m

load "load.m";

procedure assert_true(condition, message)
    if not condition then
        error message;
    end if;
end procedure;

function test_unique_prime_with_norm(prime_list, norm_value)
    matches := [P : P in prime_list | Norm(P) eq norm_value];

    if #matches ne 1 then
        error Sprintf("Expected a unique ramified prime of norm %o.", norm_value);
    end if;

    return matches[1];
end function;

print "Distinct ramified nontrivial complementary-triple test";

order_data := order_data_from_index(1125);
ramified_primes := admissible_ramified_primes(order_data);
P2 := test_unique_prime_with_norm(ramified_primes, 2);
P25 := test_unique_prime_with_norm(ramified_primes, 25);

context, localized_groups := complementary_context_with_all_U_T(order_data);
gamma_empty := false;

for localized_group in localized_groups do
    if #localized_group`ramified_subset eq 0 then
        gamma_empty := localized_group;
        break;
    end if;
end for;

assert_true(Type(gamma_empty) ne BoolElt, "Could not find Gamma_emptyset.");
assert_true(gamma_empty`subgroup_order eq 1, "Index 1125 should have trivial Gamma_emptyset.");

result_T_P2_mod_P25 := complementary_pairs_at_ideal(
    order_data,
    P25 :
    T := [P2],
    Print := 0
);

assert_true(
    result_T_P2_mod_P25`injective,
    "Gamma_{P2} should inject into G[P25]."
);
assert_true(
    result_T_P2_mod_P25`complements_computed,
    "Complements for Gamma_{P2} in G[P25] should be computed."
);
assert_true(
    #result_T_P2_mod_P25`complement_classes eq 1,
    "Gamma_{P2} should have one complement in G[P25]."
);
assert_true(
    #result_T_P2_mod_P25`normal_complement_classes eq 1,
    "The complement of Gamma_{P2} in G[P25] should be normal."
);

result_T_P25_mod_P2_square := complementary_pairs_at_ideal(
    order_data,
    P2^2 :
    T := [P25],
    Print := 0
);

assert_true(
    result_T_P25_mod_P2_square`injective,
    "Gamma_{P25} should inject into G[P2^2]."
);
assert_true(
    result_T_P25_mod_P2_square`complements_computed,
    "Complements for Gamma_{P25} in G[P2^2] should be computed."
);
assert_true(
    #result_T_P25_mod_P2_square`complement_classes eq 0,
    "Gamma_{P25} should have no complement in G[P2^2]."
);

print "Distinct ramified nontrivial complementary-triple test passed.";
