// Verification test for the lifted torsion obstruction.
//
// Run from the repository root:
//     magma tests/verify_lifted_torsion_obstruction.m

load "load.m";

procedure assert_true(condition, message)
    if not condition then
        error message;
    end if;
end procedure;

print "Lifted torsion obstruction test";

order_data := order_data_from_index(1);
R := order_data`integer_ring;
P := ideal<R | 2>;

result := complementary_pairs_at_ideal(
    order_data,
    P :
    T := [],
    Print := 0
);

assert_true(result`injective, "The basic lifted-obstruction example should be injective.");
assert_true(
    result`complements_computed and #result`complement_classes eq 1,
    "The basic lifted-obstruction example should have one complement class."
);

skip_reason := lifted_torsion_obstruction_skip_reason(result, 1);
assert_true(skip_reason eq "", "The lifted torsion obstruction should be eligible.");

summary := lifted_torsion_obstruction_summary(result, 1 : Print := 0);
assert_true(summary`prime_power_exponent eq 3, "The lifted obstruction should use P^3.");
assert_true(summary`norm eq 8, "The lifted obstruction modulus should have norm 8.");
assert_true(summary`delta_size eq 4, "The lifted Delta group should have four classes.");
assert_true(summary`omega_size eq 1, "The lifted obstruction should contain one class.");
assert_true(
    not summary`omega_contains_one,
    "The lifted obstruction should not contain the square class in this test case."
);

inverted_result := complementary_pairs_at_ideal(
    order_data,
    P :
    T := [P],
    Print := 0
);

skip_reason := lifted_torsion_obstruction_skip_reason(inverted_result, 1);
assert_true(
    skip_reason eq "modulus prime lies in T",
    "The lifted obstruction should skip inverted triples."
);

print "Lifted torsion obstruction test passed.";
