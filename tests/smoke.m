// Lightweight integration test for the complementary-triples loader and basic workflow.
//
// Run from the repository root:
//     magma tests/smoke.m

load "load.m";

procedure assert_true(condition, message)
    if not condition then
        error message;
    end if;
end procedure;

print "Complementary triples smoke test";

order_data := order_data_from_index(1);
assert_true(order_data`index eq 1, "order_data_from_index returned the wrong index.");
assert_true(order_data`label eq "main", "order_data_from_index should return the main order.");

R := order_data`integer_ring;
assert_true(ClassNumber(R) eq 1, "the package supports only class-number-one base fields.");

unit_data := compute_U_empty(order_data);
assert_true(unit_data`subgroup_order eq #order_data`unit_group, "U_empty subgroup order mismatch.");

P := ideal<R | 2>;
result := complementary_pairs_at_ideal(order_data, P : T := [], Print := 0);
assert_true(not result`skipped_due_to_estimate, "complementary_pairs_at_ideal skipped the basic test modulus.");
assert_true(result`complements_computed, "complementary_pairs_at_ideal did not compute complements.");

scan := scan_prime_power_complementary_triples(order_data, P, 1 : T := [], Print := 0);
assert_true(#scan`ideal_results eq 1, "prime-power scan should test exactly one modulus.");
assert_true(#scan`complementary_triples eq 1, "prime-power scan should record exactly one triple.");

group_mod_p2 := build_projective_unit_group(
    order_data,
    P,
    2 :
    Print := 0,
    compute_complements := false
);
assert_true(
    not group_mod_p2`skipped_due_to_estimate,
    "The P^2 projective unit group should not be skipped in the basic test case."
);
assert_true(
    #group_mod_p2`reduced_units eq group_mod_p2`expected_reduced_unit_order,
    "The nilpotent-lift unit enumeration should match the expected P^2 unit count."
);
assert_true(
    #group_mod_p2`scalar_units eq group_mod_p2`expected_scalar_unit_order,
    "The nilpotent-lift scalar-unit enumeration should match the expected P^2 scalar-unit count."
);

trivial_order_data := order_data_from_index(18);
trivial_scan := scan_order_for_complementary_triples(
    trivial_order_data,
    0 :
    Print := 0
);
assert_true(
    trivial_scan`trivial_unit_quotient,
    "The scan should still mark orders with trivial Gamma_emptyset."
);
assert_true(
    Type(trivial_scan`triple_data) ne MonStgElt,
    "A trivial Gamma_emptyset should no longer skip all nonempty T computations."
);
assert_true(
    #complementary_order_minimal_ideal_results(trivial_scan) eq
        2^#admissible_ramified_primes(trivial_order_data) - 1,
    "The scan should compute exactly the nonempty ramified T subsets for trivial Gamma_emptyset."
);

triples_header := complementary_triples_csv_header();
assert_true(
    Position(triples_header, "complement_index") gt 0,
    "The complementary-triples CSV should identify the complement class on each row."
);
assert_true(
    Position(triples_header, "local_norm_status") gt 0,
    "The complementary-triples CSV should include local-norm computation status."
);
assert_true(
    Position(triples_header, "local_norm_omega_representatives") gt 0,
    "The complementary-triples CSV should include the local-norm Theta representatives."
);
assert_true(
    Position(triples_header, "lifted_obstruction_theta_representatives") gt 0,
    "The complementary-triples CSV should include lifted torsion-obstruction representatives."
);

print "Complementary triples smoke test passed.";
