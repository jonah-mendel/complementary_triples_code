// Recompute the presentation displayed in Example ex:torsion-free-77 of the
// paper.
//
// The example uses K = Q(sqrt(2)), the definite quaternion algebra with
// discriminant p_2 p_9, a maximal order O, the complementary triple
// (T,C,H) with T = emptyset and C = p_2, and S equal to the two split
// primes above 7.
//
// The script also checks the local torsion test used in the example:
// no selected generator and no product a_i b_j is one of the candidate
// edge- or face-inverting torsion elements.
//
// Run from the repository root:
//     magma examples/example_presentation_qsqrt2_d18_p2_S7split.m

load "load.m";


// ---------------------------------------------------------------------------
// User-editable inputs.
// ---------------------------------------------------------------------------

if not assigned ORDER_INDEX then
    ORDER_INDEX := 1118;
end if;

if not assigned S_RATIONAL_PRIME then
    S_RATIONAL_PRIME := 7;
end if;

if not assigned NORMAL_ONLY then
    NORMAL_ONLY := false;
end if;

if not assigned COMPLEMENT_SELECTOR then
    COMPLEMENT_SELECTOR := 1;
end if;

if not assigned MINIMAL_RELATIONS then
    MINIMAL_RELATIONS := true;
end if;

if not assigned COMPLEMENT_PRINT_LEVEL then
    COMPLEMENT_PRINT_LEVEL := 0;
end if;

if not assigned PRESENTATION_PRINT_LEVEL then
    PRESENTATION_PRINT_LEVEL := 1;
end if;

if not assigned SHOW_RELATIONS then
    SHOW_RELATIONS := true;
end if;

if not assigned SHOW_GENERATOR_REPRESENTATIVES then
    SHOW_GENERATOR_REPRESENTATIVES := true;
end if;


// ---------------------------------------------------------------------------
// Helpers.
// ---------------------------------------------------------------------------

procedure assert_true(condition, message)
    if not condition then
        error message;
    end if;
end procedure;


function ideal_line(label, ideal_x)
    has_generator, generator := IsPrincipal(ideal_x);
    if has_generator then
        return Sprintf("%o: norm=%o | generator=%o", label, Norm(ideal_x), generator);
    end if;

    return Sprintf("%o: norm=%o | generator unavailable", label, Norm(ideal_x));
end function;


procedure print_paper_generator_aliases(presentation, first_prefix, second_prefix)
    print "";
    print "============================================================";
    print "Paper generator aliases";
    print "============================================================";
    print Sprintf("S[1] generators are written %o_i in the paper.", first_prefix);
    print Sprintf("S[2] generators are written %o_j in the paper.", second_prefix);
    print "The deterministic order below is the order used by this script.";
    print "";

    for generator_data in presentation`presentation_generator_data do
        alias_prefix := generator_data`s_index eq 1 select first_prefix else second_prefix;
        alias := Sprintf("%o_%o", alias_prefix, generator_data`generator_index);
        print Sprintf(
            "%o = %o | %o | coordinates=%o | quaternion=%o",
            alias,
            generator_data`label,
            ideal_summary("P", generator_data`prime_ideal),
            presentation_coordinate_list_string(generator_data`principal_basis_coordinates),
            generator_data`quaternion_representative
        );
    end for;
end procedure;


// ---------------------------------------------------------------------------
// Build the order and complementary triple.
// ---------------------------------------------------------------------------

print "Presentation example: K=Q(sqrt(2)), D(B)=p_2 p_9, T=empty, C=p_2, S={p_7,q_7}";

order_data := order_data_from_index(ORDER_INDEX);
R := order_data`integer_ring;
B := order_data`quaternion_algebra;

assert_true(Degree(order_data`base_field) eq 2, "Expected [K:Q] = 2.");
assert_true(Discriminant(R) eq 8, "Expected K = Q(sqrt(2)), so d_K = 8.");
assert_true(Norm(Discriminant(B)) eq 18, "Expected D(B) = 18.");

prime_over_2_factors := Factorization(ideal<R | 2>);
assert_true(#prime_over_2_factors eq 1, "Expected a unique prime above 2.");
C := prime_over_2_factors[1][1];
assert_true(Norm(C) eq 2, "Expected C to have norm 2.");

prime_over_7_factors := Factorization(ideal<R | S_RATIONAL_PRIME>);
S := [factor[1] : factor in prime_over_7_factors];
assert_true(#S eq 2, "Expected two distinct primes above 7.");
assert_true(&and[Norm(P) eq 7 : P in S], "Expected both S-primes to have norm 7.");

print "";
print "Order and modulus:";
print "  order index:", ORDER_INDEX;
print "  d_K:", Discriminant(R);
print "  D(B):", Discriminant(B);
print "  " cat ideal_line("C=P_2", C);
print "  T: empty";
print "  S:";
for i in [1..#S] do
    print Sprintf("    S[%o] %o", i, ideal_line("P", S[i]));
end for;

complementary_result := complementary_pairs_at_ideal(
    order_data,
    C :
    T := [],
    Print := COMPLEMENT_PRINT_LEVEL
);

assert_true(not complementary_result`skipped_due_to_estimate, "Complement computation was skipped.");
assert_true(complementary_result`injective, "Gamma_emptyset should inject into G[C].");
assert_true(complementary_result`complements_computed, "Complements should be computed.");
assert_true(#complementary_result`complement_classes gt 0, "Expected at least one complement class.");

print "";
print "Complement data:";
print "  complement class count:", #complementary_result`complement_classes;
print "  normal complement class count:", #complementary_result`normal_complement_classes;
print "  selected complement:", COMPLEMENT_SELECTOR;


// ---------------------------------------------------------------------------
// Build and print the presentation.
// ---------------------------------------------------------------------------

presentation := build_presentation_for_complementary_result(
    complementary_result,
    S :
    normal_only := NORMAL_ONLY,
    complement_selector := COMPLEMENT_SELECTOR,
    minimal_relations := MINIMAL_RELATIONS,
    print_results := PRESENTATION_PRINT_LEVEL
);

assert_true(
    presentation`generators_torsion_free,
    "An edge-inverting generator candidate has order 2."
);
assert_true(
    #presentation`square_torsion eq 0,
    "A face-inverting candidate of the form a_i b_j has order 2."
);

print "";
print "Torsion checks from the presentation pipeline:";
print "  edge-inverting generator candidates: none have order 2";
print "  face-inverting candidates a_i b_j: none have order 2";

print_paper_generator_aliases(presentation, "a", "b");
print_presentation_summary(
    presentation,
    SHOW_RELATIONS,
    SHOW_GENERATOR_REPRESENTATIVES
);

print "";
print "The Magma variable `presentation` contains the presentation record.";
