// Verification test for the Hurwitz and Lipschitz computations in the paper.
//
// This script uses explicit orders in (-1,-1 | Q), so it does not require
// Kirschmer's smalltypenumber.m data file.
//
// Run from the repository root:
//     magma tests/verify_hurwitz_lipschitz_computations.m

SetColumns(0);

// The core source files parse functions referring to OneClassGenera.  The
// explicit-order computations below do not use that table.
OneClassGenera := [];
load "src/order_data.m";
load "src/projective_unit_group.m";
load "src/arithmetic_utils.m";
load "src/complementary_ideals.m";
load "src/local_norm_pipeline.m";
load "src/lifted_torsion_obstruction.m";

procedure assert_true(condition, message)
    if not condition then
        error message;
    end if;
end procedure;

function group_type_string(group_g)
    try
        return Sprint(IdentifyGroup(group_g));
    catch error_object
        return "";
    end try;
end function;

function count_strings(values, target)
    count := 0;
    for value in values do
        if value eq target then
            count +:= 1;
        end if;
    end for;
    return count;
end function;

function order_element_from_reduced_element(group_model, reduced_element)
    order_data := group_model`order_data;
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    principal_basis := order_data`principal_basis;
    coordinates := [];

    for coordinate in Eltseq(reduced_element) do
        Append(~coordinates, integer_ring!(coordinate @@ group_model`reduction_map));
    end for;

    return quaternion_algebra!&+[coordinates[i] * principal_basis[i] : i in [1..4]];
end function;

function reduced_representative_for_projective_element(group_model, group_element)
    class_index_by_key := complementary_class_index_by_key(group_model);
    class_key_data := assigned group_model`class_key_data select
        group_model`class_key_data else false;
    reduced_identity := reduced_order_identity(
        group_model`order_data,
        group_model`reduction_map,
        group_model`reduced_algebra
    );
    identity_index := identity_class_index(
        reduced_identity,
        class_index_by_key,
        group_model`scalars,
        class_key_data
    );
    representative_index := identity_index^group_element;

    return group_model`class_representatives[representative_index];
end function;

function image_in_target_projective_group(source_model, target_model, source_group_element)
    source_reduced_element := reduced_representative_for_projective_element(
        source_model,
        source_group_element
    );
    order_element := order_element_from_reduced_element(source_model, source_reduced_element);
    image_permutation := false;
    complementary_projective_image_permutation(
        target_model,
        order_element,
        "comparison map",
        ~image_permutation
    );

    return image_permutation;
end function;

function subgroup_image_in_target_projective_group(source_model, target_model, source_subgroup)
    target_elements := [
        image_in_target_projective_group(source_model, target_model, g) :
        g in source_subgroup
    ];
    return sub<target_model`projective_unit_group | target_elements>;
end function;

function kernel_of_projective_reduction(source_model, target_model)
    target_identity := Identity(target_model`projective_unit_group);
    kernel_elements := [];

    for source_group_element in source_model`projective_unit_group do
        image_element := image_in_target_projective_group(
            source_model,
            target_model,
            source_group_element
        );
        if image_element eq target_identity then
            Append(~kernel_elements, source_group_element);
        end if;
    end for;

    return sub<source_model`projective_unit_group | kernel_elements>;
end function;

function subgroup_generated_by_order_element(group_model, order_element)
    image_permutation := false;
    complementary_projective_image_permutation(
        group_model,
        order_element,
        "explicit generator",
        ~image_permutation
    );
    return sub<group_model`projective_unit_group | image_permutation>;
end function;

function subgroup_occurs_in_complements(subgroup_h, complement_classes)
    for complement_class in complement_classes do
        if subgroup_h eq complement_class`subgroup then
            return true;
        end if;
    end for;
    return false;
end function;

function find_unique_complement_by_type(complement_classes, type_string)
    matches := [
        i : i in [1..#complement_classes] |
        group_type_string(complement_classes[i]`subgroup) eq type_string
    ];

    assert_true(
        #matches eq 1,
        Sprintf("Expected a unique complement of type %o.", type_string)
    );

    return matches[1], complement_classes[matches[1]]`subgroup;
end function;

function actual_reduced_trace_zero(quaternion_algebra, element_x)
    return Trace(quaternion_algebra!element_x) eq 0;
end function;

print "Hurwitz and Lipschitz verification";

Q := RationalsAsNumberField();
B<i, j> := QuaternionAlgebra< Q | -1, -1 >;
k := i * j;

// ------------------------------------------------------------------------
// Hurwitz order.
// ------------------------------------------------------------------------
O := Order([B!1, i, k, (1 + i + j + k) / 2]);
hurwitz_data := build_order_data_for_order(
    0,
    Q,
    B,
    O :
    label := "Hurwitz",
    order_type := 4,
    class_number := 1
);
R := hurwitz_data`integer_ring;
C2 := ideal<R | 2>;
C4 := ideal<R | 4>;

assert_true(Discriminant(O) eq C2, "The Hurwitz order should have discriminant (2).");
assert_true(#hurwitz_data`unit_group eq 12, "Gamma_{O,emptyset} should have order 12.");

hurwitz_mod_2 := complementary_pairs_at_ideal(hurwitz_data, C2 : T := [], Print := 0);
assert_true(hurwitz_mod_2`injective, "Gamma_{O,emptyset} should inject modulo 2.");
assert_true(
    #hurwitz_mod_2`image_subgroup eq #hurwitz_mod_2`ambient_group,
    "Reduction modulo 2 should identify Gamma_{O,emptyset} with G_O[2]."
);
assert_true(
    #hurwitz_mod_2`complement_classes eq 1 and
    #hurwitz_mod_2`complement_classes[1]`subgroup eq 1,
    "The complementary triple (emptyset, 2, {1}) should occur."
);

hurwitz_mod_4 := complementary_pairs_at_ideal(hurwitz_data, C4 : T := [], Print := 0);
assert_true(hurwitz_mod_4`injective, "Gamma_{O,emptyset} should inject modulo 4.");
assert_true(
    #hurwitz_mod_4`complement_classes eq 3,
    "Expected three complement classes for the Hurwitz order modulo 4."
);

hurwitz_complement_types := [
    group_type_string(complement_class`subgroup) :
    complement_class in hurwitz_mod_4`complement_classes
];
assert_true(count_strings(hurwitz_complement_types, "<8, 2>") eq 1, "Expected one C2 x C4 complement.");
assert_true(count_strings(hurwitz_complement_types, "<8, 5>") eq 1, "Expected one elementary abelian complement.");
assert_true(count_strings(hurwitz_complement_types, "<8, 3>") eq 1, "Expected one dihedral complement.");

H1_index, H1 := find_unique_complement_by_type(hurwitz_mod_4`complement_classes, "<8, 2>");
H2_index, H2 := find_unique_complement_by_type(hurwitz_mod_4`complement_classes, "<8, 5>");
H3_index, H3 := find_unique_complement_by_type(hurwitz_mod_4`complement_classes, "<8, 3>");

H1_theta := local_norm_summary_for_complementary_result(hurwitz_mod_4, H1_index : Print := 0);
H2_theta := local_norm_summary_for_complementary_result(hurwitz_mod_4, H2_index : Print := 0);
H3_theta := local_norm_summary_for_complementary_result(hurwitz_mod_4, H3_index : Print := 0);
assert_true(H1_theta`omega_size eq 0, "Expected Theta_4(H1) to be empty.");
assert_true(
    H2_theta`omega_size eq 1 and not H2_theta`omega_contains_one,
    "Expected Theta_4(H2) to be the nonsquare class."
);
assert_true(
    H3_theta`omega_size eq 2 and H3_theta`omega_contains_one,
    "Expected Theta_4(H3) to contain both square classes."
);

hurwitz_model_2 := complementary_prime_power_group_model(hurwitz_mod_2);
hurwitz_model_4 := complementary_prime_power_group_model(hurwitz_mod_4);
kernel_4_to_2 := kernel_of_projective_reduction(hurwitz_model_4, hurwitz_model_2);
assert_true(H2 eq kernel_4_to_2, "The elementary abelian complement should be ker(G_O[4] -> G_O[2]).");

print "  Hurwitz order checks passed.";

// ------------------------------------------------------------------------
// Lipschitz order.
// ------------------------------------------------------------------------
L := Order([B!1, i, j, k]);
lipschitz_data := build_order_data_for_order(
    0,
    Q,
    B,
    L :
    label := "Lipschitz",
    order_type := 1,
    class_number := 1
);
RL := lipschitz_data`integer_ring;
CL2 := ideal<RL | 2>;
CL4 := ideal<RL | 4>;

assert_true(Discriminant(L) eq ideal<RL | 4>, "The Lipschitz order should have discriminant (4).");
assert_true(#lipschitz_data`unit_group eq 4, "Gamma_{L,emptyset} should have order 4.");
assert_true(group_type_string(lipschitz_data`unit_group) eq "<4, 2>", "Gamma_{L,emptyset} should be C2 x C2.");

lipschitz_mod_2 := complementary_pairs_at_ideal(lipschitz_data, CL2 : T := [], Print := 0);
assert_true(lipschitz_mod_2`injective, "Gamma_{L,emptyset} should inject modulo 2.");
assert_true(#lipschitz_mod_2`ambient_group eq 8, "G_L[2] should have order 8.");
assert_true(group_type_string(lipschitz_mod_2`ambient_group) eq "<8, 5>", "G_L[2] should be elementary abelian.");
assert_true(#lipschitz_mod_2`complement_classes eq 4, "Expected four complements for L modulo 2.");

lipschitz_model_2 := complementary_prime_power_group_model(lipschitz_mod_2);
K_generators := [i + j + k, 1 + i + j, 1 + i + k, 1 + j + k];
K_subgroups := [subgroup_generated_by_order_element(lipschitz_model_2, generator) : generator in K_generators];

for subgroup_h in K_subgroups do
    assert_true(
        subgroup_occurs_in_complements(subgroup_h, lipschitz_mod_2`complement_classes),
        "One of the displayed Lipschitz complements was not found."
    );
end for;

assert_true(
    actual_reduced_trace_zero(B, K_generators[1]),
    "K1 should be generated by a trace-zero representative."
);
for generator_index in [2..4] do
    assert_true(
        not actual_reduced_trace_zero(B, K_generators[generator_index]),
        "K2, K3, and K4 should be generated by representatives of nonzero trace."
    );
end for;

// The map iota_1: G_L[2] -> G_O[2] has kernel K1.
kernel_iota_1 := kernel_of_projective_reduction(lipschitz_model_2, hurwitz_model_2);
assert_true(kernel_iota_1 eq K_subgroups[1], "The kernel of iota_1 should be K1.");

// The complements lifting K2, K3, and K4 to G_L[4] map to the conjugacy
// class represented by H1 in G_O[4].
lipschitz_mod_4 := complementary_pairs_at_ideal(lipschitz_data, CL4 : T := [], Print := 0);
lipschitz_model_4 := complementary_prime_power_group_model(lipschitz_mod_4);

for generator_index in [2..4] do
    lifts := [];
    for complement_class in lipschitz_mod_4`complement_classes do
        image_mod_2 := subgroup_image_in_target_projective_group(
            lipschitz_model_4,
            lipschitz_model_2,
            complement_class`subgroup
        );
        if image_mod_2 eq K_subgroups[generator_index] then
            Append(~lifts, complement_class`subgroup);
        end if;
    end for;

    assert_true(
        #lifts ge 1,
        Sprintf("No lift of K%o to G_L[4] was found.", generator_index)
    );

    found_h1_image := false;
    for lift_subgroup in lifts do
        image_in_hurwitz := subgroup_image_in_target_projective_group(
            lipschitz_model_4,
            hurwitz_model_4,
            lift_subgroup
        );
        if IsConjugate(hurwitz_model_4`projective_unit_group, image_in_hurwitz, H1) then
            found_h1_image := true;
            break;
        end if;
    end for;
    assert_true(
        found_h1_image,
        Sprintf("No lift of K%o mapped to a conjugate of H1 in G_O[4].", generator_index)
    );
end for;

print "  Lipschitz order checks passed.";
print "Hurwitz and Lipschitz verification passed.";
