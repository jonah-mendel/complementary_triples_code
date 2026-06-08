// ============================================================================
// Direct local-norm obstruction pipeline.
//
// This module computes the trace and norm forms directly from an order basis
// omega_1, ..., omega_4:
//   Trd(sum X_i omega_i) = sum Trd(omega_i) X_i
//   Nrd(sum X_i omega_i) = sum Nrd(omega_i) X_i^2
//                        + sum_{i < j} Trd(omega_i * Conjugate(omega_j)) X_i X_j
//
// Main API:
// - local_norm_forms(order_data)
// - local_norm_summary_for_ramified_prime(order_data, prime_ideal :
//       Print := 1, time_limit_seconds := 300)
// - local_norm_projective_class_records_for_complementary_result(complementary_result, complement_index :
//       normal_only := false)
// - local_norm_summary_for_complementary_result(complementary_result, complement_index :
//       normal_only := false, Print := 1)
// - local_norm_run_for_order(order_data, norm_bound :
//       ramified_bound := 0, Print := 1, time_limit_seconds := 300)
// - local_norm_maximal_disjoint_subgroups(delta_group, omega_set)
// ============================================================================


local_norm_form_data_format := recformat<
    order_data,
    basis,
    trace_coefficients,
    norm_coefficient_matrix,
    norm_terms
>;


local_norm_reduced_form_data_format := recformat<
    form_data,
    modulus_ideal,
    reduced_base_ring,
    reduction_map,
    trace_coefficients,
    norm_terms
>;


local_norm_delta_data_format := recformat<
    integer_ring_residue_unit_group,
    integer_ring_residue_unit_map,
    square_subgroup,
    delta_group,
    delta_map,
    delta_elements,
    delta_representatives
>;


local_norm_projective_class_record_format := recformat<
    reduced_tuple,
    quaternion_representative,
    principal_basis_coordinates,
    trace_value,
    norm_value,
    trace_zero
>;


local_norm_summary_format := recformat<
    branch_kind,
    prime_ideal,
    prime_power_exponent,
    modulus_ideal,
    norm,
    group_model,
    complement_family,
    complement_index,
    complement_class,
    complement_subgroup,
    trace_form_coefficients,
    norm_form_terms,
    delta_representatives,
    delta_identity_representative,
    omega_representatives,
    omega_contains_one,
    maximal_psi_representatives,
    delta_size,
    omega_size,
    maximal_psi_count,
    projective_class_count,
    trace_zero_class_count
>;


local_norm_complement_bundle_format := recformat<
    group_model,
    complement_family,
    modulus_ideal,
    modulus_norm,
    complement_summaries
>;


local_norm_run_format := recformat<
    order_data,
    norm_bound,
    ramified_bound,
    complement_family,
    complement_bundles,
    ramified_summaries,
    skipped_estimated_tasks
>;


function local_norm_print_is_concise(Print)
    return Print ge 1;
end function;


function local_norm_print_is_detailed(Print)
    return Print ge 2;
end function;


function local_norm_join_with_separator(parts, separator)
    if #parts eq 0 then
        return "";
    end if;

    output := parts[1];
    for i in [2..#parts] do
        output cat:= separator cat parts[i];
    end for;

    return output;
end function;


function local_norm_string_lookup_values(lookup)
    keys := [key : key in Keys(lookup)];
    Sort(~keys);
    return [lookup[key] : key in keys];
end function;


function local_norm_sorted_sequence_by_string(elements)
    lookup := AssociativeArray();

    for element in elements do
        lookup[Sprint(element)] := element;
    end for;

    return local_norm_string_lookup_values(lookup);
end function;


function local_norm_sorted_sequences_by_string(sequences)
    lookup := AssociativeArray();

    for sequence_x in sequences do
        string_key := local_norm_join_with_separator([Sprint(x) : x in sequence_x], " | ");
        lookup[string_key] := sequence_x;
    end for;

    return local_norm_string_lookup_values(lookup);
end function;


function local_norm_first_equal_index(elements, target_element)
    for i in [1..#elements] do
        if elements[i] eq target_element then
            return i;
        end if;
    end for;

    return 0;
end function;


function local_norm_class_index_by_key(group_model)
    if assigned group_model`class_index_by_key then
        return group_model`class_index_by_key;
    end if;

    class_index_by_key := AssociativeArray();

    for i in [1..#group_model`class_representatives] do
        class_index_by_key[Sprint(group_model`class_representatives[i])] := i;
    end for;

    return class_index_by_key;
end function;


function local_norm_normalized_tuple(raw_tuple, target_ring)
    coordinates := Type(raw_tuple) eq SeqEnum select raw_tuple else Eltseq(raw_tuple);
    if #coordinates ne 4 then
        error "Expected a 4-coordinate tuple.";
    end if;

    return [target_ring!coordinate : coordinate in coordinates];
end function;


function local_norm_integral_scalar(integer_ring, scalar_x, label)
    if not (scalar_x in integer_ring) then
        error Sprintf("%o did not land in the integer ring.", label);
    end if;

    return integer_ring!scalar_x;
end function;


function local_norm_forms(order_data)
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    basis := order_data`principal_basis;

    trace_coefficients := [];
    norm_coefficient_matrix := [[integer_ring!0 : j in [1..4]] : i in [1..4]];
    norm_terms := [];

    for i in [1..4] do
        basis_element := quaternion_algebra!basis[i];
        trace_coefficient := local_norm_integral_scalar(
            integer_ring,
            Trace(basis_element),
            Sprintf("Trace coefficient %o", i)
        );
        norm_diagonal := local_norm_integral_scalar(
            integer_ring,
            Norm(basis_element),
            Sprintf("Norm coefficient (%o,%o)", i, i)
        );

        Append(~trace_coefficients, trace_coefficient);
        norm_coefficient_matrix[i][i] := norm_diagonal;
        if norm_diagonal ne 0 then
            Append(~norm_terms, <i, i, norm_diagonal>);
        end if;
    end for;

    for i in [1..4] do
        for j in [i + 1..4] do
            cross_coefficient := local_norm_integral_scalar(
                integer_ring,
                Trace((quaternion_algebra!basis[i]) * Conjugate(quaternion_algebra!basis[j])),
                Sprintf("Norm coefficient (%o,%o)", i, j)
            );
            norm_coefficient_matrix[i][j] := cross_coefficient;

            if cross_coefficient ne 0 then
                Append(~norm_terms, <i, j, cross_coefficient>);
            end if;
        end for;
    end for;

    return rec<local_norm_form_data_format |
        order_data := order_data,
        basis := basis,
        trace_coefficients := trace_coefficients,
        norm_coefficient_matrix := norm_coefficient_matrix,
        norm_terms := norm_terms
    >;
end function;


function local_norm_reduced_forms_for_modulus(order_data, modulus_ideal)
    form_data := local_norm_forms(order_data);
    _, reduced_base_ring, reduction_map := build_reduced_algebra(order_data, modulus_ideal);

    return rec<local_norm_reduced_form_data_format |
        form_data := form_data,
        modulus_ideal := modulus_ideal,
        reduced_base_ring := reduced_base_ring,
        reduction_map := reduction_map,
        trace_coefficients := [reduction_map(c) : c in form_data`trace_coefficients],
        norm_terms := [<term[1], term[2], reduction_map(term[3])> : term in form_data`norm_terms]
    >;
end function;


function local_norm_evaluate_with_coefficients(trace_coefficients, norm_terms, coordinates, target_ring)
    if #coordinates ne 4 then
        error "Expected four coordinates for local-norm evaluation.";
    end if;

    trace_value := target_ring!0;
    norm_value := target_ring!0;
    normalized_coordinates := [target_ring!coordinate : coordinate in coordinates];

    for i in [1..4] do
        trace_value +:= trace_coefficients[i] * normalized_coordinates[i];
    end for;

    for term in norm_terms do
        i := term[1];
        j := term[2];
        coefficient := term[3];
        norm_value +:= coefficient * normalized_coordinates[i] * normalized_coordinates[j];
    end for;

    return trace_value, norm_value;
end function;


function local_norm_evaluate_coordinates(form_data, coordinates)
    return local_norm_evaluate_with_coefficients(
        form_data`trace_coefficients,
        form_data`norm_terms,
        coordinates,
        form_data`order_data`integer_ring
    );
end function;


function local_norm_evaluate_reduced_tuple(reduced_form_data, reduced_tuple)
    return local_norm_evaluate_with_coefficients(
        reduced_form_data`trace_coefficients,
        reduced_form_data`norm_terms,
        local_norm_normalized_tuple(reduced_tuple, reduced_form_data`reduced_base_ring),
        reduced_form_data`reduced_base_ring
    );
end function;


function local_norm_order_element_from_reduced_tuple(order_data, reduction_map, reduced_tuple)
    integer_ring := order_data`integer_ring;
    coordinates := [integer_ring!(coordinate @@ reduction_map) : coordinate in reduced_tuple];

    return quaternion_from_principal_basis(
        order_data`quaternion_algebra,
        order_data`principal_basis,
        coordinates
    );
end function;


function local_norm_complement_classes_for_complementary_result(complementary_result, normal_only)
    if Type(normal_only) ne BoolElt then
        error "normal_only must be true or false.";
    end if;

    if complementary_result`skipped_due_to_estimate then
        error "Cannot compute local-norm data from a skipped complementary result.";
    end if;

    if not complementary_result`complements_computed then
        error "The complementary result does not have complement data.";
    end if;

    return normal_only select
        complementary_result`normal_complement_classes
    else
        complementary_result`complement_classes;
end function;


function local_norm_projective_class_tuples_for_subgroup(group_model, complement_subgroup)
    class_index_by_key := local_norm_class_index_by_key(group_model);
    reduced_identity := reduced_order_identity(
        group_model`order_data,
        group_model`reduction_map,
        group_model`reduced_algebra
    );
    identity_index := identity_class_index(
        reduced_identity,
        class_index_by_key,
        group_model`scalars,
        assigned group_model`class_key_data select group_model`class_key_data else false
    );

    point_indices := [];
    for subgroup_element in complement_subgroup do
        Append(~point_indices, identity_index^subgroup_element);
    end for;
    Sort(~point_indices);

    tuples := [];
    seen := {};
    for point_index in point_indices do
        if point_index lt 1 or point_index gt #group_model`class_representatives then
            error "Local-norm summaries are not implemented for complements whose orbit uses the ramified-extension ambient coset.";
        end if;

        tuple_x := local_norm_normalized_tuple(
            group_model`class_representatives[point_index],
            group_model`reduced_base_ring
        );
        tuple_key := Sprint(tuple_x);
        if tuple_key in seen then
            continue;
        end if;

        Include(~seen, tuple_key);
        Append(~tuples, tuple_x);
    end for;

    return tuples;
end function;


function local_norm_projective_class_record_from_tuple(group_model, reduced_form_data, reduced_tuple)
    order_data := group_model`order_data;
    base_field := order_data`base_field;
    quaternion_algebra := order_data`quaternion_algebra;
    quaternion_representative := local_norm_order_element_from_reduced_tuple(
        order_data,
        group_model`reduction_map,
        reduced_tuple
    );
    principal_basis_coordinates := coordinates_in_basis(
        base_field,
        quaternion_algebra,
        order_data`principal_basis,
        quaternion_representative
    );
    trace_value, norm_value := local_norm_evaluate_reduced_tuple(
        reduced_form_data,
        reduced_tuple
    );

    return rec<local_norm_projective_class_record_format |
        reduced_tuple := reduced_tuple,
        quaternion_representative := quaternion_representative,
        principal_basis_coordinates := principal_basis_coordinates,
        trace_value := trace_value,
        norm_value := norm_value,
        trace_zero := trace_value eq reduced_form_data`reduced_base_ring!0
    >;
end function;


function local_norm_projective_class_records_for_subgroup(group_model, complement_subgroup)
    reduced_form_data := local_norm_reduced_forms_for_modulus(
        group_model`order_data,
        group_model`modulus_ideal
    );
    tuples := local_norm_projective_class_tuples_for_subgroup(
        group_model,
        complement_subgroup
    );

    return [
        local_norm_projective_class_record_from_tuple(
            group_model,
            reduced_form_data,
            reduced_tuple
        ) :
        reduced_tuple in tuples
    ];
end function;


function local_norm_projective_class_records_for_complementary_result(
    complementary_result,
    complement_index :
    normal_only := false
)
    if Type(complement_index) ne RngIntElt or complement_index lt 1 then
        error "complement_index must be a positive integer.";
    end if;

    group_model := complementary_prime_power_group_model(complementary_result);
    complement_classes := local_norm_complement_classes_for_complementary_result(
        complementary_result,
        normal_only
    );

    if complement_index gt #complement_classes then
        error "complement_index is out of range for the stored complements.";
    end if;

    return local_norm_projective_class_records_for_subgroup(
        group_model,
        complement_classes[complement_index]`subgroup
    );
end function;


function local_norm_delta_data_for_reduced_base_ring(reduced_base_ring)
    integer_ring_residue_unit_group, integer_ring_residue_unit_map := UnitGroup(reduced_base_ring);
    square_generators := [2 * integer_ring_residue_unit_group.i : i in [1..Ngens(integer_ring_residue_unit_group)]];
    square_subgroup := #square_generators eq 0
        select sub<integer_ring_residue_unit_group | Identity(integer_ring_residue_unit_group)>
        else sub<integer_ring_residue_unit_group | square_generators>;
    delta_group, delta_map := quo<integer_ring_residue_unit_group | square_subgroup>;

    delta_elements := [];
    delta_representatives := [];

    for residue_group_element in integer_ring_residue_unit_group do
        delta_element := delta_map(residue_group_element);
        residue_representative := integer_ring_residue_unit_map(residue_group_element);
        delta_index := local_norm_first_equal_index(delta_elements, delta_element);

        if delta_index eq 0 then
            Append(~delta_elements, delta_element);
            Append(~delta_representatives, residue_representative);
        elif Sprint(residue_representative) lt Sprint(delta_representatives[delta_index]) then
            delta_representatives[delta_index] := residue_representative;
        end if;
    end for;

    representative_lookup := AssociativeArray();
    element_lookup := AssociativeArray();
    for i in [1..#delta_representatives] do
        representative_key := Sprint(delta_representatives[i]);
        representative_lookup[representative_key] := delta_representatives[i];
        element_lookup[representative_key] := delta_elements[i];
    end for;

    representative_keys := [key : key in Keys(representative_lookup)];
    Sort(~representative_keys);

    delta_representatives := [representative_lookup[key] : key in representative_keys];
    delta_elements := [element_lookup[key] : key in representative_keys];

    return rec<local_norm_delta_data_format |
        integer_ring_residue_unit_group := integer_ring_residue_unit_group,
        integer_ring_residue_unit_map := integer_ring_residue_unit_map,
        square_subgroup := square_subgroup,
        delta_group := delta_group,
        delta_map := delta_map,
        delta_elements := delta_elements,
        delta_representatives := delta_representatives
    >;
end function;


function local_norm_subgroup_is_contained(subgroup_h, subgroup_k)
    for i in [1..Ngens(subgroup_h)] do
        if not (subgroup_h.i in subgroup_k) then
            return false;
        end if;
    end for;

    return true;
end function;


function local_norm_maximal_disjoint_subgroups(delta_group, omega_set)
    if Type(omega_set) eq SeqEnum then
        omega_elements := omega_set;
    elif Type(omega_set) eq GrpAb then
        omega_elements := [omega_element : omega_element in omega_set];
    else
        error "omega_set must be a sequence or an abelian subgroup.";
    end if;

    for omega_element in omega_elements do
        if omega_element eq Identity(delta_group) then
            return [];
        end if;
    end for;

    valid_subgroups := [];
    for subgroup_class in Subgroups(delta_group) do
        subgroup_x := subgroup_class`subgroup;
        disjoint := true;

        for omega_element in omega_elements do
            if omega_element in subgroup_x then
                disjoint := false;
                break;
            end if;
        end for;

        if disjoint then
            Append(~valid_subgroups, subgroup_x);
        end if;
    end for;

    maximal_subgroups := [];
    for subgroup_h in valid_subgroups do
        is_maximal := true;

        for subgroup_k in valid_subgroups do
            if #subgroup_h lt #subgroup_k and local_norm_subgroup_is_contained(subgroup_h, subgroup_k) then
                is_maximal := false;
                break;
            end if;
        end for;

        if is_maximal then
            Append(~maximal_subgroups, subgroup_h);
        end if;
    end for;

    return maximal_subgroups;
end function;


function local_norm_representative_for_delta_element(delta_element, delta_data)
    ambient_delta_element := delta_data`delta_group ! delta_element;

    for i in [1..#delta_data`delta_elements] do
        if delta_data`delta_elements[i] eq ambient_delta_element then
            return delta_data`delta_representatives[i];
        end if;
    end for;

    error "Could not find a canonical representative for a Delta element.";
end function;


function local_norm_explicit_representatives_for_subgroup(subgroup_x, delta_data)
    subgroup_representative_lookup := AssociativeArray();

    for delta_element in subgroup_x do
        representative := local_norm_representative_for_delta_element(delta_element, delta_data);
        subgroup_representative_lookup[Sprint(representative)] := representative;
    end for;

    return local_norm_string_lookup_values(subgroup_representative_lookup);
end function;


procedure print_local_norm_summary(summary, Print)
    if not local_norm_print_is_concise(Print) then
        return;
    end if;

    print "";
    print "[LN]", "branch=", summary`branch_kind,
          "|", ideal_summary("modulus", summary`modulus_ideal);

    if summary`branch_kind eq "complement" then
        print "[LN] complement_family=", summary`complement_family,
              "| complement_index=", summary`complement_index,
              "| subgroup_order=", #summary`complement_subgroup;
    end if;

    print "[LN] Theta:", summary`omega_representatives;
    print "[LN] theta_contains_one:", summary`omega_contains_one;
    print "[LN] sizes | Delta=", summary`delta_size,
          "| Theta=", summary`omega_size,
          "| maximal_Psi=", summary`maximal_psi_count;

    if local_norm_print_is_detailed(Print) then
        print "[LN] trace_form_coefficients:", summary`trace_form_coefficients;
        print "[LN] norm_form_terms:", summary`norm_form_terms;
        print "[LN] Delta:", summary`delta_representatives;
        print "[LN] projective_class_count:", summary`projective_class_count,
              "| trace_zero_class_count:", summary`trace_zero_class_count;
        for psi_index in [1..#summary`maximal_psi_representatives] do
            print Sprintf("[LN] maximal_Psi[%o]: %o", psi_index, summary`maximal_psi_representatives[psi_index]);
        end for;
    end if;
end procedure;


function local_norm_summary_from_tuples(
    branch_kind,
    group_model,
    complement_family,
    complement_index,
    complement_class,
    complement_subgroup,
    source_tuples :
    Print := 1
)
    Print := validate_print_level(Print);

    reduced_form_data := local_norm_reduced_forms_for_modulus(
        group_model`order_data,
        group_model`modulus_ideal
    );
    delta_data := local_norm_delta_data_for_reduced_base_ring(
        reduced_form_data`reduced_base_ring
    );
    zero_element := reduced_form_data`reduced_base_ring!0;
    omega_element_lookup := AssociativeArray();
    omega_representative_lookup := AssociativeArray();
    trace_zero_class_count := 0;

    for raw_tuple in source_tuples do
        reduced_tuple := local_norm_normalized_tuple(
            raw_tuple,
            reduced_form_data`reduced_base_ring
        );
        trace_value, norm_value := local_norm_evaluate_reduced_tuple(
            reduced_form_data,
            reduced_tuple
        );

        if trace_value ne zero_element then
            continue;
        end if;

        trace_zero_class_count +:= 1;

        if not IsUnit(norm_value) then
            error "A trace-zero projective class did not have unit norm modulo the modulus.";
        end if;

        residue_unit := norm_value @@ delta_data`integer_ring_residue_unit_map;
        delta_element := delta_data`delta_map(residue_unit);
        omega_representative := local_norm_representative_for_delta_element(delta_element, delta_data);
        omega_key := Sprint(omega_representative);

        omega_element_lookup[omega_key] := delta_data`delta_group ! delta_element;
        omega_representative_lookup[omega_key] := omega_representative;
    end for;

    omega_elements := local_norm_string_lookup_values(omega_element_lookup);
    omega_representatives := local_norm_string_lookup_values(omega_representative_lookup);
    delta_identity_representative := local_norm_representative_for_delta_element(
        Identity(delta_data`delta_group),
        delta_data
    );
    omega_contains_one := IsDefined(
        omega_representative_lookup,
        Sprint(delta_identity_representative)
    );
    maximal_psi_subgroups := local_norm_maximal_disjoint_subgroups(
        delta_data`delta_group,
        omega_elements
    );
    maximal_psi_representatives := [];

    for subgroup_x in maximal_psi_subgroups do
        Append(
            ~maximal_psi_representatives,
            local_norm_explicit_representatives_for_subgroup(
                subgroup_x,
                delta_data
            )
        );
    end for;
    maximal_psi_representatives := local_norm_sorted_sequences_by_string(maximal_psi_representatives);

    summary := rec<local_norm_summary_format |
        branch_kind := branch_kind,
        prime_ideal := group_model`prime_ideal,
        prime_power_exponent := group_model`prime_power_exponent,
        modulus_ideal := group_model`modulus_ideal,
        norm := Norm(group_model`modulus_ideal),
        group_model := group_model,
        complement_family := complement_family,
        complement_index := complement_index,
        complement_class := complement_class,
        complement_subgroup := complement_subgroup,
        trace_form_coefficients := reduced_form_data`trace_coefficients,
        norm_form_terms := reduced_form_data`norm_terms,
        delta_representatives := delta_data`delta_representatives,
        delta_identity_representative := delta_identity_representative,
        omega_representatives := omega_representatives,
        omega_contains_one := omega_contains_one,
        maximal_psi_representatives := maximal_psi_representatives,
        delta_size := #delta_data`delta_group,
        omega_size := #omega_representatives,
        maximal_psi_count := #maximal_psi_representatives,
        projective_class_count := #source_tuples,
        trace_zero_class_count := trace_zero_class_count
    >;

    print_local_norm_summary(summary, Print);
    return summary;
end function;


function local_norm_summary_for_ramified_prime(
    order_data,
    prime_ideal :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    Print := validate_print_level(Print);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );
    prime_ideal := normalize_prime_ideal(order_data`integer_ring, prime_ideal);

    if Index(ramified_primes(order_data), prime_ideal) eq 0 then
        error "local_norm_summary_for_ramified_prime expects a ramified prime of the quaternion algebra.";
    end if;

    group_model := build_projective_unit_group(
        order_data,
        prime_ideal,
        1 :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds
    );

    if group_model`skipped_due_to_estimate then
        error Sprintf(
            "The ramified local-norm model at modulus %o was skipped at task %o with estimated runtime %o seconds.",
            group_model`modulus_ideal,
            group_model`skipped_task_key,
            group_model`skipped_estimated_seconds
        );
    end if;

    source_tuples := [
        local_norm_normalized_tuple(tuple_x, group_model`reduced_base_ring) :
        tuple_x in group_model`class_representatives
    ];

    return local_norm_summary_from_tuples(
        "ramified_ambient",
        group_model,
        "",
        0,
        false,
        false,
        source_tuples :
        Print := Print
    );
end function;


function local_norm_summary_for_complementary_result(
    complementary_result,
    complement_index :
    normal_only := false,
    Print := 1
)
    Print := validate_print_level(Print);

    if Type(complement_index) ne RngIntElt or complement_index lt 1 then
        error "complement_index must be a positive integer.";
    end if;

    group_model := complementary_prime_power_group_model(complementary_result);
    complement_classes := local_norm_complement_classes_for_complementary_result(
        complementary_result,
        normal_only
    );

    if complement_index gt #complement_classes then
        error "complement_index is out of range for the stored complements.";
    end if;

    complement_class := complement_classes[complement_index];
    complement_subgroup := complement_class`subgroup;
    source_tuples := local_norm_projective_class_tuples_for_subgroup(
        group_model,
        complement_subgroup
    );

    return local_norm_summary_from_tuples(
        "complement",
        group_model,
        normal_only select "normal_localized_unit_group" else "localized_unit_group",
        complement_index,
        complement_class,
        complement_subgroup,
        source_tuples :
        Print := Print
    );
end function;


function local_norm_ramified_summaries(
    order_data :
    ramified_bound := 0,
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    Print := validate_print_level(Print);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );

    if Type(ramified_bound) ne RngIntElt or ramified_bound lt 0 then
        error "ramified_bound must be an integer >= 0.";
    end if;

    ramified_summaries := [];
    skipped_estimated_tasks := [];

    for prime_ideal in ramified_primes(order_data) do
        if ramified_bound ne 0 and Norm(prime_ideal) gt ramified_bound then
            continue;
        end if;

        group_model := build_projective_unit_group(
            order_data,
            prime_ideal,
            1 :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );

        if group_model`skipped_due_to_estimate then
            append_skipped_task_if_new(
                group_model`skipped_task_key,
                group_model`modulus_ideal,
                group_model`skipped_estimated_seconds,
                ~skipped_estimated_tasks
            );
            continue;
        end if;

        source_tuples := [
            local_norm_normalized_tuple(tuple_x, group_model`reduced_base_ring) :
            tuple_x in group_model`class_representatives
        ];
        Append(
            ~ramified_summaries,
            local_norm_summary_from_tuples(
                "ramified_ambient",
                group_model,
                "",
                0,
                false,
                false,
                source_tuples :
                Print := Print
            )
        );
    end for;

    return ramified_summaries, skipped_estimated_tasks;
end function;


function local_norm_run_for_order(
    order_data,
    norm_bound :
    ramified_bound := 0,
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    Print := validate_print_level(Print);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );

    if Type(norm_bound) ne RngIntElt or norm_bound lt 0 then
        error "norm_bound must be an integer >= 0.";
    end if;

    if Type(ramified_bound) ne RngIntElt or ramified_bound lt 0 then
        error "ramified_bound must be an integer >= 0.";
    end if;

    if local_norm_print_is_concise(Print) then
        print "";
        print "============================================================";
        print "[LN run] Direct local-norm summaries for one order";
        print "============================================================";
        print "[LN run] norm_bound=", norm_bound,
              "| ramified_bound=", ramified_bound;
    end if;

    split_primes := split_primes_up_to(order_data, norm_bound);
    algebra_ramified_primes := ramified_primes(order_data);
    context := complementary_build_context(order_data);
    complement_bundles := [];
    complement_skipped_tasks := [];

    for prime_ideal in split_primes do
        prime_power_scan := scan_prime_power_complementary_triples(
            order_data,
            prime_ideal,
            2 :
            T := [],
            context := context,
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );

        for skipped_task in prime_power_scan`skipped_estimated_tasks do
            append_skipped_task_if_new(
                skipped_task[1],
                skipped_task[2],
                skipped_task[3],
                ~complement_skipped_tasks
            );
        end for;

        for complementary_result in prime_power_scan`ideal_results do
            if complementary_result`skipped_due_to_estimate or
               (not complementary_result`injective) or
               (#complementary_result`complement_classes eq 0) then
                continue;
            end if;

            group_model := complementary_prime_power_group_model(complementary_result);
            complement_summaries := [];

            for complement_index in [1..#complementary_result`complement_classes] do
                Append(
                    ~complement_summaries,
                    local_norm_summary_for_complementary_result(
                        complementary_result,
                        complement_index :
                        Print := Print
                    )
                );
            end for;

            Append(
                ~complement_bundles,
                rec<local_norm_complement_bundle_format |
                    group_model := group_model,
                    complement_family := "localized_unit_group",
                    modulus_ideal := complementary_result`modulus_ideal,
                    modulus_norm := Norm(complementary_result`modulus_ideal),
                    complement_summaries := complement_summaries
                >
            );
        end for;
    end for;

    for prime_ideal in algebra_ramified_primes do
        if ramified_bound ne 0 and Norm(prime_ideal) gt ramified_bound then
            continue;
        end if;

        prime_power_scan := scan_prime_power_complementary_triples(
            order_data,
            prime_ideal,
            2 :
            T := [],
            context := context,
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );

        for skipped_task in prime_power_scan`skipped_estimated_tasks do
            append_skipped_task_if_new(
                skipped_task[1],
                skipped_task[2],
                skipped_task[3],
                ~complement_skipped_tasks
            );
        end for;

        for complementary_result in prime_power_scan`ideal_results do
            if complementary_result`skipped_due_to_estimate or
               (not complementary_result`injective) or
               (#complementary_result`complement_classes eq 0) then
                continue;
            end if;

            group_model := complementary_prime_power_group_model(complementary_result);
            complement_summaries := [];

            for complement_index in [1..#complementary_result`complement_classes] do
                Append(
                    ~complement_summaries,
                    local_norm_summary_for_complementary_result(
                        complementary_result,
                        complement_index :
                        Print := Print
                    )
                );
            end for;

            Append(
                ~complement_bundles,
                rec<local_norm_complement_bundle_format |
                    group_model := group_model,
                    complement_family := "localized_unit_group",
                    modulus_ideal := complementary_result`modulus_ideal,
                    modulus_norm := Norm(complementary_result`modulus_ideal),
                    complement_summaries := complement_summaries
                >
            );
        end for;
    end for;
    ramified_summaries, ramified_skipped_tasks := local_norm_ramified_summaries(
        order_data :
        ramified_bound := ramified_bound,
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds
    );

    skipped_estimated_tasks := complement_skipped_tasks;
    for skipped_task in ramified_skipped_tasks do
        append_skipped_task_if_new(
            skipped_task[1],
            skipped_task[2],
            skipped_task[3],
            ~skipped_estimated_tasks
        );
    end for;

    if local_norm_print_is_concise(Print) then
        print "";
        print "[LN run] summary | complement_bundles=", #complement_bundles,
              "| ramified_summaries=", #ramified_summaries,
              "| skipped_estimated_tasks=", #skipped_estimated_tasks;
    end if;

    return rec<local_norm_run_format |
        order_data := order_data,
        norm_bound := norm_bound,
        ramified_bound := ramified_bound,
        complement_family := "localized_unit_group",
        complement_bundles := complement_bundles,
        ramified_summaries := ramified_summaries,
        skipped_estimated_tasks := skipped_estimated_tasks
    >;
end function;
