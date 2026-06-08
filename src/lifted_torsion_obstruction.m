// ============================================================================
// Lifted torsion obstruction.
//
// For a non-inverted complementary triple (T, P^k, H) with P above 2, the
// trace-zero condition modulo P^k is often too coarse.  This module computes
// the obstruction obtained by pulling H back along G[P^m] -> G[P^k], where
// m = max(k, 2e_P + 1) and e_P = v_P(2), and imposing trace zero modulo P^m.
//
// Main API:
// - lifted_torsion_obstruction_skip_reason(complementary_result, complement_index)
// - lifted_torsion_obstruction_summary(complementary_result, complement_index)
// ============================================================================


function lifted_torsion_obstruction_skip_reason(complementary_result, complement_index)
    if complement_index lt 1 then
        return "no complement class";
    end if;

    if complementary_result`skipped_due_to_estimate then
        return "complementary computation skipped due to estimate";
    end if;

    if not assigned complementary_result`complements_computed then
        return "complements were not computed";
    end if;

    if not complementary_result`complements_computed then
        return "complements were not computed";
    end if;

    if #complementary_result`complement_classes eq 0 then
        return "no complement classes";
    end if;

    if complement_index gt #complementary_result`complement_classes then
        return "complement index out of range";
    end if;

    if not assigned complementary_result`injective then
        return "injectivity was not recorded";
    end if;

    if not complementary_result`injective then
        return "reduction is not injective";
    end if;

    if not assigned complementary_result`reduction_factors then
        return "local reduction factors were not recorded";
    end if;

    if #complementary_result`reduction_factors ne 1 then
        return "modulus is not a single prime power";
    end if;

    if #complementary_result`factor_primes ne 1 or #complementary_result`factor_exponents ne 1 then
        return "modulus factorization was not recorded as a prime power";
    end if;

    prime_ideal := complementary_result`factor_primes[1];

    if (Integers()!Norm(prime_ideal)) mod 2 ne 0 then
        return "modulus prime is not above 2";
    end if;

    if Index(complementary_result`localized_unit_group`ramified_subset, prime_ideal) ne 0 then
        return "modulus prime lies in T";
    end if;

    reduction_factor := complementary_result`reduction_factors[1];

    if reduction_factor`skipped_due_to_estimate then
        return "local reduction was skipped due to estimate";
    end if;

    return "";
end function;


function lifted_torsion_obstruction_target_exponent(complementary_result)
    prime_ideal := complementary_result`factor_primes[1];
    source_exponent := complementary_result`factor_exponents[1];
    e_p := Valuation(2 * complementary_result`localized_unit_group`order_data`integer_ring, prime_ideal);

    return Maximum(source_exponent, 2 * e_p + 1);
end function;


function lifted_torsion_obstruction_reduced_target_tuple(
    target_group_model,
    lifted_group_model,
    lifted_tuple
)
    integer_ring := target_group_model`order_data`integer_ring;
    target_tuple := [];

    for coordinate in lifted_tuple do
        integral_lift := integer_ring!(coordinate @@ lifted_group_model`reduction_map);
        Append(~target_tuple, target_group_model`reduction_map(integral_lift));
    end for;

    return local_norm_normalized_tuple(target_tuple, target_group_model`reduced_base_ring);
end function;


function lifted_torsion_obstruction_reduce_element_to_target(
    target_group_model,
    lifted_reduction_map,
    lifted_element
)
    integer_ring := target_group_model`order_data`integer_ring;
    target_tuple := [];

    for coordinate in Eltseq(lifted_element) do
        integral_lift := integer_ring!(coordinate @@ lifted_reduction_map);
        Append(~target_tuple, target_group_model`reduction_map(integral_lift));
    end for;

    return target_group_model`reduced_algebra!target_tuple;
end function;


function lifted_torsion_obstruction_reduce_scalar_to_target(
    target_group_model,
    lifted_reduction_map,
    lifted_scalar
)
    integer_ring := target_group_model`order_data`integer_ring;
    integral_lift := integer_ring!(lifted_scalar @@ lifted_reduction_map);
    return target_group_model`reduction_map(integral_lift);
end function;


function lifted_torsion_obstruction_source_tuples(
    target_group_model,
    lifted_group_model,
    complement_subgroup
)
    target_class_index_by_key := local_norm_class_index_by_key(target_group_model);
    target_class_key_data := assigned target_group_model`class_key_data select
        target_group_model`class_key_data else false;
    target_identity := reduced_order_identity(
        target_group_model`order_data,
        target_group_model`reduction_map,
        target_group_model`reduced_algebra
    );
    target_identity_index := identity_class_index(
        target_identity,
        target_class_index_by_key,
        target_group_model`scalars,
        target_class_key_data
    );
    target_class_indices := {};

    for subgroup_element in complement_subgroup do
        Include(~target_class_indices, target_identity_index^subgroup_element);
    end for;

    source_tuples := [];
    for lifted_tuple_raw in lifted_group_model`class_representatives do
        lifted_tuple := local_norm_normalized_tuple(
            lifted_tuple_raw,
            lifted_group_model`reduced_base_ring
        );
        target_tuple := lifted_torsion_obstruction_reduced_target_tuple(
            target_group_model,
            lifted_group_model,
            lifted_tuple
        );
        target_representative := target_group_model`reduced_algebra!target_tuple;
        target_representative_key := projective_class_key(
            target_representative,
            target_group_model`scalars,
            target_class_key_data
        );

        if not IsDefined(target_class_index_by_key, target_representative_key) then
            error "A lifted projective class did not reduce to a target projective class.";
        end if;

        if target_class_index_by_key[target_representative_key] in target_class_indices then
            Append(~source_tuples, lifted_tuple);
        end if;
    end for;

    return source_tuples;
end function;


function lifted_torsion_obstruction_class_model(
    target_group_model,
    lifted_exponent :
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

    order_data := target_group_model`order_data;
    prime_ideal := target_group_model`prime_ideal;

    if lifted_exponent eq target_group_model`prime_power_exponent then
        return target_group_model;
    end if;

    modulus_ideal := prime_ideal^lifted_exponent;
    reduced_algebra, reduced_base_ring, reduction_map :=
        build_reduced_algebra(order_data, modulus_ideal);
    projective_formula_known,
    expected_projective_group_order,
    formula_case := expected_projective_group_order_data(order_data, prime_ideal, lifted_exponent);
    projective_class_time_limit_seconds := effective_stage_time_limit_seconds(
        "projective_quotient",
        lifted_exponent,
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );
    timer := Cputime();
    expected_scalar_count := expected_scalar_unit_order(prime_ideal, lifted_exponent);
    target_unit_lookup := reduced_unit_lookup(target_group_model`reduced_units);
    target_scalar_lookup := AssociativeArray();

    for scalar in target_group_model`scalar_units do
        target_scalar_lookup[scalar] := true;
    end for;

    // Since P^k O / P^m O is nilpotent, a class modulo P^m is a unit if and
    // only if its reduction modulo P^k is a unit.  This avoids the generic
    // inverse-search unit enumeration for the lifted quotient.
    reduced_units := [
        lifted_element :
        lifted_element in reduced_algebra |
        reduced_element_is_unit(
            lifted_torsion_obstruction_reduce_element_to_target(
                target_group_model,
                reduction_map,
                lifted_element
            ),
            target_unit_lookup
        )
    ];

    scalar_units := [
        scalar :
        scalar in reduced_base_ring |
        IsDefined(
            target_scalar_lookup,
            lifted_torsion_obstruction_reduce_scalar_to_target(
                target_group_model,
                reduction_map,
                scalar
            )
        )
    ];

    one_algebra := reduced_order_identity(order_data, reduction_map, reduced_algebra);
    scalars := {a * one_algebra : a in scalar_units};

    if (#reduced_units mod #scalars) ne 0 then
        error "Lifted reduced-unit count is not divisible by scalar count.";
    end if;

    if #scalar_units ne expected_scalar_count then
        error "Lifted scalar-unit count did not match the expected size of (R / P^m)^*.";
    end if;

    num_classes := #reduced_units div #scalars;
    if projective_formula_known and num_classes ne expected_projective_group_order then
        error "Lifted projective class count did not match the expected maximal-local formula.";
    end if;

    class_representatives, _, projective_class_skipped, projective_class_estimated_seconds :=
        projective_class_data(
            reduced_units,
            scalars,
            num_classes :
            Print := Print,
            time_limit_seconds := projective_class_time_limit_seconds
        );

    if projective_class_skipped then
        error Sprintf(
            "The lifted P^m projective-class enumeration was skipped with estimated runtime %o seconds.",
            projective_class_estimated_seconds
        );
    end if;

    return rec<projective_unit_group_format |
        order_data := order_data,
        prime_ideal := prime_ideal,
        prime_power_exponent := lifted_exponent,
        modulus_ideal := modulus_ideal,
        elapsed_seconds := Cputime(timer),
        estimated_reduced_unit_seconds := 0,
        estimated_permutation_seconds := projective_class_estimated_seconds,
        prime_ramified_in_algebra := Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) ne 0,
        local_maximal_at_prime := order_is_locally_maximal_at_prime(order_data, prime_ideal),
        formula_case := formula_case,
        expected_projective_group_order := expected_projective_group_order,
        expected_scalar_unit_order := expected_scalar_count,
        expected_reduced_unit_order := projective_formula_known select expected_projective_group_order * expected_scalar_count else 0,
        reduced_base_ring := reduced_base_ring,
        reduced_algebra := reduced_algebra,
        reduction_map := reduction_map,
        reduced_units := reduced_units,
        scalar_units := scalar_units,
        scalars := scalars,
        class_representatives := class_representatives,
        class_index_by_key := false,
        class_key_data := false,
        normalizer_image_defined := false,
        ramified_extension_defined := false,
        complements_computed := false,
        skipped_due_to_estimate := false,
        skipped_task_key := "",
        skipped_estimated_seconds := 0
    >;
end function;


function lifted_torsion_obstruction_minimal_group_model(target_group_model, lifted_exponent)
    if lifted_exponent eq target_group_model`prime_power_exponent then
        return target_group_model;
    end if;

    order_data := target_group_model`order_data;
    prime_ideal := target_group_model`prime_ideal;
    modulus_ideal := prime_ideal^lifted_exponent;
    reduced_algebra, reduced_base_ring, reduction_map :=
        build_reduced_algebra(order_data, modulus_ideal);

    return rec<projective_unit_group_format |
        order_data := order_data,
        prime_ideal := prime_ideal,
        prime_power_exponent := lifted_exponent,
        modulus_ideal := modulus_ideal,
        reduced_base_ring := reduced_base_ring,
        reduced_algebra := reduced_algebra,
        reduction_map := reduction_map,
        normalizer_image_defined := false,
        ramified_extension_defined := false,
        complements_computed := false,
        skipped_due_to_estimate := false,
        skipped_task_key := "",
        skipped_estimated_seconds := 0
    >;
end function;


function lifted_torsion_obstruction_reduced_forms_for_group_model(group_model)
    form_data := local_norm_forms(group_model`order_data);

    return rec<local_norm_reduced_form_data_format |
        form_data := form_data,
        modulus_ideal := group_model`modulus_ideal,
        reduced_base_ring := group_model`reduced_base_ring,
        reduction_map := group_model`reduction_map,
        trace_coefficients := [group_model`reduction_map(c) : c in form_data`trace_coefficients],
        norm_terms := [<term[1], term[2], group_model`reduction_map(term[3])> : term in form_data`norm_terms]
    >;
end function;


procedure lifted_torsion_obstruction_scan_lifts(
    reduced_form_data,
    delta_data,
    coordinate_fibers,
    coordinate_index,
    current_coordinates,
    ~source_count,
    ~trace_zero_count,
    ~omega_element_lookup,
    ~omega_representative_lookup,
    ~stop_scan
)
    if stop_scan then
        return;
    end if;

    if coordinate_index gt #coordinate_fibers then
        source_count +:= 1;

        reduced_tuple := local_norm_normalized_tuple(
            current_coordinates,
            reduced_form_data`reduced_base_ring
        );
        trace_value, norm_value := local_norm_evaluate_reduced_tuple(
            reduced_form_data,
            reduced_tuple
        );

        if trace_value ne reduced_form_data`reduced_base_ring!0 then
            return;
        end if;

        trace_zero_count +:= 1;

        if not IsUnit(norm_value) then
            error "A trace-zero lifted class did not have unit norm modulo the lifted modulus.";
        end if;

        residue_unit := norm_value @@ delta_data`integer_ring_residue_unit_map;
        delta_element := delta_data`delta_map(residue_unit);
        omega_representative := local_norm_representative_for_delta_element(delta_element, delta_data);
        omega_key := Sprint(omega_representative);

        omega_element_lookup[omega_key] := delta_data`delta_group ! delta_element;
        omega_representative_lookup[omega_key] := omega_representative;

        if #Keys(omega_representative_lookup) eq #delta_data`delta_group then
            stop_scan := true;
        end if;

        return;
    end if;

    for coordinate in coordinate_fibers[coordinate_index] do
        if stop_scan then
            return;
        end if;

        lifted_torsion_obstruction_scan_lifts(
            reduced_form_data,
            delta_data,
            coordinate_fibers,
            coordinate_index + 1,
            current_coordinates cat [coordinate],
            ~source_count,
            ~trace_zero_count,
            ~omega_element_lookup,
            ~omega_representative_lookup,
            ~stop_scan
        );
    end for;
end procedure;


procedure lifted_torsion_obstruction_record_trace_zero_tuple(
    reduced_form_data,
    delta_data,
    reduced_tuple,
    ~trace_zero_count,
    ~omega_element_lookup,
    ~omega_representative_lookup,
    ~stop_scan
)
    if stop_scan then
        return;
    end if;

    _, norm_value := local_norm_evaluate_reduced_tuple(
        reduced_form_data,
        reduced_tuple
    );

    trace_zero_count +:= 1;

    if not IsUnit(norm_value) then
        error "A trace-zero lifted class did not have unit norm modulo the lifted modulus.";
    end if;

    residue_unit := norm_value @@ delta_data`integer_ring_residue_unit_map;
    delta_element := delta_data`delta_map(residue_unit);
    omega_representative := local_norm_representative_for_delta_element(delta_element, delta_data);
    omega_key := Sprint(omega_representative);

    omega_element_lookup[omega_key] := delta_data`delta_group ! delta_element;
    omega_representative_lookup[omega_key] := omega_representative;

    if #Keys(omega_representative_lookup) eq #delta_data`delta_group then
        stop_scan := true;
    end if;
end procedure;


procedure lifted_torsion_obstruction_scan_trace_zero_lifts(
    reduced_form_data,
    delta_data,
    coordinate_fibers,
    ~trace_zero_count,
    ~omega_element_lookup,
    ~omega_representative_lookup,
    ~stop_scan
)
    if stop_scan then
        return;
    end if;

    trace_coefficients := reduced_form_data`trace_coefficients;
    tail_lookup := AssociativeArray();

    for x3 in coordinate_fibers[3] do
        for x4 in coordinate_fibers[4] do
            tail_trace := trace_coefficients[3] * x3 + trace_coefficients[4] * x4;
            tail_key := Sprint(Eltseq(tail_trace));

            if IsDefined(tail_lookup, tail_key) then
                tail_pairs := tail_lookup[tail_key];
            else
                tail_pairs := [];
            end if;

            Append(~tail_pairs, [x3, x4]);
            tail_lookup[tail_key] := tail_pairs;
        end for;
    end for;

    for x1 in coordinate_fibers[1] do
        for x2 in coordinate_fibers[2] do
            if stop_scan then
                return;
            end if;

            head_trace := trace_coefficients[1] * x1 + trace_coefficients[2] * x2;
            needed_tail_key := Sprint(Eltseq(-head_trace));

            if not IsDefined(tail_lookup, needed_tail_key) then
                continue;
            end if;

            for tail_pair in tail_lookup[needed_tail_key] do
                lifted_torsion_obstruction_record_trace_zero_tuple(
                    reduced_form_data,
                    delta_data,
                    [x1, x2, tail_pair[1], tail_pair[2]],
                    ~trace_zero_count,
                    ~omega_element_lookup,
                    ~omega_representative_lookup,
                    ~stop_scan
                );

                if stop_scan then
                    return;
                end if;
            end for;
        end for;
    end for;
end procedure;


function lifted_torsion_obstruction_direct_summary(
    complementary_result,
    complement_index :
    Print := 1
)
    Print := validate_print_level(Print);

    target_group_model := complementary_prime_power_group_model(complementary_result);
    complement_class := complementary_result`complement_classes[complement_index];
    complement_subgroup := complement_class`subgroup;
    lifted_exponent := lifted_torsion_obstruction_target_exponent(complementary_result);

    if lifted_exponent eq target_group_model`prime_power_exponent then
        source_tuples := local_norm_projective_class_tuples_for_subgroup(
            target_group_model,
            complement_subgroup
        );
        return local_norm_summary_from_tuples(
            "lifted_torsion_obstruction",
            target_group_model,
            "preimage_of_complement_mod_prime_power",
            complement_index,
            complement_class,
            complement_subgroup,
            source_tuples :
            Print := Print
        );
    end if;

    lifted_group_model := lifted_torsion_obstruction_minimal_group_model(
        target_group_model,
        lifted_exponent
    );
    reduced_form_data := lifted_torsion_obstruction_reduced_forms_for_group_model(
        lifted_group_model
    );
    delta_data := local_norm_delta_data_for_reduced_base_ring(
        reduced_form_data`reduced_base_ring
    );
    scalar_fibers := scalar_prime_reduction_fibers(
        target_group_model`order_data`integer_ring,
        lifted_group_model`reduced_base_ring,
        lifted_group_model`reduction_map,
        target_group_model`reduced_base_ring,
        target_group_model`reduction_map
    );
    target_tuples := local_norm_projective_class_tuples_for_subgroup(
        target_group_model,
        complement_subgroup
    );
    omega_element_lookup := AssociativeArray();
    omega_representative_lookup := AssociativeArray();
    source_count := 0;
    trace_zero_count := 0;
    stop_scan := false;

    for target_tuple in target_tuples do
        if stop_scan then
            break;
        end if;

        coordinate_fibers := [
            scalar_prime_fiber(scalar_fibers, coordinate) :
            coordinate in target_tuple
        ];
        source_count +:= &*[#coordinate_fiber : coordinate_fiber in coordinate_fibers];
        lifted_torsion_obstruction_scan_trace_zero_lifts(
            reduced_form_data,
            delta_data,
            coordinate_fibers,
            ~trace_zero_count,
            ~omega_element_lookup,
            ~omega_representative_lookup,
            ~stop_scan
        );
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
        branch_kind := "lifted_torsion_obstruction",
        prime_ideal := lifted_group_model`prime_ideal,
        prime_power_exponent := lifted_group_model`prime_power_exponent,
        modulus_ideal := lifted_group_model`modulus_ideal,
        norm := Norm(lifted_group_model`modulus_ideal),
        group_model := lifted_group_model,
        complement_family := "preimage_of_complement_mod_prime_power",
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
        projective_class_count := source_count,
        trace_zero_class_count := trace_zero_count
    >;

    print_local_norm_summary(summary, Print);
    return summary;
end function;


function lifted_torsion_obstruction_summary(
    complementary_result,
    complement_index :
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

    skip_reason := lifted_torsion_obstruction_skip_reason(complementary_result, complement_index);
    if skip_reason ne "" then
        error skip_reason;
    end if;

    return lifted_torsion_obstruction_direct_summary(
        complementary_result,
        complement_index :
        Print := Print
    );
end function;
