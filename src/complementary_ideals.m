// ============================================================================
// Complementary-ideal pipeline built on top of the local prime-power engine.
//
// Levels:
// - direct / local computation at one ideal I,
// - single-order complementary-triple scan over all admissible ramified sets T,
// - multi-order scan reusing the single-order logic.
//
// Main API:
// - admissible_ramified_primes(order_data)
// - compute_U_empty(order_data)
// - compute_alpha_p_data(order_data)
// - compute_all_U_T(order_data : consistency_check := false)
// - local_reduction_group(order_data, prime_ideal, k :
//       Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0)
// - reduction_image_of_U_T(localized_unit_group, prime_ideal, k :
//       Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0)
// - is_reduction_injective(localized_unit_group, modulus_ideal :
//       Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0)
// - minimal_ideal_poset(order_data, T, norm_bound :
//       Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0,
//       expected_exponent_bound := 2, allow_higher_exponents := true)
// - complementary_pairs_at_ideal(order_data, modulus_ideal :
//       T := [], context := false, require_ambient := true,
//       Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0)
// - complementary_pairs_for_order(base_field, quaternion_algebra, quaternion_order, modulus_ideal :
//       ...)
// - complementary_prime_power_group_model(complementary_result)
// - scan_prime_power_complementary_triples(order_data, prime_ideal, max_exponent :
//       T := [], context := false, Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0,
//       require_ambient := true)
// - scan_order_for_complementary_triples(order_data, norm_bound :
//       Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0,
//       expected_exponent_bound := 2, allow_higher_exponents := true,
//       consistency_check := false)
// - scan_orders_for_complementary_triples(order_list, norm_bound :
//       Print := 1, time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0,
//       expected_exponent_bound := 2, allow_higher_exponents := true,
//       consistency_check := false)
//
// Convention note:
// The ramified generator alpha_p follows the existing right-ideal convention
// already used by the projective-unit-group and presentation code. It is
// recovered from a principal maximal right O-ideal with left order O, so it is
// represented by the generator of a right ideal alpha_p O.
// ============================================================================


localized_unit_group_format := recformat<
    order_data,
    admissible_ramified_primes,
    ramified_subset,
    ramified_subset_key,
    subgroup,
    subgroup_order,
    generator_primes,
    generator_group_elements,
    generator_elements
>;


localized_alpha_data_format := recformat<
    prime_ideal,
    alpha_element,
    normalizer_group_element
>;


localized_reduction_image_format := recformat<
    localized_unit_group,
    prime_ideal,
    prime_power_exponent,
    modulus_ideal,
    group_model,
    ambient_group,
    image_subgroup,
    generator_images,
    injective,
    uses_ramified_extension,
    skipped_due_to_estimate,
    skipped_task_key,
    skipped_estimated_seconds
>;


complementary_ideal_result_format := recformat<
    localized_unit_group,
    modulus_ideal,
    factor_primes,
    factor_exponents,
    reduction_factors,
    ambient_group,
    image_subgroup,
    complement_classes,
    normal_complement_classes,
    complements_computed,
    injective,
    skipped_due_to_estimate,
    skipped_estimated_tasks
>;


minimal_ideal_poset_result_format := recformat<
    localized_unit_group,
    relevant_primes,
    norm_bound,
    expected_exponent_bound,
    allow_higher_exponents,
    minimal_injective_ideals,
    minimal_results,
    tested_ideals,
    skipped_ideals,
    skipped_estimated_tasks,
    exponent_bound_warnings
>;


complementary_triple_format := recformat<
    algebra_identifier,
    order_identifier,
    order_data,
    localized_unit_group,
    ramified_subset,
    modulus_ideal,
    complementary_result
>;


prime_power_complementary_scan_format := recformat<
    localized_unit_group,
    prime_ideal,
    max_exponent,
    ideal_results,
    complementary_triples,
    skipped_estimated_tasks
>;


complementary_order_triple_data_format := recformat<
    localized_unit_groups,
    minimal_ideal_results,
    complementary_triples
>;


single_order_complementary_scan_format := recformat<
    algebra_identifier,
    order_identifier,
    order_data,
    norm_bound,
    admissible_ramified_primes,
    elapsed_seconds,
    unit_quotient_order,
    trivial_unit_quotient,
    triple_data,
    skipped_estimated_tasks,
    exponent_bound_warnings
>;


multi_order_complementary_scan_format := recformat<
    algebra_rows,
    elapsed_seconds,
    skipped_estimated_tasks,
    exponent_bound_warnings
>;


complementary_context_format := recformat<
    order_data,
    normalizer_lookup,
    normalizer_representative_lookup,
    alpha_data,
    localized_unit_group_cache,
    local_group_model_cache,
    local_image_cache,
    ideal_result_cache,
    ideal_result_ambient_cache,
    skipped_estimated_tasks,
    exponent_bound_warnings
>;


function complementary_join_strings(strings, delimiter)
    if #strings eq 0 then
        return "";
    end if;

    output := strings[1];
    for i in [2..#strings] do
        output cat:= delimiter cat strings[i];
    end for;

    return output;
end function;


function complementary_sorted_lookup_values(lookup)
    keys := [key : key in Keys(lookup)];
    Sort(~keys);
    return [lookup[key] : key in keys];
end function;


function complementary_sorted_ideals(ideal_list)
    lookup := AssociativeArray();

    for ideal_x in ideal_list do
        lookup[Sprint(ideal_x)] := ideal_x;
    end for;

    return complementary_sorted_lookup_values(lookup);
end function;


function complementary_subset_key(ramified_subset)
    return complementary_join_strings(
        [Sprint(prime_ideal) : prime_ideal in complementary_sorted_ideals(ramified_subset)],
        " || "
    );
end function;


function complementary_vector_key(exponent_vector)
    return Sprint(exponent_vector);
end function;


function complementary_normalized_order_element_key(order_data, element_x)
    integral_element := primitive_integral_order_representative(order_data, element_x);
    normalized_element := normalize_quaternion_element(order_data`quaternion_algebra, integral_element);
    return Sprint(Eltseq(normalized_element));
end function;


function complementary_subgroup_from_generators(group_g, generator_list)
    if #generator_list eq 0 then
        return sub<group_g | Identity(group_g)>;
    end if;

    return sub<group_g | generator_list>;
end function;


function complementary_class_index_by_key(group_model)
    if assigned group_model`class_index_by_key then
        return group_model`class_index_by_key;
    end if;

    class_index_by_key := AssociativeArray();

    for i in [1..#group_model`class_representatives] do
        class_index_by_key[Sprint(group_model`class_representatives[i])] := i;
    end for;

    return class_index_by_key;
end function;


function complementary_normalize_modulus_ideal(integer_ring, modulus_input)
    if Type(modulus_input) eq RngOrdIdl then
        modulus_ideal := ideal<integer_ring | Generators(modulus_input)>;
    else
        modulus_ideal := ideal<integer_ring | modulus_input>;
    end if;

    if Norm(modulus_ideal) le 1 then
        error "modulus_ideal must be a nontrivial ideal.";
    end if;

    return modulus_ideal;
end function;


function complementary_ideal_from_exponent_vector(integer_ring, prime_list, exponent_vector)
    modulus_ideal := ideal<integer_ring | 1>;

    for i in [1..#prime_list] do
        if exponent_vector[i] eq 0 then
            continue;
        end if;

        modulus_ideal *:= prime_list[i]^exponent_vector[i];
    end for;

    return modulus_ideal;
end function;


function complementary_exponent_vector_from_ideal(modulus_ideal, prime_list)
    factor_lookup := AssociativeArray();
    exponent_vector := [0 : i in [1..#prime_list]];

    for factor in Factorization(modulus_ideal) do
        factor_lookup[Sprint(factor[1])] := factor[2];
    end for;

    for i in [1..#prime_list] do
        key := Sprint(prime_list[i]);
        if IsDefined(factor_lookup, key) then
            exponent_vector[i] := factor_lookup[key];
        end if;
    end for;

    return exponent_vector;
end function;


function complementary_vector_divides(vector_a, vector_b)
    return &and[vector_a[i] le vector_b[i] : i in [1..#vector_a]];
end function;


function complementary_vector_divisible_by_any(target_vector, candidate_vectors)
    for candidate_vector in candidate_vectors do
        if complementary_vector_divides(candidate_vector, target_vector) then
            return true;
        end if;
    end for;

    return false;
end function;


function complementary_vector_index(vectors, target_vector)
    for i in [1..#vectors] do
        if vectors[i] eq target_vector then
            return i;
        end if;
    end for;

    return 0;
end function;


procedure complementary_append_vector_if_new(target_vector, minimal_vectors, tested_lookup, ~frontier)
    if complementary_vector_divisible_by_any(target_vector, minimal_vectors) then
        return;
    end if;

    target_key := complementary_vector_key(target_vector);
    if IsDefined(tested_lookup, target_key) then
        return;
    end if;

    if complementary_vector_index(frontier, target_vector) ne 0 then
        return;
    end if;

    Append(~frontier, target_vector);
end procedure;


function complementary_all_subsets(prime_list)
    if #prime_list eq 0 then
        return [[]];
    end if;

    tail_subsets := complementary_all_subsets(prime_list[2..#prime_list]);
    head_subsets := [];

    for subset_prime_list in tail_subsets do
        Append(~head_subsets, [prime_list[1]] cat subset_prime_list);
    end for;

    return tail_subsets cat head_subsets;
end function;


function complementary_ramified_subset_string(ramified_subset)
    if #ramified_subset eq 0 then
        return "{}";
    end if;

    return "{ " cat complementary_join_strings(
        [ideal_summary("P", prime_ideal) : prime_ideal in complementary_sorted_ideals(ramified_subset)],
        ", "
    ) cat " }";
end function;


function complementary_warning_string(prime_ideal, exponent_k, localized_unit_group)
    return Sprintf(
        "Expected exponent bound exceeded while scanning T = %o: need exponent %o at %o.",
        complementary_ramified_subset_string(localized_unit_group`ramified_subset),
        exponent_k,
        ideal_summary("P", prime_ideal)
    );
end function;


function complementary_relevant_primes(order_data, norm_bound)
    relevant_primes := split_primes_up_to(order_data, norm_bound);

    for ramified_prime in ramified_primes(order_data) do
        append_prime_if_new(ramified_prime, ~relevant_primes);
    end for;

    return complementary_sorted_ideals(relevant_primes);
end function;


function complementary_algebra_identifier(order_data)
    return Sprint(Discriminant(order_data`quaternion_algebra));
end function;


function complementary_order_identifier(order_data)
    return Sprintf("%o:%o", order_data`index, order_data`label);
end function;


function validate_complementary_time_controls(
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds
)
    return validate_time_limit_seconds(time_limit_seconds),
           validate_estimated_time_control(
               max_projective_quotient_seconds,
               "max_projective_quotient_seconds"
           ),
           validate_estimated_time_control(
               max_reduced_unit_seconds,
               "max_reduced_unit_seconds"
           );
end function;


function complementary_triple_data_record(localized_unit_groups, minimal_ideal_results, complementary_triples)
    return rec<complementary_order_triple_data_format |
        localized_unit_groups := localized_unit_groups,
        minimal_ideal_results := minimal_ideal_results,
        complementary_triples := complementary_triples
    >;
end function;


function complementary_triple_data_is_trivial(order_result)
    return Type(order_result`triple_data) eq MonStgElt and order_result`triple_data eq "trivial";
end function;


function complementary_order_triples(order_result)
    if complementary_triple_data_is_trivial(order_result) then
        return [];
    end if;

    return order_result`triple_data`complementary_triples;
end function;


function complementary_order_minimal_ideal_results(order_result)
    if complementary_triple_data_is_trivial(order_result) then
        return [];
    end if;

    return order_result`triple_data`minimal_ideal_results;
end function;


function admissible_ramified_primes(order_data)
    return complementary_sorted_ideals([
        prime_ideal :
        prime_ideal in ramified_primes(order_data) |
        order_is_locally_maximal_at_prime(order_data, prime_ideal)
    ]);
end function;


function complementary_build_context(order_data)
    normalizer_lookup := AssociativeArray();
    normalizer_representative_lookup := AssociativeArray();

    for normalizer_group_element in order_data`normalizer_group do
        normalizer_element := primitive_integral_order_representative(
            order_data,
            order_data`normalizer_map(normalizer_group_element)
        );
        normalizer_lookup[
            complementary_normalized_order_element_key(order_data, normalizer_element)
        ] := normalizer_group_element;
        normalizer_representative_lookup[Sprint(normalizer_group_element)] := normalizer_element;
    end for;

    return rec<complementary_context_format |
        order_data := order_data,
        normalizer_lookup := normalizer_lookup,
        normalizer_representative_lookup := normalizer_representative_lookup,
        alpha_data := AssociativeArray(),
        localized_unit_group_cache := AssociativeArray(),
        local_group_model_cache := AssociativeArray(),
        local_image_cache := AssociativeArray(),
        ideal_result_cache := AssociativeArray(),
        ideal_result_ambient_cache := AssociativeArray(),
        skipped_estimated_tasks := [],
        exponent_bound_warnings := []
    >;
end function;


function complementary_normalized_ramified_subset(order_data, ramified_subset)
    integer_ring := order_data`integer_ring;
    admissible_primes := admissible_ramified_primes(order_data);
    normalized_subset := [];
    seen := AssociativeArray();

    if Type(ramified_subset) ne SeqEnum then
        error "T must be a sequence of ramified prime ideals.";
    end if;

    for prime_data in ramified_subset do
        prime_ideal := normalize_prime_ideal(integer_ring, prime_data);

        if Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) eq 0 then
            error "T may only contain ramified primes of the quaternion algebra.";
        end if;

        if Index(admissible_primes, prime_ideal) eq 0 then
            error Sprintf(
                "T contains the inadmissible ramified prime %o; O_p is not maximal there.",
                prime_ideal
            );
        end if;

        if IsDefined(seen, Sprint(prime_ideal)) then
            error "T contains a duplicate ramified prime.";
        end if;

        seen[Sprint(prime_ideal)] := true;
        Append(~normalized_subset, prime_ideal);
    end for;

    return complementary_sorted_ideals(normalized_subset);
end function;


function complementary_normalizer_group_element(context, element_x)
    key := complementary_normalized_order_element_key(context`order_data, element_x);

    if not IsDefined(context`normalizer_lookup, key) then
        error "Could not match an order element to the stored normalizer group.";
    end if;

    return context`normalizer_lookup[key];
end function;


function complementary_normalizer_representative(context, group_element)
    key := Sprint(group_element);

    if not IsDefined(context`normalizer_representative_lookup, key) then
        error "Could not match a normalizer-group element to a stored quaternion representative.";
    end if;

    return context`normalizer_representative_lookup[key];
end function;


function complementary_unit_generators_in_normalizer(context)
    order_data := context`order_data;
    generator_group_elements := [];
    generator_elements := [];

    for i in [1..Ngens(order_data`unit_group)] do
        unit_element := primitive_integral_order_representative(
            order_data,
            order_data`unit_map(order_data`unit_group.i)
        );
        Append(~generator_group_elements, complementary_normalizer_group_element(context, unit_element));
        Append(~generator_elements, unit_element);
    end for;

    return generator_group_elements, generator_elements;
end function;


function complementary_localized_unit_group_record(
    order_data,
    admissible_primes,
    ramified_subset,
    subgroup,
    generator_primes,
    generator_group_elements,
    generator_elements
)
    return rec<localized_unit_group_format |
        order_data := order_data,
        admissible_ramified_primes := admissible_primes,
        ramified_subset := ramified_subset,
        ramified_subset_key := complementary_subset_key(ramified_subset),
        subgroup := subgroup,
        subgroup_order := #subgroup,
        generator_primes := generator_primes,
        generator_group_elements := generator_group_elements,
        generator_elements := generator_elements
    >;
end function;


procedure complementary_alpha_record(~context, prime_ideal, ~alpha_record)
    if IsDefined(context`alpha_data, prime_ideal) then
        alpha_record := context`alpha_data[prime_ideal];
        return;
    end if;

    order_data := context`order_data;
    admissible_primes := admissible_ramified_primes(order_data);

    if Index(admissible_primes, prime_ideal) eq 0 then
        error Sprintf("The ramified prime %o is not admissible for T.", prime_ideal);
    end if;

    if order_data`order_type lt 2 then
        error "Nonempty T is only supported for Eichler orders (order_type >= 2).";
    end if;

    if order_data`class_number ne 1 then
        error "Nonempty T is only supported for class-number-one orders.";
    end if;

    alpha_element := ramified_base_generator(order_data, prime_ideal);
    alpha_group_element := complementary_normalizer_group_element(context, alpha_element);
    alpha_record := rec<localized_alpha_data_format |
        prime_ideal := prime_ideal,
        alpha_element := alpha_element,
        normalizer_group_element := alpha_group_element
    >;

    context`alpha_data[prime_ideal] := alpha_record;
end procedure;


function compute_alpha_p_data(order_data)
    context := complementary_build_context(order_data);
    alpha_records := [];

    for prime_ideal in admissible_ramified_primes(order_data) do
        alpha_record := false;
        complementary_alpha_record(~context, prime_ideal, ~alpha_record);
        Append(~alpha_records, alpha_record);
    end for;

    return alpha_records;
end function;


procedure complementary_localized_unit_group_from_subset(~context, ramified_subset, ~localized_group)
    order_data := context`order_data;
    normalized_subset := complementary_normalized_ramified_subset(order_data, ramified_subset);
    admissible_primes := admissible_ramified_primes(order_data);
    subset_key := complementary_subset_key(normalized_subset);

    if IsDefined(context`localized_unit_group_cache, subset_key) then
        localized_group := context`localized_unit_group_cache[subset_key];
        return;
    end if;

    if #normalized_subset eq 0 then
        unit_generator_group_elements, unit_generator_elements :=
            complementary_unit_generators_in_normalizer(context);
        unit_subgroup := complementary_subgroup_from_generators(
            order_data`normalizer_group,
            unit_generator_group_elements
        );

        if #unit_subgroup ne #order_data`unit_group then
            error "The embedded U_empty subgroup does not match the stored unit group order.";
        end if;

        localized_group := complementary_localized_unit_group_record(
            order_data,
            admissible_primes,
            [],
            unit_subgroup,
            [],
            unit_generator_group_elements,
            unit_generator_elements
        );
        context`localized_unit_group_cache[subset_key] := localized_group;
        return;
    end if;

    previous_subset := normalized_subset[1..#normalized_subset - 1];
    previous_group := false;
    complementary_localized_unit_group_from_subset(~context, previous_subset, ~previous_group);
    last_prime := normalized_subset[#normalized_subset];
    alpha_record := false;
    complementary_alpha_record(~context, last_prime, ~alpha_record);
    generator_primes := previous_group`generator_primes cat [last_prime];
    generator_group_elements :=
        previous_group`generator_group_elements cat [alpha_record`normalizer_group_element];
    generator_elements := previous_group`generator_elements cat [alpha_record`alpha_element];
    subgroup := complementary_subgroup_from_generators(
        order_data`normalizer_group,
        generator_group_elements
    );
    localized_group := complementary_localized_unit_group_record(
        order_data,
        admissible_primes,
        normalized_subset,
        subgroup,
        generator_primes,
        generator_group_elements,
        generator_elements
    );
    context`localized_unit_group_cache[subset_key] := localized_group;
end procedure;


function compute_U_empty(order_data)
    context := complementary_build_context(order_data);
    localized_group := false;
    complementary_localized_unit_group_from_subset(~context, [], ~localized_group);
    return localized_group;
end function;


function complementary_context_with_all_U_T(order_data)
    context := complementary_build_context(order_data);
    admissible_primes := admissible_ramified_primes(order_data);
    localized_groups := [];

    for ramified_subset in complementary_all_subsets(admissible_primes) do
        localized_group := false;
        complementary_localized_unit_group_from_subset(~context, ramified_subset, ~localized_group);
        Append(~localized_groups, localized_group);
    end for;

    return context, localized_groups;
end function;


function complementary_localized_unit_group_from_prime_sequence(order_data, prime_sequence)
    context := complementary_build_context(order_data);
    normalized_sequence := complementary_normalized_ramified_subset(order_data, prime_sequence);
    empty_group := false;
    complementary_localized_unit_group_from_subset(~context, [], ~empty_group);
    generator_group_elements := empty_group`generator_group_elements;
    generator_elements := empty_group`generator_elements;

    for prime_ideal in normalized_sequence do
        alpha_record := false;
        complementary_alpha_record(~context, prime_ideal, ~alpha_record);
        Append(~generator_group_elements, alpha_record`normalizer_group_element);
        Append(~generator_elements, alpha_record`alpha_element);
    end for;

    return complementary_localized_unit_group_record(
        order_data,
        admissible_ramified_primes(order_data),
        complementary_sorted_ideals(normalized_sequence),
        complementary_subgroup_from_generators(order_data`normalizer_group, generator_group_elements),
        normalized_sequence,
        generator_group_elements,
        generator_elements
    );
end function;


function compute_all_U_T(order_data : consistency_check := false)
    if Type(consistency_check) ne BoolElt then
        error "consistency_check must be true or false.";
    end if;

    context, localized_groups := complementary_context_with_all_U_T(order_data);

    if consistency_check then
        admissible_primes := admissible_ramified_primes(order_data);

        for localized_group in localized_groups do
            if #localized_group`ramified_subset le 1 then
                continue;
            end if;

            reversed_group := complementary_localized_unit_group_from_prime_sequence(
                order_data,
                Reverse(localized_group`ramified_subset)
            );
            if localized_group`subgroup ne reversed_group`subgroup then
                error Sprintf(
                    "Inductive U_T construction is not order-independent for T = %o.",
                    complementary_ramified_subset_string(localized_group`ramified_subset)
                );
            end if;
        end for;
    end if;

    return localized_groups;
end function;


function local_reduction_group(
    order_data,
    prime_ideal,
    k :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    compute_complements := true
)
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );

    return build_projective_unit_group(
        order_data,
        prime_ideal,
        k :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds,
        compute_complements := compute_complements
    );
end function;


procedure complementary_local_group_model(
    ~context,
    prime_ideal,
    k,
    ~group_model :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    cache_key := Sprintf("%o || %o", Sprint(prime_ideal), k);

    if IsDefined(context`local_group_model_cache, cache_key) then
        group_model := context`local_group_model_cache[cache_key];
        return;
    end if;

    group_model := local_reduction_group(
        context`order_data,
        prime_ideal,
        k :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds,
        compute_complements := false
    );

    if not group_model`skipped_due_to_estimate then
        context`local_group_model_cache[cache_key] := group_model;
    end if;
end procedure;


procedure complementary_projective_image_permutation(
    group_model,
    order_element,
    label,
    ~image_permutation
)
    class_index_by_key := complementary_class_index_by_key(group_model);
    reduced_unit_lookup_data := assigned group_model`reduced_unit_membership select
        group_model`reduced_unit_membership else
        reduced_unit_lookup(group_model`reduced_units);
    class_key_data := assigned group_model`class_key_data select
        group_model`class_key_data else false;
    reduced_to_permutation := group_model`reduced_to_permutation;
    permutation_to_reduced := group_model`permutation_to_reduced;
    ok, reduced_element, message := reduce_order_element_mod_modulus(
        group_model`order_data,
        order_element,
        group_model`reduction_map,
        group_model`reduced_algebra
    );

    if not ok then
        error message;
    end if;

    if not reduced_element_is_unit(reduced_element, reduced_unit_lookup_data) then
        error Sprintf(
            "An element of U_T did not reduce to a projective unit at %o.",
            ideal_summary("modulus", group_model`modulus_ideal)
        );
    end if;

    cached_projective_permutation(
        group_model`order_data,
        group_model`reduced_algebra,
        group_model`class_representatives,
        class_index_by_key,
        group_model`scalars,
        class_key_data,
        reduced_element,
        order_element,
        label,
        ~image_permutation,
        ~reduced_to_permutation,
        ~permutation_to_reduced
    );
end procedure;


procedure complementary_assert_reduction_image_order(
    localized_unit_group,
    modulus_ideal,
    image_subgroup,
    stage_label
)
    source_order := localized_unit_group`subgroup_order;
    image_order := #image_subgroup;

    if (source_order mod image_order) ne 0 then
        error Sprintf(
            "Impossible %o: image subgroup order %o does not divide |U_T| = %o for T = %o at %o. This indicates that the computed reduction image is not a homomorphic image of U_T.",
            stage_label,
            image_order,
            source_order,
            complementary_ramified_subset_string(localized_unit_group`ramified_subset),
            ideal_summary("modulus", modulus_ideal)
        );
    end if;
end procedure;


function complementary_local_reduction_image_record(
    localized_unit_group,
    prime_ideal,
    k,
    modulus_ideal,
    group_model,
    ambient_group,
    image_subgroup,
    generator_images,
    injective,
    uses_ramified_extension
)
    complementary_assert_reduction_image_order(
        localized_unit_group,
        modulus_ideal,
        image_subgroup,
        "local reduction image"
    );

    return rec<localized_reduction_image_format |
        localized_unit_group := localized_unit_group,
        prime_ideal := prime_ideal,
        prime_power_exponent := k,
        modulus_ideal := modulus_ideal,
        group_model := group_model,
        ambient_group := ambient_group,
        image_subgroup := image_subgroup,
        generator_images := generator_images,
        injective := injective,
        uses_ramified_extension := uses_ramified_extension,
        skipped_due_to_estimate := false,
        skipped_task_key := "",
        skipped_estimated_seconds := 0
    >;
end function;


function complementary_skipped_local_reduction_image(localized_unit_group, prime_ideal, k, group_model)
    return rec<localized_reduction_image_format |
        localized_unit_group := localized_unit_group,
        prime_ideal := prime_ideal,
        prime_power_exponent := k,
        modulus_ideal := group_model`modulus_ideal,
        group_model := group_model,
        skipped_due_to_estimate := true,
        skipped_task_key := group_model`skipped_task_key,
        skipped_estimated_seconds := group_model`skipped_estimated_seconds
    >;
end function;


procedure complementary_local_reduction_image(
    ~context,
    localized_unit_group,
    prime_ideal,
    k,
    ~local_result :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    uses_ramified_extension :=
        Valuation(Discriminant(context`order_data`quaternion_algebra), prime_ideal) ne 0 and
        Index(localized_unit_group`ramified_subset, prime_ideal) ne 0;
    cache_key := Sprintf(
        "%o || %o || %o || %o",
        localized_unit_group`ramified_subset_key,
        Sprint(prime_ideal),
        k,
        uses_ramified_extension
    );

    if IsDefined(context`local_image_cache, cache_key) then
        local_result := context`local_image_cache[cache_key];
        return;
    end if;

    group_model := false;
    complementary_local_group_model(
        ~context,
        prime_ideal,
        k,
        ~group_model :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds
    );

    if group_model`skipped_due_to_estimate then
        local_result := complementary_skipped_local_reduction_image(
            localized_unit_group,
            prime_ideal,
            k,
            group_model
        );
        return;
    end if;

    if uses_ramified_extension then
        if not group_model`normalizer_image_defined then
            error "The ramified Z/2Z extension was not available for a prime in T.";
        end if;

        ambient_group := group_model`normalizer_ambient_group;
        generator_images := [
            group_model`normalizer_image_map(group_element) :
            group_element in localized_unit_group`generator_group_elements
        ];
    else
        ambient_group := group_model`projective_unit_group;
        generator_images := [];

        for generator_element in localized_unit_group`generator_elements do
            image_permutation := false;
            complementary_projective_image_permutation(
                group_model,
                generator_element,
                "localized unit group",
                ~image_permutation
            );
            // cached_projective_permutation returns left-action permutations.
            // Magma composes permutations on the right, so inverting gives the
            // homomorphic convention used by the normalizer-image path.
            Append(~generator_images, image_permutation^-1);
        end for;
    end if;

    image_subgroup := complementary_subgroup_from_generators(ambient_group, generator_images);
    local_result := complementary_local_reduction_image_record(
        localized_unit_group,
        prime_ideal,
        k,
        prime_ideal^k,
        group_model,
        ambient_group,
        image_subgroup,
        generator_images,
        #image_subgroup eq localized_unit_group`subgroup_order,
        uses_ramified_extension
    );
    context`local_image_cache[cache_key] := local_result;
end procedure;


function reduction_image_of_U_T(
    localized_unit_group,
    prime_ideal,
    k :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );
    context := complementary_build_context(localized_unit_group`order_data);
    localized_group := false;
    local_result := false;

    complementary_localized_unit_group_from_subset(
        ~context,
        localized_unit_group`ramified_subset,
        ~localized_group
    );
    complementary_local_reduction_image(
        ~context,
        localized_group,
        prime_ideal,
        k,
        ~local_result :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds
    );

    return local_result;
end function;


function complementary_embedded_block_permutation(block_permutation, offset, total_degree)
    permutation_entries := [i : i in [1..total_degree]];
    block_degree := Degree(Parent(block_permutation));

    for i in [1..block_degree] do
        permutation_entries[offset + i] := offset + (i^block_permutation);
    end for;

    return Sym(total_degree)!permutation_entries;
end function;


function complementary_composite_ambient_and_image(reduction_factors, localized_unit_group)
    total_degree := &+[Degree(reduction_factor`ambient_group) : reduction_factor in reduction_factors];
    symmetric_group := Sym(total_degree);
    ambient_generators := [];
    offsets := [];
    running_offset := 0;

    for reduction_factor in reduction_factors do
        Append(~offsets, running_offset);

        for i in [1..Ngens(reduction_factor`ambient_group)] do
            Append(
                ~ambient_generators,
                complementary_embedded_block_permutation(
                    reduction_factor`ambient_group.i,
                    running_offset,
                    total_degree
                )
            );
        end for;

        running_offset +:= Degree(reduction_factor`ambient_group);
    end for;

    ambient_group := complementary_subgroup_from_generators(symmetric_group, ambient_generators);
    image_generators := [];

    for generator_index in [1..#localized_unit_group`generator_elements] do
        global_generator := Identity(symmetric_group);

        for factor_index in [1..#reduction_factors] do
            embedded_factor_generator := complementary_embedded_block_permutation(
                reduction_factors[factor_index]`generator_images[generator_index],
                offsets[factor_index],
                total_degree
            );
            global_generator *:= embedded_factor_generator;
        end for;

        Append(~image_generators, global_generator);
    end for;

    image_subgroup := complementary_subgroup_from_generators(ambient_group, image_generators);
    return ambient_group, image_subgroup;
end function;


function complementary_ideal_result_record(
    localized_unit_group,
    modulus_ideal,
    factor_primes,
    factor_exponents,
    reduction_factors,
    ambient_group,
    image_subgroup,
    complement_list,
    normal_complement_list,
    complements_computed,
    injective
)
    complementary_assert_reduction_image_order(
        localized_unit_group,
        modulus_ideal,
        image_subgroup,
        "ideal reduction image"
    );

    return rec<complementary_ideal_result_format |
        localized_unit_group := localized_unit_group,
        modulus_ideal := modulus_ideal,
        factor_primes := factor_primes,
        factor_exponents := factor_exponents,
        reduction_factors := reduction_factors,
        ambient_group := ambient_group,
        image_subgroup := image_subgroup,
        complement_classes := complement_list,
        normal_complement_classes := normal_complement_list,
        complements_computed := complements_computed,
        injective := injective,
        skipped_due_to_estimate := false,
        skipped_estimated_tasks := []
    >;
end function;


function complementary_skipped_ideal_result(localized_unit_group, modulus_ideal, reduction_factors)
    skipped_estimated_tasks := [];

    for reduction_factor in reduction_factors do
        if reduction_factor`skipped_due_to_estimate then
            append_skipped_task_if_new(
                reduction_factor`skipped_task_key,
                reduction_factor`modulus_ideal,
                reduction_factor`skipped_estimated_seconds,
                ~skipped_estimated_tasks
            );
        end if;
    end for;

    return rec<complementary_ideal_result_format |
        localized_unit_group := localized_unit_group,
        modulus_ideal := modulus_ideal,
        factor_primes := [reduction_factor`prime_ideal : reduction_factor in reduction_factors],
        factor_exponents := [reduction_factor`prime_power_exponent : reduction_factor in reduction_factors],
        reduction_factors := reduction_factors,
        complements_computed := false,
        skipped_due_to_estimate := true,
        skipped_estimated_tasks := skipped_estimated_tasks
    >;
end function;


function complementary_ambient_ideal_result_from_image_result(image_result)
    if image_result`skipped_due_to_estimate then
        return image_result;
    end if;

    if image_result`complements_computed then
        return image_result;
    end if;

    complement_list := complement_classes(image_result`ambient_group, image_result`image_subgroup);

    return complementary_ideal_result_record(
        image_result`localized_unit_group,
        image_result`modulus_ideal,
        image_result`factor_primes,
        image_result`factor_exponents,
        image_result`reduction_factors,
        image_result`ambient_group,
        image_result`image_subgroup,
        complement_list,
        normal_complement_classes(image_result`ambient_group, complement_list),
        true,
        image_result`injective
    );
end function;


procedure complementary_pairs_at_ideal_with_context(
    ~context,
    localized_unit_group,
    modulus_ideal,
    ~ideal_result :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    require_ambient := true
)
    normalized_modulus := complementary_normalize_modulus_ideal(
        context`order_data`integer_ring,
        modulus_ideal
    );
    cache_key := Sprintf("%o || %o", localized_unit_group`ramified_subset_key, Sprint(normalized_modulus));

    if require_ambient and IsDefined(context`ideal_result_ambient_cache, cache_key) then
        ideal_result := context`ideal_result_ambient_cache[cache_key];
        return;
    end if;

    if IsDefined(context`ideal_result_cache, cache_key) then
        ideal_result := context`ideal_result_cache[cache_key];

        if require_ambient then
            ideal_result := complementary_ambient_ideal_result_from_image_result(ideal_result);
            context`ideal_result_ambient_cache[cache_key] := ideal_result;
        end if;

        return;
    end if;

    factor_data := Factorization(normalized_modulus);
    factor_primes := [factor[1] : factor in factor_data];
    factor_exponents := [factor[2] : factor in factor_data];
    reduction_factors := [];

    for factor in factor_data do
        local_result := false;
        complementary_local_reduction_image(
            ~context,
            localized_unit_group,
            factor[1],
            factor[2],
            ~local_result :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );
        Append(~reduction_factors, local_result);
    end for;

    if &or[reduction_factor`skipped_due_to_estimate : reduction_factor in reduction_factors] then
        ideal_result := complementary_skipped_ideal_result(
            localized_unit_group,
            normalized_modulus,
            reduction_factors
        );
        return;
    end if;

    if #reduction_factors eq 1 then
        ambient_group := reduction_factors[1]`ambient_group;
        image_subgroup := reduction_factors[1]`image_subgroup;
    else
        ambient_group, image_subgroup := complementary_composite_ambient_and_image(
            reduction_factors,
            localized_unit_group
        );
    end if;

    ideal_result := complementary_ideal_result_record(
        localized_unit_group,
        normalized_modulus,
        factor_primes,
        factor_exponents,
        reduction_factors,
        ambient_group,
        image_subgroup,
        [],
        [],
        false,
        #image_subgroup eq localized_unit_group`subgroup_order
    );
    context`ideal_result_cache[cache_key] := ideal_result;

    if require_ambient then
        ideal_result := complementary_ambient_ideal_result_from_image_result(ideal_result);
        context`ideal_result_ambient_cache[cache_key] := ideal_result;
    end if;
end procedure;


function complementary_pairs_at_ideal(
    order_data,
    modulus_ideal :
    T := [],
    context := false,
    require_ambient := true,
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
    if context cmpeq false then
        context := complementary_build_context(order_data);
    elif Type(context) ne Rec then
        error "context must be false or a complementary context record.";
    end if;
    localized_unit_group := false;
    ideal_result := false;

    complementary_localized_unit_group_from_subset(~context, T, ~localized_unit_group);
    complementary_pairs_at_ideal_with_context(
        ~context,
        localized_unit_group,
        modulus_ideal,
        ~ideal_result :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds,
        require_ambient := require_ambient
    );

    return ideal_result;
end function;


function complementary_pairs_for_order(
    base_field,
    quaternion_algebra,
    quaternion_order,
    modulus_ideal :
    T := [],
    label := "explicit",
    order_type := 4,
    class_number := 0,
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    order_data := build_order_data_for_order(
        0,
        base_field,
        quaternion_algebra,
        quaternion_order :
        label := label,
        order_type := order_type,
        class_number := class_number
    );

    return complementary_pairs_at_ideal(
        order_data,
        modulus_ideal :
        T := T,
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds
    );
end function;


function complementary_prime_power_group_model(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        error "Cannot extract a local group model from a skipped complementary result.";
    end if;

    if #complementary_result`reduction_factors ne 1 then
        error "This operation requires a prime-power complementary result.";
    end if;

    return complementary_result`reduction_factors[1]`group_model;
end function;


function complementary_triple_record(order_data, localized_unit_group, modulus_ideal, complementary_result)
    return rec<complementary_triple_format |
        algebra_identifier := complementary_algebra_identifier(order_data),
        order_identifier := complementary_order_identifier(order_data),
        order_data := order_data,
        localized_unit_group := localized_unit_group,
        ramified_subset := localized_unit_group`ramified_subset,
        modulus_ideal := modulus_ideal,
        complementary_result := complementary_result
    >;
end function;


function scan_prime_power_complementary_triples(
    order_data,
    prime_ideal,
    max_exponent :
    T := [],
    context := false,
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    require_ambient := true
)
    Print := validate_print_level(Print);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );

    if Type(max_exponent) ne RngIntElt or max_exponent lt 1 then
        error "max_exponent must be an integer >= 1.";
    end if;

    if context cmpeq false then
        context := complementary_build_context(order_data);
    elif Type(context) ne Rec then
        error "context must be false or a complementary context record.";
    end if;

    prime_ideal := normalize_prime_ideal(order_data`integer_ring, prime_ideal);
    localized_unit_group := false;
    ideal_results := [];
    complementary_triples := [];
    skipped_estimated_tasks := [];

    complementary_localized_unit_group_from_subset(~context, T, ~localized_unit_group);

    if print_is_concise(Print) then
        print "";
        print "============================================================";
        print "[CI prime powers] Complementary triples at prime powers";
        print "============================================================";
        print "[CI prime powers] T=", complementary_ramified_subset_string(localized_unit_group`ramified_subset),
              "|", ideal_summary("P", prime_ideal),
              "| max_exponent=", max_exponent;
    end if;

    for exponent_k in [1..max_exponent] do
        modulus_ideal := prime_ideal^exponent_k;
        ideal_result := false;

        complementary_pairs_at_ideal_with_context(
            ~context,
            localized_unit_group,
            modulus_ideal,
            ~ideal_result :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds,
            require_ambient := require_ambient
        );
        Append(~ideal_results, ideal_result);

        if ideal_result`skipped_due_to_estimate then
            for skipped_task in ideal_result`skipped_estimated_tasks do
                append_skipped_task_if_new(
                    skipped_task[1],
                    skipped_task[2],
                    skipped_task[3],
                    ~skipped_estimated_tasks
                );
            end for;

            if print_is_concise(Print) then
                print "[CI prime powers] skipped |", ideal_summary("I", modulus_ideal);
            end if;
            break;
        end if;

        Append(
            ~complementary_triples,
            complementary_triple_record(
                order_data,
                localized_unit_group,
                modulus_ideal,
                ideal_result
            )
        );

        if print_is_concise(Print) then
            print "[CI prime powers] result |",
                  ideal_summary("I", modulus_ideal),
                  "| injective=", ideal_result`injective,
                  "| complements=", require_ambient select #ideal_result`complement_classes else 0;
        end if;
    end for;

    return rec<prime_power_complementary_scan_format |
        localized_unit_group := localized_unit_group,
        prime_ideal := prime_ideal,
        max_exponent := max_exponent,
        ideal_results := ideal_results,
        complementary_triples := complementary_triples,
        skipped_estimated_tasks := skipped_estimated_tasks
    >;
end function;


function is_reduction_injective(
    localized_unit_group,
    modulus_ideal :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    reduction_result := complementary_pairs_at_ideal(
        localized_unit_group`order_data,
        modulus_ideal :
        T := localized_unit_group`ramified_subset,
        require_ambient := false,
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds
    );

    return (not reduction_result`skipped_due_to_estimate) and reduction_result`injective;
end function;


procedure minimal_ideal_poset_with_context(
    ~context,
    localized_unit_group,
    norm_bound,
    ~poset_result :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    expected_exponent_bound := 2,
    allow_higher_exponents := true
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

    if Type(expected_exponent_bound) ne RngIntElt or expected_exponent_bound lt 0 then
        error "expected_exponent_bound must be an integer >= 0.";
    end if;

    if Type(allow_higher_exponents) ne BoolElt then
        error "allow_higher_exponents must be true or false.";
    end if;

    relevant_primes := complementary_relevant_primes(context`order_data, norm_bound);
    frontier := [];
    tested_lookup := AssociativeArray();
    tested_ideals := [];
    minimal_vectors := [];
    minimal_ideals := [];
    minimal_results := [];
    skipped_ideals := [];
    skipped_estimated_tasks := [];
    exponent_bound_warnings := [];
    warning_lookup := AssociativeArray();

    if print_is_concise(Print) then
        print "";
        print "============================================================";
        print "[CI poset] Minimal injective ideals";
        print "============================================================";
        print "[CI poset] T=", complementary_ramified_subset_string(localized_unit_group`ramified_subset),
              "| norm_bound=", norm_bound,
              "| relevant_primes=", #relevant_primes,
              "| expected_exponent_bound=", expected_exponent_bound,
              "| allow_higher_exponents=", allow_higher_exponents;
    end if;

    for i in [1..#relevant_primes] do
        initial_vector := [0 : j in [1..#relevant_primes]];
        initial_vector[i] := 1;
        Append(~frontier, initial_vector);
    end for;

    while #frontier gt 0 do
        exponent_vector := frontier[1];
        Remove(~frontier, 1);

        if complementary_vector_divisible_by_any(exponent_vector, minimal_vectors) then
            continue;
        end if;

        exponent_key := complementary_vector_key(exponent_vector);
        if IsDefined(tested_lookup, exponent_key) then
            continue;
        end if;
        tested_lookup[exponent_key] := true;

        modulus_ideal := complementary_ideal_from_exponent_vector(
            context`order_data`integer_ring,
            relevant_primes,
            exponent_vector
        );
        Append(~tested_ideals, modulus_ideal);

        if print_is_concise(Print) then
            print "[CI poset] test |", ideal_summary("I", modulus_ideal);
        end if;

        reduction_result := false;
        complementary_pairs_at_ideal_with_context(
            ~context,
            localized_unit_group,
            modulus_ideal,
            ~reduction_result :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds,
            require_ambient := false
        );

        if reduction_result`skipped_due_to_estimate then
            append_ideal_if_new(modulus_ideal, ~skipped_ideals);

            for skipped_task in reduction_result`skipped_estimated_tasks do
                append_skipped_task_if_new(
                    skipped_task[1],
                    skipped_task[2],
                    skipped_task[3],
                    ~skipped_estimated_tasks
                );
            end for;

            if print_is_concise(Print) then
                print "[CI poset] skipped |", ideal_summary("I", modulus_ideal);
            end if;

            continue;
        end if;

        if reduction_result`injective then
            ambient_result := false;
            complementary_pairs_at_ideal_with_context(
                ~context,
                localized_unit_group,
                modulus_ideal,
                ~ambient_result :
                Print := Print,
                time_limit_seconds := time_limit_seconds,
                max_projective_quotient_seconds := max_projective_quotient_seconds,
                max_reduced_unit_seconds := max_reduced_unit_seconds,
                require_ambient := true
            );
            Append(~minimal_vectors, exponent_vector);
            Append(~minimal_ideals, modulus_ideal);
            Append(~minimal_results, ambient_result);

            if print_is_concise(Print) then
                print "[CI poset] minimal injective |",
                      ideal_summary("I", modulus_ideal),
                      "| complements=", #ambient_result`complement_classes,
                      "| normal_complements=", #ambient_result`normal_complement_classes;
            end if;

            continue;
        end if;

        for i in [1..#relevant_primes] do
            successor_vector := exponent_vector;
            successor_vector[i] +:= 1;

            if successor_vector[i] gt expected_exponent_bound then
                warning_string := complementary_warning_string(
                    relevant_primes[i],
                    successor_vector[i],
                    localized_unit_group
                );

                if not IsDefined(warning_lookup, warning_string) then
                    warning_lookup[warning_string] := true;
                    Append(~exponent_bound_warnings, warning_string);

                    if print_is_concise(Print) then
                        print "[CI poset] warning |", warning_string;
                    end if;
                end if;

                if not allow_higher_exponents then
                    error warning_string;
                end if;
            end if;

            complementary_append_vector_if_new(
                successor_vector,
                minimal_vectors,
                tested_lookup,
                ~frontier
            );
        end for;
    end while;

    poset_result := rec<minimal_ideal_poset_result_format |
        localized_unit_group := localized_unit_group,
        relevant_primes := relevant_primes,
        norm_bound := norm_bound,
        expected_exponent_bound := expected_exponent_bound,
        allow_higher_exponents := allow_higher_exponents,
        minimal_injective_ideals := minimal_ideals,
        minimal_results := minimal_results,
        tested_ideals := tested_ideals,
        skipped_ideals := skipped_ideals,
        skipped_estimated_tasks := skipped_estimated_tasks,
        exponent_bound_warnings := exponent_bound_warnings
    >;
end procedure;


function minimal_ideal_poset(
    order_data,
    T,
    norm_bound :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    expected_exponent_bound := 2,
    allow_higher_exponents := true
)
    context := complementary_build_context(order_data);
    localized_unit_group := false;
    poset_result := false;

    complementary_localized_unit_group_from_subset(~context, T, ~localized_unit_group);
    minimal_ideal_poset_with_context(
        ~context,
        localized_unit_group,
        norm_bound,
        ~poset_result :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds,
        expected_exponent_bound := expected_exponent_bound,
        allow_higher_exponents := allow_higher_exponents
    );

    return poset_result;
end function;


function complementary_multi_order_skipped_task_key(order_data, skipped_task)
    return Sprintf(
        "%o || %o || %o",
        complementary_order_identifier(order_data),
        skipped_task[1],
        ideal_key(skipped_task[2])
    );
end function;


function complementary_multi_order_skipped_task_record(order_data, skipped_task)
    return <
        complementary_order_identifier(order_data),
        skipped_task[1],
        ideal_summary("modulus", skipped_task[2]),
        skipped_task[3]
    >;
end function;


function scan_order_for_complementary_triples(
    order_data,
    norm_bound :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    expected_exponent_bound := 2,
    allow_higher_exponents := true,
    consistency_check := false
)
    Print := validate_print_level(Print);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );

    if Type(consistency_check) ne BoolElt then
        error "consistency_check must be true or false.";
    end if;

    timer := Cputime();
    admissible_primes := admissible_ramified_primes(order_data);
    unit_quotient_order := #order_data`unit_group;

    if print_is_concise(Print) then
        print "";
        print "============================================================";
        print "[CI order] Scan order for complementary triples";
        print "============================================================";
        print "[CI order] order=", complementary_order_identifier(order_data),
              "| admissible_ramified_primes=", #admissible_primes,
              "| unit_quotient_order=", unit_quotient_order,
              "| norm_bound=", norm_bound;
    end if;

    context, localized_unit_groups := complementary_context_with_all_U_T(order_data);

    if unit_quotient_order eq 1 then
        localized_unit_groups := [
            localized_group :
            localized_group in localized_unit_groups |
            #localized_group`ramified_subset gt 0
        ];

        if print_is_concise(Print) then
            print "[CI order] trivial unit quotient | skipping T={} search only",
                  "| nonempty_T_subsets=", #localized_unit_groups;
        end if;
    end if;

    minimal_ideal_results := [];
    complementary_triples := [];
    skipped_estimated_tasks := [];
    exponent_bound_warnings := [];

    if print_is_concise(Print) then
        print "[CI order] T_subsets=", #localized_unit_groups;
    end if;

    if consistency_check then
        for localized_group in localized_unit_groups do
            if #localized_group`ramified_subset le 1 then
                continue;
            end if;

            reversed_group := complementary_localized_unit_group_from_prime_sequence(
                order_data,
                Reverse(localized_group`ramified_subset)
            );
            if localized_group`subgroup ne reversed_group`subgroup then
                error Sprintf(
                    "Inductive U_T construction is not order-independent for T = %o.",
                    complementary_ramified_subset_string(localized_group`ramified_subset)
                );
            end if;
        end for;
    end if;

    for localized_group in localized_unit_groups do
        if print_is_concise(Print) then
            print "";
            print "[CI order] T=", complementary_ramified_subset_string(localized_group`ramified_subset),
                  "| #U_T=", localized_group`subgroup_order;
        end if;

        poset_result := false;
        minimal_ideal_poset_with_context(
            ~context,
            localized_group,
            norm_bound,
            ~poset_result :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds,
            expected_exponent_bound := expected_exponent_bound,
            allow_higher_exponents := allow_higher_exponents
        );
        Append(~minimal_ideal_results, poset_result);

        for skipped_task in poset_result`skipped_estimated_tasks do
            append_skipped_task_if_new(
                skipped_task[1],
                skipped_task[2],
                skipped_task[3],
                ~skipped_estimated_tasks
            );
        end for;

        for warning_string in poset_result`exponent_bound_warnings do
            if Index(exponent_bound_warnings, warning_string) eq 0 then
                Append(~exponent_bound_warnings, warning_string);
            end if;
        end for;

        for i in [1..#poset_result`minimal_injective_ideals] do
            Append(
                ~complementary_triples,
                complementary_triple_record(
                    order_data,
                    localized_group,
                    poset_result`minimal_injective_ideals[i],
                    poset_result`minimal_results[i]
                )
            );
        end for;
    end for;

    return rec<single_order_complementary_scan_format |
        algebra_identifier := complementary_algebra_identifier(order_data),
        order_identifier := complementary_order_identifier(order_data),
        order_data := order_data,
        norm_bound := norm_bound,
        admissible_ramified_primes := admissible_primes,
        elapsed_seconds := Cputime(timer),
        unit_quotient_order := unit_quotient_order,
            trivial_unit_quotient := unit_quotient_order eq 1,
        triple_data := complementary_triple_data_record(
            localized_unit_groups,
            minimal_ideal_results,
            complementary_triples
        ),
        skipped_estimated_tasks := skipped_estimated_tasks,
        exponent_bound_warnings := exponent_bound_warnings
    >;
end function;


function scan_orders_for_complementary_triples(
    order_list,
    norm_bound :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    expected_exponent_bound := 2,
    allow_higher_exponents := true,
    consistency_check := false
)
    Print := validate_print_level(Print);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );

    if Type(order_list) ne SeqEnum then
        error "order_list must be a sequence of order_data records.";
    end if;

    timer := Cputime();
    algebra_rows := [];
    skipped_estimated_tasks := [];
    skipped_estimated_task_keys := AssociativeArray();
    exponent_bound_warnings := [];

    if print_is_concise(Print) then
        print "";
        print "============================================================";
        print "[CI all] Multi-order complementary-triple scan";
        print "============================================================";
        print "[CI all] orders=", #order_list,
              "| norm_bound=", norm_bound;
    end if;

    for order_data in order_list do
        algebra_row := scan_order_for_complementary_triples(
            order_data,
            norm_bound :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds,
            expected_exponent_bound := expected_exponent_bound,
            allow_higher_exponents := allow_higher_exponents,
            consistency_check := consistency_check
        );
        Append(~algebra_rows, algebra_row);

        for skipped_task in algebra_row`skipped_estimated_tasks do
            skipped_task_key := complementary_multi_order_skipped_task_key(order_data, skipped_task);
            if not IsDefined(skipped_estimated_task_keys, skipped_task_key) then
                skipped_estimated_task_keys[skipped_task_key] := true;
                Append(
                    ~skipped_estimated_tasks,
                    complementary_multi_order_skipped_task_record(order_data, skipped_task)
                );
            end if;
        end for;

        for warning_string in algebra_row`exponent_bound_warnings do
            if Index(exponent_bound_warnings, warning_string) eq 0 then
                Append(~exponent_bound_warnings, warning_string);
            end if;
        end for;
    end for;

    return rec<multi_order_complementary_scan_format |
        algebra_rows := algebra_rows,
        elapsed_seconds := Cputime(timer),
        skipped_estimated_tasks := skipped_estimated_tasks,
        exponent_bound_warnings := exponent_bound_warnings
    >;
end function;
