// ============================================================================
// Presentation builder for complementary triples and their T-unit groups.
//
// The central workflow is:
// 1. start from a complementary result / complementary triple,
// 2. make the localized T-unit group U_T explicit,
// 3. choose lifts by translating principal right-ideal generators by elements
//    of U_T until the reduction lands in the selected complement subgroup, and
// 4. build the presentation from the resulting A[P] representatives.
//
// Main API:
// - build_presentation_for_complementary_result(complementary_result, s_prime_inputs : ...)
// - build_presentation_for_complementary_result_from_integral_primes(complementary_result, s_prime_specs : ...)
// - build_presentation_for_complementary_triple(complementary_triple, s_prime_inputs : ...)
// - build_presentation_for_complementary_triple_from_integral_primes(complementary_triple, s_prime_specs : ...)
// - build_presentations_for_complementary_result(complementary_result, s_prime_inputs : ...)
// - build_presentations_for_complementary_triple(complementary_triple, s_prime_inputs : ...)
// - print_presentation_summary(presentation, show_relations, show_generator_representatives)
// - print_presentation_suite(presentation_suite, show_relations, show_generator_representatives)
// ============================================================================


presentation_result_format := recformat<
    order_data,
    complementary_result,
    localized_unit_group,
    group_model,
    candidate_ideal,
    candidate_norm,
    complement_family,
    source_group_label,
    normal_only,
    complement_index,
    complement_class,
    complement_subgroup,
    s_prime_inputs,
    s_prime_ideals,
    t_unit_generator_data,
    presentation_generator_data,
    normalization_conventions,
    a_representatives,
    representative_index_maps,
    sigma_map,
    inverse_map,
    sigma_index_map,
    gamma_group,
    index_map,
    element_map,
    minimal_square_relations,
    pretty_payload,
    generators_torsion_free,
    square_torsion
>;


presentation_suite_format := recformat<
    order_data,
    complementary_triple,
    complementary_result,
    localized_unit_group,
    s_prime_inputs,
    s_prime_ideals,
    normal_only,
    presentations
>;


presentation_t_unit_generator_format := recformat<
    label,
    source_kind,
    source_prime,
    quaternion_representative,
    principal_basis_coordinates
>;


presentation_generator_record_format := recformat<
    s_index,
    generator_index,
    label,
    prime_ideal,
    quaternion_representative,
    principal_basis_coordinates
>;


function presentation_print_is_concise(print_results)
    return print_results ge 1;
end function;


function presentation_print_is_detailed(print_results)
    return print_results ge 2;
end function;


function presentation_join_strings(strings, delimiter)
    if #strings eq 0 then
        return "";
    end if;

    output := strings[1];
    for i in [2..#strings] do
        output cat:= delimiter cat strings[i];
    end for;

    return output;
end function;


function presentation_coordinate_list_string(coordinates)
    return "[" cat presentation_join_strings([Sprint(coordinate) : coordinate in coordinates], ", ") cat "]";
end function;


function presentation_principal_basis_coordinates(order_data, element_x)
    return order_coordinates_in_basis(
        order_data`base_field,
        order_data`quaternion_algebra,
        order_data`principal_basis,
        element_x
    );
end function;


function presentation_known_generator_norm_string(label, has_generator, generator, norm_value)
    generator_key := Sprintf("%o_gen", label);
    norm_key := Sprintf("%o_norm", label);

    if has_generator then
        return Sprintf("%o=%o | %o=%o", generator_key, generator, norm_key, norm_value);
    end if;

    return Sprintf("%o=unavailable | %o=%o", generator_key, norm_key, norm_value);
end function;


function presentation_ideal_generator_norm_string(label, ideal_x)
    has_generator, generator := IsPrincipal(ideal_x);
    return presentation_known_generator_norm_string(label, has_generator, has_generator select generator else 0, Norm(ideal_x));
end function;


function presentation_key_summary(label, object_x)
    if Type(object_x) eq RngOrdIdl then
        return presentation_ideal_generator_norm_string(label, object_x);
    end if;

    return Sprintf("%o: %o", label, object_x);
end function;


function presentation_prime_divides_ideal(prime_ideal, modulus_ideal)
    return Valuation(modulus_ideal, prime_ideal) gt 0;
end function;


function presentation_localized_unit_group_label(localized_unit_group)
    return Sprintf(
        "U_T for T=%o",
        complementary_ramified_subset_string(localized_unit_group`ramified_subset)
    );
end function;


function normalize_complement_selector(complement_selector)
    if Type(complement_selector) ne RngIntElt or complement_selector lt 1 then
        error "complement_selector must be an integer >= 1.";
    end if;

    return complement_selector;
end function;


function validate_bool_parameter(flag_value, flag_name)
    if Type(flag_value) ne BoolElt then
        error flag_name cat " must be true or false.";
    end if;

    return flag_value;
end function;


function presentation_complement_subgroup_key(subgroup_h)
    element_strings := [Sprint(group_element) : group_element in subgroup_h];
    Sort(~element_strings);
    return presentation_join_strings(element_strings, " | ");
end function;


function presentation_sorted_complement_list(complement_list)
    keyed_lookup := AssociativeArray();
    keyed_strings := [];

    // Sort complement representatives by a subgroup-level key so selector-based
    // APIs are stable across direct results, triple scans, and cached rebuilds.
    for i in [1..#complement_list] do
        key := Sprintf(
            "%o || %o",
            presentation_complement_subgroup_key(complement_list[i]`subgroup),
            i
        );
        keyed_lookup[key] := complement_list[i];
        Append(~keyed_strings, key);
    end for;

    Sort(~keyed_strings);
    return [keyed_lookup[key] : key in keyed_strings];
end function;


function normalize_s_prime_input_to_ideal(integer_ring, prime_data)
    return normalize_prime_ideal(integer_ring, prime_data);
end function;


function normalized_s_prime_inputs(order_data, candidate_ideal, s_prime_inputs)
    integer_ring := order_data`integer_ring;
    algebra_discriminant := Discriminant(order_data`quaternion_algebra);
    s_prime_ideals := [];
    seen_ideals := [];

    if Type(s_prime_inputs) ne SeqEnum then
        error "s_prime_inputs must be a sequence of ideal-like inputs.";
    end if;

    for prime_data in s_prime_inputs do
        prime_ideal := normalize_s_prime_input_to_ideal(integer_ring, prime_data);

        if presentation_prime_divides_ideal(prime_ideal, candidate_ideal) then
            error "S contains a prime factor of the complementary modulus C.";
        end if;

        if Valuation(algebra_discriminant, prime_ideal) ne 0 then
            error "S contains a prime where the quaternion algebra ramifies.";
        end if;

        if prime_ideal in seen_ideals then
            error "S contains duplicate prime ideals.";
        end if;

        Append(~s_prime_ideals, prime_ideal);
        Append(~seen_ideals, prime_ideal);
    end for;

    return s_prime_ideals;
end function;


// Build admissible S-ideal list from tuple specs <p, k, n>.
function admissible_prime_ideals_from_specs(order_data, candidate_ideal, s_prime_specs)
    integer_ring := order_data`integer_ring;
    algebra_discriminant := Discriminant(order_data`quaternion_algebra);
    s_prime_ideals := [];
    used_ideals := [];

    if Type(s_prime_specs) ne SeqEnum then
        error "s_prime_specs must be a sequence of tuples <p, k, n>.";
    end if;

    for tuple_data in s_prime_specs do
        if Type(tuple_data) ne Tup or #tuple_data ne 3 then
            error "Each entry of s_prime_specs must be a tuple <p, k, n>.";
        end if;

        p := tuple_data[1];
        k := tuple_data[2];
        n := tuple_data[3];

        if Type(p) ne RngIntElt or p le 1 then
            error "Each tuple <p, k, n> must have an integer p > 1.";
        end if;

        if Type(k) ne RngIntElt or k lt 1 then
            error "Exponent k in <p, k, n> must be a positive integer.";
        end if;

        if Type(n) ne RngIntElt or n lt 0 then
            error "Multiplicity n in <p, k, n> must be a nonnegative integer.";
        end if;

        if n eq 0 then
            continue;
        end if;

        target_norm := p^k;
        admissible := [];

        for fac in Factorization(ideal<integer_ring | p>) do
            prime_ideal := fac[1];

            if presentation_prime_divides_ideal(prime_ideal, candidate_ideal) then
                continue;
            end if;

            if Valuation(algebra_discriminant, prime_ideal) ne 0 then
                continue;
            end if;

            if Norm(prime_ideal) ne target_norm then
                continue;
            end if;

            if prime_ideal in used_ideals then
                continue;
            end if;

            Append(~admissible, prime_ideal);
        end for;

        if #admissible lt n then
            error Sprintf(
                "Requested %o admissible primes P over p = %o with Norm(P) = %o, but only %o available.",
                n,
                p,
                target_norm,
                #admissible
            );
        end if;

        for j in [1..n] do
            Append(~s_prime_ideals, admissible[j]);
            Append(~used_ideals, admissible[j]);
        end for;
    end for;

    return s_prime_ideals;
end function;


function presentation_class_index_by_key(group_model)
    if assigned group_model`class_index_by_key then
        return group_model`class_index_by_key;
    end if;

    class_index_by_key := AssociativeArray();

    for i in [1..#group_model`class_representatives] do
        class_index_by_key[Sprint(group_model`class_representatives[i])] := i;
    end for;

    return class_index_by_key;
end function;


procedure normalizer_ambient_permutation_for_order_element(
    group_model,
    order_element,
    reduced_unit_lookup_data,
    class_index_by_key,
    class_key_data,
    ~image_permutation,
    ~reduced_to_permutation,
    ~permutation_to_reduced
)
    normalizer_image_permutation(
        group_model`order_data,
        order_element,
        group_model`reduced_algebra,
        group_model`reduction_map,
        group_model`class_representatives,
        class_index_by_key,
        group_model`scalars,
        class_key_data,
        reduced_unit_lookup_data,
        group_model`ramified_extension_defined,
        group_model`ramified_generator,
        group_model`ramified_generator_permutation,
        #group_model`class_representatives,
        ~image_permutation,
        ~reduced_to_permutation,
        ~permutation_to_reduced
    );
end procedure;


function presentation_localized_unit_multiplier_pool(localized_unit_group)
    context := complementary_build_context(localized_unit_group`order_data);
    representative_lookup := AssociativeArray();
    representative_keys := [];

    // The lift search uses actual quaternion representatives of every element
    // of U_T, not only the stored generator list.
    for group_element in localized_unit_group`subgroup do
        representative := complementary_normalizer_representative(context, group_element);
        key := complementary_normalized_order_element_key(localized_unit_group`order_data, representative);

        if not IsDefined(representative_lookup, key) then
            representative_lookup[key] := representative;
            Append(~representative_keys, key);
        end if;
    end for;

    Sort(~representative_keys);
    return [representative_lookup[key] : key in representative_keys];
end function;


function presentation_t_unit_generator_data(localized_unit_group)
    order_data := localized_unit_group`order_data;
    unit_generator_count := Ngens(order_data`unit_group);
    generator_data := [];

    for i in [1..#localized_unit_group`generator_elements] do
        source_kind := i le unit_generator_count select "unit" else "ramified prime";
        source_prime := i le unit_generator_count select false else
            localized_unit_group`generator_primes[i - unit_generator_count];
        label := i le unit_generator_count select Sprintf("u%o", i) else
            Sprintf("alpha%o", i - unit_generator_count);

        Append(~generator_data, rec<presentation_t_unit_generator_format |
            label := label,
            source_kind := source_kind,
            source_prime := source_prime,
            quaternion_representative := localized_unit_group`generator_elements[i],
            principal_basis_coordinates := presentation_principal_basis_coordinates(
                order_data,
                localized_unit_group`generator_elements[i]
            )
        >);
    end for;

    return generator_data;
end function;


function presentation_factor_ambient_image(reduction_factor, order_element)
    group_model := reduction_factor`group_model;

    if reduction_factor`uses_ramified_extension then
        class_index_by_key := presentation_class_index_by_key(group_model);
        reduced_unit_lookup_data := assigned group_model`reduced_unit_membership select
            group_model`reduced_unit_membership else
            reduced_unit_lookup(group_model`reduced_units);
        class_key_data := assigned group_model`class_key_data select
            group_model`class_key_data else false;
        reduced_to_permutation := group_model`reduced_to_permutation;
        permutation_to_reduced := group_model`permutation_to_reduced;
        image_permutation := false;

        normalizer_ambient_permutation_for_order_element(
            group_model,
            order_element,
            reduced_unit_lookup_data,
            class_index_by_key,
            class_key_data,
            ~image_permutation,
            ~reduced_to_permutation,
            ~permutation_to_reduced
        );

        return image_permutation;
    end if;

    image_permutation := false;
    complementary_projective_image_permutation(
        group_model,
        order_element,
        "presentation T-unit element",
        ~image_permutation
    );

    // The complementary-triple image convention is homomorphic, so invert the
    // left-action permutation returned by cached_projective_permutation.
    return image_permutation^-1;
end function;


function presentation_ambient_image_in_complementary_result(complementary_result, order_element)
    reduction_factors := complementary_result`reduction_factors;

    if #reduction_factors eq 1 then
        return presentation_factor_ambient_image(reduction_factors[1], order_element);
    end if;

    total_degree := &+[Degree(reduction_factor`ambient_group) : reduction_factor in reduction_factors];
    symmetric_group := Sym(total_degree);
    offsets := [];
    running_offset := 0;

    for reduction_factor in reduction_factors do
        Append(~offsets, running_offset);
        running_offset +:= Degree(reduction_factor`ambient_group);
    end for;

    global_image := Identity(symmetric_group);

    for factor_index in [1..#reduction_factors] do
        factor_image := presentation_factor_ambient_image(
            reduction_factors[factor_index],
            order_element
        );
        global_image *:= complementary_embedded_block_permutation(
            factor_image,
            offsets[factor_index],
            total_degree
        );
    end for;

    return global_image;
end function;


// Build A[P] representatives constrained by a fixed complement subgroup.
function build_representatives_for_selected_complement(
    complementary_result,
    complement_label,
    complement_subgroup,
    s_prime_ideals :
    multiplier_pool := false
)
    localized_unit_group := complementary_result`localized_unit_group;
    order_data := localized_unit_group`order_data;
    quaternion_algebra := order_data`quaternion_algebra;
    quaternion_order := order_data`quaternion_order;

    if multiplier_pool cmpeq false then
        multiplier_pool := presentation_localized_unit_multiplier_pool(localized_unit_group);
    end if;

    a_representatives := AssociativeArray();

    for prime_ideal in s_prime_ideals do
        a_representatives[prime_ideal] := [];
        right_ideals := MaximalRightIdeals(quaternion_order, prime_ideal);

        for right_ideal in right_ideals do
            is_principal, generator := IsPrincipal(right_ideal);

            if not is_principal then
                error "A maximal right ideal in the presentation pipeline was not principal.";
            end if;

            generator := primitive_integral_order_representative(order_data, generator);
            found_representative := false;

            // Right-multiply by U_T until the ambient reduction lands in the
            // chosen complement subgroup. The first hit is the lift convention.
            for multiplier in multiplier_pool do
                lifted := quaternion_order!(quaternion_algebra!generator * quaternion_algebra!multiplier);
                lifted_image := presentation_ambient_image_in_complementary_result(
                    complementary_result,
                    lifted
                );

                if lifted_image in complement_subgroup then
                    Append(~a_representatives[prime_ideal], lifted);
                    found_representative := true;
                    break;
                end if;
            end for;

            if not found_representative then
                error Sprintf(
                    "Failed to recover a representative in the selected %o complement for %o using T-unit translates.",
                    complement_label,
                    prime_ideal
                );
            end if;
        end for;

        if #a_representatives[prime_ideal] ne Abs(Norm(prime_ideal)) + 1 then
            error "Did not recover exactly Norm(P)+1 representatives for the chosen S-prime.";
        end if;
    end for;

    return a_representatives;
end function;


function select_presentation_complement_from_complementary_result(
    complementary_result,
    normal_only,
    complement_selector
)
    complement_list := presentation_sorted_complement_list(normal_only select
        complementary_result`normal_complement_classes
    else
        complementary_result`complement_classes);

    if #complement_list eq 0 then
        error Sprintf(
            "No stored %o complements were found at modulus %o.",
            normal_only select "normal " else "",
            complementary_result`modulus_ideal
        );
    end if;

    if complement_selector gt #complement_list then
        error "complement_selector index out of range.";
    end if;

    return complement_selector,
           complement_list[complement_selector],
           complement_list[complement_selector]`subgroup;
end function;


// Compute sigma and inverse maps from representatives A[P].
function compute_sigma_data(order_data, a_representatives)
    integer_ring := order_data`integer_ring;
    quaternion_algebra := order_data`quaternion_algebra;
    quaternion_order := order_data`quaternion_order;

    sigma_map := AssociativeArray();
    inverse_map := AssociativeArray();

    primes := SetToSequence(Keys(a_representatives));

    for prime_p in primes do
        for prime_q in primes do
            if prime_p eq prime_q then
                continue;
            end if;
            sigma_map[<prime_p, prime_q>] := AssociativeArray();
        end for;
    end for;

    generators_torsion_free := true;

    for prime_p in primes do
        inverse_map[prime_p] := AssociativeArray();

        for x in a_representatives[prime_p] do
            found_inverse := false;

            for y in a_representatives[prime_p] do
                is_scalar, scalar_value := IsScalar(x * y);

                if is_scalar and scalar_value in prime_p then
                    inverse_map[prime_p][x] := y;
                    if y eq x then
                        generators_torsion_free := false;
                    end if;
                    found_inverse := true;
                    break;
                end if;
            end for;

            if not found_inverse then
                error "Failed to find an inverse partner inside A[P] for a selected representative.";
            end if;
        end for;
    end for;

    square_torsion := {};

    for prime_pair in Keys(sigma_map) do
        prime_p := prime_pair[1];
        prime_q := prime_pair[2];

        a_p := a_representatives[prime_p];
        a_q := a_representatives[prime_q];
        prime_q_order_generators := [quaternion_order!(quaternion_algebra!(integer_ring!b)) : b in Basis(prime_q)];

        for x in a_p do
            for y in a_q do
                target_ideal := rideal<quaternion_order | [x * y] cat prime_q_order_generators>;
                found_relation := false;

                for y_prime in a_q do
                    if not (y_prime in target_ideal) then
                        continue;
                    end if;

                    try
                        a_prime := primitive_integral_order_representative(
                            order_data,
                            (quaternion_algebra!y_prime)^(-1) * quaternion_algebra!x * quaternion_algebra!y
                        );
                        a_prime_ideal := rideal<quaternion_order | a_prime>;
                    catch e
                        error "Failed while constructing candidate a' in sigma computation:", e;
                    end try;

                    found_a_prime := false;

                    for candidate in a_p do
                        if a_prime_ideal eq rideal<quaternion_order | candidate> then
                            correction := quaternion_algebra!x
                                          * quaternion_algebra!y
                                          * quaternion_algebra!candidate^-1
                                          * quaternion_algebra!y_prime^-1;

                            if not (correction in Center(quaternion_algebra)) then
                                error "Sigma candidate failed center check.";
                            end if;

                            sigma_map[prime_pair][<x, y>] := <y_prime, candidate>;
                            found_a_prime := true;

                            if x eq inverse_map[prime_p][candidate] and y eq inverse_map[prime_q][y_prime] then
                                Include(~square_torsion, {x, y});
                            end if;

                            break;
                        end if;
                    end for;

                    if not found_a_prime then
                        print presentation_key_summary("prime pair first key", prime_pair[1]);
                        print presentation_key_summary("prime pair second key", prime_pair[2]);
                        print "a =", x;
                        print "b =", y;
                        print "b' =", y_prime;
                        error "Could not identify a' representative in A[P].";
                    end if;

                    found_relation := true;
                    break;
                end for;

                if not found_relation then
                    print presentation_key_summary("prime pair first key", prime_pair[1]);
                    print presentation_key_summary("prime pair second key", prime_pair[2]);
                    print "a =", x;
                    print "b =", y;
                    error "No b' found with expected ideal membership.";
                end if;
            end for;
        end for;
    end for;

    consistent := check_sigma_consistency(a_representatives, sigma_map, inverse_map);
    return sigma_map, inverse_map, consistent, generators_torsion_free, square_torsion;
end function;


// Build Gamma presentation from inverse and square relations.
//
// Prime labels in pretty output are indexed by the order of s_prime_ideals:
// generator names have the form a(k)_i where k is the S-index.
function compute_gamma_presentation(a_representatives, s_prime_ideals, sigma_map, inverse_map : minimal_relations := true)
    primes := s_prime_ideals;
    seen_primes := [];

    for prime_key in s_prime_ideals do
        if not IsDefined(a_representatives, prime_key) then
            error "s_prime_ideals does not match the A[P] representative keys.";
        end if;

        if prime_key in seen_primes then
            error "Duplicate prime key in s_prime_ideals.";
        end if;

        Append(~seen_primes, prime_key);
    end for;

    if #primes ne #Keys(a_representatives) then
        error "Mismatch between s_prime_ideals and A[P] keys.";
    end if;

    prime_labels := AssociativeArray();
    for idx in [1..#primes] do
        prime_labels[primes[idx]] := idx;
    end for;

    num_generators := &+[#a_representatives[p] : p in primes];

    free_group := FreeGroup(num_generators);
    index_map := AssociativeArray();

    pretty_names := AssociativeArray();
    pretty_inverse_relations := AssociativeArray();
    pretty_square_relations := AssociativeArray();

    minimal_square_relations := AssociativeArray();
    relations := [];

    inverse_seen := [];
    prime_pairs := Subsets(Set(primes), 2);

    next_index := 1;
    for prime_p in primes do
        for a in a_representatives[prime_p] do
            index_map[a] := next_index;
            next_index +:= 1;
        end for;
    end for;

    for prime_p in primes do
        for i in [1..#a_representatives[prime_p]] do
            pretty_names[a_representatives[prime_p][i]] := Sprintf("a(%o)_%o", prime_labels[prime_p], i);
        end for;
    end for;

    for prime_p in primes do
        pretty_inverse_relations[prime_labels[prime_p]] := [];

        for a in a_representatives[prime_p] do
            if a in inverse_seen then
                continue;
            end if;

            Append(~inverse_seen, a);
            Append(~inverse_seen, inverse_map[prime_p][a]);

            Append(~relations, free_group.index_map[a] * free_group.index_map[inverse_map[prime_p][a]]);

            if inverse_map[prime_p][a] eq a then
                Append(~pretty_inverse_relations[prime_labels[prime_p]], Sprintf("%o^2 = 1", pretty_names[a]));
            else
                Append(~pretty_inverse_relations[prime_labels[prime_p]],
                    Sprintf("%o * %o = 1", pretty_names[a], pretty_names[inverse_map[prime_p][a]]));
            end if;
        end for;
    end for;

    for prime_pair in prime_pairs do
        pair_seq := SetToSequence(prime_pair);
        prime_p := pair_seq[1];
        prime_q := pair_seq[2];
        pair_label := <Minimum([prime_labels[prime_p], prime_labels[prime_q]]), Maximum([prime_labels[prime_p], prime_labels[prime_q]])>;

        if minimal_relations then
            pretty_square_relations[pair_label] := [];
            minimal_square_relations[prime_pair] :=
                minimal_sigma_relations(a_representatives, sigma_map, inverse_map, prime_pair);

            for relation_word in Keys(minimal_square_relations[prime_pair]) do
                a := relation_word[1][2];
                b := relation_word[2][2];
                a_prime_inv := relation_word[3][2];
                b_prime_inv := relation_word[4][2];

                relation := free_group.index_map[a]
                            * free_group.index_map[b]
                            * free_group.index_map[a_prime_inv]
                            * free_group.index_map[b_prime_inv];
                Append(~relations, relation);

                Append(~pretty_square_relations[pair_label],
                    Sprintf("%o * %o * %o * %o",
                        pretty_names[a],
                        pretty_names[b],
                        pretty_names[a_prime_inv],
                        pretty_names[b_prime_inv]
                    )
                );
            end for;
        else
            minimal_square_relations := false;

            for ab in Keys(sigma_map[<prime_p, prime_q>]) do
                a := ab[1];
                b := ab[2];
                a_prime_inv := inverse_map[prime_p][sigma_map[<prime_p, prime_q>][ab][2]];
                b_prime_inv := inverse_map[prime_q][sigma_map[<prime_p, prime_q>][ab][1]];

                relation := free_group.index_map[a]
                            * free_group.index_map[b]
                            * free_group.index_map[a_prime_inv]
                            * free_group.index_map[b_prime_inv];
                Append(~relations, relation);
            end for;
        end if;
    end for;

    gamma_group := quo<free_group | relations>;

    if minimal_relations then
        pretty_payload := <pretty_names, pretty_inverse_relations, pretty_square_relations>;
    else
        pretty_payload := false;
    end if;

    if (#prime_pairs eq 1) and minimal_relations then
        only_pair := SetToSequence(prime_pairs)[1];
        return index_map, gamma_group, minimal_square_relations[only_pair], pretty_payload;
    end if;

    return index_map, gamma_group, minimal_square_relations, pretty_payload;
end function;


procedure pretty_print_relations(pretty_payload)
    pretty_inverse_relations := pretty_payload[2];
    pretty_square_relations := pretty_payload[3];

    for prime_p in Keys(pretty_inverse_relations) do
        print "Inverse relations for S-index:", prime_p;
        for relation in pretty_inverse_relations[prime_p] do
            print relation;
        end for;
        print "";
    end for;

    for prime_pair in Keys(pretty_square_relations) do
        print "Square relations for S-index pair:", prime_pair;
        for relation in pretty_square_relations[prime_pair] do
            print relation;
        end for;
        print "";
    end for;
end procedure;


function build_gamma_element_map(gamma_group, index_map)
    function element_map(word_or_list)
        if Type(word_or_list) eq SeqEnum then
            if #word_or_list eq 0 then
                return Identity(gamma_group);
            end if;
            return &*[gamma_group.index_map[a] : a in word_or_list];
        end if;

        return gamma_group.index_map[word_or_list];
    end function;

    return element_map;
end function;


function build_sigma_index_lookup(a_representatives, sigma_map)
    sigma_index_map := AssociativeArray();

    for prime_pair in Keys(sigma_map) do
        prime_p := prime_pair[1];
        prime_q := prime_pair[2];

        sigma_index_map[prime_pair] := AssociativeArray();

        for ab in Keys(sigma_map[prime_pair]) do
            i := Index(a_representatives[prime_p], ab[1]);
            j := Index(a_representatives[prime_q], ab[2]);
            k := Index(a_representatives[prime_q], sigma_map[prime_pair][ab][1]);
            l := Index(a_representatives[prime_p], sigma_map[prime_pair][ab][2]);
            sigma_index_map[prime_pair][<i, j>] := <k, l>;
        end for;
    end for;

    return sigma_index_map;
end function;


function build_representative_index_maps(a_representatives)
    representative_index_maps := AssociativeArray();

    for prime_key in Keys(a_representatives) do
        representative_index_maps[prime_key] := AssociativeArray();

        for i in [1..#a_representatives[prime_key]] do
            representative_index_maps[prime_key][a_representatives[prime_key][i]] := i;
        end for;
    end for;

    return representative_index_maps;
end function;


function presentation_generator_data_from_representatives(order_data, s_prime_ideals, a_representatives)
    generator_data := [];

    for s_index in [1..#s_prime_ideals] do
        prime_ideal := s_prime_ideals[s_index];

        for generator_index in [1..#a_representatives[prime_ideal]] do
            representative := a_representatives[prime_ideal][generator_index];
            Append(~generator_data, rec<presentation_generator_record_format |
                s_index := s_index,
                generator_index := generator_index,
                label := Sprintf("a(%o)_%o", s_index, generator_index),
                prime_ideal := prime_ideal,
                quaternion_representative := representative,
                principal_basis_coordinates := presentation_principal_basis_coordinates(
                    order_data,
                    representative
                )
            >);
        end for;
    end for;

    return generator_data;
end function;


function presentation_normalization_conventions(complementary_result)
    conventions := [
        "Quaternion coordinates are displayed in the stored principal basis of the order.",
        "Each T-unit generator is the stored primitive integral quaternion representative coming from the localized U_T construction.",
        "Each maximal right ideal is principalized and its generator is normalized with primitive_integral_order_representative(...).",
        "For each S-prime and each maximal right ideal, the chosen lift is the first T-unit translate whose reduction lies in the selected complement subgroup.",
        "T-unit multipliers are ordered lexicographically by complementary_normalized_order_element_key(...), so the lift convention is deterministic.",
        "Complement subgroups are ordered by the sorted Sprint(...) list of their ambient group elements before complement_selector is applied."
    ];

    if #complementary_result`reduction_factors gt 1 then
        Append(
            ~conventions,
            "For composite complementary moduli, ambient reduction images are assembled blockwise from the prime-power local factors."
        );
    end if;

    return conventions;
end function;


procedure presentation_print_conventions(normalization_conventions)
    print "Normalization conventions:";
    for convention in normalization_conventions do
        print "  -", convention;
    end for;
end procedure;


procedure presentation_print_t_unit_generators(t_unit_generator_data)
    print "T-unit generators:";

    if #t_unit_generator_data eq 0 then
        print "  none";
        return;
    end if;

    for generator_data in t_unit_generator_data do
        if generator_data`source_prime cmpeq false then
            print Sprintf(
                "  %o (%o): coordinates=%o | quaternion=%o",
                generator_data`label,
                generator_data`source_kind,
                presentation_coordinate_list_string(generator_data`principal_basis_coordinates),
                generator_data`quaternion_representative
            );
        else
            print Sprintf(
                "  %o (%o at %o): coordinates=%o | quaternion=%o",
                generator_data`label,
                generator_data`source_kind,
                ideal_summary("P", generator_data`source_prime),
                presentation_coordinate_list_string(generator_data`principal_basis_coordinates),
                generator_data`quaternion_representative
            );
        end if;
    end for;
end procedure;


procedure presentation_print_generator_representatives(presentation_generator_data)
    print "Presentation generators:";

    if #presentation_generator_data eq 0 then
        print "  none";
        return;
    end if;

    for generator_data in presentation_generator_data do
        print Sprintf(
            "  %o | S-index=%o | %o | coordinates=%o | quaternion=%o",
            generator_data`label,
            generator_data`s_index,
            ideal_summary("P", generator_data`prime_ideal),
            presentation_coordinate_list_string(generator_data`principal_basis_coordinates),
            generator_data`quaternion_representative
        );
    end for;
end procedure;


procedure validate_presentation_complementary_result(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        error Sprintf(
            "Cannot build a presentation from modulus %o because it was skipped.",
            complementary_result`modulus_ideal
        );
    end if;

    if not complementary_result`complements_computed then
        error "Presentation construction requires complement data on the complementary result.";
    end if;

    if not complementary_result`injective then
        error Sprintf(
            "Presentation construction requires an injective localized image at modulus %o.",
            complementary_result`modulus_ideal
        );
    end if;
end procedure;


function build_presentation_from_selected_complement(
    complementary_result,
    s_prime_inputs,
    complement_family,
    complement_index,
    complement_class,
    complement_subgroup :
    normal_only := false,
    minimal_relations := true,
    print_results := 1,
    multiplier_pool := false
)
    order_data := complementary_result`localized_unit_group`order_data;
    source_group_label := presentation_localized_unit_group_label(
        complementary_result`localized_unit_group
    );
    s_prime_ideals := normalized_s_prime_inputs(
        order_data,
        complementary_result`modulus_ideal,
        s_prime_inputs
    );
    group_model := (#complementary_result`reduction_factors eq 1) select
        complementary_result`reduction_factors[1]`group_model
    else
        false;

    if presentation_print_is_concise(print_results) then
        print "";
        print "============================================================";
        print "[PIPE presentation] Build presentation from complementary triple";
        print "============================================================";
        print "[PIPE presentation] index:", order_data`index;
        print "[PIPE presentation] source:", source_group_label;
        print "[PIPE presentation] normal only:", normal_only;
        print "[PIPE presentation]",
              presentation_ideal_generator_norm_string("C", complementary_result`modulus_ideal);
        print "[PIPE presentation] selected complement index:", complement_index;
        print "[PIPE presentation] T:",
              complementary_ramified_subset_string(
                  complementary_result`localized_unit_group`ramified_subset
              );
        print "[PIPE presentation] |U_T|:",
              complementary_result`localized_unit_group`subgroup_order;
    end if;

    a_representatives := build_representatives_for_selected_complement(
        complementary_result,
        complement_family,
        complement_subgroup,
        s_prime_ideals :
        multiplier_pool := multiplier_pool
    );

    sigma_map,
    inverse_map,
    consistent,
    generators_torsion_free,
    square_torsion := compute_sigma_data(order_data, a_representatives);

    if not consistent then
        error "Sigma consistency check failed.";
    end if;

    index_map,
    gamma_group,
    minimal_square_relations,
    pretty_payload := compute_gamma_presentation(
        a_representatives,
        s_prime_ideals,
        sigma_map,
        inverse_map :
        minimal_relations := minimal_relations
    );

    if presentation_print_is_concise(print_results) then
        gamma_ab := AbelianQuotientInvariants(gamma_group);

        print "";
        print "[PIPE presentation] Summary";
        print "[PIPE presentation] S:";
        for i in [1..#s_prime_ideals] do
            print "[PIPE presentation]",
                  presentation_ideal_generator_norm_string(Sprintf("S[%o]", i), s_prime_ideals[i]);
        end for;
        print "[PIPE presentation] Gamma^ab:", gamma_ab;
        print "[PIPE presentation] generator torsion present:", not generators_torsion_free;
        print "[PIPE presentation] square torsion present:", #square_torsion gt 0;
        print "[PIPE presentation] square torsion count:", #square_torsion;
    end if;

    representative_index_maps := build_representative_index_maps(a_representatives);
    sigma_index_map := build_sigma_index_lookup(a_representatives, sigma_map);
    element_map := build_gamma_element_map(gamma_group, index_map);
    t_unit_generator_data := presentation_t_unit_generator_data(
        complementary_result`localized_unit_group
    );
    presentation_generator_data := presentation_generator_data_from_representatives(
        order_data,
        s_prime_ideals,
        a_representatives
    );
    normalization_conventions := presentation_normalization_conventions(
        complementary_result
    );

    presentation := rec<presentation_result_format |
        order_data := order_data,
        complementary_result := complementary_result,
        localized_unit_group := complementary_result`localized_unit_group,
        group_model := group_model,
        candidate_ideal := complementary_result`modulus_ideal,
        candidate_norm := Norm(complementary_result`modulus_ideal),
        complement_family := complement_family,
        source_group_label := source_group_label,
        normal_only := normal_only,
        complement_index := complement_index,
        complement_class := complement_class,
        complement_subgroup := complement_subgroup,
        s_prime_inputs := s_prime_inputs,
        s_prime_ideals := s_prime_ideals,
        t_unit_generator_data := t_unit_generator_data,
        presentation_generator_data := presentation_generator_data,
        normalization_conventions := normalization_conventions,
        a_representatives := a_representatives,
        representative_index_maps := representative_index_maps,
        sigma_map := sigma_map,
        inverse_map := inverse_map,
        sigma_index_map := sigma_index_map,
        gamma_group := gamma_group,
        index_map := index_map,
        element_map := element_map,
        minimal_square_relations := minimal_square_relations,
        pretty_payload := pretty_payload,
        generators_torsion_free := generators_torsion_free,
        square_torsion := square_torsion
    >;

    if presentation_print_is_detailed(print_results) then
        print "";
        presentation_print_conventions(presentation`normalization_conventions);
        print "";
        presentation_print_t_unit_generators(presentation`t_unit_generator_data);
        print "";
        presentation_print_generator_representatives(presentation`presentation_generator_data);

        if minimal_relations then
            print "";
            print "Relators:";
            pretty_print_relations(pretty_payload);
        end if;
    end if;

    return presentation;
end function;


function build_presentation_for_complementary_result(
    complementary_result,
    s_prime_inputs :
    normal_only := false,
    complement_selector := 1,
    minimal_relations := true,
    print_results := 1
)
    print_results := validate_print_level(print_results);
    normal_only := validate_bool_parameter(normal_only, "normal_only");
    minimal_relations := validate_bool_parameter(minimal_relations, "minimal_relations");
    complement_selector := normalize_complement_selector(complement_selector);

    validate_presentation_complementary_result(complementary_result);

    complement_index,
    complement_class,
    complement_subgroup := select_presentation_complement_from_complementary_result(
        complementary_result,
        normal_only,
        complement_selector
    );
    complement_label := (#complementary_result`localized_unit_group`ramified_subset eq 0) select
        "unit"
    else
        "localized_unit_group";

    return build_presentation_from_selected_complement(
        complementary_result,
        s_prime_inputs,
        complement_label,
        complement_index,
        complement_class,
        complement_subgroup :
        normal_only := normal_only,
        minimal_relations := minimal_relations,
        print_results := print_results
    );
end function;


function build_presentation_for_complementary_result_from_integral_primes(
    complementary_result,
    s_prime_specs :
    normal_only := false,
    complement_selector := 1,
    minimal_relations := true,
    print_results := 1
)
    s_prime_ideals := admissible_prime_ideals_from_specs(
        complementary_result`localized_unit_group`order_data,
        complementary_result`modulus_ideal,
        s_prime_specs
    );

    return build_presentation_for_complementary_result(
        complementary_result,
        s_prime_ideals :
        normal_only := normal_only,
        complement_selector := complement_selector,
        minimal_relations := minimal_relations,
        print_results := print_results
    );
end function;


function build_presentation_for_complementary_triple(
    complementary_triple,
    s_prime_inputs :
    normal_only := false,
    complement_selector := 1,
    minimal_relations := true,
    print_results := 1
)
    return build_presentation_for_complementary_result(
        complementary_triple`complementary_result,
        s_prime_inputs :
        normal_only := normal_only,
        complement_selector := complement_selector,
        minimal_relations := minimal_relations,
        print_results := print_results
    );
end function;


function build_presentation_for_complementary_triple_from_integral_primes(
    complementary_triple,
    s_prime_specs :
    normal_only := false,
    complement_selector := 1,
    minimal_relations := true,
    print_results := 1
)
    return build_presentation_for_complementary_result_from_integral_primes(
        complementary_triple`complementary_result,
        s_prime_specs :
        normal_only := normal_only,
        complement_selector := complement_selector,
        minimal_relations := minimal_relations,
        print_results := print_results
    );
end function;


function build_presentations_for_complementary_result(
    complementary_result,
    s_prime_inputs :
    normal_only := false,
    minimal_relations := true,
    print_results := 1
)
    validate_presentation_complementary_result(complementary_result);
    normal_only := validate_bool_parameter(normal_only, "normal_only");
    minimal_relations := validate_bool_parameter(minimal_relations, "minimal_relations");
    print_results := validate_print_level(print_results);

    s_prime_ideals := normalized_s_prime_inputs(
        complementary_result`localized_unit_group`order_data,
        complementary_result`modulus_ideal,
        s_prime_inputs
    );
    complement_list := presentation_sorted_complement_list(normal_only select
        complementary_result`normal_complement_classes
    else
        complementary_result`complement_classes);
    presentations := [];

    for complement_selector in [1..#complement_list] do
        Append(~presentations, build_presentation_for_complementary_result(
            complementary_result,
            s_prime_ideals :
            normal_only := normal_only,
            complement_selector := complement_selector,
            minimal_relations := minimal_relations,
            print_results := 0
        ));
    end for;

    return rec<presentation_suite_format |
        order_data := complementary_result`localized_unit_group`order_data,
        complementary_triple := false,
        complementary_result := complementary_result,
        localized_unit_group := complementary_result`localized_unit_group,
        s_prime_inputs := s_prime_inputs,
        s_prime_ideals := s_prime_ideals,
        normal_only := normal_only,
        presentations := presentations
    >;
end function;


function build_presentations_for_complementary_triple(
    complementary_triple,
    s_prime_inputs :
    normal_only := false,
    minimal_relations := true,
    print_results := 1
)
    presentation_suite := build_presentations_for_complementary_result(
        complementary_triple`complementary_result,
        s_prime_inputs :
        normal_only := normal_only,
        minimal_relations := minimal_relations,
        print_results := print_results
    );

    return rec<presentation_suite_format |
        order_data := presentation_suite`order_data,
        complementary_triple := complementary_triple,
        complementary_result := presentation_suite`complementary_result,
        localized_unit_group := presentation_suite`localized_unit_group,
        s_prime_inputs := presentation_suite`s_prime_inputs,
        s_prime_ideals := presentation_suite`s_prime_ideals,
        normal_only := presentation_suite`normal_only,
        presentations := presentation_suite`presentations
    >;
end function;


function build_presentations_for_complementary_result_from_integral_primes(
    complementary_result,
    s_prime_specs :
    normal_only := false,
    minimal_relations := true,
    print_results := 1
)
    s_prime_ideals := admissible_prime_ideals_from_specs(
        complementary_result`localized_unit_group`order_data,
        complementary_result`modulus_ideal,
        s_prime_specs
    );

    return build_presentations_for_complementary_result(
        complementary_result,
        s_prime_ideals :
        normal_only := normal_only,
        minimal_relations := minimal_relations,
        print_results := print_results
    );
end function;


function build_presentations_for_complementary_triple_from_integral_primes(
    complementary_triple,
    s_prime_specs :
    normal_only := false,
    minimal_relations := true,
    print_results := 1
)
    return build_presentations_for_complementary_result_from_integral_primes(
        complementary_triple`complementary_result,
        s_prime_specs :
        normal_only := normal_only,
        minimal_relations := minimal_relations,
        print_results := print_results
    );
end function;


procedure print_presentation_summary(
    presentation,
    show_relations,
    show_generator_representatives
)
    show_relations := validate_bool_parameter(show_relations, "show_relations");
    show_generator_representatives := validate_bool_parameter(
        show_generator_representatives,
        "show_generator_representatives"
    );

    print "";
    print "============================================================";
    print "Presentation Summary";
    print "============================================================";
    print "order index:", presentation`order_data`index;
    print "source:", presentation`source_group_label;
    print "C:", ideal_summary("C", presentation`candidate_ideal);
    print "selected complement index:", presentation`complement_index;
    print "selected complement order:", #presentation`complement_subgroup;

    if presentation`localized_unit_group cmpne false then
        print "T:",
              complementary_ramified_subset_string(
                  presentation`localized_unit_group`ramified_subset
              );
        print "|U_T|:", presentation`localized_unit_group`subgroup_order;
        print "";
        presentation_print_t_unit_generators(presentation`t_unit_generator_data);
    end if;

    print "";
    print "S-primes:";
    for s_index in [1..#presentation`s_prime_ideals] do
        print Sprintf(
            "  S%o: %o | generators=%o",
            s_index,
            ideal_summary("P", presentation`s_prime_ideals[s_index]),
            #presentation`a_representatives[presentation`s_prime_ideals[s_index]]
        );
    end for;

    print "";
    print "Gamma abelianization:", AbelianQuotientInvariants(presentation`gamma_group);
    print "generator torsion present:", not presentation`generators_torsion_free;
    print "square torsion count:", #presentation`square_torsion;

    print "";
    presentation_print_conventions(presentation`normalization_conventions);

    if show_generator_representatives then
        print "";
        presentation_print_generator_representatives(presentation`presentation_generator_data);
    end if;

    if show_relations then
        print "";
        print "Relators:";
        if presentation`pretty_payload cmpeq false then
            print "  unavailable because minimal_relations=false";
        else
            pretty_print_relations(presentation`pretty_payload);
        end if;
    end if;
end procedure;


procedure print_presentation_suite(
    presentation_suite,
    show_relations,
    show_generator_representatives
)
    show_relations := validate_bool_parameter(show_relations, "show_relations");
    show_generator_representatives := validate_bool_parameter(
        show_generator_representatives,
        "show_generator_representatives"
    );

    print "";
    print "============================================================";
    print "Complementary Triple Presentations";
    print "============================================================";
    print "order index:", presentation_suite`order_data`index;
    print "C:", ideal_summary("C", presentation_suite`complementary_result`modulus_ideal);
    print "T:",
          complementary_ramified_subset_string(
              presentation_suite`localized_unit_group`ramified_subset
          );
    print "|U_T|:", presentation_suite`localized_unit_group`subgroup_order;
    print "#presentations:", #presentation_suite`presentations;

    for presentation in presentation_suite`presentations do
        print_presentation_summary(
            presentation,
            show_relations,
            show_generator_representatives
        );
    end for;
end procedure;


// Convenience wrapper: build the complementary result for P^k first, then
// build the presentation from that complementary-triple data.
function build_presentation_for_modulus(
    order_data,
    prime_ideal,
    k,
    s_prime_inputs :
    normal_only := false,
    complement_selector := 1,
    minimal_relations := true,
    print_results := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    T := []
)
    print_results := validate_print_level(print_results);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );
    normal_only := validate_bool_parameter(normal_only, "normal_only");
    minimal_relations := validate_bool_parameter(minimal_relations, "minimal_relations");
    complement_selector := normalize_complement_selector(complement_selector);

    complementary_result := complementary_pairs_at_ideal(
        order_data,
        normalize_prime_ideal(order_data`integer_ring, prime_ideal)^k :
        T := T,
        require_ambient := true,
        Print := print_results,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds
    );

    return build_presentation_for_complementary_result(
        complementary_result,
        s_prime_inputs :
        normal_only := normal_only,
        complement_selector := complement_selector,
        minimal_relations := minimal_relations,
        print_results := print_results
    );
end function;
