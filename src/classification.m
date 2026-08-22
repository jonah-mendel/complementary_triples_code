// Exact classification of nontrivial minimal complementary triples.
//
// For T contained in the finite ramification set of B, set
//
//        Gamma_T = <Gamma_emptyset, alpha_p : p in T>
//
// inside the projective normalizer.  For an ideal
//
//                       C = product_p p^e_p,
//
// let rho_C be reduction modulo C.  The ideals of interest are those minimal
// under divisibility for which rho_C is injective.  A complementary subgroup
// H satisfies H meet rho_C(Gamma_T) = 1 and
// |H| * |rho_C(Gamma_T)| = |G_C|.
//
// Entry points: LocalizedGroups, LocalizedGroup, MinimalInjectiveIdeals,
// MinimalComplementaryIdeals, ReductionData, and ClassifyOrder.  The
// lower-case complementary_* functions are internal, though a few are
// shared with verify.m and src/presentations.m.  Comments write Gamma_T for
// the group that record fields call localized_unit_group and error strings
// call U_T.


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
    group_model,
    ambient_group,
    image_subgroup,
    generator_images,
    uses_ramified_extension
>;


// Reduction of Gamma_T modulo C, before the complementary subgroups are found.
reduction_image_result_format := recformat<
    localized_unit_group,
    modulus_ideal,
    reduction_factors,
    ambient_group,
    image_subgroup,
    injective
>;


// The same reduction together with all conjugacy classes of complements H.
complementary_ideal_result_format := recformat<
    localized_unit_group,
    modulus_ideal,
    reduction_factors,
    ambient_group,
    image_subgroup,
    complement_classes,
    normal_complement_classes,
    injective
>;


minimal_ideal_poset_result_format := recformat<
    localized_unit_group,
    minimal_injective_ideals,
    minimal_results
>;


classification_order_result_format := recformat<
    localized_groups,
    exclusion_reasons,
    poset_results
>;


complementary_context_format := recformat<
    order_data,
    normalizer_lookup,
    normalizer_representative_lookup,
    alpha_data,
    localized_unit_group_cache,
    local_group_model_cache,
    local_image_cache
>;


// ---------------------------------------------------------------------------
// Canonical keys and the divisibility order on supported ideals
// ---------------------------------------------------------------------------


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
        lookup[CanonicalIdealKey(ideal_x)] := ideal_x;
    end for;

    return complementary_sorted_lookup_values(lookup);
end function;


function complementary_subset_key(ramified_subset)
    return complementary_join_strings(
        [CanonicalIdealKey(prime_ideal) : prime_ideal in complementary_sorted_ideals(ramified_subset)],
        " || "
    );
end function;


function complementary_vector_key(exponent_vector)
    return Sprint(exponent_vector);
end function;


function complementary_normalized_order_element_key(order_data, element_x)
    integral_element := ord_primitive_integral_representative(order_data, element_x);
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


// The exponent vector (e_p)_p represents product_p p^e_p.  Coordinatewise
// comparison is the divisibility order used to test minimality.
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


// Admit a successor to the frontier only when it escapes every recorded
// minimal cone and has been neither tested nor queued.  A multiple of an
// injective vector is injective, so a pruned upper cone contains no
// further minimal ideal.
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


// ---------------------------------------------------------------------------
// The localized projective unit groups Gamma_T
// ---------------------------------------------------------------------------

// The subsets T run through the power set of the admissible finite ramified
// primes.  Their recursive order begins with the empty set.
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


function complementary_relevant_primes(order_data, norm_bound)
    return complementary_sorted_ideals(RelevantPrimes(order_data, norm_bound));
end function;


// A ramified prime may occur in T only when the order is locally maximal
// there, so that the ramified normalizer generator alpha_p is available.
function admissible_ramified_primes(order_data)
    return complementary_sorted_ideals([
        prime_ideal :
        prime_ideal in ramified_primes(order_data) |
        order_is_locally_maximal_at_prime(order_data, prime_ideal)
    ]);
end function;


// Work in the finite projective normalizer N(O)/(K^* O^*).  The two lookups
// identify its abstract elements with primitive integral quaternion
// representatives, which are needed for reduction modulo prime powers.
function complementary_build_context(order_data)
    if order_data`class_number ne 1 then
        error "Complementary-triple classification requires a class-number-one order.";
    end if;

    normalizer_lookup := AssociativeArray();
    normalizer_representative_lookup := AssociativeArray();

    for normalizer_group_element in order_data`normalizer_group do
        normalizer_element := ord_primitive_integral_representative(
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
        local_image_cache := AssociativeArray()
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


// Inverse of complementary_normalizer_group_element: recover the stored
// primitive integral quaternion representative of an abstract
// normalizer-group element.  Shared with verify.m and the presentation
// module.
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
        unit_element := ord_primitive_integral_representative(
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


// The element alpha_p represents the ramified normalizer class adjoined when
// p belongs to T.
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

    alpha_element := ramified_base_generator(order_data, prime_ideal);
    alpha_group_element := complementary_normalizer_group_element(context, alpha_element);
    alpha_record := rec<localized_alpha_data_format |
        prime_ideal := prime_ideal,
        alpha_element := alpha_element,
        normalizer_group_element := alpha_group_element
    >;

    context`alpha_data[prime_ideal] := alpha_record;
end procedure;


// Starting with Gamma_emptyset, adjoining alpha_p for p in T gives Gamma_T.
// Constructing the groups recursively keeps the chosen generators compatible
// as T grows.
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


// Build the shared context together with Gamma_T for every admissible
// ramified subset T.  The subsets are enumerated with T = emptyset first,
// so the first entry of the returned list is always Gamma_emptyset;
// ClassifyOrder and verify.m rely on that position.
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


// ---------------------------------------------------------------------------
// Reduction of Gamma_T modulo a prime power
// ---------------------------------------------------------------------------

// When all elements have even p-adic norm valuation, the local target is
//
//        G_{p^k} = (O / p^k O)^* / (R / p^k)^*.
//
// An element of odd valuation lies in the other projective-normalizer coset,
// so the target is the corresponding extension of G_{p^k} by C_2.
procedure complementary_local_group_model(
    ~context,
    prime_ideal,
    k,
    ~group_model :
    Print := 1
)
    cache_key := Sprintf("%o || %o", Sprint(prime_ideal), k);

    if IsDefined(context`local_group_model_cache, cache_key) then
        group_model := context`local_group_model_cache[cache_key];
        return;
    end if;

    group_model := FiniteQuotient(
        context`order_data,
        prime_ideal,
        k :
        Print := Print
    );

    context`local_group_model_cache[cache_key] := group_model;
end procedure;


// Reduce an integral representative and pass from its scalar class to the
// corresponding element of G_{p^k}.
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


// Since the reduction is a homomorphism, its image order divides |Gamma_T|.
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
    modulus_ideal,
    group_model,
    ambient_group,
    image_subgroup,
    generator_images,
    uses_ramified_extension
)
    complementary_assert_reduction_image_order(
        localized_unit_group,
        modulus_ideal,
        image_subgroup,
        "local reduction image"
    );

    return rec<localized_reduction_image_format |
        group_model := group_model,
        ambient_group := ambient_group,
        image_subgroup := image_subgroup,
        generator_images := generator_images,
        uses_ramified_extension := uses_ramified_extension
    >;
end function;


// Odd valuation distinguishes the nontrivial coset of the local projective
// unit group inside the image of the projective normalizer.
function complementary_order_element_has_odd_valuation_at_prime(order_data, order_element, prime_ideal)
    norm_ideal := Norm(order_element) * order_data`integer_ring;
    return (Valuation(norm_ideal, prime_ideal) mod 2) ne 0;
end function;


function complementary_localized_group_needs_ramified_extension(localized_unit_group, prime_ideal)
    if Valuation(Discriminant(localized_unit_group`order_data`quaternion_algebra), prime_ideal) eq 0 then
        return false;
    end if;

    for generator_element in localized_unit_group`generator_elements do
        if complementary_order_element_has_odd_valuation_at_prime(
            localized_unit_group`order_data,
            generator_element,
            prime_ideal
        ) then
            return true;
        end if;
    end for;

    return false;
end function;


// Map the fixed generators of Gamma_T into the appropriate local target.
procedure complementary_local_reduction_image(
    ~context,
    localized_unit_group,
    prime_ideal,
    k,
    ~local_result :
    Print := 1
)
    uses_ramified_extension :=
        complementary_localized_group_needs_ramified_extension(
            localized_unit_group,
            prime_ideal
        );
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
        Print := Print
    );

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
            // The quotient model uses left multiplication, whereas Magma acts
            // on points on the right; inversion gives the reduction
            // homomorphism Gamma_T -> G_{p^k}.
            Append(~generator_images, image_permutation^-1);
        end for;
    end if;

    image_subgroup := complementary_subgroup_from_generators(ambient_group, generator_images);
    local_result := complementary_local_reduction_image_record(
        localized_unit_group,
        prime_ideal^k,
        group_model,
        ambient_group,
        image_subgroup,
        generator_images,
        uses_ramified_extension
    );
    context`local_image_cache[cache_key] := local_result;
end procedure;


// ---------------------------------------------------------------------------
// Composite moduli and complementary subgroups
// ---------------------------------------------------------------------------

// Embed a permutation acting on one local block into the symmetric group
// on the disjoint union of all blocks, fixing the other blocks pointwise.
function complementary_embedded_block_permutation(block_permutation, offset, total_degree)
    permutation_entries := [i : i in [1..total_degree]];
    block_degree := Degree(Parent(block_permutation));

    for i in [1..block_degree] do
        permutation_entries[offset + i] := offset + (i^block_permutation);
    end for;

    return Sym(total_degree)!permutation_entries;
end function;


// For C = product p^e, the Chinese remainder theorem identifies the ambient
// group with the product of the local groups.  Disjoint permutation blocks
// realize this product, and each generator of Gamma_T maps diagonally to its
// local reductions.
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


function complementary_ideal_image_record(
    localized_unit_group,
    modulus_ideal,
    reduction_factors,
    ambient_group,
    image_subgroup
)
    complementary_assert_reduction_image_order(
        localized_unit_group,
        modulus_ideal,
        image_subgroup,
        "ideal reduction image"
    );

    return rec<reduction_image_result_format |
        localized_unit_group := localized_unit_group,
        modulus_ideal := modulus_ideal,
        reduction_factors := reduction_factors,
        ambient_group := ambient_group,
        image_subgroup := image_subgroup,
        injective := #image_subgroup eq localized_unit_group`subgroup_order
    >;
end function;


// Enumerate the conjugacy classes of H with trivial intersection with the
// image and complementary order in G_C.
function complementary_result_from_image(image_result)
    complement_list := complement_classes(image_result`ambient_group, image_result`image_subgroup);
    return rec<complementary_ideal_result_format |
        localized_unit_group := image_result`localized_unit_group,
        modulus_ideal := image_result`modulus_ideal,
        reduction_factors := image_result`reduction_factors,
        ambient_group := image_result`ambient_group,
        image_subgroup := image_result`image_subgroup,
        complement_classes := complement_list,
        normal_complement_classes := normal_complement_classes(
            image_result`ambient_group,
            complement_list
        ),
        injective := image_result`injective
    >;
end function;


// Factor C, form every local reduction Gamma_T -> G_{p^e}, and combine them by
// the Chinese remainder theorem.  Injectivity is equivalent to preservation
// of the order of Gamma_T.
procedure complementary_ideal_image_with_context(
    ~context,
    localized_unit_group,
    modulus_ideal,
    ~image_result :
    Print := 1
)
    normalized_modulus := complementary_normalize_modulus_ideal(
        context`order_data`integer_ring,
        modulus_ideal
    );
    factor_data := Factorization(normalized_modulus);
    reduction_factors := [];

    for factor in factor_data do
        local_result := false;
        complementary_local_reduction_image(
            ~context,
            localized_unit_group,
            factor[1],
            factor[2],
            ~local_result :
            Print := Print
        );
        Append(~reduction_factors, local_result);
    end for;

    if #reduction_factors eq 1 then
        ambient_group := reduction_factors[1]`ambient_group;
        image_subgroup := reduction_factors[1]`image_subgroup;
    else
        ambient_group, image_subgroup := complementary_composite_ambient_and_image(
            reduction_factors,
            localized_unit_group
        );
    end if;

    image_result := complementary_ideal_image_record(
        localized_unit_group,
        normalized_modulus,
        reduction_factors,
        ambient_group,
        image_subgroup
    );
end procedure;


// Reduce Gamma_T modulo one modulus C and return the complete record: the
// image rho_C(Gamma_T) inside G_C together with all conjugacy classes of
// complementary subgroups H.  Passing an existing context reuses its
// cached local models; this is the workhorse behind ReductionData and the
// presentation module.
function complementary_pairs_at_ideal(
    order_data,
    modulus_ideal :
    T := [],
    context := false,
    Print := 1
)
    Print := validate_print_level(Print);
    if context cmpeq false then
        context := complementary_build_context(order_data);
    elif Type(context) ne Rec then
        error "context must be false or a complementary context record.";
    end if;
    localized_unit_group := false;
    image_result := false;

    complementary_localized_unit_group_from_subset(~context, T, ~localized_unit_group);
    complementary_ideal_image_with_context(
        ~context,
        localized_unit_group,
        modulus_ideal,
        ~image_result :
        Print := Print
    );

    return complementary_result_from_image(image_result);
end function;


// For a prime-power modulus C = p^k the reduction has a single local
// factor; expose its underlying FiniteQuotient model of G_{p^k}.
// verify.m uses this to evaluate torsion obstructions on chosen
// subgroups.
function complementary_prime_power_group_model(complementary_result)
    if #complementary_result`reduction_factors ne 1 then
        error "This operation requires a prime-power complementary result.";
    end if;

    return complementary_result`reduction_factors[1]`group_model;
end function;


// ---------------------------------------------------------------------------
// Minimal injective ideals
// ---------------------------------------------------------------------------

// The relevant support consists of all finite ramified primes and the split
// primes p with N(p) <= |Gamma_T|.  Starting from the prime ideals, a
// noninjective exponent vector (e_p)_p is replaced by all vectors obtained by
// increasing one exponent.  Once reduction is injective, it remains injective
// at every multiple, so that entire upper cone contains no new minimal ideal.
procedure ExactMinimalIdealPosetWithContext(
    ~context,
    localized_group,
    ~poset_result :
    Print := 0,
    IdealsOnly := false
)
    Print := validate_print_level(Print);
    relevant_primes := complementary_relevant_primes(
        context`order_data,
        localized_group`subgroup_order
    );
    frontier := [];
    tested_lookup := AssociativeArray();
    minimal_vectors := [];
    minimal_ideals := [];
    minimal_results := [];

    for i in [1..#relevant_primes] do
        exponent_vector := [0 : j in [1..#relevant_primes]];
        exponent_vector[i] := 1;
        Append(~frontier, exponent_vector);
    end for;

    // The frontier is consumed first-in first-out, so vectors are examined
    // in nondecreasing total exponent.  Every proper divisor of a minimal
    // injective vector is noninjective, so each minimal vector is reached
    // and recorded before any of its proper multiples is popped; the
    // divisibility test below therefore discards exactly the nonminimal
    // injective vectors.  Termination is the paper's finiteness argument:
    // reduction modulo a sufficiently high prime power is injective on the
    // finite group Gamma_T.
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
        image_result := false;
        complementary_ideal_image_with_context(
            ~context,
            localized_group,
            modulus_ideal,
            ~image_result :
            Print := Print
        );

        if image_result`injective then
            Append(~minimal_vectors, exponent_vector);
            Append(~minimal_ideals, modulus_ideal);
            if not IdealsOnly then
                Append(~minimal_results, complementary_result_from_image(image_result));
            end if;
            continue;
        end if;

        for i in [1..#relevant_primes] do
            successor := exponent_vector;
            successor[i] +:= 1;
            complementary_append_vector_if_new(
                successor,
                minimal_vectors,
                tested_lookup,
                ~frontier
            );
        end for;
    end while;

    poset_result := rec<minimal_ideal_poset_result_format |
        localized_unit_group := localized_group,
        minimal_injective_ideals := minimal_ideals,
        minimal_results := minimal_results
    >;
end procedure;


// Return the minimal injective ideals without retaining their finite ambient
// groups.  ReductionData may then be applied to each ideal separately.
function MinimalInjectiveIdeals(order_data, T : Print := 0)
    context := complementary_build_context(order_data);
    localized_group := false;
    poset_result := false;
    complementary_localized_unit_group_from_subset(~context, T, ~localized_group);
    ExactMinimalIdealPosetWithContext(
        ~context,
        localized_group,
        ~poset_result :
        Print := Print,
        IdealsOnly := true
    );
    return SortIdeals(poset_result`minimal_injective_ideals);
end function;


// Return the same minimal ideals together with all their complement classes.
function MinimalComplementaryIdeals(order_data, T : Print := 0)
    context := complementary_build_context(order_data);
    localized_group := false;
    poset_result := false;
    complementary_localized_unit_group_from_subset(~context, T, ~localized_group);
    ExactMinimalIdealPosetWithContext(
        ~context,
        localized_group,
        ~poset_result :
        Print := Print
    );
    return poset_result;
end function;


// Construct Gamma_T for every admissible ramified subset T.
function LocalizedGroups(order_data)
    context, localized_groups := complementary_context_with_all_U_T(order_data);
    return localized_groups;
end function;


// Construct Gamma_T for one specified subset T.
function LocalizedGroup(order_data, T)
    context := complementary_build_context(order_data);
    localized_group := false;
    complementary_localized_unit_group_from_subset(~context, T, ~localized_group);
    return localized_group;
end function;


// Compute Gamma_T -> G_C and all complement classes for one modulus C.
function ReductionData(order_data, T, modulus_ideal : Print := 0)
    return complementary_pairs_at_ideal(
        order_data,
        modulus_ideal :
        T := T,
        Print := Print
    );
end function;


// ---------------------------------------------------------------------------
// Nontriviality and the classification of one order
// ---------------------------------------------------------------------------

// When Gamma_emptyset is trivial, the cases below are the two elementary
// configurations excluded by the paper's definition of a nontrivial minimal
// complementary triple.
function ClassificationExclusionReason(gamma_emptyset, localized_group)
    if gamma_emptyset`subgroup_order ne 1 then
        return "";
    end if;

    if #localized_group`ramified_subset eq 0 then
        return "Gamma_emptyset=1 and T=emptyset";
    end if;

    if #localized_group`ramified_subset eq 1 then
        selected_prime := localized_group`ramified_subset[1];
        for ramified_prime in localized_group`admissible_ramified_primes do
            if ramified_prime ne selected_prime then
                return "";
            end if;
        end for;
        return "Gamma_emptyset=1, #T=1, and no distinct ramified modulus prime";
    end if;

    return "";
end function;


// For a singleton T and trivial Gamma_emptyset, nontriviality requires a
// ramified modulus prime different from the prime in T.  Subsets for
// which no such prime can exist at all were already removed by
// ClassificationExclusionReason; this predicate checks that the modulus
// actually uses one.
function IsNontrivialMinimalIdeal(gamma_emptyset, localized_group, modulus_ideal)
    if gamma_emptyset`subgroup_order ne 1 then
        return true;
    end if;

    if #localized_group`ramified_subset eq 0 then
        return false;
    end if;

    if #localized_group`ramified_subset eq 1 then
        selected_prime := localized_group`ramified_subset[1];
        for factor in Factorization(modulus_ideal) do
            if factor[1] ne selected_prime and
               Index(localized_group`admissible_ramified_primes, factor[1]) ne 0 then
                return true;
            end if;
        end for;
        return false;
    end if;

    return true;
end function;


// Keep only the nontrivial minimal ideals in the sense of
// IsNontrivialMinimalIdeal, preserving the parallel ideal and result
// sequences.  Requires a poset result computed with IdealsOnly := false.
function NontrivialPart(gamma_emptyset, poset_result)
    minimal_ideals := [];
    minimal_results := [];
    for i in [1..#poset_result`minimal_injective_ideals] do
        if IsNontrivialMinimalIdeal(
            gamma_emptyset,
            poset_result`localized_unit_group,
            poset_result`minimal_injective_ideals[i]
        ) then
            Append(~minimal_ideals, poset_result`minimal_injective_ideals[i]);
            Append(~minimal_results, poset_result`minimal_results[i]);
        end if;
    end for;

    return rec<minimal_ideal_poset_result_format |
        localized_unit_group := poset_result`localized_unit_group,
        minimal_injective_ideals := minimal_ideals,
        minimal_results := minimal_results
    >;
end function;


// Classify every Gamma_T attached to the order, omitting only the mathematical
// exclusions above and retaining the nontrivial minimal ideals.
function ClassifyOrder(order_data : Print := 0)
    context, localized_groups := complementary_context_with_all_U_T(order_data);
    // complementary_all_subsets lists the empty set first, so the first
    // localized group is Gamma_emptyset.
    gamma_emptyset := localized_groups[1];
    exclusion_reasons := [];
    // The i-th entry is false for a mathematically excluded Gamma_T and is the
    // corresponding minimal-ideal record otherwise.
    poset_results := [* *];

    for localized_group in localized_groups do
        reason := ClassificationExclusionReason(gamma_emptyset, localized_group);
        Append(~exclusion_reasons, reason);
        if reason ne "" then
            Append(~poset_results, false);
            continue;
        end if;

        result := false;
        ExactMinimalIdealPosetWithContext(
            ~context,
            localized_group,
            ~result :
            Print := Print
        );
        Append(~poset_results, NontrivialPart(gamma_emptyset, result));
    end for;

    return rec<classification_order_result_format |
        localized_groups := localized_groups,
        exclusion_reasons := exclusion_reasons,
        poset_results := poset_results
    >;
end function;
