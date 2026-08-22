// ============================================================================
// Sigma-relation validation and minimization utilities.
//
// This file builds the finite presentations of the groups Gamma displayed in
// the paper: generators are the A[P] representatives attached to each S-prime
// P, and relations are the inverse relations together with one metacommutation
// square relation per geometric square.  This first section validates the
// sigma (metacommutation) data and reduces the square relations to canonical
// representatives; the presentation builders follow in the second half.
// ============================================================================


function presentation_sigma_key_summary(label, key)
    if Type(key) eq RngOrdIdl then
        return ideal_summary(label, key);
    end if;

    return Sprintf("%o: %o", label, key);
end function;


// Check sigma symmetry:
// sigma_{p,q}(a,b) = <b',a'> should invert through sigma_{q,p}.
//
// Returns <BoolElt, SeqEnum>. On failure the second output gives a compact
// witness to aid debugging.
function check_sigma_symmetry(sigma_map)
    for prime_pair in Keys(sigma_map) do
        prime_p := prime_pair[1];
        prime_q := prime_pair[2];

        if not IsDefined(sigma_map, <prime_q, prime_p>) then
            return false, [* "missing sigma reverse key", prime_p, prime_q *];
        end if;

        for ab in Keys(sigma_map[<prime_p, prime_q>]) do
            a := ab[1];
            b := ab[2];
            image := sigma_map[<prime_p, prime_q>][<a, b>];

            if not IsDefined(sigma_map[<prime_q, prime_p>], image) then
                return false, [* "missing reverse image", prime_p, prime_q, a, b, "->", image *];
            end if;

            back_image := sigma_map[<prime_q, prime_p>][image];
            if back_image[1] ne a or back_image[2] ne b then
                return false, [* "symmetry mismatch", prime_p, prime_q, a, b, "->", image, "back->", back_image *];
            end if;
        end for;
    end for;

    return true, [* *];
end function;


// Check inverse compatibility identity:
// sigma_{q,p}(inv_q(b), inv_p(a)) = <inv_p(a'), inv_q(b')>
// when sigma_{p,q}(a,b) = <b',a'>.
function check_sigma_inverse_compatibility(a_representatives, sigma_map, inverse_map)
    for prime_pair in Keys(sigma_map) do
        prime_p := prime_pair[1];
        prime_q := prime_pair[2];

        for ab in Keys(sigma_map[<prime_p, prime_q>]) do
            a := ab[1];
            b := ab[2];
            image := sigma_map[<prime_p, prime_q>][<a, b>];

            b_prime := image[1];
            a_prime := image[2];

            lhs := sigma_map[<prime_q, prime_p>][<inverse_map[prime_q][b], inverse_map[prime_p][a]>];
            rhs := <inverse_map[prime_p][a_prime], inverse_map[prime_q][b_prime]>;

            if lhs ne rhs then
                print "Inverse compatibility check failed.";
                print presentation_sigma_key_summary("p", prime_p);
                print presentation_sigma_key_summary("q", prime_q);
                print "a index =", Index(a_representatives[prime_p], a);
                print "b index =", Index(a_representatives[prime_q], b);
                print "a' index =", Index(a_representatives[prime_p], a_prime);
                print "b' index =", Index(a_representatives[prime_q], b_prime);
                return false;
            end if;
        end for;
    end for;

    return true;
end function;


// Global consistency wrapper for sigma data.
function check_sigma_consistency(a_representatives, sigma_map, inverse_map)
    is_consistent := true;

    symmetry_ok, symmetry_witness := check_sigma_symmetry(sigma_map);
    if not symmetry_ok then
        print "Sigma symmetry check: FAIL";
        for item in symmetry_witness do
            if Type(item) eq RngOrdIdl then
                print ideal_summary("symmetry witness ideal key", item);
            else
                print item;
            end if;
        end for;
        is_consistent := false;
    end if;

    inverse_ok := check_sigma_inverse_compatibility(a_representatives, sigma_map, inverse_map);
    if not inverse_ok then
        is_consistent := false;
    end if;

    return is_consistent;
end function;


// Return all cyclic rotations of a length-4 relation word.
function cyclic_permutations_4(relation_word)
    return [relation_word[i..4] cat relation_word[1..i - 1] : i in [1..4]];
end function;


// Invert relation [<p,a>,<q,b>,<p,a_inv>,<q,b_inv>] while preserving p/q slots.
function invert_relation(inverse_map, relation_word)
    prime_p := relation_word[1][1];
    a := relation_word[1][2];

    prime_q := relation_word[2][1];
    b := relation_word[2][2];

    a_prime_inv := relation_word[3][2];
    b_prime_inv := relation_word[4][2];

    return [
        <prime_q, inverse_map[prime_q][b_prime_inv]>,
        <prime_p, inverse_map[prime_p][a_prime_inv]>,
        <prime_q, inverse_map[prime_q][b]>,
        <prime_p, inverse_map[prime_p][a]>
    ];
end function;


// Build the full equivalence class of a square relation under:
// - cyclic permutation,
// - inversion,
// - and commutator-flip symmetry for commuting cases.
function relation_equivalence_class(inverse_map, relation_word)
    relation_class := [];

    for rotation in cyclic_permutations_4(relation_word) do
        Append(~relation_class, rotation);
        Append(~relation_class, invert_relation(inverse_map, rotation));
    end for;

    prime_p := relation_word[1][1];
    a := relation_word[1][2];

    prime_q := relation_word[2][1];
    b := relation_word[2][2];

    a_prime_inv := relation_word[3][2];
    b_prime_inv := relation_word[4][2];

    // If relation is a commutator, include the swapped commutator orbit.
    if inverse_map[prime_p][a] eq a_prime_inv and inverse_map[prime_q][b] eq b_prime_inv then
        commutator_word := [
            <prime_p, a>,
            <prime_q, inverse_map[prime_q][b]>,
            <prime_p, inverse_map[prime_p][a]>,
            <prime_q, b>
        ];

        for rotation in cyclic_permutations_4(commutator_word) do
            Append(~relation_class, rotation);
            Append(~relation_class, invert_relation(inverse_map, rotation));
        end for;
    end if;

    return relation_class;
end function;


// Canonicalize a relation by lexicographic comparison of serialized forms.
function canonical_relation_representative(inverse_map, relation_word)
    reps := relation_equivalence_class(inverse_map, relation_word);
    best := reps[1];
    best_key := Sprint(best);

    for candidate in reps[2..#reps] do
        candidate_key := Sprint(candidate);
        if candidate_key lt best_key then
            best := candidate;
            best_key := candidate_key;
        end if;
    end for;

    return best;
end function;


// Compute minimal square-relation representatives for a pair of primes.
//
// Every vertex pair (a,b) in A[P] x A[Q] yields a square relation, but cyclic
// rotation, inversion, and (for commuting squares) the commutator flip all
// describe the same geometric square.  Keeping one canonical representative
// per equivalence class gives the minimal relator set used in the displayed
// presentations.
//
// Output is an associative array:
//   key   = canonical representative relation,
//   value = full equivalence class generated from that representative.
function minimal_sigma_relations(a_representatives, sigma_map, inverse_map, pair)
    pair_list := [prime : prime in pair];
    prime_p := pair_list[1];
    prime_q := pair_list[2];

    vertices := [<a, b> : a in a_representatives[prime_p], b in a_representatives[prime_q]];

    minimal_relations := AssociativeArray();
    seen_representatives := AssociativeArray();

    for vertex in vertices do
        image := sigma_map[<prime_p, prime_q>][vertex];

        // Relation shape is fixed so that p/q slot information is preserved.
        relation_word := [
            <prime_p, vertex[1]>,
            <prime_q, vertex[2]>,
            <prime_p, inverse_map[prime_p][image[2]]>,
            <prime_q, inverse_map[prime_q][image[1]]>
        ];

        representative := canonical_relation_representative(inverse_map, relation_word);
        representative_key := Sprint(representative);

        if not IsDefined(seen_representatives, representative_key) then
            seen_representatives[representative_key] := true;
            minimal_relations[representative] := relation_equivalence_class(inverse_map, representative);
        end if;
    end for;

    return minimal_relations;
end function;
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
// Public API:
// - PresentationForComplement(complementary_result, s_prime_inputs : ...)
// - PresentationForModulus(order_data, modulus_ideal, s_prime_inputs : ...)
//
// verify.m re-runs PresentationForComplement on the paper's two displayed
// examples and compares the computed relators against the displayed ones via
// canonical_relation_representative.
// ============================================================================


presentation_result_format := recformat<
    order_data,
    modulus_ideal,
    complement_index,
    complement_subgroup,
    s_prime_ideals,
    a_representatives,
    sigma_map,
    inverse_map,
    gamma_group,
    minimal_square_relations,
    generators_torsion_free,
    square_torsion
>;


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


function presentation_key_summary(label, object_x)
    if Type(object_x) eq RngOrdIdl then
        return ideal_summary(label, object_x);
    end if;

    return Sprintf("%o: %o", label, object_x);
end function;


function presentation_prime_divides_ideal(prime_ideal, modulus_ideal)
    return Valuation(modulus_ideal, prime_ideal) gt 0;
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


// Validate and normalize the S-primes: distinct prime ideals, coprime to
// the complementary modulus C, and unramified in the quaternion algebra —
// the standing hypotheses on the pair (C, S) for the presentation
// construction.
function normalized_s_prime_inputs(order_data, candidate_ideal, s_prime_inputs)
    integer_ring := order_data`integer_ring;
    algebra_discriminant := Discriminant(order_data`quaternion_algebra);
    s_prime_ideals := [];
    seen_ideals := [];

    if Type(s_prime_inputs) ne SeqEnum then
        error "s_prime_inputs must be a sequence of ideal-like inputs.";
    end if;

    for prime_data in s_prime_inputs do
        prime_ideal := normalize_prime_ideal(integer_ring, prime_data);

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


// Image of an order element in one reduction factor's ambient permutation
// group, under the same conventions used when the complement subgroups were
// computed: factors over a ramified quadratic extension go through the
// normalizer permutation machinery, split factors through the cached
// projective image.
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


// Image of an order element in the full ambient group of the complementary
// result: the block-diagonal product of its images across all reduction
// factors, with the same degree offsets used when the complement subgroups
// were built.  The complement subgroups live in this ambient group, so this
// is the membership test used by the lift search.
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
//
// For each S-prime P, A[P] holds one generator for each of the Norm(P)+1
// maximal right ideals of norm P.  Right-translating a generator by a T-unit
// leaves its right ideal unchanged while moving its reduction modulo C within
// a coset of the image of U_T, and complementarity makes exactly one translate
// land in the chosen complement subgroup.  This pins down the generator
// normalization behind the displayed presentations.
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

            generator := ord_primitive_integral_representative(order_data, generator);
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
//
// inverse_map pairs each a in A[P] with the unique abar in A[P] such that
// a*abar is a central scalar lying in P; the images of a and abar in Gamma
// are then mutually inverse.  sigma is the metacommutation permutation: for
// a in A[P] and b in A[Q] it finds the unique b' in A[Q] and a' in A[P] with
// a*b = b'*a' up to a central scalar.  Also records the torsion data:
// generators_torsion_free is false when some a is its own inverse partner
// (a^2 central), and square_torsion collects the pairs {a,b} whose square
// relation degenerates to (ab)^2 central.
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

        // The inverse partner of x is the y in A[P] with x*y a central scalar
        // lying in P: the images of x and y in Gamma are then mutually
        // inverse.  A self-paired x has x^2 central, giving a 2-torsion
        // generator, which clears generators_torsion_free.
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
                // b' in A[q] is characterized by membership in the right
                // ideal (x*y, q): it is the A[q]-factor of the
                // metacommutation of x*y, i.e. x*y lies in b'*O + q*O.
                target_ideal := rideal<quaternion_order | [x * y] cat prime_q_order_generators>;
                found_relation := false;

                for y_prime in a_q do
                    if not (y_prime in target_ideal) then
                        continue;
                    end if;

                    a_prime := ord_primitive_integral_representative(
                        order_data,
                        (quaternion_algebra!y_prime)^(-1) * quaternion_algebra!x * quaternion_algebra!y
                    );
                    a_prime_ideal := rideal<quaternion_order | a_prime>;

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

                            // If a' = x^-1 and b' = y^-1 the square relator
                            // x*y*inv(a')*inv(b') degenerates to (x*y)^2, so
                            // the word x*y is 2-torsion in Gamma (face
                            // torsion); record the unordered pair.
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


// Build Gamma from the inverse and square relations.
//
// Gamma is the quotient of the free group on the disjoint union of the A[P]
// by the inverse relators and the metacommutation square relators
// x_a x_b x_{a'}^-1 x_{b'}^-1.  With minimal_relations the square relators
// are reduced to one canonical representative per geometric square;
// otherwise every (a,b) vertex pair contributes its (redundant) relator.
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

    num_generators := &+[#a_representatives[p] : p in primes];

    free_group := FreeGroup(num_generators);
    index_map := AssociativeArray();

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
        for a in a_representatives[prime_p] do
            if a in inverse_seen then
                continue;
            end if;

            Append(~inverse_seen, a);
            Append(~inverse_seen, inverse_map[prime_p][a]);

            Append(~relations, free_group.index_map[a] * free_group.index_map[inverse_map[prime_p][a]]);
        end for;
    end for;

    for prime_pair in prime_pairs do
        pair_seq := SetToSequence(prime_pair);
        prime_p := pair_seq[1];
        prime_q := pair_seq[2];

        if minimal_relations then
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

    // With exactly two S-primes (one prime pair), return the pair's relation
    // dictionary directly rather than a one-key associative array; verify.m
    // consumes this flattened shape.  With three or more S-primes the result
    // stays keyed by prime pair.
    if (#prime_pairs eq 1) and minimal_relations then
        only_pair := SetToSequence(prime_pairs)[1];
        return gamma_group, minimal_square_relations[only_pair];
    end if;

    return gamma_group, minimal_square_relations;
end function;


procedure validate_presentation_complementary_result(complementary_result)
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
    complement_subgroup :
    minimal_relations := true,
    multiplier_pool := false
)
    order_data := complementary_result`localized_unit_group`order_data;
    s_prime_ideals := normalized_s_prime_inputs(
        order_data,
        complementary_result`modulus_ideal,
        s_prime_inputs
    );

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

    gamma_group,
    minimal_square_relations := compute_gamma_presentation(
        a_representatives,
        s_prime_ideals,
        sigma_map,
        inverse_map :
        minimal_relations := minimal_relations
    );

    presentation := rec<presentation_result_format |
        order_data := order_data,
        modulus_ideal := complementary_result`modulus_ideal,
        complement_index := complement_index,
        complement_subgroup := complement_subgroup,
        s_prime_ideals := s_prime_ideals,
        a_representatives := a_representatives,
        sigma_map := sigma_map,
        inverse_map := inverse_map,
        gamma_group := gamma_group,
        minimal_square_relations := minimal_square_relations,
        generators_torsion_free := generators_torsion_free,
        square_torsion := square_torsion
    >;

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
        complement_subgroup :
        minimal_relations := minimal_relations
    );
end function;




// Public wrapper for an already computed complementary result.
//
// NormalOnly restricts the choice to normal complement classes;
// ComplementSelector indexes the deterministically sorted complement list;
// MinimalRelations toggles reduction of the square relators to one per
// geometric square.  Print is validated for interface uniformity but the
// presentation builder emits no optional diagnostics; failures always print
// their witnesses.
function PresentationForComplement(
    complementary_result,
    s_prime_inputs :
    NormalOnly := false,
    ComplementSelector := 1,
    MinimalRelations := true,
    Print := 1
)
    return build_presentation_for_complementary_result(
        complementary_result,
        s_prime_inputs :
        normal_only := NormalOnly,
        complement_selector := ComplementSelector,
        minimal_relations := MinimalRelations,
        print_results := Print
    );
end function;


// Compute the exact complementary result at an arbitrary integral modulus and
// build its presentation.  Composite moduli are accepted.
function PresentationForModulus(
    order_data,
    modulus_ideal,
    s_prime_inputs :
    T := [],
    NormalOnly := false,
    ComplementSelector := 1,
    MinimalRelations := true,
    Print := 1
)
    Print := validate_print_level(Print);
    complementary_result := complementary_pairs_at_ideal(
        order_data,
        modulus_ideal :
        T := T,
        Print := Print
    );
    return PresentationForComplement(
        complementary_result,
        s_prime_inputs :
        NormalOnly := NormalOnly,
        ComplementSelector := ComplementSelector,
        MinimalRelations := MinimalRelations,
        Print := Print
    );
end function;
