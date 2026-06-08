// ============================================================================
// Sigma-relation validation and minimization utilities.
//
// These helpers validate metacommutation data and build canonical square-
// relation representatives for the presentation pipeline.
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
