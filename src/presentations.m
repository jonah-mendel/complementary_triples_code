// Presentations of Gamma_S(C, H) (Section 3.2). For each prime P in S, A[P] holds
// one generator for each of the N(P) + 1 maximal right ideals of norm P. The
// relations are a * abar = 1 and one metacommutation relation a b a'^-1 b'^-1
// per geometric square.
// Public: PresentationForComplement, CanonicalRelation.


PresentationFormat := recformat<
    complement_subgroup,
    s_prime_ideals,
    a_representatives,        // P -> A[P]
    inverse_map,              // P -> (a -> abar)
    sigma_map,                // <P, Q> -> (<a, b> -> <b', a'>) with a b = b' a' up to the center
    square_relations,         // one CanonicalRelation per geometric square
    gamma_group,
    generators_torsion_free,  // false if some a equals its own abar
    square_torsion            // the pairs {a, b} with (a b)^2 central
>;


// ---------------------------------------------------------------------------
// Square relations
// ---------------------------------------------------------------------------

// A relation word is [<P, a>, <Q, b>, <P, c>, <Q, d>], standing for a b c d = 1.
function invert_relation(inverse_map, word)
    return [<x[1], inverse_map[x[1]][x[2]]> : x in Reverse(word)];
end function;


// All words describing the same square: rotations and inverses, and for a
// commutator a b a^-1 b^-1 also those of a b^-1 a^-1 b.
function relation_class(inverse_map, word)
    words := [word];
    p, a := Explode(word[1]);
    q, b := Explode(word[2]);
    if inverse_map[p][a] eq word[3][2] and inverse_map[q][b] eq word[4][2] then
        Append(~words, [<p, a>, <q, inverse_map[q][b]>, <p, inverse_map[p][a]>, <q, b>]);
    end if;
    rotations := &cat[[w[i..4] cat w[1..i - 1] : i in [1..4]] : w in words];
    return rotations cat [invert_relation(inverse_map, w) : w in rotations];
end function;


// The word of a square that comes first as a printed string. Two words describe
// the same square exactly when they give the same result.
function CanonicalRelation(inverse_map, word)
    candidates := relation_class(inverse_map, word);
    keys := [Sprint(w) : w in candidates];
    _, i := Min(keys);
    return candidates[i];
end function;


// ---------------------------------------------------------------------------
// Generators and metacommutation
// ---------------------------------------------------------------------------

// For each prime P in S, a generator of each maximal right ideal of norm P,
// translated on the right by an element of Gamma_T so that its image in G_C lies
// in H. The images of the translates form a coset of the image of Gamma_T, and H
// is a complement, so exactly one translate lies in H.
function representatives_in_complement(result, H, s_primes)
    order_data := result`localized_unit_group`order_data;
    O := order_data`quaternion_order;
    multipliers := [NormalizerRepresentative(order_data, g) : g in result`localized_unit_group`subgroup];

    a_representatives := AssociativeArray();
    for P in s_primes do
        a_representatives[P] := [];
        for I in MaximalRightIdeals(O, P) do
            is_principal, generator := IsPrincipal(I);
            assert is_principal;
            generator := PrimitiveRepresentative(order_data, generator);
            lifts := [generator * m : m in multipliers | ReductionImage(result, generator * m) in H];
            assert #lifts ge 1;
            Append(~a_representatives[P], O!lifts[1]);
        end for;
        assert #a_representatives[P] eq Norm(P) + 1;
    end for;
    return a_representatives;
end function;


// abar is the element of A[P] with a * abar a scalar in P. For a in A[P] and b
// in A[Q], b' is the element of A[Q] with a b in b' O + Q O, and a' is the
// element of A[P] generating the same right ideal as b'^-1 a b.
procedure metacommutation(order_data, a_representatives, s_primes, ~inverse_map,
                          ~sigma_map, ~generators_torsion_free, ~square_torsion)
    algebra := order_data`quaternion_algebra;
    O := order_data`quaternion_order;
    scalar_in := function(z, P)
        is_scalar, s := IsScalar(z);
        return is_scalar and s in P;
    end function;
    inverse_map := AssociativeArray();
    generators_torsion_free := true;
    for P in s_primes do
        inverse_map[P] := AssociativeArray();
        for x in a_representatives[P] do
            partners := [y : y in a_representatives[P] | scalar_in(x * y, P)];
            assert #partners eq 1;
            inverse_map[P][x] := partners[1];
            if partners[1] eq x then
                generators_torsion_free := false;
            end if;
        end for;
    end for;

    sigma_map := AssociativeArray();
    square_torsion := {};
    for P in s_primes do
        for Q in [Q : Q in s_primes | Q ne P] do
            sigma_map[<P, Q>] := AssociativeArray();
            Q_generators := [O!(algebra!(order_data`integer_ring!g)) : g in Generators(Q)];
            for x in a_representatives[P] do
                for y in a_representatives[Q] do
                    target := rideal<O | [x * y] cat Q_generators>;
                    y_prime := [z : z in a_representatives[Q] | z in target][1];
                    a_prime := PrimitiveRepresentative(order_data, (algebra!y_prime)^-1 * x * y);
                    x_prime := [z : z in a_representatives[P] | rideal<O | z> eq rideal<O | a_prime>][1];
                    assert IsScalar(algebra!(x * y) * (algebra!(y_prime * x_prime))^-1);
                    sigma_map[<P, Q>][<x, y>] := <y_prime, x_prime>;
                    // If a' = abar and b' = bbar, the relation reads (a b)^2 = 1.
                    if x eq inverse_map[P][x_prime] and y eq inverse_map[Q][y_prime] then
                        Include(~square_torsion, {x, y});
                    end if;
                end for;
            end for;
        end for;
    end for;

    // Check that sigma_{Q,P} undoes sigma_{P,Q}, and that sigma commutes with
    // replacing each generator by its abar.
    for key in Keys(sigma_map) do
        P, Q := Explode(key);
        for xy in Keys(sigma_map[key]) do
            y_prime, x_prime := Explode(sigma_map[key][xy]);
            assert sigma_map[<Q, P>][<y_prime, x_prime>] eq xy;
            assert sigma_map[<Q, P>][<inverse_map[Q][xy[2]], inverse_map[P][xy[1]]>] eq
                   <inverse_map[P][x_prime], inverse_map[Q][y_prime]>;
        end for;
    end for;
end procedure;


// ---------------------------------------------------------------------------
// Presentation
// ---------------------------------------------------------------------------

// The presentation of Gamma_S(C, H) for an injective result of ReductionData and
// a set S of distinct primes, coprime to C and unramified in B. H is
// result`complement_classes[ComplementSelector], or with NormalOnly,
// result`normal_complement_classes[ComplementSelector].
function PresentationForComplement(result, s_prime_inputs :
                                   NormalOnly := false, ComplementSelector := 1)
    order_data := result`localized_unit_group`order_data;
    R := order_data`integer_ring;
    assert result`injective;
    s_primes := [ideal<R | Generators(P)> : P in s_prime_inputs];
    assert #Set(s_primes) eq #s_primes;
    assert forall{P : P in s_primes | Valuation(result`modulus_ideal, P) eq 0 and
                                      not is_ramified(order_data, P)};

    H := (NormalOnly select result`normal_complement_classes else result`complement_classes)[ComplementSelector];

    a_representatives := representatives_in_complement(result, H, s_primes);
    inverse_map := false;
    sigma_map := false;
    torsion_free := false;
    square_torsion := false;
    metacommutation(order_data, a_representatives, s_primes, ~inverse_map,
                    ~sigma_map, ~torsion_free, ~square_torsion);

    relations := [];
    for pair in [<s_primes[i], s_primes[j]> : j in [i + 1..#s_primes], i in [1..#s_primes]] do
        P, Q := Explode(pair);
        for xy in Keys(sigma_map[pair]) do
            y_prime, x_prime := Explode(sigma_map[pair][xy]);
            word := [<P, xy[1]>, <Q, xy[2]>, <P, inverse_map[P][x_prime]>, <Q, inverse_map[Q][y_prime]>];
            Include(~relations, CanonicalRelation(inverse_map, word));
        end for;
    end for;

    generators := &cat[a_representatives[P] : P in s_primes];
    F := FreeGroup(#generators);
    letters := [F.i : i in [1..#generators]];
    letter := func<x | letters[Index(generators, x)]>;
    relators := [letter(x) * letter(inverse_map[P][x]) : x in a_representatives[P], P in s_primes]
                cat [&*[letter(x[2]) : x in word] : word in relations];

    return rec<PresentationFormat |
        complement_subgroup := H,
        s_prime_ideals := s_primes,
        a_representatives := a_representatives,
        inverse_map := inverse_map,
        sigma_map := sigma_map,
        square_relations := relations,
        gamma_group := quo<F | relators>,
        generators_torsion_free := torsion_free,
        square_torsion := square_torsion
    >;
end function;
