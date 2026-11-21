// Projective unit groups G = (O/P^k O)^*/(R/P^k)^* as permutation groups.
// Public: FiniteQuotient, ResidueRing, ReducedAlgebra, ReduceElement,
// QuotientImage, QuotientRepresentative, NormalizerImage.
//
// Split P, k = 1, O locally maximal: G = PGL(2, F) acting on P^1(F).
// Otherwise G acts on itself by right multiplication. An element of G is the
// class of a unit modulo scalars; it is labeled by the unit's coordinate vector,
// scaled so that its first unit coordinate is 1.
// In both models x -> QuotientImage(Q, x) is a homomorphism.
//
// At a ramified P where the Eichler order O is maximal, Q also holds
// W = <G, t> with t^-1 g t = a^-1 g a and t^2 = [a^2], where a generates the
// two-sided prime of O above P. NormalizerImage maps elements of N(O) into W.


QuotientFormat := recformat<
    order_data,
    prime_ideal,
    modulus_ideal,
    base_ring,          // R/P^k
    reduction_map,      // R -> R/P^k
    algebra,            // O/P^k O, in the principal basis
    norm_terms,         // the norm form reduced modulo P^k
    natural,            // true for the PGL(2, F) model
    group,              // G
    representatives,    // regular model: class representatives; the identity is first
    index_of,           // regular model: normalized coordinates -> index
    associative,        // PGL model: O/P O as an associative algebra,
    split_map,          //   its isomorphism to M_2(F),
    split_basis,        //   the images of the basis as rows,
    points,             //   and the points of P^1(F)
    point_index,
    extension,          // W, or false
    a,
    t
>;


// R/A for a prime power A, with the reduction R -> R/A.
function ResidueRing(order_data, modulus_ideal)
    if Factorization(modulus_ideal)[1][2] eq 1 then
        return ResidueClassField(modulus_ideal);
    end if;
    return quo<order_data`integer_ring | modulus_ideal>;
end function;


// O/A O for a prime power A, with R/A and the reduction R -> R/A.
function ReducedAlgebra(order_data, modulus_ideal)
    base_ring, reduction_map := ResidueRing(order_data, modulus_ideal);
    basis := order_data`principal_basis;
    table := [[reduction_map(c) : c in OrderCoordinates(order_data, basis[i] * basis[j])]
              : i, j in [1..4]];
    return Algebra<base_ring, 4 | table>, base_ring, reduction_map;
end function;


// Divide a unit's coordinates by the first coordinate that is a unit. Two units
// give the same result exactly when they differ by a scalar.
function normalized(coordinates)
    for c in coordinates do
        if IsUnit(c) then
            inverse := c^-1;
            return [inverse * x : x in coordinates];
        end if;
    end for;
    error "Not a unit.";
end function;


function reduced_norm(Q, y)
    x := Eltseq(y);
    return &+[term[3] * x[term[1]] * x[term[2]] : term in Q`norm_terms];
end function;


// Reduce an element of O modulo P^k.
function ReduceElement(Q, x)
    R := Q`order_data`integer_ring;
    return Q`algebra![Q`reduction_map(R!c) : c in OrderCoordinates(Q`order_data, x)];
end function;


// The permutation of the points of P^1(F), or of the class representatives,
// given by the reduced unit y.
function permutation_of_reduced(Q, y)
    if Q`natural then
        matrix := Q`split_map(Q`associative!y);
        return Q`group![Q`point_index[normalized(Eltseq(p * matrix))] : p in Q`points];
    end if;
    return Sym(#Q`representatives)![Q`index_of[normalized(Eltseq(r * y))] : r in Q`representatives];
end function;


// The element of G represented by x in O. A reduced element is a unit exactly
// when its reduced norm is.
function QuotientImage(Q, x)
    y := ReduceElement(Q, x);
    if not IsUnit(reduced_norm(Q, y)) then
        error Sprintf("The element does not reduce to a unit modulo %o.", Q`modulus_ideal);
    end if;
    return Q`group!permutation_of_reduced(Q, y);
end function;


// A reduced unit representing g in G.
function QuotientRepresentative(Q, g)
    if not Q`natural then
        return Q`representatives[1^g];
    end if;

    // Recover the matrix, up to scalars, from the images of [1,0], [0,1], [1,1].
    F := Q`base_ring;
    images := [Q`points[Q`point_index[[F!c : c in v]]^g] : v in [[1, 0], [0, 1], [1, 1]]];
    u, v, w := Explode(images);
    scale := -(u[1] * w[2] - u[2] * w[1]) / (v[1] * w[2] - v[2] * w[1]);
    _, coordinates := IsConsistent(Q`split_basis, Vector(F, Eltseq(u) cat Eltseq(scale * v)));
    return Q`algebra!Eltseq(coordinates);
end function;


function lift_to_extension(g, n)
    return Sym(2 * n)![i le n select i^g else n + (i - n)^g : i in [1..2 * n]];
end function;


// The image in W of a primitive representative x of an element of N(O).
function NormalizerImage(Q, x)
    n := Degree(Q`group);
    y := ReduceElement(Q, x);
    if IsUnit(reduced_norm(Q, y)) then
        return Q`extension!lift_to_extension(permutation_of_reduced(Q, y), n);
    end if;
    unit_part := PrimitiveRepresentative(Q`order_data, x * Q`a^-1);
    return Q`extension!(lift_to_extension(QuotientImage(Q, unit_part), n) * Q`t);
end function;


procedure build_natural_model(~Q)
    A := AssociativeAlgebra(Q`algebra);
    ideal_x := [I : I in MinimalRightIdeals(A) | Dimension(I) eq 2][1];
    _, split_map := MatrixAlgebra(A, ideal_x : Side := "Right");
    assert forall{<i, j> : i, j in [1..4] |
                  split_map(A.i * A.j) eq split_map(A.i) * split_map(A.j)};
    Q`associative := A;
    Q`split_map := split_map;
    Q`split_basis := Matrix(Q`base_ring, 4, 4, &cat[Eltseq(split_map(A.i)) : i in [1..4]]);
    Q`group, Q`points := PGL(2, Q`base_ring);
    Q`point_index := AssociativeArray();
    for i in [1..#Q`points] do
        Q`point_index[normalized(Eltseq(Q`points[i]))] := i;
    end for;
end procedure;


procedure build_regular_model(~Q)
    B := Q`base_ring;
    elements := [b : b in B];
    nonunits := [b : b in elements | not IsUnit(b)];
    identity := normalized(Eltseq(ReduceElement(Q, Q`order_data`quaternion_algebra!1)));

    // The normalized unit vectors, with the identity first.
    classes := [identity];
    for pivot in [1..4] do
        ranges := [i lt pivot select nonunits else i eq pivot select [B!1] else elements
                   : i in [1..4]];
        for x in [[x1, x2, x3, x4] : x1 in ranges[1], x2 in ranges[2],
                                     x3 in ranges[3], x4 in ranges[4]] do
            if x ne identity and IsUnit(reduced_norm(Q, x)) then
                Append(~classes, x);
            end if;
        end for;
    end for;
    n := #classes;
    Q`representatives := [Q`algebra!x : x in classes];
    Q`index_of := AssociativeArray();
    for i in [1..n] do
        Q`index_of[classes[i]] := i;
    end for;

    // Add generators until they generate all of G. The candidates are taken
    // with a fixed stride through the list, so that a few of them usually suffice.
    stride := NextPrime(n div 3);
    while Gcd(stride, n) ne 1 do
        stride := NextPrime(stride);
    end while;
    generators := [];
    G := sub<Sym(n) | >;
    for j in [1..n] do
        if #G eq n then
            break;
        end if;
        g := permutation_of_reduced(Q, Q`representatives[(j * stride) mod n + 1]);
        if g notin G then
            Append(~generators, g);
            G := sub<Sym(n) | generators>;
        end if;
    end for;
    Q`group := G;
end procedure;


// W acts by right multiplication on G (points 1..n) and t G (points n+1..2n).
// Right multiplication by t sends c to t (a^-1 c a) and t c to [a^2] (a^-1 c a).
procedure build_extension(~Q, a)
    order_data := Q`order_data;
    conjugates := [ReduceElement(Q, a^-1 * b * a) : b in order_data`principal_basis];
    square := ReduceElement(Q, PrimitiveRepresentative(order_data, a^2));

    n := #Q`group;
    t_images := [0 : i in [1..2 * n]];
    for i in [1..n] do
        c := &+[Eltseq(Q`representatives[i])[j] * conjugates[j] : j in [1..4]];
        t_images[i] := n + Q`index_of[normalized(Eltseq(c))];
        t_images[n + i] := Q`index_of[normalized(Eltseq(square * c))];
    end for;
    Q`a := a;
    Q`t := Sym(2 * n)!t_images;
    Q`extension := sub<Sym(2 * n) |
        [lift_to_extension(g, n) : g in Generators(Q`group)] cat [Q`t]>;
    assert #Q`extension eq 2 * n;
end procedure;


// The record Q for G = (O/P^k O)^*/(R/P^k)^*, and for W when it is defined.
// When O is maximal at P, the order of G is checked against its formula.
function FiniteQuotient(order_data, prime_ideal, k)
    modulus_ideal := prime_ideal^k;
    algebra, base_ring, reduction_map := ReducedAlgebra(order_data, modulus_ideal);
    _, norm_terms := TraceNormForms(order_data);
    Q := rec<QuotientFormat |
        order_data := order_data,
        prime_ideal := prime_ideal,
        modulus_ideal := modulus_ideal,
        base_ring := base_ring,
        reduction_map := reduction_map,
        algebra := algebra,
        norm_terms := [<term[1], term[2], reduction_map(term[3])> : term in norm_terms],
        extension := false
    >;

    ramified := is_ramified(order_data, prime_ideal);
    maximal := is_locally_maximal(order_data, prime_ideal);
    Q`natural := k eq 1 and maximal and not ramified;
    if Q`natural then
        build_natural_model(~Q);
    else
        build_regular_model(~Q);
    end if;

    if maximal then
        q := Norm(prime_ideal);
        expected := ramified select q^(3*k - 1) * (q + 1) else q^(3*k - 2) * (q^2 - 1);
        assert #Q`group eq expected;
        if ramified and order_data`order_type ge 2 then
            a := TwoSidedGenerator(order_data, prime_ideal);
            if a cmpne false then
                build_extension(~Q, a);
            end if;
        end if;
    end if;
    return Q;
end function;
