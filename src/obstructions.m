// Torsion obstruction sets Theta and the stabilized modulus e(A) (Section 7.1).
//
// Theta_A(Z) is the set of square classes in Delta_A = (R/A)^*/squares of the
// reduced norms of the trace-zero elements of Z.
// Public: StabilizedModulus, ObstructionAtSubgroup, ObstructionAtModulus,
// ComplementObstructionApplies, TorsionObstruction, DiscriminantObstruction.


ObstructionFormat := recformat<
    applicable,
    modulus_ideal,
    delta_size,
    theta_size,
    theta_representatives,   // one unit residue in each class of Theta; empty for DiscriminantObstruction
    theta_contains_one
>;


// e(A) = product_{p | A} p^max(2 v_p(2) + 1, v_p(A)), from the definition after Lemma 47.
function StabilizedModulus(A)
    R := Order(A);
    E := 1 * R;
    for factor in Factorization(A) do
        E *:= factor[1]^Maximum(factor[2], 2 * Valuation(2 * R, factor[1]) + 1);
    end for;
    return E;
end function;


// The data for evaluating Theta modulo the prime power A. found collects the
// classes in Delta_A seen so far.
ThetaFormat := recformat<
    base_ring, reduction_map, trace, norm_terms,
    delta, delta_map, representative, found
>;


function theta_data(order_data, A)
    B, reduction_map := ResidueRing(order_data, A);
    trace, norm_terms := TraceNormForms(order_data);
    U, unit_map := UnitGroup(B);
    D, quotient_map := quo<U | [2 * U.i : i in [1..Ngens(U)]] cat [Zero(U)]>;
    return rec<ThetaFormat |
        base_ring := B,
        reduction_map := reduction_map,
        trace := [reduction_map(t) : t in trace],
        norm_terms := [<x[1], x[2], reduction_map(x[3])> : x in norm_terms],
        delta := D,
        delta_map := map<B -> D | b :-> quotient_map(b @@ unit_map)>,
        representative := map<D -> B | c :-> unit_map(c @@ quotient_map)>,
        found := {D | }
    >;
end function;


function trace_value(data, x)
    return &+[data`trace[i] * x[i] : i in [1..4]];
end function;


function norm_value(data, x)
    return &+[t[3] * x[t[1]] * x[t[2]] : t in data`norm_terms];
end function;


function theta_complete(data)
    return #data`found eq #data`delta;
end function;


procedure record_tuple(~data, x)
    if trace_value(data, x) eq 0 then
        n := norm_value(data, x);
        if IsUnit(n) then
            Include(~data`found, data`delta_map(n));
        end if;
    end if;
end procedure;


// Record the trace-zero tuples with x_i in ranges[i]. The trace equation is
// linear, so pair (x1, x2) with the (x3, x4) whose partial trace cancels it.
procedure scan_trace_zero(~data, ranges)
    tails := AssociativeArray();
    for x3 in ranges[3] do
        for x4 in ranges[4] do
            key := data`trace[3] * x3 + data`trace[4] * x4;
            tails[key] := (IsDefined(tails, key) select tails[key] else []) cat [<x3, x4>];
        end for;
    end for;
    for x1 in ranges[1] do
        for x2 in ranges[2] do
            key := -(data`trace[1] * x1 + data`trace[2] * x2);
            if IsDefined(tails, key) then
                for tail in tails[key] do
                    record_tuple(~data, [x1, x2, tail[1], tail[2]]);
                    if theta_complete(data) then
                        return;
                    end if;
                end for;
            end if;
        end for;
    end for;
end procedure;


function obstruction_result(data, A)
    return rec<ObstructionFormat |
        applicable := true,
        modulus_ideal := A,
        delta_size := #data`delta,
        theta_size := #data`found,
        theta_representatives := [data`representative(c) : c in data`found],
        theta_contains_one := Zero(data`delta) in data`found
    >;
end function;


// Theta_A(H) for a subgroup H of the group G of FiniteQuotient(order_data, P, k).
function ObstructionAtSubgroup(Q, H)
    data := theta_data(Q`order_data, Q`modulus_ideal);
    for g in H do
        record_tuple(~data, ChangeUniverse(Eltseq(QuotientRepresentative(Q, g)), data`base_ring));
    end for;
    return obstruction_result(data, Q`modulus_ideal);
end function;


// Theta_A of all of G[A], for a prime power A = p^k. If p is ramified, O is
// maximal at p and k >= 2 v_p(2) + 1, then Theta_A is Delta_A minus the class of
// -1. In the local division algebra, a unit d is the norm of a trace-zero unit
// exactly when -d is not a square. For such k, a unit is a square in K_p exactly
// when it is a square modulo A, so the condition can be read modulo A.
// Otherwise the function scans all of (R/A)^4.
function ObstructionAtModulus(order_data, A)
    data := theta_data(order_data, A);
    p, k := Explode(Factorization(A)[1]);
    if is_ramified(order_data, p) and is_locally_maximal(order_data, p) and
       k ge 2 * Valuation(2 * order_data`integer_ring, p) + 1 then
        minus_one := data`delta_map(data`base_ring!(-1));
        data`found := {c : c in data`delta | c ne minus_one};
    else
        elements := [b : b in data`base_ring];
        scan_trace_zero(~data, [elements : i in [1..4]]);
    end if;
    return obstruction_result(data, A);
end function;


// ---------------------------------------------------------------------------
// Complements and the discriminant
// ---------------------------------------------------------------------------

// The complement obstruction is defined when C is coprime to T. All such
// complementary ideals in the classification are prime powers.
function ComplementObstructionApplies(result)
    support := [f[1] : f in Factorization(result`modulus_ideal)];
    if exists{p : p in support | p in result`localized_unit_group`ramified_subset} then
        return false;
    end if;
    if #support ne 1 then
        error "A composite C coprime to T is not supported.";
    end if;
    return true;
end function;


// Theta_{e(C)}(H_tilde) for the complement H = result`complement_classes[i],
// where H_tilde is the preimage of H under G[e(C)] -> G[C].
function TorsionObstruction(result, i)
    assert result`injective and ComplementObstructionApplies(result);
    Q := result`factors[1]`quotient;
    H := result`complement_classes[i];
    C := result`modulus_ideal;
    E := StabilizedModulus(C);
    if E eq C then
        return ObstructionAtSubgroup(Q, H);
    end if;

    // Every coordinate tuple modulo e(C) above a representative of H lies in H_tilde.
    data := theta_data(Q`order_data, E);
    R := Q`order_data`integer_ring;
    fibers := AssociativeArray();
    for b in data`base_ring do
        c := Q`reduction_map(R!(b @@ data`reduction_map));
        fibers[c] := (IsDefined(fibers, c) select fibers[c] else []) cat [b];
    end for;
    for g in H do
        scan_trace_zero(~data, [fibers[c] : c in Eltseq(QuotientRepresentative(Q, g))]);
        if theta_complete(data) then
            break;
        end if;
    end for;
    return obstruction_result(data, E);
end function;


// Theta at e(D) for the finite discriminant D of the algebra, as the product of
// its local factors. Not applicable when D = (1).
function DiscriminantObstruction(order_data)
    E := StabilizedModulus(Discriminant(order_data`quaternion_algebra));
    factors := [ObstructionAtModulus(order_data, f[1]^f[2]) : f in Factorization(E)];
    if #factors eq 0 then
        return rec<ObstructionFormat | applicable := false, modulus_ideal := E, delta_size := 0,
                   theta_size := 0, theta_representatives := [], theta_contains_one := false>;
    end if;
    return rec<ObstructionFormat |
        applicable := true,
        modulus_ideal := E,
        delta_size := &*[f`delta_size : f in factors],
        theta_size := &*[f`theta_size : f in factors],
        theta_representatives := [],
        theta_contains_one := &and[f`theta_contains_one : f in factors]
    >;
end function;
