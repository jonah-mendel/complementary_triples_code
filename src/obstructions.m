// Exact torsion obstructions from Section 7 of the paper.
//
// This module assumes that orders.m, quotients.m, and classification.m have
// already been loaded.  It deliberately contains no scheduling or reporting
// machinery: every requested obstruction is computed exactly or raises an
// error.
//
// Public interface:
//   StabilizedModulus(A)
//   ObstructionAtSubgroup(group_model, subgroup)
//   ObstructionAtModulus(order_data, A)
//   ComplementObstructionApplies(complementary_result)
//   LiftComplement(complementary_result, complement_index)
//   TorsionObstruction(complementary_result, complement_index)
//   DiscriminantObstruction(order_data)


ObstructionFormFormat := recformat<
    order_data,
    modulus_ideal,
    reduced_base_ring,
    reduction_map,
    trace_coefficients,
    norm_terms
>;


SquareClassFormat := recformat<
    unit_group,
    unit_map,
    square_subgroup,
    delta_group,
    delta_map,
    delta_elements,
    representatives
>;


// The same result format is used for a local calculation and for the product
// of the local factors of a discriminant.  For a product, the exact local
// representatives live in local_factors; no artificial common residue ring is
// introduced.
TorsionObstructionFormat := recformat<
    kind,
    applicable,
    order_data,
    source_modulus,
    modulus_ideal,
    prime_ideal,
    prime_power_exponent,
    local_factors,
    delta_size,
    delta_representatives,
    theta_size,
    theta_representatives,
    theta_contains_one
>;


// This is an exact implicit model of
//     H_tilde = G[e(C)] -> G[C] inverse image of H.
// Its elements are represented by coordinate tuples modulo e(C) whose
// reductions lie in one of source_tuples.
LiftedComplementFormat := recformat<
    complementary_result,
    complement_index,
    source_modulus,
    modulus_ideal,
    prime_ideal,
    source_exponent,
    target_exponent,
    source_group_model,
    source_subgroup,
    source_tuples,
    target_form,
    scalar_fibers
>;


// ---------------------------------------------------------------------------
// Small deterministic helpers
// ---------------------------------------------------------------------------

function obs_values_sorted_by_key(lookup)
    keys := [key : key in Keys(lookup)];
    Sort(~keys);
    return [lookup[key] : key in keys];
end function;


function obs_tuple(tuple_x, target_ring)
    coordinates := Type(tuple_x) eq SeqEnum select tuple_x else Eltseq(tuple_x);
    if #coordinates ne 4 then
        error "A reduced quaternion must have four coordinates.";
    end if;
    return [target_ring!coordinate : coordinate in coordinates];
end function;


function obs_integral_coefficient(integer_ring, coefficient, label)
    if not (coefficient in integer_ring) then
        error Sprintf("%o is not integral.", label);
    end if;
    return integer_ring!coefficient;
end function;


// ---------------------------------------------------------------------------
// Stabilized modulus and reduced trace/norm forms
// ---------------------------------------------------------------------------

// Section 7 defines
//   e(A) = product_{p | A} p^max(2 v_p(2) + 1, v_p(A)).
// The factorization of A is the only source of exponents here.
function StabilizedModulus(modulus_ideal)
    integer_ring := Order(modulus_ideal);
    stabilized := 1 * integer_ring;

    for factor in Factorization(modulus_ideal) do
        prime_ideal := factor[1];
        exponent := Maximum(
            factor[2],
            2 * Valuation(2 * integer_ring, prime_ideal) + 1
        );
        stabilized *:= prime_ideal^exponent;
    end for;

    return stabilized;
end function;


// Reduce the order's trace and norm modulo A to forms on coordinates: for
// x = sum x_i b_i in the principal basis, Trd(x) = sum trace_coefficients[i] x_i
// and Nrd(x) = sum_{i <= j} c_ij x_i x_j, with c_ii = Nrd(b_i) and the
// off-diagonal c_ij = Trd(b_i conj(b_j)).  Every obstruction scan evaluates
// these two forms on coordinate tuples instead of touching algebra elements.
function obs_reduced_forms(order_data, modulus_ideal)
    reduced_algebra, reduced_base_ring, reduction_map :=
        build_reduced_algebra(order_data, modulus_ideal);
    integer_ring := order_data`integer_ring;
    algebra := order_data`quaternion_algebra;
    basis := order_data`principal_basis;
    trace_coefficients := [];
    norm_terms := [];

    for i in [1..4] do
        basis_element := algebra!basis[i];
        trace_coefficient := obs_integral_coefficient(
            integer_ring,
            Trace(basis_element),
            Sprintf("trace coefficient %o", i)
        );
        norm_coefficient := obs_integral_coefficient(
            integer_ring,
            Norm(basis_element),
            Sprintf("norm coefficient (%o,%o)", i, i)
        );
        Append(~trace_coefficients, reduction_map(trace_coefficient));
        if norm_coefficient ne 0 then
            Append(~norm_terms, <i, i, reduction_map(norm_coefficient)>);
        end if;
    end for;

    for i in [1..4] do
        for j in [i + 1..4] do
            coefficient := obs_integral_coefficient(
                integer_ring,
                Trace((algebra!basis[i]) * Conjugate(algebra!basis[j])),
                Sprintf("norm coefficient (%o,%o)", i, j)
            );
            if coefficient ne 0 then
                Append(~norm_terms, <i, j, reduction_map(coefficient)>);
            end if;
        end for;
    end for;

    return rec<ObstructionFormFormat |
        order_data := order_data,
        modulus_ideal := modulus_ideal,
        reduced_base_ring := reduced_base_ring,
        reduction_map := reduction_map,
        trace_coefficients := trace_coefficients,
        norm_terms := norm_terms
    >;
end function;


function obs_trace_and_norm(form_data, tuple_x)
    ring := form_data`reduced_base_ring;
    coordinates := obs_tuple(tuple_x, ring);
    trace_value := ring!0;
    norm_value := ring!0;

    for i in [1..4] do
        trace_value +:= form_data`trace_coefficients[i] * coordinates[i];
    end for;
    for term in form_data`norm_terms do
        norm_value +:= term[3] * coordinates[term[1]] * coordinates[term[2]];
    end for;

    return trace_value, norm_value;
end function;


// ---------------------------------------------------------------------------
// Square classes and local obstruction sets
// ---------------------------------------------------------------------------

// Compute Delta_A = (R/A)^* modulo squares, the group of unit square
// classes in which every Theta lives, together with one deterministic
// residue representative per class.  Theta sets are recorded, compared,
// and serialized through these representatives.
function obs_square_classes(reduced_base_ring)
    unit_group, unit_map := UnitGroup(reduced_base_ring);
    square_generators := [2 * unit_group.i : i in [1..Ngens(unit_group)]];
    square_subgroup := #square_generators eq 0
        select sub<unit_group | Identity(unit_group)>
        else sub<unit_group | square_generators>;
    delta_group, delta_map := quo<unit_group | square_subgroup>;
    element_lookup := AssociativeArray();
    representative_lookup := AssociativeArray();

    // Select a deterministic residue representative for every square class.
    for unit in unit_group do
        delta_element := delta_map(unit);
        representative := unit_map(unit);
        delta_key := Sprint(Eltseq(delta_element));
        if not IsDefined(representative_lookup, delta_key) or
           Sprint(representative) lt Sprint(representative_lookup[delta_key]) then
            element_lookup[delta_key] := delta_group!delta_element;
            representative_lookup[delta_key] := representative;
        end if;
    end for;

    keys := [key : key in Keys(representative_lookup)];
    Sort(~keys);
    return rec<SquareClassFormat |
        unit_group := unit_group,
        unit_map := unit_map,
        square_subgroup := square_subgroup,
        delta_group := delta_group,
        delta_map := delta_map,
        delta_elements := [element_lookup[key] : key in keys],
        representatives := [representative_lookup[key] : key in keys]
    >;
end function;


function obs_representative(delta_element, square_classes)
    target := square_classes`delta_group!delta_element;
    for i in [1..#square_classes`delta_elements] do
        if square_classes`delta_elements[i] eq target then
            return square_classes`representatives[i];
        end if;
    end for;
    error "A square class has no canonical representative.";
end function;


procedure obs_record_unit_norm_class(
    square_classes,
    norm_value,
    ~theta_lookup
)
    if not IsUnit(norm_value) then
        error "The supplied reduced norm is not a unit.";
    end if;

    residue_unit := norm_value @@ square_classes`unit_map;
    delta_element := square_classes`delta_map(residue_unit);
    representative := obs_representative(delta_element, square_classes);
    theta_lookup[Sprint(representative)] := representative;
end procedure;


procedure obs_record_trace_zero_norm(
    form_data,
    square_classes,
    tuple_x,
    ~theta_lookup
)
    trace_value, norm_value := obs_trace_and_norm(form_data, tuple_x);
    if trace_value ne form_data`reduced_base_ring!0 then
        return;
    end if;
    if not IsUnit(norm_value) then
        error "A trace-zero projective unit has nonunit reduced norm.";
    end if;
    obs_record_unit_norm_class(square_classes, norm_value, ~theta_lookup);
end procedure;


procedure obs_scan_trace_zero_tuples(
    form_data,
    square_classes,
    coordinate_fibers,
    fibers_are_units,
    ~theta_lookup
)
    trace_coefficients := form_data`trace_coefficients;
    tail_lookup := AssociativeArray();

    // Meet in the middle on the linear trace equation.  For the ambient
    // obstruction the four fibers are the whole residue ring; for a lifted
    // complement they are the exact coordinate fibers above a known unit.
    for x3 in coordinate_fibers[3] do
        for x4 in coordinate_fibers[4] do
            tail_trace := trace_coefficients[3] * x3 + trace_coefficients[4] * x4;
            key := Sprint(Eltseq(tail_trace));
            pairs := IsDefined(tail_lookup, key) select tail_lookup[key] else [];
            Append(~pairs, <x3, x4>);
            tail_lookup[key] := pairs;
        end for;
    end for;

    for x1 in coordinate_fibers[1] do
        for x2 in coordinate_fibers[2] do
            head_trace := trace_coefficients[1] * x1 + trace_coefficients[2] * x2;
            key := Sprint(Eltseq(-head_trace));
            if not IsDefined(tail_lookup, key) then
                continue;
            end if;

            for tail_pair in tail_lookup[key] do
                tuple_x := [x1, x2, tail_pair[1], tail_pair[2]];
                trace_value, norm_value := obs_trace_and_norm(form_data, tuple_x);
                if trace_value ne form_data`reduced_base_ring!0 then
                    error "The trace-zero fiber scan produced a nonzero trace.";
                end if;
                if not IsUnit(norm_value) then
                    if fibers_are_units then
                        error "A lift of a projective unit has nonunit reduced norm.";
                    end if;
                    continue;
                end if;
                obs_record_unit_norm_class(
                    square_classes,
                    norm_value,
                    ~theta_lookup
                );
                if #Keys(theta_lookup) eq #square_classes`delta_group then
                    return;
                end if;
            end for;
        end for;
    end for;
end procedure;


// At a ramified prime where the order is maximal, the stabilized Section 7
// exponent makes the ambient obstruction especially simple:
//
//     Theta_(p^k) = Delta_(p^k) \ {[-1]}.
//
// Indeed, k >= 2 v_p(2) + 1 lets every trace-zero residue representative be
// replaced by an integral trace-zero lift without changing its norm square
// class. In the local quaternion division algebra, a unit d is the norm of a
// trace-zero unit exactly when -d is not a square. Thus this is an exact local
// formula, not a bound or an early-exit criterion.
procedure obs_ramified_maximal_theta(
    form_data,
    square_classes,
    ~theta_lookup
)
    minus_one := form_data`reduction_map(
        form_data`order_data`integer_ring!(-1)
    );
    minus_one_class := square_classes`delta_map(
        minus_one @@ square_classes`unit_map
    );

    for i in [1..#square_classes`delta_elements] do
        if square_classes`delta_elements[i] ne minus_one_class then
            representative := square_classes`representatives[i];
            theta_lookup[Sprint(representative)] := representative;
        end if;
    end for;
end procedure;


function obs_local_result(
    kind,
    order_data,
    source_modulus,
    modulus_ideal,
    form_data,
    square_classes,
    theta_lookup
)
    factorization := Factorization(modulus_ideal);
    if #factorization ne 1 then
        error "A local obstruction modulus must be a prime power.";
    end if;

    identity_representative := obs_representative(
        Identity(square_classes`delta_group),
        square_classes
    );
    theta_representatives := obs_values_sorted_by_key(theta_lookup);

    return rec<TorsionObstructionFormat |
        kind := kind,
        applicable := true,
        order_data := order_data,
        source_modulus := source_modulus,
        modulus_ideal := modulus_ideal,
        prime_ideal := factorization[1][1],
        prime_power_exponent := factorization[1][2],
        local_factors := [],
        delta_size := #square_classes`delta_group,
        delta_representatives := square_classes`representatives,
        theta_size := #theta_representatives,
        theta_representatives := theta_representatives,
        theta_contains_one := IsDefined(theta_lookup, Sprint(identity_representative))
    >;
end function;


function obs_from_tuples(kind, group_model, source_modulus, source_tuples)
    form_data := obs_reduced_forms(
        group_model`order_data,
        group_model`modulus_ideal
    );
    square_classes := obs_square_classes(form_data`reduced_base_ring);
    theta_lookup := AssociativeArray();

    for tuple_x in source_tuples do
        obs_record_trace_zero_norm(
            form_data,
            square_classes,
            tuple_x,
            ~theta_lookup
        );
        // Once every square class occurs, equality Theta = Delta is proved.
        if #Keys(theta_lookup) eq #square_classes`delta_group then
            break;
        end if;
    end for;

    return obs_local_result(
        kind,
        group_model`order_data,
        source_modulus,
        group_model`modulus_ideal,
        form_data,
        square_classes,
        theta_lookup
    );
end function;


function obs_class_index_lookup(group_model)
    lookup := AssociativeArray();
    class_key_data := assigned group_model`class_key_data select
        group_model`class_key_data else false;

    for i in [1..#group_model`class_representatives] do
        representative := group_model`reduced_algebra!
            obs_tuple(
                group_model`class_representatives[i],
                group_model`reduced_base_ring
            );
        key := projective_class_key(
            representative,
            group_model`scalars,
            class_key_data
        );
        if IsDefined(lookup, key) then
            error "Projective class representatives are not distinct.";
        end if;
        lookup[key] := i;
    end for;
    return lookup;
end function;


// Enumerate the reduced coordinate tuples of the projective classes of an
// abstract subgroup: through the natural PGL(2,F) matrix model when the
// quotient carries one, and through the class-index permutation action
// otherwise.  A subgroup is closed under inversion, so recovering the
// representative of g^-1 (the natural model's action-side convention)
// enumerates exactly the classes of the subgroup.
function obs_subgroup_tuples(group_model, subgroup)
    if UsesNaturalSplitPrimeModel(group_model) then
        tuples := {
            obs_tuple(
                NaturalSplitPrimeReducedRepresentative(
                    group_model,
                    group_element^-1
                ),
                group_model`reduced_base_ring
            ) : group_element in subgroup
        };
        tuples := Setseq(tuples);
        Sort(~tuples);
        return tuples;
    end if;

    class_lookup := obs_class_index_lookup(group_model);
    class_key_data := assigned group_model`class_key_data select
        group_model`class_key_data else false;
    identity := reduced_order_identity(
        group_model`order_data,
        group_model`reduction_map,
        group_model`reduced_algebra
    );
    identity_index := identity_class_index(
        identity,
        class_lookup,
        group_model`scalars,
        class_key_data
    );
    indices := {identity_index^element : element in subgroup};
    sorted_indices := Setseq(indices);
    Sort(~sorted_indices);

    if exists{index : index in sorted_indices |
              index lt 1 or index gt #group_model`class_representatives} then
        error "The subgroup does not act through the projective quotient.";
    end if;

    return [
        obs_tuple(
            group_model`class_representatives[index],
            group_model`reduced_base_ring
        ) : index in sorted_indices
    ];
end function;


// Compute Theta_A(H) for a subgroup H of an already constructed G[A].
function ObstructionAtSubgroup(group_model, subgroup)
    return obs_from_tuples(
        "subgroup",
        group_model,
        group_model`modulus_ideal,
        obs_subgroup_tuples(group_model, subgroup)
    );
end function;


// Compute the full ambient set Theta_A.  A must be a prime power; composite
// ambient calculations are products of these local results.  Directly scanning
// the trace-zero locus avoids constructing a much larger permutation group.
function ObstructionAtModulus(order_data, modulus_ideal)
    factorization := Factorization(modulus_ideal);
    if #factorization ne 1 then
        error "ObstructionAtModulus expects a prime-power ideal.";
    end if;

    form_data := obs_reduced_forms(order_data, modulus_ideal);
    square_classes := obs_square_classes(form_data`reduced_base_ring);
    theta_lookup := AssociativeArray();
    prime_ideal := factorization[1][1];
    exponent := factorization[1][2];
    ramified_maximal :=
        order_is_locally_maximal_at_prime(order_data, prime_ideal) and
        Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) ne 0;
    stabilized_exponent :=
        2 * Valuation(2 * order_data`integer_ring, prime_ideal) + 1;

    if ramified_maximal and exponent ge stabilized_exponent then
        obs_ramified_maximal_theta(
            form_data,
            square_classes,
            ~theta_lookup
        );
    else
        ring_elements := [element : element in form_data`reduced_base_ring];
        obs_scan_trace_zero_tuples(
            form_data,
            square_classes,
            [ring_elements : i in [1..4]],
            false,
            ~theta_lookup
        );
    end if;
    return obs_local_result(
        "ambient",
        order_data,
        modulus_ideal,
        modulus_ideal,
        form_data,
        square_classes,
        theta_lookup
    );
end function;


// ---------------------------------------------------------------------------
// Preimages of complements at the Section 7 modulus
// ---------------------------------------------------------------------------

// The complement obstruction is defined only when the complementary ideal C
// is coprime to the localized prime set T; return false otherwise.  An
// applicable C with several prime factors would need a CRT lift of the
// complement.  That case never arises in the class-one computations, so it
// is a guarded error rather than a silently wrong answer.
function ComplementObstructionApplies(complementary_result)
    support := [factor[1] : factor in Factorization(complementary_result`modulus_ideal)];
    inverted_primes := complementary_result`localized_unit_group`ramified_subset;
    if exists{prime_ideal : prime_ideal in support |
              Index(inverted_primes, prime_ideal) ne 0} then
        return false;
    end if;
    if #support ne 1 then
        error "An applicable composite complementary ideal requires a CRT complement lift.";
    end if;
    return true;
end function;


// Build the implicit model of H_tilde described at LiftedComplementFormat,
// enforcing the hypotheses of the Section 7 complement obstruction: the
// reduction to G[C] is injective (so the complement class is faithfully a
// subgroup there), T is disjoint from the support of C, and C is a prime
// power.  When e(C) strictly exceeds C, the scalar fibers of R/e(C) over
// R/C are precomputed so the preimage can be enumerated coordinatewise.
function LiftComplement(complementary_result, complement_index)
    if not complementary_result`injective then
        error "A complement can only be lifted from an injective reduction.";
    end if;
    if Type(complement_index) ne RngIntElt or
       complement_index lt 1 or
       complement_index gt #complementary_result`complement_classes then
        error "The complement index is out of range.";
    end if;
    if not ComplementObstructionApplies(complementary_result) then
        error "The complement obstruction is not defined when T meets the support of C.";
    end if;

    factorization := Factorization(complementary_result`modulus_ideal);
    if #factorization ne 1 then
        error "The paper's applicable complement obstructions require a prime-power complementary ideal.";
    end if;

    prime_ideal := factorization[1][1];
    source_exponent := factorization[1][2];
    stabilized_modulus := StabilizedModulus(complementary_result`modulus_ideal);
    stabilized_factorization := Factorization(stabilized_modulus);
    if #stabilized_factorization ne 1 or
       stabilized_factorization[1][1] ne prime_ideal then
        error "Stabilization changed the prime support of the complementary ideal.";
    end if;

    source_group_model := complementary_result`reduction_factors[1]`group_model;
    source_subgroup := complementary_result`complement_classes[complement_index]`subgroup;
    source_tuples := obs_subgroup_tuples(source_group_model, source_subgroup);
    target_form := obs_reduced_forms(
        source_group_model`order_data,
        stabilized_modulus
    );
    scalar_fibers := false;

    if stabilized_modulus ne complementary_result`modulus_ideal then
        scalar_fibers := scalar_prime_reduction_fibers(
            source_group_model`order_data`integer_ring,
            target_form`reduced_base_ring,
            target_form`reduction_map,
            source_group_model`reduced_base_ring,
            source_group_model`reduction_map
        );
    end if;

    return rec<LiftedComplementFormat |
        complementary_result := complementary_result,
        complement_index := complement_index,
        source_modulus := complementary_result`modulus_ideal,
        modulus_ideal := stabilized_modulus,
        prime_ideal := prime_ideal,
        source_exponent := source_exponent,
        target_exponent := stabilized_factorization[1][2],
        source_group_model := source_group_model,
        source_subgroup := source_subgroup,
        source_tuples := source_tuples,
        target_form := target_form,
        scalar_fibers := scalar_fibers
    >;
end function;


// Compute Theta_{e(C)}(H_tilde) for one complement class H: the set of
// square classes in Delta_{e(C)} realized as reduced norms of trace-zero
// elements of the preimage H_tilde of H under G[e(C)] -> G[C].  When
// e(C) = C the preimage is H itself and its tuples are scanned directly;
// otherwise every coordinate tuple lying over a class of H is enumerated
// through the exact scalar fibers recorded by LiftComplement.
function TorsionObstruction(complementary_result, complement_index)
    lifted := LiftComplement(complementary_result, complement_index);

    if lifted`source_modulus eq lifted`modulus_ideal then
        return obs_from_tuples(
            "lifted_complement",
            lifted`source_group_model,
            lifted`source_modulus,
            lifted`source_tuples
        );
    end if;

    square_classes := obs_square_classes(lifted`target_form`reduced_base_ring);
    theta_lookup := AssociativeArray();
    for source_tuple in lifted`source_tuples do
        coordinate_fibers := [
            scalar_prime_fiber(lifted`scalar_fibers, coordinate) :
            coordinate in source_tuple
        ];
        obs_scan_trace_zero_tuples(
            lifted`target_form,
            square_classes,
            coordinate_fibers,
            true,
            ~theta_lookup
        );
        if #Keys(theta_lookup) eq #square_classes`delta_group then
            break;
        end if;
    end for;

    return obs_local_result(
        "lifted_complement",
        lifted`source_group_model`order_data,
        lifted`source_modulus,
        lifted`modulus_ideal,
        lifted`target_form,
        square_classes,
        theta_lookup
    );
end function;


// ---------------------------------------------------------------------------
// Discriminant obstruction
// ---------------------------------------------------------------------------

// Compute the ambient obstruction at the stabilized discriminant: for D the
// finite discriminant of the algebra, Theta_{e(D)} is assembled from one
// local ambient factor per prime power of e(D).  Delta and Theta sizes
// multiply by CRT, and 1 lies in Theta exactly when it does in every local
// factor.  D = (1) yields the inapplicable record the tables print as a
// dash.
function DiscriminantObstruction(order_data)
    discriminant := Discriminant(order_data`quaternion_algebra);
    stabilized_modulus := StabilizedModulus(discriminant);
    factorization := Factorization(stabilized_modulus);

    // The paper prints a dash when the finite discriminant has empty support.
    if #factorization eq 0 then
        return rec<TorsionObstructionFormat |
            kind := "discriminant",
            applicable := false,
            order_data := order_data,
            source_modulus := discriminant,
            modulus_ideal := stabilized_modulus,
            local_factors := [],
            delta_size := 0,
            delta_representatives := [],
            theta_size := 0,
            theta_representatives := [],
            theta_contains_one := false
        >;
    end if;

    local_factors := [];
    for factor in factorization do
        Append(
            ~local_factors,
            ObstructionAtModulus(
                order_data,
                factor[1]^factor[2]
            )
        );
    end for;

    // CRT identifies both Delta and the full ambient Theta with products of
    // their local factors.  Exact representatives remain attached locally.
    return rec<TorsionObstructionFormat |
        kind := "discriminant",
        applicable := true,
        order_data := order_data,
        source_modulus := discriminant,
        modulus_ideal := stabilized_modulus,
        local_factors := local_factors,
        delta_size := &*[factor`delta_size : factor in local_factors],
        delta_representatives := [],
        theta_size := &*[factor`theta_size : factor in local_factors],
        theta_representatives := [],
        theta_contains_one := &and[factor`theta_contains_one : factor in local_factors]
    >;
end function;
