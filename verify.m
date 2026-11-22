// Checks the CSV files and recomputes the finite calculations cited in the
// paper: Lemmas 32--34, Theorems 35, 38 and 50, Examples 19, 20, 37
// and 49, Proposition 42, the definition after Lemma 47, and the Hurwitz and
// Lipschitz orders.
// Run from code/: magma verify.m.  The full classification is in reproduce.m.

load "load.m";
SetColumns(0);   // print each message on one line

if not assigned data_directory then
    data_directory := "data";
end if;


procedure verify(condition, message)
    if not condition then
        error "Verification failed: " cat message;
    end if;
end procedure;


procedure verify_section(message)
    print "";
    print "[verify]", message;
end procedure;



function verify_boolean(value)
    verify(value in {"true", "false"}, "expected true or false, got " cat value);
    return value eq "true";
end function;


// Split at a delimiter outside brackets, so commas inside an ideal key are
// kept.  Empty pieces are kept.
function verify_split(value, delimiter)
    pieces := [];
    depth := 0;
    start := 1;
    i := 1;
    while i le #value do
        if value[i] eq "[" then
            depth +:= 1;
        elif value[i] eq "]" then
            depth -:= 1;
        end if;
        if depth eq 0 and value[i..Min(#value, i + #delimiter - 1)] eq delimiter then
            Append(~pieces, start le i - 1 select value[start..i - 1] else "");
            i +:= #delimiter;
            start := i;
        else
            i +:= 1;
        end if;
    end while;
    Append(~pieces, start le #value select value[start..#value] else "");
    return pieces;
end function;


// The fields of one CSV line: every field is quoted and none contains ",".
function verify_csv_fields(line)
    return verify_split(line[2..#line - 1], "\",\"");
end function;


// Rows of a CSV written by reproduce.m, as arrays from column name to string.
function verify_read_csv(filename, expected_headers)
    lines := Split(Read(filename), "\n");
    headers := verify_csv_fields(lines[1]);
    verify(headers eq expected_headers, filename cat " has the wrong columns");
    rows := [];
    for line in lines[2..#lines] do
        values := verify_csv_fields(line);
        verify(#values eq #headers, filename cat " has a row with the wrong number of fields");
        row := AssociativeArray();
        for i in [1..#headers] do
            row[headers[i]] := values[i];
        end for;
        Append(~rows, row);
    end for;
    return rows;
end function;


// ---------------------------------------------------------------------------
// Parsing ideals and factorizations
// ---------------------------------------------------------------------------

// The ideal written by CanonicalIdealKey as "N:[c_1, ..., c_{d^2}]": its norm
// and its d-by-d basis matrix by rows.
function verify_ideal(integer_ring, key)
    colon := Index(key, ":");
    coordinates := [StringToInteger(c) : c in Split(key[colon + 1..#key], "[], ")];
    d := Degree(integer_ring);
    basis_matrix := Matrix(Integers(), d, d, coordinates);
    ideal_x := ideal<integer_ring | [integer_ring!Eltseq(basis_matrix[i]) : i in [1..d]]>;
    verify(Norm(ideal_x) eq StringToInteger(key[1..colon - 1]), key cat " has the wrong norm");
    return ideal_x;
end function;


// "{}" or "{ k_1, k_2, ... }".
function verify_subset(integer_ring, value)
    if value eq "{}" then
        return [];
    end if;
    return [verify_ideal(integer_ring, key) : key in verify_split(value[3..#value - 2], ", ")];
end function;


// "1" or "k_1^e_1 * k_2^e_2 * ...".  Returns the ideal, its primes and exponents.
function verify_factorization(integer_ring, value)
    primes := [];
    exponents := [];
    if value ne "1" then
        for piece in verify_split(value, " * ") do
            caret := Index(piece, "^");
            prime_ideal := verify_ideal(integer_ring, piece[1..caret - 1]);
            verify(IsPrime(prime_ideal), value cat " has a nonprime factor");
            Append(~primes, prime_ideal);
            Append(~exponents, StringToInteger(piece[caret + 1..#piece]));
        end for;
    end if;
    ideal_x := 1 * integer_ring;
    for i in [1..#primes] do
        ideal_x *:= primes[i]^exponents[i];
    end for;
    return ideal_x, primes, exponents;
end function;


// Equality of two lists of distinct ideals, in any order.
function verify_same_ideals(left, right)
    return #left eq #right and forall{x : x in left | x in right};
end function;


// Check StabilizedModulus against the definition after Lemma 47: e(a) has the
// primes of a, with exponents max{v_p(a), 2 v_p(2) + 1}.
procedure verify_stabilized_formula(modulus_ideal)
    stabilized := StabilizedModulus(modulus_ideal);
    factors := Factorization(modulus_ideal);
    verify(#Factorization(stabilized) eq #factors, "StabilizedModulus changed prime support");
    for factor in factors do
        expected := Maximum(factor[2], 2 * Valuation(2 * Order(modulus_ideal), factor[1]) + 1);
        verify(Valuation(stabilized, factor[1]) eq expected,
               "StabilizedModulus disagrees with the exponent defined after Lemma 47");
    end for;
end procedure;


// The order n in "<n, id>", or 1 for "1".
function verify_group_order(type_string)
    return type_string eq "1" select 1 else StringToInteger(Split(type_string, "<, >")[1]);
end function;


// A set "{ k_1, k_2 }" or factorization "k_1^e_1 * k_2^e_2" with its pieces
// sorted, so that the order in which primes of equal norm are listed does not matter.
function verify_sorted(value, prefix, delimiter, suffix)
    if value in {"{}", "1"} then
        return value;
    end if;
    pieces := Sort(verify_split(value[#prefix + 1..#value - #suffix], delimiter));
    return prefix cat JoinStrings(pieces, delimiter) cat suffix;
end function;


function verify_group_key(order_index, subset_string)
    return order_index cat " || " cat verify_sorted(subset_string, "{ ", ", ", " }");
end function;


function verify_minimal_key(order_index, subset_string, factorization_string)
    return verify_group_key(order_index, subset_string) cat " || " cat
           verify_sorted(factorization_string, "", " * ", "");
end function;


function verify_increment(array, key)
    result := array;
    result[key] := IsDefined(result, key) select result[key] + 1 else 1;
    return result;
end function;


// ---------------------------------------------------------------------------
// CSV files and the links between them
// ---------------------------------------------------------------------------

verify_section("classification data");

algebra_rows := verify_read_csv(data_directory cat "/algebras.csv", [
    "order_index", "base_field_degree", "base_field_discriminant",
    "algebra_discriminant", "ramified_primes", "gamma_emptyset_order",
    "discriminant_theta_applicable", "discriminant_modulus_factorization",
    "discriminant_theta_size", "discriminant_theta_contains_one"
]);
localized_rows := verify_read_csv(data_directory cat "/localized_groups.csv", [
    "order_index", "ramified_subset", "gamma_order", "gamma_type",
    "exclusion_reason"
]);
minimal_rows := verify_read_csv(data_directory cat "/minimal_ideals.csv", [
    "order_index", "ramified_subset", "modulus_norm",
    "modulus_factorization", "has_complement"
]);
complement_rows := verify_read_csv(data_directory cat "/complements.csv", [
    "order_index", "ramified_subset", "modulus_norm",
    "modulus_factorization", "complement_index", "complement_order",
    "complement_is_normal", "theta_applicable",
    "theta_modulus_factorization", "theta_size", "theta_contains_one"
]);

class_indices := ClassOneOrderIndices();
verify(#class_indices eq 49, "the Kirschmer table does not give the paper's 49 orders");
verify(Sort([StringToInteger(row["order_index"]) : row in algebra_rows]) eq Sort(class_indices),
       "algebras.csv does not have exactly one row per class-number-one order");

// What algebras.csv and Kirschmer's table give for each order, keyed by the
// order_index string.
OrderInfoFormat := recformat<row, field, integer_ring, discriminant, ramified, gamma_emptyset_order>;
order_info := AssociativeArray();

for row in algebra_rows do
    order_index := row["order_index"];
    entry := OneClassEntry(StringToInteger(order_index));
    polynomial := Polynomial(entry[1]);
    field := Degree(polynomial) eq 1 select RationalsAsNumberField() else NumberField(polynomial);
    integer_ring := RingOfIntegers(field);
    algebra := QuaternionAlgebra<field | entry[3], entry[4]>;
    context := "algebras.csv order_index=" cat order_index;

    verify(StringToInteger(row["base_field_degree"]) eq Degree(field) and
           StringToInteger(row["base_field_discriminant"]) eq Discriminant(integer_ring),
           context cat " has the wrong base field");
    discriminant := verify_ideal(integer_ring, row["algebra_discriminant"]);
    verify(discriminant eq Discriminant(algebra), context cat " has the wrong algebra discriminant");
    ramified := SortIdeals([factor[1] : factor in Factorization(discriminant)]);
    verify(verify_same_ideals(SortIdeals(verify_subset(integer_ring, row["ramified_primes"])), ramified),
           context cat " has the wrong ramified primes");

    applicable := verify_boolean(row["discriminant_theta_applicable"]);
    theta_size := StringToInteger(row["discriminant_theta_size"]);
    theta_contains_one := verify_boolean(row["discriminant_theta_contains_one"]);
    verify_stabilized_formula(discriminant);
    verify(verify_factorization(integer_ring, row["discriminant_modulus_factorization"]) eq
               StabilizedModulus(discriminant),
           context cat " does not use the modulus e(D)");
    verify(applicable eq (#ramified gt 0), context cat " has the wrong obstruction applicability");
    verify(not theta_contains_one or theta_size gt 0, context cat " contains 1 but has empty Theta");
    verify(applicable or (theta_size eq 0 and not theta_contains_one),
           context cat " has an obstruction for the unit discriminant");

    order_info[order_index] := rec<OrderInfoFormat |
        row := row, field := field, integer_ring := integer_ring, discriminant := discriminant,
        ramified := ramified, gamma_emptyset_order := StringToInteger(row["gamma_emptyset_order"])>;
end for;

localized := AssociativeArray();
localized_count := AssociativeArray();
for row in localized_rows do
    order_index := row["order_index"];
    verify(IsDefined(order_info, order_index), "localized_groups.csv refers to an unknown order");
    context := "localized_groups.csv order_index=" cat order_index cat " T=" cat row["ramified_subset"];
    ramified_subset := verify_subset(order_info[order_index]`integer_ring, row["ramified_subset"]);
    verify(forall{p : p in ramified_subset | p in order_info[order_index]`ramified},
           context cat " contains an unramified prime");
    key := verify_group_key(order_index, row["ramified_subset"]);
    verify(not IsDefined(localized, key), context cat " is duplicated");

    gamma_order := StringToInteger(row["gamma_order"]);
    verify(verify_group_order(row["gamma_type"]) eq gamma_order, context cat " has a gamma_type of the wrong order");
    if #ramified_subset eq 0 then
        verify(gamma_order eq order_info[order_index]`gamma_emptyset_order, context cat " disagrees with algebras.csv");
    end if;

    expected_reason := "";
    if order_info[order_index]`gamma_emptyset_order eq 1 then
        if #ramified_subset eq 0 then
            expected_reason := "Gamma_emptyset=1 and T=emptyset";
        elif #ramified_subset eq 1 and #order_info[order_index]`ramified eq 1 then
            expected_reason := "Gamma_emptyset=1, #T=1, and no distinct ramified modulus prime";
        end if;
    end if;
    verify(row["exclusion_reason"] eq expected_reason, context cat " has the wrong exclusion reason");

    localized[key] := row;
    localized_count := verify_increment(localized_count, order_index);
end for;

for order_index in Keys(order_info) do
    verify(IsDefined(localized_count, order_index) and
           localized_count[order_index] eq 2^#order_info[order_index]`ramified,
           "localized_groups.csv does not have one row for every subset T of the ramified primes");
end for;

minimal := AssociativeArray();
minimal_has_complement := AssociativeArray();
minimal_ideals_by_group := AssociativeArray();
complementary_minimal_count_by_order := AssociativeArray();
composite_complementary_keys := [];
for row in minimal_rows do
    order_index := row["order_index"];
    verify(IsDefined(order_info, order_index), "minimal_ideals.csv refers to an unknown order");
    context := "minimal_ideals.csv order_index=" cat order_index cat " C=" cat row["modulus_factorization"];
    group_key := verify_group_key(order_index, row["ramified_subset"]);
    verify(IsDefined(localized, group_key), context cat " refers to an unknown localized group");
    verify(localized[group_key]["exclusion_reason"] eq "", context cat " belongs to an excluded case");

    modulus, primes, exponents := verify_factorization(order_info[order_index]`integer_ring, row["modulus_factorization"]);
    verify(StringToInteger(row["modulus_norm"]) eq Norm(modulus) and Norm(modulus) gt 1,
           context cat " has the wrong modulus norm");
    gamma_order := StringToInteger(localized[group_key]["gamma_order"]);

    // Split primes of C have norm at most |Gamma_T|.
    for prime_ideal in primes do
        verify(Valuation(order_info[order_index]`discriminant, prime_ideal) ne 0 or
               Norm(prime_ideal) le gamma_order,
               context cat " uses a split prime of norm above |Gamma_T|");
    end for;

    key := verify_minimal_key(order_index, row["ramified_subset"], row["modulus_factorization"]);
    verify(not IsDefined(minimal, key), context cat " is duplicated");
    has_complement := verify_boolean(row["has_complement"]);
    if has_complement then
        complementary_minimal_count_by_order := verify_increment(complementary_minimal_count_by_order, order_index);
        if #primes ne 1 then
            Append(~composite_complementary_keys, key);
        end if;

        // Theorem 35, equality case: a split prime of norm |Gamma_T| occurs
        // only as C = p with Gamma_T cyclic of order 2, 3 or 5.
        for prime_ideal in primes do
            if Valuation(order_info[order_index]`discriminant, prime_ideal) eq 0 and
               Norm(prime_ideal) eq gamma_order then
                verify(#primes eq 1 and exponents[1] eq 1 and
                       localized[group_key]["gamma_type"] in {"<2, 1>", "<3, 1>", "<5, 1>"},
                       context cat " violates the equality case of Theorem 35");
            end if;
        end for;
    end if;
    minimal[key] := row;
    minimal_has_complement[key] := has_complement;
    ideals := IsDefined(minimal_ideals_by_group, group_key) select minimal_ideals_by_group[group_key] else [];
    Append(~ideals, modulus);
    minimal_ideals_by_group[group_key] := ideals;
end for;

for key in Keys(localized) do
    verify(IsDefined(minimal_ideals_by_group, key) eq (localized[key]["exclusion_reason"] eq ""),
           "a localized group has minimal ideals exactly when it is not excluded");
end for;
for group_key in Keys(minimal_ideals_by_group) do
    ideals := minimal_ideals_by_group[group_key];
    for i in [1..#ideals] do
        for j in [i + 1..#ideals] do
            verify(not (ideals[i] subset ideals[j]) and not (ideals[j] subset ideals[i]),
                   "minimal_ideals.csv has comparable ideals for one localized group");
        end for;
    end for;
end for;

complement_count_by_minimal := AssociativeArray();
complement_indices := AssociativeArray();
complement_order_by_minimal := AssociativeArray();
for row in complement_rows do
    order_index := row["order_index"];
    verify(IsDefined(order_info, order_index), "complements.csv refers to an unknown order");
    integer_ring := order_info[order_index]`integer_ring;
    context := "complements.csv order_index=" cat order_index cat " C=" cat row["modulus_factorization"];
    minimal_key := verify_minimal_key(order_index, row["ramified_subset"], row["modulus_factorization"]);
    verify(IsDefined(minimal, minimal_key) and minimal_has_complement[minimal_key],
           context cat " does not belong to a minimal ideal with has_complement=true");

    index_key := minimal_key cat " || " cat row["complement_index"];
    verify(not IsDefined(complement_indices, index_key), context cat " repeats a complement index");
    complement_indices[index_key] := true;
    complement_count_by_minimal := verify_increment(complement_count_by_minimal, minimal_key);

    complement_order := StringToInteger(row["complement_order"]);
    if IsDefined(complement_order_by_minimal, minimal_key) then
        verify(complement_order_by_minimal[minimal_key] eq complement_order,
               context cat " has complement classes of different orders");
    else
        complement_order_by_minimal[minimal_key] := complement_order;
    end if;
    _ := verify_boolean(row["complement_is_normal"]);

    // Theta is defined exactly when C is coprime to T, and then C is a
    // prime power.
    ramified_subset := verify_subset(integer_ring, row["ramified_subset"]);
    modulus, modulus_primes, _ := verify_factorization(integer_ring, row["modulus_factorization"]);
    applicable := verify_boolean(row["theta_applicable"]);
    verify(applicable eq forall{p : p in modulus_primes | p notin ramified_subset},
           context cat " has the wrong obstruction applicability");
    if applicable then
        verify(#modulus_primes eq 1, context cat " has an obstruction at a composite modulus");
        verify_stabilized_formula(modulus);
        verify(verify_factorization(integer_ring, row["theta_modulus_factorization"]) eq StabilizedModulus(modulus),
               context cat " does not use the modulus e(C)");
        verify(not verify_boolean(row["theta_contains_one"]) or StringToInteger(row["theta_size"]) gt 0,
               context cat " contains 1 but has empty Theta");
    else
        verify(row["theta_modulus_factorization"] eq "" and row["theta_size"] eq "" and
               row["theta_contains_one"] eq "",
               context cat " has an obstruction where none is defined");
    end if;
end for;

for key in Keys(minimal) do
    count := IsDefined(complement_count_by_minimal, key) select complement_count_by_minimal[key] else 0;
    verify((count gt 0) eq minimal_has_complement[key],
           "a minimal ideal has complement rows exactly when has_complement=true");
    for index in [1..count] do
        verify(IsDefined(complement_indices, key cat " || " cat Sprint(index)),
               "complement indices are not 1, 2, ..., n");
    end for;
end for;
complementary_minimal_keys := [key : key in Keys(minimal) | minimal_has_complement[key]];

verify_section("Theorem 35, Theorem 38, Example 37, and Proposition 42");

// Theorem 38: B has a nontrivial minimal complementary triple when
// Gamma_emptyset != 1 or B has more than one finite ramified prime.
for order_index in Keys(order_info) do
    if order_info[order_index]`gamma_emptyset_order ne 1 or #order_info[order_index]`ramified gt 1 then
        verify(IsDefined(complementary_minimal_count_by_order, order_index),
               "an algebra covered by Theorem 38 has no nontrivial minimal complementary triple");
    end if;
end for;


// The unique order with the given base-field degree and discriminant and N(D).
function verify_unique_index(order_info, degree, field_discriminant, discriminant_norm)
    matches := [
        order_index : order_index in Keys(order_info) |
        Degree(order_info[order_index]`field) eq degree and
        Discriminant(order_info[order_index]`integer_ring) eq field_discriminant and
        Norm(order_info[order_index]`discriminant) eq discriminant_norm
    ];
    verify(#matches eq 1, "a paper example is not determined by its invariants");
    return matches[1];
end function;


// The unique complementary triple of an order with one ramified prime p:
// returns the string "{ p }", and the key and row of the triple's minimal ideal.
function verify_unique_triple(ramified, minimal, complementary_minimal_keys, complement_rows, order_index)
    verify(#ramified eq 1, "a paper example does not have one ramified prime");
    keys := [key : key in complementary_minimal_keys | minimal[key]["order_index"] eq order_index];
    verify(#keys eq 1 and #[row : row in complement_rows | row["order_index"] eq order_index] eq 1,
           "a paper example does not have a unique minimal complementary triple");
    return "{ " cat CanonicalIdealKey(ramified[1]) cat " }", keys[1], minimal[keys[1]];
end function;


// Example 37: over the cubic field of discriminant 49 with N(D) = 7,
// Gamma_emptyset = D7, Gamma_T = D14 for T = {p7}, and the unique triple has
// C the norm-27 prime.
d7_order_index := verify_unique_index(order_info, 3, 49, 7);
d7_subset_string, _, d7_row := verify_unique_triple(
    order_info[d7_order_index]`ramified, minimal, complementary_minimal_keys, complement_rows, d7_order_index
);
verify(
    localized[verify_group_key(d7_order_index, "{}")]["gamma_type"] eq "<14, 1>" and
    localized[verify_group_key(d7_order_index, d7_subset_string)]["gamma_type"] eq "<28, 3>",
    "Example 37 does not have Gamma_emptyset = D7 and Gamma_T = D14"
);
_, d7_factors, d7_exponents := verify_factorization(order_info[d7_order_index]`integer_ring, d7_row["modulus_factorization"]);
verify(d7_row["ramified_subset"] eq d7_subset_string and
       #d7_factors eq 1 and d7_exponents eq [1] and Norm(d7_factors[1]) eq 27,
       "Example 37 is not the triple T = {p7}, C = p27");

// Proposition 42: the only composite complementary modulus is over the cubic
// field of discriminant 81 with N(D) = 3: T = {p3}, C = p3 * p8, N(C) = 24.
zeta9_order_index := verify_unique_index(order_info, 3, 81, 3);
zeta9_subset_string, zeta9_key, zeta9_row := verify_unique_triple(
    order_info[zeta9_order_index]`ramified, minimal, complementary_minimal_keys, complement_rows, zeta9_order_index
);
_, zeta9_factors, zeta9_exponents := verify_factorization(order_info[zeta9_order_index]`integer_ring, zeta9_row["modulus_factorization"]);
verify(#composite_complementary_keys eq 1 and
       composite_complementary_keys[1] eq zeta9_key and
       zeta9_row["ramified_subset"] eq zeta9_subset_string and
       {Integers()!Norm(p) : p in zeta9_factors} eq {3, 8} and zeta9_exponents eq [1, 1] and
       order_info[zeta9_order_index]`ramified[1] in zeta9_factors,
       "Proposition 42 is not the unique composite triple T = {p3}, N(C) = 24");

verify_section("proof of Theorem 50: rational torsion obstructions");

// Theorem 50: over Q with T empty, every triple has a complement obstruction or
// a discriminant obstruction that does not contain 1. For D = 13 the
// discriminant obstruction does not contain 1.
function verify_excludes_one(row, prefix)
    return verify_boolean(row[prefix cat "theta_applicable"]) and
           not verify_boolean(row[prefix cat "theta_contains_one"]);
end function;

for row in complement_rows do
    order_index := row["order_index"];
    if Degree(order_info[order_index]`field) eq 1 and row["ramified_subset"] eq "{}" then
        verify(verify_excludes_one(row, "") or verify_excludes_one(order_info[order_index]`row, "discriminant_"),
               "a rational triple with T empty has neither torsion obstruction");
    end if;
end for;
d13_order_index := verify_unique_index(order_info, 1, 1, 13);
verify(verify_excludes_one(order_info[d13_order_index]`row, "discriminant_"),
       "the obstruction set for D = 13 contains 1");

print Sprintf(
    "[verify] data passed: %o algebras, %o localized groups, %o minimal ideals, %o complements",
    #algebra_rows, #localized_rows, #minimal_rows, #complement_rows
);


// ---------------------------------------------------------------------------
// Recomputed checks
// ---------------------------------------------------------------------------

verify_section("definition following Lemma 47: stabilized modulus");

Q := RationalsAsNumberField();
ZK := RingOfIntegers(Q);
verify_stabilized_formula((2 * ZK)^2 * (3 * ZK)^4);
verify(StabilizedModulus((2 * ZK)^2 * (3 * ZK)^4) eq (2 * ZK)^3 * (3 * ZK)^4,
       "odd and dyadic rational factors do not follow the stabilized-modulus rule");

quadratic_field<a> := QuadraticField(2);
quadratic_integers := RingOfIntegers(quadratic_field);
dyadic_prime := Factorization(2 * quadratic_integers)[1][1];
odd_prime := Factorization(3 * quadratic_integers)[1][1];
test_modulus := dyadic_prime^3 * odd_prime^2;
verify_stabilized_formula(test_modulus);
verify(Valuation(StabilizedModulus(test_modulus), dyadic_prime) eq 5,
       "the ramified dyadic example does not use 2v_p(2)+1");
verify(Valuation(StabilizedModulus(test_modulus), odd_prime) eq 2,
       "an odd-prime exponent was changed unnecessarily");
print "[verify] stabilized-modulus exponent rule passed";


verify_section("Lemma 32: unit representatives of reduced norm one");

// Build all 49 orders once; later checks find their examples among them.
orders := AssociativeArray();
unit_representative_count := 0;
for index in class_indices do
    order_data := ClassOneOrder(index);
    orders[Sprint(index)] := order_data;
    for unit in [order_data`unit_map(u) : u in order_data`unit_group] do
        verify(Norm(unit) eq 1, "a projective unit representative does not have reduced norm one");
        unit_representative_count +:= 1;
    end for;
end for;
print Sprintf("[verify] unit-norm lemma passed for %o representatives", unit_representative_count);


// An element of Gamma_T maps to the identity modulo p only if it is a scalar
// modulo p, that is, only if p divides every 2-by-2 minor of its coordinate
// vector and that of 1. Returns the primes dividing all the minors.
function verify_collision_primes(order_data, element)
    one := OrderCoordinates(order_data, order_data`quaternion_algebra!1);
    x := OrderCoordinates(order_data, element);
    minors := [one[i] * x[j] - one[j] * x[i] : j in [i + 1..4], i in [1..4]];
    verify(exists{m : m in minors | m ne 0}, "a nonidentity localized-unit class is scalar");
    R := order_data`integer_ring;
    return [f[1] : f in Factorization(ideal<R | [R!m : m in minors]>)];
end function;


procedure verify_split_prime_injective(~context, group, p, claim)
    local_image := false;
    LocalImage(~context, group, p, 1, ~local_image);
    verify(#local_image`image_subgroup eq group`subgroup_order, claim cat " at " cat CanonicalIdealKey(p));
end procedure;


// At every split prime where a nonidentity element of Gamma_T could map to the
// identity, check that reduction is injective in the cases the proofs use:
// Gamma_emptyset = C2, T = {p} with Gamma_T = C2, and N(p) > |Gamma_T|. Also
// compare each Gamma_T with localized_groups.csv, and find the order with
// Gamma_emptyset = 1 and two ramified primes for Lemma 33(iii).
verify_section("proofs of Lemma 33(ii), Lemma 34, and Theorem 35");
empty_c2_case_count := 0;
singleton_c2_case_count := 0;
localized_nonidentity_count := 0;
large_norm_candidate_count := 0;
distinct_ramified_orders := [];

for index in class_indices do
    order_data := orders[Sprint(index)];
    context, localized_groups := context_with_all_groups(order_data);
    gamma_emptyset := localized_groups[1];
    verify(#gamma_emptyset`ramified_subset eq 0, "Gamma_emptyset is not listed first");
    if gamma_emptyset`subgroup_order eq 1 and #RamifiedPrimes(order_data) gt 1 then
        Append(~distinct_ramified_orders, order_data);
    end if;

    for group in localized_groups do
        T := group`ramified_subset;
        subset_string := #T eq 0 select "{}" else
            "{ " cat JoinStrings([CanonicalIdealKey(p) : p in T], ", ") cat " }";
        group_key := verify_group_key(Sprint(index), subset_string);
        verify(IsDefined(localized, group_key),
               Sprintf("localized_groups.csv omits order %o and T=%o", index, subset_string));
        csv_group := localized[group_key];
        exact_type := group`subgroup_order eq 1 select "1" else Sprint(IdentifyGroup(group`subgroup));
        verify(
            csv_group["gamma_order"] eq Sprint(group`subgroup_order) and
            csv_group["gamma_type"] eq exact_type and
            csv_group["exclusion_reason"] eq ClassificationExclusionReason(gamma_emptyset, group),
            "localized_groups.csv disagrees with the computed Gamma_T"
        );

        split_primes := [];
        for g in group`subgroup do
            if g ne Identity(group`subgroup) then
                localized_nonidentity_count +:= 1;
                for p in verify_collision_primes(order_data, NormalizerRepresentative(order_data, g)) do
                    if not is_ramified(order_data, p) then
                        Include(~split_primes, p);
                    end if;
                end for;
            end if;
        end for;

        empty_c2_case := #T eq 0 and group`subgroup_order eq 2;
        singleton_c2_case := gamma_emptyset`subgroup_order eq 1 and #T eq 1 and group`subgroup_order eq 2;
        empty_c2_case_count +:= empty_c2_case select 1 else 0;
        singleton_c2_case_count +:= singleton_c2_case select 1 else 0;

        for p in SortIdeals(split_primes) do
            if empty_c2_case then
                verify_split_prime_injective(~context, group, p,
                    "Gamma_emptyset=C2 is not injective at a possible collision prime");
            end if;
            if singleton_c2_case then
                verify_split_prime_injective(~context, group, p,
                    "the singleton-T C2 group is not injective at a possible collision prime");
            end if;
            if Norm(p) gt group`subgroup_order then
                large_norm_candidate_count +:= 1;
                verify_split_prime_injective(~context, group, p,
                    "a split prime above #Gamma_T has noninjective reduction");
            end if;
        end for;
    end for;
end for;

verify(empty_c2_case_count gt 0, "the Kirschmer--Voight list has no Gamma_emptyset=C2 case");
verify(singleton_c2_case_count gt 0, "the Kirschmer--Voight list has no singleton-T C2 case with Gamma_emptyset=1");
verify(#distinct_ramified_orders eq 1,
       "Gamma_emptyset=1 and more than one finite ramified prime does not determine a unique order");
print Sprintf(
    "[verify] collision ideals passed for %o nonidentity localized-unit classes (%o possible large-norm primes)",
    localized_nonidentity_count,
    large_norm_candidate_count
);


verify_section("proof of Lemma 33(iii): distinct ramified primes");

// The order over Q(sqrt(2)) ramified at primes of norm 2 and 25: T = {p2}
// has a normal complement at C = p25; T = {p25} has none at C = p2.
exceptional_order := distinct_ramified_orders[1];
verify(
    Degree(exceptional_order`base_field) eq 2 and
    Integers()!Discriminant(exceptional_order`integer_ring) eq 8,
    "the distinct-ramified singleton case is not defined over Q(sqrt(2))"
);
exceptional_ramified := RamifiedPrimes(exceptional_order);
verify([Norm(p) : p in exceptional_ramified] eq [2, 25],
       "the distinct-ramified singleton case does not have ramified norms 2 and 25");
ramified_two, ramified_twenty_five := Explode(exceptional_ramified);

// The index of the minimal injective ideal that is a power of p, which must be unique.
function verify_minimal_index(poset, p)
    matches := [i : i in [1..#poset`minimal_injective_ideals] |
                [f[1] : f in Factorization(poset`minimal_injective_ideals[i])] eq [p]];
    verify(#matches eq 1, "a ramified direction has no unique minimal injective ideal");
    return matches[1];
end function;

from_two := MinimalComplementaryIdeals(exceptional_order, [ramified_two]);
exceptional_index := verify_minimal_index(from_two, ramified_twenty_five);
exceptional_result := from_two`minimal_results[exceptional_index];
verify(
    from_two`localized_unit_group`subgroup_order eq 2 and
    from_two`minimal_injective_ideals[exceptional_index] eq ramified_twenty_five and
    #exceptional_result`complement_classes eq 1 and
    #exceptional_result`normal_complement_classes eq 1,
    "the stated norm-25 minimal complementary triple was not recovered"
);
from_twenty_five := MinimalComplementaryIdeals(exceptional_order, [ramified_twenty_five]);
reverse_result := from_twenty_five`minimal_results[verify_minimal_index(from_twenty_five, ramified_two)];
verify(
    from_twenty_five`localized_unit_group`subgroup_order eq 2 and
    #reverse_result`complement_classes eq 0,
    "the reverse ramified direction unexpectedly gives a minimal complementary triple"
);
print "[verify] unique distinct-ramified singleton case passed";


function verify_unique_order(orders, degree, field_discriminant, algebra_discriminant_norm)
    matches := [
        order_data : order_data in [orders[key] : key in Keys(orders)] |
        Degree(order_data`base_field) eq degree and
        Integers()!Discriminant(order_data`integer_ring) eq field_discriminant and
        Integers()!Norm(Discriminant(order_data`quaternion_algebra)) eq algebra_discriminant_norm
    ];
    verify(#matches eq 1, "a displayed example is not uniquely determined by its paper invariants");
    return matches[1];
end function;


function verify_projective_keys(order_data, elements)
    return {projective_key(order_data, x) : x in elements};
end function;


function verify_displayed_representative(order_data, representatives, expected)
    matches := [x : x in representatives | projective_key(order_data, x) eq projective_key(order_data, expected)];
    verify(#matches eq 1, "a displayed generator class was not recovered uniquely");
    return matches[1];
end function;


function verify_relation_word(p, q, a, b, indices)
    return [<p, a[indices[1]]>, <q, b[indices[2]]>, <p, a[indices[3]]>, <q, b[indices[4]]>];
end function;


function verify_relation_keys(presentation, words)
    return {Sprint(CanonicalRelation(presentation`inverse_map, w)) : w in words};
end function;


function verify_pairs_hold(presentation, p, representatives, pairs)
    inverse := presentation`inverse_map[p];
    return forall{pair : pair in pairs |
                  inverse[representatives[pair[1]]] eq representatives[pair[2]] and
                  inverse[representatives[pair[2]]] eq representatives[pair[1]]};
end function;


// The paper labels the quadratic example's generators only through their
// relations, and MaximalRightIdeals returns them in no fixed order. So try
// every labeling consistent with the displayed inverse pairs.
function verify_displayed_relation_labeling(presentation, p, q, a, b, pairs_a, pairs_b, relation_indices)
    computed := verify_relation_keys(presentation, presentation`square_relations);
    labelings := func<x, r, pairs | [[x[i^s] : i in [1..#x]] : s in Sym(#x) |
                                     verify_pairs_hold(presentation, r, [x[i^s] : i in [1..#x]], pairs)]>;
    for labeled_a in labelings(a, p, pairs_a) do
        for labeled_b in labelings(b, q, pairs_b) do
            words := [verify_relation_word(p, q, labeled_a, labeled_b, indices) : indices in relation_indices];
            if verify_relation_keys(presentation, words) eq computed then
                return true, labeled_a, labeled_b;
            end if;
        end for;
    end for;
    return false, a, b;
end function;


verify_section("Examples 19, 20, and 49: presentations and torsion");

// Example 19: D = 5 over Q, C = (5), S = {2, 3}. Check the 3 + 4 displayed
// generators, inverse pairs, six square relations, and abelianization (Z/2)^2.
rational_order := verify_unique_order(orders, 1, 1, 5);
rational_integers := rational_order`integer_ring;
rational_result := ReductionData(rational_order, [], 5 * rational_integers);
verify(rational_result`injective and #rational_result`complement_classes gt 0,
       "the rational displayed complementary triple was not recovered");
rational_presentation := PresentationForComplement(rational_result, [2 * rational_integers, 3 * rational_integers]);
rational_p, rational_q := Explode(rational_presentation`s_prime_ideals);
verify([#rational_presentation`a_representatives[p] : p in [rational_p, rational_q]] eq [3, 4],
       "the rational presentation has the wrong local generator counts");
verify(#rational_presentation`square_relations eq 6,
       "the rational presentation has the wrong square-relation count");
verify(AbelianQuotientInvariants(rational_presentation`gamma_group) eq [2, 2],
       "the rational presentation has the wrong abelianization");

rational_algebra := rational_order`quaternion_algebra;
i := rational_algebra.1;
j := rational_algebra.2;
k := i * j;
expected_norm_two := [i, i - 2*j + k, -i - 2*j - k];
expected_norm_three := [3*i - 2*j - k, i + k, 3*i + 2*j - k, i - k];
verify(verify_projective_keys(rational_order, rational_presentation`a_representatives[rational_p]) eq
           verify_projective_keys(rational_order, expected_norm_two),
       "the rational presentation's norm-two generators differ from the displayed classes");
verify(verify_projective_keys(rational_order, rational_presentation`a_representatives[rational_q]) eq
           verify_projective_keys(rational_order, expected_norm_three),
       "the rational presentation's norm-three generators differ from the displayed classes");
rational_a := [verify_displayed_representative(rational_order, rational_presentation`a_representatives[rational_p], x)
               : x in expected_norm_two];
rational_b := [verify_displayed_representative(rational_order, rational_presentation`a_representatives[rational_q], x)
               : x in expected_norm_three];
verify(verify_pairs_hold(rational_presentation, rational_p, rational_a, [<1, 1>, <2, 2>, <3, 3>]) and
       verify_pairs_hold(rational_presentation, rational_q, rational_b, [<1, 1>, <2, 2>, <3, 3>, <4, 4>]),
       "a displayed inverse relation was not recovered");
rational_relation_indices := [
    <2, 3, 1, 3>, <1, 4, 1, 2>, <2, 1, 2, 4>,
    <3, 2, 2, 2>, <3, 1, 1, 1>, <3, 4, 3, 3>
];
verify(
    verify_relation_keys(rational_presentation, rational_presentation`square_relations) eq
    verify_relation_keys(rational_presentation,
        [verify_relation_word(rational_p, rational_q, rational_a, rational_b, x) : x in rational_relation_indices]),
    "the rational presentation does not have exactly the six displayed square relators"
);

// Example 20: over Q(sqrt(2)) with N(D) = 18, C the dyadic prime, S the two
// norm-7 primes. Check 8 + 8 generators, sixteen square relations, no torsion
// (no generator equal to its own inverse and no relation of the form (ab)^2 = 1),
// and abelianization Z/2^3 x Z/10.
quadratic_order := verify_unique_order(orders, 2, 8, 18);
quadratic_integers := quadratic_order`integer_ring;
quadratic_level := Factorization(2 * quadratic_integers)[1][1];
quadratic_s_primes := SortIdeals([f[1] : f in Factorization(7 * quadratic_integers)]);
verify(#quadratic_s_primes eq 2 and &and[Norm(p) eq 7 : p in quadratic_s_primes],
       "the quadratic example does not have the two required split primes");
quadratic_result := ReductionData(quadratic_order, [], quadratic_level);
verify(quadratic_result`injective and #quadratic_result`complement_classes gt 0,
       "the quadratic displayed complementary triple was not recovered");
quadratic_presentation := PresentationForComplement(quadratic_result, quadratic_s_primes);
quadratic_p, quadratic_q := Explode(quadratic_presentation`s_prime_ideals);
verify([#quadratic_presentation`a_representatives[p] : p in [quadratic_p, quadratic_q]] eq [8, 8],
       "the quadratic presentation has the wrong local generator counts");
verify(#quadratic_presentation`square_relations eq 16,
       "the quadratic presentation has the wrong square-relation count");
verify(quadratic_presentation`generators_torsion_free and #quadratic_presentation`square_torsion eq 0,
       "the displayed edge/face torsion checks failed");
verify(AbelianQuotientInvariants(quadratic_presentation`gamma_group) eq [2, 2, 2, 10],
       "the quadratic presentation has the wrong abelianization");
quadratic_pairs_a := [<1, 3>, <2, 8>, <4, 5>, <6, 7>];
quadratic_pairs_b := [<1, 7>, <2, 8>, <3, 4>, <5, 6>];
quadratic_relation_indices := [
    <4, 4, 3, 2>, <2, 8, 8, 2>, <7, 5, 8, 1>, <7, 6, 2, 7>,
    <4, 1, 2, 4>, <7, 4, 6, 3>, <4, 7, 6, 8>, <4, 3, 2, 1>,
    <1, 5, 7, 2>, <1, 2, 6, 5>, <4, 2, 3, 3>, <4, 5, 5, 6>,
    <1, 4, 8, 6>, <1, 1, 3, 7>, <1, 6, 8, 3>, <4, 8, 7, 7>
];
// Either prime of S may be the first prime in the paper's display.
quadratic_labels_found := false;
for pq in [<quadratic_p, quadratic_q>, <quadratic_q, quadratic_p>] do
    p, q := Explode(pq);
    quadratic_labels_found := verify_displayed_relation_labeling(
        quadratic_presentation, p, q,
        quadratic_presentation`a_representatives[p], quadratic_presentation`a_representatives[q],
        quadratic_pairs_a, quadratic_pairs_b, quadratic_relation_indices);
    if quadratic_labels_found then
        break;
    end if;
end for;
verify(quadratic_labels_found,
       "the quadratic presentation cannot be relabeled as the displayed presentation");

// Example 49: at the norm-9 ramified prime, Theta is the nonsquare class,
// which is the class of 1 + sqrt(2).
norm_nine_prime := [p : p in RamifiedPrimes(quadratic_order) | Norm(p) eq 9][1];
quadratic_theta := ObstructionAtModulus(quadratic_order, norm_nine_prime);
verify(quadratic_theta`delta_size eq 2 and quadratic_theta`theta_size eq 1 and
       not quadratic_theta`theta_contains_one,
       "the quadratic torsion obstruction is not the unique nonsquare class");
_, quadratic_reduction := ResidueRing(quadratic_order, norm_nine_prime);
fundamental_unit := quadratic_integers!(1 + quadratic_order`base_field.1);
verify(not IsSquare(quadratic_theta`theta_representatives[1]) and
       not IsSquare(quadratic_reduction(fundamental_unit)),
       "the quadratic obstruction class is not the class of 1+sqrt(2)");
print "[verify] displayed presentation and torsion checks passed";


// ---------------------------------------------------------------------------
// Hurwitz and Lipschitz
// ---------------------------------------------------------------------------

function verify_group_type(group)
    return Sprint(IdentifyGroup(group));
end function;


// The image in the target quotient of an element of the source quotient, both
// quotients of orders in the same algebra.
function verify_image_in_model(source, target, g)
    reduced := QuotientRepresentative(source, g);
    R := source`order_data`integer_ring;
    x := OrderElement(source`order_data, [R!(c @@ source`reduction_map) : c in Eltseq(reduced)]);
    return QuotientImage(target, x);
end function;


function verify_subgroup_image(source, target, H)
    return sub<target`group | [verify_image_in_model(source, target, g) : g in H]>;
end function;


function verify_reduction_kernel(source, target)
    return sub<source`group | [g : g in source`group |
                               verify_image_in_model(source, target, g) eq Identity(target`group)]>;
end function;


function verify_complement_of_type(complements, type_string)
    matches := [H : H in complements | verify_group_type(H) eq type_string];
    verify(#matches eq 1, "a Hurwitz complement type is not represented uniquely");
    return matches[1];
end function;


// Hurwitz order modulo 2 and 4 (complements H1, H2, H3 and their
// Theta sets), Lipschitz order modulo 2 and 4, and the maps between them.
verify_section("the Hurwitz and Lipschitz orders");

hamilton<i_h, j_h> := QuaternionAlgebra<Q | -1, -1>;
k_h := i_h * j_h;
hurwitz_order := Order([hamilton!1, i_h, k_h, (1 + i_h + j_h + k_h) / 2]);
hurwitz := ExplicitOrder(Q, hamilton, hurwitz_order);
hurwitz_integers := hurwitz`integer_ring;
hurwitz_mod_two := ReductionData(hurwitz, [], 2 * hurwitz_integers);
verify(Discriminant(hurwitz_order) eq 2 * hurwitz_integers and #hurwitz`unit_group eq 12,
       "the Hurwitz arithmetic data is incorrect");
verify(hurwitz_mod_two`injective and #hurwitz_mod_two`image_subgroup eq #hurwitz_mod_two`ambient_group,
       "Hurwitz reduction modulo two is not the asserted isomorphism");
verify(#hurwitz_mod_two`complement_classes eq 1 and #hurwitz_mod_two`complement_classes[1] eq 1,
       "the trivial Hurwitz complement modulo two was not recovered");
hurwitz_lifted_theta := TorsionObstruction(hurwitz_mod_two, 1);
verify(hurwitz_lifted_theta`modulus_ideal eq StabilizedModulus(2 * hurwitz_integers),
       "the Hurwitz lifted obstruction uses the wrong stabilized modulus");
verify(hurwitz_lifted_theta`theta_size eq 1 and not hurwitz_lifted_theta`theta_contains_one,
       "the Hurwitz lifted obstruction is not the asserted nonsquare class");

// ObstructionAtModulus uses a formula at ramified primes; compare it with a full scan.
hurwitz_ambient_modulus := StabilizedModulus(2 * hurwitz_integers);
hurwitz_ambient_theta := ObstructionAtModulus(hurwitz, hurwitz_ambient_modulus);
hurwitz_scan := theta_data(hurwitz, hurwitz_ambient_modulus);
scan_trace_zero(~hurwitz_scan, [[b : b in hurwitz_scan`base_ring] : i in [1..4]]);
verify(
    hurwitz_ambient_theta`delta_size eq 4 and
    hurwitz_ambient_theta`theta_size eq 3 and
    hurwitz_ambient_theta`theta_contains_one and
    {hurwitz_scan`delta_map(hurwitz_scan`base_ring!r) : r in hurwitz_ambient_theta`theta_representatives}
        eq hurwitz_scan`found,
    "the ramified-maximal ambient formula fails its dyadic definition check"
);

hurwitz_mod_four := ReductionData(hurwitz, [], 4 * hurwitz_integers);
verify(hurwitz_mod_four`injective and #hurwitz_mod_four`complement_classes eq 3,
       "the three Hurwitz complements modulo four were not recovered");
hurwitz_model_two := hurwitz_mod_two`factors[1]`quotient;
hurwitz_model_four := hurwitz_mod_four`factors[1]`quotient;
h1 := verify_complement_of_type(hurwitz_mod_four`complement_classes, "<8, 2>");
h2 := verify_complement_of_type(hurwitz_mod_four`complement_classes, "<8, 5>");
h3 := verify_complement_of_type(hurwitz_mod_four`complement_classes, "<8, 3>");
h1_theta := ObstructionAtSubgroup(hurwitz_model_four, h1);
h2_theta := ObstructionAtSubgroup(hurwitz_model_four, h2);
h3_theta := ObstructionAtSubgroup(hurwitz_model_four, h3);
verify(h1_theta`theta_size eq 0, "Theta_4(H1) is not empty");
verify(h2_theta`theta_size eq 1 and not h2_theta`theta_contains_one,
       "Theta_4(H2) is not the unique nonsquare class");
verify(h3_theta`theta_size eq 2 and h3_theta`theta_contains_one,
       "Theta_4(H3) does not contain both square classes");
verify(h2 eq verify_reduction_kernel(hurwitz_model_four, hurwitz_model_two),
       "H2 is not the kernel of reduction from four to two");

lipschitz_order := Order([hamilton!1, i_h, j_h, k_h]);
lipschitz := ExplicitOrder(Q, hamilton, lipschitz_order : OrderType := 1);
lipschitz_integers := lipschitz`integer_ring;
lipschitz_mod_two := ReductionData(lipschitz, [], 2 * lipschitz_integers);
verify(Discriminant(lipschitz_order) eq 4 * lipschitz_integers and
       verify_group_type(lipschitz`unit_group) eq "<4, 2>",
       "the Lipschitz arithmetic data is incorrect");
verify(lipschitz_mod_two`injective and verify_group_type(lipschitz_mod_two`ambient_group) eq "<8, 5>" and
       #lipschitz_mod_two`complement_classes eq 4,
       "the Lipschitz quotient or its four complements were not recovered");

lipschitz_model_two := lipschitz_mod_two`factors[1]`quotient;
verify(verify_projective_keys(lipschitz, [lipschitz`unit_map(u) : u in lipschitz`unit_group]) eq
           verify_projective_keys(lipschitz, [hamilton!1, i_h, j_h, k_h]),
       "Gamma_L,emptyset is not exactly the four displayed projective classes");
displayed_lipschitz_mod_two := [
    hamilton!1, j_h, 1 + i_h + j_h, 1 + i_h + k_h,
    i_h, k_h, 1 + j_h + k_h, i_h + j_h + k_h
];
verify({QuotientImage(lipschitz_model_two, x) : x in displayed_lipschitz_mod_two} eq
           Set(lipschitz_model_two`group),
       "G_L[2] is not exactly the eight displayed projective classes");
k_generators := [i_h + j_h + k_h, 1 + i_h + j_h, 1 + i_h + k_h, 1 + j_h + k_h];
k_subgroups := [sub<lipschitz_model_two`group | QuotientImage(lipschitz_model_two, x)> : x in k_generators];
verify(forall{K : K in k_subgroups | K in lipschitz_mod_two`complement_classes},
       "a displayed Lipschitz complement was not recovered");
// The paper compares traces in the algebra, not modulo 2 (where trace 2
// becomes 0), so it does not claim Theta_2(K_l) is empty.
verify(
    Trace(hamilton!1) ne 0 and
    #k_subgroups[1] eq 2 and Trace(k_generators[1]) eq 0 and
    &and[#k_subgroups[i] eq 2 and Trace(k_generators[i]) ne 0 : i in [2..4]],
    "the displayed Lipschitz trace-zero distinction failed"
);
verify(verify_reduction_kernel(lipschitz_model_two, hurwitz_model_two) eq k_subgroups[1],
       "the kernel of the Lipschitz-to-Hurwitz map is not K1");

lipschitz_mod_four := ReductionData(lipschitz, [], 4 * lipschitz_integers);
lipschitz_model_four := lipschitz_mod_four`factors[1]`quotient;
for i in [2..4] do
    lifts := [H : H in lipschitz_mod_four`complement_classes |
              verify_subgroup_image(lipschitz_model_four, lipschitz_model_two, H) eq k_subgroups[i]];
    verify(#lifts eq 1, "a trace-zero-free Lipschitz complement does not have a unique lift class");
    verify(IsConjugate(hurwitz_model_four`group,
                       verify_subgroup_image(lipschitz_model_four, hurwitz_model_four, lifts[1]), h1),
           "a trace-zero-free Lipschitz complement does not lift to H1");
end for;

print "[verify] Hurwitz and Lipschitz checks passed";
print "";
print "All verification checks passed.";
