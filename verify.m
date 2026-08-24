// Fast, fail-closed audit of Mendel--Yu's paper-facing finite computations.
//
// Run from code/:
//     magma verify.m
//
// This begins with a normalized-data integrity preflight and then recomputes
// the finite calculations used in Lemmas 32--34, Theorems 35, 38, and 50,
// Examples 19, 20, 37, and 49, Proposition 42, the stabilized modulus defined
// after Lemma 47, and Section 7.2. The full 49-order classification is run by
// reproduce.m; it is intentionally not repeated here.

// Use the same exact-algorithm choices as the isolated reproduction workers.
SetSeed(1);
load "load.m";
SetColumns(0);

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


function verify_join(strings, delimiter)
    if #strings eq 0 then
        return "";
    end if;
    result := strings[1];
    for i in [2..#strings] do
        result cat:= delimiter cat strings[i];
    end for;
    return result;
end function;


function verify_boolean(value, context)
    if value eq "true" then
        return true;
    end if;
    if value eq "false" then
        return false;
    end if;
    error Sprintf("Verification failed: %o must be true or false, got %o.", context, value);
end function;


function verify_integer(value, context)
    try
        result := StringToInteger(value);
    catch error_object
        error Sprintf("Verification failed: %o must be an integer, got %o.", context, value);
    end try;
    verify(Sprint(result) eq value, context cat " is not a canonical integer");
    return result;
end function;


// Split only at delimiters outside coordinate brackets.  Thus commas inside
// an ideal generator never separate ideals in a set.
function verify_split_outside_brackets(value, delimiter)
    verify(#delimiter gt 0, "an internal delimiter is empty");
    pieces := [];
    bracket_depth := 0;
    piece_start := 1;
    i := 1;

    while i le #value do
        if value[i] eq "[" then
            bracket_depth +:= 1;
        elif value[i] eq "]" then
            bracket_depth -:= 1;
            verify(bracket_depth ge 0, "unbalanced brackets in " cat value);
        end if;

        if bracket_depth eq 0 and
           i + #delimiter - 1 le #value and
           value[i..i + #delimiter - 1] eq delimiter then
            Append(~pieces, piece_start le i - 1 select value[piece_start..i - 1] else "");
            i +:= #delimiter;
            piece_start := i;
            continue;
        end if;
        i +:= 1;
    end while;

    verify(bracket_depth eq 0, "unbalanced brackets in " cat value);
    Append(~pieces, piece_start le #value select value[piece_start..#value] else "");
    return pieces;
end function;


// ---------------------------------------------------------------------------
// Minimal CSV reader (RFC 4180 quoting, one record per physical line)
// ---------------------------------------------------------------------------

function verify_csv_line(line)
    fields := [];
    i := 1;

    while i le #line do
        verify(line[i] eq "\"", "a CSV field is not quoted");
        i +:= 1;
        field := "";
        closed := false;

        while i le #line do
            character := line[i];
            if character eq "\"" then
                if i lt #line and line[i + 1] eq "\"" then
                    field cat:= "\"";
                    i +:= 2;
                    continue;
                end if;
                closed := true;
                i +:= 1;
                break;
            else
                field cat:= character;
            end if;
            i +:= 1;
        end while;

        verify(closed, "an input CSV line has an unterminated quoted field");
        Append(~fields, field);
        if i le #line then
            verify(line[i] eq ",", "characters follow a closing CSV quote");
            i +:= 1;
            verify(i le #line, "an input CSV line ends with a delimiter");
        end if;
    end while;

    verify(#fields gt 0, "an input CSV line has no fields");
    return fields;
end function;


// Split(..., "\n") leaves a carriage return when a CSV was written with
// RFC-style CRLF line endings.  Remove only that record terminator: Trim would
// also silently change legitimate leading or trailing field data.
function verify_csv_record(line)
    // Magma spells both "\n" and "\r" as byte 10 in string literals, so
    // inspect the byte value instead of comparing with a literal here.
    if #line gt 0 and StringToCode(line[#line]) eq 13 then
        return #line eq 1 select "" else line[1..#line - 1];
    end if;
    return line;
end function;


// Read one normalized CSV and enforce the publication contract byte for
// byte: every field quoted, exactly one final record terminator, no blank
// records, and rows in canonical sorted order.  reproduce.m publishes under
// the same contract, so a reproduced file is byte-identical exactly when
// its mathematical content agrees.
function verify_read_csv(filename, expected_headers)
    verify(FileExists(filename), "missing normalized data file " cat filename);
    contents := Read(filename);
    verify(
        #contents gt 0 and StringToCode(contents[#contents]) eq 10,
        filename cat " does not end with exactly one record terminator"
    );
    body_end := #contents - 1;
    if body_end gt 0 and StringToCode(contents[body_end]) eq 13 then
        body_end -:= 1;
    end if;
    verify(
        body_end eq 0 or StringToCode(contents[body_end]) notin {10, 13},
        filename cat " has more than one final record terminator"
    );
    record_has_data := false;
    for i in [1..#contents] do
        code := StringToCode(contents[i]);
        if code eq 10 then
            verify(record_has_data, filename cat " contains a blank record");
            record_has_data := false;
        elif code eq 13 then
            verify(
                record_has_data and i lt #contents and StringToCode(contents[i + 1]) eq 10,
                filename cat " contains a stray carriage return"
            );
        else
            record_has_data := true;
        end if;
    end for;
    lines := Split(contents, "\n");
    verify(#lines ge 1, filename cat " is empty");

    headers := verify_csv_line(verify_csv_record(lines[1]));
    verify(headers eq expected_headers, filename cat " has the wrong normalized schema");
    rows := [];
    serialized_rows := [];
    for line_number in [2..#lines] do
        line := verify_csv_record(lines[line_number]);
        verify(line ne "", Sprintf("%o has a blank record at line %o", filename, line_number));
        values := verify_csv_line(line);
        verify(
            #values eq #headers,
            Sprintf("%o line %o has %o fields; expected %o", filename, line_number, #values, #headers)
        );
        row := AssociativeArray();
        for i in [1..#headers] do
            row[headers[i]] := values[i];
        end for;
        Append(~rows, row);
        Append(~serialized_rows, line);
    end for;
    sorted_rows := [line : line in serialized_rows];
    Sort(~sorted_rows);
    verify(serialized_rows eq sorted_rows, filename cat " rows are not canonically ordered");
    return rows;
end function;


// ---------------------------------------------------------------------------
// Canonical ideal serialization
// ---------------------------------------------------------------------------

VerificationArithmeticFormat := recformat<field, integer_ring, algebra>;


function verify_arithmetic_input(index)
    entry := OneClassEntry(index);
    polynomial := Polynomial(entry[1]);
    field := Degree(polynomial) eq 1 select
        RationalsAsNumberField() else NumberField(polynomial);
    integer_ring := RingOfIntegers(field);
    algebra := QuaternionAlgebra<field | entry[3], entry[4]>;
    return rec<VerificationArithmeticFormat |
        field := field,
        integer_ring := integer_ring,
        algebra := algebra
    >;
end function;


// An ideal is serialized as "N:[c_1, ..., c_{d^2}]": its absolute norm
// followed by the entries of a d-by-d integral basis matrix in row-major
// order.  Rebuild the ideal from those basis rows, confirm the recorded
// norm, and round-trip through CanonicalIdealKey so distinct keys always
// name distinct ideals.
function verify_ideal_key(integer_ring, key, context)
    colon := Index(key, ":");
    verify(colon gt 1, context cat " is not a canonical ideal key");
    norm_value := verify_integer(key[1..colon - 1], context cat " norm");
    verify(norm_value ge 1, context cat " has nonpositive norm");
    coordinate_string := key[colon + 1..#key];
    verify(
        #coordinate_string ge 2 and coordinate_string[1] eq "[" and
        coordinate_string[#coordinate_string] eq "]",
        context cat " has malformed ideal-basis coordinates"
    );
    body := Trim(coordinate_string[2..#coordinate_string - 1]);
    coordinate_parts := Split(body, ",");
    coordinates := [
        verify_integer(Trim(part), context cat " ideal-basis coordinate") :
        part in coordinate_parts
    ];
    degree := Degree(integer_ring);
    verify(
        #coordinates eq degree^2,
        context cat " does not contain a full ideal-basis matrix"
    );
    basis_matrix := Matrix(Integers(), degree, degree, coordinates);
    ideal_x := ideal<integer_ring |
        [integer_ring!Eltseq(basis_matrix[i]) : i in [1..degree]]
    >;
    verify(Integers()!Norm(ideal_x) eq norm_value, context cat " has the wrong norm");
    verify(CanonicalIdealKey(ideal_x) eq key, context cat " is not canonically serialized");
    return ideal_x;
end function;


function verify_same_ideals(left, right)
    if #left ne #right then
        return false;
    end if;
    if #left eq 0 then
        return true;
    end if;
    return &and[left[i] eq right[i] : i in [1..#left]];
end function;


function verify_subset(integer_ring, value, context)
    if value eq "{}" then
        return [];
    end if;
    verify(
        #value ge 5 and value[1..2] eq "{ " and value[#value - 1..#value] eq " }",
        context cat " is not a canonical ideal subset"
    );
    body := value[3..#value - 2];
    keys := verify_split_outside_brackets(body, ", ");
    ideals := [verify_ideal_key(integer_ring, key, context) : key in keys];
    verify(verify_same_ideals(ideals, SortIdeals(ideals)), context cat " is not canonically ordered");
    verify(#Seqset(keys) eq #keys, context cat " contains a repeated prime");
    verify(
        value eq "{ " cat verify_join([CanonicalIdealKey(p) : p in ideals], ", ") cat " }",
        context cat " is not canonically serialized"
    );
    return ideals;
end function;


function verify_factorization(integer_ring, value, context)
    if value eq "1" then
        return 1 * integer_ring, [], [];
    end if;

    pieces := verify_split_outside_brackets(value, " * ");
    primes := [];
    exponents := [];
    for piece in pieces do
        caret := Index(piece, "^");
        verify(caret gt 1 and caret lt #piece, context cat " has a malformed prime-power factor");
        verify(Index(piece[caret + 1..#piece], "^") eq 0, context cat " has repeated exponent markers");
        prime_ideal := verify_ideal_key(integer_ring, piece[1..caret - 1], context);
        exponent := verify_integer(piece[caret + 1..#piece], context cat " exponent");
        verify(IsPrime(prime_ideal), context cat " contains a nonprime factor");
        verify(exponent ge 1, context cat " has a nonpositive exponent");
        Append(~primes, prime_ideal);
        Append(~exponents, exponent);
    end for;

    verify(verify_same_ideals(primes, SortIdeals(primes)), context cat " factors are not canonically ordered");
    verify(#Seqset([CanonicalIdealKey(p) : p in primes]) eq #primes, context cat " repeats a prime factor");
    canonical := verify_join([
        CanonicalIdealKey(primes[i]) cat "^" cat Sprint(exponents[i]) :
        i in [1..#primes]
    ], " * ");
    verify(value eq canonical, context cat " is not canonically serialized");

    ideal_x := 1 * integer_ring;
    for i in [1..#primes] do
        ideal_x *:= primes[i]^exponents[i];
    end for;
    return ideal_x, primes, exponents;
end function;


// Recompute the stabilized modulus defined after Mendel--Yu Lemma 47 prime by
// prime: every prime p
// dividing a must occur in e(a) with exponent max{v_p(a), 2*v_p(2) + 1}, and
// no other prime may occur.  This checks StabilizedModulus independently of
// its implementation in obstructions.m.
procedure verify_stabilized_formula(modulus_ideal)
    stabilized := StabilizedModulus(modulus_ideal);
    source_factors := Factorization(modulus_ideal);
    target_factors := Factorization(stabilized);
    verify(#source_factors eq #target_factors, "StabilizedModulus changed prime support");
    for source_factor in source_factors do
        prime_ideal := source_factor[1];
        expected_exponent := Maximum(
            source_factor[2],
            2 * Valuation(2 * Order(modulus_ideal), prime_ideal) + 1
        );
        verify(
            Valuation(stabilized, prime_ideal) eq expected_exponent,
            "StabilizedModulus disagrees with the exponent defined after Lemma 47"
        );
    end for;
end procedure;


function verify_group_order(type_string, context)
    if type_string eq "1" then
        return 1;
    end if;
    verify(
        #type_string ge 5 and type_string[1] eq "<" and type_string[#type_string] eq ">",
        context cat " is not an IdentifyGroup label"
    );
    parts := Split(type_string[2..#type_string - 1], ",");
    verify(#parts eq 2, context cat " is not an IdentifyGroup pair");
    order_value := verify_integer(Trim(parts[1]), context cat " group order");
    identifier := verify_integer(Trim(parts[2]), context cat " group identifier");
    verify(order_value ge 1 and identifier ge 1, context cat " has an invalid group identifier");
    group := SmallGroup(order_value, identifier);
    verify(Sprint(IdentifyGroup(group)) eq type_string, context cat " is not a canonical group identifier");
    return order_value;
end function;


function verify_group_key(order_index, subset_string)
    return order_index cat " || " cat subset_string;
end function;


function verify_minimal_key(order_index, subset_string, factorization_string)
    return verify_group_key(order_index, subset_string) cat " || " cat factorization_string;
end function;


// ---------------------------------------------------------------------------
// Normalized result contract
// ---------------------------------------------------------------------------

verify_section("classification-data integrity preflight");

algebra_headers := [
    "order_index", "base_field_degree", "base_field_discriminant",
    "algebra_discriminant", "ramified_primes", "gamma_emptyset_order",
    "discriminant_theta_applicable", "discriminant_modulus_factorization",
    "discriminant_theta_size", "discriminant_theta_contains_one"
];
localized_headers := [
    "order_index", "ramified_subset", "gamma_order", "gamma_type",
    "exclusion_reason"
];
minimal_headers := [
    "order_index", "ramified_subset", "modulus_norm",
    "modulus_factorization", "has_complement"
];
complement_headers := [
    "order_index", "ramified_subset", "modulus_norm",
    "modulus_factorization", "complement_index", "complement_order",
    "complement_is_normal", "theta_applicable",
    "theta_modulus_factorization", "theta_size", "theta_contains_one"
];

algebra_rows := verify_read_csv(data_directory cat "/algebras.csv", algebra_headers);
localized_rows := verify_read_csv(data_directory cat "/localized_groups.csv", localized_headers);
minimal_rows := verify_read_csv(data_directory cat "/minimal_ideals.csv", minimal_headers);
complement_rows := verify_read_csv(data_directory cat "/complements.csv", complement_headers);

class_indices := ClassOneOrderIndices();
verify(#class_indices eq 49, "the supplied Kirschmer--Voight table does not yield the paper's 49 orders");
verify(#algebra_rows eq #class_indices, "algebras.csv does not contain one row per class-number-one order");

algebras := AssociativeArray();
arithmetic_inputs := AssociativeArray();
algebra_discriminants := AssociativeArray();
ramified_primes := AssociativeArray();
gamma_emptyset_orders := AssociativeArray();

for row in algebra_rows do
    order_index_string := row["order_index"];
    order_index := verify_integer(order_index_string, "algebras.csv order_index");
    verify(Index(class_indices, order_index) ne 0, "algebras.csv refers to an ineligible table row");
    verify(not IsDefined(algebras, order_index_string), "algebras.csv repeats an order_index");

    arithmetic := verify_arithmetic_input(order_index);
    integer_ring := arithmetic`integer_ring;
    context := "algebras.csv order_index=" cat order_index_string;
    verify(
        verify_integer(row["base_field_degree"], context cat " base_field_degree") eq Degree(arithmetic`field),
        context cat " has the wrong base-field degree"
    );
    verify(
        verify_integer(row["base_field_discriminant"], context cat " base_field_discriminant") eq
            Integers()!Discriminant(integer_ring),
        context cat " has the wrong base-field discriminant"
    );

    algebra_discriminant := verify_ideal_key(integer_ring, row["algebra_discriminant"], context cat " D");
    verify(algebra_discriminant eq Discriminant(arithmetic`algebra), context cat " has the wrong algebra discriminant");
    stored_ramified := verify_subset(integer_ring, row["ramified_primes"], context cat " ramified_primes");
    actual_ramified := SortIdeals([factor[1] : factor in Factorization(algebra_discriminant)]);
    verify(verify_same_ideals(stored_ramified, actual_ramified), context cat " has the wrong ramified-prime set");

    gamma_order := verify_integer(row["gamma_emptyset_order"], context cat " gamma_emptyset_order");
    verify(gamma_order ge 1, context cat " has a nonpositive Gamma_emptyset order");
    applicable := verify_boolean(row["discriminant_theta_applicable"], context cat " discriminant_theta_applicable");
    theta_size := verify_integer(row["discriminant_theta_size"], context cat " discriminant_theta_size");
    theta_contains_one := verify_boolean(
        row["discriminant_theta_contains_one"],
        context cat " discriminant_theta_contains_one"
    );
    obstruction_modulus, _, _ := verify_factorization(
        integer_ring,
        row["discriminant_modulus_factorization"],
        context cat " discriminant_modulus_factorization"
    );
    verify_stabilized_formula(algebra_discriminant);
    verify(
        obstruction_modulus eq StabilizedModulus(algebra_discriminant),
        context cat " does not use the stabilized discriminant modulus"
    );
    verify(applicable eq (#actual_ramified gt 0), context cat " has the wrong obstruction applicability");
    verify(theta_size ge 0, context cat " has a negative obstruction-set size");
    verify(not theta_contains_one or theta_size gt 0, context cat " contains one but has empty Theta");
    if not applicable then
        verify(theta_size eq 0 and not theta_contains_one, context cat " assigns an obstruction to unit discriminant");
    end if;

    algebras[order_index_string] := row;
    arithmetic_inputs[order_index_string] := arithmetic;
    algebra_discriminants[order_index_string] := algebra_discriminant;
    ramified_primes[order_index_string] := stored_ramified;
    gamma_emptyset_orders[order_index_string] := gamma_order;
end for;

for index in class_indices do
    verify(IsDefined(algebras, Sprint(index)), "algebras.csv omits a class-number-one order");
end for;

localized := AssociativeArray();
localized_count := AssociativeArray();
for row in localized_rows do
    order_index := row["order_index"];
    verify(IsDefined(algebras, order_index), "localized_groups.csv refers to an unknown order");
    integer_ring := arithmetic_inputs[order_index]`integer_ring;
    context := "localized_groups.csv order_index=" cat order_index cat " T=" cat row["ramified_subset"];
    ramified_subset := verify_subset(integer_ring, row["ramified_subset"], context);
    verify(&and[Index(ramified_primes[order_index], p) ne 0 : p in ramified_subset], context cat " contains a nonramified prime");
    key := verify_group_key(order_index, row["ramified_subset"]);
    verify(not IsDefined(localized, key), context cat " is duplicated");

    gamma_order := verify_integer(row["gamma_order"], context cat " gamma_order");
    verify(gamma_order ge 1, context cat " has nonpositive group order");
    verify(verify_group_order(row["gamma_type"], context cat " gamma_type") eq gamma_order, context cat " group type has the wrong order");

    expected_reason := "";
    if gamma_emptyset_orders[order_index] eq 1 then
        if #ramified_subset eq 0 then
            expected_reason := "Gamma_emptyset=1 and T=emptyset";
        elif #ramified_subset eq 1 and #ramified_primes[order_index] eq 1 then
            expected_reason := "Gamma_emptyset=1, #T=1, and no distinct ramified modulus prime";
        end if;
    end if;
    verify(row["exclusion_reason"] eq expected_reason, context cat " has the wrong mathematical exclusion label");

    if #ramified_subset eq 0 then
        verify(gamma_order eq gamma_emptyset_orders[order_index], context cat " disagrees with algebras.csv");
    end if;
    localized[key] := row;
    localized_count[order_index] := IsDefined(localized_count, order_index)
        select localized_count[order_index] + 1 else 1;
end for;

for order_index in Keys(algebras) do
    verify(
        IsDefined(localized_count, order_index) and
        localized_count[order_index] eq 2^#ramified_primes[order_index],
        "localized_groups.csv does not contain the complete ramified-prime power set"
    );
end for;

minimal := AssociativeArray();
minimal_has_complement := AssociativeArray();
minimal_ideals_by_group := AssociativeArray();
complementary_minimal_count_by_order := AssociativeArray();
composite_complementary_keys := [];
for row in minimal_rows do
    order_index := row["order_index"];
    verify(IsDefined(algebras, order_index), "minimal_ideals.csv refers to an unknown order");
    integer_ring := arithmetic_inputs[order_index]`integer_ring;
    context := "minimal_ideals.csv order_index=" cat order_index cat " C=" cat row["modulus_factorization"];
    ramified_subset := verify_subset(integer_ring, row["ramified_subset"], context cat " T");
    group_key := verify_group_key(order_index, row["ramified_subset"]);
    verify(IsDefined(localized, group_key), context cat " refers to an unknown localized group");
    verify(localized[group_key]["exclusion_reason"] eq "", context cat " belongs to a mathematically excluded case");

    modulus, primes, exponents := verify_factorization(integer_ring, row["modulus_factorization"], context);
    modulus_norm := verify_integer(row["modulus_norm"], context cat " modulus_norm");
    verify(modulus_norm eq Integers()!Norm(modulus) and modulus_norm gt 1, context cat " has an incorrect modulus norm");
    gamma_order := verify_integer(localized[group_key]["gamma_order"], context cat " Gamma order");

    // Every row belongs to the finite relevant-prime poset used by the paper.
    for prime_ideal in primes do
        verify(
            Valuation(algebra_discriminants[order_index], prime_ideal) ne 0 or
            Norm(prime_ideal) le gamma_order,
            context cat " uses a split prime outside the paper's finite relevant-prime set"
        );
    end for;

    key := verify_minimal_key(order_index, row["ramified_subset"], row["modulus_factorization"]);
    verify(not IsDefined(minimal, key), context cat " is duplicated");
    has_complement := verify_boolean(row["has_complement"], context cat " has_complement");
    if has_complement then
        complementary_minimal_count_by_order[order_index] :=
            IsDefined(complementary_minimal_count_by_order, order_index)
                select complementary_minimal_count_by_order[order_index] + 1 else 1;
        if #primes ne 1 then
            Append(~composite_complementary_keys, key);
        end if;

        // Equality clause of the classification theorem: a complementary
        // modulus may involve a split prime of norm exactly #Gamma_T only
        // when Gamma_T is cyclic of order 2, 3, or 5 and C is that prime
        // itself to the first power.
        for prime_index in [1..#primes] do
            prime_ideal := primes[prime_index];
            if Valuation(algebra_discriminants[order_index], prime_ideal) eq 0 then
                prime_norm := Integers()!Norm(prime_ideal);
                if prime_norm eq gamma_order then
                    gamma_type := localized[group_key]["gamma_type"];
                    verify(
                        #primes eq 1 and exponents[1] eq 1 and
                        ((gamma_type eq "<2, 1>" and prime_norm eq 2) or
                         (gamma_type eq "<3, 1>" and prime_norm eq 3) or
                         (gamma_type eq "<5, 1>" and prime_norm eq 5)),
                        context cat " violates the equality clause of the classification theorem"
                    );
                end if;
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
    if localized[key]["exclusion_reason"] eq "" then
        verify(IsDefined(minimal_ideals_by_group, key), "a classified localized group has no minimal ideal");
    else
        verify(not IsDefined(minimal_ideals_by_group, key), "a mathematically excluded group has minimal-ideal rows");
    end if;
end for;
for group_key in Keys(minimal_ideals_by_group) do
    ideals := minimal_ideals_by_group[group_key];
    for i in [1..#ideals] do
        for j in [i + 1..#ideals] do
            verify(
                not (ideals[i] subset ideals[j]) and not (ideals[j] subset ideals[i]),
                "minimal_ideals.csv contains comparable ideals for one localized group"
            );
        end for;
    end for;
end for;

complement_count_by_minimal := AssociativeArray();
complement_indices := AssociativeArray();
complement_order_by_minimal := AssociativeArray();
for row in complement_rows do
    order_index := row["order_index"];
    verify(IsDefined(algebras, order_index), "complements.csv refers to an unknown order");
    integer_ring := arithmetic_inputs[order_index]`integer_ring;
    context := "complements.csv order_index=" cat order_index cat " C=" cat row["modulus_factorization"];
    ramified_subset := verify_subset(integer_ring, row["ramified_subset"], context cat " T");
    modulus, modulus_primes, _ := verify_factorization(integer_ring, row["modulus_factorization"], context);
    verify(
        verify_integer(row["modulus_norm"], context cat " modulus_norm") eq Integers()!Norm(modulus),
        context cat " has an incorrect modulus norm"
    );
    minimal_key := verify_minimal_key(order_index, row["ramified_subset"], row["modulus_factorization"]);
    verify(IsDefined(minimal, minimal_key), context cat " has no corresponding minimal ideal");
    verify(minimal_has_complement[minimal_key], context cat " contradicts has_complement=false");

    complement_index := verify_integer(row["complement_index"], context cat " complement_index");
    verify(complement_index ge 1, context cat " has a nonpositive complement index");
    index_key := minimal_key cat " || " cat Sprint(complement_index);
    verify(not IsDefined(complement_indices, index_key), context cat " repeats a complement index");
    complement_indices[index_key] := true;
    complement_count_by_minimal[minimal_key] := IsDefined(complement_count_by_minimal, minimal_key)
        select complement_count_by_minimal[minimal_key] + 1 else 1;

    complement_order := verify_integer(row["complement_order"], context cat " complement_order");
    verify(complement_order ge 1, context cat " has a nonpositive complement order");
    if IsDefined(complement_order_by_minimal, minimal_key) then
        verify(complement_order_by_minimal[minimal_key] eq complement_order, context cat " complement classes have different orders");
    else
        complement_order_by_minimal[minimal_key] := complement_order;
    end if;
    _ := verify_boolean(row["complement_is_normal"], context cat " complement_is_normal");

    // The complement torsion obstruction is defined exactly when the
    // modulus C is coprime to the ramified subset T; the classification
    // computes it only for prime-power moduli.
    expected_applicability := not exists{
        prime_ideal : prime_ideal in modulus_primes | Index(ramified_subset, prime_ideal) ne 0
    };
    applicable := verify_boolean(row["theta_applicable"], context cat " theta_applicable");
    verify(applicable eq expected_applicability, context cat " has the wrong mathematical obstruction applicability");
    if applicable then
        verify(#modulus_primes eq 1, context cat " applies a complement obstruction to a non-prime-power modulus");
        theta_modulus, _, _ := verify_factorization(
            integer_ring,
            row["theta_modulus_factorization"],
            context cat " theta_modulus_factorization"
        );
        verify_stabilized_formula(modulus);
        verify(theta_modulus eq StabilizedModulus(modulus), context cat " does not use the stabilized obstruction modulus");
        theta_size := verify_integer(row["theta_size"], context cat " theta_size");
        theta_contains_one := verify_boolean(row["theta_contains_one"], context cat " theta_contains_one");
        verify(theta_size ge 0, context cat " has negative theta_size");
        verify(not theta_contains_one or theta_size gt 0, context cat " contains one but has empty Theta");
    else
        verify(
            row["theta_modulus_factorization"] eq "" and row["theta_size"] eq "" and
            row["theta_contains_one"] eq "",
            context cat " records an obstruction where the paper defines none"
        );
    end if;
end for;

for key in Keys(minimal) do
    if minimal_has_complement[key] then
        verify(IsDefined(complement_count_by_minimal, key), "a complementary ideal has no complement rows");
        count := complement_count_by_minimal[key];
        for index in [1..count] do
            verify(IsDefined(complement_indices, key cat " || " cat Sprint(index)), "complement indices are not consecutive");
        end for;
    else
        verify(not IsDefined(complement_count_by_minimal, key), "a noncomplementary ideal has complement rows");
    end if;
end for;

complementary_minimal_keys := [key : key in Keys(minimal) | minimal_has_complement[key]];
verify(
    #Keys(complement_count_by_minimal) eq #complementary_minimal_keys,
    "the complement rows do not cover exactly the complementary minimal ideals"
);

verify_section("Theorem 35, Theorem 38, Example 37, and Proposition 42");

// Classification-wide consequences of the normalized data.
for order_index in Keys(algebras) do
    if gamma_emptyset_orders[order_index] ne 1 or #ramified_primes[order_index] gt 1 then
        verify(
            IsDefined(complementary_minimal_count_by_order, order_index) and
            complementary_minimal_count_by_order[order_index] gt 0,
            "an algebra covered by the nonemptiness theorem has empty M(B)"
        );
    end if;
end for;

// The paper's discriminant-seven example: over the real cyclotomic cubic
// field of discriminant 49, the algebra with N(D) = 7 has Gamma_emptyset
// isomorphic to D7 (order 14), Gamma_T isomorphic to D14 (order 28) at
// T = {p7}, and a unique minimal complementary triple with C the norm-27
// prime.
d7_order_indices := [
    order_index : order_index in Keys(algebras) |
    Degree(arithmetic_inputs[order_index]`field) eq 3 and
    Integers()!Discriminant(arithmetic_inputs[order_index]`integer_ring) eq 49 and
    Integers()!Norm(algebra_discriminants[order_index]) eq 7
];
verify(#d7_order_indices eq 1, "the real-cyclotomic discriminant-seven example is not unique");
d7_order_index := d7_order_indices[1];
d7_ramified := ramified_primes[d7_order_index];
verify(#d7_ramified eq 1 and Norm(d7_ramified[1]) eq 7,
       "the discriminant-seven example has the wrong ramified prime");
d7_subset_string := "{ " cat CanonicalIdealKey(d7_ramified[1]) cat " }";
d7_empty_key := verify_group_key(d7_order_index, "{}");
d7_localized_key := verify_group_key(d7_order_index, d7_subset_string);
verify(
    localized[d7_empty_key]["gamma_order"] eq "14" and
    localized[d7_empty_key]["gamma_type"] eq "<14, 1>" and
    localized[d7_localized_key]["gamma_order"] eq "28" and
    localized[d7_localized_key]["gamma_type"] eq "<28, 3>",
    "the discriminant-seven example does not have Gamma_emptyset=D7 and Gamma_T=D14"
);
d7_minimal_keys := [
    key : key in complementary_minimal_keys |
    minimal[key]["order_index"] eq d7_order_index
];
d7_complement_rows := [row : row in complement_rows | row["order_index"] eq d7_order_index];
verify(#d7_minimal_keys eq 1 and #d7_complement_rows eq 1,
       "the discriminant-seven example does not have a unique minimal complementary triple");
d7_row := minimal[d7_minimal_keys[1]];
d7_modulus, d7_factors, d7_exponents := verify_factorization(
    arithmetic_inputs[d7_order_index]`integer_ring,
    d7_row["modulus_factorization"],
    "discriminant-seven example"
);
verify(
    d7_row["ramified_subset"] eq d7_subset_string and
    Integers()!Norm(d7_modulus) eq 27 and #d7_factors eq 1 and
    d7_exponents[1] eq 1 and Norm(d7_factors[1]) eq 27,
    "the discriminant-seven example is not the stated T={p7}, C=p27 triple"
);

// The unique composite complementary modulus in the entire classification:
// over the real cyclotomic cubic field of discriminant 81, the algebra with
// N(D) = 3 has its single minimal triple at T = {p3} with N(C) = 24, the
// product of the ramified norm-3 prime and a split norm-8 prime.
zeta9_order_indices := [
    order_index : order_index in Keys(algebras) |
    Degree(arithmetic_inputs[order_index]`field) eq 3 and
    Integers()!Discriminant(arithmetic_inputs[order_index]`integer_ring) eq 81 and
    Integers()!Norm(algebra_discriminants[order_index]) eq 3
];
verify(#zeta9_order_indices eq 1, "the real-cyclotomic composite-modulus case is not unique");
zeta9_order_index := zeta9_order_indices[1];
zeta9_ramified := ramified_primes[zeta9_order_index];
verify(#zeta9_ramified eq 1 and Norm(zeta9_ramified[1]) eq 3,
       "the real-cyclotomic composite-modulus case has the wrong ramified prime");
zeta9_subset_string := "{ " cat CanonicalIdealKey(zeta9_ramified[1]) cat " }";
zeta9_minimal_keys := [
    key : key in complementary_minimal_keys |
    minimal[key]["order_index"] eq zeta9_order_index
];
zeta9_complement_rows := [row : row in complement_rows | row["order_index"] eq zeta9_order_index];
verify(
    #composite_complementary_keys eq 1 and
    #zeta9_minimal_keys eq 1 and zeta9_minimal_keys[1] eq composite_complementary_keys[1] and
    #zeta9_complement_rows eq 1,
    "the composite complementary modulus is not the unique stated element of M(B)"
);
zeta9_row := minimal[zeta9_minimal_keys[1]];
zeta9_modulus, zeta9_factors, zeta9_exponents := verify_factorization(
    arithmetic_inputs[zeta9_order_index]`integer_ring,
    zeta9_row["modulus_factorization"],
    "real-cyclotomic composite-modulus case"
);
verify(
    zeta9_row["ramified_subset"] eq zeta9_subset_string and
    Integers()!Norm(zeta9_modulus) eq 24 and #zeta9_factors eq 2 and
    {Integers()!Norm(prime_ideal) : prime_ideal in zeta9_factors} eq {3, 8} and
    &and[exponent eq 1 : exponent in zeta9_exponents] and
    Index(zeta9_factors, zeta9_ramified[1]) ne 0,
    "the unique composite case is not the stated T={p3}, N(C)=24 triple"
);

verify_section("proof of Theorem 50: rational torsion obstructions");

// The rational torsion theorem uses one of the two applicable obstruction
// sets for every nontrivial empty-T triple; D=13 handles the trivial family.
for row in complement_rows do
    order_index := row["order_index"];
    if Degree(arithmetic_inputs[order_index]`field) eq 1 and row["ramified_subset"] eq "{}" then
        complement_excludes_one :=
            verify_boolean(row["theta_applicable"], "rational complement theta_applicable") and
            not verify_boolean(row["theta_contains_one"], "rational complement theta_contains_one");
        algebra_excludes_one :=
            verify_boolean(algebras[order_index]["discriminant_theta_applicable"], "rational discriminant theta_applicable") and
            not verify_boolean(algebras[order_index]["discriminant_theta_contains_one"], "rational discriminant theta_contains_one");
        verify(complement_excludes_one or algebra_excludes_one,
               "a rational empty-T triple has neither torsion obstruction");
    end if;
end for;
rational_d13_indices := [
    order_index : order_index in Keys(algebras) |
    Degree(arithmetic_inputs[order_index]`field) eq 1 and
    Integers()!Norm(algebra_discriminants[order_index]) eq 13
];
verify(#rational_d13_indices eq 1, "the rational discriminant-thirteen algebra is not unique");
rational_d13_row := algebras[rational_d13_indices[1]];
verify(
    verify_boolean(rational_d13_row["discriminant_theta_applicable"], "D=13 theta_applicable") and
    not verify_boolean(rational_d13_row["discriminant_theta_contains_one"], "D=13 theta_contains_one"),
    "the rational discriminant-thirteen obstruction contains one"
);

print Sprintf(
    "[verify] data passed: %o algebras, %o localized groups, %o mathematically derived minimal ideals, %o complements",
    #algebra_rows, #localized_rows, #minimal_rows, #complement_rows
);


// ---------------------------------------------------------------------------
// Independent exact checks
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

// Build all paper orders once.  This independently checks the computational
// unit-norm lemma and supplies the two displayed examples without naming table
// row numbers.
orders := AssociativeArray();
unit_representative_count := 0;
for index in class_indices do
    // Reproduce each isolated worker's random state before exact order
    // construction, so canonical prime-ideal representatives agree as well.
    SetSeed(1);
    order_data := ClassOneOrder(index);
    orders[Sprint(index)] := order_data;
    verify(#order_data`unit_elements eq #order_data`unit_group, "unit representatives do not enumerate the unit quotient");
    for unit in order_data`unit_elements do
        verify(Norm(unit) eq order_data`base_field!1, "a projective unit representative does not have reduced norm one");
        unit_representative_count +:= 1;
    end for;
end for;
print Sprintf("[verify] unit-norm lemma passed for %o representatives", unit_representative_count);


function verify_integral_coordinates(order_data, element)
    coordinates := OrderCoordinates(order_data, element);
    verify(&and[coordinate in order_data`integer_ring : coordinate in coordinates],
           "a normalizer representative has a nonintegral order coordinate");
    return [order_data`integer_ring!coordinate : coordinate in coordinates];
end function;


// A projective class can enter the kernel modulo p only when its order-basis
// coordinate vector becomes proportional to the identity vector.  The 2-by-2
// minors therefore give a finite, exhaustive set of possible split primes.
function verify_scalar_collision_primes(order_data, element)
    integer_ring := order_data`integer_ring;
    identity_coordinates := verify_integral_coordinates(
        order_data,
        order_data`quaternion_order!1
    );
    element_coordinates := verify_integral_coordinates(order_data, element);
    minors := [];
    for i in [1..4] do
        for j in [i + 1..4] do
            minor := identity_coordinates[i] * element_coordinates[j] -
                     identity_coordinates[j] * element_coordinates[i];
            if minor ne integer_ring!0 then
                Append(~minors, minor);
            end if;
        end for;
    end for;

    if #minors eq 0 then
        return [], true;
    end if;
    collision_ideal := ideal<integer_ring | minors>;
    return SortIdeals([factor[1] : factor in Factorization(collision_ideal)]), false;
end function;


function verify_split_collision_primes(order_data, context, localized_group)
    split_primes := [];
    nonidentity_count := 0;
    for group_element in localized_group`subgroup do
        if group_element eq Identity(localized_group`subgroup) then
            continue;
        end if;
        nonidentity_count +:= 1;
        representative := complementary_normalizer_representative(context, group_element);
        collision_primes, is_scalar := verify_scalar_collision_primes(order_data, representative);
        verify(not is_scalar, "a nonidentity localized-unit class has a scalar representative");
        for prime_ideal in collision_primes do
            if Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) eq 0 then
                AppendIdeal(~split_primes, prime_ideal);
            end if;
        end for;
    end for;
    return SortIdeals(split_primes), nonidentity_count;
end function;


procedure verify_split_prime_injective(~context, localized_group, prime_ideal, claim)
    local_result := false;
    complementary_local_reduction_image(
        ~context,
        localized_group,
        prime_ideal,
        1,
        ~local_result :
        Print := 0
    );
    verify(
        #local_result`image_subgroup eq localized_group`subgroup_order,
        claim cat " at " cat CanonicalIdealKey(prime_ideal)
    );
end procedure;


// For every localized group, the collision minors above give the finitely
// many split primes at which some nonidentity projective class could reduce
// to the identity.  Verify the paper's finite injectivity lemmas at every
// candidate: the Gamma_emptyset = C2 case, the singleton-T C2 case with
// Gamma_emptyset = 1, and every split prime of norm above #Gamma_T all
// reduce injectively.  The loop also isolates the unique order with
// Gamma_emptyset = 1 and two ramified primes for the exceptional case below.
verify_section("proofs of Lemma 33(ii), Lemma 34, and Theorem 35");
empty_c2_case_count := 0;
singleton_c2_case_count := 0;
localized_nonidentity_count := 0;
large_norm_candidate_count := 0;
distinct_ramified_orders := [];

for index in class_indices do
    order_data := orders[Sprint(index)];
    context, localized_groups := complementary_context_with_all_U_T(order_data);
    empty_groups := [group : group in localized_groups | #group`ramified_subset eq 0];
    verify(#empty_groups eq 1, "an order does not have a unique Gamma_emptyset record");
    gamma_emptyset := empty_groups[1];

    if gamma_emptyset`subgroup_order eq 1 and #RamifiedPrimes(order_data) gt 1 then
        Append(~distinct_ramified_orders, order_data);
    end if;

    for localized_group in localized_groups do
        subset_string := #localized_group`ramified_subset eq 0 select "{}" else
            "{ " cat verify_join(
                [CanonicalIdealKey(prime_ideal) : prime_ideal in SortIdeals(localized_group`ramified_subset)],
                ", "
            ) cat " }";
        group_key := verify_group_key(Sprint(index), subset_string);
        verify(
            IsDefined(localized, group_key),
            Sprintf("localized_groups.csv omits order %o and T=%o", index, subset_string)
        );
        csv_group := localized[group_key];
        exact_type := localized_group`subgroup_order eq 1 select
            "1" else Sprint(IdentifyGroup(localized_group`subgroup));
        verify(
            csv_group["gamma_order"] eq Sprint(localized_group`subgroup_order) and
            csv_group["gamma_type"] eq exact_type and
            csv_group["exclusion_reason"] eq
                ClassificationExclusionReason(gamma_emptyset, localized_group),
            "localized_groups.csv disagrees with an exact localized-unit computation"
        );

        split_primes, element_count := verify_split_collision_primes(
            order_data,
            context,
            localized_group
        );
        localized_nonidentity_count +:= element_count;

        empty_c2_case :=
            #localized_group`ramified_subset eq 0 and
            localized_group`subgroup_order eq 2;
        singleton_c2_case :=
            gamma_emptyset`subgroup_order eq 1 and
            #localized_group`ramified_subset eq 1 and
            localized_group`subgroup_order eq 2;
        if empty_c2_case then
            empty_c2_case_count +:= 1;
        end if;
        if singleton_c2_case then
            singleton_c2_case_count +:= 1;
        end if;

        for prime_ideal in split_primes do
            if empty_c2_case then
                verify_split_prime_injective(
                    ~context,
                    localized_group,
                    prime_ideal,
                    "Gamma_emptyset=C2 is not injective at a possible collision prime"
                );
            end if;
            if singleton_c2_case then
                verify_split_prime_injective(
                    ~context,
                    localized_group,
                    prime_ideal,
                    "the singleton-T C2 group is not injective at a possible collision prime"
                );
            end if;
            if Norm(prime_ideal) gt localized_group`subgroup_order then
                large_norm_candidate_count +:= 1;
                verify_split_prime_injective(
                    ~context,
                    localized_group,
                    prime_ideal,
                    "a split prime above #Gamma_T has noninjective reduction"
                );
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

// Verify the sole distinct-ramified singleton case by its arithmetic
// characterization and by the exact minimal-ideal traversal in both directions.
exceptional_order := distinct_ramified_orders[1];
verify(
    Degree(exceptional_order`base_field) eq 2 and
    Integers()!Discriminant(exceptional_order`integer_ring) eq 8,
    "the distinct-ramified singleton case is not defined over Q(sqrt(2))"
);
exceptional_ramified := RamifiedPrimes(exceptional_order);
norm_two_primes := [prime_ideal : prime_ideal in exceptional_ramified | Norm(prime_ideal) eq 2];
norm_twenty_five_primes := [prime_ideal : prime_ideal in exceptional_ramified | Norm(prime_ideal) eq 25];
verify(
    #exceptional_ramified eq 2 and #norm_two_primes eq 1 and #norm_twenty_five_primes eq 1,
    "the distinct-ramified singleton case does not have ramified norms 2 and 25"
);
ramified_two := norm_two_primes[1];
ramified_twenty_five := norm_twenty_five_primes[1];

from_two := MinimalComplementaryIdeals(exceptional_order, [ramified_two] : Print := 0);
to_twenty_five := [
    i : i in [1..#from_two`minimal_injective_ideals] |
    #Factorization(from_two`minimal_injective_ideals[i]) eq 1 and
    Factorization(from_two`minimal_injective_ideals[i])[1][1] eq ramified_twenty_five
];
verify(#to_twenty_five eq 1, "the norm-25 direction has no unique minimal injective ideal");
exceptional_result := from_two`minimal_results[to_twenty_five[1]];
verify(
    from_two`localized_unit_group`subgroup_order eq 2 and
    from_two`minimal_injective_ideals[to_twenty_five[1]] eq ramified_twenty_five and
    #exceptional_result`complement_classes eq 1 and
    #exceptional_result`normal_complement_classes eq 1,
    "the stated norm-25 minimal complementary triple was not recovered"
);

from_twenty_five := MinimalComplementaryIdeals(
    exceptional_order,
    [ramified_twenty_five] :
    Print := 0
);
to_two := [
    i : i in [1..#from_twenty_five`minimal_injective_ideals] |
    #Factorization(from_twenty_five`minimal_injective_ideals[i]) eq 1 and
    Factorization(from_twenty_five`minimal_injective_ideals[i])[1][1] eq ramified_two
];
verify(#to_two eq 1, "the reverse ramified direction has no unique minimal injective ideal");
reverse_ramified_result := from_twenty_five`minimal_results[to_two[1]];
verify(
    from_twenty_five`localized_unit_group`subgroup_order eq 2 and
    #reverse_ramified_result`complement_classes eq 0,
    "the reverse ramified direction unexpectedly gives a minimal complementary triple"
);
print "[verify] unique distinct-ramified singleton case passed";


function verify_unique_order(orders, degree, field_discriminant, algebra_discriminant_norm)
    matches := [];
    for key in Keys(orders) do
        order_data := orders[key];
        if Degree(order_data`base_field) eq degree and
           Integers()!Discriminant(order_data`integer_ring) eq field_discriminant and
           Integers()!Norm(Discriminant(order_data`quaternion_algebra)) eq algebra_discriminant_norm then
            Append(~matches, order_data);
        end if;
    end for;
    verify(#matches eq 1, "a displayed example is not uniquely determined by its paper invariants");
    return matches[1];
end function;


function verify_string_set(values)
    return {value : value in values};
end function;


function verify_projective_keys(order_data, elements)
    return verify_string_set([
        Sprint(Eltseq(ProjectiveRepresentative(order_data`quaternion_algebra, element))) :
        element in elements
    ]);
end function;


function verify_displayed_representative(order_data, representatives, expected)
    expected_class := ProjectiveRepresentative(order_data`quaternion_algebra, expected);
    matches := [
        representative : representative in representatives |
        ProjectiveRepresentative(order_data`quaternion_algebra, representative) eq expected_class
    ];
    verify(#matches eq 1, "a displayed generator class was not recovered uniquely");
    return matches[1];
end function;


function verify_relation_word(prime_p, prime_q, a, b, indices)
    return [
        <prime_p, a[indices[1]]>,
        <prime_q, b[indices[2]]>,
        <prime_p, a[indices[3]]>,
        <prime_q, b[indices[4]]>
    ];
end function;


function verify_relation_keys(presentation, relation_words)
    return {
        Sprint(canonical_relation_representative(presentation`inverse_map, relation_word)) :
        relation_word in relation_words
    };
end function;


function verify_computed_relation_keys(presentation)
    return {
        Sprint(canonical_relation_representative(presentation`inverse_map, relation_word)) :
        relation_word in Keys(presentation`minimal_square_relations)
    };
end function;


procedure verify_inverse_pairs(presentation, prime_ideal, representatives, pairs)
    for pair in pairs do
        verify(
            presentation`inverse_map[prime_ideal][representatives[pair[1]]] eq representatives[pair[2]] and
            presentation`inverse_map[prime_ideal][representatives[pair[2]]] eq representatives[pair[1]],
            "a displayed inverse relation was not recovered"
        );
    end for;
end procedure;


// The quadratic example names generators only by their inverse and square
// relations.  MaximalRightIdeals supplies the same eight projective classes in
// an unspecified order, so recover the paper's labels rather than comparing
// its subscripts with that implementation order.
function verify_inverse_compatible_labelings(presentation, prime_ideal, representatives, pairs)
    labelings := [];
    for permutation in Sym(#representatives) do
        labeling := [representatives[i^permutation] : i in [1..#representatives]];
        if &and[
            presentation`inverse_map[prime_ideal][labeling[pair[1]]] eq labeling[pair[2]] and
            presentation`inverse_map[prime_ideal][labeling[pair[2]]] eq labeling[pair[1]] :
            pair in pairs
        ] then
            Append(~labelings, labeling);
        end if;
    end for;
    return labelings;
end function;


function verify_displayed_relation_labeling(
    presentation,
    prime_p,
    prime_q,
    representatives_p,
    representatives_q,
    inverse_pairs_p,
    inverse_pairs_q,
    relation_indices
)
    computed_keys := verify_computed_relation_keys(presentation);
    p_labelings := verify_inverse_compatible_labelings(
        presentation,
        prime_p,
        representatives_p,
        inverse_pairs_p
    );
    q_labelings := verify_inverse_compatible_labelings(
        presentation,
        prime_q,
        representatives_q,
        inverse_pairs_q
    );

    for labeled_p in p_labelings do
        for labeled_q in q_labelings do
            displayed_words := [
                verify_relation_word(prime_p, prime_q, labeled_p, labeled_q, indices) :
                indices in relation_indices
            ];
            if verify_relation_keys(presentation, displayed_words) eq computed_keys then
                return true, labeled_p, labeled_q;
            end if;
        end for;
    end for;

    return false, representatives_p, representatives_q;
end function;


verify_section("Examples 19, 20, and 49: presentations and torsion");

// The rational displayed presentation: for the algebra of discriminant 5
// over Q with level C = (5), the presentation at S = {2, 3} has generator
// counts 3 and 4, six square relators, and abelianization (Z/2)^2, with
// exactly the displayed generator classes and relators recovered below.
rational_order := verify_unique_order(orders, 1, 1, 5);
rational_integers := rational_order`integer_ring;
rational_level := 5 * rational_integers;
rational_result := ReductionData(rational_order, [], rational_level : Print := 0);
verify(rational_result`injective and #rational_result`complement_classes gt 0,
       "the rational displayed complementary triple was not recovered");
rational_presentation := PresentationForComplement(
    rational_result,
    [2 * rational_integers, 3 * rational_integers] :
    Print := 0
);
verify([#rational_presentation`a_representatives[p] : p in rational_presentation`s_prime_ideals] eq [3, 4],
       "the rational presentation has the wrong local generator counts");
verify(#rational_presentation`minimal_square_relations eq 6,
       "the rational presentation has the wrong square-relation count");
verify(AbelianQuotientInvariants(rational_presentation`gamma_group) eq [2, 2],
       "the rational presentation has the wrong abelianization");

rational_algebra := rational_order`quaternion_algebra;
i := rational_algebra.1;
j := rational_algebra.2;
k := i * j;
expected_norm_two := [i, i - 2*j + k, -i - 2*j - k];
expected_norm_three := [3*i - 2*j - k, i + k, 3*i + 2*j - k, i - k];
verify(
    verify_projective_keys(rational_order, rational_presentation`a_representatives[rational_presentation`s_prime_ideals[1]]) eq
        verify_projective_keys(rational_order, expected_norm_two),
    "the rational presentation's norm-two generators differ from the displayed classes"
);
verify(
    verify_projective_keys(rational_order, rational_presentation`a_representatives[rational_presentation`s_prime_ideals[2]]) eq
        verify_projective_keys(rational_order, expected_norm_three),
    "the rational presentation's norm-three generators differ from the displayed classes"
);
rational_p := rational_presentation`s_prime_ideals[1];
rational_q := rational_presentation`s_prime_ideals[2];
rational_a := [
    verify_displayed_representative(
        rational_order,
        rational_presentation`a_representatives[rational_p],
        expected
    ) : expected in expected_norm_two
];
rational_b := [
    verify_displayed_representative(
        rational_order,
        rational_presentation`a_representatives[rational_q],
        expected
    ) : expected in expected_norm_three
];
verify_inverse_pairs(rational_presentation, rational_p, rational_a, [<1, 1>, <2, 2>, <3, 3>]);
verify_inverse_pairs(rational_presentation, rational_q, rational_b, [<1, 1>, <2, 2>, <3, 3>, <4, 4>]);
rational_relation_indices := [
    <2, 3, 1, 3>, <1, 4, 1, 2>, <2, 1, 2, 4>,
    <3, 2, 2, 2>, <3, 1, 1, 1>, <3, 4, 3, 3>
];
rational_relation_words := [
    verify_relation_word(rational_p, rational_q, rational_a, rational_b, indices) :
    indices in rational_relation_indices
];
verify(
    verify_computed_relation_keys(rational_presentation) eq
    verify_relation_keys(rational_presentation, rational_relation_words),
    "the rational presentation does not have exactly the six displayed square relators"
);

quadratic_order := verify_unique_order(orders, 2, 8, 18);
quadratic_integers := quadratic_order`integer_ring;
quadratic_level := [factor[1] : factor in Factorization(2 * quadratic_integers)][1];
quadratic_s_primes := SortIdeals([factor[1] : factor in Factorization(7 * quadratic_integers)]);
verify(#quadratic_s_primes eq 2 and &and[Norm(p) eq 7 : p in quadratic_s_primes],
       "the quadratic example does not have the two required split primes");
quadratic_result := ReductionData(quadratic_order, [], quadratic_level : Print := 0);
verify(quadratic_result`injective and #quadratic_result`complement_classes gt 0,
       "the quadratic displayed complementary triple was not recovered");
quadratic_presentation := PresentationForComplement(
    quadratic_result,
    quadratic_s_primes :
    Print := 0
);
verify([#quadratic_presentation`a_representatives[p] : p in quadratic_presentation`s_prime_ideals] eq [8, 8],
       "the quadratic presentation has the wrong local generator counts");
verify(#quadratic_presentation`minimal_square_relations eq 16,
       "the quadratic presentation has the wrong square-relation count");
verify(quadratic_presentation`generators_torsion_free and #quadratic_presentation`square_torsion eq 0,
       "the displayed edge/face torsion checks failed");
verify(AbelianQuotientInvariants(quadratic_presentation`gamma_group) eq [2, 2, 2, 10],
       "the quadratic presentation has the wrong abelianization");
quadratic_p := quadratic_presentation`s_prime_ideals[1];
quadratic_q := quadratic_presentation`s_prime_ideals[2];
quadratic_a := quadratic_presentation`a_representatives[quadratic_p];
quadratic_b := quadratic_presentation`a_representatives[quadratic_q];
quadratic_inverse_pairs_a := [<1, 3>, <2, 8>, <4, 5>, <6, 7>];
quadratic_inverse_pairs_b := [<1, 7>, <2, 8>, <3, 4>, <5, 6>];
quadratic_relation_indices := [
    <4, 4, 3, 2>, <2, 8, 8, 2>, <7, 5, 8, 1>, <7, 6, 2, 7>,
    <4, 1, 2, 4>, <7, 4, 6, 3>, <4, 7, 6, 8>, <4, 3, 2, 1>,
    <1, 5, 7, 2>, <1, 2, 6, 5>, <4, 2, 3, 3>, <4, 5, 5, 6>,
    <1, 4, 8, 6>, <1, 1, 3, 7>, <1, 6, 8, 3>, <4, 8, 7, 7>
];
quadratic_labels_found,
quadratic_a,
quadratic_b := verify_displayed_relation_labeling(
    quadratic_presentation,
    quadratic_p,
    quadratic_q,
    quadratic_a,
    quadratic_b,
    quadratic_inverse_pairs_a,
    quadratic_inverse_pairs_b,
    quadratic_relation_indices
);
if not quadratic_labels_found then
    quadratic_labels_found,
    quadratic_a,
    quadratic_b := verify_displayed_relation_labeling(
        quadratic_presentation,
        quadratic_q,
        quadratic_p,
        quadratic_b,
        quadratic_a,
        quadratic_inverse_pairs_a,
        quadratic_inverse_pairs_b,
        quadratic_relation_indices
    );
    if quadratic_labels_found then
        quadratic_p, quadratic_q := quadratic_q, quadratic_p;
    end if;
end if;
verify(quadratic_labels_found,
       "the quadratic presentation cannot be relabeled as the displayed presentation");
verify_inverse_pairs(quadratic_presentation, quadratic_p, quadratic_a, quadratic_inverse_pairs_a);
verify_inverse_pairs(quadratic_presentation, quadratic_q, quadratic_b, quadratic_inverse_pairs_b);
quadratic_relation_words := [
    verify_relation_word(quadratic_p, quadratic_q, quadratic_a, quadratic_b, indices) :
    indices in quadratic_relation_indices
];
verify(
    verify_computed_relation_keys(quadratic_presentation) eq
    verify_relation_keys(quadratic_presentation, quadratic_relation_words),
    "the quadratic presentation does not have exactly the sixteen displayed square relators"
);

// The quadratic torsion example: at the norm-nine ramified prime the
// obstruction set Theta is the single nonsquare residue class, and that
// class is represented by the image of the fundamental unit 1 + sqrt(2).
norm_nine_prime := [
    factor[1] : factor in Factorization(Discriminant(quadratic_order`quaternion_algebra)) |
    Norm(factor[1]) eq 9
][1];
quadratic_theta := ObstructionAtModulus(quadratic_order, norm_nine_prime);
verify(quadratic_theta`delta_size eq 2 and quadratic_theta`theta_size eq 1 and
       not quadratic_theta`theta_contains_one,
       "the quadratic torsion obstruction is not the unique nonsquare class");
_, _, quadratic_reduction := build_reduced_algebra(quadratic_order, norm_nine_prime);
fundamental_unit := quadratic_integers!(1 + quadratic_order`base_field.1);
verify(not IsSquare(quadratic_theta`theta_representatives[1]) and
       not IsSquare(quadratic_reduction(fundamental_unit)),
       "the quadratic obstruction class is not the class of 1+sqrt(2)");
print "[verify] displayed presentation and torsion checks passed";


// ---------------------------------------------------------------------------
// Hurwitz and Lipschitz helpers
// ---------------------------------------------------------------------------

function verify_group_type(group)
    return Sprint(IdentifyGroup(group));
end function;


// Return a reduced-algebra representative of a permutation-model class:
// through the natural split-prime matrix model when the model provides one,
// and otherwise by following where the permutation sends the projective
// class index of the identity.  This transports subgroups between the
// Lipschitz and Hurwitz models in the comparison checks below.
function verify_reduced_representative(group_model, group_element)
    if UsesNaturalSplitPrimeModel(group_model) then
        return NaturalSplitPrimeReducedRepresentative(
            group_model,
            group_element^-1
        );
    end if;

    class_index_by_key := complementary_class_index_by_key(group_model);
    class_key_data := assigned group_model`class_key_data select group_model`class_key_data else false;
    identity := reduced_order_identity(
        group_model`order_data,
        group_model`reduction_map,
        group_model`reduced_algebra
    );
    identity_index := identity_class_index(
        identity,
        class_index_by_key,
        group_model`scalars,
        class_key_data
    );
    return group_model`class_representatives[identity_index^group_element];
end function;


function verify_order_element_from_reduction(group_model, reduced_element)
    coordinates := [
        group_model`order_data`integer_ring!(coordinate @@ group_model`reduction_map) :
        coordinate in Eltseq(reduced_element)
    ];
    return OrderElement(group_model`order_data, coordinates);
end function;


function verify_image_in_model(source_model, target_model, source_element)
    reduced_element := verify_reduced_representative(source_model, source_element);
    order_element := verify_order_element_from_reduction(source_model, reduced_element);
    image := false;
    complementary_projective_image_permutation(target_model, order_element, "comparison map", ~image);
    return image;
end function;


function verify_subgroup_image(source_model, target_model, subgroup)
    images := [verify_image_in_model(source_model, target_model, element) : element in subgroup];
    return sub<target_model`projective_unit_group | images>;
end function;


function verify_reduction_kernel(source_model, target_model)
    kernel_elements := [
        element : element in source_model`projective_unit_group |
        verify_image_in_model(source_model, target_model, element) eq Identity(target_model`projective_unit_group)
    ];
    return sub<source_model`projective_unit_group | kernel_elements>;
end function;


function verify_subgroup_from_order_element(group_model, element)
    image := false;
    complementary_projective_image_permutation(group_model, element, "explicit generator", ~image);
    return sub<group_model`projective_unit_group | image>;
end function;


function verify_projective_image_keys(group_model, elements)
    keys := [];
    for element in elements do
        image := false;
        complementary_projective_image_permutation(group_model, element, "displayed class", ~image);
        Append(~keys, Sprint(image));
    end for;
    return {key : key in keys};
end function;


function verify_complement_index_of_type(complement_classes, type_string)
    matches := [
        index : index in [1..#complement_classes] |
        verify_group_type(complement_classes[index]`subgroup) eq type_string
    ];
    verify(#matches eq 1, "a Hurwitz complement type is not represented uniquely");
    return matches[1];
end function;


function verify_subgroup_occurs(subgroup, complement_classes)
    return exists{class : class in complement_classes | class`subgroup eq subgroup};
end function;


// Construct the Hamilton quaternions with the Hurwitz and Lipschitz orders
// explicitly and verify the paper's worked calculations: the Hurwitz
// reduction isomorphism modulo two with its trivial complement and lifted
// obstruction, the three Hurwitz complements H1, H2, H3 modulo four with
// their Theta_4 sets, the four displayed Lipschitz complements and their
// trace-zero distinction, and the kernel and lifting relations connecting
// the two orders.
verify_section("Section 7.2: the Hurwitz and Lipschitz orders");

hamilton<i_h, j_h> := QuaternionAlgebra<Q | -1, -1>;
k_h := i_h * j_h;
hurwitz_order := Order([hamilton!1, i_h, k_h, (1 + i_h + j_h + k_h) / 2]);
hurwitz := ExplicitOrder(
    Q,
    hamilton,
    hurwitz_order :
    Label := "Hurwitz",
    OrderType := 4,
    ClassNumber := 1
);
hurwitz_integers := hurwitz`integer_ring;
hurwitz_mod_two := ReductionData(hurwitz, [], 2 * hurwitz_integers : Print := 0);
verify(Discriminant(hurwitz_order) eq 2 * hurwitz_integers and #hurwitz`unit_group eq 12,
       "the Hurwitz arithmetic data is incorrect");
verify(hurwitz_mod_two`injective and #hurwitz_mod_two`image_subgroup eq #hurwitz_mod_two`ambient_group,
       "Hurwitz reduction modulo two is not the asserted isomorphism");
verify(#hurwitz_mod_two`complement_classes eq 1 and
       #hurwitz_mod_two`complement_classes[1]`subgroup eq 1,
       "the trivial Hurwitz complement modulo two was not recovered");
hurwitz_lifted_theta := TorsionObstruction(hurwitz_mod_two, 1);
verify(hurwitz_lifted_theta`modulus_ideal eq StabilizedModulus(2 * hurwitz_integers),
       "the Hurwitz lifted obstruction uses the wrong stabilized modulus");
verify(hurwitz_lifted_theta`theta_size eq 1 and not hurwitz_lifted_theta`theta_contains_one,
       "the Hurwitz lifted obstruction is not the asserted nonsquare class");

// Independently enumerate the small dyadic ambient case, checking the exact
// ramified-maximal formula used for larger stabilized moduli.
hurwitz_ambient_modulus := StabilizedModulus(2 * hurwitz_integers);
hurwitz_ambient_theta := ObstructionAtModulus(hurwitz, hurwitz_ambient_modulus);
hurwitz_ambient_form := obs_reduced_forms(hurwitz, hurwitz_ambient_modulus);
hurwitz_square_classes := obs_square_classes(hurwitz_ambient_form`reduced_base_ring);
hurwitz_theta_lookup := AssociativeArray();
hurwitz_residues := [element : element in hurwitz_ambient_form`reduced_base_ring];
obs_scan_trace_zero_tuples(
    hurwitz_ambient_form,
    hurwitz_square_classes,
    [hurwitz_residues : i in [1..4]],
    false,
    ~hurwitz_theta_lookup
);
hurwitz_enumerated_theta := obs_local_result(
    "definition check",
    hurwitz,
    hurwitz_ambient_modulus,
    hurwitz_ambient_modulus,
    hurwitz_ambient_form,
    hurwitz_square_classes,
    hurwitz_theta_lookup
);
verify(
    hurwitz_ambient_theta`delta_size eq 4 and
    hurwitz_ambient_theta`theta_size eq 3 and
    hurwitz_ambient_theta`theta_contains_one and
    Sprint(hurwitz_ambient_theta`theta_representatives) eq
        Sprint(hurwitz_enumerated_theta`theta_representatives),
    "the ramified-maximal ambient formula fails its dyadic definition check"
);

hurwitz_mod_four := ReductionData(hurwitz, [], 4 * hurwitz_integers : Print := 0);
verify(hurwitz_mod_four`injective and #hurwitz_mod_four`complement_classes eq 3,
       "the three Hurwitz complements modulo four were not recovered");
h1_index := verify_complement_index_of_type(hurwitz_mod_four`complement_classes, "<8, 2>");
h2_index := verify_complement_index_of_type(hurwitz_mod_four`complement_classes, "<8, 5>");
h3_index := verify_complement_index_of_type(hurwitz_mod_four`complement_classes, "<8, 3>");
h1 := hurwitz_mod_four`complement_classes[h1_index]`subgroup;
h2 := hurwitz_mod_four`complement_classes[h2_index]`subgroup;
h3 := hurwitz_mod_four`complement_classes[h3_index]`subgroup;
h1_theta := ObstructionAtSubgroup(complementary_prime_power_group_model(hurwitz_mod_four), h1);
h2_theta := ObstructionAtSubgroup(complementary_prime_power_group_model(hurwitz_mod_four), h2);
h3_theta := ObstructionAtSubgroup(complementary_prime_power_group_model(hurwitz_mod_four), h3);
verify(h1_theta`theta_size eq 0, "Theta_4(H1) is not empty");
verify(h2_theta`theta_size eq 1 and not h2_theta`theta_contains_one,
       "Theta_4(H2) is not the unique nonsquare class");
verify(h3_theta`theta_size eq 2 and h3_theta`theta_contains_one,
       "Theta_4(H3) does not contain both square classes");
hurwitz_model_two := complementary_prime_power_group_model(hurwitz_mod_two);
hurwitz_model_four := complementary_prime_power_group_model(hurwitz_mod_four);
verify(h2 eq verify_reduction_kernel(hurwitz_model_four, hurwitz_model_two),
       "H2 is not the kernel of reduction from four to two");

lipschitz_order := Order([hamilton!1, i_h, j_h, k_h]);
lipschitz := ExplicitOrder(
    Q,
    hamilton,
    lipschitz_order :
    Label := "Lipschitz",
    OrderType := 1,
    ClassNumber := 1
);
lipschitz_integers := lipschitz`integer_ring;
lipschitz_mod_two := ReductionData(lipschitz, [], 2 * lipschitz_integers : Print := 0);
verify(Discriminant(lipschitz_order) eq 4 * lipschitz_integers and
       verify_group_type(lipschitz`unit_group) eq "<4, 2>",
       "the Lipschitz arithmetic data is incorrect");
verify(lipschitz_mod_two`injective and verify_group_type(lipschitz_mod_two`ambient_group) eq "<8, 5>" and
       #lipschitz_mod_two`complement_classes eq 4,
       "the Lipschitz quotient or its four complements were not recovered");

lipschitz_model_two := complementary_prime_power_group_model(lipschitz_mod_two);
verify(
    verify_projective_keys(lipschitz, lipschitz`unit_elements) eq
    verify_projective_keys(lipschitz, [hamilton!1, i_h, j_h, k_h]),
    "Gamma_L,emptyset is not exactly the four displayed projective classes"
);
displayed_lipschitz_mod_two := [
    hamilton!1, j_h, 1 + i_h + j_h, 1 + i_h + k_h,
    i_h, k_h, 1 + j_h + k_h, i_h + j_h + k_h
];
verify(
    #verify_projective_image_keys(lipschitz_model_two, displayed_lipschitz_mod_two) eq 8 and
    verify_projective_image_keys(lipschitz_model_two, displayed_lipschitz_mod_two) eq
        {Sprint(element) : element in lipschitz_model_two`projective_unit_group},
    "G_L[2] is not exactly the eight displayed projective classes"
);
k_generators := [i_h + j_h + k_h, 1 + i_h + j_h, 1 + i_h + k_h, 1 + j_h + k_h];
k_subgroups := [verify_subgroup_from_order_element(lipschitz_model_two, generator) : generator in k_generators];
for subgroup in k_subgroups do
    verify(verify_subgroup_occurs(subgroup, lipschitz_mod_two`complement_classes),
           "a displayed Lipschitz complement was not recovered");
end for;
// The paper uses the ordinary traces of the two representatives {1, g_l}
// here.  It does not assert that Theta_2(K_l) is empty: modulo 2, their
// ordinary trace 2 becomes zero.
verify(
    Trace(hamilton!1) ne 0 and
    #k_subgroups[1] eq 2 and Trace(k_generators[1]) eq 0 and
    &and[#k_subgroups[i] eq 2 and Trace(k_generators[i]) ne 0 : i in [2..4]],
    "the displayed Lipschitz trace-zero distinction failed"
);
verify(verify_reduction_kernel(lipschitz_model_two, hurwitz_model_two) eq k_subgroups[1],
       "the kernel of the Lipschitz-to-Hurwitz map is not K1");

lipschitz_mod_four := ReductionData(lipschitz, [], 4 * lipschitz_integers : Print := 0);
lipschitz_model_four := complementary_prime_power_group_model(lipschitz_mod_four);
for i in [2..4] do
    lifts := [];
    for complement_class in lipschitz_mod_four`complement_classes do
        if verify_subgroup_image(lipschitz_model_four, lipschitz_model_two, complement_class`subgroup) eq
           k_subgroups[i] then
            Append(~lifts, complement_class`subgroup);
        end if;
    end for;
    verify(#lifts eq 1, "a trace-zero-free Lipschitz complement does not have a unique lift class");
    image_in_hurwitz := verify_subgroup_image(
        lipschitz_model_four,
        hurwitz_model_four,
        lifts[1]
    );
    verify(
        IsConjugate(hurwitz_model_four`projective_unit_group, image_in_hurwitz, h1),
        "a trace-zero-free Lipschitz complement does not lift to H1"
    );
end for;

print "[verify] Hurwitz and Lipschitz checks passed";
print "";
print "All streamlined-code verification checks passed.";
