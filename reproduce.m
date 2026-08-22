// Reproduce the four normalized CSV datasets used by the paper.
//
// Run from the code directory:
//     magma reproduce.m
//
// Each order either produces exact rows for every relevant case or raises an
// error.  Orders are evaluated in fresh Magma processes so
// finite quotient data from one order cannot accumulate in memory.  Workers
// write only to a private staging directory; the four canonical CSV files
// are replaced only after all 49 calculations and the combined dataset have
// succeeded.
//
// Assignable parameters, set before loading: output_directory, the directory
// receiving the four CSV files (default "data"), and Print, the verbosity
// level.  The coordinator re-invokes this same file once per order in a
// fresh Magma process; the private environment variables CT_REPRODUCE_ORDER
// and CT_REPRODUCE_DIRECTORY mark those worker invocations and are never set
// by hand.  Set MAGMA_CMD to the Magma executable for workers when plain
// "magma" is not on PATH.

// Magma uses randomized exact algorithms when constructing some orders and
// prime ideals.  A fixed seed makes their canonical textual representatives
// agree across the isolated workers and across complete reruns.
SetSeed(1);
load "load.m";

if not assigned output_directory then
    output_directory := "data";
end if;
if not assigned Print then
    Print := 1;
end if;

if Type(output_directory) ne MonStgElt or #output_directory eq 0 then
    error "output_directory must be a nonempty string.";
end if;
if Type(Print) eq MonStgElt then
    Print := StringToInteger(Print);
end if;
Print := validate_print_level(Print);

// Both private environment variables are set exactly when this load is a
// single-order worker spawned by the coordinator below; their presence, not
// a command-line flag, selects the worker role.
worker_order_string := GetEnv("CT_REPRODUCE_ORDER");
worker_directory := GetEnv("CT_REPRODUCE_DIRECTORY");
reproduction_worker := #worker_order_string gt 0 or #worker_directory gt 0;
if reproduction_worker and
   (#worker_order_string eq 0 or #worker_directory eq 0) then
    error "The private reproduction-worker environment is incomplete.";
end if;


// ---------------------------------------------------------------------------
// Deterministic strings and CSV encoding
// ---------------------------------------------------------------------------

function rep_join(strings, delimiter)
    if #strings eq 0 then
        return "";
    end if;
    result := strings[1];
    for i in [2..#strings] do
        result cat:= delimiter cat strings[i];
    end for;
    return result;
end function;


// Serialize one CSV field.  Every field is quoted, an embedded quote is
// doubled, and newline characters are replaced by spaces, so a serialized
// row is exactly one physical line and sorting rows lexicographically is
// well defined.
function rep_csv_field(value)
    string := Type(value) eq MonStgElt select value else Sprint(value);
    escaped := "";
    for character in Eltseq(string) do
        if character eq "\"" then
            escaped cat:= "\"\"";
        elif StringToCode(character) in {10, 13} then
            escaped cat:= " ";
        else
            escaped cat:= character;
        end if;
    end for;
    return "\"" cat escaped cat "\"";
end function;


function rep_csv_row(values)
    return rep_join([rep_csv_field(value) : value in values], ",");
end function;


function rep_bool(flag)
    if Type(flag) ne BoolElt then
        error "A CSV Boolean value must be true or false.";
    end if;
    return flag select "true" else "false";
end function;


function rep_ideal(ideal_x)
    return CanonicalIdealKey(ideal_x);
end function;


function rep_ideal_set(ideals)
    ideals := SortIdeals(ideals);
    if #ideals eq 0 then
        return "{}";
    end if;
    return "{ " cat rep_join([rep_ideal(ideal_x) : ideal_x in ideals], ", ") cat " }";
end function;


// Serialize the factorization of a nonzero integral ideal as
// "p^a * q^b * ..." with primes in canonical sorted order, or "1" for the
// unit ideal.  This is the textual form of every modulus column and a
// component of the duplicate-detection keys below.
function rep_factorization(ideal_x)
    factors := Factorization(ideal_x);
    if #factors eq 0 then
        return "1";
    end if;
    sorted_primes := SortIdeals([factor[1] : factor in factors]);
    exponents := AssociativeArray();
    for factor in factors do
        exponents[CanonicalIdealKey(factor[1])] := factor[2];
    end for;
    return rep_join([
        rep_ideal(prime_ideal) cat "^" cat Sprint(exponents[CanonicalIdealKey(prime_ideal)])
        : prime_ideal in sorted_primes
    ], " * ");
end function;


// The gamma_type CSV column: "1" for the trivial group, otherwise Magma's
// small-group identifier <order, id>.  A permutation group is first replaced
// by an image of smaller degree, checked exactly to be isomorphic, so that
// IdentifyGroup receives a manageable representation.
function rep_group_type(group_g)
    if #group_g eq 1 then
        return "1";
    end if;
    identify_group := group_g;
    if Type(group_g) eq GrpPerm then
        identify_group, reduction_map := DegreeReduction(group_g);
        if #Kernel(reduction_map) ne 1 or #identify_group ne #group_g then
            error "Degree reduction changed a finite group.";
        end if;
    end if;
    return Sprint(IdentifyGroup(identify_group));
end function;


function rep_order_degree(order_data)
    return Degree(order_data`base_field);
end function;


function rep_order_field_discriminant(order_data)
    return Discriminant(order_data`base_field);
end function;


// Duplicate-detection keys mirroring the natural keys of the CSV files: a
// localized group is identified by (order index, T), and a minimal ideal
// additionally by its modulus factorization.
function rep_localized_key(order_index, localized_group)
    return Sprintf("%o || %o", order_index, localized_group`ramified_subset_key);
end function;


function rep_minimal_key(order_index, localized_group, modulus_ideal)
    return Sprintf(
        "%o || %o || %o",
        order_index,
        localized_group`ramified_subset_key,
        rep_factorization(modulus_ideal)
    );
end function;


function rep_directory_path(directory, filename)
    return directory[#directory] eq "/" select directory cat filename
                                              else directory cat "/" cat filename;
end function;


procedure rep_write_lines(filename, lines)
    handle := Open(filename, "w");
    for line in lines do
        Puts(handle, line);
    end for;
    Flush(handle);
    delete handle;
end procedure;


function rep_shell_quote(path)
    quoted := "'";
    for character in Eltseq(path) do
        quoted cat:= character eq "'" select "'\"'\"'" else character;
    end for;
    return quoted cat "'";
end function;


// Move one staged file onto its canonical name.  The staging directory
// lives inside the output directory, so this is a rename within one
// filesystem and each canonical file is replaced atomically.
procedure rep_publish(staged_filename, canonical_filename)
    command := "/bin/mv -f " cat rep_shell_quote(staged_filename) cat
               " " cat rep_shell_quote(canonical_filename);
    if System(command) ne 0 then
        error Sprintf("Could not publish %o.", canonical_filename);
    end if;
end procedure;


procedure rep_make_directory(path)
    if System("/bin/mkdir " cat rep_shell_quote(path)) ne 0 then
        error Sprintf("Could not create staging directory %o.", path);
    end if;
end procedure;


function rep_read_lines(filename)
    handle := Open(filename, "r");
    lines := ["" : i in [1..0]];
    while true do
        line := Gets(handle);
        if IsEof(line) then
            break;
        end if;
        Append(~lines, line);
    end while;
    delete handle;
    return lines;
end function;


function rep_file_exists(filename)
    return System("/bin/test -f " cat rep_shell_quote(filename)) eq 0;
end function;


function rep_worker_filename(directory, index, suffix)
    return rep_directory_path(
        directory,
        Sprintf("order-%o-%o", index, suffix)
    );
end function;


procedure rep_remove_directory(path)
    // path was created in this run by Tempname and checked mkdir.
    System("/usr/bin/find " cat rep_shell_quote(path) cat " -depth -delete");
end procedure;


// ---------------------------------------------------------------------------
// In-memory output rows
// ---------------------------------------------------------------------------

algebra_header := rep_csv_row([
    "order_index",
    "base_field_degree",
    "base_field_discriminant",
    "algebra_discriminant",
    "ramified_primes",
    "gamma_emptyset_order",
    "discriminant_theta_applicable",
    "discriminant_modulus_factorization",
    "discriminant_theta_size",
    "discriminant_theta_contains_one"
]);

localized_group_header := rep_csv_row([
    "order_index",
    "ramified_subset",
    "gamma_order",
    "gamma_type",
    "exclusion_reason"
]);

minimal_ideal_header := rep_csv_row([
    "order_index",
    "ramified_subset",
    "modulus_norm",
    "modulus_factorization",
    "has_complement"
]);

complement_header := rep_csv_row([
    "order_index",
    "ramified_subset",
    "modulus_norm",
    "modulus_factorization",
    "complement_index",
    "complement_order",
    "complement_is_normal",
    "theta_applicable",
    "theta_modulus_factorization",
    "theta_size",
    "theta_contains_one"
]);

RepRowsFormat := recformat<
    algebras,
    localized_groups,
    minimal_ideals,
    complements,
    exclusions,
    discriminant_obstructions,
    complement_obstructions
>;


RepComplementRowFormat := recformat<
    order,
    is_normal,
    theta_applicable,
    theta_modulus_factorization,
    theta_size,
    theta_contains_one,
    sort_key
>;


// Compute exactly the mathematical fields exported for one complement.
function rep_complement_row(result, computed_index)
    subgroup := result`complement_classes[computed_index]`subgroup;
    is_normal := IsNormal(result`ambient_group, subgroup);
    theta_applicable := ComplementObstructionApplies(result);
    theta_modulus_factorization := "";
    theta_size := "";
    theta_contains_one := "";

    if theta_applicable then
        theta := TorsionObstruction(result, computed_index);
        if theta`modulus_ideal ne StabilizedModulus(result`modulus_ideal) then
            error "A complement obstruction modulus is not e(C).";
        end if;
        theta_modulus_factorization := rep_factorization(theta`modulus_ideal);
        theta_size := Sprint(theta`theta_size);
        theta_contains_one := rep_bool(theta`theta_contains_one);
    end if;

    fields := [
        Sprint(#subgroup),
        rep_bool(is_normal),
        rep_bool(theta_applicable),
        theta_modulus_factorization,
        theta_size,
        theta_contains_one
    ];
    return rec<RepComplementRowFormat |
        order := fields[1],
        is_normal := fields[2],
        theta_applicable := fields[3],
        theta_modulus_factorization := fields[4],
        theta_size := fields[5],
        theta_contains_one := fields[6],
        sort_key := rep_csv_row(fields)
    >;
end function;


function rep_sorted_complement_rows(result)
    // The normalized dataset identifies a complement class by precisely these
    // exported mathematical fields.  Sorting that complete payload makes the
    // rows independent of Magma's subgroup-class return order.  Equal payloads
    // are intentionally indistinguishable and therefore yield identical rows
    // apart from the consecutive display index assigned below.
    rows := [
        rep_complement_row(result, i) :
        i in [1..#result`complement_classes]
    ];
    Sort(~rows, func<left, right |
        left`sort_key lt right`sort_key select -1 else
        left`sort_key gt right`sort_key select 1 else 0
    >);
    return rows;
end function;


// Compute and validate one order.  Only the four serialized row sequences
// leave this function, so a worker releases all finite groups when it exits.
function rep_order_rows(index, worker_print)
    algebra_lines := ["" : i in [1..0]];
    localized_group_lines := ["" : i in [1..0]];
    minimal_ideal_lines := ["" : i in [1..0]];
    complement_lines := ["" : i in [1..0]];
    seen_localized_groups := AssociativeArray();
    seen_minimal_ideals := AssociativeArray();
    seen_complements := AssociativeArray();
    complements_by_minimal_ideal := AssociativeArray();
    written_complements_by_minimal_ideal := AssociativeArray();
    num_exclusions := 0;
    num_discriminant_obstructions := 0;
    num_complement_obstructions := 0;

    order_data := ClassOneOrder(index);
    localized_groups := LocalizedGroups(order_data);
    gamma_emptyset_positions := [
        i : i in [1..#localized_groups]
        | #localized_groups[i]`ramified_subset eq 0
    ];
    if #gamma_emptyset_positions ne 1 then
        error Sprintf("Order %o does not have exactly one Gamma_emptyset record.", index);
    end if;
    gamma_emptyset := localized_groups[gamma_emptyset_positions[1]];

    discriminant_obstruction := DiscriminantObstruction(order_data);
    expected_discriminant_modulus := StabilizedModulus(
        Discriminant(order_data`quaternion_algebra)
    );
    if discriminant_obstruction`modulus_ideal ne expected_discriminant_modulus then
        error Sprintf("The discriminant obstruction modulus is not e(D) for order %o.", index);
    end if;
    if discriminant_obstruction`applicable then
        num_discriminant_obstructions +:= 1;
    end if;

    Append(~algebra_lines, rep_csv_row([
        Sprint(index),
        Sprint(rep_order_degree(order_data)),
        Sprint(rep_order_field_discriminant(order_data)),
        rep_ideal(Discriminant(order_data`quaternion_algebra)),
        rep_ideal_set(gamma_emptyset`admissible_ramified_primes),
        Sprint(gamma_emptyset`subgroup_order),
        rep_bool(discriminant_obstruction`applicable),
        rep_factorization(discriminant_obstruction`modulus_ideal),
        Sprint(discriminant_obstruction`theta_size),
        rep_bool(discriminant_obstruction`theta_contains_one)
    ]));

    for localized_group in localized_groups do
        exclusion_reason := ClassificationExclusionReason(gamma_emptyset, localized_group);

        localized_key := rep_localized_key(index, localized_group);
        if IsDefined(seen_localized_groups, localized_key) then
            error Sprintf("Duplicate localized group for order %o and T=%o.", index, localized_group`ramified_subset_key);
        end if;
        seen_localized_groups[localized_key] := true;
        if exclusion_reason ne "" then
            num_exclusions +:= 1;
        end if;

        Append(~localized_group_lines, rep_csv_row([
            Sprint(index),
            rep_ideal_set(localized_group`ramified_subset),
            Sprint(localized_group`subgroup_order),
            rep_group_type(localized_group`subgroup),
            exclusion_reason
        ]));

        if exclusion_reason ne "" then
            continue;
        end if;

        minimal_ideals := MinimalInjectiveIdeals(
            order_data,
            localized_group`ramified_subset :
            Print := worker_print
        );
        for modulus_ideal in minimal_ideals do
            if not IsNontrivialMinimalIdeal(
                gamma_emptyset,
                localized_group,
                modulus_ideal
            ) then
                continue;
            end if;

            // Reconstruct one complete reduction result, serialize its
            // complements and obstructions, then let it leave scope before
            // moving to the next ideal.
            result := ReductionData(
                order_data,
                localized_group`ramified_subset,
                modulus_ideal :
                Print := worker_print
            );
            if result`modulus_ideal ne modulus_ideal or not result`injective then
                error Sprintf("A minimal ideal result failed its exact invariants for order %o.", index);
            end if;
            minimal_key := rep_minimal_key(index, localized_group, modulus_ideal);
            if IsDefined(seen_minimal_ideals, minimal_key) then
                error Sprintf("Duplicate minimal ideal row for order %o.", index);
            end if;
            seen_minimal_ideals[minimal_key] := true;

            has_complement := #result`complement_classes gt 0;
            complements_by_minimal_ideal[minimal_key] := #result`complement_classes;
            written_complements_by_minimal_ideal[minimal_key] := 0;
            Append(~minimal_ideal_lines, rep_csv_row([
                Sprint(index),
                rep_ideal_set(localized_group`ramified_subset),
                Sprint(Norm(modulus_ideal)),
                rep_factorization(modulus_ideal),
                rep_bool(has_complement)
            ]));

            sorted_complement_rows := rep_sorted_complement_rows(result);
            for displayed_index in [1..#sorted_complement_rows] do
                complement_row := sorted_complement_rows[displayed_index];
                complement_key := Sprintf("%o || %o", minimal_key, displayed_index);
                if IsDefined(seen_complements, complement_key) then
                    error Sprintf("Duplicate complement row for order %o.", index);
                end if;
                seen_complements[complement_key] := true;
                written_complements_by_minimal_ideal[minimal_key] :=
                    written_complements_by_minimal_ideal[minimal_key] + 1;

                if complement_row`theta_applicable eq "true" then
                    num_complement_obstructions +:= 1;
                end if;

                Append(~complement_lines, rep_csv_row([
                    Sprint(index),
                    rep_ideal_set(localized_group`ramified_subset),
                    Sprint(Norm(modulus_ideal)),
                    rep_factorization(modulus_ideal),
                    Sprint(displayed_index),
                    complement_row`order,
                    complement_row`is_normal,
                    complement_row`theta_applicable,
                    complement_row`theta_modulus_factorization,
                    complement_row`theta_size,
                    complement_row`theta_contains_one
                ]));
            end for;
        end for;
    end for;

    for minimal_key in Keys(complements_by_minimal_ideal) do
        expected := complements_by_minimal_ideal[minimal_key];
        actual := written_complements_by_minimal_ideal[minimal_key];
        if expected ne actual then
            error Sprintf("Complement row count mismatch for minimal ideal %o.", minimal_key);
        end if;
    end for;
    if #algebra_lines ne 1 or
       #localized_group_lines ne #Keys(seen_localized_groups) or
       #minimal_ideal_lines ne #Keys(seen_minimal_ideals) or
       #complement_lines ne #Keys(seen_complements) then
        error Sprintf("Serialized row validation failed for order %o.", index);
    end if;

    return rec<RepRowsFormat |
        algebras := algebra_lines,
        localized_groups := localized_group_lines,
        minimal_ideals := minimal_ideal_lines,
        complements := complement_lines,
        exclusions := num_exclusions,
        discriminant_obstructions := num_discriminant_obstructions,
        complement_obstructions := num_complement_obstructions
    >;
end function;


// The shell command for one single-order worker: a fresh Magma process
// loading this same file with the private worker environment set.  The -e
// expression assigns Print before the load, so workers stay silent and
// their captured output is printed only when a worker fails.  MAGMA_CMD
// overrides the executable when plain "magma" is not on PATH.
function rep_worker_command(index, directory)
    magma_command := GetEnv("MAGMA_CMD");
    if #magma_command eq 0 then
        magma_command := "magma";
    end if;
    expression := "Print := 0; load \"reproduce.m\";";
    return "/usr/bin/env CT_REPRODUCE_ORDER=" cat rep_shell_quote(Sprint(index)) cat
           " CT_REPRODUCE_DIRECTORY=" cat rep_shell_quote(directory) cat
           " " cat rep_shell_quote(magma_command) cat
           " -b -e " cat rep_shell_quote(expression);
end function;


indices := ClassOneOrderIndices();
if #indices ne 49 or #Setseq(Seqset(indices)) ne 49 then
    error Sprintf("Expected 49 distinct class-one maximal orders in the input table, found %o.", #indices);
end if;

fragment_suffixes := [
    "algebras.rows",
    "localized-groups.rows",
    "minimal-ideals.rows",
    "complements.rows"
];

if reproduction_worker then
    index := StringToInteger(worker_order_string);
    if Index(indices, index) eq 0 then
        error Sprintf("%o is not a class-one order requested by the paper.", index);
    end if;

    rows := rep_order_rows(index, Print);
    fragments := [
        rows`algebras,
        rows`localized_groups,
        rows`minimal_ideals,
        rows`complements
    ];
    for i in [1..#fragments] do
        Sort(~fragments[i]);
        rep_write_lines(
            rep_worker_filename(worker_directory, index, fragment_suffixes[i]),
            fragments[i]
        );
    end for;

    // This marker is written last.  Its absence makes every worker failure,
    // including an uncaught Magma error, visible to the coordinator.
    rep_write_lines(
        rep_worker_filename(worker_directory, index, "complete"),
        [
            Sprint(index),
            Sprint(#rows`algebras),
            Sprint(#rows`localized_groups),
            Sprint(#rows`minimal_ideals),
            Sprint(#rows`complements),
            Sprint(rows`exclusions),
            Sprint(rows`discriminant_obstructions),
            Sprint(rows`complement_obstructions)
        ]
    );
else
    algebra_lines := ["" : i in [1..0]];
    localized_group_lines := ["" : i in [1..0]];
    minimal_ideal_lines := ["" : i in [1..0]];
    complement_lines := ["" : i in [1..0]];
    num_exclusions := 0;
    num_applicable_discriminant_obstructions := 0;
    num_applicable_complement_obstructions := 0;

    // The same private directory holds worker fragments and the completed
    // four-file generation.  It is created inside the output directory so
    // that publication is a same-filesystem rename.  Nothing here is
    // canonical until publication.
    stage_directory := rep_directory_path(
        output_directory,
        Tempname(".reproduce-stage-")
    );
    rep_make_directory(stage_directory);

    position := 1;
    while position le #indices do
        // Each batch holds a single order, so the 49 workers run serially
        // in table order, one fresh Magma process per order.
        last_position := position;
        batch := indices[position..last_position];
        if Print ge 1 then
            print Sprintf(
                "[%o-%o/%o] classifying orders %o",
                position,
                last_position,
                #indices,
                rep_join([Sprint(index) : index in batch], ", ")
            );
        end if;

        try
            logs := Pipe(
                [rep_worker_command(index, stage_directory) : index in batch],
                ["" : index in batch]
            );
        catch error_data
            rep_remove_directory(stage_directory);
            error "A reproduction worker process failed.";
        end try;
        for batch_position in [1..#batch] do
            index := batch[batch_position];
            marker_filename := rep_worker_filename(
                stage_directory,
                index,
                "complete"
            );
            if not rep_file_exists(marker_filename) then
                print logs[batch_position];
                rep_remove_directory(stage_directory);
                error Sprintf("Exact reproduction failed for order %o.", index);
            end if;

            // A marker holds eight lines: the order index, the four
            // fragment row counts, and the exclusion and obstruction
            // tallies.  Exactly one algebras row per order is part of the
            // contract.
            marker := rep_read_lines(marker_filename);
            if #marker ne 8 or StringToInteger(marker[1]) ne index or
               StringToInteger(marker[2]) ne 1 then
                rep_remove_directory(stage_directory);
                error Sprintf("Worker output validation failed for order %o.", index);
            end if;

            fragments := [
                rep_read_lines(rep_worker_filename(stage_directory, index, suffix))
                : suffix in fragment_suffixes
            ];
            expected_counts := [StringToInteger(marker[i]) : i in [2..5]];
            if [#fragment : fragment in fragments] ne expected_counts then
                rep_remove_directory(stage_directory);
                error Sprintf("Worker row counts disagree for order %o.", index);
            end if;

            algebra_lines cat:= fragments[1];
            localized_group_lines cat:= fragments[2];
            minimal_ideal_lines cat:= fragments[3];
            complement_lines cat:= fragments[4];
            num_exclusions +:= StringToInteger(marker[6]);
            num_applicable_discriminant_obstructions +:= StringToInteger(marker[7]);
            num_applicable_complement_obstructions +:= StringToInteger(marker[8]);
        end for;
        position := last_position + 1;
    end while;

    // Distinct order indices make per-order uniqueness checks global; repeat
    // the serialized-row test here before canonical sorting and publication.
    if #algebra_lines ne 49 or
       #Setseq(Seqset(algebra_lines)) ne #algebra_lines or
       #Setseq(Seqset(localized_group_lines)) ne #localized_group_lines or
       #Setseq(Seqset(minimal_ideal_lines)) ne #minimal_ideal_lines or
       #Setseq(Seqset(complement_lines)) ne #complement_lines then
        rep_remove_directory(stage_directory);
        error "Combined reproduction row validation failed.";
    end if;

    // Sorting complete serialized rows makes repeated runs byte-identical.
    Sort(~algebra_lines);
    Sort(~localized_group_lines);
    Sort(~minimal_ideal_lines);
    Sort(~complement_lines);

    filenames := [
        "algebras.csv",
        "localized_groups.csv",
        "minimal_ideals.csv",
        "complements.csv"
    ];
    contents := [
        [algebra_header] cat algebra_lines,
        [localized_group_header] cat localized_group_lines,
        [minimal_ideal_header] cat minimal_ideal_lines,
        [complement_header] cat complement_lines
    ];

    for i in [1..#filenames] do
        rep_write_lines(
            rep_directory_path(stage_directory, filenames[i]),
            contents[i]
        );
    end for;
    for filename in filenames do
        rep_publish(
            rep_directory_path(stage_directory, filename),
            rep_directory_path(output_directory, filename)
        );
    end for;
    rep_remove_directory(stage_directory);

    print "Reproduction complete.";
    print "orders:", #algebra_lines;
    print "localized groups:", #localized_group_lines;
    print "mathematical exclusions:", num_exclusions;
    print "minimal injective ideals:", #minimal_ideal_lines;
    print "complement classes:", #complement_lines;
    print "applicable discriminant obstructions:", num_applicable_discriminant_obstructions;
    print "applicable complement obstructions:", num_applicable_complement_obstructions;
end if;
