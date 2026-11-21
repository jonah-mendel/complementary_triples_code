// Recomputes the four CSV files in data/.  Run from code/: magma reproduce.m
//
// Each order runs in a fresh Magma process, to keep memory use bounded.  The
// CSV files are written only after all 49 orders succeed.  To write them
// elsewhere, set output_directory on the command line
// (magma -b output_directory:=DIR reproduce.m).  Set MAGMA_CMD if "magma" is
// not on PATH.

load "load.m";

if not assigned output_directory then
    output_directory := "data";
end if;


// ---------------------------------------------------------------------------
// Strings, CSV encoding and files
// ---------------------------------------------------------------------------

// Every field is quoted, because ideal keys contain commas. No field contains
// a quote or a line break.
function rep_csv_row(values)
    return JoinStrings(["\"" cat value cat "\"" : value in values], ",");
end function;


rep_bool := func<flag | flag select "true" else "false">;


function rep_ideal_set(ideals)
    if #ideals eq 0 then
        return "{}";
    end if;
    return "{ " cat JoinStrings([CanonicalIdealKey(I) : I in SortIdeals(ideals)], ", ") cat " }";
end function;


// "p^a * q^b * ..." with primes sorted by SortIdeals, or "1" for the unit ideal.
function rep_factorization(ideal_x)
    factors := Factorization(ideal_x);
    if #factors eq 0 then
        return "1";
    end if;
    return JoinStrings([
        CanonicalIdealKey(p) cat "^" cat Sprint([f[2] : f in factors | f[1] eq p][1])
        : p in SortIdeals([f[1] : f in factors])
    ], " * ");
end function;


// "1" for the trivial group, otherwise IdentifyGroup's <order, id>.  Reducing
// the degree first keeps IdentifyGroup fast.
function rep_group_type(group_g)
    if #group_g eq 1 then
        return "1";
    end if;
    if Type(group_g) eq GrpPerm then
        group_g := DegreeReduction(group_g);
    end if;
    return Sprint(IdentifyGroup(group_g));
end function;


function rep_path(directory, filename)
    return directory[#directory] eq "/" select directory cat filename
                                         else directory cat "/" cat filename;
end function;


function rep_fragment(directory, index, name)
    return rep_path(directory, Sprintf("order-%o-%o", index, name));
end function;


procedure rep_write_lines(filename, lines)
    handle := Open(filename, "w");
    for line in lines do
        Puts(handle, line);
    end for;
    Flush(handle);
    delete handle;
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


function rep_shell_quote(string)
    quoted := "'";
    for character in Eltseq(string) do
        quoted cat:= character eq "'" select "'\"'\"'" else character;
    end for;
    return quoted cat "'";
end function;


procedure rep_remove_directory(path)
    System("/usr/bin/find " cat rep_shell_quote(path) cat " -depth -delete");
end procedure;


// ---------------------------------------------------------------------------
// Rows for one order
// ---------------------------------------------------------------------------

csv_columns := [
    ["order_index", "base_field_degree", "base_field_discriminant",
     "algebra_discriminant", "ramified_primes", "gamma_emptyset_order",
     "discriminant_theta_applicable", "discriminant_modulus_factorization",
     "discriminant_theta_size", "discriminant_theta_contains_one"],
    ["order_index", "ramified_subset", "gamma_order", "gamma_type",
     "exclusion_reason"],
    ["order_index", "ramified_subset", "modulus_norm",
     "modulus_factorization", "has_complement"],
    ["order_index", "ramified_subset", "modulus_norm",
     "modulus_factorization", "complement_index", "complement_order",
     "complement_is_normal", "theta_applicable",
     "theta_modulus_factorization", "theta_size", "theta_contains_one"]
];
csv_filenames := [
    "algebras.csv", "localized_groups.csv", "minimal_ideals.csv", "complements.csv"
];


// The CSV fields of complement i, from complement_order to theta_contains_one.
function rep_complement_fields(result, i)
    subgroup := result`complement_classes[i];
    applies := ComplementObstructionApplies(result);
    fields := [
        Sprint(#subgroup),
        rep_bool(IsNormal(result`ambient_group, subgroup)),
        rep_bool(applies)
    ];
    if not applies then
        return fields cat ["", "", ""];
    end if;
    theta := TorsionObstruction(result, i);
    error if theta`modulus_ideal ne StabilizedModulus(result`modulus_ideal),
        "A complement obstruction modulus is not e(C).";
    return fields cat [
        rep_factorization(theta`modulus_ideal),
        Sprint(theta`theta_size),
        rep_bool(theta`theta_contains_one)
    ];
end function;


// The rows of the four CSV files for one order, and the counts
// [exclusions, applicable discriminant obstructions, applicable complement
// obstructions].
function rep_order_rows(index)
    rows := [["" : i in [1..0]] : j in [1..4]];
    counts := [0, 0, 0];

    order_data := ClassOneOrder(index);
    classification := ClassifyOrder(order_data);
    gamma_emptyset := classification`localized_groups[1];

    discriminant := Discriminant(order_data`quaternion_algebra);
    obstruction := DiscriminantObstruction(order_data);
    error if obstruction`modulus_ideal ne StabilizedModulus(discriminant),
        Sprintf("The discriminant obstruction modulus is not e(D) for order %o.", index);
    if obstruction`applicable then
        counts[2] +:= 1;
    end if;
    Append(~rows[1], rep_csv_row([
        Sprint(index),
        Sprint(Degree(order_data`base_field)),
        Sprint(Discriminant(order_data`base_field)),
        CanonicalIdealKey(discriminant),
        rep_ideal_set(gamma_emptyset`admissible_ramified_primes),
        Sprint(gamma_emptyset`subgroup_order),
        rep_bool(obstruction`applicable),
        rep_factorization(obstruction`modulus_ideal),
        Sprint(obstruction`theta_size),
        rep_bool(obstruction`theta_contains_one)
    ]));

    for t in [1..#classification`localized_groups] do
        localized_group := classification`localized_groups[t];
        reason := classification`exclusion_reasons[t];
        T_string := rep_ideal_set(localized_group`ramified_subset);
        Append(~rows[2], rep_csv_row([
            Sprint(index),
            T_string,
            Sprint(localized_group`subgroup_order),
            rep_group_type(localized_group`subgroup),
            reason
        ]));
        if reason ne "" then
            counts[1] +:= 1;
            continue;
        end if;

        for result in classification`poset_results[t]`minimal_results do
            C := result`modulus_ideal;
            prefix := [Sprint(index), T_string, Sprint(Norm(C)), rep_factorization(C)];
            Append(~rows[3], rep_csv_row(
                prefix cat [rep_bool(#result`complement_classes gt 0)]
            ));

            for i in [1..#result`complement_classes] do
                fields := rep_complement_fields(result, i);
                if fields[3] eq "true" then
                    counts[3] +:= 1;
                end if;
                Append(~rows[4], rep_csv_row(prefix cat [Sprint(i)] cat fields));
            end for;
        end for;
    end for;

    return rows, counts;
end function;


// ---------------------------------------------------------------------------
// Worker and coordinator
// ---------------------------------------------------------------------------

indices := ClassOneOrderIndices();
error if #indices ne 49 or #Seqset(indices) ne 49,
    Sprintf("Expected 49 distinct class-one maximal orders in the input table, found %o.", #indices);

fragment_names := ["algebras", "localized-groups", "minimal-ideals", "complements"];

if assigned ct_order then
    // Worker for one order, started by the coordinator below.
    error if not assigned ct_dir, "ct_dir must be given together with ct_order.";
    index := StringToInteger(ct_order);
    error if index notin indices, Sprintf("%o is not a class-one order.", index);

    rows, counts := rep_order_rows(index);
    for i in [1..4] do
        rep_write_lines(rep_fragment(ct_dir, index, fragment_names[i]), rows[i]);
    end for;
    // Written last, so that its presence means the worker succeeded.
    rep_write_lines(rep_fragment(ct_dir, index, "done"), [Sprint(c) : c in counts]);
else
    magma_command := GetEnv("MAGMA_CMD");
    if #magma_command eq 0 then
        magma_command := "magma";
    end if;
    stage_directory := rep_path(output_directory, Tempname(".reproduce-stage-"));
    if System("/bin/mkdir " cat rep_shell_quote(stage_directory)) ne 0 then
        error Sprintf("Could not create staging directory %o.", stage_directory);
    end if;

    rows := [["" : i in [1..0]] : j in [1..4]];
    counts := [0, 0, 0];
    for position in [1..#indices] do
        index := indices[position];
        printf "[%o/%o] classifying order %o\n", position, #indices, index;
        command := JoinStrings([rep_shell_quote(argument) : argument in [
            magma_command, "-b",
            "ct_order:=" cat Sprint(index),
            "ct_dir:=" cat stage_directory,
            "reproduce.m"
        ]], " ");
        try
            log := Pipe(command, "");
        catch error_data
            rep_remove_directory(stage_directory);
            error "A reproduction worker process failed.";
        end try;

        done_file := rep_fragment(stage_directory, index, "done");
        if not FileExists(done_file) then
            print log;
            rep_remove_directory(stage_directory);
            error Sprintf("Reproduction failed for order %o.", index);
        end if;
        for i in [1..4] do
            rows[i] cat:= rep_read_lines(rep_fragment(stage_directory, index, fragment_names[i]));
        end for;
        worker_counts := [StringToInteger(line) : line in rep_read_lines(done_file)];
        counts := [counts[i] + worker_counts[i] : i in [1..3]];
    end for;
    rep_remove_directory(stage_directory);

    for i in [1..4] do
        rep_write_lines(
            rep_path(output_directory, csv_filenames[i]),
            [rep_csv_row(csv_columns[i])] cat rows[i]
        );
    end for;

    print "Reproduction complete.";
    print "orders:", #rows[1];
    print "localized groups:", #rows[2];
    print "mathematical exclusions:", counts[1];
    print "minimal injective ideals:", #rows[3];
    print "complement classes:", #rows[4];
    print "applicable discriminant obstructions:", counts[2];
    print "applicable complement obstructions:", counts[3];
end if;
