// Batch export of non-trivial complementary triples for class-one maximal
// orders.
//
// This script follows the classification setup in Section 5.3 of the paper.
// It skips the computations declared trivial by Lemmas triv-1 and triv-2:
//   - Gamma_emptyset = 1, T = emptyset;
//   - Gamma_emptyset = 1, #T = 1, except when a distinct ramified prime
//     remains available as the complementary modulus.
//
// Lemma triv-3 is not treated as trivial here.  In particular, the
// Gamma_emptyset = C_2, T = emptyset cases are still computed.
//
// For each non-skipped T, the relevant primes are all ramified primes of B
// together with all split primes P satisfying Norm(P) <= #Gamma_T + 1.
//
// Run from the repository root:
//     magma scripts/batch_nontrivial_maximal_complementary_triples.m

load "load.m";

// ========================================================================
// Edit inputs here.
// ========================================================================

if not assigned index_start then
    index_start := 1;
end if;

if not assigned index_stop then
    index_stop := #OneClassGenera;
end if;

if not assigned calculation_Print then
    calculation_Print := 1;
end if;

if not assigned progress_Print then
    progress_Print := 1;
end if;

if not assigned time_limit_seconds then
    time_limit_seconds := 0;
end if;

if not assigned max_projective_quotient_seconds then
    max_projective_quotient_seconds := 0;
end if;

if not assigned max_reduced_unit_seconds then
    max_reduced_unit_seconds := 1000;
end if;

if not assigned expected_exponent_bound then
    expected_exponent_bound := 2;
end if;

if not assigned allow_higher_exponents then
    allow_higher_exponents := true;
end if;

if not assigned complementary_triples_csv_filename then
    complementary_triples_csv_filename := "outputs/nontrivial_complementary_triples.csv";
end if;

if not assigned order_overview_csv_filename then
    order_overview_csv_filename := "outputs/nontrivial_complementary_triples_order_overview.csv";
end if;

if not assigned T_overview_csv_filename then
    T_overview_csv_filename := "outputs/nontrivial_complementary_triples_T_overview.csv";
end if;

if not assigned skipped_csv_filename then
    skipped_csv_filename := "outputs/nontrivial_complementary_triples_skipped.csv";
end if;

if not assigned warnings_csv_filename then
    warnings_csv_filename := "outputs/nontrivial_complementary_triples_warnings.csv";
end if;

if not assigned trivial_skipped_csv_filename then
    trivial_skipped_csv_filename := "outputs/nontrivial_complementary_triples_trivial_skipped.csv";
end if;

// ========================================================================
// Implementation below. Usually no edits needed below this line.
// ========================================================================

function ntct_integer_parameter(value, parameter_name)
    if Type(value) eq RngIntElt then
        return value;
    end if;

    if Type(value) eq MonStgElt then
        return StringToInteger(value);
    end if;

    error Sprintf("%o must be an integer or an integer string.", parameter_name);
end function;


function ntct_bool_parameter(value, parameter_name)
    if Type(value) eq BoolElt then
        return value;
    end if;

    if Type(value) eq MonStgElt then
        if value eq "true" or value eq "True" or value eq "1" then
            return true;
        end if;

        if value eq "false" or value eq "False" or value eq "0" then
            return false;
        end if;
    end if;

    error Sprintf("%o must be true or false.", parameter_name);
end function;


function ntct_string(value)
    if Type(value) eq MonStgElt then
        return value;
    end if;

    return Sprint(value);
end function;


function ntct_csv_row(values)
    return bct_csv_row([ntct_string(value) : value in values]);
end function;


procedure ntct_write_csv_line(filename, values : clear_file := false)
    mode := clear_file select "w" else "a";
    file_handle := Open(filename, mode);
    Puts(file_handle, ntct_csv_row(values));
    Flush(file_handle);
    delete file_handle;
end procedure;


function ntct_gamma_emptyset(localized_groups)
    for localized_group in localized_groups do
        if #localized_group`ramified_subset eq 0 then
            return localized_group;
        end if;
    end for;

    error "Could not find Gamma_emptyset among the localized groups.";
end function;


function ntct_has_distinct_ramified_prime_outside_T(admissible_primes, localized_group)
    if #localized_group`ramified_subset ne 1 then
        return false;
    end if;

    P := localized_group`ramified_subset[1];
    for Q in admissible_primes do
        if Q ne P then
            return true;
        end if;
    end for;

    return false;
end function;


function ntct_modulus_has_distinct_ramified_prime_outside_T(admissible_primes, localized_group, modulus_ideal)
    if #localized_group`ramified_subset ne 1 then
        return false;
    end if;

    P := localized_group`ramified_subset[1];
    for factor in Factorization(modulus_ideal) do
        Q := factor[1];
        if Q ne P and Index(admissible_primes, Q) ne 0 then
            return true;
        end if;
    end for;

    return false;
end function;


function ntct_minimal_ideal_is_nontrivial(gamma_emptyset_group, admissible_primes, localized_group, modulus_ideal)
    if gamma_emptyset_group`subgroup_order ne 1 then
        return true;
    end if;

    if #localized_group`ramified_subset eq 0 then
        return false;
    end if;

    if #localized_group`ramified_subset eq 1 then
        return ntct_modulus_has_distinct_ramified_prime_outside_T(
            admissible_primes,
            localized_group,
            modulus_ideal
        );
    end if;

    return true;
end function;


function ntct_trivial_skip_reason(gamma_emptyset_group, localized_group, admissible_primes)
    if gamma_emptyset_group`subgroup_order ne 1 then
        return "";
    end if;

    if #localized_group`ramified_subset eq 0 then
        return "triv-1: Gamma_emptyset=1, T=emptyset";
    end if;

    if #localized_group`ramified_subset eq 1 then
        if ntct_has_distinct_ramified_prime_outside_T(admissible_primes, localized_group) then
            return "";
        end if;

        return "triv-2: Gamma_emptyset=1, #T=1 and no distinct ramified modulus prime";
    end if;

    return "";
end function;


function ntct_nontrivial_poset_result(gamma_emptyset_group, admissible_primes, poset_result)
    minimal_ideals := [];
    minimal_results := [];

    for j in [1..#poset_result`minimal_injective_ideals] do
        modulus_ideal := poset_result`minimal_injective_ideals[j];
        if ntct_minimal_ideal_is_nontrivial(
            gamma_emptyset_group,
            admissible_primes,
            poset_result`localized_unit_group,
            modulus_ideal
        ) then
            Append(~minimal_ideals, modulus_ideal);
            Append(~minimal_results, poset_result`minimal_results[j]);
        end if;
    end for;

    return rec<minimal_ideal_poset_result_format |
        localized_unit_group := poset_result`localized_unit_group,
        relevant_primes := poset_result`relevant_primes,
        norm_bound := poset_result`norm_bound,
        expected_exponent_bound := poset_result`expected_exponent_bound,
        allow_higher_exponents := poset_result`allow_higher_exponents,
        minimal_injective_ideals := minimal_ideals,
        minimal_results := minimal_results,
        tested_ideals := poset_result`tested_ideals,
        skipped_ideals := poset_result`skipped_ideals,
        skipped_estimated_tasks := poset_result`skipped_estimated_tasks,
        exponent_bound_warnings := poset_result`exponent_bound_warnings
    >;
end function;


function ntct_fake_algebra_row_for_bound(algebra_row, norm_bound)
    return rec<single_order_complementary_scan_format |
        algebra_identifier := algebra_row`algebra_identifier,
        order_identifier := algebra_row`order_identifier,
        order_data := algebra_row`order_data,
        norm_bound := norm_bound,
        admissible_ramified_primes := algebra_row`admissible_ramified_primes,
        elapsed_seconds := algebra_row`elapsed_seconds,
        unit_quotient_order := algebra_row`unit_quotient_order,
        trivial_unit_quotient := algebra_row`trivial_unit_quotient,
        triple_data := algebra_row`triple_data,
        skipped_estimated_tasks := algebra_row`skipped_estimated_tasks,
        exponent_bound_warnings := algebra_row`exponent_bound_warnings
    >;
end function;


function ntct_max_integer(values)
    if #values eq 0 then
        return 0;
    end if;

    maximum_value := values[1];
    for i in [2..#values] do
        if values[i] gt maximum_value then
            maximum_value := values[i];
        end if;
    end for;

    return maximum_value;
end function;


function ntct_order_summary_header()
    return bct_csv_row(bct_order_context_headers() cat [
        "max_T_norm_bound",
        "elapsed_seconds",
        "unit_quotient_order",
        "trivial_unit_quotient",
        "gamma_emptyset_order",
        "admissible_ramified_prime_count",
        "admissible_ramified_primes",
        "localized_T_count_total",
        "localized_T_count_computed",
        "skipped_trivial_T_count",
        "main_csv_triple_rows",
        "minimal_injective_ideal_count",
        "minimal_complementary_ideal_count",
        "minimal_normal_complementary_ideal_count",
        "total_complement_class_count",
        "total_normal_complement_class_count",
        "tested_ideal_count",
        "skipped_ideal_count",
        "skipped_task_count",
        "exponent_bound_warning_count",
        "T_overview"
    ]);
end function;


function ntct_order_summary_row(algebra_row, total_T_count, skipped_trivial_T_count, gamma_emptyset_order)
    order_data := algebra_row`order_data;
    totals := bct_order_totals(algebra_row);

    return bct_csv_row(bct_order_context_values(order_data) cat [
        Sprint(algebra_row`norm_bound),
        Sprint(algebra_row`elapsed_seconds),
        Sprint(algebra_row`unit_quotient_order),
        bct_bool_string(algebra_row`trivial_unit_quotient),
        Sprint(gamma_emptyset_order),
        Sprint(#algebra_row`admissible_ramified_primes),
        bct_sorted_ideal_sequence_string(algebra_row`admissible_ramified_primes),
        Sprint(total_T_count),
        Sprint(#complementary_order_minimal_ideal_results(algebra_row)),
        Sprint(skipped_trivial_T_count),
        Sprint(bct_main_csv_row_count_for_order(algebra_row)),
        Sprint(#complementary_order_triples(algebra_row)),
        Sprint(totals[3]),
        Sprint(totals[4]),
        Sprint(totals[5]),
        Sprint(totals[6]),
        Sprint(totals[1]),
        Sprint(totals[2]),
        Sprint(#algebra_row`skipped_estimated_tasks),
        Sprint(#algebra_row`exponent_bound_warnings),
        bct_order_T_summary(algebra_row)
    ]);
end function;


function ntct_trivial_skipped_header()
    return bct_csv_row(bct_order_context_headers() cat [
        "skip_row",
        "gamma_emptyset_order",
        "ramified_subset_count",
        "ramified_subset",
        "localized_unit_group_order",
        "localized_generator_primes",
        "skip_reason"
    ]);
end function;


function ntct_trivial_skipped_row(order_data, skip_row, gamma_emptyset_order, localized_group, reason)
    return bct_csv_row(bct_order_context_values(order_data) cat [
        Sprint(skip_row),
        Sprint(gamma_emptyset_order),
        Sprint(#localized_group`ramified_subset),
        bct_ramified_subset_summary(localized_group`ramified_subset),
        Sprint(localized_group`subgroup_order),
        bct_localized_generator_prime_string(localized_group),
        reason
    ]);
end function;


procedure ntct_scan_order(
    order_data,
    calculation_Print_value,
    progress_Print_value,
    time_limit_seconds_value,
    max_projective_quotient_seconds_value,
    max_reduced_unit_seconds_value,
    expected_exponent_bound_value,
    allow_higher_exponents_value,
    ~algebra_row,
    ~total_T_count,
    ~skipped_trivial_T_count,
    ~gamma_emptyset_order,
    ~trivial_skipped_lines
)
    timer := Cputime();
    context, localized_groups := complementary_context_with_all_U_T(order_data);
    gamma_emptyset_group := ntct_gamma_emptyset(localized_groups);
    gamma_emptyset_order := gamma_emptyset_group`subgroup_order;
    admissible_primes := admissible_ramified_primes(order_data);
    computed_groups := [];
    computed_norm_bounds := [];
    minimal_ideal_results := [];
    complementary_triples := [];
    skipped_estimated_tasks := [];
    exponent_bound_warnings := [];
    total_T_count := #localized_groups;
    skipped_trivial_T_count := 0;

    for localized_group in localized_groups do
        reason := ntct_trivial_skip_reason(gamma_emptyset_group, localized_group, admissible_primes);

        if reason ne "" then
            skipped_trivial_T_count +:= 1;
            Append(
                ~trivial_skipped_lines,
                ntct_trivial_skipped_row(
                    order_data,
                    #trivial_skipped_lines + 1,
                    gamma_emptyset_order,
                    localized_group,
                    reason
                )
            );
            continue;
        end if;

        Append(~computed_groups, localized_group);
        Append(~computed_norm_bounds, localized_group`subgroup_order + 1);
    end for;

    if progress_Print_value ge 1 then
        print Sprintf(
            "idx=%o | Gamma_emptyset=%o | T_total=%o | T_computed=%o | T_skipped_trivial=%o",
            order_data`index,
            gamma_emptyset_order,
            total_T_count,
            #computed_groups,
            skipped_trivial_T_count
        );
    end if;

    for i in [1..#computed_groups] do
        localized_group := computed_groups[i];
        norm_bound := computed_norm_bounds[i];

        if progress_Print_value ge 1 then
            print Sprintf(
                "  T=%o | #Gamma_T=%o | norm_bound=%o",
                bct_ramified_subset_summary(localized_group`ramified_subset),
                localized_group`subgroup_order,
                norm_bound
            );
        end if;

        poset_result := false;
        minimal_ideal_poset_with_context(
            ~context,
            localized_group,
            norm_bound,
            ~poset_result :
            Print := calculation_Print_value,
            time_limit_seconds := time_limit_seconds_value,
            max_projective_quotient_seconds := max_projective_quotient_seconds_value,
            max_reduced_unit_seconds := max_reduced_unit_seconds_value,
            expected_exponent_bound := expected_exponent_bound_value,
            allow_higher_exponents := allow_higher_exponents_value
        );
        nontrivial_poset_result := ntct_nontrivial_poset_result(
            gamma_emptyset_group,
            admissible_primes,
            poset_result
        );
        Append(~minimal_ideal_results, nontrivial_poset_result);

        for skipped_task in poset_result`skipped_estimated_tasks do
            append_skipped_task_if_new(
                skipped_task[1],
                skipped_task[2],
                skipped_task[3],
                ~skipped_estimated_tasks
            );
        end for;

        for warning_string in poset_result`exponent_bound_warnings do
            if Index(exponent_bound_warnings, warning_string) eq 0 then
                Append(~exponent_bound_warnings, warning_string);
            end if;
        end for;

        for j in [1..#nontrivial_poset_result`minimal_injective_ideals] do
            Append(
                ~complementary_triples,
                complementary_triple_record(
                    order_data,
                    localized_group,
                    nontrivial_poset_result`minimal_injective_ideals[j],
                    nontrivial_poset_result`minimal_results[j]
                )
            );
        end for;
    end for;

    algebra_row := rec<single_order_complementary_scan_format |
        algebra_identifier := complementary_algebra_identifier(order_data),
        order_identifier := complementary_order_identifier(order_data),
        order_data := order_data,
        norm_bound := ntct_max_integer(computed_norm_bounds),
        admissible_ramified_primes := admissible_primes,
        elapsed_seconds := Cputime(timer),
        unit_quotient_order := #order_data`unit_group,
        trivial_unit_quotient := #order_data`unit_group eq 1,
        triple_data := complementary_triple_data_record(
            computed_groups,
            minimal_ideal_results,
            complementary_triples
        ),
        skipped_estimated_tasks := skipped_estimated_tasks,
        exponent_bound_warnings := exponent_bound_warnings
    >;
end procedure;


function ntct_scan_multi_order(
    index_start,
    index_stop,
    calculation_Print_value,
    progress_Print_value,
    time_limit_seconds_value,
    max_projective_quotient_seconds_value,
    max_reduced_unit_seconds_value,
    expected_exponent_bound_value,
    allow_higher_exponents_value
)
    timer := Cputime();
    algebra_rows := [];
    order_summary_lines := [];
    trivial_skipped_lines := [];
    skipped_estimated_tasks := [];
    skipped_estimated_task_keys := AssociativeArray();
    exponent_bound_warnings := [];
    orders_seen := 0;
    orders_tested := 0;

    for idx in [index_start..index_stop] do
        orders_seen +:= 1;
        entry := one_class_genera_entry(idx);

        if entry[6] ne 4 or entry[7] ne 1 then
            continue;
        end if;

        order_data := order_data_from_index(idx);
        orders_tested +:= 1;
        algebra_row := false;
        total_T_count := 0;
        skipped_trivial_T_count := 0;
        gamma_emptyset_order := 0;

        ntct_scan_order(
            order_data,
            calculation_Print_value,
            progress_Print_value,
            time_limit_seconds_value,
            max_projective_quotient_seconds_value,
            max_reduced_unit_seconds_value,
            expected_exponent_bound_value,
            allow_higher_exponents_value,
            ~algebra_row,
            ~total_T_count,
            ~skipped_trivial_T_count,
            ~gamma_emptyset_order,
            ~trivial_skipped_lines
        );
        Append(~algebra_rows, algebra_row);
        Append(
            ~order_summary_lines,
            ntct_order_summary_row(
                algebra_row,
                total_T_count,
                skipped_trivial_T_count,
                gamma_emptyset_order
            )
        );

        for skipped_task in algebra_row`skipped_estimated_tasks do
            skipped_task_key := complementary_multi_order_skipped_task_key(order_data, skipped_task);
            if not IsDefined(skipped_estimated_task_keys, skipped_task_key) then
                skipped_estimated_task_keys[skipped_task_key] := true;
                Append(
                    ~skipped_estimated_tasks,
                    complementary_multi_order_skipped_task_record(order_data, skipped_task)
                );
            end if;
        end for;

        for warning_string in algebra_row`exponent_bound_warnings do
            if Index(exponent_bound_warnings, warning_string) eq 0 then
                Append(~exponent_bound_warnings, warning_string);
            end if;
        end for;
    end for;

    print "";
    print "[NTCT run] indices seen:", orders_seen;
    print "[NTCT run] eligible maximal orders:", orders_tested;

    return rec<multi_order_complementary_scan_format |
        algebra_rows := algebra_rows,
        elapsed_seconds := Cputime(timer),
        skipped_estimated_tasks := skipped_estimated_tasks,
        exponent_bound_warnings := exponent_bound_warnings
    >, order_summary_lines, trivial_skipped_lines;
end function;


function ntct_main_csv_rows(results)
    lines := [];
    triple_row := 0;

    for algebra_row in results`algebra_rows do
        for complementary_triple in complementary_order_triples(algebra_row) do
            triple_row +:= 1;
            complement_count := bct_result_complement_count(complementary_triple`complementary_result);
            row_algebra := ntct_fake_algebra_row_for_bound(
                algebra_row,
                complementary_triple`localized_unit_group`subgroup_order + 1
            );

            if complement_count eq 0 then
                Append(~lines, complementary_triples_csv_row(row_algebra, complementary_triple, triple_row, 0));
            else
                for complement_index in [1..complement_count] do
                    Append(
                        ~lines,
                        complementary_triples_csv_row(
                            row_algebra,
                            complementary_triple,
                            triple_row,
                            complement_index
                        )
                    );
                end for;
            end if;
        end for;
    end for;

    return lines;
end function;


function ntct_T_overview_csv_rows(results)
    lines := [];
    T_row := 0;

    for algebra_row in results`algebra_rows do
        for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
            T_row +:= 1;
            row_algebra := ntct_fake_algebra_row_for_bound(algebra_row, poset_result`norm_bound);
            Append(~lines, complementary_triples_T_overview_csv_row(row_algebra, poset_result, T_row));
        end for;
    end for;

    return lines;
end function;


function ntct_skipped_csv_rows(results)
    lines := [];
    T_row := 0;
    skipped_row := 0;

    for algebra_row in results`algebra_rows do
        for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
            T_row +:= 1;
            row_algebra := ntct_fake_algebra_row_for_bound(algebra_row, poset_result`norm_bound);

            for skipped_task in poset_result`skipped_estimated_tasks do
                skipped_row +:= 1;
                Append(
                    ~lines,
                    complementary_triples_skipped_csv_row(
                        row_algebra,
                        poset_result,
                        T_row,
                        skipped_task,
                        skipped_row
                    )
                );
            end for;
        end for;
    end for;

    return lines;
end function;


function ntct_warnings_csv_rows(results)
    lines := [];
    T_row := 0;
    warning_row := 0;

    for algebra_row in results`algebra_rows do
        for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
            T_row +:= 1;
            row_algebra := ntct_fake_algebra_row_for_bound(algebra_row, poset_result`norm_bound);

            for warning_string in poset_result`exponent_bound_warnings do
                warning_row +:= 1;
                Append(~lines, bct_csv_row(bct_order_context_values(algebra_row`order_data) cat [
                    Sprint(warning_row),
                    Sprint(row_algebra`norm_bound),
                    Sprint(T_row),
                    Sprint(#poset_result`localized_unit_group`ramified_subset),
                    bct_ramified_subset_summary(poset_result`localized_unit_group`ramified_subset),
                    warning_string
                ]));
            end for;
        end for;
    end for;

    return lines;
end function;


index_start := ntct_integer_parameter(index_start, "index_start");
index_stop := ntct_integer_parameter(index_stop, "index_stop");
calculation_Print := ntct_integer_parameter(calculation_Print, "calculation_Print");
progress_Print := ntct_integer_parameter(progress_Print, "progress_Print");
time_limit_seconds := ntct_integer_parameter(time_limit_seconds, "time_limit_seconds");
max_projective_quotient_seconds := ntct_integer_parameter(max_projective_quotient_seconds, "max_projective_quotient_seconds");
max_reduced_unit_seconds := ntct_integer_parameter(max_reduced_unit_seconds, "max_reduced_unit_seconds");
expected_exponent_bound := ntct_integer_parameter(expected_exponent_bound, "expected_exponent_bound");
allow_higher_exponents := ntct_bool_parameter(allow_higher_exponents, "allow_higher_exponents");

if index_start lt 1 or index_start gt #OneClassGenera then
    error "index_start is outside the OneClassGenera table.";
end if;

if index_stop lt index_start then
    error "index_stop must be >= index_start.";
end if;

index_stop := Min(index_stop, #OneClassGenera);

print "";
print "============================================================";
print "Batch Non-Trivial Complementary-Triple CSV Export";
print "============================================================";
print "index start:", index_start;
print "index stop:", index_stop;
print "order filter:", "class_number=1 and order_type=4";
print "prime rule:", "all ramified primes and split primes with Norm(P) <= #Gamma_T + 1";
print "skip rule:", "skip triv-1 and singleton triv-2 only when no distinct ramified modulus prime remains";
print "main CSV:", complementary_triples_csv_filename;

results, order_summary_lines, trivial_skipped_lines := ntct_scan_multi_order(
    index_start,
    index_stop,
    calculation_Print,
    progress_Print,
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds,
    expected_exponent_bound,
    allow_higher_exponents
);

bct_write_csv_lines(
    ntct_main_csv_rows(results),
    complementary_triples_csv_filename,
    true,
    complementary_triples_csv_header()
);

bct_write_csv_lines(
    order_summary_lines,
    order_overview_csv_filename,
    true,
    ntct_order_summary_header()
);

bct_write_csv_lines(
    ntct_T_overview_csv_rows(results),
    T_overview_csv_filename,
    true,
    complementary_triples_T_overview_csv_header()
);

bct_write_csv_lines(
    ntct_skipped_csv_rows(results),
    skipped_csv_filename,
    true,
    complementary_triples_skipped_csv_header()
);

bct_write_csv_lines(
    ntct_warnings_csv_rows(results),
    warnings_csv_filename,
    true,
    complementary_triples_warnings_csv_header()
);

bct_write_csv_lines(
    trivial_skipped_lines,
    trivial_skipped_csv_filename,
    true,
    ntct_trivial_skipped_header()
);

print "";
print "============================================================";
print "Batch Non-Trivial Complementary-Triple CSV Export Complete";
print "============================================================";
print "orders:", #results`algebra_rows;
print "elapsed seconds:", results`elapsed_seconds;
print "main CSV rows:", #ntct_main_csv_rows(results);
print "order overview rows:", #order_summary_lines;
print "T overview rows:", #ntct_T_overview_csv_rows(results);
print "trivial T rows skipped:", #trivial_skipped_lines;
print "skipped estimated tasks:", #results`skipped_estimated_tasks;
print "exponent bound warnings:", #results`exponent_bound_warnings;
print "";
print "Wrote:";
print " ", complementary_triples_csv_filename;
print " ", order_overview_csv_filename;
print " ", T_overview_csv_filename;
print " ", skipped_csv_filename;
print " ", warnings_csv_filename;
print " ", trivial_skipped_csv_filename;
