// Targeted recomputation of lifted torsion obstruction sets.
//
// This script does not rescan complementary triples.  It recomputes only the
// lifted prime-power obstruction sets for complementary triples already present
// in outputs/nontrivial_complementary_triples.csv.
//
// Run from the repository root:
//
//     magma scripts/recompute_lifted_obstructions.m

load "load.m";

if not assigned output_filename then
    output_filename := "outputs/lifted_obstructions.csv";
end if;

if not assigned task_start then
    task_start := 1;
end if;
if Type(task_start) eq MonStgElt then
    task_start := StringToInteger(task_start);
end if;

if not assigned task_stop then
    task_stop := 0;
end if;
if Type(task_stop) eq MonStgElt then
    task_stop := StringToInteger(task_stop);
end if;

if not assigned lifted_Print then
    lifted_Print := 1;
end if;
if Type(lifted_Print) eq MonStgElt then
    lifted_Print := StringToInteger(lifted_Print);
end if;

if not assigned lifted_time_limit_seconds then
    lifted_time_limit_seconds := 0;
end if;
if Type(lifted_time_limit_seconds) eq MonStgElt then
    lifted_time_limit_seconds := StringToInteger(lifted_time_limit_seconds);
end if;

if not assigned lifted_max_projective_quotient_seconds then
    lifted_max_projective_quotient_seconds := 0;
end if;
if Type(lifted_max_projective_quotient_seconds) eq MonStgElt then
    lifted_max_projective_quotient_seconds := StringToInteger(lifted_max_projective_quotient_seconds);
end if;

if not assigned lifted_max_reduced_unit_seconds then
    lifted_max_reduced_unit_seconds := 0;
end if;
if Type(lifted_max_reduced_unit_seconds) eq MonStgElt then
    lifted_max_reduced_unit_seconds := StringToInteger(lifted_max_reduced_unit_seconds);
end if;

lifted_task_format := recformat<
    order_index,
    ramified_subset_csv,
    ramified_subset_strings,
    prime_norm,
    prime_string,
    prime_exponent,
    modulus_factorization_csv,
    complement_index
>;

lifted_tasks := [
    rec<lifted_task_format |
        order_index := 1,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 2 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 2,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 2 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 2,
        ramified_subset_csv := "{ 3:[ 3 ] }",
        ramified_subset_strings := ["3:[ 3 ]"],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 2 ]^2",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 2,
        ramified_subset_csv := "{ 3:[ 3 ] }",
        ramified_subset_strings := ["3:[ 3 ]"],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 2 ]^2",
        complement_index := 2
    >,
    rec<lifted_task_format |
        order_index := 2,
        ramified_subset_csv := "{ 3:[ 3 ] }",
        ramified_subset_strings := ["3:[ 3 ]"],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 2 ]^2",
        complement_index := 3
    >,
    rec<lifted_task_format |
        order_index := 2,
        ramified_subset_csv := "{ 3:[ 3 ] }",
        ramified_subset_strings := ["3:[ 3 ]"],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 2 ]^2",
        complement_index := 4
    >,
    rec<lifted_task_format |
        order_index := 5,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 2 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 5,
        ramified_subset_csv := "{ 5:[ 5 ] }",
        ramified_subset_strings := ["5:[ 5 ]"],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 2 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 11,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 2 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 11,
        ramified_subset_csv := "{ 7:[ 7 ] }",
        ramified_subset_strings := ["7:[ 7 ]"],
        prime_norm := 2,
        prime_string := "2:[ 2 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 2 ]^2",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 795,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 4,
        prime_string := "4:[ 2, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "4:[ 2, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 797,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 4,
        prime_string := "4:[ 2, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "4:[ 2, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 1108,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 0, 1 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 0, 1 ]^2",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 1108,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 0, 1 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 0, 1 ]^2",
        complement_index := 2
    >,
    rec<lifted_task_format |
        order_index := 1108,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 0, 1 ]",
        prime_exponent := 2,
        modulus_factorization_csv := "2:[ 0, 1 ]^2",
        complement_index := 3
    >,
    rec<lifted_task_format |
        order_index := 1118,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 0, 1 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 0, 1 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 2058,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 4,
        prime_string := "4:[ 2, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "4:[ 2, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 2286,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 1, 1 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 1, 1 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 2286,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 2, -1 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 2, -1 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 3437,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 1, -1, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 1, -1, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 3437,
        ramified_subset_csv := "{ 5:[ 1, 1, -1 ] }",
        ramified_subset_strings := ["5:[ 1, 1, -1 ]"],
        prime_norm := 2,
        prime_string := "2:[ 1, -1, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 1, -1, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 3793,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 0, 1, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 0, 1, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 3793,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 1, -1, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 1, -1, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 3793,
        ramified_subset_csv := "{ 2:[ 0, 1, 0 ] }",
        ramified_subset_strings := ["2:[ 0, 1, 0 ]"],
        prime_norm := 2,
        prime_string := "2:[ 1, -1, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 1, -1, 0 ]^1",
        complement_index := 1
    >,
    rec<lifted_task_format |
        order_index := 4097,
        ramified_subset_csv := "{}",
        ramified_subset_strings := [],
        prime_norm := 2,
        prime_string := "2:[ 0, 1, 0, 0 ]",
        prime_exponent := 1,
        modulus_factorization_csv := "2:[ 0, 1, 0, 0 ]^1",
        complement_index := 1
    >
];

function lifted_task_header()
    return bct_csv_row([
        "order_index",
        "ramified_subset",
        "modulus_factorization",
        "complement_index",
        "source_exponent",
        "target_exponent",
        "lifted_obstruction_status",
        "lifted_obstruction_message",
        "lifted_obstruction_modulus_norm",
        "lifted_obstruction_delta_size",
        "lifted_obstruction_delta_representatives",
        "lifted_obstruction_delta_identity_representative",
        "lifted_obstruction_theta_size",
        "lifted_obstruction_theta_representatives",
        "lifted_obstruction_theta_contains_one",
        "lifted_obstruction_maximal_psi_count",
        "lifted_obstruction_maximal_psi_representatives",
        "lifted_obstruction_projective_class_count",
        "lifted_obstruction_trace_zero_class_count",
        "lifted_obstruction_trace_form_coefficients",
        "lifted_obstruction_norm_form_terms"
    ]);
end function;

function lifted_obstruction_blank_values(status, message)
    return [
        status,
        message,
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        ""
    ];
end function;

function lifted_find_ideal_by_string(order_data, ideal_norm, ideal_string)
    candidates := [
        ideal_x : ideal_x in IdealsUpTo(ideal_norm, order_data`integer_ring) |
        Norm(ideal_x) eq ideal_norm and bct_ideal_string(ideal_x) eq ideal_string
    ];

    if #candidates ne 1 then
        error Sprintf(
            "Expected one ideal matching %o in order index %o, found %o.",
            ideal_string,
            order_data`index,
            #candidates
        );
    end if;

    return candidates[1];
end function;

function lifted_ideal_norm_from_string(ideal_string)
    colon_position := Index(ideal_string, ":");

    if colon_position eq 0 then
        error Sprintf("Could not read ideal norm from %o.", ideal_string);
    end if;

    return StringToInteger(ideal_string[1..colon_position - 1]);
end function;

function lifted_join_task_strings(strings)
    return bct_join_strings(strings, " | ");
end function;

function lifted_task_key(task)
    return Sprintf(
        "%o || %o || %o || %o",
        task`order_index,
        task`ramified_subset_csv,
        task`modulus_factorization_csv,
        task`prime_exponent
    );
end function;

procedure lifted_summary_with_cache(
    complementary_result,
    complement_index,
    result_cache_key,
    ~summary,
    ~lifted_model_cache :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    target_group_model := complementary_prime_power_group_model(complementary_result);
    complement_class := complementary_result`complement_classes[complement_index];
    complement_subgroup := complement_class`subgroup;
    target_exponent := lifted_torsion_obstruction_target_exponent(complementary_result);
    lifted_key := Sprintf("%o || %o", result_cache_key, target_exponent);

    if IsDefined(lifted_model_cache, lifted_key) then
        lifted_group_model := lifted_model_cache[lifted_key];
    else
        lifted_group_model := lifted_torsion_obstruction_class_model(
            target_group_model,
            target_exponent :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );
        lifted_model_cache[lifted_key] := lifted_group_model;
    end if;

    source_tuples := lifted_torsion_obstruction_source_tuples(
        target_group_model,
        lifted_group_model,
        complement_subgroup
    );

    summary := local_norm_summary_from_tuples(
        "lifted_torsion_obstruction",
        lifted_group_model,
        "preimage_of_complement_mod_prime_power",
        complement_index,
        complement_class,
        complement_subgroup,
        source_tuples :
        Print := Print
    );
end procedure;

procedure lifted_summary_values(
    complementary_result,
    complement_index,
    result_cache_key,
    ~target_exponent,
    ~obstruction_values,
    ~lifted_model_cache :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0
)
    skip_reason := lifted_torsion_obstruction_skip_reason(
        complementary_result,
        complement_index
    );

    if skip_reason ne "" then
        target_exponent := assigned complementary_result`factor_exponents
            select complementary_result`factor_exponents[1] else 0;
        obstruction_values := lifted_obstruction_blank_values("skipped", skip_reason);
        return;
    end if;

    target_exponent := lifted_torsion_obstruction_target_exponent(complementary_result);

    try
        summary := lifted_torsion_obstruction_summary(
            complementary_result,
            complement_index :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );

        obstruction_values := [
            "computed",
            "",
            Sprint(summary`norm),
            Sprint(summary`delta_size),
            bct_sprint_sequence(summary`delta_representatives),
            Sprint(summary`delta_identity_representative),
            Sprint(summary`omega_size),
            bct_sprint_sequence(summary`omega_representatives),
            bct_bool_string(summary`omega_contains_one),
            Sprint(summary`maximal_psi_count),
            bct_sprint_sequence(summary`maximal_psi_representatives),
            Sprint(summary`projective_class_count),
            Sprint(summary`trace_zero_class_count),
            bct_sprint_sequence(summary`trace_form_coefficients),
            bct_sprint_sequence(summary`norm_form_terms)
        ];
    catch e
        obstruction_values := lifted_obstruction_blank_values("error", Sprint(e`Object));
    end try;
end procedure;

order_cache := AssociativeArray();
context_cache := AssociativeArray();
result_cache := AssociativeArray();
lifted_model_cache := AssociativeArray();

if task_stop eq 0 or task_stop gt #lifted_tasks then
    task_stop := #lifted_tasks;
end if;

lines := [];

print "Targeted lifted torsion obstruction recomputation";
print "tasks:", task_start, "through", task_stop, "of", #lifted_tasks;
print "output:", output_filename;

for task_index in [task_start..task_stop] do
    task := lifted_tasks[task_index];
    order_key := Sprint(task`order_index);

    if IsDefined(order_cache, order_key) then
        order_data := order_cache[order_key];
        context := context_cache[order_key];
    else
        order_data := order_data_from_index(task`order_index);
        context := complementary_build_context(order_data);
        order_cache[order_key] := order_data;
        context_cache[order_key] := context;
    end if;

    prime_ideal := lifted_find_ideal_by_string(
        order_data,
        task`prime_norm,
        task`prime_string
    );
    T := [
        lifted_find_ideal_by_string(
            order_data,
            lifted_ideal_norm_from_string(ideal_string),
            ideal_string
        ) :
        ideal_string in task`ramified_subset_strings
    ];
    modulus_ideal := prime_ideal^task`prime_exponent;
    result_key := lifted_task_key(task);

    if IsDefined(result_cache, result_key) then
        complementary_result := result_cache[result_key];
    else
        complementary_result := complementary_pairs_at_ideal(
            order_data,
            modulus_ideal :
            T := T,
            context := context,
            Print := 0,
            time_limit_seconds := lifted_time_limit_seconds,
            max_projective_quotient_seconds := lifted_max_projective_quotient_seconds,
            max_reduced_unit_seconds := lifted_max_reduced_unit_seconds
        );
        result_cache[result_key] := complementary_result;
        context_cache[order_key] := context;
    end if;

    lifted_summary_values(
        complementary_result,
        task`complement_index,
        result_key,
        ~target_exponent,
        ~obstruction_values,
        ~lifted_model_cache :
        Print := 0,
        time_limit_seconds := lifted_time_limit_seconds,
        max_projective_quotient_seconds := lifted_max_projective_quotient_seconds,
        max_reduced_unit_seconds := lifted_max_reduced_unit_seconds
    );

    Append(
        ~lines,
        bct_csv_row([
            Sprint(task`order_index),
            task`ramified_subset_csv,
            task`modulus_factorization_csv,
            Sprint(task`complement_index),
            Sprint(task`prime_exponent),
            Sprint(target_exponent)
        ] cat obstruction_values)
    );

    if lifted_Print ge 1 then
        print Sprintf(
            "[%o/%o] index=%o T=%o C=%o complement=%o status=%o target_exp=%o",
            task_index,
            task_stop,
            task`order_index,
            task`ramified_subset_csv,
            task`modulus_factorization_csv,
            task`complement_index,
            obstruction_values[1],
            target_exponent
        );
    end if;
end for;

bct_write_csv_lines(lines, output_filename, true, lifted_task_header());

print "Wrote", output_filename;
