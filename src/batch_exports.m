// ============================================================================
// Batch complementary-triple scan over class-number-one maximal orders from
// the OneClassGenera table.
//
// Main API:
// - scan_all_class_one_maximal_orders_for_complementary_triples(index_range, norm_bound :
//       Print := 1,
//       time_limit_seconds := 0,
//       max_projective_quotient_seconds := 0,
//       max_reduced_unit_seconds := 0,
//       expected_exponent_bound := 2,
//       allow_higher_exponents := true,
//       consistency_check := false)
//
// Export API:
// - write_complementary_triples_csv(results, filename :
//       clear_file := false)
// - write_complementary_triples_order_overview_csv(results, filename :
//       clear_file := false)
// - write_complementary_triples_T_overview_csv(results, filename :
//       clear_file := false)
// - write_complementary_triples_skipped_csv(results, filename :
//       clear_file := false)
// - write_complementary_triples_warnings_csv(results, filename :
//       clear_file := false)
// - write_complementary_triples_summary_csv(results, filename :
//       clear_file := false)  // alias for order overview
// ============================================================================


function bct_join_strings(strings, delimiter)
    if #strings eq 0 then
        return "";
    end if;

    joined := strings[1];
    for i in [2..#strings] do
        joined cat:= delimiter cat strings[i];
    end for;

    return joined;
end function;


function bct_normalized_ideal_generator(generator)
    coefficients := Eltseq(generator);

    for coefficient in coefficients do
        if coefficient eq 0 then
            continue;
        end if;

        if coefficient lt 0 then
            return -generator;
        end if;

        return generator;
    end for;

    return generator;
end function;


function bct_ideal_data(ideal_x)
    has_generator, generator := IsPrincipal(ideal_x);
    generator_coefficients := [];

    if has_generator then
        generator := bct_normalized_ideal_generator(generator);
        generator_coefficients := [Sprint(coefficient) : coefficient in Eltseq(generator)];
    end if;

    return <Norm(ideal_x), has_generator, generator_coefficients>;
end function;


function bct_json_escape(raw_string)
    escaped := "";

    for i in [1..#raw_string] do
        character := raw_string[i];

        if character eq "\"" then
            escaped cat:= "\\\"";
        elif character eq "\\" then
            escaped cat:= "\\\\";
        elif character eq "\n" then
            escaped cat:= "\\n";
        elif character eq "\r" then
            escaped cat:= "\\r";
        elif character eq "\t" then
            escaped cat:= "\\t";
        else
            escaped cat:= character;
        end if;
    end for;

    return escaped;
end function;


function bct_json_string(raw_string)
    return "\"" cat bct_json_escape(raw_string) cat "\"";
end function;


function bct_json_number(number_x)
    return Sprint(number_x);
end function;


function bct_json_bool(flag)
    return flag select "true" else "false";
end function;


function bct_json_array(json_entries)
    return "[" cat bct_join_strings(json_entries, ",") cat "]";
end function;


function bct_json_string_array(string_entries)
    return bct_json_array([bct_json_string(entry) : entry in string_entries]);
end function;


function bct_json_object(field_entries)
    object_entries := [];

    for field_entry in field_entries do
        Append(
            ~object_entries,
            bct_json_string(field_entry[1]) cat ":" cat field_entry[2]
        );
    end for;

    return "{" cat bct_join_strings(object_entries, ",") cat "}";
end function;


function bct_ideal_json(ideal_x)
    ideal_data := bct_ideal_data(ideal_x);
    return bct_json_object([
        <"norm", bct_json_number(ideal_data[1])>,
        <"has_principal_generator", bct_json_bool(ideal_data[2])>,
        <"generator_coefficients", bct_json_string_array(ideal_data[3])>
    ]);
end function;


function bct_ideal_array_json(ideal_list)
    return bct_json_array([bct_ideal_json(ideal_x) : ideal_x in ideal_list]);
end function;


function bct_ideal_string(ideal_x)
    ideal_data := bct_ideal_data(ideal_x);
    return Sprintf("%o:%o", ideal_data[1], ideal_data[3]);
end function;


function bct_csv_field(field_string)
    escaped := "";

    for i in [1..#field_string] do
        character := field_string[i];

        if character eq "\"" then
            escaped cat:= "\"\"";
        elif character eq "\n" then
            escaped cat:= " ";
        elif character eq "\r" then
            escaped cat:= " ";
        else
            escaped cat:= character;
        end if;
    end for;

    return "\"" cat escaped cat "\"";
end function;


function bct_csv_row(field_strings)
    return bct_join_strings([bct_csv_field(field) : field in field_strings], ",");
end function;


function bct_integer_with_commas(integer_n)
    integer_n := Integers()!integer_n;
    is_negative := integer_n lt 0;
    digits := Sprint(Abs(integer_n));
    grouped_digits := "";
    digit_count := 0;

    for i in Reverse([1..#digits]) do
        grouped_digits := digits[i] cat grouped_digits;
        digit_count +:= 1;

        if (i gt 1) and (digit_count mod 3 eq 0) then
            grouped_digits := "," cat grouped_digits;
        end if;
    end for;

    return is_negative select "-" cat grouped_digits else grouped_digits;
end function;


function bct_duration_string(seconds)
    rounded_seconds := Integers()!Round(seconds);
    hours := rounded_seconds div 3600;
    minutes := (rounded_seconds mod 3600) div 60;
    remaining_seconds := rounded_seconds mod 60;

    if hours gt 0 then
        return Sprintf(
            "%o s (~%oh %om %os)",
            bct_integer_with_commas(rounded_seconds),
            hours,
            minutes,
            remaining_seconds
        );
    end if;

    if minutes gt 0 then
        return Sprintf(
            "%o s (~%om %os)",
            bct_integer_with_commas(rounded_seconds),
            minutes,
            remaining_seconds
        );
    end if;

    return bct_integer_with_commas(rounded_seconds) cat " s";
end function;


function bct_order_identifier_csv(order_data)
    if order_data`label eq "main" then
        return Sprint(order_data`index);
    end if;

    return complementary_order_identifier(order_data);
end function;


function bct_base_field_degree_csv(order_data)
    return Sprint(Degree(order_data`base_field));
end function;


function bct_base_field_discriminant_csv(order_data)
    return Sprint(Discriminant(order_data`base_field));
end function;


function bct_algebra_discriminant_csv(order_data)
    return bct_ideal_string(Discriminant(order_data`quaternion_algebra));
end function;


function bct_ramified_subset_count(triple_or_group)
    return Sprint(#triple_or_group`ramified_subset);
end function;


function bct_ramified_subset_json(ramified_subset)
    return bct_ideal_array_json(complementary_sorted_ideals(ramified_subset));
end function;


function bct_skipped_estimated_tasks_json(skipped_task_list)
    task_entries := [];

    for skipped_task in skipped_task_list do
        Append(
            ~task_entries,
            bct_json_object([
                <"task_key", bct_json_string(skipped_task[1])>,
                <"modulus_ideal", bct_ideal_json(skipped_task[2])>,
                <"estimated_seconds", bct_json_number(skipped_task[3])>,
                <"estimated_runtime", bct_json_string(bct_duration_string(skipped_task[3]))>
            ])
        );
    end for;

    return bct_json_array(task_entries);
end function;


function bct_skipped_estimated_tasks_summary(skipped_task_list)
    if #skipped_task_list eq 0 then
        return "";
    end if;

    return bct_join_strings([
        Sprintf(
            "%o at %o expected %o",
            skipped_task[1],
            bct_ideal_string(skipped_task[2]),
            bct_duration_string(skipped_task[3])
        ) :
        skipped_task in skipped_task_list
    ], " || ");
end function;


function bct_exponent_bound_warnings_json(warning_list)
    return bct_json_string_array(warning_list);
end function;


function bct_modulus_factorization_json(complementary_result)
    if not assigned complementary_result`factor_primes then
        return "[]";
    end if;

    factor_entries := [];
    for i in [1..#complementary_result`factor_primes] do
        Append(
            ~factor_entries,
            bct_json_object([
                <"prime_ideal", bct_ideal_json(complementary_result`factor_primes[i])>,
                <"exponent", bct_json_number(complementary_result`factor_exponents[i])>
            ])
        );
    end for;

    return bct_json_array(factor_entries);
end function;


function bct_complementary_triple_json(complementary_triple)
    complementary_result := complementary_triple`complementary_result;
    ambient_group_order := complementary_result`skipped_due_to_estimate select
        "null" else bct_json_number(#complementary_result`ambient_group);
    image_subgroup_order := complementary_result`skipped_due_to_estimate select
        "null" else bct_json_number(#complementary_result`image_subgroup);
    injective_json := complementary_result`skipped_due_to_estimate select
        "false" else bct_json_bool(complementary_result`injective);
    complement_count_json := complementary_result`skipped_due_to_estimate select
        bct_json_number(0) else bct_json_number(#complementary_result`complement_classes);
    normal_complement_count_json := complementary_result`skipped_due_to_estimate select
        bct_json_number(0) else bct_json_number(#complementary_result`normal_complement_classes);

    return bct_json_object([
        <"ramified_subset_count", bct_json_number(#complementary_triple`ramified_subset)>,
        <"ramified_subset_primes", bct_ramified_subset_json(complementary_triple`ramified_subset)>,
        <"modulus_ideal", bct_ideal_json(complementary_triple`modulus_ideal)>,
        <"modulus_norm", bct_json_number(Norm(complementary_triple`modulus_ideal))>,
        <"modulus_factorization", bct_modulus_factorization_json(complementary_result)>,
        <"localized_unit_group_order", bct_json_number(complementary_triple`localized_unit_group`subgroup_order)>,
        <"ambient_group_order", ambient_group_order>,
        <"image_subgroup_order", image_subgroup_order>,
        <"injective", injective_json>,
        <"skipped_due_to_estimate", bct_json_bool(complementary_result`skipped_due_to_estimate)>,
        <"complement_count", complement_count_json>,
        <"normal_complement_count", normal_complement_count_json>,
        <"skipped_estimated_tasks", bct_skipped_estimated_tasks_json(complementary_result`skipped_estimated_tasks)>
    ]);
end function;


function bct_ramified_subset_summary(ramified_subset)
    if #ramified_subset eq 0 then
        return "{}";
    end if;

    return "{ " cat bct_join_strings(
        [bct_ideal_string(ideal_x) : ideal_x in complementary_sorted_ideals(ramified_subset)],
        ", "
    ) cat " }";
end function;


function bct_modulus_factorization_summary(complementary_result)
    if not assigned complementary_result`factor_primes then
        return "";
    end if;

    factor_entries := [];
    for i in [1..#complementary_result`factor_primes] do
        Append(
            ~factor_entries,
            Sprintf(
                "%o^%o",
                bct_ideal_string(complementary_result`factor_primes[i]),
                complementary_result`factor_exponents[i]
            )
        );
    end for;

    return bct_join_strings(factor_entries, " * ");
end function;


function bct_complementary_triple_summary(complementary_triple)
    complementary_result := complementary_triple`complementary_result;
    summary_fields := [
        "T=" cat bct_ramified_subset_summary(complementary_triple`ramified_subset),
        "I=" cat bct_ideal_string(complementary_triple`modulus_ideal),
        "factors=" cat bct_modulus_factorization_summary(complementary_result),
        "|U_T|=" cat Sprint(complementary_triple`localized_unit_group`subgroup_order),
        "injective=" cat Sprint(complementary_result`injective),
        "skipped=" cat Sprint(complementary_result`skipped_due_to_estimate)
    ];

    if complementary_result`skipped_due_to_estimate then
        Append(
            ~summary_fields,
            "skipped_tasks=" cat bct_skipped_estimated_tasks_summary(complementary_result`skipped_estimated_tasks)
        );
    else
        Append(~summary_fields, "|G|=" cat bct_integer_with_commas(#complementary_result`ambient_group));
        Append(~summary_fields, "|image|=" cat bct_integer_with_commas(#complementary_result`image_subgroup));
        Append(~summary_fields, "complements=" cat Sprint(#complementary_result`complement_classes));
        Append(~summary_fields, "normal=" cat Sprint(#complementary_result`normal_complement_classes));
    end if;

    return bct_join_strings(summary_fields, "; ");
end function;


function bct_complementary_triples_json(algebra_row)
    if complementary_triple_data_is_trivial(algebra_row) then
        return "trivial";
    end if;

    return bct_json_array([
        bct_complementary_triple_json(complementary_triple) :
        complementary_triple in complementary_order_triples(algebra_row)
    ]);
end function;


function bct_complementary_triples_summary(algebra_row)
    if complementary_triple_data_is_trivial(algebra_row) then
        return "trivial";
    end if;

    return bct_join_strings([
        bct_complementary_triple_summary(complementary_triple) :
        complementary_triple in complementary_order_triples(algebra_row)
    ], " || ");
end function;


function bct_summary_counts_json(algebra_row)
    if complementary_triple_data_is_trivial(algebra_row) then
        return "trivial";
    end if;

    count_entries := [];

    for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
        localized_group := poset_result`localized_unit_group;
        minimal_complementary_ideal_count := #[
            result_x : result_x in poset_result`minimal_results |
            #result_x`complement_classes gt 0
        ];
        Append(
            ~count_entries,
            bct_json_object([
                <"ramified_subset_count", bct_json_number(#localized_group`ramified_subset)>,
                <"ramified_subset_primes", bct_ramified_subset_json(localized_group`ramified_subset)>,
                <"minimal_complementary_ideal_count", bct_json_number(minimal_complementary_ideal_count)>
            ])
        );
    end for;

    return bct_json_array(count_entries);
end function;


function bct_summary_counts_pretty(algebra_row)
    if complementary_triple_data_is_trivial(algebra_row) then
        return "trivial";
    end if;

    return bct_join_strings([
        Sprintf(
            "T=%o; minimal_complementary_ideals=%o",
            bct_ramified_subset_summary(poset_result`localized_unit_group`ramified_subset),
            #[ result_x : result_x in poset_result`minimal_results | #result_x`complement_classes gt 0 ]
        ) :
        poset_result in complementary_order_minimal_ideal_results(algebra_row)
    ], " || ");
end function;


function bct_total_minimal_complementary_ideal_count(algebra_row)
    if complementary_triple_data_is_trivial(algebra_row) then
        return "trivial";
    end if;

    return Sprint(&+[
        #[ result_x : result_x in poset_result`minimal_results | #result_x`complement_classes gt 0 ] :
        poset_result in complementary_order_minimal_ideal_results(algebra_row)
    ]);
end function;


procedure bct_write_csv_lines(lines, filename, clear_file, header_line)
    if Type(clear_file) ne BoolElt then
        error "clear_file must be true or false.";
    end if;

    if Type(filename) ne MonStgElt or #filename eq 0 then
        error "filename must be a nonempty string.";
    end if;

    if clear_file then
        lines := [header_line] cat lines;
        file_handle := Open(filename, "w");
        for line in lines do
            Puts(file_handle, line);
        end for;
        delete file_handle;
        return;
    end if;

    can_open, file_handle := OpenTest(filename, "r");
    if not can_open then
        error "filename must refer to a pre-existing CSV file when clear_file is false.";
    end if;
    delete file_handle;

    if #lines eq 0 then
        return;
    end if;

    file_handle := Open(filename, "a");
    for line in lines do
        Puts(file_handle, line);
    end for;
    delete file_handle;
end procedure;


function bct_algebra_rows_from_results(results)
    if Type(results) eq Rec then
        return results`algebra_rows;
    end if;

    if Type(results) ne SeqEnum then
        error "results must be a complementary-triples scan record or a sequence of algebra rows.";
    end if;

    return results;
end function;


function bct_bool_string(flag)
    return flag select "true" else "false";
end function;


function bct_ideal_sequence_string(ideal_list)
    if #ideal_list eq 0 then
        return "";
    end if;

    return bct_join_strings([bct_ideal_string(ideal_x) : ideal_x in ideal_list], " ; ");
end function;


function bct_sorted_ideal_sequence_string(ideal_list)
    return bct_ideal_sequence_string(complementary_sorted_ideals(ideal_list));
end function;


function bct_integer_sequence_string(integer_list)
    if #integer_list eq 0 then
        return "";
    end if;

    return bct_join_strings([Sprint(integer_x) : integer_x in integer_list], " ; ");
end function;


function bct_bool_sequence_string(flag_list)
    if #flag_list eq 0 then
        return "";
    end if;

    return bct_join_strings([bct_bool_string(flag) : flag in flag_list], " ; ");
end function;


function bct_sprint_sequence(value_list)
    if #value_list eq 0 then
        return "";
    end if;

    return bct_join_strings([Sprint(value) : value in value_list], " ; ");
end function;


function bct_order_context_headers()
    return [
        "base_field_degree",
        "base_field_discriminant",
        "algebra_discriminant",
        "order_discriminant",
        "order_index",
        "order_label",
        "order_identifier",
        "order_type",
        "class_number"
    ];
end function;


function bct_order_context_values(order_data)
    return [
        bct_base_field_degree_csv(order_data),
        bct_base_field_discriminant_csv(order_data),
        bct_algebra_discriminant_csv(order_data),
        bct_ideal_string(order_data`order_discriminant),
        Sprint(order_data`index),
        order_data`label,
        bct_order_identifier_csv(order_data),
        Sprint(order_data`order_type),
        Sprint(order_data`class_number)
    ];
end function;


function bct_localized_generator_prime_string(localized_group)
    if not assigned localized_group`generator_primes then
        return "";
    end if;

    return bct_sorted_ideal_sequence_string(localized_group`generator_primes);
end function;


function bct_result_complement_count(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        return 0;
    end if;

    if not assigned complementary_result`complement_classes then
        return 0;
    end if;

    return #complementary_result`complement_classes;
end function;


function bct_result_normal_complement_count(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        return 0;
    end if;

    if not assigned complementary_result`normal_complement_classes then
        return 0;
    end if;

    return #complementary_result`normal_complement_classes;
end function;


function bct_result_ambient_group_order_string(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        return "";
    end if;

    if not assigned complementary_result`ambient_group then
        return "";
    end if;

    return Sprint(#complementary_result`ambient_group);
end function;


function bct_result_image_subgroup_order_string(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        return "";
    end if;

    if not assigned complementary_result`image_subgroup then
        return "";
    end if;

    return Sprint(#complementary_result`image_subgroup);
end function;


function bct_result_ambient_index_string(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        return "";
    end if;

    if (not assigned complementary_result`ambient_group) or
       (not assigned complementary_result`image_subgroup) then
        return "";
    end if;

    return Sprint(#complementary_result`ambient_group div #complementary_result`image_subgroup);
end function;


function bct_complement_type_string(complementary_result, complement_index)
    if complement_index lt 1 or
       complement_index gt bct_result_complement_count(complementary_result) then
        return "";
    end if;

    complement_subgroup := complementary_result`complement_classes[complement_index]`subgroup;

    try
        return Sprint(IdentifyGroup(complement_subgroup));
    catch e
        return "";
    end try;
end function;


function bct_complement_is_normal_string(complementary_result, complement_index)
    if complement_index lt 1 or
       complement_index gt bct_result_complement_count(complementary_result) then
        return "";
    end if;

    if not assigned complementary_result`ambient_group then
        return "";
    end if;

    complement_subgroup := complementary_result`complement_classes[complement_index]`subgroup;

    try
        return bct_bool_string(IsNormal(complementary_result`ambient_group, complement_subgroup));
    catch e
        return "";
    end try;
end function;


function bct_complement_csv_values(complementary_result, complement_index)
    if complement_index lt 1 or
       complement_index gt bct_result_complement_count(complementary_result) then
        return ["", "", "", ""];
    end if;

    complement_subgroup := complementary_result`complement_classes[complement_index]`subgroup;

    return [
        Sprint(complement_index),
        Sprint(#complement_subgroup),
        bct_complement_type_string(complementary_result, complement_index),
        bct_complement_is_normal_string(complementary_result, complement_index)
    ];
end function;


function bct_local_norm_blank_values(status, message)
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
        ""
    ];
end function;


function bct_local_norm_skip_reason(complementary_result, complement_index)
    if complement_index lt 1 then
        return "no complement class";
    end if;

    if complementary_result`skipped_due_to_estimate then
        return "complementary computation skipped due to estimate";
    end if;

    if not assigned complementary_result`complements_computed then
        return "complements were not computed";
    end if;

    if not complementary_result`complements_computed then
        return "complements were not computed";
    end if;

    if bct_result_complement_count(complementary_result) eq 0 then
        return "no complement classes";
    end if;

    if complement_index gt bct_result_complement_count(complementary_result) then
        return "complement index out of range";
    end if;

    if not assigned complementary_result`injective then
        return "injectivity was not recorded";
    end if;

    if not complementary_result`injective then
        return "reduction is not injective";
    end if;

    if not assigned complementary_result`reduction_factors then
        return "local reduction factors were not recorded";
    end if;

    if #complementary_result`reduction_factors ne 1 then
        return "modulus is not a single prime power";
    end if;

    reduction_factor := complementary_result`reduction_factors[1];

    if reduction_factor`skipped_due_to_estimate then
        return "local reduction was skipped due to estimate";
    end if;

    if reduction_factor`uses_ramified_extension then
        return "local norm is not implemented for the ramified-extension ambient model";
    end if;

    return "";
end function;


function bct_local_norm_csv_values(complementary_result, complement_index)
    skip_reason := bct_local_norm_skip_reason(complementary_result, complement_index);

    if skip_reason ne "" then
        return bct_local_norm_blank_values("skipped", skip_reason);
    end if;

    try
        summary := local_norm_summary_for_complementary_result(
            complementary_result,
            complement_index :
            Print := 0
        );

        return [
            "computed",
            "",
            Sprint(summary`delta_size),
            bct_sprint_sequence(summary`delta_representatives),
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
        return bct_local_norm_blank_values("error", Sprint(e`Object));
    end try;
end function;


function bct_lifted_obstruction_blank_values(status, message)
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
        ""
    ];
end function;


function bct_lifted_obstruction_is_relevant(complementary_result)
    if complementary_result`skipped_due_to_estimate then
        return false;
    end if;

    if not assigned complementary_result`factor_primes or
       not assigned complementary_result`factor_exponents then
        return false;
    end if;

    if #complementary_result`factor_primes ne 1 or
       #complementary_result`factor_exponents ne 1 then
        return false;
    end if;

    return (Integers()!Norm(complementary_result`factor_primes[1])) mod 2 eq 0;
end function;


function bct_lifted_obstruction_csv_values(complementary_result, complement_index)
    if not bct_lifted_obstruction_is_relevant(complementary_result) then
        return bct_lifted_obstruction_blank_values("", "");
    end if;

    skip_reason := lifted_torsion_obstruction_skip_reason(complementary_result, complement_index);

    if skip_reason ne "" then
        return bct_lifted_obstruction_blank_values("skipped", skip_reason);
    end if;

    try
        summary := lifted_torsion_obstruction_summary(
            complementary_result,
            complement_index :
            Print := 0
        );

        return [
            "computed",
            "",
            Sprint(summary`norm),
            Sprint(summary`delta_size),
            bct_sprint_sequence(summary`delta_representatives),
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
        return bct_lifted_obstruction_blank_values("error", Sprint(e`Object));
    end try;
end function;


function bct_result_factor_prime_norms(complementary_result)
    if not assigned complementary_result`factor_primes then
        return "";
    end if;

    return bct_integer_sequence_string([Norm(prime_ideal) : prime_ideal in complementary_result`factor_primes]);
end function;


function bct_modulus_factorization_readable(complementary_result)
    return bct_modulus_factorization_summary(complementary_result);
end function;


function bct_reduction_factor_summary(complementary_result)
    if not assigned complementary_result`reduction_factors then
        return "";
    end if;

    factor_entries := [];
    for reduction_factor in complementary_result`reduction_factors do
        fields := [
            "P=" cat bct_ideal_string(reduction_factor`prime_ideal),
            "k=" cat Sprint(reduction_factor`prime_power_exponent),
            "modulus=" cat bct_ideal_string(reduction_factor`modulus_ideal),
            "skipped=" cat bct_bool_string(reduction_factor`skipped_due_to_estimate)
        ];

        if reduction_factor`skipped_due_to_estimate then
            Append(~fields, "task=" cat reduction_factor`skipped_task_key);
            Append(~fields, "estimated=" cat bct_duration_string(reduction_factor`skipped_estimated_seconds));
        else
            Append(~fields, "ambient_order=" cat Sprint(#reduction_factor`ambient_group));
            Append(~fields, "image_order=" cat Sprint(#reduction_factor`image_subgroup));
            Append(~fields, "injective=" cat bct_bool_string(reduction_factor`injective));
            Append(~fields, "uses_ramified_extension=" cat bct_bool_string(reduction_factor`uses_ramified_extension));

            if assigned reduction_factor`group_model and assigned reduction_factor`group_model`formula_case then
                Append(~fields, "formula_case=" cat reduction_factor`group_model`formula_case);
            end if;
        end if;

        Append(~factor_entries, bct_join_strings(fields, "; "));
    end for;

    return bct_join_strings(factor_entries, " | ");
end function;


function bct_skipped_task_readable(skipped_task)
    return Sprintf(
        "%o at %o; estimated=%o",
        skipped_task[1],
        bct_ideal_string(skipped_task[2]),
        bct_duration_string(skipped_task[3])
    );
end function;


function bct_skipped_tasks_readable(skipped_task_list)
    if #skipped_task_list eq 0 then
        return "";
    end if;

    return bct_join_strings(
        [bct_skipped_task_readable(skipped_task) : skipped_task in skipped_task_list],
        " | "
    );
end function;


function bct_minimal_result_has_complement(complementary_result)
    return bct_result_complement_count(complementary_result) gt 0;
end function;


function bct_minimal_result_has_normal_complement(complementary_result)
    return bct_result_normal_complement_count(complementary_result) gt 0;
end function;


function bct_poset_minimal_complementary_ideals(poset_result)
    ideals := [];

    for i in [1..#poset_result`minimal_results] do
        if bct_minimal_result_has_complement(poset_result`minimal_results[i]) then
            Append(~ideals, poset_result`minimal_injective_ideals[i]);
        end if;
    end for;

    return ideals;
end function;


function bct_poset_minimal_normal_complementary_ideals(poset_result)
    ideals := [];

    for i in [1..#poset_result`minimal_results] do
        if bct_minimal_result_has_normal_complement(poset_result`minimal_results[i]) then
            Append(~ideals, poset_result`minimal_injective_ideals[i]);
        end if;
    end for;

    return ideals;
end function;


function bct_poset_complement_class_count(poset_result)
    total := 0;

    for complementary_result in poset_result`minimal_results do
        total +:= bct_result_complement_count(complementary_result);
    end for;

    return total;
end function;


function bct_poset_normal_complement_class_count(poset_result)
    total := 0;

    for complementary_result in poset_result`minimal_results do
        total +:= bct_result_normal_complement_count(complementary_result);
    end for;

    return total;
end function;


function bct_order_totals(algebra_row)
    tested_ideal_count := 0;
    skipped_ideal_count := 0;
    minimal_complementary_ideal_count := 0;
    minimal_normal_complementary_ideal_count := 0;
    complement_class_count := 0;
    normal_complement_class_count := 0;

    for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
        tested_ideal_count +:= #poset_result`tested_ideals;
        skipped_ideal_count +:= #poset_result`skipped_ideals;
        minimal_complementary_ideal_count +:= #bct_poset_minimal_complementary_ideals(poset_result);
        minimal_normal_complementary_ideal_count +:= #bct_poset_minimal_normal_complementary_ideals(poset_result);
        complement_class_count +:= bct_poset_complement_class_count(poset_result);
        normal_complement_class_count +:= bct_poset_normal_complement_class_count(poset_result);
    end for;

    return <tested_ideal_count,
            skipped_ideal_count,
            minimal_complementary_ideal_count,
            minimal_normal_complementary_ideal_count,
            complement_class_count,
            normal_complement_class_count>;
end function;


function bct_T_summary_line(poset_result)
    return bct_join_strings([
        "T=" cat bct_ramified_subset_summary(poset_result`localized_unit_group`ramified_subset),
        "|U_T|=" cat Sprint(poset_result`localized_unit_group`subgroup_order),
        "tested=" cat Sprint(#poset_result`tested_ideals),
        "minimal_injective=" cat Sprint(#poset_result`minimal_injective_ideals),
        "minimal_complementary=" cat Sprint(#bct_poset_minimal_complementary_ideals(poset_result)),
        "complement_classes=" cat Sprint(bct_poset_complement_class_count(poset_result)),
        "normal_complement_classes=" cat Sprint(bct_poset_normal_complement_class_count(poset_result)),
        "skipped_ideals=" cat Sprint(#poset_result`skipped_ideals),
        "warnings=" cat Sprint(#poset_result`exponent_bound_warnings)
    ], "; ");
end function;


function bct_order_T_summary(algebra_row)
    if complementary_triple_data_is_trivial(algebra_row) then
        return "trivial unit quotient";
    end if;

    return bct_join_strings(
        [bct_T_summary_line(poset_result) : poset_result in complementary_order_minimal_ideal_results(algebra_row)],
        " | "
    );
end function;


function bct_main_csv_row_count_for_triple(complementary_triple)
    complement_count := bct_result_complement_count(complementary_triple`complementary_result);
    return complement_count eq 0 select 1 else complement_count;
end function;


function bct_main_csv_row_count_for_order(algebra_row)
    if complementary_triple_data_is_trivial(algebra_row) then
        return 0;
    end if;

    triples := complementary_order_triples(algebra_row);

    if #triples eq 0 then
        return 0;
    end if;

    return &+[bct_main_csv_row_count_for_triple(complementary_triple) :
        complementary_triple in triples];
end function;


function complementary_triples_csv_header()
    return bct_csv_row(bct_order_context_headers() cat [
        "triple_row",
        "norm_bound",
        "order_elapsed_seconds",
        "unit_quotient_order",
        "trivial_unit_quotient",
        "admissible_ramified_prime_count",
        "admissible_ramified_primes",
        "ramified_subset_count",
        "ramified_subset",
        "localized_unit_group_order",
        "localized_generator_primes",
        "modulus_norm",
        "modulus_ideal",
        "modulus_factorization",
        "factor_count",
        "factor_prime_norms",
        "factor_exponents",
        "local_reduction_factors",
        "injective",
        "skipped_due_to_estimate",
        "complements_computed",
        "ambient_group_order",
        "image_subgroup_order",
        "ambient_index_over_image",
        "complement_count",
        "normal_complement_count",
        "complement_index",
        "complement_order",
        "complement_type",
        "complement_is_normal",
        "local_norm_status",
        "local_norm_message",
        "local_norm_delta_size",
        "local_norm_delta_representatives",
        "local_norm_omega_size",
        "local_norm_omega_representatives",
        "local_norm_omega_contains_one",
        "local_norm_maximal_psi_count",
        "local_norm_maximal_psi_representatives",
        "local_norm_projective_class_count",
        "local_norm_trace_zero_class_count",
        "local_norm_trace_form_coefficients",
        "local_norm_norm_form_terms",
        "lifted_obstruction_status",
        "lifted_obstruction_message",
        "lifted_obstruction_modulus_norm",
        "lifted_obstruction_delta_size",
        "lifted_obstruction_delta_representatives",
        "lifted_obstruction_theta_size",
        "lifted_obstruction_theta_representatives",
        "lifted_obstruction_theta_contains_one",
        "lifted_obstruction_maximal_psi_count",
        "lifted_obstruction_maximal_psi_representatives",
        "lifted_obstruction_projective_class_count",
        "lifted_obstruction_trace_zero_class_count",
        "lifted_obstruction_trace_form_coefficients",
        "lifted_obstruction_norm_form_terms",
        "skipped_task_count",
        "skipped_tasks"
    ]);
end function;


function complementary_triples_csv_row(algebra_row, complementary_triple, triple_row, complement_index)
    order_data := complementary_triple`order_data;
    localized_group := complementary_triple`localized_unit_group;
    complementary_result := complementary_triple`complementary_result;

    factor_exponents := assigned complementary_result`factor_exponents select
        bct_integer_sequence_string(complementary_result`factor_exponents) else "";
    complement_values := bct_complement_csv_values(complementary_result, complement_index);
    local_norm_values := bct_local_norm_csv_values(complementary_result, complement_index);
    lifted_obstruction_values := bct_lifted_obstruction_csv_values(complementary_result, complement_index);

    return bct_csv_row(bct_order_context_values(order_data) cat [
        Sprint(triple_row),
        Sprint(algebra_row`norm_bound),
        Sprint(algebra_row`elapsed_seconds),
        Sprint(algebra_row`unit_quotient_order),
        bct_bool_string(algebra_row`trivial_unit_quotient),
        Sprint(#algebra_row`admissible_ramified_primes),
        bct_sorted_ideal_sequence_string(algebra_row`admissible_ramified_primes),
        Sprint(#complementary_triple`ramified_subset),
        bct_ramified_subset_summary(complementary_triple`ramified_subset),
        Sprint(localized_group`subgroup_order),
        bct_localized_generator_prime_string(localized_group),
        Sprint(Norm(complementary_triple`modulus_ideal)),
        bct_ideal_string(complementary_triple`modulus_ideal),
        bct_modulus_factorization_readable(complementary_result),
        assigned complementary_result`factor_primes select Sprint(#complementary_result`factor_primes) else "",
        bct_result_factor_prime_norms(complementary_result),
        factor_exponents,
        bct_reduction_factor_summary(complementary_result),
        complementary_result`skipped_due_to_estimate select "" else bct_bool_string(complementary_result`injective),
        bct_bool_string(complementary_result`skipped_due_to_estimate),
        assigned complementary_result`complements_computed select bct_bool_string(complementary_result`complements_computed) else "",
        bct_result_ambient_group_order_string(complementary_result),
        bct_result_image_subgroup_order_string(complementary_result),
        bct_result_ambient_index_string(complementary_result),
        Sprint(bct_result_complement_count(complementary_result)),
        Sprint(bct_result_normal_complement_count(complementary_result)),
        complement_values[1],
        complement_values[2],
        complement_values[3],
        complement_values[4],
        local_norm_values[1],
        local_norm_values[2],
        local_norm_values[3],
        local_norm_values[4],
        local_norm_values[5],
        local_norm_values[6],
        local_norm_values[7],
        local_norm_values[8],
        local_norm_values[9],
        local_norm_values[10],
        local_norm_values[11],
        local_norm_values[12],
        local_norm_values[13],
        lifted_obstruction_values[1],
        lifted_obstruction_values[2],
        lifted_obstruction_values[3],
        lifted_obstruction_values[4],
        lifted_obstruction_values[5],
        lifted_obstruction_values[6],
        lifted_obstruction_values[7],
        lifted_obstruction_values[8],
        lifted_obstruction_values[9],
        lifted_obstruction_values[10],
        lifted_obstruction_values[11],
        lifted_obstruction_values[12],
        lifted_obstruction_values[13],
        lifted_obstruction_values[14],
        assigned complementary_result`skipped_estimated_tasks select Sprint(#complementary_result`skipped_estimated_tasks) else "0",
        assigned complementary_result`skipped_estimated_tasks select bct_skipped_tasks_readable(complementary_result`skipped_estimated_tasks) else ""
    ]);
end function;


function complementary_triples_csv_rows(results)
    algebra_rows := bct_algebra_rows_from_results(results);
    lines := [];
    triple_row := 0;

    for algebra_row in algebra_rows do
        for complementary_triple in complementary_order_triples(algebra_row) do
            triple_row +:= 1;
            complement_count := bct_result_complement_count(complementary_triple`complementary_result);

            if complement_count eq 0 then
                Append(~lines, complementary_triples_csv_row(algebra_row, complementary_triple, triple_row, 0));
            else
                for complement_index in [1..complement_count] do
                    Append(
                        ~lines,
                        complementary_triples_csv_row(
                            algebra_row,
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


procedure write_complementary_triples_csv(results, filename : clear_file := false)
    lines := complementary_triples_csv_rows(results);
    bct_write_csv_lines(lines, filename, clear_file, complementary_triples_csv_header());
end procedure;


function complementary_triples_order_overview_csv_header()
    return bct_csv_row(bct_order_context_headers() cat [
        "norm_bound",
        "elapsed_seconds",
        "unit_quotient_order",
        "trivial_unit_quotient",
        "admissible_ramified_prime_count",
        "admissible_ramified_primes",
        "localized_T_count",
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


function complementary_triples_order_overview_csv_row(algebra_row)
    order_data := algebra_row`order_data;
    totals := bct_order_totals(algebra_row);

    return bct_csv_row(bct_order_context_values(order_data) cat [
        Sprint(algebra_row`norm_bound),
        Sprint(algebra_row`elapsed_seconds),
        Sprint(algebra_row`unit_quotient_order),
        bct_bool_string(algebra_row`trivial_unit_quotient),
        Sprint(#algebra_row`admissible_ramified_primes),
        bct_sorted_ideal_sequence_string(algebra_row`admissible_ramified_primes),
        Sprint(#complementary_order_minimal_ideal_results(algebra_row)),
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


function complementary_triples_order_overview_csv_rows(results)
    algebra_rows := bct_algebra_rows_from_results(results);
    return [complementary_triples_order_overview_csv_row(algebra_row) : algebra_row in algebra_rows];
end function;


procedure write_complementary_triples_order_overview_csv(results, filename : clear_file := false)
    lines := complementary_triples_order_overview_csv_rows(results);
    bct_write_csv_lines(lines, filename, clear_file, complementary_triples_order_overview_csv_header());
end procedure;


function complementary_triples_T_overview_csv_header()
    return bct_csv_row(bct_order_context_headers() cat [
        "T_row",
        "norm_bound",
        "trivial_unit_quotient",
        "ramified_subset_count",
        "ramified_subset",
        "localized_unit_group_order",
        "localized_generator_primes",
        "relevant_prime_count",
        "relevant_primes",
        "expected_exponent_bound",
        "allow_higher_exponents",
        "tested_ideal_count",
        "tested_ideals",
        "minimal_injective_ideal_count",
        "minimal_injective_ideals",
        "minimal_complementary_ideal_count",
        "minimal_complementary_ideals",
        "minimal_normal_complementary_ideal_count",
        "minimal_normal_complementary_ideals",
        "total_complement_class_count",
        "total_normal_complement_class_count",
        "skipped_ideal_count",
        "skipped_ideals",
        "skipped_task_count",
        "exponent_bound_warning_count",
        "exponent_bound_warnings"
    ]);
end function;


function complementary_triples_T_overview_csv_row(algebra_row, poset_result, T_row)
    order_data := algebra_row`order_data;
    localized_group := poset_result`localized_unit_group;

    return bct_csv_row(bct_order_context_values(order_data) cat [
        Sprint(T_row),
        Sprint(algebra_row`norm_bound),
        bct_bool_string(algebra_row`trivial_unit_quotient),
        Sprint(#localized_group`ramified_subset),
        bct_ramified_subset_summary(localized_group`ramified_subset),
        Sprint(localized_group`subgroup_order),
        bct_localized_generator_prime_string(localized_group),
        Sprint(#poset_result`relevant_primes),
        bct_sorted_ideal_sequence_string(poset_result`relevant_primes),
        Sprint(poset_result`expected_exponent_bound),
        bct_bool_string(poset_result`allow_higher_exponents),
        Sprint(#poset_result`tested_ideals),
        bct_sorted_ideal_sequence_string(poset_result`tested_ideals),
        Sprint(#poset_result`minimal_injective_ideals),
        bct_sorted_ideal_sequence_string(poset_result`minimal_injective_ideals),
        Sprint(#bct_poset_minimal_complementary_ideals(poset_result)),
        bct_sorted_ideal_sequence_string(bct_poset_minimal_complementary_ideals(poset_result)),
        Sprint(#bct_poset_minimal_normal_complementary_ideals(poset_result)),
        bct_sorted_ideal_sequence_string(bct_poset_minimal_normal_complementary_ideals(poset_result)),
        Sprint(bct_poset_complement_class_count(poset_result)),
        Sprint(bct_poset_normal_complement_class_count(poset_result)),
        Sprint(#poset_result`skipped_ideals),
        bct_sorted_ideal_sequence_string(poset_result`skipped_ideals),
        Sprint(#poset_result`skipped_estimated_tasks),
        Sprint(#poset_result`exponent_bound_warnings),
        bct_join_strings(poset_result`exponent_bound_warnings, " | ")
    ]);
end function;


function complementary_triples_T_overview_csv_rows(results)
    algebra_rows := bct_algebra_rows_from_results(results);
    lines := [];
    T_row := 0;

    for algebra_row in algebra_rows do
        for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
            T_row +:= 1;
            Append(~lines, complementary_triples_T_overview_csv_row(algebra_row, poset_result, T_row));
        end for;
    end for;

    return lines;
end function;


procedure write_complementary_triples_T_overview_csv(results, filename : clear_file := false)
    lines := complementary_triples_T_overview_csv_rows(results);
    bct_write_csv_lines(lines, filename, clear_file, complementary_triples_T_overview_csv_header());
end procedure;


function complementary_triples_skipped_csv_header()
    return bct_csv_row(bct_order_context_headers() cat [
        "skipped_row",
        "norm_bound",
        "T_row",
        "ramified_subset_count",
        "ramified_subset",
        "task_key",
        "modulus_norm",
        "modulus_ideal",
        "estimated_seconds",
        "estimated_runtime",
        "source"
    ]);
end function;


function complementary_triples_skipped_csv_row(algebra_row, poset_result, T_row, skipped_task, skipped_row)
    order_data := algebra_row`order_data;
    localized_group := poset_result`localized_unit_group;

    return bct_csv_row(bct_order_context_values(order_data) cat [
        Sprint(skipped_row),
        Sprint(algebra_row`norm_bound),
        Sprint(T_row),
        Sprint(#localized_group`ramified_subset),
        bct_ramified_subset_summary(localized_group`ramified_subset),
        skipped_task[1],
        Sprint(Norm(skipped_task[2])),
        bct_ideal_string(skipped_task[2]),
        Sprint(skipped_task[3]),
        bct_duration_string(skipped_task[3]),
        "minimal_ideal_poset"
    ]);
end function;


function complementary_triples_skipped_csv_rows(results)
    algebra_rows := bct_algebra_rows_from_results(results);
    lines := [];
    T_row := 0;
    skipped_row := 0;

    for algebra_row in algebra_rows do
        for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
            T_row +:= 1;
            for skipped_task in poset_result`skipped_estimated_tasks do
                skipped_row +:= 1;
                Append(
                    ~lines,
                    complementary_triples_skipped_csv_row(
                        algebra_row,
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


procedure write_complementary_triples_skipped_csv(results, filename : clear_file := false)
    lines := complementary_triples_skipped_csv_rows(results);
    bct_write_csv_lines(lines, filename, clear_file, complementary_triples_skipped_csv_header());
end procedure;


function complementary_triples_warnings_csv_header()
    return bct_csv_row(bct_order_context_headers() cat [
        "warning_row",
        "norm_bound",
        "T_row",
        "ramified_subset_count",
        "ramified_subset",
        "warning"
    ]);
end function;


function complementary_triples_warnings_csv_rows(results)
    algebra_rows := bct_algebra_rows_from_results(results);
    lines := [];
    T_row := 0;
    warning_row := 0;

    for algebra_row in algebra_rows do
        for poset_result in complementary_order_minimal_ideal_results(algebra_row) do
            T_row +:= 1;
            for warning_string in poset_result`exponent_bound_warnings do
                warning_row +:= 1;
                Append(~lines, bct_csv_row(bct_order_context_values(algebra_row`order_data) cat [
                    Sprint(warning_row),
                    Sprint(algebra_row`norm_bound),
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


procedure write_complementary_triples_warnings_csv(results, filename : clear_file := false)
    lines := complementary_triples_warnings_csv_rows(results);
    bct_write_csv_lines(lines, filename, clear_file, complementary_triples_warnings_csv_header());
end procedure;


function complementary_triples_summary_csv_header()
    return complementary_triples_order_overview_csv_header();
end function;


function complementary_triples_summary_csv_rows(results)
    return complementary_triples_order_overview_csv_rows(results);
end function;


procedure write_complementary_triples_summary_csv(results, filename : clear_file := false)
    lines := complementary_triples_summary_csv_rows(results);
    bct_write_csv_lines(lines, filename, clear_file, complementary_triples_summary_csv_header());
end procedure;


function scan_all_class_one_maximal_orders_for_complementary_triples(
    index_range,
    norm_bound :
    Print := 1,
    time_limit_seconds := 0,
    max_projective_quotient_seconds := 0,
    max_reduced_unit_seconds := 0,
    expected_exponent_bound := 2,
    allow_higher_exponents := true,
    consistency_check := false
)
    Print := validate_print_level(Print);
    time_limit_seconds,
    max_projective_quotient_seconds,
    max_reduced_unit_seconds := validate_complementary_time_controls(
        time_limit_seconds,
        max_projective_quotient_seconds,
        max_reduced_unit_seconds
    );

    if Type(expected_exponent_bound) ne RngIntElt or expected_exponent_bound lt 0 then
        error "expected_exponent_bound must be an integer >= 0.";
    end if;

    if Type(allow_higher_exponents) ne BoolElt then
        error "allow_higher_exponents must be true or false.";
    end if;

    if Type(consistency_check) ne BoolElt then
        error "consistency_check must be true or false.";
    end if;

    requested_start, requested_end := validated_index_range(index_range);
    effective_start := Max(requested_start, 1);
    effective_end := Min(requested_end, #OneClassGenera);
    order_list := [];

    if print_is_concise(Print) then
        print "";
        print "============================================================";
        print "[BCT run] Scan all class-one maximal orders for complementary triples";
        print "============================================================";
        print "[BCT run] requested_range=[", requested_start, ",", requested_end, "]",
              "| effective_range=[", effective_start, ",", effective_end, "]";
        print "[BCT run] norm_bound=", norm_bound,
              "| time_limit_seconds=", time_limit_seconds,
              "| max_projective_quotient_seconds=", max_projective_quotient_seconds,
              "| max_reduced_unit_seconds=", max_reduced_unit_seconds,
              "| expected_exponent_bound=", expected_exponent_bound,
              "| allow_higher_exponents=", allow_higher_exponents,
              "| consistency_check=", consistency_check,
              "| num_indices=", #OneClassGenera;
    end if;

    if effective_start gt #OneClassGenera or effective_start gt effective_end then
        return scan_orders_for_complementary_triples(
            [],
            norm_bound :
            Print := Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds,
            expected_exponent_bound := expected_exponent_bound,
            allow_higher_exponents := allow_higher_exponents,
            consistency_check := consistency_check
        );
    end if;

    for idx in [effective_start..effective_end] do
        order_type := OneClassGenera[idx][6];
        class_number := OneClassGenera[idx][7];

        if order_type ne 4 or class_number ne 1 then
            continue;
        end if;

        if print_is_concise(Print) then
            print "";
            print "[BCT order] idx=", idx,
                  "| order_type=", order_type,
                  "| class_number=", class_number;
        end if;

        main_order := order_data_from_index(idx);
        Append(~order_list, main_order);
    end for;

    if print_is_concise(Print) then
        print "";
        print "[BCT run] eligible_orders=", #order_list;
    end if;

    return scan_orders_for_complementary_triples(
        order_list,
        norm_bound :
        Print := Print,
        time_limit_seconds := time_limit_seconds,
        max_projective_quotient_seconds := max_projective_quotient_seconds,
        max_reduced_unit_seconds := max_reduced_unit_seconds,
        expected_exponent_bound := expected_exponent_bound,
        allow_higher_exponents := allow_higher_exponents,
        consistency_check := consistency_check
    );
end function;
