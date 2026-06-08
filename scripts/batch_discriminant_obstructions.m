// Compute the torsion obstruction set at the discriminant modulus A(D).
//
// For each class-one maximal order O in OneClassGenera, with quaternion
// algebra discriminant D, set
//
//     A(D) = product_{P | D} P^max(2 v_P(2) + 1, v_P(D)).
//
// Since A(D) is usually composite, this script computes the local obstruction
// set at each prime-power factor and combines the results using the product
// decomposition modulo coprime ideals. In particular, 1 lies in Theta_{A(D)}
// exactly when 1 lies in every local factor.
//
// Run from the repository root:
//     magma scripts/batch_discriminant_obstructions.m

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
    calculation_Print := 0;
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
    max_reduced_unit_seconds := 0;
end if;

if not assigned exact_projective_order_threshold then
    exact_projective_order_threshold := 5000;
end if;

if not assigned output_csv_filename then
    output_csv_filename := "outputs/discriminant_obstructions.csv";
end if;

// ========================================================================
// Implementation below. Usually no edits needed below this line.
// ========================================================================

function ado_string(value)
    if Type(value) eq MonStgElt then
        return value;
    end if;

    return Sprint(value);
end function;


function ado_csv_row(values)
    return bct_csv_row([ado_string(value) : value in values]);
end function;


procedure ado_write_csv_line(filename, values : clear_file := false)
    mode := clear_file select "w" else "a";
    file_handle := Open(filename, mode);
    Puts(file_handle, ado_csv_row(values));
    Flush(file_handle);
    delete file_handle;
end procedure;


function ado_bool_string(flag)
    return flag select "true" else "false";
end function;


function ado_factorization_string(factors)
    if #factors eq 0 then
        return "1";
    end if;

    return bct_join_strings([
        bct_ideal_string(factor[1]) cat "^" cat Sprint(factor[2]) :
        factor in factors
    ], " * ");
end function;


function ado_exact_local_factor_string(prime_ideal, exponent, summary)
    return bct_join_strings([
        bct_ideal_string(prime_ideal) cat "^" cat Sprint(exponent),
        "method=exact",
        "Delta=" cat Sprint(summary`delta_size),
        "Theta=" cat Sprint(summary`omega_size),
        "contains_one=" cat ado_bool_string(summary`omega_contains_one),
        "trace_zero=" cat Sprint(summary`trace_zero_class_count),
        "classes=" cat Sprint(summary`projective_class_count)
    ], " ; ");
end function;


function ado_criterion_local_factor_string(prime_ideal, exponent, expected_projective_order, contains_one)
    return bct_join_strings([
        bct_ideal_string(prime_ideal) cat "^" cat Sprint(exponent),
        "method=minus_one_square_criterion",
        "expected_classes=" cat Sprint(expected_projective_order),
        "minus_one_square=" cat ado_bool_string(not contains_one),
        "contains_one=" cat ado_bool_string(contains_one)
    ], " ; ");
end function;


function ado_minus_one_is_square_modulus(integer_ring, modulus_ideal)
    quotient_ring, reduction_map := quo<integer_ring | modulus_ideal>;
    target := reduction_map(integer_ring!(-1));

    for residue_x in quotient_ring do
        if IsUnit(residue_x) and residue_x^2 eq target then
            return true;
        end if;
    end for;

    return false;
end function;


function ado_target_factorization(order_data)
    integer_ring := order_data`integer_ring;
    algebra_discriminant := Discriminant(order_data`quaternion_algebra);
    target_factors := [];

    for factor in Factorization(algebra_discriminant) do
        prime_ideal := factor[1];
        discriminant_exponent := factor[2];
        two_adic_exponent := 2 * Valuation(2 * integer_ring, prime_ideal) + 1;
        target_exponent := Maximum(two_adic_exponent, discriminant_exponent);
        Append(~target_factors, <prime_ideal, target_exponent>);
    end for;

    return target_factors;
end function;


function ado_target_modulus(integer_ring, target_factors)
    modulus := 1 * integer_ring;

    for factor in target_factors do
        modulus *:= factor[1]^factor[2];
    end for;

    return modulus;
end function;


function ado_projective_source_tuples(group_model)
    return [
        local_norm_normalized_tuple(tuple_x, group_model`reduced_base_ring) :
        tuple_x in group_model`class_representatives
    ];
end function;


procedure ado_compute_order_values(
    order_data,
    Print,
    time_limit_seconds_value,
    max_projective_quotient_seconds_value,
    max_reduced_unit_seconds_value,
    ~values
)
    integer_ring := order_data`integer_ring;
    target_factors := ado_target_factorization(order_data);
    target_modulus := ado_target_modulus(integer_ring, target_factors);

    if #target_factors eq 0 then
        values := [
            bct_ideal_string(target_modulus),
            ado_factorization_string(target_factors),
            "computed_empty_product",
            "finite discriminant is trivial; no torsion obstruction set recorded",
            "",
            "",
            ado_bool_string(false),
            "",
            "",
            ""
        ];
        return;
    end if;

    theta_size := 1;
    delta_size := 1;
    theta_contains_one := true;
    projective_class_count := 0;
    trace_zero_class_count := 0;
    local_factor_strings := [];
    all_local_factors_exact := true;

    for factor in target_factors do
        prime_ideal := factor[1];
        exponent := factor[2];
        projective_formula_known, expected_projective_order, formula_case :=
            expected_projective_group_order_data(order_data, prime_ideal, exponent);
        criterion_contains_one := not ado_minus_one_is_square_modulus(
            integer_ring,
            prime_ideal^exponent
        );

        if (not projective_formula_known) or expected_projective_order gt exact_projective_order_threshold then
            all_local_factors_exact := false;
            theta_contains_one := theta_contains_one and criterion_contains_one;
            Append(
                ~local_factor_strings,
                ado_criterion_local_factor_string(
                    prime_ideal,
                    exponent,
                    expected_projective_order,
                    criterion_contains_one
                )
            );
            continue;
        end if;

        group_model := build_projective_unit_group(
            order_data,
            prime_ideal,
            exponent :
            Print := Print,
            time_limit_seconds := time_limit_seconds_value,
            max_projective_quotient_seconds := max_projective_quotient_seconds_value,
            max_reduced_unit_seconds := max_reduced_unit_seconds_value,
            compute_complements := false
        );

        if group_model`skipped_due_to_estimate then
            values := [
                bct_ideal_string(target_modulus),
                ado_factorization_string(target_factors),
                "skipped",
                group_model`skipped_task_key cat " estimated_seconds=" cat Sprint(group_model`skipped_estimated_seconds),
                "",
                "",
                "false",
                "",
                "",
                bct_join_strings(local_factor_strings, " || ")
            ];
            return;
        end if;

        summary := local_norm_summary_from_tuples(
            "algebra_discriminant",
            group_model,
            "ambient_projective_group",
            0,
            false,
            false,
            ado_projective_source_tuples(group_model) :
            Print := Print
        );

        theta_size *:= summary`omega_size;
        delta_size *:= summary`delta_size;
        if summary`omega_contains_one ne criterion_contains_one then
            error Sprintf(
                "The exact local obstruction and the -1 square criterion disagree at %o^%o.",
                prime_ideal,
                exponent
            );
        end if;
        theta_contains_one := theta_contains_one and summary`omega_contains_one;
        projective_class_count +:= summary`projective_class_count;
        trace_zero_class_count +:= summary`trace_zero_class_count;
        Append(~local_factor_strings, ado_exact_local_factor_string(prime_ideal, exponent, summary));
    end for;

    values := [
        bct_ideal_string(target_modulus),
        ado_factorization_string(target_factors),
        "computed",
        all_local_factors_exact select "" else "large local factors used the -1 square criterion",
        all_local_factors_exact select Sprint(delta_size) else "",
        all_local_factors_exact select Sprint(theta_size) else "",
        ado_bool_string(theta_contains_one),
        all_local_factors_exact select Sprint(projective_class_count) else "",
        all_local_factors_exact select Sprint(trace_zero_class_count) else "",
        bct_join_strings(local_factor_strings, " || ")
    ];
end procedure;


headers := bct_order_context_headers() cat [
    "A_D",
    "A_D_factorization",
    "theta_A_D_status",
    "theta_A_D_message",
    "theta_A_D_delta_size",
    "theta_A_D_size",
    "theta_A_D_contains_one",
    "theta_A_D_projective_class_count",
    "theta_A_D_trace_zero_class_count",
    "theta_A_D_local_factors"
];
ado_write_csv_line(output_csv_filename, headers : clear_file := true);

index_start := (Type(index_start) eq MonStgElt) select StringToInteger(index_start) else index_start;
index_stop := (Type(index_stop) eq MonStgElt) select StringToInteger(index_stop) else index_stop;
index_stop := Min(index_stop, #OneClassGenera);

if progress_Print ge 1 then
    print "============================================================";
    print "Discriminant obstruction scan";
    print "table:", "OneClassGenera";
    print "index range:", index_start, "to", index_stop;
    print "exact projective order threshold:", exact_projective_order_threshold;
    print "output:", output_csv_filename;
    print "============================================================";
end if;

timer := Cputime();
orders_seen := 0;
orders_tested := 0;
orders_computed := 0;
orders_failed := 0;

for idx in [index_start..index_stop] do
    orders_seen +:= 1;
    entry := one_class_genera_entry(idx);

    // Type-one maximal orders of class number one.
    if entry[6] ne 4 or entry[7] ne 1 then
        continue;
    end if;

    orders_tested +:= 1;

    if progress_Print ge 1 then
        print "";
        print "------------------------------------------------------------";
        print Sprintf("[ADO order] idx=%o | eligible_order=%o", idx, orders_tested);
        print "------------------------------------------------------------";
    end if;

    order_data := order_data_from_index(idx);
    obstruction_values := [];

    try
        ado_compute_order_values(
            order_data,
            calculation_Print,
            time_limit_seconds,
            max_projective_quotient_seconds,
            max_reduced_unit_seconds,
            ~obstruction_values
        );
        orders_computed +:= 1;
    catch e
        target_factors := ado_target_factorization(order_data);
        target_modulus := ado_target_modulus(order_data`integer_ring, target_factors);
        obstruction_values := [
            bct_ideal_string(target_modulus),
            ado_factorization_string(target_factors),
            "error",
            Sprint(e`Object),
            "",
            "",
            "false",
            "",
            "",
            ""
        ];
        orders_failed +:= 1;
    end try;

    ado_write_csv_line(
        output_csv_filename,
        bct_order_context_values(order_data) cat obstruction_values
    );
end for;

if progress_Print ge 1 then
    print "";
    print "============================================================";
    print "Discriminant obstruction scan complete";
    print "orders_seen:", orders_seen;
    print "orders_tested:", orders_tested;
    print "orders_computed:", orders_computed;
    print "orders_failed:", orders_failed;
    print "elapsed_seconds:", Cputime(timer);
    print "output:", output_csv_filename;
    print "============================================================";
end if;
