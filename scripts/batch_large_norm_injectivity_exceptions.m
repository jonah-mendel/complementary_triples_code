// Batch scan for exceptions to large-norm injectivity.
//
// For every class-one maximal order O in OneClassGenera, and every admissible
// T subset Ram_f(B), this script checks the claim used in Theorem 31:
//
//     if P is split and Norm(P) > #Gamma_T, then Gamma_T -> G[P] is injective.
//
// The scan is finite.  For each nontrivial element x in Gamma_T, it first
// computes the finite set of primes where x can reduce to a scalar modulo P.
// Only those primes can cause non-injectivity.  The script then confirms each
// candidate prime using the finite-quotient reduction routine.
//
// Run from the repository root:
//     magma scripts/batch_large_norm_injectivity_exceptions.m

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
    max_reduced_unit_seconds := 1000;
end if;

// The theorem only needs split primes.  Set this to true for a broader
// diagnostic scan; ramified primes are reported separately in the CSV.
if not assigned include_ramified_primes then
    include_ramified_primes := false;
end if;

// Usually P should not lie in T for the ordinary map Gamma_T -> G[P].
if not assigned include_primes_in_T then
    include_primes_in_T := false;
end if;

// If false, the script only records scalar-collision candidates.  If true, it
// also confirms injectivity using the finite-quotient reduction routine.
if not assigned confirm_with_reduction then
    confirm_with_reduction := true;
end if;

if not assigned test_csv_filename then
    test_csv_filename := "outputs/large_norm_injectivity_tests.csv";
end if;

if not assigned order_summary_csv_filename then
    order_summary_csv_filename := "outputs/large_norm_injectivity_order_summary.csv";
end if;

if not assigned exception_csv_filename then
    exception_csv_filename := "outputs/large_norm_injectivity_exceptions.csv";
end if;

if not assigned fail_on_exception then
    fail_on_exception := false;
end if;

// ========================================================================
// Implementation below. Usually no edits needed below this line.
// ========================================================================

function lnit_integer_parameter(value, parameter_name)
    if Type(value) eq RngIntElt then
        return value;
    end if;

    if Type(value) eq MonStgElt then
        return StringToInteger(value);
    end if;

    error Sprintf("%o must be an integer or an integer string.", parameter_name);
end function;


function lnit_bool_parameter(value, parameter_name)
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


function lnit_string(value)
    if Type(value) eq MonStgElt then
        return value;
    end if;

    return Sprint(value);
end function;


function lnit_csv_row(values)
    return bct_csv_row([lnit_string(value) : value in values]);
end function;


procedure lnit_write_csv_line(filename, values : clear_file := false)
    mode := clear_file select "w" else "a";
    file_handle := Open(filename, mode);
    Puts(file_handle, lnit_csv_row(values));
    Flush(file_handle);
    delete file_handle;
end procedure;


function lnit_group_type_string(group_g)
    try
        return Sprint(IdentifyGroup(group_g));
    catch error_object
        return "";
    end try;
end function;


function lnit_ideal_less_than(ideal_a, ideal_b)
    norm_a := Norm(ideal_a);
    norm_b := Norm(ideal_b);

    if norm_a ne norm_b then
        return norm_a lt norm_b;
    end if;

    return Sprint(ideal_a) lt Sprint(ideal_b);
end function;


function lnit_sorted_ideals_by_norm(ideal_list)
    remaining := complementary_sorted_ideals(ideal_list);
    sorted_ideals := [];

    while #remaining gt 0 do
        minimal_index := 1;

        for i in [2..#remaining] do
            if lnit_ideal_less_than(remaining[i], remaining[minimal_index]) then
                minimal_index := i;
            end if;
        end for;

        Append(~sorted_ideals, remaining[minimal_index]);
        Remove(~remaining, minimal_index);
    end while;

    return sorted_ideals;
end function;


function lnit_ideal_sequence_string(ideal_list)
    return bct_ideal_sequence_string(lnit_sorted_ideals_by_norm(ideal_list));
end function;


function lnit_prime_ramifies(order_data, prime_ideal)
    return Valuation(Discriminant(order_data`quaternion_algebra), prime_ideal) ne 0;
end function;


function lnit_prime_in_T(localized_group, prime_ideal)
    return Index(localized_group`ramified_subset, prime_ideal) ne 0;
end function;


function lnit_prime_allowed(order_data, localized_group, prime_ideal)
    if Norm(prime_ideal) le localized_group`subgroup_order then
        return false;
    end if;

    if (not include_ramified_primes) and lnit_prime_ramifies(order_data, prime_ideal) then
        return false;
    end if;

    if (not include_primes_in_T) and lnit_prime_in_T(localized_group, prime_ideal) then
        return false;
    end if;

    return true;
end function;


function lnit_coordinates_in_order_basis(order_data, element_x)
    coordinates := order_coordinates_in_basis(
        order_data`base_field,
        order_data`quaternion_algebra,
        order_data`principal_basis,
        element_x
    );

    integer_coordinates := [];
    for coefficient in coordinates do
        if not (coefficient in order_data`integer_ring) then
            error "Expected an integral order-basis coordinate.";
        end if;

        Append(~integer_coordinates, order_data`integer_ring!coefficient);
    end for;

    return integer_coordinates;
end function;


function lnit_scalar_collision_primes_for_element(order_data, element_x)
    integer_ring := order_data`integer_ring;
    one_coordinates := lnit_coordinates_in_order_basis(order_data, order_data`quaternion_order!1);
    element_coordinates := lnit_coordinates_in_order_basis(order_data, element_x);
    minors := [];

    for i in [1..#one_coordinates] do
        for j in [i + 1..#one_coordinates] do
            minor := one_coordinates[i] * element_coordinates[j] -
                     one_coordinates[j] * element_coordinates[i];
            if minor ne integer_ring!0 then
                Append(~minors, minor);
            end if;
        end for;
    end for;

    if #minors eq 0 then
        return [], true;
    end if;

    collision_ideal := ideal<integer_ring | minors>;

    if collision_ideal eq ideal<integer_ring | 1> then
        return [], false;
    end if;

    return lnit_sorted_ideals_by_norm([factor[1] : factor in Factorization(collision_ideal)]), false;
end function;


procedure lnit_add_candidate_prime(
    ~candidate_primes,
    ~candidate_lookup,
    ~source_count_lookup,
    prime_ideal
)
    key := Sprint(prime_ideal);

    if IsDefined(candidate_lookup, key) then
        source_count_lookup[key] := source_count_lookup[key] + 1;
        return;
    end if;

    candidate_lookup[key] := true;
    source_count_lookup[key] := 1;
    Append(~candidate_primes, prime_ideal);
end procedure;


function lnit_candidate_primes_for_group(order_data, context, localized_group)
    candidate_primes := [];
    candidate_lookup := AssociativeArray();
    source_count_lookup := AssociativeArray();
    scalar_representative_count := 0;
    nonidentity_element_count := 0;

    for group_element in localized_group`subgroup do
        if group_element eq Identity(localized_group`subgroup) then
            continue;
        end if;

        nonidentity_element_count +:= 1;
        representative := complementary_normalizer_representative(context, group_element);
        collision_primes, representative_is_scalar :=
            lnit_scalar_collision_primes_for_element(order_data, representative);

        if representative_is_scalar then
            scalar_representative_count +:= 1;
            continue;
        end if;

        for prime_ideal in collision_primes do
            if lnit_prime_allowed(order_data, localized_group, prime_ideal) then
                lnit_add_candidate_prime(
                    ~candidate_primes,
                    ~candidate_lookup,
                    ~source_count_lookup,
                    prime_ideal
                );
            end if;
        end for;
    end for;

    return lnit_sorted_ideals_by_norm(candidate_primes),
           source_count_lookup,
           scalar_representative_count,
           nonidentity_element_count;
end function;


function lnit_result_status(local_result)
    if Type(local_result) ne Rec then
        return "error";
    end if;

    if local_result`skipped_due_to_estimate then
        return "skipped_estimate";
    end if;

    if local_result`injective then
        return "pass";
    end if;

    return "fail_noninjective";
end function;


function lnit_result_bool_field(local_result, field_name)
    if Type(local_result) ne Rec then
        return "";
    end if;

    if field_name eq "skipped_due_to_estimate" then
        return bct_bool_string(local_result`skipped_due_to_estimate);
    elif field_name eq "injective" then
        if local_result`skipped_due_to_estimate then
            return "";
        end if;
        return bct_bool_string(local_result`injective);
    elif field_name eq "uses_ramified_extension" then
        if local_result`skipped_due_to_estimate then
            return "";
        end if;
        return bct_bool_string(local_result`uses_ramified_extension);
    end if;

    return "";
end function;


function lnit_result_image_order(local_result)
    if Type(local_result) ne Rec or local_result`skipped_due_to_estimate then
        return "";
    end if;

    return Sprint(#local_result`image_subgroup);
end function;


function lnit_result_ambient_order(local_result)
    if Type(local_result) ne Rec or local_result`skipped_due_to_estimate then
        return "";
    end if;

    return Sprint(#local_result`ambient_group);
end function;


function lnit_result_skipped_task(local_result)
    if Type(local_result) eq Rec and local_result`skipped_due_to_estimate then
        return local_result`skipped_task_key;
    end if;

    return "";
end function;


function lnit_result_skipped_seconds(local_result)
    if Type(local_result) eq Rec and local_result`skipped_due_to_estimate then
        return Sprint(local_result`skipped_estimated_seconds);
    end if;

    return "";
end function;


function lnit_test_headers()
    return bct_order_context_headers() cat [
        "T_prime_count",
        "T_primes",
        "gamma_T_order",
        "gamma_T_type",
        "candidate_prime_count_for_T",
        "candidate_source_count",
        "test_prime_norm",
        "test_prime_ideal",
        "prime_ramified_in_B",
        "prime_in_T",
        "status",
        "message",
        "skipped_due_to_estimate",
        "skipped_task",
        "skipped_estimated_seconds",
        "injective",
        "source_order",
        "image_order",
        "ambient_order",
        "uses_ramified_extension"
    ];
end function;


function lnit_order_summary_headers()
    return bct_order_context_headers() cat [
        "admissible_ramified_prime_count",
        "admissible_ramified_primes",
        "localized_T_count",
        "localized_T_count_with_candidates",
        "nonidentity_element_count",
        "scalar_representative_count",
        "candidate_prime_count",
        "test_count",
        "pass_count",
        "failure_count",
        "skipped_count",
        "error_count"
    ];
end function;


procedure lnit_write_test_row(
    filename,
    order_data,
    localized_group,
    candidate_prime_count_for_T,
    candidate_source_count,
    test_prime,
    local_result,
    status,
    message
)
    lnit_write_csv_line(
        filename,
        bct_order_context_values(order_data) cat [
            Sprint(#localized_group`ramified_subset),
            lnit_ideal_sequence_string(localized_group`ramified_subset),
            Sprint(localized_group`subgroup_order),
            lnit_group_type_string(localized_group`subgroup),
            Sprint(candidate_prime_count_for_T),
            Sprint(candidate_source_count),
            Sprint(Norm(test_prime)),
            bct_ideal_string(test_prime),
            bct_bool_string(lnit_prime_ramifies(order_data, test_prime)),
            bct_bool_string(lnit_prime_in_T(localized_group, test_prime)),
            status,
            message,
            lnit_result_bool_field(local_result, "skipped_due_to_estimate"),
            lnit_result_skipped_task(local_result),
            lnit_result_skipped_seconds(local_result),
            lnit_result_bool_field(local_result, "injective"),
            Sprint(localized_group`subgroup_order),
            lnit_result_image_order(local_result),
            lnit_result_ambient_order(local_result),
            lnit_result_bool_field(local_result, "uses_ramified_extension")
        ]
    );
end procedure;


procedure lnit_run_one_test(
    ~context,
    order_data,
    localized_group,
    candidate_prime_count_for_T,
    candidate_source_count,
    test_prime,
    ~test_count,
    ~pass_count,
    ~failure_count,
    ~skipped_count,
    ~error_count,
    ~total_test_count,
    ~total_pass_count,
    ~total_failure_count,
    ~total_skipped_count,
    ~total_error_count
)
    test_count +:= 1;
    total_test_count +:= 1;

    if not confirm_with_reduction then
        status := "candidate_unconfirmed";
        message := "scalar-collision candidate; reduction confirmation disabled";
        lnit_write_test_row(
            test_csv_filename,
            order_data,
            localized_group,
            candidate_prime_count_for_T,
            candidate_source_count,
            test_prime,
            false,
            status,
            message
        );
        return;
    end if;

    try
        local_result := false;
        complementary_local_reduction_image(
            ~context,
            localized_group,
            test_prime,
            1,
            ~local_result :
            Print := calculation_Print,
            time_limit_seconds := time_limit_seconds,
            max_projective_quotient_seconds := max_projective_quotient_seconds,
            max_reduced_unit_seconds := max_reduced_unit_seconds
        );

        status := lnit_result_status(local_result);
        message := "";

        if status eq "pass" then
            pass_count +:= 1;
            total_pass_count +:= 1;
        elif status eq "skipped_estimate" then
            skipped_count +:= 1;
            total_skipped_count +:= 1;
        else
            failure_count +:= 1;
            total_failure_count +:= 1;
        end if;

        lnit_write_test_row(
            test_csv_filename,
            order_data,
            localized_group,
            candidate_prime_count_for_T,
            candidate_source_count,
            test_prime,
            local_result,
            status,
            message
        );

        if status ne "pass" then
            lnit_write_test_row(
                exception_csv_filename,
                order_data,
                localized_group,
                candidate_prime_count_for_T,
                candidate_source_count,
                test_prime,
                local_result,
                status,
                message
            );
        end if;
    catch error_object
        error_count +:= 1;
        total_error_count +:= 1;
        message := Sprint(error_object`Object);
        lnit_write_test_row(
            test_csv_filename,
            order_data,
            localized_group,
            candidate_prime_count_for_T,
            candidate_source_count,
            test_prime,
            false,
            "error",
            message
        );
        lnit_write_test_row(
            exception_csv_filename,
            order_data,
            localized_group,
            candidate_prime_count_for_T,
            candidate_source_count,
            test_prime,
            false,
            "error",
            message
        );
    end try;
end procedure;


index_start := lnit_integer_parameter(index_start, "index_start");
index_stop := lnit_integer_parameter(index_stop, "index_stop");
calculation_Print := lnit_integer_parameter(calculation_Print, "calculation_Print");
progress_Print := lnit_integer_parameter(progress_Print, "progress_Print");
time_limit_seconds := lnit_integer_parameter(time_limit_seconds, "time_limit_seconds");
max_projective_quotient_seconds := lnit_integer_parameter(max_projective_quotient_seconds, "max_projective_quotient_seconds");
max_reduced_unit_seconds := lnit_integer_parameter(max_reduced_unit_seconds, "max_reduced_unit_seconds");
include_ramified_primes := lnit_bool_parameter(include_ramified_primes, "include_ramified_primes");
include_primes_in_T := lnit_bool_parameter(include_primes_in_T, "include_primes_in_T");
confirm_with_reduction := lnit_bool_parameter(confirm_with_reduction, "confirm_with_reduction");
fail_on_exception := lnit_bool_parameter(fail_on_exception, "fail_on_exception");

if index_start lt 1 or index_start gt #OneClassGenera then
    error "index_start is outside the OneClassGenera table.";
end if;

if index_stop lt index_start then
    error "index_stop must be >= index_start.";
end if;

index_stop := Min(index_stop, #OneClassGenera);

print "";
print "============================================================";
print "Batch Large-Norm Injectivity Exception Scan";
print "============================================================";
print "table:", "OneClassGenera";
print "index start:", index_start;
print "index stop:", index_stop;
print "order filter:", "class_number=1 and order_type=4";
print "condition:", "Norm(P) > #Gamma_T";
print "include ramified primes:", include_ramified_primes;
print "include primes in T:", include_primes_in_T;
print "confirm with reduction:", confirm_with_reduction;
print "test CSV:", test_csv_filename;
print "order summary CSV:", order_summary_csv_filename;
print "exception CSV:", exception_csv_filename;
print "";

lnit_write_csv_line(test_csv_filename, lnit_test_headers() : clear_file := true);
lnit_write_csv_line(order_summary_csv_filename, lnit_order_summary_headers() : clear_file := true);
lnit_write_csv_line(exception_csv_filename, lnit_test_headers() : clear_file := true);

orders_seen := 0;
orders_tested := 0;
orders_with_candidates := 0;
total_test_count := 0;
total_pass_count := 0;
total_failure_count := 0;
total_skipped_count := 0;
total_error_count := 0;

for idx in [index_start..index_stop] do
    orders_seen +:= 1;
    entry := one_class_genera_entry(idx);

    if entry[6] ne 4 or entry[7] ne 1 then
        continue;
    end if;

    order_data := order_data_from_index(idx);
    orders_tested +:= 1;
    context, localized_groups := complementary_context_with_all_U_T(order_data);
    admissible_primes := admissible_ramified_primes(order_data);
    localized_T_count_with_candidates := 0;
    nonidentity_element_count := 0;
    scalar_representative_count := 0;
    candidate_prime_count := 0;
    test_count := 0;
    pass_count := 0;
    failure_count := 0;
    skipped_count := 0;
    error_count := 0;

    if progress_Print ge 1 then
        print Sprintf(
            "idx=%o | degree=%o | dK=%o | T_subsets=%o",
            idx,
            Degree(order_data`base_field),
            Discriminant(order_data`integer_ring),
            #localized_groups
        );
    end if;

    for localized_group in localized_groups do
        candidate_primes, source_count_lookup, scalar_count_for_T, nonidentity_count_for_T :=
            lnit_candidate_primes_for_group(order_data, context, localized_group);

        nonidentity_element_count +:= nonidentity_count_for_T;
        scalar_representative_count +:= scalar_count_for_T;
        candidate_prime_count +:= #candidate_primes;

        if #candidate_primes gt 0 then
            localized_T_count_with_candidates +:= 1;
        end if;

        if progress_Print ge 2 and #candidate_primes gt 0 then
            print Sprintf(
                "  T=%o | #Gamma_T=%o | candidates=%o",
                bct_ramified_subset_summary(localized_group`ramified_subset),
                localized_group`subgroup_order,
                #candidate_primes
            );
        end if;

        for test_prime in candidate_primes do
            lnit_run_one_test(
                ~context,
                order_data,
                localized_group,
                #candidate_primes,
                source_count_lookup[Sprint(test_prime)],
                test_prime,
                ~test_count,
                ~pass_count,
                ~failure_count,
                ~skipped_count,
                ~error_count,
                ~total_test_count,
                ~total_pass_count,
                ~total_failure_count,
                ~total_skipped_count,
                ~total_error_count
            );
        end for;
    end for;

    if candidate_prime_count gt 0 then
        orders_with_candidates +:= 1;
    end if;

    lnit_write_csv_line(
        order_summary_csv_filename,
        bct_order_context_values(order_data) cat [
            Sprint(#admissible_primes),
            lnit_ideal_sequence_string(admissible_primes),
            Sprint(#localized_groups),
            Sprint(localized_T_count_with_candidates),
            Sprint(nonidentity_element_count),
            Sprint(scalar_representative_count),
            Sprint(candidate_prime_count),
            Sprint(test_count),
            Sprint(pass_count),
            Sprint(failure_count),
            Sprint(skipped_count),
            Sprint(error_count)
        ]
    );
end for;

print "";
print "============================================================";
print "Batch Large-Norm Injectivity Exception Scan Complete";
print "============================================================";
print "indices seen:", orders_seen;
print "orders tested:", orders_tested;
print "orders with candidate primes:", orders_with_candidates;
print "tests:", total_test_count;
print "passes:", total_pass_count;
print "failures:", total_failure_count;
print "skipped:", total_skipped_count;
print "errors:", total_error_count;
print "test CSV:", test_csv_filename;
print "order summary CSV:", order_summary_csv_filename;
print "exception CSV:", exception_csv_filename;

if total_failure_count eq 0 and total_skipped_count eq 0 and total_error_count eq 0 then
    print "PASS: no large-norm injectivity exceptions were found.";
else
    print "FAIL: at least one large-norm injectivity test failed, skipped, or errored.";
end if;

if fail_on_exception and (total_failure_count gt 0 or total_skipped_count gt 0 or total_error_count gt 0) then
    error "Some large-norm injectivity tests failed, skipped, or errored.";
end if;
