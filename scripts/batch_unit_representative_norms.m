// Batch test for the stored quaternion representatives of O^*.
//
// For every class-one maximal order in OneClassGenera, this script builds
// order_data_from_index(idx) and checks whether every element of
// order_data`unit_elements has reduced norm 1.
//
// Run from the repository root:
//     magma scripts/batch_unit_representative_norms.m

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

if not assigned progress_Print then
    progress_Print := 1;
end if;

if not assigned summary_csv_filename then
    summary_csv_filename := "outputs/unit_representative_norm_one_summary.csv";
end if;

if not assigned failure_csv_filename then
    failure_csv_filename := "outputs/unit_representative_norm_one_failures.csv";
end if;

if not assigned fail_on_failure then
    fail_on_failure := false;
end if;

// ========================================================================
// Implementation below. Usually no edits needed below this line.
// ========================================================================

function burn_integer_parameter(value, parameter_name)
    if Type(value) eq RngIntElt then
        return value;
    end if;

    if Type(value) eq MonStgElt then
        return StringToInteger(value);
    end if;

    error Sprintf("%o must be an integer or an integer string.", parameter_name);
end function;


function burn_bool_parameter(value, parameter_name)
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


function burn_string(value)
    if Type(value) eq MonStgElt then
        return value;
    end if;

    return Sprint(value);
end function;


function burn_csv_row(values)
    return bct_csv_row([burn_string(value) : value in values]);
end function;


procedure burn_write_csv_line(filename, values : clear_file := false)
    mode := clear_file select "w" else "a";
    file_handle := Open(filename, mode);
    Puts(file_handle, burn_csv_row(values));
    Flush(file_handle);
    delete file_handle;
end procedure;


procedure burn_append_string_if_new(value, ~values)
    value_string := burn_string(value);

    for existing_value in values do
        if existing_value eq value_string then
            return;
        end if;
    end for;

    Append(~values, value_string);
end procedure;


function burn_sequence_string(sequence)
    return bct_join_strings([burn_string(x) : x in sequence], " ; ");
end function;


function burn_ambient_coefficients_string(order_data, unit_element)
    return burn_sequence_string(Eltseq(order_data`quaternion_algebra!unit_element));
end function;


function burn_principal_coordinates_string(order_data, unit_element)
    coordinates := order_coordinates_in_basis(
        order_data`base_field,
        order_data`quaternion_algebra,
        order_data`principal_basis,
        unit_element
    );

    return burn_sequence_string(coordinates);
end function;


function burn_summary_headers()
    return bct_order_context_headers() cat [
        "unit_group_order",
        "unit_representative_count",
        "norm_one_count",
        "failure_count",
        "all_norm_one",
        "distinct_norm_values",
        "first_failure_index",
        "first_failure_norm",
        "first_failure_ambient_coefficients",
        "first_failure_principal_coordinates"
    ];
end function;


function burn_failure_headers()
    return bct_order_context_headers() cat [
        "unit_index",
        "unit_norm",
        "unit_ambient_coefficients",
        "unit_principal_coordinates"
    ];
end function;


procedure burn_write_failure_row(filename, order_data, unit_index, unit_element, norm_value)
    burn_write_csv_line(
        filename,
        bct_order_context_values(order_data) cat [
            Sprint(unit_index),
            burn_string(norm_value),
            burn_ambient_coefficients_string(order_data, unit_element),
            burn_principal_coordinates_string(order_data, unit_element)
        ]
    );
end procedure;


procedure burn_test_order(
    order_data,
    summary_filename,
    failure_filename,
    ~unit_representatives_tested,
    ~failed_order_count,
    ~total_failure_count
)
    norm_one_count := 0;
    failure_count := 0;
    distinct_norm_values := [];
    first_failure_index := "";
    first_failure_norm := "";
    first_failure_ambient_coefficients := "";
    first_failure_principal_coordinates := "";

    for unit_index in [1..#order_data`unit_elements] do
        unit_element := order_data`unit_elements[unit_index];
        norm_value := Norm(unit_element);
        burn_append_string_if_new(norm_value, ~distinct_norm_values);
        unit_representatives_tested +:= 1;

        if norm_value eq order_data`base_field!1 then
            norm_one_count +:= 1;
            continue;
        end if;

        failure_count +:= 1;
        total_failure_count +:= 1;

        if first_failure_index eq "" then
            first_failure_index := Sprint(unit_index);
            first_failure_norm := burn_string(norm_value);
            first_failure_ambient_coefficients := burn_ambient_coefficients_string(order_data, unit_element);
            first_failure_principal_coordinates := burn_principal_coordinates_string(order_data, unit_element);
        end if;

        burn_write_failure_row(failure_filename, order_data, unit_index, unit_element, norm_value);
    end for;

    if failure_count gt 0 then
        failed_order_count +:= 1;
    end if;

    burn_write_csv_line(
        summary_filename,
        bct_order_context_values(order_data) cat [
            Sprint(#order_data`unit_group),
            Sprint(#order_data`unit_elements),
            Sprint(norm_one_count),
            Sprint(failure_count),
            bct_bool_string(failure_count eq 0),
            bct_join_strings(distinct_norm_values, " ; "),
            first_failure_index,
            first_failure_norm,
            first_failure_ambient_coefficients,
            first_failure_principal_coordinates
        ]
    );
end procedure;


index_start := burn_integer_parameter(index_start, "index_start");
index_stop := burn_integer_parameter(index_stop, "index_stop");
progress_Print := burn_integer_parameter(progress_Print, "progress_Print");
fail_on_failure := burn_bool_parameter(fail_on_failure, "fail_on_failure");

if index_start lt 1 or index_start gt #OneClassGenera then
    error "index_start is outside the OneClassGenera table.";
end if;

if index_stop lt index_start then
    error "index_stop must be >= index_start.";
end if;

index_stop := Min(index_stop, #OneClassGenera);

print "";
print "============================================================";
print "Batch Unit Representative Norm-One Test";
print "============================================================";
print "table:", "OneClassGenera";
print "index start:", index_start;
print "index stop:", index_stop;
print "order filter:", "class_number=1 and order_type=4";
print "summary CSV:", summary_csv_filename;
print "failure CSV:", failure_csv_filename;
print "";

burn_write_csv_line(summary_csv_filename, burn_summary_headers() : clear_file := true);
burn_write_csv_line(failure_csv_filename, burn_failure_headers() : clear_file := true);

orders_seen := 0;
orders_tested := 0;
unit_representatives_tested := 0;
failed_order_count := 0;
total_failure_count := 0;

for idx in [index_start..index_stop] do
    orders_seen +:= 1;
    entry := one_class_genera_entry(idx);
    order_type := entry[6];
    class_number := entry[7];

    if order_type ne 4 or class_number ne 1 then
        continue;
    end if;

    order_data := order_data_from_index(idx);
    orders_tested +:= 1;

    if progress_Print ge 1 then
        print Sprintf(
            "idx=%o | degree=%o | dK=%o | disc=%o | unit_count=%o",
            idx,
            Degree(order_data`base_field),
            Discriminant(order_data`integer_ring),
            bct_ideal_string(order_data`order_discriminant),
            #order_data`unit_elements
        );
    end if;

    burn_test_order(
        order_data,
        summary_csv_filename,
        failure_csv_filename,
        ~unit_representatives_tested,
        ~failed_order_count,
        ~total_failure_count
    );
end for;

print "";
print "============================================================";
print "Batch Unit Representative Norm-One Test Complete";
print "============================================================";
print "indices seen:", orders_seen;
print "orders tested:", orders_tested;
print "unit representatives tested:", unit_representatives_tested;
print "orders with failures:", failed_order_count;
print "non-norm-one representatives:", total_failure_count;
print "summary CSV:", summary_csv_filename;
print "failure CSV:", failure_csv_filename;

if total_failure_count eq 0 then
    print "PASS: every stored unit representative has norm 1.";
else
    print "FAIL: at least one stored unit representative has norm different from 1.";
end if;

if total_failure_count gt 0 and fail_on_failure then
    error "Some stored unit representatives have norm different from 1.";
end if;
