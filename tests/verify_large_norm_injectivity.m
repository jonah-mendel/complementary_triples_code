// Verification test for the large-norm injectivity claim in Theorem 31.
//
// Run from the repository root:
//     magma tests/verify_large_norm_injectivity.m

test_csv_filename := "outputs/test_large_norm_injectivity_tests.csv";
order_summary_csv_filename := "outputs/test_large_norm_injectivity_order_summary.csv";
exception_csv_filename := "outputs/test_large_norm_injectivity_exceptions.csv";

calculation_Print := 0;
progress_Print := 0;
include_ramified_primes := false;
include_primes_in_T := false;
confirm_with_reduction := true;
fail_on_exception := true;

load "scripts/batch_large_norm_injectivity_exceptions.m";
