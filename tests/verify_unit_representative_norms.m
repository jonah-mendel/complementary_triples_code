// Verification test for the norm-one representative claim.
//
// Run from the repository root:
//     magma tests/verify_unit_representative_norms.m

summary_csv_filename := "outputs/test_unit_representative_norm_one_summary.csv";
failure_csv_filename := "outputs/test_unit_representative_norm_one_failures.csv";
progress_Print := 0;
fail_on_failure := true;

load "scripts/batch_unit_representative_norms.m";
