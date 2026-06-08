// ============================================================================
// Complementary-triples computation package loader.
//
// Run from the repository root with:
//     load "load.m";
// Magma resolves load paths relative to its current working directory, not
// relative to this file.
//
// This package expects Kirschmer's smalltypenumber.m file at
// data/smalltypenumber.m.  See data/README.md for download instructions.
//
// Public scope: class-number-one base fields only.
// ============================================================================

if not FileExists("data/smalltypenumber.m") then
    error "Missing data/smalltypenumber.m. Download smalltypenumber.m from https://www.math.uni-bielefeld.de/~mkirschm/orders/ and place it in data/.";
end if;

load "data/smalltypenumber.m";
load "src/order_data.m";
load "src/projective_unit_group.m";
load "src/arithmetic_utils.m";
load "src/complementary_ideals.m";
load "src/local_norm_pipeline.m";
load "src/lifted_torsion_obstruction.m";
load "src/presentation_sigma_relations.m";
load "src/presentation_pipeline.m";
load "src/batch_exports.m";
