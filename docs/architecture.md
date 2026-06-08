# Architecture

The package separates arithmetic construction, finite quotient computation,
batch export, presentation construction, and verification of the paper's
computational claims.

## Layers

1. `order_data.m`
   Builds a record for one quaternion order, either from `OneClassGenera` or
   from an explicit Magma order.  The supported base fields have class number
   one.

2. `projective_unit_group.m`
   Builds the finite groups `(O / C O)^* / (R / C)^*`, embeds unit and
   normalizer images, and computes complement classes.

3. `complementary_ideals.m`
   Builds localized groups `Gamma_T`, computes reduction images at ideals `C`,
   assembles composite ideals from prime-power factors, and records
   complementary triples.

4. `local_norm_pipeline.m`
   Computes trace/norm forms and square-class obstruction summaries attached to
   complementary results.

5. `lifted_torsion_obstruction.m`
   Computes the lifted torsion obstruction used in the appendix table.

6. `presentation_pipeline.m` and `presentation_sigma_relations.m`
   Build presentations of selected `S`-arithmetic groups by choosing
   representatives whose reductions land in a complement subgroup.

7. `batch_exports.m`
   Writes long-form CSVs for the main scans.  CSV files in `outputs/` are run
   products, not source data.

8. `scripts/`
   Contains reproducible scan drivers for the computations used in the paper.

9. `tests/`
   Contains verification commands for computational claims used in the paper.

## Public Entry Points

- `order_data_from_index(idx)`
- `build_order_data_for_order(...)`
- `build_maximal_orders(base_field, quaternion_algebra)`
- `complementary_pairs_at_ideal(order_data, C : T := [])`
- `scan_prime_power_complementary_triples(order_data, P, max_exponent : T := [])`
- `minimal_ideal_poset(order_data, T, prime_norm_bound)`
- `scan_order_for_complementary_triples(order_data, prime_norm_bound)`
- `scan_orders_for_complementary_triples(order_list, prime_norm_bound)`
- `local_norm_summary_for_complementary_result(result, complement_index)`
- `lifted_torsion_obstruction_summary(result, complement_index)`
- `build_presentation_for_complementary_result(result, S)`
- `build_presentation_for_complementary_triple(triple, S)`

## Prime Norm Bound Convention

In the complementary-triple scan functions, `norm_bound` is a prime norm bound:
split primes up to this norm are considered, while finite ramified primes of the
quaternion algebra are also included by the scan.
