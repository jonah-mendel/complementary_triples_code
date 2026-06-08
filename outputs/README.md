# Outputs

Generated CSVs from the complementary-triples computations belong here.

The CSVs in this directory are the recorded outputs used by the paper.  They
are included so readers can inspect the computed data directly and verify the
appendix tables without first rerunning the longest scans.

- `nontrivial_complementary_triples*.csv`: the non-trivial minimal
  complementary triples appearing in the appendix tables, together with the
  order, field, algebra, set `T`, complementary ideal, complement counts, and
  torsion-obstruction data.
- `complementary_gamma_types.csv`: group-type data used to format the appendix
  table.
- `lifted_obstructions.csv`: lifted torsion obstruction data used in the
  appendix table.
- `discriminant_obstructions.csv`: torsion obstruction data attached to the
  discriminant ideal.
- `unit_representative_norm_one*.csv`: norm-one representative verification.
- `large_norm_injectivity*.csv`: large-norm injectivity verification.

Some verification CSVs contain only a header row. This means that the scan
found no failures or exceptions of that type.

These files are reproducible from the commands documented in `../README.md`.
Ignored `test_*.csv` files may also appear here after running files in
`../tests/`.
