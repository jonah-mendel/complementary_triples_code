# Computations for *S-arithmetic groups acting simply transitively on products of Bruhat–Tits trees*

Magma code and data for our paper *S-arithmetic groups acting simply transitively on products of Bruhat–Tits trees*, by Jonah Mendel and Jiahui Yu ([arXiv:2305.04448](https://arxiv.org/abs/2305.04448)).

For each of the 49 maximal orders of class number one in totally definite quaternion algebras [1], we find all nontrivial minimal complementary triples and their torsion obstructions. The results are in `data/`, and the tables in Appendix A of our paper are made from them. We use the notation of our paper.

## Setup

The code needs Kirschmer's table of quaternion orders [2], which is not included. Download it from this folder:

```
curl -fsSL https://www.math.uni-bielefeld.de/~mkirschm/orders/smalltypenumber.tar.bz2 | tar -xjf - -C data
```

The file `data/smalltypenumber.m` has SHA-256 checksum `2f044b3345c129523b19d7f2bca21bad06f48675132d8cbe984af220fb02b27b`. We ran the code with Magma V2.30-1.

## Usage

`magma verify.m` checks the data and recomputes Lemmas 32–34, Theorems 35, 38 and 50, Proposition 42, Examples 19, 20, 37 and 49, and the Hurwitz and Lipschitz examples. It takes about 15 seconds.

`magma reproduce.m` recomputes `data/*.csv`. It takes about 45 minutes and needs a POSIX shell. Use `magma -b output_directory:=DIR reproduce.m` to write elsewhere, and set `MAGMA_CMD` if `magma` is not on your `PATH`.

To use the functions, run `load "load.m";` in Magma from this folder. For example, for the algebra of discriminant 5 at $T = \emptyset$ and $\mathfrak{C} = (5)$, with $S = \lbrace 2, 3 \rbrace$:

```magma
order_data := ClassOneOrder(5);
R := order_data`integer_ring;
result := ReductionData(order_data, [], 5*R);
presentation := PresentationForComplement(result, [2*R, 3*R]);
AbelianQuotientInvariants(presentation`gamma_group);
```

`ClassifyOrder(order_data)` returns every nontrivial minimal ideal and its complements, for every $T$.

## Data

| File | One row for each |
| --- | --- |
| `algebras.csv` | order |
| `localized_groups.csv` | pair $(\mathfrak{O}, T)$ |
| `minimal_ideals.csv` | minimal ideal $\mathfrak{C}$ for $T$ |
| `complements.csv` | conjugacy class of complements $H$ |

`order_index` is the row of the order in Kirschmer's table. An ideal is written as its norm followed by its basis matrix in Hermite normal form; over $\mathbb{Q}$, the ideal $(5)$ is `5:[ 5 ]`. `minimal_ideals.csv` includes ideals with no complement (`has_complement` is `false`). The `theta` columns are empty when $\mathfrak{C}$ is not coprime to $T$. A new run of `reproduce.m` may order the rows and number the complements differently.

## Code

| File | Contents |
| --- | --- |
| `src/orders.m` | order records and ideals |
| `src/quotients.m` | the groups $G[\mathfrak{p}^k]$ and $W_{\mathfrak{p}}^k$ |
| `src/classification.m` | $\Gamma_T$, reduction, minimal ideals and complements |
| `src/obstructions.m` | the sets $\Theta$ and $\mathfrak{e}(\mathfrak{a})$ |
| `src/presentations.m` | the presentations of $\Gamma_S(\mathfrak{C}, H)$ |

## References

1. Markus Kirschmer and John Voight, *Algorithmic enumeration of ideal classes for quaternion orders*, SIAM Journal on Computing 39 (2010), no. 5, 1714–1747.
2. Markus Kirschmer, *Quaternion orders of type number one and two*, <https://www.math.uni-bielefeld.de/~mkirschm/orders/>.

## License

The code and `data/*.csv` are released under the [MIT License](LICENSE). `data/smalltypenumber.m` is Kirschmer's work and is not covered by it.
