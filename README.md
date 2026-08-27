# Magma code for "S-arithmetic groups acting simply transitively on products of Bruhat–Tits trees"

This repository contains the Magma code and computed data supporting the paper

> Jonah Mendel and Jiahui Yu, *S-arithmetic groups acting simply transitively
> on products of Bruhat–Tits trees*.

Mendel–Yu classify the nontrivial minimal complementary triples of class
number one maximal orders in totally definite quaternion algebras and use them
to construct simply transitive lattices on products of Bruhat–Tits trees.  This
repository holds the computations behind that classification: the four CSV
files in `data/` are the complete computational output, and the tables of
Mendel–Yu's Appendix A are generated from them.

## What is computed

Let $B$ be one of the 49 totally definite quaternion algebras over a number field $K$ that admit a maximal order of class number one (as enumerated by Kirschmer–Voight [1]), and let $\mathfrak{O} \subseteq B$ be such an order. For $T \subseteq \mathrm{Ram}_f(B)$, write

$$
\Gamma_{\mathfrak{O},T} = \mathfrak{O}[1/T]^\times/\mathcal{O}_K[1/T]^\times.
$$

(see Mendel–Yu, Section 3.1)

For an integral ideal $\mathfrak{C} \subseteq \mathcal{O}_K$, put

$$
G_{\mathfrak{O}}[\mathfrak{C}] = (\mathfrak{O}/\mathfrak{C}\mathfrak{O})^\times/(\mathcal{O}_K/\mathfrak{C})^\times.
$$

When the order is clear, we drop the order subscript in both groups.
When a prime $\mathfrak{p}$ ramifies in $B$, the completion $B_{\mathfrak{p}}$ is a division algebra. Write $\mathfrak{P}$ for the maximal ideal of its local maximal order; then $\mathfrak{P}^2$ is $\mathfrak{p}$ times that order. Set

$$
U_{\mathfrak{p}}^k = \mathfrak{O}_{\mathfrak{p}}^\times/(\mathcal{O}_{K,\mathfrak{p}}^\times \cdot (1 + \mathfrak{P}^{2k})),
\qquad
W_{\mathfrak{p}}^k = B_{\mathfrak{p}}^\times/(K_{\mathfrak{p}}^\times \cdot (1 + \mathfrak{P}^{2k})).
$$

They fit into the split exact sequence

$$
1 \to U_{\mathfrak{p}}^k \to W_{\mathfrak{p}}^k \to C_2 \to 1.
$$

(see Mendel–Yu, Section 2.3.2)

We can identify $U_{\mathfrak{p}}^k$ with $G_{\mathfrak{O}}[\mathfrak{p}^k]$.
For an integral ideal $\mathfrak{C}$, set

$$
G_{\mathfrak{O},T}[\mathfrak{C}] = \prod_{\mathfrak{p} \mid \mathfrak{C}} G_{\mathfrak{O},T}[\mathfrak{p}^{v_{\mathfrak{p}}(\mathfrak{C})}],
\qquad
G_{\mathfrak{O},T}[\mathfrak{p}^k] =
\begin{cases}
W_{\mathfrak{p}}^k, & \mathfrak{p} \in T, \\
G_{\mathfrak{O}}[\mathfrak{p}^k], & \mathfrak{p} \notin T.
\end{cases}
$$

Reduction gives

$$
\pi_{\mathfrak{O},T,\mathfrak{C}}\colon \Gamma_{\mathfrak{O},T} \to G_{\mathfrak{O},T}[\mathfrak{C}]
$$

(see Mendel–Yu, Sections 5.1–5.2)

A complementary triple is a triple $(T,\mathfrak{C},H)$ in which $\pi_{T,\mathfrak{C}}$ is injective and $H$ is complementary to $\pi_{T,\mathfrak{C}}(\Gamma_{\mathfrak{O},T})$; that is,

$$
H \cap \pi_{T,\mathfrak{C}}(\Gamma_{\mathfrak{O},T}) = 1,
\qquad
H \cdot \pi_{T,\mathfrak{C}}(\Gamma_{\mathfrak{O},T}) = G_{\mathfrak{O},T}[\mathfrak{C}].
$$

Such a complementary ideal is *uninverted* when $\mathfrak{C}$ is coprime to $T$, and *inverted* otherwise.
A complementary triple $(T,\mathfrak{C},H)$ is *minimal* if, for every proper divisor $\mathfrak{a} \mid \mathfrak{C}$, the map $\pi_{T,\mathfrak{a}}$ is not injective on $\Gamma_T$ (see Mendel–Yu, Section 6.3).
Across all 49 orders $\mathfrak{O}$ and every admissible $T$, the code determines every minimal complementary triple.

> With $\mathfrak{O}$, $T$, and $\mathfrak{C}$ fixed, the code computes $\Gamma_T$, $G_T[\mathfrak{C}]$, and $\pi_{T,\mathfrak{C}}$, then determines all complementary triples $(T,\mathfrak{C},H)$.

For $Z \subseteq G_{\mathfrak{O}}[\mathfrak{a}]$, define

$$
\Theta_{\mathfrak{a}}(Z) = \left\lbrace\mathrm{Nrd}_{\mathfrak{a}}(g) : g \in Z,\ \mathrm{trd}_{\mathfrak{a}}(g) = 0\right\rbrace \subseteq \Delta_{\mathfrak{a}},
$$

where $\Delta_{\mathfrak{a}}$ is the group of square classes of $(\mathcal{O}_K/\mathfrak{a})^\times$, and $\Theta_{\mathfrak a}$ abbreviates $\Theta_{\mathfrak{a}}(G_{\mathfrak{O}}[\mathfrak{a}])$. Set

$$
\mathfrak{e}(\mathfrak{a}) = \prod_{\mathfrak{p} \mid \mathfrak{a}} \mathfrak{p}^{\max\lbrace 2v_{\mathfrak{p}}(2)+1,\quad v_{\mathfrak{p}}(\mathfrak{a})\rbrace}.
$$

(see Mendel–Yu, Section 7.1)

> For each algebra, the code determines whether $1 \in \Theta_{\mathfrak{e}(\mathfrak{D}(B))}$. For each uninverted complement class at modulus $\mathfrak{C}$, it determines whether $1 \in \Theta_{\mathfrak{e}(\mathfrak{C})}(\widetilde H)$, where $\widetilde H = \pi_{\mathfrak{e}(\mathfrak{C}),\mathfrak{C}}^{-1}(H)$ under the natural map $G_{\mathfrak{O}}[\mathfrak{e}(\mathfrak{C})] \to G_{\mathfrak{O}}[\mathfrak{C}]$.

> For a finite set $S$ of primes, write $S_r = S \cap \mathrm{Ram}_f(B)$ and $S_0 = S \setminus S_r$ for its ramified and split parts. For a complementary triple $(T,\mathfrak{C},H)$ and eligible $S$, the code builds finite presentations of
>
> $$
> \Gamma_{\mathfrak{O},S}(\mathfrak{C},H) = \pi_{\mathfrak{O},S_r,\mathfrak{C}}^{-1}(H).
> $$

(see Mendel–Yu, Sections 5.1–5.2)

Specifically, for each split prime $\mathfrak{p} \in S$, the code assembles a set $A_{\mathfrak{p}}$ containing one generator for each of the $N(\mathfrak{p}) + 1$ maximal right ideals of $\mathfrak{O}$ of norm $\mathfrak{p}$, translating each generator by units of $\mathfrak{O}[1/T]$ until its reduction modulo $\mathfrak{C}$ lies in $H$. For each $a \in A_{\mathfrak{p}}$, there exists $\bar a \in A_{\mathfrak{p}}$ for which $a\bar a$ is central, and metacommutation assigns to each pair $a \in A_{\mathfrak{p}}$, $b \in A_{\mathfrak{q}}$ the unique $b' \in A_{\mathfrak{q}}$ and $a' \in A_{\mathfrak{p}}$ with $ab = b'a'$ up to the center. The group $\Gamma_{\mathfrak{O},S}(\mathfrak{C},H)$ has the presentation

$$
\left\langle \bigsqcup_{\mathfrak{p} \in S} A_{\mathfrak{p}} \;\middle|\; a\bar a = 1,\ ab = b'a' \right\rangle,
$$

where the second family ranges over the metacommutation pairs and one relation is retained for each geometric square. The construction follows Mendel–Yu, Section 3.2, with the relations coming from metacommutation in the style of Chari [3] and of Rungtanapirom, Stix, and Vdovina [4]. The two presentations displayed in Mendel–Yu are re-derived by `verify.m`.

## Notation and terminology

The code and data name some objects that Mendel–Yu leave symbolic or
unnamed:

- A *localized group* is $\Gamma_{\mathfrak{O},T}$, written $\Gamma_T$ when the order is clear; the normalizers are $N_{\mathfrak{O},T}$ (Section 3.1). The case $T = \emptyset$ gives $\Gamma_{\mathfrak{O},\emptyset} = \mathfrak{O}^\times/\mathcal{O}_K^\times$.
- A *modulus* is an integral ideal $\mathfrak{C}$ used to define a reduction target. It is a complementary ideal when the associated reduction is injective and has a complement.
- The *minimal injective ideals* of `minimal_ideals.csv` are the ideals
  minimal under divisibility with injective reduction, whether or not a
  complement exists at them; they therefore include slightly more than the
  minimal complementary ideals classified in Section 6.3.
- A *complement class* is a conjugacy class of complements $H$ in $G_{\mathfrak{O},T}[\mathfrak{C}]$, reported through one representative subgroup.
- The *stabilized modulus* computed by `StabilizedModulus` is the ideal $\mathfrak{e}(\mathfrak{a})$ displayed above.
- The *discriminant obstruction* of `algebras.csv` records whether $1 \in \Theta_{\mathfrak{e}(\mathfrak{D}(B))}$ for the discriminant $\mathfrak{D}(B)$ of $B$; the `theta` columns of `complements.csv` record $\Theta_{\mathfrak{e}(\mathfrak{C})}(\widetilde H)$ for the preimage $\widetilde H$ of a complement under $G_{\mathfrak{O}}[\mathfrak{e}(\mathfrak{C})] \to G_{\mathfrak{O}}[\mathfrak{C}]$ (Section 7.1).

## Repository layout

| Path | Role |
| --- | --- |
| `load.m` | Loads the arithmetic table and then the five modules below. |
| `src/orders.m` | Builds order records from the arithmetic table, and provides the canonical ideal serialization and the relevant primes. |
| `src/quotients.m` | Computes the finite quotients $G_{\mathfrak{O}}[\mathfrak{p}^k] = (\mathfrak{O}/\mathfrak{p}^k\mathfrak{O})^\times/(\mathcal{O}_K/\mathfrak{p}^k)^\times$ and their normalizer images. |
| `src/classification.m` | Builds the groups $\Gamma_{\mathfrak{O},T}$, computes $\pi_{\mathfrak{O},T,\mathfrak{C}}$, and classifies the minimal injective ideals and their complement classes. |
| `src/obstructions.m` | Computes the moduli $\mathfrak{e}(\mathfrak{a})$ and the torsion obstruction sets $\Theta_{\mathfrak{a}}(Z)$. |
| `src/presentations.m` | Builds the presentations of the simply transitive groups $\Gamma_{\mathfrak{O},S}(\mathfrak{C},H)$. |
| `reproduce.m` | Recomputes the four CSV files from scratch. |
| `verify.m` | Checks the CSV files and re-derives the displayed computations of Mendel–Yu. |
| `data/*.csv` | These files hold the computed classification (see "The data" below). |

### Common commands

Run `load "load.m";` before using these commands.

| Command | What it does |
| --- | --- |
| `ClassOneOrderIndices()` | Returns the 49 row indices in Kirschmer's `OneClassGenera` table that describe maximal orders of class number one. Use an entry of this list as the argument of `ClassOneOrder`, or loop over the list to process every order in the classification. |
| `ClassOneOrder(index)` | Builds the `order_data` record for one class-number-one maximal order. This record contains its number field, quaternion algebra, order, unit group, normalizer data, and arithmetic information. Pass it to the other commands below. |
| `ClassifyOrder(order_data)` | For every subset $T$ of the finite ramified primes at which $\mathfrak{O}$ is locally maximal (an *admissible* $T$), constructs $\Gamma_T$ by adjoining the corresponding ramified normalizer generators to $\Gamma_{\emptyset}$. For each $T$, it computes every conjugacy class of complements $H$ at each minimal ideal $\mathfrak{C}$. Its three fields are parallel lists indexed by these $T$: `localized_groups[i]` records $T$, $\Gamma_T$, and its chosen generators; `exclusion_reasons[i]` is empty unless the paper's nontriviality definition excludes that $T$, in which case it gives the reason; and `poset_results[i]` is `false` when excluded and otherwise records the nontrivial minimal ideals and their matching reduction results, including all complement classes. |
| `ReductionData(order_data, T, modulus_ideal)` | Studies one chosen pair $(T,\mathfrak{C})$. The result states whether $\pi_{T,\mathfrak{C}}$ is injective and gives its image in the finite target together with every complement class, including the normal ones. Use `T := []` for the unlocalized case. |
| `PresentationForComplement(result, s_prime_inputs)` | Takes an injective result returned by `ReductionData` and builds a presentation for the group associated to a selected complement class. `s_prime_inputs` is a list of distinct split primes that are coprime to the modulus. The result includes the presented group, generators, and square relations. |
| `FiniteQuotient(order_data, prime_ideal, exponent)` | Computes the one-prime-power quotient $G_{\mathfrak{O}}[\mathfrak{p}^k]$, together with the normalizer information needed at ramified primes. Use it to inspect a local factor before assembling a composite modulus. |

Every public computation either returns its result or raises a Magma error; nothing fails silently. The interactive example below creates an `order_data` record and illustrates the first steps.

## Requirements

The code is tested with Magma V2.29-5.

The sole external input is Markus Kirschmer's small-type-number table [2],
from which the code selects the 49 class number one maximal orders.  The table is
not included in this repository (it is Kirschmer's work and is not covered by
this repository's license).  Download and extract it from this directory:

```
curl -fsSL https://www.math.uni-bielefeld.de/~mkirschm/orders/smalltypenumber.tar.bz2 | tar -xjf - -C data
```

The resulting file must be `data/smalltypenumber.m`, with SHA-256 checksum

```
2f044b3345c129523b19d7f2bca21bad06f48675132d8cbe984af220fb02b27b
```

(check with `shasum -a 256 data/smalltypenumber.m`).

`reproduce.m` additionally requires a POSIX system (macOS or Linux): it runs
each order in a separate Magma process via standard shell utilities.
`verify.m` and interactive use are portable.

## The data

The four CSV files in `data/` record, per class number one maximal order:

| File | One row per | Columns |
| --- | --- | --- |
| `algebras.csv` | algebra | `order_index`, `base_field_degree`, `base_field_discriminant`, `algebra_discriminant`, `ramified_primes`, `gamma_emptyset_order`, `discriminant_theta_applicable`, `discriminant_modulus_factorization`, `discriminant_theta_size`, `discriminant_theta_contains_one` |
| `localized_groups.csv` | pair $(\mathfrak{O}, T)$ | `order_index`, `ramified_subset`, `gamma_order`, `gamma_type`, `exclusion_reason` |
| `minimal_ideals.csv` | minimal injective ideal | `order_index`, `ramified_subset`, `modulus_norm`, `modulus_factorization`, `has_complement` |
| `complements.csv` | complement class | `order_index`, `ramified_subset`, `modulus_norm`, `modulus_factorization`, `complement_index`, `complement_order`, `complement_is_normal`, `theta_applicable`, `theta_modulus_factorization`, `theta_size`, `theta_contains_one` |

`order_index` is the row index in Kirschmer's table, so the datasets can be
joined and traced back to the arithmetic input.  A nonempty
`exclusion_reason` marks a pair $(\mathfrak{O}, T)$ excluded by Mendel–Yu's
definition of a nontrivial triple (Section 6.3).  `gamma_type` is Magma's small-group
identifier `<order, id>`; complement classes carry only their order, because
groups of some occurring orders (512 among them) are beyond Magma's
identification database.  `theta_applicable` is false exactly when a prime of
$T$ divides $\mathfrak{C}$, in which case the obstruction is undefined and the remaining
`theta` columns are empty.

Serialization is canonical so that repeated runs produce byte-identical
files: a prime ideal is written as its norm followed by a Hermite-normal-form
basis matrix, sets and factorizations are sorted by that key, complement
classes are sorted by their full exported row (classes with equal rows are
genuinely indistinguishable in the recorded data and differ only in
`complement_index`), and complete rows are sorted before publication.

## Reproducing the data

From this directory:

```
magma reproduce.m
```

This recreates the four CSV files by computing all 49 orders. Results are first written to a temporary staging area. The CSV files in `data/` are replaced only after every calculation and final consistency check succeeds, so a failed run leaves the existing datasets intact. If the `magma` executable is not on `PATH`, set `MAGMA_CMD`:

```
MAGMA_CMD=/Applications/Magma/magma /Applications/Magma/magma reproduce.m
```

The computation is deterministic (a fixed seed pins Magma's randomized
algorithms), so a rerun under the same Magma version reproduces the shipped
files byte for byte.

## Verifying the paper's computations

```
magma verify.m
```

`verify.m` is a targeted audit of the computations used in Mendel–Yu. It does not rerun the complete 49-order classification; use `reproduce.m` when a fresh classification is required. The left column gives the corresponding numbering in the paper.

| Mendel–Yu location | Computation in `verify.m` |
| --- | --- |
| Lemma 32 | Rebuilds each of the 49 orders and checks that every representative of $\Gamma_{\emptyset}$ is a unit of reduced norm $1$. |
| Proofs of Lemma 33(ii), Lemma 34, and Theorem 35 | For a nonidentity element of $\Gamma_T$, reduction at a split prime can fail to be injective only if that element becomes scalar. The $2\times2$ minors of its order-basis coordinates with the identity give a finite list of all such possible primes. The code reduces at every prime on this list in the cases used by the proofs: $\Gamma_{\emptyset}\cong C_2$, cyclic singleton $T$, and $N(\mathfrak{p}) > \lvert\Gamma_T\rvert$. |
| Proof of Lemma 33(iii) | Identifies the unique exceptional order over $\mathbb{Q}(\sqrt{2})$, with ramified-prime norms $2$ and $25$, and computes the two directed singleton $T$ cases: the stated normal complement exists in one direction and no complement exists in the reverse direction. |
| Theorem 35 | For each recorded minimal complementary ideal, checks that every prime factor is ramified or has norm at most $\lvert\Gamma_T\rvert$. In the equality case, it checks that the modulus is one prime to the first power and that $\Gamma_T$ is cyclic of order $2$, $3$, or $5$, as stated in the theorem. |
| Theorem 38 | Counts the recorded nontrivial minimal complementary triples for each order and checks that the count is positive whenever $\Gamma_{\emptyset}\ne 1$ or the algebra has more than one finite ramified prime. |
| Example 37 | Locates the real cubic field of discriminant $49$ with ramified-prime norm $7$, checks $\Gamma_{\emptyset}\cong D_7$ and $\Gamma_T\cong D_{14}$ for $T$ equal to that prime, and checks that its unique minimal triple has modulus of norm $27$. |
| Proposition 42 | Checks that exactly one recorded complementary modulus is composite. It then identifies it as the real-cyclotomic field of discriminant $81$, ramified at the norm $3$ prime, with $T$ that prime and modulus norm $24$. |
| Definition following Lemma 47 | Evaluates $\mathfrak{e}(\mathfrak{a})$ at rational and $\mathbb{Q}(\sqrt{2})$ test ideals, including a ramified dyadic prime, to check the exponent $\max\lbrace 2v_{\mathfrak{p}}(2)+1, v_{\mathfrak{p}}(\mathfrak{a})\rbrace$. |
| Proof of Theorem 50 | Checks that the tabulated nontrivial rational triples with $T=\emptyset$ have at least one of the two recorded obstruction sets excluding $1$, and separately checks the discriminant $13$ trivial family. |
| Example 19 | Recomputes the complementary triple and presentation for discriminant $5$ at $S=\lbrace 2,3\rbrace$, then matches the displayed generators, inverse relations, six square relations, and abelianization. |
| Example 20 and Example 49 | Recomputes the two norm $7$ generator sets, the sixteen displayed square relations, the abelianization, and the edge/face torsion checks. It also computes the norm $9$ obstruction set and identifies its nonsquare class with $1+\sqrt{2}$. |
| Section 7.2, “The Hurwitz order” | Recomputes the Hurwitz reductions modulo $2$ and $4$, their complements and obstruction sets, and the comparison with the Lipschitz order: the four displayed complements, the trace-zero distinction, the reduction kernel, and the stated lifting relation. |

Several of the classification-wide checks above use the four CSV files. Before using them, `verify.m` checks their columns and canonical representations, then follows the links between them: each localized-group row names an algebra, each minimal-ideal row names a nonexcluded localized group, and each complement row names a minimal ideal declared to have a complement. It also checks that there are 49 algebra rows and that each order has one localized group for every subset of its ramified primes. This detects changes to the shipped data that would invalidate those checks.

Use `verify.m` to audit the finite claims above. Use `reproduce.m` to regenerate the complete classification. A failed assertion stops the run, while a silent finish means that every listed check passed. Mendel–Yu contains the structural proofs.

## Interactive use

Start Magma from this directory so the relative paths resolve:

```
magma
load "load.m";
```

For example:

```magma
indices := ClassOneOrderIndices();
order_data := ClassOneOrder(indices[1]);
P := RelevantSplitPrimes(order_data, 3)[1];

quotient := FiniteQuotient(order_data, P, 1);
localized_groups := LocalizedGroups(order_data);
minimal_ideals := MinimalInjectiveIdeals(order_data, []);
classification := ClassifyOrder(order_data);
```

The algebra $B = \left(\frac{-2, -5}{\mathbb{Q}}\right)$ of Mendel–Yu's
introduction has discriminant $5$ and is entry $5$ of the Kirschmer table.  The
following recovers its complementary triple at $T = \emptyset$ and
$\mathfrak{C} = (5)$, whose unique complement class $H$ is normal of order $50$ with
$1 \notin \Theta_{\mathfrak{e}(\mathfrak{C})}(\widetilde H)$, and then builds the
presentation of $\Gamma_{\mathfrak{O},S}(\mathfrak{C},H)$ at $S = \lbrace 2, 3\rbrace$:

```magma
order_data := ClassOneOrder(5);
R := order_data`integer_ring;

result := ReductionData(order_data, [], 5*R : Print := 0);
assert result`injective and #result`complement_classes eq 1;

presentation := PresentationForComplement(result, [2*R, 3*R] : Print := 0);
```

## References

1. Markus Kirschmer and John Voight, *Algorithmic enumeration of ideal
   classes for quaternion orders*, SIAM Journal on Computing 39 (2010),
   no. 5, 1714–1747.
2. Markus Kirschmer, *Quaternion orders of type number one and two*,
   <https://www.math.uni-bielefeld.de/~mkirschm/orders/>.
3. Sara Chari, *Metacommutation of primes in central simple algebras*,
   Journal of Number Theory 206 (2020), 296–309.
4. Nithi Rungtanapirom, Jakob Stix, and Alina Vdovina, *Infinite series of
   quaternionic 1-vertex cube complexes, the doubling construction, and
   explicit cubical Ramanujan complexes*, International Journal of Algebra
   and Computation 29 (2019), no. 6, 951–1007.

## License

The code and the data files in `data/*.csv` are released under the
[MIT License](LICENSE).  `data/smalltypenumber.m` is Markus Kirschmer's work,
obtained separately as described above, and is not covered by that license.
