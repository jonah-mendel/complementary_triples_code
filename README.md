# Magma code for "S-arithmetic groups acting simply transitively on products of Bruhat–Tits trees"

This repository contains the Magma code and computed data supporting the paper

> Jonah Mendel and Jiahui Yu, *$S$-arithmetic groups acting simply transitively
> on products of Bruhat–Tits trees*.

Mendel–Yu classify the nontrivial minimal complementary triples of class
number one maximal orders in totally definite quaternion algebras and use them
to construct simply transitive lattices on products of Bruhat–Tits trees.  This
repository holds the computations behind that classification: the four CSV
files in `data/` are the complete computational output, and the tables of
Mendel–Yu's Appendix A are generated from them.  The CSV files ship with the
repository, so Magma is needed only to recompute or verify them, not to use
them.

## What is computed

Let $B$ be one of the 49 totally definite quaternion algebras over a number
field $K$ that admit a maximal order of class number one (as enumerated by
Kirschmer–Voight [1]), and let $\mathcal{O} \subseteq B$ be such an
order.  For a set $T$ of finite ramified primes of $B$, let

$$\Gamma_T \;=\; \mathcal{O}[1/T]^\times/\mathfrak o_K[1/T]^\times,$$

which is a finite group, and for an integral ideal $C$ of $\mathfrak o_K$,
let

$$G[C] \;=\; (\mathcal{O}/C\mathcal{O})^\times/(\mathfrak o_K/C)^\times.$$

When a prime $\mathfrak p$ ramifies in $B$, the completion $B_{\mathfrak p}$
is a division algebra; write $\mathcal{O}_{\mathfrak p}$ for its maximal
order and $\mathfrak P$ for the maximal ideal of $\mathcal{O}_{\mathfrak p}$,
so that $\mathfrak P^2 = \mathfrak p\mathcal{O}_{\mathfrak p}$.  Let

$$U^k_{\mathfrak p} \;=\; \mathcal{O}_{\mathfrak p}^\times/(\mathfrak o_{\mathfrak p}^\times \cdot (1+\mathfrak P^{2k})),
\qquad
W^k_{\mathfrak p} \;=\; B_{\mathfrak p}^\times/(K_{\mathfrak p}^\times \cdot (1+\mathfrak P^{2k})),$$

so that $U^k_{\mathfrak p}$ has index two in $W^k_{\mathfrak p}$
(Section 2.3.2 of Mendel–Yu).  The code recovers $U^k_{\mathfrak p}$ as
$G[\mathfrak p^k]$ and computes $W^k_{\mathfrak p}$ alongside, since the
reductions attached to inverted complementary ideals land in
$W^k_{\mathfrak p}$ (Section 5.3).

A complementary triple $(T, C, H)$ consists of $T$ and $C$ such that the
reduction $\Gamma_T \to G[C]$ is injective, together with a complement $H$
of the image: a subgroup meeting it trivially with
$\#H \cdot \#\Gamma_T = \#G[C]$.  For each of the 49 orders and each $T$,
the code finds all ideals $C$ that are minimal under divisibility with
injective reduction, and all conjugacy classes of complements $H$ at each
such $C$.  This is the classification described in Section 6 of Mendel–Yu.

The code then evaluates the torsion obstruction sets, following
Section 7.1: for $Z \subseteq G[\mathfrak a]$,

$$\Theta_{\mathfrak a}(Z) \;=\; \left\{\operatorname{Nrd}(g) : g \in Z,\ \operatorname{trd}(g) = 0\right\} \;\subseteq\; \Delta_{\mathfrak a},$$

where $\Delta_{\mathfrak a}$ is the group of square classes of
$(\mathfrak o_K/\mathfrak a)^\times$, and $\Theta_{\mathfrak a}$ abbreviates
$\Theta_{\mathfrak a}(G[\mathfrak a])$.  Torsion is ruled out when $1$ lies
outside the obstruction set, and it suffices to test this at the modulus

$$\mathfrak e(\mathfrak a) \;=\; \prod_{\mathfrak p \mid \mathfrak a} \mathfrak p^{\max\{2v_{\mathfrak p}(2)+1,\; v_{\mathfrak p}(\mathfrak a)\}}.$$

Two obstructions are recorded.  For each algebra, the code determines
whether $1 \in \Theta_{\mathfrak e(\mathfrak D(B))}$, where $\mathfrak D(B)$
is the discriminant of $B$.  For each complement class whose modulus $C$ is
coprime to $T$, it determines whether
$1 \in \Theta_{\mathfrak e(C)}(\widetilde H)$, where $\widetilde H$ is the
preimage of $H$ under $G[\mathfrak e(C)] \to G[C]$.

Finally, the code builds finite presentations of the groups
$\Gamma_{\mathcal{O},S}(C,H)$.  Given a triple $(T, C, H)$ and a set $S$ of
primes coprime to $C$ and unramified in $B$, the group
$\Gamma_{\mathcal{O},S}(C,H)$ is the preimage of $H$ under the reduction
$\Gamma_S \to G[C]$, where $\Gamma_S$ is defined by the same formula as
$\Gamma_T$; these are the groups acting simply transitively on products of
Bruhat–Tits trees (Section 5.1 of Mendel–Yu).  For each
$\mathfrak p \in S$, the code assembles a set $A[\mathfrak p]$ containing
one generator for each of the $N(\mathfrak p) + 1$ maximal right ideals of
$\mathcal{O}$ of norm $\mathfrak p$, translating each generator by units of
$\mathcal{O}[1/T]$ until its reduction modulo $C$ lies in $H$ — this is
where the complement enters.  Each $a \in A[\mathfrak p]$ has an inverse
partner $\bar a \in A[\mathfrak p]$ for which $a\bar a$ is central, and
metacommutation assigns to each pair $a \in A[\mathfrak p]$,
$b \in A[\mathfrak q]$ the unique $b' \in A[\mathfrak q]$ and
$a' \in A[\mathfrak p]$ with $ab = b'a'$ up to center.  The group
$\Gamma_{\mathcal{O},S}(C,H)$ is then presented on the generators
$\bigsqcup_{\mathfrak p \in S} A[\mathfrak p]$, subject to the relations
$a\bar a = 1$ and $ab = b'a'$, keeping one relation per geometric square.
The construction follows Section 3.2 of Mendel–Yu, with the relations
coming from metacommutation in the style of Chari [3] and of Rungtanapirom,
Stix, and Vdovina [4].  The two presentations displayed in Mendel–Yu are
re-derived by `verify.m`.

## Notation and terminology

The code and data name some objects that Mendel–Yu leave symbolic or
unnamed:

- A *localized group* is one of the groups $\Gamma_T$, written
  $\Gamma_{\mathcal{O},T}$ in Mendel–Yu when the order needs emphasis; the
  normalizers are $N_{\mathcal{O},T}$ (Section 3.1).  The case
  $T = \emptyset$ gives
  $\Gamma_\emptyset = \mathcal{O}^\times/\mathfrak o_K^\times$.
- A *modulus* is a complementary ideal $C$ (Section 5.2).
- The *minimal injective ideals* of `minimal_ideals.csv` are the ideals
  minimal under divisibility with injective reduction, whether or not a
  complement exists at them; they therefore include slightly more than the
  minimal complementary ideals classified in Section 6.3.
- A *complement class* is a conjugacy class of complements $H$ in $G[C]$,
  reported through one representative subgroup.
- The *stabilized modulus* computed by `StabilizedModulus` is the ideal
  $\mathfrak e(\mathfrak a)$ displayed above.
- The *discriminant obstruction* of `algebras.csv` records whether
  $1 \in \Theta_{\mathfrak e(\mathfrak D(B))}$ for the discriminant
  $\mathfrak D(B)$ of $B$; the `theta` columns of `complements.csv` record
  $\Theta_{\mathfrak e(C)}(\widetilde H)$ for the preimage $\widetilde H$ of
  a complement under $G[\mathfrak e(C)] \to G[C]$ (Section 7.1).
- *Class-one* abbreviates "class number one".

## Repository layout

| Path | Role |
| --- | --- |
| `load.m` | Loads the arithmetic table and then the five modules below. |
| `src/orders.m` | Builds order records from the arithmetic table, and provides the canonical ideal serialization and the relevant primes. |
| `src/quotients.m` | Computes the finite quotients $G = (\mathcal{O}/P^k\mathcal{O})^\times/(R/P^k)^\times$ and their normalizer images. |
| `src/classification.m` | Builds the groups $\Gamma_T$, reduces them modulo $C$, and classifies the minimal injective ideals and their complement classes. |
| `src/obstructions.m` | Computes the moduli $\mathfrak e(\mathfrak a)$ and the torsion obstruction sets $\Theta_{\mathfrak a}(Z)$. |
| `src/presentations.m` | Builds the presentations of the simply transitive groups $\Gamma_{\mathcal{O},S}(C,H)$. |
| `reproduce.m` | Recomputes the four CSV files from scratch. |
| `verify.m` | Checks the CSV files and re-derives the displayed computations of Mendel–Yu. |
| `data/*.csv` | These files hold the computed classification (see "The data" below). |

Suggested entry points for interactive use: `ClassOneOrderIndices`,
`ClassOneOrder`, `ExplicitOrder`, `RamifiedPrimes`, `RelevantSplitPrimes`
(orders); `FiniteQuotient` (quotients); `LocalizedGroups`, `LocalizedGroup`,
`MinimalInjectiveIdeals`, `ReductionData`, `ClassifyOrder` (classification);
`StabilizedModulus`, `TorsionObstruction`, `DiscriminantObstruction`
(obstructions); `PresentationForComplement`, `PresentationForModulus`
(presentations).  Every public computation either returns its result or raises
a Magma error; nothing fails silently.

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
| `localized_groups.csv` | pair $(\mathcal{O}, T)$ | `order_index`, `ramified_subset`, `gamma_order`, `gamma_type`, `exclusion_reason` |
| `minimal_ideals.csv` | minimal injective ideal | `order_index`, `ramified_subset`, `modulus_norm`, `modulus_factorization`, `has_complement` |
| `complements.csv` | complement class | `order_index`, `ramified_subset`, `modulus_norm`, `modulus_factorization`, `complement_index`, `complement_order`, `complement_is_normal`, `theta_applicable`, `theta_modulus_factorization`, `theta_size`, `theta_contains_one` |

`order_index` is the row index in Kirschmer's table, so the datasets can be
joined and traced back to the arithmetic input.  A nonempty
`exclusion_reason` marks a pair $(\mathcal{O}, T)$ excluded by Mendel–Yu's
definition of a nontrivial triple (Section 6.3).  `gamma_type` is Magma's small-group
identifier `<order, id>`; complement classes carry only their order, because
groups of some occurring orders (512 among them) are beyond Magma's
identification database.  `theta_applicable` is false exactly when a prime of
$T$ divides $C$, in which case the obstruction is undefined and the remaining
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

This recomputes all 49 orders, each in a fresh Magma worker process so that
finite-group data cannot accumulate across orders.  Workers write to a
private staging directory inside `data/`; the
four CSV files are replaced, atomically per file, only after every order and
the combined cross-checks succeed.  If the `magma` executable is not on
`PATH`, set `MAGMA_CMD`:

```
MAGMA_CMD=/Applications/Magma/magma /Applications/Magma/magma reproduce.m
```

The computation is deterministic (a fixed seed pins Magma's randomized
algorithms), so a rerun under the same Magma version reproduces the shipped
files byte for byte.

## Verifying the data

```
magma verify.m
```

This first re-checks the four CSV files against their schema and
serialization contract and re-derives their cross-file relations and
aggregate counts.  It then re-checks the displayed computations of
Mendel–Yu independently of the classification pipeline: the exponent rule defining
$\mathfrak e(\mathfrak a)$ (Section 7.1), the unit-norm and finite
injectivity lemmas behind the classification (Section 6), the exceptional
case of an order with two ramified primes and trivial $\Gamma_\emptyset$,
the two displayed presentations, the quadratic torsion example, and the
Hurwitz–Lipschitz calculations of Section 7.2.  The first failed
assertion aborts with an error; a silent finish means every check passed.

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

The algebra $B = \left(\frac{-2,\,-5}{\mathbb{Q}}\right)$ of Mendel–Yu's
introduction has discriminant $5$ and is entry $5$ of the table.  The
following recovers its complementary triple at $T = \emptyset$ and
$C = (5)$, whose unique complement class $H$ is normal of order $50$ with
$1 \notin \Theta_{\mathfrak e(C)}(\widetilde H)$, and then builds the
presentation of $\Gamma_{\mathcal{O},S}(C,H)$ at $S = \{2, 3\}$:

```magma
order_data := ClassOneOrder(5);
R := order_data`integer_ring;

result := ReductionData(order_data, [], 5*R : Print := 0);
assert result`injective and #result`complement_classes eq 1;

presentation := PresentationForComplement(result, [2*R, 3*R] : Print := 0);
```

## Scope

The code takes the Kirschmer–Voight class number one enumeration as input
rather than reproving it, and it establishes the finite computations,
hypotheses, and examples that Mendel–Yu rely on — not their structural
theorems, whose proofs are in the paper itself.

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
