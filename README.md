# Wagner's planarity criterion and list colouring of planar graphs in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository formalizes, for finite simple graphs in Lean 4 with Mathlib:

1. **Wagner's theorem (1937).** A finite graph is planar if and only if it has neither `K₅` nor
   `K₃,₃` as a minor.
2. **Škrekovski (1998).** Every finite graph without a `K₅` minor is 5-choosable (following
   Wood–Linusson), and hence **Thomassen (1994)**: every finite planar graph is 5-choosable.
3. **DP-colouring.** Every finite graph without a `K₅` minor (Li–Wang, 2022), and hence every
   finite planar graph (Dvořák–Postle, 2018), is DP-5-colourable.
4. **Voigt (1993).** An explicit planar graph on 238 vertices with lists of four colours has no
   proper list colouring, so planar graphs need not be 4-choosable.
5. **Wagner (1937).** The Four Colour Theorem is equivalent to Hadwiger's conjecture for `K₅`
   (neither side is proved).

The audited statements are in [`Challenge.lean`](Challenge.lean), which imports only Mathlib and
contains the definitions of planarity, minors, list colouring and DP-colouring; the proofs are in
[`Solution.lean`](Solution.lean). [`comparator.json`](comparator.json) lists the compared
theorems, [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md) reproduces verbatim the Mathlib
definitions used by the statements, and [`formalization.yaml`](formalization.yaml) records
provenance, sources and process.

## Definitions

* **Planarity.** `G` is planar if it has a *plane map*: a rotation system (a cyclic order of the
  darts at every vertex) whose hypermap has Euler defect
  `|D| + 2K - c(rot) - c(dartSymm) - c(rot ∘ dartSymm) = 0`, i.e. every component has genus `0`.
  This is the classical combinatorial description of sphere embeddings (Heffter–Edmonds–Ringel);
  the equivalence with topological embeddings is not formalized. Sanity checks: `K₄` is planar,
  `K₅` and `K₃,₃` are not.
* **Minors.** `H` is a minor of `G` if `G` has disjoint, nonempty, connected branch sets, one for
  each vertex of `H`, with an edge between the branch sets of adjacent vertices of `H`.
* **Choosability.** `G` is `k`-choosable (over a colour type `C`) if every assignment of lists of
  at least `k` colours admits a proper colouring from the lists.
* **DP-colouring.** Each pair of vertices carries a correspondence (a symmetric partial matching
  between colours); a DP-colouring chooses from every list so that no edge joins matched colours.

## Contents of the library

`LeanPool/K5MinorFreeChoosability/` contains the 69 modules of the author's planarity and
colouring library needed by these statements: plane maps and Euler's formula (`Planar/`),
minor models and minor-closedness, the Wood–Linusson extension lemma and its DP version
(`Extension.lean` and the case analysis in `Boundary`, `Cases`, `Lemma5`, `Split`, …), the
decompositions behind Wagner's theorem (`Wagner/`), and Voigt's graph with its rotation system and
lists (`Voigt/`, checked by kernel reduction without `native_decide`). Research modules of the same
library that are not needed here are not included.

## Scope and limitations

* Planarity is combinatorial (see above).
* Statements are for finite vertex types in any universe; Voigt's example is a graph on `Fin 238`
  with colours in `ℕ`.
* No `sorry`, no custom axioms; the compared theorems depend only on `propext`,
  `Classical.choice` and `Quot.sound`. One library file raises `maxHeartbeats` for two
  declarations.

## Sources

* K. Wagner, *Über eine Eigenschaft der ebenen Komplexe*, Math. Ann. 114 (1937) 570–590.
* R. Škrekovski, *Choosability of K5-minor-free graphs*, Discrete Math. 190 (1998) 223–226.
* D. R. Wood, S. Linusson, *Thomassen's choosability argument revisited*, SIAM J. Discrete Math.
  24 (2010) 1632–1637, arXiv:1005.5194.
* C. Thomassen, *Every planar graph is 5-choosable*, J. Combin. Theory Ser. B 62 (1994) 180–181.
* Z. Dvořák, L. Postle, *Correspondence coloring and its application to list-coloring planar
  graphs without cycles of lengths 4 to 8*, J. Combin. Theory Ser. B 129 (2018) 38–54.
* L. Li, T. Wang, *An extension of Thomassen's result on choosability*, Appl. Math. Comput. 425
  (2022) 127100, arXiv:2111.15220.
* M. Voigt, *List colourings of planar graphs*, Discrete Math. 120 (1993) 215–219.
* K. Kuratowski, *Sur le problème des courbes gauches en topologie*, Fund. Math. 15 (1930)
  271–283 (background).

## Authorship and use of AI

The results, proof routes and statements were chosen by the author. Most Lean proofs of the
library were produced by Harmonic's Aristotle over several rounds and audited; integration,
review and packaging were done with an AI agent (Claude Opus 5.5 in Claude Code). Every result is
checked mechanically with Lean. See `formalization.yaml` for details.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
