/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Basic

/-!
# Voigt's 238-vertex planar graph and its list assignment

This file defines, explicitly, the graph `voigtGraph : SimpleGraph (Fin 238)` and the lists
`voigtList : Fin 238 → Finset ℕ` of Voigt's construction (M. Voigt, *List colourings of planar
graphs*, Discrete Math. 120 (1993) 215–219).

## Vertices

* `0 … 9` are the vertices `A B C D E F L M N O` of the basic graph `G₁` (Fig. 1); `F L M N`
  are the four marked (`•`) vertices, the *hubs*.
* `10 + k` (`k < 12`) is the vertex `P` of the copy of the figure `Δ` (Fig. 2) inserted into
  the `k`-th marked triangle `U_k W_k V_k` of `G₁`, whose marked vertex is the hub `W_k`.
* `22 + 9 g + i` (`g < 24`, `i < 9`) is the `i`-th vertex of the *gadget* `g`, in the order
  `R₁ R₂ R₃ S₁ S₂ S₃ T₀ T₁ T₂`.  Gadget `2 k` is the copy of Fig. 3 inserted into the
  triangle `U_k W_k P_k`, gadget `2 k + 1` is the copy of Fig. 4 inserted into `P_k W_k V_k`.
  Voigt's `T₁ T₂ T₃` (resp. `T₄ T₅ T₆`) are our `T₀ T₁ T₂`.

Hence `10 + 12 · 19 = 238` vertices, as in the paper.

## Edges

* the 24 edges `coreEdges` of `G₁` among `A … O`;
* each `P_k` is joined to `U_k`, `W_k`, `V_k`;
* inside every gadget, the inner triangle `R₁ R₂ R₃`, the hexagon `R₁ S₁ R₂ S₂ R₃ S₃`, and
  `T₀ ∼ R₂, S₁`, `T₁ ∼ R₃, S₂`, `T₂ ∼ R₁, S₃` (`gadgetInnerEdges`);
* every gadget vertex is joined to the outer corners of its triangle `X Y Z`: `R₁ S₁` to `X`,
  `R₂ S₂` to `Y`, `R₃ S₃` to `Z`, `T₀` to `X Y`, `T₁` to `Y Z`, `T₂` to `X Z`.

There are `24 + 36 + 24 · 27 = 708` edges.

## Lists

Base vertices get `{1, 2, 3, 4}`.  A gadget whose corners `X Y Z` carry the *designated
colours* `x y z` (`2 1 4` for Fig. 3, `4 1 2` for Fig. 4) gives `R₁ S₁` the list
`{x, 3, 5, 6}`, `R₂ S₂` the list `{y, 3, 5, 6}`, `R₃ S₃` the list `{z, 3, 5, 6}`, and
`T₀ T₁ T₂` the lists `{x, y, 3, 5}`, `{y, z, 3, 5}`, `{z, x, 3, 5}` — exactly the lists of
Voigt's Figs. 3 and 4.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability.Voigt

/-! ### The basic graph `G₁` and the twelve marked triangles -/

/-- The 24 edges of Voigt's basic graph `G₁` among `A B C D E F L M N O = 0 … 9`. -/
def coreEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5),
   (1, 6), (1, 8), (1, 9), (2, 3), (2, 9), (3, 4), (3, 6), (3, 7), (3, 8), (3, 9),
   (4, 5), (4, 6), (4, 7), (8, 9)]

/-- First unmarked corner `U_k` of the `k`-th marked triangle. -/
def unitU (k : ℕ) : ℕ := [0, 4, 0, 1, 3, 1, 0, 3, 0, 1, 3, 1].getD k 0

/-- The marked corner (hub) `W_k ∈ {F, L, M, N}` of the `k`-th marked triangle. -/
def unitW (k : ℕ) : ℕ := [5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 8].getD k 0

/-- Second unmarked corner `V_k` of the `k`-th marked triangle. -/
def unitV (k : ℕ) : ℕ := [4, 1, 1, 3, 4, 4, 3, 4, 4, 3, 9, 9].getD k 0

/-- Adjacency among the 22 base vertices (`G₁` plus the twelve vertices `P_k`). -/
def baseAdj (u v : ℕ) : Bool :=
  coreEdges.any (fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)) ||
  (10 ≤ v && v < 22 && (u == unitU (v - 10) || u == unitW (v - 10) || u == unitV (v - 10))) ||
  (10 ≤ u && u < 22 && (v == unitU (u - 10) || v == unitW (u - 10) || v == unitV (u - 10)))

/-! ### Gadgets -/

/-- Corner `X` of gadget `g`. -/
def gadX (g : ℕ) : ℕ := if g % 2 = 0 then unitU (g / 2) else 10 + g / 2

/-- Corner `Y` of gadget `g` (always the hub). -/
def gadY (g : ℕ) : ℕ := unitW (g / 2)

/-- Corner `Z` of gadget `g`. -/
def gadZ (g : ℕ) : ℕ := if g % 2 = 0 then 10 + g / 2 else unitV (g / 2)

/-- Designated colour of corner `X` of gadget `g`. -/
def colX (g : ℕ) : ℕ := if g % 2 = 0 then 2 else 4

/-- Designated colour of corner `Y` of gadget `g`. -/
def colY (_g : ℕ) : ℕ := 1

/-- Designated colour of corner `Z` of gadget `g`. -/
def colZ (g : ℕ) : ℕ := if g % 2 = 0 then 4 else 2

/-- Edges inside a gadget, in local indices `R₁ R₂ R₃ S₁ S₂ S₃ T₀ T₁ T₂ = 0 … 8`. -/
def gadgetInnerEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 0), (3, 0), (3, 1), (4, 1), (4, 2), (5, 2), (5, 0),
   (6, 1), (6, 3), (7, 2), (7, 4), (8, 0), (8, 5)]

/-- Local vertices joined to corner `X`: `R₁ S₁ T₀ T₂`. -/
def attachX (i : ℕ) : Bool := i == 0 || i == 3 || i == 6 || i == 8

/-- Local vertices joined to corner `Y`: `R₂ S₂ T₀ T₁`. -/
def attachY (i : ℕ) : Bool := i == 1 || i == 4 || i == 6 || i == 7

/-- Local vertices joined to corner `Z`: `R₃ S₃ T₁ T₂`. -/
def attachZ (i : ℕ) : Bool := i == 2 || i == 5 || i == 7 || i == 8

/-- Adjacency between the base vertex `b` and the gadget vertex `22 + w`. -/
def outerAdj (b w : ℕ) : Bool :=
  (attachX (w % 9) && b == gadX (w / 9)) || (attachY (w % 9) && b == gadY (w / 9)) ||
  (attachZ (w % 9) && b == gadZ (w / 9))

/-- Adjacency inside one gadget, in local indices. -/
def innerAdj (i j : ℕ) : Bool :=
  gadgetInnerEdges.any (fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i))

/-- The adjacency relation of Voigt's graph, as a Boolean function on vertex numbers. -/
def voigtAdjB (u v : ℕ) : Bool :=
  if u < 22 then
    if v < 22 then baseAdj u v else outerAdj u (v - 22)
  else
    if v < 22 then outerAdj v (u - 22)
    else (u - 22) / 9 == (v - 22) / 9 && innerAdj ((u - 22) % 9) ((v - 22) % 9)

theorem voigtAdjB_symm : ∀ u v : Fin 238, voigtAdjB u v = voigtAdjB v u := by
  decide +kernel

theorem voigtAdjB_irrefl : ∀ u : Fin 238, voigtAdjB u u = false := by
  decide +kernel

/-- **Voigt's graph** on `238` vertices. -/
def voigtGraph : SimpleGraph (Fin 238) where
  Adj u v := voigtAdjB u v = true
  symm := ⟨fun u v h => by rwa [voigtAdjB_symm]⟩
  loopless := ⟨fun u h => by rw [voigtAdjB_irrefl] at h; exact Bool.false_ne_true h⟩

instance : DecidableRel voigtGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (voigtAdjB u v = true))

theorem voigtGraph_adj {u v : Fin 238} : voigtGraph.Adj u v ↔ voigtAdjB u v = true := Iff.rfl

/-! ### Lists -/

/-- The list of the gadget vertex with local index `i` in gadget `g`. -/
def gadgetList (g i : ℕ) : Finset ℕ :=
  if i = 0 ∨ i = 3 then {colX g, 3, 5, 6}
  else if i = 1 ∨ i = 4 then {colY g, 3, 5, 6}
  else if i = 2 ∨ i = 5 then {colZ g, 3, 5, 6}
  else if i = 6 then {colX g, colY g, 3, 5}
  else if i = 7 then {colY g, colZ g, 3, 5}
  else {colZ g, colX g, 3, 5}

/-- **Voigt's lists**: `{1, 2, 3, 4}` on the base vertices, Figs. 3/4 on the gadgets. -/
def voigtList (v : Fin 238) : Finset ℕ :=
  if (v : ℕ) < 22 then {1, 2, 3, 4} else gadgetList (((v : ℕ) - 22) / 9) (((v : ℕ) - 22) % 9)

/-- Every list has exactly four colours. -/
theorem voigtList_card : ∀ v, (voigtList v).card = 4 := by
  decide +kernel

end LeanPool.K5MinorFreeChoosability.Voigt
