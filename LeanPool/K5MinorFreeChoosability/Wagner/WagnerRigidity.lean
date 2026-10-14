/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.YDeltaModelAttack

/-!
# Rigidity of the Wagner graph

Adding any missing edge to `V₈` creates a `K₅` minor.  Consequently a `K₅`-minor-free graph
containing a spanning copy of `V₈` on an eight-element support is a `V₈`-piece
(`isWagnerPiece_of_spanning_wagner`).  This is the base case of the classical argument that a
three-connected `K₅`-minor-free graph with a `V₈` minor is `V₈` itself; the remaining steps of
Wagner's maximal-core classification are **not** proved here.

The `K₅` models are explicit: for the missing edge `0 — d` they are
* `d = 2`: `{0}, {2}, {1,5}, {3,4}, {6,7}`;
* `d = 3`: `{0}, {3}, {1,2}, {4,5}, {6,7}`;
* `d = 5`: `{0}, {5}, {1,2}, {3,4}, {6,7}`;
* `d = 6`: `{0}, {6}, {1,2}, {3,7}, {4,5}`;
and a general missing edge `i — j` is handled by rotating the model for `d = j - i`.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- Base `K₅` models for `V₈` plus the edge `0 — d` (`d ∈ {2,3,5,6}`); every branch is a
clique of `V₈`. -/
def wagnerPlusBase (d : Fin 8) : Fin 5 → Finset (Fin 8) :=
  if d = 2 then ![{0}, {2}, {1, 5}, {3, 4}, {6, 7}]
  else if d = 3 then ![{0}, {3}, {1, 2}, {4, 5}, {6, 7}]
  else if d = 5 then ![{0}, {5}, {1, 2}, {3, 4}, {6, 7}]
  else ![{0}, {6}, {1, 2}, {3, 7}, {4, 5}]

/-- Branch sets of a `K₅` model of `V₈` plus the edge `i — j`. -/
def wagnerPlusBranch (i j : Fin 8) (k : Fin 5) : Finset (Fin 8) :=
  (wagnerPlusBase (j - i) k).image (· + i)

/-- Adjacency in `V₈` plus the edge `i — j`, as a Boolean test. -/
def wagnerPlusAdj (i j a b : Fin 8) : Bool :=
  decide (wagnerGraph.Adj a b) || (a == i && b == j) || (a == j && b == i)

/-- Finite certificate: the branch sets of `wagnerPlusBranch i j` are nonempty. -/
theorem wagnerPlusBranch_nonempty :
    ∀ i j : Fin 8, ∀ k, (wagnerPlusBranch i j k).Nonempty := by
  decide

/-- Finite certificate: every branch set of `wagnerPlusBranch i j` is a clique of `V₈`. -/
theorem wagnerPlusBranch_clique : ∀ i j : Fin 8, ∀ k, ∀ a ∈ wagnerPlusBranch i j k,
    ∀ b ∈ wagnerPlusBranch i j k, a = b ∨ wagnerGraph.Adj a b := by
  decide

/-- Finite certificate: the branch sets of `wagnerPlusBranch i j` are pairwise disjoint. -/
theorem wagnerPlusBranch_disjoint : ∀ i j : Fin 8, ∀ k l, k ≠ l →
    Disjoint (wagnerPlusBranch i j k) (wagnerPlusBranch i j l) := by
  decide

/-- Finite certificate: for a missing edge `i — j` of `V₈`, any two branch sets of
`wagnerPlusBranch i j` are joined by an edge of `V₈` plus `i — j`. -/
theorem wagnerPlusBranch_adjacent : ∀ i j : Fin 8, i ≠ j → ¬ wagnerGraph.Adj i j →
    ∀ k l, k ≠ l → ∃ a ∈ wagnerPlusBranch i j k, ∃ b ∈ wagnerPlusBranch i j l,
      wagnerPlusAdj i j a b = true := by
  decide

/-- A nonempty set of pairwise adjacent vertices is connected. -/
theorem connSet_of_pairwise_adj {G : SimpleGraph V} {s : Set V} (hne : s.Nonempty)
    (h : ∀ a ∈ s, ∀ b ∈ s, a = b ∨ G.Adj a b) : ConnSet G s := by
  refine ⟨hne, fun a ha b hb => ?_⟩
  rcases h a ha b hb with rfl | hab
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hab, ha, hb⟩

/-- **Rigidity of `V₈`**: if a graph contains the image of `V₈` under an injection `f` and also
an edge between the images of two vertices nonadjacent in `V₈`, then it has a `K₅` minor. -/
theorem not_k5MinorFree_of_wagner_plus_edge {G : SimpleGraph V} (f : Fin 8 → V)
    (hf : Function.Injective f) (hW : ∀ a b, wagnerGraph.Adj a b → G.Adj (f a) (f b))
    {i j : Fin 8} (hij : i ≠ j) (hn : ¬ wagnerGraph.Adj i j) (hG : G.Adj (f i) (f j)) :
    ¬ K5MinorFree G := by
  classical
  have hne := wagnerPlusBranch_nonempty i j
  have hcl := wagnerPlusBranch_clique i j
  have hdis := wagnerPlusBranch_disjoint i j
  have hadj := wagnerPlusBranch_adjacent i j hij hn
  intro h5
  refine h5 ⟨{
    branch := fun k => (wagnerPlusBranch i j k).image f
    branch_nonempty := fun k => (hne k).image f
    branch_connected := fun k => ?_
    branch_disjoint := fun k l hkl => ?_
    branch_adjacent := fun k l hkl => ?_ }⟩
  · rw [← connSet_iff_induce_connected]
    refine connSet_of_pairwise_adj (by simpa using (hne k).image f) ?_
    intro x hx y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rcases hcl k a ha b hb with rfl | hab
    · exact Or.inl rfl
    · exact Or.inr (hW a b hab)
  · exact Finset.disjoint_image hf |>.2 (hdis k l hkl)
  · obtain ⟨a, ha, b, hb, hab⟩ := hadj k l hkl
    refine ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb, ?_⟩
    simp only [wagnerPlusAdj, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq] at hab
    rcases hab with (hab | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · exact hW a b hab
    · exact hG
    · exact hG.symm

/-- **A `K₅`-minor-free graph containing a spanning `V₈` is a `V₈`-piece**: if `f` maps `Fin 8`
injectively onto `S` and every edge of `V₈` to an edge of `G`, then every edge of `G` inside the
image is the image of an edge of `V₈`. -/
theorem isWagnerPiece_of_spanning_wagner {G : SimpleGraph V} {S : Finset V}
    (h5 : K5MinorFree G) (f : Fin 8 → V) (hf : Function.Injective f) (hfS : ∀ i, f i ∈ S)
    (hSf : ∀ v ∈ S, ∃ i, f i = v) (hW : ∀ a b, wagnerGraph.Adj a b → G.Adj (f a) (f b)) :
    IsWagnerPiece G S := by
  refine ⟨f, hf, hfS, hSf, fun i j hG => ?_⟩
  by_contra hn
  have hij : i ≠ j := by
    rintro rfl
    exact G.loopless.irrefl _ hG
  exact not_k5MinorFree_of_wagner_plus_edge f hf hW hij hn hG h5

/-- The Wagner graph has no triangle. -/
theorem wagnerGraph_no_triangle :
    ∀ a b c : Fin 8, wagnerGraph.Adj a b → wagnerGraph.Adj b c → ¬ wagnerGraph.Adj a c := by
  decide

end LeanPool.K5MinorFreeChoosability
