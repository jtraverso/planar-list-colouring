/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.MaximalCoreAttack

/-!
# Small vertex covers in the maximal Wagner core

A complete minor has at most one branch avoiding a vertex cover, and disjoint
branches meeting the cover can be injected into it. A cover of size at most
three therefore excludes a `K₅` minor, even in an infinite ambient type.
Edge maximality makes such a cover a clique. A core with at least five
supported vertices then has a proper clique separator, a contradiction.

These statements do not assert that a general Wagner core has a small cover.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex cover of size `c` rules out every complete minor of order
strictly greater than `c + 1`. No finite ambient type is required. -/
theorem cliqueMinorFree_of_vertex_cover (C : Finset V) {k : ℕ}
    (hcover : ∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C)
    (hcard : C.card + 1 < k) : CliqueMinorFree G k := by
  classical
  rintro ⟨M⟩
  let I : Finset (Fin k) := Finset.univ.filter (fun i => ∃ x ∈ M.branch i, x ∈ C)
  have hpick : ∀ i : I, ∃ x : C, (x : V) ∈ M.branch i := by
    intro i
    obtain ⟨x, hx, hxC⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨x, hxC⟩, hx⟩
  choose pick hpick using hpick
  have hinj : Function.Injective pick := by
    intro i j heq
    by_contra hij
    have hij' : (i : Fin k) ≠ (j : Fin k) := fun h => hij (Subtype.ext h)
    have hx : (pick i : V) = (pick j : V) := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp (M.branch_disjoint i j hij') (hpick i) (hx ▸ hpick j)
  have hI : I.card ≤ C.card := by
    have hle := Fintype.card_le_of_injective pick hinj
    simpa using hle
  have hJ : (Finset.univ \ I).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    obtain ⟨a, ha, b, hb, hab⟩ := M.branch_adjacent i j hij
    rcases hcover a b hab with haC | hbC
    · exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, a, ha, haC⟩)
    · exact (Finset.mem_sdiff.mp hj).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, b, hb, hbC⟩)
  have he := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset
    (fun i => ∃ x ∈ M.branch i, x ∈ C) Finset.univ)
  change (Finset.univ \ I).card + I.card = (Finset.univ : Finset (Fin k)).card at he
  have htotal : (Finset.univ : Finset (Fin k)).card = k := Finset.card_fin k
  omega

theorem k5MinorFree_of_vertex_cover_three (C : Finset V)
    (hcover : ∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C)
    (hcard : C.card ≤ 3) : K5MinorFree G :=
  cliqueMinorFree_of_vertex_cover C hcover (by omega)

/-- Adding an edge within the cover preserves the same minor bound, so
maximality forces all pairs of its vertices to be adjacent. -/
theorem vertex_cover_clique_of_maximal {S C : Finset V}
    (hM : IsMaxK5Free G S) (hCS : C ⊆ S) (hcard : C.card ≤ 3)
    (hcover : ∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C) :
    ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v := by
  classical
  intro u hu v hv huv
  by_contra hnot
  apply hM.2.2 u (hCS hu) v (hCS hv) huv hnot
  apply k5MinorFree_of_vertex_cover_three C ?_ hcard
  intro a b hab
  rcases (addEdgeGraph_adj huv a b).mp hab with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hcover a b h
  · exact Or.inl hu
  · exact Or.inl hv

variable [DecidableEq V]

/-- A maximal clique-separator-free core with at least five supported
vertices has no vertex cover of size at most three. -/
theorem no_vertex_cover_three_of_maximal_core {S C : Finset V}
    (hM : IsMaxK5Free G S) (hsep : NoCliqueSepThree G S)
    (hS : 5 ≤ S.card) (hCS : C ⊆ S) (hcard : C.card ≤ 3)
    (hcover : ∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C) : False := by
  classical
  have hclique := vertex_cover_clique_of_maximal hM hCS hcard hcover
  have hout : (S \ C).Nonempty := by
    apply Finset.card_pos.mp
    have he := Finset.card_sdiff_add_card_eq_card hCS
    omega
  obtain ⟨c, hc⟩ := hout
  obtain ⟨hcS, hcC⟩ := Finset.mem_sdiff.mp hc
  let A := insert c C
  let B := S.erase c
  have hAS : A ⊆ S := Finset.insert_subset_iff.mpr ⟨hcS, hCS⟩
  have hcov : A ∪ B = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact hAS hxA
      · exact Finset.mem_of_mem_erase hxB
    · intro hxS
      by_cases hxc : x = c
      · subst x
        exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxc, hxS⟩)
  have hinter : A ∩ B = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_insert.mp hxA with hxc | hxC
      · exact ((Finset.mem_erase.mp hxB).1 hxc).elim
      · exact hxC
    · intro hxC
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hxC,
        Finset.mem_erase.mpr ⟨fun h => hcC (h ▸ hxC), hCS hxC⟩⟩
  have hcross : ∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → ¬ G.Adj x y := by
    intro x hxA hxB y _ hyA hxy
    have hxc : x = c := by
      rcases Finset.mem_insert.mp hxA with hxc | hxC
      · exact hxc
      · by_contra hxc
        exact hxB (Finset.mem_erase.mpr ⟨hxc, hCS hxC⟩)
    have hyC : y ∉ C := fun hyC => hyA (Finset.mem_insert_of_mem hyC)
    rcases hcover x y hxy with hxC | hyC'
    · exact hcC (hxc ▸ hxC)
    · exact hyC hyC'
  have hAB : ¬ A ⊆ B := by
    intro h
    exact (Finset.mem_erase.mp (h (Finset.mem_insert_self _ _))).1 rfl
  have hBA : ¬ B ⊆ A := by
    intro h
    have hSA : S ⊆ A := by
      rw [← hcov]
      exact Finset.union_subset (Finset.Subset.refl _) h
    have hle := Finset.card_le_card hSA
    have hAc : A.card = C.card + 1 := Finset.card_insert_of_notMem hcC
    omega
  exact hsep A B hcov (by simpa only [hinter] using hcard) hcross hAB hBA
    (fun u hu v hv huv => hclique u (hinter ▸ hu) v (hinter ▸ hv) huv)

end LeanPool.K5MinorFreeChoosability
