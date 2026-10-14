/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerV8Core

/-!
# Two corollaries of Wagner's structure theorem

* **Colouring transfer** (`colorable_of_k5MinorFree_of_planar`,
  `planar_colorable_iff_k5MinorFree_colorable`): for every `k ≥ 3`, all finite planar graphs
  are `k`-colourable iff all finite `K₅`-minor-free graphs are.  For `k = 4`
  (`fourColour_iff_hadwigerFive`) this is Wagner's equivalence between the Four Colour Theorem
  and Hadwiger's conjecture for `K₅`; neither side is assumed or proved here.
* **Planarity without small separations** (`isPlanar_of_k5MinorFree_of_noSep3`): a finite
  `K₅`-minor-free graph without a proper separation of order at most three is planar; i.e.
  every such nonplanar graph (in particular every 4-connected nonplanar graph) has a `K₅`
  minor.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

universe u

variable {V : Type*}

/-- A proper `k`-colouring of `H` on the vertex set `S`. -/
def ColorableOn (H : SimpleGraph V) (k : ℕ) (S : Finset V) : Prop :=
  ∃ c : V → Fin k, ∀ u ∈ S, ∀ v ∈ S, H.Adj u v → c u ≠ c v

/-- A proper `3`-colouring of the Wagner graph. -/
def wagnerColour : Fin 8 → Fin 3 := ![0, 1, 0, 1, 2, 0, 1, 2]

theorem wagnerColour_valid : ∀ i j, wagnerGraph.Adj i j → wagnerColour i ≠ wagnerColour j := by
  decide

/-- `V₈` pieces are `k`-colourable for `k ≥ 3`. -/
theorem colorableOn_of_isWagnerPiece {H : SimpleGraph V} {S : Finset V} {k : ℕ} (hk : 3 ≤ k)
    (hw : IsWagnerPiece H S) : ColorableOn H k S := by
  classical
  obtain ⟨f, hf, hfS, hSf, hadj⟩ := hw
  refine ⟨fun v => if h : ∃ i, f i = v then Fin.castLE hk (wagnerColour h.choose)
    else ⟨0, by omega⟩, fun u hu v hv huv => ?_⟩
  have hu' : ∃ i, f i = u := hSf u hu
  have hv' : ∃ i, f i = v := hSf v hv
  simp only [hu', hv', dite_true]
  intro h
  have h2 := Fin.castLE_injective hk h
  have k1 := hu'.choose_spec
  have k2 := hv'.choose_spec
  refine wagnerColour_valid _ _ (hadj _ _ ?_) h2
  rw [k1, k2]; exact huv

variable [DecidableEq V]

/-- Colourings glue along a clique separator (after permuting the colours of one side). -/
theorem ColorableOn.glue {H : SimpleGraph V} {k : ℕ} {A B : Finset V}
    (hcl : ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → H.Adj u v)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v)
    (hA : ColorableOn H k A) (hB : ColorableOn H k B) : ColorableOn H k (A ∪ B) := by
  classical
  obtain ⟨cA, hcA⟩ := hA
  obtain ⟨cB, hcB⟩ := hB
  set K := A ∩ B with hK
  have injA : ∀ x ∈ K, ∀ y ∈ K, cA x = cA y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    exact hcA x (Finset.mem_inter.1 hx).1 y (Finset.mem_inter.1 hy).1 (hcl x hx y hy hne) hxy
  have injB : ∀ x ∈ K, ∀ y ∈ K, cB x = cB y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    exact hcB x (Finset.mem_inter.1 hx).2 y (Finset.mem_inter.1 hy).2 (hcl x hx y hy hne) hxy
  set s : Set (Fin k) := cB '' ↑K
  have hpre : ∀ y : s, ∃ x, x ∈ K ∧ cB x = y.1 := fun y => by
    obtain ⟨x, hx, h⟩ := y.2
    exact ⟨x, hx, h⟩
  choose pre hpreK hpreB using hpre
  let f : s ↪ Fin k := ⟨fun y => cA (pre y), fun y z hyz => by
    have := injA _ (hpreK y) _ (hpreK z) hyz
    apply Subtype.ext
    rw [← hpreB y, ← hpreB z, this]⟩
  obtain ⟨g, hg⟩ := Cardinal.extend_function_finite f ⟨Equiv.refl _⟩
  have hgK : ∀ x ∈ K, g (cB x) = cA x := by
    intro x hx
    have := hg ⟨cB x, x, hx, rfl⟩
    rw [this]
    change cA (pre ⟨cB x, _⟩) = cA x
    rw [injB _ (hpreK _) _ hx (hpreB _)]
  refine ⟨fun v => if v ∈ A then cA v else g (cB v), fun u hu v hv huv => ?_⟩
  have side : ∀ {a b : V}, a ∈ A ∪ B → b ∈ A ∪ B → H.Adj a b → a ∈ A → b ∉ A →
      a ∈ K ∧ b ∈ B := by
    intro a b ha hb hab haA hbA
    have hbB : b ∈ B := (Finset.mem_union.1 hb).resolve_left hbA
    refine ⟨Finset.mem_inter.2 ⟨haA, ?_⟩, hbB⟩
    by_contra haB
    exact hnc a haA haB b hbB hbA hab
  by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A <;> simp only [huA, hvA, ite_true, ite_false]
  · exact hcA u huA v hvA huv
  · obtain ⟨huK, hvB⟩ := side hu hv huv huA hvA
    rw [← hgK u huK]
    exact fun h => hcB u (Finset.mem_inter.1 huK).2 v hvB huv (g.injective h)
  · obtain ⟨hvK, huB⟩ := side hv hu huv.symm hvA huA
    rw [← hgK v hvK]
    exact fun h => hcB u huB v (Finset.mem_inter.1 hvK).2 huv (g.injective h)
  · have huB := (Finset.mem_union.1 hu).resolve_left huA
    have hvB := (Finset.mem_union.1 hv).resolve_left hvA
    exact fun h => hcB u huB v hvB huv (g.injective h)

/-- Colourings propagate along a Wagner certificate. -/
theorem colorableOn_of_k5Decomp {H : SimpleGraph V} {k : ℕ} (hk : 3 ≤ k)
    (hpl : ∀ G' : SimpleGraph V, IsPlanar G' → G'.Colorable k) {S : Finset V}
    (hD : K5Decomp H S) : ColorableOn H k S := by
  induction hD with
  | planar h =>
    obtain ⟨c⟩ := hpl _ h
    exact ⟨c, fun u hu v hv huv => c.valid ⟨huv, hu, hv⟩⟩
  | wagner h => exact colorableOn_of_isWagnerPiece hk h
  | glue _ _ _ hcl hnc _ _ ihA ihB => exact ColorableOn.glue hcl hnc ihA ihB

omit [DecidableEq V] in
/-- **Colouring transfer.**  If every planar graph on the finite vertex type `V` is
`k`-colourable (`k ≥ 3`), then so is every `K₅`-minor-free graph on `V`. -/
theorem colorable_of_k5MinorFree_of_planar [Finite V] {k : ℕ} (hk : 3 ≤ k)
    (hpl : ∀ G' : SimpleGraph V, IsPlanar G' → G'.Colorable k) (G : SimpleGraph V)
    (hG : K5MinorFree G) : G.Colorable k := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨H, hGH, hD⟩ := exists_k5Decomp_wagner G hG
  obtain ⟨c, hc⟩ := colorableOn_of_k5Decomp hk hpl hD
  exact ⟨SimpleGraph.Coloring.mk c fun h =>
    hc _ (Finset.mem_univ _) _ (Finset.mem_univ _) (hGH h)⟩

omit [DecidableEq V] in
/-- **Wagner's colouring equivalence**, for every `k ≥ 3`: all finite planar graphs are
`k`-colourable iff all finite `K₅`-minor-free graphs are. -/
theorem planar_colorable_iff_k5MinorFree_colorable {k : ℕ} (hk : 3 ≤ k) :
    (∀ (W : Type u) [Finite W] (G : SimpleGraph W), IsPlanar G → G.Colorable k) ↔
      (∀ (W : Type u) [Finite W] (G : SimpleGraph W), K5MinorFree G → G.Colorable k) := by
  constructor
  · intro h W _ G hG
    exact colorable_of_k5MinorFree_of_planar hk (h W) G hG
  · intro h W _ G hG
    exact h W G (cliqueMinorFree_five_of_isPlanar hG)

omit [DecidableEq V] in
/-- **Wagner (1937)**: the Four Colour Theorem is equivalent to Hadwiger's conjecture for `K₅`
(every finite `K₅`-minor-free graph is 4-colourable).  Neither side is assumed. -/
theorem fourColour_iff_hadwigerFive :
    (∀ (W : Type u) [Finite W] (G : SimpleGraph W), IsPlanar G → G.Colorable 4) ↔
      (∀ (W : Type u) [Finite W] (G : SimpleGraph W), K5MinorFree G → G.Colorable 4) :=
  planar_colorable_iff_k5MinorFree_colorable (by norm_num)

/-! ### Planarity without small separations -/

/-- `G` has no proper separation of order at most three: whenever `A ∪ B = V`,
`|A ∩ B| ≤ 3` and no edge joins `A \ B` to `B \ A`, one side contains the other.  Every
4-connected graph has this property. -/
def NoSep3 [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ A B : Finset V, A ∪ B = Finset.univ → (A ∩ B).card ≤ 3 →
    (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ G.Adj u v) → A ⊆ B ∨ B ⊆ A

/-- **A `K₅`-minor-free graph without proper separations of order at most three is planar.** -/
theorem isPlanar_of_k5MinorFree_of_noSep3 [Fintype V] (G : SimpleGraph V) (hG : K5MinorFree G)
    (hsep : NoSep3 G) : IsPlanar G := by
  classical
  obtain ⟨H, hGH, hD⟩ := exists_k5Decomp_wagner G hG
  have key : ∀ S, K5Decomp H S → S = Finset.univ → IsPlanar G := by
    intro S hD hS
    cases hD with
    | planar h =>
      subst hS
      exact h.mono fun u v huv => ⟨hGH huv, Finset.mem_coe.2 (Finset.mem_univ _),
        Finset.mem_coe.2 (Finset.mem_univ _)⟩
    | wagner h =>
      subst hS
      exfalso
      obtain ⟨f, hf, -, hSf, hadj⟩ := h
      set v := f 0
      set N := Finset.univ.filter (G.Adj v)
      have hN : N.card ≤ 3 := by
        calc N.card ≤ ((wagnerGraph.neighborFinset 0).image f).card := by
              refine Finset.card_le_card fun u hu => ?_
              obtain ⟨j, rfl⟩ := hSf u (Finset.mem_univ _)
              exact Finset.mem_image_of_mem f ((wagnerGraph.mem_neighborFinset _ _).2
                (hadj 0 j (hGH (Finset.mem_filter.1 hu).2)))
          _ ≤ (wagnerGraph.neighborFinset 0).card := Finset.card_image_le
          _ = 3 := by rw [SimpleGraph.card_neighborFinset_eq_degree, wagnerGraph_degree]
      have hcard : Fintype.card V = 8 := by
        have := Fintype.card_of_bijective (f := f) ⟨hf, fun v => hSf v (Finset.mem_univ _)⟩
        simpa using this.symm
      have hvN : v ∉ N := by simp [N]
      rcases hsep (insert v N) (Finset.univ.erase v) (by ext x; by_cases h : x = v <;> simp [h])
        (by
          refine le_trans (Finset.card_le_card fun u hu => ?_) hN
          rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase] at hu
          rcases hu.1 with rfl | h
          · exact absurd rfl hu.2.1
          · exact h)
        (by
          intro a ha haB b hb hbA hab
          have hav : a = v := by simpa using haB
          subst hav
          exact hbA (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩)))
        with h | h
      · exact (Finset.mem_erase.1 (h (Finset.mem_insert_self v N))).1 rfl
      · have h1 := Finset.card_le_card h
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard,
          Finset.card_insert_of_notMem hvN] at h1
        omega
    | glue hAB hBA hc _ hnc _ _ =>
      exfalso
      rcases hsep _ _ hS hc (fun u hu huB v hv hvA h => hnc u hu huB v hv hvA (hGH h)) with h | h
      · exact hAB h
      · exact hBA h
  exact key _ hD rfl

/-- Contrapositive: **every nonplanar finite graph without proper separations of order at most
three (e.g. every 4-connected nonplanar graph) has a `K₅` minor.** -/
theorem not_k5MinorFree_of_not_isPlanar_of_noSep3 [Fintype V] (G : SimpleGraph V)
    (hP : ¬ IsPlanar G) (hsep : NoSep3 G) : ¬ K5MinorFree G :=
  fun hG => hP (isPlanar_of_k5MinorFree_of_noSep3 G hG hsep)

end LeanPool.K5MinorFreeChoosability
