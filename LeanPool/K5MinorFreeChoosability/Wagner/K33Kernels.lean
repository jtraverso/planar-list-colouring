/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K33CopyConsumer
public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerMinorRigidity

/-!
# Branch-set kernels around a `K₃,₃` model

Three finite kernels, stated for arbitrary connected, pairwise disjoint branch
sets of a host graph, with an explicit side-preserving relabelling of the six
`K₃,₃` positions (left part `val < 3`, right part `3 ≤ val`):

* `not_k5MinorFree_of_k33_bags_two_chords`: a `K₃,₃` bag model with one extra
  touch inside each part gives a `K₅` minor (bags `{2,5},{0},{1},{3},{4}`).
* `not_k5MinorFree_of_k33_bags_hub`: six bags with all cross touches except
  possibly `(i,k)`, together with a seventh bag touching `i, j, k, m`
  (`i ≠ j` left, `k ≠ m` right) give a `K₅` minor
  (bags `{0,5},{1},{2,3},{4},{6}`; the edge `0–3` is not used).
* `isMinor_wagner_of_k33_bags_crossing`: six bags with all cross touches except
  possibly `(i,k)` and `(j,m)` (`i ≠ j`, `k ≠ m`), a bag `P` touching `i, k`,
  a bag `P'` touching `j, m`, and `P` touching `P'`, form a `V₈` minor.

The finite pattern facts are checked by `decide`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

/-! ### Side-preserving relabelling -/

theorem exists_k33_relabel {i j k m : Fin 6} (hi : i.val < 3) (hj : j.val < 3)
    (hk : 3 ≤ k.val) (hm : 3 ≤ m.val) (hij : i ≠ j) (hkm : k ≠ m) :
    ∃ σ : Fin 6 → Fin 6, Function.Injective σ ∧ (∀ a, a.val < 3 → (σ a).val < 3) ∧
      (∀ a, 3 ≤ a.val → 3 ≤ (σ a).val) ∧ σ 0 = i ∧ σ 1 = j ∧ σ 3 = k ∧ σ 4 = m := by
  obtain ⟨n, hn, hin, hjn⟩ := k33_third_left hi hj hij
  obtain ⟨n', hn', hkn, hmn⟩ := k33_third_right hk hm hkm
  refine ⟨![i, j, n, k, m, n'], k33_relabel_injective hi hj hn hk hm hn' hij hin hjn hkm hkn hmn,
    ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro a ha
    fin_cases a <;> simp_all
  · intro a ha
    fin_cases a <;> simp_all

/-! ### Pattern graphs -/

/-- `K₃,₃` minus `0–3`, plus a vertex `6` adjacent to `0, 1, 3, 4`. -/
def k33HubMinus : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun a b => (a.val < 3 ∧ 3 ≤ b.val ∧ b.val < 6 ∧ ¬ (a = 0 ∧ b = 3)) ∨
    (a = 6 ∧ (b = 0 ∨ b = 1 ∨ b = 3 ∨ b = 4))

instance : DecidableRel k33HubMinus.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj _ a b).symm

/-- Bags `{0,5}, {1}, {2,3}, {4}, {6}`. -/
def k33HubMinusModel (i : Fin 5) : Finset (Fin 7) :=
  match i.val with
  | 0 => {0, 5}
  | 1 => {1}
  | 2 => {2, 3}
  | 3 => {4}
  | _ => {6}

theorem not_k5MinorFree_k33HubMinus : ¬ K5MinorFree k33HubMinus :=
  not_k5MinorFree_of_cliqueBags _ k33HubMinusModel (by decide) (by decide) (by decide)
    (by decide)

/-- The pattern relation of `K₃,₃` with the edges `0–3` and `1–4` subdivided by
`6` and `7`, and `6–7` added. -/
def k33CrossRel (x y : Fin 8) : Prop :=
  (x.val < 3 ∧ 3 ≤ y.val ∧ y.val < 6 ∧ ¬ (x = 0 ∧ y = 3) ∧ ¬ (x = 1 ∧ y = 4)) ∨
    (x = 6 ∧ (y = 0 ∨ y = 3)) ∨ (x = 7 ∧ (y = 1 ∨ y = 4)) ∨ (x = 6 ∧ y = 7)

instance : DecidableRel k33CrossRel := fun x y => by
  unfold k33CrossRel; infer_instance

/-- An isomorphism of `V₈` onto the crossed pattern. -/
def k33CrossPat : Fin 8 → Fin 8 := ![0, 5, 1, 7, 4, 2, 3, 6]

theorem k33CrossPat_injective : Function.Injective k33CrossPat := by decide

theorem k33CrossPat_adj : ∀ w w' : Fin 8, wagnerGraph.Adj w w' →
    k33CrossRel (k33CrossPat w) (k33CrossPat w') ∨
      k33CrossRel (k33CrossPat w') (k33CrossPat w) := by decide

variable {V : Type*} {G : SimpleGraph V}

/-! ### Standard-position kernels -/

theorem not_k5MinorFree_of_two_chords_std (ψ : Fin 6 → Finset V)
    (hc : ∀ a, ConnSet G ↑(ψ a)) (hd : ∀ a b, a ≠ b → Disjoint (ψ a) (ψ b))
    (ht : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → Touch G (ψ a) (ψ b))
    (h01 : Touch G (ψ 0) (ψ 1)) (h34 : Touch G (ψ 3) (ψ 4)) : ¬ K5MinorFree G := by
  intro h5
  apply not_k5MinorFree_k33TwoChords
  refine cliqueMinorFree_of_transport (by decide) Set.univ (fun _ _ _ => trivial) ψ
    (fun a _ => hc a) (fun a _ b _ hab => hd a b hab) ?_ h5
  intro a b hab
  unfold k33TwoChords at hab
  rw [SimpleGraph.fromRel_adj] at hab
  obtain ⟨_, hab⟩ := hab
  rcases hab with (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact ht a b h.1 h.2
  · exact h01
  · exact h34
  · exact (ht b a h.1 h.2).symm
  · exact h01.symm
  · exact h34.symm

theorem not_k5MinorFree_of_hub_std (ψ : Fin 7 → Finset V)
    (hc : ∀ a, ConnSet G ↑(ψ a)) (hd : ∀ a b, a ≠ b → Disjoint (ψ a) (ψ b))
    (ht : ∀ a b : Fin 7, a.val < 3 → 3 ≤ b.val → b.val < 6 → ¬ (a = 0 ∧ b = 3) →
      Touch G (ψ a) (ψ b))
    (h0 : Touch G (ψ 6) (ψ 0)) (h1 : Touch G (ψ 6) (ψ 1)) (h3 : Touch G (ψ 6) (ψ 3))
    (h4 : Touch G (ψ 6) (ψ 4)) : ¬ K5MinorFree G := by
  intro h5
  apply not_k5MinorFree_k33HubMinus
  refine cliqueMinorFree_of_transport (by decide) Set.univ (fun _ _ _ => trivial) ψ
    (fun a _ => hc a) (fun a _ b _ hab => hd a b hab) ?_ h5
  intro a b hab
  unfold k33HubMinus at hab
  rw [SimpleGraph.fromRel_adj] at hab
  obtain ⟨_, hab⟩ := hab
  rcases hab with (h | ⟨rfl, rfl | rfl | rfl | rfl⟩) | (h | ⟨rfl, rfl | rfl | rfl | rfl⟩)
  · exact ht a b h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact h0
  · exact h1
  · exact h3
  · exact h4
  · exact (ht b a h.1 h.2.1 h.2.2.1 h.2.2.2).symm
  · exact h0.symm
  · exact h1.symm
  · exact h3.symm
  · exact h4.symm

theorem isMinor_wagner_of_cross_std (ψ : Fin 8 → Finset V)
    (hc : ∀ a, ConnSet G ↑(ψ a)) (hd : ∀ a b, a ≠ b → Disjoint (ψ a) (ψ b))
    (hT : ∀ x y, k33CrossRel x y → Touch G (ψ x) (ψ y)) : IsMinor wagnerGraph G := by
  refine ⟨⟨fun w => ψ (k33CrossPat w), fun w => ?_, fun w => ?_, fun w w' hww => ?_,
    fun w w' hww => ?_⟩⟩
  · obtain ⟨x, hx⟩ := (hc (k33CrossPat w)).1
    exact ⟨x, hx⟩
  · exact (connSet_iff_induce_connected _ _).1 (hc _)
  · exact hd _ _ (fun h => hww (k33CrossPat_injective h))
  · rcases k33CrossPat_adj w w' hww with h | h
    · exact hT _ _ h
    · exact (hT _ _ h).symm

/-! ### Relabelled kernels -/

/-- **Two chords.** A `K₃,₃` bag model with a touch inside each part has a `K₅` minor. -/
theorem not_k5MinorFree_of_k33_bags_two_chords (ψ : Fin 6 → Finset V)
    (hc : ∀ a, ConnSet G ↑(ψ a)) (hd : ∀ a b, a ≠ b → Disjoint (ψ a) (ψ b))
    (ht : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → Touch G (ψ a) (ψ b))
    {i j k m : Fin 6} (hi : i.val < 3) (hj : j.val < 3) (hk : 3 ≤ k.val) (hm : 3 ≤ m.val)
    (hij : i ≠ j) (hkm : k ≠ m)
    (hA : Touch G (ψ i) (ψ j)) (hB : Touch G (ψ k) (ψ m)) : ¬ K5MinorFree G := by
  obtain ⟨σ, hσ, hσl, hσr, h0, h1, h3, h4⟩ := exists_k33_relabel hi hj hk hm hij hkm
  refine not_k5MinorFree_of_two_chords_std (ψ ∘ σ) (fun a => hc _)
    (fun a b hab => hd _ _ (fun h => hab (hσ h))) (fun a b ha hb => ht _ _ (hσl a ha) (hσr b hb))
    ?_ ?_
  · simpa [h0, h1] using hA
  · simpa [h3, h4] using hB

/-- **Hub.** Six bags with all cross touches except possibly `(i,k)` and a seventh
bag touching `i, j, k, m` give a `K₅` minor. -/
theorem not_k5MinorFree_of_k33_bags_hub (ψ : Fin 6 → Finset V) (H : Finset V)
    (hc : ∀ a, ConnSet G ↑(ψ a)) (hcH : ConnSet G ↑H)
    (hd : ∀ a b, a ≠ b → Disjoint (ψ a) (ψ b)) (hdH : ∀ a, Disjoint H (ψ a))
    {i j k m : Fin 6} (hi : i.val < 3) (hj : j.val < 3) (hk : 3 ≤ k.val) (hm : 3 ≤ m.val)
    (hij : i ≠ j) (hkm : k ≠ m)
    (ht : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → ¬ (a = i ∧ b = k) → Touch G (ψ a) (ψ b))
    (hHi : Touch G H (ψ i)) (hHj : Touch G H (ψ j)) (hHk : Touch G H (ψ k))
    (hHm : Touch G H (ψ m)) : ¬ K5MinorFree G := by
  classical
  obtain ⟨σ, hσ, hσl, hσr, h0, h1, h3, h4⟩ := exists_k33_relabel hi hj hk hm hij hkm
  let Φ : Fin 7 → Finset V := fun x => if h : x.val < 6 then ψ (σ ⟨x.val, h⟩) else H
  have hΦ : ∀ x : Fin 7, ∀ h : x.val < 6, Φ x = ψ (σ ⟨x.val, h⟩) := fun x h => by simp [Φ, h]
  have hΦ6 : Φ 6 = H := by simp [Φ]
  refine not_k5MinorFree_of_hub_std Φ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x
    by_cases h : x.val < 6
    · rw [hΦ x h]; exact hc _
    · simpa [Φ, h] using hcH
  · intro x y hxy
    by_cases hx : x.val < 6 <;> by_cases hy : y.val < 6
    · rw [hΦ x hx, hΦ y hy]
      refine hd _ _ (fun h => hxy ?_)
      have := congrArg Fin.val (hσ h)
      exact Fin.ext (by simpa using this)
    · simp only [Φ, hx, hy, dite_true, dite_false]
      exact (hdH _).symm
    · simp only [Φ, hx, hy, dite_true, dite_false]
      exact hdH _
    · exact absurd (Fin.ext (by omega) : x = y) hxy
  · intro x y hx hy hy6 hne
    rw [hΦ x (by omega), hΦ y hy6]
    refine ht _ _ (hσl _ hx) (hσr _ hy) ?_
    rintro ⟨hxi, hyk⟩
    apply hne
    have e1 : (⟨x.val, by omega⟩ : Fin 6) = 0 := hσ (hxi.trans h0.symm)
    have e2 : (⟨y.val, hy6⟩ : Fin 6) = 3 := hσ (hyk.trans h3.symm)
    exact ⟨Fin.ext (by simpa using congrArg Fin.val e1),
      Fin.ext (by simpa using congrArg Fin.val e2)⟩
  · rw [hΦ6, hΦ 0 (by decide)]; simpa [h0] using hHi
  · rw [hΦ6, hΦ 1 (by decide)]; simpa [h1] using hHj
  · rw [hΦ6, hΦ 3 (by decide)]; simpa [h3] using hHk
  · rw [hΦ6, hΦ 4 (by decide)]; simpa [h4] using hHm

/-- **Crossing.** Six bags with all cross touches except possibly `(i,k)` and
`(j,m)`, a bag `P` touching `i, k`, a bag `P'` touching `j, m`, and a touch
between `P` and `P'` form a `V₈` minor. -/
theorem isMinor_wagner_of_k33_bags_crossing (ψ : Fin 6 → Finset V) (P P' : Finset V)
    (hc : ∀ a, ConnSet G ↑(ψ a)) (hcP : ConnSet G ↑P) (hcP' : ConnSet G ↑P')
    (hd : ∀ a b, a ≠ b → Disjoint (ψ a) (ψ b)) (hdP : ∀ a, Disjoint P (ψ a))
    (hdP' : ∀ a, Disjoint P' (ψ a)) (hPP : Disjoint P P')
    {i j k m : Fin 6} (hi : i.val < 3) (hj : j.val < 3) (hk : 3 ≤ k.val) (hm : 3 ≤ m.val)
    (hij : i ≠ j) (hkm : k ≠ m)
    (ht : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → ¬ (a = i ∧ b = k) → ¬ (a = j ∧ b = m) →
      Touch G (ψ a) (ψ b))
    (hPi : Touch G P (ψ i)) (hPk : Touch G P (ψ k)) (hP'j : Touch G P' (ψ j))
    (hP'm : Touch G P' (ψ m)) (hPP' : Touch G P P') : IsMinor wagnerGraph G := by
  classical
  obtain ⟨σ, hσ, hσl, hσr, h0, h1, h3, h4⟩ := exists_k33_relabel hi hj hk hm hij hkm
  let Φ : Fin 8 → Finset V := fun x =>
    if h : x.val < 6 then ψ (σ ⟨x.val, h⟩) else if x.val = 6 then P else P'
  have hΦ : ∀ x : Fin 8, ∀ h : x.val < 6, Φ x = ψ (σ ⟨x.val, h⟩) := fun x h => by simp [Φ, h]
  have hΦ6 : Φ 6 = P := by simp [Φ]
  have hΦ7 : Φ 7 = P' := by simp [Φ]
  have hcases : ∀ x : Fin 8, x.val < 6 ∨ x = 6 ∨ x = 7 := by decide
  refine isMinor_wagner_of_cross_std Φ ?_ ?_ ?_
  · intro x
    rcases hcases x with h | rfl | rfl
    · rw [hΦ x h]; exact hc _
    · rw [hΦ6]; exact hcP
    · rw [hΦ7]; exact hcP'
  · intro x y hxy
    rcases hcases x with hx | rfl | rfl <;> rcases hcases y with hy | rfl | rfl
    · rw [hΦ x hx, hΦ y hy]
      refine hd _ _ (fun h => hxy ?_)
      have := congrArg Fin.val (hσ h)
      exact Fin.ext (by simpa using this)
    · rw [hΦ x hx, hΦ6]; exact (hdP _).symm
    · rw [hΦ x hx, hΦ7]; exact (hdP' _).symm
    · rw [hΦ y hy, hΦ6]; exact hdP _
    · exact absurd rfl hxy
    · rw [hΦ6, hΦ7]; exact hPP
    · rw [hΦ y hy, hΦ7]; exact hdP' _
    · rw [hΦ6, hΦ7]; exact hPP.symm
    · exact absurd rfl hxy
  · intro x y hxy
    rcases hxy with ⟨hx, hy, hy6, hn1, hn2⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · rw [hΦ x (by omega), hΦ y hy6]
      refine ht _ _ (hσl _ hx) (hσr _ hy) ?_ ?_
      · rintro ⟨hxi, hyk⟩
        apply hn1
        have e1 : (⟨x.val, by omega⟩ : Fin 6) = 0 := hσ (hxi.trans h0.symm)
        have e2 : (⟨y.val, hy6⟩ : Fin 6) = 3 := hσ (hyk.trans h3.symm)
        exact ⟨Fin.ext (by simpa using congrArg Fin.val e1),
          Fin.ext (by simpa using congrArg Fin.val e2)⟩
      · rintro ⟨hxj, hym⟩
        apply hn2
        have e1 : (⟨x.val, by omega⟩ : Fin 6) = 1 := hσ (hxj.trans h1.symm)
        have e2 : (⟨y.val, hy6⟩ : Fin 6) = 4 := hσ (hym.trans h4.symm)
        exact ⟨Fin.ext (by simpa using congrArg Fin.val e1),
          Fin.ext (by simpa using congrArg Fin.val e2)⟩
    · rw [hΦ6, hΦ 0 (by decide)]; simpa [h0] using hPi
    · rw [hΦ6, hΦ 3 (by decide)]; simpa [h3] using hPk
    · rw [hΦ7, hΦ 1 (by decide)]; simpa [h1] using hP'j
    · rw [hΦ7, hΦ 4 (by decide)]; simpa [h4] using hP'm
    · rw [hΦ6, hΦ7]; exact hPP'

end LeanPool.K5MinorFreeChoosability
