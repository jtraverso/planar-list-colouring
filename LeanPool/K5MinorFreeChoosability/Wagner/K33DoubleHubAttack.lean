/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K33ContactRigidity

/-!
# The two opposite contact types cannot coexist

An actual `K₃,₃` with one outside vertex attached to each part has the
explicit `K₅` model `{0,3}`, `{1,6}`, `{4,7}`, `{2}`, `{5}`. Transporting
that eight-vertex kernel leaves at most one outside vertex in the maximal
core. Nothing here classifies arbitrary six-branch minor models.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

def k33DoubleHub : SimpleGraph (Fin 8) where
  Adj a b := (a.val < 3 ∧ 3 ≤ b.val ∧ b.val < 6) ∨
    (b.val < 3 ∧ 3 ≤ a.val ∧ a.val < 6) ∨
    (a.val = 6 ∧ b.val < 3) ∨ (b.val = 6 ∧ a.val < 3) ∨
    (a.val = 7 ∧ 3 ≤ b.val ∧ b.val < 6) ∨
    (b.val = 7 ∧ 3 ≤ a.val ∧ a.val < 6)
  symm := ⟨by
    intro a b h
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  loopless := ⟨by intro a h; rcases h with h | h | h | h | h | h <;> omega⟩

instance : DecidableRel k33DoubleHub.Adj := by
  unfold k33DoubleHub
  infer_instance

def k33DoubleHubModel (i : Fin 5) : Finset (Fin 8) :=
  match i.val with
  | 0 => {0, 3}
  | 1 => {1, 6}
  | 2 => {4, 7}
  | 3 => {2}
  | _ => {5}

theorem k33DoubleHubModel_nonempty : ∀ i, (k33DoubleHubModel i).Nonempty := by decide

theorem k33DoubleHubModel_clique : ∀ i, ∀ a ∈ k33DoubleHubModel i,
    ∀ b ∈ k33DoubleHubModel i, a ≠ b → k33DoubleHub.Adj a b := by decide

theorem k33DoubleHubModel_disjoint : ∀ i j, i ≠ j →
    Disjoint (k33DoubleHubModel i) (k33DoubleHubModel j) := by decide

theorem k33DoubleHubModel_adjacent : ∀ i j, i ≠ j →
    ∃ a ∈ k33DoubleHubModel i, ∃ b ∈ k33DoubleHubModel j, k33DoubleHub.Adj a b := by decide

theorem not_k5MinorFree_k33DoubleHub : ¬ K5MinorFree k33DoubleHub := by
  intro h5
  apply h5
  refine ⟨⟨k33DoubleHubModel, k33DoubleHubModel_nonempty, ?_,
    k33DoubleHubModel_disjoint, k33DoubleHubModel_adjacent⟩⟩
  intro i
  rw [← connSet_iff_induce_connected]
  exact connSet_of_pairwise_adj (by simpa using k33DoubleHubModel_nonempty i)
    (fun a ha b hb => by
      by_cases hab : a = b
      · exact Or.inl hab
      · exact Or.inr (k33DoubleHubModel_clique i a ha b hb hab))

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The finite two-host obstruction is transported by an adjacency-preserving
injection; the ambient graph need not itself be finite. -/
theorem not_k5MinorFree_of_opposite_k33_hosts (f : Fin 6 → V)
    (hf : Function.Injective f)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {u v : V} (huF : u ∉ Finset.univ.image f) (hvF : v ∉ Finset.univ.image f)
    (huv : u ≠ v) (hu : ∀ i : Fin 6, i.val < 3 → G.Adj u (f i))
    (hv : ∀ i : Fin 6, 3 ≤ i.val → G.Adj v (f i)) : ¬ K5MinorFree G := by
  classical
  let g : Fin 8 → V := fun a =>
    if h : a.val < 6 then f ⟨a.val, h⟩ else if a.val = 6 then u else v
  have hfu : ∀ i, f i ≠ u := by
    intro i hi
    exact huF (hi ▸ Finset.mem_image_of_mem f (Finset.mem_univ i))
  have hfv : ∀ i, f i ≠ v := by
    intro i hi
    exact hvF (hi ▸ Finset.mem_image_of_mem f (Finset.mem_univ i))
  have hg : Function.Injective g := by
    intro a b heq
    by_cases ha : a.val < 6 <;> by_cases hb : b.val < 6
    · simp only [g, dite_eq_left ha, dite_eq_left hb] at heq
      exact Fin.ext (congrArg (fun i : Fin 6 => i.val) (hf heq))
    · by_cases hb6 : b.val = 6
      · exact (hfu ⟨a.val, ha⟩ (by simpa [g, ha, hb, hb6] using heq)).elim
      · exact (hfv ⟨a.val, ha⟩ (by simpa [g, ha, hb, hb6] using heq)).elim
    · by_cases ha6 : a.val = 6
      · exact (hfu ⟨b.val, hb⟩ (by simpa [g, ha, hb, ha6] using heq.symm)).elim
      · exact (hfv ⟨b.val, hb⟩ (by simpa [g, ha, hb, ha6] using heq.symm)).elim
    · by_cases ha6 : a.val = 6 <;> by_cases hb6 : b.val = 6
      · exact Fin.ext (by omega)
      · exact (huv (by simpa [g, ha, hb, ha6, hb6] using heq)).elim
      · exact (huv (by simpa [g, ha, hb, ha6, hb6] using heq.symm)).elim
      · exact Fin.ext (by omega)
  have hadj : ∀ a b, k33DoubleHub.Adj a b → G.Adj (g a) (g b) := by
    intro a b hab
    rcases hab with ⟨hal, hbr, hb6⟩ | ⟨hbl, har, ha6⟩ | ⟨ha, hbl⟩ |
      ⟨hb, hal⟩ | ⟨ha, hbr, hb6⟩ | ⟨hb, har, ha6⟩
    · have ha6 : a.val < 6 := by omega
      simpa [g, ha6, hb6] using hK ⟨a.val, ha6⟩ ⟨b.val, hb6⟩ hal hbr
    · have hb6 : b.val < 6 := by omega
      simpa [g, ha6, hb6] using (hK ⟨b.val, hb6⟩ ⟨a.val, ha6⟩ hbl har).symm
    · have ha6 : ¬ a.val < 6 := by omega
      have hb6 : b.val < 6 := by omega
      simpa [g, ha6, hb6, ha] using hu ⟨b.val, hb6⟩ hbl
    · have hb6 : ¬ b.val < 6 := by omega
      have ha6 : a.val < 6 := by omega
      simpa [g, ha6, hb6, hb] using (hu ⟨a.val, ha6⟩ hal).symm
    · have ha6 : ¬ a.val < 6 := by omega
      have haNot6 : a.val ≠ 6 := by omega
      simpa [g, ha6, hb6, haNot6] using hv ⟨b.val, hb6⟩ hbr
    · have hb6 : ¬ b.val < 6 := by omega
      have hbNot6 : b.val ≠ 6 := by omega
      simpa [g, ha6, hb6, hbNot6] using (hv ⟨a.val, ha6⟩ har).symm
  exact fun h5 => not_k5MinorFree_k33DoubleHub (cliqueMinorFree_of_embedding g hg hadj h5)

/-- Combining purity, uniqueness and the two-host minor obstruction leaves
at most one vertex outside the actual copy. -/
theorem card_le_seven_of_actual_k33_core {S : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b)) :
    S.card ≤ 7 := by
  classical
  let F := Finset.univ.image f
  have hsingle : (S \ F).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huS, huF⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hvS, hvF⟩ := Finset.mem_sdiff.mp hv
    have huPure := k33_outside_contacts_pure hM hns hsep f hf hfS hK huS huF
    have hvPure := k33_outside_contacts_pure hM hns hsep f hf hfS hK hvS hvF
    by_contra huv
    have hstep : ∀ u v : V, u ≠ v → u ∉ F → v ∉ F →
        k33Attachments G f {u} = k33ContactSide true →
        k33Attachments G f {v} = k33ContactSide false → False := by
      intro u v huv huF hvF hul hvr
      apply not_k5MinorFree_of_opposite_k33_hosts f hf hK huF hvF huv ?_ ?_ hM.2.1
      · intro i hi
        have him : i ∈ k33Attachments G f {u} := by simpa [hul, k33ContactSide] using hi
        obtain ⟨x, hx, hix⟩ := (Finset.mem_filter.mp him).2
        have hxU : x = u := Finset.mem_singleton.mp hx
        simpa only [hxU] using hix.symm
      · intro i hi
        have him : i ∈ k33Attachments G f {v} := by simpa [hvr, k33ContactSide] using hi
        obtain ⟨x, hx, hix⟩ := (Finset.mem_filter.mp him).2
        have hxV : x = v := Finset.mem_singleton.mp hx
        simpa only [hxV] using hix.symm
    rcases huPure with hul | hur <;> rcases hvPure with hvl | hvr
    · exact huv (k33_outside_contacts_injective hM hns hsep f hf hfS hK huS hvS huF hvF
        (hul.trans hvl.symm))
    · exact hstep u v huv huF hvF hul hvr
    · exact hstep v u (fun h => huv h.symm) hvF huF hvl hur
    · exact huv (k33_outside_contacts_injective hM hns hsep f hf hfS hK huS hvS huF hvF
        (hur.trans hvr.symm))
  have hFS : F ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfS i
  have hFcard : F.card = 6 := by simp [F, Finset.card_image_of_injective _ hf]
  have he := Finset.card_sdiff_add_card_eq_card hFS
  omega

end LeanPool.K5MinorFreeChoosability
