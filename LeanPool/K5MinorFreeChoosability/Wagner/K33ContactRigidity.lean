/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K33AttachmentAttack

/-!
# Contact triples at an actual `K₃,₃` in the maximal core

Outside components are singletons by `k33_outside_component_rigid`. Their
three neighbours are independent, so they form one full side of the copied
`K₃,₃`. Repeated triples would give a proper three-separation with two large
private sides. These reductions do not replace an arbitrary minor model by
an actual copy and do not close `WagnerV8MinorCore`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The two parts of the fixed six-vertex copy. -/
def k33ContactSide (left : Bool) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => if left then i.val < 3 else 3 ≤ i.val)

theorem card_k33ContactSide (left : Bool) : (k33ContactSide left).card = 3 := by
  cases left <;> decide

/-- The contacts of an outside vertex are its entire neighbourhood,
including in an ambient type larger than the finite support. -/
theorem k33_outside_neighbourhood {S : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {v : V} (hvS : v ∈ S) (hvF : v ∉ Finset.univ.image f) :
    (k33Attachments G f {v}).card = 3 ∧
      ∀ y, G.Adj v y ↔ y ∈ (k33Attachments G f {v}).image f := by
  classical
  let F := Finset.univ.image f
  let R := reachIn G (S \ F) v
  have hvR : v ∈ R := mem_reachIn_self (Finset.mem_sdiff.mpr ⟨hvS, hvF⟩)
  obtain ⟨hRcard, hcontacts⟩ := k33_outside_component_rigid hM hns hsep f hf hfS hK hvS hvF
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hRcard
  have hvw : v = w := Finset.mem_singleton.mp (hw ▸ hvR)
  have hR : R = {v} := by simpa only [← hvw] using hw
  refine ⟨?_, ?_⟩
  · simpa only [show reachIn G (S \ Finset.univ.image f) v = {v} from hR] using hcontacts
  · intro y
    constructor
    · intro h
      have hyS : y ∈ S := hM.1 y v h.symm
      have hyF : y ∈ F := by
        by_contra hyF
        have hyR := reachIn_closed hvR (Finset.mem_sdiff.mpr ⟨hyS, hyF⟩) h
        have hyv : y = v := Finset.mem_singleton.mp (hR ▸ hyR)
        exact h.ne hyv.symm
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hyF
      apply Finset.mem_image_of_mem
      simp only [k33Attachments, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, Finset.mem_singleton_self v, h.symm⟩
    · intro hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨x, hx, hax⟩ := (Finset.mem_filter.mp ha).2
      have hxv : x = v := Finset.mem_singleton.mp hx
      subst x
      exact hax.symm

/-- Every outside contact triple is one entire part of the actual copy. -/
theorem k33_outside_contacts_pure {S : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {v : V} (hvS : v ∈ S) (hvF : v ∉ Finset.univ.image f) :
    k33Attachments G f {v} = k33ContactSide true ∨
      k33Attachments G f {v} = k33ContactSide false := by
  classical
  let K := k33Attachments G f {v}
  let Z := K.image f
  obtain ⟨hcard, hn⟩ := k33_outside_neighbourhood hM hns hsep f hf hfS hK hvS hvF
  have hZcard : Z.card = 3 := (Finset.card_image_of_injective _ hf).trans hcard
  have hZS : Z ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfS i
  have hvZ : v ∉ Z := by
    intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    exact hvF (hi ▸ Finset.mem_image_of_mem f (Finset.mem_univ i))
  have hS : 5 ≤ S.card := by
    have hF : Finset.univ.image f ⊆ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hfS i
    have hle := Finset.card_le_card hF
    have hFc : (Finset.univ.image f).card = 6 := by
      simp [Finset.card_image_of_injective _ hf]
    omega
  have hind := independent_neighbourhood_of_maximal hM hsep hvS hZS hvZ hZcard hS
    (fun y hy => (hn y).mp hy) (fun y hy => (hn y).mpr hy)
  have hcross : ∀ i ∈ K, ∀ j ∈ K, i.val < 3 → 3 ≤ j.val → False := by
    intro i hi j hj hleft hright
    exact hind (f i) (Finset.mem_image_of_mem f hi) (f j)
      (Finset.mem_image_of_mem f hj) (hK i j hleft hright)
  by_cases hleft : ∃ i ∈ K, i.val < 3
  · obtain ⟨i, hi, hil⟩ := hleft
    left
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      have hjl : j.val < 3 := by
        by_contra h
        exact hcross i hi j hj hil (by omega)
      simpa [k33ContactSide] using hjl
    · simpa only [card_k33ContactSide] using hcard.ge
  · right
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      have hjr : 3 ≤ j.val := by
        by_contra h
        exact hleft ⟨j, hj, by omega⟩
      simpa [k33ContactSide] using hjr
    · simpa only [card_k33ContactSide] using hcard.ge

/-- Two distinct vertices with the same three-neighbour container would
violate the large-side separator exclusion. -/
theorem no_repeated_three_neighbourhood {S Z : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (hS : 7 ≤ S.card) (hZS : Z ⊆ S) (hZ : Z.card = 3)
    {u v : V} (huS : u ∈ S) (hvS : v ∈ S) (huZ : u ∉ Z) (hvZ : v ∉ Z)
    (hu : ∀ y, G.Adj u y → y ∈ Z) (hv : ∀ y, G.Adj v y → y ∈ Z) : u = v := by
  classical
  by_contra huv
  let U : Finset V := {u, v}
  let A := U ∪ Z
  let B := S \ U
  have hU : U.card = 2 := by simp [U, huv]
  have hUS : U ⊆ S := by
    simp only [U, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨huS, hvS⟩
  have hUZ : Disjoint U Z := by
    simp [U, Finset.disjoint_left, huZ, hvZ]
  have hcover : A ∪ B = S := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((hxU | hxZ) | ⟨hxS, _⟩)
      · exact hUS hxU
      · exact hZS hxZ
      · exact hxS
    · intro hxS
      by_cases hxU : x ∈ U
      · exact Or.inl (Or.inl hxU)
      · exact Or.inr ⟨hxS, hxU⟩
  have hinter : A ∩ B = Z := by
    ext x
    simp only [A, B, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxU | hxZ, _, hxNotU⟩
      · exact (hxNotU hxU).elim
      · exact hxZ
    · intro hxZ
      exact ⟨Or.inr hxZ, hZS hxZ, fun hxU => Finset.disjoint_left.mp hUZ hxU hxZ⟩
  have hprivate : A \ B = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxNotB⟩ := Finset.mem_sdiff.mp hx
      by_cases hxU : x ∈ U
      · exact hxU
      · exact (hxNotB (Finset.mem_sdiff.mpr
          ⟨hZS ((Finset.mem_union.mp hxA).resolve_left hxU), hxU⟩)).elim
    · intro hxU
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hxU,
        fun hxB => (Finset.mem_sdiff.mp hxB).2 hxU⟩
  have hcross : ∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → ¬ G.Adj x y := by
    intro x hx hxB y _ hyA hxy
    have hxU : x ∈ U := hprivate ▸ Finset.mem_sdiff.mpr ⟨hx, hxB⟩
    have hyZ : y ∉ Z := fun hyZ => hyA (Finset.mem_union_right _ hyZ)
    rcases Finset.mem_insert.mp hxU with rfl | hxV
    · exact hyZ (hu y hxy)
    · have hxv := Finset.mem_singleton.mp hxV
      subst x
      exact hyZ (hv y hxy)
  have hAS : A ⊆ S := Finset.union_subset hUS hZS
  have hAc : A.card = 5 := by rw [Finset.card_union_of_disjoint hUZ, hU, hZ]
  have hBprivate : B \ A = S \ A := by
    ext x
    simp only [B, Finset.mem_sdiff]
    constructor
    · exact fun ⟨⟨hxS, _⟩, hxA⟩ => ⟨hxS, hxA⟩
    · exact fun ⟨hxS, hxA⟩ => ⟨⟨hxS, fun hxU => hxA (Finset.mem_union_left _ hxU)⟩, hxA⟩
  have hBc : 2 ≤ (B \ A).card := by
    have he := Finset.card_sdiff_add_card_eq_card hAS
    rw [← hBprivate] at he
    omega
  exact no_three_separation_with_large_sides hM hns hsep hcover
    (by simpa only [hinter] using hZ) hcross (by simpa only [hprivate] using hU.ge) hBc

/-- Outside vertices are distinguished by their contact triples. -/
theorem k33_outside_contacts_injective {S : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {u v : V} (huS : u ∈ S) (hvS : v ∈ S)
    (huF : u ∉ Finset.univ.image f) (hvF : v ∉ Finset.univ.image f)
    (heq : k33Attachments G f {u} = k33Attachments G f {v}) : u = v := by
  classical
  let Z := (k33Attachments G f {u}).image f
  obtain ⟨hcard, hnu⟩ := k33_outside_neighbourhood hM hns hsep f hf hfS hK huS huF
  obtain ⟨_, hnv⟩ := k33_outside_neighbourhood hM hns hsep f hf hfS hK hvS hvF
  have hZcard : Z.card = 3 := (Finset.card_image_of_injective _ hf).trans hcard
  have hZS : Z ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfS i
  have hZF : Z ⊆ Finset.univ.image f :=
    Finset.image_mono f (Finset.filter_subset _ _)
  have hF : Finset.univ.image f ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfS i
  have hS : 7 ≤ S.card := by
    have hiS : insert u (Finset.univ.image f) ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨huS, hF⟩
    have hle := Finset.card_le_card hiS
    have hic : (insert u (Finset.univ.image f)).card = 7 := by
      simp [Finset.card_insert_of_notMem huF, Finset.card_image_of_injective _ hf]
    omega
  exact no_repeated_three_neighbourhood hM hns hsep hS hZS hZcard huS hvS
    (fun h => huF (hZF h)) (fun h => hvF (hZF h))
    (fun y hy => (hnu y).mp hy) (fun y hy => by
      have h := (hnv y).mp hy
      simpa only [← heq] using h)

/-- The actual-copy branch reduces to at most eight supported vertices:
six copied vertices and at most one outside vertex per part. -/
theorem card_le_eight_of_actual_k33_core {S : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b)) :
    S.card ≤ 8 := by
  classical
  let F := Finset.univ.image f
  let label : V → Bool := fun v => decide (k33Attachments G f {v} = k33ContactSide true)
  have hinj : Set.InjOn label ↑(S \ F) := by
    intro u hu v hv heq
    obtain ⟨huS, huF⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hvS, hvF⟩ := Finset.mem_sdiff.mp hv
    apply k33_outside_contacts_injective hM hns hsep f hf hfS hK huS hvS huF hvF
    by_cases hul : k33Attachments G f {u} = k33ContactSide true
    · have hvl : k33Attachments G f {v} = k33ContactSide true := by
        by_contra hvl
        simp [label, hul, hvl] at heq
      exact hul.trans hvl.symm
    · have hvl : k33Attachments G f {v} ≠ k33ContactSide true := by
        intro hvl
        simp [label, hul, hvl] at heq
      have hur := (k33_outside_contacts_pure hM hns hsep f hf hfS hK huS huF).resolve_left hul
      have hvr := (k33_outside_contacts_pure hM hns hsep f hf hfS hK hvS hvF).resolve_left hvl
      exact hur.trans hvr.symm
  have houtside : (S \ F).card ≤ 2 := by
    have hle := Finset.card_le_card_of_injOn label
      (fun _ _ => Finset.mem_univ _) hinj
    simpa using hle
  have hFS : F ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfS i
  have hFcard : F.card = 6 := by simp [F, Finset.card_image_of_injective _ hf]
  have he := Finset.card_sdiff_add_card_eq_card hFS
  omega

end LeanPool.K5MinorFreeChoosability
