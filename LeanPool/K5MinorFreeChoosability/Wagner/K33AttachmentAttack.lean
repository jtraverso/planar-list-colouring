/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerRigidity

/-!
# Four attachments to an actual `K₃,₃` force a `K₅` minor

This is a bridge restriction for an actual six-vertex copy, not a theorem
about arbitrary `K₃,₃` branch-set models. Every connected set outside that
copy has at most three attachment vertices in a `K₅`-minor-free graph.
The finite kernel is checked by explicit branch sets; transport to the
ambient graph contracts the whole connected outside set, regardless of size.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanPool.K5MinorFreeChoosability

/-- A mask for the neighbours of the extra vertex. -/
def k33HubSelected (m : Fin 64) (a : Fin 6) : Prop := m.val / 2 ^ a.val % 2 = 1

instance (m : Fin 64) (a : Fin 6) : Decidable (k33HubSelected m a) :=
  inferInstanceAs (Decidable (m.val / 2 ^ a.val % 2 = 1))

def k33HubNeighbours (m : Fin 64) : Finset (Fin 6) :=
  Finset.univ.filter (k33HubSelected m)

/-- `K₃,₃` with an additional vertex `6` carrying the specified attachments. -/
def k33Hub (m : Fin 64) : SimpleGraph (Fin 7) where
  Adj a b :=
    (a.val < 3 ∧ 3 ≤ b.val ∧ b.val < 6) ∨
    (b.val < 3 ∧ 3 ≤ a.val ∧ a.val < 6) ∨
    (a.val = 6 ∧ b.val < 6 ∧ m.val / 2 ^ b.val % 2 = 1) ∨
    (b.val = 6 ∧ a.val < 6 ∧ m.val / 2 ^ a.val % 2 = 1)
  symm := ⟨by
    intro a b h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨ha, hb, _⟩ | ⟨ha, hb, _⟩ | ⟨ha, hb, _⟩ | ⟨ha, hb, _⟩ <;> omega⟩

instance (m : Fin 64) : DecidableRel (k33Hub m).Adj := by
  unfold k33Hub
  infer_instance

/-- Two edge contractions and three singleton branches suffice for every valid mask. -/
def k33HubModel (m : Fin 64) : Fin 5 → Finset (Fin 7) :=
  if m.val = 15 then ![{0, 4}, {1, 5}, {2}, {3}, {6}]
  else if m.val = 23 ∨ m.val = 30 ∨ m.val = 31 then ![{0, 3}, {1, 5}, {2}, {4}, {6}]
  else if m.val = 27 then ![{0, 5}, {2, 3}, {1}, {4}, {6}]
  else if m.val = 29 then ![{0, 5}, {1, 3}, {2}, {4}, {6}]
  else if m.val = 43 then ![{0, 4}, {2, 3}, {1}, {5}, {6}]
  else if m.val = 45 then ![{0, 4}, {1, 3}, {2}, {5}, {6}]
  else if m.val = 51 ∨ m.val = 58 ∨ m.val = 59 then ![{0, 3}, {2, 4}, {1}, {5}, {6}]
  else if m.val = 54 then ![{0, 4}, {1, 3}, {2}, {5}, {6}]
  else if m.val = 57 then ![{1, 3}, {2, 4}, {0}, {5}, {6}]
  else ![{0, 3}, {1, 4}, {2}, {5}, {6}]

theorem k33HubModel_nonempty : ∀ m k, (k33HubModel m k).Nonempty := by decide

theorem k33HubModel_clique : ∀ m k, ∀ a ∈ k33HubModel m k,
    ∀ b ∈ k33HubModel m k, a = b ∨ (k33Hub m).Adj a b := by decide

theorem k33HubModel_disjoint : ∀ m k l, k ≠ l →
    Disjoint (k33HubModel m k) (k33HubModel m l) := by decide

set_option maxHeartbeats 2000000 in
-- Check all 64 masks and all pairs of the five explicit branch sets in the kernel.
theorem k33HubModel_adjacent : ∀ m, 4 ≤ (k33HubNeighbours m).card →
    ∀ k l, k ≠ l → ∃ a ∈ k33HubModel m k, ∃ b ∈ k33HubModel m l,
      (k33Hub m).Adj a b := by decide

theorem not_k5MinorFree_k33Hub (m : Fin 64) (hm : 4 ≤ (k33HubNeighbours m).card) :
    ¬ K5MinorFree (k33Hub m) := by
  intro h5
  apply h5
  refine ⟨⟨k33HubModel m, k33HubModel_nonempty m, ?_,
    k33HubModel_disjoint m, k33HubModel_adjacent m hm⟩⟩
  intro k
  rw [← connSet_iff_induce_connected]
  exact connSet_of_pairwise_adj (by simpa using k33HubModel_nonempty m k)
    (k33HubModel_clique m k)

set_option maxHeartbeats 2000000 in
-- Exhaust the 64 finite attachment sets and their finite witness masks.
set_option maxRecDepth 10000 in
-- The nested finite-set and witness enumerators exceed the default recursion depth.
/-- Every set of at least four indices supplies a mask with at least four attachments. -/
theorem k33Hub_exists_mask : ∀ A : Finset (Fin 6), 4 ≤ A.card →
    ∃ m : Fin 64, 4 ≤ (k33HubNeighbours m).card ∧
      ∀ i, k33HubSelected m i → i ∈ A := by decide

variable {V : Type*} {G : SimpleGraph V}

/-- Contracting a connected outside set realizes the finite attachment kernel. -/
theorem not_k5MinorFree_of_k33_four_attachments (f : Fin 6 → V)
    (hf : Function.Injective f)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    (X : Finset V) (hX : ConnSet G ↑X) (hdis : ∀ a, f a ∉ X)
    (m : Fin 64) (hm : 4 ≤ (k33HubNeighbours m).card)
    (ht : ∀ i, k33HubSelected m i → ∃ x ∈ X, G.Adj (f i) x) :
    ¬ K5MinorFree G := by
  classical
  intro h5
  let φ : Fin 7 → Finset V := fun a => if h : a.val < 6 then {f ⟨a.val, h⟩} else X
  have hc : ∀ a, ConnSet G ↑(φ a) := by
    intro a
    by_cases ha : a.val < 6
    · simpa [φ, ha] using connSet_singleton G (f ⟨a.val, ha⟩)
    · simpa [φ, ha] using hX
  have hd : ∀ a b, a ≠ b → Disjoint (φ a) (φ b) := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    by_cases ha : a.val < 6 <;> by_cases hb : b.val < 6
    · simp only [φ, dite_eq_left ha, dite_eq_left hb, Finset.mem_singleton] at hx hy
      exact hab (Fin.ext (congrArg (fun i : Fin 6 => i.val) (hf (hx.symm.trans hy))))
    · simp only [φ, dite_eq_left ha, dite_eq_right hb, Finset.mem_singleton] at hx hy
      exact hdis ⟨a.val, ha⟩ (hx ▸ hy)
    · simp only [φ, dite_eq_right ha, dite_eq_left hb, Finset.mem_singleton] at hx hy
      exact hdis ⟨b.val, hb⟩ (hy ▸ hx)
    · exact hab (Fin.ext (by omega))
  have hadj : ∀ a b, (k33Hub m).Adj a b → Touch G (φ a) (φ b) := by
    intro a b hab
    rcases hab with ⟨ha, hb, hb6⟩ | ⟨hb, ha, ha6⟩ | ⟨ha, hb6, hmb⟩ | ⟨hb, ha6, hma⟩
    · have ha6 : a.val < 6 := by omega
      simpa [φ, ha6, hb6] using
        (show Touch G {f ⟨a.val, ha6⟩} {f ⟨b.val, hb6⟩} from
          ⟨f ⟨a.val, ha6⟩, by simp, f ⟨b.val, hb6⟩, by simp,
            hK ⟨a.val, ha6⟩ ⟨b.val, hb6⟩ ha hb⟩)
    · have hb6 : b.val < 6 := by omega
      simpa [φ, ha6, hb6] using
        (show Touch G {f ⟨a.val, ha6⟩} {f ⟨b.val, hb6⟩} from
          ⟨f ⟨a.val, ha6⟩, by simp, f ⟨b.val, hb6⟩, by simp,
            (hK ⟨b.val, hb6⟩ ⟨a.val, ha6⟩ hb ha).symm⟩)
    · obtain ⟨x, hx, hfx⟩ := ht ⟨b.val, hb6⟩ hmb
      have ha6 : ¬ a.val < 6 := by omega
      simpa [φ, ha6, hb6] using
        (show Touch G X {f ⟨b.val, hb6⟩} from ⟨x, hx, _, by simp, hfx.symm⟩)
    · obtain ⟨x, hx, hfx⟩ := ht ⟨a.val, ha6⟩ hma
      have hb6 : ¬ b.val < 6 := by omega
      simpa [φ, ha6, hb6] using
        (show Touch G {f ⟨a.val, ha6⟩} X from ⟨_, by simp, x, hx, hfx⟩)
  exact not_k5MinorFree_k33Hub m hm (cliqueMinorFree_of_transport (by decide) Set.univ
    (fun _ _ _ => Set.mem_univ _) φ (fun a _ => hc a)
    (fun a _ b _ hab => hd a b hab) hadj h5)

/-- Copied vertices touching a finite outside set. -/
noncomputable def k33Attachments (G : SimpleGraph V) (f : Fin 6 → V) (X : Finset V) :
    Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun a => ∃ x ∈ X, G.Adj (f a) x)

/-- A connected set outside an actual `K₃,₃` can touch at most three copied vertices. -/
theorem k33_attachment_card_le_three (h5 : K5MinorFree G) (f : Fin 6 → V)
    (hf : Function.Injective f)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    (X : Finset V) (hX : ConnSet G ↑X) (hdis : ∀ a, f a ∉ X) :
    (k33Attachments G f X).card ≤ 3 := by
  classical
  by_contra hn
  obtain ⟨m, hm, hsub⟩ := k33Hub_exists_mask (k33Attachments G f X) (by omega)
  exact not_k5MinorFree_of_k33_four_attachments f hf hK X hX hdis m hm
    (fun i hi => (Finset.mem_filter.mp (hsub i hi)).2) h5

variable [DecidableEq V]

/-- In a maximal core, each component outside an actual `K₃,₃` is a single
vertex with exactly three attachments. This does not classify those triples. -/
theorem k33_outside_component_rigid {S : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {v : V} (hvS : v ∈ S) (hvF : v ∉ Finset.univ.image f) :
    (reachIn G (S \ Finset.univ.image f) v).card = 1 ∧
      (k33Attachments G f (reachIn G (S \ Finset.univ.image f) v)).card = 3 := by
  classical
  let F := Finset.univ.image f
  let X := reachIn G (S \ F) v
  have hvX : v ∈ X := mem_reachIn_self (Finset.mem_sdiff.mpr ⟨hvS, hvF⟩)
  have hFS : F ⊆ S := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfS a
  have hXS : X ⊆ S := fun _ hx => (Finset.mem_sdiff.mp (reachIn_sub _ _ hx)).1
  have hXF : ∀ a, f a ∉ X := by
    intro a ha
    exact (Finset.mem_sdiff.mp (reachIn_sub _ _ ha)).2
      (Finset.mem_image_of_mem f (Finset.mem_univ a))
  let K := k33Attachments G f X
  let Z := K.image f
  have hKcard : K.card ≤ 3 := k33_attachment_card_le_three hM.2.1 f hf hK X
    (reachIn_conn (Finset.mem_sdiff.mpr ⟨hvS, hvF⟩)) hXF
  have hZcard : Z.card ≤ 3 := (Finset.card_image_le).trans hKcard
  have hZF : Z ⊆ F := Finset.image_mono f (Finset.filter_subset _ _)
  have hZS : Z ⊆ S := hZF.trans hFS
  have hZX : Disjoint Z X := by
    apply Finset.disjoint_left.mpr
    intro x hx hxX
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hXF a hxX
  let A := X ∪ Z
  let B := S \ X
  have hcover : A ∪ B = S := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((hx | hx) | ⟨hx, _⟩)
      · exact hXS hx
      · exact hZS hx
      · exact hx
    · intro hx
      by_cases hxX : x ∈ X
      · exact Or.inl (Or.inl hxX)
      · exact Or.inr ⟨hx, hxX⟩
  have hinter : A ∩ B = Z := by
    ext x
    simp only [A, B, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxX | hxZ, _, hxNotX⟩
      · exact (hxNotX hxX).elim
      · exact hxZ
    · intro hxZ
      exact ⟨Or.inr hxZ, hZS hxZ, fun hxX => Finset.disjoint_left.mp hZX hxZ hxX⟩
  have hprivate : A \ B = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxNotB⟩ := Finset.mem_sdiff.mp hx
      by_cases hxX : x ∈ X
      · exact hxX
      · exact (hxNotB (Finset.mem_sdiff.mpr
          ⟨hZS ((Finset.mem_union.mp hxA).resolve_left hxX), hxX⟩)).elim
    · intro hxX
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hxX,
        fun hxB => (Finset.mem_sdiff.mp hxB).2 hxX⟩
  have hcross : ∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → ¬ G.Adj x y := by
    intro x hx hxB y hy hyA hxy
    have hyS := (Finset.mem_sdiff.mp hy).1
    have hyX := (Finset.mem_sdiff.mp hy).2
    have hyZ : y ∉ Z := fun hyZ => hyA (Finset.mem_union_right _ hyZ)
    rcases Finset.mem_union.mp hx with hxX | hxZ
    · by_cases hyF : y ∈ F
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hyF
        exact hyZ (Finset.mem_image_of_mem f (Finset.mem_filter.mpr
          ⟨Finset.mem_univ a, x, hxX, hxy.symm⟩))
      · exact hyX (reachIn_closed hxX (Finset.mem_sdiff.mpr ⟨hyS, hyF⟩) hxy)
    · exact hxB (Finset.mem_sdiff.mpr ⟨hZS hxZ,
        fun hxX => Finset.disjoint_left.mp hZX hxZ hxX⟩)
  have hAB : ¬ A ⊆ B := by
    intro h
    exact (Finset.mem_sdiff.mp (h (Finset.mem_union_left _ hvX))).2 hvX
  have hFprivate : F ⊆ Z ∪ (B \ A) := by
    intro x hxF
    have hxNotX : x ∉ X := by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxF
      exact hXF a
    by_cases hxZ : x ∈ Z
    · exact Finset.mem_union_left _ hxZ
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hFS hxF, hxNotX⟩,
          fun hxA => (Finset.mem_union.mp hxA).elim hxNotX hxZ⟩)
  have hFcard : F.card = 6 := by simp [F, Finset.card_image_of_injective _ hf]
  have hBcard : 3 ≤ (B \ A).card := by
    have hle := (Finset.card_le_card hFprivate).trans (Finset.card_union_le _ _)
    omega
  have hBA : ¬ B ⊆ A := by
    intro h
    have he := Finset.sdiff_eq_empty_iff_subset.mpr h
    rw [he, Finset.card_empty] at hBcard
    omega
  obtain ⟨hinter3, hA1 | hB1⟩ := three_separation_has_singleton_side hM hns hsep
    hcover (by rwa [hinter]) hcross hAB hBA
  · refine ⟨?_, ?_⟩
    · simpa only [hprivate] using hA1
    · have hZ3 : Z.card = 3 := by rwa [hinter] at hinter3
      have hcard : Z.card = K.card := Finset.card_image_of_injective _ hf
      exact hcard.symm.trans hZ3
  · omega

end LeanPool.K5MinorFreeChoosability
