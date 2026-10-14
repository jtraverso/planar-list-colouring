/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K33DoubleHubAttack
public import LeanPool.K5MinorFreeChoosability.Wagner.VertexCoverCore

/-!
# No actual `K₃,₃` copy in the maximal Wagner core

Let `f : Fin 6 → V` be an injective map into the support `S` of an
edge-maximal `K₅`-minor-free graph without small separations and without
clique separators of order at most three, preserving all cross edges of
`K₃,₃` (left part `val < 3`, right part `3 ≤ val`). Then we derive a
contradiction.

* At most one supported vertex lies outside the copy
  (`card_le_seven_of_actual_k33_core`).
* With no outside vertex, chords in both parts give a `K₅` minor with bags
  `{m,n}, {i}, {j}, {k}, {l}`; so one part is independent and the other part
  is a vertex cover of size three.
* With one outside vertex whose contacts are the left part, the left part is
  independent (`independent_neighbourhood_of_maximal`), and a right chord
  `k–l` gives a `K₅` minor with bags `{0,n}, {1,v}, {2}, {k}, {l}`; so the
  left part is a vertex cover. The right-contact case follows by swapping parts.
* A vertex cover of size three contradicts `no_vertex_cover_three_of_maximal_core`.

Global edge coverage is derived from edge support (`IsMaxK5Free`) and the
exact outside neighbourhood (`k33_outside_neighbourhood`).

This consumes ACTUAL copies only; it says nothing about arbitrary minor models.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

/-- A finite graph with five pairwise-adjacent clique bags has a `K₅` minor. -/
theorem not_k5MinorFree_of_cliqueBags {n : ℕ} (H : SimpleGraph (Fin n))
    (B : Fin 5 → Finset (Fin n)) (hne : ∀ i, (B i).Nonempty)
    (hcl : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b → H.Adj a b)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hadj : ∀ i j, i ≠ j → ∃ a ∈ B i, ∃ b ∈ B j, H.Adj a b) : ¬ K5MinorFree H := by
  intro h5
  apply h5
  refine ⟨⟨B, hne, ?_, hdisj, hadj⟩⟩
  intro i
  rw [← connSet_iff_induce_connected]
  exact connSet_of_pairwise_adj (by simpa using hne i)
    (fun a ha b hb => by
      by_cases hab : a = b
      · exact Or.inl hab
      · exact Or.inr (hcl i a ha b hb hab))

/-- `K₃,₃` on `Fin 6` with one chord `0–1` in the left part and one chord
`3–4` in the right part. -/
def k33TwoChords : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun a b => (a.val < 3 ∧ 3 ≤ b.val) ∨ (a = 0 ∧ b = 1) ∨ (a = 3 ∧ b = 4)

instance : DecidableRel k33TwoChords.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj _ a b).symm

/-- Bags `{2,5}, {0}, {1}, {3}, {4}`. -/
def k33TwoChordsModel (i : Fin 5) : Finset (Fin 6) :=
  match i.val with
  | 0 => {2, 5}
  | 1 => {0}
  | 2 => {1}
  | 3 => {3}
  | _ => {4}

theorem not_k5MinorFree_k33TwoChords : ¬ K5MinorFree k33TwoChords :=
  not_k5MinorFree_of_cliqueBags _ k33TwoChordsModel (by decide) (by decide) (by decide)
    (by decide)

/-- `K₃,₃` on `Fin 6` plus a vertex `6` adjacent to `1` and `2`, and a right
chord `3–4`. -/
def k33HubChord : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun a b => (a.val < 3 ∧ 3 ≤ b.val ∧ b.val < 6) ∨
    (a = 6 ∧ (b = 1 ∨ b = 2)) ∨ (a = 3 ∧ b = 4)

instance : DecidableRel k33HubChord.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj _ a b).symm

/-- Bags `{0,5}, {1,6}, {2}, {3}, {4}`. -/
def k33HubChordModel (i : Fin 5) : Finset (Fin 7) :=
  match i.val with
  | 0 => {0, 5}
  | 1 => {1, 6}
  | 2 => {2}
  | 3 => {3}
  | _ => {4}

theorem not_k5MinorFree_k33HubChord : ¬ K5MinorFree k33HubChord :=
  not_k5MinorFree_of_cliqueBags _ k33HubChordModel (by decide) (by decide) (by decide)
    (by decide)

variable {V : Type*} {G : SimpleGraph V}

/-- Transport of the two-chord kernel along an injective map. -/
theorem not_k5MinorFree_of_k33_two_chords (g : Fin 6 → V) (hg : Function.Injective g)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (g a) (g b))
    (h01 : G.Adj (g 0) (g 1)) (h34 : G.Adj (g 3) (g 4)) : ¬ K5MinorFree G := by
  intro h5
  apply not_k5MinorFree_k33TwoChords
  refine cliqueMinorFree_of_embedding g hg ?_ h5
  intro a b hab
  unfold k33TwoChords at hab
  rw [SimpleGraph.fromRel_adj] at hab
  obtain ⟨_, hab⟩ := hab
  rcases hab with (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact hK a b h.1 h.2
  · exact h01
  · exact h34
  · exact (hK b a h.1 h.2).symm
  · exact h01.symm
  · exact h34.symm

/-- Transport of the hub-chord kernel along an injective map extended by an
outside vertex `v`. -/
theorem not_k5MinorFree_of_k33_hub_chord (g : Fin 6 → V) (hg : Function.Injective g)
    {v : V} (hv : ∀ i, g i ≠ v)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (g a) (g b))
    (hv1 : G.Adj v (g 1)) (hv2 : G.Adj v (g 2)) (h34 : G.Adj (g 3) (g 4)) :
    ¬ K5MinorFree G := by
  classical
  let e : Fin 7 → V := fun a => if h : a.val < 6 then g ⟨a.val, h⟩ else v
  have he : Function.Injective e := by
    intro a b hab
    by_cases ha : a.val < 6 <;> by_cases hb : b.val < 6
    · simp only [e, ha, hb, dite_true] at hab
      have := hg hab
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · simp only [e, ha, hb, dite_true, dite_false] at hab
      exact (hv _ hab).elim
    · simp only [e, ha, hb, dite_true, dite_false] at hab
      exact (hv _ hab.symm).elim
    · exact Fin.ext (by omega)
  have e0 : ∀ i : Fin 6, e ⟨i.val, by omega⟩ = g i := by
    intro i
    simp [e, i.isLt]
  have e6 : e 6 = v := by simp [e]
  intro h5
  apply not_k5MinorFree_k33HubChord
  refine cliqueMinorFree_of_embedding e he ?_ h5
  have hcross : ∀ a b : Fin 7, a.val < 3 ∧ 3 ≤ b.val ∧ b.val < 6 → G.Adj (e a) (e b) := by
    intro a b ⟨h1, h2, h3⟩
    have := hK ⟨a.val, by omega⟩ ⟨b.val, h3⟩ h1 h2
    rw [← e0, ← e0] at this
    exact this
  have h1 : e 1 = g 1 := e0 1
  have h2 : e 2 = g 2 := e0 2
  have hv1' : G.Adj (e 6) (e 1) := by
    rw [e6, h1]; exact hv1
  have hv2' : G.Adj (e 6) (e 2) := by
    rw [e6, h2]; exact hv2
  have h34' : G.Adj (e 3) (e 4) := by
    have := h34
    rw [← e0 3, ← e0 4] at this
    exact this
  intro a b hab
  unfold k33HubChord at hab
  rw [SimpleGraph.fromRel_adj] at hab
  obtain ⟨_, hab⟩ := hab
  rcases hab with (h | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) | (h | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩)
  · exact hcross a b h
  · exact hv1'
  · exact hv2'
  · exact h34'
  · exact (hcross b a h).symm
  · exact hv1'.symm
  · exact hv2'.symm
  · exact h34'.symm

/-- Injectivity of a relabelling of `Fin 6` that keeps the two parts. -/
theorem k33_relabel_injective {i j m k l n : Fin 6}
    (hi : i.val < 3) (hj : j.val < 3) (hm : m.val < 3)
    (hk : 3 ≤ k.val) (hl : 3 ≤ l.val) (hn : 3 ≤ n.val)
    (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) (hkl : k ≠ l) (hkn : k ≠ n) (hln : l ≠ n) :
    Function.Injective ![i, j, m, k, l, n] := by
  have hij' := Fin.val_ne_of_ne hij
  have him' := Fin.val_ne_of_ne him
  have hjm' := Fin.val_ne_of_ne hjm
  have hkl' := Fin.val_ne_of_ne hkl
  have hkn' := Fin.val_ne_of_ne hkn
  have hln' := Fin.val_ne_of_ne hln
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at hab ⊢ <;> omega

theorem k33_relabel_cross {i j m k l n : Fin 6}
    (hi : i.val < 3) (hj : j.val < 3) (hm : m.val < 3)
    (hk : 3 ≤ k.val) (hl : 3 ≤ l.val) (hn : 3 ≤ n.val) :
    ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val →
      (![i, j, m, k, l, n] a).val < 3 ∧ 3 ≤ (![i, j, m, k, l, n] b).val := by
  intro a b ha hb
  fin_cases a <;> fin_cases b <;> simp_all

/-- The third vertex of a part of `Fin 6`. -/
theorem k33_third_left {i j : Fin 6} (hi : i.val < 3) (hj : j.val < 3) (hij : i ≠ j) :
    ∃ m : Fin 6, m.val < 3 ∧ i ≠ m ∧ j ≠ m := by
  have := Fin.val_ne_of_ne hij
  refine ⟨⟨3 - i.val - j.val, by omega⟩, by simp; omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Fin.val h; simp at this; omega

theorem k33_third_right {k l : Fin 6} (hk : 3 ≤ k.val) (hl : 3 ≤ l.val) (hkl : k ≠ l) :
    ∃ n : Fin 6, 3 ≤ n.val ∧ k ≠ n ∧ l ≠ n := by
  have := Fin.val_ne_of_ne hkl
  have hk6 := k.isLt
  have hl6 := l.isLt
  refine ⟨⟨12 - k.val - l.val, by omega⟩, by simp; omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Fin.val h; simp at this; omega

/-- An actual copy cannot have chords in both parts. -/
theorem not_k33_chords_both_parts (h5 : K5MinorFree G) (f : Fin 6 → V)
    (hf : Function.Injective f)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {i j k l : Fin 6} (hi : i.val < 3) (hj : j.val < 3) (hk : 3 ≤ k.val) (hl : 3 ≤ l.val)
    (hij : G.Adj (f i) (f j)) (hkl : G.Adj (f k) (f l)) : False := by
  have hij' : i ≠ j := fun h => hij.ne (congrArg f h)
  have hkl' : k ≠ l := fun h => hkl.ne (congrArg f h)
  obtain ⟨m, hm, him, hjm⟩ := k33_third_left hi hj hij'
  obtain ⟨n, hn, hkn, hln⟩ := k33_third_right hk hl hkl'
  have hσ := k33_relabel_injective hi hj hm hk hl hn hij' him hjm hkl' hkn hln
  have hc := k33_relabel_cross hi hj hm hk hl hn
  refine not_k5MinorFree_of_k33_two_chords (f ∘ ![i, j, m, k, l, n]) (hf.comp hσ) ?_ ?_ ?_ h5
  · intro a b ha hb
    exact hK _ _ (hc a b ha hb).1 (hc a b ha hb).2
  · simpa using hij
  · simpa using hkl

/-- An outside vertex adjacent to the whole left part and a right chord give
a `K₅` minor. -/
theorem not_k33_hub_right_chord (h5 : K5MinorFree G) (f : Fin 6 → V)
    (hf : Function.Injective f)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {v : V} (hv : ∀ i, f i ≠ v) (hvl : ∀ i : Fin 6, i.val < 3 → G.Adj v (f i))
    {k l : Fin 6} (hk : 3 ≤ k.val) (hl : 3 ≤ l.val) (hkl : G.Adj (f k) (f l)) : False := by
  have hkl' : k ≠ l := fun h => hkl.ne (congrArg f h)
  obtain ⟨n, hn, hkn, hln⟩ := k33_third_right hk hl hkl'
  have hσ := k33_relabel_injective (i := 0) (j := 1) (m := 2) (by decide) (by decide)
    (by decide) hk hl hn (by decide) (by decide) (by decide) hkl' hkn hln
  have hc := k33_relabel_cross (i := 0) (j := 1) (m := 2) (by decide) (by decide)
    (by decide) hk hl hn
  refine not_k5MinorFree_of_k33_hub_chord (f ∘ ![0, 1, 2, k, l, n]) (hf.comp hσ)
    (fun i => hv _) ?_ ?_ ?_ ?_ h5
  · intro a b ha hb
    exact hK _ _ (hc a b ha hb).1 (hc a b ha hb).2
  · simpa using hvl 1 (by decide)
  · simpa using hvl 2 (by decide)
  · simpa using hkl

variable [DecidableEq V]

/-- Left image of the copy. -/
def k33LeftImage (f : Fin 6 → V) : Finset V := {f 0, f 1, f 2}

/-- Right image of the copy. -/
def k33RightImage (f : Fin 6 → V) : Finset V := {f 3, f 4, f 5}

theorem mem_k33LeftImage {f : Fin 6 → V} {x : V} :
    x ∈ k33LeftImage f ↔ ∃ i : Fin 6, i.val < 3 ∧ f i = x := by
  constructor
  · intro hx
    simp only [k33LeftImage, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all [k33LeftImage]

theorem mem_k33RightImage {f : Fin 6 → V} {x : V} :
    x ∈ k33RightImage f ↔ ∃ i : Fin 6, 3 ≤ i.val ∧ f i = x := by
  constructor
  · intro hx
    simp only [k33RightImage, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨4, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all [k33RightImage]

theorem card_k33LeftImage_le (f : Fin 6 → V) : (k33LeftImage f).card ≤ 3 :=
  Finset.card_le_three

theorem card_k33RightImage_le (f : Fin 6 → V) : (k33RightImage f).card ≤ 3 :=
  Finset.card_le_three

theorem card_k33LeftImage (f : Fin 6 → V) (hf : Function.Injective f) :
    (k33LeftImage f).card = 3 := by
  apply Finset.card_eq_three.mpr
  exact ⟨f 0, f 1, f 2, fun h => by simpa using hf h, fun h => by simpa using hf h,
    fun h => by simpa using hf h, rfl⟩

/-- The left-contact branch of the consumer, stated for an arbitrary actual
copy with one outside vertex whose neighbourhood is exactly the left part. -/
theorem no_actual_k33_left_hub {S : Finset V}
    (hM : IsMaxK5Free G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b))
    {v : V} (hvS : v ∈ S) (hv : ∀ i, f i ≠ v)
    (hnb : ∀ y, G.Adj v y ↔ y ∈ k33LeftImage f)
    (hSv : ∀ x ∈ S, x = v ∨ ∃ i, f i = x) (hS5 : 5 ≤ S.card) : False := by
  have hLS : k33LeftImage f ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_k33LeftImage.mp hx
    exact hfS i
  have hvL : v ∉ k33LeftImage f := by
    intro hx
    obtain ⟨i, _, hi⟩ := mem_k33LeftImage.mp hx
    exact hv i hi
  have hind := independent_neighbourhood_of_maximal hM hsep hvS hLS hvL
    (card_k33LeftImage f hf) hS5 (fun y hy => (hnb y).mp hy) (fun y hy => (hnb y).mpr hy)
  have hvl : ∀ i : Fin 6, i.val < 3 → G.Adj v (f i) :=
    fun i hi => (hnb _).mpr (mem_k33LeftImage.mpr ⟨i, hi, rfl⟩)
  apply no_vertex_cover_three_of_maximal_core hM hsep hS5 hLS (card_k33LeftImage_le f)
  intro a b hab
  have haS := hM.1 a b hab
  have hbS := hM.1 b a hab.symm
  rcases hSv a haS with rfl | ⟨i, rfl⟩
  · exact Or.inr ((hnb b).mp hab)
  rcases hSv b hbS with rfl | ⟨j, rfl⟩
  · exact Or.inl ((hnb _).mp hab.symm)
  by_cases hi : i.val < 3
  · exact Or.inl (mem_k33LeftImage.mpr ⟨i, hi, rfl⟩)
  by_cases hj : j.val < 3
  · exact Or.inr (mem_k33LeftImage.mpr ⟨j, hj, rfl⟩)
  exact (not_k33_hub_right_chord hM.2.1 f hf hK hv hvl (by omega) (by omega) hab).elim

/-- **No actual `K₃,₃` copy in the maximal Wagner core.** -/
theorem no_actual_k33_of_maximal_core {S : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (f : Fin 6 → V) (hf : Function.Injective f) (hfS : ∀ a, f a ∈ S)
    (hK : ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → G.Adj (f a) (f b)) : False := by
  classical
  let F := Finset.univ.image f
  have hFS : F ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfS i
  have hFcard : F.card = 6 := by simp [F, Finset.card_image_of_injective _ hf]
  have hS6 : 6 ≤ S.card := hFcard ▸ Finset.card_le_card hFS
  have hS7 := card_le_seven_of_actual_k33_core hM hns hsep f hf hfS hK
  have hsd := Finset.card_sdiff_add_card_eq_card hFS
  by_cases hout : ∃ v ∈ S, v ∉ F
  · obtain ⟨v, hvS, hvF⟩ := hout
    have hv : ∀ i, f i ≠ v := fun i hi => hvF (hi ▸ Finset.mem_image_of_mem f
      (Finset.mem_univ i))
    have hSv : ∀ x ∈ S, x = v ∨ ∃ i, f i = x := by
      intro x hx
      by_cases hxF : x ∈ F
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxF
        exact Or.inr ⟨i, hi⟩
      · left
        have hle : (S \ F).card ≤ 1 := by omega
        exact Finset.card_le_one.mp hle x (Finset.mem_sdiff.mpr ⟨hx, hxF⟩) v
          (Finset.mem_sdiff.mpr ⟨hvS, hvF⟩)
    obtain ⟨_, hn⟩ := k33_outside_neighbourhood hM hns hsep f hf hfS hK hvS hvF
    rcases k33_outside_contacts_pure hM hns hsep f hf hfS hK hvS hvF with hl | hr
    · refine no_actual_k33_left_hub hM hsep f hf hfS hK hvS hv ?_ hSv (by omega)
      intro y
      rw [hn y, hl, mem_k33LeftImage]
      constructor
      · intro hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨i, by simpa [k33ContactSide] using hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact Finset.mem_image_of_mem f (by simpa [k33ContactSide] using hi)
    · -- swap the two parts
      let σ : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]
      have hσ : Function.Injective σ := by decide
      have hσl : ∀ a : Fin 6, a.val < 3 → 3 ≤ (σ a).val := by decide
      have hσr : ∀ a : Fin 6, 3 ≤ a.val → (σ a).val < 3 := by decide
      have hσσ : ∀ a : Fin 6, σ (σ a) = a := by decide
      refine no_actual_k33_left_hub hM hsep (f ∘ σ) (hf.comp hσ) (fun a => hfS _) ?_ hvS
        (fun i => hv _) ?_ ?_ (by omega)
      · intro a b ha hb
        exact (hK (σ b) (σ a) (hσr b hb) (hσl a ha)).symm
      · intro y
        rw [hn y, hr, mem_k33LeftImage]
        constructor
        · intro hy
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
          have hi' : 3 ≤ i.val := by simpa [k33ContactSide] using hi
          exact ⟨σ i, hσr i hi', by simp [hσσ]⟩
        · rintro ⟨i, hi, rfl⟩
          exact Finset.mem_image_of_mem f (by simpa [k33ContactSide] using hσl i hi)
      · intro x hx
        rcases hSv x hx with h | ⟨i, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨σ i, by simp [hσσ]⟩
  · push Not at hout
    have hSF : ∀ x ∈ S, ∃ i, f i = x := by
      intro x hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hout x hx)
      exact ⟨i, hi⟩
    have hedge : ∀ a b, G.Adj a b → ∃ i j, f i = a ∧ f j = b := by
      intro a b hab
      obtain ⟨i, hi⟩ := hSF a (hM.1 a b hab)
      obtain ⟨j, hj⟩ := hSF b (hM.1 b a hab.symm)
      exact ⟨i, j, hi, hj⟩
    by_cases hl : ∃ i j : Fin 6, i.val < 3 ∧ j.val < 3 ∧ G.Adj (f i) (f j)
    · obtain ⟨i, j, hi, hj, hij⟩ := hl
      -- the right part is independent, so the left image is a cover
      have hr : ∀ k l : Fin 6, 3 ≤ k.val → 3 ≤ l.val → ¬ G.Adj (f k) (f l) :=
        fun k l hk hl' hkl => not_k33_chords_both_parts hM.2.1 f hf hK hi hj hk hl' hij hkl
      have hLS : k33LeftImage f ⊆ S := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := mem_k33LeftImage.mp hx
        exact hfS i
      apply no_vertex_cover_three_of_maximal_core hM hsep (by omega) hLS
        (card_k33LeftImage_le f)
      intro a b hab
      obtain ⟨k, l, rfl, rfl⟩ := hedge a b hab
      by_cases hk : k.val < 3
      · exact Or.inl (mem_k33LeftImage.mpr ⟨k, hk, rfl⟩)
      by_cases hl' : l.val < 3
      · exact Or.inr (mem_k33LeftImage.mpr ⟨l, hl', rfl⟩)
      exact (hr k l (by omega) (by omega) hab).elim
    · push Not at hl
      have hRS : k33RightImage f ⊆ S := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := mem_k33RightImage.mp hx
        exact hfS i
      apply no_vertex_cover_three_of_maximal_core hM hsep (by omega) hRS
        (card_k33RightImage_le f)
      intro a b hab
      obtain ⟨k, l, rfl, rfl⟩ := hedge a b hab
      by_cases hk : 3 ≤ k.val
      · exact Or.inl (mem_k33RightImage.mpr ⟨k, hk, rfl⟩)
      by_cases hl' : 3 ≤ l.val
      · exact Or.inr (mem_k33RightImage.mpr ⟨l, hl', rfl⟩)
      exact (hl k l (by omega) (by omega) hab).elim

end LeanPool.K5MinorFreeChoosability
