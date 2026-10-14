/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K33StarModel

/-!
# Bridges of a normalised `K₃,₃` model in the maximal Wagner core

For a normal form `K33Star G a Y y R` (left vertices `a t`, right stars `Y l`
with centres `y l` and arms `R l t` aimed at `a t`):

* `exists_bridge_of_core`: in the maximal core, a connected set `X` with at least
  two vertices, avoiding a set `Z` of at most three used vertices, has a bridge
  (a direct edge, or a path through unused vertices) to another used vertex outside
  `Z ∪ X`, provided at least two such vertices exist. Otherwise `Z` would be a
  proper three-separator with two private sides of size at least two,
  contradicting `three_separation_has_singleton_side`.
* bag constructions `k33ABag` / `k33YBag`, moving any family of arms from the
  right stars to the left vertices.
* three case lemmas:
  - `isMinor_wagner_of_crossing_bridge`: a bridge between arms `R l₁ t₁` and
    `R l₂ t₂` with `l₁ ≠ l₂`, `t₁ ≠ t₂` gives a `V₈` minor;
  - `not_k5MinorFree_of_nonconflict_bridges`: an A-bridge and a B-bridge that do
    not share an arm give a `K₅` minor (two chords, or a hub);
  - `not_k5MinorFree_of_conflict_bridges`: an A-bridge and a B-bridge sharing the
    arm `R l t` give a `K₅` minor (hub kernel with the shared arm as hub).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-! ### Bridges -/

/-- `Q` realises a bridge from `p` to `q`: either a direct edge (`Q = ∅`) or a
connected set touching both ends. -/
def IsBridge (G : SimpleGraph V) (p q : V) (Q : Finset V) : Prop :=
  (Q = ∅ ∧ G.Adj p q) ∨ (ConnSet G ↑Q ∧ Touch G Q {p} ∧ Touch G Q {q})

omit [DecidableEq V] in
theorem IsBridge.symm {p q : V} {Q : Finset V} (h : IsBridge G p q Q) : IsBridge G q p Q := by
  rcases h with ⟨hQ, hpq⟩ | ⟨hc, hp, hq⟩
  · exact Or.inl ⟨hQ, hpq.symm⟩
  · exact Or.inr ⟨hc, hq, hp⟩

theorem IsBridge.touch_union {p q : V} {Q X Y : Finset V} (h : IsBridge G p q Q)
    (hp : p ∈ X) (hq : q ∈ Y) : Touch G (X ∪ Q) Y := by
  rcases h with ⟨-, hpq⟩ | ⟨-, -, hQq⟩
  · exact ⟨p, Finset.mem_union_left _ hp, q, hq, hpq⟩
  · exact hQq.mono Finset.subset_union_right (Finset.singleton_subset_iff.2 hq)

theorem IsBridge.conn_union {p q : V} {Q X : Finset V} (h : IsBridge G p q Q)
    (hX : ConnSet G ↑X) (hp : p ∈ X) : ConnSet G ↑(X ∪ Q) := by
  rcases h with ⟨rfl, -⟩ | ⟨hc, hQp, -⟩
  · simpa using hX
  · exact ConnSet.union_of_touch hX hc
      (hQp.symm.mono (Finset.singleton_subset_iff.2 hp) subset_rfl)

/-- **Bridge existence in the maximal core.** -/
theorem exists_bridge_of_core {S Z X F : Finset V}
    (hM : IsMaxK5Free G S) (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S)
    (hZ3 : Z.card ≤ 3) (hZF : Z ⊆ F) (hFS : F ⊆ S) (hXF : X ⊆ F) (hXZ : Disjoint X Z)
    (hXc : ConnSet G ↑X) (hX2 : 2 ≤ X.card) (hrest : 2 ≤ ((F \ Z) \ X).card) :
    ∃ p ∈ X, ∃ q ∈ ((F \ Z) \ X), ∃ Q : Finset V, Q ⊆ S \ F ∧ IsBridge G p q Q := by
  classical
  obtain ⟨x0, hx0⟩ := hXc.1
  have hx0' : x0 ∈ X := by exact_mod_cast hx0
  set W := X ∪ (S \ F) with hW
  set C := reachIn G W x0 with hC
  have hx0W : x0 ∈ W := Finset.mem_union_left _ hx0'
  have hXC : X ⊆ C := sub_reachIn Finset.subset_union_left hXc hx0' (mem_reachIn_self hx0W)
  have hCW : C ⊆ W := reachIn_sub _ _
  have hCS : C ⊆ S := fun c hc => by
    rcases Finset.mem_union.1 (hCW hc) with h | h
    · exact hFS (hXF h)
    · exact (Finset.mem_sdiff.1 h).1
  have hCF : ∀ c ∈ C, c ∈ F → c ∈ X := fun c hc hcF => by
    rcases Finset.mem_union.1 (hCW hc) with h | h
    · exact h
    · exact absurd hcF (Finset.mem_sdiff.1 h).2
  have hZC : ∀ z ∈ Z, z ∉ C := fun z hz hzC =>
    Finset.disjoint_left.1 hXZ (hCF z hzC (hZF hz)) hz
  -- every edge leaving `C` towards a used vertex gives a bridge
  have key : ∀ u ∈ C, ∀ v ∈ (F \ Z) \ X, G.Adj u v →
      ∃ p ∈ X, ∃ q ∈ ((F \ Z) \ X), ∃ Q : Finset V, Q ⊆ S \ F ∧ IsBridge G p q Q := by
    intro u hu v hv huv
    rcases Finset.mem_union.1 (hCW hu) with huX | huSF
    · exact ⟨u, huX, v, hv, ∅, Finset.empty_subset _, Or.inl ⟨rfl, huv⟩⟩
    · set Q := reachIn G (S \ F) u with hQdef
      have hQsub : Q ⊆ S \ F := reachIn_sub _ _
      have huQ : u ∈ Q := mem_reachIn_self huSF
      have hx0Q : x0 ∉ Q := fun h => (Finset.mem_sdiff.1 (hQsub h)).2 (hXF hx0')
      obtain ⟨p', q', -, -, hp'Q, hq'W, hq'Q, hp'q'⟩ :=
        (mem_reachIn.1 hu).2.symm.exit (P := (↑Q : Set V)) (by exact_mod_cast huQ)
          (by exact_mod_cast hx0Q)
      have hp'Q' : p' ∈ Q := by exact_mod_cast hp'Q
      have hq'W' : q' ∈ W := by exact_mod_cast hq'W
      have hq'X : q' ∈ X := by
        rcases Finset.mem_union.1 hq'W' with h | h
        · exact h
        · exact absurd (by exact_mod_cast reachIn_closed hp'Q' h hp'q') hq'Q
      exact ⟨q', hq'X, v, hv, Q, hQsub, Or.inr ⟨reachIn_conn huSF,
        ⟨p', hp'Q', q', Finset.mem_singleton_self _, hp'q'⟩,
        ⟨u, huQ, v, Finset.mem_singleton_self _, huv⟩⟩⟩
  by_contra hno
  let A' := C ∪ Z
  let B' := S \ C
  have hcov : A' ∪ B' = S := by
    ext x
    simp only [A', B', Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | ⟨h, -⟩)
      · exact hCS h
      · exact hFS (hZF h)
      · exact h
    · intro hx
      by_cases hxC : x ∈ C
      · exact Or.inl (Or.inl hxC)
      · exact Or.inr ⟨hx, hxC⟩
  have hinter : A' ∩ B' ⊆ Z := by
    intro x hx
    simp only [A', B', Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hx
    rcases hx with ⟨h | h, -, hxC⟩
    · exact absurd h hxC
    · exact h
  have hK : (A' ∩ B').card ≤ 3 := (Finset.card_le_card hinter).trans hZ3
  have hnc : ∀ u ∈ A', u ∉ B' → ∀ v ∈ B', v ∉ A' → ¬ G.Adj u v := by
    intro u hu huB v hv hvA huv
    have huC : u ∈ C := by
      rcases Finset.mem_union.1 hu with h | h
      · exact h
      · exact absurd (Finset.mem_sdiff.2 ⟨hFS (hZF h), hZC u h⟩) huB
    obtain ⟨hvS, hvC⟩ := Finset.mem_sdiff.1 hv
    have hvZ : v ∉ Z := fun h => hvA (Finset.mem_union_right _ h)
    have hvF : v ∈ F := by
      by_contra hvF
      exact hvC (reachIn_closed huC (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hvS, hvF⟩))
        huv)
    have hvX : v ∉ X := fun h => hvC (hXC h)
    exact hno (key u huC v (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hvF, hvZ⟩, hvX⟩) huv)
  have hrestB : (F \ Z) \ X ⊆ B' \ A' := by
    intro w hw
    obtain ⟨hw1, hwX⟩ := Finset.mem_sdiff.1 hw
    obtain ⟨hwF, hwZ⟩ := Finset.mem_sdiff.1 hw1
    have hwC : w ∉ C := fun h => hwX (hCF w h hwF)
    refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hFS hwF, hwC⟩, ?_⟩
    simp only [A', Finset.mem_union, not_or]
    exact ⟨hwC, hwZ⟩
  have hXA : X ⊆ A' \ B' := by
    intro x hx
    refine Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ (hXC hx), ?_⟩
    simp only [B', Finset.mem_sdiff, not_and, not_not]
    exact fun _ => hXC hx
  have hAB : ¬ A' ⊆ B' := by
    intro h
    exact (Finset.mem_sdiff.1 (hXA hx0')).2 (h (Finset.mem_sdiff.1 (hXA hx0')).1)
  have hBA : ¬ B' ⊆ A' := by
    intro h
    obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < ((F \ Z) \ X).card)
    have := Finset.mem_sdiff.1 (hrestB hw)
    exact this.2 (h this.1)
  obtain ⟨-, h1 | h1⟩ := three_separation_has_singleton_side hM hns hsep hcov hK hnc hAB hBA
  · have := Finset.card_le_card hXA; omega
  · have := Finset.card_le_card hrestB; omega

/-! ### Bags of a normalised model -/

section Bags

variable {a : Fin 3 → V} {Y : Fin 3 → Finset V} {y : Fin 3 → V}
  {R : Fin 3 → Fin 3 → Finset V}

/-- Left bag: the vertex `a t` together with the moved arms aimed at it. -/
def k33ABag (a : Fin 3 → V) (R : Fin 3 → Fin 3 → Finset V) (mv : Finset (Fin 3 × Fin 3))
    (t : Fin 3) : Finset V :=
  {a t} ∪ (Finset.univ.filter (fun l => (l, t) ∈ mv)).biUnion (fun l => R l t)

/-- Right bag: the star `Y l` minus the removed arms. -/
def k33YBag (Y : Fin 3 → Finset V) (R : Fin 3 → Fin 3 → Finset V)
    (J : Finset (Fin 3 × Fin 3)) (l : Fin 3) : Finset V :=
  Y l \ (Finset.univ.filter (fun t => (l, t) ∈ J)).biUnion (R l)

/-- All used vertices. -/
def k33Used (a : Fin 3 → V) (Y : Fin 3 → Finset V) : Finset V :=
  Finset.univ.image a ∪ Finset.univ.biUnion Y

theorem K33Star.R_sub (hK : K33Star G a Y y R) (l t : Fin 3) : R l t ⊆ Y l :=
  (hK.star l).R_sub_B t

theorem K33Star.y_mem (hK : K33Star G a Y y R) (l : Fin 3) : y l ∈ Y l := (hK.star l).z_mem

theorem K33Star.y_notMem_R (hK : K33Star G a Y y R) (l l' t : Fin 3) : y l ∉ R l' t := by
  intro h
  by_cases hl : l = l'
  · subst hl; exact (hK.star l).z_not_mem t h
  · exact Finset.disjoint_left.1 (hK.Y_disj l l' hl) (hK.y_mem l) (hK.R_sub l' t h)

theorem K33Star.a_notMem_R (hK : K33Star G a Y y R) (t l t' : Fin 3) : a t ∉ R l t' :=
  fun h => hK.a_notMem t l (hK.R_sub l t' h)

theorem K33Star.R_disj (hK : K33Star G a Y y R) {l t l' t' : Fin 3} (h : (l, t) ≠ (l', t')) :
    Disjoint (R l t) (R l' t') := by
  by_cases hl : l = l'
  · subst hl
    have ht : t ≠ t' := fun h' => h (by rw [h'])
    exact (hK.star l).R_disj t t' ht
  · exact Finset.disjoint_of_subset_left (hK.R_sub l t)
      (Finset.disjoint_of_subset_right (hK.R_sub l' t') (hK.Y_disj l l' hl))

theorem K33Star.mem_Y_cases (hK : K33Star G a Y y R) {l : Fin 3} {x : V} (hx : x ∈ Y l) :
    x = y l ∨ ∃ t, x ∈ R l t := by
  by_cases h : x = y l
  · exact Or.inl h
  · exact Or.inr ((hK.star l).cover x hx h)

theorem k33ABag_a_mem (mv : Finset (Fin 3 × Fin 3)) (t : Fin 3) :
    a t ∈ k33ABag a R mv t := Finset.mem_union_left _ (Finset.mem_singleton_self _)

theorem k33ABag_mem_of_arm {mv : Finset (Fin 3 × Fin 3)} {l t : Fin 3}
    (h : (l, t) ∈ mv) {x : V} (hx : x ∈ R l t) : x ∈ k33ABag a R mv t :=
  Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, by simpa using h, hx⟩)

theorem k33ABag_mem_cases {mv : Finset (Fin 3 × Fin 3)} {t : Fin 3} {x : V}
    (hx : x ∈ k33ABag a R mv t) : x = a t ∨ ∃ l, (l, t) ∈ mv ∧ x ∈ R l t := by
  rcases Finset.mem_union.1 hx with h | h
  · exact Or.inl (Finset.mem_singleton.1 h)
  · obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.1 h
    exact Or.inr ⟨l, by simpa using hl, hxl⟩

theorem k33YBag_mem {J : Finset (Fin 3 × Fin 3)} {l : Fin 3} {x : V} (hx : x ∈ Y l)
    (hJ : ∀ t, (l, t) ∈ J → x ∉ R l t) : x ∈ k33YBag Y R J l := by
  refine Finset.mem_sdiff.2 ⟨hx, ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
    not_and]
  exact fun t ht => hJ t ht

theorem K33Star.y_mem_YBag (hK : K33Star G a Y y R) (J : Finset (Fin 3 × Fin 3)) (l : Fin 3) :
    y l ∈ k33YBag Y R J l :=
  k33YBag_mem (hK.y_mem l) (fun t _ => hK.y_notMem_R l l t)

theorem k33YBag_sub (J : Finset (Fin 3 × Fin 3)) (l : Fin 3) : k33YBag Y R J l ⊆ Y l :=
  Finset.sdiff_subset

theorem connSet_singleton_union_biUnion {ι : Type*} (x : V) (L : Finset ι)
    (X : ι → Finset V) (h : ∀ i ∈ L, (X i).Nonempty → ConnSet G ↑(X i) ∧ Touch G (X i) {x}) :
    ConnSet G ↑({x} ∪ L.biUnion X) := by
  classical
  induction L using Finset.induction_on with
  | empty => simpa using connSet_singleton G x
  | insert i L hi ih =>
    have ih' := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.biUnion_insert]
    have he : {x} ∪ (X i ∪ L.biUnion X) = ({x} ∪ L.biUnion X) ∪ X i := by
      ext z; simp only [Finset.mem_union]; tauto
    rw [he]
    by_cases hne : (X i).Nonempty
    · obtain ⟨hc, ht⟩ := h i (Finset.mem_insert_self _ _) hne
      exact ConnSet.union_of_touch ih' hc (ht.symm.mono (by simp) subset_rfl)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.union_empty]; exact ih'

theorem K33Star.ABag_conn (hK : K33Star G a Y y R) (mv : Finset (Fin 3 × Fin 3)) (t : Fin 3) :
    ConnSet G ↑(k33ABag a R mv t) :=
  connSet_singleton_union_biUnion _ _ _ (fun l _ hne =>
    ⟨(hK.star l).conn t hne, (hK.star l).touch_T t hne⟩)

theorem K33Star.YBag_conn (hK : K33Star G a Y y R) (J : Finset (Fin 3 × Fin 3)) (l : Fin 3) :
    ConnSet G ↑(k33YBag Y R J l) := (hK.star l).rest_conn _

theorem K33Star.ABag_disj (hK : K33Star G a Y y R) (mv mv' : Finset (Fin 3 × Fin 3))
    {t t' : Fin 3} (htt : t ≠ t') : Disjoint (k33ABag a R mv t) (k33ABag a R mv' t') := by
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  rcases k33ABag_mem_cases hx with rfl | ⟨l, -, hxl⟩ <;>
    rcases k33ABag_mem_cases hx' with h | ⟨l', -, hxl'⟩
  · exact htt (hK.a_inj h)
  · exact hK.a_notMem_R t l' t' hxl'
  · subst h; exact hK.a_notMem_R t' l t hxl
  · exact Finset.disjoint_left.1 (hK.R_disj (by simp [htt] : (l, t) ≠ (l', t'))) hxl hxl'

theorem K33Star.R_disj_ABag (hK : K33Star G a Y y R) {mv : Finset (Fin 3 × Fin 3)} {l t : Fin 3}
    (h : (l, t) ∉ mv) (t' : Fin 3) : Disjoint (R l t) (k33ABag a R mv t') := by
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  rcases k33ABag_mem_cases hx' with rfl | ⟨l', hl', hxl'⟩
  · exact hK.a_notMem_R t' l t hx
  · have hne : (l, t) ≠ (l', t') := fun he => h (he ▸ hl')
    exact Finset.disjoint_left.1 (hK.R_disj hne) hx hxl'

theorem K33Star.R_disj_YBag (hK : K33Star G a Y y R) {J : Finset (Fin 3 × Fin 3)} {l t : Fin 3}
    (h : (l, t) ∈ J) (l' : Fin 3) : Disjoint (R l t) (k33YBag Y R J l') := by
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  by_cases hl : l = l'
  · subst hl
    exact (Finset.mem_sdiff.1 hx').2 (Finset.mem_biUnion.2 ⟨t, by simpa using h, hx⟩)
  · exact Finset.disjoint_left.1 (hK.Y_disj l l' hl) (hK.R_sub l t hx) (Finset.sdiff_subset hx')

theorem K33Star.ABag_YBag_disj (hK : K33Star G a Y y R) {mv J : Finset (Fin 3 × Fin 3)}
    (hsub : mv ⊆ J) (t l : Fin 3) : Disjoint (k33ABag a R mv t) (k33YBag Y R J l) := by
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  rcases k33ABag_mem_cases hx with rfl | ⟨l', hl', hxl'⟩
  · exact hK.a_notMem t l (Finset.sdiff_subset hx')
  · exact Finset.disjoint_left.1 (hK.R_disj_YBag (hsub hl') l) hxl' hx'

theorem K33Star.YBag_disj (hK : K33Star G a Y y R) (J J' : Finset (Fin 3 × Fin 3)) {l l' : Fin 3}
    (hll : l ≠ l') : Disjoint (k33YBag Y R J l) (k33YBag Y R J' l') :=
  Finset.disjoint_of_subset_left Finset.sdiff_subset
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (hK.Y_disj l l' hll))

theorem K33Star.touch_moved (hK : K33Star G a Y y R) {mv J : Finset (Fin 3 × Fin 3)}
    {l t : Fin 3} (h : (l, t) ∈ mv) : Touch G (k33ABag a R mv t) (k33YBag Y R J l) := by
  by_cases hR : (R l t).Nonempty
  · refine ((hK.star l).touch_z t hR).mono (fun x hx => k33ABag_mem_of_arm h hx) ?_
    exact Finset.singleton_subset_iff.2 (hK.y_mem_YBag J l)
  · have := (hK.star l).empty_T t (Finset.not_nonempty_iff_eq_empty.1 hR)
    exact this.symm.mono (Finset.singleton_subset_iff.2 (k33ABag_a_mem mv t))
      (Finset.singleton_subset_iff.2 (hK.y_mem_YBag J l))

theorem K33Star.touch_unmoved (hK : K33Star G a Y y R) {mv J : Finset (Fin 3 × Fin 3)}
    {l t : Fin 3} (h : (l, t) ∉ J) : Touch G (k33ABag a R mv t) (k33YBag Y R J l) := by
  have := (hK.star l).rest_touch (Finset.univ.filter (fun t => (l, t) ∈ J)) (l := t)
    (by simpa using h)
  exact this.symm.mono (Finset.singleton_subset_iff.2 (k33ABag_a_mem mv t)) subset_rfl

theorem K33Star.ABag_sub_used (hK : K33Star G a Y y R) (mv : Finset (Fin 3 × Fin 3))
    (t : Fin 3) : k33ABag a R mv t ⊆ k33Used a Y := by
  intro x hx
  rcases k33ABag_mem_cases hx with rfl | ⟨l, -, hxl⟩
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hK.R_sub l t hxl⟩)

theorem k33Y_sub_used (l : Fin 3) : Y l ⊆ k33Used a Y := fun _ hx =>
  Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hx⟩)

theorem K33Star.R_sub_used (hK : K33Star G a Y y R) (l t : Fin 3) : R l t ⊆ k33Used a Y :=
  (hK.R_sub l t).trans (k33Y_sub_used l)

/-- Six bags indexed by `Fin 6`. -/
def k33Bags (A B : Fin 3 → Finset V) (x : Fin 6) : Finset V :=
  if h : x.val < 3 then A ⟨x.val, h⟩ else B ⟨x.val - 3, by omega⟩

omit [DecidableEq V] in
theorem k33Bags_L (A B : Fin 3 → Finset V) (t : Fin 3) : k33Bags A B (k33L t) = A t := by
  simp [k33Bags, k33L, t.isLt]

omit [DecidableEq V] in
theorem k33Bags_R (A B : Fin 3 → Finset V) (l : Fin 3) : k33Bags A B (k33R l) = B l := by
  simp [k33Bags, k33R]

omit [DecidableEq V] in
theorem k33Bags_conn {A B : Fin 3 → Finset V} (hA : ∀ t, ConnSet G ↑(A t))
    (hB : ∀ l, ConnSet G ↑(B l)) (x : Fin 6) : ConnSet G ↑(k33Bags A B x) := by
  rcases k33_cases x with ⟨t, rfl⟩ | ⟨l, rfl⟩
  · rw [k33Bags_L]; exact hA t
  · rw [k33Bags_R]; exact hB l

omit [DecidableEq V] in
theorem k33Bags_disj {A B : Fin 3 → Finset V} (hAA : ∀ t t', t ≠ t' → Disjoint (A t) (A t'))
    (hBB : ∀ l l', l ≠ l' → Disjoint (B l) (B l')) (hAB : ∀ t l, Disjoint (A t) (B l))
    (x x' : Fin 6) (hxx : x ≠ x') : Disjoint (k33Bags A B x) (k33Bags A B x') := by
  rcases k33_cases x with ⟨t, rfl⟩ | ⟨l, rfl⟩ <;> rcases k33_cases x' with ⟨t', rfl⟩ | ⟨l', rfl⟩
  · rw [k33Bags_L, k33Bags_L]; exact hAA t t' (fun h => hxx (h ▸ rfl))
  · rw [k33Bags_L, k33Bags_R]; exact hAB t l'
  · rw [k33Bags_R, k33Bags_L]; exact (hAB t' l).symm
  · rw [k33Bags_R, k33Bags_R]; exact hBB l l' (fun h => hxx (h ▸ rfl))

omit [DecidableEq V] in
theorem k33Bags_touch {A B : Fin 3 → Finset V} (P : Fin 3 → Fin 3 → Prop)
    (hT : ∀ t l, P t l → Touch G (A t) (B l)) (u v : Fin 6) (hu : u.val < 3) (hv : 3 ≤ v.val)
    (hP : ∀ t l, u = k33L t → v = k33R l → P t l) : Touch G (k33Bags A B u) (k33Bags A B v) := by
  rcases k33_cases u with ⟨t, rfl⟩ | ⟨l, rfl⟩
  · rcases k33_cases v with ⟨t', rfl⟩ | ⟨l', rfl⟩
    · simp [k33L] at hv; omega
    · rw [k33Bags_L, k33Bags_R]; exact hT t l' (hP t l' rfl rfl)
  · simp [k33R] at hu

omit [DecidableEq V] in
theorem k33L_val_lt (t : Fin 3) : (k33L t).val < 3 := t.isLt

omit [DecidableEq V] in
theorem k33R_val_ge (l : Fin 3) : 3 ≤ (k33R l).val := by simp [k33R]

omit [DecidableEq V] in
theorem k33L_ne {t t' : Fin 3} (h : t ≠ t') : k33L t ≠ k33L t' := fun e => h (k33L_inj e)

omit [DecidableEq V] in
theorem k33R_ne {l l' : Fin 3} (h : l ≠ l') : k33R l ≠ k33R l' := fun e => h (k33R_inj e)

/-! ### The three cases -/

/-- **Crossing bridge.** A bridge between arms `R l₁ t₁` and `R l₂ t₂` with
`l₁ ≠ l₂` and `t₁ ≠ t₂` gives a `V₈` minor. -/
theorem isMinor_wagner_of_crossing_bridge (hK : K33Star G a Y y R)
    {l₁ l₂ t₁ t₂ : Fin 3} (hl : l₁ ≠ l₂) (ht : t₁ ≠ t₂) {p q : V} {Q : Finset V}
    (hp : p ∈ R l₁ t₁) (hq : q ∈ R l₂ t₂) (hQ : Disjoint Q (k33Used a Y))
    (hb : IsBridge G p q Q) : IsMinor wagnerGraph G := by
  classical
  let J : Finset (Fin 3 × Fin 3) := {(l₁, t₁), (l₂, t₂)}
  let A := k33ABag a R ∅
  let B := k33YBag Y R J
  let P := R l₁ t₁ ∪ Q
  let P' := R l₂ t₂
  have hJ1 : (l₁, t₁) ∈ J := by simp [J]
  have hJ2 : (l₂, t₂) ∈ J := by simp [J]
  have hne1 : (R l₁ t₁).Nonempty := ⟨p, hp⟩
  have hne2 : (R l₂ t₂).Nonempty := ⟨q, hq⟩
  have hQA : ∀ t, Disjoint Q (A t) := fun t =>
    Finset.disjoint_of_subset_right (hK.ABag_sub_used ∅ t) hQ
  have hQB : ∀ l, Disjoint Q (B l) := fun l =>
    Finset.disjoint_of_subset_right ((k33YBag_sub J l).trans (k33Y_sub_used l)) hQ
  have hRR : Disjoint (R l₁ t₁) (R l₂ t₂) := hK.R_disj (by simp [hl])
  refine isMinor_wagner_of_k33_bags_crossing (k33Bags A B) P P'
    (k33Bags_conn (hK.ABag_conn ∅) (hK.YBag_conn J))
    (hb.conn_union ((hK.star l₁).conn t₁ hne1) hp) ((hK.star l₂).conn t₂ hne2)
    (k33Bags_disj (fun t t' h => hK.ABag_disj ∅ ∅ h) (fun l l' h => hK.YBag_disj J J h)
      (fun t l => hK.ABag_YBag_disj (Finset.empty_subset _) t l))
    ?_ ?_ ?_ (k33L_val_lt t₁) (k33L_val_lt t₂) (k33R_val_ge l₁) (k33R_val_ge l₂)
    (k33L_ne ht) (k33R_ne hl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x
    rcases k33_cases x with ⟨t, rfl⟩ | ⟨l, rfl⟩
    · rw [k33Bags_L]
      exact Finset.disjoint_union_left.2 ⟨hK.R_disj_ABag (by simp) t, hQA t⟩
    · rw [k33Bags_R]
      exact Finset.disjoint_union_left.2 ⟨hK.R_disj_YBag hJ1 l, hQB l⟩
  · intro x
    rcases k33_cases x with ⟨t, rfl⟩ | ⟨l, rfl⟩
    · rw [k33Bags_L]; exact hK.R_disj_ABag (by simp) t
    · rw [k33Bags_R]; exact hK.R_disj_YBag hJ2 l
  · exact Finset.disjoint_union_left.2 ⟨hRR, Finset.disjoint_of_subset_right
      (hK.R_sub_used l₂ t₂) hQ⟩
  · intro u v hu hv h1 h2
    refine k33Bags_touch (fun t l => (l, t) ∉ J) (fun t l h => hK.touch_unmoved h) u v hu hv ?_
    rintro t l rfl rfl
    simp only [J, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or, not_and]
    exact ⟨fun hl1 ht1 => h1 ⟨ht1 ▸ rfl, hl1 ▸ rfl⟩, fun hl2 ht2 => h2 ⟨ht2 ▸ rfl, hl2 ▸ rfl⟩⟩
  · rw [k33Bags_L]
    exact ((hK.star l₁).touch_T t₁ hne1).mono Finset.subset_union_left
      (Finset.singleton_subset_iff.2 (k33ABag_a_mem ∅ t₁))
  · rw [k33Bags_R]
    exact ((hK.star l₁).touch_z t₁ hne1).mono Finset.subset_union_left
      (Finset.singleton_subset_iff.2 (hK.y_mem_YBag J l₁))
  · rw [k33Bags_L]
    exact ((hK.star l₂).touch_T t₂ hne2).mono subset_rfl
      (Finset.singleton_subset_iff.2 (k33ABag_a_mem ∅ t₂))
  · rw [k33Bags_R]
    exact ((hK.star l₂).touch_z t₂ hne2).mono subset_rfl
      (Finset.singleton_subset_iff.2 (hK.y_mem_YBag J l₂))
  · exact hb.touch_union hp hq

/-- **Non-conflicting bridges.** An A-bridge between the left bags `i ≠ j` and a
B-bridge between the right bags `k ≠ m` of the moved model give a `K₅` minor. -/
theorem not_k5MinorFree_of_nonconflict_bridges (hK : K33Star G a Y y R)
    (mv : Finset (Fin 3 × Fin 3)) {i j k m : Fin 3} (hij : i ≠ j) (hkm : k ≠ m)
    {pA qA pB qB : V} {QA QB : Finset V}
    (hpA : pA ∈ k33ABag a R mv i) (hqA : qA ∈ k33ABag a R mv j)
    (hpB : pB ∈ k33YBag Y R mv k) (hqB : qB ∈ k33YBag Y R mv m)
    (hQA : Disjoint QA (k33Used a Y)) (hQB : Disjoint QB (k33Used a Y))
    (hbA : IsBridge G pA qA QA) (hbB : IsBridge G pB qB QB) : ¬ K5MinorFree G := by
  classical
  let A := k33ABag a R mv
  let B := k33YBag Y R mv
  have hcA : ∀ t, ConnSet G ↑(A t) := hK.ABag_conn mv
  have hcB : ∀ l, ConnSet G ↑(B l) := hK.YBag_conn mv
  have hAA : ∀ t t', t ≠ t' → Disjoint (A t) (A t') := fun t t' h => hK.ABag_disj mv mv h
  have hBB : ∀ l l', l ≠ l' → Disjoint (B l) (B l') := fun l l' h => hK.YBag_disj mv mv h
  have hAB : ∀ t l, Disjoint (A t) (B l) := fun t l => hK.ABag_YBag_disj subset_rfl t l
  have hT : ∀ t l, Touch G (A t) (B l) := fun t l => by
    by_cases h : (l, t) ∈ mv
    · exact hK.touch_moved h
    · exact hK.touch_unmoved h
  have hAu : ∀ t, A t ⊆ k33Used a Y := hK.ABag_sub_used mv
  have hBu : ∀ l, B l ⊆ k33Used a Y := fun l => (k33YBag_sub mv l).trans (k33Y_sub_used l)
  by_cases hhub : (QA ∩ QB).Nonempty
  · -- hub
    obtain ⟨x, hx⟩ := hhub
    have hxA := (Finset.mem_inter.1 hx).1
    have hxB := (Finset.mem_inter.1 hx).2
    obtain ⟨hcQA, hQAp, hQAq⟩ : ConnSet G ↑QA ∧ Touch G QA {pA} ∧ Touch G QA {qA} := by
      rcases hbA with ⟨rfl, -⟩ | h
      · simp at hxA
      · exact h
    obtain ⟨hcQB, hQBp, hQBq⟩ : ConnSet G ↑QB ∧ Touch G QB {pB} ∧ Touch G QB {qB} := by
      rcases hbB with ⟨rfl, -⟩ | h
      · simp at hxB
      · exact h
    let H := QA ∪ QB
    have hHu : Disjoint H (k33Used a Y) := Finset.disjoint_union_left.2 ⟨hQA, hQB⟩
    refine not_k5MinorFree_of_k33_bags_hub (k33Bags A B) H (k33Bags_conn hcA hcB)
      (connSet_union_of_mem hcQA hcQB hxA hxB) (k33Bags_disj hAA hBB hAB) ?_
      (k33L_val_lt i) (k33L_val_lt j) (k33R_val_ge k) (k33R_val_ge m) (k33L_ne hij)
      (k33R_ne hkm) ?_ ?_ ?_ ?_ ?_
    · intro x
      rcases k33_cases x with ⟨t, rfl⟩ | ⟨l, rfl⟩
      · rw [k33Bags_L]; exact Finset.disjoint_of_subset_right (hAu t) hHu
      · rw [k33Bags_R]; exact Finset.disjoint_of_subset_right (hBu l) hHu
    · intro u v hu hv _
      exact k33Bags_touch (fun _ _ => True) (fun t l _ => hT t l) u v hu hv (fun _ _ _ _ => trivial)
    · rw [k33Bags_L]
      exact hQAp.mono Finset.subset_union_left (Finset.singleton_subset_iff.2 hpA)
    · rw [k33Bags_L]
      exact hQAq.mono Finset.subset_union_left (Finset.singleton_subset_iff.2 hqA)
    · rw [k33Bags_R]
      exact hQBp.mono Finset.subset_union_right (Finset.singleton_subset_iff.2 hpB)
    · rw [k33Bags_R]
      exact hQBq.mono Finset.subset_union_right (Finset.singleton_subset_iff.2 hqB)
  · -- two chords
    have hQQ : Disjoint QA QB := Finset.disjoint_iff_inter_eq_empty.2
      (Finset.not_nonempty_iff_eq_empty.1 hhub)
    let A' : Fin 3 → Finset V := fun t => if t = i then A t ∪ QA else A t
    let B' : Fin 3 → Finset V := fun l => if l = k then B l ∪ QB else B l
    have hA'i : A' i = A i ∪ QA := by simp [A']
    have hA'o : ∀ t, t ≠ i → A' t = A t := fun t h => by simp [A', h]
    have hB'k : B' k = B k ∪ QB := by simp [B']
    have hB'o : ∀ l, l ≠ k → B' l = B l := fun l h => by simp [B', h]
    have hA'sub : ∀ t, A' t ⊆ A t ∪ QA := fun t => by
      by_cases h : t = i
      · rw [h, hA'i]
      · rw [hA'o t h]; exact Finset.subset_union_left
    have hB'sub : ∀ l, B' l ⊆ B l ∪ QB := fun l => by
      by_cases h : l = k
      · rw [h, hB'k]
      · rw [hB'o l h]; exact Finset.subset_union_left
    have hA'sup : ∀ t, A t ⊆ A' t := fun t => by
      by_cases h : t = i
      · rw [h, hA'i]; exact Finset.subset_union_left
      · rw [hA'o t h]
    have hB'sup : ∀ l, B l ⊆ B' l := fun l => by
      by_cases h : l = k
      · rw [h, hB'k]; exact Finset.subset_union_left
      · rw [hB'o l h]
    refine not_k5MinorFree_of_k33_bags_two_chords (k33Bags A' B') ?_ ?_ ?_
      (k33L_val_lt i) (k33L_val_lt j) (k33R_val_ge k) (k33R_val_ge m) (k33L_ne hij)
      (k33R_ne hkm) ?_ ?_
    · refine k33Bags_conn (fun t => ?_) (fun l => ?_)
      · by_cases h : t = i
        · rw [h, hA'i]; exact hbA.conn_union (hcA i) hpA
        · rw [hA'o t h]; exact hcA t
      · by_cases h : l = k
        · rw [h, hB'k]; exact hbB.conn_union (hcB k) hpB
        · rw [hB'o l h]; exact hcB l
    · have hQAA : ∀ t, Disjoint QA (A t) := fun t =>
        Finset.disjoint_of_subset_right (hAu t) hQA
      have hQBB : ∀ l, Disjoint QB (B l) := fun l =>
        Finset.disjoint_of_subset_right (hBu l) hQB
      have hQAB : ∀ l, Disjoint QA (B l) := fun l =>
        Finset.disjoint_of_subset_right (hBu l) hQA
      have hQBA : ∀ t, Disjoint QB (A t) := fun t =>
        Finset.disjoint_of_subset_right (hAu t) hQB
      refine k33Bags_disj (fun t t' htt => ?_) (fun l l' hll => ?_) (fun t l => ?_)
      · by_cases h1 : t = i
        · subst h1
          rw [hA'i, hA'o t' (Ne.symm htt)]
          exact Finset.disjoint_union_left.2 ⟨hAA _ _ htt, hQAA t'⟩
        · by_cases h2 : t' = i
          · subst h2
            rw [hA'i, hA'o t h1]
            exact Finset.disjoint_union_right.2 ⟨hAA _ _ htt, (hQAA t).symm⟩
          · rw [hA'o t h1, hA'o t' h2]; exact hAA _ _ htt
      · by_cases h1 : l = k
        · subst h1
          rw [hB'k, hB'o l' (Ne.symm hll)]
          exact Finset.disjoint_union_left.2 ⟨hBB _ _ hll, hQBB l'⟩
        · by_cases h2 : l' = k
          · subst h2
            rw [hB'k, hB'o l h1]
            exact Finset.disjoint_union_right.2 ⟨hBB _ _ hll, (hQBB l).symm⟩
          · rw [hB'o l h1, hB'o l' h2]; exact hBB _ _ hll
      · refine Finset.disjoint_of_subset_left (hA'sub t)
          (Finset.disjoint_of_subset_right (hB'sub l) ?_)
        exact Finset.disjoint_union_left.2
          ⟨Finset.disjoint_union_right.2 ⟨hAB t l, (hQBA t).symm⟩,
            Finset.disjoint_union_right.2 ⟨hQAB l, hQQ⟩⟩
    · intro u v hu hv
      exact k33Bags_touch (fun _ _ => True)
        (fun t l _ => (hT t l).mono (hA'sup t) (hB'sup l)) u v hu hv (fun _ _ _ _ => trivial)
    · rw [k33Bags_L, k33Bags_L, hA'i]
      exact hbA.touch_union hpA (hA'sup j hqA)
    · rw [k33Bags_R, k33Bags_R, hB'k]
      exact hbB.touch_union hpB (hB'sup m hqB)

end Bags

end LeanPool.K5MinorFreeChoosability
