/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K33Kernels

/-!
# Normal form of an arbitrary `K₃,₃` minor model

Starting from an arbitrary branch-set model of `K₃,₃` (`IsMinor K33 G`):

1. Minimising the total size of the three left branch sets makes each of them a
   single vertex: a minimal connected set touching the three right sets is a
   three-armed star (`exists_isStar3`), and all its arms can be slid into the
   right sets at once, leaving only the centre.
2. Among models with singleton left sets, minimising the total size makes every
   right set a three-armed star with centre `y l` and arms `R l t` aimed at the
   left vertex `a t`.

The result is recorded in `K33Star`. No contraction or preservation of
maximality is used: all sets live in the original graph.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Left position `t` of `Fin 6`. -/
def k33L (t : Fin 3) : Fin 6 := ⟨t.val, by omega⟩

/-- Right position `l` of `Fin 6`. -/
def k33R (l : Fin 3) : Fin 6 := ⟨l.val + 3, by omega⟩

omit [DecidableEq V] in
theorem k33L_val (t : Fin 3) : (k33L t).val = t.val := rfl

omit [DecidableEq V] in
theorem k33R_val (l : Fin 3) : (k33R l).val = l.val + 3 := rfl

omit [DecidableEq V] in
theorem k33L_inj {t t' : Fin 3} (h : k33L t = k33L t') : t = t' :=
  Fin.ext (by simpa [k33L] using congrArg Fin.val h)

omit [DecidableEq V] in
theorem k33R_inj {l l' : Fin 3} (h : k33R l = k33R l') : l = l' :=
  Fin.ext (by have := congrArg Fin.val h; simp [k33R] at this; omega)

omit [DecidableEq V] in
theorem k33L_ne_k33R (t l : Fin 3) : k33L t ≠ k33R l := by
  intro h; have := congrArg Fin.val h; simp [k33L, k33R] at this; omega

omit [DecidableEq V] in
theorem k33_cases (x : Fin 6) : (∃ t, x = k33L t) ∨ ∃ l, x = k33R l := by
  by_cases h : x.val < 3
  · exact Or.inl ⟨⟨x.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨x.val - 3, by omega⟩, Fin.ext (by simp [k33R]; omega)⟩

/-- A branch-set model of `K₃,₃` indexed by `Fin 6`. -/
structure IsK33Model (G : SimpleGraph V) (φ : Fin 6 → Finset V) : Prop where
  conn : ∀ a, ConnSet G ↑(φ a)
  disj : ∀ a b, a ≠ b → Disjoint (φ a) (φ b)
  adj : ∀ t l : Fin 3, Touch G (φ (k33L t)) (φ (k33R l))

omit [DecidableEq V] in
theorem IsK33Model.adj' {φ : Fin 6 → Finset V} (h : IsK33Model G φ) :
    ∀ a b : Fin 6, a.val < 3 → 3 ≤ b.val → Touch G (φ a) (φ b) := by
  intro a b ha hb
  have h1 : a = k33L ⟨a.val, ha⟩ := Fin.ext rfl
  have h2 : b = k33R ⟨b.val - 3, by omega⟩ := Fin.ext (by simp [k33R]; omega)
  rw [h1, h2]; exact h.adj _ _

/-- The index map `Fin 6 → Fin 3 ⊕ Fin 3`. -/
def k33Sum (x : Fin 6) : Fin 3 ⊕ Fin 3 :=
  if h : x.val < 3 then Sum.inl ⟨x.val, h⟩ else Sum.inr ⟨x.val - 3, by omega⟩

omit [DecidableEq V] in
theorem k33Sum_injective : Function.Injective k33Sum := by decide

omit [DecidableEq V] in
theorem exists_isK33Model (h : IsMinor K33 G) : ∃ φ, IsK33Model G φ := by
  obtain ⟨M⟩ := h
  refine ⟨fun x => M.branch (k33Sum x), fun x => ?_, fun x y hxy => ?_, fun t l => ?_⟩
  · exact (connSet_iff_induce_connected _ _).2 (M.branch_connected _)
  · exact M.branch_disjoint _ _ (fun h => hxy (k33Sum_injective h))
  · apply M.branch_adjacent
    have h1 : k33Sum (k33L t) = Sum.inl t := by
      simp [k33Sum, k33L, t.isLt]
    have h2 : k33Sum (k33R l) = Sum.inr l := by
      simp [k33Sum, k33R]
    rw [h1, h2]; simp

omit [DecidableEq V] in
/-- A connected set touching some set carries edges, hence lies in the support. -/
theorem connSet_sub_support {S X Y : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hX : ConnSet G ↑X) (hXY : Touch G X Y) : X ⊆ S := by
  intro v hv
  obtain ⟨c, hc, d, -, hcd⟩ := hXY
  have hr := hX.2 v hv c hc
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨e, hve, -⟩
  · exact hS _ _ hcd
  · exact hS _ _ hve.1

/-! ### Step 1: singleton left sets -/

/-- Total size of the left branch sets. -/
def k33LeftSize (φ : Fin 6 → Finset V) : ℕ := ∑ t : Fin 3, (φ (k33L t)).card

/-- Total size of all branch sets. -/
def k33Size (φ : Fin 6 → Finset V) : ℕ := ∑ x : Fin 6, (φ x).card

omit [DecidableEq V] in
/-- Replacing one branch set by a connected subset that still touches all of the
required neighbours keeps a `K₃,₃` model. -/
theorem IsK33Model.update_sub {φ : Fin 6 → Finset V} (hφ : IsK33Model G φ) (x : Fin 6)
    {B : Finset V} (hB : B ⊆ φ x) (hc : ConnSet G ↑B)
    (ht : ∀ t l, (x = k33L t ∨ x = k33R l) →
      Touch G (Function.update φ x B (k33L t)) (Function.update φ x B (k33R l))) :
    IsK33Model G (Function.update φ x B) := by
  refine ⟨fun a => ?_, fun a b hab => ?_, fun t l => ?_⟩
  · by_cases hax : a = x
    · subst hax; simpa using hc
    · simpa [Function.update_of_ne hax] using hφ.conn a
  · by_cases hax : a = x
    · subst hax
      simp only [Function.update_self, Function.update_of_ne (Ne.symm hab)]
      exact Finset.disjoint_of_subset_left hB (hφ.disj a b hab)
    by_cases hbx : b = x
    · subst hbx
      simp only [Function.update_self, Function.update_of_ne hab]
      exact Finset.disjoint_of_subset_right hB (hφ.disj a b hab)
    simp only [Function.update_of_ne hax, Function.update_of_ne hbx]
    exact hφ.disj a b hab
  · by_cases h : x = k33L t ∨ x = k33R l
    · exact ht t l h
    · push Not at h
      rw [Function.update_of_ne (Ne.symm h.1), Function.update_of_ne (Ne.symm h.2)]
      exact hφ.adj t l

/-- Slide all arms of the left star at `t` into the right sets. -/
theorem IsK33Model.slide_left {φ : Fin 6 → Finset V} (hφ : IsK33Model G φ) (t : Fin 3)
    {z : V} {R : Fin 3 → Finset V}
    (hst : IsStar3 G (fun l => φ (k33R l)) (φ (k33L t)) z R) :
    ∃ ψ, IsK33Model G ψ ∧ ψ (k33L t) = {z} ∧ ∀ t', t' ≠ t → ψ (k33L t') = φ (k33L t') := by
  classical
  let ψ : Fin 6 → Finset V := fun x =>
    if x = k33L t then {z} else
      if h : 3 ≤ x.val then φ x ∪ R ⟨x.val - 3, by omega⟩ else φ x
  have hψL : ψ (k33L t) = {z} := by simp [ψ]
  have hψL' : ∀ t', t' ≠ t → ψ (k33L t') = φ (k33L t') := by
    intro t' ht'
    have h1 : t'.val ≠ t.val := fun h => ht' (Fin.ext h)
    have h2 : ¬ 3 ≤ t'.val := by omega
    simp [ψ, k33L, h1, h2]
  have hψR : ∀ l, ψ (k33R l) = φ (k33R l) ∪ R l := by
    intro l
    have hne : k33R l ≠ k33L t := fun h => k33L_ne_k33R t l h.symm
    have h3 : 3 ≤ (k33R l).val := by simp [k33R]
    simp only [ψ, hne, ite_false, h3, dite_true]
    congr 2
  have hRsub : ∀ l, R l ⊆ φ (k33L t) := fun l => hst.R_sub_B l
  have hzmem : z ∈ φ (k33L t) := hst.z_mem
  refine ⟨ψ, ⟨fun x => ?_, fun x x' hxx => ?_, fun t' l => ?_⟩, hψL, hψL'⟩
  · rcases k33_cases x with ⟨t', rfl⟩ | ⟨l, rfl⟩
    · by_cases ht' : t' = t
      · subst ht'; rw [hψL]; exact connSet_singleton G z |>.mono le_rfl |> fun h => by
          simpa using h
      · rw [hψL' t' ht']; exact hφ.conn _
    · rw [hψR l]
      by_cases hR : (R l).Nonempty
      · exact ConnSet.union_of_touch (hφ.conn _) (hst.conn l hR) (hst.touch_T l hR).symm
      · rw [Finset.not_nonempty_iff_eq_empty.1 hR, Finset.union_empty]; exact hφ.conn _
  · -- disjointness
    have key : ∀ t' l, Disjoint (ψ (k33L t')) (ψ (k33R l)) := by
      intro t' l
      rw [hψR l]
      by_cases ht' : t' = t
      · subst ht'
        rw [hψL, Finset.disjoint_singleton_left, Finset.mem_union, not_or]
        exact ⟨fun h => Finset.disjoint_left.1 (hφ.disj _ _ (k33L_ne_k33R t' l)) hzmem h,
          hst.z_not_mem l⟩
      · rw [hψL' t' ht']
        refine Finset.disjoint_union_right.2 ⟨hφ.disj _ _ (k33L_ne_k33R t' l), ?_⟩
        exact Finset.disjoint_of_subset_right (hRsub l)
          (hφ.disj _ _ (fun h => ht' (k33L_inj h)))
    rcases k33_cases x with ⟨t1, rfl⟩ | ⟨l1, rfl⟩ <;>
      rcases k33_cases x' with ⟨t2, rfl⟩ | ⟨l2, rfl⟩
    · have ht12 : t1 ≠ t2 := fun h => hxx (h ▸ rfl)
      by_cases h1 : t1 = t
      · subst h1
        rw [hψL, hψL' t2 (Ne.symm ht12), Finset.disjoint_singleton_left]
        exact fun h => Finset.disjoint_left.1 (hφ.disj _ _ (fun h' => ht12 (k33L_inj h')))
          hzmem h
      · by_cases h2 : t2 = t
        · subst h2
          rw [hψL, hψL' t1 ht12, Finset.disjoint_singleton_right]
          exact fun h => Finset.disjoint_left.1 (hφ.disj _ _ (fun h' => ht12 (k33L_inj h')))
            h hzmem
        · rw [hψL' t1 h1, hψL' t2 h2]
          exact hφ.disj _ _ (fun h => ht12 (k33L_inj h))
    · exact key t1 l2
    · exact (key t2 l1).symm
    · have hl12 : l1 ≠ l2 := fun h => hxx (h ▸ rfl)
      rw [hψR l1, hψR l2]
      have hne : k33R l1 ≠ k33R l2 := fun h => hl12 (k33R_inj h)
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
        ⟨hφ.disj _ _ hne, ?_⟩, Finset.disjoint_union_right.2 ⟨?_, hst.R_disj l1 l2 hl12⟩⟩
      · exact Finset.disjoint_of_subset_right (hRsub l2) (hφ.disj _ _ (k33L_ne_k33R t l1).symm)
      · exact Finset.disjoint_of_subset_left (hRsub l1) (hφ.disj _ _ (k33L_ne_k33R t l2))
  · rw [hψR l]
    by_cases ht' : t' = t
    · subst ht'
      rw [hψL]
      by_cases hR : (R l).Nonempty
      · exact (hst.touch_z l hR).symm.mono subset_rfl Finset.subset_union_right
      · exact (hst.empty_T l (Finset.not_nonempty_iff_eq_empty.1 hR)).mono subset_rfl
          Finset.subset_union_left
    · rw [hψL' t' ht']
      exact (hφ.adj t' l).mono subset_rfl Finset.subset_union_left

omit [DecidableEq V] in
/-- A `K₃,₃` model whose left branch sets are single vertices. -/
theorem exists_isK33Model_left_singleton (h : ∃ φ, IsK33Model G φ) :
    ∃ φ, IsK33Model G φ ∧ ∀ t, (φ (k33L t)).card = 1 := by
  classical
  have hex : ∃ n, ∃ φ, IsK33Model G φ ∧ k33LeftSize φ = n := by
    obtain ⟨φ, hφ⟩ := h; exact ⟨_, φ, hφ, rfl⟩
  obtain ⟨φ, hφ, hs⟩ := Nat.find_spec hex
  have hmin : ∀ ψ, IsK33Model G ψ → k33LeftSize φ ≤ k33LeftSize ψ := by
    intro ψ hψ; rw [hs]; exact Nat.find_min' hex ⟨ψ, hψ, rfl⟩
  refine ⟨φ, hφ, fun t => ?_⟩
  -- minimal touching
  have hmt : IsMinTouch3 G (fun l => φ (k33R l)) (φ (k33L t)) := by
    refine ⟨hφ.conn _, fun l => hφ.adj t l, fun B' hsub hne hc ht => ?_⟩
    have hψ := hφ.update_sub (k33L t) hsub hc (fun t' l hx => by
      rcases hx with hx | hx
      · have ht' : t = t' := k33L_inj hx
        subst ht'
        rw [Function.update_self, Function.update_of_ne (k33L_ne_k33R t l).symm]
        exact ht l
      · exact absurd hx (k33L_ne_k33R t l))
    have hlt : k33LeftSize (Function.update φ (k33L t) B') < k33LeftSize φ := by
      apply Finset.sum_lt_sum
      · intro t' _
        by_cases ht' : t' = t
        · subst ht'; simpa using Finset.card_le_card hsub
        · rw [Function.update_of_ne (fun h => ht' (k33L_inj h))]
      · exact ⟨t, Finset.mem_univ _, by
          simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)⟩
    exact absurd (hmin _ hψ) (not_le.2 hlt)
  obtain ⟨z, R, hst⟩ := exists_isStar3 hmt
  obtain ⟨ψ, hψ, hψt, hψo⟩ := hφ.slide_left t hst
  by_contra hcard
  have hpos : 0 < (φ (k33L t)).card := Finset.card_pos.2 (hφ.conn _).1
  have hlt : k33LeftSize ψ < k33LeftSize φ := by
    apply Finset.sum_lt_sum
    · intro t' _
      by_cases ht' : t' = t
      · rw [ht', hψt, Finset.card_singleton]; exact hpos
      · rw [hψo t' ht']
    · exact ⟨t, Finset.mem_univ _, by rw [hψt, Finset.card_singleton]; omega⟩
  exact absurd (hmin _ hψ) (not_le.2 hlt)

/-! ### Step 2: star right sets -/

/-- Normal form: singleton left vertices `a t`, right sets `Y l` that are stars
with centre `y l` and arms `R l t` aimed at `a t`. -/
structure K33Star (G : SimpleGraph V) (a : Fin 3 → V) (Y : Fin 3 → Finset V) (y : Fin 3 → V)
    (R : Fin 3 → Fin 3 → Finset V) : Prop where
  a_inj : Function.Injective a
  a_notMem : ∀ t l, a t ∉ Y l
  Y_disj : ∀ l l', l ≠ l' → Disjoint (Y l) (Y l')
  Y_conn : ∀ l, ConnSet G ↑(Y l)
  star : ∀ l, IsStar3 G (fun t => ({a t} : Finset V)) (Y l) (y l) (R l)

theorem exists_k33Star_of_isMinor (h : IsMinor K33 G) :
    ∃ a Y y R, K33Star G a Y y R := by
  classical
  have hex : ∃ n, ∃ φ, (IsK33Model G φ ∧ ∀ t, (φ (k33L t)).card = 1) ∧ k33Size φ = n := by
    obtain ⟨φ, hφ⟩ := exists_isK33Model_left_singleton (exists_isK33Model h)
    exact ⟨_, φ, hφ, rfl⟩
  obtain ⟨φ, ⟨hφ, hφ1⟩, hs⟩ := Nat.find_spec hex
  have hmin : ∀ ψ, (IsK33Model G ψ ∧ ∀ t, (ψ (k33L t)).card = 1) → k33Size φ ≤ k33Size ψ := by
    intro ψ hψ; rw [hs]; exact Nat.find_min' hex ⟨ψ, hψ, rfl⟩
  have ha : ∀ t, ∃ x, φ (k33L t) = {x} := fun t => Finset.card_eq_one.1 (hφ1 t)
  choose a ha using ha
  have hmt : ∀ l, IsMinTouch3 G (fun t => ({a t} : Finset V)) (φ (k33R l)) := by
    intro l
    refine ⟨hφ.conn _, fun t => ?_, fun B' hsub hne hc ht => ?_⟩
    · change Touch G (φ (k33R l)) {a t}
      rw [← ha t]; exact (hφ.adj t l).symm
    have hψ := hφ.update_sub (k33R l) hsub hc (fun t l' hx => by
      rcases hx with hx | hx
      · exact absurd hx.symm (k33L_ne_k33R t l)
      · have hl : l = l' := k33R_inj hx
        subst hl
        rw [Function.update_self, Function.update_of_ne (k33L_ne_k33R t l), ha t]
        exact (ht t).symm)
    have h1 : ∀ t, (Function.update φ (k33R l) B' (k33L t)).card = 1 := by
      intro t; rw [Function.update_of_ne (k33L_ne_k33R t l)]; exact hφ1 t
    have hlt : k33Size (Function.update φ (k33R l) B') < k33Size φ := by
      apply Finset.sum_lt_sum
      · intro x _
        by_cases hx : x = k33R l
        · subst hx; simpa using Finset.card_le_card hsub
        · rw [Function.update_of_ne hx]
      · exact ⟨k33R l, Finset.mem_univ _, by
          simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)⟩
    exact absurd (hmin _ ⟨hψ, h1⟩) (not_le.2 hlt)
  have hstar := fun l => exists_isStar3 (hmt l)
  choose y R hst using hstar
  refine ⟨a, fun l => φ (k33R l), y, R, ⟨?_, ?_, ?_, ?_, hst⟩⟩
  · intro t t' htt
    by_contra hne
    have hd := hφ.disj _ _ (fun h => hne (k33L_inj h))
    rw [ha t, ha t', htt] at hd
    simp at hd
  · intro t l hmem
    have hd := hφ.disj _ _ (k33L_ne_k33R t l)
    rw [ha t] at hd
    exact Finset.disjoint_singleton_left.1 hd hmem
  · intro l l' hll
    exact hφ.disj _ _ (fun h => hll (k33R_inj h))
  · intro l; exact hφ.conn _

end LeanPool.K5MinorFreeChoosability
