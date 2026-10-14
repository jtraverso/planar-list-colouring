/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.K33Bridges
public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerV8Reduction

/-!
# Wagner (b): the `V₈`-minor core statement, proved

`wagnerV8MinorCore` proves `WagnerV8MinorCore V` for every finite `V`:
a nonplanar edge-maximal `K₅`-minor-free graph on `S` without separations of
order at most two and without proper clique separations of order at most three
has `V₈` as a minor.

Proof outline (all sets live in the original graph; nothing is contracted):

1. Kuratowski–Wagner (a) gives a `K₃,₃` minor; normalise it (`K33Star`): left
   branch sets are vertices `a t`, right branch sets are stars `Y l` with centre
   `y l` and arms `R l t` aimed at `a t` (`exists_k33Star_of_isMinor`).
2. If every arm is empty, the model is an actual copy of `K₃,₃`, excluded by
   `no_actual_k33_of_maximal_core`.
3. Otherwise some arm `R l₀ t₀` is nonempty. `exists_bridge_of_core` applied to
   the separator `{y 0, y 1, y 2}` and the claw `{a t₀} ∪ ⋃ₗ R l t₀` gives an
   A-bridge between two claws; applied to the separator `{a 0, a 1, a 2}` and
   `Y l₀` it gives a B-bridge between two stars.
4. A crossing A-bridge gives `V₈` (`isMinor_wagner_of_crossing_bridge`). Otherwise
   the two bridges either share no arm (`not_k5MinorFree_of_nonconflict_bridges`)
   or share one arm (`not_k5MinorFree_of_conflict_bridges`), both contradicting
   `K₅`-minor-freeness.

The unconditional exports `wagnerMaximalCore`, `wagnerPrimeCore`,
`exists_k5Decomp_wagner` and `k5MinorFree_iff_exists_k5Decomp_wagner` follow by
the existing reductions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

section Core

variable {a : Fin 3 → V} {Y : Fin 3 → Finset V} {y : Fin 3 → V}
  {R : Fin 3 → Fin 3 → Finset V}

/-- **Conflicting bridges.** An A-bridge from the arm `R l t` to the left bag `t'`
and a B-bridge from the same arm to the right bag `l'` give a `K₅` minor: the arm
together with both bridge interiors is a hub touching `a t`, `a t'`, `y l` and `Y l'`. -/
theorem not_k5MinorFree_of_conflict_bridges (hK : K33Star G a Y y R)
    (mv : Finset (Fin 3 × Fin 3)) {l t t' l' : Fin 3} (htt : t ≠ t') (hll : l ≠ l')
    (hmv : (l, t) ∉ mv) {pA qA pB qB : V} {QA QB : Finset V}
    (hpA : pA ∈ R l t) (hqA : qA ∈ k33ABag a R mv t')
    (hpB : pB ∈ R l t) (hqB : qB ∈ k33YBag Y R (insert (l, t) mv) l')
    (hQA : Disjoint QA (k33Used a Y)) (hQB : Disjoint QB (k33Used a Y))
    (hbA : IsBridge G pA qA QA) (hbB : IsBridge G pB qB QB) : ¬ K5MinorFree G := by
  classical
  let J := insert (l, t) mv
  let A := k33ABag a R mv
  let B := k33YBag Y R J
  let H := (R l t ∪ QA) ∪ QB
  have hne : (R l t).Nonempty := ⟨pA, hpA⟩
  have hRH : R l t ⊆ H := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hlt : (l, t) ∈ J := Finset.mem_insert_self _ _
  refine not_k5MinorFree_of_k33_bags_hub (k33Bags A B) H
    (k33Bags_conn (hK.ABag_conn mv) (hK.YBag_conn J))
    (hbB.conn_union (hbA.conn_union ((hK.star l).conn t hne) hpA) (Finset.mem_union_left _ hpB))
    (k33Bags_disj (fun _ _ h => hK.ABag_disj mv mv h) (fun _ _ h => hK.YBag_disj J J h)
      (fun t l => hK.ABag_YBag_disj (Finset.subset_insert _ _) t l))
    ?_ (k33L_val_lt t) (k33L_val_lt t') (k33R_val_ge l) (k33R_val_ge l') (k33L_ne htt)
    (k33R_ne hll) ?_ ?_ ?_ ?_ ?_
  · intro x
    rcases k33_cases x with ⟨t2, rfl⟩ | ⟨l2, rfl⟩
    · rw [k33Bags_L]
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2
        ⟨hK.R_disj_ABag hmv t2, ?_⟩, ?_⟩
      · exact Finset.disjoint_of_subset_right (hK.ABag_sub_used mv t2) hQA
      · exact Finset.disjoint_of_subset_right (hK.ABag_sub_used mv t2) hQB
    · rw [k33Bags_R]
      have hsub : B l2 ⊆ k33Used a Y := (k33YBag_sub J l2).trans (k33Y_sub_used l2)
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2
        ⟨hK.R_disj_YBag hlt l2, ?_⟩, ?_⟩
      · exact Finset.disjoint_of_subset_right hsub hQA
      · exact Finset.disjoint_of_subset_right hsub hQB
  · intro u v hu hv hnot
    refine k33Bags_touch (fun t2 l2 => (l2, t2) ∈ mv ∨ (l2, t2) ∉ J)
      (fun t2 l2 h => h.elim (fun h' => hK.touch_moved h') (fun h' => hK.touch_unmoved h'))
      u v hu hv ?_
    rintro t2 l2 rfl rfl
    by_cases h : (l2, t2) ∈ mv
    · exact Or.inl h
    · right
      simp only [J, Finset.mem_insert, Prod.mk.injEq, not_or]
      refine ⟨fun ⟨h1, h2⟩ => hnot ⟨h2 ▸ rfl, h1 ▸ rfl⟩, h⟩
  · rw [k33Bags_L]
    exact ((hK.star l).touch_T t hne).mono hRH
      (Finset.singleton_subset_iff.2 (k33ABag_a_mem mv t))
  · rw [k33Bags_L]
    exact (hbA.touch_union hpA hqA).mono Finset.subset_union_left subset_rfl
  · rw [k33Bags_R]
    exact ((hK.star l).touch_z t hne).mono hRH
      (Finset.singleton_subset_iff.2 (hK.y_mem_YBag J l))
  · rw [k33Bags_R]
    exact hbB.touch_union (Finset.mem_union_left _ hpB) hqB

theorem K33Star.eq_of_mem_R (hK : K33Star G a Y y R) {k l t : Fin 3} {x : V} (hx : x ∈ Y k)
    (hR : x ∈ R l t) : k = l := by
  by_contra h
  exact Finset.disjoint_left.1 (hK.Y_disj k l h) hx (hK.R_sub l t hR)

theorem k33YBag_mem_of_ne {J : Finset (Fin 3 × Fin 3)} {m : Fin 3} {x : V} (hx : x ∈ Y m)
    (hJ : ∀ e ∈ J, e.1 ≠ m) : x ∈ k33YBag Y R J m :=
  k33YBag_mem hx (fun _ ht => absurd rfl (hJ _ ht))

/-- One end of the A-bridge at a left vertex, the other inside an arm. -/
theorem k33_bridges_case_ar (hK : K33Star G a Y y R) {i j k m l : Fin 3} (hij : i ≠ j)
    (hkm : k ≠ m) {qA pB qB : V} {QA QB : Finset V} (hqA : qA ∈ R l j)
    (hpB : pB ∈ Y k) (hqB : qB ∈ Y m)
    (hQA : Disjoint QA (k33Used a Y)) (hQB : Disjoint QB (k33Used a Y))
    (hbA : IsBridge G (a i) qA QA) (hbB : IsBridge G pB qB QB) : ¬ K5MinorFree G := by
  classical
  by_cases c1 : pB ∈ R l j
  · have hkl : k = l := hK.eq_of_mem_R hpB c1
    subst hkl
    exact not_k5MinorFree_of_conflict_bridges hK ∅ (Ne.symm hij) hkm (by simp) hqA
      (k33ABag_a_mem ∅ i) c1 (k33YBag_mem_of_ne hqB (by simpa using hkm))
      hQA hQB hbA.symm hbB
  by_cases c2 : qB ∈ R l j
  · have hml : m = l := hK.eq_of_mem_R hqB c2
    subst hml
    exact not_k5MinorFree_of_conflict_bridges hK ∅ (Ne.symm hij) (Ne.symm hkm) (by simp) hqA
      (k33ABag_a_mem ∅ i) c2 (k33YBag_mem_of_ne hpB (by simpa using Ne.symm hkm))
      hQA hQB hbA.symm hbB.symm
  refine not_k5MinorFree_of_nonconflict_bridges hK {(l, j)} hij hkm (k33ABag_a_mem _ i)
    (k33ABag_mem_of_arm (Finset.mem_singleton_self _) hqA) ?_ ?_ hQA hQB hbA hbB
  · exact k33YBag_mem hpB (fun t ht => by
      simp only [Finset.mem_singleton, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht; exact c1)
  · exact k33YBag_mem hqB (fun t ht => by
      simp only [Finset.mem_singleton, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht; exact c2)

/-- Both ends of the A-bridge inside arms of the same star `Y l`. -/
theorem k33_bridges_case_rr (hK : K33Star G a Y y R) {i j k m l : Fin 3} (hij : i ≠ j)
    (hkm : k ≠ m) {pA qA pB qB : V} {QA QB : Finset V} (hpA : pA ∈ R l i) (hqA : qA ∈ R l j)
    (hpB : pB ∈ Y k) (hqB : qB ∈ Y m)
    (hQA : Disjoint QA (k33Used a Y)) (hQB : Disjoint QB (k33Used a Y))
    (hbA : IsBridge G pA qA QA) (hbB : IsBridge G pB qB QB) : ¬ K5MinorFree G := by
  classical
  have hli : (l, i) ∉ ({(l, j)} : Finset (Fin 3 × Fin 3)) := by simp [hij]
  have hlj : (l, j) ∉ ({(l, i)} : Finset (Fin 3 × Fin 3)) := by simp [Ne.symm hij]
  have hJ : ∀ (s s' : Fin 3) (m' : Fin 3), m' ≠ l →
      ∀ e ∈ (insert (l, s) {(l, s')} : Finset (Fin 3 × Fin 3)), e.1 ≠ m' := by
    intro s s' m' hm' e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> exact Ne.symm hm'
  have hqAj := k33ABag_mem_of_arm (a := a) (Finset.mem_singleton_self (l, j)) hqA
  have hpAi := k33ABag_mem_of_arm (a := a) (Finset.mem_singleton_self (l, i)) hpA
  by_cases c1 : pB ∈ R l i
  · have hkl : k = l := hK.eq_of_mem_R hpB c1
    subst hkl
    exact not_k5MinorFree_of_conflict_bridges hK {(k, j)} hij hkm hli hpA hqAj c1
      (k33YBag_mem_of_ne hqB (hJ i j m (Ne.symm hkm))) hQA hQB hbA hbB
  by_cases c2 : pB ∈ R l j
  · have hkl : k = l := hK.eq_of_mem_R hpB c2
    subst hkl
    exact not_k5MinorFree_of_conflict_bridges hK {(k, i)} (Ne.symm hij) hkm hlj hqA hpAi c2
      (k33YBag_mem_of_ne hqB (hJ j i m (Ne.symm hkm))) hQA hQB hbA.symm hbB
  by_cases c3 : qB ∈ R l i
  · have hml : m = l := hK.eq_of_mem_R hqB c3
    subst hml
    exact not_k5MinorFree_of_conflict_bridges hK {(m, j)} hij (Ne.symm hkm) hli hpA hqAj c3
      (k33YBag_mem_of_ne hpB (hJ i j k hkm)) hQA hQB hbA hbB.symm
  by_cases c4 : qB ∈ R l j
  · have hml : m = l := hK.eq_of_mem_R hqB c4
    subst hml
    exact not_k5MinorFree_of_conflict_bridges hK {(m, i)} (Ne.symm hij) (Ne.symm hkm) hlj hqA
      hpAi c4 (k33YBag_mem_of_ne hpB (hJ j i k hkm)) hQA hQB hbA.symm hbB.symm
  let mv : Finset (Fin 3 × Fin 3) := {(l, i), (l, j)}
  refine not_k5MinorFree_of_nonconflict_bridges hK mv hij hkm
    (k33ABag_mem_of_arm (by simp [mv]) hpA) (k33ABag_mem_of_arm (by simp [mv]) hqA) ?_ ?_
    hQA hQB hbA hbB
  · exact k33YBag_mem hpB (fun t ht => by
      simp only [mv, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact c1
      · exact c2)
  · exact k33YBag_mem hqB (fun t ht => by
      simp only [mv, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact c3
      · exact c4)

/-- **Dispatch.** An A-bridge between claws `i ≠ j` and a B-bridge between stars
`k ≠ m` give a `V₈` minor or a `K₅` minor. -/
theorem isMinor_wagner_or_not_k5MinorFree_of_bridges (hK : K33Star G a Y y R)
    {i j k m : Fin 3} (hij : i ≠ j) (hkm : k ≠ m) {pA qA pB qB : V} {QA QB : Finset V}
    (hpA : pA = a i ∨ ∃ l, pA ∈ R l i) (hqA : qA = a j ∨ ∃ l, qA ∈ R l j)
    (hpB : pB ∈ Y k) (hqB : qB ∈ Y m)
    (hQA : Disjoint QA (k33Used a Y)) (hQB : Disjoint QB (k33Used a Y))
    (hbA : IsBridge G pA qA QA) (hbB : IsBridge G pB qB QB) :
    IsMinor wagnerGraph G ∨ ¬ K5MinorFree G := by
  classical
  rcases hpA with rfl | ⟨l1, hl1⟩ <;> rcases hqA with rfl | ⟨l2, hl2⟩
  · right
    exact not_k5MinorFree_of_nonconflict_bridges hK ∅ hij hkm (k33ABag_a_mem ∅ i)
      (k33ABag_a_mem ∅ j) (k33YBag_mem hpB (fun t ht => by simp at ht))
      (k33YBag_mem hqB (fun t ht => by simp at ht)) hQA hQB hbA hbB
  · exact Or.inr (k33_bridges_case_ar hK hij hkm hl2 hpB hqB hQA hQB hbA hbB)
  · exact Or.inr (k33_bridges_case_ar hK (Ne.symm hij) hkm hl1 hpB hqB hQA hQB hbA.symm hbB)
  · by_cases hl : l1 = l2
    · subst hl
      exact Or.inr (k33_bridges_case_rr hK hij hkm hl1 hl2 hpB hqB hQA hQB hbA hbB)
    · exact Or.inl (isMinor_wagner_of_crossing_bridge hK hl hij hl1 hl2 hQA hbA)

theorem K33Star.y_inj (hK : K33Star G a Y y R) : Function.Injective y := by
  intro l l' h
  by_contra hne
  exact Finset.disjoint_left.1 (hK.Y_disj l l' hne) (hK.y_mem l) (h ▸ hK.y_mem l')

theorem K33Star.touch_Y_a (hK : K33Star G a Y y R) (l t : Fin 3) : Touch G (Y l) {a t} := by
  have := (hK.star l).rest_touch ∅ (l := t) (by simp)
  simpa using this

/-- With all arms empty the normal form is an actual copy of `K₃,₃`, which the
maximal core excludes. -/
theorem K33Star.false_of_arms_empty {S : Finset V} (hM : IsMaxK5Free G S)
    (hns : NoSmallSep G S) (hsep : NoCliqueSepThree G S) (hK : K33Star G a Y y R)
    (hall : ∀ l t, R l t = ∅) : False := by
  classical
  have hadj : ∀ t l, G.Adj (a t) (y l) := by
    intro t l
    obtain ⟨u, hu, v, hv, huv⟩ := (hK.star l).empty_T t (hall l t)
    rw [Finset.mem_singleton] at hu hv
    subst hu; subst hv; exact huv.symm
  let f : Fin 6 → V := fun x => if h : x.val < 3 then a ⟨x.val, h⟩ else y ⟨x.val - 3, by omega⟩
  have fL : ∀ t, f (k33L t) = a t := fun t => by simp [f, k33L, t.isLt]
  have fR : ∀ l, f (k33R l) = y l := fun l => by simp [f, k33R]
  have hay : ∀ t l, a t ≠ y l := fun t l h => hK.a_notMem t l (h ▸ hK.y_mem l)
  refine no_actual_k33_of_maximal_core hM hns hsep f ?_ ?_ ?_
  · intro x x' hxx
    rcases k33_cases x with ⟨t, rfl⟩ | ⟨l, rfl⟩ <;> rcases k33_cases x' with ⟨t', rfl⟩ | ⟨l', rfl⟩
    · rw [fL, fL] at hxx; rw [hK.a_inj hxx]
    · rw [fL, fR] at hxx; exact absurd hxx (hay t l')
    · rw [fR, fL] at hxx; exact absurd hxx.symm (hay t' l)
    · rw [fR, fR] at hxx; rw [hK.y_inj hxx]
  · intro x
    rcases k33_cases x with ⟨t, rfl⟩ | ⟨l, rfl⟩
    · rw [fL]; exact hM.1 _ _ (hadj t 0)
    · rw [fR]; exact hM.1 _ _ (hadj 0 l).symm
  · intro u v hu hv
    rcases k33_cases u with ⟨t, rfl⟩ | ⟨l, rfl⟩
    · rcases k33_cases v with ⟨t', rfl⟩ | ⟨l', rfl⟩
      · simp [k33L] at hv; omega
      · rw [fL, fR]; exact hadj t l'
    · simp [k33R] at hu

end Core

theorem fin3_filter_ne_card : ∀ t0 : Fin 3, (Finset.univ.filter (fun t => t ≠ t0)).card = 2 := by
  decide

section Bridges

variable {a : Fin 3 → V} {Y : Fin 3 → Finset V} {y : Fin 3 → V}
  {R : Fin 3 → Fin 3 → Finset V}

theorem K33Star.a_ne_y (hK : K33Star G a Y y R) (t l : Fin 3) : a t ≠ y l :=
  fun h => hK.a_notMem t l (h ▸ hK.y_mem l)

theorem k33Used_a_mem (t : Fin 3) : a t ∈ k33Used a Y :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))

/-- The A-bridge leaving the claw of `a t₀` when the arm `R l₀ t₀` is nonempty. -/
theorem K33Star.exists_A_bridge {S : Finset V} (hM : IsMaxK5Free G S) (hns : NoSmallSep G S)
    (hsep : NoCliqueSepThree G S) (hK : K33Star G a Y y R) (hFS : k33Used a Y ⊆ S)
    {l0 t0 : Fin 3} {r : V} (hr : r ∈ R l0 t0) :
    ∃ (pA qA : V) (QA : Finset V) (j : Fin 3), j ≠ t0 ∧ (pA = a t0 ∨ ∃ l, pA ∈ R l t0) ∧
      (qA = a j ∨ ∃ l, qA ∈ R l j) ∧ Disjoint QA (k33Used a Y) ∧ IsBridge G pA qA QA := by
  classical
  have hZA3 : (Finset.univ.image y).card ≤ 3 := Finset.card_image_le.trans (by simp)
  have hZAF : Finset.univ.image y ⊆ k33Used a Y := by
    intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    exact k33Y_sub_used l (hK.y_mem l)
  have hXAZ : Disjoint (k33ABag a R Finset.univ t0) (Finset.univ.image y) := by
    refine Finset.disjoint_left.2 fun x hx hxZ => ?_
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hxZ
    rcases k33ABag_mem_cases hx with h | ⟨l', -, h⟩
    · exact hK.a_ne_y t0 l h.symm
    · exact hK.y_notMem_R l l' t0 h
  have hXA2 : 2 ≤ (k33ABag a R Finset.univ t0).card := by
    apply Finset.one_lt_card.2
    exact ⟨a t0, k33ABag_a_mem _ t0, r, k33ABag_mem_of_arm (Finset.mem_univ _) hr,
      fun h => hK.a_notMem_R t0 l0 t0 (h ▸ hr)⟩
  have hXArest : 2 ≤ ((k33Used a Y \ Finset.univ.image y) \ k33ABag a R Finset.univ t0).card := by
    have hsub : (Finset.univ.filter (fun t => t ≠ t0)).image a ⊆
        (k33Used a Y \ Finset.univ.image y) \ k33ABag a R Finset.univ t0 := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      have ht0 : t ≠ t0 := (Finset.mem_filter.1 ht).2
      refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨k33Used_a_mem t, ?_⟩, ?_⟩
      · intro h
        obtain ⟨l, -, hl⟩ := Finset.mem_image.1 h
        exact hK.a_ne_y t l hl.symm
      · exact Finset.disjoint_left.1 (hK.ABag_disj Finset.univ Finset.univ ht0)
          (k33ABag_a_mem _ t)
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hK.a_inj, fin3_filter_ne_card] at this
    exact this
  obtain ⟨pA, hpA, qA, hqA, QA, hQAsub, hbA⟩ := exists_bridge_of_core hM hns hsep hZA3 hZAF hFS
    (hK.ABag_sub_used _ t0) hXAZ (hK.ABag_conn _ t0) hXA2 hXArest
  have hQA : Disjoint QA (k33Used a Y) := Finset.disjoint_left.2 fun x hx hxF =>
    (Finset.mem_sdiff.1 (hQAsub hx)).2 hxF
  have hpA' : pA = a t0 ∨ ∃ l, pA ∈ R l t0 := by
    rcases k33ABag_mem_cases hpA with h | ⟨l, -, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨l, h⟩
  obtain ⟨hqA1, hqAX⟩ := Finset.mem_sdiff.1 hqA
  obtain ⟨hqAF, hqAZ⟩ := Finset.mem_sdiff.1 hqA1
  rcases Finset.mem_union.1 hqAF with h | h
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
    refine ⟨pA, a j, QA, j, fun hj => ?_, hpA', Or.inl rfl, hQA, hbA⟩
    subst hj
    exact hqAX (k33ABag_a_mem _ _)
  · obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 h
    rcases hK.mem_Y_cases hl with h' | ⟨j, hj⟩
    · exact absurd (by rw [h']; exact Finset.mem_image_of_mem y (Finset.mem_univ l)) hqAZ
    · refine ⟨pA, qA, QA, j, fun hj' => hqAX ?_, hpA', Or.inr ⟨l, hj⟩, hQA, hbA⟩
      subst hj'
      exact k33ABag_mem_of_arm (Finset.mem_univ _) hj

/-- The B-bridge leaving the star `Y l₀` when the arm `R l₀ t₀` is nonempty. -/
theorem K33Star.exists_B_bridge {S : Finset V} (hM : IsMaxK5Free G S) (hns : NoSmallSep G S)
    (hsep : NoCliqueSepThree G S) (hK : K33Star G a Y y R) (hFS : k33Used a Y ⊆ S)
    {l0 t0 : Fin 3} {r : V} (hr : r ∈ R l0 t0) :
    ∃ (pB qB : V) (QB : Finset V) (m : Fin 3), m ≠ l0 ∧ pB ∈ Y l0 ∧ qB ∈ Y m ∧
      Disjoint QB (k33Used a Y) ∧ IsBridge G pB qB QB := by
  classical
  have hZB3 : (Finset.univ.image a).card ≤ 3 := Finset.card_image_le.trans (by simp)
  have hZBF : Finset.univ.image a ⊆ k33Used a Y := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx
    exact k33Used_a_mem t
  have hXBZ : Disjoint (Y l0) (Finset.univ.image a) := by
    refine Finset.disjoint_left.2 fun x hx hxZ => ?_
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hxZ
    exact hK.a_notMem t l0 hx
  have hXB2 : 2 ≤ (Y l0).card := by
    apply Finset.one_lt_card.2
    exact ⟨y l0, hK.y_mem l0, r, hK.R_sub l0 t0 hr,
      fun h => hK.y_notMem_R l0 l0 t0 (h ▸ hr)⟩
  have hXBrest : 2 ≤ ((k33Used a Y \ Finset.univ.image a) \ Y l0).card := by
    have hsub : (Finset.univ.filter (fun l => l ≠ l0)).image y ⊆
        (k33Used a Y \ Finset.univ.image a) \ Y l0 := by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
      have hl0 : l ≠ l0 := (Finset.mem_filter.1 hl).2
      refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨k33Y_sub_used l (hK.y_mem l), ?_⟩, ?_⟩
      · intro h
        obtain ⟨t, -, ht⟩ := Finset.mem_image.1 h
        exact hK.a_ne_y t l ht
      · exact Finset.disjoint_left.1 (hK.Y_disj l l0 hl0) (hK.y_mem l)
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hK.y_inj, fin3_filter_ne_card] at this
    exact this
  obtain ⟨pB, hpB, qB, hqB, QB, hQBsub, hbB⟩ := exists_bridge_of_core hM hns hsep hZB3 hZBF hFS
    (k33Y_sub_used l0) hXBZ (hK.Y_conn l0) hXB2 hXBrest
  have hQB : Disjoint QB (k33Used a Y) := Finset.disjoint_left.2 fun x hx hxF =>
    (Finset.mem_sdiff.1 (hQBsub hx)).2 hxF
  obtain ⟨hqB1, hqBX⟩ := Finset.mem_sdiff.1 hqB
  obtain ⟨hqBF, hqBZ⟩ := Finset.mem_sdiff.1 hqB1
  rcases Finset.mem_union.1 hqBF with h | h
  · exact absurd h hqBZ
  · obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 h
    refine ⟨pB, qB, QB, m, fun hm' => ?_, hpB, hm, hQB, hbB⟩
    subst hm'
    exact hqBX hm

theorem K33Star.used_sub_support {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hK : K33Star G a Y y R) : k33Used a Y ⊆ S := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨u, -, v, hv, huv⟩ := hK.touch_Y_a 0 t
    rw [Finset.mem_singleton] at hv; subst hv
    exact hS _ _ huv.symm
  · obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 h
    exact connSet_sub_support hS (hK.Y_conn l) (hK.touch_Y_a l 0) hl

end Bridges

/-- **Wagner (b), structural core (PROVED).** For finite `V`, every nonplanar
edge-maximal `K₅`-minor-free graph on `S` without separations of order at most two
and without proper clique separations of order at most three has `V₈` as a minor. -/
theorem wagnerV8MinorCore [Finite V] : WagnerV8MinorCore V := by
  intro M S hM hns hsep hpl
  have hK33 : IsMinor K33 M := by
    by_contra h
    exact hpl ((isPlanar_iff_k5MinorFree_and_k33MinorFree M).2 ⟨hM.2.1, h⟩)
  obtain ⟨a, Y, y, R, hK⟩ := exists_k33Star_of_isMinor hK33
  have hFS := hK.used_sub_support hM.1
  by_cases hall : ∀ l t, R l t = ∅
  · exact (hK.false_of_arms_empty hM hns hsep hall).elim
  push Not at hall
  obtain ⟨l0, t0, r, hr⟩ := hall
  obtain ⟨pA, qA, QA, j, hj, hpA, hqA, hQA, hbA⟩ := hK.exists_A_bridge hM hns hsep hFS hr
  obtain ⟨pB, qB, QB, m, hm, hpB, hqB, hQB, hbB⟩ := hK.exists_B_bridge hM hns hsep hFS hr
  rcases isMinor_wagner_or_not_k5MinorFree_of_bridges hK (Ne.symm hj) (Ne.symm hm) hpA hqA
    hpB hqB hQA hQB hbA hbB with h | h
  · exact h
  · exact absurd hM.2.1 h

/-! ### Unconditional exports -/

/-- **Wagner (b), maximal core (PROVED, unconditional for finite `V`).** -/
theorem wagnerMaximalCore [Finite V] : WagnerMaximalCore V :=
  wagnerMaximalCore_of_v8MinorCore wagnerV8MinorCore

/-- **Wagner (b), prime core (PROVED, unconditional for finite `V`).** -/
theorem wagnerPrimeCore [Finite V] : WagnerPrimeCore V :=
  wagnerPrimeCore_of_v8MinorCore wagnerV8MinorCore

/-- **Wagner's structure theorem (PROVED, unconditional).** Every `K₅`-minor-free
graph on a finite vertex type is a spanning subgraph of a `K₅`-decomposable graph
(clique-sums of order at most three of planar pieces and copies of `V₈`). -/
theorem exists_k5Decomp_wagner [Fintype V] (G : SimpleGraph V) (hG : K5MinorFree G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ K5Decomp H Finset.univ :=
  exists_k5Decomp_of_v8MinorCore wagnerV8MinorCore G hG

/-- **Wagner's structure theorem, both directions (PROVED, unconditional).** -/
theorem k5MinorFree_iff_exists_k5Decomp_wagner [Fintype V] (G : SimpleGraph V) :
    K5MinorFree G ↔ ∃ H : SimpleGraph V, G ≤ H ∧ K5Decomp H Finset.univ :=
  k5MinorFree_iff_exists_k5Decomp_of_v8MinorCore wagnerV8MinorCore G

end LeanPool.K5MinorFreeChoosability
