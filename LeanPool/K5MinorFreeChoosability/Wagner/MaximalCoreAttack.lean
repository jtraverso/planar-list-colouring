/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerB
public import LeanPool.K5MinorFreeChoosability.Lemma5

/-!
# Local reductions for the unresolved maximal Wagner core

These lemmas do not assume `WagnerPrimeCore` or `WagnerMaximalCore`.
They isolate the degree-three case: in an edge-maximal `K₅`-minor-free graph
without proper clique separators of order at most three, a three-vertex
neighbourhood is independent and its Y–Δ completion has a `K₅` minor.
The classification of the resulting minor model is still required.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

/-- The separator exclusion appearing literally in `WagnerMaximalCore`. -/
def NoCliqueSepThree (M : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ A B : Finset V, A ∪ B = S → (A ∩ B).card ≤ 3 →
    (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v) →
    ¬ A ⊆ B → ¬ B ⊆ A →
    ¬ ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → M.Adj u v

/-- A side with at least two private vertices carries a rooted triangle
on a three-vertex separator. A failed rooted triangle would disconnect
the whole graph after deleting at most two vertices. -/
theorem rootedK3_of_three_separation {H : SimpleGraph V} {S A B : Finset V} {x y z : V}
    (hns : NoSmallSep H S) (hcov : A ∪ B = S)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v)
    (hK : A ∩ B = {x, y, z}) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hA : 2 ≤ (A \ B).card) (hB : ¬ B ⊆ A) : RootedK3 H A x y z := by
  classical
  have hAS : A ⊆ S := hcov ▸ Finset.subset_union_left
  have hBS : B ⊆ S := hcov ▸ Finset.subset_union_right
  have hroots : ({x, y, z} : Finset V) ⊆ A := by
    rw [← hK]
    exact Finset.inter_subset_left
  apply rootedK3_of_good (hroots (by simp)) (hroots (by simp))
    (hroots (by simp)) hxy hyz hxz
  intro u hu
  by_contra hbad
  obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne (by omega : 1 < (A \ B).card) u
  obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.mp hB
  let C := reachIn H (A.erase u) w
  let T := C ∩ ({x, y, z} : Finset V)
  let Z := insert u T
  have hCA : C ⊆ A.erase u := reachIn_sub _ _
  have hwC : w ∈ C := mem_reachIn_self (Finset.mem_erase.mpr ⟨hwu, (Finset.mem_sdiff.mp hw).1⟩)
  have hT : T.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    have hpC := (Finset.mem_inter.mp hp).1
    have hqC := (Finset.mem_inter.mp hq).1
    exact hbad ⟨p, (Finset.mem_inter.mp hp).2, q, (Finset.mem_inter.mp hq).2, hpq,
      (Finset.mem_erase.mp (hCA hpC)).1, (Finset.mem_erase.mp (hCA hqC)).1,
      ((reachIn_conn (Finset.mem_erase.mpr ⟨hwu, (Finset.mem_sdiff.mp hw).1⟩)).2
        p hpC q hqC).mono_set (Finset.coe_subset.mpr hCA)⟩
  have hZS : Z ⊆ S := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hAS hu
    · exact hAS (Finset.mem_of_mem_erase (hCA (Finset.mem_inter.mp hv).1))
  have hZ : Z.card ≤ 2 := (Finset.card_insert_le u T).trans (by omega)
  have hwZ : w ∉ Z := by
    intro hwZ
    rcases Finset.mem_insert.mp hwZ with he | ht
    · exact hwu he
    · have hwK := (Finset.mem_inter.mp ht).2
      rw [← hK] at hwK
      exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_inter.mp hwK).2
  have hbZ : b ∉ Z := by
    intro hbZ
    rcases Finset.mem_insert.mp hbZ with he | ht
    · exact hbA (he ▸ hu)
    · exact hbA (Finset.mem_of_mem_erase (hCA (Finset.mem_inter.mp ht).1))
  have hwSZ : w ∈ S \ Z := Finset.mem_sdiff.mpr ⟨hAS (Finset.mem_sdiff.mp hw).1, hwZ⟩
  have hbSZ : b ∈ S \ Z := Finset.mem_sdiff.mpr ⟨hBS hbB, hbZ⟩
  have hr := (hns.connSet_sdiff hZS hZ ⟨w, hwSZ⟩).2 w hwSZ b hbSZ
  have hbC : b ∉ C := fun hbC => hbA (Finset.mem_of_mem_erase (hCA hbC))
  obtain ⟨p, q, -, hpSZ, hpC, hqSZ, hqC, hpq⟩ := hr.exit hwC hbC
  have hqZ : q ∉ Z := (Finset.mem_sdiff.mp hqSZ).2
  have hqU : q ≠ u := fun he => hqZ (Finset.mem_insert.mpr (Or.inl he))
  by_cases hqA : q ∈ A
  · exact hqC (reachIn_closed hpC (Finset.mem_erase.mpr ⟨hqU, hqA⟩) hpq)
  · have hpA := Finset.mem_of_mem_erase (hCA hpC)
    have hpB : p ∉ B := by
      intro hpB
      have hpK : p ∈ ({x, y, z} : Finset V) := hK ▸ Finset.mem_inter.mpr ⟨hpA, hpB⟩
      have hpT : p ∈ T := Finset.mem_inter.mpr ⟨hpC, hpK⟩
      have hpZ : p ∈ Z := Finset.mem_insert_of_mem hpT
      exact (Finset.mem_sdiff.mp hpSZ).2 hpZ
    have hqB := (Finset.mem_union.mp (hcov.symm ▸ (Finset.mem_sdiff.mp hqSZ).1)).resolve_left hqA
    exact hnc p hpA hpB q hqB hqA hpq

/-- Convert the existing three-root API to the separator API, without
introducing a second representation of minor models. -/
theorem RootedK3.rootedClique {H : SimpleGraph V} {A : Finset V} {x y z : V}
    (h : RootedK3 H A x y z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    RootedClique H A {x, y, z} := by
  obtain ⟨X, Y, Z, hXA, hYA, hZA, hx, hy, hz, hcX, hcY, hcZ,
    hXY, hYZ, hXZ, htXY, htYZ, htXZ⟩ := h
  let R : V → Finset V := fun v => if v = x then X else if v = y then Y else Z
  have hRx : R x = X := by simp [R]
  have hRy : R y = Y := by simp [R, hxy.symm]
  have hRz : R z = Z := by simp [R, hxz.symm, hyz.symm]
  refine ⟨R, ?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · rw [hRx]
      refine ⟨hx, hXA, hcX, ?_⟩
      intro v hv hvK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvK
      rcases hvK with rfl | rfl | rfl
      · rfl
      · exact (Finset.disjoint_left.mp hXY hv hy).elim
      · exact (Finset.disjoint_left.mp hXZ hv hz).elim
    · rw [hRy]
      refine ⟨hy, hYA, hcY, ?_⟩
      intro v hv hvK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvK
      rcases hvK with rfl | rfl | rfl
      · exact (Finset.disjoint_left.mp hXY hx hv).elim
      · rfl
      · exact (Finset.disjoint_left.mp hYZ hv hz).elim
    · rw [hRz]
      refine ⟨hz, hZA, hcZ, ?_⟩
      intro v hv hvK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvK
      rcases hvK with rfl | rfl | rfl
      · exact (Finset.disjoint_left.mp hXZ hx hv).elim
      · exact (Finset.disjoint_left.mp hYZ hy hv).elim
      · rfl
  · intro k hk l hl hkl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
    rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl
    all_goals simp only [hRx, hRy, hRz]
    all_goals first
      | exact (hkl rfl).elim
      | exact ⟨hXY, htXY⟩
      | exact ⟨hXZ, htXZ⟩
      | exact ⟨hYZ, htYZ⟩
      | exact ⟨hXY.symm, Touch.symm htXY⟩
      | exact ⟨hXZ.symm, Touch.symm htXZ⟩
      | exact ⟨hYZ.symm, Touch.symm htYZ⟩

/-- A good separation contradicts the clique-separator exclusion, because
edge maximality forces its separator to be a clique. -/
theorem not_isGoodSep_of_maximal {M : SimpleGraph V} {S A B : Finset V}
    (hM : IsMaxK5Free M S) (hsep : NoCliqueSepThree M S) :
    ¬ IsGoodSep M S A B := by
  intro hg
  exact hsep A B hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1
    (isClique_of_isGoodSep hM hg)

/-- A three-separation with at least two private vertices on each side
is impossible in the maximal clique-separator-free core. -/
theorem no_three_separation_with_large_sides {M : SimpleGraph V} {S A B : Finset V}
    (hM : IsMaxK5Free M S) (hns : NoSmallSep M S) (hsep : NoCliqueSepThree M S)
    (hcov : A ∪ B = S) (hK : (A ∩ B).card = 3)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v)
    (hA : 2 ≤ (A \ B).card) (hB : 2 ≤ (B \ A).card) : False := by
  have hAB : ¬ A ⊆ B := by
    intro h
    have : A \ B = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr h
    rw [this, Finset.card_empty] at hA
    omega
  have hBA : ¬ B ⊆ A := by
    intro h
    have : B \ A = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr h
    rw [this, Finset.card_empty] at hB
    omega
  obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.mp hK
  have hRA := (rootedK3_of_three_separation hns hcov hnc hxyz hxy hyz hxz hA hBA).rootedClique
    hxy hxz hyz
  have hRB := (rootedK3_of_three_separation hns (by rwa [Finset.union_comm])
    (fun u hu huA v hv hvB huv => hnc v hv hvB u hu huA huv.symm)
    (by rwa [Finset.inter_comm]) hxy hyz hxz hB hAB).rootedClique hxy hxz hyz
  apply not_isGoodSep_of_maximal hM hsep
  apply isGoodSep_of_rootedClique hcov (by omega) hnc hAB hBA
  · rwa [hxyz]
  · rwa [hxyz]
  · exact hM.2.1

/-- Every proper separation of order at most three in the maximal core
has order exactly three, and one of its private sides is a singleton.
Thus the nontrivial two-sided separator case is discharged. -/
theorem three_separation_has_singleton_side {M : SimpleGraph V} {S A B : Finset V}
    (hM : IsMaxK5Free M S) (hns : NoSmallSep M S) (hsep : NoCliqueSepThree M S)
    (hcov : A ∪ B = S) (hK : (A ∩ B).card ≤ 3)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v)
    (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) :
    (A ∩ B).card = 3 ∧ ((A \ B).card = 1 ∨ (B \ A).card = 1) := by
  have hK3 : (A ∩ B).card = 3 := by
    by_contra hne
    rcases hns A B hcov (by omega) hnc with h | h
    · exact hAB h
    · exact hBA h
  have hApos : 0 < (A \ B).card := by
    obtain ⟨a, ha, hb⟩ := Finset.not_subset.mp hAB
    exact Finset.card_pos.mpr ⟨a, Finset.mem_sdiff.mpr ⟨ha, hb⟩⟩
  have hBpos : 0 < (B \ A).card := by
    obtain ⟨b, hb, ha⟩ := Finset.not_subset.mp hBA
    exact Finset.card_pos.mpr ⟨b, Finset.mem_sdiff.mpr ⟨hb, ha⟩⟩
  refine ⟨hK3, ?_⟩
  by_contra h
  have hA : 2 ≤ (A \ B).card := by omega
  have hB : 2 ≤ (B \ A).card := by omega
  exact no_three_separation_with_large_sides hM hns hsep hcov hK3 hnc hA hB

/-- The centre of a singleton private side has no neighbours outside
the separator; support is essential because the ambient type may be
larger than `S`. -/
theorem singleton_side_neighbourhood {M : SimpleGraph V} {S A B : Finset V} {c : V}
    (hS : ∀ u v, M.Adj u v → u ∈ S) (hcov : A ∪ B = S)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v)
    (hprivate : A \ B = {c}) :
    c ∈ S ∧ c ∉ A ∩ B ∧ ∀ v, M.Adj c v → v ∈ A ∩ B := by
  have hc : c ∈ A \ B := hprivate.symm ▸ Finset.mem_singleton_self c
  obtain ⟨hcA, hcB⟩ := Finset.mem_sdiff.mp hc
  refine ⟨hcov ▸ Finset.mem_union_left B hcA,
    fun h => hcB (Finset.mem_inter.mp h).2, ?_⟩
  intro v hcv
  have hvS : v ∈ S := hS v c hcv.symm
  have hvA : v ∈ A := by
    by_contra hvA
    have hvB := (Finset.mem_union.mp (hcov.symm ▸ hvS)).resolve_left hvA
    exact hnc c hcA hcB v hvB hvA hcv
  have hvB : v ∈ B := by
    by_contra hvB
    have hvC : v = c := by
      have hv : v ∈ A \ B := Finset.mem_sdiff.mpr ⟨hvA, hvB⟩
      rw [hprivate] at hv
      exact Finset.mem_singleton.mp hv
    exact hcv.ne hvC.symm
  exact Finset.mem_inter.mpr ⟨hvA, hvB⟩

/-- Three-connectivity forces a vertex to have at least three possible
neighbours when the support has at least four vertices. No finite
ambient type or decidability of adjacency is needed. -/
theorem NoSmallSep.three_le_neighbour_bound {M : SimpleGraph V} {S K : Finset V} {c : V}
    (hns : NoSmallSep M S) (hcS : c ∈ S) (hKS : K ⊆ S) (hcK : c ∉ K)
    (hS : 4 ≤ S.card) (hc : ∀ v, M.Adj c v → v ∈ K) : 3 ≤ K.card := by
  by_contra hcard
  have hK2 : K.card ≤ 2 := by omega
  have hinter : insert c K ∩ S.erase c = K := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | hv, hne, -⟩
      · exact (hne rfl).elim
      · exact hv
    · intro hv
      exact ⟨Or.inr hv, fun he => hcK (he ▸ hv), hKS hv⟩
  have hcov : insert c K ∪ S.erase c = S := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((rfl | hv) | ⟨-, hv⟩)
      · exact hcS
      · exact hKS hv
      · exact hv
    · intro hv
      by_cases he : v = c
      · exact Or.inl (Or.inl he)
      · exact Or.inr ⟨he, hv⟩
  have hnc : ∀ u ∈ insert c K, u ∉ S.erase c →
      ∀ v ∈ S.erase c, v ∉ insert c K → ¬ M.Adj u v := by
    intro u hu huB v _ hvA huv
    rcases Finset.mem_insert.mp hu with rfl | huK
    · exact hvA (Finset.mem_insert_of_mem (hc v huv))
    · exact huB (Finset.mem_erase.mpr ⟨fun he => hcK (he ▸ huK), hKS huK⟩)
  rcases hns _ _ hcov (by rwa [hinter]) hnc with hAB | hBA
  · exact (Finset.mem_erase.mp (hAB (Finset.mem_insert_self c K))).1 rfl
  · have hsub : S ⊆ insert c K := by
      intro v hv
      by_cases he : v = c
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact hBA (Finset.mem_erase.mpr ⟨he, hv⟩)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_insert_le c K)
    omega

/-- A three-element neighbour bound in a prime piece is the exact
neighbourhood; dropping one purported neighbour would give a two-cut. -/
theorem NoSmallSep.adj_of_mem_three_neighbour_bound {M : SimpleGraph V}
    {S K : Finset V} {c : V} (hns : NoSmallSep M S) (hcS : c ∈ S)
    (hKS : K ⊆ S) (hcK : c ∉ K) (hK : K.card = 3) (hS : 4 ≤ S.card)
    (hc : ∀ v, M.Adj c v → v ∈ K) : ∀ v ∈ K, M.Adj c v := by
  intro v hv
  by_contra hnadj
  have hsmall := hns.three_le_neighbour_bound hcS
    ((Finset.erase_subset v K).trans hKS)
    (fun h => hcK (Finset.mem_of_mem_erase h)) hS (fun w hw =>
      Finset.mem_erase.mpr ⟨fun he => hnadj (he ▸ hw), hc w hw⟩)
  have hcard : (K.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, hK]
  omega

/-- Completing a three-vertex neighbourhood after deleting its centre
must create a `K₅` minor in the maximal, clique-separator-free case. -/
theorem not_k5MinorFree_yDelta_of_maximal {M : SimpleGraph V} {S K : Finset V} {c : V}
    (hM : IsMaxK5Free M S) (hsep : NoCliqueSepThree M S)
    (hcS : c ∈ S) (hKS : K ⊆ S) (hcK : c ∉ K) (hK : K.card = 3)
    (hS : 5 ≤ S.card) (hc : ∀ v, M.Adj c v → v ∈ K) :
    ¬ K5MinorFree (pieceGraph M (S.erase c) K) := by
  intro h5
  exact not_isGoodSep_of_maximal hM hsep
    (isGoodSep_of_yDelta hcS hKS hcK hK hS hc h5)

/-- The previous obstruction yields an actual branch-set model, rather
than an assumption about the missing Wagner classification. -/
theorem exists_yDelta_k5Model_of_maximal {M : SimpleGraph V} {S K : Finset V} {c : V}
    (hM : IsMaxK5Free M S) (hsep : NoCliqueSepThree M S)
    (hcS : c ∈ S) (hKS : K ⊆ S) (hcK : c ∉ K) (hK : K.card = 3)
    (hS : 5 ≤ S.card) (hc : ∀ v, M.Adj c v → v ∈ K) :
    Nonempty (CliqueMinorModel (pieceGraph M (S.erase c) K) 5) := by
  classical
  by_contra h
  exact not_k5MinorFree_yDelta_of_maximal hM hsep hcS hKS hcK hK hS hc h

/-- Any proper separator of order at most three in the maximal core
produces a singleton centre and a Y–Δ `K₅` obstruction. This is a
proved reduction of the separator branch, not the Wagner classification. -/
theorem yDelta_obstruction_of_small_separation {M : SimpleGraph V} {S A B : Finset V}
    (hM : IsMaxK5Free M S) (hns : NoSmallSep M S) (hsep : NoCliqueSepThree M S)
    (hS : 5 ≤ S.card) (hcov : A ∪ B = S) (hK : (A ∩ B).card ≤ 3)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v)
    (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) :
    ∃ c K, c ∈ S ∧ K ⊆ S ∧ c ∉ K ∧ K.card = 3 ∧
      (∀ v, M.Adj c v → v ∈ K) ∧
      Nonempty (CliqueMinorModel (pieceGraph M (S.erase c) K) 5) := by
  have step : ∀ A B : Finset V, A ∪ B = S →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v) →
      (A ∩ B).card = 3 → (A \ B).card = 1 →
      ∃ c K, c ∈ S ∧ K ⊆ S ∧ c ∉ K ∧ K.card = 3 ∧
        (∀ v, M.Adj c v → v ∈ K) ∧
        Nonempty (CliqueMinorModel (pieceGraph M (S.erase c) K) 5) := by
    intro A B hcov hnc hK hsingle
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hsingle
    obtain ⟨hcS, hcK, hbound⟩ := singleton_side_neighbourhood hM.1 hcov hnc hc
    have hKS : A ∩ B ⊆ S := fun v hv => hcov ▸
      Finset.mem_union_left B (Finset.mem_inter.mp hv).1
    exact ⟨c, A ∩ B, hcS, hKS, hcK, hK, hbound,
      exists_yDelta_k5Model_of_maximal hM hsep hcS hKS hcK hK hS hbound⟩
  obtain ⟨hK3, hsingle | hsingle⟩ :=
    three_separation_has_singleton_side hM hns hsep hcov hK hnc hAB hBA
  · exact step A B hcov hnc hK3 hsingle
  · exact step B A (by rwa [Finset.union_comm])
      (fun u hu huA v hv hvB huv => hnc v hv hvB u hu huA huv.symm)
      (by rwa [Finset.inter_comm]) hsingle

/-- The minimum-degree-at-least-four branch has no proper separations
of order at most three. The degree hypothesis is phrased as a bound on
finite neighbour containers to avoid extra decidability assumptions. -/
theorem no_three_separation_of_min_degree_four {M : SimpleGraph V} {S : Finset V}
    (hM : IsMaxK5Free M S) (hns : NoSmallSep M S) (hsep : NoCliqueSepThree M S)
    (hS : 5 ≤ S.card)
    (hdegree : ∀ c ∈ S, ∀ K : Finset V, K ⊆ S → c ∉ K →
      (∀ v, M.Adj c v → v ∈ K) → 4 ≤ K.card) :
    ∀ A B : Finset V, A ∪ B = S → (A ∩ B).card ≤ 3 →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v) → A ⊆ B ∨ B ⊆ A := by
  intro A B hcov hK hnc
  by_contra h
  have hAB : ¬ A ⊆ B := fun hAB => h (Or.inl hAB)
  have hBA : ¬ B ⊆ A := fun hBA => h (Or.inr hBA)
  obtain ⟨c, K, hcS, hKS, hcK, hK3, hbound, -⟩ :=
    yDelta_obstruction_of_small_separation hM hns hsep hS hcov hK hnc hAB hBA
  have := hdegree c hcS K hKS hcK hbound
  omega

/-- If all three members of the neighbourhood really are adjacent to
the centre, no two of them can be adjacent to one another. Otherwise
contracting the centre to the third neighbour realizes the Y–Δ graph
as a minor, contradicting the obstruction above. -/
theorem independent_neighbourhood_of_maximal {M : SimpleGraph V} {S K : Finset V} {c : V}
    (hM : IsMaxK5Free M S) (hsep : NoCliqueSepThree M S)
    (hcS : c ∈ S) (hKS : K ⊆ S) (hcK : c ∉ K) (hK : K.card = 3)
    (hS : 5 ≤ S.card) (hc : ∀ v, M.Adj c v → v ∈ K)
    (hback : ∀ v ∈ K, M.Adj c v) :
    ∀ u ∈ K, ∀ v ∈ K, ¬ M.Adj u v := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hK
  have hcx := hback x (by simp)
  have hcy := hback y (by simp)
  have hcz := hback z (by simp)
  have hbad := not_k5MinorFree_yDelta_of_maximal hM hsep hcS hKS hcK hK hS hc
  have hxy' : ¬ M.Adj x y := by
    intro h
    apply hbad
    have hp := k5MinorFree_pieceGraph_of_triangle_edge
      (A := S.erase c) (by simp) hxz.symm hyz.symm hxy
      hcz hcx hcy h hM.2.1
    have hset : ({z, x, y} : Finset V) = {x, y, z} := by
      ext t
      simp [or_comm, or_left_comm]
    rwa [hset] at hp
  have hxz' : ¬ M.Adj x z := by
    intro h
    apply hbad
    have hp := k5MinorFree_pieceGraph_of_triangle_edge
      (A := S.erase c) (by simp) hxy.symm hyz hxz
      hcy hcx hcz h hM.2.1
    have hset : ({y, x, z} : Finset V) = {x, y, z} := by
      ext t
      simp [or_left_comm]
    rwa [hset] at hp
  have hyz' : ¬ M.Adj y z := by
    intro h
    exact hbad (k5MinorFree_pieceGraph_of_triangle_edge
      (A := S.erase c) (by simp) hxy hxz hyz hcx hcy hcz h hM.2.1)
  intro u hu v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  all_goals first
    | exact fun h => h.ne rfl
    | exact hxy'
    | exact hxz'
    | exact hyz'
    | exact fun h => hxy' h.symm
    | exact fun h => hxz' h.symm
    | exact fun h => hyz' h.symm

end LeanPool.K5MinorFreeChoosability
