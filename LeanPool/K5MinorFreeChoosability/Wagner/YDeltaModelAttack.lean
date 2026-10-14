/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.MaximalCoreAttack

/-!
# Branch-set obstruction after a Y–Δ completion

These lemmas analyse actual minor models, without assuming Wagner's maximal-core
classification. A model whose roots are concentrated in one branch, apart from
one possible exceptional root, lifts back through the deleted centre.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A connected branch containing at most one completed root was already
connected before completing the roots to a clique. -/
theorem connSet_pieceGraph_of_one_root {H : SimpleGraph V} {A K B : Finset V}
    (hB : ConnSet (pieceGraph H A K) ↑B)
    (hone : ∀ u ∈ B, ∀ v ∈ B, u ∈ K → v ∈ K → u = v) :
    ConnSet H ↑B := by
  refine ⟨hB.1, fun a ha b hb => ?_⟩
  exact RIn.map id (fun u v huv hu hv => by
    rcases huv.2.2 with hadj | ⟨huK, hvK, hne⟩
    · exact RIn.single hadj hu hv
    · exact (hne (hone u hu v hv huK hvK)).elim) (hB.2 a ha b hb)

omit [DecidableEq V] in
/-- Replacing each completed-root edge by a two-edge walk through `c`
restores reachability inside any set containing the original branch and `c`. -/
theorem rin_pieceGraph_through_centre {H : SimpleGraph V} {A K B D : Finset V}
    {c a b : V} (hc : c ∈ D) (hBD : B ⊆ D)
    (hback : ∀ u ∈ K, H.Adj c u) (hr : RIn (pieceGraph H A K) ↑B a b) :
    RIn H ↑D a b := by
  exact RIn.map id (fun u v huv hu hv => by
    rcases huv.2.2 with hadj | ⟨huK, hvK, -⟩
    · exact RIn.single hadj (hBD hu) (hBD hv)
    · exact (RIn.single (hback u huK).symm (hBD hu) hc).trans
        (RIn.single (hback v hvK) hc (hBD hv))) hr

omit [DecidableEq V] in
/-- If all roots appearing outside one selected branch coincide with `r`,
the completed clique model lifts to the original graph. Unused roots are
absorbed into the selected branch; this is essential for the coverage case. -/
theorem CliqueMinorModel.lift_yDelta_concentrated {H : SimpleGraph V} {A K : Finset V}
    {c r : V} {k : ℕ} (M : CliqueMinorModel (pieceGraph H A K) k)
    (hk : 2 ≤ k) (hcA : c ∉ A) (hback : ∀ u ∈ K, H.Adj c u)
    (i : Fin k) (hanchor : ∃ u ∈ K, u ∈ M.branch i)
    (hother : ∀ j, j ≠ i → ∀ u ∈ K, u ∈ M.branch j → u = r) :
    Nonempty (CliqueMinorModel H k) := by
  classical
  let D := insert c (M.branch i ∪ K.erase r)
  have hmem : ∀ j, ∀ u ∈ M.branch j, u ∈ A :=
    fun j u hu => M.mem_of_edges hk ↑A (fun _ _ h => h.1) j hu
  have hcnot : ∀ j, c ∉ M.branch j := fun j h => hcA (hmem j c h)
  have hBD : M.branch i ⊆ D := fun _ h =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
  have hcD : c ∈ D := Finset.mem_insert_self _ _
  have hconnD : ConnSet H ↑D := by
    obtain ⟨u, huK, huB⟩ := hanchor
    have hcu : RIn H ↑D c u := RIn.single (hback u huK) hcD (hBD huB)
    have hreach : ∀ v ∈ D, RIn H ↑D c v := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact RIn.refl _
      rcases Finset.mem_union.mp hv with hvB | hvK
      · exact hcu.trans (rin_pieceGraph_through_centre hcD hBD
          hback ((M.connSet i).2 u huB v hvB))
      · exact RIn.single (hback v (Finset.mem_of_mem_erase hvK)) hcD
          (Finset.mem_insert_of_mem (Finset.mem_union_right _ hvK))
    exact ⟨⟨c, hcD⟩, fun x hx y hy => (hreach x hx).symm.trans (hreach y hy)⟩
  have hdisj : ∀ j, j ≠ i → Disjoint D (M.branch j) := by
    intro j hji
    rw [Finset.disjoint_left]
    intro u hu huj
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hcnot j huj
    rcases Finset.mem_union.mp hu with hui | huK
    · exact Finset.disjoint_left.mp (M.branch_disjoint i j hji.symm) hui huj
    · exact (Finset.mem_erase.mp huK).1
        (hother j hji u (Finset.mem_of_mem_erase huK) huj)
  let branch := fun j => if j = i then D else M.branch j
  have hsub : ∀ j, M.branch j ⊆ branch j := by
    intro j
    by_cases hji : j = i
    · subst j; simpa [branch] using hBD
    · simp [branch, hji]
  refine ⟨CliqueMinorModel.ofConnSet branch (fun j => ?_) (fun j l hjl => ?_)
    (fun j l hjl => ?_)⟩
  · by_cases hji : j = i
    · simpa [branch, hji] using hconnD
    · simp only [branch, hji, ite_false]
      exact connSet_pieceGraph_of_one_root (M.connSet j) (fun u hu v hv huK hvK =>
        (hother j hji u huK hu).trans (hother j hji v hvK hv).symm)
  · by_cases hji : j = i <;> by_cases hli : l = i
    · exact (hjl (hji.trans hli.symm)).elim
    · subst j; simpa [branch, hli] using hdisj l hli
    · subst l; simpa [branch, hji] using (hdisj j hji).symm
    · simpa [branch, hji, hli] using M.branch_disjoint j l hjl
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent j l hjl
    rcases huv.2.2 with hadj | ⟨huK, hvK, hne⟩
    · exact ⟨u, hsub j hu, v, hsub l hv, hadj⟩
    · by_cases hji : j = i
      · exact ⟨c, by simp [branch, hji, hcD], v, hsub l hv, hback v hvK⟩
      · by_cases hli : l = i
        · exact ⟨u, hsub j hu, c, by simp [branch, hli, hcD], (hback u huK).symm⟩
        · exact (hne ((hother j hji u huK hu).trans
            (hother l hli v hvK hv).symm)).elim

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation of the 216 root assignments needs a deeper recursion
-- allowance. The heartbeat cap remains finite; no external evaluator is used.
/-- Exhaustive kernel-checked occupancy lemma: either no root is used,
all three roots are used in distinct branches, or a concentrated lift applies.
This finite statement has no graph-theoretic hypotheses. -/
theorem three_root_occupancy_trichotomy (f : Fin 3 → Option (Fin 5)) :
    (∀ u, f u = none) ∨
    ((∀ u, ∃ i, f u = some i) ∧ Function.Injective f) ∨
    (∃ i r, (∃ u, f u = some i) ∧
      ∀ u j, f u = some j → j ≠ i → u = r) := by
  have all_cases : ∀ f : Fin 3 → Option (Fin 5),
      (∀ u, f u = none) ∨
      ((∀ u, ∃ i, f u = some i) ∧ Function.Injective f) ∨
      (∃ i r, (∃ u, f u = some i) ∧
        ∀ u j, f u = some j → j ≠ i → u = r) := by decide
  exact all_cases f

/-- In a `K₅`-free original graph, every `K₅` model of the Y–Δ completion
uses all three roots, and places them in three distinct branches. -/
theorem yDelta_k5Model_roots_distinct {H : SimpleGraph V} {A K : Finset V} {c : V}
    (h5 : K5MinorFree H) (hcA : c ∉ A) (hback : ∀ u ∈ K, H.Adj c u)
    (roots : Fin 3 → V) (hK : K = Finset.univ.image roots)
    (M : CliqueMinorModel (pieceGraph H A K) 5) :
    ∃ idx : Fin 3 → Fin 5, Function.Injective idx ∧
      ∀ t, roots t ∈ M.branch (idx t) := by
  classical
  have hroot : ∀ t, roots t ∈ K := fun t => by
    rw [hK]; exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
  let f : Fin 3 → Option (Fin 5) := fun t =>
    if h : ∃ j, roots t ∈ M.branch j then some (Classical.choose h) else none
  have hf : ∀ t j, f t = some j ↔ roots t ∈ M.branch j := by
    intro t j
    by_cases h : ∃ l, roots t ∈ M.branch l
    · simp only [f, dite_eq_left h, Option.some.injEq]
      constructor
      · intro he; subst j; exact Classical.choose_spec h
      · intro hj
        by_contra hne
        exact Finset.disjoint_left.mp (M.branch_disjoint _ _ hne)
          (Classical.choose_spec h) hj
    · simp only [f, dite_eq_right h]
      constructor
      · intro he; simp at he
      · intro hj; exact (h ⟨j, hj⟩).elim
  obtain hnone | hdistinct | hconcentrated := three_root_occupancy_trichotomy f
  · have habs : ∀ j, ∀ u ∈ K, u ∉ M.branch j := by
      intro j u hu huj
      rw [hK] at hu
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hu
      have he := (hf t j).mpr huj
      rw [hnone t] at he
      simp at he
    apply (h5 ?_).elim
    exact ⟨CliqueMinorModel.ofConnSet M.branch
      (fun j => connSet_pieceGraph_of_one_root (M.connSet j)
        (fun u hu _ _ huK _ => (habs j u huK hu).elim))
      M.branch_disjoint (fun i j hij => by
        obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
        rcases huv.2.2 with hadj | ⟨huK, -, -⟩
        · exact ⟨u, hu, v, hv, hadj⟩
        · exact (habs i u huK hu).elim)⟩
  · let idx : Fin 3 → Fin 5 := fun t => Classical.choose (hdistinct.1 t)
    have hidx : ∀ t, f t = some (idx t) := fun t => Classical.choose_spec (hdistinct.1 t)
    exact ⟨idx, fun u v huv => hdistinct.2 ((hidx u).trans
      ((congrArg some huv).trans (hidx v).symm)), fun t => (hf t (idx t)).mp (hidx t)⟩
  · obtain ⟨i, r, ⟨t, ht⟩, hother⟩ := hconcentrated
    apply (h5 (M.lift_yDelta_concentrated (r := roots r) (by norm_num) hcA hback i
      ⟨roots t, hroot t, (hf t i).mp ht⟩ ?_)).elim
    intro j hji u huK huj
    rw [hK] at huK
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp huK
    exact congrArg roots (hother s j ((hf s j).mpr huj) hji)

/-- A `K₅` obstruction to a Y–Δ completion supplies a physical `K₃,₃`
model before the completion. The three rooted branches are on one side;
the deleted centre and the two unrooted branches are on the other. -/
theorem k33Minor_of_yDelta_k5Model {H : SimpleGraph V} {A K : Finset V} {c : V}
    (h5 : K5MinorFree H) (hcA : c ∉ A) (hback : ∀ u ∈ K, H.Adj c u)
    (roots : Fin 3 → V) (hK : K = Finset.univ.image roots)
    (M : CliqueMinorModel (pieceGraph H A K) 5) : IsMinor K33 H := by
  classical
  obtain ⟨idx, hinj, hroot⟩ := yDelta_k5Model_roots_distinct h5 hcA hback roots hK M
  have hown : ∀ t j, roots t ∈ M.branch j → idx t = j := by
    intro t j hj
    by_contra hne
    exact Finset.disjoint_left.mp (M.branch_disjoint _ _ hne) (hroot t) hj
  have hconn : ∀ j, ConnSet H ↑(M.branch j) := by
    intro j
    apply connSet_pieceGraph_of_one_root (M.connSet j)
    intro u hu v hv huK hvK
    rw [hK] at huK hvK
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp huK
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hvK
    exact congrArg roots (hinj ((hown t j hu).trans (hown s j hv).symm))
  let unused := Finset.univ \ Finset.univ.image idx
  have hcard : unused.card = 2 := by
    have himage : (Finset.univ.image idx).card = 3 := by
      rw [Finset.card_image_of_injective _ hinj]; simp
    change (Finset.univ \ Finset.univ.image idx).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), himage]
    decide
  obtain ⟨d, hd, e, he, hde⟩ := Finset.one_lt_card.mp (show 1 < unused.card by omega)
  have haway : ∀ j ∈ unused, ∀ t, j ≠ idx t := by
    intro j hj t hje
    exact (Finset.mem_sdiff.mp hj).2
      (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hje.symm⟩)
  have htouch : ∀ j ∈ unused, ∀ t, Touch H (M.branch j) (M.branch (idx t)) := by
    intro j hj t
    obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent j (idx t) (haway j hj t)
    rcases huv.2.2 with hadj | ⟨huK, -, -⟩
    · exact ⟨u, hu, v, hv, hadj⟩
    · rw [hK] at huK
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp huK
      exact (haway j hj s (hown s j hu).symm).elim
  have hcdisj : ∀ j, Disjoint ({c} : Finset V) (M.branch j) := by
    intro j
    rw [Finset.disjoint_singleton_left]
    exact fun hc => hcA (M.mem_of_edges (by norm_num) ↑A (fun _ _ h => h.1) j hc)
  have hctouch : ∀ t, Touch H {c} (M.branch (idx t)) := by
    intro t
    refine ⟨c, Finset.mem_singleton_self _, roots t, hroot t, hback _ ?_⟩
    rw [hK]; exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hij : ∀ t s : Fin 3, t ≠ s → Disjoint (M.branch (idx t)) (M.branch (idx s)) :=
    fun t s hts => M.branch_disjoint _ _ (fun h => hts (hinj h))
  exact isMinor_K33_of_six (by simpa using connSet_singleton H c) (hconn d) (hconn e)
    (hconn (idx 0)) (hconn (idx 1)) (hconn (idx 2))
    (hcdisj d) (hcdisj e) (M.branch_disjoint d e hde)
    (hij 0 1 (by decide)) (hij 0 2 (by decide)) (hij 1 2 (by decide))
    (hcdisj (idx 0)) (hcdisj (idx 1)) (hcdisj (idx 2))
    (M.branch_disjoint _ _ (haway d hd 0))
    (M.branch_disjoint _ _ (haway d hd 1))
    (M.branch_disjoint _ _ (haway d hd 2))
    (M.branch_disjoint _ _ (haway e he 0))
    (M.branch_disjoint _ _ (haway e he 1))
    (M.branch_disjoint _ _ (haway e he 2))
    (hctouch 0) (hctouch 1) (hctouch 2)
    (htouch d hd 0) (htouch d hd 1) (htouch d hd 2)
    (htouch e he 0) (htouch e he 1) (htouch e he 2)

end LeanPool.K5MinorFreeChoosability
