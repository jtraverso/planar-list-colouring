/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Voigt.RotationChecks
public import LeanPool.K5MinorFreeChoosability.Planar.Examples

/-!
# A plane embedding of Voigt's graph

`voigtPlaneMap : PlaneMap voigtGraph` is an embedding of `voigtGraph` in the rotation-system
model of `Planar/Embedding.lean`:

* `voigtRot` is a permutation of the darts (`rotFun_injective`, finite ⇒ bijective);
* it keeps the tail of every dart and all darts with a common tail form one of its cycles
  (`isRotationSystem_voigtRot`);
* every face is a triangle (`voigtRot_face_cube`), the graph is connected
  (`voigtGraph_connected`), and the Euler defect is zero (`eulerDefect_voigtRot`).

Euler's formula follows by counting as for the tetrahedron (`isPlanar_K4`): `V = 238` rotation
cycles, `E = 708`, `F ≥ 1416 / 3 = 472` faces and at most one component, so the defect
`|D| + 2 K - V - E - F` is at most `1416 + 2 - 238 - 708 - 472 = 0`; it is never negative
(`eulerDefect_nonneg`).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability.Voigt

open Equiv Equiv.Perm

/-! ### The rotation on darts -/

theorem mem_rotList_of_adj {v u : Fin 238} (h : voigtGraph.Adj v u) : (u : ℕ) ∈ rotList v :=
  (adj_iff_mem_rotList v u).1 h

/-- The successor of `u` around `v`, as a vertex. -/
def rotNextFin (v u : Fin 238) : Fin 238 := Fin.ofNat 238 (rotNext v u)

theorem rotNextFin_val {v u : Fin 238} (h : voigtGraph.Adj v u) :
    (rotNextFin v u : ℕ) = rotNext v u := by
  rw [rotNextFin, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt (rotList_lt v v.2 _ (rotNext_mem v v.2 u (mem_rotList_of_adj h)))

theorem adj_rotNextFin {v u : Fin 238} (h : voigtGraph.Adj v u) :
    voigtGraph.Adj v (rotNextFin v u) := by
  rw [adj_iff_mem_rotList, rotNextFin_val h]
  exact rotNext_mem v v.2 u (mem_rotList_of_adj h)

/-- The rotation as a function on darts: `v → u` goes to `v → rotNext v u`. -/
def rotFun (d : voigtGraph.Dart) : voigtGraph.Dart :=
  ⟨(d.fst, rotNextFin d.fst d.snd), adj_rotNextFin d.adj⟩

theorem rotFun_fst (d : voigtGraph.Dart) : (rotFun d).fst = d.fst := rfl

theorem rotFun_snd (d : voigtGraph.Dart) : ((rotFun d).snd : ℕ) = rotNext d.fst d.snd :=
  rotNextFin_val d.adj

theorem rotFun_injective : Function.Injective rotFun := by
  rintro ⟨⟨v, u⟩, h⟩ ⟨⟨v', u'⟩, h'⟩ he
  have h1 : v = v' := congrArg (fun d : voigtGraph.Dart => d.fst) he
  subst h1
  have h2 : rotNext v u = rotNext v u' := by
    have := congrArg (fun d : voigtGraph.Dart => (d.snd : ℕ)) he
    simpa only [rotFun, rotNextFin_val h, rotNextFin_val h'] using this
  have h3 : (u : ℕ) = u' := by
    rw [← rotPrev_rotNext v v.2 u (mem_rotList_of_adj h), h2,
      rotPrev_rotNext v v.2 u' (mem_rotList_of_adj h')]
  have : u = u' := Fin.ext h3
  subst this
  rfl

/-- **The rotation of Voigt's graph**, a permutation of its darts. -/
noncomputable def voigtRot : Perm voigtGraph.Dart :=
  Equiv.ofBijective rotFun (Finite.injective_iff_bijective.1 rotFun_injective)

theorem voigtRot_apply (d : voigtGraph.Dart) : voigtRot d = rotFun d := rfl

theorem voigtRot_pow_apply (k : ℕ) (d : voigtGraph.Dart) :
    ((voigtRot ^ k) d).fst = d.fst ∧ (((voigtRot ^ k) d).snd : ℕ) = (rotNext d.fst)^[k] d.snd := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, voigtRot_apply, rotFun_fst, rotFun_snd, ih.1, ih.2,
      Function.iterate_succ_apply']
    exact ⟨rfl, rfl⟩

theorem mem_iterList {f : ℕ → ℕ} {x u : ℕ} {n : ℕ} (h : u ∈ iterList f x n) :
    ∃ k, f^[k] x = u := by
  induction n generalizing x with
  | zero => simp [iterList] at h
  | succ n ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := ih h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, hk]⟩

/-- Every dart with tail `v` is reached from the dart `v → head` by iterating the rotation. -/
theorem exists_pow_of_head (d : voigtGraph.Dart) :
    ∃ (h : (rotList d.fst).headD 0 < 238) (hadj : voigtGraph.Adj d.fst ⟨_, h⟩) (k : ℕ),
      (voigtRot ^ k) ⟨(d.fst, ⟨_, h⟩), hadj⟩ = d := by
  have hu := mem_rotList_of_adj d.adj
  have hmem : (rotList d.fst).headD 0 ∈ rotList d.fst := by
    cases hl : rotList d.fst with
    | nil => rw [hl] at hu; simp at hu
    | cons a t => simp
  have hlt := rotList_lt _ d.fst.2 _ hmem
  have hadj : voigtGraph.Adj d.fst ⟨_, hlt⟩ := (adj_iff_mem_rotList _ _).2 hmem
  refine ⟨hlt, hadj, ?_⟩
  have hu' := hu
  rw [← rotList_orbit _ d.fst.2] at hu'
  obtain ⟨k, hk⟩ := mem_iterList hu'
  refine ⟨k, SimpleGraph.Dart.ext _ _ (Prod.ext ?_ (Fin.ext ?_))⟩
  · exact (voigtRot_pow_apply k _).1
  · rw [(voigtRot_pow_apply k _).2]
    exact hk

/-- The rotation of Voigt's graph is a rotation system. -/
theorem isRotationSystem_voigtRot : IsRotationSystem voigtGraph voigtRot := by
  refine ⟨fun d => rfl, fun d e hde => ?_⟩
  obtain ⟨h, hadj, k, hk⟩ := exists_pow_of_head d
  obtain ⟨h', hadj', k', hk'⟩ := exists_pow_of_head e
  have hd : SameCycle voigtRot ⟨(d.fst, ⟨_, h⟩), hadj⟩ d := ⟨k, by rw [zpow_natCast, hk]⟩
  have he : SameCycle voigtRot ⟨(e.fst, ⟨_, h'⟩), hadj'⟩ e := ⟨k', by rw [zpow_natCast, hk']⟩
  have heq : (⟨(d.fst, ⟨_, h⟩), hadj⟩ : voigtGraph.Dart) = ⟨(e.fst, ⟨_, h'⟩), hadj'⟩ := by
    apply SimpleGraph.Dart.ext
    simp only [hde]
  rw [heq] at hd
  exact hd.symm.trans he

/-! ### Faces are triangles -/

theorem rotFun_face_cube (a : voigtGraph.Dart) :
    rotFun (rotFun (rotFun a.symm).symm).symm = a := by
  obtain ⟨⟨v, u⟩, h⟩ := a
  obtain ⟨f1, f2⟩ := face_triangle v v.2 u (mem_rotList_of_adj h)
  apply SimpleGraph.Dart.ext
  have e1 := rotFun_snd (⟨(v, u), h⟩ : voigtGraph.Dart).symm
  set d1 := rotFun (⟨(v, u), h⟩ : voigtGraph.Dart).symm with hd1
  have e2 := rotFun_snd d1.symm
  set d2 := rotFun d1.symm with hd2
  have e3 := rotFun_snd d2.symm
  have d1f : d1.fst = u := rfl
  have d2f : d2.fst = d1.snd := rfl
  have hd2v : d2.snd = v := by
    apply Fin.ext
    rw [e2]
    change rotNext (d1.snd : ℕ) d1.fst = v
    rw [d1f, e1]
    exact f1
  refine Prod.ext hd2v (Fin.ext ?_)
  change ((rotFun d2.symm).snd : ℕ) = u
  rw [e3]
  change rotNext (d2.snd : ℕ) d2.fst = u
  rw [hd2v, d2f, e1]
  exact f2

theorem voigtRot_face_cube (a : voigtGraph.Dart) :
    ((voigtRot * dartSymm voigtGraph) ^ 3) a = a := by
  simpa [pow_succ, voigtRot_apply] using rotFun_face_cube a

/-! ### Connectivity -/

theorem reachable_zero : ∀ n, ∀ v : Fin 238, treeDepth v = n → voigtGraph.Reachable v 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    rcases tree_step v v.2 with h0 | ⟨hlt, hmem, hdep⟩
    · have : v = 0 := Fin.ext h0
      rw [this]
    · have hadj : voigtGraph.Adj v ⟨_, hlt⟩ := (adj_iff_mem_rotList _ _).2 hmem
      exact hadj.reachable.trans (ih _ (hv ▸ hdep) _ rfl)

theorem voigtGraph_connected : voigtGraph.Connected :=
  (SimpleGraph.connected_iff _).2
    ⟨fun u v => (reachable_zero _ u rfl).trans (reachable_zero _ v rfl).symm, ⟨0⟩⟩

/-! ### Euler's formula -/

theorem eulerDefect_voigtRot : eulerDefect voigtRot (dartSymm voigtGraph) = 0 := by
  refine le_antisymm ?_ (eulerDefect_nonneg _ _)
  have hn : Nat.card voigtGraph.Dart = 1416 := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.dart_card_eq_sum_degrees, sum_degrees]
  have hα := card_dart_eq_two_mul voigtGraph
  have hσ : cycleCount voigtRot = 238 := by
    rw [cycleCount_eq_card_nonisolated isRotationSystem_voigtRot,
      Nat.card_congr (Equiv.subtypeUnivEquiv exists_adj), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hK := numComponents_le_one_of_connected isRotationSystem_voigtRot voigtGraph_connected
  have hφ : Nat.card voigtGraph.Dart ≤ 3 * cycleCount (voigtRot * dartSymm voigtGraph) :=
    card_le_mul_numClasses _ 3 fun d =>
      card_sameCycle_le _ 3 (by norm_num) voigtRot_face_cube d
  unfold eulerDefect
  omega

/-- **The plane embedding of Voigt's graph.** -/
noncomputable def voigtPlaneMap : PlaneMap voigtGraph :=
  ⟨voigtRot, isRotationSystem_voigtRot, eulerDefect_voigtRot⟩

/-- Voigt's graph is planar. -/
theorem isPlanar_voigtGraph : IsPlanar voigtGraph := ⟨voigtPlaneMap⟩

end LeanPool.K5MinorFreeChoosability.Voigt
