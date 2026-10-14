/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Voigt.Graph
public import LeanPool.K5MinorFreeChoosability.Voigt.RotationData
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Kernel-checked facts about the generated rotation data

The rotation of Voigt's graph on vertex numbers, and the finite facts about it used to build
`voigtPlaneMap` (`Voigt/PlaneMap.lean`).  The successor of the dart `v → u` is
`v → rotNext v u`, where `rotNext v u` is the entry following `u` (cyclically) in the list
`rotList v` of `v` taken from the generated `voigtRotData`.  The following facts are checked by
kernel `decide` (`decide +kernel`, no `native_decide`):

* `adj_iff_mem_rotList`: the list of `v` contains exactly the neighbours of `v` in
  `voigtGraph`, and `rotList_lt`: it contains only vertex numbers;
* `rotNext_mem`, `rotPrev_rotNext`: `rotNext v` maps the list of `v` into itself and is undone
  by `rotPrev v`, so the rotation is a well-defined injective (hence bijective) map on darts;
* `rotList_orbit`: iterating `rotNext v` from the head of the list of `v` lists all of it, so
  all darts with tail `v` form one cycle;
* `face_triangle`: every face of the rotation system is a triangle;
* `tree_step`: a spanning tree, so the graph is connected;
* `exists_adj`: no vertex is isolated;
* `sum_degrees`: the graph has `1416` darts (`708` edges).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability.Voigt

open Equiv Equiv.Perm

/-! ### The rotation on vertex numbers -/

/-- The cyclic neighbour order of vertex `v`. -/
def rotList (v : ℕ) : List ℕ := voigtRotData.getD v []

/-- The entry after `u` in `l`, cyclically returning to `first` after the last entry. -/
def nextAux (first : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => first
  | [_], _ => first
  | a :: b :: t, u => if a = u then b else nextAux first (b :: t) u

/-- The neighbour of `v` following `u` counterclockwise. -/
def rotNext (v u : ℕ) : ℕ :=
  match rotList v with
  | [] => u
  | f :: t => nextAux f (f :: t) u

/-- The neighbour of `v` preceding `u`, i.e. the inverse of `rotNext v`. -/
def rotPrev (v u : ℕ) : ℕ :=
  match (rotList v).reverse with
  | [] => u
  | f :: t => nextAux f (f :: t) u

/-- The list `[x, f x, …, f^[n-1] x]`. -/
def iterList (f : ℕ → ℕ) (x : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => x :: iterList f (f x) n

/-- Parent of `v` in the spanning tree. -/
def treeParent (v : ℕ) : ℕ := voigtParentData.getD v 0

/-- Depth of `v` in the spanning tree. -/
def treeDepth (v : ℕ) : ℕ := voigtDepthData.getD v 0

/-! ### Finite facts, checked by the kernel -/

theorem adj_iff_mem_rotList : ∀ v u : Fin 238, voigtGraph.Adj v u ↔ (u : ℕ) ∈ rotList v := by
  decide +kernel

theorem rotList_lt : ∀ v < 238, ∀ u ∈ rotList v, u < 238 := by
  decide +kernel

theorem rotNext_mem : ∀ v < 238, ∀ u ∈ rotList v, rotNext v u ∈ rotList v := by
  decide +kernel

theorem rotPrev_rotNext : ∀ v < 238, ∀ u ∈ rotList v, rotPrev v (rotNext v u) = u := by
  decide +kernel

theorem rotList_orbit : ∀ v < 238,
    iterList (rotNext v) ((rotList v).headD 0) (rotList v).length = rotList v := by
  decide +kernel

theorem face_triangle : ∀ v < 238, ∀ u ∈ rotList v,
    rotNext (rotNext u v) u = v ∧ rotNext v (rotNext u v) = u := by
  decide +kernel

theorem tree_step : ∀ v < 238, v = 0 ∨
    (treeParent v < 238 ∧ treeParent v ∈ rotList v ∧
      treeDepth (treeParent v) < treeDepth v) := by
  decide +kernel

theorem exists_adj : ∀ v : Fin 238, ∃ u, voigtGraph.Adj v u := by
  decide +kernel

theorem sum_degrees : ∑ v, voigtGraph.degree v = 1416 := by
  decide +kernel

end LeanPool.K5MinorFreeChoosability.Voigt
