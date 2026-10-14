/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Voigt.Forcing
public import LeanPool.K5MinorFreeChoosability.Voigt.PlaneMap

/-!
# Voigt's theorem: a planar graph that is not 4-choosable

M. Voigt, *List colourings of planar graphs*, Discrete Math. 120 (1993) 215–219, answering a
question of Erdős, Rubin and Taylor: there is a finite planar graph that is not 4-choosable.
Together with Thomassen's theorem (`choosableWith_five_of_isPlanar`) this shows that `5` is the
least `k` such that every finite planar graph is `k`-choosable.

Planarity is the existing `IsPlanar` (a genus-zero rotation system, `PlaneMap`), and
non-choosability is the negation of the existing `ChoosableWith`; neither is restated.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Voigt

/-- **Voigt (1993)**, concrete form: the explicit graph `voigtGraph` on `Fin 238` is planar
(with the explicit plane map `voigtPlaneMap`), every list `voigtList v` has four colours, and no
proper colouring of `voigtGraph` chooses its colours from these lists. -/
theorem voigt_theorem :
    IsPlanar voigtGraph ∧ (∀ v, (voigtList v).card = 4) ∧
      ¬ ListColourable voigtGraph voigtList :=
  ⟨isPlanar_voigtGraph, voigtList_card, voigt_not_listColourable⟩

/-- **Voigt (1993)**: the planar graph `voigtGraph` is not `4`-choosable. -/
theorem voigt_isPlanar_not_choosableWith_four :
    IsPlanar voigtGraph ∧ ¬ ChoosableWith voigtGraph ℕ 4 :=
  ⟨isPlanar_voigtGraph, voigt_not_choosableWith_four⟩

/-- **Voigt (1993)**: some finite planar graph is not `4`-choosable. -/
theorem exists_isPlanar_not_choosableWith_four :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), IsPlanar G ∧ ¬ ChoosableWith G ℕ 4 :=
  ⟨Fin 238, inferInstance, voigtGraph, voigt_isPlanar_not_choosableWith_four⟩

/-- **Voigt (1993)**, negative form: "every finite planar graph is 4-choosable" is false. -/
theorem not_forall_isPlanar_choosableWith_four :
    ¬ ∀ (V : Type) [Finite V] (G : SimpleGraph V), IsPlanar G → ChoosableWith G ℕ 4 :=
  fun h => voigt_not_choosableWith_four (h (Fin 238) voigtGraph isPlanar_voigtGraph)

end LeanPool.K5MinorFreeChoosability
