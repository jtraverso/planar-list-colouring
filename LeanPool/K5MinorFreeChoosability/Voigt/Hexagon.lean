/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

/-!
# The finite forcing step in Voigt's construction

The three `r` vertices form the inner triangle. The alternating `s` vertices
form the surrounding hexagon. Every proper colouring with three colours has
one designated hexagon edge using colours zero and one. This is the local
combinatorial step, not yet the 238-vertex counterexample or its planar map.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

/-- The inner triangle is essential; a hexagon alone can alternate two colours. -/
theorem voigt_hexagon_forcing :
    ∀ r₁ r₂ r₃ s₁ s₂ s₃ : Fin 3,
      r₁ ≠ r₂ → r₂ ≠ r₃ → r₃ ≠ r₁ →
      s₁ ≠ r₁ → s₁ ≠ r₂ → s₂ ≠ r₂ → s₂ ≠ r₃ → s₃ ≠ r₃ → s₃ ≠ r₁ →
      ((s₁ = 0 ∧ r₂ = 1) ∨ (s₁ = 1 ∧ r₂ = 0)) ∨
      ((s₂ = 0 ∧ r₃ = 1) ∨ (s₂ = 1 ∧ r₃ = 0)) ∨
      ((s₃ = 0 ∧ r₁ = 1) ∨ (s₃ = 1 ∧ r₁ = 0)) := by
  intro r₁ r₂ r₃ s₁ s₂ s₃
  fin_cases r₁ <;> fin_cases r₂ <;> fin_cases r₃ <;>
    fin_cases s₁ <;> fin_cases s₂ <;> fin_cases s₃ <;> decide

end LeanPool.K5MinorFreeChoosability
