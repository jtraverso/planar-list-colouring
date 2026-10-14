/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerMinorRigidity
public import LeanPool.K5MinorFreeChoosability.Wagner.YDeltaModelAttack
public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerA

/-!
# Wagner (b): reduction of the maximal core to a single `V₈`-minor statement

This file proves reductions only. The residual `WagnerV8MinorCore V` is proved for finite `V`
in `Wagner/WagnerV8Core.lean` (`wagnerV8MinorCore`), which closes Wagner (b).

* `not_isPlanar_of_degree_three_core` (unconditional): in the degree-three maximal core the
  graph has a `K₃,₃` minor, hence is nonplanar.
* `WagnerV8MinorCore V`: the **residual statement**.  Every edge-maximal `K₅`-minor-free graph on
  `S` without separations of order at most two, without proper clique separations of order at
  most three, and which is nonplanar, has `V₈` as a minor.
* `wagnerMaximalCore_of_v8MinorCore`: the residual implies the classical maximal core
  `WagnerMaximalCore V`, using the unconditional minor-to-copy rigidity
  `isWagnerPiece_of_isMinor_wagner`.  Consequently the residual also yields `WagnerPrimeCore V`
  and the two public decomposition endpoints (`exists_k5Decomp_of_v8MinorCore`,
  `k5MinorFree_iff_exists_k5Decomp_of_v8MinorCore`), which remain **conditional** on it.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

/-- **Degree-three maximal core is nonplanar** (unconditional): it has a `K₃,₃` minor, obtained
from the Y–Δ `K₅` obstruction forced by maximality. -/
theorem isMinor_k33_of_degree_three_core {M : SimpleGraph V} {S K : Finset V} {c : V}
    (hM : IsMaxK5Free M S) (hns : NoSmallSep M S) (hsep : NoCliqueSepThree M S)
    (hS : 5 ≤ S.card) (hcS : c ∈ S) (hKS : K ⊆ S) (hcK : c ∉ K) (hK : K.card = 3)
    (hc : ∀ v, M.Adj c v → v ∈ K) : IsMinor K33 M := by
  obtain ⟨Mod⟩ := exists_yDelta_k5Model_of_maximal hM hsep hcS hKS hcK hK hS hc
  have hback := hns.adj_of_mem_three_neighbour_bound hcS hKS hcK hK (by omega) hc
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hK
  refine k33Minor_of_yDelta_k5Model hM.2.1 (by simp) hback ![x, y, z] ?_ Mod
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-- **Degree-three maximal core is nonplanar** (unconditional). -/
theorem not_isPlanar_of_degree_three_core [Finite V] {M : SimpleGraph V} {S K : Finset V} {c : V}
    (hM : IsMaxK5Free M S) (hns : NoSmallSep M S) (hsep : NoCliqueSepThree M S)
    (hS : 5 ≤ S.card) (hcS : c ∈ S) (hKS : K ⊆ S) (hcK : c ∉ K) (hK : K.card = 3)
    (hc : ∀ v, M.Adj c v → v ∈ K) : ¬ IsPlanar M := fun hp =>
  ((isPlanar_iff_k5MinorFree_and_k33MinorFree M).1 hp).2
    (isMinor_k33_of_degree_three_core hM hns hsep hS hcS hKS hcK hK hc)

/-- **Residual statement of Wagner (b)** (proved for finite `V` as `wagnerV8MinorCore` in
`Wagner/WagnerV8Core.lean`): a nonplanar
edge-maximal `K₅`-minor-free graph on `S` without separations of order at most two and without
proper clique separations of order at most three has `V₈` as a minor. -/
def WagnerV8MinorCore (V : Type*) [DecidableEq V] : Prop :=
  ∀ (M : SimpleGraph V) (S : Finset V), IsMaxK5Free M S → NoSmallSep M S →
    NoCliqueSepThree M S → ¬ IsPlanar M → IsMinor wagnerGraph M

/-- The residual `V₈`-minor statement implies the classical maximal core (proved reduction,
via the unconditional minor-to-copy rigidity). -/
theorem wagnerMaximalCore_of_v8MinorCore (h : WagnerV8MinorCore V) : WagnerMaximalCore V :=
  fun M S hM hns hpl hsep =>
    isWagnerPiece_of_isMinor_wagner hM.1 hM.2.1 hns (h M S hM hns hsep hpl)

/-- The residual implies the prime core (proved reduction). -/
theorem wagnerPrimeCore_of_v8MinorCore [Finite V] (h : WagnerV8MinorCore V) :
    WagnerPrimeCore V :=
  wagnerPrimeCore_of_maximal (wagnerMaximalCore_of_v8MinorCore h)

/-- **Wagner's structure theorem, conditional on the residual `WagnerV8MinorCore V`**
(scaffolding, not closure). -/
theorem exists_k5Decomp_of_v8MinorCore [Fintype V] (h : WagnerV8MinorCore V)
    (G : SimpleGraph V) (hG : K5MinorFree G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ K5Decomp H Finset.univ :=
  exists_k5Decomp_of_core (wagnerPrimeCore_of_v8MinorCore h) G hG

/-- **Wagner's structure theorem, both directions, conditional on the residual
`WagnerV8MinorCore V`** (scaffolding, not closure). -/
theorem k5MinorFree_iff_exists_k5Decomp_of_v8MinorCore [Fintype V] (h : WagnerV8MinorCore V)
    (G : SimpleGraph V) :
    K5MinorFree G ↔ ∃ H : SimpleGraph V, G ≤ H ∧ K5Decomp H Finset.univ :=
  k5MinorFree_iff_exists_k5Decomp_of_core (wagnerPrimeCore_of_v8MinorCore h) G

end LeanPool.K5MinorFreeChoosability
