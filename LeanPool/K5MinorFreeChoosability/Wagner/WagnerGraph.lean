/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-!
# The Wagner graph

The Wagner graph `V₈` (the Möbius ladder on eight vertices: the cycle `0 1 … 7` together with
the four long diagonals `i (i+4)`) is the exceptional summand in Wagner's structure theorem for
`K₅`-minor-free graphs.  We prove the parts of that picture that do not need the structure
theorem itself:

* `cliqueMinorFree_five_of_degree_le_three`: a finite graph of maximum degree at most three on
  fewer than ten vertices has no `K₅` minor (every branch set of a `K₅` model must have at least
  two vertices);
* `cliqueMinorFree_five_wagnerGraph`: `V₈` has no `K₅` minor;
* `isMinor_K33_wagnerGraph`, `not_isPlanar_wagnerGraph`: `V₈` has a `K_{3,3}` minor, hence is
  not planar (in the combinatorial sense of `IsPlanar`).

The existence half of Wagner's structure theorem (every edge-maximal `K₅`-minor-free graph is a
clique-sum of planar triangulations and copies of `V₈`) is **not** proved here.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- **Degree bound for `K₅` minors**: a finite graph of maximum degree at most three on fewer
than ten vertices has no `K₅` minor. -/
theorem cliqueMinorFree_five_of_degree_le_three [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (hcard : Fintype.card V < 10) : CliqueMinorFree G 5 := by
  classical
  rintro ⟨M⟩
  have htwo : ∀ i, 2 ≤ (M.branch i).card := by
    intro i
    by_contra hlt
    obtain ⟨v, hv⟩ := Finset.card_eq_one.1 (le_antisymm (by omega)
      (Finset.card_pos.2 (M.branch_nonempty i)))
    have hnb : ∀ j, j ≠ i → ∃ w ∈ M.branch j, G.Adj v w := by
      intro j hj
      obtain ⟨u, hu, w, hw, huw⟩ := M.branch_adjacent i j (Ne.symm hj)
      rw [hv, Finset.mem_singleton] at hu
      exact ⟨w, hw, hu ▸ huw⟩
    have : Nonempty V := ⟨v⟩
    choose! g hgB hgA using hnb
    have hinj : Set.InjOn g (↑(Finset.univ.erase i) : Set (Fin 5)) := by
      intro j hj k hk hjk
      by_contra hne
      exact Finset.disjoint_left.1 (M.branch_disjoint j k hne)
        (hgB j (Finset.mem_erase.1 hj).1) (hjk ▸ hgB k (Finset.mem_erase.1 hk).1)
    have hle := Finset.card_le_card_of_injOn g (t := G.neighborFinset v)
      (fun j hj => (G.mem_neighborFinset v _).2 (hgA j (Finset.mem_erase.1 hj).1)) hinj
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      SimpleGraph.card_neighborFinset_eq_degree] at hle
    have := hdeg v
    omega
  have hsum : (Finset.univ.biUnion M.branch).card = ∑ i, (M.branch i).card :=
    Finset.card_biUnion fun i _ j _ hij => M.branch_disjoint i j hij
  have hge : 2 * 5 ≤ ∑ i, (M.branch i).card := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) fun i _ => htwo i
    simpa using this
  have hle := Finset.card_le_univ (Finset.univ.biUnion M.branch)
  omega

/-- The Wagner graph `V₈`: vertices `Fin 8`, `i ~ j` iff `j - i ∈ {1, 4, 7}` modulo `8`. -/
def wagnerGraph : SimpleGraph (Fin 8) where
  Adj i j := (j - i).val = 1 ∨ (j - i).val = 4 ∨ (j - i).val = 7
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel wagnerGraph.Adj := fun i j =>
  inferInstanceAs (Decidable ((j - i).val = 1 ∨ (j - i).val = 4 ∨ (j - i).val = 7))

theorem wagnerGraph_degree (v : Fin 8) : wagnerGraph.degree v = 3 := by
  revert v
  decide

/-- The Wagner graph has no `K₅` minor. -/
theorem cliqueMinorFree_five_wagnerGraph : CliqueMinorFree wagnerGraph 5 :=
  cliqueMinorFree_five_of_degree_le_three wagnerGraph (fun v => (wagnerGraph_degree v).le)
    (by simp)

/-- Branch sets of a `K_{3,3}` minor in `V₈`: `{0}, {2}, {5}` against `{1}, {3,4}, {6,7}`. -/
def wagnerK33Branch : Fin 3 ⊕ Fin 3 → Finset (Fin 8)
  | .inl 0 => {0}
  | .inl 1 => {2}
  | .inl 2 => {5}
  | .inr 0 => {1}
  | .inr 1 => {3, 4}
  | .inr 2 => {6, 7}

/-- A `K_{3,3}` minor model in the Wagner graph. -/
def wagnerK33Model : MinorModel wagnerGraph K33 where
  branch := wagnerK33Branch
  branch_nonempty := by decide
  branch_connected w := by
    rw [← connSet_iff_induce_connected]
    rcases w with w | w <;> fin_cases w <;> simp only [wagnerK33Branch, Finset.coe_singleton,
      Finset.coe_insert] <;>
      first
      | exact connSet_singleton _ _
      | exact (connSet_iff_induce_connected _ _).2
          (SimpleGraph.induce_pair_connected_of_adj (by decide))
  branch_disjoint := by decide
  branch_adjacent := by decide

theorem isMinor_K33_wagnerGraph : IsMinor K33 wagnerGraph := ⟨wagnerK33Model⟩

/-- The Wagner graph is not planar. -/
theorem not_isPlanar_wagnerGraph : ¬ IsPlanar wagnerGraph :=
  fun h => k33MinorFree_of_isPlanar h isMinor_K33_wagnerGraph

end LeanPool.K5MinorFreeChoosability
