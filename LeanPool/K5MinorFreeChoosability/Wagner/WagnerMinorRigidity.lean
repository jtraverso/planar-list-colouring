/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.StarThree

/-!
# Minor-to-copy rigidity for the Wagner graph

`isWagnerPiece_of_isMinor_wagner`: if a `K₅`-minor-free graph `G` with edges inside `S` and no
separation of order at most two (`NoSmallSep G S`) has `V₈` as a minor (in the branch-set sense
of `IsMinor`), then it is a `V₈`-piece on `S`: the support has exactly eight vertices and carries
a spanning copy of `V₈` with no further edges.

Proof.  Take a `V₈` model of minimum total size.  Each branch set is a minimal connected set
touching its three neighbours, hence a three-armed star (`exists_isStar3`); this is the
branch-set form of "a minor of a cubic graph is a topological minor".  If some arm is nonempty,
let it lie on the edge `i j` of `V₈` and remove the two centres `z i`, `z j`.  The rest of `S`
stays connected (`NoSmallSep`), so the arms of the edge `i j` are joined, through vertices
outside the model, to some other vertex of the model.  In each of the three possible positions
of that vertex, sliding at most two arms to the neighbouring branch set and absorbing the bridge
produces a `V₈` model with one extra adjacency between two nonadjacent vertices of `V₈`
(`V₈` is triangle-free), hence a `K₅` minor (`not_k5MinorFree_of_v8Model`).  So every branch set
is a single vertex and the model is an actual copy of `V₈`; the existing attachment theorem
`isWagnerPiece_of_wagner_subgraph` finishes.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-! ### Neighbours in `V₈` -/

/-- The `k`-th neighbour of `i` in `V₈` (offsets `1, 4, 7` modulo `8`). -/
def wagnerNb (i : Fin 8) (k : Fin 3) : Fin 8 := i + ![1, 4, 7] k

theorem wagnerNb_adj : ∀ i k, wagnerGraph.Adj i (wagnerNb i k) := by decide

theorem wagnerNb_surj : ∀ i j, wagnerGraph.Adj i j → ∃ k, wagnerNb i k = j := by decide

theorem wagnerNb_inj : ∀ i k l, wagnerNb i k = wagnerNb i l → k = l := by decide

theorem wagnerNb_ne : ∀ i k, wagnerNb i k ≠ i := by decide

theorem wagnerNb_back : ∀ i k, ∃ k', wagnerNb (wagnerNb i k) k' = i := by decide

theorem fin3_exists_ne (k : Fin 3) : ∃ l, l ≠ k := by revert k; decide

theorem fin3_exists_third (k l : Fin 3) (hkl : k ≠ l) : ∃ m, m ≠ k ∧ m ≠ l ∧
    ∀ n, n = k ∨ n = l ∨ n = m := by
  revert k l; decide

/-! ### Branch-set models of `V₈` -/

/-- A branch-set model of `V₈` in `G` (with the existing `ConnSet` and `Touch`). -/
structure IsV8Model (G : SimpleGraph V) (φ : Fin 8 → Finset V) : Prop where
  conn : ∀ a, ConnSet G ↑(φ a)
  disj : ∀ a b, a ≠ b → Disjoint (φ a) (φ b)
  adj : ∀ a b, wagnerGraph.Adj a b → Touch G (φ a) (φ b)

omit [DecidableEq V] in
theorem isV8Model_of_minorModel (M : MinorModel G wagnerGraph) : IsV8Model G M.branch :=
  ⟨fun a => (connSet_iff_induce_connected _ _).2 (M.branch_connected a), M.branch_disjoint,
    fun a b h => M.branch_adjacent a b h⟩

omit [DecidableEq V] in
/-- **Forbidden chords of a `V₈` model.**  A `V₈` model in which two branch sets of nonadjacent
vertices touch yields a `K₅` minor. -/
theorem not_k5MinorFree_of_v8Model {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ) {i j : Fin 8}
    (hij : i ≠ j) (hn : ¬ wagnerGraph.Adj i j) (ht : Touch G (φ i) (φ j)) :
    ¬ K5MinorFree G := by
  intro h5
  have hadj : ∀ a b, (addEdgeGraph wagnerGraph i j).Adj a b →
      ∃ u ∈ φ a, ∃ v ∈ φ b, G.Adj u v := by
    intro a b hab
    rcases hab with hab | ⟨_, hab⟩
    · exact hφ.adj a b hab
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ht
      · obtain ⟨u, hu, v, hv, huv⟩ := ht
        exact ⟨v, hv, u, hu, huv.symm⟩
  have hp : K5MinorFree (addEdgeGraph wagnerGraph i j) :=
    cliqueMinorFree_of_transport (by decide) Set.univ (fun _ _ _ => Set.mem_univ _)
      φ (fun a _ => hφ.conn a) (fun a _ b _ hab => hφ.disj a b hab) hadj h5
  exact not_k5MinorFree_of_wagner_plus_edge id Function.injective_id
    (fun _ _ h => Or.inl h) hij hn (Or.inr ⟨hij, Or.inl ⟨rfl, rfl⟩⟩) hp

/-- Moving a piece `X` of the branch set `i` to the neighbouring branch set `j`. -/
def v8Move (φ : Fin 8 → Finset V) (i j : Fin 8) (X : Finset V) : Fin 8 → Finset V :=
  fun a => if a = i then φ i \ X else if a = j then φ j ∪ X else φ a

/-- Adding a set `Q` to the branch set `i`. -/
def v8Add (φ : Fin 8 → Finset V) (i : Fin 8) (Q : Finset V) : Fin 8 → Finset V :=
  fun a => if a = i then φ i ∪ Q else φ a

@[simp] theorem v8Move_i (φ : Fin 8 → Finset V) (i j : Fin 8) (X : Finset V) :
    v8Move φ i j X i = φ i \ X := by simp [v8Move]

@[simp] theorem v8Move_j (φ : Fin 8 → Finset V) {i j : Fin 8} (h : i ≠ j) (X : Finset V) :
    v8Move φ i j X j = φ j ∪ X := by simp [v8Move, h.symm]

theorem v8Move_other (φ : Fin 8 → Finset V) {i j a : Fin 8} (hi : a ≠ i) (hj : a ≠ j)
    (X : Finset V) : v8Move φ i j X a = φ a := by simp [v8Move, hi, hj]

@[simp] theorem v8Add_i (φ : Fin 8 → Finset V) (i : Fin 8) (Q : Finset V) :
    v8Add φ i Q i = φ i ∪ Q := by simp [v8Add]

theorem v8Add_other (φ : Fin 8 → Finset V) {i a : Fin 8} (h : a ≠ i) (Q : Finset V) :
    v8Add φ i Q a = φ a := by simp [v8Add, h]

theorem v8Move_sub (φ : Fin 8 → Finset V) {i j : Fin 8} {X : Finset V} (hX : X ⊆ φ i)
    (a : Fin 8) : v8Move φ i j X a ⊆ Finset.univ.biUnion φ := by
  intro x hx
  simp only [v8Move] at hx
  split_ifs at hx with h1 h2
  · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (Finset.mem_sdiff.1 hx).1⟩
  · rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hx⟩
    · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hX hx⟩
  · exact Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hx⟩

/-- Sliding a piece to a neighbouring branch set keeps a `V₈` model. -/
theorem IsV8Model.move {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ) {i j : Fin 8}
    (hij : wagnerGraph.Adj i j) {X : Finset V} (hXi : X ⊆ φ i) (hXc : ConnSet G ↑X)
    (hXj : Touch G X (φ j)) (hRc : ConnSet G ↑(φ i \ X))
    (hRt : ∀ l, wagnerGraph.Adj i l → l ≠ j → Touch G (φ i \ X) (φ l))
    (hRX : Touch G (φ i \ X) X) : IsV8Model G (v8Move φ i j X) := by
  have hne : i ≠ j := fun h => wagnerGraph.loopless.irrefl i (h ▸ hij)
  have hXdis : ∀ a, a ≠ i → Disjoint X (φ a) := fun a ha =>
    Finset.disjoint_of_subset_left hXi (hφ.disj i a (Ne.symm ha))
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · by_cases hai : a = i
    · subst hai; simpa using hRc
    by_cases haj : a = j
    · subst haj; rw [v8Move_j φ hne]
      exact ConnSet.union_of_touch (hφ.conn a) hXc hXj.symm
    · rw [v8Move_other φ hai haj]; exact hφ.conn a
  · -- disjointness
    have key : ∀ c d, c ≠ d → c = i → Disjoint (v8Move φ i j X c) (v8Move φ i j X d) := by
      intro c d hcd hc
      subst hc
      rw [v8Move_i]
      by_cases hdj : d = j
      · subst hdj; rw [v8Move_j φ hne]
        exact Finset.disjoint_union_right.2 ⟨Finset.disjoint_of_subset_left
          Finset.sdiff_subset (hφ.disj c d hcd), Finset.sdiff_disjoint⟩
      · rw [v8Move_other φ (Ne.symm hcd) hdj]
        exact Finset.disjoint_of_subset_left Finset.sdiff_subset (hφ.disj c d hcd)
    by_cases hai : a = i
    · exact key a b hab hai
    by_cases hbi : b = i
    · exact (key b a (Ne.symm hab) hbi).symm
    by_cases haj : a = j
    · subst haj
      rw [v8Move_j φ hne, v8Move_other φ hbi (Ne.symm hab)]
      exact Finset.disjoint_union_left.2 ⟨hφ.disj a b hab, hXdis b hbi⟩
    by_cases hbj : b = j
    · subst hbj
      rw [v8Move_j φ hne, v8Move_other φ hai hab]
      exact Finset.disjoint_union_right.2 ⟨hφ.disj a b hab, (hXdis a hai).symm⟩
    rw [v8Move_other φ hai haj, v8Move_other φ hbi hbj]
    exact hφ.disj a b hab
  · -- adjacency
    have keyi : ∀ b, wagnerGraph.Adj i b → Touch G (v8Move φ i j X i) (v8Move φ i j X b) := by
      intro b hb
      have hbi : b ≠ i := fun h => wagnerGraph.loopless.irrefl i (h ▸ hb)
      rw [v8Move_i]
      by_cases hbj : b = j
      · subst hbj; rw [v8Move_j φ hne]
        exact hRX.mono subset_rfl Finset.subset_union_right
      · rw [v8Move_other φ hbi hbj]; exact hRt b hb hbj
    have keyj : ∀ b, wagnerGraph.Adj j b → b ≠ i →
        Touch G (v8Move φ i j X j) (v8Move φ i j X b) := by
      intro b hb hbi
      have hbj : b ≠ j := fun h => wagnerGraph.loopless.irrefl j (h ▸ hb)
      rw [v8Move_j φ hne, v8Move_other φ hbi hbj]
      exact (hφ.adj j b hb).mono Finset.subset_union_left subset_rfl
    by_cases hai : a = i
    · subst hai; exact keyi b hab
    by_cases hbi : b = i
    · subst hbi; exact (keyi a hab.symm).symm
    by_cases haj : a = j
    · subst haj; exact keyj b hab hbi
    by_cases hbj : b = j
    · subst hbj; exact (keyj a hab.symm hai).symm
    rw [v8Move_other φ hai haj, v8Move_other φ hbi hbj]
    exact hφ.adj a b hab

/-- Absorbing an outside connected set (or nothing) keeps a `V₈` model. -/
theorem IsV8Model.add {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ) (i : Fin 8) {Q : Finset V}
    (hQ : ∀ a, Disjoint Q (φ a)) (hQc : Q = ∅ ∨ (ConnSet G ↑Q ∧ Touch G Q (φ i))) :
    IsV8Model G (v8Add φ i Q) := by
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · by_cases hai : a = i
    · subst hai; rw [v8Add_i]
      rcases hQc with rfl | ⟨hc, ht⟩
      · simpa using hφ.conn a
      · exact ConnSet.union_of_touch (hφ.conn a) hc ht.symm
    · rw [v8Add_other φ hai]; exact hφ.conn a
  · by_cases hai : a = i
    · subst hai
      rw [v8Add_i, v8Add_other φ (Ne.symm hab)]
      exact Finset.disjoint_union_left.2 ⟨hφ.disj a b hab, hQ b⟩
    by_cases hbi : b = i
    · subst hbi
      rw [v8Add_i, v8Add_other φ hab]
      exact Finset.disjoint_union_right.2 ⟨hφ.disj a b hab, (hQ a).symm⟩
    rw [v8Add_other φ hai, v8Add_other φ hbi]; exact hφ.disj a b hab
  · have hab' : a ≠ b := fun h => wagnerGraph.loopless.irrefl a (h ▸ hab)
    by_cases hai : a = i
    · subst hai
      rw [v8Add_i, v8Add_other φ (Ne.symm hab')]
      exact (hφ.adj a b hab).mono Finset.subset_union_left subset_rfl
    by_cases hbi : b = i
    · subst hbi
      rw [v8Add_i, v8Add_other φ hab']
      exact (hφ.adj a b hab).mono subset_rfl Finset.subset_union_left
    rw [v8Add_other φ hai, v8Add_other φ hbi]; exact hφ.adj a b hab

/-! ### Minimal models are stars -/

/-- Total size of a family of branch sets. -/
def v8Size (φ : Fin 8 → Finset V) : ℕ := ∑ i, (φ i).card

omit [DecidableEq V] in
theorem exists_min_v8Model (h : ∃ φ, IsV8Model G φ) :
    ∃ φ, IsV8Model G φ ∧ ∀ ψ, IsV8Model G ψ → v8Size φ ≤ v8Size ψ := by
  classical
  have hex : ∃ n, ∃ φ, IsV8Model G φ ∧ v8Size φ = n := by
    obtain ⟨φ, hφ⟩ := h; exact ⟨_, φ, hφ, rfl⟩
  obtain ⟨φ, hφ, hs⟩ := Nat.find_spec hex
  refine ⟨φ, hφ, fun ψ hψ => ?_⟩
  rw [hs]; exact Nat.find_min' hex ⟨ψ, hψ, rfl⟩

omit [DecidableEq V] in
/-- In a minimal `V₈` model every branch set is a minimal connected set touching its three
neighbours. -/
theorem isMinTouch3_of_min {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ)
    (hmin : ∀ ψ, IsV8Model G ψ → v8Size φ ≤ v8Size ψ) (i : Fin 8) :
    IsMinTouch3 G (fun k => φ (wagnerNb i k)) (φ i) := by
  refine ⟨hφ.conn i, fun k => hφ.adj i _ (wagnerNb_adj i k), fun B' hsub hne hc ht => ?_⟩
  let ψ := Function.update φ i B'
  have hψ : IsV8Model G ψ := by
    refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
    · by_cases hai : a = i
      · subst hai; simpa [ψ] using hc
      · simpa [ψ, Function.update_of_ne hai] using hφ.conn a
    · by_cases hai : a = i
      · subst hai
        simp only [ψ, Function.update_self, Function.update_of_ne (Ne.symm hab)]
        exact Finset.disjoint_of_subset_left hsub (hφ.disj a b hab)
      by_cases hbi : b = i
      · subst hbi
        simp only [ψ, Function.update_self, Function.update_of_ne hab]
        exact Finset.disjoint_of_subset_right hsub (hφ.disj a b hab)
      simp only [ψ, Function.update_of_ne hai, Function.update_of_ne hbi]
      exact hφ.disj a b hab
    · have hab' : a ≠ b := fun h => wagnerGraph.loopless.irrefl a (h ▸ hab)
      by_cases hai : a = i
      · subst hai
        simp only [ψ, Function.update_self, Function.update_of_ne (Ne.symm hab')]
        obtain ⟨k, rfl⟩ := wagnerNb_surj a b hab
        exact ht k
      by_cases hbi : b = i
      · subst hbi
        simp only [ψ, Function.update_self, Function.update_of_ne hab']
        obtain ⟨k, rfl⟩ := wagnerNb_surj b a hab.symm
        exact (ht k).symm
      simp only [ψ, Function.update_of_ne hai, Function.update_of_ne hbi]
      exact hφ.adj a b hab
  have hlt : v8Size ψ < v8Size φ := by
    apply Finset.sum_lt_sum
    · intro a _
      by_cases hai : a = i
      · subst hai; simpa [ψ] using Finset.card_le_card hsub
      · simp [ψ, Function.update_of_ne hai]
    · exact ⟨i, Finset.mem_univ _, by
        simpa [ψ] using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)⟩
  exact absurd (hmin ψ hψ) (not_le.2 hlt)

/-! ### Facts about stars -/

namespace IsStar3

variable {T : Fin 3 → Finset V} {B : Finset V} {z : V} {R : Fin 3 → Finset V}

theorem R_sub_B (h : IsStar3 G T B z R) (k : Fin 3) : R k ⊆ B :=
  (h.R_sub k).trans (Finset.erase_subset _ _)

theorem z_not_mem (h : IsStar3 G T B z R) (k : Fin 3) : z ∉ R k := fun hz => by
  simpa using h.R_sub k hz

theorem z_mem_rest (h : IsStar3 G T B z R) (J : Finset (Fin 3)) : z ∈ B \ J.biUnion R := by
  refine Finset.mem_sdiff.2 ⟨h.z_mem, ?_⟩
  simp only [Finset.mem_biUnion, not_exists, not_and]
  exact fun j _ => h.z_not_mem j

/-- Removing any family of arms leaves a connected set. -/
theorem rest_conn (h : IsStar3 G T B z R) (J : Finset (Fin 3)) :
    ConnSet G ↑(B \ J.biUnion R) := by
  have hz := h.z_mem_rest J
  have key : ∀ y ∈ B \ J.biUnion R, RIn G ↑(B \ J.biUnion R) y z := by
    intro y hy
    obtain ⟨hyB, hyJ⟩ := Finset.mem_sdiff.1 hy
    by_cases hyz : y = z
    · subst hyz; exact RIn.refl _
    obtain ⟨k, hk⟩ := h.cover y hyB hyz
    have hkJ : k ∉ J := fun hkJ => hyJ (Finset.mem_biUnion.2 ⟨k, hkJ, hk⟩)
    have hsub : R k ⊆ B \ J.biUnion R := by
      intro x hx
      refine Finset.mem_sdiff.2 ⟨h.R_sub_B k hx, ?_⟩
      simp only [Finset.mem_biUnion, not_exists, not_and]
      intro j hj hxj
      have hjk : j ≠ k := fun he => hkJ (he ▸ hj)
      exact Finset.disjoint_left.1 (h.R_disj j k hjk) hxj hx
    have hne : (R k).Nonempty := ⟨y, hk⟩
    obtain ⟨w, hw, z', hz', hwz⟩ := h.touch_z k hne
    rw [Finset.mem_singleton] at hz'
    subst hz'
    exact (((h.conn k hne).2 y hk w hw).mono_set (by exact_mod_cast hsub)).tail hwz
      (by exact_mod_cast hsub hw) (by exact_mod_cast hz)
  refine ⟨⟨z, by exact_mod_cast hz⟩, fun x hx y hy => ?_⟩
  exact (key x (by exact_mod_cast hx)).trans (key y (by exact_mod_cast hy)).symm

/-- Removing arms not aimed at `l` keeps the contact with `T l`. -/
theorem rest_touch (h : IsStar3 G T B z R) (J : Finset (Fin 3)) {l : Fin 3} (hl : l ∉ J) :
    Touch G (B \ J.biUnion R) (T l) := by
  by_cases hR : (R l).Nonempty
  · refine (h.touch_T l hR).mono ?_ subset_rfl
    intro x hx
    refine Finset.mem_sdiff.2 ⟨h.R_sub_B l hx, ?_⟩
    simp only [Finset.mem_biUnion, not_exists, not_and]
    intro j hj hxj
    have hjl : j ≠ l := fun he => hl (he ▸ hj)
    exact Finset.disjoint_left.1 (h.R_disj j l hjl) hxj hx
  · have := h.empty_T l (Finset.not_nonempty_iff_eq_empty.1 hR)
    exact this.mono (Finset.singleton_subset_iff.2 (h.z_mem_rest J)) subset_rfl

/-- The centre touches every nonempty arm. -/
theorem rest_touch_arm (h : IsStar3 G T B z R) (J : Finset (Fin 3)) {k : Fin 3}
    (hk : (R k).Nonempty) : Touch G (B \ J.biUnion R) (R k) :=
  (h.touch_z k hk).symm.mono (Finset.singleton_subset_iff.2 (h.z_mem_rest J)) subset_rfl

end IsStar3

/-! ### Bridges create forbidden chords -/

theorem sdiff_pair_eq (X : Finset V) (A : Fin 3 → Finset V) (k l : Fin 3) :
    (X \ A k) \ A l = X \ ({k, l} : Finset (Fin 3)).biUnion A := by
  ext x; simp [Finset.mem_sdiff, and_assoc]

theorem bridge_touch {A Bm Q : Finset V} {p q : V} (hp : p ∈ A) (hq : q ∈ Bm)
    (hbr : (Q = ∅ ∧ G.Adj p q) ∨ (ConnSet G ↑Q ∧ Touch G Q {p} ∧ Touch G Q {q})) :
    Touch G (A ∪ Q) Bm := by
  rcases hbr with ⟨-, hpq⟩ | ⟨-, -, hQq⟩
  · exact ⟨p, Finset.mem_union_left _ hp, q, hq, hpq⟩
  · exact hQq.mono Finset.subset_union_right (Finset.singleton_subset_iff.2 hq)

omit [DecidableEq V] in
theorem bridge_cond {A Q : Finset V} {p q : V} (hp : p ∈ A)
    (hbr : (Q = ∅ ∧ G.Adj p q) ∨ (ConnSet G ↑Q ∧ Touch G Q {p} ∧ Touch G Q {q})) :
    Q = ∅ ∨ (ConnSet G ↑Q ∧ Touch G Q A) := by
  rcases hbr with ⟨hQ, -⟩ | ⟨hc, hQp, -⟩
  · exact Or.inl hQ
  · exact Or.inr ⟨hc, hQp.mono subset_rfl (Finset.singleton_subset_iff.2 hp)⟩

/-- Slide the arm `R i k` of a star branch set to the neighbour `wagnerNb i k`. -/
theorem IsV8Model.move_arm {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ) {z : V}
    {R : Fin 3 → Finset V} {i : Fin 8} (hst : IsStar3 G (fun k => φ (wagnerNb i k)) (φ i) z R)
    {k : Fin 3} (hk : (R k).Nonempty) :
    IsV8Model G (v8Move φ i (wagnerNb i k) (R k)) := by
  refine hφ.move (wagnerNb_adj i k) (hst.R_sub_B k) (hst.conn k hk) (hst.touch_T k hk)
    (by simpa using hst.rest_conn {k}) (fun l hl hlj => ?_)
    (by simpa using hst.rest_touch_arm {k} hk)
  obtain ⟨m, rfl⟩ := wagnerNb_surj i l hl
  have hmk : m ≠ k := fun h => hlj (h ▸ rfl)
  simpa using hst.rest_touch {k} (l := m) (by simpa using hmk)

/-- **The bridge lemma.**  In a `V₈` model whose branch sets are stars, a bridge from an arm
of the edge `i j` to any vertex of the model other than the two centres and the arms of that
edge yields a `K₅` minor. -/
theorem not_k5MinorFree_of_bridge {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ)
    {z : Fin 8 → V} {R : Fin 8 → Fin 3 → Finset V}
    (hst : ∀ i, IsStar3 G (fun k => φ (wagnerNb i k)) (φ i) (z i) (R i))
    {i j : Fin 8} {k k' : Fin 3} (hj : wagnerNb i k = j) (hj' : wagnerNb j k' = i)
    {p q : V} (hp : p ∈ R i k) {m : Fin 8} (hqm : q ∈ φ m)
    (hqE1 : q ∉ R i k) (hqE2 : q ∉ R j k') (hqz1 : q ≠ z i) (hqz2 : q ≠ z j)
    {Q : Finset V} (hQ : ∀ a, Disjoint Q (φ a))
    (hbr : (Q = ∅ ∧ G.Adj p q) ∨ (ConnSet G ↑Q ∧ Touch G Q {p} ∧ Touch G Q {q})) :
    ¬ K5MinorFree G := by
  have hij : wagnerGraph.Adj i j := hj ▸ wagnerNb_adj i k
  have hne : i ≠ j := fun h => wagnerGraph.loopless.irrefl i (h ▸ hij)
  have hpi : p ∈ φ i := (hst i).R_sub_B k hp
  have hRk : (R i k).Nonempty := ⟨p, hp⟩
  -- sliding the arm `R i k` to `j`
  have hφ1 : IsV8Model G (v8Move φ i j (R i k)) := hj ▸ hφ.move_arm (hst i) hRk
  have hQ1 : ∀ a, Disjoint Q (v8Move φ i j (R i k) a) := by
    intro a
    refine Finset.disjoint_left.2 fun x hxQ hx => ?_
    obtain ⟨b, -, hxb⟩ := Finset.mem_biUnion.1 (v8Move_sub φ ((hst i).R_sub_B k) a hx)
    exact Finset.disjoint_left.1 (hQ b) hxQ hxb
  have hpj1 : p ∈ v8Move φ i j (R i k) j := by
    rw [v8Move_j φ hne]; exact Finset.mem_union_right _ hp
  by_cases hmi : m = i
  · -- the bridge returns to another arm of `i`
    subst hmi
    obtain ⟨k2, hk2⟩ := (hst m).cover q hqm hqz1
    have hk2k : k2 ≠ k := fun h => hqE1 (h ▸ hk2)
    set mm := wagnerNb m k2 with hmm
    have hmmj : mm ≠ j := fun h => hk2k (wagnerNb_inj m k2 k (h.trans hj.symm))
    have hmmi : mm ≠ m := wagnerNb_ne m k2
    have hRk2 : (R m k2).Nonempty := ⟨q, hk2⟩
    -- slide the second arm to `mm`
    have hφ2 : IsV8Model G (v8Move (v8Move φ m j (R m k)) m mm (R m k2)) := by
      refine hφ1.move (wagnerNb_adj m k2) ?_ ((hst m).conn k2 hRk2) ?_ ?_ ?_ ?_
      · rw [v8Move_i]
        exact Finset.subset_sdiff.2 ⟨(hst m).R_sub_B k2, (hst m).R_disj k2 k hk2k⟩
      · rw [v8Move_other φ hmmi hmmj]; exact (hst m).touch_T k2 hRk2
      · rw [v8Move_i, sdiff_pair_eq]; exact (hst m).rest_conn _
      · intro l hl hlmm
        obtain ⟨n, rfl⟩ := wagnerNb_surj m l hl
        have hnk2 : n ≠ k2 := fun h => hlmm (h ▸ rfl)
        rw [v8Move_i, sdiff_pair_eq]
        by_cases hnk : n = k
        · subst hnk
          rw [hj, v8Move_j φ hne]
          exact ((hst m).rest_touch_arm _ hRk).mono subset_rfl Finset.subset_union_right
        · have hnj : wagnerNb m n ≠ j := fun h => hnk (wagnerNb_inj m n k (h.trans hj.symm))
          rw [v8Move_other φ (wagnerNb_ne m n) hnj]
          exact (hst m).rest_touch _ (by simp [hnk, hnk2])
      · rw [v8Move_i, sdiff_pair_eq]; exact (hst m).rest_touch_arm _ hRk2
    have hQ2 : ∀ a, Disjoint Q (v8Move (v8Move φ m j (R m k)) m mm (R m k2) a) := by
      intro a
      refine Finset.disjoint_left.2 fun x hxQ hx => ?_
      have hsub : R m k2 ⊆ v8Move φ m j (R m k) m := by
        rw [v8Move_i]
        exact Finset.subset_sdiff.2 ⟨(hst m).R_sub_B k2, (hst m).R_disj k2 k hk2k⟩
      obtain ⟨b, -, hxb⟩ := Finset.mem_biUnion.1 (v8Move_sub _ hsub a hx)
      exact Finset.disjoint_left.1 (hQ1 b) hxQ hxb
    have hpj2 : p ∈ v8Move (v8Move φ m j (R m k)) m mm (R m k2) j := by
      rw [v8Move_other _ (Ne.symm hne) (Ne.symm hmmj)]; exact hpj1
    have hφ3 := hφ2.add j hQ2 (bridge_cond hpj2 hbr)
    refine not_k5MinorFree_of_v8Model hφ3 (Ne.symm hmmj)
      (wagnerGraph_no_triangle j m mm hij.symm (wagnerNb_adj m k2)) ?_
    rw [v8Add_i, v8Add_other _ hmmj]
    refine bridge_touch hpj2 ?_ hbr
    rw [v8Move_j _ (Ne.symm hmmi)]
    exact Finset.mem_union_right _ hk2
  by_cases hmj : m = j
  · -- the bridge returns to another arm of `j`
    subst hmj
    obtain ⟨k3, hk3⟩ := (hst m).cover q hqm hqz2
    have hk3k : k3 ≠ k' := fun h => hqE2 (h ▸ hk3)
    set mm := wagnerNb m k3 with hmm
    have hmmi : mm ≠ i := fun h => hk3k (wagnerNb_inj m k3 k' (h.trans hj'.symm))
    have hmmj : mm ≠ m := wagnerNb_ne m k3
    have hRk3 : (R m k3).Nonempty := ⟨q, hk3⟩
    have hφ2 : IsV8Model G (v8Move φ m mm (R m k3)) := hφ.move_arm (hst m) hRk3
    have hQ2 : ∀ a, Disjoint Q (v8Move φ m mm (R m k3) a) := by
      intro a
      refine Finset.disjoint_left.2 fun x hxQ hx => ?_
      obtain ⟨b, -, hxb⟩ := Finset.mem_biUnion.1 (v8Move_sub φ ((hst m).R_sub_B k3) a hx)
      exact Finset.disjoint_left.1 (hQ b) hxQ hxb
    have hpi2 : p ∈ v8Move φ m mm (R m k3) i := by
      rw [v8Move_other φ hne (Ne.symm hmmi)]; exact hpi
    have hφ3 := hφ2.add i hQ2 (bridge_cond hpi2 hbr)
    refine not_k5MinorFree_of_v8Model hφ3 (Ne.symm hmmi)
      (wagnerGraph_no_triangle i m mm hij (wagnerNb_adj m k3)) ?_
    rw [v8Add_i, v8Add_other _ hmmi]
    refine bridge_touch hpi2 ?_ hbr
    rw [v8Move_j _ (Ne.symm hmmj)]
    exact Finset.mem_union_right _ hk3
  · -- the bridge reaches a third branch set
    by_cases him : wagnerGraph.Adj i m
    · have hjm : ¬ wagnerGraph.Adj j m := wagnerGraph_no_triangle j i m hij.symm him
      have hφ2 := hφ1.add j hQ1 (bridge_cond hpj1 hbr)
      refine not_k5MinorFree_of_v8Model hφ2 (Ne.symm hmj) hjm ?_
      rw [v8Add_i, v8Add_other _ hmj]
      refine bridge_touch hpj1 ?_ hbr
      rw [v8Move_other φ hmi hmj]; exact hqm
    · have hφ2 := hφ.add i hQ (bridge_cond hpi hbr)
      refine not_k5MinorFree_of_v8Model hφ2 (Ne.symm hmi) him ?_
      rw [v8Add_i, v8Add_other _ hmi]
      exact bridge_touch hpi hqm hbr

/-! ### All arms are empty -/

omit [DecidableEq V] in
/-- Branch sets of a `V₈` model lie in the support of the edges. -/
theorem IsV8Model.sub_support {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ) {S : Finset V}
    (hS : ∀ u v, G.Adj u v → u ∈ S) (a : Fin 8) : φ a ⊆ S := by
  intro v hv
  obtain ⟨b, hb⟩ := (wagnerNb_surj a _ (wagnerNb_adj a 0))
  obtain ⟨c, hc, d, -, hcd⟩ := hφ.adj a _ (wagnerNb_adj a 0)
  have hr := (hφ.conn a).2 v hv c hc
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨e, hve, -⟩
  · exact hS _ _ hcd
  · exact hS _ _ hve.1

theorem all_arms_empty {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S) (h5 : K5MinorFree G)
    (hsep : NoSmallSep G S) {φ : Fin 8 → Finset V} (hφ : IsV8Model G φ)
    {z : Fin 8 → V} {R : Fin 8 → Fin 3 → Finset V}
    (hst : ∀ i, IsStar3 G (fun k => φ (wagnerNb i k)) (φ i) (z i) (R i)) :
    ∀ i k, R i k = ∅ := by
  intro i k
  by_contra hne
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
  set j := wagnerNb i k with hj
  obtain ⟨k', hj'⟩ := wagnerNb_back i k
  rw [← hj] at hj'
  have hij : wagnerGraph.Adj i j := wagnerNb_adj i k
  have hneij : i ≠ j := fun h => wagnerGraph.loopless.irrefl i (h ▸ hij)
  obtain ⟨k2, hk2⟩ := fin3_exists_ne k
  set m := wagnerNb i k2 with hm
  have hmi : m ≠ i := wagnerNb_ne i k2
  have hmj : m ≠ j := fun h => hk2 (wagnerNb_inj i k2 k h)
  have hφS := hφ.sub_support hS
  have hzi : z i ∈ φ i := (hst i).z_mem
  have hzj : z j ∈ φ j := (hst j).z_mem
  have hzm : z m ∈ φ m := (hst m).z_mem
  have hsi : s ∈ φ i := (hst i).R_sub_B k hs
  let Z : Finset V := {z i, z j}
  have hZS : Z ⊆ S := by
    intro x hx
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hφS i hzi
    · exact hφS j hzj
  have hnotZ : ∀ x a, x ∈ φ a → a ≠ i → a ≠ j → x ∉ Z := by
    intro x a hx hai haj hxZ
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hxZ
    rcases hxZ with rfl | rfl
    · exact Finset.disjoint_left.1 (hφ.disj a i hai) hx hzi
    · exact Finset.disjoint_left.1 (hφ.disj a j haj) hx hzj
  have hsZ : s ∉ Z := by
    intro hsZ
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hsZ
    rcases hsZ with rfl | rfl
    · exact (hst i).z_not_mem k hs
    · exact Finset.disjoint_left.1 (hφ.disj i j hneij) hsi hzj
  have hsSZ : s ∈ S \ Z := Finset.mem_sdiff.2 ⟨hφS i hsi, hsZ⟩
  have hzmSZ : z m ∈ S \ Z := Finset.mem_sdiff.2 ⟨hφS m hzm, hnotZ _ m hzm hmi hmj⟩
  have hconn := hsep.connSet_sdiff hZS (Finset.card_le_two) ⟨s, hsSZ⟩
  set F := Finset.univ.biUnion φ with hF
  set E := R i k ∪ R j k' with hE
  set W := E ∪ (S \ F) with hW
  have hsW : s ∈ W := Finset.mem_union_left _ (Finset.mem_union_left _ hs)
  set Y := reachIn G W s with hY
  have hEsub : E ⊆ φ i ∪ φ j := Finset.union_subset_union ((hst i).R_sub_B k)
    ((hst j).R_sub_B k')
  have hmemF : ∀ x a, x ∈ φ a → x ∈ F := fun x a hx =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hx⟩
  have hzmY : z m ∉ Y := by
    intro h
    rcases Finset.mem_union.1 (reachIn_sub _ _ h) with hE' | hSF
    · rcases Finset.mem_union.1 (hEsub hE') with h1 | h1
      · exact Finset.disjoint_left.1 (hφ.disj m i hmi) hzm h1
      · exact Finset.disjoint_left.1 (hφ.disj m j hmj) hzm h1
    · exact (Finset.mem_sdiff.1 hSF).2 (hmemF _ m hzm)
  obtain ⟨p, q, -, hpSZ, hpY, hqSZ, hqY, hpq⟩ := (hconn.2 s (by exact_mod_cast hsSZ) (z m)
    (by exact_mod_cast hzmSZ)).exit (P := (↑Y : Set V))
    (by exact_mod_cast mem_reachIn_self hsW) (by exact_mod_cast hzmY)
  have hpY' : p ∈ Y := by exact_mod_cast hpY
  have hqSZ' : q ∈ S \ Z := by exact_mod_cast hqSZ
  have hqW : q ∉ W := fun h => hqY (by exact_mod_cast reachIn_closed hpY' h hpq)
  have hqF : q ∈ F := by
    by_contra hqF
    exact hqW (Finset.mem_union_right _
      (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hqSZ').1, hqF⟩))
  obtain ⟨mq, -, hqmq⟩ := Finset.mem_biUnion.1 hqF
  have hqE : q ∉ E := fun h => hqW (Finset.mem_union_left _ h)
  have hqE1 : q ∉ R i k := fun h => hqE (Finset.mem_union_left _ h)
  have hqE2 : q ∉ R j k' := fun h => hqE (Finset.mem_union_right _ h)
  have hqZ : q ∉ Z := (Finset.mem_sdiff.1 hqSZ').2
  have hqz1 : q ≠ z i := fun h => hqZ (by simp [Z, h])
  have hqz2 : q ≠ z j := fun h => hqZ (by simp [Z, h])
  -- apply the bridge lemma in the orientation of the attachment point
  have finish : ∀ (p0 : V) (Q : Finset V), p0 ∈ E → (∀ a, Disjoint Q (φ a)) →
      ((Q = ∅ ∧ G.Adj p0 q) ∨ (ConnSet G ↑Q ∧ Touch G Q {p0} ∧ Touch G Q {q})) →
        False := by
    intro p0 Q hp0 hQ hbr
    rcases Finset.mem_union.1 hp0 with h1 | h1
    · exact not_k5MinorFree_of_bridge hφ hst hj.symm hj' h1 hqmq hqE1 hqE2 hqz1 hqz2 hQ hbr h5
    · exact not_k5MinorFree_of_bridge hφ hst hj' hj.symm h1 hqmq hqE2 hqE1 hqz2 hqz1 hQ hbr h5
  rcases Finset.mem_union.1 (reachIn_sub _ _ hpY') with hpE | hpSF
  · exact finish p ∅ hpE (fun _ => Finset.disjoint_empty_left _) (Or.inl ⟨rfl, hpq⟩)
  · -- the bridge passes through the outside component `Q` of `p`
    set Q := reachIn G (S \ F) p with hQdef
    have hQsub : Q ⊆ S \ F := reachIn_sub _ _
    have hQdis : ∀ a, Disjoint Q (φ a) := fun a => Finset.disjoint_left.2 fun x hxQ hxa =>
      (Finset.mem_sdiff.1 (hQsub hxQ)).2 (hmemF x a hxa)
    have hpQ : p ∈ Q := mem_reachIn_self hpSF
    have hsQ : s ∉ Q := fun h => (Finset.mem_sdiff.1 (hQsub h)).2 (hmemF s i hsi)
    obtain ⟨p', q', -, -, hp'Q, hq'W, hq'Q, hp'q'⟩ :=
      (mem_reachIn.1 hpY').2.symm.exit (P := (↑Q : Set V)) (by exact_mod_cast hpQ)
        (by exact_mod_cast hsQ)
    have hp'Q' : p' ∈ Q := by exact_mod_cast hp'Q
    have hq'W' : q' ∈ W := by exact_mod_cast hq'W
    have hq'E : q' ∈ E := by
      rcases Finset.mem_union.1 hq'W' with h | h
      · exact h
      · exact absurd (by exact_mod_cast reachIn_closed hp'Q' h hp'q') hq'Q
    exact finish q' Q hq'E hQdis (Or.inr ⟨reachIn_conn hpSF,
      ⟨p', hp'Q', q', Finset.mem_singleton_self _, hp'q'⟩,
      ⟨p, hpQ, q, Finset.mem_singleton_self _, hpq⟩⟩)

/-! ### The rigidity theorem -/

/-- **Minor-to-copy rigidity for `V₈`.**  A `K₅`-minor-free graph with edges inside `S`, no
separation of order at most two on `S`, and a `V₈` minor contains an actual copy of `V₈`
inside `S`. -/
theorem exists_wagner_copy_of_isMinor {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S)
    (h5 : K5MinorFree G) (hsep : NoSmallSep G S) (hm : IsMinor wagnerGraph G) :
    ∃ f : Fin 8 → V, Function.Injective f ∧ (∀ a, f a ∈ S) ∧
      ∀ a b, wagnerGraph.Adj a b → G.Adj (f a) (f b) := by
  obtain ⟨M⟩ := hm
  obtain ⟨φ, hφ, hmin⟩ := exists_min_v8Model ⟨_, isV8Model_of_minorModel M⟩
  have hstar := fun i => exists_isStar3 (isMinTouch3_of_min hφ hmin i)
  choose z R hst using hstar
  have hempty := all_arms_empty hS h5 hsep hφ hst
  have hsingle : ∀ i, φ i = {z i} := by
    intro i
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨(hst i).z_mem, fun x hx => ?_⟩
    by_contra hxz
    obtain ⟨k, hk⟩ := (hst i).cover x hx hxz
    simp [hempty i k] at hk
  refine ⟨z, fun a b hab => ?_, fun a => hφ.sub_support hS a (hst a).z_mem, fun a b hab => ?_⟩
  · by_contra hne
    exact Finset.disjoint_left.1 (hφ.disj a b hne) (hst a).z_mem (hab ▸ (hst b).z_mem)
  · obtain ⟨u, hu, v, hv, huv⟩ := hφ.adj a b hab
    rw [hsingle a, Finset.mem_singleton] at hu
    rw [hsingle b, Finset.mem_singleton] at hv
    subst hu; subst hv; exact huv

/-- **Wagner rigidity for minors.**  A `K₅`-minor-free graph with edges inside `S`, no
separation of order at most two on `S`, and a `V₈` minor is a `V₈`-piece on `S`. -/
theorem isWagnerPiece_of_isMinor_wagner {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S)
    (h5 : K5MinorFree G) (hsep : NoSmallSep G S) (hm : IsMinor wagnerGraph G) :
    IsWagnerPiece G S := by
  obtain ⟨f, hf, hfS, hW⟩ := exists_wagner_copy_of_isMinor hS h5 hsep hm
  exact isWagnerPiece_of_wagner_subgraph h5 hsep f hf hfS hW

end LeanPool.K5MinorFreeChoosability
