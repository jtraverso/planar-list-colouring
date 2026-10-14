/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerA
public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerGraph

/-!
# Wagner's structure theorem for `K_5`-minor-free graphs: certificate and reductions

**Status: the existence direction is CONDITIONAL on one explicitly stated lemma
(`WagnerPrimeCore`, equivalently its classical edge-maximal form `WagnerMaximalCore`), which is
OPEN.**  Everything in this file is proved without `sorry`; the conditional results take the
missing lemma as an explicit hypothesis and are scaffolding, not closure.

Definitions.

* `IsWagnerPiece H S`: `H[S]` is a spanning subgraph of a copy of the Wagner graph `V₈`
  (`wagnerGraph`) on the eight vertices `S`.
* `K5Decomp H S`: leaves are planar pieces (`IsPlanar (H[S])`) or `V₈`-pieces; internal nodes
  glue two pieces `A`, `B` (neither containing the other) along a **retained** clique `A ∩ B` of
  order at most three, with no edge of `H` between `A \ B` and `B \ A`.
* `IsGoodSep H S A B`: a separation of `S` of order at most three, both private parts nonempty,
  whose two clique-completed sides `pieceGraph H A (A ∩ B)`, `pieceGraph H B (A ∩ B)` are
  `K_5`-minor-free.
* `WagnerPrimeCore V` (OPEN): every nonplanar `K_5`-minor-free graph without separations of order
  at most two is a `V₈`-piece or has a good separation.

Unconditional results.

* `k5MinorFree_of_k5Decomp`: every certified graph is `K_5`-minor-free (easy direction).
* `k5MinorFree_pieceGraph_of_roots`, `k5MinorFree_pieceGraph_of_rootedClique`: a rooted clique
  on the separator inside one side makes the clique-completed other side a minor of `H`.
* `isGoodSep_of_rootedClique`, `isGoodSep_of_yDelta`, `k5MinorFree_pieceGraph_of_triangle_edge`:
  sources of good separations (rooted cliques on both sides; a vertex of degree three whose
  `Y–Δ` replacement stays `K_5`-minor-free, automatically so if its neighbourhood has an edge).
* `exists_isMaxK5Free`, `isClique_of_isGoodSep`: edge-maximal `K_5`-minor-free supergraphs exist,
  and in them good separators are cliques.
* Reductions of the missing lemma: `wagnerPrimeCore_of_internal` (to graphs with no rooted-clique
  separation and in which every `Y–Δ` creates a `K_5` minor) and `wagnerPrimeCore_of_maximal`
  (to the classical statement: an edge-maximal `K_5`-minor-free graph without separations of order
  at most two and without separating triangles is planar or a `V₈`-piece).

Conditional results (hypothesis `WagnerPrimeCore V`).

* `exists_k5Decomp_of_support_of_core`, `exists_k5Decomp_of_core`: the recursion.  Separations of
  order at most two are handled exactly as in `WagnerA` (minimum order, paths through the other
  side, `k5MinorFree_pieces_of_minSep`); planar pieces are leaves; nonplanar pieces without small
  separations are split by the core.
* `k5MinorFree_iff_exists_k5Decomp_of_core`: both directions.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- `H[S]` is a spanning subgraph of a copy of the Wagner graph on the vertex set `S`: an
injection `f : Fin 8 → V` onto `S` such that every edge of `H` between vertices of `S` is the
image of an edge of `V₈`. -/
def IsWagnerPiece (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ f : Fin 8 → V, Function.Injective f ∧ (∀ i, f i ∈ S) ∧ (∀ v ∈ S, ∃ i, f i = v) ∧
    ∀ i j, H.Adj (f i) (f j) → wagnerGraph.Adj i j

/-- A `V₈`-piece is `K_5`-minor-free. -/
theorem k5MinorFree_restrict_of_isWagnerPiece {H : SimpleGraph V} {S : Finset V}
    (h : IsWagnerPiece H S) : K5MinorFree (restrict H ↑S) := by
  classical
  obtain ⟨f, hf, hfS, hSf, hadj⟩ := h
  choose! g hg using hSf
  refine cliqueMinorFree_of_transport (by norm_num) (↑S) (fun x y hxy => hxy.2.1)
    (fun x => {g x}) (fun x _ => by rw [Finset.coe_singleton]; exact connSet_singleton _ _)
    (fun x hx y hy hxy => ?_) (fun x y hxy => ?_) cliqueMinorFree_five_wagnerGraph
  · rw [Finset.disjoint_singleton]
    intro he
    apply hxy
    rw [← hg x hx, ← hg y hy, he]
  · obtain ⟨h1, hx, hy⟩ := hxy
    refine ⟨g x, Finset.mem_singleton_self _, g y, Finset.mem_singleton_self _, hadj _ _ ?_⟩
    rw [hg x hx, hg y hy]; exact h1

variable [DecidableEq V]

/-- **Wagner certificate for `K_5`-minor-free graphs** on the vertex set `S` of `H`.  Leaves are
planar pieces or `V₈`-pieces; internal nodes glue two pieces `A`, `B` (neither containing the
other) along a retained clique `A ∩ B` of order at most three, with no edges of `H` between
`A \ B` and `B \ A` (clique-sums of order at most three whose separator edges are kept). -/
inductive K5Decomp (H : SimpleGraph V) : Finset V → Prop
  | planar {S : Finset V} : IsPlanar (restrict H ↑S) → K5Decomp H S
  | wagner {S : Finset V} : IsWagnerPiece H S → K5Decomp H S
  | glue {A B : Finset V} : ¬ A ⊆ B → ¬ B ⊆ A → (A ∩ B).card ≤ 3 →
      (∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → H.Adj u v) →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) →
      K5Decomp H A → K5Decomp H B → K5Decomp H (A ∪ B)

omit [DecidableEq V] in
theorem IsWagnerPiece.congr {H₁ H₂ : SimpleGraph V} {S : Finset V} (hw : IsWagnerPiece H₁ S)
    (h : ∀ u ∈ S, ∀ v ∈ S, H₁.Adj u v ↔ H₂.Adj u v) : IsWagnerPiece H₂ S := by
  obtain ⟨f, hf, hfS, hSf, hadj⟩ := hw
  exact ⟨f, hf, hfS, hSf, fun i j hij => hadj i j ((h _ (hfS i) _ (hfS j)).2 hij)⟩

/-- A certificate only depends on the edges inside the certified vertex set. -/
theorem K5Decomp.congr {H₁ H₂ : SimpleGraph V} {S : Finset V} (hd : K5Decomp H₁ S)
    (h : ∀ u ∈ S, ∀ v ∈ S, H₁.Adj u v ↔ H₂.Adj u v) : K5Decomp H₂ S := by
  induction hd with
  | planar hp => exact K5Decomp.planar (by rwa [← restrict_congr h])
  | wagner hw => exact K5Decomp.wagner (hw.congr h)
  | @glue A B hAB hBA hc hcl hnc _ _ ihA ihB =>
    have hA : ∀ u ∈ A, u ∈ A ∪ B := fun u hu => Finset.mem_union_left _ hu
    have hB : ∀ u ∈ B, u ∈ A ∪ B := fun u hu => Finset.mem_union_right _ hu
    refine K5Decomp.glue hAB hBA hc (fun u hu v hv huv => ?_) (fun u hu huB v hv hvA => ?_)
      (ihA fun u hu v hv => h u (hA u hu) v (hA v hv))
      (ihB fun u hu v hv => h u (hB u hu) v (hB v hv))
    · exact (h u (hA u (Finset.mem_inter.1 hu).1) v (hA v (Finset.mem_inter.1 hv).1)).1
        (hcl u hu v hv huv)
    · rw [← h u (hA u hu) v (hB v hv)]
      exact hnc u hu huB v hv hvA

omit [DecidableEq V] in
theorem restrict_restrict_of_subset {H : SimpleGraph V} {A T : Set V} (h : A ⊆ T) :
    restrict (restrict H T) A = restrict H A := by
  ext u v
  simp only [restrict_adj]
  exact ⟨fun ⟨⟨h1, _, _⟩, hu, hv⟩ => ⟨h1, hu, hv⟩, fun ⟨h1, hu, hv⟩ => ⟨⟨h1, h hu, h hv⟩, hu, hv⟩⟩

/-- Gluing two `K_5`-minor-free induced pieces along a retained clique keeps
`K_5`-minor-freeness. -/
theorem k5MinorFree_restrict_union {H : SimpleGraph V} {A B : Finset V}
    (hcl : ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → H.Adj u v)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v)
    (hA : K5MinorFree (restrict H ↑A)) (hB : K5MinorFree (restrict H ↑B)) :
    K5MinorFree (restrict H ↑(A ∪ B)) := by
  unfold K5MinorFree at *
  refine cliqueMinorFree_of_cliqueSum (by norm_num) (↑A) (↑B) (fun a b hab => ?_)
    (fun a ha b hb hab => ?_) ?_ ?_
  · obtain ⟨h, ha, hb⟩ := hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    by_cases haA : a ∈ A
    · by_cases hbA : b ∈ A
      · exact Or.inl ⟨haA, hbA⟩
      · have hbB := hb.resolve_left hbA
        by_cases haB : a ∈ B
        · exact Or.inr ⟨haB, hbB⟩
        · exact absurd h (hnc a haA haB b hbB hbA)
    · have haB := ha.resolve_left haA
      by_cases hbB : b ∈ B
      · exact Or.inr ⟨haB, hbB⟩
      · have hbA := hb.resolve_right hbB
        exact absurd h.symm (hnc b hbA hbB a haB haA)
  · have ha' : a ∈ A ∩ B := by exact_mod_cast ha
    have hb' : b ∈ A ∩ B := by exact_mod_cast hb
    refine ⟨hcl a ha' b hb' hab, ?_, ?_⟩
    · exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_inter.1 ha').1)
    · exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_inter.1 hb').1)
  · rw [restrict_restrict_of_subset (by intro x hx; simp_all)]; exact hA
  · rw [restrict_restrict_of_subset (by intro x hx; simp_all)]; exact hB

/-- **Easy direction of Wagner's structure theorem**: a certified piece is `K_5`-minor-free. -/
theorem k5MinorFree_of_k5Decomp [Finite V] {H : SimpleGraph V} {S : Finset V}
    (hd : K5Decomp H S) : K5MinorFree (restrict H ↑S) := by
  induction hd with
  | planar h => exact cliqueMinorFree_five_of_isPlanar h
  | wagner h => exact k5MinorFree_restrict_of_isWagnerPiece h
  | glue _ _ _ hcl hnc _ _ ihA ihB => exact k5MinorFree_restrict_union hcl hnc ihA ihB

/-- A separation of `S` of order at most three with both private parts nonempty whose two
clique-completed sides are `K_5`-minor-free. -/
def IsGoodSep (H : SimpleGraph V) (S A B : Finset V) : Prop :=
  A ∪ B = S ∧ (A ∩ B).card ≤ 3 ∧ (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) ∧
    ¬ A ⊆ B ∧ ¬ B ⊆ A ∧ K5MinorFree (pieceGraph H A (A ∩ B)) ∧
    K5MinorFree (pieceGraph H B (A ∩ B))

/-- **The prime core of Wagner's theorem** (for the vertex type `V`): a nonplanar
`K_5`-minor-free graph whose edges lie in `S`, without separations of order at most two, is a
`V₈`-piece or has a good separation of order at most three. -/
def WagnerPrimeCore (V : Type*) [DecidableEq V] : Prop :=
  ∀ (H : SimpleGraph V) (S : Finset V), (∀ u v, H.Adj u v → u ∈ S) → NoSmallSep H S →
    K5MinorFree H → ¬ IsPlanar H → IsWagnerPiece H S ∨ ∃ A B, IsGoodSep H S A B

/-- One gluing step: if both clique-completed sides of a proper separation of order at most
three carry certificates of supergraphs, so does the whole graph. -/
theorem exists_k5Decomp_glue {H : SimpleGraph V} {S A B : Finset V}
    (hS : ∀ u v, H.Adj u v → u ∈ S) (hcov : A ∪ B = S) (hcard : (A ∩ B).card ≤ 3)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A)
    (dA : ∃ HA : SimpleGraph V, pieceGraph H A (A ∩ B) ≤ HA ∧ (∀ u v, HA.Adj u v → u ∈ A) ∧
      K5Decomp HA A)
    (dB : ∃ HB : SimpleGraph V, pieceGraph H B (A ∩ B) ≤ HB ∧ (∀ u v, HB.Adj u v → u ∈ B) ∧
      K5Decomp HB B) :
    ∃ H' : SimpleGraph V, H ≤ H' ∧ (∀ u v, H'.Adj u v → u ∈ S) ∧ K5Decomp H' S := by
  obtain ⟨HA, hHA, hHAS, hdA⟩ := dA
  obtain ⟨HB, hHB, hHBS, hdB⟩ := dB
  have hSA : A ⊆ S := hcov ▸ Finset.subset_union_left
  have hSB : B ⊆ S := hcov ▸ Finset.subset_union_right
  set K := A ∩ B with hKdef
  have hHAS' : ∀ u v, HA.Adj u v → u ∈ A ∧ v ∈ A := fun u v h =>
    ⟨hHAS u v h, hHAS v u h.symm⟩
  have hHBS' : ∀ u v, HB.Adj u v → u ∈ B ∧ v ∈ B := fun u v h =>
    ⟨hHBS u v h, hHBS v u h.symm⟩
  have hKA : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → HA.Adj u v := fun u hu v hv huv =>
    hHA ⟨(Finset.mem_inter.1 hu).1, (Finset.mem_inter.1 hv).1, Or.inr ⟨hu, hv, huv⟩⟩
  have hKB : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → HB.Adj u v := fun u hu v hv huv =>
    hHB ⟨(Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hv).2, Or.inr ⟨hu, hv, huv⟩⟩
  refine ⟨HA ⊔ HB, ?_, ?_, ?_⟩
  · intro u v huv
    have huS := hS u v huv
    have hvS := hS v u huv.symm
    rw [← hcov] at huS hvS
    by_cases huA : u ∈ A
    · by_cases hvA : v ∈ A
      · exact Or.inl (hHA ⟨huA, hvA, Or.inl huv⟩)
      · have hvB := (Finset.mem_union.1 hvS).resolve_left hvA
        by_cases huB : u ∈ B
        · exact Or.inr (hHB ⟨huB, hvB, Or.inl huv⟩)
        · exact absurd huv (hnc u huA huB v hvB hvA)
    · have huB := (Finset.mem_union.1 huS).resolve_left huA
      by_cases hvB : v ∈ B
      · exact Or.inr (hHB ⟨huB, hvB, Or.inl huv⟩)
      · have hvA := (Finset.mem_union.1 hvS).resolve_right hvB
        exact absurd huv.symm (hnc v hvA hvB u huB huA)
  · intro u v huv
    rcases huv with h | h
    · exact hSA (hHAS u v h)
    · exact hSB (hHBS u v h)
  · rw [← hcov]
    have congrA : ∀ u ∈ A, ∀ v ∈ A, HA.Adj u v ↔ (HA ⊔ HB).Adj u v := by
      intro u hu v hv
      constructor
      · exact fun h => Or.inl h
      · rintro (h | h)
        · exact h
        · exact hKA u (Finset.mem_inter.2 ⟨hu, (hHBS' u v h).1⟩) v
            (Finset.mem_inter.2 ⟨hv, (hHBS' u v h).2⟩) h.ne
    have congrB : ∀ u ∈ B, ∀ v ∈ B, HB.Adj u v ↔ (HA ⊔ HB).Adj u v := by
      intro u hu v hv
      constructor
      · exact fun h => Or.inr h
      · rintro (h | h)
        · exact hKB u (Finset.mem_inter.2 ⟨(hHAS' u v h).1, hu⟩) v
            (Finset.mem_inter.2 ⟨(hHAS' u v h).2, hv⟩) h.ne
        · exact h
    refine K5Decomp.glue hAB hBA hcard (fun u hu v hv huv => Or.inl (hKA u hu v hv huv))
      (fun u hu huB v hv hvA huv => ?_) (K5Decomp.congr hdA congrA) (K5Decomp.congr hdB congrB)
    rcases huv with h | h
    · exact hvA (hHAS' u v h).2
    · exact huB (hHBS' u v h).1

omit [DecidableEq V] in
/-- **Rooted cliques on the separator.**  If every vertex `k` of `K` has a connected root set
`R k ∋ k` meeting `A` only in `k`, the root sets being pairwise disjoint and pairwise touching,
then the clique-completed piece `pieceGraph H A K` is a minor of `H`; in particular it is
`K_5`-minor-free when `H` is. -/
theorem k5MinorFree_pieceGraph_of_roots {H : SimpleGraph V} {A K : Finset V} (R : V → Finset V)
    (hmem : ∀ k ∈ K, k ∈ R k) (hA : ∀ k ∈ K, ∀ v ∈ R k, v ∈ A → v = k)
    (hdisj : ∀ k ∈ K, ∀ l ∈ K, k ≠ l → Disjoint (R k) (R l))
    (hconn : ∀ k ∈ K, ConnSet H ↑(R k))
    (htouch : ∀ k ∈ K, ∀ l ∈ K, k ≠ l → Touch H (R k) (R l))
    (hH : K5MinorFree H) : K5MinorFree (pieceGraph H A K) := by
  classical
  let φ : V → Finset V := fun v => if v ∈ K then R v else {v}
  have hφK : ∀ v ∈ K, φ v = R v := fun v hv => by simp [φ, hv]
  have hφ : ∀ v ∉ K, φ v = {v} := fun v hv => by simp [φ, hv]
  have hself : ∀ v, v ∈ φ v := fun v => by
    by_cases hv : v ∈ K
    · rw [hφK v hv]; exact hmem v hv
    · rw [hφ v hv]; exact Finset.mem_singleton_self v
  refine cliqueMinorFree_of_transport (by norm_num) (↑A) (fun u v huv => huv.1) φ
    (fun v _ => ?_) (fun v hv w hw hvw => ?_) (fun v w hvw => ?_) hH
  · by_cases hvK : v ∈ K
    · rw [hφK v hvK]; exact hconn v hvK
    · rw [hφ v hvK, Finset.coe_singleton]; exact connSet_singleton _ _
  · have hv' : v ∈ A := by exact_mod_cast hv
    have hw' : w ∈ A := by exact_mod_cast hw
    by_cases hvK : v ∈ K <;> by_cases hwK : w ∈ K
    · rw [hφK v hvK, hφK w hwK]; exact hdisj v hvK w hwK hvw
    · rw [hφK v hvK, hφ w hwK, Finset.disjoint_singleton_right]
      exact fun h => hvw (hA v hvK w h hw').symm
    · rw [hφ v hvK, hφK w hwK, Finset.disjoint_singleton_left]
      exact fun h => hvw (hA w hwK v h hv')
    · rw [hφ v hvK, hφ w hwK, Finset.disjoint_singleton]; exact hvw
  · obtain ⟨-, -, hadj | ⟨hv, hw, hne⟩⟩ := hvw
    · exact ⟨v, hself v, w, hself w, hadj⟩
    · rw [hφK v hv, hφK w hw]; exact htouch v hv w hw hne

/-- **Y–Δ inside a minor.**  If `c` has exactly the neighbours `x, y, z` inside `A ∪ {c}` and
`yz` is an edge, then replacing `c` by a triangle on `{x, y, z}` gives a minor: contract `c`
into `x`. -/
theorem k5MinorFree_pieceGraph_of_triangle_edge {H : SimpleGraph V} {A : Finset V} {c x y z : V}
    (hc : c ∉ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hcx : H.Adj c x) (hcy : H.Adj c y)
    (hcz : H.Adj c z) (hyz' : H.Adj y z) (hH : K5MinorFree H) :
    K5MinorFree (pieceGraph H A {x, y, z}) := by
  have hcx' : c ≠ x := hcx.ne
  refine k5MinorFree_pieceGraph_of_roots (fun v => if v = x then {x, c} else {v})
    (fun k hk => ?_) (fun k hk v hv hvA => ?_) (fun k hk l hl hkl => ?_) (fun k hk => ?_)
    (fun k hk l hl hkl => ?_) hH
  · by_cases h : k = x
    · simp [h]
    · simp [h]
  · by_cases h : k = x
    · simp only [h, ite_true, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      rcases hv with rfl | rfl
      · rfl
      · exact absurd hvA hc
    · simp only [h, ite_false, Finset.mem_singleton] at hv; exact hv
  · have hcy' : c ≠ y := hcy.ne
    have hcz' : c ≠ z := hcz.ne
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
    rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
      simp only [Finset.mem_insert, Finset.mem_singleton,
        Ne.symm hxy, Ne.symm hxz, ite_true, ite_false] at ha hb <;>
      first
      | exact hkl rfl
      | (rcases ha with rfl | rfl <;> simp_all)
  · by_cases h : k = x
    · simp only [h, ite_true]
      rw [Finset.coe_insert, Finset.coe_singleton, Set.pair_comm]
      exact (connSet_singleton H x).insert_adj rfl hcx
    · simp only [h, ite_false, Finset.coe_singleton]; exact connSet_singleton H k
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
    rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl
    · exact absurd rfl hkl
    · exact ⟨c, by simp, l, by simp [Ne.symm hkl], hcy⟩
    · exact ⟨c, by simp, l, by simp [Ne.symm hkl], hcz⟩
    · exact ⟨k, by simp [hkl], c, by simp, hcy.symm⟩
    · exact absurd rfl hkl
    · exact ⟨k, by simp [Ne.symm hxy], l, by simp [Ne.symm hxz], hyz'⟩
    · exact ⟨k, by simp [hkl], c, by simp, hcz.symm⟩
    · exact ⟨k, by simp [Ne.symm hxz], l, by simp [Ne.symm hxy], hyz'.symm⟩
    · exact absurd rfl hkl

/-- A **rooted clique on `K` inside `B`**: every `k ∈ K` has a connected root set `R k ⊆ B`
containing `k` and no other vertex of `K`, the root sets being pairwise disjoint and pairwise
touching (a `K_{|K|}` minor of `H[B]` whose branch sets are rooted at the vertices of `K`). -/
def RootedClique (H : SimpleGraph V) (B K : Finset V) : Prop :=
  ∃ R : V → Finset V, (∀ k ∈ K, k ∈ R k ∧ R k ⊆ B ∧ ConnSet H ↑(R k) ∧ ∀ v ∈ R k, v ∈ K → v = k) ∧
    ∀ k ∈ K, ∀ l ∈ K, k ≠ l → Disjoint (R k) (R l) ∧ Touch H (R k) (R l)

/-- If the side `B` carries a rooted clique on the separator `A ∩ B`, the clique-completed side
`A` is a minor of `H`, hence `K_5`-minor-free. -/
theorem k5MinorFree_pieceGraph_of_rootedClique {H : SimpleGraph V} {A B : Finset V}
    (hR : RootedClique H B (A ∩ B)) (hH : K5MinorFree H) :
    K5MinorFree (pieceGraph H A (A ∩ B)) := by
  obtain ⟨R, h1, h2⟩ := hR
  refine k5MinorFree_pieceGraph_of_roots R (fun k hk => (h1 k hk).1)
    (fun k hk v hv hvA => (h1 k hk).2.2.2 v hv
      (Finset.mem_inter.2 ⟨hvA, (h1 k hk).2.1 hv⟩))
    (fun k hk l hl hkl => (h2 k hk l hl hkl).1) (fun k hk => (h1 k hk).2.2.1)
    (fun k hk l hl hkl => (h2 k hk l hl hkl).2) hH

/-- A proper separation of order at most three with rooted cliques on the separator on both
sides is good. -/
theorem isGoodSep_of_rootedClique {H : SimpleGraph V} {S A B : Finset V} (hcov : A ∪ B = S)
    (hcard : (A ∩ B).card ≤ 3) (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v)
    (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) (hRA : RootedClique H A (A ∩ B))
    (hRB : RootedClique H B (A ∩ B)) (hH : K5MinorFree H) : IsGoodSep H S A B := by
  refine ⟨hcov, hcard, hnc, hAB, hBA, k5MinorFree_pieceGraph_of_rootedClique hRB hH, ?_⟩
  have := k5MinorFree_pieceGraph_of_rootedClique (A := B) (B := A) (by rwa [Finset.inter_comm])
    hH
  rwa [Finset.inter_comm] at this

/-- **Separating a vertex of degree three.**  If all neighbours of `c ∈ S` lie in a
three-element set `K ⊆ S \ {c}`, `|S| ≥ 5`, and replacing `c` by a triangle on `K` keeps the graph
`K_5`-minor-free, then `(K ∪ {c}, S \ {c})` is a good separation. -/
theorem isGoodSep_of_yDelta {H : SimpleGraph V} {S K : Finset V} {c : V} (hcS : c ∈ S)
    (hKS : K ⊆ S) (hcK : c ∉ K) (hK : K.card = 3) (hS : 5 ≤ S.card)
    (hc : ∀ v, H.Adj c v → v ∈ K) (h5 : K5MinorFree (pieceGraph H (S.erase c) K)) :
    IsGoodSep H S (insert c K) (S.erase c) := by
  have hinter : insert c K ∩ S.erase c = K := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | h, hne, -⟩
      · exact absurd rfl hne
      · exact h
    · intro h
      exact ⟨Or.inr h, fun (he : v = c) => hcK (he ▸ h), hKS h⟩
  refine ⟨?_, by rw [hinter, hK], ?_, ?_, ?_, ?_, by rwa [hinter]⟩
  · ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((rfl | h) | ⟨-, h⟩)
      · exact hcS
      · exact hKS h
      · exact h
    · intro hv
      by_cases hvc : v = c
      · exact Or.inl (Or.inl hvc)
      · exact Or.inr ⟨hvc, hv⟩
  · intro u hu huB v hv hvA huv
    have huc : u = c := by
      rcases Finset.mem_insert.1 hu with h | h
      · exact h
      · exact absurd (Finset.mem_erase.2 ⟨fun (he : u = c) => hcK (he ▸ h), hKS h⟩) huB
    subst huc
    exact hvA (Finset.mem_insert_of_mem (hc v huv))
  · intro h
    exact (Finset.mem_erase.1 (h (Finset.mem_insert_self c K))).1 rfl
  · intro h
    have hsub : S ⊆ insert c K := by
      intro v hv
      by_cases hvc : v = c
      · rw [hvc]; exact Finset.mem_insert_self c K
      · exact h (Finset.mem_erase.2 ⟨hvc, hv⟩)
    have := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le c K
    omega
  · rw [hinter]
    refine cliqueMinorFree_of_edges_subset (by norm_num) (insert c K)
      (fun a b hab => hab.1) ?_
    have := Finset.card_insert_le c K
    omega

/-- **Internal form of the prime core.**  The prime core restricted to graphs in which no
proper separation of order at most three has rooted cliques on both sides, and in which every
vertex `c` whose neighbours lie in a three-element set `K` is such that replacing `c` by a
triangle on `K` creates a `K_5` minor.  (These are the graphs in which no good separation is
produced by `isGoodSep_of_rootedClique` or `isGoodSep_of_yDelta`.) -/
def WagnerInternalCore (V : Type*) [DecidableEq V] : Prop :=
  ∀ (H : SimpleGraph V) (S : Finset V), (∀ u v, H.Adj u v → u ∈ S) → NoSmallSep H S →
    K5MinorFree H → ¬ IsPlanar H →
    (∀ A B : Finset V, A ∪ B = S → (A ∩ B).card ≤ 3 →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) → ¬ A ⊆ B → ¬ B ⊆ A →
      ¬ (RootedClique H A (A ∩ B) ∧ RootedClique H B (A ∩ B))) →
    (∀ c ∈ S, ∀ K : Finset V, K ⊆ S → c ∉ K → K.card = 3 → (∀ v, H.Adj c v → v ∈ K) →
      ¬ K5MinorFree (pieceGraph H (S.erase c) K)) →
    IsWagnerPiece H S

/-- The internal form of the prime core implies the prime core. -/
theorem wagnerPrimeCore_of_internal [Finite V] (h : WagnerInternalCore V) :
    WagnerPrimeCore V := by
  intro H S hS hns h5 hpl
  by_contra hcon
  push Not at hcon
  obtain ⟨hw, hgood⟩ := hcon
  have hS5 : 5 ≤ S.card := by
    by_contra hlt
    exact hpl (isPlanar_of_card_le_four hS (by omega))
  refine hw (h H S hS hns h5 hpl (fun A B hcov hcard hnc hAB hBA hR => ?_)
    (fun c hc K hKS hcK hK hcK' hK5 => ?_))
  · exact hgood A B (isGoodSep_of_rootedClique hcov hcard hnc hAB hBA hR.1 hR.2 h5)
  · exact hgood _ _ (isGoodSep_of_yDelta hc hKS hcK hK hS5 hcK' hK5)

/-- A proper separation of order at most two of minimum order has `K_5`-minor-free
clique-completed sides. -/
theorem k5MinorFree_pieces_of_minSep {H : SimpleGraph V} {S A B : Finset V}
    (hsep : IsSmallSep H S A B)
    (hmin : ∀ A' B', IsSmallSep H S A' B' → (A ∩ B).card ≤ (A' ∩ B').card)
    (h5 : K5MinorFree H) :
    K5MinorFree (pieceGraph H A (A ∩ B)) ∧ K5MinorFree (pieceGraph H B (A ∩ B)) := by
  obtain ⟨hcov, hcard, hnc, hAB, hBA⟩ := hsep
  set K := A ∩ B with hKdef
  by_cases hcl : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → H.Adj u v
  · exact ⟨k5MinorFree_pieceGraph_of_clique hcl h5, k5MinorFree_pieceGraph_of_clique hcl h5⟩
  push Not at hcl
  obtain ⟨x, hx, y, hy, hxy, -⟩ := hcl
  have hK2 : K = {x, y} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    · rw [Finset.card_pair hxy]; exact hcard
  have hmin2 : ∀ A' B', IsSmallSep H S A' B' → 2 ≤ (A' ∩ B').card := by
    intro A' B' h'
    have := hmin A' B' h'
    rw [hK2, Finset.card_pair hxy] at this
    exact this
  obtain ⟨C, hCsub, hCconn, hCx, hCy⟩ :=
    exists_path_of_minSep ⟨hcov, hcard, hnc, hAB, hBA⟩ hK2 hmin2
  have hK2' : B ∩ A = {x, y} := by rw [Finset.inter_comm]; exact hK2
  obtain ⟨C', hC'sub, hC'conn, hC'x, hC'y⟩ :=
    exists_path_of_minSep (IsSmallSep.symm ⟨hcov, hcard, hnc, hAB, hBA⟩) hK2'
      (fun A' B' h' => hmin2 A' B' h')
  have hdA : Disjoint C A :=
    Finset.disjoint_left.2 fun w hw hwA => (Finset.mem_sdiff.1 (hCsub hw)).2 hwA
  have hdB : Disjoint C' B :=
    Finset.disjoint_left.2 fun w hw hwB => (Finset.mem_sdiff.1 (hC'sub hw)).2 hwB
  rw [hK2]
  exact ⟨k5MinorFree_pieceGraph_of_path hxy C hdA hCconn hCx hCy h5,
    k5MinorFree_pieceGraph_of_path hxy C' hdB hC'conn hC'x hC'y h5⟩

/-- The recursion behind Wagner's structure theorem, given the prime core: every
`K_5`-minor-free graph whose edges lie in `S` is a spanning subgraph of a certified graph. -/
theorem exists_k5Decomp_of_support_of_core (hcore : WagnerPrimeCore V) :
    ∀ (n : ℕ) (H : SimpleGraph V) (S : Finset V), S.card = n →
    (∀ u v, H.Adj u v → u ∈ S) → K5MinorFree H →
    ∃ H' : SimpleGraph V, H ≤ H' ∧ (∀ u v, H'.Adj u v → u ∈ S) ∧ K5Decomp H' S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H S hn hS h5
  -- recursion on a proper separation with good sides
  have recurse : ∀ A B, A ∪ B = S → (A ∩ B).card ≤ 3 →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) → ¬ A ⊆ B → ¬ B ⊆ A →
      K5MinorFree (pieceGraph H A (A ∩ B)) → K5MinorFree (pieceGraph H B (A ∩ B)) →
      ∃ H' : SimpleGraph V, H ≤ H' ∧ (∀ u v, H'.Adj u v → u ∈ S) ∧ K5Decomp H' S := by
    intro A B hcov hcard hnc hAB hBA hpA hpB
    have hSA : A ⊆ S := hcov ▸ Finset.subset_union_left
    have hSB : B ⊆ S := hcov ▸ Finset.subset_union_right
    have hltA : A.card < n := by
      rw [← hn]
      obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.1 hBA
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hSA,
        fun h => hbA (h ▸ hSB hbB)⟩)
    have hltB : B.card < n := by
      rw [← hn]
      obtain ⟨a, haA, haB⟩ := Finset.not_subset.1 hAB
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hSB,
        fun h => haB (h ▸ hSA haA)⟩)
    exact exists_k5Decomp_glue hS hcov hcard hnc hAB hBA
      (ih _ hltA (pieceGraph H A (A ∩ B)) A rfl (fun u v huv => huv.1) hpA)
      (ih _ hltB (pieceGraph H B (A ∩ B)) B rfl (fun u v huv => huv.1) hpB)
  by_cases hpl : IsPlanar H
  · exact ⟨H, le_rfl, hS, K5Decomp.planar (by rwa [restrict_eq_self hS])⟩
  by_cases hns : NoSmallSep H S
  · rcases hcore H S hS hns h5 hpl with hw | ⟨A, B, hcov, hcard, hnc, hAB, hBA, hpA, hpB⟩
    · exact ⟨H, le_rfl, hS, K5Decomp.wagner hw⟩
    · exact recurse A B hcov hcard hnc hAB hBA hpA hpB
  -- a separation of minimum order at most two
  classical
  have hex : ∃ k, ∃ A B, IsSmallSep H S A B ∧ (A ∩ B).card = k := by
    unfold NoSmallSep at hns
    push Not at hns
    obtain ⟨A, B, h1, h2, h3, h4, h5⟩ := hns
    exact ⟨_, A, B, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
  obtain ⟨A, B, hsep, hk⟩ := Nat.find_spec hex
  have hmin : ∀ A' B', IsSmallSep H S A' B' → (A ∩ B).card ≤ (A' ∩ B').card := by
    intro A' B' h'
    rw [hk]; exact Nat.find_min' hex ⟨A', B', h', rfl⟩
  obtain ⟨hpA, hpB⟩ := k5MinorFree_pieces_of_minSep hsep hmin h5
  obtain ⟨hcov, hcard, hnc, hAB, hBA⟩ := hsep
  exact recurse A B hcov (by omega) hnc hAB hBA hpA hpB

/-- **Wagner's structure theorem, conditional on the prime core** (scaffolding, not closure):
if `WagnerPrimeCore V` holds, every finite `K_5`-minor-free graph is a spanning subgraph of a
graph with a `K5Decomp` certificate on all vertices. -/
theorem exists_k5Decomp_of_core [Fintype V] (hcore : WagnerPrimeCore V)
    (G : SimpleGraph V) (hG : K5MinorFree G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ K5Decomp H Finset.univ := by
  obtain ⟨H, hGH, -, hd⟩ := exists_k5Decomp_of_support_of_core hcore _ G Finset.univ rfl
    (fun _ _ _ => Finset.mem_univ _) hG
  exact ⟨H, hGH, hd⟩

/-- **Wagner's structure theorem, both directions, conditional on the prime core**
(scaffolding, not closure): if `WagnerPrimeCore V` holds, a finite graph has no `K_5` minor iff
it is a spanning subgraph of a graph with a `K5Decomp` certificate.  The direction `←` is
unconditional (`k5MinorFree_of_k5Decomp`). -/
theorem k5MinorFree_iff_exists_k5Decomp_of_core [Fintype V] (hcore : WagnerPrimeCore V)
    (G : SimpleGraph V) : K5MinorFree G ↔ ∃ H : SimpleGraph V, G ≤ H ∧ K5Decomp H Finset.univ := by
  refine ⟨exists_k5Decomp_of_core hcore G, ?_⟩
  rintro ⟨H, hGH, hd⟩
  have h := k5MinorFree_of_k5Decomp hd
  have he : restrict H ↑(Finset.univ : Finset V) = H := by
    ext u v; simp [restrict_adj]
  rw [he] at h
  exact CliqueMinorFree.anti h hGH


/-! ### Reduction to edge-maximal graphs -/

/-- `M` is **edge-maximal `K_5`-minor-free on `S`**: its edges lie in `S`, it has no `K_5`
minor, and adding any missing edge between two vertices of `S` creates a `K_5` minor. -/
def IsMaxK5Free (M : SimpleGraph V) (S : Finset V) : Prop :=
  (∀ u v, M.Adj u v → u ∈ S) ∧ K5MinorFree M ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ M.Adj u v → ¬ K5MinorFree (addEdgeGraph M u v)

/-- Separations only disappear when edges are added. -/
theorem NoSmallSep.mono {H M : SimpleGraph V} {S : Finset V}
    (h : NoSmallSep H S) (hle : H ≤ M) : NoSmallSep M S :=
  fun A B hcov hcard hnc => h A B hcov hcard fun u hu huB v hv hvA huv =>
    hnc u hu huB v hv hvA (hle huv)

open scoped Classical in
/-- Every `K_5`-minor-free graph with edges in a finite set `S` has an edge-maximal
`K_5`-minor-free supergraph on `S`. -/
theorem exists_isMaxK5Free_aux (S : Finset V) : ∀ (n : ℕ) (H : SimpleGraph V),
    ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2)).card = n →
    (∀ u v, H.Adj u v → u ∈ S) → K5MinorFree H → ∃ M, H ≤ M ∧ IsMaxK5Free M S := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hS h5
  by_cases hmax : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ H.Adj u v → ¬ K5MinorFree (addEdgeGraph H u v)
  · exact ⟨H, le_rfl, hS, h5, hmax⟩
  push Not at hmax
  obtain ⟨u, hu, v, hv, huv, hnadj, h5'⟩ := hmax
  have hle : H ≤ addEdgeGraph H u v := fun a b h => Or.inl h
  have hlt : ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ ¬ (addEdgeGraph H u v).Adj p.1 p.2)).card
      < n := by
    rw [← hn]
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩)
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1, fun h => hp.2.2 (hle h)⟩
    · intro heq
      have hmem : (u, v) ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2) := by
        simp [hu, hv, huv, hnadj]
      rw [← heq] at hmem
      simp only [Finset.mem_filter] at hmem
      exact hmem.2.2 ((addEdgeGraph_adj huv u v).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  obtain ⟨M, hM, hMmax⟩ := ih _ hlt (addEdgeGraph H u v) rfl (fun a b h => by
    rcases (addEdgeGraph_adj huv a b).1 h with h | h | h
    · exact hS a b h
    · rw [h.1]; exact hu
    · rw [h.1]; exact hv) h5'
  exact ⟨M, hle.trans hM, hMmax⟩

omit [DecidableEq V] in
theorem exists_isMaxK5Free {H : SimpleGraph V} {S : Finset V} (hS : ∀ u v, H.Adj u v → u ∈ S)
    (h5 : K5MinorFree H) : ∃ M, H ≤ M ∧ IsMaxK5Free M S := by
  classical
  exact exists_isMaxK5Free_aux S _ H rfl hS h5

/-- In an edge-maximal `K_5`-minor-free graph the separator of a good separation is a clique. -/
theorem isClique_of_isGoodSep {M : SimpleGraph V} {S A B : Finset V} (hM : IsMaxK5Free M S)
    (hg : IsGoodSep M S A B) : ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → M.Adj u v := by
  obtain ⟨hS, -, hmax⟩ := hM
  obtain ⟨hcov, -, hnc, -, -, hpA, hpB⟩ := hg
  intro u hu v hv huv
  by_contra hnadj
  have huS : u ∈ S := hcov ▸ Finset.mem_union_left _ (Finset.mem_inter.1 hu).1
  have hvS : v ∈ S := hcov ▸ Finset.mem_union_left _ (Finset.mem_inter.1 hv).1
  apply hmax u huS v hvS huv hnadj
  set K := A ∩ B
  set G := pieceGraph M A K ⊔ pieceGraph M B K
  have hG : K5MinorFree G := by
    unfold K5MinorFree
    refine cliqueMinorFree_of_cliqueSum (by norm_num) (↑A) (↑B) (fun a b hab => ?_)
      (fun a ha b hb hab => ?_) ?_ ?_
    · rcases hab with h | h
      · exact Or.inl ⟨h.1, h.2.1⟩
      · exact Or.inr ⟨h.1, h.2.1⟩
    · have ha' : a ∈ K := by exact_mod_cast ha
      have hb' : b ∈ K := by exact_mod_cast hb
      exact Or.inl ⟨(Finset.mem_inter.1 ha').1, (Finset.mem_inter.1 hb').1, Or.inr ⟨ha', hb', hab⟩⟩
    · refine CliqueMinorFree.anti hpA fun a b hab => ?_
      obtain ⟨h, ha, hb⟩ := hab
      rcases h with h | h
      · exact h
      · refine ⟨ha, hb, ?_⟩
        obtain ⟨haB, hbB, h'⟩ := h
        rcases h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
    · refine CliqueMinorFree.anti hpB fun a b hab => ?_
      obtain ⟨h, ha, hb⟩ := hab
      rcases h with h | h
      · obtain ⟨haA, hbA, h'⟩ := h
        exact ⟨ha, hb, h'⟩
      · exact h
  refine CliqueMinorFree.anti hG fun a b hab => ?_
  rcases (addEdgeGraph_adj huv a b).1 hab with h | h | h
  · have haS := hS a b h
    have hbS := hS b a h.symm
    rw [← hcov] at haS hbS
    by_cases haA : a ∈ A
    · by_cases hbA : b ∈ A
      · exact Or.inl ⟨haA, hbA, Or.inl h⟩
      · have hbB := (Finset.mem_union.1 hbS).resolve_left hbA
        by_cases haB : a ∈ B
        · exact Or.inr ⟨haB, hbB, Or.inl h⟩
        · exact absurd h (hnc a haA haB b hbB hbA)
    · have haB := (Finset.mem_union.1 haS).resolve_left haA
      by_cases hbB : b ∈ B
      · exact Or.inr ⟨haB, hbB, Or.inl h⟩
      · have hbA := (Finset.mem_union.1 hbS).resolve_right hbB
        exact absurd h.symm (hnc b hbA hbB a haB haA)
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨(Finset.mem_inter.1 hu).1, (Finset.mem_inter.1 hv).1, Or.inr ⟨hu, hv, huv⟩⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨(Finset.mem_inter.1 hv).1, (Finset.mem_inter.1 hu).1,
      Or.inr ⟨hv, hu, Ne.symm huv⟩⟩

/-- **Classical form of the prime core**: an edge-maximal `K_5`-minor-free graph on `S` without
separations of order at most two and without proper separations of order at most three whose
separator is a clique (no separating triangles) is planar or a `V₈`-piece. -/
def WagnerMaximalCore (V : Type*) [DecidableEq V] : Prop :=
  ∀ (M : SimpleGraph V) (S : Finset V), IsMaxK5Free M S → NoSmallSep M S → ¬ IsPlanar M →
    (∀ A B : Finset V, A ∪ B = S → (A ∩ B).card ≤ 3 →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v) → ¬ A ⊆ B → ¬ B ⊆ A →
      ¬ ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → M.Adj u v) →
    IsWagnerPiece M S

/-- The classical (edge-maximal) form of the prime core implies the prime core. -/
theorem wagnerPrimeCore_of_maximal [Finite V] (h : WagnerMaximalCore V) : WagnerPrimeCore V := by
  intro H S hS hns h5 hpl
  obtain ⟨M, hHM, hM⟩ := exists_isMaxK5Free hS h5
  have hMpl : ¬ IsPlanar M := fun hp => hpl (hp.mono hHM)
  -- transfer of conclusions from `M` to `H`
  have hgood : ∀ A B, IsGoodSep M S A B → IsGoodSep H S A B := by
    rintro A B ⟨hcov, hcard, hnc, hAB, hBA, hpA, hpB⟩
    refine ⟨hcov, hcard, fun u hu huB v hv hvA huv => hnc u hu huB v hv hvA (hHM huv), hAB, hBA,
      CliqueMinorFree.anti hpA ?_, CliqueMinorFree.anti hpB ?_⟩ <;>
    · rintro a b ⟨ha, hb, h | h⟩
      · exact ⟨ha, hb, Or.inl (hHM h)⟩
      · exact ⟨ha, hb, Or.inr h⟩
  by_cases hcl : ∃ A B : Finset V, A ∪ B = S ∧ (A ∩ B).card ≤ 3 ∧
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ M.Adj u v) ∧ ¬ A ⊆ B ∧ ¬ B ⊆ A ∧
      ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → M.Adj u v
  · obtain ⟨A, B, hcov, hcard, hnc, hAB, hBA, hK⟩ := hcl
    exact Or.inr ⟨A, B, hgood A B ⟨hcov, hcard, hnc, hAB, hBA,
      k5MinorFree_pieceGraph_of_clique hK hM.2.1, k5MinorFree_pieceGraph_of_clique hK hM.2.1⟩⟩
  push Not at hcl
  have hw := h M S hM (hns.mono hHM) hMpl fun A B hcov hcard hnc hAB hBA hK => by
    obtain ⟨u, hu, v, hv, huv, hn⟩ := hcl A B hcov hcard hnc hAB hBA
    exact hn (hK u hu v hv huv)
  obtain ⟨f, hf, hfS, hSf, hadj⟩ := hw
  exact Or.inl ⟨f, hf, hfS, hSf, fun i j hij => hadj i j (hHM hij)⟩

end LeanPool.K5MinorFreeChoosability
