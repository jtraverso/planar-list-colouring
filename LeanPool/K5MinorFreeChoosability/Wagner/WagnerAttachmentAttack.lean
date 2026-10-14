/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerRigidity

/-!
# Attachments to an actual copy of the Wagner graph

A connected set disjoint from a copy of `V₈` cannot touch two nonadjacent copied
vertices in a `K₅`-minor-free graph. Contracting that set into one attachment
would create a forbidden chord. Hence every such component has at most two
attachments. With `NoSmallSep`, an actual copy of `V₈` must therefore span the
support. This does not yet convert an arbitrary `V₈` minor into a copy.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- An outside connected set cannot provide a missing chord of `V₈`. -/
theorem wagner_attachment_adj (h5 : K5MinorFree G) (f : Fin 8 → V)
    (hf : Function.Injective f)
    (hW : ∀ a b, wagnerGraph.Adj a b → G.Adj (f a) (f b))
    (X : Finset V) (hX : ConnSet G ↑X) (hdis : ∀ a, f a ∉ X)
    {i j : Fin 8} (hij : i ≠ j)
    (hi : ∃ x ∈ X, G.Adj (f i) x) (hj : ∃ x ∈ X, G.Adj (f j) x) :
    wagnerGraph.Adj i j := by
  classical
  by_contra hn
  let φ : Fin 8 → Finset V := fun a => if a = i then insert (f i) X else {f a}
  have hmem : ∀ a, f a ∈ φ a := by
    intro a
    by_cases ha : a = i <;> simp [φ, ha]
  have hc : ∀ a, ConnSet G ↑(φ a) := by
    intro a
    by_cases ha : a = i
    · obtain ⟨x, hx, hix⟩ := hi
      simpa [φ, ha] using hX.insert_adj hx hix
    · simpa [φ, ha] using connSet_singleton G (f a)
  have hd : ∀ a b, a ≠ b → Disjoint (φ a) (φ b) := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact hab (ha.trans hb.symm)
    · simp only [φ, ite_eq_left ha, ite_eq_right hb, Finset.mem_insert,
        Finset.mem_singleton] at hva hvb
      subst v
      rcases hva with he | hx
      · exact hab (ha.trans (hf he.symm))
      · exact hdis b hx
    · simp only [φ, ite_eq_right ha, ite_eq_left hb, Finset.mem_insert,
        Finset.mem_singleton] at hva hvb
      subst v
      rcases hvb with he | hx
      · exact hab ((hf he).trans hb.symm)
      · exact hdis a hx
    · simp only [φ, ite_eq_right ha, ite_eq_right hb, Finset.mem_singleton] at hva hvb
      exact hab (hf (hva.symm.trans hvb))
  have hadj : ∀ a b, (addEdgeGraph wagnerGraph i j).Adj a b →
      ∃ u ∈ φ a, ∃ v ∈ φ b, G.Adj u v := by
    intro a b hab
    rcases hab with hab | ⟨_, hab⟩
    · exact ⟨f a, hmem a, f b, hmem b, hW a b hab⟩
    · rcases hab with ⟨hai, hbj⟩ | ⟨haj, hbi⟩
      · rw [hai, hbj]
        obtain ⟨x, hx, hjx⟩ := hj
        exact ⟨x, by simp [φ, hx], f j, hmem j, hjx.symm⟩
      · rw [haj, hbi]
        obtain ⟨x, hx, hjx⟩ := hj
        exact ⟨f j, hmem j, x, by simp [φ, hx], hjx⟩
  have hp : K5MinorFree (addEdgeGraph wagnerGraph i j) :=
    cliqueMinorFree_of_transport (by decide) Set.univ (fun _ _ _ => Set.mem_univ _)
      φ (fun a _ => hc a) (fun a _ b _ hab => hd a b hab) hadj h5
  exact not_k5MinorFree_of_wagner_plus_edge id Function.injective_id
    (fun _ _ h => Or.inl h) hij hn (Or.inr ⟨hij, Or.inl ⟨rfl, rfl⟩⟩) hp

/-- A clique in the triangle-free Wagner graph has at most two vertices. -/
theorem wagner_clique_card_le_two : ∀ K : Finset (Fin 8),
    (∀ i ∈ K, ∀ j ∈ K, i ≠ j → wagnerGraph.Adj i j) → K.card ≤ 2 := by
  intro K h
  by_contra hn
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge hn)
  exact wagnerGraph_no_triangle a b c (h a ha b hb hab) (h b hb c hc hbc)
    (h a ha c hc hac)

omit [DecidableEq V] in
/-- Indices of copied vertices touching an outside finite set. -/
noncomputable def wagnerAttachments (G : SimpleGraph V) (f : Fin 8 → V) (X : Finset V) :
    Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun a => ∃ x ∈ X, G.Adj (f a) x

omit [DecidableEq V] in
/-- The attachment indices of any outside connected set form a clique, of size at most two. -/
theorem wagner_attachment_card_le_two (h5 : K5MinorFree G) (f : Fin 8 → V)
    (hf : Function.Injective f)
    (hW : ∀ a b, wagnerGraph.Adj a b → G.Adj (f a) (f b))
    (X : Finset V) (hX : ConnSet G ↑X) (hdis : ∀ a, f a ∉ X) :
    (wagnerAttachments G f X).card ≤ 2 := by
  classical
  apply wagner_clique_card_le_two
  intro i hi j hj hij
  exact wagner_attachment_adj h5 f hf hW X hX hdis hij
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- In a three-connected support, an actual copy of `V₈` has no outside vertices. -/
theorem spanning_wagner_of_noSmallSep {S : Finset V} (h5 : K5MinorFree G)
    (hsep : NoSmallSep G S) (f : Fin 8 → V) (hf : Function.Injective f)
    (hfS : ∀ a, f a ∈ S)
    (hW : ∀ a b, wagnerGraph.Adj a b → G.Adj (f a) (f b)) :
    ∀ v ∈ S, ∃ a, f a = v := by
  classical
  let F := Finset.univ.image f
  have hFS : F ⊆ S := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    exact hfS a
  intro v hvS
  by_contra hv
  have hvF : v ∉ F := by
    simpa [F, Finset.mem_image] using hv
  let X := reachIn G (S \ F) v
  have hvX : v ∈ X := mem_reachIn_self (Finset.mem_sdiff.mpr ⟨hvS, hvF⟩)
  have hXS : X ⊆ S := fun _ hx => (Finset.mem_sdiff.mp (reachIn_sub _ _ hx)).1
  have hXF : ∀ a, f a ∉ X := by
    intro a ha
    exact (Finset.mem_sdiff.mp (reachIn_sub _ _ ha)).2
      (Finset.mem_image_of_mem f (Finset.mem_univ a))
  let K := wagnerAttachments G f X
  let Z := K.image f
  have hK : K.card ≤ 2 := wagner_attachment_card_le_two h5 f hf hW X
    (reachIn_conn (Finset.mem_sdiff.mpr ⟨hvS, hvF⟩)) hXF
  have hZ : Z.card ≤ 2 := (Finset.card_image_le).trans hK
  have hZF : Z ⊆ F := Finset.image_mono f (Finset.filter_subset _ _)
  have hZS : Z ⊆ S := hZF.trans hFS
  have hZX : Disjoint Z X := by
    apply Finset.disjoint_left.mpr
    intro x hx hxX
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hXF a hxX
  let A := X ∪ Z
  let B := S \ X
  have hcover : A ∪ B = S := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((hx | hx) | ⟨hx, _⟩)
      · exact hXS hx
      · exact hZS hx
      · exact hx
    · intro hx
      by_cases hxX : x ∈ X
      · exact Or.inl (Or.inl hxX)
      · exact Or.inr ⟨hx, hxX⟩
  have hinter : A ∩ B ⊆ Z := by
    intro x hx
    obtain ⟨hxA, _, hxX⟩ := (Finset.mem_inter.mp hx).imp_right Finset.mem_sdiff.mp
    exact (Finset.mem_union.mp hxA).resolve_left hxX
  have hcross : ∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → ¬ G.Adj x y := by
    intro x hx hxB y hy hyA hxy
    have hyS := (Finset.mem_sdiff.mp hy).1
    have hyX := (Finset.mem_sdiff.mp hy).2
    have hyZ : y ∉ Z := fun hyZ => hyA (Finset.mem_union_right _ hyZ)
    rcases Finset.mem_union.mp hx with hxX | hxZ
    · by_cases hyF : y ∈ F
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hyF
        apply hyZ
        exact Finset.mem_image_of_mem f (Finset.mem_filter.mpr
          ⟨Finset.mem_univ a, x, hxX, hxy.symm⟩)
      · exact hyX (reachIn_closed hxX (Finset.mem_sdiff.mpr ⟨hyS, hyF⟩) hxy)
    · exact hxB (Finset.mem_sdiff.mpr ⟨hZS hxZ,
        fun hxX => Finset.disjoint_left.mp hZX hxZ hxX⟩)
  have hAB : ¬ A ⊆ B := by
    intro h
    exact (Finset.mem_sdiff.mp (h (Finset.mem_union_left _ hvX))).2 hvX
  have hBA : ¬ B ⊆ A := by
    intro h
    have hFA : F ⊆ A := by
      intro x hxF
      have hxX : x ∉ X := by
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxF
        exact hXF a
      exact h (Finset.mem_sdiff.mpr ⟨hFS hxF, hxX⟩)
    have hFZ : F ⊆ Z := by
      intro x hxF
      rcases Finset.mem_union.mp (hFA hxF) with hxX | hxZ
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxF
        exact (hXF a hxX).elim
      · exact hxZ
    have hFcard : F.card = 8 := by
      simp [F, Finset.card_image_of_injective _ hf]
    have := (Finset.card_le_card hFZ).trans hZ
    omega
  exact (hsep A B hcover ((Finset.card_le_card hinter).trans hZ) hcross).elim hAB hBA

/-- The actual-copy branch of Wagner rigidity, with no spanning assumption. -/
theorem isWagnerPiece_of_wagner_subgraph {S : Finset V} (h5 : K5MinorFree G)
    (hsep : NoSmallSep G S) (f : Fin 8 → V) (hf : Function.Injective f)
    (hfS : ∀ a, f a ∈ S)
    (hW : ∀ a b, wagnerGraph.Adj a b → G.Adj (f a) (f b)) :
    IsWagnerPiece G S :=
  isWagnerPiece_of_spanning_wagner h5 f hf hfS
    (spanning_wagner_of_noSmallSep h5 hsep f hf hfS hW) hW

end LeanPool.K5MinorFreeChoosability
