/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerAttachmentAttack

/-!
# Non-cut vertices and three-armed stars

Two generic facts about finite connected vertex sets, stated with the existing `ConnSet`,
`RIn`, `reachIn` and `Touch` API (no second reachability representation is introduced).

* `exists_noncut_ne`: a connected set with at least two vertices has, for every vertex `a`,
  a vertex `u ≠ a` whose removal leaves the set connected.
* `exists_isStar3`: a set `B` that is a *minimal* connected set touching three target sets
  `T 0, T 1, T 2` is a star: it has a centre `z` and three disjoint arms `R k` covering
  `B \ {z}`, each nonempty arm being connected and touching both the centre and its target
  `T k`, and the centre touching `T k` whenever the arm `R k` is empty.

The star lemma is the branch-set form of the fact that a minor of a graph of maximum degree
three is a topological minor: it is applied to minimal models of the cubic graphs `V₈` and
`K_{3,3}`.
-/

@[expose] public section

set_option autoImplicit false

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-! ### Small connectivity lemmas -/

/-- The union of two connected sets sharing a vertex is connected. -/
theorem connSet_union_of_mem {X Y : Finset V} (hX : ConnSet G ↑X) (hY : ConnSet G ↑Y)
    {c : V} (hcX : c ∈ X) (hcY : c ∈ Y) : ConnSet G ↑(X ∪ Y) := by
  classical
  have hXs : (↑X : Set V) ⊆ ↑(X ∪ Y) := Finset.coe_subset.2 Finset.subset_union_left
  have hYs : (↑Y : Set V) ⊆ ↑(X ∪ Y) := Finset.coe_subset.2 Finset.subset_union_right
  have key : ∀ x ∈ (↑(X ∪ Y) : Set V), RIn G ↑(X ∪ Y) x c := by
    intro x hx
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
    · exact (hX.2 x hx c hcX).mono_set hXs
    · exact (hY.2 x hx c hcY).mono_set hYs
  exact ⟨⟨c, hXs hcX⟩, fun a ha b hb => (key a ha).trans (key b hb).symm⟩

/-- In a connected set, every vertex has a neighbour among the other vertices (if any). -/
theorem exists_adj_erase_of_connSet {B : Finset V} (hB : ConnSet G ↑B) {u w : V}
    (hu : u ∈ B) (hw : w ∈ B) (hwu : w ≠ u) : ∃ x ∈ B.erase u, G.Adj u x := by
  obtain ⟨p, q, -, -, hp, hq, hqP, hpq⟩ :=
    (hB.2 u hu w hw).exit (P := ({u} : Set V)) rfl (by simpa using hwu)
  rw [Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨q, Finset.mem_erase.2 ⟨by simpa using hqP, hq⟩, hpq⟩

/-- A component of `B \ {b}` touches `b`, when `B` is connected. -/
theorem exists_adj_of_reachIn_erase {B : Finset V} (hB : ConnSet G ↑B) {b x : V}
    (hb : b ∈ B) (hx : x ∈ B.erase b) : ∃ y ∈ reachIn G (B.erase b) x, G.Adj y b := by
  have hxK : x ∈ reachIn G (B.erase b) x := mem_reachIn_self hx
  have hbK : b ∉ reachIn G (B.erase b) x := fun h => by
    simpa using reachIn_sub _ _ h
  obtain ⟨p, q, -, -, hp, hq, hqP, hpq⟩ :=
    (hB.2 x (Finset.mem_of_mem_erase hx) b hb).exit
      (P := (↑(reachIn G (B.erase b) x) : Set V)) hxK hbK
  by_cases hqb : q = b
  · subst hqb; exact ⟨p, hp, hpq⟩
  · exact absurd (reachIn_closed hp (Finset.mem_erase.2 ⟨hqb, hq⟩) hpq) hqP

/-! ### Non-cut vertices -/

theorem exists_noncut_ne_aux (n : ℕ) : ∀ B : Finset V, B.card = n → ConnSet G ↑B →
    ∀ a ∈ B, 2 ≤ B.card → ∃ u ∈ B, u ≠ a ∧ ConnSet G ↑(B.erase u) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hn hB a ha h2
  obtain ⟨b, hbB, hba⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) a
  by_cases hcon : ConnSet G ↑(B.erase b)
  · exact ⟨b, hbB, hba, hcon⟩
  have haE : a ∈ B.erase b := Finset.mem_erase.2 ⟨hba.symm, ha⟩
  -- a vertex of `B \ {b}` not reachable from `a`
  have hw : ∃ w ∈ B.erase b, ¬ RIn G ↑(B.erase b) a w := by
    by_contra hall
    push Not at hall
    exact hcon ⟨⟨a, by exact_mod_cast haE⟩, fun x hx y hy =>
      (hall x (by exact_mod_cast hx)).symm.trans (hall y (by exact_mod_cast hy))⟩
  obtain ⟨w, hwE, haw⟩ := hw
  set D := reachIn G (B.erase b) w with hD
  have hDE : D ⊆ B.erase b := reachIn_sub _ _
  have haD : a ∉ D := fun h => haw (mem_reachIn.1 h).2.symm
  have hbD : b ∉ D := fun h => by simpa using hDE h
  have hwD : w ∈ D := mem_reachIn_self hwE
  have hDB : D ⊆ B := hDE.trans (Finset.erase_subset _ _)
  obtain ⟨y, hyD, hyb⟩ := exists_adj_of_reachIn_erase hB hbB hwE
  have hD'conn : ConnSet G ↑(insert b D) := by
    have := (reachIn_conn (G := G) hwE).insert_adj (a := b) (by exact_mod_cast hyD) hyb.symm
    simpa using this
  have hD'card : (insert b D).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    refine ⟨Finset.insert_subset hbB hDB, fun h => ?_⟩
    have := h ha
    rcases Finset.mem_insert.1 this with h1 | h1
    · exact hba h1.symm
    · exact haD h1
  have hD'2 : 2 ≤ (insert b D).card := by
    rw [Finset.card_insert_of_notMem hbD]
    have : 0 < D.card := Finset.card_pos.2 ⟨w, hwD⟩
    omega
  obtain ⟨u, huD', hub, hu⟩ := ih _ hD'card (insert b D) rfl hD'conn b
    (Finset.mem_insert_self b D) hD'2
  have huD : u ∈ D := (Finset.mem_insert.1 huD').resolve_left hub
  -- the rest `B \ D` is connected through `b`
  have hrest : ConnSet G ↑(B \ D) := by
    have hbR : b ∈ B \ D := Finset.mem_sdiff.2 ⟨hbB, hbD⟩
    have key : ∀ x ∈ B \ D, RIn G ↑(B \ D) x b := by
      intro x hx
      obtain ⟨hxB, hxD⟩ := Finset.mem_sdiff.1 hx
      by_cases hxb : x = b
      · subst hxb; exact RIn.refl _
      have hxE : x ∈ B.erase b := Finset.mem_erase.2 ⟨hxb, hxB⟩
      set K := reachIn G (B.erase b) x with hK
      have hKD : ∀ z ∈ K, z ∉ D := by
        intro z hzK hzD
        apply hxD
        exact mem_reachIn.2 ⟨hxE, (mem_reachIn.1 hzD).2.trans (mem_reachIn.1 hzK).2.symm⟩
      have hKR : K ⊆ B \ D := fun z hz =>
        Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase (reachIn_sub _ _ hz), hKD z hz⟩
      obtain ⟨z, hzK, hzb⟩ := exists_adj_of_reachIn_erase hB hbB hxE
      have h1 : RIn G ↑(B \ D) x z :=
        ((reachIn_conn (G := G) hxE).2 x (by exact_mod_cast mem_reachIn_self hxE) z
          (by exact_mod_cast hzK)).mono_set (by exact_mod_cast hKR)
      exact h1.tail hzb (by exact_mod_cast hKR hzK) (by exact_mod_cast hbR)
    exact ⟨⟨b, by exact_mod_cast hbR⟩, fun x hx y hy =>
      (key x (by exact_mod_cast hx)).trans (key y (by exact_mod_cast hy)).symm⟩
  have hU := connSet_union_of_mem hu hrest (c := b)
    (Finset.mem_erase.2 ⟨fun h => hub h.symm, Finset.mem_insert_self b D⟩)
    (Finset.mem_sdiff.2 ⟨hbB, hbD⟩)
  have heq : (insert b D).erase u ∪ (B \ D) = B.erase u := by
    ext x
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_sdiff]
    constructor
    · rintro (⟨hxu, rfl | hxD⟩ | ⟨hxB, hxD⟩)
      · exact ⟨hxu, hbB⟩
      · exact ⟨hxu, hDB hxD⟩
      · exact ⟨fun h => hxD (h ▸ huD), hxB⟩
    · rintro ⟨hxu, hxB⟩
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxu, Or.inr hxD⟩
      · exact Or.inr ⟨hxB, hxD⟩
  rw [heq] at hU
  exact ⟨u, hDB huD, fun h => haD (h ▸ huD), hU⟩

/-- **Non-cut vertices.** A finite connected set with at least two vertices has, besides any
prescribed vertex `a`, a vertex whose removal leaves it connected. -/
theorem exists_noncut_ne {B : Finset V} (hB : ConnSet G ↑B) {a : V} (ha : a ∈ B)
    (h2 : 2 ≤ B.card) : ∃ u ∈ B, u ≠ a ∧ ConnSet G ↑(B.erase u) :=
  exists_noncut_ne_aux _ B rfl hB a ha h2

/-! ### Three-armed stars -/

/-- `B` is a minimal connected set touching the three targets `T k`. -/
def IsMinTouch3 (G : SimpleGraph V) (T : Fin 3 → Finset V) (B : Finset V) : Prop :=
  ConnSet G ↑B ∧ (∀ k, Touch G B (T k)) ∧
    ∀ B' : Finset V, B' ⊆ B → B' ≠ B → ConnSet G ↑B' → ¬ ∀ k, Touch G B' (T k)

/-- A star decomposition of `B` with centre `z` and arms `R k` aimed at the targets `T k`. -/
structure IsStar3 (G : SimpleGraph V) (T : Fin 3 → Finset V) (B : Finset V) (z : V)
    (R : Fin 3 → Finset V) : Prop where
  z_mem : z ∈ B
  R_sub : ∀ k, R k ⊆ B.erase z
  R_disj : ∀ k l, k ≠ l → Disjoint (R k) (R l)
  cover : ∀ x ∈ B, x ≠ z → ∃ k, x ∈ R k
  conn : ∀ k, (R k).Nonempty → ConnSet G ↑(R k)
  touch_z : ∀ k, (R k).Nonempty → Touch G (R k) {z}
  touch_T : ∀ k, (R k).Nonempty → Touch G (R k) (T k)
  empty_T : ∀ k, R k = ∅ → Touch G {z} (T k)

theorem touch_singleton_of_private {B T : Finset V} {u : V} (hT : Touch G B T)
    (hn : ¬ Touch G (B.erase u) T) : Touch G {u} T := by
  obtain ⟨a, ha, b, hb, hab⟩ := hT
  by_cases hau : a = u
  · subst hau; exact ⟨a, Finset.mem_singleton_self a, b, hb, hab⟩
  · exact absurd ⟨a, Finset.mem_erase.2 ⟨hau, ha⟩, b, hb, hab⟩ hn

theorem fin3_pigeon (k l j j' : Fin 3) (hkl : k ≠ l) (hjj : j ≠ j') :
    j = k ∨ j = l ∨ j' = k ∨ j' = l := by
  revert k l j j'; decide

theorem exists_isStar3_aux (n : ℕ) : ∀ (T : Fin 3 → Finset V) (B : Finset V), B.card = n →
    IsMinTouch3 G T B → ∃ z R, IsStar3 G T B z R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T B hn hB
  obtain ⟨hBc, hBt, hBmin⟩ := hB
  obtain ⟨a, ha⟩ := hBc.1
  have ha' : a ∈ B := by exact_mod_cast ha
  by_cases h1 : B.card ≤ 1
  · -- a single vertex is a star with empty arms
    have hBa : B = {a} := Finset.eq_singleton_iff_unique_mem.2
      ⟨ha', fun x hx => Finset.card_le_one.1 h1 x hx a ha'⟩
    refine ⟨a, fun _ => ∅, ⟨ha', fun _ => Finset.empty_subset _, fun _ _ _ => by simp,
      fun x hx hxa => absurd (by simpa [hBa] using hx) hxa, fun _ h => absurd h (by simp),
      fun _ h => absurd h (by simp), fun _ h => absurd h (by simp), fun k _ => ?_⟩⟩
    rw [← hBa]; exact hBt k
  push Not at h1
  obtain ⟨u, huB, -, hucon⟩ := exists_noncut_ne hBc ha' (by omega)
  -- `u` is adjacent to the rest of `B`
  obtain ⟨w, hwB, hwu⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) u
  obtain ⟨x0, hx0, hux0⟩ := exists_adj_erase_of_connSet hBc huB hwB hwu
  have hne : B.erase u ≠ B := fun h => by
    have : u ∈ B.erase u := h.symm ▸ huB
    simp at this
  -- private targets of `u`
  set P : Fin 3 → Prop := fun k => ¬ Touch G (B.erase u) (T k) with hP
  have hPu : ∀ k, P k → Touch G {u} (T k) := fun k hk => touch_singleton_of_private (hBt k) hk
  have hsomeP : ∃ k, P k := by
    by_contra hno
    push Not at hno
    exact hBmin _ (Finset.erase_subset _ _) hne hucon (fun k => not_not.1 (hno k))
  by_cases htwo : ∃ k l, k ≠ l ∧ P k ∧ P l
  · obtain ⟨k, l, hkl, hk, hl⟩ := htwo
    -- at most one non-private target
    have hat : ∀ j j', j ≠ j' → P j ∨ P j' := by
      intro j j' hjj
      rcases fin3_pigeon k l j j' hkl hjj with rfl | rfl | rfl | rfl
      · exact Or.inl hk
      · exact Or.inl hl
      · exact Or.inr hk
      · exact Or.inr hl
    -- not all three are private
    have hnotall : ¬ ∀ j, P j := by
      intro hall
      have hsub : ({u} : Finset V) ⊆ B := Finset.singleton_subset_iff.2 huB
      have hne' : ({u} : Finset V) ≠ B := by
        intro h
        rw [← h, Finset.card_singleton] at h1
        omega
      exact hBmin _ hsub hne' (by simpa using connSet_singleton G u) (fun j => hPu j (hall j))
    classical
    refine ⟨u, fun j => if P j then ∅ else B.erase u, ⟨huB, fun j => ?_, fun j j' hjj => ?_,
      fun x hx hxu => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩⟩
    · split_ifs <;> simp
    · rcases hat j j' hjj with h | h <;> simp [h]
    · obtain ⟨j, hj⟩ := not_forall.1 hnotall
      exact ⟨j, by simp [hj, hx, hxu]⟩
    · have hPj : ¬ P j := fun h => by simp [h] at hj
      simpa [hPj] using hucon
    · have hPj : ¬ P j := fun h => by simp [h] at hj
      simp only [hPj, ite_false]
      exact ⟨x0, hx0, u, Finset.mem_singleton_self u, hux0.symm⟩
    · have hPj : ¬ P j := fun h => by simp [h] at hj
      simp only [hPj, ite_false]
      exact not_not.1 hPj
    · by_cases hPj : P j
      · exact hPu j hPj
      · simp only [hPj, ite_false] at hj
        exact absurd hj (Finset.nonempty_iff_ne_empty.1 ⟨x0, hx0⟩)
  · -- exactly one private target `k0`: recurse on `B \ {u}`
    push Not at htwo
    obtain ⟨k0, hk0⟩ := hsomeP
    have honly : ∀ j, j ≠ k0 → Touch G (B.erase u) (T j) := by
      intro j hj
      by_contra h
      exact htwo j k0 hj h hk0
    set T' := Function.update T k0 {u} with hT'
    have hmin' : IsMinTouch3 G T' (B.erase u) := by
      refine ⟨hucon, fun j => ?_, fun B' hB'sub hB'ne hB'c hB't => ?_⟩
      · by_cases hj : j = k0
        · subst hj
          simp only [hT', Function.update_self]
          exact ⟨x0, hx0, u, Finset.mem_singleton_self u, hux0.symm⟩
        · simp only [hT', Function.update_of_ne hj]
          exact honly j hj
      · -- `B' ∪ {u}` would be a smaller good set
        have hu' : Touch G B' {u} := by
          have := hB't k0
          simpa [hT'] using this
        obtain ⟨p, hp, q, hq, hpq⟩ := hu'
        rw [Finset.mem_singleton] at hq
        subst hq
        have huB' : q ∉ B' := fun h => by simpa using hB'sub h
        refine hBmin (insert q B') (Finset.insert_subset huB (hB'sub.trans
          (Finset.erase_subset _ _))) ?_ ?_ (fun j => ?_)
        · intro h
          apply hB'ne
          ext x
          constructor
          · exact fun hx => hB'sub hx
          · intro hx
            have hxB : x ∈ insert q B' := h ▸ Finset.mem_of_mem_erase hx
            rcases Finset.mem_insert.1 hxB with rfl | hx'
            · simp at hx
            · exact hx'
        · simpa using hB'c.insert_adj (by exact_mod_cast hp) hpq.symm
        · by_cases hj : j = k0
          · subst hj
            exact (hPu j hk0).mono (by simp) subset_rfl
          · have := hB't j
            simp only [hT', Function.update_of_ne hj] at this
            exact this.mono (Finset.subset_insert _ _) subset_rfl
    have hcard : (B.erase u).card < n := by
      rw [← hn]; exact Finset.card_erase_lt_of_mem huB
    obtain ⟨z, R', hst⟩ := ih _ hcard T' (B.erase u) rfl hmin'
    have hzB : z ∈ B.erase u := hst.z_mem
    have hzu : z ≠ u := (Finset.mem_erase.1 hzB).1
    have hR'B : ∀ j, R' j ⊆ B.erase u := fun j =>
      (hst.R_sub j).trans (Finset.erase_subset _ _)
    have huR' : ∀ j, u ∉ R' j := fun j h => by simpa using hR'B j h
    refine ⟨z, Function.update R' k0 (insert u (R' k0)), ⟨Finset.mem_of_mem_erase hzB,
      fun j => ?_, fun j l hjl => ?_, fun x hx hxz => ?_, fun j hj => ?_, fun j hj => ?_,
      fun j hj => ?_, fun j hj => ?_⟩⟩
    · by_cases hj : j = k0
      · subst hj
        simp only [Function.update_self]
        refine Finset.insert_subset (Finset.mem_erase.2 ⟨hzu.symm, huB⟩) ?_
        exact (hst.R_sub j).trans (Finset.erase_subset_erase _ (Finset.erase_subset _ _))
      · simp only [Function.update_of_ne hj]
        exact (hst.R_sub j).trans (Finset.erase_subset_erase _ (Finset.erase_subset _ _))
    · by_cases hj : j = k0
      · subst hj
        simp only [Function.update_self, Function.update_of_ne hjl.symm]
        exact Finset.disjoint_insert_left.2 ⟨huR' l, hst.R_disj j l hjl⟩
      · by_cases hl : l = k0
        · subst hl
          simp only [Function.update_self, Function.update_of_ne hj]
          exact Finset.disjoint_insert_right.2 ⟨huR' j, hst.R_disj j l hjl⟩
        · simp only [Function.update_of_ne hj, Function.update_of_ne hl]
          exact hst.R_disj j l hjl
    · by_cases hxu : x = u
      · subst hxu; exact ⟨k0, by simp⟩
      · obtain ⟨j, hj⟩ := hst.cover x (Finset.mem_erase.2 ⟨hxu, hx⟩) hxz
        by_cases hjk : j = k0
        · subst hjk; exact ⟨j, by simp [hj]⟩
        · exact ⟨j, by simpa [Function.update_of_ne hjk] using hj⟩
    · by_cases hjk : j = k0
      · subst hjk
        simp only [Function.update_self]
        by_cases hR : (R' j).Nonempty
        · have ht := hst.touch_T j hR
          simp only [hT', Function.update_self] at ht
          obtain ⟨p, hp, q, hq, hpq⟩ := ht
          rw [Finset.mem_singleton] at hq
          subst hq
          simpa using (hst.conn j hR).insert_adj (by exact_mod_cast hp) hpq.symm
        · rw [Finset.not_nonempty_iff_eq_empty.1 hR]
          simpa using connSet_singleton G u
      · simp only [Function.update_of_ne hjk] at hj ⊢
        exact hst.conn j hj
    · by_cases hjk : j = k0
      · subst hjk
        simp only [Function.update_self]
        by_cases hR : (R' j).Nonempty
        · exact (hst.touch_z j hR).mono (Finset.subset_insert _ _) subset_rfl
        · have ht := hst.empty_T j (Finset.not_nonempty_iff_eq_empty.1 hR)
          simp only [hT', Function.update_self] at ht
          obtain ⟨p, hp, q, hq, hpq⟩ := ht
          rw [Finset.mem_singleton] at hp hq
          subst hp; subst hq
          exact ⟨q, Finset.mem_insert_self _ _, p, Finset.mem_singleton_self _, hpq.symm⟩
      · simp only [Function.update_of_ne hjk] at hj ⊢
        exact hst.touch_z j hj
    · by_cases hjk : j = k0
      · subst hjk
        simp only [Function.update_self]
        exact (hPu j hk0).mono (by simp) subset_rfl
      · simp only [Function.update_of_ne hjk] at hj ⊢
        have := hst.touch_T j hj
        simpa [hT', Function.update_of_ne hjk] using this
    · by_cases hjk : j = k0
      · subst hjk
        simp at hj
      · simp only [Function.update_of_ne hjk] at hj ⊢
        have := hst.empty_T j hj
        simpa [hT', Function.update_of_ne hjk] using this

/-- **Three-armed stars.** A minimal connected set touching three targets is a star. -/
theorem exists_isStar3 {T : Fin 3 → Finset V} {B : Finset V} (h : IsMinTouch3 G T B) :
    ∃ z R, IsStar3 G T B z R :=
  exists_isStar3_aux _ T B rfl h

end LeanPool.K5MinorFreeChoosability
