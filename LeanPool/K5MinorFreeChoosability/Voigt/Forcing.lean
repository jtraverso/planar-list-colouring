/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Voigt.Graph
public import LeanPool.K5MinorFreeChoosability.Voigt.Hexagon
public import Mathlib.Tactic.Linarith

/-!
# Voigt's forcing argument: no colouring from the lists

This file proves `voigt_not_listColourable`: no proper colouring of `voigtGraph` takes every
vertex `v` to a colour of `voigtList v`.  The proof follows Voigt's Section 3.

1. **Gadget step** (`gadget_forcing`, Voigt's *Observation*).  If the corners `X Y Z` of a
   gadget receive its designated colours `x y z`, the six vertices `R₁ … S₃` must use colours
   from `{3, 5, 6}` and the `T`'s from `{3, 5}`.  By `voigt_hexagon_forcing` (applied to the
   inner triangle `R₁ R₂ R₃` and the hexagon), one of the pairs `S₁ R₂`, `S₂ R₃`, `S₃ R₁` uses
   both `3` and `5`, so the `T` adjacent to that pair has no colour left.
2. **Unit step** (`unit_blocks`).  In the `k`-th marked triangle `U W V`, if the hub `W` has
   colour `1` and `{U, V}` has colours `{2, 3}`, then `P` is forced to `4`, and one of the two
   gadgets (Fig. 3 if `U = 2`, Fig. 4 if `V = 2`) is blocked.
3. **Hub step** (`hub_lemma`).  Each hub `F L M N` is adjacent to a triangle of `G₁`; if it had
   colour `1`, two of the three triangle colours would be `2` and `3`.  So the hub avoids `1`,
   and colour `1` appears on its triangle.
4. **Core step** (`core_contradiction`, Voigt's *Lemma*).  On the `K₄` `A B C D`, `E` repeats
   the colour of `C` and `O` the colour of `A`; the four triangles `ABE`, `BDE`, `ADE`, `BDO`
   then cover the four triples of `{A, B, C, D}`, and colour `1` cannot lie in all of them.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability.Voigt

/-! ### The gadget step -/

/-- The encoding `3 ↦ 0`, `5 ↦ 1`, `6 ↦ 2` of the three free gadget colours. -/
def enc3 (n : ℕ) : Fin 3 := if n = 3 then 0 else if n = 5 then 1 else 2

private theorem enc3_ne {a b : ℕ} (ha : a = 3 ∨ a = 5 ∨ a = 6) (hb : b = 3 ∨ b = 5 ∨ b = 6)
    (h : a ≠ b) : enc3 a ≠ enc3 b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl h | decide

private theorem enc3_zero {a : ℕ} (ha : a = 3 ∨ a = 5 ∨ a = 6) (h : enc3 a = 0) : a = 3 := by
  rcases ha with rfl | rfl | rfl <;> first | rfl | exact absurd h (by decide)

private theorem enc3_one {a : ℕ} (ha : a = 3 ∨ a = 5 ∨ a = 6) (h : enc3 a = 1) : a = 5 := by
  rcases ha with rfl | rfl | rfl <;> first | rfl | exact absurd h (by decide)

private theorem free_of_mem {a x : ℕ} (h : a ∈ ({x, 3, 5, 6} : Finset ℕ)) (hx : a ≠ x) :
    a = 3 ∨ a = 5 ∨ a = 6 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  tauto

private theorem t_of_mem {a x y : ℕ} (h : a ∈ ({x, y, 3, 5} : Finset ℕ)) (hx : a ≠ x)
    (hy : a ≠ y) : a = 3 ∨ a = 5 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  tauto

/-- **Voigt's Observation, gadget form.**  A gadget (Fig. 3/4) whose corners carry its
designated colours `x y z` has no colouring from its lists.  Only the list memberships and the
inequalities along the 15 inner and 12 corner edges of the gadget are used. -/
theorem gadget_forcing (x y z r₁ r₂ r₃ s₁ s₂ s₃ t₀ t₁ t₂ : ℕ)
    (hr₁ : r₁ ∈ ({x, 3, 5, 6} : Finset ℕ)) (hs₁ : s₁ ∈ ({x, 3, 5, 6} : Finset ℕ))
    (hr₂ : r₂ ∈ ({y, 3, 5, 6} : Finset ℕ)) (hs₂ : s₂ ∈ ({y, 3, 5, 6} : Finset ℕ))
    (hr₃ : r₃ ∈ ({z, 3, 5, 6} : Finset ℕ)) (hs₃ : s₃ ∈ ({z, 3, 5, 6} : Finset ℕ))
    (ht₀ : t₀ ∈ ({x, y, 3, 5} : Finset ℕ)) (ht₁ : t₁ ∈ ({y, z, 3, 5} : Finset ℕ))
    (ht₂ : t₂ ∈ ({z, x, 3, 5} : Finset ℕ))
    (xr₁ : r₁ ≠ x) (xs₁ : s₁ ≠ x) (yr₂ : r₂ ≠ y) (ys₂ : s₂ ≠ y) (zr₃ : r₃ ≠ z) (zs₃ : s₃ ≠ z)
    (xt₀ : t₀ ≠ x) (yt₀ : t₀ ≠ y) (yt₁ : t₁ ≠ y) (zt₁ : t₁ ≠ z) (zt₂ : t₂ ≠ z) (xt₂ : t₂ ≠ x)
    (r₁₂ : r₁ ≠ r₂) (r₂₃ : r₂ ≠ r₃) (r₃₁ : r₃ ≠ r₁)
    (s₁r₁ : s₁ ≠ r₁) (s₁r₂ : s₁ ≠ r₂) (s₂r₂ : s₂ ≠ r₂) (s₂r₃ : s₂ ≠ r₃)
    (s₃r₃ : s₃ ≠ r₃) (s₃r₁ : s₃ ≠ r₁)
    (t₀r₂ : t₀ ≠ r₂) (t₀s₁ : t₀ ≠ s₁) (t₁r₃ : t₁ ≠ r₃) (t₁s₂ : t₁ ≠ s₂)
    (t₂r₁ : t₂ ≠ r₁) (t₂s₃ : t₂ ≠ s₃) : False := by
  have fr₁ := free_of_mem hr₁ xr₁
  have fs₁ := free_of_mem hs₁ xs₁
  have fr₂ := free_of_mem hr₂ yr₂
  have fs₂ := free_of_mem hs₂ ys₂
  have fr₃ := free_of_mem hr₃ zr₃
  have fs₃ := free_of_mem hs₃ zs₃
  have ft₀ := t_of_mem ht₀ xt₀ yt₀
  have ft₁ := t_of_mem ht₁ yt₁ zt₁
  have ft₂ := t_of_mem ht₂ zt₂ xt₂
  rcases voigt_hexagon_forcing (enc3 r₁) (enc3 r₂) (enc3 r₃) (enc3 s₁) (enc3 s₂) (enc3 s₃)
      (enc3_ne fr₁ fr₂ r₁₂) (enc3_ne fr₂ fr₃ r₂₃) (enc3_ne fr₃ fr₁ r₃₁)
      (enc3_ne fs₁ fr₁ s₁r₁) (enc3_ne fs₁ fr₂ s₁r₂) (enc3_ne fs₂ fr₂ s₂r₂)
      (enc3_ne fs₂ fr₃ s₂r₃) (enc3_ne fs₃ fr₃ s₃r₃) (enc3_ne fs₃ fr₁ s₃r₁) with
    (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have := enc3_zero fs₁ h1; have := enc3_one fr₂ h2; omega
  · have := enc3_one fs₁ h1; have := enc3_zero fr₂ h2; omega
  · have := enc3_zero fs₂ h1; have := enc3_one fr₃ h2; omega
  · have := enc3_one fs₂ h1; have := enc3_zero fr₃ h2; omega
  · have := enc3_zero fs₃ h1; have := enc3_one fr₁ h2; omega
  · have := enc3_one fs₃ h1; have := enc3_zero fr₁ h2; omega

/-! ### Concrete facts about the graph, checked by the kernel -/

/-- The vertex with number `n` (taken modulo `238`). -/
def vtx (n : ℕ) : Fin 238 := Fin.ofNat 238 n

/-- The gadget `g` has its 15 inner edges and 12 corner edges. -/
theorem gadget_adj : ∀ g < 24,
    let v := fun i => vtx (22 + 9 * g + i)
    (voigtGraph.Adj (v 0) (v 1) ∧ voigtGraph.Adj (v 1) (v 2) ∧ voigtGraph.Adj (v 2) (v 0) ∧
      voigtGraph.Adj (v 3) (v 0) ∧ voigtGraph.Adj (v 3) (v 1) ∧ voigtGraph.Adj (v 4) (v 1) ∧
      voigtGraph.Adj (v 4) (v 2) ∧ voigtGraph.Adj (v 5) (v 2) ∧ voigtGraph.Adj (v 5) (v 0) ∧
      voigtGraph.Adj (v 6) (v 1) ∧ voigtGraph.Adj (v 6) (v 3) ∧ voigtGraph.Adj (v 7) (v 2) ∧
      voigtGraph.Adj (v 7) (v 4) ∧ voigtGraph.Adj (v 8) (v 0) ∧ voigtGraph.Adj (v 8) (v 5)) ∧
    (voigtGraph.Adj (v 0) (vtx (gadX g)) ∧ voigtGraph.Adj (v 3) (vtx (gadX g)) ∧
      voigtGraph.Adj (v 1) (vtx (gadY g)) ∧ voigtGraph.Adj (v 4) (vtx (gadY g)) ∧
      voigtGraph.Adj (v 2) (vtx (gadZ g)) ∧ voigtGraph.Adj (v 5) (vtx (gadZ g)) ∧
      voigtGraph.Adj (v 6) (vtx (gadX g)) ∧ voigtGraph.Adj (v 6) (vtx (gadY g)) ∧
      voigtGraph.Adj (v 7) (vtx (gadY g)) ∧ voigtGraph.Adj (v 7) (vtx (gadZ g)) ∧
      voigtGraph.Adj (v 8) (vtx (gadZ g)) ∧ voigtGraph.Adj (v 8) (vtx (gadX g))) := by
  decide +kernel

/-- The lists of gadget `g`. -/
theorem gadget_lists : ∀ g < 24,
    let v := fun i => vtx (22 + 9 * g + i)
    voigtList (v 0) = {colX g, 3, 5, 6} ∧ voigtList (v 3) = {colX g, 3, 5, 6} ∧
    voigtList (v 1) = {colY g, 3, 5, 6} ∧ voigtList (v 4) = {colY g, 3, 5, 6} ∧
    voigtList (v 2) = {colZ g, 3, 5, 6} ∧ voigtList (v 5) = {colZ g, 3, 5, 6} ∧
    voigtList (v 6) = {colX g, colY g, 3, 5} ∧ voigtList (v 7) = {colY g, colZ g, 3, 5} ∧
    voigtList (v 8) = {colZ g, colX g, 3, 5} := by
  decide +kernel

/-- The base vertices carry the list `{1, 2, 3, 4}`. -/
theorem base_lists : ∀ n < 22, voigtList (vtx n) = {1, 2, 3, 4} := by
  decide +kernel

/-- The two gadgets of the `k`-th marked triangle `U W V` with inner vertex `P = 10 + k`. -/
theorem unit_gadgets : ∀ k < 12,
    gadX (2 * k) = unitU k ∧ gadY (2 * k) = unitW k ∧ gadZ (2 * k) = 10 + k ∧
    colX (2 * k) = 2 ∧ colY (2 * k) = 1 ∧ colZ (2 * k) = 4 ∧
    gadX (2 * k + 1) = 10 + k ∧ gadY (2 * k + 1) = unitW k ∧ gadZ (2 * k + 1) = unitV k ∧
    colX (2 * k + 1) = 4 ∧ colY (2 * k + 1) = 1 ∧ colZ (2 * k + 1) = 2 := by
  decide

/-- `P_k` is adjacent to the three corners of the `k`-th marked triangle. -/
theorem unit_adj : ∀ k < 12,
    voigtGraph.Adj (vtx (10 + k)) (vtx (unitU k)) ∧
    voigtGraph.Adj (vtx (10 + k)) (vtx (unitW k)) ∧
    voigtGraph.Adj (vtx (10 + k)) (vtx (unitV k)) := by
  decide +kernel

/-- The base vertices used by the core argument. -/
theorem unit_base : ∀ k < 12, unitU k < 22 ∧ unitW k < 22 ∧ unitV k < 22 := by
  decide

/-! ### The forcing argument -/

section Colouring

variable (c : voigtGraph.Coloring ℕ) (hc : ∀ v, c v ∈ voigtList v)
include hc

/-- **Gadget step**: the corners of a gadget never carry its designated colours. -/
theorem gadget_blocks {g : ℕ} (hg : g < 24) :
    ¬ (c (vtx (gadX g)) = colX g ∧ c (vtx (gadY g)) = colY g ∧
      c (vtx (gadZ g)) = colZ g) := by
  rintro ⟨hx, hy, hz⟩
  obtain ⟨⟨a01, a12, a20, a30, a31, a41, a42, a52, a50, a61, a63, a72, a74, a80, a85⟩,
    ⟨x0, x3, y1, y4, z2, z5, x6, y6, y7, z7, z8, x8⟩⟩ := gadget_adj g hg
  obtain ⟨l0, l3, l1, l4, l2, l5, l6, l7, l8⟩ := gadget_lists g hg
  have v := fun i => hc (vtx (22 + 9 * g + i))
  have ne : ∀ {u w}, voigtGraph.Adj u w → c u ≠ c w := fun h => c.valid h
  refine gadget_forcing (colX g) (colY g) (colZ g) _ _ _ _ _ _ _ _ _
    (l0 ▸ v 0) (l3 ▸ v 3) (l1 ▸ v 1) (l4 ▸ v 4) (l2 ▸ v 2) (l5 ▸ v 5)
    (l6 ▸ v 6) (l7 ▸ v 7) (l8 ▸ v 8)
    (hx ▸ ne x0) (hx ▸ ne x3) (hy ▸ ne y1) (hy ▸ ne y4) (hz ▸ ne z2) (hz ▸ ne z5)
    (hx ▸ ne x6) (hy ▸ ne y6) (hy ▸ ne y7) (hz ▸ ne z7) (hz ▸ ne z8) (hx ▸ ne x8)
    (ne a01) (ne a12) (ne a20) (ne a30) (ne a31) (ne a41) (ne a42) (ne a52) (ne a50)
    (ne a61) (ne a63) (ne a72) (ne a74) (ne a80) (ne a85)

/-- Base vertices are coloured from `{1, 2, 3, 4}`. -/
theorem base_colour {n : ℕ} (hn : n < 22) :
    c (vtx n) = 1 ∨ c (vtx n) = 2 ∨ c (vtx n) = 3 ∨ c (vtx n) = 4 := by
  have := hc (vtx n)
  rw [base_lists n hn] at this
  simpa using this

/-- **Unit step**: if the hub of the `k`-th marked triangle `U W V` has colour `1`, then
`U` and `V` are not coloured `2, 3` in either order. -/
theorem unit_blocks {k : ℕ} (hk : k < 12) (hW : c (vtx (unitW k)) = 1) :
    ¬ ((c (vtx (unitU k)) = 2 ∧ c (vtx (unitV k)) = 3) ∨
      (c (vtx (unitU k)) = 3 ∧ c (vtx (unitV k)) = 2)) := by
  obtain ⟨gx, gy, gz, cx, cy, cz, gx', gy', gz', cx', cy', cz'⟩ := unit_gadgets k hk
  obtain ⟨pU, pW, pV⟩ := unit_adj k hk
  have hP := base_colour c hc (n := 10 + k) (by omega)
  have nU := c.valid pU
  have nW := c.valid pW
  have nV := c.valid pV
  rintro (⟨hU, hV⟩ | ⟨hU, hV⟩)
  · have hP4 : c (vtx (10 + k)) = 4 := by omega
    exact gadget_blocks c hc (g := 2 * k) (by omega)
      ⟨by rw [gx, cx, hU], by rw [gy, cy, hW], by rw [gz, cz, hP4]⟩
  · have hP4 : c (vtx (10 + k)) = 4 := by omega
    exact gadget_blocks c hc (g := 2 * k + 1) (by omega)
      ⟨by rw [gx', cx', hP4], by rw [gy', cy', hW], by rw [gz', cz', hV]⟩

end Colouring

/-- **Hub step** (pure arithmetic): a vertex `w` adjacent to a triangle `x y z`, all coloured
from `{1, 2, 3, 4}`, such that `w = 1` forbids colours `{2, 3}` on each pair of the triangle,
leaves colour `1` to the triangle. -/
theorem hub_lemma (x y z w : ℕ) (hx : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4)
    (hy : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4) (hz : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4)
    (hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (h₁ : w = 1 → ¬ ((x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2)))
    (h₂ : w = 1 → ¬ ((x = 2 ∧ z = 3) ∨ (x = 3 ∧ z = 2)))
    (h₃ : w = 1 → ¬ ((y = 2 ∧ z = 3) ∨ (y = 3 ∧ z = 2))) :
    x = 1 ∨ y = 1 ∨ z = 1 := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;> simp_all

/-- **Core step** (Voigt's Lemma, pure arithmetic).  `a b c d` colour the `K₄` `A B C D`,
`e` colours `E ∼ A, B, D` and `o` colours `O ∼ B, C, D`; colour `1` cannot meet each of the
triangles `ABE`, `BDE`, `ADE`, `BDO`. -/
theorem core_contradiction (a b c d e o : ℕ) (ha : 1 ≤ a ∧ a ≤ 4) (hb : 1 ≤ b ∧ b ≤ 4)
    (hc : 1 ≤ c ∧ c ≤ 4) (hd : 1 ≤ d ∧ d ≤ 4) (he : 1 ≤ e ∧ e ≤ 4) (ho : 1 ≤ o ∧ o ≤ 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hea : e ≠ a) (heb : e ≠ b) (hed : e ≠ d) (hob : o ≠ b) (hoc : o ≠ c) (hod : o ≠ d)
    (hF : a = 1 ∨ b = 1 ∨ e = 1) (hL : b = 1 ∨ d = 1 ∨ e = 1)
    (hM : a = 1 ∨ d = 1 ∨ e = 1) (hN : b = 1 ∨ d = 1 ∨ o = 1) : False := by
  omega

/-- The edges of the basic graph used by the core argument. -/
theorem core_adj :
    voigtGraph.Adj (vtx 0) (vtx 1) ∧ voigtGraph.Adj (vtx 0) (vtx 2) ∧
    voigtGraph.Adj (vtx 0) (vtx 3) ∧ voigtGraph.Adj (vtx 1) (vtx 2) ∧
    voigtGraph.Adj (vtx 1) (vtx 3) ∧ voigtGraph.Adj (vtx 2) (vtx 3) ∧
    voigtGraph.Adj (vtx 4) (vtx 0) ∧ voigtGraph.Adj (vtx 4) (vtx 1) ∧
    voigtGraph.Adj (vtx 4) (vtx 3) ∧ voigtGraph.Adj (vtx 9) (vtx 1) ∧
    voigtGraph.Adj (vtx 9) (vtx 2) ∧ voigtGraph.Adj (vtx 9) (vtx 3) ∧
    voigtGraph.Adj (vtx 5) (vtx 0) ∧ voigtGraph.Adj (vtx 5) (vtx 1) ∧
    voigtGraph.Adj (vtx 5) (vtx 4) ∧ voigtGraph.Adj (vtx 6) (vtx 1) ∧
    voigtGraph.Adj (vtx 6) (vtx 3) ∧ voigtGraph.Adj (vtx 6) (vtx 4) ∧
    voigtGraph.Adj (vtx 7) (vtx 0) ∧ voigtGraph.Adj (vtx 7) (vtx 3) ∧
    voigtGraph.Adj (vtx 7) (vtx 4) ∧ voigtGraph.Adj (vtx 8) (vtx 1) ∧
    voigtGraph.Adj (vtx 8) (vtx 3) ∧ voigtGraph.Adj (vtx 8) (vtx 9) := by
  decide +kernel

/-- **Voigt's theorem, list form**: `voigtGraph` has no proper colouring from `voigtList`. -/
theorem voigt_not_listColourable : ¬ ListColourable voigtGraph voigtList := by
  rintro ⟨c, hc⟩
  obtain ⟨AB, AC, AD, BC, BD, CD, EA, EB, ED, OB, OC, OD, FA, FB, FE, LB, LD, LE, MA, MD, ME,
    NB, ND, NO⟩ := core_adj
  have ne : ∀ {u w}, voigtGraph.Adj u w → c u ≠ c w := fun h => c.valid h
  have col : ∀ n < 22, c (vtx n) = 1 ∨ c (vtx n) = 2 ∨ c (vtx n) = 3 ∨ c (vtx n) = 4 :=
    fun n hn => base_colour c hc hn
  have u : ∀ k < 12, c (vtx (unitW k)) = 1 → ¬ ((c (vtx (unitU k)) = 2 ∧
      c (vtx (unitV k)) = 3) ∨ (c (vtx (unitU k)) = 3 ∧ c (vtx (unitV k)) = 2)) :=
    fun k hk => unit_blocks c hc hk
  -- the twelve marked triangles `U_k W_k V_k`, with their corners made explicit
  have u0 : c (vtx 5) = 1 → ¬ ((c (vtx 0) = 2 ∧ c (vtx 4) = 3) ∨
      (c (vtx 0) = 3 ∧ c (vtx 4) = 2)) := u 0 (by decide)
  have u1 : c (vtx 5) = 1 → ¬ ((c (vtx 4) = 2 ∧ c (vtx 1) = 3) ∨
      (c (vtx 4) = 3 ∧ c (vtx 1) = 2)) := u 1 (by decide)
  have u2 : c (vtx 5) = 1 → ¬ ((c (vtx 0) = 2 ∧ c (vtx 1) = 3) ∨
      (c (vtx 0) = 3 ∧ c (vtx 1) = 2)) := u 2 (by decide)
  have u3 : c (vtx 6) = 1 → ¬ ((c (vtx 1) = 2 ∧ c (vtx 3) = 3) ∨
      (c (vtx 1) = 3 ∧ c (vtx 3) = 2)) := u 3 (by decide)
  have u4 : c (vtx 6) = 1 → ¬ ((c (vtx 3) = 2 ∧ c (vtx 4) = 3) ∨
      (c (vtx 3) = 3 ∧ c (vtx 4) = 2)) := u 4 (by decide)
  have u5 : c (vtx 6) = 1 → ¬ ((c (vtx 1) = 2 ∧ c (vtx 4) = 3) ∨
      (c (vtx 1) = 3 ∧ c (vtx 4) = 2)) := u 5 (by decide)
  have u6 : c (vtx 7) = 1 → ¬ ((c (vtx 0) = 2 ∧ c (vtx 3) = 3) ∨
      (c (vtx 0) = 3 ∧ c (vtx 3) = 2)) := u 6 (by decide)
  have u7 : c (vtx 7) = 1 → ¬ ((c (vtx 3) = 2 ∧ c (vtx 4) = 3) ∨
      (c (vtx 3) = 3 ∧ c (vtx 4) = 2)) := u 7 (by decide)
  have u8 : c (vtx 7) = 1 → ¬ ((c (vtx 0) = 2 ∧ c (vtx 4) = 3) ∨
      (c (vtx 0) = 3 ∧ c (vtx 4) = 2)) := u 8 (by decide)
  have u9 : c (vtx 8) = 1 → ¬ ((c (vtx 1) = 2 ∧ c (vtx 3) = 3) ∨
      (c (vtx 1) = 3 ∧ c (vtx 3) = 2)) := u 9 (by decide)
  have u10 : c (vtx 8) = 1 → ¬ ((c (vtx 3) = 2 ∧ c (vtx 9) = 3) ∨
      (c (vtx 3) = 3 ∧ c (vtx 9) = 2)) := u 10 (by decide)
  have u11 : c (vtx 8) = 1 → ¬ ((c (vtx 1) = 2 ∧ c (vtx 9) = 3) ∨
      (c (vtx 1) = 3 ∧ c (vtx 9) = 2)) := u 11 (by decide)
  have hF := hub_lemma _ _ _ _ (col 0 (by decide)) (col 1 (by decide)) (col 4 (by decide))
    (col 5 (by decide)) (ne AB) (ne EB).symm (ne EA).symm (ne FA) (ne FB) (ne FE)
    u2 u0 fun h h' => u1 h (h'.elim (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩) fun ⟨a, b⟩ => Or.inl ⟨b, a⟩)
  have hL := hub_lemma _ _ _ _ (col 1 (by decide)) (col 3 (by decide)) (col 4 (by decide))
    (col 6 (by decide)) (ne BD) (ne ED).symm (ne EB).symm (ne LB) (ne LD) (ne LE)
    u3 u5 u4
  have hM := hub_lemma _ _ _ _ (col 0 (by decide)) (col 3 (by decide)) (col 4 (by decide))
    (col 7 (by decide)) (ne AD) (ne ED).symm (ne EA).symm (ne MA) (ne MD) (ne ME)
    u6 u8 u7
  have hN := hub_lemma _ _ _ _ (col 1 (by decide)) (col 3 (by decide)) (col 9 (by decide))
    (col 8 (by decide)) (ne BD) (ne OD).symm (ne OB).symm (ne NB) (ne ND) (ne NO)
    u9 u11 u10
  have r : ∀ n < 22, 1 ≤ c (vtx n) ∧ c (vtx n) ≤ 4 := fun n hn => by
    rcases col n hn with h | h | h | h <;> omega
  exact core_contradiction _ _ _ _ _ _ (r 0 (by decide)) (r 1 (by decide)) (r 2 (by decide))
    (r 3 (by decide)) (r 4 (by decide)) (r 9 (by decide)) (ne AB) (ne AC) (ne AD) (ne BC)
    (ne BD) (ne CD) (ne EA) (ne EB) (ne ED) (ne OB) (ne OC) (ne OD) hF hL hM hN

/-- Voigt's graph is not `4`-choosable (with colours in `ℕ`). -/
theorem voigt_not_choosableWith_four : ¬ ChoosableWith voigtGraph ℕ 4 := fun h =>
  voigt_not_listColourable (h voigtList fun v => (voigtList_card v).ge)

end LeanPool.K5MinorFreeChoosability.Voigt
