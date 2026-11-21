/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The event tree, date sums and discounted expected utility

Miao, §13.1, pp. 415–416, as used in §§13.4–13.5 (pp. 424–439).

A node (history) `sᵗ = (s₀, s₁, …, sₜ)` is a list of shocks over a finite set `S`, *newest
first*: the root `s⁰` is `[]`, the date of a node is its length, the immediate successors of
`h` are `s :: h` (`s ∈ S`) and the immediate predecessor of `s :: h` is `h`. The descendants of
`h` at distance `j` are the lists `l ++ h` with `l` of length `j`.

* `rd_paths S j`: the finite set of shock lists of length `j` (`rd_mem_paths`).
* `rd_dsum F h j = ∑_{sᵗ⁺ʲ | h} F(sᵗ⁺ʲ)`: the sum of `F` over the descendants of `h` at distance
  `j`; `rd_dsum F [] t` is the sum over all date-`t` nodes. It satisfies the root-side recursion
  `rd_dsum_succ`, the leaf-side recursion `rd_dsum_succ'` and `rd_dsum_add_len`.
* `RDTree S`: the probabilities `Pr(sᵗ)` (positive, `Pr(s⁰) = 1`, consistent:
  `∑ₛ Pr(s :: h) = Pr(h)`); `rd_uniformTree` is a concrete instance. `rd_condE` is the
  conditional expectation `E_t[X_{t+j}]`.
* `rd_Bdd`, `rd_LinfPos`, `rd_L1`: the spaces `L^∞`, `L^∞₊` and `L¹` of adapted processes.
  `L¹` is read with respect to the date sums (`∑ₜ ∑_{sᵗ} |x(sᵗ)| < ∞`, as on p. 416).
* `rd_EU`: the discounted expected utility (13.1); `rd_eq_13_1` shows it is strictly increasing on
  `L^∞₊` when `u` is strictly increasing (the property used by Theorem 13.4.1).
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- Appending a single shock at the old end of a list is injective. -/
theorem rd_snoc_injective (S : Type*) :
    Function.Injective (fun x : List S × S => x.1 ++ [x.2]) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ hab
  have h := List.append_inj' hab rfl
  simp only [List.cons.injEq, and_true] at h
  rw [h.1, h.2]

/-- The finite set of all shock lists of length `j`. -/
def rd_paths (S : Type*) [Fintype S] : ℕ → Finset (List S)
  | 0 => {[]}
  | j + 1 => (rd_paths S j ×ˢ Finset.univ).map ⟨fun x => x.1 ++ [x.2], rd_snoc_injective S⟩

/-- Membership in `rd_paths S j` is having length `j`. -/
theorem rd_mem_paths {S : Type*} [Fintype S] (j : ℕ) (l : List S) :
    l ∈ rd_paths S j ↔ l.length = j := by
  induction j generalizing l with
  | zero => simp [rd_paths]
  | succ j ih =>
    simp only [rd_paths, Finset.mem_map, Finset.mem_product, Finset.mem_univ, and_true,
      Function.Embedding.coeFn_mk, Prod.exists, ih]
    constructor
    · rintro ⟨a, b, ha, rfl⟩
      simp [ha]
    · intro hl
      have hne : l ≠ [] := by
        rintro rfl
        simp at hl
      refine ⟨l.dropLast, l.getLast hne, ?_, List.dropLast_append_getLast hne⟩
      simp [hl]

/-- The sum of `F` over the descendants of the node `h` at distance `j`. -/
def rd_dsum {S : Type*} [Fintype S] (F : List S → ℝ) (h : List S) (j : ℕ) : ℝ :=
  ∑ l ∈ rd_paths S j, F (l ++ h)

variable {S : Type*} [Fintype S]

/-- Distance `0`: the node itself. -/
theorem rd_dsum_zero (F : List S → ℝ) (h : List S) : rd_dsum F h 0 = F h := by
  simp [rd_dsum, rd_paths]

/-- Root-side recursion: descendants at distance `j + 1` of `h` are the descendants at distance
`j` of its successors `s :: h`. -/
theorem rd_dsum_succ (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum F h (j + 1) = ∑ s, rd_dsum F (s :: h) j := by
  simp only [rd_dsum, rd_paths, Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_product,
    List.append_assoc, List.singleton_append]
  exact Finset.sum_comm

/-- Splitting the distance: `∑_{a+b}` is the sum over distance-`a` nodes of distance-`b` sums. -/
theorem rd_dsum_add_len (F : List S → ℝ) (h : List S) (a b : ℕ) :
    rd_dsum F h (a + b) = rd_dsum (fun g => rd_dsum F g b) h a := by
  induction a generalizing h with
  | zero => simp [rd_dsum_zero]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring, rd_dsum_succ, rd_dsum_succ]
    exact Finset.sum_congr rfl fun s _ => ih (s :: h)

/-- Leaf-side recursion: the distance-`(j + 1)` sum is the distance-`j` sum of the sums over
immediate successors. -/
theorem rd_dsum_succ' (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum F h (j + 1) = rd_dsum (fun g => ∑ s, F (s :: g)) h j := by
  rw [rd_dsum_add_len]
  congr 1
  funext g
  rw [rd_dsum_succ]
  simp [rd_dsum_zero]

theorem rd_dsum_add (F G : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => F g + G g) h j = rd_dsum F h j + rd_dsum G h j :=
  Finset.sum_add_distrib

theorem rd_dsum_sub (F G : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => F g - G g) h j = rd_dsum F h j - rd_dsum G h j :=
  Finset.sum_sub_distrib _ _

theorem rd_dsum_neg (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => -F g) h j = -rd_dsum F h j :=
  Finset.sum_neg_distrib _

theorem rd_dsum_const_mul (a : ℝ) (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => a * F g) h j = a * rd_dsum F h j :=
  (Finset.mul_sum _ _ _).symm

theorem rd_dsum_finsetSum {ι : Type*} (A : Finset ι) (F : ι → List S → ℝ) (h : List S)
    (j : ℕ) : rd_dsum (fun g => ∑ i ∈ A, F i g) h j = ∑ i ∈ A, rd_dsum (F i) h j :=
  Finset.sum_comm

theorem rd_dsum_mono {F G : List S → ℝ} (hFG : ∀ g, F g ≤ G g) (h : List S) (j : ℕ) :
    rd_dsum F h j ≤ rd_dsum G h j :=
  Finset.sum_le_sum fun _ _ => hFG _

theorem rd_dsum_nonneg {F : List S → ℝ} (hF : ∀ g, 0 ≤ F g) (h : List S) (j : ℕ) :
    0 ≤ rd_dsum F h j :=
  Finset.sum_nonneg fun _ _ => hF _

theorem rd_dsum_congr {F G : List S → ℝ} (hFG : ∀ g, F g = G g) (h : List S) (j : ℕ) :
    rd_dsum F h j = rd_dsum G h j := by
  rw [funext hFG]

theorem rd_abs_dsum_le (F : List S → ℝ) (h : List S) (j : ℕ) :
    |rd_dsum F h j| ≤ rd_dsum (fun g => |F g|) h j :=
  Finset.abs_sum_le_sum_abs _ _

/-- A single descendant is bounded by the sum (nonnegative summands). -/
theorem rd_le_dsum {F : List S → ℝ} (hF : ∀ g, 0 ≤ F g) {h l : List S} {j : ℕ}
    (hl : l.length = j) : F (l ++ h) ≤ rd_dsum F h j :=
  Finset.single_le_sum (f := fun l => F (l ++ h)) (fun _ _ => hF _)
    ((rd_mem_paths j l).2 hl)

/-- Strict monotonicity of the distance-`j` sum. -/
theorem rd_dsum_lt {F G : List S → ℝ} (hFG : ∀ g, F g ≤ G g) {h l : List S} {j : ℕ}
    (hl : l.length = j) (hlt : F (l ++ h) < G (l ++ h)) : rd_dsum F h j < rd_dsum G h j :=
  Finset.sum_lt_sum (fun _ _ => hFG _) ⟨l, (rd_mem_paths j l).2 hl, hlt⟩

/-- The date sum of the indicator of a node `n`. -/
theorem rd_dsum_ite [DecidableEq S] (n : List S) (a : ℝ) (j : ℕ) :
    rd_dsum (fun g => if g = n then a else 0) [] j = if n.length = j then a else 0 := by
  simp [rd_dsum, rd_mem_paths]

/-- The descendants of `h` at distance `j` are among the date-`(len h + j)` nodes. -/
theorem rd_dsum_le_root {F : List S → ℝ} (hF : ∀ g, 0 ≤ F g) (h : List S) (j : ℕ) :
    rd_dsum F h j ≤ rd_dsum F [] (h.length + j) := by
  rw [rd_dsum_add_len]
  have := rd_le_dsum (F := fun g => rd_dsum F g j) (fun g => rd_dsum_nonneg hF g j)
    (h := []) (l := h) rfl
  simpa using this

/-- A function supported on the subtree of `h` has date sums equal to its subtree sums. -/
theorem rd_dsum_subtree {G : List S → ℝ} {h : List S} (hG : ∀ g, ¬ h <:+ g → G g = 0)
    (j : ℕ) : rd_dsum G [] (h.length + j) = rd_dsum G h j := by
  rw [rd_dsum_add_len, rd_dsum]
  simp only [List.append_nil]
  rw [Finset.sum_eq_single_of_mem h ((rd_mem_paths _ h).2 rfl)]
  · intro l hl hlh
    rw [rd_mem_paths] at hl
    refine Finset.sum_eq_zero fun l' _ => hG _ ?_
    rintro ⟨t, ht⟩
    have hlen : t.length = l'.length := by
      have := congrArg List.length ht
      simp only [List.length_append] at this
      omega
    exact hlh (List.append_inj ht hlen).2.symm

/-- A function supported on the subtree of `h` has zero date sums before the date of `h`. -/
theorem rd_dsum_subtree_early {G : List S → ℝ} {h : List S} (hG : ∀ g, ¬ h <:+ g → G g = 0)
    {t : ℕ} (ht : t < h.length) : rd_dsum G [] t = 0 := by
  refine Finset.sum_eq_zero fun l hl => hG _ ?_
  rw [rd_mem_paths] at hl
  intro hs
  have := hs.length_le
  simp only [List.append_nil] at this
  omega

/-- The probabilities on the event tree: `Pr(sᵗ) > 0`, `Pr(s⁰) = 1`, and
`∑_{s} Pr(s :: h) = Pr(h)`. -/
structure RDTree (S : Type*) [Fintype S] where
  /-- The unconditional probability `Pr(sᵗ)`. -/
  Pr : List S → ℝ
  /-- Every node has positive probability. -/
  pos : ∀ h, 0 < Pr h
  /-- `Pr(s⁰) = 1`. -/
  root : Pr [] = 1
  /-- Consistency of the probabilities of successors. -/
  cons : ∀ h, ∑ s, Pr (s :: h) = Pr h

/-- The probabilities of the descendants at distance `j` sum to the probability of the node. -/
theorem rd_dsum_Pr (T : RDTree S) (h : List S) (j : ℕ) : rd_dsum T.Pr h j = T.Pr h := by
  induction j generalizing h with
  | zero => exact rd_dsum_zero _ _
  | succ j ih =>
    rw [rd_dsum_succ]
    simp only [ih, T.cons]

/-- The uniform tree: every shock has conditional probability `1 / |S|`. -/
noncomputable def rd_uniformTree (S : Type*) [Fintype S] [Nonempty S] : RDTree S where
  Pr h := ((Fintype.card S : ℝ)⁻¹) ^ h.length
  pos h := pow_pos (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)) _
  root := by simp
  cons h := by
    have hc : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [List.length_cons, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_succ]
    field_simp

/-- The conditional probability `Pr(s | h) = Pr(s :: h) / Pr(h)`. -/
noncomputable def rd_condPr (T : RDTree S) (h : List S) (s : S) : ℝ := T.Pr (s :: h) / T.Pr h

/-- Conditional probabilities sum to one. -/
theorem rd_condPr_sum (T : RDTree S) (h : List S) : ∑ s, rd_condPr T h s = 1 := by
  simp only [rd_condPr, div_eq_mul_inv, ← Finset.sum_mul, T.cons]
  exact mul_inv_cancel₀ (T.pos h).ne'

/-- The conditional expectation `E_t[X_{t+j}]` at the date-`t` node `h`. -/
noncomputable def rd_condE (T : RDTree S) (X : List S → ℝ) (h : List S) (j : ℕ) : ℝ :=
  (T.Pr h)⁻¹ * rd_dsum (fun g => T.Pr g * X g) h j

/-- The unconditional expectation `E[X_t]` is the conditional one at the root. -/
theorem rd_condE_root (T : RDTree S) (X : List S → ℝ) (t : ℕ) :
    rd_condE T X [] t = rd_dsum (fun g => T.Pr g * X g) [] t := by
  simp [rd_condE, T.root]

/-- One-step conditional expectation as a sum over successors. -/
theorem rd_condE_one (T : RDTree S) (X : List S → ℝ) (h : List S) :
    rd_condE T X h 1 = ∑ s, rd_condPr T h s * X (s :: h) := by
  rw [rd_condE, rd_dsum_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rd_dsum_zero, rd_condPr]
  ring

/-- Bounded adapted processes (`L^∞`). -/
def rd_Bdd (x : List S → ℝ) : Prop := ∃ M, ∀ h, |x h| ≤ M

/-- Nonnegative bounded processes (`L^∞₊`). -/
def rd_LinfPos (c : List S → ℝ) : Prop := rd_Bdd c ∧ ∀ h, 0 ≤ c h

/-- Summable processes (`L¹`): `∑ₜ ∑_{sᵗ} |x(sᵗ)| < ∞`. -/
def rd_L1 (q : List S → ℝ) : Prop := Summable (fun t => rd_dsum (fun g => |q g|) [] t)

/-- An `L¹` process times a bounded one is summable in absolute value over dates. -/
theorem rd_L1_mul_abs {q x : List S → ℝ} (hq : rd_L1 q) (hx : rd_Bdd x) :
    Summable (fun t => rd_dsum (fun g => |q g * x g|) [] t) := by
  obtain ⟨M, hM⟩ := hx
  refine Summable.of_nonneg_of_le (fun t => rd_dsum_nonneg (fun g => abs_nonneg _) _ _)
    (fun t => ?_) (hq.mul_left M)
  rw [← rd_dsum_const_mul]
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM g) (abs_nonneg _)

/-- An `L¹` process times a bounded one has summable date sums. -/
theorem rd_L1_mul {q x : List S → ℝ} (hq : rd_L1 q) (hx : rd_Bdd x) :
    Summable (fun t => rd_dsum (fun g => q g * x g) [] t) :=
  Summable.of_norm_bounded (rd_L1_mul_abs hq hx) fun t => by
    rw [Real.norm_eq_abs]
    exact rd_abs_dsum_le _ _ _

/-- The date sums of an `L¹` process times a bounded one tend to zero. -/
theorem rd_L1_mul_tendsto {q x : List S → ℝ} (hq : rd_L1 q) (hx : rd_Bdd x) :
    Tendsto (fun t => rd_dsum (fun g => q g * x g) [] t) atTop (𝓝 0) :=
  (rd_L1_mul hq hx).tendsto_atTop_zero

omit [Fintype S] in
/-- The constant process `1` is bounded. -/
theorem rd_bdd_one : rd_Bdd (fun _ : List S => (1 : ℝ)) := ⟨1, fun _ => by simp⟩

/-- `L¹` processes have date sums tending to zero. -/
theorem rd_L1_tendsto {q : List S → ℝ} (hq : rd_L1 q) :
    Tendsto (fun t => rd_dsum q [] t) atTop (𝓝 0) := by
  simpa using rd_L1_mul_tendsto hq rd_bdd_one

omit [Fintype S] in
/-- Bounded processes are closed under sums, differences and scaling. -/
theorem rd_bdd_add {x z : List S → ℝ} (hx : rd_Bdd x) (hz : rd_Bdd z) :
    rd_Bdd (fun h => x h + z h) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hz
  exact ⟨M + N, fun h => (abs_add_le _ _).trans (add_le_add (hM h) (hN h))⟩

omit [Fintype S] in
theorem rd_bdd_neg {x : List S → ℝ} (hx : rd_Bdd x) : rd_Bdd (fun h => -x h) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M, fun h => by simpa using hM h⟩

omit [Fintype S] in
theorem rd_bdd_sub {x z : List S → ℝ} (hx : rd_Bdd x) (hz : rd_Bdd z) :
    rd_Bdd (fun h => x h - z h) := by
  simpa [sub_eq_add_neg] using rd_bdd_add hx (rd_bdd_neg hz)

omit [Fintype S] in
theorem rd_bdd_const_mul (a : ℝ) {x : List S → ℝ} (hx : rd_Bdd x) :
    rd_Bdd (fun h => a * x h) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨|a| * M, fun h => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM h) (abs_nonneg a)⟩

/-- A utility functional is strictly increasing on `L^∞₊`. -/
def rd_StrictIncr (U : (List S → ℝ) → ℝ) : Prop :=
  ∀ c c', rd_LinfPos c → rd_LinfPos c' → (∀ h, c h ≤ c' h) → c ≠ c' → U c < U c'

/-- A utility functional is (weakly) increasing on `L^∞₊`. -/
def rd_Mono (U : (List S → ℝ) → ℝ) : Prop :=
  ∀ c c', rd_LinfPos c → rd_LinfPos c' → (∀ h, c h ≤ c' h) → U c ≤ U c'

omit [Fintype S] in
/-- Strictly increasing utility functionals are increasing. -/
theorem rd_mono_of_strictIncr {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U) : rd_Mono U := by
  intro c c' hc hc' hle
  by_cases h : c = c'
  · rw [h]
  · exact (hU c c' hc hc' hle h).le

/-- **(13.1)** (Miao, p. 416). The discounted expected utility
`U(c) = ∑ₜ ∑_{sᵗ} βᵗ u(cₜ(sᵗ)) Pr(sᵗ)`. -/
noncomputable def rd_EU (T : RDTree S) (β : ℝ) (u : ℝ → ℝ) (c : List S → ℝ) : ℝ :=
  ∑' t, β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t

/-- The date-`t` expected utility is bounded by `K` when `|u ∘ c| ≤ K`. -/
theorem rd_abs_dsum_Pr_le (T : RDTree S) {X : List S → ℝ} {K : ℝ} (hX : ∀ g, |X g| ≤ K)
    (h : List S) (j : ℕ) : |rd_dsum (fun g => T.Pr g * X g) h j| ≤ K * T.Pr h := by
  refine (rd_abs_dsum_le _ _ _).trans ?_
  rw [← rd_dsum_Pr T h j, ← rd_dsum_const_mul]
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [abs_mul, abs_of_pos (T.pos g), mul_comm]
  exact mul_le_mul_of_nonneg_right (hX g) (T.pos g).le

/-- The series (13.1) converges when `u ∘ c` is bounded and `0 ≤ β < 1`. -/
theorem rd_EU_summable (T : RDTree S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (u : ℝ → ℝ)
    {c : List S → ℝ} {K : ℝ} (hK : ∀ g, |u (c g)| ≤ K) :
    Summable (fun t => β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  have := rd_abs_dsum_Pr_le T hK [] t
  rw [T.root, mul_one] at this
  exact mul_le_mul_of_nonneg_left this (pow_nonneg hβ0 t)

omit [Fintype S] in
/-- A utility increasing on `[0, ∞)` is bounded on a bounded nonnegative plan. -/
theorem rd_abs_u_le {u : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) {c : List S → ℝ}
    (hc : rd_LinfPos c) : ∃ K, ∀ g, |u (c g)| ≤ K := by
  obtain ⟨⟨M, hM⟩, h0⟩ := hc
  refine ⟨|u 0| + |u M|, fun g => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM g)
  have hcM : c g ≤ M := (le_abs_self _).trans (hM g)
  have h1 : u 0 ≤ u (c g) := hu (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (h0 g)) (h0 g)
  have h2 : u (c g) ≤ u M := hu (Set.mem_Ici.2 (h0 g)) (Set.mem_Ici.2 hM0) hcM
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (u 0), abs_nonneg (u M)]
  · linarith [le_abs_self (u M), abs_nonneg (u 0)]

/-- **(13.1)** (Miao, p. 416, with Assumption 13.1.1's monotonicity). If `u` is strictly
increasing on `[0, ∞)` and `0 < β < 1`, the discounted expected utility is strictly increasing
on `L^∞₊`: raising consumption weakly everywhere and strictly somewhere raises utility. -/
theorem rd_eq_13_1 (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hu : StrictMonoOn u (Set.Ici 0)) : rd_StrictIncr (rd_EU T β u) := by
  intro c c' hc hc' hle hne
  obtain ⟨K, hK⟩ := rd_abs_u_le hu.monotoneOn hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu.monotoneOn hc'
  obtain ⟨h0, hh0⟩ := Function.ne_iff.1 hne
  have hlt : c h0 < c' h0 := lt_of_le_of_ne (hle h0) hh0
  have hule : ∀ g, T.Pr g * u (c g) ≤ T.Pr g * u (c' g) := fun g =>
    mul_le_mul_of_nonneg_left (hu.monotoneOn (Set.mem_Ici.2 (hc.2 g))
      (Set.mem_Ici.2 (hc'.2 g)) (hle g)) (T.pos g).le
  refine Summable.tsum_lt_tsum (i := h0.length) (fun t => ?_) ?_
    (rd_EU_summable T hβ0.le hβ1 u hK) (rd_EU_summable T hβ0.le hβ1 u hK')
  · exact mul_le_mul_of_nonneg_left (rd_dsum_mono hule _ _) (pow_nonneg hβ0.le t)
  · refine mul_lt_mul_of_pos_left ?_ (pow_pos hβ0 _)
    refine rd_dsum_lt hule (l := h0) (by simp) ?_
    simp only [List.append_nil]
    exact mul_lt_mul_of_pos_left (hu (Set.mem_Ici.2 (hc.2 h0)) (Set.mem_Ici.2 (hc'.2 h0)) hlt)
      (T.pos h0)

end Miao.CompleteMarkets
