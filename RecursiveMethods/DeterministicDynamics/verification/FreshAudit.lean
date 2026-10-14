import Mathlib
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Extended real numbers for the sequence problem

SLP §4.1 lets the supremum function `v*` and the objective `u` take the values `±∞`. They take
values in `EReal`, where the needed algebra is collected here.

* `addIso`, `mulIso`: `z ↦ c + z` and `z ↦ βz` (`β > 0`) are order isomorphisms of `EReal`, so
  they commute with suprema and are continuous.
* `add_mul_biSup`: `c + β ⨆ᵢ gᵢ = ⨆ᵢ (c + βgᵢ)` for real `c`, `β ≥ 0` and a nonempty index set.
* `coe_mul_add`: `b(d + e) = bd + be` for real `b ≥ 0` and `d`.
* `le_of_le_add_limsup`, `le_of_add_le_liminf`: passing to the limit in `a ≤ sₙ + wₙ` and
  `sₙ + wₙ ≤ a` when `sₙ` converges and `wₙ` is asymptotically `≤ 0` (resp. `≥ 0`).
* `eq_biSup_iff`: the book's description of a supremum in `R̄` through the three cases
  "finite", `+∞` and `−∞` (SLP (2)–(3) and (4)–(7), pp. 70–71).
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

/-- `z ↦ c + z` is an order isomorphism of `EReal`. -/
noncomputable def addIso (c : ℝ) : EReal ≃o EReal where
  toFun z := (c : EReal) + z
  invFun z := ((-c : ℝ) : EReal) + z
  left_inv z := by
    induction z with
    | bot => simp
    | top => simp
    | coe z => simp only [← EReal.coe_add]; congr 1; ring
  right_inv z := by
    induction z with
    | bot => simp
    | top => simp
    | coe z => simp only [← EReal.coe_add]; congr 1; ring
  map_rel_iff' {x y} := by
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      have := add_le_add (le_refl ((-c : ℝ) : EReal)) h
      rwa [← add_assoc, ← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add,
        zero_add] at this
    · exact fun h => add_le_add (le_refl _) h

theorem addIso_apply (c : ℝ) (z : EReal) : addIso c z = (c : EReal) + z := rfl

/-- `z ↦ βz` is an order isomorphism of `EReal` for `β > 0`. -/
noncomputable def mulIso (β : ℝ) (hβ : 0 < β) : EReal ≃o EReal where
  toFun z := (β : EReal) * z
  invFun z := ((β⁻¹ : ℝ) : EReal) * z
  left_inv z := by
    simp only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hβ.ne', EReal.coe_one, one_mul]
  right_inv z := by
    simp only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hβ.ne', EReal.coe_one, one_mul]
  map_rel_iff' {x y} := by
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ ((β⁻¹ : ℝ) : EReal) from
        EReal.coe_nonneg.2 (inv_nonneg.2 hβ.le))
      simpa only [Equiv.coe_fn_mk, ← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hβ.ne',
        EReal.coe_one, one_mul] using this
    · intro h
      exact mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 hβ.le)

theorem mulIso_apply (β : ℝ) (hβ : 0 < β) (z : EReal) : mulIso β hβ z = (β : EReal) * z := rfl

/-- `c + β ⨆_{i ∈ s} gᵢ = ⨆_{i ∈ s} (c + βgᵢ)` for real `c`, `β ≥ 0`, `s` nonempty. -/
theorem add_mul_biSup {ι : Type*} (c β : ℝ) (hβ : 0 ≤ β) {s : Set ι} (hs : s.Nonempty)
    (g : ι → EReal) :
    (c : EReal) + (β : EReal) * ⨆ i ∈ s, g i = ⨆ i ∈ s, ((c : EReal) + (β : EReal) * g i) := by
  rcases hβ.eq_or_lt with h0 | hpos
  · subst h0
    simp only [EReal.coe_zero, zero_mul, add_zero]
    exact (biSup_const hs).symm
  · have h1 : (β : EReal) * ⨆ i ∈ s, g i = ⨆ i ∈ s, (β : EReal) * g i :=
      map_iSup₂ (mulIso β hpos) fun i _ => g i
    have h2 : (c : EReal) + ⨆ i ∈ s, (β : EReal) * g i =
        ⨆ i ∈ s, ((c : EReal) + (β : EReal) * g i) :=
      map_iSup₂ (addIso c) fun i _ => (β : EReal) * g i
    rw [h1, h2]

/-- `z ↦ c + βz` is continuous on `EReal` for real `c` and `β ≥ 0`. -/
theorem continuous_add_mul (c β : ℝ) (hβ : 0 ≤ β) :
    Continuous fun z : EReal => (c : EReal) + (β : EReal) * z := by
  rcases hβ.eq_or_lt with h0 | hpos
  · subst h0
    simp only [EReal.coe_zero, zero_mul, add_zero]
    exact continuous_const
  · exact (addIso c).continuous.comp (mulIso β hpos).continuous

/-- `b(d + e) = bd + be` for real `b ≥ 0` and real `d`. -/
theorem coe_mul_add (b d : ℝ) (hb : 0 ≤ b) (e : EReal) :
    (b : EReal) * ((d : EReal) + e) = (b : EReal) * d + (b : EReal) * e := by
  rcases hb.eq_or_lt with h0 | hpos
  · subst h0; simp
  · induction e with
    | bot => simp [EReal.coe_mul_bot_of_pos hpos]
    | top => simp [EReal.coe_mul_top_of_pos hpos, ← EReal.coe_mul]
    | coe e => simp only [← EReal.coe_add, ← EReal.coe_mul]; congr 1; ring

/-- If `a ≤ sₙ + wₙ` for all `n`, `sₙ → L` and `limsup wₙ ≤ 0`, then `a ≤ L`. -/
theorem le_of_le_add_limsup {a L : EReal} {s w : ℕ → EReal} (h : ∀ n, a ≤ s n + w n)
    (hs : Tendsto s atTop (𝓝 L)) (hw : limsup w atTop ≤ 0) : a ≤ L := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hLp, hpa⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨q, hpq, hqa⟩ := EReal.lt_iff_exists_real_btwn.1 hpa
  have hpq' : p < q := EReal.coe_lt_coe_iff.1 hpq
  have h1 : ∀ᶠ n in atTop, s n < p := hs.eventually (gt_mem_nhds hLp)
  have h2 : ∀ᶠ n in atTop, w n < ((q - p : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt (hw.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith)))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have := EReal.add_lt_add hn1 hn2
  rw [← EReal.coe_add, show p + (q - p) = q by ring] at this
  exact absurd ((h n).trans_lt (this.trans hqa)) (lt_irrefl a)

/-- If `sₙ + wₙ ≤ a` for all `n`, `sₙ → L` and `liminf wₙ ≥ 0`, then `L ≤ a`. -/
theorem le_of_add_le_liminf {a L : EReal} {s w : ℕ → EReal} (h : ∀ n, s n + w n ≤ a)
    (hs : Tendsto s atTop (𝓝 L)) (hw : 0 ≤ liminf w atTop) : L ≤ a := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hap, hpL⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨q, hpq, hqL⟩ := EReal.lt_iff_exists_real_btwn.1 hpL
  have hpq' : p < q := EReal.coe_lt_coe_iff.1 hpq
  have h1 : ∀ᶠ n in atTop, (q : EReal) < s n := hs.eventually (lt_mem_nhds hqL)
  have h2 : ∀ᶠ n in atTop, ((p - q : ℝ) : EReal) < w n :=
    eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.2 (by linarith)).trans_le hw)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have := EReal.add_lt_add hn1 hn2
  rw [← EReal.coe_add, show q + (p - q) = p by ring] at this
  exact absurd ((hap.trans this).trans_le (h n)) (lt_irrefl a)

/-- `v ≤ w` as soon as every real `a < v` satisfies `a ≤ w`. -/
theorem le_of_forall_coe_lt_le {v w : EReal} (h : ∀ a : ℝ, (a : EReal) < v → (a : EReal) ≤ w) :
    v ≤ w := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, hwa, hav⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  exact absurd (h a hav) (not_le.2 hwa)

/-- **The book's description of a supremum** (SLP (2)–(3), (4)–(7), pp. 70–71):
`v = ⨆_{i ∈ s} fᵢ` iff (a) when `v` is finite, `fᵢ ≤ v` for all `i ∈ s` and `v ≤ fᵢ + ε` for
some `i ∈ s`, for every `ε > 0`; (b) when `v = +∞`, some sequence in `s` has `f → +∞`; and
(c) when `v = −∞`, every `fᵢ = −∞`. -/
theorem eq_biSup_iff {ι : Type*} {s : Set ι} {f : ι → EReal} {v : EReal} :
    v = ⨆ i ∈ s, f i ↔
      (∀ r : ℝ, v = r → (∀ i ∈ s, f i ≤ r) ∧ ∀ ε > (0 : ℝ), ∃ i ∈ s, (r : EReal) ≤ f i + ε) ∧
      (v = ⊤ → ∃ i : ℕ → ι, (∀ k, i k ∈ s) ∧ Tendsto (fun k => f (i k)) atTop (𝓝 ⊤)) ∧
      (v = ⊥ → ∀ i ∈ s, f i = ⊥) := by
  constructor
  · rintro rfl
    refine ⟨fun r hr => ⟨fun i hi => hr ▸ le_biSup f hi, fun ε hε => ?_⟩, fun htop => ?_,
      fun hbot i hi => le_bot_iff.1 (hbot ▸ le_biSup f hi)⟩
    · have hlt : ((r - ε : ℝ) : EReal) < ⨆ i ∈ s, f i := by
        rw [hr]; exact EReal.coe_lt_coe_iff.2 (by linarith)
      obtain ⟨i, hi, hfi⟩ := lt_biSup_iff.1 hlt
      refine ⟨i, hi, ?_⟩
      have := add_le_add hfi.le (le_refl (ε : EReal))
      rwa [← EReal.coe_add, sub_add_cancel] at this
    · have hk : ∀ k : ℕ, ∃ i ∈ s, ((k : ℝ) : EReal) < f i := fun k =>
        lt_biSup_iff.1 (htop ▸ EReal.coe_lt_top (k : ℝ))
      choose i hi hfi using hk
      refine ⟨i, hi, EReal.tendsto_nhds_top_iff_real.2 fun x => ?_⟩
      obtain ⟨k, hk⟩ := exists_nat_gt x
      filter_upwards [eventually_ge_atTop k] with m hm
      exact (EReal.coe_lt_coe_iff.2 (hk.trans_le (Nat.cast_le.2 hm))).trans (hfi m)
  · rintro ⟨hfin, htop, hbot⟩
    induction v with
    | bot => exact (le_bot_iff.1 (iSup₂_le fun i hi => (hbot rfl i hi).le)).symm
    | top =>
      obtain ⟨i, hi, hlim⟩ := htop rfl
      refine (top_le_iff.1 ?_).symm
      refine le_of_tendsto' hlim fun k => le_biSup f (hi k)
    | coe r =>
      obtain ⟨hle, happ⟩ := hfin r rfl
      refine le_antisymm ?_ (iSup₂_le hle)
      refine le_of_forall_coe_lt_le fun a ha => ?_
      have hε : (0 : ℝ) < r - a := sub_pos.2 (EReal.coe_lt_coe_iff.1 ha)
      obtain ⟨i, hi, hri⟩ := happ (r - a) hε
      have h1 : f i ≤ ⨆ j ∈ s, f j := le_biSup f hi
      by_contra hS
      push Not at hS
      -- `f i ≤ S < a`, so `f i + (r − a) < r`
      have h2 := EReal.add_lt_add_right_coe (h1.trans_lt hS) (r - a)
      rw [← EReal.coe_add, add_sub_cancel] at h2
      exact absurd (hri.trans_lt h2) (lt_irrefl _)

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Principle of Optimality

SLP §4.1, pp. 67–77. The sequence problem

  (SP) `v*(x₀) = sup Σ_{t ≥ 0} βᵗ F(x_t, x_{t+1})` over plans with `x_{t+1} ∈ Γ(x_t)`,

and the functional equation

  (FE) `v(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]`,

with values in the extended reals `R̄ = EReal`.

* `Feasible` (`Π(x₀)`), `partialSum` (`uₙ`), `total` (`u`), `vstar` (`v*`), `SatisfiesFE`,
  `Assumption41`, `Assumption42`.
* `lemma_4_1`: `u(x) = F(x₀, x₁) + βu(x')`.
* `theorem_4_2`: `v*` satisfies (FE).
* `theorem_4_3`: a solution of (FE) with `βⁿv(xₙ) → 0` along every feasible plan is `v*`.
  Its two halves are `total_le_of_FE` and `ex_4_3a` (`v ≤ v*` when `limsup βⁿv(xₙ) ≤ 0`);
  `ex_4_3b` is Exercise 4.3b.
* `theorem_4_4`: an optimal plan satisfies `v*(x*_t) = F(x*_t, x*_{t+1}) + βv*(x*_{t+1})`.
  This needs `β > 0`; the book allows `β ≥ 0` (`theorem_4_4_beta_zero`).
* `theorem_4_5`: a feasible plan satisfying (9) with `limsup βᵗv*(x*_t) ≤ 0` is optimal.
* `Gstar`, `optimal_generated_by_Gstar`, `generated_by_Gstar_optimal`: the optimal policy
  correspondence.
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {X : Type*}

/-- `Π(x₀)`: the plans feasible from `x₀`. -/
def Feasible (Γ : X → Set X) (x₀ : X) : Set (ℕ → X) :=
  {x | x 0 = x₀ ∧ ∀ t, x (t + 1) ∈ Γ (x t)}

/-- `uₙ(x) = Σ_{t=0}^n βᵗ F(x_t, x_{t+1})`. -/
def partialSum (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (n + 1), β ^ t * F (x t) (x (t + 1))

/-- **Assumption 4.1.** `Γ(x)` is nonempty for every `x`. -/
def Assumption41 (Γ : X → Set X) : Prop := ∀ x, (Γ x).Nonempty

/-- **Assumption 4.2.** Along every feasible plan the partial sums converge in `R̄`. -/
def Assumption42 (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) : Prop :=
  ∀ x₀, ∀ x ∈ Feasible Γ x₀, ∃ L : EReal,
    Tendsto (fun n => (partialSum F β x n : EReal)) atTop (𝓝 L)

/-- `u(x) = lim uₙ(x)`. -/
noncomputable def total (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) : EReal :=
  limUnder atTop fun n => (partialSum F β x n : EReal)

/-- The supremum function `v*(x₀) = sup_{x ∈ Π(x₀)} u(x)`. -/
noncomputable def vstar (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (x₀ : X) : EReal :=
  ⨆ x ∈ Feasible Γ x₀, total F β x

/-- `v` satisfies the functional equation (FE). By `eq_biSup_iff` this is the book's
definition through (4)–(7), p. 71. -/
def SatisfiesFE (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (v : X → EReal) : Prop :=
  ∀ x, v x = ⨆ y ∈ Γ x, ((F x y : EReal) + (β : EReal) * v y)

variable {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

theorem tendsto_total (h42 : Assumption42 Γ F β) {x₀ : X} {x : ℕ → X} (hx : x ∈ Feasible Γ x₀) :
    Tendsto (fun n => (partialSum F β x n : EReal)) atTop (𝓝 (total F β x)) :=
  tendsto_nhds_limUnder (h42 x₀ x hx)

/-- The plan `x' = (x₁, x₂, …)`. -/
def tail (k : ℕ) (x : ℕ → X) : ℕ → X := fun t => x (t + k)

theorem tail_mem {x₀ : X} {x : ℕ → X} (hx : x ∈ Feasible Γ x₀) (k : ℕ) :
    tail k x ∈ Feasible Γ (x k) :=
  ⟨by simp [tail], fun t => by
    simp only [tail, show t + 1 + k = (t + k) + 1 by ring]
    exact hx.2 _⟩

theorem tail_tail (x : ℕ → X) (k : ℕ) : tail 1 (tail k x) = tail (k + 1) x := by
  funext t; simp only [tail]; congr 1; ring

/-- The plan `(x₀, x'₀, x'₁, …)`. -/
def consPlan (x₀ : X) (x' : ℕ → X) : ℕ → X
  | 0 => x₀
  | t + 1 => x' t

theorem consPlan_mem {x₀ y : X} (hy : y ∈ Γ x₀) {x' : ℕ → X} (hx' : x' ∈ Feasible Γ y) :
    consPlan x₀ x' ∈ Feasible Γ x₀ := by
  refine ⟨rfl, fun t => ?_⟩
  cases t with
  | zero => simpa [consPlan, hx'.1] using hy
  | succ t => exact hx'.2 t

theorem tail_consPlan (x₀ : X) (x' : ℕ → X) : tail 1 (consPlan x₀ x') = x' := rfl

/-- Under Assumption 4.1 every `Π(x₀)` is nonempty. -/
theorem feasible_nonempty (h41 : Assumption41 Γ) (x₀ : X) : (Feasible Γ x₀).Nonempty := by
  refine ⟨fun n => Nat.rec x₀ (fun _ z => (h41 z).some) n, rfl, fun t => ?_⟩
  exact (h41 _).some_mem

theorem partialSum_succ (x : ℕ → X) (n : ℕ) :
    partialSum F β x (n + 1) = F (x 0) (x 1) + β * partialSum F β (tail 1 x) n := by
  simp only [partialSum, tail]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem partialSum_succ' (x : ℕ → X) (n : ℕ) :
    partialSum F β x (n + 1) = partialSum F β x n + β ^ (n + 1) * F (x (n + 1)) (x (n + 2)) := by
  simp only [partialSum]
  rw [Finset.sum_range_succ]

/-- **Lemma 4.1.** `u(x) = F(x₀, x₁) + βu(x')` for every feasible plan, `β ≥ 0`. -/
theorem lemma_4_1 (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {x₀ : X} {x : ℕ → X}
    (hx : x ∈ Feasible Γ x₀) :
    total F β x = (F (x 0) (x 1) : EReal) + (β : EReal) * total F β (tail 1 x) := by
  have h1 := (tendsto_total h42 hx).comp (tendsto_add_atTop_nat 1)
  have h2 := ((continuous_add_mul (F (x 0) (x 1)) β hβ).tendsto _).comp
    (tendsto_total h42 (tail_mem hx 1))
  refine tendsto_nhds_unique h1 ?_
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, partialSum_succ, EReal.coe_add, EReal.coe_mul]

/-- **Theorem 4.2.** Under Assumptions 4.1–4.2, `v*` satisfies (FE). -/
theorem theorem_4_2 (hβ : 0 ≤ β) (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β) :
    SatisfiesFE Γ F β (vstar Γ F β) := by
  intro x₀
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    rw [lemma_4_1 hβ h42 hx]
    have hx1 : x 1 ∈ Γ x₀ := hx.1 ▸ hx.2 0
    calc (F (x 0) (x 1) : EReal) + (β : EReal) * total F β (tail 1 x)
        ≤ (F x₀ (x 1) : EReal) + (β : EReal) * vstar Γ F β (x 1) := by
          rw [hx.1]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (le_biSup (total F β) (tail_mem hx 1)) (EReal.coe_nonneg.2 hβ))
      _ ≤ _ := le_biSup (fun y => (F x₀ y : EReal) + (β : EReal) * vstar Γ F β y) hx1
  · refine iSup₂_le fun y hy => ?_
    rw [vstar, add_mul_biSup _ β hβ (feasible_nonempty h41 y)]
    refine iSup₂_le fun x' hx' => ?_
    have hc := consPlan_mem hy hx'
    have := lemma_4_1 hβ h42 hc
    rw [tail_consPlan] at this
    change total F β (consPlan x₀ x') = (F x₀ (x' 0) : EReal) + _ at this
    rw [hx'.1] at this
    rw [← this]
    exact le_biSup (total F β) hc

/-- Along a feasible plan, `uₙ(x) + βⁿ⁺¹v(xₙ₊₁) ≤ v(x₀)` when `v(x) ≥ F(x, y) + βv(y)` for all
`y ∈ Γ(x)`; in the limit, `u(x) ≤ v(x₀)` if `liminf βⁿv(xₙ) ≥ 0`. -/
theorem total_le_of_FE (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {v : X → EReal}
    (hv : ∀ x, ∀ y ∈ Γ x, (F x y : EReal) + (β : EReal) * v y ≤ v x) {x₀ : X} {x : ℕ → X}
    (hx : x ∈ Feasible Γ x₀)
    (hlim : 0 ≤ liminf (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop) :
    total F β x ≤ v x₀ := by
  have key : ∀ n, (partialSum F β x n : EReal) + ((β ^ (n + 1) : ℝ) : EReal) * v (x (n + 1)) ≤
      v x₀ := by
    intro n
    induction n with
    | zero =>
      simp only [partialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        pow_one]
      exact hx.1 ▸ hv _ _ (hx.2 0)
    | succ n ih =>
      refine le_trans ?_ ih
      rw [partialSum_succ', EReal.coe_add, add_assoc]
      refine add_le_add le_rfl ?_
      have hpow : (0 : ℝ) ≤ β ^ (n + 1) := pow_nonneg hβ _
      calc ((β ^ (n + 1) * F (x (n + 1)) (x (n + 2)) : ℝ) : EReal) +
            ((β ^ (n + 1 + 1) : ℝ) : EReal) * v (x (n + 1 + 1))
          = ((β ^ (n + 1) : ℝ) : EReal) *
              ((F (x (n + 1)) (x (n + 1 + 1)) : EReal) + (β : EReal) * v (x (n + 1 + 1))) := by
            rw [coe_mul_add _ _ hpow, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul, ← pow_succ]
        _ ≤ ((β ^ (n + 1) : ℝ) : EReal) * v (x (n + 1)) :=
            mul_le_mul_of_nonneg_left (hv _ _ (hx.2 _)) (EReal.coe_nonneg.2 hpow)
  refine le_of_add_le_liminf key (tendsto_total h42 hx) ?_
  rwa [liminf_nat_add (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) 1]

/-- From `a < c + βw` with `β > 0` and real `a, c`: `(a − c)/β < w`. -/
theorem div_lt_of_lt_add_mul {a c β : ℝ} (hβ : 0 < β) {w : EReal}
    (h : (a : EReal) < (c : EReal) + (β : EReal) * w) : (((a - c) / β : ℝ) : EReal) < w := by
  by_contra hle
  push Not at hle
  have := add_le_add (le_refl (c : EReal))
    (mul_le_mul_of_nonneg_left hle (EReal.coe_nonneg.2 hβ.le))
  rw [← EReal.coe_mul, ← EReal.coe_add, mul_div_cancel₀ _ hβ.ne', add_sub_cancel] at this
  exact absurd (h.trans_le this) (lt_irrefl _)

/-- **Exercise 4.3a.** If `v` satisfies (FE), `β > 0` and `limsup βⁿv(xₙ) ≤ 0` along every
feasible plan, then `v ≤ v*`. For a real `a < v(x₀)`, choose `x_{t+1} ∈ Γ(x_t)` with
`a_t < F(x_t, x_{t+1}) + βv(x_{t+1})` and set `a_{t+1} = (a_t − F(x_t, x_{t+1}))/β`; then
`a = uₙ(x) + βⁿ⁺¹a_{n+1} < uₙ(x) + βⁿ⁺¹v(x_{n+1})`, and `a ≤ u(x)` in the limit. -/
theorem ex_4_3a (hβ : 0 < β) (h42 : Assumption42 Γ F β) {v : X → EReal}
    (hv : SatisfiesFE Γ F β v)
    (hlim : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      limsup (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop ≤ 0) (x₀ : X) :
    v x₀ ≤ vstar Γ F β x₀ := by
  -- states paired with targets below their value
  set P := {p : X × ℝ // (p.2 : EReal) < v p.1}
  have hstep : ∀ p : P, ∃ y ∈ Γ p.1.1,
      (p.1.2 : EReal) < (F p.1.1 y : EReal) + (β : EReal) * v y := fun p =>
    lt_biSup_iff.1 (hv p.1.1 ▸ p.2)
  choose next hnext hlt using hstep
  let step : P → P := fun p =>
    ⟨(next p, (p.1.2 - F p.1.1 (next p)) / β), div_lt_of_lt_add_mul hβ (hlt p)⟩
  refine le_of_forall_coe_lt_le fun a ha => ?_
  let s : ℕ → P := fun n => step^[n] ⟨(x₀, a), ha⟩
  have hs : ∀ n, s (n + 1) = step (s n) := fun n => Function.iterate_succ_apply' _ _ _
  set x : ℕ → X := fun n => (s n).1.1
  set b : ℕ → ℝ := fun n => (s n).1.2
  have hx : x ∈ Feasible Γ x₀ := ⟨rfl, fun t => by
    change (s (t + 1)).1.1 ∈ Γ (s t).1.1
    rw [hs]; exact hnext _⟩
  have hb : ∀ t, b t = F (x t) (x (t + 1)) + β * b (t + 1) := fun t => by
    change (s t).1.2 = F (s t).1.1 (s (t + 1)).1.1 + β * (s (t + 1)).1.2
    rw [hs]
    change (s t).1.2 = F (s t).1.1 (next (s t)) + β * ((((s t).1.2 - F (s t).1.1 (next (s t))) / β))
    field_simp
    ring
  -- `a = uₙ(x) + βⁿ⁺¹ b_{n+1}`
  have hsum : ∀ n, a = partialSum F β x n + β ^ (n + 1) * b (n + 1) := by
    intro n
    induction n with
    | zero =>
      simp only [partialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        pow_one]
      exact hb 0
    | succ n ih =>
      rw [partialSum_succ', ih, hb (n + 1)]
      ring
  have key : ∀ n, (a : EReal) ≤ (partialSum F β x n : EReal) +
      ((β ^ (n + 1) : ℝ) : EReal) * v (x (n + 1)) := fun n => by
    rw [hsum n, EReal.coe_add, EReal.coe_mul]
    refine add_le_add le_rfl ((mulIso _ (pow_pos hβ _)).monotone (s (n + 1)).2.le)
  have hlim' := hlim x₀ x hx
  rw [← limsup_nat_add (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) 1] at hlim'
  exact (le_of_le_add_limsup key (tendsto_total h42 hx) hlim').trans (le_biSup _ hx)

/-- **Theorem 4.3.** Under Assumptions 4.1–4.2, a solution `v` of (FE) with `βⁿv(xₙ) → 0` along
every feasible plan is the supremum function. -/
theorem theorem_4_3 (hβ : 0 ≤ β) (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β)
    {v : X → EReal} (hv : SatisfiesFE Γ F β v)
    (h8 : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      Tendsto (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop (𝓝 0)) :
    v = vstar Γ F β := by
  funext x₀
  rcases hβ.eq_or_lt with h0 | hpos
  · -- with `β = 0` both sides equal `sup_{y ∈ Γ(x₀)} F(x₀, y)`
    subst h0
    rw [hv x₀, theorem_4_2 le_rfl h41 h42 x₀]
    simp only [EReal.coe_zero, zero_mul]
  · refine le_antisymm (ex_4_3a hpos h42 hv (fun x₀ x hx => (h8 x₀ x hx).limsup_eq.le) x₀) ?_
    refine iSup₂_le fun x hx => total_le_of_FE hpos.le h42 (fun x y hy => ?_) hx
      (h8 x₀ x hx).liminf_eq.ge
    rw [hv x]
    exact le_biSup (fun y => (F x y : EReal) + (β : EReal) * v y) hy

/-- **Exercise 4.3b.** If in addition to the hypotheses of Exercise 4.3a every feasible plan is
weakly dominated by one along which `βⁿv(xₙ) → 0`, then `v = v*`. -/
theorem ex_4_3b (hβ : 0 < β) (h42 : Assumption42 Γ F β) {v : X → EReal}
    (hv : SatisfiesFE Γ F β v)
    (hlim : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      limsup (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop ≤ 0)
    (hdom : ∀ x₀, ∀ x ∈ Feasible Γ x₀, ∃ x' ∈ Feasible Γ x₀,
      Tendsto (fun n => ((β ^ n : ℝ) : EReal) * v (x' n)) atTop (𝓝 0) ∧
        total F β x ≤ total F β x') :
    v = vstar Γ F β := by
  funext x₀
  refine le_antisymm (ex_4_3a hβ h42 hv hlim x₀) (iSup₂_le fun x hx => ?_)
  obtain ⟨x', hx', hlim', hle⟩ := hdom x₀ x hx
  refine hle.trans (total_le_of_FE hβ.le h42 (fun x y hy => ?_) hx' hlim'.liminf_eq.ge)
  rw [hv x]
  exact le_biSup (fun y => (F x y : EReal) + (β : EReal) * v y) hy

/-- **Theorem 4.4.** If `x*` is optimal from `x₀` and `β > 0`, then
`v*(x*_t) = F(x*_t, x*_{t+1}) + βv*(x*_{t+1})` for all `t`. -/
theorem theorem_4_4 (hβ : 0 < β) (h42 : Assumption42 Γ F β) {x₀ : X} {xs : ℕ → X}
    (hxs : xs ∈ Feasible Γ x₀) (hopt : total F β xs = vstar Γ F β x₀) (t : ℕ) :
    vstar Γ F β (xs t) =
      (F (xs t) (xs (t + 1)) : EReal) + (β : EReal) * vstar Γ F β (xs (t + 1)) := by
  -- every tail of an optimal plan is optimal
  have htail : ∀ k, total F β (tail k xs) = vstar Γ F β (xs k) := by
    intro k
    induction k with
    | zero =>
      have : tail 0 xs = xs := rfl
      rw [this, hopt, hxs.1]
    | succ k ih =>
      have hk := tail_mem hxs k
      refine le_antisymm ?_ (iSup₂_le fun x' hx' => ?_)
      · have := le_biSup (total F β) (tail_mem hk 1)
        have e : tail k xs 1 = xs (k + 1) := by simp [tail, add_comm]
        rw [tail_tail, e] at this
        exact this
      · have hy : xs (k + 1) ∈ Γ (xs k) := hxs.2 k
        have hc := consPlan_mem hy hx'
        have h1 : total F β (consPlan (xs k) x') ≤ total F β (tail k xs) :=
          ih ▸ le_biSup (total F β) hc
        rw [lemma_4_1 hβ.le h42 hc, lemma_4_1 hβ.le h42 hk, tail_consPlan, tail_tail] at h1
        change (F (xs k) (x' 0) : EReal) + _ ≤ (F (xs (0 + k)) (xs (1 + k)) : EReal) + _ at h1
        rw [hx'.1, zero_add, add_comm 1 k] at h1
        have h2 := ((addIso (F (xs k) (xs (k + 1)))).le_iff_le).1 h1
        exact ((mulIso β hβ).le_iff_le).1 h2
  have h1 := htail t
  rw [lemma_4_1 hβ.le h42 (tail_mem hxs t), tail_tail, htail (t + 1)] at h1
  have e0 : tail t xs 0 = xs t := by simp [tail]
  have e1 : tail t xs 1 = xs (t + 1) := by simp [tail, add_comm]
  rw [e0, e1] at h1
  exact h1.symm

/-- **Theorem 4.4 needs `β > 0`.** With `β = 0`, two states, `Γ(x) = {false, true}` and
`F(x, y) = 1` if `y = true`, `0` otherwise, the plan `(false, true, false, false, …)` is optimal
from `false`, but `v*(true) = 1 ≠ 0 = F(true, false) + 0 · v*(false)`, so (9) fails at `t = 1`. -/
theorem theorem_4_4_beta_zero :
    let F : Bool → Bool → ℝ := fun _ y => if y then 1 else 0
    let xs : ℕ → Bool := fun t => decide (t = 1)
    Assumption42 (fun _ => Set.univ) F 0 ∧ xs ∈ Feasible (fun _ => Set.univ) false ∧
      total F 0 xs = vstar (fun _ => Set.univ) F 0 false ∧
      vstar (fun _ => Set.univ) F 0 (xs 1) ≠
        (F (xs 1) (xs 2) : EReal) + ((0 : ℝ) : EReal) * vstar (fun _ => Set.univ) F 0 (xs 2) := by
  intro F xs
  -- with `β = 0` the partial sums are `F(x₀, x₁)`
  have hps : ∀ (x : ℕ → Bool) (n : ℕ), partialSum F 0 x n = F (x 0) (x 1) := by
    intro x n
    induction n with
    | zero => simp [partialSum]
    | succ n ih => rw [partialSum_succ', ih]; simp
  have h42 : Assumption42 (fun _ => Set.univ) F 0 := fun _ x _ =>
    ⟨_, by simp only [hps]; exact tendsto_const_nhds⟩
  have htot : ∀ x : ℕ → Bool, total F 0 x = (F (x 0) (x 1) : EReal) := fun x =>
    tendsto_nhds_unique (tendsto_nhds_limUnder (h42 (x 0) x ⟨rfl, fun _ => trivial⟩))
      (by simp only [hps]; exact tendsto_const_nhds)
  have hF1 : ∀ a b, F a b ≤ 1 := fun a b => by simp only [F]; split_ifs <;> norm_num
  -- `v*(b) = 1` for every `b`
  have hv : ∀ b, vstar (fun _ => Set.univ) F 0 b = 1 := fun b => by
    refine le_antisymm (iSup₂_le fun x _ => ?_) ?_
    · rw [htot]; exact_mod_cast hF1 (x 0) (x 1)
    · have hx : (fun t : ℕ => if t = 0 then b else true) ∈ Feasible (fun _ => Set.univ) b :=
        ⟨by simp, fun _ => trivial⟩
      have := le_biSup (total F 0) hx
      rw [htot] at this
      refine le_trans ?_ this
      simp [F]
  refine ⟨h42, ⟨by simp [xs], fun _ => trivial⟩, ?_, ?_⟩
  · rw [htot, hv]; simp [F, xs]
  · rw [hv]; simp [F, xs]

/-- **Theorem 4.5.** A feasible plan satisfying (9) and (11) `limsup βᵗv*(x*_t) ≤ 0` attains the
supremum. -/
theorem theorem_4_5 (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {x₀ : X} {xs : ℕ → X}
    (hxs : xs ∈ Feasible Γ x₀)
    (h9 : ∀ t, vstar Γ F β (xs t) =
      (F (xs t) (xs (t + 1)) : EReal) + (β : EReal) * vstar Γ F β (xs (t + 1)))
    (h11 : limsup (fun t => ((β ^ t : ℝ) : EReal) * vstar Γ F β (xs t)) atTop ≤ 0) :
    total F β xs = vstar Γ F β x₀ := by
  refine le_antisymm (le_biSup (total F β) hxs) ?_
  have key : ∀ n, vstar Γ F β x₀ = (partialSum F β xs n : EReal) +
      ((β ^ (n + 1) : ℝ) : EReal) * vstar Γ F β (xs (n + 1)) := by
    intro n
    induction n with
    | zero =>
      simp only [partialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        pow_one]
      rw [← hxs.1]
      exact h9 0
    | succ n ih =>
      rw [ih, h9 (n + 1), coe_mul_add _ _ (pow_nonneg hβ _), partialSum_succ', EReal.coe_add,
        add_assoc, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul, ← pow_succ]
      simp only [add_assoc]
  rw [← limsup_nat_add (fun t => ((β ^ t : ℝ) : EReal) * vstar Γ F β (xs t)) 1] at h11
  exact le_of_le_add_limsup (fun n => (key n).le) (tendsto_total h42 hxs) h11

/-- The optimal policy correspondence `G*(x) = {y ∈ Γ(x) : v*(x) = F(x, y) + βv*(y)}`. -/
def Gstar (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (x : X) : Set X :=
  {y | y ∈ Γ x ∧ vstar Γ F β x = (F x y : EReal) + (β : EReal) * vstar Γ F β y}

/-- Every optimal plan is generated by `G*` (from Theorem 4.4). -/
theorem optimal_generated_by_Gstar (hβ : 0 < β) (h42 : Assumption42 Γ F β) {x₀ : X}
    {xs : ℕ → X} (hxs : xs ∈ Feasible Γ x₀) (hopt : total F β xs = vstar Γ F β x₀) (t : ℕ) :
    xs (t + 1) ∈ Gstar Γ F β (xs t) :=
  ⟨hxs.2 t, theorem_4_4 hβ h42 hxs hopt t⟩

/-- A plan generated by `G*` and satisfying (11) is optimal (from Theorem 4.5). -/
theorem generated_by_Gstar_optimal (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {x₀ : X}
    {xs : ℕ → X} (h0 : xs 0 = x₀) (hgen : ∀ t, xs (t + 1) ∈ Gstar Γ F β (xs t))
    (h11 : limsup (fun t => ((β ^ t : ℝ) : EReal) * vstar Γ F β (xs t)) atTop ≤ 0) :
    total F β xs = vstar Γ F β x₀ :=
  theorem_4_5 hβ h42 ⟨h0, fun t => (hgen t).1⟩ (fun t => (hgen t).2) h11

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# When the sequence problem is well defined

SLP §4.1, pp. 67–69: sufficient conditions for Assumption 4.2, and Exercises 4.1–4.2.

* `tendsto_of_summable_pos`, `tendsto_of_summable_neg`: partial sums converge in `R̄` when the
  positive (or the negative) parts are summable.
* `assumption42_of_summable_pos`, `assumption42_of_summable_neg` (p. 69): Assumption 4.2 holds if
  `lim Σ βᵗF⁺ < ∞` or `lim Σ βᵗF⁻ < ∞` along every feasible plan.
* `assumption42_of_bddAbove`, `assumption42_of_bddBelow`: `F` bounded above or below and
  `0 ≤ β < 1`.
* `assumption42_of_geometric`: `F(x_t, x_{t+1}) ≤ cθᵗ` with `θ < 1/β`.
* `ex_4_2a`, `ex_4_2b`: two sets of conditions on `F` and `Γ` over `ℝˡ₊`.
* `ex_4_1a`, `ex_4_1b`: the one-sector and many-sector growth models as sequence problems.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Filter Topology Finset

/-- Partial sums of a real sequence converge in `R̄` if the positive parts are summable. -/
theorem tendsto_of_summable_pos (a : ℕ → ℝ) (h : Summable fun t => max (a t) 0) :
    ∃ L : EReal, Tendsto (fun n => ((∑ t ∈ range (n + 1), a t : ℝ) : EReal)) atTop (𝓝 L) := by
  set P : ℕ → ℝ := fun n => ∑ t ∈ range (n + 1), max (a t) 0
  set N : ℕ → ℝ := fun n => ∑ t ∈ range (n + 1), max (-a t) 0
  have hP : Tendsto P atTop (𝓝 (∑' t, max (a t) 0)) :=
    h.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hNmono : Monotone fun n => ((N n : ℝ) : EReal) := fun m n hmn => by
    refine EReal.coe_le_coe_iff.2 (sum_le_sum_of_subset_of_nonneg
      (range_subset_range.2 (by omega)) fun _ _ _ => le_max_right _ _)
  have hN := tendsto_atTop_iSup hNmono
  have hsplit : ∀ n, ((∑ t ∈ range (n + 1), a t : ℝ) : EReal) =
      ((P n : ℝ) : EReal) + -((N n : ℝ) : EReal) := fun n => by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    simp only [P, N, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rcases le_total (a t) 0 with h0 | h0
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
  refine ⟨((∑' t, max (a t) 0 : ℝ) : EReal) + -(⨆ n, ((N n : ℝ) : EReal)), ?_⟩
  simp only [hsplit]
  refine Tendsto.comp (f := fun n => (((P n : ℝ) : EReal), -((N n : ℝ) : EReal)))
    (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))
    ((EReal.tendsto_coe.2 hP).prodMk_nhds (continuous_neg.tendsto _ |>.comp hN))

/-- Partial sums of a real sequence converge in `R̄` if the negative parts are summable. -/
theorem tendsto_of_summable_neg (a : ℕ → ℝ) (h : Summable fun t => max (-a t) 0) :
    ∃ L : EReal, Tendsto (fun n => ((∑ t ∈ range (n + 1), a t : ℝ) : EReal)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := tendsto_of_summable_pos (fun t => -a t) h
  refine ⟨-L, ?_⟩
  have := (continuous_neg.tendsto L).comp hL
  refine this.congr fun n => ?_
  simp [sum_neg_distrib]

variable {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

/-- **p. 69.** Assumption 4.2 holds if `Σ βᵗF⁺(x_t, x_{t+1}) < ∞` along every feasible plan. -/
theorem assumption42_of_summable_pos
    (h : ∀ x₀, ∀ x ∈ Feasible Γ x₀, Summable fun t => max (β ^ t * F (x t) (x (t + 1))) 0) :
    Assumption42 Γ F β := fun x₀ x hx => tendsto_of_summable_pos _ (h x₀ x hx)

/-- **p. 69.** Assumption 4.2 holds if `Σ βᵗF⁻(x_t, x_{t+1}) < ∞` along every feasible plan. -/
theorem assumption42_of_summable_neg
    (h : ∀ x₀, ∀ x ∈ Feasible Γ x₀, Summable fun t => max (-(β ^ t * F (x t) (x (t + 1)))) 0) :
    Assumption42 Γ F β := fun x₀ x hx => tendsto_of_summable_neg _ (h x₀ x hx)

/-- Positive multiples of a geometric bound are summable. -/
theorem summable_max_of_le_geometric {b : ℕ → ℝ} {c r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hc : 0 ≤ c) (hb : ∀ t, b t ≤ c * r ^ t) : Summable fun t => max (b t) 0 :=
  Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
    (fun t => max_le (hb t) (mul_nonneg hc (pow_nonneg hr0 t)))
    ((summable_geometric_of_lt_one hr0 hr).mul_left c)

/-- **p. 69.** `F` bounded above and `0 ≤ β < 1`. -/
theorem assumption42_of_bddAbove {M : ℝ} (hF : ∀ x y, F x y ≤ M) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Assumption42 Γ F β :=
  assumption42_of_summable_pos fun _ x _ =>
    summable_max_of_le_geometric hβ0 hβ1 (le_max_right M 0) fun t => by
      rw [mul_comm (max M 0)]
      exact mul_le_mul_of_nonneg_left ((hF _ _).trans (le_max_left _ _)) (pow_nonneg hβ0 t)

/-- **p. 69.** `F` bounded below and `0 ≤ β < 1`. -/
theorem assumption42_of_bddBelow {M : ℝ} (hF : ∀ x y, M ≤ F x y) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Assumption42 Γ F β :=
  assumption42_of_summable_neg fun _ x _ =>
    summable_max_of_le_geometric hβ0 hβ1 (le_max_right (-M) 0) fun t => by
      have := mul_le_mul_of_nonneg_left
        ((neg_le_neg (hF (x t) (x (t + 1)))).trans (le_max_left (-M) 0)) (pow_nonneg hβ0 t)
      linarith

/-- **p. 69.** If along every feasible plan `F(x_t, x_{t+1}) ≤ cθᵗ` for some `0 < θ < 1/β` and
`c > 0`, Assumption 4.2 holds (`β > 0`). -/
theorem assumption42_of_geometric (hβ : 0 < β)
    (h : ∀ x₀, ∀ x ∈ Feasible Γ x₀, ∃ θ c : ℝ, 0 < θ ∧ θ < β⁻¹ ∧ 0 < c ∧
      ∀ t, F (x t) (x (t + 1)) ≤ c * θ ^ t) :
    Assumption42 Γ F β :=
  assumption42_of_summable_pos fun x₀ x hx => by
    obtain ⟨θ, c, hθ, hθβ, hc, hF⟩ := h x₀ x hx
    have hβθ : β * θ < 1 := by
      calc β * θ < β * β⁻¹ := mul_lt_mul_of_pos_left hθβ hβ
        _ = 1 := mul_inv_cancel₀ hβ.ne'
    refine summable_max_of_le_geometric (mul_nonneg hβ.le hθ.le) hβθ hc.le fun t => ?_
    rw [mul_pow, mul_comm c, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hF t).trans_eq (mul_comm _ _)) (pow_nonneg hβ.le t)

/-! ### Exercise 4.2: problems on `ℝˡ₊` -/

/-- The nonnegative orthant `ℝˡ₊`. -/
abbrev Orthant (l : ℕ) := {x : Fin l → ℝ // 0 ≤ x}

variable {l : ℕ}

/-- `θx + (1 − θ)x'` in `ℝˡ₊` for `θ ∈ [0, 1]`. -/
def orthCombo (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x x' : Orthant l) : Orthant l :=
  ⟨θ • x.1 + (1 - θ) • x'.1, add_nonneg (smul_nonneg hθ0 x.2) (smul_nonneg (by linarith) x'.2)⟩

/-- The origin of `ℝˡ₊`. -/
def orthZero (l : ℕ) : Orthant l := ⟨0, le_rfl⟩

/-- The vector `(1, …, 1)`. -/
def orthOne (l : ℕ) : Orthant l := ⟨1, zero_le_one⟩

/-- Along a plan with `‖x_{t+1}‖ ≤ θ‖x_t‖`, `‖x_t‖ ≤ θᵗ‖x₀‖`. -/
theorem norm_le_geometric {Γ : Orthant l → Set (Orthant l)} {θ : ℝ} (hθ : 0 ≤ θ)
    (hΓ : ∀ x, ∀ y ∈ Γ x, ‖y.1‖ ≤ θ * ‖x.1‖) {x₀ : Orthant l} {x : ℕ → Orthant l}
    (hx : x ∈ Feasible Γ x₀) (t : ℕ) : ‖(x t).1‖ ≤ θ ^ t * ‖x₀.1‖ := by
  induction t with
  | zero => simp [hx.1]
  | succ t ih =>
    calc ‖(x (t + 1)).1‖ ≤ θ * ‖(x t).1‖ := hΓ _ _ (hx.2 t)
      _ ≤ θ * (θ ^ t * ‖x₀.1‖) := mul_le_mul_of_nonneg_left ih hθ
      _ = θ ^ (t + 1) * ‖x₀.1‖ := by ring

/-- **Exercise 4.2a.** On `X = ℝˡ₊` with `0 < β < 1`, Assumption 4.2 holds if for some
`0 < θ < 1/β`, `y ∈ Γ(x)` implies `‖y‖ ≤ θ‖x‖`; `F(0, 0) = 0`; and `F` is increasing and concave
in its first `l` arguments and decreasing in its last `l`. (The norm is the sup norm.) -/
theorem ex_4_2a {Γ : Orthant l → Set (Orthant l)} {F : Orthant l → Orthant l → ℝ} {θ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθβ : θ < β⁻¹)
    (hΓ : ∀ x, ∀ y ∈ Γ x, ‖y.1‖ ≤ θ * ‖x.1‖) (hF0 : F (orthZero l) (orthZero l) = 0)
    (hinc : ∀ y, Monotone fun x => F x y) (hdec : ∀ x, Antitone (F x))
    (hconc : ∀ y x x' (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1),
      s * F x y + (1 - s) * F x' y ≤ F (orthCombo s hs0 hs1 x x') y) :
    Assumption42 Γ F β := by
  set C := max (F (orthOne l) (orthZero l)) 0
  -- `F(x, 0) ≤ C max{1, ‖x‖}`
  have hle_one : ∀ z : Orthant l, ‖z.1‖ ≤ 1 → z ≤ orthOne l := fun z hz i =>
    ((Real.le_norm_self _).trans (norm_le_pi_norm z.1 i)).trans hz
  have hbound : ∀ z : Orthant l, F z (orthZero l) ≤ C * (1 + ‖z.1‖) := fun z => by
    have hC : 0 ≤ C := le_max_right _ _
    rcases le_or_gt ‖z.1‖ 1 with hz | hz
    · calc F z (orthZero l) ≤ F (orthOne l) (orthZero l) := hinc _ (hle_one z hz)
        _ ≤ C := le_max_left _ _
        _ ≤ C * (1 + ‖z.1‖) := le_mul_of_one_le_right hC (by linarith [norm_nonneg z.1])
    · set s := ‖z.1‖⁻¹
      have hs0 : 0 < s := inv_pos.2 (by linarith)
      have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ hz.le
      have hcomb := hconc (orthZero l) z (orthZero l) s hs0.le hs1
      rw [hF0, mul_zero, add_zero] at hcomb
      have hsmall : orthCombo s hs0.le hs1 z (orthZero l) ≤ orthOne l := by
        refine hle_one _ ?_
        simp only [orthCombo, orthZero, smul_zero, add_zero, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs0, s]
        rw [inv_mul_cancel₀ (by linarith)]
      have h1 : s * F z (orthZero l) ≤ C :=
        hcomb.trans ((hinc _ hsmall).trans (le_max_left _ _))
      have hz' : 0 < ‖z.1‖ := by linarith
      have e : ‖z.1‖ * s = 1 := mul_inv_cancel₀ hz'.ne'
      have h2 : F z (orthZero l) ≤ C * ‖z.1‖ := by
        calc F z (orthZero l) = (‖z.1‖ * s) * F z (orthZero l) := by rw [e, one_mul]
          _ = ‖z.1‖ * (s * F z (orthZero l)) := by ring
          _ ≤ ‖z.1‖ * C := mul_le_mul_of_nonneg_left h1 hz'.le
          _ = C * ‖z.1‖ := mul_comm _ _
      nlinarith
  refine assumption42_of_summable_pos fun x₀ x hx => ?_
  have hβθ : β * θ < 1 := by
    calc β * θ < β * β⁻¹ := mul_lt_mul_of_pos_left hθβ hβ0
      _ = 1 := mul_inv_cancel₀ hβ0.ne'
  have hC : 0 ≤ C := le_max_right _ _
  refine Summable.of_nonneg_of_le (fun t => le_max_right _ _) (fun t => ?_)
    (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left C).add
      ((summable_geometric_of_lt_one (mul_nonneg hβ0.le hθ0.le) hβθ).mul_left (C * ‖x₀.1‖)))
  refine max_le ?_ (by positivity)
  have h1 : F (x t) (x (t + 1)) ≤ F (x t) (orthZero l) := hdec _ (x (t + 1)).2
  have h2 := (hbound (x t)).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (norm_le_geometric hθ0.le hΓ hx t)) hC)
  calc β ^ t * F (x t) (x (t + 1)) ≤ β ^ t * (C * (1 + θ ^ t * ‖x₀.1‖)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hβ0.le t)
    _ = C * β ^ t + C * ‖x₀.1‖ * (β * θ) ^ t := by rw [mul_pow]; ring

/-- **Exercise 4.2b.** On `X = ℝˡ₊` with `0 < β < 1`, Assumption 4.2 holds if for some
`0 < θ < 1/β`, `y ∈ Γ(x)` implies `F(y, 0) ≤ θF(x, 0)`, and `F` is decreasing in its last `l`
arguments. (The book also assumes `F` increasing in its first `l` arguments and `0 ∈ Γ(x)`;
neither is needed.) -/
theorem ex_4_2b {Γ : Orthant l → Set (Orthant l)} {F : Orthant l → Orthant l → ℝ} {θ : ℝ}
    (hβ0 : 0 < β) (hθ0 : 0 < θ) (hθβ : θ < β⁻¹)
    (hΓ : ∀ x, ∀ y ∈ Γ x, F y (orthZero l) ≤ θ * F x (orthZero l))
    (hdec : ∀ x, Antitone (F x)) :
    Assumption42 Γ F β := by
  refine assumption42_of_geometric hβ0 fun x₀ x hx =>
    ⟨θ, |F x₀ (orthZero l)| + 1, hθ0, hθβ, by positivity, fun t => ?_⟩
  have hgeo : ∀ t, F (x t) (orthZero l) ≤ θ ^ t * F x₀ (orthZero l) := by
    intro t
    induction t with
    | zero => simp [hx.1]
    | succ t ih =>
      calc F (x (t + 1)) (orthZero l) ≤ θ * F (x t) (orthZero l) := hΓ _ _ (hx.2 t)
        _ ≤ θ * (θ ^ t * F x₀ (orthZero l)) := mul_le_mul_of_nonneg_left ih hθ0.le
        _ = θ ^ (t + 1) * F x₀ (orthZero l) := by ring
  calc F (x t) (x (t + 1)) ≤ F (x t) (orthZero l) := hdec _ (x (t + 1)).2
    _ ≤ θ ^ t * F x₀ (orthZero l) := hgeo t
    _ ≤ θ ^ t * (|F x₀ (orthZero l)| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [le_abs_self (F x₀ (orthZero l))])
          (pow_nonneg hθ0.le t)
    _ = (|F x₀ (orthZero l)| + 1) * θ ^ t := mul_comm _ _

/-! ### Exercise 4.1: growth models as sequence problems -/

/-- **Exercise 4.1a.** The one-sector growth model `max Σ βᵗU(f(k_t) − k_{t+1})`,
`0 ≤ k_{t+1} ≤ f(k_t)`, is the sequence problem with `Γ(k) = [0, f(k)]` and
`F(k, y) = U(f(k) − y)`: the plans are those of `Π(k₀)` and the objectives agree. -/
theorem ex_4_1a (U f : ℝ → ℝ) (k₀ : ℝ) (k : ℕ → ℝ) (n : ℕ) :
    (k ∈ Feasible (fun k => Set.Icc 0 (f k)) k₀ ↔
      k 0 = k₀ ∧ ∀ t, 0 ≤ k (t + 1) ∧ k (t + 1) ≤ f (k t)) ∧
    partialSum (fun k y => U (f k - y)) β k n =
      ∑ t ∈ range (n + 1), β ^ t * U (f (k t) - k (t + 1)) :=
  ⟨Iff.rfl, rfl⟩

/-- The many-sector technology: the consumption vectors `c ≥ 0` with `(k' + c, k) ∈ Y`. -/
def consSet {l : ℕ} (Y : Set ((Fin l → ℝ) × (Fin l → ℝ))) (k k' : Fin l → ℝ) :
    Set (Fin l → ℝ) :=
  {c | 0 ≤ c ∧ (k' + c, k) ∈ Y}

/-- **Exercise 4.1b.** The many-sector growth model `max Σ βᵗU(c_t)` subject to
`(k_{t+1} + c_t, k_t) ∈ Y`, `c_t ≥ 0`, is the sequence problem with
`Γ(k) = {k' : some c ≥ 0 has (k' + c, k) ∈ Y}` and `F(k, k') = max{U(c) : c ≥ 0, (k' + c, k) ∈ Y}`
(the maximum assumed attained): every plan `(c, k)` is dominated period by period by `F` along
`k`, and every `k ∈ Π(k₀)` is attained by some consumption plan. -/
theorem ex_4_1b {l : ℕ} (Y : Set ((Fin l → ℝ) × (Fin l → ℝ))) (U : (Fin l → ℝ) → ℝ)
    (F : (Fin l → ℝ) → (Fin l → ℝ) → ℝ) (hβ : 0 ≤ β)
    (hF : ∀ k k', ∀ c ∈ consSet Y k k', U c ≤ F k k')
    (hatt : ∀ k k', (consSet Y k k').Nonempty → ∃ c ∈ consSet Y k k', U c = F k k')
    (k₀ : Fin l → ℝ) :
    (∀ (c k : ℕ → (Fin l → ℝ)), k 0 = k₀ → (∀ t, c t ∈ consSet Y (k t) (k (t + 1))) →
      k ∈ Feasible (fun k => {k' | (consSet Y k k').Nonempty}) k₀ ∧
      ∀ n, ∑ t ∈ range (n + 1), β ^ t * U (c t) ≤ partialSum F β k n) ∧
    (∀ k ∈ Feasible (fun k => {k' | (consSet Y k k').Nonempty}) k₀, ∃ c : ℕ → (Fin l → ℝ),
      (∀ t, c t ∈ consSet Y (k t) (k (t + 1))) ∧
      ∀ n, ∑ t ∈ range (n + 1), β ^ t * U (c t) = partialSum F β k n) := by
  refine ⟨fun c k hk0 hc => ⟨⟨hk0, fun t => ⟨c t, hc t⟩⟩, fun n => ?_⟩, fun k hk => ?_⟩
  · exact sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hF _ _ _ (hc t)) (pow_nonneg hβ t)
  · choose c hc hU using fun t => hatt (k t) (k (t + 1)) (hk.2 t)
    exact ⟨c, hc, fun n => sum_congr rfl fun t _ => by rw [hU t]⟩

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Contraction Mapping Theorem

SLP §3.2, pp. 49–53, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`) so that this project is self-contained. Chapter 4 uses Theorem 3.2
and Corollary 1.

* `IsContraction` (p. 50): `ρ(Tx, Ty) ≤ βρ(x, y)` with `β ∈ (0, 1)`.
* `IsContraction.uniformContinuous` (Ex 3.8).
* `dist_iterate_succ_le`, `dist_iterate_le` ((1)–(2), p. 51), `cauchySeq_iterate`.
* `theorem_3_2` (**Contraction Mapping Theorem**): in a complete metric space a contraction has
  exactly one fixed point `v`, and `ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)`; the proof follows the book.
* `dist_fixedPoint_le` (Ex 3.9): `ρ(Tⁿv₀, v) ≤ ρ(Tⁿv₀, Tⁿ⁺¹v₀)/(1 − β)`.
* `corollary_1`: the fixed point lies in every nonempty closed set `T` maps into itself, and in
  every `S''` with `T(S') ⊆ S'' ⊆ S'`.
* `corollary_2` (**N-stage Contraction Theorem**).
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {S : Type*} [MetricSpace S]

/-- `T` is a contraction with modulus `β ∈ (0, 1)` (SLP p. 50). -/
def IsContraction (T : S → S) (β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧ ∀ x y, dist (T x) (T y) ≤ β * dist x y

variable {T : S → S} {β : ℝ}

/-- **Ex 3.8.** A contraction is uniformly continuous. -/
theorem IsContraction.uniformContinuous (hT : IsContraction T β) : UniformContinuous T :=
  Metric.uniformContinuous_iff.2 fun ε hε => ⟨ε, hε, fun {x y} h =>
    lt_of_le_of_lt (hT.2.2 x y) (by
      calc β * dist x y ≤ 1 * dist x y := mul_le_mul_of_nonneg_right hT.2.1.le dist_nonneg
        _ < ε := by rw [one_mul]; exact h)⟩

/-- (1), p. 51: `ρ(v_{n+1}, v_n) ≤ βⁿ ρ(v₁, v₀)`. -/
theorem dist_iterate_succ_le (hT : IsContraction T β) (v₀ : S) (n : ℕ) :
    dist (T^[n + 1] v₀) (T^[n] v₀) ≤ β ^ n * dist (T v₀) v₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    calc dist (T^[n + 1 + 1] v₀) (T^[n + 1] v₀) = dist (T (T^[n + 1] v₀)) (T (T^[n] v₀)) := by
          rw [Function.iterate_succ_apply' T (n + 1), Function.iterate_succ_apply' T n]
      _ ≤ β * dist (T^[n + 1] v₀) (T^[n] v₀) := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist (T v₀) v₀) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist (T v₀) v₀ := by ring

/-- (2), p. 51: `ρ(v_m, v_n) ≤ βⁿ/(1 − β) ρ(v₁, v₀)` for `m ≥ n`. -/
theorem dist_iterate_le (hT : IsContraction T β) (v₀ : S) {m n : ℕ} (hmn : n ≤ m) :
    dist (T^[m] v₀) (T^[n] v₀) ≤ β ^ n / (1 - β) * dist (T v₀) v₀ := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  -- the telescoped bound `∑_{k=n}^{m−1} βᵏ ρ(v₁, v₀) = βⁿ(1 − β^{m−n})/(1 − β) ρ(v₁, v₀)`
  have key : ∀ j, dist (T^[n + j] v₀) (T^[n] v₀) ≤
      β ^ n * (1 - β ^ j) / (1 - β) * dist (T v₀) v₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := dist_iterate_succ_le hT v₀ (n + j)
      have htri := dist_triangle (T^[n + (j + 1)] v₀) (T^[n + j] v₀) (T^[n] v₀)
      rw [← add_assoc] at htri ⊢
      have e : β ^ n * (1 - β ^ (j + 1)) / (1 - β) =
          β ^ n * (1 - β ^ j) / (1 - β) + β ^ (n + j) := by
        field_simp
        ring
      rw [e, add_mul]
      linarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine (key j).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  have := pow_nonneg hT.1.le j
  rw [div_le_div_iff_of_pos_right h1β]
  nlinarith [pow_nonneg hT.1.le n]

/-- The successive approximations `vₙ = Tⁿv₀` form a Cauchy sequence. -/
theorem cauchySeq_iterate (hT : IsContraction T β) (v₀ : S) : CauchySeq fun n => T^[n] v₀ := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hlim : Tendsto (fun n => β ^ n / (1 - β) * dist (T v₀) v₀) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hT.1.le hT.2.1).div_const (1 - β)).mul_const
      (dist (T v₀) v₀)
    simpa using this
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  exact ⟨N, fun n hn => (dist_iterate_le hT v₀ hn).trans_lt (hN N le_rfl)⟩

/-- **Theorem 3.2 (Contraction Mapping Theorem).** If `(S, ρ)` is complete and `T` is a contraction
with modulus `β`, then (a) `T` has exactly one fixed point `v`, and (b) `ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)`
for every `v₀`. The space must be nonempty. -/
theorem theorem_3_2 [CompleteSpace S] [Nonempty S] (hT : IsContraction T β) :
    ∃ v, T v = v ∧ (∀ w, T w = w → w = v) ∧
      ∀ v₀ (n : ℕ), dist (T^[n] v₀) v ≤ β ^ n * dist v₀ v := by
  -- existence: the limit of the successive approximations from any `v₀`
  obtain ⟨v₀⟩ : Nonempty S := inferInstance
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (cauchySeq_iterate hT v₀)
  have hfix : T v = v := by
    have h1 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 (T v)) :=
      (hT.uniformContinuous.continuous.tendsto v).comp hv
    have h2 : Tendsto (fun n => T (T^[n] v₀)) atTop (𝓝 v) := by
      have := hv.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Function.iterate_succ_apply'] using this
    exact tendsto_nhds_unique h1 h2
  -- uniqueness
  have huniq : ∀ w, T w = w → w = v := fun w hw => by
    by_contra hne
    have hpos : 0 < dist w v := dist_pos.2 hne
    have := hT.2.2 w v
    rw [hw, hfix] at this
    nlinarith [hT.2.1]
  -- the rate
  refine ⟨v, hfix, huniq, fun v₁ n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    calc dist (T (T^[n] v₁)) v = dist (T (T^[n] v₁)) (T v) := by rw [hfix]
      _ ≤ β * dist (T^[n] v₁) v := hT.2.2 _ _
      _ ≤ β * (β ^ n * dist v₁ v) := mul_le_mul_of_nonneg_left ih hT.1.le
      _ = β * β ^ n * dist v₁ v := by ring

/-- **Ex 3.9.** If `v` is the fixed point, `ρ(Tⁿv₀, v) ≤ ρ(Tⁿv₀, Tⁿ⁺¹v₀)/(1 − β)`. -/
theorem dist_fixedPoint_le (hT : IsContraction T β) {v : S} (hv : T v = v) (v₀ : S) (n : ℕ) :
    dist (T^[n] v₀) v ≤ dist (T^[n] v₀) (T^[n + 1] v₀) / (1 - β) := by
  have h1β : 0 < 1 - β := sub_pos.2 hT.2.1
  rw [le_div_iff₀ h1β]
  have h1 := dist_triangle (T^[n] v₀) (T^[n + 1] v₀) v
  have h2 : dist (T^[n + 1] v₀) v ≤ β * dist (T^[n] v₀) v := by
    rw [Function.iterate_succ_apply']
    conv_lhs => rw [← hv]
    exact hT.2.2 _ _
  nlinarith

/-- **Corollary 1.** The fixed point lies in every nonempty closed set `S'` with `T(S') ⊆ S'`,
and in every `S''` with `T(S') ⊆ S'' ⊆ S'`. (The book does not ask `S'` to be nonempty; for
`S' = ∅` the claim fails.) -/
theorem corollary_1 (hT : IsContraction T β) {v : S} (hv : T v = v) {S' S'' : Set S}
    (hne : S'.Nonempty) (hclosed : IsClosed S') (hmaps : Set.MapsTo T S' S')
    (hS'' : Set.MapsTo T S' S'') : v ∈ S' ∧ v ∈ S'' := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hmem : ∀ n, T^[n] v₀ ∈ S' := fun n => hmaps.iterate n hv₀
  -- the iterates converge to the fixed point
  have hlim : Tendsto (fun n => T^[n] v₀) atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hrate : ∀ n, dist (T^[n] v₀) v ≤ β ^ n * dist v₀ v := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ']
        calc dist (T (T^[n] v₀)) v = dist (T (T^[n] v₀)) (T v) := by rw [hv]
          _ ≤ β * dist (T^[n] v₀) v := hT.2.2 _ _
          _ ≤ β * (β ^ n * dist v₀ v) := mul_le_mul_of_nonneg_left ih hT.1.le
          _ = β * β ^ n * dist v₀ v := by ring
    refine squeeze_zero (fun _ => dist_nonneg) hrate ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hT.1.le hT.2.1).mul_const (dist v₀ v)
  have hvS' : v ∈ S' := hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  refine ⟨hvS', ?_⟩
  rw [← hv]
  exact hS'' hvS'

/-- **Corollary 2 (N-stage Contraction Theorem).** If `S` is complete and `T^N` is a contraction
with modulus `β`, then `T` has exactly one fixed point `v`, and `ρ(T^{kN}v₀, v) ≤ βᵏρ(v₀, v)`. -/
theorem corollary_2 [CompleteSpace S] [Nonempty S] {N : ℕ} (hT : IsContraction T^[N] β) :
    ∃ v, T v = v ∧ (∀ w, T w = w → w = v) ∧
      ∀ v₀ (k : ℕ), dist (T^[k * N] v₀) v ≤ β ^ k * dist v₀ v := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 hT
  -- the fixed point of `T^N` is a fixed point of `T`
  have hTv : T v = v := by
    have h := hT.2.2 (T v) v
    have hc : T^[N] (T v) = T v := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hv]
    rw [hc, hv] at h
    by_contra hne
    have hpos : 0 < dist (T v) v := dist_pos.2 hne
    nlinarith [hT.2.1]
  refine ⟨v, hTv, fun w hw => huniq w (Function.iterate_fixed hw N), fun v₀ k => ?_⟩
  rw [mul_comm k N, Function.iterate_mul]
  exact hrate v₀ k

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Correspondences

SLP §3.3, pp. 56–61, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`): lower and upper hemi-continuity on metric spaces (`IsLHC`, `IsUHC`),
the graph, Exercise 3.11a (`continuousAt_of_isUHC_singleton`) and Exercise 3.15
(`isCompact_graph`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `Γ` is **lower hemi-continuous** at `x` (SLP p. 56). -/
def IsLHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ y ∈ Γ x, ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) →
    ∃ N, ∃ ys : ℕ → Y, (∀ n ≥ N, ys n ∈ Γ (xs n)) ∧ Tendsto ys atTop (𝓝 y)

/-- `Γ` is **upper hemi-continuous** at `x` (SLP p. 56; the book applies it to compact-valued
correspondences). -/
def IsUHC (Γ : X → Set Y) (x : X) : Prop :=
  (Γ x).Nonempty ∧ ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) → ∀ ys : ℕ → Y, (∀ n, ys n ∈ Γ (xs n)) →
    ∃ y ∈ Γ x, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (ys ∘ φ) atTop (𝓝 y)

/-- The graph `A = {(x, y) : y ∈ Γ(x)}`. -/
def graph (Γ : X → Set Y) : Set (X × Y) := {p | p.2 ∈ Γ p.1}

/-- **Ex 3.11a.** A single-valued u.h.c. correspondence is continuous. -/
theorem continuousAt_of_isUHC_singleton {f : X → Y} {x : X} (h : IsUHC (fun x => {f x}) x) :
    ContinuousAt f x := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, hy, φ, -, hφ⟩ := h.2 (xs ∘ ns) (hxs.comp hns) (fun n => f (xs (ns n))) fun n => rfl
  rw [mem_singleton_iff] at hy
  exact ⟨φ, by rw [← hy]; exact hφ⟩

/-- **Ex 3.15.** A compact-valued u.h.c. correspondence on a compact space has a compact graph. -/
theorem isCompact_graph [CompactSpace X] {Γ : X → Set Y} (h : ∀ x, IsUHC Γ x) :
    IsCompact (graph Γ) := by
  refine IsSeqCompact.isCompact fun ps hps => ?_
  obtain ⟨x, -, ν, hν, hlim⟩ := isCompact_univ.tendsto_subseq (x := fun n => (ps n).1)
    fun _ => mem_univ _
  obtain ⟨y, hy, μ, hμ, hlim'⟩ := (h x).2 _ hlim (fun n => (ps (ν n)).2) fun n => hps (ν n)
  refine ⟨(x, y), hy, ν ∘ μ, hν.comp hμ, ?_⟩
  exact (Prod.tendsto_iff _ _).2 ⟨hlim.comp hμ.tendsto_atTop, hlim'⟩

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Theorem of the Maximum

SLP §3.3, pp. 56–65, carried over from the Chapter 3 project (`RecursiveMethods/
MathematicalPreliminaries`).

For `f : X × Y → ℝ` and a correspondence `Γ`, `h(x) = max_{y ∈ Γ(x)} f(x, y)` (`maxValue`) and
`G(x) = {y ∈ Γ(x) : f(x, y) = h(x)}` (`argmax`).

* `theorem_3_6` (**Theorem of the Maximum**).
* `UniqueArgmax`, `argmaxFn`, `continuous_argmaxFn`, `lemma_3_7`, `theorem_3_8`: Lemma 3.7 and
  Theorem 3.8 for objectives with a unique maximizer. Chapter 3 proves them with `Γ`
  convex-valued in a normed space and `f(x, ·)` strictly concave; the proofs use only uniqueness
  of the maximizer, and Chapter 4 needs them on a convex subset of a normed space.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `h(x) = max_{y ∈ Γ(x)} f(x, y)`. -/
noncomputable def maxValue (f : X × Y → ℝ) (Γ : X → Set Y) (x : X) : ℝ :=
  sSup ((fun y => f (x, y)) '' Γ x)

/-- `G(x) = {y ∈ Γ(x) : f(x, y) = h(x)}`. -/
def argmax (f : X × Y → ℝ) (Γ : X → Set Y) (x : X) : Set Y :=
  {y | y ∈ Γ x ∧ f (x, y) = maxValue f Γ x}

variable {f : X × Y → ℝ} {Γ : X → Set Y}

theorem continuousOn_section (hf : ContinuousOn f (graph Γ)) (x : X) :
    ContinuousOn (fun y => f (x, y)) (Γ x) :=
  hf.comp (Continuous.prodMk_right x).continuousOn fun _ hy => hy

/-- On a compact nonempty `Γ(x)` the maximum is attained. -/
theorem exists_argmax (hf : ContinuousOn f (graph Γ)) {x : X} (hc : IsCompact (Γ x))
    (hne : (Γ x).Nonempty) :
    ∃ y ∈ Γ x, f (x, y) = maxValue f Γ x ∧ ∀ z ∈ Γ x, f (x, z) ≤ f (x, y) := by
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn hne (continuousOn_section hf x)
  have hgr : IsGreatest ((fun y => f (x, y)) '' Γ x) (f (x, y)) :=
    ⟨⟨y, hy, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hmax hz⟩
  exact ⟨y, hy, hgr.csSup_eq.symm, fun z hz => hmax hz⟩

theorem le_maxValue (hf : ContinuousOn f (graph Γ)) {x : X} (hc : IsCompact (Γ x)) {z : Y}
    (hz : z ∈ Γ x) : f (x, z) ≤ maxValue f Γ x :=
  le_csSup ((hc.image_of_continuousOn (continuousOn_section hf x)).bddAbove) ⟨z, hz, rfl⟩

/-- Along a sequence in the graph converging to a graph point, `f` converges. -/
theorem tendsto_f_graph (hf : ContinuousOn f (graph Γ)) {xs : ℕ → X} {ys : ℕ → Y} {x : X} {y : Y}
    (hy : y ∈ Γ x) (hxs : Tendsto xs atTop (𝓝 x)) (hys : Tendsto ys atTop (𝓝 y)) {N : ℕ}
    (hmem : ∀ n ≥ N, ys n ∈ Γ (xs n)) :
    Tendsto (fun n => f (xs n, ys n)) atTop (𝓝 (f (x, y))) := by
  have hp : Tendsto (fun n => (xs n, ys n)) atTop (𝓝[graph Γ] (x, y)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Prod.tendsto_iff _ _).2 ⟨hxs, hys⟩,
      eventually_atTop.2 ⟨N, fun n hn => hmem n hn⟩⟩
  exact (hf (x, y) hy).tendsto.comp hp

/-- **Theorem 3.6 (Theorem of the Maximum).** If `f` is continuous on the graph and `Γ` is
compact-valued and continuous (l.h.c. and u.h.c.), then `h` is continuous and `G` is nonempty,
compact-valued and u.h.c. -/
theorem theorem_3_6 (hf : ContinuousOn f (graph Γ)) (hc : ∀ x, IsCompact (Γ x))
    (hl : ∀ x, IsLHC Γ x) (hu : ∀ x, IsUHC Γ x) :
    Continuous (maxValue f Γ) ∧
      ∀ x, (argmax f Γ x).Nonempty ∧ IsCompact (argmax f Γ x) ∧ IsUHC (argmax f Γ) x := by
  -- G is nonempty and compact
  have hGne : ∀ x, (argmax f Γ x).Nonempty := fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_argmax hf (hc x) (hu x).1
    exact ⟨y, hy, hval⟩
  have hGc : ∀ x, IsCompact (argmax f Γ x) := fun x => by
    have hcl : IsClosed (Γ x ∩ (fun y => f (x, y)) ⁻¹' {maxValue f Γ x}) :=
      (continuousOn_section hf x).preimage_isClosed_of_isClosed (hc x).isClosed isClosed_singleton
    exact (hc x).of_isClosed_subset hcl (fun y hy => hy.1)
  -- G is u.h.c.
  have hGu : ∀ x, IsUHC (argmax f Γ) x := fun x => by
    refine ⟨hGne x, fun xs hxs ys hys => ?_⟩
    obtain ⟨y, hy, ν, hν, hlim⟩ := (hu x).2 xs hxs ys fun n => (hys n).1
    refine ⟨y, ⟨hy, ?_⟩, ν, hν, hlim⟩
    refine le_antisymm (le_maxValue hf (hc x) hy) ?_
    obtain ⟨z, hz, hzval, -⟩ := exists_argmax hf (hc x) (hu x).1
    rw [← hzval]
    -- compare with a sequence converging to the maximizer `z`
    have hxν : Tendsto (xs ∘ ν) atTop (𝓝 x) := hxs.comp hν.tendsto_atTop
    obtain ⟨N, zs, hzs, hzlim⟩ := (hl x).2 z hz (xs ∘ ν) hxν
    have h1 := tendsto_f_graph hf hy hxν hlim (N := 0) fun n _ => (hys (ν n)).1
    have h2 := tendsto_f_graph hf hz hxν hzlim hzs
    refine le_of_tendsto_of_tendsto h2 h1 (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hyn := hys (ν n)
    simp only [Function.comp_apply]
    rw [hyn.2]
    exact le_maxValue hf (hc _) (hzs n hn)
  refine ⟨continuous_iff_continuousAt.2 fun x => ?_, fun x => ⟨hGne x, hGc x, hGu x⟩⟩
  -- h is continuous: every subsequence has a further subsequence along which `h → h(x)`
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro xs hxs
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  choose ys hys using fun n => hGne (xs (ns n))
  obtain ⟨y, hy, φ, hφ, hlim⟩ := (hGu x).2 (xs ∘ ns) (hxs.comp hns) ys hys
  refine ⟨φ, ?_⟩
  have h1 := tendsto_f_graph hf hy.1 ((hxs.comp hns).comp hφ.tendsto_atTop) hlim (N := 0)
    fun n _ => (hys (φ n)).1
  rw [hy.2] at h1
  refine h1.congr fun n => ?_
  simp only [Function.comp_apply]
  exact (hys (φ n)).2

/-! ### Unique maximizers: Lemma 3.7 and Theorem 3.8 -/

/-- The hypotheses of Lemma 3.7 with uniqueness of the maximizer in place of strict concavity. -/
structure UniqueArgmax (Γ : X → Set Y) (f : X × Y → ℝ) : Prop where
  nonempty : ∀ x, (Γ x).Nonempty
  compact : ∀ x, IsCompact (Γ x)
  lhc : ∀ x, IsLHC Γ x
  uhc : ∀ x, IsUHC Γ x
  cont : ContinuousOn f (graph Γ)
  unique : ∀ x, ∀ y₁ ∈ argmax f Γ x, ∀ y₂ ∈ argmax f Γ x, y₁ = y₂

variable [Nonempty Y]

/-- The maximizer `g(x) = argmax_{y ∈ Γ(x)} f(x, y)`. -/
noncomputable def argmaxFn (Γ : X → Set Y) (f : X × Y → ℝ) (x : X) : Y :=
  Classical.epsilon fun y => y ∈ argmax f Γ x

namespace UniqueArgmax

variable (h : UniqueArgmax Γ f)
include h

theorem argmaxFn_mem (x : X) : argmaxFn Γ f x ∈ argmax f Γ x := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax h.cont (h.compact x) (h.nonempty x)
  exact Classical.epsilon_spec (p := fun y => y ∈ argmax f Γ x) ⟨y, hy, hval⟩

theorem argmax_eq (x : X) : argmax f Γ x = {argmaxFn Γ f x} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨h.argmaxFn_mem x, fun _ hy => h.unique x _ hy _
    (h.argmaxFn_mem x)⟩

/-- `f(x, y) < f(x, g(x))` for `y ≠ g(x)` in `Γ(x)`. -/
theorem lt_of_ne {x : X} {y : Y} (hy : y ∈ Γ x) (hne : y ≠ argmaxFn Γ f x) :
    f (x, y) < f (x, argmaxFn Γ f x) := by
  have hle : f (x, y) ≤ f (x, argmaxFn Γ f x) := by
    rw [(h.argmaxFn_mem x).2]
    exact le_maxValue h.cont (h.compact x) hy
  refine lt_of_le_of_ne hle fun heq => hne ?_
  have : y ∈ argmax f Γ x := ⟨hy, by rw [heq]; exact (h.argmaxFn_mem x).2⟩
  rw [h.argmax_eq x] at this
  exact this

/-- The maximizer is continuous (Theorem 3.6 with Ex 3.11a). -/
theorem continuous_argmaxFn : Continuous (argmaxFn Γ f) := by
  have h36 := theorem_3_6 h.cont h.compact h.lhc h.uhc
  refine continuous_iff_continuousAt.2 fun x => continuousAt_of_isUHC_singleton ?_
  have := (h36.2 x).2.2
  have heq : argmax f Γ = fun x => {argmaxFn Γ f x} := funext h.argmax_eq
  rwa [heq] at this

/-- **Lemma 3.7.** For each `ε > 0` and `x` there is `δ > 0` such that `y ∈ Γ(x)` and
`|f(x, g(x)) − f(x, y)| < δ` imply `ρ(g(x), y) < ε`. -/
theorem lemma_3_7 {ε : ℝ} (hε : 0 < ε) (x : X) :
    ∃ δ > 0, ∀ y ∈ Γ x, |f (x, argmaxFn Γ f x) - f (x, y)| < δ → dist (argmaxFn Γ f x) y < ε := by
  set g := argmaxFn Γ f x
  set K := Γ x ∩ {y | ε ≤ dist g y}
  have hK : IsCompact K := (h.compact x).inter_right
    (isClosed_le continuous_const (continuous_const.dist continuous_id))
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    by_contra hge
    have : y ∈ K := ⟨hy, not_lt.1 hge⟩
    rw [hK0] at this
    exact this
  have hcont : ContinuousOn (fun y => f (x, g) - f (x, y)) K :=
    continuousOn_const.sub ((continuousOn_section h.cont x).mono inter_subset_left)
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hKne hcont
  have hpos : 0 < f (x, g) - f (x, y₀) := by
    have hne : y₀ ≠ g := fun he => by
      have := hy₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, dist_self] at this
      linarith
    linarith [h.lt_of_ne hy₀.1 hne]
  refine ⟨f (x, g) - f (x, y₀), hpos, fun y hy hyδ => ?_⟩
  by_contra hge
  have hyK : y ∈ K := ⟨hy, not_lt.1 hge⟩
  have := isMinOn_iff.1 hmin y hyK
  have habs := le_abs_self (f (x, g) - f (x, y))
  linarith

/-- **Lemma 3.7 (compact `X`).** If `X` is compact, `δ` can be chosen independently of `x`. -/
theorem lemma_3_7_uniform [CompactSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, ∀ y ∈ Γ x,
      |f (x, argmaxFn Γ f x) - f (x, y)| < δ → dist (argmaxFn Γ f x) y < ε := by
  set g := argmaxFn Γ f
  have hg := h.continuous_argmaxFn
  set Aε := graph Γ ∩ {p : X × Y | ε ≤ dist (g p.1) p.2}
  have hA : IsCompact Aε := (isCompact_graph h.uhc).inter_right
    (isClosed_le continuous_const ((hg.comp continuous_fst).dist continuous_snd))
  rcases Aε.eq_empty_or_nonempty with hA0 | hAne
  · refine ⟨1, one_pos, fun x y hy _ => ?_⟩
    by_contra hge
    have : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
    rw [hA0] at this
    exact this
  have hcont : ContinuousOn (fun p : X × Y => f (p.1, g p.1) - f p) Aε := by
    refine ContinuousOn.sub ?_ (h.cont.mono inter_subset_left)
    exact h.cont.comp (continuous_fst.prodMk (hg.comp continuous_fst)).continuousOn
      fun p _ => (h.argmaxFn_mem p.1).1
  obtain ⟨p₀, hp₀, hmin⟩ := hA.exists_isMinOn hAne hcont
  have hpos : 0 < f (p₀.1, g p₀.1) - f p₀ := by
    have hne : p₀.2 ≠ g p₀.1 := fun he => by
      have := hp₀.2
      simp only [Set.mem_ofPred_eq] at this
      rw [he, dist_self] at this
      linarith
    have := h.lt_of_ne hp₀.1 hne
    linarith
  refine ⟨_, hpos, fun x y hy hyδ => ?_⟩
  by_contra hge
  have hyA : (x, y) ∈ Aε := ⟨hy, not_lt.1 hge⟩
  have := isMinOn_iff.1 hmin (x, y) hyA
  have habs := le_abs_self (f (x, g x) - f (x, y))
  linarith

end UniqueArgmax

/-- The shortfall bound behind Theorem 3.8: if `|f − fₙ| < δ/2` on the graph, then
`|f(x, g(x)) − f(x, gₙ(x))| < δ`. -/
theorem shortfall_lt {f fn : X × Y → ℝ} (hf : UniqueArgmax Γ f) (hfn : UniqueArgmax Γ fn)
    {δ : ℝ} (hclose : ∀ p ∈ graph Γ, |f p - fn p| < δ / 2) (x : X) :
    |f (x, argmaxFn Γ f x) - f (x, argmaxFn Γ fn x)| < δ := by
  set g := argmaxFn Γ f x
  set gn := argmaxFn Γ fn x
  have hg := hf.argmaxFn_mem x
  have hgn := hfn.argmaxFn_mem x
  have h1 : f (x, gn) ≤ f (x, g) := by rw [hg.2]; exact le_maxValue hf.cont (hf.compact x) hgn.1
  have h2 : fn (x, g) ≤ fn (x, gn) := by
    rw [hgn.2]; exact le_maxValue hfn.cont (hfn.compact x) hg.1
  have e1 := abs_lt.1 (hclose (x, g) hg.1)
  have e2 := abs_lt.1 (hclose (x, gn) hgn.1)
  rw [abs_of_nonneg (sub_nonneg.2 h1)]
  linarith [e1.1, e1.2, e2.1, e2.2]

/-- **Theorem 3.8.** If `fₙ → f` uniformly on the graph, each with a unique maximizer, then the
maximizers converge pointwise: `gₙ(x) → g(x)`. -/
theorem theorem_3_8 {fs : ℕ → X × Y → ℝ} (hf : UniqueArgmax Γ f)
    (hfs : ∀ n, UniqueArgmax Γ (fs n)) (hunif : TendstoUniformlyOn fs f atTop (graph Γ))
    (x : X) : Tendsto (fun n => argmaxFn Γ (fs n) x) atTop (𝓝 (argmaxFn Γ f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7 hε x
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine ⟨M, fun n hn => ?_⟩
  rw [dist_comm]
  refine hlem _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

/-- **Theorem 3.8 (compact `X`).** If `X` is compact the convergence is uniform. -/
theorem theorem_3_8_uniform [CompactSpace X] {fs : ℕ → X × Y → ℝ}
    (hf : UniqueArgmax Γ f) (hfs : ∀ n, UniqueArgmax Γ (fs n))
    (hunif : TendstoUniformlyOn fs f atTop (graph Γ)) :
    TendstoUniformly (fun n => argmaxFn Γ (fs n)) (argmaxFn Γ f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hlem⟩ := hf.lemma_3_7_uniform hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) (δ / 2)
    (half_pos hδ))
  refine eventually_atTop.2 ⟨M, fun n hn x => ?_⟩
  refine hlem x _ (hfs n |>.argmaxFn_mem x).1 (shortfall_lt hf (hfs n) (fun p hp => ?_) x)
  have := hM n hn p hp
  rwa [Real.dist_eq] at this

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded returns

SLP §4.2, pp. 77–80: the functional equation `v(x) = max_{y ∈ Γ(x)} [F(x, y) + βv(y)]` in the
space `C(X)` of bounded continuous functions with the sup norm (`X →ᵇ ℝ`).

* `Assumption43` (`Γ` nonempty, compact-valued and continuous) and `Assumption44` (`F` bounded
  and continuous on the graph, `0 < β < 1`). The state space is a metric space; the book's
  convexity of `X ⊆ ℝˡ` is not used until Theorem 4.8.
* `bellman` (`T`), `bellman_mono`, `bellman_add_const`, `blackwell`: `T` maps `C(X)` into itself,
  is monotone and discounts (Theorem 3.3).
* `theorem_4_6`: `T` has a unique fixed point `v ∈ C(X)`, `‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and the
  policy correspondence `G` is nonempty, compact-valued and u.h.c.
* `fixedPoint_eq_vstar`, `policy_plan_optimal` (p. 80): `v = v*`, and every plan generated by
  `G` is optimal.
* `theorem_4_7` (with Assumptions 4.5–4.6): `v` is strictly increasing.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {X : Type*} [MetricSpace X]

/-- **Assumption 4.3** (metric form): `Γ` is nonempty, compact-valued and continuous. -/
structure Assumption43 (Γ : X → Set X) : Prop where
  nonempty : ∀ x, (Γ x).Nonempty
  compact : ∀ x, IsCompact (Γ x)
  lhc : ∀ x, IsLHC Γ x
  uhc : ∀ x, IsUHC Γ x

/-- **Assumption 4.4.** `F` is bounded and continuous on the graph `A`, and `0 < β < 1`. -/
structure Assumption44 (Γ : X → Set X) (F : X × X → ℝ) (β : ℝ) : Prop where
  cont : ContinuousOn F (graph Γ)
  bdd : ∃ B, ∀ p ∈ graph Γ, |F p| ≤ B
  β_pos : 0 < β
  β_lt : β < 1

variable {Γ : X → Set X} {F : X × X → ℝ} {β : ℝ}

/-- The objective `F(x, y) + βf(y)`. -/
def obj (F : X × X → ℝ) (β : ℝ) (f : X → ℝ) (p : X × X) : ℝ := F p + β * f p.2

theorem continuousOn_obj (h44 : Assumption44 Γ F β) {f : X → ℝ} (hf : Continuous f) :
    ContinuousOn (obj F β f) (graph Γ) :=
  h44.cont.add (continuousOn_const.mul (hf.comp continuous_snd).continuousOn)

theorem bound_maxValue (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) (f : X →ᵇ ℝ) (x : X) :
    ‖maxValue (obj F β f) Γ x‖ ≤ h44.bdd.choose + β * ‖f‖ := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax (continuousOn_obj h44 f.continuous) (h43.compact x)
    (h43.nonempty x)
  rw [← hval, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add (h44.bdd.choose_spec (x, y) hy) ?_)
  rw [abs_mul, abs_of_pos h44.β_pos]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) h44.β_pos.le

/-- The operator `(Tf)(x) = max_{y ∈ Γ(x)} [F(x, y) + βf(y)]` on `C(X)` (Theorem 4.6: `Tf` is
bounded and continuous by the Theorem of the Maximum). -/
noncomputable def bellman (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) (f : X →ᵇ ℝ) :
    X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => maxValue (obj F β f) Γ x)
    (theorem_3_6 (continuousOn_obj h44 f.continuous) h43.compact h43.lhc h43.uhc).1
    (h44.bdd.choose + β * ‖f‖) (bound_maxValue h43 h44 f)

theorem bellman_apply (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) (f : X →ᵇ ℝ) (x : X) :
    bellman h43 h44 f x = maxValue (obj F β f) Γ x := rfl

/-- `Tf(x) = F(x, y) + βf(y)` at a maximizer `y`. -/
theorem exists_bellman_argmax (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) (f : X →ᵇ ℝ)
    (x : X) : ∃ y ∈ Γ x, bellman h43 h44 f x = F (x, y) + β * f y ∧
      ∀ z ∈ Γ x, F (x, z) + β * f z ≤ bellman h43 h44 f x := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_obj h44 f.continuous)
    (h43.compact x) (h43.nonempty x)
  exact ⟨y, hy, hval.symm, fun z hz => (hmax z hz).trans_eq hval⟩

/-- `T` is monotone (Theorem 3.3a). -/
theorem bellman_mono (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) {f g : X →ᵇ ℝ}
    (hfg : f ≤ g) : bellman h43 h44 f ≤ bellman h43 h44 g := fun x => by
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax h43 h44 f x
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax h43 h44 g x
  change bellman h43 h44 f x ≤ bellman h43 h44 g x
  rw [hval]
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (show f y ≤ g y from hfg y)
    h44.β_pos.le)).trans (hmax y hy)

/-- `T(f + a) = Tf + βa` (discounting, Theorem 3.3b, with equality). -/
theorem bellman_add_const (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) (f : X →ᵇ ℝ)
    (a : ℝ) : bellman h43 h44 (f + const X a) = bellman h43 h44 f + const X (β * a) := by
  ext x
  obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax h43 h44 f x
  obtain ⟨z, hz, hzval, hzmax⟩ := exists_bellman_argmax h43 h44 (f + const X a) x
  simp only [BoundedContinuousFunction.add_apply, const_apply] at hzval hzmax ⊢
  refine le_antisymm ?_ ?_
  · rw [hzval]; have := hmax z hz; linarith
  · have := hzmax y hy; rw [hval]; linarith

/-- **Blackwell's sufficient conditions** (Theorem 3.3) on the bounded continuous functions
on any topological space. -/
theorem blackwell {Y : Type*} [TopologicalSpace Y] {T : (Y →ᵇ ℝ) → (Y →ᵇ ℝ)} (hβ : 0 ≤ β)
    (hmono : ∀ f g, f ≤ g → T f ≤ T g)
    (hdisc : ∀ f a, 0 ≤ a → T (f + const Y a) ≤ T f + const Y (β * a)) (f g : Y →ᵇ ℝ) :
    dist (T f) (T g) ≤ β * dist f g := by
  have hle : ∀ f g : Y →ᵇ ℝ, f ≤ g + const Y (dist f g) := fun f g x => by
    change f x ≤ (g + const Y (dist f g)) x
    rw [BoundedContinuousFunction.add_apply, const_apply]
    have := dist_coe_le_dist (f := f) (g := g) x
    rw [Real.dist_eq] at this
    linarith [le_abs_self (f x - g x)]
  have h1 : ∀ f g : Y →ᵇ ℝ, ∀ x, T f x ≤ T g x + β * dist f g := fun f g x => by
    have : T f x ≤ (T g + const Y (β * dist f g)) x :=
      (hmono _ _ (hle f g)).trans (hdisc g _ dist_nonneg) x
    rwa [BoundedContinuousFunction.add_apply, const_apply] at this
  refine (dist_le (mul_nonneg hβ dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq, abs_le]
  have a := h1 f g x
  have b := h1 g f x
  rw [dist_comm] at b
  constructor <;> linarith

/-- `T` is a contraction of modulus `β`. -/
theorem bellman_contraction [Nonempty X] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) :
    IsContraction (bellman h43 h44) β :=
  ⟨h44.β_pos, h44.β_lt, blackwell h44.β_pos.le (fun _ _ => bellman_mono h43 h44)
    (fun f a _ => (bellman_add_const h43 h44 f a).le)⟩

/-- **Theorem 4.6.** Under Assumptions 4.3–4.4, `T : C(X) → C(X)` has a unique fixed point `v`,
`‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and `G(x) = {y ∈ Γ(x) : v(x) = F(x, y) + βv(y)}` is nonempty,
compact-valued and u.h.c. -/
theorem theorem_4_6 [Nonempty X] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) :
    ∃ v : X →ᵇ ℝ, bellman h43 h44 v = v ∧ (∀ w, bellman h43 h44 w = w → w = v) ∧
      (∀ v₀ (n : ℕ), dist ((bellman h43 h44)^[n] v₀) v ≤ β ^ n * dist v₀ v) ∧
      ∀ x, (argmax (obj F β v) Γ x).Nonempty ∧ IsCompact (argmax (obj F β v) Γ x) ∧
        IsUHC (argmax (obj F β v) Γ) x := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 (bellman_contraction h43 h44)
  exact ⟨v, hv, huniq, hrate,
    (theorem_3_6 (continuousOn_obj h44 v.continuous) h43.compact h43.lhc h43.uhc).2⟩

/-! ### The fixed point is the supremum function (p. 80) -/

/-- The sequence-problem return `(x, y) ↦ F(x, y)`. -/
def curryF (F : X × X → ℝ) (x y : X) : ℝ := F (x, y)

theorem assumption42_of_44 (h44 : Assumption44 Γ F β) : Assumption42 Γ (curryF F) β := by
  obtain ⟨B, hB⟩ := h44.bdd
  refine assumption42_of_summable_pos fun x₀ x hx =>
    summable_max_of_le_geometric h44.β_pos.le h44.β_lt (le_max_right B 0) fun t => ?_
  rw [mul_comm (max B 0)]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((hB (x t, x (t + 1)) (hx.2 t)).trans
    (le_max_left _ _))) (pow_nonneg h44.β_pos.le t)

/-- A bounded continuous fixed point of `T` satisfies (FE) in `R̄`. -/
theorem satisfiesFE_of_fixed (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) {v : X →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) : SatisfiesFE Γ (curryF F) β fun x => (v x : EReal) := by
  intro x
  obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax h43 h44 v x
  rw [hv] at hval hmax
  change (v x : EReal) = ⨆ y ∈ Γ x, ((curryF F x y : ℝ) : EReal) + (β : EReal) * (v y : EReal)
  refine le_antisymm ?_ (iSup₂_le fun z hz => ?_)
  · have := le_biSup (fun z => ((curryF F x z : ℝ) : EReal) + (β : EReal) * (v z : EReal)) hy
    refine le_trans ?_ this
    rw [hval, curryF, ← EReal.coe_mul, ← EReal.coe_add]
  · rw [curryF, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (hmax z hz)

theorem tendsto_bounded_discount (h44 : Assumption44 Γ F β) (v : X →ᵇ ℝ) (x : ℕ → X) :
    Tendsto (fun n => ((β ^ n : ℝ) : EReal) * (v (x n) : EReal)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => β ^ n * v (x n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => β ^ n * ‖v‖) (fun n => ?_) ?_
    · rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos h44.β_pos]
      exact mul_le_mul_of_nonneg_left (v.norm_coe_le_norm _) (pow_nonneg h44.β_pos.le n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h44.β_pos.le h44.β_lt).mul_const ‖v‖
  have := (EReal.tendsto_coe.2 hb)
  simpa only [EReal.coe_mul, EReal.coe_zero] using this

/-- **p. 80.** The fixed point of `T` is the supremum function `v*` (Theorem 4.3). -/
theorem fixedPoint_eq_vstar (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) {v : X →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) : (fun x => (v x : EReal)) = vstar Γ (curryF F) β :=
  theorem_4_3 h44.β_pos.le h43.nonempty (assumption42_of_44 h44) (satisfiesFE_of_fixed h43 h44 hv)
    fun _ x _ => tendsto_bounded_discount h44 v x

/-- **p. 80.** Every plan generated by the policy correspondence `G` is optimal (Theorem 4.5). -/
theorem policy_plan_optimal (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) {v : X →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) {x₀ : X} {x : ℕ → X} (h0 : x 0 = x₀)
    (hgen : ∀ t, x (t + 1) ∈ argmax (obj F β v) Γ (x t)) :
    total (curryF F) β x = vstar Γ (curryF F) β x₀ := by
  have hvs := fixedPoint_eq_vstar h43 h44 hv
  refine theorem_4_5 h44.β_pos.le (assumption42_of_44 h44) ⟨h0, fun t => (hgen t).1⟩
    (fun t => ?_) ?_
  · rw [← hvs]
    have h := (hgen t).2
    rw [← bellman_apply h43 h44, hv] at h
    change (v (x t) : EReal) =
      ((curryF F (x t) (x (t + 1)) : ℝ) : EReal) + (β : EReal) * (v (x (t + 1)) : EReal)
    rw [← h, obj, curryF, EReal.coe_add, EReal.coe_mul]
  · rw [← hvs]
    exact (tendsto_bounded_discount h44 v x).limsup_eq.le

/-! ### Theorem 4.7: monotonicity -/

/-- **Theorem 4.7.** If in addition (Assumption 4.5) `F(·, y)` is strictly increasing and
(Assumption 4.6) `x ≤ x'` implies `Γ(x) ⊆ Γ(x')`, the fixed point `v` is strictly increasing. -/
theorem theorem_4_7 [Nonempty X] [PartialOrder X] (h43 : Assumption43 Γ)
    (h44 : Assumption44 Γ F β) (h45 : ∀ x x' y, x < x' → y ∈ Γ x → F (x, y) < F (x', y))
    (h46 : ∀ x x', x ≤ x' → Γ x ⊆ Γ x') {v : X →ᵇ ℝ} (hv : bellman h43 h44 v = v) :
    StrictMono v := by
  -- `T` maps the closed set of nondecreasing functions into the strictly increasing ones
  set C' : Set (X →ᵇ ℝ) := {f | Monotone f}
  set C'' : Set (X →ᵇ ℝ) := {f | StrictMono f}
  have hclosed : IsClosed C' := by
    have : C' = ⋂ x, ⋂ y, ⋂ (_ : x ≤ y), {f : X →ᵇ ℝ | f x ≤ f y} := by
      ext f; simp [C', Monotone]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const x) (continuous_eval_const y)
  have hmaps : MapsTo (bellman h43 h44) C' C'' := fun f _ x x' hxx' => by
    obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax h43 h44 f x
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax h43 h44 f x'
    rw [hval]
    exact (add_lt_add_of_lt_of_le (h45 x x' y hxx' hy) le_rfl).trans_le
      (hmax y (h46 x x' hxx'.le hy))
  have hne : C'.Nonempty := ⟨0, fun _ _ _ => le_rfl⟩
  exact (corollary_1 (bellman_contraction h43 h44) hv hne hclosed
    (hmaps.mono_right fun _ hf => hf.monotone) hmaps).2

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Concavity and the policy function

SLP §4.2, pp. 80–82. The state space is a convex set `S` in a real normed space (the book's
`X ⊆ ℝˡ`); functions on it are concave along the combinations `θx + (1 − θ)x'` (`cmb`).

* `IsConcaveS`, `IsStrictConcaveS`: (strict) concavity on `S`.
* `Assumption47` (`F` concave on the graph, strictly in `x`), `Assumption48` (the graph of `Γ` is
  convex).
* `bellman_maps_concave`: `T` maps concave functions to strictly concave ones.
* `theorem_4_8`: the fixed point `v` is strictly concave, the policy correspondence is a
  single-valued function `g`, and `g` is continuous.
* `theorem_4_9`: from a concave `v₀`, the policy functions `gₙ` of `vₙ = Tⁿv₀` converge to `g`
  pointwise, and uniformly when `S` is compact.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- `θx + (1 − θ)x'` in the convex set `S`. -/
def cmb (hS : Convex ℝ S) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x x' : S) : S :=
  ⟨θ • x.1 + (1 - θ) • x'.1, hS x.2 x'.2 h0 (by linarith) (by ring)⟩

theorem cmb_self (hS : Convex ℝ S) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : S) :
    cmb hS h0 h1 x x = x := by
  ext1; simp only [cmb]; rw [← add_smul]; simp

/-- `f` is concave on `S`. -/
def IsConcaveS (hS : Convex ℝ S) (f : S → ℝ) : Prop :=
  ∀ x x' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), θ * f x + (1 - θ) * f x' ≤ f (cmb hS h0 h1 x x')

/-- `f` is strictly concave on `S`. -/
def IsStrictConcaveS (hS : Convex ℝ S) (f : S → ℝ) : Prop :=
  ∀ x x', x ≠ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * f x + (1 - θ) * f x' < f (cmb hS h0.le h1.le x x')

/-- **Assumption 4.7.** `F` is concave on the graph `A`, strictly when `x ≠ x'`. -/
def Assumption47 (hS : Convex ℝ S) (Γ : S → Set S) (F : S × S → ℝ) : Prop :=
  ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hS h0.le h1.le x x', cmb hS h0.le h1.le y y') ∧
    (x ≠ x' →
      θ * F (x, y) + (1 - θ) * F (x', y') < F (cmb hS h0.le h1.le x x', cmb hS h0.le h1.le y y'))

/-- **Assumption 4.8.** `y ∈ Γ(x)` and `y' ∈ Γ(x')` imply `θy + (1 − θ)y' ∈ Γ(θx + (1 − θ)x')`. -/
def Assumption48 (hS : Convex ℝ S) (Γ : S → Set S) : Prop :=
  ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    cmb hS h0 h1 y y' ∈ Γ (cmb hS h0 h1 x x')

variable {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ} {β : ℝ}

/-- The concave functions form a closed subset of `C(S)`. -/
theorem isClosed_concave (hS : Convex ℝ S) : IsClosed {f : S →ᵇ ℝ | IsConcaveS hS f} := by
  have : {f : S →ᵇ ℝ | IsConcaveS hS f} = ⋂ x, ⋂ x', ⋂ θ : ℝ, ⋂ h0 : 0 ≤ θ, ⋂ h1 : θ ≤ 1,
      {f : S →ᵇ ℝ | θ * f x + (1 - θ) * f x' ≤ f (cmb hS h0 h1 x x')} := by
    ext f; simp [IsConcaveS]
  rw [this]
  refine isClosed_iInter fun x => isClosed_iInter fun x' => isClosed_iInter fun θ =>
    isClosed_iInter fun h0 => isClosed_iInter fun h1 => isClosed_le ?_ (continuous_eval_const _)
  exact (continuous_const.mul (continuous_eval_const x)).add
    (continuous_const.mul (continuous_eval_const x'))

/-- `T` maps concave functions into strictly concave ones (proof of Theorem 4.8). -/
theorem bellman_maps_concave (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {f : S →ᵇ ℝ}
    (hf : IsConcaveS hS f) : IsStrictConcaveS hS (bellman h43 h44 f) := by
  intro x₀ x₁ hne θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax h43 h44 f x₀
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax h43 h44 f x₁
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax h43 h44 f (cmb hS h0.le h1.le x₀ x₁)
  have hyθ := h48 x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0.le h1.le
  have hF := (h47 x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0 h1).2 hne
  have hfc := mul_le_mul_of_nonneg_left (hf y₀ y₁ θ h0.le h1.le) h44.β_pos.le
  rw [hv₀, hv₁]
  refine lt_of_lt_of_le ?_ (hmax _ hyθ)
  nlinarith

/-- `T` preserves concavity. -/
theorem bellman_concave (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {f : S →ᵇ ℝ}
    (hf : IsConcaveS hS f) : IsConcaveS hS (bellman h43 h44 f) := by
  intro x x' θ h0 h1
  rcases eq_or_ne x x' with rfl | hne
  · rw [cmb_self]; linarith
  rcases h0.eq_or_lt with rfl | h0'
  · simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  rcases h1.eq_or_lt with rfl | h1'
  · simp only [one_mul, sub_self, zero_mul, add_zero]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  exact (bellman_maps_concave h43 h44 h47 h48 hf x x' hne θ h0' h1').le

/-- With `w` strictly concave, `y ↦ F(x, y) + βw(y)` has at most one maximizer on `Γ(x)`. -/
theorem argmax_unique_of_strictConcave (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {w : S →ᵇ ℝ}
    (hw : IsStrictConcaveS hS w) (x : S) :
    ∀ y₁ ∈ argmax (obj F β w) Γ x, ∀ y₂ ∈ argmax (obj F β w) Γ x, y₁ = y₂ := by
  intro y₁ hy₁ y₂ hy₂
  by_contra hne
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hmem := h48 x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh.le hh1.le
  rw [cmb_self] at hmem
  have hF := (h47 x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh hh1).1
  rw [cmb_self] at hF
  have hvs := mul_lt_mul_of_pos_left (hw y₁ y₂ hne (1 / 2) hh hh1) h44.β_pos
  have hle := le_maxValue (continuousOn_obj h44 w.continuous) (h43.compact x) hmem
  have e1 := hy₁.2
  have e2 := hy₂.2
  simp only [obj] at hle e1 e2
  linarith

/-- **Theorem 4.8.** Under Assumptions 4.3–4.4 and 4.7–4.8, the fixed point `v` is strictly
concave, the policy correspondence `G` is single-valued, and its selection `g` is continuous. -/
theorem theorem_4_8 [Nonempty S] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) :
    IsStrictConcaveS hS v ∧ UniqueArgmax Γ (obj F β v) ∧
      (∀ x, argmax (obj F β v) Γ x = {argmaxFn Γ (obj F β v) x}) ∧
      Continuous (argmaxFn Γ (obj F β v)) := by
  have hvc : IsStrictConcaveS hS v :=
    (corollary_1 (S' := {f : S →ᵇ ℝ | IsConcaveS hS f}) (S'' := {f | IsStrictConcaveS hS f})
      (bellman_contraction h43 h44) hv ⟨0, fun x x' θ _ _ => by simp⟩ (isClosed_concave hS)
      (fun _ hf => bellman_concave h43 h44 h47 h48 hf)
      (fun _ hf => bellman_maps_concave h43 h44 h47 h48 hf)).2
  have huniq := argmax_unique_of_strictConcave h43 h44 h47 h48 hvc
  have hU : UniqueArgmax Γ (obj F β v) :=
    ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc, continuousOn_obj h44 v.continuous, huniq⟩
  exact ⟨hvc, hU, hU.argmax_eq, hU.continuous_argmaxFn⟩

/-- **Theorem 4.9 (convergence of the policy functions).** Let `v₀` be bounded, continuous and
concave, `vₙ = Tⁿv₀` and `gₙ` the maximizer for `vₙ`. Then `gₙ → g` pointwise, and uniformly
if `S` is compact. -/
theorem theorem_4_9 [Nonempty S] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) {v₀ : S →ᵇ ℝ} (hv₀ : IsConcaveS hS v₀) :
    (∀ x, Tendsto (fun n => argmaxFn Γ (obj F β ((bellman h43 h44)^[n] v₀)) x) atTop
      (𝓝 (argmaxFn Γ (obj F β v) x))) ∧
    (CompactSpace S → TendstoUniformly
      (fun n => argmaxFn Γ (obj F β ((bellman h43 h44)^[n] v₀)))
      (argmaxFn Γ (obj F β v)) atTop) := by
  set T := bellman h43 h44
  -- every iterate is concave, and from `n = 1` on strictly concave
  have hconc : ∀ n, IsConcaveS hS (T^[n] v₀) := by
    intro n
    induction n with
    | zero => exact hv₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact bellman_concave h43 h44 h47 h48 ih
  have hU : ∀ n, UniqueArgmax Γ (obj F β (T^[n + 1] v₀)) := fun n => by
    have hsc : IsStrictConcaveS hS (T^[n + 1] v₀) := by
      rw [Function.iterate_succ_apply']
      exact bellman_maps_concave h43 h44 h47 h48 (hconc n)
    exact ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc,
      continuousOn_obj h44 (T^[n + 1] v₀).continuous,
      argmax_unique_of_strictConcave h43 h44 h47 h48 hsc⟩
  have hUv := (theorem_4_8 h43 h44 h47 h48 hv).2.1
  -- `F + βvₙ → F + βv` uniformly
  have hunif : TendstoUniformlyOn (fun n => obj F β (T^[n + 1] v₀)) (obj F β v) atTop
      (graph Γ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => β * (β ^ (n + 1) * dist v₀ v)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h44.β_pos.le h44.β_lt).comp
        (tendsto_add_atTop_nat 1)).mul_const (dist v₀ v) |>.const_mul β
      simpa using this
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn p _
    have hd : dist (T^[n + 1] v₀) v ≤ β ^ (n + 1) * dist v₀ v := by
      obtain ⟨w, -, hwu, hwr⟩ := theorem_3_2 (bellman_contraction h43 h44)
      rw [← hwu v hv] at hwr
      exact hwr v₀ (n + 1)
    simp only [obj, Real.dist_eq]
    calc |F p + β * v p.2 - (F p + β * (T^[n + 1] v₀) p.2)|
        = β * |v p.2 - (T^[n + 1] v₀) p.2| := by
          rw [show F p + β * v p.2 - (F p + β * (T^[n + 1] v₀) p.2) =
            β * (v p.2 - (T^[n + 1] v₀) p.2) by ring, abs_mul, abs_of_pos h44.β_pos]
      _ ≤ β * (β ^ (n + 1) * dist v₀ v) := by
          refine mul_le_mul_of_nonneg_left ?_ h44.β_pos.le
          rw [← Real.dist_eq, dist_comm]
          exact (dist_coe_le_dist _).trans hd
      _ < ε := hn
  refine ⟨fun x => ?_, fun _ => ?_⟩
  · exact (tendsto_add_atTop_iff_nat 1).1 (theorem_3_8 hUv hU hunif x)
  · have := theorem_3_8_uniform hUv hU hunif
    rw [Metric.tendstoUniformly_iff] at this ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (this ε hε)
    refine eventually_atTop.2 ⟨N + 1, fun n hn x => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hN m (by omega) x

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Differentiability of a concave function from below: Benveniste and Scheinkman

SLP §4.2, pp. 83–86.

* `theorem_4_10` (**Benveniste–Scheinkman**): if `V` is concave on a convex `X`, `x₀ ∈ int X`, and
  a function `W` differentiable at `x₀` satisfies `W(x₀) = V(x₀)` and `W ≤ V` near `x₀`, then `V`
  is differentiable at `x₀` with `DV(x₀) = DW(x₀)`. The proof needs no subgradients: near `x₀`,
  `W(x₀ + h) − W(x₀) ≤ V(x₀ + h) − V(x₀) ≤ V(x₀) − V(x₀ − h) ≤ W(x₀) − W(x₀ − h)`, the middle
  step by concavity at the midpoint `x₀`. Concavity of `W` (assumed in the book) is not needed.
* `ex_4_5`: from the first-order condition `U′(f(x) − g(x)) = βv′(g(x))` with `U`, `f`, `v`
  strictly increasing, strictly concave and differentiable, `0 < g(x′) − g(x) < f(x′) − f(x)`
  for `x′ > x`.
-/

open Filter Topology Asymptotics Set

namespace StokeyLucasPrescott.DeterministicDynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 4.10 (Benveniste and Scheinkman).** Let `V` be concave on a convex set `X`,
`x₀ ∈ int X`, and `W` differentiable at `x₀` with `W(x₀) = V(x₀)` and `W ≤ V` on a neighborhood
of `x₀`. Then `V` is differentiable at `x₀` and `DV(x₀) = DW(x₀)`. -/
theorem theorem_4_10 {X : Set E} {V W : E → ℝ} {x₀ : E} {W' : E →L[ℝ] ℝ}
    (hV : ConcaveOn ℝ X V) (hx₀ : X ∈ 𝓝 x₀) (hW : HasFDerivAt W W' x₀) (heq : W x₀ = V x₀)
    (hle : ∀ᶠ x in 𝓝 x₀, W x ≤ V x) : HasFDerivAt V W' x₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hW ⊢
  set r : E → ℝ := fun h => W (x₀ + h) - W x₀ - W' h
  -- the remainder of `W` at `−h`
  have hr' : (fun h : E => r (-h)) =o[𝓝 0] fun h => h := by
    have := hW.comp_tendsto (show Tendsto (fun h : E => -h) (𝓝 0) (𝓝 0) by
      simpa using (continuous_neg (G := E)).tendsto 0)
    refine (this.trans_isBigO ?_)
    exact IsBigO.of_bound 1 (Eventually.of_forall fun h => by simp)
  -- `x₀ ± h ∈ X` and `W ≤ V` there, for `h` near `0`
  have hplus : ∀ᶠ h in 𝓝 (0 : E), x₀ + h ∈ X ∧ W (x₀ + h) ≤ V (x₀ + h) := by
    have hc : Tendsto (fun h : E => x₀ + h) (𝓝 0) (𝓝 x₀) := by
      simpa using (continuous_const_add x₀).tendsto (0 : E)
    exact (hc.eventually (Filter.eventually_mem_set.2 hx₀)).and (hc.eventually hle)
  have hminus : ∀ᶠ h in 𝓝 (0 : E), x₀ - h ∈ X ∧ W (x₀ - h) ≤ V (x₀ - h) := by
    have hc : Tendsto (fun h : E => x₀ - h) (𝓝 0) (𝓝 x₀) := by
      simpa using ((continuous_const.sub continuous_id).tendsto (0 : E) (f := fun h : E => x₀ - h))
    exact (hc.eventually (Filter.eventually_mem_set.2 hx₀)).and (hc.eventually hle)
  have hbound : ∀ᶠ h in 𝓝 (0 : E),
      ‖V (x₀ + h) - V x₀ - W' h‖ ≤ 1 * ‖‖r h‖ + ‖r (-h)‖‖ := by
    filter_upwards [hplus, hminus] with h hp hm
    have hx₀X : x₀ ∈ X := mem_of_mem_nhds hx₀
    -- concavity at the midpoint `x₀ = ½(x₀ + h) + ½(x₀ − h)`
    have hmid := hV.2 hp.1 hm.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e : (1 / 2 : ℝ) • (x₀ + h) + (1 / 2 : ℝ) • (x₀ - h) = x₀ := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hmid
    have er : r (-h) = W (x₀ - h) - W x₀ + W' h := by
      simp only [r, map_neg, ← sub_eq_add_neg]; ring
    rw [er, one_mul]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (abs_nonneg (r h))
      (abs_nonneg (W (x₀ - h) - W x₀ + W' h))), abs_le]
    have h1 := hp.2
    have h2 := hm.2
    constructor
    · cases abs_cases (W (x₀ + h) - W x₀ - W' h) <;> cases abs_cases (W (x₀ - h) - W x₀ + W' h) <;>
        simp only [r] at * <;> linarith
    · cases abs_cases (W (x₀ + h) - W x₀ - W' h) <;> cases abs_cases (W (x₀ - h) - W x₀ + W' h) <;>
        simp only [r] at * <;> linarith
  have hsum : (fun h : E => ‖r h‖ + ‖r (-h)‖) =o[𝓝 0] fun h => h :=
    hW.norm_left.add hr'.norm_left
  exact (IsBigO.of_bound 1 hbound).trans_isLittleO hsum

/-- **Exercise 4.5.** Let `U`, `f`, `v` be strictly increasing, strictly concave and
differentiable on `ℝ₊`, `0 < g(x) < f(x)`, and `U′(f(x) − g(x)) = βv′(g(x))` with `β > 0`. Then
`0 < g(x′) − g(x) < f(x′) − f(x)` for `0 ≤ x < x′`. -/
theorem ex_4_5 {U f v g : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUd : ∀ c ∈ Ici (0 : ℝ), DifferentiableAt ℝ U c)
    (hv : StrictConcaveOn ℝ (Ici 0) v) (hvd : ∀ c ∈ Ici (0 : ℝ), DifferentiableAt ℝ v c)
    (hf : StrictMonoOn f (Ici 0)) (hg : ∀ x ∈ Ici (0 : ℝ), 0 < g x ∧ g x < f x)
    (hfoc : ∀ x ∈ Ici (0 : ℝ), deriv U (f x - g x) = β * deriv v (g x))
    {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x < x') :
    0 < g x' - g x ∧ g x' - g x < f x' - f x := by
  have hx' : 0 ≤ x' := hx.trans hxx'.le
  have hU' := hU.strictAntiOn_deriv hUd
  have hv' := hv.strictAntiOn_deriv hvd
  have hfx := hf hx hx' hxx'
  obtain ⟨g0, g1⟩ := hg x hx
  obtain ⟨g0', g1'⟩ := hg x' hx'
  have hc : (0 : ℝ) ≤ f x - g x := by linarith
  have hc' : (0 : ℝ) ≤ f x' - g x' := by linarith
  constructor
  · -- if `g(x′) ≤ g(x)` then consumption rises, contradicting the first-order condition
    by_contra hle
    push Not at hle
    have h1 : deriv v (g x) ≤ deriv v (g x') := hv'.antitoneOn g0'.le g0.le (by linarith)
    have h2 : f x - g x < f x' - g x' := by linarith
    have h3 := hU' hc hc' h2
    rw [hfoc x hx, hfoc x' hx'] at h3
    nlinarith
  · -- if `g` rises by at least `f`, consumption falls, again a contradiction
    by_contra hle
    push Not at hle
    have h2 : f x' - g x' ≤ f x - g x := by linarith
    have h3 : deriv U (f x - g x) ≤ deriv U (f x' - g x') := hU'.antitoneOn hc' hc h2
    rw [hfoc x hx, hfoc x' hx'] at h3
    have hgg : g x < g x' := by linarith
    have h4 := hv' g0.le g0'.le hgg
    nlinarith

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interior points of convex-valued l.h.c. correspondences

Carried over from the Chapter 3 project (`RecursiveMethods/MathematicalPreliminaries`, the proof
of Exercise 3.12d): if `φ` is l.h.c. at `x` with convex values in `ℝᵐ`, every point interior to
`φ(x)` lies in `φ(xₙ)` for all large `n` (`eventually_mem_of_mem_interior`). Chapter 4 uses it in
Theorem 4.11, where the book asserts that `g(x₀) ∈ int Γ(x₀)` and continuity of `Γ` give
`g(x₀) ∈ Γ(x)` near `x₀`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {X : Type*} [MetricSpace X] {m : ℕ}

/-- A linear functional on `ℝ^m` in coordinates. -/
theorem dual_apply_eq_sum (f : StrongDual ℝ (Fin m → ℝ)) (v : Fin m → ℝ) :
    f v = ∑ j, v j * f (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, map_smul]

/-- `z ± 2δeⱼ`. -/
noncomputable def vertex (z : Fin m → ℝ) (δ : ℝ) (j : Fin m) (s : Bool) : Fin m → ℝ :=
  z + (if s then 2 * δ else -(2 * δ)) • Pi.single j 1

/-- No hyperplane separates `z` from points within `δ/(m + 1)` of every vertex `z ± 2δeⱼ`
(and from one further point `w₀`). -/
theorem no_separation {z : Fin m → ℝ} {δ : ℝ} (hδ : 0 < δ) (f : StrongDual ℝ (Fin m → ℝ))
    {u : ℝ} (hz : f z < u) {w₀ : Fin m → ℝ} (hw₀ : u < f w₀) (w : Fin m → Bool → Fin m → ℝ)
    (hw : ∀ j s, u < f (w j s)) (hclose : ∀ j s, ‖w j s - vertex z δ j s‖ ≤ δ / (m + 1)) :
    False := by
  set c : Fin m → ℝ := fun j => f (Pi.single j 1)
  set A := ∑ j, |c j|
  set ε := δ / ((m : ℝ) + 1)
  have hε : 0 < ε := by positivity
  -- the error terms move `f` by at most `εA`
  have herr : ∀ e : Fin m → ℝ, ‖e‖ ≤ ε → |f e| ≤ ε * A := fun e he => by
    rw [dual_apply_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm e j).trans he) (abs_nonneg _)
  have hcoord : ∀ j, 2 * δ * |c j| ≤ ε * A := fun j => by
    have hs : ∀ s, 0 < f (w j s) - f z := fun s => by linarith [hw j s]
    have hdec : ∀ s, f (w j s) - f z =
        (if s then 2 * δ else -(2 * δ)) * c j + f (w j s - vertex z δ j s) := fun s => by
      simp only [vertex, map_sub, map_add, map_smul, smul_eq_mul, c]
      ring
    have h1 := hdec true
    have h2 := hdec false
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    have e1 := (abs_le.1 (herr _ (hclose j true))).2
    have e2 := (abs_le.1 (herr _ (hclose j false))).2
    have s1 := hs true
    have s2 := hs false
    rcases abs_cases (c j) with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [hc] <;> nlinarith
  have hsum : 2 * δ * A ≤ m * (ε * A) := by
    calc 2 * δ * A = ∑ j, 2 * δ * |c j| := Finset.mul_sum _ _ _
      _ ≤ ∑ _j : Fin m, ε * A := Finset.sum_le_sum fun j _ => hcoord j
      _ = m * (ε * A) := by simp
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hmε : (m : ℝ) * ε < 2 * δ := by
    have : (m : ℝ) * ε = δ * (m / (m + 1)) := by simp only [ε]; ring
    rw [this]
    have : (m : ℝ) / (m + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    nlinarith
  have hA : A = 0 := le_antisymm (by nlinarith) hA0
  have hc0 : ∀ j, c j = 0 := fun j => abs_eq_zero.1 (le_antisymm
    ((Finset.single_le_sum (fun k _ => abs_nonneg (c k)) (Finset.mem_univ j)).trans hA.le)
    (abs_nonneg _))
  have hf0 : ∀ v, f v = 0 := fun v => by
    rw [dual_apply_eq_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [show f (Pi.single j 1) = c j from rfl, hc0 j,
      mul_zero]
  linarith [hf0 z, hf0 w₀]

/-- If `φ` is l.h.c. at `x` with convex values in `ℝ^m`, every point interior to `φ(x)` lies in
`φ(xₙ)` for all large `n`, whenever `xₙ → x`. -/
theorem eventually_mem_of_mem_interior {φ : X → Set (Fin m → ℝ)} (hconv : ∀ x', Convex ℝ (φ x'))
    {x : X} (hφ : IsLHC φ x) {z : Fin m → ℝ} (hz : z ∈ interior (φ x)) {xs : ℕ → X}
    (hxs : Tendsto xs atTop (𝓝 x)) : ∀ᶠ n in atTop, z ∈ φ (xs n) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  set δ := r / 4
  have hδ : 0 < δ := by positivity
  have hv : ∀ j s, vertex z δ j s ∈ φ x := fun j s => interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, vertex, add_sub_cancel_left]
    refine (norm_smul_le _ _).trans_lt ?_
    have h1 : ‖(Pi.single j 1 : Fin m → ℝ)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2
      fun k => by
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
    have h2 : ‖(if s then 2 * δ else -(2 * δ))‖ = 2 * δ := by
      cases s <;> simp [abs_of_pos hδ]
    rw [h2]
    have h3 : 2 * δ < r := by simp only [δ]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * δ)]))
  obtain ⟨N₀, y₀, hy₀, -⟩ := hφ.2 z (interior_subset hz) xs hxs
  have happ := fun j s => hφ.2 _ (hv j s) xs hxs
  choose N ys hys hlim using happ
  have hclose : ∀ᶠ n in atTop, ∀ j s, ‖ys j s n - vertex z δ j s‖ ≤ δ / (m + 1) :=
    eventually_all.2 fun j => eventually_all.2 fun s => by
      filter_upwards [(hlim j s).eventually (Metric.closedBall_mem_nhds _
        (show (0 : ℝ) < δ / (m + 1) by positivity))] with n hn
      rwa [dist_eq_norm] at hn
  have hN : ∀ᶠ n in atTop, ∀ j s, N j s ≤ n :=
    eventually_all.2 fun j => eventually_all.2 fun s => eventually_ge_atTop _
  filter_upwards [hclose, hN, eventually_ge_atTop N₀] with n h1 h2 h3
  by_contra hzn
  set S : Set (Fin m → ℝ) := insert (y₀ n) (range fun p : Fin m × Bool => ys p.1 p.2 n)
  have hS : S ⊆ φ (xs n) := by
    rintro w (rfl | ⟨p, rfl⟩)
    · exact hy₀ n h3
    · exact hys p.1 p.2 n (h2 p.1 p.2)
  have hcl : IsClosed (convexHull ℝ S) :=
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) ((Set.finite_range _).insert _)).isClosed
  obtain ⟨f, u, hfz, hfu⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ S) hcl
    fun h => hzn (convexHull_min hS (hconv _) h)
  exact no_separation hδ f hfz (hfu _ (subset_convexHull ℝ S (mem_insert _ _)))
    (fun j s => ys j s n)
    (fun j s => hfu _ (subset_convexHull ℝ S (mem_insert_of_mem _ ⟨(j, s), rfl⟩))) h1

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Differentiability of the value function

SLP Theorem 4.11, p. 85. The state space is a convex set `S ⊆ ℝˡ`; a function `f` on `S` is
extended by zero to `ℝˡ` (`liftS`) so that its derivative at interior points of `S` makes sense.

* `concaveOn_liftS`: a concave function on `S` gives a concave function on `S ⊆ ℝˡ`.
* `eventually_mem_Γ`: if `g(x₀)` is interior to `Γ(x₀)`, then `g(x₀) ∈ Γ(x)` for all `x` near
  `x₀`. The book takes this from the continuity of `Γ`; it uses the convexity of the values of
  `Γ` (Assumption 4.8).
* `theorem_4_11`: if `x₀ ∈ int S`, `g(x₀) ∈ int Γ(x₀)` and `x ↦ F(x, g(x₀))` is differentiable at
  `x₀`, then `v` is differentiable at `x₀` with `Dv(x₀) = D_xF(x₀, g(x₀))`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ} {S : Set (Fin l → ℝ)} {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ}
  {β : ℝ}

/-- A function on `S` extended by zero to `ℝˡ`. -/
noncomputable def liftS (f : S → ℝ) (x : Fin l → ℝ) : ℝ := by
  classical exact if hx : x ∈ S then f ⟨x, hx⟩ else 0

theorem liftS_of_mem (f : S → ℝ) {x : Fin l → ℝ} (hx : x ∈ S) : liftS f x = f ⟨x, hx⟩ := by
  simp only [liftS, hx, ↓reduceDIte]

/-- A strictly concave function is concave. -/
theorem IsStrictConcaveS.isConcaveS {f : S → ℝ} (hf : IsStrictConcaveS hS f) :
    IsConcaveS hS f := by
  intro x x' θ h0 h1
  rcases eq_or_ne x x' with rfl | hne
  · rw [cmb_self]; linarith
  rcases h0.eq_or_lt with rfl | h0'
  · simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  rcases h1.eq_or_lt with rfl | h1'
  · simp only [one_mul, sub_self, zero_mul, add_zero]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  exact (hf x x' hne θ h0' h1').le

/-- A concave function on `S` is concave on `S ⊆ ℝˡ` after extension. -/
theorem concaveOn_liftS {f : S → ℝ} (hf : IsConcaveS hS f) : ConcaveOn ℝ S (liftS f) := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hmem : a • x + b • y ∈ S := hS hx hy ha hb hab
  rw [liftS_of_mem f hx, liftS_of_mem f hy, liftS_of_mem f hmem, smul_eq_mul, smul_eq_mul]
  have := hf ⟨x, hx⟩ ⟨y, hy⟩ a ha ha1
  subst hb'
  exact this

/-- Under Assumption 4.8 the values of `Γ` are convex subsets of `ℝˡ`. -/
theorem convex_image_Γ (h48 : Assumption48 hS Γ) (x : S) : Convex ℝ (Subtype.val '' Γ x) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := h48 x y x y' hy hy' a ha (by linarith)
  rw [cmb_self] at this
  exact ⟨_, this, rfl⟩

/-- If `g₀` is interior to `Γ(x₀)` (as a subset of `ℝˡ`), then `g₀ ∈ Γ(x)` for all `x` near
`x₀` (continuity of `Γ` and Assumption 4.8). -/
theorem eventually_mem_Γ (h43 : Assumption43 Γ) (h48 : Assumption48 hS Γ) {x₀ g₀ : S}
    (hg : g₀.1 ∈ interior (Subtype.val '' Γ x₀)) : ∀ᶠ x in 𝓝 x₀, g₀ ∈ Γ x := by
  have hlhc : IsLHC (fun x => Subtype.val '' Γ x) x₀ := by
    refine ⟨(h43.lhc x₀).1.image _, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ xs hxs
    obtain ⟨N, ys, hys, hlim⟩ := (h43.lhc x₀).2 y hy xs hxs
    exact ⟨N, fun n => (ys n).1, fun n hn => ⟨ys n, hys n hn, rfl⟩,
      (continuous_subtype_val.tendsto y).comp hlim⟩
  have hseq : ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x₀) → ∀ᶠ n in atTop, g₀ ∈ Γ (xs n) :=
    fun xs hxs => (eventually_mem_of_mem_interior (convex_image_Γ h48) hlhc hg hxs).mono
      fun n ⟨y, hy, hyg⟩ => Subtype.ext hyg ▸ hy
  exact eventually_iff_seq_eventually.2 hseq

/-- **Theorem 4.11 (differentiability of the value function).** Under Assumptions 4.3–4.4 and
4.7–4.8, if `x₀ ∈ int S`, `g(x₀) ∈ int Γ(x₀)` and `x ↦ F(x, g(x₀))` has derivative `DF` at `x₀`,
then `v` is differentiable at `x₀` with derivative `DF`, i.e. `vᵢ(x₀) = Fᵢ(x₀, g(x₀))`. -/
theorem theorem_4_11 [Nonempty S] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) {x₀ : S} (hint : S ∈ 𝓝 x₀.1)
    (hg : (argmaxFn Γ (obj F β v) x₀).1 ∈ interior (Subtype.val '' Γ x₀))
    {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x => F (x, argmaxFn Γ (obj F β v) x₀)) DF x₀.1) :
    HasFDerivAt (liftS v) DF x₀.1 := by
  set g₀ := argmaxFn Γ (obj F β v) x₀
  obtain ⟨hvc, hU, -, -⟩ := theorem_4_8 h43 h44 h47 h48 hv
  set W : (Fin l → ℝ) → ℝ := fun x => liftS (fun x => F (x, g₀)) x + β * v g₀
  have hW : HasFDerivAt W DF x₀.1 := hF.add_const _
  -- `W(x₀) = v(x₀)`
  have hg₀ := hU.argmaxFn_mem x₀
  have hvx : ∀ x : S, v x = maxValue (obj F β v) Γ x := fun x => by
    rw [← bellman_apply h43 h44, hv]
  have heq : W x₀.1 = liftS v x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx x₀]
    exact hg₀.2
  -- `W ≤ v` near `x₀`
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS v x := by
    have h1 := eventually_mem_Γ (hS := hS) h43 h48 (x₀ := x₀) (g₀ := g₀) hg
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx ⟨x, hxS⟩]
    exact le_maxValue (continuousOn_obj h44 v.continuous) (h43.compact _) (hx ⟨x, hxS⟩ rfl)
  exact theorem_4_10 (concaveOn_liftS hvc.isConcaveS) hint hW heq hle

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Euler equations and the transversality condition

SLP §4.5, pp. 97–100. States lie in a real normed space `E`; `F : E × E → ℝ` has derivative
`DF_t` at `(x*_t, x*_{t+1})`, with partial derivatives `F_x = DF_t(·, 0)` and `F_y = DF_t(0, ·)`.

* `concave_le_fderiv`: a concave function lies below its tangent plane at a point of
  differentiability.
* `euler_telescope`: under the Euler equations (2)
  `F_y(x*_t, x*_{t+1}) + βF_x(x*_{t+1}, x*_{t+2}) = 0`, the first-order terms of
  `Σ_{t ≤ T} βᵗ[F(x*_t, x*_{t+1}) − F(x_t, x_{t+1})]` telescope to the boundary term
  `−βᵀ⁺¹F_x(x*_{T+1}, x*_{T+2})·(x*_{T+1} − x_{T+1})`.
* `euler_sufficient`: a plan satisfying (2), with `F` below its tangent planes along it and the
  boundary terms asymptotically nonnegative against every feasible plan, is optimal.
* `theorem_4_15` (**sufficiency of the Euler and transversality conditions**): on the
  nonnegative cone, with `F` concave and nondecreasing in `x`, (2) and (3)
  `βᵗF_x(x*_t, x*_{t+1})·x*_t → 0` imply optimality.
* `euler_of_envelope` (p. 100): the first-order condition (4) and the envelope condition (5)
  give (2) along a plan generated by the policy.
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A concave function lies below its tangent plane: if `φ` is concave on a convex set `A`
containing `z*` and `z`, and has derivative `φ'` at `z*`, then `φ(z) ≤ φ(z*) + φ'(z − z*)`. -/
theorem concave_le_fderiv {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {A : Set F'}
    {φ : F' → ℝ} (hφ : ConcaveOn ℝ A φ) {z₀ z : F'} (hz₀ : z₀ ∈ A) (hz : z ∈ A)
    {φ' : F' →L[ℝ] ℝ} (hd : HasFDerivAt φ φ' z₀) : φ z ≤ φ z₀ + φ' (z - z₀) := by
  set g : ℝ → ℝ := fun t => φ (z₀ + t • (z - z₀))
  have hg : HasDerivAt g (φ' (z - z₀)) 0 := by
    have hline : HasDerivAt (fun t : ℝ => z₀ + t • (z - z₀)) (z - z₀) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (z - z₀)).const_add z₀
    have hd' : HasFDerivAt φ φ' (z₀ + (0 : ℝ) • (z - z₀)) := by simpa using hd
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    simpa [g, Function.comp_def] using this
  -- for `t ∈ (0, 1]`, `(g(t) − g(0))/t ≥ g(1) − g(0)` by concavity
  have hslope : ∀ t : ℝ, 0 < t → t ≤ 1 → φ z - φ z₀ ≤ t⁻¹ • (g (0 + t) - g 0) := by
    intro t ht0 ht1
    have hc := hφ.2 hz₀ hz (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    have e : (1 - t) • z₀ + t • z = z₀ + t • (z - z₀) := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hc
    simp only [g, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    linarith
  have hlim := hg.tendsto_slope_zero_right
  refine sub_le_iff_le_add'.1 (ge_of_tendsto hlim ?_)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with t ht
  exact hslope t ht.1 ht.2.le

/-- `F_x = DF(·, 0)`. -/
def Fx (D : E × E →L[ℝ] ℝ) (v : E) : ℝ := D (v, 0)

/-- `F_y = DF(0, ·)`. -/
def Fy (D : E × E →L[ℝ] ℝ) (v : E) : ℝ := D (0, v)

theorem apply_eq_Fx_add_Fy (D : E × E →L[ℝ] ℝ) (u v : E) : D (u, v) = Fx D u + Fy D v := by
  rw [Fx, Fy, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

variable {Γ : E → Set E} {F : E × E → ℝ} {β : ℝ}

/-- **The telescoping step of Theorem 4.15.** If `d₀ = 0` and the Euler equations hold, then
`Σ_{t ≤ T} βᵗ DF_t(d_t, d_{t+1}) = −βᵀ⁺¹F_x(T + 1)(d_{T+1})`. -/
theorem euler_telescope (D : ℕ → E × E →L[ℝ] ℝ) (d : ℕ → E) (hd0 : d 0 = 0)
    (heuler : ∀ t v, Fy (D t) v + β * Fx (D (t + 1)) v = 0) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * D t (d t, d (t + 1)) =
      -(β ^ (T + 1) * Fx (D (T + 1)) (d (T + 1))) := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one,
      apply_eq_Fx_add_Fy, hd0]
    have h0 : Fx (D 0) 0 = 0 := by
      change D 0 (0, 0) = 0
      rw [Prod.mk_zero_zero, map_zero]
    have := heuler 0 (d 1)
    rw [h0]; linarith
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, apply_eq_Fx_add_Fy]
    have := heuler (T + 1) (d (T + 1 + 1))
    have e : β ^ (T + 1 + 1) = β ^ (T + 1) * β := pow_succ _ _
    rw [e]
    linear_combination β ^ (T + 1) * this

/-- If `sₙ → L`, `wₙ → 0` and `s'ₙ ≤ sₙ + wₙ`, `s'ₙ → L'`, then `L' ≤ L` (in `R̄`, for real
sequences). -/
theorem le_of_le_add_tendsto_zero {s s' w : ℕ → ℝ} {L L' : EReal}
    (hs : Tendsto (fun n => (s n : EReal)) atTop (𝓝 L))
    (hs' : Tendsto (fun n => (s' n : EReal)) atTop (𝓝 L'))
    (hw : Tendsto w atTop (𝓝 0)) (h : ∀ n, s' n ≤ s n + w n) : L' ≤ L := by
  have hw' : Tendsto (fun n => ((w n : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
    have := EReal.tendsto_coe.2 hw
    rwa [EReal.coe_zero] at this
  have hsum : Tendsto (fun n => ((s n + w n : ℝ) : EReal)) atTop (𝓝 (L + 0)) := by
    simp only [EReal.coe_add]
    exact (EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))).tendsto.comp
      (hs.prodMk_nhds hw')
  rw [add_zero] at hsum
  exact le_of_tendsto_of_tendsto hs' hsum (Eventually.of_forall fun n =>
    EReal.coe_le_coe_iff.2 (h n))

/-- **Sufficiency of the Euler equations.** Let `x*` be feasible from `x₀`, with `F` below its
tangent planes at `(x*_t, x*_{t+1})` on the graph of `Γ`, satisfying the Euler equations (2), and
such that, against every feasible `x` with `u(x) > −∞`, the boundary terms
`βᵀ⁺¹F_x(T + 1)(x*_{T+1} − x_{T+1})` are bounded above by a sequence tending to `0`. Then `x*` is
optimal. -/
theorem euler_sufficient (h42 : Assumption42 Γ (fun x y => F (x, y)) β) {x₀ : E}
    {xs : ℕ → E} (hxs : xs ∈ Feasible Γ x₀) (D : ℕ → E × E →L[ℝ] ℝ)
    (hsup : ∀ t, ∀ x y, y ∈ Γ x → F (x, y) ≤ F (xs t, xs (t + 1)) + D t ((x, y) -
      (xs t, xs (t + 1))))
    (heuler : ∀ t v, Fy (D t) v + β * Fx (D (t + 1)) v = 0) (hβ : 0 ≤ β)
    (hbdry : ∀ x ∈ Feasible Γ x₀, total (fun x y => F (x, y)) β x ≠ ⊥ →
      ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
        ∀ T, β ^ (T + 1) * Fx (D (T + 1)) (xs (T + 1) - x (T + 1)) ≤ w T) :
    total (fun x y => F (x, y)) β xs = vstar Γ (fun x y => F (x, y)) β x₀ := by
  refine le_antisymm (le_biSup _ hxs) (iSup₂_le fun x hx => ?_)
  by_cases hbot : total (fun x y => F (x, y)) β x = ⊥
  · rw [hbot]; exact bot_le
  obtain ⟨w, hw, hwb⟩ := hbdry x hx hbot
  refine le_of_le_add_tendsto_zero (tendsto_total h42 hxs) (tendsto_total h42 hx) hw
    fun T => ?_
  -- `u_T(x) ≤ u_T(x*) + Σ βᵗ DF_t(x_t − x*_t, x_{t+1} − x*_{t+1}) = u_T(x*) + boundary`
  have hd0 : (fun t => xs t - x t) 0 = 0 := by simp [hxs.1, hx.1]
  have htel := euler_telescope D (fun t => xs t - x t) hd0 heuler T
  have hterm : ∀ t ∈ Finset.range (T + 1), β ^ t * F (x t, x (t + 1)) ≤
      β ^ t * F (xs t, xs (t + 1)) - β ^ t * D t (xs t - x t, xs (t + 1) - x (t + 1)) :=
    fun t _ => by
      have h := hsup t (x t) (x (t + 1)) (hx.2 t)
      have e : D t ((x t, x (t + 1)) - (xs t, xs (t + 1))) =
          -D t (xs t - x t, xs (t + 1) - x (t + 1)) := by
        rw [← map_neg]; congr 1; ext <;> simp
      rw [e] at h
      have := mul_le_mul_of_nonneg_left h (pow_nonneg hβ t)
      linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, htel] at hsum
  simp only [partialSum]
  have := hwb T
  linarith

/-- **Theorem 4.15 (sufficiency of the Euler and transversality conditions).** Let `E` be
ordered, feasible plans be nonnegative, `F` be concave on the (convex) graph of `Γ` and
differentiable along `x*`, with `F_x ≥ 0` there (from Assumption 4.5). If `x*` satisfies the
Euler equations (2) and the transversality condition (3) `βᵗF_x(x*_t, x*_{t+1})·x*_t → 0`, it is
optimal. -/
theorem theorem_4_15 [PartialOrder E] (h42 : Assumption42 Γ (fun x y => F (x, y)) β)
    (hβ : 0 ≤ β) (hA : ConcaveOn ℝ {p : E × E | p.2 ∈ Γ p.1} F)
    (hpos : ∀ x₀, ∀ x ∈ Feasible Γ x₀, ∀ t, 0 ≤ x t) {x₀ : E} {xs : ℕ → E}
    (hxs : xs ∈ Feasible Γ x₀) (D : ℕ → E × E →L[ℝ] ℝ)
    (hd : ∀ t, HasFDerivAt F (D t) (xs t, xs (t + 1)))
    (hFx : ∀ t v, 0 ≤ v → 0 ≤ Fx (D t) v)
    (heuler : ∀ t v, Fy (D t) v + β * Fx (D (t + 1)) v = 0)
    (htrans : Tendsto (fun t => β ^ t * Fx (D t) (xs t)) atTop (𝓝 0)) :
    total (fun x y => F (x, y)) β xs = vstar Γ (fun x y => F (x, y)) β x₀ := by
  refine euler_sufficient h42 hxs D (fun t x y hy => ?_) heuler hβ fun x hx _ => ?_
  · have := concave_le_fderiv hA (show (xs t, xs (t + 1)) ∈ {p : E × E | p.2 ∈ Γ p.1} from
      hxs.2 t) (show (x, y) ∈ {p : E × E | p.2 ∈ Γ p.1} from hy) (hd t)
    exact this
  · -- the boundary term is at most `βᵀ⁺¹F_x·x*_{T+1}`, which tends to `0`
    refine ⟨fun T => β ^ (T + 1) * Fx (D (T + 1)) (xs (T + 1)),
      htrans.comp (tendsto_add_atTop_nat 1), fun T => ?_⟩
    have hlin : Fx (D (T + 1)) (xs (T + 1) - x (T + 1)) =
        Fx (D (T + 1)) (xs (T + 1)) - Fx (D (T + 1)) (x (T + 1)) := by
      simp only [Fx, ← map_sub, Prod.mk_sub_mk, sub_zero]
    rw [hlin]
    have := hFx (T + 1) (x (T + 1)) (hpos x₀ x hx (T + 1))
    have hb := pow_nonneg hβ (T + 1)
    nlinarith

/-- **p. 100.** If the policy `g` satisfies the first-order condition (4)
`F_y(x, g(x)) + βv′(g(x)) = 0` and the envelope condition (5) `v′(x) = F_x(x, g(x))`, then every
plan generated by `g` satisfies the Euler equations (2). -/
theorem euler_of_envelope {g : E → E} {DF : E → E × E →L[ℝ] ℝ} {Dv : E → E →L[ℝ] ℝ}
    (hfoc : ∀ x v, Fy (DF x) v + β * Dv (g x) v = 0)
    (henv : ∀ x v, Dv x v = Fx (DF x) v) {xs : ℕ → E} (hgen : ∀ t, xs (t + 1) = g (xs t))
    (t : ℕ) (v : E) : Fy (DF (xs t)) v + β * Fx (DF (xs (t + 1))) v = 0 := by
  have := hfoc (xs t) v
  rwa [← hgen t, henv] at this

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The one-sector model of optimal growth

SLP §5.1, pp. 103–105: `max Σ βᵗU[f(x_t) − x_{t+1}]` subject to `0 ≤ x_{t+1} ≤ f(x_t)`, on the
set `X = [0, x̄]` of maintainable capital stocks.

* `GrowthHyp`: (U1)–(U3) and (T1)–(T3) on `X`.
* `growthΓ`, `growthF`: `Γ(x) = [0, f(x)]` and `F(x, y) = U(f(x) − y)` on `X`.
* `growth_assumption43`, `growth_assumption44`, `growth_a45`, `growth_a46` (Ex 5.1a–b):
  Assumptions 4.3–4.6 hold, and with them Assumptions 4.1–4.2 (`growth_assumption41`,
  `growth_assumption42`).
* `ex_5_1ab`: there is a unique bounded continuous `v` satisfying (2). It is `v*`, it is strictly
  increasing, and the policy correspondence is nonempty and u.h.c.
* `growth_a47`, `growth_a48`, `ex_5_1c` (Ex 5.1c): with `U` strictly concave and `f` strictly
  concave, Assumptions 4.7–4.8 hold, `v` is strictly concave and the policy is a continuous
  function. `ex_5_1c_weak_counterexample`: with `f` only weakly concave, as (T4) allows,
  Assumption 4.7 can fail.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

/-- (U1)–(U3) and (T1)–(T3) of SLP §5.1 (p. 104), on `X = [0, x̄]`. The second half of (T2),
`f(x) < x` for `x > x̄`, only explains why the state space can be cut down to `X`; the analysis
on `X` does not use it, and leaving it out lets `f(k) = k` (Section 5.2) fit as well. -/
structure GrowthHyp (U f : ℝ → ℝ) (β xbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  xbar_pos : 0 < xbar
  f_maintain : ∀ x ∈ Icc 0 xbar, x ≤ f x ∧ f x ≤ xbar
  f_mono : StrictMonoOn f (Ici 0)

variable {U f : ℝ → ℝ} {β xbar : ℝ}

/-- `Γ(x) = [0, f(x)]` on `X = [0, x̄]`. -/
def growthΓ (f : ℝ → ℝ) (xbar : ℝ) (x : Icc (0 : ℝ) xbar) : Set (Icc (0 : ℝ) xbar) :=
  {y | y.1 ≤ f x.1}

/-- `F(x, y) = U(f(x) − y)`. -/
def growthF (U f : ℝ → ℝ) (xbar : ℝ) (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar) : ℝ :=
  U (f p.1.1 - p.2.1)

theorem growth_f_nonneg (h : GrowthHyp U f β xbar) (x : Icc (0 : ℝ) xbar) : 0 ≤ f x.1 :=
  x.2.1.trans (h.f_maintain x.1 x.2).1

theorem continuous_growth_f (h : GrowthHyp U f β xbar) :
    Continuous fun x : Icc (0 : ℝ) xbar => f x.1 :=
  h.f_cont.comp_continuous continuous_subtype_val fun x => x.2.1

/-- Assumption 4.3 (Ex 5.1a–b, via Exercise 3.13): `Γ` is nonempty, compact-valued and
continuous. -/
theorem growth_assumption43 (h : GrowthHyp U f β xbar) : Assumption43 (growthΓ f xbar) := by
  have hcf := continuous_growth_f h
  have hclosed : ∀ x, IsClosed (growthΓ f xbar x) := fun x =>
    isClosed_le continuous_subtype_val continuous_const
  refine ⟨fun x => ⟨⟨0, le_rfl, h.xbar_pos.le⟩, growth_f_nonneg h x⟩,
    fun x => (hclosed x).isCompact, fun x => ⟨⟨⟨0, le_rfl, h.xbar_pos.le⟩, growth_f_nonneg h x⟩,
      fun y hy xs hxs => ?_⟩, fun x => ⟨⟨⟨0, le_rfl, h.xbar_pos.le⟩, growth_f_nonneg h x⟩,
      fun xs hxs ys hys => ?_⟩⟩
  · -- l.h.c.: `yₙ = min{y, f(xₙ)}`
    refine ⟨0, fun n => ⟨min y.1 (f (xs n).1), le_min y.2.1 (growth_f_nonneg h _),
      (min_le_left _ _).trans y.2.2⟩,
      fun n _ => show min y.1 (f (xs n).1) ≤ f (xs n).1 from min_le_right _ _, ?_⟩
    have hlim := (tendsto_const_nhds (x := y.1)).min ((hcf.tendsto x).comp hxs)
    rw [min_eq_left hy] at hlim
    exact tendsto_subtype_rng.2 hlim
  · -- u.h.c.: `X` is compact and `{(x, y) : y ≤ f(x)}` is closed
    obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
    refine ⟨y, ?_, φ, hφ, hlim⟩
    exact le_of_tendsto_of_tendsto ((continuous_subtype_val.tendsto y).comp hlim)
      ((hcf.tendsto x).comp (hxs.comp hφ.tendsto_atTop))
      (Eventually.of_forall fun n => hys (φ n))

/-- Assumption 4.4 (Ex 5.1a–b): `F` is bounded and continuous on the graph and `0 < β < 1`. -/
theorem growth_assumption44 (h : GrowthHyp U f β xbar) :
    Assumption44 (growthΓ f xbar) (growthF U f xbar) β := by
  have hcf := continuous_growth_f h
  have hcons : ∀ p ∈ graph (growthΓ f xbar), f p.1.1 - p.2.1 ∈ Icc 0 xbar := fun p hp =>
    ⟨sub_nonneg.2 hp, by linarith [p.2.2.1, (h.f_maintain p.1.1 p.1.2).2]⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.U_cont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) xbar ⊆ Ici 0))
  refine ⟨?_, ⟨B, fun p hp => (Real.norm_eq_abs _).symm.le.trans (hB _ (hcons p hp))⟩,
    h.β_pos, h.β_lt⟩
  refine h.U_cont.comp (((hcf.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).continuousOn) fun p hp => (hcons p hp).1

/-- Assumption 4.5: `F(·, y)` is strictly increasing. -/
theorem growth_a45 (h : GrowthHyp U f β xbar) (x x' y : Icc (0 : ℝ) xbar) (hxx' : x < x')
    (hy : y ∈ growthΓ f xbar x) : growthF U f xbar (x, y) < growthF U f xbar (x', y) := by
  have hfx : f x.1 < f x'.1 := h.f_mono x.2.1 x'.2.1 hxx'
  have hy' : y.1 ≤ f x.1 := hy
  change U (f x.1 - y.1) < U (f x'.1 - y.1)
  exact h.U_mono (show f x.1 - y.1 ∈ Set.Ici 0 from sub_nonneg.2 hy')
    (show f x'.1 - y.1 ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith) (by linarith)

/-- Assumption 4.6: `Γ` is monotone. -/
theorem growth_a46 (h : GrowthHyp U f β xbar) (x x' : Icc (0 : ℝ) xbar) (hxx' : x ≤ x') :
    growthΓ f xbar x ⊆ growthΓ f xbar x' := fun _ hy =>
  hy.trans (h.f_mono.monotoneOn x.2.1 x'.2.1 hxx')

theorem growth_assumption41 (h : GrowthHyp U f β xbar) : Assumption41 (growthΓ f xbar) :=
  (growth_assumption43 h).nonempty

theorem growth_assumption42 (h : GrowthHyp U f β xbar) :
    Assumption42 (growthΓ f xbar) (curryF (growthF U f xbar)) β :=
  assumption42_of_44 (growth_assumption44 h)

/-- **Exercise 5.1a–b.** Under (U1)–(U3) and (T1)–(T3) there is a unique bounded continuous
solution `v` of (2). It is the supremum function of (1), it is strictly increasing, the policy
correspondence `G` is nonempty and u.h.c., and plans generated by `G` are optimal. -/
theorem ex_5_1ab (h : GrowthHyp U f β xbar) :
    ∃ v : Icc (0 : ℝ) xbar →ᵇ ℝ,
      bellman (growth_assumption43 h) (growth_assumption44 h) v = v ∧
      (∀ w, bellman (growth_assumption43 h) (growth_assumption44 h) w = w → w = v) ∧
      (fun x => (v x : EReal)) = vstar (growthΓ f xbar) (curryF (growthF U f xbar)) β ∧
      StrictMono v ∧
      ∀ x, (argmax (obj (growthF U f xbar) β v) (growthΓ f xbar) x).Nonempty ∧
        IsUHC (argmax (obj (growthF U f xbar) β v) (growthΓ f xbar)) x := by
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  obtain ⟨v, hv, huniq, -, hG⟩ := theorem_4_6 (growth_assumption43 h) (growth_assumption44 h)
  exact ⟨v, hv, huniq, fixedPoint_eq_vstar _ _ hv,
    theorem_4_7 _ _ (growth_a45 h) (growth_a46 h) hv, fun x => ⟨(hG x).1, (hG x).2.2⟩⟩

/-! ### Exercise 5.1c: concavity -/

/-- Assumption 4.7 holds when `U` is concave and strictly increasing and `f` is strictly
concave. -/
theorem growth_a47 (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : StrictConcaveOn ℝ (Ici 0) f) :
    Assumption47 (convex_Icc 0 xbar) (growthΓ f xbar) (growthF U f xbar) := by
  intro x y x' y' hy hy' θ h0 h1
  set c := f x.1 - y.1
  set c' := f x'.1 - y'.1
  have hc : 0 ≤ c := sub_nonneg.2 hy
  have hc' : 0 ≤ c' := sub_nonneg.2 hy'
  have h1' : 0 ≤ 1 - θ := by linarith
  -- `θU(c) + (1 − θ)U(c′) ≤ U(θc + (1 − θ)c′)`
  have hUc := hU.2 (mem_Ici.2 hc) (mem_Ici.2 hc') h0.le h1' (by ring)
  simp only [smul_eq_mul] at hUc
  have hcomb : 0 ≤ θ * c + (1 - θ) * c' := by positivity
  have hfw := hf.concaveOn.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) h0.le h1' (by ring)
  simp only [smul_eq_mul] at hfw
  have harg : θ * c + (1 - θ) * c' ≤
      f (θ * x.1 + (1 - θ) * x'.1) - (θ * y.1 + (1 - θ) * y'.1) := by
    simp only [c, c']; linarith
  have hmono : U (θ * c + (1 - θ) * c') ≤ U (f (θ * x.1 + (1 - θ) * x'.1) -
      (θ * y.1 + (1 - θ) * y'.1)) :=
    h.U_mono.monotoneOn (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg)) harg
  simp only [growthF, cmb, smul_eq_mul]
  refine ⟨hUc.trans hmono, fun hne => ?_⟩
  -- `x ≠ x′`: strict concavity of `f` makes the argument strictly larger
  have hne' : x.1 ≠ x'.1 := fun he => hne (Subtype.ext he)
  have hfs : θ * f x.1 + (1 - θ) * f x'.1 < f (θ * x.1 + (1 - θ) * x'.1) := by
    have := hf.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) hne' h0 (show (0 : ℝ) < 1 - θ by linarith)
      (show θ + (1 - θ) = 1 by ring)
    simpa only [smul_eq_mul] using this
  have harg' : θ * c + (1 - θ) * c' <
      f (θ * x.1 + (1 - θ) * x'.1) - (θ * y.1 + (1 - θ) * y'.1) := by
    simp only [c, c']; linarith
  exact hUc.trans_lt (h.U_mono (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg'.le)) harg')

/-- Assumption 4.8 holds when `f` is concave. -/
theorem growth_a48 (hf : ConcaveOn ℝ (Ici 0) f) :
    Assumption48 (convex_Icc 0 xbar) (growthΓ f xbar) := by
  intro x y x' y' hy hy' θ h0 h1
  have hfw := hf.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) h0 (by linarith : 0 ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hfw
  change θ * y.1 + (1 - θ) * y'.1 ≤ f (θ * x.1 + (1 - θ) * x'.1)
  have : (0 : ℝ) ≤ 1 - θ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (show y.1 ≤ f x.1 from hy) h0,
    mul_le_mul_of_nonneg_left (show y'.1 ≤ f x'.1 from hy') this]

/-- **Exercise 5.1c.** With `U` strictly concave (U4) and `f` strictly concave, `v` is strictly
concave and the optimal policy is a continuous function. -/
theorem ex_5_1c [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : StrictConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v) ∧
      Continuous (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v)) := by
  obtain ⟨h1, h2, -, h4⟩ := theorem_4_8 (growth_assumption43 h) (growth_assumption44 h)
    (growth_a47 h hU.concaveOn hf) (growth_a48 hf.concaveOn) hv
  exact ⟨h1, h2, h4⟩

/-- **Exercise 5.1c with a weakly concave `f`.** (T4) only asks `f` to be weakly concave, and
then Assumption 4.7 can fail. Take `x̄ = 2`, `f(k) = min{2k, 1 + k/2}` and `U(c) = √c`; these
satisfy (T2)–(T4) and (U2)–(U4). The points `(0.1, 0.1)` and `(0.2, 0.3)` give the same
consumption `0.1`, and `f` is linear between `0.1` and `0.2`. So
`F(θ(x, y) + (1 − θ)(x′, y′)) = θF(x, y) + (1 − θ)F(x′, y′)` with `x ≠ x′`. -/
theorem ex_5_1c_weak_counterexample :
    let f : ℝ → ℝ := fun k => min (2 * k) (1 + k / 2)
    let U : ℝ → ℝ := fun c => √c
    (f 0 = 0 ∧ (∀ x ∈ Icc (0 : ℝ) 2, x ≤ f x ∧ f x ≤ 2) ∧ (∀ x, 2 < x → f x < x) ∧
      StrictMonoOn f (Ici 0) ∧ ConcaveOn ℝ (Ici 0) f) ∧
    (StrictMonoOn U (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) U) ∧
    ¬ Assumption47 (convex_Icc 0 2) (growthΓ f 2) (growthF U f 2) := by
  intro f U
  refine ⟨⟨by simp [f], fun x hx => ⟨?_, ?_⟩, fun x hx => ?_, fun a _ b _ hab => ?_, ?_⟩,
    ⟨fun a ha b _ hab => Real.sqrt_lt_sqrt ha hab, Real.strictConcaveOn_sqrt⟩, fun h47 => ?_⟩
  · simp only [f, le_min_iff]; constructor <;> linarith [hx.1, hx.2]
  · exact (min_le_right _ _).trans (by linarith [hx.2])
  · exact (min_le_right _ _).trans_lt (by linarith)
  · simp only [f]
    rcases le_total (2 * a) (1 + a / 2) with h1 | h1 <;>
      rcases le_total (2 * b) (1 + b / 2) with h2 | h2 <;>
      simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith
  · exact (concaveOn_id (convex_Ici 0) |>.smul (by norm_num : (0 : ℝ) ≤ 2)).inf
      ((concaveOn_const 1 (convex_Ici 0)).add ((concaveOn_id (convex_Ici 0)).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 2))) |>.congr fun x _ => by
          simp only [f, Pi.inf_apply, smul_eq_mul, id, Pi.add_apply]; ring_nf
  · set x : Icc (0 : ℝ) 2 := ⟨0.1, by norm_num, by norm_num⟩
    set x' : Icc (0 : ℝ) 2 := ⟨0.2, by norm_num, by norm_num⟩
    set y : Icc (0 : ℝ) 2 := ⟨0.1, by norm_num, by norm_num⟩
    set y' : Icc (0 : ℝ) 2 := ⟨0.3, by norm_num, by norm_num⟩
    have hy : y ∈ growthΓ f 2 x := by
      change (0.1 : ℝ) ≤ min (2 * 0.1) (1 + 0.1 / 2); norm_num
    have hy' : y' ∈ growthΓ f 2 x' := by
      change (0.3 : ℝ) ≤ min (2 * 0.2) (1 + 0.2 / 2); norm_num
    have hne : x ≠ x' := fun he => by
      have := congrArg Subtype.val he; norm_num [x, x'] at this
    have := (h47 x y x' y' hy hy' (1 / 2) (by norm_num) (by norm_num)).2 hne
    simp only [growthF, cmb, U, f, smul_eq_mul, x, x', y, y'] at this
    norm_num at this
    linarith

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 5.1c with a weakly concave technology

SLP §5.1, p. 104: Exercise 5.1c asks to show that under (U1)–(U4) and (T1)–(T4) the hypotheses
of Theorem 4.8 hold. They do not: with `f` only weakly concave, Assumption 4.7 can fail
(`ex_5_1c_weak_counterexample`). The conclusions of Theorem 4.8 nevertheless hold, and this
module proves them directly.

* `growthF_concave`: `F(x, y) = U(f(x) − y)` is concave on the graph (the weak half of
  Assumption 4.7), and `bellman_concave_growth`: `T` preserves concavity, so `v` is concave
  (`growth_concave`).
* `chord_step`: if `v` is affine along the chord between `a ≠ a'`, then the optimal
  consumptions at `a` and `a'` are equal (strict concavity of `U`), the optimal savings
  `b ≠ b'` again give an affine chord, and `v(a) − v(a') = β(v(b) − v(b'))`.
* `growth_strictConcave`: iterating, `v(x) − v(x') = βⁿ(v(bₙ) − v(bₙ'))` for every `n`, so
  `v(x) = v(x')`; this contradicts strict monotonicity. Hence `v` is strictly concave.
* `ex_5_1c_weak`: under (U1)–(U4) and (T1)–(T4), `v` is strictly concave and the optimal policy
  is a continuous function, as the book claims.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {U f : ℝ → ℝ} {β xbar : ℝ}

/-- `F(x, y) = U(f(x) − y)` is concave on the graph when `U` is concave and `f` is concave. -/
theorem growthF_concave (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {x y x' y' : Icc (0 : ℝ) xbar} (hy : y ∈ growthΓ f xbar x)
    (hy' : y' ∈ growthΓ f xbar x') {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * growthF U f xbar (x, y) + (1 - θ) * growthF U f xbar (x', y') ≤
      growthF U f xbar (cmb (convex_Icc 0 xbar) h0 h1 x x',
        cmb (convex_Icc 0 xbar) h0 h1 y y') := by
  set c := f x.1 - y.1
  set c' := f x'.1 - y'.1
  have hc : 0 ≤ c := sub_nonneg.2 hy
  have hc' : 0 ≤ c' := sub_nonneg.2 hy'
  have h1' : 0 ≤ 1 - θ := by linarith
  have hUc := hU.2 (mem_Ici.2 hc) (mem_Ici.2 hc') h0 h1' (by ring)
  simp only [smul_eq_mul] at hUc
  have hcomb : 0 ≤ θ * c + (1 - θ) * c' := by positivity
  have hfw := hf.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) h0 h1' (by ring)
  simp only [smul_eq_mul] at hfw
  have harg : θ * c + (1 - θ) * c' ≤
      f (θ * x.1 + (1 - θ) * x'.1) - (θ * y.1 + (1 - θ) * y'.1) := by
    simp only [c, c']; linarith
  have hmono := h.U_mono.monotoneOn (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg)) harg
  simp only [growthF, cmb, smul_eq_mul]
  exact hUc.trans hmono

/-- `T` preserves concavity when `U` and `f` are concave. -/
theorem bellman_concave_growth (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {g : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hg : IsConcaveS (convex_Icc 0 xbar) g) :
    IsConcaveS (convex_Icc 0 xbar)
      (bellman (growth_assumption43 h) (growth_assumption44 h) g) := by
  intro x x' θ h0 h1
  obtain ⟨y, hy, hyv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) g x
  obtain ⟨y', hy', hyv', -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) g x'
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax (growth_assumption43 h)
    (growth_assumption44 h) g (cmb (convex_Icc 0 xbar) h0 h1 x x')
  have hm := hmax _ (growth_a48 hf x y x' y' hy hy' θ h0 h1)
  have hF := growthF_concave h hU hf hy hy' h0 h1
  have hgc := mul_le_mul_of_nonneg_left (hg y y' θ h0 h1) h.β_pos.le
  rw [hyv, hyv']
  nlinarith

/-- With `U` and `f` concave the fixed point `v` is concave. -/
theorem growth_concave (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsConcaveS (convex_Icc 0 xbar) v :=
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  (corollary_1 (S' := {g | IsConcaveS (convex_Icc 0 xbar) g})
    (S'' := {g | IsConcaveS (convex_Icc 0 xbar) g})
    (bellman_contraction (growth_assumption43 h) (growth_assumption44 h)) hv
    ⟨0, fun x x' θ _ _ => by simp⟩ (isClosed_concave _)
    (fun _ hg => bellman_concave_growth h hU hf hg)
    (fun _ hg => bellman_concave_growth h hU hf hg)).1

/-- **The chord step.** If `v` is affine along the chord between `a ≠ a'`, so is it between the
optimal savings `b ≠ b'`, and `v(a) − v(a') = β(v(b) − v(b'))`. -/
theorem chord_step (h : GrowthHyp U f β xbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hvc : IsConcaveS (convex_Icc 0 xbar) v) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    {a a' : Icc (0 : ℝ) xbar} (hne : a ≠ a')
    (hchord : v (cmb (convex_Icc 0 xbar) h0.le h1.le a a') ≤ θ * v a + (1 - θ) * v a') :
    ∃ b b' : Icc (0 : ℝ) xbar, b ≠ b' ∧
      v (cmb (convex_Icc 0 xbar) h0.le h1.le b b') ≤ θ * v b + (1 - θ) * v b' ∧
      v a - v a' = β * (v b - v b') := by
  obtain ⟨b, hb, hbv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v a
  obtain ⟨b', hb', hbv', -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v a'
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax (growth_assumption43 h)
    (growth_assumption44 h) v (cmb (convex_Icc 0 xbar) h0.le h1.le a a')
  rw [hv] at hbv hbv' hmax
  have hm := hmax _ (growth_a48 hf a b a' b' hb hb' θ h0.le h1.le)
  have hF := growthF_concave h hU.concaveOn hf hb hb' h0.le h1.le
  have hvb := mul_le_mul_of_nonneg_left (hvc b b' θ h0.le h1.le) h.β_pos.le
  have e : θ * v a + (1 - θ) * v a' = θ * growthF U f xbar (a, b) +
      (1 - θ) * growthF U f xbar (a', b') + β * (θ * v b + (1 - θ) * v b') := by
    rw [hbv, hbv']; ring
  have hb₁ : b.1 ≤ f a.1 := hb
  have hb₁' : b'.1 ≤ f a'.1 := hb'
  -- equal consumption, by strict concavity of `U`
  have hcc : f a.1 - b.1 = f a'.1 - b'.1 := by
    by_contra hcne
    have hc0 : 0 ≤ f a.1 - b.1 := sub_nonneg.2 hb
    have hc0' : 0 ≤ f a'.1 - b'.1 := sub_nonneg.2 hb'
    have hs := hU.2 (mem_Ici.2 hc0) (mem_Ici.2 hc0') hcne h0
      (show (0 : ℝ) < 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
    simp only [smul_eq_mul] at hs
    have hfw := hf.2 (mem_Ici.2 a.2.1) (mem_Ici.2 a'.2.1) h0.le
      (show (0 : ℝ) ≤ 1 - θ by linarith) (by ring)
    simp only [smul_eq_mul] at hfw
    have hcomb : 0 ≤ θ * (f a.1 - b.1) + (1 - θ) * (f a'.1 - b'.1) := by
      have : (0 : ℝ) ≤ 1 - θ := by linarith
      positivity
    have harg : θ * (f a.1 - b.1) + (1 - θ) * (f a'.1 - b'.1) ≤
        f (θ * a.1 + (1 - θ) * a'.1) - (θ * b.1 + (1 - θ) * b'.1) := by linarith
    have hmono := h.U_mono.monotoneOn (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg)) harg
    have hFc : growthF U f xbar (cmb (convex_Icc 0 xbar) h0.le h1.le a a',
        cmb (convex_Icc 0 xbar) h0.le h1.le b b') =
        U (f (θ * a.1 + (1 - θ) * a'.1) - (θ * b.1 + (1 - θ) * b'.1)) := by
      simp [growthF, cmb]
    simp only [growthF] at e
    rw [hFc] at hm
    linarith
  refine ⟨b, b', fun heq => hne (Subtype.ext ?_), ?_, ?_⟩
  · have hfe : f a.1 = f a'.1 := by rw [heq] at hcc; linarith
    exact h.f_mono.injOn (mem_Ici.2 a.2.1) (mem_Ici.2 a'.2.1) hfe
  · refine le_of_mul_le_mul_left ?_ h.β_pos
    linarith
  · have hFe : growthF U f xbar (a, b) = growthF U f xbar (a', b') := by
      simp only [growthF]; rw [hcc]
    rw [hbv, hbv', hFe]; ring

/-- Under (U1)–(U4) and (T1)–(T4) the fixed point `v` is strictly concave. -/
theorem growth_strictConcave (h : GrowthHyp U f β xbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v := by
  have hvc := growth_concave h hU.concaveOn hf hv
  have hvm : StrictMono v := by
    obtain ⟨u, -, huniq, -, hmono, -⟩ := ex_5_1ab h
    rw [huniq v hv]
    exact hmono
  intro x x' hne θ h0 h1
  by_contra hle
  push Not at hle
  -- the chord stays affine along the optimal paths
  have hiter : ∀ n : ℕ, ∃ b b' : Icc (0 : ℝ) xbar, b ≠ b' ∧
      v (cmb (convex_Icc 0 xbar) h0.le h1.le b b') ≤ θ * v b + (1 - θ) * v b' ∧
      v x - v x' = β ^ n * (v b - v b') := by
    intro n
    induction n with
    | zero => exact ⟨x, x', hne, hle, by ring⟩
    | succ n ih =>
      obtain ⟨b, b', hbb, hch, he⟩ := ih
      obtain ⟨c, c', hcc, hch', he'⟩ := chord_step h hU hf hv hvc h0 h1 hbb hch
      exact ⟨c, c', hcc, hch', by rw [he, he']; ring⟩
  -- so `|v(x) − v(x')| ≤ 2βⁿ‖v‖ → 0`
  have hbound : ∀ n : ℕ, |v x - v x'| ≤ β ^ n * (2 * ‖v‖) := fun n => by
    obtain ⟨b, b', -, -, he⟩ := hiter n
    rw [he, abs_mul, abs_of_nonneg (pow_nonneg h.β_pos.le n)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h.β_pos.le n)
    have := v.norm_coe_le_norm b
    have := v.norm_coe_le_norm b'
    rw [Real.norm_eq_abs] at *
    linarith [abs_sub (v b) (v b')]
  have hlim : Tendsto (fun n : ℕ => β ^ n * (2 * ‖v‖)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).mul_const (2 * ‖v‖)
  have hzero : |v x - v x'| ≤ 0 := ge_of_tendsto' hlim hbound
  have heq : v x = v x' := sub_eq_zero.1 (abs_nonpos_iff.1 hzero)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (hvm hlt).ne heq
  · exact (hvm hlt).ne heq.symm

/-- **Exercise 5.1c, as the book states it.** Under (U1)–(U4) and (T1)–(T4), with `f` only
weakly concave, `v` is strictly concave, the policy correspondence is single-valued and the
policy function is continuous, although Assumption 4.7 can fail. -/
theorem ex_5_1c_weak [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v) ∧
      Continuous (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v)) := by
  have hvs := growth_strictConcave h hU hf hv
  have h43 := growth_assumption43 h
  have huniq : ∀ x, ∀ y₁ ∈ argmax (obj (growthF U f xbar) β v) (growthΓ f xbar) x,
      ∀ y₂ ∈ argmax (obj (growthF U f xbar) β v) (growthΓ f xbar) x, y₁ = y₂ := by
    intro x y₁ hy₁ y₂ hy₂
    by_contra hne
    have hh : (0 : ℝ) < 1 / 2 := by norm_num
    have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
    have hmem := growth_a48 (xbar := xbar) hf x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh.le hh1.le
    rw [cmb_self] at hmem
    have hF := growthF_concave h hU.concaveOn hf hy₁.1 hy₂.1 hh.le hh1.le
    rw [cmb_self] at hF
    have hvs' := mul_lt_mul_of_pos_left (hvs y₁ y₂ hne (1 / 2) hh hh1) h.β_pos
    have hle := le_maxValue (continuousOn_obj (growth_assumption44 h) v.continuous)
      (h43.compact x) hmem
    have e1 := hy₁.2
    have e2 := hy₂.2
    simp only [obj] at hle e1 e2
    linarith
  have hUA : UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v) :=
    ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc,
      continuousOn_obj (growth_assumption44 h) v.continuous, huniq⟩
  exact ⟨hvs, hUA, hUA.continuous_argmaxFn⟩

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Differentiability and interior policies in the growth model

SLP Exercise 5.1d, pp. 104–105. In the setting of Exercise 5.1c (`U` and `f` strictly concave):

* `liftR`, `concaveOn_liftR`: `v` extended by zero to `ℝ` is concave on `[0, x̄]`.
* `ex_5_1d`: if `g(x) < f(x)` at an interior `x`, with `U` differentiable at `f(x) − g(x)` and `f`
  differentiable at `x`, then `v′(x) = U′(f(x) − g(x)) f′(x)` (Theorem 4.10). Only `g(x) < f(x)`
  is used, not `g(x) > 0`.
* `ex_5_1d_interior`: if `U′(c) → ∞` as `c ↓ 0`, then `0 < g(x) < f(x)` for every `x > 0`.
  Zero consumption is not optimal, because the first unit of consumption has unbounded marginal
  utility while `v` has bounded slopes. Zero saving is not optimal for the same reason applied to
  `v(ε) − v(0) ≥ U(f(ε)) − U(0)`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {U f : ℝ → ℝ} {β xbar : ℝ}

/-- `v` on `[0, x̄]` extended by zero to `ℝ`. -/
noncomputable def liftR (xbar : ℝ) (v : Icc (0 : ℝ) xbar → ℝ) (x : ℝ) : ℝ := by
  classical exact if hx : x ∈ Icc 0 xbar then v ⟨x, hx⟩ else 0

theorem liftR_of_mem (v : Icc (0 : ℝ) xbar → ℝ) {x : ℝ} (hx : x ∈ Icc 0 xbar) :
    liftR xbar v x = v ⟨x, hx⟩ := by
  simp only [liftR, hx, ↓reduceDIte]

theorem concaveOn_liftR {v : Icc (0 : ℝ) xbar → ℝ} (hv : IsStrictConcaveS (convex_Icc 0 xbar) v) :
    ConcaveOn ℝ (Icc 0 xbar) (liftR xbar v) := by
  refine ⟨convex_Icc 0 xbar, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have hmem : a • x + b • y ∈ Icc (0 : ℝ) xbar := convex_Icc 0 xbar hx hy ha hb hab
  rw [liftR_of_mem v hx, liftR_of_mem v hy, liftR_of_mem v hmem, smul_eq_mul, smul_eq_mul]
  subst hb'
  rcases eq_or_ne x y with rfl | hne
  · have : a • x + (1 - a) • x = x := by rw [← add_smul]; simp
    simp only [this]; ring_nf; rfl
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases (show a ≤ 1 by linarith).eq_or_lt with rfl | ha1
  · simp
  exact (hv ⟨x, hx⟩ ⟨y, hy⟩ (fun he => hne (congrArg Subtype.val he)) a ha' ha1).le

/-- **Exercise 5.1d (differentiability).** If `g(x₀) < f(x₀)` at `x₀ ∈ (0, x̄)`, `U` has derivative
`U′` at `f(x₀) − g(x₀)` and `f` has derivative `f′` at `x₀`, then `v′(x₀) = U′ f′`. -/
theorem ex_5_1d [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x₀ : Icc (0 : ℝ) xbar}
    (hx₀ : x₀.1 ∈ Ioo 0 xbar)
    (hgf : (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x₀).1 < f x₀.1)
    {U' f' : ℝ}
    (hU' : HasDerivAt U U' (f x₀.1 - (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x₀).1))
    (hf' : HasDerivAt f f' x₀.1) : HasDerivAt (liftR xbar v) (U' * f') x₀.1 := by
  obtain ⟨hvc, hUA, -⟩ := ex_5_1c_weak h hU hf hv
  set g₀ := argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x₀
  have hX : Icc (0 : ℝ) xbar ∈ 𝓝 x₀.1 := Icc_mem_nhds hx₀.1 hx₀.2
  set W : ℝ → ℝ := fun x => U (f x - g₀.1) + β * v g₀
  have hW : HasDerivAt W (U' * f') x₀.1 := (hU'.comp x₀.1 (hf'.sub_const g₀.1)).add_const _
  have hvx : ∀ x, v x = maxValue (obj (growthF U f xbar) β v) (growthΓ f xbar) x := fun x => by
    rw [← bellman_apply (growth_assumption43 h) (growth_assumption44 h), hv]
  have heq : W x₀.1 = liftR xbar v x₀.1 := by
    rw [liftR_of_mem v x₀.2, Subtype.coe_eta, hvx x₀]
    exact (hUA.argmaxFn_mem x₀).2
  -- for `x` near `x₀`, `g₀ ≤ f(x)`, so `W(x) ≤ v(x)`
  have hfc : ContinuousAt f x₀.1 := hf'.continuousAt
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftR xbar v x := by
    filter_upwards [hX, hfc.eventually (lt_mem_nhds hgf)] with x hx hfx
    rw [liftR_of_mem v hx, hvx]
    exact le_maxValue (z := g₀) (continuousOn_obj (growth_assumption44 h) v.continuous)
      ((growth_assumption43 h).compact _) (show g₀ ∈ growthΓ f xbar ⟨x, hx⟩ from hfx.le)
  have := (theorem_4_10 (concaveOn_liftR hvc) hX hW.hasFDerivAt heq hle).hasDerivAt
  simpa using this

/-- Marginal utility tends to infinity at zero: for every `M`, `U(c) − U(0) ≥ Mc` for small
`c > 0` (the tangent line at `c` lies above `U(0)`). -/
theorem eventually_slope_ge (hU : ConcaveOn ℝ (Ici 0) U)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hinada : Tendsto (deriv U) (𝓝[>] 0) atTop)
    (M : ℝ) : ∀ᶠ c in 𝓝[>] (0 : ℝ), M * c ≤ U c - U 0 := by
  filter_upwards [hinada.eventually (eventually_ge_atTop M), self_mem_nhdsWithin] with c hc hc0
  have htan := concave_le_fderiv hU (z₀ := c) (z := 0) (mem_Ici.2 (le_of_lt hc0))
    (mem_Ici.2 le_rfl) ((hUd c hc0).hasDerivAt.hasFDerivAt)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, zero_sub] at htan
  have hc0' : (0 : ℝ) < c := hc0
  nlinarith

/-- A concave function on `[0, x̄]` has its left difference quotients at `a` bounded by its chord
slope over `[0, a/2]`, for steps `ε < a/2`. -/
theorem slope_le_chord {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {a ε : ℝ}
    (h0 : (0 : ℝ) ∈ s) (ha : a ∈ s) (hε0 : 0 < ε) (hε : ε < a / 2) :
    φ a - φ (a - ε) ≤ ε * ((φ (a / 2) - φ 0) / (a / 2)) := by
  have hs : Icc 0 a ⊆ s := hφ.1.ordConnected.out h0 ha
  have h1 := hφ.slope_anti_adjacent (x := a / 2) (y := a - ε) (z := a)
    (hs ⟨by linarith, by linarith⟩) ha (by linarith) (by linarith)
  have h2 := hφ.slope_anti_adjacent (x := 0) (y := a / 2) (z := a - ε) h0
    (hs ⟨by linarith, by linarith⟩) (by linarith) (by linarith)
  rw [sub_zero] at h2
  have e : a - (a - ε) = ε := by ring
  have h1' : (φ a - φ (a - ε)) / ε ≤ (φ (a - ε) - φ (a / 2)) / (a - ε - a / 2) := by
    simpa only [e] using h1
  rw [div_le_iff₀ hε0] at h1'
  calc φ a - φ (a - ε) ≤ (φ (a - ε) - φ (a / 2)) / (a - ε - a / 2) * ε := h1'
    _ ≤ (φ (a / 2) - φ 0) / (a / 2) * ε := mul_le_mul_of_nonneg_right h2 hε0.le
    _ = ε * ((φ (a / 2) - φ 0) / (a / 2)) := mul_comm _ _

/-- **Exercise 5.1d (interior policies).** If `U` is differentiable on `(0, ∞)` with
`U′(c) → ∞` as `c ↓ 0`, then `0 < g(x) < f(x)` for every `x ∈ (0, x̄]`. -/
theorem ex_5_1d_interior [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hinada : Tendsto (deriv U) (𝓝[>] 0) atTop)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x : Icc (0 : ℝ) xbar}
    (hx : 0 < x.1) :
    0 < (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x).1 ∧
      (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x).1 < f x.1 := by
  obtain ⟨hvc, hUA, -⟩ := ex_5_1c_weak h hU hf hv
  set g := argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x
  have hg := hUA.argmaxFn_mem x
  have hgΓ : g.1 ≤ f x.1 := hg.1
  have hvx : ∀ z, v z = maxValue (obj (growthF U f xbar) β v) (growthΓ f xbar) z := fun z => by
    rw [← bellman_apply (growth_assumption43 h) (growth_assumption44 h), hv]
  have hcont := continuousOn_obj (growth_assumption44 h) v.continuous
  -- any `y ≤ f(x)` gives `F(x, y) + βv(y) ≤ F(x, g) + βv(g)`
  have hopt : ∀ y : Icc (0 : ℝ) xbar, y.1 ≤ f x.1 →
      U (f x.1 - y.1) + β * v y ≤ U (f x.1 - g.1) + β * v g := fun y hy => by
    have h1 := le_maxValue hcont ((growth_assumption43 h).compact x) (show y ∈ growthΓ f xbar x
      from hy)
    rw [← hg.2] at h1
    exact h1
  have hfx : x.1 ≤ f x.1 := (h.f_maintain x.1 x.2).1
  have hfxb : f x.1 ≤ xbar := (h.f_maintain x.1 x.2).2
  have hfpos : 0 < f x.1 := hx.trans_le hfx
  have hβ := h.β_pos
  have hconcV := concaveOn_liftR hvc
  have hU0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.2 le_rfl
  constructor
  · -- `g(x) > 0`
    by_contra hg0
    have hg0' : g.1 = 0 := le_antisymm (not_lt.1 hg0) g.2.1
    -- `v(0) = U(0) + βv(0)`
    set z₀ : Icc (0 : ℝ) xbar := ⟨0, le_rfl, h.xbar_pos.le⟩
    have hv0 : v z₀ = U 0 + β * v z₀ := by
      obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax (growth_assumption43 h)
        (growth_assumption44 h) v z₀
      have hy0 : y = z₀ := Subtype.ext (le_antisymm (by
        have : y.1 ≤ f 0 := hy; rwa [h.f_zero] at this) y.2.1)
      rw [hv] at hval
      have hF0 : growthF U f xbar (z₀, z₀) = U 0 := by simp [growthF, z₀, h.f_zero]
      rw [hy0, hF0] at hval
      exact hval
    -- the chord bound for `U` near `f(x)`
    set K := (U (f x.1 / 2) - U 0) / (f x.1 / 2)
    have hfc0 : ContinuousWithinAt f (Ici 0) 0 := h.f_cont 0 (mem_Ici.2 le_rfl)
    -- choose `ε` with `U(f(ε)) − U(0) ≥ ((K + 1)/β) f(ε)` and `f(ε)` small
    have hslope := eventually_slope_ge hU.concaveOn hUd hinada ((K + 1) / β)
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hslope)
    obtain ⟨η, hη, hηf⟩ := Metric.continuousWithinAt_iff.1 hfc0 δ hδ
    set ε := min (min (η / 2) (f x.1 / 4)) (x.1 / 2)
    have hε0 : 0 < ε := by positivity
    have hεη : ε < η := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hη))
    have hεf : ε < f x.1 / 2 := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt
      (by linarith))
    have hεx : ε ≤ x.1 := (min_le_right _ _).trans (by linarith)
    set e : Icc (0 : ℝ) xbar := ⟨ε, hε0.le, hεx.trans x.2.2⟩
    -- `f(ε)` is small and at least `ε`
    have hfe : ε ≤ f ε := (h.f_maintain ε e.2).1
    have hfeδ : f ε < δ := by
      have := hηf (mem_Ici.2 hε0.le) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε0]; exact hεη)
      rw [h.f_zero, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    have hsl := hδs (by rw [Real.dist_eq, sub_zero, abs_of_pos (hε0.trans_le hfe)]; exact hfeδ)
      (show (0 : ℝ) < f ε from hε0.trans_le hfe)
    -- `v(ε) ≥ U(f(ε)) + βv(0)`
    have hve : U (f ε) + β * v z₀ ≤ v e := by
      rw [hvx e]
      have := le_maxValue hcont ((growth_assumption43 h).compact e)
        (show z₀ ∈ growthΓ f xbar e from (show (0 : ℝ) ≤ f ε by linarith))
      simpa [obj, growthF, z₀] using this
    -- optimality of `g = 0` against `ε`
    have hopt' := hopt e (by linarith)
    rw [hg0', sub_zero] at hopt'
    have hgz : g = z₀ := Subtype.ext hg0'
    rw [hgz] at hopt'
    have hUc := slope_le_chord hU.concaveOn hU0 (mem_Ici.2 hfpos.le) hε0 hεf
    have hK0 : 0 ≤ K := by
      have hm : U 0 ≤ U (f x.1 / 2) :=
        h.U_mono.monotoneOn hU0 (mem_Ici.2 (half_pos hfpos).le) (half_pos hfpos).le
      exact div_nonneg (by linarith) (half_pos hfpos).le
    have hKb : 0 ≤ (K + 1) / β := div_nonneg (by linarith) hβ.le
    have h1 : (K + 1) / β * ε ≤ U (f ε) - U 0 :=
      (mul_le_mul_of_nonneg_left hfe hKb).trans hsl
    have he : (e : ℝ) = ε := rfl
    rw [he] at hopt'
    have hdiff : U (f ε) - U 0 ≤ v e - v z₀ := by linarith
    have h2' := mul_le_mul_of_nonneg_left hdiff hβ.le
    have h2 : β * (U (f ε) - U 0) ≤ ε * K := by
      have : β * (v e - v z₀) ≤ U (f x.1) - U (f x.1 - ε) := by linarith
      have hUc' : U (f x.1) - U (f x.1 - ε) ≤ ε * K := hUc
      linarith
    have h3 : β * ((K + 1) / β * ε) = (K + 1) * ε := by field_simp
    nlinarith
  · -- `g(x) < f(x)`
    by_contra hgf
    have hga : g.1 = f x.1 := le_antisymm hgΓ (not_lt.1 hgf)
    set a := f x.1
    set Kv := (liftR xbar v (a / 2) - liftR xbar v 0) / (a / 2)
    have hslope := eventually_slope_ge hU.concaveOn hUd hinada (β * Kv + 1)
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hslope)
    set ε := min (δ / 2) (a / 4)
    have hε0 : 0 < ε := by positivity
    have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hεa : ε < a / 2 := (min_le_right _ _).trans_lt (by linarith)
    have hsl := hδs (by rw [Real.dist_eq, sub_zero, abs_of_pos hε0]; exact hεδ) hε0
    set y : Icc (0 : ℝ) xbar := ⟨a - ε, by linarith, by linarith⟩
    have hopt' := hopt y (by change a - ε ≤ a; linarith)
    rw [hga, show a - (a - ε) = ε by ring, sub_self] at hopt'
    have hvc' := slope_le_chord hconcV (show (0 : ℝ) ∈ Icc 0 xbar from ⟨le_rfl,
      h.xbar_pos.le⟩) (show a ∈ Icc 0 xbar from ⟨hfpos.le, hfxb⟩) hε0 hεa
    rw [liftR_of_mem v (show a ∈ Icc 0 xbar from ⟨hfpos.le, hfxb⟩),
      liftR_of_mem v (show a - ε ∈ Icc 0 xbar from ⟨by linarith, by linarith⟩)] at hvc'
    have hgeq : g = ⟨a, hfpos.le, hfxb⟩ := Subtype.ext hga
    rw [hgeq] at hopt'
    have h1 : β * (v ⟨a, hfpos.le, hfxb⟩ - v ⟨a - ε, by linarith, by linarith⟩) ≤
        β * (ε * Kv) := mul_le_mul_of_nonneg_left hvc' hβ.le
    nlinarith

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 5.1e: saving rises with the discount factor

SLP §5.1, p. 105: writing `g(x, β)` for the policy function, `g(x, β)` is increasing in `β`.

The manual iterates `T_{β'}` from `v(·, β)` and argues from first-order conditions that the
policies `g_k` rise with `k`; that step needs more than it states. Here the argument is a lattice
(Topkis) argument and needs neither interior solutions nor differentiability.

* `concave_exchange`: for concave `φ`, `p ≤ q` and `δ ≥ 0`,
  `φ(p) + φ(q + δ) ≤ φ(q) + φ(p + δ)`. With `U` concave and `f` increasing this makes
  `U(f(x) − y)` have increasing differences in `(x, y)`.
* `bellman_sub_monotone`: if `β'a − βb` is nondecreasing, so is `T_{β'}a − T_βb`.
* `discounted_value_monotone`: `β'v(·, β') − βv(·, β)` is nondecreasing for `β ≤ β'` (iterate
  `T_{β'}` from `v(·, β)` and pass to the limit).
* `policy_le_of_discount_le`: every optimal choice under `β'` is at least the unique optimal
  choice under `β`; `ex_5_1e`: `g(x, β) ≤ g(x, β')` under the hypotheses of Exercise 5.1c.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {U f : ℝ → ℝ} {β β' xbar : ℝ}

/-- For concave `φ`, moving `δ` from the larger point to the smaller one raises the sum:
`φ(p) + φ(q + δ) ≤ φ(q) + φ(p + δ)` when `p ≤ q`, `0 ≤ δ`. -/
theorem concave_exchange {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {p q δ : ℝ}
    (hp : p ∈ s) (hqδ : q + δ ∈ s) (hpq : p ≤ q) (hδ : 0 ≤ δ) :
    φ p + φ (q + δ) ≤ φ q + φ (p + δ) := by
  rcases eq_or_lt_of_le (add_nonneg (sub_nonneg.2 hpq) hδ) with hL | hL
  · have hq : q = p := by linarith
    have hδ0 : δ = 0 := by linarith
    subst hq hδ0
    simp
  set L := q - p + δ
  set t := δ / L
  have ht0 : 0 ≤ t := div_nonneg hδ hL.le
  have ht1 : t ≤ 1 := (div_le_one hL).2 (by linarith)
  have hLne : L ≠ 0 := hL.ne'
  have h1 := hφ.2 hp hqδ ht0 (sub_nonneg.2 ht1) (by ring)
  have h2 := hφ.2 hp hqδ (sub_nonneg.2 ht1) ht0 (by ring)
  have htL : t * (q - p + δ) = δ := div_mul_cancel₀ δ hLne
  have e1 : t • p + (1 - t) • (q + δ) = q := by
    simp only [smul_eq_mul]; linear_combination (-1 : ℝ) * htL
  have e2 : (1 - t) • p + t • (q + δ) = p + δ := by
    simp only [smul_eq_mul]; linear_combination htL
  rw [e1] at h1
  rw [e2] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- `U(f(x) − y)` has increasing differences: for `x₁ ≤ x₂` and `y₁ ≤ y₂ ≤ f(x₁)`,
`F(x₂, y₂) + F(x₁, y₁) ≥ F(x₁, y₂) + F(x₂, y₁)`. -/
theorem growthF_increasingDiff (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    {x₁ x₂ y₁ y₂ : Icc (0 : ℝ) xbar} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) (hy₂ : y₂.1 ≤ f x₁.1) :
    growthF U f xbar (x₁, y₂) + growthF U f xbar (x₂, y₁) ≤
      growthF U f xbar (x₂, y₂) + growthF U f xbar (x₁, y₁) := by
  have hf : f x₁.1 ≤ f x₂.1 := h.f_mono.monotoneOn (mem_Ici.2 x₁.2.1) (mem_Ici.2 x₂.2.1) hx
  have hy' : y₁.1 ≤ y₂.1 := hy
  have := concave_exchange hU (p := f x₁.1 - y₂.1) (q := f x₂.1 - y₂.1) (δ := y₂.1 - y₁.1)
    (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith [y₁.2.1])) (by linarith) (by linarith)
  simp only [growthF]
  rw [show f x₂.1 - y₂.1 + (y₂.1 - y₁.1) = f x₂.1 - y₁.1 by ring,
    show f x₁.1 - y₂.1 + (y₂.1 - y₁.1) = f x₁.1 - y₁.1 by ring] at this
  linarith

/-- **The lattice step.** If `y ↦ β'a(y) − βb(y)` is nondecreasing, so is
`x ↦ (T_{β'}a)(x) − (T_βb)(x)`. -/
theorem bellman_sub_monotone (h : GrowthHyp U f β xbar) (h' : GrowthHyp U f β' xbar)
    (hU : ConcaveOn ℝ (Ici 0) U) {a b : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hD : Monotone fun y => β' * a y - β * b y) :
    Monotone fun x => bellman (growth_assumption43 h') (growth_assumption44 h') a x -
      bellman (growth_assumption43 h) (growth_assumption44 h) b x := by
  intro x₁ x₂ hx
  have hf : f x₁.1 ≤ f x₂.1 := h.f_mono.monotoneOn (mem_Ici.2 x₁.2.1) (mem_Ici.2 x₂.2.1) hx
  obtain ⟨c, hc, hcv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h') (growth_assumption44 h') a x₁
  obtain ⟨d, hd, hdv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) b x₂
  obtain ⟨-, -, -, hmax'⟩ :=
    exists_bellman_argmax (growth_assumption43 h') (growth_assumption44 h') a x₂
  obtain ⟨-, -, -, hmax⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) b x₁
  have hc' : c.1 ≤ f x₁.1 := hc
  have hd' : d.1 ≤ f x₂.1 := hd
  simp only
  rw [hcv, hdv]
  rcases le_total c d with hcd | hdc
  · -- `c ≤ d`: use `d` at `x₂` under `β'` and `c` at `x₁` under `β`
    have e1 := hmax' d hd
    have e2 := hmax c hc
    have e3 := hD hcd
    simp only at e3
    linarith
  · -- `d ≤ c`: use `c` at `x₂` under `β'` and `d` at `x₁` under `β`
    have e1 := hmax' c (show c.1 ≤ f x₂.1 by linarith)
    have e2 := hmax d (show d.1 ≤ f x₁.1 by linarith [show d.1 ≤ c.1 from hdc])
    have e3 := growthF_increasingDiff h hU hx hdc hc'
    linarith

/-- **Exercise 5.1e, increasing differences.** For `β ≤ β'`, `y ↦ β'v(y, β') − βv(y, β)` is
nondecreasing. -/
theorem discounted_value_monotone (h : GrowthHyp U f β xbar) (h' : GrowthHyp U f β' xbar)
    (hββ' : β ≤ β') (hU : ConcaveOn ℝ (Ici 0) U) {v v' : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hv' : bellman (growth_assumption43 h') (growth_assumption44 h') v' = v') :
    Monotone fun y => β' * v' y - β * v y := by
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  set T' := bellman (growth_assumption43 h') (growth_assumption44 h')
  have hvm : Monotone v := by
    obtain ⟨u, -, huniq, -, hmono, -⟩ := ex_5_1ab h
    rw [huniq v hv]
    exact hmono.monotone
  -- the iterates `wₙ = T_{β'}ⁿ v` keep `β'wₙ − βv` nondecreasing
  have hstep : ∀ n : ℕ, Monotone fun y => β' * (T'^[n] v) y - β * v y := by
    intro n
    induction n with
    | zero =>
      intro y₁ y₂ hy
      have := hvm hy
      simp only [Function.iterate_zero, id_eq]
      nlinarith
    | succ n ih =>
      have hm := bellman_sub_monotone h h' hU ih
      rw [hv] at hm
      intro y₁ y₂ hy
      have e1 := hm hy
      have e2 := hvm hy
      simp only [Function.iterate_succ_apply'] at e1 ⊢
      change T' (T'^[n] v) y₁ - v y₁ ≤ T' (T'^[n] v) y₂ - v y₂ at e1
      nlinarith [h'.β_pos]
  -- pass to the limit `wₙ → v'`
  obtain ⟨u, hu, huniq, hrate, -⟩ :=
    theorem_4_6 (growth_assumption43 h') (growth_assumption44 h')
  have hu' : v' = u := huniq v' hv'
  subst hu'
  have hlim : Tendsto (fun n => T'^[n] v) atTop (𝓝 v') := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (hrate v) ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h'.β_pos.le h'.β_lt).mul_const (dist v v')
  intro y₁ y₂ hy
  have hpt : ∀ y, Tendsto (fun n => β' * (T'^[n] v) y - β * v y) atTop
      (𝓝 (β' * v' y - β * v y)) := fun y =>
    ((((continuous_eval_const y).tendsto v').comp hlim).const_mul β').sub_const _
  exact le_of_tendsto_of_tendsto (hpt y₁) (hpt y₂) (Eventually.of_forall fun n => hstep n hy)

/-- **Exercise 5.1e.** If the policy under `β` is unique, then every optimal choice under any
`β' ≥ β` is at least as large: saving rises with patience. -/
theorem policy_le_of_discount_le [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (h' : GrowthHyp U f β' xbar) (hββ' : β ≤ β') (hU : ConcaveOn ℝ (Ici 0) U)
    {v v' : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hv' : bellman (growth_assumption43 h') (growth_assumption44 h') v' = v')
    (huniq : UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v))
    (x : Icc (0 : ℝ) xbar) {y' : Icc (0 : ℝ) xbar}
    (hy' : y' ∈ argmax (obj (growthF U f xbar) β' v') (growthΓ f xbar) x) :
    argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x ≤ y' := by
  set y := argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x
  have hy : y ∈ growthΓ f xbar x := (huniq.argmaxFn_mem x).1
  by_contra hlt
  push Not at hlt
  have h1 := huniq.lt_of_ne hy'.1 hlt.ne
  have h2 : obj (growthF U f xbar) β' v' (x, y) ≤ obj (growthF U f xbar) β' v' (x, y') := by
    rw [hy'.2]
    exact le_maxValue (continuousOn_obj (growth_assumption44 h') v'.continuous)
      ((growth_assumption43 h').compact x) hy
  have hD := discounted_value_monotone h h' hββ' hU hv hv' hlt.le
  simp only [obj] at h1 h2 hD
  linarith

/-- **Exercise 5.1e** under the hypotheses of Exercise 5.1c: `g(x, β) ≤ g(x, β')` for
`β ≤ β'`. -/
theorem ex_5_1e [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (h' : GrowthHyp U f β' xbar) (hββ' : β ≤ β') (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v v' : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hv' : bellman (growth_assumption43 h') (growth_assumption44 h') v' = v')
    (x : Icc (0 : ℝ) xbar) :
    argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x ≤
      argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β' v') x :=
  policy_le_of_discount_le h h' hββ' hU.concaveOn hv hv' (ex_5_1c_weak h hU hf hv).2.1 x
    ((ex_5_1c_weak h' hU hf hv').2.1.argmaxFn_mem x)

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Investment with linear costs

SLP §5.9, pp. 112–113: a firm with technology `f` buys capital at price `q`, sells output at
price `p`, and solves `v(k) = max_{y ≥ 0} {pf(k) − q[y − (1 − δ)k] + βv(y)}`.

**Exercise 5.9a.** Write `G(k) = pf(k) + q(1 − δ)k`, so the return is `G(k) − qy`, and
`h(y) = βG(y) − qy`.

* `invest_fe`: if `y*` maximizes `h` on `[0, ∞)`, then `v(k) = G(k) + h(y*)/(1 − β)` solves the
  functional equation, and `y = y*` attains the maximum at every `k`: the firm jumps to `y*` at
  once, whatever its capital. No differentiability is needed.
* `invest_partialSum_le`, `invest_plan_tendsto`: on the sequence problem, every plan's partial
  sums are at most `v(k₀)`, and the plan `k_t = y*` (`t ≥ 1`) attains `v(k₀)` in the limit; so `v`
  is the supremum function (although `f` is unbounded, the problem telescopes).
* `exists_max_sublinear`: if `f(y)/y → 0`, a maximizer `y*` exists; `invest_euler`: at an interior
  `y*`, `q = β[pf'(y*) + (1 − δ)q]`.
* Investment is reversible: nothing requires `y ≥ (1 − δ)k`, so the firm can sell capital.
* **Bounds on investment** (`(1 − δ)k ≤ y ≤ (1 − δ)k + a`): `clamp_maximizes`: with `v` concave,
  the objective `−qy + βv(y)` does not depend on `k`, so the policy is its unconstrained
  maximizer `ŷ` pushed into `[(1 − δ)k, (1 − δ)k + a]`:
  `g(k) = (1 − δ)k + a` below `(ŷ − a)/(1 − δ)`, `ŷ` in between, and `(1 − δ)k` above
  `ŷ/(1 − δ)` (`bounded_policy`).
* Tools used again later: `intervalΓ_assumption43` (an interval correspondence on `[0, K]`
  satisfies Assumption 4.3) and `fixed_concave_of_concaveF` (with `F` concave on the graph, not
  necessarily strictly, the fixed point is concave).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {f : ℝ → ℝ} {p q δ β : ℝ}

/-- `G(k) = pf(k) + q(1 − δ)k`. -/
def investG (f : ℝ → ℝ) (p q δ k : ℝ) : ℝ := p * f k + q * (1 - δ) * k

/-- `h(y) = βG(y) − qy`. -/
def investH (f : ℝ → ℝ) (p q δ β y : ℝ) : ℝ := β * investG f p q δ y - q * y

/-- **Exercise 5.9a.** `v(k) = G(k) + h(y*)/(1 − β)` solves the functional equation and `y*`
attains the maximum at every `k`. -/
theorem invest_fe (hβ1 : β < 1) {ystar : ℝ}
    (hmax : ∀ y, 0 ≤ y → investH f p q δ β y ≤ investH f p q δ β ystar) (k : ℝ) :
    (∀ y, 0 ≤ y → investG f p q δ k - q * y +
        β * (investG f p q δ y + investH f p q δ β ystar / (1 - β)) ≤
      investG f p q δ k + investH f p q δ β ystar / (1 - β)) ∧
    investG f p q δ k - q * ystar +
        β * (investG f p q δ ystar + investH f p q δ β ystar / (1 - β)) =
      investG f p q δ k + investH f p q δ β ystar / (1 - β) := by
  have h1β : (1 - β) ≠ 0 := by linarith
  have e : ∀ y, investG f p q δ k - q * y +
      β * (investG f p q δ y + investH f p q δ β ystar / (1 - β)) =
      investG f p q δ k + investH f p q δ β y + β * (investH f p q δ β ystar / (1 - β)) :=
    fun y => by simp only [investH]; ring
  have e2 : investH f p q δ β ystar + β * (investH f p q δ β ystar / (1 - β)) =
      investH f p q δ β ystar / (1 - β) := by field_simp; ring
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [e y]; linarith [hmax y hy]
  · rw [e ystar]; linarith

/-- The telescoping identity: `Σ_{t ≤ N} βᵗ[G(k_t) − qk_{t+1}] =
G(k₀) + Σ_{t < N} βᵗh(k_{t+1}) − βᴺqk_{N+1}`. -/
theorem invest_telescope (k : ℕ → ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * (investG f p q δ (k t) - q * k (t + 1)) =
      investG f p q δ (k 0) + ∑ t ∈ Finset.range N, β ^ t * investH f p q δ β (k (t + 1)) -
        β ^ N * (q * k (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [investH, pow_succ]
    ring

/-- **Exercise 5.9a.** Every plan with `k_t ≥ 0` has partial sums at most `v(k₀)`. -/
theorem invest_partialSum_le (hβ0 : 0 < β) (hβ1 : β < 1) (hq : 0 ≤ q) (hf0 : f 0 = 0)
    {ystar : ℝ} (hmax : ∀ y, 0 ≤ y → investH f p q δ β y ≤ investH f p q δ β ystar)
    {k : ℕ → ℝ} (hk : ∀ t, 0 ≤ k t) (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * (investG f p q δ (k t) - q * k (t + 1)) ≤
      investG f p q δ (k 0) + investH f p q δ β ystar / (1 - β) := by
  rw [invest_telescope]
  set M := investH f p q δ β ystar
  have hM0 : 0 ≤ M := by
    have := hmax 0 le_rfl
    simp only [investH, investG, hf0] at this
    simpa using this
  have hsum : ∑ t ∈ Finset.range N, β ^ t * investH f p q δ β (k (t + 1)) ≤
      ∑ t ∈ Finset.range N, β ^ t * M :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hmax _ (hk _)) (pow_nonneg hβ0.le t)
  have hgeom : ∑ t ∈ Finset.range N, β ^ t * M ≤ M / (1 - β) := by
    have h1 : 0 < 1 - β := by linarith
    have hs : ∑ t ∈ Finset.range N, β ^ t ≤ 1 / (1 - β) := by
      rw [le_div_iff₀ h1, geom_sum_mul_neg]
      linarith [pow_nonneg hβ0.le N]
    rw [← Finset.sum_mul]
    calc (∑ t ∈ Finset.range N, β ^ t) * M ≤ 1 / (1 - β) * M := mul_le_mul_of_nonneg_right hs hM0
      _ = M / (1 - β) := by ring
  have htail : 0 ≤ β ^ N * (q * k (N + 1)) :=
    mul_nonneg (pow_nonneg hβ0.le N) (mul_nonneg hq (hk _))
  linarith

/-- **Exercise 5.9a.** The plan `k₀, y*, y*, …` attains `v(k₀)` in the limit. -/
theorem invest_plan_tendsto (hβ0 : 0 < β) (hβ1 : β < 1) (ystar k₀ : ℝ) :
    Tendsto (fun N => ∑ t ∈ Finset.range (N + 1), β ^ t *
        (investG f p q δ (if t = 0 then k₀ else ystar) - q * ystar)) atTop
      (𝓝 (investG f p q δ k₀ + investH f p q δ β ystar / (1 - β))) := by
  have e : ∀ N, ∑ t ∈ Finset.range (N + 1), β ^ t *
      (investG f p q δ (if t = 0 then k₀ else ystar) - q * ystar) =
      investG f p q δ k₀ + ∑ t ∈ Finset.range N, β ^ t * investH f p q δ β ystar -
        β ^ N * (q * ystar) := fun N => by
    have := invest_telescope (f := f) (p := p) (q := q) (δ := δ) (β := β)
      (fun t => if t = 0 then k₀ else ystar) N
    simpa using this
  simp_rw [e]
  have h1 := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right (investH f p q δ β ystar)
  have h2 := h1.tendsto_sum_nat
  have h3 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (q * ystar)
  have := (h2.const_add (investG f p q δ k₀)).sub h3
  simp only [zero_mul, sub_zero] at this
  convert this using 2
  rw [div_eq_mul_inv, mul_comm]

/-- If `g(y)/y → 0` and `κ > 0`, then `g(y) − κy` attains its maximum on `[0, ∞)`. -/
theorem exists_max_sublinear {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0))
    (hsub : Tendsto (fun y => g y / y) atTop (𝓝 0)) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ystar, 0 ≤ ystar ∧ ∀ y, 0 ≤ y → g y - κ * y ≤ g ystar - κ * ystar := by
  -- beyond some `R ≥ 1`, `g(y) − κy < g(0)`
  have hev : ∀ᶠ y in atTop, g y / y < κ / 2 := hsub.eventually (gt_mem_nhds (by linarith))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hev
  set R := max (max R₀ 1) (2 * |g 0| / κ + 1)
  have hR1 : 1 ≤ R := (le_max_left _ _).trans' (le_max_right _ _)
  have hout : ∀ y, R < y → g y - κ * y < g 0 - κ * 0 := fun y hy => by
    have hy0 : 0 < y := by linarith
    have h1 := hR₀ y ((le_max_left _ _).trans ((le_max_left _ _).trans hy.le))
    rw [div_lt_iff₀ hy0] at h1
    have h2 : 2 * |g 0| / κ + 1 < y := (le_max_right _ _).trans_lt hy
    rw [div_add_one hκ.ne', div_lt_iff₀ hκ] at h2
    nlinarith [le_abs_self (g 0), neg_abs_le (g 0)]
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith : (0:ℝ) ≤ R))
    ((hg.mono Icc_subset_Ici_self).sub (continuousOn_const.mul continuousOn_id))
  refine ⟨y₀, hy₀.1, fun y hy => ?_⟩
  rcases le_or_gt y R with hyR | hyR
  · exact hmax ⟨hy, hyR⟩
  · exact (hout y hyR).le.trans (hmax ⟨le_rfl, by linarith⟩)

/-- **Exercise 5.9a.** At an interior maximizer the Euler equation `q = β[pf'(y*) + (1 − δ)q]`
holds. -/
theorem invest_euler {ystar f' : ℝ} (hpos : 0 < ystar)
    (hmax : ∀ y, 0 ≤ y → investH f p q δ β y ≤ investH f p q δ β ystar)
    (hf : HasDerivAt f f' ystar) : q = β * (p * f' + (1 - δ) * q) := by
  have hd : HasDerivAt (investH f p q δ β) (β * (p * f' + q * (1 - δ) * 1) - q * 1) ystar :=
    (((hf.const_mul p).add ((hasDerivAt_id' ystar).const_mul (q * (1 - δ)))).const_mul β).sub
      ((hasDerivAt_id' ystar).const_mul q)
  have hloc : IsLocalMax (investH f p q δ β) ystar := by
    filter_upwards [Ici_mem_nhds hpos] with y hy
    exact hmax y hy
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-! ### Bounds on investment -/

/-- A concave function is maximized over an interval `[l, u]` of its domain `s` at its maximizer
`ŷ` over `s` pushed into `[l, u]`. -/
theorem clamp_maximizes {s : Set ℝ} {ψ : ℝ → ℝ} (hψ : ConcaveOn ℝ s ψ) {yhat : ℝ}
    (hy0 : yhat ∈ s) (hmax : ∀ y ∈ s, ψ y ≤ ψ yhat) {l u : ℝ} (hlu : l ≤ u)
    (hsub : Icc l u ⊆ s) {y : ℝ} (hy : y ∈ Icc l u) : ψ y ≤ ψ (max l (min yhat u)) := by
  set c := max l (min yhat u)
  -- on either side of `ŷ`, concavity makes `ψ` monotone towards `ŷ`
  have key : ∀ a b, a ∈ s → a ≤ b → b ≤ yhat → ψ a ≤ ψ b := fun a b ha hab hb => by
    rcases eq_or_lt_of_le (hab.trans hb) with he | hlt
    · have : a = b := le_antisymm hab (he ▸ hb); rw [this]
    have hθ0 : 0 ≤ (yhat - b) / (yhat - a) := div_nonneg (by linarith) (by linarith)
    have hθ1 : (yhat - b) / (yhat - a) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have := hψ.2 ha hy0 hθ0 (sub_nonneg.2 hθ1) (by ring)
    simp only [smul_eq_mul] at this
    have e : (yhat - b) / (yhat - a) * a + (1 - (yhat - b) / (yhat - a)) * yhat = b := by
      field_simp; ring
    rw [e] at this
    have := hmax a ha
    nlinarith
  have key' : ∀ a b, a ∈ s → yhat ≤ b → b ≤ a → ψ a ≤ ψ b := fun a b ha hb hba => by
    rcases eq_or_lt_of_le (hb.trans hba) with he | hlt
    · have : a = b := le_antisymm (he ▸ hb) hba; rw [this]
    have hθ0 : 0 ≤ (b - yhat) / (a - yhat) := div_nonneg (by linarith) (by linarith)
    have hθ1 : (b - yhat) / (a - yhat) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have := hψ.2 ha hy0 hθ0 (sub_nonneg.2 hθ1) (by ring)
    simp only [smul_eq_mul] at this
    have e : (b - yhat) / (a - yhat) * a + (1 - (b - yhat) / (a - yhat)) * yhat = b := by
      field_simp; ring
    rw [e] at this
    have := hmax a ha
    nlinarith
  have hys := hsub hy
  rcases le_total yhat l with hyl | hyl
  · -- `ŷ ≤ l`: `c = l`, and `ψ` falls on `[l, u]`
    have hcl : c = l := max_eq_left ((min_le_left _ _).trans hyl)
    rw [hcl]
    exact key' y l hys hyl hy.1
  · rcases le_total yhat u with hyu | hyu
    · have hcy : c = yhat := by simp only [c, min_eq_left hyu, max_eq_right hyl]
      rw [hcy]; exact hmax y hys
    · -- `u ≤ ŷ`: `c = u`, and `ψ` rises on `[l, u]`
      have hcu : c = u := by simp only [c, min_eq_right hyu, max_eq_right hlu]
      rw [hcu]
      exact key y u hys hy.2 hyu

/-- **Exercise 5.9a with bounds on investment.** If `ψ(y) = −qy + βv(y)` is concave with
maximizer `ŷ`, the optimal choice under `(1 − δ)k ≤ y ≤ (1 − δ)k + a` is
`g(k) = max{(1 − δ)k, min{ŷ, (1 − δ)k + a}}`: maximal investment for
`k ≤ (ŷ − a)/(1 − δ)`, the target `ŷ` in between, and no gross investment for `k ≥ ŷ/(1 − δ)`. -/
theorem bounded_policy {v : ℝ → ℝ} (hψ : ConcaveOn ℝ (Ici 0) fun y => -(q * y) + β * v y)
    {yhat : ℝ} (hy0 : 0 ≤ yhat) (hmax : ∀ y, 0 ≤ y → -(q * y) + β * v y ≤ -(q * yhat) + β * v yhat)
    (hδ : δ < 1) {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) :
    (∀ y ∈ Icc ((1 - δ) * k) ((1 - δ) * k + a),
      investG f p q δ k - q * y + β * v y ≤
        investG f p q δ k - q * max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) +
          β * v (max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)))) ∧
    (k ≤ (yhat - a) / (1 - δ) → max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) =
      (1 - δ) * k + a) ∧
    ((yhat - a) / (1 - δ) ≤ k → k ≤ yhat / (1 - δ) →
      max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) = yhat) ∧
    (yhat / (1 - δ) ≤ k → max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) = (1 - δ) * k) := by
  have h1δ : 0 < 1 - δ := by linarith
  have hl : 0 ≤ (1 - δ) * k := mul_nonneg h1δ.le hk
  refine ⟨fun y hy => ?_, fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · have := clamp_maximizes hψ (mem_Ici.2 hy0) (fun y hy => hmax y hy) (by linarith)
      (fun z hz => mem_Ici.2 (hl.trans hz.1)) hy
    linarith
  · rw [le_div_iff₀ h1δ] at h
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [div_le_iff₀ h1δ] at h1
    rw [le_div_iff₀ h1δ] at h2
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  · rw [div_le_iff₀ h1δ] at h
    rw [max_eq_left ((min_le_left _ _).trans (by linarith))]

/-! ### Tools: interval correspondences and concave fixed points -/

/-- The interval correspondence `Γ(x) = [l(x), u(x)]` on `[0, K]`. -/
def intervalΓ (K : ℝ) (l u : ℝ → ℝ) (x : Icc (0 : ℝ) K) : Set (Icc (0 : ℝ) K) :=
  {y | l x.1 ≤ y.1 ∧ y.1 ≤ u x.1}

/-- An interval correspondence with continuous bounds `0 ≤ l ≤ u ≤ K` satisfies
Assumption 4.3. -/
theorem intervalΓ_assumption43 {K : ℝ} {l u : ℝ → ℝ} (hl : ContinuousOn l (Icc 0 K))
    (hu : ContinuousOn u (Icc 0 K)) (hl0 : ∀ x ∈ Icc 0 K, 0 ≤ l x)
    (hlu : ∀ x ∈ Icc 0 K, l x ≤ u x) (huK : ∀ x ∈ Icc 0 K, u x ≤ K) :
    Assumption43 (intervalΓ K l u) := by
  have hlc : Continuous fun x : Icc (0 : ℝ) K => l x.1 :=
    hl.comp_continuous continuous_subtype_val fun x => x.2
  have huc : Continuous fun x : Icc (0 : ℝ) K => u x.1 :=
    hu.comp_continuous continuous_subtype_val fun x => x.2
  have : CompactSpace (Icc (0 : ℝ) K) := isCompact_iff_compactSpace.1 isCompact_Icc
  set pt : Icc (0 : ℝ) K → Icc (0 : ℝ) K := fun x =>
    ⟨l x.1, hl0 x.1 x.2, (hlu x.1 x.2).trans (huK x.1 x.2)⟩
  have hpt : ∀ x, pt x ∈ intervalΓ K l u x := fun x => ⟨le_rfl, hlu x.1 x.2⟩
  refine ⟨fun x => ⟨pt x, hpt x⟩, fun x => ?_, fun x => ⟨⟨pt x, hpt x⟩, fun y hy xs hxs => ?_⟩,
    fun x => ⟨⟨pt x, hpt x⟩, fun xs hxs ys hys => ?_⟩⟩
  · exact ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).isCompact
  · -- l.h.c.: `yₙ = max{l(xₙ), min{y, u(xₙ)}}`
    refine ⟨0, fun n => ⟨max (l (xs n).1) (min y.1 (u (xs n).1)),
      le_max_of_le_left (hl0 _ (xs n).2),
      max_le ((hlu _ (xs n).2).trans (huK _ (xs n).2)) ((min_le_right _ _).trans
        (huK _ (xs n).2))⟩,
      fun n _ => ⟨le_max_left _ _, max_le (hlu _ (xs n).2) (min_le_right _ _)⟩, ?_⟩
    have hlim := ((hlc.tendsto x).comp hxs).max
      ((tendsto_const_nhds (x := y.1)).min ((huc.tendsto x).comp hxs))
    rw [min_eq_left hy.2, max_eq_right hy.1] at hlim
    exact tendsto_subtype_rng.2 hlim
  · -- u.h.c.: `X` is compact and the graph is closed
    obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
    have hxφ := hxs.comp hφ.tendsto_atTop
    have hyl := (continuous_subtype_val.tendsto y).comp hlim
    refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
    · exact le_of_tendsto_of_tendsto ((hlc.tendsto x).comp hxφ) hyl
        (Eventually.of_forall fun n => (hys (φ n)).1)
    · exact le_of_tendsto_of_tendsto hyl ((huc.tendsto x).comp hxφ)
        (Eventually.of_forall fun n => (hys (φ n)).2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- With `F` concave on the graph (the weak half of Assumption 4.7) and Assumption 4.8, `T`
preserves concavity. -/
theorem bellman_concave_of_concaveF {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ}
    (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (hF : ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hS h0 h1 x x', cmb hS h0 h1 y y'))
    (h48 : Assumption48 hS Γ) {g : S →ᵇ ℝ} (hg : IsConcaveS hS g) :
    IsConcaveS hS (bellman h43 h44 g) := by
  intro x x' θ h0 h1
  obtain ⟨y, hy, hyv, -⟩ := exists_bellman_argmax h43 h44 g x
  obtain ⟨y', hy', hyv', -⟩ := exists_bellman_argmax h43 h44 g x'
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax h43 h44 g (cmb hS h0 h1 x x')
  have hm := hmax _ (h48 x y x' y' hy hy' θ h0 h1)
  have hFc := hF x y x' y' hy hy' θ h0 h1
  have hgc := mul_le_mul_of_nonneg_left (hg y y' θ h0 h1) h44.β_pos.le
  rw [hyv, hyv']
  nlinarith

/-- With `F` concave on the graph and Assumption 4.8, the fixed point is concave. -/
theorem fixed_concave_of_concaveF [Nonempty S] {hS : Convex ℝ S} {Γ : S → Set S}
    {F : S × S → ℝ} (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (hF : ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hS h0 h1 x x', cmb hS h0 h1 y y'))
    (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ} (hv : bellman h43 h44 v = v) : IsConcaveS hS v :=
  (corollary_1 (S' := {g | IsConcaveS hS g}) (S'' := {g | IsConcaveS hS g})
    (bellman_contraction h43 h44) hv ⟨0, fun x x' θ _ _ => by simp⟩ (isClosed_concave hS)
    (fun _ hg => bellman_concave_of_concaveF h43 h44 hF h48 hg)
    (fun _ hg => bellman_concave_of_concaveF h43 h44 hF h48 hg)).1

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Investment with bounds, with convex adjustment costs, and short-run profits

SLP §5.9, pp. 112–113, continued. All three problems live on a compact state space `[0, K]`.

* **Exercise 5.9a with bounds** (`ex_5_9a_bounds`): with
  `(1 − δ)k ≤ y ≤ (1 − δ)k + a` and `K ≥ a/δ` (so `[0, K]` is invariant), there is a unique
  bounded continuous `v`; it is concave, and the policy is the target `ŷ = argmax [−qy + βv(y)]`
  pushed into the feasible interval.
* **Exercise 5.9b** (`ex_5_9b`): with a strictly convex cost `c` of gross investment and `f`
  strictly concave, Assumption 4.7 holds, so `v` is strictly concave and the policy `g` is a
  continuous function. `g` is nondecreasing (`ex_5_9b_mono`) and
  `g(k') − g(k) ≤ (1 − δ)(k' − k)` (`ex_5_9b_slope`): investment falls as capital rises, so
  capital adjusts gradually. Both are lattice arguments: no derivatives are used.
  `ex_5_9b_envelope`, `ex_5_9b_foc`, `ex_5_9b_euler`: `v'(k) = pf'(k) + (1 − δ)c'(i)`,
  `c'(i) = βv'(g(k))`, and the Euler equation
  `c'(g(k) − (1 − δ)k) = β[pf'(g(k)) + (1 − δ)c'(g(g(k)) − (1 − δ)g(k))]`, which at a steady
  state reads `c'(δk*)(1 − β(1 − δ)) = βpf'(k*)` (`ex_5_9b_steady`). With a linear cost the
  marginal cost of investing is constant and the firm jumps to its target (part a).
* **Exercise 5.9c**: short-run profit `Π(k) = max_{l ≥ 0} [pF(k, l) − wl]`.
  `labor_demand_exists`: labour demand exists if `F(k, ·)` is continuous and `F(k, l)/l → 0`;
  `labor_demand_unique`: it is unique if `F(k, ·)` is strictly concave. Then `Π(0) = 0` if
  `F(0, ·) = 0` (`profitPi_zero`), `Π` is nondecreasing if `F` is (`profitPi_mono`), concave if
  `F` is jointly concave (`profitPi_concave`), strictly concave if `F` is jointly strictly
  concave (`profitPi_strictConcave`), and `Π'(k) = pF_k(k, φ(k))` (`profitPi_deriv`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {f c : ℝ → ℝ} {p q δ β a K : ℝ}

/-- A concave function on `[0, K]` extends to a concave function on the real interval. -/
theorem concaveOn_liftR_of_concave {v : Icc (0 : ℝ) K → ℝ} (hv : IsConcaveS (convex_Icc 0 K) v) :
    ConcaveOn ℝ (Icc 0 K) (liftR K v) := by
  refine ⟨convex_Icc 0 K, fun x hx y hy s t hs ht hst => ?_⟩
  have ht' : t = 1 - s := by linarith
  subst ht'
  have hmem : s • x + (1 - s) • y ∈ Icc (0 : ℝ) K := convex_Icc 0 K hx hy hs ht hst
  rw [liftR_of_mem v hx, liftR_of_mem v hy, liftR_of_mem v hmem, smul_eq_mul, smul_eq_mul]
  exact hv ⟨x, hx⟩ ⟨y, hy⟩ s hs (by linarith)

/-- A continuous function on the compact `[0, K] × [0, K]` is bounded. -/
theorem exists_bound_Icc_prod {F : Icc (0 : ℝ) K × Icc (0 : ℝ) K → ℝ} (hF : Continuous F) :
    ∃ B, ∀ p, |F p| ≤ B := by
  have : CompactSpace (Icc (0 : ℝ) K) := isCompact_iff_compactSpace.1 isCompact_Icc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨B, fun p => by simpa [Real.norm_eq_abs] using hB p (mem_univ p)⟩

/-! ### Exercise 5.9a with bounds on investment -/

/-- The return `pf(k) − q[y − (1 − δ)k] = G(k) − qy` on `[0, K]`. -/
def investF (f : ℝ → ℝ) (p q δ K : ℝ) (pr : Icc (0 : ℝ) K × Icc (0 : ℝ) K) : ℝ :=
  investG f p q δ pr.1.1 - q * pr.2.1

/-- `Γ(k) = [(1 − δ)k, (1 − δ)k + a]`. -/
def boundedΓ (δ a K : ℝ) : Icc (0 : ℝ) K → Set (Icc (0 : ℝ) K) :=
  intervalΓ K (fun k => (1 - δ) * k) (fun k => (1 - δ) * k + a)

theorem bounded_assumption43 (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha : 0 ≤ a) (hK : a ≤ δ * K) :
    Assumption43 (boundedΓ δ a K) :=
  intervalΓ_assumption43 (continuousOn_const.mul continuousOn_id)
    ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
    (fun x hx => mul_nonneg (by linarith) hx.1) (fun x _ => by linarith)
    (fun x hx => by nlinarith [hx.2])

theorem bounded_assumption44 (hβ0 : 0 < β) (hβ1 : β < 1) (hf : ContinuousOn f (Icc 0 K)) :
    Assumption44 (boundedΓ δ a K) (investF f p q δ K) β := by
  have hc : Continuous (investF f p q δ K) :=
    ((continuous_const.mul (hf.comp_continuous (continuous_subtype_val.comp continuous_fst)
      fun pr => pr.1.2)).add (continuous_const.mul (continuous_subtype_val.comp
        continuous_fst))).sub (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  obtain ⟨B, hB⟩ := exists_bound_Icc_prod hc
  exact ⟨hc.continuousOn, ⟨B, fun pr _ => hB pr⟩, hβ0, hβ1⟩

/-- **Exercise 5.9a with bounds.** There is a unique bounded continuous `v`; it is concave; and
with `ŷ` maximizing `−qy + βv(y)` on `[0, K]`, the choice
`max{(1 − δ)k, min{ŷ, (1 − δ)k + a}}` is optimal at every `k`. -/
theorem ex_5_9a_bounds (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha : 0 ≤ a) (hK : a ≤ δ * K)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : 0 ≤ p) (hfc : ContinuousOn f (Icc 0 K))
    (hfcc : ConcaveOn ℝ (Icc 0 K) f) :
    ∃ v : Icc (0 : ℝ) K →ᵇ ℝ,
      bellman (bounded_assumption43 hδ0 hδ1 ha hK) (bounded_assumption44 (a := a) (p := p)
        (q := q) (δ := δ) hβ0 hβ1 hfc) v = v ∧
      (∀ w, bellman (bounded_assumption43 hδ0 hδ1 ha hK) (bounded_assumption44 (a := a) (p := p)
        (q := q) (δ := δ) hβ0 hβ1 hfc) w = w → w = v) ∧
      IsConcaveS (convex_Icc 0 K) v ∧
      ∃ yhat : Icc (0 : ℝ) K, ∀ k : Icc (0 : ℝ) K,
        ∀ hc : max ((1 - δ) * k.1) (min yhat.1 ((1 - δ) * k.1 + a)) ∈ Icc (0 : ℝ) K,
          (⟨_, hc⟩ : Icc (0 : ℝ) K) ∈
            argmax (obj (investF f p q δ K) β v) (boundedΓ δ a K) k := by
  have hK0 : 0 ≤ K := by nlinarith
  have : Nonempty (Icc (0 : ℝ) K) := ⟨⟨0, le_rfl, hK0⟩⟩
  have : CompactSpace (Icc (0 : ℝ) K) := isCompact_iff_compactSpace.1 isCompact_Icc
  set h43 := bounded_assumption43 hδ0 hδ1 ha hK
  set h44 := bounded_assumption44 (a := a) (p := p) (q := q) (δ := δ) hβ0 hβ1 hfc
  obtain ⟨v, hv, huniq, -⟩ := theorem_4_6 h43 h44
  -- `F` is concave on the graph and `Γ` has a convex graph
  have hF : ∀ x y x' y', y ∈ boundedΓ δ a K x → y' ∈ boundedΓ δ a K x' →
      ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * investF f p q δ K (x, y) + (1 - θ) * investF f p q δ K (x', y') ≤
        investF f p q δ K (cmb (convex_Icc 0 K) h0 h1 x x', cmb (convex_Icc 0 K) h0 h1 y y') := by
    intro x y x' y' _ _ θ h0 h1
    have hfw := hfcc.2 x.2 x'.2 h0 (sub_nonneg.2 h1) (by ring)
    simp only [smul_eq_mul] at hfw
    simp only [investF, investG, cmb, smul_eq_mul]
    nlinarith
  have h48 : Assumption48 (convex_Icc 0 K) (boundedΓ δ a K) := by
    intro x y x' y' hy hy' θ h0 h1
    have h1' : 0 ≤ 1 - θ := by linarith
    simp only [boundedΓ, intervalΓ, cmb, smul_eq_mul, mem_ofPred_eq] at hy hy' ⊢
    constructor <;> nlinarith [hy.1, hy.2, hy'.1, hy'.2]
  have hvc := fixed_concave_of_concaveF h43 h44 hF h48 hv
  -- the target `ŷ`
  set ψ : ℝ → ℝ := fun y => -(q * y) + β * liftR K v y
  have hψc : ConcaveOn ℝ (Icc 0 K) ψ :=
    ((LinearMap.mulLeft ℝ (-q)).concaveOn (convex_Icc 0 K)).add
      ((concaveOn_liftR_of_concave hvc).smul hβ0.le) |>.congr fun y _ => by
        simp [ψ, smul_eq_mul]
  have hψcont : ContinuousOn ψ (Icc 0 K) := by
    refine (continuousOn_const.mul continuousOn_id).neg.add (continuousOn_const.mul ?_)
    refine (v.continuous.comp (continuous_projIcc (h := hK0))).continuousOn.congr fun y hy => ?_
    rw [liftR_of_mem v hy, Function.comp_apply, projIcc_of_mem hK0 hy]
  obtain ⟨yh, hyh, hyhmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hK0) hψcont
  refine ⟨v, hv, huniq, hvc, ⟨yh, hyh⟩, fun k hc => ?_⟩
  have hl0 : 0 ≤ (1 - δ) * k.1 := mul_nonneg (by linarith) k.2.1
  have hlu : (1 - δ) * k.1 ≤ (1 - δ) * k.1 + a := by linarith
  have hsub : Icc ((1 - δ) * k.1) ((1 - δ) * k.1 + a) ⊆ Icc 0 K := fun z hz =>
    ⟨hl0.trans hz.1, hz.2.trans (by nlinarith [k.2.2])⟩
  have hmemΓ : (⟨_, hc⟩ : Icc (0 : ℝ) K) ∈ boundedΓ δ a K k :=
    ⟨le_max_left _ _, max_le hlu ((min_le_right _ _))⟩
  have hge : ∀ z ∈ boundedΓ δ a K k, obj (investF f p q δ K) β v (k, z) ≤
      obj (investF f p q δ K) β v (k, ⟨_, hc⟩) := fun z hz => by
    have := clamp_maximizes hψc hyh (fun y hy => hyhmax hy) hlu hsub (y := z.1) hz
    simp only [ψ, liftR_of_mem v z.2, liftR_of_mem v hc] at this
    simp only [obj, investF]
    linarith
  refine ⟨hmemΓ, le_antisymm (le_maxValue (continuousOn_obj h44 v.continuous) (h43.compact k)
    hmemΓ) ?_⟩
  obtain ⟨y, hy, hyv, -⟩ := exists_argmax (continuousOn_obj h44 v.continuous) (h43.compact k)
    (h43.nonempty k)
  rw [← hyv]
  exact hge y hy

/-! ### Exercise 5.9b: convex adjustment costs -/

/-- The return `pf(k) − c(y − (1 − δ)k)` on `[0, K]`. -/
def adjF (f c : ℝ → ℝ) (p δ K : ℝ) (pr : Icc (0 : ℝ) K × Icc (0 : ℝ) K) : ℝ :=
  p * f pr.1.1 - c (pr.2.1 - (1 - δ) * pr.1.1)

/-- `Γ(k) = [0, K]`. -/
def fullΓ (K : ℝ) : Icc (0 : ℝ) K → Set (Icc (0 : ℝ) K) := intervalΓ K (fun _ => 0) (fun _ => K)

theorem full_assumption43 (hK : 0 ≤ K) : Assumption43 (fullΓ K) :=
  intervalΓ_assumption43 continuousOn_const continuousOn_const (fun _ _ => le_rfl)
    (fun _ _ => hK) (fun _ _ => le_rfl)

theorem mem_fullΓ (k y : Icc (0 : ℝ) K) : y ∈ fullΓ K k := ⟨y.2.1, y.2.2⟩

theorem adj_assumption44 (hβ0 : 0 < β) (hβ1 : β < 1) (hf : ContinuousOn f (Icc 0 K))
    (hc : Continuous c) : Assumption44 (fullΓ K) (adjF f c p δ K) β := by
  have hcont : Continuous (adjF f c p δ K) :=
    (continuous_const.mul (hf.comp_continuous (continuous_subtype_val.comp continuous_fst)
      fun pr => pr.1.2)).sub (hc.comp ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))
  obtain ⟨B, hB⟩ := exists_bound_Icc_prod hcont
  exact ⟨hcont.continuousOn, ⟨B, fun pr _ => hB pr⟩, hβ0, hβ1⟩

/-- Assumption 4.7: `f` strictly concave and `c` convex. -/
theorem adj_a47 (hp : 0 < p) (hf : StrictConcaveOn ℝ (Icc 0 K) f) (hc : ConvexOn ℝ univ c) :
    Assumption47 (convex_Icc 0 K) (fullΓ K) (adjF f c p δ K) := by
  intro x y x' y' _ _ θ h0 h1
  have h1' : 0 ≤ 1 - θ := by linarith
  have hcw := hc.2 (mem_univ (y.1 - (1 - δ) * x.1)) (mem_univ (y'.1 - (1 - δ) * x'.1)) h0.le h1'
    (by ring)
  simp only [smul_eq_mul] at hcw
  have hfw := hf.concaveOn.2 x.2 x'.2 h0.le h1' (by ring)
  simp only [smul_eq_mul] at hfw
  have e : θ * y.1 + (1 - θ) * y'.1 - (1 - δ) * (θ * x.1 + (1 - θ) * x'.1) =
      θ * (y.1 - (1 - δ) * x.1) + (1 - θ) * (y'.1 - (1 - δ) * x'.1) := by ring
  simp only [adjF, cmb, smul_eq_mul, e]
  refine ⟨by nlinarith, fun hne => ?_⟩
  have hne' : x.1 ≠ x'.1 := fun he => hne (Subtype.ext he)
  have hfs := hf.2 x.2 x'.2 hne' h0 (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hfs
  nlinarith

theorem full_a48 : Assumption48 (convex_Icc 0 K) (fullΓ K) := fun _ y _ y' _ _ _ h0 h1 =>
  mem_fullΓ _ (cmb (convex_Icc 0 K) h0 h1 y y')

/-- The hypotheses of Exercise 5.9b. -/
structure AdjHyp (f c : ℝ → ℝ) (p δ β K : ℝ) : Prop where
  p_pos : 0 < p
  δ_pos : 0 < δ
  δ_lt : δ < 1
  β_pos : 0 < β
  β_lt : β < 1
  K_pos : 0 < K
  f_cont : ContinuousOn f (Icc 0 K)
  f_concave : StrictConcaveOn ℝ (Icc 0 K) f
  c_cont : Continuous c
  c_convex : ConvexOn ℝ univ c

theorem AdjHyp.h43 (h : AdjHyp f c p δ β K) : Assumption43 (fullΓ K) :=
  full_assumption43 h.K_pos.le

theorem AdjHyp.h44 (h : AdjHyp f c p δ β K) : Assumption44 (fullΓ K) (adjF f c p δ K) β :=
  adj_assumption44 h.β_pos h.β_lt h.f_cont h.c_cont

/-- **Exercise 5.9b.** `v` is strictly concave and the policy is a continuous function. -/
theorem ex_5_9b [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) :
    IsStrictConcaveS (convex_Icc 0 K) v ∧ UniqueArgmax (fullΓ K) (obj (adjF f c p δ K) β v) ∧
      Continuous (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)) := by
  obtain ⟨h1, h2, -, h4⟩ := theorem_4_8 h.h43 h.h44 (adj_a47 h.p_pos h.f_concave h.c_convex)
    full_a48 hv
  exact ⟨h1, h2, h4⟩

/-- **Exercise 5.9b.** The policy is nondecreasing. -/
theorem ex_5_9b_mono [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) :
    Monotone (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)) := by
  obtain ⟨-, hUA, -⟩ := ex_5_9b h hv
  intro k k' hkk'
  set g := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)
  by_contra hlt
  push Not at hlt
  have hk : k.1 ≤ k'.1 := hkk'
  have hlt' : (g k').1 < (g k).1 := hlt
  -- swapping the two choices helps by convexity of `c`, contradicting uniqueness
  have e1 := hUA.lt_of_ne (mem_fullΓ k (g k')) hlt.ne
  have e2 := hUA.lt_of_ne (mem_fullΓ k' (g k)) hlt.ne'
  have hex := concave_exchange (φ := fun z => -c z) (s := univ) h.c_convex.neg
    (p := (g k').1 - (1 - δ) * k'.1) (q := (g k').1 - (1 - δ) * k.1)
    (δ := (g k).1 - (g k').1) (mem_univ _) (mem_univ _)
    (by nlinarith [h.δ_lt]) (by linarith)
  simp only [obj, adjF] at e1 e2 hex
  rw [show (g k').1 - (1 - δ) * k.1 + ((g k).1 - (g k').1) = (g k).1 - (1 - δ) * k.1 by ring,
    show (g k').1 - (1 - δ) * k'.1 + ((g k).1 - (g k').1) = (g k).1 - (1 - δ) * k'.1 by ring]
    at hex
  linarith

/-- **Exercise 5.9b.** `g(k') − g(k) ≤ (1 − δ)(k' − k)`: gross investment `g(k) − (1 − δ)k`
falls as capital rises. -/
theorem ex_5_9b_slope [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k k' : Icc (0 : ℝ) K} (hkk' : k ≤ k') :
    (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k').1 -
        (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 ≤ (1 - δ) * (k'.1 - k.1) := by
  obtain ⟨hvs, hUA, -⟩ := ex_5_9b h hv
  have hvc := concaveOn_liftR hvs
  set g := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)
  have hk : k.1 ≤ k'.1 := hkk'
  have hgm := ex_5_9b_mono h hv hkk'
  have hgm' : (g k).1 ≤ (g k').1 := hgm
  by_contra hgt
  push Not at hgt
  set i := (g k).1 - (1 - δ) * k.1 with hi_def
  set i' := (g k').1 - (1 - δ) * k'.1 with hi'_def
  have hii : i < i' := by simp only [i, i']; linarith
  -- the exchanged choices `y₁ = i' + (1 − δ)k` at `k` and `y₂ = i + (1 − δ)k'` at `k'`
  have hy₁ : i' + (1 - δ) * k.1 ∈ Icc (0 : ℝ) K :=
    ⟨by simp only [i']; nlinarith [(g k).2.1, h.δ_lt], by simp only [i']; nlinarith [(g k').2.2,
      h.δ_lt]⟩
  have hy₂ : i + (1 - δ) * k'.1 ∈ Icc (0 : ℝ) K :=
    ⟨by simp only [i]; nlinarith [(g k).2.1, h.δ_lt], by simp only [i]; nlinarith [(g k').2.2,
      h.δ_lt]⟩
  have hne₁ : (⟨_, hy₁⟩ : Icc (0 : ℝ) K) ≠ g k := fun he => by
    have := congrArg Subtype.val he; simp only at this; linarith
  have hne₂ : (⟨_, hy₂⟩ : Icc (0 : ℝ) K) ≠ g k' := fun he => by
    have := congrArg Subtype.val he; simp only at this; linarith
  have e1 := hUA.lt_of_ne (mem_fullΓ k _) hne₁
  have e2 := hUA.lt_of_ne (mem_fullΓ k' _) hne₂
  -- concavity of `v`: `v(gₖ) + v(gₖ') ≤ v(y₁) + v(y₂)`
  have hex := concave_exchange hvc (p := (g k).1) (q := i' + (1 - δ) * k.1)
    (δ := (1 - δ) * (k'.1 - k.1)) (g k).2 (by
      rw [show i' + (1 - δ) * k.1 + (1 - δ) * (k'.1 - k.1) = (g k').1 by simp only [i']; ring]
      exact (g k').2) (by simp only [i, i'] at hii ⊢; linarith) (by nlinarith [h.δ_lt])
  rw [show i' + (1 - δ) * k.1 + (1 - δ) * (k'.1 - k.1) = (g k').1 by simp only [i']; ring,
    show (g k).1 + (1 - δ) * (k'.1 - k.1) = i + (1 - δ) * k'.1 by simp only [i]; ring,
    liftR_of_mem v (g k).2, liftR_of_mem v (g k').2, liftR_of_mem v hy₁,
    liftR_of_mem v hy₂] at hex
  simp only [Subtype.coe_eta] at hex
  simp only [obj, adjF] at e1 e2
  have r1 : i' + (1 - δ) * k.1 - (1 - δ) * k.1 = i' := by ring
  have r2 : i + (1 - δ) * k'.1 - (1 - δ) * k'.1 = i := by ring
  rw [r1] at e1
  rw [r2] at e2
  have hβ := h.β_pos
  nlinarith

/-- **Exercise 5.9b (envelope condition).** At an interior `k₀`,
`v'(k₀) = pf'(k₀) + (1 − δ)c'(g(k₀) − (1 − δ)k₀)`. -/
theorem ex_5_9b_envelope [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k₀ : Icc (0 : ℝ) K} (hk₀ : k₀.1 ∈ Ioo 0 K) {f' c' : ℝ}
    (hf' : HasDerivAt f f' k₀.1)
    (hc' : HasDerivAt c c' ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k₀).1 -
      (1 - δ) * k₀.1)) :
    HasDerivAt (liftR K v) (p * f' + (1 - δ) * c') k₀.1 := by
  obtain ⟨hvs, hUA, -⟩ := ex_5_9b h hv
  set g₀ := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k₀
  have hX : Icc (0 : ℝ) K ∈ 𝓝 k₀.1 := Icc_mem_nhds hk₀.1 hk₀.2
  set W : ℝ → ℝ := fun x => p * f x - c (g₀.1 - (1 - δ) * x) + β * v g₀
  have hW : HasDerivAt W (p * f' + (1 - δ) * c') k₀.1 := by
    have h2 : HasDerivAt (fun x => p * f x - c (g₀.1 - (1 - δ) * x) + β * v g₀)
        (p * f' - c' * (0 - (1 - δ) * 1)) k₀.1 :=
      ((hf'.const_mul p).sub (hc'.comp k₀.1 ((hasDerivAt_const k₀.1 g₀.1).sub
        ((hasDerivAt_id' k₀.1).const_mul (1 - δ))))).add_const (β * v g₀)
    convert h2 using 1
    ring
  have hvx : ∀ x, v x = maxValue (obj (adjF f c p δ K) β v) (fullΓ K) x := fun x => by
    rw [← bellman_apply h.h43 h.h44, hv]
  have heq : W k₀.1 = liftR K v k₀.1 := by
    rw [liftR_of_mem v k₀.2, Subtype.coe_eta, hvx k₀]
    exact (hUA.argmaxFn_mem k₀).2
  have hle : ∀ᶠ x in 𝓝 k₀.1, W x ≤ liftR K v x := by
    filter_upwards [hX] with x hx
    rw [liftR_of_mem v hx, hvx]
    exact le_maxValue (x := ⟨x, hx⟩) (z := g₀) (continuousOn_obj h.h44 v.continuous)
      (h.h43.compact _) (mem_fullΓ _ g₀)
  have := (theorem_4_10 (concaveOn_liftR hvs) hX hW.hasFDerivAt heq hle).hasDerivAt
  simpa using this

/-- **Exercise 5.9b (first-order condition).** At an interior `g(k)`,
`c'(g(k) − (1 − δ)k) = βv'(g(k))`. -/
theorem ex_5_9b_foc [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k : Icc (0 : ℝ) K}
    (hg : (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 ∈ Ioo 0 K) {c' v' : ℝ}
    (hc' : HasDerivAt c c' ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 -
      (1 - δ) * k.1))
    (hv' : HasDerivAt (liftR K v) v' (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1) :
    c' = β * v' := by
  obtain ⟨-, hUA, -⟩ := ex_5_9b h hv
  set g₀ := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k
  set Φ : ℝ → ℝ := fun y => -c (y - (1 - δ) * k.1) + β * liftR K v y
  have hΦ : HasDerivAt Φ (-(c' * 1) + β * v') g₀.1 :=
    (hc'.comp g₀.1 ((hasDerivAt_id' g₀.1).sub_const ((1 - δ) * k.1))).neg.add
      (hv'.const_mul β)
  have hloc : IsLocalMax Φ g₀.1 := by
    filter_upwards [Icc_mem_nhds hg.1 hg.2] with y hy
    have hmem := (hUA.argmaxFn_mem k)
    have hle := le_maxValue (continuousOn_obj h.h44 v.continuous) (h.h43.compact k)
      (mem_fullΓ k ⟨y, hy⟩)
    rw [← hmem.2] at hle
    simp only [obj, adjF, Φ, liftR_of_mem v hy, liftR_of_mem v g₀.2, Subtype.coe_eta] at hle ⊢
    linarith
  have := hloc.hasDerivAt_eq_zero hΦ
  linarith

/-- **Exercise 5.9b (Euler equation).** With `g(k)` interior and the derivatives below,
`c'(g(k) − (1 − δ)k) = β[pf'(g(k)) + (1 − δ)c'(g(g(k)) − (1 − δ)g(k))]`. -/
theorem ex_5_9b_euler [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k : Icc (0 : ℝ) K}
    (hg : (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 ∈ Ioo 0 K) {f' c₀ c₁ : ℝ}
    (hf' : HasDerivAt f f' (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1)
    (hc₀ : HasDerivAt c c₀ ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 -
      (1 - δ) * k.1))
    (hc₁ : HasDerivAt c c₁ ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)
      (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k)).1 -
      (1 - δ) * (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1)) :
    c₀ = β * (p * f' + (1 - δ) * c₁) :=
  ex_5_9b_foc h hv hg hc₀ (ex_5_9b_envelope h hv hg hf' hc₁)

/-- **Exercise 5.9b (steady state).** At an interior steady state `g(k*) = k*`,
`c'(δk*)(1 − β(1 − δ)) = βpf'(k*)`. -/
theorem ex_5_9b_steady [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k : Icc (0 : ℝ) K}
    (hss : argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k = k) (hk : k.1 ∈ Ioo 0 K)
    {f' c' : ℝ} (hf' : HasDerivAt f f' k.1) (hc' : HasDerivAt c c' (δ * k.1)) :
    c' * (1 - β * (1 - δ)) = β * p * f' := by
  have e : (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 - (1 - δ) * k.1 = δ * k.1 := by
    rw [hss]; ring
  have hc'' : HasDerivAt c c' ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 -
      (1 - δ) * k.1) := e ▸ hc'
  have e2 : k.1 - (1 - δ) * k.1 = δ * k.1 := by ring
  have := ex_5_9b_euler h hv (k := k) (by rw [hss]; exact hk) (by rw [hss]; exact hf') hc''
    (by rw [hss, hss, e2]; exact hc')
  linarith

/-! ### Exercise 5.9c: short-run profits -/

/-- `Π(k) = sup_{l ≥ 0} [pF(k, l) − wl]`. -/
noncomputable def profitPi (F : ℝ → ℝ → ℝ) (p w k : ℝ) : ℝ :=
  sSup ((fun l => p * F k l - w * l) '' Ici 0)

variable {F : ℝ → ℝ → ℝ} {w : ℝ}

/-- `Π(k)` equals the profit at a profit-maximizing labour input. -/
theorem profitPi_eq {k l : ℝ} (hl : 0 ≤ l)
    (hmax : ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l) :
    profitPi F p w k = p * F k l - w * l :=
  le_antisymm (csSup_le ⟨_, 0, mem_Ici.2 le_rfl, rfl⟩
    (by rintro _ ⟨l', hl', rfl⟩; exact hmax l' hl'))
    (le_csSup ⟨_, by rintro _ ⟨l', hl', rfl⟩; exact hmax l' hl'⟩ ⟨l, hl, rfl⟩)

/-- **Exercise 5.9c.** Labour demand exists if `F(k, ·)` is continuous with `F(k, l)/l → 0`. -/
theorem labor_demand_exists {k : ℝ} (hw : 0 < w) (hc : ContinuousOn (F k) (Ici 0))
    (hsub : Tendsto (fun l => F k l / l) atTop (𝓝 0)) :
    ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l := by
  have := exists_max_sublinear (g := fun l => p * F k l) (continuousOn_const.mul hc)
    (by simpa [mul_div_assoc] using hsub.const_mul p) hw
  simpa using this

/-- **Exercise 5.9c.** Labour demand is unique if `F(k, ·)` is strictly concave. -/
theorem labor_demand_unique {k l₁ l₂ : ℝ} (hp : 0 < p) (hF : StrictConcaveOn ℝ (Ici 0) (F k))
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hm₁ : ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l₁ - w * l₁)
    (hm₂ : ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l₂ - w * l₂) : l₁ = l₂ := by
  by_contra hne
  have hs := hF.2 (mem_Ici.2 h₁) (mem_Ici.2 h₂) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hs
  have e1 := hm₁ (1 / 2 * l₁ + 1 / 2 * l₂) (by positivity)
  have e2 := hm₂ l₁ h₁
  have e3 := hm₁ l₂ h₂
  nlinarith

/-- **Exercise 5.9c.** `Π(0) = 0` if `F(0, l) = 0` for all `l` and `w ≥ 0`. -/
theorem profitPi_zero (hw : 0 ≤ w) (hF0 : ∀ l, F 0 l = 0) : profitPi F p w 0 = 0 := by
  have := profitPi_eq (F := F) (p := p) (w := w) (k := 0) (l := 0) le_rfl fun l' hl' => by
    simp only [hF0, mul_zero, zero_sub, sub_zero]; nlinarith
  simpa [hF0] using this

/-- **Exercise 5.9c.** `Π` is nondecreasing if `F` is nondecreasing in `k` and `p ≥ 0`. -/
theorem profitPi_mono (hp : 0 ≤ p) (hF : ∀ l, 0 ≤ l → Monotone fun k => F k l)
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l)
    {k k' : ℝ} (hk : 0 ≤ k) (hkk' : k ≤ k') : profitPi F p w k ≤ profitPi F p w k' := by
  obtain ⟨l, hl, hlmax⟩ := hmax k hk
  obtain ⟨l', hl', hl'max⟩ := hmax k' (hk.trans hkk')
  rw [profitPi_eq hl hlmax, profitPi_eq hl' hl'max]
  have := hl'max l hl
  have := mul_le_mul_of_nonneg_left (hF l hl hkk') hp
  linarith

/-- **Exercise 5.9c.** `Π` is concave if `F` is jointly concave and `p ≥ 0`. -/
theorem profitPi_concave (hp : 0 ≤ p) (hF : ConcaveOn ℝ (Set.Ici 0 ×ˢ Set.Ici 0) fun z => F z.1 z.2)
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l) :
    ConcaveOn ℝ (Ici 0) (profitPi F p w) := by
  refine ⟨convex_Ici 0, fun k hk k' hk' s t hs ht hst => ?_⟩
  obtain ⟨l, hl, hlmax⟩ := hmax k hk
  obtain ⟨l', hl', hl'max⟩ := hmax k' hk'
  obtain ⟨lθ, hlθ, hlθmax⟩ := hmax (s • k + t • k') ((convex_Ici 0) hk hk' hs ht hst)
  rw [profitPi_eq hl hlmax, profitPi_eq hl' hl'max, profitPi_eq hlθ hlθmax]
  have hFc := hF.2 (show (k, l) ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk, hl⟩)
    (show (k', l') ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk', hl'⟩) hs ht hst
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hFc ⊢
  have hle := hlθmax (s * l + t * l') (by positivity)
  simp only [smul_eq_mul] at hle
  have := mul_le_mul_of_nonneg_left hFc hp
  nlinarith

/-- **Exercise 5.9c.** `Π` is strictly concave if `F` is jointly strictly concave and `p > 0`. -/
theorem profitPi_strictConcave (hp : 0 < p)
    (hF : StrictConcaveOn ℝ (Set.Ici 0 ×ˢ Set.Ici 0) fun z => F z.1 z.2)
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l) :
    StrictConcaveOn ℝ (Ici 0) (profitPi F p w) := by
  refine ⟨convex_Ici 0, fun k hk k' hk' hne s t hs ht hst => ?_⟩
  obtain ⟨l, hl, hlmax⟩ := hmax k hk
  obtain ⟨l', hl', hl'max⟩ := hmax k' hk'
  obtain ⟨lθ, hlθ, hlθmax⟩ := hmax (s • k + t • k') ((convex_Ici 0) hk hk' hs.le ht.le hst)
  rw [profitPi_eq hl hlmax, profitPi_eq hl' hl'max, profitPi_eq hlθ hlθmax]
  have hne' : (k, l) ≠ (k', l') := fun he => hne (congrArg Prod.fst he)
  have hFc := hF.2 (show (k, l) ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk, hl⟩)
    (show (k', l') ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk', hl'⟩) hne' hs ht hst
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hFc ⊢
  have hle := hlθmax (s * l + t * l') (by positivity)
  simp only [smul_eq_mul] at hle
  have := mul_lt_mul_of_pos_left hFc hp
  nlinarith

/-- **Exercise 5.9c (envelope).** If `Π` is concave and `F(·, l₀)` is differentiable at an
interior `k₀`, where `l₀` is the labour demand, then `Π'(k₀) = pF_k(k₀, l₀)`. -/
theorem profitPi_deriv {k₀ l₀ Fk : ℝ} (hk₀ : 0 < k₀) (hl₀ : 0 ≤ l₀)
    (hconc : ConcaveOn ℝ (Ici 0) (profitPi F p w))
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l)
    (hl₀max : ∀ l', 0 ≤ l' → p * F k₀ l' - w * l' ≤ p * F k₀ l₀ - w * l₀)
    (hFk : HasDerivAt (fun k => F k l₀) Fk k₀) :
    HasDerivAt (profitPi F p w) (p * Fk) k₀ := by
  set W : ℝ → ℝ := fun k => p * F k l₀ - w * l₀
  have hW : HasDerivAt W (p * Fk) k₀ := (hFk.const_mul p).sub_const _
  have heq : W k₀ = profitPi F p w k₀ := (profitPi_eq hl₀ hl₀max).symm
  have hle : ∀ᶠ k in 𝓝 k₀, W k ≤ profitPi F p w k := by
    filter_upwards [Ici_mem_nhds hk₀] with k hk
    obtain ⟨l, hl, hlmax⟩ := hmax k hk
    rw [profitPi_eq hl hlmax]
    exact hlmax l₀ hl₀
  have := (theorem_4_10 hconc (Ici_mem_nhds hk₀) hW.hasFDerivAt heq hle).hasDerivAt
  simpa using this

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive preferences

SLP §5.11, pp. 114–116. `L` is the space of bounded sequences `c = (c₀, c₁, …)` in `ℝˡ₊` with the
sup norm (`Seq l`; on `ℝˡ` Lean's norm is the max norm, equivalent to the book's Euclidean
norm), and `S = C(L)` is the space of bounded continuous `u : L → ℝ`. `₁c = (c₁, c₂, …)` is the
shift (`shiftSeq`) and `cⁿ = (c₀, …, cₙ, 0, 0, …)` the truncation (`trunc`).

* **Exercise 5.11a, c** (`ex_5_11a`, `ex_5_11c`): `(Tu)(c) = U(c₀) + βu(₁c)` is a contraction on
  `S`, and its fixed point is `û(c) = Σ βᵗU(c_t)`; so `û` is bounded (by `M/(1 − β)`) and
  continuous.
* **Exercise 5.11b**: `S` is complete (`ex_5_11b_complete`); but `u(cⁿ) → u(c)` fails for some
  `u ∈ S` (`ex_5_11b_counterexample`: `u(c) = min{1, dist(c, sequences that are eventually 0)}`
  has `u(1) = 1` and `u(1ⁿ) = 0`). The manual's example `inf_t c_t` is not bounded, so it is not
  in `S`.
* **Exercise 5.11d** (`ex_5_11d`): for an aggregator `W` with (W1)–(W3), `T_W u(c) = W[c₀, u(₁c)]`
  has a unique fixed point `u_W`, with `|u_W(c) − u_W(cⁿ)| ≤ βⁿ⁺¹‖u_W‖ ≤ βⁿ‖u_W‖`; (W4) makes `u_W`
  increasing (`ex_5_11d_mono`); (W5) makes it concave (`ex_5_11d_concave`). For (W5) monotonicity
  of `W` is not needed: a nonnegative concave function on `[0, ∞)` is nondecreasing
  (`monotoneOn_of_concave_nonneg`).
* **Exercise 5.11e** (`ex_5_11e`): raising `c_{it}` by `h ≥ 0` changes utility at the rate
  `[∏_{s < t} W_z(c_s, u_W(ₛ₊₁c))] · W_{x_i}(c_t, u_W(ₜ₊₁c))`. The marginal rate of substitution
  between `c_{it}` and `c_{j,t+k}` is the ratio of two such rates, with the product
  `∏_{s=t}^{t+k−1} W_z(c_s, u_W(ₛ₊₁c))`; the manual's formula keeps a single `W_z` factor.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ}

/-- The set of bounded sequences in `ℝˡ₊`. -/
def seqSet (l : ℕ) : Set (ℕ →ᵇ (Fin l → ℝ)) := {c | ∀ t, 0 ≤ c t}

/-- `L`: bounded sequences in `ℝˡ₊`. -/
abbrev Seq (l : ℕ) := ↥(seqSet l)

theorem convex_seqSet : Convex ℝ (seqSet l) := fun c hc c' hc' a b ha hb _ t => by
  simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.coe_smul]
  exact add_nonneg (smul_nonneg ha (hc t)) (smul_nonneg hb (hc' t))

/-- The shift `₁c = (c₁, c₂, …)`. -/
def shiftSeq (c : Seq l) : Seq l :=
  ⟨c.1.compContinuous ⟨fun t => t + 1, continuous_of_discreteTopology⟩, fun t => c.2 (t + 1)⟩

@[simp] theorem shiftSeq_apply (c : Seq l) (t : ℕ) : (shiftSeq c).1 t = c.1 (t + 1) := rfl

theorem continuous_shiftSeq : Continuous (shiftSeq (l := l)) := by
  refine (LipschitzWith.of_dist_le' (K := 1) fun c c' => ?_).continuous
  rw [one_mul]
  change dist (shiftSeq c).1 (shiftSeq c').1 ≤ dist c.1 c'.1
  exact (dist_le dist_nonneg).2 fun t => dist_coe_le_dist (t + 1)

theorem continuous_head : Continuous fun c : Seq l => c.1 0 :=
  (continuous_eval_const 0).comp continuous_subtype_val

theorem abs_apply_le_norm (u : Seq l →ᵇ ℝ) (c : Seq l) : |u c| ≤ ‖u‖ := by
  simpa [Real.norm_eq_abs] using u.norm_coe_le_norm c

/-- The zero sequence. -/
def zeroSeq : Seq l := ⟨0, fun _ => le_rfl⟩

theorem shiftSeq_zero : shiftSeq (zeroSeq (l := l)) = zeroSeq := Subtype.ext (by ext; rfl)

/-- The truncation `cⁿ = (c₀, …, cₙ, 0, 0, …)`. -/
noncomputable def trunc (n : ℕ) (c : Seq l) : Seq l :=
  ⟨BoundedContinuousFunction.mkOfDiscrete (fun t => if t ≤ n then c.1 t else 0) (2 * ‖c.1‖)
    fun s t => by
      have h0 : ∀ u, ‖(if u ≤ n then c.1 u else 0)‖ ≤ ‖c.1‖ := fun u => by
        split_ifs
        · exact c.1.norm_coe_le_norm u
        · simp
      exact (dist_le_norm_add_norm _ _).trans (by linarith [h0 s, h0 t]),
    fun t => by
      change 0 ≤ (if t ≤ n then c.1 t else 0)
      split_ifs
      · exact c.2 t
      · exact le_rfl⟩

theorem trunc_apply (n : ℕ) (c : Seq l) (t : ℕ) :
    (trunc n c).1 t = if t ≤ n then c.1 t else 0 := rfl

theorem head_trunc (n : ℕ) (c : Seq l) : (trunc n c).1 0 = c.1 0 := by
  simp [trunc_apply]

theorem shiftSeq_trunc_zero (c : Seq l) : shiftSeq (trunc 0 c) = zeroSeq :=
  Subtype.ext (by ext t i; simp [trunc_apply, zeroSeq])

theorem shiftSeq_trunc_succ (n : ℕ) (c : Seq l) :
    shiftSeq (trunc (n + 1) c) = trunc n (shiftSeq c) :=
  Subtype.ext (by ext t i; simp [trunc_apply])

/-! ### Exercise 5.11a–c: additive preferences -/

variable {U : (Fin l → ℝ) → ℝ} {β M : ℝ}

/-- `(Tu)(c) = U(c₀) + βu(₁c)`. -/
noncomputable def opTU (U : (Fin l → ℝ) → ℝ) (hU : Continuous U) (hM : ∀ x, 0 ≤ x → |U x| ≤ M)
    (hβ : 0 ≤ β) (u : Seq l →ᵇ ℝ) : Seq l →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun c => U (c.1 0) + β * u (shiftSeq c))
    ((hU.comp continuous_head).add (continuous_const.mul (u.continuous.comp continuous_shiftSeq)))
    (M + β * ‖u‖) fun c => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add (hM _ (c.2 0)) ?_)
      rw [abs_mul, abs_of_nonneg hβ]
      exact mul_le_mul_of_nonneg_left (abs_apply_le_norm u (shiftSeq c)) hβ

theorem opTU_contraction (hU : Continuous U) (hM : ∀ x, 0 ≤ x → |U x| ≤ M) (hβ0 : 0 < β)
    (hβ1 : β < 1) : IsContraction (opTU (l := l) U hU hM hβ0.le) β := by
  refine ⟨hβ0, hβ1, fun u u' => (dist_le (mul_nonneg hβ0.le dist_nonneg)).2 fun c => ?_⟩
  change dist (U (c.1 0) + β * u (shiftSeq c)) (U (c.1 0) + β * u' (shiftSeq c)) ≤ _
  rw [Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos hβ0]
  exact mul_le_mul_of_nonneg_left (by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := u) (g := u') (shiftSeq c)) hβ0.le

/-- **Exercises 5.11a and 5.11c.** `T` has a unique fixed point `û ∈ S`, and
`û(c) = Σ βᵗU(c_t)`: so `u(c) = Σ βᵗU(c_t)` is bounded and continuous on `L`. -/
theorem ex_5_11c (hU : Continuous U) (hM : ∀ x, 0 ≤ x → |U x| ≤ M) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ uhat : Seq l →ᵇ ℝ, opTU U hU hM hβ0.le uhat = uhat ∧
      (∀ w, opTU U hU hM hβ0.le w = w → w = uhat) ∧
      ∀ c, HasSum (fun t => β ^ t * U (c.1 t)) (uhat c) := by
  obtain ⟨u, hu, huniq, -⟩ := theorem_3_2 (opTU_contraction (l := l) hU hM hβ0 hβ1)
  refine ⟨u, hu, huniq, fun c => ?_⟩
  -- unroll the fixed point: `û(c) = Σ_{t<n} βᵗU(c_t) + βⁿû(ₙc)`
  have hfe : ∀ c, u c = U (c.1 0) + β * u (shiftSeq c) := fun c =>
    (DFunLike.congr_fun hu c).symm
  have hunroll : ∀ (n : ℕ) (c : Seq l), u c = ∑ t ∈ Finset.range n, β ^ t * U (c.1 t) +
      β ^ n * u ((shiftSeq)^[n] c) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [hfe c, ih (shiftSeq c), Finset.sum_range_succ', Function.iterate_succ_apply]
      simp only [shiftSeq_apply]
      have e : β * ∑ t ∈ Finset.range n, β ^ t * U (c.1 (t + 1)) =
          ∑ t ∈ Finset.range n, β ^ (t + 1) * U (c.1 (t + 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [pow_zero, one_mul, pow_succ, ← e]
      ring
  have hsum : Summable fun t => β ^ t * U (c.1 t) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right M)
      fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le t)]
        exact mul_le_mul_of_nonneg_left (hM _ (c.2 t)) (pow_nonneg hβ0.le t)
  have hrest : Tendsto (fun n => β ^ n * u ((shiftSeq)^[n] c)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => ‖u‖ * β ^ n) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le n), mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_apply_le_norm u _) (pow_nonneg hβ0.le n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul ‖u‖
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range n, β ^ t * U (c.1 t)) atTop (𝓝 (u c)) := by
    have := (tendsto_const_nhds (x := u c)).sub hrest
    rw [sub_zero] at this
    exact this.congr fun n => by rw [hunroll n c]; ring
  rw [← tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim]
  exact hsum.hasSum

/-- **Exercise 5.11a.** `|u(c)| ≤ M/(1 − β)`. -/
theorem ex_5_11a (hβ0 : 0 < β) (hβ1 : β < 1) (hM : ∀ x, 0 ≤ x → |U x| ≤ M) {c : Seq l}
    {s : ℝ} (hs : HasSum (fun t => β ^ t * U (c.1 t)) s) : |s| ≤ M / (1 - β) := by
  have hg := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left M
  have := hasSum_le (fun t => (show β ^ t * U (c.1 t) ≤ M * β ^ t by
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hM _ (c.2 t)))
      (pow_nonneg hβ0.le t))) hs hg
  have := hasSum_le (fun t => (show -(M * β ^ t) ≤ β ^ t * U (c.1 t) by
    have := neg_abs_le (U (c.1 t)) |>.trans' (neg_le_neg (hM _ (c.2 t)))
    nlinarith [pow_nonneg hβ0.le t])) hg.neg hs
  rw [abs_le, ← div_eq_mul_inv] at *
  constructor <;> linarith

/-- **Exercise 5.11b.** `S` is complete. -/
theorem ex_5_11b_complete : CompleteSpace (Seq l →ᵇ ℝ) := inferInstance

/-- The sequences that are eventually zero. -/
def eventuallyZero (l : ℕ) : Set (Seq l) := {e | ∃ N, ∀ t, N < t → e.1 t = 0}

/-- **Exercise 5.11b.** `u(cⁿ) → u(c)` can fail: `u(c) = min{1, dist(c, eventually zero)}` is in
`S`, and the constant sequence `1` has `|u(1) − u(1ⁿ)| = 1` for every `n`. -/
theorem ex_5_11b_counterexample (hl : 0 < l) :
    ∃ u : Seq l →ᵇ ℝ, ∃ c : Seq l, ∀ n, |u c - u (trunc n c)| = 1 := by
  have : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  set u : Seq l →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun c => min (Metric.infDist c (eventuallyZero l)) 1)
    ((Metric.continuous_infDist_pt _).min continuous_const) 1 fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min Metric.infDist_nonneg zero_le_one)]
      exact min_le_right _ _
  set c : Seq l := ⟨BoundedContinuousFunction.const ℕ 1, fun _ => zero_le_one⟩
  have hne : (eventuallyZero l).Nonempty := ⟨zeroSeq, 0, fun _ _ => rfl⟩
  have hc : u c = 1 := by
    change min (Metric.infDist c (eventuallyZero l)) 1 = 1
    refine min_eq_right ((Metric.le_infDist hne).2 fun e ⟨N, hN⟩ => ?_)
    have h1 := dist_coe_le_dist (f := c.1) (g := e.1) (N + 1)
    rw [hN (N + 1) (Nat.lt_succ_self N)] at h1
    have h2 : dist (c.1 (N + 1)) 0 = 1 := by
      rw [dist_zero_right]
      change ‖fun _ : Fin l => (1 : ℝ)‖ = 1
      rw [pi_norm_const, norm_one]
    rw [h2] at h1
    exact h1
  have htr : ∀ n, u (trunc n c) = 0 := fun n => by
    change min (Metric.infDist (trunc n c) (eventuallyZero l)) 1 = 0
    rw [Metric.infDist_zero_of_mem (show trunc n c ∈ eventuallyZero l from
      ⟨n, fun t ht => by simp [trunc_apply, not_le.2 ht]⟩)]
    simp
  exact ⟨u, c, fun n => by rw [hc, htr]; simp⟩

/-! ### Exercise 5.11d: aggregator functions -/

variable {W : (Fin l → ℝ) → ℝ → ℝ}

/-- (W1)–(W3), with `W(x, ·)` given on all of `ℝ` (for `z ≥ 0` this is the book's `W`). -/
structure AggHyp (W : (Fin l → ℝ) → ℝ → ℝ) (β M : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  cont : Continuous fun p : (Fin l → ℝ) × ℝ => W p.1 p.2
  zero : W 0 0 = 0
  bdd : ∀ x, 0 ≤ x → |W x 0| ≤ M
  lip : ∀ x, 0 ≤ x → ∀ z z', |W x z - W x z'| ≤ β * |z - z'|

/-- `(T_W u)(c) = W[c₀, u(₁c)]`. -/
noncomputable def opTW (h : AggHyp W β M) (u : Seq l →ᵇ ℝ) : Seq l →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun c => W (c.1 0) (u (shiftSeq c)))
    (h.cont.comp (continuous_head.prodMk (u.continuous.comp continuous_shiftSeq)))
    (M + β * ‖u‖) fun c => by
      rw [Real.norm_eq_abs]
      have h1 := h.lip _ (c.2 0) (u (shiftSeq c)) 0
      have h2 := h.bdd _ (c.2 0)
      have h3 : |u (shiftSeq c)| ≤ ‖u‖ := by
        simpa [Real.norm_eq_abs] using u.norm_coe_le_norm (shiftSeq c)
      rw [sub_zero] at h1
      have := abs_sub_abs_le_abs_sub (W (c.1 0) (u (shiftSeq c))) (W (c.1 0) 0)
      nlinarith [h.β_pos]

theorem opTW_apply (h : AggHyp W β M) (u : Seq l →ᵇ ℝ) (c : Seq l) :
    opTW h u c = W (c.1 0) (u (shiftSeq c)) := rfl

theorem opTW_contraction (h : AggHyp W β M) : IsContraction (opTW (l := l) h) β := by
  refine ⟨h.β_pos, h.β_lt, fun u u' => (dist_le (mul_nonneg h.β_pos.le dist_nonneg)).2 fun c => ?_⟩
  rw [opTW_apply, opTW_apply, Real.dist_eq]
  exact (h.lip _ (c.2 0) _ _).trans (mul_le_mul_of_nonneg_left (by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := u) (g := u') (shiftSeq c)) h.β_pos.le)

/-- **Exercise 5.11d.** `T_W` has a unique fixed point `u_W ∈ S`, `u_W(0) = 0`, and
`|u_W(c) − u_W(cⁿ)| ≤ βⁿ⁺¹‖u_W‖ ≤ βⁿ‖u_W‖`. -/
theorem ex_5_11d (h : AggHyp W β M) :
    ∃ uW : Seq l →ᵇ ℝ, opTW h uW = uW ∧ (∀ w, opTW h w = w → w = uW) ∧ uW zeroSeq = 0 ∧
      ∀ n c, |uW c - uW (trunc n c)| ≤ β ^ (n + 1) * ‖uW‖ ∧
        β ^ (n + 1) * ‖uW‖ ≤ β ^ n * ‖uW‖ := by
  obtain ⟨u, hu, huniq, -⟩ := theorem_3_2 (opTW_contraction (l := l) h)
  have hfe : ∀ c, u c = W (c.1 0) (u (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu c).symm
  -- `u(0) = W(0, u(0))` forces `u(0) = 0`
  have hz : u zeroSeq = 0 := by
    have h1 : u zeroSeq = W 0 (u zeroSeq) := by
      have := hfe zeroSeq
      rwa [shiftSeq_zero] at this
    have h2 := h.lip 0 le_rfl (u zeroSeq) 0
    rw [h.zero, sub_zero, sub_zero, ← h1] at h2
    have hb : 0 < 1 - β := by linarith [h.β_lt]
    have h3 : |u zeroSeq| * (1 - β) ≤ 0 := by nlinarith
    have h4 := abs_nonneg (u zeroSeq)
    exact abs_eq_zero.1 (le_antisymm (by nlinarith) h4)
  have hnorm : ∀ c, |u c| ≤ ‖u‖ := abs_apply_le_norm u
  have hbound : ∀ n c, |u c - u (trunc n c)| ≤ β ^ (n + 1) * ‖u‖ := by
    intro n
    induction n with
    | zero =>
      intro c
      rw [hfe c, hfe (trunc 0 c), head_trunc, shiftSeq_trunc_zero, hz, zero_add, pow_one]
      refine (h.lip _ (c.2 0) _ _).trans ?_
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left (hnorm _) h.β_pos.le
    | succ n ih =>
      intro c
      rw [hfe c, hfe (trunc (n + 1) c), head_trunc, shiftSeq_trunc_succ, pow_succ']
      refine (h.lip _ (c.2 0) _ _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih _) h.β_pos.le
  refine ⟨u, hu, huniq, hz, fun n c => ⟨hbound n c, ?_⟩⟩
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg h.β_pos.le n)
    h.β_lt.le) (norm_nonneg _)

/-- **Exercise 5.11d.** Under (W4), `W` increasing, `u_W` is increasing: `c ≤ c'` termwise
implies `u_W(c) ≤ u_W(c')`. -/
theorem ex_5_11d_mono (h : AggHyp W β M)
    (hW4 : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W x z ≤ W x' z') {uW : Seq l →ᵇ ℝ}
    (hu : opTW h uW = uW) {c c' : Seq l} (hcc' : ∀ t, c.1 t ≤ c'.1 t) : uW c ≤ uW c' := by
  have : Nonempty (Seq l →ᵇ ℝ) := ⟨0⟩
  set C' : Set (Seq l →ᵇ ℝ) := {u | ∀ c c' : Seq l, (∀ t, c.1 t ≤ c'.1 t) → u c ≤ u c'}
  have hclosed : IsClosed C' := by
    have : C' = ⋂ c, ⋂ c', ⋂ (_ : ∀ t, c.1 t ≤ c'.1 t), {u : Seq l →ᵇ ℝ | u c ≤ u c'} := by
      ext u; simp [C']
    rw [this]
    exact isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const c) (continuous_eval_const c')
  have hmaps : MapsTo (opTW h) C' C' := fun u hu c c' hcc => by
    rw [opTW_apply, opTW_apply]
    exact hW4 _ _ _ _ (c.2 0) (hcc 0) (hu _ _ fun t => hcc (t + 1))
  exact (corollary_1 (S' := C') (S'' := C') (opTW_contraction h) hu
    ⟨0, fun _ _ _ => le_rfl⟩ hclosed hmaps hmaps).1 c c' hcc'

/-- A nonnegative concave function on `[0, ∞)` is nondecreasing. -/
theorem monotoneOn_of_concave_nonneg {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ)
    (h0 : ∀ z, 0 ≤ z → 0 ≤ φ z) : MonotoneOn φ (Ici 0) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  by_contra hgt
  push Not at hgt
  -- the chord slope `s < 0` from `a` to `b` bounds `φ` beyond `b`
  set s := (φ b - φ a) / (b - a)
  have hs : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  set z := b + (φ b + 1) / (-s)
  have hz : b < z := lt_add_of_pos_right _ (div_pos (by linarith [h0 b hb]) (by linarith))
  have hadj := hφ.slope_anti_adjacent ha (mem_Ici.2 (by linarith [hb.out] : (0 : ℝ) ≤ z))
    hlt hz
  rw [div_le_iff₀ (by linarith)] at hadj
  have hs0 : s ≠ 0 := hs.ne
  have : (φ b + 1) / -s * s = -(φ b + 1) := by field_simp
  have hzb : z - b = (φ b + 1) / -s := by simp only [z]; ring
  rw [hzb] at hadj
  have := h0 z (by linarith [hb.out])
  nlinarith

/-- **Exercise 5.11d.** Under (W5), `W` concave on `ℝˡ₊ × ℝ₊`, with `W ≥ 0` there, `u_W` is
nonnegative and concave. -/
theorem ex_5_11d_concave (h : AggHyp W β M)
    (hW5 : ConcaveOn ℝ ({x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0) fun p => W p.1 p.2)
    (hnn : ∀ x z, 0 ≤ x → 0 ≤ z → 0 ≤ W x z) {uW : Seq l →ᵇ ℝ} (hu : opTW h uW = uW) :
    (∀ c, 0 ≤ uW c) ∧ IsConcaveS convex_seqSet uW := by
  have : Nonempty (Seq l →ᵇ ℝ) := ⟨0⟩
  -- `W(x, ·)` is nondecreasing on `[0, ∞)`
  have hWz : ∀ x, 0 ≤ x → MonotoneOn (W x) (Ici 0) := fun x hx => by
    refine monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
      fun z hz => hnn x z hx hz
    have := hW5.2 (show (x, z) ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from ⟨hx, hz⟩)
      (show (x, z') ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from ⟨hx, hz'⟩) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at this
    exact this
  set C : Set (Seq l →ᵇ ℝ) := {u | (∀ c, 0 ≤ u c) ∧ IsConcaveS convex_seqSet u}
  have hclosed : IsClosed C := by
    have : C = (⋂ c, {u : Seq l →ᵇ ℝ | 0 ≤ u c}) ∩ {u | IsConcaveS convex_seqSet u} := by
      ext u; simp [C]
    rw [this]
    exact (isClosed_iInter fun c => isClosed_le continuous_const (continuous_eval_const c)).inter
      (isClosed_concave convex_seqSet)
  have hshift : ∀ (c c' : Seq l) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      shiftSeq (cmb convex_seqSet h0 h1 c c') =
        cmb convex_seqSet h0 h1 (shiftSeq c) (shiftSeq c') := fun c c' θ h0 h1 =>
    Subtype.ext (by ext t i; rfl)
  have hmaps : MapsTo (opTW h) C C := fun u ⟨hu0, huc⟩ => by
    refine ⟨fun c => hnn _ _ (c.2 0) (hu0 _), fun c c' θ h0 h1 => ?_⟩
    rw [opTW_apply, opTW_apply, opTW_apply, hshift]
    have hc := huc (shiftSeq c) (shiftSeq c') θ h0 h1
    have hmid : 0 ≤ θ * u (shiftSeq c) + (1 - θ) * u (shiftSeq c') :=
      add_nonneg (mul_nonneg h0 (hu0 _)) (mul_nonneg (by linarith) (hu0 _))
    have hWc := hW5.2 (show (c.1 0, u (shiftSeq c)) ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from
      ⟨c.2 0, hu0 _⟩) (show (c'.1 0, u (shiftSeq c')) ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from
      ⟨c'.2 0, hu0 _⟩) h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hWc
    have hhead : (cmb convex_seqSet h0 h1 c c').1 0 = θ • c.1 0 + (1 - θ) • c'.1 0 := rfl
    rw [hhead]
    refine hWc.trans (hWz _ ?_ (mem_Ici.2 hmid) (mem_Ici.2 (hu0 _)) hc)
    exact (convex_seqSet c.2 c'.2 h0 (by linarith) (by ring) : _) 0
  exact (corollary_1 (S' := C) (S'' := C) (opTW_contraction h) hu
    ⟨0, fun _ => le_rfl, fun _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1

/-! ### Exercise 5.11e: marginal rates of substitution -/

/-- `c` with `h⁺ = max{h, 0}` added to good `i` in period `t`. -/
noncomputable def bump (c : Seq l) (t : ℕ) (i : Fin l) (h : ℝ) : Seq l :=
  ⟨c.1 + BoundedContinuousFunction.mkOfDiscrete
      (fun s => if s = t then Pi.single i (max h 0) else (0 : Fin l → ℝ))
      (2 * ‖(Pi.single i (max h 0) : Fin l → ℝ)‖) fun s s' => by
        refine (dist_le_norm_add_norm _ _).trans ?_
        have : ∀ u, ‖(if u = t then Pi.single i (max h 0) else (0 : Fin l → ℝ))‖ ≤
            ‖(Pi.single i (max h 0) : Fin l → ℝ)‖ := fun u => by
          split_ifs <;> simp
        linarith [this s, this s'],
    fun s => by
      change 0 ≤ c.1 s + (if s = t then Pi.single i (max h 0) else (0 : Fin l → ℝ))
      refine add_nonneg (c.2 s) ?_
      split_ifs
      · intro j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      · exact le_rfl⟩

theorem shiftSeq_bump_zero (c : Seq l) (i : Fin l) (h : ℝ) :
    shiftSeq (bump c 0 i h) = shiftSeq c :=
  Subtype.ext (by ext s j; simp [bump])

theorem shiftSeq_bump_succ (c : Seq l) (t : ℕ) (i : Fin l) (h : ℝ) :
    shiftSeq (bump c (t + 1) i h) = bump (shiftSeq c) t i h :=
  Subtype.ext (by ext s j; simp [bump])

theorem head_bump_zero (c : Seq l) (i : Fin l) (h : ℝ) :
    (bump c 0 i h).1 0 = c.1 0 + Pi.single i (max h 0) := by
  simp [bump]

theorem head_bump_succ (c : Seq l) (t : ℕ) (i : Fin l) (h : ℝ) :
    (bump c (t + 1) i h).1 0 = c.1 0 := by
  simp [bump]

/-- **Exercise 5.11e.** Raising good `i` in period `t` by `h ≥ 0` changes `u_W` at the rate
`[∏_{s<t} W_z(c_s, u_W(ₛ₊₁c))] · W_{x_i}(c_t, u_W(ₜ₊₁c))`. The marginal rate of substitution
between `c_{it}` and `c_{j,t+k}` is the ratio of two such rates. -/
theorem ex_5_11e (h : AggHyp W β M) {uW : Seq l →ᵇ ℝ} (hu : opTW h uW = uW) (t : ℕ)
    (i : Fin l) (c : Seq l) {Wz : ℕ → ℝ} {Wx : ℝ}
    (hz : ∀ s < t, HasDerivAt (W (c.1 s)) (Wz s) (uW ((shiftSeq)^[s + 1] c)))
    (hx : HasDerivAt (fun h => W (c.1 t + Pi.single i h) (uW ((shiftSeq)^[t + 1] c))) Wx 0) :
    HasDerivWithinAt (fun h => uW (bump c t i h)) ((∏ s ∈ Finset.range t, Wz s) * Wx)
      (Ici 0) 0 := by
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu c).symm
  induction t generalizing c Wz with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, one_mul]
    refine hx.hasDerivWithinAt.congr (fun h (hh : 0 ≤ h) => ?_) ?_
    · rw [hfe, head_bump_zero, shiftSeq_bump_zero, max_eq_left hh]; rfl
    · rw [hfe, head_bump_zero, shiftSeq_bump_zero, max_self]; rfl
  | succ t ih =>
    -- one level of the recursion: `u_W(c + h e_{i,t+1}) = W(c₀, u_W(₁c + h e_{i,t}))`
    have hshift : ∀ s, (shiftSeq c).1 s = c.1 (s + 1) := fun s => rfl
    have hit : ∀ s, (shiftSeq)^[s + 1] (shiftSeq c) = (shiftSeq)^[s + 2] c := fun s => by
      rw [← Function.iterate_succ_apply]
    have hinner := ih (shiftSeq c) (Wz := fun s => Wz (s + 1))
      (fun s hs => by rw [hshift, hit]; exact hz (s + 1) (by omega))
      (by rw [hshift, hit]; exact hx)
    have houter : HasDerivAt (W (c.1 0)) (Wz 0) (uW (bump (shiftSeq c) t i 0)) := by
      have e : bump (shiftSeq c) t i 0 = (shiftSeq)^[0 + 1] c := Subtype.ext (by
        ext s j; simp [bump])
      rw [e]; exact hz 0 (by omega)
    have := houter.comp_hasDerivWithinAt (0 : ℝ) hinner
    rw [Finset.prod_range_succ']
    refine (this.congr (fun h _ => ?_) ?_).congr_deriv (by ring)
    · simp only [Function.comp_apply]; rw [hfe, head_bump_succ, shiftSeq_bump_succ]
    · simp only [Function.comp_apply]; rw [hfe, head_bump_succ, shiftSeq_bump_succ]

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The consumer with recursive preferences

SLP §5.12, pp. 116–117: with prices `p ∈ ℝˡ₊₊`, `R = 1/(1 + r)` and wealth `A ≥ 0`, the
functional equation is `v(A) = max_{C ∈ Γ(A)} W(C, v[R⁻¹(A − p·C)])`,
`Γ(A) = {C ∈ ℝˡ₊ : p·C ≤ A}`.

* `budget_compact`, `budget_lhc`, `budget_uhc`: `Γ` is compact-valued and continuous.
* **Exercise 5.12b**: `ex_5_12b`: there is a unique bounded continuous solution `v`. With `W`
  concave and nonnegative and strictly concave in `C`, `v` is concave and demand
  `C = φ(p, A)` is a single-valued continuous function (`ex_5_12b_demand`); demand is
  homogeneous of degree zero in `(p, A)` (`ex_5_12b_homogeneous`).
* **Exercise 5.12c**: `ex_5_12c_envelope`: at an interior optimum (`C_i > 0`), `v` is
  differentiable with `v'(A) = W_{C_i}/p_i`, the marginal utility of a dollar spent on good `i`;
  so `W_{C_i}/p_i = W_{C_j}/p_j` for goods consumed (`ex_5_12c_intratemporal`), and
  `ex_5_12c_euler`: a dollar spent today on good `i` is worth what it buys tomorrow,
  `W_{C_i}/p_i = R⁻¹W_z·v'(A')`.
* **Exercise 5.12d**: `ex_5_12d`: with `h` strictly increasing, `W̃(C, a) = h(W[C, h⁻¹(a)])` gives
  the value `h ∘ v` and the same demand. `ex_5_12d_not_aggregator`: `W̃` need not be an aggregator:
  `W(C, z) = z/2` and `h(x) = x/(1 + x)` give `W̃(a) = a/(2 − a)`, which violates (W3).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ}

/-- Wealth `A ≥ 0`. -/
abbrev Wealth := ↥(Ici (0 : ℝ))

/-- `p·C`. -/
def spend (p C : Fin l → ℝ) : ℝ := ∑ i, p i * C i

/-- `Γ(A) = {C ≥ 0 : p·C ≤ A}`. -/
def budgetΓ (p : Fin l → ℝ) (A : Wealth) : Set (Fin l → ℝ) := {C | 0 ≤ C ∧ spend p C ≤ A.1}

/-- Next period's wealth `R⁻¹(A − p·C)`. -/
noncomputable def nextWealth (p : Fin l → ℝ) (R : ℝ) (A : ℝ) (C : Fin l → ℝ) : ℝ :=
  (A - spend p C) / R

/-- `v` on wealth extended to `ℝ` by `v(max{x, 0})`. -/
def vext (v : Wealth → ℝ) (x : ℝ) : ℝ := v ⟨max x 0, mem_Ici.2 (le_max_right _ _)⟩

theorem vext_of_nonneg (v : Wealth → ℝ) {x : ℝ} (hx : 0 ≤ x) : vext v x = v ⟨x, hx⟩ := by
  simp only [vext, max_eq_left hx]

theorem continuous_vext {v : Wealth → ℝ} (hv : Continuous v) : Continuous (vext v) :=
  hv.comp ((continuous_id.max continuous_const).subtype_mk _)

theorem abs_vext_le (v : Wealth →ᵇ ℝ) (x : ℝ) : |vext v x| ≤ ‖v‖ := by
  unfold vext
  simpa [Real.norm_eq_abs] using v.norm_coe_le_norm _

theorem continuous_spend (p : Fin l → ℝ) : Continuous (spend p) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

theorem spend_nonneg {p C : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hC : 0 ≤ C) : 0 ≤ spend p C :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp i).le (hC i)

theorem le_div_of_spend {p C : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hC : 0 ≤ C) {A : ℝ}
    (hs : spend p C ≤ A) (i : Fin l) : C i ≤ A / p i := by
  rw [le_div_iff₀ (hp i), mul_comm]
  exact (Finset.single_le_sum (f := fun j => p j * C j)
    (fun j _ => mul_nonneg (hp j).le (hC j)) (Finset.mem_univ i)).trans hs

theorem norm_le_of_budget {p C : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hC : 0 ≤ C) {A : ℝ}
    (hA : 0 ≤ A) (hs : spend p C ≤ A) : ‖C‖ ≤ ∑ j, A / p j := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => div_nonneg hA (hp j).le)).2
    fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hC i)]
  exact (le_div_of_spend hp hC hs i).trans (Finset.single_le_sum
    (f := fun j => A / p j) (fun j _ => div_nonneg hA (hp j).le) (Finset.mem_univ i))

theorem budget_compact {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (A : Wealth) :
    IsCompact (budgetΓ p A) := by
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_le continuous_const continuous_id).inter
    (isClosed_le (continuous_spend p) continuous_const)) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin l → ℝ)) (r := ∑ j, A.1 / p j)).subset
    fun C hC => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_budget hp hC.1 A.2 hC.2

theorem zero_mem_budget (p : Fin l → ℝ) (A : Wealth) : (0 : Fin l → ℝ) ∈ budgetΓ p A :=
  ⟨le_rfl, by simp [spend, A.2.out]⟩

theorem budget_lhc {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (A : Wealth) : IsLHC (budgetΓ p) A := by
  refine ⟨⟨0, zero_mem_budget p A⟩, fun C hC As hAs => ?_⟩
  have hval := (continuous_subtype_val.tendsto A).comp hAs
  rcases eq_or_lt_of_le A.2.out with hA0 | hApos
  · -- `A = 0` forces `C = 0`
    have hC0 : C = 0 := by
      funext i
      have := le_div_of_spend hp hC.1 hC.2 i
      rw [← hA0, zero_div] at this
      exact le_antisymm this (hC.1 i)
    refine ⟨0, fun _ => 0, fun n _ => zero_mem_budget p _, ?_⟩
    rw [hC0]; exact tendsto_const_nhds
  · -- `Cₙ = min{1, Aₙ/A}·C`
    refine ⟨0, fun n => min 1 ((As n).1 / A.1) • C, fun n _ => ⟨?_, ?_⟩, ?_⟩
    · exact smul_nonneg (le_min zero_le_one (div_nonneg (As n).2.out A.2.out)) hC.1
    · have hlam0 : 0 ≤ min 1 ((As n).1 / A.1) := le_min zero_le_one (div_nonneg (As n).2.out
        A.2.out)
      have e : spend p (min 1 ((As n).1 / A.1) • C) = min 1 ((As n).1 / A.1) * spend p C := by
        simp only [spend, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      calc min 1 ((As n).1 / A.1) * spend p C ≤ min 1 ((As n).1 / A.1) * A.1 :=
            mul_le_mul_of_nonneg_left hC.2 hlam0
        _ ≤ (As n).1 / A.1 * A.1 := mul_le_mul_of_nonneg_right (min_le_right _ _) A.2.out
        _ = (As n).1 := div_mul_cancel₀ _ hApos.ne'
    · have h1 : Tendsto (fun n => min 1 ((As n).1 / A.1)) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).min (hval.div_const A.1)
        rwa [div_self hApos.ne', min_self] at this
      simpa using h1.smul_const C

theorem budget_uhc {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (A : Wealth) : IsUHC (budgetΓ p) A := by
  refine ⟨⟨0, zero_mem_budget p A⟩, fun As hAs Cs hCs => ?_⟩
  have hval := (continuous_subtype_val.tendsto A).comp hAs
  obtain ⟨B, hB⟩ := hval.bddAbove_range
  have hB0 : 0 ≤ B := (As 0).2.out.trans (hB ⟨0, rfl⟩)
  have hmem : ∀ n, Cs n ∈ Metric.closedBall (0 : Fin l → ℝ) (∑ j, B / p j) := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_of_budget hp (hCs n).1 (As n).2.out (hCs n).2).trans
      (Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hB ⟨n, rfl⟩) (hp j).le)
  obtain ⟨C, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  refine ⟨C, ⟨?_, ?_⟩, φ, hφ, hlim⟩
  · exact isClosed_le continuous_const continuous_id |>.mem_of_tendsto hlim
      (Eventually.of_forall fun n => (hCs (φ n)).1)
  · exact le_of_tendsto_of_tendsto (((continuous_spend p).tendsto C).comp hlim)
      (hval.comp hφ.tendsto_atTop) (Eventually.of_forall fun n => (hCs (φ n)).2)

/-! ### The operator -/

/-- The hypotheses for the consumer: prices, interest and an aggregator with (W1)–(W3). -/
structure ConsHyp (W : (Fin l → ℝ) → ℝ → ℝ) (p : Fin l → ℝ) (R β M : ℝ) : Prop where
  p_pos : ∀ i, 0 < p i
  R_pos : 0 < R
  β_pos : 0 < β
  β_lt : β < 1
  cont : Continuous fun q : (Fin l → ℝ) × ℝ => W q.1 q.2
  bdd : ∀ C, 0 ≤ C → |W C 0| ≤ M
  lip : ∀ C, 0 ≤ C → ∀ z z', |W C z - W C z'| ≤ β * |z - z'|

variable {W : (Fin l → ℝ) → ℝ → ℝ} {p : Fin l → ℝ} {R β M : ℝ}

/-- The objective `W(C, v[R⁻¹(A − p·C)])`. -/
noncomputable def consObj (W : (Fin l → ℝ) → ℝ → ℝ) (p : Fin l → ℝ) (R : ℝ) (v : Wealth → ℝ)
    (q : Wealth × (Fin l → ℝ)) : ℝ :=
  W q.2 (vext v (nextWealth p R q.1.1 q.2))

theorem continuous_consObj (h : ConsHyp W p R β M) {v : Wealth → ℝ} (hv : Continuous v) :
    Continuous (consObj W p R v) :=
  h.cont.comp (continuous_snd.prodMk ((continuous_vext hv).comp
    (((continuous_subtype_val.comp continuous_fst).sub ((continuous_spend p).comp
      continuous_snd)).div_const R)))

theorem abs_consObj_le (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) {A : Wealth}
    {C : Fin l → ℝ} (hC : C ∈ budgetΓ p A) : |consObj W p R v (A, C)| ≤ M + β * ‖v‖ := by
  have h1 := h.lip C hC.1 (vext v (nextWealth p R A.1 C)) 0
  have h2 := h.bdd C hC.1
  have h3 : |vext v (nextWealth p R A.1 C)| ≤ ‖v‖ := abs_vext_le v _
  rw [sub_zero] at h1
  have := abs_sub_abs_le_abs_sub (W C (vext v (nextWealth p R A.1 C))) (W C 0)
  simp only [consObj]
  nlinarith [h.β_pos]

theorem consMax_le (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    ‖maxValue (consObj W p R v) (budgetΓ p) A‖ ≤ M + β * ‖v‖ := by
  obtain ⟨C, hC, hval, -⟩ := exists_argmax (continuous_consObj h v.continuous).continuousOn
    (budget_compact h.p_pos A) ⟨0, zero_mem_budget p A⟩
  rw [← hval, Real.norm_eq_abs]
  exact abs_consObj_le h v hC

/-- `(Tv)(A) = max_{C ∈ Γ(A)} W(C, v[R⁻¹(A − p·C)])`. -/
noncomputable def consT (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) : Wealth →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun A => maxValue (consObj W p R v) (budgetΓ p) A)
    (theorem_3_6 (continuous_consObj h v.continuous).continuousOn (budget_compact h.p_pos)
      (budget_lhc h.p_pos) (budget_uhc h.p_pos)).1 (M + β * ‖v‖) (consMax_le h v)

theorem exists_consT_argmax (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    ∃ C ∈ budgetΓ p A, consT h v A = consObj W p R v (A, C) ∧
      ∀ C' ∈ budgetΓ p A, consObj W p R v (A, C') ≤ consT h v A := by
  obtain ⟨C, hC, hval, hmax⟩ := exists_argmax (continuous_consObj h v.continuous).continuousOn
    (budget_compact h.p_pos A) ⟨0, zero_mem_budget p A⟩
  exact ⟨C, hC, hval.symm, fun C' hC' => (hmax C' hC').trans_eq hval⟩

theorem consT_contraction (h : ConsHyp W p R β M) : IsContraction (consT h) β := by
  refine ⟨h.β_pos, h.β_lt, fun v v' => (dist_le (mul_nonneg h.β_pos.le dist_nonneg)).2 fun A => ?_⟩
  obtain ⟨C, hC, hval, -⟩ := exists_consT_argmax h v A
  obtain ⟨C', hC', hval', -⟩ := exists_consT_argmax h v' A
  obtain ⟨-, -, -, hmax⟩ := exists_consT_argmax h v A
  obtain ⟨-, -, -, hmax'⟩ := exists_consT_argmax h v' A
  have hd : ∀ x, |vext v x - vext v' x| ≤ dist v v' := fun x => by
    simpa [Real.dist_eq, vext] using
      dist_coe_le_dist (f := v) (g := v') ⟨max x 0, mem_Ici.2 (le_max_right _ _)⟩
  have e1 := hmax C' hC'
  have e2 := hmax' C hC
  have l1 := h.lip C hC.1 (vext v (nextWealth p R A.1 C)) (vext v' (nextWealth p R A.1 C))
  have l2 := h.lip C' hC'.1 (vext v (nextWealth p R A.1 C')) (vext v' (nextWealth p R A.1 C'))
  have d1 := mul_le_mul_of_nonneg_left (hd (nextWealth p R A.1 C)) h.β_pos.le
  have d2 := mul_le_mul_of_nonneg_left (hd (nextWealth p R A.1 C')) h.β_pos.le
  rw [Real.dist_eq, abs_le]
  simp only [consObj] at hval hval' e1 e2
  constructor
  · rw [abs_le] at l2; linarith [l2.1, l2.2]
  · rw [abs_le] at l1; linarith [l1.1, l1.2]

/-- **Exercise 5.12b.** There is a unique bounded continuous solution `v` of (2). -/
theorem ex_5_12b (h : ConsHyp W p R β M) :
    ∃ v : Wealth →ᵇ ℝ, consT h v = v ∧ ∀ w, consT h w = w → w = v := by
  have : Nonempty (Wealth →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (consT_contraction h)
  exact ⟨v, hv, huniq⟩

/-! ### Concavity and demand -/

/-- With `W` concave and nonnegative on `ℝˡ₊ × ℝ₊`, `T` preserves nonnegative concave functions,
and the fixed point is nonnegative and concave. -/
theorem ex_5_12b_concave (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v) :
    (∀ A, 0 ≤ v A) ∧ IsConcaveS (convex_Ici 0) v := by
  have : Nonempty (Wealth →ᵇ ℝ) := ⟨0⟩
  have hWz : ∀ C, 0 ≤ C → MonotoneOn (W C) (Ici 0) := fun C hC => by
    refine monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
      fun z hz => hnn C z hC hz
    have := hconc.2 (show (C, z) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz⟩)
      (show (C, z') ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz'⟩) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at this
    exact this
  set S : Set (Wealth →ᵇ ℝ) := {u | (∀ A, 0 ≤ u A) ∧ IsConcaveS (convex_Ici 0) u}
  have hclosed : IsClosed S := by
    have : S = (⋂ A, {u : Wealth →ᵇ ℝ | 0 ≤ u A}) ∩ {u | IsConcaveS (convex_Ici 0) u} := by
      ext u; simp [S]
    rw [this]
    exact (isClosed_iInter fun A => isClosed_le continuous_const (continuous_eval_const A)).inter
      (isClosed_concave (convex_Ici 0))
  have hmaps : MapsTo (consT h) S S := fun u ⟨hu0, huc⟩ => by
    refine ⟨fun A => ?_, fun A A' θ h0 h1 => ?_⟩
    · obtain ⟨C, hC, hval, -⟩ := exists_consT_argmax h u A
      rw [hval]
      exact hnn _ _ hC.1 (hu0 ⟨max (nextWealth p R A.1 C) 0, mem_Ici.2 (le_max_right _ _)⟩)
    · obtain ⟨C, hC, hval, -⟩ := exists_consT_argmax h u A
      obtain ⟨C', hC', hval', -⟩ := exists_consT_argmax h u A'
      obtain ⟨-, -, -, hmax⟩ := exists_consT_argmax h u (cmb (convex_Ici 0) h0 h1 A A')
      set Cθ := θ • C + (1 - θ) • C'
      have h1' : (0 : ℝ) ≤ 1 - θ := by linarith
      have hCθ : Cθ ∈ budgetΓ p (cmb (convex_Ici 0) h0 h1 A A') := by
        refine ⟨add_nonneg (smul_nonneg h0 hC.1) (smul_nonneg h1' hC'.1), ?_⟩
        have e : spend p Cθ = θ * spend p C + (1 - θ) * spend p C' := by
          simp only [spend, Cθ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e]
        change _ ≤ θ • A.1 + (1 - θ) • A'.1
        simp only [smul_eq_mul]
        nlinarith [hC.2, hC'.2]
      have hm := hmax Cθ hCθ
      rw [hval, hval']
      refine le_trans ?_ hm
      -- next wealth is the mixture, and `v` is concave there
      have hn : 0 ≤ nextWealth p R A.1 C := div_nonneg (by linarith [hC.2]) h.R_pos.le
      have hn' : 0 ≤ nextWealth p R A'.1 C' := div_nonneg (by linarith [hC'.2]) h.R_pos.le
      have hmix : nextWealth p R (cmb (convex_Ici 0) h0 h1 A A').1 Cθ =
          θ * nextWealth p R A.1 C + (1 - θ) * nextWealth p R A'.1 C' := by
        have e : spend p Cθ = θ * spend p C + (1 - θ) * spend p C' := by
          simp only [spend, Cθ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        simp only [nextWealth, cmb, smul_eq_mul, e]
        field_simp
        ring
      have hvc := huc ⟨_, hn⟩ ⟨_, hn'⟩ θ h0 h1
      have hmixnn : 0 ≤ θ * nextWealth p R A.1 C + (1 - θ) * nextWealth p R A'.1 C' :=
        add_nonneg (mul_nonneg h0 hn) (mul_nonneg h1' hn')
      simp only [consObj, hmix, vext_of_nonneg u hn, vext_of_nonneg u hn',
        vext_of_nonneg u hmixnn]
      have hcm : cmb (convex_Ici 0) h0 h1 (⟨_, hn⟩ : Wealth) ⟨_, hn'⟩ =
          ⟨_, hmixnn⟩ := Subtype.ext (by simp [cmb])
      rw [hcm] at hvc
      have hWc := hconc.2 (show (C, u ⟨_, hn⟩) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from
        ⟨hC.1, hu0 _⟩) (show (C', u ⟨_, hn'⟩) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from
        ⟨hC'.1, hu0 _⟩) h0 h1' (by ring)
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hWc
      exact hWc.trans (hWz _ hCθ.1 (mem_Ici.2 (add_nonneg (mul_nonneg h0 (hu0 _))
        (mul_nonneg h1' (hu0 _)))) (mem_Ici.2 (hu0 _)) hvc)
  exact (corollary_1 (S' := S) (S'' := S) (consT_contraction h) hv
    ⟨0, fun _ => le_rfl, fun _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1

/-- **Exercise 5.12b.** If moreover `W` is strictly concave in `C` (strictly when `C ≠ C'`), demand
is single-valued and continuous in `A`. -/
theorem ex_5_12b_demand [Nonempty (Fin l → ℝ)] (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hstrict : ∀ C C' : Fin l → ℝ, 0 ≤ C → 0 ≤ C' → C ≠ C' → ∀ z z', 0 ≤ z → 0 ≤ z' →
      W ((1 / 2 : ℝ) • C + (1 / 2 : ℝ) • C') ((1 / 2) * z + (1 / 2) * z') >
        (1 / 2) * W C z + (1 / 2) * W C' z')
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v) :
    UniqueArgmax (budgetΓ p) (consObj W p R v) ∧
      Continuous (argmaxFn (budgetΓ p) (consObj W p R v)) := by
  obtain ⟨hv0, hvc⟩ := ex_5_12b_concave h hconc hnn hv
  have hWz : ∀ C, 0 ≤ C → MonotoneOn (W C) (Ici 0) := fun C hC => by
    refine monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
      fun z hz => hnn C z hC hz
    have := hconc.2 (show (C, z) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz⟩)
      (show (C, z') ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz'⟩) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at this
    exact this
  have huniq : ∀ A, ∀ C₁ ∈ argmax (consObj W p R v) (budgetΓ p) A,
      ∀ C₂ ∈ argmax (consObj W p R v) (budgetΓ p) A, C₁ = C₂ := by
    intro A C₁ hC₁ C₂ hC₂
    by_contra hne
    set Cm := (1 / 2 : ℝ) • C₁ + (1 / 2 : ℝ) • C₂
    have hs : spend p Cm = 1 / 2 * spend p C₁ + 1 / 2 * spend p C₂ := by
      simp only [spend, Cm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hCm : Cm ∈ budgetΓ p A := ⟨add_nonneg (smul_nonneg (by norm_num) hC₁.1.1)
      (smul_nonneg (by norm_num) hC₂.1.1), by rw [hs]; linarith [hC₁.1.2, hC₂.1.2]⟩
    have hn₁ : 0 ≤ nextWealth p R A.1 C₁ := div_nonneg (by linarith [hC₁.1.2]) h.R_pos.le
    have hn₂ : 0 ≤ nextWealth p R A.1 C₂ := div_nonneg (by linarith [hC₂.1.2]) h.R_pos.le
    have hmix : nextWealth p R A.1 Cm =
        1 / 2 * nextWealth p R A.1 C₁ + 1 / 2 * nextWealth p R A.1 C₂ := by
      simp only [nextWealth, hs]; field_simp; ring
    have hmn : 0 ≤ 1 / 2 * nextWealth p R A.1 C₁ + 1 / 2 * nextWealth p R A.1 C₂ := by positivity
    have hvm := hvc ⟨_, hn₁⟩ ⟨_, hn₂⟩ (1 / 2) (by norm_num) (by norm_num)
    have hcm : cmb (convex_Ici 0) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (⟨_, hn₁⟩ : Wealth) ⟨_, hn₂⟩ = ⟨_, hmn⟩ :=
      Subtype.ext (by simp only [cmb, smul_eq_mul]; ring)
    rw [hcm] at hvm
    have hle := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos A) hCm
    have e1 := hC₁.2
    have e2 := hC₂.2
    simp only [consObj, hmix, vext_of_nonneg v hn₁, vext_of_nonneg v hn₂,
      vext_of_nonneg v hmn] at hle e1 e2
    have hst := hstrict C₁ C₂ hC₁.1.1 hC₂.1.1 hne _ _ (hv0 ⟨_, hn₁⟩) (hv0 ⟨_, hn₂⟩)
    have hz0 : 0 ≤ 1 / 2 * v ⟨_, hn₁⟩ + 1 / 2 * v ⟨_, hn₂⟩ :=
      add_nonneg (mul_nonneg (by norm_num) (hv0 _)) (mul_nonneg (by norm_num) (hv0 _))
    have hvm' : 1 / 2 * v ⟨_, hn₁⟩ + 1 / 2 * v ⟨_, hn₂⟩ ≤ v ⟨_, hmn⟩ := by
      have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [this] at hvm
      exact hvm
    have hmono := hWz Cm hCm.1 (mem_Ici.2 hz0) (mem_Ici.2 (hv0 _)) hvm'
    linarith
  have hUA : UniqueArgmax (budgetΓ p) (consObj W p R v) :=
    ⟨fun A => ⟨0, zero_mem_budget p A⟩, budget_compact h.p_pos, budget_lhc h.p_pos,
      budget_uhc h.p_pos, (continuous_consObj h v.continuous).continuousOn, huniq⟩
  exact ⟨hUA, hUA.continuous_argmaxFn⟩


/-! ### Homogeneity of degree zero -/

theorem ConsHyp.smul (h : ConsHyp W p R β M) {lam : ℝ} (hlam : 0 < lam) :
    ConsHyp W (lam • p) R β M :=
  ⟨fun i => by simpa using mul_pos hlam (h.p_pos i), h.R_pos, h.β_pos, h.β_lt, h.cont, h.bdd,
    h.lip⟩

theorem spend_smul (lam : ℝ) (p C : Fin l → ℝ) : spend (lam • p) C = lam * spend p C := by
  simp only [spend, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `A ↦ A/λ` on wealth. -/
noncomputable def scaleW (lam : ℝ) (hlam : 0 < lam) (A : Wealth) : Wealth :=
  ⟨A.1 / lam, mem_Ici.2 (div_nonneg A.2.out hlam.le)⟩

/-- **Exercise 5.12b.** Demand is homogeneous of degree zero in `(p, A)`: scaling prices and
wealth by `λ > 0` scales nothing. The value for `λp` is `A ↦ v(A/λ)`, the budget sets agree and
the objectives agree, so the demand correspondences coincide. -/
theorem ex_5_12b_homogeneous (h : ConsHyp W p R β M) {lam : ℝ} (hlam : 0 < lam)
    {v v' : Wealth →ᵇ ℝ} (hv : consT h v = v) (hv' : consT (h.smul hlam) v' = v')
    (A : Wealth) :
    v' A = v (scaleW lam hlam A) ∧ budgetΓ (lam • p) A = budgetΓ p (scaleW lam hlam A) ∧
      ∀ C, consObj W (lam • p) R v' (A, C) = consObj W p R v (scaleW lam hlam A, C) := by
  -- `w(A) = v(A/λ)` is a fixed point of the operator for `λp`
  set w : Wealth →ᵇ ℝ := v.compContinuous ⟨scaleW lam hlam,
    ((continuous_subtype_val.div_const lam).subtype_mk _)⟩
  have hw : ∀ A, w A = v (scaleW lam hlam A) := fun A => by
    simp only [w, BoundedContinuousFunction.compContinuous_apply]
    rfl
  have hΓ : ∀ A, budgetΓ (lam • p) A = budgetΓ p (scaleW lam hlam A) := fun A => by
    ext C
    simp only [budgetΓ, mem_ofPred_eq, spend_smul, scaleW]
    rw [le_div_iff₀ hlam, mul_comm]
  have hobj : ∀ (u : Wealth → ℝ) A C, consObj W (lam • p) R (fun B => u (scaleW lam hlam B))
      (A, C) = consObj W p R u (scaleW lam hlam A, C) := fun u A C => by
    simp only [consObj, vext, nextWealth, spend_smul, scaleW]
    congr 2
    refine Subtype.ext ?_
    simp only
    rw [← max_div_div_right hlam.le, zero_div]
    congr 1
    field_simp
  have hfix : consT (h.smul hlam) w = w := by
    ext A
    change maxValue (consObj W (lam • p) R w) (budgetΓ (lam • p)) A = w A
    rw [hw, ← hv]
    change _ = maxValue (consObj W p R v) (budgetΓ p) (scaleW lam hlam A)
    unfold maxValue
    rw [hΓ A]
    exact congrArg sSup (Set.image_congr fun C _ => hobj v A C)
  have hvw : v' = w := by
    have : Nonempty (Wealth →ᵇ ℝ) := ⟨0⟩
    obtain ⟨u, -, huniq, -⟩ := theorem_3_2 (consT_contraction (h.smul hlam))
    rw [huniq v' hv', huniq w hfix]
  refine ⟨by rw [hvw]; exact hw A, hΓ A, fun C => ?_⟩
  rw [hvw]
  exact hobj v A C

/-! ### Exercise 5.12c: differentiability and first-order conditions -/

theorem spend_add_smul_single (p C : Fin l → ℝ) (i : Fin l) (x : ℝ) :
    spend p (C + x • Pi.single i 1) = spend p C + p i * x := by
  simp only [spend, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- `vext v` is concave on `[0, ∞)` when `v` is. -/
theorem concaveOn_vext {v : Wealth → ℝ} (hv : IsConcaveS (convex_Ici 0) v) :
    ConcaveOn ℝ (Ici 0) (vext v) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hmem : a • x + (1 - a) • y ∈ Ici (0 : ℝ) := convex_Ici 0 hx hy ha hb hab
  rw [vext_of_nonneg v hx, vext_of_nonneg v hy, vext_of_nonneg v hmem, smul_eq_mul, smul_eq_mul]
  exact hv ⟨x, hx⟩ ⟨y, hy⟩ a ha (by linarith)

/-- **Exercise 5.12c (envelope).** At `A₀ > 0`, if `C*` is optimal with `C*_i > 0` and `W` has
partial derivative `W_{C_i}` in good `i` at `(C*, v(A₁))`, then `v'(A₀) = W_{C_i}/p_i`. -/
theorem ex_5_12c_envelope (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ : Wealth} (hA₀ : 0 < A₀.1) {C : Fin l → ℝ}
    (hC : C ∈ argmax (consObj W p R v) (budgetΓ p) A₀) {i : Fin l} (hCi : 0 < C i) {Wi : ℝ}
    (hW : HasDerivAt (fun x : ℝ => W (C + x • Pi.single i 1) (vext v (nextWealth p R A₀.1 C)))
      Wi (0 : ℝ)) :
    HasDerivAt (vext v) (Wi / p i) A₀.1 := by
  obtain ⟨-, hvc⟩ := ex_5_12b_concave h hconc hnn hv
  have hpi := h.p_pos i
  set z₁ := vext v (nextWealth p R A₀.1 C)
  set Wbar : ℝ → ℝ := fun A => W (C + ((A - A₀.1) / p i) • Pi.single i 1) z₁
  have hWbar : HasDerivAt Wbar (Wi * (1 / p i)) A₀.1 := by
    have hin : HasDerivAt (fun A : ℝ => (A - A₀.1) / p i) (1 / p i) A₀.1 := by
      simpa using ((hasDerivAt_id' A₀.1).sub_const A₀.1).div_const (p i)
    exact hW.comp_of_eq A₀.1 hin (by simp)
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W p R v) (budgetΓ p) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have heq : Wbar A₀.1 = vext v A₀.1 := by
    simp only [Wbar, sub_self, zero_div, zero_smul, add_zero]
    rw [vext_of_nonneg v A₀.2, Subtype.coe_eta, hvx]
    exact hC.2
  have hle : ∀ᶠ A in 𝓝 A₀.1, Wbar A ≤ vext v A := by
    filter_upwards [Ioi_mem_nhds (show A₀.1 - p i * C i < A₀.1 by nlinarith)] with A hA
    have hA' : A₀.1 - p i * C i < A := hA
    have hAnn : 0 ≤ A := by
      have := spend_nonneg h.p_pos hC.1.1
      have : p i * C i ≤ spend p C := Finset.single_le_sum (f := fun j => p j * C j)
        (fun j _ => mul_nonneg (h.p_pos j).le (hC.1.1 j)) (Finset.mem_univ i)
      linarith [hC.1.2]
    set Cn := C + ((A - A₀.1) / p i) • Pi.single i 1
    have hCn : Cn ∈ budgetΓ p ⟨A, hAnn⟩ := by
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj
          simp only [Cn, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
            Pi.zero_apply]
          rw [← sub_nonneg]
          have : 0 < A - (A₀.1 - p j * C j) := by linarith
          have h2 : C j + (A - A₀.1) / p j = (A - (A₀.1 - p j * C j)) / p j := by
            field_simp; ring
          rw [sub_zero, h2]
          positivity
        · have hji : (Pi.single i (1 : ℝ) : Fin l → ℝ) j = 0 := Pi.single_eq_of_ne hj 1
          simp only [Cn, Pi.add_apply, Pi.smul_apply, hji, smul_zero, add_zero, Pi.zero_apply]
          exact hC.1.1 j
      · simp only [Cn, spend_add_smul_single]
        rw [mul_div_cancel₀ _ hpi.ne']
        linarith [hC.1.2]
    have hnext : nextWealth p R A Cn = nextWealth p R A₀.1 C := by
      simp only [nextWealth, Cn, spend_add_smul_single, mul_div_cancel₀ _ hpi.ne']
      ring
    rw [vext_of_nonneg v hAnn, hvx]
    have := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos _) hCn
    simp only [consObj, hnext] at this
    exact this
  have := (theorem_4_10 (concaveOn_vext hvc) (Ici_mem_nhds hA₀) hWbar.hasFDerivAt heq
    hle).hasDerivAt
  simpa [div_eq_mul_inv] using this

/-- **Exercise 5.12c (across goods).** Goods consumed in positive amounts have equal marginal
utility per dollar: `W_{C_i}/p_i = W_{C_j}/p_j`. -/
theorem ex_5_12c_intratemporal (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ : Wealth} (hA₀ : 0 < A₀.1) {C : Fin l → ℝ}
    (hC : C ∈ argmax (consObj W p R v) (budgetΓ p) A₀) {i j : Fin l} (hCi : 0 < C i)
    (hCj : 0 < C j) {Wi Wj : ℝ}
    (hWi : HasDerivAt (fun x : ℝ => W (C + x • Pi.single i 1)
      (vext v (nextWealth p R A₀.1 C))) Wi (0 : ℝ))
    (hWj : HasDerivAt (fun x : ℝ => W (C + x • Pi.single j 1)
      (vext v (nextWealth p R A₀.1 C))) Wj (0 : ℝ)) :
    Wi / p i = Wj / p j :=
  (ex_5_12c_envelope h hconc hnn hv hA₀ hC hCi hWi).unique
    (ex_5_12c_envelope h hconc hnn hv hA₀ hC hCj hWj)

/-- **Exercise 5.12c (over time).** If saving is positive (`A₁ = R⁻¹(A₀ − p·C*) > 0`), `v` has
derivative `v₁'` at `A₁` and `W` is differentiable at `(C*, v(A₁))`, then moving a dollar from
good `i` today to wealth tomorrow does not pay: `W_{C_i}/p_i = R⁻¹ W_z v₁'`. -/
theorem ex_5_12c_euler (h : ConsHyp W p R β M) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ : Wealth} {C : Fin l → ℝ} (hC : C ∈ argmax (consObj W p R v) (budgetΓ p) A₀) {i : Fin l}
    (hCi : 0 < C i) (hA₁ : 0 < nextWealth p R A₀.1 C) {v₁' : ℝ}
    (hv₁ : HasDerivAt (vext v) v₁' (nextWealth p R A₀.1 C))
    {DW : (Fin l → ℝ) × ℝ →L[ℝ] ℝ}
    (hW : HasFDerivAt (fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) DW
      (C, vext v (nextWealth p R A₀.1 C))) :
    DW (Pi.single i 1, 0) / p i = DW (0, 1) * v₁' / R := by
  have hpi := h.p_pos i
  set A₁ := nextWealth p R A₀.1 C
  set c := -1 / p i
  set path : ℝ → (Fin l → ℝ) × ℝ := fun ε => (C + (c * ε) • Pi.single i 1, vext v (A₁ + ε / R))
  have hpath : HasDerivAt path ((c * 1) • Pi.single i 1, v₁' * (1 / R)) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · exact (((hasDerivAt_id' (0 : ℝ)).const_mul c).smul_const
        (Pi.single i 1 : Fin l → ℝ)).const_add C
    · have hin : HasDerivAt (fun ε : ℝ => A₁ + ε / R) (1 / R) 0 := by
        simpa using ((hasDerivAt_id' (0 : ℝ)).div_const R).const_add A₁
      exact hv₁.comp_of_eq (0 : ℝ) hin (by simp)
  have hcomp := hW.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp [path, A₁])
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W p R v) (budgetΓ p) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hRA : R * A₁ = A₀.1 - spend p C := by
    have hR0 := h.R_pos.ne'
    simp only [A₁, nextWealth]
    field_simp
  have hpc : ∀ ε, p i * (c * ε) = -ε := fun ε => by simp only [c]; field_simp
  -- the path is feasible near `0`, so its value has a local maximum at `0`
  have hloc : IsLocalMax ((fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) ∘ path) 0 := by
    have h1 : (0 : ℝ) < p i * C i := mul_pos hpi hCi
    have h2 : (0 : ℝ) < R * A₁ := mul_pos h.R_pos hA₁
    filter_upwards [Ioo_mem_nhds (show -(R * A₁) < 0 by linarith) h1] with ε hε
    set Cε := C + (c * ε) • Pi.single i 1
    have hCε : Cε ∈ budgetΓ p A₀ := by
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj
          simp only [Cε, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
            Pi.zero_apply]
          have : p j * (C j + c * ε) = p j * C j - ε := by rw [mul_add, hpc]; ring
          have h3 : 0 ≤ p j * (C j + c * ε) := by rw [this]; linarith [hε.2]
          exact (mul_nonneg_iff_of_pos_left hpi).1 h3
        · have hji : (Pi.single i (1 : ℝ) : Fin l → ℝ) j = 0 := Pi.single_eq_of_ne hj 1
          simp only [Cε, Pi.add_apply, Pi.smul_apply, hji, smul_zero, add_zero, Pi.zero_apply]
          exact hC.1.1 j
      · simp only [Cε, spend_add_smul_single, hpc]
        linarith [hε.1]
    have hnext : nextWealth p R A₀.1 Cε = A₁ + ε / R := by
      simp only [nextWealth, Cε, spend_add_smul_single, hpc]
      have hR0 := h.R_pos.ne'
      field_simp
      linarith [hRA]
    have hle := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos A₀) hCε
    have hL : ((fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) ∘ path) ε = consObj W p R v (A₀, Cε) := by
      simp only [Function.comp_apply, path, consObj, hnext, Cε]
    have hR0 : ((fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) ∘ path) 0 =
        consObj W p R v (A₀, C) := by
      simp [path, consObj, A₁]
    rw [hL, hR0, hC.2]
    exact hle
  have h0 := hloc.hasDerivAt_eq_zero hcomp
  have hlin : DW ((c * 1) • Pi.single i 1, v₁' * (1 / R)) =
      c * DW (Pi.single i 1, 0) + v₁' * (1 / R) * DW (0, 1) := by
    rw [show ((c * 1) • Pi.single i 1, v₁' * (1 / R)) =
        c • ((Pi.single i 1 : Fin l → ℝ), (0 : ℝ)) +
          (v₁' * (1 / R)) • ((0 : Fin l → ℝ), (1 : ℝ)) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin] at h0
  simp only [c] at h0
  have hR := h.R_pos.ne'
  field_simp at h0 ⊢
  linarith

/-! ### Exercise 5.12d: monotone transformations of the aggregator -/

/-- **Exercise 5.12d.** With `h` strictly increasing and `h⁻¹ ∘ h = id`, the aggregator
`W̃(C, a) = h(W[C, h⁻¹(a)])` gives the value `h ∘ v` at every `A`, with the same optimal
choices: the demand functions coincide. -/
theorem ex_5_12d (h : ConsHyp W p R β M) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {hf hinv : ℝ → ℝ} (hmono : StrictMono hf) (hleft : ∀ x, hinv (hf x) = x) (A : Wealth) :
    maxValue (fun q => hf (W q.2 (hinv (vext (hf ∘ v) (nextWealth p R q.1.1 q.2)))))
        (budgetΓ p) A = hf (v A) ∧
      argmax (fun q => hf (W q.2 (hinv (vext (hf ∘ v) (nextWealth p R q.1.1 q.2)))))
        (budgetΓ p) A = argmax (consObj W p R v) (budgetΓ p) A := by
  have hfun : (fun q : Wealth × (Fin l → ℝ) =>
      hf (W q.2 (hinv (vext (hf ∘ v) (nextWealth p R q.1.1 q.2))))) =
      fun q => hf (consObj W p R v q) := by
    funext q
    simp only [consObj, vext, Function.comp_apply, hleft]
  rw [hfun]
  obtain ⟨C, hC, hval, hmax⟩ := exists_argmax (continuous_consObj h v.continuous).continuousOn
    (budget_compact h.p_pos A) ⟨0, zero_mem_budget p A⟩
  have hvA : v A = maxValue (consObj W p R v) (budgetΓ p) A := (DFunLike.congr_fun hv A).symm
  have hM : maxValue (fun q => hf (consObj W p R v q)) (budgetΓ p) A = hf (v A) := by
    rw [hvA, ← hval]
    refine (IsGreatest.csSup_eq ⟨⟨C, hC, rfl⟩, ?_⟩)
    rintro _ ⟨C', hC', rfl⟩
    exact hmono.monotone (hmax C' hC')
  refine ⟨hM, ?_⟩
  ext C'
  simp only [argmax, mem_ofPred_eq, hM, hvA]
  exact and_congr_right fun _ => hmono.injective.eq_iff

/-- **Exercise 5.12d.** `W̃` need not be an aggregator. `W(C, z) = z/2` satisfies (W1)–(W3) with
`β = 1/2`; with `h(x) = x/(1 + x)` (bounded, smooth, strictly increasing, `h(0) = 0`),
`W̃(C, a) = h(h⁻¹(a)/2) = a/(2 − a)` on `[0, 1)`, and between `a = 4/5` and `a = 9/10` it moves by
more than `a` does, so (W3) fails for every modulus below one. (`W̃` is not even defined for
`a ≥ 1`.) -/
theorem ex_5_12d_not_aggregator :
    let hf : ℝ → ℝ := fun x => x / (1 + x)
    let hinv : ℝ → ℝ := fun a => a / (1 - a)
    let Wt : ℝ → ℝ := fun a => hf (hinv a / 2)
    (∀ x, 0 ≤ x → hinv (hf x) = x) ∧ StrictMonoOn hf (Ici 0) ∧
      ∀ β' < 1, ¬ ∀ a ∈ Icc (0 : ℝ) (9 / 10), ∀ a' ∈ Icc (0 : ℝ) (9 / 10),
        |Wt a - Wt a'| ≤ β' * |a - a'| := by
  intro hf hinv Wt
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun β' hβ' hall => ?_⟩
  · simp only [hf, hinv]
    have : (1 + x) ≠ 0 := by linarith
    field_simp
    ring
  · simp only [hf]
    rw [div_lt_div_iff₀ (by linarith [mem_Ici.1 hx]) (by linarith [mem_Ici.1 hy])]
    nlinarith
  · have := hall (9 / 10) ⟨by norm_num, by norm_num⟩ (4 / 5) ⟨by norm_num, by norm_num⟩
    simp only [Wt, hf, hinv] at this
    norm_num [abs_of_pos] at this
    nlinarith

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Global stability in the one-sector growth model

SLP §6.1, pp. 133–136: `v(k) = max_{0 ≤ y ≤ f(k)} {U[f(k) − y] + βv(y)}` with `f`, `U` strictly
increasing, strictly concave and continuously differentiable, `f(0) = 0`, `f'(0+) = ∞`,
`f'(∞) = 0` and `U'(0+) = ∞` (`GrowthDyn`).

* `exists_kbar`: there is a unique `k̄ > 0` with `f(k̄) = k̄`, with `k < f(k)` on `(0, k̄)` and
  `f(k) < k` beyond; Section 5.1 applies on `[0, k̄]` (`growthHyp_kbar`).
* **Exercise 6.1a** (`ex_6_1a`): for `k ∈ (0, k̄]` the maximum is interior,
  `0 < g(k) < f(k)`; `v` is continuously differentiable on `(0, k̄)` with (3)
  `v'(k) = U'[f(k) − g(k)]f'(k)`; and (2) `U'[f(k) − g(k)] = βv'[g(k)]` holds on `(0, k̄]`.
* **Exercise 6.1b** (`ex_6_1b`): `g` is strictly increasing.
* `exists_setting61`: `k̄` and the solution `v` of (1) on `[0, k̄]` exist (Exercise 5.1).
* **Proposition** (p. 136, `prop_6_1`): the stationary points of `g` are `0` and
  `k* = f'⁻¹(1/β)`, and from every `k₀ ∈ (0, k̄]` the path `k_{t+1} = g(k_t)` converges
  monotonically to `k*`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

/-! ### Derivatives of concave functions -/

/-- A concave function lies below its tangent line. -/
theorem tangent_le {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {a b d : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) (hd : HasDerivAt φ d a) : φ b ≤ φ a + d * (b - a) := by
  have := concave_le_fderiv hφ ha hb hd.hasFDerivAt
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at this
  linarith

/-- A strictly concave function lies strictly below its tangent line off the point of tangency. -/
theorem tangent_lt {φ : ℝ → ℝ} {s : Set ℝ} (hφ : StrictConcaveOn ℝ s φ) {a b d : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) (hd : HasDerivAt φ d a) : φ b < φ a + d * (b - a) := by
  have hm : (a + b) / 2 ∈ s := by
    have := hφ.1 ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1; simp only [smul_eq_mul]; ring
  have h1 := tangent_le hφ.concaveOn ha hm hd
  have h2 := hφ.2 ha hb hab (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at h2
  rw [show (1 / 2 : ℝ) * a + 1 / 2 * b = (a + b) / 2 by ring] at h2
  linarith

/-- The derivative of a concave function falls. -/
theorem deriv_le_of_concave {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {a b da db : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b) (hda : HasDerivAt φ da a) (hdb : HasDerivAt φ db b) :
    db ≤ da := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_of_eq (hdb.unique hda)
  have h1 := tangent_le hφ ha hb hda
  have h2 := tangent_le hφ hb ha hdb
  nlinarith

/-- The derivative of a strictly concave function falls strictly. -/
theorem deriv_lt_of_strictConcave {φ : ℝ → ℝ} {s : Set ℝ} (hφ : StrictConcaveOn ℝ s φ)
    {a b da db : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hda : HasDerivAt φ da a)
    (hdb : HasDerivAt φ db b) : db < da := by
  have h1 := tangent_lt hφ ha hb hab.ne hda
  have h2 := tangent_lt hφ hb ha hab.ne' hdb
  nlinarith

/-! ### The model -/

/-- The assumptions of §6.1 (p. 134). -/
structure GrowthDyn (U f U' f' : ℝ → ℝ) (β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  f_zero : f 0 = 0
  f_cont : ContinuousOn f (Ici 0)
  f_deriv : ∀ k, 0 < k → HasDerivAt f (f' k) k
  f'_cont : ContinuousOn f' (Ioi 0)
  f_mono : StrictMonoOn f (Ici 0)
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f'_zero : Tendsto f' (𝓝[>] 0) atTop
  f'_top : Tendsto f' atTop (𝓝 0)
  U_cont : ContinuousOn U (Ici 0)
  U_deriv : ∀ c, 0 < c → HasDerivAt U (U' c) c
  U'_cont : ContinuousOn U' (Ioi 0)
  U_mono : StrictMonoOn U (Ici 0)
  U_conc : StrictConcaveOn ℝ (Ici 0) U
  U'_zero : Tendsto U' (𝓝[>] 0) atTop

variable {U f U' f' : ℝ → ℝ} {β : ℝ}

theorem GrowthDyn.f'_lt (h : GrowthDyn U f U' f' β) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    f' b < f' a :=
  deriv_lt_of_strictConcave h.f_conc (mem_Ici.2 ha.le) (mem_Ici.2 (ha.trans hab).le) hab
    (h.f_deriv a ha) (h.f_deriv b (ha.trans hab))

theorem GrowthDyn.U'_lt (h : GrowthDyn U f U' f' β) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    U' b < U' a :=
  deriv_lt_of_strictConcave h.U_conc (mem_Ici.2 ha.le) (mem_Ici.2 (ha.trans hab).le) hab
    (h.U_deriv a ha) (h.U_deriv b (ha.trans hab))

theorem GrowthDyn.U'_pos (h : GrowthDyn U f U' f' β) {c : ℝ} (hc : 0 < c) : 0 < U' c := by
  have h1 := tangent_lt h.U_conc (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c ≠ c + 1) (h.U_deriv c hc)
  have h2 := h.U_mono (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c < c + 1)
  nlinarith

/-- `f(k) ≥ k f'(k)` (the tangent at `k` passes above `f(0) = 0`). -/
theorem GrowthDyn.f_ge_tangent (h : GrowthDyn U f U' f' β) {k : ℝ} (hk : 0 < k) :
    k * f' k ≤ f k := by
  have := tangent_le h.f_conc.concaveOn (mem_Ici.2 hk.le) (mem_Ici.2 le_rfl) (h.f_deriv k hk)
  rw [h.f_zero] at this
  linarith

/-- The average product `f(k)/k` falls strictly: `x f(y) < y f(x)` for `0 < x < y`. -/
theorem GrowthDyn.mul_lt (h : GrowthDyn U f U' f' β) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x * f y < y * f x := by
  have hy := hx.trans hxy
  have h1 : 0 < 1 - x / y := sub_pos.2 ((div_lt_one hy).2 hxy)
  have := h.f_conc.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy.ne h1 (div_pos hx hy)
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h.f_zero] at this
  rw [div_mul_cancel₀ x hy.ne', div_mul_eq_mul_div, div_lt_iff₀ hy] at this
  linarith

/-- The maximum maintainable capital stock: a unique `k̄ > 0` with `f(k̄) = k̄`; `k < f(k)` below
it and `f(k) < k` above it. -/
theorem exists_kbar (h : GrowthDyn U f U' f' β) :
    ∃ kbar, 0 < kbar ∧ f kbar = kbar ∧ (∀ k, 0 < k → k < kbar → k < f k) ∧
      ∀ k, kbar < k → f k < k := by
  -- `f(a) > a` for small `a`
  obtain ⟨a, ha0, ha⟩ : ∃ a, 0 < a ∧ a < f a := by
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1
      (eventually_nhdsWithin_iff.1 (h.f'_zero.eventually (eventually_gt_atTop 2)))
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    have hd : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith
    have h2 : 2 < f' (δ / 2) := hδs hd (half_pos hδ)
    have := h.f_ge_tangent (half_pos hδ)
    nlinarith
  -- `f(b) < b` for large `b`
  obtain ⟨b, hab, hb⟩ : ∃ b, a < b ∧ f b < b := by
    obtain ⟨K, hK⟩ := eventually_atTop.1 (h.f'_top.eventually (gt_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 2)))
    set K' := max K a + 1
    have hK'0 : 0 < K' := by have := le_max_right K a; linarith
    refine ⟨max K' (2 * f K') + 1, ?_, ?_⟩
    · have := le_max_left K' (2 * f K')
      have := le_max_right K a
      linarith
    have hb0 : K' ≤ max K' (2 * f K') + 1 := by have := le_max_left K' (2 * f K'); linarith
    have ht := tangent_le h.f_conc.concaveOn (mem_Ici.2 hK'0.le)
      (mem_Ici.2 (hK'0.le.trans hb0)) (h.f_deriv K' hK'0)
    have hKK : K ≤ K' := by have := le_max_left K a; linarith
    have hfK := hK K' hKK
    have := le_max_right K' (2 * f K')
    nlinarith
  -- the intermediate value theorem for `f(k) − k`
  have hcont : ContinuousOn (fun k => f k - k) (Icc a b) :=
    (h.f_cont.mono fun k hk => mem_Ici.2 (ha0.le.trans hk.1)).sub continuousOn_id
  obtain ⟨kb, hkb, hkb0⟩ := intermediate_value_Icc' hab.le hcont
    (show (0 : ℝ) ∈ Icc (f b - b) (f a - a) from ⟨by linarith, by linarith⟩)
  have hkb0' : f kb = kb := by simp only at hkb0; linarith
  have hkpos : 0 < kb := ha0.trans_le hkb.1
  refine ⟨kb, hkpos, hkb0', fun k hk hkk => ?_, fun k hk => ?_⟩
  · have := h.mul_lt hk hkk
    rw [hkb0'] at this
    nlinarith
  · have := h.mul_lt hkpos hk
    rw [hkb0'] at this
    nlinarith

/-! ### The policy function on `[0, k̄]` -/

/-- On `[0, k̄]`, Section 5.1 applies. -/
theorem growthHyp_kbar (h : GrowthDyn U f U' f' β) {kbar : ℝ} (hk0 : 0 < kbar)
    (hkf : f kbar = kbar) (hbelow : ∀ k, 0 < k → k < kbar → k < f k) :
    GrowthHyp U f β kbar where
  β_pos := h.β_pos
  β_lt := h.β_lt
  U_cont := h.U_cont
  U_mono := h.U_mono
  f_cont := h.f_cont
  f_zero := h.f_zero
  xbar_pos := hk0
  f_maintain := fun x hx => by
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hx.1 with h0 | hpos
      · rw [← h0, h.f_zero]
      rcases eq_or_lt_of_le hx.2 with he | hlt
      · rw [he, hkf]
      · exact (hbelow x hpos hlt).le
    · rw [← hkf]
      exact h.f_mono.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 hk0.le) hx.2
  f_mono := h.f_mono

/-- The policy `g`, extended by zero off `[0, k̄]`. -/
noncomputable def gpol (U f : ℝ → ℝ) (β kbar : ℝ) [Nonempty (Icc (0 : ℝ) kbar)]
    (v : Icc (0 : ℝ) kbar →ᵇ ℝ) (k : ℝ) : ℝ := by
  classical exact if hk : k ∈ Icc 0 kbar then
    (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk⟩).1 else 0

theorem gpol_of_mem {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] (v : Icc (0 : ℝ) kbar →ᵇ ℝ) {k : ℝ}
    (hk : k ∈ Icc 0 kbar) :
    gpol U f β kbar v k = (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk⟩).1 := by
  simp only [gpol, hk, ↓reduceDIte]

/-- `v` is strictly concave on `[0, k̄]`. -/
theorem strictConcaveOn_liftR {kbar : ℝ} {v : Icc (0 : ℝ) kbar → ℝ}
    (hv : IsStrictConcaveS (convex_Icc 0 kbar) v) :
    StrictConcaveOn ℝ (Icc 0 kbar) (liftR kbar v) := by
  refine ⟨convex_Icc 0 kbar, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have hmem : a • x + b • y ∈ Icc (0 : ℝ) kbar := convex_Icc 0 kbar hx hy ha.le hb.le hab
  rw [liftR_of_mem v hx, liftR_of_mem v hy, liftR_of_mem v hmem, smul_eq_mul, smul_eq_mul]
  subst hb'
  exact hv ⟨x, hx⟩ ⟨y, hy⟩ (fun he => hxy (congrArg Subtype.val he)) a ha (by linarith)

/-- The setting of Exercise 6.1: `k̄`, the fixed point `v` of Section 5.1 on `[0, k̄]`, and its
policy. -/
structure Setting61 (U f U' f' : ℝ → ℝ) (β kbar : ℝ) (v : Icc (0 : ℝ) kbar →ᵇ ℝ) : Prop where
  dyn : GrowthDyn U f U' f' β
  kbar_pos : 0 < kbar
  kbar_fix : f kbar = kbar
  below : ∀ k, 0 < k → k < kbar → k < f k
  fixed : bellman (growth_assumption43 (growthHyp_kbar dyn kbar_pos kbar_fix below))
    (growth_assumption44 (growthHyp_kbar dyn kbar_pos kbar_fix below)) v = v

namespace Setting61

variable {kbar : ℝ} {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v)
  [Nonempty (Icc (0 : ℝ) kbar)]
include S

omit [Nonempty (Icc (0 : ℝ) kbar)] in
theorem hyp : GrowthHyp U f β kbar := growthHyp_kbar S.dyn S.kbar_pos S.kbar_fix S.below

omit [Nonempty (Icc (0 : ℝ) kbar)] in
theorem inada : Tendsto (deriv U) (𝓝[>] 0) atTop := by
  refine S.dyn.U'_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact ((S.dyn.U_deriv c hc).deriv).symm

theorem weak :
    IsStrictConcaveS (convex_Icc 0 kbar) v ∧
      UniqueArgmax (growthΓ f kbar) (obj (growthF U f kbar) β v) ∧
      Continuous (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v)) := by
  exact ex_5_1c_weak S.hyp S.dyn.U_conc S.dyn.f_conc.concaveOn S.fixed

theorem gpol_mem {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    gpol U f β kbar v k ∈ Icc 0 kbar ∧ gpol U f β kbar v k ≤ f k := by
  rw [gpol_of_mem v hk]
  exact ⟨Subtype.mem _, (S.weak.2.1.argmaxFn_mem ⟨k, hk⟩).1⟩

theorem gpol_zero : gpol U f β kbar v 0 = 0 := by
  have hk : (0 : ℝ) ∈ Icc 0 kbar := ⟨le_rfl, S.kbar_pos.le⟩
  have := S.gpol_mem hk
  rw [S.dyn.f_zero] at this
  exact le_antisymm this.2 this.1.1

/-- The maximum is interior: `0 < g(k) < f(k)` for `k ∈ (0, k̄]`. -/
theorem gpol_interior {k : ℝ} (hk : 0 < k) (hkb : k ≤ kbar) :
    0 < gpol U f β kbar v k ∧ gpol U f β kbar v k < f k := by
  rw [gpol_of_mem v ⟨hk.le, hkb⟩]
  exact ex_5_1d_interior S.hyp S.dyn.U_conc S.dyn.f_conc.concaveOn
    (fun c hc => (S.dyn.U_deriv c hc).differentiableAt) S.inada S.fixed (x := ⟨k, hk.le, hkb⟩) hk

theorem gpol_lt_kbar {k : ℝ} (hk : 0 < k) (hkb : k ≤ kbar) : gpol U f β kbar v k < kbar := by
  have h1 := (S.gpol_interior hk hkb).2
  have h2 := (S.hyp.f_maintain k ⟨hk.le, hkb⟩).2
  linarith

theorem continuousOn_gpol : ContinuousOn (gpol U f β kbar v) (Icc 0 kbar) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (Icc (0 : ℝ) kbar).domRestrict (gpol U f β kbar v) =
      fun k => (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) k).1 := by
    funext k
    simp only [Set.domRestrict_apply]
    rw [gpol_of_mem v k.2]
  rw [e]
  exact continuous_subtype_val.comp S.weak.2.2

/-- (3): `v'(k) = U'[f(k) − g(k)]f'(k)` on `(0, k̄)`. -/
theorem hasDerivAt_v {k : ℝ} (hk : 0 < k) (hkb : k < kbar) :
    HasDerivAt (liftR kbar v) (U' (f k - gpol U f β kbar v k) * f' k) k := by
  have hint := S.gpol_interior hk hkb.le
  rw [gpol_of_mem v ⟨hk.le, hkb.le⟩] at hint ⊢
  exact ex_5_1d S.hyp S.dyn.U_conc S.dyn.f_conc.concaveOn S.fixed (x₀ := ⟨k, hk.le, hkb.le⟩)
    ⟨hk, hkb⟩ hint.2 (S.dyn.U_deriv _ (by linarith [hint.2])) (S.dyn.f_deriv k hk)

/-- (2): `U'[f(k) − g(k)] = βv'[g(k)]` on `(0, k̄]`. -/
theorem foc {k : ℝ} (hk : 0 < k) (hkb : k ≤ kbar) :
    U' (f k - gpol U f β kbar v k) =
      β * (U' (f (gpol U f β kbar v k) - gpol U f β kbar v (gpol U f β kbar v k)) *
        f' (gpol U f β kbar v k)) := by
  set y := gpol U f β kbar v k
  have hint := S.gpol_interior hk hkb
  have hyk : y < kbar := S.gpol_lt_kbar hk hkb
  have hc : 0 < f k - y := by linarith [hint.2]
  have hdv := S.hasDerivAt_v hint.1 hyk
  set φ : ℝ → ℝ := fun z => U (f k - z) + β * liftR kbar v z
  have hφ : HasDerivAt φ (U' (f k - y) * (0 - 1) +
      β * (U' (f y - gpol U f β kbar v y) * f' y)) y :=
    ((S.dyn.U_deriv _ hc).comp y ((hasDerivAt_const y (f k)).sub (hasDerivAt_id y))).add
      (hdv.const_mul β)
  -- `y` maximizes `φ` over `(0, f(k))`
  have hUA := S.weak.2.1
  have hmax : IsLocalMax φ y := by
    filter_upwards [Ioo_mem_nhds hint.1 hint.2] with z hz
    have hzI : z ∈ Icc (0 : ℝ) kbar :=
      ⟨hz.1.le, hz.2.le.trans (S.hyp.f_maintain k ⟨hk.le, hkb⟩).2⟩
    have hyI : y ∈ Icc (0 : ℝ) kbar := (S.gpol_mem ⟨hk.le, hkb⟩).1
    have hmem := hUA.argmaxFn_mem ⟨k, hk.le, hkb⟩
    have hle := le_maxValue hUA.cont (hUA.compact ⟨k, hk.le, hkb⟩)
      (z := ⟨z, hzI⟩) (show (⟨z, hzI⟩ : Icc (0 : ℝ) kbar) ∈ growthΓ f kbar ⟨k, hk.le, hkb⟩ from
        hz.2.le)
    rw [← hmem.2] at hle
    simp only [φ, liftR_of_mem v hzI, liftR_of_mem v hyI]
    have hy : y = (argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk.le, hkb⟩).1 :=
      gpol_of_mem v ⟨hk.le, hkb⟩
    have hyv : (⟨y, hyI⟩ : Icc (0 : ℝ) kbar) =
        argmaxFn (growthΓ f kbar) (obj (growthF U f kbar) β v) ⟨k, hk.le, hkb⟩ := Subtype.ext hy
    rw [hyv, hy]
    simpa [obj, growthF] using hle
  have := hmax.hasDerivAt_eq_zero hφ
  linarith

/-- `v` is strictly concave on `[0, k̄]`. -/
theorem strictConcave_v : StrictConcaveOn ℝ (Icc 0 kbar) (liftR kbar v) :=
  strictConcaveOn_liftR S.weak.1

end Setting61

/-- **Exercise 6.1a.** For `k ∈ (0, k̄]` the maximum in (1) is interior; `v` is continuously
differentiable on `(0, k̄)`, with (3) `v'(k) = U'[f(k) − g(k)]f'(k)`; and (2)
`U'[f(k) − g(k)] = βv'[g(k)]` holds on `(0, k̄]`. -/
theorem ex_6_1a {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] {v : Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : Setting61 U f U' f' β kbar v) :
    (∀ k, 0 < k → k ≤ kbar → 0 < gpol U f β kbar v k ∧ gpol U f β kbar v k < f k) ∧
      (∀ k, 0 < k → k < kbar →
        HasDerivAt (liftR kbar v) (U' (f k - gpol U f β kbar v k) * f' k) k) ∧
      ContinuousOn (fun k => U' (f k - gpol U f β kbar v k) * f' k) (Ioo 0 kbar) ∧
      ∀ k, 0 < k → k ≤ kbar → HasDerivAt (liftR kbar v)
        (U' (f (gpol U f β kbar v k) - gpol U f β kbar v (gpol U f β kbar v k)) *
          f' (gpol U f β kbar v k)) (gpol U f β kbar v k) ∧
        U' (f k - gpol U f β kbar v k) =
          β * (U' (f (gpol U f β kbar v k) - gpol U f β kbar v (gpol U f β kbar v k)) *
            f' (gpol U f β kbar v k)) := by
  refine ⟨fun k hk hkb => S.gpol_interior hk hkb, fun k hk hkb => S.hasDerivAt_v hk hkb, ?_,
    fun k hk hkb => ⟨S.hasDerivAt_v (S.gpol_interior hk hkb).1 (S.gpol_lt_kbar hk hkb),
      S.foc hk hkb⟩⟩
  intro k hk
  have hc : 0 < f k - gpol U f β kbar v k := by linarith [(S.gpol_interior hk.1 hk.2.le).2]
  have hfc : ContinuousAt f k := (S.dyn.f_deriv k hk.1).continuousAt
  have hgc : ContinuousAt (gpol U f β kbar v) k :=
    (S.continuousOn_gpol k (Ioo_subset_Icc_self hk)).continuousAt (Icc_mem_nhds hk.1 hk.2)
  have hU'c : ContinuousAt U' (f k - gpol U f β kbar v k) :=
    S.dyn.U'_cont.continuousAt (Ioi_mem_nhds hc)
  have hf'c : ContinuousAt f' k := S.dyn.f'_cont.continuousAt (Ioi_mem_nhds hk.1)
  have hsub : ContinuousAt (fun x => f x - gpol U f β kbar v x) k := hfc.sub hgc
  exact ((ContinuousAt.comp (f := fun x => f x - gpol U f β kbar v x) hU'c hsub).mul
    hf'c).continuousWithinAt

/-- **Exercise 6.1b.** The policy `g` is strictly increasing on `[0, k̄]`. -/
theorem ex_6_1b {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] {v : Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : Setting61 U f U' f' β kbar v) :
    StrictMonoOn (gpol U f β kbar v) (Icc 0 kbar) := by
  intro k hk k' hk' hkk'
  rcases eq_or_lt_of_le hk.1 with h0 | hpos
  · rw [← h0, S.gpol_zero]
    exact (S.gpol_interior (h0 ▸ hkk' : 0 < k') hk'.2).1
  have hpos' : 0 < k' := hpos.trans hkk'
  by_contra hcon
  push Not at hcon
  set y := gpol U f β kbar v k
  set y' := gpol U f β kbar v k'
  have hi := S.gpol_interior hpos hk.2
  have hi' := S.gpol_interior hpos' hk'.2
  -- consumption rises with `k`
  have hfk : f k < f k' := S.dyn.f_mono (mem_Ici.2 hpos.le) (mem_Ici.2 hpos'.le) hkk'
  have hU : U' (f k' - y') < U' (f k - y) := S.dyn.U'_lt (by linarith) (by linarith)
  rw [S.foc hpos hk.2, S.foc hpos' hk'.2] at hU
  -- but `v'` falls, and `y' ≤ y`
  have hd := deriv_le_of_concave S.strictConcave_v.concaveOn
    (⟨hi'.1.le, (S.gpol_lt_kbar hpos' hk'.2).le⟩ : y' ∈ Icc 0 kbar)
    (⟨hi.1.le, (S.gpol_lt_kbar hpos hk.2).le⟩ : y ∈ Icc 0 kbar) hcon
    (S.hasDerivAt_v hi'.1 (S.gpol_lt_kbar hpos' hk'.2))
    (S.hasDerivAt_v hi.1 (S.gpol_lt_kbar hpos hk.2))
  have := mul_le_mul_of_nonneg_left hd S.dyn.β_pos.le
  linarith

/-! ### Stationary points and global stability -/

/-- `k* = f'⁻¹(1/β)`: there is a unique `k* > 0` with `f'(k*) = 1/β`. -/
theorem exists_kstar (h : GrowthDyn U f U' f' β) :
    ∃ kstar, 0 < kstar ∧ f' kstar = 1 / β ∧ ∀ k, 0 < k → f' k = 1 / β → k = kstar := by
  have hβ := h.β_pos
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (h.f'_zero.eventually (eventually_gt_atTop (1 / β))))
  set a := δ / 2
  have ha : 0 < a := half_pos hδ
  have hda : dist a 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]
    exact half_lt_self hδ
  have hfa : 1 / β < f' a := hδs hda ha
  obtain ⟨K, hK⟩ := eventually_atTop.1 (h.f'_top.eventually (gt_mem_nhds (one_div_pos.2 hβ)))
  set b := max K a + 1
  have hab : a < b := by have := le_max_right K a; linarith
  have hfb : f' b < 1 / β := hK b (by have := le_max_left K a; linarith)
  have hcont : ContinuousOn f' (Icc a b) := h.f'_cont.mono fun k hk => ha.trans_le hk.1
  obtain ⟨ks, hks, hks1⟩ := intermediate_value_Icc' hab.le hcont ⟨hfb.le, hfa.le⟩
  refine ⟨ks, ha.trans_le hks.1, hks1, fun k hk hk1 => ?_⟩
  rcases lt_trichotomy k ks with hlt | heq | hgt
  · have := h.f'_lt hk hlt; linarith
  · exact heq
  · have := h.f'_lt (ha.trans_le hks.1) hgt; linarith

namespace Setting61

variable {kbar : ℝ} {v : Icc (0 : ℝ) kbar →ᵇ ℝ} (S : Setting61 U f U' f' β kbar v)
  [Nonempty (Icc (0 : ℝ) kbar)]
include S

/-- (5) with strict inequality: off the stationary points, `[f'(k) − 1/β][k − g(k)] < 0`. -/
theorem five {k : ℝ} (hk : 0 < k) (hkb : k < kbar) (hne : gpol U f β kbar v k ≠ k) :
    (f' k - 1 / β) * (k - gpol U f β kbar v k) < 0 := by
  set y := gpol U f β kbar v k
  have hi := S.gpol_interior hk hkb.le
  have hyk := S.gpol_lt_kbar hk hkb.le
  have hc : 0 < f k - y := by linarith [hi.2]
  have hU := S.dyn.U'_pos hc
  have hfoc := S.foc hk hkb.le
  have hβ := S.dyn.β_pos
  have hdk := S.hasDerivAt_v hk hkb
  have hdy := S.hasDerivAt_v hi.1 hyk
  set dk := U' (f k - y) * f' k
  set dy := U' (f y - gpol U f β kbar v y) * f' y
  have hkI : k ∈ Icc (0 : ℝ) kbar := ⟨hk.le, hkb.le⟩
  have hyI : y ∈ Icc (0 : ℝ) kbar := ⟨hi.1.le, hyk.le⟩
  -- strict concavity of `v`: `(v'(k) − v'(g(k)))(k − g(k)) < 0`
  have hmono : (dk - dy) * (k - y) < 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := deriv_lt_of_strictConcave S.strictConcave_v hyI hkI hlt hdy hdk
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · have := deriv_lt_of_strictConcave S.strictConcave_v hkI hyI hgt hdk hdy
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  -- `v'(g(k)) = U'(c)/β`
  have hdy' : dy = U' (f k - y) / β := by
    rw [eq_div_iff hβ.ne']
    linarith
  have e : (dk - dy) * (k - y) = U' (f k - y) * ((f' k - 1 / β) * (k - y)) := by
    rw [hdy']
    simp only [dk]
    ring
  rw [e] at hmono
  exact neg_of_mul_neg_right hmono hU.le

/-- The positive stationary points of `g` solve `f'(k) = 1/β`. -/
theorem fixed_iff {k : ℝ} (hk : 0 < k) (hkb' : k < kbar) :
    gpol U f β kbar v k = k ↔ f' k = 1 / β := by
  have hβ := S.dyn.β_pos
  have hkb := hkb'.le
  constructor
  · intro hfix
    have hfoc := S.foc hk hkb
    rw [hfix, hfix] at hfoc
    have hc : 0 < f k - k := by
      have := (S.gpol_interior hk hkb).2
      rw [hfix] at this
      linarith
    have hU := S.dyn.U'_pos hc
    field_simp
    nlinarith
  · intro hf1
    by_contra hne
    have := S.five hk hkb' hne
    rw [hf1, sub_self, zero_mul] at this
    exact lt_irrefl 0 this

end Setting61

/-- **Proposition** (p. 136). The stationary points of `g` on `[0, k̄]` are `0` and `k*`, where
`f'(k*) = 1/β`, and from every `k₀ ∈ (0, k̄]` the path `k_{t+1} = g(k_t)` converges monotonically
to `k*`. -/
theorem prop_6_1 {kbar : ℝ} [Nonempty (Icc (0 : ℝ) kbar)] {v : Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : Setting61 U f U' f' β kbar v) {kstar : ℝ} (hks0 : 0 < kstar) (hks : f' kstar = 1 / β) :
    kstar < kbar ∧
      (∀ k ∈ Icc 0 kbar, gpol U f β kbar v k = k ↔ k = 0 ∨ k = kstar) ∧
      ∀ k₀, 0 < k₀ → k₀ ≤ kbar →
        (Monotone (fun t => (gpol U f β kbar v)^[t] k₀) ∨
          Antitone (fun t => (gpol U f β kbar v)^[t] k₀)) ∧
        Tendsto (fun t => (gpol U f β kbar v)^[t] k₀) atTop (𝓝 kstar) := by
  have hβ := S.dyn.β_pos
  have hβ1 := S.dyn.β_lt
  set g := gpol U f β kbar v
  -- `k* < k̄`, since `f'(k̄) ≤ 1 < 1/β`
  have hlt : kstar < kbar := by
    by_contra hge
    push Not at hge
    have h1 := S.dyn.f_ge_tangent S.kbar_pos
    rw [S.kbar_fix] at h1
    have h2 : f' kbar ≤ 1 := by nlinarith [S.kbar_pos]
    have h3 : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith
    rcases eq_or_lt_of_le hge with he | hgt
    · rw [← he] at hks; linarith
    · have := S.dyn.f'_lt S.kbar_pos hgt; linarith
  have hkI : kstar ∈ Icc (0 : ℝ) kbar := ⟨hks0.le, hlt.le⟩
  have hgks : g kstar = kstar := (S.fixed_iff hks0 hlt).2 hks
  have hmono := ex_6_1b S
  -- the sign of `g(k) − k`
  have below : ∀ k, 0 < k → k < kstar → k < g k := fun k hk hkk => by
    have hne : g k ≠ k := fun he => by
      have := (S.fixed_iff hk (hkk.trans hlt)).1 he
      have := S.dyn.f'_lt hk hkk
      linarith
    have h5 := S.five hk (hkk.trans hlt) hne
    have hf : 1 / β < f' k := by rw [← hks]; exact S.dyn.f'_lt hk hkk
    nlinarith
  have above : ∀ k, kstar < k → k ≤ kbar → g k < k := fun k hkk hkb => by
    have hk : 0 < k := hks0.trans hkk
    rcases eq_or_lt_of_le hkb with he | hkb'
    · have := (S.gpol_interior hk hkb).2
      rw [he, S.kbar_fix] at this
      rw [he]; exact this
    have hne : g k ≠ k := fun he => by
      have := (S.fixed_iff hk hkb').1 he
      have := S.dyn.f'_lt hks0 hkk
      linarith
    have h5 := S.five hk hkb' hne
    have hf : f' k < 1 / β := by rw [← hks]; exact S.dyn.f'_lt hks0 hkk
    nlinarith
  refine ⟨hlt, fun k hk => ⟨fun hfix => ?_, ?_⟩, fun k₀ hk₀ hk₀b => ?_⟩
  · rcases eq_or_lt_of_le hk.1 with h0 | hpos
    · exact Or.inl h0.symm
    · exact Or.inr (by
        rcases lt_trichotomy k kstar with h1 | h1 | h1
        · exact absurd hfix (ne_of_gt (below k hpos h1))
        · exact h1
        · exact absurd hfix (ne_of_lt (above k h1 hk.2)))
  · rintro (rfl | rfl)
    · exact S.gpol_zero
    · exact hgks
  -- the path stays in `(0, k̄]` and is monotone
  set x : ℕ → ℝ := fun t => g^[t] k₀
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => by
    simp only [x, Function.iterate_succ_apply']
  have hpos : ∀ t, 0 < x t ∧ x t ≤ kbar := by
    intro t
    induction t with
    | zero => exact ⟨hk₀, hk₀b⟩
    | succ t ih =>
      rw [hstep]
      exact ⟨(S.gpol_interior ih.1 ih.2).1, (S.gpol_lt_kbar ih.1 ih.2).le⟩
  have hcont : ∀ L, 0 < L → L ≤ kbar → Tendsto x atTop (𝓝 L) → L = kstar := by
    intro L hL hLb hx
    have hgL : ContinuousWithinAt g (Icc 0 kbar) L := S.continuousOn_gpol L ⟨hL.le, hLb⟩
    have h1 : Tendsto (fun t => g (x t)) atTop (𝓝 (g L)) :=
      hgL.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun t =>
        ⟨(hpos t).1.le, (hpos t).2⟩⟩)
    have h2 : Tendsto (fun t => g (x t)) atTop (𝓝 L) := by
      simp only [← hstep]
      exact hx.comp (tendsto_add_atTop_nat 1)
    have hfix : g L = L := tendsto_nhds_unique h1 h2
    have hLlt : L < kbar := by
      have : g L < kbar := S.gpol_lt_kbar hL hLb
      rwa [hfix] at this
    exact ((S.fixed_iff hL hLlt).1 hfix) |> fun h1 => (by
      obtain ⟨k', -, -, huniq⟩ := exists_kstar S.dyn
      exact (huniq L hL h1).trans (huniq kstar hks0 hks).symm)
  rcases le_total k₀ kstar with hle | hge
  · -- from below: the path rises to `k*`
    have hbd : ∀ t, x t ≤ kstar := by
      intro t
      induction t with
      | zero => exact hle
      | succ t ih =>
        rw [hstep, ← hgks]
        exact hmono.monotoneOn ⟨(hpos t).1.le, (hpos t).2⟩ hkI ih
    have hm : Monotone x := monotone_nat_of_le_succ fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt'
      · rw [he, hgks]
      · exact (below (x t) (hpos t).1 hlt').le
    have hx := tendsto_atTop_ciSup hm ⟨kstar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL0 : 0 < ⨆ t, x t := (hpos 0).1.trans_le (le_ciSup ⟨kstar, by
      rintro _ ⟨t, rfl⟩; exact hbd t⟩ 0)
    have hLb : (⨆ t, x t) ≤ kbar := ciSup_le fun t => (hpos t).2
    exact ⟨Or.inl hm, hcont _ hL0 hLb hx ▸ hx⟩
  · -- from above: the path falls to `k*`
    have hbd : ∀ t, kstar ≤ x t := by
      intro t
      induction t with
      | zero => exact hge
      | succ t ih =>
        rw [hstep, ← hgks]
        exact hmono.monotoneOn hkI ⟨(hpos t).1.le, (hpos t).2⟩ ih
    have ha : Antitone x := antitone_nat_of_succ_le fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hbd t) with he | hlt'
      · rw [← he, hgks]
      · exact (above (x t) hlt' (hpos t).2).le
    have hx := tendsto_atTop_ciInf ha ⟨kstar, by rintro _ ⟨t, rfl⟩; exact hbd t⟩
    have hL0 : kstar ≤ ⨅ t, x t := le_ciInf hbd
    have hLb : (⨅ t, x t) ≤ kbar := (ciInf_le ⟨kstar, by
      rintro _ ⟨t, rfl⟩; exact hbd t⟩ 0).trans (hpos 0).2
    exact ⟨Or.inr ha, hcont _ (hks0.trans_le hL0) hLb hx ▸ hx⟩

/-- The setting of §6.1 exists: `k̄`, and the unique bounded continuous solution `v` of (1) on
`[0, k̄]` (Exercise 5.1). -/
theorem exists_setting61 (h : GrowthDyn U f U' f' β) :
    ∃ kbar v, Setting61 U f U' f' β kbar v := by
  obtain ⟨kbar, hk0, hkf, hbelow, -⟩ := exists_kbar h
  obtain ⟨v, hv, -⟩ := ex_5_1ab (growthHyp_kbar h hk0 hkf hbelow)
  exact ⟨kbar, v, ⟨h, hk0, hkf, hbelow, hv⟩⟩

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Every smooth map is an optimal policy: Boldrin and Montrucchio

SLP Theorem 6.1, p. 138: let `X ⊆ ℝ` be compact and `g : X → X` twice continuously
differentiable, with `Γ(x) = X`. Then there are a return function `F` and a discount factor `β`
such that `(X, Γ, F, β)` satisfies Assumptions 4.3–4.4 and 4.7–4.9, and `g` is the optimal policy
function.

The book does not prove the theorem. The proof here uses the telescoping return
`F(x, y) = U(x) − βU(y) − (y − g(x))²/2` with `U(x) = −Kx²/2` and `β = 1/(2K)` (`bmF`):
`F(x, y) + βU(y) = U(x) − (y − g(x))²/2`. So `v = U` solves (FE) and the maximum is attained
exactly at `y = g(x)` (`bellman_bm`, `argmax_bm`). For `K` large, `F` is strictly concave
(`bm_assumption47`). Its concavity gap is
`θ(1 − θ)[KΔx²/2 − Δy²/4 + (Δy − Δg)²/2] + He − e²/2`, where `e` is the error of `g` against its
chord. That error is at most `(M₂/2)θ(1 − θ)Δx²`, because `g ± M₂x²/2` is convex
(`chord_error_le`).

`X` is a compact interval `[a, b]`, as the convexity of `X` in Assumption 4.3 requires. "Twice
continuously differentiable" is used only through bounds `|g'| ≤ M₁` and `|g''| ≤ M₂` on
`(a, b)`, which a `C²` map on `[a, b]` satisfies (`theorem_6_1`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

/-- The return function `F(x, y) = −Kx²/2 + y²/4 − (y − g(x))²/2`; with `β = 1/(2K)` this is
`U(x) − βU(y) − (y − g(x))²/2` for `U(x) = −Kx²/2`. -/
noncomputable def bmF (g : ℝ → ℝ) (K x y : ℝ) : ℝ :=
  -(K * x ^ 2 / 2) + y ^ 2 / 4 - (y - g x) ^ 2 / 2

variable {a b : ℝ} {g g' g'' : ℝ → ℝ} {M₁ M₂ : ℝ}

/-- `|g(θx + (1 − θ)x') − θg(x) − (1 − θ)g(x')| ≤ (M₂/2)θ(1 − θ)(x − x')²`: `g ± M₂x²/2` is
convex. -/
theorem chord_error_le (hgc : ContinuousOn g (Icc a b))
    (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) {x x' θ : ℝ} (hx : x ∈ Icc a b) (hx' : x' ∈ Icc a b)
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x'| ≤
      M₂ / 2 * (θ * (1 - θ)) * (x - x') ^ 2 := by
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  -- `ψ_s(z) = s·g(z) + M₂z²/2` is convex for `s = ±1`
  have hconv : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ConvexOn ℝ (Icc a b) (fun z => s * g z + M₂ / 2 * z ^ 2) := by
    intro s hs
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := fun z => s * g' z + M₂ * z)
      (f'' := fun z => s * g'' z + M₂) (convex_Icc a b)
      ((continuousOn_const.mul hgc).add (continuousOn_const.mul (continuousOn_pow 2)))
      (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_)
    · rw [hint] at hz
      have := ((hg' z hz).const_mul s).add ((hasDerivAt_pow 2 z).const_mul (M₂ / 2))
      convert this.hasDerivWithinAt using 1
      push_cast
      ring
    · rw [hint] at hz
      have := ((hg'' z hz).const_mul s).add ((hasDerivAt_id' z).const_mul M₂)
      convert this.hasDerivWithinAt using 1
      ring
    · rw [hint] at hz
      have := hM₂ z hz
      rw [abs_le] at this
      rcases hs with rfl | rfl <;> linarith [this.1, this.2]
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      s * (g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x') ≤
        M₂ / 2 * (θ * (1 - θ)) * (x - x') ^ 2 := by
    intro s hs
    have := (hconv s hs).2 hx hx' h0 (by linarith : 0 ≤ 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    nlinarith
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

/-- `|g(x) − g(x')| ≤ M₁|x − x'|`. -/
theorem lipschitz_of_deriv_le (hgc : ContinuousOn g (Icc a b))
    (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁) {x x' : ℝ}
    (hx : x ∈ Icc a b) (hx' : x' ∈ Icc a b) : |g x - g x'| ≤ M₁ * |x - x'| := by
  wlog hle : x' ≤ x generalizing x x'
  · rw [abs_sub_comm, abs_sub_comm x]
    exact this hx' hx (le_of_not_ge hle)
  rcases eq_or_lt_of_le hle with rfl | hlt
  · simp
  have hsub : Icc x' x ⊆ Icc a b := Icc_subset_Icc hx'.1 hx.2
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g g' hlt (hgc.mono hsub) fun z hz =>
    hg' z ⟨lt_of_le_of_lt hx'.1 hz.1, lt_of_lt_of_le hz.2 hx.2⟩
  have hcI : c ∈ Ioo a b := ⟨lt_of_le_of_lt hx'.1 hc.1, lt_of_lt_of_le hc.2 hx.2⟩
  have hpos : 0 < x - x' := sub_pos.2 hlt
  rw [eq_div_iff hpos.ne'] at hcd
  rw [← hcd, abs_mul]
  exact mul_le_mul_of_nonneg_right (hM₁ c hcI) (abs_nonneg _)

/-- The concavity gap of `F`, written out. -/
theorem bmF_gap (K θ x y x' y' : ℝ) :
    bmF g K (θ * x + (1 - θ) * x') (θ * y + (1 - θ) * y') - θ * bmF g K x y -
        (1 - θ) * bmF g K x' y' =
      θ * (1 - θ) * (K / 2 * (x - x') ^ 2 - (y - y') ^ 2 / 4 +
        ((y - g x) - (y' - g x')) ^ 2 / 2) +
      (θ * (y - g x) + (1 - θ) * (y' - g x')) *
          (g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x') -
        (g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x') ^ 2 / 2 := by
  simp only [bmF]
  ring

/-- `K = M₁² + DM₂ + M₂²D²/16 + 1` with `D = b − a`. -/
noncomputable def bmK (a b M₁ M₂ : ℝ) : ℝ := M₁ ^ 2 + (b - a) * M₂ + M₂ ^ 2 * (b - a) ^ 2 / 16 + 1

theorem one_le_bmK (hab : a < b) (hM₂ : 0 ≤ M₂) : 1 ≤ bmK a b M₁ M₂ := by
  have : 0 ≤ (b - a) * M₂ := mul_nonneg (by linarith) hM₂
  simp only [bmK]
  nlinarith [sq_nonneg M₁, sq_nonneg (M₂ * (b - a))]

/-- **The concavity gap.** For `x, y, x', y' ∈ [a, b]`, the gap of `F` is at least
`θ(1 − θ)(x − x')²/2`. -/
theorem bm_gap_ge (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) {x y x' y' θ : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) (hx' : x' ∈ Icc a b) (hy' : y' ∈ Icc a b) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (1 - θ) * (x - x') ^ 2 / 2 ≤
      bmF g (bmK a b M₁ M₂) (θ * x + (1 - θ) * x') (θ * y + (1 - θ) * y') -
        θ * bmF g (bmK a b M₁ M₂) x y - (1 - θ) * bmF g (bmK a b M₁ M₂) x' y' := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ _ hmid)
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ _ hmid)
  rw [bmF_gap]
  set D := b - a
  set T := θ * (1 - θ)
  set X2 := (x - x') ^ 2
  set e := g (θ * x + (1 - θ) * x') - θ * g x - (1 - θ) * g x'
  set H := θ * (y - g x) + (1 - θ) * (y' - g x')
  have hT : 0 ≤ T := mul_nonneg h0 (by linarith)
  have hT4 : T ≤ 1 / 4 := by simp only [T]; nlinarith [sq_nonneg (2 * θ - 1)]
  have hX2 : 0 ≤ X2 := sq_nonneg _
  have hXD : X2 ≤ D ^ 2 := by
    simp only [X2, D]
    nlinarith [hx.1, hx.2, hx'.1, hx'.2]
  have he : |e| ≤ M₂ / 2 * T * X2 := chord_error_le hgc hg' hg'' hM₂ hx hx' h0 h1
  have hgx := hmaps hx
  have hgx' := hmaps hx'
  have hH : |H| ≤ D := by
    rw [abs_le]
    simp only [H, D]
    constructor <;> nlinarith [hy.1, hy.2, hy'.1, hy'.2, hgx.1, hgx.2, hgx'.1, hgx'.2]
  have hE0 : 0 ≤ M₂ / 2 * T * X2 := by positivity
  have hHe : -(D * (M₂ / 2 * T * X2)) ≤ H * e := by
    have : |H * e| ≤ D * (M₂ / 2 * T * X2) := by
      rw [abs_mul]
      exact mul_le_mul hH he (abs_nonneg _) (by simp only [D]; linarith)
    linarith [neg_abs_le (H * e)]
  have hEE : M₂ / 2 * T * X2 ≤ M₂ / 8 * D ^ 2 := by
    have := mul_le_mul hT4 hXD hX2 (by norm_num)
    nlinarith
  have he2 : e ^ 2 ≤ (M₂ / 2 * T * X2) * (M₂ / 8 * D ^ 2) := by
    have h1' : e ^ 2 ≤ (M₂ / 2 * T * X2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) he 2
    nlinarith
  have hlip := lipschitz_of_deriv_le hgc hg' hM₁ hx hx'
  have hΔg : (g x - g x') ^ 2 ≤ M₁ ^ 2 * X2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hlip 2
    rw [sq_abs, mul_pow, sq_abs] at this
    exact this
  have hsq : -((g x - g x') ^ 2 / 2) ≤
      -((y - y') ^ 2 / 4) + ((y - g x) - (y' - g x')) ^ 2 / 2 := by
    nlinarith [sq_nonneg ((y - y') / 2 - (g x - g x'))]
  have m1 := mul_le_mul_of_nonneg_left hsq hT
  have m2 := mul_le_mul_of_nonneg_left hΔg hT
  rw [show bmK a b M₁ M₂ = M₁ ^ 2 + D * M₂ + M₂ ^ 2 * D ^ 2 / 16 + 1 from rfl]
  linarith

/-! ### The dynamic program on `[a, b]` -/

/-- `F` on `X × X`, `X = [a, b]`. -/
noncomputable def bmFs (g : ℝ → ℝ) (K : ℝ) (p : Icc a b × Icc a b) : ℝ := bmF g K p.1.1 p.2.1

theorem bm_assumption43 (hab : a < b) : Assumption43 (fun _ : Icc a b => (univ : Set (Icc a b))) :=
  have hne : (univ : Set (Icc a b)).Nonempty := ⟨⟨a, left_mem_Icc.2 hab.le⟩, mem_univ _⟩
  ⟨fun _ => hne, fun _ => isCompact_univ, fun _ => ⟨hne, fun y _ _ _ =>
    ⟨0, fun _ => y, fun _ _ => mem_univ _, tendsto_const_nhds⟩⟩,
    fun _ => ⟨hne, fun _ _ ys _ => by
      obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
      exact ⟨y, mem_univ _, φ, hφ, hlim⟩⟩⟩

theorem continuous_bmFs (hgc : ContinuousOn g (Icc a b)) (K : ℝ) :
    Continuous (bmFs (a := a) (b := b) g K) := by
  have hg : Continuous fun x : Icc a b => g x.1 :=
    hgc.comp_continuous continuous_subtype_val fun x => x.2
  have h1 : Continuous fun p : Icc a b × Icc a b => p.1.1 :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun p : Icc a b × Icc a b => p.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have h3 : Continuous fun p : Icc a b × Icc a b => g p.1.1 := hg.comp continuous_fst
  unfold bmFs bmF
  exact ((continuous_const.mul (h1.pow 2)).div_const _).neg.add ((h2.pow 2).div_const _) |>.sub
    (((h2.sub h3).pow 2).div_const _)

theorem bm_assumption44 (hab : a < b) (hgc : ContinuousOn g (Icc a b)) (hM₂ : 0 ≤ M₂) :
    Assumption44 (fun _ : Icc a b => (univ : Set (Icc a b))) (bmFs g (bmK a b M₁ M₂))
      (1 / (2 * bmK a b M₁ M₂)) := by
  have hK := one_le_bmK (M₁ := M₁) hab hM₂
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_bmFs (a := a) (b := b) hgc (bmK a b M₁ M₂)).continuousOn
  refine ⟨(continuous_bmFs hgc _).continuousOn, ⟨B, fun p _ => hB p (mem_univ _)⟩,
    by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- **Assumption 4.7** for `F` (strict concavity, with the strict gap when `x ≠ x'`). -/
theorem bm_assumption47 (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) :
    Assumption47 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b)))
      (bmFs g (bmK a b M₁ M₂)) := by
  intro x y x' y' _ _ θ h0 h1
  have hgap := bm_gap_ge hab hmaps hgc hg' hg'' hM₁ hM₂ x.2 y.2 x'.2 y'.2 h0.le h1.le
  have e : bmFs g (bmK a b M₁ M₂) (cmb (convex_Icc a b) h0.le h1.le x x',
      cmb (convex_Icc a b) h0.le h1.le y y') =
      bmF g (bmK a b M₁ M₂) (θ * x.1 + (1 - θ) * x'.1) (θ * y.1 + (1 - θ) * y'.1) := by
    simp [bmFs, cmb, smul_eq_mul]
  rw [e]
  simp only [bmFs]
  have hT : 0 < θ * (1 - θ) := mul_pos h0 (by linarith)
  refine ⟨by nlinarith [sq_nonneg (x.1 - x'.1)], fun hne => ?_⟩
  have hx : x.1 ≠ x'.1 := fun h => hne (Subtype.ext h)
  have : 0 < (x.1 - x'.1) ^ 2 := by positivity
  nlinarith

/-- **Assumption 4.8**: `Γ(x) = X` has a convex graph. -/
theorem bm_assumption48 :
    Assumption48 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b))) :=
  fun _ _ _ _ _ _ _ _ _ => mem_univ _

/-- **Assumption 4.9**: `F` is continuously differentiable on the interior of `A`. -/
theorem bm_assumption49 (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (K : ℝ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => bmF g K p.1 p.2) (Ioo a b ×ˢ Ioo a b) := by
  have hgC : ContDiffOn ℝ 1 g (Ioo a b) := by
    have h := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 0) (f := g)
      (isOpen_Ioo (a := a) (b := b))).2
    refine h ⟨fun x hx => (hg' x hx).differentiableAt.differentiableWithinAt,
      fun h0 => by simp at h0, ?_⟩
    refine contDiffOn_zero.2 ?_
    refine ContinuousOn.congr (f := g') (fun x hx => (hg'' x hx).continuousAt.continuousWithinAt)
      fun x hx => (hg' x hx).deriv
  have hgfst : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => g p.1) (Ioo a b ×ˢ Ioo a b) :=
    hgC.comp contDiffOn_fst fun p hp => hp.1
  unfold bmF
  exact (((contDiffOn_const.mul (contDiffOn_fst.pow 2)).div_const _).neg.add
    ((contDiffOn_snd.pow 2).div_const _)).sub (((contDiffOn_snd.sub hgfst).pow 2).div_const _)

/-- `v = U`, `U(x) = −Kx²/2`, as a bounded continuous function on `[a, b]`. -/
noncomputable def bmV (a b K : ℝ) : Icc a b →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => -(K * x.1 ^ 2 / 2), by fun_prop⟩

/-- The objective telescopes: `F(x, y) + βU(y) = U(x) − (y − g(x))²/2`. -/
theorem bm_obj {K : ℝ} (hK : 0 < K) (x y : Icc a b) :
    obj (bmFs g K) (1 / (2 * K)) (bmV a b K) (x, y) =
      -(K * x.1 ^ 2 / 2) - (y.1 - g x.1) ^ 2 / 2 := by
  simp only [obj, bmFs, bmF, bmV, mkOfCompact_apply, ContinuousMap.coe_mk]
  field_simp
  ring

/-- `U` solves (FE), and the maximum is attained exactly at `y = g(x)`. -/
theorem bellman_bm (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hM₂ : 0 ≤ M₂) :
    bellman (bm_assumption43 hab) (bm_assumption44 (M₁ := M₁) hab hgc hM₂)
        (bmV a b (bmK a b M₁ M₂)) = bmV a b (bmK a b M₁ M₂) ∧
      ∀ x, argmax (obj (bmFs g (bmK a b M₁ M₂)) (1 / (2 * bmK a b M₁ M₂))
        (bmV a b (bmK a b M₁ M₂))) (fun _ : Icc a b => (univ : Set (Icc a b))) x =
          {⟨g x.1, hmaps x.2⟩} := by
  have hK : 0 < bmK a b M₁ M₂ := lt_of_lt_of_le one_pos (one_le_bmK hab hM₂)
  -- the maximum value is `U(x)`, attained at `g(x)`
  have hgr : ∀ x : Icc a b, IsGreatest ((fun y => obj (bmFs g (bmK a b M₁ M₂))
      (1 / (2 * bmK a b M₁ M₂)) (bmV a b (bmK a b M₁ M₂)) (x, y)) '' (univ : Set (Icc a b)))
      (-(bmK a b M₁ M₂ * x.1 ^ 2 / 2)) := fun x => by
    refine ⟨⟨⟨g x.1, hmaps x.2⟩, mem_univ _, ?_⟩, ?_⟩
    · simp only [bm_obj hK, sub_self]; ring
    · rintro _ ⟨y, -, rfl⟩
      simp only [bm_obj hK]
      nlinarith [sq_nonneg (y.1 - g x.1)]
  have hmax : ∀ x : Icc a b, maxValue (obj (bmFs g (bmK a b M₁ M₂)) (1 / (2 * bmK a b M₁ M₂))
      (bmV a b (bmK a b M₁ M₂))) (fun _ => univ) x = -(bmK a b M₁ M₂ * x.1 ^ 2 / 2) :=
    fun x => (hgr x).csSup_eq
  refine ⟨?_, fun x => ?_⟩
  · ext x
    rw [bellman_apply, hmax]
    simp [bmV]
  · ext y
    rw [mem_singleton_iff]
    change (y ∈ univ ∧ _ = _) ↔ _
    rw [hmax, bm_obj hK]
    constructor
    · rintro ⟨-, hy⟩
      have h0 : (y.1 - g x.1) ^ 2 = 0 := by linarith
      exact Subtype.ext (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0))
    · rintro rfl
      exact ⟨mem_univ _, by simp⟩

/-- **Theorem 6.1 (Boldrin and Montrucchio).** Let `X = [a, b]` and let `g : X → X` be twice
differentiable on `(a, b)`, continuous on `X`, with `|g'| ≤ M₁` and `|g''| ≤ M₂`. With
`F(x, y) = −Kx²/2 + y²/4 − (y − g(x))²/2` and `β = 1/(2K)`, `K = bmK a b M₁ M₂`, and `Γ(x) = X`,
Assumptions 4.3–4.4 and 4.7–4.9 hold, and for the fixed point `v` of `T` (Theorem 4.6) the policy
correspondence is `G(x) = {g(x)}`: `g` is the optimal policy function. -/
theorem theorem_6_1 (hab : a < b) (hmaps : MapsTo g (Icc a b) (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x) (hM₁ : ∀ x ∈ Ioo a b, |g' x| ≤ M₁)
    (hM₂ : ∀ x ∈ Ioo a b, |g'' x| ≤ M₂) :
    ∃ (h43 : Assumption43 (fun _ : Icc a b => (univ : Set (Icc a b))))
      (h44 : Assumption44 (fun _ : Icc a b => (univ : Set (Icc a b))) (bmFs g (bmK a b M₁ M₂))
        (1 / (2 * bmK a b M₁ M₂))),
      Assumption47 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b)))
          (bmFs g (bmK a b M₁ M₂)) ∧
        Assumption48 (convex_Icc a b) (fun _ : Icc a b => (univ : Set (Icc a b))) ∧
        ContDiffOn ℝ 1 (fun p : ℝ × ℝ => bmF g (bmK a b M₁ M₂) p.1 p.2) (Ioo a b ×ˢ Ioo a b) ∧
        ∀ v, bellman h43 h44 v = v → ∀ x,
          argmax (obj (bmFs g (bmK a b M₁ M₂)) (1 / (2 * bmK a b M₁ M₂)) v)
            (fun _ : Icc a b => (univ : Set (Icc a b))) x = {⟨g x.1, hmaps x.2⟩} := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ _ hmid)
  have : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.2 hab.le⟩⟩
  obtain ⟨hfix, hargmax⟩ := bellman_bm (M₁ := M₁) hab hmaps hgc hM₂0
  obtain ⟨v₀, -, huniq, -⟩ := theorem_4_6 (bm_assumption43 hab)
    (bm_assumption44 (M₁ := M₁) hab hgc hM₂0)
  refine ⟨bm_assumption43 hab, bm_assumption44 hab hgc hM₂0,
    bm_assumption47 hab hmaps hgc hg' hg'' hM₁ hM₂, bm_assumption48,
    bm_assumption49 hg' hg'' _, fun v hv x => ?_⟩
  rw [(huniq v hv).trans (huniq _ hfix).symm]
  exact hargmax x

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cycles of the logistic map

SLP Exercise 6.3, p. 139: `x_{t+1} = g(x_t) = 4x_t − 4x_t²`.

* **Exercise 6.3a** (`ex_6_3a`): `g` maps `[0, 1]` into itself, and its stationary points are
  `0` and `3/4`.
* **Exercise 6.3b**: `g²` at `0, 1/4, 1/2, 3/4, 1` (`ex_6_3b_values`). There is a two-cycle,
  `(5 − √5)/8 ↔ (5 + √5)/8` (`ex_6_3b_two_cycle`). There is a three-cycle,
  `sin²(π/7) → sin²(2π/7) → sin²(4π/7)` (`ex_6_3b_three_cycle`), because
  `g(sin²θ) = sin²(2θ)` (`logistic_sin_sq`).
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Set Real

/-- The logistic map `g(x) = 4x − 4x²`. -/
def logistic (x : ℝ) : ℝ := 4 * x - 4 * x ^ 2

/-- **Exercise 6.3a.** `g : [0, 1] → [0, 1]`, with stationary points `0` and `3/4`. -/
theorem ex_6_3a :
    MapsTo logistic (Icc 0 1) (Icc 0 1) ∧
      ∀ x, logistic x = x ↔ x = 0 ∨ x = 3 / 4 := by
  refine ⟨fun x hx => ⟨?_, ?_⟩, fun x => ?_⟩
  · simp only [logistic]; nlinarith [hx.1, hx.2]
  · simp only [logistic]; nlinarith [sq_nonneg (2 * x - 1)]
  · simp only [logistic]
    constructor
    · intro h
      have : x * (3 - 4 * x) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num

/-- **Exercise 6.3b.** `g²` at `x = 0, 1/4, 1/2, 3/4, 1`. -/
theorem ex_6_3b_values :
    logistic^[2] 0 = 0 ∧ logistic^[2] (1 / 4) = 3 / 4 ∧ logistic^[2] (1 / 2) = 0 ∧
      logistic^[2] (3 / 4) = 3 / 4 ∧ logistic^[2] 1 = 0 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, logistic]
  norm_num

/-- **Exercise 6.3b.** A two-cycle: `(5 − √5)/8 ↔ (5 + √5)/8`. -/
theorem ex_6_3b_two_cycle :
    ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ x ≠ y ∧ logistic x = y ∧ logistic y = x := by
  have h5 : sqrt 5 ^ 2 = 5 := sq_sqrt (by norm_num)
  have hs0 : 0 < sqrt 5 := sqrt_pos.2 (by norm_num)
  have hs3 : sqrt 5 < 3 := by nlinarith
  refine ⟨(5 - sqrt 5) / 8, (5 + sqrt 5) / 8, ⟨by linarith, by linarith⟩, ⟨by linarith,
    by linarith⟩, by intro h; linarith, ?_, ?_⟩ <;> simp only [logistic] <;> nlinarith

/-- `g(sin²θ) = sin²(2θ)`. -/
theorem logistic_sin_sq (θ : ℝ) : logistic (sin θ ^ 2) = sin (2 * θ) ^ 2 := by
  simp only [logistic, sin_two_mul]
  have := sin_sq_add_cos_sq θ
  nlinarith [this]

/-- **Exercise 6.3b.** A three-cycle: `sin²(π/7) → sin²(2π/7) → sin²(4π/7) → sin²(π/7)`, with
three distinct points. -/
theorem ex_6_3b_three_cycle :
    ∃ x y z : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ z ∈ Icc 0 1 ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      logistic x = y ∧ logistic y = z ∧ logistic z = x := by
  have hpi := pi_pos
  set x := sin (π / 7) ^ 2
  set y := sin (2 * (π / 7)) ^ 2
  set z := sin (2 * (2 * (π / 7))) ^ 2
  have hsq : ∀ θ : ℝ, sin θ ^ 2 ∈ Icc (0 : ℝ) 1 := fun θ =>
    ⟨sq_nonneg _, by rw [sin_sq]; linarith [sq_nonneg (cos θ)]⟩
  -- `sin(8π/7)² = sin(π/7)²`
  have h8 : sin (2 * (2 * (2 * (π / 7)))) ^ 2 = x := by
    have : 2 * (2 * (2 * (π / 7))) = π / 7 + π := by ring
    rw [this, sin_add_pi, neg_sq]
  -- `sin(4π/7) = sin(3π/7)`
  have h4 : sin (2 * (2 * (π / 7))) = sin (3 * (π / 7)) := by
    rw [← sin_pi_sub]; congr 1; ring
  -- `sin` rises on `(0, π/2)`
  have hlt : ∀ a b : ℝ, 0 < a → a < b → b ≤ π / 2 → sin a ^ 2 < sin b ^ 2 := fun a b ha hab hb =>
    by
      have h1 := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hb hab
      have h2 : 0 < sin a := sin_pos_of_pos_of_lt_pi ha (by linarith)
      nlinarith
  have hxy : x < y := hlt _ _ (by positivity) (by linarith) (by linarith)
  have hyz : y < z := by
    simp only [y, z, h4]
    exact hlt _ _ (by positivity) (by linarith) (by linarith)
  refine ⟨x, y, z, hsq _, hsq _, hsq _, hxy.ne, hyz.ne, (hxy.trans hyz).ne, logistic_sin_sq _,
    logistic_sin_sq _, ?_⟩
  rw [logistic_sin_sq, h8]

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Global stability: Liapounov functions

SLP §6.2, pp. 139–143.

* **Lemma 6.2** (`lemma_6_2`): on a compact metric space `X`, let `g : X → X` be continuous with
  `g(x̄) = x̄`, and let `L` be continuous with (b) `L[g(x)] ≥ L(x)`, with equality only at `x̄`.
  Then `x_{t+1} = g(x_t)` converges to `x̄` from every `x₀`. Hypothesis (a) (`L ≤ 0`, zero only at
  `x̄`) is not needed: `L` is bounded on the compact `X` (`lemma_6_2_book` states the book's form).
* **The value loss** `L(x) = (x − x̄)·[v'(x) − v'(x̄)]` (p. 142), in a real inner product space.
  * (a) holds when `v` is strictly concave (`valueLoss_nonpos`).
  * From (3)–(5): (6) `v'(x̄) = F_x(x̄, x̄) = −F_y(x̄, x̄)/β` (`six`), and (7)
    `L(x) − βL[g(x)] ≤ 0`, with equality only at `x̄` (`seven`). So with `β = 1`, `L` satisfies
    (b) (`valueLoss_beta_one`).
  * Condition (8) gives `L[g(x)] ≥ L(x)` (`valueLoss_of_eight`), and strict (8) gives (b).
  * With (b), paths from a compact invariant set converge to `x̄` (`globally_stable`).
* **Exercise 6.4** (quadratic `F` on `ℝ`).
  * (8) holds iff `βbd ≥ (1 + β)²c²/4` (`ex_6_4`).
  * The book's condition `bd − (1 + β)²c²/4 ≥ 0` is not sufficient
    (`ex_6_4_book_condition_fails`).
  * `x̄` is the unique stationary point iff `(1 + β)c + d + βb ≠ 0` (`ex_6_4_stationary`). That can
    fail for a strictly concave `F` (`ex_6_4_not_unique`), but not under the strict form of the
    corrected condition (`ex_6_4_unique_of_eight`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

/-! ### Lemma 6.2 -/

/-- **Lemma 6.2** (without hypothesis (a)). -/
theorem lemma_6_2 {X : Type*} [MetricSpace X] [CompactSpace X] {g : X → X} (hg : Continuous g)
    {xbar : X} {L : X → ℝ} (hL : Continuous L)
    (hb : ∀ x, L x ≤ L (g x) ∧ (L (g x) = L x → x = xbar)) (x₀ : X) :
    Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar) := by
  set x : ℕ → X := fun t => g^[t] x₀
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => Function.iterate_succ_apply' g t x₀
  -- `L(x_t)` rises and is bounded, so it converges
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hL.continuousOn
  have hmono : Monotone fun t => L (x t) := monotone_nat_of_le_succ fun t => by
    rw [hstep]; exact (hb _).1
  have hbdd : BddAbove (range fun t => L (x t)) := ⟨B, by
    rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (by simpa using hB (x t) (mem_univ _))⟩
  have hLlim := tendsto_atTop_ciSup hmono hbdd
  set L₀ := ⨆ t, L (x t)
  -- every subsequence has a further subsequence converging to `x̄`
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, -, φ, hφ, hy⟩ := isCompact_univ.tendsto_subseq (x := fun n => x (ns n))
    fun _ => mem_univ _
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have h1 : L y = L₀ := tendsto_nhds_unique ((hL.tendsto y).comp hy) (hLlim.comp hsub)
  have h2 : L (g y) = L₀ := by
    have hgy : Tendsto (fun n => x (ns (φ n) + 1)) atTop (𝓝 (g y)) := by
      simp only [hstep]
      exact (hg.tendsto y).comp hy
    exact tendsto_nhds_unique ((hL.tendsto (g y)).comp hgy)
      (hLlim.comp ((tendsto_add_atTop_nat 1).comp hsub))
  have : y = xbar := (hb y).2 (h2.trans h1.symm)
  rw [← this]
  exact hy

/-- **Lemma 6.2** as stated in the book, with both (a) and (b). -/
theorem lemma_6_2_book {X : Type*} [MetricSpace X] [CompactSpace X] {g : X → X}
    (hg : Continuous g) {xbar : X} (_hfix : g xbar = xbar) {L : X → ℝ} (hL : Continuous L)
    (_ha : ∀ x, L x ≤ 0 ∧ (L x = 0 → x = xbar))
    (hb : ∀ x, L x ≤ L (g x) ∧ (L (g x) = L x → x = xbar)) (x₀ : X) :
    Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar) :=
  lemma_6_2 hg hL hb x₀

/-! ### The value loss -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The value loss `L(x) = (x − x̄)·[v'(x) − v'(x̄)]`. -/
def valueLoss (v' : E → E) (xbar x : E) : ℝ := inner ℝ (x - xbar) (v' x - v' xbar)

/-- **(a)** for the value loss: `L ≤ 0`, with equality only at `x̄`, when `v` is strictly concave
with gradient `v'`. -/
theorem valueLoss_nonpos [CompleteSpace E] {X : Set E} {v : E → ℝ} {v' : E → E}
    (hv : StrictConcaveOn ℝ X v)
    (hd : ∀ x ∈ X, HasGradientAt v (v' x) x) {xbar : E} (hxbar : xbar ∈ X) {x : E}
    (hx : x ∈ X) : valueLoss v' xbar x ≤ 0 ∧ (valueLoss v' xbar x = 0 → x = xbar) := by
  -- tangent inequalities, strict off the point of tangency
  have tan : ∀ p ∈ X, ∀ q ∈ X, v q ≤ v p + inner ℝ (v' p) (q - p) := fun p hp q hq => by
    have := concave_le_fderiv hv.concaveOn hp hq (hd p hp).hasFDerivAt
    simpa using this
  have tanlt : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → v q < v p + inner ℝ (v' p) (q - p) :=
    fun p hp q hq hpq => by
      have hm : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ X :=
        hv.1 hp hq (by norm_num) (by norm_num) (by norm_num)
      have h1 := tan p hp _ hm
      have h2 := hv.2 hp hq hpq (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num)
      have e : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q - p = (1 / 2 : ℝ) • (q - p) := by module
      rw [e, inner_smul_right] at h1
      simp only [smul_eq_mul] at h2
      linarith
  have key : ∀ p ∈ X, ∀ q ∈ X, inner ℝ (p - q) (v' p - v' q) ≤ 0 := fun p hp q hq => by
    have h1 := tan p hp q hq
    have h2 := tan q hq p hp
    have e : inner ℝ (p - q) (v' p - v' q) =
        -(inner ℝ (v' p) (q - p)) - inner ℝ (v' q) (p - q) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  refine ⟨key x hx xbar hxbar, fun h0 => by_contra fun hne => ?_⟩
  have h1 := tanlt x hx xbar hxbar hne
  have h2 := tanlt xbar hxbar x hx (Ne.symm hne)
  have e : inner ℝ (x - xbar) (v' x - v' xbar) =
      -(inner ℝ (v' x) (xbar - x)) - inner ℝ (v' xbar) (x - xbar) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  simp only [valueLoss] at h0
  linarith

/-- The facts of p. 142: on a set `A` of pairs containing `(x̄, x̄)` and the graph of `g`,
(3) the gradient `(F_x, F_y)` of `F` is strictly monotone, (4) `F_y[x, g(x)] = −βv'[g(x)]` and
(5) `F_x[x, g(x)] = v'(x)`. -/
structure LossFacts (A : Set (E × E)) (Fx Fy : E → E → E) (v' g : E → E) (β : ℝ) (xbar : E) where
  fix : g xbar = xbar
  mem_bar : (xbar, xbar) ∈ A
  three : ∀ p ∈ A, ∀ q ∈ A,
    inner ℝ (p.1 - q.1) (Fx p.1 p.2 - Fx q.1 q.2) + inner ℝ (p.2 - q.2) (Fy p.1 p.2 - Fy q.1 q.2) ≤
      0 ∧ (inner ℝ (p.1 - q.1) (Fx p.1 p.2 - Fx q.1 q.2) +
        inner ℝ (p.2 - q.2) (Fy p.1 p.2 - Fy q.1 q.2) = 0 → p = q)
  four : ∀ x, (x, g x) ∈ A → Fy x (g x) = -(β • v' (g x))
  five : ∀ x, (x, g x) ∈ A → Fx x (g x) = v' x

namespace LossFacts

variable {A : Set (E × E)} {Fx Fy : E → E → E} {v' g : E → E} {β : ℝ} {xbar : E}
  (H : LossFacts A Fx Fy v' g β xbar)
include H

/-- (6): `v'(x̄) = F_x(x̄, x̄)` and `F_y(x̄, x̄) = −βv'(x̄)`. -/
theorem six : v' xbar = Fx xbar xbar ∧ Fy xbar xbar = -(β • v' xbar) := by
  have hA : (xbar, g xbar) ∈ A := by rw [H.fix]; exact H.mem_bar
  have h4 := H.four xbar hA
  have h5 := H.five xbar hA
  rw [H.fix] at h4 h5
  exact ⟨h5.symm, h4⟩

/-- (7): `L(x) − βL[g(x)] ≤ 0`, with equality only at `x̄`. -/
theorem seven {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x - β * valueLoss v' xbar (g x) ≤ 0 ∧
      (valueLoss v' xbar x - β * valueLoss v' xbar (g x) = 0 → x = xbar) := by
  obtain ⟨h6x, h6y⟩ := H.six
  have e : inner ℝ ((x, g x).1 - (xbar, xbar).1) (Fx (x, g x).1 (x, g x).2 - Fx xbar xbar) +
      inner ℝ ((x, g x).2 - (xbar, xbar).2) (Fy (x, g x).1 (x, g x).2 - Fy xbar xbar) =
      valueLoss v' xbar x - β * valueLoss v' xbar (g x) := by
    simp only [H.four x hx, H.five x hx, h6y, ← h6x, valueLoss]
    rw [show -(β • v' (g x)) - -(β • v' xbar) = -(β • (v' (g x) - v' xbar)) by
      rw [smul_sub]; abel, inner_neg_right, inner_smul_right]
    ring
  obtain ⟨h3, h3eq⟩ := H.three (x, g x) hx (xbar, xbar) H.mem_bar
  rw [e] at h3 h3eq
  exact ⟨h3, fun h0 => (Prod.mk.inj (h3eq h0)).1⟩

/-- With `β = 1`, the value loss satisfies (b) of Lemma 6.2. -/
theorem valueLoss_beta_one (hβ : β = 1) {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x ≤ valueLoss v' xbar (g x) ∧
      (valueLoss v' xbar (g x) = valueLoss v' xbar x → x = xbar) := by
  obtain ⟨h7, h7eq⟩ := H.seven hx
  rw [hβ, one_mul] at h7 h7eq
  exact ⟨by linarith, fun h => h7eq (by linarith)⟩

/-- (8) gives `L[g(x)] ≥ L(x)` when `β > 0`; strict (8) off `(x̄, x̄)` gives (b). -/
theorem valueLoss_of_eight (hβ : 0 < β)
    (h8 : ∀ p ∈ A, β * inner ℝ (p.1 - xbar) (Fx p.1 p.2 - Fx xbar xbar) +
      inner ℝ (p.2 - xbar) (Fy p.1 p.2 - Fy xbar xbar) ≤ 0) {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x ≤ valueLoss v' xbar (g x) := by
  obtain ⟨h6x, h6y⟩ := H.six
  have h := h8 (x, g x) hx
  simp only [H.four x hx, H.five x hx, h6y, ← h6x] at h
  rw [show -(β • v' (g x)) - -(β • v' xbar) = -(β • (v' (g x) - v' xbar)) by
    rw [smul_sub]; abel, inner_neg_right, inner_smul_right] at h
  simp only [valueLoss]
  nlinarith

theorem valueLoss_of_eight_strict (hβ : 0 < β)
    (h8 : ∀ p ∈ A, p ≠ (xbar, xbar) → β * inner ℝ (p.1 - xbar) (Fx p.1 p.2 - Fx xbar xbar) +
      inner ℝ (p.2 - xbar) (Fy p.1 p.2 - Fy xbar xbar) < 0) {x : E} (hx : (x, g x) ∈ A) :
    valueLoss v' xbar x ≤ valueLoss v' xbar (g x) ∧
      (valueLoss v' xbar (g x) = valueLoss v' xbar x → x = xbar) := by
  obtain ⟨h6x, h6y⟩ := H.six
  have e : ∀ p : E × E, p = (x, g x) →
      β * inner ℝ (p.1 - xbar) (Fx p.1 p.2 - Fx xbar xbar) +
        inner ℝ (p.2 - xbar) (Fy p.1 p.2 - Fy xbar xbar) =
      β * (valueLoss v' xbar x - valueLoss v' xbar (g x)) := by
    rintro p rfl
    simp only [H.four x hx, H.five x hx, h6y, ← h6x, valueLoss]
    rw [show -(β • v' (g x)) - -(β • v' xbar) = -(β • (v' (g x) - v' xbar)) by
      rw [smul_sub]; abel, inner_neg_right, inner_smul_right]
    ring
  by_cases hxb : x = xbar
  · subst hxb
    simp [H.fix]
  · have hne : (x, g x) ≠ (xbar, xbar) := fun h => hxb (Prod.mk.inj h).1
    have h := h8 (x, g x) hx hne
    rw [e _ rfl] at h
    have hlt : valueLoss v' xbar x - valueLoss v' xbar (g x) < 0 := by
      by_contra hc
      push Not at hc
      have := mul_nonneg hβ.le hc
      linarith
    exact ⟨by linarith, fun h0 => (by linarith : False).elim⟩

end LossFacts

omit [InnerProductSpace ℝ E] in
/-- **Global stability from a Liapounov function on a compact set.** If `g` maps a compact
`X ⊆ E` into itself continuously, and a continuous `L` satisfies (b) on `X`, then every path
from `X` converges to `x̄`. With the value loss, (b) holds for `β = 1` (`valueLoss_beta_one`) or
under strict (8) (`valueLoss_of_eight_strict`). -/
theorem globally_stable {X : Set E} (hX : IsCompact X) {g : E → E} (hgX : MapsTo g X X)
    (hgc : ContinuousOn g X) {xbar : E} (hxbar : xbar ∈ X) {L : E → ℝ} (hL : ContinuousOn L X)
    (hb : ∀ x ∈ X, L x ≤ L (g x) ∧ (L (g x) = L x → x = xbar)) {x₀ : E} (hx₀ : x₀ ∈ X) :
    Tendsto (fun t => g^[t] x₀) atTop (𝓝 xbar) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX
  set gX : X → X := fun x => ⟨g x, hgX x.2⟩
  have hgXc : Continuous gX :=
    (hgc.comp_continuous continuous_subtype_val fun x => x.2).subtype_mk _
  have hLX : Continuous fun x : X => L x := hL.comp_continuous continuous_subtype_val fun x => x.2
  have hlim := lemma_6_2 hgXc (xbar := ⟨xbar, hxbar⟩) hLX (fun x => ⟨(hb x x.2).1,
    fun h => Subtype.ext ((hb x x.2).2 h)⟩) ⟨x₀, hx₀⟩
  have hiter : ∀ t, (gX^[t] ⟨x₀, hx₀⟩).1 = g^[t] x₀ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  have := (continuous_subtype_val.tendsto _).comp hlim
  simpa [Function.comp_def, hiter] using this

/-! ### Exercise 6.4 -/

/-- The quadratic form of (8) for Exercise 6.4: with `u = x − x̄`, `w = y − x̄`,
`β(x − x̄)[F_x(x, y) − F_x(x̄, x̄)] + (y − x̄)[F_y(x, y) − F_y(x̄, x̄)]`
`= βbu² + (1 + β)cuw + dw²`. -/
theorem ex_6_4_form (a b c d β xbar x y : ℝ) :
    β * ((x - xbar) * ((a + b * (x - xbar) + c * (y - xbar)) - (a + b * 0 + c * 0))) +
      (y - xbar) * ((-(β * a) + c * (x - xbar) + d * (y - xbar)) - (-(β * a) + c * 0 + d * 0)) =
    β * b * (x - xbar) ^ 2 + (1 + β) * c * (x - xbar) * (y - xbar) + d * (y - xbar) ^ 2 := by
  ring

/-- **Exercise 6.4 (corrected).** With `d < 0`, (8) holds for all `(x, y)`
if and only if `βbd − (1 + β)²c²/4 ≥ 0`. -/
theorem ex_6_4 {b c d β : ℝ} (hd : d < 0) :
    (∀ u w : ℝ, β * b * u ^ 2 + (1 + β) * c * u * w + d * w ^ 2 ≤ 0) ↔
      0 ≤ β * b * d - (1 + β) ^ 2 * c ^ 2 / 4 := by
  constructor
  · intro h
    -- take `u = 1`, `w = −(1 + β)c/(2d)`
    have := h (2 * d) (-((1 + β) * c))
    nlinarith
  · intro h u w
    -- complete the square in `w`
    have hdd : 0 < -d := by linarith
    have key : 4 * (-d) * (β * b * u ^ 2 + (1 + β) * c * u * w + d * w ^ 2) =
        -(4 * (β * b * d - (1 + β) ^ 2 * c ^ 2 / 4) * u ^ 2) -
          (2 * d * w + (1 + β) * c * u) ^ 2 := by ring
    have : 4 * (-d) * (β * b * u ^ 2 + (1 + β) * c * u * w + d * w ^ 2) ≤ 0 := by
      rw [key]; nlinarith [sq_nonneg u, sq_nonneg (2 * d * w + (1 + β) * c * u)]
    nlinarith

/-- **Exercise 6.4 (correction).** The book's condition `bd − (1 + β)²c²/4 ≥ 0` does not give (8):
with `b = d = −1`, `c = 1/2`, `β = 1/100`, `F` is strictly concave and the book's condition holds,
but (8) fails at `u = 1`, `w = 1/4`. -/
theorem ex_6_4_book_condition_fails :
    let b : ℝ := -1; let c : ℝ := 1 / 2; let d : ℝ := -1; let β : ℝ := 1 / 100
    b < 0 ∧ d < 0 ∧ 0 < b * d - c ^ 2 ∧ 0 ≤ b * d - (1 + β) ^ 2 * c ^ 2 / 4 ∧
      0 < β * b * 1 ^ 2 + (1 + β) * c * 1 * (1 / 4) + d * (1 / 4) ^ 2 := by
  norm_num

/-- The stationary points of Exercise 6.4: `z` is stationary (`F_y(z, z) + βF_x(z, z) = 0`) iff
`[(1 + β)c + d + βb](z − x̄) = 0`; so `x̄` is the unique stationary point iff
`(1 + β)c + d + βb ≠ 0`. -/
theorem ex_6_4_stationary (a b c d β xbar : ℝ) :
    (∀ z, (-(β * a) + c * (z - xbar) + d * (z - xbar)) + β * (a + b * (z - xbar) + c * (z - xbar))
        = 0 → z = xbar) ↔ (1 + β) * c + d + β * b ≠ 0 := by
  constructor
  · intro h h0
    have := h (xbar + 1) (by linear_combination h0)
    linarith
  · intro h z hz
    have : ((1 + β) * c + d + β * b) * (z - xbar) = 0 := by linear_combination hz
    have := (mul_eq_zero.1 this).resolve_left h
    linarith

/-- **Exercise 6.4 (correction).** Strict concavity does not make `x̄` the unique stationary
point: with `b = −4`, `d = −1`, `β = 1/100`, `c = 104/101`, `F` is strictly concave but
`(1 + β)c + d + βb = 0`, so every point is stationary. -/
theorem ex_6_4_not_unique :
    let b : ℝ := -4; let c : ℝ := 104 / 101; let d : ℝ := -1; let β : ℝ := 1 / 100
    b < 0 ∧ d < 0 ∧ 0 < b * d - c ^ 2 ∧ (1 + β) * c + d + β * b = 0 := by
  norm_num

/-- Under the strict form of the corrected condition, `βbd > (1 + β)²c²/4`, the stationary point is
unique. -/
theorem ex_6_4_unique_of_eight {b c d β : ℝ} (h : (1 + β) ^ 2 * c ^ 2 / 4 < β * b * d) :
    (1 + β) * c + d + β * b ≠ 0 := by
  intro h0
  -- `(1 + β)c = −(d + βb)`, and `(d + βb)² ≥ 4βbd`
  have hsq : (1 + β) ^ 2 * c ^ 2 = (d + β * b) ^ 2 := by
    have : (1 + β) * c = -(d + β * b) := by linarith
    rw [show (1 + β) ^ 2 * c ^ 2 = ((1 + β) * c) ^ 2 by ring, this, neg_sq]
  nlinarith [sq_nonneg (d - β * b)]

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear systems

SLP §6.3, pp. 143–147: `x_{t+1} = a₀ + Ax_t`, with `I − A` nonsingular and stationary point
`x̄ = (I − A)⁻¹a₀`, so that `z_t = x_t − x̄` solves `z_{t+1} = Az_t`.

The book argues through the Jordan form, which is not in Mathlib. Here the key fact is proved
for any operator `f` on a finite-dimensional complex normed space:
`fᵗz → 0` iff `z` lies in the **stable subspace**, the sum of the generalized eigenspaces of the
eigenvalues `|μ| < 1` (`tendsto_iff_mem_stable`).

* If `|μ| < 1`, `fᵗv → 0` on the generalized eigenspace of `μ`, by induction on the nilpotency
  index of `f − μ`. Each step solves `a_{t+1} = μa_t + e_t` with `e_t → 0`
  (`tendsto_zero_of_rec`).
* Conversely, the vectors with `fᵗz → 0` form an invariant subspace. If it met the unstable part,
  it would contain an eigenvector of an eigenvalue `|μ| ≥ 1`, along which `fᵗz = μᵗz`.

Then:

* **Theorem 6.3** (`theorem_6_3`): `x_t → x̄` from every `x₀` iff every characteristic root of `A`
  has absolute value less than one.
* **Theorem 6.4** (`theorem_6_4`), as stated in the book: if `A = B⁻¹ΛB` with `Λ` upper triangular
  (a Jordan matrix is one), its first `m` diagonal entries less than one in absolute value and
  the rest not, then `x_t → x̄` iff `x₀ = x̄ + B⁻¹w₀` with `w₀ᵢ = 0` for `i ≥ m`
  (`triangular_tendsto_iff`).
* (9) (`solution_eq`): `x_t = x̄ + B⁻¹ΛᵗB(x₀ − x̄)`.
-/

open Set Filter Topology Module
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

/-! ### A perturbed geometric recursion -/

/-- If `b_{t+1} ≤ rb_t + c_t` with `0 ≤ r < 1`, `b ≥ 0` and `c_t → 0`, then `b_t → 0`. -/
theorem tendsto_zero_of_le_rec {b c : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb0 : ∀ t, 0 ≤ b t) (hc : Tendsto c atTop (𝓝 0)) (hrec : ∀ t, b (t + 1) ≤ r * b t + c t) :
    Tendsto b atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hc) (ε / 2 * (1 - r)) (by
    have : 0 < 1 - r := by linarith
    positivity)
  -- `b_t ≤ r^{t − T}b_T + ε/2` for `t ≥ T`
  have hbound : ∀ k, b (T + k) ≤ r ^ k * b T + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have hcT : c (T + k) ≤ ε / 2 * (1 - r) := by
        have := hT (T + k) (by omega)
        rw [Real.dist_eq, sub_zero] at this
        exact (le_abs_self _).trans this.le
      have := hrec (T + k)
      rw [show T + (k + 1) = T + k + 1 by ring]
      calc b (T + k + 1) ≤ r * b (T + k) + c (T + k) := this
        _ ≤ r * (r ^ k * b T + ε / 2) + ε / 2 * (1 - r) := by
          have := mul_le_mul_of_nonneg_left ih hr0
          linarith
        _ = r ^ (k + 1) * b T + ε / 2 := by ring
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 / (b T + 1) by
    have := hb0 T; positivity) hr1
  refine ⟨T + K, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = T + k := ⟨t - T, by omega⟩
  have hk : r ^ k ≤ r ^ K := pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have h1 : r ^ k * b T < ε / 2 := by
    have hbT := hb0 T
    have : r ^ k * b T ≤ r ^ K * (b T + 1) := by
      have := pow_nonneg hr0 k
      nlinarith
    calc r ^ k * b T ≤ r ^ K * (b T + 1) := this
      _ < ε / 2 / (b T + 1) * (b T + 1) := mul_lt_mul_of_pos_right hK (by linarith)
      _ = ε / 2 := by field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hb0 _)]
  linarith [hbound k]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- If `a_{t+1} = μa_t + e_t` with `|μ| < 1` and `e_t → 0`, then `a_t → 0`. -/
theorem tendsto_zero_of_rec {a e : ℕ → V} {μ : ℂ} (hμ : ‖μ‖ < 1) (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ t, a (t + 1) = μ • a t + e t) : Tendsto a atTop (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_zero_of_le_rec (norm_nonneg μ) hμ
    (fun t => norm_nonneg _) (tendsto_zero_iff_norm_tendsto_zero.1 he) fun t => ?_)
  rw [hrec, ← norm_smul]
  exact norm_add_le _ _

/-! ### The stable subspace -/

/-- The **stable subspace**: the generalized eigenspaces of the eigenvalues with `|μ| < 1`. -/
noncomputable def stableSubspace (f : End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ {μ : ℂ | ‖μ‖ < 1}, f.maxGenEigenspace μ

/-- The **unstable subspace**: the generalized eigenspaces of the eigenvalues with `|μ| ≥ 1`. -/
noncomputable def unstableSubspace (f : End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ {μ : ℂ | 1 ≤ ‖μ‖}, f.maxGenEigenspace μ

/-- The vectors whose orbits converge to zero. -/
noncomputable def convSubspace (f : End ℂ V) : Submodule ℂ V where
  carrier := {z | Tendsto (fun t => (f ^ t) z) atTop (𝓝 0)}
  add_mem' {x y} hx hy := by
    simp only [mem_ofPred_eq, map_add] at hx hy ⊢
    simpa using hx.add hy
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [mem_ofPred_eq, map_smul] at hx ⊢
    simpa using hx.const_smul c

theorem mem_convSubspace {f : End ℂ V} {z : V} :
    z ∈ convSubspace f ↔ Tendsto (fun t => (f ^ t) z) atTop (𝓝 0) := Iff.rfl

/-- On the generalized eigenspace of `|μ| < 1`, orbits converge to zero. -/
theorem tendsto_of_mem_maxGenEigenspace {f : End ℂ V} {μ : ℂ} (hμ : ‖μ‖ < 1) {v : V}
    (hv : v ∈ f.maxGenEigenspace μ) : Tendsto (fun t => (f ^ t) v) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ v).1 hv
  set N := f - μ • (1 : End ℂ V)
  have hcomm : ∀ t, N * f ^ t = f ^ t * N := fun t =>
    ((Commute.sub_left (Commute.refl f) (Commute.smul_left (Commute.one_left f) μ)).pow_right t).eq
  induction k generalizing v with
  | zero => simp only [pow_zero, Module.End.one_apply] at hk; subst hk; simp
  | succ k ih =>
    have hNv : (N ^ k) (N v) = 0 := by rw [← Module.End.mul_apply, ← pow_succ]; exact hk
    have hNv' := ih (Module.End.mem_maxGenEigenspace f μ (N v) |>.2 ⟨k, hNv⟩) hNv
    refine tendsto_zero_of_rec hμ hNv' fun t => ?_
    have h1 : ∀ w, f w = μ • w + N w := fun w => by simp [N]
    calc (f ^ (t + 1)) v = f ((f ^ t) v) := by rw [pow_succ', Module.End.mul_apply]
      _ = μ • (f ^ t) v + N ((f ^ t) v) := h1 _
      _ = μ • (f ^ t) v + (f ^ t) (N v) := by
        rw [← Module.End.mul_apply, hcomm t, Module.End.mul_apply]

/-- Along an eigenvector of `|μ| ≥ 1`, the orbit does not converge to zero. -/
theorem not_tendsto_of_eigen {f : End ℂ V} {μ : ℂ} (hμ : 1 ≤ ‖μ‖) {v : V} (hv : f v = μ • v)
    (hv0 : v ≠ 0) : ¬ Tendsto (fun t => (f ^ t) v) atTop (𝓝 0) := by
  intro h
  have hpow : ∀ t, (f ^ t) v = μ ^ t • v := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have hn := (tendsto_zero_iff_norm_tendsto_zero.1 h)
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have : ∀ t, ‖v‖ ≤ ‖(f ^ t) v‖ := fun t => by
    rw [hpow, norm_smul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hμ)
  have := ge_of_tendsto' hn this
  linarith

theorem stable_le_conv (f : End ℂ V) : stableSubspace f ≤ convSubspace f :=
  iSup₂_le fun _ hμ _ hv => tendsto_of_mem_maxGenEigenspace hμ hv

theorem stable_sup_unstable [FiniteDimensional ℂ V] (f : End ℂ V) :
    stableSubspace f ⊔ unstableSubspace f = ⊤ := by
  refine eq_top_iff.2 ((Module.End.iSup_maxGenEigenspace_eq_top f).symm.le.trans
    (iSup_le fun μ => ?_))
  rcases lt_or_ge ‖μ‖ 1 with h | h
  · exact le_sup_of_le_left (le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from h))
  · exact le_sup_of_le_right (le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | 1 ≤ ‖μ‖} from h))

theorem disjoint_stable_unstable (f : End ℂ V) :
    Disjoint (stableSubspace f) (unstableSubspace f) :=
  (Module.End.independent_maxGenEigenspace f).disjoint_biSup_biSup
    (Set.disjoint_left.2 fun μ h1 h2 => by
      simp only [mem_ofPred_eq] at h1 h2; linarith)

theorem unstable_invariant (f : End ℂ V) {z : V} (hz : z ∈ unstableSubspace f) :
    f z ∈ unstableSubspace f := by
  have : unstableSubspace f ≤ (unstableSubspace f).comap f := iSup₂_le fun μ hμ v hv =>
    (le_biSup (fun μ => f.maxGenEigenspace μ) hμ)
      (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hv)
  exact this hz

/-- **Orbits converge to zero exactly on the stable subspace.** -/
theorem tendsto_iff_mem_stable [FiniteDimensional ℂ V] (f : End ℂ V) (z : V) :
    Tendsto (fun t => (f ^ t) z) atTop (𝓝 0) ↔ z ∈ stableSubspace f := by
  refine ⟨fun hz => ?_, fun hz => stable_le_conv f hz⟩
  -- the convergent vectors meet the unstable subspace only in zero
  set W := convSubspace f ⊓ unstableSubspace f
  have hWinv : ∀ w ∈ W, f w ∈ W := fun w hw => ⟨by
    change Tendsto _ _ _
    have := (mem_convSubspace.1 hw.1).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, pow_succ, Module.End.mul_apply] using this,
    unstable_invariant f hw.2⟩
  have hW : W = ⊥ := by
    by_contra hne
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hWinv)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hfw : f w = μ • (w : V) := by
      have := Module.End.mem_eigenspace_iff.1 hw.1
      rw [Subtype.ext_iff] at this
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hstab : ‖μ‖ < 1 := by
      by_contra hge
      exact not_tendsto_of_eigen (not_lt.1 hge) hfw hw0 (mem_convSubspace.1 w.2.1)
    have hs : (w : V) ∈ stableSubspace f := le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hstab)
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hfw))
    exact hw0 ((Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs w.2.2)
  -- split `z` along stable ⊕ unstable
  have hztop : z ∈ stableSubspace f ⊔ unstableSubspace f := by
    rw [stable_sup_unstable]; exact Submodule.mem_top
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.1 hztop
  have huc : u ∈ convSubspace f := by
    have := (convSubspace f).sub_mem hz (stable_le_conv f hs)
    simpa using this
  have hu0 : u = 0 := by
    have : u ∈ W := ⟨huc, hu⟩
    rw [hW] at this
    exact (Submodule.mem_bot ℂ).1 this
  simpa [hu0] using hs

/-- If every eigenvalue lies inside the unit disc, the stable subspace is everything. -/
theorem stable_eq_top [FiniteDimensional ℂ V] (f : End ℂ V)
    (h : ∀ μ, f.HasEigenvalue μ → ‖μ‖ < 1) : stableSubspace f = ⊤ := by
  have hu : unstableSubspace f = ⊥ := by
    by_contra hne
    have : Nontrivial (unstableSubspace f) := Submodule.nontrivial_iff_ne_bot.2 hne
    have hinv : ∀ w ∈ unstableSubspace f, f w ∈ unstableSubspace f := fun w hw =>
      unstable_invariant f hw
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hinv)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hfw : f w = μ • (w : V) := by
      have := Module.End.mem_eigenspace_iff.1 hw.1
      rw [Subtype.ext_iff] at this
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hstab := h μ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hfw, hw0⟩)
    have hs : (w : V) ∈ stableSubspace f := le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hstab)
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hfw))
    exact hw0 ((Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs w.2)
  have := stable_sup_unstable f
  rwa [hu, sup_bot_eq] at this

/-! ### Matrices -/

variable {ι : Type*}

/-- A real vector as a complex vector. -/
def cplx (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

theorem cplx_sub (x y : ι → ℝ) : cplx (x - y) = cplx x - cplx y := by
  funext i; simp [cplx]

theorem cplx_add (x y : ι → ℝ) : cplx (x + y) = cplx x + cplx y := by
  funext i; simp [cplx]

theorem tendsto_cplx_iff {y : ℕ → ι → ℝ} :
    Tendsto (fun t => cplx (y t)) atTop (𝓝 0) ↔ Tendsto y atTop (𝓝 0) := by
  simp only [tendsto_pi_nhds, cplx, Pi.zero_apply]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => ?_⟩
  · have := (Complex.continuous_re.tendsto 0).comp h
    simpa [Function.comp_def] using this
  · have := (Complex.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using this

variable [Fintype ι] [DecidableEq ι]

/-- `A` acting on `ℂⁿ`. -/
noncomputable def cplxEnd (A : Matrix (ι) (ι) ℝ) : End ℂ (ι → ℂ) :=
  Matrix.toLin' (A.map Complex.ofRealHom)

theorem cplxEnd_pow_cplx (A : Matrix (ι) (ι) ℝ) (t : ℕ) (z : ι → ℝ) :
    (cplxEnd A ^ t) (cplx z) = cplx ((A ^ t) *ᵥ z) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← Matrix.mulVec_mulVec]
    funext i
    simp only [cplxEnd, Matrix.toLin'_apply, cplx]
    exact (RingHom.map_mulVec Complex.ofRealHom A _ i).symm

/-- The characteristic roots of `A` are the eigenvalues of `A` on `ℂⁿ`. -/
theorem hasEigenvalue_cplxEnd_iff (A : Matrix (ι) (ι) ℝ) (μ : ℂ) :
    (cplxEnd A).HasEigenvalue μ ↔ (A.charpoly.map Complex.ofRealHom).IsRoot μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, cplxEnd, Matrix.charpoly_toLin',
    Matrix.charpoly_map]

/-- The stationary point `x̄ = (I − A)⁻¹a₀` and the deviations `x_t − x̄ = Aᵗ(x₀ − x̄)`. -/
theorem deviation_eq (A : Matrix (ι) (ι) ℝ) (a₀ : ι → ℝ) (hI : IsUnit (1 - A).det)
    {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = a₀ + A *ᵥ x t) (t : ℕ) :
    x t - (1 - A)⁻¹ *ᵥ a₀ = (A ^ t) *ᵥ (x 0 - (1 - A)⁻¹ *ᵥ a₀) := by
  set xbar := (1 - A)⁻¹ *ᵥ a₀
  have hbar : xbar = a₀ + A *ᵥ xbar := by
    have h1 : (1 - A) *ᵥ xbar = a₀ := by
      simp only [xbar, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hI, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    rw [← h1]; abel
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hx t, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
    conv_lhs => rw [hbar]
    rw [Matrix.mulVec_sub]
    abel

/-- **Theorem 6.3.** `x_t → x̄` from every `x₀` if and only if every characteristic root of `A` is
less than one in absolute value. -/
theorem theorem_6_3 (A : Matrix (ι) (ι) ℝ) (a₀ : ι → ℝ) (hI : IsUnit (1 - A).det) :
    (∀ x : ℕ → ι → ℝ, (∀ t, x (t + 1) = a₀ + A *ᵥ x t) →
      Tendsto x atTop (𝓝 ((1 - A)⁻¹ *ᵥ a₀))) ↔
    ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1 := by
  set xbar := (1 - A)⁻¹ *ᵥ a₀
  -- convergence from `x₀` is convergence of `Aᵗ(x₀ − x̄)` to zero
  have hconv : ∀ x : ℕ → ι → ℝ, (∀ t, x (t + 1) = a₀ + A *ᵥ x t) →
      (Tendsto x atTop (𝓝 xbar) ↔
        Tendsto (fun t => (A ^ t) *ᵥ (x 0 - xbar)) atTop (𝓝 0)) := fun x hx => by
    rw [← tendsto_sub_nhds_zero_iff, show (fun t => x t - xbar) =
      fun t => (A ^ t) *ᵥ (x 0 - xbar) from funext (deviation_eq A a₀ hI hx)]
  -- every `z` is the initial deviation of some solution
  have hsol : ∀ z : ι → ℝ, ∃ x : ℕ → ι → ℝ, (∀ t, x (t + 1) = a₀ + A *ᵥ x t) ∧
      x 0 - xbar = z := fun z => by
    refine ⟨fun t => Nat.rec (xbar + z) (fun _ y => a₀ + A *ᵥ y) t, fun t => rfl, ?_⟩
    simp
  constructor
  · intro h μ hμ
    by_contra hge
    push Not at hge
    obtain ⟨w, hw⟩ := ((hasEigenvalue_cplxEnd_iff A μ).2 hμ).exists_hasEigenvector
    have hfw : cplxEnd A w = μ • w := Module.End.mem_eigenspace_iff.1 hw.1
    -- real and imaginary parts
    set r : ι → ℝ := fun i => (w i).re
    set q : ι → ℝ := fun i => (w i).im
    have hwrq : w = cplx r + Complex.I • cplx q := by
      funext i
      simp only [r, q, cplx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im _).symm
    have hreal : ∀ z : ι → ℝ, Tendsto (fun t => (A ^ t) *ᵥ z) atTop (𝓝 0) := fun z => by
      obtain ⟨x, hx, hx0⟩ := hsol z
      have := (hconv x hx).1 (h x hx)
      rwa [hx0] at this
    have hc : Tendsto (fun t => (cplxEnd A ^ t) w) atTop (𝓝 0) := by
      have h1 := tendsto_cplx_iff.2 (hreal r)
      have h2 := (tendsto_cplx_iff.2 (hreal q)).const_smul Complex.I
      rw [smul_zero] at h2
      have := h1.add h2
      rw [add_zero] at this
      refine this.congr fun t => ?_
      rw [hwrq, map_add, map_smul, cplxEnd_pow_cplx, cplxEnd_pow_cplx]
    exact not_tendsto_of_eigen hge hfw hw.2 hc
  · intro h x hx
    rw [hconv x hx]
    have htop := stable_eq_top (cplxEnd A) fun μ hμ => h μ ((hasEigenvalue_cplxEnd_iff A μ).1 hμ)
    have := (tendsto_iff_mem_stable (cplxEnd A) (cplx (x 0 - xbar))).2
      (by rw [htop]; exact Submodule.mem_top)
    simp only [cplxEnd_pow_cplx] at this
    exact tendsto_cplx_iff.1 this

variable {n : ℕ}

/-! ### Triangular systems and Theorem 6.4 -/

/-- One step of an upper triangular system, coordinate by coordinate. -/
theorem triangular_step (Λ : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (Λ *ᵥ v) i = Λ i i * v i + ∑ j ∈ Finset.univ.erase i, Λ i j * v j := by
  simp only [Matrix.mulVec, dotProduct]
  exact (Finset.add_sum_erase _ (fun j => Λ i j * v j) (Finset.mem_univ i)).symm

/-- Coordinates beyond `k` stay zero. -/
theorem triangular_invariant (Λ : Matrix (Fin n) (Fin n) ℂ) (hΛ : ∀ i j, j < i → Λ i j = 0)
    {k : ℕ} {w : Fin n → ℂ} (hw : ∀ j : Fin n, k ≤ j.val → w j = 0) (t : ℕ) :
    ∀ j : Fin n, k ≤ j.val → ((Λ ^ t) *ᵥ w) j = 0 := by
  induction t with
  | zero => intro j hj; simpa using hw j hj
  | succ t ih =>
    intro j hj
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l j with hlj | hjl
    · rw [hΛ j l hlj, zero_mul]
    · have := ih l (hj.trans (Fin.le_def.1 hjl))
      simp only [Matrix.mulVec, dotProduct] at this
      rw [this, mul_zero]

/-- **The triangular case.** If `Λ` is upper triangular, with `|Λᵢᵢ| < 1` for `i < m` and
`|Λᵢᵢ| ≥ 1` otherwise, then `Λᵗw → 0` iff `wᵢ = 0` for every `i ≥ m`. -/
theorem triangular_tendsto_iff (Λ : Matrix (Fin n) (Fin n) ℂ) (hΛ : ∀ i j, j < i → Λ i j = 0)
    (m : ℕ) (hs : ∀ i : Fin n, i.val < m → ‖Λ i i‖ < 1)
    (hu : ∀ i : Fin n, m ≤ i.val → 1 ≤ ‖Λ i i‖) (w : Fin n → ℂ) :
    Tendsto (fun t => (Λ ^ t) *ᵥ w) atTop (𝓝 0) ↔ ∀ i : Fin n, m ≤ i.val → w i = 0 := by
  set W : ℕ → Fin n → ℂ := fun t => (Λ ^ t) *ᵥ w
  have hrec : ∀ t i, W (t + 1) i = Λ i i * W t i + ∑ j ∈ Finset.univ.erase i, Λ i j * W t j :=
    fun t i => by
      simp only [W]
      rw [pow_succ', ← Matrix.mulVec_mulVec, triangular_step]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hjm, hj⟩ := hcon
    set S := Finset.univ.filter fun l : Fin n => w l ≠ 0
    have hS : S.Nonempty := ⟨j, by simp [S, hj]⟩
    set J := S.max' hS
    have hJS : J ∈ S := S.max'_mem hS
    have hwJ : w J ≠ 0 := (Finset.mem_filter.1 hJS).2
    have hjJ : j ≤ J := S.le_max' j (by simp [S, hj])
    have hbeyond : ∀ l : Fin n, J.val + 1 ≤ l.val → w l = 0 := fun l hl => by
      by_contra hl0
      have := S.le_max' l (by simp [S, hl0])
      have : l.val ≤ J.val := this
      omega
    have hinv := triangular_invariant Λ hΛ hbeyond
    -- the `J`-th coordinate is `Λ_JJᵗ w_J`
    have hJ : ∀ t, W t J = Λ J J ^ t * w J := by
      intro t
      induction t with
      | zero => simp [W]
      | succ t ih =>
        rw [hrec, ih, Finset.sum_eq_zero, add_zero, pow_succ]
        · ring
        · intro l hl
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlJ | hJl
          · rw [hΛ J l hlJ, zero_mul]
          · rw [show W t l = 0 from hinv t l hJl, mul_zero]
    have hcoord : Tendsto (fun t => W t J) atTop (𝓝 0) := by
      have := ((continuous_apply J).tendsto 0).comp h
      simpa [Function.comp_def] using this
    have hpos : 0 < ‖w J‖ := norm_pos_iff.2 hwJ
    have hge : ∀ t, ‖w J‖ ≤ ‖W t J‖ := fun t => by
      rw [hJ, norm_mul, norm_pow]
      exact le_mul_of_one_le_left (norm_nonneg _)
        (one_le_pow₀ (hu J (hjm.trans (Fin.le_def.1 hjJ))))
    have := ge_of_tendsto' (tendsto_zero_iff_norm_tendsto_zero.1 hcoord) hge
    linarith
  · intro hw
    have hinv := triangular_invariant Λ hΛ hw
    -- downward induction on the coordinates
    have key : ∀ d : ℕ, ∀ i : Fin n, n ≤ i.val + d → Tendsto (fun t => W t i) atTop (𝓝 0) := by
      intro d
      induction d with
      | zero => intro i hi; exact absurd i.2 (by omega)
      | succ d ih =>
        intro i hi
        rcases le_or_gt m i.val with hmi | him
        · simp only [show ∀ t, W t i = 0 from fun t => hinv t i hmi]
          exact tendsto_const_nhds
        · refine tendsto_zero_of_rec (hs i him) ?_ fun t => by rw [hrec, smul_eq_mul]
          rw [show (0 : ℂ) = ∑ j ∈ Finset.univ.erase i, 0 by simp]
          refine tendsto_finsetSum _ fun j hj => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hij
          · simp only [hΛ i j hji, zero_mul]
            exact tendsto_const_nhds
          · have := (ih j (by have : i.val < j.val := hij; omega)).const_mul (Λ i j)
            rwa [mul_zero] at this
    exact tendsto_pi_nhds.2 fun i => key n i (by omega)

theorem map_pow_mulVec_cplx (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) (z : Fin n → ℝ) :
    ((A.map Complex.ofRealHom) ^ t) *ᵥ cplx z = cplx ((A ^ t) *ᵥ z) := by
  have := cplxEnd_pow_cplx A t z
  rw [cplxEnd, ← Matrix.toLin'_pow, Matrix.toLin'_apply] at this
  exact this

theorem conj_pow (B Λ : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) (t : ℕ) :
    (B⁻¹ * Λ * B) ^ t = B⁻¹ * Λ ^ t * B := by
  induction t with
  | zero => simp [Matrix.nonsing_inv_mul _ hB]
  | succ t ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]

/-- **(9).** `x_t = x̄ + B⁻¹ΛᵗB(x₀ − x̄)`. -/
theorem solution_eq (A : Matrix (Fin n) (Fin n) ℝ) (a₀ : Fin n → ℝ) (hI : IsUnit (1 - A).det)
    (B Λ : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det)
    (hA : A.map Complex.ofRealHom = B⁻¹ * Λ * B) {x : ℕ → Fin n → ℝ}
    (hx : ∀ t, x (t + 1) = a₀ + A *ᵥ x t) (t : ℕ) :
    cplx (x t) = cplx ((1 - A)⁻¹ *ᵥ a₀) +
      B⁻¹ *ᵥ ((Λ ^ t) *ᵥ (B *ᵥ cplx (x 0 - (1 - A)⁻¹ *ᵥ a₀))) := by
  have h := congrArg cplx (deviation_eq A a₀ hI hx t)
  rw [← map_pow_mulVec_cplx, hA, conj_pow B Λ hB, cplx_sub] at h
  simp only [Matrix.mulVec_mulVec] at h ⊢
  rw [Matrix.mul_assoc] at h
  rw [← h]
  abel

/-- **Theorem 6.4.** Let `A = B⁻¹ΛB` with `Λ` upper triangular (for instance a Jordan matrix),
`|Λᵢᵢ| < 1` for `i < m` and `|Λᵢᵢ| ≥ 1` for `i ≥ m`. Then `x_t → x̄` iff `x₀ = x̄ + B⁻¹w₀` with
`w₀ᵢ = 0` for every `i ≥ m`. -/
theorem theorem_6_4 (A : Matrix (Fin n) (Fin n) ℝ) (a₀ : Fin n → ℝ) (hI : IsUnit (1 - A).det)
    (B Λ : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det)
    (hA : A.map Complex.ofRealHom = B⁻¹ * Λ * B) (hΛ : ∀ i j, j < i → Λ i j = 0) (m : ℕ)
    (hs : ∀ i : Fin n, i.val < m → ‖Λ i i‖ < 1) (hu : ∀ i : Fin n, m ≤ i.val → 1 ≤ ‖Λ i i‖)
    {x : ℕ → Fin n → ℝ} (hx : ∀ t, x (t + 1) = a₀ + A *ᵥ x t) :
    Tendsto x atTop (𝓝 ((1 - A)⁻¹ *ᵥ a₀)) ↔
      ∃ w₀ : Fin n → ℂ, (∀ i : Fin n, m ≤ i.val → w₀ i = 0) ∧
        cplx (x 0) = cplx ((1 - A)⁻¹ *ᵥ a₀) + B⁻¹ *ᵥ w₀ := by
  set xbar := (1 - A)⁻¹ *ᵥ a₀
  set z₀ := cplx (x 0 - xbar)
  have hB' : B *ᵥ (B⁻¹ *ᵥ z₀) = z₀ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
  have hcont : ∀ M : Matrix (Fin n) (Fin n) ℂ, Continuous fun v : Fin n → ℂ => M *ᵥ v :=
    fun M => continuous_const.matrix_mulVec continuous_id
  have step1 : Tendsto x atTop (𝓝 xbar) ↔
      Tendsto (fun t => (Λ ^ t) *ᵥ (B *ᵥ z₀)) atTop (𝓝 0) := by
    rw [← tendsto_sub_nhds_zero_iff, show (fun t => x t - xbar) =
      fun t => (A ^ t) *ᵥ (x 0 - xbar) from funext (deviation_eq A a₀ hI hx),
      ← tendsto_cplx_iff]
    simp only [← map_pow_mulVec_cplx, hA, conj_pow B Λ hB]
    constructor
    · intro h
      have := ((hcont B).tendsto 0).comp h
      simpa [Function.comp_def, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hB] using this
    · intro h
      have := ((hcont B⁻¹).tendsto 0).comp h
      simpa [Function.comp_def, Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
  rw [step1, triangular_tendsto_iff Λ hΛ m hs hu]
  constructor
  · intro h
    refine ⟨B *ᵥ z₀, h, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
    simp only [z₀, cplx_sub]
    abel
  · rintro ⟨w₀, hw₀, hx0⟩
    have : z₀ = B⁻¹ *ᵥ w₀ := by
      simp only [z₀, cplx_sub, hx0]
      abel
    rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    exact hw₀

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Local stability of nonlinear systems

SLP Theorem 6.5, p. 147: let `x̄` be a stationary point of `x_{t+1} = h(x_t)`, with `h`
differentiable at `x̄` and Jacobian `A`. If every characteristic root of `A` is less than one in
absolute value, then `x_t → x̄` from every `x₀` near `x̄`.

The book cites Scheinkman (1973) and does not prove the theorem. Only differentiability of `h` at
`x̄` is used; the book assumes continuous differentiability on a neighbourhood and that `I − A` is
nonsingular, which follows from the root condition.

The proof:
* by Theorem 6.3, `Aᵗz → 0` for every `z`, so `‖Aᵗ‖ → 0` (`tendsto_opNorm_pow`) and
  `‖Aᵏ‖ ≤ 1/4` for some `k`;
* the `k`-step map `hᵏ` has derivative `Aᵏ` at `x̄`, so it halves distances to `x̄` nearby;
* continuity of `h, …, hᵏ⁻¹` at `x̄` carries convergence along multiples of `k` to all `t`.
-/

open Set Filter Topology Module
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

/-- With every characteristic root inside the unit disc, `Aᵗz → 0` for every real `z`. -/
theorem tendsto_pow_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1) (z : ι → ℝ) :
    Tendsto (fun t => (A ^ t) *ᵥ z) atTop (𝓝 0) := by
  have htop := stable_eq_top (cplxEnd A) fun μ hμ => h μ ((hasEigenvalue_cplxEnd_iff A μ).1 hμ)
  have := (tendsto_iff_mem_stable (cplxEnd A) (cplx z)).2 (by rw [htop]; exact Submodule.mem_top)
  simp only [cplxEnd_pow_cplx] at this
  exact tendsto_cplx_iff.1 this

variable {n : ℕ}

/-- `A` as a continuous linear map on `ℝⁿ`. -/
noncomputable def matCLM (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

theorem matCLM_pow_apply (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) (z : Fin n → ℝ) :
    (matCLM A ^ t) z = (A ^ t) *ᵥ z := by
  induction t generalizing z with
  | zero => simp
  | succ t ih =>
    rw [pow_succ']
    change matCLM A ((matCLM A ^ t) z) = _
    rw [ih, pow_succ', ← Matrix.mulVec_mulVec]
    rfl

/-- Pointwise convergence to zero of powers gives convergence of operator norms. -/
theorem tendsto_opNorm_pow (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1) :
    Tendsto (fun t => ‖matCLM A ^ t‖) atTop (𝓝 0) := by
  set e : Fin n → Fin n → ℝ := fun i => Pi.single i 1
  have hsum : Tendsto (fun t => ∑ i, ‖(matCLM A ^ t) (e i)‖) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ i : Fin n, ‖(0 : Fin n → ℝ)‖ by simp]
    refine tendsto_finsetSum _ fun i _ => ?_
    simp only [matCLM_pow_apply]
    exact (tendsto_pow_mulVec A h (e i)).norm
  -- `‖L‖ ≤ Σᵢ ‖L eᵢ‖`
  have hbound : ∀ t, ‖matCLM A ^ t‖ ≤ ∑ i, ‖(matCLM A ^ t) (e i)‖ := fun t => by
    refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      fun z => ?_
    have hz : z = ∑ i, z i • e i := by
      funext j; simp [e, Pi.single_apply]
    calc ‖(matCLM A ^ t) z‖ = ‖∑ i, z i • (matCLM A ^ t) (e i)‖ := by
          conv_lhs => rw [hz]
          rw [map_sum]; simp only [map_smul]
      _ ≤ ∑ i, ‖z i • (matCLM A ^ t) (e i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖z‖ * ‖(matCLM A ^ t) (e i)‖ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z i) (norm_nonneg _)
      _ = (∑ i, ‖(matCLM A ^ t) (e i)‖) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
  exact squeeze_zero (fun t => norm_nonneg _) hbound hsum

/-- **Theorem 6.5.** Let `h(x̄) = x̄`, with `h` differentiable at `x̄` and Jacobian `A` there. If
every characteristic root of `A` is less than one in absolute value, there is a neighbourhood `U`
of `x̄` such that `x_t → x̄` whenever `x₀ ∈ U`. -/
theorem theorem_6_5 (h : (Fin n → ℝ) → (Fin n → ℝ)) {xbar : Fin n → ℝ} (hfix : h xbar = xbar)
    (A : Matrix (Fin n) (Fin n) ℝ) (hd : HasFDerivAt h (matCLM A) xbar)
    (hroots : ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1) :
    ∃ U ∈ 𝓝 xbar, ∀ x₀ ∈ U, Tendsto (fun t => h^[t] x₀) atTop (𝓝 xbar) := by
  -- a power `Aᵏ` of norm at most `1/4`, with `k ≥ 1`
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_opNorm_pow A hroots).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  set k := k₀ + 1
  have hk : ‖matCLM A ^ k‖ < 1 / 4 := hk₀ k (by omega)
  -- `hᵏ` has derivative `Aᵏ` at `x̄`
  have hdk : HasFDerivAt h^[k] (matCLM A ^ k) xbar := hd.iterate hfix k
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1
    (hdk.isLittleO.def (show (0 : ℝ) < 1 / 4 by norm_num))
  have hfixk : ∀ j, h^[j] xbar = xbar := fun j => Function.iterate_fixed hfix j
  -- the `k`-step map halves distances to `x̄` on the `δ`-ball
  have hhalf : ∀ y, dist y xbar < δ → dist (h^[k] y) xbar ≤ 1 / 2 * dist y xbar := by
    intro y hy
    have h1 := hδs hy
    rw [hfixk k] at h1
    rw [dist_eq_norm, dist_eq_norm]
    have h2 : ‖(matCLM A ^ k) (y - xbar)‖ ≤ 1 / 4 * ‖y - xbar‖ :=
      ((matCLM A ^ k).le_opNorm _).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))
    calc ‖h^[k] y - xbar‖ = ‖(h^[k] y - xbar - (matCLM A ^ k) (y - xbar)) +
          (matCLM A ^ k) (y - xbar)‖ := by congr 1; abel
      _ ≤ 1 / 4 * ‖y - xbar‖ + 1 / 4 * ‖y - xbar‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = 1 / 2 * ‖y - xbar‖ := by ring
  -- each `hʲ`, `j < k`, is continuous at `x̄`
  have hcont : ∀ j, ContinuousAt h^[j] xbar := fun j =>
    (hd.iterate hfix j).continuousAt
  refine ⟨Metric.ball xbar δ, Metric.ball_mem_nhds _ hδ, fun x₀ hx₀ => ?_⟩
  -- along multiples of `k`: `dist ≤ (1/2)ʲ dist(x₀, x̄)`
  have hgeom : ∀ j, dist (h^[k * j] x₀) xbar ≤ (1 / 2) ^ j * dist x₀ xbar := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hin : dist (h^[k * j] x₀) xbar < δ := ih.trans_lt (by
        have : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have := Metric.mem_ball.1 hx₀
        nlinarith [dist_nonneg (x := x₀) (y := xbar)])
      rw [show k * (j + 1) = k + k * j by ring, Function.iterate_add_apply]
      calc dist (h^[k] (h^[k * j] x₀)) xbar ≤ 1 / 2 * dist (h^[k * j] x₀) xbar := hhalf _ hin
        _ ≤ 1 / 2 * ((1 / 2) ^ j * dist x₀ xbar) := by gcongr
        _ = (1 / 2) ^ (j + 1) * dist x₀ xbar := by ring
  have hmul : Tendsto (fun j => h^[k * j] x₀) atTop (𝓝 xbar) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) hgeom ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const (dist x₀ xbar)
  -- every `t` is `k(t/k) + t % k`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : ∀ r, ∃ η > 0, ∀ y, dist y xbar < η → dist (h^[r] y) xbar < ε := fun r => by
    obtain ⟨η, hη, hηs⟩ := Metric.continuousAt_iff.1 (hcont r) ε hε
    exact ⟨η, hη, fun y hy => by rw [← hfixk r]; exact hηs hy⟩
  choose η hηpos hηs using hη
  set η₀ := (Finset.range k).inf' ⟨0, by simp [k]⟩ η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff _).2 fun r _ => hηpos r
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hmul η₀ hη₀
  refine ⟨k * J, fun t ht => ?_⟩
  have hdecomp : t = t % k + k * (t / k) := (Nat.mod_add_div t k).symm
  rw [hdecomp, Function.iterate_add_apply]
  have hJt : J ≤ t / k := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact ht)
  have hr : t % k ∈ Finset.range k := Finset.mem_range.2 (Nat.mod_lt _ (by omega))
  exact hηs (t % k) _ ((hJ _ hJt).trans_le (Finset.inf'_le _ hr))

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linearized Euler equations

SLP §6.4, pp. 149–151. For a quadratic return, with `l × l` matrices `F_xx`, `F_xy`, `F_yy` of
second derivatives (`F_xx`, `F_yy` symmetric), the Euler equations in deviations are
`z_{t+2} = Jz_{t+1} + Kz_t`, with `J = −β⁻¹F_xy⁻¹(F_yy + βF_xx)` and `K = −β⁻¹F_xy⁻¹F'_xy`.
Stacked as `Z_{t+1} = AZ_t`, the matrix is `A = [[J, K], [I, 0]]` (`eulerA`).

* **Exercise 6.5** (`ex_6_5`): if `F_xy` and `F'_xy + F_yy + βF_xx + βF_xy` are nonsingular, so
  are `A` and `I − A`.
* **Lemma 6.7** (`lemma_6_7`, Levhari–Liviatan): if `λ` is a characteristic root of `A`, so is
  `(βλ)⁻¹`. The algebra is done over any field (`root_inv_of_root`) from the relations
  `F_xyJ = −β⁻¹(F_yy + βF_xx)` and `F_xyK = −β⁻¹F'_xy`. `λ` is a root iff (5)
  `det[β⁻¹F'_xy + λβ⁻¹(F_yy + βF_xx) + λ²F_xy] = 0` (`det_char_eq`), and the matrix at
  `(βλ)⁻¹`, times `λ²β`, is the transpose of the matrix at `λ`.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Matrix

variable {l : ℕ}

/-- `J = −β⁻¹F_xy⁻¹(F_yy + βF_xx)`. -/
noncomputable def eulerJ (Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) :
    Matrix (Fin l) (Fin l) ℝ := -(β⁻¹ • (Fxy⁻¹ * (Fyy + β • Fxx)))

/-- `K = −β⁻¹F_xy⁻¹F'_xy`. -/
noncomputable def eulerK (Fxy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  -(β⁻¹ • (Fxy⁻¹ * Fxyᵀ))

/-- The stacked matrix `A = [[J, K], [I, 0]]`. -/
noncomputable def eulerA (Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) :
    Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) ℝ :=
  fromBlocks (eulerJ Fxx Fxy Fyy β) (eulerK Fxy β) 1 0

/-! ### Determinants of block matrices -/

variable {𝕜 : Type*} [Field 𝕜]

/-- `det [[J, K], [I, 0]] = ±det K`: the block swap `S = [[0, I], [I, 0]]` squares to `I` and
`[[J, K], [I, 0]]·S = [[K, J], [0, I]]`. -/
theorem det_fromBlocks_one_zero (J K : Matrix (Fin l) (Fin l) 𝕜) :
    (fromBlocks J K 1 0).det ≠ 0 ↔ K.det ≠ 0 := by
  set S : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) 𝕜 := fromBlocks 0 1 1 0
  have hS : S * S = 1 := by
    simp only [S, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero]
    exact fromBlocks_one
  have hSdet : S.det * S.det = 1 := by rw [← det_mul, hS, det_one]
  have hAS : fromBlocks J K 1 0 * S =
      fromBlocks K J (0 : Matrix (Fin l) (Fin l) 𝕜) 1 := by
    simp only [S, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero]
  have hdet : (fromBlocks J K 1 0).det * S.det = K.det := by
    rw [← det_mul, hAS, det_fromBlocks_zero₂₁, det_one, mul_one]
  have hS0 : S.det ≠ 0 := fun h => by rw [h, zero_mul] at hSdet; exact zero_ne_one hSdet
  constructor
  · intro h; rw [← hdet]; exact mul_ne_zero h hS0
  · intro h h0; rw [h0, zero_mul] at hdet; exact h hdet.symm

/-- Block triangular factorization: for `λ ≠ 0`,
`det [[λ − J, −K], [−I, λ]] = det(λ²I − λJ − K)`. -/
theorem det_char_block {J K : Matrix (Fin l) (Fin l) 𝕜} {μ : 𝕜} (hμ : μ ≠ 0) :
    (scalar (Fin l ⊕ Fin l) μ - fromBlocks J K 1 0).det = (μ ^ 2 • 1 - μ • J - K).det := by
  have hsc : scalar (Fin l ⊕ Fin l) μ - fromBlocks J K 1 0 =
      fromBlocks (μ • 1 - J) (-K) (-1) (μ • 1) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]
  -- `[[P, Q], [R, D]] = [[1, QD⁻¹], [0, 1]]·[[P − QD⁻¹R, 0], [R, D]]` with `D = μ`
  have hfac : fromBlocks (μ • 1 - J) (-K) (-1) (μ • (1 : Matrix (Fin l) (Fin l) 𝕜)) =
      fromBlocks 1 (μ⁻¹ • -K) 0 1 * fromBlocks (μ • 1 - J - μ⁻¹ • K) 0 (-1) (μ • 1) := by
    rw [fromBlocks_multiply]
    congr 1
    · simp only [Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, smul_neg, neg_neg]
      abel
    · simp only [Matrix.mul_zero, zero_add, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        mul_inv_cancel₀ hμ, one_smul]
    · simp
    · simp
  rw [hsc, hfac, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
  simp only [det_one, one_mul]
  rw [mul_comm, det_smul, det_one, mul_one, ← det_smul]
  congr 1
  rw [smul_sub, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hμ, one_smul, ← pow_two]

variable {P S J K : Matrix (Fin l) (Fin l) 𝕜} {β : 𝕜}

/-- (5): with `PJ = −β⁻¹S` and `PK = −β⁻¹Pᵀ`,
`P(λ²I − λJ − K) = λ²P + λβ⁻¹S + β⁻¹Pᵀ`. -/
theorem det_char_eq (hJ : P * J = -(β⁻¹ • S)) (hK : P * K = -(β⁻¹ • Pᵀ)) (μ : 𝕜) :
    P * (μ ^ 2 • 1 - μ • J - K) = μ ^ 2 • P + μ • (β⁻¹ • S) + β⁻¹ • Pᵀ := by
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, hJ, hK]
  simp only [smul_neg]
  abel

/-- **Lemma 6.7** over a field. Let `P` be nonsingular, `S` symmetric, `β ≠ 0`, `PJ = −β⁻¹S` and
`PK = −β⁻¹Pᵀ`. If `λ` is a characteristic root of `[[J, K], [I, 0]]`, so is `(βλ)⁻¹`. -/
theorem root_inv_of_root (hP : P.det ≠ 0) (hS : Sᵀ = S) (hβ : β ≠ 0)
    (hJ : P * J = -(β⁻¹ • S)) (hK : P * K = -(β⁻¹ • Pᵀ)) {μ : 𝕜}
    (hroot : (scalar (Fin l ⊕ Fin l) μ - fromBlocks J K 1 0).det = 0) :
    (scalar (Fin l ⊕ Fin l) (β * μ)⁻¹ - fromBlocks J K 1 0).det = 0 := by
  -- `K` is nonsingular, so `0` is not a root
  have hKdet : K.det ≠ 0 := by
    have := congrArg det hK
    rw [det_mul, det_neg, det_smul, det_transpose] at this
    intro h0
    rw [h0, mul_zero] at this
    have h2 : (-1 : 𝕜) ^ Fintype.card (Fin l) * (β⁻¹ ^ Fintype.card (Fin l) * P.det) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hβ)) hP)
    exact h2 this.symm
  have hμ : μ ≠ 0 := by
    rintro rfl
    have hA := (det_fromBlocks_one_zero J K).2 hKdet
    have : (scalar (Fin l ⊕ Fin l) (0 : 𝕜) - fromBlocks J K 1 0).det =
        (-1) ^ Fintype.card (Fin l ⊕ Fin l) * (fromBlocks J K 1 0).det := by
      rw [map_zero, zero_sub, ← det_smul, neg_one_smul]
    rw [this] at hroot
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hA hroot
  set ν := (β * μ)⁻¹
  have hν : ν ≠ 0 := inv_ne_zero (mul_ne_zero hβ hμ)
  -- the matrix of (5)
  set M : 𝕜 → Matrix (Fin l) (Fin l) 𝕜 := fun t => t ^ 2 • P + t • (β⁻¹ • S) + β⁻¹ • Pᵀ
  have hdet : ∀ t : 𝕜, t ≠ 0 →
      (scalar (Fin l ⊕ Fin l) t - fromBlocks J K 1 0).det * P.det = (M t).det := fun t ht => by
    rw [det_char_block ht, mul_comm, ← det_mul, det_char_eq hJ hK]
  have hMμ : (M μ).det = 0 := by rw [← hdet μ hμ, hroot, zero_mul]
  -- `λ²β·M(ν) = M(λ)ᵀ`
  have htr : (μ ^ 2 * β) • M ν = (M μ)ᵀ := by
    simp only [M, ν, transpose_add, transpose_smul, transpose_transpose, hS, smul_add,
      smul_smul]
    have e1 : μ ^ 2 * β * (β * μ)⁻¹ ^ 2 = β⁻¹ := by field_simp
    have e2 : μ ^ 2 * β * ((β * μ)⁻¹ * β⁻¹) = μ * β⁻¹ := by field_simp
    have e3 : μ ^ 2 * β * β⁻¹ = μ ^ 2 := by field_simp
    rw [e1, e2, e3]
    abel
  have hMν : (M ν).det = 0 := by
    have := congrArg det htr
    rw [det_smul, det_transpose, hMμ] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hμ) hβ))
  have := hdet ν hν
  rw [hMν] at this
  exact (mul_eq_zero.1 this).resolve_right hP

/-! ### The real Euler matrix -/

theorem fxy_mul_eulerJ {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hxy : Fxy.det ≠ 0) :
    Fxy * eulerJ Fxx Fxy Fyy β = -(β⁻¹ • (Fyy + β • Fxx)) := by
  rw [eulerJ, Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hxy), Matrix.one_mul]

theorem fxy_mul_eulerK {Fxy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hxy : Fxy.det ≠ 0) :
    Fxy * eulerK Fxy β = -(β⁻¹ • Fxyᵀ) := by
  rw [eulerK, Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hxy), Matrix.one_mul]

/-- **Exercise 6.5.** If `F_xy` and `F'_xy + F_yy + βF_xx + βF_xy` are nonsingular (and `β ≠ 0`),
then `A` and `I − A` are nonsingular. -/
theorem ex_6_5 {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hβ : β ≠ 0)
    (hxy : Fxy.det ≠ 0) (hS : (Fxyᵀ + Fyy + β • Fxx + β • Fxy).det ≠ 0) :
    (eulerA Fxx Fxy Fyy β).det ≠ 0 ∧ (1 - eulerA Fxx Fxy Fyy β).det ≠ 0 := by
  have hcard : ∀ c : ℝ, c ≠ 0 → c ^ Fintype.card (Fin l) ≠ 0 := fun c hc => pow_ne_zero _ hc
  refine ⟨(det_fromBlocks_one_zero _ _).2 ?_, ?_⟩
  · -- `F_xy K = −β⁻¹F'_xy` is nonsingular
    intro h0
    have := congrArg det (fxy_mul_eulerK (β := β) hxy)
    rw [det_mul, h0, mul_zero, det_neg, det_smul, det_transpose] at this
    exact mul_ne_zero (hcard _ (by norm_num)) (mul_ne_zero (hcard _ (inv_ne_zero hβ)) hxy)
      this.symm
  · -- `I − A = [[I − J, −K], [−I, I]]`, with determinant `det(I − J − K)`
    have h1 : 1 - eulerA Fxx Fxy Fyy β =
        fromBlocks (1 - eulerJ Fxx Fxy Fyy β) (-eulerK Fxy β) (-1) 1 := by
      ext (i | i) (j | j) <;> simp [eulerA, Matrix.one_apply]
    rw [h1, det_fromBlocks_one₂₂]
    have h2 : Fxy * (1 - eulerJ Fxx Fxy Fyy β - -eulerK Fxy β * -1) =
        β⁻¹ • (Fxyᵀ + Fyy + β • Fxx + β • Fxy) := by
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, Matrix.mul_sub, Matrix.mul_sub,
        Matrix.mul_one, fxy_mul_eulerJ hxy, fxy_mul_eulerK hxy]
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hβ, one_smul, sub_neg_eq_add]
      abel
    intro h0
    have := congrArg det h2
    rw [det_mul, h0, mul_zero, det_smul] at this
    exact mul_ne_zero (hcard _ (inv_ne_zero hβ)) hS this.symm

/-- **Lemma 6.7.** If `F_xy` is nonsingular, `F_xx` and `F_yy` are symmetric and `β ≠ 0`, then
whenever `λ` is a characteristic root of `A`, so is `(βλ)⁻¹`. -/
theorem lemma_6_7 {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hβ : β ≠ 0)
    (hxy : Fxy.det ≠ 0) (hxx : Fxxᵀ = Fxx) (hyy : Fyyᵀ = Fyy) {μ : ℂ}
    (hμ : ((eulerA Fxx Fxy Fyy β).charpoly.map Complex.ofRealHom).IsRoot μ) :
    ((eulerA Fxx Fxy Fyy β).charpoly.map Complex.ofRealHom).IsRoot ((β * μ)⁻¹ : ℂ) := by
  set f := Complex.ofRealHom
  have hroot : ∀ ν : ℂ, ((eulerA Fxx Fxy Fyy β).charpoly.map f).IsRoot ν ↔
      (scalar (Fin l ⊕ Fin l) ν - fromBlocks ((eulerJ Fxx Fxy Fyy β).map f)
        ((eulerK Fxy β).map f) 1 0).det = 0 := fun ν => by
    rw [Polynomial.IsRoot.def, ← Matrix.charpoly_map, Matrix.eval_charpoly, eulerA,
      fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)]
  rw [hroot] at hμ ⊢
  have hP : (Fxy.map f).det ≠ 0 := by
    have : (Fxy.map f).det = f Fxy.det := by rw [RingHom.map_det]; rfl
    rw [this]; exact (map_ne_zero f).2 hxy
  have hS : ((Fyy + β • Fxx).map f)ᵀ = (Fyy + β • Fxx).map f := by
    rw [← Matrix.transpose_map, transpose_add, transpose_smul, hxx, hyy]
  have hJ : Fxy.map f * (eulerJ Fxx Fxy Fyy β).map f =
      -((f β)⁻¹ • (Fyy + β • Fxx).map f) := by
    rw [← Matrix.map_mul, fxy_mul_eulerJ hxy]
    ext i j
    simp [f]
    ring
  have hK : Fxy.map f * (eulerK Fxy β).map f = -((f β)⁻¹ • (Fxy.map f)ᵀ) := by
    rw [← Matrix.map_mul, fxy_mul_eulerK hxy]
    ext i j
    simp [f]
  have := root_inv_of_root hP hS ((map_ne_zero f).2 hβ) hJ hK hμ
  simpa [f] using this

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# One state variable: the roots of the linearized Euler equation

SLP §6.4, pp. 154–156. With one state variable the stacked matrix is
`A = [[J, K], [1, 0]]` with `J = −(F_yy + βF_xx)/(βF_xy)` and `K = −1/β`. Its characteristic
polynomial is `λ² − Jλ + 1/β`.

* **The growth example** (pp. 154–155, `growth_roots`). For `U[f(k) − y]`,
  `J = 1 + β⁻¹ + c` with `c = βf''U'/U'' > 0`. The polynomial `λ² − (1 + β⁻¹ + c)λ + β⁻¹` has one
  root in `(0, 1)` and one above `1/β` (Figure 6.3).
* **Exercise 6.6** (`ex_6_6`). With the second-order conditions of a concave `F` at the steady
  state (`F_xx ≤ 0`, `F_yy ≤ 0`, `F_xxF_yy ≥ F_xy²`, `F_xy ≠ 0`):
  (a) both roots of `A` are real;
  (b) both are positive if `F_xy > 0`;
  (c) both are negative if `F_xy < 0`.
  The product of the roots is `1/β > 0`, and their sum `J` has the sign of `F_xy`.

Roots are stated as the complex roots of the polynomial (`quadRoot`), so "real" is a conclusion.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Complex

/-- `μ` is a root of `λ² − sλ + p`. -/
def quadRoot (s p : ℝ) (μ : ℂ) : Prop := μ ^ 2 - (s : ℂ) * μ + (p : ℂ) = 0

/-- If `s² ≥ 4p`, the roots of `λ² − sλ + p` are `(s ± √(s² − 4p))/2`, and they are real. -/
theorem quadRoot_real {s p : ℝ} (hd : 4 * p ≤ s ^ 2) {μ : ℂ} (hμ : quadRoot s p μ) :
    ∃ r : ℝ, μ = r ∧ (r = (s + Real.sqrt (s ^ 2 - 4 * p)) / 2 ∨
      r = (s - Real.sqrt (s ^ 2 - 4 * p)) / 2) := by
  set q := Real.sqrt (s ^ 2 - 4 * p)
  have hq : q ^ 2 = s ^ 2 - 4 * p := Real.sq_sqrt (by linarith)
  have hfac : (μ - ((s + q) / 2 : ℝ)) * (μ - ((s - q) / 2 : ℝ)) = 0 := by
    have e : (μ - ((s + q) / 2 : ℝ)) * (μ - ((s - q) / 2 : ℝ)) =
        μ ^ 2 - (s : ℂ) * μ + ((s ^ 2 - q ^ 2) / 4 : ℝ) := by push_cast; ring
    have e2 : ((s ^ 2 - q ^ 2) / 4 : ℝ) = p := by rw [hq]; ring
    rw [e, e2]
    exact hμ
  rcases mul_eq_zero.1 hfac with h | h
  · exact ⟨_, sub_eq_zero.1 h, Or.inl rfl⟩
  · exact ⟨_, sub_eq_zero.1 h, Or.inr rfl⟩

/-- **The growth example** (pp. 154–155). For `c > 0` and `0 < β < 1`, the roots of
`λ² − (1 + β⁻¹ + c)λ + β⁻¹` are real, one in `(0, 1)` and one greater than `1/β`. -/
theorem growth_roots {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ l₁ < 1 ∧ 1 / β < l₂ ∧ quadRoot (1 + β⁻¹ + c) β⁻¹ l₁ ∧
      quadRoot (1 + β⁻¹ + c) β⁻¹ l₂ ∧ ∀ μ, quadRoot (1 + β⁻¹ + c) β⁻¹ μ → μ = l₁ ∨ μ = l₂ := by
  set s := 1 + β⁻¹ + c
  have hbi : 1 < β⁻¹ := (one_lt_inv₀ hβ0).2 hβ1
  -- `p(1) = −c < 0` and `p(1/β) = −c/β < 0` while `p(0) = 1/β > 0`
  have hd : 4 * β⁻¹ ≤ s ^ 2 := by
    simp only [s]; nlinarith [sq_nonneg (1 - β⁻¹)]
  set q := Real.sqrt (s ^ 2 - 4 * β⁻¹)
  have hq : q ^ 2 = s ^ 2 - 4 * β⁻¹ := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * (β : ℂ)⁻¹ := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s β⁻¹ r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  -- locate the roots through the sign of `p`
  have hp1 : (1 : ℝ) ^ 2 - s * 1 + β⁻¹ < 0 := by simp only [s]; linarith
  have hpβ : β⁻¹ ^ 2 - s * β⁻¹ + β⁻¹ < 0 := by simp only [s]; nlinarith
  -- `p(r) = (r − r₁)(r − r₂)` with `r₁ ≤ r₂`
  have hfact : ∀ r : ℝ, r ^ 2 - s * r + β⁻¹ = (r - (s - q) / 2) * (r - (s + q) / 2) := fun r => by
    have : s ^ 2 - q ^ 2 = 4 * β⁻¹ := by linarith
    nlinarith
  have h1 := hfact 1
  have h2 := hfact β⁻¹
  have hlt1 : (s - q) / 2 < 1 ∧ 1 < (s + q) / 2 := by
    rw [h1] at hp1
    constructor <;> nlinarith
  have hlt2 : β⁻¹ < (s + q) / 2 := by
    rw [h2] at hpβ
    nlinarith
  have hpos : 0 < (s - q) / 2 := by
    have : q < s := by
      have hs : 0 < s := by simp only [s]; linarith
      nlinarith
    linarith
  refine ⟨(s - q) / 2, (s + q) / 2, hpos, hlt1.1, by rw [one_div]; exact hlt2,
    hroot _ (Or.inr rfl), hroot _ (Or.inl rfl), fun μ hμ => ?_⟩
  obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
  rcases hr with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Exercise 6.6.** With `F_xx ≤ 0`, `F_yy ≤ 0`, `F_xxF_yy ≥ F_xy²`, `F_xy ≠ 0` and `β > 0`, the
roots of `λ² − Jλ + 1/β`, `J = −(F_yy + βF_xx)/(βF_xy)`, are real, with product `1/β`, and both
have the sign of `F_xy`. -/
theorem ex_6_6 {Fxx Fxy Fyy β : ℝ} (hβ : 0 < β) (hxx : Fxx ≤ 0) (hyy : Fyy ≤ 0)
    (hdet : Fxy ^ 2 ≤ Fxx * Fyy) (hxy : Fxy ≠ 0) :
    ∃ l₁ l₂ : ℝ, l₁ * l₂ = 1 / β ∧
      quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) l₁ ∧
      quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) l₂ ∧
      (∀ μ, quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) μ → μ = l₁ ∨ μ = l₂) ∧
      (0 < Fxy → 0 < l₁ ∧ 0 < l₂) ∧ (Fxy < 0 → l₁ < 0 ∧ l₂ < 0) := by
  set s := -(Fyy + β * Fxx) / (β * Fxy)
  have hsq : 0 < Fxy ^ 2 := by positivity
  have hxx' : Fxx < 0 := lt_of_le_of_ne hxx fun h => by rw [h, zero_mul] at hdet; linarith
  have hyy' : Fyy < 0 := lt_of_le_of_ne hyy fun h => by rw [h, mul_zero] at hdet; linarith
  have hS : Fyy + β * Fxx < 0 := by nlinarith
  -- the discriminant: `(F_yy + βF_xx)² ≥ 4βF_xxF_yy ≥ 4βF_xy²`
  have hd : 4 * (1 / β) ≤ s ^ 2 := by
    have h1 : 4 * β * Fxy ^ 2 ≤ (Fyy + β * Fxx) ^ 2 := by
      nlinarith [sq_nonneg (Fyy - β * Fxx)]
    have hb : 0 < (β * Fxy) ^ 2 := by positivity
    simp only [s, div_pow, neg_sq]
    rw [le_div_iff₀ hb]
    field_simp
    nlinarith
  set q := Real.sqrt (s ^ 2 - 4 * (1 / β))
  have hq : q ^ 2 = s ^ 2 - 4 * (1 / β) := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * (1 / (β : ℂ)) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s (1 / β) r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hprod : (s + q) / 2 * ((s - q) / 2) = 1 / β := by nlinarith
  have hqs : q < |s| := by
    have h1 : 0 < 1 / β := by positivity
    have h2 : q ^ 2 < |s| ^ 2 := by rw [sq_abs, hq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg s) h2
  refine ⟨(s + q) / 2, (s - q) / 2, hprod, hroot _ (Or.inl rfl), hroot _ (Or.inr rfl),
    fun μ hμ => ?_, fun hpos => ?_, fun hneg => ?_⟩
  · obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have hs : 0 < s := by
      simp only [s]; exact div_pos (by linarith) (by positivity)
    rw [abs_of_pos hs] at hqs
    constructor <;> linarith
  · have hs : s < 0 := by
      simp only [s]; exact div_neg_of_pos_of_neg (by linarith) (by nlinarith)
    rw [abs_of_neg hs] at hqs
    constructor <;> linarith

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cyclical example: the return function and its steady state

SLP §6.1 (Exercise 6.2) and §6.5 (Exercise 6.7), pp. 138 and 156–158. With `U(c) = c^α` and
`f(z) = z^θ`, the return of (6) is `F(k, y) = [(1 − y)(k/(1 − y))^θ]^α = k^a(1 − y)^b` with
`a = αθ`, `b = α(1 − θ)`, so `a, b > 0` and `a + b = α < 1` (`cdF`). Its partial derivatives are
`F_x = ak^{a−1}(1 − y)^b` and `F_y = −bk^a(1 − y)^{b−1}` (`cdFx`, `cdFy`).

* **Exercise 6.7b** (`ex_6_7b`): the Euler equation
  `F_y(k_t, k_{t+1}) + βF_x(k_{t+1}, k_{t+2}) = 0` has exactly one interior stationary point,
  `k* = βa/(b + βa) = βθ/(1 − θ + βθ)`.
* **Exercise 6.7c**:
  * At `k*`, `(F_yy + βF_xx)/(βF_xy)` equals the book's
    `B = [1 − α(1 − θ)]/[α(1 − θ)] + (1 − αθ)/(αθβ)` (`linearization_B`). So the linear
    approximation is `(k_{t+2} − k*) + B(k_{t+1} − k*) + β⁻¹(k_t − k*) = 0`.
  * The roots of `λ² + Bλ + β⁻¹` are real, with `λ₁λ₂ = β⁻¹` (so `λ₂ = (βλ₁)⁻¹`) and
    `λ₁ + λ₂ = −B`, and both are negative (`ex_6_7c`).
  * `k*` is locally stable, in the sense that one root lies in `(−1, 0)`, iff `B > 1 + β⁻¹`
    (`ex_6_7c_stable_iff`).
* **Exercise 6.7d** (`ex_6_7d`): for `β = 0.1`, `α = 0.8`, `θ = 0.75`, `k* = 3/13 ≈ 0.23` and
  `B = 32/3 < 11 = 1 + β⁻¹`: both roots are below `−1`, so `k*` is unstable.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Real

/-- `F(k, y) = k^a(1 − y)^b`. -/
noncomputable def cdF (a b k y : ℝ) : ℝ := k ^ a * (1 - y) ^ b

/-- `F_x(k, y) = ak^{a−1}(1 − y)^b`. -/
noncomputable def cdFx (a b k y : ℝ) : ℝ := a * k ^ (a - 1) * (1 - y) ^ b

/-- `F_y(k, y) = −bk^a(1 − y)^{b−1}`. -/
noncomputable def cdFy (a b k y : ℝ) : ℝ := -(b * k ^ a * (1 - y) ^ (b - 1))

/-- `F_xx = a(a − 1)k^{a−2}(1 − y)^b`. -/
noncomputable def cdFxx (a b k y : ℝ) : ℝ := a * (a - 1) * k ^ (a - 2) * (1 - y) ^ b

/-- `F_yy = b(b − 1)k^a(1 − y)^{b−2}`. -/
noncomputable def cdFyy (a b k y : ℝ) : ℝ := b * (b - 1) * k ^ a * (1 - y) ^ (b - 2)

/-- `F_xy = −abk^{a−1}(1 − y)^{b−1}`. -/
noncomputable def cdFxy (a b k y : ℝ) : ℝ := -(a * b * k ^ (a - 1) * (1 - y) ^ (b - 1))

variable {a b : ℝ}

/-- `F_x` is the partial derivative in `k` (for `k > 0`). -/
theorem hasDerivAt_cdF_k {k : ℝ} (hk : 0 < k) (y : ℝ) :
    HasDerivAt (fun k => cdF a b k y) (cdFx a b k y) k := by
  have := (hasDerivAt_rpow_const (p := a) (Or.inl hk.ne')).mul_const ((1 - y) ^ b)
  simpa [cdF, cdFx, mul_comm, mul_assoc, mul_left_comm] using this

/-- `F_y` is the partial derivative in `y` (for `y < 1`). -/
theorem hasDerivAt_cdF_y (k : ℝ) {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun y => cdF a b k y) (cdFy a b k y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := (h1.rpow_const (p := b) (Or.inl (by linarith))).const_mul (k ^ a)
  unfold cdF cdFy
  convert this using 1
  ring

/-- `F_xx` and `F_xy` are the partial derivatives of `F_x`. -/
theorem hasDerivAt_cdFx_k {k : ℝ} (hk : 0 < k) (y : ℝ) :
    HasDerivAt (fun k => cdFx a b k y) (cdFxx a b k y) k := by
  have := ((hasDerivAt_rpow_const (p := a - 1) (Or.inl hk.ne')).const_mul a).mul_const
    ((1 - y) ^ b)
  unfold cdFx cdFxx
  convert this using 1
  rw [show a - 1 - 1 = a - 2 by ring]
  ring

theorem hasDerivAt_cdFx_y (k : ℝ) {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun y => cdFx a b k y) (cdFxy a b k y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := (h1.rpow_const (p := b) (Or.inl (by linarith))).const_mul (a * k ^ (a - 1))
  unfold cdFx cdFxy
  convert this using 1
  ring

theorem hasDerivAt_cdFy_y (k : ℝ) {y : ℝ} (hy : y < 1) :
    HasDerivAt (fun y => cdFy a b k y) (cdFyy a b k y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := (h1.rpow_const (p := b - 1) (Or.inl (by linarith))).const_mul (-(b * k ^ a))
  have e : (fun y => cdFy a b k y) = fun y => -(b * k ^ a) * (1 - y) ^ (b - 1) := by
    funext z; simp only [cdFy]; ring
  rw [e]
  convert this using 1
  rw [show b - 1 - 1 = b - 2 by ring]
  simp only [cdFyy]
  ring

/-- The Euler equation at a constant path factors as
`F_y(k, k) + βF_x(k, k) = k^{a−1}(1 − k)^{b−1}[βa(1 − k) − bk]`. -/
theorem euler_steady {β k : ℝ} (hk : 0 < k) (hk1 : k < 1) :
    cdFy a b k k + β * cdFx a b k k =
      k ^ (a - 1) * (1 - k) ^ (b - 1) * (β * a * (1 - k) - b * k) := by
  have h1 : k ^ a = k ^ (a - 1) * k := by
    rw [← rpow_add_one hk.ne', sub_add_cancel]
  have h2 : (1 - k) ^ b = (1 - k) ^ (b - 1) * (1 - k) := by
    rw [← rpow_add_one (by linarith), sub_add_cancel]
  simp only [cdFy, cdFx, h1, h2]
  ring

/-- **Exercise 6.7b.** The unique interior stationary point of the Euler equation is
`k* = βa/(b + βa)`. -/
theorem ex_6_7b {β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β) :
    let kstar := β * a / (b + β * a)
    0 < kstar ∧ kstar < 1 ∧ cdFy a b kstar kstar + β * cdFx a b kstar kstar = 0 ∧
      ∀ k, 0 < k → k < 1 → cdFy a b k k + β * cdFx a b k k = 0 → k = kstar := by
  intro kstar
  have hpos : 0 < b + β * a := by positivity
  have hk0 : 0 < kstar := by positivity
  have hk1 : kstar < 1 := by
    simp only [kstar]; rw [div_lt_one hpos]; linarith
  have hlin : β * a * (1 - kstar) - b * kstar = 0 := by
    simp only [kstar]; field_simp; ring
  refine ⟨hk0, hk1, by rw [euler_steady hk0 hk1, hlin, mul_zero], fun k hk hk1' h => ?_⟩
  rw [euler_steady hk hk1'] at h
  have hne : k ^ (a - 1) * (1 - k) ^ (b - 1) ≠ 0 :=
    mul_ne_zero (rpow_pos_of_pos hk _).ne' (rpow_pos_of_pos (by linarith) _).ne'
  have := (mul_eq_zero.1 h).resolve_left hne
  simp only [kstar]
  field_simp
  linarith

/-- In the book's parameters, `k* = βθ/(1 − θ + βθ)`. -/
theorem kstar_eq {α θ β : ℝ} (hα : 0 < α) :
    β * (α * θ) / (α * (1 - θ) + β * (α * θ)) = β * θ / (1 - θ + β * θ) := by
  have : α * (1 - θ) + β * (α * θ) = α * (1 - θ + β * θ) := by ring
  rw [this, show β * (α * θ) = α * (β * θ) by ring, mul_div_mul_left _ _ hα.ne']

/-- **Exercise 6.7c (the linearization).** At `k* = βa/(b + βa)`,
`(F_yy + βF_xx)/(βF_xy) = (1 − b)/b + (1 − a)/(βa)`, which is the book's
`B = [1 − α(1 − θ)]/[α(1 − θ)] + (1 − αθ)/(αθβ)`. -/
theorem linearization_B {β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β) :
    let kstar := β * a / (b + β * a)
    (cdFyy a b kstar kstar + β * cdFxx a b kstar kstar) / (β * cdFxy a b kstar kstar) =
      (1 - b) / b + (1 - a) / (β * a) := by
  intro kstar
  obtain ⟨hk0, hk1, -, -⟩ := ex_6_7b ha hb hβ
  have hk0' : 0 < kstar := hk0
  have hk1' : 0 < 1 - kstar := by have : kstar < 1 := hk1; linarith
  set p := kstar ^ (a - 1) * (1 - kstar) ^ (b - 1)
  have hp : 0 < p := mul_pos (rpow_pos_of_pos hk0' _) (rpow_pos_of_pos hk1' _)
  -- express every second derivative through `p`
  have e1 : kstar ^ a = kstar ^ (a - 1) * kstar := by
    rw [← rpow_add_one hk0'.ne', sub_add_cancel]
  have e2 : (1 - kstar) ^ b = (1 - kstar) ^ (b - 1) * (1 - kstar) := by
    rw [← rpow_add_one hk1'.ne', sub_add_cancel]
  have e3 : kstar ^ (a - 2) * kstar = kstar ^ (a - 1) := by
    rw [← rpow_add_one hk0'.ne']; congr 1; ring
  have e4 : (1 - kstar) ^ (b - 2) * (1 - kstar) = (1 - kstar) ^ (b - 1) := by
    rw [← rpow_add_one hk1'.ne']; congr 1; ring
  have hxx : cdFxx a b kstar kstar * kstar = a * (a - 1) * p * (1 - kstar) := by
    simp only [cdFxx, p, e2]; rw [← e3]; ring
  have hyy : cdFyy a b kstar kstar * (1 - kstar) = b * (b - 1) * p * kstar := by
    simp only [cdFyy, p, e1]; rw [← e4]; ring
  have hxy : cdFxy a b kstar kstar = -(a * b * p) := by simp only [cdFxy, p]; ring
  have hss : b * kstar = β * a * (1 - kstar) := by
    simp only [kstar]; field_simp; ring
  have hxx' : cdFxx a b kstar kstar = a * (a - 1) * p * (1 - kstar) / kstar := by
    rw [← hxx, mul_div_cancel_right₀ _ hk0'.ne']
  have hyy' : cdFyy a b kstar kstar = b * (b - 1) * p * kstar / (1 - kstar) := by
    rw [← hyy, mul_div_cancel_right₀ _ hk1'.ne']
  have r1 : kstar / (1 - kstar) = β * a / b := by
    rw [div_eq_div_iff hk1'.ne' hb.ne']; linarith
  have r2 : (1 - kstar) / kstar = b / (β * a) := by
    rw [div_eq_div_iff hk0'.ne' (by positivity)]; linarith
  rw [hxy, hxx', hyy']
  calc (b * (b - 1) * p * kstar / (1 - kstar) + β * (a * (a - 1) * p * (1 - kstar) / kstar)) /
        (β * -(a * b * p))
      = (b * (b - 1) * p * (kstar / (1 - kstar)) +
          β * (a * (a - 1) * p * ((1 - kstar) / kstar))) / (β * -(a * b * p)) := by ring
    _ = (1 - b) / b + (1 - a) / (β * a) := by
      rw [r1, r2]
      field_simp
      ring

/-- **Exercise 6.7c (the roots).** For `0 < a`, `0 < b`, `a + b < 1` and `β > 0`, with
`B = (1 − b)/b + (1 − a)/(βa)`, the roots of `λ² + Bλ + β⁻¹` are real and negative, with product
`β⁻¹` (so `λ₂ = (βλ₁)⁻¹`) and sum `−B`. -/
theorem ex_6_7c {β : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1) (hβ : 0 < β) :
    let B := (1 - b) / b + (1 - a) / (β * a)
    ∃ l₁ l₂ : ℝ, l₁ < 0 ∧ l₂ < 0 ∧ l₁ * l₂ = β⁻¹ ∧ l₁ + l₂ = -B ∧
      quadRoot (-B) β⁻¹ l₁ ∧ quadRoot (-B) β⁻¹ l₂ ∧
      ∀ μ, quadRoot (-B) β⁻¹ μ → μ = l₁ ∨ μ = l₂ := by
  intro B
  have h1b : 0 < 1 - b := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hBpos : 0 < B := by positivity
  -- `B² ≥ 4/β`: `B ≥ 2√((1 − a)(1 − b)/(abβ))` and `(1 − a)(1 − b) ≥ ab`
  have hd : 4 * β⁻¹ ≤ (-B) ^ 2 := by
    rw [neg_sq]
    have hx : 0 < (1 - b) / b := by positivity
    have hy : 0 < (1 - a) / (β * a) := by positivity
    have hxy : β⁻¹ ≤ (1 - b) / b * ((1 - a) / (β * a)) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      field_simp
      nlinarith
    nlinarith [sq_nonneg ((1 - b) / b - (1 - a) / (β * a))]
  set q := Real.sqrt ((-B) ^ 2 - 4 * β⁻¹)
  have hq : q ^ 2 = (-B) ^ 2 - 4 * β⁻¹ := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = ((-B : ℝ) : ℂ) ^ 2 - 4 * (β : ℂ)⁻¹ := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hq
    push_cast at this ⊢
    exact this
  have hroot : ∀ r : ℝ, r = (-B + q) / 2 ∨ r = (-B - q) / 2 → quadRoot (-B) β⁻¹ r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast at hqc ⊢ <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hqB : q < B := by
    have : q ^ 2 < B ^ 2 := by
      rw [hq, neg_sq]; have := inv_pos.2 hβ; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hBpos.le this
  refine ⟨(-B + q) / 2, (-B - q) / 2, by linarith, by linarith, by nlinarith, by ring,
    hroot _ (Or.inl rfl), hroot _ (Or.inr rfl), fun μ hμ => ?_⟩
  obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
  rcases hr with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Exercise 6.7c (stability).** The roots of `λ² + Bλ + β⁻¹` are negative with product
`β⁻¹ > 1`, so at most one lies in `(−1, 0)`; one does iff `B > 1 + β⁻¹`. -/
theorem ex_6_7c_stable_iff {B β l₁ l₂ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (h1 : l₁ < 0)
    (h2 : l₂ < 0) (hprod : l₁ * l₂ = β⁻¹) (hsum : l₁ + l₂ = -B) :
    (-1 < l₁ ∨ -1 < l₂) ↔ 1 + β⁻¹ < B := by
  have hbi : 1 < β⁻¹ := (one_lt_inv₀ hβ).2 hβ1
  -- `p(−1) = 1 − B + β⁻¹ = (−1 − l₁)(−1 − l₂)`
  have hp : 1 - B + β⁻¹ = (-1 - l₁) * (-1 - l₂) := by nlinarith
  constructor
  · rintro (h | h)
    · have : l₂ < -1 := by
        by_contra hc; push Not at hc
        have : l₁ * l₂ ≤ 1 := by nlinarith
        linarith
      nlinarith
    · have : l₁ < -1 := by
        by_contra hc; push Not at hc
        have : l₁ * l₂ ≤ 1 := by nlinarith
        linarith
      nlinarith
  · intro hB
    by_contra hc
    push Not at hc
    nlinarith

/-- **Exercise 6.7d.** For `β = 0.1`, `α = 0.8`, `θ = 0.75` (`a = 0.6`, `b = 0.2`):
`k* = 3/13 ≈ 0.23` and `B = 32/3 < 11 = 1 + β⁻¹`, so `k*` is not locally stable. -/
theorem ex_6_7d :
    (1 / 10 : ℝ) * (4 / 5 * (3 / 4)) / (4 / 5 * (1 - 3 / 4) + 1 / 10 * (4 / 5 * (3 / 4))) =
        3 / 13 ∧
      (1 - 1 / 5 : ℝ) / (1 / 5) + (1 - 3 / 5) / (1 / 10 * (3 / 5)) = 32 / 3 ∧
      ¬ (1 + (1 / 10 : ℝ)⁻¹ < 32 / 3) := by
  norm_num

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cyclical example: concavity and differentiability of the return

SLP §6.5, p. 156. `F(k, y) = k^a(1 − y)^b`, `a, b > 0`, `a + b ≤ 1`, on `[0, 1]²`.

* `geomMean_concave`: the weighted geometric mean `u₁^p u₂^q` (`p + q = 1`) is concave on `ℝ²₊`.
  Divide by its value at the convex combination and apply the weighted AM–GM inequality.
* `cd_concave`: `F` is concave on `[0, 1]²`, since `F = (geometric mean)^{a+b}` composed with an
  affine map.
* `cd_not_strict`: `F` is **not** strictly concave in the sense of Assumption 4.7, because
  `F(·, 1) ≡ 0`: `F(1/4, 1) = F(3/4, 1) = F(1/2, 1) = 0`. Exercise 6.7a's claim that
  Assumption 4.7 holds is therefore false as stated.
* `hasFDerivAt_cd`: at interior points, `DF(k, y)(u, w) = F_x u + F_y w`.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Set Real

/-- The weighted geometric mean `u₁^p u₂^q`, `p, q > 0`, `p + q = 1`, is concave on `ℝ²₊`. -/
theorem geomMean_concave {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1)
    {u₁ u₂ v₁ v₂ θ : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (u₁ ^ p * u₂ ^ q) + (1 - θ) * (v₁ ^ p * v₂ ^ q) ≤
      (θ * u₁ + (1 - θ) * v₁) ^ p * (θ * u₂ + (1 - θ) * v₂) ^ q := by
  set m₁ := θ * u₁ + (1 - θ) * v₁
  set m₂ := θ * u₂ + (1 - θ) * v₂
  have hm₁ : 0 ≤ m₁ := by positivity
  have hm₂ : 0 ≤ m₂ := by positivity
  have hθ1 : 0 ≤ 1 - θ := by linarith
  -- if a coordinate of the combination vanishes, both sides are zero
  have zero_case : ∀ {s₁ s₂ : ℝ} (r : ℝ), 0 < r → 0 ≤ s₁ → 0 ≤ s₂ →
      θ * s₁ + (1 - θ) * s₂ = 0 → θ * s₁ ^ r = 0 ∧ (1 - θ) * s₂ ^ r = 0 :=
    fun {s₁} {s₂} r hr h₁ h₂ h => by
      have e1 : θ * s₁ = 0 := by nlinarith [mul_nonneg h0 h₁, mul_nonneg hθ1 h₂]
      have e2 : (1 - θ) * s₂ = 0 := by nlinarith [mul_nonneg h0 h₁, mul_nonneg hθ1 h₂]
      constructor
      · rcases mul_eq_zero.1 e1 with h | h
        · rw [h, zero_mul]
        · rw [h, zero_rpow hr.ne', mul_zero]
      · rcases mul_eq_zero.1 e2 with h | h
        · rw [h, zero_mul]
        · rw [h, zero_rpow hr.ne', mul_zero]
  rcases eq_or_lt_of_le hm₁ with he₁ | hlt₁
  · obtain ⟨z1, z2⟩ := zero_case p hp hu₁ hv₁ he₁.symm
    rw [← he₁, zero_rpow hp.ne', zero_mul,
      show θ * (u₁ ^ p * u₂ ^ q) = θ * u₁ ^ p * u₂ ^ q by ring,
      show (1 - θ) * (v₁ ^ p * v₂ ^ q) = (1 - θ) * v₁ ^ p * v₂ ^ q by ring, z1, z2]
    simp
  rcases eq_or_lt_of_le hm₂ with he₂ | hlt₂
  · obtain ⟨z1, z2⟩ := zero_case q hq hu₂ hv₂ he₂.symm
    rw [← he₂, zero_rpow hq.ne', mul_zero,
      show θ * (u₁ ^ p * u₂ ^ q) = θ * u₂ ^ q * u₁ ^ p by ring,
      show (1 - θ) * (v₁ ^ p * v₂ ^ q) = (1 - θ) * v₂ ^ q * v₁ ^ p by ring, z1, z2]
    simp
  -- AM–GM for `u/m` and `v/m`
  have hu := geom_mean_le_arith_mean2_weighted hp.le hq.le (div_nonneg hu₁ hlt₁.le)
    (div_nonneg hu₂ hlt₂.le) hpq
  have hv := geom_mean_le_arith_mean2_weighted hp.le hq.le (div_nonneg hv₁ hlt₁.le)
    (div_nonneg hv₂ hlt₂.le) hpq
  rw [div_rpow hu₁ hlt₁.le, div_rpow hu₂ hlt₂.le] at hu
  rw [div_rpow hv₁ hlt₁.le, div_rpow hv₂ hlt₂.le] at hv
  have hG : 0 < m₁ ^ p * m₂ ^ q := mul_pos (rpow_pos_of_pos hlt₁ _) (rpow_pos_of_pos hlt₂ _)
  have e : ∀ s t : ℝ, s ^ p / m₁ ^ p * (t ^ q / m₂ ^ q) = s ^ p * t ^ q / (m₁ ^ p * m₂ ^ q) :=
    fun s t => by rw [div_mul_div_comm]
  rw [e] at hu hv
  rw [div_le_iff₀ hG] at hu hv
  have hsum : θ * (p * (u₁ / m₁) + q * (u₂ / m₂)) + (1 - θ) * (p * (v₁ / m₁) + q * (v₂ / m₂)) =
      1 := by
    field_simp
    simp only [m₁, m₂] at *
    linear_combination (θ * u₁ + (1 - θ) * v₁) * (θ * u₂ + (1 - θ) * v₂) * hpq
  have := add_le_add (mul_le_mul_of_nonneg_left hu h0)
    (mul_le_mul_of_nonneg_left hv (by linarith : (0 : ℝ) ≤ 1 - θ))
  nlinarith

variable {a b : ℝ}

/-- **`F` is concave on `[0, 1]²`.** -/
theorem cd_concave (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) :
    ConcaveOn ℝ (Icc 0 1 ×ˢ Icc 0 1) (fun p : ℝ × ℝ => cdF a b p.1 p.2) := by
  refine ⟨(convex_Icc 0 1).prod (convex_Icc 0 1), ?_⟩
  rintro ⟨k, y⟩ ⟨⟨hk0, hk1⟩, ⟨hy0, hy1⟩⟩ ⟨k', y'⟩ ⟨⟨hk0', hk1'⟩, ⟨hy0', hy1'⟩⟩ θ μ h0 hμ hθμ
  simp only at hk0 hk1 hy0 hy1 hk0' hk1' hy0' hy1'
  obtain rfl : μ = 1 - θ := by linarith
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  set s := a + b
  have hs : 0 < s := by positivity
  set p := a / s
  set q := b / s
  have hp : 0 < p := div_pos ha hs
  have hq : 0 < q := div_pos hb hs
  have hpq : p + q = 1 := by simp only [p, q, s]; field_simp
  -- `F(k, y) = (k^p(1 − y)^q)^s`
  have hF : ∀ k y : ℝ, 0 ≤ k → y ≤ 1 → cdF a b k y = (k ^ p * (1 - y) ^ q) ^ s := by
    intro k y hk hy
    rw [mul_rpow (rpow_nonneg hk _) (rpow_nonneg (by linarith) _), ← rpow_mul hk,
      ← rpow_mul (by linarith : (0 : ℝ) ≤ 1 - y)]
    simp only [cdF, p, q, div_mul_cancel₀ _ hs.ne']
  have hm : θ * y + (1 - θ) * y' ≤ 1 := by nlinarith
  have hmk : 0 ≤ θ * k + (1 - θ) * k' := by nlinarith
  rw [hF k y hk0 hy1, hF k' y' hk0' hy1', hF _ _ hmk hm]
  have e : 1 - (θ * y + (1 - θ) * y') = θ * (1 - y) + (1 - θ) * (1 - y') := by ring
  rw [e]
  have hG := geomMean_concave (u₁ := k) (u₂ := 1 - y) (v₁ := k') (v₂ := 1 - y') hp hq hpq hk0
    (by linarith) hk0' (by linarith) h0 (by linarith)
  have hGu : 0 ≤ k ^ p * (1 - y) ^ q := mul_nonneg (rpow_nonneg hk0 _)
    (rpow_nonneg (by linarith) _)
  have hGv : 0 ≤ k' ^ p * (1 - y') ^ q := mul_nonneg (rpow_nonneg hk0' _)
    (rpow_nonneg (by linarith) _)
  have hconc := (concaveOn_rpow hs.le hab).2 (mem_Ici.2 hGu) (mem_Ici.2 hGv) h0
    (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hconc
  refine hconc.trans (rpow_le_rpow (by positivity) hG hs.le)

/-- **Exercise 6.7a (correction).** `F` is not strictly concave in the sense of Assumption 4.7:
on the edge `y = 1`, `F(1/4, 1) = F(3/4, 1) = F(1/2, 1) = 0`, although `1/4 ≠ 3/4`. -/
theorem cd_not_strict (hb : 0 < b) :
    (1 / 2 : ℝ) * cdF a b (1 / 4) 1 + (1 / 2) * cdF a b (3 / 4) 1 =
      cdF a b (1 / 2 * (1 / 4) + 1 / 2 * (3 / 4)) (1 / 2 * 1 + 1 / 2 * 1) := by
  norm_num [cdF, zero_rpow hb.ne']

/-- At an interior point, `DF(k, y)(u, w) = F_x u + F_y w`. -/
theorem hasFDerivAt_cd {k y : ℝ} (hk : 0 < k) (hy : y < 1) :
    HasFDerivAt (fun p : ℝ × ℝ => cdF a b p.1 p.2)
      (cdFx a b k y • ContinuousLinearMap.fst ℝ ℝ ℝ +
        cdFy a b k y • ContinuousLinearMap.snd ℝ ℝ ℝ) (k, y) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ a)
      ((a * k ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (k, y) := by
    have := (hasDerivAt_rpow_const (p := a) (Or.inl hk.ne')).comp_hasFDerivAt (k, y)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (k, y)))
    exact this
  have h2' : HasDerivAt (fun z : ℝ => (1 - z) ^ b) (-(b * (1 - y) ^ (b - 1))) y := by
    have hlin : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    convert hlin.rpow_const (p := b) (Or.inl (by linarith)) using 1
    ring
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => (1 - p.2) ^ b)
      ((-(b * (1 - y) ^ (b - 1))) • ContinuousLinearMap.snd ℝ ℝ ℝ) (k, y) := by
    have := h2'.comp_hasFDerivAt (k, y) (hasFDerivAt_snd (𝕜 := ℝ) (p := (k, y)))
    exact this
  unfold cdF
  convert h1.mul h2 using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [cdFx, cdFy, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cyclical example: optimal two-cycles

SLP Exercise 6.7e, p. 158. The sequence problem is `max Σ βᵗF(k_t, k_{t+1})` with
`F(k, y) = k^a(1 − y)^b` and `k_t ∈ [0, 1]` (`cdΓ`). A two-cycle `(x, y)`, `x ≠ y`, is the plan
`x, y, x, y, …` (`cyc`).

* **Exercise 6.7e** (`ex_6_7e`): for `x, y ∈ (0, 1)`, the two-cycle is optimal from `k₀ = x` iff
  `F_y(x, y) + βF_x(y, x) = 0` and `F_y(y, x) + βF_x(x, y) = 0`.
  * Sufficiency is Theorem 4.15's argument (`euler_sufficient`): `F` is concave on `[0, 1]²` and
    the boundary terms are at most a constant times `βᵗ⁺¹`.
  * Necessity moves a single `k_t` and leaves the rest of the plan alone; only two terms of the
    sum change, so their sum is maximized at the cycle, and its derivative vanishes there.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDynamics

variable {a b β : ℝ}

/-- `Γ(k) = [0, 1]` for `k ∈ [0, 1]` (and empty off `[0, 1]`). -/
def cdΓ (k : ℝ) : Set ℝ := {y | k ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1}

/-- The two-cycle `x, y, x, y, …`. -/
def cyc (x y : ℝ) (t : ℕ) : ℝ := if Even t then x else y

theorem cyc_succ (x y : ℝ) (t : ℕ) : cyc x y (t + 1) = cyc y x t := by
  simp only [cyc, Nat.even_add_one]
  split_ifs <;> rfl

theorem cdF_mem (ha : 0 < a) (hb : 0 < b) {k y : ℝ} (hk : k ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ cdF a b k y ∧ cdF a b k y ≤ 1 := by
  have h1 : 0 ≤ k ^ a := Real.rpow_nonneg hk.1 _
  have h2 : k ^ a ≤ 1 := Real.rpow_le_one hk.1 hk.2 ha.le
  have h3 : 0 ≤ (1 - y) ^ b := Real.rpow_nonneg (by linarith [hy.2]) _
  have h4 : (1 - y) ^ b ≤ 1 := Real.rpow_le_one (by linarith [hy.2]) (by linarith [hy.1]) hb.le
  exact ⟨mul_nonneg h1 h3, by unfold cdF; nlinarith⟩

theorem feasible_mem {x₀ : ℝ} {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) (t : ℕ) :
    p t ∈ Icc (0 : ℝ) 1 := by
  cases t with
  | zero => have := (hp.2 0).1; rwa [hp.1] at this ⊢
  | succ t => exact (hp.2 t).2

/-- Partial sums along a feasible plan converge to the (real) sum of the series. -/
theorem summable_plan (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ}
    {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) :
    Summable fun t => β ^ t * cdF a b (p t) (p (t + 1)) := by
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0 t)
    (cdF_mem ha hb (feasible_mem hp t) (feasible_mem hp (t + 1))).1) (fun t => ?_)
    (summable_geometric_of_lt_one hβ0 hβ1)
  have := (cdF_mem ha hb (feasible_mem hp t) (feasible_mem hp (t + 1))).2
  have := pow_nonneg hβ0 t
  nlinarith

theorem tendsto_partialSum (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ}
    {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) :
    Tendsto (fun n => partialSum (fun k y => cdF a b k y) β p n) atTop
      (𝓝 (∑' t, β ^ t * cdF a b (p t) (p (t + 1)))) := by
  simp only [partialSum]
  exact (summable_plan ha hb hβ0 hβ1 hp).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem cd_assumption42 (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Assumption42 cdΓ (fun k y => cdF a b k y) β := fun _ _ hp =>
  ⟨_, EReal.tendsto_coe.2 (tendsto_partialSum ha hb hβ0 hβ1 hp)⟩

theorem total_eq (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ} {p : ℕ → ℝ}
    (hp : p ∈ Feasible cdΓ x₀) :
    total (fun k y => cdF a b k y) β p = ((∑' t, β ^ t * cdF a b (p t) (p (t + 1)) : ℝ) : EReal) :=
  tendsto_nhds_unique (tendsto_total (cd_assumption42 ha hb hβ0 hβ1) hp)
    (EReal.tendsto_coe.2 (tendsto_partialSum ha hb hβ0 hβ1 hp))

theorem cyc_mem {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (t : ℕ) :
    cyc x y t ∈ Icc (0 : ℝ) 1 := by
  unfold cyc; split_ifs <;> assumption

theorem cyc_feasible {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    cyc x y ∈ Feasible cdΓ x :=
  ⟨by simp [cyc], fun t => ⟨cyc_mem hx hy t, cyc_mem hx hy (t + 1)⟩⟩

/-- The derivative of `F` at `(k_t, k_{t+1})` along the cycle. -/
noncomputable def cycD (a b x y : ℝ) (t : ℕ) : ℝ × ℝ →L[ℝ] ℝ :=
  cdFx a b (cyc x y t) (cyc x y (t + 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    cdFy a b (cyc x y t) (cyc x y (t + 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- **Exercise 6.7e (sufficiency).** A two-cycle in `(0, 1)` satisfying both Euler equations is
optimal from `x`. -/
theorem cyc_sufficient (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (h1 : cdFy a b x y + β * cdFx a b y x = 0) (h2 : cdFy a b y x + β * cdFx a b x y = 0) :
    total (fun k y => cdF a b k y) β (cyc x y) = vstar cdΓ (fun k y => cdF a b k y) β x := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hyI : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
  have hpos : ∀ t, cyc x y t ∈ Ioo (0 : ℝ) 1 := fun t => by unfold cyc; split_ifs <;> assumption
  refine euler_sufficient (F := fun p : ℝ × ℝ => cdF a b p.1 p.2) (cd_assumption42 ha hb hβ0 hβ1)
    (cyc_feasible hxI hyI) (cycD a b x y) (fun t x' y' hy' => ?_) (fun t v => ?_) hβ0
    (fun x' hx' _ => ?_)
  · -- `F` lies below its tangent plane on `[0, 1]²`
    exact concave_le_fderiv (cd_concave ha hb hab)
      (show (cyc x y t, cyc x y (t + 1)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨cyc_mem hxI hyI t, cyc_mem hxI hyI (t + 1)⟩)
      (show (x', y') ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from ⟨hy'.1, hy'.2⟩)
      (hasFDerivAt_cd (hpos t).1 (hpos (t + 1)).2)
  · -- the Euler equations along the cycle
    simp only [Fy, Fx, cycD, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero,
      add_zero, zero_add]
    rw [cyc_succ, cyc_succ, cyc_succ y x]
    unfold cyc
    split_ifs
    · linear_combination v * h1
    · linear_combination v * h2
  · -- the boundary terms are at most `βᵀ⁺¹(|F_x(x, y)| + |F_x(y, x)|)`
    set C := |cdFx a b x y| + |cdFx a b y x|
    refine ⟨fun T => β ^ (T + 1) * C, ?_, fun T => ?_⟩
    · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).comp
        (tendsto_add_atTop_nat 1)).mul_const C
    · simp only [Fx, cycD, _root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero,
        add_zero]
      have hd : |cyc x y (T + 1) - x' (T + 1)| ≤ 1 := by
        have h1' := cyc_mem hxI hyI (T + 1)
        have h2' := feasible_mem hx' (T + 1)
        rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
      have hc : |cdFx a b (cyc x y (T + 1)) (cyc x y (T + 1 + 1))| ≤ C := by
        have e : cyc x y (T + 1 + 1) = cyc x y T := by rw [cyc_succ, cyc_succ]
        rw [e, cyc_succ]
        unfold cyc
        split_ifs <;> simp only [C] <;>
          linarith [abs_nonneg (cdFx a b x y), abs_nonneg (cdFx a b y x)]
      have hb' := pow_nonneg hβ0 (T + 1)
      calc β ^ (T + 1) * (cdFx a b (cyc x y (T + 1)) (cyc x y (T + 1 + 1)) *
            (cyc x y (T + 1) - x' (T + 1)))
          ≤ β ^ (T + 1) * |cdFx a b (cyc x y (T + 1)) (cyc x y (T + 1 + 1)) *
            (cyc x y (T + 1) - x' (T + 1))| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hb'
        _ ≤ β ^ (T + 1) * (C * 1) := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (mul_le_mul hc hd (abs_nonneg _)
              (le_trans (abs_nonneg _) hc)) hb'
        _ = β ^ (T + 1) * C := by ring

/-- Changing a feasible plan at the single date `j + 1` changes the value by the two affected
terms. -/
theorem sum_update (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x₀ : ℝ}
    {p : ℕ → ℝ} (hp : p ∈ Feasible cdΓ x₀) (j : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    Function.update p (j + 1) z ∈ Feasible cdΓ x₀ ∧
      ∑' t, β ^ t * cdF a b (Function.update p (j + 1) z t)
          (Function.update p (j + 1) z (t + 1)) =
        ∑' t, β ^ t * cdF a b (p t) (p (t + 1)) +
          (β ^ j * (cdF a b (p j) z - cdF a b (p j) (p (j + 1))) +
            β ^ (j + 1) * (cdF a b z (p (j + 2)) - cdF a b (p (j + 1)) (p (j + 2)))) := by
  set p' := Function.update p (j + 1) z
  have hmem : ∀ t, p' t ∈ Icc (0 : ℝ) 1 := fun t => by
    simp only [p', Function.update_apply]
    split_ifs
    · exact hz
    · exact feasible_mem hp t
  have hp' : p' ∈ Feasible cdΓ x₀ := ⟨by simp [p', hp.1], fun t => ⟨hmem t, hmem (t + 1)⟩⟩
  refine ⟨hp', ?_⟩
  have hs := summable_plan ha hb hβ0 hβ1 hp
  have hs' := summable_plan (a := a) (b := b) ha hb hβ0 hβ1 hp'
  rw [← sub_eq_iff_eq_add', ← hs'.tsum_sub hs]
  rw [tsum_eq_sum (s := {j, j + 1}) fun t ht => ?_]
  · rw [Finset.sum_pair (by omega)]
    simp only [p', Function.update_self, Function.update_of_ne (show j ≠ j + 1 by omega),
      Function.update_of_ne (show j + 1 + 1 ≠ j + 1 by omega)]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp only [p', Function.update_of_ne (show t ≠ j + 1 from ht.2),
      Function.update_of_ne (show t + 1 ≠ j + 1 by omega), sub_self]

/-- **Exercise 6.7e (necessity).** An optimal two-cycle in `(0, 1)` satisfies both Euler
equations. -/
theorem cyc_necessary (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β) (hβ1 : β < 1) {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hopt : total (fun k y => cdF a b k y) β (cyc x y) = vstar cdΓ (fun k y => cdF a b k y) β x) :
    cdFy a b x y + β * cdFx a b y x = 0 ∧ cdFy a b y x + β * cdFx a b x y = 0 := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hyI : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
  have hfeas := cyc_feasible hxI hyI
  -- the change at date `j + 1` is never positive
  have hle : ∀ j : ℕ, ∀ z ∈ Icc (0 : ℝ) 1,
      β ^ j * (cdF a b (cyc x y j) z - cdF a b (cyc x y j) (cyc x y (j + 1))) +
        β ^ (j + 1) * (cdF a b z (cyc x y (j + 2)) - cdF a b (cyc x y (j + 1)) (cyc x y (j + 2)))
        ≤ 0 := by
    intro j z hz
    obtain ⟨hp', hsum⟩ := sum_update ha hb hβ0.le hβ1 hfeas j hz
    have h1 : total (fun k y => cdF a b k y) β (Function.update (cyc x y) (j + 1) z) ≤
        vstar cdΓ (fun k y => cdF a b k y) β x := le_biSup (total (fun k y => cdF a b k y) β) hp'
    rw [← hopt, total_eq ha hb hβ0.le hβ1 hp', total_eq ha hb hβ0.le hβ1 hfeas, hsum,
      EReal.coe_le_coe_iff] at h1
    linarith
  have hc0 : cyc x y 0 = x := by simp [cyc]
  have hc1 : cyc x y 1 = y := by simp [cyc]
  have hc2 : cyc x y 2 = x := by simp [cyc]
  have hc3 : cyc x y 3 = y := by simp [cyc, Nat.even_iff]
  -- Fermat's theorem in the moved coordinate
  have fermat : ∀ u v : ℝ, u ∈ Ioo (0 : ℝ) 1 → v ∈ Ioo (0 : ℝ) 1 →
      (∀ z ∈ Icc (0 : ℝ) 1, cdF a b u z + β * cdF a b z u ≤ cdF a b u v + β * cdF a b v u) →
      cdFy a b u v + β * cdFx a b v u = 0 := fun u v hu hv hmax => by
    have hd : HasDerivAt (fun z => cdF a b u z + β * cdF a b z u)
        (cdFy a b u v + β * cdFx a b v u) v :=
      (hasDerivAt_cdF_y u hv.2).add ((hasDerivAt_cdF_k hv.1 u).const_mul β)
    refine IsLocalMax.hasDerivAt_eq_zero ?_ hd
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with z hz
    exact hmax z (Ioo_subset_Icc_self hz)
  refine ⟨fermat x y hx hy fun z hz => ?_, fermat y x hy hx fun z hz => ?_⟩
  · have := hle 0 z hz
    rw [hc0, hc1, hc2] at this
    simp only [pow_zero, one_mul, zero_add, pow_one] at this
    linarith
  · have := hle 1 z hz
    rw [hc1, show (1 + 1 : ℕ) = 2 from rfl, hc2, show (1 + 2 : ℕ) = 3 from rfl, hc3] at this
    have h2 : β * (cdF a b y z - cdF a b y x + β * (cdF a b z y - cdF a b x y)) ≤ 0 := by
      simp only [pow_one, pow_two] at this
      linarith
    have := nonpos_of_mul_nonpos_right h2 hβ0
    linarith

/-- **Exercise 6.7e.** For `x, y ∈ (0, 1)`, the two-cycle `(x, y)` is optimal from `k₀ = x` iff
`F_y(x, y) + βF_x(y, x) = 0` and `F_y(y, x) + βF_x(x, y) = 0`. -/
theorem ex_6_7e (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    total (fun k y => cdF a b k y) β (cyc x y) = vstar cdΓ (fun k y => cdF a b k y) β x ↔
      cdFy a b x y + β * cdFx a b y x = 0 ∧ cdFy a b y x + β * cdFx a b x y = 0 :=
  ⟨cyc_necessary ha hb hβ0 hβ1 hx hy, fun h =>
    cyc_sufficient ha hb hab hβ0.le hβ1 hx hy h.1 h.2⟩

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cyclical example: the two-cycle at `β = 0.1`, `α = 0.8`, `θ = 0.75`

SLP Exercise 6.7f–g, p. 158. Here `a = αθ = 3/5`, `b = α(1 − θ) = 1/5`, `β = 1/10`.

* **The Euler equations as polynomials** (`euler_iff_poly`). For `x, y ∈ (0, 1)`,
  `F_y(x, y) + βF_x(y, x) = 0` iff `P(x, y) = b⁵x³y² − (βa)⁵(1 − x)(1 − y)⁴ = 0`. Multiply by
  `y^{2/5}(1 − y)^{4/5}` and raise to the fifth power.
* **Exercise 6.7f (correction).** `(0.29, 0.18)` is not a two-cycle: no two-cycle has
  `x ∈ [0.28, 0.30]` and `y ∈ [0.17, 0.19]` (`ex_6_7f_book_box`). The two Euler equations force
  `x(1 − x)³ = y(1 − y)³`, which fails on that box.
  The optimal two-cycle has `x ∈ (0.483, 0.485)` and `y ∈ (0.087, 0.088)`; numerically it is
  `(0.4838, 0.0876)` (`ex_6_7f`). Its existence comes from the intermediate value theorem along
  the curve `P(x, y) = 0` (`polyRoot`), and its optimality from Exercise 6.7e.
* **Exercise 6.7g** (`ex_6_7g`). Linearize the stacked map `(k_{t+1}, k_t) ↦ (k_{t+3}, k_{t+2})`
  at the cycle. With the Euler equations, `J₁ = (1 − x)[(b − 1)/(1 − y) + (a − 1)/y]/b` and
  `K₁ = −a(1 − x)/(bx)`, and symmetrically for `J₂`, `K₂`. The two-step matrix has determinant
  `K₁K₂ = β⁻² = 100` and trace `16 + 5X + 5Y + 4XY > 101`, where `X = (1 − x)/x` and
  `Y = (1 − y)/y`. So its characteristic roots are real, one in `(0, 1)` (about `0.855`) and one
  above `1` (about `117`): one root is less than one in absolute value.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Set Filter Topology Real

/-- The Euler equation `F_y(x, y) + βF_x(y, x) = 0` as a polynomial:
`P(x, y) = (1/5)⁵x³y² − (3/50)⁵(1 − x)(1 − y)⁴`. -/
noncomputable def cycP (x y : ℝ) : ℝ :=
  (1 / 5) ^ 5 * x ^ 3 * y ^ 2 - (3 / 50) ^ 5 * (1 - x) * (1 - y) ^ 4

/-- `t^{k/5} = (t^{1/5})^k` for `t > 0`. -/
theorem rpow_fifth {t : ℝ} (ht : 0 < t) (k : ℕ) :
    t ^ ((k : ℝ) / 5) = (t ^ ((1 : ℝ) / 5)) ^ k := by
  rw [← rpow_natCast (t ^ ((1 : ℝ) / 5)), ← rpow_mul ht.le]
  congr 1; ring

/-- `(t^{1/5})⁵ = t` for `t > 0`. -/
theorem fifth_pow {t : ℝ} (ht : 0 < t) : (t ^ ((1 : ℝ) / 5)) ^ 5 = t := by
  rw [← rpow_natCast, ← rpow_mul ht.le]; norm_num

/-- **The Euler equation as a polynomial.** For `x, y ∈ (0, 1)`,
`F_y(x, y) + βF_x(y, x) = 0 ↔ P(x, y) = 0` (`a = 3/5`, `b = 1/5`, `β = 1/10`). -/
theorem euler_iff_poly {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0 ↔ cycP x y = 0 := by
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  set u := x ^ ((1 : ℝ) / 5)
  set w := y ^ ((1 : ℝ) / 5)
  set r := (1 - x) ^ ((1 : ℝ) / 5)
  set s := (1 - y) ^ ((1 : ℝ) / 5)
  have hu : 0 < u := rpow_pos_of_pos hx.1 _
  have hw : 0 < w := rpow_pos_of_pos hy.1 _
  have hr : 0 < r := rpow_pos_of_pos hx1 _
  have hs : 0 < s := rpow_pos_of_pos hy1 _
  -- the four powers in terms of fifth roots
  have e1 : x ^ (3 / 5 : ℝ) = u ^ 3 := by
    rw [show (3 / 5 : ℝ) = ((3 : ℕ) : ℝ) / 5 by norm_num, rpow_fifth hx.1]
  have e2 : (1 - y) ^ (1 / 5 - 1 : ℝ) = (s ^ 4)⁻¹ := by
    rw [show (1 / 5 - 1 : ℝ) = -(((4 : ℕ) : ℝ) / 5) by norm_num, rpow_neg hy1.le,
      rpow_fifth hy1]
  have e3 : y ^ (3 / 5 - 1 : ℝ) = (w ^ 2)⁻¹ := by
    rw [show (3 / 5 - 1 : ℝ) = -(((2 : ℕ) : ℝ) / 5) by norm_num, rpow_neg hy.1.le,
      rpow_fifth hy.1]
  have e4 : (1 - x) ^ (1 / 5 : ℝ) = r := rfl
  have hE : cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x =
      (3 / 50 * r * s ^ 4 - 1 / 5 * u ^ 3 * w ^ 2) / (w ^ 2 * s ^ 4) := by
    simp only [cdFy, cdFx, e1, e2, e3, e4]
    field_simp
    ring
  have hx5 := fifth_pow hx.1
  have hy5 := fifth_pow hy.1
  have hr5 := fifth_pow hx1
  have hs5 := fifth_pow hy1
  rw [hE, div_eq_zero_iff, or_iff_left (by positivity), sub_eq_zero]
  -- `L = R ↔ L⁵ = R⁵` for positive `L`, `R`
  have hL : 0 < 1 / 5 * u ^ 3 * w ^ 2 := by positivity
  have hR : 0 < 3 / 50 * r * s ^ 4 := by positivity
  have h5 : (3 / 50 * r * s ^ 4) ^ 5 = (1 / 5 * u ^ 3 * w ^ 2) ^ 5 ↔ cycP x y = 0 := by
    have eR : (3 / 50 * r * s ^ 4) ^ 5 = (3 / 50) ^ 5 * r ^ 5 * (s ^ 5) ^ 4 := by ring
    have eL : (1 / 5 * u ^ 3 * w ^ 2) ^ 5 = (1 / 5) ^ 5 * (u ^ 5) ^ 3 * (w ^ 5) ^ 2 := by ring
    rw [eR, eL, hx5, hy5, hr5, hs5, cycP]
    constructor <;> intro h <;> linarith
  rw [← h5]
  exact (pow_left_inj₀ hR.le hL.le (by norm_num : (5 : ℕ) ≠ 0)).symm

/-! ### The curve `P(x, y) = 0` -/

theorem cycP_strictMono_y {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {y y' : ℝ} (hy : 0 ≤ y)
    (hyy' : y < y') (hy' : y' ≤ 1) : cycP x y < cycP x y' := by
  have hx3 : 0 < x ^ 3 := pow_pos hx.1 3
  have h1 : y ^ 2 < y' ^ 2 := by nlinarith
  have h2 : (1 - y') ^ 4 < (1 - y) ^ 4 := by
    have : 0 ≤ 1 - y' := by linarith
    exact pow_lt_pow_left₀ (by linarith) this (by norm_num)
  have h3 : 0 < 1 - x := by linarith [hx.2]
  simp only [cycP]
  nlinarith [mul_lt_mul_of_pos_left h1 hx3, mul_lt_mul_of_pos_left h2 h3]

/-- `P(y, x)` rises with `y ∈ [0, 1]` (for `x ∈ (0, 1)`). -/
theorem cycP_mono_x {x y y' : ℝ} (hy : 0 ≤ y) (hyy' : y ≤ y') : cycP y x ≤ cycP y' x := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h1 : y ^ 3 ≤ y' ^ 3 := pow_le_pow_left₀ hy hyy' 3
  have h4 : 0 ≤ (1 - x) ^ 4 := by positivity
  simp only [cycP]
  nlinarith [mul_le_mul_of_nonneg_right h1 hx2, mul_le_mul_of_nonneg_right hyy' h4]

/-- The root `y = φ(x)` of `P(x, ·)` in `[0, 1]`. -/
noncomputable def polyRoot (x : ℝ) : ℝ := sInf {y | y ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ cycP x y}

theorem continuous_cycP : Continuous fun p : ℝ × ℝ => cycP p.1 p.2 := by
  unfold cycP; fun_prop

theorem polyRoot_spec {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    polyRoot x ∈ Ioo (0 : ℝ) 1 ∧ cycP x (polyRoot x) = 0 := by
  set S := {y | y ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ cycP x y}
  have hP0 : cycP x 0 < 0 := by simp only [cycP]; nlinarith [hx.1, hx.2]
  have hP1 : 0 < cycP x 1 := by simp only [cycP]; have := pow_pos hx.1 3; nlinarith
  have hne : S.Nonempty := ⟨1, ⟨by norm_num, le_rfl⟩, hP1.le⟩
  have hbdd : BddBelow S := ⟨0, fun y hy => hy.1.1⟩
  have hcl : IsClosed S := by
    have hc : Continuous fun y => cycP x y := by unfold cycP; fun_prop
    exact isClosed_Icc.inter (isClosed_le continuous_const hc)
  have hmem : polyRoot x ∈ S := hcl.csInf_mem hne hbdd
  -- the intermediate value theorem on `[0, φ(x)]`
  have hc : ContinuousOn (fun y => cycP x y) (Icc 0 (polyRoot x)) := by
    unfold cycP; fun_prop
  obtain ⟨y₀, hy₀, hy₀P⟩ := intermediate_value_Icc hmem.1.1 hc ⟨hP0.le, hmem.2⟩
  have hy₀S : y₀ ∈ S := ⟨⟨hy₀.1, hy₀.2.trans hmem.1.2⟩, hy₀P.ge⟩
  have hle : polyRoot x ≤ y₀ := csInf_le hbdd hy₀S
  have heq : y₀ = polyRoot x := le_antisymm hy₀.2 hle
  have hroot : cycP x (polyRoot x) = 0 := by rw [← heq]; exact hy₀P
  refine ⟨⟨lt_of_le_of_ne hmem.1.1 fun h => ?_, lt_of_le_of_ne hmem.1.2 fun h => ?_⟩, hroot⟩
  · rw [← h] at hroot; linarith
  · rw [h] at hroot; linarith

theorem polyRoot_le {x y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hP : 0 ≤ cycP x y) : polyRoot x ≤ y :=
  csInf_le ⟨0, fun _ h => h.1.1⟩ ⟨hy, hP⟩

theorem lt_polyRoot {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hP : cycP x y < 0) : y < polyRoot x := by
  obtain ⟨hφ, hroot⟩ := polyRoot_spec hx
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with he | hlt
  · rw [he] at hroot; linarith
  · have := cycP_strictMono_y hx hφ.1.le hlt hy.2; linarith

theorem continuousAt_polyRoot {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt polyRoot x₀ := by
  obtain ⟨hφ, hroot⟩ := polyRoot_spec hx₀
  have hI : ∀ᶠ x in 𝓝 x₀, x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds hx₀.1 hx₀.2
  have hcy : ∀ y, ContinuousAt (fun x => cycP x y) x₀ := fun y => by
    unfold cycP; fun_prop
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rcases lt_or_ge c 0 with hc0 | hc0
    · filter_upwards [hI] with x hx
      exact hc0.trans (polyRoot_spec hx).1.1
    · set c' := (c + polyRoot x₀) / 2
      have hc' : c < c' ∧ c' < polyRoot x₀ := ⟨by simp only [c']; linarith,
        by simp only [c']; linarith⟩
      have hneg : cycP x₀ c' < 0 := by
        have := cycP_strictMono_y hx₀ (by linarith) hc'.2 hφ.2.le; linarith
      filter_upwards [hI, (hcy c').eventually (gt_mem_nhds hneg)] with x hx hxc
      exact hc'.1.trans (lt_polyRoot hx ⟨by linarith, by linarith [hφ.2]⟩ hxc)
  · rcases lt_or_ge 1 c with hc1 | hc1
    · filter_upwards [hI] with x hx
      exact (polyRoot_spec hx).1.2.trans hc1
    · set c' := (c + polyRoot x₀) / 2
      have hc' : polyRoot x₀ < c' ∧ c' < c := ⟨by simp only [c']; linarith,
        by simp only [c']; linarith⟩
      have hpos : 0 < cycP x₀ c' := by
        have := cycP_strictMono_y hx₀ hφ.1.le hc'.1 (by linarith); linarith
      filter_upwards [(hcy c').eventually (lt_mem_nhds hpos)] with x hxc
      exact (polyRoot_le ⟨by linarith [hφ.1], by linarith⟩ hxc.le).trans_lt hc'.2

/-! ### Exercise 6.7f -/

/-- A two-cycle `(x, y)`, `x ≠ y`, in `(0, 1)` gives `x(1 − x)³ = y(1 − y)³`. -/
theorem cycle_q_eq {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (h1 : cycP x y = 0) (h2 : cycP y x = 0) : x * (1 - x) ^ 3 = y * (1 - y) ^ 3 := by
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  simp only [cycP] at h1 h2
  -- cross-multiply the two equations and cancel `x²y²(1 − x)(1 − y)`
  have hc : x ^ 3 * y ^ 2 * ((1 - y) * (1 - x) ^ 4) = y ^ 3 * x ^ 2 * ((1 - x) * (1 - y) ^ 4) := by
    have e1 : (1 / 5 : ℝ) ^ 5 * x ^ 3 * y ^ 2 = (3 / 50) ^ 5 * (1 - x) * (1 - y) ^ 4 := by
      linarith
    have e2 : (1 / 5 : ℝ) ^ 5 * y ^ 3 * x ^ 2 = (3 / 50) ^ 5 * (1 - y) * (1 - x) ^ 4 := by
      linarith
    linear_combination (5 : ℝ) ^ 5 * ((1 - y) * (1 - x) ^ 4) * e1 -
      (5 : ℝ) ^ 5 * ((1 - x) * (1 - y) ^ 4) * e2
  have hpos : 0 < x ^ 2 * y ^ 2 * (1 - x) * (1 - y) :=
    mul_pos (mul_pos (mul_pos (pow_pos hx.1 2) (pow_pos hy.1 2)) hx1) hy1
  have : (x * (1 - x) ^ 3) * (x ^ 2 * y ^ 2 * (1 - x) * (1 - y)) =
      (y * (1 - y) ^ 3) * (x ^ 2 * y ^ 2 * (1 - x) * (1 - y)) := by nlinarith [hc]
  exact mul_right_cancel₀ hpos.ne' this

/-- **Exercise 6.7f (correction).** There is no two-cycle with `x ∈ [0.28, 0.30]` and
`y ∈ [0.17, 0.19]`; in particular `(0.29, 0.18)` is not one. -/
theorem ex_6_7f_book_box {x y : ℝ} (hx : x ∈ Icc (0.28 : ℝ) 0.30) (hy : y ∈ Icc (0.17 : ℝ) 0.19) :
    ¬ (cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0 ∧
      cdFy (3 / 5) (1 / 5) y x + 1 / 10 * cdFx (3 / 5) (1 / 5) x y = 0) := by
  rintro ⟨h1, h2⟩
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hq := cycle_q_eq hxI hyI ((euler_iff_poly hxI hyI).1 h1) ((euler_iff_poly hyI hxI).1 h2)
  -- `x(1 − x)³ ≥ 0.1029 > 0.101 ≥ y(1 − y)³` on the box
  have hqx : 0.1029 ≤ x * (1 - x) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2), hx.1, hx.2,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2)) (sub_nonneg.2 hx.2)]
  have hqy : y * (1 - y) ^ 3 ≤ 0.101 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2), hy.1, hy.2,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)) (sub_nonneg.2 hy.1)]
  linarith

/-- **Exercise 6.7f.** For `β = 0.1`, `α = 0.8`, `θ = 0.75` there is an optimal two-cycle
`(x, y)` with `0.483 ≤ x ≤ 0.485` and `0.087 < y < 0.088`. -/
theorem ex_6_7f : ∃ x y : ℝ, x ∈ Icc (0.483 : ℝ) 0.485 ∧ y ∈ Ioo (0.087 : ℝ) 0.088 ∧
    cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0 ∧
    cdFy (3 / 5) (1 / 5) y x + 1 / 10 * cdFx (3 / 5) (1 / 5) x y = 0 ∧
    total (fun k y => cdF (3 / 5) (1 / 5) k y) (1 / 10) (cyc x y) =
      vstar cdΓ (fun k y => cdF (3 / 5) (1 / 5) k y) (1 / 10) x := by
  have hI : ∀ x ∈ Icc (0.483 : ℝ) 0.485, x ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set G : ℝ → ℝ := fun x => cycP (polyRoot x) x
  have hGc : ContinuousOn G (Icc 0.483 0.485) := fun x hx =>
    ((continuous_cycP.continuousAt).comp ((continuousAt_polyRoot (hI x hx)).prodMk
      continuousAt_id)).continuousWithinAt
  -- the sign of `G` at the ends, through brackets for the root
  have hG1 : G 0.483 ≤ 0 := by
    have hb : polyRoot 0.483 ≤ 0.08786 :=
      polyRoot_le ⟨by norm_num, by norm_num⟩ (by norm_num [cycP])
    have h0 := (polyRoot_spec (hI 0.483 ⟨le_rfl, by norm_num⟩)).1.1.le
    exact (cycP_mono_x h0 hb).trans (by norm_num [cycP])
  have hG2 : 0 ≤ G 0.485 := by
    have hb : 0.08725 < polyRoot 0.485 :=
      lt_polyRoot (hI 0.485 ⟨by norm_num, le_rfl⟩) ⟨by norm_num, by norm_num⟩
        (by norm_num [cycP])
    exact (show (0 : ℝ) ≤ cycP 0.08725 0.485 by norm_num [cycP]).trans
      (cycP_mono_x (by norm_num) hb.le)
  obtain ⟨x, hx, hGx⟩ := intermediate_value_Icc (by norm_num) hGc ⟨hG1, hG2⟩
  have hxI := hI x hx
  obtain ⟨hyI, hPxy⟩ := polyRoot_spec hxI
  set y := polyRoot x
  -- bounds on `y`
  have hyhi : y ≤ 0.08786 := by
    refine polyRoot_le ⟨by norm_num, by norm_num⟩ ?_
    exact (show (0 : ℝ) ≤ cycP 0.483 0.08786 by norm_num [cycP]).trans
      (cycP_mono_x (by norm_num) hx.1)
  have hylo : 0.08725 < y := by
    refine lt_polyRoot hxI ⟨by norm_num, by norm_num⟩ ?_
    exact lt_of_le_of_lt (cycP_mono_x (by linarith [hx.1]) hx.2) (by norm_num [cycP])
  have e1 := (euler_iff_poly hxI hyI).2 hPxy
  have e2 := (euler_iff_poly hyI hxI).2 hGx
  refine ⟨x, y, hx, ⟨by linarith, by linarith⟩, e1, e2, ?_⟩
  exact (ex_6_7e (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxI
    hyI).2 ⟨e1, e2⟩

/-! ### Exercise 6.7g -/

/-- The linearized Euler equation along a path: with `z = k − k̄`,
`z_{t+2} = Jz_{t+1} + Kz_t`, where `J = −(F_yy(p, q) + βF_xx(q, r))/(βF_xy(q, r))` and
`K = −F_xy(p, q)/(βF_xy(q, r))` at `(p, q, r) = (k_t, k_{t+1}, k_{t+2})`. -/
noncomputable def linJ (a b β p q r : ℝ) : ℝ :=
  -(cdFyy a b p q + β * cdFxx a b q r) / (β * cdFxy a b q r)

noncomputable def linK (a b β p q r : ℝ) : ℝ := -cdFxy a b p q / (β * cdFxy a b q r)

/-- Along a path satisfying the Euler equation `F_y(p, q) + βF_x(q, r) = 0`,
`J = (1 − r)[(b − 1)/(1 − q) + (a − 1)/q]/b` and `K = −a(1 − r)/(bp)`. -/
theorem linJK_eq {a b β p q r : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (he : cdFy a b p q + β * cdFx a b q r = 0) :
    linJ a b β p q r = (1 - r) * ((b - 1) / (1 - q) + (a - 1) / q) / b ∧
      linK a b β p q r = -(a * (1 - r) / (b * p)) := by
  have hq1 : 0 < 1 - q := by linarith [hq.2]
  have hr1 : 0 < 1 - r := by linarith [hr.2]
  -- `Q = aq^{a−1}(1 − r)^b` and the Euler equation `bp^a(1 − q)^{b−1} = βQ`
  set Q := a * q ^ (a - 1) * (1 - r) ^ b
  have hQ : 0 < Q := mul_pos (mul_pos ha (rpow_pos_of_pos hq.1 _)) (rpow_pos_of_pos hr1 _)
  have hE : b * p ^ a * (1 - q) ^ (b - 1) = β * Q := by
    simp only [cdFy, cdFx] at he; simp only [Q]; linarith
  have r1 : (1 - q) ^ (b - 2) = (1 - q) ^ (b - 1) / (1 - q) := by
    rw [eq_div_iff hq1.ne', ← rpow_add_one hq1.ne']; congr 1; ring
  have r2 : q ^ (a - 2) = q ^ (a - 1) / q := by
    rw [eq_div_iff hq.1.ne', ← rpow_add_one hq.1.ne']; congr 1; ring
  have r3 : p ^ (a - 1) = p ^ a / p := by
    rw [eq_div_iff hp.1.ne', ← rpow_add_one hp.1.ne']; congr 1; ring
  have r4 : (1 - r) ^ (b - 1) = (1 - r) ^ b / (1 - r) := by
    rw [eq_div_iff hr1.ne', ← rpow_add_one hr1.ne']; congr 1; ring
  have hyy : cdFyy a b p q = (b - 1) / (1 - q) * (β * Q) := by
    rw [← hE]; simp only [cdFyy, r1]; field_simp
  have hxx : cdFxx a b q r = (a - 1) / q * Q := by
    simp only [cdFxx, Q, r2]; field_simp
  have hxyqr : cdFxy a b q r = -(b / (1 - r) * Q) := by
    simp only [cdFxy, Q, r4]; field_simp
  have hxypq : cdFxy a b p q = -(a / p * (β * Q)) := by
    rw [← hE]; simp only [cdFxy, r3]; field_simp
  constructor
  · rw [linJ, hyy, hxx, hxyqr]; field_simp
  · rw [linK, hxypq, hxyqr]; field_simp

/-- **Exercise 6.7g.** At the two-cycle of Exercise 6.7f, the stacked map
`(k_{t+1}, k_t) ↦ (k_{t+3}, k_{t+2})` has the linearization
`M = [[J₂, K₂], [1, 0]]·[[J₁, K₁], [1, 0]]` (`J₁ = J(x, y, x)`, `J₂ = J(y, x, y)`, and likewise
for `K`). Its characteristic roots are real, one in `(0, 1)` and one greater than `1`: exactly
one root is less than one in absolute value. -/
theorem ex_6_7g {x y : ℝ} (hx : x ∈ Icc (0.483 : ℝ) 0.485) (hy : y ∈ Ioo (0.087 : ℝ) 0.088)
    (e1 : cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0)
    (e2 : cdFy (3 / 5) (1 / 5) y x + 1 / 10 * cdFx (3 / 5) (1 / 5) x y = 0) :
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![linJ (3 / 5) (1 / 5) (1 / 10) y x y, linK (3 / 5) (1 / 5) (1 / 10) y x y; 1, 0] *
        !![linJ (3 / 5) (1 / 5) (1 / 10) x y x, linK (3 / 5) (1 / 5) (1 / 10) x y x; 1, 0]
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ < 1 ∧ 1 < μ₂ ∧ quadRoot M.trace M.det μ₁ ∧
      quadRoot M.trace M.det μ₂ ∧ ∀ μ, quadRoot M.trace M.det μ → μ = μ₁ ∨ μ = μ₂ := by
  intro M
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨hJ1, hK1⟩ := linJK_eq (by norm_num) (by norm_num) (by norm_num) hxI hyI hxI e1
  obtain ⟨hJ2, hK2⟩ := linJK_eq (by norm_num) (by norm_num) (by norm_num) hyI hxI hyI e2
  -- `det M = K₁K₂ = β⁻² = 100`, `tr M = J₁J₂ + K₁ + K₂`
  have hdet : M.det = linK (3 / 5) (1 / 5) (1 / 10) x y x * linK (3 / 5) (1 / 5) (1 / 10) y x y :=
    by simp only [M, Matrix.det_mul, Matrix.det_fin_two_of]; ring
  have htr : M.trace = linJ (3 / 5) (1 / 5) (1 / 10) y x y * linJ (3 / 5) (1 / 5) (1 / 10) x y x +
      linK (3 / 5) (1 / 5) (1 / 10) y x y + linK (3 / 5) (1 / 5) (1 / 10) x y x := by
    simp [M, Matrix.trace_fin_two]
  have hK12 : linK (3 / 5) (1 / 5) (1 / 10) x y x * linK (3 / 5) (1 / 5) (1 / 10) y x y = 100 := by
    have hxy0 : cdFxy (3 / 5) (1 / 5) x y ≠ 0 := by
      simp only [cdFxy]
      have : 0 < x ^ ((3 : ℝ) / 5 - 1) * (1 - y) ^ ((1 : ℝ) / 5 - 1) :=
        mul_pos (rpow_pos_of_pos hxI.1 _) (rpow_pos_of_pos (by linarith [hyI.2]) _)
      intro h; nlinarith
    have hyx0 : cdFxy (3 / 5) (1 / 5) y x ≠ 0 := by
      simp only [cdFxy]
      have : 0 < y ^ ((3 : ℝ) / 5 - 1) * (1 - x) ^ ((1 : ℝ) / 5 - 1) :=
        mul_pos (rpow_pos_of_pos hyI.1 _) (rpow_pos_of_pos (by linarith [hxI.2]) _)
      intro h; nlinarith
    simp only [linK]
    field_simp
    norm_num
  rw [hdet, hK12]
  -- `X = (1 − x)/x ≥ 1` and `Y = (1 − y)/y ≥ 10`, so `tr M > 101`
  have htr' : 101 < M.trace := by
    rw [htr, hJ1, hJ2, hK1, hK2]
    have hX : 1 ≤ (1 - x) / x := by rw [le_div_iff₀ hxI.1]; linarith [hx.2]
    have hY : 10 ≤ (1 - y) / y := by rw [le_div_iff₀ hyI.1]; linarith [hy.2]
    have e : ∀ u v : ℝ, 0 < u → 0 < v → u < 1 → v < 1 →
        (1 - u) * ((1 / 5 - 1) / (1 - v) + (3 / 5 - 1) / v) / (1 / 5) *
          ((1 - v) * ((1 / 5 - 1) / (1 - u) + (3 / 5 - 1) / u) / (1 / 5)) +
        -(3 / 5 * (1 - u) / (1 / 5 * u)) + -(3 / 5 * (1 - v) / (1 / 5 * v)) =
        16 + 5 * ((1 - u) / u) + 5 * ((1 - v) / v) + 4 * ((1 - u) / u) * ((1 - v) / v) :=
      fun u v hu hv hu1 hv1 => by
        have : 0 < 1 - u := by linarith
        have : 0 < 1 - v := by linarith
        field_simp
        ring
    rw [e y x hyI.1 hxI.1 hyI.2 hxI.2]
    nlinarith
  -- `p(1) = 1 − tr + 100 < 0 < p(0)`: one root in `(0, 1)`, one above `1`
  set s := M.trace
  have hd : 4 * 100 ≤ s ^ 2 := by nlinarith
  set q := Real.sqrt (s ^ 2 - 4 * 100)
  have hq : q ^ 2 = s ^ 2 - 4 * 100 := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * 100 := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s 100 r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hfact : (1 - (s - q) / 2) * (1 - (s + q) / 2) = 1 - s + 100 := by nlinarith
  have hqs : q < s := by
    have : q ^ 2 < s ^ 2 := by rw [hq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) this
  refine ⟨(s - q) / 2, (s + q) / 2, by linarith, ?_, ?_, hroot _ (Or.inr rfl),
    hroot _ (Or.inl rfl), fun μ hμ => ?_⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
    rcases hr with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear–quadratic problems: optimality of Euler paths

SLP §6.4, pp. 149–152. A quadratic return on `ℝˡ × ℝˡ`,
`F(x, y) = c₀ + F̄_x·x + F̄_y·y + ½x'F_xx x + x'F_xy y + ½y'F_yy y` (`lqF`), with `F_xx`, `F_yy`
symmetric, has partial derivatives `F_x = F̄_x + F_xx x + F_xy y` and
`F_y = F̄_y + F'_xy x + F_yy y` (`lqFx`, `lqFy`), and the Taylor expansion is exact
(`lqF_add`). Strict concavity makes the quadratic part negative definite (`lqQ_neg`), and
by compactness of the unit sphere uniformly so (`exists_lqQ_bound`).

* `lq_sufficient`: with `Γ(x) = ℝˡ` and `0 < β < 1`, a convergent path satisfying the Euler
  equations (2) is optimal. Plans with `u(x) > −∞` have `Σβᵗ|x_t|² < ∞`, which kills the
  boundary terms of `euler_sufficient`.
* `lq_unique`: an optimal plan with finite value is the only optimal plan (the midpoint of two
  optimal plans would do strictly better).
-/

open Set Filter Topology
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ} {P Q R : Matrix (Fin l) (Fin l) ℝ} {a b : Fin l → ℝ} {c₀ β : ℝ}

/-- The quadratic part `½u'F_xx u + u'F_xy v + ½v'F_yy v`. -/
noncomputable def lqQ (P Q R : Matrix (Fin l) (Fin l) ℝ) (u v : Fin l → ℝ) : ℝ :=
  u ⬝ᵥ (P *ᵥ u) / 2 + u ⬝ᵥ (Q *ᵥ v) + v ⬝ᵥ (R *ᵥ v) / 2

/-- The quadratic return `F(x, y) = c₀ + a·x + b·y + ½x'Px + x'Qy + ½y'Ry`. -/
noncomputable def lqF (P Q R : Matrix (Fin l) (Fin l) ℝ) (a b : Fin l → ℝ) (c₀ : ℝ)
    (p : (Fin l → ℝ) × (Fin l → ℝ)) : ℝ :=
  c₀ + a ⬝ᵥ p.1 + b ⬝ᵥ p.2 + lqQ P Q R p.1 p.2

/-- `F_x(x, y) = a + Px + Qy`. -/
def lqFx (P Q : Matrix (Fin l) (Fin l) ℝ) (a x y : Fin l → ℝ) : Fin l → ℝ := a + P *ᵥ x + Q *ᵥ y

/-- `F_y(x, y) = b + Q'x + Ry`. -/
def lqFy (Q R : Matrix (Fin l) (Fin l) ℝ) (b x y : Fin l → ℝ) : Fin l → ℝ := b + Qᵀ *ᵥ x + R *ᵥ y

theorem dot_sym (hP : Pᵀ = P) (u x : Fin l → ℝ) : u ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hP, dotProduct_comm]

theorem dot_transpose (Q : Matrix (Fin l) (Fin l) ℝ) (x v : Fin l → ℝ) :
    (Qᵀ *ᵥ x) ⬝ᵥ v = x ⬝ᵥ (Q *ᵥ v) := by
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]

/-- **The Taylor expansion of a quadratic is exact.** -/
theorem lqF_add (hP : Pᵀ = P) (hR : Rᵀ = R) (x y u v : Fin l → ℝ) :
    lqF P Q R a b c₀ (x + u, y + v) = lqF P Q R a b c₀ (x, y) + lqFx P Q a x y ⬝ᵥ u +
      lqFy Q R b x y ⬝ᵥ v + lqQ P Q R u v := by
  have e1 : (P *ᵥ x) ⬝ᵥ u = x ⬝ᵥ (P *ᵥ u) := by rw [dotProduct_comm, dot_sym hP]
  have e2 : (Q *ᵥ y) ⬝ᵥ u = u ⬝ᵥ (Q *ᵥ y) := dotProduct_comm _ _
  have e3 : (R *ᵥ y) ⬝ᵥ v = y ⬝ᵥ (R *ᵥ v) := by rw [dotProduct_comm, dot_sym hR]
  have e5 : u ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ u) := dot_sym hP u x
  have e6 : v ⬝ᵥ (R *ᵥ y) = y ⬝ᵥ (R *ᵥ v) := dot_sym hR v y
  simp only [lqF, lqQ, lqFx, lqFy, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    dot_transpose, e1, e2, e3, e5, e6]
  ring

theorem lqQ_smul (t : ℝ) (u v : Fin l → ℝ) :
    lqQ P Q R (t • u) (t • v) = t ^ 2 * lqQ P Q R u v := by
  simp only [lqQ, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem lqQ_zero_left : lqQ P Q R 0 0 = 0 := by simp [lqQ]

/-- **Strict concavity makes the quadratic part negative definite.** -/
theorem lqQ_neg (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) {u v : Fin l → ℝ}
    (huv : (u, v) ≠ 0) : lqQ P Q R u v < 0 := by
  have hne : (u, v) ≠ -(u, v) := fun h => huv (by
    have h2 : (2 : ℝ) • (u, v) = 0 := by
      rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero)
  have := hconc.2 (mem_univ (u, v)) (mem_univ (-(u, v))) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • (u, v) + (1 / 2 : ℝ) • -(u, v) = 0 := by
    rw [smul_neg, add_neg_cancel]
  rw [e] at this
  simp only [lqF, lqQ, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero,
    Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, Matrix.mulVec_zero,
    dotProduct_zero, smul_eq_mul] at this
  unfold lqQ
  linarith

/-- The quadratic part is continuous. -/
theorem continuous_lqQ : Continuous fun w : (Fin l → ℝ) × (Fin l → ℝ) => lqQ P Q R w.1 w.2 := by
  unfold lqQ
  fun_prop

/-- **Uniform negative definiteness**: `q(u, v) ≤ −m‖(u, v)‖²`. -/
theorem exists_lqQ_bound (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ P Q R u v < 0) :
    ∃ m > 0, ∀ u v : Fin l → ℝ, lqQ P Q R u v ≤ -m * ‖(u, v)‖ ^ 2 := by
  set φ : (Fin l → ℝ) × (Fin l → ℝ) → ℝ := fun w => lqQ P Q R w.1 w.2
  -- `φ(w) = ‖w‖²φ(w/‖w‖)`
  have hhom : ∀ w : (Fin l → ℝ) × (Fin l → ℝ), w ≠ 0 →
      φ w = ‖w‖ ^ 2 * φ (‖w‖⁻¹ • w) ∧ ‖w‖⁻¹ • w ∈ Metric.sphere 0 1 := fun w hw => by
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    refine ⟨?_, by simp [norm_smul, hn]⟩
    have := lqQ_smul (P := P) (Q := Q) (R := R) ‖w‖ (‖w‖⁻¹ • w).1 (‖w‖⁻¹ • w).2
    simp only [Prod.smul_fst, Prod.smul_snd, smul_smul, mul_inv_cancel₀ hn, one_smul] at this
    exact this
  by_cases hs : (Metric.sphere (0 : (Fin l → ℝ) × (Fin l → ℝ)) 1).Nonempty
  · obtain ⟨w₀, hw₀, hmax⟩ := (isCompact_sphere (0 : (Fin l → ℝ) × (Fin l → ℝ)) 1).exists_isMaxOn
      hs (continuous_lqQ (P := P) (Q := Q) (R := R)).continuousOn
    have hw₀0 : w₀ ≠ 0 := by
      intro h; rw [h] at hw₀; simp at hw₀
    refine ⟨-φ w₀, by linarith [hneg w₀.1 w₀.2 hw₀0], fun u v => ?_⟩
    by_cases hw : (u, v) = 0
    · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 hw; simp [lqQ_zero_left]
    · obtain ⟨e, hmem⟩ := hhom (u, v) hw
      have : φ (‖(u, v)‖⁻¹ • (u, v)) ≤ φ w₀ := hmax hmem
      change φ (u, v) ≤ _
      rw [e]
      have h2 : 0 ≤ ‖(u, v)‖ ^ 2 := sq_nonneg _
      nlinarith
  · refine ⟨1, one_pos, fun u v => ?_⟩
    by_cases hw : (u, v) = 0
    · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 hw; simp [lqQ_zero_left]
    · exact absurd ⟨_, (hhom (u, v) hw).2⟩ hs

/-- `|g·v| ≤ (Σ|gᵢ|)‖v‖` in the sup norm. -/
theorem abs_dot_le (g v : Fin l → ℝ) : |g ⬝ᵥ v| ≤ (∑ i, |g i|) * ‖v‖ := by
  rw [dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v i) (abs_nonneg _)

/-- **`F` is bounded above by a downward parabola**: `F(p) ≤ C − m‖p‖²`. -/
theorem exists_lqF_bound (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) :
    ∃ C, ∃ m > 0, ∀ p, lqF P Q R a b c₀ p ≤ C - m * ‖p‖ ^ 2 := by
  obtain ⟨m, hm, hq⟩ := exists_lqQ_bound (P := P) (Q := Q) (R := R)
    fun u v huv => lqQ_neg hconc huv
  set G := (∑ i, |a i|) + ∑ i, |b i|
  refine ⟨c₀ + G ^ 2 / (2 * m), m / 2, by linarith, fun p => ?_⟩
  have h1 : a ⬝ᵥ p.1 ≤ (∑ i, |a i|) * ‖p‖ :=
    (le_abs_self _).trans ((abs_dot_le _ _).trans (mul_le_mul_of_nonneg_left (norm_fst_le p)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)))
  have h2 : b ⬝ᵥ p.2 ≤ (∑ i, |b i|) * ‖p‖ :=
    (le_abs_self _).trans ((abs_dot_le _ _).trans (mul_le_mul_of_nonneg_left (norm_snd_le p)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)))
  have h3 := hq p.1 p.2
  have h4 : G * ‖p‖ ≤ m / 2 * ‖p‖ ^ 2 + G ^ 2 / (2 * m) := by
    have e : m / 2 * ‖p‖ ^ 2 + G ^ 2 / (2 * m) - G * ‖p‖ = (m * ‖p‖ - G) ^ 2 / (2 * m) := by
      field_simp; ring
    have : 0 ≤ (m * ‖p‖ - G) ^ 2 / (2 * m) := by positivity
    linarith
  simp only [lqF]
  simp only [G] at h4
  nlinarith

/-- **Assumption 4.2** holds for the quadratic return with `Γ(x) = ℝˡ`. -/
theorem lq_assumption42 (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    Assumption42 (fun _ : Fin l → ℝ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β := by
  obtain ⟨C, m, hm, hb⟩ := exists_lqF_bound hconc
  exact assumption42_of_bddAbove (M := C) (fun x y => (hb (x, y)).trans
    (by nlinarith [sq_nonneg ‖(x, y)‖])) hβ0 hβ1

/-- **A plan with `u(x) > −∞` has `βᵗ‖(x_t, x_{t+1})‖² → 0`.** -/
theorem tendsto_of_total_ne_bot (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀))
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → Fin l → ℝ}
    (hx : total (fun x y => lqF P Q R a b c₀ (x, y)) β x ≠ ⊥) :
    Tendsto (fun t => β ^ t * ‖(x t, x (t + 1))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, m, hm, hb⟩ := exists_lqF_bound hconc
  have h42 := lq_assumption42 (a := a) (b := b) (c₀ := c₀) hconc hβ0 hβ1
  have hlim := tendsto_total h42 (x₀ := x 0) (x := x) ⟨rfl, fun _ => mem_univ _⟩
  -- the partial sums are eventually above some real `r`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : EReal) < total (fun x y => lqF P Q R a b c₀ (x, y)) β x := by
    induction h : total (fun x y => lqF P Q R a b c₀ (x, y)) β x with
    | bot => exact absurd h hx
    | coe s => exact ⟨s - 1, EReal.coe_lt_coe_iff.2 (by linarith)⟩
    | top => exact ⟨0, EReal.coe_lt_top 0⟩
  have hev := hlim.eventually (lt_mem_nhds hr)
  set s : ℕ → ℝ := fun n => ∑ t ∈ Finset.range (n + 1), β ^ t * ‖(x t, x (t + 1))‖ ^ 2
  have hgeo : ∀ n, ∑ t ∈ Finset.range (n + 1), β ^ t * |C| ≤ |C| / (1 - β) := fun n => by
    have hb1 : 0 < 1 - β := by linarith
    rw [← Finset.sum_mul, geom_sum_eq (by linarith : β ≠ 1)]
    have e : (β ^ (n + 1) - 1) / (β - 1) = (1 - β ^ (n + 1)) / (1 - β) := by
      rw [div_eq_div_iff (by linarith) hb1.ne']; ring
    rw [e, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hb1]
    nlinarith [abs_nonneg C, pow_nonneg hβ0 (n + 1)]
  have hbound : ∀ n, partialSum (fun x y => lqF P Q R a b c₀ (x, y)) β x n ≤
      |C| / (1 - β) - m * s n := fun n => by
    simp only [partialSum, s, Finset.mul_sum]
    refine le_trans ?_ (sub_le_sub_right (hgeo n) _)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have := hb (x t, x (t + 1))
    have hβt := pow_nonneg hβ0 t
    nlinarith [le_abs_self C]
  -- so `s` is eventually, hence always, bounded
  have hmono : Monotone s := fun n n' hnn' => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega)) fun t _ _ => mul_nonneg (pow_nonneg hβ0 t)
      (sq_nonneg _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsb : ∀ n, s n ≤ (|C| / (1 - β) - r) / m := fun n => by
    have h1 := hN (max n N) (le_max_right _ _)
    have h2 := hbound (max n N)
    have h3 : r < partialSum (fun x y => lqF P Q R a b c₀ (x, y)) β x (max n N) :=
      EReal.coe_lt_coe_iff.1 h1
    rw [le_div_iff₀ hm]
    nlinarith [hmono (le_max_left n N)]
  have hsum : Summable fun t => β ^ t * ‖(x t, x (t + 1))‖ ^ 2 :=
    summable_of_sum_range_le (fun t => mul_nonneg (pow_nonneg hβ0 t) (sq_nonneg _))
      fun n => (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2
        (Nat.le_succ n)) fun t _ _ => mul_nonneg (pow_nonneg hβ0 t) (sq_nonneg _)).trans (hsb n)
  exact hsum.tendsto_atTop_zero

theorem lqQ_nonpos (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (u v : Fin l → ℝ) :
    lqQ P Q R u v ≤ 0 := by
  by_cases h : (u, v) = 0
  · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 h
    rw [lqQ_zero_left]
  · exact (lqQ_neg hconc h).le

theorem continuous_lqF : Continuous (lqF P Q R a b c₀) := by
  unfold lqF lqQ
  fun_prop

/-- The derivative `(u, v) ↦ g₁·u + g₂·v`. -/
noncomputable def lqD (g₁ g₂ : Fin l → ℝ) : ((Fin l → ℝ) × (Fin l → ℝ)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => g₁ ⬝ᵥ p.1 + g₂ ⬝ᵥ p.2
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, dotProduct_add]; ring
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul,
          RingHom.id_apply]
        ring }

theorem lqD_apply (g₁ g₂ : Fin l → ℝ) (p : (Fin l → ℝ) × (Fin l → ℝ)) :
    lqD g₁ g₂ p = g₁ ⬝ᵥ p.1 + g₂ ⬝ᵥ p.2 := rfl

/-- **A convergent Euler path is optimal.** With `Γ(x) = ℝˡ`, `0 < β < 1` and `F` strictly
concave, a path satisfying the Euler equations (2)
`F_y(x_t, x_{t+1}) + βF_x(x_{t+1}, x_{t+2}) = 0` and converging is optimal. -/
theorem lq_sufficient (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 < β) (hβ1 : β < 1)
    {xs : ℕ → Fin l → ℝ} {xbar : Fin l → ℝ}
    (heuler : ∀ t, lqFy Q R b (xs t) (xs (t + 1)) + β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) = 0)
    (hconv : Tendsto xs atTop (𝓝 xbar)) :
    total (fun x y => lqF P Q R a b c₀ (x, y)) β xs =
      vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β (xs 0) := by
  have h42 := lq_assumption42 (a := a) (b := b) (c₀ := c₀) hconc hβ0.le hβ1
  set D : ℕ → ((Fin l → ℝ) × (Fin l → ℝ)) →L[ℝ] ℝ := fun t =>
    lqD (lqFx P Q a (xs t) (xs (t + 1))) (lqFy Q R b (xs t) (xs (t + 1)))
  refine euler_sufficient (F := lqF P Q R a b c₀) (Γ := fun _ => univ) h42
    ⟨rfl, fun _ => mem_univ _⟩ D ?_ ?_ hβ0.le ?_
  · -- `F` lies below its tangent planes
    intro t x y _
    have := lqF_add hP hR (Q := Q) (a := a) (b := b) (c₀ := c₀) (xs t) (xs (t + 1)) (x - xs t)
      (y - xs (t + 1))
    rw [show xs t + (x - xs t) = x by abel, show xs (t + 1) + (y - xs (t + 1)) = y by abel]
      at this
    rw [this, lqD_apply]
    simp only [Prod.fst_sub, Prod.snd_sub]
    linarith [lqQ_nonpos hconc (x - xs t) (y - xs (t + 1))]
  · -- the Euler equations
    intro t v
    have h := congrArg (· ⬝ᵥ v) (heuler t)
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h
    simp only [Fy, Fx, D, lqD_apply, dotProduct_zero, zero_add, add_zero]
    exact h
  · -- the boundary terms vanish against plans with `u(x) > −∞`
    intro x _ hx
    have hg : Tendsto (fun t => ∑ i, |lqFx P Q a (xs t) (xs (t + 1)) i|) atTop
        (𝓝 (∑ i, |lqFx P Q a xbar xbar i|)) := by
      have hFx : Continuous fun p : (Fin l → ℝ) × (Fin l → ℝ) => lqFx P Q a p.1 p.2 :=
        (continuous_const.add (continuous_const.matrix_mulVec continuous_fst)).add
          (continuous_const.matrix_mulVec continuous_snd)
      have hc : Continuous fun p : (Fin l → ℝ) × (Fin l → ℝ) => ∑ i, |lqFx P Q a p.1 p.2 i| :=
        continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hFx).abs
      have hp : Tendsto (fun t => (xs t, xs (t + 1))) atTop (𝓝 (xbar, xbar)) :=
        hconv.prodMk_nhds (hconv.comp (tendsto_add_atTop_nat 1))
      have h := (hc.tendsto (xbar, xbar)).comp hp
      simp only [Function.comp_def] at h
      exact h
    obtain ⟨G, hG⟩ := hg.bddAbove_range
    obtain ⟨B, hB⟩ := hconv.norm.bddAbove_range
    have hpT := tendsto_of_total_ne_bot (a := a) (b := b) (c₀ := c₀) hconc hβ0.le hβ1 hx
    have hxT : Tendsto (fun T => β ^ (T + 1) * ‖x (T + 1)‖) atTop (𝓝 0) := by
      have hup : Tendsto (fun T => β * (β ^ T + β ^ T * ‖(x T, x (T + 1))‖ ^ 2)) atTop
          (𝓝 (β * (0 + 0))) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).add hpT |>.const_mul β
      rw [add_zero, mul_zero] at hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun T => mul_nonneg (pow_nonneg hβ0.le _) (norm_nonneg _)) fun T => ?_
      have h1 : ‖x (T + 1)‖ ≤ ‖(x T, x (T + 1))‖ := norm_snd_le (x T, x (T + 1))
      have h2 : ‖(x T, x (T + 1))‖ ≤ 1 + ‖(x T, x (T + 1))‖ ^ 2 := by
        nlinarith [sq_nonneg (‖(x T, x (T + 1))‖ - 1)]
      have hβT := pow_nonneg hβ0.le T
      have := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hβT hβ0.le)
      calc β ^ (T + 1) * ‖x (T + 1)‖ = β ^ T * β * ‖x (T + 1)‖ := by rw [pow_succ]
        _ ≤ β ^ T * β * (1 + ‖(x T, x (T + 1))‖ ^ 2) := this
        _ = _ := by ring
    set G' := max G 0
    refine ⟨fun T => G' * (B * β ^ (T + 1) + β ^ (T + 1) * ‖x (T + 1)‖), ?_, fun T => ?_⟩
    · have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
        (tendsto_add_atTop_nat 1)).const_mul B |>.add hxT |>.const_mul G'
      simpa [Function.comp_def] using this
    · simp only [Fx, D, lqD_apply, dotProduct_zero, add_zero]
      have hd := (le_abs_self _).trans (abs_dot_le (lqFx P Q a (xs (T + 1)) (xs (T + 1 + 1)))
        (xs (T + 1) - x (T + 1)))
      have hGT : ∑ i, |lqFx P Q a (xs (T + 1)) (xs (T + 1 + 1)) i| ≤ G' :=
        (hG ⟨T + 1, rfl⟩).trans (le_max_left _ _)
      have hn : ‖xs (T + 1) - x (T + 1)‖ ≤ B + ‖x (T + 1)‖ :=
        (norm_sub_le _ _).trans (add_le_add (hB ⟨T + 1, rfl⟩) le_rfl)
      have hG0 : 0 ≤ G' := le_max_right _ _
      have hβT := pow_nonneg hβ0.le (T + 1)
      have h3 : (∑ i, |lqFx P Q a (xs (T + 1)) (xs (T + 1 + 1)) i|) *
          ‖xs (T + 1) - x (T + 1)‖ ≤ G' * (B + ‖x (T + 1)‖) :=
        mul_le_mul hGT hn (norm_nonneg _) hG0
      nlinarith

/-- **The midpoint gains `−¼q(d)`**: with `d = (y, y') − (x, x')`,
`F(midpoint) = ½F(x, x') + ½F(y, y') − ¼q(d)`. -/
theorem lqF_midpoint (hP : Pᵀ = P) (hR : Rᵀ = R) (x x' y y' : Fin l → ℝ) :
    lqF P Q R a b c₀ (x + (1 / 2 : ℝ) • (y - x), x' + (1 / 2 : ℝ) • (y' - x')) =
      lqF P Q R a b c₀ (x, x') / 2 + lqF P Q R a b c₀ (y, y') / 2 -
        lqQ P Q R (y - x) (y' - x') / 4 := by
  have h1 := lqF_add hP hR (Q := Q) (a := a) (b := b) (c₀ := c₀) x x' ((1 / 2 : ℝ) • (y - x))
    ((1 / 2 : ℝ) • (y' - x'))
  have h2 := lqF_add hP hR (Q := Q) (a := a) (b := b) (c₀ := c₀) x x' (y - x) (y' - x')
  rw [show x + (y - x) = y by abel, show x' + (y' - x') = y' by abel] at h2
  rw [h1, h2, lqQ_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The optimal plan is unique.** If a convergent plan `x*` is optimal, every optimal plan
from `x₀ = x*₀` equals it: otherwise their midpoint would do strictly better. -/
theorem lq_unique (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 < β) (hβ1 : β < 1)
    {xs : ℕ → Fin l → ℝ} {xbar : Fin l → ℝ} (hconv : Tendsto xs atTop (𝓝 xbar))
    (hopt : total (fun x y => lqF P Q R a b c₀ (x, y)) β xs =
      vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β (xs 0))
    {y : ℕ → Fin l → ℝ} (hy0 : y 0 = xs 0)
    (hyopt : total (fun x y => lqF P Q R a b c₀ (x, y)) β y =
      vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β (xs 0)) : y = xs := by
  have h42 := lq_assumption42 (a := a) (b := b) (c₀ := c₀) hconc hβ0.le hβ1
  set Fc : (Fin l → ℝ) → (Fin l → ℝ) → ℝ := fun x y => lqF P Q R a b c₀ (x, y)
  -- the value of `x*` is finite: its terms are bounded by a geometric sequence
  have hFt : Tendsto (fun t => lqF P Q R a b c₀ (xs t, xs (t + 1))) atTop
      (𝓝 (lqF P Q R a b c₀ (xbar, xbar))) := by
    have hp : Tendsto (fun t => (xs t, xs (t + 1))) atTop (𝓝 (xbar, xbar)) :=
      hconv.prodMk_nhds (hconv.comp (tendsto_add_atTop_nat 1))
    have h := ((continuous_lqF (P := P) (Q := Q) (R := R) (a := a) (b := b) (c₀ := c₀)).tendsto
      (xbar, xbar)).comp hp
    simp only [Function.comp_def] at h
    exact h
  obtain ⟨K, hK⟩ := hFt.norm.bddAbove_range
  have hsum : Summable fun t => β ^ t * Fc (xs t) (xs (t + 1)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K)
      fun t => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hβ0.le]
    exact mul_le_mul_of_nonneg_left (hK ⟨t, rfl⟩) (pow_nonneg hβ0.le t)
  set ℓ := ∑' t, β ^ t * Fc (xs t) (xs (t + 1))
  have hxs : Tendsto (fun n => partialSum Fc β xs n) atTop (𝓝 ℓ) :=
    hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have htot : total Fc β xs = (ℓ : EReal) :=
    tendsto_nhds_unique (tendsto_total h42 ⟨rfl, fun _ => mem_univ _⟩)
      (EReal.tendsto_coe.2 hxs)
  have hys : Tendsto (fun n => partialSum Fc β y n) atTop (𝓝 ℓ) := by
    have := tendsto_total h42 (x₀ := xs 0) (x := y) ⟨hy0, fun _ => mem_univ _⟩
    rw [hyopt, ← hopt, htot] at this
    exact EReal.tendsto_coe.1 this
  -- a first date at which the plans differ
  by_contra hne
  obtain ⟨s, hs⟩ : ∃ s, y s ≠ xs s := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨t₀, rfl⟩ : ∃ t₀, s = t₀ + 1 := by
    rcases s with _ | t₀
    · exact absurd hy0 hs
    · exact ⟨t₀, rfl⟩
  have hd : (y t₀ - xs t₀, y (t₀ + 1) - xs (t₀ + 1)) ≠ 0 := fun h =>
    hs (sub_eq_zero.1 (Prod.mk_eq_zero.1 h).2)
  set δ := β ^ t₀ * (-(lqQ P Q R (y t₀ - xs t₀) (y (t₀ + 1) - xs (t₀ + 1)) / 4))
  have hδ : 0 < δ := mul_pos (pow_pos hβ0 t₀) (by linarith [lqQ_neg hconc hd])
  -- the midpoint plan
  set z : ℕ → Fin l → ℝ := fun t => xs t + (1 / 2 : ℝ) • (y t - xs t)
  have hz : z ∈ Feasible (fun _ => univ) (xs 0) :=
    ⟨by simp [z, hy0], fun _ => mem_univ _⟩
  have hzle : total Fc β z ≤ (ℓ : EReal) := by
    rw [← htot, hopt]; exact le_biSup _ hz
  have hgain : ∀ n, t₀ ≤ n →
      partialSum Fc β xs n / 2 + partialSum Fc β y n / 2 + δ ≤ partialSum Fc β z n := by
    intro n hn
    have hterm : ∀ t, β ^ t * Fc (z t) (z (t + 1)) = β ^ t * Fc (xs t) (xs (t + 1)) / 2 +
        β ^ t * Fc (y t) (y (t + 1)) / 2 +
        β ^ t * (-(lqQ P Q R (y t - xs t) (y (t + 1) - xs (t + 1)) / 4)) := fun t => by
      simp only [Fc, z, lqF_midpoint hP hR]; ring
    simp only [partialSum, hterm, Finset.sum_add_distrib, ← Finset.sum_div]
    have hsingle : δ ≤ ∑ t ∈ Finset.range (n + 1), β ^ t *
        (-(lqQ P Q R (y t - xs t) (y (t + 1) - xs (t + 1)) / 4)) :=
      Finset.single_le_sum (f := fun t => β ^ t *
        (-(lqQ P Q R (y t - xs t) (y (t + 1) - xs (t + 1)) / 4)))
        (fun t _ => mul_nonneg (pow_nonneg hβ0.le t)
          (by linarith [lqQ_nonpos hconc (y t - xs t) (y (t + 1) - xs (t + 1))]))
        (Finset.mem_range.2 (by omega))
    linarith
  have hlow : Tendsto (fun n => partialSum Fc β xs n / 2 + partialSum Fc β y n / 2 + δ) atTop
      (𝓝 (ℓ / 2 + ℓ / 2 + δ)) := ((hxs.div_const 2).add (hys.div_const 2)).add_const δ
  have hge : ((ℓ / 2 + ℓ / 2 + δ : ℝ) : EReal) ≤ total Fc β z :=
    le_of_tendsto_of_tendsto (EReal.tendsto_coe.2 hlow) (tendsto_total h42 hz)
      (eventually_atTop.2 ⟨t₀, fun n hn => EReal.coe_le_coe_iff.2 (hgain n hn)⟩)
  have := EReal.coe_le_coe_iff.1 (hge.trans hzle)
  linarith

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Global stability of linear–quadratic problems (Theorem 6.8)

SLP §6.4, pp. 151–153. The book diagonalizes `A` by a Jordan decomposition `A = B⁻¹ΛB` and
shows that the block `B₂₁` is nonsingular. Here the same steps run through the stable subspace
of `A` acting on `ℂ²ˡ` (`LinearSystems`):

* `finrank_stableSubspace`: the stable subspace has dimension equal to the number of
  characteristic roots (with multiplicity) inside the unit circle, since generalized
  eigenspaces are independent and each has dimension equal to the root's multiplicity.
* `hom_euler_eq_zero`: a solution `d` of the homogeneous Euler equations with `d₀ = 0` and
  `d_t → 0` is zero. With `g_t = d_t'(F_xx d_t + F_xy d_{t+1})`, the Euler equations give
  `2βᵗq(d_t, d_{t+1}) = βᵗg_t − βᵗ⁺¹g_{t+1}`; the sum telescopes to `0`, and `q < 0` off zero.
  This is the book's argument that `B₂₁` is nonsingular (two convergent Euler paths from the
  same `x₀` would both be optimal), without passing through optimality.
* `stable_inr_injective`: so the projection `(z₁, z₀) ↦ z₀` is injective on the stable subspace
  (the real and imaginary parts of a complex stable vector are real stable vectors). With
  `l` roots inside the unit circle the dimensions match, so it is onto: from every `z₀` there is
  a `z₁` with `(z₁, z₀)` stable (`exists_stable_start`).
* **Theorem 6.8** (`theorem_6_8`): from every `x₀` there is a unique optimal plan; it satisfies
  the Euler equations (2) and converges to `x̄`.
-/

open Set Filter Topology Module
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ} {P Q R : Matrix (Fin l) (Fin l) ℝ} {a b : Fin l → ℝ} {c₀ β : ℝ}

/-! ### The dimension of the stable subspace -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The generalized eigenspaces are independent, so their dimensions add. -/
theorem finrank_biSup_maxGenEigenspace (f : Module.End ℂ V) (T : Finset ℂ) :
    finrank ℂ ↥(⨆ μ ∈ T, f.maxGenEigenspace μ) = ∑ μ ∈ T, finrank ℂ (f.maxGenEigenspace μ) := by
  refine Finset.induction_on T (by simp) ?_
  intro a T ha ih
  rw [Finset.sum_insert ha, ← ih, Finset.iSup_insert]
  have hdis : Disjoint (f.maxGenEigenspace a) (⨆ μ ∈ T, f.maxGenEigenspace μ) := by
    have := (Module.End.independent_maxGenEigenspace f).disjoint_biSup (y := (T : Set ℂ))
      (by simpa using ha)
    simpa using this
  have := Submodule.finrank_sup_add_finrank_inf_eq (f.maxGenEigenspace a)
    (⨆ μ ∈ T, f.maxGenEigenspace μ)
  rw [hdis.eq_bot, finrank_bot, add_zero] at this
  exact this

/-- **The dimension of the stable subspace** is the number of characteristic roots, with
multiplicity, inside the unit circle. -/
theorem finrank_stableSubspace (f : Module.End ℂ V) :
    finrank ℂ (stableSubspace f) = (f.charpoly.roots.filter fun μ => ‖μ‖ < 1).card := by
  set T := (f.charpoly.roots.filter fun μ => ‖μ‖ < 1).toFinset
  have hT : ∀ μ, μ ∈ T ↔ μ ∈ f.charpoly.roots ∧ ‖μ‖ < 1 := fun μ => by
    simp [T]
  have hbot : ∀ μ, μ ∉ f.charpoly.roots → f.maxGenEigenspace μ = ⊥ := fun μ hμ => by
    rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq]
    exact Polynomial.rootMultiplicity_eq_zero fun h =>
      hμ ((Polynomial.mem_roots f.charpoly_monic.ne_zero).2 h)
  have heq : stableSubspace f = ⨆ μ ∈ T, f.maxGenEigenspace μ := by
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => ?_)
    · by_cases hr : μ ∈ f.charpoly.roots
      · exact le_biSup (fun μ => f.maxGenEigenspace μ) ((hT μ).2 ⟨hr, hμ⟩)
      · rw [hbot μ hr]; exact bot_le
    · exact le_biSup (fun μ => f.maxGenEigenspace μ) (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from
        ((hT μ).1 hμ).2)
  rw [heq, finrank_biSup_maxGenEigenspace, ← Multiset.toFinset_sum_count_eq]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [LinearMap.finrank_maxGenEigenspace_eq,
    Multiset.count_filter_of_pos (p := fun μ : ℂ => ‖μ‖ < 1) ((hT μ).1 hμ).2,
    Polynomial.count_roots]

/-! ### Real and imaginary parts -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem re_cplxEnd_apply (A : Matrix ι ι ℝ) (V : ι → ℂ) (i : ι) :
    (cplxEnd A V i).re = (A *ᵥ fun j => (V j).re) i := by
  simp [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Complex.re_sum]

theorem im_cplxEnd_apply (A : Matrix ι ι ℝ) (V : ι → ℂ) (i : ι) :
    (cplxEnd A V i).im = (A *ᵥ fun j => (V j).im) i := by
  simp [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Complex.im_sum]

theorem re_cplxEnd_pow (A : Matrix ι ι ℝ) (t : ℕ) (W : ι → ℂ) (i : ι) :
    ((cplxEnd A ^ t) W i).re = ((A ^ t) *ᵥ fun j => (W j).re) i := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, re_cplxEnd_apply, pow_succ', ← Matrix.mulVec_mulVec,
      show (fun j => ((cplxEnd A ^ t) W j).re) = (A ^ t) *ᵥ (fun j => (W j).re) from funext ih]

theorem im_cplxEnd_pow (A : Matrix ι ι ℝ) (t : ℕ) (W : ι → ℂ) (i : ι) :
    ((cplxEnd A ^ t) W i).im = ((A ^ t) *ᵥ fun j => (W j).im) i := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, im_cplxEnd_apply, pow_succ', ← Matrix.mulVec_mulVec,
      show (fun j => ((cplxEnd A ^ t) W j).im) = (A ^ t) *ᵥ (fun j => (W j).im) from funext ih]

/-- The real part of a complex stable vector is a real stable vector. -/
theorem tendsto_re_of_stable (A : Matrix ι ι ℝ) {W : ι → ℂ}
    (hW : W ∈ stableSubspace (cplxEnd A)) :
    Tendsto (fun t => (A ^ t) *ᵥ fun j => (W j).re) atTop (𝓝 0) := by
  have h := (tendsto_iff_mem_stable (cplxEnd A) W).2 hW
  rw [tendsto_pi_nhds] at h ⊢
  intro i
  have := (Complex.continuous_re.tendsto 0).comp (h i)
  simpa [Function.comp_def, re_cplxEnd_pow] using this

theorem tendsto_im_of_stable (A : Matrix ι ι ℝ) {W : ι → ℂ}
    (hW : W ∈ stableSubspace (cplxEnd A)) :
    Tendsto (fun t => (A ^ t) *ᵥ fun j => (W j).im) atTop (𝓝 0) := by
  have h := (tendsto_iff_mem_stable (cplxEnd A) W).2 hW
  rw [tendsto_pi_nhds] at h ⊢
  intro i
  have := (Complex.continuous_im.tendsto 0).comp (h i)
  simpa [Function.comp_def, im_cplxEnd_pow] using this

/-! ### The Euler equations in stacked form -/

theorem eulerA_mulVec_inl (V : Fin l ⊕ Fin l → ℝ) (i : Fin l) :
    (eulerA P Q R β *ᵥ V) (Sum.inl i) =
      (eulerJ P Q R β *ᵥ (V ∘ Sum.inl) + eulerK Q β *ᵥ (V ∘ Sum.inr)) i := by
  simp [eulerA, Matrix.fromBlocks_mulVec]

theorem eulerA_mulVec_inr (V : Fin l ⊕ Fin l → ℝ) (i : Fin l) :
    (eulerA P Q R β *ᵥ V) (Sum.inr i) = V (Sum.inl i) := by
  simp [eulerA, Matrix.fromBlocks_mulVec]

/-- Along an orbit `V_t = AᵗZ`, the second blocks `d_t` solve `d_{t+2} = Jd_{t+1} + Kd_t`. -/
theorem orbit_rec (Z : Fin l ⊕ Fin l → ℝ) (t : ℕ) :
    (fun i => ((eulerA P Q R β ^ (t + 2)) *ᵥ Z) (Sum.inr i)) =
      eulerJ P Q R β *ᵥ (fun i => ((eulerA P Q R β ^ (t + 1)) *ᵥ Z) (Sum.inr i)) +
        eulerK Q β *ᵥ (fun i => ((eulerA P Q R β ^ t) *ᵥ Z) (Sum.inr i)) := by
  have hs : ∀ n, (eulerA P Q R β ^ (n + 1)) *ᵥ Z = eulerA P Q R β *ᵥ ((eulerA P Q R β ^ n) *ᵥ Z) :=
    fun n => by rw [pow_succ', ← Matrix.mulVec_mulVec]
  have h1 : (fun i => ((eulerA P Q R β ^ (t + 1)) *ᵥ Z) (Sum.inr i)) =
      (eulerA P Q R β ^ t *ᵥ Z) ∘ Sum.inl := by
    funext i; rw [hs, eulerA_mulVec_inr]; rfl
  funext i
  rw [h1]
  change ((eulerA P Q R β ^ (t + 1 + 1)) *ᵥ Z) (Sum.inr i) = _
  rw [hs (t + 1), eulerA_mulVec_inr, hs t, eulerA_mulVec_inl]
  rfl

/-- The recursion `z₂ = Jz₁ + Kz₀` is the homogeneous Euler equation
`F'_xy z₀ + F_yy z₁ + β(F_xx z₁ + F_xy z₂) = 0`. -/
theorem euler_of_rec (hQ : Q.det ≠ 0) (hβ : β ≠ 0) {z₀ z₁ z₂ : Fin l → ℝ}
    (h : z₂ = eulerJ P Q R β *ᵥ z₁ + eulerK Q β *ᵥ z₀) :
    Qᵀ *ᵥ z₀ + R *ᵥ z₁ + β • (P *ᵥ z₁ + Q *ᵥ z₂) = 0 := by
  rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, fxy_mul_eulerJ hQ,
    fxy_mul_eulerK hQ]
  simp only [Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, smul_add,
    smul_neg, smul_smul, mul_inv_cancel₀ hβ, inv_mul_cancel₀ hβ, one_smul]
  abel

/-- **Two convergent Euler paths from the same point coincide**: a solution of the homogeneous
Euler equations with `d₀ = 0` and `d_t → 0` is zero. -/
theorem hom_euler_eq_zero (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 < β)
    (hβ1 : β < 1) {d : ℕ → Fin l → ℝ} (hd0 : d 0 = 0) (hdt : Tendsto d atTop (𝓝 0))
    (he : ∀ t, Qᵀ *ᵥ d t + R *ᵥ d (t + 1) + β • (P *ᵥ d (t + 1) + Q *ᵥ d (t + 2)) = 0) :
    ∀ t, d t = 0 := by
  set g : ℕ → ℝ := fun t => d t ⬝ᵥ (P *ᵥ d t + Q *ᵥ d (t + 1))
  set q : ℕ → ℝ := fun t => lqQ P Q R (d t) (d (t + 1))
  -- `2q_t = g_t − βg_{t+1}`
  have hkey : ∀ t, 2 * q t = g t - β * g (t + 1) := fun t => by
    have h := congrArg (d (t + 1) ⬝ᵥ ·) (he t)
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] at h
    have e : d (t + 1) ⬝ᵥ (Qᵀ *ᵥ d t) = d t ⬝ᵥ (Q *ᵥ d (t + 1)) := by
      rw [dotProduct_comm, dot_transpose]
    simp only [q, g, lqQ, dotProduct_add]
    rw [e] at h
    linarith
  -- `2Σ_{t<N} βᵗq_t = −β^N g_N`
  set S : ℕ → ℝ := fun N => ∑ t ∈ Finset.range N, β ^ t * q t
  have hg0 : g 0 = 0 := by simp [g, hd0]
  have hS : ∀ N, 2 * S N = -(β ^ N * g N) := fun N => by
    induction N with
    | zero => simp [S, hg0]
    | succ N ih =>
      simp only [S, Finset.sum_range_succ, mul_add] at ih ⊢
      rw [ih, show 2 * (β ^ N * q N) = β ^ N * (2 * q N) by ring, hkey, pow_succ]
      ring
  have hgt : Tendsto g atTop (𝓝 0) := by
    have hc : Continuous fun p : (Fin l → ℝ) × (Fin l → ℝ) => p.1 ⬝ᵥ (P *ᵥ p.1 + Q *ᵥ p.2) := by
      unfold dotProduct; fun_prop
    have hp : Tendsto (fun t => (d t, d (t + 1))) atTop (𝓝 (0, 0)) :=
      hdt.prodMk_nhds (hdt.comp (tendsto_add_atTop_nat 1))
    have h := (hc.tendsto (0, 0)).comp hp
    simp only [Function.comp_def, Matrix.mulVec_zero, add_zero, dotProduct_zero] at h
    exact h
  have hSt : Tendsto S atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul hgt).neg.div_const 2
    simp only [mul_zero, neg_zero, zero_div] at h
    refine h.congr fun N => ?_
    linarith [hS N]
  have hq : ∀ t, q t ≤ 0 := fun t => lqQ_nonpos hconc _ _
  have hanti : Antitone S := antitone_nat_of_succ_le fun N => by
    simp only [S, Finset.sum_range_succ]
    nlinarith [hq N, pow_pos hβ0 N]
  have hS0 : ∀ N, S N = 0 := fun N => by
    have h1 := hanti.le_of_tendsto hSt N
    have h2 : S N ≤ 0 := Finset.sum_nonpos fun t _ =>
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0.le t) (hq t)
    linarith
  have hq0 : ∀ t, q t = 0 := fun t => by
    have h := hS0 (t + 1)
    simp only [S, Finset.sum_range_succ] at h
    have h' := hS0 t
    simp only [S] at h'
    rw [h', zero_add] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero t hβ0.ne')
  have hpair : ∀ t, (d t, d (t + 1)) = 0 := fun t => by
    by_contra hne
    exact (lqQ_neg hconc hne).ne (hq0 t)
  intro t
  rcases t with _ | t
  · exact hd0
  · exact (Prod.mk_eq_zero.1 (hpair t)).2

/-- **A real stable vector with zero second block is zero.** -/
theorem stable_real_inr_zero (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀))
    (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : Q.det ≠ 0) {Z : Fin l ⊕ Fin l → ℝ}
    (hZ : ∀ i, Z (Sum.inr i) = 0)
    (ht : Tendsto (fun t => (eulerA P Q R β ^ t) *ᵥ Z) atTop (𝓝 0)) : Z = 0 := by
  set d : ℕ → Fin l → ℝ := fun t i => ((eulerA P Q R β ^ t) *ᵥ Z) (Sum.inr i)
  have hd0 : d 0 = 0 := by funext i; simp [d, hZ]
  have hdt : Tendsto d atTop (𝓝 0) := by
    rw [tendsto_pi_nhds] at ht ⊢
    exact fun i => ht (Sum.inr i)
  have hzero := hom_euler_eq_zero (P := P) (Q := Q) (R := R) hconc hβ0 hβ1 hd0 hdt
    fun t => euler_of_rec hQ hβ0.ne' (orbit_rec Z t)
  have h1 : ∀ i, Z (Sum.inl i) = 0 := fun i => by
    have := congrFun (hzero 1) i
    simp only [d, pow_one, eulerA_mulVec_inr] at this
    exact this
  funext j
  rcases j with i | i
  · exact h1 i
  · exact hZ i

/-- **A complex stable vector with zero second block is zero.** -/
theorem stable_inr_zero (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀))
    (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : Q.det ≠ 0) {W : Fin l ⊕ Fin l → ℂ}
    (hW : W ∈ stableSubspace (cplxEnd (eulerA P Q R β))) (h0 : ∀ i, W (Sum.inr i) = 0) :
    W = 0 := by
  have hre := stable_real_inr_zero hconc hβ0 hβ1 hQ (Z := fun j => (W j).re)
    (fun i => by simp [h0 i]) (tendsto_re_of_stable _ hW)
  have him := stable_real_inr_zero hconc hβ0 hβ1 hQ (Z := fun j => (W j).im)
    (fun i => by simp [h0 i]) (tendsto_im_of_stable _ hW)
  funext j
  exact Complex.ext (congrFun hre j) (congrFun him j)

/-- **From every `z₀` there is a `z₁` with `(z₁, z₀)` in the stable subspace**, when `A` has `l`
characteristic roots inside the unit circle. This is the book's `B₂₁` nonsingular. -/
theorem exists_stable_start (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀))
    (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : Q.det ≠ 0)
    (hroots : (((eulerA P Q R β).charpoly.map Complex.ofRealHom).roots.filter
      fun μ => ‖μ‖ < 1).card = l) (z₀ : Fin l → ℝ) :
    ∃ z₁ : Fin l → ℝ,
      Tendsto (fun t => (eulerA P Q R β ^ t) *ᵥ Sum.elim z₁ z₀) atTop (𝓝 0) := by
  set f := cplxEnd (eulerA P Q R β)
  set S := stableSubspace f
  set proj : S →ₗ[ℂ] (Fin l → ℂ) := (LinearMap.funLeft ℂ ℂ Sum.inr).comp S.subtype
  have hcp : LinearMap.charpoly f = (eulerA P Q R β).charpoly.map Complex.ofRealHom := by
    simp only [f, cplxEnd]
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  have hdim : finrank ℂ S = finrank ℂ (Fin l → ℂ) := by
    rw [Module.finrank_fin_fun, finrank_stableSubspace, hcp, hroots]
  have hinj : Function.Injective proj := by
    refine (injective_iff_map_eq_zero proj).2 fun w hw => Subtype.ext ?_
    exact stable_inr_zero hconc hβ0 hβ1 hQ w.2 fun i => congrFun hw i
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    (cplx z₀)
  refine ⟨fun i => ((w : Fin l ⊕ Fin l → ℂ) (Sum.inl i)).re, ?_⟩
  have e : Sum.elim (fun i => ((w : Fin l ⊕ Fin l → ℂ) (Sum.inl i)).re) z₀ =
      fun j => ((w : Fin l ⊕ Fin l → ℂ) j).re := by
    funext j
    rcases j with i | i
    · rfl
    · have := congrFun hw i
      simp only [proj, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.funLeft_apply,
        cplx] at this
      simp [this]
  rw [e]
  exact tendsto_re_of_stable _ w.2

/-! ### Theorem 6.8 -/

/-- The stationary point `x̄ = −(F'_xy + F_yy + βF_xx + βF_xy)⁻¹(F̄_y + βF̄_x)`. -/
noncomputable def lqBar (P Q R : Matrix (Fin l) (Fin l) ℝ) (a b : Fin l → ℝ) (β : ℝ) :
    Fin l → ℝ :=
  -((Qᵀ + R + β • P + β • Q)⁻¹ *ᵥ (b + β • a))

theorem lqBar_stationary (hS : (Qᵀ + R + β • P + β • Q).det ≠ 0) :
    lqFy Q R b (lqBar P Q R a b β) (lqBar P Q R a b β) +
      β • lqFx P Q a (lqBar P Q R a b β) (lqBar P Q R a b β) = 0 := by
  have e : ∀ x, lqFy Q R b x x + β • lqFx P Q a x x =
      (b + β • a) + (Qᵀ + R + β • P + β • Q) *ᵥ x := fun x => by
    simp only [lqFy, lqFx, Matrix.add_mulVec, Matrix.smul_mulVec, smul_add]
    abel
  rw [e, lqBar, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hS), Matrix.one_mulVec, add_neg_cancel]

/-- **Theorem 6.8.** Let `F` be a strictly concave quadratic on `ℝˡ × ℝˡ`, `Γ(x) = ℝˡ`,
`0 < β < 1`, with `F_xy` and `F'_xy + F_yy + βF_xx + βF_xy` nonsingular, and suppose `A` has `l`
characteristic roots (with multiplicity) inside the unit circle. Then from every `x₀` there is a
unique optimal plan; it satisfies the Euler equations (2) and converges to `x̄`. -/
theorem theorem_6_8 (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hQ : Q.det ≠ 0) (hS : (Qᵀ + R + β • P + β • Q).det ≠ 0)
    (hroots : (((eulerA P Q R β).charpoly.map Complex.ofRealHom).roots.filter
      fun μ => ‖μ‖ < 1).card = l) (x₀ : Fin l → ℝ) :
    ∃ xs : ℕ → Fin l → ℝ, xs 0 = x₀ ∧
      total (fun x y => lqF P Q R a b c₀ (x, y)) β xs =
        vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β x₀ ∧
      (∀ t, lqFy Q R b (xs t) (xs (t + 1)) + β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) = 0) ∧
      Tendsto xs atTop (𝓝 (lqBar P Q R a b β)) ∧
      ∀ y : ℕ → Fin l → ℝ, y 0 = x₀ →
        total (fun x y => lqF P Q R a b c₀ (x, y)) β y =
          vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β x₀ → y = xs := by
  set xbar := lqBar P Q R a b β
  obtain ⟨z₁, hz⟩ := exists_stable_start hconc hβ0 hβ1 hQ hroots (x₀ - xbar)
  set Z := Sum.elim z₁ (x₀ - xbar)
  set z : ℕ → Fin l → ℝ := fun t i => ((eulerA P Q R β ^ t) *ᵥ Z) (Sum.inr i)
  set xs : ℕ → Fin l → ℝ := fun t => xbar + z t
  have hx0 : xs 0 = x₀ := by
    funext i; simp [xs, z, Z, xbar]
  have hzt : Tendsto z atTop (𝓝 0) := by
    rw [tendsto_pi_nhds] at hz ⊢
    exact fun i => hz (Sum.inr i)
  have hconv : Tendsto xs atTop (𝓝 xbar) := by
    have := hzt.const_add xbar
    rwa [add_zero] at this
  have heuler : ∀ t, lqFy Q R b (xs t) (xs (t + 1)) +
      β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) = 0 := fun t => by
    have hhom := euler_of_rec hQ hβ0.ne' (orbit_rec (P := P) (Q := Q) (R := R) (β := β) Z t)
    have e : lqFy Q R b (xs t) (xs (t + 1)) + β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) =
        (lqFy Q R b xbar xbar + β • lqFx P Q a xbar xbar) +
          (Qᵀ *ᵥ z t + R *ᵥ z (t + 1) + β • (P *ᵥ z (t + 1) + Q *ᵥ z (t + 2))) := by
      simp only [xs, lqFy, lqFx, Matrix.mulVec_add, smul_add]
      abel
    rw [e, lqBar_stationary hS, zero_add]
    exact hhom
  have hopt := lq_sufficient (c₀ := c₀) hP hR hconc hβ0 hβ1 heuler hconv
  rw [hx0] at hopt
  refine ⟨xs, hx0, hopt, heuler, hconv, fun y hy0 hyopt => ?_⟩
  rw [← hx0] at hy0 hyopt hopt
  exact lq_unique hP hR hconc hβ0 hβ1 hconv hopt hy0 hyopt

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A firm with adjustment costs (Exercise 6.8)

SLP §6.5, pp. 158–159. The firm of §5.9 (`AdjustmentCosts`):
`v(k) = max_y {pf(k) − c[y − (1 − δ)k] + βv(y)}`, `β = 1/(1 + r)`, on the compact state space
`[0, K]` used there.

* `orbit_tendsto_of_crossing` (the method of §6.1): if `g` is continuous and nondecreasing on
  an interval it maps into itself, with a fixed point `k̄`, `g(k) > k` below `k̄` and `g(k) < k`
  above, then every orbit converges monotonically to `k̄`.
* **Exercise 6.8a** (`ex_6_8a_unique`, `ex_6_8`): an interior stationary point satisfies
  `c'(δk̄)(1 − β(1 − δ)) = βpf'(k̄)`, that is `(r + δ)c'(δk̄) = pf'(k̄)`. The left side rises and
  the right side falls in `k̄`, so there is at most one.
* **Exercise 6.8b** (`ex_6_8`): with `f(0) = 0`, `f'(0+) = ∞`, `c(0) = 0`, `c` nondecreasing and
  strictly convex, and `K` beyond the steady state (`βpf'(K) < c'(δK)(1 − β(1 − δ))`):
  `g(0) > 0` (investing at `k = 0` pays, because `f(ε)/ε → ∞`), `g(K) < K` (a first-order
  argument at the upper end), so `g` has exactly one fixed point `k̄`, interior, and from every
  `k₀ ∈ [0, K]` capital converges monotonically to `k̄`.
* **Exercise 6.8c** (`ex_6_8c`): at `k̄`, `F_xx = pf'' − (1 − δ)²c''`, `F_xy = (1 − δ)c''`,
  `F_yy = −c''`. With `f'' ≤ 0` and `c'' > 0` the characteristic roots of the linearized Euler
  equation are real, one in `(0, 1)` and one above `1` (`p(1) = −[δ(1 − β(1 − δ))c'' − βpf'']
  /(β(1 − δ)c'') < 0`), so `k̄` is saddle-path stable (`roots_split`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

/-! ### Monotone convergence -/

/-- **The method of §6.1.** -/
theorem orbit_tendsto_of_crossing {g : ℝ → ℝ} {lo hi ks : ℝ}
    (hgc : ContinuousOn g (Icc lo hi)) (hgm : MonotoneOn g (Icc lo hi))
    (hmaps : MapsTo g (Icc lo hi) (Icc lo hi)) (hks : ks ∈ Icc lo hi) (hfix : g ks = ks)
    (hbelow : ∀ k ∈ Icc lo hi, k < ks → k < g k) (habove : ∀ k ∈ Icc lo hi, ks < k → g k < k)
    {k₀ : ℝ} (hk₀ : k₀ ∈ Icc lo hi) :
    (Monotone (fun t => g^[t] k₀) ∨ Antitone (fun t => g^[t] k₀)) ∧
      Tendsto (fun t => g^[t] k₀) atTop (𝓝 ks) := by
  set x : ℕ → ℝ := fun t => g^[t] k₀
  have hstep : ∀ t, x (t + 1) = g (x t) := fun t => Function.iterate_succ_apply' g t k₀
  have hmem : ∀ t, x t ∈ Icc lo hi := fun t => by
    induction t with
    | zero => exact hk₀
    | succ t ih => rw [hstep]; exact hmaps ih
  -- a limit `L` of the orbit is a fixed point
  have hfixL : ∀ L ∈ Icc lo hi, Tendsto x atTop (𝓝 L) → g L = L := fun L hL hlim => by
    have h1 : Tendsto (fun t => g (x t)) atTop (𝓝 (g L)) :=
      (hgc L hL).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
    have h2 : Tendsto (fun t => g (x t)) atTop (𝓝 L) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      simp only [Function.comp_def, hstep] at this
      exact this
    exact tendsto_nhds_unique h1 h2
  rcases le_or_gt k₀ ks with hle | hgt
  · have hub : ∀ t, x t ≤ ks := fun t => by
      induction t with
      | zero => exact hle
      | succ t ih => rw [hstep, ← hfix]; exact hgm (hmem t) hks ih
    have hmono : Monotone x := monotone_nat_of_le_succ fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hub t) with he | hlt
      · rw [he, hfix]
      · exact (hbelow _ (hmem t) hlt).le
    have hbdd : BddAbove (range x) := ⟨ks, by rintro _ ⟨t, rfl⟩; exact hub t⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hL : (⨆ t, x t) ∈ Icc lo hi := ⟨(hmem 0).1.trans (le_ciSup hbdd 0),
      (ciSup_le hub).trans hks.2⟩
    have hgL := hfixL _ hL hlim
    have heq : (⨆ t, x t) = ks := by
      by_contra hne
      have hlt : (⨆ t, x t) < ks := lt_of_le_of_ne (ciSup_le hub) hne
      have := hbelow _ hL hlt
      rw [hgL] at this
      exact lt_irrefl _ this
    rw [heq] at hlim
    exact ⟨Or.inl hmono, hlim⟩
  · have hlb : ∀ t, ks ≤ x t := fun t => by
      induction t with
      | zero => exact hgt.le
      | succ t ih => rw [hstep, ← hfix]; exact hgm hks (hmem t) ih
    have hanti : Antitone x := antitone_nat_of_succ_le fun t => by
      rw [hstep]
      rcases eq_or_lt_of_le (hlb t) with he | hlt
      · rw [← he, hfix]
      · exact (habove _ (hmem t) hlt).le
    have hbdd : BddBelow (range x) := ⟨ks, by rintro _ ⟨t, rfl⟩; exact hlb t⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hL : (⨅ t, x t) ∈ Icc lo hi := ⟨hks.1.trans (le_ciInf hlb),
      (ciInf_le hbdd 0).trans (hmem 0).2⟩
    have hgL := hfixL _ hL hlim
    have heq : (⨅ t, x t) = ks := by
      by_contra hne
      have hlt : ks < (⨅ t, x t) := lt_of_le_of_ne (le_ciInf hlb) (Ne.symm hne)
      have := habove _ hL hlt
      rw [hgL] at this
      exact lt_irrefl _ this
    rw [heq] at hlim
    exact ⟨Or.inr hanti, hlim⟩

/-! ### Saddle-path roots -/

/-- If `p > 0` and `1 − s + p < 0`, the roots of `λ² − sλ + p` are real, one in `(0, 1)` and one
greater than `1`. -/
theorem roots_split {s p : ℝ} (hp : 0 < p) (h1 : 1 - s + p < 0) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ < 1 ∧ 1 < μ₂ ∧ quadRoot s p μ₁ ∧ quadRoot s p μ₂ ∧
      ∀ μ, quadRoot s p μ → μ = μ₁ ∨ μ = μ₂ := by
  have hd : 4 * p ≤ s ^ 2 := by nlinarith [sq_nonneg (1 - p)]
  set q := Real.sqrt (s ^ 2 - 4 * p)
  have hq : q ^ 2 = s ^ 2 - 4 * p := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * p := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s p r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hfact : (1 - (s - q) / 2) * (1 - (s + q) / 2) = 1 - s + p := by nlinarith
  have hqs : q < s := by
    have : q ^ 2 < s ^ 2 := by rw [hq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) this
  refine ⟨(s - q) / 2, (s + q) / 2, by linarith, ?_, ?_, hroot _ (Or.inr rfl),
    hroot _ (Or.inl rfl), fun μ hμ => ?_⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
    rcases hr with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- **Exercise 6.8c.** With `F_xx = pf'' − (1 − δ)²c''`, `F_xy = (1 − δ)c''`, `F_yy = −c''`,
`f'' ≤ 0 < c''`, `p > 0`, `0 < β < 1` and `0 < δ < 1`, the characteristic roots of the
linearized Euler equation, `λ² − Jλ + 1/β` with `J = −(F_yy + βF_xx)/(βF_xy)`, are real, one in
`(0, 1)` and one above `1`. -/
theorem ex_6_8c {p β δ f₂ c₂ : ℝ} (hp : 0 < p) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hf₂ : f₂ ≤ 0) (hc₂ : 0 < c₂) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ < 1 ∧ 1 < μ₂ ∧
      quadRoot (-(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂))) (1 / β) μ₁ ∧
      quadRoot (-(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂))) (1 / β) μ₂ ∧
      ∀ μ, quadRoot (-(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂))) (1 / β) μ →
        μ = μ₁ ∨ μ = μ₂ := by
  refine roots_split (by positivity) ?_
  have hD : 0 < β * ((1 - δ) * c₂) := mul_pos hβ0 (mul_pos (by linarith) hc₂)
  -- `p(1)·β(1 − δ)c'' = −δ(1 − β(1 − δ))c'' + βpf'' < 0`
  have e : 1 - -(-c₂ + β * (p * f₂ - (1 - δ) ^ 2 * c₂)) / (β * ((1 - δ) * c₂)) + 1 / β =
      (-(δ * (1 - β * (1 - δ)) * c₂) + β * p * f₂) / (β * ((1 - δ) * c₂)) := by
    have h1δ : (1 - δ) ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  refine div_neg_of_neg_of_pos ?_ hD
  have h1 : 0 < 1 - β * (1 - δ) := by nlinarith
  have h2 : β * p * f₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hf₂
  have h3 : 0 < δ * (1 - β * (1 - δ)) * c₂ := by positivity
  linarith

/-! ### The firm -/

variable {f c f' c' : ℝ → ℝ} {p δ β K : ℝ}

/-- The hypotheses of Exercise 6.8 on `[0, K]`, on top of those of Exercise 5.9b. -/
structure FirmDyn (f c f' c' : ℝ → ℝ) (p δ β K : ℝ) : Prop where
  adj : AdjHyp f c p δ β K
  f_zero : f 0 = 0
  f_deriv : ∀ k, 0 < k → HasDerivAt f (f' k) k
  inada : Tendsto f' (𝓝[>] 0) atTop
  c_zero : c 0 = 0
  c_mono : Monotone c
  c_strict : StrictConvexOn ℝ univ c
  c_deriv : ∀ x, HasDerivAt c (c' x) x
  K_big : β * p * f' K < c' (δ * K) * (1 - β * (1 - δ))

/-- The policy `g`, extended by zero off `[0, K]`. -/
noncomputable def fpol (f c : ℝ → ℝ) (p δ β K : ℝ) [Nonempty (Icc (0 : ℝ) K)]
    (v : Icc (0 : ℝ) K →ᵇ ℝ) (k : ℝ) : ℝ := by
  classical exact if hk : k ∈ Icc 0 K then
    (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) ⟨k, hk⟩).1 else 0

theorem fpol_of_mem [Nonempty (Icc (0 : ℝ) K)] (v : Icc (0 : ℝ) K →ᵇ ℝ) {k : ℝ}
    (hk : k ∈ Icc 0 K) :
    fpol f c p δ β K v k = (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) ⟨k, hk⟩).1 := by
  simp only [fpol, hk, ↓reduceDIte]

namespace FirmDyn

variable {v : Icc (0 : ℝ) K →ᵇ ℝ} [Nonempty (Icc (0 : ℝ) K)] (h : FirmDyn f c f' c' p δ β K)
  (hv : bellman h.adj.h43 h.adj.h44 v = v)
include h hv

/-- `v(x) = pf(x) − c(g(x) − (1 − δ)x) + βv(g(x))`. -/
theorem v_eq (x : Icc (0 : ℝ) K) :
    v x = obj (adjF f c p δ K) β v (x, argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) x) := by
  obtain ⟨-, hUA, -⟩ := ex_5_9b h.adj hv
  have e := bellman_apply h.adj.h43 h.adj.h44 v x
  rw [hv] at e
  rw [e]
  exact (hUA.argmaxFn_mem x).2.symm

omit [Nonempty (Icc (0 : ℝ) K)] in
/-- Every choice does at most as well as `v`. -/
theorem obj_le (x y : Icc (0 : ℝ) K) : obj (adjF f c p δ K) β v (x, y) ≤ v x := by
  have e := bellman_apply h.adj.h43 h.adj.h44 v x
  rw [hv] at e
  rw [e]
  exact le_maxValue (continuousOn_obj h.adj.h44 v.continuous) (h.adj.h43.compact _)
    (mem_fullΓ x y)

omit h hv in
theorem fpol_mem {k : ℝ} (hk : k ∈ Icc 0 K) : fpol f c p δ β K v k ∈ Icc 0 K := by
  rw [fpol_of_mem v hk]; exact Subtype.mem _

theorem continuousOn_fpol : ContinuousOn (fpol f c p δ β K v) (Icc 0 K) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (Icc (0 : ℝ) K).domRestrict (fpol f c p δ β K v) =
      fun k => (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 := by
    funext k
    simp only [Set.domRestrict_apply]
    rw [fpol_of_mem v k.2]
  rw [e]
  exact continuous_subtype_val.comp (ex_5_9b h.adj hv).2.2

theorem monotoneOn_fpol : MonotoneOn (fpol f c p δ β K v) (Icc 0 K) := fun k hk k' hk' hkk' => by
  rw [fpol_of_mem v hk, fpol_of_mem v hk']
  exact ex_5_9b_mono h.adj hv (show (⟨k, hk⟩ : Icc (0 : ℝ) K) ≤ ⟨k', hk'⟩ from hkk')

/-- **Investing at `k = 0` pays**: `g(0) > 0`. If `g(0) = 0`, then `v(0) = 0` and
`βpf(ε) ≤ β[v(ε) − v(0)] ≤ c(ε)` for small `ε`, but `f(ε)/ε ≥ f'(ε) → ∞` while `c(ε)/ε → c'(0)`. -/
theorem fpol_zero_pos : 0 < fpol f c p δ β K v 0 := by
  have hK := h.adj.K_pos
  have hβ := h.adj.β_pos
  have hp := h.adj.p_pos
  have h0 : (0 : ℝ) ∈ Icc 0 K := ⟨le_rfl, hK.le⟩
  rw [fpol_of_mem v h0]
  by_contra hle
  push Not at hle
  set z0 : Icc (0 : ℝ) K := ⟨0, h0⟩
  have hg0 : argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) z0 = z0 :=
    Subtype.ext (le_antisymm hle (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) z0).2.1)
  have hv0 : v z0 = 0 := by
    have := h.v_eq hv z0
    rw [hg0] at this
    simp only [obj, adjF, z0, mul_zero, sub_zero, h.f_zero, h.c_zero] at this
    nlinarith [h.adj.β_lt]
  have hbound : ∀ ε, 0 < ε → ε ≤ K → β * p * f ε ≤ c ε := fun ε hε hεK => by
    set zε : Icc (0 : ℝ) K := ⟨ε, hε.le, hεK⟩
    have hA := h.obj_le hv z0 zε
    have hB := h.obj_le hv zε z0
    have hc : c (0 - (1 - δ) * ε) ≤ 0 := by
      have := h.c_mono (show 0 - (1 - δ) * ε ≤ 0 by nlinarith [h.adj.δ_lt])
      rwa [h.c_zero] at this
    simp only [obj, adjF, z0, zε, h.f_zero, mul_zero, sub_zero, hv0] at hA hB
    have hB' := mul_le_mul_of_nonneg_left hB hβ.le
    nlinarith
  have htan : ∀ ε, 0 < ε → ε ≤ K → ε * f' ε ≤ f ε := fun ε hε hεK => by
    have := tangent_le h.adj.f_concave.concaveOn (a := ε) (b := 0) ⟨hε.le, hεK⟩ h0
      (h.f_deriv ε hε)
    rw [h.f_zero] at this
    linarith
  have hslope := (h.c_deriv 0).tendsto_slope_zero_right
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε⁻¹ • (c (0 + ε) - c 0) < c' 0 + 1 :=
    hslope.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (c' 0 + 1) / (β * p) < f' ε :=
    h.inada.eventually (eventually_gt_atTop _)
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 K := Ioo_mem_nhdsGT hK
  obtain ⟨ε, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  simp only [zero_add, h.c_zero, sub_zero, smul_eq_mul] at h1
  have hε := h3.1
  have h1' : c ε < (c' 0 + 1) * ε := by
    rw [inv_mul_lt_iff₀ hε] at h1; linarith
  rw [div_lt_iff₀ (by positivity)] at h2
  have := hbound ε hε h3.2.le
  have := htan ε hε h3.2.le
  have h4 : (c' 0 + 1) * ε < β * p * (ε * f' ε) := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ β * p)
  linarith

/-- **The upper end is not a steady state**: `g(K) < K`. Otherwise, comparing `y = K − ε` at
`K` and `y = K` at `K − ε`, `φ(ε) = β[p(f(K) − f(K − ε)) + c(δK + (1 − δ)ε) − c(δK)]
− [c(δK) − c(δK − ε)] ≥ 0`, while `φ(0) = 0` and `φ'(0) = βpf'(K) − c'(δK)(1 − β(1 − δ)) < 0`. -/
theorem fpol_K_lt : fpol f c p δ β K v K < K := by
  have hK := h.adj.K_pos
  have hβ := h.adj.β_pos
  have hK1 : K ∈ Icc 0 K := ⟨hK.le, le_rfl⟩
  rw [fpol_of_mem v hK1]
  by_contra hle
  push Not at hle
  set zK : Icc (0 : ℝ) K := ⟨K, hK1⟩
  have hgK : argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) zK = zK :=
    Subtype.ext (le_antisymm (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) zK).2.2 hle)
  have hvK := h.v_eq hv zK
  rw [hgK] at hvK
  simp only [obj, adjF, zK] at hvK
  rw [show K - (1 - δ) * K = δ * K by ring] at hvK
  set φ : ℝ → ℝ := fun ε => β * (p * (f K - f (K - ε)) + c (δ * K + (1 - δ) * ε) - c (δ * K)) -
    (c (δ * K) - c (δ * K - ε))
  have hφ : ∀ ε, 0 < ε → ε ≤ K → 0 ≤ φ ε := fun ε hε hεK => by
    set zε : Icc (0 : ℝ) K := ⟨K - ε, by linarith, by linarith⟩
    have hA := h.obj_le hv zK zε
    have hB := h.obj_le hv zε zK
    simp only [obj, adjF, zK, zε] at hA hB
    rw [show K - ε - (1 - δ) * K = δ * K - ε by ring] at hA
    rw [show K - (1 - δ) * (K - ε) = δ * K + (1 - δ) * ε by ring] at hB
    have hB' := mul_le_mul_of_nonneg_left hB hβ.le
    simp only [φ]
    nlinarith
  -- `φ'(0) < 0`
  have hf1 : HasDerivAt (fun ε => f (K - ε)) (-f' K) 0 :=
    HasDerivAt.comp_const_sub K 0 (by rw [sub_zero]; exact h.f_deriv K hK)
  have hc2 : HasDerivAt (fun ε => c (δ * K - ε)) (-c' (δ * K)) 0 :=
    HasDerivAt.comp_const_sub (δ * K) 0 (by rw [sub_zero]; exact h.c_deriv _)
  have hc1 : HasDerivAt (fun ε => c (δ * K + (1 - δ) * ε)) (c' (δ * K) * (1 - δ)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => δ * K + (1 - δ) * ε) (1 - δ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 - δ)).const_add (δ * K)
    have := (h.c_deriv (δ * K + (1 - δ) * 0)).comp 0 hin
    simpa [Function.comp_def] using this
  have hφ' : HasDerivAt φ (β * (p * (0 - -f' K) + c' (δ * K) * (1 - δ) - 0) -
      (0 - -c' (δ * K))) 0 :=
    ((((hasDerivAt_const 0 (f K)).sub hf1).const_mul p).add hc1 |>.sub
      (hasDerivAt_const 0 (c (δ * K))) |>.const_mul β).sub
      ((hasDerivAt_const 0 (c (δ * K))).sub hc2)
  have hd : β * (p * (0 - -f' K) + c' (δ * K) * (1 - δ) - 0) - (0 - -c' (δ * K)) < 0 := by
    have := h.K_big
    nlinarith
  have hφ0 : φ 0 = 0 := by simp [φ]
  have e1 := hφ'.tendsto_slope_zero_right.eventually (gt_mem_nhds hd)
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 K := Ioo_mem_nhdsGT hK
  obtain ⟨ε, h1, h2⟩ := (e1.and e2).exists
  simp only [zero_add, hφ0, sub_zero, smul_eq_mul] at h1
  have := hφ ε h2.1 h2.2.le
  have : 0 ≤ ε⁻¹ * φ ε := mul_nonneg (inv_nonneg.2 h2.1.le) this
  linarith

/-- An interior steady state satisfies `c'(δk)(1 − β(1 − δ)) = βpf'(k)`. -/
theorem steady_eq {k : ℝ} (hk : k ∈ Ioo 0 K) (hfix : fpol f c p δ β K v k = k) :
    c' (δ * k) * (1 - β * (1 - δ)) = β * p * f' k := by
  have hkI : k ∈ Icc 0 K := ⟨hk.1.le, hk.2.le⟩
  rw [fpol_of_mem v hkI] at hfix
  exact ex_5_9b_steady h.adj hv (k := ⟨k, hkI⟩) (Subtype.ext hfix) hk (h.f_deriv k hk.1)
    (h.c_deriv _)

end FirmDyn

/-- **Exercise 6.8a: at most one stationary capital stock.** `k ↦ c'(δk)(1 − β(1 − δ))` rises
and `k ↦ βpf'(k)` falls. -/
theorem ex_6_8a_unique (h : FirmDyn f c f' c' p δ β K) {k₁ k₂ : ℝ} (hk₁ : k₁ ∈ Ioc 0 K)
    (hk₂ : k₂ ∈ Ioc 0 K) (e₁ : c' (δ * k₁) * (1 - β * (1 - δ)) = β * p * f' k₁)
    (e₂ : c' (δ * k₂) * (1 - β * (1 - δ)) = β * p * f' k₂) : k₁ = k₂ := by
  have hβp : 0 < β * p := mul_pos h.adj.β_pos h.adj.p_pos
  have h1 : 0 < 1 - β * (1 - δ) := by nlinarith [h.adj.β_lt, h.adj.δ_pos, h.adj.δ_lt]
  have key : ∀ a b : ℝ, a ∈ Ioc 0 K → b ∈ Ioc 0 K → a < b →
      c' (δ * a) * (1 - β * (1 - δ)) = β * p * f' a →
      c' (δ * b) * (1 - β * (1 - δ)) = β * p * f' b → False := fun a b ha hb hab ea eb => by
    have hf := deriv_lt_of_strictConcave h.adj.f_concave ⟨ha.1.le, ha.2⟩ ⟨hb.1.le, hb.2⟩ hab
      (h.f_deriv a ha.1) (h.f_deriv b hb.1)
    have hc := deriv_lt_of_strictConcave h.c_strict.neg (mem_univ (δ * a)) (mem_univ (δ * b))
      (mul_lt_mul_of_pos_left hab h.adj.δ_pos) (h.c_deriv _).neg (h.c_deriv _).neg
    nlinarith
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exact (key _ _ hk₁ hk₂ hlt e₁ e₂).elim
  · exact heq
  · exact (key _ _ hk₂ hk₁ hgt e₂ e₁).elim

/-- **Exercise 6.8a–b.** The policy has exactly one fixed point `k̄` in `[0, K]`; it is interior
and solves `c'(δk̄)(1 − β(1 − δ)) = βpf'(k̄)`; and from every `k₀ ∈ [0, K]` the capital stock
converges monotonically to `k̄`. -/
theorem ex_6_8 [Nonempty (Icc (0 : ℝ) K)] (h : FirmDyn f c f' c' p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ} (hv : bellman h.adj.h43 h.adj.h44 v = v) :
    ∃ kbar ∈ Ioo 0 K, c' (δ * kbar) * (1 - β * (1 - δ)) = β * p * f' kbar ∧
      (∀ k ∈ Icc 0 K, fpol f c p δ β K v k = k ↔ k = kbar) ∧
      ∀ k₀ ∈ Icc 0 K,
        (Monotone (fun t => (fpol f c p δ β K v)^[t] k₀) ∨
          Antitone (fun t => (fpol f c p δ β K v)^[t] k₀)) ∧
        Tendsto (fun t => (fpol f c p δ β K v)^[t] k₀) atTop (𝓝 kbar) := by
  set g := fpol f c p δ β K v
  have hK := h.adj.K_pos
  have hgc := h.continuousOn_fpol hv
  have hφc : ContinuousOn (fun k => g k - k) (Icc 0 K) := hgc.sub continuousOn_id
  have hg0 := h.fpol_zero_pos hv
  have hgK := h.fpol_K_lt hv
  -- a fixed point is interior, so it solves the steady-state equation
  have hfix_int : ∀ k ∈ Icc 0 K, g k = k → k ∈ Ioo 0 K := fun k hk hgk => by
    refine ⟨lt_of_le_of_ne hk.1 fun he => ?_, lt_of_le_of_ne hk.2 fun he => ?_⟩
    · rw [← he] at hgk; linarith
    · rw [he] at hgk; linarith
  obtain ⟨kbar, hkbar, hφ⟩ := intermediate_value_Icc' hK.le hφc
    (show (0 : ℝ) ∈ Icc (g K - K) (g 0 - 0) from ⟨by linarith, by linarith⟩)
  have hfix : g kbar = kbar := by simp only at hφ; linarith
  have hkI := hfix_int kbar hkbar hfix
  have heq := h.steady_eq hv hkI hfix
  have hiff : ∀ k ∈ Icc 0 K, g k = k ↔ k = kbar := fun k hk => ⟨fun hgk => by
      have hki := hfix_int k hk hgk
      exact ex_6_8a_unique h ⟨hki.1, hki.2.le⟩ ⟨hkI.1, hkI.2.le⟩
        (h.steady_eq hv hki hgk) heq, fun he => he ▸ hfix⟩
  have hbelow : ∀ k ∈ Icc 0 K, k < kbar → k < g k := fun k hk hlt => by
    by_contra hle
    push Not at hle
    obtain ⟨k', hk', hφ'⟩ := intermediate_value_Icc' hk.1 (hφc.mono (Icc_subset_Icc le_rfl hk.2))
      (show (0 : ℝ) ∈ Icc (g k - k) (g 0 - 0) from ⟨by linarith, by linarith⟩)
    have hk'I : k' ∈ Icc 0 K := ⟨hk'.1, hk'.2.trans hk.2⟩
    have := (hiff k' hk'I).1 (by simp only at hφ'; linarith)
    linarith [hk'.2]
  have habove : ∀ k ∈ Icc 0 K, kbar < k → g k < k := fun k hk hlt => by
    by_contra hle
    push Not at hle
    obtain ⟨k', hk', hφ'⟩ := intermediate_value_Icc' hk.2 (hφc.mono (Icc_subset_Icc hk.1 le_rfl))
      (show (0 : ℝ) ∈ Icc (g K - K) (g k - k) from ⟨by linarith, by linarith⟩)
    have hk'I : k' ∈ Icc 0 K := ⟨hk.1.trans hk'.1, hk'.2⟩
    have := (hiff k' hk'I).1 (by simp only at hφ'; linarith)
    linarith [hk'.1]
  refine ⟨kbar, hkI, heq, hiff, fun k₀ hk₀ => ?_⟩
  exact orbit_tendsto_of_crossing hgc (h.monotoneOn_fpol hv)
    (fun k hk => FirmDyn.fpol_mem hk) hkbar hfix hbelow habove hk₀

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cyclical example: the dynamic program (Exercises 6.2 and 6.7a)

SLP §6.1, p. 137 (Exercise 6.2), and §6.5, p. 156 (Exercise 6.7a). The functional equation
`v(k) = max_{0 ≤ y ≤ 1} [k^a(1 − y)^b + βv(y)]`, `a, b > 0`, `a + b < 1`, `0 < β < 1`.

Assumption 4.7 fails (`cd_not_strict`), so Theorem 4.8 does not apply. The argument here works
with any `V` that is concave on `[0, 1]` and satisfies the functional equation there
(`CDValue`), as the bounded continuous fixed point does (`cdValue_of_fixed`).

* `V` is nondecreasing, `V(0) = βV(1)`, and `V(1) − V(1 − s) ≤ s(V(1) − V(0))` by concavity.
* **Interior choices.** Every maximizer `y` at `k` satisfies `y > 0` (`argmax_pos`): from `V(0)`
  the gain `V(ε) − V(0) ≥ ε^{a+b} − βε(V(1) − V(0))` beats the loss `ε`, because `a + b < 1`.
  If `k > 0`, then `y < 1` (`argmax_lt_one`): `F_y → −∞` as `y → 1` while `V` is Lipschitz
  near `1`.
* `V` is strictly increasing (`strictMonoOn`), and the maximizer is unique
  (`argmax_unique`): at `k = 0` it is `y = 1`, and for `k > 0` the objective is strictly concave.
* `V` is differentiable on `(0, 1)` with `V'(z) = F_x(z, g(z))` (`hasDerivAt_V`): Theorem 4.10
  with `W(x) = F(x, g(z)) + βV(g(z))`, which is feasible near `z` because `Γ` is constant. At an
  interior maximizer, `F_y(k, y) + βV'(y) = 0` (`foc`).
* **Exercise 6.2** (`ex_6_2`): the policy is strictly decreasing: `k < k'` implies
  `g(k') < g(k)`. `F` has strictly decreasing differences (`F_xy < 0`), which gives `≤`.
  Equality at an interior `y` would make the first-order conditions give `k^a = k'^a`.
* **Exercise 6.7a** (`ex_6_7a`): Assumptions 4.3–4.4 hold, `F` is concave (but Assumption 4.7
  fails), the maximizer is unique, and from every `k₀ ∈ [0, 1]` there is exactly one optimal
  plan. It is generated by `g` (Theorem 4.4 with `v = v*`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {a b β : ℝ}

/-! ### The return -/

theorem cdF_zero_left (ha : 0 < a) (y : ℝ) : cdF a b 0 y = 0 := by
  simp [cdF, Real.zero_rpow ha.ne']

theorem cdF_one_right (hb : 0 < b) (k : ℝ) : cdF a b k 1 = 0 := by
  simp [cdF, Real.zero_rpow hb.ne']

theorem cdF_nonneg {k y : ℝ} (hk : 0 ≤ k) (hy : y ≤ 1) : 0 ≤ cdF a b k y :=
  mul_nonneg (Real.rpow_nonneg hk a) (Real.rpow_nonneg (by linarith) b)

theorem cdF_mono (ha : 0 < a) {k k' y : ℝ} (hk : 0 ≤ k) (hkk' : k ≤ k') (hy : y ≤ 1) :
    cdF a b k y ≤ cdF a b k' y :=
  mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hk hkk' ha.le)
    (Real.rpow_nonneg (by linarith) b)

theorem cdF_strictMono (ha : 0 < a) {k k' y : ℝ} (hk : 0 ≤ k) (hkk' : k < k') (hy : y < 1) :
    cdF a b k y < cdF a b k' y :=
  mul_lt_mul_of_pos_right (Real.rpow_lt_rpow hk hkk' ha) (Real.rpow_pos_of_pos (by linarith) b)

/-- `s^{−e}` exceeds any bound for some `s ∈ (0, 1)`. -/
theorem exists_rpow_neg_gt {e : ℝ} (he : 0 < e) (C : ℝ) : ∃ s ∈ Ioo (0 : ℝ) 1, C < s ^ (-e) := by
  have h1 := (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.2 he)).eventually (eventually_gt_atTop C)
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
  exact ⟨s, hs2, hs1⟩

/-! ### Concave solutions of the functional equation -/

/-- `V` is concave on `[0, 1]` and solves the functional equation there. -/
structure CDValue (a b β : ℝ) (V : ℝ → ℝ) : Prop where
  a_pos : 0 < a
  b_pos : 0 < b
  ab : a + b < 1
  β_pos : 0 < β
  β_lt : β < 1
  le : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, cdF a b x y + β * V y ≤ V x
  arg : ∀ x ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (0 : ℝ) 1, cdF a b x y + β * V y = V x
  conc : ConcaveOn ℝ (Icc 0 1) V

namespace CDValue

variable {V : ℝ → ℝ} (h : CDValue a b β V)
include h

theorem b_lt : b < 1 := by linarith [h.a_pos, h.ab]

theorem mono {x x' : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx' : x' ∈ Icc (0 : ℝ) 1) (hxx' : x ≤ x') :
    V x ≤ V x' := by
  obtain ⟨y, hy, hyv⟩ := h.arg x hx
  have := cdF_mono (b := b) h.a_pos hx.1 hxx' hy.2
  have := h.le x' hx' y hy
  linarith

theorem V_zero : V 0 = β * V 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨y, hy, hyv⟩ := h.arg 0 h0
  have hl := h.le 0 h0 1 h1
  have hm := h.mono hy h1 hy.2
  rw [cdF_zero_left h.a_pos] at hyv hl
  nlinarith [h.β_pos]

/-- Concavity: `V(1) − V(1 − s) ≤ s(V(1) − V(0))`. -/
theorem lip_one {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : V 1 - V (1 - s) ≤ s * (V 1 - V 0) := by
  have := h.conc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) hs.1 (by linarith [hs.2])
    (by ring : s + (1 - s) = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at this
  linarith

/-- **Every maximizer is positive.** -/
theorem argmax_pos {k y : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hyv : cdF a b k y + β * V y = V k) : 0 < y := by
  rcases eq_or_lt_of_le hy.1 with h0 | h0
  swap; · exact h0
  subst h0
  obtain ⟨L, hLdef⟩ : ∃ L, L = V 1 - V 0 := ⟨_, rfl⟩
  have hL : 0 ≤ L := hLdef ▸ sub_nonneg.2
    (h.mono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one)
  have hβ := h.β_pos
  obtain ⟨ε, hε, hεC⟩ := exists_rpow_neg_gt (by linarith [h.ab] : 0 < 1 - (a + b))
    ((1 + β ^ 2 * L) / β)
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1.le, hε.2.le⟩
  -- the loss from choosing `ε` instead of `0` at `k` is at most `ε`
  have hloss : β * (V ε - V 0) ≤ ε := by
    have h1 := h.le k hk ε hεI
    have h2 : (1 - ε) ≤ (1 - ε) ^ b :=
      Real.self_le_rpow_of_le_one (by linarith [hε.2]) (by linarith [hε.1]) h.b_lt.le
    have h3 : k ^ a ≤ 1 := Real.rpow_le_one hk.1 hk.2 h.a_pos.le
    have h4 : 0 ≤ k ^ a := Real.rpow_nonneg hk.1 a
    simp only [cdF, sub_zero, Real.one_rpow, mul_one] at h1 hyv
    nlinarith [mul_le_mul_of_nonneg_left h2 h4, mul_le_mul_of_nonneg_right h3 hε.1.le]
  -- the gain: `V(ε) − V(0) ≥ ε^{a+b} − βεL`
  have hgain : ε ^ (a + b) - β * ε * L ≤ V ε - V 0 := by
    have h1 := h.le ε hεI (1 - ε) ⟨by linarith [hε.2], by linarith [hε.1]⟩
    have h2 := h.lip_one hεI
    simp only [cdF, sub_sub_cancel] at h1
    rw [← Real.rpow_add hε.1] at h1
    rw [← hLdef] at h2
    have h0 := h.V_zero
    have := mul_le_mul_of_nonneg_left h2 hβ.le
    nlinarith
  have hsplit : ε ^ (a + b) = ε * ε ^ (-(1 - (a + b))) := by
    rw [← Real.rpow_one_add' hε.1.le
      (by linarith [h.a_pos, h.b_pos] : (0 : ℝ) < 1 + -(1 - (a + b))).ne']; ring_nf
  rw [div_lt_iff₀ hβ] at hεC
  have : β * (ε * ε ^ (-(1 - (a + b)))) ≤ ε * (1 + β ^ 2 * L) := by
    rw [← hsplit]; nlinarith
  nlinarith [hε.1]

/-- **If `k > 0`, every maximizer is below `1`.** -/
theorem argmax_lt_one {k y : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) (hk0 : 0 < k) (hy : y ∈ Icc (0 : ℝ) 1)
    (hyv : cdF a b k y + β * V y = V k) : y < 1 := by
  rcases eq_or_lt_of_le hy.2 with h1 | h1
  swap; · exact h1
  subst h1
  set L := V 1 - V 0
  have hβ := h.β_pos
  have hka : 0 < k ^ a := Real.rpow_pos_of_pos hk0 a
  obtain ⟨s, hs, hsC⟩ := exists_rpow_neg_gt (by linarith [h.b_lt] : 0 < 1 - b)
    (β * |L| / k ^ a)
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have h1 := h.le k hk (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h2 := h.lip_one hsI
  rw [cdF_one_right h.b_pos] at hyv
  simp only [cdF, sub_sub_cancel] at h1
  have hsplit : s ^ b = s * s ^ (-(1 - b)) := by
    rw [← Real.rpow_one_add' hs.1.le
        (by linarith [h.b_pos] : (0 : ℝ) < 1 + -(1 - b)).ne']; ring_nf
  rw [div_lt_iff₀ hka] at hsC
  have h3 : k ^ a * (s * s ^ (-(1 - b))) ≤ β * s * L := by rw [← hsplit]; nlinarith
  have h4 : β * s * L ≤ β * s * |L| :=
    mul_le_mul_of_nonneg_left (le_abs_self L) (mul_nonneg hβ.le hs.1.le)
  nlinarith [hs.1]

/-- **`V` is strictly increasing on `[0, 1]`.** -/
theorem strictMonoOn : StrictMonoOn V (Icc 0 1) := by
  intro x hx x' hx' hxx'
  obtain ⟨y, hy, hyv⟩ := h.arg x hx
  rcases eq_or_lt_of_le hy.2 with h1 | h1
  · -- `y = 1` forces `x = 0`
    subst h1
    have hx0 : x = 0 := by
      by_contra hne
      exact lt_irrefl _ (h.argmax_lt_one hx (lt_of_le_of_ne hx.1 (Ne.symm hne)) hy hyv)
    subst hx0
    set L := V 1 - V 0
    have hβ := h.β_pos
    have hx'0 : 0 < x' := hxx'
    have hka : 0 < x' ^ a := Real.rpow_pos_of_pos hx'0 a
    obtain ⟨s, hs, hsC⟩ := exists_rpow_neg_gt (by linarith [h.b_lt] : 0 < 1 - b)
      (β * |L| / x' ^ a)
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have h1 := h.le x' hx' (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h2 := h.lip_one hsI
    have h0 := h.V_zero
    simp only [cdF, sub_sub_cancel] at h1
    have hsplit : s ^ b = s * s ^ (-(1 - b)) := by
      rw [← Real.rpow_one_add' hs.1.le
        (by linarith [h.b_pos] : (0 : ℝ) < 1 + -(1 - b)).ne']; ring_nf
    rw [div_lt_iff₀ hka] at hsC
    have h4 : β * s * L ≤ β * s * |L| :=
      mul_le_mul_of_nonneg_left (le_abs_self L) (mul_nonneg hβ.le hs.1.le)
    have h5 : β * s * |L| < x' ^ a * (s * s ^ (-(1 - b))) := by nlinarith [hs.1]
    rw [← hsplit] at h5
    nlinarith
  · have := cdF_strictMono (b := b) h.a_pos hx.1 hxx' h1
    have := h.le x' hx' y hy
    linarith

/-- **The maximizer is unique.** -/
theorem argmax_unique {k y₁ y₂ : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) (hy₁ : y₁ ∈ Icc (0 : ℝ) 1)
    (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) (h₁ : cdF a b k y₁ + β * V y₁ = V k)
    (h₂ : cdF a b k y₂ + β * V y₂ = V k) : y₁ = y₂ := by
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rcases eq_or_lt_of_le hk.1 with hk0 | hk0
  · -- at `k = 0` the maximizer is `1`
    subst hk0
    have hone : ∀ y ∈ Icc (0 : ℝ) 1, cdF a b 0 y + β * V y = V 0 → y = 1 := fun y hy hyv => by
      rw [cdF_zero_left h.a_pos, zero_add, h.V_zero] at hyv
      have hVy : V y = V 1 := by
        have := h.β_pos; field_simp at hyv; linarith
      by_contra hne
      exact (h.strictMonoOn hy h1I (lt_of_le_of_ne hy.2 hne)).ne hVy
    rw [hone y₁ hy₁ h₁, hone y₂ hy₂ h₂]
  · -- for `k > 0` the objective is strictly concave
    by_contra hne
    set m := (y₁ + y₂) / 2
    have hmI : m ∈ Icc (0 : ℝ) 1 := ⟨by simp only [m]; linarith [hy₁.1, hy₂.1],
      by simp only [m]; linarith [hy₁.2, hy₂.2]⟩
    have hsc := (Real.strictConcaveOn_rpow h.b_pos h.b_lt).2
      (show 1 - y₁ ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith [hy₁.2])
      (show 1 - y₂ ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith [hy₂.2])
      (fun he => hne (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hsc
    rw [show 1 / 2 * (1 - y₁) + 1 / 2 * (1 - y₂) = 1 - m by simp only [m]; ring] at hsc
    have hVm := h.conc.2 hy₁ hy₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at hVm
    rw [show 1 / 2 * y₁ + 1 / 2 * y₂ = m by simp only [m]; ring] at hVm
    have hka : 0 < k ^ a := Real.rpow_pos_of_pos hk0 a
    have := h.le k hk m hmI
    simp only [cdF] at this h₁ h₂
    have hsc' := mul_lt_mul_of_pos_left hsc hka
    nlinarith [h.β_pos]

/-- **`V` is differentiable on `(0, 1)`** (Theorem 4.10), with `V'(z) = F_x(z, w)` for any
maximizer `w` at `z`. -/
theorem hasDerivAt_V {z w : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1)
    (hwv : cdF a b z w + β * V w = V z) : HasDerivAt V (cdFx a b z w) z := by
  set W : ℝ → ℝ := fun x => cdF a b x w + β * V w
  have hW : HasDerivAt W (cdFx a b z w) z := (hasDerivAt_cdF_k hz.1 w).add_const _
  have hX : Icc (0 : ℝ) 1 ∈ 𝓝 z := Icc_mem_nhds hz.1 hz.2
  have hle : ∀ᶠ x in 𝓝 z, W x ≤ V x := by
    filter_upwards [hX] with x hx
    exact h.le x hx w hw
  have := (theorem_4_10 h.conc hX hW.hasFDerivAt hwv hle).hasDerivAt
  simpa using this

/-- **The first-order condition** at an interior maximizer: `F_y(k, y) + βV'(y) = 0`. -/
theorem foc {k y d : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hyv : cdF a b k y + β * V y = V k) (hd : HasDerivAt V d y) :
    cdFy a b k y + β * d = 0 := by
  have hΦ : HasDerivAt (fun z => cdF a b k z + β * V z) (cdFy a b k y + β * d) y :=
    (hasDerivAt_cdF_y k hy.2).add (hd.const_mul β)
  have hloc : IsLocalMax (fun z => cdF a b k z + β * V z) y := by
    filter_upwards [Icc_mem_nhds hy.1 hy.2] with z hz
    rw [hyv]
    exact h.le k hk z hz
  exact hloc.hasDerivAt_eq_zero hΦ

/-- **Exercise 6.2.** The policy is strictly decreasing. -/
theorem ex_6_2 {k k' y y' : ℝ} (hk : k ∈ Icc (0 : ℝ) 1) (hk' : k' ∈ Icc (0 : ℝ) 1)
    (hkk' : k < k') (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1)
    (hyv : cdF a b k y + β * V y = V k) (hyv' : cdF a b k' y' + β * V y' = V k') : y' < y := by
  -- strictly decreasing differences give `y' ≤ y`
  have hle : y' ≤ y := by
    by_contra hlt
    push Not at hlt
    have h1 := h.le k hk y' hy'
    have h2 := h.le k' hk' y hy
    have hka := Real.rpow_lt_rpow hk.1 hkk' h.a_pos
    have hb := Real.rpow_lt_rpow (by linarith [hy'.2] : 0 ≤ 1 - y') (by linarith : 1 - y' < 1 - y)
      h.b_pos
    simp only [cdF] at h1 h2 hyv hyv'
    nlinarith
  refine lt_of_le_of_ne hle fun heq => ?_
  subst heq
  have hk'0 : 0 < k' := lt_of_le_of_lt hk.1 hkk'
  have hpos := h.argmax_pos hk' hy' hyv'
  have hlt := h.argmax_lt_one hk' hk'0 hy' hyv'
  have hI : y' ∈ Ioo (0 : ℝ) 1 := ⟨hpos, hlt⟩
  obtain ⟨w, hw, hwv⟩ := h.arg y' hy'
  have hd := h.hasDerivAt_V hI hw hwv
  have e1 := h.foc hk hI hyv hd
  have e2 := h.foc hk' hI hyv' hd
  simp only [cdFy] at e1 e2
  have hpos' : 0 < b * (1 - y') ^ (b - 1) :=
    mul_pos h.b_pos (Real.rpow_pos_of_pos (by linarith) _)
  have hka := Real.rpow_lt_rpow hk.1 hkk' h.a_pos
  nlinarith

end CDValue

/-! ### The bounded continuous fixed point -/

/-- `F` on `[0, 1]²`. -/
noncomputable def cdFs (a b : ℝ) (pr : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : ℝ :=
  cdF a b pr.1.1 pr.2.1

theorem continuous_cdFs (ha : 0 < a) (hb : 0 < b) : Continuous (cdFs a b) :=
  ((continuous_subtype_val.comp continuous_fst).rpow_const fun _ => Or.inr ha.le).mul
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).rpow_const
      fun _ => Or.inr hb.le)

/-- **Assumption 4.3**: `Γ(k) = [0, 1]`. -/
theorem cd_assumption43 : Assumption43 (fullΓ 1) := full_assumption43 zero_le_one

/-- **Assumption 4.4.** -/
theorem cd_assumption44 (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Assumption44 (fullΓ 1) (cdFs a b) β := by
  obtain ⟨B, hB⟩ := exists_bound_Icc_prod (continuous_cdFs ha hb)
  exact ⟨(continuous_cdFs ha hb).continuousOn, ⟨B, fun pr _ => hB pr⟩, hβ0, hβ1⟩

/-- The bounded continuous fixed point, lifted to `ℝ`, is a concave solution. -/
theorem cdValue_of_fixed [Nonempty (Icc (0 : ℝ) 1)] (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {v : Icc (0 : ℝ) 1 →ᵇ ℝ}
    (hv : bellman cd_assumption43 (cd_assumption44 ha hb hβ0 hβ1) v = v) :
    CDValue a b β (liftR 1 v) := by
  have hF : ∀ x y x' y' : Icc (0 : ℝ) 1, y ∈ fullΓ 1 x → y' ∈ fullΓ 1 x' →
      ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), θ * cdFs a b (x, y) + (1 - θ) * cdFs a b (x', y') ≤
        cdFs a b (cmb (convex_Icc 0 1) h0 h1 x x', cmb (convex_Icc 0 1) h0 h1 y y') :=
    fun x y x' y' _ _ θ h0 h1 => by
      have := (cd_concave ha hb hab.le).2 (show (x.1, y.1) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨x.2, y.2⟩) (show (x'.1, y'.1) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from ⟨x'.2, y'.2⟩) h0
        (by linarith : 0 ≤ 1 - θ) (by ring)
      simpa [cdFs, cmb, smul_eq_mul] using this
  have hvc := fixed_concave_of_concaveF cd_assumption43 (cd_assumption44 ha hb hβ0 hβ1) hF
    full_a48 hv
  refine ⟨ha, hb, hab, hβ0, hβ1, fun x hx y hy => ?_, fun x hx => ?_,
    concaveOn_liftR_of_concave hvc⟩
  · obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax cd_assumption43
      (cd_assumption44 ha hb hβ0 hβ1) v ⟨x, hx⟩
    rw [hv] at hmax
    have := hmax ⟨y, hy⟩ (mem_fullΓ _ _)
    rw [liftR_of_mem v hx, liftR_of_mem v hy]
    exact this
  · obtain ⟨y, -, hval, -⟩ := exists_bellman_argmax cd_assumption43
      (cd_assumption44 ha hb hβ0 hβ1) v ⟨x, hx⟩
    rw [hv] at hval
    refine ⟨y.1, y.2, ?_⟩
    rw [liftR_of_mem v hx, liftR_of_mem v y.2, hval]
    rfl

/-- Maximizers are characterized by `F(x, y) + βv(y) = v(x)`. -/
theorem mem_argmax_iff (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β) (hβ1 : β < 1)
    {v : Icc (0 : ℝ) 1 →ᵇ ℝ} (hv : bellman cd_assumption43 (cd_assumption44 ha hb hβ0 hβ1) v = v)
    (x y : Icc (0 : ℝ) 1) : y ∈ argmax (obj (cdFs a b) β v) (fullΓ 1) x ↔
      cdF a b x.1 y.1 + β * liftR 1 v y.1 = liftR 1 v x.1 := by
  rw [liftR_of_mem v y.2, liftR_of_mem v x.2]
  have e := bellman_apply cd_assumption43 (cd_assumption44 ha hb hβ0 hβ1) v x
  rw [hv] at e
  simp only [argmax, mem_ofPred_eq, Subtype.coe_eta, obj, cdFs, ← e]
  exact ⟨fun h => h.2, fun h => ⟨mem_fullΓ _ _, h⟩⟩

/-- **Exercise 6.2** for the fixed point: optimal choices fall strictly as `k` rises. -/
theorem ex_6_2_fixed [Nonempty (Icc (0 : ℝ) 1)] (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {v : Icc (0 : ℝ) 1 →ᵇ ℝ}
    (hv : bellman cd_assumption43 (cd_assumption44 ha hb hβ0 hβ1) v = v)
    {k k' y y' : Icc (0 : ℝ) 1} (hkk' : k.1 < k'.1)
    (hy : y ∈ argmax (obj (cdFs a b) β v) (fullΓ 1) k)
    (hy' : y' ∈ argmax (obj (cdFs a b) β v) (fullΓ 1) k') : y'.1 < y.1 :=
  (cdValue_of_fixed ha hb hab hβ0 hβ1 hv).ex_6_2 k.2 k'.2 hkk' y.2 y'.2
    ((mem_argmax_iff ha hb hβ0 hβ1 hv k y).1 hy) ((mem_argmax_iff ha hb hβ0 hβ1 hv k' y').1 hy')

/-- **Exercise 6.7a.** Assumptions 4.3–4.4 hold and `F` is concave (but not strictly so,
`cd_not_strict`). Still, the maximizer is unique at every `k`, and from every `k₀ ∈ [0, 1]` there
is exactly one optimal capital sequence; it is generated by the policy. -/
theorem ex_6_7a [Nonempty (Icc (0 : ℝ) 1)] (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ v : Icc (0 : ℝ) 1 →ᵇ ℝ, bellman cd_assumption43 (cd_assumption44 ha hb hβ0 hβ1) v = v ∧
      UniqueArgmax (fullΓ 1) (obj (cdFs a b) β v) ∧
      ∀ x₀ : Icc (0 : ℝ) 1, ∃! x : ℕ → Icc (0 : ℝ) 1, x ∈ Feasible (fullΓ 1) x₀ ∧
        total (curryF (cdFs a b)) β x = vstar (fullΓ 1) (curryF (cdFs a b)) β x₀ := by
  have h43 := cd_assumption43
  have h44 := cd_assumption44 ha hb hβ0 hβ1
  obtain ⟨v, hv, -, -, -⟩ := theorem_4_6 h43 h44
  have hV := cdValue_of_fixed ha hb hab hβ0 hβ1 hv
  have harg := mem_argmax_iff ha hb hβ0 hβ1 hv
  have hUA : UniqueArgmax (fullΓ 1) (obj (cdFs a b) β v) :=
    ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc, continuousOn_obj h44 v.continuous,
      fun x y₁ hy₁ y₂ hy₂ => Subtype.ext (hV.argmax_unique x.2 y₁.2 y₂.2 ((harg x y₁).1 hy₁)
        ((harg x y₂).1 hy₂))⟩
  refine ⟨v, hv, hUA, fun x₀ => ?_⟩
  set g := argmaxFn (fullΓ 1) (obj (cdFs a b) β v)
  set xs : ℕ → Icc (0 : ℝ) 1 := fun t => g^[t] x₀
  have hstep : ∀ t, xs (t + 1) = g (xs t) := fun t => Function.iterate_succ_apply' g t x₀
  have hfeas : xs ∈ Feasible (fullΓ 1) x₀ := ⟨rfl, fun _ => mem_fullΓ _ _⟩
  refine ⟨xs, ⟨hfeas, policy_plan_optimal h43 h44 hv rfl fun t => ?_⟩, ?_⟩
  · rw [hstep]; exact hUA.argmaxFn_mem _
  · rintro y ⟨hy, hyopt⟩
    have hvs := fixedPoint_eq_vstar h43 h44 hv
    have hrec : ∀ t, y (t + 1) = g (y t) := fun t => by
      have := theorem_4_4 h44.β_pos (assumption42_of_44 h44) hy hyopt t
      rw [← congrFun hvs, ← congrFun hvs, curryF, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_eq_coe_iff] at this
      have hmem : y (t + 1) ∈ argmax (obj (cdFs a b) β v) (fullΓ 1) (y t) := by
        have e := bellman_apply h43 h44 v (y t)
        rw [hv] at e
        exact ⟨mem_fullΓ _ _, by rw [← e, obj, this]⟩
      exact hUA.unique _ _ hmem _ (hUA.argmaxFn_mem _)
    funext t
    induction t with
    | zero => exact hy.1
    | succ t ih => rw [hrec, hstep, ih]

end StokeyLucasPrescott.DeterministicDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A consumer with recursive preferences (Exercise 6.10)

SLP §6.5, pp. 160–161. The consumer of §5.12 (`ConsumerRecursive`) with a single good and price
`1`: `v(x) = max_{0 ≤ y ≤ x} W[x − y, v(R⁻¹y)]`, written as the choice of consumption
`C = x − y` (`cv c` is the one-good bundle `c`). Wealth `x̄` is **stationary** if consuming
`x̄(1 − R)` is optimal at `x̄`; it leaves next period's wealth at `R⁻¹(x̄ − x̄(1 − R)) = x̄`.

* `exists_unique_fixed_z` (the reduction in **Exercise 6.10b**): for each consumption level
  `c ≥ 0`, `z = W(c, z)` has exactly one solution (`W` is a contraction in `z`). So a stationary
  pair `(x̄, z̄)` is determined by `x̄` alone.
* **Exercise 6.10a** (`ex_6_10a_if`, `ex_6_10a_only_if`): with `W` concave and nonnegative,
  differentiable at `(x̄(1 − R), z̄)` and `0 < R < 1`:
  * if `z̄ = W[x̄(1 − R), z̄]`, `R = W₂[x̄(1 − R), z̄]` and `W₁ ≥ 0` there, then `x̄` is stationary
    and `v(x̄) = z̄`. Concavity gives `v(x_t) − z̄ ≤ W₁(c_t − c̄) + R[v(x_{t+1}) − z̄]` along the
    optimal path, and the budget makes `Σ_{t<T} Rᵗ(c_t − c̄) ≤ Rᵀx̄`;
  * conversely, if `x̄ > 0` is stationary and `W₁ ≠ 0`, then `z̄ = v(x̄)` solves both equations.
    This is the envelope condition and the Euler equation of Exercise 5.12c at `x̄`.
* **Exercise 6.10c** (`ex_6_10c_eq`, `ex_6_10c_ne`): with `W(c, z) = U(c) + βz`, so `W₂ = β`:
  if `β = R`, every wealth level is stationary (the optimal wealth sequence is constant); if
  `β ≠ R` and `U' ≠ 0`, no positive wealth level is.
* **Exercise 6.10d** (`ex_6_10d`): the Euler equation
  `W₁(c_t, z_{t+1}) = R⁻¹W₂(c_t, z_{t+1})W₁(c_{t+1}, z_{t+2})` along an optimal path.

Parts (e) and (f) ask the reader to find conditions for local and global stability, which is
open-ended.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {W : (Fin 1 → ℝ) → ℝ → ℝ} {R β M : ℝ}

/-- The one-good bundle `c`. -/
def cv (c : ℝ) : Fin 1 → ℝ := fun _ => c

/-- The price `1`. -/
def one1 : Fin 1 → ℝ := fun _ => 1

theorem spend_cv (c : ℝ) : spend one1 (cv c) = c := by simp [spend, one1, cv]

theorem cv_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cv c := fun _ => hc

theorem eq_cv (C : Fin 1 → ℝ) : C = cv (C 0) := by
  funext i; rw [Subsingleton.elim i 0]; rfl

theorem single_eq_cv : (Pi.single 0 1 : Fin 1 → ℝ) = cv 1 := by
  funext i; rw [Subsingleton.elim i 0]; simp [cv]

/-- **Exercise 6.10b (reduction).** `z = W(c, z)` has exactly one solution for each `c ≥ 0`. -/
theorem exists_unique_fixed_z (h : ConsHyp W one1 R β M) {C : Fin 1 → ℝ} (hC : 0 ≤ C) :
    ∃! z, W C z = z := by
  have hc : ContractingWith (Real.toNNReal β) (W C) := by
    refine ⟨Real.toNNReal_lt_one.2 h.β_lt, LipschitzWith.of_dist_le' fun z z' => ?_⟩
    rw [Real.dist_eq, Real.dist_eq]
    exact h.lip C hC z z'
  obtain ⟨z, hz, -⟩ := hc.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨z, hz, fun z' hz' => ?_⟩
  exact hc.fixedPoint_unique' hz' hz

/-- The partial derivative in the good, from the derivative of `W`. -/
theorem hasDerivAt_dir {DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ} {C : Fin 1 → ℝ} {z : ℝ}
    (hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (C, z)) :
    HasDerivAt (fun x : ℝ => W (C + x • Pi.single 0 1) z) (DW (Pi.single 0 1, 0)) 0 := by
  have hp : HasDerivAt (fun x : ℝ => (C + x • (Pi.single 0 1 : Fin 1 → ℝ), z))
      ((1 : ℝ) • (Pi.single 0 1 : Fin 1 → ℝ), 0) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const (Pi.single 0 1 : Fin 1 → ℝ)).const_add C).prodMk
      (hasDerivAt_const _ _)
  rw [one_smul] at hp
  exact hDW.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)

/-- `DW(u, s) = u₀·W₁ + s·W₂`. -/
theorem dw_apply (DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ) (u : Fin 1 → ℝ) (s : ℝ) :
    DW (u, s) = u 0 * DW (cv 1, 0) + s * DW (0, 1) := by
  have e : (u, s) = u 0 • (cv 1, (0 : ℝ)) + s • ((0 : Fin 1 → ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ (by simp)
    funext i; rw [Subsingleton.elim i 0]; simp [cv]
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Stationary consumption leaves wealth unchanged. -/
theorem nextWealth_bar {x : ℝ} (hR : 0 < R) : nextWealth one1 R x (cv (x * (1 - R))) = x := by
  rw [nextWealth, spend_cv]; field_simp; ring

/-- **Exercise 6.10a (if).** If `z̄ = W[x̄(1 − R), z̄]`, `R = W₂[x̄(1 − R), z̄]` and `W₁ ≥ 0`, then
`x̄` is stationary and `v(x̄) = z̄`. -/
theorem ex_6_10a_if (h : ConsHyp W one1 R β M) (hR1 : R < 1)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {x z : ℝ} (hx : 0 ≤ x) (hz : W (cv (x * (1 - R))) z = z)
    {DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ}
    (hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (cv (x * (1 - R)), z))
    (hW2 : DW (0, 1) = R) (hW1 : 0 ≤ DW (cv 1, 0)) :
    cv (x * (1 - R)) ∈ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx⟩ ∧ v ⟨x, hx⟩ = z := by
  have hR := h.R_pos
  set c := x * (1 - R)
  have hc : 0 ≤ c := mul_nonneg hx (by linarith)
  set A₀ : Wealth := ⟨x, hx⟩
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W one1 R v) (budgetΓ one1) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hle : ∀ (A : Wealth) (C : Fin 1 → ℝ), C ∈ budgetΓ one1 A →
      consObj W one1 R v (A, C) ≤ v A := fun A C hC => by
    obtain ⟨-, -, -, hmax⟩ := exists_consT_argmax h v A
    rw [hv] at hmax
    exact hmax C hC
  have hmem : cv c ∈ budgetΓ one1 A₀ :=
    ⟨cv_nonneg hc, by rw [spend_cv]; simp only [A₀, c]; nlinarith⟩
  have hobj : consObj W one1 R v (A₀, cv c) = W (cv c) (v A₀) := by
    simp only [consObj, A₀, c, nextWealth_bar hR, vext_of_nonneg v hx]
  -- `z̄ ≥ 0`
  have hz0 : 0 ≤ z := by
    by_contra hneg
    push Not at hneg
    have h1 := h.lip (cv c) (cv_nonneg hc) z 0
    have h2 := hnn (cv c) 0 (cv_nonneg hc) le_rfl
    rw [hz, sub_zero, abs_of_neg hneg] at h1
    rw [abs_le] at h1
    nlinarith [h.β_lt]
  -- `v(x̄) ≥ z̄`: `v(x̄) ≥ W(c̄, v(x̄))` and `W(c̄, ·)` is a contraction with fixed point `z̄`
  have hlow : z ≤ v A₀ := by
    have h1 := hle A₀ (cv c) hmem
    rw [hobj] at h1
    by_contra hlt
    push Not at hlt
    have h2 := h.lip (cv c) (cv_nonneg hc) z (v A₀)
    rw [hz, abs_of_pos (by linarith : 0 < z - v A₀), abs_le] at h2
    nlinarith [h.β_lt]
  -- the optimal path from `x̄`
  choose sel hsel using fun A : Wealth => exists_consT_argmax h v A
  have hnx : ∀ A : Wealth, 0 ≤ nextWealth one1 R A.1 (sel A) := fun A =>
    div_nonneg (sub_nonneg.2 (hsel A).1.2) hR.le
  set nx : Wealth → Wealth := fun A => ⟨nextWealth one1 R A.1 (sel A), hnx A⟩
  set xs : ℕ → Wealth := fun t => nx^[t] A₀
  have hstep : ∀ t, xs (t + 1) = nx (xs t) := fun t => Function.iterate_succ_apply' nx t A₀
  have hval : ∀ t, v (xs t) = W (sel (xs t)) (v (xs (t + 1))) := fun t => by
    have := (hsel (xs t)).2.1
    rw [hv] at this
    rw [this, consObj, hstep, vext_of_nonneg v (hnx (xs t))]
  have hbudget : ∀ t, R * (xs (t + 1)).1 = (xs t).1 - sel (xs t) 0 := fun t => by
    rw [hstep]
    simp only [nx, nextWealth]
    have : spend one1 (sel (xs t)) = sel (xs t) 0 := by simp [spend, one1]
    rw [this, mul_div_cancel₀ _ hR.ne']
  -- concavity: `v(x_t) − z̄ ≤ W₁(c_t − c̄) + R[v(x_{t+1}) − z̄]`
  have hv0 := (ex_5_12b_concave h hconc hnn hv).1
  have hconcstep : ∀ t, v (xs t) - z ≤ DW (cv 1, 0) * (sel (xs t) 0 - c) +
      R * (v (xs (t + 1)) - z) := fun t => by
    have hsupp := concave_le_fderiv hconc (z₀ := (cv c, z)) (z := (sel (xs t), v (xs (t + 1))))
      ⟨cv_nonneg hc, hz0⟩ ⟨(hsel (xs t)).1.1, hv0 _⟩ hDW
    simp only [hz] at hsupp
    rw [Prod.mk_sub_mk, dw_apply, hW2] at hsupp
    rw [hval t]
    have e : (sel (xs t) - cv c) 0 = sel (xs t) 0 - c := by simp [cv]
    rw [e] at hsupp
    linarith
  -- unrolling
  have hunroll : ∀ T, v A₀ - z ≤ DW (cv 1, 0) * (x - R ^ T * (xs T).1 - x * (1 - R ^ T)) +
      R ^ T * (v (xs T) - z) := fun T => by
    induction T with
    | zero => norm_num [xs, A₀]
    | succ T ih =>
      have h1 := mul_le_mul_of_nonneg_left (hconcstep T) (pow_nonneg hR.le T)
      have h2 := hbudget T
      have e1 : R ^ (T + 1) * (xs (T + 1)).1 = R ^ T * ((xs T).1 - sel (xs T) 0) := by
        rw [pow_succ, mul_assoc, h2]
      rw [e1, pow_succ]
      simp only [c] at h1
      nlinarith
  have hbound : ∀ T, v A₀ - z ≤ R ^ T * (DW (cv 1, 0) * x + (‖v‖ + |z|)) := fun T => by
    have h1 := hunroll T
    have hx0 : 0 ≤ (xs T).1 := (xs T).2
    have hvT : |v (xs T)| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (xs T)
    have hRT := pow_nonneg hR.le T
    have h2 : R ^ T * (v (xs T) - z) ≤ R ^ T * (‖v‖ + |z|) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self (v (xs T)), neg_abs_le z]) hRT
    have h3 : 0 ≤ DW (cv 1, 0) * (R ^ T * (xs T).1) := mul_nonneg hW1 (mul_nonneg hRT hx0)
    nlinarith
  have hlim : Tendsto (fun T => R ^ T * (DW (cv 1, 0) * x + (‖v‖ + |z|))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hR.le hR1).mul_const
      (DW (cv 1, 0) * x + (‖v‖ + |z|))
  have hup : v A₀ - z ≤ 0 := ge_of_tendsto' hlim hbound
  have hvz : v A₀ = z := by linarith
  refine ⟨⟨hmem, ?_⟩, hvz⟩
  rw [← hvx, hobj, hvz, hz]

/-- **Exercise 6.10a (only if).** If `x̄ > 0` is stationary and `W₁ ≠ 0` at `(x̄(1 − R), v(x̄))`,
then `z̄ = v(x̄)` satisfies `z̄ = W[x̄(1 − R), z̄]` and `R = W₂[x̄(1 − R), z̄]`. -/
theorem ex_6_10a_only_if (h : ConsHyp W one1 R β M) (hR1 : R < 1)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {x : ℝ} (hx : 0 < x)
    (hstat : cv (x * (1 - R)) ∈ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx.le⟩)
    {DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ}
    (hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW
      (cv (x * (1 - R)), v ⟨x, hx.le⟩))
    (hW1 : DW (cv 1, 0) ≠ 0) :
    W (cv (x * (1 - R))) (v ⟨x, hx.le⟩) = v ⟨x, hx.le⟩ ∧ DW (0, 1) = R := by
  have hR := h.R_pos
  set A₀ : Wealth := ⟨x, hx.le⟩
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W one1 R v) (budgetΓ one1) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hnext : nextWealth one1 R A₀.1 (cv (x * (1 - R))) = x := nextWealth_bar hR
  have hz : vext v (nextWealth one1 R A₀.1 (cv (x * (1 - R)))) = v A₀ := by
    rw [hnext, vext_of_nonneg v hx.le]
  have hCi : 0 < cv (x * (1 - R)) 0 := mul_pos hx (by linarith)
  have hdir := hasDerivAt_dir hDW
  rw [← hz] at hdir hDW
  have henv := ex_5_12c_envelope h hconc hnn hv (A₀ := A₀) hx hstat hCi hdir
  have heul := ex_5_12c_euler h hv hstat hCi (by rw [hnext]; exact hx)
    (by rw [hnext]; exact henv) hDW
  refine ⟨?_, ?_⟩
  · have := hstat.2
    rw [← hvx] at this
    simp only [consObj, hz] at this
    exact this
  · simp only [one1, div_one] at heul
    rw [single_eq_cv] at heul
    field_simp at heul
    linarith

/-! ### Exercise 6.10c: additively separable preferences -/

/-- **Exercise 6.10c (`β = R`).** With `W(c, z) = U(c) + βz` and `β = R`, every wealth level is
stationary: consuming the interest `x(1 − R)` is optimal at every `x`. -/
theorem ex_6_10c_eq {U U' : ℝ → ℝ} (hW : ∀ C z, W C z = U (C 0) + β * z)
    (h : ConsHyp W one1 R β M) (hβR : β = R)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    (hU : ∀ c, 0 ≤ c → HasDerivAt U (U' c) c) (hU' : ∀ c, 0 ≤ c → 0 ≤ U' c)
    {x : ℝ} (hx : 0 ≤ x) :
    cv (x * (1 - R)) ∈ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx⟩ := by
  have hβ1 := h.β_lt
  set c := x * (1 - R)
  have hc : 0 ≤ c := mul_nonneg hx (by linarith)
  set z := U c / (1 - β)
  set DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ := U' c • ((ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)) + β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ
  have hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (cv c, z) := by
    have h1 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0))
        (U' c • ((ContinuousLinearMap.proj 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ))) (cv c, z) := by
      have := (hU c hc).comp_hasFDerivAt (cv c, z)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)).hasFDerivAt)
      simpa [cv, Function.comp_def] using this
    have h2 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => β * q.2)
        (β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ) (cv c, z) :=
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ).hasFDerivAt.const_mul β
    have e : (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) =
        (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0)) + fun q => β * q.2 := by
      funext q; simp [hW]
    rw [e]
    exact h1.add h2
  have hz : W (cv c) z = z := by
    have : (1 : ℝ) - β ≠ 0 := by linarith
    rw [hW]; simp only [cv, z]; field_simp; ring
  have hW2 : DW (0, 1) = R := by simp [DW, hβR]
  have hW1 : 0 ≤ DW (cv 1, 0) := by simp [DW, cv, hU' c hc]
  exact (ex_6_10a_if h (hβR ▸ hβ1) hconc hnn hv hx hz hDW hW2 hW1).1

/-- **Exercise 6.10c (`β ≠ R`).** With `W(c, z) = U(c) + βz`, `β ≠ R` and `U' ≠ 0`, no positive
wealth level is stationary. -/
theorem ex_6_10c_ne {U U' : ℝ → ℝ} (hW : ∀ C z, W C z = U (C 0) + β * z)
    (h : ConsHyp W one1 R β M) (hR1 : R < 1) (hβR : β ≠ R)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    (hU : ∀ c, 0 ≤ c → HasDerivAt U (U' c) c) (hU' : ∀ c, 0 < c → U' c ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    cv (x * (1 - R)) ∉ argmax (consObj W one1 R v) (budgetΓ one1) ⟨x, hx.le⟩ := by
  intro hstat
  set c := x * (1 - R)
  have hc : 0 < c := mul_pos hx (by linarith)
  set DW : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ := U' c • ((ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)) + β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ
  have hDW : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW (cv c, v ⟨x, hx.le⟩) := by
    have h1 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0))
        (U' c • ((ContinuousLinearMap.proj 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ))) (cv c, v ⟨x, hx.le⟩) := by
      have := (hU c hc.le).comp_hasFDerivAt (cv c, v ⟨x, hx.le⟩)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ)).hasFDerivAt)
      simpa [cv, Function.comp_def] using this
    have h2 : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => β * q.2)
        (β • ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ) (cv c, v ⟨x, hx.le⟩) :=
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ).hasFDerivAt.const_mul β
    have e : (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) =
        (fun q : (Fin 1 → ℝ) × ℝ => U (q.1 0)) + fun q => β * q.2 := by
      funext q; simp [hW]
    rw [e]
    exact h1.add h2
  have hW1 : DW (cv 1, 0) ≠ 0 := by simpa [DW, cv] using hU' c hc
  have := (ex_6_10a_only_if h hR1 hconc hnn hv hx hstat hDW hW1).2
  have hb : DW (0, 1) = β := by simp [DW]
  exact hβR (hb.symm.trans this)

/-- **Exercise 6.10d: the Euler equation.** Along an optimal path with positive consumption and
wealth, `W₁(c₀, z₁) = R⁻¹W₂(c₀, z₁)W₁(c₁, z₂)`. -/
theorem ex_6_10d (h : ConsHyp W one1 R β M)
    (hconc : ConcaveOn ℝ ({C : Fin 1 → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ A₁ : Wealth} {C₀ C₁ : Fin 1 → ℝ}
    (hC₀ : C₀ ∈ argmax (consObj W one1 R v) (budgetΓ one1) A₀) (hc₀ : 0 < C₀ 0)
    (hA₁ : A₁.1 = nextWealth one1 R A₀.1 C₀) (hA₁0 : 0 < A₁.1)
    (hC₁ : C₁ ∈ argmax (consObj W one1 R v) (budgetΓ one1) A₁) (hc₁ : 0 < C₁ 0)
    {DW₀ DW₁ : (Fin 1 → ℝ) × ℝ →L[ℝ] ℝ}
    (hDW₀ : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW₀
      (C₀, vext v (nextWealth one1 R A₀.1 C₀)))
    (hDW₁ : HasFDerivAt (fun q : (Fin 1 → ℝ) × ℝ => W q.1 q.2) DW₁
      (C₁, vext v (nextWealth one1 R A₁.1 C₁))) :
    DW₀ (cv 1, 0) = DW₀ (0, 1) * DW₁ (cv 1, 0) / R := by
  have henv := ex_5_12c_envelope h hconc hnn hv hA₁0 hC₁ hc₁ (hasDerivAt_dir hDW₁)
  rw [hA₁] at henv hA₁0
  have heul := ex_5_12c_euler h hv hC₀ hc₀ hA₁0 henv hDW₀
  simp only [one1, div_one, single_eq_cv] at heul
  exact heul

end StokeyLucasPrescott.DeterministicDynamics

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.DeterministicDynamics.addIso
#print axioms StokeyLucasPrescott.DeterministicDynamics.addIso_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.mulIso
#print axioms StokeyLucasPrescott.DeterministicDynamics.mulIso_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.add_mul_biSup
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_add_mul
#print axioms StokeyLucasPrescott.DeterministicDynamics.coe_mul_add
#print axioms StokeyLucasPrescott.DeterministicDynamics.le_of_le_add_limsup
#print axioms StokeyLucasPrescott.DeterministicDynamics.le_of_add_le_liminf
#print axioms StokeyLucasPrescott.DeterministicDynamics.le_of_forall_coe_lt_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.eq_biSup_iff
#print axioms StokeyLucasPrescott.DeterministicDynamics.Feasible
#print axioms StokeyLucasPrescott.DeterministicDynamics.partialSum
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption41
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption42
#print axioms StokeyLucasPrescott.DeterministicDynamics.total
#print axioms StokeyLucasPrescott.DeterministicDynamics.vstar
#print axioms StokeyLucasPrescott.DeterministicDynamics.SatisfiesFE
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_total
#print axioms StokeyLucasPrescott.DeterministicDynamics.tail
#print axioms StokeyLucasPrescott.DeterministicDynamics.tail_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.tail_tail
#print axioms StokeyLucasPrescott.DeterministicDynamics.consPlan
#print axioms StokeyLucasPrescott.DeterministicDynamics.consPlan_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.tail_consPlan
#print axioms StokeyLucasPrescott.DeterministicDynamics.feasible_nonempty
#print axioms StokeyLucasPrescott.DeterministicDynamics.partialSum_succ
#print axioms StokeyLucasPrescott.DeterministicDynamics.partialSum_succ'
#print axioms StokeyLucasPrescott.DeterministicDynamics.lemma_4_1
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_2
#print axioms StokeyLucasPrescott.DeterministicDynamics.total_le_of_FE
#print axioms StokeyLucasPrescott.DeterministicDynamics.div_lt_of_lt_add_mul
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_4_3a
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_3
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_4_3b
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_4
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_4_beta_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_5
#print axioms StokeyLucasPrescott.DeterministicDynamics.Gstar
#print axioms StokeyLucasPrescott.DeterministicDynamics.optimal_generated_by_Gstar
#print axioms StokeyLucasPrescott.DeterministicDynamics.generated_by_Gstar_optimal
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_of_summable_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_of_summable_neg
#print axioms StokeyLucasPrescott.DeterministicDynamics.assumption42_of_summable_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.assumption42_of_summable_neg
#print axioms StokeyLucasPrescott.DeterministicDynamics.summable_max_of_le_geometric
#print axioms StokeyLucasPrescott.DeterministicDynamics.assumption42_of_bddAbove
#print axioms StokeyLucasPrescott.DeterministicDynamics.assumption42_of_bddBelow
#print axioms StokeyLucasPrescott.DeterministicDynamics.assumption42_of_geometric
#print axioms StokeyLucasPrescott.DeterministicDynamics.Orthant
#print axioms StokeyLucasPrescott.DeterministicDynamics.orthCombo
#print axioms StokeyLucasPrescott.DeterministicDynamics.orthZero
#print axioms StokeyLucasPrescott.DeterministicDynamics.orthOne
#print axioms StokeyLucasPrescott.DeterministicDynamics.norm_le_geometric
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_4_2a
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_4_2b
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_4_1a
#print axioms StokeyLucasPrescott.DeterministicDynamics.consSet
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_4_1b
#print axioms StokeyLucasPrescott.DeterministicDynamics.IsContraction
#print axioms StokeyLucasPrescott.DeterministicDynamics.IsContraction.uniformContinuous
#print axioms StokeyLucasPrescott.DeterministicDynamics.dist_iterate_succ_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.dist_iterate_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.cauchySeq_iterate
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_3_2
#print axioms StokeyLucasPrescott.DeterministicDynamics.dist_fixedPoint_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.corollary_1
#print axioms StokeyLucasPrescott.DeterministicDynamics.corollary_2
#print axioms StokeyLucasPrescott.DeterministicDynamics.IsLHC
#print axioms StokeyLucasPrescott.DeterministicDynamics.IsUHC
#print axioms StokeyLucasPrescott.DeterministicDynamics.graph
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuousAt_of_isUHC_singleton
#print axioms StokeyLucasPrescott.DeterministicDynamics.isCompact_graph
#print axioms StokeyLucasPrescott.DeterministicDynamics.maxValue
#print axioms StokeyLucasPrescott.DeterministicDynamics.argmax
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuousOn_section
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_argmax
#print axioms StokeyLucasPrescott.DeterministicDynamics.le_maxValue
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_f_graph
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_3_6
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.nonempty
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.compact
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.lhc
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.uhc
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.unique
#print axioms StokeyLucasPrescott.DeterministicDynamics.argmaxFn
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.argmaxFn_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.argmax_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.lt_of_ne
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.continuous_argmaxFn
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.lemma_3_7
#print axioms StokeyLucasPrescott.DeterministicDynamics.UniqueArgmax.lemma_3_7_uniform
#print axioms StokeyLucasPrescott.DeterministicDynamics.shortfall_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_3_8
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_3_8_uniform
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption43
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption43.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption43.nonempty
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption43.compact
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption43.lhc
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption43.uhc
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption44
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption44.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption44.cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption44.bdd
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption44.β_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption44.β_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.obj
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuousOn_obj
#print axioms StokeyLucasPrescott.DeterministicDynamics.bound_maxValue
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_bellman_argmax
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_add_const
#print axioms StokeyLucasPrescott.DeterministicDynamics.blackwell
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_contraction
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_6
#print axioms StokeyLucasPrescott.DeterministicDynamics.curryF
#print axioms StokeyLucasPrescott.DeterministicDynamics.assumption42_of_44
#print axioms StokeyLucasPrescott.DeterministicDynamics.satisfiesFE_of_fixed
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_bounded_discount
#print axioms StokeyLucasPrescott.DeterministicDynamics.fixedPoint_eq_vstar
#print axioms StokeyLucasPrescott.DeterministicDynamics.policy_plan_optimal
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_7
#print axioms StokeyLucasPrescott.DeterministicDynamics.cmb
#print axioms StokeyLucasPrescott.DeterministicDynamics.cmb_self
#print axioms StokeyLucasPrescott.DeterministicDynamics.IsConcaveS
#print axioms StokeyLucasPrescott.DeterministicDynamics.IsStrictConcaveS
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption47
#print axioms StokeyLucasPrescott.DeterministicDynamics.Assumption48
#print axioms StokeyLucasPrescott.DeterministicDynamics.isClosed_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_maps_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.argmax_unique_of_strictConcave
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_8
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_9
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_10
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_4_5
#print axioms StokeyLucasPrescott.DeterministicDynamics.dual_apply_eq_sum
#print axioms StokeyLucasPrescott.DeterministicDynamics.vertex
#print axioms StokeyLucasPrescott.DeterministicDynamics.no_separation
#print axioms StokeyLucasPrescott.DeterministicDynamics.eventually_mem_of_mem_interior
#print axioms StokeyLucasPrescott.DeterministicDynamics.liftS
#print axioms StokeyLucasPrescott.DeterministicDynamics.liftS_of_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.IsStrictConcaveS.isConcaveS
#print axioms StokeyLucasPrescott.DeterministicDynamics.concaveOn_liftS
#print axioms StokeyLucasPrescott.DeterministicDynamics.convex_image_Γ
#print axioms StokeyLucasPrescott.DeterministicDynamics.eventually_mem_Γ
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_11
#print axioms StokeyLucasPrescott.DeterministicDynamics.concave_le_fderiv
#print axioms StokeyLucasPrescott.DeterministicDynamics.Fx
#print axioms StokeyLucasPrescott.DeterministicDynamics.Fy
#print axioms StokeyLucasPrescott.DeterministicDynamics.apply_eq_Fx_add_Fy
#print axioms StokeyLucasPrescott.DeterministicDynamics.euler_telescope
#print axioms StokeyLucasPrescott.DeterministicDynamics.le_of_le_add_tendsto_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.euler_sufficient
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_4_15
#print axioms StokeyLucasPrescott.DeterministicDynamics.euler_of_envelope
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.U_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.U_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.f_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.f_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.xbar_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.f_maintain
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthHyp.f_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.growthΓ
#print axioms StokeyLucasPrescott.DeterministicDynamics.growthF
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_f_nonneg
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_growth_f
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_assumption43
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_assumption44
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_a45
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_a46
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_assumption41
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_assumption42
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_1ab
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_a47
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_a48
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_1c
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_1c_weak_counterexample
#print axioms StokeyLucasPrescott.DeterministicDynamics.growthF_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_concave_growth
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.chord_step
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_strictConcave
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_1c_weak
#print axioms StokeyLucasPrescott.DeterministicDynamics.liftR
#print axioms StokeyLucasPrescott.DeterministicDynamics.liftR_of_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.concaveOn_liftR
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_1d
#print axioms StokeyLucasPrescott.DeterministicDynamics.eventually_slope_ge
#print axioms StokeyLucasPrescott.DeterministicDynamics.slope_le_chord
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_1d_interior
#print axioms StokeyLucasPrescott.DeterministicDynamics.concave_exchange
#print axioms StokeyLucasPrescott.DeterministicDynamics.growthF_increasingDiff
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_sub_monotone
#print axioms StokeyLucasPrescott.DeterministicDynamics.discounted_value_monotone
#print axioms StokeyLucasPrescott.DeterministicDynamics.policy_le_of_discount_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_1e
#print axioms StokeyLucasPrescott.DeterministicDynamics.investG
#print axioms StokeyLucasPrescott.DeterministicDynamics.investH
#print axioms StokeyLucasPrescott.DeterministicDynamics.invest_fe
#print axioms StokeyLucasPrescott.DeterministicDynamics.invest_telescope
#print axioms StokeyLucasPrescott.DeterministicDynamics.invest_partialSum_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.invest_plan_tendsto
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_max_sublinear
#print axioms StokeyLucasPrescott.DeterministicDynamics.invest_euler
#print axioms StokeyLucasPrescott.DeterministicDynamics.clamp_maximizes
#print axioms StokeyLucasPrescott.DeterministicDynamics.bounded_policy
#print axioms StokeyLucasPrescott.DeterministicDynamics.intervalΓ
#print axioms StokeyLucasPrescott.DeterministicDynamics.intervalΓ_assumption43
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_concave_of_concaveF
#print axioms StokeyLucasPrescott.DeterministicDynamics.fixed_concave_of_concaveF
#print axioms StokeyLucasPrescott.DeterministicDynamics.concaveOn_liftR_of_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_bound_Icc_prod
#print axioms StokeyLucasPrescott.DeterministicDynamics.investF
#print axioms StokeyLucasPrescott.DeterministicDynamics.boundedΓ
#print axioms StokeyLucasPrescott.DeterministicDynamics.bounded_assumption43
#print axioms StokeyLucasPrescott.DeterministicDynamics.bounded_assumption44
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9a_bounds
#print axioms StokeyLucasPrescott.DeterministicDynamics.adjF
#print axioms StokeyLucasPrescott.DeterministicDynamics.fullΓ
#print axioms StokeyLucasPrescott.DeterministicDynamics.full_assumption43
#print axioms StokeyLucasPrescott.DeterministicDynamics.mem_fullΓ
#print axioms StokeyLucasPrescott.DeterministicDynamics.adj_assumption44
#print axioms StokeyLucasPrescott.DeterministicDynamics.adj_a47
#print axioms StokeyLucasPrescott.DeterministicDynamics.full_a48
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.p_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.δ_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.δ_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.K_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.f_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.f_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.c_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.c_convex
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.h43
#print axioms StokeyLucasPrescott.DeterministicDynamics.AdjHyp.h44
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9b
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9b_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9b_slope
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9b_envelope
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9b_foc
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9b_euler
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_9b_steady
#print axioms StokeyLucasPrescott.DeterministicDynamics.profitPi
#print axioms StokeyLucasPrescott.DeterministicDynamics.profitPi_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.labor_demand_exists
#print axioms StokeyLucasPrescott.DeterministicDynamics.labor_demand_unique
#print axioms StokeyLucasPrescott.DeterministicDynamics.profitPi_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.profitPi_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.profitPi_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.profitPi_strictConcave
#print axioms StokeyLucasPrescott.DeterministicDynamics.profitPi_deriv
#print axioms StokeyLucasPrescott.DeterministicDynamics.seqSet
#print axioms StokeyLucasPrescott.DeterministicDynamics.Seq
#print axioms StokeyLucasPrescott.DeterministicDynamics.convex_seqSet
#print axioms StokeyLucasPrescott.DeterministicDynamics.shiftSeq
#print axioms StokeyLucasPrescott.DeterministicDynamics.shiftSeq_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_shiftSeq
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_head
#print axioms StokeyLucasPrescott.DeterministicDynamics.abs_apply_le_norm
#print axioms StokeyLucasPrescott.DeterministicDynamics.zeroSeq
#print axioms StokeyLucasPrescott.DeterministicDynamics.shiftSeq_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.trunc
#print axioms StokeyLucasPrescott.DeterministicDynamics.trunc_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.head_trunc
#print axioms StokeyLucasPrescott.DeterministicDynamics.shiftSeq_trunc_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.shiftSeq_trunc_succ
#print axioms StokeyLucasPrescott.DeterministicDynamics.opTU
#print axioms StokeyLucasPrescott.DeterministicDynamics.opTU_contraction
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11c
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11a
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11b_complete
#print axioms StokeyLucasPrescott.DeterministicDynamics.eventuallyZero
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11b_counterexample
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp.cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp.zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp.bdd
#print axioms StokeyLucasPrescott.DeterministicDynamics.AggHyp.lip
#print axioms StokeyLucasPrescott.DeterministicDynamics.opTW
#print axioms StokeyLucasPrescott.DeterministicDynamics.opTW_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.opTW_contraction
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11d
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11d_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.monotoneOn_of_concave_nonneg
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11d_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.bump
#print axioms StokeyLucasPrescott.DeterministicDynamics.shiftSeq_bump_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.shiftSeq_bump_succ
#print axioms StokeyLucasPrescott.DeterministicDynamics.head_bump_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.head_bump_succ
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_11e
#print axioms StokeyLucasPrescott.DeterministicDynamics.Wealth
#print axioms StokeyLucasPrescott.DeterministicDynamics.spend
#print axioms StokeyLucasPrescott.DeterministicDynamics.budgetΓ
#print axioms StokeyLucasPrescott.DeterministicDynamics.nextWealth
#print axioms StokeyLucasPrescott.DeterministicDynamics.vext
#print axioms StokeyLucasPrescott.DeterministicDynamics.vext_of_nonneg
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_vext
#print axioms StokeyLucasPrescott.DeterministicDynamics.abs_vext_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_spend
#print axioms StokeyLucasPrescott.DeterministicDynamics.spend_nonneg
#print axioms StokeyLucasPrescott.DeterministicDynamics.le_div_of_spend
#print axioms StokeyLucasPrescott.DeterministicDynamics.norm_le_of_budget
#print axioms StokeyLucasPrescott.DeterministicDynamics.budget_compact
#print axioms StokeyLucasPrescott.DeterministicDynamics.zero_mem_budget
#print axioms StokeyLucasPrescott.DeterministicDynamics.budget_lhc
#print axioms StokeyLucasPrescott.DeterministicDynamics.budget_uhc
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.p_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.R_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.bdd
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.lip
#print axioms StokeyLucasPrescott.DeterministicDynamics.consObj
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_consObj
#print axioms StokeyLucasPrescott.DeterministicDynamics.abs_consObj_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.consMax_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.consT
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_consT_argmax
#print axioms StokeyLucasPrescott.DeterministicDynamics.consT_contraction
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12b
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12b_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12b_demand
#print axioms StokeyLucasPrescott.DeterministicDynamics.ConsHyp.smul
#print axioms StokeyLucasPrescott.DeterministicDynamics.spend_smul
#print axioms StokeyLucasPrescott.DeterministicDynamics.scaleW
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12b_homogeneous
#print axioms StokeyLucasPrescott.DeterministicDynamics.spend_add_smul_single
#print axioms StokeyLucasPrescott.DeterministicDynamics.concaveOn_vext
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12c_envelope
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12c_intratemporal
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12c_euler
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12d
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_5_12d_not_aggregator
#print axioms StokeyLucasPrescott.DeterministicDynamics.tangent_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.tangent_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.deriv_le_of_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.deriv_lt_of_strictConcave
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.β_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.β_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f_deriv
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f'_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f_conc
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f'_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f'_top
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U_deriv
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U'_cont
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U_conc
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U'_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f'_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U'_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.U'_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.f_ge_tangent
#print axioms StokeyLucasPrescott.DeterministicDynamics.GrowthDyn.mul_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_kbar
#print axioms StokeyLucasPrescott.DeterministicDynamics.growthHyp_kbar
#print axioms StokeyLucasPrescott.DeterministicDynamics.gpol
#print axioms StokeyLucasPrescott.DeterministicDynamics.gpol_of_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.strictConcaveOn_liftR
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.dyn
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.kbar_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.kbar_fix
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.below
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.fixed
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.hyp
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.inada
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.weak
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.gpol_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.gpol_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.gpol_interior
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.gpol_lt_kbar
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.continuousOn_gpol
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.hasDerivAt_v
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.foc
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.strictConcave_v
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_1a
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_1b
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_kstar
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.five
#print axioms StokeyLucasPrescott.DeterministicDynamics.Setting61.fixed_iff
#print axioms StokeyLucasPrescott.DeterministicDynamics.prop_6_1
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_setting61
#print axioms StokeyLucasPrescott.DeterministicDynamics.bmF
#print axioms StokeyLucasPrescott.DeterministicDynamics.chord_error_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.lipschitz_of_deriv_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.bmF_gap
#print axioms StokeyLucasPrescott.DeterministicDynamics.bmK
#print axioms StokeyLucasPrescott.DeterministicDynamics.one_le_bmK
#print axioms StokeyLucasPrescott.DeterministicDynamics.bm_gap_ge
#print axioms StokeyLucasPrescott.DeterministicDynamics.bmFs
#print axioms StokeyLucasPrescott.DeterministicDynamics.bm_assumption43
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_bmFs
#print axioms StokeyLucasPrescott.DeterministicDynamics.bm_assumption44
#print axioms StokeyLucasPrescott.DeterministicDynamics.bm_assumption47
#print axioms StokeyLucasPrescott.DeterministicDynamics.bm_assumption48
#print axioms StokeyLucasPrescott.DeterministicDynamics.bm_assumption49
#print axioms StokeyLucasPrescott.DeterministicDynamics.bmV
#print axioms StokeyLucasPrescott.DeterministicDynamics.bm_obj
#print axioms StokeyLucasPrescott.DeterministicDynamics.bellman_bm
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_6_1
#print axioms StokeyLucasPrescott.DeterministicDynamics.logistic
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_3a
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_3b_values
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_3b_two_cycle
#print axioms StokeyLucasPrescott.DeterministicDynamics.logistic_sin_sq
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_3b_three_cycle
#print axioms StokeyLucasPrescott.DeterministicDynamics.lemma_6_2
#print axioms StokeyLucasPrescott.DeterministicDynamics.lemma_6_2_book
#print axioms StokeyLucasPrescott.DeterministicDynamics.valueLoss
#print axioms StokeyLucasPrescott.DeterministicDynamics.valueLoss_nonpos
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.fix
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.mem_bar
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.three
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.four
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.five
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.six
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.seven
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.valueLoss_beta_one
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.valueLoss_of_eight
#print axioms StokeyLucasPrescott.DeterministicDynamics.LossFacts.valueLoss_of_eight_strict
#print axioms StokeyLucasPrescott.DeterministicDynamics.globally_stable
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_4_form
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_4
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_4_book_condition_fails
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_4_stationary
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_4_not_unique
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_4_unique_of_eight
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_zero_of_le_rec
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_zero_of_rec
#print axioms StokeyLucasPrescott.DeterministicDynamics.stableSubspace
#print axioms StokeyLucasPrescott.DeterministicDynamics.unstableSubspace
#print axioms StokeyLucasPrescott.DeterministicDynamics.convSubspace
#print axioms StokeyLucasPrescott.DeterministicDynamics.mem_convSubspace
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_of_mem_maxGenEigenspace
#print axioms StokeyLucasPrescott.DeterministicDynamics.not_tendsto_of_eigen
#print axioms StokeyLucasPrescott.DeterministicDynamics.stable_le_conv
#print axioms StokeyLucasPrescott.DeterministicDynamics.stable_sup_unstable
#print axioms StokeyLucasPrescott.DeterministicDynamics.disjoint_stable_unstable
#print axioms StokeyLucasPrescott.DeterministicDynamics.unstable_invariant
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_iff_mem_stable
#print axioms StokeyLucasPrescott.DeterministicDynamics.stable_eq_top
#print axioms StokeyLucasPrescott.DeterministicDynamics.cplx
#print axioms StokeyLucasPrescott.DeterministicDynamics.cplx_sub
#print axioms StokeyLucasPrescott.DeterministicDynamics.cplx_add
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_cplx_iff
#print axioms StokeyLucasPrescott.DeterministicDynamics.cplxEnd
#print axioms StokeyLucasPrescott.DeterministicDynamics.cplxEnd_pow_cplx
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasEigenvalue_cplxEnd_iff
#print axioms StokeyLucasPrescott.DeterministicDynamics.deviation_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_6_3
#print axioms StokeyLucasPrescott.DeterministicDynamics.triangular_step
#print axioms StokeyLucasPrescott.DeterministicDynamics.triangular_invariant
#print axioms StokeyLucasPrescott.DeterministicDynamics.triangular_tendsto_iff
#print axioms StokeyLucasPrescott.DeterministicDynamics.map_pow_mulVec_cplx
#print axioms StokeyLucasPrescott.DeterministicDynamics.conj_pow
#print axioms StokeyLucasPrescott.DeterministicDynamics.solution_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_6_4
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_pow_mulVec
#print axioms StokeyLucasPrescott.DeterministicDynamics.matCLM
#print axioms StokeyLucasPrescott.DeterministicDynamics.matCLM_pow_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_opNorm_pow
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_6_5
#print axioms StokeyLucasPrescott.DeterministicDynamics.eulerJ
#print axioms StokeyLucasPrescott.DeterministicDynamics.eulerK
#print axioms StokeyLucasPrescott.DeterministicDynamics.eulerA
#print axioms StokeyLucasPrescott.DeterministicDynamics.det_fromBlocks_one_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.det_char_block
#print axioms StokeyLucasPrescott.DeterministicDynamics.det_char_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.root_inv_of_root
#print axioms StokeyLucasPrescott.DeterministicDynamics.fxy_mul_eulerJ
#print axioms StokeyLucasPrescott.DeterministicDynamics.fxy_mul_eulerK
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_5
#print axioms StokeyLucasPrescott.DeterministicDynamics.lemma_6_7
#print axioms StokeyLucasPrescott.DeterministicDynamics.quadRoot
#print axioms StokeyLucasPrescott.DeterministicDynamics.quadRoot_real
#print axioms StokeyLucasPrescott.DeterministicDynamics.growth_roots
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_6
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdF
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdFx
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdFy
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdFxx
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdFyy
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdFxy
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasDerivAt_cdF_k
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasDerivAt_cdF_y
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasDerivAt_cdFx_k
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasDerivAt_cdFx_y
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasDerivAt_cdFy_y
#print axioms StokeyLucasPrescott.DeterministicDynamics.euler_steady
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7b
#print axioms StokeyLucasPrescott.DeterministicDynamics.kstar_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.linearization_B
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7c
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7c_stable_iff
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7d
#print axioms StokeyLucasPrescott.DeterministicDynamics.geomMean_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.cd_concave
#print axioms StokeyLucasPrescott.DeterministicDynamics.cd_not_strict
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasFDerivAt_cd
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdΓ
#print axioms StokeyLucasPrescott.DeterministicDynamics.cyc
#print axioms StokeyLucasPrescott.DeterministicDynamics.cyc_succ
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdF_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.feasible_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.summable_plan
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_partialSum
#print axioms StokeyLucasPrescott.DeterministicDynamics.cd_assumption42
#print axioms StokeyLucasPrescott.DeterministicDynamics.total_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.cyc_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.cyc_feasible
#print axioms StokeyLucasPrescott.DeterministicDynamics.cycD
#print axioms StokeyLucasPrescott.DeterministicDynamics.cyc_sufficient
#print axioms StokeyLucasPrescott.DeterministicDynamics.sum_update
#print axioms StokeyLucasPrescott.DeterministicDynamics.cyc_necessary
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7e
#print axioms StokeyLucasPrescott.DeterministicDynamics.cycP
#print axioms StokeyLucasPrescott.DeterministicDynamics.rpow_fifth
#print axioms StokeyLucasPrescott.DeterministicDynamics.fifth_pow
#print axioms StokeyLucasPrescott.DeterministicDynamics.euler_iff_poly
#print axioms StokeyLucasPrescott.DeterministicDynamics.cycP_strictMono_y
#print axioms StokeyLucasPrescott.DeterministicDynamics.cycP_mono_x
#print axioms StokeyLucasPrescott.DeterministicDynamics.polyRoot
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_cycP
#print axioms StokeyLucasPrescott.DeterministicDynamics.polyRoot_spec
#print axioms StokeyLucasPrescott.DeterministicDynamics.polyRoot_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.lt_polyRoot
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuousAt_polyRoot
#print axioms StokeyLucasPrescott.DeterministicDynamics.cycle_q_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7f_book_box
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7f
#print axioms StokeyLucasPrescott.DeterministicDynamics.linJ
#print axioms StokeyLucasPrescott.DeterministicDynamics.linK
#print axioms StokeyLucasPrescott.DeterministicDynamics.linJK_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7g
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqQ
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqF
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqFx
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqFy
#print axioms StokeyLucasPrescott.DeterministicDynamics.dot_sym
#print axioms StokeyLucasPrescott.DeterministicDynamics.dot_transpose
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqF_add
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqQ_smul
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqQ_zero_left
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqQ_neg
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_lqQ
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_lqQ_bound
#print axioms StokeyLucasPrescott.DeterministicDynamics.abs_dot_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_lqF_bound
#print axioms StokeyLucasPrescott.DeterministicDynamics.lq_assumption42
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_of_total_ne_bot
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqQ_nonpos
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_lqF
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqD
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqD_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.lq_sufficient
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqF_midpoint
#print axioms StokeyLucasPrescott.DeterministicDynamics.lq_unique
#print axioms StokeyLucasPrescott.DeterministicDynamics.finrank_biSup_maxGenEigenspace
#print axioms StokeyLucasPrescott.DeterministicDynamics.finrank_stableSubspace
#print axioms StokeyLucasPrescott.DeterministicDynamics.re_cplxEnd_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.im_cplxEnd_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.re_cplxEnd_pow
#print axioms StokeyLucasPrescott.DeterministicDynamics.im_cplxEnd_pow
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_re_of_stable
#print axioms StokeyLucasPrescott.DeterministicDynamics.tendsto_im_of_stable
#print axioms StokeyLucasPrescott.DeterministicDynamics.eulerA_mulVec_inl
#print axioms StokeyLucasPrescott.DeterministicDynamics.eulerA_mulVec_inr
#print axioms StokeyLucasPrescott.DeterministicDynamics.orbit_rec
#print axioms StokeyLucasPrescott.DeterministicDynamics.euler_of_rec
#print axioms StokeyLucasPrescott.DeterministicDynamics.hom_euler_eq_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.stable_real_inr_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.stable_inr_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_stable_start
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqBar
#print axioms StokeyLucasPrescott.DeterministicDynamics.lqBar_stationary
#print axioms StokeyLucasPrescott.DeterministicDynamics.theorem_6_8
#print axioms StokeyLucasPrescott.DeterministicDynamics.orbit_tendsto_of_crossing
#print axioms StokeyLucasPrescott.DeterministicDynamics.roots_split
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_8c
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.adj
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.f_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.f_deriv
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.inada
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.c_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.c_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.c_strict
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.c_deriv
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.K_big
#print axioms StokeyLucasPrescott.DeterministicDynamics.fpol
#print axioms StokeyLucasPrescott.DeterministicDynamics.fpol_of_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.v_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.obj_le
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.fpol_mem
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.continuousOn_fpol
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.monotoneOn_fpol
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.fpol_zero_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.fpol_K_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.FirmDyn.steady_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_8a_unique
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_8
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdF_zero_left
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdF_one_right
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdF_nonneg
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdF_mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdF_strictMono
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_rpow_neg_gt
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.mk
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.a_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.b_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.ab
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.β_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.β_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.le
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.arg
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.conc
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.b_lt
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.mono
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.V_zero
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.lip_one
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.argmax_pos
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.argmax_lt_one
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.strictMonoOn
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.argmax_unique
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.hasDerivAt_V
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.foc
#print axioms StokeyLucasPrescott.DeterministicDynamics.CDValue.ex_6_2
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdFs
#print axioms StokeyLucasPrescott.DeterministicDynamics.continuous_cdFs
#print axioms StokeyLucasPrescott.DeterministicDynamics.cd_assumption43
#print axioms StokeyLucasPrescott.DeterministicDynamics.cd_assumption44
#print axioms StokeyLucasPrescott.DeterministicDynamics.cdValue_of_fixed
#print axioms StokeyLucasPrescott.DeterministicDynamics.mem_argmax_iff
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_2_fixed
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_7a
#print axioms StokeyLucasPrescott.DeterministicDynamics.cv
#print axioms StokeyLucasPrescott.DeterministicDynamics.one1
#print axioms StokeyLucasPrescott.DeterministicDynamics.spend_cv
#print axioms StokeyLucasPrescott.DeterministicDynamics.cv_nonneg
#print axioms StokeyLucasPrescott.DeterministicDynamics.eq_cv
#print axioms StokeyLucasPrescott.DeterministicDynamics.single_eq_cv
#print axioms StokeyLucasPrescott.DeterministicDynamics.exists_unique_fixed_z
#print axioms StokeyLucasPrescott.DeterministicDynamics.hasDerivAt_dir
#print axioms StokeyLucasPrescott.DeterministicDynamics.dw_apply
#print axioms StokeyLucasPrescott.DeterministicDynamics.nextWealth_bar
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_10a_if
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_10a_only_if
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_10c_eq
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_10c_ne
#print axioms StokeyLucasPrescott.DeterministicDynamics.ex_6_10d
