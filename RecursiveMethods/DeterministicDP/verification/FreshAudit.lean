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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

open Filter Topology Finset

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Why Theorems 4.3 and 4.5 need their boundedness conditions

SLP pp. 74–77: a consumer who values discounted consumption `Σ βᵗc_t`, with
`c_t = x_t − βx_{t+1}`, so `F(x, y) = x − βy`.

* Unrestricted borrowing, `Γ(x) = (−∞, x/β]` (`borrowΓ`): `v* ≡ +∞` (`borrow_vstar`), but
  `v(x) = x` also solves (FE) (`borrow_identity_FE`) and violates (8) along `x_t = β⁻ᵗx₀`
  (`borrow_identity_not_8`).
* No borrowing, `Γ(x) = [0, x/β]` on `ℝ₊` (`saveΓ`): `v*(x) = x` (`save_vstar`). Every feasible
  plan satisfies (9) (`save_all_satisfy_9`), but `x_t = β⁻ᵗx₀` yields `0` (`save_hoard_total`)
  and violates (11) (`save_hoard_not_11`).
-/

open Filter Topology Finset

namespace StokeyLucasPrescott.DeterministicDP

variable {β : ℝ}

/-- `F(x, y) = x − βy`: consumption when wealth `x` becomes `y` next period. -/
def consF (β : ℝ) (x y : ℝ) : ℝ := x - β * y

/-- Along any plan, `uₙ(x) = x₀ − βⁿ⁺¹x_{n+1}`. -/
theorem partialSum_consF (x : ℕ → ℝ) (n : ℕ) :
    partialSum (consF β) β x n = x 0 - β ^ (n + 1) * x (n + 1) := by
  induction n with
  | zero => simp [partialSum, consF]
  | succ n ih => rw [partialSum_succ', ih]; simp only [consF]; ring

/-- When `x_{t+1} ≤ x_t/β`, the terms `βᵗx_t` decrease, so the partial sums increase. -/
theorem monotone_partialSum_consF (hβ : 0 < β) {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) ≤ x t / β) :
    Monotone fun n => partialSum (consF β) β x n := by
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [partialSum_consF]
  have h := mul_le_mul_of_nonneg_left (hx (n + 1)) (pow_nonneg hβ.le (n + 2))
  have e : β ^ (n + 2) * (x (n + 1) / β) = β ^ (n + 1) * x (n + 1) := by
    field_simp; ring
  rw [e] at h
  linarith

/-! ### Unrestricted borrowing -/

/-- `Γ(x) = (−∞, x/β]`. -/
def borrowΓ (β : ℝ) (x : ℝ) : Set ℝ := Set.Iic (x / β)

theorem borrow_assumption41 : Assumption41 (borrowΓ β) := fun x => ⟨x / β, Set.mem_Iic.2 le_rfl⟩

theorem borrow_assumption42 (hβ : 0 < β) : Assumption42 (borrowΓ β) (consF β) β :=
  fun _ _ hx => ⟨_, tendsto_atTop_iSup fun _ _ hmn =>
    EReal.coe_le_coe_iff.2 (monotone_partialSum_consF hβ hx.2 hmn)⟩

/-- With unrestricted borrowing, `v* ≡ +∞`: the plan `x_t = (x₀ − t)/βᵗ` yields `n + 1` by
period `n`. -/
theorem borrow_vstar (hβ : 0 < β) (x₀ : ℝ) : vstar (borrowΓ β) (consF β) β x₀ = ⊤ := by
  set x : ℕ → ℝ := fun t => (x₀ - t) / β ^ t
  have hx : x ∈ Feasible (borrowΓ β) x₀ := ⟨by simp [x], fun t => by
    simp only [borrowΓ, Set.mem_Iic, x, pow_succ, Nat.cast_succ]
    rw [div_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  have hsum : ∀ n, partialSum (consF β) β x n = n + 1 := fun n => by
    rw [partialSum_consF]
    simp only [x, pow_zero, div_one, Nat.cast_zero, sub_zero, Nat.cast_succ]
    field_simp
    ring
  have htend : Tendsto (fun n => (partialSum (consF β) β x n : EReal)) atTop (𝓝 ⊤) := by
    simp only [hsum]
    refine EReal.tendsto_nhds_top_iff_real.2 fun r => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt r
    filter_upwards [eventually_ge_atTop N] with n hn
    exact EReal.coe_lt_coe_iff.2 (by linarith [(Nat.cast_le (α := ℝ)).2 hn])
  have htot : total (consF β) β x = ⊤ :=
    tendsto_nhds_unique (tendsto_total (borrow_assumption42 hβ) hx) htend
  have := le_biSup (f := total (consF β) β) hx
  rw [htot] at this
  exact top_le_iff.1 this

/-- `v(x) = x` also solves the functional equation. -/
theorem borrow_identity_FE :
    SatisfiesFE (borrowΓ β) (consF β) β fun x => (x : EReal) := by
  intro x
  have h : ∀ y, ((consF β x y : ℝ) : EReal) + (β : EReal) * (y : EReal) = (x : EReal) := by
    intro y; rw [← EReal.coe_mul, ← EReal.coe_add]; congr 1; simp only [consF]; ring
  simp only [h]
  exact (biSup_const (s := borrowΓ β x) ⟨x / β, Set.mem_Iic.2 le_rfl⟩).symm

/-- `v(x) = x` violates (8) along `x_t = β⁻ᵗx₀` when `x₀ ≠ 0`, so Theorem 4.3 does not apply. -/
theorem borrow_identity_not_8 (hβ : 0 < β) {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    (fun t : ℕ => x₀ / β ^ t) ∈ Feasible (borrowΓ β) x₀ ∧
      ¬ Tendsto (fun n => ((β ^ n : ℝ) : EReal) * ((x₀ / β ^ n : ℝ) : EReal)) atTop (𝓝 0) := by
  refine ⟨⟨by simp, fun t => by simp only [borrowΓ, Set.mem_Iic, pow_succ, div_div]; rfl⟩, ?_⟩
  have h : ∀ n : ℕ, ((β ^ n : ℝ) : EReal) * ((x₀ / β ^ n : ℝ) : EReal) = (x₀ : EReal) := by
    intro n; rw [← EReal.coe_mul]; congr 1; field_simp
  simp only [h, tendsto_const_nhds_iff]
  exact fun h0 => hx₀ (EReal.coe_eq_zero.1 h0)

/-! ### No borrowing -/

/-- The state space `ℝ₊`. -/
abbrev NNR := {x : ℝ // 0 ≤ x}

/-- `Γ(x) = [0, x/β]`. -/
def saveΓ (β : ℝ) (x : NNR) : Set NNR := {y | y.1 ≤ x.1 / β}

/-- `F(x, y) = x − βy` on `ℝ₊`. -/
def saveF (β : ℝ) (x y : NNR) : ℝ := x.1 - β * y.1

theorem save_partialSum (x : ℕ → NNR) (n : ℕ) :
    partialSum (saveF β) β x n = (x 0).1 - β ^ (n + 1) * (x (n + 1)).1 :=
  partialSum_consF (β := β) (fun t => (x t).1) n

theorem save_assumption41 (hβ : 0 < β) : Assumption41 (saveΓ β) :=
  fun x => ⟨⟨0, le_rfl⟩, div_nonneg x.2 hβ.le⟩

theorem save_assumption42 (hβ : 0 < β) : Assumption42 (saveΓ β) (saveF β) β := by
  intro _ x hx
  refine ⟨_, tendsto_atTop_iSup fun m n hmn => EReal.coe_le_coe_iff.2 ?_⟩
  have := monotone_partialSum_consF (β := β) (x := fun t => (x t).1) hβ (fun t => hx.2 t) hmn
  simpa only [save_partialSum, partialSum_consF] using this

/-- Without borrowing, `v*(x₀) = x₀`. -/
theorem save_vstar (hβ : 0 < β) (x₀ : NNR) : vstar (saveΓ β) (saveF β) β x₀ = (x₀.1 : EReal) := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) ?_
  · -- `uₙ = x₀ − βⁿ⁺¹x_{n+1} ≤ x₀`
    refine le_of_tendsto' (tendsto_total (save_assumption42 hβ) hx) fun n => ?_
    rw [save_partialSum, hx.1]
    exact EReal.coe_le_coe_iff.2 (by
      have := mul_nonneg (pow_nonneg hβ.le (n + 1)) (x (n + 1)).2; linarith)
  · -- eat everything at once
    set x : ℕ → NNR := fun t => if t = 0 then x₀ else ⟨0, le_rfl⟩
    have hx : x ∈ Feasible (saveΓ β) x₀ := ⟨rfl, fun t => by
      simp only [saveΓ, Set.mem_ofPred_eq, x, Nat.add_one_ne_zero, ↓reduceIte]
      split_ifs <;> simp [div_nonneg x₀.2 hβ.le]⟩
    have hc : ∀ n, partialSum (saveF β) β x n = x₀.1 := fun n => by
      rw [save_partialSum]; simp [x]
    have := tendsto_nhds_unique (tendsto_total (save_assumption42 hβ) hx)
      (by simp only [hc]; exact tendsto_const_nhds)
    exact this ▸ le_biSup (total (saveF β) β) hx

/-- Every feasible plan satisfies (9). -/
theorem save_all_satisfy_9 (hβ : 0 < β) {x₀ : NNR} {x : ℕ → NNR}
    (_hx : x ∈ Feasible (saveΓ β) x₀) (t : ℕ) :
    vstar (saveΓ β) (saveF β) β (x t) =
      (saveF β (x t) (x (t + 1)) : EReal) +
        (β : EReal) * vstar (saveΓ β) (saveF β) β (x (t + 1)) := by
  rw [save_vstar hβ, save_vstar hβ, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1; simp only [saveF]; ring

/-- The hoarding plan `x_t = β⁻ᵗx₀`. -/
noncomputable def hoard (β : ℝ) (hβ : 0 < β) (x₀ : NNR) (t : ℕ) : NNR :=
  ⟨x₀.1 / β ^ t, div_nonneg x₀.2 (pow_nonneg hβ.le t)⟩

theorem hoard_mem (hβ : 0 < β) (x₀ : NNR) : hoard β hβ x₀ ∈ Feasible (saveΓ β) x₀ :=
  ⟨by simp [hoard], fun t => by simp only [saveΓ, Set.mem_ofPred_eq, hoard, pow_succ, div_div]; rfl⟩

/-- Hoarding everything yields `0`, so for `x₀ > 0` it is not optimal although it satisfies (9). -/
theorem save_hoard_total (hβ : 0 < β) (x₀ : NNR) :
    total (saveF β) β (hoard β hβ x₀) = 0 := by
  have hc : ∀ n, partialSum (saveF β) β (hoard β hβ x₀) n = 0 := fun n => by
    rw [save_partialSum]; simp only [hoard, pow_zero, div_one]; field_simp; ring
  exact tendsto_nhds_unique (tendsto_total (save_assumption42 hβ) (hoard_mem hβ x₀))
    (by simp only [hc, EReal.coe_zero]; exact tendsto_const_nhds)

/-- The hoarding plan violates (11) when `x₀ > 0`: `βᵗv*(x_t) = x₀`. -/
theorem save_hoard_not_11 (hβ : 0 < β) {x₀ : NNR} (hx₀ : 0 < x₀.1) :
    ¬ limsup (fun t => ((β ^ t : ℝ) : EReal) *
      vstar (saveΓ β) (saveF β) β (hoard β hβ x₀ t)) atTop ≤ 0 := by
  have h : ∀ t : ℕ, ((β ^ t : ℝ) : EReal) * vstar (saveΓ β) (saveF β) β (hoard β hβ x₀ t) =
      (x₀.1 : EReal) := fun t => by
    rw [save_vstar hβ, ← EReal.coe_mul]; congr 1; simp only [hoard]; field_simp
  simp only [h, limsup_const]
  exact not_le.2 (EReal.coe_pos.2 hx₀)

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite or countable state spaces and policy iteration

SLP Exercise 4.4, pp. 82–83. `X` carries the discrete topology, so `X →ᵇ ℝ` is `B(X)`, the
bounded functions with the sup norm; `Γ` is nonempty and finite-valued; `F` is bounded on the
graph; `0 < β < 1`. (Countability of `X` is not used.)

* `bellmanD` (`T`), `ex_4_4a`: `T` maps `B(X)` into itself, has a unique fixed point `v`,
  `‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and the policy correspondence is nonempty.
* `policyOp` (`T_h`), `ex_4_4b`: for a feasible policy `h`, `T_h` has a unique fixed point.
* `ex_4_4c`: policy iteration. From any feasible `h₀`, alternate the value `wₙ` of `hₙ` with an
  improving policy `hₙ₊₁`; then `wₙ → v`, and `Tⁿw₀ ≤ wₙ ≤ v`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDP

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {Γ : X → Set X} {F : X → X → ℝ}
  {β : ℝ}

/-- The hypotheses of Exercise 4.4. -/
structure DiscreteSetup (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) : Prop where
  nonempty : ∀ x, (Γ x).Nonempty
  finite : ∀ x, (Γ x).Finite
  bdd : ∃ B, ∀ x, ∀ y ∈ Γ x, |F x y| ≤ B
  β_pos : 0 < β
  β_lt : β < 1

/-- `max_{y ∈ Γ(x)} [F(x, y) + βf(y)]`. -/
noncomputable def maxD (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  sSup ((fun y => F x y + β * f y) '' Γ x)

omit [TopologicalSpace X] [DiscreteTopology X] in
theorem exists_maxD (h : DiscreteSetup Γ F β) (f : X → ℝ) (x : X) :
    ∃ y ∈ Γ x, maxD Γ F β f x = F x y + β * f y ∧ ∀ z ∈ Γ x, F x z + β * f z ≤ F x y + β * f y := by
  obtain ⟨y, hy, hmax⟩ := Set.exists_max_image (Γ x) (fun y => F x y + β * f y) (h.finite x)
    (h.nonempty x)
  have hgr : IsGreatest ((fun y => F x y + β * f y) '' Γ x) (F x y + β * f y) :=
    ⟨⟨y, hy, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz⟩
  exact ⟨y, hy, hgr.csSup_eq, hmax⟩

omit [TopologicalSpace X] [DiscreteTopology X] in
theorem le_maxD (h : DiscreteSetup Γ F β) (f : X → ℝ) {x y : X} (hy : y ∈ Γ x) :
    F x y + β * f y ≤ maxD Γ F β f x := by
  obtain ⟨z, -, hz, hmax⟩ := exists_maxD h f x
  rw [hz]; exact hmax y hy

/-- The operator `T` on `B(X)`. -/
noncomputable def bellmanD (h : DiscreteSetup Γ F β) (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (maxD Γ F β f) (h.bdd.choose + β * ‖f‖) fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_maxD h f x
    rw [hval, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add (h.bdd.choose_spec x y hy) ?_)
    rw [abs_mul, abs_of_pos h.β_pos]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) h.β_pos.le

theorem bellmanD_apply (h : DiscreteSetup Γ F β) (f : X →ᵇ ℝ) (x : X) :
    bellmanD h f x = maxD Γ F β f x := rfl

theorem bellmanD_mono (h : DiscreteSetup Γ F β) {f g : X →ᵇ ℝ} (hfg : f ≤ g) :
    bellmanD h f ≤ bellmanD h g := fun x => by
  change maxD Γ F β f x ≤ maxD Γ F β g x
  obtain ⟨y, hy, hval, -⟩ := exists_maxD h f x
  rw [hval]
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (show f y ≤ g y from hfg y)
    h.β_pos.le)).trans (le_maxD h g hy)

theorem bellmanD_add_const (h : DiscreteSetup Γ F β) (f : X →ᵇ ℝ) (a : ℝ) :
    bellmanD h (f + const X a) ≤ bellmanD h f + const X (β * a) := fun x => by
  obtain ⟨y, hy, hval, -⟩ := exists_maxD h (f + const X a) x
  have h1 := le_maxD h f hy
  have e : bellmanD h (f + const X a) x = F x y + β * (f y + a) := by
    rw [bellmanD_apply, BoundedContinuousFunction.coe_add, hval]; simp
  have e2 : (bellmanD h f + const X (β * a)) x = maxD Γ F β f x + β * a := by
    simp [bellmanD_apply]
  change bellmanD h (f + const X a) x ≤ (bellmanD h f + const X (β * a)) x
  rw [e, e2]
  linarith

theorem bellmanD_contraction (h : DiscreteSetup Γ F β) : IsContraction (bellmanD h) β :=
  ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun _ _ => bellmanD_mono h)
    (fun f a _ => bellmanD_add_const h f a)⟩

/-- **Exercise 4.4a.** `T : B(X) → B(X)` has a unique fixed point `v`, (4) holds, and the
policy correspondence `G(x) = {y ∈ Γ(x) : v(x) = F(x, y) + βv(y)}` is nonempty. -/
theorem ex_4_4a (h : DiscreteSetup Γ F β) :
    ∃ v : X →ᵇ ℝ, bellmanD h v = v ∧ (∀ w, bellmanD h w = w → w = v) ∧
      (∀ v₀ (n : ℕ), dist ((bellmanD h)^[n] v₀) v ≤ β ^ n * dist v₀ v) ∧
      ∀ x, ∃ y ∈ Γ x, v x = F x y + β * v y := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 (bellmanD_contraction h)
  refine ⟨v, hv, huniq, hrate, fun x => ?_⟩
  obtain ⟨y, hy, hval, -⟩ := exists_maxD h v x
  refine ⟨y, hy, ?_⟩
  rw [← hval, ← bellmanD_apply h, hv]

/-- The policy operator `(T_h f)(x) = F(x, h(x)) + βf(h(x))`. -/
noncomputable def policyOp (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (fun x => F x (hp x) + β * f (hp x)) (h.bdd.choose + β * ‖f‖)
    fun x => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add (h.bdd.choose_spec x _ (hhp x)) ?_)
      rw [abs_mul, abs_of_pos h.β_pos]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) h.β_pos.le

theorem policyOp_apply (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    (f : X →ᵇ ℝ) (x : X) : policyOp h hp hhp f x = F x (hp x) + β * f (hp x) := rfl

theorem policyOp_mono (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    {f g : X →ᵇ ℝ} (hfg : f ≤ g) : policyOp h hp hhp f ≤ policyOp h hp hhp g := fun x => by
  change F x (hp x) + β * f (hp x) ≤ F x (hp x) + β * g (hp x)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (show f (hp x) ≤ g (hp x) from hfg _)
    h.β_pos.le)

theorem policyOp_contraction (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x) :
    IsContraction (policyOp h hp hhp) β :=
  ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun _ _ => policyOp_mono h hp hhp)
    (fun f a _ x => by
      change F x (hp x) + β * (f + const X a) (hp x) ≤
        (policyOp h hp hhp f + const X (β * a)) x
      simp only [BoundedContinuousFunction.add_apply, const_apply, policyOp_apply]
      linarith)⟩

/-- **Exercise 4.4b.** For every feasible policy `h`, `T_h : B(X) → B(X)` has a unique fixed
point. -/
theorem ex_4_4b (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x) :
    ∃ w : X →ᵇ ℝ, policyOp h hp hhp w = w ∧ ∀ w', policyOp h hp hhp w' = w' → w' = w := by
  obtain ⟨w, hw, huniq, -⟩ := theorem_3_2 (policyOp_contraction h hp hhp)
  exact ⟨w, hw, huniq⟩

/-- `T_h ≤ T`. -/
theorem policyOp_le_bellmanD (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    (f : X →ᵇ ℝ) : policyOp h hp hhp f ≤ bellmanD h f := fun x =>
  le_maxD h f (hhp x)

omit [DiscreteTopology X] in
/-- `{f : g ≤ f}` and `{f : f ≤ g}` are closed in `B(X)`. -/
theorem isClosed_ge (g : X →ᵇ ℝ) : IsClosed {f : X →ᵇ ℝ | g ≤ f} := by
  have : {f : X →ᵇ ℝ | g ≤ f} = ⋂ x, {f : X →ᵇ ℝ | g x ≤ f x} := by
    ext f; simp only [mem_ofPred_eq, mem_iInter]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_eval_const x)

omit [DiscreteTopology X] in
theorem isClosed_le' (g : X →ᵇ ℝ) : IsClosed {f : X →ᵇ ℝ | f ≤ g} := by
  have : {f : X →ᵇ ℝ | f ≤ g} = ⋂ x, {f : X →ᵇ ℝ | f x ≤ g x} := by
    ext f; simp only [mem_ofPred_eq, mem_iInter]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun x => isClosed_le (continuous_eval_const x) continuous_const

/-- **Exercise 4.4c (policy iteration).** Let `hₙ` be feasible policies and `wₙ` the fixed point
of `T_{hₙ}`, with `hₙ₊₁(x)` maximizing `F(x, y) + βwₙ(y)` over `Γ(x)`. Then
`w₀ ≤ Tw₀ ≤ w₁ ≤ Tw₁ ≤ ⋯`, `Tⁿw₀ ≤ wₙ ≤ v`, and `wₙ → v`. -/
theorem ex_4_4c (h : DiscreteSetup Γ F β) {v : X →ᵇ ℝ} (hv : bellmanD h v = v)
    (hp : ℕ → X → X) (hhp : ∀ n x, hp n x ∈ Γ x) (w : ℕ → X →ᵇ ℝ)
    (hw : ∀ n, policyOp h (hp n) (hhp n) (w n) = w n)
    (himp : ∀ n x, ∀ y ∈ Γ x, F x y + β * w n y ≤ F x (hp (n + 1) x) + β * w n (hp (n + 1) x)) :
    (∀ n, w n ≤ bellmanD h (w n) ∧ bellmanD h (w n) ≤ w (n + 1)) ∧
      (∀ n, (bellmanD h)^[n] (w 0) ≤ w n ∧ w n ≤ v) ∧ Tendsto w atTop (𝓝 v) := by
  -- `wₙ ≤ Twₙ`
  have h1 : ∀ n, w n ≤ bellmanD h (w n) := fun n => by
    rw [← hw n]
    exact (policyOp_le_bellmanD h _ _ _).trans (bellmanD_mono h (le_of_eq (hw n).symm))
  -- `Twₙ = T_{hₙ₊₁} wₙ`
  have h2 : ∀ n, bellmanD h (w n) = policyOp h (hp (n + 1)) (hhp (n + 1)) (w n) := fun n => by
    ext x
    refine le_antisymm ?_ (policyOp_le_bellmanD h _ _ _ x)
    change maxD Γ F β (w n) x ≤ _
    obtain ⟨y, hy, hval, -⟩ := exists_maxD h (w n) x
    rw [hval, policyOp_apply]
    exact himp n x y hy
  -- `Twₙ ≤ wₙ₊₁`: the set `{f : Twₙ ≤ f}` is closed and invariant under `T_{hₙ₊₁}`
  have h3 : ∀ n, bellmanD h (w n) ≤ w (n + 1) := fun n => by
    set g := bellmanD h (w n)
    have hinv : MapsTo (policyOp h (hp (n + 1)) (hhp (n + 1))) {f | g ≤ f} {f | g ≤ f} :=
      fun f hf => by
        have hg : g ≤ policyOp h (hp (n + 1)) (hhp (n + 1)) g := by
          have := policyOp_mono h (hp (n + 1)) (hhp (n + 1)) (h1 n)
          rwa [← h2 n] at this
        exact hg.trans (policyOp_mono h _ _ hf)
    exact (corollary_1 (S' := {f | g ≤ f}) (S'' := {f | g ≤ f}) (policyOp_contraction h _ _)
      (hw (n + 1)) ⟨g, (le_refl g : g ≤ g)⟩ (isClosed_ge g)
      hinv hinv).1
  -- `wₙ ≤ v`: the set `{f : f ≤ v}` is closed and invariant under `T_{hₙ}`
  have h4 : ∀ n, w n ≤ v := fun n => by
    have hinv : MapsTo (policyOp h (hp n) (hhp n)) {f | f ≤ v} {f | f ≤ v} := fun f hf =>
      (policyOp_le_bellmanD h _ _ f).trans ((bellmanD_mono h hf).trans (le_of_eq hv))
    exact (corollary_1 (S' := {f | f ≤ v}) (S'' := {f | f ≤ v}) (policyOp_contraction h _ _)
      (hw n) ⟨v, (le_refl v : v ≤ v)⟩ (isClosed_le' v)
      hinv hinv).1
  -- `Tⁿw₀ ≤ wₙ`
  have h5 : ∀ n, (bellmanD h)^[n] (w 0) ≤ w n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (bellmanD_mono h ih).trans (h3 n)
  refine ⟨fun n => ⟨h1 n, h3 n⟩, fun n => ⟨h5 n, h4 n⟩, ?_⟩
  -- squeeze: `dist (wₙ) v ≤ dist (Tⁿw₀) v → 0`
  obtain ⟨v', hv', huniq, hrate⟩ := theorem_3_2 (bellmanD_contraction h)
  rw [← huniq v hv] at hrate
  have hT : Tendsto (fun n => (bellmanD h)^[n] (w 0)) atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => hrate (w 0) n) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).mul_const
      (dist (w 0) v)
  rw [tendsto_iff_dist_tendsto_zero] at hT ⊢
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hT
  refine (dist_le dist_nonneg).2 fun x => ?_
  have a1 : (bellmanD h)^[n] (w 0) x ≤ w n x := h5 n x
  have a2 : w n x ≤ v x := h4 n x
  have a3 := dist_coe_le_dist (f := (bellmanD h)^[n] (w 0)) (g := v) x
  rw [Real.dist_eq] at a3 ⊢
  rw [abs_of_nonpos (by linarith)] at ⊢
  rw [abs_of_nonpos (by linarith)] at a3
  linarith

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Constant returns to scale

SLP §4.3, pp. 87–92. The state space is a cone `X` in a real normed space (`x ∈ X`, `λ ≥ 0`
imply `λx ∈ X`). Functions on `X` that are continuous and homogeneous of degree one, with
`|f(x)| ≤ M‖x‖`, form `H(X)` (`InH`), normed by `‖f‖ = sup_{‖x‖ = 1} |f(x)|` (`hnorm`).

* `abs_le_hnorm`: `|f(x)| ≤ ‖f‖‖x‖` on `H(X)`.
* `ex_4_7a_norm`, `ex_4_7a_complete`: `hnorm` is a norm on `H(X)`, and `H(X)` is complete.
* `theorem_4_12`: monotone operators on `H(X)` that discount by `γ` in the sense
  `T(f + a‖·‖) ≤ Tf + γa‖·‖` are contractions of modulus `γ`.
* `Assumption410`, `Assumption411`, `ex_4_6a`, `ex_4_6b`, `ex_4_6c`: feasible plans grow at most
  at rate `α`, the sequence problem is well defined, and `v*` is homogeneous with `|v*| ≤ c‖x‖`.
* `ex_4_7b`, `theorem_4_13`: `T` maps `H(X)` into itself and has a unique fixed point `v`, with
  `‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖`; the policy correspondence is compact-valued, u.h.c. and
  homogeneous; and `v = v*`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}

/-- `X` is a cone. -/
def IsCone (X : Set E) : Prop := ∀ x ∈ X, ∀ a : ℝ, 0 ≤ a → a • x ∈ X

/-- `ax` in the cone `X`, for `a ≥ 0`. -/
def csmul (hX : IsCone X) {a : ℝ} (ha : 0 ≤ a) (x : X) : X := ⟨a • x.1, hX x.1 x.2 a ha⟩

/-- `f : X → ℝ` is in `H(X)`: continuous, homogeneous of degree one and `|f(x)| ≤ M‖x‖`. -/
def InH (hX : IsCone X) (f : X → ℝ) : Prop :=
  Continuous f ∧ (∀ x (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x) = a * f x) ∧
    ∃ M, ∀ x, |f x| ≤ M * ‖x.1‖

/-- The norm (1), p. 89: `‖f‖ = sup_{‖x‖ = 1} |f(x)|`. -/
noncomputable def hnorm (X : Set E) (f : X → ℝ) : ℝ := ⨆ x : {x : X // ‖x.1‖ = 1}, |f x.1|

variable {hX : IsCone X}

omit [NormedSpace ℝ E] in
theorem hnorm_nonneg (f : X → ℝ) : 0 ≤ hnorm X f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [NormedSpace ℝ E] in
theorem bddAbove_sphere {f : X → ℝ} {M : ℝ} (hM : ∀ x, |f x| ≤ M * ‖x.1‖) :
    BddAbove (range fun x : {x : X // ‖x.1‖ = 1} => |f x.1|) :=
  ⟨M, by rintro _ ⟨x, rfl⟩; simpa [x.2] using hM x.1⟩

/-- On `H(X)`, `|f(x)| ≤ ‖f‖‖x‖`. -/
theorem abs_le_hnorm {f : X → ℝ} (hf : InH hX f) (x : X) : |f x| ≤ hnorm X f * ‖x.1‖ := by
  obtain ⟨M, hM⟩ := hf.2.2
  rcases eq_or_ne x.1 0 with h0 | h0
  · have : x = csmul hX le_rfl x := Subtype.ext (by simp [csmul, h0])
    rw [this, hf.2.1, zero_mul, abs_zero]
    exact mul_nonneg (hnorm_nonneg f) (norm_nonneg _)
  · have hn : 0 < ‖x.1‖ := norm_pos_iff.2 h0
    set u : X := csmul hX (inv_nonneg.2 hn.le) x
    have hu : ‖u.1‖ = 1 := by
      simp only [u, csmul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hxu : x = csmul hX hn.le u := Subtype.ext (by
      simp only [u, csmul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul])
    conv_lhs => rw [hxu, hf.2.1, abs_mul, abs_of_pos hn, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (le_ciSup (bddAbove_sphere hM) (⟨u, hu⟩ : {x : X // ‖x.1‖ = 1})) hn.le

omit [NormedSpace ℝ E] in
theorem hnorm_le {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x : X, ‖x.1‖ = 1 → |f x| ≤ C) :
    hnorm X f ≤ C :=
  Real.iSup_le (fun x => h x.1 x.2) hC

theorem inH_sub {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) : InH hX (f - g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.sub hg.1, fun x a ha => by simp [hf.2.1, hg.2.1, mul_sub], M + N, fun x => ?_⟩
  simp only [Pi.sub_apply]
  calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ M * ‖x.1‖ + N * ‖x.1‖ := add_le_add (hM x) (hN x)
    _ = (M + N) * ‖x.1‖ := by ring

theorem inH_add {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) : InH hX (f + g) := by
  obtain ⟨M, hM⟩ := hf.2.2
  obtain ⟨N, hN⟩ := hg.2.2
  refine ⟨hf.1.add hg.1, fun x a ha => by simp [hf.2.1, hg.2.1, mul_add], M + N, fun x => ?_⟩
  simp only [Pi.add_apply]
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ M * ‖x.1‖ + N * ‖x.1‖ := add_le_add (hM x) (hN x)
    _ = (M + N) * ‖x.1‖ := by ring

theorem inH_smul {f : X → ℝ} (hf : InH hX f) (r : ℝ) : InH hX (r • f) := by
  obtain ⟨M, hM⟩ := hf.2.2
  refine ⟨hf.1.const_smul r, fun x a ha => by simp [hf.2.1]; ring, |r| * M, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg r)

/-- **Exercise 4.7a (norm).** `‖·‖` of (1) is a norm on `H(X)`. -/
theorem ex_4_7a_norm {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) (r : ℝ) :
    0 ≤ hnorm X f ∧ (hnorm X f = 0 ↔ f = 0) ∧ hnorm X (r • f) = |r| * hnorm X f ∧
      hnorm X (f + g) ≤ hnorm X f + hnorm X g := by
  refine ⟨hnorm_nonneg f, ⟨fun h0 => funext fun x => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have := abs_le_hnorm hf x
    rw [h0, zero_mul] at this
    exact abs_nonpos_iff.1 this
  · subst h; simp [hnorm]
  · simp only [hnorm, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · refine hnorm_le (add_nonneg (hnorm_nonneg f) (hnorm_nonneg g)) fun x hx => ?_
    have h1 := abs_le_hnorm hf x
    have h2 := abs_le_hnorm hg x
    rw [hx, mul_one] at h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **Exercise 4.7a (completeness).** A sequence in `H(X)` that is Cauchy for `‖·‖` converges in
`‖·‖` to an element of `H(X)`. -/
theorem ex_4_7a_complete {f : ℕ → X → ℝ} (hf : ∀ n, InH hX (f n))
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hnorm X (f m - f n) < ε) :
    ∃ g, InH hX g ∧ Tendsto (fun n => hnorm X (f n - g)) atTop (𝓝 0) := by
  -- pointwise Cauchy, hence a pointwise limit
  have hpt : ∀ x : X, CauchySeq fun n => f n x := fun x => Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hc (ε / (‖x.1‖ + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := abs_le_hnorm (inH_sub (hf m) (hf n)) x
    rw [Real.dist_eq]
    simp only [Pi.sub_apply] at h
    calc |f m x - f n x| ≤ hnorm X (f m - f n) * ‖x.1‖ := h
      _ ≤ ε / (‖x.1‖ + 1) * ‖x.1‖ :=
          mul_le_mul_of_nonneg_right (hN m hm n hn).le (norm_nonneg _)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg x.1]
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hpt x)
  -- `|fₙ(x) − g(x)| ≤ ε‖x‖` from some `N` on
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x : X, |f n x - g x| ≤ ε * ‖x.1‖ := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun n hn x => ?_⟩
    have hlim : Tendsto (fun m => |f n x - f m x|) atTop (𝓝 |f n x - g x|) :=
      ((tendsto_const_nhds.sub (hg x)).abs)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have h := abs_le_hnorm (inH_sub (hf n) (hf m)) x
    simp only [Pi.sub_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hN n hn m hm).le (norm_nonneg _))
  -- `g` is continuous: locally uniform limit
  have hgc : Continuous g := by
    refine TendstoLocallyUniformly.continuous (F := f) (p := atTop) ?_
      (Frequently.of_forall fun n => (hf n).1)
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / (‖x.1‖ + 2)) (by positivity)
    refine eventually_atTop.2 ⟨N, fun n hn y hy => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have hy' : ‖y.1‖ ≤ ‖x.1‖ + 1 := by
      have hd : dist y x < 1 := Metric.mem_ball.1 hy
      rw [Subtype.dist_eq, dist_eq_norm] at hd
      have := norm_sub_norm_le y.1 x.1
      linarith
    calc |f n y - g y| ≤ ε / (‖x.1‖ + 2) * ‖y.1‖ := hN n hn y
      _ ≤ ε / (‖x.1‖ + 2) * (‖x.1‖ + 1) := mul_le_mul_of_nonneg_left hy' (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg x.1]
  -- `g` is homogeneous and bounded
  have hghom : ∀ x (a : ℝ) (ha : 0 ≤ a), g (csmul hX ha x) = a * g x := fun x a ha =>
    tendsto_nhds_unique (hg _) (by
      simp only [(hf _).2.1]
      exact (hg x).const_mul a)
  obtain ⟨N, hN⟩ := hunif 1 one_pos
  obtain ⟨M, hM⟩ := (hf N).2.2
  have hgb : ∀ x : X, |g x| ≤ (M + 1) * ‖x.1‖ := fun x => by
    have := hN N le_rfl x
    calc |g x| ≤ |f N x| + |f N x - g x| := by
          have := abs_sub (f N x) (f N x - g x)
          rwa [sub_sub_cancel] at this
      _ ≤ M * ‖x.1‖ + 1 * ‖x.1‖ := add_le_add (hM x) this
      _ = (M + 1) * ‖x.1‖ := by ring
  refine ⟨g, ⟨hgc, hghom, M + 1, hgb⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N', hN'⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N', fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnorm_nonneg _)]
  refine (hnorm_le (half_pos hε).le fun x hx => ?_).trans_lt (half_lt_self hε)
  have := hN' n hn x
  rwa [hx, mul_one] at this

/-- **Theorem 4.12.** Let `T` be monotone on `H(X)` and discount in the sense
`T(f + a‖·‖) ≤ Tf + γa‖·‖` for `a ≥ 0`. Then `‖Tf − Tg‖ ≤ γ‖f − g‖` on `H(X)`. (That `T` maps
`H(X)` into itself is not needed for the inequality.) -/
theorem theorem_4_12 {T : (X → ℝ) → (X → ℝ)} {γ : ℝ} (hγ : 0 ≤ γ)
    (hmono : ∀ f g, InH hX f → InH hX g → f ≤ g → T f ≤ T g)
    (hdisc : ∀ f, InH hX f → ∀ a : ℝ, 0 ≤ a →
      T (fun x => f x + a * ‖x.1‖) ≤ fun x => T f x + γ * a * ‖x.1‖)
    {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) :
    hnorm X (T f - T g) ≤ γ * hnorm X (f - g) := by
  have hnormH : InH hX fun x : X => ‖x.1‖ := ⟨continuous_subtype_val.norm,
    fun x a ha => by simp [csmul, norm_smul, abs_of_nonneg ha], 1, fun x => by simp⟩
  -- `f ≤ g + ‖f − g‖‖·‖`
  have hle : ∀ f g, InH hX f → InH hX g →
      T f ≤ fun x => T g x + γ * hnorm X (f - g) * ‖x.1‖ := fun f g hf hg => by
    have h1 : f ≤ fun x => g x + hnorm X (f - g) * ‖x.1‖ := fun x => by
      have := abs_le_hnorm (inH_sub hf hg) x
      simp only [Pi.sub_apply] at this
      linarith [le_abs_self (f x - g x)]
    have e : (fun x : X => hnorm X (f - g) * ‖x.1‖) = hnorm X (f - g) • fun x : X => ‖x.1‖ := by
      funext x; simp
    have hgH : InH hX fun x => g x + hnorm X (f - g) * ‖x.1‖ := by
      change InH hX (g + fun x : X => hnorm X (f - g) * ‖x.1‖)
      rw [e]
      exact inH_add hg (inH_smul hnormH _)
    exact (hmono _ _ hf hgH h1).trans (hdisc g hg _ (hnorm_nonneg _))
  refine hnorm_le (mul_nonneg hγ (hnorm_nonneg _)) fun x hx => ?_
  have a := hle f g hf hg x
  have b := hle g f hg hf x
  have hsym : hnorm X (g - f) = hnorm X (f - g) := by
    have := (ex_4_7a_norm (inH_sub hf hg) (inH_sub hf hg) (-1)).2.2.1
    rw [abs_neg, abs_one, one_mul] at this
    rw [← this]; congr 1; funext y; simp
  dsimp only at a b
  rw [hsym, hx, mul_one] at b
  rw [hx, mul_one] at a
  simp only [Pi.sub_apply]
  rw [abs_le]
  constructor <;> linarith

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic programs with constant returns to scale

SLP §4.3, pp. 88–91.

* `Assumption410`: `Γ` is nonempty, compact-valued, continuous, has a conical graph, and
  `‖y‖ ≤ α‖x‖` for `y ∈ Γ(x)` with `αβ < 1`. `Assumption411`: `0 < β < 1` and `F` is continuous,
  homogeneous of degree one and `|F(x, y)| ≤ B(‖x‖ + ‖y‖)` on the graph.
* `ex_4_6a`: `‖x_t‖ ≤ αᵗ‖x₀‖` along feasible plans; `ex_4_6b`: Assumptions 4.1–4.2 hold;
  `ex_4_6c`: `|v*(x)| ≤ c‖x‖`.
* `crs` (`T`), `ex_4_7b`: `T` maps `H(X)` into itself; `crs_mono`, `crs_disc`: it is monotone and
  discounts by `αβ`.
* `theorem_4_13`: `T` has a unique fixed point `v ∈ H(X)`, `‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖`, and the
  policy correspondence is nonempty, compact-valued, u.h.c. and homogeneous of degree one.
* `crs_fixed_eq_vstar` (p. 89): `v = v*` by Theorem 4.3; `ex_4_6c_hom`: `v*` is homogeneous.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E} {hX : IsCone X}

/-- **Assumption 4.10.** -/
structure Assumption410 (hX : IsCone X) (Γ : X → Set X) (β α : ℝ) : Prop where
  convex : Convex ℝ X
  nonempty : ∀ x, (Γ x).Nonempty
  compact : ∀ x, IsCompact (Γ x)
  lhc : ∀ x, IsLHC Γ x
  uhc : ∀ x, IsUHC Γ x
  cone : ∀ x, ∀ y ∈ Γ x, ∀ (a : ℝ) (ha : 0 ≤ a), csmul hX ha y ∈ Γ (csmul hX ha x)
  α_pos : 0 < α
  αβ_lt : α * β < 1
  growth : ∀ x, ∀ y ∈ Γ x, ‖y.1‖ ≤ α * ‖x.1‖

/-- **Assumption 4.11.** -/
structure Assumption411 (hX : IsCone X) (Γ : X → Set X) (F : X × X → ℝ) (β B : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  cont : ContinuousOn F (graph Γ)
  hom : ∀ x, ∀ y ∈ Γ x, ∀ (a : ℝ) (ha : 0 ≤ a), F (csmul hX ha x, csmul hX ha y) = a * F (x, y)
  B_pos : 0 < B
  bdd : ∀ x, ∀ y ∈ Γ x, |F (x, y)| ≤ B * (‖x.1‖ + ‖y.1‖)

variable {Γ : X → Set X} {F : X × X → ℝ} {β α B : ℝ}

/-- **Exercise 4.6a.** Along a feasible plan, `‖x_t‖ ≤ αᵗ‖x₀‖`. -/
theorem ex_4_6a (h410 : Assumption410 hX Γ β α) {x₀ : X} {x : ℕ → X}
    (hx : x ∈ Feasible Γ x₀) (t : ℕ) : ‖(x t).1‖ ≤ α ^ t * ‖x₀.1‖ := by
  induction t with
  | zero => simp [hx.1]
  | succ t ih =>
    calc ‖(x (t + 1)).1‖ ≤ α * ‖(x t).1‖ := h410.growth _ _ (hx.2 t)
      _ ≤ α * (α ^ t * ‖x₀.1‖) := mul_le_mul_of_nonneg_left ih h410.α_pos.le
      _ = α ^ (t + 1) * ‖x₀.1‖ := by ring

/-- The bound `|βᵗF(x_t, x_{t+1})| ≤ B(1 + α)‖x₀‖(αβ)ᵗ` along feasible plans. -/
theorem abs_term_le (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {x₀ : X} {x : ℕ → X} (hx : x ∈ Feasible Γ x₀) (t : ℕ) :
    |β ^ t * F (x t, x (t + 1))| ≤ B * (1 + α) * ‖x₀.1‖ * (α * β) ^ t := by
  have h1 := ex_4_6a h410 hx t
  have h2 := ex_4_6a h410 hx (t + 1)
  have hβt : 0 ≤ β ^ t := pow_nonneg h411.β_pos.le t
  rw [abs_mul, abs_of_nonneg hβt]
  calc β ^ t * |F (x t, x (t + 1))| ≤ β ^ t * (B * (‖(x t).1‖ + ‖(x (t + 1)).1‖)) :=
        mul_le_mul_of_nonneg_left (h411.bdd _ _ (hx.2 t)) hβt
    _ ≤ β ^ t * (B * (α ^ t * ‖x₀.1‖ + α ^ (t + 1) * ‖x₀.1‖)) := by
        gcongr; exact h411.B_pos.le
    _ = B * (1 + α) * ‖x₀.1‖ * (α * β) ^ t := by rw [mul_pow, pow_succ]; ring

/-- **Exercise 4.6b.** Under Assumptions 4.10–4.11, Assumptions 4.1–4.2 hold. -/
theorem ex_4_6b (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) :
    Assumption41 Γ ∧ Assumption42 Γ (curryF F) β :=
  ⟨h410.nonempty, assumption42_of_summable_pos fun x₀ x hx =>
    summable_max_of_le_geometric (mul_nonneg h410.α_pos.le h411.β_pos.le) h410.αβ_lt
      (by have := h411.B_pos; have := h410.α_pos; positivity) fun t =>
        (le_abs_self _).trans (abs_term_le h410 h411 hx t)⟩

/-- **Exercise 4.6c.** `|v*(x)| ≤ c‖x‖` with `c = B(1 + α)/(1 − αβ)`. -/
theorem ex_4_6c (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) (x₀ : X) :
    ((-(B * (1 + α) / (1 - α * β) * ‖x₀.1‖) : ℝ) : EReal) ≤ vstar Γ (curryF F) β x₀ ∧
      vstar Γ (curryF F) β x₀ ≤ ((B * (1 + α) / (1 - α * β) * ‖x₀.1‖ : ℝ) : EReal) := by
  set c := B * (1 + α) / (1 - α * β)
  have hαβ : 0 ≤ α * β := mul_nonneg h410.α_pos.le h411.β_pos.le
  have h42 := (ex_4_6b h410 h411).2
  -- partial sums lie in `[−c‖x₀‖, c‖x₀‖]`
  have hps : ∀ x ∈ Feasible Γ x₀, ∀ n, |partialSum (curryF F) β x n| ≤ c * ‖x₀.1‖ := by
    intro x hx n
    have hsum := summable_geometric_of_lt_one hαβ h410.αβ_lt
    calc |partialSum (curryF F) β x n|
        ≤ ∑ t ∈ Finset.range (n + 1), |β ^ t * F (x t, x (t + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range (n + 1), B * (1 + α) * ‖x₀.1‖ * (α * β) ^ t :=
          Finset.sum_le_sum fun t _ => abs_term_le h410 h411 hx t
      _ = B * (1 + α) * ‖x₀.1‖ * ∑ t ∈ Finset.range (n + 1), (α * β) ^ t := by
          rw [Finset.mul_sum]
      _ ≤ B * (1 + α) * ‖x₀.1‖ * ∑' t, (α * β) ^ t := by
          refine mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun t _ => pow_nonneg hαβ t) ?_
          have := h411.B_pos; have := h410.α_pos; positivity
      _ = c * ‖x₀.1‖ := by rw [tsum_geometric_of_lt_one hαβ h410.αβ_lt]; simp only [c]; ring
  have htot : ∀ x ∈ Feasible Γ x₀, ((-(c * ‖x₀.1‖) : ℝ) : EReal) ≤ total (curryF F) β x ∧
      total (curryF F) β x ≤ ((c * ‖x₀.1‖ : ℝ) : EReal) := fun x hx =>
    ⟨ge_of_tendsto' (tendsto_total h42 hx) fun n =>
        EReal.coe_le_coe_iff.2 (neg_le_of_abs_le (hps x hx n)),
      le_of_tendsto' (tendsto_total h42 hx) fun n =>
        EReal.coe_le_coe_iff.2 (le_of_abs_le (hps x hx n))⟩
  obtain ⟨x, hx⟩ := feasible_nonempty h410.nonempty x₀
  exact ⟨(htot x hx).1.trans (le_biSup _ hx), iSup₂_le fun y hy => (htot y hy).2⟩

/-! ### The operator `T` on `H(X)` -/

/-- `(Tf)(x) = max_{y ∈ Γ(x)} [F(x, y) + βf(y)]`. -/
noncomputable def crs (Γ : X → Set X) (F : X × X → ℝ) (β : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  maxValue (obj F β f) Γ x

theorem continuousOn_obj' (h411 : Assumption411 hX Γ F β B) {f : X → ℝ} (hf : Continuous f) :
    ContinuousOn (obj F β f) (graph Γ) :=
  h411.cont.add (continuousOn_const.mul (hf.comp continuous_snd).continuousOn)

theorem exists_crs_argmax (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f : X → ℝ} (hf : Continuous f) (x : X) :
    ∃ y ∈ Γ x, crs Γ F β f x = F (x, y) + β * f y ∧
      ∀ z ∈ Γ x, F (x, z) + β * f z ≤ crs Γ F β f x := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_obj' h411 hf) (h410.compact x)
    (h410.nonempty x)
  exact ⟨y, hy, hval.symm, fun z hz => (hmax z hz).trans_eq hval⟩

/-- `Γ(0) = {0}`: the only feasible successor of the origin is the origin. -/
theorem eq_zero_of_mem_zero (h410 : Assumption410 hX Γ β α) {x y : X} (hx : x.1 = 0)
    (hy : y ∈ Γ x) : y.1 = 0 := by
  have := h410.growth x y hy
  rw [hx, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- **Exercise 4.7b.** Under Assumptions 4.10–4.11, `T` maps `H(X)` into itself. -/
theorem ex_4_7b (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) {f : X → ℝ}
    (hf : InH hX f) : InH hX (crs Γ F β f) := by
  refine ⟨(theorem_3_6 (continuousOn_obj' h411 hf.1) h410.compact h410.lhc h410.uhc).1,
    fun x a ha => ?_, B * (1 + α) + β * α * hnorm X f, fun x => ?_⟩
  · -- homogeneity
    obtain ⟨y, hy, hval, hmax⟩ := exists_crs_argmax h410 h411 hf.1 x
    obtain ⟨z, hz, hzval, hzmax⟩ := exists_crs_argmax h410 h411 hf.1 (csmul hX ha x)
    rcases ha.eq_or_lt with rfl | hpos
    · -- `Γ(0) = {0}` and `F(0, 0) = 0`
      have hz0 : z.1 = 0 := eq_zero_of_mem_zero h410 (by simp [csmul]) hz
      have hzeq : z = csmul hX le_rfl y := Subtype.ext (by simp [csmul, hz0])
      rw [hzval, hzeq, h411.hom x y hy, hf.2.1]
      ring
    · refine le_antisymm ?_ ?_
      · -- pull the maximizer back to `x`
        have hinv : 0 ≤ a⁻¹ := inv_nonneg.2 hpos.le
        have hz' : csmul hX hinv z ∈ Γ x := by
          have := h410.cone _ z hz a⁻¹ hinv
          have e : csmul hX hinv (csmul hX hpos.le x) = x := Subtype.ext (by
            simp [csmul, smul_smul, inv_mul_cancel₀ hpos.ne'])
          rwa [e] at this
        have hle := hmax _ hz'
        have e1 : csmul hX hpos.le (csmul hX hinv z) = z := Subtype.ext (by
          simp [csmul, smul_smul, mul_inv_cancel₀ hpos.ne'])
        have hF := h411.hom x _ hz' a hpos.le
        have hfz := hf.2.1 (csmul hX hinv z) a hpos.le
        rw [e1] at hF hfz
        rw [hzval, hF, hfz]
        nlinarith
      · have hF := h411.hom x y hy a hpos.le
        have hfy := hf.2.1 y a hpos.le
        have := hzmax _ (h410.cone x y hy a hpos.le)
        rw [hF, hfy] at this
        rw [hval]
        nlinarith
  · -- the bound `|Tf(x)| ≤ (B(1 + α) + βα‖f‖)‖x‖`
    obtain ⟨y, hy, hval, -⟩ := exists_crs_argmax h410 h411 hf.1 x
    have hy' := h410.growth x y hy
    have hfy := abs_le_hnorm hf y
    have hB := h411.bdd x y hy
    rw [hval]
    have hβ := h411.β_pos
    have hn := hnorm_nonneg (X := X) f
    calc |F (x, y) + β * f y| ≤ |F (x, y)| + β * |f y| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_pos hβ]
      _ ≤ B * (‖x.1‖ + α * ‖x.1‖) + β * (hnorm X f * (α * ‖x.1‖)) := by
          gcongr
          · exact hB.trans (mul_le_mul_of_nonneg_left (by linarith) h411.B_pos.le)
          · exact hfy.trans (mul_le_mul_of_nonneg_left hy' hn)
      _ = (B * (1 + α) + β * α * hnorm X f) * ‖x.1‖ := by ring

/-- `T` is monotone. -/
theorem crs_mono (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hfg : f ≤ g) :
    crs Γ F β f ≤ crs Γ F β g := fun x => by
  obtain ⟨y, hy, hval, -⟩ := exists_crs_argmax h410 h411 hf x
  obtain ⟨-, -, -, hmax⟩ := exists_crs_argmax h410 h411 hg x
  rw [hval]
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hfg y) h411.β_pos.le)).trans (hmax y hy)

/-- `T(f + a‖·‖) ≤ Tf + αβa‖·‖` (p. 91). -/
theorem crs_disc (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f : X → ℝ} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a) :
    crs Γ F β (fun x => f x + a * ‖x.1‖) ≤ fun x => crs Γ F β f x + α * β * a * ‖x.1‖ :=
  fun x => by
    have hc : Continuous fun x : X => f x + a * ‖x.1‖ :=
      hf.add (continuous_const.mul continuous_subtype_val.norm)
    obtain ⟨y, hy, hval, -⟩ := exists_crs_argmax h410 h411 hc x
    obtain ⟨-, -, -, hmax⟩ := exists_crs_argmax h410 h411 hf x
    rw [hval]
    have h1 := hmax y hy
    have h2 := mul_le_mul_of_nonneg_left (h410.growth x y hy) (mul_nonneg h411.β_pos.le ha)
    dsimp only
    nlinarith

/-- `T` is a contraction of modulus `αβ` on `H(X)` (Theorem 4.12). -/
theorem crs_contraction (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) :
    hnorm X (crs Γ F β f - crs Γ F β g) ≤ α * β * hnorm X (f - g) :=
  theorem_4_12 (mul_nonneg h410.α_pos.le h411.β_pos.le)
    (fun _ _ hf hg hfg => crs_mono h410 h411 hf.1 hg.1 hfg)
    (fun _ hf _ ha => crs_disc h410 h411 hf.1 ha) hf hg

/-- The triangle inequality for `‖f − h‖` on `H(X)`. -/
theorem hnorm_sub_le {f g h : X → ℝ} (hf : InH hX f) (hg : InH hX g) (hh : InH hX h) :
    hnorm X (f - h) ≤ hnorm X (f - g) + hnorm X (g - h) := by
  have := (ex_4_7a_norm (inH_sub hf hg) (inH_sub hg hh) 1).2.2.2
  rwa [sub_add_sub_cancel] at this

/-- **Theorem 4.13.** Under Assumptions 4.10–4.11, `T` has a unique fixed point `v ∈ H(X)`,
`‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖` for `v₀ ∈ H(X)`, and the policy correspondence `G` is nonempty,
compact-valued, u.h.c. and homogeneous of degree one. -/
theorem theorem_4_13 (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) :
    ∃ v, InH hX v ∧ crs Γ F β v = v ∧ (∀ w, InH hX w → crs Γ F β w = w → w = v) ∧
      (∀ v₀, InH hX v₀ → ∀ n : ℕ,
        hnorm X ((crs Γ F β)^[n] v₀ - v) ≤ (α * β) ^ n * hnorm X (v₀ - v)) ∧
      (∀ x, (argmax (obj F β v) Γ x).Nonempty ∧ IsCompact (argmax (obj F β v) Γ x) ∧
        IsUHC (argmax (obj F β v) Γ) x) ∧
      ∀ x y (a : ℝ) (ha : 0 ≤ a), y ∈ argmax (obj F β v) Γ x →
        csmul hX ha y ∈ argmax (obj F β v) Γ (csmul hX ha x) := by
  set T := crs Γ F β
  set γ := α * β
  have hγ0 : 0 ≤ γ := mul_nonneg h410.α_pos.le h411.β_pos.le
  have hγ1 : γ < 1 := h410.αβ_lt
  have hTH : ∀ f, InH hX f → InH hX (T f) := fun f hf => ex_4_7b h410 h411 hf
  -- the iterates from `0`
  have h0 : InH hX (0 : X → ℝ) := ⟨continuous_const, fun _ _ _ => by simp, 0, fun _ => by simp⟩
  set fs : ℕ → X → ℝ := fun n => T^[n] 0
  have hfs : ∀ n, InH hX (fs n) := fun n => by
    induction n with
    | zero => exact h0
    | succ n ih => simp only [fs, Function.iterate_succ_apply']; exact hTH _ ih
  have hstep : ∀ n, hnorm X (fs (n + 1) - fs n) ≤ γ ^ n * hnorm X (fs 1 - fs 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : fs (n + 1 + 1) = T (fs (n + 1)) := Function.iterate_succ_apply' _ _ _
      have e2 : fs (n + 1) = T (fs n) := Function.iterate_succ_apply' _ _ _
      rw [e1, e2]
      calc hnorm X (T (T (fs n)) - T (fs n)) ≤ γ * hnorm X (T (fs n) - fs n) :=
            crs_contraction h410 h411 (e2 ▸ hfs (n + 1)) (hfs n)
        _ ≤ γ * (γ ^ n * hnorm X (fs 1 - fs 0)) := by
            rw [← e2]; exact mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * hnorm X (fs 1 - fs 0) := by ring
  -- Cauchy: `‖f_m − f_n‖ ≤ γⁿ/(1 − γ) ‖f₁ − f₀‖`
  have hgap : ∀ n k, hnorm X (fs (n + k) - fs n) ≤
      γ ^ n / (1 - γ) * hnorm X (fs 1 - fs 0) := by
    intro n k
    have hd := hnorm_nonneg (X := X) (fs 1 - fs 0)
    have hsum : ∀ k, hnorm X (fs (n + k) - fs n) ≤
        ∑ i ∈ Finset.range k, γ ^ (n + i) * hnorm X (fs 1 - fs 0) := by
      intro k
      induction k with
      | zero => simp [hnorm]
      | succ k ih =>
        rw [Finset.sum_range_succ]
        calc hnorm X (fs (n + (k + 1)) - fs n)
            ≤ hnorm X (fs (n + k + 1) - fs (n + k)) + hnorm X (fs (n + k) - fs n) :=
              hnorm_sub_le (hfs _) (hfs _) (hfs _)
          _ ≤ γ ^ (n + k) * hnorm X (fs 1 - fs 0) +
              ∑ i ∈ Finset.range k, γ ^ (n + i) * hnorm X (fs 1 - fs 0) :=
              add_le_add (hstep _) ih
          _ = _ := by ring
    refine (hsum k).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hd
    simp only [pow_add, ← Finset.mul_sum]
    rw [div_eq_mul_inv, ← tsum_geometric_of_lt_one hγ0 hγ1]
    exact mul_le_mul_of_nonneg_left ((summable_geometric_of_lt_one hγ0 hγ1).sum_le_tsum _
      fun i _ => pow_nonneg hγ0 i) (pow_nonneg hγ0 n)
  have hgeo : Tendsto (fun n => γ ^ n / (1 - γ) * hnorm X (fs 1 - fs 0)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).div_const (1 - γ)).mul_const
      (hnorm X (fs 1 - fs 0))
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hnorm X (fs m - fs n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hgeo).2 (ε / 2) (half_pos hε))
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmN : hnorm X (fs m - fs N) < ε / 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact (hgap N k).trans_lt (hN N le_rfl)
    have hnN : hnorm X (fs N - fs n) < ε / 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      have hsym := (ex_4_7a_norm (inH_sub (hfs (N + k)) (hfs N)) h0 (-1)).2.2.1
      rw [abs_neg, abs_one, one_mul, neg_smul, one_smul, neg_sub] at hsym
      rw [hsym]
      exact (hgap N k).trans_lt (hN N le_rfl)
    calc hnorm X (fs m - fs n) ≤ hnorm X (fs m - fs N) + hnorm X (fs N - fs n) :=
          hnorm_sub_le (hfs _) (hfs _) (hfs _)
      _ < ε := by linarith
  obtain ⟨v, hvH, hlim⟩ := ex_4_7a_complete hfs hcauchy
  -- `v` is a fixed point
  have hTv : T v = v := by
    have hb : ∀ n, hnorm X (T v - v) ≤ γ * hnorm X (fs n - v) + hnorm X (fs (n + 1) - v) := by
      intro n
      have e : fs (n + 1) = T (fs n) := Function.iterate_succ_apply' _ _ _
      calc hnorm X (T v - v) ≤ hnorm X (T v - fs (n + 1)) + hnorm X (fs (n + 1) - v) :=
            hnorm_sub_le (hTH v hvH) (hfs _) hvH
        _ ≤ γ * hnorm X (fs n - v) + hnorm X (fs (n + 1) - v) := by
            refine add_le_add ?_ le_rfl
            have hsym := (ex_4_7a_norm (inH_sub (hTH _ (hfs n)) (hTH v hvH)) h0 (-1)).2.2.1
            rw [abs_neg, abs_one, one_mul, neg_smul, one_smul, neg_sub] at hsym
            rw [e, hsym]
            exact crs_contraction h410 h411 (hfs n) hvH
    have hlim2 : Tendsto (fun n => γ * hnorm X (fs n - v) + hnorm X (fs (n + 1) - v)) atTop
        (𝓝 0) := by
      simpa using (hlim.const_mul γ).add (hlim.comp (tendsto_add_atTop_nat 1))
    have hz : hnorm X (T v - v) = 0 :=
      le_antisymm (ge_of_tendsto' hlim2 hb) (hnorm_nonneg _)
    exact sub_eq_zero.1 ((ex_4_7a_norm (inH_sub (hTH v hvH) hvH) h0 1).2.1.1 hz)
  -- uniqueness
  have huniq : ∀ w, InH hX w → T w = w → w = v := fun w hw hTw => by
    have h1 := crs_contraction h410 h411 hw hvH
    change hnorm X (T w - T v) ≤ _ at h1
    rw [hTw, hTv] at h1
    have hz : hnorm X (w - v) = 0 := by
      nlinarith [hnorm_nonneg (X := X) (w - v)]
    exact sub_eq_zero.1 ((ex_4_7a_norm (inH_sub hw hvH) h0 1).2.1.1 hz)
  refine ⟨v, hvH, hTv, huniq, fun v₀ hv₀ n => ?_, fun x => ?_, fun x y a ha hy => ?_⟩
  · -- the rate
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : InH hX (T^[n] v₀) := by
        clear ih
        induction n with
        | zero => exact hv₀
        | succ n ihn => rw [Function.iterate_succ_apply']; exact hTH _ ihn
      rw [Function.iterate_succ_apply']
      conv_lhs => rw [← hTv]
      calc hnorm X (T (T^[n] v₀) - T v) ≤ γ * hnorm X (T^[n] v₀ - v) :=
            crs_contraction h410 h411 hn hvH
        _ ≤ γ * (γ ^ n * hnorm X (v₀ - v)) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * hnorm X (v₀ - v) := by ring
  · exact (theorem_3_6 (continuousOn_obj' h411 hvH.1) h410.compact h410.lhc h410.uhc).2 x
  · -- homogeneity of `G`
    refine ⟨h410.cone x y hy.1 a ha, ?_⟩
    have hvx : v x = maxValue (obj F β v) Γ x := (congrFun hTv x).symm
    have hvax : v (csmul hX ha x) = maxValue (obj F β v) Γ (csmul hX ha x) :=
      (congrFun hTv _).symm
    rw [← hvax, hvH.2.1, hvx, ← hy.2]
    simp only [obj, h411.hom x y hy.1 a ha, hvH.2.1]
    ring

/-! ### The fixed point is the supremum function (p. 89) -/

/-- A fixed point of `T` in `H(X)` satisfies (FE) in `R̄`. -/
theorem satisfiesFE_crs (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {v : X → ℝ} (hvH : InH hX v) (hv : crs Γ F β v = v) :
    SatisfiesFE Γ (curryF F) β fun x => (v x : EReal) := by
  intro x
  obtain ⟨y, hy, hval, hmax⟩ := exists_crs_argmax h410 h411 hvH.1 x
  rw [hv] at hval hmax
  change (v x : EReal) = ⨆ y ∈ Γ x, ((curryF F x y : ℝ) : EReal) + (β : EReal) * (v y : EReal)
  refine le_antisymm ?_ (iSup₂_le fun z hz => ?_)
  · have := le_biSup (fun z => ((curryF F x z : ℝ) : EReal) + (β : EReal) * (v z : EReal)) hy
    refine le_trans ?_ this
    rw [hval, curryF, ← EReal.coe_mul, ← EReal.coe_add]
  · rw [curryF, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (hmax z hz)

/-- **p. 89.** Under Assumptions 4.10–4.11 the fixed point of `T` in `H(X)` is `v*`: along
feasible plans `|βⁿv(xₙ)| ≤ ‖v‖(αβ)ⁿ‖x₀‖ → 0`, so Theorem 4.3 applies. -/
theorem crs_fixed_eq_vstar (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {v : X → ℝ} (hvH : InH hX v) (hv : crs Γ F β v = v) :
    (fun x => (v x : EReal)) = vstar Γ (curryF F) β := by
  obtain ⟨h41, h42⟩ := ex_4_6b h410 h411
  refine theorem_4_3 h411.β_pos.le h41 h42 (satisfiesFE_crs h410 h411 hvH hv) fun x₀ x hx => ?_
  have hαβ : 0 ≤ α * β := mul_nonneg h410.α_pos.le h411.β_pos.le
  have hb : Tendsto (fun n => β ^ n * v (x n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => hnorm X v * ‖x₀.1‖ * (α * β) ^ n) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h411.β_pos.le n)]
      calc β ^ n * |v (x n)| ≤ β ^ n * (hnorm X v * (α ^ n * ‖x₀.1‖)) :=
            mul_le_mul_of_nonneg_left ((abs_le_hnorm hvH _).trans (mul_le_mul_of_nonneg_left
              (ex_4_6a h410 hx n) (hnorm_nonneg v))) (pow_nonneg h411.β_pos.le n)
        _ = hnorm X v * ‖x₀.1‖ * (α * β) ^ n := by rw [mul_pow]; ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hαβ h410.αβ_lt).const_mul
        (hnorm X v * ‖x₀.1‖)
  simpa only [EReal.coe_mul, EReal.coe_zero] using EReal.tendsto_coe.2 hb

/-- **Exercise 4.6c (homogeneity).** `v*` is homogeneous of degree one and real-valued, with
`|v*(x)| ≤ c‖x‖` (`ex_4_6c`): it is the fixed point of Theorem 4.13. -/
theorem ex_4_6c_hom (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) :
    ∃ v : X → ℝ, InH hX v ∧ vstar Γ (curryF F) β = fun x => (v x : EReal) := by
  obtain ⟨v, hvH, hv, -⟩ := theorem_4_13 h410 h411
  exact ⟨v, hvH, (crs_fixed_eq_vstar h410 h411 hvH hv).symm⟩

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Homogeneous quasi-concave functions

SLP Exercise 4.8a–b, pp. 91–92. `X` is a convex cone in a real normed space.

* `IsQuasiConcaveS`, `IsStrictQuasiConcaveS`: the book's definitions (p. 91).
* `ex_4_8a`: a homogeneous quasi-concave function that is positive off the origin is concave.
  `ex_4_8a_counterexample`: positivity cannot be dropped. On `ℝ²₊`,
  `f(x, y) = max{x − y, 2(x − y)}` is homogeneous of degree one and quasi-concave, but not
  concave.
* `ex_4_8b`: if `f` is also strictly quasi-concave, then
  `f(θx + (1 − θ)x′) > θf(x) + (1 − θ)f(x′)` for `x, x′` that are not proportional.
-/

open Set

namespace StokeyLucasPrescott.DeterministicDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}

/-- `f` is quasi-concave (p. 91): `x ≠ x′`, `f(x) ≥ f(x′)` and `θ ∈ (0, 1)` imply
`f(θx + (1 − θ)x′) ≥ f(x′)`. -/
def IsQuasiConcaveS (hC : Convex ℝ X) (f : X → ℝ) : Prop :=
  ∀ x x', x ≠ x' → f x' ≤ f x → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    f x' ≤ f (cmb hC h0.le h1.le x x')

/-- `f` is strictly quasi-concave: the last inequality is strict. -/
def IsStrictQuasiConcaveS (hC : Convex ℝ X) (f : X → ℝ) : Prop :=
  ∀ x x', x ≠ x' → f x' ≤ f x → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    f x' < f (cmb hC h0.le h1.le x x')

variable {hX : IsCone X} {hC : Convex ℝ X}

/-- The scaling behind Exercise 4.8: for `f(x) = a > 0` and `f(x′) = b > 0`,
`θx + (1 − θ)x′ = s(λx/a + (1 − λ)x′/b)` with `s = θa + (1 − θ)b`, `λ = θa/s`. -/
theorem cmb_eq_csmul_cmb (θ a b : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (x x' : X) :
    let s := θ * a + (1 - θ) * b
    let lam := θ * a / s
    ∃ (hs : 0 ≤ s) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1),
      cmb hC h0 h1 x x' = csmul hX hs (cmb hC hl0 hl1 (csmul hX (inv_nonneg.2 ha.le) x)
        (csmul hX (inv_nonneg.2 hb.le) x')) := by
  intro s lam
  have hs : 0 < s := by
    rcases h0.eq_or_lt with rfl | h0'
    · simp only [s]; nlinarith
    · simp only [s]; nlinarith
  have hl0 : 0 ≤ lam := div_nonneg (mul_nonneg h0 ha.le) hs.le
  have hl1 : lam ≤ 1 := by
    rw [div_le_one hs]; simp only [s]; nlinarith
  refine ⟨hs.le, hl0, hl1, Subtype.ext ?_⟩
  simp only [cmb, csmul, smul_add, smul_smul]
  congr 1
  · congr 1; simp only [lam]; field_simp
  · congr 1; simp only [lam]; field_simp; ring

/-- **Exercise 4.8a.** On a convex cone, a function that is homogeneous of degree one,
quasi-concave, and positive at every `x ≠ 0` is concave. -/
theorem ex_4_8a {f : X → ℝ} (hhom : ∀ x (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x) = a * f x)
    (hq : IsQuasiConcaveS hC f) (hpos : ∀ x : X, x.1 ≠ 0 → 0 < f x) : IsConcaveS hC f := by
  -- `f(0) = 0`
  have hzero : ∀ x : X, x.1 = 0 → f x = 0 := fun x hx => by
    have : x = csmul hX le_rfl x := Subtype.ext (by simp [csmul, hx])
    rw [this, hhom]; ring
  intro x x' θ h0 h1
  by_cases hx : x.1 = 0
  · have e : cmb hC h0 h1 x x' = csmul hX (by linarith : (0 : ℝ) ≤ 1 - θ) x' :=
      Subtype.ext (by simp [cmb, csmul, hx])
    rw [e, hhom, hzero x hx]; ring_nf; rfl
  by_cases hx' : x'.1 = 0
  · have e : cmb hC h0 h1 x x' = csmul hX h0 x := Subtype.ext (by simp [cmb, csmul, hx'])
    rw [e, hhom, hzero x' hx']; ring_nf; rfl
  set a := f x
  set b := f x'
  have ha := hpos x hx
  have hb := hpos x' hx'
  obtain ⟨hs, hl0, hl1, e⟩ := cmb_eq_csmul_cmb (hX := hX) (hC := hC) θ a b h0 h1 ha hb x x'
  rw [e, hhom]
  set u := csmul hX (inv_nonneg.2 ha.le) x
  set u' := csmul hX (inv_nonneg.2 hb.le) x'
  have hu : f u = 1 := by simp only [u, hhom]; field_simp
  have hu' : f u' = 1 := by simp only [u', hhom]; field_simp
  -- `f(λu + (1 − λ)u′) ≥ 1`
  have hge : 1 ≤ f (cmb hC hl0 hl1 u u') := by
    by_cases huu : u = u'
    · rw [huu, cmb_self, hu']
    rcases hl0.eq_or_lt with h | hl0'
    · have : cmb hC hl0 hl1 u u' = u' := Subtype.ext (by simp [cmb, ← h])
      rw [this, hu']
    rcases hl1.eq_or_lt with h | hl1'
    · have : cmb hC hl0 hl1 u u' = u := Subtype.ext (by simp [cmb, h])
      rw [this, hu]
    have := hq u u' huu (by rw [hu, hu']) _ hl0' hl1'
    rwa [hu'] at this
  nlinarith

/-- **Exercise 4.8a: positivity is needed.** On `ℝ²₊`, `f(x, y) = max{x − y, 2(x − y)}` is
homogeneous of degree one and quasi-concave (a nondecreasing function of `x − y`), but not
concave: `f(1, 0) = 2`, `f(0, 1) = −1`, `f(½, ½) = 0 < ½`. -/
theorem ex_4_8a_counterexample :
    let X : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}
    let f : ℝ × ℝ → ℝ := fun p => max (p.1 - p.2) (2 * (p.1 - p.2))
    (∀ p ∈ X, ∀ a : ℝ, 0 ≤ a → a • p ∈ X) ∧ Convex ℝ X ∧
      (∀ p ∈ X, ∀ a : ℝ, 0 ≤ a → f (a • p) = a * f p) ∧
      (∀ p ∈ X, ∀ q ∈ X, f q ≤ f p → ∀ θ : ℝ, 0 < θ → θ < 1 → f q ≤ f (θ • p + (1 - θ) • q)) ∧
      ¬ ConcaveOn ℝ X f := by
  intro X f
  have hmono : ∀ s t : ℝ, s ≤ t → max s (2 * s) ≤ max t (2 * t) := fun s t h =>
    max_le_max h (by linarith)
  refine ⟨fun p hp a ha => ⟨mul_nonneg ha hp.1, mul_nonneg ha hp.2⟩, ?_, fun p _ a ha => ?_,
    fun p _ q _ hpq θ h0 h1 => ?_, fun hconc => ?_⟩
  · intro p hp q hq a b ha hb _
    exact ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
      add_nonneg (mul_nonneg ha hp.2) (mul_nonneg hb hq.2)⟩
  · simp only [f, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← mul_sub, mul_left_comm, mul_max_of_nonneg _ _ ha]
  · -- `x − y` of the combination lies between those of `p` and `q`
    simp only [f, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hpq ⊢
    rcases le_total (q.1 - q.2) (p.1 - p.2) with h | h
    · exact hmono _ _ (by nlinarith)
    · -- then `f(p) ≤ f(q)`, so all three values agree
      have := hmono _ _ h
      have hle : (p.1 - p.2) ≤ θ * p.1 + (1 - θ) * q.1 - (θ * p.2 + (1 - θ) * q.2) := by nlinarith
      have hfeq : max (q.1 - q.2) (2 * (q.1 - q.2)) = max (p.1 - p.2) (2 * (p.1 - p.2)) :=
        le_antisymm hpq this
      rw [hfeq]
      exact hmono _ _ hle
  · have := hconc.2 (show ((1 : ℝ), (0 : ℝ)) ∈ X from ⟨zero_le_one, le_rfl⟩)
      (show ((0 : ℝ), (1 : ℝ)) ∈ X from ⟨le_rfl, zero_le_one⟩) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [f, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
    norm_num at this

/-- **Exercise 4.8b.** If in addition `f` is strictly quasi-concave, then
`f(θx + (1 − θ)x′) > θf(x) + (1 − θ)f(x′)` for `θ ∈ (0, 1)` and `x, x′` neither of which is a
multiple of the other. (The book asks only `x ≠ αx′`; with `x′ = 0` that allows
`f(θx) = θf(x)`, so `x′ ≠ αx` is needed as well.) -/
theorem ex_4_8b {f : X → ℝ} (hhom : ∀ x (a : ℝ) (ha : 0 ≤ a), f (csmul hX ha x) = a * f x)
    (hq : IsStrictQuasiConcaveS hC f) (hpos : ∀ x : X, x.1 ≠ 0 → 0 < f x) {x x' : X}
    (hxx' : ∀ a : ℝ, x.1 ≠ a • x'.1) (hx'x : ∀ a : ℝ, x'.1 ≠ a • x.1) {θ : ℝ} (h0 : 0 < θ)
    (h1 : θ < 1) : θ * f x + (1 - θ) * f x' < f (cmb hC h0.le h1.le x x') := by
  have hx : x.1 ≠ 0 := fun h => hxx' 0 (by simp [h])
  have hx' : x'.1 ≠ 0 := fun h => hx'x 0 (by simp [h])
  set a := f x
  set b := f x'
  have ha := hpos x hx
  have hb := hpos x' hx'
  obtain ⟨hs, hl0, hl1, e⟩ := cmb_eq_csmul_cmb (hX := hX) (hC := hC) θ a b h0.le h1.le ha hb x x'
  rw [e, hhom]
  set u := csmul hX (inv_nonneg.2 ha.le) x
  set u' := csmul hX (inv_nonneg.2 hb.le) x'
  have hu : f u = 1 := by simp only [u, hhom]; field_simp
  have hu' : f u' = 1 := by simp only [u', hhom]; field_simp
  have huu : u ≠ u' := fun h => hxx' (a / b) (by
    have := congrArg Subtype.val h
    simp only [u, u', csmul] at this
    calc x.1 = a • (a⁻¹ • x.1) := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
      _ = a • (b⁻¹ • x'.1) := by rw [this]
      _ = (a / b) • x'.1 := by rw [smul_smul, div_eq_mul_inv])
  have hs' : 0 < θ * a + (1 - θ) * b := by nlinarith
  have hl0' : 0 < θ * a / (θ * a + (1 - θ) * b) := div_pos (by positivity) hs'
  have hl1' : θ * a / (θ * a + (1 - θ) * b) < 1 := by
    rw [div_lt_one hs']; nlinarith
  have hgt := hq u u' huu (by rw [hu, hu']) _ hl0' hl1'
  rw [hu'] at hgt
  nlinarith

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Quasi-concavity of the value function with constant returns

SLP Exercise 4.8c, p. 92: "Under what conditions is the fixed point `v` of `T` strictly
quasi-concave?" The answer proved here follows the hint (the proof of Theorem 4.8 and
Exercise 4.8a–b).

* `NonProp`: `x` and `x′` are not nonnegative multiples of one another.
* `crs_concave`: if `F` is concave on the (convex, Assumption 4.8) graph of `Γ`, strictly so
  across pairs with `NonProp` states, then `T` maps concave functions in `H(X)` to concave
  functions that are strictly concave across `NonProp` pairs.
* `ex_4_8c`: under these conditions the fixed point `v` is concave, and if `v(x) ≠ 0` for
  `x ≠ 0` it is strictly quasi-concave.
* `ex_4_8d` ("Under what conditions is `v` differentiable?"): in `ℝˡ`, at an interior `x₀` with a
  maximizer `y₀` interior to `Γ(x₀)` and `x ↦ F(x, y₀)` differentiable at `x₀`, `v` is
  differentiable at `x₀` with `Dv(x₀) = D_xF(x₀, y₀)` (the argument of Theorem 4.11).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E} {hX : IsCone X}
  {hC : Convex ℝ X} {Γ : X → Set X} {F : X × X → ℝ} {β α B : ℝ}

/-- Neither of `x`, `x′` is a nonnegative multiple of the other. -/
def NonProp (x x' : X) : Prop := (∀ a : ℝ, 0 ≤ a → x.1 ≠ a • x'.1) ∧ ∀ a : ℝ, 0 ≤ a → x'.1 ≠ a • x.1

/-- `F` is concave on the graph of `Γ`, strictly across pairs whose states are `NonProp`. -/
def ConcaveGraph (hC : Convex ℝ X) (Γ : X → Set X) (F : X × X → ℝ) : Prop :=
  ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y') ∧
    (NonProp x x' →
      θ * F (x, y) + (1 - θ) * F (x', y') < F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y'))

/-- `T` maps concave functions in `H(X)` to concave functions, strictly concave across
`NonProp` pairs. -/
theorem crs_concave (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    (h48 : Assumption48 hC Γ) (hF : ConcaveGraph hC Γ F) {f : X → ℝ} (hfc : Continuous f)
    (hf : IsConcaveS hC f) :
    IsConcaveS hC (crs Γ F β f) ∧ ∀ x x', NonProp x x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
      θ * crs Γ F β f x + (1 - θ) * crs Γ F β f x' < crs Γ F β f (cmb hC h0.le h1.le x x') := by
  -- the inequality at interior `θ`, strict for `NonProp` pairs
  have key : ∀ x x' (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
      θ * crs Γ F β f x + (1 - θ) * crs Γ F β f x' ≤ crs Γ F β f (cmb hC h0.le h1.le x x') ∧
      (NonProp x x' → θ * crs Γ F β f x + (1 - θ) * crs Γ F β f x' <
        crs Γ F β f (cmb hC h0.le h1.le x x')) := by
    intro x x' θ h0 h1
    obtain ⟨y, hy, hv, -⟩ := exists_crs_argmax h410 h411 hfc x
    obtain ⟨y', hy', hv', -⟩ := exists_crs_argmax h410 h411 hfc x'
    obtain ⟨-, -, -, hmax⟩ := exists_crs_argmax h410 h411 hfc (cmb hC h0.le h1.le x x')
    have hyθ := h48 x y x' y' hy hy' θ h0.le h1.le
    have hfy := mul_le_mul_of_nonneg_left (hf y y' θ h0.le h1.le) h411.β_pos.le
    have hm := hmax _ hyθ
    obtain ⟨hFw, hFs⟩ := hF x y x' y' hy hy' θ h0 h1
    rw [hv, hv']
    exact ⟨by nlinarith, fun hnp => by nlinarith [hFs hnp]⟩
  refine ⟨fun x x' θ h0 h1 => ?_, fun x x' hnp θ h0 h1 => (key x x' θ h0 h1).2 hnp⟩
  rcases h0.eq_or_lt with rfl | h0'
  · simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  rcases h1.eq_or_lt with rfl | h1'
  · simp only [one_mul, sub_self, zero_mul, add_zero]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  exact (key x x' θ h0' h1').1

/-- **Exercise 4.8c.** Under Assumptions 4.10–4.11 and 4.8, if `F` is concave on the graph of `Γ`
and strictly concave across `NonProp` pairs, then the fixed point `v ∈ H(X)` of `T` is concave;
if moreover `v(x) ≠ 0` for `x ≠ 0`, it is strictly quasi-concave. -/
theorem ex_4_8c (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    (h48 : Assumption48 hC Γ) (hF : ConcaveGraph hC Γ F) {v : X → ℝ} (hvH : InH hX v)
    (hv : crs Γ F β v = v) :
    IsConcaveS hC v ∧ ((∀ x : X, x.1 ≠ 0 → v x ≠ 0) → IsStrictQuasiConcaveS hC v) := by
  set T := crs Γ F β
  -- the iterates from `0` are concave and in `H(X)`
  have h0 : InH hX (0 : X → ℝ) := ⟨continuous_const, fun _ _ _ => by simp, 0, fun _ => by simp⟩
  have hiter : ∀ n, InH hX (T^[n] 0) ∧ IsConcaveS hC (T^[n] 0) := by
    intro n
    induction n with
    | zero => exact ⟨h0, fun _ _ _ _ _ => by simp⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ex_4_7b h410 h411 ih.1, (crs_concave h410 h411 h48 hF ih.1.1 ih.2).1⟩
  -- they converge pointwise to `v`
  obtain ⟨v', hv'H, hv', huniq, hrate, -, -⟩ := theorem_4_13 h410 h411
  have hvv' : v = v' := huniq v hvH hv
  have hpt : ∀ x, Tendsto (fun n => T^[n] 0 x) atTop (𝓝 (v x)) := fun x => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hαβ : 0 ≤ α * β := mul_nonneg h410.α_pos.le h411.β_pos.le
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hαβ h410.αβ_lt).mul_const
        (hnorm X (0 - v'))).mul_const ‖x.1‖)
    have h1 := abs_le_hnorm (inH_sub (hiter n).1 hvH) x
    have h2 := hrate 0 h0 n
    rw [zero_sub] at h2
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h1 ⊢
    rw [hvv'] at h1 ⊢
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  -- concavity passes to the limit
  have hvc : IsConcaveS hC v := fun x x' θ h0 h1 => le_of_tendsto_of_tendsto
    (((hpt x).const_mul θ).add ((hpt x').const_mul (1 - θ))) (hpt _)
    (Eventually.of_forall fun n => (hiter n).2 x x' θ h0 h1)
  refine ⟨hvc, fun hne x x' hxx' hle θ h0 h1 => ?_⟩
  have hstrict := (crs_concave h410 h411 h48 hF hvH.1 hvc).2
  have hv2 : crs Γ F β v = v := hv
  rw [hv2] at hstrict
  by_cases hnp : NonProp x x'
  · have := hstrict x x' hnp θ h0 h1
    nlinarith
  -- `x` and `x′` lie on a common ray: use homogeneity
  simp only [NonProp, not_and_or, not_forall, not_not] at hnp
  rcases hnp with ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩
  · -- `x = a x′`
    have hx'0 : x'.1 ≠ 0 := fun h => hxx' (Subtype.ext (by rw [hxa, h, smul_zero]))
    have ha1 : a ≠ 1 := fun h => hxx' (Subtype.ext (by rw [hxa, h, one_smul]))
    have hvx : v x = a * v x' := by
      have : x = csmul hX ha x' := Subtype.ext hxa
      rw [this, hvH.2.1]
    have hc : cmb hC h0.le h1.le x x' = csmul hX (by nlinarith : (0 : ℝ) ≤ θ * a + (1 - θ)) x' :=
      Subtype.ext (by simp only [cmb, csmul, hxa, smul_smul, add_smul])
    rw [hc, hvH.2.1]
    have hv' := hne x' hx'0
    rw [hvx] at hle
    have : (a - 1) * v x' ≠ 0 := mul_ne_zero (sub_ne_zero.2 ha1) hv'
    have hpos : 0 < (a - 1) * v x' := lt_of_le_of_ne (by nlinarith) (Ne.symm this)
    nlinarith
  · -- `x′ = a x`
    have hx0 : x.1 ≠ 0 := fun h => hxx' (Subtype.ext (by rw [hxa, h, smul_zero]))
    have ha1 : a ≠ 1 := fun h => hxx' (Subtype.ext (by rw [hxa, h, one_smul]))
    have hvx : v x' = a * v x := by
      have : x' = csmul hX ha x := Subtype.ext hxa
      rw [this, hvH.2.1]
    have hc : cmb hC h0.le h1.le x x' = csmul hX (by nlinarith : (0 : ℝ) ≤ θ + (1 - θ) * a) x :=
      Subtype.ext (by simp only [cmb, csmul, hxa, smul_smul, add_smul])
    rw [hc, hvH.2.1, hvx]
    have hv := hne x hx0
    rw [hvx] at hle
    have : (1 - a) * v x ≠ 0 := mul_ne_zero (sub_ne_zero.2 (Ne.symm ha1)) hv
    have hpos : 0 < (1 - a) * v x := lt_of_le_of_ne (by nlinarith) (Ne.symm this)
    nlinarith

/-- **Exercise 4.8d.** In `ℝˡ`, under the hypotheses of Exercise 4.8c, let `x₀ ∈ int X` and let
`y₀ ∈ G(x₀)` be interior to `Γ(x₀)`. If `x ↦ F(x, y₀)` has derivative `DF` at `x₀`, then `v` is
differentiable at `x₀` with derivative `DF`. -/
theorem ex_4_8d {l : ℕ} {X : Set (Fin l → ℝ)} {hX : IsCone X} {hC : Convex ℝ X}
    {Γ : X → Set X} {F : X × X → ℝ} (h410 : Assumption410 hX Γ β α)
    (h411 : Assumption411 hX Γ F β B) (h48 : Assumption48 hC Γ) (hF : ConcaveGraph hC Γ F)
    {v : X → ℝ} (hvH : InH hX v) (hv : crs Γ F β v = v) {x₀ y₀ : X}
    (hy₀ : y₀ ∈ argmax (obj F β v) Γ x₀) (hint : X ∈ 𝓝 x₀.1)
    (hg : y₀.1 ∈ interior (Subtype.val '' Γ x₀)) {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hFd : HasFDerivAt (liftS fun x => F (x, y₀)) DF x₀.1) :
    HasFDerivAt (liftS v) DF x₀.1 := by
  have hvc := (ex_4_8c h410 h411 h48 hF hvH hv).1
  have h43 : Assumption43 Γ := ⟨h410.nonempty, h410.compact, h410.lhc, h410.uhc⟩
  have hvx : ∀ x, v x = maxValue (obj F β v) Γ x := fun x => (congrFun hv x).symm
  set W : (Fin l → ℝ) → ℝ := fun x => liftS (fun x => F (x, y₀)) x + β * v y₀
  have heq : W x₀.1 = liftS v x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx x₀]
    exact hy₀.2
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS v x := by
    have h1 := eventually_mem_Γ (hS := hC) h43 h48 (x₀ := x₀) (g₀ := y₀) hg
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx ⟨x, hxS⟩]
    exact le_maxValue (continuousOn_obj' h411 hvH.1) (h410.compact _) (hx ⟨x, hxS⟩ rfl)
  exact theorem_4_10 (concaveOn_liftS hvc) hint (hFd.add_const _) heq hle

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Unbounded returns

SLP §4.4, pp. 92–93. The operator `(Tf)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βf(y)]` acts on all
functions `X → R̄` (`opT`). Starting from an upper bound `v̂` of `v*` with `Tv̂ ≤ v̂`, the iterates
`Tⁿv̂` decrease to a limit `v` (`limitFn`); if that limit solves (FE) it is `v*`.

* `opT_mono`: `T` is monotone.
* `iterate_antitone`, `tendsto_iterate`: `Tⁿ⁺¹v̂ ≤ Tⁿv̂`, and `Tⁿv̂ → v`.
* `theorem_4_14`: under Assumptions 4.1–4.2, with (2) `limsup βⁿv̂(xₙ) ≤ 0` and
  (3) `u(x) ≤ v̂(x₀)` along feasible plans, a limit `v` that is a fixed point of `T` equals `v*`.
  Condition (1) `Tv̂ ≤ v̂` makes `v` the limit of the iterates.
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

/-- `(Tf)(x) = sup_{y ∈ Γ(x)} [F(x, y) + βf(y)]` on functions `X → R̄`. -/
noncomputable def opT (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (f : X → EReal) (x : X) : EReal :=
  ⨆ y ∈ Γ x, ((F x y : EReal) + (β : EReal) * f y)

theorem satisfiesFE_iff_opT {v : X → EReal} : SatisfiesFE Γ F β v ↔ opT Γ F β v = v :=
  ⟨fun h => funext fun x => (h x).symm, fun h x => (congrFun h x).symm⟩

/-- `T` is monotone. -/
theorem opT_mono (hβ : 0 ≤ β) {f g : X → EReal} (hfg : f ≤ g) : opT Γ F β f ≤ opT Γ F β g :=
  fun _ => iSup₂_mono fun y _ => add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hfg y) (EReal.coe_nonneg.2 hβ))

/-- From `Tv̂ ≤ v̂` the iterates decrease. -/
theorem iterate_antitone (hβ : 0 ≤ β) {vhat : X → EReal} (h1 : opT Γ F β vhat ≤ vhat) :
    Antitone fun n => (opT Γ F β)^[n] vhat := by
  have key : ∀ n, opT Γ F β ((opT Γ F β)^[n] vhat) ≤ (opT Γ F β)^[n] vhat := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact opT_mono hβ ih
  refine antitone_nat_of_succ_le fun n => ?_
  rw [Function.iterate_succ_apply']
  exact key n

/-- `v(x) = lim (Tⁿv̂)(x)`, the infimum of the decreasing iterates. -/
noncomputable def limitFn (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (vhat : X → EReal) (x : X) :
    EReal :=
  ⨅ n : ℕ, (opT Γ F β)^[n] vhat x

theorem tendsto_iterate (hβ : 0 ≤ β) {vhat : X → EReal} (h1 : opT Γ F β vhat ≤ vhat) (x : X) :
    Tendsto (fun n => (opT Γ F β)^[n] vhat x) atTop (𝓝 (limitFn Γ F β vhat x)) :=
  tendsto_atTop_iInf fun _ _ hmn => iterate_antitone hβ h1 hmn x

/-- **Theorem 4.14.** Let Assumptions 4.1–4.2 hold with `β > 0`, and let `v̂ : X → R̄` satisfy
(2) `limsup βⁿv̂(xₙ) ≤ 0` and (3) `u(x) ≤ v̂(x₀)` along every feasible plan. If
`v = inf Tⁿv̂` is a fixed point of `T`, then `v = v*`. Under (1) `Tv̂ ≤ v̂`, `v` is the limit
`lim Tⁿv̂` (`tendsto_iterate`); (1) is used only for that. -/
theorem theorem_4_14 (hβ : 0 < β) (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β)
    {vhat : X → EReal}
    (h2 : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      limsup (fun n => ((β ^ n : ℝ) : EReal) * vhat (x n)) atTop ≤ 0)
    (h3 : ∀ x₀, ∀ x ∈ Feasible Γ x₀, total F β x ≤ vhat x₀)
    (hfix : opT Γ F β (limitFn Γ F β vhat) = limitFn Γ F β vhat) :
    limitFn Γ F β vhat = vstar Γ F β := by
  set v := limitFn Γ F β vhat
  have hvle : v ≤ vhat := fun x => iInf_le (fun n => (opT Γ F β)^[n] vhat x) 0
  -- `v ≤ v*` by Exercise 4.3a
  have hle : v ≤ vstar Γ F β := fun x₀ =>
    ex_4_3a hβ h42 (satisfiesFE_iff_opT.2 hfix) (fun x₀ x hx => (limsup_le_limsup
      (Eventually.of_forall fun n => mul_le_mul_of_nonneg_left (hvle (x n))
        (EReal.coe_nonneg.2 (pow_nonneg hβ.le n)))).trans (h2 x₀ x hx)) x₀
  -- `v* ≤ Tⁿv̂` for all `n`
  have hstar : ∀ n, vstar Γ F β ≤ (opT Γ F β)^[n] vhat := by
    intro n
    induction n with
    | zero => exact fun x₀ => iSup₂_le fun x hx => h3 x₀ x hx
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← satisfiesFE_iff_opT.1 (theorem_4_2 hβ.le h41 h42)]
      exact opT_mono hβ.le ih
  exact le_antisymm hle fun x => le_iInf fun n => hstar n x

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The unit-elastic growth model

SLP §4.4, pp. 93–95: `max Σ βᵗ ln(k_t^α − k_{t+1})` with `0 < α, β < 1` on `X = (0, ∞)`, where
returns are unbounded above and below.

* `logΓ`, `logF`: `Γ(k) = (0, k^α)` and `F(k, y) = ln(k^α − y)`. The book's `Γ(k) = (0, k^α]`
  gives `F(k, k^α) = ln 0 = −∞`, while `F` must be real-valued; the open interval has the same
  supremum.
* `log_assumption41`, `log_assumption42`: Assumptions 4.1–4.2 hold.
* `log_opT_affine`: `T` maps `A + B ln k`, `B = α/(1 − αβ)`, to `(βA + C) + B ln k`, with
  maximizer `αβk^α`; so `Tⁿv̂ = C(1 − βⁿ)/(1 − β) + B ln k` for `v̂ = B ln k` (`log_iterate`).
* `log_vstar`: `v*(k) = C/(1 − β) + B ln k` (Theorem 4.14).
* `log_policy_optimal`: the plan `k_{t+1} = αβk_t^α` is optimal (Theorem 4.5).
-/

open Filter Topology Real

namespace StokeyLucasPrescott.DeterministicDP

/-- `(0, ∞)`. -/
abbrev PosR := {k : ℝ // 0 < k}

variable {α β : ℝ}

/-- `Γ(k) = (0, k^α)`. -/
def logΓ (α : ℝ) (k : PosR) : Set PosR := {y | y.1 < k.1 ^ α}

/-- `F(k, y) = ln(k^α − y)`. -/
noncomputable def logF (α : ℝ) (k y : PosR) : ℝ := Real.log (k.1 ^ α - y.1)

/-- `B = α/(1 − αβ)`. -/
noncomputable def coefB (α β : ℝ) : ℝ := α / (1 - α * β)

/-- `C = ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ)`. -/
noncomputable def coefC (α β : ℝ) : ℝ :=
  Real.log (1 - α * β) + α * β / (1 - α * β) * Real.log (α * β)

/-- `A + B ln k`. -/
noncomputable def affineLog (α β A : ℝ) (k : PosR) : EReal :=
  ((A + coefB α β * Real.log k.1 : ℝ) : EReal)

/-- The optimal saving `αβk^α ∈ Γ(k)`. -/
noncomputable def logPolicy (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k : PosR) : PosR :=
  ⟨α * β * k.1 ^ α, by have := rpow_pos_of_pos k.2 α; positivity⟩

variable (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
include hα0 hα1 hβ0 hβ1

omit hβ0 in
theorem αβ_lt_one : α * β < 1 := by nlinarith

omit hβ0 in
theorem coefB_pos : 0 < coefB α β := div_pos hα0 (by linarith [αβ_lt_one hα0 hα1 hβ1])

theorem coefC_neg : coefC α β < 0 := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hab : 0 < α * β := mul_pos hα0 hβ0
  have l1 : Real.log (1 - α * β) < 0 := Real.log_neg (by linarith) (by linarith)
  have l2 : Real.log (α * β) < 0 := Real.log_neg hab h1
  have : 0 < α * β / (1 - α * β) := div_pos hab (by linarith)
  unfold coefC; nlinarith

theorem logPolicy_mem (k : PosR) : logPolicy α β hα0 hβ0 k ∈ logΓ α k := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have := rpow_pos_of_pos k.2 α
  change α * β * k.1 ^ α < k.1 ^ α
  nlinarith

/-- The maximization: for `y ∈ (0, k^α)`,
`ln(k^α − y) + β(A + B ln y) ≤ ln((1 − αβ)k^α) + β(A + B ln(αβk^α))`. -/
theorem log_objective_le (A : ℝ) (k y : PosR) (hy : y ∈ logΓ α k) :
    logF α k y + β * (A + coefB α β * Real.log y.1) ≤
      logF α k (logPolicy α β hα0 hβ0 k) +
        β * (A + coefB α β * Real.log (logPolicy α β hα0 hβ0 k).1) := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set c := k.1 ^ α
  have hc : 0 < c := rpow_pos_of_pos k.2 α
  have hy0 : 0 < y.1 := y.2
  have hyc : y.1 < c := hy
  simp only [logF, logPolicy, coefB]
  have hcy : 0 < c - y.1 := by linarith
  have hcs : 0 < c - α * β * c := by nlinarith
  have hsc : 0 < α * β * c := by positivity
  -- `ln u ≤ u − 1` at `u = (c − y)/((1 − αβ)c)` and `u = y/(αβc)`
  have e1 := Real.log_le_sub_one_of_pos (div_pos hcy hcs)
  have e2 := Real.log_le_sub_one_of_pos (div_pos hy0 hsc)
  rw [Real.log_div hcy.ne' hcs.ne'] at e1
  rw [Real.log_div hy0.ne' hsc.ne'] at e2
  have hk : 0 < β * (α / (1 - α * β)) := mul_pos hβ0 (div_pos hα0 (by linarith))
  have e2' := mul_le_mul_of_nonneg_left e2 hk.le
  have hne : (1 - α * β) ≠ 0 := by linarith
  have key : (c - y.1) / (c - α * β * c) - 1 + β * (α / (1 - α * β)) * (y.1 / (α * β * c) - 1)
      = 0 := by
    rw [show c - α * β * c = (1 - α * β) * c by ring]
    field_simp
    ring
  nlinarith

/-- `T` maps `A + B ln k` to `(βA + C) + B ln k`. -/
theorem log_opT_affine (A : ℝ) :
    opT (logΓ α) (logF α) β (affineLog α β A) = affineLog α β (β * A + coefC α β) := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hab : 0 < α * β := mul_pos hα0 hβ0
  funext k
  have hval : logF α k (logPolicy α β hα0 hβ0 k) +
      β * (A + coefB α β * Real.log (logPolicy α β hα0 hβ0 k).1) =
      β * A + coefC α β + coefB α β * Real.log k.1 := by
    have hc : 0 < k.1 ^ α := rpow_pos_of_pos k.2 α
    have hne : (1 - α * β) ≠ 0 := by linarith
    simp only [logF, logPolicy, coefB, coefC]
    rw [show k.1 ^ α - α * β * k.1 ^ α = (1 - α * β) * k.1 ^ α by ring,
      Real.log_mul (by linarith) hc.ne', Real.log_mul hab.ne' hc.ne', Real.log_rpow k.2]
    field_simp
    ring
  refine le_antisymm (iSup₂_le fun y hy => ?_) ?_
  · rw [affineLog, affineLog, ← EReal.coe_mul, ← EReal.coe_add, ← hval]
    exact EReal.coe_le_coe_iff.2 (log_objective_le hα0 hα1 hβ0 hβ1 A k y hy)
  · refine le_trans ?_ (le_biSup _ (logPolicy_mem hα0 hα1 hβ0 hβ1 k))
    rw [affineLog, affineLog, ← EReal.coe_mul, ← EReal.coe_add, ← hval]

/-- `Tⁿv̂ = C(1 − βⁿ)/(1 − β) + B ln k` for `v̂ = B ln k` (p. 95). -/
theorem log_iterate (n : ℕ) :
    (opT (logΓ α) (logF α) β)^[n] (affineLog α β 0) =
      affineLog α β (coefC α β * (1 - β ^ n) / (1 - β)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, log_opT_affine hα0 hα1 hβ0 hβ1]
    congr 1
    have hne : (1 - β) ≠ 0 := by linarith
    field_simp
    ring

theorem log_assumption41 : Assumption41 (logΓ α) := fun k =>
  ⟨logPolicy α β hα0 hβ0 k, logPolicy_mem hα0 hα1 hβ0 hβ1 k⟩

omit hα1 hβ0 hβ1 in
/-- Along feasible plans, `ln k_t ≤ αᵗ ln k₀` (the technology bound (4), p. 94). -/
theorem log_capital_le {k₀ : PosR} {k : ℕ → PosR} (hk : k ∈ Feasible (logΓ α) k₀) (t : ℕ) :
    Real.log (k t).1 ≤ α ^ t * Real.log k₀.1 := by
  induction t with
  | zero => simp [hk.1]
  | succ t ih =>
    have h := Real.log_lt_log (k (t + 1)).2 (hk.2 t)
    rw [Real.log_rpow (k t).2] at h
    calc Real.log (k (t + 1)).1 ≤ α * Real.log (k t).1 := h.le
      _ ≤ α * (α ^ t * Real.log k₀.1) := mul_le_mul_of_nonneg_left ih hα0.le
      _ = α ^ (t + 1) * Real.log k₀.1 := by ring

omit hα1 hβ0 hβ1 in
/-- (4), p. 94: `F(k_t, k_{t+1}) ≤ αᵗ⁺¹ ln k₀`. -/
theorem logF_le {k₀ : PosR} {k : ℕ → PosR} (hk : k ∈ Feasible (logΓ α) k₀) (t : ℕ) :
    logF α (k t) (k (t + 1)) ≤ α ^ (t + 1) * Real.log k₀.1 := by
  have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
  have hlt : (k (t + 1)).1 < (k t).1 ^ α := hk.2 t
  have hpos : 0 < (k t).1 ^ α - (k (t + 1)).1 := by linarith
  calc logF α (k t) (k (t + 1)) ≤ Real.log ((k t).1 ^ α) :=
        Real.log_le_log hpos (by linarith [(k (t + 1)).2])
    _ = α * Real.log (k t).1 := Real.log_rpow (k t).2 α
    _ ≤ α * (α ^ t * Real.log k₀.1) :=
        mul_le_mul_of_nonneg_left (log_capital_le hα0 hk t) hα0.le
    _ = α ^ (t + 1) * Real.log k₀.1 := by ring

theorem log_assumption42 : Assumption42 (logΓ α) (logF α) β :=
  assumption42_of_summable_pos fun k₀ k hk =>
    summable_max_of_le_geometric (mul_pos hα0 hβ0).le (αβ_lt_one hα0 hα1 hβ1)
      (by positivity : (0 : ℝ) ≤ α * |Real.log k₀.1|) fun t => by
        have := logF_le hα0 hk t
        calc β ^ t * logF α (k t) (k (t + 1)) ≤ β ^ t * (α ^ (t + 1) * |Real.log k₀.1|) :=
              mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left
                (le_abs_self _) (pow_nonneg hα0.le _))) (pow_nonneg hβ0.le t)
          _ = α * |Real.log k₀.1| * (α * β) ^ t := by rw [mul_pow]; ring

/-- **p. 95.** `v*(k) = C/(1 − β) + B ln k`. -/
theorem log_vstar : vstar (logΓ α) (logF α) β = affineLog α β (coefC α β / (1 - β)) := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  have hB := coefB_pos hα0 hα1 hβ1
  have hC := coefC_neg hα0 hα1 hβ0 hβ1
  -- the limit of the iterates
  have hlim : limitFn (logΓ α) (logF α) β (affineLog α β 0) =
      affineLog α β (coefC α β / (1 - β)) := by
    funext k
    simp only [limitFn, log_iterate hα0 hα1 hβ0 hβ1]
    have hanti : Antitone fun n : ℕ => affineLog α β (coefC α β * (1 - β ^ n) / (1 - β)) k := by
      intro m n hmn
      refine EReal.coe_le_coe_iff.2 (add_le_add_left ?_ _)
      refine div_le_div_of_nonneg_right ?_ (by linarith)
      have : β ^ n ≤ β ^ m := pow_le_pow_of_le_one hβ0.le hβ1.le hmn
      nlinarith
    have hconv : Tendsto (fun n : ℕ => affineLog α β (coefC α β * (1 - β ^ n) / (1 - β)) k)
        atTop (𝓝 (affineLog α β (coefC α β / (1 - β)) k)) := by
      refine EReal.tendsto_coe.2 ?_
      have := ((((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_sub 1).const_mul
        (coefC α β)).div_const (1 - β)).add_const (coefB α β * Real.log k.1)
      simpa using this
    exact tendsto_nhds_unique (tendsto_atTop_iInf hanti) hconv
  rw [← hlim]
  refine (theorem_4_14 hβ0 (log_assumption41 hα0 hα1 hβ0 hβ1)
    (log_assumption42 hα0 hα1 hβ0 hβ1) (fun k₀ k hk => ?_) (fun k₀ k hk => ?_) ?_).symm
  · -- (2): `βⁿB ln kₙ ≤ B|ln k₀|(αβ)ⁿ → 0`
    have hb : ∀ n, ((β ^ n : ℝ) : EReal) * affineLog α β 0 (k n) ≤
        ((coefB α β * |Real.log k₀.1| * (α * β) ^ n : ℝ) : EReal) := fun n => by
      rw [affineLog, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.2 ?_
      have := log_capital_le hα0 hk n
      have h2 : α ^ n * Real.log k₀.1 ≤ α ^ n * |Real.log k₀.1| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hα0.le n)
      calc β ^ n * (0 + coefB α β * Real.log (k n).1)
          ≤ β ^ n * (coefB α β * (α ^ n * |Real.log k₀.1|)) := by
            rw [zero_add]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (this.trans h2) hB.le)
              (pow_nonneg hβ0.le n)
        _ = coefB α β * |Real.log k₀.1| * (α * β) ^ n := by rw [mul_pow]; ring
    have hzero : Tendsto (fun n => ((coefB α β * |Real.log k₀.1| * (α * β) ^ n : ℝ) : EReal))
        atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hα0 hβ0).le h1).const_mul
        (coefB α β * |Real.log k₀.1|)
      simpa using EReal.tendsto_coe.2 this
    exact (limsup_le_limsup (Eventually.of_forall hb)).trans hzero.limsup_eq.le
  · -- (3): `u(k) ≤ B ln k₀`
    have hps : ∀ n, (partialSum (logF α) β k n : EReal) ≤
        ((∑ t ∈ Finset.range (n + 1), α * Real.log k₀.1 * (α * β) ^ t : ℝ) : EReal) :=
      fun n => EReal.coe_le_coe_iff.2 (Finset.sum_le_sum fun t _ => by
        have := logF_le hα0 hk t
        calc β ^ t * logF α (k t) (k (t + 1)) ≤ β ^ t * (α ^ (t + 1) * Real.log k₀.1) :=
              mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le t)
          _ = α * Real.log k₀.1 * (α * β) ^ t := by rw [mul_pow]; ring)
    have hgeo : Tendsto (fun n => ((∑ t ∈ Finset.range (n + 1), α * Real.log k₀.1 *
        (α * β) ^ t : ℝ) : EReal)) atTop (𝓝 (affineLog α β 0 k₀)) := by
      refine EReal.tendsto_coe.2 ?_
      have hs := (hasSum_geometric_of_lt_one (mul_pos hα0 hβ0).le h1).mul_left
        (α * Real.log k₀.1)
      have := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      convert this using 2
      · simp
      · simp only [coefB, zero_add, div_eq_mul_inv]; ring
    exact le_of_tendsto_of_tendsto (tendsto_total (log_assumption42 hα0 hα1 hβ0 hβ1) hk) hgeo
      (Eventually.of_forall hps)
  · -- the limit is a fixed point
    rw [hlim, log_opT_affine hα0 hα1 hβ0 hβ1]
    congr 1
    have hne : (1 - β) ≠ 0 := by linarith
    field_simp
    ring

/-- **p. 95.** The policy `g(k) = αβk^α` generates an optimal plan (Theorem 4.5). -/
theorem log_policy_optimal (k₀ : PosR) :
    total (logF α) β (fun t => (logPolicy α β hα0 hβ0)^[t] k₀) =
      vstar (logΓ α) (logF α) β k₀ := by
  have h1 := αβ_lt_one hα0 hα1 hβ1
  set g := logPolicy α β hα0 hβ0
  set k : ℕ → PosR := fun t => g^[t] k₀
  have hk : ∀ t, k (t + 1) = g (k t) := fun t => Function.iterate_succ_apply' _ _ _
  set A := coefC α β / (1 - β)
  have hvs := log_vstar hα0 hα1 hβ0 hβ1
  refine theorem_4_5 hβ0.le (log_assumption42 hα0 hα1 hβ0 hβ1)
    ⟨rfl, fun t => hk t ▸ logPolicy_mem hα0 hα1 hβ0 hβ1 _⟩ (fun t => ?_) ?_
  · -- (9): the maximizer attains `T v* = v*`
    rw [hvs, hk t, affineLog, affineLog, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
    have hab : 0 < α * β := mul_pos hα0 hβ0
    have hne : (1 - α * β) ≠ 0 := by linarith
    have hne' : (1 - β) ≠ 0 := by linarith
    simp only [g, logF, logPolicy, coefB, coefC]
    rw [show (k t).1 ^ α - α * β * (k t).1 ^ α = (1 - α * β) * (k t).1 ^ α by ring,
      Real.log_mul (by linarith) hc.ne', Real.log_mul hab.ne' hc.ne', Real.log_rpow (k t).2]
    field_simp
    ring
  · -- (11): `ln k_t` stays bounded, so `βᵗv*(k_t) → 0`
    set M := |Real.log k₀.1| + |Real.log (α * β)| / (1 - α)
    have hlog : ∀ t, |Real.log (k t).1| ≤ M := by
      intro t
      induction t with
      | zero =>
        simp only [k, Function.iterate_zero, id_eq, M]
        have : 0 ≤ |Real.log (α * β)| / (1 - α) := div_nonneg (abs_nonneg _) (by linarith)
        linarith
      | succ t ih =>
        rw [hk t]
        have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
        have e : Real.log (g (k t)).1 = Real.log (α * β) + α * Real.log (k t).1 := by
          simp only [g, logPolicy]
          rw [Real.log_mul (mul_pos hα0 hβ0).ne' hc.ne', Real.log_rpow (k t).2]
        rw [e]
        have hM : |Real.log (α * β)| + α * M ≤ M := by
          simp only [M]
          rw [div_eq_mul_inv]
          have h1α : 0 < 1 - α := by linarith
          have : |Real.log (α * β)| * (1 - α)⁻¹ * (1 - α) = |Real.log (α * β)| := by
            field_simp
          nlinarith [abs_nonneg (Real.log k₀.1), abs_nonneg (Real.log (α * β)),
            inv_pos.2 h1α]
        calc |Real.log (α * β) + α * Real.log (k t).1|
            ≤ |Real.log (α * β)| + α * |Real.log (k t).1| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_of_pos hα0]
          _ ≤ |Real.log (α * β)| + α * M := by gcongr
          _ ≤ M := hM
    have hb : ∀ t, ((β ^ t : ℝ) : EReal) * vstar (logΓ α) (logF α) β (k t) ≤
        (((|A| + coefB α β * M) * β ^ t : ℝ) : EReal) := fun t => by
      rw [hvs, affineLog, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.2 ?_
      have hB := coefB_pos hα0 hα1 hβ1
      have h1 : A + coefB α β * Real.log (k t).1 ≤ |A| + coefB α β * M := by
        have := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (k t).1) |>.trans (hlog t))
          hB.le
        linarith [le_abs_self A]
      rw [mul_comm _ (β ^ t)]
      exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ0.le t)
    have hzero : Tendsto (fun t => (((|A| + coefB α β * M) * β ^ t : ℝ) : EReal)) atTop
        (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (|A| + coefB α β * M)
      simpa using EReal.tendsto_coe.2 this
    exact (limsup_le_limsup (Eventually.of_forall hb)).trans hzero.limsup_eq.le

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A quadratic investment problem

SLP §4.4, pp. 95–97. A firm with capital `x` earns `ax − bx²/2` and pays `c(y − x)²/2` to move
its capital to `y`; it discounts at `δ ∈ (0, 1)`. So `X = Γ(x) = ℝ` and
`F(x, y) = ax − bx²/2 − c(y − x)²/2` (`quadF`), with `a, b, c > 0`.

* `quad_opT`: `T` maps the quadratic `px − qx²/2 + r` (`q ≥ 0`) to the quadratic with
  coefficients (6)–(8), attained at `y = (δp + cx)/(δq + c)`.
* `quad_iterate`: `Tⁿv̂ = αₙx − βₙx²/2 + γₙ` for `v̂ = a²/(2b(1 − δ))`.
* `tendsto_qs`, `tendsto_ps`, `tendsto_rs`: `βₙ → β` with `b < β < b + c`, `αₙ → α` and
  `γₙ → γ` (`tendsto_linear_recursion` handles (7)–(8)).
* `quad_vstar`: `v* = αx − βx²/2 + γ` (Theorem 4.14).
* `quad_policy_optimal`: the linear policy `g(x) = (δα + cx)/(δβ + c)` is optimal (Theorem 4.5).
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

/-- If `e_{n+1} ≤ δeₙ + εₙ` with `0 ≤ δ < 1`, `eₙ ≥ 0` and `εₙ → 0`, then `eₙ → 0`. -/
theorem tendsto_zero_of_le_contract {e ε : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (he : ∀ n, 0 ≤ e n) (hrec : ∀ n, e (n + 1) ≤ δ * e n + ε n)
    (hε : Tendsto ε atTop (𝓝 0)) : Tendsto e atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hε).2 (η * (1 - δ) / 2) (by
    have : 0 < 1 - δ := by linarith
    positivity))
  -- from `N` on, `e_{N+k} ≤ δᵏ e_N + η/2`
  have hk : ∀ k, e (N + k) ≤ δ ^ k * e N + η / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have h1 := hrec (N + k)
      have h2 := hN (N + k) (by omega)
      calc e (N + (k + 1)) ≤ δ * e (N + k) + ε (N + k) := h1
        _ ≤ δ * (δ ^ k * e N + η / 2) + η * (1 - δ) / 2 := by
            gcongr
        _ = δ ^ (k + 1) * e N + η / 2 := by ring
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const (e N)
  rw [zero_mul] at hpow
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 hpow).2 (η / 2) (half_pos hη))
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he _)]
  have := hK (K + k) (by omega)
  rw [add_assoc] at *
  have := hk (K + k)
  linarith

/-- The linear recursion `x_{n+1} = uₙ + κₙxₙ` with `uₙ → u`, `κₙ → κ`, `0 ≤ κₙ ≤ δ < 1`
converges to `u/(1 − κ)`. -/
theorem tendsto_linear_recursion {x u κ : ℕ → ℝ} {u₀ κ₀ δ : ℝ} (hδ1 : δ < 1)
    (hκ : ∀ n, 0 ≤ κ n ∧ κ n ≤ δ) (hrec : ∀ n, x (n + 1) = u n + κ n * x n)
    (hu : Tendsto u atTop (𝓝 u₀)) (hκlim : Tendsto κ atTop (𝓝 κ₀)) :
    Tendsto x atTop (𝓝 (u₀ / (1 - κ₀))) := by
  have hδ0 : 0 ≤ δ := (hκ 0).1.trans (hκ 0).2
  have hκ₀ : κ₀ ≤ δ := le_of_tendsto' hκlim fun n => (hκ n).2
  set L := u₀ / (1 - κ₀)
  have hL : L = u₀ + κ₀ * L := by
    have : 1 - κ₀ ≠ 0 := by linarith
    simp only [L]; field_simp; ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_zero_of_le_contract hδ0 hδ1 (fun n => norm_nonneg _) (fun n => ?_)
    (ε := fun n => |u n - u₀| + |κ n - κ₀| * |L|) ?_
  · simp only [Real.norm_eq_abs]
    rw [hrec n]
    have e : u n + κ n * x n - L = (u n - u₀) + κ n * (x n - L) + (κ n - κ₀) * L := by
      linear_combination (-1 : ℝ) * hL
    rw [e]
    calc |(u n - u₀) + κ n * (x n - L) + (κ n - κ₀) * L|
        ≤ |u n - u₀| + |κ n * (x n - L)| + |(κ n - κ₀) * L| := abs_add_three _ _ _
      _ ≤ |u n - u₀| + δ * |x n - L| + |κ n - κ₀| * |L| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hκ n).1]
          gcongr
          exact (hκ n).2
      _ = δ * |x n - L| + (|u n - u₀| + |κ n - κ₀| * |L|) := by ring
  · have h1 := (hu.sub_const u₀).abs
    have h2 := ((hκlim.sub_const κ₀).abs).mul_const |L|
    simpa using h1.add h2

variable {a b c δ : ℝ}

/-- `F(x, y) = ax − bx²/2 − c(y − x)²/2`. -/
noncomputable def quadF (a b c : ℝ) (x y : ℝ) : ℝ := a * x - b * x ^ 2 / 2 - c * (y - x) ^ 2 / 2

/-- `Γ(x) = ℝ`. -/
def quadΓ (_ : ℝ) : Set ℝ := Set.univ

/-- The quadratic `px − qx²/2 + r`. -/
noncomputable def quadFn (p q r : ℝ) (x : ℝ) : EReal := ((p * x - q * x ^ 2 / 2 + r : ℝ) : EReal)

/-- (6): `β' = b + δβc/(δβ + c)`. -/
noncomputable def nextQ (b c δ q : ℝ) : ℝ := b + δ * q * c / (δ * q + c)

/-- (7): `α' = a + δαc/(δβ + c)`. -/
noncomputable def nextP (a c δ p q : ℝ) : ℝ := a + δ * p * c / (δ * q + c)

/-- (8): `γ' = δγ + (δα)²/(2(δβ + c))`. -/
noncomputable def nextR (c δ p q r : ℝ) : ℝ := δ * r + (δ * p) ^ 2 / (2 * (δ * q + c))

/-- The objective as a function of `y` is the value at `y* = (δp + cx)/(δq + c)` minus
`(c + δq)(y − y*)²/2`. -/
theorem quad_objective (p q r x y : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hq : 0 ≤ q) :
    quadF a b c x y + δ * (p * y - q * y ^ 2 / 2 + r) =
      nextP a c δ p q * x - nextQ b c δ q * x ^ 2 / 2 + nextR c δ p q r -
        (δ * q + c) / 2 * (y - (δ * p + c * x) / (δ * q + c)) ^ 2 := by
  have hne : δ * q + c ≠ 0 := by positivity
  simp only [quadF, nextP, nextQ, nextR]
  field_simp
  ring

/-- `T` maps `px − qx²/2 + r` (`q ≥ 0`) to the quadratic with coefficients (6)–(8). -/
theorem quad_opT (p q r : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hq : 0 ≤ q) :
    opT quadΓ (quadF a b c) δ (quadFn p q r) =
      quadFn (nextP a c δ p q) (nextQ b c δ q) (nextR c δ p q r) := by
  funext x
  have hpos : 0 ≤ (δ * q + c) / 2 := by positivity
  refine le_antisymm (iSup₂_le fun y _ => ?_) ?_
  · rw [quadFn, quadFn, ← EReal.coe_mul, ← EReal.coe_add, quad_objective p q r x y hc hδ hq]
    exact EReal.coe_le_coe_iff.2 (by nlinarith [sq_nonneg (y - (δ * p + c * x) / (δ * q + c))])
  · refine le_trans ?_ (le_biSup _ (Set.mem_univ ((δ * p + c * x) / (δ * q + c))))
    rw [quadFn, quadFn, ← EReal.coe_mul, ← EReal.coe_add,
      quad_objective p q r x _ hc hδ hq]
    simp

/-- `F(x, y) ≤ a²/(2b)`. -/
theorem quadF_le (hb : 0 < b) (hc : 0 < c) (x y : ℝ) : quadF a b c x y ≤ a ^ 2 / (2 * b) := by
  simp only [quadF]
  have e : a ^ 2 / (2 * b) - (a * x - b * x ^ 2 / 2) = (b * x - a) ^ 2 / (2 * b) := by
    field_simp; ring
  have : 0 ≤ (b * x - a) ^ 2 / (2 * b) := by positivity
  nlinarith [sq_nonneg (y - x)]

/-- The coefficient sequences, from `v̂ = a²/(2b(1 − δ))`. -/
noncomputable def qs (b c δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => nextQ b c δ (qs b c δ n)

noncomputable def ps (a b c δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => nextP a c δ (ps a b c δ n) (qs b c δ n)

noncomputable def rs (a b c δ : ℝ) : ℕ → ℝ
  | 0 => a ^ 2 / (2 * b * (1 - δ))
  | n + 1 => nextR c δ (ps a b c δ n) (qs b c δ n) (rs a b c δ n)

variable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
include ha hb hc hδ0 hδ1

omit ha hδ1 in
theorem qs_nonneg (n : ℕ) : 0 ≤ qs b c δ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [qs, nextQ]; positivity

omit ha hb hδ1 in
theorem nextQ_mono {q q' : ℝ} (hq : 0 ≤ q) (hqq' : q ≤ q') : nextQ b c δ q ≤ nextQ b c δ q' := by
  simp only [nextQ]
  have h1 : 0 < δ * q + c := by positivity
  have h2 : 0 < δ * q' + c := by have : 0 ≤ q' := hq.trans hqq'; positivity
  rw [add_le_add_iff_left, div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_left hqq' (by positivity : (0 : ℝ) ≤ δ * c ^ 2)]

omit ha hb hδ1 in
theorem nextQ_lt (q : ℝ) (hq : 0 ≤ q) : nextQ b c δ q < b + c := by
  simp only [nextQ]
  have h1 : 0 < δ * q + c := by positivity
  rw [add_lt_add_iff_left, div_lt_iff₀ h1]
  nlinarith

omit ha hδ1 in
theorem qs_mono : Monotone (qs b c δ) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero =>
    change (0 : ℝ) ≤ nextQ b c δ 0
    simp only [nextQ, mul_zero, zero_mul, zero_div, add_zero]
    exact hb.le
  | succ n ih => exact nextQ_mono hc hδ0 (qs_nonneg hb hc hδ0 n) ih

omit ha hδ1 in
/-- (6): `βₙ → β` with `b < β < b + c`, and `β` solves `β = b + δβc/(δβ + c)`. -/
theorem tendsto_qs : ∃ Q, Tendsto (qs b c δ) atTop (𝓝 Q) ∧ nextQ b c δ Q = Q ∧ b < Q ∧
    Q < b + c := by
  have hbdd : ∀ n, qs b c δ n ≤ b + c := fun n => by
    cases n with
    | zero => change (0 : ℝ) ≤ b + c; positivity
    | succ n => exact (nextQ_lt hc hδ0 _ (qs_nonneg hb hc hδ0 n)).le
  have hlim := tendsto_atTop_ciSup (qs_mono hb hc hδ0) ⟨b + c, by
    rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  set Q := ⨆ n, qs b c δ n
  have hQ0 : 0 ≤ Q := (qs_nonneg hb hc hδ0 0).trans (le_ciSup ⟨b + c, by
    rintro _ ⟨n, rfl⟩; exact hbdd n⟩ 0)
  have hfix : nextQ b c δ Q = Q := by
    have hcont : ContinuousAt (nextQ b c δ) Q := by
      have e : nextQ b c δ = fun q => b + δ * q * c / (δ * q + c) := rfl
      rw [e]
      exact continuousAt_const.add (((continuousAt_const.mul continuousAt_id).mul
        continuousAt_const).div ((continuousAt_const.mul continuousAt_id).add
          continuousAt_const) (by change δ * Q + c ≠ 0; positivity))
    exact tendsto_nhds_unique (hcont.tendsto.comp hlim)
      (hlim.comp (tendsto_add_atTop_nat 1))
  refine ⟨Q, hlim, hfix, ?_, ?_⟩
  · have hQpos : 0 < Q := by
      have h1 : b ≤ Q := by
        have := le_ciSup (f := qs b c δ) ⟨b + c, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩ 1
        have e1 : qs b c δ 1 = b := by change nextQ b c δ 0 = b; simp [nextQ]
        rwa [e1] at this
      linarith
    rw [← hfix]
    simp only [nextQ]
    have : 0 < δ * Q * c / (δ * Q + c) := by positivity
    linarith
  · rw [← hfix]; exact nextQ_lt hc hδ0 Q hQ0

omit ha hδ1 in
/-- `Tⁿv̂ = αₙx − βₙx²/2 + γₙ`. -/
theorem quad_iterate (n : ℕ) :
    (opT quadΓ (quadF a b c) δ)^[n] (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) =
      quadFn (ps a b c δ n) (qs b c δ n) (rs a b c δ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, quad_opT _ _ _ hc hδ0.le (qs_nonneg hb hc hδ0 n)]
    rfl

omit ha in
/-- (7)–(8): `αₙ → α` and `γₙ → γ`, solving `α = a + δαc/(δβ + c)` and
`γ = δγ + (δα)²/(2(δβ + c))`. -/
theorem tendsto_ps_rs : ∃ Q P R, Tendsto (qs b c δ) atTop (𝓝 Q) ∧ nextQ b c δ Q = Q ∧ b < Q ∧
    Q < b + c ∧ Tendsto (ps a b c δ) atTop (𝓝 P) ∧ nextP a c δ P Q = P ∧
    Tendsto (rs a b c δ) atTop (𝓝 R) ∧ nextR c δ P Q R = R := by
  obtain ⟨Q, hQ, hfix, hbQ, hQbc⟩ := tendsto_qs hb hc hδ0
  have hQ0 : 0 ≤ Q := by linarith
  set κ : ℕ → ℝ := fun n => δ * c / (δ * qs b c δ n + c)
  have hκ : ∀ n, 0 ≤ κ n ∧ κ n ≤ δ := fun n => by
    have h1 : 0 < δ * qs b c δ n + c := by have := qs_nonneg hb hc hδ0 n; positivity
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ h1]
    have := qs_nonneg hb hc hδ0 n
    nlinarith [mul_nonneg (mul_nonneg hδ0.le hδ0.le) this]
  have hκlim : Tendsto κ atTop (𝓝 (δ * c / (δ * Q + c))) :=
    tendsto_const_nhds.div ((hQ.const_mul δ).add_const c) (by positivity)
  have hP := tendsto_linear_recursion hδ1 hκ (u := fun _ => a) (x := ps a b c δ)
    (fun n => by simp only [ps, nextP, κ]; ring) tendsto_const_nhds hκlim
  set P := a / (1 - δ * c / (δ * Q + c))
  have hPfix : nextP a c δ P Q = P := by
    have hne : δ * Q + c ≠ 0 := by positivity
    have hne2 : 1 - δ * c / (δ * Q + c) ≠ 0 := by
      have : δ * c / (δ * Q + c) < 1 := by
        rw [div_lt_one (by positivity)]; nlinarith
      linarith
    have e : δ * P * c / (δ * Q + c) = (δ * c / (δ * Q + c)) * P := by ring
    simp only [nextP]
    rw [e]
    have h2 : P * (1 - δ * c / (δ * Q + c)) = a := div_mul_cancel₀ a hne2
    linear_combination (-1 : ℝ) * h2
  -- (8) with `κₙ = δ`
  have hd : Tendsto (fun n => (δ * ps a b c δ n) ^ 2 / (2 * (δ * qs b c δ n + c))) atTop
      (𝓝 ((δ * P) ^ 2 / (2 * (δ * Q + c)))) :=
    ((hP.const_mul δ).pow 2).div (((hQ.const_mul δ).add_const c).const_mul 2) (by positivity)
  have hR := tendsto_linear_recursion hδ1 (κ := fun _ => δ) (fun _ => ⟨hδ0.le, le_rfl⟩)
    (x := rs a b c δ) (fun n => by simp only [rs, nextR]; ring) hd tendsto_const_nhds
  refine ⟨Q, P, (δ * P) ^ 2 / (2 * (δ * Q + c)) / (1 - δ), hQ, hfix, hbQ, hQbc, hP, hPfix, hR,
    ?_⟩
  have hne : (1 - δ) ≠ 0 := by linarith
  simp only [nextR]
  field_simp
  ring

/-- **p. 96.** `v*(x) = αx − βx²/2 + γ` with the limits of (6)–(8). -/
theorem quad_vstar : ∃ P Q R, b < Q ∧ Q < b + c ∧ nextQ b c δ Q = Q ∧ nextP a c δ P Q = P ∧
    nextR c δ P Q R = R ∧ vstar quadΓ (quadF a b c) δ = quadFn P Q R := by
  obtain ⟨Q, P, R, hQ, hQfix, hbQ, hQbc, hP, hPfix, hR, hRfix⟩ :=
    tendsto_ps_rs hb hc hδ0 hδ1
  refine ⟨P, Q, R, hbQ, hQbc, hQfix, hPfix, hRfix, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have h42 : Assumption42 quadΓ (quadF a b c) δ :=
    assumption42_of_bddAbove (quadF_le hb hc) hδ0.le hδ1
  -- `Tv̂ ≤ v̂`
  have hTv : opT quadΓ (quadF a b c) δ (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) ≤
      quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ))) := by
    have e := quad_iterate hb hc hδ0 (a := a) 1
    rw [Function.iterate_one] at e
    rw [e]
    intro x
    have e1 : ps a b c δ 1 = a := by change nextP a c δ 0 0 = a; simp [nextP]
    have e2 : qs b c δ 1 = b := by change nextQ b c δ 0 = b; simp [nextQ]
    have e3 : rs a b c δ 1 = δ * (a ^ 2 / (2 * b * (1 - δ))) := by
      change nextR c δ 0 0 (a ^ 2 / (2 * b * (1 - δ))) = _; simp [nextR]
    simp only [quadFn, e1, e2, e3]
    refine EReal.coe_le_coe_iff.2 ?_
    have h2 : a * x - b * x ^ 2 / 2 ≤ a ^ 2 / (2 * b) := by
      have := quadF_le (a := a) hb hc x x
      simpa [quadF] using this
    have key : δ * (a ^ 2 / (2 * b * (1 - δ))) + a ^ 2 / (2 * b) = a ^ 2 / (2 * b * (1 - δ)) := by
      field_simp; ring
    linarith
  -- the iterates decrease to the quadratic limit
  have hlimfun : limitFn quadΓ (quadF a b c) δ (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) =
      quadFn P Q R := by
    funext x
    have hconv : Tendsto (fun n => (opT quadΓ (quadF a b c) δ)^[n]
        (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) x) atTop (𝓝 (quadFn P Q R x)) := by
      simp only [quad_iterate hb hc hδ0 (a := a)]
      exact EReal.tendsto_coe.2 (((hP.mul_const x).sub ((hQ.mul_const (x ^ 2)).div_const 2)).add
        hR)
    exact tendsto_nhds_unique (tendsto_iterate hδ0.le hTv x) hconv
  rw [← hlimfun]
  refine (theorem_4_14 (Γ := quadΓ) hδ0 (fun x => ⟨0, Set.mem_univ _⟩) h42 (fun x₀ x hx => ?_)
    (fun x₀ x hx => ?_) ?_).symm
  · -- (2): `δⁿv̂ → 0`
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).mul_const
      (a ^ 2 / (2 * b * (1 - δ)))
    rw [zero_mul] at h
    have : Tendsto (fun n => ((δ ^ n : ℝ) : EReal) *
        quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ))) (x n)) atTop (𝓝 0) := by
      refine (EReal.tendsto_coe.2 h).congr fun n => ?_
      simp [quadFn, EReal.coe_mul]
    exact this.limsup_eq.le
  · -- (3): `u(x) ≤ v̂(x₀)`
    have hps : ∀ n, (partialSum (quadF a b c) δ x n : EReal) ≤
        ((a ^ 2 / (2 * b * (1 - δ)) : ℝ) : EReal) := fun n => by
      refine EReal.coe_le_coe_iff.2 ?_
      calc partialSum (quadF a b c) δ x n
          ≤ ∑ t ∈ Finset.range (n + 1), δ ^ t * (a ^ 2 / (2 * b)) :=
            Finset.sum_le_sum fun t _ =>
              mul_le_mul_of_nonneg_left (quadF_le hb hc _ _) (pow_nonneg hδ0.le t)
        _ = (a ^ 2 / (2 * b)) * ∑ t ∈ Finset.range (n + 1), δ ^ t := by
            rw [Finset.mul_sum]; congr 1; funext t; ring
        _ ≤ (a ^ 2 / (2 * b)) * ∑' t, δ ^ t := mul_le_mul_of_nonneg_left
            ((summable_geometric_of_lt_one hδ0.le hδ1).sum_le_tsum _ fun t _ =>
              pow_nonneg hδ0.le t) (by positivity)
        _ = a ^ 2 / (2 * b * (1 - δ)) := by
            rw [tsum_geometric_of_lt_one hδ0.le hδ1]; field_simp
    have : quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ))) x₀ =
        ((a ^ 2 / (2 * b * (1 - δ)) : ℝ) : EReal) := by
      simp [quadFn]
    rw [this]
    exact le_of_tendsto' (tendsto_total h42 hx) hps
  · -- the limit is a fixed point
    rw [hlimfun, quad_opT _ _ _ hc hδ0.le (by linarith), hPfix, hQfix, hRfix]

/-- **p. 96.** The linear policy `g(x) = (δα + cx)/(δβ + c)` generates optimal plans. -/
theorem quad_policy_optimal (x₀ : ℝ) :
    ∃ P Q : ℝ, ∀ x : ℕ → ℝ, x 0 = x₀ → (∀ t, x (t + 1) = (δ * P + c * x t) / (δ * Q + c)) →
      total (quadF a b c) δ x = vstar quadΓ (quadF a b c) δ x₀ := by
  obtain ⟨P, Q, R, hbQ, -, hQfix, hPfix, hRfix, hvs⟩ := quad_vstar ha hb hc hδ0 hδ1
  refine ⟨P, Q, fun x hx0 hx => ?_⟩
  have hQ0 : 0 < Q := by linarith
  have hne : δ * Q + c ≠ 0 := by positivity
  have h42 : Assumption42 quadΓ (quadF a b c) δ :=
    assumption42_of_bddAbove (quadF_le hb hc) hδ0.le hδ1
  refine theorem_4_5 hδ0.le h42 ⟨hx0, fun _ => Set.mem_univ _⟩ (fun t => ?_) ?_
  · -- (9): the value at the maximizer
    rw [hvs, quadFn, quadFn, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    have h := quad_objective (a := a) (b := b) P Q R (x t) (x (t + 1)) hc hδ0.le hQ0.le
    have hz : x (t + 1) - (δ * P + c * x t) / (δ * Q + c) = 0 := by rw [hx t]; ring
    rw [hz, hPfix, hQfix, hRfix] at h
    rw [h]
    ring
  · -- (11): the plan contracts towards `P/Q`, so it stays bounded
    set s := c / (δ * Q + c)
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    set xbar := P / Q
    have hstep : ∀ t, x (t + 1) - xbar = s * (x t - xbar) := fun t => by
      rw [hx t]; simp only [s, xbar]; field_simp; ring
    have hdist : ∀ t, |x t - xbar| ≤ |x₀ - xbar| := by
      intro t
      induction t with
      | zero => rw [hx0]
      | succ t ih =>
        rw [hstep, abs_mul, abs_of_nonneg hs0]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs1).trans ih
    set M := |xbar| + |x₀ - xbar|
    have hxM : ∀ t, |x t| ≤ M := fun t => by
      have := hdist t
      calc |x t| = |(x t - xbar) + xbar| := by ring_nf
        _ ≤ |x t - xbar| + |xbar| := abs_add_le _ _
        _ ≤ M := by simp only [M]; linarith
    set K := |P| * M + Q * M ^ 2 / 2 + |R|
    have hbound : ∀ t, ((δ ^ t : ℝ) : EReal) * vstar quadΓ (quadF a b c) δ (x t) ≤
        ((K * δ ^ t : ℝ) : EReal) := fun t => by
      rw [hvs, quadFn, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.2 ?_
      have hPx : |P * x t| ≤ |P| * M := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hxM t) (abs_nonneg P)
      have h1 : P * x t ≤ |P| * M := (le_abs_self _).trans hPx
      have h2 : 0 ≤ Q * x t ^ 2 / 2 := by positivity
      have h3 : P * x t - Q * x t ^ 2 / 2 + R ≤ K := by
        simp only [K]
        have : 0 ≤ Q * M ^ 2 / 2 := by positivity
        linarith [le_abs_self R]
      rw [mul_comm K]
      exact mul_le_mul_of_nonneg_left h3 (pow_nonneg hδ0.le t)
    have hzero : Tendsto (fun t => ((K * δ ^ t : ℝ) : EReal)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).const_mul K
      simpa using EReal.tendsto_coe.2 this
    exact (limsup_le_limsup (Eventually.of_forall hbound)).trans hzero.limsup_eq.le

end StokeyLucasPrescott.DeterministicDP

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

namespace StokeyLucasPrescott.DeterministicDP

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

end StokeyLucasPrescott.DeterministicDP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policies from the Euler equations

SLP Exercise 4.9, pp. 99–100.

* `ex_4_9a`: in the unit-elastic growth model `F(k, y) = ln(k^α − y)` on `k > 0`, the plan
  `k_{t+1} = αβk_t^α` satisfies the Euler equations and the transversality condition, so it is
  optimal by Theorem 4.15.
* `ex_4_9b`: in the quadratic investment model `F(x, y) = ax − bx²/2 − c(y − x)²/2` on `ℝ`, the
  linear policy `g(x) = (δα + cx)/(δβ + c)` satisfies the Euler equations and is optimal.
  Theorem 4.15 itself does not apply, since the state space is `ℝ` and `F_x` takes both signs.
  The sufficiency argument goes through with `euler_sufficient`: a plan with `u(x) > −∞` has
  `Σ δᵗx_t² < ∞`, so `δᵗx_t → 0` and the boundary terms vanish.
-/

open Filter Topology Real

namespace StokeyLucasPrescott.DeterministicDP

/-! ### Exercise 4.9a: the unit-elastic growth model -/

variable {α β : ℝ}

/-- `Γ(k) = {y : 0 < y < k^α}` for `k > 0` (empty otherwise). -/
def egΓ (α : ℝ) (k : ℝ) : Set ℝ := {y | 0 < k ∧ 0 < y ∧ y < k ^ α}

/-- `F(k, y) = ln(k^α − y)`. -/
noncomputable def egF (α : ℝ) (p : ℝ × ℝ) : ℝ := Real.log (p.1 ^ α - p.2)

/-- The derivative of `F` at `(k, y)`. -/
noncomputable def egD (α k y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (k ^ α - y)⁻¹ • ((α * k ^ (α - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem egF_hasFDerivAt {k y : ℝ} (hk : 0 < k) (hy : y < k ^ α) :
    HasFDerivAt (egF α) (egD α k y) (k, y) := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (k, y))).rpow_const
    (p := α) (Or.inl hk.ne')
  have h2 := (h1.sub (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (k, y)))).log
    (by simp; linarith)
  exact h2

theorem egFx (k y v : ℝ) : Fx (egD α k y) v = (k ^ α - y)⁻¹ * (α * k ^ (α - 1) * v) := by
  simp [Fx, egD]

theorem egFy (k y w : ℝ) : Fy (egD α k y) w = -((k ^ α - y)⁻¹ * w) := by
  simp [Fy, egD]

/-- The graph `{(k, y) : k > 0, 0 < y < k^α}` is convex and `F` is concave on it. -/
theorem egF_concave (hα0 : 0 < α) (hα1 : α < 1) :
    ConcaveOn ℝ {p : ℝ × ℝ | p.2 ∈ egΓ α p.1} (egF α) := by
  have hrp := Real.concaveOn_rpow hα0.le hα1.le
  have hconv : Convex ℝ {p : ℝ × ℝ | p.2 ∈ egΓ α p.1} := by
    rintro ⟨k, y⟩ ⟨hk, hy0, hy⟩ ⟨k', y'⟩ ⟨hk', hy0', hy'⟩ a b ha hb hab
    have hc := hrp.2 (Set.mem_Ici.2 hk.le) (Set.mem_Ici.2 hk'.le) ha hb hab
    simp only [smul_eq_mul] at hc
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    · rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab; subst hab; simp [hk']
      · nlinarith
    · rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab; subst hab; simp [hy0']
      · nlinarith
    · rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab; subst hab; simp [hy']
      · nlinarith
  refine ⟨hconv, ?_⟩
  rintro ⟨k, y⟩ ⟨hk, hy0, hy⟩ ⟨k', y'⟩ ⟨hk', hy0', hy'⟩ a b ha hb hab
  have hc := hrp.2 (Set.mem_Ici.2 hk.le) (Set.mem_Ici.2 hk'.le) ha hb hab
  simp only [smul_eq_mul] at hc
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (by linarith : 0 < k ^ α - y))
    (Set.mem_Ioi.2 (by linarith : 0 < k' ^ α - y')) ha hb hab
  simp only [smul_eq_mul] at hlog
  simp only [egF, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine hlog.trans (Real.log_le_log ?_ (by linarith))
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp; linarith
  · nlinarith

/-- Feasible plans are positive. -/
theorem eg_pos {x₀ : ℝ} {x : ℕ → ℝ} (hx : x ∈ Feasible (egΓ α) x₀) (t : ℕ) : 0 < x t :=
  (hx.2 t).1

theorem eg_assumption42 (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Assumption42 (egΓ α) (fun x y => egF α (x, y)) β := by
  refine assumption42_of_summable_pos fun x₀ x hx => ?_
  have hx0 : 0 < x₀ := hx.1 ▸ eg_pos hx 0
  have hlog : ∀ t, Real.log (x t) ≤ α ^ t * Real.log x₀ := by
    intro t
    induction t with
    | zero => simp [hx.1]
    | succ t ih =>
      have h := Real.log_lt_log (hx.2 t).2.1 (hx.2 t).2.2
      rw [Real.log_rpow (eg_pos hx t)] at h
      calc Real.log (x (t + 1)) ≤ α * Real.log (x t) := h.le
        _ ≤ α * (α ^ t * Real.log x₀) := mul_le_mul_of_nonneg_left ih hα0.le
        _ = α ^ (t + 1) * Real.log x₀ := by ring
  have hαβ : α * β < 1 := by nlinarith
  refine summable_max_of_le_geometric (mul_pos hα0 hβ0).le hαβ
    (by positivity : (0 : ℝ) ≤ α * |Real.log x₀|) fun t => ?_
  have hpos : 0 < x t ^ α - x (t + 1) := by linarith [(hx.2 t).2.2]
  have hF : egF α (x t, x (t + 1)) ≤ α * Real.log (x t) := by
    simp only [egF]
    rw [← Real.log_rpow (eg_pos hx t)]
    exact Real.log_le_log hpos (by linarith [(hx.2 t).2.1])
  calc β ^ t * egF α (x t, x (t + 1)) ≤ β ^ t * (α * (α ^ t * |Real.log x₀|)) := by
        refine mul_le_mul_of_nonneg_left (hF.trans (mul_le_mul_of_nonneg_left ((hlog t).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hα0.le t))) hα0.le))
          (pow_nonneg hβ0.le t)
    _ = α * |Real.log x₀| * (α * β) ^ t := by rw [mul_pow]; ring

/-- **Exercise 4.9a.** The plan `k_{t+1} = αβk_t^α` from `k₀ > 0` is optimal (Theorem 4.15). -/
theorem ex_4_9a (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) {k₀ : ℝ}
    (hk₀ : 0 < k₀) :
    total (fun x y => egF α (x, y)) β (fun t => (fun k => α * β * k ^ α)^[t] k₀) =
      vstar (egΓ α) (fun x y => egF α (x, y)) β k₀ := by
  have hαβ : α * β < 1 := by nlinarith
  have hab : 0 < α * β := mul_pos hα0 hβ0
  set k : ℕ → ℝ := fun t => (fun k => α * β * k ^ α)^[t] k₀
  have hk : ∀ t, k (t + 1) = α * β * k t ^ α := fun t => Function.iterate_succ_apply' _ _ _
  have hkpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk₀
    | succ t ih => rw [hk]; have := rpow_pos_of_pos ih α; positivity
  have hlt : ∀ t, k (t + 1) < k t ^ α := fun t => by
    rw [hk]; have := rpow_pos_of_pos (hkpos t) α; nlinarith
  have hfeas : k ∈ Feasible (egΓ α) k₀ := ⟨rfl, fun t => ⟨hkpos t, hkpos (t + 1), hlt t⟩⟩
  -- consumption `c_t = (1 − αβ)k_t^α`
  have hc : ∀ t, k t ^ α - k (t + 1) = (1 - α * β) * k t ^ α := fun t => by rw [hk]; ring
  refine theorem_4_15 (eg_assumption42 hα0 hα1 hβ0 hβ1) hβ0.le (egF_concave hα0 hα1)
    (fun x₀ x hx t => (eg_pos hx t).le) hfeas (fun t => egD α (k t) (k (t + 1)))
    (fun t => egF_hasFDerivAt (hkpos t) (hlt t)) (fun t v hv => ?_) (fun t v => ?_) ?_
  · rw [egFx]
    have := rpow_pos_of_pos (hkpos t) (α - 1)
    have hpos : 0 < k t ^ α - k (t + 1) := by linarith [hlt t]
    positivity
  · -- the Euler equation
    rw [egFy, egFx, hc, hc]
    have hK := rpow_pos_of_pos (hkpos t) α
    have hK' := rpow_pos_of_pos (hkpos (t + 1)) α
    rw [Real.rpow_sub_one (hkpos (t + 1)).ne', hk t]
    have hne : 1 - α * β ≠ 0 := by linarith
    field_simp
    ring
  · -- transversality: `βᵗF_x·k_t = βᵗα/(1 − αβ)`
    have e : ∀ t, β ^ t * Fx (egD α (k t) (k (t + 1))) (k t) = α / (1 - α * β) * β ^ t := by
      intro t
      rw [egFx, hc, Real.rpow_sub_one (hkpos t).ne']
      have hK := rpow_pos_of_pos (hkpos t) α
      have hne : 1 - α * β ≠ 0 := by linarith
      have := (hkpos t).ne'
      field_simp
    simp only [e]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (α / (1 - α * β))

/-! ### Exercise 4.9b: the quadratic investment model -/

variable {a b c δ : ℝ}

/-- `F(x, y) = ax − bx²/2 − c(y − x)²/2`. -/
noncomputable def qF (a b c : ℝ) (p : ℝ × ℝ) : ℝ :=
  a * p.1 - b * p.1 ^ 2 / 2 - c * (p.2 - p.1) ^ 2 / 2

/-- Its derivative at `(x, y)`: `F_x = a − bx + c(y − x)`, `F_y = −c(y − x)`. -/
noncomputable def qD (a b c x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (a - b * x + c * (y - x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (-(c * (y - x))) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem qFx (x y v : ℝ) : Fx (qD a b c x y) v = (a - b * x + c * (y - x)) * v := by
  simp [Fx, qD]

theorem qFy (x y w : ℝ) : Fy (qD a b c x y) w = -(c * (y - x)) * w := by
  simp [Fy, qD]

/-- `F` lies below its tangent planes: the gap is `−b(x − x*)²/2 − c((y − x) − (y* − x*))²/2`. -/
theorem qF_le (hb : 0 < b) (hc : 0 < c) (x y x' y' : ℝ) :
    qF a b c (x, y) ≤ qF a b c (x', y') + qD a b c x' y' ((x, y) - (x', y')) := by
  simp only [qF, qD, Prod.mk_sub_mk, FunLike.coe_add, FunLike.coe_smul,
    Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  nlinarith [sq_nonneg (x - x'), sq_nonneg ((y - x) - (y' - x'))]

/-- **Exercise 4.9b.** If `β` and `α` solve (6)–(7) in the limit,
`β = b + δβc/(δβ + c)` and `α = a + δαc/(δβ + c)` with `β > 0`, then the linear policy
`g(x) = (δα + cx)/(δβ + c)` satisfies the Euler equations and generates optimal plans. -/
theorem ex_4_9b (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {P Q : ℝ} (hQ0 : 0 < Q) (hQ : b + δ * Q * c / (δ * Q + c) = Q)
    (hP : a + δ * P * c / (δ * Q + c) = P) {x₀ : ℝ} {x : ℕ → ℝ} (hx0 : x 0 = x₀)
    (hx : ∀ t, x (t + 1) = (δ * P + c * x t) / (δ * Q + c)) :
    total (fun x y => qF a b c (x, y)) δ x =
      vstar (fun _ => Set.univ) (fun x y => qF a b c (x, y)) δ x₀ := by
  set K := δ * Q + c with hKdef
  have hK : 0 < K := by positivity
  have hFle : ∀ x y, qF a b c (x, y) ≤ a ^ 2 / (2 * b) := fun x y => by
    simp only [qF]
    have e : a ^ 2 / (2 * b) - (a * x - b * x ^ 2 / 2) = (b * x - a) ^ 2 / (2 * b) := by
      field_simp; ring
    have : 0 ≤ (b * x - a) ^ 2 / (2 * b) := by positivity
    nlinarith [sq_nonneg (y - x)]
  have h42 : Assumption42 (fun _ => Set.univ) (fun x y => qF a b c (x, y)) δ :=
    assumption42_of_bddAbove (fun x y => hFle x y) hδ0.le hδ1
  -- the plan is bounded: it contracts towards `P/Q`
  have hs1 : c / K ≤ 1 := by rw [div_le_one hK]; nlinarith
  have hstep : ∀ t, x (t + 1) - P / Q = c / K * (x t - P / Q) := fun t => by
    rw [hx t]
    have hb' : b * K = Q * K - δ * Q * c := by
      have := hQ; field_simp at this; linarith
    field_simp
    ring_nf
    nlinarith [hb']
  have hxb : ∀ t, |x t - P / Q| ≤ |x₀ - P / Q| := by
    intro t
    induction t with
    | zero => rw [hx0]
    | succ t ih =>
      rw [hstep, abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs1).trans ih
  set M := |P / Q| + |x₀ - P / Q|
  have hxM : ∀ t, |x t| ≤ M := fun t => by
    have := hxb t
    calc |x t| = |(x t - P / Q) + P / Q| := by ring_nf
      _ ≤ |x t - P / Q| + |P / Q| := abs_add_le _ _
      _ ≤ M := by simp only [M]; linarith
  refine euler_sufficient h42 ⟨hx0, fun _ => Set.mem_univ _⟩
    (fun t => qD a b c (x t) (x (t + 1))) (fun t x y _ => qF_le hb hc x y _ _)
    (fun t v => ?_) hδ0.le (fun y hy hbot => ?_)
  · -- the Euler equation along the linear policy
    rw [qFy, qFx, hx (t + 1), hx t]
    have ha2 : a = P - δ * P * c / K := by linarith
    have hb2 : b = Q - δ * Q * c / K := by linarith
    have hne : δ * Q + c ≠ 0 := hK.ne'
    rw [ha2, hb2, hKdef]
    field_simp
    ring
  · -- against a plan with `u(y) > −∞`, `Σ δᵗy_t² < ∞`, so `δᵗy_t → 0`
    have hFsq : ∀ u w, qF a b c (u, w) ≤ a ^ 2 / b - b / 4 * u ^ 2 := fun u w => by
      simp only [qF]
      have e : a ^ 2 / b - a * u + b * u ^ 2 / 4 = (2 * a - b * u) ^ 2 / (4 * b) := by
        field_simp; ring
      have : 0 ≤ (2 * a - b * u) ^ 2 / (4 * b) := by positivity
      nlinarith [sq_nonneg (w - u)]
    have hsum : Summable fun t => δ ^ t * y t ^ 2 := by
      by_contra hns
      have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
        (fun t => mul_nonneg (pow_nonneg hδ0.le t) (sq_nonneg (y t)))).1 hns
      -- then `u_T(y) → −∞`
      have hbound : ∀ T, partialSum (fun x y => qF a b c (x, y)) δ y T ≤
          a ^ 2 / (b * (1 - δ)) - b / 4 * ∑ t ∈ Finset.range (T + 1), δ ^ t * y t ^ 2 := by
        intro T
        have h1 : partialSum (fun x y => qF a b c (x, y)) δ y T ≤
            ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b - b / 4 * y t ^ 2) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hFsq _ _)
            (pow_nonneg hδ0.le t)
        have h2 : ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b) ≤ a ^ 2 / (b * (1 - δ)) := by
          rw [← Finset.sum_mul]
          calc (∑ t ∈ Finset.range (T + 1), δ ^ t) * (a ^ 2 / b)
              ≤ (∑' t, δ ^ t) * (a ^ 2 / b) := mul_le_mul_of_nonneg_right
                ((summable_geometric_of_lt_one hδ0.le hδ1).sum_le_tsum _
                  fun t _ => pow_nonneg hδ0.le t) (by positivity)
            _ = a ^ 2 / (b * (1 - δ)) := by
                rw [tsum_geometric_of_lt_one hδ0.le hδ1]
                have : (1 - δ) ≠ 0 := by linarith
                field_simp
        have e : ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b - b / 4 * y t ^ 2) =
            ∑ t ∈ Finset.range (T + 1), δ ^ t * (a ^ 2 / b) -
              b / 4 * ∑ t ∈ Finset.range (T + 1), δ ^ t * y t ^ 2 := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun t _ => by ring
        linarith
      have hQ := ((hdiv.comp (tendsto_add_atTop_nat 1)).const_mul_atTop
        (by positivity : (0 : ℝ) < b / 4))
      have hlow : Tendsto (fun T => a ^ 2 / (b * (1 - δ)) - b / 4 *
          ∑ t ∈ Finset.range (T + 1), δ ^ t * y t ^ 2) atTop atBot := by
        simp only [sub_eq_add_neg]
        exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp hQ)
      have hneg : Tendsto (fun T => partialSum (fun x y => qF a b c (x, y)) δ y T) atTop
          atBot := tendsto_atBot_mono hbound hlow
      exact hbot (tendsto_nhds_unique (tendsto_total h42 hy)
        (EReal.tendsto_coe_atBot.comp hneg))
    -- `δᵗ|y_t| → 0`
    have hsq := hsum.tendsto_atTop_zero
    have hz : Tendsto (fun t => δ ^ t * |y t|) atTop (𝓝 0) := by
      have hsqrt := ((Real.continuous_sqrt.tendsto 0).comp hsq)
      rw [Real.sqrt_zero] at hsqrt
      refine squeeze_zero (fun t => by positivity) (fun t => ?_) hsqrt
      simp only [Function.comp_apply]
      rw [← Real.sqrt_sq (by positivity : 0 ≤ δ ^ t * |y t|)]
      refine Real.sqrt_le_sqrt ?_
      rw [mul_pow, sq_abs, ← pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hδ0.le hδ1.le (by omega))
        (sq_nonneg _)
    -- the bound on `F_x` along the policy plan
    set Cf := |a| + b * M + 2 * c * M
    have hf : ∀ t, |a - b * x t + c * (x (t + 1) - x t)| ≤ Cf := fun t => by
      have h1 := hxM t
      have h2 := hxM (t + 1)
      calc |a - b * x t + c * (x (t + 1) - x t)|
          ≤ |a| + b * |x t| + c * (|x (t + 1)| + |x t|) := by
            refine (abs_add_le _ _).trans ?_
            refine add_le_add ((abs_sub _ _).trans ?_) ?_
            · rw [abs_mul, abs_of_pos hb]
            · rw [abs_mul, abs_of_pos hc]
              exact mul_le_mul_of_nonneg_left (abs_sub _ _) hc.le
        _ ≤ Cf := by simp only [Cf]; nlinarith
    refine ⟨fun T => Cf * (δ ^ (T + 1) * M + δ ^ (T + 1) * |y (T + 1)|), ?_, fun T => ?_⟩
    · have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).comp
        (tendsto_add_atTop_nat 1)
      have h2 := hz.comp (tendsto_add_atTop_nat 1)
      have := ((h1.mul_const M).add h2).const_mul Cf
      simpa [Function.comp_def] using this
    · rw [qFx]
      have hδp : 0 ≤ δ ^ (T + 1) := pow_nonneg hδ0.le _
      calc δ ^ (T + 1) * ((a - b * x (T + 1) + c * (x (T + 1 + 1) - x (T + 1))) *
            (x (T + 1) - y (T + 1)))
          ≤ δ ^ (T + 1) * (Cf * (M + |y (T + 1)|)) := by
            refine mul_le_mul_of_nonneg_left ?_ hδp
            refine (le_abs_self _).trans ?_
            rw [abs_mul]
            refine mul_le_mul (hf _) ((abs_sub _ _).trans (add_le_add (hxM _) le_rfl))
              (abs_nonneg _) (by simp only [Cf]; positivity)
        _ = Cf * (δ ^ (T + 1) * M + δ ^ (T + 1) * |y (T + 1)|) := by ring

end StokeyLucasPrescott.DeterministicDP

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.DeterministicDP.addIso
#print axioms StokeyLucasPrescott.DeterministicDP.addIso_apply
#print axioms StokeyLucasPrescott.DeterministicDP.mulIso
#print axioms StokeyLucasPrescott.DeterministicDP.mulIso_apply
#print axioms StokeyLucasPrescott.DeterministicDP.add_mul_biSup
#print axioms StokeyLucasPrescott.DeterministicDP.continuous_add_mul
#print axioms StokeyLucasPrescott.DeterministicDP.coe_mul_add
#print axioms StokeyLucasPrescott.DeterministicDP.le_of_le_add_limsup
#print axioms StokeyLucasPrescott.DeterministicDP.le_of_add_le_liminf
#print axioms StokeyLucasPrescott.DeterministicDP.le_of_forall_coe_lt_le
#print axioms StokeyLucasPrescott.DeterministicDP.eq_biSup_iff
#print axioms StokeyLucasPrescott.DeterministicDP.Feasible
#print axioms StokeyLucasPrescott.DeterministicDP.partialSum
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption41
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption42
#print axioms StokeyLucasPrescott.DeterministicDP.total
#print axioms StokeyLucasPrescott.DeterministicDP.vstar
#print axioms StokeyLucasPrescott.DeterministicDP.SatisfiesFE
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_total
#print axioms StokeyLucasPrescott.DeterministicDP.tail
#print axioms StokeyLucasPrescott.DeterministicDP.tail_mem
#print axioms StokeyLucasPrescott.DeterministicDP.tail_tail
#print axioms StokeyLucasPrescott.DeterministicDP.consPlan
#print axioms StokeyLucasPrescott.DeterministicDP.consPlan_mem
#print axioms StokeyLucasPrescott.DeterministicDP.tail_consPlan
#print axioms StokeyLucasPrescott.DeterministicDP.feasible_nonempty
#print axioms StokeyLucasPrescott.DeterministicDP.partialSum_succ
#print axioms StokeyLucasPrescott.DeterministicDP.partialSum_succ'
#print axioms StokeyLucasPrescott.DeterministicDP.lemma_4_1
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_2
#print axioms StokeyLucasPrescott.DeterministicDP.total_le_of_FE
#print axioms StokeyLucasPrescott.DeterministicDP.div_lt_of_lt_add_mul
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_3a
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_3
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_3b
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_4
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_4_beta_zero
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_5
#print axioms StokeyLucasPrescott.DeterministicDP.Gstar
#print axioms StokeyLucasPrescott.DeterministicDP.optimal_generated_by_Gstar
#print axioms StokeyLucasPrescott.DeterministicDP.generated_by_Gstar_optimal
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_of_summable_pos
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_of_summable_neg
#print axioms StokeyLucasPrescott.DeterministicDP.assumption42_of_summable_pos
#print axioms StokeyLucasPrescott.DeterministicDP.assumption42_of_summable_neg
#print axioms StokeyLucasPrescott.DeterministicDP.summable_max_of_le_geometric
#print axioms StokeyLucasPrescott.DeterministicDP.assumption42_of_bddAbove
#print axioms StokeyLucasPrescott.DeterministicDP.assumption42_of_bddBelow
#print axioms StokeyLucasPrescott.DeterministicDP.assumption42_of_geometric
#print axioms StokeyLucasPrescott.DeterministicDP.Orthant
#print axioms StokeyLucasPrescott.DeterministicDP.orthCombo
#print axioms StokeyLucasPrescott.DeterministicDP.orthZero
#print axioms StokeyLucasPrescott.DeterministicDP.orthOne
#print axioms StokeyLucasPrescott.DeterministicDP.norm_le_geometric
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_2a
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_2b
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_1a
#print axioms StokeyLucasPrescott.DeterministicDP.consSet
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_1b
#print axioms StokeyLucasPrescott.DeterministicDP.consF
#print axioms StokeyLucasPrescott.DeterministicDP.partialSum_consF
#print axioms StokeyLucasPrescott.DeterministicDP.monotone_partialSum_consF
#print axioms StokeyLucasPrescott.DeterministicDP.borrowΓ
#print axioms StokeyLucasPrescott.DeterministicDP.borrow_assumption41
#print axioms StokeyLucasPrescott.DeterministicDP.borrow_assumption42
#print axioms StokeyLucasPrescott.DeterministicDP.borrow_vstar
#print axioms StokeyLucasPrescott.DeterministicDP.borrow_identity_FE
#print axioms StokeyLucasPrescott.DeterministicDP.borrow_identity_not_8
#print axioms StokeyLucasPrescott.DeterministicDP.NNR
#print axioms StokeyLucasPrescott.DeterministicDP.saveΓ
#print axioms StokeyLucasPrescott.DeterministicDP.saveF
#print axioms StokeyLucasPrescott.DeterministicDP.save_partialSum
#print axioms StokeyLucasPrescott.DeterministicDP.save_assumption41
#print axioms StokeyLucasPrescott.DeterministicDP.save_assumption42
#print axioms StokeyLucasPrescott.DeterministicDP.save_vstar
#print axioms StokeyLucasPrescott.DeterministicDP.save_all_satisfy_9
#print axioms StokeyLucasPrescott.DeterministicDP.hoard
#print axioms StokeyLucasPrescott.DeterministicDP.hoard_mem
#print axioms StokeyLucasPrescott.DeterministicDP.save_hoard_total
#print axioms StokeyLucasPrescott.DeterministicDP.save_hoard_not_11
#print axioms StokeyLucasPrescott.DeterministicDP.IsContraction
#print axioms StokeyLucasPrescott.DeterministicDP.IsContraction.uniformContinuous
#print axioms StokeyLucasPrescott.DeterministicDP.dist_iterate_succ_le
#print axioms StokeyLucasPrescott.DeterministicDP.dist_iterate_le
#print axioms StokeyLucasPrescott.DeterministicDP.cauchySeq_iterate
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_3_2
#print axioms StokeyLucasPrescott.DeterministicDP.dist_fixedPoint_le
#print axioms StokeyLucasPrescott.DeterministicDP.corollary_1
#print axioms StokeyLucasPrescott.DeterministicDP.corollary_2
#print axioms StokeyLucasPrescott.DeterministicDP.IsLHC
#print axioms StokeyLucasPrescott.DeterministicDP.IsUHC
#print axioms StokeyLucasPrescott.DeterministicDP.graph
#print axioms StokeyLucasPrescott.DeterministicDP.continuousAt_of_isUHC_singleton
#print axioms StokeyLucasPrescott.DeterministicDP.isCompact_graph
#print axioms StokeyLucasPrescott.DeterministicDP.maxValue
#print axioms StokeyLucasPrescott.DeterministicDP.argmax
#print axioms StokeyLucasPrescott.DeterministicDP.continuousOn_section
#print axioms StokeyLucasPrescott.DeterministicDP.exists_argmax
#print axioms StokeyLucasPrescott.DeterministicDP.le_maxValue
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_f_graph
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_3_6
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.mk
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.nonempty
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.compact
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.lhc
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.uhc
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.cont
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.unique
#print axioms StokeyLucasPrescott.DeterministicDP.argmaxFn
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.argmaxFn_mem
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.argmax_eq
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.lt_of_ne
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.continuous_argmaxFn
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.lemma_3_7
#print axioms StokeyLucasPrescott.DeterministicDP.UniqueArgmax.lemma_3_7_uniform
#print axioms StokeyLucasPrescott.DeterministicDP.shortfall_lt
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_3_8
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_3_8_uniform
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption43
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption43.mk
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption43.nonempty
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption43.compact
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption43.lhc
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption43.uhc
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption44
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption44.mk
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption44.cont
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption44.bdd
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption44.β_pos
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption44.β_lt
#print axioms StokeyLucasPrescott.DeterministicDP.obj
#print axioms StokeyLucasPrescott.DeterministicDP.continuousOn_obj
#print axioms StokeyLucasPrescott.DeterministicDP.bound_maxValue
#print axioms StokeyLucasPrescott.DeterministicDP.bellman
#print axioms StokeyLucasPrescott.DeterministicDP.bellman_apply
#print axioms StokeyLucasPrescott.DeterministicDP.exists_bellman_argmax
#print axioms StokeyLucasPrescott.DeterministicDP.bellman_mono
#print axioms StokeyLucasPrescott.DeterministicDP.bellman_add_const
#print axioms StokeyLucasPrescott.DeterministicDP.blackwell
#print axioms StokeyLucasPrescott.DeterministicDP.bellman_contraction
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_6
#print axioms StokeyLucasPrescott.DeterministicDP.curryF
#print axioms StokeyLucasPrescott.DeterministicDP.assumption42_of_44
#print axioms StokeyLucasPrescott.DeterministicDP.satisfiesFE_of_fixed
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_bounded_discount
#print axioms StokeyLucasPrescott.DeterministicDP.fixedPoint_eq_vstar
#print axioms StokeyLucasPrescott.DeterministicDP.policy_plan_optimal
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_7
#print axioms StokeyLucasPrescott.DeterministicDP.cmb
#print axioms StokeyLucasPrescott.DeterministicDP.cmb_self
#print axioms StokeyLucasPrescott.DeterministicDP.IsConcaveS
#print axioms StokeyLucasPrescott.DeterministicDP.IsStrictConcaveS
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption47
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption48
#print axioms StokeyLucasPrescott.DeterministicDP.isClosed_concave
#print axioms StokeyLucasPrescott.DeterministicDP.bellman_maps_concave
#print axioms StokeyLucasPrescott.DeterministicDP.bellman_concave
#print axioms StokeyLucasPrescott.DeterministicDP.argmax_unique_of_strictConcave
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_8
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_9
#print axioms StokeyLucasPrescott.DeterministicDP.DiscreteSetup
#print axioms StokeyLucasPrescott.DeterministicDP.DiscreteSetup.mk
#print axioms StokeyLucasPrescott.DeterministicDP.DiscreteSetup.nonempty
#print axioms StokeyLucasPrescott.DeterministicDP.DiscreteSetup.finite
#print axioms StokeyLucasPrescott.DeterministicDP.DiscreteSetup.bdd
#print axioms StokeyLucasPrescott.DeterministicDP.DiscreteSetup.β_pos
#print axioms StokeyLucasPrescott.DeterministicDP.DiscreteSetup.β_lt
#print axioms StokeyLucasPrescott.DeterministicDP.maxD
#print axioms StokeyLucasPrescott.DeterministicDP.exists_maxD
#print axioms StokeyLucasPrescott.DeterministicDP.le_maxD
#print axioms StokeyLucasPrescott.DeterministicDP.bellmanD
#print axioms StokeyLucasPrescott.DeterministicDP.bellmanD_apply
#print axioms StokeyLucasPrescott.DeterministicDP.bellmanD_mono
#print axioms StokeyLucasPrescott.DeterministicDP.bellmanD_add_const
#print axioms StokeyLucasPrescott.DeterministicDP.bellmanD_contraction
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_4a
#print axioms StokeyLucasPrescott.DeterministicDP.policyOp
#print axioms StokeyLucasPrescott.DeterministicDP.policyOp_apply
#print axioms StokeyLucasPrescott.DeterministicDP.policyOp_mono
#print axioms StokeyLucasPrescott.DeterministicDP.policyOp_contraction
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_4b
#print axioms StokeyLucasPrescott.DeterministicDP.policyOp_le_bellmanD
#print axioms StokeyLucasPrescott.DeterministicDP.isClosed_ge
#print axioms StokeyLucasPrescott.DeterministicDP.isClosed_le'
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_4c
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_10
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_5
#print axioms StokeyLucasPrescott.DeterministicDP.dual_apply_eq_sum
#print axioms StokeyLucasPrescott.DeterministicDP.vertex
#print axioms StokeyLucasPrescott.DeterministicDP.no_separation
#print axioms StokeyLucasPrescott.DeterministicDP.eventually_mem_of_mem_interior
#print axioms StokeyLucasPrescott.DeterministicDP.liftS
#print axioms StokeyLucasPrescott.DeterministicDP.liftS_of_mem
#print axioms StokeyLucasPrescott.DeterministicDP.IsStrictConcaveS.isConcaveS
#print axioms StokeyLucasPrescott.DeterministicDP.concaveOn_liftS
#print axioms StokeyLucasPrescott.DeterministicDP.convex_image_Γ
#print axioms StokeyLucasPrescott.DeterministicDP.eventually_mem_Γ
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_11
#print axioms StokeyLucasPrescott.DeterministicDP.IsCone
#print axioms StokeyLucasPrescott.DeterministicDP.csmul
#print axioms StokeyLucasPrescott.DeterministicDP.InH
#print axioms StokeyLucasPrescott.DeterministicDP.hnorm
#print axioms StokeyLucasPrescott.DeterministicDP.hnorm_nonneg
#print axioms StokeyLucasPrescott.DeterministicDP.bddAbove_sphere
#print axioms StokeyLucasPrescott.DeterministicDP.abs_le_hnorm
#print axioms StokeyLucasPrescott.DeterministicDP.hnorm_le
#print axioms StokeyLucasPrescott.DeterministicDP.inH_sub
#print axioms StokeyLucasPrescott.DeterministicDP.inH_add
#print axioms StokeyLucasPrescott.DeterministicDP.inH_smul
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_7a_norm
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_7a_complete
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_12
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.mk
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.convex
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.nonempty
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.compact
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.lhc
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.uhc
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.cone
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.α_pos
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.αβ_lt
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption410.growth
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411.mk
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411.β_pos
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411.β_lt
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411.cont
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411.hom
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411.B_pos
#print axioms StokeyLucasPrescott.DeterministicDP.Assumption411.bdd
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_6a
#print axioms StokeyLucasPrescott.DeterministicDP.abs_term_le
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_6b
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_6c
#print axioms StokeyLucasPrescott.DeterministicDP.crs
#print axioms StokeyLucasPrescott.DeterministicDP.continuousOn_obj'
#print axioms StokeyLucasPrescott.DeterministicDP.exists_crs_argmax
#print axioms StokeyLucasPrescott.DeterministicDP.eq_zero_of_mem_zero
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_7b
#print axioms StokeyLucasPrescott.DeterministicDP.crs_mono
#print axioms StokeyLucasPrescott.DeterministicDP.crs_disc
#print axioms StokeyLucasPrescott.DeterministicDP.crs_contraction
#print axioms StokeyLucasPrescott.DeterministicDP.hnorm_sub_le
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_13
#print axioms StokeyLucasPrescott.DeterministicDP.satisfiesFE_crs
#print axioms StokeyLucasPrescott.DeterministicDP.crs_fixed_eq_vstar
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_6c_hom
#print axioms StokeyLucasPrescott.DeterministicDP.IsQuasiConcaveS
#print axioms StokeyLucasPrescott.DeterministicDP.IsStrictQuasiConcaveS
#print axioms StokeyLucasPrescott.DeterministicDP.cmb_eq_csmul_cmb
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_8a
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_8a_counterexample
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_8b
#print axioms StokeyLucasPrescott.DeterministicDP.NonProp
#print axioms StokeyLucasPrescott.DeterministicDP.ConcaveGraph
#print axioms StokeyLucasPrescott.DeterministicDP.crs_concave
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_8c
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_8d
#print axioms StokeyLucasPrescott.DeterministicDP.opT
#print axioms StokeyLucasPrescott.DeterministicDP.satisfiesFE_iff_opT
#print axioms StokeyLucasPrescott.DeterministicDP.opT_mono
#print axioms StokeyLucasPrescott.DeterministicDP.iterate_antitone
#print axioms StokeyLucasPrescott.DeterministicDP.limitFn
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_iterate
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_14
#print axioms StokeyLucasPrescott.DeterministicDP.PosR
#print axioms StokeyLucasPrescott.DeterministicDP.logΓ
#print axioms StokeyLucasPrescott.DeterministicDP.logF
#print axioms StokeyLucasPrescott.DeterministicDP.coefB
#print axioms StokeyLucasPrescott.DeterministicDP.coefC
#print axioms StokeyLucasPrescott.DeterministicDP.affineLog
#print axioms StokeyLucasPrescott.DeterministicDP.logPolicy
#print axioms StokeyLucasPrescott.DeterministicDP.αβ_lt_one
#print axioms StokeyLucasPrescott.DeterministicDP.coefB_pos
#print axioms StokeyLucasPrescott.DeterministicDP.coefC_neg
#print axioms StokeyLucasPrescott.DeterministicDP.logPolicy_mem
#print axioms StokeyLucasPrescott.DeterministicDP.log_objective_le
#print axioms StokeyLucasPrescott.DeterministicDP.log_opT_affine
#print axioms StokeyLucasPrescott.DeterministicDP.log_iterate
#print axioms StokeyLucasPrescott.DeterministicDP.log_assumption41
#print axioms StokeyLucasPrescott.DeterministicDP.log_capital_le
#print axioms StokeyLucasPrescott.DeterministicDP.logF_le
#print axioms StokeyLucasPrescott.DeterministicDP.log_assumption42
#print axioms StokeyLucasPrescott.DeterministicDP.log_vstar
#print axioms StokeyLucasPrescott.DeterministicDP.log_policy_optimal
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_zero_of_le_contract
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_linear_recursion
#print axioms StokeyLucasPrescott.DeterministicDP.quadF
#print axioms StokeyLucasPrescott.DeterministicDP.quadΓ
#print axioms StokeyLucasPrescott.DeterministicDP.quadFn
#print axioms StokeyLucasPrescott.DeterministicDP.nextQ
#print axioms StokeyLucasPrescott.DeterministicDP.nextP
#print axioms StokeyLucasPrescott.DeterministicDP.nextR
#print axioms StokeyLucasPrescott.DeterministicDP.quad_objective
#print axioms StokeyLucasPrescott.DeterministicDP.quad_opT
#print axioms StokeyLucasPrescott.DeterministicDP.quadF_le
#print axioms StokeyLucasPrescott.DeterministicDP.qs
#print axioms StokeyLucasPrescott.DeterministicDP.ps
#print axioms StokeyLucasPrescott.DeterministicDP.rs
#print axioms StokeyLucasPrescott.DeterministicDP.qs_nonneg
#print axioms StokeyLucasPrescott.DeterministicDP.nextQ_mono
#print axioms StokeyLucasPrescott.DeterministicDP.nextQ_lt
#print axioms StokeyLucasPrescott.DeterministicDP.qs_mono
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_qs
#print axioms StokeyLucasPrescott.DeterministicDP.quad_iterate
#print axioms StokeyLucasPrescott.DeterministicDP.tendsto_ps_rs
#print axioms StokeyLucasPrescott.DeterministicDP.quad_vstar
#print axioms StokeyLucasPrescott.DeterministicDP.quad_policy_optimal
#print axioms StokeyLucasPrescott.DeterministicDP.concave_le_fderiv
#print axioms StokeyLucasPrescott.DeterministicDP.Fx
#print axioms StokeyLucasPrescott.DeterministicDP.Fy
#print axioms StokeyLucasPrescott.DeterministicDP.apply_eq_Fx_add_Fy
#print axioms StokeyLucasPrescott.DeterministicDP.euler_telescope
#print axioms StokeyLucasPrescott.DeterministicDP.le_of_le_add_tendsto_zero
#print axioms StokeyLucasPrescott.DeterministicDP.euler_sufficient
#print axioms StokeyLucasPrescott.DeterministicDP.theorem_4_15
#print axioms StokeyLucasPrescott.DeterministicDP.euler_of_envelope
#print axioms StokeyLucasPrescott.DeterministicDP.egΓ
#print axioms StokeyLucasPrescott.DeterministicDP.egF
#print axioms StokeyLucasPrescott.DeterministicDP.egD
#print axioms StokeyLucasPrescott.DeterministicDP.egF_hasFDerivAt
#print axioms StokeyLucasPrescott.DeterministicDP.egFx
#print axioms StokeyLucasPrescott.DeterministicDP.egFy
#print axioms StokeyLucasPrescott.DeterministicDP.egF_concave
#print axioms StokeyLucasPrescott.DeterministicDP.eg_pos
#print axioms StokeyLucasPrescott.DeterministicDP.eg_assumption42
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_9a
#print axioms StokeyLucasPrescott.DeterministicDP.qF
#print axioms StokeyLucasPrescott.DeterministicDP.qD
#print axioms StokeyLucasPrescott.DeterministicDP.qFx
#print axioms StokeyLucasPrescott.DeterministicDP.qFy
#print axioms StokeyLucasPrescott.DeterministicDP.qF_le
#print axioms StokeyLucasPrescott.DeterministicDP.ex_4_9b
