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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The unit-elastic growth model, `0 < α ≤ 1`

SLP §4.4, pp. 93–95: `max Σ βᵗ ln(k_t^α − k_{t+1})` with `0 < β < 1` on `X = (0, ∞)`, where
returns are unbounded above and below. Chapter 4 takes `0 < α < 1`; here `α = 1` is allowed, which
is the cake-eating problem of Exercise 5.2b. The only change is in (11): the book's bound
`|ln k_t| ≤ |ln k₀| + |ln αβ|/(1 − α)` needs `α < 1`, and `|ln k_t| ≤ |ln k₀| + t|ln αβ|`, which
still gives `βᵗv*(k_t) → 0`, replaces it.

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

namespace StokeyLucasPrescott.DeterministicApplications

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

variable (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
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
  · -- (11): `|ln k_t| ≤ |ln k₀| + t|ln αβ|`, so `βᵗv*(k_t) → 0`
    set L := |Real.log (α * β)|
    have hlog : ∀ t : ℕ, |Real.log (k t).1| ≤ |Real.log k₀.1| + t * L := by
      intro t
      induction t with
      | zero => simp [k]
      | succ t ih =>
        rw [hk t]
        have hc : 0 < (k t).1 ^ α := rpow_pos_of_pos (k t).2 α
        have e : Real.log (g (k t)).1 = Real.log (α * β) + α * Real.log (k t).1 := by
          simp only [g, logPolicy]
          rw [Real.log_mul (mul_pos hα0 hβ0).ne' hc.ne', Real.log_rpow (k t).2]
        rw [e]
        have hαk : α * |Real.log (k t).1| ≤ |Real.log (k t).1| := by
          nlinarith [abs_nonneg (Real.log (k t).1)]
        calc |Real.log (α * β) + α * Real.log (k t).1|
            ≤ L + α * |Real.log (k t).1| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_of_pos hα0]
          _ ≤ |Real.log k₀.1| + ((t + 1 : ℕ) : ℝ) * L := by push_cast; linarith
    have hb : ∀ t : ℕ, ((β ^ t : ℝ) : EReal) * vstar (logΓ α) (logF α) β (k t) ≤
        (((|A| + coefB α β * |Real.log k₀.1|) * β ^ t + coefB α β * L * (t * β ^ t) : ℝ) :
          EReal) := fun t => by
      rw [hvs, affineLog, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.2 ?_
      have hB := coefB_pos hα0 hα1 hβ1
      have h1 : A + coefB α β * Real.log (k t).1 ≤
          |A| + coefB α β * (|Real.log k₀.1| + t * L) := by
        have := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (k t).1) |>.trans (hlog t))
          hB.le
        linarith [le_abs_self A]
      have := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ0.le t)
      linarith
    have hzero : Tendsto (fun t : ℕ => (((|A| + coefB α β * |Real.log k₀.1|) * β ^ t +
        coefB α β * L * (t * β ^ t) : ℝ) : EReal)) atTop (𝓝 0) := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul
        (|A| + coefB α β * |Real.log k₀.1|)
      have h2 := (tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul (coefB α β * L)
      simpa using EReal.tendsto_coe.2 (h1.add h2)
    exact (limsup_le_limsup (Eventually.of_forall hb)).trans hzero.limsup_eq.le

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A cake-eating problem

SLP §5.2, p. 105: the model of Section 5.1 with `f(k) = k`.

* `ex_5_2a_technology`, `ex_5_2a_not_T2`, `ex_5_2a`: `f(k) = k` satisfies (T1) and (T3)–(T5),
  but not the second half of (T2); any `x̄ > 0` defines `X = [0, x̄]`, because `[0, x̄]` is
  invariant (`GrowthHyp U id β x̄` holds), and feasible paths only fall (`cake_path_le`).
* `ex_5_2b`: for `U = ln`, `v(x) = ln x/(1 − β) + [ln(1 − β) + β ln β/(1 − β)]/(1 − β)`, and the
  policy `g(x) = βx` generates the optimal plan. This is the case `α = 1` of the unit-elastic
  model (`LogModel`), with state space `(0, ∞)` and `Γ(x) = (0, x)`.
* `ex_5_2c`: in general, on `[0, x̄]`, `v` is the supremum function, strictly increasing and
  strictly concave, and the policy is a continuous function (Exercise 5.1 with a weakly concave
  `f`, `ex_5_1c_weak`); under the Inada condition consumption and saving are both positive, and
  `v'(x) = U'(x − g(x))`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {U : ℝ → ℝ} {β xbar : ℝ}

/-- **Exercise 5.2a.** `f(k) = k` satisfies (T1) and (T3)–(T5). -/
theorem ex_5_2a_technology :
    Continuous (id : ℝ → ℝ) ∧ StrictMono (id : ℝ → ℝ) ∧ ConcaveOn ℝ (Ici 0) (id : ℝ → ℝ) ∧
      ContDiff ℝ 1 (id : ℝ → ℝ) :=
  ⟨continuous_id, strictMono_id, concaveOn_id (convex_Ici 0), contDiff_id⟩

/-- **Exercise 5.2a.** `f(k) = k` fails the second half of (T2): there is no `x̄` beyond which
`f(x) < x`. -/
theorem ex_5_2a_not_T2 : ¬ ∃ xbar : ℝ, ∀ x, xbar < x → (id : ℝ → ℝ) x < x := by
  rintro ⟨xbar, h⟩
  exact lt_irrefl _ (h (xbar + 1) (by linarith))

/-- **Exercise 5.2a.** Any `x̄ > 0` can be used to define `X`: (U1)–(U3) give the hypotheses of
Section 5.1 with `f(k) = k` on `[0, x̄]`. -/
theorem ex_5_2a (hβ0 : 0 < β) (hβ1 : β < 1) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) (hx : 0 < xbar) : GrowthHyp U id β xbar :=
  ⟨hβ0, hβ1, hUc, hUm, continuous_id.continuousOn, rfl, hx,
    fun _ hx' => ⟨le_rfl, hx'.2⟩, strictMono_id.strictMonoOn _⟩

/-- Feasible cake paths fall: `x_t ≤ x₀`, so `[0, x₀]` contains the whole path. -/
theorem cake_path_le {x : ℕ → ℝ} (hx : ∀ t, x (t + 1) ≤ x t) (t : ℕ) : x t ≤ x 0 := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (hx t).trans ih

/-- `Γ(x) = (0, x)` when `α = 1`. -/
theorem cake_logΓ (k : PosR) : logΓ 1 k = {y | y.1 < k.1} := by
  ext y; simp [logΓ, Real.rpow_one]

/-- `F(x, y) = ln(x − y)` when `α = 1`. -/
theorem cake_logF (k y : PosR) : logF 1 k y = Real.log (k.1 - y.1) := by
  simp [logF, Real.rpow_one]

/-- The policy `g(x) = βx` (`αβk^α` with `α = 1`). -/
theorem cake_policy (hβ0 : 0 < β) (k : PosR) : (logPolicy 1 β one_pos hβ0 k).1 = β * k.1 := by
  simp [logPolicy, Real.rpow_one]

/-- **Exercise 5.2b.** With `U = ln`,
`v(x) = ln x/(1 − β) + [ln(1 − β) + β ln β/(1 − β)]/(1 − β)`. -/
theorem ex_5_2b (hβ0 : 0 < β) (hβ1 : β < 1) :
    vstar (logΓ 1) (logF 1) β = fun k : PosR =>
      (((Real.log (1 - β) + β / (1 - β) * Real.log β) / (1 - β) +
        Real.log k.1 / (1 - β) : ℝ) : EReal) := by
  rw [log_vstar one_pos le_rfl hβ0 hβ1]
  funext k
  simp only [affineLog, coefB, coefC, one_mul]
  congr 1
  ring

/-- **Exercise 5.2b.** The policy `g(x) = βx` generates an optimal plan. -/
theorem ex_5_2b_policy (hβ0 : 0 < β) (hβ1 : β < 1) (k₀ : PosR) :
    total (logF 1) β (fun t => (logPolicy 1 β one_pos hβ0)^[t] k₀) =
      vstar (logΓ 1) (logF 1) β k₀ :=
  log_policy_optimal one_pos le_rfl hβ0 hβ1 k₀

/-- **Exercise 5.2c.** For any `U` satisfying (U1)–(U4), on `[0, x̄]`: `v` is the supremum
function, strictly increasing and strictly concave, and the policy is a continuous function. -/
theorem ex_5_2c [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U id β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    (fun x => (v x : EReal)) = vstar (growthΓ id xbar) (curryF (growthF U id xbar)) β ∧
      StrictMono v ∧ IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ id xbar) (obj (growthF U id xbar) β v) ∧
      Continuous (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v)) := by
  obtain ⟨u, -, huniq, hvs, hmono, -⟩ := ex_5_1ab h
  have hvu := huniq v hv
  subst hvu
  obtain ⟨h1, h2, h3⟩ := ex_5_1c_weak h hU (concaveOn_id (convex_Ici 0)) hv
  exact ⟨hvs, hmono, h1, h2, h3⟩

/-- **Exercise 5.2c.** Under the Inada condition `U'(0+) = ∞`, for `x > 0` the cake is neither
eaten at once nor left untouched: `0 < g(x) < x`. -/
theorem ex_5_2c_interior [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U id β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hinada : Tendsto (deriv U) (𝓝[>] 0) atTop) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    {x : Icc (0 : ℝ) xbar} (hx : 0 < x.1) :
    0 < (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v) x).1 ∧
      (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v) x).1 < x.1 :=
  ex_5_1d_interior h hU (concaveOn_id (convex_Ici 0)) hUd hinada hv hx

/-- **Exercise 5.2c.** Where saving is interior, `v'(x) = U'(x − g(x))`. -/
theorem ex_5_2c_deriv [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U id β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x₀ : Icc (0 : ℝ) xbar}
    (hx₀ : x₀.1 ∈ Ioo 0 xbar)
    (hgf : (argmaxFn (growthΓ id xbar) (obj (growthF U id xbar) β v) x₀).1 < x₀.1) {U' : ℝ}
    (hU' : HasDerivAt U U' (x₀.1 - (argmaxFn (growthΓ id xbar)
      (obj (growthF U id xbar) β v) x₀).1)) :
    HasDerivAt (liftR xbar v) U' x₀.1 := by
  have := ex_5_1d h hU (concaveOn_id (convex_Ici 0)) hv hx₀ hgf hU' (hasDerivAt_id x₀.1)
  simpa using this

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal growth with linear utility

SLP §5.3, p. 105: the model of Section 5.1 with `U(c) = c` and `f` satisfying (T1)–(T5). Let
`k*` maximize `βf(k) − k` and `A = βf(k*) − k*`.

* `ex_5_3a`: (U1)–(U3) hold, so Exercise 5.1a–b applies: `v` is the unique bounded continuous
  solution, equals `v*` and is strictly increasing, and `G` is nonempty and u.h.c.; `v` is
  concave. (U4) fails, but when `f` is strictly concave Assumption 4.7 still holds, so `v` is
  strictly concave and the policy is a continuous function (`ex_5_3a_strict`). The interior
  result of Exercise 5.1d fails: below `k*` nothing is consumed (`ex_5_3a_corner`).
* `kstar_le_xbar`: by (T2), `k*` lies in `X`.
* `linear_value_le`, `linear_value_eq`: `v(k) ≤ f(k) + A/(1 − β)` everywhere, with equality
  when `k* ≤ f(k)`.
* `ex_5_3b`: for some `ε > 0`, `|k − k*| < ε` implies `v(k) = f(k) − k* + β[f(k*) − k*]/(1 − β)`.
* `ex_5_3c`: the policy `g(k) = min{f(k), k*}` is optimal: jump to `k*` when it is feasible,
  otherwise invest everything.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {f : ℝ → ℝ} {β xbar : ℝ}

/-- **Exercise 5.3a.** With `U(c) = c` the conclusions of Exercise 5.1a–b hold, and `v` is
concave. -/
theorem ex_5_3a (h : GrowthHyp id f β xbar) (hf : ConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    (fun x => (v x : EReal)) = vstar (growthΓ f xbar) (curryF (growthF id f xbar)) β ∧
      StrictMono v ∧ IsConcaveS (convex_Icc 0 xbar) v ∧
      ∀ x, (argmax (obj (growthF id f xbar) β v) (growthΓ f xbar) x).Nonempty ∧
        IsUHC (argmax (obj (growthF id f xbar) β v) (growthΓ f xbar)) x := by
  obtain ⟨u, -, huniq, hvs, hmono, hG⟩ := ex_5_1ab h
  have hvu := huniq v hv
  subst hvu
  exact ⟨hvs, hmono, growth_concave h (concaveOn_id (convex_Ici 0)) hf hv, hG⟩

/-- **Exercise 5.3a.** Although (U4) fails, a strictly concave `f` gives Assumption 4.7, so `v`
is strictly concave and the policy is a continuous function. -/
theorem ex_5_3a_strict [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp id f β xbar)
    (hf : StrictConcaveOn ℝ (Ici 0) f) {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ f xbar) (obj (growthF id f xbar) β v) ∧
      Continuous (argmaxFn (growthΓ f xbar) (obj (growthF id f xbar) β v)) := by
  obtain ⟨h1, h2, -, h4⟩ := theorem_4_8 (growth_assumption43 h) (growth_assumption44 h)
    (growth_a47 h (concaveOn_id (convex_Ici 0)) hf) (growth_a48 hf.concaveOn) hv
  exact ⟨h1, h2, h4⟩

/-- By (T2), a maximizer of `βf(k) − k` over `k ≥ 0` lies in `[0, x̄]`. -/
theorem kstar_le_xbar (hβ : 0 < β) (hβ1 : β < 1) (hf0 : f 0 = 0) (hbelow : ∀ x, xbar < x → f x < x)
    {kstar : ℝ} (hk0 : 0 ≤ kstar) (hk : ∀ k, 0 ≤ k → β * f k - k ≤ β * f kstar - kstar) :
    kstar ≤ xbar := by
  by_contra hlt
  push Not at hlt
  have h1 := hbelow kstar hlt
  have h2 := hk 0 le_rfl
  rw [hf0] at h2
  nlinarith [mul_lt_mul_of_pos_left h1 hβ]

variable {kstar : Icc (0 : ℝ) xbar}

/-- `f(k*) ≥ k*`, since `βf(k*) − k* ≥ βf(0) − 0 = 0`. -/
theorem kstar_le_f (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1) :
    0 ≤ β * f kstar.1 - kstar.1 ∧ kstar.1 ≤ f kstar.1 := by
  have h0 := hk ⟨0, le_rfl, h.xbar_pos.le⟩
  simp only [h.f_zero, mul_zero, sub_zero] at h0
  have hf := growth_f_nonneg h kstar
  refine ⟨h0, ?_⟩
  nlinarith [h.β_lt]

/-- `v(k) ≤ f(k) + A/(1 − β)`, `A = βf(k*) − k*`, for every `k`. -/
theorem linear_value_le (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) (x : Icc (0 : ℝ) xbar) :
    v x ≤ f x.1 + (β * f kstar.1 - kstar.1) / (1 - β) := by
  have : CompactSpace (Icc (0 : ℝ) xbar) := isCompact_iff_compactSpace.1 isCompact_Icc
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  set A := β * f kstar.1 - kstar.1
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  -- the largest excess `m = max (v − f − A/(1 − β))` satisfies `m ≤ βm`
  set D : Icc (0 : ℝ) xbar → ℝ := fun z => v z - f z.1 - A / (1 - β)
  have hD : Continuous D := (v.continuous.sub (continuous_growth_f h)).sub continuous_const
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hD.continuousOn
  have hmax : ∀ z, D z ≤ D x₀ := fun z => hx₀ (mem_univ z)
  obtain ⟨y, hy, hyv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v x₀
  rw [hv] at hyv
  have e1 := hmax y
  have e2 := hk y
  have hA : A / (1 - β) * (1 - β) = A := div_mul_cancel₀ A h1β.ne'
  have hm : D x₀ ≤ β * D x₀ := by
    simp only [D, growthF, id] at e1 hyv ⊢
    nlinarith [h.β_pos]
  have hm0 : D x₀ ≤ 0 := by nlinarith [h.β_lt]
  have := (hmax x).trans hm0
  simp only [D] at this
  linarith

/-- `v(k) = f(k) + A/(1 − β)` whenever `k* ≤ f(k)`: jumping to `k*` and staying there is
optimal. -/
theorem linear_value_eq (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) {x : Icc (0 : ℝ) xbar}
    (hx : kstar.1 ≤ f x.1) : v x = f x.1 + (β * f kstar.1 - kstar.1) / (1 - β) := by
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  refine le_antisymm (linear_value_le h hk hv x) ?_
  have hjump : ∀ z : Icc (0 : ℝ) xbar, kstar.1 ≤ f z.1 → f z.1 - kstar.1 + β * v kstar ≤ v z :=
    fun z hz => by
      obtain ⟨-, -, -, hmax⟩ :=
        exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) v z
      rw [hv] at hmax
      simpa [growthF] using hmax kstar hz
  have hks := hjump kstar (kstar_le_f h hk).2
  have hvk : (f kstar.1 - kstar.1) / (1 - β) ≤ v kstar := by
    rw [div_le_iff₀ h1β]; linarith
  have := hjump x hx
  have e : f x.1 + (β * f kstar.1 - kstar.1) / (1 - β) =
      f x.1 - kstar.1 + β * ((f kstar.1 - kstar.1) / (1 - β)) := by
    field_simp; ring
  rw [e]
  nlinarith [h.β_pos]

/-- **Exercise 5.3b.** For some `ε > 0`, `|k − k*| < ε` implies
`v(k) = f(k) − k* + β[f(k*) − k*]/(1 − β)`. -/
theorem ex_5_3b (h : GrowthHyp id f β xbar)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    ∃ ε > 0, ∀ k : Icc (0 : ℝ) xbar, |k.1 - kstar.1| < ε →
      v k = f k.1 - kstar.1 + β * (f kstar.1 - kstar.1) / (1 - β) := by
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  have hform : ∀ k : Icc (0 : ℝ) xbar, kstar.1 ≤ f k.1 →
      v k = f k.1 - kstar.1 + β * (f kstar.1 - kstar.1) / (1 - β) := fun k hk' => by
    rw [linear_value_eq h hk hv hk']
    field_simp; ring
  obtain ⟨hA, -⟩ := kstar_le_f h hk
  rcases eq_or_lt_of_le kstar.2.1 with h0 | hpos
  · -- `k* = 0`: every `k` can jump to `k*`
    exact ⟨1, one_pos, fun k _ => hform k (h0 ▸ growth_f_nonneg h k)⟩
  · -- `k* > 0`: `f(k*) > k*`, and `f` stays above `k*` near `k*`
    have hfk : kstar.1 < f kstar.1 := by nlinarith [h.β_lt, h.β_pos]
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1
      (h.f_cont kstar.1 (mem_Ici.2 kstar.2.1)) (f kstar.1 - kstar.1) (by linarith)
    refine ⟨δ, hδ, fun k hkd => hform k ?_⟩
    have := hball (mem_Ici.2 k.2.1) (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (f k.1 - f kstar.1)]

/-- The policy `g(k) = min{f(k), k*}`. -/
noncomputable def linearPolicy (h : GrowthHyp id f β xbar) (kstar x : Icc (0 : ℝ) xbar) :
    Icc (0 : ℝ) xbar :=
  ⟨min (f x.1) kstar.1, le_min (growth_f_nonneg h x) kstar.2.1, (min_le_right _ _).trans kstar.2.2⟩

/-- **Exercise 5.3c.** The policy `g(k) = min{f(k), k*}` is optimal: jump to `k*` when that is
feasible, and otherwise consume nothing and invest all output. -/
theorem ex_5_3c (h : GrowthHyp id f β xbar) (hf : ConcaveOn ℝ (Ici 0) f)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) (x : Icc (0 : ℝ) xbar) :
    linearPolicy h kstar x ∈ argmax (obj (growthF id f xbar) β v) (growthΓ f xbar) x := by
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  have hvc := growth_concave h (concaveOn_id (convex_Ici 0)) hf hv
  set A := β * f kstar.1 - kstar.1
  -- `ψ(y) = βv(y) − y` is maximized at `k*`
  have hψ : ∀ z : Icc (0 : ℝ) xbar, β * v z - z.1 ≤ β * v kstar - kstar.1 := fun z => by
    have e1 := linear_value_le h hk hv z
    have e2 := linear_value_eq h hk hv (kstar_le_f h hk).2
    have e3 := hk z
    have e : A / (1 - β) * (1 - β) = A := div_mul_cancel₀ A h1β.ne'
    rw [e2]
    nlinarith [h.β_pos]
  -- `ψ` is nondecreasing below `k*`
  have hmono : ∀ z w : Icc (0 : ℝ) xbar, z ≤ w → w ≤ kstar →
      β * v z - z.1 ≤ β * v w - w.1 := fun z w hzw hwk => by
    have hzw' : z.1 ≤ w.1 := hzw
    have hwk' : w.1 ≤ kstar.1 := hwk
    rcases eq_or_lt_of_le (hzw'.trans hwk') with he | hlt
    · have hz : z = w := Subtype.ext (le_antisymm hzw' (he ▸ hwk'))
      rw [hz]
    set θ := (kstar.1 - w.1) / (kstar.1 - z.1)
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
    have hθ1 : θ ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have hne : kstar.1 - z.1 ≠ 0 := by linarith
    have hcmb : cmb (convex_Icc 0 xbar) hθ0 hθ1 z kstar = w := by
      ext1
      simp only [cmb, smul_eq_mul, θ]
      field_simp
      ring
    have hc := hvc z kstar θ hθ0 hθ1
    rw [hcmb] at hc
    have hw : w.1 = θ * z.1 + (1 - θ) * kstar.1 := by
      have := congrArg Subtype.val hcmb
      simp only [cmb, smul_eq_mul] at this
      linarith
    have := hψ z
    have hθ1' : 0 ≤ 1 - θ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hθ1', h.β_pos]
  -- the policy maximizes `F(x, y) + βv(y) = f(x) + ψ(y)`
  have hge : ∀ z ∈ growthΓ f xbar x, obj (growthF id f xbar) β v (x, z) ≤
      obj (growthF id f xbar) β v (x, linearPolicy h kstar x) := fun z hz => by
    have hz' : z.1 ≤ f x.1 := hz
    simp only [obj, growthF, id, linearPolicy]
    rcases le_total (f x.1) kstar.1 with hfk | hfk
    · have hmin : min (f x.1) kstar.1 = f x.1 := min_eq_left hfk
      have := hmono z ⟨f x.1, growth_f_nonneg h x, hfk.trans kstar.2.2⟩ hz' hfk
      simp only [hmin]
      simp only at this
      linarith
    · have hmin : min (f x.1) kstar.1 = kstar.1 := min_eq_right hfk
      have hks : (⟨min (f x.1) kstar.1, le_min (growth_f_nonneg h x) kstar.2.1,
          (min_le_right _ _).trans kstar.2.2⟩ : Icc (0 : ℝ) xbar) = kstar :=
        Subtype.ext hmin
      rw [hks]
      have := hψ z
      linarith
  have hmem : linearPolicy h kstar x ∈ growthΓ f xbar x :=
    show min (f x.1) kstar.1 ≤ f x.1 from min_le_left _ _
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · exact le_maxValue (continuousOn_obj (growth_assumption44 h) v.continuous)
      ((growth_assumption43 h).compact x) hmem
  · obtain ⟨y, hy, hyv, -⟩ := exists_argmax (continuousOn_obj (growth_assumption44 h)
      v.continuous) ((growth_assumption43 h).compact x) ((growth_assumption43 h).nonempty x)
    rw [← hyv]
    exact hge y hy

/-- **Exercise 5.3a, what fails.** With `f` strictly concave the policy is unique, and wherever
`f(k) < k*` it is `g(k) = f(k)`: nothing is consumed, so the conclusion `0 < g(k) < f(k)` of
Exercise 5.1d fails (there is no Inada condition). If `k* > 0` such `k > 0` exist. -/
theorem ex_5_3a_corner [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp id f β xbar)
    (hf : StrictConcaveOn ℝ (Ici 0) f)
    (hk : ∀ k : Icc (0 : ℝ) xbar, β * f k.1 - k.1 ≤ β * f kstar.1 - kstar.1)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    (∀ x : Icc (0 : ℝ) xbar, f x.1 < kstar.1 →
      (argmaxFn (growthΓ f xbar) (obj (growthF id f xbar) β v) x).1 = f x.1) ∧
    (0 < kstar.1 → ∃ x : Icc (0 : ℝ) xbar, 0 < x.1 ∧ f x.1 < kstar.1) := by
  obtain ⟨-, hUA, -⟩ := ex_5_3a_strict h hf hv
  refine ⟨fun x hx => ?_, fun hpos => ?_⟩
  · have hg := hUA.argmax_eq x
    have hmem := ex_5_3c h hf.concaveOn hk hv x
    rw [hg] at hmem
    rw [← hmem]
    exact min_eq_left hx.le
  · obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1
      (h.f_cont 0 (mem_Ici.2 le_rfl)) kstar.1 hpos
    set x := min (δ / 2) xbar
    have hx0 : 0 < x := lt_min (by linarith) h.xbar_pos
    refine ⟨⟨x, hx0.le, min_le_right _ _⟩, hx0, ?_⟩
    have := hball (mem_Ici.2 hx0.le) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
      exact (min_le_left _ _).trans_lt (by linarith))
    rw [Real.dist_eq, h.f_zero, sub_zero] at this
    exact (le_abs_self _).trans_lt this

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Growth with technical progress

SLP §5.4, pp. 105–107: effective labour grows by the factor `1 + λ > 1`, `F` has constant returns,
capital depreciates at rate `δ`, and `U(C) = C^γ/γ`. Dividing every variable by `(1 + λ)ᵗ` gives
a problem in `k_t = K_t/(1 + λ)ᵗ`.

* `renorm_budget`, `renorm_capital`: with `F` homogeneous of degree one, the constraints become
  `c_t + i_t ≤ f(k_t)`, `f(k) = F(k, 1)`, and `k_{t+1} = [(1 − δ)k_t + i_t]/(1 + λ)`.
* `renorm_power_utility`: `βᵗ C_t^γ/γ = [β(1 + λ)^γ]ᵗ c_t^γ/γ`; `renorm_log_utility`: for
  `U = ln` the objective changes only by a constant.
* `renorm_consumption`: eliminating `i_t`, consumption is `(1 + λ)[f̃(k_t) − k_{t+1}]` with
  `f̃(k) = [f(k) + (1 − δ)k]/(1 + λ)`. **Exercise 5.4**: the functional equation is
  `v(k) = max_{0 ≤ y ≤ f̃(k)} {Ũ(f̃(k) − y) + β̃v(y)}`, `Ũ(c) = U((1 + λ)c)`, `β̃ = β(1 + λ)^γ`.
* `ex_5_4`: if `β̃ < 1` (and `f̃` satisfies (T2)), then `(Ũ, f̃, β̃)` satisfies the hypotheses of
  Section 5.1, and concavity carries over (`renormU_strictConcave`, `renormF_concave`); so the
  analysis of Section 5.1 goes through (`ex_5_4_analysis`).
* `power_utility`: `c^γ/γ` with `0 < γ < 1` satisfies (U2)–(U4).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {U f : ℝ → ℝ} {β γ δ lam xbar : ℝ}

/-- `Ũ(c) = U((1 + λ)c)`. -/
def renormU (U : ℝ → ℝ) (lam : ℝ) (c : ℝ) : ℝ := U ((1 + lam) * c)

/-- `f̃(k) = [f(k) + (1 − δ)k]/(1 + λ)`. -/
noncomputable def renormF (f : ℝ → ℝ) (δ lam : ℝ) (k : ℝ) : ℝ := (f k + (1 - δ) * k) / (1 + lam)

/-- With `F` homogeneous of degree one and `L_t = (1 + λ)ᵗ`, `C_t + I_t ≤ F(K_t, L_t)` iff
`c_t + i_t ≤ f(k_t)` for the renormalized variables. -/
theorem renorm_budget (F : ℝ → ℝ → ℝ) (hF : ∀ a > 0, ∀ K L, F (a * K) (a * L) = a * F K L)
    (hlam : 0 < 1 + lam) (t : ℕ) (C I K : ℝ) :
    C + I ≤ F K ((1 + lam) ^ t) ↔
      C / (1 + lam) ^ t + I / (1 + lam) ^ t ≤ F (K / (1 + lam) ^ t) 1 := by
  have hp : 0 < (1 + lam) ^ t := pow_pos hlam t
  have e : F K ((1 + lam) ^ t) = (1 + lam) ^ t * F (K / (1 + lam) ^ t) 1 := by
    rw [← hF _ hp]
    congr 1 <;> field_simp
  rw [e, ← add_div, div_le_iff₀ hp, mul_comm]

/-- `K_{t+1} = (1 − δ)K_t + I_t` iff `k_{t+1} = [(1 − δ)k_t + i_t]/(1 + λ)`. -/
theorem renorm_capital (hlam : 0 < 1 + lam) (t : ℕ) (K K' I : ℝ) :
    K' = (1 - δ) * K + I ↔
      K' / (1 + lam) ^ (t + 1) =
        ((1 - δ) * (K / (1 + lam) ^ t) + I / (1 + lam) ^ t) / (1 + lam) := by
  have hp : 0 < (1 + lam) ^ t := pow_pos hlam t
  have hne : (1 + lam) ^ t ≠ 0 := hp.ne'
  have hne' : (1 + lam) ≠ 0 := hlam.ne'
  rw [pow_succ]
  constructor
  · intro h; rw [h]; field_simp
  · intro h
    field_simp at h
    linarith

/-- `βᵗ C^γ/γ = [β(1 + λ)^γ]ᵗ c^γ/γ` for `C = (1 + λ)ᵗc`, `c ≥ 0`. -/
theorem renorm_power_utility (hlam : 0 < 1 + lam) {c : ℝ} (hc : 0 ≤ c) (t : ℕ) :
    β ^ t * (((1 + lam) ^ t * c) ^ γ / γ) = (β * (1 + lam) ^ γ) ^ t * (c ^ γ / γ) := by
  have e : ((1 + lam) ^ t) ^ γ = ((1 + lam) ^ γ) ^ t := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le,
      ← Real.rpow_mul hlam.le]
    congr 1
    ring
  rw [Real.mul_rpow (pow_nonneg hlam.le t) hc, e, mul_pow]
  ring

/-- For `U = ln`, `βᵗ ln C_t = βᵗ t ln(1 + λ) + βᵗ ln c_t`: the objective changes by a constant
and `β̃ = β`. -/
theorem renorm_log_utility (hlam : 0 < 1 + lam) {c : ℝ} (hc : 0 < c) (t : ℕ) :
    β ^ t * Real.log ((1 + lam) ^ t * c) =
      β ^ t * (t * Real.log (1 + lam)) + β ^ t * Real.log c := by
  rw [Real.log_mul (pow_pos hlam t).ne' hc.ne', Real.log_pow]
  ring

/-- Eliminating investment, consumption is `f(k) + (1 − δ)k − (1 + λ)y = (1 + λ)[f̃(k) − y]`,
so the return is `U(c) = Ũ(f̃(k) − y)`. -/
theorem renorm_consumption (hlam : 0 < 1 + lam) (k y : ℝ) :
    U (f k + (1 - δ) * k - (1 + lam) * y) = renormU U lam (renormF f δ lam k - y) := by
  simp only [renormU, renormF]
  congr 1
  field_simp

/-- `Ũ` inherits continuity and strict monotonicity on `[0, ∞)`. -/
theorem renormU_hyp (hlam : 0 < 1 + lam) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) :
    ContinuousOn (renormU U lam) (Ici 0) ∧ StrictMonoOn (renormU U lam) (Ici 0) := by
  have hmaps : MapsTo (fun c => (1 + lam) * c) (Ici 0) (Ici 0) := fun c hc =>
    mem_Ici.2 (mul_nonneg hlam.le hc)
  refine ⟨hUc.comp (continuous_const.mul continuous_id).continuousOn hmaps, ?_⟩
  intro a ha b hb hab
  exact hUm (hmaps ha) (hmaps hb) (mul_lt_mul_of_pos_left hab hlam)

/-- `Ũ` inherits strict concavity. -/
theorem renormU_strictConcave (hlam : 0 < 1 + lam) (hU : StrictConcaveOn ℝ (Ici 0) U) :
    StrictConcaveOn ℝ (Ici 0) (renormU U lam) := by
  refine ⟨convex_Ici 0, fun a ha b hb hab s t hs ht hst => ?_⟩
  have ha' : (1 + lam) * a ∈ Ici (0 : ℝ) := mem_Ici.2 (mul_nonneg hlam.le ha)
  have hb' : (1 + lam) * b ∈ Ici (0 : ℝ) := mem_Ici.2 (mul_nonneg hlam.le hb)
  have hne : (1 + lam) * a ≠ (1 + lam) * b := fun he =>
    hab (mul_left_cancel₀ hlam.ne' he)
  have := hU.2 ha' hb' hne hs ht hst
  simp only [smul_eq_mul, renormU] at this ⊢
  convert this using 2
  ring

/-- `f̃` inherits (T1), `f̃(0) = 0` and (T3) when `0 ≤ δ ≤ 1`. -/
theorem renormF_hyp (hlam : 0 < 1 + lam) (hδ : δ ≤ 1) (hfc : ContinuousOn f (Ici 0))
    (hf0 : f 0 = 0) (hfm : StrictMonoOn f (Ici 0)) :
    ContinuousOn (renormF f δ lam) (Ici 0) ∧ renormF f δ lam 0 = 0 ∧
      StrictMonoOn (renormF f δ lam) (Ici 0) := by
  refine ⟨(hfc.add (continuous_const.mul continuous_id).continuousOn).div_const _,
    by simp [renormF, hf0], fun a ha b hb hab => ?_⟩
  have h1 := hfm ha hb hab
  have h2 : (1 - δ) * a ≤ (1 - δ) * b := mul_le_mul_of_nonneg_left hab.le (by linarith)
  exact div_lt_div_of_pos_right (by linarith) hlam

/-- `f̃` inherits (T4). -/
theorem renormF_concave (hlam : 0 < 1 + lam) (hf : ConcaveOn ℝ (Ici 0) f) :
    ConcaveOn ℝ (Ici 0) (renormF f δ lam) := by
  have hlin : ConcaveOn ℝ (Ici 0) fun k : ℝ => (1 - δ) * k :=
    (LinearMap.mulLeft ℝ (1 - δ)).concaveOn (convex_Ici 0)
  have := (hf.add hlin).smul (inv_nonneg.2 hlam.le)
  refine this.congr fun k _ => ?_
  simp only [renormF, Pi.add_apply, smul_eq_mul]
  ring

/-- **Exercise 5.4.** If `β̃ = β(1 + λ)^γ` lies in `(0, 1)` and `f̃` satisfies (T2) on `[0, x̄]`,
the renormalized problem satisfies the hypotheses of Section 5.1. -/
theorem ex_5_4 (hlam : 0 < lam) (hδ : δ ≤ 1) (hβ0 : 0 < β * (1 + lam) ^ γ)
    (hβ1 : β * (1 + lam) ^ γ < 1) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) (hfc : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hfm : StrictMonoOn f (Ici 0)) (hx : 0 < xbar)
    (hT2 : ∀ x ∈ Icc 0 xbar, x ≤ renormF f δ lam x ∧ renormF f δ lam x ≤ xbar) :
    GrowthHyp (renormU U lam) (renormF f δ lam) (β * (1 + lam) ^ γ) xbar := by
  have hl : 0 < 1 + lam := by linarith
  obtain ⟨h1, h2⟩ := renormU_hyp hl hUc hUm
  obtain ⟨h3, h4, h5⟩ := renormF_hyp hl hδ hfc hf0 hfm
  exact ⟨hβ0, hβ1, h1, h2, h3, h4, hx, hT2, h5⟩

/-- **Exercise 5.4.** The analysis of Section 5.1 goes through: under (U1)–(U4) and
(T1)–(T4) for the original model, the renormalized value function is the supremum function, is
strictly increasing and strictly concave, and the policy is a continuous function. -/
theorem ex_5_4_analysis [Nonempty (Icc (0 : ℝ) xbar)] (hlam : 0 < lam) (hδ : δ ≤ 1)
    (hβ0 : 0 < β * (1 + lam) ^ γ) (hβ1 : β * (1 + lam) ^ γ < 1) (hUc : ContinuousOn U (Ici 0))
    (hUm : StrictMonoOn U (Ici 0)) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hfc : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0) (hfm : StrictMonoOn f (Ici 0))
    (hf : ConcaveOn ℝ (Ici 0) f) (hx : 0 < xbar)
    (hT2 : ∀ x ∈ Icc 0 xbar, x ≤ renormF f δ lam x ∧ renormF f δ lam x ≤ xbar)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 (ex_5_4 hlam hδ hβ0 hβ1 hUc hUm hfc hf0 hfm hx hT2))
      (growth_assumption44 (ex_5_4 hlam hδ hβ0 hβ1 hUc hUm hfc hf0 hfm hx hT2)) v = v) :
    (fun x => (v x : EReal)) = vstar (growthΓ (renormF f δ lam) xbar)
      (curryF (growthF (renormU U lam) (renormF f δ lam) xbar)) (β * (1 + lam) ^ γ) ∧
      StrictMono v ∧ IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      Continuous (argmaxFn (growthΓ (renormF f δ lam) xbar)
        (obj (growthF (renormU U lam) (renormF f δ lam) xbar) (β * (1 + lam) ^ γ) v)) := by
  have hl : 0 < 1 + lam := by linarith
  set h := ex_5_4 hlam hδ hβ0 hβ1 hUc hUm hfc hf0 hfm hx hT2
  obtain ⟨u, -, huniq, hvs, hmono, -⟩ := ex_5_1ab h
  have hvu := huniq v hv
  subst hvu
  obtain ⟨c1, -, c3⟩ := ex_5_1c_weak h (renormU_strictConcave hl hU) (renormF_concave hl hf) hv
  exact ⟨hvs, hmono, c1, c3⟩

/-- `c^γ/γ` with `0 < γ < 1` satisfies (U2)–(U4) on `[0, ∞)`. -/
theorem power_utility (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ContinuousOn (fun c : ℝ => c ^ γ / γ) (Ici 0) ∧
      StrictMonoOn (fun c : ℝ => c ^ γ / γ) (Ici 0) ∧
      StrictConcaveOn ℝ (Ici 0) (fun c : ℝ => c ^ γ / γ) := by
  refine ⟨fun c _ =>
    ((Real.continuousAt_rpow_const c γ (Or.inr hγ0.le)).div_const γ).continuousWithinAt,
    fun a ha b hb hab => div_lt_div_of_pos_right (Real.rpow_lt_rpow ha hab hγ0) hγ0, ?_⟩
  refine ⟨convex_Ici 0, fun a ha b hb hab s t hs ht hst => ?_⟩
  have h := (Real.strictConcaveOn_rpow hγ0 hγ1).2 ha hb hab hs ht hst
  simp only [smul_eq_mul] at h ⊢
  calc s * (a ^ γ / γ) + t * (b ^ γ / γ) = (s * a ^ γ + t * b ^ γ) / γ := by ring
    _ < (s * a + t * b) ^ γ / γ := div_lt_div_of_pos_right h hγ0

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A tree-cutting problem

SLP §5.5, p. 107: a tree of size `k_t` grows to `k_{t+1} = h(k_t)`; wood sells at `p = 1`, and
`β = 1/(1 + r)`. Exercise 5.5 is open-ended ("under what assumptions about `h` is there a simple
rule"); the answers here are the monotone (one-step look-ahead) rules.

Both parts are optimal stopping problems along `k_t = hᵗ(k₀)`. Cutting at `T` when the land
left behind is worth `L` pays `P(T) = βᵀ(k_T + L)`, and
`P(T + 1) − P(T) = βᵀ[βh(k_T) − k_T − (1 − β)L]`. Let `S_L = {k : βh(k) − k ≤ (1 − β)L}`.

* `first_entry_optimal`: if the path stays in `S_L` once it has entered (an `h`-invariant
  `S' ⊆ S_L`), the first entry time maximizes `P`. `never_entry_strictMono`: if the path never
  enters `S_L`, `P` increases forever and no cutting time is optimal.
* **Exercise 5.5a** (no replanting, `L = 0`): `ex_5_5a`: cut at the first `t` with
  `h(k_t)/k_t ≤ 1 + r`. This is optimal when trees grow (`h(k) ≥ k`) and the growth factor
  `h(k)/k` does not rise with size (`ratio_invariant`). `treeValue` solves the functional
  equation `v(k) = max{k, βv(h(k))}` (`treeValue_fe`), and is the largest payoff
  (`le_treeValue`).
* **Exercise 5.5b** (replanting at cost `c` with a sapling of size `s`): the stationary rotation
  of length `T` has land value `L(T) = (βᵀk_T − c)/(1 − βᵀ)` (Faustmann; `faustmann_identity`);
  the best rotation value `L*` solves `L = max_{T ≥ 1} βᵀ(k_T + L) − c` (`faustmann_fe`); and
  `ex_5_5b`: cut when `βh(k) − k ≤ (1 − β)L*` (the one-period gain from waiting no longer covers
  the rent on the land). This rule gives an optimal rotation when the gain `βh(k) − k` falls
  with size past some `k₁` (`antitone_invariant`).
-/

open Set

namespace StokeyLucasPrescott.DeterministicApplications

variable {h : ℝ → ℝ} {β L : ℝ}

/-- The payoff `βᵀ(k_T + L)` from cutting at `T`, `k_T = hᵀ(k₀)`. -/
noncomputable def cutPayoff (h : ℝ → ℝ) (β L k₀ : ℝ) (T : ℕ) : ℝ := β ^ T * (h^[T] k₀ + L)

/-- `S_L = {k : βh(k) − k ≤ (1 − β)L}`: waiting one more period does not pay. -/
def stopSet (h : ℝ → ℝ) (β L : ℝ) : Set ℝ := {k | β * h k - k ≤ (1 - β) * L}

theorem cutPayoff_succ (k₀ : ℝ) (T : ℕ) :
    cutPayoff h β L k₀ (T + 1) - cutPayoff h β L k₀ T =
      β ^ T * (β * h (h^[T] k₀) - h^[T] k₀ - (1 - β) * L) := by
  simp only [cutPayoff, Function.iterate_succ_apply', pow_succ]
  ring

/-- **The monotone rule.** If the path enters an `h`-invariant subset `S'` of `S_L` at `T*` and
lies outside `S_L` before, cutting at `T*` is optimal. -/
theorem first_entry_optimal (hβ : 0 < β) {S' : Set ℝ} (hS' : S' ⊆ stopSet h β L)
    (hinv : MapsTo h S' S') {k₀ : ℝ} {Tstar : ℕ} (hin : h^[Tstar] k₀ ∈ S')
    (hbefore : ∀ t < Tstar, h^[t] k₀ ∉ stopSet h β L) (T : ℕ) :
    cutPayoff h β L k₀ T ≤ cutPayoff h β L k₀ Tstar := by
  -- the payoff rises before `T*`
  have hup : ∀ t < Tstar, cutPayoff h β L k₀ t < cutPayoff h β L k₀ (t + 1) := fun t ht => by
    have := cutPayoff_succ (h := h) (β := β) (L := L) k₀ t
    have hns := hbefore t ht
    simp only [stopSet, mem_ofPred_eq, not_le] at hns
    have : 0 < β ^ t * (β * h (h^[t] k₀) - h^[t] k₀ - (1 - β) * L) :=
      mul_pos (pow_pos hβ t) (by linarith)
    linarith
  -- and falls after it
  have hstay : ∀ n, h^[Tstar + n] k₀ ∈ S' := fun n => by
    induction n with
    | zero => simpa using hin
    | succ n ih =>
      rw [← add_assoc, Function.iterate_succ_apply']
      exact hinv ih
  have hdown : ∀ n, cutPayoff h β L k₀ (Tstar + n + 1) ≤ cutPayoff h β L k₀ (Tstar + n) :=
    fun n => by
      have := cutPayoff_succ (h := h) (β := β) (L := L) k₀ (Tstar + n)
      have hs : β * h (h^[Tstar + n] k₀) - h^[Tstar + n] k₀ ≤ (1 - β) * L := hS' (hstay n)
      have : β ^ (Tstar + n) * (β * h (h^[Tstar + n] k₀) - h^[Tstar + n] k₀ - (1 - β) * L)
          ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le _) (by linarith)
      linarith
  have hleft : ∀ d : ℕ, ∀ T, T + d = Tstar → cutPayoff h β L k₀ T ≤ cutPayoff h β L k₀ Tstar := by
    intro d
    induction d with
    | zero =>
      intro T hT
      obtain rfl : T = Tstar := by omega
      exact le_rfl
    | succ d ih =>
      intro T hT
      exact (hup T (by omega)).le.trans (ih (T + 1) (by omega))
  have hright : ∀ n, cutPayoff h β L k₀ (Tstar + n) ≤ cutPayoff h β L k₀ Tstar := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (hdown n).trans ih
  rcases le_total T Tstar with hT | hT
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hT
    exact hleft d T hd.symm
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hright n

/-- If the path never enters `S_L`, the payoff increases forever: no cutting time is optimal. -/
theorem never_entry_strictMono (hβ : 0 < β) {k₀ : ℝ} (hnever : ∀ t, h^[t] k₀ ∉ stopSet h β L) :
    StrictMono (cutPayoff h β L k₀) := by
  refine strictMono_nat_of_lt_succ fun t => ?_
  have := cutPayoff_succ (h := h) (β := β) (L := L) k₀ t
  have hns := hnever t
  simp only [stopSet, mem_ofPred_eq, not_le] at hns
  have : 0 < β ^ t * (β * h (h^[t] k₀) - h^[t] k₀ - (1 - β) * L) :=
    mul_pos (pow_pos hβ t) (by linarith)
  linarith

/-! ### Exercise 5.5a: no replanting -/

/-- If trees grow and the growth factor `h(k)/k` does not rise with size, then the positive
part of `S_0 = {k : βh(k) ≤ k}` is `h`-invariant. -/
theorem ratio_invariant (hβ : 0 < β) (hgrow : ∀ k, 0 < k → k ≤ h k)
    (hratio : ∀ a b, 0 < a → a ≤ b → h b * a ≤ h a * b) :
    MapsTo h (stopSet h β 0 ∩ Ioi 0) (stopSet h β 0 ∩ Ioi 0) := by
  rintro k ⟨hk, hk0⟩
  have hk0' : 0 < k := hk0
  have hkh := hgrow k hk0'
  have hb : 0 < h k := hk0'.trans_le hkh
  refine ⟨?_, hb⟩
  simp only [stopSet, mem_ofPred_eq, mul_zero] at hk ⊢
  have h1 := hratio k (h k) hk0' hkh
  have h2 : β * h (h k) * k ≤ β * h k * h k := by
    have := mul_le_mul_of_nonneg_left h1 hβ.le; linarith
  have h3 : β * h k * h k ≤ k * h k := mul_le_mul_of_nonneg_right (by linarith) hb.le
  nlinarith

/-- **Exercise 5.5a.** Under `ratio_invariant`'s assumptions the rule "cut at the first `t` with
`βh(k_t) ≤ k_t`, i.e. `h(k_t)/k_t ≤ 1 + r`" is optimal. -/
theorem ex_5_5a (hβ : 0 < β) (hgrow : ∀ k, 0 < k → k ≤ h k)
    (hratio : ∀ a b, 0 < a → a ≤ b → h b * a ≤ h a * b) {k₀ : ℝ} (hk₀ : 0 < k₀) {Tstar : ℕ}
    (hin : β * h (h^[Tstar] k₀) ≤ h^[Tstar] k₀)
    (hbefore : ∀ t < Tstar, h^[t] k₀ < β * h (h^[t] k₀)) (T : ℕ) :
    β ^ T * h^[T] k₀ ≤ β ^ Tstar * h^[Tstar] k₀ := by
  have hpos : ∀ t, 0 < h^[t] k₀ := fun t => by
    induction t with
    | zero => simpa using hk₀
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans_le (hgrow _ ih)
  have := first_entry_optimal (L := 0) hβ inter_subset_left (ratio_invariant hβ hgrow hratio)
    ⟨show β * h (h^[Tstar] k₀) - h^[Tstar] k₀ ≤ (1 - β) * 0 by linarith, hpos Tstar⟩
    (fun t ht hs => by
      have := hbefore t ht
      simp only [stopSet, mem_ofPred_eq, mul_zero] at hs
      linarith) T
  simpa [cutPayoff] using this

/-- When every path reaches `S_0`, cut at the first entry: `v(k) = βᵀ*k_{T*}`. -/
noncomputable def treeValue (h : ℝ → ℝ) (β : ℝ)
    (hreach : ∀ k, ∃ t, h^[t] k ∈ stopSet h β 0) (k : ℝ) : ℝ :=
  by classical exact cutPayoff h β 0 k (Nat.find (hreach k))

/-- **Exercise 5.5a.** `treeValue` solves `v(k) = max{k, βv(h(k))}` when `S_0` is invariant. -/
theorem treeValue_fe (hβ : 0 < β) (hinv : MapsTo h (stopSet h β 0) (stopSet h β 0))
    (hreach : ∀ k, ∃ t, h^[t] k ∈ stopSet h β 0) (k : ℝ) :
    treeValue h β hreach k = max k (β * treeValue h β hreach (h k)) := by
  classical
  simp only [treeValue]
  by_cases hk : k ∈ stopSet h β 0
  · -- cut now: `T*(k) = 0`, and `T*(h k) = 0` too
    have h0 : Nat.find (hreach k) = 0 := (Nat.find_eq_zero _).2 (by simpa using hk)
    have h1 : Nat.find (hreach (h k)) = 0 := (Nat.find_eq_zero _).2 (by simpa using hinv hk)
    rw [h0, h1]
    simp only [stopSet, mem_ofPred_eq, mul_zero] at hk
    simp only [cutPayoff, pow_zero, Function.iterate_zero, id_eq, add_zero, one_mul]
    rw [max_eq_left (by linarith)]
  · -- wait: `T*(k) = T*(h k) + 1`
    have hpos : Nat.find (hreach k) ≠ 0 := fun he => hk (by
      have := Nat.find_spec (hreach k); rwa [he] at this)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hfind : Nat.find (hreach (h k)) = n := by
      rw [Nat.find_eq_iff]
      constructor
      · have := Nat.find_spec (hreach k)
        rwa [hn, Function.iterate_succ_apply] at this
      · intro m hm hmem
        have := Nat.find_min (hreach k) (show m + 1 < Nat.find (hreach k) by omega)
        exact this (by rwa [Function.iterate_succ_apply])
    rw [hn, hfind]
    have hval : cutPayoff h β 0 k (n + 1) = β * cutPayoff h β 0 (h k) n := by
      simp only [cutPayoff, Function.iterate_succ_apply, pow_succ]
      ring
    rw [hval]
    simp only [stopSet, mem_ofPred_eq, mul_zero, not_le] at hk
    -- waiting beats cutting: `βv(h k) ≥ βh(k) > k`
    have hge : cutPayoff h β 0 (h k) 0 ≤ cutPayoff h β 0 (h k) n :=
      first_entry_optimal hβ subset_rfl hinv (Nat.find_spec (hreach (h k)) |> fun h' => by
        rwa [hfind] at h') (fun t ht => by
          have := Nat.find_min (hreach (h k)) (show t < Nat.find (hreach (h k)) by omega)
          exact this) 0
    simp only [cutPayoff, pow_zero, Function.iterate_zero, id_eq, add_zero, one_mul] at hge
    rw [max_eq_right]
    have := mul_le_mul_of_nonneg_left hge hβ.le
    simp only [cutPayoff, add_zero] at this ⊢
    linarith

/-- **Exercise 5.5a.** `treeValue` is the largest payoff from any cutting time. -/
theorem le_treeValue (hβ : 0 < β) (hinv : MapsTo h (stopSet h β 0) (stopSet h β 0))
    (hreach : ∀ k, ∃ t, h^[t] k ∈ stopSet h β 0) (k : ℝ) (T : ℕ) :
    β ^ T * h^[T] k ≤ treeValue h β hreach k := by
  classical
  have := first_entry_optimal hβ subset_rfl hinv (Nat.find_spec (hreach k))
    (fun t ht => Nat.find_min (hreach k) ht) T
  simpa [cutPayoff, treeValue] using this

/-! ### Exercise 5.5b: replanting -/

/-- The land value of the stationary rotation of length `T` from a sapling of size `s`:
`L(T) = (βᵀk_T − c)/(1 − βᵀ)` (Faustmann). -/
noncomputable def rotationValue (h : ℝ → ℝ) (β c s : ℝ) (T : ℕ) : ℝ :=
  (β ^ T * h^[T] s - c) / (1 - β ^ T)

/-- `L(T)` is the value of planting, cutting at `T` and starting again:
`L(T) = βᵀ(k_T + L(T)) − c`. -/
theorem faustmann_identity (hβ0 : 0 < β) (hβ1 : β < 1) (c s : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    rotationValue h β c s T = cutPayoff h β (rotationValue h β c s T) s T - c := by
  have hlt : β ^ T < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  have hne : 1 - β ^ T ≠ 0 := by linarith
  simp only [rotationValue, cutPayoff]
  field_simp
  ring

/-- **Exercise 5.5b.** If `T*` is a best rotation, `L* = L(T*)` solves the land-value equation
`L = max_{T ≥ 1} βᵀ(k_T + L) − c`. -/
theorem faustmann_fe (hβ0 : 0 < β) (hβ1 : β < 1) (c s : ℝ) {Tstar : ℕ} (hTs : 1 ≤ Tstar)
    (hbest : ∀ T, 1 ≤ T → rotationValue h β c s T ≤ rotationValue h β c s Tstar) :
    (∀ T, 1 ≤ T → cutPayoff h β (rotationValue h β c s Tstar) s T - c ≤
      rotationValue h β c s Tstar) ∧
    cutPayoff h β (rotationValue h β c s Tstar) s Tstar - c = rotationValue h β c s Tstar := by
  refine ⟨fun T hT => ?_, (faustmann_identity hβ0 hβ1 c s hTs).symm⟩
  have hlt : β ^ T < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  have hb := hbest T hT
  simp only [rotationValue] at hb
  rw [div_le_iff₀ (by linarith)] at hb
  have hb' : β ^ T * h^[T] s - c ≤ rotationValue h β c s Tstar * (1 - β ^ T) := hb
  simp only [cutPayoff]
  linarith

/-- If trees grow and the gain from waiting `βh(k) − k` falls with size past `k₁`, then the
part of `S_L` beyond `k₁` is `h`-invariant. -/
theorem antitone_invariant {k₁ : ℝ} (hgrow : ∀ k, k ≤ h k)
    (hanti : AntitoneOn (fun k => β * h k - k) (Ici k₁)) :
    MapsTo h (stopSet h β L ∩ Ici k₁) (stopSet h β L ∩ Ici k₁) := by
  rintro k ⟨hk, hk₁⟩
  have hk₁' : h k ∈ Ici k₁ := mem_Ici.2 ((mem_Ici.1 hk₁).trans (hgrow k))
  refine ⟨?_, hk₁'⟩
  exact (hanti hk₁ hk₁' (hgrow k)).trans hk

/-- **Exercise 5.5b.** Let `L*` be the best rotation value. Starting from a sapling `s`, cut at
the first `T_e ≥ 1` with `βh(k_T) − k_T ≤ (1 − β)L*`. If the path stays in that set beyond
`k₁`, the rotation of length `T_e` is optimal: `L(T_e) = L*`. -/
theorem ex_5_5b (hβ0 : 0 < β) (hβ1 : β < 1) (c s : ℝ) {k₁ : ℝ} (hgrow : ∀ k, k ≤ h k)
    {Tstar : ℕ} (hTs : 1 ≤ Tstar)
    (hbest : ∀ T, 1 ≤ T → rotationValue h β c s T ≤ rotationValue h β c s Tstar)
    (hanti : AntitoneOn (fun k => β * h k - k) (Ici k₁)) {Te : ℕ} (hTe : 1 ≤ Te)
    (hin : h^[Te] s ∈ stopSet h β (rotationValue h β c s Tstar) ∩ Ici k₁)
    (hbefore : ∀ t < Te, h^[t] s ∉ stopSet h β (rotationValue h β c s Tstar)) :
    rotationValue h β c s Te = rotationValue h β c s Tstar := by
  set Ls := rotationValue h β c s Tstar
  obtain ⟨hfe, hfeq⟩ := faustmann_fe hβ0 hβ1 c s hTs hbest
  have hopt := first_entry_optimal hβ0 inter_subset_left (antitone_invariant hgrow hanti) hin
    hbefore Tstar
  have hle := hfe Te hTe
  -- so `βᵀᵉ(k_{Tₑ} + L*) − c = L*`, and `L*` solves the rotation identity at `Tₑ`
  have heq : cutPayoff h β Ls s Te - c = Ls := by linarith
  have hlt : β ^ Te < 1 := pow_lt_one₀ hβ0.le hβ1 (by omega)
  simp only [cutPayoff] at heq
  simp only [rotationValue]
  rw [div_eq_iff (by linarith)]
  linarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Learning by doing

SLP §5.6, pp. 107–109: unit cost `γ(Q)` falls with cumulative experience `Q`; output in a period
is `q = y − Q`, where `y` is next period's experience. Exercises 5.6a and 5.6b both have the
return `F(Q, y) = R(y − Q) − (y − Q)γ(Q)`: revenue `R(q) = qφ(q)` for the monopolist and
consumer surplus `R(q) = S(q)` for the planner. This module treats a general `R`.

The state space is `X = [0, ∞)` and, as in the manual, output is bounded by `q̄`:
`Γ(Q) = [Q, Q + q̄]`. (The manual's reason, that output above `q̄` never pays, ignores the
learning gain from it; the bound is an assumption of the model here.)

* `lbd_assumption43`, `lbd_assumption44`, `lbd_exists`: Theorem 4.6 applies, so there is a
  unique bounded continuous solution `v` of the functional equation, and `v = v*`.
* `lbd_not_a46`, `lbd_not_a47`: Assumptions 4.6 and 4.7 fail, so Theorems 4.7 and 4.8 do not
  apply. (`F(Q, Q) = 0` for every `Q`, so `F` is never strictly concave.)
* `lbd_argmax_pos`: with a nondecreasing continuation value, producing nothing is never optimal.
* `lbd_strictMono`: `v` is strictly increasing (another argument: `T` maps nondecreasing
  functions into strictly increasing ones, then Corollary 1 to Theorem 3.2).
* `lbd_policy_exceeds`: any optimal output exceeds the output `q̃` that maximizes the current
  return. The manual argues from a first-order condition that needs `v` differentiable, which
  Theorem 4.11 cannot supply here (concavity fails). The proof here uses only the convexity of
  `γ`: one more unit of output lowers future costs at a rate bounded below, while it costs
  nothing to first order at `q̃`.
* `unique_interior_max`: a return with strictly decreasing derivative, positive at `0` and
  negative at `q̄`, has a unique maximizer in `(0, q̄)`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- The state space `X = [0, ∞)` of cumulative experience. -/
abbrev ExpStock := ↥(Ici (0 : ℝ))

variable {R γ : ℝ → ℝ} {qbar β : ℝ}

/-- The hypotheses used for the learning-by-doing problem with return `R(q) − qγ(Q)`. -/
structure LBDHyp (R γ : ℝ → ℝ) (qbar β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  qbar_pos : 0 < qbar
  R_cont : ContinuousOn R (Icc 0 qbar)
  R_zero : R 0 = 0
  γ_cont : ContinuousOn γ (Ici 0)
  γ_anti : StrictAntiOn γ (Ici 0)
  γ_nonneg : ∀ Q, 0 ≤ Q → 0 ≤ γ Q
  /-- Some output `q₀ ≤ q̄` earns a positive return even at the highest cost `γ(0)`. -/
  profit : ∃ q₀ ∈ Ioc 0 qbar, q₀ * γ 0 < R q₀

/-- `Γ(Q) = [Q, Q + q̄]`. -/
def lbdΓ (qbar : ℝ) (Q : ExpStock) : Set ExpStock := {y | Q.1 ≤ y.1 ∧ y.1 ≤ Q.1 + qbar}

/-- `F(Q, y) = R(y − Q) − (y − Q)γ(Q)`. -/
def lbdF (R γ : ℝ → ℝ) (p : ExpStock × ExpStock) : ℝ :=
  R (p.2.1 - p.1.1) - (p.2.1 - p.1.1) * γ p.1.1

theorem lbd_γ_le (h : LBDHyp R γ qbar β) (Q : ExpStock) : γ Q.1 ≤ γ 0 :=
  h.γ_anti.antitoneOn (mem_Ici.2 le_rfl) Q.2 Q.2

/-- Assumption 4.3 holds for `Γ(Q) = [Q, Q + q̄]`. -/
theorem lbd_assumption43 (h : LBDHyp R γ qbar β) : Assumption43 (lbdΓ qbar) := by
  have hemb := (isClosed_Ici (a := (0 : ℝ))).isClosedEmbedding_subtypeVal
  have hself : ∀ Q : ExpStock, Q ∈ lbdΓ qbar Q := fun Q => ⟨le_rfl, by linarith [h.qbar_pos]⟩
  refine ⟨fun Q => ⟨Q, hself Q⟩, fun Q => hemb.isCompact_preimage isCompact_Icc,
    fun Q => ⟨⟨Q, hself Q⟩, fun y hy Qs hQs => ?_⟩,
    fun Q => ⟨⟨Q, hself Q⟩, fun Qs hQs ys hys => ?_⟩⟩
  · -- l.h.c.: shift `y` with `Q`
    have hy0 : 0 ≤ y.1 - Q.1 := sub_nonneg.2 hy.1
    refine ⟨0, fun n => ⟨(Qs n).1 + (y.1 - Q.1), mem_Ici.2 (add_nonneg (Qs n).2 hy0)⟩,
      fun n _ => ⟨by simp only; linarith, by simp only; linarith [hy.2]⟩, ?_⟩
    have := ((continuous_subtype_val.tendsto Q).comp hQs).add_const (y.1 - Q.1)
    rw [show Q.1 + (y.1 - Q.1) = y.1 by ring] at this
    exact tendsto_subtype_rng.2 this
  · -- u.h.c.: the `yₙ` lie in a compact set, and `Γ` has a closed graph
    have hval := (continuous_subtype_val.tendsto Q).comp hQs
    obtain ⟨B, hB⟩ := hval.bddAbove_range
    have hK : ∀ n, ys n ∈ Subtype.val ⁻¹' Icc (0 : ℝ) (B + qbar) := fun n =>
      ⟨(ys n).2, (hys n).2.trans (by linarith [show (Qs n).1 ≤ B from hB ⟨n, rfl⟩])⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := (hemb.isCompact_preimage isCompact_Icc).tendsto_subseq hK
    have hyl := (continuous_subtype_val.tendsto y).comp hlim
    have hQl := hval.comp hφ.tendsto_atTop
    refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
    · exact le_of_tendsto_of_tendsto hQl hyl (Eventually.of_forall fun n => (hys (φ n)).1)
    · exact le_of_tendsto_of_tendsto hyl (hQl.add_const qbar)
        (Eventually.of_forall fun n => (hys (φ n)).2)

/-- Assumption 4.4 holds: on the graph `q = y − Q ∈ [0, q̄]`, so `F` is bounded and continuous. -/
theorem lbd_assumption44 (h : LBDHyp R γ qbar β) : Assumption44 (lbdΓ qbar) (lbdF R γ) β := by
  have hq : ∀ p ∈ graph (lbdΓ qbar), p.2.1 - p.1.1 ∈ Icc 0 qbar := fun p hp =>
    ⟨sub_nonneg.2 hp.1, by linarith [hp.2]⟩
  have hγc : Continuous fun p : ExpStock × ExpStock => γ p.1.1 :=
    h.γ_cont.comp_continuous (continuous_subtype_val.comp continuous_fst) fun p => p.1.2
  have hqc : Continuous fun p : ExpStock × ExpStock => p.2.1 - p.1.1 :=
    (continuous_subtype_val.comp continuous_snd).sub (continuous_subtype_val.comp continuous_fst)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn h.R_cont
  refine ⟨(h.R_cont.comp hqc.continuousOn hq).sub (hqc.mul hγc).continuousOn,
    ⟨B + qbar * γ 0, fun p hp => ?_⟩, h.β_pos, h.β_lt⟩
  have h1 := hB _ (hq p hp)
  rw [Real.norm_eq_abs] at h1
  have hγ0 := h.γ_nonneg _ p.1.2
  have hγ1 := lbd_γ_le h p.1
  have hq' := hq p hp
  have h2 : |(p.2.1 - p.1.1) * γ p.1.1| ≤ qbar * γ 0 := by
    rw [abs_mul, abs_of_nonneg hq'.1, abs_of_nonneg hγ0]
    exact mul_le_mul hq'.2 hγ1 hγ0 h.qbar_pos.le
  simp only [lbdF]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- **Exercises 5.6a–b.** There is a unique bounded continuous `v` satisfying the functional
equation; it is the supremum function, and the policy correspondence is nonempty and u.h.c. -/
theorem lbd_exists (h : LBDHyp R γ qbar β) :
    ∃ v : ExpStock →ᵇ ℝ, bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v ∧
      (∀ w, bellman (lbd_assumption43 h) (lbd_assumption44 h) w = w → w = v) ∧
      (fun x => (v x : EReal)) = vstar (lbdΓ qbar) (curryF (lbdF R γ)) β ∧
      ∀ x, (argmax (obj (lbdF R γ) β v) (lbdΓ qbar) x).Nonempty ∧
        IsUHC (argmax (obj (lbdF R γ) β v) (lbdΓ qbar)) x := by
  have : Nonempty ExpStock := ⟨⟨0, mem_Ici.2 le_rfl⟩⟩
  obtain ⟨v, hv, huniq, -, hG⟩ := theorem_4_6 (lbd_assumption43 h) (lbd_assumption44 h)
  exact ⟨v, hv, huniq, fixedPoint_eq_vstar _ _ hv, fun x => ⟨(hG x).1, (hG x).2.2⟩⟩

/-- **Exercise 5.6a.** Assumption 4.6 fails: `Γ` is not monotone. -/
theorem lbd_not_a46 (hq : 0 < qbar) :
    ¬ ∀ Q Q' : ExpStock, Q ≤ Q' → lbdΓ qbar Q ⊆ lbdΓ qbar Q' := by
  intro hmono
  have h0 : (⟨0, mem_Ici.2 le_rfl⟩ : ExpStock) ≤ ⟨qbar, mem_Ici.2 hq.le⟩ := hq.le
  have := hmono _ _ h0 (show (⟨0, mem_Ici.2 le_rfl⟩ : ExpStock) ∈ lbdΓ qbar ⟨0, _⟩ from
    ⟨le_rfl, by simp only; linarith⟩)
  exact absurd this.1 (by simp only [not_le]; exact hq)

/-- **Exercise 5.6a.** Assumption 4.7 fails: `F(Q, Q) = 0` for every `Q`, so `F` is not strictly
concave between `(0, 0)` and `(1, 1)`. -/
theorem lbd_not_a47 (h : LBDHyp R γ qbar β) :
    ¬ Assumption47 (convex_Ici 0) (lbdΓ qbar) (lbdF R γ) := by
  intro h47
  have hself : ∀ Q : ExpStock, Q ∈ lbdΓ qbar Q := fun Q => ⟨le_rfl, by linarith [h.qbar_pos]⟩
  set a : ExpStock := ⟨0, mem_Ici.2 le_rfl⟩
  set b : ExpStock := ⟨1, mem_Ici.2 zero_le_one⟩
  have hne : a ≠ b := fun he => by
    have := congrArg Subtype.val he
    simp [a, b] at this
  have := (h47 a a b b (hself a) (hself b) (1 / 2) (by norm_num) (by norm_num)).2 hne
  simp [lbdF, h.R_zero] at this

/-- With a nondecreasing continuation value `w`, producing nothing is never optimal: every
maximizer `y` at `Q` has `y > Q`. -/
theorem lbd_argmax_pos (h : LBDHyp R γ qbar β) {w : ExpStock → ℝ} (hw : Monotone w)
    {Q y : ExpStock} (hy : y ∈ lbdΓ qbar Q)
    (hmax : ∀ z ∈ lbdΓ qbar Q, lbdF R γ (Q, z) + β * w z ≤ lbdF R γ (Q, y) + β * w y) :
    Q.1 < y.1 := by
  obtain ⟨q₀, ⟨hq0, hq0'⟩, hprof⟩ := h.profit
  by_contra hle
  push Not at hle
  have hyQ : y = Q := Subtype.ext (le_antisymm hle hy.1)
  subst hyQ
  set z : ExpStock := ⟨y.1 + q₀, mem_Ici.2 (by linarith [y.2.out])⟩
  have hz : z ∈ lbdΓ qbar y := ⟨by simp only [z]; linarith, by simp only [z]; linarith⟩
  have h1 := hmax z hz
  have hwz : w y ≤ w z := hw (show y.1 ≤ z.1 by simp only [z]; linarith)
  have hγ := lbd_γ_le h y
  simp only [lbdF, z, sub_self, h.R_zero, zero_mul, add_sub_cancel_left] at h1
  nlinarith [h.β_pos]

/-- **Exercises 5.6a–b.** `v` is strictly increasing: `T` maps nondecreasing functions into
strictly increasing ones (copy the optimal output from `Q` at `Q' > Q`: the cost is lower and
the continuation no smaller). -/
theorem lbd_strictMono (h : LBDHyp R γ qbar β) {v : ExpStock →ᵇ ℝ}
    (hv : bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v) : StrictMono v := by
  set C' : Set (ExpStock →ᵇ ℝ) := {f | Monotone f}
  set C'' : Set (ExpStock →ᵇ ℝ) := {f | StrictMono f}
  have hclosed : IsClosed C' := by
    have : C' = ⋂ x, ⋂ y, ⋂ (_ : x ≤ y), {f : ExpStock →ᵇ ℝ | f x ≤ f y} := by
      ext f; simp [C', Monotone]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const x) (continuous_eval_const y)
  have hmaps : MapsTo (bellman (lbd_assumption43 h) (lbd_assumption44 h)) C' C'' :=
    fun f hf Q Q' hQQ' => by
      obtain ⟨y, hy, hval, hmax⟩ :=
        exists_bellman_argmax (lbd_assumption43 h) (lbd_assumption44 h) f Q
      obtain ⟨-, -, -, hmax'⟩ :=
        exists_bellman_argmax (lbd_assumption43 h) (lbd_assumption44 h) f Q'
      have hpos := lbd_argmax_pos h hf hy fun z hz => hval ▸ hmax z hz
      have hQQ'' : Q.1 < Q'.1 := hQQ'
      set y' : ExpStock := ⟨y.1 + (Q'.1 - Q.1), mem_Ici.2 (by linarith [y.2.out])⟩
      have hy' : y' ∈ lbdΓ qbar Q' :=
        ⟨by simp only [y']; linarith [hy.1], by simp only [y']; linarith [hy.2]⟩
      have h1 := hmax' y' hy'
      have hγ : γ Q'.1 < γ Q.1 := h.γ_anti Q.2 Q'.2 hQQ''
      have hfy : f y ≤ f y' := hf (show y.1 ≤ y'.1 by simp only [y']; linarith)
      have hcost : (y.1 - Q.1) * γ Q'.1 < (y.1 - Q.1) * γ Q.1 :=
        mul_lt_mul_of_pos_left hγ (by linarith)
      change bellman _ _ f Q < bellman _ _ f Q'
      rw [hval]
      have e : y'.1 - Q'.1 = y.1 - Q.1 := by simp only [y']; ring
      simp only [lbdF, e] at h1 ⊢
      nlinarith [h.β_pos]
  have hne : C'.Nonempty := ⟨0, fun _ _ _ => le_rfl⟩
  exact (corollary_1 (bellman_contraction (lbd_assumption43 h) (lbd_assumption44 h)) hv hne
    hclosed (fun f hf => (hmaps hf).monotone) hmaps).2

/-- **Exercises 5.6a–b.** Let `q̃ ∈ (0, q̄)` be the unique maximizer of the current return
`R(q) − qγ(Q)` on `[0, q̄]`, with `R` differentiable at `q̃`, and let `γ` be convex. Then every
optimal choice `y*` has output `y* − Q > q̃`. -/
theorem lbd_policy_exceeds (h : LBDHyp R γ qbar β) (hγc : ConvexOn ℝ (Ici 0) γ)
    {v : ExpStock →ᵇ ℝ} (hv : bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v)
    {Q : ExpStock} {qt R' : ℝ} (hqt : qt ∈ Ioo 0 qbar)
    (hqmax : ∀ q ∈ Icc 0 qbar, q ≠ qt → R q - q * γ Q.1 < R qt - qt * γ Q.1)
    (hR : HasDerivAt R R' qt) {ystar : ExpStock}
    (hys : ystar ∈ argmax (obj (lbdF R γ) β v) (lbdΓ qbar) Q) :
    qt < ystar.1 - Q.1 := by
  have h43 := lbd_assumption43 h
  have h44 := lbd_assumption44 h
  have hvm := lbd_strictMono h hv
  have hle : ∀ z ∈ lbdΓ qbar Q, obj (lbdF R γ) β v (Q, z) ≤ obj (lbdF R γ) β v (Q, ystar) :=
    fun z hz => by
      rw [hys.2]; exact le_maxValue (continuousOn_obj h44 v.continuous) (h43.compact Q) hz
  have hq := hys.1
  set ψ : ℝ → ℝ := fun q => R q - q * γ Q.1
  -- (1) `q* ≥ q̃`
  have hge : qt ≤ ystar.1 - Q.1 := by
    by_contra hlt
    push Not at hlt
    set z : ExpStock := ⟨Q.1 + qt, mem_Ici.2 (by linarith [Q.2.out, hqt.1])⟩
    have hz : z ∈ lbdΓ qbar Q := ⟨by simp only [z]; linarith [hqt.1],
      by simp only [z]; linarith [hqt.2]⟩
    have h1 := hqmax (ystar.1 - Q.1) ⟨by linarith [hq.1], by linarith [hq.2]⟩ hlt.ne
    have h2 : v ystar < v z := hvm (show ystar.1 < z.1 by simp only [z]; linarith)
    have h3 := hle z hz
    simp only [obj, lbdF, z, add_sub_cancel_left] at h3
    nlinarith [h.β_pos]
  -- (2) `q* ≠ q̃`
  refine lt_of_le_of_ne hge fun heq => ?_
  have hyst : ystar.1 = Q.1 + qt := by linarith
  -- the first-order condition at the interior maximum `q̃`
  have hψ : HasDerivAt ψ (R' - γ Q.1) qt := by
    have := hR.sub ((hasDerivAt_id' qt).mul_const (γ Q.1))
    rwa [one_mul] at this
  have hloc : IsLocalMax ψ qt := by
    filter_upwards [Icc_mem_nhds hqt.1 hqt.2] with q hq'
    rcases eq_or_ne q qt with rfl | hne
    · exact le_rfl
    · exact (hqmax q hq' hne).le
  have hfoc : R' - γ Q.1 = 0 := hloc.hasDerivAt_eq_zero hψ
  rw [hfoc] at hψ
  -- the optimal output at `y*` is positive
  obtain ⟨y₁, hy₁, hy₁v, hy₁max⟩ := exists_bellman_argmax h43 h44 v ystar
  rw [hv] at hy₁v hy₁max
  have hq₁ := lbd_argmax_pos h hvm.monotone hy₁ fun z hz => hy₁v ▸ hy₁max z hz
  set q₁ := y₁.1 - ystar.1
  -- the cost falls at a rate at least `s₀ = γ(y*) − γ(y* + 1) > 0`
  set s₀ := γ ystar.1 - γ (ystar.1 + 1)
  have hs₀ : 0 < s₀ := sub_pos.2 (h.γ_anti ystar.2 (mem_Ici.2 (by linarith [ystar.2.out]))
    (by linarith))
  have hcost : ∀ ε, 0 < ε → ε ≤ 1 → s₀ * ε ≤ γ ystar.1 - γ (ystar.1 + ε) := fun ε hε hε1 => by
    have := hγc.2 (mem_Ici.2 ystar.2.out) (mem_Ici.2 (by linarith [ystar.2.out] :
      (0 : ℝ) ≤ ystar.1 + 1)) (sub_nonneg.2 hε1) hε.le (by ring)
    simp only [smul_eq_mul] at this
    rw [show (1 - ε) * ystar.1 + ε * (ystar.1 + 1) = ystar.1 + ε by ring] at this
    simp only [s₀]
    nlinarith
  -- so `v(y* + ε) − v(y*) ≥ q₁ s₀ ε`
  have hvgain : ∀ ε (hε : 0 < ε), ε ≤ 1 →
      v ystar + q₁ * (s₀ * ε) ≤ v ⟨ystar.1 + ε, mem_Ici.2 (by linarith [ystar.2.out])⟩ :=
    fun ε hε hε1 => by
      set yε : ExpStock := ⟨ystar.1 + ε, mem_Ici.2 (by linarith [ystar.2.out])⟩
      set y₁ε : ExpStock := ⟨y₁.1 + ε, mem_Ici.2 (by linarith [y₁.2.out])⟩
      obtain ⟨-, -, -, hmaxε⟩ := exists_bellman_argmax h43 h44 v yε
      rw [hv] at hmaxε
      have hmem : y₁ε ∈ lbdΓ qbar yε :=
        ⟨by simp only [y₁ε, yε]; linarith [hy₁.1], by simp only [y₁ε, yε]; linarith [hy₁.2]⟩
      have h1 := hmaxε y₁ε hmem
      have h2 : v y₁ ≤ v y₁ε := hvm.monotone (show y₁.1 ≤ y₁ε.1 by simp only [y₁ε]; linarith)
      have h3 := hcost ε hε hε1
      have e : y₁ε.1 - yε.1 = q₁ := by simp only [y₁ε, yε, q₁]; ring
      simp only [lbdF, e] at h1 hy₁v
      have h4 : q₁ * (s₀ * ε) ≤ q₁ * (γ ystar.1 - γ (ystar.1 + ε)) :=
        mul_le_mul_of_nonneg_left h3 (by simp only [q₁]; linarith)
      simp only [yε] at h1 ⊢
      nlinarith [h.β_pos]
  -- pick `ε` small enough that the current return falls by less than half the gain
  set c := β * q₁ * s₀ / 2
  have hc : 0 < c := by
    have : 0 < q₁ := by simp only [q₁]; linarith
    exact div_pos (mul_pos (mul_pos h.β_pos this) hs₀) two_pos
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (ψ (qt + t) - ψ qt)) (𝓝[>] 0) (𝓝 0) :=
    (hasDerivAt_iff_tendsto_slope_zero.1 hψ).mono_left
      (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne')
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), -c < t⁻¹ • (ψ (qt + t) - ψ qt) ∧ 0 < t ∧ t < 1 ∧
      t < qbar - qt := by
    refine (hslope.eventually (lt_mem_nhds (neg_lt_zero.2 hc))).and
      ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ))).and ?_)
    have h1 : (0 : ℝ) < min 1 (qbar - qt) := lt_min one_pos (by linarith [hqt.2])
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h1)] with t ht
    exact ⟨ht.trans_le (min_le_left _ _), ht.trans_le (min_le_right _ _)⟩
  obtain ⟨ε, hslp, hε, hε1, hεq⟩ := hev.exists
  have hψε : -c * ε < ψ (qt + ε) - ψ qt := by
    rw [smul_eq_mul] at hslp
    have := mul_lt_mul_of_pos_left hslp hε
    rwa [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_comm] at this
  -- the larger output `q̃ + ε` beats `y*`
  set z : ExpStock := ⟨ystar.1 + ε, mem_Ici.2 (by linarith [ystar.2.out])⟩
  have hz : z ∈ lbdΓ qbar Q := ⟨by simp only [z]; linarith [hq.1],
    by simp only [z]; linarith [hqt.2]⟩
  have h1 := hle z hz
  have h2 : v ystar + q₁ * (s₀ * ε) ≤ v z := hvgain ε hε hε1.le
  have ez : z.1 - Q.1 = qt + ε := by simp only [z]; linarith
  have ey : ystar.1 - Q.1 = qt := by linarith
  simp only [obj, lbdF, ez, ey] at h1
  simp only [ψ] at hψε
  have hq₁0 : 0 < q₁ := by simp only [q₁]; linarith
  have hβ2 := mul_le_mul_of_nonneg_left h2 h.β_pos.le
  have hcε : c * ε = β * (q₁ * (s₀ * ε)) / 2 := by simp only [c]; ring
  have hpos : 0 < β * (q₁ * (s₀ * ε)) := mul_pos h.β_pos (mul_pos hq₁0 (mul_pos hs₀ hε))
  nlinarith

/-- A function with strictly decreasing derivative on `[0, q̄]`, positive at `0` and negative at
`q̄`, has a unique maximizer `q̃ ∈ (0, q̄)` on `[0, q̄]`, where its derivative vanishes. -/
theorem unique_interior_max {ψ ψ' : ℝ → ℝ} (hq : 0 < qbar) (hc : ContinuousOn ψ (Icc 0 qbar))
    (hd : ∀ q ∈ Ioo 0 qbar, HasDerivAt ψ (ψ' q) q) (hc' : ContinuousOn ψ' (Icc 0 qbar))
    (hanti : StrictAntiOn ψ' (Icc 0 qbar)) (h0 : 0 < ψ' 0) (h1 : ψ' qbar < 0) :
    ∃ qt ∈ Ioo 0 qbar, ψ' qt = 0 ∧ ∀ q ∈ Icc 0 qbar, q ≠ qt → ψ q < ψ qt := by
  obtain ⟨qt, hqt, hzero⟩ := intermediate_value_Icc' hq.le hc' ⟨h1.le, h0.le⟩
  have hqt0 : qt ≠ 0 := fun he => by rw [he] at hzero; linarith
  have hqt1 : qt ≠ qbar := fun he => by rw [he] at hzero; linarith
  have hqt' : qt ∈ Ioo 0 qbar := ⟨lt_of_le_of_ne hqt.1 (Ne.symm hqt0), lt_of_le_of_ne hqt.2 hqt1⟩
  refine ⟨qt, hqt', hzero, fun q hq' hne => ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' hlt
      (hc.mono (Icc_subset_Icc hq'.1 hqt.2))
      (fun x hx => hd x ⟨hq'.1.trans_lt hx.1, hx.2.trans hqt'.2⟩)
    have hpos : 0 < ψ' ξ := by
      have := hanti ⟨hq'.1.trans hξ.1.le, (hξ.2.trans hqt'.2).le⟩ hqt hξ.2
      linarith
    rw [hslope] at hpos
    have := (div_pos_iff_of_pos_right (by linarith : 0 < qt - q)).1 hpos
    linarith
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' hgt
      (hc.mono (Icc_subset_Icc hqt.1 hq'.2))
      (fun x hx => hd x ⟨hqt'.1.trans hx.1, hx.2.trans_le hq'.2⟩)
    have hneg : ψ' ξ < 0 := by
      have := hanti hqt ⟨(hqt.1.trans hξ.1.le), (hξ.2.trans_le hq'.2).le⟩ hξ.1
      linarith
    rw [hslope] at hneg
    have := (div_neg_iff.1 hneg)
    rcases this with ⟨-, h2⟩ | ⟨h2, -⟩
    · linarith
    · linarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Learning by doing: the monopolist, the planner and the competitive industry

SLP §5.6, pp. 107–109, with the book's assumptions (`LBDModel`): `γ` is strictly decreasing and
convex with `γ(Q) → c ≥ 0`; inverse demand `φ` is strictly decreasing and differentiable, with
strictly decreasing marginal revenue, `φ(0) > γ(0) = c̄` and `φ(q̄) = c`.

* **Exercise 5.6a** (`ex_5_6a`): for the monopolist, `R(q) = qφ(q)`. The general results of
  `LearningByDoing` apply, and at each `Q` the output `q̃` that maximizes current profit is
  unique and interior, and every optimal output exceeds it.
* **Exercise 5.6b** (`ex_5_6b_surplus`, `ex_5_6b`): consumer surplus `S(q) = ∫₀^q φ` is strictly
  increasing, strictly concave and continuously differentiable; for the planner, `R = S`, the
  value `w` is unique, strictly increasing and at most `S(q̄)/(1 − β)`, and every efficient
  output exceeds the output maximizing current surplus.
* **Exercise 5.6c** (`ex_5_6c`, `competitive_path`): competitive output at `Q` solves
  `φ(q) = γ(Q)` (price equals unit cost), which is exactly the current-surplus maximizer; so the
  efficient output exceeds the competitive output at every `Q`. Along the competitive path
  output rises, the price `γ(Q_t)` falls, and the price converges to `c`.
* **Exercise 5.6d** (`ex_5_6d`): for a nonrenewable resource with stock `Q ∈ [0, Q̄]`, extraction
  `Q − y` and `Γ(Q) = [0, Q]`, the functional equation again has a unique bounded continuous
  solution, equal to the supremum function.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- The assumptions of SLP §5.6 on demand `φ` (with derivative `φ'`) and unit cost `γ`. -/
structure LBDModel (φ φ' γ : ℝ → ℝ) (c qbar β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  qbar_pos : 0 < qbar
  φ_cont : ContinuousOn φ (Ici 0)
  φ_deriv : ∀ q, 0 < q → HasDerivAt φ (φ' q) q
  φ'_cont : ContinuousOn φ' (Ici 0)
  φ_anti : StrictAntiOn φ (Ici 0)
  φ_nonneg : ∀ q, 0 ≤ q → 0 ≤ φ q
  mr_anti : StrictAntiOn (fun q => φ q + q * φ' q) (Icc 0 qbar)
  φ_zero : γ 0 < φ 0
  φ_qbar : φ qbar = c
  γ_cont : ContinuousOn γ (Ici 0)
  γ_anti : StrictAntiOn γ (Ici 0)
  γ_convex : ConvexOn ℝ (Ici 0) γ
  γ_lim : Tendsto γ atTop (𝓝 c)

variable {φ φ' γ : ℝ → ℝ} {c qbar β : ℝ}

/-- Unit cost stays above its limit: `γ(Q) > c`. -/
theorem LBDModel.c_lt_γ (h : LBDModel φ φ' γ c qbar β) {Q : ℝ} (hQ : 0 ≤ Q) : c < γ Q := by
  have hlt : γ (Q + 1) < γ Q := h.γ_anti (mem_Ici.2 hQ) (mem_Ici.2 (by linarith)) (by linarith)
  have hle : c ≤ γ (Q + 1) := by
    refine le_of_tendsto h.γ_lim (eventually_atTop.2 ⟨Q + 1, fun x hx => ?_⟩)
    exact h.γ_anti.antitoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) hx
  linarith

theorem LBDModel.c_nonneg (h : LBDModel φ φ' γ c qbar β) : 0 ≤ c := by
  rw [← h.φ_qbar]; exact h.φ_nonneg _ h.qbar_pos.le

/-- A decreasing differentiable function has a nonpositive derivative. -/
theorem LBDModel.φ'_nonpos (h : LBDModel φ φ' γ c qbar β) {q : ℝ} (hq : 0 < q) : φ' q ≤ 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope_zero.1 (h.φ_deriv q hq)).mono_left
    (nhdsWithin_mono (0 : ℝ) fun t (ht : t ∈ Ioi (0 : ℝ)) => ne_of_gt ht)
  refine le_of_tendsto hs ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have := h.φ_anti (mem_Ici.2 hq.le) (mem_Ici.2 (by linarith)) (by linarith : q < q + t)
  rw [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht.le) (by linarith)

/-- Near `0`, demand exceeds the highest unit cost: some `q₀ ∈ (0, q̄]` has `φ > γ(0)` on
`[0, q₀]`. -/
theorem LBDModel.exists_small (h : LBDModel φ φ' γ c qbar β) :
    ∃ q₀ ∈ Ioc 0 qbar, ∀ q ∈ Icc 0 q₀, γ 0 < φ q := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1
    (h.φ_cont 0 (mem_Ici.2 le_rfl)) (φ 0 - γ 0) (by linarith [h.φ_zero])
  refine ⟨min (δ / 2) qbar, ⟨lt_min (by linarith) h.qbar_pos, min_le_right _ _⟩,
    fun q hq => ?_⟩
  have := hball (mem_Ici.2 hq.1) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hq.1]
    exact hq.2.trans_lt ((min_le_left _ _).trans_lt (by linarith)))
  rw [Real.dist_eq] at this
  linarith [neg_abs_le (φ q - φ 0)]

/-! ### Exercise 5.6a: the monopolist -/

/-- The monopolist's problem satisfies the hypotheses of `LearningByDoing` with `R(q) = qφ(q)`. -/
theorem monopoly_hyp (h : LBDModel φ φ' γ c qbar β) :
    LBDHyp (fun q => q * φ q) γ qbar β := by
  obtain ⟨q₀, hq₀, hsmall⟩ := h.exists_small
  refine ⟨h.β_pos, h.β_lt, h.qbar_pos,
    continuousOn_id.mul (h.φ_cont.mono fun q hq => mem_Ici.2 hq.1), by simp, h.γ_cont,
    h.γ_anti, fun Q hQ => h.c_nonneg.trans (h.c_lt_γ hQ).le, ⟨q₀, hq₀, ?_⟩⟩
  exact mul_lt_mul_of_pos_left (hsmall q₀ ⟨hq₀.1.le, le_rfl⟩) hq₀.1

/-- **Exercise 5.6a.** There is a unique bounded continuous `v`; it is strictly increasing; and at
every `Q` the profit-maximizing output `q̃` is unique and interior, and every optimal output
exceeds it: `y* ∈ G(Q)` implies `y* − Q > q̃`. -/
theorem ex_5_6a (h : LBDModel φ φ' γ c qbar β) :
    (∃ v : ExpStock →ᵇ ℝ,
      bellman (lbd_assumption43 (monopoly_hyp h)) (lbd_assumption44 (monopoly_hyp h)) v = v ∧
      ∀ w, bellman (lbd_assumption43 (monopoly_hyp h)) (lbd_assumption44 (monopoly_hyp h)) w = w →
        w = v) ∧
    ∀ {v : ExpStock →ᵇ ℝ},
      bellman (lbd_assumption43 (monopoly_hyp h)) (lbd_assumption44 (monopoly_hyp h)) v = v →
      StrictMono v ∧ ∀ Q : ExpStock, ∃ qt ∈ Ioo 0 qbar,
        (∀ q ∈ Icc 0 qbar, q ≠ qt → q * φ q - q * γ Q.1 < qt * φ qt - qt * γ Q.1) ∧
        ∀ y ∈ argmax (obj (lbdF (fun q => q * φ q) γ) β v) (lbdΓ qbar) Q, qt < y.1 - Q.1 := by
  obtain ⟨v, hv, huniq, -⟩ := lbd_exists (monopoly_hyp h)
  refine ⟨⟨v, hv, huniq⟩, fun {v} hv => ⟨lbd_strictMono (monopoly_hyp h) hv, fun Q => ?_⟩⟩
  have hγQ := h.c_lt_γ Q.2.out
  have hγ0 : γ Q.1 ≤ γ 0 := lbd_γ_le (monopoly_hyp h) Q
  -- the current-profit maximizer
  obtain ⟨qt, hqt, -, hmax⟩ := unique_interior_max (ψ := fun q => q * φ q - q * γ Q.1)
    (ψ' := fun q => φ q + q * φ' q - γ Q.1) h.qbar_pos
    ((continuousOn_id.mul (h.φ_cont.mono fun q hq => mem_Ici.2 hq.1)).sub
      (continuousOn_id.mul continuousOn_const))
    (fun q hq => by
      have := ((hasDerivAt_id' q).mul (h.φ_deriv q hq.1)).sub
        ((hasDerivAt_id' q).mul_const (γ Q.1))
      convert this using 1; ring)
    (((h.φ_cont.mono fun q hq => mem_Ici.2 hq.1).add (continuousOn_id.mul
      (h.φ'_cont.mono fun q hq => mem_Ici.2 hq.1))).sub continuousOn_const)
    (fun a ha b hb hab => by have := h.mr_anti ha hb hab; simp only at this ⊢; linarith)
    (by simp only [zero_mul, add_zero]; linarith [h.φ_zero])
    (by
      have := h.φ'_nonpos h.qbar_pos
      have : qbar * φ' qbar ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h.qbar_pos.le this
      simp only [h.φ_qbar]; linarith)
  refine ⟨qt, hqt, hmax, fun y hy => ?_⟩
  exact lbd_policy_exceeds (monopoly_hyp h) h.γ_convex hv hqt hmax
    ((hasDerivAt_id' qt).mul (h.φ_deriv qt hqt.1)) hy

/-! ### Exercise 5.6b: consumer surplus and the planner -/

/-- Consumer surplus `S(q) = ∫₀^q φ`. -/
noncomputable def surplus (φ : ℝ → ℝ) (q : ℝ) : ℝ := ∫ z in (0 : ℝ)..q, φ z

theorem surplus_hasDerivAt (h : LBDModel φ φ' γ c qbar β) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (surplus φ) (φ q) q :=
  intervalIntegral.integral_hasDerivAt_right
    ((h.φ_cont.mono fun z hz => by
      rw [uIcc_of_le hq.le] at hz; exact mem_Ici.2 hz.1).intervalIntegrable)
    ((h.φ_cont.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi q hq)
    (h.φ_cont.continuousAt (Ici_mem_nhds hq))

theorem surplus_continuousOn (h : LBDModel φ φ' γ c qbar β) {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (surplus φ) (Icc 0 b) := by
  have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
    (a := 0) (b := b) (f := φ)
    ((h.φ_cont.mono fun z hz => by
      rw [uIcc_of_le hb] at hz; exact mem_Ici.2 hz.1).integrableOn_compact isCompact_uIcc)
  rwa [uIcc_of_le hb] at this

theorem surplus_continuousOn_Ici (h : LBDModel φ φ' γ c qbar β) :
    ContinuousOn (surplus φ) (Ici 0) := by
  intro q hq
  have h1 := surplus_continuousOn h (b := q + 1) (by linarith [hq.out])
  have hmem : Icc (0 : ℝ) (q + 1) ∈ 𝓝[Ici 0] q := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (h1 q ⟨hq.out, by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- **Exercise 5.6b.** `S` is strictly increasing, strictly concave and continuously
differentiable (`S' = φ`, continuous). -/
theorem ex_5_6b_surplus (h : LBDModel φ φ' γ c qbar β) :
    StrictMonoOn (surplus φ) (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) (surplus φ) ∧
      (∀ q, 0 < q → HasDerivAt (surplus φ) (φ q) q) ∧ ContinuousOn φ (Ici 0) := by
  have hderiv : ∀ q ∈ interior (Ici (0 : ℝ)), deriv (surplus φ) q = φ q := fun q hq => by
    rw [interior_Ici] at hq
    exact (surplus_hasDerivAt h hq).deriv
  refine ⟨strictMonoOn_of_deriv_pos (convex_Ici 0) (surplus_continuousOn_Ici h)
    fun q hq => ?_, StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
    (surplus_continuousOn_Ici h) fun a ha b hb hab => ?_,
    fun q hq => surplus_hasDerivAt h hq, h.φ_cont⟩
  · rw [hderiv q hq]
    rw [interior_Ici] at hq
    have hq' : (0 : ℝ) < q := hq
    have := h.φ_anti (mem_Ici.2 hq'.le) (mem_Ici.2 (by linarith)) (by linarith : q < q + 1)
    linarith [h.φ_nonneg (q + 1) (by linarith)]
  · rw [hderiv a ha, hderiv b hb]
    rw [interior_Ici] at ha hb
    exact h.φ_anti (mem_Ici.2 (le_of_lt ha)) (mem_Ici.2 (le_of_lt hb)) hab

/-- The planner's problem satisfies the hypotheses of `LearningByDoing` with `R = S`. -/
theorem planner_hyp (h : LBDModel φ φ' γ c qbar β) : LBDHyp (surplus φ) γ qbar β := by
  obtain ⟨q₀, hq₀, hsmall⟩ := h.exists_small
  refine ⟨h.β_pos, h.β_lt, h.qbar_pos, surplus_continuousOn h h.qbar_pos.le,
    by simp [surplus], h.γ_cont, h.γ_anti, fun Q hQ => h.c_nonneg.trans (h.c_lt_γ hQ).le,
    ⟨q₀, hq₀, ?_⟩⟩
  -- the mean value theorem: `S(q₀) = φ(ξ)q₀` with `φ(ξ) > γ(0)`
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (surplus φ) φ hq₀.1
    (surplus_continuousOn h hq₀.1.le) fun x hx => surplus_hasDerivAt h hx.1
  have h0 : surplus φ 0 = 0 := by simp [surplus]
  rw [h0, sub_zero, sub_zero, eq_div_iff hq₀.1.ne'] at hslope
  rw [← hslope]
  have := hsmall ξ ⟨hξ.1.le, hξ.2.le⟩
  nlinarith [hq₀.1]

/-- A fixed point is bounded by `M/(1 − β)` when the return is bounded by `M`. -/
theorem lbd_value_le {R : ℝ → ℝ} (h : LBDHyp R γ qbar β) {v : ExpStock →ᵇ ℝ}
    (hv : bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v) {M : ℝ}
    (hM : ∀ p ∈ graph (lbdΓ qbar), lbdF R γ p ≤ M) (Q : ExpStock) :
    v Q ≤ M / (1 - β) := by
  have hbdd : BddAbove (range v) := ⟨‖v‖, by
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (v.norm_coe_le_norm x))⟩
  have hs : ∀ x, v x ≤ M + β * ⨆ z, v z := fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax (lbd_assumption43 h) (lbd_assumption44 h) v x
    rw [hv] at hval
    rw [hval]
    exact add_le_add (hM (x, y) hy) (mul_le_mul_of_nonneg_left (le_ciSup hbdd y) h.β_pos.le)
  have : Nonempty ExpStock := ⟨⟨0, mem_Ici.2 le_rfl⟩⟩
  have hsup : (⨆ z, v z) ≤ M + β * ⨆ z, v z := ciSup_le hs
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  rw [le_div_iff₀ h1β]
  have := le_ciSup hbdd Q
  nlinarith [h.β_pos]

/-- **Exercise 5.6b.** For the planner: `w` is unique, strictly increasing and at most
`S(q̄)/(1 − β)`; the current-surplus maximizer `q̃` is unique and interior, solves
`φ(q̃) = γ(Q)`, and every efficient output exceeds it. -/
theorem ex_5_6b (h : LBDModel φ φ' γ c qbar β) {w : ExpStock →ᵇ ℝ}
    (hw : bellman (lbd_assumption43 (planner_hyp h)) (lbd_assumption44 (planner_hyp h)) w = w) :
    StrictMono w ∧ (∀ Q, w Q ≤ surplus φ qbar / (1 - β)) ∧
      ∀ Q : ExpStock, ∃ qt ∈ Ioo 0 qbar, φ qt = γ Q.1 ∧
        (∀ q ∈ Icc 0 qbar, q ≠ qt →
          surplus φ q - q * γ Q.1 < surplus φ qt - qt * γ Q.1) ∧
        ∀ y ∈ argmax (obj (lbdF (surplus φ) γ) β w) (lbdΓ qbar) Q, qt < y.1 - Q.1 := by
  have hS := ex_5_6b_surplus h
  refine ⟨lbd_strictMono (planner_hyp h) hw, lbd_value_le (planner_hyp h) hw fun p hp => ?_,
    fun Q => ?_⟩
  · -- `S(q) − qγ(Q) ≤ S(q) ≤ S(q̄)`
    have hq : p.2.1 - p.1.1 ∈ Icc 0 qbar := ⟨sub_nonneg.2 hp.1, by linarith [hp.2]⟩
    have h1 := hS.1.monotoneOn (mem_Ici.2 hq.1) (mem_Ici.2 h.qbar_pos.le) hq.2
    have h2 : 0 ≤ (p.2.1 - p.1.1) * γ p.1.1 :=
      mul_nonneg hq.1 (h.c_nonneg.trans (h.c_lt_γ p.1.2.out).le)
    simp only [lbdF]
    linarith
  · have hγQ := h.c_lt_γ Q.2.out
    have hγ0 : γ Q.1 ≤ γ 0 := lbd_γ_le (planner_hyp h) Q
    obtain ⟨qt, hqt, hzero, hmax⟩ := unique_interior_max
      (ψ := fun q => surplus φ q - q * γ Q.1) (ψ' := fun q => φ q - γ Q.1) h.qbar_pos
      ((surplus_continuousOn h h.qbar_pos.le).sub (continuousOn_id.mul continuousOn_const))
      (fun q hq => by
        have := (surplus_hasDerivAt h hq.1).sub ((hasDerivAt_id' q).mul_const (γ Q.1))
        rwa [one_mul] at this)
      ((h.φ_cont.mono fun q hq => mem_Ici.2 hq.1).sub continuousOn_const)
      (fun a ha b hb hab => by
        have := h.φ_anti (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab
        change φ b - γ Q.1 < φ a - γ Q.1
        linarith)
      (show 0 < φ 0 - γ Q.1 by linarith [h.φ_zero])
      (show φ qbar - γ Q.1 < 0 by rw [h.φ_qbar]; linarith)
    refine ⟨qt, hqt, sub_eq_zero.1 hzero, hmax, fun y hy => ?_⟩
    exact lbd_policy_exceeds (planner_hyp h) h.γ_convex hw hqt hmax
      (surplus_hasDerivAt h hqt.1) hy

/-! ### Exercise 5.6c: the competitive industry -/

/-- **Exercise 5.6c.** Competitive output at `Q` solves `φ(q) = γ(Q)`: price equals unit cost.
Every efficient output exceeds it, so competition produces too little. -/
theorem ex_5_6c (h : LBDModel φ φ' γ c qbar β) {w : ExpStock →ᵇ ℝ}
    (hw : bellman (lbd_assumption43 (planner_hyp h)) (lbd_assumption44 (planner_hyp h)) w = w)
    (Q : ExpStock) {qc : ℝ} (hqc0 : 0 ≤ qc) (hqc : φ qc = γ Q.1)
    {y : ExpStock} (hy : y ∈ argmax (obj (lbdF (surplus φ) γ) β w) (lbdΓ qbar) Q) :
    qc < y.1 - Q.1 := by
  obtain ⟨-, -, hQ⟩ := ex_5_6b h hw
  obtain ⟨qt, hqt, hφ, -, hexc⟩ := hQ Q
  have : qc = qt := h.φ_anti.injOn (mem_Ici.2 hqc0) (mem_Ici.2 hqt.1.le) (by rw [hqc, hφ])
  rw [this]
  exact hexc y hy

/-- Competitive output rises with experience. -/
theorem competitive_output_mono (h : LBDModel φ φ' γ c qbar β) {Q Q' q q' : ℝ} (hQ : 0 ≤ Q)
    (hQQ' : Q < Q') (hq : 0 ≤ q) (hq' : 0 ≤ q') (hφ : φ q = γ Q) (hφ' : φ q' = γ Q') :
    q < q' := by
  by_contra hle
  push Not at hle
  have h1 := h.φ_anti.antitoneOn (mem_Ici.2 hq') (mem_Ici.2 hq) hle
  have h2 := h.γ_anti (mem_Ici.2 hQ) (mem_Ici.2 (by linarith)) hQQ'
  linarith

/-- **Exercise 5.6c.** Along a competitive path `Q_{t+1} = Q_t + q_t` with `φ(q_t) = γ(Q_t)`,
output rises, the price `p_t = γ(Q_t)` falls, and the price converges to `c`. -/
theorem competitive_path (h : LBDModel φ φ' γ c qbar β) {Qs qs : ℕ → ℝ} (hQ0 : 0 ≤ Qs 0)
    (hstep : ∀ t, Qs (t + 1) = Qs t + qs t) (hq : ∀ t, 0 ≤ qs t)
    (hφ : ∀ t, φ (qs t) = γ (Qs t)) :
    StrictMono qs ∧ StrictAnti (fun t => γ (Qs t)) ∧
      Tendsto (fun t => γ (Qs t)) atTop (𝓝 c) := by
  have hQnn : ∀ t, 0 ≤ Qs t := fun t => by
    induction t with
    | zero => exact hQ0
    | succ t ih => rw [hstep]; linarith [hq t]
  -- output is positive, since `φ(0) > γ(0) ≥ γ(Q_t)`
  have hqpos : ∀ t, 0 < qs t := fun t => by
    refine lt_of_le_of_ne (hq t) fun he => ?_
    have h1 := hφ t
    rw [← he] at h1
    have h2 := h.γ_anti.antitoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 (hQnn t)) (hQnn t)
    linarith [h.φ_zero]
  have hQmono : StrictMono Qs := strictMono_nat_of_lt_succ fun t => by
    rw [hstep]; linarith [hqpos t]
  have hqmono : StrictMono qs := strictMono_nat_of_lt_succ fun t =>
    competitive_output_mono h (hQnn t) (hQmono (Nat.lt_succ_self t)) (hq t) (hq (t + 1))
      (hφ t) (hφ (t + 1))
  refine ⟨hqmono, fun s t hst => h.γ_anti (mem_Ici.2 (hQnn s)) (mem_Ici.2 (hQnn t))
    (hQmono hst), h.γ_lim.comp ?_⟩
  -- `Q_t ≥ Q_0 + t q_0 → ∞`
  have hlow : ∀ t : ℕ, Qs 0 + t * qs 0 ≤ Qs t := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hstep]
      have := (hqmono.monotone (Nat.zero_le t))
      push_cast
      linarith
  refine tendsto_atTop_mono hlow (tendsto_atTop_add_const_left _ _ ?_)
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (hqpos 0)

/-! ### Exercise 5.6d: a nonrenewable resource -/

/-- The resource problem: stock `Q ∈ [0, Q̄]`, `Γ(Q) = [0, Q]`, extraction `Q − y`, return
`S(Q − y) − (Q − y)γ(Q)`. -/
def resourceF (R γ : ℝ → ℝ) (Qbar : ℝ) (p : Icc (0 : ℝ) Qbar × Icc (0 : ℝ) Qbar) : ℝ :=
  R (p.1.1 - p.2.1) - (p.1.1 - p.2.1) * γ p.1.1

/-- `Γ(Q) = [0, Q]` on `[0, Q̄]` is the growth correspondence with `f = id`. -/
theorem resource_hyp {Qbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Qbar) :
    GrowthHyp id id β Qbar :=
  ⟨hβ0, hβ1, continuousOn_id, strictMono_id.strictMonoOn _, continuousOn_id, rfl, hQ,
    fun _ hx => ⟨le_rfl, hx.2⟩, strictMono_id.strictMonoOn _⟩

/-- Assumption 4.4 for the resource problem. -/
theorem resource_assumption44 {R : ℝ → ℝ} {Qbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hR : ContinuousOn R (Icc 0 Qbar)) (hγ : ContinuousOn γ (Icc 0 Qbar)) :
    Assumption44 (growthΓ id Qbar) (resourceF R γ Qbar) β := by
  have hq : ∀ p ∈ graph (growthΓ id Qbar), p.1.1 - p.2.1 ∈ Icc 0 Qbar := fun p hp =>
    ⟨sub_nonneg.2 hp, by linarith [p.1.2.2, p.2.2.1]⟩
  have hγc : Continuous fun p : Icc (0 : ℝ) Qbar × Icc (0 : ℝ) Qbar => γ p.1.1 :=
    hγ.comp_continuous (continuous_subtype_val.comp continuous_fst) fun p => p.1.2
  have hqc : Continuous fun p : Icc (0 : ℝ) Qbar × Icc (0 : ℝ) Qbar => p.1.1 - p.2.1 :=
    (continuous_subtype_val.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ
  refine ⟨(hR.comp hqc.continuousOn hq).sub (hqc.mul hγc).continuousOn,
    ⟨B + Qbar * C, fun p hp => ?_⟩, hβ0, hβ1⟩
  have h1 := hB _ (hq p hp)
  have h2 := hC _ p.1.2
  rw [Real.norm_eq_abs] at h1 h2
  have hq' := hq p hp
  have h3 : |(p.1.1 - p.2.1) * γ p.1.1| ≤ Qbar * C := by
    rw [abs_mul, abs_of_nonneg hq'.1]
    exact mul_le_mul hq'.2 h2 (abs_nonneg _) (hq'.1.trans hq'.2)
  simp only [resourceF]
  exact (abs_sub _ _).trans (add_le_add h1 h3)

/-- **Exercise 5.6d.** For a nonrenewable resource the analysis carries over: with `R = S`
continuous and `γ` continuous on `[0, Q̄]`, there is a unique bounded continuous solution of
`w(Q) = max_{0 ≤ y ≤ Q} {S(Q − y) − (Q − y)γ(Q) + βw(y)}`, it is the supremum function, and the
policy correspondence is nonempty and u.h.c. -/
theorem ex_5_6d {R : ℝ → ℝ} {Qbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Qbar)
    (hR : ContinuousOn R (Icc 0 Qbar)) (hγ : ContinuousOn γ (Icc 0 Qbar)) :
    ∃ w : Icc (0 : ℝ) Qbar →ᵇ ℝ,
      bellman (growth_assumption43 (resource_hyp hβ0 hβ1 hQ))
        (resource_assumption44 hβ0 hβ1 hR hγ) w = w ∧
      (∀ w', bellman (growth_assumption43 (resource_hyp hβ0 hβ1 hQ))
        (resource_assumption44 hβ0 hβ1 hR hγ) w' = w' → w' = w) ∧
      (fun x => (w x : EReal)) = vstar (growthΓ id Qbar) (curryF (resourceF R γ Qbar)) β ∧
      ∀ x, (argmax (obj (resourceF R γ Qbar) β w) (growthΓ id Qbar) x).Nonempty ∧
        IsUHC (argmax (obj (resourceF R γ Qbar) β w) (growthΓ id Qbar)) x := by
  have : Nonempty (Icc (0 : ℝ) Qbar) := ⟨⟨0, le_rfl, hQ.le⟩⟩
  obtain ⟨w, hw, huniq, -, hG⟩ := theorem_4_6 (growth_assumption43 (resource_hyp hβ0 hβ1 hQ))
    (resource_assumption44 hβ0 hβ1 hR hγ)
  exact ⟨w, hw, huniq, fixedPoint_eq_vstar _ _ hw, fun x => ⟨(hG x).1, (hG x).2.2⟩⟩

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Human capital accumulation

SLP §5.7, pp. 109–110: a worker with skill `k` who chooses next period's skill `y` works the
fraction `φ(y/k)` of the period and earns `kφ(y/k)`; `(1 − δ)k ≤ y ≤ (1 + λ)k`, with `φ`
strictly decreasing and concave on `I = [1 − δ, 1 + λ]`, `φ(1 − δ) = 1` and `φ(1 + λ) = 0`. The
operator is `(Tf)(k) = max_{y ∈ Γ(k)} [kφ(y/k) + βf(y)]` and `v₀ = 0`.

* `humanT_linear`: `T(a·k) = M(a)·k`, `M(a) = max_{x ∈ I} [φ(x) + βax]`; so
  **Exercise 5.7a**: `Tⁿv₀ = aₙk` with `aₙ₊₁ = M(aₙ)` (`ex_5_7a_iterate`), `a₁ = 1`
  (`ex_5_7a_one`) and `aₙ₊₁ > aₙ` (`ex_5_7a_strictMono`).
* `ex_5_7a_bounded_iff`: `(aₙ)` is bounded iff `β(1 + λ) ≤ 1`, that is `λ ≤ r`. The manual
  answers `λ < r`; at `λ = r` the sequence is still bounded, by `−φ'(1 + λ)(1 + λ)`, because the
  tangent to the concave `φ` at `1 + λ` lies above `φ` (`slope_bound`).
* **Exercise 5.7b**: with `n` periods left the optimal growth factor `xₙ = y/k` maximizes
  `φ(x) + βaₙ₋₁x`. `growth_factor_mono`: it rises with the number of periods left (a Topkis
  argument), so over the life cycle the growth factor of human capital falls and the share
  `φ(xₙ)` of time spent working rises (`ex_5_7b_profile`). In the last period the worker does
  not invest (`ex_5_7b_last`). Minimal accumulation, once optimal, stays optimal, and maximal
  accumulation, once optimal, was optimal before (`ex_5_7b_corners`). Human capital is
  single-peaked: once it falls it keeps falling (`ex_5_7b_single_peaked`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {φ : ℝ → ℝ} {δ lam β : ℝ}

/-- The hypotheses of SLP §5.7. -/
structure HumanHyp (φ : ℝ → ℝ) (δ lam β : ℝ) : Prop where
  δ_pos : 0 < δ
  δ_lt : δ < 1
  lam_pos : 0 < lam
  β_pos : 0 < β
  β_lt : β < 1
  φ_cont : ContinuousOn φ (Icc (1 - δ) (1 + lam))
  φ_anti : StrictAntiOn φ (Icc (1 - δ) (1 + lam))
  φ_concave : ConcaveOn ℝ (Icc (1 - δ) (1 + lam)) φ
  φ_left : φ (1 - δ) = 1
  φ_right : φ (1 + lam) = 0

/-- `Γ(k) = [(1 − δ)k, (1 + λ)k]` on `(0, ∞)`. -/
def humanΓ (δ lam : ℝ) (k : PosR) : Set PosR := {y | (1 - δ) * k.1 ≤ y.1 ∧ y.1 ≤ (1 + lam) * k.1}

/-- `(Tf)(k) = sup_{y ∈ Γ(k)} [kφ(y/k) + βf(y)]`. -/
noncomputable def humanT (φ : ℝ → ℝ) (δ lam β : ℝ) (f : PosR → ℝ) (k : PosR) : ℝ :=
  sSup ((fun y : PosR => k.1 * φ (y.1 / k.1) + β * f y) '' humanΓ δ lam k)

/-- The per-unit objective `φ(x) + βax`. -/
def humanObj (φ : ℝ → ℝ) (β a x : ℝ) : ℝ := φ x + β * a * x

/-- `M(a) = max_{x ∈ [1 − δ, 1 + λ]} [φ(x) + βax]`. -/
noncomputable def humanM (φ : ℝ → ℝ) (δ lam β a : ℝ) : ℝ :=
  sSup (humanObj φ β a '' Icc (1 - δ) (1 + lam))

/-- `a₀ = 0`, `aₙ₊₁ = M(aₙ)`. -/
noncomputable def humanA (φ : ℝ → ℝ) (δ lam β : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => humanM φ δ lam β (humanA φ δ lam β n)

/-- The maximizers of `φ(x) + βax` on `I`. -/
def humanArgmax (φ : ℝ → ℝ) (δ lam β a : ℝ) : Set ℝ :=
  {x | x ∈ Icc (1 - δ) (1 + lam) ∧
    ∀ x' ∈ Icc (1 - δ) (1 + lam), humanObj φ β a x' ≤ humanObj φ β a x}

theorem HumanHyp.I_nonempty (h : HumanHyp φ δ lam β) : (1 - δ) ≤ (1 + lam) := by
  linarith [h.δ_pos, h.lam_pos]

theorem HumanHyp.obj_cont (h : HumanHyp φ δ lam β) (a : ℝ) :
    ContinuousOn (humanObj φ β a) (Icc (1 - δ) (1 + lam)) :=
  h.φ_cont.add (continuousOn_const.mul continuousOn_id)

theorem HumanHyp.bddAbove (h : HumanHyp φ δ lam β) (a : ℝ) :
    BddAbove (humanObj φ β a '' Icc (1 - δ) (1 + lam)) :=
  (isCompact_Icc.image_of_continuousOn (h.obj_cont a)).bddAbove

/-- `M(a)` is attained. -/
theorem HumanHyp.exists_max (h : HumanHyp φ δ lam β) (a : ℝ) :
    ∃ x ∈ humanArgmax φ δ lam β a, humanM φ δ lam β a = humanObj φ β a x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 h.I_nonempty)
    (h.obj_cont a)
  refine ⟨x, ⟨hx, fun x' hx' => hmax hx'⟩, le_antisymm (csSup_le
    ((Set.nonempty_Icc.2 h.I_nonempty).image _) ?_) (le_csSup (h.bddAbove a) ⟨x, hx, rfl⟩)⟩
  rintro _ ⟨x', hx', rfl⟩
  exact hmax hx'

theorem HumanHyp.le_M (h : HumanHyp φ δ lam β) (a : ℝ) {x : ℝ}
    (hx : x ∈ Icc (1 - δ) (1 + lam)) : humanObj φ β a x ≤ humanM φ δ lam β a :=
  le_csSup (h.bddAbove a) ⟨x, hx, rfl⟩

/-- `T(a·k) = M(a)·k`: substitute `x = y/k`. -/
theorem humanT_linear (h : HumanHyp φ δ lam β) (a : ℝ) (k : PosR) :
    humanT φ δ lam β (fun y => a * y.1) k = humanM φ δ lam β a * k.1 := by
  have hk := k.2
  have hδ : 0 < 1 - δ := by linarith [h.δ_lt]
  have hval : ∀ y ∈ humanΓ δ lam k,
      k.1 * φ (y.1 / k.1) + β * (a * y.1) = k.1 * humanObj φ β a (y.1 / k.1) := fun y _ => by
    simp only [humanObj]; field_simp
  have hmem : ∀ y ∈ humanΓ δ lam k, y.1 / k.1 ∈ Icc (1 - δ) (1 + lam) := fun y hy =>
    ⟨(le_div_iff₀ hk).2 hy.1, (div_le_iff₀ hk).2 hy.2⟩
  have hub : ∀ z ∈ (fun y : PosR => k.1 * φ (y.1 / k.1) + β * (a * y.1)) '' humanΓ δ lam k,
      z ≤ humanM φ δ lam β a * k.1 := by
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    rw [hval y hy, mul_comm _ k.1]
    exact mul_le_mul_of_nonneg_left (h.le_M a (hmem y hy)) hk.le
  obtain ⟨x, hx, hM⟩ := h.exists_max a
  set y : PosR := ⟨k.1 * x, mul_pos hk (by linarith [hx.1.1])⟩
  have hy : y ∈ humanΓ δ lam k :=
    ⟨by simp only [y]; nlinarith [hx.1.1], by simp only [y]; nlinarith [hx.1.2]⟩
  refine le_antisymm (csSup_le ⟨_, y, hy, rfl⟩ hub) ?_
  refine le_trans ?_ (le_csSup ⟨_, hub⟩ ⟨y, hy, rfl⟩)
  simp only
  rw [hval y hy, hM]
  have : y.1 / k.1 = x := by simp only [y]; field_simp
  rw [this, mul_comm]

/-- **Exercise 5.7a.** `Tⁿv₀ = aₙk`. -/
theorem ex_5_7a_iterate (h : HumanHyp φ δ lam β) (n : ℕ) :
    (humanT φ δ lam β)^[n] (fun _ => 0) = fun k => humanA φ δ lam β n * k.1 := by
  induction n with
  | zero => funext k; simp [humanA]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext k
    rw [humanT_linear h]
    rfl

/-- **Exercise 5.7a.** `a₁ = max φ = φ(1 − δ) = 1`. -/
theorem ex_5_7a_one (h : HumanHyp φ δ lam β) : humanA φ δ lam β 1 = 1 := by
  change humanM φ δ lam β 0 = 1
  have hleft : (1 - δ) ∈ Icc (1 - δ) (1 + lam) := ⟨le_rfl, h.I_nonempty⟩
  refine le_antisymm (csSup_le ((Set.nonempty_Icc.2 h.I_nonempty).image _) ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    simp only [humanObj, mul_zero, zero_mul, add_zero]
    rw [← h.φ_left]
    exact h.φ_anti.antitoneOn hleft hx hx.1
  · have := h.le_M 0 hleft
    simpa [humanObj, h.φ_left] using this

/-- `M` is strictly increasing. -/
theorem humanM_strictMono (h : HumanHyp φ δ lam β) : StrictMono (humanM φ δ lam β) := by
  intro a a' haa'
  obtain ⟨x, hx, hM⟩ := h.exists_max a
  have hx0 : 0 < x := by linarith [hx.1.1, h.δ_lt]
  rw [hM]
  refine lt_of_lt_of_le ?_ (h.le_M a' hx.1)
  simp only [humanObj]
  have := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right haa' hx0) h.β_pos
  nlinarith

/-- **Exercise 5.7a.** `aₙ₊₁ > aₙ`. -/
theorem ex_5_7a_strictMono (h : HumanHyp φ δ lam β) : StrictMono (humanA φ δ lam β) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  induction n with
  | zero =>
    have := ex_5_7a_one h
    simp only [humanA] at this ⊢
    change (0 : ℝ) < humanM φ δ lam β 0
    rw [show humanM φ δ lam β 0 = humanA φ δ lam β 1 from rfl, ex_5_7a_one h]
    exact one_pos
  | succ n ih => exact humanM_strictMono h ih

theorem humanA_nonneg (h : HumanHyp φ δ lam β) (n : ℕ) : 0 ≤ humanA φ δ lam β n :=
  (ex_5_7a_strictMono h).monotone (Nat.zero_le n)

/-- `M(a) ≤ 1 + β(1 + λ)a` for `a ≥ 0`. -/
theorem humanM_le (h : HumanHyp φ δ lam β) {a : ℝ} (ha : 0 ≤ a) :
    humanM φ δ lam β a ≤ 1 + β * (1 + lam) * a := by
  obtain ⟨x, hx, hM⟩ := h.exists_max a
  rw [hM]
  have h1 : φ x ≤ 1 := by
    rw [← h.φ_left]; exact h.φ_anti.antitoneOn ⟨le_rfl, h.I_nonempty⟩ hx.1 hx.1.1
  have h2 : β * a * x ≤ β * a * (1 + lam) :=
    mul_le_mul_of_nonneg_left hx.1.2 (mul_nonneg h.β_pos.le ha)
  simp only [humanObj]
  linarith

/-- `M(a) ≥ β(1 + λ)a` (choose `x = 1 + λ`, where `φ = 0`). -/
theorem humanM_ge (h : HumanHyp φ δ lam β) (a : ℝ) : β * (1 + lam) * a ≤ humanM φ δ lam β a := by
  have := h.le_M a ⟨h.I_nonempty, le_rfl⟩
  simp only [humanObj, h.φ_right, zero_add] at this
  linarith

/-- The tangent at `1 + λ` lies above the concave `φ`: with left derivative `d` at `1 + λ`,
`φ(x) ≤ −d(1 + λ − x)` on `I`. -/
theorem slope_bound (h : HumanHyp φ δ lam β) {d : ℝ}
    (hd : HasDerivWithinAt φ d (Iio (1 + lam)) (1 + lam)) {x : ℝ}
    (hx : x ∈ Icc (1 - δ) (1 + lam)) : φ x ≤ -d * (1 + lam - x) := by
  set b := 1 + lam
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · rw [hxb, h.φ_right]; simp
  have hslope : Tendsto (slope φ b) (𝓝[<] b) (𝓝 d) := by
    have := hasDerivWithinAt_iff_tendsto_slope.1 hd
    rwa [sdiff_singleton_eq_self (show b ∉ Iio b from lt_irrefl b)] at this
  -- along `z ∈ (x, b)`: `slope(z, b)·(b − x) ≤ φ(b) − φ(x)`
  have hev : ∀ᶠ z in 𝓝[<] b, slope φ b z * (b - x) ≤ φ b - φ x := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hxb)] with z hz hzx
    have hz' : z < b := hz
    have hzx' : x < z := hzx
    have hzI : z ∈ Icc (1 - δ) (1 + lam) := ⟨hx.1.trans hzx'.le, hz'.le⟩
    have hadj := h.φ_concave.slope_anti_adjacent hx ⟨h.I_nonempty, le_rfl⟩ hzx' hz'
    rw [slope_def_field]
    have e1 : (φ z - φ b) / (z - b) = (φ b - φ z) / (b - z) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [e1]
    have hbz : 0 < b - z := by linarith
    have hzx0 : 0 < z - x := by linarith
    set s2 := (φ b - φ z) / (b - z)
    set s1 := (φ z - φ x) / (z - x)
    have e2 : φ b - φ z = s2 * (b - z) := by simp only [s2]; field_simp
    have e3 : φ z - φ x = s1 * (z - x) := by simp only [s1]; field_simp
    nlinarith
  have hlim := le_of_tendsto (hslope.mul_const (b - x)) hev
  rw [h.φ_right] at hlim
  linarith

/-- **Exercise 5.7a.** `(aₙ)` is bounded iff `β(1 + λ) ≤ 1`, i.e. `λ ≤ r` for `β = 1/(1 + r)`
(the manual's `λ < r` misses the boundary case). `φ` has a left derivative at `1 + λ`, as it does
when `φ` is continuously differentiable on `I`. -/
theorem ex_5_7a_bounded_iff (h : HumanHyp φ δ lam β) {d : ℝ}
    (hd : HasDerivWithinAt φ d (Iio (1 + lam)) (1 + lam)) :
    BddAbove (range (humanA φ δ lam β)) ↔ β * (1 + lam) ≤ 1 := by
  constructor
  · -- if `β(1 + λ) > 1`, then `aₙ₊₁ ≥ β(1 + λ)aₙ` and `a₁ = 1` force `aₙ → ∞`
    intro hb
    by_contra hgt
    push Not at hgt
    have hge : ∀ n, (β * (1 + lam)) ^ n ≤ humanA φ δ lam β (n + 1) := fun n => by
      induction n with
      | zero => simp [ex_5_7a_one h]
      | succ n ih =>
        rw [pow_succ]
        calc (β * (1 + lam)) ^ n * (β * (1 + lam)) ≤ humanA φ δ lam β (n + 1) * (β * (1 + lam)) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
          _ = β * (1 + lam) * humanA φ δ lam β (n + 1) := by ring
          _ ≤ humanA φ δ lam β (n + 2) := humanM_ge h _
    obtain ⟨B, hB⟩ := hb
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop B |>.exists
    exact absurd ((hge n).trans (hB ⟨n + 1, rfl⟩)) (not_le.2 hn)
  · intro hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- `β(1 + λ) = 1`: `a* = −d(1 + λ)` is a fixed point bound
      set s := -d
      have hs : ∀ x ∈ Icc (1 - δ) (1 + lam), φ x ≤ s * (1 + lam - x) := fun x hx =>
        slope_bound h hd hx
      have hs0 : 0 ≤ s := by
        have := hs (1 - δ) ⟨le_rfl, h.I_nonempty⟩
        rw [h.φ_left] at this
        nlinarith [h.δ_pos, h.lam_pos]
      have hM : humanM φ δ lam β (s * (1 + lam)) ≤ s * (1 + lam) := by
        obtain ⟨x, hx, hMx⟩ := h.exists_max (s * (1 + lam))
        rw [hMx]
        have := hs x hx.1
        simp only [humanObj]
        have e : β * (s * (1 + lam)) * x = s * x * (β * (1 + lam)) := by ring
        rw [e, heq]
        linarith
      refine ⟨s * (1 + lam), ?_⟩
      rintro _ ⟨n, rfl⟩
      induction n with
      | zero => exact mul_nonneg hs0 (by linarith [h.lam_pos])
      | succ n ih => exact ((humanM_strictMono h).monotone ih).trans hM
    · -- `β(1 + λ) < 1`: `aₙ ≤ 1/(1 − β(1 + λ))`
      refine ⟨1 / (1 - β * (1 + lam)), ?_⟩
      rintro _ ⟨n, rfl⟩
      have h1 : 0 < 1 - β * (1 + lam) := by linarith
      induction n with
      | zero => exact (div_pos one_pos h1).le
      | succ n ih =>
        have := humanM_le h (humanA_nonneg h n)
        change humanM φ δ lam β (humanA φ δ lam β n) ≤ 1 / (1 - β * (1 + lam))
        rw [le_div_iff₀ h1] at ih ⊢
        have hβl : 0 ≤ β * (1 + lam) := by nlinarith [h.β_pos, h.lam_pos]
        nlinarith [humanA_nonneg h n]

/-! ### Exercise 5.7b: the life-cycle profile -/

/-- **Monotone comparative statics.** A larger continuation slope `a' > a` calls for a weakly
larger growth factor. -/
theorem growth_factor_mono (h : HumanHyp φ δ lam β) {a a' x x' : ℝ} (haa' : a < a')
    (hx : x ∈ humanArgmax φ δ lam β a) (hx' : x' ∈ humanArgmax φ δ lam β a') : x ≤ x' := by
  by_contra hlt
  push Not at hlt
  have h1 := hx.2 x' hx'.1
  have h2 := hx'.2 x hx.1
  simp only [humanObj] at h1 h2
  have : 0 < β * (a' - a) * (x - x') := mul_pos (mul_pos h.β_pos (by linarith)) (by linarith)
  nlinarith

/-- **Exercise 5.7b.** In the last working period (`a₀ = 0`) the worker does not invest:
the only optimal growth factor is `1 − δ`, and he works full time. -/
theorem ex_5_7b_last (h : HumanHyp φ δ lam β) {x : ℝ}
    (hx : x ∈ humanArgmax φ δ lam β (humanA φ δ lam β 0)) : x = 1 - δ := by
  by_contra hne
  have hlt : 1 - δ < x := lt_of_le_of_ne hx.1.1 (Ne.symm hne)
  have h1 := hx.2 (1 - δ) ⟨le_rfl, h.I_nonempty⟩
  have h2 := h.φ_anti ⟨le_rfl, h.I_nonempty⟩ hx.1 hlt
  simp only [humanObj, humanA, mul_zero, zero_mul, add_zero] at h1
  linarith

/-- **Exercise 5.7b.** Let `xₙ` be optimal with `n + 1` periods left. Growth factors fall and
the working share `φ(xₙ)` rises as the worker ages (as `n` falls). -/
theorem ex_5_7b_profile (h : HumanHyp φ δ lam β) {x : ℕ → ℝ}
    (hx : ∀ n, x n ∈ humanArgmax φ δ lam β (humanA φ δ lam β n)) :
    Monotone x ∧ Antitone fun n => φ (x n) := by
  have hmono : Monotone x := monotone_nat_of_le_succ fun n =>
    growth_factor_mono h (ex_5_7a_strictMono h (Nat.lt_succ_self n)) (hx n) (hx (n + 1))
  exact ⟨hmono, fun m n hmn => h.φ_anti.antitoneOn (hx m).1 (hx n).1 (hmono hmn)⟩

/-- **Exercise 5.7b.** If minimal accumulation `1 − δ` is optimal with `n + 1` periods left, it
is optimal with fewer; if maximal accumulation `1 + λ` is optimal with `n + 1` periods left, it
is optimal with more. -/
theorem ex_5_7b_corners (h : HumanHyp φ δ lam β) {x : ℕ → ℝ}
    (hx : ∀ n, x n ∈ humanArgmax φ δ lam β (humanA φ δ lam β n)) {m n : ℕ} (hmn : m ≤ n) :
    (x n = 1 - δ → x m = 1 - δ) ∧ (x m = 1 + lam → x n = 1 + lam) := by
  have hmono := (ex_5_7b_profile h hx).1 hmn
  refine ⟨fun hn => le_antisymm (hn ▸ hmono) (hx m).1.1,
    fun hm => le_antisymm (hx n).1.2 (hm ▸ hmono)⟩

/-- **Exercise 5.7b.** Human capital is single-peaked over the life cycle: with growth factors
`g` falling with age, `k_{t+1} = g_t k_t` and `k > 0`, once human capital falls it keeps
falling. -/
theorem ex_5_7b_single_peaked {g k : ℕ → ℝ} (hg : Antitone g) (hk : ∀ t, k (t + 1) = g t * k t)
    (hpos : ∀ t, 0 < k t) {t : ℕ} (hfall : k (t + 1) ≤ k t) {s : ℕ} (hts : t ≤ s) :
    k (s + 1) ≤ k s := by
  have hgt : g t ≤ 1 := by
    rw [hk t] at hfall
    by_contra hlt
    push Not at hlt
    nlinarith [hpos t]
  have hgs := (hg hts).trans hgt
  rw [hk s]
  nlinarith [hpos s]

end StokeyLucasPrescott.DeterministicApplications

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.DeterministicApplications.addIso
#print axioms StokeyLucasPrescott.DeterministicApplications.addIso_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.mulIso
#print axioms StokeyLucasPrescott.DeterministicApplications.mulIso_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.add_mul_biSup
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_add_mul
#print axioms StokeyLucasPrescott.DeterministicApplications.coe_mul_add
#print axioms StokeyLucasPrescott.DeterministicApplications.le_of_le_add_limsup
#print axioms StokeyLucasPrescott.DeterministicApplications.le_of_add_le_liminf
#print axioms StokeyLucasPrescott.DeterministicApplications.le_of_forall_coe_lt_le
#print axioms StokeyLucasPrescott.DeterministicApplications.eq_biSup_iff
#print axioms StokeyLucasPrescott.DeterministicApplications.Feasible
#print axioms StokeyLucasPrescott.DeterministicApplications.partialSum
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption41
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption42
#print axioms StokeyLucasPrescott.DeterministicApplications.total
#print axioms StokeyLucasPrescott.DeterministicApplications.vstar
#print axioms StokeyLucasPrescott.DeterministicApplications.SatisfiesFE
#print axioms StokeyLucasPrescott.DeterministicApplications.tendsto_total
#print axioms StokeyLucasPrescott.DeterministicApplications.tail
#print axioms StokeyLucasPrescott.DeterministicApplications.tail_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.tail_tail
#print axioms StokeyLucasPrescott.DeterministicApplications.consPlan
#print axioms StokeyLucasPrescott.DeterministicApplications.consPlan_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.tail_consPlan
#print axioms StokeyLucasPrescott.DeterministicApplications.feasible_nonempty
#print axioms StokeyLucasPrescott.DeterministicApplications.partialSum_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.partialSum_succ'
#print axioms StokeyLucasPrescott.DeterministicApplications.lemma_4_1
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_2
#print axioms StokeyLucasPrescott.DeterministicApplications.total_le_of_FE
#print axioms StokeyLucasPrescott.DeterministicApplications.div_lt_of_lt_add_mul
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_3a
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_3
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_3b
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_4
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_4_beta_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_5
#print axioms StokeyLucasPrescott.DeterministicApplications.Gstar
#print axioms StokeyLucasPrescott.DeterministicApplications.optimal_generated_by_Gstar
#print axioms StokeyLucasPrescott.DeterministicApplications.generated_by_Gstar_optimal
#print axioms StokeyLucasPrescott.DeterministicApplications.tendsto_of_summable_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.tendsto_of_summable_neg
#print axioms StokeyLucasPrescott.DeterministicApplications.assumption42_of_summable_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.assumption42_of_summable_neg
#print axioms StokeyLucasPrescott.DeterministicApplications.summable_max_of_le_geometric
#print axioms StokeyLucasPrescott.DeterministicApplications.assumption42_of_bddAbove
#print axioms StokeyLucasPrescott.DeterministicApplications.assumption42_of_bddBelow
#print axioms StokeyLucasPrescott.DeterministicApplications.assumption42_of_geometric
#print axioms StokeyLucasPrescott.DeterministicApplications.Orthant
#print axioms StokeyLucasPrescott.DeterministicApplications.orthCombo
#print axioms StokeyLucasPrescott.DeterministicApplications.orthZero
#print axioms StokeyLucasPrescott.DeterministicApplications.orthOne
#print axioms StokeyLucasPrescott.DeterministicApplications.norm_le_geometric
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_2a
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_2b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_1a
#print axioms StokeyLucasPrescott.DeterministicApplications.consSet
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_1b
#print axioms StokeyLucasPrescott.DeterministicApplications.IsContraction
#print axioms StokeyLucasPrescott.DeterministicApplications.IsContraction.uniformContinuous
#print axioms StokeyLucasPrescott.DeterministicApplications.dist_iterate_succ_le
#print axioms StokeyLucasPrescott.DeterministicApplications.dist_iterate_le
#print axioms StokeyLucasPrescott.DeterministicApplications.cauchySeq_iterate
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_3_2
#print axioms StokeyLucasPrescott.DeterministicApplications.dist_fixedPoint_le
#print axioms StokeyLucasPrescott.DeterministicApplications.corollary_1
#print axioms StokeyLucasPrescott.DeterministicApplications.corollary_2
#print axioms StokeyLucasPrescott.DeterministicApplications.IsLHC
#print axioms StokeyLucasPrescott.DeterministicApplications.IsUHC
#print axioms StokeyLucasPrescott.DeterministicApplications.graph
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousAt_of_isUHC_singleton
#print axioms StokeyLucasPrescott.DeterministicApplications.isCompact_graph
#print axioms StokeyLucasPrescott.DeterministicApplications.maxValue
#print axioms StokeyLucasPrescott.DeterministicApplications.argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousOn_section
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.le_maxValue
#print axioms StokeyLucasPrescott.DeterministicApplications.tendsto_f_graph
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_3_6
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.nonempty
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.compact
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.lhc
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.uhc
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.cont
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.unique
#print axioms StokeyLucasPrescott.DeterministicApplications.argmaxFn
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.argmaxFn_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.argmax_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.lt_of_ne
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.continuous_argmaxFn
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.lemma_3_7
#print axioms StokeyLucasPrescott.DeterministicApplications.UniqueArgmax.lemma_3_7_uniform
#print axioms StokeyLucasPrescott.DeterministicApplications.shortfall_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_3_8
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_3_8_uniform
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption43
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption43.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption43.nonempty
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption43.compact
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption43.lhc
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption43.uhc
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption44
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption44.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption44.cont
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption44.bdd
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption44.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption44.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.obj
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousOn_obj
#print axioms StokeyLucasPrescott.DeterministicApplications.bound_maxValue
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_bellman_argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_add_const
#print axioms StokeyLucasPrescott.DeterministicApplications.blackwell
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_6
#print axioms StokeyLucasPrescott.DeterministicApplications.curryF
#print axioms StokeyLucasPrescott.DeterministicApplications.assumption42_of_44
#print axioms StokeyLucasPrescott.DeterministicApplications.satisfiesFE_of_fixed
#print axioms StokeyLucasPrescott.DeterministicApplications.tendsto_bounded_discount
#print axioms StokeyLucasPrescott.DeterministicApplications.fixedPoint_eq_vstar
#print axioms StokeyLucasPrescott.DeterministicApplications.policy_plan_optimal
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_7
#print axioms StokeyLucasPrescott.DeterministicApplications.cmb
#print axioms StokeyLucasPrescott.DeterministicApplications.cmb_self
#print axioms StokeyLucasPrescott.DeterministicApplications.IsConcaveS
#print axioms StokeyLucasPrescott.DeterministicApplications.IsStrictConcaveS
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption47
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption48
#print axioms StokeyLucasPrescott.DeterministicApplications.isClosed_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_maps_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.argmax_unique_of_strictConcave
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_8
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_9
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_10
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_5
#print axioms StokeyLucasPrescott.DeterministicApplications.dual_apply_eq_sum
#print axioms StokeyLucasPrescott.DeterministicApplications.vertex
#print axioms StokeyLucasPrescott.DeterministicApplications.no_separation
#print axioms StokeyLucasPrescott.DeterministicApplications.eventually_mem_of_mem_interior
#print axioms StokeyLucasPrescott.DeterministicApplications.liftS
#print axioms StokeyLucasPrescott.DeterministicApplications.liftS_of_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.IsStrictConcaveS.isConcaveS
#print axioms StokeyLucasPrescott.DeterministicApplications.concaveOn_liftS
#print axioms StokeyLucasPrescott.DeterministicApplications.convex_image_Γ
#print axioms StokeyLucasPrescott.DeterministicApplications.eventually_mem_Γ
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_11
#print axioms StokeyLucasPrescott.DeterministicApplications.IsCone
#print axioms StokeyLucasPrescott.DeterministicApplications.csmul
#print axioms StokeyLucasPrescott.DeterministicApplications.InH
#print axioms StokeyLucasPrescott.DeterministicApplications.hnorm
#print axioms StokeyLucasPrescott.DeterministicApplications.hnorm_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.bddAbove_sphere
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_le_hnorm
#print axioms StokeyLucasPrescott.DeterministicApplications.hnorm_le
#print axioms StokeyLucasPrescott.DeterministicApplications.inH_sub
#print axioms StokeyLucasPrescott.DeterministicApplications.inH_add
#print axioms StokeyLucasPrescott.DeterministicApplications.inH_smul
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_7a_norm
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_7a_complete
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_12
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.convex
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.nonempty
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.compact
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.lhc
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.uhc
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.cone
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.α_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.αβ_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption410.growth
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411.cont
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411.hom
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411.B_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.Assumption411.bdd
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_6a
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_term_le
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_6b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_6c
#print axioms StokeyLucasPrescott.DeterministicApplications.crs
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousOn_obj'
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_crs_argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.eq_zero_of_mem_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_7b
#print axioms StokeyLucasPrescott.DeterministicApplications.crs_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.crs_disc
#print axioms StokeyLucasPrescott.DeterministicApplications.crs_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.hnorm_sub_le
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_13
#print axioms StokeyLucasPrescott.DeterministicApplications.satisfiesFE_crs
#print axioms StokeyLucasPrescott.DeterministicApplications.crs_fixed_eq_vstar
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_4_6c_hom
#print axioms StokeyLucasPrescott.DeterministicApplications.opT
#print axioms StokeyLucasPrescott.DeterministicApplications.satisfiesFE_iff_opT
#print axioms StokeyLucasPrescott.DeterministicApplications.opT_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.iterate_antitone
#print axioms StokeyLucasPrescott.DeterministicApplications.limitFn
#print axioms StokeyLucasPrescott.DeterministicApplications.tendsto_iterate
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_14
#print axioms StokeyLucasPrescott.DeterministicApplications.concave_le_fderiv
#print axioms StokeyLucasPrescott.DeterministicApplications.Fx
#print axioms StokeyLucasPrescott.DeterministicApplications.Fy
#print axioms StokeyLucasPrescott.DeterministicApplications.apply_eq_Fx_add_Fy
#print axioms StokeyLucasPrescott.DeterministicApplications.euler_telescope
#print axioms StokeyLucasPrescott.DeterministicApplications.le_of_le_add_tendsto_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.euler_sufficient
#print axioms StokeyLucasPrescott.DeterministicApplications.theorem_4_15
#print axioms StokeyLucasPrescott.DeterministicApplications.euler_of_envelope
#print axioms StokeyLucasPrescott.DeterministicApplications.PosR
#print axioms StokeyLucasPrescott.DeterministicApplications.logΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.logF
#print axioms StokeyLucasPrescott.DeterministicApplications.coefB
#print axioms StokeyLucasPrescott.DeterministicApplications.coefC
#print axioms StokeyLucasPrescott.DeterministicApplications.affineLog
#print axioms StokeyLucasPrescott.DeterministicApplications.logPolicy
#print axioms StokeyLucasPrescott.DeterministicApplications.αβ_lt_one
#print axioms StokeyLucasPrescott.DeterministicApplications.coefB_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.coefC_neg
#print axioms StokeyLucasPrescott.DeterministicApplications.logPolicy_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.log_objective_le
#print axioms StokeyLucasPrescott.DeterministicApplications.log_opT_affine
#print axioms StokeyLucasPrescott.DeterministicApplications.log_iterate
#print axioms StokeyLucasPrescott.DeterministicApplications.log_assumption41
#print axioms StokeyLucasPrescott.DeterministicApplications.log_capital_le
#print axioms StokeyLucasPrescott.DeterministicApplications.logF_le
#print axioms StokeyLucasPrescott.DeterministicApplications.log_assumption42
#print axioms StokeyLucasPrescott.DeterministicApplications.log_vstar
#print axioms StokeyLucasPrescott.DeterministicApplications.log_policy_optimal
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.U_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.U_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.f_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.f_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.xbar_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.f_maintain
#print axioms StokeyLucasPrescott.DeterministicApplications.GrowthHyp.f_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.growthΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.growthF
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_f_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_growth_f
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_assumption43
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_assumption44
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_a45
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_a46
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_assumption41
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_assumption42
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_1ab
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_a47
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_a48
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_1c
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_1c_weak_counterexample
#print axioms StokeyLucasPrescott.DeterministicApplications.growthF_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_concave_growth
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.chord_step
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_strictConcave
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_1c_weak
#print axioms StokeyLucasPrescott.DeterministicApplications.liftR
#print axioms StokeyLucasPrescott.DeterministicApplications.liftR_of_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.concaveOn_liftR
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_1d
#print axioms StokeyLucasPrescott.DeterministicApplications.eventually_slope_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.slope_le_chord
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_1d_interior
#print axioms StokeyLucasPrescott.DeterministicApplications.concave_exchange
#print axioms StokeyLucasPrescott.DeterministicApplications.growthF_increasingDiff
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_sub_monotone
#print axioms StokeyLucasPrescott.DeterministicApplications.discounted_value_monotone
#print axioms StokeyLucasPrescott.DeterministicApplications.policy_le_of_discount_le
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_1e
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2a_technology
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2a_not_T2
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2a
#print axioms StokeyLucasPrescott.DeterministicApplications.cake_path_le
#print axioms StokeyLucasPrescott.DeterministicApplications.cake_logΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.cake_logF
#print axioms StokeyLucasPrescott.DeterministicApplications.cake_policy
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2b_policy
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2c
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2c_interior
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_2c_deriv
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_3a
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_3a_strict
#print axioms StokeyLucasPrescott.DeterministicApplications.kstar_le_xbar
#print axioms StokeyLucasPrescott.DeterministicApplications.kstar_le_f
#print axioms StokeyLucasPrescott.DeterministicApplications.linear_value_le
#print axioms StokeyLucasPrescott.DeterministicApplications.linear_value_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_3b
#print axioms StokeyLucasPrescott.DeterministicApplications.linearPolicy
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_3c
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_3a_corner
#print axioms StokeyLucasPrescott.DeterministicApplications.renormU
#print axioms StokeyLucasPrescott.DeterministicApplications.renormF
#print axioms StokeyLucasPrescott.DeterministicApplications.renorm_budget
#print axioms StokeyLucasPrescott.DeterministicApplications.renorm_capital
#print axioms StokeyLucasPrescott.DeterministicApplications.renorm_power_utility
#print axioms StokeyLucasPrescott.DeterministicApplications.renorm_log_utility
#print axioms StokeyLucasPrescott.DeterministicApplications.renorm_consumption
#print axioms StokeyLucasPrescott.DeterministicApplications.renormU_hyp
#print axioms StokeyLucasPrescott.DeterministicApplications.renormU_strictConcave
#print axioms StokeyLucasPrescott.DeterministicApplications.renormF_hyp
#print axioms StokeyLucasPrescott.DeterministicApplications.renormF_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_4
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_4_analysis
#print axioms StokeyLucasPrescott.DeterministicApplications.power_utility
#print axioms StokeyLucasPrescott.DeterministicApplications.cutPayoff
#print axioms StokeyLucasPrescott.DeterministicApplications.stopSet
#print axioms StokeyLucasPrescott.DeterministicApplications.cutPayoff_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.first_entry_optimal
#print axioms StokeyLucasPrescott.DeterministicApplications.never_entry_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.ratio_invariant
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_5a
#print axioms StokeyLucasPrescott.DeterministicApplications.treeValue
#print axioms StokeyLucasPrescott.DeterministicApplications.treeValue_fe
#print axioms StokeyLucasPrescott.DeterministicApplications.le_treeValue
#print axioms StokeyLucasPrescott.DeterministicApplications.rotationValue
#print axioms StokeyLucasPrescott.DeterministicApplications.faustmann_identity
#print axioms StokeyLucasPrescott.DeterministicApplications.faustmann_fe
#print axioms StokeyLucasPrescott.DeterministicApplications.antitone_invariant
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_5b
#print axioms StokeyLucasPrescott.DeterministicApplications.ExpStock
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.qbar_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.R_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.R_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.γ_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.γ_anti
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.γ_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDHyp.profit
#print axioms StokeyLucasPrescott.DeterministicApplications.lbdΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.lbdF
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_γ_le
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_assumption43
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_assumption44
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_exists
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_not_a46
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_not_a47
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_argmax_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_policy_exceeds
#print axioms StokeyLucasPrescott.DeterministicApplications.unique_interior_max
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.qbar_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ_deriv
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ'_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ_anti
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.mr_anti
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ_qbar
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.γ_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.γ_anti
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.γ_convex
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.γ_lim
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.c_lt_γ
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.c_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.φ'_nonpos
#print axioms StokeyLucasPrescott.DeterministicApplications.LBDModel.exists_small
#print axioms StokeyLucasPrescott.DeterministicApplications.monopoly_hyp
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_6a
#print axioms StokeyLucasPrescott.DeterministicApplications.surplus
#print axioms StokeyLucasPrescott.DeterministicApplications.surplus_hasDerivAt
#print axioms StokeyLucasPrescott.DeterministicApplications.surplus_continuousOn
#print axioms StokeyLucasPrescott.DeterministicApplications.surplus_continuousOn_Ici
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_6b_surplus
#print axioms StokeyLucasPrescott.DeterministicApplications.planner_hyp
#print axioms StokeyLucasPrescott.DeterministicApplications.lbd_value_le
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_6b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_6c
#print axioms StokeyLucasPrescott.DeterministicApplications.competitive_output_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.competitive_path
#print axioms StokeyLucasPrescott.DeterministicApplications.resourceF
#print axioms StokeyLucasPrescott.DeterministicApplications.resource_hyp
#print axioms StokeyLucasPrescott.DeterministicApplications.resource_assumption44
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_6d
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.δ_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.δ_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.lam_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.φ_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.φ_anti
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.φ_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.φ_left
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.φ_right
#print axioms StokeyLucasPrescott.DeterministicApplications.humanΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.humanT
#print axioms StokeyLucasPrescott.DeterministicApplications.humanObj
#print axioms StokeyLucasPrescott.DeterministicApplications.humanM
#print axioms StokeyLucasPrescott.DeterministicApplications.humanA
#print axioms StokeyLucasPrescott.DeterministicApplications.humanArgmax
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.I_nonempty
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.obj_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.bddAbove
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.exists_max
#print axioms StokeyLucasPrescott.DeterministicApplications.HumanHyp.le_M
#print axioms StokeyLucasPrescott.DeterministicApplications.humanT_linear
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7a_iterate
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7a_one
#print axioms StokeyLucasPrescott.DeterministicApplications.humanM_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7a_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.humanA_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.humanM_le
#print axioms StokeyLucasPrescott.DeterministicApplications.humanM_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.slope_bound
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7a_bounded_iff
#print axioms StokeyLucasPrescott.DeterministicApplications.growth_factor_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7b_last
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7b_profile
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7b_corners
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_7b_single_peaked
