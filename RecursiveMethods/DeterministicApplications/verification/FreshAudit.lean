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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The functional equation with a weighted bound

Several problems of Chapter 5 (Exercise 5.8) have returns that grow with the state, so `T` is
not a self-map of the bounded functions. With a positive continuous weight `w` such that
`|F(x, y)| ≤ Bw(x)` and `βw(y) ≤ ρw(x)` for `y ∈ Γ(x)` and some `ρ < 1`, the functional equation
has exactly one continuous solution with `|v| ≤ Cw`: apply the contraction mapping theorem to
`u = v/w` in `C(X)`, where `T` becomes
`(T̃u)(x) = max_{y ∈ Γ(x)} [F(x, y) + βw(y)u(y)]/w(x)`, a contraction of modulus `ρ` (Blackwell's
conditions).

* `WeightedHyp`: the hypotheses; `wbellman`: the operator `T̃`; `wbellman_contraction`.
* `SolvesFE`: `v` satisfies `v(x) = max_{y ∈ Γ(x)} [F(x, y) + βv(y)]`, with the maximum
  attained.
* `weighted_exists_unique`: exactly one continuous `v` with `|v| ≤ Cw` solves the functional
  equation.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {X : Type*} [MetricSpace X] {Γ : X → Set X} {F : X × X → ℝ} {w : X → ℝ} {β ρ : ℝ}

/-- The hypotheses for the weighted functional equation. -/
structure WeightedHyp (Γ : X → Set X) (F : X × X → ℝ) (w : X → ℝ) (β ρ : ℝ) : Prop where
  h43 : Assumption43 Γ
  cont : ContinuousOn F (graph Γ)
  w_cont : Continuous w
  w_pos : ∀ x, 0 < w x
  bdd : ∃ B, ∀ p ∈ graph Γ, |F p| ≤ B * w p.1
  β_pos : 0 < β
  ρ_lt : ρ < 1
  growth : ∀ x, ∀ y ∈ Γ x, β * w y ≤ ρ * w x

/-- `v` solves the functional equation, with the maximum attained. -/
def SolvesFE (Γ : X → Set X) (F : X × X → ℝ) (β : ℝ) (v : X → ℝ) : Prop :=
  ∀ x, (∃ y ∈ Γ x, v x = F (x, y) + β * v y) ∧ ∀ y ∈ Γ x, F (x, y) + β * v y ≤ v x

/-- The scaled objective `[F(x, y) + βw(y)u(y)]/w(x)`. -/
noncomputable def wobj (F : X × X → ℝ) (w : X → ℝ) (β : ℝ) (u : X → ℝ) (p : X × X) : ℝ :=
  (F p + β * (w p.2 * u p.2)) / w p.1

theorem WeightedHyp.ρ_pos (hW : WeightedHyp Γ F w β ρ) [Nonempty X] : 0 < ρ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y, hy⟩ := hW.h43.nonempty x
  have := hW.growth x y hy
  have h1 := mul_pos hW.β_pos (hW.w_pos y)
  by_contra hρ
  push Not at hρ
  nlinarith [hW.w_pos x]

theorem continuousOn_wobj (hW : WeightedHyp Γ F w β ρ) {u : X → ℝ} (hu : Continuous u) :
    ContinuousOn (wobj F w β u) (graph Γ) :=
  (hW.cont.add (continuous_const.mul ((hW.w_cont.comp continuous_snd).mul
    (hu.comp continuous_snd))).continuousOn).div
    (hW.w_cont.comp continuous_fst).continuousOn fun p _ => (hW.w_pos p.1).ne'

/-- The bound `|[F(x, y) + βw(y)u(y)]/w(x)| ≤ B + ρ‖u‖` on the graph. -/
theorem abs_wobj_le (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) {p : X × X} (hp : p ∈ graph Γ) :
    |wobj F w β u p| ≤ hW.bdd.choose + ρ * ‖u‖ := by
  have hw := hW.w_pos p.1
  have hwy := hW.w_pos p.2
  rw [wobj, abs_div, abs_of_pos hw, div_le_iff₀ hw]
  have h1 := hW.bdd.choose_spec p hp
  have hu := u.norm_coe_le_norm p.2
  rw [Real.norm_eq_abs] at hu
  have h2 : |β * (w p.2 * u p.2)| ≤ ρ * w p.1 * ‖u‖ := by
    rw [abs_mul, abs_mul, abs_of_pos hW.β_pos, abs_of_pos hwy]
    calc β * (w p.2 * |u p.2|) = β * w p.2 * |u p.2| := by ring
      _ ≤ ρ * w p.1 * ‖u‖ := mul_le_mul (hW.growth p.1 p.2 hp) hu (abs_nonneg _)
          (by nlinarith [hW.growth p.1 p.2 hp, mul_pos hW.β_pos hwy])
  calc |F p + β * (w p.2 * u p.2)| ≤ |F p| + |β * (w p.2 * u p.2)| := abs_add_le _ _
    _ ≤ hW.bdd.choose * w p.1 + ρ * w p.1 * ‖u‖ := add_le_add h1 h2
    _ = (hW.bdd.choose + ρ * ‖u‖) * w p.1 := by ring

theorem bound_wmaxValue (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) (x : X) :
    ‖maxValue (wobj F w β u) Γ x‖ ≤ hW.bdd.choose + ρ * ‖u‖ := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax (continuousOn_wobj hW u.continuous)
    (hW.h43.compact x) (hW.h43.nonempty x)
  rw [← hval, Real.norm_eq_abs]
  exact abs_wobj_le hW u hy

/-- The operator `(T̃u)(x) = max_{y ∈ Γ(x)} [F(x, y) + βw(y)u(y)]/w(x)` on `C(X)`. -/
noncomputable def wbellman (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => maxValue (wobj F w β u) Γ x)
    (theorem_3_6 (continuousOn_wobj hW u.continuous) hW.h43.compact hW.h43.lhc hW.h43.uhc).1
    (hW.bdd.choose + ρ * ‖u‖) (bound_wmaxValue hW u)

theorem exists_wbellman_argmax (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) (x : X) :
    ∃ y ∈ Γ x, wbellman hW u x = wobj F w β u (x, y) ∧
      ∀ z ∈ Γ x, wobj F w β u (x, z) ≤ wbellman hW u x := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_wobj hW u.continuous)
    (hW.h43.compact x) (hW.h43.nonempty x)
  exact ⟨y, hy, hval.symm, fun z hz => (hmax z hz).trans_eq hval⟩

/-- `T̃` is a contraction of modulus `ρ`. -/
theorem wbellman_contraction [Nonempty X] (hW : WeightedHyp Γ F w β ρ) :
    IsContraction (wbellman hW) ρ := by
  refine ⟨hW.ρ_pos, hW.ρ_lt, blackwell hW.ρ_pos.le (fun f g hfg x => ?_) (fun f a ha x => ?_)⟩
  · obtain ⟨y, hy, hval, -⟩ := exists_wbellman_argmax hW f x
    obtain ⟨-, -, -, hmax⟩ := exists_wbellman_argmax hW g x
    change wbellman hW f x ≤ wbellman hW g x
    rw [hval]
    refine le_trans ?_ (hmax y hy)
    simp only [wobj]
    refine div_le_div_of_nonneg_right ?_ (hW.w_pos x).le
    have := mul_le_mul_of_nonneg_left (show f y ≤ g y from hfg y) (hW.w_pos y).le
    nlinarith [hW.β_pos]
  · obtain ⟨y, hy, hval, -⟩ := exists_wbellman_argmax hW (f + const X a) x
    obtain ⟨-, -, -, hmax⟩ := exists_wbellman_argmax hW f x
    change wbellman hW (f + const X a) x ≤ (wbellman hW f + const X (ρ * a)) x
    rw [hval, BoundedContinuousFunction.add_apply, const_apply]
    have h1 := hmax y hy
    have hgr := hW.growth x y hy
    have hw := hW.w_pos x
    simp only [wobj, BoundedContinuousFunction.add_apply, const_apply] at h1 ⊢
    have e : (F (x, y) + β * (w y * (f y + a))) / w x =
        (F (x, y) + β * (w y * f y)) / w x + β * w y * a / w x := by
      field_simp; ring
    rw [e]
    have h2 : β * w y * a / w x ≤ ρ * a := by
      rw [div_le_iff₀ hw]; nlinarith
    linarith

/-- `u` is a fixed point of `T̃` iff `wu` solves the functional equation. -/
theorem solvesFE_iff (hW : WeightedHyp Γ F w β ρ) (u : X →ᵇ ℝ) :
    wbellman hW u = u ↔ SolvesFE Γ F β fun x => w x * u x := by
  constructor
  · intro hu x
    obtain ⟨y, hy, hval, hmax⟩ := exists_wbellman_argmax hW u x
    rw [hu] at hval hmax
    have hw := hW.w_pos x
    refine ⟨⟨y, hy, ?_⟩, fun z hz => ?_⟩
    · change w x * u x = F (x, y) + β * (w y * u y)
      rw [hval, wobj]; field_simp
    · have := hmax z hz
      rw [wobj, div_le_iff₀ hw] at this
      change F (x, z) + β * (w z * u z) ≤ w x * u x
      linarith
  · intro hv
    ext x
    have hw := hW.w_pos x
    obtain ⟨⟨y, hy, hval⟩, hmax⟩ := hv x
    beta_reduce at hval hmax
    refine le_antisymm ?_ ?_
    · obtain ⟨z, hz, hzval, -⟩ := exists_wbellman_argmax hW u x
      rw [hzval, wobj, div_le_iff₀ hw]
      have := hmax z hz
      linarith
    · obtain ⟨-, -, -, hle⟩ := exists_wbellman_argmax hW u x
      refine le_trans ?_ (hle y hy)
      rw [wobj, le_div_iff₀ hw]
      linarith

/-- **The weighted functional equation.** Exactly one continuous `v` with `|v| ≤ Cw` for some
`C` solves the functional equation. -/
theorem weighted_exists_unique [Nonempty X] (hW : WeightedHyp Γ F w β ρ) :
    ∃ v : X → ℝ, SolvesFE Γ F β v ∧ Continuous v ∧ (∃ C, ∀ x, |v x| ≤ C * w x) ∧
      ∀ v' : X → ℝ, SolvesFE Γ F β v' → Continuous v' → (∃ C, ∀ x, |v' x| ≤ C * w x) →
        v' = v := by
  obtain ⟨u, hu, huniq, -⟩ := theorem_3_2 (wbellman_contraction hW)
  refine ⟨fun x => w x * u x, (solvesFE_iff hW u).1 hu, hW.w_cont.mul u.continuous,
    ⟨‖u‖, fun x => ?_⟩, fun v' hv' hc' ⟨C, hC⟩ => ?_⟩
  · rw [abs_mul, abs_of_pos (hW.w_pos x), mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using u.norm_coe_le_norm x)
      (hW.w_pos x).le
  · -- `u' = v'/w` is a bounded continuous fixed point of `T̃`
    set u' : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => v' x / w x)
      (hc'.div hW.w_cont fun x => (hW.w_pos x).ne') C fun x => by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (hW.w_pos x), div_le_iff₀ (hW.w_pos x)]
        exact hC x
    have hv'eq : (fun x => w x * u' x) = v' := by
      funext x
      change w x * (v' x / w x) = v' x
      field_simp [(hW.w_pos x).ne']
    have hfix : wbellman hW u' = u' := (solvesFE_iff hW u').2 (hv'eq ▸ hv')
    rw [← hv'eq, huniq u' hfix]

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Growth with human capital

SLP §5.8, pp. 111–112: `max Σ βᵗU(f[k_tφ(k_{t+1}/k_t)])` subject to
`(1 − δ)k_t ≤ k_{t+1} ≤ (1 + λ)k_t`, with functional equation
`v(k) = max_{y ∈ Γ(k)} {U(f[kφ(y/k)]) + βv(y)}` on `k > 0`.

Returns grow with `k`, so `v` is not bounded; the book's "unique continuous function" is
unique among continuous functions with `|v(k)| ≤ C(1 + k)` (any `v` of the form `Ak^{ασ}` with
`ασ < 1` qualifies).

* `human_assumption43`: `Γ(k) = [(1 − δ)k, (1 + λ)k]` is nonempty, compact-valued and continuous.
* **Exercise 5.8a** (`ex_5_8a`): if `β(1 + λ) < 1`, exactly one continuous `v` with
  `|v(k)| ≤ C(1 + k)` solves the functional equation (the weighted contraction of
  `WeightedBellman`, weight `1 + k`, modulus `β(1 + λ)`). `U` and `f` need only be continuous
  and nondecreasing with `U(f(L)) ≤ A + BL`, which holds when `U ∘ f` is concave
  (`concave_linear_bound`).
* **Exercise 5.8b** (`ex_5_8b`): for `f(L) = L^α` and `U(c) = c^σ/σ`, `0 < α, σ < 1`,
  `v(k) = Ak^{ασ}` with `A > 0` (the sign of `σ`), and the policy `g(k) = θk` is optimal: human
  capital grows at a constant rate. `A` is the fixed point of
  `A ↦ max_x [φ(x)^{ασ}/σ + βAx^{ασ}]`, a contraction of modulus `β(1 + λ)^{ασ}`. For `σ < 0`,
  `U(0) = −∞` and the returns are unbounded below, so part (a) does not apply; that case is not
  covered.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {U f φ : ℝ → ℝ} {δ lam β : ℝ}

/-- `Γ(k) = [(1 − δ)k, (1 + λ)k]` satisfies Assumption 4.3 on `(0, ∞)`. -/
theorem human_assumption43 (hδ0 : 0 < δ) (hδ1 : δ < 1) (hlam : 0 < lam) :
    Assumption43 (humanΓ δ lam) := by
  have hI : (1 - δ) ≤ 1 + lam := by linarith
  have hself : ∀ k : PosR, k ∈ humanΓ δ lam k := fun k =>
    ⟨by nlinarith [k.2], by nlinarith [k.2]⟩
  -- the ratio `y/k` of a feasible pair lies in `I`
  have hratio : ∀ k y : PosR, y ∈ humanΓ δ lam k → y.1 / k.1 ∈ Icc (1 - δ) (1 + lam) :=
    fun k y hy => ⟨(le_div_iff₀ k.2).2 hy.1, (div_le_iff₀ k.2).2 hy.2⟩
  have hmk : ∀ (k : PosR) (x : ℝ), x ∈ Icc (1 - δ) (1 + lam) → 0 < x * k.1 := fun k x hx =>
    mul_pos (by linarith [hx.1]) k.2
  refine ⟨fun k => ⟨k, hself k⟩, fun k => ?_, fun k => ⟨⟨k, hself k⟩, fun y hy ks hks => ?_⟩,
    fun k => ⟨⟨k, hself k⟩, fun ks hks ys hys => ?_⟩⟩
  · -- compact: the image in `ℝ` is `[(1 − δ)k, (1 + λ)k]`
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' humanΓ δ lam k = Icc ((1 - δ) * k.1) ((1 + lam) * k.1) := by
      ext z
      refine ⟨fun ⟨y, hy, hz⟩ => hz ▸ hy, fun hz => ⟨⟨z, ?_⟩, hz, rfl⟩⟩
      exact lt_of_lt_of_le (mul_pos (by linarith) k.2) hz.1
    rw [this]
    exact isCompact_Icc
  · -- l.h.c.: `yₙ = (y/k)kₙ`
    have hx := hratio k y hy
    refine ⟨0, fun n => ⟨y.1 / k.1 * (ks n).1, hmk (ks n) _ hx⟩, fun n _ =>
      ⟨by simp only; nlinarith [(ks n).2, hx.1], by simp only; nlinarith [(ks n).2, hx.2]⟩, ?_⟩
    have := ((continuous_subtype_val.tendsto k).comp hks).const_mul (y.1 / k.1)
    rw [div_mul_cancel₀ _ k.2.ne'] at this
    exact tendsto_subtype_rng.2 this
  · -- u.h.c.: the ratios `yₙ/kₙ` have a convergent subsequence in `I`
    obtain ⟨x, hx, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq
      (x := fun n => (ys n).1 / (ks n).1) fun n => hratio _ _ (hys n)
    refine ⟨⟨x * k.1, hmk k x hx⟩, ⟨by simp only; nlinarith [k.2, hx.1],
      by simp only; nlinarith [k.2, hx.2]⟩, ψ, hψ, ?_⟩
    have hk := ((continuous_subtype_val.tendsto k).comp hks).comp hψ.tendsto_atTop
    have := hlim.mul hk
    refine tendsto_subtype_rng.2 (this.congr fun n => ?_)
    simp only [Function.comp_apply]
    field_simp [(ks (ψ n)).2.ne']

/-- The hypotheses of SLP §5.8 used here. -/
structure HCGrowthHyp (U f φ : ℝ → ℝ) (δ lam β : ℝ) : Prop where
  δ_pos : 0 < δ
  δ_lt : δ < 1
  lam_pos : 0 < lam
  β_pos : 0 < β
  discount : β * (1 + lam) < 1
  φ_cont : ContinuousOn φ (Icc (1 - δ) (1 + lam))
  φ_nonneg : ∀ x ∈ Icc (1 - δ) (1 + lam), 0 ≤ φ x
  φ_le_one : ∀ x ∈ Icc (1 - δ) (1 + lam), φ x ≤ 1
  f_cont : ContinuousOn f (Ici 0)
  f_nonneg : ∀ L, 0 ≤ L → 0 ≤ f L
  f_mono : MonotoneOn f (Ici 0)
  U_cont : ContinuousOn U (Ici 0)
  U_mono : MonotoneOn U (Ici 0)
  lin : ∃ A B, ∀ L, 0 ≤ L → U (f L) ≤ A + B * L

/-- `F(k, y) = U(f[kφ(y/k)])`. -/
noncomputable def hcF (U f φ : ℝ → ℝ) (p : PosR × PosR) : ℝ := U (f (p.1.1 * φ (p.2.1 / p.1.1)))

/-- The weight `1 + k`. -/
def hcW (k : PosR) : ℝ := 1 + k.1

/-- A concave nondecreasing function on `[0, ∞)` lies below a line. -/
theorem concave_linear_bound {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ici 0) g)
    (hm : MonotoneOn g (Ici 0)) : ∃ A B, ∀ L, 0 ≤ L → g L ≤ A + B * L := by
  set s := (g 1 - g (1 / 2)) / (1 / 2)
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.2 (hm (mem_Ici.2 (by norm_num))
    (mem_Ici.2 (by norm_num)) (by norm_num))) (by norm_num)
  refine ⟨g 1, s, fun L hL => ?_⟩
  rcases le_or_gt L 1 with hL1 | hL1
  · have := hm (mem_Ici.2 hL) (mem_Ici.2 zero_le_one) hL1
    nlinarith
  · have hadj := hg.slope_anti_adjacent (x := 1 / 2) (y := 1) (z := L) (mem_Ici.2 (by norm_num))
      (mem_Ici.2 hL) (by norm_num) hL1
    rw [div_le_iff₀ (by linarith)] at hadj
    nlinarith

/-- Under `HCGrowthHyp` the weighted framework applies with weight `1 + k` and modulus
`β(1 + λ)`. -/
theorem hc_weighted (h : HCGrowthHyp U f φ δ lam β) :
    WeightedHyp (humanΓ δ lam) (hcF U f φ) hcW β (β * (1 + lam)) := by
  have hratio : ∀ p ∈ graph (humanΓ δ lam), p.2.1 / p.1.1 ∈ Icc (1 - δ) (1 + lam) :=
    fun p hp => ⟨(le_div_iff₀ p.1.2).2 hp.1, (div_le_iff₀ p.1.2).2 hp.2⟩
  have hL : ∀ p ∈ graph (humanΓ δ lam), p.1.1 * φ (p.2.1 / p.1.1) ∈ Icc 0 p.1.1 := fun p hp =>
    ⟨mul_nonneg p.1.2.le (h.φ_nonneg _ (hratio p hp)),
      mul_le_of_le_one_right p.1.2.le (h.φ_le_one _ (hratio p hp))⟩
  have hxc : ContinuousOn (fun p : PosR × PosR => p.2.1 / p.1.1) (graph (humanΓ δ lam)) :=
    ((continuous_subtype_val.comp continuous_snd).div (continuous_subtype_val.comp continuous_fst)
      fun p => p.1.2.ne').continuousOn
  have hLc : ContinuousOn (fun p : PosR × PosR => p.1.1 * φ (p.2.1 / p.1.1))
      (graph (humanΓ δ lam)) :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.mul (h.φ_cont.comp hxc hratio)
  have hfc := h.f_cont.comp hLc fun p hp => mem_Ici.2 (hL p hp).1
  obtain ⟨A, B, hAB⟩ := h.lin
  refine ⟨human_assumption43 h.δ_pos h.δ_lt h.lam_pos,
    h.U_cont.comp hfc fun p hp => mem_Ici.2 (h.f_nonneg _ (hL p hp).1),
    continuous_const.add continuous_subtype_val, fun k => by simp only [hcW]; linarith [k.2],
    ⟨|U (f 0)| + |A| + |B|, fun p hp => ?_⟩, h.β_pos, h.discount, fun k y hy => ?_⟩
  · -- `U(f(0)) ≤ F ≤ U(f(k)) ≤ A + Bk`
    have hLp := hL p hp
    have hf0 := h.f_nonneg 0 le_rfl
    have hlo : U (f 0) ≤ hcF U f φ p :=
      h.U_mono (mem_Ici.2 hf0) (mem_Ici.2 (h.f_nonneg _ hLp.1))
        (h.f_mono (mem_Ici.2 le_rfl) (mem_Ici.2 hLp.1) hLp.1)
    have hhi : hcF U f φ p ≤ A + B * p.1.1 :=
      (h.U_mono (mem_Ici.2 (h.f_nonneg _ hLp.1)) (mem_Ici.2 (h.f_nonneg _ p.1.2.le))
        (h.f_mono (mem_Ici.2 hLp.1) (mem_Ici.2 p.1.2.le) hLp.2)).trans (hAB _ p.1.2.le)
    have hk := p.1.2
    have hB : B * p.1.1 ≤ |B| * p.1.1 := mul_le_mul_of_nonneg_right (le_abs_self B) hk.le
    have h1 := mul_nonneg (abs_nonneg (U (f 0))) hk.le
    have h2 := mul_nonneg (abs_nonneg A) hk.le
    have h3 := mul_nonneg (abs_nonneg B) hk.le
    have h4 := neg_abs_le (U (f 0))
    have h5 := le_abs_self A
    simp only [hcW]
    rw [abs_le]
    constructor
    · nlinarith [abs_nonneg A, abs_nonneg B]
    · nlinarith [abs_nonneg (U (f 0)), abs_nonneg B]
  · -- `β(1 + y) ≤ β(1 + λ)(1 + k)`
    have hy2 : y.1 ≤ (1 + lam) * k.1 := hy.2
    simp only [hcW]
    nlinarith [h.β_pos, h.lam_pos, k.2]

/-- **Exercise 5.8a.** If `β(1 + λ) < 1`, exactly one continuous `v` with `|v(k)| ≤ C(1 + k)`
solves the functional equation. -/
theorem ex_5_8a (h : HCGrowthHyp U f φ δ lam β) :
    ∃ v : PosR → ℝ, SolvesFE (humanΓ δ lam) (hcF U f φ) β v ∧ Continuous v ∧
      (∃ C, ∀ k, |v k| ≤ C * hcW k) ∧
      ∀ v' : PosR → ℝ, SolvesFE (humanΓ δ lam) (hcF U f φ) β v' → Continuous v' →
        (∃ C, ∀ k, |v' k| ≤ C * hcW k) → v' = v := by
  have : Nonempty PosR := ⟨⟨1, one_pos⟩⟩
  exact weighted_exists_unique (hc_weighted h)

/-! ### Exercise 5.8b: the power case -/

variable {α σ : ℝ}

/-- `k^p ≤ 1 + k` for `0 ≤ p ≤ 1` and `k ≥ 0`. -/
theorem rpow_le_one_add {k p : ℝ} (hk : 0 ≤ k) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : k ^ p ≤ 1 + k := by
  rcases le_or_gt k 1 with hk1 | hk1
  · linarith [Real.rpow_le_one hk hk1 hp0]
  · have := Real.rpow_le_rpow_of_exponent_le hk1.le hp1
    rw [Real.rpow_one] at this
    linarith

/-- The per-unit objective `φ(x)^{ασ}/σ + βAx^{ασ}`. -/
noncomputable def hcObj (φ : ℝ → ℝ) (α σ β A x : ℝ) : ℝ :=
  φ x ^ (α * σ) / σ + β * A * x ^ (α * σ)

/-- `Φ(A) = max_{x ∈ I} [φ(x)^{ασ}/σ + βAx^{ασ}]`. -/
noncomputable def hcPhi (φ : ℝ → ℝ) (δ lam α σ β A : ℝ) : ℝ :=
  sSup (hcObj φ α σ β A '' Icc (1 - δ) (1 + lam))

/-- **Exercise 5.8b.** With `f(L) = L^α`, `U(c) = c^σ/σ`, `0 < α, σ < 1`, `β(1 + λ) < 1` and
`φ(1 − δ) = 1`: there are `A > 0` and `θ ∈ [1 − δ, 1 + λ]` such that `v(k) = Ak^{ασ}` solves the
functional equation, it is the unique solution of part (a), and `y = θk` attains the maximum, so
human capital grows at the constant rate `θ`. -/
theorem ex_5_8b (h : HCGrowthHyp (fun c => c ^ σ / σ) (fun L => L ^ α) φ δ lam β)
    (hφ1 : φ (1 - δ) = 1) (hα0 : 0 < α) (hα1 : α < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ A > 0, ∃ θ ∈ Icc (1 - δ) (1 + lam),
      SolvesFE (humanΓ δ lam) (hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ) β
        (fun k => A * k.1 ^ (α * σ)) ∧
      (∀ v' : PosR → ℝ,
        SolvesFE (humanΓ δ lam) (hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ) β v' →
        Continuous v' → (∃ C, ∀ k, |v' k| ≤ C * hcW k) → v' = fun k => A * k.1 ^ (α * σ)) ∧
      ∀ (k : PosR) (hy : 0 < θ * k.1),
        hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ (k, ⟨θ * k.1, hy⟩) +
          β * (A * (θ * k.1) ^ (α * σ)) = A * k.1 ^ (α * σ) := by
  set p := α * σ
  set I := Icc (1 - δ) (1 + lam)
  have hp0 : 0 < p := mul_pos hα0 hσ0
  have hp1 : p < 1 := by
    have : α * σ < 1 * 1 := mul_lt_mul'' hα1 hσ1 hα0.le hσ0.le
    simpa using this
  have hδ0 := h.δ_pos
  have hδ1 := h.δ_lt
  have hlam := h.lam_pos
  have hβ1 : β < 1 := by nlinarith [h.discount, h.β_pos]
  have hIne : I.Nonempty := nonempty_Icc.2 (by linarith)
  have hIpos : ∀ x ∈ I, 0 < x := fun x hx => by linarith [hx.1]
  -- the per-unit objective and `Φ`
  have hcont : ∀ A, ContinuousOn (hcObj φ α σ β A) I := fun A =>
    ((h.φ_cont.rpow_const fun x hx => Or.inr hp0.le).div_const σ).add
      (continuousOn_const.mul (continuousOn_id.rpow_const fun x _ => Or.inr hp0.le))
  have hbdd : ∀ A, BddAbove (hcObj φ α σ β A '' I) := fun A =>
    (isCompact_Icc.image_of_continuousOn (hcont A)).bddAbove
  have hle : ∀ A, ∀ x ∈ I, hcObj φ α σ β A x ≤ hcPhi φ δ lam α σ β A := fun A x hx =>
    le_csSup (hbdd A) ⟨x, hx, rfl⟩
  have hxp : ∀ x ∈ I, 0 ≤ x ^ p ∧ x ^ p ≤ (1 + lam) ^ p := fun x hx =>
    ⟨Real.rpow_nonneg (hIpos x hx).le _, Real.rpow_le_rpow (hIpos x hx).le hx.2 hp0.le⟩
  have hlip : ∀ A A', hcPhi φ δ lam α σ β A ≤
      hcPhi φ δ lam α σ β A' + β * (1 + lam) ^ p * |A - A'| := fun A A' => by
    refine csSup_le (hIne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hle A' x hx
    obtain ⟨hx0, hx1⟩ := hxp x hx
    have h2 : β * (A - A') * x ^ p ≤ β * (1 + lam) ^ p * |A - A'| := by
      have := mul_le_mul (le_abs_self (A - A')) hx1 hx0 (abs_nonneg _)
      nlinarith [h.β_pos]
    simp only [hcObj] at h1 ⊢
    nlinarith
  -- `Φ` is a contraction of modulus `β(1 + λ)^{ασ}`
  have hρ1 : β * (1 + lam) ^ p < 1 := by
    have : (1 + lam) ^ p ≤ (1 + lam) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hp1.le
    rw [Real.rpow_one] at this
    nlinarith [h.β_pos, h.discount]
  have hcontr : IsContraction (hcPhi φ δ lam α σ β) (β * (1 + lam) ^ p) := by
    refine ⟨mul_pos h.β_pos (Real.rpow_pos_of_pos (by linarith) _), hρ1, fun A A' => ?_⟩
    rw [Real.dist_eq, Real.dist_eq, abs_le]
    have h1 := hlip A A'
    have h2 := hlip A' A
    rw [abs_sub_comm A' A] at h2
    constructor <;> linarith
  obtain ⟨A, hA, -, -⟩ := theorem_3_2 hcontr
  obtain ⟨θ, hθ, hθmax⟩ := isCompact_Icc.exists_isMaxOn hIne (hcont A)
  have hΦθ : hcPhi φ δ lam α σ β A = hcObj φ α σ β A θ :=
    le_antisymm (csSup_le (hIne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hθmax hx))
      (hle A θ hθ)
  -- `A > 0`
  have hApos : 0 < A := by
    have h1 := hle A (1 - δ) ⟨le_rfl, by linarith⟩
    rw [hA] at h1
    simp only [hcObj, hφ1, Real.one_rpow] at h1
    set t := (1 - δ) ^ (α * σ)
    have h2 : t ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hp0.le
    have h3 : 0 < 1 / σ := by positivity
    by_contra hneg
    push Not at hneg
    have h4 : A ≤ A * t := by nlinarith
    have h5 : β * A ≤ β * A * t := by nlinarith [h.β_pos]
    nlinarith [h.β_pos]
  -- the key identity: `F(k, y) + βAy^{ασ} = k^{ασ}[φ(x)^{ασ}/σ + βAx^{ασ}]`, `x = y/k`
  have hkey : ∀ (k y : PosR), y.1 / k.1 ∈ I →
      hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ (k, y) + β * (A * y.1 ^ p) =
        k.1 ^ p * hcObj φ α σ β A (y.1 / k.1) := fun k y hx => by
    have hφ0 := h.φ_nonneg _ hx
    have hk := k.2
    set x := y.1 / k.1
    have hyp : y.1 ^ p = x ^ p * k.1 ^ p := by
      rw [← Real.mul_rpow (hIpos _ hx).le hk.le, div_mul_cancel₀ _ hk.ne']
    simp only [hcF, hcObj]
    rw [← Real.rpow_mul (mul_nonneg hk.le hφ0), Real.mul_rpow hk.le hφ0, hyp]
    ring
  have hratio : ∀ k y : PosR, y ∈ humanΓ δ lam k → y.1 / k.1 ∈ I :=
    fun k y hy => ⟨(le_div_iff₀ k.2).2 hy.1, (div_le_iff₀ k.2).2 hy.2⟩
  have hsolve : SolvesFE (humanΓ δ lam) (hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ) β
      (fun k => A * k.1 ^ p) := by
    intro k
    have hkp : 0 ≤ k.1 ^ p := Real.rpow_nonneg k.2.le _
    set y : PosR := ⟨θ * k.1, mul_pos (hIpos θ hθ) k.2⟩
    have hyk : y.1 / k.1 = θ := mul_div_cancel_right₀ θ k.2.ne'
    refine ⟨⟨y, ⟨by simp only [y]; nlinarith [hθ.1, k.2], by simp only [y]; nlinarith [hθ.2, k.2]⟩,
      ?_⟩, fun z hz => ?_⟩
    · change A * k.1 ^ p = _ + β * (A * y.1 ^ p)
      rw [hkey k y (hyk ▸ hθ), hyk, ← hΦθ, hA, mul_comm]
    · change _ + β * (A * z.1 ^ p) ≤ A * k.1 ^ p
      rw [hkey k z (hratio k z hz), mul_comm A]
      refine mul_le_mul_of_nonneg_left ?_ hkp
      exact (hle A _ (hratio k z hz)).trans hA.le
  -- uniqueness from part (a)
  obtain ⟨v₀, -, -, -, huniq⟩ := ex_5_8a h
  have hcv : Continuous fun k : PosR => A * k.1 ^ p :=
    continuous_const.mul (continuous_subtype_val.rpow_const fun k => Or.inl k.2.ne')
  have hbv : ∃ C, ∀ k : PosR, |A * k.1 ^ p| ≤ C * hcW k := ⟨A, fun k => by
    rw [abs_of_nonneg (mul_nonneg hApos.le (Real.rpow_nonneg k.2.le _))]
    exact mul_le_mul_of_nonneg_left (rpow_le_one_add k.2.le hp0.le hp1.le) hApos.le⟩
  have hv₀ := huniq _ hsolve hcv hbv
  refine ⟨A, hApos, θ, hθ, hsolve, fun v' hv' hc' hb' => (huniq v' hv' hc' hb').trans hv₀.symm,
    fun k hy => ?_⟩
  have hyk : θ * k.1 / k.1 = θ := mul_div_cancel_right₀ θ k.2.ne'
  rw [hkey k ⟨θ * k.1, hy⟩ (by simp only; rw [hyk]; exact hθ)]
  simp only
  rw [hyk, ← hΦθ, hA, mul_comm]

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Investment with constant returns

SLP §5.10, pp. 113–114: output `F(k, y)` depends on current and end-of-period capital, `F` has
constant returns, and `(1 − δ)k ≤ y ≤ (1 + α)k`. The firm solves
`v(k) = max_{y ∈ Γ(k)} {pF(k, y) − q[y − (1 − δ)k] + βv(y)}` on `k ≥ 0`.

With `β(1 + α) < 1`, Assumptions 4.10–4.11 hold (`crs_assumption410`, `crs_assumption411`); this
is what must be assumed about `α` and `β`.

* **Exercise 5.10a** (`ex_5_10a`): `v*` is homogeneous of degree one.
* **Exercise 5.10b**: `solvesFE_rescale`: if `v` solves the functional equation, so does
  `k ↦ v(ak)/a` for every `a > 0`. `ex_5_10b`: every solution with `|v(k)| ≤ Ck` is `v*`, hence
  homogeneous of degree one. (Some growth bound is needed: Theorem 4.3 is what rules out other
  solutions.)
* **Exercise 5.10c** (`ex_5_10c`): the solution is `v(k) = Ak` with
  `A = max_{θ ∈ [1 − δ, 1 + α]} [pF(1, θ) − q(θ − (1 − δ)) + βAθ]`; the policy is `g(k) = θk` with
  `θ` the maximizer, unique when `F(1, ·)` is strictly concave (which homogeneity and strict
  quasi-concavity give, Exercise 4.8b); `v = v*`; and the plan `k_t = θᵗk₀` is optimal.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

/-- The state space `[0, ∞)` of capital. -/
abbrev CapStock := ↥(Ici (0 : ℝ))

theorem isCone_Ici : IsCone (Ici (0 : ℝ)) := fun x hx a ha => by
  simp only [smul_eq_mul, Set.mem_Ici] at hx ⊢; exact mul_nonneg ha hx

variable {Fk : ℝ → ℝ → ℝ} {p q δ α β : ℝ}

/-- `Γ(k) = [(1 − δ)k, (1 + α)k]`. -/
def crsΓ (δ α : ℝ) (k : CapStock) : Set CapStock := {y | (1 - δ) * k.1 ≤ y.1 ∧ y.1 ≤ (1 + α) * k.1}

/-- The return `pF(k, y) − q[y − (1 − δ)k]`. -/
def crsH (Fk : ℝ → ℝ → ℝ) (p q δ : ℝ) (pr : CapStock × CapStock) : ℝ :=
  p * Fk pr.1.1 pr.2.1 - q * (pr.2.1 - (1 - δ) * pr.1.1)

/-- The hypotheses of SLP §5.10 used here. -/
structure CRSInvHyp (Fk : ℝ → ℝ → ℝ) (p q δ α β : ℝ) : Prop where
  δ_pos : 0 < δ
  δ_lt : δ < 1
  α_pos : 0 < α
  β_pos : 0 < β
  discount : β * (1 + α) < 1
  p_nonneg : 0 ≤ p
  q_nonneg : 0 ≤ q
  F_cont : ContinuousOn (fun z : ℝ × ℝ => Fk z.1 z.2) (Set.Ici 0 ×ˢ Set.Ici 0)
  F_hom : ∀ a k y, 0 ≤ a → 0 ≤ k → 0 ≤ y → Fk (a * k) (a * y) = a * Fk k y

theorem CRSInvHyp.β_lt (h : CRSInvHyp Fk p q δ α β) : β < 1 := by
  nlinarith [h.discount, h.β_pos, h.α_pos]

/-- Assumption 4.10 holds with growth factor `1 + α`. -/
theorem crs_assumption410 (h : CRSInvHyp Fk p q δ α β) :
    Assumption410 isCone_Ici (crsΓ δ α) β (1 + α) := by
  have hemb := (isClosed_Ici (a := (0 : ℝ))).isClosedEmbedding_subtypeVal
  have hδ := h.δ_lt
  have hδ0 := h.δ_pos
  have hα := h.α_pos
  have hself : ∀ k : CapStock, k ∈ crsΓ δ α k := fun k =>
    ⟨by nlinarith [k.2.out, h.δ_pos], by nlinarith [k.2.out]⟩
  refine ⟨convex_Ici 0, fun k => ⟨k, hself k⟩, fun k => hemb.isCompact_preimage isCompact_Icc,
    fun k => ⟨⟨k, hself k⟩, fun y hy ks hks => ?_⟩,
    fun k => ⟨⟨k, hself k⟩, fun ks hks ys hys => ?_⟩,
    fun k y hy a ha => ?_, by linarith, by linarith [h.discount], fun k y hy => ?_⟩
  · -- l.h.c.: `yₙ = max{(1 − δ)kₙ, min{y, (1 + α)kₙ}}`
    have hval := (continuous_subtype_val.tendsto k).comp hks
    refine ⟨0, fun n => ⟨max ((1 - δ) * (ks n).1) (min y.1 ((1 + α) * (ks n).1)),
      le_max_of_le_left (mul_nonneg (by linarith) (ks n).2.out)⟩,
      fun n _ => ⟨le_max_left _ _, max_le (mul_le_mul_of_nonneg_right (by linarith)
        (ks n).2.out) (min_le_right _ _)⟩, ?_⟩
    have hlim := (hval.const_mul (1 - δ)).max ((tendsto_const_nhds (x := y.1)).min
      (hval.const_mul (1 + α)))
    rw [min_eq_left hy.2, max_eq_right hy.1] at hlim
    exact tendsto_subtype_rng.2 hlim
  · -- u.h.c.: the `yₙ` stay in a compact set
    have hval := (continuous_subtype_val.tendsto k).comp hks
    obtain ⟨B, hB⟩ := hval.bddAbove_range
    have hK : ∀ n, ys n ∈ Subtype.val ⁻¹' Icc (0 : ℝ) ((1 + α) * B) := fun n =>
      ⟨(ys n).2, (hys n).2.trans (mul_le_mul_of_nonneg_left
        (show (ks n).1 ≤ B from hB ⟨n, rfl⟩) (by linarith))⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := (hemb.isCompact_preimage isCompact_Icc).tendsto_subseq hK
    have hyl := (continuous_subtype_val.tendsto y).comp hlim
    have hkl := hval.comp hφ.tendsto_atTop
    refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
    · exact le_of_tendsto_of_tendsto (hkl.const_mul (1 - δ)) hyl
        (Eventually.of_forall fun n => (hys (φ n)).1)
    · exact le_of_tendsto_of_tendsto hyl (hkl.const_mul (1 + α))
        (Eventually.of_forall fun n => (hys (φ n)).2)
  · -- the graph is a cone
    have h1 := hy.1
    have h2 := hy.2
    simp only [csmul, smul_eq_mul]
    exact ⟨by nlinarith, by nlinarith⟩
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg y.2.out, abs_of_nonneg k.2.out]
    exact hy.2

/-- On the graph, `|F(k, y)| ≤ Ck`. -/
theorem crs_F_bound (h : CRSInvHyp Fk p q δ α β) :
    ∃ C, 0 ≤ C ∧ ∀ k : CapStock, ∀ y ∈ crsΓ δ α k, |Fk k.1 y.1| ≤ C * k.1 := by
  have hδ := h.δ_lt
  have hδ0 := h.δ_pos
  have hα := h.α_pos
  have hc : ContinuousOn (Fk 1) (Icc (1 - δ) (1 + α)) :=
    h.F_cont.comp (continuous_const.prodMk continuous_id).continuousOn fun θ hθ =>
      ⟨mem_Ici.2 zero_le_one, mem_Ici.2 (show (0 : ℝ) ≤ θ by linarith [hθ.1])⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 ⟨by linarith, by linarith⟩)
  refine ⟨C, hC0, fun k y hy => ?_⟩
  rcases eq_or_lt_of_le k.2.out with hk0 | hkpos
  · -- `k = 0` forces `y = 0`, and `F(0, 0) = 0`
    have hy0 : y.1 = 0 := le_antisymm (by have := hy.2; rw [← hk0] at this; linarith) y.2.out
    have hF00 : Fk 0 0 = 0 := by
      have := h.F_hom 0 0 0 le_rfl le_rfl le_rfl
      simpa using this
    rw [← hk0, hy0, hF00]
    simp
  · have hθ : y.1 / k.1 ∈ Icc (1 - δ) (1 + α) :=
      ⟨(le_div_iff₀ hkpos).2 hy.1, (div_le_iff₀ hkpos).2 hy.2⟩
    have e : Fk k.1 y.1 = k.1 * Fk 1 (y.1 / k.1) := by
      have := h.F_hom k.1 1 (y.1 / k.1) hkpos.le zero_le_one (by linarith [hθ.1])
      rwa [mul_one, mul_div_cancel₀ _ hkpos.ne'] at this
    rw [e, abs_mul, abs_of_pos hkpos, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hC _ hθ) hkpos.le

/-- Assumption 4.11 holds. -/
theorem crs_assumption411 (h : CRSInvHyp Fk p q δ α β) :
    ∃ B, Assumption411 isCone_Ici (crsΓ δ α) (crsH Fk p q δ) β B := by
  obtain ⟨C, hC0, hC⟩ := crs_F_bound h
  have hδ := h.δ_lt
  refine ⟨p * C + q + 1, h.β_pos, h.β_lt, ?_, fun k y hy a ha => ?_,
    by nlinarith [h.p_nonneg, h.q_nonneg], fun k y hy => ?_⟩
  · have hmaps : MapsTo (fun pr : CapStock × CapStock => (pr.1.1, pr.2.1))
        (graph (crsΓ δ α)) (Set.Ici 0 ×ˢ Set.Ici 0) := fun pr _ => ⟨pr.1.2, pr.2.2⟩
    exact (continuousOn_const.mul (h.F_cont.comp ((continuous_subtype_val.comp
      continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
        hmaps)).sub (continuous_const.mul ((continuous_subtype_val.comp continuous_snd).sub
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst)))).continuousOn
  · simp only [crsH, csmul, smul_eq_mul]
    rw [h.F_hom a k.1 y.1 ha k.2.out y.2.out]
    ring
  · have h1 := hC k y hy
    have hk := k.2.out
    have hy0 := y.2.out
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk, abs_of_nonneg hy0]
    simp only [crsH]
    have h2 : |q * (y.1 - (1 - δ) * k.1)| ≤ q * (y.1 + k.1) := by
      rw [abs_mul, abs_of_nonneg h.q_nonneg]
      refine mul_le_mul_of_nonneg_left ?_ h.q_nonneg
      have := mul_nonneg h.δ_pos.le hk
      rw [abs_le]; constructor <;> nlinarith
    have h3 : |p * Fk k.1 y.1| ≤ p * C * k.1 := by
      rw [abs_mul, abs_of_nonneg h.p_nonneg, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 h.p_nonneg
    calc |p * Fk k.1 y.1 - q * (y.1 - (1 - δ) * k.1)|
        ≤ |p * Fk k.1 y.1| + |q * (y.1 - (1 - δ) * k.1)| := abs_sub _ _
      _ ≤ p * C * k.1 + q * (y.1 + k.1) := add_le_add h3 h2
      _ ≤ (p * C + q + 1) * (k.1 + y.1) := by
          nlinarith [mul_nonneg (mul_nonneg h.p_nonneg hC0) hy0, h.q_nonneg]

/-- **Exercise 5.10a.** `v*` is homogeneous of degree one: `v*(ak) = av*(k)` for `a ≥ 0`. -/
theorem ex_5_10a (h : CRSInvHyp Fk p q δ α β) (k : CapStock) {a : ℝ} (ha : 0 ≤ a) :
    vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β (csmul isCone_Ici ha k) =
      (a : EReal) * vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β k := by
  obtain ⟨B, h411⟩ := crs_assumption411 h
  obtain ⟨v, hvH, hv⟩ := ex_4_6c_hom (crs_assumption410 h) h411
  rw [hv]
  beta_reduce
  rw [hvH.2.1 k a ha, EReal.coe_mul]

/-- A real solution of the functional equation in max form solves it in `R̄`. -/
theorem satisfiesFE_of_solvesFE {X : Type*} {Γ : X → Set X} {F : X × X → ℝ} {v : X → ℝ}
    (hv : SolvesFE Γ F β v) : SatisfiesFE Γ (curryF F) β fun x => (v x : EReal) := by
  intro x
  obtain ⟨⟨y, hy, hval⟩, hmax⟩ := hv x
  change (v x : EReal) = ⨆ y ∈ Γ x, ((curryF F x y : ℝ) : EReal) + (β : EReal) * (v y : EReal)
  refine le_antisymm ?_ (iSup₂_le fun z hz => ?_)
  · refine le_trans ?_ (le_biSup (fun z => ((curryF F x z : ℝ) : EReal) +
      (β : EReal) * (v z : EReal)) hy)
    rw [hval, curryF, ← EReal.coe_mul, ← EReal.coe_add]
  · rw [curryF, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (hmax z hz)

/-- **Exercise 5.10b.** The functional equation is invariant under rescaling: if `v` solves it,
so does `k ↦ v(ak)/a` for `a > 0`. -/
theorem solvesFE_rescale (h : CRSInvHyp Fk p q δ α β) {v : CapStock → ℝ}
    (hv : SolvesFE (crsΓ δ α) (crsH Fk p q δ) β v) {a : ℝ} (ha : 0 < a) :
    SolvesFE (crsΓ δ α) (crsH Fk p q δ) β fun k => v (csmul isCone_Ici ha.le k) / a := by
  have hhom : ∀ (k y : CapStock) (b : ℝ) (hb : 0 ≤ b),
      crsH Fk p q δ (csmul isCone_Ici hb k, csmul isCone_Ici hb y) = b * crsH Fk p q δ (k, y) :=
    fun k y b hb => by
      simp only [crsH, csmul, smul_eq_mul]
      rw [h.F_hom b k.1 y.1 hb k.2.out y.2.out]; ring
  have hcone : ∀ (k y : CapStock) (b : ℝ) (hb : 0 ≤ b), y ∈ crsΓ δ α k →
      csmul isCone_Ici hb y ∈ crsΓ δ α (csmul isCone_Ici hb k) := fun k y b hb hy => by
    simp only [crsΓ, csmul, smul_eq_mul, mem_ofPred_eq] at hy ⊢
    exact ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
  have hinv : ∀ y : CapStock, csmul isCone_Ici ha.le (csmul isCone_Ici (inv_pos.2 ha).le y) = y :=
    fun y => Subtype.ext (by simp only [csmul, smul_eq_mul]; field_simp)
  intro k
  obtain ⟨⟨y', hy', hval⟩, hmax⟩ := hv (csmul isCone_Ici ha.le k)
  set y := csmul isCone_Ici (inv_pos.2 ha).le y'
  have hy : y ∈ crsΓ δ α k := by
    have := hcone _ y' a⁻¹ (inv_pos.2 ha).le hy'
    have hk : csmul isCone_Ici (inv_pos.2 ha).le (csmul isCone_Ici ha.le k) = k :=
      Subtype.ext (by simp only [csmul, smul_eq_mul]; field_simp)
    rwa [hk] at this
  refine ⟨⟨y, hy, ?_⟩, fun z hz => ?_⟩
  · beta_reduce
    rw [hval, ← hinv y', hhom k y a ha.le, hinv y']
    field_simp
  · beta_reduce
    have := hmax _ (hcone k z a ha.le hz)
    rw [hhom k z a ha.le] at this
    rw [le_div_iff₀ ha]
    have e : (crsH Fk p q δ (k, z) + β * (v (csmul isCone_Ici ha.le z) / a)) * a =
        a * crsH Fk p q δ (k, z) + β * v (csmul isCone_Ici ha.le z) := by field_simp
    rw [e]
    exact this

/-- **Exercise 5.10b.** Every solution of the functional equation with `|v(k)| ≤ Ck` equals
`v*`, and so is homogeneous of degree one. -/
theorem ex_5_10b (h : CRSInvHyp Fk p q δ α β) {v : CapStock → ℝ}
    (hv : SolvesFE (crsΓ δ α) (crsH Fk p q δ) β v) {C : ℝ} (hC : ∀ k : CapStock, |v k| ≤ C * k.1) :
    (fun k => (v k : EReal)) = vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β ∧
      ∀ (k : CapStock) (a : ℝ) (ha : 0 ≤ a), v (csmul isCone_Ici ha k) = a * v k := by
  obtain ⟨B, h411⟩ := crs_assumption411 h
  have h410 := crs_assumption410 h
  obtain ⟨h41, h42⟩ := ex_4_6b h410 h411
  have hαβ : 0 ≤ (1 + α) * β := mul_nonneg (by linarith [h.α_pos]) h.β_pos.le
  have hαβ1 : (1 + α) * β < 1 := by linarith [h.discount]
  have heq : (fun k => (v k : EReal)) = vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β := by
    refine theorem_4_3 h.β_pos.le h41 h42 (satisfiesFE_of_solvesFE hv) fun x₀ x hx => ?_
    have hb : Tendsto (fun n => β ^ n * v (x n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n => |C| * ‖x₀.1‖ * ((1 + α) * β) ^ n)
        (fun n => ?_) ?_
      · have hxn := ex_4_6a h410 hx n
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h.β_pos.le n)]
        have hvx : |v (x n)| ≤ |C| * ‖(x n).1‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (x n).2.out]
          exact (hC _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (x n).2.out)
        calc β ^ n * |v (x n)| ≤ β ^ n * (|C| * ((1 + α) ^ n * ‖x₀.1‖)) :=
              mul_le_mul_of_nonneg_left (hvx.trans (mul_le_mul_of_nonneg_left hxn
                (abs_nonneg C))) (pow_nonneg h.β_pos.le n)
          _ = |C| * ‖x₀.1‖ * ((1 + α) * β) ^ n := by rw [mul_pow]; ring
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hαβ hαβ1).const_mul (|C| * ‖x₀.1‖)
    simpa only [EReal.coe_mul, EReal.coe_zero] using EReal.tendsto_coe.2 hb
  refine ⟨heq, fun k a ha => ?_⟩
  have h1 := congrFun heq (csmul isCone_Ici ha k)
  have h2 := congrFun heq k
  rw [ex_5_10a h k ha, ← h2, ← EReal.coe_mul] at h1
  exact EReal.coe_injective h1

/-- **Exercise 5.10c.** Let `v` be the fixed point of Theorem 4.13 and `A = v(1)`. Then
`v(k) = Ak`; `A = max_θ [pF(1, θ) − q(θ − (1 − δ)) + βAθ]`, attained at some
`θ ∈ [1 − δ, 1 + α]`; `y = θk` is optimal at every `k`; `v = v*`; and when `p > 0` and
`F(1, ·)` is strictly concave on `[1 − δ, 1 + α]`, `θ` is the only optimal growth factor. -/
theorem ex_5_10c (h : CRSInvHyp Fk p q δ α β) :
    ∃ v : CapStock → ℝ, ∃ A θ : ℝ, θ ∈ Icc (1 - δ) (1 + α) ∧
      (∀ k : CapStock, v k = A * k.1) ∧
      (fun k => (v k : EReal)) = vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β ∧
      A = p * Fk 1 θ - q * (θ - (1 - δ)) + β * A * θ ∧
      (∀ θ' ∈ Icc (1 - δ) (1 + α), p * Fk 1 θ' - q * (θ' - (1 - δ)) + β * A * θ' ≤ A) ∧
      (0 < p → StrictConcaveOn ℝ (Icc (1 - δ) (1 + α)) (Fk 1) →
        ∀ θ' ∈ Icc (1 - δ) (1 + α), p * Fk 1 θ' - q * (θ' - (1 - δ)) + β * A * θ' = A →
          θ' = θ) := by
  obtain ⟨B, h411⟩ := crs_assumption411 h
  have h410 := crs_assumption410 h
  obtain ⟨v, hvH, hv, -, -, hG, -⟩ := theorem_4_13 h410 h411
  have hδ := h.δ_lt
  have hα := h.α_pos
  set one : CapStock := ⟨1, mem_Ici.2 zero_le_one⟩
  set A := v one
  have hlin : ∀ k : CapStock, v k = A * k.1 := fun k => by
    have := hvH.2.1 one k.1 k.2.out
    have hk : csmul isCone_Ici k.2.out one = k := Subtype.ext (by simp [csmul, one])
    rw [hk] at this
    rw [this, mul_comm]
  -- the maximizer at `k = 1`
  obtain ⟨y, hy⟩ := (hG one).1
  have hθ : y.1 ∈ Icc (1 - δ) (1 + α) := by
    have := hy.1; simp only [crsΓ, one, mul_one, mem_ofPred_eq] at this; exact this
  have hvx : ∀ x, v x = maxValue (obj (crsH Fk p q δ) β v) (crsΓ δ α) x := fun x =>
    (congrFun hv x).symm
  have hFE : ∀ z ∈ crsΓ δ α one, obj (crsH Fk p q δ) β v (one, z) ≤ v one := fun z hz => by
    rw [hvx one]
    exact le_maxValue (continuousOn_obj' h411 hvH.1) (h410.compact one) hz
  have hval : v one = obj (crsH Fk p q δ) β v (one, y) := by rw [hvx one]; exact hy.2.symm
  have hobj : ∀ z : CapStock, obj (crsH Fk p q δ) β v (one, z) =
      p * Fk 1 z.1 - q * (z.1 - (1 - δ)) + β * A * z.1 := fun z => by
    simp only [obj, crsH, one, hlin z, mul_one]; ring
  refine ⟨v, A, y.1, hθ, hlin, crs_fixed_eq_vstar h410 h411 hvH hv, ?_, fun θ' hθ' => ?_,
    fun hp hFs θ' hθ' heq => ?_⟩
  · rw [← hobj]; exact hval
  · have := hFE ⟨θ', mem_Ici.2 (by linarith [hθ'.1])⟩
      (by simp only [crsΓ, one, mul_one, mem_ofPred_eq]; exact hθ')
    rwa [hobj] at this
  · -- strict concavity of the objective in `θ` makes the maximizer unique
    by_contra hne
    have hs := hFs.2 hθ hθ' (Ne.symm hne) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hs
    have hmid : (1 / 2 : ℝ) • y.1 + (1 / 2 : ℝ) • θ' ∈ Icc (1 - δ) (1 + α) :=
      (convex_Icc _ _) hθ hθ' (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hmid
    have h1 := hFE ⟨1 / 2 * y.1 + 1 / 2 * θ', mem_Ici.2 (by linarith [hmid.1])⟩
      (by simp only [crsΓ, one, mul_one, mem_ofPred_eq]; exact hmid)
    rw [hobj] at h1
    have h2 : p * Fk 1 y.1 - q * (y.1 - (1 - δ)) + β * A * y.1 = A := by
      rw [← hobj]; exact hval.symm
    simp only at h1
    nlinarith [mul_lt_mul_of_pos_left hs hp]

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

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

namespace StokeyLucasPrescott.DeterministicApplications

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

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The principle of optimality with recursive preferences

SLP Exercise 5.12a, p. 117: relate the sequence problem
`max u_W(c)` subject to `Σ Rᵗ(p·c_t) ≤ A` (1) to the functional equation (2), as Theorems
4.2–4.5 do for additive preferences. Here `u_W` is the utility of Exercise 5.11d, plans are
bounded sequences in `ℝˡ₊`, and `R < 1`.

* `planCost_cons`, `feasible_head`, `feasible_shift`: a plan is feasible from `A` iff its first
  choice is in `Γ(A)` and the rest is feasible from `R⁻¹(A − p·c₀)` (the budget recursion).
* `utility_le_value` (Theorems 4.2–4.3, upper half): with `W` nondecreasing in `z` (W4), every
  feasible plan has `u_W(c) ≤ v(A)`.
* `exists_plan_near` (lower half): following the policy for `n + 1` periods and consuming nothing
  afterwards is feasible and comes within `βⁿ⁺¹(‖u_W‖ + ‖v‖)` of `v(A)`.
* `ex_5_12a`: so `v(A) = sup{u_W(c) : c feasible from A}`, the supremum function.
* `ex_5_12a_optimal` (Theorem 4.5): a plan whose wealth path satisfies
  `v(A_t) = W(c_t, v(A_{t+1}))` at every date attains `v(A)`; `ex_5_12a_necessary`
  (Theorem 4.4): with `W` strictly increasing in `z`, an optimal plan satisfies (2) at the first
  date and its continuation is optimal.

Optimal plans need not exist: when the policy's consumption path is unbounded it is not in `L`,
and the supremum is approached by the truncated plans only.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {l : ℕ} {W : (Fin l → ℝ) → ℝ → ℝ} {p : Fin l → ℝ} {R β M : ℝ}

/-- The present value `Σ Rᵗ(p·c_t)` of a plan. -/
noncomputable def planCost (p : Fin l → ℝ) (R : ℝ) (c : Seq l) : ℝ :=
  ∑' t, R ^ t * spend p (c.1 t)

theorem spend_le_bound {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (c : Seq l) (t : ℕ) :
    spend p (c.1 t) ≤ (∑ i, p i) * ‖c.1‖ := by
  simp only [spend, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp i).le
  calc c.1 t i ≤ ‖c.1 t i‖ := Real.le_norm_self _
    _ ≤ ‖c.1 t‖ := norm_le_pi_norm _ i
    _ ≤ ‖c.1‖ := c.1.norm_coe_le_norm t

theorem summable_planCost {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    (c : Seq l) : Summable fun t => R ^ t * spend p (c.1 t) :=
  Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hR0.le t) (spend_nonneg hp (c.2 t)))
    (fun t => mul_le_mul_of_nonneg_left (spend_le_bound hp c t) (pow_nonneg hR0.le t))
    ((summable_geometric_of_lt_one hR0.le hR1).mul_right _)

theorem planCost_nonneg {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (c : Seq l) :
    0 ≤ planCost p R c :=
  tsum_nonneg fun t => mul_nonneg (pow_nonneg hR0.le t) (spend_nonneg hp (c.2 t))

/-- The budget recursion: `Σ Rᵗp·c_t = p·c₀ + R Σ Rᵗp·c_{t+1}`. -/
theorem planCost_eq {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    (c : Seq l) : planCost p R c = spend p (c.1 0) + R * planCost p R (shiftSeq c) := by
  rw [planCost, (summable_planCost hp hR0 hR1 c).tsum_eq_zero_add, planCost, ← tsum_mul_left]
  simp only [pow_zero, one_mul, shiftSeq_apply, pow_succ]
  congr 1
  exact tsum_congr fun t => by ring

/-- `c` is feasible from `A`. -/
def Feasible5 (p : Fin l → ℝ) (R : ℝ) (A : ℝ) (c : Seq l) : Prop := planCost p R c ≤ A

theorem feasible_head {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    {A : Wealth} {c : Seq l} (hc : Feasible5 p R A.1 c) : c.1 0 ∈ budgetΓ p A := by
  refine ⟨c.2 0, ?_⟩
  have := planCost_eq hp hR0 hR1 c
  have := mul_nonneg hR0.le (planCost_nonneg hp hR0 (shiftSeq c))
  unfold Feasible5 at hc
  linarith

theorem feasible_shift {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hR0 : 0 < R) (hR1 : R < 1)
    {A : ℝ} {c : Seq l} (hc : Feasible5 p R A c) :
    Feasible5 p R (nextWealth p R A (c.1 0)) (shiftSeq c) := by
  have := planCost_eq hp hR0 hR1 c
  unfold Feasible5 at hc ⊢
  rw [nextWealth, le_div_iff₀ hR0]
  linarith

/-! ### The value bounds every feasible plan -/

/-- **Exercise 5.12a (Theorems 4.2–4.3, upper half).** With `W` nondecreasing in `z`, every
feasible plan has `u_W(c) ≤ v(A)`. -/
theorem utility_le_value (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    (hW4 : ∀ C, 0 ≤ C → Monotone (W C)) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW) (A : Wealth) (c : Seq l)
    (hc : Feasible5 p R A.1 c) : uW c ≤ v A := by
  set K := ‖uW‖ + ‖v‖
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W p R v) (budgetΓ p) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  have hstep : ∀ n : ℕ, ∀ (A : Wealth) (c : Seq l), Feasible5 p R A.1 c →
      uW c - v A ≤ β ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro A c _
      have h1 := abs_apply_le_norm uW c
      have h2 : |v A| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm A
      have h3 := le_abs_self (uW c)
      have h4 := neg_abs_le (v A)
      rw [pow_zero, one_mul]
      simp only [K]
      linarith
    | succ n ih =>
      intro A c hc
      have hc0 := feasible_head h.p_pos h.R_pos hR1 hc
      set A₁ : Wealth := ⟨nextWealth p R A.1 (c.1 0), mem_Ici.2 (div_nonneg
        (by linarith [hc0.2]) h.R_pos.le)⟩
      have hsc := feasible_shift h.p_pos h.R_pos hR1 hc
      have hIH := ih A₁ (shiftSeq c) hsc
      have hvA : W (c.1 0) (v A₁) ≤ v A := by
        rw [hvx A]
        have := le_maxValue (continuous_consObj h v.continuous).continuousOn
          (budget_compact h.p_pos A) hc0
        have e : vext v (nextWealth p R A.1 (c.1 0)) = v A₁ := vext_of_nonneg v A₁.2
        simp only [consObj] at this
        rw [e] at this
        exact this
      rw [hfe c]
      rcases le_total (uW (shiftSeq c)) (v A₁) with hle | hlt
      · have := hW4 _ (c.2 0) hle
        have : 0 ≤ β ^ (n + 1) * K :=
          mul_nonneg (pow_nonneg h.β_pos.le _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        linarith
      · have hl := h.lip _ (c.2 0) (uW (shiftSeq c)) (v A₁)
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hl
        have := le_abs_self (W (c.1 0) (uW (shiftSeq c)) - W (c.1 0) (v A₁))
        have hb := mul_le_mul_of_nonneg_left hIH h.β_pos.le
        rw [pow_succ]
        nlinarith
  have hlim : Tendsto (fun n => β ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).mul_const K
  have := ge_of_tendsto' hlim fun n => hstep n A c hc
  linarith

/-! ### Plans that follow the policy -/

/-- `(C, c₀, c₁, …)`. -/
noncomputable def consSeq (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l) : Seq l :=
  ⟨BoundedContinuousFunction.mkOfDiscrete (fun t => Nat.casesOn t C fun s => c.1 s)
      (2 * (‖C‖ + ‖c.1‖)) fun s t => by
        have hb : ∀ u : ℕ, ‖(Nat.casesOn u C fun s => c.1 s : Fin l → ℝ)‖ ≤ ‖C‖ + ‖c.1‖ :=
          fun u => by
            cases u with
            | zero =>
              change ‖C‖ ≤ ‖C‖ + ‖c.1‖
              linarith [norm_nonneg c.1]
            | succ s =>
              change ‖c.1 s‖ ≤ ‖C‖ + ‖c.1‖
              linarith [c.1.norm_coe_le_norm s, norm_nonneg C]
        exact (dist_le_norm_add_norm _ _).trans (by linarith [hb s, hb t]),
    fun t => by
      cases t with
      | zero => exact hC
      | succ s => exact c.2 s⟩

theorem consSeq_head (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l) : (consSeq C hC c).1 0 = C := rfl

theorem shiftSeq_consSeq (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l) :
    shiftSeq (consSeq C hC c) = c := Subtype.ext (by ext t i; rfl)

/-- The policy: a maximizer at each wealth level. -/
noncomputable def consPolicy (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    Fin l → ℝ :=
  (exists_consT_argmax h v A).choose

theorem consPolicy_spec (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    consPolicy h v A ∈ budgetΓ p A ∧
      consT h v A = consObj W p R v (A, consPolicy h v A) :=
  ⟨(exists_consT_argmax h v A).choose_spec.1, (exists_consT_argmax h v A).choose_spec.2.1⟩

/-- Next period's wealth under the policy. -/
noncomputable def policyNext (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) : Wealth :=
  ⟨nextWealth p R A.1 (consPolicy h v A), mem_Ici.2 (by
    unfold nextWealth
    exact div_nonneg (by linarith [(consPolicy_spec h v A).1.2]) h.R_pos.le)⟩

/-- Follow the policy for `n + 1` periods, then consume nothing. -/
noncomputable def policyPlan (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) :
    ℕ → Wealth → Seq l
  | 0, A => consSeq (consPolicy h v A) (consPolicy_spec h v A).1.1 zeroSeq
  | n + 1, A => consSeq (consPolicy h v A) (consPolicy_spec h v A).1.1
      (policyPlan h v n (policyNext h v A))

/-- **Exercise 5.12a (lower half).** The truncated policy plans are feasible and come within
`βⁿ⁺¹(‖u_W‖ + ‖v‖)` of `v(A)`. -/
theorem exists_plan_near (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    {v : Wealth →ᵇ ℝ} (hv : consT h v = v) {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW)
    (huz : uW zeroSeq = 0) (n : ℕ) (A : Wealth) :
    Feasible5 p R A.1 (policyPlan h v n A) ∧
      |uW (policyPlan h v n A) - v A| ≤ β ^ (n + 1) * (‖uW‖ + ‖v‖) := by
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  have hvA : ∀ A : Wealth, v A = W (consPolicy h v A) (v (policyNext h v A)) := fun A => by
    have := (consPolicy_spec h v A).2
    rw [hv] at this
    rw [this]
    simp only [consObj]
    have e : vext v (nextWealth p R A.1 (consPolicy h v A)) = v (policyNext h v A) :=
      vext_of_nonneg v (policyNext h v A).2
    rw [e]
  have hcost : ∀ (C : Fin l → ℝ) (hC : 0 ≤ C) (c : Seq l),
      planCost p R (consSeq C hC c) = spend p C + R * planCost p R c := fun C hC c => by
    rw [planCost_eq h.p_pos h.R_pos hR1, consSeq_head, shiftSeq_consSeq]
  have hzero : planCost p R (zeroSeq : Seq l) = 0 := by
    simp [planCost, zeroSeq, spend]
  have hKn : 0 ≤ ‖uW‖ + ‖v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  induction n generalizing A with
  | zero =>
    have hs := (consPolicy_spec h v A).1
    refine ⟨?_, ?_⟩
    · unfold Feasible5
      simp only [policyPlan]
      rw [hcost, hzero, mul_zero, add_zero]
      exact hs.2
    · simp only [policyPlan]
      rw [hfe, consSeq_head, shiftSeq_consSeq, huz, hvA A]
      refine (h.lip _ hs.1 0 _).trans ?_
      rw [zero_sub, abs_neg, zero_add, pow_one]
      have : |v (policyNext h v A)| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using v.norm_coe_le_norm _
      nlinarith [h.β_pos, norm_nonneg uW]
  | succ n ih =>
    have hs := (consPolicy_spec h v A).1
    obtain ⟨hf, hb⟩ := ih (policyNext h v A)
    refine ⟨?_, ?_⟩
    · unfold Feasible5 at hf ⊢
      simp only [policyPlan]
      rw [hcost]
      have hn : (policyNext h v A).1 = nextWealth p R A.1 (consPolicy h v A) := rfl
      rw [hn, nextWealth] at hf
      have := mul_le_mul_of_nonneg_left hf h.R_pos.le
      rw [mul_div_cancel₀ _ h.R_pos.ne'] at this
      linarith
    · simp only [policyPlan]
      rw [hfe, consSeq_head, shiftSeq_consSeq, hvA A]
      refine (h.lip _ hs.1 _ _).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left hb h.β_pos.le

/-- **Exercise 5.12a.** The solution of (2) is the supremum function of (1):
`v(A) = sup{u_W(c) : Σ Rᵗp·c_t ≤ A}`. -/
theorem ex_5_12a (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    (hW4 : ∀ C, 0 ≤ C → Monotone (W C)) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW) (huz : uW zeroSeq = 0) (A : Wealth) :
    v A = sSup (uW '' {c | Feasible5 p R A.1 c}) := by
  have hne : (uW '' {c | Feasible5 p R A.1 c}).Nonempty :=
    ⟨_, zeroSeq, show planCost p R zeroSeq ≤ A.1 by simp [planCost, zeroSeq, spend, A.2.out], rfl⟩
  have hbdd : BddAbove (uW '' {c | Feasible5 p R A.1 c}) := by
    refine ⟨v A, ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    exact utility_le_value h hA hR1 hW4 hv hu A c hc
  have hub : ∀ y ∈ uW '' {c | Feasible5 p R A.1 c}, y ≤ v A := by
    rintro _ ⟨c, hc, rfl⟩
    exact utility_le_value h hA hR1 hW4 hv hu A c hc
  refine le_antisymm ?_ (csSup_le hne hub)
  have hlim : Tendsto (fun n : ℕ => v A - β ^ (n + 1) * (‖uW‖ + ‖v‖)) atTop (𝓝 (v A)) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).comp
      (tendsto_add_atTop_nat 1)).mul_const (‖uW‖ + ‖v‖)
    simpa using (tendsto_const_nhds (x := v A)).sub this
  refine le_of_tendsto' hlim fun n => ?_
  obtain ⟨hf, hb⟩ := exists_plan_near h hA hR1 hv hu huz n A
  have := le_csSup hbdd ⟨_, hf, rfl⟩
  linarith [neg_abs_le (uW (policyPlan h v n A) - v A)]

/-- The wealth path `A₀ = A`, `A_{t+1} = R⁻¹(A_t − p·c_t)`. -/
noncomputable def wealthPath (p : Fin l → ℝ) (R : ℝ) (A : ℝ) (c : Seq l) : ℕ → ℝ
  | 0 => A
  | t + 1 => nextWealth p R (wealthPath p R A c t) (c.1 t)

/-- **Exercise 5.12a (Theorem 4.5).** If `v(A_t) = W(c_t, v(A_{t+1}))` along the wealth path at
every date, then `u_W(c) = v(A)`: the plan is optimal. -/
theorem ex_5_12a_optimal (hA : AggHyp W β M) {v : Wealth →ᵇ ℝ} {uW : Seq l →ᵇ ℝ}
    (hu : opTW hA uW = uW) (A : ℝ) (c : Seq l)
    (hpath : ∀ t, vext v (wealthPath p R A c t) =
      W (c.1 t) (vext v (wealthPath p R A c (t + 1)))) : uW c = vext v A := by
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  set K := ‖uW‖ + ‖v‖
  -- along the shifted plans, `|u_W(ₜc) − v(A_t)| ≤ βⁿK`
  have hpathshift : ∀ (n : ℕ) (A : ℝ) (c : Seq l), (∀ t, vext v (wealthPath p R A c t) =
      W (c.1 t) (vext v (wealthPath p R A c (t + 1)))) →
      |uW c - vext v A| ≤ β ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro A c _
      have h1 := abs_apply_le_norm uW c
      have h2 := abs_vext_le v A
      simp only [pow_zero, one_mul, K]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    | succ n ih =>
      intro A c hp
      have hp' : ∀ t, vext v (wealthPath p R (nextWealth p R A (c.1 0)) (shiftSeq c) t) =
          W ((shiftSeq c).1 t) (vext v (wealthPath p R (nextWealth p R A (c.1 0))
            (shiftSeq c) (t + 1))) := by
        have hw : ∀ t, wealthPath p R (nextWealth p R A (c.1 0)) (shiftSeq c) t =
            wealthPath p R A c (t + 1) := by
          intro t
          induction t with
          | zero => rfl
          | succ t iht => simp only [wealthPath] at iht ⊢; rw [iht]; rfl
        intro t
        rw [hw, hw]
        exact hp (t + 1)
      have hIH := ih _ _ hp'
      rw [hfe c, show vext v A = W (c.1 0) (vext v (wealthPath p R A c 1)) from hp 0]
      refine (hA.lip _ (c.2 0) _ _).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left hIH hA.β_pos.le
  have hlim : Tendsto (fun n => β ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hA.β_pos.le hA.β_lt).mul_const K
  have := ge_of_tendsto' hlim fun n => hpathshift n A c hpath
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- **Exercise 5.12a (Theorem 4.4).** With `W` strictly increasing in `z`, an optimal feasible plan
satisfies (2) at the first date, and its continuation is optimal from next period's wealth. -/
theorem ex_5_12a_necessary (h : ConsHyp W p R β M) (hA : AggHyp W β M) (hR1 : R < 1)
    (hW4 : ∀ C, 0 ≤ C → StrictMono (W C)) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {uW : Seq l →ᵇ ℝ} (hu : opTW hA uW = uW) {A : Wealth} {c : Seq l}
    (hc : Feasible5 p R A.1 c) (hopt : uW c = v A) :
    v A = W (c.1 0) (vext v (nextWealth p R A.1 (c.1 0))) ∧
      uW (shiftSeq c) = vext v (nextWealth p R A.1 (c.1 0)) := by
  have hc0 := feasible_head h.p_pos h.R_pos hR1 hc
  have hA₁ : 0 ≤ nextWealth p R A.1 (c.1 0) := div_nonneg (by linarith [hc0.2]) h.R_pos.le
  set A₁ : Wealth := ⟨_, hA₁⟩
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c => (DFunLike.congr_fun hu c).symm
  have hle := utility_le_value h hA hR1 (fun C hC => (hW4 C hC).monotone) hv hu A₁ (shiftSeq c)
    (feasible_shift h.p_pos h.R_pos hR1 hc)
  have hvA : W (c.1 0) (v A₁) ≤ v A := by
    rw [← DFunLike.congr_fun hv A]
    have := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos A) hc0
    simp only [consObj, vext_of_nonneg v hA₁] at this
    exact this
  have h1 := (hW4 _ (c.2 0)).monotone hle
  rw [← hfe c, hopt] at h1
  have heq : W (c.1 0) (uW (shiftSeq c)) = W (c.1 0) (v A₁) := by
    rw [← hfe c]; linarith
  rw [vext_of_nonneg v hA₁]
  exact ⟨by linarith, (hW4 _ (c.2 0)).injective heq⟩

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A Pareto problem with recursive preferences

SLP §5.13, pp. 117–118: two agents share one unit of a single good each period; agent `i` has
aggregator `W_i` with (W1)–(W3) and utility `u_i` (Exercise 5.11d). One good means `l = 1`;
`cst c` is the bundle `c`. With `I_i = [u_i(0), u_i(1)] = [0, b_i]`,
`(Tf)(x) = max {W₁[c, f(y)] : c ∈ [0, 1], y ∈ I₂, W₂(1 − c, y) ≥ x}`.

Assume both aggregators are nondecreasing (W4) and `W₂` is strictly increasing in each argument.

* `isLHC_of_approx`: a correspondence is l.h.c. at `x` when every point of `Γ(x)` is a limit of
  points that stay feasible near `x` (a Slater condition). `pareto_lhc`, `pareto_uhc`: the
  constraint set is continuous.
* **Exercise 5.13a** (`ex_5_13a`): `T` maps the continuous functions `I₂ → I₁` into themselves
  and is a contraction of modulus `β₁`; so it has a unique fixed point `v`.
* **Exercise 5.13b** (`ex_5_13b`): `v = v*`: for `x ∈ I₂`,
  `v(x) = sup{u₁(c) : 0 ≤ c_t ≤ 1, u₂(1 − c) ≥ x}`, and the supremum is attained by the plan
  that follows the maximizers of `T`. `v` is the Pareto frontier.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- A correspondence is l.h.c. at `x` if every `w ∈ Γ(x)` is approximated by points that remain
feasible for all `x'` near `x`. -/
theorem isLHC_of_approx {X Y : Type*} [MetricSpace X] [MetricSpace Y] {Γ : X → Set Y} {x : X}
    (hne : (Γ x).Nonempty)
    (h : ∀ w ∈ Γ x, ∀ ε > 0, ∃ w', dist w' w < ε ∧ ∀ᶠ x' in 𝓝 x, w' ∈ Γ x') :
    IsLHC Γ x := by
  refine ⟨hne, fun w hw xs hxs => ?_⟩
  choose w' hw'd hw'ev using fun k : ℕ => h w hw (1 / ((k : ℝ) + 1)) (by positivity)
  have hN : ∀ k, ∃ N, ∀ n ≥ N, w' k ∈ Γ (xs n) := fun k =>
    eventually_atTop.1 (hxs.eventually (hw'ev k))
  choose N hN using hN
  classical
  set K : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  refine ⟨N 0, fun n => w' (K n), fun n hn => hN (K n) n
    (Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0) (Nat.zero_le n) hn), ?_⟩
  have hK : Tendsto K atTop atTop := tendsto_atTop_atTop.2 fun k =>
    ⟨max k (N k), fun n hn => Nat.le_findGreatest (le_of_max_le_left hn)
      (le_of_max_le_right hn)⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hw'd (K n)).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hK)

/-- The bundle with `c` units of the single good. -/
def cst (c : ℝ) : Fin 1 → ℝ := fun _ => c

theorem cst_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cst c := fun _ => hc

theorem cst_le {c c' : ℝ} (h : c ≤ c') : cst c ≤ cst c' := fun _ => h

variable {W₁ W₂ : (Fin 1 → ℝ) → ℝ → ℝ} {β₁ β₂ M₁ M₂ : ℝ}

/-- The hypotheses of SLP §5.13 used here. -/
structure ParetoHyp (W₁ W₂ : (Fin 1 → ℝ) → ℝ → ℝ) (β₁ β₂ M₁ M₂ : ℝ) : Prop where
  h1 : AggHyp W₁ β₁ M₁
  h2 : AggHyp W₂ β₂ M₂
  mono1 : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W₁ x z ≤ W₁ x' z'
  mono2 : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W₂ x z ≤ W₂ x' z'
  strict2c : ∀ c c' z, 0 ≤ c → c < c' → W₂ (cst c) z < W₂ (cst c') z
  strict2z : ∀ c z z', 0 ≤ c → z < z' → W₂ (cst c) z < W₂ (cst c) z'

/-- The constant sequence `1`. -/
def oneSeq : Seq 1 := ⟨BoundedContinuousFunction.const ℕ (cst 1), fun _ _ => zero_le_one⟩

theorem shiftSeq_one : shiftSeq oneSeq = oneSeq := Subtype.ext (by ext t i; rfl)

/-- The fixed-point equations `u(0) = 0` and `u(1) = W(1, u(1))`, and monotonicity: `0 ≤ u(1)`. -/
theorem utility_one {W : (Fin 1 → ℝ) → ℝ → ℝ} {β M : ℝ} (h : AggHyp W β M)
    (hmono : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W x z ≤ W x' z') {u : Seq 1 →ᵇ ℝ}
    (hu : opTW h u = u) : u oneSeq = W (cst 1) (u oneSeq) ∧ 0 ≤ u oneSeq ∧
      ∀ c, u zeroSeq ≤ u c := by
  obtain ⟨u', hu', huniq, hz, -⟩ := ex_5_11d h
  have hu'' := huniq u hu
  subst hu''
  have hfe := (DFunLike.congr_fun hu oneSeq).symm
  rw [opTW_apply, shiftSeq_one] at hfe
  refine ⟨hfe, ?_, fun c => ex_5_11d_mono h hmono hu fun t => c.2 t⟩
  rw [← hz]
  exact ex_5_11d_mono h hmono hu fun t => oneSeq.2 t

/-! ### The operator -/

variable {u₁ u₂ : Seq 1 →ᵇ ℝ}

/-- `I₂ = [0, b₂]`, `b₂ = u₂(1)`. -/
abbrev I2 (u₂ : Seq 1 →ᵇ ℝ) := ↥(Icc (0 : ℝ) (u₂ oneSeq))

/-- The constraint set `{(c, y) : 0 ≤ c ≤ 1, W₂(1 − c, y) ≥ x}`. -/
def paretoΦ (W₂ : (Fin 1 → ℝ) → ℝ → ℝ) (u₂ : Seq 1 →ᵇ ℝ) (x : I2 u₂) : Set (ℝ × I2 u₂) :=
  {w | w.1 ∈ Icc (0 : ℝ) 1 ∧ x.1 ≤ W₂ (cst (1 - w.1)) w.2.1}

/-- The objective `W₁(c, f(y))`. -/
def paretoObj (W₁ : (Fin 1 → ℝ) → ℝ → ℝ) (f : I2 u₂ → ℝ) (q : I2 u₂ × (ℝ × I2 u₂)) : ℝ :=
  W₁ (cst q.2.1) (f q.2.2)

theorem continuous_cst : Continuous cst := continuous_pi fun _ => continuous_id

theorem pareto_top_mem (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) (x : I2 u₂) :
    ((0 : ℝ), (⟨u₂ oneSeq, (utility_one h.h2 h.mono2 hu₂).2.1, le_rfl⟩ : I2 u₂)) ∈
      paretoΦ W₂ u₂ x := by
  refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
  simp only [sub_zero]
  rw [← (utility_one h.h2 h.mono2 hu₂).1]
  exact x.2.2

theorem pareto_compact (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (x : I2 u₂) :
    IsCompact (paretoΦ W₂ u₂ x) := by
  have : CompactSpace (I2 u₂) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hc : Continuous fun w : ℝ × I2 u₂ => W₂ (cst (1 - w.1)) w.2.1 :=
    h.h2.cont.comp ((continuous_cst.comp (continuous_const.sub continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  refine (isCompact_Icc.prod (isCompact_univ (X := I2 u₂))).of_isClosed_subset ?_
    fun w hw => ⟨hw.1, mem_univ _⟩
  exact ((isClosed_Icc.preimage continuous_fst)).inter (isClosed_le continuous_const hc)

theorem pareto_uhc (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) (x : I2 u₂) :
    IsUHC (paretoΦ W₂ u₂) x := by
  have : CompactSpace (I2 u₂) := isCompact_iff_compactSpace.1 isCompact_Icc
  refine ⟨⟨_, pareto_top_mem h hu₂ x⟩, fun xs hxs ws hws => ?_⟩
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_Icc.prod (isCompact_univ (X := I2 u₂))).tendsto_subseq
    (x := ws) fun n => ⟨(hws n).1, mem_univ _⟩
  have hc : Continuous fun w : ℝ × I2 u₂ => W₂ (cst (1 - w.1)) w.2.1 :=
    h.h2.cont.comp ((continuous_cst.comp (continuous_const.sub continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨w, ⟨hw.1, ?_⟩, φ, hφ, hlim⟩
  exact le_of_tendsto_of_tendsto (((continuous_subtype_val.tendsto x).comp hxs).comp
    hφ.tendsto_atTop) ((hc.tendsto w).comp hlim) (Eventually.of_forall fun n => (hws (φ n)).2)

theorem pareto_lhc (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) (x : I2 u₂) :
    IsLHC (paretoΦ W₂ u₂) x := by
  refine isLHC_of_approx ⟨_, pareto_top_mem h hu₂ x⟩ fun w hw ε hε => ?_
  have hc : Continuous fun w : ℝ × I2 u₂ => W₂ (cst (1 - w.1)) w.2.1 :=
    h.h2.cont.comp ((continuous_cst.comp (continuous_const.sub continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  -- a strictly feasible point stays feasible near `x`
  have hstrict : ∀ w' : ℝ × I2 u₂, w'.1 ∈ Icc (0 : ℝ) 1 → x.1 < W₂ (cst (1 - w'.1)) w'.2.1 →
      ∀ᶠ x' in 𝓝 x, w' ∈ paretoΦ W₂ u₂ x' := fun w' hw'1 hw' => by
    have := ((continuous_subtype_val.tendsto x).eventually (gt_mem_nhds hw'))
    filter_upwards [this] with x' hx'
    exact ⟨hw'1, hx'.le⟩
  rcases lt_or_eq_of_le hw.2 with hlt | heq
  · exact ⟨w, by simpa using hε, hstrict w hw.1 hlt⟩
  rcases eq_or_lt_of_le hw.1.1 with hc0 | hcpos
  · -- `c = 0`: raise `y` unless it is already at the top
    have hb : (0 : ℝ) ≤ u₂ oneSeq := (utility_one h.h2 h.mono2 hu₂).2.1
    rcases eq_or_lt_of_le w.2.2.2 with htop | hylt
    · refine ⟨w, by simpa using hε, Eventually.of_forall fun x' => ⟨hw.1, ?_⟩⟩
      rw [← hc0, sub_zero, htop, ← (utility_one h.h2 h.mono2 hu₂).1]
      exact x'.2.2
    · set δ := min (ε / 2) (u₂ oneSeq - w.2.1)
      have hδ : 0 < δ := lt_min (by linarith) (by linarith)
      set y' : I2 u₂ := ⟨w.2.1 + δ, by linarith [w.2.2.1], by
        linarith [min_le_right (ε / 2) (u₂ oneSeq - w.2.1)]⟩
      refine ⟨(w.1, y'), ?_, hstrict (w.1, y') hw.1 ?_⟩
      · rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Real.dist_eq]
        simp only [y', add_sub_cancel_left, abs_of_pos hδ]
        exact max_lt hε (lt_of_le_of_lt (min_le_left _ _) (by linarith))
      · rw [heq]
        exact h.strict2z _ _ _ (by linarith [hw.1.2]) (by simp [y', hδ])
  · -- `c > 0`: give agent 2 a little more
    set δ := min (ε / 2) w.1
    have hδ : 0 < δ := lt_min (by linarith) hcpos
    refine ⟨(w.1 - δ, w.2), ?_, hstrict (w.1 - δ, w.2) ⟨by linarith [min_le_right (ε / 2) w.1],
      by linarith [hw.1.2]⟩ ?_⟩
    · rw [Prod.dist_eq, dist_self, Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
      exact max_lt (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hε
    · rw [heq]
      exact h.strict2c _ _ _ (by linarith [hw.1.2]) (by linarith)

theorem continuous_paretoObj (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) {f : I2 u₂ → ℝ}
    (hf : Continuous f) : Continuous (paretoObj (u₂ := u₂) W₁ f) :=
  h.h1.cont.comp ((continuous_cst.comp (continuous_fst.comp continuous_snd)).prodMk
    (hf.comp (continuous_snd.comp continuous_snd)))

theorem abs_paretoObj_le (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (f : I2 u₂ →ᵇ ℝ)
    {q : I2 u₂ × (ℝ × I2 u₂)} (hq : q.2.1 ∈ Icc (0 : ℝ) 1) :
    |paretoObj W₁ f q| ≤ M₁ + β₁ * ‖f‖ := by
  have h1 := h.h1.lip _ (cst_nonneg hq.1) (f q.2.2) 0
  have h2 := h.h1.bdd _ (cst_nonneg hq.1)
  have h3 : |f q.2.2| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm q.2.2
  rw [sub_zero] at h1
  have := abs_sub_abs_le_abs_sub (W₁ (cst q.2.1) (f q.2.2)) (W₁ (cst q.2.1) 0)
  simp only [paretoObj]
  nlinarith [h.h1.β_pos]

/-- `(Tf)(x) = max {W₁[c, f(y)] : (c, y) ∈ Φ(x)}`. -/
noncomputable def paretoT (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (f : I2 u₂ →ᵇ ℝ) : I2 u₂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => maxValue (paretoObj W₁ f) (paretoΦ W₂ u₂) x)
    (theorem_3_6 (continuous_paretoObj h f.continuous).continuousOn (pareto_compact h)
      (pareto_lhc h hu₂) (pareto_uhc h hu₂)).1 (M₁ + β₁ * ‖f‖) fun x => by
        obtain ⟨w, hw, hval, -⟩ := exists_argmax (continuous_paretoObj h f.continuous).continuousOn
          (pareto_compact h x) ⟨_, pareto_top_mem h hu₂ x⟩
        rw [← hval, Real.norm_eq_abs]
        exact abs_paretoObj_le h f hw.1

theorem exists_paretoT_argmax (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (f : I2 u₂ →ᵇ ℝ) (x : I2 u₂) :
    ∃ w ∈ paretoΦ W₂ u₂ x, paretoT h hu₂ f x = W₁ (cst w.1) (f w.2) ∧
      ∀ w' ∈ paretoΦ W₂ u₂ x, W₁ (cst w'.1) (f w'.2) ≤ paretoT h hu₂ f x := by
  obtain ⟨w, hw, hval, hmax⟩ := exists_argmax (continuous_paretoObj h f.continuous).continuousOn
    (pareto_compact h x) ⟨_, pareto_top_mem h hu₂ x⟩
  exact ⟨w, hw, hval.symm, fun w' hw' => (hmax w' hw').trans_eq hval⟩

theorem paretoT_contraction (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) :
    IsContraction (paretoT h hu₂) β₁ := by
  refine ⟨h.h1.β_pos, h.h1.β_lt, fun f g => (dist_le (mul_nonneg h.h1.β_pos.le
    dist_nonneg)).2 fun x => ?_⟩
  obtain ⟨w, hw, hval, hmax⟩ := exists_paretoT_argmax h hu₂ f x
  obtain ⟨w', hw', hval', hmax'⟩ := exists_paretoT_argmax h hu₂ g x
  have e1 := hmax w' hw'
  have e2 := hmax' w hw
  have l1 := h.h1.lip _ (cst_nonneg hw.1.1) (f w.2) (g w.2)
  have l2 := h.h1.lip _ (cst_nonneg hw'.1.1) (f w'.2) (g w'.2)
  have d1 := mul_le_mul_of_nonneg_left (show |f w.2 - g w.2| ≤ dist f g by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := f) (g := g) w.2) h.h1.β_pos.le
  have d2 := mul_le_mul_of_nonneg_left (show |f w'.2 - g w'.2| ≤ dist f g by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := f) (g := g) w'.2) h.h1.β_pos.le
  rw [Real.dist_eq, abs_le]
  rw [abs_le] at l1 l2
  constructor <;> linarith [l1.1, l1.2, l2.1, l2.2]

/-- **Exercise 5.13a.** `T` maps the continuous functions `I₂ → I₁ = [0, b₁]` into themselves and
is a contraction; it has a unique fixed point there. -/
theorem ex_5_13a (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₁ : opTW h.h1 u₁ = u₁)
    (hu₂ : opTW h.h2 u₂ = u₂) :
    IsContraction (paretoT h hu₂) β₁ ∧
      (∀ f : I2 u₂ →ᵇ ℝ, (∀ y, f y ∈ Icc 0 (u₁ oneSeq)) →
        ∀ x, paretoT h hu₂ f x ∈ Icc 0 (u₁ oneSeq)) ∧
      ∃ v : I2 u₂ →ᵇ ℝ, paretoT h hu₂ v = v ∧ (∀ y, v y ∈ Icc 0 (u₁ oneSeq)) ∧
        ∀ w, paretoT h hu₂ w = w → w = v := by
  have hmaps : ∀ f : I2 u₂ →ᵇ ℝ, (∀ y, f y ∈ Icc 0 (u₁ oneSeq)) →
      ∀ x, paretoT h hu₂ f x ∈ Icc 0 (u₁ oneSeq) := fun f hf x => by
    obtain ⟨w, hw, hval, -⟩ := exists_paretoT_argmax h hu₂ f x
    rw [hval]
    have h0 : W₁ 0 0 = 0 := h.h1.zero
    refine ⟨?_, ?_⟩
    · have := h.mono1 0 (cst w.1) 0 (f w.2) le_rfl (cst_nonneg hw.1.1) (hf _).1
      rw [h0] at this
      exact this
    · rw [(utility_one h.h1 h.mono1 hu₁).1]
      exact h.mono1 _ _ _ _ (cst_nonneg hw.1.1) (cst_le hw.1.2) (hf _).2
  have : Nonempty (I2 u₂ →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (paretoT_contraction h hu₂)
  set S : Set (I2 u₂ →ᵇ ℝ) := {f | ∀ y, f y ∈ Icc 0 (u₁ oneSeq)}
  have hclosed : IsClosed S := by
    have : S = ⋂ y, {f : I2 u₂ →ᵇ ℝ | f y ∈ Icc 0 (u₁ oneSeq)} := by ext f; simp [S]
    rw [this]
    exact isClosed_iInter fun y => isClosed_Icc.preimage (continuous_eval_const y)
  have hb : 0 ≤ u₁ oneSeq := (utility_one h.h1 h.mono1 hu₁).2.1
  have hvS : v ∈ S := (corollary_1 (S' := S) (S'' := S) (paretoT_contraction h hu₂) hv
    ⟨0, fun _ => ⟨le_rfl, hb⟩⟩ hclosed (fun f hf => hmaps f hf) (fun f hf => hmaps f hf)).1
  exact ⟨paretoT_contraction h hu₂, hmaps, v, hv, hvS, huniq⟩

/-! ### Exercise 5.13b: the fixed point is the Pareto frontier -/

/-- `1 − c` for a sequence with `c_t ≤ 1`. -/
def oneMinus (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) : Seq 1 :=
  ⟨BoundedContinuousFunction.const ℕ (cst 1) - c.1, fun t => sub_nonneg.2 (hc t)⟩

theorem shiftSeq_oneMinus (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) :
    shiftSeq (oneMinus c hc) = oneMinus (shiftSeq c) fun t => hc (t + 1) :=
  Subtype.ext (by ext t i; rfl)

theorem head_oneMinus (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) :
    (oneMinus c hc).1 0 = cst (1 - c.1 0 0) := by
  ext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  rfl

theorem head_eq_cst (c : Seq 1) (t : ℕ) : c.1 t = cst (c.1 t 0) := by
  ext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  rfl

theorem utility_zero {W : (Fin 1 → ℝ) → ℝ → ℝ} {β M : ℝ} (h : AggHyp W β M) {u : Seq 1 →ᵇ ℝ}
    (hu : opTW h u = u) : u zeroSeq = 0 := by
  obtain ⟨u', -, huniq, hz, -⟩ := ex_5_11d h
  rw [huniq u hu]; exact hz

/-- Utilities of allocations with `c_t ≤ 1` lie in `I = [0, u(1)]`. -/
theorem utility_range {W : (Fin 1 → ℝ) → ℝ → ℝ} {β M : ℝ} (h : AggHyp W β M)
    (hmono : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W x z ≤ W x' z') {u : Seq 1 →ᵇ ℝ}
    (hu : opTW h u = u) (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) : u c ∈ Icc 0 (u oneSeq) :=
  ⟨(utility_zero h hu) ▸ (utility_one h hmono hu).2.2 c, ex_5_11d_mono h hmono hu hc⟩

theorem oneMinus_le (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) (t : ℕ) :
    (oneMinus c hc).1 t ≤ cst 1 := fun i => by
  have := c.2 t i
  simp only [Pi.zero_apply] at this
  change (1 : ℝ) - c.1 t i ≤ 1
  linarith

/-- **Exercise 5.13b (upper half).** Every allocation with `c_t ≤ 1` that gives agent 2 at least
`x` gives agent 1 at most `v(x)`. -/
theorem pareto_le_value (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₁ : opTW h.h1 u₁ = u₁)
    (hu₂ : opTW h.h2 u₂ = u₂) {v : I2 u₂ →ᵇ ℝ} (hv : paretoT h hu₂ v = v) (x : I2 u₂)
    (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) (hx : x.1 ≤ u₂ (oneMinus c hc)) : u₁ c ≤ v x := by
  set K := ‖u₁‖ + ‖v‖
  have hfe₁ : ∀ c, u₁ c = W₁ (c.1 0) (u₁ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₁ c).symm
  have hfe₂ : ∀ c, u₂ c = W₂ (c.1 0) (u₂ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₂ c).symm
  have hstep : ∀ n : ℕ, ∀ (x : I2 u₂) (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1),
      x.1 ≤ u₂ (oneMinus c hc) → u₁ c - v x ≤ β₁ ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro x c hc _
      have h1 := abs_apply_le_norm u₁ c
      have h2 : |v x| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm x
      have h3 := le_abs_self (u₁ c)
      have h4 := neg_abs_le (v x)
      rw [pow_zero, one_mul]
      simp only [K]
      linarith
    | succ n ih =>
      intro x c hc hx
      have hsc : ∀ t, (shiftSeq c).1 t ≤ cst 1 := fun t => hc (t + 1)
      set y : I2 u₂ := ⟨u₂ (oneMinus (shiftSeq c) hsc), utility_range h.h2 h.mono2 hu₂ _
        (oneMinus_le _ hsc)⟩
      have hc0 : c.1 0 0 ∈ Icc (0 : ℝ) 1 := ⟨c.2 0 0, hc 0 0⟩
      have hmem : (c.1 0 0, y) ∈ paretoΦ W₂ u₂ x := by
        refine ⟨hc0, ?_⟩
        have e := hfe₂ (oneMinus c hc)
        rw [head_oneMinus, shiftSeq_oneMinus] at e
        rw [e] at hx
        exact hx
      have hvx : W₁ (cst (c.1 0 0)) (v y) ≤ v x := by
        obtain ⟨-, -, -, hmax⟩ := exists_paretoT_argmax h hu₂ v x
        rw [hv] at hmax
        exact hmax _ hmem
      have hIH := ih y (shiftSeq c) hsc le_rfl
      rw [hfe₁ c, head_eq_cst c 0]
      rcases le_total (u₁ (shiftSeq c)) (v y) with hle | hlt
      · have := h.mono1 _ _ _ _ (cst_nonneg hc0.1) le_rfl hle
        have : 0 ≤ β₁ ^ (n + 1) * K :=
          mul_nonneg (pow_nonneg h.h1.β_pos.le _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        linarith
      · have hl := h.h1.lip _ (cst_nonneg hc0.1) (u₁ (shiftSeq c)) (v y)
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hl
        have := le_abs_self (W₁ (cst (c.1 0 0)) (u₁ (shiftSeq c)) - W₁ (cst (c.1 0 0)) (v y))
        have hb := mul_le_mul_of_nonneg_left hIH h.h1.β_pos.le
        rw [pow_succ]
        nlinarith
  have hlim : Tendsto (fun n => β₁ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.h1.β_pos.le h.h1.β_lt).mul_const K
  have := ge_of_tendsto' hlim fun n => hstep n x c hc hx
  linarith

/-- The maximizers of `T` at the fixed point. -/
noncomputable def paretoPol (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) : ℝ × I2 u₂ :=
  (exists_paretoT_argmax h hu₂ v x).choose

/-- The allocation that follows the maximizers: `c_t` is the first component of the maximizer at
`x_t`, and `x_{t+1}` the second. -/
noncomputable def paretoPlan (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) : Seq 1 :=
  ⟨BoundedContinuousFunction.mkOfDiscrete
      (fun t => cst (paretoPol h hu₂ v ((fun y => (paretoPol h hu₂ v y).2)^[t] x)).1) 2
      fun s t => by
        have hb : ∀ u : ℕ, ‖cst (paretoPol h hu₂ v ((fun y => (paretoPol h hu₂ v y).2)^[u] x)).1‖
            ≤ 1 := fun u => by
          have hm : (paretoPol h hu₂ v ((fun y => (paretoPol h hu₂ v y).2)^[u] x)).1 ∈
              Icc (0 : ℝ) 1 := (exists_paretoT_argmax h hu₂ v
            ((fun y => (paretoPol h hu₂ v y).2)^[u] x)).choose_spec.1.1
          refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
          rw [Real.norm_eq_abs, abs_le]
          simp only [cst]
          exact ⟨by linarith [hm.1], hm.2⟩
        exact (dist_le_norm_add_norm _ _).trans (by linarith [hb s, hb t]),
    fun t => cst_nonneg ((exists_paretoT_argmax h hu₂ v
      ((fun y => (paretoPol h hu₂ v y).2)^[t] x)).choose_spec.1.1.1)⟩

theorem paretoPlan_le (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) (t : ℕ) : (paretoPlan h hu₂ v x).1 t ≤ cst 1 :=
  cst_le ((exists_paretoT_argmax h hu₂ v
    ((fun y => (paretoPol h hu₂ v y).2)^[t] x)).choose_spec.1.1.2)

theorem shiftSeq_paretoPlan (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) :
    shiftSeq (paretoPlan h hu₂ v x) = paretoPlan h hu₂ v (paretoPol h hu₂ v x).2 :=
  Subtype.ext (by
    ext t i
    simp only [shiftSeq_apply, paretoPlan, BoundedContinuousFunction.mkOfDiscrete_apply,
      Function.iterate_succ_apply])

theorem head_paretoPlan (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) :
    (paretoPlan h hu₂ v x).1 0 = cst (paretoPol h hu₂ v x).1 := rfl

/-- **Exercise 5.13b.** The fixed point of `T` is the Pareto frontier:
`v(x) = max{u₁(c) : 0 ≤ c_t ≤ 1, u₂(1 − c) ≥ x}`, attained by the allocation that follows the
maximizers of `T`. -/
theorem ex_5_13b (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₁ : opTW h.h1 u₁ = u₁)
    (hu₂ : opTW h.h2 u₂ = u₂) {v : I2 u₂ →ᵇ ℝ} (hv : paretoT h hu₂ v = v) (x : I2 u₂) :
    IsGreatest {r | ∃ c : Seq 1, ∃ hc : ∀ t, c.1 t ≤ cst 1,
      x.1 ≤ u₂ (oneMinus c hc) ∧ r = u₁ c} (v x) ∧
    v x = sSup {r | ∃ c : Seq 1, ∃ hc : ∀ t, c.1 t ≤ cst 1,
      x.1 ≤ u₂ (oneMinus c hc) ∧ r = u₁ c} := by
  have hfe₁ : ∀ c, u₁ c = W₁ (c.1 0) (u₁ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₁ c).symm
  have hfe₂ : ∀ c, u₂ c = W₂ (c.1 0) (u₂ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₂ c).symm
  have hspec : ∀ y : I2 u₂, paretoPol h hu₂ v y ∈ paretoΦ W₂ u₂ y ∧
      v y = W₁ (cst (paretoPol h hu₂ v y).1) (v (paretoPol h hu₂ v y).2) := fun y => by
    have := (exists_paretoT_argmax h hu₂ v y).choose_spec
    exact ⟨this.1, (DFunLike.congr_fun hv y).symm.trans this.2.1⟩
  -- the plan attains `v`
  have hval : ∀ n : ℕ, ∀ y : I2 u₂,
      |u₁ (paretoPlan h hu₂ v y) - v y| ≤ β₁ ^ n * (‖u₁‖ + ‖v‖) := by
    intro n
    induction n with
    | zero =>
      intro y
      have h1 := abs_apply_le_norm u₁ (paretoPlan h hu₂ v y)
      have h2 : |v y| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm y
      rw [pow_zero, one_mul]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    | succ n ih =>
      intro y
      rw [hfe₁, head_paretoPlan, shiftSeq_paretoPlan, (hspec y).2]
      refine (h.h1.lip _ (cst_nonneg (hspec y).1.1.1) _ _).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih _) h.h1.β_pos.le
  -- and it gives agent 2 at least `x`
  have hfeas : ∀ n : ℕ, ∀ y : I2 u₂, y.1 - u₂ (oneMinus (paretoPlan h hu₂ v y)
      (paretoPlan_le h hu₂ v y)) ≤ β₂ ^ n * (2 * ‖u₂‖) := by
    intro n
    induction n with
    | zero =>
      intro y
      have h1 := abs_apply_le_norm u₂ (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y))
      have h2 : y.1 ≤ ‖u₂‖ := y.2.2.trans ((le_abs_self _).trans (abs_apply_le_norm u₂ oneSeq))
      rw [pow_zero, one_mul]
      linarith [neg_abs_le (u₂ (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y)))]
    | succ n ih =>
      intro y
      set y' := (paretoPol h hu₂ v y).2
      have hcons := (hspec y).1.2
      have hc0 := (hspec y).1.1
      have hshift : shiftSeq (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y)) =
          oneMinus (paretoPlan h hu₂ v y') (paretoPlan_le h hu₂ v y') :=
        Subtype.ext (by ext t i; rfl)
      have e := hfe₂ (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y))
      rw [head_oneMinus, hshift] at e
      rw [e]
      have hIH := ih y'
      set z := u₂ (oneMinus (paretoPlan h hu₂ v y') (paretoPlan_le h hu₂ v y'))
      have hhead : (paretoPlan h hu₂ v y).1 0 0 = (paretoPol h hu₂ v y).1 := rfl
      rw [hhead]
      have hc1 : 0 ≤ cst (1 - (paretoPol h hu₂ v y).1) := cst_nonneg (by linarith [hc0.2])
      rcases le_total y'.1 z with hle | hlt
      · have := h.mono2 _ _ _ _ hc1 le_rfl hle
        have : 0 ≤ β₂ ^ (n + 1) * (2 * ‖u₂‖) :=
          mul_nonneg (pow_nonneg h.h2.β_pos.le _) (by positivity)
        linarith
      · have hl := h.h2.lip _ hc1 y'.1 z
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hl
        have := le_abs_self (W₂ (cst (1 - (paretoPol h hu₂ v y).1)) y'.1 -
          W₂ (cst (1 - (paretoPol h hu₂ v y).1)) z)
        have hb := mul_le_mul_of_nonneg_left hIH h.h2.β_pos.le
        rw [pow_succ]
        nlinarith
  have hlim : ∀ K : ℝ, ∀ {b : ℝ}, 0 < b → b < 1 → Tendsto (fun n => b ^ n * K) atTop (𝓝 0) :=
    fun K b hb0 hb1 => by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).mul_const K
  have hattain : u₁ (paretoPlan h hu₂ v x) = v x := by
    have := ge_of_tendsto' (hlim _ h.h1.β_pos h.h1.β_lt) fun n => hval n x
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  have hfx : x.1 ≤ u₂ (oneMinus (paretoPlan h hu₂ v x) (paretoPlan_le h hu₂ v x)) := by
    have := ge_of_tendsto' (hlim _ h.h2.β_pos h.h2.β_lt) fun n => hfeas n x
    linarith
  have hG : IsGreatest {r | ∃ c : Seq 1, ∃ hc : ∀ t, c.1 t ≤ cst 1,
      x.1 ≤ u₂ (oneMinus c hc) ∧ r = u₁ c} (v x) :=
    ⟨⟨_, paretoPlan_le h hu₂ v x, hfx, hattain.symm⟩, by
      rintro _ ⟨c, hc, hcx, rfl⟩
      exact pareto_le_value h hu₁ hu₂ hv x c hc hcx⟩
  exact ⟨hG, hG.csSup_eq.symm⟩

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An (s, S) inventory problem

SLP §5.14, pp. 118–122: a manager sells up to one unit per period at price `p`, can order `y`
units for delivery next period at cost `c₀ + c₁y`, and discounts at `β = 1/(1 + r)`; `βp > c₁ > 0`,
`c₀ > 0`. With stock `x`, sales are `min{x, 1}` and the stock left is `z(x) = max{x − 1, 0}`, so
(1) reads `v(x) = p·min{x, 1} + max{βv(z), sup_{y > 0} [−c₀ − c₁y + βv(z + y)]}`.

* **Exercise 5.14a** (`ex_5_14a`): the operator `T` of (1) maps `C(ℝ₊)` into itself (the supremum
  over `y > 0` equals a maximum over a compact interval, `ordSup_eq`), satisfies Blackwell's
  conditions, and has a unique fixed point `v`, with `0 ≤ v ≤ p/(1 − β)`; and an optimal ordering
  policy exists (`ex_5_14a_policy`): at every `x` either not ordering is optimal or some `y > 0`
  attains the supremum.
* **Exercise 5.14b**: `r_n = −c₀ − c₁n + β(1 − βⁿ)p/(1 − β)` and
  `Y_n = r_n/(1 − βⁿ) = −(c₀ + c₁n)/(1 − βⁿ) + βp/(1 − β)` (`Yn_eq`); `Y_n → −∞`
  (`tendsto_Yn`), so some finite `N ≥ 1` maximizes `Y_n` (`ex_5_14b`). The maximizers do not
  depend on `p` (`argmax_Yn_indep_p`), and `N` rises with the fixed cost `c₀`
  (`argmax_Yn_mono_c0`, increasing differences) and with the discount factor `β`
  (`argmax_Yn_mono_beta`).
* **Exercise 5.14c** (`ex_5_14c`): if `Y_N > 0`, then `A = (1 − β)Y_N/(βp − c₁)` lies in `(0, 1)`;
  in fact `A < 1` for every `N ≥ 1`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- Inventories `x ≥ 0`. -/
abbrev Stock := ↥(Ici (0 : ℝ))

/-- `f` on stocks extended to `ℝ` by `f(max{x, 0})`. -/
def sext (f : Stock → ℝ) (x : ℝ) : ℝ := f ⟨max x 0, mem_Ici.2 (le_max_right _ _)⟩

theorem sext_of_nonneg (f : Stock → ℝ) {x : ℝ} (hx : 0 ≤ x) : sext f x = f ⟨x, hx⟩ := by
  simp only [sext, max_eq_left hx]

theorem continuous_sext {f : Stock → ℝ} (hf : Continuous f) : Continuous (sext f) :=
  hf.comp ((continuous_id.max continuous_const).subtype_mk _)

theorem abs_sext_le (f : Stock →ᵇ ℝ) (x : ℝ) : |sext f x| ≤ ‖f‖ := by
  unfold sext
  simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _

/-- The stock left after sales, `z(x) = max{x − 1, 0}`. -/
def leftover (x : ℝ) : ℝ := max (x - 1) 0

variable {p c₀ c₁ β : ℝ}

/-- The value of ordering `y`: `−c₀ − c₁y + βf(z + y)`. -/
def orderVal (c₀ c₁ β : ℝ) (f : Stock → ℝ) (z y : ℝ) : ℝ := -c₀ - c₁ * y + β * sext f (z + y)

/-- `sup_{y > 0} [−c₀ − c₁y + βf(z + y)]`. -/
noncomputable def ordSup (c₀ c₁ β : ℝ) (f : Stock → ℝ) (z : ℝ) : ℝ :=
  sSup (orderVal c₀ c₁ β f z '' Ioi 0)

/-- The hypotheses of SLP §5.14. -/
structure InvHyp (p c₀ c₁ β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  c₀_pos : 0 < c₀
  c₁_pos : 0 < c₁
  margin : c₁ < β * p

theorem InvHyp.p_pos (h : InvHyp p c₀ c₁ β) : 0 < p := by
  by_contra hp; push Not at hp; nlinarith [h.β_pos, h.c₁_pos, h.margin]

theorem orderVal_le (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) {z y : ℝ} (hy : 0 ≤ y) :
    orderVal c₀ c₁ β f z y ≤ -c₀ + β * ‖f‖ := by
  have := abs_sext_le f (z + y)
  have := mul_le_mul_of_nonneg_left ((le_abs_self _).trans this) h.β_pos.le
  simp only [orderVal]
  nlinarith [h.c₁_pos]

theorem bddAbove_ordSup (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) :
    BddAbove (orderVal c₀ c₁ β f z '' Ioi 0) :=
  ⟨-c₀ + β * ‖f‖, by rintro _ ⟨y, hy, rfl⟩; exact orderVal_le h f (le_of_lt hy)⟩

/-- The order horizon `Y = 2β‖f‖/c₁ + 1`: larger orders never beat not ordering. -/
noncomputable def horizon (c₁ β : ℝ) (f : Stock →ᵇ ℝ) : ℝ := 2 * β * ‖f‖ / c₁ + 1

theorem horizon_pos (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) : 0 < horizon c₁ β f := by
  unfold horizon
  have : 0 ≤ 2 * β * ‖f‖ / c₁ := div_nonneg (by nlinarith [h.β_pos, norm_nonneg f]) h.c₁_pos.le
  linarith

theorem orderVal_beyond (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) {y : ℝ}
    (hy : horizon c₁ β f < y) : orderVal c₀ c₁ β f z y < β * sext f z := by
  have h1 := abs_sext_le f (z + y)
  have h2 := abs_sext_le f z
  have hY : 2 * β * ‖f‖ < c₁ * y := by
    have h3 : 2 * β * ‖f‖ / c₁ < y := by unfold horizon at hy; linarith
    rw [div_lt_iff₀ h.c₁_pos] at h3
    linarith
  simp only [orderVal]
  nlinarith [h.β_pos, le_abs_self (sext f (z + y)), neg_abs_le (sext f z), h.c₀_pos]

/-- The supremum over `y > 0` together with not ordering equals a maximum over the compact
`[0, Y]` together with not ordering. -/
theorem ordSup_eq (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) :
    max (β * sext f z) (ordSup c₀ c₁ β f z) =
      max (β * sext f z) (sSup (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f))) := by
  have hY := horizon_pos h f
  have hc : ContinuousOn (orderVal c₀ c₁ β f z) (Icc 0 (horizon c₁ β f)) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).add (continuous_const.mul
      ((continuous_sext f.continuous).comp (continuous_const.add continuous_id)))).continuousOn
  have hbdd : BddAbove (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f)) :=
    (isCompact_Icc.image_of_continuousOn hc).bddAbove
  have h0 : orderVal c₀ c₁ β f z 0 < β * sext f z := by
    simp only [orderVal, add_zero, mul_zero, sub_zero]; linarith [h.c₀_pos]
  refine le_antisymm (max_le (le_max_left _ _) ?_) (max_le (le_max_left _ _) ?_)
  · -- `sup_{y > 0} ≤ max{no order, max over [0, Y]}`
    refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases le_or_gt y (horizon c₁ β f) with hyY | hyY
    · exact (le_csSup hbdd ⟨y, ⟨le_of_lt hy, hyY⟩, rfl⟩).trans (le_max_right _ _)
    · exact (orderVal_beyond h f z hyY).le.trans (le_max_left _ _)
  · -- the maximum over `[0, Y]` is attained; at `0` it is beaten by not ordering
    obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hY.le) hc
    have heq : sSup (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f)) = orderVal c₀ c₁ β f z y :=
      (IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmax hu⟩)
    rw [heq]
    rcases eq_or_lt_of_le hy.1 with hy0 | hypos
    · rw [← hy0]; exact h0.le.trans (le_max_left _ _)
    · exact (le_csSup (bddAbove_ordSup h f z) ⟨y, hypos, rfl⟩).trans (le_max_right _ _)

/-- The right side of (1) as a function on stocks. -/
noncomputable def invRHS (p c₀ c₁ β : ℝ) (f : Stock → ℝ) (x : Stock) : ℝ :=
  p * min x.1 1 + max (β * sext f (leftover x.1)) (ordSup c₀ c₁ β f (leftover x.1))

theorem continuous_invRHS (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) :
    Continuous (invRHS p c₀ c₁ β f) := by
  -- the maximum over the compact `[0, Y]` is continuous in `z` (Theorem 3.6)
  set Y := horizon c₁ β f
  have hY := horizon_pos h f
  set G : ℝ × ℝ → ℝ := fun q => orderVal c₀ c₁ β f q.1 q.2
  have hG : Continuous G :=
    (continuous_const.sub (continuous_const.mul continuous_snd)).add (continuous_const.mul
      ((continuous_sext f.continuous).comp (continuous_fst.add continuous_snd)))
  have hM : Continuous fun z : ℝ => maxValue G (fun _ => Icc 0 Y) z :=
    (theorem_3_6 hG.continuousOn (fun _ => isCompact_Icc)
      (fun z => ⟨⟨0, le_rfl, hY.le⟩, fun y hy xs _ => ⟨0, fun _ => y, fun _ _ => hy,
        tendsto_const_nhds⟩⟩)
      (fun z => ⟨⟨0, le_rfl, hY.le⟩, fun xs _ ys hys => by
        obtain ⟨y, hy, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hys
        exact ⟨y, hy, φ, hφ, hlim⟩⟩)).1
  have heq : invRHS p c₀ c₁ β f = fun x : Stock => p * min x.1 1 +
      max (β * sext f (leftover x.1)) (maxValue G (fun _ => Icc 0 Y) (leftover x.1)) := by
    funext x
    simp only [invRHS]
    rw [ordSup_eq h f]
    rfl
  rw [heq]
  have hl : Continuous fun x : Stock => leftover x.1 :=
    (continuous_subtype_val.sub continuous_const).max continuous_const
  exact (continuous_const.mul (continuous_subtype_val.min continuous_const)).add
    ((continuous_const.mul ((continuous_sext f.continuous).comp hl)).max (hM.comp hl))

theorem abs_invRHS_le (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (x : Stock) :
    |invRHS p c₀ c₁ β f x| ≤ p + β * ‖f‖ := by
  have hp := h.p_pos
  have h1 : 0 ≤ p * min x.1 1 := mul_nonneg hp.le (le_min x.2.out zero_le_one)
  have h2 : p * min x.1 1 ≤ p := mul_le_of_le_one_right hp.le (min_le_right _ _)
  have h3 := abs_sext_le f (leftover x.1)
  have hs : ordSup c₀ c₁ β f (leftover x.1) ≤ -c₀ + β * ‖f‖ :=
    csSup_le ⟨_, 1, by norm_num, rfl⟩
      (by rintro _ ⟨y, hy, rfl⟩; exact orderVal_le h f (le_of_lt hy))
  have hb := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h3) h.β_pos.le
  have hlow : -‖f‖ ≤ sext f (leftover x.1) := by
    have := neg_abs_le (sext f (leftover x.1)); linarith
  have hb' := mul_le_mul_of_nonneg_left hlow h.β_pos.le
  have hnf : 0 ≤ β * ‖f‖ := mul_nonneg h.β_pos.le (norm_nonneg f)
  simp only [invRHS]
  rw [abs_le]
  constructor
  · have := le_max_left (β * sext f (leftover x.1)) (ordSup c₀ c₁ β f (leftover x.1))
    linarith
  · have := max_le hb (hs.trans (by linarith [h.c₀_pos]))
    linarith

/-- The operator `T` of (1) on `C(ℝ₊)`. -/
noncomputable def invT (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) : Stock →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (invRHS p c₀ c₁ β f) (continuous_invRHS h f)
    (p + β * ‖f‖) fun x => by rw [Real.norm_eq_abs]; exact abs_invRHS_le h f x

theorem invT_apply (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (x : Stock) :
    invT h f x = invRHS p c₀ c₁ β f x := rfl

theorem ordSup_mono (h : InvHyp p c₀ c₁ β) {f g : Stock →ᵇ ℝ} (hfg : f ≤ g) (z : ℝ) :
    ordSup c₀ c₁ β f z ≤ ordSup c₀ c₁ β g z := by
  refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  refine le_trans ?_ (le_csSup (bddAbove_ordSup h g z) ⟨y, hy, rfl⟩)
  have hle : f ⟨max (z + y) 0, mem_Ici.2 (le_max_right _ _)⟩ ≤
      g ⟨max (z + y) 0, mem_Ici.2 (le_max_right _ _)⟩ := hfg _
  have := mul_le_mul_of_nonneg_left hle h.β_pos.le
  change -c₀ - c₁ * y + β * f ⟨max (z + y) 0, _⟩ ≤ -c₀ - c₁ * y + β * g ⟨max (z + y) 0, _⟩
  linarith

theorem ordSup_add_const (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (a : ℝ) (z : ℝ) :
    ordSup c₀ c₁ β ⇑(f + const Stock a) z = ordSup c₀ c₁ β f z + β * a := by
  have hval : ∀ y, orderVal c₀ c₁ β ⇑(f + const Stock a) z y =
      orderVal c₀ c₁ β f z y + β * a := fun y => by
    simp only [orderVal, sext, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply]
    ring
  have hbdd := bddAbove_ordSup h f z
  have hne : (orderVal c₀ c₁ β f z '' Ioi 0).Nonempty := ⟨_, 1, by norm_num, rfl⟩
  unfold ordSup
  refine le_antisymm (csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [hval]
    linarith [le_csSup hbdd ⟨y, hy, rfl⟩]
  · have hbdd' := bddAbove_ordSup h (f + const Stock a) z
    have : sSup (orderVal c₀ c₁ β f z '' Ioi 0) ≤
        sSup (orderVal c₀ c₁ β ⇑(f + const Stock a) z '' Ioi 0) - β * a := by
      refine csSup_le hne ?_
      rintro _ ⟨y, hy, rfl⟩
      have := le_csSup hbdd' ⟨y, hy, rfl⟩
      rw [hval] at this
      linarith
    linarith

/-- `T` is a contraction of modulus `β` (Blackwell). -/
theorem invT_contraction (h : InvHyp p c₀ c₁ β) : IsContraction (invT h) β := by
  refine ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun f g hfg x => ?_) (fun f a ha x => ?_)⟩
  · change invRHS p c₀ c₁ β f x ≤ invRHS p c₀ c₁ β g x
    simp only [invRHS]
    have h1 : β * sext f (leftover x.1) ≤ β * sext g (leftover x.1) :=
      mul_le_mul_of_nonneg_left (hfg _) h.β_pos.le
    have h2 := ordSup_mono h hfg (leftover x.1)
    have := max_le_max h1 h2
    linarith
  · change invRHS p c₀ c₁ β ⇑(f + const Stock a) x ≤ invRHS p c₀ c₁ β f x + β * a
    have e : sext ⇑(f + const Stock a) (leftover x.1) = sext f (leftover x.1) + a := by
      simp [sext]
    unfold invRHS
    rw [ordSup_add_const h f a, e, mul_add, max_add_add_right]
    linarith

/-- **Exercise 5.14a.** (1) has a unique solution `v ∈ C(ℝ₊)`, and `0 ≤ v ≤ p/(1 − β)`. -/
theorem ex_5_14a (h : InvHyp p c₀ c₁ β) :
    ∃ v : Stock →ᵇ ℝ, (∀ x, v x = invRHS p c₀ c₁ β v x) ∧
      (∀ w : Stock →ᵇ ℝ, (∀ x, w x = invRHS p c₀ c₁ β w x) → w = v) ∧
      ∀ x, 0 ≤ v x ∧ v x ≤ p / (1 - β) := by
  have : Nonempty (Stock →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (invT_contraction h)
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  set S : Set (Stock →ᵇ ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ p / (1 - β)}
  have hclosed : IsClosed S := by
    have : S = ⋂ x, {f : Stock →ᵇ ℝ | f x ∈ Icc 0 (p / (1 - β))} := by ext f; simp [S]
    rw [this]
    exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x)
  have hmaps : MapsTo (invT h) S S := fun f hf x => by
    rw [invT_apply]
    simp only [invRHS]
    have hp := h.p_pos
    have hz := hf ⟨max (leftover x.1) 0, mem_Ici.2 (le_max_right _ _)⟩
    have h0 : 0 ≤ p * min x.1 1 := mul_nonneg hp.le (le_min x.2.out zero_le_one)
    have h1 : p * min x.1 1 ≤ p := mul_le_of_le_one_right hp.le (min_le_right _ _)
    have hs : ordSup c₀ c₁ β f (leftover x.1) ≤ -c₀ + β * (p / (1 - β)) := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      have h3 := mul_le_mul_of_nonneg_left
        (hf ⟨max (leftover x.1 + y) 0, mem_Ici.2 (le_max_right _ _)⟩).2 h.β_pos.le
      have h4 := mul_pos h.c₁_pos (mem_Ioi.1 hy)
      change -c₀ - c₁ * y + β * f ⟨max (leftover x.1 + y) 0, _⟩ ≤ _
      linarith
    have hm1 := le_max_left (β * sext f (leftover x.1)) (ordSup c₀ c₁ β f (leftover x.1))
    have hz0 : 0 ≤ sext f (leftover x.1) := hz.1
    have hz1 : sext f (leftover x.1) ≤ p / (1 - β) := hz.2
    have hb : β * sext f (leftover x.1) ≤ β * (p / (1 - β)) :=
      mul_le_mul_of_nonneg_left hz1 h.β_pos.le
    have hm2 := max_le hb (hs.trans (by linarith [h.c₀_pos]))
    have hbp : p + β * (p / (1 - β)) = p / (1 - β) := by field_simp; ring
    have hβz := mul_nonneg h.β_pos.le hz0
    exact ⟨by linarith, by linarith⟩
  have hvS : v ∈ S := (corollary_1 (S' := S) (S'' := S) (invT_contraction h) hv
    ⟨0, fun _ => ⟨le_rfl, div_nonneg h.p_pos.le h1β.le⟩⟩ hclosed hmaps hmaps).1
  refine ⟨v, fun x => (DFunLike.congr_fun hv x).symm, fun w hw => ?_, hvS⟩
  exact huniq w (by ext x; exact (hw x).symm)

/-- **Exercise 5.14a.** An optimal ordering policy exists: at every stock either not ordering is
optimal, or some order `y > 0` attains the supremum (and beats not ordering). -/
theorem ex_5_14a_policy (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) :
    ordSup c₀ c₁ β f z ≤ β * sext f z ∨
      ∃ y > 0, orderVal c₀ c₁ β f z y = ordSup c₀ c₁ β f z := by
  rcases le_or_gt (ordSup c₀ c₁ β f z) (β * sext f z) with hle | hlt
  · exact Or.inl hle
  right
  have hY := horizon_pos h f
  have hc : ContinuousOn (orderVal c₀ c₁ β f z) (Icc 0 (horizon c₁ β f)) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).add (continuous_const.mul
      ((continuous_sext f.continuous).comp (continuous_const.add continuous_id)))).continuousOn
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hY.le) hc
  have heq : sSup (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f)) = orderVal c₀ c₁ β f z y :=
    (IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmax hu⟩)
  have hE := ordSup_eq h f z
  rw [max_eq_right hlt.le, heq] at hE
  have hpos : 0 < y := by
    rcases eq_or_lt_of_le hy.1 with hy0 | hp
    · exfalso
      have h0 : orderVal c₀ c₁ β f z 0 < β * sext f z := by
        simp only [orderVal, add_zero, mul_zero, sub_zero]; linarith [h.c₀_pos]
      rw [← hy0] at hE
      have := le_max_right (β * sext f z) (orderVal c₀ c₁ β f z 0)
      rw [max_eq_left h0.le] at hE
      linarith
    · exact hp
  refine ⟨y, hpos, le_antisymm (le_csSup (bddAbove_ordSup h f z) ⟨y, hpos, rfl⟩) ?_⟩
  have := le_max_right (β * sext f z) (orderVal c₀ c₁ β f z y)
  rw [← hE] at this
  rcases le_total (β * sext f z) (orderVal c₀ c₁ β f z y) with h1 | h1
  · rw [max_eq_right h1] at hE; linarith
  · rw [max_eq_left h1] at hE; linarith

/-! ### Exercise 5.14b–c: the cycle values -/

/-- `r_n = −c₀ − c₁n + β(1 − βⁿ)p/(1 − β)`. -/
noncomputable def rn (p c₀ c₁ β : ℝ) (n : ℕ) : ℝ :=
  -c₀ - c₁ * n + β * (1 - β ^ n) / (1 - β) * p

/-- `Y_n = r_n/(1 − βⁿ)`. -/
noncomputable def Yn (p c₀ c₁ β : ℝ) (n : ℕ) : ℝ := rn p c₀ c₁ β n / (1 - β ^ n)

theorem one_sub_pow_pos (h : InvHyp p c₀ c₁ β) {n : ℕ} (hn : 1 ≤ n) : 0 < 1 - β ^ n := by
  have := pow_lt_one₀ h.β_pos.le h.β_lt (by omega : n ≠ 0)
  linarith

/-- **Exercise 5.14b.** `Y_n = −(c₀ + c₁n)/(1 − βⁿ) + βp/(1 − β)`. -/
theorem Yn_eq (h : InvHyp p c₀ c₁ β) {n : ℕ} (hn : 1 ≤ n) :
    Yn p c₀ c₁ β n = -(c₀ + c₁ * n) / (1 - β ^ n) + β * p / (1 - β) := by
  have h1 := one_sub_pow_pos h hn
  have h2 : 0 < 1 - β := by linarith [h.β_lt]
  simp only [Yn, rn]
  field_simp
  ring

/-- **Exercise 5.14b.** `Y_n → −∞`. -/
theorem tendsto_Yn (h : InvHyp p c₀ c₁ β) : Tendsto (Yn p c₀ c₁ β) atTop atBot := by
  have h2 : 0 < 1 - β := by linarith [h.β_lt]
  -- `Y_n ≤ −c₁n + βp/(1 − β)` since `0 < 1 − βⁿ ≤ 1`
  have hle : ∀ n : ℕ, 1 ≤ n → Yn p c₀ c₁ β n ≤ -(c₁ * n) + β * p / (1 - β) := fun n hn => by
    rw [Yn_eq h hn]
    have h1 := one_sub_pow_pos h hn
    have hb : 1 - β ^ n ≤ 1 := by linarith [pow_nonneg h.β_pos.le n]
    have hnum : 0 ≤ c₀ + c₁ * n :=
      add_nonneg h.c₀_pos.le (mul_nonneg h.c₁_pos.le (Nat.cast_nonneg n))
    have : c₀ + c₁ * n ≤ (c₀ + c₁ * n) / (1 - β ^ n) := by
      rw [le_div_iff₀ h1]; nlinarith
    have : c₁ * n ≤ (c₀ + c₁ * n) / (1 - β ^ n) := by linarith [h.c₀_pos]
    rw [neg_div]
    linarith
  have hlin : Tendsto (fun n : ℕ => -(c₁ * n) + β * p / (1 - β)) atTop atBot := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop h.c₁_pos
    exact tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp this)
  exact tendsto_atBot_mono' atTop (eventually_atTop.2 ⟨1, hle⟩) hlin

/-- **Exercise 5.14b.** There is a finite `N ≥ 1` with `Y_N ≥ Y_n` for all `n ≥ 1`. -/
theorem ex_5_14b (h : InvHyp p c₀ c₁ β) :
    ∃ N, 1 ≤ N ∧ ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_Yn h).eventually_lt_atBot (Yn p c₀ c₁ β 1))
  -- maximize over the finite set `{1, …, max K 1}`
  obtain ⟨N, hN, hmax⟩ := (Finset.Icc 1 (max K 1)).exists_max_image (Yn p c₀ c₁ β)
    ⟨1, Finset.mem_Icc.2 ⟨le_rfl, le_max_right _ _⟩⟩
  refine ⟨N, (Finset.mem_Icc.1 hN).1, fun n hn => ?_⟩
  rcases le_or_gt n (max K 1) with hnK | hnK
  · exact hmax n (Finset.mem_Icc.2 ⟨hn, hnK⟩)
  · exact (hK n (le_of_max_le_left hnK.le)).le.trans
      (hmax 1 (Finset.mem_Icc.2 ⟨le_rfl, le_max_right _ _⟩))

/-- **Exercise 5.14b.** The optimal cycle does not depend on the price `p`. -/
theorem argmax_Yn_indep_p {p' : ℝ} (h : InvHyp p c₀ c₁ β) (h' : InvHyp p' c₀ c₁ β) {N : ℕ}
    (hN : 1 ≤ N) (hmax : ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N) :
    ∀ n, 1 ≤ n → Yn p' c₀ c₁ β n ≤ Yn p' c₀ c₁ β N := fun n hn => by
  have := hmax n hn
  rw [Yn_eq h hn, Yn_eq h hN] at this
  rw [Yn_eq h' hn, Yn_eq h' hN]
  linarith

/-- **Exercise 5.14b.** A larger fixed cost calls for a longer cycle: if `N` is optimal for `c₀`
and `N'` for `c₀' > c₀`, then `N ≤ N'` unless both are optimal for both (increasing differences:
`1/(1 − βⁿ)` falls with `n`). -/
theorem argmax_Yn_mono_c0 {c₀' : ℝ} (h : InvHyp p c₀ c₁ β) (h' : InvHyp p c₀' c₁ β) (hc : c₀ < c₀')
    {N N' : ℕ} (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hmax : ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N)
    (hmax' : ∀ n, 1 ≤ n → Yn p c₀' c₁ β n ≤ Yn p c₀' c₁ β N') : N ≤ N' := by
  by_contra hlt
  push Not at hlt
  have e1 := hmax N' hN'
  have e2 := hmax' N hN
  rw [Yn_eq h hN', Yn_eq h hN] at e1
  rw [Yn_eq h' hN, Yn_eq h' hN'] at e2
  -- adding the two optimality conditions leaves `(c₀' − c₀)(1/(1 − β^{N'}) − 1/(1 − β^N)) ≤ 0`
  have hA := one_sub_pow_pos h hN
  have hB := one_sub_pow_pos h hN'
  have hpow : β ^ N < β ^ N' := pow_lt_pow_right_of_lt_one₀ h.β_pos h.β_lt hlt
  have hlt' : 1 / (1 - β ^ N) < 1 / (1 - β ^ N') := one_div_lt_one_div_of_lt hB (by linarith)
  have key : (c₀' - c₀) * (1 / (1 - β ^ N')) ≤ (c₀' - c₀) * (1 / (1 - β ^ N)) := by
    have e : ∀ a b : ℝ, -(a + b) / (1 - β ^ N) = -(a + b) * (1 / (1 - β ^ N)) := fun a b => by
      ring
    have e' : ∀ a b : ℝ, -(a + b) / (1 - β ^ N') = -(a + b) * (1 / (1 - β ^ N')) := fun a b => by
      ring
    rw [e, e'] at e1 e2
    nlinarith
  have := mul_lt_mul_of_pos_left hlt' (by linarith : 0 < c₀' - c₀)
  linarith

/-- For `m > n ≥ 1`, `(1 − β^m)/(1 − β^n)` rises strictly with `β ∈ (0, 1)`: with `s = β^n`, it
is the slope of the chord of the strictly convex `s ↦ s^{m/n}` from `s` to `1`. -/
theorem pow_ratio_strictMono {β β' : ℝ} (h0 : 0 < β) (hββ' : β < β') (h1 : β' < 1) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n < m) :
    (1 - β ^ m) * (1 - β' ^ n) < (1 - β' ^ m) * (1 - β ^ n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set q : ℝ := (m : ℝ) / n
  have hq : 1 < q := by
    rw [one_lt_div (by positivity)]
    exact_mod_cast hnm
  have hpow : ∀ x : ℝ, 0 ≤ x → (x ^ n) ^ q = x ^ m := fun x hx => by
    rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx, show (n : ℝ) * q = m by
      simp only [q]; field_simp, Real.rpow_natCast]
  have hs : β ^ n < β' ^ n := pow_lt_pow_left₀ hββ' h0.le (by omega)
  have hs1 : β' ^ n < 1 := pow_lt_one₀ (h0.le.trans hββ'.le) h1 (by omega)
  have hs0 : 0 < β ^ n := pow_pos h0 n
  have key := (strictConvexOn_rpow hq).secant_strict_mono (a := 1) (x := β ^ n) (y := β' ^ n)
    (mem_Ici.2 zero_le_one) (mem_Ici.2 hs0.le) (mem_Ici.2 (hs0.trans hs).le) (by linarith)
    (by linarith) hs
  rw [hpow β h0.le, hpow β' (h0.trans hββ').le, Real.one_rpow] at key
  have d1 : 0 < 1 - β ^ n := by linarith
  have d2 : 0 < 1 - β' ^ n := by linarith
  rw [← neg_div_neg_eq, ← neg_div_neg_eq (β' ^ m - 1), neg_sub, neg_sub, neg_sub, neg_sub,
    div_lt_div_iff₀ d1 d2] at key
  linarith

/-- **Exercise 5.14b.** A higher discount factor (a lower interest rate) calls for a longer cycle:
if `N` is optimal for `β` and `N'` for `β' > β`, then `N ≤ N'` (increasing differences:
`(1 − β^m)/(1 − β^n)` rises with `β` for `m > n`, `pow_ratio_strictMono`). -/
theorem argmax_Yn_mono_beta {β' : ℝ} (h : InvHyp p c₀ c₁ β) (h' : InvHyp p c₀ c₁ β')
    (hβ : β < β') {N N' : ℕ} (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hmax : ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N)
    (hmax' : ∀ n, 1 ≤ n → Yn p c₀ c₁ β' n ≤ Yn p c₀ c₁ β' N') : N ≤ N' := by
  by_contra hlt
  push Not at hlt
  have e1 := hmax N' hN'
  have e2 := hmax' N hN
  rw [Yn_eq h hN', Yn_eq h hN] at e1
  rw [Yn_eq h' hN, Yn_eq h' hN'] at e2
  have x0 := one_sub_pow_pos h hN
  have y0 := one_sub_pow_pos h hN'
  have x0' := one_sub_pow_pos h' hN
  have y0' := one_sub_pow_pos h' hN'
  have hA : 0 < c₀ + c₁ * N := by have := h.c₀_pos; have := h.c₁_pos; positivity
  have hB : 0 < c₀ + c₁ * N' := by have := h.c₀_pos; have := h.c₁_pos; positivity
  -- clear denominators: `A(1 − β^{N'}) ≤ B(1 − β^N)` and `B(1 − β'^N) ≤ A(1 − β'^{N'})`
  have f1 : (c₀ + c₁ * N) * (1 - β ^ N') ≤ (c₀ + c₁ * N') * (1 - β ^ N) := by
    have : -(c₀ + c₁ * N') / (1 - β ^ N') ≤ -(c₀ + c₁ * N) / (1 - β ^ N) := by linarith
    rw [div_le_div_iff₀ y0 x0] at this
    linarith
  have f2 : (c₀ + c₁ * N') * (1 - β' ^ N) ≤ (c₀ + c₁ * N) * (1 - β' ^ N') := by
    have : -(c₀ + c₁ * N) / (1 - β' ^ N) ≤ -(c₀ + c₁ * N') / (1 - β' ^ N') := by linarith
    rw [div_le_div_iff₀ x0' y0'] at this
    linarith
  have hr := pow_ratio_strictMono h.β_pos hβ h'.β_lt hN' hlt
  have g1 := mul_le_mul_of_nonneg_right f1 x0'.le
  have g2 := mul_le_mul_of_nonneg_right f2 x0.le
  have g3 := mul_lt_mul_of_pos_left hr hA
  nlinarith

/-- **Exercise 5.14c.** With `Y_N > 0`, `A = (1 − β)Y_N/(βp − c₁) ∈ (0, 1)`; `A < 1` holds for
every `N ≥ 1`, because `1 − β^N ≤ N(1 − β)` and `c₀ > 0`. -/
theorem ex_5_14c (h : InvHyp p c₀ c₁ β) {N : ℕ} (hN : 1 ≤ N) (hY : 0 < Yn p c₀ c₁ β N) :
    0 < (1 - β) * Yn p c₀ c₁ β N / (β * p - c₁) ∧
      (1 - β) * Yn p c₀ c₁ β N / (β * p - c₁) < 1 := by
  have h2 : 0 < 1 - β := by linarith [h.β_lt]
  have hm : 0 < β * p - c₁ := by linarith [h.margin]
  refine ⟨div_pos (mul_pos h2 hY) hm, ?_⟩
  rw [div_lt_one hm, Yn_eq h hN]
  have h1 := one_sub_pow_pos h hN
  -- `1 − β^N ≤ N(1 − β)` (Bernoulli)
  have hbern : 1 - β ^ N ≤ N * (1 - β) := by
    have := one_add_mul_le_pow (show -2 ≤ -(1 - β) by linarith [h.β_pos]) N
    rw [show (1 : ℝ) + -(1 - β) = β by ring] at this
    linarith
  have hkey : c₁ * (1 - β ^ N) < (1 - β) * (c₀ + c₁ * N) := by nlinarith [h.c₀_pos, h.c₁_pos]
  have e : (1 - β) * (-(c₀ + c₁ * N) / (1 - β ^ N) + β * p / (1 - β)) =
      (1 - β) * -(c₀ + c₁ * N) / (1 - β ^ N) + β * p := by
    field_simp
  rw [e]
  have : (1 - β) * -(c₀ + c₁ * N) / (1 - β ^ N) < -c₁ := by
    rw [div_lt_iff₀ h1]; nlinarith
  linarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The (s, S) policy: the value function

SLP Exercise 5.14d–h, pp. 120–122. Let `N ≥ 1` maximize `Y_n`, with `Y = Y_N > 0`, and
`A = (1 − β)Y/(βp − c₁) ∈ (0, 1)`.

* `cellW`: on the cell `[ν, ν + 1]` (`ν ≥ 1`), with `α = u − ν`,
  `w(u) = p(1 − β^ν)/(1 − β) + β^{ν−1} max{c₁α + Y, β(pα + Y)}` (`wSS_cell`); the maximum picks
  `c₁α + Y` exactly when `α ≤ A` (`cross_iff`). This is the book's (6) (`wSS_six`), and holds on
  the closed cell because `A < 1`.
* **Exercise 5.14d**: `wSS` solves the difference equations (2), (3) and (5)
  (`wSS_two`, `wSS_three_left`, `wSS_three_right`, `wSS_five`); it is continuous on `ℝ₊`
  (`continuousOn_wSS`), bounded (`wSS_bounds`) and piecewise linear.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {p c₀ c₁ β : ℝ} {N : ℕ}

/-- The hypotheses of Exercise 5.14d–h: `N` maximizes `Y_n` and `Y_N > 0`. -/
structure SSHyp (p c₀ c₁ β : ℝ) (N : ℕ) : Prop where
  inv : InvHyp p c₀ c₁ β
  N_pos : 1 ≤ N
  N_max : ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N
  Y_pos : 0 < Yn p c₀ c₁ β N

/-- The indifference point `A = (1 − β)Y_N/(βp − c₁)`. -/
noncomputable def Aind (p c₀ c₁ β : ℝ) (N : ℕ) : ℝ := (1 - β) * Yn p c₀ c₁ β N / (β * p - c₁)

/-- `w` on the cell `[ν, ν + 1]`. -/
noncomputable def cellW (p c₀ c₁ β : ℝ) (N ν : ℕ) (u : ℝ) : ℝ :=
  p * (1 - β ^ ν) / (1 - β) +
    β ^ (ν - 1) * max (c₁ * (u - ν) + Yn p c₀ c₁ β N) (β * (p * (u - ν) + Yn p c₀ c₁ β N))

/-- The conjectured value function (2), (3), (5), in the closed form (6). -/
noncomputable def wSS (p c₀ c₁ β : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 1 then p * x + Yn p c₀ c₁ β N else cellW p c₀ c₁ β N ⌊x⌋₊ x

theorem SSHyp.A_pos (h : SSHyp p c₀ c₁ β N) : 0 < Aind p c₀ c₁ β N :=
  (ex_5_14c h.inv h.N_pos h.Y_pos).1

theorem SSHyp.A_lt (h : SSHyp p c₀ c₁ β N) : Aind p c₀ c₁ β N < 1 :=
  (ex_5_14c h.inv h.N_pos h.Y_pos).2

/-- `c₁a + Y ≤ β(pa + Y)` iff `A ≤ a`: the two branches cross at `A`. -/
theorem cross_iff (h : SSHyp p c₀ c₁ β N) (a : ℝ) :
    c₁ * a + Yn p c₀ c₁ β N ≤ β * (p * a + Yn p c₀ c₁ β N) ↔ Aind p c₀ c₁ β N ≤ a := by
  have hm : 0 < β * p - c₁ := by linarith [h.inv.margin]
  unfold Aind
  rw [div_le_iff₀ hm]
  constructor <;> intro hh <;> nlinarith

theorem cross_one (h : SSHyp p c₀ c₁ β N) :
    max (c₁ * 1 + Yn p c₀ c₁ β N) (β * (p * 1 + Yn p c₀ c₁ β N)) =
      β * (p * 1 + Yn p c₀ c₁ β N) :=
  max_eq_right ((cross_iff h 1).2 h.A_lt.le)

theorem cross_zero (h : SSHyp p c₀ c₁ β N) :
    max (c₁ * 0 + Yn p c₀ c₁ β N) (β * (p * 0 + Yn p c₀ c₁ β N)) = Yn p c₀ c₁ β N := by
  simp only [mul_zero, zero_add]
  exact max_eq_left (mul_le_of_le_one_left h.Y_pos.le h.inv.β_lt.le)

/-- On the closed cell `[ν, ν + 1]`, `ν ≥ 1`, `w = cellW ν`. -/
theorem wSS_cell (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {u : ℝ}
    (hu : u ∈ Icc (ν : ℝ) (ν + 1)) : wSS p c₀ c₁ β N u = cellW p c₀ c₁ β N ν u := by
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  push_cast at hu
  rcases eq_or_lt_of_le hu.2 with htop | hlt
  · -- the right end `u = m + 2`
    have hfl : ⌊u⌋₊ = m + 2 := by
      rw [htop]; exact_mod_cast Nat.floor_natCast (m + 2) |>.trans rfl
    have hu1 : ¬ u ≤ 1 := by rw [htop]; push Not; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    simp only [wSS, hu1, ↓reduceIte, hfl, cellW]
    have e1 : u - ((m + 2 : ℕ) : ℝ) = 0 := by rw [htop]; push_cast; ring
    have e2 : u - ((m + 1 : ℕ) : ℝ) = 1 := by rw [htop]; push_cast; ring
    rw [e1, e2, cross_zero h, cross_one h]
    simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega, pow_succ]
    field_simp
    ring
  · rcases eq_or_lt_of_le hu.1 with hbot | hgt
    · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- `u = 1`
        subst hm0
        have hu1 : u = 1 := by rw [← hbot]; norm_num
        subst hu1
        simp only [wSS, le_refl, ↓reduceIte, cellW]
        rw [show (1 : ℝ) - ((0 + 1 : ℕ) : ℝ) = 0 by norm_num, cross_zero h]
        simp only [pow_one, zero_add, Nat.sub_self, pow_zero, one_mul, mul_one]
        field_simp
      · have hu1 : ¬ u ≤ 1 := by
          push Not
          have : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
          linarith
        have hfl : ⌊u⌋₊ = m + 1 := (Nat.floor_eq_iff (by linarith)).2 ⟨by push_cast; linarith,
          by push_cast; linarith⟩
        simp only [wSS, hu1, ↓reduceIte, hfl]
    · have hu1 : ¬ u ≤ 1 := by
        push Not
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hfl : ⌊u⌋₊ = m + 1 :=
        (Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).2
          ⟨by push_cast; linarith, by push_cast; linarith⟩
      simp only [wSS, hu1, ↓reduceIte, hfl]

theorem wSS_low {x : ℝ} (hx : x ≤ 1) : wSS p c₀ c₁ β N x = p * x + Yn p c₀ c₁ β N := by
  simp only [wSS, hx, ↓reduceIte]

/-- **Exercise 5.14d, (2).** `w(x) = px + Y` on `[0, 1]`. -/
theorem wSS_two (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : wSS p c₀ c₁ β N x = p * x + Yn p c₀ c₁ β N :=
  wSS_low hx.2

/-- On `[1, 2]`, `w(x) = p + max{c₁(x − 1) + Y, βw(x − 1)}`. -/
theorem wSS_one_two (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    wSS p c₀ c₁ β N x = p + max (c₁ * (x - 1) + Yn p c₀ c₁ β N)
      (β * wSS p c₀ c₁ β N (x - 1)) := by
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  rw [wSS_cell h le_rfl (by push_cast; exact ⟨hx.1, by linarith [hx.2]⟩),
    wSS_low (by linarith [hx.2] : x - 1 ≤ 1)]
  simp only [cellW, Nat.cast_one, pow_one, Nat.sub_self, pow_zero, one_mul]
  congr 1
  field_simp

/-- **Exercise 5.14d, (3).** On `(1, 1 + A)`, `w(x) = p + c₁(x − 1) + Y`. -/
theorem wSS_three_left (h : SSHyp p c₀ c₁ β N) {x : ℝ}
    (hx : x ∈ Ioo (1 : ℝ) (1 + Aind p c₀ c₁ β N)) :
    wSS p c₀ c₁ β N x = p + c₁ * (x - 1) + Yn p c₀ c₁ β N := by
  rw [wSS_one_two h ⟨hx.1.le, by linarith [hx.2, h.A_lt]⟩,
    wSS_low (show x - 1 ≤ 1 by linarith [hx.2, h.A_lt])]
  rw [max_eq_left]
  · ring
  · have := (cross_iff h (x - 1)).not.2 (by push Not; linarith [hx.2])
    push Not at this
    exact this.le

/-- **Exercise 5.14d, (3).** On `[1 + A, 2]`, `w(x) = p + βw(x − 1)`. -/
theorem wSS_three_right (h : SSHyp p c₀ c₁ β N) {x : ℝ}
    (hx : x ∈ Icc (1 + Aind p c₀ c₁ β N) 2) :
    wSS p c₀ c₁ β N x = p + β * wSS p c₀ c₁ β N (x - 1) := by
  rw [wSS_one_two h ⟨by linarith [hx.1, h.A_pos], hx.2⟩]
  rw [wSS_low (by linarith [hx.2] : x - 1 ≤ 1)]
  rw [max_eq_right ((cross_iff h (x - 1)).2 (by linarith [hx.1]))]

/-- **Exercise 5.14d, (5).** For `x ≥ 2`, `w(x) = p + βw(x − 1)`. -/
theorem wSS_five (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 2 ≤ x) :
    wSS p c₀ c₁ β N x = p + β * wSS p c₀ c₁ β N (x - 1) := by
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  set ν := ⌊x⌋₊
  have hν2 : 2 ≤ ν := Nat.le_floor (by exact_mod_cast hx)
  have hνx : (ν : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxν : x < ν + 1 := Nat.lt_floor_add_one x
  obtain ⟨m, hm⟩ : ∃ m, ν = m + 2 := ⟨ν - 2, by omega⟩
  rw [wSS_cell h (ν := ν) (by omega) ⟨hνx, hxν.le⟩,
    wSS_cell h (ν := m + 1) (by omega) ⟨by rw [hm] at hνx; push_cast at hνx ⊢; linarith,
      by rw [hm] at hxν; push_cast at hxν ⊢; linarith⟩]
  simp only [cellW, hm]
  push_cast
  have e : x - (↑m + 1) - 1 = x - (↑m + 2) := by ring
  rw [show x - 1 - (↑m + 1) = x - (↑m + 2) by ring]
  simp only [pow_succ]
  field_simp
  ring

/-- **Exercise 5.14d, (6).** For `x > 1` with `ν = ⌊x⌋`, `α = x − ν`: below the indifference
point `w(x) = p(1 − β^ν)/(1 − β) + β^{ν−1}(c₁α + Y)`, above it
`w(x) = p(1 − β^ν)/(1 − β) + β^ν(pα + Y)`. -/
theorem wSS_six (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 1 < x) :
    (x - ⌊x⌋₊ < Aind p c₀ c₁ β N → wSS p c₀ c₁ β N x =
      p * (1 - β ^ ⌊x⌋₊) / (1 - β) + β ^ (⌊x⌋₊ - 1) * (c₁ * (x - ⌊x⌋₊) + Yn p c₀ c₁ β N)) ∧
    (Aind p c₀ c₁ β N ≤ x - ⌊x⌋₊ → wSS p c₀ c₁ β N x =
      p * (1 - β ^ ⌊x⌋₊) / (1 - β) + β ^ ⌊x⌋₊ * (p * (x - ⌊x⌋₊) + Yn p c₀ c₁ β N)) := by
  have hν : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.le)
  have hcell := wSS_cell h hν ⟨Nat.floor_le (by linarith), (Nat.lt_floor_add_one x).le⟩
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · rw [hcell, cellW, max_eq_left]
    have := (cross_iff h (x - ⌊x⌋₊)).not.2 (by push Not; exact hα)
    push Not at this
    exact this.le
  · rw [hcell, cellW, max_eq_right ((cross_iff h _).2 hα)]
    obtain ⟨m, hm⟩ : ∃ m, ⌊x⌋₊ = m + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    ring

/-! ### Continuity and bounds -/

theorem continuous_cellW (ν : ℕ) : Continuous (cellW p c₀ c₁ β N ν) := by
  unfold cellW
  fun_prop

/-- `w` is continuous on each cell `[n, n + 1]`. -/
theorem continuousOn_wSS_cell (h : SSHyp p c₀ c₁ β N) (n : ℕ) :
    ContinuousOn (wSS p c₀ c₁ β N) (Icc (n : ℝ) (n + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (show Continuous (fun x : ℝ => p * x + Yn p c₀ c₁ β N) by
      fun_prop).continuousOn.congr fun x hx => ?_
    simp only [Nat.cast_zero, zero_add] at hx
    exact wSS_low hx.2
  · exact (continuous_cellW n).continuousOn.congr fun x hx => wSS_cell h hn hx

/-- **Exercise 5.14d.** `w` is continuous on `ℝ₊`. -/
theorem continuousOn_wSS (h : SSHyp p c₀ c₁ β N) : ContinuousOn (wSS p c₀ c₁ β N) (Ici 0) := by
  -- two adjacent cells cover a neighbourhood
  have hpair : ∀ n : ℕ, ContinuousOn (wSS p c₀ c₁ β N) (Icc (n : ℝ) (n + 2)) := fun n => by
    have := (continuousOn_wSS_cell h n).union_of_isClosed (continuousOn_wSS_cell h (n + 1))
      isClosed_Icc isClosed_Icc
    rwa [show ((n + 1 : ℕ) : ℝ) = n + 1 by push_cast; ring,
      show (n : ℝ) + 1 + 1 = n + 2 by ring, Icc_union_Icc_eq_Icc (by linarith)
        (by linarith)] at this
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  set m := ⌊x⌋₊
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have hc := hpair 0
    simp only [Nat.cast_zero, zero_add] at hc
    refine (hc x ⟨hx0, by rw [hm0] at hxm; push_cast at hxm; linarith⟩).mono_of_mem_nhdsWithin ?_
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by rw [hm0] at hxm; push_cast at hxm; linarith))
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hc := hpair k
    have hk' : (m : ℝ) = k + 1 := by rw [hk]; push_cast; ring
    refine (hc x ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin
      (nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith)))

/-- **Exercise 5.14d.** `w` is bounded: `0 ≤ w ≤ p/(1 − β) + p + Y` on `ℝ₊`. -/
theorem wSS_bounds (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ wSS p c₀ c₁ β N x ∧
      wSS p c₀ c₁ β N x ≤ p / (1 - β) + p + Yn p c₀ c₁ β N := by
  have hp := h.inv.p_pos
  have hY := h.Y_pos
  have h1β : 0 < 1 - β := by linarith [h.inv.β_lt]
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [wSS_low hx1]
    have : 0 ≤ p / (1 - β) := div_nonneg hp.le h1β.le
    constructor <;> nlinarith
  · set ν := ⌊x⌋₊
    have hν : 1 ≤ ν := Nat.le_floor (by exact_mod_cast hx1.le)
    have hνx : (ν : ℝ) ≤ x := Nat.floor_le hx
    have hxν : x < ν + 1 := Nat.lt_floor_add_one x
    rw [wSS_cell h hν ⟨hνx, hxν.le⟩, cellW]
    have hpow : 0 ≤ β ^ ν := pow_nonneg h.inv.β_pos.le ν
    have hpow1 : β ^ ν ≤ 1 := pow_le_one₀ h.inv.β_pos.le h.inv.β_lt.le
    have hq0 : 0 ≤ β ^ (ν - 1) := pow_nonneg h.inv.β_pos.le _
    have hq1 : β ^ (ν - 1) ≤ 1 := pow_le_one₀ h.inv.β_pos.le h.inv.β_lt.le
    have hα0 : 0 ≤ x - ν := by linarith
    have hα1 : x - ν ≤ 1 := by linarith
    have hM0 : 0 ≤ max (c₁ * (x - ν) + Yn p c₀ c₁ β N) (β * (p * (x - ν) + Yn p c₀ c₁ β N)) :=
      le_max_of_le_left (by nlinarith [h.inv.c₁_pos])
    have hM1 : max (c₁ * (x - ν) + Yn p c₀ c₁ β N) (β * (p * (x - ν) + Yn p c₀ c₁ β N)) ≤
        p + Yn p c₀ c₁ β N := by
      have hpα : p * (x - ν) ≤ p := mul_le_of_le_one_right hp.le hα1
      have hpα0 : 0 ≤ p * (x - ν) := mul_nonneg hp.le hα0
      have hc₁p : c₁ ≤ p := by nlinarith [h.inv.margin, h.inv.β_lt, h.inv.β_pos]
      refine max_le ?_ ?_
      · nlinarith [h.inv.c₁_pos]
      · have := mul_le_of_le_one_left (by linarith : 0 ≤ p * (x - ν) + Yn p c₀ c₁ β N)
          h.inv.β_lt.le
        linarith
    have hA : 0 ≤ p * (1 - β ^ ν) / (1 - β) := div_nonneg (by nlinarith) h1β.le
    have hB : p * (1 - β ^ ν) / (1 - β) ≤ p / (1 - β) :=
      div_le_div_of_nonneg_right (by nlinarith) h1β.le
    constructor <;> nlinarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The (s, S) policy: verification

SLP Exercise 5.14d–h, continued. Throughout, `N` maximizes `Y_n`, `Y = Y_N > 0` and
`φ(u) = −c₁u + βw(u)`, so that ordering up to `u` from `z` is worth `−c₀ + c₁z + φ(u)`.

* **Exercise 5.14d (derivatives)**: `w' = p` on `(0, 1)`, `w' = β^{ν−1}c₁` on `(ν, ν + A)` and
  `w' = β^νp` on `(ν + A, ν + 1)` (`wSS_deriv_low`, `wSS_deriv_left`, `wSS_deriv_right`); `w` is not
  differentiable at `1`, at each integer `ν ≥ 2`, or at `ν + A` (`wSS_kink_one`,
  `wSS_kink_int`, `wSS_kink_A`).
* **Exercise 5.14e**: `phi_cell_convex`: `φ` is convex on each cell, so
  (`ex_5_14e`) any order is beaten either by the limit `y ↓ 0` (not attained) or by an order
  that brings the stock to an integer.
* **Exercise 5.14f** (`ex_5_14f`): ordering up to the integer `n` from `z` is worth
  `c₁z + r_n + βⁿY`.
* **Exercise 5.14g** (`ex_5_14g`): `max_{n ≥ 1} (r_n + βⁿY_N) = Y_N`.
* **Exercise 5.14h** (`ex_5_14h`): `w` satisfies (1); so `w = v` (`ex_5_14_value`). The key
  step for `x ≥ 2` is `key_ineq`: `βw(z) > c₁z + r_n + βⁿY` for integers `n > z ≥ 1`.
* `ex_5_14_policy`: the (s, S) policy, `s = 1 + A`, `S = N`: below `1 + A` order up to `N`,
  above it do not order; at `1 + A` both are optimal, so the optimal policy is not unique
  (Exercise 5.14a).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {p c₀ c₁ β : ℝ} {N : ℕ}

/-- The branches differ by `(βp − c₁)(α − A)`. -/
theorem cross_eq (h : SSHyp p c₀ c₁ β N) (a : ℝ) :
    β * (p * a + Yn p c₀ c₁ β N) - (c₁ * a + Yn p c₀ c₁ β N) =
      (β * p - c₁) * (a - Aind p c₀ c₁ β N) := by
  have hm : β * p - c₁ ≠ 0 := by linarith [h.inv.margin]
  unfold Aind
  field_simp
  ring

/-- On `[ν, ν + A]`, `w(u) = p(1 − β^ν)/(1 − β) + β^{ν−1}(c₁(u − ν) + Y)`. -/
theorem wSS_left_piece (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {u : ℝ}
    (hu : u ∈ Icc (ν : ℝ) (ν + Aind p c₀ c₁ β N)) :
    wSS p c₀ c₁ β N u = p * (1 - β ^ ν) / (1 - β) +
      β ^ (ν - 1) * (c₁ * (u - ν) + Yn p c₀ c₁ β N) := by
  rw [wSS_cell h hν ⟨hu.1, by linarith [hu.2, h.A_lt]⟩, cellW, max_eq_left]
  have := cross_eq h (u - ν)
  nlinarith [h.inv.margin, hu.2]

/-- On `[ν + A, ν + 1]`, `w(u) = p(1 − β^ν)/(1 − β) + β^ν(p(u − ν) + Y)`. -/
theorem wSS_right_piece (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {u : ℝ}
    (hu : u ∈ Icc ((ν : ℝ) + Aind p c₀ c₁ β N) (ν + 1)) :
    wSS p c₀ c₁ β N u = p * (1 - β ^ ν) / (1 - β) +
      β ^ ν * (p * (u - ν) + Yn p c₀ c₁ β N) := by
  rw [wSS_cell h hν ⟨by linarith [hu.1, h.A_pos], hu.2⟩, cellW,
    max_eq_right ((cross_iff h _).2 (by linarith [hu.1]))]
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-! ### Exercise 5.14d: derivatives -/

theorem wSS_deriv_low {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt (wSS p c₀ c₁ β N) p x := by
  have h1 : HasDerivAt (fun u => p * u + Yn p c₀ c₁ β N) p x := by
    simpa using ((hasDerivAt_id' x).const_mul p).add_const (Yn p c₀ c₁ β N)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx.2] with u hu
  exact wSS_low (le_of_lt hu)

theorem wSS_deriv_left (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {x : ℝ}
    (hx : x ∈ Ioo (ν : ℝ) (ν + Aind p c₀ c₁ β N)) :
    HasDerivAt (wSS p c₀ c₁ β N) (β ^ (ν - 1) * c₁) x := by
  have h1 : HasDerivAt (fun u => p * (1 - β ^ ν) / (1 - β) +
      β ^ (ν - 1) * (c₁ * (u - ν) + Yn p c₀ c₁ β N)) (β ^ (ν - 1) * c₁) x := by
    have := (((hasDerivAt_id' x).sub_const (ν : ℝ)).const_mul c₁).add_const (Yn p c₀ c₁ β N)
      |>.const_mul (β ^ (ν - 1)) |>.const_add (p * (1 - β ^ ν) / (1 - β))
    simpa using this
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
  exact wSS_left_piece h hν ⟨hu.1.le, hu.2.le⟩

theorem wSS_deriv_right (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) {x : ℝ}
    (hx : x ∈ Ioo ((ν : ℝ) + Aind p c₀ c₁ β N) (ν + 1)) :
    HasDerivAt (wSS p c₀ c₁ β N) (β ^ ν * p) x := by
  have h1 : HasDerivAt (fun u => p * (1 - β ^ ν) / (1 - β) +
      β ^ ν * (p * (u - ν) + Yn p c₀ c₁ β N)) (β ^ ν * p) x := by
    have := (((hasDerivAt_id' x).sub_const (ν : ℝ)).const_mul p).add_const (Yn p c₀ c₁ β N)
      |>.const_mul (β ^ ν) |>.const_add (p * (1 - β ^ ν) / (1 - β))
    simpa using this
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
  exact wSS_right_piece h hν ⟨hu.1.le, hu.2.le⟩

/-- A function that is affine with slope `a` just left of `x₀` and slope `b ≠ a` just right of it is
not differentiable at `x₀`. -/
theorem not_differentiableAt_of_kink {f : ℝ → ℝ} {x₀ a b : ℝ}
    (hL : ∀ᶠ u in 𝓝[≤] x₀, f u = f x₀ + a * (u - x₀))
    (hR : ∀ᶠ u in 𝓝[≥] x₀, f u = f x₀ + b * (u - x₀)) (hab : a ≠ b) :
    ¬ DifferentiableAt ℝ f x₀ := by
  intro hd
  have hlin : ∀ c : ℝ, HasDerivAt (fun u => f x₀ + c * (u - x₀)) c x₀ := fun c => by
    simpa using (((hasDerivAt_id' x₀).sub_const x₀).const_mul c).const_add (f x₀)
  have h1 : HasDerivWithinAt f a (Iic x₀) x₀ :=
    (hlin a).hasDerivWithinAt.congr_of_eventuallyEq hL (by simp)
  have h2 : HasDerivWithinAt f b (Ici x₀) x₀ :=
    (hlin b).hasDerivWithinAt.congr_of_eventuallyEq hR (by simp)
  have e1 := (uniqueDiffWithinAt_Iic x₀).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h1
  have e2 := (uniqueDiffWithinAt_Ici x₀).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h2
  exact hab (e1.symm.trans e2)

/-- **Exercise 5.14d.** `w` has a kink at `1`: slopes `p` and `c₁`. -/
theorem wSS_kink_one (h : SSHyp p c₀ c₁ β N) : ¬ DifferentiableAt ℝ (wSS p c₀ c₁ β N) 1 := by
  have hw1 : wSS p c₀ c₁ β N 1 = p + Yn p c₀ c₁ β N := by rw [wSS_low le_rfl]; ring
  refine not_differentiableAt_of_kink (a := p) (b := c₁) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≤ 1)
    rw [wSS_low hu, hw1]; ring
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show (1 : ℝ) < 1 + Aind p c₀ c₁ β N by linarith [h.A_pos]))] with u (hu : 1 ≤ u) hu'
    rw [wSS_left_piece h (ν := 1) le_rfl ⟨by simpa using hu, by simpa using hu'.le⟩, hw1]
    simp only [Nat.cast_one, pow_one, Nat.sub_self, pow_zero, one_mul]
    have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
    field_simp
    ring
  · have : c₁ < p := by nlinarith [h.inv.margin, h.inv.β_lt, h.inv.β_pos, h.inv.c₁_pos]
    exact this.ne'

/-- **Exercise 5.14d.** `w` has a kink at each integer `ν ≥ 2`: slopes `β^{ν−1}p` and
`β^{ν−1}c₁`. -/
theorem wSS_kink_int (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 2 ≤ ν) :
    ¬ DifferentiableAt ℝ (wSS p c₀ c₁ β N) ν := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 2 := ⟨ν - 2, by omega⟩
  have hb := pow_pos h.inv.β_pos (m + 1)
  have hw : wSS p c₀ c₁ β N ((m + 2 : ℕ) : ℝ) = p * (1 - β ^ (m + 2)) / (1 - β) +
      β ^ (m + 1) * Yn p c₀ c₁ β N := by
    rw [wSS_left_piece h (ν := m + 2) (by omega) ⟨le_rfl, by linarith [h.A_pos]⟩]
    simp
  refine not_differentiableAt_of_kink (a := β ^ (m + 1) * p) (b := β ^ (m + 1) * c₁) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds
      (show ((m + 1 : ℕ) : ℝ) + Aind p c₀ c₁ β N < ((m + 2 : ℕ) : ℝ) by
        push_cast; linarith [h.A_lt]))] with u (hu : u ≤ _) hu'
    rw [wSS_right_piece h (ν := m + 1) (by omega) ⟨hu'.le, by push_cast at hu ⊢; linarith⟩, hw]
    have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
    push_cast
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show ((m + 2 : ℕ) : ℝ) < (m + 2 : ℕ) + Aind p c₀ c₁ β N by linarith [h.A_pos]))] with
      u (hu : _ ≤ u) hu'
    rw [wSS_left_piece h (ν := m + 2) (by omega) ⟨hu, hu'.le⟩, hw]
    simp only [show m + 2 - 1 = m + 1 by omega]
    ring
  · intro he
    have : p = c₁ := mul_left_cancel₀ hb.ne' he
    nlinarith [h.inv.margin, h.inv.β_lt, h.inv.β_pos, h.inv.c₁_pos]

/-- **Exercise 5.14d.** `w` has a kink at `ν + A` (`ν ≥ 1`): slopes `β^{ν−1}c₁` and `β^νp`. -/
theorem wSS_kink_A (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) :
    ¬ DifferentiableAt ℝ (wSS p c₀ c₁ β N) (ν + Aind p c₀ c₁ β N) := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  have hb := pow_pos h.inv.β_pos m
  set A := Aind p c₀ c₁ β N
  have hw := wSS_left_piece h (ν := m + 1) hν (u := ((m + 1 : ℕ) : ℝ) + A)
    ⟨by linarith [h.A_pos], le_rfl⟩
  refine not_differentiableAt_of_kink (a := β ^ m * c₁) (b := β ^ (m + 1) * p) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds
      (show ((m + 1 : ℕ) : ℝ) < (m + 1 : ℕ) + A by linarith [h.A_pos]))] with u (hu : u ≤ _) hu'
    rw [wSS_left_piece h hν ⟨hu'.le, hu⟩, hw]
    try simp only [Nat.add_sub_cancel]
    ring
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show ((m + 1 : ℕ) : ℝ) + A < (m + 1 : ℕ) + 1 by linarith [h.A_lt]))] with
      u (hu : _ ≤ u) hu'
    rw [wSS_right_piece h hν ⟨hu, hu'.le⟩, hw]
    try simp only [Nat.add_sub_cancel]
    have hc := cross_eq h (Aind p c₀ c₁ β N)
    rw [sub_self, mul_zero] at hc
    rw [pow_succ]
    nlinarith [hc]
  · intro he
    rw [pow_succ, mul_assoc] at he
    have := mul_left_cancel₀ hb.ne' he
    linarith [h.inv.margin]

/-! ### Exercise 5.14e–g -/

/-- `φ(u) = −c₁u + βw(u)`. -/
noncomputable def phiSS (p c₀ c₁ β : ℝ) (N : ℕ) (u : ℝ) : ℝ := -(c₁ * u) + β * wSS p c₀ c₁ β N u

/-- `φ` is convex on each cell `[ν, ν + 1]`, `ν ≥ 1`: an affine function plus a nonnegative
multiple of the maximum of two affine functions. -/
theorem phi_cell_convex (h : SSHyp p c₀ c₁ β N) {ν : ℕ} (hν : 1 ≤ ν) :
    ConvexOn ℝ (Icc (ν : ℝ) (ν + 1)) (phiSS p c₀ c₁ β N) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hmem : a • x + b • y ∈ Icc (ν : ℝ) (ν + 1) := convex_Icc _ _ hx hy ha hb hab
  simp only [phiSS]
  rw [wSS_cell h hν hmem, wSS_cell h hν hx, wSS_cell h hν hy]
  simp only [smul_eq_mul, cellW]
  set Y := Yn p c₀ c₁ β N
  set q := β ^ (ν - 1)
  have hq : 0 ≤ q := pow_nonneg h.inv.β_pos.le _
  have hb' : b = 1 - a := by linarith
  subst hb'
  -- the maximum of affine functions is convex
  have hmax : max (c₁ * (a * x + (1 - a) * y - ν) + Y) (β * (p * (a * x + (1 - a) * y - ν) + Y))
      ≤ a * max (c₁ * (x - ν) + Y) (β * (p * (x - ν) + Y)) +
        (1 - a) * max (c₁ * (y - ν) + Y) (β * (p * (y - ν) + Y)) := by
    refine max_le ?_ ?_
    · have := mul_le_mul_of_nonneg_left (le_max_left (c₁ * (x - ν) + Y)
        (β * (p * (x - ν) + Y))) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (c₁ * (y - ν) + Y)
        (β * (p * (y - ν) + Y))) hb
      nlinarith
    · have := mul_le_mul_of_nonneg_left (le_max_right (c₁ * (x - ν) + Y)
        (β * (p * (x - ν) + Y))) ha
      have := mul_le_mul_of_nonneg_left (le_max_right (c₁ * (y - ν) + Y)
        (β * (p * (y - ν) + Y))) hb
      nlinarith
  have := mul_le_mul_of_nonneg_left hmax (mul_nonneg h.inv.β_pos.le hq)
  nlinarith

/-- **Exercise 5.14e.** For `u > z ≥ 0`, either `φ(u) ≤ φ(z)` or `φ(u) ≤ φ(n)` for an integer
`n > z`: an order is beaten by not ordering (the supremum approached as `y ↓ 0`) or by an order
that brings the stock to an integer. -/
theorem ex_5_14e (h : SSHyp p c₀ c₁ β N) {z u : ℝ} (hz : 0 ≤ z) (hzu : z < u) :
    phiSS p c₀ c₁ β N u ≤ phiSS p c₀ c₁ β N z ∨
      ∃ n : ℕ, z < n ∧ phiSS p c₀ c₁ β N u ≤ phiSS p c₀ c₁ β N n := by
  set m := ⌊u⌋₊
  have hu0 : 0 ≤ u := by linarith
  have hmu : (m : ℝ) ≤ u := Nat.floor_le hu0
  have hum : u < m + 1 := Nat.lt_floor_add_one u
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- on `[0, 1]`, `φ` increases (slope `βp − c₁ > 0`)
    rw [hm0, Nat.cast_zero, zero_add] at hum
    right
    refine ⟨1, by push_cast; linarith, ?_⟩
    simp only [phiSS, Nat.cast_one]
    rw [wSS_low hum.le, wSS_low le_rfl]
    nlinarith [h.inv.margin]
  · have hconv := phi_cell_convex h (ν := m) hmpos
    have hm1 : ((m + 1 : ℕ) : ℝ) = m + 1 := by push_cast; ring
    have hmm : (m : ℝ) ∈ Icc (m : ℝ) (m + 1) := ⟨le_rfl, by linarith⟩
    have hm1m : (m : ℝ) + 1 ∈ Icc (m : ℝ) (m + 1) := ⟨by linarith, le_rfl⟩
    rcases le_total z m with hzm | hmz
    · -- `u ∈ [m, m + 1]`: the larger end value bounds `φ(u)`
      have hle := hconv.le_max_of_mem_Icc (x := (m : ℝ)) (y := (m : ℝ) + 1) (z := u)
        hmm hm1m ⟨hmu, hum.le⟩
      rcases le_total (phiSS p c₀ c₁ β N m) (phiSS p c₀ c₁ β N (m + 1)) with h1 | h1
      · right
        refine ⟨m + 1, by rw [hm1]; linarith, ?_⟩
        rw [hm1]
        exact hle.trans (max_le h1 le_rfl)
      · rcases eq_or_lt_of_le hzm with hzm' | hzm'
        · left
          rw [hzm']
          exact hle.trans (max_le le_rfl h1)
        · right
          exact ⟨m, hzm', hle.trans (max_le le_rfl h1)⟩
    · have hzI : z ∈ Icc (m : ℝ) (m + 1) := ⟨hmz, by linarith⟩
      have hle := hconv.le_max_of_mem_Icc (x := z) (y := (m : ℝ) + 1) (z := u)
        hzI hm1m ⟨hzu.le, hum.le⟩
      rcases le_total (phiSS p c₀ c₁ β N z) (phiSS p c₀ c₁ β N (m + 1)) with h1 | h1
      · right
        refine ⟨m + 1, by rw [hm1]; linarith, ?_⟩
        rw [hm1]
        exact hle.trans (max_le h1 le_rfl)
      · left
        exact hle.trans (max_le le_rfl h1)

/-- `w(n) = p(1 − βⁿ)/(1 − β) + β^{n−1}Y` at integers `n ≥ 1`. -/
theorem wSS_int (h : SSHyp p c₀ c₁ β N) {n : ℕ} (hn : 1 ≤ n) :
    wSS p c₀ c₁ β N n = p * (1 - β ^ n) / (1 - β) + β ^ (n - 1) * Yn p c₀ c₁ β N := by
  rw [wSS_left_piece h hn ⟨le_rfl, by linarith [h.A_pos]⟩]
  simp

/-- **Exercise 5.14f.** Ordering up to the integer `n ≥ 1` from `z` is worth
`−c₀ − c₁(n − z) + βw(n) = c₁z + r_n + βⁿY`. -/
theorem ex_5_14f (h : SSHyp p c₀ c₁ β N) (z : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    -c₀ - c₁ * (n - z) + β * wSS p c₀ c₁ β N n =
      c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N := by
  rw [wSS_int h hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [rn, Nat.add_sub_cancel, pow_succ]
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  field_simp
  ring

/-- **Exercise 5.14g.** `r_n + βⁿY_N ≤ Y_N` for every `n ≥ 1`, with equality at `n = N`. -/
theorem ex_5_14g (h : SSHyp p c₀ c₁ β N) :
    (∀ n, 1 ≤ n → rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N ≤ Yn p c₀ c₁ β N) ∧
      rn p c₀ c₁ β N + β ^ N * Yn p c₀ c₁ β N = Yn p c₀ c₁ β N := by
  have hr : ∀ n, 1 ≤ n → rn p c₀ c₁ β n = (1 - β ^ n) * Yn p c₀ c₁ β n := fun n hn => by
    have := one_sub_pow_pos h.inv hn
    simp only [Yn]; field_simp
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [hr n hn]
    have := mul_le_mul_of_nonneg_left (h.N_max n hn) (one_sub_pow_pos h.inv hn).le
    linarith
  · rw [hr N h.N_pos]; ring

/-- **The key step of Exercise 5.14h.** For `z ≥ 1` and an integer `n > z`,
`βw(z) > c₁z + r_n + βⁿY`: with `z = ν + α` and `n = ν + k` the difference is at least
`β^ν(1 − β^k)(Y_N − Y_k) + (1 − β^ν)(c₀ + c₁(k − α)) > 0`. -/
theorem key_ineq (h : SSHyp p c₀ c₁ β N) {z : ℝ} (hz : 1 ≤ z) {n : ℕ} (hn : z < n) :
    c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N < β * wSS p c₀ c₁ β N z := by
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = ⌊z⌋₊ := ⟨_, rfl⟩
  have hν : 1 ≤ ν := hνdef ▸ Nat.le_floor (by exact_mod_cast hz)
  have hνz : (ν : ℝ) ≤ z := hνdef ▸ Nat.floor_le (by linarith)
  have hzν : z < ν + 1 := hνdef ▸ Nat.lt_floor_add_one z
  have hk : ν + 1 ≤ n := by
    have : (ν : ℝ) < n := lt_of_le_of_lt hνz hn
    exact_mod_cast this
  obtain ⟨k, hk', rfl⟩ : ∃ k, 1 ≤ k ∧ n = ν + k := ⟨n - ν, by omega, by omega⟩
  have hcell := wSS_cell h hν ⟨hνz, hzν.le⟩
  clear hνdef
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
  set Y := Yn p c₀ c₁ β N
  have hw : p * (1 - β ^ (m + 1)) / (1 - β) + β ^ m * (c₁ * (z - ((m + 1 : ℕ) : ℝ)) + Y) ≤
      wSS p c₀ c₁ β N z := by
    rw [hcell, cellW, Nat.add_sub_cancel]
    have := le_max_left (c₁ * (z - ((m + 1 : ℕ) : ℝ)) + Y) (β * (p * (z - ((m + 1 : ℕ) : ℝ)) + Y))
    nlinarith [pow_nonneg h.inv.β_pos.le m]
  have hYk : rn p c₀ c₁ β k ≤ (1 - β ^ k) * Y := by
    have := mul_le_mul_of_nonneg_left (h.N_max k hk') (one_sub_pow_pos h.inv hk').le
    have e : rn p c₀ c₁ β k = (1 - β ^ k) * Yn p c₀ c₁ β k := by
      have := one_sub_pow_pos h.inv hk'
      simp only [Yn]; field_simp
    rw [e]; exact this
  have hα : z - ((m + 1 : ℕ) : ℝ) < k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk'
    push_cast at hzν ⊢; linarith
  have hbpos := pow_pos h.inv.β_pos (m + 1)
  have h1β : (1 - β) ≠ 0 := by linarith [h.inv.β_lt]
  have hexp : β * (p * (1 - β ^ (m + 1)) / (1 - β) + β ^ m * (c₁ * (z - ((m + 1 : ℕ) : ℝ)) + Y)) -
      (c₁ * z + rn p c₀ c₁ β (m + 1 + k) + β ^ (m + 1 + k) * Y) =
      β ^ (m + 1) * ((1 - β ^ k) * Y - rn p c₀ c₁ β k) +
        (1 - β ^ (m + 1)) * (c₀ + c₁ * (k - (z - ((m + 1 : ℕ) : ℝ)))) := by
    simp only [rn, pow_add, pow_succ]
    push_cast
    field_simp
    ring
  have hfirst : 0 ≤ β ^ (m + 1) * ((1 - β ^ k) * Y - rn p c₀ c₁ β k) :=
    mul_nonneg hbpos.le (by linarith)
  have hlt1 : β ^ (m + 1) < 1 := pow_lt_one₀ h.inv.β_pos.le h.inv.β_lt (by omega)
  have hsecond : 0 < (1 - β ^ (m + 1)) * (c₀ + c₁ * (k - (z - ((m + 1 : ℕ) : ℝ)))) :=
    mul_pos (by linarith) (by nlinarith [h.inv.c₀_pos, h.inv.c₁_pos])
  have := mul_le_mul_of_nonneg_left hw h.inv.β_pos.le
  linarith

/-! ### Exercise 5.14h: the conjecture solves (1) -/

/-- `w` as a bounded continuous function on `ℝ₊`. -/
noncomputable def wBCF (h : SSHyp p c₀ c₁ β N) : Stock →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => wSS p c₀ c₁ β N x.1)
    ((continuousOn_wSS h).comp_continuous continuous_subtype_val fun x => x.2)
    (p / (1 - β) + p + Yn p c₀ c₁ β N) fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (wSS_bounds h x.2.out).1]
      exact (wSS_bounds h x.2.out).2

theorem sext_wBCF (h : SSHyp p c₀ c₁ β N) {x : ℝ} (hx : 0 ≤ x) :
    sext (wBCF h) x = wSS p c₀ c₁ β N x := by
  rw [sext_of_nonneg _ hx]; rfl

/-- The value of an order `y > 0` from `z`, in terms of `φ`. -/
theorem orderVal_wBCF (h : SSHyp p c₀ c₁ β N) {z y : ℝ} (hz : 0 ≤ z) (hy : 0 < y) :
    orderVal c₀ c₁ β (wBCF h) z y = -c₀ + c₁ * z + phiSS p c₀ c₁ β N (z + y) := by
  simp only [orderVal, phiSS, sext_wBCF h (by linarith : 0 ≤ z + y)]
  ring

/-- Every order from `z ≥ 0` is worth at most not ordering minus `c₀`, or some integer
order. -/
theorem order_le (h : SSHyp p c₀ c₁ β N) {z y : ℝ} (hz : 0 ≤ z) (hy : 0 < y) :
    orderVal c₀ c₁ β (wBCF h) z y ≤ -c₀ + β * wSS p c₀ c₁ β N z ∨
      ∃ n : ℕ, z < n ∧ orderVal c₀ c₁ β (wBCF h) z y ≤
        c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N := by
  rw [orderVal_wBCF h hz hy]
  rcases ex_5_14e h hz (by linarith : z < z + y) with h1 | ⟨n, hn, h1⟩
  · left; simp only [phiSS] at h1 ⊢; linarith
  · right
    have hn1 : 1 ≤ n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt hz hn
      exact_mod_cast this
    refine ⟨n, hn, ?_⟩
    rw [← ex_5_14f h z hn1]
    simp only [phiSS] at h1 ⊢
    linarith

/-- An integer order is available whenever `n > z`. -/
theorem order_int (h : SSHyp p c₀ c₁ β N) {z : ℝ} (hz : 0 ≤ z) {n : ℕ} (hn : z < n) :
    c₁ * z + rn p c₀ c₁ β n + β ^ n * Yn p c₀ c₁ β N ≤ ordSup c₀ c₁ β (wBCF h) z := by
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt hz hn
    exact_mod_cast this
  refine le_trans (le_of_eq ?_) (le_csSup (bddAbove_ordSup h.inv (wBCF h) z)
    ⟨n - z, by simp only [Set.mem_Ioi]; linarith, rfl⟩)
  rw [orderVal, sext_wBCF h (by linarith), show z + (n - z) = n by ring, ← ex_5_14f h z hn1]

/-- **Exercise 5.14h.** `w` satisfies the functional equation (1) at every `x ≥ 0`. -/
theorem ex_5_14h (h : SSHyp p c₀ c₁ β N) (x : Stock) :
    invRHS p c₀ c₁ β (wBCF h) x = wBCF h x := by
  have hx := x.2.out
  have hY := h.Y_pos
  obtain ⟨hg, hgN⟩ := ex_5_14g h
  change p * min x.1 1 + max (β * sext (wBCF h) (leftover x.1))
    (ordSup c₀ c₁ β (wBCF h) (leftover x.1)) = wSS p c₀ c₁ β N x.1
  have hz0 : 0 ≤ leftover x.1 := le_max_right _ _
  rw [sext_wBCF h hz0]
  rcases le_or_gt x.1 1 with hx1 | hx1
  · -- `x ≤ 1`: order `N`, worth `Y`
    have hz : leftover x.1 = 0 := max_eq_right (by linarith)
    rw [hz, wSS_low (by norm_num : (0 : ℝ) ≤ 1), wSS_low hx1, min_eq_left hx1]
    have hlow := order_int h (le_refl 0) (n := N) (by exact_mod_cast h.N_pos)
    have hlow' : Yn p c₀ c₁ β N ≤ ordSup c₀ c₁ β (wBCF h) 0 := by linarith [hgN]
    have hup : ordSup c₀ c₁ β (wBCF h) 0 ≤ Yn p c₀ c₁ β N := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := 0) le_rfl hy with h1 | ⟨n, hn, h1⟩
      · rw [wSS_low (by norm_num : (0 : ℝ) ≤ 1)] at h1
        nlinarith [h.inv.c₀_pos, h.inv.β_lt]
      · have hn1 : 1 ≤ n := by exact_mod_cast hn
        linarith [hg n hn1]
    rw [le_antisymm hup hlow', max_eq_right]
    nlinarith [h.inv.β_lt]
  rcases lt_or_ge x.1 2 with hx2 | hx2
  · -- `1 < x < 2`: compare not ordering with ordering up to `N`
    have hz : leftover x.1 = x.1 - 1 := max_eq_left (by linarith)
    rw [hz, min_eq_right hx1.le, mul_one, wSS_one_two h ⟨hx1.le, hx2.le⟩]
    have hlow := order_int h (by linarith : (0 : ℝ) ≤ x.1 - 1) (n := N)
      (by have : (1 : ℝ) ≤ N := by exact_mod_cast h.N_pos
          linarith)
    have hlow' : c₁ * (x.1 - 1) + Yn p c₀ c₁ β N ≤ ordSup c₀ c₁ β (wBCF h) (x.1 - 1) := by
      linarith [hgN]
    have hup : ordSup c₀ c₁ β (wBCF h) (x.1 - 1) ≤
        max (β * wSS p c₀ c₁ β N (x.1 - 1)) (c₁ * (x.1 - 1) + Yn p c₀ c₁ β N) := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := x.1 - 1) (by linarith) hy with h1 | ⟨n, hn, h1⟩
      · exact (h1.trans (by linarith [h.inv.c₀_pos])).trans (le_max_left _ _)
      · have hn1 : 1 ≤ n := by
          have : (0 : ℝ) < n := lt_of_le_of_lt (by linarith) hn
          exact_mod_cast this
        exact (h1.trans (by linarith [hg n hn1])).trans (le_max_right _ _)
    rw [max_comm (c₁ * (x.1 - 1) + _)]
    congr 1
    refine le_antisymm (max_le (le_max_left _ _) hup) (max_le (le_max_left _ _) ?_)
    exact hlow'.trans (le_max_right _ _)
  · -- `x ≥ 2`: not ordering is optimal (`key_ineq`)
    have hz : leftover x.1 = x.1 - 1 := max_eq_left (by linarith)
    rw [hz, min_eq_right (by linarith), mul_one, wSS_five h hx2]
    have hup : ordSup c₀ c₁ β (wBCF h) (x.1 - 1) ≤ β * wSS p c₀ c₁ β N (x.1 - 1) := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := x.1 - 1) (by linarith) hy with h1 | ⟨n, hn, h1⟩
      · linarith [h.inv.c₀_pos]
      · exact h1.trans (key_ineq h (by linarith) hn).le
    rw [max_eq_left hup]

/-- **Exercise 5.14h.** The solution of (1) is `w`: the (s, S) conjecture is correct. -/
theorem ex_5_14_value (h : SSHyp p c₀ c₁ β N) {v : Stock →ᵇ ℝ}
    (hv : ∀ x, v x = invRHS p c₀ c₁ β v x) : v = wBCF h := by
  obtain ⟨v₀, -, huniq, -⟩ := ex_5_14a h.inv
  rw [huniq v hv, huniq (wBCF h) fun x => (ex_5_14h h x).symm]

/-- **The (s, S) policy.** With `s = 1 + A` and `S = N`: below `s` it is strictly optimal to order
up to `N` (from stock `z` left after sales, order `N − z`); above `s` not ordering is optimal;
at `x = s` ordering up to `N` and not ordering are both optimal, so the optimal policy is not
unique. -/
theorem ex_5_14_policy (h : SSHyp p c₀ c₁ β N) :
    (∀ x : Stock, x.1 < 1 + Aind p c₀ c₁ β N →
      β * sext (wBCF h) (leftover x.1) < orderVal c₀ c₁ β (wBCF h) (leftover x.1)
        (N - leftover x.1) ∧
      orderVal c₀ c₁ β (wBCF h) (leftover x.1) (N - leftover x.1) =
        ordSup c₀ c₁ β (wBCF h) (leftover x.1)) ∧
    (∀ x : Stock, 1 + Aind p c₀ c₁ β N ≤ x.1 →
      ordSup c₀ c₁ β (wBCF h) (leftover x.1) ≤ β * sext (wBCF h) (leftover x.1)) ∧
    (∀ x : Stock, x.1 = 1 + Aind p c₀ c₁ β N →
      orderVal c₀ c₁ β (wBCF h) (leftover x.1) (N - leftover x.1) =
        β * sext (wBCF h) (leftover x.1)) := by
  have hA0 := h.A_pos
  have hA1 := h.A_lt
  have hY := h.Y_pos
  obtain ⟨hg, hgN⟩ := ex_5_14g h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.N_pos
  -- the order up to `N` from `z < 1` is worth `c₁z + Y`
  have hvalN : ∀ z : ℝ, 0 ≤ z → z < 1 →
      orderVal c₀ c₁ β (wBCF h) z (N - z) = c₁ * z + Yn p c₀ c₁ β N := fun z hz hz1 => by
    rw [orderVal, sext_wBCF h (by linarith), show z + (N - z) = (N : ℝ) by ring,
      ex_5_14f h z h.N_pos]
    linarith [hgN]
  -- for `z < 1` the supremum is `max{βw(z) − c₀, c₁z + Y}` at most, and `c₁z + Y` at least
  have hsup : ∀ z : ℝ, 0 ≤ z → z < 1 → ordSup c₀ c₁ β (wBCF h) z ≤
      max (-c₀ + β * wSS p c₀ c₁ β N z) (c₁ * z + Yn p c₀ c₁ β N) := fun z hz hz1 => by
    refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases order_le h hz hy with h1 | ⟨n, hn, h1⟩
    · exact h1.trans (le_max_left _ _)
    · have hn1 : 1 ≤ n := by
        have : (0 : ℝ) < n := lt_of_le_of_lt hz hn
        exact_mod_cast this
      exact (h1.trans (by linarith [hg n hn1])).trans (le_max_right _ _)
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have hz0 : 0 ≤ leftover x.1 := le_max_right _ _
    have hz1 : leftover x.1 < Aind p c₀ c₁ β N := by
      unfold leftover; exact max_lt (by linarith) hA0
    rw [sext_wBCF h hz0, hvalN _ hz0 (by linarith),
      wSS_low (by linarith : leftover x.1 ≤ 1)]
    have hc := cross_eq h (leftover x.1)
    have hlt : β * (p * leftover x.1 + Yn p c₀ c₁ β N) < c₁ * leftover x.1 + Yn p c₀ c₁ β N := by
      nlinarith [h.inv.margin]
    refine ⟨hlt, le_antisymm ?_ ?_⟩
    · have := order_int h hz0 (n := N) (by linarith)
      linarith [hgN]
    · refine (hsup _ hz0 (by linarith)).trans (max_le ?_ le_rfl)
      rw [wSS_low (by linarith : leftover x.1 ≤ 1)]
      linarith [h.inv.c₀_pos]
  · have hz : leftover x.1 = x.1 - 1 := max_eq_left (by linarith)
    rw [hz, sext_wBCF h (by linarith)]
    rcases lt_or_ge x.1 2 with hx2 | hx2
    · refine (hsup _ (by linarith) (by linarith)).trans (max_le (by linarith [h.inv.c₀_pos]) ?_)
      rw [wSS_low (by linarith : x.1 - 1 ≤ 1)]
      exact (cross_iff h _).2 (by linarith)
    · refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      rcases order_le h (z := x.1 - 1) (by linarith) hy with h1 | ⟨n, hn, h1⟩
      · linarith [h.inv.c₀_pos]
      · exact h1.trans (key_ineq h (by linarith) hn).le
  · have hz : leftover x.1 = Aind p c₀ c₁ β N := by
      unfold leftover; rw [hx]; simp [hA0.le]
    rw [hz, hvalN _ hA0.le hA1, sext_wBCF h hA0.le, wSS_low hA1.le]
    have := cross_eq h (Aind p c₀ c₁ β N)
    simp only [sub_self, mul_zero] at this
    linarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The inventory problem in continuous time

SLP §5.15, pp. 122–123: demand is a flow of `a > 0` units per unit time, the interest rate is
`r > 0`, an order of `y` costs `c₀ + c₁y`, and the price is `p`. Selling a stock that lasts `τ`
units of time earns `S(τ) = ∫₀^τ e^{−rt}ap dt = ap(1 − e^{−rτ})/r` (`Srev_integral`), and
`S(τ + s) = S(τ) + e^{−rτ}S(s)` (`Srev_add`).

* **Exercise 5.15a** (`ex_5_15a`): with `G(τ) = (1 + e^{−rτ} + e^{−2rτ} + …)(S(τ) − c₀ − c₁aτ)`
  (`Gcyc_geometric`), `Y* = max{0, sup_{τ > 0} G(τ)}` is well defined and finite (`G ≤ ap/r`), and
  when `Y* > 0` the supremum is attained, at a unique `τ*` (`Gcyc_argmax_unique`: the numerator
  of `G'` is strictly increasing, so `G` rises then falls).
* **Exercise 5.15b**: `w(A) = S(A/a) + e^{−rA/a}Y*` satisfies the functional equation
  (`ex_5_15b`): no plan beats it (`Vval_le`: ordering early only brings the fixed cost forward,
  and each cycle is worth at most `Y*`), and when `Y* > 0` the policy "order `aτ*` units after
  `A/a` units of time" attains it (`Vval_attain`). That policy is the unique optimal one
  (`ex_5_15b_unique`).
-/

open Real Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {a p r c₀ c₁ : ℝ}

/-- `S(τ) = ap(1 − e^{−rτ})/r`. -/
noncomputable def Srev (a p r τ : ℝ) : ℝ := a * p * (1 - exp (-r * τ)) / r

/-- The hypotheses of SLP §5.15. -/
structure CTHyp (a p r c₀ c₁ : ℝ) : Prop where
  a_pos : 0 < a
  p_pos : 0 < p
  r_pos : 0 < r
  c₀_pos : 0 < c₀
  c₁_pos : 0 < c₁

/-- `S(τ) = ∫₀^τ e^{−rt}ap dt`. -/
theorem Srev_integral (h : CTHyp a p r c₀ c₁) (τ : ℝ) :
    Srev a p r τ = ∫ t in (0 : ℝ)..τ, exp (-r * t) * (a * p) := by
  have hr := h.r_pos.ne'
  have hd : ∀ t ∈ uIcc (0 : ℝ) τ, HasDerivAt (fun t => -(a * p) * exp (-r * t) / r)
      (exp (-r * t) * (a * p)) t := fun t _ => by
    have := ((((hasDerivAt_id' t).const_mul (-r)).exp).const_mul (-(a * p))).div_const r
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => exp (-r * t) * (a * p)).intervalIntegrable 0 τ)]
  simp only [Srev, mul_zero, exp_zero]
  field_simp
  ring

/-- `S(τ + s) = S(τ) + e^{−rτ}S(s)`. -/
theorem Srev_add (h : CTHyp a p r c₀ c₁) (τ s : ℝ) :
    Srev a p r (τ + s) = Srev a p r τ + exp (-r * τ) * Srev a p r s := by
  have hr := h.r_pos.ne'
  simp only [Srev]
  rw [show -r * (τ + s) = -r * τ + -r * s by ring, exp_add]
  field_simp
  ring

theorem exp_neg_lt_one (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) : exp (-r * σ) < 1 :=
  exp_lt_one_iff.2 (by nlinarith [h.r_pos])

/-- The value of one cycle, per unit of discounting: `G(τ) = (S(τ) − c₀ − c₁aτ)/(1 − e^{−rτ})`. -/
noncomputable def Gcyc (a p r c₀ c₁ σ : ℝ) : ℝ :=
  (Srev a p r σ - c₀ - c₁ * a * σ) / (1 - exp (-r * σ))

/-- `G(τ) = (1 + e^{−rτ} + e^{−2rτ} + …)(S(τ) − c₀ − c₁aτ)`: repeating the cycle forever. -/
theorem Gcyc_geometric (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : ℕ => exp (-r * σ) ^ k * (Srev a p r σ - c₀ - c₁ * a * σ))
      (Gcyc a p r c₀ c₁ σ) := by
  have := (hasSum_geometric_of_lt_one (exp_pos _).le (exp_neg_lt_one h hσ)).mul_right
    (Srev a p r σ - c₀ - c₁ * a * σ)
  convert this using 1
  simp only [Gcyc, div_eq_mul_inv]
  ring

/-- `G(τ) = ap/r − (c₀ + c₁aτ)/(1 − e^{−rτ})`. -/
theorem Gcyc_eq (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    Gcyc a p r c₀ c₁ σ = a * p / r - (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) := by
  have hlt := exp_neg_lt_one h hσ
  have hr := h.r_pos.ne'
  simp only [Gcyc, Srev]
  generalize exp (-r * σ) = e at hlt ⊢
  have h1 : 1 - e ≠ 0 := by linarith
  field_simp
  ring

theorem Gcyc_le (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) : Gcyc a p r c₀ c₁ σ ≤ a * p / r := by
  rw [Gcyc_eq h hσ]
  have hc : 0 < c₀ + c₁ * a * σ := by
    have := mul_pos (mul_pos h.c₁_pos h.a_pos) hσ; linarith [h.c₀_pos]
  have : 0 < (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) :=
    div_pos hc (by linarith [exp_neg_lt_one h hσ])
  linarith

/-- `Y* = max{0, sup_{τ > 0} G(τ)}`. -/
noncomputable def Ystar (a p r c₀ c₁ : ℝ) : ℝ := max 0 (sSup (Gcyc a p r c₀ c₁ '' Ioi 0))

theorem bddAbove_Gcyc (h : CTHyp a p r c₀ c₁) : BddAbove (Gcyc a p r c₀ c₁ '' Ioi 0) :=
  ⟨a * p / r, by rintro _ ⟨σ, hσ, rfl⟩; exact Gcyc_le h hσ⟩

theorem Gcyc_le_Ystar (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    Gcyc a p r c₀ c₁ σ ≤ Ystar a p r c₀ c₁ :=
  (le_csSup (bddAbove_Gcyc h) ⟨σ, hσ, rfl⟩).trans (le_max_right _ _)

theorem continuousOn_Gcyc (h : CTHyp a p r c₀ c₁) : ContinuousOn (Gcyc a p r c₀ c₁) (Ioi 0) := by
  refine ContinuousOn.div (by unfold Srev; fun_prop) (by fun_prop) fun σ hσ => ?_
  linarith [exp_neg_lt_one h hσ]

/-- **Exercise 5.15a.** `Y*` is well defined and finite, `0 ≤ Y* ≤ ap/r`, and if `Y* > 0` the
supremum is attained at some `τ* > 0`. -/
theorem ex_5_15a (h : CTHyp a p r c₀ c₁) :
    BddAbove (Gcyc a p r c₀ c₁ '' Ioi 0) ∧ 0 ≤ Ystar a p r c₀ c₁ ∧
      Ystar a p r c₀ c₁ ≤ a * p / r ∧
      (0 < Ystar a p r c₀ c₁ → ∃ τ > 0, Gcyc a p r c₀ c₁ τ = Ystar a p r c₀ c₁) := by
  have hap : 0 < a * p / r := div_pos (mul_pos h.a_pos h.p_pos) h.r_pos
  have hne : (Gcyc a p r c₀ c₁ '' Ioi 0).Nonempty := ⟨_, 1, by norm_num, rfl⟩
  have hub : ∀ v ∈ Gcyc a p r c₀ c₁ '' Ioi 0, v ≤ a * p / r := by
    rintro _ ⟨σ, hσ, rfl⟩; exact Gcyc_le h hσ
  refine ⟨bddAbove_Gcyc h, le_max_left _ _, max_le hap.le (csSup_le hne hub), fun hY => ?_⟩
  -- some cycle is profitable
  have hS : 0 < sSup (Gcyc a p r c₀ c₁ '' Ioi 0) := by
    by_contra hle; push Not at hle
    have : Ystar a p r c₀ c₁ = 0 := max_eq_left hle
    linarith
  obtain ⟨_, ⟨σ₁, hσ₁, rfl⟩, hG₁⟩ := exists_lt_of_lt_csSup hne hS
  -- `G < 0` near `0` and far out
  set ε := min σ₁ (c₀ / (2 * a * p))
  have hε : 0 < ε := lt_min hσ₁ (div_pos h.c₀_pos (by nlinarith [h.a_pos, h.p_pos]))
  have hsmall : ∀ σ, 0 < σ → σ ≤ ε → Gcyc a p r c₀ c₁ σ < 0 := fun σ hσ hσε => by
    rw [Gcyc_eq h hσ]
    have hd : 0 < 1 - exp (-r * σ) := by linarith [exp_neg_lt_one h hσ]
    have hd' : 1 - exp (-r * σ) ≤ r * σ := by linarith [add_one_le_exp (-r * σ)]
    have hσc : σ ≤ c₀ / (2 * a * p) := hσε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by nlinarith [h.a_pos, h.p_pos])] at hσc
    have hap0 : 0 < a * p := mul_pos h.a_pos h.p_pos
    have h1 : a * p * (1 - exp (-r * σ)) ≤ a * p * (r * σ) := mul_le_mul_of_nonneg_left hd' hap0.le
    have h2 : a * p * (r * σ) ≤ r * c₀ / 2 := by nlinarith [h.r_pos]
    have h3 : 0 ≤ c₁ * a * σ := (mul_pos (mul_pos h.c₁_pos h.a_pos) hσ).le
    have : a * p / r < (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) := by
      rw [div_lt_div_iff₀ h.r_pos hd]
      nlinarith [h.c₀_pos, h.r_pos]
    linarith
  set M := max σ₁ (p / (r * c₁) + 1)
  have hlarge : ∀ σ, M < σ → Gcyc a p r c₀ c₁ σ < 0 := fun σ hσ => by
    have hσ0 : 0 < σ := lt_of_le_of_lt (le_max_left _ _ |>.trans' hσ₁.le) hσ
    rw [Gcyc_eq h hσ0]
    have hd : 0 < 1 - exp (-r * σ) := by linarith [exp_neg_lt_one h hσ0]
    have hd1 : 1 - exp (-r * σ) ≤ 1 := by linarith [exp_pos (-r * σ)]
    have hnum : 0 < c₀ + c₁ * a * σ := by
      have := mul_pos (mul_pos h.c₁_pos h.a_pos) hσ0; linarith [h.c₀_pos]
    have h1 : c₀ + c₁ * a * σ ≤ (c₀ + c₁ * a * σ) / (1 - exp (-r * σ)) := by
      rw [le_div_iff₀ hd]; nlinarith
    have hσM : p / (r * c₁) < σ := by
      have := (le_max_right σ₁ (p / (r * c₁) + 1)).trans_lt hσ; linarith
    rw [div_lt_iff₀ (mul_pos h.r_pos h.c₁_pos)] at hσM
    have : a * p / r < c₁ * a * σ := by
      rw [div_lt_iff₀ h.r_pos]; nlinarith [h.a_pos]
    linarith [h.c₀_pos]
  -- maximize over the compact `[ε, M]`
  have hεM : ε ≤ M := (min_le_left _ _).trans (le_max_left _ _)
  obtain ⟨τ, hτ, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hεM)
    ((continuousOn_Gcyc h).mono fun σ hσ => lt_of_lt_of_le hε hσ.1)
  have hτ0 : 0 < τ := lt_of_lt_of_le hε hτ.1
  have hG₁τ : Gcyc a p r c₀ c₁ σ₁ ≤ Gcyc a p r c₀ c₁ τ :=
    hmax ⟨min_le_left _ _, le_max_left _ _⟩
  have hglobal : ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ := fun σ hσ => by
    by_cases h1 : σ ≤ ε
    · linarith [hsmall σ hσ h1]
    by_cases h2 : M < σ
    · linarith [hlarge σ h2]
    push Not at h1 h2
    exact hmax ⟨h1.le, h2⟩
  have hsup : sSup (Gcyc a p r c₀ c₁ '' Ioi 0) = Gcyc a p r c₀ c₁ τ :=
    IsGreatest.csSup_eq ⟨⟨τ, hτ0, rfl⟩, by rintro _ ⟨σ, hσ, rfl⟩; exact hglobal σ hσ⟩
  refine ⟨τ, hτ0, ?_⟩
  rw [Ystar, hsup, max_eq_right (by linarith)]

/-- The numerator of `h'`, where `h(σ) = (c₀ + c₁aσ)/(1 − e^{−rσ})` and `G = ap/r − h`. -/
noncomputable def Ncyc (a r c₀ c₁ σ : ℝ) : ℝ :=
  c₁ * a * (1 - exp (-r * σ)) - r * exp (-r * σ) * (c₀ + c₁ * a * σ)

theorem Ncyc_strictMono (h : CTHyp a p r c₀ c₁) : StrictMonoOn (Ncyc a r c₀ c₁) (Ici 0) := by
  have hd : ∀ σ, HasDerivAt (Ncyc a r c₀ c₁)
      (r ^ 2 * exp (-r * σ) * (c₀ + c₁ * a * σ)) σ := fun σ => by
    have he : HasDerivAt (fun s => exp (-r * s)) (exp (-r * σ) * (-r)) σ := by
      simpa using ((hasDerivAt_id' σ).const_mul (-r)).exp
    have := ((he.const_mul (c₁ * a)).const_sub (c₁ * a)).sub
      ((he.const_mul r).mul (((hasDerivAt_id' σ).const_mul (c₁ * a)).const_add c₀))
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by ring)
    simp only [Ncyc, Pi.sub_apply, Pi.mul_apply]
    ring
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun σ _ => (hd σ).continuousAt.continuousWithinAt) fun σ hσ => ?_
  rw [interior_Ici] at hσ
  rw [(hd σ).deriv]
  have hσ' : (0 : ℝ) < σ := hσ
  have h1 := exp_pos (-r * σ)
  have h2 : 0 < c₀ + c₁ * a * σ := by
    have := mul_pos (mul_pos h.c₁_pos h.a_pos) hσ'; linarith [h.c₀_pos]
  have h3 := pow_pos h.r_pos 2
  positivity

theorem hasDerivAt_hcyc (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s => (c₀ + c₁ * a * s) / (1 - exp (-r * s)))
      (Ncyc a r c₀ c₁ σ / (1 - exp (-r * σ)) ^ 2) σ := by
  have hd : 1 - exp (-r * σ) ≠ 0 := by linarith [exp_neg_lt_one h hσ]
  have he := ((hasDerivAt_id' σ).const_mul (-r)).exp
  have := (((hasDerivAt_id' σ).const_mul (c₁ * a)).const_add c₀).div (he.const_sub 1) hd
  convert this using 1
  simp only [Ncyc]
  ring

/-- **Exercise 5.15a.** `G` has at most one maximizer on `(0, ∞)`: at a maximizer `h' = 0`, so the
strictly increasing `N` vanishes there. -/
theorem Gcyc_argmax_unique (h : CTHyp a p r c₀ c₁) {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h₂ : 0 < τ₂)
    (hm₁ : ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ₁)
    (hm₂ : ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ₂) : τ₁ = τ₂ := by
  -- at a maximizer of `G`, `h` has a local minimum, so `N = 0`
  have hzero : ∀ τ, 0 < τ → (∀ σ, 0 < σ → Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ) →
      Ncyc a r c₀ c₁ τ = 0 := fun τ hτ hm => by
    have hloc : IsLocalMin (fun s => (c₀ + c₁ * a * s) / (1 - exp (-r * s))) τ := by
      filter_upwards [Ioi_mem_nhds hτ] with s hs
      have := hm s hs
      rw [Gcyc_eq h hs, Gcyc_eq h hτ] at this
      linarith
    have := hloc.hasDerivAt_eq_zero (hasDerivAt_hcyc h hτ)
    have hd : (1 - exp (-r * τ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [exp_neg_lt_one h hτ])
    exact (div_eq_zero_iff.1 this).resolve_right hd
  have e₁ := hzero τ₁ h₁ hm₁
  have e₂ := hzero τ₂ h₂ hm₂
  exact (Ncyc_strictMono h).injOn (mem_Ici.2 h₁.le) (mem_Ici.2 h₂.le) (e₁.trans e₂.symm)

/-! ### Exercise 5.15b -/

/-- `w(A) = S(A/a) + e^{−rA/a}Y*`. -/
noncomputable def wCT (a p r c₀ c₁ A : ℝ) : ℝ :=
  Srev a p r (A / a) + exp (-r * (A / a)) * Ystar a p r c₀ c₁

/-- The value of ordering `y` at time `τ`, starting from stock `A`. -/
noncomputable def Vval (a p r c₀ c₁ A τ y : ℝ) : ℝ :=
  Srev a p r (min τ (A / a)) +
    exp (-r * τ) * (wCT a p r c₀ c₁ (max (A - a * τ) 0 + y) - c₀ - c₁ * y)

/-- A cycle of length `σ` followed by the continuation is worth at most `Y*`. -/
theorem cycle_le (h : CTHyp a p r c₀ c₁) {σ : ℝ} (hσ : 0 < σ) :
    Srev a p r σ - c₀ - c₁ * a * σ + exp (-r * σ) * Ystar a p r c₀ c₁ ≤ Ystar a p r c₀ c₁ := by
  have hd : 0 < 1 - exp (-r * σ) := by linarith [exp_neg_lt_one h hσ]
  have := Gcyc_le_Ystar h hσ
  rw [Gcyc, div_le_iff₀ hd] at this
  linarith

/-- No plan beats `w(A)`. -/
theorem Vval_le (h : CTHyp a p r c₀ c₁) {A τ y : ℝ} (hy : 0 < y) :
    Vval a p r c₀ c₁ A τ y ≤ wCT a p r c₀ c₁ A := by
  have ha := h.a_pos
  have hY := (ex_5_15a h).2.1
  have hσ : 0 < y / a := div_pos hy ha
  have hcyc := cycle_le h hσ
  rcases le_total τ (A / a) with hτA | hτA
  · -- ordering before the stock runs out only brings the fixed cost forward
    have hx : 0 ≤ A - a * τ := by rw [le_div_iff₀ ha] at hτA; linarith
    have e1 : (A - a * τ + y) / a = (A / a - τ) + y / a := by field_simp
    have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) +
        exp (-r * (A / a)) * (Srev a p r (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) -
          exp (-r * τ) * (c₀ + c₁ * y) := by
      simp only [Vval, wCT, min_eq_left hτA, max_eq_left hx, e1]
      rw [Srev_add h (A / a - τ), show A / a = τ + (A / a - τ) by ring, Srev_add h τ]
      rw [show τ + (A / a - τ) = A / a by ring]
      rw [show -r * (A / a - τ + y / a) = -r * (A / a - τ) + -r * (y / a) by ring, exp_add,
        show -r * (A / a) = -r * τ + -r * (A / a - τ) by ring, exp_add]
      ring
    have hexp : exp (-r * (A / a)) ≤ exp (-r * τ) :=
      exp_le_exp.2 (by nlinarith [h.r_pos])
    have hcost : 0 < c₀ + c₁ * y := by nlinarith [h.c₀_pos, h.c₁_pos]
    have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
    rw [hV, wCT]
    have h1 := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * (A / a))).le
    have h2 := mul_le_mul_of_nonneg_right hexp hcost.le
    have h3 : exp (-r * (A / a)) * (c₀ + c₁ * y) =
        exp (-r * (A / a)) * (c₀ + c₁ * a * (y / a)) := by rw [hcy]
    linarith
  · -- waiting past `A/a` only delays the next cycle
    have hx : A - a * τ ≤ 0 := by rw [div_le_iff₀ ha] at hτA; linarith
    have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) + exp (-r * τ) *
        (Srev a p r (y / a) - c₀ - c₁ * a * (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) := by
      simp only [Vval, wCT, min_eq_right hτA, max_eq_right hx, zero_add]
      have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
      rw [hcy]; ring
    have hexp : exp (-r * τ) ≤ exp (-r * (A / a)) := exp_le_exp.2 (by nlinarith [h.r_pos])
    rw [hV, wCT]
    have := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * τ)).le
    have := mul_le_mul_of_nonneg_right hexp hY
    linarith

/-- When `Y* > 0`, ordering `aτ*` units after `A/a` units of time attains `w(A)`. -/
theorem Vval_attain (h : CTHyp a p r c₀ c₁) {A τs : ℝ} (hτs : 0 < τs)
    (hG : Gcyc a p r c₀ c₁ τs = Ystar a p r c₀ c₁) :
    Vval a p r c₀ c₁ A (A / a) (a * τs) = wCT a p r c₀ c₁ A := by
  have ha := h.a_pos
  have hd : 0 < 1 - exp (-r * τs) := by linarith [exp_neg_lt_one h hτs]
  have hx : A - a * (A / a) = 0 := by field_simp; ring
  have hcyc : Srev a p r τs - c₀ - c₁ * a * τs = Ystar a p r c₀ c₁ * (1 - exp (-r * τs)) := by
    have := hG
    rw [Gcyc, div_eq_iff hd.ne'] at this
    exact this
  simp only [Vval, wCT, min_self, hx, max_self, zero_add]
  rw [show a * τs / a = τs by field_simp]
  have e : Srev a p r τs + exp (-r * τs) * Ystar a p r c₀ c₁ - c₀ - c₁ * (a * τs) =
      Ystar a p r c₀ c₁ := by linarith
  rw [e]

/-- **Exercise 5.15b.** `w` satisfies the functional equation:
`w(A) = max{S(A/a), sup_{τ ≥ 0, y > 0} V(A, τ, y)}`. -/
theorem ex_5_15b (h : CTHyp a p r c₀ c₁) {A : ℝ} (hA : 0 ≤ A) :
    wCT a p r c₀ c₁ A = max (Srev a p r (A / a))
      (sSup {v | ∃ τ y, 0 ≤ τ ∧ 0 < y ∧ v = Vval a p r c₀ c₁ A τ y}) := by
  have hY := (ex_5_15a h).2.1
  have hne : {v | ∃ τ y, 0 ≤ τ ∧ 0 < y ∧ v = Vval a p r c₀ c₁ A τ y}.Nonempty :=
    ⟨_, 0, 1, le_rfl, one_pos, rfl⟩
  have hub : ∀ v ∈ {v | ∃ τ y, 0 ≤ τ ∧ 0 < y ∧ v = Vval a p r c₀ c₁ A τ y},
      v ≤ wCT a p r c₀ c₁ A := by
    rintro _ ⟨τ, y, hτ, hy, rfl⟩
    exact Vval_le h hy
  have hS : Srev a p r (A / a) ≤ wCT a p r c₀ c₁ A := by
    have := mul_nonneg (exp_pos (-r * (A / a))).le hY
    simp only [wCT]; linarith
  refine le_antisymm ?_ (max_le hS (csSup_le hne hub))
  rcases eq_or_lt_of_le hY with hY0 | hYpos
  · -- `Y* = 0`: never ordering is optimal
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    simp only [wCT, ← hY0, mul_zero, add_zero]
  · obtain ⟨τs, hτs, hG⟩ := (ex_5_15a h).2.2.2 hYpos
    refine le_trans ?_ (le_max_right _ _)
    refine le_csSup ⟨_, hub⟩ ⟨A / a, a * τs, div_nonneg hA h.a_pos.le,
      mul_pos h.a_pos hτs, ?_⟩
    rw [Vval_attain h hτs hG]

/-- **Exercise 5.15b.** If `Y* > 0`, the unique optimal policy is to order `aτ*` units when the
stock runs out, after `A/a` units of time; not ordering is strictly worse. -/
theorem ex_5_15b_unique (h : CTHyp a p r c₀ c₁) (hYpos : 0 < Ystar a p r c₀ c₁) {A τs : ℝ}
    (hτs : 0 < τs) (hG : Gcyc a p r c₀ c₁ τs = Ystar a p r c₀ c₁) :
    Srev a p r (A / a) < wCT a p r c₀ c₁ A ∧
      ∀ τ y, 0 ≤ τ → 0 < y → Vval a p r c₀ c₁ A τ y = wCT a p r c₀ c₁ A →
        τ = A / a ∧ y = a * τs := by
  have ha := h.a_pos
  refine ⟨by simp only [wCT]; nlinarith [exp_pos (-r * (A / a))], fun τ y hτ hy heq => ?_⟩
  have hσ : 0 < y / a := div_pos hy ha
  have hcyc := cycle_le h hσ
  -- `τ < A/a` loses the earlier fixed cost
  have hτge : A / a ≤ τ := by
    by_contra hlt
    push Not at hlt
    have hx : 0 ≤ A - a * τ := by rw [lt_div_iff₀ ha] at hlt; linarith
    have e1 : (A - a * τ + y) / a = (A / a - τ) + y / a := by field_simp
    have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) +
        exp (-r * (A / a)) * (Srev a p r (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) -
          exp (-r * τ) * (c₀ + c₁ * y) := by
      simp only [Vval, wCT, min_eq_left hlt.le, max_eq_left hx, e1]
      rw [Srev_add h (A / a - τ), show A / a = τ + (A / a - τ) by ring, Srev_add h τ]
      rw [show τ + (A / a - τ) = A / a by ring]
      rw [show -r * (A / a - τ + y / a) = -r * (A / a - τ) + -r * (y / a) by ring, exp_add,
        show -r * (A / a) = -r * τ + -r * (A / a - τ) by ring, exp_add]
      ring
    have hexp : exp (-r * (A / a)) < exp (-r * τ) := exp_lt_exp.2 (by nlinarith [h.r_pos])
    have hcost : 0 < c₀ + c₁ * y := by nlinarith [h.c₀_pos, h.c₁_pos]
    have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
    rw [hV, wCT] at heq
    have h1 := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * (A / a))).le
    have h2 := mul_lt_mul_of_pos_right hexp hcost
    have h3 : exp (-r * (A / a)) * (c₀ + c₁ * y) =
        exp (-r * (A / a)) * (c₀ + c₁ * a * (y / a)) := by rw [hcy]
    linarith
  have hx : A - a * τ ≤ 0 := by rw [div_le_iff₀ ha] at hτge; linarith
  have hV : Vval a p r c₀ c₁ A τ y = Srev a p r (A / a) + exp (-r * τ) *
      (Srev a p r (y / a) - c₀ - c₁ * a * (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) := by
    simp only [Vval, wCT, min_eq_right hτge, max_eq_right hx, zero_add]
    have hcy : c₁ * y = c₁ * a * (y / a) := by field_simp
    rw [hcy]; ring
  rw [hV, wCT] at heq
  -- waiting past `A/a` loses discounting on `Y* > 0`
  have hτeq : τ = A / a := by
    by_contra hne
    have hlt : A / a < τ := lt_of_le_of_ne hτge (Ne.symm hne)
    have hexp : exp (-r * τ) < exp (-r * (A / a)) := exp_lt_exp.2 (by nlinarith [h.r_pos])
    have := mul_le_mul_of_nonneg_left hcyc (exp_pos (-r * τ)).le
    have := mul_lt_mul_of_pos_right hexp hYpos
    linarith
  refine ⟨hτeq, ?_⟩
  -- the cycle must be optimal: `G(y/a) = Y*`, so `y/a = τ*`
  rw [hτeq] at heq
  have hcyc_eq : Srev a p r (y / a) - c₀ - c₁ * a * (y / a) +
      exp (-r * (y / a)) * Ystar a p r c₀ c₁ = Ystar a p r c₀ c₁ := by
    have := exp_pos (-r * (A / a))
    have := mul_left_cancel₀ this.ne' (show exp (-r * (A / a)) * (Srev a p r (y / a) - c₀ -
      c₁ * a * (y / a) + exp (-r * (y / a)) * Ystar a p r c₀ c₁) =
        exp (-r * (A / a)) * Ystar a p r c₀ c₁ by linarith)
    exact this
  have hGy : Gcyc a p r c₀ c₁ (y / a) = Ystar a p r c₀ c₁ := by
    have hd : 1 - exp (-r * (y / a)) ≠ 0 := by linarith [exp_neg_lt_one h hσ]
    rw [Gcyc, div_eq_iff hd]
    linarith
  have hm : ∀ τ', ∀ σ, 0 < σ → Gcyc a p r c₀ c₁ τ' = Ystar a p r c₀ c₁ →
      Gcyc a p r c₀ c₁ σ ≤ Gcyc a p r c₀ c₁ τ' := fun τ' σ hσ' he => by
    rw [he]; exact Gcyc_le_Ystar h hσ'
  have := Gcyc_argmax_unique h hσ hτs (fun σ hσ' => hm _ σ hσ' hGy) (fun σ hσ' => hm _ σ hσ' hG)
  rw [div_eq_iff ha.ne'] at this
  linarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A seller with unknown demand

SLP §5.16, pp. 123–125: the reservation price `R` is uniform on `[A, B) ⊆ [0, 1)`. A price
`P ∈ [A, B]` sells with probability `q = (B − P)/(B − A)`, after which `R ∈ [P, B)`; otherwise
`R ∈ [A, P)`. On `D = {(A, B) : 0 ≤ A ≤ B ≤ 1}`,
`(Tf)(A, B) = sup_P {qP + β[(1 − q)f(A, P) + qf(P, B)]}`.

The book's formula divides by `B − A`, which vanishes on the diagonal of `D`. We parametrize by
the probability of sale `q ∈ [0, 1]`, with `P = (1 − q)B + qA`: this is the book's operator off the
diagonal, and it is continuous on all of `D` (on the diagonal it gives `A + βf(A, A)`).

* **Exercise 5.16a** (`ex_5_16a`): `T : C(D) → C(D)` is a contraction (Blackwell's conditions), and
  its fixed point `v` is homogeneous of degree one (`ex_5_16a_hom`, Corollary 1).
* **Exercise 5.16b**: with `w(a) = v(a, 1)`, `v(A, B) = Bw(A/B)` (`v_eq_w`), `w(1) = 1/(1 − β)`
  (`ex_5_16b_one`); `v` is jointly convex on `D` (`v_convex`), so `w` is weakly convex
  (`ex_5_16b_convex`); and `w` is strictly increasing (`ex_5_16b_strictMono`). For `v`: it is
  increasing in both bounds, convex, and at least `A/(1 − β)` (`v_ge`), the value of charging `A`
  forever.
* **Exercise 5.16c** (`ex_5_16c`): with `â = 1/(2 − β)`, setting `P = A` is optimal and
  `w(a) = a/(1 − β)` exactly when `a ≥ â`: on the region `A(2 − β) ≥ B` the bound `v ≤ A/(1 − β)` is
  preserved by `T` (both children stay in the region), while for `a < â` some `P > A` does
  strictly better.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- `D = {(A, B) : 0 ≤ A ≤ B ≤ 1}`. -/
def Dtri : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ 1}

abbrev DPt := ↥Dtri

/-- Probabilities of sale `q ∈ [0, 1]`. -/
abbrev Prob := ↥(Icc (0 : ℝ) 1)

theorem convex_Dtri : Convex ℝ Dtri := by
  intro x hx y hy a b ha hb hab
  simp only [Dtri, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2.1, hy.2.1], by nlinarith [hx.2.2, hy.2.2]⟩

/-- The price `P = (1 − q)B + qA`. -/
def priceQ (x : DPt) (q : Prob) : ℝ := (1 - q.1) * x.1.2 + q.1 * x.1.1

theorem priceQ_mem (x : DPt) (q : Prob) : x.1.1 ≤ priceQ x q ∧ priceQ x q ≤ x.1.2 := by
  have h1 := x.2.2.1
  have hq := q.2
  simp only [priceQ]
  constructor <;> nlinarith [hq.1, hq.2]

/-- The state after no sale: `(A, P)`. -/
def leftPt (x : DPt) (q : Prob) : DPt :=
  ⟨(x.1.1, priceQ x q), x.2.1, (priceQ_mem x q).1, (priceQ_mem x q).2.trans x.2.2.2⟩

/-- The state after a sale: `(P, B)`. -/
def rightPt (x : DPt) (q : Prob) : DPt :=
  ⟨(priceQ x q, x.1.2), x.2.1.trans (priceQ_mem x q).1, (priceQ_mem x q).2, x.2.2.2⟩

variable {β : ℝ}

/-- The objective `qP + β[(1 − q)f(A, P) + qf(P, B)]`. -/
def sellerObj (β : ℝ) (f : DPt → ℝ) (z : DPt × Prob) : ℝ :=
  z.2.1 * priceQ z.1 z.2 + β * ((1 - z.2.1) * f (leftPt z.1 z.2) + z.2.1 * f (rightPt z.1 z.2))

theorem sellerObj_apply (f : DPt → ℝ) (x : DPt) (q : Prob) :
    sellerObj β f (x, q) =
      q.1 * priceQ x q + β * ((1 - q.1) * f (leftPt x q) + q.1 * f (rightPt x q)) := rfl

theorem continuous_priceQ : Continuous fun z : DPt × Prob => priceQ z.1 z.2 := by
  unfold priceQ; fun_prop

theorem continuous_sellerObj {f : DPt → ℝ} (hf : Continuous f) :
    Continuous (sellerObj β f) := by
  have hl : Continuous fun z : DPt × Prob => leftPt z.1 z.2 :=
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_priceQ).subtype_mk _
  have hr : Continuous fun z : DPt × Prob => rightPt z.1 z.2 :=
    (continuous_priceQ.prodMk (continuous_snd.comp (continuous_subtype_val.comp
      continuous_fst))).subtype_mk _
  unfold sellerObj
  have hq : Continuous fun z : DPt × Prob => z.2.1 := continuous_subtype_val.comp continuous_snd
  exact (hq.mul continuous_priceQ).add (continuous_const.mul
    (((continuous_const.sub hq).mul (hf.comp hl)).add (hq.mul (hf.comp hr))))

theorem prob_lhc (x : DPt) : IsLHC (fun _ : DPt => (univ : Set Prob)) x :=
  ⟨univ_nonempty, fun y _ _ _ => ⟨0, fun _ => y, fun _ _ => mem_univ _, tendsto_const_nhds⟩⟩

theorem prob_uhc (x : DPt) : IsUHC (fun _ : DPt => (univ : Set Prob)) x := by
  refine ⟨univ_nonempty, fun xs _ ys _ => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  exact ⟨y, mem_univ _, φ, hφ, hlim⟩

theorem abs_sellerObj_le (hβ : 0 ≤ β) (f : DPt →ᵇ ℝ) (z : DPt × Prob) :
    |sellerObj β f z| ≤ 1 + β * ‖f‖ := by
  have hq := z.2.2
  have hP := priceQ_mem z.1 z.2
  have hA := z.1.2.1
  have hB := z.1.2.2.2
  have h1 : |f (leftPt z.1 z.2)| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _
  have h2 : |f (rightPt z.1 z.2)| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _
  have h3 : |(1 - z.2.1) * f (leftPt z.1 z.2) + z.2.1 * f (rightPt z.1 z.2)| ≤ ‖f‖ := by
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [hq.1, hq.2]
  have h4 : |z.2.1 * priceQ z.1 z.2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [hq.1, hq.2]
  unfold sellerObj
  calc _ ≤ |z.2.1 * priceQ z.1 z.2| + |β * ((1 - z.2.1) * f (leftPt z.1 z.2) +
        z.2.1 * f (rightPt z.1 z.2))| := abs_add_le _ _
    _ ≤ 1 + β * ‖f‖ := by
        rw [abs_mul β, abs_of_nonneg hβ]
        exact add_le_add h4 (mul_le_mul_of_nonneg_left h3 hβ)

/-- The operator `T` on `C(D)`. -/
noncomputable def sellerT (hβ : 0 ≤ β) (f : DPt →ᵇ ℝ) : DPt →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => maxValue (sellerObj β f) (fun _ => univ) x)
    (theorem_3_6 (continuous_sellerObj f.continuous).continuousOn (fun _ => isCompact_univ)
      prob_lhc prob_uhc).1 (1 + β * ‖f‖) fun x => by
        obtain ⟨q, -, hval, -⟩ := exists_argmax (Γ := fun _ : DPt => (univ : Set Prob))
          (continuous_sellerObj (β := β) f.continuous).continuousOn isCompact_univ (x := x)
          univ_nonempty
        rw [← hval, Real.norm_eq_abs]
        exact abs_sellerObj_le hβ f _

theorem exists_sellerT_argmax (hβ : 0 ≤ β) (f : DPt →ᵇ ℝ) (x : DPt) :
    ∃ q : Prob, sellerT hβ f x = sellerObj β f (x, q) ∧
      ∀ q' : Prob, sellerObj β f (x, q') ≤ sellerT hβ f x := by
  obtain ⟨q, -, hval, hmax⟩ := exists_argmax (Γ := fun _ : DPt => (univ : Set Prob))
    (continuous_sellerObj (β := β) f.continuous).continuousOn isCompact_univ (x := x)
    univ_nonempty
  exact ⟨q, hval.symm, fun q' => (hmax q' (mem_univ _)).trans_eq hval⟩

/-- **Exercise 5.16a.** `T` is a contraction of modulus `β`: Blackwell's conditions hold, since the
weights `1 − q` and `q` sum to one. -/
theorem sellerT_contraction (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsContraction (sellerT hβ0.le) β := by
  refine ⟨hβ0, hβ1, blackwell hβ0.le (fun f g hfg x => ?_) (fun f a ha x => ?_)⟩
  · obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨-, -, hmax⟩ := exists_sellerT_argmax hβ0.le g x
    change sellerT hβ0.le f x ≤ sellerT hβ0.le g x
    rw [hq]
    refine le_trans ?_ (hmax q)
    rw [sellerObj_apply, sellerObj_apply]
    have e1 : f (leftPt x q) ≤ g (leftPt x q) := hfg _
    have e2 : f (rightPt x q) ≤ g (rightPt x q) := hfg _
    have h1 := mul_le_mul_of_nonneg_left e1
      (mul_nonneg hβ0.le (by linarith [q.2.2] : (0 : ℝ) ≤ 1 - q.1))
    have h2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ0.le q.2.1)
    linarith
  · obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le (f + const DPt a) x
    obtain ⟨-, -, hmax⟩ := exists_sellerT_argmax hβ0.le f x
    change sellerT hβ0.le (f + const DPt a) x ≤ (sellerT hβ0.le f + const DPt (β * a)) x
    rw [hq, BoundedContinuousFunction.add_apply, const_apply]
    have := hmax q
    unfold sellerObj at this ⊢
    simp only [BoundedContinuousFunction.add_apply, const_apply]
    nlinarith

/-- **Exercise 5.16a.** `T` has a unique fixed point `v ∈ C(D)`. -/
theorem ex_5_16a (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ v : DPt →ᵇ ℝ, sellerT hβ0.le v = v ∧ ∀ w, sellerT hβ0.le w = w → w = v := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (sellerT_contraction hβ0 hβ1)
  exact ⟨v, hv, huniq⟩

/-- `λx = (λA, λB)` for `λ ∈ [0, 1]`. -/
def scalePt (lam : ℝ) (hl : lam ∈ Icc (0 : ℝ) 1) (x : DPt) : DPt :=
  ⟨(lam * x.1.1, lam * x.1.2), mul_nonneg hl.1 x.2.1, mul_le_mul_of_nonneg_left x.2.2.1 hl.1,
    by nlinarith [x.2.2.2, hl.2, x.2.1, x.2.2.1]⟩

/-- **Exercise 5.16a.** The fixed point is homogeneous of degree one: `v(λA, λB) = λv(A, B)`
(Corollary 1: `T` preserves the closed set of homogeneous functions). -/
theorem ex_5_16a_hom (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v)
    (lam : ℝ) (hl : lam ∈ Icc (0 : ℝ) 1) (x : DPt) : v (scalePt lam hl x) = lam * v x := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  set H : Set (DPt →ᵇ ℝ) :=
    {f | ∀ lam (hl : lam ∈ Icc (0 : ℝ) 1) x, f (scalePt lam hl x) = lam * f x}
  have hclosed : IsClosed H := by
    have : H = ⋂ lam, ⋂ (hl : lam ∈ Icc (0 : ℝ) 1), ⋂ x,
        {f : DPt →ᵇ ℝ | f (scalePt lam hl x) = lam * f x} := by ext f; simp [H]
    rw [this]
    exact isClosed_iInter fun lam => isClosed_iInter fun hl => isClosed_iInter fun x =>
      isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const x))
  have hscale : ∀ lam (hl : lam ∈ Icc (0 : ℝ) 1) x q,
      leftPt (scalePt lam hl x) q = scalePt lam hl (leftPt x q) ∧
      rightPt (scalePt lam hl x) q = scalePt lam hl (rightPt x q) ∧
      priceQ (scalePt lam hl x) q = lam * priceQ x q := fun lam hl x q => by
    refine ⟨Subtype.ext (Prod.ext ?_ ?_), Subtype.ext (Prod.ext ?_ ?_), ?_⟩ <;>
      simp only [leftPt, rightPt, scalePt, priceQ] <;> ring
  have hmaps : MapsTo (sellerT hβ0.le) H H := fun f hf lam hl x => by
    obtain ⟨q, hq, hmax⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨q', hq', hmax'⟩ := exists_sellerT_argmax hβ0.le f (scalePt lam hl x)
    have hobj : ∀ q, sellerObj β f (scalePt lam hl x, q) = lam * sellerObj β f (x, q) := fun q => by
      obtain ⟨h1, h2, h3⟩ := hscale lam hl x q
      simp only [sellerObj, h1, h2, h3, hf lam hl]
      ring
    refine le_antisymm ?_ ?_
    · rw [hq', hobj]
      exact mul_le_mul_of_nonneg_left (hmax q') hl.1
    · rw [hq, ← hobj]
      exact hmax' q
  exact (corollary_1 (S' := H) (S'' := H) (sellerT_contraction hβ0 hβ1) hv
    ⟨0, fun _ _ _ => by simp⟩ hclosed hmaps hmaps).1 lam hl x

/-! ### Exercise 5.16b -/

/-- The points `(a, 1)` and `(A, A)`. -/
def topPt (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : DPt := ⟨(a, 1), ha.1, ha.2, le_rfl⟩
def diagPt (A : ℝ) (hA : A ∈ Icc (0 : ℝ) 1) : DPt := ⟨(A, A), hA.1, le_rfl, hA.2⟩

/-- `w(a) = v(a, 1)`. -/
noncomputable def wSel (v : DPt → ℝ) (a : ℝ) : ℝ := by
  classical exact if ha : a ∈ Icc (0 : ℝ) 1 then v (topPt a ha) else 0

theorem fe_seller (hβ0 : 0 < β) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) (x : DPt) :
    (∃ q : Prob, v x = sellerObj β v (x, q)) ∧ ∀ q : Prob, sellerObj β v (x, q) ≤ v x := by
  obtain ⟨q, hq, hmax⟩ := exists_sellerT_argmax hβ0.le v x
  rw [hv] at hq hmax
  exact ⟨⟨q, hq⟩, hmax⟩

/-- Charging `A` (`q = 1`) is always available: `v(A, B) ≥ A + βv(A, B)`, so `v ≥ A/(1 − β)`. -/
theorem v_ge (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) (x : DPt) :
    x.1.1 / (1 - β) ≤ v x := by
  have := (fe_seller hβ0 hv x).2 ⟨1, by norm_num, le_rfl⟩
  have hr : rightPt x ⟨1, by norm_num, le_rfl⟩ = x := Subtype.ext (by simp [rightPt, priceQ])
  simp only [sellerObj, priceQ, hr, sub_self, zero_mul, one_mul, zero_add] at this
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Exercise 5.16b.** On the diagonal, `v(A, A) = A/(1 − β)`; in particular `w(1) = 1/(1 − β)`. -/
theorem ex_5_16b_one (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v)
    (A : ℝ) (hA : A ∈ Icc (0 : ℝ) 1) : v (diagPt A hA) = A / (1 - β) := by
  have hge := v_ge hβ0 hβ1 hv (diagPt A hA)
  refine le_antisymm ?_ hge
  obtain ⟨⟨q, hq⟩, -⟩ := fe_seller hβ0 hv (diagPt A hA)
  have hl : leftPt (diagPt A hA) q = diagPt A hA := Subtype.ext (by
    simp only [leftPt, diagPt, priceQ, Prod.mk.injEq, true_and]; ring)
  have hr : rightPt (diagPt A hA) q = diagPt A hA := Subtype.ext (by
    simp only [rightPt, diagPt, priceQ, Prod.mk.injEq, and_true]; ring)
  have hP : priceQ (diagPt A hA) q = A := by simp only [priceQ, diagPt]; ring
  rw [sellerObj, hl, hr, hP] at hq
  have := q.2
  rw [le_div_iff₀ (by linarith)]
  nlinarith [this.2, hA.1]

/-- With `B > 0`, `v(A, B) = Bw(A/B)`: the value depends on the ratio `a = A/B`. -/
theorem v_eq_w (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v)
    (x : DPt) (hB : 0 < x.1.2) : v x = x.1.2 * wSel v (x.1.1 / x.1.2) := by
  have ha : x.1.1 / x.1.2 ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg x.2.1 hB.le, (div_le_one hB).2 x.2.2.1⟩
  have hl : x.1.2 ∈ Icc (0 : ℝ) 1 := ⟨hB.le, x.2.2.2⟩
  have hx : scalePt x.1.2 hl (topPt _ ha) = x := Subtype.ext (by
    simp only [scalePt, topPt, mul_one]
    field_simp)
  simp only [wSel, ha, ↓reduceDIte]
  rw [← ex_5_16a_hom hβ0 hβ1 hv x.1.2 hl, hx]

/-- `f` is convex on `D`. -/
def IsConvexD (f : DPt → ℝ) : Prop :=
  ∀ x y : DPt, ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    f (cmb convex_Dtri h0 h1 x y) ≤ θ * f x + (1 - θ) * f y

/-- **Exercise 5.16b.** `v` is jointly convex on `D` (`T` preserves convexity: each objective is a
convex function of `(A, B)`, since `(A, P)` and `(P, B)` are linear in `(A, B)`). -/
theorem v_convex (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    IsConvexD v := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  set S : Set (DPt →ᵇ ℝ) := {f | IsConvexD f}
  have hclosed : IsClosed S := by
    have : S = ⋂ x, ⋂ y, ⋂ θ : ℝ, ⋂ (h0 : 0 ≤ θ), ⋂ (h1 : θ ≤ 1),
        {f : DPt →ᵇ ℝ | f (cmb convex_Dtri h0 h1 x y) ≤ θ * f x + (1 - θ) * f y} := by
      ext f; simp [S, IsConvexD]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun θ =>
      isClosed_iInter fun h0 => isClosed_iInter fun h1 => isClosed_le (continuous_eval_const _) ?_
    exact (continuous_const.mul (continuous_eval_const x)).add
      (continuous_const.mul (continuous_eval_const y))
  have hmix : ∀ (x y : DPt) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : Prob),
      leftPt (cmb convex_Dtri h0 h1 x y) q = cmb convex_Dtri h0 h1 (leftPt x q) (leftPt y q) ∧
      rightPt (cmb convex_Dtri h0 h1 x y) q = cmb convex_Dtri h0 h1 (rightPt x q) (rightPt y q) ∧
      priceQ (cmb convex_Dtri h0 h1 x y) q = θ * priceQ x q + (1 - θ) * priceQ y q :=
    fun x y θ h0 h1 q => by
      refine ⟨Subtype.ext (Prod.ext ?_ ?_), Subtype.ext (Prod.ext ?_ ?_), ?_⟩ <;>
        simp only [leftPt, rightPt, cmb, priceQ, smul_eq_mul, Prod.smul_fst, Prod.smul_snd,
          Prod.fst_add, Prod.snd_add] <;> ring
  have hmaps : MapsTo (sellerT hβ0.le) S S := fun f hf x y θ h0 h1 => by
    obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f (cmb convex_Dtri h0 h1 x y)
    obtain ⟨-, -, hx⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨-, -, hy⟩ := exists_sellerT_argmax hβ0.le f y
    rw [hq]
    obtain ⟨h1', h2', h3'⟩ := hmix x y θ h0 h1 q
    have e1 := hx q
    have e2 := hy q
    have c1 := hf (leftPt x q) (leftPt y q) θ h0 h1
    have c2 := hf (rightPt x q) (rightPt y q) θ h0 h1
    unfold sellerObj at e1 e2 ⊢
    rw [h1', h2', h3']
    have hq0 := q.2.1
    have hq1 := q.2.2
    have hb := hβ0.le
    have d1 := mul_le_mul_of_nonneg_left c1 (mul_nonneg hb (by linarith : (0 : ℝ) ≤ 1 - q.1))
    have d2 := mul_le_mul_of_nonneg_left c2 (mul_nonneg hb hq0)
    have m1 := mul_le_mul_of_nonneg_left e1 h0
    have m2 := mul_le_mul_of_nonneg_left e2 (by linarith : (0 : ℝ) ≤ 1 - θ)
    nlinarith
  exact (corollary_1 (S' := S) (S'' := S) (sellerT_contraction hβ0 hβ1) hv
    ⟨0, fun _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1

/-- **Exercise 5.16b.** `w` is weakly convex on `[0, 1]`. -/
theorem ex_5_16b_convex (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (wSel v) := by
  refine ⟨convex_Icc 0 1, fun a ha b hb s t hs ht hst => ?_⟩
  have hab : s • a + t • b ∈ Icc (0 : ℝ) 1 := convex_Icc 0 1 ha hb hs ht hst
  have ht' : t = 1 - s := by linarith
  subst ht'
  simp only [wSel, hab, ha, hb, ↓reduceDIte]
  have hc : cmb convex_Dtri hs (by linarith) (topPt a ha) (topPt b hb) = topPt _ hab :=
    Subtype.ext (by simp only [cmb, topPt, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; ring_nf)
  have := v_convex hβ0 hβ1 hv (topPt a ha) (topPt b hb) s hs (by linarith)
  rw [hc] at this
  simpa [smul_eq_mul] using this

/-- `v` is nondecreasing in the lower bound `A` (and in `B`), on `D`. -/
theorem v_mono (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    ∀ x y : DPt, x.1.1 ≤ y.1.1 → x.1.2 ≤ y.1.2 → v x ≤ v y := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  set S : Set (DPt →ᵇ ℝ) := {f | ∀ x y : DPt, x.1.1 ≤ y.1.1 → x.1.2 ≤ y.1.2 → f x ≤ f y}
  have hclosed : IsClosed S := by
    have : S = ⋂ x, ⋂ y, ⋂ (_ : x.1.1 ≤ y.1.1), ⋂ (_ : x.1.2 ≤ y.1.2),
        {f : DPt →ᵇ ℝ | f x ≤ f y} := by ext f; simp [S]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_le (continuous_eval_const x) (continuous_eval_const y)
  have hmaps : MapsTo (sellerT hβ0.le) S S := fun f hf x y h1 h2 => by
    obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨-, -, hmax⟩ := exists_sellerT_argmax hβ0.le f y
    rw [hq]
    refine le_trans ?_ (hmax q)
    have hP : priceQ x q ≤ priceQ y q := by
      simp only [priceQ]; have := q.2; nlinarith [this.1, this.2]
    have e1 : f (leftPt x q) ≤ f (leftPt y q) := hf (leftPt x q) (leftPt y q) h1 hP
    have e2 : f (rightPt x q) ≤ f (rightPt y q) := hf (rightPt x q) (rightPt y q) hP h2
    rw [sellerObj_apply, sellerObj_apply]
    have m1 := mul_le_mul_of_nonneg_left e1
      (mul_nonneg hβ0.le (by linarith [q.2.2] : (0 : ℝ) ≤ 1 - q.1))
    have m2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ0.le q.2.1)
    have m3 := mul_le_mul_of_nonneg_left hP q.2.1
    linarith
  exact (corollary_1 (S' := S) (S'' := S) (sellerT_contraction hβ0 hβ1) hv
    ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed hmaps hmaps).1

/-- **Exercise 5.16b.** `w` is strictly increasing. -/
theorem ex_5_16b_strictMono (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ}
    (hv : sellerT hβ0.le v = v) : StrictMonoOn (wSel v) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  simp only [wSel, ha, hb, ↓reduceDIte]
  obtain ⟨⟨q, hq⟩, -⟩ := fe_seller hβ0 hv (topPt a ha)
  have hmax := (fe_seller hβ0 hv (topPt b hb)).2 q
  have hP : priceQ (topPt a ha) q ≤ priceQ (topPt b hb) q := by
    simp only [priceQ, topPt]; have := q.2; nlinarith [this.1, this.2]
  have e1 := v_mono hβ0 hβ1 hv (leftPt (topPt a ha) q) (leftPt (topPt b hb) q) hab.le hP
  have e2 := v_mono hβ0 hβ1 hv (rightPt (topPt a ha) q) (rightPt (topPt b hb) q) hP le_rfl
  have hq0 := q.2.1
  rcases eq_or_lt_of_le hq0 with hq00 | hqpos
  · -- `q = 0`: `v(a, 1) = βv(a, 1)`, so `v(a, 1) = 0 < b/(1 − β) ≤ v(b, 1)`
    have hz : v (topPt a ha) = 0 := by
      have hl : leftPt (topPt a ha) q = topPt a ha := Subtype.ext (by
        simp only [leftPt, topPt, priceQ, ← hq00, Prod.mk.injEq, true_and]; ring)
      rw [sellerObj, hl, ← hq00] at hq
      simp only [zero_mul, sub_zero, one_mul, add_zero, zero_add] at hq
      have : (1 - β) * v (topPt a ha) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (by linarith)
    have : b / (1 - β) ≤ v (topPt b hb) := v_ge hβ0 hβ1 hv (topPt b hb)
    have hbpos : 0 < b / (1 - β) := div_pos (lt_of_le_of_lt ha.1 hab) (by linarith)
    linarith
  · -- `q > 0`: the same `q` earns strictly more at `b`
    have hPlt : priceQ (topPt a ha) q < priceQ (topPt b hb) q := by
      simp only [priceQ, topPt]; nlinarith
    rw [hq]
    rw [sellerObj_apply] at hmax ⊢
    have m1 := mul_le_mul_of_nonneg_left e1
      (mul_nonneg hβ0.le (by linarith [q.2.2] : (0 : ℝ) ≤ 1 - q.1))
    have m2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ0.le q.2.1)
    have m3 := mul_lt_mul_of_pos_left hPlt hqpos
    linarith

/-! ### Exercise 5.16c -/

/-- **Exercise 5.16c.** On the region `A(2 − β) ≥ B`, `v(A, B) = A/(1 − β)` and setting `P = A`
(`q = 1`) is optimal; off it (`a < â = 1/(2 − β)`), some price above `A` does strictly better, so
`v(A, B) > A/(1 − β)`. In terms of `w`: `w(a) = a/(1 − β)` exactly for `a ∈ [â, 1]`. -/
theorem ex_5_16c (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    (∀ x : DPt, x.1.2 ≤ x.1.1 * (2 - β) → v x = x.1.1 / (1 - β)) ∧
      (∀ x : DPt, x.1.1 * (2 - β) < x.1.2 → x.1.1 / (1 - β) < v x) := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  have h1β : 0 < 1 - β := by linarith
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · -- the bound `f ≤ A/(1 − β)` on the region is preserved by `T`
    set S : Set (DPt →ᵇ ℝ) := {f | ∀ x : DPt, x.1.2 ≤ x.1.1 * (2 - β) → f x ≤ x.1.1 / (1 - β)}
    have hclosed : IsClosed S := by
      have : S = ⋂ x : DPt, ⋂ (_ : x.1.2 ≤ x.1.1 * (2 - β)),
          {f : DPt →ᵇ ℝ | f x ≤ x.1.1 / (1 - β)} := by ext f; simp [S]
      rw [this]
      exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (continuous_eval_const x) continuous_const
    have hmaps : MapsTo (sellerT hβ0.le) S S := fun f hf x hx => by
      obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f x
      rw [hq]
      have hP := priceQ_mem x q
      have hq0 := q.2.1
      have hq1 := q.2.2
      -- both children stay in the region
      have hl : f (leftPt x q) ≤ x.1.1 / (1 - β) := hf (leftPt x q) (by
        change priceQ x q ≤ x.1.1 * (2 - β)
        linarith [hP.2])
      have hr : f (rightPt x q) ≤ priceQ x q / (1 - β) := hf (rightPt x q) (by
        change x.1.2 ≤ priceQ x q * (2 - β)
        nlinarith [mul_le_mul_of_nonneg_right hP.1 (by linarith : (0 : ℝ) ≤ 2 - β)])
      rw [sellerObj_apply, le_div_iff₀ h1β]
      -- `qP + β(1 − q)A ≤ A` because `q(B − A) ≤ A(1 − β)` on the region
      have key : q.1 * priceQ x q + β * (1 - q.1) * x.1.1 ≤ x.1.1 := by
        have e : q.1 * priceQ x q + β * (1 - q.1) * x.1.1 - x.1.1 =
            (1 - q.1) * (q.1 * (x.1.2 - x.1.1) - x.1.1 * (1 - β)) := by
          simp only [priceQ]; ring
        have : q.1 * (x.1.2 - x.1.1) ≤ x.1.1 * (1 - β) := by
          have hBA : x.1.2 - x.1.1 ≤ x.1.1 * (1 - β) := by linarith
          have := x.2.2.1
          nlinarith
        nlinarith
      have m1 := mul_le_mul_of_nonneg_left hl (mul_nonneg hβ0.le (by linarith : (0 : ℝ) ≤ 1 - q.1))
      have m2 := mul_le_mul_of_nonneg_left hr (mul_nonneg hβ0.le hq0)
      have e1 : β * (1 - q.1) * (x.1.1 / (1 - β)) * (1 - β) = β * (1 - q.1) * x.1.1 := by
        field_simp
      have e2 : β * q.1 * (priceQ x q / (1 - β)) * (1 - β) = β * q.1 * priceQ x q := by
        field_simp
      have m1' := mul_le_mul_of_nonneg_right m1 h1β.le
      have m2' := mul_le_mul_of_nonneg_right m2 h1β.le
      linarith
    have hvS := (corollary_1 (S' := S) (S'' := S) (sellerT_contraction hβ0 hβ1) hv
      ⟨0, fun x _ => div_nonneg x.2.1 h1β.le⟩ hclosed hmaps hmaps).1
    exact le_antisymm (hvS x hx) (v_ge hβ0 hβ1 hv x)
  · -- a price just above `A` beats `A/(1 − β)`
    have hBA : x.1.1 * (1 - β) < x.1.2 - x.1.1 := by linarith
    have hBA0 : 0 < x.1.2 - x.1.1 := by nlinarith [x.2.1]
    -- choose `q < 1` with `q(B − A) > A(1 − β)`
    set q₀ := (1 + x.1.1 * (1 - β) / (x.1.2 - x.1.1)) / 2
    have hfrac : x.1.1 * (1 - β) / (x.1.2 - x.1.1) < 1 := (div_lt_one hBA0).2 hBA
    have hfrac0 : 0 ≤ x.1.1 * (1 - β) / (x.1.2 - x.1.1) :=
      div_nonneg (mul_nonneg x.2.1 h1β.le) hBA0.le
    have hq0 : 0 ≤ q₀ := by simp only [q₀]; linarith
    have hq1 : q₀ < 1 := by simp only [q₀]; linarith
    have hqgap : x.1.1 * (1 - β) < q₀ * (x.1.2 - x.1.1) := by
      have : x.1.1 * (1 - β) / (x.1.2 - x.1.1) < q₀ := by simp only [q₀]; linarith
      rwa [div_lt_iff₀ hBA0] at this
    set q : Prob := ⟨q₀, hq0, hq1.le⟩
    have hle := (fe_seller hβ0 hv x).2 q
    have hl : x.1.1 / (1 - β) ≤ v (leftPt x q) := v_ge hβ0 hβ1 hv (leftPt x q)
    have hr : priceQ x q / (1 - β) ≤ v (rightPt x q) := v_ge hβ0 hβ1 hv (rightPt x q)
    have hqv : (q : ℝ) = q₀ := rfl
    rw [sellerObj_apply, hqv] at hle
    rw [div_lt_iff₀ h1β]
    have e : q₀ * priceQ x q + β * (1 - q₀) * x.1.1 - x.1.1 =
        (1 - q₀) * (q₀ * (x.1.2 - x.1.1) - x.1.1 * (1 - β)) := by
      simp only [priceQ, q]; ring
    have hpos : 0 < (1 - q₀) * (q₀ * (x.1.2 - x.1.1) - x.1.1 * (1 - β)) :=
      mul_pos (by linarith) (by linarith)
    have m1 := mul_le_mul_of_nonneg_left hl (mul_nonneg hβ0.le (by linarith : (0 : ℝ) ≤ 1 - q₀))
    have m2 := mul_le_mul_of_nonneg_left hr (mul_nonneg hβ0.le hq0)
    have e1 : β * (1 - q₀) * (x.1.1 / (1 - β)) * (1 - β) = β * (1 - q₀) * x.1.1 := by field_simp
    have e2 : β * q₀ * (priceQ x q / (1 - β)) * (1 - β) = β * q₀ * priceQ x q := by field_simp
    have m1' := mul_le_mul_of_nonneg_right m1 h1β.le
    have m2' := mul_le_mul_of_nonneg_right m2 h1β.le
    have hle' := mul_le_mul_of_nonneg_right hle h1β.le
    linarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A consumption–savings problem: the optimal plan

SLP §5.17, pp. 126–128. Preferences `Σ βᵗU(c_t)`, income `I > 0` each period, wealth `x_t ≥ 0`
(no borrowing), interest factor `R` with `0 < R < 1/β`:
`c_t + x_{t+1}/R = I + x_t`, so `Γ(x) = [0, (I + x)R]` and `F(x, y) = U(I + x − y/R)`.

`U` is continuous, strictly increasing and strictly concave on `ℝ₊`, with a continuous derivative
`U'` on `(0, ∞)` (the book asks for `C¹` on `ℝ₊`; nothing here uses a derivative at `0`), and
`U'(c) → 0` as `c → ∞`. That last condition is not in the book, which needs some such condition:
see `ConsumptionSavingsCounterexample` for a counterexample.

Rather than building `v` interval by interval as the book does, we write down every optimal plan
at once. For a multiplier `μ > 0`, let `cI(p) = max{I, (U')⁻¹(p)}` (`cI`) and consume
`c_t = cI(μ/(Rβ)ᵗ)`. Consumption falls (`Rβ < 1`) until it reaches `I`, after which wealth is
zero. The wealth that this plan exhausts is `Ξ(μ) = Σ_t R⁻ᵗ(c_t − I)` (`wealth`, a finite sum),
and the plan's wealth path is `x_t = Ξ(μ/(Rβ)ᵗ)` (`planμ`). `Ξ` is continuous and decreasing,
from `+∞` down to `Ξ(U'(I)) = 0`, so every `x₀ ≥ 0` is `Ξ(μ)` for some `μ ∈ (0, U'(I)]`
(`exists_wealth_eq`).

The plan is optimal, and uniquely so, by a summation-by-parts argument (`abel_bound`). With
`p_t = βᵗU'(c_t)` we have `Rp_{t+1} ≤ p_t`, with equality unless `x_{t+1} = 0`. This bounds
`Σ p_t(c'_t − c_t)` for any feasible `c'` by `p₀(x'₀ − x₀)`, and concavity of `U` does the rest
(`value_bound`). This gives at once:

* optimality and uniqueness (`plan_total`, `total_lt`), and `v*(x₀) = V(μ)` (`vstar_eq`);
* the supergradient inequality `v*(z) ≤ v*(x₀) + U'(c₀)(z − x₀)` (`vstar_le_tangent`), which
  `ConsumptionSavingsPolicy` turns into differentiability and strict concavity of `v`.

**Exercise 5.17a** (`ex_5_17a`): `v*` is real-valued and satisfies (FE), and an optimal plan
satisfies `v*(x_t) = U(I + x_t − x_{t+1}/R) + βv*(x_{t+1})`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

/-- The hypotheses of §5.17. -/
structure CSHyp (U U' : ℝ → ℝ) (β R I : ℝ) : Prop where
  hβ0 : 0 < β
  hβ1 : β < 1
  hR : 0 < R
  hRβ : R * β < 1
  hI : 0 < I
  hUc : ContinuousOn U (Ici 0)
  hUd : ∀ c, 0 < c → HasDerivAt U (U' c) c
  hU'c : ContinuousOn U' (Ioi 0)
  hUm : StrictMonoOn U (Ici 0)
  hUcc : StrictConcaveOn ℝ (Ici 0) U
  hlim : Tendsto U' atTop (𝓝 0)

variable {U U' : ℝ → ℝ} {β R I : ℝ}

theorem CSHyp.rho_pos (h : CSHyp U U' β R I) : 0 < R * β := mul_pos h.hR h.hβ0

/-- `U` lies below its tangent lines. -/
theorem CSHyp.super_le (h : CSHyp U U' β R I) {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c') :
    U c' ≤ U c + U' c * (c' - c) := by
  have := concave_le_fderiv h.hUcc.concaveOn (mem_Ici.2 hc.le) (mem_Ici.2 hc')
    (h.hUd c hc).hasFDerivAt
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at this
  linarith

/-- `U` lies strictly below its tangent lines away from the point of tangency. -/
theorem CSHyp.super_lt (h : CSHyp U U' β R I) {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c')
    (hne : c' ≠ c) : U c' < U c + U' c * (c' - c) := by
  have hm := h.super_le hc (c' := (c + c') / 2) (by positivity)
  have hs := h.hUcc.2 (mem_Ici.2 hc.le) (mem_Ici.2 hc') (Ne.symm hne)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hs
  have e : (1 / 2 : ℝ) * c + 1 / 2 * c' = (c + c') / 2 := by ring
  rw [e] at hs
  linarith

theorem CSHyp.U'_pos (h : CSHyp U U' β R I) {c : ℝ} (hc : 0 < c) : 0 < U' c := by
  have h1 := h.super_lt hc (c' := c + 1) (by linarith) (by linarith)
  have h2 := h.hUm (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c < c + 1)
  nlinarith

theorem CSHyp.U'_lt (h : CSHyp U U' β R I) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    U' b < U' a := by
  have h1 := h.super_lt ha (c' := b) (by linarith) hab.ne'
  have h2 := h.super_lt (ha.trans hab) (c' := a) ha.le hab.ne
  nlinarith

theorem CSHyp.U'_le (h : CSHyp U U' β R I) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    U' b ≤ U' a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (h.U'_lt ha hlt).le

/-! ### Consumption at a given marginal utility -/

/-- `cI(p)`: the least `c ≥ I` with `U'(c) ≤ p`, i.e. `max{I, (U')⁻¹(p)}`. -/
noncomputable def cI (U' : ℝ → ℝ) (I p : ℝ) : ℝ := sInf {c | I ≤ c ∧ U' c ≤ p}

theorem CSHyp.cI_nonempty (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) :
    {c | I ≤ c ∧ U' c ≤ p}.Nonempty := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.hlim.eventually (gt_mem_nhds hp))
  exact ⟨max N I, le_max_right _ _, (hN _ (le_max_left _ _)).le⟩

theorem CSHyp.cI_mem (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) :
    I ≤ cI U' I p ∧ U' (cI U' I p) ≤ p := by
  have hcl : IsClosed {c | I ≤ c ∧ U' c ≤ p} :=
    (h.hU'c.mono fun c (hc : c ∈ Ici I) => lt_of_lt_of_le h.hI hc).preimage_isClosed_of_isClosed
      isClosed_Ici isClosed_Iic
  exact hcl.csInf_mem (h.cI_nonempty hp) ⟨I, fun _ hc => hc.1⟩

theorem cI_le {p c : ℝ} (hc : I ≤ c) (hpc : U' c ≤ p) : cI U' I p ≤ c :=
  csInf_le ⟨I, fun _ hc => hc.1⟩ ⟨hc, hpc⟩

theorem CSHyp.cI_pos (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) : 0 < cI U' I p :=
  h.hI.trans_le (h.cI_mem hp).1

theorem CSHyp.cI_of_le (h : CSHyp U U' β R I) {p : ℝ} (hp : U' I ≤ p) : cI U' I p = I :=
  le_antisymm (cI_le le_rfl hp) (h.cI_mem ((h.U'_pos h.hI).trans_le hp)).1

/-- Above `I`, `cI` inverts `U'`. -/
theorem CSHyp.cI_eq (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) (hgt : I < cI U' I p) :
    U' (cI U' I p) = p := by
  set c := cI U' I p
  refine le_antisymm (h.cI_mem hp).2 (not_lt.1 fun hlt => ?_)
  have hcont : ContinuousAt U' c := h.hU'c.continuousAt (Ioi_mem_nhds (h.hI.trans hgt))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hlt))
  set d := max (c - ε / 2) ((I + c) / 2)
  have hd1 : d < c := max_lt (by linarith) (by linarith)
  have hd2 : I ≤ d := le_max_of_le_right (by linarith)
  have hd3 : dist d c < ε := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor
    · linarith
    · linarith [le_max_left (c - ε / 2) ((I + c) / 2)]
  exact absurd (cI_le hd2 (hball hd3).le) (not_le.2 hd1)

theorem CSHyp.cI_U' (h : CSHyp U U' β R I) {c : ℝ} (hc : I ≤ c) : cI U' I (U' c) = c := by
  have hp := h.U'_pos (h.hI.trans_le hc)
  refine le_antisymm (cI_le hc le_rfl) (not_lt.1 fun hlt => ?_)
  exact absurd (h.cI_mem hp).2 (not_le.2 (h.U'_lt (h.cI_pos hp) hlt))

theorem CSHyp.cI_anti (h : CSHyp U U' β R I) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    cI U' I q ≤ cI U' I p :=
  cI_le (h.cI_mem hp).1 ((h.cI_mem hp).2.trans hpq)

theorem CSHyp.cI_gt (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) (hpI : p < U' I) :
    I < cI U' I p := by
  refine lt_of_le_of_ne (h.cI_mem hp).1 fun he => ?_
  have := (h.cI_mem hp).2
  rw [← he] at this
  linarith

theorem CSHyp.cI_strictAnti (h : CSHyp U U' β R I) {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hpI : p < U' I) : cI U' I q < cI U' I p := by
  have hgt := h.cI_gt hp hpI
  have hU := h.cI_eq hp hgt
  rcases eq_or_lt_of_le (h.cI_mem (hp.trans hpq)).1 with he | hlt
  · rw [← he]; exact hgt
  · have hUq := h.cI_eq (hp.trans hpq) hlt
    refine not_le.1 fun hle => ?_
    have := h.U'_le (h.hI.trans hgt) hle
    linarith

/-- `cI(p) ≥ c` once `p < U'(c)`. -/
theorem CSHyp.le_cI (h : CSHyp U U' β R I) {p c : ℝ} (hp : 0 < p)
    (hpc : p < U' c) : c ≤ cI U' I p := by
  refine not_lt.1 fun hlt => ?_
  have := h.U'_le (h.cI_pos hp) hlt.le
  linarith [(h.cI_mem hp).2]

theorem CSHyp.continuousAt_cI (h : CSHyp U U' β R I) {p₀ : ℝ} (hp₀ : 0 < p₀) :
    ContinuousAt (cI U' I) p₀ := by
  have hpos : ∀ᶠ p in 𝓝 p₀, 0 < p := lt_mem_nhds hp₀
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a I with haI | haI
    · filter_upwards [hpos] with p hp
      exact haI.trans_le (h.cI_mem hp).1
    · have hgt : I < cI U' I p₀ := lt_of_le_of_lt haI ha
      have hUa : p₀ < U' a := by
        have := h.U'_lt (h.hI.trans_le haI) ha
        rwa [h.cI_eq hp₀ hgt] at this
      filter_upwards [hpos, gt_mem_nhds hUa] with p hp hpa
      refine not_le.1 fun hle => ?_
      have := h.U'_le (h.cI_pos hp) hle
      linarith [(h.cI_mem hp).2]
  · set b' := (cI U' I p₀ + b) / 2
    have hb'1 : cI U' I p₀ < b' := by simp only [b']; linarith
    have hb'2 : b' < b := by simp only [b']; linarith
    have hUb : U' b' < p₀ := (h.U'_lt (h.cI_pos hp₀) hb'1).trans_le (h.cI_mem hp₀).2
    filter_upwards [lt_mem_nhds hUb] with p hp
    exact (cI_le ((h.cI_mem hp₀).1.trans hb'1.le) hp.le).trans_lt hb'2

/-! ### The wealth a multiplier exhausts -/

/-- `Ξ(μ) = Σ_t R⁻ᵗ(cI(μ/(Rβ)ᵗ) − I)`. -/
noncomputable def wealth (U' : ℝ → ℝ) (β R I μ : ℝ) : ℝ :=
  ∑' t : ℕ, (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I)

/-- From some date on, `μ/(Rβ)ᵗ ≥ U'(I)` (uniformly in `μ ≥ μ₁`). -/
theorem CSHyp.exists_K (h : CSHyp U U' β R I) {μ₁ : ℝ} (hμ₁ : 0 < μ₁) :
    ∃ K : ℕ, ∀ t, K ≤ t → ∀ μ, μ₁ ≤ μ → U' I ≤ μ / (R * β) ^ t := by
  have hU := h.U'_pos h.hI
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hμ₁ hU) h.hRβ
  refine ⟨K, fun t ht μ hμ => ?_⟩
  have hρt : (R * β) ^ t ≤ (R * β) ^ K := pow_le_pow_of_le_one h.rho_pos.le h.hRβ.le ht
  rw [le_div_iff₀ (pow_pos h.rho_pos t)]
  have := (lt_div_iff₀ hU).1 (hρt.trans_lt hK)
  linarith

theorem CSHyp.wealth_term_eq_zero (h : CSHyp U U' β R I) {μ : ℝ} {t : ℕ}
    (ht : U' I ≤ μ / (R * β) ^ t) : (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I) = 0 := by
  rw [h.cI_of_le ht, sub_self, mul_zero]

theorem CSHyp.wealth_eq_sum (h : CSHyp U U' β R I) {μ₁ : ℝ} (hμ₁ : 0 < μ₁) :
    ∃ K : ℕ, ∀ μ, μ₁ ≤ μ → wealth U' β R I μ =
      ∑ t ∈ Finset.range K, (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I) := by
  obtain ⟨K, hK⟩ := h.exists_K hμ₁
  exact ⟨K, fun μ hμ => tsum_eq_sum fun t ht =>
    h.wealth_term_eq_zero (hK t (by simpa using ht) μ hμ)⟩

theorem CSHyp.summable_wealth (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    Summable fun t : ℕ => (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I) := by
  obtain ⟨K, hK⟩ := h.exists_K hμ
  exact summable_of_ne_finset_zero (s := Finset.range K) fun t ht =>
    h.wealth_term_eq_zero (hK t (by simpa using ht) μ le_rfl)

theorem CSHyp.wealth_nonneg (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    0 ≤ wealth U' β R I μ :=
  tsum_nonneg fun t => mul_nonneg (inv_nonneg.2 (pow_pos h.hR t).le)
    (sub_nonneg.2 (h.cI_mem (div_pos hμ (pow_pos h.rho_pos t))).1)

/-- `Ξ(μ) = (cI(μ) − I) + R⁻¹Ξ(μ/(Rβ))`. -/
theorem CSHyp.wealth_shift (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    wealth U' β R I μ = (cI U' I μ - I) + R⁻¹ * wealth U' β R I (μ / (R * β)) := by
  rw [wealth, (h.summable_wealth hμ).tsum_eq_zero_add, wealth, ← tsum_mul_left]
  congr 1
  · simp
  · refine tsum_congr fun t => ?_
    rw [show μ / (R * β) ^ (t + 1) = μ / (R * β) / (R * β) ^ t by
      rw [pow_succ', div_mul_eq_div_div], pow_succ', mul_inv]
    ring

theorem CSHyp.wealth_of_ge (h : CSHyp U U' β R I) {μ : ℝ} (hμ : U' I ≤ μ) :
    wealth U' β R I μ = 0 := by
  refine (tsum_congr fun t => h.wealth_term_eq_zero ?_).trans tsum_zero
  exact hμ.trans (le_div_self ((h.U'_pos h.hI).le.trans hμ) (pow_pos h.rho_pos t)
    (pow_le_one₀ h.rho_pos.le h.hRβ.le))

theorem CSHyp.wealth_ge (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    cI U' I μ - I ≤ wealth U' β R I μ := by
  rw [h.wealth_shift hμ]
  exact le_add_of_nonneg_right
    (mul_nonneg (inv_nonneg.2 h.hR.le) (h.wealth_nonneg (div_pos hμ h.rho_pos)))

theorem CSHyp.wealth_anti (h : CSHyp U U' β R I) {μ μ' : ℝ} (hμ : 0 < μ) (hμμ' : μ ≤ μ') :
    wealth U' β R I μ' ≤ wealth U' β R I μ := by
  refine Summable.tsum_le_tsum (fun t => ?_) (h.summable_wealth (hμ.trans_le hμμ'))
    (h.summable_wealth hμ)
  have hρt := pow_pos h.rho_pos t
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (h.cI_anti (div_pos hμ hρt)
    (div_le_div_of_nonneg_right hμμ' hρt.le)) I) (inv_nonneg.2 (pow_pos h.hR t).le)

theorem CSHyp.wealth_strictAnti (h : CSHyp U U' β R I) {μ μ' : ℝ} (hμ : 0 < μ) (hμμ' : μ < μ')
    (hμI : μ < U' I) : wealth U' β R I μ' < wealth U' β R I μ := by
  rw [h.wealth_shift hμ, h.wealth_shift (hμ.trans hμμ')]
  have h1 := h.cI_strictAnti hμ hμμ' hμI
  have h2 := mul_le_mul_of_nonneg_left (h.wealth_anti (div_pos hμ h.rho_pos)
    (div_le_div_of_nonneg_right hμμ'.le h.rho_pos.le)) (inv_nonneg.2 h.hR.le)
  linarith

theorem CSHyp.wealth_pos (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (hμI : μ < U' I) :
    0 < wealth U' β R I μ := by
  rw [← h.wealth_of_ge (le_refl (U' I))]
  exact h.wealth_strictAnti hμ hμI hμI

/-- `Ξ(μ) > 0` only below `U'(I)`. -/
theorem CSHyp.lt_of_wealth_pos (h : CSHyp U U' β R I) {μ : ℝ} (hw : 0 < wealth U' β R I μ) :
    μ < U' I :=
  not_le.1 fun hle => by rw [h.wealth_of_ge hle] at hw; exact lt_irrefl _ hw

theorem CSHyp.continuousAt_wealth (h : CSHyp U U' β R I) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    ContinuousAt (wealth U' β R I) μ₀ := by
  obtain ⟨K, hK⟩ := h.wealth_eq_sum (half_pos hμ₀)
  have hev : (fun μ => ∑ t ∈ Finset.range K, (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I))
      =ᶠ[𝓝 μ₀] wealth U' β R I := by
    filter_upwards [lt_mem_nhds (half_lt_self hμ₀)] with μ hμ
    exact (hK μ hμ.le).symm
  refine ContinuousAt.congr ?_ hev
  refine tendsto_finsetSum _ fun t _ => ?_
  have hc : ContinuousAt (fun μ => cI U' I (μ / (R * β) ^ t)) μ₀ :=
    (h.continuousAt_cI (div_pos hμ₀ (pow_pos h.rho_pos t))).comp
      (f := fun μ => μ / (R * β) ^ t) (continuous_id.div_const _).continuousAt
  exact continuousAt_const.mul (hc.sub continuousAt_const)

/-- Every `x₀ ≥ 0` is `Ξ(μ)` for some `μ ∈ (0, U'(I)]`. -/
theorem CSHyp.exists_wealth_eq (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    ∃ μ, 0 < μ ∧ μ ≤ U' I ∧ wealth U' β R I μ = x := by
  have hμ₁ : 0 < U' (I + x) := h.U'_pos (by linarith [h.hI])
  have hμ₁I : U' (I + x) ≤ U' I := h.U'_le h.hI (by linarith)
  have hcont : ContinuousOn (wealth U' β R I) (Icc (U' (I + x)) (U' I)) := fun μ hμ =>
    (h.continuousAt_wealth (hμ₁.trans_le hμ.1)).continuousWithinAt
  have hx1 : x ≤ wealth U' β R I (U' (I + x)) := by
    have := h.wealth_ge hμ₁
    rwa [h.cI_U' (by linarith : I ≤ I + x), add_sub_cancel_left] at this
  obtain ⟨μ, hμ, hμx⟩ := intermediate_value_Icc' hμ₁I hcont
    ⟨by rw [h.wealth_of_ge le_rfl]; exact hx, hx1⟩
  exact ⟨μ, hμ₁.trans_le hμ.1, hμ.2, hμx⟩

/-! ### The plan of a multiplier -/

/-- Wealth along the plan of `μ`: `x_t = Ξ(μ/(Rβ)ᵗ)`. -/
noncomputable def planμ (U' : ℝ → ℝ) (β R I μ : ℝ) (t : ℕ) : ℝ :=
  wealth U' β R I (μ / (R * β) ^ t)

/-- Consumption along the plan of `μ`: `c_t = cI(μ/(Rβ)ᵗ)`. -/
noncomputable def consμ (U' : ℝ → ℝ) (β R I μ : ℝ) (t : ℕ) : ℝ := cI U' I (μ / (R * β) ^ t)

theorem planμ_zero (μ : ℝ) : planμ U' β R I μ 0 = wealth U' β R I μ := by simp [planμ]

theorem consμ_zero (μ : ℝ) : consμ U' β R I μ 0 = cI U' I μ := by simp [consμ]

theorem div_pow_succ (μ ρ : ℝ) (t : ℕ) : μ / ρ ^ (t + 1) = μ / ρ ^ t / ρ := by
  rw [pow_succ, div_div]

/-- The budget constraint: `x_{t+1} = R(I + x_t − c_t)`. -/
theorem CSHyp.planμ_succ (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    planμ U' β R I μ (t + 1) = R * (I + planμ U' β R I μ t - consμ U' β R I μ t) := by
  have e := h.wealth_shift (div_pos hμ (pow_pos h.rho_pos t))
  rw [← div_pow_succ] at e
  simp only [planμ, consμ]
  set W := wealth U' β R I (μ / (R * β) ^ (t + 1))
  have hRR : R * R⁻¹ = 1 := mul_inv_cancel₀ h.hR.ne'
  rw [e]
  linear_combination (-W) * hRR

theorem CSHyp.consμ_eq (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    consμ U' β R I μ t = I + planμ U' β R I μ t - planμ U' β R I μ (t + 1) / R := by
  rw [h.planμ_succ hμ, mul_div_cancel_left₀ _ h.hR.ne']
  ring

theorem CSHyp.planμ_nonneg (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    0 ≤ planμ U' β R I μ t :=
  h.wealth_nonneg (div_pos hμ (pow_pos h.rho_pos t))

theorem CSHyp.consμ_ge (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    I ≤ consμ U' β R I μ t :=
  (h.cI_mem (div_pos hμ (pow_pos h.rho_pos t))).1

/-- The tail of a plan is a plan: `x_{t+s}` is the plan of `μ/(Rβ)ᵗ`. -/
theorem planμ_tail (μ : ℝ) (t s : ℕ) :
    planμ U' β R I (μ / (R * β) ^ t) s = planμ U' β R I μ (s + t) := by
  simp only [planμ, div_div, ← pow_add, add_comm t s]

theorem consμ_tail (μ : ℝ) (t s : ℕ) :
    consμ U' β R I (μ / (R * β) ^ t) s = consμ U' β R I μ (s + t) := by
  simp only [consμ, div_div, ← pow_add, add_comm t s]

/-- From some date on, the plan consumes `I` and holds no wealth. -/
theorem CSHyp.exists_plan_zero (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    ∃ K : ℕ, ∀ t, K ≤ t → planμ U' β R I μ t = 0 ∧ consμ U' β R I μ t = I := by
  obtain ⟨K, hK⟩ := h.exists_K hμ
  exact ⟨K, fun t ht => ⟨h.wealth_of_ge (hK t ht μ le_rfl), h.cI_of_le (hK t ht μ le_rfl)⟩⟩

/-- The Euler conditions along a plan: `RβU'(c_{t+1}) ≤ U'(c_t)`, with equality unless
`x_{t+1} = 0`. -/
theorem CSHyp.euler_step (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    R * β * U' (consμ U' β R I μ (t + 1)) ≤ U' (consμ U' β R I μ t) ∧
      (U' (consμ U' β R I μ t) - R * β * U' (consμ U' β R I μ (t + 1))) *
        planμ U' β R I μ (t + 1) = 0 := by
  have hρ := h.rho_pos
  set m := μ / (R * β) ^ t
  have hm : 0 < m := div_pos hμ (pow_pos hρ t)
  have hm' : m / (R * β) = μ / (R * β) ^ (t + 1) := (div_pow_succ μ (R * β) t).symm
  have hρm : R * β * (m / (R * β)) = m := mul_div_cancel₀ m hρ.ne'
  have hmm' : m ≤ m / (R * β) := le_div_self hm.le hρ h.hRβ.le
  simp only [consμ, planμ]
  rw [← hm']
  rcases eq_or_lt_of_le (h.cI_mem (hm.trans_le hmm')).1 with he | hgt
  · -- `c_{t+1} = I`: then `x_{t+1} = 0`
    have hUI : U' I ≤ m / (R * β) := by have := (h.cI_mem (hm.trans_le hmm')).2; rwa [← he] at this
    rw [h.wealth_of_ge hUI, mul_zero, ← he]
    refine ⟨?_, rfl⟩
    rcases eq_or_lt_of_le (h.cI_mem hm).1 with he' | hgt'
    · rw [← he']
      have := h.U'_pos h.hI
      nlinarith [h.hRβ]
    · rw [h.cI_eq hm hgt']
      have := mul_le_mul_of_nonneg_left hUI hρ.le
      rwa [hρm] at this
  · -- `c_{t+1} > I`: then `c_t > I` too and the Euler equation holds with equality
    have hgt' : I < cI U' I m := hgt.trans_le (h.cI_anti hm hmm')
    rw [h.cI_eq (hm.trans_le hmm') hgt, h.cI_eq hm hgt', hρm, sub_self, zero_mul]
    exact ⟨le_rfl, rfl⟩

/-! ### Summation by parts -/

/-- **Summation by parts.** If `Rp_{t+1} ≤ p_t`, with equality unless `x_{t+1} = 0`, and
`x' ≥ 0`, then `Σ_{t ≤ n} p_t(c'_t − c_t) ≤ p₀(x'₀ − x₀) + p_n(x_{n+1} − x'_{n+1})/R`, where
`c_t = x_t − x_{t+1}/R` (up to the common income `I`). -/
theorem abel_bound {R : ℝ} (hR : 0 < R) {p x x' : ℕ → ℝ}
    (hp : ∀ t, R * p (t + 1) ≤ p t) (hpx : ∀ t, (p t - R * p (t + 1)) * x (t + 1) = 0)
    (hx' : ∀ t, 0 ≤ x' t) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), p t * ((x' t - x' (t + 1) / R) - (x t - x (t + 1) / R)) ≤
      p 0 * (x' 0 - x 0) + p n * (x (n + 1) - x' (n + 1)) / R := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    apply le_of_eq
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : p n * (x (n + 1) - x' (n + 1)) / R + p (n + 1) * (x' (n + 1) - x (n + 1)) =
        -(x' (n + 1) * (p n - R * p (n + 1))) / R := by
      field_simp
      linear_combination hpx n
    have hk : 0 ≤ x' (n + 1) * (p n - R * p (n + 1)) / R :=
      div_nonneg (mul_nonneg (hx' (n + 1)) (by linarith [hp n])) hR.le
    have e : p (n + 1) * ((x' (n + 1) - x' (n + 1 + 1) / R) - (x (n + 1) - x (n + 1 + 1) / R)) =
        p (n + 1) * (x' (n + 1) - x (n + 1)) +
          p (n + 1) * (x (n + 1 + 1) - x' (n + 1 + 1)) / R := by
      ring
    rw [e]
    have : -(x' (n + 1) * (p n - R * p (n + 1))) / R =
        -(x' (n + 1) * (p n - R * p (n + 1)) / R) := neg_div _ _
    linarith

/-! ### The dynamic program -/

/-- Wealth levels `x ≥ 0`. -/
abbrev CSWealth := ↥(Ici (0 : ℝ))

/-- `Γ(x) = [0, (I + x)R]`. -/
def csΓ (R I : ℝ) (x : CSWealth) : Set CSWealth := {y | y.1 ≤ (I + x.1) * R}

/-- `F(x, y) = U(I + x − y/R)`, clamped at zero consumption off the graph of `Γ` (where it is
never evaluated). -/
noncomputable def csF (U : ℝ → ℝ) (R I : ℝ) (x y : CSWealth) : ℝ := U (max (I + x.1 - y.1 / R) 0)

/-- Consumption `c_t = I + x_t − x_{t+1}/R` along a plan. -/
noncomputable def consOf (R I : ℝ) (x : ℕ → CSWealth) (t : ℕ) : ℝ := I + (x t).1 - (x (t + 1)).1 / R

theorem CSHyp.consOf_nonneg (h : CSHyp U U' β R I) {z : CSWealth} {x : ℕ → CSWealth}
    (hx : x ∈ Feasible (csΓ R I) z) (t : ℕ) : 0 ≤ consOf R I x t := by
  have : (x (t + 1)).1 / R ≤ I + (x t).1 := (div_le_iff₀ h.hR).2 (hx.2 t)
  simp only [consOf]
  linarith

theorem CSHyp.csF_eq (h : CSHyp U U' β R I) {z : CSWealth} {x : ℕ → CSWealth}
    (hx : x ∈ Feasible (csΓ R I) z) (t : ℕ) : csF U R I (x t) (x (t + 1)) = U (consOf R I x t) := by
  change U (max (consOf R I x t) 0) = _
  rw [max_eq_left (h.consOf_nonneg hx t)]

theorem CSHyp.assumption41 (h : CSHyp U U' β R I) : Assumption41 (csΓ R I) := fun x =>
  ⟨⟨0, mem_Ici.2 le_rfl⟩, mul_nonneg (add_nonneg h.hI.le x.2) h.hR.le⟩

/-- `F ≥ U(0)`, so Assumption 4.2 holds. -/
theorem CSHyp.assumption42 (h : CSHyp U U' β R I) : Assumption42 (csΓ R I) (csF U R I) β :=
  assumption42_of_bddBelow (M := U 0) (fun _ _ => h.hUm.monotoneOn (mem_Ici.2 le_rfl)
    (mem_Ici.2 (le_max_right _ _)) (le_max_right _ _)) h.hβ0.le h.hβ1

/-- The plan of `μ` as a sequence of wealth levels. -/
noncomputable def planN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) : CSWealth :=
  ⟨planμ U' β R I μ t, h.planμ_nonneg hμ t⟩

/-- The initial wealth `Ξ(μ)` of the plan of `μ`. -/
noncomputable def wealthN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) : CSWealth :=
  ⟨wealth U' β R I μ, h.wealth_nonneg hμ⟩

theorem CSHyp.planN_feasible (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    planN h hμ ∈ Feasible (csΓ R I) (wealthN h hμ) := by
  refine ⟨Subtype.ext (planμ_zero μ), fun t => ?_⟩
  change planμ U' β R I μ (t + 1) ≤ (I + planμ U' β R I μ t) * R
  rw [h.planμ_succ hμ]
  have := h.consμ_ge hμ t
  nlinarith [h.hR, h.hI]

theorem CSHyp.consOf_planN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    consOf R I (planN h hμ) t = consμ U' β R I μ t :=
  (h.consμ_eq hμ t).symm

/-- `V(μ) = Σ_t βᵗU(c_t)`, the value of the plan of `μ`. -/
noncomputable def valμ (U U' : ℝ → ℝ) (β R I μ : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * U (consμ U' β R I μ t)

theorem CSHyp.summable_val (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    Summable fun t : ℕ => β ^ t * U (consμ U' β R I μ t) := by
  obtain ⟨K, hK⟩ := h.exists_plan_zero hμ
  have hg : Summable fun t : ℕ => β ^ t * U I :=
    (summable_geometric_of_lt_one h.hβ0.le h.hβ1).mul_right _
  have hd : Summable fun t : ℕ => β ^ t * U (consμ U' β R I μ t) - β ^ t * U I :=
    summable_of_ne_finset_zero (s := Finset.range K) fun t ht => by
      rw [(hK t (by simpa using ht)).2, sub_self]
  exact (hd.add hg).congr fun t => by ring

theorem CSHyp.partialSum_planN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    partialSum (csF U R I) β (planN h hμ) n =
      ∑ t ∈ Finset.range (n + 1), β ^ t * U (consμ U' β R I μ t) := by
  simp only [partialSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [h.csF_eq (h.planN_feasible hμ) t, h.consOf_planN hμ t]

theorem CSHyp.tendsto_plan (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n => partialSum (csF U R I) β (planN h hμ) n) atTop
      (𝓝 (valμ U U' β R I μ)) := by
  simp only [h.partialSum_planN hμ]
  exact (h.summable_val hμ).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem CSHyp.plan_total (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    total (csF U R I) β (planN h hμ) = (valμ U U' β R I μ : EReal) :=
  tendsto_nhds_unique (tendsto_total h.assumption42 (h.planN_feasible hμ))
    (EReal.tendsto_coe.2 (h.tendsto_plan hμ))

/-- The concavity gap `δ_t = U(c_t) + U'(c_t)(c'_t − c_t) − U(c'_t) ≥ 0`. -/
noncomputable def gapAt (U U' : ℝ → ℝ) (c c' : ℝ) : ℝ := U c + U' c * (c' - c) - U c'

theorem CSHyp.gapAt_nonneg (h : CSHyp U U' β R I) {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c') :
    0 ≤ gapAt U U' c c' := by
  have := h.super_le hc hc'
  simp only [gapAt]
  linarith

/-- **The key bound.** Along any plan `x'` feasible from `z`, from some date on,
`Σ_{t ≤ n} βᵗU(c'_t) + Σ_{t ≤ n} βᵗδ_t ≤ Σ_{t ≤ n} βᵗU(c_t) + U'(c₀)(z − x₀)`. -/
theorem CSHyp.value_bound (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {z : CSWealth}
    {x' : ℕ → CSWealth} (hx' : x' ∈ Feasible (csΓ R I) z) :
    ∃ K : ℕ, ∀ n, K ≤ n →
      partialSum (csF U R I) β x' n + ∑ t ∈ Finset.range (n + 1),
        β ^ t * gapAt U U' (consμ U' β R I μ t) (consOf R I x' t) ≤
      partialSum (csF U R I) β (planN h hμ) n +
        U' (cI U' I μ) * (z.1 - wealth U' β R I μ) := by
  obtain ⟨K, hK⟩ := h.exists_plan_zero hμ
  refine ⟨K, fun n hn => ?_⟩
  have hc : ∀ t, consμ U' β R I μ t =
      I + planμ U' β R I μ t - planμ U' β R I μ (t + 1) / R := h.consμ_eq hμ
  have hp : ∀ t, R * (β ^ (t + 1) * U' (consμ U' β R I μ (t + 1))) ≤
      β ^ t * U' (consμ U' β R I μ t) := fun t => by
    have := mul_le_mul_of_nonneg_left (h.euler_step hμ t).1 (pow_nonneg h.hβ0.le t)
    calc R * (β ^ (t + 1) * U' (consμ U' β R I μ (t + 1)))
        = β ^ t * (R * β * U' (consμ U' β R I μ (t + 1))) := by ring
      _ ≤ _ := this
  have hpx : ∀ t, (β ^ t * U' (consμ U' β R I μ t) -
      R * (β ^ (t + 1) * U' (consμ U' β R I μ (t + 1)))) * planμ U' β R I μ (t + 1) = 0 :=
    fun t => by
      calc _ = β ^ t * ((U' (consμ U' β R I μ t) - R * β * U' (consμ U' β R I μ (t + 1))) *
            planμ U' β R I μ (t + 1)) := by ring
        _ = 0 := by rw [(h.euler_step hμ t).2, mul_zero]
  have hab := abel_bound h.hR hp hpx (x' := fun t => (x' t).1) (fun t => (x' t).2) n
  have hsum : partialSum (csF U R I) β x' n + ∑ t ∈ Finset.range (n + 1),
      β ^ t * gapAt U U' (consμ U' β R I μ t) (consOf R I x' t) =
      partialSum (csF U R I) β (planN h hμ) n + ∑ t ∈ Finset.range (n + 1),
        β ^ t * U' (consμ U' β R I μ t) * (((x' t).1 - (x' (t + 1)).1 / R) -
          (planμ U' β R I μ t - planμ U' β R I μ (t + 1) / R)) := by
    rw [h.partialSum_planN hμ]
    simp only [partialSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [h.csF_eq hx' t]
    simp only [gapAt, consOf]
    rw [hc t]
    ring
  have hxn : planμ U' β R I μ (n + 1) = 0 := (hK (n + 1) (by omega)).1
  have hpn : 0 ≤ β ^ n * U' (consμ U' β R I μ n) :=
    mul_nonneg (pow_nonneg h.hβ0.le n) (h.U'_pos (h.hI.trans_le (h.consμ_ge hμ n))).le
  have hlast : 0 ≤ β ^ n * U' (consμ U' β R I μ n) * (x' (n + 1)).1 / R :=
    div_nonneg (mul_nonneg hpn (x' (n + 1)).2) h.hR.le
  have hx0 : (x' 0).1 = z.1 := by rw [hx'.1]
  simp only [pow_zero, one_mul, consμ_zero, planμ_zero, hx0, hxn] at hab
  rw [hsum]
  have e : β ^ n * U' (consμ U' β R I μ n) * (0 - (x' (n + 1)).1) / R =
      -(β ^ n * U' (consμ U' β R I μ n) * (x' (n + 1)).1 / R) := by ring
  rw [e] at hab
  linarith

/-- Along any plan feasible from `z`: `u(x') ≤ V(μ) + U'(c₀)(z − x₀) − βᵗδ_t`. -/
theorem CSHyp.total_le (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {z : CSWealth}
    {x' : ℕ → CSWealth} (hx' : x' ∈ Feasible (csΓ R I) z) (t₀ : ℕ) :
    total (csF U R I) β x' ≤ ((valμ U U' β R I μ + U' (cI U' I μ) * (z.1 - wealth U' β R I μ) -
      β ^ t₀ * gapAt U U' (consμ U' β R I μ t₀) (consOf R I x' t₀) : ℝ) : EReal) := by
  obtain ⟨K, hK⟩ := h.value_bound hμ hx'
  have hgap : ∀ t, 0 ≤ β ^ t * gapAt U U' (consμ U' β R I μ t) (consOf R I x' t) := fun t =>
    mul_nonneg (pow_nonneg h.hβ0.le t) (h.gapAt_nonneg (h.hI.trans_le (h.consμ_ge hμ t))
      (h.consOf_nonneg hx' t))
  refine le_of_tendsto_of_tendsto (tendsto_total h.assumption42 hx')
    (EReal.tendsto_coe.2 (((h.tendsto_plan hμ).add_const
      (U' (cI U' I μ) * (z.1 - wealth U' β R I μ))).sub_const
        (β ^ t₀ * gapAt U U' (consμ U' β R I μ t₀) (consOf R I x' t₀)))) ?_
  filter_upwards [eventually_ge_atTop (max K t₀)] with n hn
  refine EReal.coe_le_coe_iff.2 ?_
  have hb := hK n (le_of_max_le_left hn)
  have hs := Finset.single_le_sum (f := fun t => β ^ t * gapAt U U' (consμ U' β R I μ t)
    (consOf R I x' t)) (fun t _ => hgap t)
    (Finset.mem_range.2 (by omega : t₀ < n + 1))
  linarith

/-- The supergradient bound `u(x') ≤ V(μ) + U'(c₀)(z − x₀)`. -/
theorem CSHyp.total_le_tangent (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {z : CSWealth}
    {x' : ℕ → CSWealth} (hx' : x' ∈ Feasible (csΓ R I) z) :
    total (csF U R I) β x' ≤
      ((valμ U U' β R I μ + U' (cI U' I μ) * (z.1 - wealth U' β R I μ) : ℝ) : EReal) := by
  refine (h.total_le hμ hx' 0).trans (EReal.coe_le_coe_iff.2 ?_)
  have := h.gapAt_nonneg (h.hI.trans_le (h.consμ_ge hμ 0)) (h.consOf_nonneg hx' 0)
  simp only [pow_zero, one_mul]
  linarith

/-- A feasible plan with the consumption of the plan of `μ`, from the same wealth, is that plan. -/
theorem CSHyp.eq_planN_of_cons (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ)
    {x' : ℕ → CSWealth} (h0 : (x' 0).1 = wealth U' β R I μ)
    (hc : ∀ t, consOf R I x' t = consμ U' β R I μ t) : x' = planN h hμ := by
  have key : ∀ t, (x' t).1 = planμ U' β R I μ t := by
    intro t
    induction t with
    | zero => rw [h0, planμ_zero]
    | succ t ih =>
      have e := hc t
      rw [h.consμ_eq hμ t] at e
      simp only [consOf] at e
      rw [ih] at e
      have hR := h.hR.ne'
      field_simp at e
      linarith
  funext t
  exact Subtype.ext (key t)

/-- **Uniqueness.** Every other plan feasible from `Ξ(μ)` does strictly worse. -/
theorem CSHyp.total_lt (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {x' : ℕ → CSWealth}
    (hx' : x' ∈ Feasible (csΓ R I) (wealthN h hμ)) (hne : x' ≠ planN h hμ) :
    total (csF U R I) β x' < (valμ U U' β R I μ : EReal) := by
  have hc : ∃ t, consOf R I x' t ≠ consμ U' β R I μ t := by
    by_contra hall
    push Not at hall
    exact hne (h.eq_planN_of_cons hμ (by rw [hx'.1]; rfl) hall)
  obtain ⟨t₀, ht₀⟩ := hc
  have hgap : 0 < gapAt U U' (consμ U' β R I μ t₀) (consOf R I x' t₀) := by
    have := h.super_lt (h.hI.trans_le (h.consμ_ge hμ t₀)) (h.consOf_nonneg hx' t₀) ht₀
    simp only [gapAt]
    linarith
  refine (h.total_le hμ hx' t₀).trans_lt (EReal.coe_lt_coe_iff.2 ?_)
  have := mul_pos (pow_pos h.hβ0 t₀) hgap
  simp only [wealthN, sub_self, mul_zero, add_zero]
  linarith

/-- `v*(Ξ(μ)) = V(μ)`. -/
theorem CSHyp.vstar_eq (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    vstar (csΓ R I) (csF U R I) β (wealthN h hμ) = (valμ U U' β R I μ : EReal) := by
  refine le_antisymm (iSup₂_le fun x' hx' => (h.total_le_tangent hμ hx').trans ?_) ?_
  · simp [wealthN]
  · rw [← h.plan_total hμ]
    exact le_biSup (total (csF U R I) β) (h.planN_feasible hμ)

/-- The supergradient inequality `v*(z) ≤ v*(Ξ(μ)) + U'(c₀)(z − Ξ(μ))`. -/
theorem CSHyp.vstar_le_tangent (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (z : CSWealth) :
    vstar (csΓ R I) (csF U R I) β z ≤
      ((valμ U U' β R I μ + U' (cI U' I μ) * (z.1 - wealth U' β R I μ) : ℝ) : EReal) :=
  iSup₂_le fun _ hx' => h.total_le_tangent hμ hx'

/-- The plan of `μ` is the unique optimal plan from `Ξ(μ)`. -/
theorem CSHyp.optimal_iff (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {x' : ℕ → CSWealth}
    (hx' : x' ∈ Feasible (csΓ R I) (wealthN h hμ)) :
    total (csF U R I) β x' = vstar (csΓ R I) (csF U R I) β (wealthN h hμ) ↔
      x' = planN h hμ := by
  rw [h.vstar_eq hμ]
  refine ⟨fun heq => by_contra fun hne => ?_, fun he => he ▸ h.plan_total hμ⟩
  exact lt_irrefl _ (heq ▸ h.total_lt hμ hx' hne)

/-- `v*` is real-valued: `v*(x) = V(μ)` for any `μ > 0` with `Ξ(μ) = x`. -/
theorem CSHyp.vstar_real (h : CSHyp U U' β R I) (x : CSWealth) :
    ∃ v : ℝ, vstar (csΓ R I) (csF U R I) β x = v := by
  obtain ⟨μ, hμ, -, hw⟩ := h.exists_wealth_eq x.2
  have : x = wealthN h hμ := Subtype.ext hw.symm
  exact ⟨_, this ▸ h.vstar_eq hμ⟩

/-- **Exercise 5.17a.** `v*` is real-valued and satisfies (FE), and an optimal plan satisfies
`v*(x_t) = U(I + x_t − x_{t+1}/R) + βv*(x_{t+1})`. -/
theorem ex_5_17a (h : CSHyp U U' β R I) :
    (∀ x : CSWealth, ∃ v : ℝ, vstar (csΓ R I) (csF U R I) β x = v) ∧
      SatisfiesFE (csΓ R I) (csF U R I) β (vstar (csΓ R I) (csF U R I) β) ∧
      ∀ (x₀ : CSWealth) (xs : ℕ → CSWealth), xs ∈ Feasible (csΓ R I) x₀ →
        total (csF U R I) β xs = vstar (csΓ R I) (csF U R I) β x₀ → ∀ t,
          vstar (csΓ R I) (csF U R I) β (xs t) = (U (consOf R I xs t) : EReal) +
            (β : EReal) * vstar (csΓ R I) (csF U R I) β (xs (t + 1)) :=
  ⟨h.vstar_real, theorem_4_2 h.hβ0.le h.assumption41 h.assumption42,
    fun _ _ hxs hopt t => by
      rw [theorem_4_4 h.hβ0 h.assumption42 hxs hopt t, h.csF_eq hxs t]⟩

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A consumption–savings problem: value, policy and the induction

SLP §5.17, Exercise 5.17b–h. From `ConsumptionSavings`, the optimal plan from `x ≥ 0` is the plan
of any multiplier `μ` with `Ξ(μ) = x` (`muOf`; all such plans coincide, `planN_eq`). On `ℝ₊`
define the value `v` (`vR`), the policy `g` (`gR`) and initial consumption `c₀ = I + x − g(x)/R`
(`cR`).

* `c₀` is continuous and strictly increasing from `c₀(0) = I` onto `[I, ∞)`.
* `v(z) ≤ v(x) + U'(c₀(x))(z − x)` (`vR_le_tangent`, from the summation-by-parts bound), and
  `U'(c₀)` is continuous, so `v` is differentiable on `ℝ₊` with `v'(x) = U'(I + x − g(x)/R)`
  (`hasDerivWithinAt_vR`). Since `v' > 0` and `v'` falls strictly, `v` is strictly increasing
  and strictly concave.

The book's induction runs over intervals `(m_{n−1}, m_n]`. Its objects are global here:
* `m₁` solves `U'(I + m₁) = RβU'(I)` (`m1`);
* `h(y) = Ξ(RβU'(c₀(y)))` (`hfun`) solves (2) for every `y > 0`;
* `m_{n+1} = h(m_n)`, with `m_n = Ξ((Rβ)ⁿU'(I)) → ∞` (`mSeq`).

Exercises 5.17b–h follow (`ex_5_17b` … `ex_5_17h`).

**Correction to 5.17h.** The book claims `g(x') − g(x) < x' − x`. That holds when `R ≤ 1`, but not
in general when `R > 1`. What does hold is `g(x') − g(x) < R(x' − x)`, i.e. consumption rises
strictly with wealth (`ex_5_17h_slope`). See `ConsumptionSavingsCounterexample`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {U U' : ℝ → ℝ} {β R I : ℝ}

/-! ### Plans from the same wealth coincide -/

theorem CSHyp.planN_eq (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) : planN h hν = planN h hμ := by
  have hW : wealthN h hν = wealthN h hμ := Subtype.ext hw.symm
  have hfeas : planN h hν ∈ Feasible (csΓ R I) (wealthN h hμ) := by
    rw [← hW]; exact h.planN_feasible hν
  refine (h.optimal_iff hμ hfeas).1 ?_
  rw [h.plan_total hν, ← h.vstar_eq hν, hW]

theorem CSHyp.planμ_eq_of_wealth (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) (t : ℕ) :
    planμ U' β R I ν t = planμ U' β R I μ t :=
  congrArg Subtype.val (congrFun (h.planN_eq hμ hν hw) t)

theorem CSHyp.consμ_eq_of_wealth (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) (t : ℕ) :
    consμ U' β R I ν t = consμ U' β R I μ t := by
  rw [← h.consOf_planN hν, ← h.consOf_planN hμ, h.planN_eq hμ hν hw]

theorem CSHyp.valμ_eq_of_wealth (h : CSHyp U U' β R I) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hw : wealth U' β R I μ = wealth U' β R I ν) : valμ U U' β R I ν = valμ U U' β R I μ :=
  tsum_congr fun t => by rw [h.consμ_eq_of_wealth hμ hν hw t]

/-- `U'(cI(p)) = p` for `0 < p ≤ U'(I)`. -/
theorem CSHyp.U'_cI (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) (hpI : p ≤ U' I) :
    U' (cI U' I p) = p := by
  rcases eq_or_lt_of_le (h.cI_mem hp).1 with he | hgt
  · have := (h.cI_mem hp).2
    rw [← he] at this ⊢
    exact le_antisymm this hpI
  · exact h.cI_eq hp hgt

/-! ### Value, policy and consumption on `ℝ₊` -/

/-- A multiplier of wealth `x ≥ 0`: some `μ ∈ (0, U'(I)]` with `Ξ(μ) = x`. -/
noncomputable def muOf (h : CSHyp U U' β R I) (x : ℝ) : ℝ := by
  classical exact if hx : 0 ≤ x then Classical.choose (h.exists_wealth_eq hx) else U' I

theorem CSHyp.muOf_spec (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    0 < muOf h x ∧ muOf h x ≤ U' I ∧ wealth U' β R I (muOf h x) = x := by
  simp only [muOf, hx, ↓reduceDIte]
  exact Classical.choose_spec (h.exists_wealth_eq hx)

/-- The value function `v`. -/
noncomputable def vR (h : CSHyp U U' β R I) (x : ℝ) : ℝ := valμ U U' β R I (muOf h x)

/-- The policy function `g`. -/
noncomputable def gR (h : CSHyp U U' β R I) (x : ℝ) : ℝ := planμ U' β R I (muOf h x) 1

/-- Initial consumption `c₀(x) = I + x − g(x)/R`. -/
noncomputable def cR (h : CSHyp U U' β R I) (x : ℝ) : ℝ := cI U' I (muOf h x)

theorem CSHyp.vR_wealth (h : CSHyp U U' β R I) {ν : ℝ} (hν : 0 < ν) :
    vR h (wealth U' β R I ν) = valμ U U' β R I ν := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec (h.wealth_nonneg hν)
  exact h.valμ_eq_of_wealth hν hμ hw.symm

theorem CSHyp.gR_wealth (h : CSHyp U U' β R I) {ν : ℝ} (hν : 0 < ν) :
    gR h (wealth U' β R I ν) = wealth U' β R I (ν / (R * β)) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec (h.wealth_nonneg hν)
  rw [gR, h.planμ_eq_of_wealth hν hμ hw.symm, planμ, pow_one]

theorem CSHyp.cR_wealth (h : CSHyp U U' β R I) {ν : ℝ} (hν : 0 < ν) :
    cR h (wealth U' β R I ν) = cI U' I ν := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec (h.wealth_nonneg hν)
  have := h.consμ_eq_of_wealth hν hμ hw.symm 0
  rwa [consμ_zero, consμ_zero] at this

/-- **`v = v*`** on `ℝ₊`. -/
theorem CSHyp.vstar_wealth (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    vstar (csΓ R I) (csF U R I) β ⟨x, hx⟩ = (vR h x : EReal) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  have : (⟨x, hx⟩ : CSWealth) = wealthN h hμ := Subtype.ext hw.symm
  rw [this, h.vstar_eq hμ]
  rfl

theorem CSHyp.cR_ge (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) : I ≤ cR h x :=
  (h.cI_mem (h.muOf_spec hx).1).1

theorem CSHyp.cR_pos (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) : 0 < cR h x :=
  h.hI.trans_le (h.cR_ge hx)

theorem CSHyp.gR_nonneg (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gR h x :=
  h.planμ_nonneg (h.muOf_spec hx).1 1

/-- `g(x) = R(I + x − c₀(x))`. -/
theorem CSHyp.gR_eq (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    gR h x = R * (I + x - cR h x) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  rw [gR, h.planμ_succ hμ 0, planμ_zero, hw, consμ_zero]
  rfl

theorem CSHyp.cR_eq (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    cR h x = I + x - gR h x / R := by
  rw [h.gR_eq hx, mul_div_cancel_left₀ _ h.hR.ne']
  ring

theorem CSHyp.cR_zero (h : CSHyp U U' β R I) : cR h 0 = I := by
  have hU := h.U'_pos h.hI
  have := h.cR_wealth hU
  rwa [h.wealth_of_ge le_rfl, h.cI_of_le le_rfl] at this

/-- Larger wealth has a smaller multiplier, below `U'(I)`. -/
theorem CSHyp.muOf_lt (h : CSHyp U U' β R I) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x < x') :
    muOf h x' < muOf h x ∧ muOf h x' < U' I := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  obtain ⟨hμ', -, hw'⟩ := h.muOf_spec (hx.trans hxx'.le)
  refine ⟨not_le.1 fun hle => ?_, h.lt_of_wealth_pos (by rw [hw']; linarith)⟩
  have := h.wealth_anti hμ hle
  rw [hw, hw'] at this
  linarith

theorem CSHyp.cR_strictMono (h : CSHyp U U' β R I) : StrictMonoOn (cR h) (Ici 0) := by
  intro x hx x' _ hxx'
  obtain ⟨hlt, hltI⟩ := h.muOf_lt hx hxx'
  exact h.cI_strictAnti (h.muOf_spec (le_trans hx hxx'.le)).1 hlt hltI

/-- `c₀` maps `ℝ₊` onto `[I, ∞)`. -/
theorem CSHyp.cR_surj (h : CSHyp U U' β R I) {c : ℝ} (hc : I ≤ c) :
    ∃ x, 0 ≤ x ∧ cR h x = c := by
  have hp := h.U'_pos (h.hI.trans_le hc)
  exact ⟨_, h.wealth_nonneg hp, by rw [h.cR_wealth hp, h.cI_U' hc]⟩

theorem CSHyp.continuousWithinAt_cR (h : CSHyp U U' β R I) {x₀ : ℝ} (hx₀ : 0 ≤ x₀) :
    ContinuousWithinAt (cR h) (Ici 0) x₀ := by
  have hmono := h.cR_strictMono
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a I with haI | haI
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact haI.trans_le (h.cR_ge hx)
    · obtain ⟨x₁, hx₁, hc₁⟩ := h.cR_surj (c := (a + cR h x₀) / 2) (by linarith)
      have hx₁x₀ : x₁ < x₀ := (hmono.lt_iff_lt hx₁ hx₀).1 (by rw [hc₁]; linarith)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds hx₁x₀)]
        with x hx hxx
      have := hmono hx₁ hx hxx
      linarith
  · obtain ⟨x₂, hx₂, hc₂⟩ := h.cR_surj (c := (cR h x₀ + b) / 2) (by linarith [h.cR_ge hx₀])
    have hx₀x₂ : x₀ < x₂ := (hmono.lt_iff_lt hx₀ hx₂).1 (by rw [hc₂]; linarith)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hx₀x₂)] with x hx hxx
    have := hmono hx hx₂ hxx
    linarith

theorem CSHyp.continuousOn_cR (h : CSHyp U U' β R I) : ContinuousOn (cR h) (Ici 0) :=
  fun _ hx => h.continuousWithinAt_cR hx

theorem CSHyp.continuousOn_gR (h : CSHyp U U' β R I) : ContinuousOn (gR h) (Ici 0) := by
  refine ContinuousOn.congr (f := fun x => R * (I + x - cR h x)) ?_ fun x hx => h.gR_eq hx
  exact continuousOn_const.mul ((continuousOn_const.add continuousOn_id).sub h.continuousOn_cR)

/-- The marginal value `U'(c₀(x))` is continuous on `ℝ₊`. -/
theorem CSHyp.continuousOn_marg (h : CSHyp U U' β R I) :
    ContinuousOn (fun x => U' (cR h x)) (Ici 0) := fun _ hx =>
  (h.hU'c.continuousAt (Ioi_mem_nhds (h.cR_pos hx))).comp_continuousWithinAt
    (h.continuousWithinAt_cR hx)

/-! ### Differentiability, monotonicity and concavity of `v` -/

/-- **The supergradient inequality** `v(z) ≤ v(x) + U'(c₀(x))(z − x)`. -/
theorem CSHyp.vR_le_tangent (h : CSHyp U U' β R I) {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    vR h z ≤ vR h x + U' (cR h x) * (z - x) := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  have := h.vstar_le_tangent hμ ⟨z, hz⟩
  rw [h.vstar_wealth hz, hw] at this
  exact EReal.coe_le_coe_iff.1 this

/-- `v` is differentiable on `ℝ₊` (one-sided at `0`) with `v'(x) = U'(c₀(x))`. -/
theorem CSHyp.hasDerivWithinAt_vR (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (vR h) (U' (cR h x)) (Ici 0) x := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Tendsto (fun z => U' (cR h z)) (𝓝[Ici 0 \ {x}] x) (𝓝 (U' (cR h x))) :=
    (h.continuousOn_marg x hx).tendsto.mono_left (nhdsWithin_mono _ sdiff_subset)
  have hlo : Tendsto (fun z => min (U' (cR h z)) (U' (cR h x))) (𝓝[Ici 0 \ {x}] x)
      (𝓝 (U' (cR h x))) := by
    have := hs.min (tendsto_const_nhds (x := U' (cR h x)))
    rwa [min_self] at this
  have hhi : Tendsto (fun z => max (U' (cR h z)) (U' (cR h x))) (𝓝[Ici 0 \ {x}] x)
      (𝓝 (U' (cR h x))) := by
    have := hs.max (tendsto_const_nhds (x := U' (cR h x)))
    rwa [max_self] at this
  have hbd : ∀ z ∈ Ici (0 : ℝ) \ {x}, min (U' (cR h z)) (U' (cR h x)) ≤ slope (vR h) x z ∧
      slope (vR h) x z ≤ max (U' (cR h z)) (U' (cR h x)) := by
    rintro z ⟨hz, hzx⟩
    have hz1 := h.vR_le_tangent hx hz
    have hz2 := h.vR_le_tangent hz hx
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hzx with hlt | hgt
    · have hneg : z - x < 0 := sub_neg.2 hlt
      exact ⟨(min_le_right _ _).trans ((le_div_iff_of_neg hneg).2 (by linarith)),
        ((div_le_iff_of_neg hneg).2 (by linarith)).trans (le_max_left _ _)⟩
    · have hpos : 0 < z - x := sub_pos.2 hgt
      exact ⟨(min_le_left _ _).trans ((le_div_iff₀ hpos).2 (by linarith)),
        ((div_le_iff₀ hpos).2 (by linarith)).trans (le_max_right _ _)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (eventually_nhdsWithin_of_forall fun z hz => (hbd z hz).1)
    (eventually_nhdsWithin_of_forall fun z hz => (hbd z hz).2)

theorem CSHyp.hasDerivAt_vR (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (vR h) (U' (cR h x)) x :=
  (h.hasDerivWithinAt_vR hx.le).hasDerivAt (Ici_mem_nhds hx)

theorem CSHyp.deriv_vR (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 < x) :
    deriv (vR h) x = U' (I + x - gR h x / R) := by
  rw [(h.hasDerivAt_vR hx).deriv, h.cR_eq hx.le]

theorem CSHyp.continuousOn_vR (h : CSHyp U U' β R I) : ContinuousOn (vR h) (Ici 0) :=
  fun _ hx => (h.hasDerivWithinAt_vR hx).continuousWithinAt

theorem CSHyp.vR_strictMono (h : CSHyp U U' β R I) : StrictMonoOn (vR h) (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) h.continuousOn_vR fun x hx => by
    rw [interior_Ici] at hx
    rw [(h.hasDerivAt_vR hx).deriv]
    exact h.U'_pos (h.cR_pos hx.le)

theorem CSHyp.vR_strictConcave (h : CSHyp U U' β R I) : StrictConcaveOn ℝ (Ici 0) (vR h) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) h.continuousOn_vR ?_
  rw [interior_Ici]
  intro a ha b hb hab
  rw [(h.hasDerivAt_vR ha).deriv, (h.hasDerivAt_vR hb).deriv]
  exact h.U'_lt (h.cR_pos (le_of_lt ha)) (h.cR_strictMono (mem_Ici.2 (le_of_lt ha))
    (mem_Ici.2 (le_of_lt hb)) hab)

/-! ### Exercise 5.17b: the interval `[0, m₁]` -/

/-- `m₁`, defined by `U'(I + m₁) = RβU'(I)`. -/
noncomputable def m1 (U' : ℝ → ℝ) (β R I : ℝ) : ℝ := cI U' I (R * β * U' I) - I

theorem CSHyp.rhoU_pos (h : CSHyp U U' β R I) : 0 < R * β * U' I :=
  mul_pos h.rho_pos (h.U'_pos h.hI)

theorem CSHyp.rhoU_lt (h : CSHyp U U' β R I) : R * β * U' I < U' I := by
  have := h.U'_pos h.hI
  nlinarith [h.hRβ]

/-- **Exercise 5.17b.** `m₁ > 0` is well defined: it is the unique `m ≥ 0` with
`U'(I + m) = RβU'(I)`. -/
theorem ex_5_17b_m1 (h : CSHyp U U' β R I) :
    0 < m1 U' β R I ∧ U' (I + m1 U' β R I) = R * β * U' I ∧
      ∀ m, 0 ≤ m → U' (I + m) = R * β * U' I → m = m1 U' β R I := by
  have hgt := h.cI_gt h.rhoU_pos h.rhoU_lt
  have hU : U' (I + m1 U' β R I) = R * β * U' I := by
    rw [m1, add_sub_cancel]; exact h.cI_eq h.rhoU_pos hgt
  refine ⟨by simp only [m1]; linarith, hU, fun m hm hm' => ?_⟩
  have hpos : 0 < I + m := by linarith [h.hI]
  have hpos1 : 0 < I + m1 U' β R I := by simp only [m1]; linarith [h.hI]
  rcases lt_trichotomy m (m1 U' β R I) with hlt | heq | hgt'
  · have := h.U'_lt hpos (by linarith : I + m < I + m1 U' β R I); linarith
  · exact heq
  · have := h.U'_lt hpos1 (by linarith : I + m1 U' β R I < I + m); linarith

theorem CSHyp.m1_pos (h : CSHyp U U' β R I) : 0 < m1 U' β R I := (ex_5_17b_m1 h).1

theorem CSHyp.wealth_rhoU (h : CSHyp U U' β R I) :
    wealth U' β R I (R * β * U' I) = m1 U' β R I := by
  rw [h.wealth_shift h.rhoU_pos, mul_div_cancel_left₀ _ h.rho_pos.ne',
    h.wealth_of_ge le_rfl, mul_zero, add_zero]
  rfl

theorem CSHyp.muOf_ge (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) (hxm : x ≤ m1 U' β R I) :
    R * β * U' I ≤ muOf h x := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hx
  refine not_lt.1 fun hlt => ?_
  have := h.wealth_strictAnti hμ hlt (hlt.trans h.rhoU_lt)
  rw [hw, h.wealth_rhoU] at this
  linarith

theorem CSHyp.gR_eq_zero (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x)
    (hxm : x ≤ m1 U' β R I) : gR h x = 0 := by
  have := h.muOf_ge hx hxm
  rw [gR, planμ, pow_one]
  exact h.wealth_of_ge ((le_div_iff₀ h.rho_pos).2 (by linarith))

theorem CSHyp.gR_pos (h : CSHyp U U' β R I) {x : ℝ} (hxm : m1 U' β R I < x) : 0 < gR h x := by
  have hx : 0 ≤ x := h.m1_pos.le.trans hxm.le
  obtain ⟨hμ, -, -⟩ := h.muOf_spec hx
  have hlt : muOf h x / (R * β) < U' I := by
    refine not_le.1 fun hle => ?_
    have h1 : R * β * U' I ≤ muOf h x := by
      have := (le_div_iff₀ h.rho_pos).1 hle; linarith
    have h2 := h.cI_anti h.rhoU_pos h1
    have h3 := h.cR_eq hx
    rw [show gR h x = 0 by rw [gR, planμ, pow_one]; exact h.wealth_of_ge hle, zero_div,
      sub_zero] at h3
    have : cR h x ≤ I + m1 U' β R I := by simp only [m1, cR]; linarith
    linarith
  rw [gR, planμ, pow_one]
  exact h.wealth_pos (div_pos hμ h.rho_pos) hlt

/-- On `[0, m₁]`, `v(x) = U(I + x) + βU(I)/(1 − β)`. -/
theorem CSHyp.vR_eq_low (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) (hxm : x ≤ m1 U' β R I) :
    vR h x = U (I + x) + β * U I / (1 - β) := by
  obtain ⟨hμ, -, -⟩ := h.muOf_spec hx
  have hge := h.muOf_ge hx hxm
  have hc0 : consμ U' β R I (muOf h x) 0 = I + x := by
    rw [consμ_zero, ← cR, h.cR_eq hx, h.gR_eq_zero hx hxm, zero_div, sub_zero]
  have hct : ∀ t : ℕ, consμ U' β R I (muOf h x) (t + 1) = I := fun t => by
    refine h.cI_of_le ?_
    have h1 : U' I ≤ muOf h x / (R * β) := (le_div_iff₀ h.rho_pos).2 (by linarith)
    refine h1.trans ?_
    rw [div_pow_succ]
    exact le_div_self (div_pos hμ h.rho_pos).le (pow_pos h.rho_pos t)
      (pow_le_one₀ h.rho_pos.le h.hRβ.le) |>.trans (le_of_eq (by
        rw [div_div, div_div, mul_comm]))
  rw [vR, valμ, (h.summable_val hμ).tsum_eq_zero_add, pow_zero, one_mul, hc0]
  have e : ∀ t : ℕ, β ^ (t + 1) * U (consμ U' β R I (muOf h x) (t + 1)) = β * U I * β ^ t :=
    fun t => by rw [hct t, pow_succ]; ring
  rw [tsum_congr e, tsum_mul_left, tsum_geometric_of_lt_one h.hβ0.le h.hβ1]
  ring

/-- **Exercise 5.17b.** On `[0, m₁]`: `g = 0`, `v(x) = U(I + x) + βU(I)/(1 − β)`, `v` is
continuous, strictly increasing and strictly concave, and `v'(x) = U'(I + x)` (one-sided at
`0`). -/
theorem ex_5_17b (h : CSHyp U U' β R I) :
    (∀ x ∈ Icc 0 (m1 U' β R I), gR h x = 0 ∧ vR h x = U (I + x) + β * U I / (1 - β) ∧
      HasDerivWithinAt (vR h) (U' (I + x)) (Ici 0) x) ∧
    ContinuousOn (vR h) (Icc 0 (m1 U' β R I)) ∧ StrictMonoOn (vR h) (Icc 0 (m1 U' β R I)) ∧
      StrictConcaveOn ℝ (Icc 0 (m1 U' β R I)) (vR h) := by
  have hsub : Icc 0 (m1 U' β R I) ⊆ Ici 0 := Icc_subset_Ici_self
  refine ⟨fun x hx => ⟨h.gR_eq_zero hx.1 hx.2, h.vR_eq_low hx.1 hx.2, ?_⟩,
    h.continuousOn_vR.mono hsub, h.vR_strictMono.mono hsub,
    h.vR_strictConcave.subset hsub (convex_Icc _ _)⟩
  have := h.hasDerivWithinAt_vR hx.1
  rwa [h.cR_eq hx.1, h.gR_eq_zero hx.1 hx.2, zero_div, sub_zero] at this

/-! ### Exercise 5.17c: the function `h` -/

/-- `h(y) = Ξ(RβU'(c₀(y)))`: the wealth from which the consumer saves `y/R`. -/
noncomputable def hfun (h : CSHyp U U' β R I) (y : ℝ) : ℝ := wealth U' β R I (R * β * U' (cR h y))

/-- The marginal value `U'(c₀(y))` is the multiplier of `y`. -/
theorem CSHyp.U'_cR (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) : U' (cR h y) = muOf h y :=
  h.U'_cI (h.muOf_spec hy).1 (h.muOf_spec hy).2.1

theorem CSHyp.gR_def (h : CSHyp U U' β R I) (x : ℝ) :
    gR h x = wealth U' β R I (muOf h x / (R * β)) := by
  rw [gR, planμ, pow_one]

theorem CSHyp.hfun_zero (h : CSHyp U U' β R I) : hfun h 0 = m1 U' β R I := by
  rw [hfun, h.cR_zero, h.wealth_rhoU]

theorem CSHyp.hfun_nonneg (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ hfun h y :=
  h.wealth_nonneg (mul_pos h.rho_pos (h.U'_pos (h.cR_pos hy)))

/-- `g(h(y)) = y`. -/
theorem CSHyp.gR_hfun (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) : gR h (hfun h y) = y := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec hy
  rw [hfun, h.U'_cR hy, h.gR_wealth (mul_pos h.rho_pos hμ),
    mul_div_cancel_left₀ _ h.rho_pos.ne', hw]

/-- (2): `U'(I + h(y) − y/R) = RβU'(c₀(y))`. -/
theorem CSHyp.euler_hfun (h : CSHyp U U' β R I) {y : ℝ} (hy : 0 ≤ y) :
    U' (I + hfun h y - y / R) = R * β * U' (cR h y) := by
  obtain ⟨hμ, hμI, -⟩ := h.muOf_spec hy
  have hρμ : 0 < R * β * muOf h y := mul_pos h.rho_pos hμ
  have hc := h.cR_eq (h.hfun_nonneg hy)
  rw [h.gR_hfun hy] at hc
  rw [← hc, hfun, h.U'_cR hy, h.cR_wealth hρμ, h.U'_cI hρμ]
  have := h.rhoU_lt
  have : R * β * muOf h y ≤ R * β * U' I := mul_le_mul_of_nonneg_left hμI h.rho_pos.le
  linarith

theorem CSHyp.hfun_strictMono (h : CSHyp U U' β R I) : StrictMonoOn (hfun h) (Ici 0) := by
  intro y hy y' hy' hyy'
  obtain ⟨hlt, hltI⟩ := h.muOf_lt hy hyy'
  have hμ' := (h.muOf_spec hy').1
  rw [hfun, hfun, h.U'_cR hy, h.U'_cR hy']
  refine h.wealth_strictAnti (mul_pos h.rho_pos hμ')
    (mul_lt_mul_of_pos_left hlt h.rho_pos) ?_
  have := h.rhoU_lt
  have : R * β * muOf h y' < R * β * U' I := mul_lt_mul_of_pos_left hltI h.rho_pos
  linarith

theorem CSHyp.continuousOn_hfun (h : CSHyp U U' β R I) : ContinuousOn (hfun h) (Ici 0) :=
  fun y hy => by
    have hc : ContinuousWithinAt (fun x => R * β * U' (cR h x)) (Ici 0) y :=
      continuousWithinAt_const.mul (h.continuousOn_marg y hy)
    change ContinuousWithinAt (wealth U' β R I ∘ fun x => R * β * U' (cR h x)) (Ici 0) y
    exact ContinuousAt.comp_continuousWithinAt (g := wealth U' β R I)
      (h.continuousAt_wealth (mul_pos h.rho_pos (h.U'_pos (h.cR_pos hy)))) hc

/-- **Exercise 5.17c.** `h` is continuous and strictly increasing, `h(y) → m₁` as `y ↓ 0`, and
for `y > 0`, `h(y)` solves (2), `U'(I + h(y) − y/R) = Rβv'(y)`, and is the wealth from which the
consumer saves `y/R`. -/
theorem ex_5_17c (h : CSHyp U U' β R I) :
    ContinuousOn (hfun h) (Ici 0) ∧ StrictMonoOn (hfun h) (Ici 0) ∧
      Tendsto (hfun h) (𝓝[>] 0) (𝓝 (m1 U' β R I)) ∧
      ∀ y, 0 < y → U' (I + hfun h y - y / R) = R * β * deriv (vR h) y ∧ gR h (hfun h y) = y := by
  refine ⟨h.continuousOn_hfun, h.hfun_strictMono, ?_, fun y hy => ⟨?_, h.gR_hfun hy.le⟩⟩
  · have := (h.continuousOn_hfun 0 (mem_Ici.2 le_rfl)).tendsto.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
    rwa [h.hfun_zero] at this
  · rw [h.euler_hfun hy.le, (h.hasDerivAt_vR hy).deriv]

/-! ### Exercises 5.17d–e: the interval `(m₁, m₂]` -/

/-- `g` is nondecreasing on `ℝ₊`. -/
theorem CSHyp.gR_mono (h : CSHyp U U' β R I) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x ≤ x') :
    gR h x ≤ gR h x' := by
  rcases eq_or_lt_of_le hxx' with rfl | hlt
  · exact le_rfl
  · rw [h.gR_def, h.gR_def]
    exact h.wealth_anti (div_pos (h.muOf_spec (hx.trans hxx')).1 h.rho_pos)
      (div_le_div_of_nonneg_right (h.muOf_lt hx hlt).1.le h.rho_pos.le)

/-- `g` is strictly increasing on `[m₁, ∞)`. -/
theorem CSHyp.gR_strictMono (h : CSHyp U U' β R I) :
    StrictMonoOn (gR h) (Ici (m1 U' β R I)) := by
  intro x hx x' _ hxx'
  have hx0 : 0 ≤ x := h.m1_pos.le.trans hx
  have hpos := h.gR_pos (lt_of_le_of_lt hx hxx')
  rw [h.gR_def] at hpos
  rw [h.gR_def, h.gR_def]
  exact h.wealth_strictAnti (div_pos (h.muOf_spec (hx0.trans hxx'.le)).1 h.rho_pos)
    (div_lt_div_of_pos_right (h.muOf_lt hx0 hxx').1 h.rho_pos) (h.lt_of_wealth_pos hpos)

/-- `m₂ = h(m₁)`. -/
noncomputable def m2 (h : CSHyp U U' β R I) : ℝ := hfun h (m1 U' β R I)

/-- `v'(x) = U'(I + x − g(x)/R)` is continuous on `ℝ₊`. -/
theorem CSHyp.continuousOn_vR' (h : CSHyp U U' β R I) :
    ContinuousOn (fun x => U' (I + x - gR h x / R)) (Ici 0) :=
  h.continuousOn_marg.congr fun x hx => by simp only [h.cR_eq hx]

/-- **Exercise 5.17d.** `m₂ > m₁`; on `[m₁, m₂]`, `g` is continuous (in particular at `m₁`)
and strictly increasing, and `v` is continuous, strictly increasing and strictly concave; on
`(m₁, m₂)`, `v` is continuously differentiable with `v'(x) = U'(I + x − g(x)/R)` (5). -/
theorem ex_5_17d (h : CSHyp U U' β R I) :
    m1 U' β R I < m2 h ∧ ContinuousOn (gR h) (Icc (m1 U' β R I) (m2 h)) ∧
      StrictMonoOn (gR h) (Icc (m1 U' β R I) (m2 h)) ∧
      ContinuousOn (vR h) (Icc (m1 U' β R I) (m2 h)) ∧
      StrictMonoOn (vR h) (Icc (m1 U' β R I) (m2 h)) ∧
      StrictConcaveOn ℝ (Icc (m1 U' β R I) (m2 h)) (vR h) ∧
      (∀ x ∈ Ioo (m1 U' β R I) (m2 h), HasDerivAt (vR h) (U' (I + x - gR h x / R)) x) ∧
      ContinuousOn (fun x => U' (I + x - gR h x / R)) (Ioo (m1 U' β R I) (m2 h)) := by
  have hm1 := h.m1_pos
  have hsub : Icc (m1 U' β R I) (m2 h) ⊆ Ici 0 := fun x hx => mem_Ici.2 (hm1.le.trans hx.1)
  refine ⟨?_, h.continuousOn_gR.mono hsub, h.gR_strictMono.mono fun x hx => hx.1,
    h.continuousOn_vR.mono hsub, h.vR_strictMono.mono hsub,
    h.vR_strictConcave.subset hsub (convex_Icc _ _), fun x hx => ?_,
    h.continuousOn_vR'.mono fun x hx => mem_Ici.2 (hm1.le.trans hx.1.le)⟩
  · have := h.hfun_strictMono (mem_Ici.2 le_rfl) (mem_Ici.2 hm1.le) hm1
    rwa [h.hfun_zero] at this
  · have := h.hasDerivAt_vR (hm1.trans hx.1)
    rwa [h.cR_eq (hm1.le.trans hx.1.le)] at this

/-- **Exercise 5.17e.** `v` and `v'` are continuous at `m₁`. -/
theorem ex_5_17e (h : CSHyp U U' β R I) :
    ContinuousAt (vR h) (m1 U' β R I) ∧ ContinuousAt (deriv (vR h)) (m1 U' β R I) := by
  have hm1 := h.m1_pos
  refine ⟨(h.hasDerivAt_vR hm1).continuousAt, ?_⟩
  have hev : (fun x => U' (cR h x)) =ᶠ[𝓝 (m1 U' β R I)] deriv (vR h) := by
    filter_upwards [lt_mem_nhds hm1] with x hx
    exact ((h.hasDerivAt_vR hx).deriv).symm
  exact ((h.continuousOn_marg _ (mem_Ici.2 hm1.le)).continuousAt (Ici_mem_nhds hm1)).congr hev

/-! ### Exercise 5.17f: the induction covers `ℝ₊` -/

/-- `m_n = Ξ((Rβ)ⁿU'(I))`: `m₀ = 0`, `m₁`, and `m_{n+1} = h(m_n)`. -/
noncomputable def mSeq (U' : ℝ → ℝ) (β R I : ℝ) (n : ℕ) : ℝ :=
  wealth U' β R I ((R * β) ^ n * U' I)

theorem CSHyp.mSeq_succ (h : CSHyp U U' β R I) (n : ℕ) :
    mSeq U' β R I (n + 1) = hfun h (mSeq U' β R I n) := by
  have hU := h.U'_pos h.hI
  have hp : 0 < (R * β) ^ n * U' I := mul_pos (pow_pos h.rho_pos n) hU
  have hpI : (R * β) ^ n * U' I ≤ U' I :=
    mul_le_of_le_one_left hU.le (pow_le_one₀ h.rho_pos.le h.hRβ.le)
  rw [mSeq, mSeq, hfun, h.cR_wealth hp, h.U'_cI hp hpI, pow_succ']
  ring_nf

theorem CSHyp.mSeq_strictMono (h : CSHyp U U' β R I) : StrictMono (mSeq U' β R I) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hU := h.U'_pos h.hI
  have hρn := pow_pos h.rho_pos n
  have hlt : (R * β) ^ (n + 1) * U' I < (R * β) ^ n * U' I := by
    rw [pow_succ]
    have : (R * β) ^ n * (R * β) < (R * β) ^ n := mul_lt_of_lt_one_right hρn h.hRβ
    exact mul_lt_mul_of_pos_right this hU
  refine h.wealth_strictAnti (mul_pos (pow_pos h.rho_pos _) hU) hlt ?_
  refine lt_of_lt_of_le hlt (mul_le_of_le_one_left hU.le (pow_le_one₀ h.rho_pos.le h.hRβ.le))

theorem CSHyp.tendsto_mSeq (h : CSHyp U U' β R I) :
    Tendsto (mSeq U' β R I) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun B => ?_
  have hU := h.U'_pos h.hI
  have hc : 0 < I + max B 0 := by linarith [h.hI, le_max_right B 0]
  have hUc := h.U'_pos hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hUc hU) h.hRβ
  refine ⟨n, fun m hm => ?_⟩
  have hp : 0 < (R * β) ^ n * U' I := mul_pos (pow_pos h.rho_pos n) hU
  have h1 : I + max B 0 ≤ cI U' I ((R * β) ^ n * U' I) :=
    h.le_cI hp (by rwa [lt_div_iff₀ hU] at hn)
  have h2 := h.wealth_ge hp
  have h3 := h.mSeq_strictMono.monotone hm
  simp only [mSeq] at h3 ⊢
  linarith [le_max_left B 0]

/-- **Exercise 5.17f.** The intervals `(m_n, m_{n+1}]` cover `ℝ₊` (`m₀ = 0`, `m_n ↑ ∞`), and on
all of `ℝ₊`: `g` is continuous, zero on `[0, m₁]` and strictly increasing on `[m₁, ∞)`; `h` is
continuous and strictly increasing; `v` is continuous, strictly increasing and strictly concave,
and continuously differentiable with `v'(x) = U'(I + x − g(x)/R)` (one-sided at `0`). -/
theorem ex_5_17f (h : CSHyp U U' β R I) :
    (mSeq U' β R I 0 = 0 ∧ mSeq U' β R I 1 = m1 U' β R I ∧
      (∀ n, mSeq U' β R I (n + 1) = hfun h (mSeq U' β R I n)) ∧ StrictMono (mSeq U' β R I) ∧
      Tendsto (mSeq U' β R I) atTop atTop) ∧
    (ContinuousOn (gR h) (Ici 0) ∧ (∀ x ∈ Icc 0 (m1 U' β R I), gR h x = 0) ∧
      StrictMonoOn (gR h) (Ici (m1 U' β R I))) ∧
    (ContinuousOn (hfun h) (Ici 0) ∧ StrictMonoOn (hfun h) (Ici 0)) ∧
    (ContinuousOn (vR h) (Ici 0) ∧ StrictMonoOn (vR h) (Ici 0) ∧
      StrictConcaveOn ℝ (Ici 0) (vR h) ∧
      (∀ x, 0 ≤ x → HasDerivWithinAt (vR h) (U' (I + x - gR h x / R)) (Ici 0) x) ∧
      ContinuousOn (fun x => U' (I + x - gR h x / R)) (Ici 0)) := by
  refine ⟨⟨?_, ?_, h.mSeq_succ, h.mSeq_strictMono, h.tendsto_mSeq⟩,
    ⟨h.continuousOn_gR, fun x hx => h.gR_eq_zero hx.1 hx.2, h.gR_strictMono⟩,
    ⟨h.continuousOn_hfun, h.hfun_strictMono⟩,
    ⟨h.continuousOn_vR, h.vR_strictMono, h.vR_strictConcave, fun x hx => ?_,
      h.continuousOn_vR'⟩⟩
  · rw [mSeq, pow_zero, one_mul, h.wealth_of_ge le_rfl]
  · rw [mSeq, pow_one, h.wealth_rhoU]
  · have := h.hasDerivWithinAt_vR hx
    rwa [h.cR_eq hx] at this

/-! ### Exercise 5.17g: `v` solves (1) and `v = v*` -/

/-- `v(x) = U(c₀(x)) + βv(g(x))`. -/
theorem CSHyp.vR_attained (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    vR h x = U (I + x - gR h x / R) + β * vR h (gR h x) := by
  obtain ⟨hμ, -, -⟩ := h.muOf_spec hx
  have hμρ : 0 < muOf h x / (R * β) := div_pos hμ h.rho_pos
  rw [← h.cR_eq hx, h.gR_def, h.vR_wealth hμρ, vR, valμ, valμ,
    (h.summable_val hμ).tsum_eq_zero_add, pow_zero, one_mul, consμ_zero, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun t => ?_
  have := consμ_tail (U' := U') (β := β) (R := R) (I := I) (muOf h x) 1 t
  rw [pow_one] at this
  rw [this, pow_succ]
  ring

/-- **Exercise 5.17g.** `v = v*`, and `v` satisfies (1): `v(x) ≥ U(I + x − y/R) + βv(y)` for
every `y ∈ [0, (I + x)R]`, with equality at `y = g(x) ∈ [0, (I + x)R]`. -/
theorem ex_5_17g (h : CSHyp U U' β R I) :
    (∀ x (hx : 0 ≤ x), vstar (csΓ R I) (csF U R I) β ⟨x, hx⟩ = (vR h x : EReal)) ∧
      ∀ x, 0 ≤ x →
        (∀ y, 0 ≤ y → y ≤ (I + x) * R → U (I + x - y / R) + β * vR h y ≤ vR h x) ∧
        0 ≤ gR h x ∧ gR h x ≤ (I + x) * R ∧
        vR h x = U (I + x - gR h x / R) + β * vR h (gR h x) := by
  refine ⟨fun x hx => h.vstar_wealth hx, fun x hx => ⟨fun y hy hyx => ?_, h.gR_nonneg hx, ?_,
    h.vR_attained hx⟩⟩
  · have hFE := theorem_4_2 h.hβ0.le h.assumption41 h.assumption42 ⟨x, hx⟩
    have hle := le_biSup (fun y' : CSWealth => ((csF U R I ⟨x, hx⟩ y' : ℝ) : EReal) +
      (β : EReal) * vstar (csΓ R I) (csF U R I) β y') (show (⟨y, hy⟩ : CSWealth) ∈ csΓ R I ⟨x, hx⟩
        from hyx)
    rw [← hFE, h.vstar_wealth hx, h.vstar_wealth hy] at hle
    have hc : 0 ≤ I + x - y / R := by
      have := (div_le_iff₀ h.hR).2 hyx
      linarith
    have hF : csF U R I ⟨x, hx⟩ ⟨y, hy⟩ = U (I + x - y / R) := by
      simp only [csF]
      rw [max_eq_left hc]
    rw [hF, ← EReal.coe_mul, ← EReal.coe_add] at hle
    exact EReal.coe_le_coe_iff.1 hle
  · rw [h.gR_eq hx]
    have := h.cR_pos hx
    nlinarith [h.hR]

/-! ### Exercise 5.17h: the optimal plan -/

theorem CSHyp.gR_planμ (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    gR h (planμ U' β R I μ t) = planμ U' β R I μ (t + 1) := by
  rw [planμ, h.gR_wealth (div_pos hμ (pow_pos h.rho_pos t)), planμ, div_pow_succ]

/-- **Exercise 5.17h.** From any `x₀ ≥ 0`, a feasible plan is optimal if and only if it follows
`x_{t+1} = g(x_t)`; so that plan is the unique optimal plan. -/
theorem ex_5_17h_plan (h : CSHyp U U' β R I) (x₀ : CSWealth) {xs : ℕ → CSWealth}
    (hxs : xs ∈ Feasible (csΓ R I) x₀) :
    total (csF U R I) β xs = vstar (csΓ R I) (csF U R I) β x₀ ↔
      ∀ t, (xs (t + 1)).1 = gR h (xs t).1 := by
  obtain ⟨hμ, -, hw⟩ := h.muOf_spec x₀.2
  have hx₀ : x₀ = wealthN h hμ := Subtype.ext hw.symm
  have hxs' : xs ∈ Feasible (csΓ R I) (wealthN h hμ) := hx₀ ▸ hxs
  rw [show vstar (csΓ R I) (csF U R I) β x₀ = vstar (csΓ R I) (csF U R I) β (wealthN h hμ) from
    congrArg _ hx₀, h.optimal_iff hμ hxs']
  constructor
  · rintro rfl t
    exact (h.gR_planμ hμ t).symm
  · intro hg
    funext t
    refine Subtype.ext ?_
    induction t with
    | zero => rw [hxs.1]; exact hw.symm.trans (planμ_zero _).symm
    | succ t ih => rw [hg t, ih]; exact h.gR_planμ hμ t

/-- **Exercise 5.17h (corrected).** For `0 ≤ x < x'`: `0 ≤ g(x') − g(x) < R(x' − x)`, with
equality on the left only if `g(x) = g(x') = 0`. The book's sharper `g(x') − g(x) < x' − x` holds
when `R ≤ 1` (`ex_5_17h_slope_le_one`), but can fail when `R > 1`. -/
theorem ex_5_17h_slope (h : CSHyp U U' β R I) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x < x') :
    0 ≤ gR h x' - gR h x ∧ gR h x' - gR h x < R * (x' - x) ∧
      (gR h x' = gR h x → gR h x = 0 ∧ gR h x' = 0) := by
  have hx' : 0 ≤ x' := hx.trans hxx'.le
  refine ⟨sub_nonneg.2 (h.gR_mono hx hxx'.le), ?_, fun heq => ?_⟩
  · rw [h.gR_eq hx, h.gR_eq hx']
    have := h.cR_strictMono (mem_Ici.2 hx) (mem_Ici.2 hx') hxx'
    nlinarith [h.hR]
  · have h0 : gR h x' = 0 := by
      refine le_antisymm (not_lt.1 fun hpos => ?_) (h.gR_nonneg hx')
      rw [h.gR_def] at hpos
      have := h.wealth_strictAnti (div_pos (h.muOf_spec hx').1 h.rho_pos)
        (div_lt_div_of_pos_right (h.muOf_lt hx hxx').1 h.rho_pos) (h.lt_of_wealth_pos hpos)
      rw [← h.gR_def, ← h.gR_def] at this
      linarith
    exact ⟨heq ▸ h0, h0⟩

theorem ex_5_17h_slope_le_one (h : CSHyp U U' β R I) (hR1 : R ≤ 1) {x x' : ℝ} (hx : 0 ≤ x)
    (hxx' : x < x') : gR h x' - gR h x < x' - x := by
  have := (ex_5_17h_slope h hx hxx').2.1
  nlinarith

end StokeyLucasPrescott.DeterministicApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A consumption–savings problem: three corrections

SLP §5.17.

* **`m₁` need not exist** (`ex_5_17b_m1_fails`). Take `U(c) = c − e^{−c}`, which is `C¹`,
  strictly increasing and strictly concave, with `β = 1/2`, `R = 1`, `I = 1`. Then
  `U'(c) = 1 + e^{−c} > 1 > RβU'(I)`, so `U'(I + m₁) = RβU'(I)` has no solution. (Here consuming
  all wealth at once is optimal from every `x`.) Some condition such as `U'(c) → 0`, which
  `CSHyp` assumes, is needed.
* **The hint to 5.17g fails when `R < 1`** (`ex_5_17g_hint_fails`). With `W = RI/(R − 1) < 0`,
  `x_n ≤ Rⁿ(x₀ + W)` is false already at `n = 1`; at `R = 1`, `W` is undefined. The proof of
  `v = v*` in `ConsumptionSavings` does not use the hint.
* **`g(x') − g(x) < x' − x` fails when `R > 1`** (`ex_5_17h_counterexample`). Take `R = 2`,
  `β = 9/20`, `I = 1`. Let `U'` be almost flat on `[0, 2]`, at `1 − (c − 1)/100`, then falling
  steeply as `0.099/(c − 1.9)`. A consumer who will consume `c₁ ∈ (1, 2)` next period chooses
  `c₀` with `U'(c₀) = RβU'(c₁)`, which barely moves with `c₁`. So nearly all of an extra unit of
  wealth is saved, and saving grows at rate about `R = 2`. Concretely, at
  `x = 1 + 55/499 < x' = 11/10 + 55/498`, `g(x) = 1/5` and `g(x') = 2/5`. The correct bound is
  `g(x') − g(x) < R(x' − x)` (`ex_5_17h_slope`), and the book's bound holds for `R ≤ 1`
  (`ex_5_17h_slope_le_one`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

/-! ### `m₁` need not exist -/

theorem hasDerivAt_cexp (c : ℝ) :
    HasDerivAt (fun c : ℝ => c - Real.exp (-c)) (1 + Real.exp (-c)) c := by
  convert (hasDerivAt_id' c).sub ((hasDerivAt_neg c).exp) using 1
  ring

/-- **Exercise 5.17b (correction).** `U(c) = c − e^{−c}` is `C¹`, strictly increasing and
strictly concave on `ℝ₊`, but with `β = 1/2`, `R = 1`, `I = 1` no `m ≥ 0` solves
`U'(I + m) = RβU'(I)`. -/
theorem ex_5_17b_m1_fails :
    (∀ c, HasDerivAt (fun c : ℝ => c - Real.exp (-c)) (1 + Real.exp (-c)) c) ∧
      Continuous (fun c : ℝ => 1 + Real.exp (-c)) ∧
      StrictMonoOn (fun c : ℝ => c - Real.exp (-c)) (Ici 0) ∧
      StrictConcaveOn ℝ (Ici 0) (fun c : ℝ => c - Real.exp (-c)) ∧
      ¬ ∃ m : ℝ, 0 ≤ m ∧
        1 + Real.exp (-(1 + m)) = 1 * (1 / 2) * (1 + Real.exp (-1)) := by
  have hcont : Continuous (fun c : ℝ => c - Real.exp (-c)) :=
    continuous_iff_continuousAt.2 fun c => (hasDerivAt_cexp c).continuousAt
  have hderiv : ∀ c, deriv (fun c : ℝ => c - Real.exp (-c)) c = 1 + Real.exp (-c) :=
    fun c => (hasDerivAt_cexp c).deriv
  refine ⟨hasDerivAt_cexp, by fun_prop, strictMonoOn_of_deriv_pos (convex_Ici 0)
    hcont.continuousOn fun c _ => by rw [hderiv]; positivity, ?_, ?_⟩
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hcont.continuousOn ?_
    intro a _ b _ hab
    rw [hderiv, hderiv]
    have := Real.exp_lt_exp.2 (neg_lt_neg hab)
    linarith
  · rintro ⟨m, -, hm⟩
    have h1 : Real.exp (-1) < 1 := by
      have := Real.exp_lt_exp.2 (by norm_num : (-1 : ℝ) < 0)
      rwa [Real.exp_zero] at this
    have h2 := Real.exp_pos (-(1 + m))
    linarith

/-! ### The hint to 5.17g -/

/-- **Exercise 5.17g (correction to the hint).** With `R = 1/2`, `I = 1` and `x₀ = 0`, saving
all income, `x₁ = RI = 1/2`, is feasible, but `R(x₀ + W) = −1/2` with `W = RI/(R − 1)`. -/
theorem ex_5_17g_hint_fails :
    (1 / 2 : ℝ) ≤ (1 + 0) * (1 / 2) ∧
      (1 / 2 : ℝ) ^ 1 * (0 + 1 / 2 * 1 / (1 / 2 - 1)) < 1 / 2 := by
  norm_num

/-! ### `g(x') − g(x) < x' − x` fails for `R > 1` -/

/-- Utility of the counterexample: `c − (c − 1)²/200` on `(−∞, 2]`, then
`399/200 + 0.099 ln(10(c − 1.9))`. -/
noncomputable def ceU (c : ℝ) : ℝ :=
  if c ≤ 2 then c - (c - 1) ^ 2 / 200 else 399 / 200 + 99 / 1000 * Real.log ((c - 19 / 10) * 10)

/-- Its marginal utility: `1 − (c − 1)/100` on `(−∞, 2]`, then `0.099/(c − 1.9)`. -/
noncomputable def ceU' (c : ℝ) : ℝ := if c ≤ 2 then 1 - (c - 1) / 100 else 99 / 1000 / (c - 19 / 10)

theorem hasDerivAt_ce1 (c : ℝ) :
    HasDerivAt (fun c : ℝ => c - (c - 1) ^ 2 / 200) (1 - (c - 1) / 100) c := by
  convert (hasDerivAt_id' c).sub ((((hasDerivAt_id' c).sub_const 1).pow 2).div_const 200)
    using 1
  norm_num
  ring

theorem hasDerivAt_ce2 {c : ℝ} (hc : 19 / 10 < c) :
    HasDerivAt (fun c : ℝ => 399 / 200 + 99 / 1000 * Real.log ((c - 19 / 10) * 10))
      (99 / 1000 / (c - 19 / 10)) c := by
  have hne : (c - 19 / 10) * 10 ≠ 0 := by
    have : 0 < c - 19 / 10 := by linarith
    positivity
  have hlog := (((hasDerivAt_id' c).sub_const (19 / 10)).mul_const 10).log hne
  convert (hlog.const_mul (99 / 1000)).const_add (399 / 200) using 1
  have : c - 19 / 10 ≠ 0 := by linarith
  field_simp

theorem ceU'_low {c : ℝ} (hc : c ≤ 2) : ceU' c = 1 - (c - 1) / 100 := by
  simp only [ceU', hc, ↓reduceIte]

theorem ceU'_high {c : ℝ} (hc : 2 < c) : ceU' c = 99 / 1000 / (c - 19 / 10) := by
  simp only [ceU', not_le.2 hc, ↓reduceIte]

theorem hasDerivAt_ceU (c : ℝ) : HasDerivAt ceU (ceU' c) c := by
  rcases lt_trichotomy c 2 with hlt | rfl | hgt
  · rw [ceU'_low hlt.le]
    refine (hasDerivAt_ce1 c).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hlt] with y hy
    simp only [ceU, (mem_Iio.1 hy).le, ↓reduceIte]
  · have hl : HasDerivWithinAt ceU (ceU' 2) (Iic 2) 2 := by
      rw [ceU'_low le_rfl]
      exact (hasDerivAt_ce1 2).hasDerivWithinAt.congr
        (fun y hy => by simp only [ceU, mem_Iic.1 hy, ↓reduceIte])
        (by simp only [ceU, le_refl, ↓reduceIte])
    have hr : HasDerivWithinAt ceU (ceU' 2) (Ici 2) 2 := by
      have h2 : ceU' 2 = 99 / 1000 / ((2 : ℝ) - 19 / 10) := by rw [ceU'_low le_rfl]; norm_num
      rw [h2]
      refine (hasDerivAt_ce2 (by norm_num)).hasDerivWithinAt.congr (fun y hy => ?_) ?_
      · rcases eq_or_lt_of_le (mem_Ici.1 hy) with rfl | hlt
        · simp only [ceU, le_refl, ↓reduceIte]; norm_num
        · simp only [ceU, not_le.2 hlt, ↓reduceIte]
      · simp only [ceU, le_refl, ↓reduceIte]; norm_num
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [ceU'_high hgt]
    refine (hasDerivAt_ce2 (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    simp only [ceU, not_le.2 (mem_Ioi.1 hy), ↓reduceIte]

theorem ceU'_strictAnti : StrictAnti ceU' := by
  intro a b hab
  rcases le_or_gt b 2 with hb | hb
  · rw [ceU'_low hb, ceU'_low (hab.le.trans hb)]
    linarith
  · rw [ceU'_high hb]
    have hb' : 0 < b - 19 / 10 := by linarith
    rcases le_or_gt a 2 with ha | ha
    · rw [ceU'_low ha, div_lt_iff₀ hb']
      nlinarith
    · rw [ceU'_high ha]
      exact div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

theorem ceU'_pos (c : ℝ) : 0 < ceU' c := by
  rcases le_or_gt c 2 with h2 | h2
  · rw [ceU'_low h2]; linarith
  · rw [ceU'_high h2]; exact div_pos (by norm_num) (by linarith)

theorem continuousAt_ceU' (c : ℝ) : ContinuousAt ceU' c := by
  have hlin : Continuous fun c : ℝ => 1 - (c - 1) / 100 := by fun_prop
  rcases lt_trichotomy c 2 with hlt | rfl | hgt
  · refine hlin.continuousAt.congr ?_
    filter_upwards [Iio_mem_nhds hlt] with y hy
    exact (ceU'_low hy.le).symm
  · refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · exact hlin.continuousAt.continuousWithinAt.congr (fun y hy => ceU'_low hy) (ceU'_low le_rfl)
    · have ht : ContinuousAt (fun c : ℝ => 99 / 1000 / (c - 19 / 10)) 2 :=
        continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)
      refine ht.continuousWithinAt.congr (fun y hy => ?_) ?_
      · rcases eq_or_lt_of_le (mem_Ici.1 hy) with rfl | hlt
        · rw [ceU'_low le_rfl]; norm_num
        · exact ceU'_high hlt
      · rw [ceU'_low le_rfl]; norm_num
  · have ht : ContinuousAt (fun c : ℝ => 99 / 1000 / (c - 19 / 10)) c :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by
        have : (19 : ℝ) / 10 < c := by linarith
        exact sub_ne_zero.2 this.ne')
    refine ht.congr ?_
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    exact (ceU'_high hy).symm

/-- The counterexample satisfies the hypotheses of §5.17, with `R = 2 > 1`. -/
theorem ceHyp : CSHyp ceU ceU' (9 / 20) 2 1 := by
  have hcont : Continuous ceU :=
    continuous_iff_continuousAt.2 fun c => (hasDerivAt_ceU c).continuousAt
  have hderiv : ∀ c, deriv ceU c = ceU' c := fun c => (hasDerivAt_ceU c).deriv
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, hcont.continuousOn,
    fun c _ => hasDerivAt_ceU c, fun c _ => (continuousAt_ceU' c).continuousWithinAt,
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn fun c hc => ?_,
    StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hcont.continuousOn ?_, ?_⟩
  · rw [interior_Ici] at hc
    rw [hderiv]
    exact ceU'_pos c
  · intro a _ b _ hab
    rw [hderiv, hderiv]
    exact ceU'_strictAnti hab
  · have ht : Tendsto (fun c : ℝ => 99 / 1000 / (c - 19 / 10)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_atTop_add_const_right atTop (-(19 / 10)) tendsto_id).congr fun c => by
          simp [sub_eq_add_neg])
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 2] with c hc
    exact (ceU'_high hc).symm

/-- **Exercise 5.17h (correction).** In the counterexample (`R = 2`),
`x = 1 + 55/499 < x' = 11/10 + 55/498` but
`g(x') − g(x) = 1/5 > x' − x = 1/10 + 55/(498 · 499)`. -/
theorem ex_5_17h_counterexample :
    (1 : ℝ) < 2 ∧ ∃ x x' : ℝ, 0 ≤ x ∧ x < x' ∧ x' - x < gR ceHyp x' - gR ceHyp x := by
  have h := ceHyp
  have hU1 : ceU' 1 = 1 := by rw [ceU'_low (by norm_num)]; norm_num
  -- `g(Ξ(RβU'(1 + y))) = y` and `Ξ(RβU'(1 + y)) = cI(RβU'(1 + y)) − 1 + y/2`, for `y = 1/5, 2/5`
  have key : ∀ y c : ℝ, 0 < y → y ≤ 1 → 2 < c → ceU' c = 2 * (9 / 20) * ceU' (1 + y) →
      gR ceHyp (wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + y))) = y ∧
        wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + y)) = c - 1 + y / 2 := by
    intro y c hy hy1 hc hcU
    have hp : 0 < ceU' (1 + y) := ceU'_pos _
    have hρp : 0 < 2 * (9 / 20) * ceU' (1 + y) := by positivity
    have hpy : ceU' (1 + y) = 1 - y / 100 := by rw [ceU'_low (by linarith)]; ring
    have hw : wealth ceU' (9 / 20) 2 1 (ceU' (1 + y)) = y := by
      rw [h.wealth_shift hp, h.cI_U' (by linarith), h.wealth_of_ge (by
        rw [hU1, hpy, le_div_iff₀ (by norm_num)]; linarith)]
      ring
    refine ⟨?_, ?_⟩
    · rw [h.gR_wealth hρp, mul_div_cancel_left₀ _ (by norm_num), hw]
    · rw [h.wealth_shift hρp, mul_div_cancel_left₀ _ (by norm_num), hw, ← hcU,
        h.cI_U' (by linarith)]
      ring
  have hc1 : (2 : ℝ) < 19 / 10 + 55 / 499 := by norm_num
  have hc2 : (2 : ℝ) < 19 / 10 + 55 / 498 := by norm_num
  obtain ⟨hg1, hx1⟩ := key (1 / 5) (19 / 10 + 55 / 499) (by norm_num) (by norm_num) hc1 (by
    rw [ceU'_high hc1, ceU'_low (by norm_num)]; norm_num)
  obtain ⟨hg2, hx2⟩ := key (2 / 5) (19 / 10 + 55 / 498) (by norm_num) (by norm_num) hc2 (by
    rw [ceU'_high hc2, ceU'_low (by norm_num)]; norm_num)
  refine ⟨by norm_num, wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + 1 / 5)),
    wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + 2 / 5)), ?_, ?_, ?_⟩
  · rw [hx1]; norm_num
  · rw [hx1, hx2]; norm_num
  · rw [hg1, hg2, hx1, hx2]; norm_num

/-- **Exercise 5.17h (correction).** The book's bound `g(x') − g(x) < x' − x` does not hold for
every model satisfying its hypotheses. -/
theorem ex_5_17h_book_bound_fails :
    ¬ ∀ x x' : ℝ, 0 ≤ x → x < x' → gR ceHyp x' - gR ceHyp x < x' - x := by
  intro hall
  obtain ⟨-, x, x', hx, hxx', hlt⟩ := ex_5_17h_counterexample
  exact lt_asymm (hall x x' hx hxx') hlt

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
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.h43
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.cont
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.w_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.w_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.bdd
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.ρ_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.growth
#print axioms StokeyLucasPrescott.DeterministicApplications.SolvesFE
#print axioms StokeyLucasPrescott.DeterministicApplications.wobj
#print axioms StokeyLucasPrescott.DeterministicApplications.WeightedHyp.ρ_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousOn_wobj
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_wobj_le
#print axioms StokeyLucasPrescott.DeterministicApplications.bound_wmaxValue
#print axioms StokeyLucasPrescott.DeterministicApplications.wbellman
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_wbellman_argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.wbellman_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.solvesFE_iff
#print axioms StokeyLucasPrescott.DeterministicApplications.weighted_exists_unique
#print axioms StokeyLucasPrescott.DeterministicApplications.human_assumption43
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.δ_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.δ_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.lam_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.discount
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.φ_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.φ_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.φ_le_one
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.f_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.f_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.f_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.U_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.U_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.HCGrowthHyp.lin
#print axioms StokeyLucasPrescott.DeterministicApplications.hcF
#print axioms StokeyLucasPrescott.DeterministicApplications.hcW
#print axioms StokeyLucasPrescott.DeterministicApplications.concave_linear_bound
#print axioms StokeyLucasPrescott.DeterministicApplications.hc_weighted
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_8a
#print axioms StokeyLucasPrescott.DeterministicApplications.rpow_le_one_add
#print axioms StokeyLucasPrescott.DeterministicApplications.hcObj
#print axioms StokeyLucasPrescott.DeterministicApplications.hcPhi
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_8b
#print axioms StokeyLucasPrescott.DeterministicApplications.investG
#print axioms StokeyLucasPrescott.DeterministicApplications.investH
#print axioms StokeyLucasPrescott.DeterministicApplications.invest_fe
#print axioms StokeyLucasPrescott.DeterministicApplications.invest_telescope
#print axioms StokeyLucasPrescott.DeterministicApplications.invest_partialSum_le
#print axioms StokeyLucasPrescott.DeterministicApplications.invest_plan_tendsto
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_max_sublinear
#print axioms StokeyLucasPrescott.DeterministicApplications.invest_euler
#print axioms StokeyLucasPrescott.DeterministicApplications.clamp_maximizes
#print axioms StokeyLucasPrescott.DeterministicApplications.bounded_policy
#print axioms StokeyLucasPrescott.DeterministicApplications.intervalΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.intervalΓ_assumption43
#print axioms StokeyLucasPrescott.DeterministicApplications.bellman_concave_of_concaveF
#print axioms StokeyLucasPrescott.DeterministicApplications.fixed_concave_of_concaveF
#print axioms StokeyLucasPrescott.DeterministicApplications.concaveOn_liftR_of_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_bound_Icc_prod
#print axioms StokeyLucasPrescott.DeterministicApplications.investF
#print axioms StokeyLucasPrescott.DeterministicApplications.boundedΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.bounded_assumption43
#print axioms StokeyLucasPrescott.DeterministicApplications.bounded_assumption44
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9a_bounds
#print axioms StokeyLucasPrescott.DeterministicApplications.adjF
#print axioms StokeyLucasPrescott.DeterministicApplications.fullΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.full_assumption43
#print axioms StokeyLucasPrescott.DeterministicApplications.mem_fullΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.adj_assumption44
#print axioms StokeyLucasPrescott.DeterministicApplications.adj_a47
#print axioms StokeyLucasPrescott.DeterministicApplications.full_a48
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.p_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.δ_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.δ_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.K_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.f_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.f_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.c_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.c_convex
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.h43
#print axioms StokeyLucasPrescott.DeterministicApplications.AdjHyp.h44
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9b_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9b_slope
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9b_envelope
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9b_foc
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9b_euler
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_9b_steady
#print axioms StokeyLucasPrescott.DeterministicApplications.profitPi
#print axioms StokeyLucasPrescott.DeterministicApplications.profitPi_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.labor_demand_exists
#print axioms StokeyLucasPrescott.DeterministicApplications.labor_demand_unique
#print axioms StokeyLucasPrescott.DeterministicApplications.profitPi_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.profitPi_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.profitPi_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.profitPi_strictConcave
#print axioms StokeyLucasPrescott.DeterministicApplications.profitPi_deriv
#print axioms StokeyLucasPrescott.DeterministicApplications.CapStock
#print axioms StokeyLucasPrescott.DeterministicApplications.isCone_Ici
#print axioms StokeyLucasPrescott.DeterministicApplications.crsΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.crsH
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.δ_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.δ_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.α_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.discount
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.p_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.q_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.F_cont
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.F_hom
#print axioms StokeyLucasPrescott.DeterministicApplications.CRSInvHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.crs_assumption410
#print axioms StokeyLucasPrescott.DeterministicApplications.crs_F_bound
#print axioms StokeyLucasPrescott.DeterministicApplications.crs_assumption411
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_10a
#print axioms StokeyLucasPrescott.DeterministicApplications.satisfiesFE_of_solvesFE
#print axioms StokeyLucasPrescott.DeterministicApplications.solvesFE_rescale
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_10b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_10c
#print axioms StokeyLucasPrescott.DeterministicApplications.seqSet
#print axioms StokeyLucasPrescott.DeterministicApplications.Seq
#print axioms StokeyLucasPrescott.DeterministicApplications.convex_seqSet
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_shiftSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_head
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_apply_le_norm
#print axioms StokeyLucasPrescott.DeterministicApplications.zeroSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.trunc
#print axioms StokeyLucasPrescott.DeterministicApplications.trunc_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.head_trunc
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_trunc_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_trunc_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.opTU
#print axioms StokeyLucasPrescott.DeterministicApplications.opTU_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11c
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11a
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11b_complete
#print axioms StokeyLucasPrescott.DeterministicApplications.eventuallyZero
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11b_counterexample
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp.cont
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp.zero
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp.bdd
#print axioms StokeyLucasPrescott.DeterministicApplications.AggHyp.lip
#print axioms StokeyLucasPrescott.DeterministicApplications.opTW
#print axioms StokeyLucasPrescott.DeterministicApplications.opTW_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.opTW_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11d
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11d_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.monotoneOn_of_concave_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11d_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.bump
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_bump_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_bump_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.head_bump_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.head_bump_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_11e
#print axioms StokeyLucasPrescott.DeterministicApplications.Wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.spend
#print axioms StokeyLucasPrescott.DeterministicApplications.budgetΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.nextWealth
#print axioms StokeyLucasPrescott.DeterministicApplications.vext
#print axioms StokeyLucasPrescott.DeterministicApplications.vext_of_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_vext
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_vext_le
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_spend
#print axioms StokeyLucasPrescott.DeterministicApplications.spend_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.le_div_of_spend
#print axioms StokeyLucasPrescott.DeterministicApplications.norm_le_of_budget
#print axioms StokeyLucasPrescott.DeterministicApplications.budget_compact
#print axioms StokeyLucasPrescott.DeterministicApplications.zero_mem_budget
#print axioms StokeyLucasPrescott.DeterministicApplications.budget_lhc
#print axioms StokeyLucasPrescott.DeterministicApplications.budget_uhc
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.p_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.R_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.cont
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.bdd
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.lip
#print axioms StokeyLucasPrescott.DeterministicApplications.consObj
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_consObj
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_consObj_le
#print axioms StokeyLucasPrescott.DeterministicApplications.consMax_le
#print axioms StokeyLucasPrescott.DeterministicApplications.consT
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_consT_argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.consT_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12b_concave
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12b_demand
#print axioms StokeyLucasPrescott.DeterministicApplications.ConsHyp.smul
#print axioms StokeyLucasPrescott.DeterministicApplications.spend_smul
#print axioms StokeyLucasPrescott.DeterministicApplications.scaleW
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12b_homogeneous
#print axioms StokeyLucasPrescott.DeterministicApplications.spend_add_smul_single
#print axioms StokeyLucasPrescott.DeterministicApplications.concaveOn_vext
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12c_envelope
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12c_intratemporal
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12c_euler
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12d
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12d_not_aggregator
#print axioms StokeyLucasPrescott.DeterministicApplications.planCost
#print axioms StokeyLucasPrescott.DeterministicApplications.spend_le_bound
#print axioms StokeyLucasPrescott.DeterministicApplications.summable_planCost
#print axioms StokeyLucasPrescott.DeterministicApplications.planCost_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.planCost_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.Feasible5
#print axioms StokeyLucasPrescott.DeterministicApplications.feasible_head
#print axioms StokeyLucasPrescott.DeterministicApplications.feasible_shift
#print axioms StokeyLucasPrescott.DeterministicApplications.utility_le_value
#print axioms StokeyLucasPrescott.DeterministicApplications.consSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.consSeq_head
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_consSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.consPolicy
#print axioms StokeyLucasPrescott.DeterministicApplications.consPolicy_spec
#print axioms StokeyLucasPrescott.DeterministicApplications.policyNext
#print axioms StokeyLucasPrescott.DeterministicApplications.policyPlan
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_plan_near
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12a
#print axioms StokeyLucasPrescott.DeterministicApplications.wealthPath
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12a_optimal
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_12a_necessary
#print axioms StokeyLucasPrescott.DeterministicApplications.isLHC_of_approx
#print axioms StokeyLucasPrescott.DeterministicApplications.cst
#print axioms StokeyLucasPrescott.DeterministicApplications.cst_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.cst_le
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp.h1
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp.h2
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp.mono1
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp.mono2
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp.strict2c
#print axioms StokeyLucasPrescott.DeterministicApplications.ParetoHyp.strict2z
#print axioms StokeyLucasPrescott.DeterministicApplications.oneSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_one
#print axioms StokeyLucasPrescott.DeterministicApplications.utility_one
#print axioms StokeyLucasPrescott.DeterministicApplications.I2
#print axioms StokeyLucasPrescott.DeterministicApplications.paretoΦ
#print axioms StokeyLucasPrescott.DeterministicApplications.paretoObj
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_cst
#print axioms StokeyLucasPrescott.DeterministicApplications.pareto_top_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.pareto_compact
#print axioms StokeyLucasPrescott.DeterministicApplications.pareto_uhc
#print axioms StokeyLucasPrescott.DeterministicApplications.pareto_lhc
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_paretoObj
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_paretoObj_le
#print axioms StokeyLucasPrescott.DeterministicApplications.paretoT
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_paretoT_argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.paretoT_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_13a
#print axioms StokeyLucasPrescott.DeterministicApplications.oneMinus
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_oneMinus
#print axioms StokeyLucasPrescott.DeterministicApplications.head_oneMinus
#print axioms StokeyLucasPrescott.DeterministicApplications.head_eq_cst
#print axioms StokeyLucasPrescott.DeterministicApplications.utility_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.utility_range
#print axioms StokeyLucasPrescott.DeterministicApplications.oneMinus_le
#print axioms StokeyLucasPrescott.DeterministicApplications.pareto_le_value
#print axioms StokeyLucasPrescott.DeterministicApplications.paretoPol
#print axioms StokeyLucasPrescott.DeterministicApplications.paretoPlan
#print axioms StokeyLucasPrescott.DeterministicApplications.paretoPlan_le
#print axioms StokeyLucasPrescott.DeterministicApplications.shiftSeq_paretoPlan
#print axioms StokeyLucasPrescott.DeterministicApplications.head_paretoPlan
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_13b
#print axioms StokeyLucasPrescott.DeterministicApplications.Stock
#print axioms StokeyLucasPrescott.DeterministicApplications.sext
#print axioms StokeyLucasPrescott.DeterministicApplications.sext_of_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_sext
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_sext_le
#print axioms StokeyLucasPrescott.DeterministicApplications.leftover
#print axioms StokeyLucasPrescott.DeterministicApplications.orderVal
#print axioms StokeyLucasPrescott.DeterministicApplications.ordSup
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp.β_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp.β_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp.c₀_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp.c₁_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp.margin
#print axioms StokeyLucasPrescott.DeterministicApplications.InvHyp.p_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.orderVal_le
#print axioms StokeyLucasPrescott.DeterministicApplications.bddAbove_ordSup
#print axioms StokeyLucasPrescott.DeterministicApplications.horizon
#print axioms StokeyLucasPrescott.DeterministicApplications.horizon_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.orderVal_beyond
#print axioms StokeyLucasPrescott.DeterministicApplications.ordSup_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.invRHS
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_invRHS
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_invRHS_le
#print axioms StokeyLucasPrescott.DeterministicApplications.invT
#print axioms StokeyLucasPrescott.DeterministicApplications.invT_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.ordSup_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.ordSup_add_const
#print axioms StokeyLucasPrescott.DeterministicApplications.invT_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14a
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14a_policy
#print axioms StokeyLucasPrescott.DeterministicApplications.rn
#print axioms StokeyLucasPrescott.DeterministicApplications.Yn
#print axioms StokeyLucasPrescott.DeterministicApplications.one_sub_pow_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.Yn_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.tendsto_Yn
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14b
#print axioms StokeyLucasPrescott.DeterministicApplications.argmax_Yn_indep_p
#print axioms StokeyLucasPrescott.DeterministicApplications.argmax_Yn_mono_c0
#print axioms StokeyLucasPrescott.DeterministicApplications.pow_ratio_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.argmax_Yn_mono_beta
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14c
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp.inv
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp.N_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp.N_max
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp.Y_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.Aind
#print axioms StokeyLucasPrescott.DeterministicApplications.cellW
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp.A_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.SSHyp.A_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.cross_iff
#print axioms StokeyLucasPrescott.DeterministicApplications.cross_one
#print axioms StokeyLucasPrescott.DeterministicApplications.cross_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_cell
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_low
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_two
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_one_two
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_three_left
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_three_right
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_five
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_six
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_cellW
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousOn_wSS_cell
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousOn_wSS
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_bounds
#print axioms StokeyLucasPrescott.DeterministicApplications.cross_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_left_piece
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_right_piece
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_deriv_low
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_deriv_left
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_deriv_right
#print axioms StokeyLucasPrescott.DeterministicApplications.not_differentiableAt_of_kink
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_kink_one
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_kink_int
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_kink_A
#print axioms StokeyLucasPrescott.DeterministicApplications.phiSS
#print axioms StokeyLucasPrescott.DeterministicApplications.phi_cell_convex
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14e
#print axioms StokeyLucasPrescott.DeterministicApplications.wSS_int
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14f
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14g
#print axioms StokeyLucasPrescott.DeterministicApplications.key_ineq
#print axioms StokeyLucasPrescott.DeterministicApplications.wBCF
#print axioms StokeyLucasPrescott.DeterministicApplications.sext_wBCF
#print axioms StokeyLucasPrescott.DeterministicApplications.orderVal_wBCF
#print axioms StokeyLucasPrescott.DeterministicApplications.order_le
#print axioms StokeyLucasPrescott.DeterministicApplications.order_int
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14h
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14_value
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_14_policy
#print axioms StokeyLucasPrescott.DeterministicApplications.Srev
#print axioms StokeyLucasPrescott.DeterministicApplications.CTHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.CTHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.CTHyp.a_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CTHyp.p_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CTHyp.r_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CTHyp.c₀_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CTHyp.c₁_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.Srev_integral
#print axioms StokeyLucasPrescott.DeterministicApplications.Srev_add
#print axioms StokeyLucasPrescott.DeterministicApplications.exp_neg_lt_one
#print axioms StokeyLucasPrescott.DeterministicApplications.Gcyc
#print axioms StokeyLucasPrescott.DeterministicApplications.Gcyc_geometric
#print axioms StokeyLucasPrescott.DeterministicApplications.Gcyc_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.Gcyc_le
#print axioms StokeyLucasPrescott.DeterministicApplications.Ystar
#print axioms StokeyLucasPrescott.DeterministicApplications.bddAbove_Gcyc
#print axioms StokeyLucasPrescott.DeterministicApplications.Gcyc_le_Ystar
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousOn_Gcyc
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_15a
#print axioms StokeyLucasPrescott.DeterministicApplications.Ncyc
#print axioms StokeyLucasPrescott.DeterministicApplications.Ncyc_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.hasDerivAt_hcyc
#print axioms StokeyLucasPrescott.DeterministicApplications.Gcyc_argmax_unique
#print axioms StokeyLucasPrescott.DeterministicApplications.wCT
#print axioms StokeyLucasPrescott.DeterministicApplications.Vval
#print axioms StokeyLucasPrescott.DeterministicApplications.cycle_le
#print axioms StokeyLucasPrescott.DeterministicApplications.Vval_le
#print axioms StokeyLucasPrescott.DeterministicApplications.Vval_attain
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_15b
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_15b_unique
#print axioms StokeyLucasPrescott.DeterministicApplications.Dtri
#print axioms StokeyLucasPrescott.DeterministicApplications.DPt
#print axioms StokeyLucasPrescott.DeterministicApplications.Prob
#print axioms StokeyLucasPrescott.DeterministicApplications.convex_Dtri
#print axioms StokeyLucasPrescott.DeterministicApplications.priceQ
#print axioms StokeyLucasPrescott.DeterministicApplications.priceQ_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.leftPt
#print axioms StokeyLucasPrescott.DeterministicApplications.rightPt
#print axioms StokeyLucasPrescott.DeterministicApplications.sellerObj
#print axioms StokeyLucasPrescott.DeterministicApplications.sellerObj_apply
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_priceQ
#print axioms StokeyLucasPrescott.DeterministicApplications.continuous_sellerObj
#print axioms StokeyLucasPrescott.DeterministicApplications.prob_lhc
#print axioms StokeyLucasPrescott.DeterministicApplications.prob_uhc
#print axioms StokeyLucasPrescott.DeterministicApplications.abs_sellerObj_le
#print axioms StokeyLucasPrescott.DeterministicApplications.sellerT
#print axioms StokeyLucasPrescott.DeterministicApplications.exists_sellerT_argmax
#print axioms StokeyLucasPrescott.DeterministicApplications.sellerT_contraction
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_16a
#print axioms StokeyLucasPrescott.DeterministicApplications.scalePt
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_16a_hom
#print axioms StokeyLucasPrescott.DeterministicApplications.topPt
#print axioms StokeyLucasPrescott.DeterministicApplications.diagPt
#print axioms StokeyLucasPrescott.DeterministicApplications.wSel
#print axioms StokeyLucasPrescott.DeterministicApplications.fe_seller
#print axioms StokeyLucasPrescott.DeterministicApplications.v_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_16b_one
#print axioms StokeyLucasPrescott.DeterministicApplications.v_eq_w
#print axioms StokeyLucasPrescott.DeterministicApplications.IsConvexD
#print axioms StokeyLucasPrescott.DeterministicApplications.v_convex
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_16b_convex
#print axioms StokeyLucasPrescott.DeterministicApplications.v_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_16b_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_16c
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.mk
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hβ0
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hβ1
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hRβ
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hI
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hUc
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hUd
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hU'c
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hUm
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hUcc
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hlim
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.rho_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.super_le
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.super_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.U'_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.U'_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.U'_le
#print axioms StokeyLucasPrescott.DeterministicApplications.cI
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_nonempty
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_mem
#print axioms StokeyLucasPrescott.DeterministicApplications.cI_le
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_of_le
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_U'
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_anti
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_gt
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cI_strictAnti
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.le_cI
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousAt_cI
#print axioms StokeyLucasPrescott.DeterministicApplications.wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.exists_K
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_term_eq_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_eq_sum
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.summable_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_shift
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_of_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_anti
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_strictAnti
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.lt_of_wealth_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousAt_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.exists_wealth_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.planμ
#print axioms StokeyLucasPrescott.DeterministicApplications.consμ
#print axioms StokeyLucasPrescott.DeterministicApplications.planμ_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.consμ_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.div_pow_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.planμ_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.consμ_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.planμ_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.consμ_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.planμ_tail
#print axioms StokeyLucasPrescott.DeterministicApplications.consμ_tail
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.exists_plan_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.euler_step
#print axioms StokeyLucasPrescott.DeterministicApplications.abel_bound
#print axioms StokeyLucasPrescott.DeterministicApplications.CSWealth
#print axioms StokeyLucasPrescott.DeterministicApplications.csΓ
#print axioms StokeyLucasPrescott.DeterministicApplications.csF
#print axioms StokeyLucasPrescott.DeterministicApplications.consOf
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.consOf_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.csF_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.assumption41
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.assumption42
#print axioms StokeyLucasPrescott.DeterministicApplications.planN
#print axioms StokeyLucasPrescott.DeterministicApplications.wealthN
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.planN_feasible
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.consOf_planN
#print axioms StokeyLucasPrescott.DeterministicApplications.valμ
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.summable_val
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.partialSum_planN
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.tendsto_plan
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.plan_total
#print axioms StokeyLucasPrescott.DeterministicApplications.gapAt
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gapAt_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.value_bound
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.total_le
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.total_le_tangent
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.eq_planN_of_cons
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.total_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vstar_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vstar_le_tangent
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.optimal_iff
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vstar_real
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17a
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.planN_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.planμ_eq_of_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.consμ_eq_of_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.valμ_eq_of_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.U'_cI
#print axioms StokeyLucasPrescott.DeterministicApplications.muOf
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.muOf_spec
#print axioms StokeyLucasPrescott.DeterministicApplications.vR
#print axioms StokeyLucasPrescott.DeterministicApplications.gR
#print axioms StokeyLucasPrescott.DeterministicApplications.cR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vR_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cR_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vstar_wealth
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cR_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cR_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cR_eq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cR_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.muOf_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cR_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.cR_surj
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousWithinAt_cR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousOn_cR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousOn_gR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousOn_marg
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vR_le_tangent
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hasDerivWithinAt_vR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hasDerivAt_vR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.deriv_vR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousOn_vR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vR_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vR_strictConcave
#print axioms StokeyLucasPrescott.DeterministicApplications.m1
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.rhoU_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.rhoU_lt
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17b_m1
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.m1_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.wealth_rhoU
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.muOf_ge
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_eq_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vR_eq_low
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17b
#print axioms StokeyLucasPrescott.DeterministicApplications.hfun
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.U'_cR
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_def
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hfun_zero
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hfun_nonneg
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_hfun
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.euler_hfun
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.hfun_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousOn_hfun
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17c
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_mono
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.m2
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.continuousOn_vR'
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17d
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17e
#print axioms StokeyLucasPrescott.DeterministicApplications.mSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.mSeq_succ
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.mSeq_strictMono
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.tendsto_mSeq
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17f
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.vR_attained
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17g
#print axioms StokeyLucasPrescott.DeterministicApplications.CSHyp.gR_planμ
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17h_plan
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17h_slope
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17h_slope_le_one
#print axioms StokeyLucasPrescott.DeterministicApplications.hasDerivAt_cexp
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17b_m1_fails
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17g_hint_fails
#print axioms StokeyLucasPrescott.DeterministicApplications.ceU
#print axioms StokeyLucasPrescott.DeterministicApplications.ceU'
#print axioms StokeyLucasPrescott.DeterministicApplications.hasDerivAt_ce1
#print axioms StokeyLucasPrescott.DeterministicApplications.hasDerivAt_ce2
#print axioms StokeyLucasPrescott.DeterministicApplications.ceU'_low
#print axioms StokeyLucasPrescott.DeterministicApplications.ceU'_high
#print axioms StokeyLucasPrescott.DeterministicApplications.hasDerivAt_ceU
#print axioms StokeyLucasPrescott.DeterministicApplications.ceU'_strictAnti
#print axioms StokeyLucasPrescott.DeterministicApplications.ceU'_pos
#print axioms StokeyLucasPrescott.DeterministicApplications.continuousAt_ceU'
#print axioms StokeyLucasPrescott.DeterministicApplications.ceHyp
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17h_counterexample
#print axioms StokeyLucasPrescott.DeterministicApplications.ex_5_17h_book_bound_fails
