/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.JDDistribution

/-!
# Endogenous job destruction: the equilibrium conditions (Miao §18.2, pp. 600–603)

Miao, *Economic Dynamics in Discrete Time*, §18.2 (Mortensen–Pissarides 1994), pp. 600–603.
Matches draw an i.i.d. idiosyncratic productivity `z ∼ G` (a probability measure `μ`) each period;
exogenous separation has probability `ρˣ`; a filled job produces `A z`. All integrals over `z`
are set integrals over `(z*, ∞)` with respect to `μ`. Proved, as the text derives them:

* employment and unemployment dynamics (18.29) ⇒ (18.43) (`eq_18_43`); the total separation
  rate `ρ_t = ρˣ + (1 − ρˣ) G(z*_t)` (`jd_sepRate`, `jd_sepRate_mem`, `jd_sepRate_mono`);
* the Bellman equation for a filled job rewritten with the cutoff (`jd_filled_job_cutoff_form`);
* free entry in (18.30) ⇒ (18.31) (`eq_18_31`), (18.32) (`eq_18_32`), (18.33) (`eq_18_33`);
  the reservation productivity condition (18.34) (`eq_18_34`);
* Nash bargaining (18.37)–(18.38) (`eq_18_37_38`, via `jd_nash_iff`), the worker-surplus
  identity on p. 602 (`jd_worker_surplus`), the intermediate wage expression
  (`jd_wage_intermediate`) and the wage equation (18.39) (`eq_18_39`);
* the firm's value under the wage, (18.40) (`eq_18_40`), its linear form
  `J^F_t(z) = (1 − η) A (z − z*_t)` (`jd_JF_linear`) and the cutoff property (`jd_cutoff`);
* the job creation condition (18.41) (`eq_18_41`) and the job destruction condition (18.42)
  (`eq_18_42`);
* the job creation and destruction rates and their equality in a steady state
  (`jd_jcRate`, `jd_jdRate`, `jd_jc_eq_jd_of_steady`).

**Correction (timing in (18.41)–(18.42)).** The book writes `∫_{z*_t}^∞ (z_{t+1} − z*_t) dG` in
(18.41) and `∫_{z*_t}^∞ (z − z*_t) dG` in (18.42). Substituting `J^F_{t+1}(z) =
(1 − η) A (z − z*_{t+1})` into (18.31) gives the reservation productivity of period `t + 1`:
`κ / q(θ_t) = β (1 − η) A Φ(z*_{t+1})` and `η θ_t κ = (1 − η)(A z*_t − b) +
β (1 − ρˣ)(1 − η) A Φ(z*_{t+1})`, which is what `eq_18_41` and `eq_18_42` prove. The two
versions agree along constant paths, so the steady-state conditions (18.44)–(18.45) are
unaffected; the dynamics are in `JDSteadyState`.
-/

namespace Miao.SearchAndMatching

open MeasureTheory

/-- Miao, p. 600: the total separation rate `ρ_t = ρˣ + (1 − ρˣ) G(z*_t)`. -/
noncomputable def jd_sepRate (μ : Measure ℝ) (ρx zs : ℝ) : ℝ := ρx + (1 - ρx) * jd_G μ zs

/-- Miao, p. 600: `ρˣ ≤ ρ_t ≤ 1`. -/
theorem jd_sepRate_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] {ρx : ℝ} (h1 : ρx ≤ 1)
    (zs : ℝ) : ρx ≤ jd_sepRate μ ρx zs ∧ jd_sepRate μ ρx zs ≤ 1 := by
  obtain ⟨g0, g1⟩ := jd_G_mem μ zs
  unfold jd_sepRate
  constructor <;> nlinarith

/-- Miao, p. 600: the separation rate is nondecreasing in the reservation productivity. -/
theorem jd_sepRate_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] {ρx : ℝ} (h1 : ρx ≤ 1) :
    Monotone (jd_sepRate μ ρx) := by
  intro c c' h
  unfold jd_sepRate
  have := jd_G_mono μ h
  nlinarith

/-- Miao, (18.29) and (18.43), p. 603: with `u_t = 1 − N_t` and `v_t = θ_t u_t`, the employment
dynamics `N_{t+1} = (1 − ρ_t) N_t + q(θ_t) v_t` are `u_{t+1} = (1 − ρ_t − q(θ_t) θ_t) u_t + ρ_t`. -/
theorem eq_18_43 {q : ℝ → ℝ} {θ ρ N u v : ℕ → ℝ}
    (h29 : ∀ t, N (t + 1) = (1 - ρ t) * N t + q (θ t) * v t) (hu : ∀ t, u t = 1 - N t)
    (hv : ∀ t, v t = θ t * u t) (t : ℕ) :
    u (t + 1) = (1 - ρ t - q (θ t) * θ t) * u t + ρ t := by
  rw [hu (t + 1), h29 t, hv t, hu t]
  ring

/-- Miao, p. 601: when `J ≤ V` below the cutoff `c` and `J ≥ V` above it, the continuation value
`∫ max(J(z), V) dG` equals `∫_c^∞ (J(z) − V) dG + V`. This rewrites the Bellman equation for a
filled job with the reservation productivity. -/
theorem jd_filled_job_cutoff_form {μ : Measure ℝ} [IsProbabilityMeasure μ] {J : ℝ → ℝ}
    {V c : ℝ} (hJ : Integrable J μ) (hlo : ∀ z, z ≤ c → J z ≤ V) (hhi : ∀ z, c < z → V ≤ J z) :
    ∫ z, max (J z) V ∂μ = (∫ z in Set.Ioi c, (J z - V) ∂μ) + V := by
  have hpt : (fun z => max (J z) V) = fun z => (Set.Ioi c).indicator (fun z => J z - V) z + V := by
    funext z
    by_cases hz : c < z
    · rw [Set.indicator_of_mem (by exact hz), max_eq_left (hhi z hz)]; ring
    · rw [Set.indicator_of_notMem (by exact hz), max_eq_right (hlo z (not_lt.mp hz))]; ring
  have hi : Integrable (fun z => (Set.Ioi c).indicator (fun z => J z - V) z) μ :=
    (hJ.sub (integrable_const V)).indicator measurableSet_Ioi
  rw [hpt, integral_add hi (integrable_const V), integral_indicator measurableSet_Ioi]
  simp

/-- Miao, (18.30)–(18.31), p. 601: free entry (`V_t = 0` for all `t`) in the vacancy value
equation gives `β ∫_{z*_{t+1}}^∞ J^F_{t+1}(z) dG = κ / q(θ_t)`. -/
theorem eq_18_31 {μ : Measure ℝ} {β κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ} {JF : ℕ → ℝ → ℝ}
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (t : ℕ) :
    β * ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ = κ / q (θ t) := by
  have h := h30 t
  simp only [hfree, sub_zero, add_zero] at h
  have hq0 := (hq t).ne'
  field_simp
  linarith

/-- Miao, (18.32), p. 601: with free entry, the value of a filled job is
`J^F_t(z) = A z − w_t(z) + (1 − ρˣ) κ / q(θ_t)`. -/
theorem eq_18_32 {μ : Measure ℝ} {A β ρx κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (t : ℕ) (z : ℝ) :
    JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t) := by
  have h31 := eq_18_31 h30 hfree hq t
  have h := hJF t z
  simp only [hfree, sub_zero, add_zero] at h
  have e : (1 - ρx) * κ / q (θ t) = (1 - ρx) * (κ / q (θ t)) := by ring
  rw [h, e, ← h31]
  ring

/-- Miao, (18.33), p. 601: `κ / q(θ_t) = β ∫_{z*_{t+1}}^∞ (A z − w_{t+1}(z) + (1 − ρˣ) κ /
q(θ_{t+1})) dG(z)`. -/
theorem eq_18_33 {μ : Measure ℝ} {A β ρx κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (t : ℕ) :
    κ / q (θ t) = β * ∫ z in Set.Ioi (zs (t + 1)),
      (A * z - w (t + 1) z + (1 - ρx) * κ / q (θ (t + 1))) ∂μ := by
  rw [← eq_18_31 h30 hfree hq t]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun z _ => eq_18_32 hJF h30 hfree hq (t + 1) z

/-- Miao, (18.34), p. 601: the reservation productivity solves `J^F_t(z*_t) = 0`, i.e.
`A z*_t − w_t(z*_t) + (1 − ρˣ) κ / q(θ_t) = 0`. -/
theorem eq_18_34 {μ : Measure ℝ} {A β ρx κ : ℝ} {q : ℝ → ℝ} {θ zs V : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t)) (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    A * zs t - w t (zs t) + (1 - ρx) * κ / q (θ t) = 0 := by
  rw [← eq_18_32 hJF h30 hfree hq t (zs t)]
  exact hres t

/-- Miao, (18.37)–(18.38), p. 602: Nash bargaining over `w_t(z)`. The worker's surplus is
`J^W_t(z) − J^U_t = w + a` and the firm's `J^F_t(z) = c − w`, where `a` and `c` collect terms
that do not depend on the current wage. A feasible wage maximises
`(J^W − J^U)^η (J^F)^(1−η)` iff `η S = J^W − J^U` and `(1 − η) S = J^F`, `S = J^F + J^W − J^U`. -/
theorem eq_18_37_38 {η a c w : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hW : 0 ≤ a + w)
    (hF : 0 ≤ c - w) :
    (∀ w', 0 ≤ a + w' → 0 ≤ c - w' →
      (a + w') ^ η * (c - w') ^ (1 - η) ≤ (a + w) ^ η * (c - w) ^ (1 - η)) ↔
      (η * ((c - w) + (a + w)) = a + w ∧ (1 - η) * ((c - w) + (a + w)) = c - w) := by
  have h := jd_nash_iff (lam := 1) hη0 hη1 one_pos (by simpa using hW) hF
  simp only [one_mul] at h
  rw [h]
  constructor
  · intro h1; constructor <;> linarith
  · intro h1; linarith [h1.1]

/-- Miao, p. 602: subtracting (18.36) from (18.35), the worker's surplus satisfies
`J^W_t(z) − J^U_t = w_t(z) − b + β (1 − ρˣ − q^u_t) ∫_{z*_{t+1}}^∞ (J^W_{t+1} − J^U_{t+1}) dG`. -/
theorem jd_worker_surplus {μ : Measure ℝ} {β ρx b : ℝ} {qu zs JU : ℕ → ℝ}
    {JW w : ℕ → ℝ → ℝ}
    (h35 : ∀ t z, JW t z = w t z + β * ((1 - ρx) *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (h36 : ∀ t, JU t = b + β * (qu t *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (t : ℕ) (z : ℝ) :
    JW t z - JU t = w t z - b + β * (1 - ρx - qu t) *
      ∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ := by
  rw [h35 t z, h36 t]
  ring

/-- Miao, (18.39), p. 602: the Nash-bargained wage `w_t(z) = η (A z + θ_t κ) + (1 − η) b`,
derived from the Bellman equations (18.35)–(18.36) with `q^u_t = q(θ_t) θ_t`, the sharing rule
(18.37)–(18.38) (in the form `(1 − η)(J^W − J^U) = η J^F`), (18.31) and (18.32). -/
theorem eq_18_39 {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs V JU : ℕ → ℝ}
    {JF JW w : ℕ → ℝ → ℝ} (hβ : 0 < β) (hη1 : η < 1)
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t))
    (h35 : ∀ t z, JW t z = w t z + β * ((1 - ρx) *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (h36 : ∀ t, JU t = b + β * (q (θ t) * θ t *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (hnash : ∀ t z, (1 - η) * (JW t z - JU t) = η * JF t z) (t : ℕ) (z : ℝ) :
    w t z = η * (A * z + θ t * κ) + (1 - η) * b := by
  have h1η : (1 - η) ≠ 0 := by linarith
  have hq0 := (hq t).ne'
  have hβ0 := hβ.ne'
  set X := ∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ with hXdef
  have hX : X = η / (1 - η) * ∫ x in Set.Ioi (zs (t + 1)), JF (t + 1) x ∂μ := by
    rw [hXdef, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have := hnash (t + 1) x
    field_simp
    linarith
  have h31 := eq_18_31 h30 hfree hq t
  have hβX : β * X = η * κ / ((1 - η) * q (θ t)) := by
    rw [hX]
    have : β * (η / (1 - η) * ∫ x in Set.Ioi (zs (t + 1)), JF (t + 1) x ∂μ) =
        η / (1 - η) * (β * ∫ x in Set.Ioi (zs (t + 1)), JF (t + 1) x ∂μ) := by ring
    rw [this, h31]
    field_simp
  have hs := jd_worker_surplus (qu := fun t => q (θ t) * θ t) h35 h36 t z
  rw [← hXdef] at hs
  have h32 := eq_18_32 hJF h30 hfree hq t z
  have hn := hnash t z
  rw [hs, h32] at hn
  linear_combination (norm := (field_simp; ring)) hn - (1 - η) * (1 - ρx - q (θ t) * θ t) * hβX

/-- Miao, p. 602 (the intermediate wage expression): substituting (18.38) into the worker-surplus
identity, `w_t(z) = (1 − η) b + η (A z + (1 − ρˣ) κ / q(θ_t)) − η β (1 − ρˣ − q^u_t)
∫_{z*_{t+1}}^∞ (A z′ − w_{t+1}(z′) + (1 − ρˣ) κ / q(θ_{t+1})) dG(z′)`; with (18.33) this is the
wage equation (18.39). -/
theorem jd_wage_intermediate {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ}
    {θ zs V JU : ℕ → ℝ} {JF JW w : ℕ → ℝ → ℝ} (hβ : 0 < β) (hη1 : η < 1)
    (hJF : ∀ t z, JF t z = A * z - w t z + β * (1 - ρx) *
      ((∫ x in Set.Ioi (zs (t + 1)), (JF (t + 1) x - V (t + 1)) ∂μ) + V (t + 1)))
    (h30 : ∀ t, V t = -κ + β * (q (θ t) * (∫ z in Set.Ioi (zs (t + 1)),
      (JF (t + 1) z - V (t + 1)) ∂μ) + V (t + 1)))
    (hfree : ∀ t, V t = 0) (hq : ∀ t, 0 < q (θ t))
    (h35 : ∀ t z, JW t z = w t z + β * ((1 - ρx) *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (h36 : ∀ t, JU t = b + β * (q (θ t) * θ t *
      (∫ x in Set.Ioi (zs (t + 1)), (JW (t + 1) x - JU (t + 1)) ∂μ) + JU (t + 1)))
    (hnash : ∀ t z, (1 - η) * (JW t z - JU t) = η * JF t z) (t : ℕ) (z : ℝ) :
    w t z = (1 - η) * b + η * (A * z + (1 - ρx) * κ / q (θ t)) -
      η * β * (1 - ρx - q (θ t) * θ t) * ∫ x in Set.Ioi (zs (t + 1)),
        (A * x - w (t + 1) x + (1 - ρx) * κ / q (θ (t + 1))) ∂μ := by
  have h39 := eq_18_39 hβ hη1 hJF h30 hfree hq h35 h36 hnash t z
  have h33 := eq_18_33 hJF h30 hfree hq t
  have hq0 := (hq t).ne'
  have hβ0 := hβ.ne'
  set I := ∫ x in Set.Ioi (zs (t + 1)), (A * x - w (t + 1) x + (1 - ρx) * κ / q (θ (t + 1))) ∂μ
  have hI : I = κ / (β * q (θ t)) := by
    field_simp; field_simp at h33; linarith
  rw [hI, h39]
  field_simp
  ring

/-- Miao, (18.40), p. 602: under the wage (18.39),
`J^F_t(z) = (1 − η)(A z − b) − η θ_t κ + (1 − ρˣ) κ / q(θ_t)`, and this vanishes at `z*_t`. -/
theorem eq_18_40 {A ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ} {JF w : ℕ → ℝ → ℝ}
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    (∀ z, JF t z = (1 - η) * (A * z - b) - η * θ t * κ + (1 - ρx) * κ / q (θ t)) ∧
      0 = (1 - η) * (A * zs t - b) - η * θ t * κ + (1 - ρx) * κ / q (θ t) := by
  have hz : ∀ z, JF t z = (1 - η) * (A * z - b) - η * θ t * κ + (1 - ρx) * κ / q (θ t) := by
    intro z; rw [h32, h39]; ring
  exact ⟨hz, by rw [← hz, hres]⟩

/-- Miao, p. 603: taking the difference of the two equations in (18.40),
`J^F_t(z) = (1 − η) A (z − z*_t)`. -/
theorem jd_JF_linear {A ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ} {JF w : ℕ → ℝ → ℝ}
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) (z : ℝ) :
    JF t z = (1 - η) * A * (z - zs t) := by
  obtain ⟨h1, h2⟩ := eq_18_40 h32 h39 hres t
  rw [h1 z]
  linarith

/-- Miao, p. 600 ("clearly, there is a cutoff value"): with `A > 0` and `η < 1`, the firm keeps
the match iff `z > z*_t`: `J^F_t(z) ≤ 0 ↔ z ≤ z*_t`. -/
theorem jd_cutoff {A ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ} {JF w : ℕ → ℝ → ℝ}
    (hA : 0 < A) (hη1 : η < 1)
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) (z : ℝ) : JF t z ≤ 0 ↔ z ≤ zs t := by
  rw [jd_JF_linear h32 h39 hres t z]
  have hc : 0 < (1 - η) * A := mul_pos (by linarith) hA
  constructor
  · intro h
    by_contra hne
    have : 0 < (1 - η) * A * (z - zs t) := mul_pos hc (by linarith [not_le.mp hne])
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)

/-- Miao, (18.41), p. 603, with the timing corrected: the job creation condition
`κ / q(θ_t) = β (1 − η) A ∫_{z*_{t+1}}^∞ (z − z*_{t+1}) dG(z) = β (1 − η) A Φ(z*_{t+1})`. -/
theorem eq_18_41 {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (h31 : ∀ t, β * ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ = κ / q (θ t))
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    κ / q (θ t) = β * (1 - η) * A * ∫ z in Set.Ioi (zs (t + 1)), (z - zs (t + 1)) ∂μ ∧
      κ / q (θ t) = β * (1 - η) * A * jd_Phi μ (zs (t + 1)) := by
  have h : κ / q (θ t) = β * (1 - η) * A * ∫ z in Set.Ioi (zs (t + 1)), (z - zs (t + 1)) ∂μ := by
    have e : ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ =
        ∫ z in Set.Ioi (zs (t + 1)), (1 - η) * A * (z - zs (t + 1)) ∂μ :=
      setIntegral_congr_fun measurableSet_Ioi fun z _ => jd_JF_linear h32 h39 hres (t + 1) z
    rw [← h31 t, e, integral_const_mul]
    ring
  exact ⟨h, by rw [h, jd_Phi_eq_setIntegral]⟩

/-- Miao, (18.42), p. 603, with the timing corrected: the job destruction condition
`η θ_t κ = (1 − η)(A z*_t − b) + β (1 − ρˣ)(1 − η) A Φ(z*_{t+1})`. -/
theorem eq_18_42 {μ : Measure ℝ} {A β ρx κ η b : ℝ} {q : ℝ → ℝ} {θ zs : ℕ → ℝ}
    {JF w : ℕ → ℝ → ℝ}
    (h31 : ∀ t, β * ∫ z in Set.Ioi (zs (t + 1)), JF (t + 1) z ∂μ = κ / q (θ t))
    (h32 : ∀ t z, JF t z = A * z - w t z + (1 - ρx) * κ / q (θ t))
    (h39 : ∀ t z, w t z = η * (A * z + θ t * κ) + (1 - η) * b)
    (hres : ∀ t, JF t (zs t) = 0) (t : ℕ) :
    η * θ t * κ = (1 - η) * (A * zs t - b) +
      β * (1 - ρx) * (1 - η) * A * jd_Phi μ (zs (t + 1)) := by
  have h40 := (eq_18_40 h32 h39 hres t).2
  have h41 := (eq_18_41 h31 h32 h39 hres t).2
  have : (1 - ρx) * κ / q (θ t) = (1 - ρx) * (κ / q (θ t)) := by ring
  rw [this, h41] at h40
  linarith

/-- Miao, p. 603: the job destruction rate `jd_t = ρˣ + (1 − ρˣ) G(z*_t)`. -/
noncomputable def jd_jdRate (μ : Measure ℝ) (ρx zs : ℝ) : ℝ := jd_sepRate μ ρx zs

/-- Miao, p. 603: the job creation rate
`jc_t = M(u_t, v_t)/(1 − u_t) = q(θ_t) θ_t u_t/(1 − u_t)`. -/
noncomputable def jd_jcRate (q : ℝ → ℝ) (θ u : ℝ) : ℝ := q θ * θ * u / (1 - u)

/-- Miao, (18.43), pp. 603–607: in a steady state of (18.43) with `u < 1`, the job creation rate
equals the job destruction rate, and `u = ρ / (ρ + q(θ) θ)`. -/
theorem jd_jc_eq_jd_of_steady {μ : Measure ℝ} {ρx zs θ u : ℝ} {q : ℝ → ℝ} (hu1 : u < 1)
    (hpos : 0 < jd_sepRate μ ρx zs + q θ * θ)
    (hss : u = (1 - jd_sepRate μ ρx zs - q θ * θ) * u + jd_sepRate μ ρx zs) :
    jd_jcRate q θ u = jd_jdRate μ ρx zs ∧
      u = jd_sepRate μ ρx zs / (jd_sepRate μ ρx zs + q θ * θ) := by
  have h1u : (1 - u) ≠ 0 := by linarith
  unfold jd_jcRate jd_jdRate
  constructor
  · field_simp
    linarith
  · field_simp
    linarith

end Miao.SearchAndMatching
