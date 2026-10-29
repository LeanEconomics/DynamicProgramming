/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.IncrementAnalysis

/-!
# The `h`-approximation of the M/PH/1 queue (MT §16.4.3)

Meyn and Tweedie, §16.4.3, pp. 413–414. Jobs arrive at rate `λ`; a job needs `l ≥ 1` independent
exponential phases of service, each completed at rate `ν`, with probability `p_l`. The state is
`i = (i₁, i₂)`: `i₁` jobs wait in the queue and the job in service has `i₂` phases left. The
`h`-approximation is the discrete time chain that in one step of length `h` has an arrival with
probability `λh`, a phase completion with probability `νh`, and otherwise stays put.

**The chain** (`phKernel`). The state space is `phSpace = {i : i₂ = 0 → i₁ = 0}` (the server is
busy whenever a job waits). The number of phases of a job is `k + 1` with probability `p k`
(`p : ℕ → ℝ≥0∞`, `Σ p = 1`), and `a = λh`, `b = νh`, `a + b < 1`:
* from `0`: `→ (0, k + 1)` with probability `a p_k`, stay with probability `1 − a`;
* from `(i₁, i₂)`, `i₂ ≥ 1`: `→ (i₁ + 1, i₂)` with probability `a`; with probability `b` a phase
  is completed, `→ (i₁, i₂ − 1)` if `i₂ ≥ 2`, `→ (i₁ − 1, k + 1)` with probability `b p_k` if
  `i₂ = 1 ≤ i₁`, and `→ 0` if `i = (0, 1)`; stay with probability `1 − a − b`.

**Results.**
* `lintegral_phKernel_zero`, `lintegral_phKernel_one`, `lintegral_phKernel_succ_one`,
  `lintegral_phKernel_two`: one-step integrals.
* `phV`, `phKernel_drift` ((16.36)–(16.37) in drift form, p. 413): with `m = Σ (k + 1) p_k` the
  mean number of phases and `w = 1/(νh − λh m)`, the linear function
  `V(i) = w (m i₁ + i₂)` satisfies `PV = V − 1` off `{0}`: `V(i + e₂) − V(i) = w` and
  `V(i + e₁) − V(i) = w m`, the book's `c` and `c̄ = c Σ l p_l`.
* `phKernel_reach_zero`, `phKernel_isPhiIrreducible`: the chain reaches `0` from every state.
* **`theorem_16_4_3`** (p. 414): if `λ m < ν` (ergodicity) and the phase distribution is in
  `G⁺(γ)`, `Σ p_k e^{γk} < ∞`, the chain is positive, aperiodic and `e^{δV}`-uniformly ergodic
  for some `δ > 0`, with `Σ rⁿ |||Pⁿ − 1 ⊗ π|||_V < ∞`: it is geometrically ergodic.
* `theorem_16_4_3_finite`: with finitely many phases (`p_k = 0` for `k ≥ N`), `λ m < ν` alone
  gives geometric ergodicity.

**Corrections (the transition probabilities of p. 413).** The printed list is not a transition
law of the M/PH/1 queue: an arrival to the empty queue goes to `0 + l e₂` (printed `0 + e₂`); a
job that completes its last phase is followed by a job with `l` phases, `i − e₁ + (l − 1)e₂`, so
that `i₂` becomes `l` (printed `i − e₁ + l e₂`); arrivals and phase completions occur whenever
the server is busy, `i₂ > 0` (printed `i₁ > 0`); and the transition `(0, 1) → 0` is missing. The
chain here is the M/PH/1 reading of the description.

**Hypotheses.** "Ergodic" is read as the load condition `λ m < ν` (mean service time `m/ν` less
than the mean interarrival time `1/λ`), under which the linear drift above holds; the book's
`h < (λ + ν)⁻¹` is `a + b < 1`.

**Not formalised.** The coupling proof that `E_i[σ₀]` is exactly linear is replaced by the
direct verification that the linear `V` satisfies (16.25) with equality.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ### The state space and the kernel -/

/-- The state space of the M/PH/1 chain: `(i₁, i₂)` with `i₂ = 0 → i₁ = 0`. -/
def phSpace : Set (ℕ × ℕ) := {i | i.2 = 0 → i.1 = 0}

/-- `(q, r + 1)` is a state. -/
theorem mem_phSpace_succ (q r : ℕ) : (q, r + 1) ∈ phSpace := fun h =>
  absurd h (Nat.succ_ne_zero r)

/-- `0` is a state. -/
theorem zero_mem_phSpace : ((0 : ℕ), (0 : ℕ)) ∈ phSpace := fun _ => rfl

/-- The empty state `0`. -/
def phZero : phSpace := ⟨(0, 0), zero_mem_phSpace⟩

/-- The start of a new job behind `q` waiting jobs: `(q, k + 1)` with probability `p k`. -/
noncomputable def phStart (p : ℕ → ℝ≥0∞) (q : ℕ) : Measure phSpace :=
  Measure.sum fun k => p k • Measure.dirac ⟨(q, k + 1), mem_phSpace_succ q k⟩

/-- The one-step law of the `h`-approximation of the M/PH/1 queue from `(q, r)`, with `a = λh`,
`b = νh` (the remaining phases `r` are matched first). -/
noncomputable def phMeasure (p : ℕ → ℝ≥0∞) (a b : ℝ≥0) :
    (r q : ℕ) → (r = 0 → q = 0) → Measure phSpace
  | r + 2, q, _ => (a : ℝ≥0∞) • Measure.dirac ⟨(q + 1, r + 2), mem_phSpace_succ (q + 1) _⟩ +
      (b : ℝ≥0∞) • Measure.dirac ⟨(q, r + 1), mem_phSpace_succ q r⟩ +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) • Measure.dirac ⟨(q, r + 2), mem_phSpace_succ q _⟩
  | 1, 0, _ => (a : ℝ≥0∞) • Measure.dirac ⟨(1, 1), mem_phSpace_succ 1 0⟩ +
      (b : ℝ≥0∞) • Measure.dirac phZero +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) • Measure.dirac ⟨(0, 1), mem_phSpace_succ 0 0⟩
  | 1, q + 1, _ => (a : ℝ≥0∞) • Measure.dirac ⟨(q + 2, 1), mem_phSpace_succ (q + 2) 0⟩ +
      (b : ℝ≥0∞) • phStart p q +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) • Measure.dirac ⟨(q + 1, 1), mem_phSpace_succ (q + 1) 0⟩
  | 0, 0, _ => ((1 - a : ℝ≥0) : ℝ≥0∞) • Measure.dirac phZero + (a : ℝ≥0∞) • phStart p 0
  | 0, q + 1, h => (Nat.succ_ne_zero q (h rfl)).elim

/-- The `h`-approximation of the M/PH/1 queue as a kernel. -/
noncomputable def phKernel (p : ℕ → ℝ≥0∞) (a b : ℝ≥0) : Kernel phSpace phSpace :=
  ⟨fun x => phMeasure p a b x.1.2 x.1.1 x.2, measurable_of_countable _⟩

/-! ### One-step integrals -/

/-- `∫ g d(phStart p q) = Σₖ p_k g(q, k + 1)`. -/
theorem lintegral_phStart (p : ℕ → ℝ≥0∞) (q : ℕ) (g : phSpace → ℝ≥0∞) :
    ∫⁻ y, g y ∂phStart p q = ∑' k, p k * g ⟨(q, k + 1), mem_phSpace_succ q k⟩ := by
  rw [phStart, lintegral_sum_measure]
  refine tsum_congr fun k => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- From `0`: `Pg(0) = (1 − a) g(0) + a Σₖ p_k g(0, k + 1)`. -/
theorem lintegral_phKernel_zero (p : ℕ → ℝ≥0∞) (a b : ℝ≥0) (g : phSpace → ℝ≥0∞) :
    ∫⁻ y, g y ∂phKernel p a b phZero = ((1 - a : ℝ≥0) : ℝ≥0∞) * g phZero +
      (a : ℝ≥0∞) * ∑' k, p k * g ⟨(0, k + 1), mem_phSpace_succ 0 k⟩ := by
  change ∫⁻ y, g y ∂(((1 - a : ℝ≥0) : ℝ≥0∞) • Measure.dirac phZero +
    (a : ℝ≥0∞) • phStart p 0) = _
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_phStart, smul_eq_mul, smul_eq_mul]

/-- From `(0, 1)`: `Pg = a g(1, 1) + b g(0) + (1 − a − b) g(0, 1)`. -/
theorem lintegral_phKernel_one (p : ℕ → ℝ≥0∞) (a b : ℝ≥0) (g : phSpace → ℝ≥0∞) :
    ∫⁻ y, g y ∂phKernel p a b ⟨(0, 1), mem_phSpace_succ 0 0⟩ =
      (a : ℝ≥0∞) * g ⟨(1, 1), mem_phSpace_succ 1 0⟩ + (b : ℝ≥0∞) * g phZero +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) * g ⟨(0, 1), mem_phSpace_succ 0 0⟩ := by
  change ∫⁻ y, g y ∂((a : ℝ≥0∞) • Measure.dirac ⟨(1, 1), mem_phSpace_succ 1 0⟩ +
      (b : ℝ≥0∞) • Measure.dirac phZero +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) • Measure.dirac ⟨(0, 1), mem_phSpace_succ 0 0⟩) = _
  rw [lintegral_add_measure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
    lintegral_dirac, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- From `(q + 1, 1)`: `Pg = a g(q + 2, 1) + b Σₖ p_k g(q, k + 1) + (1 − a − b) g(q + 1, 1)`. -/
theorem lintegral_phKernel_succ_one (p : ℕ → ℝ≥0∞) (a b : ℝ≥0) (q : ℕ) (g : phSpace → ℝ≥0∞) :
    ∫⁻ y, g y ∂phKernel p a b ⟨(q + 1, 1), mem_phSpace_succ (q + 1) 0⟩ =
      (a : ℝ≥0∞) * g ⟨(q + 2, 1), mem_phSpace_succ (q + 2) 0⟩ +
      (b : ℝ≥0∞) * ∑' k, p k * g ⟨(q, k + 1), mem_phSpace_succ q k⟩ +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) * g ⟨(q + 1, 1), mem_phSpace_succ (q + 1) 0⟩ := by
  change ∫⁻ y, g y ∂((a : ℝ≥0∞) • Measure.dirac ⟨(q + 2, 1), mem_phSpace_succ (q + 2) 0⟩ +
      (b : ℝ≥0∞) • phStart p q +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) • Measure.dirac ⟨(q + 1, 1), mem_phSpace_succ (q + 1) 0⟩) = _
  rw [lintegral_add_measure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
    lintegral_phStart, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- From `(q, r + 2)`: `Pg = a g(q + 1, r + 2) + b g(q, r + 1) + (1 − a − b) g(q, r + 2)`. -/
theorem lintegral_phKernel_two (p : ℕ → ℝ≥0∞) (a b : ℝ≥0) (q r : ℕ) (g : phSpace → ℝ≥0∞) :
    ∫⁻ y, g y ∂phKernel p a b ⟨(q, r + 2), mem_phSpace_succ q (r + 1)⟩ =
      (a : ℝ≥0∞) * g ⟨(q + 1, r + 2), mem_phSpace_succ (q + 1) (r + 1)⟩ +
      (b : ℝ≥0∞) * g ⟨(q, r + 1), mem_phSpace_succ q r⟩ +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) * g ⟨(q, r + 2), mem_phSpace_succ q (r + 1)⟩ := by
  change ∫⁻ y, g y ∂((a : ℝ≥0∞) • Measure.dirac
      ⟨(q + 1, r + 2), mem_phSpace_succ (q + 1) (r + 1)⟩ +
      (b : ℝ≥0∞) • Measure.dirac ⟨(q, r + 1), mem_phSpace_succ q r⟩ +
      ((1 - a - b : ℝ≥0) : ℝ≥0∞) • Measure.dirac ⟨(q, r + 2), mem_phSpace_succ q (r + 1)⟩) = _
  rw [lintegral_add_measure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
    lintegral_dirac, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- Every state is `0`, `(0, 1)`, `(q + 1, 1)` or `(q, r + 2)`. -/
theorem phSpace_cases (x : phSpace) : x = phZero ∨ x = ⟨(0, 1), mem_phSpace_succ 0 0⟩ ∨
    (∃ q, x = ⟨(q + 1, 1), mem_phSpace_succ (q + 1) 0⟩) ∨
    ∃ q r, x = ⟨(q, r + 2), mem_phSpace_succ q (r + 1)⟩ := by
  obtain ⟨⟨q, r⟩, hx⟩ := x
  rcases r with _ | _ | r
  · have hq : q = 0 := hx rfl
    subst hq
    exact Or.inl rfl
  · rcases q with _ | q
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨q, r, rfl⟩))

/-- The coefficients sum to one. -/
theorem ph_coeff_sum {a b : ℝ≥0} (hab : a + b ≤ 1) :
    (a : ℝ≥0∞) + b + ((1 - a - b : ℝ≥0) : ℝ≥0∞) = 1 := by
  rw [← ENNReal.coe_add, ← ENNReal.coe_add, tsub_tsub, add_tsub_cancel_of_le hab,
    ENNReal.coe_one]

/-- The chain is a Markov kernel when `a + b ≤ 1` and `Σ p = 1`. -/
theorem isMarkovKernel_phKernel {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {a b : ℝ≥0}
    (hab : a + b ≤ 1) : IsMarkovKernel (phKernel p a b) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have ha : a ≤ 1 := le_trans le_self_add hab
  rw [← lintegral_one]
  rcases phSpace_cases x with rfl | rfl | ⟨q, rfl⟩ | ⟨q, r, rfl⟩
  · rw [lintegral_phKernel_zero]
    simp only [mul_one, hp]
    rw [← ENNReal.coe_add, tsub_add_cancel_of_le ha, ENNReal.coe_one]
  · rw [lintegral_phKernel_one]
    simp only [mul_one]
    exact ph_coeff_sum hab
  · rw [lintegral_phKernel_succ_one]
    simp only [mul_one, hp]
    exact ph_coeff_sum hab
  · rw [lintegral_phKernel_two]
    simp only [mul_one]
    exact ph_coeff_sum hab

/-! ### The linear drift function -/

/-- The linear function `V(i) = w (m i₁ + i₂)` of (16.36)–(16.37). -/
def phV (w m : ℝ) (x : phSpace) : ℝ := w * (m * x.1.1 + x.1.2)

/-- `V ≥ 0`. -/
theorem phV_nonneg {w m : ℝ} (hw : 0 ≤ w) (hm : 0 ≤ m) (x : phSpace) : 0 ≤ phV w m x := by
  unfold phV
  positivity

/-- `a ⋅ ofReal t = ofReal (a t)` for `a ≥ 0`. -/
theorem ph_coe_mul_ofReal (a : ℝ≥0) (t : ℝ) :
    (a : ℝ≥0∞) * ENNReal.ofReal t = ENNReal.ofReal (a * t) := by
  rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- The mean number of phases, `m = Σ (k + 1) p_k`. -/
noncomputable def phMean (p : ℕ → ℝ≥0∞) : ℝ := (∑' k, p k * ((k : ℝ≥0∞) + 1)).toReal

/-- `Σₖ p_k (w(A + k + 1)) = w(A + m)`. -/
theorem ph_tsum_linear {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1)
    (hM : ∑' k, p k * ((k : ℝ≥0∞) + 1) ≠ ∞) {w A : ℝ} (hw : 0 ≤ w) (hA : 0 ≤ A)
    (g : ℕ → ℝ≥0∞) (hg : ∀ k, g k = ENNReal.ofReal (w * (A + ((k + 1 : ℕ) : ℝ)))) :
    ∑' k, p k * g k = ENNReal.ofReal (w * (A + phMean p)) := by
  have hterm : ∀ k, p k * g k = p k * ENNReal.ofReal (w * A) +
      ENNReal.ofReal w * (p k * ((k : ℝ≥0∞) + 1)) := fun k => by
    rw [hg k, mul_add, ENNReal.ofReal_add (mul_nonneg hw hA) (mul_nonneg hw (Nat.cast_nonneg _)),
      ENNReal.ofReal_mul (q := ((k + 1 : ℕ) : ℝ)) hw, ENNReal.ofReal_natCast, Nat.cast_succ]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hp,
    one_mul, phMean, mul_add,
    ENNReal.ofReal_add (mul_nonneg hw hA) (mul_nonneg hw ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (q := (∑' k, p k * ((k : ℝ≥0∞) + 1)).toReal) hw,
    ENNReal.ofReal_toReal hM]

/-- `a x + b y + c z = ofReal (a x + b y + c z)` for nonnegative reals. -/
theorem ph_three (a b c : ℝ≥0) {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (a : ℝ≥0∞) * ENNReal.ofReal x + (b : ℝ≥0∞) * ENNReal.ofReal y +
      (c : ℝ≥0∞) * ENNReal.ofReal z = ENNReal.ofReal (a * x + b * y + c * z) := by
  rw [ph_coe_mul_ofReal, ph_coe_mul_ofReal, ph_coe_mul_ofReal,
    ← ENNReal.ofReal_add (mul_nonneg a.coe_nonneg hx) (mul_nonneg b.coe_nonneg hy),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg a.coe_nonneg hx) (mul_nonneg b.coe_nonneg hy))
      (mul_nonneg c.coe_nonneg hz)]

/-- `1 − a − b` as a real number. -/
theorem ph_coeff_real {a b : ℝ≥0} (hab : a + b ≤ 1) :
    ((1 - a - b : ℝ≥0) : ℝ) = 1 - a - b := by
  rw [tsub_tsub, NNReal.coe_sub hab, NNReal.coe_add, NNReal.coe_one]
  ring

/-- `PV(0) = a w m`. -/
theorem phKernel_drift_zero {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1)
    (hM : ∑' k, p k * ((k : ℝ≥0∞) + 1) ≠ ∞) (a b : ℝ≥0) {w : ℝ} (hw : 0 ≤ w) :
    ∫⁻ y, ENNReal.ofReal (phV w (phMean p) y) ∂phKernel p a b phZero =
      ENNReal.ofReal (a * (w * phMean p)) := by
  have hm : 0 ≤ phMean p := ENNReal.toReal_nonneg
  have h0 : phV w (phMean p) phZero = 0 := by
    simp only [phV, phZero, Nat.cast_zero, mul_zero, add_zero]
  rw [lintegral_phKernel_zero, ph_tsum_linear hp hM hw (A := phMean p * ((0 : ℕ) : ℝ))
      (by positivity) (fun k => ENNReal.ofReal (phV w (phMean p) ⟨(0, k + 1), _⟩)) fun k => rfl,
    h0, ENNReal.ofReal_zero, mul_zero, zero_add, ph_coe_mul_ofReal]
  congr 1
  push_cast
  ring

/-- **The linear drift** ((16.36)–(16.37) in drift form, MT p. 413): with `w (b − a m) = 1`,
`PV = V − 1` off `0`. -/
theorem phKernel_drift {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1)
    (hM : ∑' k, p k * ((k : ℝ≥0∞) + 1) ≠ ∞) {a b : ℝ≥0} (hab : a + b ≤ 1) {w : ℝ}
    (hw : 0 ≤ w) (hwb : w * (b - a * phMean p) = 1) {x : phSpace} (hx : x ≠ phZero) :
    ∫⁻ y, ENNReal.ofReal (phV w (phMean p) y) ∂phKernel p a b x =
      ENNReal.ofReal (phV w (phMean p) x - 1) := by
  set m := phMean p with hmdef
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hc := ph_coeff_real hab
  rcases phSpace_cases x with rfl | rfl | ⟨q, rfl⟩ | ⟨q, r, rfl⟩
  · exact absurd rfl hx
  · rw [lintegral_phKernel_one,
      show phV w m phZero = 0 by simp only [phV, phZero, Nat.cast_zero, mul_zero, add_zero],
      ph_three _ _ _ (phV_nonneg hw hm _) le_rfl (phV_nonneg hw hm _)]
    congr 1
    simp only [phV]
    push_cast
    rw [hc]
    linear_combination (-1 : ℝ) * hwb
  · rw [lintegral_phKernel_succ_one,
      ph_tsum_linear hp hM hw (mul_nonneg hm (Nat.cast_nonneg q))
        (fun k => ENNReal.ofReal (phV w m ⟨(q, k + 1), mem_phSpace_succ q k⟩)) fun k => rfl,
      ph_three _ _ _ (phV_nonneg hw hm _) (by positivity) (phV_nonneg hw hm _)]
    congr 1
    simp only [phV]
    push_cast
    rw [hc]
    linear_combination (-1 : ℝ) * hwb
  · rw [lintegral_phKernel_two,
      ph_three _ _ _ (phV_nonneg hw hm _) (phV_nonneg hw hm _) (phV_nonneg hw hm _)]
    congr 1
    simp only [phV]
    push_cast
    rw [hc]
    linear_combination (-1 : ℝ) * hwb

/-! ### Bounds on the increments -/

/-- A three-point mixture of values `≤ B` is `≤ B`. -/
theorem ph_three_le {a b : ℝ≥0} (hab : a + b ≤ 1) {X Y Z B : ℝ≥0∞} (hX : X ≤ B) (hY : Y ≤ B)
    (hZ : Z ≤ B) : (a : ℝ≥0∞) * X + (b : ℝ≥0∞) * Y + ((1 - a - b : ℝ≥0) : ℝ≥0∞) * Z ≤ B := by
  calc (a : ℝ≥0∞) * X + (b : ℝ≥0∞) * Y + ((1 - a - b : ℝ≥0) : ℝ≥0∞) * Z
      ≤ (a : ℝ≥0∞) * B + (b : ℝ≥0∞) * B + ((1 - a - b : ℝ≥0) : ℝ≥0∞) * B := by gcongr
    _ = B := by rw [← add_mul, ← add_mul, ph_coeff_sum hab, one_mul]

/-- A two-point mixture of values `≤ B` is `≤ B`. -/
theorem ph_two_le {a : ℝ≥0} (ha : a ≤ 1) {X Y B : ℝ≥0∞} (hX : X ≤ B) (hY : Y ≤ B) :
    ((1 - a : ℝ≥0) : ℝ≥0∞) * X + (a : ℝ≥0∞) * Y ≤ B := by
  calc ((1 - a : ℝ≥0) : ℝ≥0∞) * X + (a : ℝ≥0∞) * Y
      ≤ ((1 - a : ℝ≥0) : ℝ≥0∞) * B + (a : ℝ≥0∞) * B := by gcongr
    _ = B := by rw [← add_mul, ← ENNReal.coe_add, tsub_add_cancel_of_le ha, ENNReal.coe_one,
        one_mul]

/-- A `p`-mixture of values `≤ B` is `≤ B`. -/
theorem ph_tsum_le {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {g : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀ k, g k ≤ B) : ∑' k, p k * g k ≤ B := by
  calc ∑' k, p k * g k ≤ ∑' k, p k * B := ENNReal.tsum_le_tsum fun k => by gcongr; exact h k
    _ = B := by rw [ENNReal.tsum_mul_right, hp, one_mul]

/-- **Exponential moments of the increments** ((16.26) for the M/PH/1 chain): with `βw = γ`,
`E_x[e^{β(V(Φ₁) − V(x))}] ≤ e^{γm} + e^γ Σ p_k e^{γk} + 2` for every `x`. -/
theorem phKernel_exp_le {p : ℕ → ℝ≥0∞} {a b : ℝ≥0} (hab : a + b ≤ 1)
    {w m β γ : ℝ} (hm : 0 ≤ m) (hγ : 0 ≤ γ) (hβw : β * w = γ) (x : phSpace) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (β * (phV w m y - phV w m x))) ∂phKernel p a b x ≤
      ENNReal.ofReal (Real.exp (γ * m)) +
        ENNReal.ofReal (Real.exp γ) * ∑' k, p k * ENNReal.ofReal (Real.exp (γ * k)) + 2 := by
  set G := ∑' k, p k * ENNReal.ofReal (Real.exp (γ * k)) with hG
  set B := ENNReal.ofReal (Real.exp (γ * m)) + ENNReal.ofReal (Real.exp γ) * G + 2 with hB
  have ha : a ≤ 1 := le_trans le_self_add hab
  have h1B : (1 : ℝ≥0∞) ≤ B := le_trans (by norm_num) le_add_self
  have hmB : ENNReal.ofReal (Real.exp (γ * m)) ≤ B := le_trans le_self_add le_self_add
  have hGB : ENNReal.ofReal (Real.exp γ) * G ≤ B := le_trans le_add_self le_self_add
  have hGG : G ≤ ENNReal.ofReal (Real.exp γ) * G := le_mul_of_one_le_left zero_le
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hγ))
  have hle1 : ∀ t : ℝ, t ≤ 0 → ENNReal.ofReal (Real.exp t) ≤ B := fun t ht => by
    have h := ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 ht)
    rw [ENNReal.ofReal_one] at h
    exact h.trans h1B
  have hlem : ∀ t : ℝ, t ≤ γ * m → ENNReal.ofReal (Real.exp t) ≤ B := fun t ht =>
    le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ht)) hmB
  have hstart : ∀ (q : ℕ) (c : ℝ), (∀ k : ℕ, β * (phV w m ⟨(q, k + 1), mem_phSpace_succ q k⟩ - c)
      ≤ γ + γ * k) → ∑' k, p k * ENNReal.ofReal (Real.exp
        (β * (phV w m ⟨(q, k + 1), mem_phSpace_succ q k⟩ - c))) ≤ B := fun q c hk => by
    refine le_trans ?_ hGB
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    gcongr
    exact hk k
  rcases phSpace_cases x with rfl | rfl | ⟨q, rfl⟩ | ⟨q, r, rfl⟩
  · rw [lintegral_phKernel_zero]
    refine ph_two_le ha (hle1 _ (by rw [sub_self, mul_zero])) (hstart 0 _ fun k => ?_)
    have e : β * (phV w m ⟨(0, k + 1), mem_phSpace_succ 0 k⟩ - phV w m phZero) =
        β * w * (k + 1) := by simp only [phV, phZero]; push_cast; ring
    rw [e, hβw]
    linarith
  · rw [lintegral_phKernel_one]
    refine ph_three_le hab (hlem _ (le_of_eq ?_)) (hle1 _ ?_) (hle1 _ (by rw [sub_self,
      mul_zero]))
    · have e : β * (phV w m ⟨(1, 1), mem_phSpace_succ 1 0⟩ -
          phV w m ⟨(0, 1), mem_phSpace_succ 0 0⟩) = β * w * m := by
        simp only [phV]; push_cast; ring
      rw [e, hβw]
    · have e : β * (phV w m phZero - phV w m ⟨(0, 1), mem_phSpace_succ 0 0⟩) = -(β * w) := by
        simp only [phV, phZero]; push_cast; ring
      rw [e, hβw]
      linarith
  · rw [lintegral_phKernel_succ_one]
    refine ph_three_le hab (hlem _ (le_of_eq ?_)) (hstart q _ fun k => ?_)
      (hle1 _ (by rw [sub_self, mul_zero]))
    · have e : β * (phV w m ⟨(q + 2, 1), mem_phSpace_succ (q + 2) 0⟩ -
          phV w m ⟨(q + 1, 1), mem_phSpace_succ (q + 1) 0⟩) = β * w * m := by
        simp only [phV]; push_cast; ring
      rw [e, hβw]
    · have e : β * (phV w m ⟨(q, k + 1), mem_phSpace_succ q k⟩ -
          phV w m ⟨(q + 1, 1), mem_phSpace_succ (q + 1) 0⟩) = β * w * (k - m) := by
        simp only [phV]; push_cast; ring
      rw [e, hβw]
      nlinarith
  · rw [lintegral_phKernel_two]
    refine ph_three_le hab (hlem _ (le_of_eq ?_)) (hle1 _ ?_) (hle1 _ (by rw [sub_self,
      mul_zero]))
    · have e : β * (phV w m ⟨(q + 1, r + 2), mem_phSpace_succ (q + 1) (r + 1)⟩ -
          phV w m ⟨(q, r + 2), mem_phSpace_succ q (r + 1)⟩) = β * w * m := by
        simp only [phV]; push_cast; ring
      rw [e, hβw]
    · have e : β * (phV w m ⟨(q, r + 1), mem_phSpace_succ q r⟩ -
          phV w m ⟨(q, r + 2), mem_phSpace_succ q (r + 1)⟩) = -(β * w) := by
        simp only [phV]; push_cast; ring
      rw [e, hβw]
      linarith

/-- **The decreases are bounded** ((16.27) for the M/PH/1 chain): `V(Φ₁) ≥ V(x) − w(m + 1)`, so
`E_x[(V(Φ₁) − V(x))² ; V(Φ₁) < V(x)] ≤ (w(m + 1))²`. -/
theorem phKernel_sq_le {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {a b : ℝ≥0} (hab : a + b ≤ 1)
    {w m : ℝ} (hw : 0 ≤ w) (hm : 0 ≤ m) (x : phSpace) :
    ∫⁻ y, ENNReal.ofReal ({y | phV w m y < phV w m x}.indicator
      (fun y => (phV w m y - phV w m x) ^ 2) y) ∂phKernel p a b x ≤
      ENNReal.ofReal ((w * (m + 1)) ^ 2) := by
  have ha : a ≤ 1 := le_trans le_self_add hab
  have hL : 0 ≤ w * (m + 1) := by positivity
  have hpt : ∀ y, phV w m x - w * (m + 1) ≤ phV w m y →
      ENNReal.ofReal ({y | phV w m y < phV w m x}.indicator
        (fun y => (phV w m y - phV w m x) ^ 2) y) ≤ ENNReal.ofReal ((w * (m + 1)) ^ 2) :=
    fun y hy => by
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hS : y ∈ {y | phV w m y < phV w m x}
      · rw [indicator_of_mem hS]
        have hS' : phV w m y < phV w m x := hS
        exact sq_le_sq' (by linarith) (by linarith)
      · rw [indicator_of_notMem hS]
        positivity
  have hself : ∀ y : phSpace, phV w m y - w * (m + 1) ≤ phV w m y := fun y => by linarith
  have hV0 : ∀ y, 0 ≤ phV w m y := phV_nonneg hw hm
  rcases phSpace_cases x with rfl | rfl | ⟨q, rfl⟩ | ⟨q, r, rfl⟩
  · rw [lintegral_phKernel_zero]
    refine ph_two_le ha (hpt _ (hself _)) (ph_tsum_le hp fun k => hpt _ ?_)
    have h0 : phV w m phZero = 0 := by simp only [phV, phZero, Nat.cast_zero, mul_zero, add_zero]
    rw [h0]
    linarith [hV0 ⟨(0, k + 1), mem_phSpace_succ 0 k⟩]
  · rw [lintegral_phKernel_one]
    refine ph_three_le hab (hpt _ ?_) (hpt _ ?_) (hpt _ (hself _))
    · simp only [phV]; push_cast; nlinarith
    · simp only [phV, phZero]; push_cast; nlinarith
  · rw [lintegral_phKernel_succ_one]
    refine ph_three_le hab (hpt _ ?_) (ph_tsum_le hp fun k => hpt _ ?_) (hpt _ (hself _))
    · simp only [phV]; push_cast; nlinarith
    · simp only [phV]; push_cast
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
  · rw [lintegral_phKernel_two]
    refine ph_three_le hab (hpt _ ?_) (hpt _ ?_) (hpt _ (hself _))
    · simp only [phV]; push_cast; nlinarith
    · simp only [phV]; push_cast; nlinarith

/-! ### Irreducibility and the main theorem -/

/-- **Chapman–Kolmogorov from one state**: `Pⁿ⁺²(x, A) ≥ P(x, {y}) Pⁿ⁺¹(y, A)`. -/
theorem ph_pow_succ_ge (K : Kernel phSpace phSpace) (n : ℕ) (x y : phSpace) {A : Set phSpace}
    (hA : MeasurableSet A) : K x {y} * (K ^ (n + 1)) y A ≤ (K ^ (n + 1 + 1)) x A := by
  rw [pow_succ_apply _ (n + 1) x hA, mul_comm,
    ← lintegral_singleton (fun z => (K ^ (n + 1)) z A) y]
  exact setLIntegral_le_lintegral _ _

/-- The chain reaches `0` from every state: for every `x` some `Pⁿ⁺¹(x, {0}) > 0`. Along the path
the server completes phases with no arrivals (each step has probability at least
`b min(1, p_{k₀})` for some `k₀` with `p_{k₀} > 0`). -/
theorem phKernel_reach_zero {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {a b : ℝ≥0} (ha : a < 1)
    (hb : 0 < b) (x : phSpace) : ∃ n, 0 < (phKernel p a b ^ (n + 1)) x {phZero} := by
  obtain ⟨k₀, hk₀⟩ : ∃ k, p k ≠ 0 := by
    by_contra h
    push Not at h
    rw [tsum_congr h, tsum_zero] at hp
    exact zero_ne_one hp
  have hb' : (0 : ℝ≥0∞) < b := ENNReal.coe_pos.2 hb
  have hP : ∀ (z y : phSpace), phKernel p a b z {y} = ∫⁻ u, ({y} : Set phSpace).indicator 1 u
      ∂phKernel p a b z := fun z y => (lintegral_indicator_one (measurableSet_singleton y)).symm
  have hone : ∀ y : phSpace, ({y} : Set phSpace).indicator (1 : phSpace → ℝ≥0∞) y = 1 :=
    fun y => by rw [indicator_of_mem (mem_singleton y), Pi.one_apply]
  have key : ∀ N : ℕ, ∀ x : phSpace, (k₀ + 2) * x.1.1 + x.1.2 ≤ N →
      ∃ n, 0 < (phKernel p a b ^ (n + 1)) x {phZero} := by
    intro N
    induction N with
    | zero =>
      intro x hx
      rcases phSpace_cases x with rfl | rfl | ⟨q, rfl⟩ | ⟨q, r, rfl⟩
      · refine ⟨0, ?_⟩
        rw [zero_add, pow_one, hP, lintegral_phKernel_zero]
        refine lt_of_lt_of_le ?_ le_self_add
        rw [hone, mul_one]
        exact ENNReal.coe_pos.2 (tsub_pos_of_lt ha)
      · exact absurd hx (by norm_num)
      · exact absurd hx (by norm_num)
      · exact absurd hx (by norm_num)
    | succ N ih =>
      intro x hx
      rcases phSpace_cases x with rfl | rfl | ⟨q, rfl⟩ | ⟨q, r, rfl⟩
      · exact ih phZero (by norm_num [phZero])
      · refine ⟨0, ?_⟩
        rw [zero_add, pow_one, hP, lintegral_phKernel_one]
        refine lt_of_lt_of_le ?_ (le_trans le_add_self le_self_add)
        rw [hone, mul_one]
        exact hb'
      · obtain ⟨n, hn⟩ := ih ⟨(q, k₀ + 1), mem_phSpace_succ q k₀⟩ (by
          have : (k₀ + 2) * (q + 1) + 1 ≤ N + 1 := hx
          change (k₀ + 2) * q + (k₀ + 1) ≤ N
          nlinarith)
        refine ⟨n + 1, lt_of_lt_of_le (ENNReal.mul_pos ?_ hn.ne')
          (ph_pow_succ_ge _ n _ _ (measurableSet_singleton _))⟩
        rw [hP, lintegral_phKernel_succ_one]
        refine (lt_of_lt_of_le ?_ (le_trans le_add_self le_self_add)).ne'
        refine lt_of_lt_of_le ?_ (mul_le_mul' le_rfl (ENNReal.le_tsum k₀))
        rw [hone, mul_one]
        exact ENNReal.mul_pos hb'.ne' hk₀
      · obtain ⟨n, hn⟩ := ih ⟨(q, r + 1), mem_phSpace_succ q r⟩ (by
          have : (k₀ + 2) * q + (r + 2) ≤ N + 1 := hx
          change (k₀ + 2) * q + (r + 1) ≤ N
          omega)
        refine ⟨n + 1, lt_of_lt_of_le (ENNReal.mul_pos ?_ hn.ne')
          (ph_pow_succ_ge _ n _ _ (measurableSet_singleton _))⟩
        rw [hP, lintegral_phKernel_two]
        refine (lt_of_lt_of_le ?_ (le_trans le_add_self le_self_add)).ne'
        rw [hone, mul_one]
        exact hb'
  exact key _ x le_rfl

/-- **`ψ`-irreducibility**: the chain is `δ₀`-irreducible. -/
theorem phKernel_isPhiIrreducible {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {a b : ℝ≥0}
    (hab : a + b < 1) (hb : 0 < b) :
    haveI := isMarkovKernel_phKernel hp hab.le
    IsPhiIrreducible (phKernel p a b) (Measure.dirac phZero) := by
  have := isMarkovKernel_phKernel hp hab.le
  intro A hA hφA x
  have h0 : phZero ∈ A := by
    by_contra h
    rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hφA
    exact lt_irrefl _ hφA
  obtain ⟨n, hn⟩ := phKernel_reach_zero hp (lt_of_le_of_lt le_self_add hab) hb x
  exact lt_of_lt_of_le (lt_of_lt_of_le hn (measure_mono (singleton_subset_iff.2 h0)))
    (pow_le_hitProb _ hA n x)

/-- Integrals from lintegrals: a nonnegative `f` with `∫ f ≤ B < ∞` (in `[0, ∞]`) is integrable
with `∫ f ≤ B`. -/
theorem ph_integral_le {μ : Measure phSpace} {f : phSpace → ℝ} (hf : ∀ y, 0 ≤ f y)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (h : ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≤ B) :
    Integrable f μ ∧ ∫ y, f y ∂μ ≤ B.toReal := by
  have hm : AEStronglyMeasurable f μ := (measurable_of_countable f).aestronglyMeasurable
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf)).2 (lt_of_le_of_lt h hB.lt_top)⟩,
    ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hm]
  exact ENNReal.toReal_mono hB h

/-- **Theorem 16.4.3** (MT p. 414): the `h`-approximation of the M/PH/1 queue is geometrically
ergodic whenever it is ergodic (`λ m < ν`, `m` the mean number of phases), provided the phase
distribution is in `G⁺(γ)`, `Σ p_k e^{γk} < ∞`. Precisely: with `a = λh`, `b = νh`,
`(λ + ν)h < 1`, and `V(i) = w(m i₁ + i₂)`, `w = 1/(b − a m)`, the chain is positive and
aperiodic, and for some `δ > 0` it is `e^{δV}`-uniformly ergodic with
`Σ rⁿ |||Pⁿ − 1 ⊗ π|||_{e^{δV}} < ∞` for every invariant probability `π`. -/
theorem theorem_16_4_3 {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {lam nu h : ℝ≥0}
    (hh : (lam + nu) * h < 1) (hh0 : 0 < h) (hergo : (lam : ℝ) * phMean p < nu) {γ : ℝ}
    (hγ : 0 < γ) (hG : ∑' k, p k * ENNReal.ofReal (Real.exp (γ * k)) ≠ ∞) :
    haveI := isMarkovKernel_phKernel hp (show lam * h + nu * h ≤ 1 by rw [← add_mul]; exact hh.le)
    ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : Measure phSpace,
      IsPositive (phKernel p (lam * h) (nu * h)) ψ ∧ IsAperiodic (phKernel p (lam * h) (nu * h)) ψ ∧
      ∀ (μ : Measure phSpace) [IsProbabilityMeasure μ],
        IsInvariant (phKernel p (lam * h) (nu * h)) μ →
        IsVUniformlyErgodic
          (fun y => ENNReal.ofReal (Real.exp (δ * phV (1 / (nu * h - lam * h * phMean p))
            (phMean p) y))) (phKernel p (lam * h) (nu * h)) μ ∧
        ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist
          (fun y => ENNReal.ofReal (Real.exp (δ * phV (1 / (nu * h - lam * h * phMean p))
            (phMean p) y))) (phKernel p (lam * h) (nu * h)) μ n ≠ ∞ := by
  set a : ℝ≥0 := lam * h with hadef
  set b : ℝ≥0 := nu * h with hbdef
  have hab : a + b < 1 := by rw [hadef, hbdef, ← add_mul]; exact hh
  have hM := isMarkovKernel_phKernel hp hab.le
  set P := phKernel p a b with hPdef
  set m := phMean p with hmdef
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  -- the mean number of phases is finite
  have hMfin : ∑' k, p k * ((k : ℝ≥0∞) + 1) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 1 + γ⁻¹)) hG) ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← Nat.cast_succ, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.add_one_le_exp (γ * k)
    have hk : (k : ℝ) ≤ Real.exp (γ * k) * γ⁻¹ := by
      rw [le_mul_inv_iff₀ hγ]
      nlinarith
    push_cast
    nlinarith [Real.add_one_le_exp (γ * k)]
  -- the weight `w`
  have hD : 0 < (b : ℝ) - a * m := by
    rw [hadef, hbdef, NNReal.coe_mul, NNReal.coe_mul]
    have := mul_lt_mul_of_pos_right hergo (NNReal.coe_pos.2 hh0)
    nlinarith
  set w : ℝ := 1 / ((b : ℝ) - a * m) with hwdef
  have hw : 0 < w := by positivity
  have hwb : w * ((b : ℝ) - a * m) = 1 := by rw [hwdef]; field_simp
  have hb1 : (b : ℝ) < 1 := by
    have : (a : ℝ) + b < 1 := by exact_mod_cast hab
    linarith [a.coe_nonneg]
  have hw1 : 1 ≤ w := by
    rw [hwdef, le_div_iff₀ hD, one_mul]
    nlinarith [a.coe_nonneg]
  have hb0 : 0 < b := by
    have : (0 : ℝ) < b := by nlinarith [a.coe_nonneg]
    exact_mod_cast this
  -- irreducibility, aperiodicity, petiteness
  have hφ := phKernel_isPhiIrreducible hp hab hb0
  have hψ := isMaximalIrreducibility_maxIrrMeasure P hφ (Measure.dirac_ne_zero)
  set ψ := maxIrrMeasure P (Measure.dirac phZero) with hψdef
  have hψ0 : 0 < ψ {phZero} := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := hψ.2.2 _ hφ h0
    rw [Measure.dirac_apply_of_mem (mem_singleton _)] at this
    exact one_ne_zero this
  have hP00 : 0 < P phZero {phZero} := by
    rw [← lintegral_indicator_one (measurableSet_singleton _), hPdef, lintegral_phKernel_zero]
    refine lt_of_lt_of_le ?_ le_self_add
    rw [indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one]
    exact ENNReal.coe_pos.2 (tsub_pos_of_lt (lt_of_le_of_lt le_self_add hab))
  obtain ⟨Mn, hMC, hMν, -⟩ := exists_minorization_of_le (P := P) (measurableSet_singleton phZero)
    ⟨phZero, rfl⟩ (ν' := P phZero) (fun x hx => by rw [mem_singleton_iff.1 hx]) hP00
  have hap : IsAperiodic P ψ := isAperiodic_of_minorization hψ Mn (by rw [hMC]; exact hψ0)
    (by rw [hMν]; exact one_pos)
  have hsmall : IsSmallSet P 1 (P phZero) {phZero} :=
    ⟨measurableSet_singleton _, one_pos, IsProbabilityMeasure.ne_zero _, fun x hx => by
      rw [mem_singleton_iff.1 hx, pow_one]⟩
  have hC : IsPetite P {phZero} := ⟨_, _, proposition_5_5_3 hsmall⟩
  -- the increment conditions
  set V : phSpace → ℝ := phV w m with hVdef
  have hV0 : ∀ x, 0 ≤ V x := phV_nonneg hw.le hm
  have hVm : Measurable V := measurable_of_countable _
  have hdrift : ∀ x, ∫⁻ y, ENNReal.ofReal (V y) ∂P x ≤ ENNReal.ofReal (V x + a * (w * m)) :=
    fun x => by
      by_cases hx : x = phZero
      · rw [hx, phKernel_drift_zero hp hMfin a b hw.le]
        refine ENNReal.ofReal_le_ofReal ?_
        linarith [hV0 phZero]
      · rw [phKernel_drift hp hMfin hab.le hw.le hwb hx]
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ (a : ℝ) * (w * m) := by positivity
        linarith
  have hint : ∀ x, Integrable V (P x) := fun x =>
    (ph_integral_le hV0 ENNReal.ofReal_ne_top (hdrift x)).1
  have hF1 : ∀ x ∉ ({phZero} : Set phSpace), ∫ y, V y ∂P x ≤ V x - 1 := fun x hx => by
    have hx' : x ≠ phZero := hx
    have h := ph_integral_le hV0 ENNReal.ofReal_ne_top
      (le_of_eq (phKernel_drift hp hMfin hab.le hw.le hwb hx'))
    refine h.2.trans (le_of_eq (ENNReal.toReal_ofReal ?_))
    -- `V x ≥ w ≥ 1` off `0`
    obtain ⟨⟨q, r⟩, hxs⟩ := x
    have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · exact absurd (Subtype.ext (Prod.ext (hxs h0) h0) : (⟨(q, r), hxs⟩ : phSpace) = phZero)
          hx'
      · exact h0
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    change 0 ≤ w * (m * q + r) - 1
    nlinarith [mul_nonneg hm (Nat.cast_nonneg (α := ℝ) q)]
  have hF2 : ∀ x ∈ ({phZero} : Set phSpace), ∫ y, V y ∂P x ≤ a * (w * m) := fun x hx => by
    rw [mem_singleton_iff.1 hx]
    have h := ph_integral_le hV0 ENNReal.ofReal_ne_top
      (le_of_eq (phKernel_drift_zero hp hMfin a b hw.le))
    exact h.2.trans (le_of_eq (ENNReal.toReal_ofReal (by positivity)))
  set β : ℝ := γ / w with hβdef
  have hβ : 0 < β := by positivity
  have hβw : β * w = γ := by rw [hβdef]; field_simp
  set Bc : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * m)) +
    ENNReal.ofReal (Real.exp γ) * ∑' k, p k * ENNReal.ofReal (Real.exp (γ * k)) + 2 with hBc
  have hBc' : Bc ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG⟩, by norm_num⟩
  have h26all : ∀ x, Integrable (fun y => Real.exp (β * (V y - V x))) (P x) ∧
      ∫ y, Real.exp (β * (V y - V x)) ∂P x ≤ Bc.toReal := fun x =>
    ph_integral_le (fun y => (Real.exp_pos _).le) hBc'
      (phKernel_exp_le hab.le hm hγ.le hβw x)
  have h26i : ∀ x, IntegrableOn (fun y => Real.exp (β * (V y - V x))) {y | V x ≤ V y} (P x) :=
    fun x => (h26all x).1.integrableOn
  have h26 : ∀ x, ∫ y in {y | V x ≤ V y}, Real.exp (β * (V y - V x)) ∂P x ≤ Bc.toReal :=
    fun x => (setIntegral_le_integral (h26all x).1 (ae_of_all _ fun y => (Real.exp_pos _).le)).trans
      (h26all x).2
  have h27all : ∀ x, Integrable ({y | V y < V x}.indicator fun y => (V y - V x) ^ 2) (P x) ∧
      ∫ y, {y | V y < V x}.indicator (fun y => (V y - V x) ^ 2) y ∂P x ≤
        (ENNReal.ofReal ((w * (m + 1)) ^ 2)).toReal := fun x =>
    ph_integral_le (fun y => indicator_nonneg (fun y _ => sq_nonneg _) y) ENNReal.ofReal_ne_top
      (phKernel_sq_le hp hab.le hw.le hm x)
  have h27i : ∀ x, IntegrableOn (fun y => (V y - V x) ^ 2) {y | V y < V x} (P x) := fun x =>
    (integrable_indicator_iff (measurableSet_lt hVm measurable_const)).1 (h27all x).1
  have h27 : ∀ x, ∫ y in {y | V y < V x}, (V y - V x) ^ 2 ∂P x ≤
      (ENNReal.ofReal ((w * (m + 1)) ^ 2)).toReal := fun x => by
    rw [← integral_indicator (measurableSet_lt hVm measurable_const)]
    exact (h27all x).2
  obtain ⟨δ, hδ0, -, hpos, hall⟩ := theorem_16_3_1 hψ hap hVm hV0 hC hβ hint hF1 hF2 h26i h26
    h27i h27
  refine ⟨δ, hδ0, ψ, hpos, hap, fun μ _ hμ => ?_⟩
  obtain ⟨-, hU, hsum⟩ := hall μ hμ
  exact ⟨hU, hsum⟩

/-- With finitely many phases (`p_k = 0` for `k ≥ N`) the phase distribution is in `G⁺(γ)` for
every `γ`. -/
theorem ph_finite_laplace {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {N : ℕ}
    (hN : ∀ k, N ≤ k → p k = 0) (γ : ℝ) :
    ∑' k, p k * ENNReal.ofReal (Real.exp (γ * k)) ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.range N) fun k hk => by
    rw [hN k (not_lt.1 (Finset.mem_range.not.1 hk)), zero_mul]]
  refine ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum k).trans (le_of_eq hp))

/-- **Finitely many phases** (MT p. 414): if `p_k = 0` for `k ≥ N`, ergodicity (`λ m < ν`) is
equivalent to geometric ergodicity for the `h`-approximation: under `λ m < ν` the conclusion of
`theorem_16_4_3` holds. -/
theorem theorem_16_4_3_finite {p : ℕ → ℝ≥0∞} (hp : ∑' k, p k = 1) {N : ℕ}
    (hN : ∀ k, N ≤ k → p k = 0) {lam nu h : ℝ≥0} (hh : (lam + nu) * h < 1) (hh0 : 0 < h)
    (hergo : (lam : ℝ) * phMean p < nu) :
    haveI := isMarkovKernel_phKernel hp (show lam * h + nu * h ≤ 1 by rw [← add_mul]; exact hh.le)
    ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : Measure phSpace,
      IsPositive (phKernel p (lam * h) (nu * h)) ψ ∧ IsAperiodic (phKernel p (lam * h) (nu * h)) ψ ∧
      ∀ (μ : Measure phSpace) [IsProbabilityMeasure μ],
        IsInvariant (phKernel p (lam * h) (nu * h)) μ →
        IsVUniformlyErgodic
          (fun y => ENNReal.ofReal (Real.exp (δ * phV (1 / (nu * h - lam * h * phMean p))
            (phMean p) y))) (phKernel p (lam * h) (nu * h)) μ ∧
        ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist
          (fun y => ENNReal.ofReal (Real.exp (δ * phV (1 / (nu * h - lam * h * phMean p))
            (phMean p) y))) (phKernel p (lam * h) (nu * h)) μ n ≠ ∞ :=
  theorem_16_4_3 hp hh hh0 hergo one_pos (ph_finite_laplace hp hN 1)

end MeynTweedie.Epilogue
