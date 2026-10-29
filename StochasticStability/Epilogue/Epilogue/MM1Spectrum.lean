/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.SpectralGap
import Epilogue.GeometricModels

/-!
# The spectrum of the M/M/1 queue (MT §20.1.2–20.1.3, Propositions 20.1.2 (i), 20.1.3)

Meyn and Tweedie, pp. 514–517. The sampled M/M/1 queue is the Bernoulli random walk on `ℤ₊`
(`bernoulliWalk p` of Chapter 15): `P(n, n + 1) = p`, `P(n, n − 1) = 1 − p`, `P(0, 0) = 1 − p`,
with load `ρ = p/(1 − p) < 1` (`p < 1/2`).

* `mm1Op` (20.8), `bernoulliWalk_eq`, `integral_bernoulliWalk`, `integral_bernoulliWalk_real`:
  the kernel acts by `Ph(n) = p h(n + 1) + (1 − p) h(n − 1)`.
* `mm1Pi`, `isProbabilityMeasure_mm1Pi`, `mm1_detailed_balance`, `IsReversible` ((20.5),
  p. 514), `isReversible_of_singleton`, `IsReversible.isInvariant`, `mm1_isReversible`: the
  geometric law `π(n) = (1 − ρ)ρⁿ` satisfies detailed balance, so the queue is reversible and `π`
  is invariant (p. 516).
* **Proposition 20.1.3 (i)** (`proposition_20_1_3_i`): `V`-uniform ergodicity for `V(n) = rⁿ`,
  `1 < r < ρ⁻¹`, at a geometric rate (Theorem 16.1.2 with (V4) at `{0}`).
* **Proposition 20.1.3 (ii)** (`proposition_20_1_3_ii`, with `mm1Op_eigfn`,
  `proposition_20_1_3_ii_eig`, `abs_mm1Eigfn_le`, `mm1_mem_spectrumV`): for
  `ρ^{−1/2} < β < r₀ < ρ⁻¹`, `λ = pβ + (1 − p)β⁻¹ ∈ (0, 1)` is an eigenvalue in `L∞_V`,
  `V(n) = r₀ⁿ`, hence in `S_V(P)`; `β₋ = ρ⁻¹/β ∈ (1, ρ^{−1/2})` is the unique second root.
* **Proposition 20.1.3 (iii)** (`proposition_20_1_3_iii_limit`, `proposition_20_1_3_iii`,
  `mm1Op_eigLim`): `λ(β)` is strictly increasing on `[ρ^{−1/2}, ∞)` and decreases to
  `2√(p(1 − p))` as `β ↓ ρ^{−1/2}`; this limit is also an eigenvalue in `L∞_V`.
* `mm1_spectralGap_not_discrete` (pp. 516–517): for `ρ^{−1/2} < r₀ < ρ⁻¹` there is a spectral gap
  (Theorem 20.1.1 (i)) but the spectrum is not discrete.
* **Proposition 20.1.2 (i)** (`proposition_20_1_2_i`, p. 515, with `IsLpGeomErgodic` (20.7)):
  the M/M/1 queue is reversible, `V`-uniformly ergodic, and not geometrically ergodic in `L¹(π)`.

**Corrections.**
* (20.9) has the coefficients of the two geometric series interchanged: the eigenfunction is
  `h(n) = (1 − β₋⁻¹)βⁿ − (1 − β⁻¹)β₋ⁿ` (`mm1Op_eigfn`), and the constant in the proof is
  `c = (1 − β⁻¹)/(1 − β₋⁻¹)`. Counterexample to the printed form: `mm1EigfnBook_counterexample`
  (`p = 1/5`, `β = 3`, `n = 0`).
* In (iii) the limiting eigenfunction is `h(n) = (1 + (1 − ρ^{−1/2})n)ρ^{−n/2}`
  (`mm1Op_eigLim`), not `(1 − (p⁻¹ − 2)n)ρ^{−n/2}`; counterexample `mm1EigLimBook_counterexample`
  (`p = 1/5`, `n = 0`).
* The proof of Proposition 20.1.2 (i) says every `λ ∈ [λ₋, 1)` is an eigenvalue with
  eigenfunction in `L∞_V`; for a fixed `V(n) = r₀ⁿ` the eigenvalues in `L∞_V` stay below
  `pr₀ + (1 − p)/r₀ < 1` (as the book itself notes on p. 517). The argument is repaired by working
  in `L¹(π)`, where `h_β` is integrable for all `β < ρ⁻¹` and `λ(β) ↑ 1`.
-/
namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ### The eigenvalue equation of the M/M/1 queue -/

/-- The M/M/1 transition operator (20.8): `Ph(n) = p h(n + 1) + (1 − p) h(n − 1)`, with
`h(0 − 1) = h(0)` (natural subtraction). -/
def mm1Op (p : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ := p * h (n + 1) + (1 - p) * h (n - 1)

/-- The eigenvalue `λ = pβ + (1 − p)β⁻¹` attached to `β` (MT p. 516). -/
noncomputable def mm1Eig (p β : ℝ) : ℝ := p * β + (1 - p) / β

/-- The second root `β₋ = (1 − p)/(pβ) = ρ⁻¹/β` of `λ = pβ + (1 − p)β⁻¹`. -/
noncomputable def mm1Conj (p β : ℝ) : ℝ := (1 - p) / (p * β)

/-- **The eigenfunction of Proposition 20.1.3 (ii), corrected**:
`h(n) = (1 − β₋⁻¹)βⁿ − (1 − β⁻¹)β₋ⁿ`. -/
noncomputable def mm1Eigfn (p β : ℝ) (n : ℕ) : ℝ :=
  (1 - (mm1Conj p β)⁻¹) * β ^ n - (1 - β⁻¹) * mm1Conj p β ^ n

/-- The function (20.9) as printed, `(1 − β⁻¹)βⁿ − (1 − β₋⁻¹)β₋ⁿ`. -/
noncomputable def mm1EigfnBook (p β : ℝ) (n : ℕ) : ℝ :=
  (1 - β⁻¹) * β ^ n - (1 - (mm1Conj p β)⁻¹) * mm1Conj p β ^ n

/-- `β₋` has the same eigenvalue as `β`. -/
theorem mm1Eig_conj {p β : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : β ≠ 0) :
    mm1Eig p (mm1Conj p β) = mm1Eig p β := by
  have h1p : 1 - p ≠ 0 := by linarith
  unfold mm1Eig mm1Conj
  field_simp
  ring

/-- Away from the boundary every geometric series solves the eigenvalue equation (MT p. 516):
`pβ^{k+2} + (1 − p)β^k = λ β^{k+1}`. -/
theorem mm1_geom (p : ℝ) {β : ℝ} (hβ : β ≠ 0) (k : ℕ) :
    p * β ^ (k + 1 + 1) + (1 - p) * β ^ k = mm1Eig p β * β ^ (k + 1) := by
  unfold mm1Eig
  field_simp
  ring

/-- `β₋ ≠ 0`. -/
theorem mm1Conj_ne_zero {p β : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : β ≠ 0) :
    mm1Conj p β ≠ 0 :=
  div_ne_zero (by linarith) (mul_ne_zero hp0.ne' hβ)

/-- **Proposition 20.1.3 (ii), the eigenfunction equation** (MT p. 516, corrected): for every
`β ≠ 0`, `Ph = λh` with `λ = pβ + (1 − p)β⁻¹` and `h = mm1Eigfn p β`. -/
theorem mm1Op_eigfn {p β : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : β ≠ 0) (n : ℕ) :
    mm1Op p (mm1Eigfn p β) n = mm1Eig p β * mm1Eigfn p β n := by
  have hγ0 := mm1Conj_ne_zero hp0 hp1 hβ
  have hγ : p * β * mm1Conj p β = 1 - p := by
    unfold mm1Conj; field_simp
  have hlam : mm1Eig p β = p * β + p * mm1Conj p β := by
    unfold mm1Eig; rw [← hγ]; field_simp
  unfold mm1Op mm1Eigfn
  rcases n with _ | k
  · simp only [zero_add, Nat.zero_sub, pow_zero, pow_one]
    rw [hlam, ← hγ]
    field_simp
    ring
  · simp only [Nat.add_sub_cancel]
    have g1 := mm1_geom p hβ k
    have g2 := mm1_geom p hγ0 k
    rw [mm1Eig_conj hp0 hp1 hβ] at g2
    linear_combination (1 - (mm1Conj p β)⁻¹) * g1 - (1 - β⁻¹) * g2

/-- **The printed (20.9) is not an eigenfunction** (`p = 1/5`, `β = 3`, `n = 0`): the
coefficients of the two geometric series are interchanged in the book. -/
theorem mm1EigfnBook_counterexample :
    mm1Op (1 / 5) (mm1EigfnBook (1 / 5) 3) 0 ≠ mm1Eig (1 / 5) 3 * mm1EigfnBook (1 / 5) 3 0 := by
  unfold mm1Op mm1EigfnBook mm1Eig mm1Conj
  norm_num

/-- The corrected limiting eigenfunction of Proposition 20.1.3 (iii):
`h(n) = (1 + (1 − s)n)sⁿ` with `s = ρ^{−1/2}`. -/
noncomputable def mm1EigLim (s : ℝ) (n : ℕ) : ℝ := (1 + (1 - s) * n) * s ^ n

/-- The limiting eigenfunction as printed: `(1 − (p⁻¹ − 2)n)ρ^{−n/2}`. -/
noncomputable def mm1EigLimBook (p s : ℝ) (n : ℕ) : ℝ := (1 - (p⁻¹ - 2) * n) * s ^ n

/-- **Proposition 20.1.3 (iii), the limiting eigenfunction, corrected** (MT p. 516): with
`s² = ρ⁻¹ = (1 − p)/p`, `h(n) = (1 + (1 − s)n)sⁿ` satisfies `Ph = 2ps h`, and
`2ps = 2√(p(1 − p))` for `s > 0`. -/
theorem mm1Op_eigLim {p s : ℝ} (hs : p * s ^ 2 = 1 - p) (n : ℕ) :
    mm1Op p (mm1EigLim s) n = 2 * p * s * mm1EigLim s n := by
  unfold mm1Op mm1EigLim
  have h1p : 1 - p = p * s ^ 2 := hs.symm
  rcases n with _ | k
  · simp only [zero_add, Nat.zero_sub, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one]
    rw [h1p]; ring
  · simp only [Nat.add_sub_cancel]
    rw [h1p]; push_cast; ring

/-- `2ps = 2√(p(1 − p))` when `s = √((1 − p)/p)`. -/
theorem two_mul_p_s {p : ℝ} (hp0 : 0 < p) :
    2 * p * Real.sqrt ((1 - p) / p) = 2 * Real.sqrt (p * (1 - p)) := by
  have h : p * (1 - p) = p ^ 2 * ((1 - p) / p) := by field_simp
  rw [h, Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp0.le]
  ring

/-- `p s² = 1 − p` for `s = √((1 − p)/p)`. -/
theorem p_mul_sqrt_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p * Real.sqrt ((1 - p) / p) ^ 2 = 1 - p := by
  rw [Real.sq_sqrt (div_nonneg (by linarith) hp0.le)]
  field_simp

/-- **The printed limiting eigenfunction is not an eigenfunction** (`p = 1/5`, `s = 2`, `n = 0`):
`P h(0) = 0 ≠ λ h(0) = 4/5`. -/
theorem mm1EigLimBook_counterexample :
    Real.sqrt ((1 - 1 / 5) / (1 / 5)) = 2 ∧
      mm1Op (1 / 5) (mm1EigLimBook (1 / 5) 2) 0 ≠
        2 * (1 / 5) * 2 * mm1EigLimBook (1 / 5) 2 0 := by
  refine ⟨?_, ?_⟩
  · rw [show (1 - 1 / 5 : ℝ) / (1 / 5) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · unfold mm1Op mm1EigLimBook
    norm_num


/-- The load `ρ = p/(1 − p)` of the M/M/1 queue (MT p. 516). -/
noncomputable def mm1Rho (p : ℝ) : ℝ := p / (1 - p)

/-- `ρ⁻¹ = (1 − p)/p`. -/
theorem mm1Rho_inv (p : ℝ) : (mm1Rho p)⁻¹ = (1 - p) / p := by
  rw [mm1Rho, inv_div]

/-- `ρ < 1` iff `p < 1/2`, and then `s = ρ^{−1/2} > 1` with `p s² = 1 − p`. -/
theorem mm1_sqrt_facts {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    1 < Real.sqrt (mm1Rho p)⁻¹ ∧ p * Real.sqrt (mm1Rho p)⁻¹ ^ 2 = 1 - p ∧
      Real.sqrt (mm1Rho p)⁻¹ ^ 2 = (1 - p) / p := by
  have hq : 1 < (1 - p) / p := by rw [one_lt_div hp0]; linarith
  rw [mm1Rho_inv]
  refine ⟨?_, ?_, Real.sq_sqrt (by linarith)⟩
  · rw [Real.lt_sqrt zero_le_one, one_pow]; exact hq
  · rw [Real.sq_sqrt (by linarith)]; field_simp

/-- **Proposition 20.1.3 (ii), the eigenvalues** (MT p. 516): for `ρ < 1` and
`ρ^{−1/2} < β < ρ⁻¹`: `λ = pβ + (1 − p)β⁻¹ ∈ (0, 1)`; `β₋ ∈ (1, ρ^{−1/2})` has the same eigenvalue
and is the only other solution in `(1, ρ^{−1/2})`; and the eigenfunction is nonzero
(`h(0) ≠ 0`). -/
theorem proposition_20_1_3_ii_eig {p β : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2)
    (hβ1 : Real.sqrt (mm1Rho p)⁻¹ < β) (hβ2 : β < (mm1Rho p)⁻¹) :
    0 < mm1Eig p β ∧ mm1Eig p β < 1 ∧ 1 < mm1Conj p β ∧
      mm1Conj p β < Real.sqrt (mm1Rho p)⁻¹ ∧ mm1Eig p (mm1Conj p β) = mm1Eig p β ∧
      (∀ γ, 1 < γ → γ < Real.sqrt (mm1Rho p)⁻¹ → mm1Eig p γ = mm1Eig p β →
        γ = mm1Conj p β) ∧ mm1Eigfn p β 0 ≠ 0 := by
  obtain ⟨hs1, -, hs2⟩ := mm1_sqrt_facts hp0 hp
  set s := Real.sqrt (mm1Rho p)⁻¹ with hsdef
  rw [mm1Rho_inv] at hβ2
  have hp1 : p < 1 := by linarith
  have hβ0 : 0 < β := by linarith
  have hβ1' : 1 < β := by linarith
  have hsq : (1 - p) / p < β ^ 2 := by
    rw [← hs2]; exact pow_lt_pow_left₀ hβ1 (by linarith) two_ne_zero
  have hsq' : 1 - p < p * β ^ 2 := by rwa [div_lt_iff₀' hp0] at hsq
  have hpβ : p * β < 1 - p := by rwa [lt_div_iff₀' hp0] at hβ2
  have hγ : mm1Conj p β = (1 - p) / (p * β) := rfl
  have hγ1 : 1 < mm1Conj p β := by rw [hγ, one_lt_div (by positivity)]; exact hpβ
  have hγ0 : 0 < mm1Conj p β := by linarith
  have hγs : mm1Conj p β < s := by
    rw [hsdef, Real.lt_sqrt hγ0.le, mm1Rho_inv, hγ, div_pow, div_lt_div_iff₀ (by positivity) hp0]
    nlinarith [mul_pos hp0 (by linarith : (0 : ℝ) < 1 - p)]
  have hlamβ : mm1Eig p β = (p * β ^ 2 + (1 - p)) / β := by
    unfold mm1Eig; field_simp
  refine ⟨?_, ?_, hγ1, hγs, mm1Eig_conj hp0 hp1 hβ0.ne', fun γ hγ1' hγs' heq => ?_, ?_⟩
  · unfold mm1Eig; have : 0 < 1 - p := by linarith
    positivity
  · rw [hlamβ, div_lt_one hβ0]; nlinarith
  · have hγ'0 : γ ≠ 0 := by linarith
    have hne : γ - β ≠ 0 := by linarith
    have hfac : p * (γ - β) * (γ - mm1Conj p β) = γ * (mm1Eig p γ - mm1Eig p β) := by
      rw [hγ]; unfold mm1Eig; field_simp; ring
    rw [heq, sub_self, mul_zero] at hfac
    have := mul_eq_zero.1 hfac
    rcases this with h | h
    · exact absurd h (mul_ne_zero hp0.ne' hne)
    · exact sub_eq_zero.1 h
  · unfold mm1Eigfn
    simp only [pow_zero, mul_one]
    intro h
    have : β⁻¹ = (mm1Conj p β)⁻¹ := by linarith
    have := inv_injective this
    linarith

/-- The eigenfunction grows at most like `rⁿ` when `β, β₋ ≤ r` (so it lies in `L∞_V`,
`V(n) = rⁿ`). -/
theorem abs_mm1Eigfn_le {p β r : ℝ} (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ mm1Conj p β) (hβr : β ≤ r)
    (hγr : mm1Conj p β ≤ r) (n : ℕ) :
    |mm1Eigfn p β n| ≤ (|1 - (mm1Conj p β)⁻¹| + |1 - β⁻¹|) * r ^ n := by
  unfold mm1Eigfn
  have h1 : β ^ n ≤ r ^ n := pow_le_pow_left₀ hβ0 hβr n
  have h2 : mm1Conj p β ^ n ≤ r ^ n := pow_le_pow_left₀ hγ0 hγr n
  calc |(1 - (mm1Conj p β)⁻¹) * β ^ n - (1 - β⁻¹) * mm1Conj p β ^ n|
      ≤ |(1 - (mm1Conj p β)⁻¹) * β ^ n| + |(1 - β⁻¹) * mm1Conj p β ^ n| := abs_sub _ _
    _ = |1 - (mm1Conj p β)⁻¹| * β ^ n + |1 - β⁻¹| * mm1Conj p β ^ n := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n), abs_of_nonneg (pow_nonneg hγ0 n)]
    _ ≤ |1 - (mm1Conj p β)⁻¹| * r ^ n + |1 - β⁻¹| * r ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = _ := by ring

/-- **Proposition 20.1.3 (iii), the limit** (MT p. 516): `λ(β) = pβ + (1 − p)β⁻¹` is strictly
increasing on `[ρ^{−1/2}, ∞)` and `λ(β) ↓ 2√(p(1 − p)) = λ(ρ^{−1/2})` as `β ↓ ρ^{−1/2}`. -/
theorem proposition_20_1_3_iii_limit {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    StrictMonoOn (mm1Eig p) (Ici (Real.sqrt (mm1Rho p)⁻¹)) ∧
      mm1Eig p (Real.sqrt (mm1Rho p)⁻¹) = 2 * Real.sqrt (p * (1 - p)) ∧
      Tendsto (mm1Eig p) (𝓝[>] (Real.sqrt (mm1Rho p)⁻¹)) (𝓝 (2 * Real.sqrt (p * (1 - p)))) := by
  obtain ⟨hs1, hps, hs2⟩ := mm1_sqrt_facts hp0 hp
  set s := Real.sqrt (mm1Rho p)⁻¹ with hsdef
  have hs0 : 0 < s := by linarith
  have hval : mm1Eig p s = 2 * Real.sqrt (p * (1 - p)) := by
    rw [← two_mul_p_s hp0, ← mm1Rho_inv, ← hsdef]
    unfold mm1Eig
    rw [← hps]
    field_simp
    ring
  refine ⟨fun a ha b hb hab => ?_, hval, ?_⟩
  · have ha0 : 0 < a := lt_of_lt_of_le hs0 ha
    have hb0 : 0 < b := ha0.trans hab
    have hab2 : s ^ 2 < a * b := by
      calc s ^ 2 = s * s := sq s
        _ ≤ a * s := mul_le_mul_of_nonneg_right ha hs0.le
        _ < a * b := mul_lt_mul_of_pos_left (lt_of_le_of_lt ha hab) ha0
    have hkey : (1 - p) < p * (a * b) := by rw [← hps]; nlinarith
    unfold mm1Eig
    rw [← sub_pos]
    have : p * b + (1 - p) / b - (p * a + (1 - p) / a) =
        (b - a) * (p * (a * b) - (1 - p)) / (a * b) := by field_simp; ring
    rw [this]
    exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos ha0 hb0)
  · rw [← hval]
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : ContinuousAt (mm1Eig p) s := by
      unfold mm1Eig
      exact (continuousAt_const.mul continuousAt_id).add
        (continuousAt_const.div continuousAt_id hs0.ne')
    exact hc.tendsto


/-! ### The M/M/1 chain: kernel, invariant law, reversibility -/

/-- The M/M/1 kernel is `P(x, ·) = p δ_{x+1} + (1 − p) δ_{x−1}`. -/
theorem bernoulliWalk_eq (p : ℝ) (x : ℕ) :
    bernoulliWalk p x = ENNReal.ofReal p • Measure.dirac (x + 1) +
      ENNReal.ofReal (1 - p) • Measure.dirac (x - 1) := by
  ext A hA
  rw [← lintegral_indicator_one hA, lintegral_bernoulliWalk, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hA, smul_eq_mul, smul_eq_mul]

/-- `∫ f dP(x, ·) = p f(x + 1) + (1 − p) f(x − 1)` for complex `f`: the M/M/1 kernel acts by
(20.8). -/
theorem integral_bernoulliWalk {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ℕ → ℂ) (x : ℕ) :
    ∫ y, f y ∂bernoulliWalk p x = (p : ℂ) * f (x + 1) + ((1 - p : ℝ) : ℂ) * f (x - 1) := by
  have hi : ∀ (c : ℝ) (n : ℕ), Integrable f (ENNReal.ofReal c • Measure.dirac n) := fun c n =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [bernoulliWalk_eq, integral_add_measure (hi _ _) (hi _ _), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (by linarith), Complex.real_smul, Complex.real_smul]

/-- `P(x, {y})` as a real number: `p 1{y = x + 1} + (1 − p) 1{y = x − 1}`. -/
theorem bernoulliWalk_singleton_eq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : ℕ) :
    bernoulliWalk p x {y} = ENNReal.ofReal (p * (if x + 1 = y then 1 else 0) +
      (1 - p) * (if x - 1 = y then 1 else 0)) := by
  rw [bernoulliWalk_singleton, ENNReal.ofReal_add (by positivity) (by
    have : 0 ≤ 1 - p := by linarith
    positivity), ENNReal.ofReal_mul hp0, ENNReal.ofReal_mul (by linarith)]
  congr 2
  · by_cases h : x + 1 = y
    · rw [indicator_of_mem (mem_singleton_iff.2 h), Pi.one_apply, ite_eq_left h, ENNReal.ofReal_one]
    · rw [indicator_of_notMem (fun h' => h (mem_singleton_iff.1 h')), ite_eq_right h,
        ENNReal.ofReal_zero]
  · by_cases h : x - 1 = y
    · rw [indicator_of_mem (mem_singleton_iff.2 h), Pi.one_apply, ite_eq_left h, ENNReal.ofReal_one]
    · rw [indicator_of_notMem (fun h' => h (mem_singleton_iff.1 h')), ite_eq_right h,
        ENNReal.ofReal_zero]

/-- The geometric weights `π(n) = (1 − ρ)ρⁿ` (MT p. 516). -/
noncomputable def mm1W (p : ℝ) (n : ℕ) : ℝ := (1 - mm1Rho p) * mm1Rho p ^ n

/-- **The invariant law of the M/M/1 queue**, `π(n) = (1 − ρ)ρⁿ` (MT p. 516). -/
noncomputable def mm1Pi (p : ℝ) : Measure ℕ :=
  Measure.sum fun n => ENNReal.ofReal (mm1W p n) • Measure.dirac n

/-- `π{n} = (1 − ρ)ρⁿ`. -/
theorem mm1Pi_singleton (p : ℝ) (y : ℕ) : mm1Pi p {y} = ENNReal.ofReal (mm1W p y) := by
  rw [mm1Pi, Measure.sum_apply _ (measurableSet_singleton y)]
  rw [tsum_eq_single y fun n hn => by
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
      indicator_of_notMem (fun h => hn (mem_singleton_iff.1 h)), smul_zero]]
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton y), smul_eq_mul, mul_one]

/-- For `0 < p < 1/2`, `0 < ρ < 1` and `ρ(1 − p) = p`. -/
theorem mm1Rho_facts {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    0 < mm1Rho p ∧ mm1Rho p < 1 ∧ mm1Rho p * (1 - p) = p := by
  have h1p : 0 < 1 - p := by linarith
  refine ⟨div_pos hp0 h1p, (div_lt_one h1p).2 (by linarith), ?_⟩
  rw [mm1Rho]; field_simp

/-- `π` is a probability measure. -/
theorem isProbabilityMeasure_mm1Pi {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    IsProbabilityMeasure (mm1Pi p) := by
  obtain ⟨hρ0, hρ1, -⟩ := mm1Rho_facts hp0 hp
  constructor
  rw [mm1Pi, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, mm1W]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by linarith) (pow_nonneg hρ0.le n))
    ((summable_geometric_of_lt_one hρ0.le hρ1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one hρ0.le hρ1, mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one]


/-- **Detailed balance** (20.5) for the M/M/1 queue (MT p. 516): `π(x)P(x, y) = π(y)P(y, x)`. -/
theorem mm1_detailed_balance {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (x y : ℕ) :
    mm1Pi p {x} * bernoulliWalk p x {y} = mm1Pi p {y} * bernoulliWalk p y {x} := by
  obtain ⟨hρ0, hρ1, hρp⟩ := mm1Rho_facts hp0 hp
  have hw : ∀ n, 0 ≤ mm1W p n := fun n => mul_nonneg (by linarith) (pow_nonneg hρ0.le n)
  have hp1 : p ≤ 1 := by linarith
  rw [mm1Pi_singleton, mm1Pi_singleton, bernoulliWalk_singleton_eq hp0.le hp1,
    bernoulliWalk_singleton_eq hp0.le hp1, ← ENNReal.ofReal_mul (hw x),
    ← ENNReal.ofReal_mul (hw y)]
  congr 1
  unfold mm1W
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · by_cases hy : y = x + 1
    · subst hy
      rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega), pow_succ]
      linear_combination -(1 - mm1Rho p) * mm1Rho p ^ x * hρp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      ring
  · rfl
  · by_cases hx : x = y + 1
    · subst hx
      rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left rfl,
        ite_eq_right (by omega), pow_succ]
      linear_combination (1 - mm1Rho p) * mm1Rho p ^ y * hρp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      ring

/-- **Reversibility** (20.5), MT p. 514: `π(dx)P(x, dy) = π(dy)P(y, dx)`, i.e.
`∫_A P(x, B) π(dx) = ∫_B P(x, A) π(dx)` for all measurable `A`, `B`. -/
def IsReversible {X : Type*} [MeasurableSpace X] (P : Kernel X X) (μ : Measure X) : Prop :=
  ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, P x B ∂μ = ∫⁻ x in B, P x A ∂μ

/-- On a countable space, `P(x, A) = Σ_y 1_A(y) P(x, {y})`. -/
theorem measure_eq_tsum_singleton {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    μ A = ∑' y, A.indicator 1 y * μ {y} := by
  rw [← lintegral_indicator_one hA, lintegral_countable']

/-- **Detailed balance on singletons gives reversibility** on a countable space. -/
theorem isReversible_of_singleton {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (P : Kernel X X) (μ : Measure X)
    (h : ∀ x y, μ {x} * P x {y} = μ {y} * P y {x}) : IsReversible P μ := by
  intro A B hA hB
  rw [← lintegral_indicator hA, ← lintegral_indicator hB, lintegral_countable',
    lintegral_countable']
  have hexp : ∀ (C D : Set X), MeasurableSet D → ∀ x,
      C.indicator (fun x => P x D) x * μ {x} =
        ∑' y, C.indicator 1 x * D.indicator 1 y * (μ {x} * P x {y}) := fun C D hD x => by
    classical
    rw [indicator_apply]
    split_ifs with hx
    · rw [measure_eq_tsum_singleton (P x) hD, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun y => ?_
      rw [indicator_of_mem hx, Pi.one_apply, one_mul]
      ring
    · rw [zero_mul]
      refine (ENNReal.tsum_eq_zero.2 fun y => ?_).symm
      rw [indicator_of_notMem hx, zero_mul, zero_mul]
  simp_rw [hexp A B hB, hexp B A hA]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => tsum_congr fun y => ?_
  rw [h y x]
  ring

/-- **Reversibility gives invariance** (`B = X`, MT p. 514). -/
theorem IsReversible.isInvariant {X : Type*} [MeasurableSpace X] {P : Kernel X X}
    [IsMarkovKernel P] {μ : Measure X} (h : IsReversible P μ) : IsInvariant P μ := by
  refine (isInvariant_iff P μ).2 fun A hA => ?_
  have := h univ A MeasurableSet.univ hA
  rw [Measure.restrict_univ] at this
  rw [this]
  simp_rw [measure_univ]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]

/-- **The M/M/1 queue is reversible**, hence `π` is invariant (MT p. 516). -/
theorem mm1_isReversible {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    IsReversible (bernoulliWalk p) (mm1Pi p) ∧ IsInvariant (bernoulliWalk p) (mm1Pi p) := by
  have := isMarkovKernel_bernoulliWalk hp0.le (by linarith : p ≤ 1)
  have hrev := isReversible_of_singleton _ _ (mm1_detailed_balance hp0 hp)
  exact ⟨hrev, hrev.isInvariant⟩


/-! ### `V`-uniform ergodicity and the spectrum in `L∞_V`, `V(n) = r₀ⁿ` -/

/-- `pr + (1 − p)/r < 1` for `1 < r < ρ⁻¹`. -/
theorem mm1_rate_lt_one {p r : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (hr1 : 1 < r)
    (hr : r < (mm1Rho p)⁻¹) : p * r + (1 - p) / r < 1 := by
  rw [mm1Rho_inv, lt_div_iff₀' hp0] at hr
  have hr0 : 0 < r := by linarith
  rw [show p * r + (1 - p) / r = (p * r ^ 2 + (1 - p)) / r by field_simp, div_lt_one hr0]
  nlinarith

/-- **Proposition 20.1.3 (i)** (MT p. 516): for `ρ < 1` and `1 < r₀ < ρ⁻¹`, the M/M/1 queue is
`V`-uniformly ergodic with `V(n) = r₀ⁿ`, at a geometric rate (16.3). -/
theorem proposition_20_1_3_i {p r : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (hr1 : 1 < r)
    (hr : r < (mm1Rho p)⁻¹) :
    haveI := isMarkovKernel_bernoulliWalk hp0.le (by linarith : p ≤ 1)
    IsVUniformlyErgodic (eW fun n : ℕ => r ^ n) (bernoulliWalk p) (mm1Pi p) ∧
      ∃ t : ℝ≥0∞, 1 < t ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧
        ∀ n, vErgDist (eW fun n : ℕ => r ^ n) (bernoulliWalk p) (mm1Pi p) n ≤ R * t⁻¹ ^ n := by
  have hp1 : p < 1 := by linarith
  have := isMarkovKernel_bernoulliWalk hp0.le hp1.le
  have := isProbabilityMeasure_mm1Pi hp0 hp
  have hdrift := bernoulliWalk_driftV4 hp0.le hp1.le hr1.le
  have hψ := isMaximalIrreducibility_count _ (bernoulliWalk_isIrreducibleChain hp0 hp1)
  have hδ0 : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (by linarith)
  have hδ1 : ENNReal.ofReal (1 - p) < 1 := by
    rw [ENNReal.ofReal_lt_one]; linarith
  let M : Minorization (bernoulliWalk p) :=
    { C := {0}, δ := ENNReal.ofReal (1 - p), ν := Measure.dirac 0,
      measurableSet_C := measurableSet_singleton 0, δ_pos := hδ0, δ_lt_one := hδ1,
      isProbabilityMeasure_ν := inferInstance,
      le := fun x hx => Measure.le_intro fun A _ _ => by
        rw [mem_singleton_iff.1 hx, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' _ (by measurability),
          ← lintegral_indicator_one (by measurability), lintegral_bernoulliWalk]
        exact le_add_self }
  have hap : IsAperiodic (bernoulliWalk p) Measure.count :=
    isAperiodic_of_minorization hψ M (by simp [M]) (by simp [M])
  have hV1 : ∀ x : ℕ, 1 ≤ ENNReal.ofReal (r ^ x) := fun x =>
    ENNReal.one_le_ofReal.2 (one_le_pow₀ hr1.le)
  have hC : IsPetite (bernoulliWalk p) {0} := (isAtom_singleton _ 0).isPetite ⟨0, rfl⟩
  have hinv := (mm1_isReversible hp0 hp).2
  obtain ⟨-, t, ht, -, R, hR, hb⟩ := vErgDist_le_of_driftV4 hψ hap (measurable_of_countable _)
    hV1 (fun _ => ENNReal.ofReal_ne_top) (ENNReal.ofReal_lt_one.2 (mm1_rate_lt_one hp0 hp hr1 hr))
    ENNReal.ofReal_ne_top hC hdrift (mm1Pi p) hinv
  refine ⟨⟨hinv, ?_⟩, t, ht, R, hR, hb⟩
  have ht1 : t⁻¹ < 1 := ENNReal.inv_lt_one.2 ht
  have hlim : Tendsto (fun n => R * t⁻¹ ^ n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ht1)
      (Or.inr hR)
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

/-- `V(n) = rⁿ` (`r ≥ 1`) is admissible for the M/M/1 kernel: `PV ≤ (pr + 1)V`. -/
theorem mm1_weightOK {p r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) :
    WeightOK (fun n : ℕ => r ^ n) (bernoulliWalk p) := by
  have hr0 : 0 ≤ r := by linarith
  refine ⟨measurable_of_countable _, fun n => one_le_pow₀ hr1, p * r + 1, by positivity,
    fun x => ?_⟩
  rw [lintegral_bernoulliWalk, ← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) (by positivity))]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : r ^ (x - 1) ≤ r ^ x := pow_le_pow_right₀ hr1 (Nat.sub_le x 1)
  have h2 : (1 - p) * r ^ (x - 1) ≤ 1 * r ^ x :=
    mul_le_mul (by linarith) h1 (by positivity) zero_le_one
  change p * r ^ (x + 1) + (1 - p) * r ^ (x - 1) ≤ (p * r + 1) * r ^ x
  rw [pow_succ]
  nlinarith [pow_nonneg hr0 x]

/-- **Eigenfunctions in `L∞_V` give points of `S_V(P)`** for the M/M/1 queue: if
`|h(n)| ≤ C rⁿ`, `Ph = λh` (20.8) and `h ≠ 0`, then `λ ∈ S_V(P)` for `V(n) = rⁿ`. -/
theorem mm1_mem_spectrumV {p r C lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    {h : ℕ → ℝ} (hbd : ∀ n, |h n| ≤ C * r ^ n) (heig : ∀ n, mm1Op p h n = lam * h n)
    (hne : ∃ n, h n ≠ 0) : (lam : ℂ) ∈ spectrumV (fun n : ℕ => r ^ n) (bernoulliWalk p) := by
  have hr0 : 0 < r := by linarith
  have hW := mm1_weightOK hp0 hp1 hr1
  have hfb : ∀ n, ‖((h n / r ^ n : ℝ) : ℂ)‖ ≤ C := fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hr0 n),
      div_le_iff₀ (pow_pos hr0 n)]
    exact hbd n
  set g : BM ℕ := mkBM (fun n => ((h n / r ^ n : ℝ) : ℂ)) (measurable_of_countable _) C hfb
  have hgV : ∀ y, bmFun g y * ((r ^ y : ℝ) : ℂ) = (h y : ℂ) := fun y => by
    rw [bmFun_mkBM, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos hr0 y).ne']
  refine mem_spectrum_of_apply_eq (E := BM ℕ) _ (h := g) ?_ ?_
  · obtain ⟨n, hn⟩ := hne
    intro h0
    have := congrArg (fun w => bmFun w n) h0
    simp only [bmFun_zero] at this
    rw [bmFun_mkBM, Complex.ofReal_eq_zero, div_eq_zero_iff] at this
    rcases this with h1 | h1
    · exact hn h1
    · exact (pow_pos hr0 n).ne' h1
  · refine bm_ext fun x => ?_
    rw [kOp_apply hW, kFun, bmFun_smul, integral_bernoulliWalk hp0 hp1]
    rw [hgV, hgV, bmFun_mkBM]
    have hm := congrArg (fun t : ℝ => (t : ℂ)) (heig x)
    simp only [mm1Op, Complex.ofReal_add, Complex.ofReal_mul] at hm
    rw [hm, Complex.ofReal_div]
    have : ((r ^ x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_pos hr0 x).ne'
    field_simp


/-- **Proposition 20.1.3 (ii)** (MT p. 516, corrected): for `ρ < 1`, `r₀ < ρ⁻¹` and
`ρ^{−1/2} < β < r₀`, the number `λ = pβ + (1 − p)β⁻¹ ∈ (0, 1)` lies in `S_V(P)`,
`V(n) = r₀ⁿ`: it is an eigenvalue in `L∞_V` with eigenfunction
`h = (1 − β₋⁻¹)βⁿ − (1 − β⁻¹)β₋ⁿ`, where `β₋ ∈ (1, ρ^{−1/2})` is the second root. -/
theorem proposition_20_1_3_ii {p r β : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2)
    (hr : r < (mm1Rho p)⁻¹) (hβ1 : Real.sqrt (mm1Rho p)⁻¹ < β) (hβr : β < r) :
    (mm1Eig p β : ℂ) ∈ spectrumV (fun n : ℕ => r ^ n) (bernoulliWalk p) ∧
      0 < mm1Eig p β ∧ mm1Eig p β < 1 ∧
      (∀ n, mm1Op p (mm1Eigfn p β) n = mm1Eig p β * mm1Eigfn p β n) ∧
      (∃ C, ∀ n, |mm1Eigfn p β n| ≤ C * r ^ n) ∧
      1 < mm1Conj p β ∧ mm1Conj p β < Real.sqrt (mm1Rho p)⁻¹ ∧
      mm1Eig p (mm1Conj p β) = mm1Eig p β := by
  obtain ⟨hs1, -, -⟩ := mm1_sqrt_facts hp0 hp
  obtain ⟨hl0, hl1, hγ1, hγs, hconj, -, hne⟩ :=
    proposition_20_1_3_ii_eig hp0 hp hβ1 (hβr.trans hr)
  have hβ0 : 0 < β := by linarith
  have heig := mm1Op_eigfn hp0 (by linarith) hβ0.ne'
  have hbd := abs_mm1Eigfn_le (p := p) hβ0.le (by linarith) hβr.le (by linarith)
  exact ⟨mm1_mem_spectrumV hp0.le (by linarith) (by linarith) hbd heig ⟨0, hne⟩, hl0, hl1,
    heig, ⟨_, hbd⟩, hγ1, hγs, hconj⟩

/-- **Proposition 20.1.3 (iii)** (MT p. 516, corrected): the limiting value
`λ = 2√(p(1 − p))` is also in `S_V(P)`, an eigenvalue with eigenfunction
`h(n) = (1 + (1 − ρ^{−1/2})n)ρ^{−n/2}` (the printed `(1 − (p⁻¹ − 2)n)ρ^{−n/2}` is not an
eigenfunction: `mm1EigLimBook_counterexample`). -/
theorem proposition_20_1_3_iii {p r : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2)
    (hrs : Real.sqrt (mm1Rho p)⁻¹ < r) :
    ((2 * Real.sqrt (p * (1 - p)) : ℝ) : ℂ) ∈ spectrumV (fun n : ℕ => r ^ n) (bernoulliWalk p) ∧
      (∀ n, mm1Op p (mm1EigLim (Real.sqrt (mm1Rho p)⁻¹)) n =
        2 * Real.sqrt (p * (1 - p)) * mm1EigLim (Real.sqrt (mm1Rho p)⁻¹) n) ∧
      ∃ C, ∀ n, |mm1EigLim (Real.sqrt (mm1Rho p)⁻¹) n| ≤ C * r ^ n := by
  obtain ⟨hs1, hps, -⟩ := mm1_sqrt_facts hp0 hp
  set s := Real.sqrt (mm1Rho p)⁻¹ with hsdef
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < r := by linarith
  have hlam2 : 2 * p * s = 2 * Real.sqrt (p * (1 - p)) := by
    rw [hsdef, mm1Rho_inv]; exact two_mul_p_s hp0
  have heig : ∀ n, mm1Op p (mm1EigLim s) n = 2 * Real.sqrt (p * (1 - p)) * mm1EigLim s n :=
    fun n => by rw [← hlam2]; exact mm1Op_eigLim hps n
  set q := s / r with hq
  have hq0 : 0 ≤ q := div_nonneg hs0.le hr0.le
  have hq1 : q < 1 := (div_lt_one hr0).2 hrs
  have hlim : Tendsto (fun n : ℕ => q ^ n + |1 - s| * (n * q ^ n)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).add
      ((tendsto_self_mul_const_pow_of_lt_one hq0 hq1).const_mul |1 - s|)
    rwa [mul_zero, add_zero] at this
  obtain ⟨C, hC⟩ := hlim.bddAbove_range
  have hbd : ∀ n, |mm1EigLim s n| ≤ C * r ^ n := fun n => by
    have hCn : q ^ n + |1 - s| * (n * q ^ n) ≤ C := hC ⟨n, rfl⟩
    unfold mm1EigLim
    rw [abs_mul, abs_of_pos (pow_pos hs0 n)]
    have hsn : s ^ n = q ^ n * r ^ n := by rw [hq, div_pow, div_mul_cancel₀ _ (pow_pos hr0 n).ne']
    calc |1 + (1 - s) * n| * s ^ n ≤ (1 + |1 - s| * n) * s ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hs0.le n)
          calc |1 + (1 - s) * n| ≤ |1| + |(1 - s) * n| := abs_add_le _ _
            _ = 1 + |1 - s| * n := by rw [abs_one, abs_mul, Nat.abs_cast]
      _ = (q ^ n + |1 - s| * (n * q ^ n)) * r ^ n := by rw [hsn]; ring
      _ ≤ C * r ^ n := mul_le_mul_of_nonneg_right hCn (pow_nonneg hr0.le n)
  refine ⟨mm1_mem_spectrumV hp0.le (by linarith) (by linarith) hbd heig ⟨0, ?_⟩, heig, C, hbd⟩
  unfold mm1EigLim; norm_num

/-- **The M/M/1 queue has a spectral gap but not a discrete spectrum** in `L∞_V`,
`V(n) = r₀ⁿ`, `ρ^{−1/2} < r₀ < ρ⁻¹` (MT pp. 516–517): every `λ(β)`, `β ∈ (ρ^{−1/2}, r₀)`, lies in
`S_V(P)` with `|λ(β)| > 2√(p(1 − p))`, infinitely many points. -/
theorem mm1_spectralGap_not_discrete {p r : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2)
    (hrs : Real.sqrt (mm1Rho p)⁻¹ < r) (hr : r < (mm1Rho p)⁻¹) :
    HasSpectralGap (E := BM ℕ) (kOp (fun n : ℕ => r ^ n) (bernoulliWalk p)) ∧
      ¬ HasDiscreteSpectrum (E := BM ℕ) (kOp (fun n : ℕ => r ^ n) (bernoulliWalk p)) := by
  have hp1 : p < 1 := by linarith
  have := isMarkovKernel_bernoulliWalk hp0.le hp1.le
  have := isProbabilityMeasure_mm1Pi hp0 hp
  obtain ⟨hs1, -, -⟩ := mm1_sqrt_facts hp0 hp
  have hr1 : 1 < r := by linarith
  obtain ⟨-, hrate⟩ := proposition_20_1_3_i hp0 hp hr1 hr
  obtain ⟨-, -, -, -, -, -, hgap⟩ := theorem_20_1_1_i (mm1_isReversible hp0 hp).2
    (measurable_of_countable (fun n : ℕ => r ^ n)) (fun n => one_le_pow₀ hr1.le) hrate
  refine ⟨hgap, fun hd => ?_⟩
  obtain ⟨hmono, hval, -⟩ := proposition_20_1_3_iii_limit hp0 hp
  set s := Real.sqrt (mm1Rho p)⁻¹ with hsdef
  have hε : 0 < 2 * Real.sqrt (p * (1 - p)) := by
    have : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
    positivity
  obtain ⟨hfin, -⟩ := hd _ hε
  have hsub : (fun β : ℝ => (mm1Eig p β : ℂ)) '' Ioo s r ⊆
      {z ∈ spectrum ℂ (kOp (fun n : ℕ => r ^ n) (bernoulliWalk p)) |
        2 * Real.sqrt (p * (1 - p)) ≤ ‖z‖} := by
    rintro _ ⟨β, ⟨hβ1, hβ2⟩, rfl⟩
    refine ⟨(proposition_20_1_3_ii hp0 hp hr hβ1 hβ2).1, ?_⟩
    have hlt : mm1Eig p s < mm1Eig p β := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hβ1.le) hβ1
    rw [hval] at hlt
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hlt.le.trans (le_abs_self _)
  have hinj : InjOn (fun β : ℝ => (mm1Eig p β : ℂ)) (Ioo s r) := fun a ha b hb hab =>
    (hmono.injOn) (mem_Ici.2 (le_of_lt ha.1)) (mem_Ici.2 (le_of_lt hb.1))
      (Complex.ofReal_injective hab)
  exact ((Ioo_infinite hrs).image hinj).mono hsub hfin


/-! ### Proposition 20.1.2 (i): not geometrically ergodic in `L¹(π)` -/

/-- **Geometric ergodicity in `Lᵖ(π)`** (20.7), MT p. 514, in norm form:
`‖Pⁿf − π(f)‖_p ≤ R r⁻ⁿ ‖f‖_p` for all `f ∈ Lᵖ(π)`, `n ≥ 0`, some `r > 1`. (For `p = 1` this is
(20.7) as printed; for `p > 1` the book raises both sides to the power `p`.) -/
def IsLpGeomErgodic {X : Type*} [MeasurableSpace X] (P : Kernel X X) (μ : Measure X)
    (q : ℝ≥0∞) : Prop :=
  ∃ r : ℝ, 1 < r ∧ ∃ R : ℝ, ∀ (n : ℕ) (f : X → ℝ), MemLp f q μ →
    eLpNorm (fun x => ∫ y, f y ∂(P ^ n) x - ∫ y, f y ∂μ) q μ ≤
      ENNReal.ofReal (R * r⁻¹ ^ n) * eLpNorm f q μ

/-- `∫ f dP(x, ·) = p f(x + 1) + (1 − p) f(x − 1)` for real `f` (20.8). -/
theorem integral_bernoulliWalk_real {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ℕ → ℝ) (x : ℕ) :
    ∫ y, f y ∂bernoulliWalk p x = mm1Op p f x := by
  have hi : ∀ (c : ℝ) (n : ℕ), Integrable f (ENNReal.ofReal c • Measure.dirac n) := fun c n =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [bernoulliWalk_eq, integral_add_measure (hi _ _) (hi _ _), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul, mm1Op]

/-- Integrating against an invariant law: `∫ (Pf) dπ = ∫ f dπ`. -/
theorem integral_kernel_of_isInvariant {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] (μ : Measure X) [IsProbabilityMeasure μ] (hinv : IsInvariant P μ)
    {f : X → ℝ} (hf : Integrable f μ) : ∫ x, (∫ y, f y ∂P x) ∂μ = ∫ y, f y ∂μ := by
  have e : (P ∘ₖ Kernel.const Unit μ) () = μ := by
    rw [Kernel.comp_const, Kernel.const_apply]; exact hinv
  have h := Kernel.integral_comp (η := P) (κ := Kernel.const Unit μ) (a := ())
    (by rw [e]; exact hf)
  rw [e, Kernel.const_apply] at h
  exact h.symm

/-- `∫ h dPⁿ(x, ·) = λⁿ h(x)` for the M/M/1 eigenfunction, with `h` integrable for `Pⁿ(x, ·)`. -/
theorem mm1_integral_pow {p β : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ1 : 1 ≤ β)
    (hγ0 : 0 ≤ mm1Conj p β) (hγβ : mm1Conj p β ≤ β) (n : ℕ) (x : ℕ) :
    Integrable (mm1Eigfn p β) ((bernoulliWalk p ^ n) x) ∧
      ∫ y, mm1Eigfn p β y ∂(bernoulliWalk p ^ n) x = mm1Eig p β ^ n * mm1Eigfn p β x := by
  have := isMarkovKernel_bernoulliWalk hp0.le hp1.le
  have hβ0 : 0 < β := by linarith
  have hW := mm1_weightOK hp0.le hp1.le hβ1
  have hbd := abs_mm1Eigfn_le (p := p) hβ0.le hγ0 le_rfl hγβ
  have hint : ∀ m y, Integrable (mm1Eigfn p β) ((bernoulliWalk p ^ m) y) := fun m y =>
    Integrable.mono' (((kOp_pow hW m).1.integrable_V y).const_mul _)
      (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun k => by rw [Real.norm_eq_abs]; exact hbd k)
  refine ⟨hint n x, ?_⟩
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply, integral_dirac, pow_zero, one_mul]
  | succ n ih =>
    have hc : bernoulliWalk p ^ (n + 1) = (bernoulliWalk p ^ n) ∘ₖ bernoulliWalk p :=
      pow_succ _ n
    have hi := hint (n + 1) x
    rw [hc] at hi ⊢
    rw [Kernel.integral_comp hi]
    rw [integral_congr_ae (g := fun y => mm1Eig p β ^ n * mm1Eigfn p β y)
      (Eventually.of_forall fun y => ih y), integral_const_mul,
      integral_bernoulliWalk_real hp0.le hp1.le, mm1Op_eigfn hp0 hp1 hβ0.ne', pow_succ]
    ring

/-- A function bounded by `C βⁿ` with `ρβ < 1` is `π`-integrable. -/
theorem mm1_integrable_pi {p β C : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (hβ0 : 0 ≤ β)
    (hρβ : mm1Rho p * β < 1) {h : ℕ → ℝ} (hbd : ∀ n, |h n| ≤ C * β ^ n) :
    Integrable h (mm1Pi p) := by
  obtain ⟨hρ0, hρ1, -⟩ := mm1Rho_facts hp0 hp
  have hC : 0 ≤ C := by
    have := hbd 0
    rw [pow_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hq0 : 0 ≤ mm1Rho p * β := mul_nonneg hρ0.le hβ0
  refine ⟨(measurable_of_countable h).aestronglyMeasurable, ?_⟩
  change ∫⁻ n, ‖h n‖ₑ ∂mm1Pi p < ∞
  rw [lintegral_countable']
  have hsum : Summable fun n : ℕ => C * (1 - mm1Rho p) * (mm1Rho p * β) ^ n :=
    (summable_geometric_of_lt_one hq0 hρβ).mul_left _
  calc ∑' n, ‖h n‖ₑ * mm1Pi p {n}
      ≤ ∑' n, ENNReal.ofReal (C * (1 - mm1Rho p) * (mm1Rho p * β) ^ n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [mm1Pi_singleton, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        unfold mm1W
        calc |h n| * ((1 - mm1Rho p) * mm1Rho p ^ n)
            ≤ C * β ^ n * ((1 - mm1Rho p) * mm1Rho p ^ n) :=
              mul_le_mul_of_nonneg_right (hbd n)
                (mul_nonneg (by linarith) (pow_nonneg hρ0.le n))
          _ = C * (1 - mm1Rho p) * (mm1Rho p * β) ^ n := by rw [mul_pow]; ring
    _ = ENNReal.ofReal (∑' n, C * (1 - mm1Rho p) * (mm1Rho p * β) ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (mul_nonneg hC (by linarith))
          (pow_nonneg hq0 n)) hsum).symm
    _ < ∞ := ENNReal.ofReal_lt_top


/-- `λ(ρ⁻¹) = 1`: the eigenvalues approach `1` as `β ↑ ρ⁻¹`. -/
theorem mm1Eig_rho_inv {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : mm1Eig p (mm1Rho p)⁻¹ = 1 := by
  rw [mm1Rho_inv]
  unfold mm1Eig
  have : 1 - p ≠ 0 := by linarith
  field_simp
  ring

/-- **Proposition 20.1.2 (i)** (MT p. 515): the M/M/1 queue with `ρ < 1` is a reversible chain
that is `V`-uniformly ergodic (`V(n) = rⁿ`, any `1 < r < ρ⁻¹`) but not geometrically ergodic in
`L¹(π)`. The proof uses the eigenfunctions `h_β ∈ L¹(π)`, `ρ^{−1/2} < β < ρ⁻¹`, whose eigenvalues
`λ(β) ↑ 1` as `β ↑ ρ⁻¹`, with `π(h_β) = 0` and `‖Pⁿh_β‖₁ = λ(β)ⁿ‖h_β‖₁`. (For a fixed `V` the
eigenvalues in `L∞_V` stay below `pr₀ + (1 − p)/r₀ < 1`; it is in `L¹(π)` that they reach
`1`.) -/
theorem proposition_20_1_2_i {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    haveI := isMarkovKernel_bernoulliWalk hp0.le (by linarith : p ≤ 1)
    IsReversible (bernoulliWalk p) (mm1Pi p) ∧
      (∀ r : ℝ, 1 < r → r < (mm1Rho p)⁻¹ →
        IsVUniformlyErgodic (eW fun n : ℕ => r ^ n) (bernoulliWalk p) (mm1Pi p)) ∧
      ¬ IsLpGeomErgodic (bernoulliWalk p) (mm1Pi p) 1 := by
  have hp1 : p < 1 := by linarith
  have := isMarkovKernel_bernoulliWalk hp0.le hp1.le
  have := isProbabilityMeasure_mm1Pi hp0 hp
  obtain ⟨hrev, hinv⟩ := mm1_isReversible hp0 hp
  refine ⟨hrev, fun r hr1 hr => (proposition_20_1_3_i hp0 hp hr1 hr).1, ?_⟩
  rintro ⟨r, hr, R, hR⟩
  obtain ⟨hs1, -, -⟩ := mm1_sqrt_facts hp0 hp
  obtain ⟨hρ0, hρ1, -⟩ := mm1Rho_facts hp0 hp
  set s := Real.sqrt (mm1Rho p)⁻¹ with hsdef
  have hρinv1 : 1 < (mm1Rho p)⁻¹ := one_lt_inv₀ hρ0 |>.2 hρ1
  have hsρ : s < (mm1Rho p)⁻¹ := by
    rw [hsdef, Real.sqrt_lt' (by linarith)]
    nlinarith
  -- choose `β` close to `ρ⁻¹` with `λ(β) > r⁻¹`
  have hcont : ContinuousAt (mm1Eig p) (mm1Rho p)⁻¹ := by
    unfold mm1Eig
    exact (continuousAt_const.mul continuousAt_id).add
      (continuousAt_const.div continuousAt_id (by positivity))
  have hlim : Tendsto (mm1Eig p) (𝓝[<] (mm1Rho p)⁻¹) (𝓝 1) := by
    rw [← mm1Eig_rho_inv hp0 hp1]; exact tendsto_nhdsWithin_of_tendsto_nhds hcont
  have hr1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  obtain ⟨β, hβlam, hβs⟩ := ((hlim.eventually (lt_mem_nhds hr1)).and
    (Ioo_mem_nhdsLT hsρ)).exists
  obtain ⟨hβ1, hβ2⟩ := hβs
  obtain ⟨hl0, hl1, hγ1, hγs, -, -, hne⟩ := proposition_20_1_3_ii_eig hp0 hp hβ1 hβ2
  set lam := mm1Eig p β with hlam
  set h := mm1Eigfn p β with hh
  have hβ0 : 0 < β := by linarith
  have hbd := abs_mm1Eigfn_le (p := p) hβ0.le (by linarith) le_rfl (by linarith)
  have hρβ : mm1Rho p * β < 1 := by
    have := mul_lt_mul_of_pos_left hβ2 hρ0
    rwa [mul_inv_cancel₀ hρ0.ne'] at this
  have hint : Integrable h (mm1Pi p) := mm1_integrable_pi hp0 hp hβ0.le hρβ hbd
  have hpow := mm1_integral_pow (β := β) hp0 hp1 (by linarith) (by linarith) (by linarith)
  -- `π(h) = 0`
  have hπh : ∫ y, h y ∂mm1Pi p = 0 := by
    have h1 := integral_kernel_of_isInvariant _ _ hinv hint
    have h2 : ∀ x, ∫ y, h y ∂bernoulliWalk p x = lam * h x := fun x => by
      rw [integral_bernoulliWalk_real hp0.le hp1.le]; exact mm1Op_eigfn hp0 hp1 hβ0.ne' x
    simp_rw [h2] at h1
    rw [integral_const_mul] at h1
    have : (lam - 1) * ∫ y, h y ∂mm1Pi p = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by linarith)
  have hfun : ∀ n, (fun x => ∫ y, h y ∂(bernoulliWalk p ^ n) x - ∫ y, h y ∂mm1Pi p) =
      lam ^ n • h := fun n => by
    funext x
    rw [(hpow n x).2, hπh, sub_zero, Pi.smul_apply, smul_eq_mul]
  -- `‖h‖₁ ∈ (0, ∞)`
  have hN0 : eLpNorm h 1 (mm1Pi p) ≠ 0 := fun h0 => by
    rw [eLpNorm_eq_zero_iff one_ne_zero] at h0
    have hm : mm1Pi p {x | h x ≠ 0} = 0 := ae_iff.1 h0
    have hpos : 0 < mm1Pi p {0} := by
      rw [mm1Pi_singleton]
      exact ENNReal.ofReal_pos.2 (mul_pos (by linarith) (pow_pos hρ0 0))
    exact hpos.ne' (measure_mono_null (fun x hx => by rw [mem_singleton_iff.1 hx]; exact hne)
      hm)
  have hNt : eLpNorm h 1 (mm1Pi p) ≠ ∞ := (memLp_one_iff_integrable.2 hint).eLpNorm_ne_top
  have hbound : ∀ n : ℕ, (lam * r) ^ n ≤ R := fun n => by
    have h1 := hR n h (memLp_one_iff_integrable.2 hint)
    rw [hfun n, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos (pow_pos hl0 n)] at h1
    have h2 := (ENNReal.mul_le_mul_iff_left hN0 hNt).1 h1
    rcases (ENNReal.ofReal_le_ofReal_iff' (p := lam ^ n)).1 h2 with h3 | h3
    · have hrn : 0 < r ^ n := pow_pos (by linarith) n
      calc (lam * r) ^ n = lam ^ n * r ^ n := mul_pow _ _ _
        _ ≤ R * r⁻¹ ^ n * r ^ n := mul_le_mul_of_nonneg_right h3 hrn.le
        _ = R := by rw [inv_pow, mul_assoc, inv_mul_cancel₀ hrn.ne', mul_one]
    · exact absurd h3 (not_le.2 (pow_pos hl0 n))
  have hlr : 1 < lam * r := by
    have := mul_lt_mul_of_pos_right hβlam (by linarith : (0 : ℝ) < r)
    rwa [inv_mul_cancel₀ (by linarith)] at this
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlr).eventually_gt_atTop R).exists
  exact absurd (hbound n) (not_le.2 hn)

end MeynTweedie.Epilogue
