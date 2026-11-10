/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RMSteady
import NeoclassicalGrowth.Nonlinear

/-!
# Dynamics of the detrended Ramsey model: phase diagram and saddle path

Miao, §14.1.1 (with the tools of §1.5–1.6). The text of §14.1 states the detrended equilibrium
system and leaves its dynamics to Chapter 1 (Example 1.6.1 treats `g_a = gₙ = 1`). Here the
detrended system with inelastic labour (`n ≡ 1`, `f(k) = F(k, 1)`) is
`g_a^σu'(c̃_t) = βu'(c̃_{t+1})(f'(k̃_{t+1}) + 1 − δ)`,
`gₙg_ak̃_{t+1} = f(k̃_t) + (1 − δ)k̃_t − c̃_t`. Write `b = β/g_a^σ`, `γ = gₙg_a`, `A = −u''/u'`.

* **Phase diagram.** Consumption rises iff next period's capital is below the steady state:
  `c̃_{t+1} > c̃_t ⟺ k̃_{t+1} < k̃*` (`rm_phase_c`); capital rises iff consumption is below the
  `Δk̃ = 0` locus: `k̃_{t+1} > k̃_t ⟺ c̃_t < f(k̃_t) − (γ − 1 + δ)k̃_t` (`rm_phase_k`).
* **Linearisation.** The partial derivatives of the two residuals at the steady state
  (`rm_lin_taylor`); the linearised equations are equivalent to
  `(dk_{t+1}, dc_{t+1}) = M(dk_t, dc_t)`,
  `M = [[1/(bγ), −1/γ], [f''/(Aγ), 1 − bf''/(Aγ)]]` (`rm_lin_reduced`).
* **Eigenvalues.** `det M = 1/(bγ)`, `tr M = 1 + 1/(bγ) − bf''/(Aγ)` (`rm_lin_trace_det`);
  the characteristic polynomial is negative at `1` and the roots satisfy `0 < λ₁ < 1 < λ₂`
  (`rm_lin_roots`): the steady state is a saddle.
* **Saddle path.** For every `dk₀` there is exactly one bounded solution of the linearised
  system; it starts on the saddle line `dc₀ = κdk₀` with slope `κ > 0`, converges monotonically
  to the steady state, and every other solution is unbounded (`rm_lin_saddle`,
  `rm_lin_saddle_monotone`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- **Phase diagram, `Δc̃ = 0` locus** (Miao, §14.1.1 with §1.5): if `u'` and `f'` are strictly
decreasing, `u'(c̃_{t+1}) > 0`, `β(f'(k̃*) + 1 − δ) = g_a^σ > 0`, and the Euler equation holds, then
consumption rises from `t` to `t + 1` iff `k̃_{t+1} < k̃*`. -/
theorem rm_phase_c {up fp : ℝ → ℝ} {β gs δ c0 c1 k1 kstar : ℝ}
    (hup : StrictAntiOn up (Set.Ioi 0)) (hfp : StrictAntiOn fp (Set.Ioi 0))
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hk1 : 0 < k1) (hks : 0 < kstar) (hβ : 0 < β)
    (hup0 : 0 < up c1) (hgs : 0 < gs) (hss : β * (fp kstar + 1 - δ) = gs)
    (heul : gs * up c0 = β * up c1 * (fp k1 + 1 - δ)) : c0 < c1 ↔ k1 < kstar := by
  have key : c0 < c1 ↔ up c1 < up c0 :=
    ⟨fun h => hup hc0 hc1 h, fun h => by
      by_contra hn
      rcases (not_lt.1 hn).eq_or_lt with he | he
      · rw [he] at h; exact lt_irrefl _ h
      · exact lt_asymm h (hup hc1 hc0 he)⟩
  have key2 : k1 < kstar ↔ fp kstar < fp k1 :=
    ⟨fun h => hfp hk1 hks h, fun h => by
      by_contra hn
      rcases (not_lt.1 hn).eq_or_lt with he | he
      · rw [he] at h; exact lt_irrefl _ h
      · exact lt_asymm h (hfp hks hk1 he)⟩
  rw [key, key2]
  -- `gs·u'(c₀) = βu'(c₁)(f'(k₁) + 1 − δ)` and `gs = β(f'(k*) + 1 − δ)`
  rw [← hss] at heul
  have hpos : 0 < β * (fp kstar + 1 - δ) := hss ▸ hgs
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have h1 : β * up c1 * (fp k1 + 1 - δ) ≤ β * up c1 * (fp kstar + 1 - δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_pos hβ hup0).le
    have : (β * (fp kstar + 1 - δ)) * up c0 ≤ (β * (fp kstar + 1 - δ)) * up c1 := by
      linarith
    have := le_of_mul_le_mul_left this hpos
    linarith
  · intro h
    by_contra hn
    push Not at hn
    have h1 : β * up c1 * (fp kstar + 1 - δ) < β * up c1 * (fp k1 + 1 - δ) :=
      mul_lt_mul_of_pos_left (by linarith) (mul_pos hβ hup0)
    have : (β * (fp kstar + 1 - δ)) * up c0 ≤ (β * (fp kstar + 1 - δ)) * up c1 :=
      mul_le_mul_of_nonneg_left hn hpos.le
    linarith

/-- **Phase diagram, `Δk̃ = 0` locus** (Miao, §14.1.1 with §1.5): with
`γk̃_{t+1} = f(k̃_t) + (1 − δ)k̃_t − c̃_t` and `γ > 0`, capital rises iff
`c̃_t < f(k̃_t) − (γ − 1 + δ)k̃_t`. -/
theorem rm_phase_k {γ δ k0 k1 c0 fk0 : ℝ} (hγ : 0 < γ)
    (hres : γ * k1 = fk0 + (1 - δ) * k0 - c0) : k0 < k1 ↔ c0 < fk0 - (γ - 1 + δ) * k0 := by
  constructor
  · intro h; nlinarith
  · intro h
    have : γ * k0 < γ * k1 := by linarith
    exact lt_of_mul_lt_mul_left this hγ.le

/-- **Linearisation** (Miao, §14.1.1 with Example 1.6.1): the partial derivatives at the steady
state `(k̄, c̄)` of the Euler residual `g_a^σu'(c_t) − βu'(c_{t+1})(f'(k_{t+1}) + 1 − δ)` in
`c_t, c_{t+1}, k_{t+1}` and of the resource residual `γk_{t+1} − f(k_t) − (1 − δ)k_t + c_t` in
`k_{t+1}, k_t, c_t`. -/
theorem rm_lin_taylor {f fp up : ℝ → ℝ} {β gs γ δ kb cb upp fpp : ℝ}
    (hf : HasDerivAt f (fp kb) kb) (hfp : HasDerivAt fp fpp kb) (hup : HasDerivAt up upp cb) :
    HasDerivAt (fun c => gs * up c - β * up cb * (fp kb + 1 - δ)) (gs * upp) cb ∧
      HasDerivAt (fun c' => gs * up cb - β * up c' * (fp kb + 1 - δ))
        (-(β * upp * (fp kb + 1 - δ))) cb ∧
      HasDerivAt (fun k' => gs * up cb - β * up cb * (fp k' + 1 - δ)) (-(β * up cb * fpp)) kb ∧
      HasDerivAt (fun k' => γ * k' - f kb - (1 - δ) * kb + cb) γ kb ∧
      HasDerivAt (fun k => γ * kb - f k - (1 - δ) * k + cb) (-(fp kb) - (1 - δ)) kb ∧
      HasDerivAt (fun c => γ * kb - f kb - (1 - δ) * kb + c) 1 cb := by
  refine ⟨(hup.const_mul gs).sub_const _, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((hup.const_mul β).mul_const (fp kb + 1 - δ)).const_sub (gs * up cb)
    convert this using 1
  · have := ((hfp.add_const (1 - δ)).const_mul (β * up cb)).const_sub (gs * up cb)
    convert this using 1
    ext k; ring
  · have := ((((hasDerivAt_id kb).const_mul γ).sub_const (f kb)).sub_const
      ((1 - δ) * kb)).add_const cb
    simpa using this
  · have := (((hf.const_sub (γ * kb)).sub ((hasDerivAt_id kb).const_mul (1 - δ))).add_const cb)
    exact this.congr_deriv (by ring)
  · simpa using (hasDerivAt_id cb).const_add (γ * kb - f kb - (1 - δ) * kb)

/-- **The linearised system** (Miao, §14.1.1): at a steady state `b(f' + 1 − δ) = 1` with
`u' > 0`, `u'' ≠ 0`, `b, γ ≠ 0`, the linearised Euler and resource equations
`u''dc_t = bu''(f' + 1 − δ)dc_{t+1} + bu'f''dk_{t+1}`,
`γdk_{t+1} = (f' + 1 − δ)dk_t − dc_t` are equivalent to `(dk_{t+1}, dc_{t+1}) = M(dk_t, dc_t)`. -/
theorem rm_lin_reduced {b γ δ up upp fp fpp : ℝ} (hb : b ≠ 0) (hγ : γ ≠ 0) (hup : 0 < up)
    (hupp : upp ≠ 0) (hss : b * (fp + 1 - δ) = 1) (dk dc : ℕ → ℝ) (t : ℕ) :
    (upp * dc t = b * upp * (fp + 1 - δ) * dc (t + 1) + b * up * fpp * dk (t + 1) ∧
        γ * dk (t + 1) = (fp + 1 - δ) * dk t - dc t) ↔
      (dk (t + 1) = 1 / (b * γ) * dk t + -1 / γ * dc t ∧
        dc (t + 1) = fpp / (-upp / up * γ) * dk t +
          (1 - b * fpp / (-upp / up * γ)) * dc t) := by
  have hfp : fp + 1 - δ = 1 / b := by field_simp; linarith
  have h1 : b * upp * (fp + 1 - δ) = upp := by rw [mul_comm b, mul_assoc, hss, mul_one]
  rw [h1]
  have hup' : up ≠ 0 := hup.ne'
  constructor
  · rintro ⟨e1, e2⟩
    have eK : dk (t + 1) = 1 / (b * γ) * dk t + -1 / γ * dc t := by
      rw [hfp] at e2; field_simp; field_simp at e2; linarith
    refine ⟨eK, ?_⟩
    rw [eK] at e1
    field_simp
    field_simp at e1
    linear_combination (-1) * e1
  · rintro ⟨e1, e2⟩
    refine ⟨?_, ?_⟩
    · rw [e2, e1]
      field_simp
      ring
    · rw [e1, hfp]; field_simp; ring

/-- **Trace and determinant** (Miao, §14.1.1): `det M = 1/(bγ)` and
`tr M = 1 + 1/(bγ) − bf''/(Aγ)`. -/
theorem rm_lin_trace_det {b γ fpp A : ℝ} (hb : b ≠ 0) (hγ : γ ≠ 0) (hA : A ≠ 0) :
    1 / (b * γ) + (1 - b * fpp / (A * γ)) = 1 + 1 / (b * γ) - b * fpp / (A * γ) ∧
      1 / (b * γ) * (1 - b * fpp / (A * γ)) - (-1 / γ) * (fpp / (A * γ)) = 1 / (b * γ) := by
  refine ⟨by ring, by field_simp; ring⟩

/-- **Eigenvalues** (Miao, §14.1.1): for `b, γ, A > 0` and `f'' < 0`, the characteristic
polynomial of `M` is negative at `1`, and its roots satisfy `0 < λ₁ < 1 < λ₂`. -/
theorem rm_lin_roots {b γ fpp A : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hf : fpp < 0) (hA : 0 < A) :
    cp22 (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) 1 < 0 ∧
      0 < lamLo (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) ∧
      lamLo (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) < 1 ∧
      1 < lamHi (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) := by
  have hcp : ∀ μ, cp22 (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) μ =
      μ ^ 2 - (1 + 1 / (b * γ) - b * fpp / (A * γ)) * μ + 1 / (b * γ) := fun μ => by
    simp only [cp22]; field_simp; ring
  have h2 : b * fpp / (A * γ) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hb hf) (mul_pos hA hγ)
  have h1 : cp22 (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) 1 < 0 := by
    rw [hcp]; linarith
  obtain ⟨hlo, hhi⟩ := roots22_lt h1
  refine ⟨h1, ?_, hlo, hhi⟩
  have h0 := cp22_factor h1 0
  rw [hcp] at h0
  have hd : 0 < 1 / (b * γ) := by positivity
  nlinarith

/-- **The saddle path** (Miao, §14.1.1): for every `dk₀` the linearised system has a solution
starting at `dk₀` converging to the steady state, every bounded solution starts on the saddle
line `dc₀ = κdk₀`, the slope `κ` is positive (consumption is increasing in capital along the
saddle path), and every solution off the line is unbounded. -/
theorem rm_lin_saddle {b γ fpp A : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hf : fpp < 0) (hA : 0 < A)
    (dk0 : ℝ) :
    let m11 := 1 / (b * γ)
    let m12 := -1 / γ
    let m21 := fpp / (A * γ)
    let m22 := 1 - b * fpp / (A * γ)
    (∃ dk dc : ℕ → ℝ, IsSol22 m11 m12 m21 m22 dk dc ∧ dk 0 = dk0 ∧
      Tendsto dk atTop (𝓝 0) ∧ Tendsto dc atTop (𝓝 0)) ∧
    (∀ dk dc : ℕ → ℝ, IsSol22 m11 m12 m21 m22 dk dc → BddSeq dk → BddSeq dc →
      dc 0 = kSaddle m11 m12 m21 m22 * dk 0) ∧
    0 < kSaddle m11 m12 m21 m22 ∧
    (∀ dk dc : ℕ → ℝ, IsSol22 m11 m12 m21 m22 dk dc →
      dc 0 ≠ kSaddle m11 m12 m21 m22 * dk 0 → ¬ (BddSeq dk ∧ BddSeq dc)) := by
  intro m11 m12 m21 m22
  obtain ⟨h1, hlo0, -, -⟩ := rm_lin_roots hb hγ hf hA
  have hm : 0 < m12 * m21 := by
    have h21 : fpp / (A * γ) < 0 := div_neg_of_neg_of_pos hf (mul_pos hA hγ)
    have h12 : -1 / γ < 0 := div_neg_of_neg_of_pos (by norm_num) hγ
    exact mul_pos_of_neg_of_neg h12 h21
  have hc : 0 < cp22 m11 m12 m21 m22 (-1) := by
    rw [cp22_factor h1 (-1)]
    have := (roots22_lt h1).2
    nlinarith
  refine ⟨(saddle22_iff h1 hm).2 hc dk0, fun dk dc h hK hC => ?_, ?_,
    fun dk dc h hoff => saddle22_unbounded h1 hm h hoff⟩
  · exact (sHi_zero_iff h1 hm dk dc 0).1 (sHi_zero_of_bdd h1 h hK hC)
  · have hlt := lamLo_lt_m11 h1 hm
    have hm12 : m12 < 0 := div_neg_of_neg_of_pos (by norm_num) hγ
    simp only [kSaddle]
    exact div_pos_of_neg_of_neg (by linarith) hm12

/-- **Monotone convergence along the saddle path** (Miao, §14.1.1): since the stable root lies in
`(0, 1)`, capital on the saddle path `dk_t = λ₁ᵗdk₀` moves monotonically towards the steady
state: `|dk_{t+1}| < |dk_t|` and `dk_t` keeps the sign of `dk₀`, for `dk₀ ≠ 0`. -/
theorem rm_lin_saddle_monotone {b γ fpp A : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hf : fpp < 0)
    (hA : 0 < A) {dk0 : ℝ} (hdk : dk0 ≠ 0) (t : ℕ) :
    let l := lamLo (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ))
    |l ^ (t + 1) * dk0| < |l ^ t * dk0| ∧ 0 < l ^ t * dk0 * dk0 := by
  intro l
  obtain ⟨-, hl0', hl1', -⟩ := rm_lin_roots hb hγ hf hA
  have hl0 : 0 < l := hl0'
  have hl1 : l < 1 := hl1'
  have hlt : 0 < l ^ t := pow_pos hl0 t
  refine ⟨?_, ?_⟩
  · rw [pow_succ, abs_mul, abs_mul, abs_mul, abs_of_pos hlt, abs_of_pos hl0]
    have : 0 < |dk0| := abs_pos.2 hdk
    nlinarith [mul_lt_mul_of_pos_left hl1 (mul_pos hlt this)]
  · have : 0 < dk0 * dk0 := mul_self_pos.2 hdk
    nlinarith

end Miao.NeoclassicalGrowth
