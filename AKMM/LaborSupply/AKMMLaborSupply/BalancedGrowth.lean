/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.Estimation
import AKMMDynamicOptimization.BalancedGrowthCRRA

/-!
# Labour supply and balanced growth

AKMM, §12.5, pp. 352–353, and Appendix 12.A, p. 849.

The planner (12.36) has `F = Z^{1−α}K^αL^{1−α}` and labour-augmenting growth `Z_{t+1} = GZ_t`;
on a balanced path `C, K, Z` grow by the factor `G` and hours `L` are constant. Utility is
`U(C, ℓ)` with leisure `ℓ = 1 − L`.

* **(12.37), "if"** (`eq_12_37_if`): for KPR utility `C^{1−σ}v(ℓ)/(1 − σ)` (`σ ≠ 1`) or
  `log C + v(ℓ)` (`kprU`, with partial derivatives `kpr_partials`), the Euler equation holds at
  every date of a balanced path iff `G^σ = β(MPK + 1 − δ)`, the intratemporal condition iff it
  holds at date `0`, and the resource constraint iff it holds at date `0`: hours can stay
  constant while the economy grows. The reason is the homogeneity of `U_C` (degree `−σ`) and
  of the MRS (degree `1`) in `C` (`kpr_homog`); in a static problem with only labour income the
  wage then has no effect on hours (`kpr_static_hours`).
* **(12.37) as printed is not of the KPR class**: `(C^{1−σ} − 1)v(1 − L)/(1 − σ)` has an MRS
  that is not homogeneous of degree one (`eq_12_37_printed_not_bgp`); the corrected form drops
  the `−1` (or puts it outside: `(C^{1−σ}v − 1)/(1 − σ)`).
* **(12.37), "only if"**, under a stated class. Step 1, (12.A.1)–(12.A.2): if for each leisure
  level the Euler ratio `U_C(gC, ℓ)/U_C(C, ℓ)` does not depend on `C`, for every growth factor
  `g > 0`, then `U_CC C/U_C = −σ(ℓ)` (the book prints `+σ`) and `U(·, ℓ)` is
  `a(ℓ)C^{1−σ(ℓ)}/(1 − σ(ℓ)) + b(ℓ)` or `a(ℓ) log C + b(ℓ)` (`eq_12_A_2`, from AKMM Chapter 4's
  Theorem .4, `theorem_4A_4`). Step 2, (12.A.3): within that class, with `a, σ, b`
  differentiable in `ℓ`, `a > 0`, `σ(ℓ) ≠ 1`, homogeneity of degree one of the MRS forces
  `σ′(ℓ) = 0` and `b′(ℓ) = 0` (`eq_12_A_3`); in the log class it forces `a′(ℓ) = 0`
  (`eq_12_A_3_log`). On the interval of leisure levels `σ` and `b` are then constant, which is
  (12.37) up to an additive constant (`eq_12_37_only_if`).
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Technology -/

/-- Output `Z^{1−α}K^αL^{1−α}` (AKMM, (12.36), p. 352). -/
noncomputable def bgF (α Z K L : ℝ) : ℝ := Z ^ (1 - α) * K ^ α * L ^ (1 - α)

/-- The marginal product of capital `αZ^{1−α}K^{α−1}L^{1−α}`. -/
noncomputable def bgMPK (α Z K L : ℝ) : ℝ := α * Z ^ (1 - α) * K ^ (α - 1) * L ^ (1 - α)

/-- The marginal product of labour `(1 − α)Z^{1−α}K^αL^{−α}`. -/
noncomputable def bgMPL (α Z K L : ℝ) : ℝ := (1 - α) * Z ^ (1 - α) * K ^ α * L ^ (-α)

/-- Scaling `Z` and `K` by `G > 0` scales output and the marginal product of labour by `G`
and leaves the marginal product of capital unchanged (AKMM, (12.A.1), p. 849:
`MPK = α(L/κ)^{1−α}`, `κ = K/Z`). -/
theorem bg_homog {α G Z K L : ℝ} (hG : 0 < G) (hZ : 0 < Z) (hK : 0 < K) :
    bgF α (G * Z) (G * K) L = G * bgF α Z K L ∧
      bgMPK α (G * Z) (G * K) L = bgMPK α Z K L ∧
      bgMPL α (G * Z) (G * K) L = G * bgMPL α Z K L := by
  unfold bgF bgMPK bgMPL
  rw [Real.mul_rpow hG.le hZ.le, Real.mul_rpow hG.le hK.le, Real.mul_rpow hG.le hK.le]
  have e1 : G ^ (1 - α) * G ^ α = G := by
    rw [← Real.rpow_add hG, show 1 - α + α = 1 by ring, Real.rpow_one]
  have e2 : G ^ (1 - α) * G ^ (α - 1) = 1 := by
    rw [← Real.rpow_add hG, show 1 - α + (α - 1) = 0 by ring, Real.rpow_zero]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (Z ^ (1 - α) * K ^ α * L ^ (1 - α)) * e1
  · linear_combination (α * Z ^ (1 - α) * K ^ (α - 1) * L ^ (1 - α)) * e2
  · linear_combination ((1 - α) * Z ^ (1 - α) * K ^ α * L ^ (-α)) * e1

/-! ### KPR utility -/

/-- KPR utility, the corrected (12.37): `C^{1−σ}v(ℓ)/(1 − σ)` for `σ ≠ 1`, `log C + v(ℓ)` for
`σ = 1` (`ℓ = 1 − L` is leisure). -/
noncomputable def kprU (σ : ℝ) (v : ℝ → ℝ) (C l : ℝ) : ℝ :=
  if σ = 1 then Real.log C + v l else C ^ (1 - σ) * v l / (1 - σ)

/-- The marginal utility of consumption of `kprU`. -/
noncomputable def kprUC (σ : ℝ) (v : ℝ → ℝ) (C l : ℝ) : ℝ :=
  if σ = 1 then C ^ (-σ) else C ^ (-σ) * v l

/-- The marginal utility of leisure of `kprU` (`v′` the derivative of `v`). -/
noncomputable def kprUl (σ : ℝ) (v' : ℝ → ℝ) (C l : ℝ) : ℝ :=
  if σ = 1 then v' l else C ^ (1 - σ) * v' l / (1 - σ)

/-- AKMM, (12.37): the partial derivatives of `kprU` are `kprUC` and `kprUl` (`C > 0`). -/
theorem kpr_partials {σ C l : ℝ} {v v' : ℝ → ℝ} (hC : 0 < C) (hv : HasDerivAt v (v' l) l) :
    HasDerivAt (fun x => kprU σ v x l) (kprUC σ v C l) C ∧
      HasDerivAt (fun y => kprU σ v C y) (kprUl σ v' C l) l := by
  by_cases hσ : σ = 1
  · subst hσ
    simp only [kprU, kprUC, kprUl, ↓reduceIte]
    refine ⟨?_, hv.const_add _⟩
    rw [Real.rpow_neg_one]
    exact (Real.hasDerivAt_log hC.ne').add_const _
  · simp only [kprU, kprUC, kprUl, hσ, ↓reduceIte]
    have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    refine ⟨?_, (hv.const_mul (C ^ (1 - σ))).div_const (1 - σ)⟩
    have := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).mul_const (v l)).div_const
      (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- The marginal rate of substitution `U_ℓ/U_C` of KPR utility: `Cv′(ℓ)/((1 − σ)v(ℓ))`, or
`Cv′(ℓ)` when `σ = 1`. -/
theorem kpr_mrs {σ C l : ℝ} {v v' : ℝ → ℝ} (hC : 0 < C) (hv : σ ≠ 1 → v l ≠ 0) :
    kprUl σ v' C l / kprUC σ v C l =
      if σ = 1 then C * v' l else C * v' l / ((1 - σ) * v l) := by
  by_cases hσ : σ = 1
  · subst hσ
    simp only [kprUC, kprUl, ↓reduceIte, Real.rpow_neg_one]
    field_simp
  · simp only [kprUC, kprUl, hσ, ↓reduceIte]
    have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    have hvl := hv hσ
    have e : C ^ (1 - σ) = C * C ^ (-σ) := by
      rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hC, Real.rpow_one]
    have hp : 0 < C ^ (-σ) := Real.rpow_pos_of_pos hC _
    rw [e]
    field_simp

/-- AKMM, p. 353, **homogeneity of KPR utility**: `U_C(GC, ℓ) = G^{−σ}U_C(C, ℓ)` and
`U_ℓ(GC, ℓ) = G^{1−σ}U_ℓ(C, ℓ)` for `G, C > 0`, so the MRS `U_ℓ/U_C` is homogeneous of degree
one in `C`. -/
theorem kpr_homog {σ G C l : ℝ} {v v' : ℝ → ℝ} (hG : 0 < G) (hC : 0 < C) :
    kprUC σ v (G * C) l = G ^ (-σ) * kprUC σ v C l ∧
      kprUl σ v' (G * C) l = G ^ (1 - σ) * kprUl σ v' C l := by
  by_cases hσ : σ = 1
  · subst hσ
    simp only [kprUC, kprUl, ↓reduceIte, Real.mul_rpow hG.le hC.le, sub_self, Real.rpow_zero,
      one_mul, and_true]
  · simp only [kprUC, kprUl, hσ, ↓reduceIte, Real.mul_rpow hG.le hC.le]
    constructor <;> ring

/-- AKMM, p. 353: "in a static setting with only labour income … a higher wage rate has no
effect on desired hours": with KPR utility the static condition `MRS(wL, 1 − L) = w`
(`C = wL`) holds iff `MRS(L, 1 − L) = 1`, which does not involve `w`. -/
theorem kpr_static_hours {σ w L : ℝ} {v v' : ℝ → ℝ} (hw : 0 < w) (hL : 0 < L)
    (hv : kprUC σ v L (1 - L) ≠ 0) :
    kprUl σ v' (w * L) (1 - L) / kprUC σ v (w * L) (1 - L) = w ↔
      kprUl σ v' L (1 - L) / kprUC σ v L (1 - L) = 1 := by
  obtain ⟨h1, h2⟩ := kpr_homog (σ := σ) (v := v) (v' := v') (l := 1 - L) hw hL
  rw [h1, h2]
  have hp : 0 < w ^ (-σ) := Real.rpow_pos_of_pos hw _
  have e : w ^ (1 - σ) = w * w ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hw, Real.rpow_one]
  rw [e, show w * w ^ (-σ) * kprUl σ v' L (1 - L) / (w ^ (-σ) * kprUC σ v L (1 - L)) =
    w * (kprUl σ v' L (1 - L) / kprUC σ v L (1 - L)) by field_simp]
  constructor
  · intro h; exact (mul_eq_left₀ hw.ne').1 h
  · intro h; rw [h, mul_one]

/-- AKMM, (12.37), p. 353, **"if"**: on a balanced path `Z_t = GᵗZ₀`, `K_t = GᵗK₀`,
`C_t = GᵗC₀` with constant hours `L ∈ (0, 1)`, and KPR utility (`v(1 − L) > 0` if `σ ≠ 1`):
(i) the Euler equation `U_C(C_t) = βU_C(C_{t+1})(MPK_{t+1} + 1 − δ)` holds at every `t` iff
`G^σ = β(MPK₀ + 1 − δ)`; (ii) the intratemporal condition `U_ℓ(C_t)/U_C(C_t) = MPL_t` holds at
every `t` iff it holds at `t = 0`; (iii) the resource constraint
`C_t + K_{t+1} = F(Z_t, K_t, L) + (1 − δ)K_t` holds at every `t` iff it holds at `t = 0`. -/
theorem eq_12_37_if {σ α β δ G Z₀ K₀ C₀ L : ℝ} {v v' : ℝ → ℝ} (hG : 0 < G) (hZ : 0 < Z₀)
    (hK : 0 < K₀) (hC : 0 < C₀) (hv : σ ≠ 1 → 0 < v (1 - L)) :
    ((∀ t : ℕ, kprUC σ v (G ^ t * C₀) (1 - L) = β * kprUC σ v (G ^ (t + 1) * C₀) (1 - L) *
        (bgMPK α (G ^ (t + 1) * Z₀) (G ^ (t + 1) * K₀) L + 1 - δ)) ↔
      G ^ σ = β * (bgMPK α Z₀ K₀ L + 1 - δ)) ∧
    ((∀ t : ℕ, kprUl σ v' (G ^ t * C₀) (1 - L) / kprUC σ v (G ^ t * C₀) (1 - L) =
        bgMPL α (G ^ t * Z₀) (G ^ t * K₀) L) ↔
      kprUl σ v' C₀ (1 - L) / kprUC σ v C₀ (1 - L) = bgMPL α Z₀ K₀ L) ∧
    ((∀ t : ℕ, G ^ t * C₀ + G ^ (t + 1) * K₀ =
        bgF α (G ^ t * Z₀) (G ^ t * K₀) L + (1 - δ) * (G ^ t * K₀)) ↔
      C₀ + G * K₀ = bgF α Z₀ K₀ L + (1 - δ) * K₀) := by
  have hGt : ∀ t : ℕ, 0 < G ^ t := fun t => pow_pos hG t
  have hUC0 : 0 < kprUC σ v C₀ (1 - L) := by
    by_cases hσ : σ = 1
    · simp only [kprUC, hσ, ↓reduceIte]; exact Real.rpow_pos_of_pos hC _
    · simp only [kprUC, hσ, ↓reduceIte]
      exact mul_pos (Real.rpow_pos_of_pos hC _) (hv hσ)
  have hGs : G ^ σ * G ^ (-σ) = 1 := by
    rw [← Real.rpow_add hG, add_neg_cancel, Real.rpow_zero]
  -- the Euler equation at date `t` is equivalent to the date-free condition
  have euler_t : ∀ t : ℕ, (kprUC σ v (G ^ t * C₀) (1 - L) = β *
      kprUC σ v (G ^ (t + 1) * C₀) (1 - L) *
        (bgMPK α (G ^ (t + 1) * Z₀) (G ^ (t + 1) * K₀) L + 1 - δ) ↔
      G ^ σ = β * (bgMPK α Z₀ K₀ L + 1 - δ)) := by
    intro t
    rw [(kpr_homog (v' := v') (hGt t) hC).1, (bg_homog (α := α) (L := L) (hGt (t + 1)) hZ hK).2.1,
      pow_succ, (kpr_homog (v' := v') (mul_pos (hGt t) hG) hC).1,
      Real.mul_rpow (hGt t).le hG.le]
    have hp : 0 < (G ^ t) ^ (-σ) := Real.rpow_pos_of_pos (hGt t) _
    constructor
    · intro h
      have h' : 1 = β * G ^ (-σ) * (bgMPK α Z₀ K₀ L + 1 - δ) := by
        have := mul_pos hp hUC0
        apply mul_left_cancel₀ this.ne'
        linear_combination h
      linear_combination G ^ σ * h' + (β * (bgMPK α Z₀ K₀ L + 1 - δ)) * hGs
    · intro h
      linear_combination ((G ^ t) ^ (-σ) * kprUC σ v C₀ (1 - L) * G ^ (-σ)) * h -
        ((G ^ t) ^ (-σ) * kprUC σ v C₀ (1 - L)) * hGs
  refine ⟨⟨fun h => (euler_t 0).1 (h 0), fun h t => (euler_t t).2 h⟩, ?_, ?_⟩
  · have intra_t : ∀ t : ℕ, (kprUl σ v' (G ^ t * C₀) (1 - L) /
        kprUC σ v (G ^ t * C₀) (1 - L) = bgMPL α (G ^ t * Z₀) (G ^ t * K₀) L ↔
        kprUl σ v' C₀ (1 - L) / kprUC σ v C₀ (1 - L) = bgMPL α Z₀ K₀ L) := by
      intro t
      obtain ⟨h1, h2⟩ := kpr_homog (σ := σ) (v := v) (v' := v') (l := 1 - L) (hGt t) hC
      rw [h1, h2, (bg_homog (α := α) (L := L) (hGt t) hZ hK).2.2]
      have hp : 0 < (G ^ t) ^ (-σ) := Real.rpow_pos_of_pos (hGt t) _
      have e : (G ^ t) ^ (1 - σ) = G ^ t * (G ^ t) ^ (-σ) := by
        rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add (hGt t), Real.rpow_one]
      rw [e, show G ^ t * (G ^ t) ^ (-σ) * kprUl σ v' C₀ (1 - L) /
        ((G ^ t) ^ (-σ) * kprUC σ v C₀ (1 - L)) =
          G ^ t * (kprUl σ v' C₀ (1 - L) / kprUC σ v C₀ (1 - L)) by field_simp]
      exact mul_right_inj' (hGt t).ne'
    exact ⟨fun h => by simpa using h 0, fun h t => (intra_t t).2 h⟩
  · have res_t : ∀ t : ℕ, (G ^ t * C₀ + G ^ (t + 1) * K₀ =
        bgF α (G ^ t * Z₀) (G ^ t * K₀) L + (1 - δ) * (G ^ t * K₀) ↔
        C₀ + G * K₀ = bgF α Z₀ K₀ L + (1 - δ) * K₀) := by
      intro t
      rw [(bg_homog (α := α) (L := L) (hGt t) hZ hK).1, pow_succ]
      constructor
      · intro h
        apply mul_left_cancel₀ (hGt t).ne'
        linear_combination h
      · intro h
        linear_combination (G ^ t) * h
    exact ⟨fun h => by simpa using h 0, fun h t => (res_t t).2 h⟩

/-- AKMM, (12.37), p. 353, **the printed form is not consistent with balanced growth**. For
`U = (C^{1−σ} − 1)v(ℓ)/(1 − σ)` (`σ ≠ 1`, `v(ℓ) ≠ 0`, `v′(ℓ) ≠ 0`) the partial derivatives
are `U_C = C^{−σ}v`, `U_ℓ = (C^{1−σ} − 1)v′/(1 − σ)`, and the MRS is not homogeneous of degree
one: `MRS(2·1, ℓ) ≠ 2·MRS(1, ℓ)` (`MRS(1, ℓ) = 0`). So constant hours with growing wages are
impossible. -/
theorem eq_12_37_printed_not_bgp {σ l v₀ v₁ : ℝ} {v : ℝ → ℝ} (hσ : σ ≠ 1)
    (hv : HasDerivAt v v₁ l) (hv0 : v l = v₀) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) :
    (∀ C, 0 < C → HasDerivAt (fun x => (x ^ (1 - σ) - 1) * v l / (1 - σ))
      (C ^ (-σ) * v₀) C) ∧
    (∀ C, HasDerivAt (fun y => (C ^ (1 - σ) - 1) * v y / (1 - σ))
      ((C ^ (1 - σ) - 1) * v₁ / (1 - σ)) l) ∧
    (((2 : ℝ) * 1) ^ (1 - σ) - 1) * v₁ / (1 - σ) / (((2 : ℝ) * 1) ^ (-σ) * v₀) ≠
      2 * (((1 : ℝ) ^ (1 - σ) - 1) * v₁ / (1 - σ) / ((1 : ℝ) ^ (-σ) * v₀)) := by
  have hs : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  refine ⟨fun C hC => ?_, fun C => ?_, ?_⟩
  · have := (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).mul_const
      (v l)).div_const (1 - σ)
    refine this.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring, hv0]
    field_simp
  · exact (hv.const_mul _).div_const _
  · simp only [Real.one_rpow, sub_self, zero_mul, zero_div, mul_zero, mul_one]
    have h2 : (2 : ℝ) ^ (1 - σ) ≠ 1 := by
      intro h
      have := congrArg Real.log h
      rw [Real.log_rpow two_pos, Real.log_one] at this
      rcases mul_eq_zero.1 this with h' | h'
      · exact hs h'
      · exact absurd h' (Real.log_pos one_lt_two).ne'
    have hp : 0 < (2 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos two_pos _
    have : ((2 : ℝ) ^ (1 - σ) - 1) ≠ 0 := sub_ne_zero.2 h2
    exact div_ne_zero (div_ne_zero (mul_ne_zero this hv₁) hs) (mul_ne_zero hp.ne' hv₀)

/-! ### Appendix 12.A: "only if" -/

/-- AKMM, (12.A.1)–(12.A.2), p. 849, **corrected sign**. Fix a leisure level and let
`u = U(·, ℓ)` have `u′ > 0` and second derivative `u″` on `(0, ∞)`. If on every balanced path
the Euler ratio is the same at every consumption level — for every growth factor `1 + γ > 0`
there is `M` with `u′((1 + γ)C) = Mu′(C)` for all `C > 0` — then for some `σ`:
`Cu″(C)/u′(C) = −σ` (the book prints `+σ`), `u′(C) = u′(1)C^{−σ}`, and `u` is
`u′(1)C^{1−σ}/(1 − σ) + b` (`σ ≠ 1`) or `u′(1) log C + u(1)` (`σ = 1`): the candidate forms with
`v¹(ℓ) = u′(1)`. Proved with AKMM Chapter 4's Theorem .4. -/
theorem eq_12_A_2 {u u' u'' : ℝ → ℝ} (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu' : ∀ c, 0 < c → HasDerivAt u' (u'' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hbgp : ∀ γ, -1 < γ → ∃ M, ∀ c, 0 < c → u' ((1 + γ) * c) = M * u' c) :
    ∃ σ, (∀ c, 0 < c → c * u'' c / u' c = -σ) ∧ (∀ c, 0 < c → u' c = u' 1 * c ^ (-σ)) ∧
      (σ = 1 → ∀ c, 0 < c → u c = u' 1 * Real.log c + u 1) ∧
      (σ ≠ 1 → ∃ b, ∀ c, 0 < c → u c = u' 1 * c ^ (1 - σ) / (1 - σ) + b) := by
  obtain ⟨hform, hlog, hpow⟩ := AKMM.DynamicOptimization.theorem_4A_4 hu hu' hpos hbgp
  set σ := -u'' 1 / u' 1
  refine ⟨σ, fun c hc => ?_, hform, hlog, hpow⟩
  have h1 : 0 < u' 1 := hpos 1 one_pos
  -- `u″(c) = −σu′(1)c^{−σ−1}` by uniqueness of the derivative
  have hd : HasDerivAt (fun x => u' 1 * x ^ (-σ)) (u' 1 * (-σ * c ^ (-σ - 1))) c :=
    (Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul _
  have heq : (fun x => u' 1 * x ^ (-σ)) =ᶠ[𝓝 c] u' := by
    filter_upwards [lt_mem_nhds hc] with x hx using (hform x hx).symm
  have hu'' : u'' c = u' 1 * (-σ * c ^ (-σ - 1)) := (hu' c hc).unique (hd.congr_of_eventuallyEq
    heq.symm)
  rw [hu'', hform c hc, Real.rpow_sub_one hc.ne']
  have hp : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  field_simp

/-- The leisure derivative of the candidate `a(ℓ)C^{1−s(ℓ)}/(1 − s(ℓ)) + b(ℓ)` (`C > 0`,
`s(ℓ) ≠ 1`): `C^{1−s}(a′/(1 − s) + as′/(1 − s)² − (as′/(1 − s)) log C) + b′`. -/
theorem kpr_candidate_deriv {a s b : ℝ → ℝ} {a' s' b' l C : ℝ} (ha : HasDerivAt a a' l)
    (hs : HasDerivAt s s' l) (hb : HasDerivAt b b' l) (hs1 : s l ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun x => a x * C ^ (1 - s x) / (1 - s x) + b x)
      (C ^ (1 - s l) * (a' / (1 - s l) + a l * s' / (1 - s l) ^ 2 -
        a l * s' / (1 - s l) * Real.log C) + b') l := by
  have hm : 1 - s l ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have hpow : HasDerivAt (fun x => C ^ (1 - s x)) (C ^ (1 - s l) * (-s' * Real.log C)) l := by
    have he : (fun x => C ^ (1 - s x)) = fun x => Real.exp ((1 - s x) * Real.log C) := by
      funext x; rw [Real.rpow_def_of_pos hC, mul_comm]
    rw [he]
    have := (((hs.const_sub 1).mul_const (Real.log C))).exp
    refine this.congr_deriv ?_
    rw [Real.rpow_def_of_pos hC, mul_comm (Real.log C)]
  have := ((ha.mul hpow).div (hs.const_sub 1) hm).add hb
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- AKMM, (12.A.3), p. 849: **the intratemporal condition forces `σ′ = 0` and `v²′ = 0`**.
Let `U(C, x) = a(x)C^{1−s(x)}/(1 − s(x)) + b(x)` near leisure `ℓ`, with `a, s, b`
differentiable at `ℓ`, `a(ℓ) > 0`, `s(ℓ) ≠ 1`, `U_C(C, ℓ) = a(ℓ)C^{−s(ℓ)}` and `U_ℓ(C)` the
leisure derivative. If the MRS is homogeneous of degree one in `C` —
`U_ℓ(gC)U_C(C) = gU_ℓ(C)U_C(gC)` for all `g, C > 0`, which is what the intratemporal condition
along balanced paths with growing wages requires — then `s′(ℓ) = 0` and `b′(ℓ) = 0`. -/
theorem eq_12_A_3 {a s b : ℝ → ℝ} {a' s' b' l : ℝ} {Ul : ℝ → ℝ} (ha : HasDerivAt a a' l)
    (hs : HasDerivAt s s' l) (hb : HasDerivAt b b' l) (hapos : 0 < a l) (hs1 : s l ≠ 1)
    (hUl : ∀ C, 0 < C → HasDerivAt (fun x => a x * C ^ (1 - s x) / (1 - s x) + b x) (Ul C) l)
    (hhom : ∀ g, 0 < g → ∀ C, 0 < C →
      Ul (g * C) * (a l * C ^ (-s l)) = g * Ul C * (a l * (g * C) ^ (-s l))) :
    s' = 0 ∧ b' = 0 := by
  have hm : 1 - s l ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  set m := 1 - s l with hmdef
  set A1 := a' / m + a l * s' / m ^ 2
  set A2 := -(a l * s' / m)
  have hUlf : ∀ C, 0 < C → Ul C = C ^ m * (A1 + A2 * Real.log C) + b' := by
    intro C hC
    have := (hUl C hC).unique (kpr_candidate_deriv ha hs hb hs1 hC)
    rw [this]; ring
  -- `U_ℓ(g) = g^m U_ℓ(1)`
  have hscale : ∀ g, 0 < g → Ul g = g ^ m * Ul 1 := by
    intro g hg
    have h := hhom g hg 1 one_pos
    simp only [mul_one, Real.one_rpow] at h
    have hp : 0 < g ^ (-s l) := Real.rpow_pos_of_pos hg _
    have e : g ^ m = g * g ^ (-s l) := by
      rw [hmdef, show 1 - s l = 1 + -s l by ring, Real.rpow_add hg, Real.rpow_one]
    rw [e]
    apply mul_right_cancel₀ hapos.ne'
    linear_combination h
  -- evaluate at `g = e^{t/m}`
  have key : ∀ t : ℝ, Real.exp t * (A2 * (t / m)) + b' * (1 - Real.exp t) = 0 := by
    intro t
    have hg : 0 < Real.exp (t / m) := Real.exp_pos _
    have h := hscale _ hg
    rw [hUlf _ hg, hUlf 1 one_pos, Real.log_exp, Real.log_one, Real.one_rpow, ← Real.exp_mul,
      div_mul_cancel₀ _ hm] at h
    linear_combination h
  have k1 := key 1
  have k2 := key 2
  have he : 2 < Real.exp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [hexp2] at k2
  set e := Real.exp 1
  have hX : A2 / m * (e * (e - 1)) = 0 := by
    linear_combination k2 - (e + 1) * k1
  have hA2 : A2 = 0 := by
    have hne : e * (e - 1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    have := (mul_eq_zero.1 hX).resolve_right hne
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hm
  have hb' : b' = 0 := by
    rw [hA2] at k1
    have : b' * (1 - e) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right (by linarith)
  refine ⟨?_, hb'⟩
  have : a l * s' / m = 0 := by linarith
  rcases div_eq_zero_iff.1 this with h | h
  · exact (mul_eq_zero.1 h).resolve_left hapos.ne'
  · exact absurd h hm

/-- AKMM, p. 849, "the derivation for the log case is similar": for
`U(C, x) = a(x) log C + b(x)` with `a(ℓ) > 0`, homogeneity of degree one of the MRS in `C`
forces `a′(ℓ) = 0` (`v¹` constant, not `v²`), so `U = a log C + b(ℓ)` is (12.37) with `σ = 1`
up to the positive factor `a`. -/
theorem eq_12_A_3_log {a b : ℝ → ℝ} {a' b' l : ℝ} (ha : HasDerivAt a a' l)
    (hb : HasDerivAt b b' l) (hapos : 0 < a l) {Ul : ℝ → ℝ}
    (hUl : ∀ C, 0 < C → HasDerivAt (fun x => a x * Real.log C + b x) (Ul C) l)
    (hhom : ∀ g, 0 < g → ∀ C, 0 < C → Ul (g * C) * (a l / C) = g * Ul C * (a l / (g * C))) :
    a' = 0 := by
  have hUlf : ∀ C, 0 < C → Ul C = a' * Real.log C + b' := fun C hC =>
    (hUl C hC).unique ((ha.mul_const _).add hb)
  have h := hhom (Real.exp 1) (Real.exp_pos 1) 1 one_pos
  rw [mul_one, hUlf _ (Real.exp_pos 1), hUlf 1 one_pos, Real.log_exp, Real.log_one] at h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  field_simp at h
  nlinarith [hapos]

/-- AKMM, (12.37), p. 353, **"only if"** under the stated class: if at every leisure level
`ℓ ∈ (0, 1)` the candidate `a(ℓ)C^{1−s(ℓ)}/(1 − s(ℓ)) + b(ℓ)` of `eq_12_A_2` satisfies the
hypotheses of `eq_12_A_3`, then `s ≡ σ` and `b ≡ b₀` are constant on `(0, 1)`: `U` is the KPR
form `C^{1−σ}a(ℓ)/(1 − σ)` up to an additive constant. -/
theorem eq_12_37_only_if {a s b a' s' b' : ℝ → ℝ} {Ul : ℝ → ℝ → ℝ}
    (ha : ∀ l ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt a (a' l) l)
    (hs : ∀ l ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt s (s' l) l)
    (hb : ∀ l ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt b (b' l) l)
    (hapos : ∀ l ∈ Set.Ioo (0 : ℝ) 1, 0 < a l) (hs1 : ∀ l ∈ Set.Ioo (0 : ℝ) 1, s l ≠ 1)
    (hUl : ∀ l ∈ Set.Ioo (0 : ℝ) 1, ∀ C, 0 < C →
      HasDerivAt (fun x => a x * C ^ (1 - s x) / (1 - s x) + b x) (Ul l C) l)
    (hhom : ∀ l ∈ Set.Ioo (0 : ℝ) 1, ∀ g, 0 < g → ∀ C, 0 < C →
      Ul l (g * C) * (a l * C ^ (-s l)) = g * Ul l C * (a l * (g * C) ^ (-s l))) :
    ∃ σ b₀, ∀ l ∈ Set.Ioo (0 : ℝ) 1, s l = σ ∧ b l = b₀ := by
  have hzero : ∀ l ∈ Set.Ioo (0 : ℝ) 1, s' l = 0 ∧ b' l = 0 := fun l hl =>
    eq_12_A_3 (ha l hl) (hs l hl) (hb l hl) (hapos l hl) (hs1 l hl) (hUl l hl) (hhom l hl)
  have hmid : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨s (1 / 2), b (1 / 2), fun l hl => ⟨?_, ?_⟩⟩
  · exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 1).isPreconnected
      (fun y hy => (hs y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hs y hy).deriv, (hzero y hy).1]; rfl) hl hmid
  · exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 1).isPreconnected
      (fun y hy => (hb y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hb y hy).deriv, (hzero y hy).2]; rfl) hl hmid

/-- The hypotheses of `eq_12_37_only_if` are satisfiable: for `a ≡ 1`, `s ≡ 2`, `b ≡ 0`
(`U = −C^{−1}`) the leisure derivative is `0` and the homogeneity condition holds. -/
theorem eq_12_37_only_if_instance :
    ∀ l ∈ Set.Ioo (0 : ℝ) 1, ∀ C, 0 < C →
      HasDerivAt (fun x => (fun _ => (1 : ℝ)) x * C ^ (1 - (fun _ => (2 : ℝ)) x) /
        (1 - (fun _ => (2 : ℝ)) x) + (fun _ => (0 : ℝ)) x) 0 l ∧
      ∀ g, 0 < g → (0 : ℝ) * (1 * C ^ (-(2 : ℝ))) = g * 0 * (1 * (g * C) ^ (-(2 : ℝ))) := by
  intro l _ C _
  exact ⟨hasDerivAt_const l _, fun g _ => by ring⟩

end AKMM.LaborSupply
