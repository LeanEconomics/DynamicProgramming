/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalContinuum
import EquilibriaWithDistortions.GlobalExamples

/-!
# Exercise 18.9: monotone iteration with a consumption floor (SLP p. 560)

`GlobalContinuum` shows that with a compact metric shock space `Ξ` (a closed bounded interval is
one) and a Feller transition, `T` is well defined on `F₊`, maps `F₊` into itself and is monotone.
This module carries out monotone iteration from the least element `0` (as in Theorem 17.7) and
shows that the limit `lfp = sup_n Tⁿ0` is a fixed point with consumption bounded away from zero,
given a **consumption floor** (`ConsFloor`): one `c > 0` with `ψ − Tⁿ0 ≥ c` for every `n`.
`GlobalContinuumFloor` proves the floor with no extra hypothesis (`ContModel.consFloor`); here it
is also derived from a **uniform anchor** (`UniformAnchor`, `consFloor_of_uniformAnchor`).

* `UniformAnchor`: some level `K ≥ 0` lies below every maximal sustainable stock `k̄(ξ)` and has
  `β(1 − θ) f′(K, ξ) ≤ 1` for every `ξ`; equivalently (`uniformAnchor_iff`), one `K` satisfies
  `k*(ξ) ≤ K < k̄(ξ)` for all `ξ`. It holds with one technology (`uniformAnchor_of_identical`)
  and whenever the technologies share `f′` (`uniformAnchor_of_f'_eq`).
* `StrongFeller`: `ξ ↦ ∫ g dκ(ξ)` is continuous for every bounded Borel `g` (for instance i.i.d.
  shocks, `strongFeller_of_const`). It is used only for continuity of the fixed point in `ξ`.

Results.
* `Tit_U'_le`, `exists_cons_lb`: the uniform anchor gives a consumption floor. Above `K`, low
  consumption forces next period's capital above `K`, where `β(1 − θ) f′ ≤ 1`, so a bound on
  marginal utility reproduces itself; below `K`, low consumption raises capital by at least `δ`,
  so after at most `⌈K/δ⌉` steps the bound above `K` takes over.
* `lfpc`, `Tc_lfpc`: given a floor, `lfp` is a fixed point of `T` (the limit step by dominated
  convergence and the continuity of the crossing point); `lfpc_cons_lb`: `ψ − lfp ≥ c > 0`;
  `lfpc_le_of_super`: `lfp` lies below every supersolution in `F₊` (the least fixed point).
* `ex_18_9_borel_equilibrium` (Feller property only): `lfp` is a fixed point with consumption
  bounded away from zero, continuous and monotone in `k`, Borel in `ξ`; `lfpc_euler_KT` and, under
  the cross-state condition, `lfpc_euler` give the integral Euler equation at every `(k, ξ)`.
* `isInFc_lfpc`, `ex_18_9_exists_equilibrium`: with the strong Feller property, `lfp ∈ F₊` is the
  least fixed point of `T`, with `ψ − lfp ≥ c > 0`; `ex_18_9_equilibrium` adds the Euler equation
  under the cross-state condition.
* `exCont`: shocks i.i.d. uniform on `[0, 1]`, `U = √`, technologies
  `f(k, ξ) = b(ξ) + 3k/(1 + k)` with `k̄(ξ) = 2 + ξ`, which differ across shocks
  (`exCont_tech_ne`); it satisfies the uniform anchor and the strong Feller property, so it has an
  equilibrium with consumption bounded away from zero (`exCont_exists_equilibrium`).

**Strong Feller.** The limit of the iterates is a priori only Borel (lower semicontinuous) in `ξ`,
and the Feller property moves the right side of (9) continuously only for continuous integrands;
the strong Feller property is used for continuity of `lfp` in `ξ` and for nothing else.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

namespace ContModel

open Set Filter Topology MeasureTheory

variable {Ξ : Type} [MetricSpace Ξ] [CompactSpace Ξ] [Nonempty Ξ] [MeasurableSpace Ξ]
  [BorelSpace Ξ] (C : ContModel Ξ)

/-- The **uniform anchor**: a level `K ≥ 0` below every maximal sustainable stock `k̄(ξ)` with
`β(1 − θ) f′(K, ξ) ≤ 1` for every shock (so `K` is at least every steady state `k*(ξ)`). -/
def UniformAnchor : Prop :=
  ∃ K, 0 ≤ K ∧ (∀ ξ, K < (C.tech ξ).kbar) ∧ ∀ ξ, C.β * (1 - C.θ) * (C.tech ξ).f' K ≤ 1

/-- The **strong Feller property**: `ξ ↦ ∫ g dκ(ξ)` is continuous for every bounded Borel
`g`. -/
def StrongFeller : Prop :=
  ∀ g : Ξ → ℝ, Measurable g → (∃ D, ∀ x, |g x| ≤ D) → Continuous fun ξ => ∫ x, g x ∂(C.κ ξ)

/-- The iterates `Tⁿ0` from the least element `0` of `F₊`. -/
noncomputable def Tit (n : ℕ) : Ξ → ℝ → ℝ := C.Tc^[n] (fun _ _ => 0)

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- `Tⁿ⁺¹0 = T(Tⁿ0)`. -/
theorem Tit_succ (n : ℕ) : C.Tit (n + 1) = C.Tc (C.Tit n) :=
  Function.iterate_succ_apply' _ _ _

/-- Every iterate lies in `F₊`. -/
theorem isInFc_Tit (n : ℕ) : C.IsInFc (C.Tit n) := by
  induction n with
  | zero => exact C.isInFc_zero
  | succ n ih => rw [Tit_succ]; exact ex_18_9 ih

/-- The iterates increase. -/
theorem Tit_le_succ (n : ℕ) : ∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tit n ξ k ≤ C.Tit (n + 1) ξ k := by
  induction n with
  | zero =>
    intro ξ k _
    rw [Tit_succ]
    exact eulerCross_nonneg
  | succ n ih =>
    intro ξ k hk
    have e1 : C.Tit (n + 1) ξ k = C.Tc (C.Tit n) ξ k := by rw [Tit_succ]
    have e2 : C.Tit (n + 1 + 1) ξ k = C.Tc (C.Tit (n + 1)) ξ k := by rw [Tit_succ C (n + 1)]
    rw [e2, e1]
    exact ex_18_9_mono (C.isInFc_Tit n) (C.isInFc_Tit (n + 1)) ih ξ hk

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- For `y ∈ [0, B]`, `ψ(y, ·)` is continuous. -/
theorem psi_continuous_shock {y : ℝ} (hy : y ∈ Icc 0 C.B) :
    Continuous fun ξ => (C.tech ξ).psi y :=
  C.psi_cont.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hy, mem_univ _⟩

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- For `y ∈ [0, B]`, `f′(y, ·)` is continuous. -/
theorem f'_continuous_shock {y : ℝ} (hy : y ∈ Icc 0 C.B) :
    Continuous fun ξ => (C.tech ξ).f' y :=
  C.f'_cont.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hy, mem_univ _⟩

omit [BorelSpace Ξ] in
/-- A uniform positive lower bound on `ψ(0, ξ)`. -/
theorem exists_psi_zero_lb : ∃ p > 0, ∀ ξ, p ≤ (C.tech ξ).psi 0 := by
  obtain ⟨ξ0, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (C.psi_continuous_shock ⟨le_rfl, C.B_pos.le⟩).continuousOn
  exact ⟨(C.tech ξ0).psi 0, (C.tech ξ0).psi_pos le_rfl,
    fun ξ => isMinOn_iff.1 hmin ξ (mem_univ _)⟩

omit [BorelSpace Ξ] in
/-- A uniform upper bound on `f′(0, ξ)`. -/
theorem exists_f'_zero_ub : ∃ A, ∀ ξ, (C.tech ξ).f' 0 ≤ A := by
  obtain ⟨ξ0, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (C.f'_continuous_shock ⟨le_rfl, C.B_pos.le⟩).continuousOn
  exact ⟨(C.tech ξ0).f' 0, fun ξ => isMaxOn_iff.1 hmax ξ (mem_univ _)⟩

omit [BorelSpace Ξ] in
/-- A uniform gap `ψ(k, ξ) − k ≥ 2δ` on `[0, K]` when `K` lies below every `k̄(ξ)`. -/
theorem exists_gap_lb {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ξ, K < (C.tech ξ).kbar) :
    ∃ δ > 0, ∀ ξ, ∀ k ∈ Icc 0 K, 2 * δ ≤ (C.tech ξ).psi k - k := by
  have hKB : K ≤ C.B := ((hK (Classical.arbitrary Ξ)).trans_le (C.kbar_le _)).le
  have hc : ContinuousOn (fun p : ℝ × Ξ => (C.tech p.2).psi p.1 - p.1) (Icc 0 K ×ˢ univ) :=
    (C.psi_cont.mono (prod_mono (Icc_subset_Icc_right hKB) subset_rfl)).sub continuousOn_fst
  obtain ⟨q, hq, hmin⟩ := (isCompact_Icc.prod isCompact_univ).exists_isMinOn
    ⟨((0 : ℝ), Classical.arbitrary Ξ), ⟨le_rfl, hK0⟩, mem_univ _⟩ hc
  have hpos : 0 < (C.tech q.2).psi q.1 - q.1 := by
    have := (C.tech q.2).lt_psi hq.1.1 (hq.1.2.trans_lt (hK q.2))
    linarith
  refine ⟨((C.tech q.2).psi q.1 - q.1) / 2, half_pos hpos, fun ξ k hk => ?_⟩
  have := isMinOn_iff.1 hmin (k, ξ) ⟨hk, mem_univ _⟩
  simp only at this
  linarith

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `U′(ψ(k, ξ)) ≤ U′(p)` when `p ≤ ψ(0, ξ)`. -/
theorem U'_psi_le {p : ℝ} (hp : 0 < p) (hpψ : ∀ ξ, p ≤ (C.tech ξ).psi 0) (ξ : Ξ) {k : ℝ}
    (hk : 0 ≤ k) : C.U' ((C.tech ξ).psi k) ≤ C.U' p := by
  have h1 := (C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk) hk
  exact C.isMarginalUtility.strictAnti.antitoneOn hp (hp.trans_le ((hpψ ξ).trans h1))
    ((hpψ ξ).trans h1)

variable {C} in
/-- A pointwise bound on the integrand bounds the right side. -/
theorem Rc_le {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) {y : ℝ} (hy : y ∈ Icc 0 C.B) {D : ℝ}
    (hD : ∀ x, C.G h y x ≤ D) : C.Rc h ξ y ≤ C.β * (1 - C.θ) * D := by
  have := C.κ_prob ξ
  refine mul_le_mul_of_nonneg_left ?_ C.coef_pos.le
  calc ∫ x, C.G h y x ∂(C.κ ξ) ≤ ∫ _x, D ∂(C.κ ξ) :=
        integral_mono (hh.G_integrable hy ξ) (integrable_const D) hD
    _ = D := by simp

/-- **The key estimate**: a bound on marginal utility along the iterates, by induction on the
number of iterations and on the number of `δ`-steps below `K`. -/
theorem Tit_U'_le {K δ p A : ℝ} (hK0 : 0 ≤ K) (hKf : ∀ ξ, C.β * (1 - C.θ) * (C.tech ξ).f' K ≤ 1)
    (hδ : 0 < δ) (hgap : ∀ ξ, ∀ k ∈ Icc 0 K, 2 * δ ≤ (C.tech ξ).psi k - k) (hp : 0 < p)
    (hpψ : ∀ ξ, p ≤ (C.tech ξ).psi 0) (hA : ∀ ξ, (C.tech ξ).f' 0 ≤ A) (n : ℕ) :
    ∀ s : ℕ, ∀ ξ, ∀ k ∈ Icc 0 C.B, K - s * δ ≤ k →
      C.U' ((C.tech ξ).psi k - C.Tit n ξ k) ≤
        max (C.U' δ) (C.U' p) * max 1 (C.β * (1 - C.θ) * A) ^ s := by
  set B0 := max (C.U' δ) (C.U' p) with hB0
  set L := max 1 (C.β * (1 - C.θ) * A) with hL
  have hu := C.isMarginalUtility
  have hB0pos : 0 < B0 := (hu.pos δ hδ).trans_le (le_max_left _ _)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hB0le : ∀ s : ℕ, B0 ≤ B0 * L ^ s := fun s =>
    le_mul_of_one_le_right hB0pos.le (one_le_pow₀ hL1)
  have hcoef := C.coef_pos
  induction n with
  | zero =>
    intro s ξ k hk _
    change C.U' ((C.tech ξ).psi k - 0) ≤ B0 * L ^ s
    rw [sub_zero]
    exact ((C.U'_psi_le hp hpψ ξ hk.1).trans (le_max_right _ _)).trans (hB0le s)
  | succ n ih =>
    intro s ξ k hk hks
    have hh := C.isInFc_Tit n
    rw [Tit_succ]
    set y := C.Tc (C.Tit n) ξ k with hydef
    rcases ex_18_9_spec_KT hh ξ hk with ⟨hlt, heq⟩ | ⟨h0, -⟩
    · have hyB : y ∈ Icc 0 C.B := ⟨eulerCross_nonneg, hlt.le.trans (C.psi_le_B ξ hk)⟩
      by_cases hc : δ ≤ (C.tech ξ).psi k - y
      · have := hu.strictAnti.antitoneOn hδ (hδ.trans_le hc) hc
        exact (this.trans (le_max_left _ _)).trans (hB0le s)
      · push Not at hc
        rw [heq]
        by_cases hkK : K ≤ k
        · have hψK := (C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 hK0)
            (mem_Ici.2 (hK0.trans hkK)) hkK
          have hg := hgap ξ K ⟨hK0, le_rfl⟩
          have hyK : K ≤ y := by linarith
          have hD : ∀ x, C.G (C.Tit n) y x ≤ B0 / (C.β * (1 - C.θ)) := by
            intro x
            have hU := ih 0 x y hyB
              (by simp only [CharP.cast_eq_zero, zero_mul, sub_zero]; exact hyK)
            rw [pow_zero, mul_one] at hU
            have hf : (C.tech x).f' y ≤ (C.tech x).f' K :=
              (C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 hK0) (mem_Ici.2 hyB.1) hyK
            have hfK : (C.tech x).f' K ≤ 1 / (C.β * (1 - C.θ)) := by
              rw [le_div_iff₀ hcoef]; linarith [hKf x]
            have hc' : 0 < (C.tech x).psi y - C.Tit n x y := by linarith [hh.lt_psi x y hyB]
            calc C.G (C.Tit n) y x ≤ (C.tech x).f' K * B0 :=
                  mul_le_mul hf hU (hu.pos _ hc').le ((C.tech x).f'_pos hK0).le
              _ ≤ 1 / (C.β * (1 - C.θ)) * B0 := mul_le_mul_of_nonneg_right hfK hB0pos.le
              _ = B0 / (C.β * (1 - C.θ)) := by ring
          have := Rc_le hh ξ hyB hD
          rw [mul_div_cancel₀ _ hcoef.ne'] at this
          exact this.trans (hB0le s)
        · push Not at hkK
          have hs : s ≠ 0 := by
            rintro rfl
            simp only [CharP.cast_eq_zero, zero_mul, sub_zero] at hks
            linarith
          obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
          have hg := hgap ξ k ⟨hk.1, hkK.le⟩
          have hys : K - s' * δ ≤ y := by
            push_cast at hks
            linarith
          have hD : ∀ x, C.G (C.Tit n) y x ≤ A * (B0 * L ^ s') := by
            intro x
            have hU := ih s' x y hyB hys
            have hf : (C.tech x).f' y ≤ A :=
              ((C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hyB.1)
                hyB.1).trans (hA x)
            have hc' : 0 < (C.tech x).psi y - C.Tit n x y := by linarith [hh.lt_psi x y hyB]
            exact mul_le_mul hf hU (hu.pos _ hc').le
              (((C.tech x).f'_pos le_rfl).le.trans (hA x))
          have h1 := Rc_le hh ξ hyB hD
          have h2 : C.β * (1 - C.θ) * A ≤ L := le_max_right _ _
          have h3 : 0 ≤ B0 * L ^ s' := mul_nonneg hB0pos.le (pow_nonneg (by linarith) _)
          calc C.Rc (C.Tit n) ξ y ≤ C.β * (1 - C.θ) * (A * (B0 * L ^ s')) := h1
            _ = (C.β * (1 - C.θ) * A) * (B0 * L ^ s') := by ring
            _ ≤ L * (B0 * L ^ s') := mul_le_mul_of_nonneg_right h2 h3
            _ = B0 * L ^ (s' + 1) := by ring
    · rw [show y = 0 from h0, sub_zero]
      exact ((C.U'_psi_le hp hpψ ξ hk.1).trans (le_max_right _ _)).trans (hB0le s)

/-- A **consumption floor** for the iterates: one `c > 0` with `ψ − Tⁿ0 ≥ c` on `[0, B] × Ξ` for
every `n`. It follows from the uniform anchor (`consFloor_of_uniformAnchor`) and, with no extra
hypothesis, from the auxiliary planner of `GlobalContinuumFloor` (`ContModel.consFloor`). -/
def ConsFloor : Prop :=
  ∃ c > 0, ∀ n ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - C.Tit n ξ k

/-- **Consumption along the iterates is bounded away from zero** under the uniform anchor. -/
theorem exists_cons_lb (hA : C.UniformAnchor) :
    ∃ c > 0, ∀ n ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - C.Tit n ξ k := by
  obtain ⟨K, hK0, hKk, hKf⟩ := hA
  obtain ⟨δ, hδ, hgap⟩ := C.exists_gap_lb hK0 hKk
  obtain ⟨p, hp, hpψ⟩ := C.exists_psi_zero_lb
  obtain ⟨A, hA⟩ := C.exists_f'_zero_ub
  set S := ⌈K / δ⌉₊
  set Mbar := max (C.U' δ) (C.U' p) * max 1 (C.β * (1 - C.θ) * A) ^ S
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    (C.isMarginalUtility.inada.eventually_gt_atTop Mbar)
  refine ⟨ε, hε, fun n ξ k hk => ?_⟩
  have hS : K - S * δ ≤ k := by
    have h1 : K / δ ≤ S := Nat.le_ceil _
    rw [div_le_iff₀ hδ] at h1
    linarith [hk.1]
  have hU := C.Tit_U'_le hK0 hKf hδ hgap hp hpψ hA n S ξ k hk hS
  have hc : 0 < (C.tech ξ).psi k - C.Tit n ξ k := by
    linarith [(C.isInFc_Tit n).lt_psi ξ k hk]
  by_contra hlt
  push Not at hlt
  have : Mbar < C.U' ((C.tech ξ).psi k - C.Tit n ξ k) := hball ⟨by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]; exact hlt, hc⟩
  linarith

/-- The uniform anchor gives a consumption floor. -/
theorem consFloor_of_uniformAnchor (hA : C.UniformAnchor) : C.ConsFloor :=
  C.exists_cons_lb hA

/-- The least fixed point `lfp(ξ, k) = sup_n (Tⁿ0)(ξ, k)`. -/
noncomputable def lfpc (ξ : Ξ) (k : ℝ) : ℝ := ⨆ n, C.Tit n ξ k

/-- `Tⁿ0 → lfp` pointwise on `[0, B] × Ξ`. -/
theorem tendsto_Tit (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    Tendsto (fun n => C.Tit n ξ k) atTop (𝓝 (C.lfpc ξ k)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => C.Tit_le_succ n ξ k hk)
    ⟨(C.tech ξ).psi k, forall_mem_range.2 fun n => ((C.isInFc_Tit n).lt_psi ξ k hk).le⟩

variable {C} in
omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- Members of `F₊` change by at most the change in `ψ`. -/
theorem IsInFc.abs_sub_le {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (x : Ξ) {a b : ℝ}
    (ha : a ∈ Icc 0 C.B) (hb : b ∈ Icc 0 C.B) :
    |h x a - h x b| ≤ |(C.tech x).psi a - (C.tech x).psi b| := by
  rcases le_total a b with hab | hab
  · have h1 := hh.mono x ha hb hab
    have h2 : (C.tech x).psi a - h x a ≤ (C.tech x).psi b - h x b := hh.mono_sub x ha hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hh.mono x hb ha hab
    have h2 : (C.tech x).psi b - h x b ≤ (C.tech x).psi a - h x a := hh.mono_sub x hb ha hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- `|lfp(x, a) − lfp(x, b)| ≤ |ψ(a, x) − ψ(b, x)|`. -/
theorem lfpc_abs_sub_le (x : Ξ) {a b : ℝ} (ha : a ∈ Icc 0 C.B) (hb : b ∈ Icc 0 C.B) :
    |C.lfpc x a - C.lfpc x b| ≤ |(C.tech x).psi a - (C.tech x).psi b| :=
  le_of_tendsto' (((C.tendsto_Tit x ha).sub (C.tendsto_Tit x hb)).abs)
    fun n => (C.isInFc_Tit n).abs_sub_le x ha hb

/-- `lfp(x, ·)` is continuous on `[0, B]`. -/
theorem lfpc_continuousOn (x : Ξ) : ContinuousOn (C.lfpc x) (Icc 0 C.B) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨δ, hδ, hψ⟩ := Metric.continuousOn_iff.1 ((C.tech x).psi_continuousOn.mono
    (Icc_subset_Ici_self : Icc (0 : ℝ) C.B ⊆ Ici 0)) b hb ε hε
  refine ⟨δ, hδ, fun a ha hab => ?_⟩
  have h1 := hψ a ha hab
  rw [Real.dist_eq] at h1 ⊢
  exact (C.lfpc_abs_sub_le x ha hb).trans_lt h1

/-- `lfp ≥ 0`. -/
theorem lfpc_nonneg (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) : 0 ≤ C.lfpc ξ k :=
  ge_of_tendsto' (C.tendsto_Tit ξ hk) fun n => (C.isInFc_Tit n).nonneg ξ k hk

/-- `lfp(ξ, ·)` is nondecreasing. -/
theorem lfpc_mono (ξ : Ξ) : MonotoneOn (C.lfpc ξ) (Icc 0 C.B) := fun _ ha _ hb hab =>
  le_of_tendsto_of_tendsto' (C.tendsto_Tit ξ ha) (C.tendsto_Tit ξ hb)
    fun n => (C.isInFc_Tit n).mono ξ ha hb hab

/-- `ψ(·, ξ) − lfp(ξ, ·)` is nondecreasing. -/
theorem lfpc_mono_sub (ξ : Ξ) :
    MonotoneOn (fun k => (C.tech ξ).psi k - C.lfpc ξ k) (Icc 0 C.B) := fun _ ha _ hb hab =>
  le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub (C.tendsto_Tit ξ ha))
    (tendsto_const_nhds.sub (C.tendsto_Tit ξ hb)) fun n => (C.isInFc_Tit n).mono_sub ξ ha hb hab

/-- Given a consumption floor, consumption at the least fixed point is bounded away from zero. -/
theorem lfpc_cons_lb (hF : C.ConsFloor) :
    ∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - C.lfpc ξ k := by
  obtain ⟨c, hc, hlb⟩ := hF
  exact ⟨c, hc, fun ξ k hk => ge_of_tendsto' (tendsto_const_nhds.sub (C.tendsto_Tit ξ hk))
    fun n => hlb n ξ k hk⟩

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The integrand is bounded by `A U′(c)` where consumption tomorrow is at least `c`. -/
theorem abs_G_le {h : Ξ → ℝ → ℝ} {c A : ℝ} (hc : 0 < c) (hA : ∀ ξ, (C.tech ξ).f' 0 ≤ A)
    {y : ℝ} (hy : 0 ≤ y) {x : Ξ} (hcx : c ≤ (C.tech x).psi y - h x y) :
    |C.G h y x| ≤ A * C.U' c := by
  have hu := C.isMarginalUtility
  have hf0 := (C.tech x).f'_pos hy
  have hU0 := hu.pos _ (hc.trans_le hcx)
  simp only [G]
  rw [abs_of_pos (mul_pos hf0 hU0)]
  have hf : (C.tech x).f' y ≤ A :=
    ((C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy).trans (hA x)
  exact mul_le_mul hf (hu.strictAnti.antitoneOn hc (hc.trans_le hcx) hcx) hU0.le
    (hf0.le.trans hf)

/-- The integrands along the iterates converge to the integrand at `lfp`. -/
theorem tendsto_G_Tit (hpos : ∀ ξ, ∀ k ∈ Icc 0 C.B, 0 < (C.tech ξ).psi k - C.lfpc ξ k)
    {y : ℝ} (hy : y ∈ Icc 0 C.B) (x : Ξ) :
    Tendsto (fun n => C.G (C.Tit n) y x) atTop (𝓝 (C.G C.lfpc y x)) :=
  tendsto_const_nhds.mul ((C.isMarginalUtility.cont.continuousAt
    (Ioi_mem_nhds (hpos x y hy))).tendsto.comp (tendsto_const_nhds.sub (C.tendsto_Tit x hy)))

/-- The integrand at `lfp` is Borel in the shock. -/
theorem measurable_G_lfpc (hpos : ∀ ξ, ∀ k ∈ Icc 0 C.B, 0 < (C.tech ξ).psi k - C.lfpc ξ k)
    {y : ℝ} (hy : y ∈ Icc 0 C.B) : Measurable fun x => C.G C.lfpc y x :=
  measurable_of_tendsto_metrizable (f := fun n x => C.G (C.Tit n) y x)
    (fun n => ((C.isInFc_Tit n).G_continuous hy).measurable)
    (tendsto_pi_nhds.2 (C.tendsto_G_Tit hpos hy))

/-- Given a consumption floor, the integrand at `lfp` is integrable. -/
theorem integrable_G_lfpc (hF : C.ConsFloor) {y : ℝ} (hy : y ∈ Icc 0 C.B) (ξ : Ξ) :
    Integrable (fun x => C.G C.lfpc y x) (C.κ ξ) := by
  obtain ⟨c, hc, hlb⟩ := C.lfpc_cons_lb hF
  obtain ⟨A, hA'⟩ := C.exists_f'_zero_ub
  have := C.κ_prob ξ
  exact Integrable.of_bound (C.measurable_G_lfpc (fun ξ k hk => hc.trans_le (hlb ξ k hk))
    hy).aestronglyMeasurable (A * C.U' c) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact C.abs_G_le hc hA' hy.1 (hlb x y hy))

/-- Given a consumption floor, the right sides along the iterates converge to the right side at
`lfp` (dominated convergence). -/
theorem tendsto_Rc_Tit (hF : C.ConsFloor) (ξ : Ξ) {y : ℝ} (hy : y ∈ Icc 0 C.B) :
    Tendsto (fun n => C.Rc (C.Tit n) ξ y) atTop (𝓝 (C.Rc C.lfpc ξ y)) := by
  obtain ⟨c', hc', hlb'⟩ := C.lfpc_cons_lb hF
  obtain ⟨c, hc, hlb⟩ := hF
  obtain ⟨A, hA'⟩ := C.exists_f'_zero_ub
  have := C.κ_prob ξ
  refine tendsto_const_nhds.mul (tendsto_integral_of_dominated_convergence
    (fun _ => A * C.U' c) (fun n => ((C.isInFc_Tit n).G_continuous hy).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun x => ?_)
    (ae_of_all _ (C.tendsto_G_Tit (fun ξ k hk => hc'.trans_le (hlb' ξ k hk)) hy)))
  rw [Real.norm_eq_abs]
  exact C.abs_G_le hc hA' hy.1 (hlb n x y hy)

/-- Given a consumption floor, the right side at `lfp` is an `IsEulerRHS` on `[0, B]` for every
current shock (finite, nonincreasing and continuous in `y`). No continuity in the shock is
needed. -/
theorem isEulerRHS_lfpc (hF : C.ConsFloor) (ξ : Ξ) :
    IsEulerRHS C.B (fun _ => False) (C.Rc C.lfpc ξ) := by
  obtain ⟨c, hc, hlb⟩ := C.lfpc_cons_lb hF
  obtain ⟨A, hA'⟩ := C.exists_f'_zero_ub
  have hpos : ∀ ξ, ∀ k ∈ Icc 0 C.B, 0 < (C.tech ξ).psi k - C.lfpc ξ k :=
    fun ξ k hk => hc.trans_le (hlb ξ k hk)
  have := C.κ_prob ξ
  refine ⟨fun _ _ _ _ _ hz => hz, ?_, ?_, fun _ _ hz => hz.elim⟩
  · intro y y' hy' hyy hyB _
    have hyK : y ∈ Icc 0 C.B := ⟨hy'.trans hyy, hyB⟩
    have hy'K : y' ∈ Icc 0 C.B := ⟨hy', hyy.trans hyB⟩
    refine mul_le_mul_of_nonneg_left (integral_mono (C.integrable_G_lfpc hF hyK ξ)
      (C.integrable_G_lfpc hF hy'K ξ) fun x => ?_) C.coef_pos.le
    have hc' := hpos x y' hy'K
    have hcc : (C.tech x).psi y' - C.lfpc x y' ≤ (C.tech x).psi y - C.lfpc x y :=
      C.lfpc_mono_sub x hy'K hyK hyy
    have hU := C.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc
    have hf : (C.tech x).f' y ≤ (C.tech x).f' y' :=
      (C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 hy') (mem_Ici.2 hyK.1) hyy
    exact mul_le_mul hf hU (C.isMarginalUtility.pos _ (hc'.trans_le hcc)).le
      ((C.tech x).f'_pos hy').le
  · intro y hy _
    refine ⟨Eventually.of_forall fun _ hz => hz, ?_⟩
    change ContinuousWithinAt (fun y => C.β * (1 - C.θ) * ∫ x, C.G C.lfpc y x ∂(C.κ ξ))
      (Icc 0 C.B) y
    refine continuousWithinAt_const.mul (continuousWithinAt_of_dominated
      (bound := fun _ => A * C.U' c)
      (eventually_mem_nhdsWithin.mono fun y' hy' =>
        (C.measurable_G_lfpc hpos hy').aestronglyMeasurable)
      (eventually_mem_nhdsWithin.mono fun y' hy' => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact C.abs_G_le hc hA' hy'.1 (hlb x y' hy'))
      (integrable_const _) (ae_of_all _ fun x => ?_))
    have h1 : ContinuousWithinAt (fun y' => (C.tech x).f' y') (Icc 0 C.B) y :=
      (C.tech x).f'_continuousOn.mono Icc_subset_Ici_self y hy
    have h2 : ContinuousWithinAt (fun y' => (C.tech x).psi y' - C.lfpc x y') (Icc 0 C.B) y :=
      ((C.tech x).psi_continuousOn.mono Icc_subset_Ici_self y hy).sub
        (C.lfpc_continuousOn x y hy)
    exact h1.mul (ContinuousAt.comp_continuousWithinAt
      (f := fun y' => (C.tech x).psi y' - C.lfpc x y')
      (C.isMarginalUtility.cont.continuousAt (Ioi_mem_nhds (hpos x y hy))) h2)

/-- **`lfp` is a fixed point of `T`** given a consumption floor. -/
theorem Tc_lfpc (hF : C.ConsFloor) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.Tc C.lfpc ξ k = C.lfpc ξ k := by
  have hP := (C.tech ξ).psi_pos hk.1
  have hPB := C.psi_le_B ξ hk
  have h1 : Tendsto (fun n => C.Tc (C.Tit n) ξ k) atTop (𝓝 (C.Tc C.lfpc ξ k)) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hev := eventually_abs_eulerCross_sub_le (u := C.U') (l := atTop)
      (Zs := fun _ _ => False) (Rs := fun n => C.Rc (C.Tit n) ξ) C.isMarginalUtility
      (C.isEulerRHS_lfpc hF ξ) (fun n => (C.isInFc_Tit n).isEulerRHS ξ) hP hPB
      (fun y hy0 hyP => ⟨fun hz => hz.elim, fun _ => ⟨Eventually.of_forall fun _ hz => hz,
        C.tendsto_Rc_Tit hF ξ ⟨hy0, hyP.le.trans hPB⟩⟩⟩) (half_pos hε)
    filter_upwards [hev] with n hn
    rw [Real.dist_eq]
    exact hn.trans_lt (half_lt_self hε)
  have h2 : Tendsto (fun n => C.Tc (C.Tit n) ξ k) atTop (𝓝 (C.lfpc ξ k)) :=
    ((tendsto_add_atTop_iff_nat 1).2 (C.tendsto_Tit ξ hk)).congr fun n => by rw [Tit_succ]
  exact tendsto_nhds_unique h1 h2

variable {C} in
/-- A supersolution `h ∈ F₊` (`T h ≤ h`) lies above every iterate `Tⁿ0`. -/
theorem Tit_le_of_super {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h)
    (hsup : ∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k ≤ h ξ k) (n : ℕ) :
    ∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tit n ξ k ≤ h ξ k := by
  induction n with
  | zero => exact fun ξ k hk => hh.nonneg ξ k hk
  | succ n ih =>
    intro ξ k hk
    rw [Tit_succ]
    exact (ex_18_9_mono (C.isInFc_Tit n) hh ih ξ hk).trans (hsup ξ k hk)

variable {C} in
/-- `lfp` lies below every supersolution in `F₊`, in particular below every fixed point. -/
theorem lfpc_le_of_super {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h)
    (hsup : ∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k ≤ h ξ k) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.lfpc ξ k ≤ h ξ k :=
  le_of_tendsto' (C.tendsto_Tit ξ hk) fun n => Tit_le_of_super hh hsup n ξ k hk

variable {C} in
omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- Joint continuity of `Th` from continuity of `ξ ↦ ∫ G h y dκ(ξ)` for each `y` (the argument of
`ex_18_9`, which needs no continuity of `h` in the shock). -/
theorem Tc_continuousOn_of {h : Ξ → ℝ → ℝ}
    (hR : ∀ ξ, IsEulerRHS C.B (fun _ => False) (C.Rc h ξ))
    (hcont : ∀ y ∈ Icc 0 C.B, Continuous fun ξ => ∫ x, C.G h y x ∂(C.κ ξ)) :
    ContinuousOn (fun p : ℝ × Ξ => C.Tc h p.2 p.1) (Icc 0 C.B ×ˢ univ) := by
  intro p hp
  have hk : p.1 ∈ Icc 0 C.B := hp.1
  set P0 := (C.tech p.2).psi p.1 with hP0def
  have hP0 : 0 < P0 := (C.tech p.2).psi_pos hk.1
  have hP0B : P0 ≤ C.B := C.psi_le_B p.2 hk
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hev := eventually_abs_eulerCross_sub_le (u := C.U') (l := 𝓝 p.2)
    (Zs := fun _ _ => False) (Rs := fun ξ => C.Rc h ξ) C.isMarginalUtility
    (hR p.2) hR hP0 hP0B
    (fun y hy0 hyP => ⟨fun hz => hz.elim, fun _ => ⟨Eventually.of_forall fun _ hz => hz,
      tendsto_const_nhds.mul ((hcont _ ⟨hy0, hyP.le.trans hP0B⟩).tendsto p.2)⟩⟩)
    (half_pos hε)
  obtain ⟨δ1, hδ1, hball⟩ := Metric.mem_nhds_iff.1 hev
  obtain ⟨δ2, hδ2, hψ⟩ := Metric.continuousWithinAt_iff.1 (C.psi_cont p hp) (ε / 2)
    (half_pos hε)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun q hq hd => ?_⟩
  have hqp : dist q.2 p.2 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hd2 : dist q.2 p.2 < δ1 := lt_of_le_of_lt hqp (hd.trans_le (min_le_left _ _))
  have e1 : |eulerCross C.U' (fun _ => False) (C.Rc h q.2) P0 - C.Tc h p.2 p.1| ≤ ε / 2 :=
    hball hd2
  have e2 := hψ hq (hd.trans_le (min_le_right _ _))
  rw [Real.dist_eq] at e2
  have e3 := abs_eulerCross_sub_le C.isMarginalUtility (hR q.2) hP0B (C.psi_le_B q.2 hq.1)
  rw [Real.dist_eq]
  change |C.Tc h q.2 q.1 - C.Tc h p.2 p.1| < ε
  have := abs_sub_le (C.Tc h q.2 q.1) (eulerCross C.U' (fun _ => False) (C.Rc h q.2) P0)
    (C.Tc h p.2 p.1)
  simp only [Tc, ← hP0def] at this e1 e3 ⊢
  linarith

/-- **`lfp ∈ F₊`** given a consumption floor and the strong Feller property. -/
theorem isInFc_lfpc (hF : C.ConsFloor) (hSF : C.StrongFeller) : C.IsInFc C.lfpc := by
  obtain ⟨c, hc, hlb⟩ := C.lfpc_cons_lb hF
  obtain ⟨A, hA'⟩ := C.exists_f'_zero_ub
  have hpos : ∀ ξ, ∀ k ∈ Icc 0 C.B, 0 < (C.tech ξ).psi k - C.lfpc ξ k :=
    fun ξ k hk => hc.trans_le (hlb ξ k hk)
  refine ⟨?_, fun ξ k hk => C.lfpc_nonneg ξ hk, fun ξ k hk => by linarith [hpos ξ k hk],
    C.lfpc_mono, C.lfpc_mono_sub⟩
  refine (Tc_continuousOn_of (C.isEulerRHS_lfpc hF) fun y hy => hSF _
    (C.measurable_G_lfpc hpos hy) ⟨A * C.U' c, fun x => C.abs_G_le hc hA' hy.1 (hlb x y hy)⟩
    ).congr fun p hp => ?_
  exact (C.Tc_lfpc hF p.2 hp.1).symm

/-- Given a consumption floor (Feller property only), `lfp` solves the integral Euler equation in
Kuhn–Tucker form at every `(k, ξ)`. -/
theorem lfpc_euler_KT (hF : C.ConsFloor) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    (C.lfpc ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.lfpc ξ k) = C.Rc C.lfpc ξ (C.lfpc ξ k)) ∨
    (C.lfpc ξ k = 0 ∧ C.Rc C.lfpc ξ 0 ≤ C.U' ((C.tech ξ).psi k)) := by
  have hP := (C.tech ξ).psi_pos hk.1
  have hfix : eulerCross C.U' (fun _ => False) (C.Rc C.lfpc ξ) ((C.tech ξ).psi k) =
      C.lfpc ξ k := C.Tc_lfpc hF ξ hk
  rcases eulerCross_spec_KT C.isMarginalUtility (C.isEulerRHS_lfpc hF ξ) hP
    (C.psi_le_B ξ hk) with ⟨h1, -, h3⟩ | ⟨-, h2⟩ | ⟨h1, -, h3⟩
  · rw [hfix] at h1 h3
    exact Or.inl ⟨h1, h3⟩
  · exact (h2 0 le_rfl hP).elim
  · rw [hfix] at h1
    exact Or.inr ⟨h1, h3⟩

/-- Given a consumption floor and the cross-state condition (Feller property only), `lfp` solves
the integral Euler equation as an equation at every `(k, ξ)`. -/
theorem lfpc_euler (hF : C.ConsFloor) (hCS : C.CrossState) (ξ : Ξ) {k : ℝ}
    (hk : k ∈ Icc 0 C.B) :
    C.lfpc ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.lfpc ξ k) = C.Rc C.lfpc ξ (C.lfpc ξ k) := by
  have hP := (C.tech ξ).psi_pos hk.1
  have hPB := C.psi_le_B ξ hk
  have h0K : (0 : ℝ) ∈ Icc 0 C.B := ⟨le_rfl, C.B_pos.le⟩
  obtain ⟨c, hc, hlb⟩ := C.lfpc_cons_lb hF
  have h0 : EulerBelow C.U' (fun _ => False) (C.Rc C.lfpc ξ) ((C.tech ξ).psi k) 0 := by
    right
    have := C.κ_prob ξ
    have hz : (fun x => (C.tech x).f' 0 * C.U' ((C.tech x).psi 0)) =
        fun x => C.G (fun _ _ => 0) 0 x := by
      funext x; simp [G]
    have hint : Integrable (fun x => (C.tech x).f' 0 * C.U' ((C.tech x).psi 0)) (C.κ ξ) := by
      rw [hz]; exact (C.isInFc_zero).G_integrable h0K ξ
    have hle : ∫ x, (C.tech x).f' 0 * C.U' ((C.tech x).psi 0) ∂(C.κ ξ) ≤
        ∫ x, C.G C.lfpc 0 x ∂(C.κ ξ) := by
      refine integral_mono hint (C.integrable_G_lfpc hF h0K ξ) fun x => ?_
      have hcx : 0 < (C.tech x).psi 0 - C.lfpc x 0 := hc.trans_le (hlb x 0 h0K)
      have hle' : (C.tech x).psi 0 - C.lfpc x 0 ≤ (C.tech x).psi 0 := by
        linarith [C.lfpc_nonneg x h0K]
      exact mul_le_mul_of_nonneg_left
        (C.isMarginalUtility.strictAnti.antitoneOn hcx ((C.tech x).psi_pos le_rfl) hle')
        ((C.tech x).f'_pos le_rfl).le
    have hψ := (C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.1) hk.1
    have h2 : C.U' ((C.tech ξ).psi k) ≤ C.U' ((C.tech ξ).psi 0) :=
      C.isMarginalUtility.strictAnti.antitoneOn ((C.tech ξ).psi_pos le_rfl)
        ((C.tech ξ).psi_pos hk.1) hψ
    have h3 := mul_le_mul_of_nonneg_left hle C.coef_pos.le
    have h4 := hCS ξ
    simp only [Rc, sub_zero]
    linarith
  have hfix : eulerCross C.U' (fun _ => False) (C.Rc C.lfpc ξ) ((C.tech ξ).psi k) =
      C.lfpc ξ k := C.Tc_lfpc hF ξ hk
  rcases eulerCross_spec C.isMarginalUtility (C.isEulerRHS_lfpc hF ξ) hP hPB h0 with
    ⟨h1, -, h3⟩ | ⟨-, h2⟩
  · rw [hfix] at h1 h3
    exact ⟨h1, h3⟩
  · exact (h2 0 le_rfl hP).elim

/-- **A Borel equilibrium of Exercise 18.9 (Feller property only).** Given a consumption floor,
`lfp = lim Tⁿ0` is a fixed point of `T` on `[0, B] × Ξ` with consumption bounded away from zero;
`lfp(ξ, ·)` is continuous with `lfp` and `ψ − lfp` nondecreasing, and `lfp(·, k)` is Borel. It lies
below every supersolution in `F₊`. -/
theorem ex_18_9_borel_equilibrium (hF : C.ConsFloor) :
    (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc C.lfpc ξ k = C.lfpc ξ k) ∧
      (∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - C.lfpc ξ k) ∧
      (∀ ξ, ContinuousOn (C.lfpc ξ) (Icc 0 C.B)) ∧
      (∀ ξ, MonotoneOn (C.lfpc ξ) (Icc 0 C.B)) ∧
      (∀ ξ, MonotoneOn (fun k => (C.tech ξ).psi k - C.lfpc ξ k) (Icc 0 C.B)) ∧
      (∀ k ∈ Icc 0 C.B, Measurable fun ξ => C.lfpc ξ k) ∧
      ∀ h, C.IsInFc h → (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k ≤ h ξ k) →
        ∀ ξ, ∀ k ∈ Icc 0 C.B, C.lfpc ξ k ≤ h ξ k := by
  refine ⟨fun ξ _ hk => C.Tc_lfpc hF ξ hk, C.lfpc_cons_lb hF, C.lfpc_continuousOn, C.lfpc_mono,
    C.lfpc_mono_sub, fun k hk => ?_, fun _ hh hsup ξ _ hk => lfpc_le_of_super hh hsup ξ hk⟩
  exact measurable_of_tendsto_metrizable (f := fun n ξ => C.Tit n ξ k)
    (fun n => ((C.isInFc_Tit n).cont.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨hk, mem_univ _⟩).measurable)
    (tendsto_pi_nhds.2 fun ξ => C.tendsto_Tit ξ hk)

/-- **Exercise 18.9: existence of an equilibrium with a continuum of shocks.** Given a consumption
floor and the strong Feller property, `T` has a fixed point `h ∈ F₊` with consumption bounded
away from zero, `ψ − h ≥ c > 0`; it is the least supersolution in `F₊`, hence the least fixed
point. -/
theorem ex_18_9_exists_equilibrium (hF : C.ConsFloor) (hSF : C.StrongFeller) :
    ∃ h, C.IsInFc h ∧ (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k = h ξ k) ∧
      (∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - h ξ k) ∧
      ∀ h', C.IsInFc h' → (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h' ξ k ≤ h' ξ k) →
        ∀ ξ, ∀ k ∈ Icc 0 C.B, h ξ k ≤ h' ξ k :=
  ⟨C.lfpc, C.isInFc_lfpc hF hSF, fun ξ _ hk => C.Tc_lfpc hF ξ hk, C.lfpc_cons_lb hF,
    fun _ hh hsup ξ _ hk => lfpc_le_of_super hh hsup ξ hk⟩

/-- **Exercise 18.9, equilibrium in equation form.** Given a consumption floor, the strong Feller
property and the cross-state condition, there is `h ∈ F₊`, a fixed point of `T`, with consumption
bounded away from zero, solving the integral Euler equation
`U′[ψ(k, ξ) − h(ξ, k)] = β(1 − θ) ∫ f′(h(ξ, k), x) U′[ψ(h(ξ, k), x) − h(x, h(ξ, k))] κ(ξ, dx)`
at every `(k, ξ) ∈ [0, B] × Ξ`. -/
theorem ex_18_9_equilibrium (hF : C.ConsFloor) (hSF : C.StrongFeller)
    (hCS : C.CrossState) :
    ∃ h, C.IsInFc h ∧ (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k = h ξ k) ∧
      (∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - h ξ k) ∧
      ∀ ξ, ∀ k ∈ Icc 0 C.B, C.U' ((C.tech ξ).psi k - h ξ k) = C.Rc h ξ (h ξ k) :=
  ⟨C.lfpc, C.isInFc_lfpc hF hSF, fun ξ _ hk => C.Tc_lfpc hF ξ hk, C.lfpc_cons_lb hF,
    fun ξ _ hk => (C.lfpc_euler hF hCS ξ hk).2⟩

/-! ### When the hypotheses hold -/

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The uniform anchor says exactly that one level `K` lies above every steady state `k*(ξ)` and
below every maximal sustainable stock `k̄(ξ)`. -/
theorem uniformAnchor_iff :
    C.UniformAnchor ↔ ∃ K, ∀ ξ, (C.tech ξ).kstar ≤ K ∧ K < (C.tech ξ).kbar := by
  constructor
  · rintro ⟨K, hK0, hKk, hKf⟩
    refine ⟨K, fun ξ => ⟨?_, hKk ξ⟩⟩
    by_contra hlt
    push Not at hlt
    have := (C.tech ξ).one_lt_euler hK0 hlt
    rw [C.tech_β ξ, C.tech_θ ξ] at this
    linarith [hKf ξ]
  · rintro ⟨K, hK⟩
    have ξ0 := Classical.arbitrary Ξ
    have hK0 : 0 ≤ K := (C.tech ξ0).kstar_pos.le.trans (hK ξ0).1
    refine ⟨K, hK0, fun ξ => (hK ξ).2, fun ξ => ?_⟩
    have hf := (C.tech ξ).f'_strictAntiOn.antitoneOn (mem_Ici.2 (C.tech ξ).kstar_pos.le)
      (mem_Ici.2 hK0) (hK ξ).1
    have he := (C.tech ξ).euler_kstar
    have hc := (C.tech ξ).euler_coef_pos
    rw [C.tech_β ξ, C.tech_θ ξ] at he hc
    nlinarith

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- **Technologies with a common marginal product** satisfy the uniform anchor: then every shock
has the same steady state `k*`, which lies below every `k̄(ξ)`. The levels `f(·, ξ)`, hence
`ψ(·, ξ)` and `k̄(ξ)`, may differ across shocks (for instance through the endowment `f(0, ξ)`). -/
theorem uniformAnchor_of_f'_eq {ξ0 : Ξ} (hf' : ∀ ξ, (C.tech ξ).f' = (C.tech ξ0).f') :
    C.UniformAnchor := by
  have heq : ∀ ξ, (C.tech ξ0).kstar = (C.tech ξ).kstar := fun ξ => by
    refine (C.tech ξ).kstar_unique (C.tech ξ0).kstar_pos.le ?_
    have he := (C.tech ξ0).euler_kstar
    rw [C.tech_β ξ0, C.tech_θ ξ0] at he
    rw [hf' ξ, C.tech_β ξ, C.tech_θ ξ]
    exact he
  exact (C.uniformAnchor_iff).2 ⟨(C.tech ξ0).kstar, fun ξ =>
    ⟨(heq ξ).ge, (heq ξ).trans_lt (C.tech ξ).kstar_lt_kbar⟩⟩

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- With one technology in every state the uniform anchor holds. -/
theorem uniformAnchor_of_identical (M : GlobalModel) (hM : ∀ ξ, C.tech ξ = M) :
    C.UniformAnchor :=
  (C.uniformAnchor_iff).2 ⟨M.kstar, fun ξ => by rw [hM ξ]; exact ⟨le_rfl, M.kstar_lt_kbar⟩⟩

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- A transition that does not depend on the current shock (i.i.d. shocks) is strong Feller. -/
theorem strongFeller_of_const (μ : Measure Ξ) (hκ : ∀ ξ, C.κ ξ = μ) : C.StrongFeller := by
  intro g _ _
  simp only [hκ]
  exact continuous_const

end ContModel

/-! ### A heterogeneous example -/

open Set Filter Topology MeasureTheory

/-- The endowment `b(t) = [(2 + t)² − (2 + t) − 1/2](2 + t)/(3 + t)²` of the example, chosen so
that `ψ(k) − k` vanishes at `k̄ = 2 + t` (`ratTech_psi_sub`). -/
noncomputable def exB (t : ℝ) : ℝ := ((2 + t) ^ 2 - (2 + t) - 1 / 2) * (2 + t) / (3 + t) ^ 2

/-- `b(t) > 0`. -/
theorem exB_pos {t : ℝ} (ht : 0 ≤ t) : 0 < exB t := by
  unfold exB
  have : 0 < (2 + t) ^ 2 - (2 + t) - 1 / 2 := by nlinarith
  positivity

/-- `b(t) ≤ 1 + t`. -/
theorem exB_le {t : ℝ} (ht : 0 ≤ t) : exB t ≤ 1 + t := by
  unfold exB
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg t]

/-- The third coefficient identity of `ratModel` for the example. -/
theorem exB_h3 {t : ℝ} (ht : 0 ≤ t) :
    (2 + t) * (1 + t - exB t) - exB t / (2 + t) = 2 * exB t + 3 * (1 - 1 / 2) - 1 := by
  unfold exB
  have h1 : (2 + t) ≠ 0 := by linarith
  have h2 : (3 + t) ≠ 0 := by linarith
  field_simp
  ring

/-- The technology of shock `t ∈ [0, 1]`. -/
noncomputable def exTech (t : ℝ) (ht : 0 ≤ t) : GlobalModel :=
  ratModel (9 / 10) (1 / 2) 3 (exB t) (2 + t) (1 + t - exB t) (exB t / (2 + t)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (exB_pos ht) (by linarith)
    (by linarith [exB_le ht]) (div_pos (exB_pos ht) (by linarith))
    (mul_div_cancel₀ _ (by linarith : (2 + t) ≠ 0)).symm (by ring) (exB_h3 ht)

/-- After-tax income in the example. -/
theorem exTech_psi (t : ℝ) (ht : 0 ≤ t) (k : ℝ) :
    (exTech t ht).psi k = exB t + 3 * k / (1 + k) - 1 / 2 * k * (3 / (1 + k) ^ 2) := rfl

/-- The marginal product in the example does not depend on the shock. -/
theorem exTech_f' (t : ℝ) (ht : 0 ≤ t) : (exTech t ht).f' = fun k => 3 / (1 + k) ^ 2 := rfl

/-- The maximal sustainable stock of shock `t` is `2 + t`. -/
theorem exTech_kbar (t : ℝ) (ht : 0 ≤ t) : (exTech t ht).kbar = 2 + t := rfl

/-- The endowment is continuous in the shock. -/
theorem exB_continuous : ContinuousOn exB (Ici 0) := by
  unfold exB
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
  have : (0:ℝ) ≤ t := ht
  positivity

/-- **A continuum economy with heterogeneous technologies**: `Ξ = [0, 1]`, shocks i.i.d.
uniform, `β = 9/10`, `θ = 1/2`, `U = √`, `f(k, ξ) = b(ξ) + 3k/(1 + k)`, `k̄(ξ) = 2 + ξ`. -/
noncomputable def exCont : ContModel unitInterval where
  tech ξ := exTech ξ ξ.2.1
  β := 9 / 10
  θ := 1 / 2
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  B := 3
  κ := fun _ => volume
  tech_β _ := rfl
  tech_θ _ := rfl
  tech_U _ := rfl
  tech_U' _ := rfl
  kbar_le ξ := by rw [exTech_kbar]; linarith [ξ.2.2]
  κ_prob _ := inferInstance
  κ_feller _ _ := continuous_const
  psi_cont := by
    simp only [exTech_psi]
    have hb : Continuous fun p : ℝ × unitInterval => exB (p.2 : ℝ) :=
      exB_continuous.comp_continuous (continuous_subtype_val.comp continuous_snd)
        fun p => p.2.2.1
    refine (hb.continuousOn.add ?_).sub ?_
    · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_
      have : (0:ℝ) ≤ p.1 := hp.1.1
      positivity
    · refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div (by fun_prop) (by fun_prop)
        fun p hp => ?_)
      have : (0:ℝ) ≤ p.1 := hp.1.1
      positivity
  f'_cont := by
    simp only [exTech_f']
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_
    have : (0:ℝ) ≤ p.1 := hp.1.1
    positivity

/-- In `exCont` the technologies differ across shocks: `k̄(0) = 2` and `k̄(1) = 3`. -/
theorem exCont_tech_ne : exCont.tech 0 ≠ exCont.tech 1 := by
  intro h
  have := congrArg GlobalModel.kbar h
  simp [exCont, exTech_kbar] at this

/-- `exCont` satisfies the uniform anchor (common marginal product). -/
theorem exCont_uniformAnchor : exCont.UniformAnchor :=
  exCont.uniformAnchor_of_f'_eq (ξ0 := 0) fun _ => rfl

/-- `exCont` is strong Feller (i.i.d. shocks). -/
theorem exCont_strongFeller : exCont.StrongFeller :=
  exCont.strongFeller_of_const volume fun _ => rfl

/-- **A non-degenerate equilibrium with heterogeneous technologies and a continuum of shocks**:
`exCont` has a fixed point of `T` in `F₊` with consumption bounded away from zero. -/
theorem exCont_exists_equilibrium :
    ∃ h, exCont.IsInFc h ∧ (∀ ξ, ∀ k ∈ Icc 0 exCont.B, exCont.Tc h ξ k = h ξ k) ∧
      ∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 exCont.B, c ≤ (exCont.tech ξ).psi k - h ξ k := by
  obtain ⟨h, h1, h2, h3, -⟩ := exCont.ex_18_9_exists_equilibrium
    (exCont.consFloor_of_uniformAnchor exCont_uniformAnchor) exCont_strongFeller
  exact ⟨h, h1, h2, h3⟩

end StokeyLucasPrescott.EquilibriaWithDistortions
