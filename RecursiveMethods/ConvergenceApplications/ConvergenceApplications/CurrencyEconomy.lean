/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.CurrencyMarkov
import ConvergenceApplications.GrowthPolicy

/-!
# Equilibrium in a pure currency economy: the household problem

SLP §13.5, Exercise 13.5(a)–(c), (e), (f), (h), pp. 397–400. Each period a household receives
`y > 0`, holds real balances `m ≥ 0`, draws an i.i.d. preference shock `z ∈ Z = [z̲, z̄]` with
distribution `μ`, and solves (1)
`v(m, z) = max_{y ≤ m′ ≤ m + y} [U(m + y − m′, z) + β ∫ v(m′, z′) μ(dz′)]`.
Write `W(m′) = ∫ v(m′, z′) μ(dz′)` (`cashW`), `g(m, z)` for the policy (`cashPolicy`) and
`c(m, z) = m + y − g(m, z)` for consumption.

* `CurrencyHyp`: `0 < β < 1`, `y > 0`, `U` bounded and continuous on `ℝ₊ × Z`, `U(·, z)` strictly
  increasing and strictly concave. `cashΓ`, `cashF`, `cashModel`: (1) in the first formulation
  of Chapter 9 on `X = ℝ₊`; `cash_boundedDP`: the hypotheses of §9.2 (`isLHC_cashΓ`,
  `isUHC_cashΓ`; Lemma 9.5 since `Z` is compact and i.i.d. shocks are Feller).
* **Exercise 13.5(a)** (`ex_13_5a`): a unique bounded continuous `v` satisfies (1), and the
  maximum in (1) is attained (Theorem 9.6, as in the solutions manual).
* **Exercise 13.5(b)**, monotonicity and concavity: `cash_strictMono` (Theorem 9.7);
  `cash_concave` (`T` preserves concavity in `m`: the graph of `Γ` is convex and
  `U(m + y − m′, z)` is jointly concave); `cash_strictConcave` (strict concavity). Theorem 9.8
  does not apply, since Assumption 9.10 fails; the proof is a chord argument: if `v(·, z)` were
  affine on a chord, consumption would be the same at its ends (`cash_flat_step`), so the chord
  is carried to `μ`-a.e. affine chords of `v(·, z′)` whose rise is `1/β` times smaller, and the
  supremum `S` of all rises satisfies `S ≤ βS`. Also `cashW_strictConcave`, `cashW_mono`,
  `abs_cashW_le`. Differentiability is in `CurrencyEnvelope.lean`.
* **Exercise 13.5(c)** (`ex_13_5c`): the policy correspondence is a continuous function `g`
  (`cash_uniqueArgmax`: the objective is strictly concave in `m′`; Theorem of the Maximum);
  `cashPolicy_spec`, `cashPolicy_eq_of_ge` characterise `g` by optimality.
* **Exercise 13.5(h)** (`ex_13_5h`): `g(m, ·)` is nonincreasing, given increasing differences
  (`CurrencyIncreasingDiff`, the difference form of "`U₁(c, ·)` strictly increasing",
  `currencyIncreasingDiff_of_deriv`). Derivative-free: add the optimality inequalities at two
  shocks (the continuation value is the same, the shocks being i.i.d.).
* **Exercise 13.5(e)**, weak form: `cashPolicy_mono` (`g(·, z)` nondecreasing) and
  `cashCons_mono` (`c(·, z)` nondecreasing: `0 ≤ g(m₂, z) − g(m₁, z) ≤ m₂ − m₁`), by
  derivative-free exchange arguments (`currency_concave_exchange`). The strict form in the book
  is false (`ex_13_5e_counterexample`); corrected statement `ex_13_5e_corrected`.
* **Exercise 13.5(f)** (`ex_13_5f`): there is `m̄ ≥ y > 0` with `g(m̄, z̲) = m̄`; taking the least
  such `m̄`, `g(m, z̲) > m` on `[y, m̄)`. If `g(m, z̲) > m` for all `m ≥ 2y`, consuming `y` more is
  feasible and optimality gives `β[W(m) − W(m − y)] ≥ U(2y, z̲) − U(y, z̲) > 0` for all
  `m ≥ 2y`, so the bounded `W` would be unbounded; then the intermediate value theorem applies.
  `m̄ = y` can occur (`ex_13_5f_mbar_eq_y`).

Formalisation notes. `U : ℝ → ℝ → ℝ` is used only on `ℝ₊ × Z`. `X = ℝ₊` is the subtype `Ici 0`
and `Z` the subtype `Icc z̲ z̄`; `W` and `v(·, z)` are extended to `ℝ` by `0` off `ℝ₊`
(`liftS`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- The hypotheses of §13.5 (p. 397): `0 < β < 1`, `y > 0`, `Z = [z̲, z̄]`, and
`U : ℝ₊ × Z → ℝ` bounded and continuous with `U(·, z)` strictly increasing and strictly concave.
(Differentiability and the monotonicity of `U₁` in `z` are assumed where they are used.) -/
structure CurrencyHyp (U : ℝ → ℝ → ℝ) (β y zl zh : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  y_pos : 0 < y
  hz : zl ≤ zh
  U_cont : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Ici 0 ×ˢ Icc zl zh)
  U_bdd : ∃ B, ∀ c, 0 ≤ c → ∀ z ∈ Icc zl zh, |U c z| ≤ B
  U_mono : ∀ z ∈ Icc zl zh, StrictMonoOn (fun c => U c z) (Ici 0)
  U_conc : ∀ z ∈ Icc zl zh, StrictConcaveOn ℝ (Ici 0) fun c => U c z

variable {U : ℝ → ℝ → ℝ} {β y zl zh : ℝ}

/-- The feasible end-of-period balances `Γ(m) = [y, m + y]` (cash in advance `c ≤ m` is
`m′ ≥ y`; the budget is `m′ = m + y − c`). -/
def cashΓ (y : ℝ) {zl zh : ℝ} (s : Ici (0 : ℝ) × Icc zl zh) : Set (Ici (0 : ℝ)) :=
  {m' | y ≤ (m' : ℝ) ∧ (m' : ℝ) ≤ (s.1 : ℝ) + y}

/-- The return `F(m, m′, z) = U(m + y − m′, z)`. -/
def cashF (U : ℝ → ℝ → ℝ) (y : ℝ) {zl zh : ℝ} (p : Ici (0 : ℝ) × Ici (0 : ℝ) × Icc zl zh) :
    ℝ :=
  U ((p.1 : ℝ) + y - (p.2.1 : ℝ)) (p.2.2 : ℝ)

/-- The household problem (1) in the first formulation of Chapter 9, with i.i.d. shocks. -/
abbrev cashModel (μ : Measure (Icc zl zh)) (U : ℝ → ℝ → ℝ) (β y : ℝ) :
    Model (Ici (0 : ℝ)) (Ici (0 : ℝ)) (Icc zl zh) :=
  Model.first (Kernel.const _ μ) (cashΓ y) (cashF U y) β

/-- `y ∈ Γ(m)`: spending everything is always feasible. -/
theorem cashΓ_nonempty (hy : 0 < y) (s : Ici (0 : ℝ) × Icc zl zh) : (cashΓ y s).Nonempty :=
  ⟨⟨y, hy.le⟩, le_rfl, by linarith [mem_Ici.1 s.1.2]⟩

/-- `Γ` is l.h.c. -/
theorem isLHC_cashΓ (hy : 0 < y) (s : Ici (0 : ℝ) × Icc zl zh) : IsLHC (cashΓ y) s := by
  refine ⟨cashΓ_nonempty hy s, fun m' hm' xs hxs => ?_⟩
  have hx : ∀ n, (0 : ℝ) ≤ (xs n).1 := fun n => (xs n).1.2
  refine ⟨0, fun n => ⟨min (m' : ℝ) ((xs n).1 + y), mem_Ici.2 (le_min m'.2
    (by linarith [hx n]))⟩, fun n _ => ⟨le_min hm'.1 (by linarith [hx n]), min_le_right _ _⟩, ?_⟩
  have hc : Tendsto (fun n => ((xs n).1 : ℝ)) atTop (𝓝 (s.1 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto s).comp hxs
  have hlim := (tendsto_const_nhds (x := (m' : ℝ))).min (hc.add_const y)
  rw [min_eq_left hm'.2] at hlim
  exact tendsto_subtype_rng.2 hlim

/-- `Γ` is u.h.c. -/
theorem isUHC_cashΓ (hy : 0 < y) (s : Ici (0 : ℝ) × Icc zl zh) : IsUHC (cashΓ y) s := by
  refine ⟨cashΓ_nonempty hy s, fun xs hxs ys hys => ?_⟩
  have hc : Tendsto (fun n => ((xs n).1 : ℝ)) atTop (𝓝 (s.1 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto s).comp hxs
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hc).bddAbove
  have hmem : ∀ n, ((ys n : ℝ)) ∈ Icc y (C + y) := fun n =>
    ⟨(hys n).1, (hys n).2.trans (by linarith [hC ⟨n, rfl⟩])⟩
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hle : a ≤ (s.1 : ℝ) + y := le_of_tendsto_of_tendsto hlim
    ((hc.comp hφ.tendsto_atTop).add_const y) (Eventually.of_forall fun n => (hys (φ n)).2)
  exact ⟨⟨a, mem_Ici.2 (by linarith [ha.1])⟩, ⟨ha.1, hle⟩, φ, hφ, tendsto_subtype_rng.2 hlim⟩

/-- The hypotheses of §9.2 hold for (1) (the solutions manual's part (a): Theorem 9.6 with
`Γ(m) = [y, m + y]` and `F(m, m′) = U(m + y − m′)`). Lemma 9.5 applies because `Z` is compact and
i.i.d. shocks are Feller. -/
theorem cash_boundedDP (h : CurrencyHyp U β y zl zh) (μ : Measure (Icc zl zh))
    [IsProbabilityMeasure μ] : BoundedDP (cashModel μ U β y) := by
  obtain ⟨B, hB⟩ := h.U_bdd
  refine ⟨cashΓ_nonempty h.y_pos, fun s => ?_, isLHC_cashΓ h.y_pos, isUHC_cashΓ h.y_pos, ?_,
    ⟨B, fun p hp => hB _ (sub_nonneg.2 hp.2) _ p.2.2.2⟩, h.β_pos, h.β_lt,
    continuous_fst.snd.continuousOn,
    contExp_first _ _ _ β (lemma_9_5_compact _ (isFeller_const μ))⟩
  · exact isClosed_Ici.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc
  · have hc : Continuous fun p : Ici (0 : ℝ) × Ici (0 : ℝ) × Icc zl zh =>
        (((p.1 : ℝ) + y - (p.2.1 : ℝ)), ((p.2.2 : ℝ))) :=
      (((continuous_subtype_val.comp continuous_fst).add continuous_const).sub
        (continuous_subtype_val.comp continuous_snd.fst)).prodMk
        (continuous_subtype_val.comp continuous_snd.snd)
    exact h.U_cont.comp hc.continuousOn fun p hp => ⟨sub_nonneg.2 hp.2, p.2.2.2⟩

/-- `W(m′) = ∫ v(m′, z′) μ(dz′)`, extended to `ℝ` (by `0` off `ℝ₊`). -/
noncomputable def cashW (μ : Measure (Icc zl zh)) (v : Ici (0 : ℝ) × Icc zl zh → ℝ) : ℝ → ℝ :=
  liftS fun m' : Ici (0 : ℝ) => ∫ z', v (m', z') ∂μ

/-- On `ℝ₊`, `W(m′) = ∫ v(m′, z′) μ(dz′)`. -/
theorem cashW_of_mem (μ : Measure (Icc zl zh)) (v : Ici (0 : ℝ) × Icc zl zh → ℝ)
    (m' : Ici (0 : ℝ)) : cashW μ v m' = ∫ z', v (m', z') ∂μ :=
  liftS_of_mem _ m'.2

/-- The objective of (1): `U(m + y − m′, z) + β ∫ v(m′, z′) μ(dz′)`. -/
theorem cash_objG (μ : Measure (Icc zl zh)) (v : Ici (0 : ℝ) × Icc zl zh → ℝ)
    (s : Ici (0 : ℝ) × Icc zl zh) (m' : Ici (0 : ℝ)) :
    objG (cashModel μ U β y) v (s, m') =
      U ((s.1 : ℝ) + y - m') (s.2 : ℝ) + β * cashW μ v m' := by
  rw [cashW_of_mem]
  rfl

/-- **Exercise 13.5(a).** There is a unique bounded continuous `v` satisfying (1); at each
`(m, z)` the maximum in (1) is attained. -/
theorem ex_13_5a (h : CurrencyHyp U β y zl zh) (μ : Measure (Icc zl zh))
    [IsProbabilityMeasure μ] :
    ∃ v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ,
      bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v ∧
      (∀ w, bellman (cashModel μ U β y) (cash_boundedDP h μ) w = w → w = v) ∧
      ∀ s : Ici (0 : ℝ) × Icc zl zh, IsGreatest
        ((fun m' : Ici (0 : ℝ) => U ((s.1 : ℝ) + y - m') (s.2 : ℝ) + β * cashW μ v m') ''
          cashΓ y s) (v s) := by
  obtain ⟨v, hv, huniq, -, -⟩ := ex_9_7b (cashModel μ U β y) (cash_boundedDP h μ)
  refine ⟨v, hv, huniq, fun s => ?_⟩
  obtain ⟨m', hm', hval, hmax⟩ := exists_bellman_argmax _ (cash_boundedDP h μ) v s
  rw [hv] at hval hmax
  refine ⟨⟨m', hm', ?_⟩, ?_⟩
  · rw [hval]; exact (cash_objG μ v s m').symm
  · rintro _ ⟨m'', hm'', rfl⟩
    have := hmax m'' hm''
    rw [show rhs _ _ s m'' = objG (cashModel μ U β y) v (s, m'') from rfl, cash_objG] at this
    exact this

/-! ### The value function: monotonicity and concavity (Exercise 13.5(b)) -/

variable (μ : Measure (Icc zl zh)) [IsProbabilityMeasure μ]

/-- The fixed point satisfies (1) with the maximum attained. -/
theorem cash_bellman_eq (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v)
    (s : Ici (0 : ℝ) × Icc zl zh) :
    ∃ m' ∈ cashΓ y s, v s = U ((s.1 : ℝ) + y - m') (s.2 : ℝ) + β * cashW μ v m' ∧
      ∀ m'' ∈ cashΓ y s, U ((s.1 : ℝ) + y - m'') (s.2 : ℝ) + β * cashW μ v m'' ≤ v s := by
  obtain ⟨m', hm', hval, hmax⟩ := exists_bellman_argmax _ (cash_boundedDP h μ) v s
  rw [hv] at hval hmax
  refine ⟨m', hm', ?_, fun m'' hm'' => ?_⟩
  · rw [hval]; exact cash_objG μ v s m'
  · have := hmax m'' hm''
    rw [show rhs _ _ s m'' = objG (cashModel μ U β y) v (s, m'') from rfl, cash_objG] at this
    exact this

/-- **Exercise 13.5(b)** (monotonicity, Theorem 9.7): `v(·, z)` is strictly increasing. -/
theorem cash_strictMono (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) :
    StrictMono fun m => v (m, z) := by
  refine theorem_9_7 _ _ _ β (cash_boundedDP h μ) (fun m m' m'' z hmm' hm'' => ?_)
    (fun m m' z hmm' m'' hm'' => ⟨hm''.1, hm''.2.trans (by
      have : (m : ℝ) ≤ m' := hmm'
      linarith)⟩) hv z
  have hlt : (m : ℝ) < m' := hmm'
  have h0 : 0 ≤ (m : ℝ) + y - m'' := sub_nonneg.2 hm''.2
  exact h.U_mono z.1 z.2 h0 (show (0 : ℝ) ≤ (m' : ℝ) + y - m'' by linarith) (by linarith)

/-- `(θm₀ + (1 − θ)m₁ : ℝ)` for the convex combination in `ℝ₊`. -/
theorem currency_cmb_Ici_val {x₀ x₁ : Ici (0 : ℝ)} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (cmb (convex_Ici 0) h0 h1 x₀ x₁ : ℝ) = θ * x₀ + (1 - θ) * x₁ := by
  simp [cmb]

omit [IsProbabilityMeasure μ] in
/-- The graph of `Γ` is convex. -/
theorem cash_mem_cmb {x₀ x₁ y₀ y₁ : Ici (0 : ℝ)} {z : Icc zl zh} (hy₀ : y₀ ∈ cashΓ y (x₀, z))
    (hy₁ : y₁ ∈ cashΓ y (x₁, z)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    cmb (convex_Ici 0) h0 h1 y₀ y₁ ∈ cashΓ y (cmb (convex_Ici 0) h0 h1 x₀ x₁, z) := by
  have e0 := hy₀
  have e1 := hy₁
  simp only [cashΓ, mem_ofPred_eq] at e0 e1
  change y ≤ (cmb (convex_Ici 0) h0 h1 y₀ y₁ : ℝ) ∧
    (cmb (convex_Ici 0) h0 h1 y₀ y₁ : ℝ) ≤ (cmb (convex_Ici 0) h0 h1 x₀ x₁ : ℝ) + y
  rw [currency_cmb_Ici_val, currency_cmb_Ici_val]
  have h1' : 0 ≤ 1 - θ := by linarith
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left e0.1 h0, mul_le_mul_of_nonneg_left e1.1 h1',
    mul_le_mul_of_nonneg_left e0.2 h0, mul_le_mul_of_nonneg_left e1.2 h1']

/-- `T` maps functions concave in `m` to functions concave in `m`. -/
theorem cash_bellman_concave (h : CurrencyHyp U β y zl zh)
    {w : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ} (hw : ∀ z, IsConcaveS (convex_Ici 0) fun x => w (x, z))
    (z : Icc zl zh) :
    IsConcaveS (convex_Ici 0) fun x =>
      bellman (cashModel μ U β y) (cash_boundedDP h μ) w (x, z) := by
  have hb := cash_boundedDP h μ
  intro x₀ x₁ θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax _ hb w (x₀, z)
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax _ hb w (x₁, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax _ hb w (cmb (convex_Ici 0) h0 h1 x₀ x₁, z)
  have hyθ := cash_mem_cmb hy₀ hy₁ h0 h1
  have hE := expV_comb (cashModel μ U β y) hb (fun _ _ _ _ _ _ _ _ => rfl) hw hy₀ hy₁ h0 h1 hyθ
  have hm := hmax _ hyθ
  have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
  have hc0 : (0 : ℝ) ≤ (x₀ : ℝ) + y - y₀ := sub_nonneg.2 hy₀.2
  have hc1 : (0 : ℝ) ≤ (x₁ : ℝ) + y - y₁ := sub_nonneg.2 hy₁.2
  have hU := (h.U_conc z.1 z.2).concaveOn.2 (mem_Ici.2 hc0) (mem_Ici.2 hc1) h0
    (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hU
  have hcθ : (cmb (convex_Ici 0) h0 h1 x₀ x₁ : ℝ) + y - (cmb (convex_Ici 0) h0 h1 y₀ y₁ : ℝ) =
      θ * ((x₀ : ℝ) + y - y₀) + (1 - θ) * ((x₁ : ℝ) + y - y₁) := by
    rw [currency_cmb_Ici_val, currency_cmb_Ici_val]; ring
  simp only [rhs] at hv₀ hv₁ hm
  change bellman _ hb w (x₀, z) = U ((x₀ : ℝ) + y - y₀) (z : ℝ) + β * _ at hv₀
  change bellman _ hb w (x₁, z) = U ((x₁ : ℝ) + y - y₁) (z : ℝ) + β * _ at hv₁
  change U ((cmb (convex_Ici 0) h0 h1 x₀ x₁ : ℝ) + y - (cmb (convex_Ici 0) h0 h1 y₀ y₁ : ℝ))
    (z : ℝ) + β * _ ≤ _ at hm
  rw [hcθ] at hm
  change θ * bellman _ hb w (x₀, z) + (1 - θ) * bellman _ hb w (x₁, z) ≤
    bellman _ hb w (cmb (convex_Ici 0) h0 h1 x₀ x₁, z)
  rw [hv₀, hv₁]
  change β * _ ≤ β * _ at hβE
  nlinarith

/-- **Exercise 13.5(b)** (concavity): `v(·, z)` is concave. -/
theorem cash_concave (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) :
    ∀ z, IsConcaveS (convex_Ici 0) fun x => v (x, z) :=
  (corollary_1 (S' := {w | ∀ z, IsConcaveS (convex_Ici 0) fun x => w (x, z)})
    (S'' := {w | ∀ z, IsConcaveS (convex_Ici 0) fun x => w (x, z)})
    (bellman_contraction _ (cash_boundedDP h μ)) hv ⟨0, fun _ _ _ _ _ _ => by simp⟩
    (isClosed_concaveX _) (fun _ hw => cash_bellman_concave μ h hw)
    fun _ hw => cash_bellman_concave μ h hw).1

omit [IsProbabilityMeasure μ] in
/-- **The step of the chord argument.** If `v(·, z)` is affine on a chord `[a, b]`, then
consumption is the same at `a` and `b`, so the optimal `m′_b − m′_a = b − a > 0`, `v(·, z′)` is
affine on `[m′_a, m′_b]` for `μ`-almost every `z′`, and
`v(b, z) − v(a, z) = β ∫ [v(m′_b, z′) − v(m′_a, z′)] μ(dz′)`. -/
theorem cash_flat_step [IsProbabilityMeasure μ] (h : CurrencyHyp U β y zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v)
    (hvc : ∀ z, IsConcaveS (convex_Ici 0) fun x => v (x, z)) {a b : Ici (0 : ℝ)}
    {z : Icc zl zh} (hab : a < b) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (heq : v (cmb (convex_Ici 0) h0.le h1.le a b, z) = θ * v (a, z) + (1 - θ) * v (b, z)) :
    ∃ ya yb : Ici (0 : ℝ), ya < yb ∧
      (∀ᵐ z' ∂μ, v (cmb (convex_Ici 0) h0.le h1.le ya yb, z') =
        θ * v (ya, z') + (1 - θ) * v (yb, z')) ∧
      v (b, z) - v (a, z) = β * ∫ z', (v (yb, z') - v (ya, z')) ∂μ := by
  obtain ⟨ya, hya, hva, -⟩ := cash_bellman_eq μ h hv (a, z)
  obtain ⟨yb, hyb, hvb, -⟩ := cash_bellman_eq μ h hv (b, z)
  obtain ⟨-, -, -, hmax⟩ := cash_bellman_eq μ h hv (cmb (convex_Ici 0) h0.le h1.le a b, z)
  have hyθ := cash_mem_cmb hya hyb h0.le h1.le
  have hm := hmax _ hyθ
  rw [cashW_of_mem] at hva hvb hm
  have hint := integrable_section_v μ v
  have hpt : ∀ z', θ * v (ya, z') + (1 - θ) * v (yb, z') ≤
      v (cmb (convex_Ici 0) h0.le h1.le ya yb, z') := fun z' => hvc z' ya yb θ h0.le h1.le
  set Ea := ∫ z', v (ya, z') ∂μ
  set Eb := ∫ z', v (yb, z') ∂μ
  set Eθ := ∫ z', v (cmb (convex_Ici 0) h0.le h1.le ya yb, z') ∂μ
  have hI : Integrable (fun z' => θ * v (ya, z') + (1 - θ) * v (yb, z')) μ :=
    ((hint ya).const_mul θ).add ((hint yb).const_mul (1 - θ))
  have hgapE : ∫ z', (v (cmb (convex_Ici 0) h0.le h1.le ya yb, z') -
      (θ * v (ya, z') + (1 - θ) * v (yb, z'))) ∂μ = Eθ - (θ * Ea + (1 - θ) * Eb) := by
    rw [integral_sub (hint _) hI,
      integral_add ((hint ya).const_mul θ) ((hint yb).const_mul (1 - θ)), integral_const_mul,
      integral_const_mul]
  have hE0 : 0 ≤ Eθ - (θ * Ea + (1 - θ) * Eb) := by
    rw [← hgapE]
    exact integral_nonneg fun z' => sub_nonneg.2 (hpt z')
  set ca := (a : ℝ) + y - ya
  set cb := (b : ℝ) + y - yb
  have hca : 0 ≤ ca := sub_nonneg.2 hya.2
  have hcb : 0 ≤ cb := sub_nonneg.2 hyb.2
  have hcθ : (cmb (convex_Ici 0) h0.le h1.le a b : ℝ) + y -
      (cmb (convex_Ici 0) h0.le h1.le ya yb : ℝ) = θ * ca + (1 - θ) * cb := by
    rw [currency_cmb_Ici_val, currency_cmb_Ici_val]; ring
  rw [hcθ] at hm
  have hU := (h.U_conc z.1 z.2).concaveOn.2 (mem_Ici.2 hca) (mem_Ici.2 hcb) h0.le
    (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hU
  have hβ := h.β_pos
  have hgapF : θ * U ca z + (1 - θ) * U cb z = U (θ * ca + (1 - θ) * cb) z := by
    nlinarith [mul_nonneg hβ.le hE0]
  have hceq : ca = cb := by
    by_contra hne
    have := (h.U_conc z.1 z.2).2 (mem_Ici.2 hca) (mem_Ici.2 hcb) hne h0
      (by linarith : (0 : ℝ) < 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    linarith
  have hEeq : Eθ - (θ * Ea + (1 - θ) * Eb) = 0 := by nlinarith
  refine ⟨ya, yb, ?_, ?_, ?_⟩
  · have hlt : (a : ℝ) < b := hab
    change (ya : ℝ) < yb
    have : (a : ℝ) + y - ya = (b : ℝ) + y - yb := hceq
    linarith
  · have hzero := (integral_eq_zero_iff_of_nonneg (fun z' => sub_nonneg.2 (hpt z'))
      ((hint _).sub hI)).1 (by rw [hgapE, hEeq])
    filter_upwards [hzero] with z' hz'
    simp only [Pi.zero_apply] at hz'
    linarith
  · rw [integral_sub (hint yb) (hint ya), hva, hvb, hceq]
    ring

/-- **Exercise 13.5(b)** (strict concavity). `v(·, z)` is strictly concave. Theorem 9.8 does not
apply (Assumption 9.10 fails: `F(m, m′) = U(m + y − m′)` is not strictly concave in `(m, m′)`).
If `v(·, z)` were affine on some chord, let `S` be the supremum of the rises `v(b, z) − v(a, z)`
over all such chords; `cash_flat_step` bounds every rise by `βS`, so `S ≤ βS`, while rises are
positive (`v` is strictly increasing). -/
theorem cash_strictConcave (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) :
    IsStrictConcaveS (convex_Ici 0) fun x => v (x, z) := by
  have hvc := cash_concave μ h hv
  have hmono := cash_strictMono μ h hv
  set D : Set ℝ := {d | ∃ a b : Ici (0 : ℝ), ∃ z : Icc zl zh, ∃ θ : ℝ,
    ∃ h0 : 0 < θ, ∃ h1 : θ < 1, a < b ∧
      v (cmb (convex_Ici 0) h0.le h1.le a b, z) = θ * v (a, z) + (1 - θ) * v (b, z) ∧
      d = v (b, z) - v (a, z)}
  have hD : D = ∅ := by
    by_contra hne
    obtain ⟨d₀, hd₀⟩ := nonempty_iff_ne_empty.2 hne
    have hbdd : BddAbove D := ⟨2 * ‖v‖, by
      rintro _ ⟨a, b, z, θ, h0, h1, -, -, rfl⟩
      have := v.dist_le_two_norm (b, z) (a, z)
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this⟩
    have hle : ∀ d ∈ D, d ≤ β * sSup D := by
      rintro _ ⟨a, b, z, θ, h0, h1, hab, heq, rfl⟩
      obtain ⟨ya, yb, hlt, hae, hdiff⟩ := cash_flat_step μ h hv hvc hab h0 h1 heq
      rw [hdiff]
      refine mul_le_mul_of_nonneg_left ?_ h.β_pos.le
      have hint := integrable_section_v μ v
      have := integral_mono_ae ((hint yb).sub (hint ya)) (integrable_const (sSup D))
        (hae.mono fun z' hz' => le_csSup hbdd ⟨ya, yb, z', θ, h0, h1, hlt, hz', rfl⟩)
      simpa using this
    have hS : sSup D ≤ β * sSup D := csSup_le ⟨d₀, hd₀⟩ hle
    have hpos : 0 < d₀ := by
      obtain ⟨a, b, z, θ, h0, h1, hab, -, rfl⟩ := hd₀
      exact sub_pos.2 (hmono z hab)
    have := lt_of_lt_of_le hpos (le_csSup hbdd hd₀)
    nlinarith [h.β_lt]
  intro x x' hne θ h0 h1
  refine lt_of_le_of_ne (hvc z x x' θ h0.le h1.le) fun heq => ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmem : v (x', z) - v (x, z) ∈ D := ⟨x, x', z, θ, h0, h1, hlt, heq.symm, rfl⟩
    rw [hD] at hmem
    exact hmem
  · have h0' : 0 < 1 - θ := by linarith
    have h1' : 1 - θ < 1 := by linarith
    have hc : cmb (convex_Ici 0) h0'.le h1'.le x' x = cmb (convex_Ici 0) h0.le h1.le x x' := by
      ext1
      rw [currency_cmb_Ici_val, currency_cmb_Ici_val]
      ring
    dsimp only at heq
    have hmem : v (x, z) - v (x', z) ∈ D := ⟨x', x, z, 1 - θ, h0', h1', hlt, by
      rw [hc, ← heq]; ring, rfl⟩
    rw [hD] at hmem
    exact hmem

/-- `W(m′) = ∫ v(m′, z′) μ(dz′)` is strictly concave on `ℝ₊`. -/
theorem cashW_strictConcave (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) :
    StrictConcaveOn ℝ (Ici 0) (cashW μ v) := by
  have hsc := cash_strictConcave μ h hv
  refine strictConcaveOn_liftS (hS := convex_Ici 0) fun x x' hne θ h0 h1 => ?_
  have hint := integrable_section_v μ v
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint x).const_mul θ) ((hint x').const_mul _)]
  exact integral_lt_integral_of_forall_lt (((hint x).const_mul θ).add ((hint x').const_mul _))
    (hint _) fun z' => hsc z' x x' hne θ h0 h1

/-- `W` is nondecreasing on `ℝ₊`. -/
theorem cashW_mono (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) {x x' : ℝ} (hx : 0 ≤ x)
    (hxx' : x ≤ x') : cashW μ v x ≤ cashW μ v x' := by
  have hint := integrable_section_v μ v
  rw [show cashW μ v x = cashW μ v (⟨x, hx⟩ : Ici (0 : ℝ)) from rfl,
    show cashW μ v x' = cashW μ v (⟨x', hx.trans hxx'⟩ : Ici (0 : ℝ)) from rfl,
    cashW_of_mem, cashW_of_mem]
  exact integral_mono (hint _) (hint _) fun z' =>
    (cash_strictMono μ h hv z').monotone (show (⟨x, hx⟩ : Ici (0 : ℝ)) ≤ ⟨x', _⟩ from hxx')

omit [IsProbabilityMeasure μ] in
/-- `|W| ≤ ‖v‖`. -/
theorem abs_cashW_le [IsProbabilityMeasure μ] (v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ) (x : ℝ) :
    |cashW μ v x| ≤ ‖v‖ := by
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [show cashW μ v x = cashW μ v (⟨x, hx⟩ : Ici (0 : ℝ)) from rfl, cashW_of_mem]
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖v‖)
      (f := fun z' => v (⟨x, hx⟩, z')) (Eventually.of_forall fun z' => v.norm_coe_le_norm _)
    simpa [Real.norm_eq_abs, measureReal_def] using this
  · simp only [cashW, liftS, hx, ↓reduceDIte, abs_zero]
    exact norm_nonneg _

/-! ### The policy function (Exercise 13.5(c)) -/

/-- **The weak exchange inequality.** For `φ` concave, `p ≤ q ≤ t` and `p + t = q + r`,
`φ(p) + φ(t) ≤ φ(q) + φ(r)`. -/
theorem currency_concave_exchange {S : Set ℝ} {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ S φ) {p q r t : ℝ}
    (hp : p ∈ S) (ht : t ∈ S) (hpq : p ≤ q) (hqt : q ≤ t) (hsum : p + t = q + r) :
    φ p + φ t ≤ φ q + φ r := by
  rcases (hpq.trans hqt).eq_or_lt with hpt | hpt
  · have hq : q = p := le_antisymm (hqt.trans hpt.ge) hpq
    have hr : r = p := by linarith
    rw [hq, hr, ← hpt]
  have hpt' : 0 < t - p := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = (t - q) / (t - p) := ⟨_, rfl⟩
  have hat : a * (t - p) = t - q := by rw [ha]; exact div_mul_cancel₀ _ hpt'.ne'
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (by linarith) hpt'.le
  have ha1 : 0 ≤ 1 - a := by
    have : a * (t - p) ≤ 1 * (t - p) := by rw [hat]; linarith
    linarith [le_of_mul_le_mul_right this hpt']
  have hq : a • p + (1 - a) • t = q := by
    simp only [smul_eq_mul]; linear_combination (-1 : ℝ) * hat
  have hr : (1 - a) • p + a • t = r := by
    simp only [smul_eq_mul]; linear_combination hat + hsum
  have h1 := hφ.2 hp ht ha0 ha1 (by ring)
  have h2 := hφ.2 hp ht ha1 ha0 (by ring)
  rw [hq] at h1
  rw [hr] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- Increments of a concave function decrease: for `0 ≤ a ≤ b` and `d ≥ 0`,
`φ(b + d) − φ(b) ≤ φ(a + d) − φ(a)`. -/
theorem currency_concave_increment_le {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ) {a b d : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b) (hd : 0 ≤ d) : φ (b + d) - φ b ≤ φ (a + d) - φ a := by
  rcases le_total (a + d) b with h | h
  · have := currency_concave_exchange hφ (mem_Ici.2 ha) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ b + d))
      (by linarith : a ≤ a + d) (by linarith : a + d ≤ b + d) (by ring : a + (b + d) = a + d + b)
    linarith
  · have := currency_concave_exchange hφ (mem_Ici.2 ha) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ b + d))
      hab (by linarith : b ≤ b + d) (by ring : a + (b + d) = b + (a + d))
    linarith

omit [IsProbabilityMeasure μ] in
/-- The maximizer in (1) is unique: the objective is strictly concave in `m′` (`U(·, z)` is
strictly concave and `W` concave). -/
theorem cash_uniqueArgmax [IsProbabilityMeasure μ] (h : CurrencyHyp U β y zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) :
    UniqueArgmax (cashΓ y) (objG (cashModel μ U β y) v) := by
  have hb := cash_boundedDP h μ
  have hW := (cashW_strictConcave μ h hv).concaveOn
  refine ⟨hb.nonempty, hb.compact, hb.lhc, hb.uhc, continuousOn_objG _ hb v,
    fun s y₁ hy₁ y₂ hy₂ => ?_⟩
  by_contra hne
  have hne' : (y₁ : ℝ) ≠ y₂ := fun h => hne (Subtype.ext h)
  set mid : Ici (0 : ℝ) := ⟨(y₁ + y₂ : ℝ) / 2, mem_Ici.2 (by linarith [y₁.2.out, y₂.2.out])⟩
  have hmid : mid ∈ cashΓ y s := by
    have e1 := hy₁.1; have e2 := hy₂.1
    simp only [cashΓ, mem_ofPred_eq] at e1 e2
    exact ⟨by change y ≤ ((y₁ : ℝ) + y₂) / 2; linarith,
      by change ((y₁ : ℝ) + y₂) / 2 ≤ _; linarith⟩
  have hle := le_maxValue (continuousOn_objG _ hb v) (hb.compact s) hmid
  rw [← hy₁.2] at hle
  have h12 := hy₂.2
  rw [← hy₁.2] at h12
  simp only [cash_objG] at hle h12
  have hc1 : (0 : ℝ) ≤ (s.1 : ℝ) + y - y₁ := sub_nonneg.2 hy₁.1.2
  have hc2 : (0 : ℝ) ≤ (s.1 : ℝ) + y - y₂ := sub_nonneg.2 hy₂.1.2
  have hU := (h.U_conc s.2.1 s.2.2).2 (mem_Ici.2 hc1) (mem_Ici.2 hc2)
    (fun h => hne' (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hWm := hW.2 (mem_Ici.2 y₁.2.out) (mem_Ici.2 y₂.2.out) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hU hWm
  have e1 : (1 / 2 : ℝ) * ((s.1 : ℝ) + y - y₁) + 1 / 2 * ((s.1 : ℝ) + y - y₂) =
      (s.1 : ℝ) + y - ((y₁ : ℝ) + y₂) / 2 := by ring
  have e2 : (1 / 2 : ℝ) * (y₁ : ℝ) + 1 / 2 * (y₂ : ℝ) = ((y₁ : ℝ) + y₂) / 2 := by ring
  rw [e1] at hU
  rw [e2] at hWm
  change U ((s.1 : ℝ) + y - ((y₁ : ℝ) + y₂) / 2) (s.2 : ℝ) +
    β * cashW μ v (((y₁ : ℝ) + y₂) / 2) ≤ _ at hle
  nlinarith [mul_le_mul_of_nonneg_left hWm h.β_pos.le]

/-- The policy function `g(m, z)`: the unique maximizer in (1). -/
noncomputable def cashPolicy (μ : Measure (Icc zl zh)) (U : ℝ → ℝ → ℝ) (β y : ℝ)
    (v : Ici (0 : ℝ) × Icc zl zh → ℝ) (s : Ici (0 : ℝ) × Icc zl zh) : Ici (0 : ℝ) :=
  argmaxFn (cashΓ y) (objG (cashModel μ U β y) v) s

/-- The policy is feasible and optimal: `y ≤ g(m, z) ≤ m + y`,
`v(m, z) = U(m + y − g, z) + βW(g)`, and every feasible `x` does no better. -/
theorem cashPolicy_spec (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v)
    (s : Ici (0 : ℝ) × Icc zl zh) :
    y ≤ (cashPolicy μ U β y v s : ℝ) ∧ (cashPolicy μ U β y v s : ℝ) ≤ (s.1 : ℝ) + y ∧
      v s = U ((s.1 : ℝ) + y - cashPolicy μ U β y v s) (s.2 : ℝ) +
        β * cashW μ v (cashPolicy μ U β y v s) ∧
      ∀ x : ℝ, y ≤ x → x ≤ (s.1 : ℝ) + y →
        U ((s.1 : ℝ) + y - x) (s.2 : ℝ) + β * cashW μ v x ≤ v s := by
  have hUA := cash_uniqueArgmax μ h hv
  have hb := cash_boundedDP h μ
  have hmem := hUA.argmaxFn_mem s
  have hval : maxValue (objG (cashModel μ U β y) v) (cashΓ y) s = v s := by
    rw [← bellman_apply _ hb, hv]
  refine ⟨hmem.1.1, hmem.1.2, ?_, fun x hx1 hx2 => ?_⟩
  · have := hmem.2
    rw [hval, cash_objG] at this
    exact this.symm
  · have hxm : (⟨x, mem_Ici.2 (h.y_pos.le.trans hx1)⟩ : Ici (0 : ℝ)) ∈ cashΓ y s := ⟨hx1, hx2⟩
    have := le_maxValue (continuousOn_objG _ hb v) (hb.compact s) hxm
    rw [hval, cash_objG] at this
    exact this

/-- A feasible `x` doing at least as well as the optimum is the policy. -/
theorem cashPolicy_eq_of_ge (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v)
    (s : Ici (0 : ℝ) × Icc zl zh) {x : ℝ} (hx1 : y ≤ x) (hx2 : x ≤ (s.1 : ℝ) + y)
    (hge : v s ≤ U ((s.1 : ℝ) + y - x) (s.2 : ℝ) + β * cashW μ v x) :
    (cashPolicy μ U β y v s : ℝ) = x := by
  have hUA := cash_uniqueArgmax μ h hv
  have hb := cash_boundedDP h μ
  have hval : maxValue (objG (cashModel μ U β y) v) (cashΓ y) s = v s := by
    rw [← bellman_apply _ hb, hv]
  set xm : Ici (0 : ℝ) := ⟨x, mem_Ici.2 (h.y_pos.le.trans hx1)⟩
  have hxm : xm ∈ cashΓ y s := ⟨hx1, hx2⟩
  have hle := (cashPolicy_spec μ h hv s).2.2.2 x hx1 hx2
  have hx : xm ∈ argmax (objG (cashModel μ U β y) v) (cashΓ y) s := by
    refine ⟨hxm, ?_⟩
    rw [hval, cash_objG]
    exact le_antisymm hle hge
  have := hUA.unique s _ hx _ (hUA.argmaxFn_mem s)
  change ((argmaxFn (cashΓ y) (objG (cashModel μ U β y) v) s : Ici (0 : ℝ)) : ℝ) = x
  rw [← this]

/-- **Exercise 13.5(c).** End-of-period real balances are a continuous function `g(m, z)`: the
policy correspondence is `{g(m, z)}`, and `g` is continuous (Theorem of the Maximum). -/
theorem ex_13_5c (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) :
    (∀ s, policy (cashModel μ U β y) v s = {cashPolicy μ U β y v s}) ∧
      Continuous (cashPolicy μ U β y v) := by
  have hUA := cash_uniqueArgmax μ h hv
  refine ⟨fun s => ?_, hUA.continuous_argmaxFn⟩
  rw [policy_eq_argmax _ (cash_boundedDP h μ) hv]
  exact hUA.argmax_eq s

/-- `m ↦ g(m, z)` as a function of real `m` (clamped at `0`) is continuous. -/
theorem continuous_cashPolicy_real (h : CurrencyHyp U β y zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh) :
    Continuous fun m : ℝ =>
      (cashPolicy μ U β y v (⟨max m 0, mem_Ici.2 (le_max_right _ _)⟩, z) : ℝ) :=
  continuous_subtype_val.comp ((ex_13_5c μ h hv).2.comp
    ((continuous_id.max continuous_const).subtype_mk _ |>.prodMk continuous_const))

/-! ### Exercise 13.5(h): the policy is nonincreasing in the shock -/

/-- **Increasing differences**, the difference form of "`U₁(c, ·)` is strictly increasing": for
`0 ≤ c < c′` and `z̲ ≤ z < z′ ≤ z̄`, `U(c′, z) − U(c, z) < U(c′, z′) − U(c, z′)`. -/
def CurrencyIncreasingDiff (U : ℝ → ℝ → ℝ) (zl zh : ℝ) : Prop :=
  ∀ c c' : ℝ, 0 ≤ c → c < c' → ∀ z z' : ℝ, zl ≤ z → z < z' → z' ≤ zh →
    U c' z - U c z < U c' z' - U c z'

/-- The book's hypothesis gives increasing differences: if `U(·, z)` has derivative `U₁(c, z)`
on `ℝ₊` and `U₁(c, ·)` is strictly increasing on `Z`, then `t ↦ U(t, z′) − U(t, z)` has positive
derivative, so it is strictly increasing. -/
theorem currencyIncreasingDiff_of_deriv {U1 : ℝ → ℝ → ℝ}
    (hd : ∀ z ∈ Icc zl zh, ∀ c, 0 ≤ c → HasDerivAt (fun c => U c z) (U1 c z) c)
    (hm : ∀ c, 0 ≤ c → StrictMonoOn (U1 c) (Icc zl zh)) : CurrencyIncreasingDiff U zl zh := by
  intro c c' hc hcc' z z' hz hzz' hz'
  set φ := fun t => U t z' - U t z
  have hφd : ∀ t, 0 ≤ t → HasDerivAt φ (U1 t z' - U1 t z) t := fun t ht =>
    (hd z' ⟨by linarith, hz'⟩ t ht).sub (hd z ⟨hz, by linarith⟩ t ht)
  have hcont : ContinuousOn φ (Icc c c') := fun t ht =>
    (hφd t (hc.trans ht.1)).continuousAt.continuousWithinAt
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc c c') hcont fun t ht => by
    rw [interior_Icc] at ht
    rw [(hφd t (hc.trans ht.1.le)).deriv]
    exact sub_pos.2 (hm t (hc.trans ht.1.le) ⟨hz, by linarith⟩ ⟨by linarith, hz'⟩ hzz')
  have := hmono ⟨le_rfl, hcc'.le⟩ ⟨hcc'.le, le_rfl⟩ hcc'
  simp only [φ] at this
  linarith

/-- **Exercise 13.5(h).** For each `m`, `g(m, ·)` is nonincreasing in `z`: with `g(m, z₁) <
g(m, z₂)` for `z₁ < z₂`, adding the two optimality inequalities (the continuation value is the
same, the shocks being i.i.d.) contradicts increasing differences. -/
theorem ex_13_5h (h : CurrencyHyp U β y zl zh) (hID : CurrencyIncreasingDiff U zl zh)
    {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (m : Ici (0 : ℝ)) :
    Antitone fun z => (cashPolicy μ U β y v (m, z) : ℝ) := by
  intro z₁ z₂ hz
  by_contra hlt
  push Not at hlt
  obtain ⟨a1, a2, e1, o1⟩ := cashPolicy_spec μ h hv (m, z₁)
  obtain ⟨b1, b2, e2, o2⟩ := cashPolicy_spec μ h hv (m, z₂)
  dsimp only at a2 b2 e1 e2 o1 o2
  set g₁ := (cashPolicy μ U β y v (m, z₁) : ℝ)
  set g₂ := (cashPolicy μ U β y v (m, z₂) : ℝ)
  have i1 := o1 g₂ b1 b2
  have i2 := o2 g₁ a1 a2
  rcases (show (z₁ : ℝ) ≤ z₂ from hz).eq_or_lt with heq | hzlt
  · have : z₁ = z₂ := Subtype.ext heq
    subst this
    exact lt_irrefl _ hlt
  · have := hID ((m : ℝ) + y - g₂) ((m : ℝ) + y - g₁) (sub_nonneg.2 b2) (by linarith) z₁ z₂
      z₁.2.1 hzlt z₂.2.2
    linarith

/-! ### Exercise 13.5(e): monotonicity of `g` and `c` in `m` -/

/-- `g(·, z)` is nondecreasing (part (e), first half): with `m₁ < m₂` and `g(m₂) < g(m₁)`,
each choice is feasible at the other balance, and adding the two optimality inequalities
contradicts the strict concavity of `U(·, z)` (`strictConcave_exchange`). -/
theorem cashPolicy_mono (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh)
    {m₁ m₂ : Ici (0 : ℝ)} (hm : m₁ ≤ m₂) :
    (cashPolicy μ U β y v (m₁, z) : ℝ) ≤ cashPolicy μ U β y v (m₂, z) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a1, a2, e1, o1⟩ := cashPolicy_spec μ h hv (m₁, z)
  obtain ⟨b1, b2, e2, o2⟩ := cashPolicy_spec μ h hv (m₂, z)
  dsimp only at a2 b2 e1 e2 o1 o2
  set g₁ := (cashPolicy μ U β y v (m₁, z) : ℝ)
  set g₂ := (cashPolicy μ U β y v (m₂, z) : ℝ)
  have hm' : (m₁ : ℝ) ≤ m₂ := hm
  have i1 := o1 g₂ b1 (by linarith)
  have i2 := o2 g₁ a1 (by linarith)
  rcases hm'.eq_or_lt with heq | hlt'
  · have : m₁ = m₂ := Subtype.ext heq
    subst this
    exact lt_irrefl _ hlt
  · have hx := strictConcave_exchange (h.U_conc z.1 z.2) (p := (m₁ : ℝ) + y - g₁)
      (q := (m₁ : ℝ) + y - g₂) (r := (m₂ : ℝ) + y - g₁) (t := (m₂ : ℝ) + y - g₂)
      (mem_Ici.2 (sub_nonneg.2 a2)) (mem_Ici.2 (sub_nonneg.2 b2)) (by linarith) (by linarith)
      (by ring)
    linarith

/-- Consumption `c(·, z) = m + y − g(·, z)` is nondecreasing (part (e), weak form):
`g(m₂, z) − g(m₁, z) ≤ m₂ − m₁` for `m₁ ≤ m₂`. Otherwise `c(m₂) < c(m₁)`; moving both
consumptions to their midpoint (`g(m₁) + t` at `m₁` and `g(m₂) − t` at `m₂`,
`t = (c(m₁) − c(m₂))/2`) is feasible, gains strictly in `U` and does not lose in `W` (concavity),
so one of the two choices was not optimal. -/
theorem cashCons_mono (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) (z : Icc zl zh)
    {m₁ m₂ : Ici (0 : ℝ)} (hm : m₁ ≤ m₂) :
    (cashPolicy μ U β y v (m₂, z) : ℝ) - cashPolicy μ U β y v (m₁, z) ≤ (m₂ : ℝ) - m₁ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a1, a2, e1, o1⟩ := cashPolicy_spec μ h hv (m₁, z)
  obtain ⟨b1, b2, e2, o2⟩ := cashPolicy_spec μ h hv (m₂, z)
  dsimp only at a2 b2 e1 e2 o1 o2
  set g₁ := (cashPolicy μ U β y v (m₁, z) : ℝ)
  set g₂ := (cashPolicy μ U β y v (m₂, z) : ℝ)
  have hm' : (m₁ : ℝ) ≤ m₂ := hm
  have hc₂ : 0 ≤ (m₂ : ℝ) + y - g₂ := sub_nonneg.2 b2
  have hc : (m₂ : ℝ) + y - g₂ < (m₁ : ℝ) + y - g₁ := by linarith
  obtain ⟨t, ht_def⟩ : ∃ t, t = (((m₁ : ℝ) + y - g₁) - ((m₂ : ℝ) + y - g₂)) / 2 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; linarith
  have ht1 : g₁ + t ≤ (m₁ : ℝ) + y := by rw [ht_def]; linarith
  have ht2 : g₁ + t ≤ g₂ - t := by rw [ht_def]; linarith
  have i1 := o1 (g₁ + t) (by linarith) ht1
  have i2 := o2 (g₂ - t) (by linarith) (by linarith)
  have q1 : (m₁ : ℝ) + y - (g₁ + t) =
      1 / 2 * ((m₁ : ℝ) + y - g₁) + 1 / 2 * ((m₂ : ℝ) + y - g₂) := by rw [ht_def]; ring
  have q2 : (m₂ : ℝ) + y - (g₂ - t) =
      1 / 2 * ((m₁ : ℝ) + y - g₁) + 1 / 2 * ((m₂ : ℝ) + y - g₂) := by rw [ht_def]; ring
  rw [q1] at i1
  rw [q2] at i2
  have hW := currency_concave_exchange (cashW_strictConcave μ h hv).concaveOn (p := g₁)
    (q := g₁ + t)
    (r := g₂ - t) (t := g₂) (mem_Ici.2 (by linarith [h.y_pos]))
    (mem_Ici.2 (by linarith [h.y_pos])) (by linarith) (by linarith) (by ring)
  have hU := (h.U_conc z.1 z.2).2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ (m₁ : ℝ) + y - g₁))
    (mem_Ici.2 hc₂) hc.ne' (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at hU
  nlinarith [mul_le_mul_of_nonneg_left hW h.β_pos.le]

/-! ### Exercise 13.5(f): the top of the ergodic set -/

/-- The point `⟨max m 0, _⟩` of `ℝ₊` is `m` when `m ≥ 0`. -/
theorem currency_Ici_max_eq (m : Ici (0 : ℝ)) :
    (⟨max (m : ℝ) 0, mem_Ici.2 (le_max_right _ _)⟩ : Ici (0 : ℝ)) = m :=
  Subtype.ext (max_eq_left m.2)

/-- **Exercise 13.5(f).** There is `m̄ ≥ y > 0` with `g(m̄, z̲) = m̄`; we take the smallest such
point in `[y, ∞)`, so that `g(m, z̲) > m` on `[y, m̄)`.

Proof (derivative-free). If `g(m, z̲) > m` for all `m ≥ 2y`, then consuming `y` more at `(m, z̲)`
is feasible, and optimality with the concavity of `U` and `W` gives
`β[W(m) − W(m − y)] ≥ U(2y, z̲) − U(y, z̲) > 0` for all `m ≥ 2y`; summing over `m = 2y, 3y, …`
makes the bounded `W` unbounded. So `g(m₁, z̲) ≤ m₁` for some `m₁ ≥ 2y`, while `g(y, z̲) ≥ y`,
and the intermediate value theorem gives a fixed point; the fixed points in `[y, m₁]` form a
compact set, whose least element is `m̄`. Below `m̄`, `g(m, z̲) − m ≥ g(m̄, z̲) − m̄ = 0` by
part (e) and `≠ 0` by minimality. -/
theorem ex_13_5f (h : CurrencyHyp U β y zl zh) {v : Ici (0 : ℝ) × Icc zl zh →ᵇ ℝ}
    (hv : bellman (cashModel μ U β y) (cash_boundedDP h μ) v = v) :
    ∃ mb : ℝ, ∃ hmb : y ≤ mb, (cashPolicy μ U β y v
        (⟨mb, mem_Ici.2 (h.y_pos.le.trans hmb)⟩, ⟨zl, le_rfl, h.hz⟩) : ℝ) = mb ∧
      ∀ m : Ici (0 : ℝ), y ≤ (m : ℝ) → (m : ℝ) < mb →
        (m : ℝ) < cashPolicy μ U β y v (m, ⟨zl, le_rfl, h.hz⟩) := by
  set zL : Icc zl zh := ⟨zl, le_rfl, h.hz⟩
  have hy := h.y_pos
  have hβ := h.β_pos
  set G : ℝ → ℝ := fun m =>
    (cashPolicy μ U β y v (⟨max m 0, mem_Ici.2 (le_max_right _ _)⟩, zL) : ℝ)
  have hG : Continuous G := continuous_cashPolicy_real μ h hv zL
  have hGm : ∀ m : Ici (0 : ℝ), G m = cashPolicy μ U β y v (m, zL) := fun m => by
    simp only [G, currency_Ici_max_eq]
  have hW := (cashW_strictConcave μ h hv).concaveOn
  have hUc := (h.U_conc zl ⟨le_rfl, h.hz⟩).concaveOn
  -- Step 1: some `m₁ ≥ 2y` has `g(m₁, z̲) ≤ m₁`
  have hstep1 : ∃ m₁ : ℝ, 2 * y ≤ m₁ ∧ G m₁ ≤ m₁ := by
    by_contra hne
    push Not at hne
    set κ := U (y + y) zl - U y zl
    have hκ : 0 < κ := sub_pos.2 (h.U_mono zl ⟨le_rfl, h.hz⟩ (mem_Ici.2 hy.le)
      (mem_Ici.2 (by linarith)) (by linarith))
    have hA : ∀ m : ℝ, 2 * y ≤ m → κ ≤ β * (cashW μ v m - cashW μ v (m - y)) := by
      intro m hm
      have hm0 : 0 ≤ m := by linarith
      set mm : Ici (0 : ℝ) := ⟨m, mem_Ici.2 hm0⟩
      have hgm := hne m hm
      rw [show G m = (cashPolicy μ U β y v (mm, zL) : ℝ) from hGm mm] at hgm
      obtain ⟨a1, a2, e1, o1⟩ := cashPolicy_spec μ h hv (mm, zL)
      dsimp only at a2 e1 o1
      set g := (cashPolicy μ U β y v (mm, zL) : ℝ)
      have hmm : (mm : ℝ) = m := rfl
      rw [hmm] at a2 e1 o1
      have i1 := o1 (g - y) (by linarith) (by linarith)
      have q : m + y - (g - y) = (m + y - g) + y := by ring
      rw [q] at i1
      have hzz : ((zL : Icc zl zh) : ℝ) = zl := rfl
      rw [hzz] at i1 e1
      have hc0 : 0 ≤ m + y - g := by linarith
      have hU := currency_concave_increment_le hUc hc0 (by linarith : m + y - g ≤ y) hy.le
      have hWi := currency_concave_increment_le hW (by linarith : (0 : ℝ) ≤ m - y)
        (by linarith : m - y ≤ g - y) hy.le
      have e3 : g - y + y = g := by ring
      have e4 : m - y + y = m := by ring
      rw [e3] at hWi
      rw [e4] at hWi
      nlinarith [mul_le_mul_of_nonneg_left hWi hβ.le]
    have hB : ∀ n : ℕ, ((n : ℝ) + 1) * κ ≤ β * (cashW μ v (((n : ℝ) + 2) * y) - cashW μ v y) := by
      intro n
      induction n with
      | zero =>
        have := hA (2 * y) le_rfl
        rw [show 2 * y - y = y by ring] at this
        simpa using this
      | succ n ih =>
        have := hA (((n : ℝ) + 3) * y) (by nlinarith)
        rw [show ((n : ℝ) + 3) * y - y = ((n : ℝ) + 2) * y by ring] at this
        push_cast
        rw [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
        nlinarith
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * β * ‖v‖ / κ)
    have hb := hB n
    have h1 := abs_le.1 (abs_cashW_le μ v (((n : ℝ) + 2) * y))
    have h2 := abs_le.1 (abs_cashW_le μ v y)
    have : 2 * β * ‖v‖ < ((n : ℝ) + 1) * κ := by
      rw [div_lt_iff₀ hκ] at hn
      nlinarith
    nlinarith
  obtain ⟨m₁, hm₁, hGm₁⟩ := hstep1
  -- Step 2: the fixed points of `g(·, z̲)` in `[y, m₁]`
  have hym₁ : y ≤ m₁ := by linarith
  set F : ℝ → ℝ := fun m => G m - m
  have hF : Continuous F := hG.sub continuous_id
  have hFy : 0 ≤ F y := by
    have := (cashPolicy_spec μ h hv (⟨max y 0, mem_Ici.2 (le_max_right _ _)⟩, zL)).1
    simp only [F, G]
    linarith
  have hFm₁ : F m₁ ≤ 0 := by simp only [F]; linarith
  obtain ⟨m₀, hm₀, hFm₀⟩ := intermediate_value_Icc' hym₁ hF.continuousOn ⟨hFm₁, hFy⟩
  set S := Icc y m₁ ∩ {m | F m = 0}
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_eq hF continuous_const)
  have hSne : S.Nonempty := ⟨m₀, hm₀, hFm₀⟩
  have hSb : BddBelow S := ⟨y, fun m hm => hm.1.1⟩
  have hmem := hSc.csInf_mem hSne hSb
  set mb := sInf S
  have hmb : y ≤ mb := hmem.1.1
  refine ⟨mb, hmb, ?_, fun m hym hmlt => ?_⟩
  · have := hmem.2
    simp only [F, mem_ofPred_eq] at this
    rw [← hGm ⟨mb, mem_Ici.2 (hy.le.trans hmb)⟩]
    linarith
  · have hFne : F m ≠ 0 := fun h0 => by
      have : mb ≤ m := csInf_le hSb ⟨⟨hym, by linarith [hmem.1.2]⟩, h0⟩
      linarith
    have hcm := cashCons_mono μ h hv zL (m₁ := m) (m₂ := ⟨mb, mem_Ici.2 (hy.le.trans hmb)⟩)
      (show (m : ℝ) ≤ mb from hmlt.le)
    have hfix := hmem.2
    simp only [F, mem_ofPred_eq] at hfix
    rw [← hGm ⟨mb, mem_Ici.2 (hy.le.trans hmb)⟩, ← hGm m] at hcm
    have : F m = G m - m := rfl
    have hne' : G m ≠ m := fun h0 => hFne (by rw [this, h0, sub_self])
    rw [← hGm m]
    change G mb - G m ≤ mb - m at hcm
    exact lt_of_le_of_ne (by linarith) (Ne.symm hne')

end StokeyLucasPrescott.ConvergenceApplications
