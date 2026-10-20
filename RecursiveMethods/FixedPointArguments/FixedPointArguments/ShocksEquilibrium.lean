/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.ShocksProposition8
import FixedPointArguments.ShocksRevelation

/-!
# Partially observed shocks: equilibria of the islands economy and fixed points of (4)

SLP §17.6, pp. 532–535. The equilibrium conditions (1)–(2) are `IslandsEqm`
(`FixedPointArguments.ShocksRevelation`). This module derives (3) from (1), proves the converse
(p. 535: a fixed point of (4) with invertible price function is an equilibrium), and turns the
failure of Proposition 8 (`FixedPointArguments.ShocksProposition8`) into a statement about
equilibria.

* `shocks_concave_tangent`, `shocks_convex_tangent`: tangent-line inequalities for `V` and `H`.
  `islands_factor_continuous`: the consumption factor `c = x′ p(ŝ)/(x̂ p(s′))` of (1).
* **(3) from (1)** (`islands_foc`, p. 534): in an equilibrium with continuous `p`, at every state
  `n H'(n) = E[φ(c n)]`, the expectation under the agent's beliefs and `ν`. The proof bounds the
  difference quotients of the expected utility by `E[c V'(c l)]` (concavity) and uses continuity
  of parametric integrals; no differentiation under the integral sign is needed.
* **Rational expectations.** `islandsShockLaw` (`x ~ ψ`, `θ ~ g` independent),
  `islandsNextLaw` (the true law `ν` of next period's state), `islandsREBeliefs` (at the price of
  the ray `x/θ = z` the state is `(zθ̂, θ̂)` with `θ̂ ~ G(·|z)`, `shocksCondLaw`);
  `islandsREBeliefs_eq`, `islandsShockLaw_ae_mem`, `condLaw_ae_ray`, `integral_islandsNextLaw`,
  `integral_rayBelief`, `isProbabilityMeasure_islandsShockLaw`, `islands_isFiniteMeasure_comap`,
  `isFiniteMeasure_islandsREBeliefs`.
* `islands_RE_phi_eq`: with these beliefs and `p = z/η(z)`, `η = ζ⁻¹ ∘ f`, the right side of the
  first-order condition at `η(z)` is `(Tf)(z)` of (4).
* **The converse (p. 535)** (`islands_eqm_of_fixedPoint`): a strictly positive continuous fixed
  point `f` of (4) with `z ↦ z/ζ⁻¹(f(z))` injective gives an equilibrium `p = ρ(x/θ)`,
  `n = ζ⁻¹(f(x/θ))` with rational-expectations beliefs (optimality by concavity and the
  first-order condition). As the book says, `π > 0` on `int Z` is needed (Exercise 17.8).
* **Equilibrium ⇒ fixed point** (`islands_fixedPoint_of_eqm`): every equilibrium with continuous
  `p` and rational-expectations beliefs comes from a strictly positive continuous fixed point of
  (4) with invertible price function. So, for continuous prices, equilibria and such fixed points
  correspond exactly.
* **Proposition 8 as a statement about equilibria.** `shocksP8_no_continuous_eqm`: the bimodal
  CRRA economy of `proposition_8_counterexample` has no equilibrium with a continuous price
  function. `shocksP8W'_ge`, `shocksP8W_eta_ge` (an a priori lower bound `η ≥ A/3` on fixed points
  for the utility `shocksP8W y₀`), `shocksP8W_no_continuous_eqm` and
  **`proposition_8_eqm_counterexample`**: the same economy with the utility
  `shocksP8W (1/300000)`, which satisfies the book's Assumptions 17.1 and 17.4, satisfies every
  hypothesis of Proposition 8 and has no equilibrium with a continuous price function at all.

**Correction (Proposition 8, p. 540).** Under Assumptions 17.1, 17.4 and 17.5 an islands economy
can fail to have any equilibrium with a continuous price function (with rational-expectations
beliefs); the unique positive solution of (3) has a non-invertible price function and so is not an
equilibrium. The regularity assumed is continuity of the price function, the class in which the
book looks for equilibria; discontinuous prices are not treated.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology BoundedContinuousFunction

variable {xlo xhi θlo θhi L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ}

/-- The tangent line of a concave `V` at `y₀ > 0` lies above `V` on `ℝ₊`. -/
theorem shocks_concave_tangent (hV : Assumption17_1VR V V' V'') {y₀ y : ℝ} (hy₀ : 0 < y₀)
    (hy : 0 ≤ y) : V y ≤ V y₀ + V' y₀ * (y - y₀) := by
  have hc := hV.V_conc.concaveOn
  rcases lt_trichotomy y y₀ with h | h | h
  · have := hc.le_slope_of_hasDerivAt (mem_Ici.2 hy) (mem_Ici.2 hy₀.le) h (hV.V_deriv y₀ hy₀)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    nlinarith
  · subst h; simp
  · have := hc.slope_le_of_hasDerivAt (mem_Ici.2 hy₀.le) (mem_Ici.2 hy) h (hV.V_deriv y₀ hy₀)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    nlinarith

/-- The tangent line of the convex `H` at an interior `m` lies below `H` on `[0, L)`. -/
theorem shocks_convex_tangent (hH : Assumption17_1H L H H' H'') {m l : ℝ} (hm : m ∈ Ioo 0 L)
    (hl : l ∈ Ico 0 L) : H m + H' m * (l - m) ≤ H l := by
  have hc := hH.H_conv.convexOn
  have hm' : m ∈ Ico 0 L := Ioo_subset_Ico_self hm
  rcases lt_trichotomy l m with h | h | h
  · have := hc.slope_le_of_hasDerivAt hl hm' h (hH.H_hasDerivAt hm)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    nlinarith
  · subst h; simp
  · have := hc.le_slope_of_hasDerivAt hm' hl h (hH.H_hasDerivAt hm)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    nlinarith

variable {p n : ℝ × ℝ → ℝ} {κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi)}
  {ν : Measure (ShocksStates xlo xhi θlo θhi)}

/-- The consumption factor `c(ŝ, s′) = x′ p(ŝ)/(x̂ p(s′))` of (1) (consumption is `c l`) is
continuous and positive on `(X × Θ)²` for continuous positive `p`. -/
theorem islands_factor_continuous (hx0 : 0 < xlo)
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    (hppos : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < p s) :
    Continuous (fun q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi =>
        q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1)) ∧
      ∀ q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi,
        0 < q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1) := by
  have hpc : Continuous fun s : ShocksStates xlo xhi θlo θhi => p s.1 :=
    hp.comp_continuous continuous_subtype_val fun s => s.2
  have hxpos : ∀ s : ShocksStates xlo xhi θlo θhi, 0 < s.1.1 := fun s => hx0.trans_le s.2.1.1
  refine ⟨((continuous_subtype_val.fst.comp continuous_snd).mul (hpc.comp continuous_fst)).div
    ((continuous_subtype_val.fst.comp continuous_fst).mul (hpc.comp continuous_snd))
    fun q => (mul_pos (hxpos q.1) (hppos _ q.2.2)).ne', fun q => ?_⟩
  exact div_pos (mul_pos (hxpos q.2) (hppos _ q.1.2)) (mul_pos (hxpos q.1) (hppos _ q.2.2))

/-- **The first-order condition of (1)** (p. 534). In an equilibrium with continuous `p`, at
every state `s` the labour supply `n = n(s) ∈ (0, L)` satisfies
`n H'(n) = E[φ(c n)]`, `φ(y) = y V'(y)`, the expectation over `ŝ ~ κ(p(s))` and `s′ ~ ν`.
No differentiation under the integral sign is needed: concavity of `V` bounds the difference
quotients of the expected utility by `E[c V'(c l)]`, which is continuous in `l > 0`. -/
theorem islands_foc (hx0 : 0 < xlo) (hθ0 : 0 < θlo) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') [IsFiniteMeasure ν] [∀ P, IsFiniteMeasure (κ P)]
    (he : IslandsEqm L H V p n κ ν) (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    {s : ℝ × ℝ} (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) :
    olgZeta H' (n s) =
      ∫ sh, ∫ s', olgPhi V' (s'.1.1 * p sh.1 / (sh.1.1 * p s'.1) * n s) ∂ν ∂κ (p s) := by
  have : CompactSpace (ShocksStates xlo xhi θlo θhi) :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have hppos := fun s hs => he.p_pos hx0 hθ0 (s := s) hs
  obtain ⟨hc, hcpos⟩ := islands_factor_continuous hx0 hp hppos
  set c := fun q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi =>
    q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1) with hcdef
  set m := n s with hmdef
  have hm : m ∈ Ioo 0 L := by
    refine ⟨?_, (he.n_mem s hs).2⟩
    have h2 := he.clear s hs
    have hz : 0 < s.1 / s.2 := div_pos (hx0.trans_le hs.1.1) (hθ0.trans_le hs.2.1)
    by_contra h
    push Not at h
    nlinarith [hppos s hs]
  set μP := (κ (p s)).prod ν
  have hint : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
      Continuous F → Integrable F μP := fun F hF =>
    (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩).integrable μP
  have hprod : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
      Continuous F → ∫ q, F q ∂μP = ∫ sh, ∫ s', F (sh, s') ∂ν ∂κ (p s) := fun F hF =>
    integral_prod F (hint F hF)
  have hVc : ∀ l, 0 ≤ l → Continuous fun q => V (c q * l) := fun l hl =>
    hV.V_cont.comp_continuous (hc.mul continuous_const) fun q =>
      mem_Ici.2 (mul_nonneg (hcpos q).le hl)
  have hV'c : ∀ l, 0 < l → Continuous fun q => c q * V' (c q * l) := fun l hl =>
    hc.mul (hV.V'_continuousOn.comp_continuous (hc.mul continuous_const) fun q =>
      mem_Ioi.2 (mul_pos (hcpos q) hl))
  -- the objective in product form
  have hobj : ∀ l, 0 ≤ l → islandsObj H V p κ ν (p s) l = -H l + ∫ q, V (c q * l) ∂μP :=
    fun l hl => by
      rw [hprod _ (hVc l hl), islandsObj]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun sh => integral_congr_ae (ae_of_all _
        fun s' => ?_))
      simp only [hcdef]
      ring_nf
  set D := fun l => ∫ q, c q * V' (c q * l) ∂μP with hDdef
  -- the difference-quotient bound
  have hkey : ∀ l ∈ Ioo 0 L, (l - m) * D l ≤ H l - H m := fun l hl => by
    have hopt := he.opt s hs l (Ioo_subset_Ico_self hl)
    rw [hobj l hl.1.le, hobj m hm.1.le] at hopt
    have hpt : ∀ q, V (c q * m) ≤ V (c q * l) - (l - m) * (c q * V' (c q * l)) := fun q => by
      have := shocks_concave_tangent hV (mul_pos (hcpos q) hl.1)
        (mul_nonneg (hcpos q).le hm.1.le)
      nlinarith
    have hmono : ∫ q, V (c q * m) ∂μP ≤
        ∫ q, (V (c q * l) - (l - m) * (c q * V' (c q * l))) ∂μP :=
      integral_mono (hint _ (hVc m hm.1.le))
        ((hint _ (hVc l hl.1.le)).sub ((hint _ (hV'c l hl.1)).const_mul (l - m))) hpt
    rw [integral_sub (hint _ (hVc l hl.1.le)) ((hint _ (hV'c l hl.1)).const_mul (l - m)),
      integral_const_mul] at hmono
    simp only [hDdef]
    linarith
  -- continuity of `D` at `m`
  set Dδ := fun l => ∫ q, c q * V' (c q * max l (m / 2)) ∂μP with hDδdef
  have hDδc : Continuous Dδ := by
    have hF : Continuous (Function.uncurry fun (l : ℝ)
        (q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi) =>
          c q * V' (c q * max l (m / 2))) :=
      (hc.comp continuous_snd).mul (hV.V'_continuousOn.comp_continuous
        ((hc.comp continuous_snd).mul (continuous_fst.max continuous_const)) fun x =>
          mem_Ioi.2 (mul_pos (hcpos x.2) (lt_max_of_lt_right (by linarith [hm.1]))))
    have := continuous_parametric_integral_of_continuous (μ := μP) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hDδ : ∀ l, m / 2 ≤ l → Dδ l = D l := fun l hl => by
    simp only [hDδdef, hDdef, max_eq_left hl]
  have hslope := hasDerivAt_iff_tendsto_slope.1 (hH.H_hasDerivAt hm)
  have hup : Dδ m ≤ H' m := by
    refine le_of_tendsto_of_tendsto (hDδc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hslope.mono_left (nhdsWithin_mono _ fun x hx => (mem_Ioi.1 hx).ne')) ?_
    filter_upwards [Ioo_mem_nhdsGT hm.2] with l hl
    rw [hDδ l (by linarith [hl.1, hm.1]), slope_def_field, le_div_iff₀ (sub_pos.2 hl.1)]
    have := hkey l ⟨hm.1.trans hl.1, hl.2⟩
    linarith
  have hlo : H' m ≤ Dδ m := by
    refine le_of_tendsto_of_tendsto
      (hslope.mono_left (nhdsWithin_mono _ fun x hx => (mem_Iio.1 hx).ne))
      (hDδc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsLT (show m / 2 < m by linarith [hm.1])] with l hl
    rw [hDδ l hl.1.le, slope_def_field, div_le_iff_of_neg (sub_neg.2 hl.2)]
    have := hkey l ⟨by linarith [hl.1, hm.1], hl.2.trans hm.2⟩
    linarith
  have hD : D m = H' m := by
    rw [← hDδ m (by linarith [hm.1])]
    exact le_antisymm hup hlo
  -- conclusion
  have hφc : Continuous fun q => olgPhi V' (c q * m) :=
    hV.phi_continuousOn.comp_continuous (hc.mul continuous_const) fun q =>
      mem_Ioi.2 (mul_pos (hcpos q) hm.1)
  rw [← hprod _ hφc]
  have e : ∀ q, olgPhi V' (c q * m) = m * (c q * V' (c q * m)) := fun q => by
    simp only [olgPhi]; ring
  simp_rw [e]
  rw [integral_const_mul]
  change m * H' m = m * D m
  rw [hD]

/-! ### Rational-expectations beliefs and the true law of next period's shocks -/

/-- The law of the shocks `(x, θ)`: `x ~ ψ` and `θ ~ g` independent. -/
noncomputable def islandsShockLaw (ψ g : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (volume.withDensity fun x => ENNReal.ofReal (ψ x)).prod
    (volume.withDensity fun θ => ENNReal.ofReal (g θ))

/-- The true law `ν` of next period's state `(x′, θ′)`, as a measure on `X × Θ`. -/
noncomputable def islandsNextLaw (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) :
    Measure (ShocksStates xlo xhi θlo θhi) :=
  (islandsShockLaw ψ g).comap Subtype.val

open scoped Classical in
/-- **Rational-expectations beliefs** for a price function `p` that depends on the state through
`z = x/θ`: a young agent who sees the price `P = p(z a(z), a(z))` believes the current state is
`(z θ̂, θ̂)` with `θ̂ ~ G(·|z)`, the conditional law of `θ` given `x/θ = z` (`shocksCondLaw`). (At
prices that never occur the belief is the zero measure; it is never used.) -/
noncomputable def islandsREBeliefs (xlo xhi θlo θhi : ℝ) (ψ g : ℝ → ℝ) (p : ℝ × ℝ → ℝ)
    (P : ℝ) : Measure (ShocksStates xlo xhi θlo θhi) :=
  if h : ∃ z ∈ Icc (xlo / θhi) (xhi / θlo), p (z * shocksA xlo θlo z, shocksA xlo θlo z) = P then
    (Measure.map (fun θ => (h.choose * θ, θ))
      (shocksCondLaw xlo xhi θlo θhi ψ g h.choose)).comap Subtype.val
  else 0

variable {ψ g : ℝ → ℝ}

/-- When `z ↦ p(z a(z), a(z))` is injective on `Z`, the belief at the price of the ray `z` is
the conditional law along that ray. -/
theorem islandsREBeliefs_eq {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo))
    (hinj : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = p (z * shocksA xlo θlo z, shocksA xlo θlo z) →
      w = z) :
    islandsREBeliefs xlo xhi θlo θhi ψ g p (p (z * shocksA xlo θlo z, shocksA xlo θlo z)) =
      (Measure.map (fun θ => (z * θ, θ))
        (shocksCondLaw xlo xhi θlo θhi ψ g z)).comap Subtype.val := by
  have h : ∃ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = p (z * shocksA xlo θlo z, shocksA xlo θlo z) :=
    ⟨z, hz, rfl⟩
  have hc : h.choose = z := hinj _ h.choose_spec.1 h.choose_spec.2
  simp only [islandsREBeliefs, h, ↓reduceDIte, hc]

variable (hA : ShocksAssumption17_5 xlo xhi θlo θhi ψ g)
include hA

/-- The shocks lie in `X × Θ` almost surely. -/
theorem islandsShockLaw_ae_mem : ∀ᵐ q ∂islandsShockLaw ψ g, q ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
  have hx : ∀ᵐ x ∂(volume.withDensity fun x => ENNReal.ofReal (ψ x)), x ∈ Icc xlo xhi := by
    refine (ae_withDensity_iff (f := fun x => ENNReal.ofReal (ψ x))
      (ENNReal.measurable_ofReal.comp hA.ψ_meas)).2 (ae_of_all _ fun x hx => ?_)
    by_contra h
    exact hx (by rw [hA.ψ_zero x h, ENNReal.ofReal_zero])
  have hθ : ∀ᵐ θ ∂(volume.withDensity fun θ => ENNReal.ofReal (g θ)), θ ∈ Icc θlo θhi := by
    refine (ae_withDensity_iff (f := fun θ => ENNReal.ofReal (g θ))
      (ENNReal.measurable_ofReal.comp hA.g_meas)).2 (ae_of_all _ fun θ hθ => ?_)
    by_contra h
    exact hθ (by rw [hA.g_zero θ h, ENNReal.ofReal_zero])
  exact ((Measure.quasiMeasurePreserving_fst.ae hx).and
    (Measure.quasiMeasurePreserving_snd.ae hθ)).mono fun q hq => ⟨hq.1, hq.2⟩

/-- Integrals against the true law of next period's state. -/
theorem integral_islandsNextLaw (k : ℝ × ℝ → ℝ) :
    ∫ s' : ShocksStates xlo xhi θlo θhi, k s'.1 ∂islandsNextLaw xlo xhi θlo θhi ψ g =
      ∫ q, k q ∂islandsShockLaw ψ g := by
  rw [islandsNextLaw, integral_subtype_comap (measurableSet_Icc.prod measurableSet_Icc),
    Measure.restrict_eq_self_of_ae_mem (islandsShockLaw_ae_mem hA)]

/-- `G(·|z)` lives on the ray: `(zθ, θ) ∈ X × Θ` for `G(·|z)`-a.e. `θ`, `z ∈ Z`. -/
theorem condLaw_ae_ray (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z) {z : ℝ}
    (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) :
    ∀ᵐ θ ∂shocksCondLaw xlo xhi θlo θhi ψ g z, (z * θ, θ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
  have hθhi : 0 < θhi := hA.θlo_pos.trans hA.θlo_lt
  have hz0 : 0 < z := (div_pos hA.xlo_pos hθhi).trans_le hz.1
  have hmeas : MeasurableSet {θ : ℝ | (z * θ, θ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi} :=
    (measurableSet_Icc.prod measurableSet_Icc).preimage
      ((measurable_const.mul measurable_id).prodMk measurable_id)
  by_cases hint : xlo / θhi < z ∧ z < xhi / θlo
  · simp only [shocksCondLaw, hint, and_self, ↓reduceIte]
    rw [ae_withDensity_iff (hA.measurable_condDens z).ennreal_ofReal]
    refine ae_of_all _ fun θ hθ => ?_
    have hmem : θ ∈ Icc (shocksA xlo θlo z) (shocksB xhi θhi z) := by
      by_contra h
      exact hθ (by rw [(hA.ex_17_8a (hπ z hint)).2.2.1 θ h, ENNReal.ofReal_zero])
    have := (mem_Icc_shocksA_shocksB_iff hz0).2 hmem
    exact ⟨this.2, this.1⟩
  · simp only [shocksCondLaw, hint, ↓reduceIte]
    split_ifs with h1
    · rw [ae_dirac_iff hmeas]
      have : z = xlo / θhi := le_antisymm h1 hz.1
      have e : z * θhi = xlo := by rw [this, div_mul_cancel₀ _ hθhi.ne']
      exact ⟨⟨e.symm.le, e.le.trans hA.xlo_lt.le⟩, hA.θlo_lt.le, le_rfl⟩
    · rw [ae_dirac_iff hmeas]
      have hz2 : z = xhi / θlo := by
        by_contra h2
        exact hint ⟨lt_of_not_ge h1, lt_of_le_of_ne hz.2 h2⟩
      have e : z * θlo = xhi := by rw [hz2, div_mul_cancel₀ _ hA.θlo_pos.ne']
      exact ⟨⟨hA.xlo_lt.le.trans e.symm.le, e.le⟩, le_rfl, hA.θlo_lt.le⟩

/-- Integrals against the rational-expectations belief along the ray `z`. -/
theorem integral_rayBelief (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) (k : ℝ × ℝ → ℝ) :
    ∫ sh : ShocksStates xlo xhi θlo θhi, k sh.1 ∂(Measure.map (fun θ => (z * θ, θ))
      (shocksCondLaw xlo xhi θlo θhi ψ g z)).comap Subtype.val =
      ∫ θ, k (z * θ, θ) ∂shocksCondLaw xlo xhi θlo θhi ψ g z := by
  have hS : MeasurableSet (Icc xlo xhi ×ˢ Icc θlo θhi) := measurableSet_Icc.prod measurableSet_Icc
  have hm : Measurable fun θ : ℝ => (z * θ, θ) := (measurable_const.mul measurable_id).prodMk
    measurable_id
  have hemb : MeasurableEmbedding fun θ : ℝ => (z * θ, θ) := by
    refine MeasurableEmbedding.of_measurable_inverse hm ?_ measurable_snd fun θ => rfl
    have : range (fun θ : ℝ => (z * θ, θ)) = {q : ℝ × ℝ | q.1 = z * q.2} := by
      ext q
      constructor
      · rintro ⟨θ, rfl⟩; rfl
      · intro h; exact ⟨q.2, Prod.ext h.symm rfl⟩
    rw [this]
    exact measurableSet_eq_fun measurable_fst (measurable_const.mul measurable_snd)
  have hae : ∀ᵐ q ∂(Measure.map (fun θ => (z * θ, θ)) (shocksCondLaw xlo xhi θlo θhi ψ g z)),
      q ∈ Icc xlo xhi ×ˢ Icc θlo θhi :=
    (ae_map_iff hm.aemeasurable hS).2 (condLaw_ae_ray hA hπ hz)
  rw [integral_subtype_comap hS, Measure.restrict_eq_self_of_ae_mem hae, hemb.integral_map]

/-- **The bridge to (4).** Let `p(x, θ) = z/η(z)`, `z = x/θ`, with `η = ζ⁻¹ ∘ f` for a continuous
positive `f` on `Z`. Under the true law `ν` of next period's state and the rational-expectations
belief along the ray `z`, the right side of the first-order condition at labour `η(z)` is
`(Tf)(z)` of (4): `E[φ(c η(z))] = ∫∫ φ((θ′/θ̂) η(z′)) dμ(θ′, z′) G(dθ̂|z)`, since
`c η(z) = (θ′/θ̂) η(z′)` on the ray. -/
theorem islands_RE_phi_eq (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (hZ : xlo / θhi ≤ xhi / θlo) (f : Icc (xlo / θhi) (xhi / θlo) → ℝ) (hfc : Continuous f)
    (hfpos : ∀ z, 0 < f z)
    (hp : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))))
    (z : Icc (xlo / θhi) (xhi / θlo)) :
    ∫ sh, ∫ s', olgPhi V' (s'.1.1 * p sh.1 / (sh.1.1 * p s'.1) * olgZetaInv L H' (f z))
      ∂islandsNextLaw xlo xhi θlo θhi ψ g
      ∂((Measure.map (fun θ => (z.1 * θ, θ)) (shocksCondLaw xlo xhi θlo θhi ψ g z.1)).comap
        Subtype.val : Measure (ShocksStates xlo xhi θlo θhi)) =
      shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z := by
  have hθ0 := hA.θlo_pos
  have hθ := hA.θlo_lt.le
  have hx0 := hA.xlo_pos
  have hη : ∀ w, 0 < olgZetaInv L H' (f w) := fun w => hH.zetaInv_pos (hfpos w)
  have h1 := integral_rayBelief hA hπ z.2 (fun qh => ∫ s', olgPhi V'
    (s'.1.1 * p qh / (qh.1 * p s'.1) * olgZetaInv L H' (f z)) ∂islandsNextLaw xlo xhi θlo θhi ψ g)
  simp only at h1
  rw [h1, shocksOpT]
  refine integral_congr_ae ((condLaw_ae_ray hA hπ z.2).mono fun θ hθS => ?_)
  have hθpos : 0 < θ := hθ0.trans_le hθS.2.1
  have h2 := integral_islandsNextLaw hA (fun q => olgPhi V'
    (q.1 * p (z.1 * θ, θ) / ((z.1 * θ, θ).1 * p q) * olgZetaInv L H' (f z)))
  simp only at h2
  beta_reduce
  rw [h2, shocksPhiF, shocksJointLaw]
  have hmap : Measurable fun q : ℝ × ℝ => (q.2, projIcc (xlo / θhi) (xhi / θlo) hZ (q.1 / q.2)) :=
    measurable_snd.prodMk (continuous_projIcc.measurable.comp (measurable_fst.div measurable_snd))
  have hcont : Continuous fun ω : ℝ × Icc (xlo / θhi) (xhi / θlo) =>
      shocksIntegrand L H' V' θlo θhi f θ ω := by
    have e1 : Continuous fun ω : ℝ × Icc (xlo / θhi) (xhi / θlo) => shocksRatio θlo θhi ω.1 θ :=
      (continuous_shocksRatio hθ0).comp (continuous_fst.prodMk continuous_const)
    have e2 : Continuous fun ω : ℝ × Icc (xlo / θhi) (xhi / θlo) => olgZetaInv L H' (f ω.2) :=
      hH.zetaInv_continuousOn.comp_continuous (hfc.comp continuous_snd) fun ω =>
        mem_Ici.2 (hfpos _).le
    refine hV.phi_continuousOn.comp_continuous (e1.mul e2) fun ω => ?_
    exact mul_pos ((div_pos hθ0 (hθ0.trans_le hθ)).trans_le
      (shocksRatio_mem hθ0 hθ ω.1 θ).1) (hη _)
  rw [integral_map hmap.aemeasurable hcont.aestronglyMeasurable]
  refine integral_congr_ae ((islandsShockLaw_ae_mem hA).mono fun q hq => ?_)
  have hq2 : 0 < q.2 := hθ0.trans_le hq.2.1
  have hq1 : 0 < q.1 := hx0.trans_le hq.1.1
  have hz0 : 0 < z.1 := (div_pos hx0 (hθ0.trans_le hθ)).trans_le z.2.1
  simp only [shocksIntegrand, shocksRatio, shocksClamp_of_mem hq.2, shocksClamp_of_mem hθS.2]
  congr 1
  rw [hp _ hθS, hp q hq]
  simp only
  rw [mul_div_cancel_right₀ _ hθpos.ne', projIcc_val]
  have := hη z
  have := hη (projIcc (xlo / θhi) (xhi / θlo) hZ (q.1 / q.2))
  field_simp

/-- The law of the shocks is a probability measure. -/
theorem isProbabilityMeasure_islandsShockLaw : IsProbabilityMeasure (islandsShockLaw ψ g) := by
  have h1 := shocks_isProbabilityMeasure_withDensity hA.ψ_nonneg
    (shocks_integrable_of_zero_off hA.ψ_cont hA.ψ_zero) hA.ψ_int
  have h2 := shocks_isProbabilityMeasure_withDensity hA.g_nonneg
    (shocks_integrable_of_zero_off hA.g_cont hA.g_zero) hA.g_int
  rw [islandsShockLaw]
  infer_instance

omit hA in
/-- The restriction of a finite measure on `ℝ × ℝ` to `X × Θ` is finite. -/
theorem islands_isFiniteMeasure_comap (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.comap Subtype.val : Measure (ShocksStates xlo xhi θlo θhi)) := by
  constructor
  rw [Measure.comap_apply _ Subtype.val_injective
    (fun _ hs => (measurableSet_Icc.prod measurableSet_Icc).subtype_image hs) _
    MeasurableSet.univ]
  exact measure_lt_top _ _

/-- **The converse (p. 535).** Let `f` be a strictly positive continuous fixed point of (4)
(with `μ` the joint law and `G(·|z)` the conditional law) whose price function
`ρ(z) = z/ζ⁻¹(f(z))` is injective on `Z`. Then `p(x, θ) = ρ(x/θ)` and `n(x, θ) = ζ⁻¹(f(x/θ))`
form an equilibrium (`IslandsEqm`) of the islands economy with rational-expectations beliefs and
the true law of next period's shocks. Optimality in (1) follows from the fixed-point equation
(which is the first-order condition, `islands_RE_phi_eq`) and concavity of the objective. -/
theorem islands_eqm_of_fixedPoint (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (hZ : xlo / θhi ≤ xhi / θlo) (f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
      (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z)
    (hinj : InjOn (fun z => z / olgZetaInv L H' (f (projIcc _ _ hZ z)))
      (Icc (xlo / θhi) (xhi / θlo)))
    (hp : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))))
    (hn : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      n s = olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2)))) :
    IslandsEqm L H V p n (islandsREBeliefs xlo xhi θlo θhi ψ g p)
      (islandsNextLaw xlo xhi θlo θhi ψ g) := by
  have : CompactSpace (ShocksStates xlo xhi θlo θhi) :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have hθ0 := hA.θlo_pos
  have hx0 := hA.xlo_pos
  have hθθ := hA.θlo_lt.le
  have hxx := hA.xlo_lt.le
  set η := fun z : ℝ => olgZetaInv L H' (f (projIcc _ _ hZ z)) with hηdef
  have hηmem : ∀ z, η z ∈ Ioo 0 L := fun z =>
    ⟨hH.zetaInv_pos (hfpos _), (hH.zetaInv_mem (hfpos _).le).2⟩
  have hηc : Continuous η := hH.zetaInv_continuousOn.comp_continuous
    (f.continuous.comp continuous_projIcc) fun z => mem_Ici.2 (hfpos _).le
  have hpos2 : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < s.2 := fun s hs => hθ0.trans_le hs.2.1
  have hppos : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < p s := fun s hs => by
    rw [hp s hs]
    exact div_pos (div_pos (hx0.trans_le hs.1.1) (hpos2 s hs)) (hηmem _).1
  have hpc : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi) := by
    have hr : ContinuousOn (fun s : ℝ × ℝ => s.1 / s.2) (Icc xlo xhi ×ˢ Icc θlo θhi) :=
      continuous_fst.continuousOn.div continuous_snd.continuousOn fun s hs => (hpos2 s hs).ne'
    refine (hr.div (hηc.comp_continuousOn hr) fun s _ => (hηmem _).1.ne').congr fun s hs => ?_
    exact hp s hs
  have := isProbabilityMeasure_islandsShockLaw hA
  have hν : IsFiniteMeasure (islandsNextLaw xlo xhi θlo θhi ψ g) :=
    islands_isFiniteMeasure_comap _
  -- the price of a ray
  have hray : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = w / η w := fun w hw => by
    have hA0 : shocksA xlo θlo w ≠ 0 := (hθ0.trans_le (le_max_right _ _)).ne'
    rw [hp _ (shocks_rayPoint_mem hx0 hxx hθ0 hθθ hw)]
    simp only
    rw [mul_div_cancel_right₀ _ hA0]
  refine ⟨fun s hs => by rw [hn s hs]; exact Ioo_subset_Ico_self (hηmem _),
    fun s hs l hl => ?_, fun s hs => ?_⟩
  · -- (1)
    set z₀ := s.1 / s.2 with hz₀def
    have hz₀ := shocks_ratio_mem_Z hx0 hθ0 hs
    have hps : p s = p (z₀ * shocksA xlo θlo z₀, shocksA xlo θlo z₀) := by
      rw [hray z₀ hz₀, hp s hs]
    have hbel := islandsREBeliefs_eq (p := p) (ψ := ψ) (g := g) hz₀ fun w hw hpw => by
      rw [hray w hw, hray z₀ hz₀] at hpw
      exact hinj hw hz₀ hpw
    rw [hps]
    simp only [islandsObj]
    rw [hbel, hn s hs]
    set κ₀ : Measure (ShocksStates xlo xhi θlo θhi) := (Measure.map (fun θ => (z₀ * θ, θ))
      (shocksCondLaw xlo xhi θlo θhi ψ g z₀)).comap Subtype.val with hκ₀
    have := hA.isProbabilityMeasure_condLaw' hπ z₀
    have hκfin : IsFiniteMeasure κ₀ := islands_isFiniteMeasure_comap _
    obtain ⟨hc, hcpos⟩ := islands_factor_continuous hx0 hpc hppos
    set c := fun q : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi =>
      q.2.1.1 * p q.1.1 / (q.1.1.1 * p q.2.1) with hcdef
    set μP := κ₀.prod (islandsNextLaw xlo xhi θlo θhi ψ g)
    have hint : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
        Continuous F → Integrable F μP := fun F hF =>
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩).integrable μP
    have hprod : ∀ F : ShocksStates xlo xhi θlo θhi × ShocksStates xlo xhi θlo θhi → ℝ,
        Continuous F → ∫ q, F q ∂μP =
          ∫ sh, ∫ s', F (sh, s') ∂islandsNextLaw xlo xhi θlo θhi ψ g ∂κ₀ := fun F hF =>
      integral_prod F (hint F hF)
    have hVc : ∀ l, 0 ≤ l → Continuous fun q => V (c q * l) := fun l hl =>
      hV.V_cont.comp_continuous (hc.mul continuous_const) fun q =>
        mem_Ici.2 (mul_nonneg (hcpos q).le hl)
    have hobj : ∀ l, 0 ≤ l → ∫ sh, ∫ s', V (s'.1.1 * l * p sh.1 / (sh.1.1 * p s'.1))
        ∂islandsNextLaw xlo xhi θlo θhi ψ g ∂κ₀ = ∫ q, V (c q * l) ∂μP := fun l hl => by
      rw [hprod _ (hVc l hl)]
      refine integral_congr_ae (ae_of_all _ fun sh => integral_congr_ae (ae_of_all _
        fun s' => ?_))
      simp only [hcdef]
      ring_nf
    set zs := projIcc _ _ hZ z₀ with hzsdef
    set η₀ := olgZetaInv L H' (f zs) with hη₀def
    have hη₀ : η₀ ∈ Ioo 0 L := hηmem z₀
    rw [hobj l hl.1, hobj η₀ hη₀.1.le]
    -- the first-order condition holds at `η₀`
    have hφc : Continuous fun q => olgPhi V' (c q * η₀) :=
      hV.phi_continuousOn.comp_continuous (hc.mul continuous_const) fun q =>
        mem_Ioi.2 (mul_pos (hcpos q) hη₀.1)
    have hzs : (zs : ℝ) = z₀ := by rw [hzsdef, projIcc_of_mem _ hz₀]
    have hb := islands_RE_phi_eq hA hπ hH hV hZ f f.continuous hfpos hp zs
    rw [hzs] at hb
    have hφ : ∫ q, olgPhi V' (c q * η₀) ∂μP = f zs :=
      calc ∫ q, olgPhi V' (c q * η₀) ∂μP = shocksOpT L H' V' θlo θhi
            (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
            (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f zs := by
            rw [hprod _ hφc]; exact hb
        _ = f zs := (hfix zs).symm
    have hζ : f zs = η₀ * H' η₀ := (hH.zeta_zetaInv (hfpos zs).le).symm
    -- concavity
    have hpt : ∀ q, V (c q * l) ≤ V (c q * η₀) + (l - η₀) / η₀ * olgPhi V' (c q * η₀) :=
      fun q => by
        have h := shocks_concave_tangent hV (mul_pos (hcpos q) hη₀.1)
          (mul_nonneg (hcpos q).le hl.1)
        have e : (l - η₀) / η₀ * olgPhi V' (c q * η₀) = V' (c q * η₀) * (c q * l - c q * η₀) := by
          simp only [olgPhi]
          field_simp [hη₀.1.ne']
        rw [e]
        exact h
    have hmono : ∫ q, V (c q * l) ∂μP ≤
        ∫ q, (V (c q * η₀) + (l - η₀) / η₀ * olgPhi V' (c q * η₀)) ∂μP :=
      integral_mono (hint _ (hVc l hl.1)) ((hint _ (hVc η₀ hη₀.1.le)).add
        ((hint _ hφc).const_mul _)) hpt
    rw [integral_add (hint _ (hVc η₀ hη₀.1.le)) ((hint _ hφc).const_mul _),
      integral_const_mul, hφ, hζ] at hmono
    have e2 : (l - η₀) / η₀ * (η₀ * H' η₀) = H' η₀ * (l - η₀) := by
      field_simp [hη₀.1.ne']
    have htan := shocks_convex_tangent hH hη₀ hl
    linarith
  · -- (2)
    rw [hn s hs, hp s hs, mul_div_cancel₀ _ (hηmem _).1.ne']

/-- Rational-expectations beliefs are finite measures. -/
theorem isFiniteMeasure_islandsREBeliefs
    (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z) (p : ℝ × ℝ → ℝ) (P : ℝ) :
    IsFiniteMeasure (islandsREBeliefs xlo xhi θlo θhi ψ g p P) := by
  rw [islandsREBeliefs]
  split_ifs with h
  · have := hA.isProbabilityMeasure_condLaw' hπ h.choose
    exact islands_isFiniteMeasure_comap _
  · infer_instance

/-- **Equilibrium ⇒ fixed point of (4)** (p. 535, the direction the book uses implicitly). Every
equilibrium of the islands economy with a continuous price function, rational-expectations
beliefs and the true law of next period's shocks comes from a strictly positive continuous fixed
point `f = ζ(η)` of (4) whose price function `z/ζ⁻¹(f(z))` is invertible:
`p(x, θ) = (x/θ)/ζ⁻¹(f(x/θ))`. (By `islands_eqm_price_of_ratio`, `p = ρ(x/θ)` with `ρ`
continuous and strictly monotone; the first-order condition `islands_foc` along each ray is
`f = Tf` by `islands_RE_phi_eq`.) -/
theorem islands_fixedPoint_of_eqm (hπ : ∀ z, xlo / θhi < z ∧ z < xhi / θlo → 0 < shocksPi ψ g z)
    (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    (hZ : xlo / θhi ≤ xhi / θlo)
    (he : IslandsEqm L H V p n (islandsREBeliefs xlo xhi θlo θhi ψ g p)
      (islandsNextLaw xlo xhi θlo θhi ψ g))
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi)) :
    ∃ f : Icc (xlo / θhi) (xhi / θlo) →ᵇ ℝ, (∀ z, 0 < f z) ∧
      (∀ z, f z = shocksOpT L H' V' θlo θhi (shocksJointLaw xlo xhi θlo θhi hZ ψ g)
        (fun z => shocksCondLaw xlo xhi θlo θhi ψ g z.1) f z) ∧
      Function.Injective (fun z : Icc (xlo / θhi) (xhi / θlo) =>
        (z : ℝ) / olgZetaInv L H' (f z)) ∧
      ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
        p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))) := by
  have hθ0 := hA.θlo_pos
  have hx0 := hA.xlo_pos
  have hθθ := hA.θlo_lt.le
  have hxx := hA.xlo_lt.le
  have := isProbabilityMeasure_islandsShockLaw hA
  have hν : IsFiniteMeasure (islandsNextLaw xlo xhi θlo θhi ψ g) :=
    islands_isFiniteMeasure_comap _
  have hκ := isFiniteMeasure_islandsREBeliefs hA hπ p
  obtain ⟨ρ, hρc, hρm, hρ⟩ := islands_eqm_price_of_ratio hx0 hxx hθ0 hθθ hH hV he hp
  have hray : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      (w * shocksA xlo θlo w, shocksA xlo θlo w) ∈ Icc xlo xhi ×ˢ Icc θlo θhi ∧
        (w * shocksA xlo θlo w) / shocksA xlo θlo w = w := fun w hw =>
    ⟨shocks_rayPoint_mem hx0 hxx hθ0 hθθ hw,
      mul_div_cancel_right₀ _ (hθ0.trans_le (le_max_right (xlo / w) θlo)).ne'⟩
  have hpρ : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      p (w * shocksA xlo θlo w, shocksA xlo θlo w) = ρ w := fun w hw => by
    rw [(hρ _ (hray w hw).1).1, (hray w hw).2]
  have hnρ : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo),
      n (w * shocksA xlo θlo w, shocksA xlo θlo w) = w / ρ w := fun w hw => by
    rw [(hρ _ (hray w hw).1).2, (hray w hw).2]
  have hinjρ : InjOn ρ (Icc (xlo / θhi) (xhi / θlo)) := by
    rcases hρm with h | h
    · exact h.injOn
    · exact h.injOn
  have hηmem : ∀ w ∈ Icc (xlo / θhi) (xhi / θlo), w / ρ w ∈ Ioo 0 L := fun w hw => by
    have h1 := he.n_mem _ (hray w hw).1
    have h2 := he.clear _ (hray w hw).1
    have h3 := he.p_pos hx0 hθ0 (hray w hw).1
    rw [hnρ w hw] at h1 h2
    rw [(hray w hw).2] at h2
    refine ⟨?_, h1.2⟩
    have hw0 : 0 < w := (div_pos hx0 (hθ0.trans_le hθθ)).trans_le hw.1
    rw [hpρ w hw] at h3
    exact div_pos hw0 h3
  have hηc : ContinuousOn (fun w => w / ρ w) (Icc (xlo / θhi) (xhi / θlo)) :=
    continuousOn_id.div hρc fun w hw => by
      have := he.p_pos hx0 hθ0 (hray w hw).1
      rw [hpρ w hw] at this
      exact this.ne'
  have hfc : Continuous fun z : Icc (xlo / θhi) (xhi / θlo) => olgZeta H' ((z : ℝ) / ρ z) :=
    hH.zeta_continuousOn.comp_continuous (hηc.comp_continuous continuous_subtype_val
      fun z => z.2) fun z => Ioo_subset_Ico_self (hηmem z.1 z.2)
  set f := BoundedContinuousFunction.mkOfCompact ⟨_, hfc⟩ with hfdef
  have hfz : ∀ z : Icc (xlo / θhi) (xhi / θlo), f z = olgZeta H' ((z : ℝ) / ρ z) := fun z => rfl
  have hfinv : ∀ z : Icc (xlo / θhi) (xhi / θlo), olgZetaInv L H' (f z) = (z : ℝ) / ρ z :=
    fun z => by rw [hfz]; exact hH.zetaInv_zeta (Ioo_subset_Ico_self (hηmem z.1 z.2))
  have hfpos : ∀ z, 0 < f z := fun z => by rw [hfz]; exact hH.zeta_pos (hηmem z.1 z.2)
  have hp' : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = s.1 / s.2 / olgZetaInv L H' (f (projIcc _ _ hZ (s.1 / s.2))) := fun s hs => by
    have hz := shocks_ratio_mem_Z hx0 hθ0 hs
    rw [hfinv, projIcc_of_mem _ hz, (hρ s hs).1]
    simp only
    have hρ0 : 0 < ρ (s.1 / s.2) := by
      have := he.p_pos hx0 hθ0 hs
      rwa [(hρ s hs).1] at this
    have hs1 : s.1 ≠ 0 := (hx0.trans_le hs.1.1).ne'
    have hs2 : s.2 ≠ 0 := (hθ0.trans_le hs.2.1).ne'
    field_simp
  refine ⟨f, hfpos, fun z => ?_, fun z w hzw => ?_, hp'⟩
  · -- the first-order condition along the ray `z` is `f = Tf`
    have hs := (hray z.1 z.2).1
    have hfoc := islands_foc hx0 hθ0 hH hV he hp hs
    have hbel := islandsREBeliefs_eq (p := p) (ψ := ψ) (g := g) z.2 fun w hw hpw => by
      rw [hpρ w hw, hpρ z.1 z.2] at hpw
      exact hinjρ hw z.2 hpw
    have hns : n (z.1 * shocksA xlo θlo z.1, shocksA xlo θlo z.1) = olgZetaInv L H' (f z) := by
      rw [hnρ z.1 z.2, hfinv]
    rw [hbel, hns, hH.zeta_zetaInv (hfpos z).le] at hfoc
    rw [hfoc]
    exact islands_RE_phi_eq hA hπ hH hV hZ f f.continuous hfpos hp' z
  · -- the price function is invertible
    simp only [hfinv] at hzw
    have h1 : ρ z = ρ w := by
      have hz0 : 0 < (z : ℝ) := (div_pos hx0 (hθ0.trans_le hθθ)).trans_le z.2.1
      have hw0 : 0 < (w : ℝ) := (div_pos hx0 (hθ0.trans_le hθθ)).trans_le w.2.1
      have hρz : 0 < ρ z := by
        have := (hηmem z.1 z.2).1
        exact (div_pos_iff_of_pos_left hz0).1 this
      have hρw : 0 < ρ w := by
        have := (hηmem w.1 w.2).1
        exact (div_pos_iff_of_pos_left hw0).1 this
      rw [div_div_cancel₀ hz0.ne', div_div_cancel₀ hw0.ne'] at hzw
      exact hzw
    exact Subtype.ext (hinjρ z.2 w.2 h1)

/-! ### Proposition 8 fails as a statement about equilibria -/

omit hA in
/-- **No equilibrium in the bimodal CRRA economy.** In the economy of
`proposition_8_counterexample` (Assumptions 17.1, 17.2 (repaired), 17.4 and 17.5 hold) there is
no equilibrium of the islands economy with a continuous price function, rational-expectations
beliefs and the true law of next period's shocks: it would give a positive fixed point of (4)
with invertible price function (`islands_fixedPoint_of_eqm`), and every positive fixed point has
a non-invertible one (`shocksP8_not_injective`). -/
theorem shocksP8_no_continuous_eqm :
    ¬ ∃ p n : ℝ × ℝ → ℝ, ContinuousOn p (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2)) ∧
      IslandsEqm 1 monoCexH shocksP8V p n
        (islandsREBeliefs 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal p)
        (islandsNextLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal) := by
  rintro ⟨p, n, hp, he⟩
  obtain ⟨f, hfpos, hfix, hinj, -⟩ := islands_fixedPoint_of_eqm shocksExBimodal_assumption
    (fun z hz => shocksExBimodal_pi_pos hz) monoCexH_assumption17_1H' shocksP8V_assumptions.1
    shocksP8_hZ he hp
  exact (shocksP8_not_injective f hfpos hfix).1 hinj

omit hA in
/-- `W'(y) ≥ A = 1/60000` on `(0, 1]` when `y₀ ≤ 1`. -/
theorem shocksP8W'_ge {y₀ y : ℝ} (hy₀ : 0 < y₀) (hy₀1 : y₀ ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) :
    1 / 60000 ≤ shocksP8W' y₀ y := by
  simp only [shocksP8W', shocksP8V']
  split_ifs with h
  · have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by norm_num : (-(1 / 20) : ℝ) ≤ 0)
    nlinarith
  · have h1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy₀ hy₀1
      (by norm_num : (-(1 / 20) : ℝ) ≤ 0)
    have h2 : y / y₀ < 1 := (div_lt_one hy₀).2 (not_le.1 h)
    have e : 1 / 20 * y / y₀ = 1 / 20 * (y / y₀) := by ring
    rw [e]
    nlinarith

omit hA in
/-- **An a priori lower bound** for the utility `shocksP8W y₀`, `y₀ ≤ 1`: every strictly positive
continuous fixed point of (4) in the bimodal economy has `η = ζ⁻¹ ∘ f ≥ 1/180000 = A/3`, since
`φ_W(y) ≥ A y` on `(0, 1]` and the arguments of `φ` are at least `(2/3) min η`. -/
theorem shocksP8W_eta_ge {y₀ : ℝ} (hy₀ : 0 < y₀) (hy₀1 : y₀ ≤ 1)
    (f : Icc (1 / (3 / 2) : ℝ) (2 / 1) →ᵇ ℝ) (hfpos : ∀ z, 0 < f z)
    (hfix : ∀ z, f z = shocksOpT 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z) :
    ∀ z, 1 / 180000 ≤ olgZetaInv 1 monoCexH' (f z) := by
  have hH := monoCexH_assumption17_1H'
  have hV := shocks_assumption17_1VR_of_V (shocksP8W_assumptions hy₀).1
  have h4 : MonoAssumption17_4Pos (shocksP8W' y₀) (shocksP8W'' y₀) := fun y hy =>
    (shocksP8W_assumptions hy₀).2 y hy.le
  have hφm := shocks_phi_monotoneOn hV h4
  have hA := shocksExBimodal_assumption
  have := isProbabilityMeasure_shocksJointLaw hA shocksP8_hZ
  have hν : ∀ z : ℝ, IsProbabilityMeasure
      (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z) :=
    hA.isProbabilityMeasure_condLaw' fun z hz => shocksExBimodal_pi_pos hz
  obtain ⟨l₀, hS⟩ := shocksBounds_exists one_pos (by norm_num : (1 : ℝ) ≤ 3 / 2) hH hV
  have hne : (univ : Set (Icc (1 / (3 / 2) : ℝ) (2 / 1))).Nonempty :=
    ⟨⟨_, left_mem_Icc.2 shocksP8_hZ⟩, mem_univ _⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn hne f.continuous.continuousOn
  set ηm := olgZetaInv 1 monoCexH' (f m) with hηmdef
  have hηm : ηm ∈ Ioo 0 1 := ⟨hH.zetaInv_pos (hfpos m), (hH.zetaInv_mem (hfpos m).le).2⟩
  have hle : ∀ z, ηm ≤ olgZetaInv 1 monoCexH' (f z) := fun z =>
    hH.zetaInv_strictMonoOn.monotoneOn (mem_Ici.2 (hfpos m).le) (mem_Ici.2 (hfpos z).le)
      (isMinOn_iff.1 hm z (mem_univ z))
  set l := min l₀ ηm
  have hl : l ∈ Ioc 0 l₀ := ⟨lt_min hS.l₀_mem.1 hηm.1, min_le_left _ _⟩
  have hlL : l ∈ Ico 0 1 := ⟨hl.1.le, hl.2.trans_lt hS.l₀_mem.2⟩
  have hfl : ∀ z, olgZeta monoCexH' l ≤ f z := fun z =>
    calc olgZeta monoCexH' l ≤ olgZeta monoCexH' ηm :=
          hH.zeta_strictMonoOn.monotoneOn hlL (hH.zetaInv_mem (hfpos m).le) (min_le_right _ _)
      _ = f m := hH.zeta_zetaInv (hfpos m).le
      _ ≤ f z := isMinOn_iff.1 hm z (mem_univ z)
  obtain ⟨B, -, hB⟩ := hS.exists_integrand_le hl
  -- the integrand is at least `c = (2/3) ηm A`
  set c := 2 / 3 * ηm * (1 / 60000) with hcdef
  have hpt : ∀ θt (ω : ℝ × Icc (1 / (3 / 2) : ℝ) (2 / 1)),
      c ≤ shocksIntegrand 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2) f θt ω := fun θt ω => by
    have hr := (shocksRatio_mem (θlo := (1 : ℝ)) (θhi := 3 / 2) one_pos (by norm_num) ω.1 θt).1
    have hη' := hle ω.2
    have hy1 : 0 < 2 / 3 * ηm := by linarith [hηm.1]
    have hy : 2 / 3 * ηm ≤ shocksRatio 1 (3 / 2) ω.1 θt * olgZetaInv 1 monoCexH' (f ω.2) := by
      have hr' : (2 : ℝ) / 3 ≤ shocksRatio 1 (3 / 2) ω.1 θt :=
        (by norm_num : (2 : ℝ) / 3 = 1 / (3 / 2)).trans_le hr
      nlinarith [hηm.1]
    have h1 := hφm (mem_Ioi.2 hy1) (mem_Ioi.2 (hy1.trans_le hy)) hy
    have h2 := shocksP8W'_ge hy₀ hy₀1 hy1 (by linarith [hηm.2])
    simp only [shocksIntegrand]
    refine le_trans ?_ h1
    simp only [olgPhi, hcdef]
    nlinarith
  have hphi : ∀ θt, c ≤ shocksPhiF 1 monoCexH' (shocksP8W' y₀) 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal) f θt :=
    fun θt => by
      have := integral_mono (integrable_const c)
        (hS.integrable_integrand hl hB f.continuous hfl
          (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal) θt)
        fun ω => hpt θt ω
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
      exact this
  have hfm : c ≤ f m := by
    rw [hfix m]
    have := integral_mono (integrable_const c)
      ((hS.phiFBCF hl hB f.continuous hfl
        (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)).integrable
        (shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal m.1)) fun θt => hphi θt
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  have hζ := shocksP8_zeta_eq hηm.2 (hH.zeta_zetaInv (hfpos m).le)
  have key : ηm * ((1 - ηm) / 90000) ≤ ηm * ηm := by
    have h1m : 0 < 1 - ηm := by linarith [hηm.2]
    have := mul_le_mul_of_nonneg_right hfm h1m.le
    simp only [hcdef] at this
    nlinarith
  have := le_of_mul_le_mul_left key hηm.1
  intro z
  linarith [hle z]

omit hA in
/-- **No equilibrium under the book's hypotheses.** With the utility `shocksP8W (1/300000)`
(the book's Assumption 17.1, `V'(0) < ∞`, and Assumption 17.4; `H` as in Assumption 17.1) the
bimodal economy has no equilibrium with a continuous price function, rational-expectations
beliefs and the true law of next period's shocks. A positive fixed point of (4) for this `V` has
`η ≥ A/3 > (3/2) y₀` (`shocksP8W_eta_ge`), so it is also a fixed point for the CRRA utility
(`shocksP8W_opT_eq`), whose price function is not invertible. -/
theorem shocksP8W_no_continuous_eqm :
    ¬ ∃ p n : ℝ × ℝ → ℝ, ContinuousOn p (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2)) ∧
      IslandsEqm 1 monoCexH (shocksP8W (1 / 300000)) p n
        (islandsREBeliefs 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal p)
        (islandsNextLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal) := by
  rintro ⟨p, n, hp, he⟩
  have hy : (0 : ℝ) < 1 / 300000 := by norm_num
  obtain ⟨f, hfpos, hfix, hinj, -⟩ := islands_fixedPoint_of_eqm shocksExBimodal_assumption
    (fun z hz => shocksExBimodal_pi_pos hz) monoCexH_assumption17_1H'
    (shocks_assumption17_1VR_of_V (shocksP8W_assumptions hy).1) shocksP8_hZ he hp
  have hη := shocksP8W_eta_ge hy (by norm_num) f hfpos hfix
  have hfix' : ∀ z, f z = shocksOpT 1 monoCexH' shocksP8V' 1 (3 / 2)
      (shocksJointLaw 1 2 1 (3 / 2) shocksP8_hZ (shocksUnif 1 2) shocksExBimodal)
      (fun z => shocksCondLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal z.1) f z :=
    fun z => (hfix z).trans (shocksP8W_opT_eq hy _ _ f (fun w => by linarith [hη w]) z)
  exact (shocksP8_not_injective f hfpos hfix').1 hinj

omit hA in
/-- **Proposition 8 (p. 540) fails for equilibria.** The bimodal economy with the utility
`shocksP8W (1/300000)` satisfies all hypotheses of Proposition 8 (the book's Assumptions 17.1 and
17.4, and Assumption 17.5), yet it has no equilibrium with a continuous price function at all,
let alone one with an increasing price function. -/
theorem proposition_8_eqm_counterexample :
    ShocksAssumption17_5 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal ∧
      Assumption17_1 1 monoCexH monoCexH' monoCexH'' (shocksP8W (1 / 300000))
        (shocksP8W' (1 / 300000)) (shocksP8W'' (1 / 300000)) ∧
      MonoAssumption17_4 (shocksP8W' (1 / 300000)) (shocksP8W'' (1 / 300000)) ∧
      ¬ ∃ p n : ℝ × ℝ → ℝ, ContinuousOn p (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) (3 / 2)) ∧
        IslandsEqm 1 monoCexH (shocksP8W (1 / 300000)) p n
          (islandsREBeliefs 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal p)
          (islandsNextLaw 1 2 1 (3 / 2) (shocksUnif 1 2) shocksExBimodal) :=
  ⟨shocksExBimodal_assumption, ⟨monoCexH_assumption17_1H',
    (shocksP8W_assumptions (by norm_num)).1⟩, (shocksP8W_assumptions (by norm_num)).2,
    shocksP8W_no_continuous_eqm⟩

end StokeyLucasPrescott.FixedPointArguments
