/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.ShocksMonotone

/-!
# Partially observed shocks: continuous equilibrium prices reveal exactly `x/θ`

SLP §17.6, pp. 532–533. The book argues that two states with the same price are
indistinguishable to the young, so (by strict concavity of (1)) they get the same labour supply,
and then (2) forces the same ratio `x/θ`; it concludes that "any equilibrium must be of the form
`p(x, θ) = ρ(x/θ)`". The argument proves only "equal prices ⇒ equal ratios"
(`p533_ratio_of_price`), and `p533_counterexample` (`FixedPointArguments.ShocksModel`) shows the
conclusion does not follow from those premises for a discontinuous `p`. Here the islands economy's
equilibrium conditions are formalised and the conclusion is proved for continuous prices, the
class in which the book looks for equilibria (`ρ` continuous on `Z`).

* `ShocksStates`: the state space `X × Θ`. `islandsObj`: the objective in (1), with the
  young agent's beliefs `κ(P)` about the current state given the price `P` and the law `ν` of next
  period's shocks. **`IslandsEqm`** (p. 532): conditions (1) (optimality given the price) and (2)
  (market clearing `n p = x/θ`); `IslandsEqm.p_pos`: equilibrium prices are positive.
* `islandsObj_max_unique` (p. 533, "(1) is strictly concave in `l`"): under Assumption 17.1 the
  maximiser in (1) is unique, so `n` is a function of `p`.
* `shocks_const_on_rays` (topology): a function continuous on `X × Θ` whose level sets lie in
  the rays `x/θ = z` is constant on each ray (intermediate value theorem on the convex ray
  segments `shocks_convex_ray`, and on nearby rays, `shocks_exists_ray_approx`).
* **`islands_eqm_price_of_ratio`** (p. 533, settled for continuous prices): every equilibrium with
  `p` continuous on `X × Θ` has `p(x, θ) = ρ(x/θ)`, `n(x, θ) = (x/θ)/ρ(x/θ)` with `ρ` continuous
  and strictly monotone (hence invertible) on `Z`. This holds for **every** price-indexed belief
  family `κ`, in particular for rational expectations. So no continuous price reveals more than
  `x/θ`, and every continuous equilibrium price reveals `x/θ` (the invertibility that the book
  imposes on `ρ` is automatic).
* `islands_eqm_not_injOn`: no continuous equilibrium price is fully revealing.

**Correction (p. 533), completed.** For continuous prices the book's conclusion is true but its
argument is incomplete: the missing step "equal ratios ⇒ equal prices" is the topological
`shocks_const_on_rays`, which uses continuity essentially (`p533_counterexample`). Whether a
*discontinuous* price revealing more than `x/θ` can satisfy (1) with rational-expectations beliefs
is not settled here.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory Set Filter Topology

variable {xlo xhi θlo θhi : ℝ}

/-- A point `u = (x, θ) ≠ (x̄, θ̲)` of the ray `x = zθ` in `X × Θ` is the limit, as `w ↓ z`, of
points of the rays `x = wθ` in `X × Θ`. -/
theorem shocks_exists_ray_approx (hθ0 : 0 < θlo) {z : ℝ} (hz : 0 < z) {u : ℝ × ℝ}
    (hu : u ∈ Icc xlo xhi ×ˢ Icc θlo θhi) (huz : u.1 = z * u.2) (hne : u ≠ (xhi, θlo)) :
    ∃ γ : ℝ → ℝ × ℝ, Tendsto γ (𝓝[>] z) (𝓝 u) ∧
      ∀ᶠ w in 𝓝[>] z, γ w ∈ Icc xlo xhi ×ˢ Icc θlo θhi ∧ (γ w).1 = w * (γ w).2 := by
  obtain ⟨⟨hx1, hx2⟩, hθ1, hθ2⟩ := hu
  have hev : ∀ᶠ w in 𝓝[>] z, z < w := self_mem_nhdsWithin
  rcases hx2.lt_or_eq with hlt | heq
  · -- move `x` up
    refine ⟨fun w => (u.1 * (w / z), u.2), ?_, ?_⟩
    · have : Tendsto (fun w => (u.1 * (w / z), u.2)) (𝓝 z) (𝓝 (u.1 * (z / z), u.2)) :=
        ((continuous_const.mul (continuous_id.div_const z)).prodMk continuous_const).tendsto z
      rw [div_self hz.ne', mul_one] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · have ht : Tendsto (fun w => u.1 * (w / z)) (𝓝[>] z) (𝓝 u.1) := by
        have : Tendsto (fun w => u.1 * (w / z)) (𝓝 z) (𝓝 (u.1 * (z / z))) :=
          ((continuous_const.mul (continuous_id.div_const z))).tendsto z
        rw [div_self hz.ne', mul_one] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      filter_upwards [hev, ht.eventually (gt_mem_nhds hlt)] with w hw h1
      have hx0 : 0 ≤ u.1 := by rw [huz]; exact mul_nonneg hz.le (by linarith)
      refine ⟨⟨⟨?_, h1.le⟩, hθ1, hθ2⟩, ?_⟩
      · have : 1 ≤ w / z := (one_le_div hz).2 hw.le
        nlinarith
      · rw [huz]
        field_simp
  · -- `x = x̄`: move `θ` down
    have hθlt : θlo < u.2 := by
      rcases hθ1.lt_or_eq with h | h
      · exact h
      · exact absurd (Prod.ext heq h.symm) hne
    have ht : Tendsto (fun w => u.2 * (z / w)) (𝓝[>] z) (𝓝 u.2) := by
      have : Tendsto (fun w => u.2 * (z / w)) (𝓝 z) (𝓝 (u.2 * (z / z))) :=
        (continuousAt_const.mul (continuousAt_const.div continuousAt_id hz.ne')).tendsto
      rw [div_self hz.ne', mul_one] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine ⟨fun w => (u.1, u.2 * (z / w)), tendsto_const_nhds.prodMk_nhds ht, ?_⟩
    filter_upwards [hev, ht.eventually (lt_mem_nhds hθlt)] with w hw h1
    have hw0 : 0 < w := hz.trans hw
    refine ⟨⟨⟨hx1, hx2⟩, h1.le, ?_⟩, ?_⟩
    · have : z / w ≤ 1 := (div_le_one hw0).2 hw.le
      have h0 : 0 ≤ u.2 := by linarith
      calc u.2 * (z / w) ≤ u.2 * 1 := mul_le_mul_of_nonneg_left this h0
        _ ≤ θhi := by linarith
    · rw [huz]
      field_simp

/-- The part of the ray `x = wθ` in `X × Θ` is convex. -/
theorem shocks_convex_ray (w : ℝ) :
    Convex ℝ {u ∈ Icc xlo xhi ×ˢ Icc θlo θhi | u.1 = w * u.2} := by
  rintro a ⟨haS, haz⟩ b ⟨hbS, hbz⟩ α β hα hβ hαβ
  refine ⟨(convex_Icc xlo xhi).prod (convex_Icc θlo θhi) haS hbS hα hβ hαβ, ?_⟩
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [haz, hbz]
  ring

/-- **Continuous prices are functions of `x/θ`.** If `p` is continuous on `X × Θ` and equal
prices imply equal ratios `x/θ` (what the argument on p. 533 proves, `p533_ratio_of_price`), then
`p` is constant on each ray `x/θ = z`. Otherwise `p` takes a value `m` strictly between two of its
values on one ray; by continuity it takes values on both sides of `m` on every nearby ray, hence
(intermediate value theorem on the convex ray segments) the value `m` itself, on two different
rays. -/
theorem shocks_const_on_rays (hx0 : 0 < xlo) (hθ0 : 0 < θlo) {p : ℝ × ℝ → ℝ}
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    (hsep : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ t ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = p t → s.1 / s.2 = t.1 / t.2)
    {s t : ℝ × ℝ} (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) (ht : t ∈ Icc xlo xhi ×ˢ Icc θlo θhi)
    (hst : s.1 / s.2 = t.1 / t.2) : p s = p t := by
  by_contra hne
  wlog h : p s < p t generalizing s t
  · exact this ht hs hst.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne))
  set S := Icc xlo xhi ×ˢ Icc θlo θhi with hSdef
  have hpos : ∀ u ∈ S, 0 < u.2 := fun u hu => hθ0.trans_le hu.2.1
  set z := s.1 / s.2 with hzdef
  have hz : 0 < z := div_pos (hx0.trans_le hs.1.1) (hpos s hs)
  have hsz : s.1 = z * s.2 := by rw [hzdef, div_mul_cancel₀ _ (hpos s hs).ne']
  have htz : t.1 = z * t.2 := by rw [hst, div_mul_cancel₀ _ (hpos t ht).ne']
  -- neither point is the corner `(x̄, θ̲)`, else the ray meets `X × Θ` only there
  have hcorner : ∀ u ∈ S, ∀ v ∈ S, u.1 = z * u.2 → v.1 = z * v.2 → u = (xhi, θlo) → v = u := by
    intro u hu v hv huz hvz hu0
    rw [hu0] at huz
    simp only at huz
    have h1 : xhi ≤ v.1 := by
      rw [hvz, huz]
      exact mul_le_mul_of_nonneg_left hv.2.1 hz.le
    have hv1 : v.1 = xhi := le_antisymm hv.1.2 h1
    have hv2 : v.2 = θlo := by
      have h2 : z * v.2 ≤ z * θlo := by rw [← hvz, ← huz]; exact hv.1.2
      exact le_antisymm (le_of_mul_le_mul_left h2 hz) hv.2.1
    rw [hu0]
    exact Prod.ext hv1 hv2
  have hs0 : s ≠ (xhi, θlo) := fun h0 => hne (by rw [hcorner s hs t ht hsz htz h0])
  have ht0 : t ≠ (xhi, θlo) := fun h0 => hne (by rw [hcorner t ht s hs htz hsz h0])
  -- the value `m` is taken on the ray `z`
  obtain ⟨m, hm⟩ : ∃ m, m = (p s + p t) / 2 := ⟨_, rfl⟩
  obtain ⟨u, ⟨huS, huz⟩, hum⟩ := (shocks_convex_ray (xlo := xlo) (xhi := xhi) (θlo := θlo)
    (θhi := θhi) z).isPreconnected.intermediate_value ⟨hs, hsz⟩ ⟨ht, htz⟩
    (hp.mono fun _ h => h.1) (show m ∈ Icc (p s) (p t) from ⟨by linarith, by linarith⟩)
  -- nearby rays
  obtain ⟨γs, hγs, hγsS⟩ := shocks_exists_ray_approx hθ0 hz hs hsz hs0
  obtain ⟨γt, hγt, hγtS⟩ := shocks_exists_ray_approx hθ0 hz ht htz ht0
  have hps : Tendsto (fun w => p (γs w)) (𝓝[>] z) (𝓝 (p s)) :=
    (hp s hs).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγs, hγsS.mono fun _ h => h.1⟩)
  have hpt : Tendsto (fun w => p (γt w)) (𝓝[>] z) (𝓝 (p t)) :=
    (hp t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγt, hγtS.mono fun _ h => h.1⟩)
  obtain ⟨w, hw, hγsw, hγtw, h1, h2⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[>] z, w ∈ Ioi z).and
    (hγsS.and (hγtS.and ((hps.eventually (gt_mem_nhds (show p s < m by linarith))).and
    (hpt.eventually (lt_mem_nhds (show m < p t by linarith))))))).exists
  obtain ⟨v, ⟨hvS, hvw⟩, hvm⟩ := (shocks_convex_ray (xlo := xlo) (xhi := xhi) (θlo := θlo)
    (θhi := θhi) w).isPreconnected.intermediate_value hγsw hγtw (hp.mono fun _ h => h.1)
    (show m ∈ Icc (p (γs w)) (p (γt w)) from ⟨h1.le, h2.le⟩)
  have := hsep v hvS u huS (by rw [hvm, hum])
  rw [hvw, huz, mul_div_cancel_right₀ _ (hpos v hvS).ne',
    mul_div_cancel_right₀ _ (hpos u huS).ne'] at this
  exact (ne_of_gt (mem_Ioi.1 hw)) this

/-! ### The islands economy: equilibrium conditions (1)–(2) -/

/-- The state space `X × Θ`, as a subtype of `ℝ × ℝ`. -/
abbrev ShocksStates (xlo xhi θlo θhi : ℝ) : Type := ↥(Icc xlo xhi ×ˢ Icc θlo θhi)

/-- The objective in (1) (p. 532) of a young agent who observes the price `P` and supplies `l`:
`−H(l) + E_{(x̂, θ̂) ~ κ(P)} E_{(x′, θ′) ~ ν} V[x′ l p(x̂, θ̂)/(x̂ p(x′, θ′))]`. Here `κ(P)` is the
agent's belief about the current state given the price `P` (in the book, the conditional law of
`(x, θ)` given `p(x, θ) = P`) and `ν` is the law of next period's shocks. -/
noncomputable def islandsObj {xlo xhi θlo θhi : ℝ} (H V : ℝ → ℝ) (p : ℝ × ℝ → ℝ)
    (κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi)) (ν : Measure (ShocksStates xlo xhi θlo θhi))
    (P l : ℝ) : ℝ :=
  -H l + ∫ sh, ∫ s', V (s'.1.1 * l * p sh.1 / (sh.1.1 * p s'.1)) ∂ν ∂κ P

variable (L : ℝ) (H V : ℝ → ℝ) (p n : ℝ × ℝ → ℝ) (κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi))
  (ν : Measure (ShocksStates xlo xhi θlo θhi)) in
/-- **Stationary equilibrium of the islands economy** (p. 532): a price function `p` and labour
supply `n` on `X × Θ` such that (1) at every state `n(x, θ) ∈ [0, L)` maximises the objective
`islandsObj` given the observed price `p(x, θ)`, and (2) `n(x, θ) p(x, θ) = x/θ`. The beliefs `κ`
are an arbitrary family indexed by the price (the agent sees only the price); the results below
hold for every such family, in particular for the rational-expectations one. -/
structure IslandsEqm : Prop where
  n_mem : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, n s ∈ Ico 0 L
  opt : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ l ∈ Ico 0 L,
    islandsObj H V p κ ν (p s) l ≤ islandsObj H V p κ ν (p s) (n s)
  clear : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, n s * p s = s.1 / s.2

variable {L : ℝ} {H H' H'' V V' V'' : ℝ → ℝ} {p n : ℝ × ℝ → ℝ}
  {κ : ℝ → Measure (ShocksStates xlo xhi θlo θhi)} {ν : Measure (ShocksStates xlo xhi θlo θhi)}

/-- In equilibrium prices are strictly positive (from (2), since `n ≥ 0` and `x/θ > 0`). -/
theorem IslandsEqm.p_pos (he : IslandsEqm L H V p n κ ν) (hx0 : 0 < xlo) (hθ0 : 0 < θlo)
    {s : ℝ × ℝ} (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) : 0 < p s := by
  have h2 := he.clear s hs
  have hz : 0 < s.1 / s.2 := div_pos (hx0.trans_le hs.1.1) (hθ0.trans_le hs.2.1)
  have hn := (he.n_mem s hs).1
  by_contra h
  push Not at h
  nlinarith

/-- **The maximiser in (1) is unique** (p. 533: "(1) is strictly concave in `l`"). Under
Assumption 17.1 (`H` strictly convex; `V` continuous and concave on `ℝ₊`), for continuous
positive `p` and finite measures `κ(P)`, `ν`, the objective `islandsObj` at the price `P` has at
most one maximiser on `[0, L)`. -/
theorem islandsObj_max_unique (hx0 : 0 < xlo) (hH : Assumption17_1H L H H' H'')
    (hV : Assumption17_1VR V V' V'') (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi))
    (hppos : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, 0 < p s) [IsFiniteMeasure ν]
    [∀ P, IsFiniteMeasure (κ P)] (P : ℝ) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ico 0 L) (hm₂ : m₂ ∈ Ico 0 L)
    (h₁ : ∀ l ∈ Ico 0 L, islandsObj H V p κ ν P l ≤ islandsObj H V p κ ν P m₁)
    (h₂ : ∀ l ∈ Ico 0 L, islandsObj H V p κ ν P l ≤ islandsObj H V p κ ν P m₂) : m₁ = m₂ := by
  have : CompactSpace (ShocksStates xlo xhi θlo θhi) :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  by_contra hne
  set Ω := ShocksStates xlo xhi θlo θhi
  have hpc : Continuous fun s : Ω => p s.1 := hp.comp_continuous continuous_subtype_val
    fun s => s.2
  have hxpos : ∀ s : Ω, 0 < s.1.1 := fun s => hx0.trans_le s.2.1.1
  have hppos' : ∀ s : Ω, 0 < p s.1 := fun s => hppos s.1 s.2
  -- the integrand and its continuity
  set F : ℝ → Ω × Ω → ℝ := fun l q => V (q.2.1.1 * l * p q.1.1 / (q.1.1.1 * p q.2.1))
  have harg : ∀ l, Continuous fun q : Ω × Ω => q.2.1.1 * l * p q.1.1 / (q.1.1.1 * p q.2.1) :=
    fun l => (((continuous_subtype_val.fst.comp continuous_snd).mul continuous_const).mul
      (hpc.comp continuous_fst)).div ((continuous_subtype_val.fst.comp continuous_fst).mul
      (hpc.comp continuous_snd)) fun q => (mul_pos (hxpos q.1) (hppos' q.2)).ne'
  have hargnn : ∀ l, 0 ≤ l → ∀ q : Ω × Ω, 0 ≤ q.2.1.1 * l * p q.1.1 / (q.1.1.1 * p q.2.1) :=
    fun l hl q => div_nonneg (mul_nonneg (mul_nonneg (hxpos q.2).le hl) (hppos' q.1).le)
      (mul_pos (hxpos q.1) (hppos' q.2)).le
  have hF : ∀ l, 0 ≤ l → Continuous (F l) := fun l hl =>
    hV.V_cont.comp_continuous (harg l) fun q => mem_Ici.2 (hargnn l hl q)
  have hFi : ∀ l, 0 ≤ l → ∀ sh : Ω, Integrable (fun s' => F l (sh, s')) ν := fun l hl sh =>
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun s' => F l (sh, s'), (hF l hl).comp (continuous_const.prodMk continuous_id)⟩).integrable ν
  have hG : ∀ l, 0 ≤ l → Continuous fun sh : Ω => ∫ s', F l (sh, s') ∂ν := fun l hl => by
    have := continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun sh s' => F l (sh, s')) (hF l hl) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hGi : ∀ l, 0 ≤ l → Integrable (fun sh : Ω => ∫ s', F l (sh, s') ∂ν) (κ P) := fun l hl =>
    (BoundedContinuousFunction.mkOfCompact ⟨_, hG l hl⟩).integrable (κ P)
  -- midpoint concavity of the expected-utility term
  set m := (m₁ + m₂) / 2 with hmdef
  have hm : m ∈ Ico 0 L := ⟨by linarith [hm₁.1, hm₂.1], by linarith [hm₁.2, hm₂.2]⟩
  have hpt : ∀ q : Ω × Ω, (F m₁ q + F m₂ q) / 2 ≤ F m q := fun q => by
    have := hV.V_conc.concaveOn.2 (mem_Ici.2 (hargnn m₁ hm₁.1 q)) (mem_Ici.2 (hargnn m₂ hm₂.1 q))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hmid : q.2.1.1 * m * p q.1.1 / (q.1.1.1 * p q.2.1) =
        1 / 2 * (q.2.1.1 * m₁ * p q.1.1 / (q.1.1.1 * p q.2.1)) +
          1 / 2 * (q.2.1.1 * m₂ * p q.1.1 / (q.1.1.1 * p q.2.1)) := by rw [hmdef]; ring
    calc (F m₁ q + F m₂ q) / 2 = 1 / 2 * F m₁ q + 1 / 2 * F m₂ q := by ring
      _ ≤ F m q := by simp only [F]; rw [hmid]; exact this
  have hE : (∫ sh, ∫ s', F m₁ (sh, s') ∂ν ∂κ P + ∫ sh, ∫ s', F m₂ (sh, s') ∂ν ∂κ P) / 2 ≤
      ∫ sh, ∫ s', F m (sh, s') ∂ν ∂κ P := by
    rw [← integral_add (hGi m₁ hm₁.1) (hGi m₂ hm₂.1), ← integral_div]
    refine integral_mono (((hGi m₁ hm₁.1).add (hGi m₂ hm₂.1)).div_const 2) (hGi m hm.1)
      fun sh => ?_
    simp only
    rw [← integral_add (hFi m₁ hm₁.1 sh) (hFi m₂ hm₂.1 sh), ← integral_div]
    exact integral_mono (((hFi m₁ hm₁.1 sh).add (hFi m₂ hm₂.1 sh)).div_const 2) (hFi m hm.1 sh)
      fun s' => hpt (sh, s')
  -- strict convexity of `H`
  have hHc := hH.H_conv.2 hm₁ hm₂ hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hHc
  rw [show 1 / 2 * m₁ + 1 / 2 * m₂ = m by rw [hmdef]; ring] at hHc
  have e1 := h₁ m₂ hm₂
  have e2 := h₂ m₁ hm₁
  have e3 := h₁ m hm
  simp only [islandsObj] at e1 e2 e3
  change -H m₁ + ∫ sh, ∫ s', F m₁ (sh, s') ∂ν ∂κ P ≤ _ at e2
  linarith

/-- The end `(z a(z), a(z))`, `a(z) = max{x̲/z, θ̲}`, of the ray `x/θ = z` lies in `X × Θ` for
`z ∈ Z`. -/
theorem shocks_rayPoint_mem (hx0 : 0 < xlo) (hxx : xlo ≤ xhi) (hθ0 : 0 < θlo) (hθθ : θlo ≤ θhi)
    {z : ℝ} (hz : z ∈ Icc (xlo / θhi) (xhi / θlo)) :
    (z * shocksA xlo θlo z, shocksA xlo θlo z) ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
  have hθhi : 0 < θhi := hθ0.trans_le hθθ
  have hz0 : 0 < z := (div_pos hx0 hθhi).trans_le hz.1
  refine ⟨⟨?_, ?_⟩, le_max_right _ _, max_le ?_ hθθ⟩
  · rw [mul_shocksA hz0]; exact le_max_left _ _
  · rw [mul_shocksA hz0]
    refine max_le hxx ?_
    have := hz.2
    rwa [le_div_iff₀ hθ0] at this
  · rw [div_le_iff₀ hz0]
    have := hz.1
    rwa [div_le_iff₀ hθhi, mul_comm] at this

/-- The ratio `x/θ` of a state lies in `Z = [x̲/θ̄, x̄/θ̲]`. -/
theorem shocks_ratio_mem_Z (hx0 : 0 < xlo) (hθ0 : 0 < θlo) {s : ℝ × ℝ}
    (hs : s ∈ Icc xlo xhi ×ˢ Icc θlo θhi) : s.1 / s.2 ∈ Icc (xlo / θhi) (xhi / θlo) :=
  ⟨div_le_div₀ (hx0.trans_le hs.1.1).le hs.1.1 (hθ0.trans_le hs.2.1) hs.2.2,
    div_le_div₀ (hx0.le.trans (hs.1.1.trans hs.1.2)) hs.1.2 hθ0 hs.2.1⟩

/-- **The p. 533 claim, for continuous prices.** Under Assumption 17.1 (`H` as in the book, `V`
continuous and concave on `ℝ₊`, as in the repaired Assumption 17.1), every stationary
equilibrium `(p, n)` of the islands economy (`IslandsEqm`, conditions (1)–(2)) with `p` continuous
on `X × Θ` has the form `p(x, θ) = ρ(x/θ)`, `n(x, θ) = (x/θ)/ρ(x/θ)` with `ρ` continuous and
strictly monotone on `Z`, whatever the price-indexed beliefs `κ`. So a continuous price never
reveals more than `x/θ`, and it always reveals `x/θ`.

Proof: the maximiser in (1) is unique (`islandsObj_max_unique`), so `n` is a function of `p`;
(2) then gives "equal prices ⇒ equal ratios" (`p533_ratio_of_price`); continuity upgrades this
to "equal ratios ⇒ equal prices" (`shocks_const_on_rays`). Continuity cannot be dropped from the
last step (`p533_counterexample`). -/
theorem islands_eqm_price_of_ratio (hx0 : 0 < xlo) (hxx : xlo ≤ xhi) (hθ0 : 0 < θlo)
    (hθθ : θlo ≤ θhi) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    [IsFiniteMeasure ν] [∀ P, IsFiniteMeasure (κ P)] (he : IslandsEqm L H V p n κ ν)
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi)) :
    ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Icc (xlo / θhi) (xhi / θlo)) ∧
      (StrictMonoOn ρ (Icc (xlo / θhi) (xhi / θlo)) ∨
        StrictAntiOn ρ (Icc (xlo / θhi) (xhi / θlo))) ∧
      ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, p s = ρ (s.1 / s.2) ∧ n s = s.1 / s.2 / ρ (s.1 / s.2) := by
  have hppos := fun s hs => he.p_pos hx0 hθ0 (s := s) hs
  -- `n` is a function of `p`
  have hn : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ t ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = p t → n s = n t := fun s hs t ht hst =>
    islandsObj_max_unique hx0 hH hV hp hppos (p s) (he.n_mem s hs) (he.n_mem t ht) (he.opt s hs)
      (by rw [hst]; exact he.opt t ht)
  have hsep : ∀ s ∈ Icc xlo xhi ×ˢ Icc θlo θhi, ∀ t ∈ Icc xlo xhi ×ˢ Icc θlo θhi,
      p s = p t → s.1 / s.2 = t.1 / t.2 := fun s hs t ht hst => by
    rw [← he.clear s hs, ← he.clear t ht, hn s hs t ht hst, hst]
  have hconst := fun s hs t ht hst =>
    shocks_const_on_rays hx0 hθ0 hp hsep (s := s) (t := t) hs ht hst
  -- the ray point and its ratio
  have hA0 : ∀ z, 0 < shocksA xlo θlo z := fun z => hθ0.trans_le (le_max_right _ _)
  have hratio : ∀ z, (z * shocksA xlo θlo z) / shocksA xlo θlo z = z := fun z =>
    mul_div_cancel_right₀ _ (hA0 z).ne'
  have hA : ContinuousOn (shocksA xlo θlo) (Icc (xlo / θhi) (xhi / θlo)) := by
    have h1 : ContinuousOn (fun z : ℝ => xlo / z) (Icc (xlo / θhi) (xhi / θlo)) :=
      continuousOn_const.div continuousOn_id fun z hz =>
        ((div_pos hx0 (hθ0.trans_le hθθ)).trans_le hz.1).ne'
    exact h1.sup continuousOn_const
  refine ⟨fun z => p (z * shocksA xlo θlo z, shocksA xlo θlo z), ?_, ?_, fun s hs => ?_⟩
  · -- continuity
    exact hp.comp ((continuousOn_id.mul hA).prodMk hA) fun z hz =>
      shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz
  · -- injectivity, hence strict monotonicity
    refine ContinuousOn.strictMonoOn_of_injOn_Icc'
      (div_le_div₀ (hx0.le.trans hxx) hxx hθ0 hθθ) ?_ fun z hz w hw hzw => ?_
    · exact hp.comp ((continuousOn_id.mul hA).prodMk hA) fun z hz =>
        shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz
    · have := hsep _ (shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz) _
        (shocks_rayPoint_mem hx0 hxx hθ0 hθθ hw) hzw
      simpa only [hratio] using this
  · have hz := shocks_ratio_mem_Z hx0 hθ0 hs
    have hu := shocks_rayPoint_mem hx0 hxx hθ0 hθθ hz
    have hps : p s = p (s.1 / s.2 * shocksA xlo θlo (s.1 / s.2), shocksA xlo θlo (s.1 / s.2)) :=
      hconst s hs _ hu (by simp only [hratio])
    refine ⟨hps, ?_⟩
    dsimp only
    rw [← hps, eq_div_iff (hppos s hs).ne']
    exact he.clear s hs

/-- **No continuous equilibrium price is fully revealing.** If `X` and `Θ` are nondegenerate, a
continuous equilibrium price cannot be injective on `X × Θ` (it is constant on rays
`x/θ = z`, which contain more than one state). -/
theorem islands_eqm_not_injOn (hx0 : 0 < xlo) (hxx : xlo < xhi) (hθ0 : 0 < θlo)
    (hθθ : θlo < θhi) (hH : Assumption17_1H L H H' H'') (hV : Assumption17_1VR V V' V'')
    [IsFiniteMeasure ν] [∀ P, IsFiniteMeasure (κ P)] (he : IslandsEqm L H V p n κ ν)
    (hp : ContinuousOn p (Icc xlo xhi ×ˢ Icc θlo θhi)) :
    ¬ InjOn p (Icc xlo xhi ×ˢ Icc θlo θhi) := by
  obtain ⟨ρ, -, -, hρ⟩ := islands_eqm_price_of_ratio hx0 hxx.le hθ0 hθθ.le hH hV he hp
  intro hinj
  set r := min (xhi / xlo) (θhi / θlo)
  have hr1 : 1 < r := lt_min ((one_lt_div hx0).2 hxx) ((one_lt_div hθ0).2 hθθ)
  have hs : ((xlo, θlo) : ℝ × ℝ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi :=
    ⟨⟨le_rfl, hxx.le⟩, le_rfl, hθθ.le⟩
  have ht : ((xlo * r, θlo * r) : ℝ × ℝ) ∈ Icc xlo xhi ×ˢ Icc θlo θhi := by
    refine ⟨⟨by nlinarith, ?_⟩, by nlinarith, ?_⟩
    · calc xlo * r ≤ xlo * (xhi / xlo) := mul_le_mul_of_nonneg_left (min_le_left _ _) hx0.le
        _ = xhi := by field_simp
    · calc θlo * r ≤ θlo * (θhi / θlo) := mul_le_mul_of_nonneg_left (min_le_right _ _) hθ0.le
        _ = θhi := by field_simp
  have heq : ((xlo, θlo) : ℝ × ℝ) = (xlo * r, θlo * r) := by
    refine hinj hs ht ?_
    rw [(hρ _ hs).1, (hρ _ ht).1]
    simp only
    rw [mul_div_mul_right _ _ (by linarith : r ≠ 0)]
  have := congrArg Prod.fst heq
  simp only at this
  nlinarith

end StokeyLucasPrescott.FixedPointArguments
