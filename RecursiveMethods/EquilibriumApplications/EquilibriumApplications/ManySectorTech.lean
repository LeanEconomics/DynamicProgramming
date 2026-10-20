/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySector

/-!
# A many-sector model of stochastic growth: technology and Exercise 16.2(a)

SLP §16.2, pp. 481–482, with the technology of §10.3 (pp. 290–292). There are `l` capital goods
(`Fin l → ℝ`) and one consumption good. The history structure: `proj t : Z^{t+1} → Z^t` drops the
last shock and `ζ t : Z^t → Z` is the current shock `z_t`.

* `MsTech`: properties (a)–(c) of §10.3 for `Φ : X × Z → ℝ₊ × X` (nonempty, compact, convex,
  continuous — upper and lower hemicontinuity, sequential form — monotone in `x`, jointly convex),
  with `X` convex (Assumption 9.4).
* `msBeg`, `msY`: beginning-of-period capital and the production set
  `Y = {c ∈ S : ∃ x ∈ S^l, x₀ = x̂, (c_t, x_{t+1}) ∈ Φ(x_t, z_t) μ^t-a.e., all t}` (p. 482; "for all
  `z^t`" read as "a.e.", NOTE (iii)).
* `ms_convex_Y`, `ms_Y_sub_C`: Assumption 15.4, `Y ⊆ C`.
* With **free disposal of consumption** (`MsFreeDisposal`): `ms_Y_timeTrunc` (15.6) and
  `ms_Y_periodTrunc` (15.8′).
* With a plan producing a **uniformly positive** amount of consumption (`MsPositiveProduction`):
  `ms_interior_Y` (15.5).
* **Exercise 16.2(a), corrected** (`ex_16_2a`): under these two extra hypotheses `(C, u, Y)`
  satisfy Assumptions 15.1–15.7 and 15.8′–15.9′.
* **Counterexamples** (NOTE to Ex 16.2a): `msPhiEps` (`Φ = {c ≥ ε, c + y ≤ x + ε}`) satisfies
  (a)–(c) (`msPhiEps_tech`) but its `Y` is closed neither under time truncation nor under event
  truncation (`ex_16_2a_trunc_counterexample`); `msPhiZero` (`Φ ≡ {(0, 0)}`) satisfies (a)–(c) but
  its `Y = {0}` has empty interior (`ex_16_2a_interior_counterexample`).

**Corrections.**
* Properties (a)–(c) of §10.3 do not imply 15.6, 15.8′ (truncation needs free disposal of
  consumption) or 15.5 (an interior point needs a feasible plan with consumption bounded away from
  `0`); both are added as hypotheses, and the counterexamples show they are needed.
* "For all `z^t`" in the definition of `Y` must read "μ^t-a.e." (elements of `S` are classes).
* One consumption good (`M = 1`, see `ManySector`).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

variable {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] {μ : ∀ t, Measure (Ω t)}
  {Z : Type*} [TopologicalSpace Z] {l : ℕ}

/-- **Properties (a)–(c) of §10.3** for the technology `Φ(x, z) ⊆ ℝ₊ × X` (one consumption good,
`l` capital goods), with `X` convex. Continuity is upper plus lower hemicontinuity in sequential
form (Chapter 3). -/
structure MsTech (Xc : Set (Fin l → ℝ)) (Φ : (Fin l → ℝ) → Z → Set (ℝ × (Fin l → ℝ))) : Prop where
  convex_X : Convex ℝ Xc
  nonempty : ∀ x ∈ Xc, ∀ z, (Φ x z).Nonempty
  compact : ∀ x ∈ Xc, ∀ z, IsCompact (Φ x z)
  convex : ∀ x ∈ Xc, ∀ z, Convex ℝ (Φ x z)
  range : ∀ x z p, p ∈ Φ x z → 0 ≤ p.1 ∧ p.2 ∈ Xc
  uhc : ∀ (x : ℕ → Fin l → ℝ) (z : ℕ → Z) (x₀ : Fin l → ℝ) (z₀ : Z), (∀ n, x n ∈ Xc) →
    x₀ ∈ Xc → Tendsto x atTop (𝓝 x₀) → Tendsto z atTop (𝓝 z₀) →
    ∀ p : ℕ → ℝ × (Fin l → ℝ), (∀ n, p n ∈ Φ (x n) (z n)) →
      ∃ q ∈ Φ x₀ z₀, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (p ∘ φ) atTop (𝓝 q)
  lhc : ∀ (x : ℕ → Fin l → ℝ) (z : ℕ → Z) (x₀ : Fin l → ℝ) (z₀ : Z), (∀ n, x n ∈ Xc) →
    x₀ ∈ Xc → Tendsto x atTop (𝓝 x₀) → Tendsto z atTop (𝓝 z₀) →
    ∀ q ∈ Φ x₀ z₀, ∃ p : ℕ → ℝ × (Fin l → ℝ), (∀ n, p n ∈ Φ (x n) (z n)) ∧
      Tendsto p atTop (𝓝 q)
  mono : ∀ x x' z p, x ∈ Xc → x ≤ x' → p ∈ Φ x z → p ∈ Φ x' z
  jointConvex : ∀ x x' z p p' (θ : ℝ), 0 ≤ θ → θ ≤ 1 → p ∈ Φ x z → p' ∈ Φ x' z →
    θ • p + (1 - θ) • p' ∈ Φ (θ • x + (1 - θ) • x') z

/-- Beginning-of-period capital: `x₀ = x̂`, `x_{t+1}(z^{t+1}) = k_t(z^t)` (the capital chosen at
`t`). -/
def msBeg (proj : ∀ t, Ω (t + 1) → Ω t) (xhat : Fin l → ℝ) (k : ∀ t, Ω t → Fin l → ℝ) :
    ∀ t, Ω t → Fin l → ℝ
  | 0 => fun _ => xhat
  | t + 1 => fun ω => k t (proj t ω)

/-- The production set `Y` (p. 482): consumption plans `c` produced by a bounded measurable
capital plan `k` (`k_t` = end-of-period capital) from `x̂`, with `(c_t, k_t) ∈ Φ(x_t, z_t)` a.e. -/
def msY (μ : ∀ t, Measure (Ω t)) (proj : ∀ t, Ω (t + 1) → Ω t) (ζ : ∀ t, Ω t → Z)
    (Φ : (Fin l → ℝ) → Z → Set (ℝ × (Fin l → ℝ))) (xhat : Fin l → ℝ) :
    Set (LinftyTimeState μ) :=
  {c | ∃ k : ∀ t, Ω t → Fin l → ℝ, (∀ t, Measurable (k t)) ∧ (∃ B, ∀ t ω, ‖k t ω‖ ≤ B) ∧
    ∀ t, ∀ᵐ ω ∂μ t, (c t ω, k t ω) ∈ Φ (msBeg proj xhat k t ω) (ζ t ω)}

/-- **Free disposal of consumption**: `(c, y) ∈ Φ(x, z)`, `0 ≤ c′ ≤ c` imply `(c′, y) ∈ Φ(x, z)`. -/
def MsFreeDisposal (Φ : (Fin l → ℝ) → Z → Set (ℝ × (Fin l → ℝ))) : Prop :=
  ∀ x z c y c', (c, y) ∈ Φ x z → 0 ≤ c' → c' ≤ c → (c', y) ∈ Φ x z

/-- **Uniformly positive production**: some bounded measurable capital plan from `x̂` produces at
least `ε > 0` of consumption a.e. in every period. -/
def MsPositiveProduction (μ : ∀ t, Measure (Ω t)) (proj : ∀ t, Ω (t + 1) → Ω t)
    (ζ : ∀ t, Ω t → Z) (Φ : (Fin l → ℝ) → Z → Set (ℝ × (Fin l → ℝ))) (xhat : Fin l → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ k : ∀ t, Ω t → Fin l → ℝ, (∀ t, Measurable (k t)) ∧
    (∃ B, ∀ t ω, ‖k t ω‖ ≤ B) ∧ ∀ t, ∀ᵐ ω ∂μ t, (ε, k t ω) ∈ Φ (msBeg proj xhat k t ω) (ζ t ω)

variable {Xc : Set (Fin l → ℝ)} {Φ : (Fin l → ℝ) → Z → Set (ℝ × (Fin l → ℝ))}
  {proj : ∀ t, Ω (t + 1) → Ω t} {ζ : ∀ t, Ω t → Z} {xhat : Fin l → ℝ}

/-- With one firm, the aggregate technology is the firm's production set. -/
theorem ms_aggTech_unit {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] (Y : Set S) :
    aggTech (fun _ : Unit => Y) = Y := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

omit [∀ t, MeasurableSpace (Ω t)] in
/-- `msBeg` of a convex combination of capital plans. -/
theorem msBeg_combo (k k' : ∀ t, Ω t → Fin l → ℝ) (θ : ℝ) (t : ℕ) (ω : Ω t) :
    msBeg proj xhat (fun t ω => θ • k t ω + (1 - θ) • k' t ω) t ω =
      θ • msBeg proj xhat k t ω + (1 - θ) • msBeg proj xhat k' t ω := by
  cases t with
  | zero => simp only [msBeg, ← add_smul]; simp
  | succ t => rfl

/-- `Y ⊆ C`. -/
theorem ms_Y_sub_C (hT : MsTech Xc Φ) : msY μ proj ζ Φ xhat ⊆ msC μ := by
  rintro c ⟨k, -, -, hk⟩ t
  filter_upwards [hk t] with ω h
  exact (hT.range _ _ _ h).1

/-- **Assumption 15.4**: `Y` is convex (joint convexity (c) of `Φ`). -/
theorem ms_convex_Y (hT : MsTech Xc Φ) : Convex ℝ (msY μ proj ζ Φ xhat) := by
  rintro c ⟨k, hkm, ⟨B, hB⟩, hk⟩ c' ⟨k', hkm', ⟨B', hB'⟩, hk'⟩ a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  refine ⟨fun t ω => a • k t ω + (1 - a) • k' t ω, fun t => ((hkm t).const_smul a).add
    ((hkm' t).const_smul (1 - a)), ⟨a * B + (1 - a) * B', fun t ω => ?_⟩, fun t => ?_⟩
  · calc ‖a • k t ω + (1 - a) • k' t ω‖ ≤ ‖a • k t ω‖ + ‖(1 - a) • k' t ω‖ := norm_add_le _ _
      _ = a * ‖k t ω‖ + (1 - a) * ‖k' t ω‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * B + (1 - a) * B' := add_le_add (mul_le_mul_of_nonneg_left (hB t ω) ha)
          (mul_le_mul_of_nonneg_left (hB' t ω) hb)
  · filter_upwards [hk t, hk' t, Lp.coeFn_add (a • c t) ((1 - a) • c' t), Lp.coeFn_smul a (c t),
      Lp.coeFn_smul (1 - a) (c' t)] with ω h1 h2 e1 e2 e3
    have := hT.jointConvex _ _ _ _ _ a ha (by linarith) h1 h2
    rw [msBeg_combo]
    rw [ms_coord_add, ms_coord_smul, ms_coord_smul, e1, Pi.add_apply, e2, e3, Pi.smul_apply,
      Pi.smul_apply]
    simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

/-- **Assumption 15.6 for `Y`, with free disposal**: truncations keep the capital plan. -/
theorem ms_Y_timeTrunc (hT : MsTech Xc Φ) (hfd : MsFreeDisposal Φ) {c : LinftyTimeState μ}
    (hc : c ∈ msY μ proj ζ Φ xhat) (T : ℕ) : linftyTimeTrunc T c ∈ msY μ proj ζ Φ xhat := by
  obtain ⟨k, hkm, hkB, hk⟩ := hc
  refine ⟨k, hkm, hkB, fun t => ?_⟩
  rw [linftyTimeTrunc_apply]
  split_ifs
  · exact hk t
  · filter_upwards [hk t, Lp.coeFn_zero ℝ ⊤ (μ t)] with ω h1 h2
    rw [h2]
    exact hfd _ _ _ _ _ h1 le_rfl (hT.range _ _ _ h1).1

/-- **Assumption 15.8′ for `Y`, with free disposal**: event truncations keep the capital plan. -/
theorem ms_Y_periodTrunc (hT : MsTech Xc Φ) (hfd : MsFreeDisposal Φ) {c : LinftyTimeState μ}
    (hc : c ∈ msY μ proj ζ Φ xhat) (s : ℕ) {A : Set (Ω s)} (hA : MeasurableSet A) :
    linftyPeriodTrunc s A c ∈ msY μ proj ζ Φ xhat := by
  obtain ⟨k, hkm, hkB, hk⟩ := hc
  refine ⟨k, hkm, hkB, fun t => ?_⟩
  by_cases hts : t = s
  · subst hts
    rw [linftyPeriodTrunc_apply_self]
    filter_upwards [hk t, coeFn_linftyRestrict hA.compl (c t)] with ω h1 h2
    rw [linftyTrunc, h2]
    by_cases hω : ω ∈ Aᶜ
    · rw [indicator_of_mem hω]; exact h1
    · rw [indicator_of_notMem hω]
      exact hfd _ _ _ _ _ h1 le_rfl (hT.range _ _ _ h1).1
  · rw [linftyPeriodTrunc_apply_of_ne hts]
    exact hk t

omit [TopologicalSpace Z] in
/-- **Assumption 15.5 under uniformly positive production and free disposal**: the ball of
radius `ε/2` about `(ε/2)𝟙` lies in `Y`. -/
theorem ms_interior_Y [∀ t, IsProbabilityMeasure (μ t)] (hfd : MsFreeDisposal Φ)
    (hpos : MsPositiveProduction μ proj ζ Φ xhat) : (interior (msY μ proj ζ Φ xhat)).Nonempty := by
  obtain ⟨ε, hε, k, hkm, hkB, hk⟩ := hpos
  refine ⟨(ε / 2) • msOne μ, interior_maximal (t := Metric.ball ((ε / 2) • msOne μ) (ε / 2)) ?_
    Metric.isOpen_ball (Metric.mem_ball_self (half_pos hε))⟩
  intro c hc
  rw [mem_ball_iff_norm] at hc
  refine ⟨k, hkm, hkB, fun t => ?_⟩
  filter_upwards [hk t, ms_ae_abs_le (c - (ε / 2) • msOne μ) t,
    Lp.coeFn_sub (c t) ((ε / 2) • msOne μ t), Lp.coeFn_smul (ε / 2) (msOne μ t),
    msOne_ae (μ := μ) t] with ω h1 h2 e1 e2 e3
  rw [ms_coord_sub, ms_coord_smul, e1, Pi.sub_apply, e2, Pi.smul_apply, e3, smul_eq_mul,
    mul_one] at h2
  have h3 := (abs_lt.1 (h2.trans_lt hc))
  exact hfd _ _ _ _ _ h1 (by linarith [h3.1]) (by linarith [h3.2])

/-- **Exercise 16.2(a), corrected**: if `Φ` satisfies (a)–(c) of §10.3, has free disposal of
consumption, and some plan produces a uniformly positive amount of consumption, then `(C, u, Y)`
satisfy Assumptions 15.1–15.7 and 15.8′–15.9′. -/
theorem ex_16_2a [∀ t, IsProbabilityMeasure (μ t)] {U : ℝ → ℝ} {β : ℝ} (H : ManySectorHyp U β)
    (hT : MsTech Xc Φ) (hfd : MsFreeDisposal Φ) (hpos : MsPositiveProduction μ proj ζ Φ xhat) :
    Assumption15_1 (fun _ : Unit => msC μ) ∧
      Assumption15_2 (fun _ : Unit => msC μ) (fun _ => msU μ β U) ∧
      Assumption15_3 (fun _ : Unit => msC μ) (fun _ => msU μ β U) ∧
      Assumption15_4 (fun _ : Unit => msY μ proj ζ Φ xhat) ∧
      Assumption15_5 (LinftyTimeState μ) (fun _ : Unit => msY μ proj ζ Φ xhat) ∧
      Assumption15_6_timeState (fun _ : Unit => msC μ) (fun _ : Unit => msY μ proj ζ Φ xhat) ∧
      Assumption15_7_timeState (fun _ : Unit => msC μ) (fun _ => msU μ β U) ∧
      Assumption15_8' μ (fun _ : Unit => msC μ) (fun _ : Unit => msY μ proj ζ Φ xhat) ∧
      Assumption15_9' μ (fun _ : Unit => msC μ) (fun _ => msU μ β U) := by
  obtain ⟨h1, h2, h3, h7, h9, hCT, hCP⟩ := ex_16_2a_consumer (μ := μ) H
  refine ⟨h1, h2, h3, ?_, Or.inl ?_, ⟨fun _ c hc => Eventually.of_forall fun T => hCT c hc T,
    fun _ c hc => Eventually.of_forall fun T => ms_Y_timeTrunc hT hfd hc T⟩, h7,
    ⟨fun _ s c hc A hA => Eventually.of_forall fun n => hCP c hc s (A n) (hA.measurableSet n),
      fun _ s c hc A hA => Eventually.of_forall fun n =>
        ms_Y_periodTrunc hT hfd hc s (hA.measurableSet n)⟩, h9⟩
  · rw [Assumption15_4, ms_aggTech_unit]
    exact ms_convex_Y hT
  · rw [ms_aggTech_unit]
    exact ms_interior_Y hfd hpos

/-! ### Counterexamples -/

/-- The technology `Φ(x, z) = {(c, y) : c ≥ ε, y ≥ 0, c + y ≤ x + ε}` (one capital good,
`f(x) = x`): no free disposal of consumption. -/
def msPhiEps (ε : ℝ) (x : Fin 1 → ℝ) (_z : Unit) : Set (ℝ × (Fin 1 → ℝ)) :=
  {p | ε ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 0 ≤ x 0 + ε}

/-- `Fin 1 → ℝ` is determined by its value at `0`. -/
theorem fin1_eq_const (y : Fin 1 → ℝ) : y = fun _ => y 0 := funext fun i => by
  rw [Subsingleton.elim i 0]

/-- The graph `{(x, p) : p ∈ Φ_ε(x)}` is closed. -/
theorem msPhiEps_graph_closed (ε : ℝ) :
    IsClosed {r : (Fin 1 → ℝ) × (ℝ × (Fin 1 → ℝ)) | r.2 ∈ msPhiEps ε r.1 ()} :=
  (isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter
    ((isClosed_le continuous_const (continuous_snd.comp continuous_snd)).inter
      (isClosed_le ((continuous_fst.comp continuous_snd).add
        ((continuous_apply 0).comp (continuous_snd.comp continuous_snd)))
        (((continuous_apply 0).comp continuous_fst).add continuous_const)))

/-- `Φ_ε(x) ⊆ [ε, R + ε] × [0, R]` when `x₀ ≤ R`. -/
theorem msPhiEps_sub_box {ε : ℝ} {x : Fin 1 → ℝ} {R : ℝ} (hR : x 0 ≤ R) :
    msPhiEps ε x () ⊆ Icc ε (R + ε) ×ˢ (univ.pi fun _ => Icc 0 R) := by
  rintro p ⟨h1, h2, h3⟩
  have h20 : (0 : ℝ) ≤ p.2 0 := h2 0
  refine ⟨⟨h1, by linarith⟩, fun i _ => ?_⟩
  rw [Subsingleton.elim i 0]
  exact ⟨h20, by linarith⟩

/-- **`Φ_ε` satisfies properties (a)–(c) of §10.3** (on `X = ℝ₊`, for `ε > 0`). -/
theorem msPhiEps_tech {ε : ℝ} (hε : 0 < ε) : MsTech {x : Fin 1 → ℝ | 0 ≤ x} (msPhiEps ε) where
  convex_X := convex_Ici 0
  nonempty x hx _ := ⟨(ε, 0), le_rfl, le_rfl, by
    have : (0 : ℝ) ≤ x 0 := hx 0
    simp only [Pi.zero_apply, add_zero]; linarith⟩
  compact x _ _ :=
    (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)).of_isClosed_subset
      ((msPhiEps_graph_closed ε).preimage (Continuous.prodMk continuous_const continuous_id))
      (msPhiEps_sub_box (R := x 0) le_rfl)
  convex x _ _ := by
    rintro p ⟨a1, a2, a3⟩ q ⟨b1, b2, b3⟩ a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · change ε ≤ a * p.1 + b * q.1
      nlinarith
    · change 0 ≤ a • p.2 + b • q.2
      exact add_nonneg (smul_nonneg ha a2) (smul_nonneg hb b2)
    · change a * p.1 + b * q.1 + (a * p.2 0 + b * q.2 0) ≤ x 0 + ε
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_le_mul_of_nonneg_left a3 ha, mul_le_mul_of_nonneg_left b3 hb]
  range x _ p hp := ⟨hε.le.trans hp.1, hp.2.1⟩
  uhc x z x₀ z₀ hx hx₀ hxt hzt p hp := by
    obtain ⟨R, hR⟩ : ∃ R, ∀ n, x n 0 ≤ R := by
      obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto _
        (((continuous_apply 0).tendsto x₀).comp hxt)).bddAbove
      exact ⟨R, fun n => hR (mem_range_self n)⟩
    obtain ⟨q, -, φ, hφ, hq⟩ := (isCompact_Icc.prod (isCompact_univ_pi fun _ =>
      isCompact_Icc)).tendsto_subseq (x := p) fun n => msPhiEps_sub_box (hR n) (hp n)
    refine ⟨q, ?_, φ, hφ, hq⟩
    have hlim : Tendsto (fun n => (x (φ n), p (φ n))) atTop (𝓝 (x₀, q)) :=
      (hxt.comp hφ.tendsto_atTop).prodMk_nhds hq
    have := (msPhiEps_graph_closed ε).mem_of_tendsto hlim (Eventually.of_forall fun n => by
      have := hp (φ n)
      rwa [show z (φ n) = () from rfl] at this)
    exact this
  lhc x z x₀ z₀ hx hx₀ hxt hzt q hq := by
    obtain ⟨q1, q2, q3⟩ := hq
    have q20 : (0 : ℝ) ≤ q.2 0 := q2 0
    have hxn : ∀ n, (0 : ℝ) ≤ x n 0 := fun n => hx n 0
    rcases (show (0 : ℝ) ≤ x₀ 0 from hx₀ 0).lt_or_eq with hpos | hzero
    · set lam : ℕ → ℝ := fun n => min 1 (x n 0 / x₀ 0) with hlam
      have hlam0 : ∀ n, 0 ≤ lam n := fun n => le_min zero_le_one (div_nonneg (hxn n) hpos.le)
      have hlamx : ∀ n, lam n * x₀ 0 ≤ x n 0 := fun n => by
        calc lam n * x₀ 0 ≤ x n 0 / x₀ 0 * x₀ 0 :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
          _ = x n 0 := div_mul_cancel₀ _ hpos.ne'
      refine ⟨fun n => (ε + lam n * (q.1 - ε), lam n • q.2), fun n => ⟨?_, ?_, ?_⟩, ?_⟩
      · change ε ≤ ε + lam n * (q.1 - ε)
        nlinarith [hlam0 n]
      · change 0 ≤ lam n • q.2
        exact smul_nonneg (hlam0 n) q2
      · change ε + lam n * (q.1 - ε) + lam n * q.2 0 ≤ x n 0 + ε
        nlinarith [hlam0 n, hlamx n]
      · have hl : Tendsto lam atTop (𝓝 1) := by
          have := ((((continuous_apply 0).tendsto x₀).comp hxt).div_const (x₀ 0)).min
            (tendsto_const_nhds (x := (1 : ℝ)))
          rw [div_self hpos.ne', min_self] at this
          simpa [hlam, min_comm] using this
        have h1 := (tendsto_const_nhds (x := ε)).add (hl.mul_const (q.1 - ε))
        have h2 := hl.smul_const q.2
        simp only [one_mul, one_smul, add_sub_cancel] at h1 h2
        exact h1.prodMk_nhds h2
    · have hq1 : q.1 = ε := by linarith
      have hq20 : q.2 0 = 0 := by linarith
      refine ⟨fun _ => q, fun n => ⟨q1, q2, ?_⟩, tendsto_const_nhds⟩
      rw [hq1, hq20]
      linarith [hxn n]
  mono x x' _ p _ hxx' hp := ⟨hp.1, hp.2.1, hp.2.2.trans (by
    have : x 0 ≤ x' 0 := hxx' 0
    linarith)⟩
  jointConvex x x' _ p p' θ h0 h1 hp hp' := by
    obtain ⟨a1, a2, a3⟩ := hp
    obtain ⟨b1, b2, b3⟩ := hp'
    refine ⟨?_, ?_, ?_⟩
    · change ε ≤ θ * p.1 + (1 - θ) * p'.1
      nlinarith
    · change 0 ≤ θ • p.2 + (1 - θ) • p'.2
      exact add_nonneg (smul_nonneg h0 a2) (smul_nonneg (by linarith) b2)
    · change θ * p.1 + (1 - θ) * p'.1 + (θ * p.2 0 + (1 - θ) * p'.2 0) ≤
        θ * x 0 + (1 - θ) * x' 0 + ε
      nlinarith [mul_le_mul_of_nonneg_left a3 h0,
        mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ 1 - θ)]

/-- The probability space `([0, 1], Lebesgue)` used in the counterexamples. -/
noncomputable def msUnitMeasure : Measure ℝ := MeasureTheory.volume.restrict (Icc 0 1)

/-- `msUnitMeasure` is a probability measure. -/
theorem msUnitMeasure_prob : IsProbabilityMeasure msUnitMeasure :=
  ⟨by simp [msUnitMeasure, Real.volume_Icc]⟩

/-- `μ([0, 1/(n+1)]) = 1/(n+1)`. -/
theorem msUnitMeasure_Icc (n : ℕ) :
    msUnitMeasure (Icc 0 (1 / ((n : ℝ) + 1))) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  rw [msUnitMeasure, Measure.restrict_apply measurableSet_Icc,
    Icc_inter_Icc, max_self, min_eq_left hle, Real.volume_Icc, sub_zero]

/-- `A_n = [0, 1/(n+1)] ↓ 0` with `μ(A_n) > 0`. -/
theorem msUnitNull : LinftyNullSeq msUnitMeasure fun n => Icc (0 : ℝ) (1 / ((n : ℝ) + 1)) where
  measurableSet _ := measurableSet_Icc
  antitone m n hmn := Icc_subset_Icc le_rfl (one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hmn 1))
  tendsto_measure := by
    simp only [msUnitMeasure_Icc]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat

/-- The constant plan `a𝟙` in the counterexample space. -/
noncomputable def msUnitConst (a : ℝ) : LinftyTimeState (fun _ : ℕ => msUnitMeasure) :=
  have : IsProbabilityMeasure msUnitMeasure := msUnitMeasure_prob
  a • msOne (fun _ : ℕ => msUnitMeasure)

/-- `(a𝟙)_t = a` a.e. -/
theorem msUnitConst_ae (a : ℝ) (t : ℕ) : ∀ᵐ ω ∂msUnitMeasure, msUnitConst a t ω = a := by
  have : IsProbabilityMeasure msUnitMeasure := msUnitMeasure_prob
  filter_upwards [Lp.coeFn_smul a (msOne (fun _ : ℕ => msUnitMeasure) t),
    msOne_ae (μ := fun _ : ℕ => msUnitMeasure) t] with ω e1 e2
  change (a • msOne (fun _ : ℕ => msUnitMeasure)) t ω = a
  rw [ms_coord_smul, e1, Pi.smul_apply, e2, smul_eq_mul, mul_one]

/-- In the counterexample economy every `c ∈ Y` has `c_t ≥ ε` a.e. -/
theorem msPhiEps_Y_ge {ε : ℝ} {c : LinftyTimeState (fun _ : ℕ => msUnitMeasure)}
    (hc : c ∈ msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) (msPhiEps ε) 0)
    (t : ℕ) : ∀ᵐ ω ∂msUnitMeasure, ε ≤ c t ω := by
  obtain ⟨k, -, -, hk⟩ := hc
  filter_upwards [hk t] with ω h
  exact h.1

/-- In the counterexample economy, `ε𝟙 ∈ Y` (with zero capital). -/
theorem msPhiEps_one_mem {ε : ℝ} :
    msUnitConst ε ∈
      msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) (msPhiEps ε) 0 := by
  refine ⟨fun _ _ => 0, fun _ => measurable_const, ⟨0, fun _ _ => by simp⟩, fun t => ?_⟩
  filter_upwards [msUnitConst_ae ε t] with ω e
  rw [e]
  refine ⟨le_rfl, le_rfl, ?_⟩
  cases t <;> simp [msBeg]

/-- **Counterexample to Ex 16.2a (truncation)**: `Φ_ε` (`ε = 1`) satisfies (a)–(c) of §10.3, but its
production set contains `𝟙` and no time truncation `𝟙ᵀ` (Assumption 15.6 fails) and no event
truncation `𝟙^{A_n}` with `A_n = [0, 1/(n+1)] ↓ 0` in period `0` (Assumption 15.8′ fails). -/
theorem ex_16_2a_trunc_counterexample :
    MsTech {x : Fin 1 → ℝ | 0 ≤ x} (msPhiEps 1) ∧
      msUnitConst 1 ∈
        msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) (msPhiEps 1) 0 ∧
      (∀ T, linftyTimeTrunc T (msUnitConst 1) ∉
        msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) (msPhiEps 1) 0) ∧
      ∀ n : ℕ, linftyPeriodTrunc 0 (Icc (0 : ℝ) (1 / ((n : ℝ) + 1))) (msUnitConst 1) ∉
        msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) (msPhiEps 1) 0 := by
  have : IsProbabilityMeasure msUnitMeasure := msUnitMeasure_prob
  refine ⟨msPhiEps_tech one_pos, msPhiEps_one_mem, fun T hT => ?_, fun n hn => ?_⟩
  · have h := msPhiEps_Y_ge hT (T + 1)
    simp only [linftyTimeTrunc_apply, show ¬ (T + 1 ≤ T) by omega, ↓reduceIte] at h
    have h0 := Lp.coeFn_zero ℝ ⊤ msUnitMeasure
    obtain ⟨ω, h1, h2⟩ := (h.and h0).exists
    rw [h2] at h1
    exact absurd h1 (by norm_num)
  · have h := msPhiEps_Y_ge hn 0
    rw [linftyPeriodTrunc_apply_self, linftyTrunc] at h
    have hA : MeasurableSet (Icc (0 : ℝ) (1 / ((n : ℝ) + 1))) := measurableSet_Icc
    have hnot : ∀ᵐ ω ∂msUnitMeasure, ω ∉ Icc (0 : ℝ) (1 / ((n : ℝ) + 1)) := by
      filter_upwards [h, coeFn_linftyRestrict (μ := msUnitMeasure) hA.compl
        (msUnitConst 1 0)] with ω h1 h2 hω
      rw [h2, indicator_of_notMem (by simpa using hω)] at h1
      exact absurd h1 (by norm_num)
    have h0 := measure_eq_zero_iff_ae_notMem.2 hnot
    rw [msUnitMeasure_Icc, ENNReal.ofReal_eq_zero] at h0
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- The technology `Φ ≡ {(0, 0)}`: nothing is ever consumed. -/
def msPhiZero (_x : Fin 1 → ℝ) (_z : Unit) : Set (ℝ × (Fin 1 → ℝ)) := {(0, 0)}

/-- **`Φ ≡ {(0, 0)}` satisfies (a)–(c) of §10.3** (on `X = ℝ₊`). -/
theorem msPhiZero_tech : MsTech {x : Fin 1 → ℝ | 0 ≤ x} msPhiZero where
  convex_X := convex_Ici 0
  nonempty _ _ _ := singleton_nonempty _
  compact _ _ _ := isCompact_singleton
  convex _ _ _ := convex_singleton _
  range _ _ p hp := by
    rw [msPhiZero, mem_singleton_iff] at hp
    subst hp
    exact ⟨le_rfl, (le_rfl : (0 : Fin 1 → ℝ) ≤ 0)⟩
  uhc _ _ _ _ _ _ _ _ p hp := ⟨(0, 0), rfl, id, strictMono_id, by
    have : p = fun _ => (0, 0) := funext hp
    rw [this]
    exact tendsto_const_nhds⟩
  lhc _ _ _ _ _ _ _ _ q hq := ⟨fun _ => q, fun _ => hq, tendsto_const_nhds⟩
  mono _ _ _ _ _ _ hp := hp
  jointConvex _ _ _ p p' θ _ _ hp hp' := by
    rw [msPhiZero, mem_singleton_iff] at hp hp' ⊢
    subst hp hp'
    simp

/-- **Counterexample to Ex 16.2a (interior point)**: `Φ ≡ {(0, 0)}` satisfies (a)–(c) of §10.3, but
its production set has empty interior (Assumption 15.5 fails). -/
theorem ex_16_2a_interior_counterexample :
    MsTech {x : Fin 1 → ℝ | 0 ≤ x} msPhiZero ∧
      interior (msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) msPhiZero 0) =
        ∅ := by
  have : IsProbabilityMeasure msUnitMeasure := msUnitMeasure_prob
  refine ⟨msPhiZero_tech, eq_empty_iff_forall_notMem.2 fun y hy => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  have hzero : ∀ c ∈ msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) msPhiZero 0,
      ∀ᵐ ω ∂msUnitMeasure, c 0 ω = 0 := by
    rintro c ⟨k, -, -, hk⟩
    filter_upwards [hk 0] with ω h
    exact (Prod.mk.inj h).1
  have h1 := hzero y (interior_subset hy)
  have hmem : y + (r / 2) • msOne (fun _ : ℕ => msUnitMeasure) ∈
      msY (fun _ : ℕ => msUnitMeasure) (fun _ => id) (fun _ _ => ()) msPhiZero 0 := hball (by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    calc r / 2 * ‖msOne (fun _ : ℕ => msUnitMeasure)‖ ≤ r / 2 * 1 :=
          mul_le_mul_of_nonneg_left norm_msOne_le (half_pos hr).le
      _ < r := by linarith)
  have h2 := hzero _ hmem
  have h3 := ms_combo_one_ae (μ := fun _ : ℕ => msUnitMeasure) (r / 2) 1 y 0
  obtain ⟨ω, e1, e2, e3⟩ := (h1.and (h2.and h3)).exists
  have : (y + (r / 2) • msOne (fun _ : ℕ => msUnitMeasure)) 0 ω = r / 2 := by
    have e4 : y + (r / 2) • msOne (fun _ : ℕ => msUnitMeasure) =
        (r / 2) • msOne (fun _ : ℕ => msUnitMeasure) + (1 : ℝ) • y := by
      rw [one_smul, add_comm]
    rw [e4, e3, e1, mul_zero, add_zero]
  linarith

end StokeyLucasPrescott.EquilibriumApplications
