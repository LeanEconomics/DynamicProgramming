/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManyConsumersOperator

/-!
# Counterexamples for §16.7

SLP §16.7, pp. 496–499. One technology serves all counterexamples (`l = p = 1`):
`Φ(κ) = {(γ, y) ∈ ℝ²₊ : γ ≤ 1 − e^{−κ}, y ≤ 2κ}` (`mcExPhi`), a box technology (`mcBox`,
`mcBox_tech`), satisfying (T1)–(T7) (`mcExPhi_tech`; `M = ℝ₊` and `mcEx_mem_interior`). The
aggregator is `W(x, z) = min(x, 1) + z/2` (`mcExW`; (W1)–(W5) with `β = 1/2`, `mcExW_agg`), with
fixed point `u(c) = Σ_t (1/2)ᵗ min(c_t, 1)` (`mcExU`, `mcExU_fixed`).

* `ex_16_7a_counterexample`: `Y(1)` is not closed: `cⁿ_t = 1 − e^{−min(2ᵗ, n+1)} ∈ Y(1)`
  (`mcExCn_mem`) converges to `c_t = 1 − e^{−2ᵗ}` (`mcExCn_tendsto`), and `c ∉ Y(1)`
  (`mcExC_not_mem`) since it needs `k_t ≥ 2ᵗ`; `c ∈ Y′(1)` (`mcExC_mem_unb`).
* `ex_16_7b_counterexample`: `I = 2`, `W₀ ≡ 0`, `W₁ = W`: the zero allocation maximises `Σθᵢuᵢ` for
  `θ = (1, 0)` but is not Pareto optimal.
* `ex_16_7c_counterexample`: `I = 1`: `z = v(1, 1)` satisfies `v(1, θ) ≥ θ · z` for all `θ ∈ Δ¹` but
  `z ∉ U(1)` (`mcEx_strict`: no plan in `Y(1)` attains the supremum); hence `U(1)` is not closed.
* `ex_16_7d_counterexample`: `f(κ′) = min(|κ′ − 1|, 1) ∈ F`, `κ = 1`: the constraint set is not
  convex.
* `ex_16_7e_counterexample`: `I = 2`, `f(κ′, θ′) = max(θ′₀ − |κ′ − 1|, 0) ∈ F`: `Tf ∉ F`
  (`Tf(·, e₀)` jumps by at least `1/2` at `κ = 1/2`).
* `ex_16_7f_hint_counterexample`: `I = 2`, `g(θ) = 10|θ₀ − ½| ∈ F`: `𝒰 = {0}`, `B = [0, a]²`, but
  `(2a, 0) ∈ 𝒰ᵃ` for `0 < a ≤ 5`.
* `ex_16_7f_counterexample`: the same `g`: `‖(g + 1) − g‖ = 1` but
  `T(g + 1)(1, e₀) ≥ Tg(1, e₀) + 1`,
  so `T` is not a contraction on `F` with modulus `β = 1/2`, nor with any modulus `< 1`.

**On the transcription's NOTEs.** All NOTEs checked here are confirmed, with the counterexamples
they propose (for 16.7c with `β = 1/2`). Two are sharpened: for (e), `T(F) ⊄ F` (not only "lower
hemicontinuity is not addressed"); for (f), the contraction claim itself fails on `F`, not only the
hint.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {l p : ℕ}

/-! ### Box technologies -/

/-- A **box technology** `Φ(κ) = [0, a(κ)] × [0, b(κ)]`. -/
def mcBox (a : (Fin p → ℝ) → (Fin l → ℝ)) (b : (Fin p → ℝ) → (Fin p → ℝ)) (κ : Fin p → ℝ) :
    Set ((Fin l → ℝ) × (Fin p → ℝ)) :=
  {q | 0 ≤ q.1 ∧ q.1 ≤ a κ ∧ 0 ≤ q.2 ∧ q.2 ≤ b κ}

/-- **A box technology satisfies (T1)–(T7)** when `a, b ≥ 0` are continuous, nondecreasing and
concave on `ℝᵖ₊`, `M` has an interior point, and `a ≫ 0` on `int M`. -/
theorem mcBox_tech {a : (Fin p → ℝ) → (Fin l → ℝ)} {b : (Fin p → ℝ) → (Fin p → ℝ)}
    (ha : ContinuousOn a (Ici 0)) (hb : ContinuousOn b (Ici 0))
    (ha0 : ∀ κ, 0 ≤ κ → 0 ≤ a κ) (hb0 : ∀ κ, 0 ≤ κ → 0 ≤ b κ)
    (ham : ∀ κ κ', 0 ≤ κ' → κ' ≤ κ → a κ' ≤ a κ) (hbm : ∀ κ κ', 0 ≤ κ' → κ' ≤ κ → b κ' ≤ b κ)
    (hac : ∀ κ κ', 0 ≤ κ → 0 ≤ κ' → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • a κ + (1 - θ) • a κ' ≤ a (θ • κ + (1 - θ) • κ'))
    (hbc : ∀ κ κ', 0 ≤ κ → 0 ≤ κ' → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • b κ + (1 - θ) • b κ' ≤ b (θ • κ + (1 - θ) • κ'))
    (hint : (interior (mcM (mcBox a b))).Nonempty)
    (hpos : ∀ κ ∈ interior (mcM (mcBox a b)), ∀ m, 0 < a κ m) :
    ManyConsumersTech (mcBox a b) := by
  have hlims : ∀ κs : ℕ → Fin p → ℝ, ∀ κ, (∀ n, 0 ≤ κs n) → Tendsto κs atTop (𝓝 κ) →
      0 ≤ κ ∧ Tendsto (fun n => a (κs n)) atTop (𝓝 (a κ)) ∧
        Tendsto (fun n => b (κs n)) atTop (𝓝 (b κ)) := fun κs κ hκs hlim => by
    have hκ : 0 ≤ κ := ge_of_tendsto' hlim hκs
    have hin : Tendsto κs atTop (𝓝[Ici 0] κ) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hκs⟩
    exact ⟨hκ, (ha κ hκ).tendsto.comp hin, (hb κ hκ).tendsto.comp hin⟩
  have hgc : ∀ κ κ', 0 ≤ κ → 0 ≤ κ' → ∀ q ∈ mcBox a b κ, ∀ q' ∈ mcBox a b κ', ∀ θ : ℝ,
      0 ≤ θ → θ ≤ 1 → θ • q + (1 - θ) • q' ∈ mcBox a b (θ • κ + (1 - θ) • κ') := by
    intro κ κ' hκ hκ' q hq q' hq' θ h0 h1
    have h1' : 0 ≤ 1 - θ := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst]
      exact add_nonneg (smul_nonneg h0 hq.1) (smul_nonneg h1' hq'.1)
    · simp only [Prod.fst_add, Prod.smul_fst]
      exact (add_le_add (smul_le_smul_of_nonneg_left hq.2.1 h0)
        (smul_le_smul_of_nonneg_left hq'.2.1 h1')).trans (hac κ κ' hκ hκ' θ h0 h1)
    · simp only [Prod.snd_add, Prod.smul_snd]
      exact add_nonneg (smul_nonneg h0 hq.2.2.1) (smul_nonneg h1' hq'.2.2.1)
    · simp only [Prod.snd_add, Prod.smul_snd]
      exact (add_le_add (smul_le_smul_of_nonneg_left hq.2.2.2 h0)
        (smul_le_smul_of_nonneg_left hq'.2.2.2 h1')).trans (hbc κ κ' hκ hκ' θ h0 h1)
  refine ⟨fun κ _ q hq => ⟨hq.1, hq.2.2.1⟩, fun κ hκ => ⟨(0, 0), le_rfl, ha0 κ hκ, le_rfl,
    hb0 κ hκ⟩, ?_, ?_, fun κ _ => ?_, fun κ hκ => ?_, ?_, ?_, hgc, hint, ?_⟩
  · intro κs κ hκs hlim qs hqs
    obtain ⟨-, hga, hgb⟩ := hlims κs κ hκs hlim
    obtain ⟨A, hA⟩ := hga.bddAbove_range
    obtain ⟨B, hB⟩ := hgb.bddAbove_range
    have hmem : ∀ n, qs n ∈ Icc (0 : Fin l → ℝ) A ×ˢ Icc (0 : Fin p → ℝ) B := fun n =>
      ⟨⟨(hqs n).1, (hqs n).2.1.trans (hA ⟨n, rfl⟩)⟩,
        ⟨(hqs n).2.2.1, (hqs n).2.2.2.trans (hB ⟨n, rfl⟩)⟩⟩
    obtain ⟨q, -, φ, hφ, hq⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
    have h1 : Tendsto (fun n => (qs (φ n)).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hq
    have h2 : Tendsto (fun n => (qs (φ n)).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hq
    exact ⟨q, ⟨ge_of_tendsto' h1 fun n => (hqs (φ n)).1,
      le_of_tendsto_of_tendsto' h1 (hga.comp hφ.tendsto_atTop) fun n => (hqs (φ n)).2.1,
      ge_of_tendsto' h2 fun n => (hqs (φ n)).2.2.1,
      le_of_tendsto_of_tendsto' h2 (hgb.comp hφ.tendsto_atTop) fun n => (hqs (φ n)).2.2.2⟩,
      φ, hφ, hq⟩
  · intro κs κ hκs hlim q hq
    obtain ⟨-, hga, hgb⟩ := hlims κs κ hκs hlim
    refine ⟨fun n => ((fun m => min (q.1 m) (a (κs n) m)), fun m => min (q.2 m) (b (κs n) m)),
      Eventually.of_forall fun n => ⟨fun m => le_min (hq.1 m) (ha0 _ (hκs n) m),
        fun m => min_le_right _ _, fun m => le_min (hq.2.2.1 m) (hb0 _ (hκs n) m),
        fun m => min_le_right _ _⟩, ?_⟩
    have hl : Tendsto (fun n => ((fun m => min (q.1 m) (a (κs n) m)),
        fun m => min (q.2 m) (b (κs n) m))) atTop
        (𝓝 ((fun m => min (q.1 m) (a κ m)), fun m => min (q.2 m) (b κ m))) :=
      (tendsto_pi_nhds.2 fun m => tendsto_const_nhds.min (((continuous_apply m).tendsto _).comp
        hga)).prodMk_nhds (tendsto_pi_nhds.2 fun m => tendsto_const_nhds.min
          (((continuous_apply m).tendsto _).comp hgb))
    have e : ((fun m => min (q.1 m) (a κ m)), fun m => min (q.2 m) (b κ m)) = q :=
      Prod.ext (funext fun m => min_eq_left (hq.2.1 m)) (funext fun m => min_eq_left (hq.2.2.2 m))
    rwa [e] at hl
  · have e : mcBox a b κ = Icc (0 : Fin l → ℝ) (a κ) ×ˢ Icc (0 : Fin p → ℝ) (b κ) := by
      ext q
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩⟩
    rw [e]
    exact isCompact_Icc.prod isCompact_Icc
  · intro q hq q' hq' s t hs ht hst
    obtain rfl : t = 1 - s := by linarith
    have := hgc κ κ hκ hκ q hq q' hq' s hs (by linarith)
    rwa [Convex.combo_self (by ring : s + (1 - s) = 1)] at this
  · intro κ _ γ y hq γ' y' h1 h2 h3 h4
    exact ⟨h1, h2.trans hq.2.1, h3, h4.trans hq.2.2.2⟩
  · intro κ κ' hκ' hle q hq
    exact ⟨hq.1, hq.2.1.trans (ham κ κ' hκ' hle), hq.2.2.1, hq.2.2.2.trans (hbm κ κ' hκ' hle)⟩
  · intro κ hκ
    have hM := interior_subset hκ
    exact ⟨a κ, hpos κ hκ, ha0 κ hM.1, le_rfl, hM.1, hM.2.2.2.2⟩

/-! ### The example technology `Φ(κ) = {γ ≤ 1 − e^{−κ}, y ≤ 2κ}` -/

/-- `a(κ) = 1 − e^{−κ}`. -/
noncomputable def mcExA (κ : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => 1 - Real.exp (-κ 0)

/-- `b(κ) = 2κ`. -/
def mcExB (κ : Fin 1 → ℝ) : Fin 1 → ℝ := fun m => 2 * κ m

/-- The technology of the NOTE to Exercise 16.7a (`l = p = 1`):
`Φ(κ) = {(γ, y) ∈ ℝ²₊ : γ ≤ 1 − e^{−κ}, y ≤ 2κ}`. -/
noncomputable def mcExPhi : (Fin 1 → ℝ) → Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) := mcBox mcExA mcExB

/-- Every `κ : Fin 1 → ℝ` with `κ 0 > 0` is in `int M`; here `M = ℝ₊`. -/
theorem mcEx_mem_interior {κ : Fin 1 → ℝ} (hκ : 0 < κ 0) : κ ∈ interior (mcM mcExPhi) := by
  refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨κ 0, hκ, fun x hx => ?_⟩)
  have h0 : |x 0 - κ 0| < κ 0 := by
    have := (dist_le_pi_dist x κ 0).trans_lt (Metric.mem_ball.1 hx)
    rwa [Real.dist_eq] at this
  have hx0 : 0 ≤ x := fun m => by
    rw [Subsingleton.elim m 0]
    change 0 ≤ x 0
    linarith [(abs_lt.1 h0).1]
  refine ⟨hx0, le_rfl, fun _ => sub_nonneg.2 (Real.exp_le_one_iff.2
    (by have h : (0 : ℝ) ≤ x 0 := hx0 0; linarith)), hx0,
    fun m => ?_⟩
  change x m ≤ 2 * x m
  have h : (0 : ℝ) ≤ x m := hx0 m
  linarith

/-- **The example technology satisfies (T1)–(T7).** -/
theorem mcExPhi_tech : ManyConsumersTech mcExPhi := by
  refine mcBox_tech ?_ ?_ (fun κ hκ _ => sub_nonneg.2 (Real.exp_le_one_iff.2
      (by have h : (0 : ℝ) ≤ κ 0 := hκ 0; linarith)))
    (fun κ hκ m => by
      change (0 : ℝ) ≤ 2 * κ m
      have h : (0 : ℝ) ≤ κ m := hκ m
      linarith)
    (fun κ κ' _ h _ => sub_le_sub_left (Real.exp_le_exp.2 (neg_le_neg (h 0))) 1)
    (fun κ κ' _ h m => mul_le_mul_of_nonneg_left (h m) zero_le_two) (fun κ κ' _ _ θ h0 h1 m => ?_)
    (fun κ κ' _ _ θ _ _ m => ?_) ⟨fun _ => 1, mcEx_mem_interior one_pos⟩ fun κ hκ m => ?_
  · exact (continuous_pi fun _ => continuous_const.sub
      (Real.continuous_exp.comp (continuous_apply 0).neg)).continuousOn
  · exact (continuous_pi fun m => continuous_const.mul (continuous_apply m)).continuousOn
  · simp only [mcExA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h := convexOn_exp.2 (mem_univ (-κ 0)) (mem_univ (-κ' 0)) h0 (by linarith : 0 ≤ 1 - θ)
      (by ring)
    simp only [smul_eq_mul] at h
    have e : -(θ * κ 0 + (1 - θ) * κ' 0) = θ * -κ 0 + (1 - θ) * -κ' 0 := by ring
    rw [e]
    linarith
  · simp only [mcExB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hκ)
    have hmem : κ - (fun _ => r / 2) ∈ mcM mcExPhi := hball (by
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro m
      rw [Real.dist_eq]
      simp only [Pi.sub_apply, sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (half_pos hr)]
      linarith)
    have h0 : 0 ≤ κ 0 - r / 2 := hmem.1 0
    change 0 < 1 - Real.exp (-κ 0)
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith

/-! ### The example aggregator `W(x, z) = min(x, 1) + z/2` -/

/-- The aggregator `W(x, z) = min(x, 1) + z/2` on `ℝ₊ × ℝ₊` (`l = 1`). -/
noncomputable def mcExW (x : Fin 1 → ℝ) (z : ℝ) : ℝ := min (x 0) 1 + z / 2

/-- Its fixed point `u(c) = Σ_t (1/2)ᵗ min(c_t, 1)`. -/
noncomputable def mcExU : BddSeq (Fin 1 → ℝ) → ℝ := discountedUtility (1 / 2) fun x => min (x 0) 1

/-- `|min(x, 1)| ≤ 1` on `ℝ₊`. -/
theorem mcEx_period_bound : ∀ c ∈ Ici (0 : Fin 1 → ℝ), |min (c 0) 1| ≤ 1 := fun c hc => by
  have h0 : 0 ≤ min (c 0) 1 := le_min (hc 0) zero_le_one
  rw [abs_of_nonneg h0]
  exact min_le_right _ _

/-- `W(x, z) = min(x, 1) + z/2` satisfies (W1)–(W5) with `β = 1/2`. -/
theorem mcExW_agg : ManyConsumersAggregator mcExW (1 / 2) := by
  refine ⟨⟨by norm_num, by norm_num, ?_, by simp [mcExW], fun z _ => ⟨1 + |z / 2|, fun c hc => ?_⟩,
    fun c hc z hz => ?_, fun c _ z _ z' _ => ?_⟩, fun x x' z z' _ hxx' _ hzz' => ?_, ?_⟩
  · exact ((((continuous_apply 0).comp continuous_fst).min continuous_const).add
      (continuous_snd.div_const 2)).continuousOn
  · exact (abs_add_le _ _).trans (by linarith [mcEx_period_bound c hc])
  · have h1 : (0 : ℝ) ≤ min (c 0) 1 := le_min (hc 0) zero_le_one
    have h2 := div_nonneg hz (zero_le_two : (0 : ℝ) ≤ 2)
    unfold mcExW
    linarith
  · unfold mcExW
    rw [show min (c 0) 1 + z / 2 - (min (c 0) 1 + z' / 2) = (1 / 2) * (z - z') by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  · unfold mcExW
    have := min_le_min (hxx' 0) (le_refl (1 : ℝ))
    linarith
  · refine ⟨(convex_Ici 0).prod (convex_Ici 0), fun q _ q' _ a b ha hb hab => ?_⟩
    simp only [mcExW, smul_eq_mul, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply]
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (q.1 0) 1) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_left (q'.1 0) 1) hb
    have h3 := mul_le_mul_of_nonneg_left (min_le_right (q.1 0) 1) ha
    have h4 := mul_le_mul_of_nonneg_left (min_le_right (q'.1 0) 1) hb
    have h5 : a * min (q.1 0) 1 + b * min (q'.1 0) 1 ≤ min (a * q.1 0 + b * q'.1 0) 1 :=
      le_min (by linarith) (by linarith)
    linarith

/-- `u(c) = Σ_t (1/2)ᵗ min(c_t, 1)` is the bounded continuous fixed point of `T_W`. -/
theorem mcExU_fixed : IsAggregatorFixedPoint (Ici (0 : Fin 1 → ℝ)) mcExW mcExU := by
  have hβ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hβ1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨⟨2, fun x hx => ?_⟩, ex_15_10b_continuousOn hβ0 hβ1 mcEx_period_bound
    (((continuous_apply 0).min continuous_const).continuousOn), fun x hx =>
    tsum_nonneg fun t => mul_nonneg (by positivity) (le_min (hx t 0) zero_le_one), fun x hx => ?_⟩
  · have hs := summable_discounted hβ0 hβ1 mcEx_period_bound hx
    have h := norm_tsum_le_tsum_norm hs.norm
    refine h.trans ?_
    calc ∑' t, ‖(1 / 2 : ℝ) ^ t * min (x t 0) 1‖ ≤ ∑' t, 1 * (1 / 2 : ℝ) ^ t :=
          hs.norm.tsum_le_tsum (norm_discounted_term_le hβ0 mcEx_period_bound hx)
            ((summable_geometric_of_lt_one hβ0 hβ1).mul_left 1)
      _ = 2 := by rw [tsum_mul_left, tsum_geometric_two]; norm_num
  · have hs := summable_discounted hβ0 hβ1 mcEx_period_bound hx
    unfold mcExU discountedUtility mcExW
    have e : ∑' b, (1 / 2 : ℝ) ^ (b + 1) * min (x (b + 1) 0) 1 =
        (∑' t, (1 / 2 : ℝ) ^ t * min (seqShift x t 0) 1) / 2 := by
      rw [← tsum_div_const]
      exact tsum_congr fun b => by rw [seqShift_apply]; ring
    rw [hs.tsum_eq_zero_add, e, pow_zero, one_mul]

/-! ### Exercise 16.7a: `Y(k̂)` is not closed -/

/-- `‖(1 − e^{−y})‖ ≤ 1` for `y ≥ 0`. -/
theorem mcEx_norm_le {y : ℝ} (hy : 0 ≤ y) : ‖(fun _ : Fin 1 => 1 - Real.exp (-y))‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => ?_
  rw [Real.norm_eq_abs, abs_le]
  have h1 := Real.exp_pos (-y)
  have h2 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  constructor <;> linarith

/-- The limit plan `c_t = 1 − e^{−2ᵗ}`; it needs the capital path `k_t ≥ 2ᵗ`. -/
noncomputable def mcExC : BddSeq (Fin 1 → ℝ) :=
  BddSeq.mk (fun t _ => 1 - Real.exp (-(2 : ℝ) ^ t)) 1 fun t => mcEx_norm_le (by positivity)

/-- The plans `cⁿ_t = 1 − e^{−min(2ᵗ, n + 1)}`, feasible along the bounded paths `kⁿ`. -/
noncomputable def mcExCn (n : ℕ) : BddSeq (Fin 1 → ℝ) :=
  BddSeq.mk (fun t _ => 1 - Real.exp (-min ((2 : ℝ) ^ t) ((n : ℝ) + 1))) 1 fun t =>
    mcEx_norm_le (le_min (by positivity) (by positivity))

/-- The bounded capital paths `kⁿ_t = min(2ᵗ, n + 1)`. -/
noncomputable def mcExKn (n : ℕ) : BddSeq (Fin 1 → ℝ) :=
  BddSeq.mk (fun t _ => min ((2 : ℝ) ^ t) ((n : ℝ) + 1)) ((n : ℝ) + 1) fun t =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by positivity))]
      exact min_le_right _ _

/-- `cⁿ ∈ Y(1)`. -/
theorem mcExCn_mem (n : ℕ) : mcExCn n ∈ mcProdSet mcExPhi (fun _ => 1) := by
  have hN : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hmin : ∀ t : ℕ, 0 ≤ min ((2 : ℝ) ^ t) ((n : ℝ) + 1) := fun t =>
    le_min (by positivity) hN
  have hc0 : ∀ t, 0 ≤ mcExCn n t := fun t m => by
    change 0 ≤ 1 - Real.exp (-min ((2 : ℝ) ^ t) ((n : ℝ) + 1))
    exact sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith [hmin t]))
  refine ⟨hc0, mcExKn n, fun t m => hmin t, ?_, fun t => ⟨hc0 t, fun m => le_rfl,
    fun m => hmin (t + 1), fun m => ?_⟩⟩
  · funext m
    change min ((2 : ℝ) ^ 0) ((n : ℝ) + 1) = 1
    rw [pow_zero]
    exact min_eq_left (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  · change min ((2 : ℝ) ^ (t + 1)) ((n : ℝ) + 1) ≤ 2 * min ((2 : ℝ) ^ t) ((n : ℝ) + 1)
    rw [pow_succ]
    rcases le_total ((2 : ℝ) ^ t) ((n : ℝ) + 1) with h | h
    · rw [min_eq_left h]
      linarith [min_le_left ((2 : ℝ) ^ t * 2) ((n : ℝ) + 1)]
    · rw [min_eq_right h]
      linarith [min_le_right ((2 : ℝ) ^ t * 2) ((n : ℝ) + 1)]

/-- `cⁿ → c` in the sup norm: `‖cⁿ − c‖ ≤ e^{−(n+1)}`. -/
theorem mcExCn_tendsto : Tendsto mcExCn atTop (𝓝 mcExC) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  refine lp.norm_le_of_forall_le (Real.exp_pos _).le fun t => ?_
  rw [mc_sub_apply]
  refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2 fun m => ?_
  change |(1 - Real.exp (-min ((2 : ℝ) ^ t) ((n : ℝ) + 1))) - (1 - Real.exp (-(2 : ℝ) ^ t))| ≤
    Real.exp (-((n : ℝ) + 1))
  rcases le_total ((2 : ℝ) ^ t) ((n : ℝ) + 1) with h | h
  · rw [min_eq_left h, sub_self, abs_zero]
    exact (Real.exp_pos _).le
  · rw [min_eq_right h]
    have h1 := Real.exp_le_exp.2 (neg_le_neg h)
    have h2 := Real.exp_pos (-(2 : ℝ) ^ t)
    rw [abs_le]
    constructor <;> linarith

/-- `c ∉ Y(1)`: `c_t ≤ 1 − e^{−k_t}` forces `k_t ≥ 2ᵗ`, so no bounded capital path supports `c`. -/
theorem mcExC_not_mem : mcExC ∉ mcProdSet mcExPhi (fun _ => 1) := by
  rintro ⟨-, k, -, -, hk⟩
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt ‖k‖ (by norm_num : (1 : ℝ) < 2)
  have h1 : 1 - Real.exp (-(2 : ℝ) ^ t) ≤ 1 - Real.exp (-(k t 0)) := (hk t).2.1 0
  have h2 : (2 : ℝ) ^ t ≤ k t 0 := by
    have := Real.exp_le_exp.1 (by linarith : Real.exp (-(k t 0)) ≤ Real.exp (-(2 : ℝ) ^ t))
    linarith
  have h3 : k t 0 ≤ ‖k‖ :=
    (Real.le_norm_self _).trans ((norm_le_pi_norm (k t) 0).trans (norm_seq_coord_le k t))
  linarith

/-- **Exercise 16.7a is false: `Y(k̂)` need not be closed** under (T1)–(T7), even for
`k̂ ∈ int M`. For `Φ(κ) = {γ ≤ 1 − e^{−κ}, y ≤ 2κ}` and `k̂ = 1`, the plans `cⁿ ∈ Y(1)` converge
in the sup norm to `c_t = 1 − e^{−2ᵗ}`, which needs an unbounded capital path. -/
theorem ex_16_7a_counterexample :
    ManyConsumersTech mcExPhi ∧ (fun _ => (1 : ℝ)) ∈ interior (mcM mcExPhi) ∧
      ¬ IsClosed (mcProdSet mcExPhi (fun _ => 1)) :=
  ⟨mcExPhi_tech, mcEx_mem_interior one_pos, fun h =>
    mcExC_not_mem (h.mem_of_tendsto mcExCn_tendsto (Eventually.of_forall mcExCn_mem))⟩

/-- With unbounded capital paths allowed (`Y′`), the limit plan `c` is feasible (`k_t = 2ᵗ`). -/
theorem mcExC_mem_unb : mcExC ∈ mcProdSetUnb mcExPhi (fun _ => 1) := by
  refine ⟨fun t m => ?_, fun t _ => (2 : ℝ) ^ t, fun t m => by positivity, ?_, fun t =>
    ⟨fun m => ?_, fun m => le_rfl, fun m => by positivity, fun m => ?_⟩⟩
  · change 0 ≤ 1 - Real.exp (-(2 : ℝ) ^ t)
    exact sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith [(by positivity : (0 : ℝ) ≤ 2 ^ t)]))
  · funext m
    simp
  · change 0 ≤ 1 - Real.exp (-(2 : ℝ) ^ t)
    exact sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith [(by positivity : (0 : ℝ) ≤ 2 ^ t)]))
  · change (2 : ℝ) ^ (t + 1) ≤ 2 * 2 ^ t
    rw [pow_succ, mul_comm]

/-! ### Exercise 16.7c: `U(k̂)` need not be closed -/

/-- Every plan in `Y(1)` is strictly improved upon by some `cⁿ` (the supremum of `u` on `Y(1)` is
not attained). -/
theorem mcEx_strict {c : BddSeq (Fin 1 → ℝ)} (hc : c ∈ mcProdSet mcExPhi (fun _ => 1)) :
    ∃ n, mcExU c < mcExU (mcExCn n) := by
  obtain ⟨hc0, k, -, hkk, hk⟩ := hc
  have hk2 : ∀ t, k t 0 ≤ (2 : ℝ) ^ t := by
    intro t
    induction t with
    | zero => rw [hkk, pow_zero]
    | succ t ih =>
      have : k (t + 1) 0 ≤ 2 * k t 0 := (hk t).2.2.2 0
      rw [pow_succ]
      linarith
  have hkK : ∀ t, k t 0 ≤ ‖k‖ := fun t =>
    (Real.le_norm_self _).trans ((norm_le_pi_norm (k t) 0).trans (norm_seq_coord_le k t))
  obtain ⟨n, hn⟩ := exists_nat_gt ‖k‖
  have hcle : ∀ t, c t 0 ≤ 1 - Real.exp (-(k t 0)) := fun t => (hk t).2.1 0
  have hcn : ∀ t, mcExCn n t 0 = 1 - Real.exp (-min ((2 : ℝ) ^ t) ((n : ℝ) + 1)) := fun t => rfl
  have hmono : ∀ t, c t 0 ≤ mcExCn n t 0 := fun t => by
    rw [hcn]
    exact (hcle t).trans (sub_le_sub_left (Real.exp_le_exp.2 (neg_le_neg
      (le_min (hk2 t) ((hkK t).trans (by linarith))))) 1)
  obtain ⟨t0, ht0⟩ := pow_unbounded_of_one_lt ((n : ℝ) + 1) (by norm_num : (1 : ℝ) < 2)
  have hstrict : c t0 0 < mcExCn n t0 0 := by
    rw [hcn, min_eq_right ht0.le]
    exact (hcle t0).trans_lt (sub_lt_sub_left (Real.exp_lt_exp.2 (neg_lt_neg
      ((hkK t0).trans_lt (by linarith)))) 1)
  have hcn1 : ∀ t, mcExCn n t 0 < 1 := fun t => by
    rw [hcn]
    linarith [Real.exp_pos (-min ((2 : ℝ) ^ t) ((n : ℝ) + 1))]
  refine ⟨n, ?_⟩
  have hcC : c ∈ mcCons 1 := fun t => hc0 t
  have hcnC : mcExCn n ∈ mcCons 1 := mcProdSet_subset_cons (Φ := mcExPhi) _ (mcExCn_mem n)
  have hs := summable_discounted (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    mcEx_period_bound hcC
  have hs' := summable_discounted (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    mcEx_period_bound hcnC
  unfold mcExU discountedUtility
  refine hs.tsum_lt_tsum (i := t0) (fun t => ?_) ?_ hs'
  · exact mul_le_mul_of_nonneg_left (min_le_min (hmono t) le_rfl) (by positivity)
  · refine mul_lt_mul_of_pos_left ?_ (by positivity)
    beta_reduce
    rw [min_eq_left (hcn1 t0).le]
    exact (min_le_left _ _).trans_lt hstrict

/-- **Exercise 16.7c is false without closedness of `U(κ)`.** With one consumer
(`W(x, z) = min(x, 1) + z/2`, `u(c) = Σ (1/2)ᵗ min(c_t, 1)`), the example technology and `κ = 1`,
the point `z = v(1, 1)` satisfies `v(1, θ) ≥ θ · z` for all `θ ∈ Δ¹` but `z ∉ U(1)`: the supremum
needs an unbounded capital path. Hence `U(1)` is not closed. -/
theorem ex_16_7c_counterexample :
    ManyConsumersTech mcExPhi ∧ ManyConsumersAggregator mcExW (1 / 2) ∧
    IsAggregatorFixedPoint (Ici 0) mcExW mcExU ∧
    (∃ z : Unit → ℝ, 0 ≤ z ∧
      (∀ θ ∈ mcSimplex Unit, ∑ i, θ i * z i ≤ mcSupport mcExPhi (fun _ => mcExU) (fun _ => 1) θ) ∧
      z ∉ mcUtilSet mcExPhi (fun _ => mcExU) (fun _ => 1)) ∧
    ¬ IsClosed (mcUtilSet mcExPhi (fun (_ : Unit) => mcExU) (fun _ => 1)) := by
  set v := mcSupport mcExPhi (fun (_ : Unit) => mcExU) (fun _ => 1) with hv
  have hu : ∀ _ : Unit, IsAggregatorFixedPoint (Ici 0) mcExW mcExU := fun _ => mcExU_fixed
  have hθ1 : ∀ θ ∈ mcSimplex Unit, θ = fun _ => 1 := fun θ hθ => funext fun i => by
    have h := hθ.2
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at h
    exact h
  have h1 : (fun _ : Unit => (1 : ℝ)) ∈ mcSimplex Unit := ⟨fun _ => zero_le_one, by simp⟩
  obtain ⟨B, -, hB⟩ := mc_utility_bounds hu
  set z : Unit → ℝ := fun _ => v (fun _ => 1) with hzdef
  have hz : z ∉ mcUtilSet mcExPhi (fun _ => mcExU) (fun _ => 1) := by
    rintro ⟨c, hc, hzc⟩
    have hc1 : c () ∈ mcProdSet mcExPhi (fun _ => 1) := by
      have := hc.2
      simpa using this
    obtain ⟨n, hn⟩ := mcEx_strict hc1
    have hfeas : mcFeasible mcExPhi (fun _ => 1) (fun _ : Unit => mcExCn n) :=
      ⟨fun _ => mcProdSet_subset_cons _ (mcExCn_mem n), by simpa using mcExCn_mem n⟩
    have hle := le_csSup (mcUtilSet_bddAbove hB (fun _ => 1) h1) ⟨_, ⟨_, hfeas, rfl⟩, rfl⟩
    have hle' : mcExU (mcExCn n) ≤ v (fun _ => 1) := (le_of_eq (by simp)).trans hle
    have hz' : v (fun _ => 1) = mcExU (c ()) := congrFun hzc ()
    linarith
  have hz0 : 0 ≤ z := fun _ =>
    (mcSupport_admissible hu mcExPhi_tech).nonneg _ (fun _ => zero_le_one) _ h1
  have hzθ : ∀ θ ∈ mcSimplex Unit, ∑ i, θ i * z i ≤ v θ := fun θ hθ => by
    rw [hθ1 θ hθ]
    simp [hzdef]
  exact ⟨mcExPhi_tech, mcExW_agg, mcExU_fixed, ⟨z, hz0, hzθ, hz⟩, fun hcl =>
    hz ((ex_16_7c (fun _ => mcExW_agg) hu mcExPhi_tech (fun _ => zero_le_one) hcl z).2
      ⟨hz0, hzθ⟩)⟩

/-! ### Exercise 16.7b: weights on the boundary of the simplex -/

/-- Two consumers: consumer `0` has `W ≡ 0`, consumer `1` has `mcExW`. -/
noncomputable def mcExW2 (i : Fin 2) : (Fin 1 → ℝ) → ℝ → ℝ :=
  if i = 0 then fun _ _ => 0 else mcExW

/-- Their utilities: `u₀ ≡ 0`, `u₁ = mcExU`. -/
noncomputable def mcExU2 (i : Fin 2) : BddSeq (Fin 1 → ℝ) → ℝ :=
  if i = 0 then fun _ => 0 else mcExU

/-- `u₁ > 0` at the constant plan `(γ, γ, …)`, `γ = 1 − e^{−1}`. -/
theorem mcExU_const_pos : 0 < mcExU (mcConst fun _ => 1 - Real.exp (-1)) := by
  have hγ : 0 < 1 - Real.exp (-1) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have hγ1 : 1 - Real.exp (-1) < 1 := by linarith [Real.exp_pos (-1)]
  have hC : mcConst (fun _ : Fin 1 => 1 - Real.exp (-1)) ∈ mcCons 1 := fun t m => hγ.le
  have hs := summable_discounted (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    mcEx_period_bound hC
  unfold mcExU discountedUtility
  refine hs.tsum_pos (fun t => ?_) 0 ?_
  · have h0 : (0 : ℝ) ≤ 1 - Real.exp (-1) := hγ.le
    exact mul_nonneg (by positivity) (le_min h0 zero_le_one)
  · change 0 < (1 / 2 : ℝ) ^ 0 * min (1 - Real.exp (-1)) 1
    rw [min_eq_left hγ1.le]
    positivity

/-- **Exercise 16.7b, "if", fails for weights on the boundary of `Δᴵ`.** With `I = 2`,
`W₀ ≡ 0` (allowed by (W1)–(W5)), `W₁(x, z) = min(x, 1) + z/2`, the example technology and
`κ = 1`, the zero allocation maximises `Σᵢ θᵢuᵢ` for `θ = (1, 0)` but is not Pareto optimal:
consumer 1 can be given the feasible constant plan `1 − e^{−1}`. -/
theorem ex_16_7b_counterexample :
    (∀ i, ManyConsumersAggregator (mcExW2 i) (1 / 2)) ∧
    (∀ i, IsAggregatorFixedPoint (Ici 0) (mcExW2 i) (mcExU2 i)) ∧ ManyConsumersTech mcExPhi ∧
    ∃ θ ∈ mcSimplex (Fin 2), ∃ c : Fin 2 → BddSeq (Fin 1 → ℝ),
      mcFeasible mcExPhi (fun _ => 1) c ∧
      (∀ c', mcFeasible mcExPhi (fun _ => 1) c' →
        ∑ i, θ i * mcExU2 i (c' i) ≤ ∑ i, θ i * mcExU2 i (c i)) ∧
      ¬ ParetoOptimal (fun _ : Fin 2 => mcCons 1) mcExU2
        (fun _ : Unit => mcProdSet mcExPhi (fun _ => 1)) c (fun _ => ∑ i, c i) := by
  have hW : ∀ i, ManyConsumersAggregator (mcExW2 i) (1 / 2) := fun i => by
    unfold mcExW2
    split_ifs
    · exact (mc_nonsatiation_counterexample (l := 1)).1
    · exact mcExW_agg
  have hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (mcExW2 i) (mcExU2 i) := fun i => by
    unfold mcExW2 mcExU2
    split_ifs
    · exact (mc_nonsatiation_counterexample (l := 1)).2.1
    · exact mcExU_fixed
  have hzero : mcExU 0 = 0 := mc_utility_zero mcExW_agg.agg mcExU_fixed
  have hu0 : mcExU2 0 = fun _ => 0 := by simp [mcExU2]
  have hu1 : mcExU2 1 = mcExU := by simp [mcExU2]
  refine ⟨hW, hu, mcExPhi_tech, Pi.single 0 1, mc_single_mem_simplex 0, 0,
    mcFeasible_zero mcExPhi_tech (fun _ => zero_le_one), fun c' _ => ?_, fun hPO => ?_⟩
  · simp [Fin.sum_univ_two, hu0]
  · have hγ0 : (0 : ℝ) ≤ 1 - Real.exp (-1) := sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num))
    have hmem : mcConst (fun _ : Fin 1 => 1 - Real.exp (-1)) ∈ mcProdSet mcExPhi (fun _ => 1) :=
      ⟨fun t m => hγ0, mcConst fun _ => 1, fun t m => zero_le_one, rfl, fun t =>
        ⟨fun m => hγ0, fun m => le_rfl, fun m => zero_le_one, fun m => by
          change (1 : ℝ) ≤ 2 * 1
          norm_num⟩⟩
    have h0C : (0 : BddSeq (Fin 1 → ℝ)) ∈ mcCons 1 :=
      (mcFeasible_zero (ι := Unit) mcExPhi_tech (fun _ => zero_le_one)).1 ()
    have hfeas : mcFeasible mcExPhi (fun _ => 1)
        ![0, mcConst fun _ : Fin 1 => 1 - Real.exp (-1)] := by
      refine ⟨fun i => ?_, by simpa [Fin.sum_univ_two] using hmem⟩
      fin_cases i
      · simpa using h0C
      · simpa using mcProdSet_subset_cons _ hmem
    refine hPO.2 ⟨_, fun _ => ∑ i, ![0, mcConst fun _ : Fin 1 => 1 - Real.exp (-1)] i,
      (mc_feasible_iff _ _ _).2 ⟨hfeas, rfl⟩, fun i => ?_, 1, ?_⟩
    · fin_cases i
      · simp [hu0]
      · simp [hu1, hzero, mcExU_const_pos.le]
    · simp [hu1, hzero, mcExU_const_pos]

/-! ### Exercise 16.7d: the constraint set need not be convex -/

/-- `f(κ′) = min(|κ′ − 1|, 1)` (`I = 1`), the function of the NOTE to Exercise 16.7d. -/
noncomputable def mcExFd (κ' : Fin 1 → ℝ) (_ : Unit → ℝ) : ℝ := min |κ' 0 - 1| 1

/-- **Exercise 16.7d is false for convexity.** For `f(κ′) = min(|κ′ − 1|, 1) ∈ F` and `κ = 1`,
`(γ, z′, κ′) = (0, 1, 0)` and `(0, 1, 2)` satisfy the constraints of (4), but their midpoint
`(0, 1, 1)` does not (`f(1) = 0 < 1`). -/
theorem ex_16_7d_counterexample :
    ManyConsumersTech mcExPhi ∧ MCInF mcExFd ∧
      ¬ Convex ℝ (mcConstraint mcExPhi mcExFd (fun _ => 1)) := by
  refine ⟨mcExPhi_tech, ⟨?_, ⟨1, fun _ _ _ _ => min_le_right _ _⟩,
    fun _ _ _ _ => le_min (abs_nonneg _) zero_le_one⟩, fun h => ?_⟩
  · exact ((((continuous_apply 0).comp continuous_fst).sub continuous_const).abs.min
      continuous_const).continuousOn
  · have hmem : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → 1 ≤ |x - 1| →
        (((0 : Unit → Fin 1 → ℝ), (fun _ => (1 : ℝ)), (fun _ => x)) :
          (Unit → Fin 1 → ℝ) × (Unit → ℝ) × (Fin 1 → ℝ)) ∈
          mcConstraint mcExPhi mcExFd (fun _ => 1) := by
      intro x hx0 hx2 hx1
      refine ⟨fun _ => le_rfl, ⟨?_, ?_, fun _ => hx0, fun _ => ?_⟩,
        ⟨fun _ => zero_le_one, fun θ hθ => ?_⟩⟩
      · simp
      · simp only [Pi.zero_apply, Finset.sum_const_zero]
        exact fun _ => sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num))
      · change x ≤ 2 * 1
        linarith
      · have h1 := hθ.2
        simp only [mcExFd, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
          mul_one] at h1 ⊢
        rw [h1]
        exact le_min hx1 le_rfl
    have h1 := hmem 0 le_rfl (by norm_num) (by norm_num)
    have h2 := hmem 2 (by norm_num) le_rfl (by norm_num)
    have hmid := h h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have := hmid.2.2.2 (fun _ => 1) ⟨fun _ => zero_le_one, by simp⟩
    norm_num [mcExFd] at this

/-! ### Exercise 16.7e: `T` does not map `F` into `F` -/

/-- `f(κ′, θ′) = max(θ′₀ − |κ′ − 1|, 0)` (`I = 2`): `𝒰_f(κ′) = {0}` for `0 ≤ κ′ < 1` but
`(1, 0) ∈ 𝒰_f(1)`. -/
noncomputable def mcExFe (κ' : Fin 1 → ℝ) (θ : Fin 2 → ℝ) : ℝ := max (θ 0 - |κ' 0 - 1|) 0

/-- `f ∈ F`. -/
theorem mcExFe_inF : MCInF mcExFe := by
  refine ⟨?_, ⟨1, fun κ _ θ hθ => max_le ?_ zero_le_one⟩, fun _ _ _ _ => le_max_right _ _⟩
  · exact ((((continuous_apply (0 : Fin 2)).comp continuous_snd).sub
      ((((continuous_apply (0 : Fin 1)).comp continuous_fst).sub continuous_const).abs)).max
      continuous_const).continuousOn
  · linarith [mcSimplex_le_one hθ 0, abs_nonneg (κ 0 - 1)]

/-- For `0 ≤ κ′ < 1`, every `z ∈ 𝒰_f(κ′)` has `z₀ = 0` (test with `θ = (1 − κ′, κ′)`). -/
theorem mcExFe_upper_zero {κ' : Fin 1 → ℝ} (h0 : 0 ≤ κ' 0) (h1 : κ' 0 < 1) {z : Fin 2 → ℝ}
    (hz : z ∈ mcUpper mcExFe κ') : z 0 = 0 := by
  have hθ : ![1 - κ' 0, κ' 0] ∈ mcSimplex (Fin 2) := by
    refine ⟨fun i => ?_, by simp [Fin.sum_univ_two]⟩
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      linarith
    · simpa using h0
  have h := hz.2 _ hθ
  simp only [Fin.sum_univ_two, mcExFe] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [abs_of_neg (by linarith : κ' 0 - 1 < 0), show 1 - κ' 0 - -(κ' 0 - 1) = 0 by ring,
    max_self] at h
  have hz0 : 0 ≤ z 0 := hz.1 0
  have hz1 : 0 ≤ z 1 := hz.1 1
  have h3 : 0 ≤ κ' 0 * z 1 := mul_nonneg h0 hz1
  have h4 : (1 - κ' 0) * z 0 ≤ 0 := by linarith
  have h5 : z 0 ≤ 0 := by nlinarith
  linarith

/-- The objective of (4) at `θ = e₀` for two consumers with aggregator `mcExW`. -/
theorem mcEx_obj_e0 (q : (Fin 2 → Fin 1 → ℝ) × (Fin 2 → ℝ) × (Fin 1 → ℝ)) :
    mcObjective (fun _ : Fin 2 => mcExW) (Pi.single 0 1) q = min (q.1 0 0) 1 + q.2.1 0 / 2 := by
  simp [mcObjective, Fin.sum_univ_two, mcExW]

/-- **Exercise 16.7e is false: `T` does not map `F` into `F`.** For `I = 2`, both consumers with
`W(x, z) = min(x, 1) + z/2`, the example technology and `f(κ′, θ′) = max(θ′₀ − |κ′ − 1|, 0) ∈ F`,
`Tf(·, e₀)` jumps at `κ = 1/2`: below `1/2` the next capital `κ′ ≤ 2κ < 1` forces `z′₀ = 0` and
`Tf(κ, e₀) ≤ 1 − e^{−1/2}`, while at `κ = 1/2` the choice `κ′ = 1`, `z′ = (1, 0)` gives
`Tf ≥ 1 − e^{−1/2} + 1/2`. The constraint correspondence is not lower hemicontinuous. -/
theorem ex_16_7e_counterexample :
    ManyConsumersTech mcExPhi ∧ ManyConsumersAggregator mcExW (1 / 2) ∧ MCInF mcExFe ∧
      ¬ MCInF (mcOperator (fun _ : Fin 2 => mcExW) mcExPhi mcExFe) := by
  refine ⟨mcExPhi_tech, mcExW_agg, mcExFe_inF, fun hF => ?_⟩
  have hW : ∀ _ : Fin 2, IsAggregator (Ici (0 : Fin 1 → ℝ)) mcExW (1 / 2) := fun _ =>
    mcExW_agg.agg
  obtain ⟨M, hM⟩ := mcExFe_inF.bdd
  have he0 : (Pi.single 0 1 : Fin 2 → ℝ) ∈ mcSimplex (Fin 2) := mc_single_mem_simplex 0
  have hhalf : (0 : Fin 1 → ℝ) ≤ fun _ => 1 / 2 := fun _ => by norm_num
  have hγ0 : (0 : ℝ) ≤ 1 - Real.exp (-(1 / 2)) :=
    sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num))
  have hhigh : 1 - Real.exp (-(1 / 2)) + 1 / 2 ≤
      mcOperator (fun _ : Fin 2 => mcExW) mcExPhi mcExFe (fun _ => 1 / 2) (Pi.single 0 1) := by
    set γ : Fin 2 → Fin 1 → ℝ := ![fun _ => 1 - Real.exp (-(1 / 2)), 0] with hγ
    have hs : ∑ i, γ i = fun _ => 1 - Real.exp (-(1 / 2)) := by
      simp [hγ, Fin.sum_univ_two]
    have hq : ((γ, ![1, 0], fun _ => 1) : (Fin 2 → Fin 1 → ℝ) × (Fin 2 → ℝ) × (Fin 1 → ℝ)) ∈
        mcConstraint mcExPhi mcExFe (fun _ => 1 / 2) := by
      refine ⟨fun i => ?_, ?_, fun i => ?_, fun θ hθ => ?_⟩
      · fin_cases i
        · exact fun _ => hγ0
        · exact le_rfl
      · dsimp only
        rw [hs]
        refine ⟨fun _ => hγ0, fun _ => le_rfl, fun _ => zero_le_one, fun _ => ?_⟩
        change (1 : ℝ) ≤ 2 * (1 / 2)
        norm_num
      · fin_cases i <;> simp
      · simp [Fin.sum_univ_two, mcExFe]
    have hval : mcObjective (fun _ : Fin 2 => mcExW) (Pi.single 0 1)
        ((γ, ![1, 0], fun _ => 1) : (Fin 2 → Fin 1 → ℝ) × (Fin 2 → ℝ) × (Fin 1 → ℝ)) =
        1 - Real.exp (-(1 / 2)) + 1 / 2 := by
      rw [mcEx_obj_e0]
      simp [hγ, (Real.exp_pos _).le]
    rw [← hval]
    exact le_csSup (mcObjective_bddAbove hW mcExPhi_tech hM hhalf he0) ⟨_, hq, rfl⟩
  have hlow : ∀ κ : Fin 1 → ℝ, 0 ≤ κ → κ 0 < 1 / 2 →
      mcOperator (fun _ : Fin 2 => mcExW) mcExPhi mcExFe κ (Pi.single 0 1) ≤
        1 - Real.exp (-(1 / 2)) := by
    intro κ hκ hκ2
    refine csSup_le ⟨_, _, mcConstraint_nonempty mcExPhi_tech mcExFe_inF.nonneg hκ, rfl⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [mcEx_obj_e0]
    obtain ⟨hγ, ⟨-, hsa, hk0, hkb⟩, hz⟩ := hq
    have hk1 : q.2.2 0 ≤ 2 * κ 0 := hkb 0
    have hk00 : (0 : ℝ) ≤ q.2.2 0 := hk0 0
    have hz0 := mcExFe_upper_zero hk00 (by linarith) hz
    have hsa0 : (∑ i, q.1 i) 0 ≤ 1 - Real.exp (-κ 0) := hsa 0
    rw [Finset.sum_apply, Fin.sum_univ_two] at hsa0
    have hγ10 : (0 : ℝ) ≤ q.1 1 0 := hγ 1 0
    have hexp : Real.exp (-(1 / 2)) ≤ Real.exp (-κ 0) := Real.exp_le_exp.2 (by linarith)
    rw [hz0]
    linarith [min_le_left (q.1 0 0) 1]
  have hx0 : ((fun _ => (1 / 2 : ℝ)), (Pi.single 0 1 : Fin 2 → ℝ)) ∈
      Ici (0 : Fin 1 → ℝ) ×ˢ mcSimplex (Fin 2) := ⟨hhalf, he0⟩
  set κs : ℕ → Fin 1 → ℝ := fun n _ => 1 / 2 - 1 / 4 * (1 / ((n : ℝ) + 1)) with hκs
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hκs0 : ∀ n, 0 ≤ κs n := fun n _ => by
    simp only [hκs, Pi.zero_apply]
    linarith [hle1 n]
  have hκs2 : ∀ n, κs n 0 < 1 / 2 := fun n => by
    simp only [hκs]
    linarith [hpos n]
  have hlimκ : Tendsto κs atTop (𝓝 fun _ => 1 / 2) := tendsto_pi_nhds.2 fun _ => by
    simpa [hκs] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 4 : ℝ)).const_sub
      (1 / 2 : ℝ)
  have hseq : Tendsto (fun n => (κs n, (Pi.single 0 1 : Fin 2 → ℝ))) atTop
      (𝓝[Ici 0 ×ˢ mcSimplex (Fin 2)] ((fun _ => (1 / 2 : ℝ)), (Pi.single 0 1 : Fin 2 → ℝ))) :=
    tendsto_nhdsWithin_iff.2 ⟨hlimκ.prodMk_nhds tendsto_const_nhds,
      Eventually.of_forall fun n => ⟨hκs0 n, he0⟩⟩
  have hlim := ((hF.cont _ hx0).tendsto).comp hseq
  have hle := le_of_tendsto' hlim fun n => hlow (κs n) (hκs0 n) (hκs2 n)
  linarith

/-! ### Exercise 16.7f: the hint and the contraction modulus -/

/-- `g(θ) = 10|θ₀ − ½|` (`I = 2`, constant in `κ′`), the function of the NOTE to the hint. -/
noncomputable def mcExG (_ : Fin 1 → ℝ) (θ : Fin 2 → ℝ) : ℝ := 10 * |θ 0 - 1 / 2|

/-- `g ∈ F`. -/
theorem mcExG_inF : MCInF mcExG := by
  refine ⟨?_, ⟨5, fun κ _ θ hθ => ?_⟩, fun _ _ _ _ => by unfold mcExG; positivity⟩
  · exact (continuous_const.mul ((((continuous_apply 0).comp continuous_snd).sub
      continuous_const).abs)).continuousOn
  · unfold mcExG
    have h0 := hθ.1 0
    have h1 := mcSimplex_le_one hθ 0
    have : |θ 0 - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith

/-- `𝒰_g = {0}` (test with `θ = (½, ½)`). -/
theorem mcExG_upper {κ' : Fin 1 → ℝ} {z : Fin 2 → ℝ} (hz : z ∈ mcUpper mcExG κ') : z = 0 := by
  have hθ : ![1 / 2, 1 / 2] ∈ mcSimplex (Fin 2) := by
    refine ⟨fun i => ?_, by norm_num [Fin.sum_univ_two]⟩
    fin_cases i <;> norm_num
  have h := hz.2 _ hθ
  simp only [Fin.sum_univ_two, mcExG, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  norm_num at h
  have hz0 : 0 ≤ z 0 := hz.1 0
  have hz1 : 0 ≤ z 1 := hz.1 1
  funext i
  fin_cases i
  · change z 0 = 0
    linarith
  · change z 1 = 0
    linarith

/-- `(2a, 0) ∈ 𝒰ᵃ = 𝒰_{g + a}` for `0 ≤ a ≤ 5`. -/
theorem mcExG_mem_upper {a : ℝ} (ha0 : 0 ≤ a) (ha5 : a ≤ 5) (κ' : Fin 1 → ℝ) :
    ![2 * a, 0] ∈ mcUpper (fun κ θ => mcExG κ θ + a) κ' := by
  refine ⟨fun i => ?_, fun θ hθ => ?_⟩
  · fin_cases i
    · simpa using ha0
    · simp
  · simp only [Fin.sum_univ_two, mcExG, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
      add_zero]
    have h0 := hθ.1 0
    rcases le_total (θ 0) (1 / 2) with h | h
    · nlinarith [abs_nonneg (θ 0 - 1 / 2)]
    · rw [abs_of_nonneg (by linarith : 0 ≤ θ 0 - 1 / 2)]
      nlinarith [mul_nonneg (sub_nonneg.2 ha5) (by linarith : 0 ≤ 2 * θ 0 - 1)]

/-- **The hint to Exercise 16.7f is false for general `f ∈ F`**: for `g(θ) = 10|θ₀ − ½|` and
`0 < a ≤ 5`, `𝒰 = {0}` so `B = [0, a]²`, but `(2a, 0) ∈ 𝒰ᵃ \ B`. (`g` is not of support-function
type: its largest support-function minorant is `0`.) -/
theorem ex_16_7f_hint_counterexample {a : ℝ} (ha : 0 < a) (ha5 : a ≤ 5) (κ' : Fin 1 → ℝ) :
    MCInF mcExG ∧ mcUpper mcExG κ' = {0} ∧
    ![2 * a, 0] ∈ mcUpper (fun κ θ => mcExG κ θ + a) κ' ∧
    ![2 * a, 0] ∉ {z | 0 ≤ z ∧ ∃ z'' ∈ mcUpper mcExG κ', z ≤ z'' + fun _ => a} := by
  refine ⟨mcExG_inF, Set.eq_singleton_iff_unique_mem.2 ⟨zero_mem_mcUpper fun θ _ => by
    unfold mcExG; positivity, fun z hz => mcExG_upper hz⟩, mcExG_mem_upper ha.le ha5 κ', ?_⟩
  rintro ⟨-, z'', hz'', hle⟩
  rw [mcExG_upper hz''] at hle
  have := hle 0
  simp at this
  linarith

/-- **Exercise 16.7f is false on `F`: `T` is not a contraction of modulus `β = 1/2`, nor of any
modulus `< 1`.** For `I = 2`, both consumers with `W(x, z) = min(x, 1) + z/2` (`β = 1/2`), the
example technology and `g = 10|θ₀ − ½| ∈ F`: `‖(g + 1) − g‖ = 1`, but
`T(g + 1)(1, e₀) ≥ Tg(1, e₀) + 1`, because `𝒰_g = {0}` while `(2, 0) ∈ 𝒰_{g+1}`. -/
theorem ex_16_7f_counterexample :
    ManyConsumersTech mcExPhi ∧ ManyConsumersAggregator mcExW (1 / 2) ∧ MCInF mcExG ∧
    MCInF (fun κ θ => mcExG κ θ + 1) ∧
    (∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex (Fin 2), |(mcExG κ θ + 1) - mcExG κ θ| ≤ 1) ∧
    mcOperator (fun _ : Fin 2 => mcExW) mcExPhi mcExG (fun _ => 1) (Pi.single 0 1) + 1 ≤
      mcOperator (fun _ : Fin 2 => mcExW) mcExPhi (fun κ θ => mcExG κ θ + 1) (fun _ => 1)
        (Pi.single 0 1) ∧
    ∀ β0 < 1, ¬ ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex (Fin 2),
      |mcOperator (fun _ : Fin 2 => mcExW) mcExPhi (fun κ θ => mcExG κ θ + 1) κ θ -
        mcOperator (fun _ : Fin 2 => mcExW) mcExPhi mcExG κ θ| ≤ β0 * 1 := by
  have hW : ∀ _ : Fin 2, IsAggregator (Ici (0 : Fin 1 → ℝ)) mcExW (1 / 2) := fun _ =>
    mcExW_agg.agg
  obtain ⟨M, hM⟩ := mcExG_inF.bdd
  have hG1 : MCInF (fun κ θ => mcExG κ θ + 1) :=
    ⟨mcExG_inF.cont.add continuousOn_const, ⟨M + 1, fun κ hκ θ hθ => by
      linarith [hM κ hκ θ hθ]⟩, fun κ hκ θ hθ => by linarith [mcExG_inF.nonneg κ hκ θ hθ]⟩
  obtain ⟨M1, hM1⟩ := hG1.bdd
  have h1 : (0 : Fin 1 → ℝ) ≤ fun _ => 1 := fun _ => zero_le_one
  have he0 : (Pi.single 0 1 : Fin 2 → ℝ) ∈ mcSimplex (Fin 2) := mc_single_mem_simplex 0
  have hkey : mcOperator (fun _ : Fin 2 => mcExW) mcExPhi mcExG (fun _ => 1) (Pi.single 0 1) + 1 ≤
      mcOperator (fun _ : Fin 2 => mcExW) mcExPhi (fun κ θ => mcExG κ θ + 1) (fun _ => 1)
        (Pi.single 0 1) := by
    have hle : mcOperator (fun _ : Fin 2 => mcExW) mcExPhi mcExG (fun _ => 1) (Pi.single 0 1) ≤
        mcOperator (fun _ : Fin 2 => mcExW) mcExPhi (fun κ θ => mcExG κ θ + 1) (fun _ => 1)
          (Pi.single 0 1) - 1 := by
      refine csSup_le ⟨_, _, mcConstraint_nonempty mcExPhi_tech mcExG_inF.nonneg h1, rfl⟩ ?_
      rintro _ ⟨q, hq, rfl⟩
      have hz := mcExG_upper hq.2.2
      have hq' : ((q.1, ![2 * 1, 0], q.2.2) : (Fin 2 → Fin 1 → ℝ) × (Fin 2 → ℝ) × (Fin 1 → ℝ)) ∈
          mcConstraint mcExPhi (fun κ θ => mcExG κ θ + 1) (fun _ => 1) :=
        ⟨hq.1, hq.2.1, mcExG_mem_upper zero_le_one (by norm_num) _⟩
      have : mcObjective (fun _ : Fin 2 => mcExW) (Pi.single 0 1) (q.1, ![2 * 1, 0], q.2.2) ≤
          mcOperator (fun _ : Fin 2 => mcExW) mcExPhi (fun κ θ => mcExG κ θ + 1) (fun _ => 1)
            (Pi.single 0 1) :=
        le_csSup (mcObjective_bddAbove hW mcExPhi_tech hM1 h1 he0) ⟨_, hq', rfl⟩
      rw [mcEx_obj_e0] at this ⊢
      rw [hz]
      simp only [Matrix.cons_val_zero, Pi.zero_apply, zero_div, add_zero] at this ⊢
      linarith
    linarith
  refine ⟨mcExPhi_tech, mcExW_agg, mcExG_inF, hG1, fun κ _ θ _ => by simp, hkey,
    fun β0 hβ0 h => ?_⟩
  have := h (fun _ => 1) h1 _ he0
  rw [abs_le] at this
  linarith [this.2]

end StokeyLucasPrescott.EquilibriumApplications
