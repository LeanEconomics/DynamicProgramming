/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.SIPolicies
import IncompleteMarkets.SIEuler
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proposition 17.2.3: the equilibrium rate is below the rate of time preference

Miao, §17.1.1, p. 561, and §17.2.1–17.2.3, pp. 571, 575–576. "In Section 8.3.3, we have shown
that if `β(1 + r) ≥ 1`, `x_t` and `a_t` converge to infinity" (p. 561); hence the interest rate
of any stationary equilibrium, in particular the highest one, the natural-limit rate, is "lower
than `1/β − 1`" (p. 571) and "less than the rate of time preference" (Proposition 17.2.3).

We prove this in the setting in which the book's supporting results are stated: the
income-fluctuation problem of §8.3.2 in cash on hand (`SIModel`, `SIModel.Solution`; debt limit
`b`, iid income), where Ea is computed from a stationary distribution `λ` of cash on hand
`x_{t+1} = Râ(x_t) + y_{t+1} − rb` (`bw_cohStationary`, the form (17.7) of p. 562).

* `bw_coh_lintegral`, `bw_coh_integral`: stationarity of `λ` for sets gives
  `∫ f dλ = ∫∫ f(Râ(x) + y − rb) dμ(y) dλ(x)` for measurable (bounded) `f`.
* `proposition_17_2_3_lt`: **if income is not almost surely constant and cash on hand has a
  stationary distribution, then `βR < 1`**, i.e. `r < 1/β − 1`. The proof: the Euler inequality
  `u′(c(x)) ≥ βR E u′(c(x′))` integrated against `λ` gives `βR ≤ 1`; if `βR = 1`, `u′(c(x_t))` is a
  stationary bounded martingale, so `E(u′(c(x′)) − u′(c(x)))² = 0`; as `u′ ∘ c` is strictly
  decreasing, `x′ = x` almost surely, which forces income to be constant.

**Departures.** The book's argument is the divergence of `x_t` (Proposition 8.3.2, and the
case `βR = 1` of p. 258); we replace it by the stationary-martingale argument above, which
needs only the Euler inequality, stationarity and non-degenerate income (the book's divergence
statements are almost-sure path statements, not formalised in the copied §8.3.2).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Miao, (17.7), p. 562, for the cash-on-hand chain of §17.1.1 (iid income): `λ` is a
stationary distribution of `x_{t+1} = Râ(x_t) + y_{t+1} − rb`,
`λ(A) = ∫ μ{y : Râ(x) + y − rb ∈ A} dλ(x)` for every measurable `A`. -/
def bw_cohStationary {M : SIModel} (S : M.Solution) (lam : Measure ℝ) : Prop :=
  ∀ A, MeasurableSet A → lam A = ∫⁻ x, M.law {y | M.next (S.sav x) y ∈ A} ∂lam

/-- The saving policy extended continuously below `x_min`. -/
theorem bw_savc_continuous {M : SIModel} (S : M.Solution) :
    Continuous fun x => S.sav (max x M.xmin) :=
  S.continuousOn_sav.comp_continuous (continuous_id.max continuous_const)
    fun _ => Set.mem_Ici.2 (le_max_right _ _)

theorem bw_next_continuous {M : SIModel} (S : M.Solution) :
    Continuous fun p : ℝ × ℝ => M.next (S.sav (max p.1 M.xmin)) p.2 := by
  simp only [SIModel.next]
  exact ((continuous_const.mul ((bw_savc_continuous S).comp continuous_fst)).add
    continuous_snd).sub continuous_const

/-- `x ↦ ∫ f(Râ(x) + y − rb) dμ(y)` is strongly measurable for measurable `f`. -/
theorem bw_sm_integral {M : SIModel} (S : M.Solution) {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable fun x => ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law :=
  StronglyMeasurable.integral_prod_right
    (f := fun x y => f (M.next (S.sav (max x M.xmin)) y))
    (hf.comp (bw_next_continuous S).measurable).stronglyMeasurable

theorem bw_ae_ge {M : SIModel} {lam : Measure ℝ} (hsupp : lam (Set.Iio M.xmin) = 0) :
    ∀ᵐ x ∂lam, M.xmin ≤ x := by
  rw [ae_iff]
  convert hsupp using 2
  ext x
  simp [not_le]

/-- Stationarity for measurable `[0, ∞]`-valued functions:
`∫⁻ f dλ = ∫⁻∫⁻ f(Râ(x) + y − rb) dμ(y) dλ(x)`. -/
theorem bw_coh_lintegral {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    (hsupp : lam (Set.Iio M.xmin) = 0) (hst : bw_cohStationary S lam) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂lam = ∫⁻ x, ∫⁻ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law ∂lam := by
  set F : ℝ → Measure ℝ := fun x => M.law.map fun y => M.next (S.sav (max x M.xmin)) y
  have hF : Measurable F := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have : (fun x => F x A) = fun x =>
        M.law (Prod.mk x ⁻¹' {p : ℝ × ℝ | M.next (S.sav (max p.1 M.xmin)) p.2 ∈ A}) := by
      funext x
      simp only [F]
      rw [Measure.map_apply (M.continuous_next_y _).measurable hA]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left ((bw_next_continuous S).measurable hA)
  have hbind : lam = lam.bind F := by
    ext A hA
    rw [Measure.bind_apply hA hF.aemeasurable, hst A hA]
    refine lintegral_congr_ae ?_
    filter_upwards [bw_ae_ge hsupp] with x hx
    simp only [F, max_eq_left hx]
    rw [Measure.map_apply (M.continuous_next_y _).measurable hA]
    rfl
  calc ∫⁻ x, f x ∂lam = ∫⁻ x, f x ∂(lam.bind F) := by rw [← hbind]
    _ = ∫⁻ x, ∫⁻ y, f y ∂(F x) ∂lam := Measure.lintegral_bind hF.aemeasurable hf.aemeasurable
    _ = _ := lintegral_congr fun x => lintegral_map hf (M.continuous_next_y _).measurable

/-- Stationarity for bounded nonnegative measurable functions:
`∫ f dλ = ∫∫ f(Râ(x) + y − rb) dμ(y) dλ(x)`. -/
theorem bw_coh_integral {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    (hsupp : lam (Set.Iio M.xmin) = 0) (hst : bw_cohStationary S lam) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    ∫ x, f x ∂lam = ∫ x, ∫ y, f (M.next (S.sav (max x M.xmin)) y) ∂M.law ∂lam := by
  have hn := (bw_next_continuous S).measurable
  have hI : ∀ x, Integrable (fun y => f (M.next (S.sav (max x M.xmin)) y)) M.law := fun x =>
    Integrable.of_bound ((hf.comp ((bw_next_continuous S).comp
      (Continuous.prodMk_right x)).measurable).aestronglyMeasurable) C
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hC _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => integral_nonneg fun y => h0 _)
      (bw_sm_integral S hf).aestronglyMeasurable,
    bw_coh_lintegral S hsupp hst hf.ennreal_ofReal]
  congr 1
  refine lintegral_congr fun x => ?_
  exact (ofReal_integral_eq_lintegral_ofReal (hI x) (ae_of_all _ fun y => h0 _)).symm

/-- **Proposition 17.2.3**, second part (Miao, p. 576; also pp. 561, 571). In the income
fluctuation problem with iid income that is not almost surely constant, if cash on hand has a
stationary distribution `λ` on `[x_min, ∞)` (as any stationary equilibrium requires), then
`βR < 1`: the interest rate `r = R − 1` is below the rate of time preference `1/β − 1`. -/
theorem proposition_17_2_3_lt {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hsupp : lam (Set.Iio M.xmin) = 0) (hst : bw_cohStationary S lam)
    (hnd : ∀ c, ¬ ∀ᵐ y ∂M.law, y = c) : M.β * M.R < 1 := by
  by_contra hge
  have hge : 1 ≤ M.β * M.R := not_lt.1 hge
  set hf : ℝ → ℝ := fun x => M.du (S.cons (max x M.xmin)) with hhf
  have hcons : ∀ x, 0 < S.cons (max x M.xmin) := fun x => S.cons_pos (le_max_right _ _)
  have hcont : Continuous hf :=
    M.du_cont.comp_continuous (S.continuousOn_cons.comp_continuous
      (continuous_id.max continuous_const) fun x => Set.mem_Ici.2 (le_max_right _ _))
      fun x => Set.mem_Ioi.2 (hcons x)
  have hmeas : Measurable hf := hcont.measurable
  set C := M.du (S.cons M.xmin)
  have hpos : ∀ x, 0 < hf x := fun x => M.du_pos _ (hcons x)
  have hle : ∀ x, hf x ≤ C := fun x => by
    have h1 : S.cons M.xmin ≤ S.cons (max x M.xmin) :=
      S.cons_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (le_max_right _ _)) (le_max_right _ _)
    have h2 : 0 < S.cons M.xmin := by simpa using hcons M.xmin
    exact M.du_anti.antitoneOn (Set.mem_Ioi.2 h2) (Set.mem_Ioi.2 (hcons x)) h1
  set n : ℝ → ℝ → ℝ := fun x y => M.next (S.sav (max x M.xmin)) y with hn
  have hncont : Continuous fun p : ℝ × ℝ => n p.1 p.2 := bw_next_continuous S
  have hIy : ∀ {f : ℝ → ℝ}, Measurable f → ∀ {D : ℝ}, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
      ∀ x, Integrable (fun y => f (n x y)) M.law := fun {f} hfm {D} h0 hD x =>
    Integrable.of_bound ((hfm.comp (hncont.comp (Continuous.prodMk_right x)).measurable
      ).aestronglyMeasurable) D
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hD _)
  set K : ℝ → ℝ := fun x => ∫ y, hf (n x y) ∂M.law with hK
  have hK0 : ∀ x, 0 ≤ K x := fun x => integral_nonneg fun y => (hpos _).le
  have hKC : ∀ x, K x ≤ C := fun x => by
    have : K x ≤ ∫ _y, C ∂M.law :=
      integral_mono (hIy hmeas (fun z => (hpos z).le) hle x) (integrable_const _) fun y => hle _
    simpa using this
  have hKm : StronglyMeasurable K := bw_sm_integral S hmeas
  have hbdd : ∀ {f : ℝ → ℝ}, StronglyMeasurable f → ∀ {D : ℝ}, (∀ x, 0 ≤ f x) →
      (∀ x, f x ≤ D) → Integrable f lam := fun {f} hfm {D} h0 hD =>
    Integrable.of_bound hfm.aestronglyMeasurable D
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hD _)
  have hIh : Integrable hf lam := hbdd hmeas.stronglyMeasurable (fun x => (hpos x).le) hle
  have hIK : Integrable K lam := hbdd hKm hK0 hKC
  -- the Euler inequality, almost everywhere
  have heuler : ∀ᵐ x ∂lam, M.β * M.R * K x ≤ hf x := by
    filter_upwards [bw_ae_ge hsupp] with x hx
    have hs0 := (S.sav_mem x hx).1
    have hE := S.euler_le hx
    rw [S.D_eq hs0] at hE
    have hKx : K x = ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law := by
      refine integral_congr_ae ?_
      filter_upwards [M.ae_next hs0] with y hy
      simp only [hn, hhf, max_eq_left hx, max_eq_left hy.1]
    simpa only [hKx, hhf, max_eq_left hx] using hE
  have hstat1 : ∫ x, hf x ∂lam = ∫ x, K x ∂lam :=
    bw_coh_integral S hsupp hst hmeas (fun x => (hpos x).le) hle
  have hIpos : 0 < ∫ x, hf x ∂lam := si_integral_pos hIh (ae_of_all _ hpos)
  have hmono : M.β * M.R * ∫ x, K x ∂lam ≤ ∫ x, hf x ∂lam := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hIK.const_mul _) hIh heuler
  have hβR : M.β * M.R = 1 := by
    refine le_antisymm ?_ hge
    rw [← hstat1] at hmono
    by_contra hlt
    have := mul_lt_mul_of_pos_right (not_le.1 hlt) hIpos
    linarith
  -- `K = h` almost everywhere
  have hKh : ∀ᵐ x ∂lam, K x = hf x := by
    have hnn : 0 ≤ᵐ[lam] fun x => hf x - K x := by
      filter_upwards [heuler] with x hx
      rw [hβR, one_mul] at hx
      simp only [Pi.zero_apply]; linarith
    have hint : ∫ x, (hf x - K x) ∂lam = 0 := by
      rw [integral_sub hIh hIK, hstat1, sub_self]
    have := (integral_eq_zero_iff_of_nonneg_ae hnn (hIh.sub hIK)).1 hint
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- the stationary martingale has zero increments in `L²`
  have hmeas2 : Measurable fun x => hf x ^ 2 := hmeas.pow_const 2
  have h20 : ∀ x, 0 ≤ hf x ^ 2 := fun x => sq_nonneg _
  have h2C : ∀ x, hf x ^ 2 ≤ C ^ 2 := fun x =>
    pow_le_pow_left₀ (hpos x).le (hle x) 2
  set K2 : ℝ → ℝ := fun x => ∫ y, hf (n x y) ^ 2 ∂M.law with hK2
  have hstat2 : ∫ x, hf x ^ 2 ∂lam = ∫ x, K2 x ∂lam :=
    bw_coh_integral S hsupp hst hmeas2 h20 h2C
  have hK20 : ∀ x, 0 ≤ K2 x := fun x => integral_nonneg fun y => h20 _
  have hK2C : ∀ x, K2 x ≤ C ^ 2 := fun x => by
    have : K2 x ≤ ∫ _y, C ^ 2 ∂M.law :=
      integral_mono (hIy hmeas2 h20 h2C x) (integrable_const _) fun y => h2C _
    simpa using this
  have hIK2 : Integrable K2 lam := hbdd (bw_sm_integral S hmeas2) hK20 hK2C
  have hIh2 : Integrable (fun x => hf x ^ 2) lam := hbdd hmeas2.stronglyMeasurable h20 h2C
  set J : ℝ → ℝ := fun x => ∫ y, (hf (n x y) - hf x) ^ 2 ∂M.law with hJ
  have hJeq : ∀ x, J x = K2 x - 2 * hf x * K x + hf x ^ 2 := fun x => by
    have i1 := hIy hmeas2 h20 h2C x
    have i2 := hIy hmeas (fun z => (hpos z).le) hle x
    have : (fun y => (hf (n x y) - hf x) ^ 2) =
        fun y => hf (n x y) ^ 2 - 2 * hf x * hf (n x y) + hf x ^ 2 := by
      funext y; ring
    simp only [hJ, this]
    rw [integral_add (f := fun y => hf (n x y) ^ 2 - 2 * hf x * hf (n x y))
      (g := fun _ => hf x ^ 2) (i1.sub (i2.const_mul _)) (integrable_const _),
      integral_sub (f := fun y => hf (n x y) ^ 2) (g := fun y => 2 * hf x * hf (n x y)) i1
        (i2.const_mul _), integral_const_mul]
    simp
    rfl
  have hJae : J =ᵐ[lam] fun x => K2 x - hf x ^ 2 := by
    filter_upwards [hKh] with x hx
    rw [hJeq, hx]; ring
  have hJ0 : ∀ x, 0 ≤ J x := fun x => integral_nonneg fun y => sq_nonneg _
  have hIJ : Integrable J lam := (hIK2.sub hIh2).congr hJae.symm
  have hintJ : ∫ x, J x ∂lam = 0 := by
    rw [integral_congr_ae hJae, integral_sub hIK2 hIh2, hstat2, sub_self]
  have hJz := (integral_eq_zero_iff_of_nonneg (fun x => hJ0 x) hIJ).1 hintJ
  have hne : (ae lam).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero lam)
  obtain ⟨x, hx0, hx⟩ := (hJz.and (bw_ae_ge hsupp)).exists
  simp only [Pi.zero_apply] at hx0
  have hs0 := (S.sav_mem x hx).1
  have hy0 := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (hf (n x y) - hf x))
    ((hIy hmeas2 h20 h2C x).sub ((hIy hmeas (fun z => (hpos z).le) hle x).const_mul (2 * hf x))
      |>.add (integrable_const (hf x ^ 2)) |>.congr (ae_of_all _ fun y => by
        simp only [Pi.add_apply, Pi.sub_apply]; ring))).1 hx0
  -- `u′ ∘ c` is strictly decreasing, so `x′ = x` almost surely
  have hanti : StrictAntiOn hf (Set.Ici M.xmin) := by
    intro u hu v hv huv
    simp only [hhf, max_eq_left (Set.mem_Ici.1 hu), max_eq_left (Set.mem_Ici.1 hv)]
    exact M.du_anti (Set.mem_Ioi.2 (S.cons_pos hu)) (Set.mem_Ioi.2 (S.cons_pos hv))
      (S.lemma_8_3_1.1 hu hv huv)
  apply hnd (x - M.R * S.sav x + M.r * M.b)
  filter_upwards [hy0, M.ae_next hs0] with y hy hyn
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    sub_eq_zero] at hy
  have hnx : n x y = M.next (S.sav x) y := by simp only [hn, max_eq_left hx]
  rw [hnx] at hy
  have := hanti.injOn (Set.mem_Ici.2 hyn.1) (Set.mem_Ici.2 hx) hy
  simp only [SIModel.next] at this
  linarith

end Miao.IncompleteMarkets
