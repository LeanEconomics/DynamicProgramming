/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackNet
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Dyadic transition probabilities: bounded errors, no CLT (post #3, codes (ii) and (iii))

Post #3 reports for the per-state Sobol stacks with a random digital shift (ii) or Owen
scrambling (iii) that "in the two-state chain every spell lasts exactly 8 periods" and that, "as
in the i.i.d. case, the RQMC estimators are typically not normally distributed". For **dyadic**
transition probabilities this is exact and holds for every realisation.

**Dyadic thresholds.** If `x = a / 2^L ∈ [0,1]` and the digits of every point are not eventually
constant (the good event, probability one), then an aligned `2^m`-block with `m ≥ L` has counting
error exactly `0` at `x` (`segErr_scrambledVdc_block_dyadic`): a point lies below `x` iff its
first `m` scrambled digits do. Hence every initial segment has error `≤ L`
(`abs_segErr_scrambledVdc_dyadic_le`), uniformly in its length.

**Chains** (`DyadicCumProb P L`: every `cs_{ij} ∈ 2^{-L} ℕ`; `dyadicCumProb_of_entries`). On the
good event, for every `T`:
* `abs_transCount_dyadic_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ 2L`;
* `abs_departureDiscrepancy_dyadic_le`: `|D_i(g, T)| ≤ V(g) L`;
* `abs_occCount_dyadic_sub_le`: `|N_s(T) − T π_s| ≤ 2M + n V(h) L`;
* `ae_abs_occCount_dyadic_owen_le`, `ae_abs_occCount_dyadic_shift_le`: almost surely, for all `T`.

**No CLT.** `not_tendstoInDistribution_of_card_le`: random variables taking, almost surely, at
most `K` values (a set that may depend on `T`) do not converge in distribution to any law
without atoms (portmanteau on `K + 1` disjoint intervals of positive limit mass, chosen by the
intermediate value theorem for the continuous CDF). `not_tendstoInDistribution_occCount_owen`,
`not_tendstoInDistribution_occCount_shift`: for a dyadic chain no normalisation
`(N_s(T) − T π_s − b_T) / a_T` converges in distribution to a law without atoms, in particular
not to `N(0,1)` (`not_tendstoInDistribution_occCount_owen_gaussian`).

**The post's two-state chain** `stackChain78` (`p₁₁ = p₂₂ = 7/8`): `h = (2, −2)` solves Poisson's
equation for `π = (1/2, 1/2)`; on the good event `|N_0(T) − T/2| ≤ 28` for all `T`
(`abs_occCount_stackChain78_le`), so `N_0(T) − T/2` lies in the fixed finite set
`{k/2 : |k| ≤ 56}` (`occCount_stackChain78_mem`), and there is no CLT under either randomisation
(`not_tendstoInDistribution_stackChain78_owen`, `not_tendstoInDistribution_stackChain78_shift`).

**Correction** (post #3, "normality cannot be rejected" / "typically not normally
distributed"): for codes (ii) and (iii) with dyadic transition probabilities, as in the post's
two-state chain, the occupation error is bounded and takes finitely many values, so it is not
asymptotically normal under any normalisation, for the digital shift *and* for Owen scrambling
(post #2's CLT for Owen-scrambled nets does not transfer to the Markov stack setting).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Finset Matrix Filter Topology

variable {n : ℕ}

/-! ### Finitely many values: no convergence to an atomless law -/

/-- The CDF of an atomless probability measure is continuous. -/
theorem continuous_cdf_of_noAtoms {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∀ x, ν {x} = 0) : Continuous (cdf ν) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [(monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim, (cdf ν).rightLim_eq]
  have h := (cdf ν).measure_singleton x
  rw [measure_cdf, hν x] at h
  have h1 : cdf ν x - Function.leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.1 h.symm
  have h2 : Function.leftLim (cdf ν) x ≤ cdf ν x := (monotone_cdf ν).leftLim_le le_rfl
  linarith

/-- An atomless probability measure on `ℝ` attains every CDF value in `(0,1)`. -/
theorem exists_cdf_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} = 0) {y : ℝ}
    (hy0 : 0 < y) (hy1 : y < 1) : ∃ t, cdf ν t = y := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds hy0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds hy1)).exists
  have hab : a ≤ b := by
    by_contra h
    linarith [monotone_cdf ν (not_le.1 h).le]
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hab
    (continuous_cdf_of_noAtoms hν).continuousOn ⟨ha.le, hb.le⟩
  exact ⟨t, ht⟩

/-- **Finitely many values rule out an atomless limit.** If, for every `T`, `W T` lies almost
surely in a finite set `S T` with at most `K` elements, then `W T` does not converge in
distribution to any `Z` whose law has no atoms. -/
theorem not_tendstoInDistribution_of_card_le {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {W : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {K : ℕ} (S : ℕ → Finset ℝ)
    (hS : ∀ T, (S T).card ≤ K) (hW : ∀ T, ∀ᵐ ω ∂μ, W T ω ∈ S T)
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution W atTop Z (fun _ => μ) μ' := by
  intro h
  set ν := μ'.map Z with hνdef
  -- quantiles `q l` with `F(q l) = (l + 1)/(K + 3)` for `l ≤ K + 1`
  have hq : ∀ l : ℕ, ∃ t, cdf ν t = ((min l (K + 1) : ℕ) + 1 : ℝ) / (K + 3) := by
    intro l
    have h1 : ((min l (K + 1) : ℕ) : ℝ) ≤ K + 1 := by exact_mod_cast min_le_right _ _
    refine exists_cdf_eq hZ (by positivity) ?_
    rw [div_lt_one (by positivity)]
    linarith
  choose q hq using hq
  have hqval : ∀ l ≤ K + 1, cdf ν (q l) = ((l : ℝ) + 1) / (K + 3) := by
    intro l hl
    rw [hq l, min_eq_left hl]
  have hqlt : ∀ l l', l < l' → l' ≤ K + 1 → q l < q l' := by
    intro l l' hll' hl'
    by_contra hcon
    have := monotone_cdf ν (not_lt.1 hcon)
    rw [hqval l (by omega), hqval l' hl'] at this
    have h2 : ((l : ℝ) + 1) < (l' : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right hll' 1
    have h3 : ((l' : ℝ) + 1) / (K + 3) ≤ ((l : ℝ) + 1) / (K + 3) := this
    rw [div_le_div_iff_of_pos_right (by positivity)] at h3
    linarith
  -- each piece `(q l, q (l+1)]`, `l ≤ K`, has limit mass `1/(K+3) > 0` and a null frontier
  have hpiece : ∀ l ∈ range (K + 1), ∀ᶠ T in atTop,
      0 < (μ.map (W T)) (Set.Ioc (q l) (q (l + 1))) := by
    intro l hl
    have hl' := mem_range.1 hl
    have hfr : ν (frontier (Set.Ioc (q l) (q (l + 1)))) = 0 := by
      rw [frontier_Ioc (hqlt l (l + 1) (by omega) (by omega))]
      refine measure_mono_null (Set.insert_subset_iff.2 ⟨Set.mem_insert _ _, ?_⟩)
        (measure_union_null (hZ (q l)) (hZ (q (l + 1))))
      simp
    have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto hfr
    have hpos : 0 < ν (Set.Ioc (q l) (q (l + 1))) := by
      have e := (cdf ν).measure_Ioc (q l) (q (l + 1))
      rw [measure_cdf, hqval l (by omega), hqval (l + 1) (by omega)] at e
      change 0 < ν (Set.Ioc (q l) (q (l + 1)))
      rw [e, ENNReal.ofReal_pos, ← sub_div, div_pos_iff_of_pos_right (by positivity)]
      push_cast
      linarith
    exact (tendsto_order.1 hlim).1 0 hpos
  obtain ⟨T, hT⟩ := ((eventually_all_finset (range (K + 1))).2 hpiece).exists
  -- each piece contains a point of `S T`
  have hpt : ∀ l ∈ range (K + 1), ∃ x ∈ S T, x ∈ Set.Ioc (q l) (q (l + 1)) := by
    intro l hl
    by_contra hcon
    push Not at hcon
    have hnull : μ (W T ⁻¹' Set.Ioc (q l) (q (l + 1))) = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hW T))
      intro hmem
      exact hcon _ hmem hω
    have := hT l hl
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable T) measurableSet_Ioc,
      hnull] at this
    exact lt_irrefl _ this
  choose! x hxS hxI using hpt
  -- distinct pieces give distinct points
  have hinj : Set.InjOn x (range (K + 1) : Set ℕ) := by
    intro l hl l' hl' hll'
    have hl1 := mem_range.1 hl
    have hl1' := mem_range.1 hl'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := (hxI l hl).2
      have h2 := (hxI l' hl').1
      have h3 : q (l + 1) ≤ q l' := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with he | he
        · exact le_of_eq (congrArg q he)
        · exact (hqlt _ _ he (by omega)).le
      rw [hll'] at h1
      linarith
    · have h1 := (hxI l' hl').2
      have h2 := (hxI l hl).1
      have h3 : q (l' + 1) ≤ q l := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with he | he
        · exact le_of_eq (congrArg q he)
        · exact (hqlt _ _ he (by omega)).le
      rw [← hll'] at h1
      linarith
  have hcard := card_le_card_of_injOn x (fun l hl => hxS l hl) hinj
  rw [card_range] at hcard
  linarith [hS T]

/-- An integer within `C` of `y` is `⌈y − C⌉ + r` for some `r ≤ ⌊2C⌋`. -/
theorem exists_eq_ceil_add_of_abs_le {y C : ℝ} {z : ℤ} (hz : |(z : ℝ) - y| ≤ C) :
    ∃ r < ⌊2 * C⌋₊ + 1, z = ⌈y - C⌉ + r := by
  have h1 := (abs_le.1 hz).1
  have h2 := (abs_le.1 hz).2
  have hc : ⌈y - C⌉ ≤ z := Int.ceil_le.2 (by linarith)
  have hc2 : ((⌈y - C⌉ : ℤ) : ℝ) ≥ y - C := Int.le_ceil _
  refine ⟨(z - ⌈y - C⌉).toNat, ?_, by omega⟩
  have hr : ((z - ⌈y - C⌉ : ℤ) : ℝ) ≤ 2 * C := by push_cast; linarith
  have hr0 : 0 ≤ z - ⌈y - C⌉ := by omega
  have : (z - ⌈y - C⌉).toNat ≤ ⌊2 * C⌋₊ := by
    refine Nat.le_floor ?_
    rw [show (((z - ⌈y - C⌉).toNat : ℕ) : ℝ) = ((z - ⌈y - C⌉ : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]]
    exact hr
  omega

/-- **Bounded integer errors rule out an atomless limit**: if `|Y T − y T| ≤ C` almost surely
with `Y T` integer-valued, no normalisation `(Y T − y T − b T) / a T` converges in distribution
to a law without atoms. -/
theorem not_tendstoInDistribution_of_abs_sub_le {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω → ℤ} {y : ℕ → ℝ} {C : ℝ}
    (hY : ∀ T, ∀ᵐ ω ∂μ, |(Y T ω : ℝ) - y T| ≤ C) (a b : ℕ → ℝ) {Z : Ω' → ℝ}
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω => ((Y T ω : ℝ) - y T - b T) / a T) atTop Z
      (fun _ => μ) μ' := by
  refine not_tendstoInDistribution_of_card_le (K := ⌊2 * C⌋₊ + 1)
    (fun T => (range (⌊2 * C⌋₊ + 1)).image fun r : ℕ =>
      (((⌈y T - C⌉ + r : ℤ) : ℝ) - y T - b T) / a T)
    (fun T => card_image_le.trans (card_range _).le) (fun T => ?_) hZ
  filter_upwards [hY T] with ω hω
  obtain ⟨r, hr, hz⟩ := exists_eq_ceil_add_of_abs_le hω
  exact mem_image.2 ⟨r, mem_range.2 hr, by rw [hz]⟩

/-! ### Dyadic thresholds -/

/-- **Dyadic thresholds split aligned blocks exactly**: if no digit sequence of the points is
eventually constant, then at a threshold `a' / 2^L ≤ 1` every aligned `2^m`-block with `m ≥ L`
has counting error `0`. -/
theorem segErr_scrambledVdc_block_dyadic {f : ℕ → ℕ → Bool}
    (hf : ∀ k, NotEventuallyConst (scrambledDigit f k)) {L a' m : ℕ} (hm : L ≤ m)
    (hx1 : (a' : ℝ) / 2 ^ L ≤ 1) (a : ℕ) :
    segErr (scrambledVdc f) ((a' : ℝ) / 2 ^ L) (a * 2 ^ m) (2 ^ m) = 0 := by
  rw [segErr_eq_card]
  set c := a' * 2 ^ (m - L) with hc
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hpL : (0 : ℝ) < 2 ^ L := by positivity
  have hcx : (c : ℝ) = 2 ^ m * ((a' : ℝ) / 2 ^ L) := by
    have h2 : (2 : ℝ) ^ m = 2 ^ (m - L) * 2 ^ L := by rw [← pow_add, Nat.sub_add_cancel hm]
    rw [hc, h2]
    push_cast
    field_simp
  have hcm : c ≤ 2 ^ m := by
    have : (c : ℝ) ≤ 2 ^ m := by rw [hcx]; nlinarith
    exact_mod_cast this
  have hxc : (a' : ℝ) / 2 ^ L * 2 ^ m = c := by rw [hcx]; ring
  have hset : (range (2 ^ m)).filter
      (fun k => scrambledVdc f (a * 2 ^ m + k) ≤ (a' : ℝ) / 2 ^ L) =
      (range (2 ^ m)).filter (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m < c) := by
    refine filter_congr fun k _ => ?_
    constructor
    · intro hle
      by_contra hcon
      have hk : (c : ℝ) ≤ (digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m : ℕ) := by
        exact_mod_cast not_lt.1 hcon
      have h := digitPrefix_div_lt_binaryVal (hf (a * 2 ^ m + k)) m
      rw [div_lt_iff₀ hp] at h
      have h3 : scrambledVdc f (a * 2 ^ m + k) * 2 ^ m ≤ (a' : ℝ) / 2 ^ L * 2 ^ m :=
        mul_le_mul_of_nonneg_right hle hp.le
      change (digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m : ℝ) <
        scrambledVdc f (a * 2 ^ m + k) * 2 ^ m at h
      linarith
    · intro hlt
      have hk : ((digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m : ℕ) : ℝ) + 1 ≤ c := by
        exact_mod_cast hlt
      have h := binaryVal_le_digitPrefix_add_one_div (scrambledDigit f (a * 2 ^ m + k)) m
      refine h.trans ?_
      rw [div_le_iff₀ hp]
      linarith
  have hcard := card_filter_digitPrefix_block f a m (· < c)
  rw [hset, hcard, card_filter_lt_range, min_eq_left hcm]
  push_cast
  rw [hcx]
  ring

/-- **Dyadic thresholds: bounded error for every initial segment** (on the good event):
`|#{k < N : u k ≤ a'/2^L} − N a'/2^L| ≤ L`, uniformly in `N`. -/
theorem abs_segErr_scrambledVdc_dyadic_le {f : ℕ → ℕ → Bool}
    (hf : ∀ k, NotEventuallyConst (scrambledDigit f k)) {L a' : ℕ}
    (hx1 : (a' : ℝ) / 2 ^ L ≤ 1) (N : ℕ) :
    |segErr (scrambledVdc f) ((a' : ℝ) / 2 ^ L) 0 N| ≤ L := by
  have hx0 : (0 : ℝ) ≤ (a' : ℝ) / 2 ^ L := by positivity
  have hβ : ∀ m a, |segErr (scrambledVdc f) ((a' : ℝ) / 2 ^ L) (a * 2 ^ m) (2 ^ m)| ≤
      (if m < L then (1 : ℝ) else 0) := by
    intro m a
    split_ifs with hm
    · exact abs_segErr_scrambledVdc_block_le f m a hx0 hx1
    · rw [segErr_scrambledVdc_block_dyadic hf (not_lt.1 hm) hx1 a, abs_zero]
  set m := max L (Nat.log 2 N + 1)
  have hN : N < 2 ^ m := (Nat.lt_pow_succ_log_self (by norm_num) N).trans_le
    (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have h := abs_segErr_prefix_le hβ m 0 N hN
  rw [zero_mul] at h
  refine h.trans ?_
  rw [sum_boole]
  have : ((range m).filter fun j => j < L).card ≤ L := by
    calc ((range m).filter fun j => j < L).card ≤ (range L).card :=
          card_le_card fun j hj => by
            simp only [mem_filter, mem_range] at hj ⊢
            exact hj.2
      _ = L := card_range L
  exact_mod_cast this

/-! ### Chains with dyadic transition probabilities -/

/-- **Dyadic cumulative sums**: every `cs_{i,m}` is in `2^{-L} ℕ`. -/
def DyadicCumProb (P : Fin n → Fin n → ℝ) (L : ℕ) : Prop :=
  ∀ i (m : ℕ), ∃ a : ℕ, cumProb P i m = a / 2 ^ L

/-- Dyadic entries give dyadic cumulative sums. -/
theorem dyadicCumProb_of_entries {P : Fin n → Fin n → ℝ} {L : ℕ}
    (h : ∀ i j, ∃ a : ℕ, P i j = a / 2 ^ L) : DyadicCumProb P L := by
  intro i m
  choose A hA using h
  refine ⟨∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < m), A i k, ?_⟩
  unfold cumProb
  push_cast
  rw [sum_div]
  exact sum_congr rfl fun k _ => hA i k

variable {P : Fin n → Fin n → ℝ}

/-- One dyadic threshold of a stack: `|#{k < N : step < m} − N cs_{i,m}| ≤ L` on the good
event. -/
theorem abs_departuresBelow_dyadic_sub_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (i : Fin n) {f : ℕ → ℕ → Bool} (hf : ∀ k, NotEventuallyConst (scrambledDigit f k))
    (N m : ℕ) :
    |(departuresBelow P i (scrambledVdc f) N m : ℝ) - N * cumProb P i m| ≤ L := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : departuresBelow P i (scrambledVdc f) N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    rw [h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  have e : departuresBelow P i (scrambledVdc f) N m =
      ((range N).filter fun k => scrambledVdc f (0 + k) ≤ cumProb P i m).card := by
    unfold departuresBelow
    congr 1
    refine filter_congr fun k _ => ?_
    rw [zero_add]
    exact step_lt_iff hP i (scrambledVdc_mem_Icc f k).2 hm
  rw [e]
  have h := card_filter_segment_sub_eq_segErr (scrambledVdc f) (cumProb P i m) 0 N
  rw [card_range] at h
  rw [h]
  obtain ⟨a', ha'⟩ := hdy i m
  have hx1 := (cumProb_mem_Icc hP i m).2
  rw [ha'] at hx1 ⊢
  exact abs_segErr_scrambledVdc_dyadic_le hf hx1 N

/-- **Dyadic chains: bounded transition errors** (on the good event, every `T`):
`|N_ij(T) − p_ij N_i(T)| ≤ 2L`. -/
theorem abs_transCount_dyadic_sub_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack f)) i T| ≤ 2 * L := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) i T
  rw [transCount_stackDrive]
  have hv : scrambledStack f i = scrambledVdc (f i) := rfl
  rw [hv, card_step_eq_eq_sub]
  have e : (departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) -
        departuresBelow P i (scrambledVdc (f i)) N j - P i j * N =
      ((departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)) -
        ((departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j) := by
    rw [cumProb_succ]
    ring
  rw [e]
  have h1 := abs_departuresBelow_dyadic_sub_le hP hdy i (hf i) N (j + 1)
  have h2 := abs_departuresBelow_dyadic_sub_le hP hdy i (hf i) N j
  calc _ ≤ |(departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)| +
        |(departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Dyadic chains: bounded departure discrepancy**: `|D_i(g, T)| ≤ V(g) L` on the good
event. -/
theorem abs_departureDiscrepancy_dyadic_le (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f)
    (g : Fin n → ℝ) (i : Fin n) (T : ℕ) :
    |departureDiscrepancy P g (stackPath P x₀ (scrambledStack f)) i T| ≤ stateVariation g * L := by
  refine (congrArg abs (departureDiscrepancy_stackDrive P g (step P) x₀ (scrambledStack f) i
    T)).trans_le ?_
  refine abs_sum_step_sub_le_of_count hP i (fun k _ => (scrambledVdc_mem_Icc (f i) k).2)
    (fun m _ => ?_) g
  have h := card_filter_segment_sub_eq_segErr (scrambledVdc (f i)) (cumProb P i m) 0
    (occCount (stackPath P x₀ (scrambledStack f)) i T)
  simp only [zero_add] at h
  change |(((range (occCount (stackPath P x₀ (scrambledStack f)) i T)).filter
    fun k => scrambledVdc (f i) k ≤ cumProb P i m).card : ℝ) -
      (range (occCount (stackPath P x₀ (scrambledStack f)) i T)).card * cumProb P i m| ≤ L
  rw [h]
  obtain ⟨a', ha'⟩ := hdy i m
  have hx1 := (cumProb_mem_Icc hP i m).2
  rw [ha'] at hx1 ⊢
  exact abs_segErr_scrambledVdc_dyadic_le (hf i) hx1 _

/-- **Dyadic chains: bounded occupation error** (on the good event, uniformly in `T`):
`|N_s(T) − T π_s| ≤ 2M + n V(h) L`. -/
theorem abs_occCount_dyadic_sub_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) (T : ℕ) :
    |(occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * L := by
  refine (abs_occCount_sub_le P hh hM _ T).trans (add_le_add le_rfl ?_)
  calc ∑ i, |departureDiscrepancy P h (stackPath P x₀ (scrambledStack f)) i T|
      ≤ ∑ _i : Fin n, stateVariation h * L :=
        sum_le_sum fun i _ => abs_departureDiscrepancy_dyadic_le hP hdy x₀ hf h i T
    _ = n * stateVariation h * L := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Under Owen scrambling, almost surely the occupation error of a dyadic chain is bounded by
`2M + n V(h) L` for all `T`. -/
theorem ae_abs_occCount_dyadic_owen_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂owenMeasure n, ∀ T,
      |(occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c| ≤
        2 * M + n * stateVariation h * L :=
  (ae_isGoodTable_owen n).mono fun _ hω T => abs_occCount_dyadic_sub_le hP hdy x₀ hω hh hM T

/-- Under the digital shift, almost surely the occupation error of a dyadic chain is bounded
by `2M + n V(h) L` for all `T`. -/
theorem ae_abs_occCount_dyadic_shift_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂shiftMeasure n, ∀ T,
      |(occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℝ) - T * c| ≤
        2 * M + n * stateVariation h * L :=
  (ae_isGoodTable_shift n).mono fun _ hω T => abs_occCount_dyadic_sub_le hP hdy x₀ hω hh hM T

/-- **No CLT for a dyadic chain under Owen scrambling**: no normalisation
`(N_s(T) − T π_s − b_T) / a_T` converges in distribution to a law without atoms. -/
theorem not_tendstoInDistribution_occCount_owen (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c - b T) / a T)
      atTop Z (fun _ => owenMeasure n) μ' := by
  have := not_tendstoInDistribution_of_abs_sub_le (μ := owenMeasure n)
    (Y := fun T ω => (occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℤ))
    (y := fun T => T * c) (C := 2 * M + n * stateVariation h * L)
    (fun T => (ae_abs_occCount_dyadic_owen_le hP hdy x₀ hh hM).mono fun ω hω => by
      simpa only [Int.cast_natCast] using hω T) a b hZ
  simpa only [Int.cast_natCast] using this

/-- **No CLT for a dyadic chain under the digital shift.** -/
theorem not_tendstoInDistribution_occCount_shift (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℝ) - T * c - b T) / a T)
      atTop Z (fun _ => shiftMeasure n) μ' := by
  have := not_tendstoInDistribution_of_abs_sub_le (μ := shiftMeasure n)
    (Y := fun T ω => (occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℤ))
    (y := fun T => T * c) (C := 2 * M + n * stateVariation h * L)
    (fun T => (ae_abs_occCount_dyadic_shift_le hP hdy x₀ hh hM).mono fun ω hω => by
      simpa only [Int.cast_natCast] using hω T) a b hZ
  simpa only [Int.cast_natCast] using this

/-- The standard normal law has no atoms. -/
theorem map_id_gaussianReal_singleton (x : ℝ) : (gaussianReal 0 1).map id {x} = 0 := by
  rw [Measure.map_id]
  exact (nullSingletonClass_gaussianReal one_ne_zero).measure_singleton x

/-- **No normalisation of a dyadic chain's occupation error is asymptotically `N(0,1)`** under
Owen scrambling. -/
theorem not_tendstoInDistribution_occCount_owen_gaussian (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (a b : ℕ → ℝ) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c - b T) / a T)
      atTop id (fun _ => owenMeasure n) (gaussianReal 0 1) :=
  not_tendstoInDistribution_occCount_owen hP hdy x₀ hh hM a b map_id_gaussianReal_singleton

/-! ### The post's two-state chain, `p₁₁ = p₂₂ = 7/8` -/

/-- The two-state chain of post #3 with `p₁₁ = p₂₂ = 7/8` (mean spell length `8`). -/
noncomputable def stackChain78 : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 7 / 8 else 1 / 8

/-- `stackChain78` is stochastic. -/
theorem isStochastic_stackChain78 : IsStochastic stackChain78 where
  nonneg i j := by unfold stackChain78; split_ifs <;> norm_num
  sum_eq_one i := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [stackChain78] <;> norm_num

/-- Its entries are multiples of `2^{-3}`. -/
theorem dyadicCumProb_stackChain78 : DyadicCumProb stackChain78 3 :=
  dyadicCumProb_of_entries fun i j => ⟨if i = j then 7 else 1, by
    unfold stackChain78
    split_ifs <;> norm_num⟩

/-- The solution `h = (2, −2)` of Poisson's equation `h − Ph = 1_{0} − 1/2`. -/
noncomputable def poisson78 : Fin 2 → ℝ := fun i => if i = 0 then 2 else -2

/-- `h = (2, −2)` solves `h − Ph = 1_{0} − 1/2`. -/
theorem poisson78_spec (i : Fin 2) :
    poisson78 i - (stackChain78 *ᵥ poisson78) i = (if i = 0 then 1 else 0) - 1 / 2 := by
  fin_cases i <;> simp [poisson78, stackChain78, mulVec, dotProduct, Fin.sum_univ_two] <;>
    norm_num

/-- `|h| ≤ 2`. -/
theorem abs_poisson78_le (i : Fin 2) : |poisson78 i| ≤ 2 := by
  unfold poisson78
  split_ifs <;> norm_num

/-- `V(h) = 4`. -/
theorem stateVariation_poisson78 : stateVariation poisson78 = 4 := by
  simp [stateVariation, extendNat, poisson78]
  norm_num

/-- **The two-state 7/8 chain: bounded occupation error** for every good flip table:
`|N_0(T) − T/2| ≤ 28` for all `T` (Owen scrambling and digital shift alike). -/
theorem abs_occCount_stackChain78_le (x₀ : Fin 2) {f : Fin 2 → ℕ → ℕ → Bool}
    (hf : IsGoodTable f) (T : ℕ) :
    |(occCount (stackPath stackChain78 x₀ (scrambledStack f)) 0 T : ℝ) - T / 2| ≤ 28 := by
  have h := abs_occCount_dyadic_sub_le isStochastic_stackChain78 dyadicCumProb_stackChain78 x₀
    hf poisson78_spec abs_poisson78_le T
  rw [stateVariation_poisson78] at h
  rw [div_eq_mul_one_div (T : ℝ) 2]
  norm_num at h ⊢
  linarith

/-- **A fixed finite set of values** (post #3, "every spell lasts exactly 8 periods"): on the
good event, `N_0(T) − T/2 ∈ {k/2 : |k| ≤ 56}` for every `T`. -/
theorem occCount_stackChain78_mem (x₀ : Fin 2) {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f)
    (T : ℕ) : (occCount (stackPath stackChain78 x₀ (scrambledStack f)) 0 T : ℝ) - T / 2 ∈
      (Finset.Icc (-56 : ℤ) 56).image fun k : ℤ => (k : ℝ) / 2 := by
  set N := occCount (stackPath stackChain78 x₀ (scrambledStack f)) 0 T
  have h := abs_occCount_stackChain78_le x₀ hf T
  refine mem_image.2 ⟨2 * N - T, ?_, by push_cast; ring⟩
  have h2 : |((2 * N - T : ℤ) : ℝ)| ≤ 56 := by
    push_cast
    rw [show (2 : ℝ) * N - T = 2 * ((N : ℝ) - T / 2) by ring, abs_mul, abs_two]
    linarith
  rw [abs_le] at h2
  have h3 : (-56 : ℤ) ≤ 2 * N - T := by exact_mod_cast h2.1
  have h4 : (2 * N - T : ℤ) ≤ 56 := by exact_mod_cast h2.2
  exact Finset.mem_Icc.2 ⟨h3, h4⟩

/-- **No CLT for the 7/8 chain under Owen scrambling** (post #3, code (iii)). -/
theorem not_tendstoInDistribution_stackChain78_owen (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → ℝ}
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath stackChain78 x₀ (scrambledStack (owenTable ω))) 0 T : ℝ) -
        T * (1 / 2) - b T) / a T) atTop Z (fun _ => owenMeasure 2) μ' :=
  not_tendstoInDistribution_occCount_owen isStochastic_stackChain78 dyadicCumProb_stackChain78
    x₀ poisson78_spec abs_poisson78_le a b hZ

/-- **No CLT for the 7/8 chain under the digital shift** (post #3, code (ii)). -/
theorem not_tendstoInDistribution_stackChain78_shift (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → ℝ}
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath stackChain78 x₀ (scrambledStack (shiftFlips ω))) 0 T : ℝ) -
        T * (1 / 2) - b T) / a T) atTop Z (fun _ => shiftMeasure 2) μ' :=
  not_tendstoInDistribution_occCount_shift isStochastic_stackChain78 dyadicCumProb_stackChain78
    x₀ poisson78_spec abs_poisson78_le a b hZ

end RQMCMarkov.ScrambledStacks
