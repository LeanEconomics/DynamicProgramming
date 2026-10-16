/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LawsOfLargeNumbers.MarkovPaths
import LawsOfLargeNumbers.Riesz

/-!
# The strong law for Markov processes: Lemma 14.9 and Theorem 14.7

SLP §14.2, pp. 425–437. Assumption 14.1 is a compact metric `S` (the book: a compact subset of
`ℝˡ`), Assumption 14.2 the Feller property, Assumption 14.3 `Assumption14_3`.

* **Lemma 14.9** (`lemma_14_9`, p. 427): `(1/M) Σ_{m=1}^M Tᵐf → ∫ f dλ*` uniformly on `S`.
  It combines `lemma_14_9_of_repr` with the Riesz representation theorem (Theorem 14.14,
  `theorem_14_14_exists`).
* **Theorem 14.7** (`theorem_14_7`, Breiman's strong law, p. 425): for every `s₀` and every
  continuous `f`, `(1/N) Σ_{n=1}^N f(σₙ) → ∫ f dλ*`, `μ(s₀, ·)`-a.s. The proof is the book's: the
  splitting (1)–(2) of pp. 426–427, Lemma 14.8 for the first term and Lemma 14.9 for the second.

**Corrections.**
* Display (4) of p. 427 claims a threshold `N_m(ε)` uniform in `ω ∈ A_mᶜ`. Almost-everywhere
  convergence gives only a threshold depending on `ω`. The proof here lets every threshold depend
  on `ω`, which is all the conclusion needs.
* The introduction (p. 416) says that (3) holds when `S` is compact and `P` is Feller. That
  omits Assumption 14.3 (`feller_compact_not_enough`). On `S = {0, 1}` the identity kernel is
  Feller, but `(1/N) Σ f(sₙ) = f(s₀)`, so no single `λ*` serves for both starting points.
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-- **Lemma 14.9.** Under Assumptions 14.1–14.3, for every `f ∈ C(S)`,
`(1/M) Σ_{m=1}^M Tᵐf → ∫ f dλ*` uniformly on `S`. -/
theorem lemma_14_9 {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S]
    [BorelSpace S] (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) {lstar : Measure S}
    (hA : Assumption14_3 κ lstar) (f : S →ᵇ ℝ) :
    Tendsto (fun M : ℕ => ‖(M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM κ hF ^ (m + 1)) f -
      const S (∫ s, f s ∂lstar)‖) atTop (𝓝 0) :=
  lemma_14_9_of_repr κ hF hA theorem_14_14_exists f

/-- The powers of `T` on `C(S)` are the iterates of the Markov operator. -/
theorem markovCLM_pow_apply {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ) (m : ℕ) (s : S) :
    (markovCLM κ hF ^ m) f s = (markovOpR κ)^[m] f s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    change ∫ s', (markovCLM κ hF ^ m) f s' ∂κ s = _
    simp_rw [ih]
    rfl

/-- `|Σ_{n<N} aₙ − Σ_{n<N} a_{n+k}| ≤ 2kB` when `|aₙ| ≤ B`. -/
theorem abs_sum_sub_shift_le {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) (N k : ℕ) :
    |∑ n ∈ Finset.range N, a n - ∑ n ∈ Finset.range N, a (n + k)| ≤ 2 * k * B := by
  have h1 := Finset.sum_range_add a N k
  have h2 := Finset.sum_range_add a k N
  have hs : ∀ p : ℕ → ℕ, |∑ n ∈ Finset.range k, a (p n)| ≤ k * B := fun p => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Finset.range k) (fun n => |a (p n)|) B fun n _ => hB _
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have e1 := hs (fun n => N + n)
  have e2 := hs id
  have hshift : ∑ n ∈ Finset.range N, a (n + k) = ∑ n ∈ Finset.range N, a (k + n) :=
    Finset.sum_congr rfl fun n _ => by rw [add_comm]
  rw [hshift, add_comm N k] at *
  have : ∑ n ∈ Finset.range N, a n - ∑ n ∈ Finset.range N, a (k + n) =
      ∑ n ∈ Finset.range k, a n - ∑ n ∈ Finset.range k, a (N + n) := by linarith
  rw [this]
  simp only [id] at e2
  calc _ ≤ |∑ n ∈ Finset.range k, a n| + |∑ n ∈ Finset.range k, a (N + n)| := abs_sub _ _
    _ ≤ k * B + k * B := add_le_add e2 e1
    _ = 2 * k * B := by ring

/-- **Theorem 14.7** (the strong law of large numbers for Markov processes; Breiman 1960). Under
Assumptions 14.1–14.3, for every `s₀ ∈ S` and every continuous `f`,
`(1/N) Σ_{n=1}^N f(σₙ) → ∫ f dλ*`, `μ(s₀, ·)`-a.s. -/
theorem theorem_14_7 {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S]
    [BorelSpace S] (Q : Kernel S S) [IsMarkovKernel Q] (hF : IsFeller Q) {lstar : Measure S}
    (hA : Assumption14_3 Q lstar) (s₀ : S) (f : S →ᵇ ℝ) :
    ∀ᵐ ω ∂pathM Q s₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 0 N, f (ω n)) atTop
      (𝓝 (∫ s, f s ∂lstar)) := by
  set c := ∫ s, f s ∂lstar
  set g : ℕ → S → ℝ := fun m => (markovOpR Q)^[m] f
  have hB : ∀ s, |f s| ≤ ‖f‖ := fun s => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s
  have h9 := lemma_14_9 Q hF hA f
  filter_upwards [lemma_14_8_shift Q s₀ f.continuous.measurable hB] with ω hω
  -- the shifted form `(1/N) Σ_{n<N} f(σₙ) → c`
  have hcore : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (ω n)) atTop (𝓝 c) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Lemma 14.9: choose `M ≥ 1`
    obtain ⟨M, hMε, hM1⟩ := ((h9.eventually (gt_mem_nhds (half_pos hε))).and
      (eventually_ge_atTop 1)).exists
    set δ := ‖(M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM Q hF ^ (m + 1)) f - const S c‖
    have hH : ∀ s, |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) s - c| ≤ δ := fun s => by
      have := (((M : ℝ)⁻¹ • ∑ m ∈ Finset.range M, (markovCLM Q hF ^ (m + 1)) f -
        const S c)).norm_coe_le_norm s
      rw [Real.norm_eq_abs] at this
      convert this using 2
      simp only [coe_sub, coe_smul, coe_sum, Pi.sub_apply, Finset.sum_apply,
        const_apply, smul_eq_mul, markovCLM_pow_apply, g]
    -- Lemma 14.8 for `m = 1, …, M`, and the boundary terms
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM1
    have hev : ∀ᶠ N : ℕ in atTop, (∀ m ∈ Finset.range M, |(N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (f (ω (n + (m + 1))) - g (m + 1) (ω n))| < ε / 4) ∧
        (N : ℝ)⁻¹ * (2 * M * ‖f‖) < ε / 4 ∧ 1 ≤ N := by
      refine ((Filter.eventually_all_finset _).2 fun m _ => ?_).and (Eventually.and ?_ ?_)
      · have := (hω (m + 1)).eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 4))
        filter_upwards [this] with N hN
        rwa [Real.dist_eq, sub_zero] at hN
      · have : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * M * ‖f‖)) atTop (𝓝 0) := by
          simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 * (M : ℝ) * ‖f‖)
        exact this.eventually (gt_mem_nhds (by positivity))
      · exact eventually_ge_atTop 1
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨hA8, hbd, hN1⟩ := hN₀ N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    set avg := (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (ω n)
    set G : ℕ → ℝ := fun m => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, g (m + 1) (ω n)
    -- each `|avg − Gₘ| < ε/2`
    have hfirst : ∀ m ∈ Finset.range M, |avg - G m| < ε / 2 := fun m hm => by
      have hbnd := abs_sum_sub_shift_le (a := fun n => f (ω n)) (fun n => hB _) N (m + 1)
      have hdecomp : avg - G m = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (f (ω (n + (m + 1))) - g (m + 1) (ω n)) + (N : ℝ)⁻¹ * (∑ n ∈ Finset.range N, f (ω n) -
            ∑ n ∈ Finset.range N, f (ω (n + (m + 1)))) := by
        simp only [avg, G, Finset.sum_sub_distrib]
        ring
      have hm1 : ((m + 1 : ℕ) : ℝ) ≤ M := by
        have := Finset.mem_range.1 hm
        exact_mod_cast this
      have hb2 : |(N : ℝ)⁻¹ * (∑ n ∈ Finset.range N, f (ω n) -
          ∑ n ∈ Finset.range N, f (ω (n + (m + 1))))| < ε / 4 := by
        rw [abs_mul, abs_inv, Nat.abs_cast]
        refine lt_of_le_of_lt ?_ hbd
        refine mul_le_mul_of_nonneg_left (hbnd.trans ?_) (inv_nonneg.2 hNpos.le)
        have := norm_nonneg f
        nlinarith
      rw [hdecomp]
      exact (abs_add_le _ _).trans_lt (by linarith [hA8 m hm])
    -- the average over `m` of `Gₘ` is the time average of `(1/M) Σ_m T^{m+1}f`
    have hswap : (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, G m - c = (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, ((M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) (ω n) - c) := by
      simp only [G, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
      rw [Finset.sum_comm]
      field_simp
    have hsecond : |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, G m - c| < ε / 2 := by
      rw [hswap, abs_mul, abs_inv, Nat.abs_cast]
      refine lt_of_le_of_lt ?_ hMε
      have := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul (Finset.range N)
        (fun n => |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) (ω n) - c|) δ
        fun n _ => hH (ω n))
      rw [Finset.card_range, nsmul_eq_mul] at this
      calc (N : ℝ)⁻¹ * |∑ n ∈ Finset.range N,
            ((M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, g (m + 1) (ω n) - c)|
          ≤ (N : ℝ)⁻¹ * (N * δ) := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hNpos.le)
        _ = δ := by field_simp
    have hsplit : avg - c = (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, (avg - G m) +
        ((M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, G m - c) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring
    have hfirst' : |(M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, (avg - G m)| ≤ ε / 2 := by
      rw [abs_mul, abs_inv, Nat.abs_cast]
      have := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul (Finset.range M)
        (fun m => |avg - G m|) (ε / 2) fun m hm => (hfirst m hm).le)
      rw [Finset.card_range, nsmul_eq_mul] at this
      calc (M : ℝ)⁻¹ * |∑ m ∈ Finset.range M, (avg - G m)| ≤ (M : ℝ)⁻¹ * (M * (ε / 2)) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hM'.le)
        _ = ε / 2 := by field_simp
    rw [Real.dist_eq, hsplit]
    exact (abs_add_le _ _).trans_lt (by linarith)
  -- back to the book's `Σ_{n=1}^N`
  refine tendsto_avg_of_bounded_diff (C := 2 * ‖f‖) hcore fun N => ?_
  have hIoc : ∑ n ∈ Finset.Ioc 0 N, f (ω n) =
      ∑ n ∈ Finset.range N, f (ω n) + f (ω N) - f (ω 0) := by
    have h1 := Finset.sum_range_succ (fun n => f (ω n)) N
    have h2 : ∑ n ∈ Finset.range (N + 1), f (ω n) = f (ω 0) + ∑ n ∈ Finset.Ioc 0 N, f (ω n) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), Nat.succ_eq_add_one,
        Finset.Ico_add_one_add_one_eq_Ioc]
    linarith
  rw [hIoc]
  have := hB (ω N)
  have := hB (ω 0)
  rw [show ∑ n ∈ Finset.range N, f (ω n) + f (ω N) - f (ω 0) - ∑ n ∈ Finset.range N, f (ω n) =
    f (ω N) - f (ω 0) by ring]
  linarith [abs_sub (f (ω N)) (f (ω 0))]

/-! ### Compactness and the Feller property are not enough (p. 416) -/

theorem adjointOp_id {S : Type*} [MeasurableSpace S] (μ : Measure S) :
    adjointOp (Kernel.id : Kernel S S) μ = μ := by
  change μ.bind Kernel.id = μ
  have : (⇑(Kernel.id : Kernel S S)) = fun s => Measure.dirac s := funext Kernel.id_apply
  rw [this, Measure.bind_dirac]

/-- **Correction (p. 416).** On the compact space `S = {0, 1}` the identity kernel is Feller, yet
no `λ*` satisfies the strong law (3) of p. 416 for every starting point: Assumption 14.3 is
needed. -/
theorem feller_compact_not_enough :
    IsFeller (Kernel.id : Kernel Bool Bool) ∧
      ¬ ∃ lstar : Measure Bool, ∀ (s₀ : Bool) (f : Bool →ᵇ ℝ), ∀ᵐ ω ∂pathM Kernel.id s₀,
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 0 N, f (ω n)) atTop
          (𝓝 (∫ s, f s ∂lstar)) := by
  refine ⟨fun f _ _ => continuous_of_discreteTopology, ?_⟩
  rintro ⟨lstar, h⟩
  set fT : Bool →ᵇ ℝ := ofNormedAddCommGroupDiscrete indTrue 1 fun b => by
    cases b <;> simp [indTrue]
  have hval : ∀ s₀ : Bool, ∫ s, fT s ∂lstar = indTrue s₀ := fun s₀ => by
    have := isProbabilityMeasure_pathM (Kernel.id : Kernel Bool Bool) s₀
    have hid : ∀ n, (adjointOp (Kernel.id : Kernel Bool Bool))^[n] (Measure.dirac s₀) =
        Measure.dirac s₀ := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, adjointOp_id]
    have hcoord : ∀ n, ∀ᵐ ω ∂pathM (Kernel.id : Kernel Bool Bool) s₀, ω n = s₀ := fun n => by
      have hlaw := law_coord (Kernel.id : Kernel Bool Bool) s₀ n
      rw [hid n] at hlaw
      have : ∀ᵐ x ∂((pathM (Kernel.id : Kernel Bool Bool) s₀).map fun ω => ω n), x = s₀ := by
        rw [hlaw, ae_dirac_eq]
        exact eventually_pure.2 rfl
      exact ae_of_ae_map (measurable_pi_apply n).aemeasurable this
    obtain ⟨ω, hω1, hω2⟩ := ((ae_all_iff.2 hcoord).and (h s₀ fT)).exists
    have hseq : ∀ᶠ N : ℕ in atTop,
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 0 N, fT (ω n) = indTrue s₀ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (N : ℝ) ≠ 0 := by positivity
      simp only [hω1, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      change (N : ℝ)⁻¹ * (N * indTrue s₀) = indTrue s₀
      field_simp
    exact tendsto_nhds_unique hω2 (tendsto_const_nhds.congr' (hseq.mono fun N hN => hN.symm))
  have h1 := hval true
  have h0 := hval false
  rw [h1] at h0
  simp [indTrue] at h0

end StokeyLucasPrescott.LawsOfLargeNumbers
