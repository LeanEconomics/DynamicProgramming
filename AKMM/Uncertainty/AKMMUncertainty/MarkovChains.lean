/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainStationary
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Markov chains

AKMM, §7.1.2, pp. 189–190 (with fns. 2–3). A Markov chain on a finite set `S` has a
row-stochastic transition matrix `P` and distributions are row vectors `π`, so `π_{t+1} = π_tP`
is `π ᵥ* P`. The stationary-distribution machinery is Miao's `MarkovProcesses`
(`mc_IsStationary`, `mc_IsIrreducible`, `theorem_3_1_3`, `mc_irreducible_stationary`).

* `π₁ = π₀P` entrywise, as the product of `π₀` with the `j`th column of `P`
  (`markov_marginal_column`); `π_{t+k} = π_tPᵏ` (`markov_marginal_pow`).
* Stationarity is the unit-eigenvector condition `P'π̄' = π̄'` (`markov_stationary_iff_eigen`);
  fn. 2: `P1 = 1`, and both `P` and `P'` have the eigenvalue `1` (`markov_unit_eigenvalue`).
* The employment chain: `ū = s/(s + f)` is the unique stationary distribution
  (`employment_stationary_iff`, `employment_unique`); fn. 3, `u_{t+1} = s + (1 − f − s)u_t`
  (`employment_law`), the solution (`employment_closed_form`, `employment_fn3`, with
  `employment_fn3_printed_counterexample`) and convergence (`employment_converges`).
* The identity and the flip matrix (`identity_stationary`, `identity_not_unique`,
  `flip_stationary_iff`, `flip_oscillates`, `flip_not_converge`).
* The convergence conditions: `P ≫ 0` suffices (`positive_matrix_converges`), is not necessary
  (`positive_matrix_not_necessary`), and the book's "positive probability of moving to any other
  state" is not sufficient (`offdiag_positive_not_sufficient`).
* The book's definitions of reachability, irreducibility and aperiodicity (`ak_Reachable`,
  `ak_Irreducible`, `ak_Aperiodic`); irreducibility agrees with Miao's
  (`ak_irreducible_iff`); an irreducible chain has a unique stationary distribution
  (`markov_irreducible_unique`), and if it is also aperiodic `π₀Pᵗ → π̄` for every `π₀`
  (`markov_irreducible_aperiodic_converges`).

Departures: the definition of aperiodicity is corrected (the printed one conditions on `x_n`
rather than `x_0` and so forces `P_ii > 0`: `aperiodic_printed_iff`,
`aperiodic_printed_counterexample`); the column in "the product of `π₀` against the `i`th
column" is the `j`th; the solution in fn. 3 is corrected.
-/

namespace AKMM.Uncertainty

open Matrix Filter Topology Miao.MarkovProcesses

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Marginal distributions -/

omit [DecidableEq S] in
/-- AKMM, p. 189 (corrected): `Pr[x₁ = x̄ⱼ] = Σᵢ Pᵢⱼ[π₀]ᵢ` is the product of `π₀` with the
`j`th column of `P` (the book says the `i`th). -/
theorem markov_marginal_column (P : Matrix S S ℝ) (p₀ : S → ℝ) (j : S) :
    (p₀ ᵥ* P) j = ∑ i, P i j * p₀ i ∧ (p₀ ᵥ* P) j = p₀ ⬝ᵥ (fun i => P i j) := by
  refine ⟨?_, rfl⟩
  simp only [vecMul, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- AKMM, p. 189: if `π_{t+1} = π_tP` for all `t`, then `π_{t+k} = π_tPᵏ`. -/
theorem markov_marginal_pow (P : Matrix S S ℝ) (pv : ℕ → S → ℝ)
    (h : ∀ t, pv (t + 1) = pv t ᵥ* P) (t k : ℕ) : pv (t + k) = pv t ᵥ* P ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, h, ih, vecMul_vecMul, pow_succ]

/-! ### Stationary distributions as unit eigenvectors -/

omit [DecidableEq S] in
/-- AKMM, p. 189: `π̄ = π̄P` iff `P'π̄' = π̄'`, i.e. `π̄'` is an eigenvector of `P'` with
eigenvalue one (when `π̄ ≠ 0`, e.g. when it is a distribution). -/
theorem markov_stationary_iff_eigen (P : Matrix S S ℝ) (pv : S → ℝ) :
    pv ᵥ* P = pv ↔ Pᵀ *ᵥ pv = pv := by
  rw [mulVec_transpose]

/-- AKMM, fn. 2, p. 189: a transition matrix has the unit eigenvalue, since `P1 = 1`, and so
does `P'` (its unit eigenvector is a stationary distribution). -/
theorem markov_unit_eigenvalue [Nonempty S] {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) :
    P *ᵥ (fun _ => 1) = (fun _ => 1) ∧
      Module.End.HasEigenvalue (Matrix.toLin' P) 1 ∧
      Module.End.HasEigenvalue (Matrix.toLin' Pᵀ) 1 := by
  have h1 : P *ᵥ (fun _ => 1) = (fun _ => 1) := by
    funext i
    simp only [mulVec, dotProduct, mul_one]
    exact (mem_rowStochastic_iff_sum.1 hP).2 i
  refine ⟨h1, ?_, ?_⟩
  · refine Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ => (1 : ℝ)) ⟨?_, ?_⟩
    · rw [Module.End.mem_genEigenspace_one, Matrix.toLin'_apply, h1, one_smul]
    · intro h0
      have := congrFun h0 (Classical.arbitrary S)
      simp at this
  · obtain ⟨μ, hμ, -⟩ := mc_exists_stationary hP (Classical.arbitrary S)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := μ) ⟨?_, ?_⟩
    · rw [Module.End.mem_genEigenspace_one, Matrix.toLin'_apply, one_smul]
      exact (markov_stationary_iff_eigen P μ).1 hμ.2.2
    · intro h0
      have h := hμ.2.1
      rw [h0] at h
      simp at h

/-! ### The employment chain -/

/-- AKMM, p. 189: the employment–unemployment chain with separation rate `s` and job-finding
rate `f` (state `0` employed, state `1` unemployed). -/
def employmentP (s f : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - s, s; f, 1 - f]

theorem employment_mem {s f : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    employmentP s f ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [employmentP] <;> linarith
  · fin_cases i <;> simp [employmentP, Fin.sum_univ_two]

/-- AKMM, p. 190: `π̄ = [1 − ū, ū]` is stationary iff `ū = s(1 − ū) + (1 − f)ū` iff
`ū = s/(s + f)`. -/
theorem employment_stationary_iff {s f u : ℝ} (hsf : 0 < s + f) :
    (![1 - u, u] ᵥ* employmentP s f = ![1 - u, u] ↔ u = s * (1 - u) + (1 - f) * u) ∧
      (u = s * (1 - u) + (1 - f) * u ↔ u = s / (s + f)) := by
  constructor
  · constructor
    · intro h
      have := congrFun h 1
      simp [vecMul, dotProduct, employmentP, Fin.sum_univ_two] at this
      linarith
    · intro h
      funext j
      fin_cases j <;> simp [vecMul, dotProduct, employmentP, Fin.sum_univ_two] <;> linarith
  · rw [eq_div_iff hsf.ne']
    constructor <;> intro h <;> linarith

/-- AKMM, p. 190: "there is a unique stationary distribution of this economy":
`[f/(s + f), s/(s + f)]`. -/
theorem employment_unique {s f : ℝ} (hs0 : 0 ≤ s) (hf0 : 0 ≤ f) (hsf : 0 < s + f) (μ : Fin 2 → ℝ) :
    mc_IsStationary (employmentP s f) μ ↔ μ = ![f / (s + f), s / (s + f)] := by
  have hne := hsf.ne'
  constructor
  · rintro ⟨-, hsum, hfix⟩
    rw [Fin.sum_univ_two] at hsum
    have h1 : μ 1 = s / (s + f) := by
      have := congrFun hfix 1
      simp [vecMul, dotProduct, employmentP, Fin.sum_univ_two] at this
      rw [eq_div_iff hne]
      nlinarith
    funext j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [eq_div_iff hne]
      rw [eq_div_iff hne] at h1
      nlinarith
    · simpa using h1
  · rintro rfl
    refine ⟨fun i => ?_, ?_, ?_⟩
    · fin_cases i
      · exact div_nonneg hf0 hsf.le
      · exact div_nonneg hs0 hsf.le
    · simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      ring
    · funext j
      fin_cases j <;> simp [vecMul, dotProduct, employmentP, Fin.sum_univ_two] <;>
        field_simp <;> ring

/-- AKMM, fn. 3, p. 190: along `π_{t+1} = π_tP` with `π_t = [1 − u_t, u_t]`, the unemployment
rate follows `u_{t+1} = s(1 − u_t) + (1 − f)u_t = s + (1 − f − s)u_t`. -/
theorem employment_law (s f u : ℝ) :
    (![1 - u, u] ᵥ* employmentP s f) 1 = s * (1 - u) + (1 - f) * u ∧
      s * (1 - u) + (1 - f) * u = s + (1 - f - s) * u := by
  refine ⟨?_, by ring⟩
  simp [vecMul, dotProduct, employmentP, Fin.sum_univ_two]
  ring

/-- AKMM, fn. 3, p. 190: the solution of `u_{t+1} = s + λu_t`, `λ = 1 − f − s`, is
`u_t = ū + λᵗ(u₀ − ū)` with `ū = s/(s + f)`. -/
theorem employment_closed_form {s f : ℝ} (hsf : 0 < s + f) (u : ℕ → ℝ)
    (hu : ∀ t, u (t + 1) = s + (1 - f - s) * u t) (t : ℕ) :
    u t = s / (s + f) + (1 - f - s) ^ t * (u 0 - s / (s + f)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hu, ih, pow_succ]
    field_simp
    ring

/-- AKMM, fn. 3, p. 190 (corrected): by repeated substitution
`u_t = s(1 + λ + ⋯ + λ^{t−1}) + λᵗu₀`. -/
theorem employment_fn3 (s lam : ℝ) (u : ℕ → ℝ) (hu : ∀ t, u (t + 1) = s + lam * u t) (t : ℕ) :
    u t = s * ∑ i ∈ Finset.range t, lam ^ i + lam ^ t * u 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hu, ih, Finset.sum_range_succ', pow_zero, pow_succ]
    have h : ∑ i ∈ Finset.range t, lam ^ (i + 1) = lam * ∑ i ∈ Finset.range t, lam ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h]
    ring

/-- AKMM, fn. 3, p. 190: the printed solution `u_t = s(1 + λ + ⋯ + λᵗu₀)` is false: with
`s = f = 1/4` (`λ = 1/2`) and `u₀ = 1`, `u₁ = 3/4` while the printed formula gives `3/8`. -/
theorem employment_fn3_printed_counterexample :
    let s : ℝ := 1 / 4
    let lam : ℝ := 1 - 1 / 4 - 1 / 4
    s + lam * 1 = 3 / 4 ∧ s * (∑ i ∈ Finset.range 1, lam ^ i + lam ^ 1 * 1) ≠ 3 / 4 := by
  norm_num

/-- AKMM, p. 190 and fn. 3: with `s, f ∈ (0, 1)` the unemployment rate converges to
`ū = s/(s + f)` from every `u₀`. -/
theorem employment_converges {s f : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hf0 : 0 < f) (hf1 : f < 1)
    (u : ℕ → ℝ) (hu : ∀ t, u (t + 1) = s + (1 - f - s) * u t) :
    Tendsto u atTop (𝓝 (s / (s + f))) := by
  have hsf : 0 < s + f := by linarith
  have hlam : |1 - f - s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hlam
  have := (hp.mul_const (u 0 - s / (s + f))).const_add (s / (s + f))
  simp only [zero_mul, add_zero] at this
  exact this.congr fun t => (employment_closed_form hsf u hu t).symm

/-! ### The identity and the flip matrix -/

/-- AKMM, p. 190: with `P = I` every distribution is stationary and `π₀Pᵗ = π₀`. -/
theorem identity_stationary (μ : S → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) :
    mc_IsStationary (1 : Matrix S S ℝ) μ ∧ ∀ t : ℕ, μ ᵥ* (1 : Matrix S S ℝ) ^ t = μ :=
  ⟨⟨hμ0, hμ1, vecMul_one μ⟩, fun t => by rw [one_pow, vecMul_one]⟩

/-- AKMM, p. 190: with `P = I` the stationary distribution is not unique (two states). -/
theorem identity_not_unique :
    mc_IsStationary (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] ∧
      mc_IsStationary (1 : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] ∧
      (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
  refine ⟨(identity_stationary _ (fun i => ?_) (by simp)).1,
    (identity_stationary _ (fun i => ?_) (by simp)).1, ?_⟩
  · fin_cases i <;> simp
  · fin_cases i <;> simp
  · intro h
    have := congrFun h 0
    simp at this

/-- AKMM, p. 190: the flip matrix `[0 1; 1 0]`. -/
def flipP : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem flip_mem : flipP ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [flipP]
  · fin_cases i <;> simp [flipP, Fin.sum_univ_two]

/-- AKMM, p. 190: the flip matrix has the unique stationary distribution `[1/2, 1/2]`. -/
theorem flip_stationary_iff (μ : Fin 2 → ℝ) : mc_IsStationary flipP μ ↔ μ = ![1 / 2, 1 / 2] := by
  constructor
  · rintro ⟨-, hsum, hfix⟩
    rw [Fin.sum_univ_two] at hsum
    have := congrFun hfix 0
    simp [vecMul, dotProduct, flipP, Fin.sum_univ_two] at this
    funext j
    fin_cases j <;> simp <;> linarith
  · rintro rfl
    refine ⟨fun i => ?_, ?_, ?_⟩
    · fin_cases i <;> simp
    · simp [Fin.sum_univ_two]; norm_num
    · funext j
      fin_cases j <;> simp [vecMul, dotProduct, flipP, Fin.sum_univ_two]

/-- AKMM, p. 190: starting from `[p, 1 − p]`, the mass on the first state alternates between
`p` and `1 − p`. -/
theorem flip_oscillates (p : ℝ) (t : ℕ) :
    (![p, 1 - p] ᵥ* flipP ^ (2 * t)) 0 = p ∧ (![p, 1 - p] ᵥ* flipP ^ (2 * t + 1)) 0 = 1 - p := by
  have h2 : flipP ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [flipP, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have he : flipP ^ (2 * t) = 1 := by rw [pow_mul, h2, one_pow]
  refine ⟨by rw [he, vecMul_one]; simp, ?_⟩
  rw [pow_succ, he, Matrix.one_mul]
  simp [vecMul, dotProduct, flipP, Fin.sum_univ_two]

/-- AKMM, p. 190: unless `p = 1/2` the flip chain never converges: the mass on the first state
has no limit. -/
theorem flip_not_converge {p : ℝ} (hp : p ≠ 1 / 2) :
    ¬ ∃ L : ℝ, Tendsto (fun t => (![p, 1 - p] ᵥ* flipP ^ t) 0) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hev : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
  have h1 : L = p := tendsto_nhds_unique (hL.comp hev)
    (by simp only [Function.comp_def, (flip_oscillates p _).1]; exact tendsto_const_nhds)
  have h2 : L = 1 - p := tendsto_nhds_unique (hL.comp hodd)
    (by simp only [Function.comp_def, (flip_oscillates p _).2]; exact tendsto_const_nhds)
  exact hp (by linarith)

/-! ### Conditions for convergence -/

/-- Rows of `Pᵗ` converge to `μ` iff `π₀Pᵗ → μ` for every distribution `π₀`: the forward
direction. -/
theorem markov_vecMul_tendsto {P : Matrix S S ℝ} {μ : S → ℝ}
    (h : ∀ i j, Tendsto (fun t => (P ^ t) i j) atTop (𝓝 (μ j))) (p₀ : S → ℝ)
    (h1 : ∑ i, p₀ i = 1) : Tendsto (fun t => p₀ ᵥ* P ^ t) atTop (𝓝 μ) := by
  rw [tendsto_pi_nhds]
  intro j
  have hs := tendsto_finsetSum (Finset.univ : Finset S) fun i _ => (h i j).const_mul (p₀ i)
  rw [← Finset.sum_mul, h1, one_mul] at hs
  exact hs

/-- AKMM, p. 190 (corrected): if every entry of `P` is positive, the chain has a unique
stationary distribution `π̄` and `π₀Pᵗ → π̄` for every initial distribution `π₀`. -/
theorem positive_matrix_converges [Nonempty S] {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hpos : ∀ i j, 0 < P i j) :
    ∃ μ, mc_IsStationary P μ ∧ (∀ ν, mc_IsStationary P ν → ν = μ) ∧
      ∀ p₀ : S → ℝ, ∑ i, p₀ i = 1 → Tendsto (fun t => p₀ ᵥ* P ^ t) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, -, hlim, huniq⟩ := theorem_3_1_3 hP ⟨1, one_pos, by simpa using hpos⟩
  exact ⟨μ, hμ, huniq, fun p₀ h1 => markov_vecMul_tendsto hlim p₀ h1⟩

/-- A chain with a zero entry: `[0 1; 1/2 1/2]`. -/
noncomputable def halfP : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1 / 2, 1 / 2]

theorem halfP_mem : halfP ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [halfP]
  · fin_cases i <;> simp [halfP, Fin.sum_univ_two]; norm_num

theorem halfP_sq_pos : ∀ i j, 0 < (halfP ^ 2) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [halfP, sq, Matrix.mul_apply, Fin.sum_univ_two]

/-- AKMM, p. 190: positivity of every entry is not necessary for convergence: `[0 1; 1/2 1/2]`
has a zero entry, yet `π₀Pᵗ` converges to its unique stationary distribution from every `π₀`. -/
theorem positive_matrix_not_necessary :
    halfP 0 0 = 0 ∧ ∃ μ, mc_IsStationary halfP μ ∧ (∀ ν, mc_IsStationary halfP ν → ν = μ) ∧
      ∀ p₀ : Fin 2 → ℝ, ∑ i, p₀ i = 1 → Tendsto (fun t => p₀ ᵥ* halfP ^ t) atTop (𝓝 μ) := by
  refine ⟨by simp [halfP], ?_⟩
  obtain ⟨μ, hμ, -, hlim, huniq⟩ := theorem_3_1_3 halfP_mem ⟨2, two_pos, halfP_sq_pos⟩
  exact ⟨μ, hμ, huniq, fun p₀ h1 => markov_vecMul_tendsto hlim p₀ h1⟩

/-- AKMM, p. 190 (corrected): the condition "from each state there is a positive probability of
moving to any other state" is not sufficient for convergence (so not a condition that is
"stronger than we need"): the flip matrix satisfies it and `[1, 0]Pᵗ` does not converge. -/
theorem offdiag_positive_not_sufficient :
    (∀ i j : Fin 2, i ≠ j → 0 < flipP i j) ∧
      ¬ ∃ L : ℝ, Tendsto (fun t => (![1, 1 - 1] ᵥ* flipP ^ t) 0) atTop (𝓝 L) := by
  refine ⟨fun i j hij => ?_, flip_not_converge (by norm_num)⟩
  fin_cases i <;> fin_cases j <;> simp [flipP] at hij ⊢

/-! ### Irreducibility and aperiodicity -/

/-- AKMM, p. 190: state `j` is reachable from `i` if `Pr(x_n = x̄ⱼ | x₀ = x̄ᵢ) > 0` for some
`n`. -/
def ak_Reachable (P : Matrix S S ℝ) (i j : S) : Prop := ∃ n : ℕ, 0 < (P ^ n) i j

/-- AKMM, p. 190: the chain is irreducible if all states are reachable from all other states. -/
def ak_Irreducible (P : Matrix S S ℝ) : Prop := ∀ i j, i ≠ j → ak_Reachable P i j

/-- AKMM, p. 190 (corrected): state `i` is aperiodic if there is `n` with
`Pr(x_{n′} = x̄ᵢ | x₀ = x̄ᵢ) > 0` for all `n′ ≥ n`. -/
def ak_Aperiodic (P : Matrix S S ℝ) (i : S) : Prop := ∃ n : ℕ, ∀ n' ≥ n, 0 < (P ^ n') i i

/-- AKMM, p. 190: the book's irreducibility is Miao's (Definition 3.1.2). -/
theorem ak_irreducible_iff (P : Matrix S S ℝ) : ak_Irreducible P ↔ mc_IsIrreducible P := by
  constructor
  · intro h i j
    by_cases hij : i = j
    · exact Or.inl hij
    refine Or.inr ⟨?_, ?_⟩
    · obtain ⟨n, hn⟩ := h i j hij
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [one_apply, hij] at hn
      · exact ⟨n, hn0, hn⟩
    · obtain ⟨n, hn⟩ := h j i (Ne.symm hij)
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [one_apply, Ne.symm hij] at hn
      · exact ⟨n, hn0, hn⟩
  · intro h i j hij
    rcases h i j with h' | ⟨⟨n, -, hn⟩, -⟩
    · exact absurd h' hij
    · exact ⟨n, hn⟩

/-- **AKMM, p. 190: an irreducible Markov chain has a unique stationary distribution.** -/
theorem markov_irreducible_unique [Nonempty S] {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hirr : ak_Irreducible P) :
    ∃ μ, mc_IsStationary P μ ∧ ∀ ν, mc_IsStationary P ν → ν = μ := by
  obtain ⟨μ, hμ, -, huniq⟩ := mc_irreducible_stationary hP ((ak_irreducible_iff P).1 hirr)
  exact ⟨μ, hμ, huniq⟩

/-- An irreducible chain all of whose states are aperiodic has a positive power. -/
theorem ak_positive_power {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hirr : ak_Irreducible P) (hap : ∀ i, ak_Aperiodic P i) :
    ∃ k, 0 < k ∧ ∀ i j, 0 < (P ^ k) i j := by
  have hreach : ∀ i j, ∃ m : ℕ, 0 < (P ^ m) i j := fun i j => by
    by_cases hij : i = j
    · exact ⟨0, by simp [hij]⟩
    · exact hirr i j hij
  choose m hm using hreach
  choose n hn using hap
  set N := ∑ i, ∑ j, (n i + m i j) + 1 with hN
  have hle : ∀ i j, n i + m i j ≤ ∑ i, ∑ j, (n i + m i j) := fun i j =>
    (Finset.single_le_sum (f := fun j => n i + m i j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, (n i + m i j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i))
  refine ⟨N, by omega, fun i j => ?_⟩
  have hk : N = (N - m i j) + m i j := by have := hle i j; omega
  have h1 : 0 < (P ^ (N - m i j)) i i := hn i _ (by have := hle i j; omega)
  have h2 := mc_pow_add_ge hP (N - m i j) (m i j) i i j
  rw [← hk] at h2
  exact lt_of_lt_of_le (mul_pos h1 (hm i j)) h2

/-- **AKMM, p. 190: if an irreducible chain is also aperiodic, `lim π₀Pᵗ = π̄` for all `π₀`**
(with the corrected definition of aperiodicity). -/
theorem markov_irreducible_aperiodic_converges [Nonempty S] {P : Matrix S S ℝ}
    (hP : P ∈ rowStochastic ℝ S) (hirr : ak_Irreducible P) (hap : ∀ i, ak_Aperiodic P i) :
    ∃ μ, mc_IsStationary P μ ∧ (∀ ν, mc_IsStationary P ν → ν = μ) ∧
      ∀ p₀ : S → ℝ, ∑ i, p₀ i = 1 → Tendsto (fun t => p₀ ᵥ* P ^ t) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, -, hlim, huniq⟩ := theorem_3_1_3 hP (ak_positive_power hP hirr hap)
  exact ⟨μ, hμ, huniq, fun p₀ h1 => markov_vecMul_tendsto hlim p₀ h1⟩

/-- AKMM, p. 190, the printed definition of aperiodicity: "there is some `n` such that for all
`n′ ≥ n`, `Pr(x_{n′} = x̄ᵢ | x_n = x̄ᵢ) > 0`", i.e. `(P^{n′−n})ᵢᵢ > 0`. It is equivalent to
`(Pᵐ)ᵢᵢ > 0` for every `m`. -/
theorem aperiodic_printed_iff (P : Matrix S S ℝ) (i : S) :
    (∃ n : ℕ, ∀ n' ≥ n, 0 < (P ^ (n' - n)) i i) ↔ ∀ m : ℕ, 0 < (P ^ m) i i := by
  constructor
  · rintro ⟨n, hn⟩ m
    have := hn (n + m) (by omega)
    rwa [Nat.add_sub_cancel_left] at this
  · intro h
    exact ⟨0, fun n' _ => h _⟩

/-- AKMM, p. 190: the printed definition of aperiodicity is too strong. For `[0 1; 1/2 1/2]`
state `0` is aperiodic in the corrected sense (`(Pᵐ)₀₀ > 0` for all `m ≥ 2`) but not in the
printed sense, since `P₀₀ = 0`. -/
theorem aperiodic_printed_counterexample :
    ak_Aperiodic halfP 0 ∧ ¬ ∃ n : ℕ, ∀ n' ≥ n, 0 < (halfP ^ (n' - n)) 0 0 := by
  constructor
  · have hpow : ∀ q : ℕ, ∀ i j, 0 < (halfP ^ (q + 2)) i j := by
      intro q
      induction q with
      | zero => simpa using halfP_sq_pos
      | succ q ih =>
        intro i j
        have h1 := mc_pow_add_ge halfP_mem (q + 2) 1 i 1 j
        rw [show q + 2 + 1 = q + 1 + 2 by ring] at h1
        refine lt_of_lt_of_le (mul_pos (ih i 1) ?_) h1
        fin_cases j <;> norm_num [halfP]
    refine ⟨2, fun n' hn' => ?_⟩
    rw [show n' = (n' - 2) + 2 by omega]
    exact hpow _ 0 0
  · rintro h
    have := (aperiodic_printed_iff halfP 0).1 h 1
    simp [halfP] at this

end AKMM.Uncertainty
