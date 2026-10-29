/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.WeightedSpace
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Spectral theory of `V`-uniformly ergodic chains (MT §20.1.1–20.1.2, Theorem 20.1.1)

Meyn and Tweedie, §20.1.1–20.1.2, pp. 510–514. `P` acts on `L∞_V` as `kOp V P` (module
`WeightedSpace`), `Π = 1 ⊗ π` as `piOp V π = kOp V (Kernel.const X π)`, and
`Q = P − Π` as `qOp V P π`.

**Definitions (p. 512).**
* `spectrumV V P` (`S_V(P)`): Mathlib's `spectrum ℂ` of the operator, i.e. the `z` for which
  `T_z = [Iz − P]⁻¹` (`resolvent`) is not a bounded operator on `L∞_V`. `fundKernel V P π z`:
  `Z_z = [Iz − P + 1 ⊗ π]⁻¹` (20.2).
* `rieszProj a z₀ ε = (2πi)⁻¹ ∮_{|z − z₀| = ε} [Iz − a]⁻¹ dz`; `IsFinitePole` (ii): an isolated
  point whose Riesz projections converge to a finite-rank operator; `HasSpectralGap` (iii);
  `HasDiscreteSpectrum` (iv).

**Algebra (p. 513).** `sub_proj_pow`: `(P − Π)ⁿ = Pⁿ − Π` (`n ≥ 1`); `proj_mul_inv`:
`ΠZ_z = Z_zΠ = z⁻¹Π`; `inv_sub_of_inv_sub_proj`: `T_z = Z_z + ((z − 1)⁻¹ − z⁻¹)Π
= Z_z[I + (z − 1)⁻¹Π]`; `inv_sub_proj_of_inv_sub`: conversely `Z_z = T_z(I − Π) + z⁻¹Π`;
`mem_spectrum_iff_sub_proj`: off `{0, 1}`, `S_V(P)` and the spectrum of `P − Π` agree.

**Results.**
* `hasSum_resolvent_of_norm_pow_le` (p. 511): `‖aⁿ‖ ≤ Ktⁿ`, `|z| > t` give
  `[Iz − a]⁻¹ = Σ z^{−n−1} aⁿ`; `mem_spectrum_of_apply_eq`: eigenvalues lie in the spectrum;
  `one_mem_spectrumV`: `1 ∈ S_V(P)`.
* `rieszProj_one_eq`: the Riesz projection at `1` is `Π` for small radii (contour integral).
* **Theorem 20.1.1 (i)** (`theorem_20_1_1_i`, p. 513): `V`-uniform ergodicity gives `Z_z` for
  `|z| > ε₀` (with its power series), `S_V(P) ⊆ {|z| ≤ ε₀} ∪ {1}`, Riesz projection `Π` (rank
  one, `kOp_const_eq`) and so a spectral gap; `resolvent_eq_fundKernel` is the formula for `T_z`.
* **Theorem 20.1.1 (ii)** (`theorem_20_1_1_ii`, p. 513; operator core `spectral_rate_op`): if
  `Z_z` is bounded for `|z| > ε₀`, `ε₀ < 1`, the chain is `V`-uniformly ergodic,
  `λ* = spectralRadius(P − Π) = sup{|z| : z ∈ S_V(P), z ≠ 1} ≤ ε₀` and
  `limsup |||Pⁿ − 1 ⊗ π|||_V^{1/n} ≤ λ*` (20.3), with `|||Pⁿ − 1 ⊗ π|||_V ≤ R εⁿ` for `ε > λ*`.
* `fundKernel_poisson` (p. 511): `f̂ = (Zg)V` solves Poisson's equation `Pf̂ = f̂ − f + π(f)`.
* `eigen_rate` (p. 512): `Ph = λh`, `λ ≠ 1` give `π(h) = 0` and `(Pⁿ − Π)h = λⁿh`.

**Hypotheses and proof route.** In (ii) the book assumes implicitly that `P` acts on `L∞_V`; this
is the hypothesis `WeightOK V P` (`PV ≤ cV`) together with `π(V) < ∞`. The book proves (ii) by
Cauchy's formula on `|z| = ε` with a uniform bound on `|||Z_z|||_V`; we use Gelfand's spectral
radius formula (Mathlib), which gives the same limit (20.3). The "finite multiplicity" of (i) is
proved through the contour integral itself: the Riesz projection equals `Π`, of rank one.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ### Algebra of `P`, `Π = 1 ⊗ π` and `Q = P − Π` -/

/-- `Pⁿ Π = Π` when `PΠ = Π`. -/
theorem pow_mul_proj {A : Type*} [Ring A] {P E : A} (hPE : P * E = E) (n : ℕ) :
    P ^ n * E = E := by
  induction n with
  | zero => rw [pow_zero, one_mul]
  | succ n ih => rw [pow_succ, mul_assoc, hPE, ih]

/-- `(P − Π)ⁿ = Pⁿ − Π` for `n ≥ 1` when `PΠ = ΠP = Π² = Π` (used in the proof of
Theorem 20.1.1, MT p. 513). -/
theorem sub_proj_pow {A : Type*} [Ring A] {P E : A} (hPE : P * E = E) (hEP : E * P = E)
    (hEE : E * E = E) {n : ℕ} (hn : n ≠ 0) : (P - E) ^ n = P ^ n - E := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [zero_add, pow_one, pow_one]
    rw [pow_succ, ih hpos.ne', sub_mul, mul_sub, mul_sub, pow_mul_proj hPE, hEP, hEE,
      ← pow_succ]
    abel

/-- `Π (P − Π) = 0`. -/
theorem proj_mul_sub {A : Type*} [Ring A] {P E : A} (hEP : E * P = E) (hEE : E * E = E) :
    E * (P - E) = 0 := by rw [mul_sub, hEP, hEE, sub_self]

/-- `(P − Π) Π = 0`. -/
theorem sub_mul_proj {A : Type*} [Ring A] {P E : A} (hPE : P * E = E) (hEE : E * E = E) :
    (P - E) * E = 0 := by rw [sub_mul, hPE, hEE, sub_self]

/-- `ΠZ_z = Z_z Π = z⁻¹ Π` for the inverse `Z_z` of `z − (P − Π)` (MT p. 513). -/
theorem proj_mul_inv {A : Type*} [Ring A] [Algebra ℂ A] {P E Z : A} (hPE : P * E = E)
    (hEP : E * P = E) (hEE : E * E = E) {z : ℂ} (hz : z ≠ 0)
    (h1 : (algebraMap ℂ A z - (P - E)) * Z = 1) (h2 : Z * (algebraMap ℂ A z - (P - E)) = 1) :
    E * Z = z⁻¹ • E ∧ Z * E = z⁻¹ • E := by
  have hl : E * (algebraMap ℂ A z - (P - E)) = z • E := by
    rw [mul_sub, proj_mul_sub hEP hEE, sub_zero, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one]
  have hr : (algebraMap ℂ A z - (P - E)) * E = z • E := by
    rw [sub_mul, sub_mul_proj hPE hEE, sub_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  constructor
  · have : E = z • (E * Z) := by
      calc E = E * ((algebraMap ℂ A z - (P - E)) * Z) := by rw [h1, mul_one]
        _ = z • (E * Z) := by rw [← mul_assoc, hl, smul_mul_assoc]
    rw [this, smul_smul, inv_mul_cancel₀ hz, one_smul, ← this]
  · have : E = z • (Z * E) := by
      calc E = (Z * (algebraMap ℂ A z - (P - E))) * E := by rw [h2, one_mul]
        _ = z • (Z * E) := by rw [mul_assoc, hr, mul_smul_comm]
    rw [this, smul_smul, inv_mul_cancel₀ hz, one_smul, ← this]

/-- **The resolvent from the fundamental kernel** (MT p. 513): for `z ∉ {0, 1}`, if `Z_z`
inverts `z − (P − Π)`, then `T_z = Z_z + ((z − 1)⁻¹ − z⁻¹) Π = Z_z [I + (z − 1)⁻¹ Π]` inverts
`z − P`. -/
theorem inv_sub_of_inv_sub_proj {A : Type*} [Ring A] [Algebra ℂ A] {P E Z : A}
    (hPE : P * E = E) (hEP : E * P = E) (hEE : E * E = E) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (h1 : (algebraMap ℂ A z - (P - E)) * Z = 1) (h2 : Z * (algebraMap ℂ A z - (P - E)) = 1) :
    (algebraMap ℂ A z - P) * (Z + ((z - 1)⁻¹ - z⁻¹) • E) = 1 ∧
      (Z + ((z - 1)⁻¹ - z⁻¹) • E) * (algebraMap ℂ A z - P) = 1 := by
  obtain ⟨hEZ, hZE⟩ := proj_mul_inv hPE hEP hEE hz0 h1 h2
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  have hc : ((z - 1)⁻¹ - z⁻¹) * z - z⁻¹ - ((z - 1)⁻¹ - z⁻¹) = 0 := by
    field_simp; ring
  have hsplit : algebraMap ℂ A z - P = (algebraMap ℂ A z - (P - E)) - E := by abel
  have hQE : (algebraMap ℂ A z - (P - E)) * E = z • E := by
    rw [sub_mul, sub_mul_proj hPE hEE, sub_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  have hEQ : E * (algebraMap ℂ A z - (P - E)) = z • E := by
    rw [mul_sub, proj_mul_sub hEP hEE, sub_zero, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one]
  constructor
  · rw [hsplit, sub_mul, mul_add, mul_add, h1, mul_smul_comm, hQE, hEZ, mul_smul_comm, hEE]
    calc 1 + ((z - 1)⁻¹ - z⁻¹) • z • E - (z⁻¹ • E + ((z - 1)⁻¹ - z⁻¹) • E)
        = 1 + (((z - 1)⁻¹ - z⁻¹) * z - z⁻¹ - ((z - 1)⁻¹ - z⁻¹)) • E := by
          module
      _ = 1 := by rw [hc, zero_smul, add_zero]
  · rw [hsplit, mul_sub, add_mul, add_mul, h2, smul_mul_assoc, hEQ, hZE, smul_mul_assoc, hEE]
    calc 1 + ((z - 1)⁻¹ - z⁻¹) • z • E - (z⁻¹ • E + ((z - 1)⁻¹ - z⁻¹) • E)
        = 1 + (((z - 1)⁻¹ - z⁻¹) * z - z⁻¹ - ((z - 1)⁻¹ - z⁻¹)) • E := by
          module
      _ = 1 := by rw [hc, zero_smul, add_zero]

/-- An inverse commutes with what its operand commutes with. -/
theorem inv_commute {A : Type*} [Ring A] {a T E : A} (haE : a * E = E * a) (h1 : a * T = 1)
    (h2 : T * a = 1) : T * E = E * T := by
  calc T * E = T * E * (a * T) := by rw [h1, mul_one]
    _ = T * (E * a) * T := by simp only [mul_assoc]
    _ = T * (a * E) * T := by rw [haE]
    _ = (T * a) * E * T := by simp only [mul_assoc]
    _ = E * T := by rw [h2, one_mul]

/-- **The fundamental kernel from the resolvent**: for `z ≠ 0`, if `T_z` inverts `z − P`, then
`T_z (I − Π) + z⁻¹ Π` inverts `z − (P − Π)`. -/
theorem inv_sub_proj_of_inv_sub {A : Type*} [Ring A] [Algebra ℂ A] {P E T : A}
    (hPE : P * E = E) (hEP : E * P = E) (hEE : E * E = E) {z : ℂ} (hz0 : z ≠ 0)
    (h1 : (algebraMap ℂ A z - P) * T = 1) (h2 : T * (algebraMap ℂ A z - P) = 1) :
    (algebraMap ℂ A z - (P - E)) * (T * (1 - E) + z⁻¹ • E) = 1 ∧
      (T * (1 - E) + z⁻¹ • E) * (algebraMap ℂ A z - (P - E)) = 1 := by
  have hcomm : (algebraMap ℂ A z - P) * E = E * (algebraMap ℂ A z - P) := by
    rw [sub_mul, mul_sub, hPE, hEP, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
  have hTE := inv_commute hcomm h1 h2
  have hE1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hEE, sub_self]
  have hE1' : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hEE, sub_self]
  have hzE : (algebraMap ℂ A z - P) * E = z • E - E := by
    rw [sub_mul, hPE, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hEz : E * (algebraMap ℂ A z - P) = z • E - E := by rw [← hcomm, hzE]
  have hsplit : algebraMap ℂ A z - (P - E) = (algebraMap ℂ A z - P) + E := by abel
  constructor
  · rw [hsplit, add_mul, mul_add, mul_add, ← mul_assoc, h1, one_mul, mul_smul_comm, hzE,
      ← mul_assoc, ← hTE, mul_assoc, hE1, mul_zero, mul_smul_comm, hEE, smul_sub, smul_smul,
      inv_mul_cancel₀ hz0, one_smul]
    abel
  · have h1E : (1 - E) * (algebraMap ℂ A z - P) = (algebraMap ℂ A z - P) * (1 - E) := by
      calc (1 - E) * (algebraMap ℂ A z - P)
          = (algebraMap ℂ A z - P) - E * (algebraMap ℂ A z - P) := by rw [sub_mul, one_mul]
        _ = (algebraMap ℂ A z - P) - (algebraMap ℂ A z - P) * E := by rw [hcomm]
        _ = (algebraMap ℂ A z - P) * (1 - E) := by rw [mul_sub, mul_one]
    rw [hsplit, mul_add, add_mul, add_mul, mul_assoc, h1E, ← mul_assoc, h2, one_mul,
      smul_mul_assoc, hEz, mul_assoc, hE1', mul_zero, smul_mul_assoc, hEE, smul_sub, smul_smul,
      inv_mul_cancel₀ hz0, one_smul]
    abel


/-! ### Power series, eigenvalues and Riesz projections in a Banach algebra -/

/-- A two-sided inverse is the `Ring.inverse`. -/
theorem ring_inverse_eq {A : Type*} [Ring A] {a b : A} (h1 : a * b = 1) (h2 : b * a = 1) :
    Ring.inverse a = b :=
  Ring.inverse_unit ⟨a, b, h1, h2⟩

/-- **The power series for the resolvent** (MT p. 511): if `‖aⁿ‖ ≤ K tⁿ` for all `n` and
`|z| > t`, then `z − a` is invertible, with `(z − a)⁻¹ = Σₙ z^{−n−1} aⁿ`. -/
theorem hasSum_resolvent_of_norm_pow_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {a : E →L[ℂ] E} {K t : ℝ} (ha : ∀ n, ‖a ^ n‖ ≤ K * t ^ n) (ht : 0 ≤ t) {z : ℂ}
    (hz : t < ‖z‖) :
    IsUnit (algebraMap ℂ (E →L[ℂ] E) z - a) ∧
      HasSum (fun n => z⁻¹ ^ (n + 1) • a ^ n) (_root_.resolvent a z) := by
  have hzpos : 0 < ‖z‖ := ht.trans_lt hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  set f : ℕ → E →L[ℂ] E := fun n => z⁻¹ ^ n • a ^ n with hfdef
  have hq : t / ‖z‖ < 1 := (div_lt_one hzpos).2 hz
  have hf : Summable f := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (div_nonneg ht hzpos.le)
      hq).mul_left K) fun n => ?_
    rw [hfdef, norm_smul, norm_pow, norm_inv]
    calc ‖z‖⁻¹ ^ n * ‖a ^ n‖ ≤ ‖z‖⁻¹ ^ n * (K * t ^ n) :=
          mul_le_mul_of_nonneg_left (ha n) (by positivity)
      _ = K * (t / ‖z‖) ^ n := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
  obtain ⟨s, hs⟩ := hf
  have hf0 : f 0 = 1 := by rw [hfdef]; simp only [pow_zero, one_smul]
  have hshift : HasSum (fun n => f (n + 1)) (s - 1) := by
    have := (hasSum_nat_add_iff' 1).2 hs
    rwa [Finset.sum_range_one, hf0] at this
  have hcoef : ∀ n : ℕ, z * z⁻¹ ^ (n + 1) = z⁻¹ ^ n := fun n => by
    rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  have haf : ∀ n, a * f n = z • f (n + 1) := fun n => by
    rw [hfdef]; dsimp only
    rw [mul_smul_comm, smul_smul, hcoef, pow_succ']
  have hfa : ∀ n, f n * a = z • f (n + 1) := fun n => by
    rw [hfdef]; dsimp only
    rw [smul_mul_assoc, smul_smul, hcoef, pow_succ]
  have has : a * s = z • (s - 1) := by
    have h1 := hs.mul_left a
    simp_rw [haf] at h1
    exact h1.unique (hshift.const_smul z)
  have hsa : s * a = z • (s - 1) := by
    have h1 := hs.mul_right a
    simp_rw [hfa] at h1
    exact h1.unique (hshift.const_smul z)
  have hzs : algebraMap ℂ (E →L[ℂ] E) z * s = z • s := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hsz : s * algebraMap ℂ (E →L[ℂ] E) z = z • s := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have h1 : (algebraMap ℂ (E →L[ℂ] E) z - a) * (z⁻¹ • s) = 1 := by
    rw [sub_mul, mul_smul_comm, mul_smul_comm, hzs, has, inv_smul_smul₀ hz0,
      inv_smul_smul₀ hz0, sub_sub_cancel]
  have h2 : (z⁻¹ • s) * (algebraMap ℂ (E →L[ℂ] E) z - a) = 1 := by
    rw [mul_sub, smul_mul_assoc, smul_mul_assoc, hsz, hsa, inv_smul_smul₀ hz0,
      inv_smul_smul₀ hz0, sub_sub_cancel]
  refine ⟨⟨⟨_, _, h1, h2⟩, rfl⟩, ?_⟩
  rw [_root_.resolvent, ring_inverse_eq h1 h2]
  convert hs.const_smul z⁻¹ using 1
  funext n
  rw [hfdef, smul_smul, pow_succ']

/-- An eigenvalue lies in the spectrum: `ah = zh` with `h ≠ 0` makes `z − a` non-invertible. -/
theorem mem_spectrum_of_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : E →L[ℂ] E) {z : ℂ} {h : E} (h0 : h ≠ 0) (hh : a h = z • h) : z ∈ spectrum ℂ a := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have hz : (algebraMap ℂ (E →L[ℂ] E) z - a) h = 0 := by
    change (algebraMap ℂ (E →L[ℂ] E) z) h - a h = 0
    rw [Algebra.algebraMap_eq_smul_one, hh]
    change z • h - z • h = 0
    exact sub_self _
  apply h0
  calc h = ((↑u⁻¹ : E →L[ℂ] E) * ↑u) h := by rw [u.inv_mul]; rfl
    _ = (↑u⁻¹ : E →L[ℂ] E) ((u : E →L[ℂ] E) h) := rfl
    _ = 0 := by rw [hu, hz, map_zero]

/-- The Riesz projection `(2πi)⁻¹ ∮_{|z − z₀| = ε} (zI − a)⁻¹ dz` (MT p. 512). -/
noncomputable def rieszProj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : E →L[ℂ] E) (z₀ : ℂ) (ε : ℝ) : E →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(z₀, ε), _root_.resolvent a z

/-- **A pole of finite multiplicity** (MT p. 512, (ii)): `z₀` is an isolated point of the spectrum
and the Riesz projections converge, as `ε ↓ 0`, to an operator of finite rank. -/
def IsFinitePole {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : E →L[ℂ] E)
    (z₀ : ℂ) : Prop :=
  z₀ ∈ spectrum ℂ a ∧ (∃ δ > 0, ∀ z ∈ spectrum ℂ a, ‖z - z₀‖ < δ → z = z₀) ∧
    ∃ T : E →L[ℂ] E, Tendsto (rieszProj a z₀) (𝓝[>] 0) (𝓝 T) ∧
      FiniteDimensional ℂ (LinearMap.range (T : E →ₗ[ℂ] E))

/-- **A spectral gap** (MT p. 512, (iii)): `1` is a pole of finite multiplicity. -/
def HasSpectralGap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : E →L[ℂ] E) :
    Prop :=
  IsFinitePole a 1

/-- **A discrete spectrum** (MT p. 512, (iv)): for every `ε > 0` the spectrum in `|z| ≥ ε` is
finite and consists of poles of finite multiplicity. -/
def HasDiscreteSpectrum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : E →L[ℂ] E) : Prop :=
  ∀ ε > 0, {z ∈ spectrum ℂ a | ε ≤ ‖z‖}.Finite ∧
    ∀ z ∈ spectrum ℂ a, ε ≤ ‖z‖ → IsFinitePole a z

/-- **The Riesz projection at `1` is `Π`**: if `PΠ = ΠP = Π² = Π` and `z − (P − Π)` is invertible
for `|z| > t`, `t < 1`, then `(2πi)⁻¹ ∮_{|z − 1| = ε} (zI − P)⁻¹ dz = Π` for `0 < ε < 1 − t`
(the computation behind Theorem 20.1.1 (i), MT p. 513: `T_z = Z_z + ((z − 1)⁻¹ − z⁻¹) Π` with
`Z_z` holomorphic). -/
theorem rieszProj_one_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {P Pr : E →L[ℂ] E} (hPE : P * Pr = Pr) (hEP : Pr * P = Pr) (hEE : Pr * Pr = Pr) {t : ℝ}
    (ht : 0 ≤ t) (hZ : ∀ z : ℂ, t < ‖z‖ → IsUnit (algebraMap ℂ _ z - (P - Pr))) {ε : ℝ}
    (hε : 0 < ε) (hεt : ε < 1 - t) : rieszProj P 1 ε = Pr := by
  have hfar : ∀ z ∈ Metric.closedBall (1 : ℂ) ε, t < ‖z‖ := fun z hz => by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := norm_sub_norm_le (1 : ℂ) (1 - z)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  have hne0 : ∀ z ∈ Metric.closedBall (1 : ℂ) ε, z ≠ 0 := fun z hz =>
    norm_pos_iff.1 (ht.trans_lt (hfar z hz))
  -- the resolvent on the circle
  have hT : ∀ z ∈ Metric.sphere (1 : ℂ) ε, _root_.resolvent P z =
      _root_.resolvent (P - Pr) z + ((z - 1)⁻¹ - z⁻¹) • Pr := fun z hz => by
    have hzb : z ∈ Metric.closedBall (1 : ℂ) ε := Metric.sphere_subset_closedBall hz
    have hz1 : z ≠ 1 := fun h => by
      rw [h, Metric.mem_sphere, dist_self] at hz; exact hε.ne' hz.symm
    have hu := hZ z (hfar z hzb)
    obtain ⟨h1, h2⟩ := inv_sub_of_inv_sub_proj hPE hEP hEE (hne0 z hzb) hz1
      (Ring.mul_inverse_cancel _ hu) (Ring.inverse_mul_cancel _ hu)
    rw [_root_.resolvent, ring_inverse_eq h1 h2, _root_.resolvent]
  have hcont : ContinuousOn (_root_.resolvent (P - Pr) : ℂ → E →L[ℂ] E)
      (Metric.closedBall (1 : ℂ) ε) :=
    fun z hz =>
    (spectrum.hasDerivAt_resolvent_const_left (spectrum.mem_resolventSet_iff.2
      (hZ z (hfar z hz)))).continuousAt.continuousWithinAt
  have hZ0 : (∮ z in C(1, ε), _root_.resolvent (P - Pr) z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le countable_empty
      hcont fun z hz => (spectrum.hasDerivAt_resolvent_const_left
        (spectrum.mem_resolventSet_iff.2 (hZ z (hfar z (Metric.ball_subset_closedBall
          hz.1))))).differentiableAt
  have hinvc : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.closedBall 1 ε) :=
    continuousOn_inv₀.mono fun z hz => hne0 z hz
  have hinv0 : (∮ z in C(1, ε), z⁻¹) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le countable_empty
      hinvc fun z hz => differentiableAt_inv (hne0 z (Metric.ball_subset_closedBall hz.1))
  have hsph : ∀ z ∈ Metric.sphere (1 : ℂ) ε, z - 1 ≠ 0 := fun z hz h => by
    rw [sub_eq_zero] at h
    rw [h, Metric.mem_sphere, dist_self] at hz; exact hε.ne' hz.symm
  have hc1 : ContinuousOn (fun z : ℂ => (z - 1)⁻¹) (Metric.sphere 1 ε) :=
    ((continuous_id.sub continuous_const).continuousOn).inv₀ hsph
  have hc2 : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere 1 ε) :=
    hinvc.mono Metric.sphere_subset_closedBall
  have hscal : (∮ z in C(1, ε), ((z - 1)⁻¹ - z⁻¹)) = 2 * Real.pi * Complex.I := by
    rw [circleIntegral.integral_sub (hc1.circleIntegrable hε.le) (hc2.circleIntegrable hε.le),
      hinv0, sub_zero, circleIntegral.integral_sub_center_inv 1 hε.ne']
  have hcR : ContinuousOn (_root_.resolvent (P - Pr) : ℂ → E →L[ℂ] E)
      (Metric.sphere (1 : ℂ) ε) :=
    hcont.mono Metric.sphere_subset_closedBall
  have hcS : ContinuousOn (fun z : ℂ => ((z - 1)⁻¹ - z⁻¹) • Pr) (Metric.sphere 1 ε) :=
    (hc1.sub hc2).smul continuousOn_const
  rw [rieszProj, circleIntegral.integral_congr hε.le hT,
    circleIntegral.integral_add (hcR.circleIntegrable hε.le) (hcS.circleIntegrable hε.le), hZ0,
    zero_add, circleIntegral.integral_smul_const, hscal, smul_smul,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]


/-- Outside `{0, 1}`, `z` is in the spectrum of `P` iff it is in the spectrum of `P − Π`
(operator form). -/
theorem mem_spectrum_iff_sub_proj_op {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Pr : E →L[ℂ] E} (hPE : P * Pr = Pr) (hEP : Pr * P = Pr) (hEE : Pr * Pr = Pr) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) : z ∈ spectrum ℂ P ↔ z ∈ spectrum ℂ (P - Pr) := by
  rw [spectrum.mem_iff, spectrum.mem_iff, not_iff_not]
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := inv_sub_proj_of_inv_sub hPE hEP hEE hz0 (Ring.mul_inverse_cancel _ hu)
      (Ring.inverse_mul_cancel _ hu)
    exact ⟨⟨_, _, h1, h2⟩, rfl⟩
  · intro hu
    obtain ⟨h1, h2⟩ := inv_sub_of_inv_sub_proj hPE hEP hEE hz0 hz1
      (Ring.mul_inverse_cancel _ hu) (Ring.inverse_mul_cancel _ hu)
    exact ⟨⟨_, _, h1, h2⟩, rfl⟩

/-- The resolvent formula in operator form: `ΠZ = ZΠ = z⁻¹Π` and, for `z ≠ 1`,
`T_z = Z_z [I + (z − 1)⁻¹ Π] = Z_z + ((z − 1)⁻¹ − z⁻¹) Π`. -/
theorem resolvent_eq_op {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Pr : E →L[ℂ] E} (hPE : P * Pr = Pr) (hEP : Pr * P = Pr) (hEE : Pr * Pr = Pr) {z : ℂ}
    (hz0 : z ≠ 0) (hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - (P - Pr))) :
    Pr * _root_.resolvent (P - Pr) z = z⁻¹ • Pr ∧ _root_.resolvent (P - Pr) z * Pr = z⁻¹ • Pr ∧
      (z ≠ 1 → _root_.resolvent P z = _root_.resolvent (P - Pr) z * (1 + (z - 1)⁻¹ • Pr) ∧
        _root_.resolvent P z = _root_.resolvent (P - Pr) z + ((z - 1)⁻¹ - z⁻¹) • Pr) := by
  have h1 := Ring.mul_inverse_cancel _ hu
  have h2 := Ring.inverse_mul_cancel _ hu
  obtain ⟨hEZ, hZE⟩ := proj_mul_inv hPE hEP hEE hz0 h1 h2
  refine ⟨hEZ, hZE, fun hz1 => ?_⟩
  obtain ⟨h3, h4⟩ := inv_sub_of_inv_sub_proj hPE hEP hEE hz0 hz1 h1 h2
  have hT : _root_.resolvent P z = _root_.resolvent (P - Pr) z + ((z - 1)⁻¹ - z⁻¹) • Pr := by
    rw [_root_.resolvent, ring_inverse_eq h3 h4]; rfl
  refine ⟨?_, hT⟩
  have hZE' : Ring.inverse (algebraMap ℂ (E →L[ℂ] E) z - (P - Pr)) * Pr = z⁻¹ • Pr := hZE
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  have hsc : (z - 1)⁻¹ * z⁻¹ = (z - 1)⁻¹ - z⁻¹ := by
    rw [inv_sub_inv hz1' hz0, sub_sub_cancel, one_div, mul_inv]
  rw [hT, _root_.resolvent, mul_add, mul_one, mul_smul_comm, hZE', smul_smul, hsc]

/-! ### The spectrum of `P` on `L∞_V` -/

variable {X : Type*} [MeasurableSpace X]

/-- The operator `Π = 1 ⊗ π` on `L∞_V`. -/
noncomputable def piOp (V : X → ℝ) (π : Measure X) : BM X →L[ℂ] BM X :=
  kOp V (Kernel.const X π)

/-- The centred operator `P − 1 ⊗ π` on `L∞_V`. -/
noncomputable def qOp (V : X → ℝ) (P : Kernel X X) (π : Measure X) : BM X →L[ℂ] BM X :=
  kOp V P - piOp V π

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `PΠ = Π`. -/
theorem kOp_mul_piOp [IsMarkovKernel P] [IsProbabilityMeasure π] (hP : WeightOK V P)
    (hPi : WeightOK V (Kernel.const X π)) : kOp V P * piOp V π = piOp V π :=
  kOp_mul_kOp_const hP hPi

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `ΠP = Π` for invariant `π`. -/
theorem piOp_mul_kOp [IsMarkovKernel P] [IsProbabilityMeasure π] (hP : WeightOK V P)
    (hPi : WeightOK V (Kernel.const X π)) (hinv : IsInvariant P π) :
    piOp V π * kOp V P = piOp V π :=
  kOp_const_mul_kOp hP hPi hinv

variable {V : X → ℝ} {π : Measure X} in
/-- `Π² = Π`. -/
theorem piOp_mul_self [IsProbabilityMeasure π] (hPi : WeightOK V (Kernel.const X π)) :
    piOp V π * piOp V π = piOp V π :=
  kOp_const_mul_self hPi

/-- **The spectrum `S_V(P)`** (MT p. 512, (i)): the `z ∈ ℂ` for which `T_z = [Iz − P]⁻¹` does not
exist as a bounded operator on `L∞_V`. -/
noncomputable abbrev spectrumV (V : X → ℝ) (P : Kernel X X) : Set ℂ := spectrum ℂ (kOp V P)

/-- **The kernel `Z_z = [Iz − P + 1 ⊗ π]⁻¹`** (20.2), MT p. 511; `Z = Z_1` is the fundamental
kernel. -/
noncomputable def fundKernel (V : X → ℝ) (P : Kernel X X) (π : Measure X) (z : ℂ) :
    BM X →L[ℂ] BM X :=
  _root_.resolvent (qOp V P π) z

/-- The constant function `1 ∈ L∞_V`, which is `1/V` in weighted coordinates. -/
noncomputable def oneV {V : X → ℝ} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) : BM X :=
  mkBM (fun x => ((V x : ℂ))⁻¹) (Complex.measurable_ofReal.comp hV).inv 1 fun x => by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans (hV1 x))]
    exact inv_le_one_of_one_le₀ (hV1 x)

/-- `P1 = 1` for a Markov kernel. -/
theorem kOp_oneV {V : X → ℝ} {P : Kernel X X} [IsMarkovKernel P] (hP : WeightOK V P) :
    kOp V P (oneV hP.1 hP.2.1) = oneV hP.1 hP.2.1 := by
  refine bm_ext fun x => ?_
  rw [kOp_apply hP, kFun]
  change ((V x : ℂ))⁻¹ * ∫ y, ((V y : ℂ))⁻¹ * (V y : ℂ) ∂P x = ((V x : ℂ))⁻¹
  have h1 : ∫ y, ((V y : ℂ))⁻¹ * (V y : ℂ) ∂P x = 1 := by
    rw [integral_congr_ae (g := fun _ => (1 : ℂ)) (Eventually.of_forall fun y => by
      have : (V y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hP.pos y).ne'
      exact inv_mul_cancel₀ this), integral_const, probReal_univ, one_smul]
  rw [h1, mul_one]

/-- `1 ⊗ π` has rank one: `Πg = π(gV) · 1`. -/
theorem kOp_const_eq {V : X → ℝ} {π : Measure X} (h : WeightOK V (Kernel.const X π))
    (g : BM X) :
    piOp V π g = (∫ y, bmFun g y * (V y : ℂ) ∂π) • oneV h.1 h.2.1 := by
  refine bm_ext fun x => ?_
  rw [piOp, kOp_const_apply h, bmFun_smul, oneV, bmFun_mkBM, mul_comm]

/-- `1 ≠ 0` in `L∞_V` on a nonempty space. -/
theorem oneV_ne_zero {V : X → ℝ} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) [Nonempty X] :
    oneV hV hV1 ≠ 0 := fun h => by
  have x : X := Classical.arbitrary X
  have := congrArg (fun g => bmFun g x) h
  simp only [oneV, bmFun_mkBM, bmFun_zero] at this
  exact (inv_ne_zero (Complex.ofReal_ne_zero.2 (zero_lt_one.trans_le (hV1 x)).ne')) this

/-- `1 ∈ S_V(P)`: `1` is an eigenvalue, with eigenfunction `1`. -/
theorem one_mem_spectrumV {V : X → ℝ} {P : Kernel X X} [IsMarkovKernel P] [Nonempty X]
    (hP : WeightOK V P) : (1 : ℂ) ∈ spectrumV V P :=
  mem_spectrum_of_apply_eq (E := BM X) _ (oneV_ne_zero hP.1 hP.2.1) (by rw [kOp_oneV hP, one_smul])

/-- `ENNReal.ofReal ‖x‖ = ‖x‖₊`. -/
theorem ofReal_norm_eq_nnnorm {A : Type*} [NormedAddCommGroup A] (x : A) :
    ENNReal.ofReal ‖x‖ = (‖x‖₊ : ℝ≥0∞) := by
  rw [← coe_nnnorm x]; exact ENNReal.ofReal_coe_nnreal

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `V`-uniform ergodicity in the form (16.3) gives `‖(P − Π)ⁿ‖ ≤ K tⁿ` on `L∞_V`, `t < 1`,
with `P` and `1 ⊗ π` acting on `L∞_V`. -/
theorem norm_sub_pow_le_of_rate [IsMarkovKernel P] [IsProbabilityMeasure π]
    (hinv : IsInvariant P π) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {r R : ℝ≥0∞} (hr : 1 < r)
    (hR : R ≠ ∞) (hb : ∀ n, vErgDist (eW V) P π n ≤ R * r⁻¹ ^ n) :
    WeightOK V P ∧ WeightOK V (Kernel.const X π) ∧ ∃ K t : ℝ, 0 ≤ t ∧ t < 1 ∧
      ∀ n, ‖(qOp V P π) ^ n‖ ≤ K * t ^ n := by
  have hrt : r⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (zero_lt_one.trans hr).ne'
  have hfin : ∀ n, vErgDist (eW V) P π n ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hR (ENNReal.pow_ne_top hrt)) (hb n)
  obtain ⟨hP, hPi⟩ := weightOK_of_vErgDist hV hV1 (hfin 0) (hfin 1)
  have ht1 : r⁻¹.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hrt ENNReal.one_ne_top).2 (ENNReal.inv_lt_one.2 hr)
    rwa [ENNReal.toReal_one] at this
  refine ⟨hP, hPi, max (2 * R.toReal) 1, r⁻¹.toReal, ENNReal.toReal_nonneg, ht1, fun n => ?_⟩
  have htn : 0 ≤ r⁻¹.toReal ^ n := pow_nonneg ENNReal.toReal_nonneg n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_zero, mul_one]
    exact (ContinuousLinearMap.norm_id_le).trans (le_max_right _ _)
  have hpow := sub_proj_pow (A := BM X →L[ℂ] BM X) (kOp_mul_piOp hP hPi) (piOp_mul_kOp hP hPi hinv)
    (piOp_mul_self hPi) hn.ne'
  have hD : vErgDist (eW V) P π n ≤ ENNReal.ofReal (R.toReal * r⁻¹.toReal ^ n) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hR, ENNReal.ofReal_toReal hrt]
    exact hb n
  calc ‖(qOp V P π) ^ n‖
        = ‖kOp V P ^ n - piOp V π‖ := congrArg norm hpow
    _ ≤ 2 * (R.toReal * r⁻¹.toReal ^ n) :=
        norm_le_vErgDist hP hPi n (mul_nonneg ENNReal.toReal_nonneg htn) hD
    _ = 2 * R.toReal * r⁻¹.toReal ^ n := by ring
    _ ≤ max (2 * R.toReal) 1 * r⁻¹.toReal ^ n :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) htn


variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- Outside `{0, 1}`, `z` is in the spectrum of `P` iff it is in the spectrum of `P − Π`. -/
theorem mem_spectrum_iff_sub_proj [IsMarkovKernel P] [IsProbabilityMeasure π]
    (hinv : IsInvariant P π) (hP : WeightOK V P) (hPi : WeightOK V (Kernel.const X π)) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    z ∈ spectrumV V P ↔ z ∈ spectrum ℂ (qOp V P π) :=
  mem_spectrum_iff_sub_proj_op (E := BM X) (kOp_mul_piOp hP hPi) (piOp_mul_kOp hP hPi hinv)
    (piOp_mul_self hPi) hz0 hz1

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- **Theorem 20.1.1 (i)** (MT p. 513): if the chain is `V`-uniformly ergodic,
`|||Pⁿ − 1 ⊗ π|||_V ≤ R r⁻ⁿ` with `r > 1` (16.3), then for some `ε₀ < 1`:
* `Z_z` exists as a bounded operator on `L∞_V` for `|z| > ε₀`, with the power series
  `Z_z = Σ z^{−n−1} [P − 1 ⊗ π]ⁿ`;
* the spectrum `S_V(P)` lies in `{|z| ≤ ε₀} ∪ {1}`;
* the Riesz projection at `1` is `1 ⊗ π` for every radius `ε < 1 − ε₀`;
* hence there is a spectral gap in `L∞_V`: `1` is a pole of multiplicity one. -/
theorem theorem_20_1_1_i [IsMarkovKernel P] [IsProbabilityMeasure π] (hinv : IsInvariant P π)
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hrate : ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧
      ∀ n, vErgDist (eW V) P π n ≤ R * r⁻¹ ^ n) :
    ∃ ε₀ : ℝ, 0 ≤ ε₀ ∧ ε₀ < 1 ∧
      (∀ z : ℂ, ε₀ < ‖z‖ →
        z ∈ resolventSet ℂ (qOp V P π) ∧
        HasSum (fun n => z⁻¹ ^ (n + 1) • (qOp V P π) ^ n)
          (fundKernel V P π z)) ∧
      spectrumV V P ⊆ Metric.closedBall 0 ε₀ ∪ {1} ∧
      (∀ ε, 0 < ε → ε < 1 - ε₀ → rieszProj (E := BM X) (kOp V P) 1 ε = piOp V π) ∧
      HasSpectralGap (E := BM X) (kOp V P) := by
  have := nonempty_of_isProbabilityMeasure π
  have := completeSpace_BM (X := X)
  obtain ⟨r, hr, R, hR, hb⟩ := hrate
  obtain ⟨hP, hPi, K, t, ht0, ht1, hpow⟩ := norm_sub_pow_le_of_rate hinv hV hV1 hr hR hb
  have hPE := kOp_mul_piOp hP hPi
  have hEP := piOp_mul_kOp hP hPi hinv
  have hEE := piOp_mul_self hPi
  have hser : ∀ z : ℂ, t < ‖z‖ →
      z ∈ resolventSet ℂ (qOp V P π) ∧
      HasSum (fun n => z⁻¹ ^ (n + 1) • (qOp V P π) ^ n)
        (fundKernel V P π z) := fun z hz =>
    ⟨spectrum.mem_resolventSet_iff.2
      (hasSum_resolvent_of_norm_pow_le (E := BM X) hpow ht0 hz).1,
      (hasSum_resolvent_of_norm_pow_le (E := BM X) hpow ht0 hz).2⟩
  have hnot : ∀ z : ℂ, t < ‖z‖ → z ≠ 1 → z ∉ spectrumV V P := fun z hz hz1 hmem =>
    (spectrum.mem_iff.1 ((mem_spectrum_iff_sub_proj hinv hP hPi
      (norm_pos_iff.1 (ht0.trans_lt hz)) hz1).1 hmem)) (spectrum.mem_resolventSet_iff.1
        (hser z hz).1)
  have hriesz : ∀ ε, 0 < ε → ε < 1 - t → rieszProj (E := BM X) (kOp V P) 1 ε = piOp V π :=
    fun ε hε hεt => rieszProj_one_eq (E := BM X) hPE hEP hEE ht0
      (fun z hz => spectrum.mem_resolventSet_iff.1 (hser z hz).1) hε hεt
  refine ⟨t, ht0, ht1, hser, fun z hz => ?_, hriesz, one_mem_spectrumV hP, ⟨1 - t, by linarith,
    fun z hz hz1 => ?_⟩, piOp V π, ?_, ?_⟩
  · by_contra h
    rw [mem_union, Metric.mem_closedBall, dist_zero_right, mem_singleton_iff, not_or,
      not_le] at h
    exact hnot z h.1 h.2 hz
  · by_contra h
    refine hnot z ?_ h hz
    have := norm_sub_norm_le (1 : ℂ) (1 - z)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - t by linarith)] with ε hε
    exact (hriesz ε hε.1 hε.2).symm
  · refine Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ oneV hV hV1) ?_
    rintro _ ⟨g, rfl⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨_, (kOp_const_eq hPi g).symm⟩

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- **The resolvent in terms of `Z_z`** (MT p. 513): `ΠZ_z = Z_zΠ = z⁻¹Π`, and for `z ∉ {0, 1}`
with `Z_z` defined, `T_z = Z_z [I + (z − 1)⁻¹ 1 ⊗ π] = Z_z + ((z − 1)⁻¹ − z⁻¹) 1 ⊗ π`. -/
theorem resolvent_eq_fundKernel [IsMarkovKernel P] [IsProbabilityMeasure π]
    (hinv : IsInvariant P π) (hP : WeightOK V P) (hPi : WeightOK V (Kernel.const X π)) {z : ℂ}
    (hz0 : z ≠ 0) (hu : z ∈ resolventSet ℂ (qOp V P π)) :
    piOp V π * fundKernel V P π z = z⁻¹ • piOp V π ∧
      fundKernel V P π z * piOp V π = z⁻¹ • piOp V π ∧
      (z ≠ 1 → _root_.resolvent (kOp V P) z =
        fundKernel V P π z * (1 + (z - 1)⁻¹ • piOp V π) ∧
        _root_.resolvent (kOp V P) z =
          fundKernel V P π z + ((z - 1)⁻¹ - z⁻¹) • piOp V π) :=
  resolvent_eq_op (E := BM X) (kOp_mul_piOp hP hPi) (piOp_mul_kOp hP hPi hinv)
    (piOp_mul_self hPi) hz0 (spectrum.mem_resolventSet_iff.1 hu)


/-- `ENNReal.ofReal ‖T‖ = ‖T‖₊` for operators. -/
theorem ofReal_opNorm_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] E) :
    ENNReal.ofReal ‖T‖ = (‖T‖₊ : ℝ≥0∞) :=
  ofReal_norm_eq_nnnorm T

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `|||Pⁿ − 1 ⊗ π|||_V ≤ ‖(P − Π)ⁿ‖` for `n ≥ 1`. -/
theorem vErgDist_le_nnnorm_sub_pow [IsMarkovKernel P] [IsProbabilityMeasure π]
    (hinv : IsInvariant P π) (hP : WeightOK V P) (hPi : WeightOK V (Kernel.const X π)) {n : ℕ}
    (hn : n ≠ 0) :
    vErgDist (eW V) P π n ≤ (‖(qOp V P π) ^ n‖₊ : ℝ≥0∞) := by
  have hpow := sub_proj_pow (A := BM X →L[ℂ] BM X) (kOp_mul_piOp hP hPi)
    (piOp_mul_kOp hP hPi hinv) (piOp_mul_self hPi) hn
  exact ((vErgDist_le_norm hP hPi n).trans_eq
    (congrArg (fun T : BM X →L[ℂ] BM X => ENNReal.ofReal ‖T‖) hpow).symm).trans_eq
    (ofReal_opNorm_eq _)

/-- **The spectral rate in operator form** (the proof of Theorem 20.1.1 (ii), MT p. 513, by
Gelfand's formula instead of the contour integral): if `PΠ = ΠP = Π² = Π`, `z − (P − Π)` is
invertible for `|z| > ε₀`, `ε₀ < 1`, and `d n ≤ ‖(P − Π)ⁿ‖` (`n ≥ 1`) with every `d n` finite,
then `ρ = spectralRadius (P − Π) ≤ ε₀`, `ρ = sup {|z| : z ∈ σ(P), z ≠ 1}`,
`limsup (d n)^{1/n} ≤ ρ`, and `d n ≤ R εⁿ` for every `ε > ρ`. -/
theorem spectral_rate_op {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {P Pr : E →L[ℂ] E} (hPE : P * Pr = Pr) (hEP : Pr * P = Pr) (hEE : Pr * Pr = Pr) {ε₀ : ℝ}
    (hε₀ : ε₀ < 1) (hZ : ∀ z : ℂ, ε₀ < ‖z‖ → z ∈ resolventSet ℂ (P - Pr)) (d : ℕ → ℝ≥0∞)
    (hd : ∀ n, n ≠ 0 → d n ≤ (‖(P - Pr) ^ n‖₊ : ℝ≥0∞)) (hdt : ∀ n, d n ≠ ∞) :
    spectralRadius ℂ (P - Pr) ≤ ENNReal.ofReal ε₀ ∧
      spectralRadius ℂ (P - Pr) = ⨆ z ∈ spectrum ℂ P \ {1}, (‖z‖₊ : ℝ≥0∞) ∧
      limsup (fun n : ℕ => d n ^ (1 / n : ℝ)) atTop ≤ spectralRadius ℂ (P - Pr) ∧
      ∀ ε : ℝ, spectralRadius ℂ (P - Pr) < ENNReal.ofReal ε →
        ∃ R : ℝ, ∀ n, d n ≤ ENNReal.ofReal (R * ε ^ n) := by
  set Q := P - Pr with hQ
  have hnotQ : ∀ k ∈ spectrum ℂ Q, ‖k‖ ≤ ε₀ := fun k hk => by
    by_contra h
    exact (spectrum.mem_iff.1 hk) (spectrum.mem_resolventSet_iff.1 (hZ k (not_le.1 h)))
  have hSR : spectralRadius ℂ Q = ⨆ k ∈ spectrum ℂ Q, (‖k‖₊ : ℝ≥0∞) :=
    spectralRadius_eq_of_unital Q
  have hρ0 : spectralRadius ℂ Q ≤ ENNReal.ofReal ε₀ := by
    rw [hSR]
    refine iSup₂_le fun k hk => ?_
    rw [← ofReal_norm_eq_nnnorm]
    exact ENNReal.ofReal_le_ofReal (hnotQ k hk)
  have h1Q : (1 : ℂ) ∉ spectrum ℂ Q := fun h => by
    have := hnotQ 1 h; rw [norm_one] at this; linarith
  have hρeq : spectralRadius ℂ Q = ⨆ z ∈ spectrum ℂ P \ {1}, (‖z‖₊ : ℝ≥0∞) := by
    rw [hSR]
    refine le_antisymm (iSup₂_le fun k hk => ?_) (iSup₂_le fun k hk => ?_)
    · rcases eq_or_ne k 0 with rfl | hk0
      · rw [nnnorm_zero, ENNReal.coe_zero]; exact zero_le
      have hk1 : k ≠ 1 := fun h => h1Q (h ▸ hk)
      exact le_iSup₂_of_le (f := fun z (_ : z ∈ spectrum ℂ P \ {1}) => (‖z‖₊ : ℝ≥0∞)) k
        ⟨(mem_spectrum_iff_sub_proj_op hPE hEP hEE hk0 hk1).2 hk, hk1⟩ le_rfl
    · rcases eq_or_ne k 0 with rfl | hk0
      · rw [nnnorm_zero, ENNReal.coe_zero]; exact zero_le
      exact le_iSup₂_of_le (f := fun z (_ : z ∈ spectrum ℂ Q) => (‖z‖₊ : ℝ≥0∞)) k
        ((mem_spectrum_iff_sub_proj_op hPE hEP hEE hk0 hk.2).1 hk.1) le_rfl
  have hG := spectrum.gelfand_formula Q
  have hlim : limsup (fun n : ℕ => d n ^ (1 / n : ℝ)) atTop ≤ spectralRadius ℂ Q := by
    rw [← hG.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ENNReal.rpow_le_rpow (hd n (by omega)) (by positivity)
  refine ⟨hρ0, hρeq, hlim, fun ε hε => ?_⟩
  have hεpos : 0 < ε := ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hG.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop 1))
  refine ⟨1 + ∑ k ∈ Finset.range N, (d k).toReal / ε ^ k, fun n => ?_⟩
  have hεn : 0 < ε ^ n := pow_pos hεpos n
  rcases lt_or_ge n N with hnN | hnN
  · rw [← ENNReal.ofReal_toReal (hdt n)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (d n).toReal / ε ^ n ≤ ∑ k ∈ Finset.range N, (d k).toReal / ε ^ k :=
      Finset.single_le_sum (f := fun k => (d k).toReal / ε ^ k)
        (fun k _ => div_nonneg ENNReal.toReal_nonneg (pow_nonneg hεpos.le k))
        (Finset.mem_range.2 hnN)
    calc (d n).toReal = (d n).toReal / ε ^ n * ε ^ n := by field_simp
      _ ≤ (1 + ∑ k ∈ Finset.range N, (d k).toReal / ε ^ k) * ε ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) hεn.le
  · have hS : 0 ≤ ∑ k ∈ Finset.range N, (d k).toReal / ε ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg ENNReal.toReal_nonneg (pow_nonneg hεpos.le k)
    obtain ⟨hlt, hn1⟩ := hN n hnN
    have hn0 : n ≠ 0 := by omega
    have hpowlt : (‖Q ^ n‖₊ : ℝ≥0∞) < ENNReal.ofReal ε ^ n := by
      have := ENNReal.pow_lt_pow_left hn0 hlt
      rwa [one_div, ENNReal.rpow_inv_natCast_pow hn0] at this
    refine (hd n hn0).trans (hpowlt.le.trans ?_)
    rw [← ENNReal.ofReal_pow hεpos.le]
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hεn.le (by linarith))

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- **Theorem 20.1.1 (ii)** (MT p. 513): suppose `P` and `1 ⊗ π` act on `L∞_V` and `Z_z` exists
as a bounded operator on `L∞_V` for every `|z| > ε₀`, with `ε₀ < 1`. Then, with
`λ* = spectralRadius(P − 1 ⊗ π)`:
* `λ* ≤ ε₀ < 1`, and `λ* = sup {|z| : z ∈ S_V(P), z ≠ 1}` (the minimal `ε₀`);
* the rate (20.3): `limsup |||Pⁿ − 1 ⊗ π|||_V^{1/n} ≤ λ*`, i.e.
  `limsup n⁻¹ log |||Pⁿ − 1 ⊗ π|||_V ≤ log λ*`; in bound form,
  `|||Pⁿ − 1 ⊗ π|||_V ≤ R εⁿ` for every `ε > λ*`;
* the chain is `V`-uniformly ergodic. -/
theorem theorem_20_1_1_ii [IsMarkovKernel P] [IsProbabilityMeasure π] (hinv : IsInvariant P π)
    (hP : WeightOK V P) (hPi : WeightOK V (Kernel.const X π)) {ε₀ : ℝ} (hε₀ : ε₀ < 1)
    (hZ : ∀ z : ℂ, ε₀ < ‖z‖ → z ∈ resolventSet ℂ (qOp V P π)) :
    IsVUniformlyErgodic (eW V) P π ∧
      spectralRadius ℂ (qOp V P π) ≤ ENNReal.ofReal ε₀ ∧
      spectralRadius ℂ (qOp V P π) =
        ⨆ z ∈ spectrumV V P \ {1}, (‖z‖₊ : ℝ≥0∞) ∧
      limsup (fun n : ℕ => vErgDist (eW V) P π n ^ (1 / n : ℝ)) atTop ≤
        spectralRadius ℂ (qOp V P π) ∧
      ∀ ε : ℝ, spectralRadius ℂ (qOp V P π) < ENNReal.ofReal ε →
        ∃ R : ℝ, ∀ n, vErgDist (eW V) P π n ≤ ENNReal.ofReal (R * ε ^ n) := by
  have := completeSpace_BM (X := X)
  obtain ⟨hρ0, hρeq, hlim, hrate⟩ := spectral_rate_op (E := BM X) (kOp_mul_piOp hP hPi)
    (piOp_mul_kOp hP hPi hinv) (piOp_mul_self hPi) hε₀ hZ (vErgDist (eW V) P π)
    (fun n hn => vErgDist_le_nnnorm_sub_pow hinv hP hPi hn)
    (fun n => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (vErgDist_le_norm hP hPi n))
  refine ⟨⟨hinv, ?_⟩, hρ0, hρeq, hlim, hrate⟩
  set ε := (max ε₀ 0 + 1) / 2 with hεdef
  have hmax : max ε₀ 0 < 1 := max_lt hε₀ zero_lt_one
  have hεpos : 0 < ε := by have := le_max_right ε₀ 0; rw [hεdef]; linarith
  have hε1 : ε < 1 := by rw [hεdef]; linarith
  have hρε : spectralRadius ℂ (qOp V P π) < ENNReal.ofReal ε :=
    lt_of_le_of_lt (hρ0.trans (ENNReal.ofReal_le_ofReal (le_max_left ε₀ 0)))
      ((ENNReal.ofReal_lt_ofReal_iff hεpos).2 (by rw [hεdef]; linarith))
  obtain ⟨R, hR⟩ := hrate ε hρε
  have hlim0 : Tendsto (fun n : ℕ => ENNReal.ofReal (R * ε ^ n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hεpos.le hε1).const_mul R
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0 (fun _ => zero_le)
    hR

/-! ### Poisson's equation and eigenfunctions -/

/-- `P Z = Z − I + Π` for the fundamental kernel `Z = [I − P + Π]⁻¹` (operator form). -/
theorem mul_fund_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Pr : E →L[ℂ] E} (hPE : P * Pr = Pr) (hEP : Pr * P = Pr) (hEE : Pr * Pr = Pr)
    (hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) 1 - (P - Pr))) :
    P * _root_.resolvent (P - Pr) (1 : ℂ) = _root_.resolvent (P - Pr) (1 : ℂ) - 1 + Pr := by
  have h1 := Ring.mul_inverse_cancel _ hu
  obtain ⟨hEZ, -⟩ := proj_mul_inv hPE hEP hEE one_ne_zero h1 (Ring.inverse_mul_cancel _ hu)
  rw [inv_one, one_smul] at hEZ
  set Z := Ring.inverse (algebraMap ℂ (E →L[ℂ] E) 1 - (P - Pr)) with hZ
  have hA : algebraMap ℂ (E →L[ℂ] E) 1 = 1 := map_one _
  rw [hA, sub_mul, sub_mul, one_mul, hEZ] at h1
  have key : P * Z = Z - 1 + Pr := by rw [← h1]; abel
  exact key

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- **The fundamental kernel solves Poisson's equation** (MT p. 511): if `Z = Z_1` exists on
`L∞_V`, then for every `f = gV ∈ L∞_V` the function `f̂ = (Zg)V` satisfies
`P f̂ = f̂ − f + π(f)`, Poisson's equation (17.37). -/
theorem fundKernel_poisson [IsMarkovKernel P] [IsProbabilityMeasure π] (hinv : IsInvariant P π)
    (hP : WeightOK V P) (hPi : WeightOK V (Kernel.const X π))
    (hu : (1 : ℂ) ∈ resolventSet ℂ (qOp V P π)) (g : BM X) (x : X) :
    ∫ y, bmFun (fundKernel V P π 1 g) y * (V y : ℂ) ∂P x =
      bmFun (fundKernel V P π 1 g) x * V x - bmFun g x * V x + ∫ y, bmFun g y * (V y : ℂ) ∂π := by
  have key := mul_fund_eq (E := BM X) (kOp_mul_piOp hP hPi) (piOp_mul_kOp hP hPi hinv)
    (piOp_mul_self hPi) (spectrum.mem_resolventSet_iff.1 hu)
  have h2 : kOp V P (fundKernel V P π 1 g) =
      fundKernel V P π 1 g - g + piOp V π g :=
    congrArg (fun T : BM X →L[ℂ] BM X => T g) key
  have h : bmFun (kOp V P (fundKernel V P π 1 g)) x =
      bmFun (fundKernel V P π 1 g - g + piOp V π g) x :=
    congrArg (fun w => bmFun w x) h2
  rw [kOp_apply hP, kFun, bmFun_add, bmFun_sub, piOp, kOp_const_apply hPi] at h
  have hV0 : (V x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hP.pos x).ne'
  calc ∫ y, bmFun (fundKernel V P π 1 g) y * (V y : ℂ) ∂P x
      = (V x : ℂ) * (((V x : ℂ))⁻¹ * ∫ y, bmFun (fundKernel V P π 1 g) y * (V y : ℂ) ∂P x) := by
        field_simp
    _ = (V x : ℂ) * (bmFun (fundKernel V P π 1 g) x - bmFun g x +
          ((V x : ℂ))⁻¹ * ∫ y, bmFun g y * (V y : ℂ) ∂π) := by rw [h]
    _ = _ := by field_simp

/-- **Eigenfunctions and the rate of convergence** (MT p. 512): if `Ph = λh` with `λ ≠ 1`, then
`Πh = 0` (that is `π(h) = 0`) and `(Pⁿ − Π)h = λⁿh`, so `|Pⁿh − π(h)| = |λ|ⁿ|h|` exactly. -/
theorem eigen_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Pr : E →L[ℂ] E} (hEP : Pr * P = Pr) {lam : ℂ} (hlam : lam ≠ 1) {h : E}
    (hh : P h = lam • h) : Pr h = 0 ∧ ∀ n : ℕ, (P ^ n - Pr) h = lam ^ n • h := by
  have hPr : Pr h = 0 := by
    have : Pr h = lam • Pr h := by
      calc Pr h = (Pr * P) h := by rw [hEP]
        _ = lam • Pr h := by
          change Pr (P h) = _; rw [hh, map_smul]
    have h2 : (1 - lam) • Pr h = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hlam))
  have hpow : ∀ n : ℕ, (P ^ n) h = lam ^ n • h := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', mul_smul]
      change P ((P ^ n) h) = _
      rw [ih, map_smul, hh, smul_smul, smul_smul, mul_comm]
  refine ⟨hPr, fun n => ?_⟩
  change (P ^ n) h - Pr h = _
  rw [hpow, hPr, sub_zero]

end MeynTweedie.Epilogue
