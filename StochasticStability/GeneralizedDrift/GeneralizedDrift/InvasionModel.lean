/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.StateDependentDrift

/-!
# An invasion/antibody model (MT §19.1.3)

Meyn and Tweedie, §19.1.3, pp. 489–491. A Markov kernel `P` on `ℤ₊²` (invaders, defenders).

**The precise reading of the assumptions** (the book's are partly informal). With
`S(i, j) = i + j`, `I = {i, j ≥ 1}`, constants `ε > ½` and `d ∈ ℤ₊`:
* (A1), (19.26): `E_{i,j}[S(Φ₁)] ≤ i + j − 2ε` on all of `I` (the book writes `i, j > 1` in
  (19.26) but uses the drift on `I = {i, j ≥ 1}`);
* (A2), (19.27): `P((i, 0), (0, 0)) = 1` for `i > d`;
* (A3), (19.28): from `(0, j)`, `j > 0`, the chain jumps to `(j + k, j)` with `1 ≤ k ≤ d`;
* left-continuity, (19.29): in `I` neither coordinate decreases by more than one in a step. The
  book's (19.29) forbids only simultaneous decreases by more than one, but its `(j + 1)`-step
  bound needs the chain started at `(j + k, j)` to stay in `I` for `j` steps, which is this
  condition;
* the "new population of finite mean size" at `(i, 0)`, `i ≤ d`, and the finite mean of the
  increments from `(0, 0)`: `E_{(i,0)}[S(Φ₁)] < ∞` for `i ≤ d`.

**Results.**
* `invasion_pow_le`: by (A1) and left-continuity, `E_x[S(Φₘ)] ≤ S(x) − 2εm` while both
  coordinates of `x` are at least `m`.
* `invasion_stateDrift` (p. 490): with `V = S/β`, `0 < β < 2ε − 1`, the state-dependent drift
  (19.10) holds with `n = 1` on `I` and on `B₁(c) = {(i, 0) : i > c}`, and `n(0, j) = j + 1` on
  `B₂(c) = {(0, j) : j > c}`, for `c > d` with `c ≥ β` and `(2ε − 1 − β)c ≥ d + β`; the test set
  is the finite set `C = {(i, 0), (0, j) : i, j ≤ c}`.
* `invasion_meanReturnTime` (p. 490): `E_{(i,j)}[τ_C] ≤ (i + j)/β` off `C`, regardless of `d`.
* `invasion_positiveHarris`: if the chain is `ψ`-irreducible and `C` is petite, it is positive
  Harris recurrent (Theorem 19.1.2).

**Hypotheses.** The book asserts `δ_{(0,0)}`-irreducibility "under (A1)–(A3), regardless of the
behaviour at zero", but (A1)–(A3) do not force the chain to reach `(0, 0)`; the positivity is
stated under irreducibility of the chain and petiteness of the finite set `C`.

**Left out.** The geometric ergodicity sketch of p. 491 (the test function `e^{αi} + e^{αj}`,
"using a Taylor series expansion" under (19.30)–(19.31)) is not formalised: its constants and the
`(j + 1)`-step bound are only indicated.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology

/-- The total population `S(i, j) = i + j`. -/
def invS (x : ℕ × ℕ) : ℝ≥0∞ := ((x.1 + x.2 : ℕ) : ℝ≥0∞)

/-- **The `m`-step drift in the interior**: under (A1) and left-continuity,
`E_x[S(Φₘ)] + 2εm ≤ S(x)` when both coordinates of `x` are at least `m`. -/
theorem invasion_pow_le (P : Kernel (ℕ × ℕ) (ℕ × ℕ)) [IsMarkovKernel P] {ε : ℝ}
    (hA1 : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → ∫⁻ y, invS y ∂P x + ENNReal.ofReal (2 * ε) ≤ invS x)
    (hLC : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → P x {y | x.1 ≤ y.1 + 1 ∧ x.2 ≤ y.2 + 1} = 1) :
    ∀ (m : ℕ) (x : ℕ × ℕ), m ≤ x.1 → m ≤ x.2 →
      ∫⁻ y, invS y ∂(P ^ m) x + ENNReal.ofReal (2 * ε) * m ≤ invS x := by
  have hSm : Measurable invS := measurable_of_countable _
  intro m
  induction m with
  | zero =>
    intro x _ _
    rw [pow_zero_apply, lintegral_dirac' x hSm]
    simp
  | succ m ih =>
    intro x h1 h2
    have := isMarkovKernel_pow P m
    have hset : MeasurableSet {y : ℕ × ℕ | x.1 ≤ y.1 + 1 ∧ x.2 ≤ y.2 + 1} :=
      (Set.to_countable _).measurableSet
    have hae : ∀ᵐ y ∂P x, x.1 ≤ y.1 + 1 ∧ x.2 ≤ y.2 + 1 := by
      have h := hLC x (by omega) (by omega)
      rw [ae_iff]
      have : {a : ℕ × ℕ | ¬ (x.1 ≤ a.1 + 1 ∧ x.2 ≤ a.2 + 1)} =
          {y : ℕ × ℕ | x.1 ≤ y.1 + 1 ∧ x.2 ≤ y.2 + 1}ᶜ := rfl
      rw [this, prob_compl_eq_zero_iff hset]
      exact h
    have hp : P ^ (m + 1) = (P ^ m) ∘ₖ P := by rw [show m + 1 = 1 + m by ring, pow_add_eq, pow_one]
    rw [hp, Kernel.lintegral_comp _ _ _ hSm]
    have hstep : ∫⁻ y, ∫⁻ z, invS z ∂(P ^ m) y ∂P x + ENNReal.ofReal (2 * ε) * m ≤
        ∫⁻ y, invS y ∂P x := by
      calc ∫⁻ y, ∫⁻ z, invS z ∂(P ^ m) y ∂P x + ENNReal.ofReal (2 * ε) * m
          = ∫⁻ y, (∫⁻ z, invS z ∂(P ^ m) y + ENNReal.ofReal (2 * ε) * m) ∂P x := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ y, invS y ∂P x := lintegral_mono_ae (hae.mono fun y hy =>
            ih y (by omega) (by omega))
    calc ∫⁻ y, ∫⁻ z, invS z ∂(P ^ m) y ∂P x + ENNReal.ofReal (2 * ε) * ((m + 1 : ℕ) : ℝ≥0∞)
        = (∫⁻ y, ∫⁻ z, invS z ∂(P ^ m) y ∂P x + ENNReal.ofReal (2 * ε) * m) +
            ENNReal.ofReal (2 * ε) := by push_cast; ring
      _ ≤ ∫⁻ y, invS y ∂P x + ENNReal.ofReal (2 * ε) := add_le_add hstep le_rfl
      _ ≤ invS x := hA1 x (by omega) (by omega)

/-- The number of steps: `n(0, j) = j + 1` on `B₂(c)` and `n = 1` elsewhere. -/
def invN (c : ℕ) (x : ℕ × ℕ) : ℕ := if x.1 = 0 ∧ c < x.2 then x.2 + 1 else 1

/-- The finite test set `C = {(i, 0) : i ≤ c} ∪ {(0, j) : j ≤ c}`. -/
def invC (c : ℕ) : Set (ℕ × ℕ) := {x | (x.2 = 0 ∧ x.1 ≤ c) ∨ (x.1 = 0 ∧ x.2 ≤ c)}

/-- The test function `V = S/β`. -/
noncomputable def invV (β : ℝ) (x : ℕ × ℕ) : ℝ≥0∞ := invS x * ENNReal.ofReal β⁻¹

/-- The constant `b` of (19.10): the sum of `PV` over the finite set `C`, plus one. -/
noncomputable def invB (P : Kernel (ℕ × ℕ) (ℕ × ℕ)) (β : ℝ) (c : ℕ) : ℝ≥0∞ :=
  1 + ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) +
    ∑ j ∈ range (c + 1), ∫⁻ y, invV β y ∂P (0, j)

/-- **The state-dependent drift of the invasion model** (MT p. 490): under the reading of
(A1)–(A3) and left-continuity in the module docstring, with `0 < β < 2ε − 1` and `c > d`,
`c ≥ β`, `(2ε − 1 − β)c ≥ d + β`, the drift (19.10) holds for `V = S/β`, `n = invN c` and the
test set `C = invC c`. -/
theorem invasion_stateDrift (P : Kernel (ℕ × ℕ) (ℕ × ℕ)) [IsMarkovKernel P] {ε β : ℝ} {d c : ℕ}
    (hβ0 : 0 < β) (hβε : β < 2 * ε - 1) (hcd : d < c) (hcβ : β ≤ c)
    (hc : d + β ≤ (2 * ε - 1 - β) * c)
    (hA1 : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → ∫⁻ y, invS y ∂P x + ENNReal.ofReal (2 * ε) ≤ invS x)
    (hA2 : ∀ i, d < i → P (i, 0) {((0 : ℕ), (0 : ℕ))} = 1)
    (hA3 : ∀ j, 0 < j → P (0, j) {y | y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d} = 1)
    (hLC : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → P x {y | x.1 ≤ y.1 + 1 ∧ x.2 ≤ y.2 + 1} = 1)
    (x : ℕ × ℕ) :
    ∫⁻ y, invV β y ∂(P ^ invN c x) x + invN c x ≤
      invV β x + (invC c).indicator (fun _ => invB P β c) x := by
  have hSm : Measurable invS := measurable_of_countable _
  have hVm : Measurable (invV β) := measurable_of_countable _
  have hlintV : ∀ μ : Measure (ℕ × ℕ), ∫⁻ y, invV β y ∂μ = (∫⁻ y, invS y ∂μ) * ENNReal.ofReal β⁻¹ :=
    fun μ => lintegral_mul_const _ hSm
  have hβinv : 0 < β⁻¹ := inv_pos.2 hβ0
  rcases Nat.eq_zero_or_pos x.1 with hx1 | hx1 <;> rcases Nat.eq_zero_or_pos x.2 with hx2 | hx2
  · -- `x = (0, 0) ∈ C`
    have hxC : x ∈ invC c := Or.inl ⟨hx2, by omega⟩
    have hn : invN c x = 1 := by simp [invN, hx2]
    rw [hn, pow_one, indicator_of_mem hxC, invB, Nat.cast_one]
    have hmem : ∫⁻ y, invV β y ∂P x ≤ ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) := by
      have : x = (x.1, 0) := Prod.ext rfl hx2
      rw [this]
      exact single_le_sum (f := fun i => ∫⁻ y, invV β y ∂P (i, 0)) (fun _ _ => zero_le)
        (Finset.mem_range.2 (by omega))
    calc ∫⁻ y, invV β y ∂P x + 1 ≤ ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) + 1 :=
          add_le_add hmem le_rfl
      _ ≤ invV β x + (1 + ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) +
          ∑ j ∈ range (c + 1), ∫⁻ y, invV β y ∂P (0, j)) := by
          rw [add_comm (∑ i ∈ range (c + 1), _) 1]
          exact le_add_left (le_self_add)
  · -- `x = (0, j)`, `j ≥ 1`
    rcases le_or_gt x.2 c with hjc | hjc
    · have hxC : x ∈ invC c := Or.inr ⟨hx1, hjc⟩
      have hn : invN c x = 1 := by simp [invN, hx1, not_lt.2 hjc]
      rw [hn, pow_one, indicator_of_mem hxC, invB, Nat.cast_one]
      have hmem : ∫⁻ y, invV β y ∂P x ≤ ∑ j ∈ range (c + 1), ∫⁻ y, invV β y ∂P (0, j) := by
        have : x = (0, x.2) := Prod.ext hx1 rfl
        rw [this]
        exact single_le_sum (f := fun j => ∫⁻ y, invV β y ∂P (0, j)) (fun _ _ => zero_le)
          (Finset.mem_range.2 (by omega))
      calc ∫⁻ y, invV β y ∂P x + 1 ≤ ∑ j ∈ range (c + 1), ∫⁻ y, invV β y ∂P (0, j) + 1 :=
            add_le_add hmem le_rfl
        _ ≤ invV β x + (1 + ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) +
            ∑ j ∈ range (c + 1), ∫⁻ y, invV β y ∂P (0, j)) := by
            rw [add_comm (∑ j ∈ range (c + 1), _) 1]
            exact le_add_left (add_le_add le_self_add le_rfl)
    · -- `B₂(c)`: the `(j + 1)`-step drift
      have hxC : x ∉ invC c := by
        rintro (⟨h, -⟩ | ⟨-, h⟩) <;> omega
      set j := x.2 with hjdef
      have hn : invN c x = j + 1 := by unfold invN; split_ifs <;> omega
      rw [hn, indicator_of_notMem hxC, add_zero]
      have hpow := invasion_pow_le P hA1 hLC j
      have := isMarkovKernel_pow P j
      have hset : MeasurableSet {y : ℕ × ℕ | y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d} :=
        (Set.to_countable _).measurableSet
      have hae : ∀ᵐ y ∂P x, y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d := by
        have h := hA3 j hx2
        rw [show (0, j) = x from Prod.ext hx1.symm rfl] at h
        rw [ae_iff]
        have : {a : ℕ × ℕ | ¬ (a.2 = j ∧ j + 1 ≤ a.1 ∧ a.1 ≤ j + d)} =
            {y : ℕ × ℕ | y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d}ᶜ := rfl
        rw [this, prob_compl_eq_zero_iff hset]
        exact h
      have hT : ∫⁻ y, invS y ∂(P ^ (j + 1)) x + ENNReal.ofReal (2 * ε) * j ≤
          ((2 * j + d : ℕ) : ℝ≥0∞) := by
        rw [show P ^ (j + 1) = (P ^ j) ∘ₖ P by rw [show j + 1 = 1 + j by ring, pow_add_eq, pow_one],
          Kernel.lintegral_comp _ _ _ hSm]
        calc ∫⁻ y, ∫⁻ z, invS z ∂(P ^ j) y ∂P x + ENNReal.ofReal (2 * ε) * j
            = ∫⁻ y, (∫⁻ z, invS z ∂(P ^ j) y + ENNReal.ofReal (2 * ε) * j) ∂P x := by
              rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ ∫⁻ _y, ((2 * j + d : ℕ) : ℝ≥0∞) ∂P x := lintegral_mono_ae (hae.mono fun y hy => by
              refine (hpow y (by omega) (by omega)).trans ?_
              rw [invS]
              exact_mod_cast (by omega : y.1 + y.2 ≤ 2 * j + d))
          _ = ((2 * j + d : ℕ) : ℝ≥0∞) := by rw [lintegral_const, measure_univ, mul_one]
      set T := ∫⁻ y, invS y ∂(P ^ (j + 1)) x with hTdef
      have hTfin : T ≠ ∞ :=
        ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (le_trans le_self_add hT)
      have hTr : T.toReal + 2 * ε * j ≤ 2 * j + d := by
        have h := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hT
        rw [ENNReal.toReal_add hTfin
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal
          (by linarith), ENNReal.toReal_natCast] at h
        push_cast at h
        exact h
      have hjc' : (c : ℝ) ≤ j := by exact_mod_cast hjc.le
      have hkey : T.toReal * β⁻¹ + (j + 1) ≤ j * β⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_add' _ _ _ hβ0.ne',
          div_le_div_iff_of_pos_right hβ0]
        have h1 : (d : ℝ) + β ≤ (2 * ε - 1 - β) * j :=
          hc.trans (mul_le_mul_of_nonneg_left hjc' (by linarith))
        nlinarith
      have hgoal : ∫⁻ y, invV β y ∂(P ^ (j + 1)) x + ((j + 1 : ℕ) : ℝ≥0∞) =
          ENNReal.ofReal (T.toReal * β⁻¹ + (j + 1)) := by
        rw [hlintV, ← hTdef, ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hβinv.le)
          (by positivity), ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hTfin]
        congr 1
        rw [← ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
      have hV : invV β x = ENNReal.ofReal (j * β⁻¹) := by
        rw [invV, invS, hx1, zero_add, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
      rw [hgoal, hV]
      exact ENNReal.ofReal_le_ofReal hkey
  · -- `x = (i, 0)`, `i ≥ 1`
    rcases le_or_gt x.1 c with hic | hic
    · have hxC : x ∈ invC c := Or.inl ⟨hx2, hic⟩
      have hn : invN c x = 1 := by simp [invN, show x.1 ≠ 0 by omega]
      rw [hn, pow_one, indicator_of_mem hxC, invB, Nat.cast_one]
      have hmem : ∫⁻ y, invV β y ∂P x ≤ ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) := by
        have : x = (x.1, 0) := Prod.ext rfl hx2
        rw [this]
        exact single_le_sum (f := fun i => ∫⁻ y, invV β y ∂P (i, 0)) (fun _ _ => zero_le)
          (Finset.mem_range.2 (by omega))
      calc ∫⁻ y, invV β y ∂P x + 1 ≤ ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) + 1 :=
            add_le_add hmem le_rfl
        _ ≤ invV β x + (1 + ∑ i ∈ range (c + 1), ∫⁻ y, invV β y ∂P (i, 0) +
            ∑ j ∈ range (c + 1), ∫⁻ y, invV β y ∂P (0, j)) := by
            rw [add_comm (∑ i ∈ range (c + 1), _) 1]
            exact le_add_left le_self_add
    · -- `B₁(c)`: the body dies
      have hxC : x ∉ invC c := by
        rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
      have hn : invN c x = 1 := by simp [invN, show x.1 ≠ 0 by omega]
      rw [hn, pow_one, indicator_of_notMem hxC, add_zero, Nat.cast_one]
      have h0 : P x {((0 : ℕ), (0 : ℕ))}ᶜ = 0 := by
        rw [prob_compl_eq_zero_iff (measurableSet_singleton _)]
        have h := hA2 x.1 (by omega)
        rwa [show (x.1, 0) = x from Prod.ext rfl hx2.symm] at h
      have hae : ∀ᵐ y ∂P x, y = ((0 : ℕ), (0 : ℕ)) := by
        rw [ae_iff]; exact h0
      rw [lintegral_congr_ae (g := fun _ => invV β ((0 : ℕ), (0 : ℕ)))
        (hae.mono fun y hy => by rw [hy]), lintegral_const, measure_univ,
        mul_one]
      simp only [invV, invS, add_zero, Nat.cast_zero, zero_mul, zero_add]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hi : (c : ℝ) + 1 ≤ ((x.1 + x.2 : ℕ) : ℝ) := by
        rw [hx2, add_zero]; exact_mod_cast (show c + 1 ≤ x.1 from hic)
      rw [← div_eq_mul_inv, le_div_iff₀ hβ0, one_mul]
      linarith
  · -- the interior `I`
    have hxC : x ∉ invC c := by
      rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega
    have hn : invN c x = 1 := by simp [invN, show x.1 ≠ 0 by omega]
    rw [hn, pow_one, indicator_of_notMem hxC, add_zero, Nat.cast_one, hlintV, invV]
    have h := hA1 x hx1 hx2
    have h1 : 1 ≤ ENNReal.ofReal (2 * ε) * ENNReal.ofReal β⁻¹ := by
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← div_eq_mul_inv, le_div_iff₀ hβ0, one_mul]
      linarith
    calc (∫⁻ y, invS y ∂P x) * ENNReal.ofReal β⁻¹ + 1
        ≤ (∫⁻ y, invS y ∂P x) * ENNReal.ofReal β⁻¹ +
            ENNReal.ofReal (2 * ε) * ENNReal.ofReal β⁻¹ := add_le_add le_rfl h1
      _ = (∫⁻ y, invS y ∂P x + ENNReal.ofReal (2 * ε)) * ENNReal.ofReal β⁻¹ := by ring
      _ ≤ invS x * ENNReal.ofReal β⁻¹ := mul_le_mul' h le_rfl

/-- **The mean hitting time of `C`** (MT p. 490): under the assumptions of
`invasion_stateDrift`, `E_x[τ_C] ≤ V(x) + b 1_C(x)`; off `C`, `E_{(i,j)}[τ_C] ≤ (i + j)/β`,
"regardless of the threshold level `d`". -/
theorem invasion_meanReturnTime (P : Kernel (ℕ × ℕ) (ℕ × ℕ)) [IsMarkovKernel P] {ε β : ℝ}
    {d c : ℕ} (hβ0 : 0 < β) (hβε : β < 2 * ε - 1) (hcd : d < c) (hcβ : β ≤ c)
    (hc : d + β ≤ (2 * ε - 1 - β) * c)
    (hA1 : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → ∫⁻ y, invS y ∂P x + ENNReal.ofReal (2 * ε) ≤ invS x)
    (hA2 : ∀ i, d < i → P (i, 0) {((0 : ℕ), (0 : ℕ))} = 1)
    (hA3 : ∀ j, 0 < j → P (0, j) {y | y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d} = 1)
    (hLC : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → P x {y | x.1 ≤ y.1 + 1 ∧ x.2 ≤ y.2 + 1} = 1) :
    (∀ x, meanReturnTime P (invC c) x ≤ invV β x + (invC c).indicator (fun _ => invB P β c) x) ∧
      ∀ x ∉ invC c, meanReturnTime P (invC c) x ≤ ENNReal.ofReal ((x.1 + x.2 : ℕ) / β) := by
  have hall := meanReturnTime_le_stateDrift P (n := invN c) (measurable_of_countable _)
    (fun x => by unfold invN; split_ifs <;> omega) (measurable_of_countable _)
    ((Set.to_countable _).measurableSet)
    (invasion_stateDrift P hβ0 hβε hcd hcβ hc hA1 hA2 hA3 hLC)
  refine ⟨hall, fun x hx => ?_⟩
  refine (hall x).trans (le_of_eq ?_)
  rw [indicator_of_notMem hx, add_zero, invV, invS, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), div_eq_mul_inv]

variable [MeasurableSpace.CountablyGenerated (ℕ × ℕ)] in
/-- **Positive Harris recurrence of the invasion model** (MT p. 490, Theorem 19.1.2): under the
assumptions of `invasion_stateDrift`, if the boundary populations generated at `(i, 0)`,
`i ≤ d`, have finite mean, the chain is `ψ`-irreducible and the finite set `C` is petite, the
chain is positive Harris recurrent. -/
theorem invasion_positiveHarris (P : Kernel (ℕ × ℕ) (ℕ × ℕ)) [IsMarkovKernel P]
    {ψ : Measure (ℕ × ℕ)} (hψ : IsMaximalIrreducibility P ψ) {ε β : ℝ} {d c : ℕ}
    (hβ0 : 0 < β) (hβε : β < 2 * ε - 1) (hcd : d < c) (hcβ : β ≤ c)
    (hc : d + β ≤ (2 * ε - 1 - β) * c)
    (hA1 : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → ∫⁻ y, invS y ∂P x + ENNReal.ofReal (2 * ε) ≤ invS x)
    (hA2 : ∀ i, d < i → P (i, 0) {((0 : ℕ), (0 : ℕ))} = 1)
    (hA3 : ∀ j, 0 < j → P (0, j) {y | y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d} = 1)
    (hLC : ∀ x : ℕ × ℕ, 1 ≤ x.1 → 1 ≤ x.2 → P x {y | x.1 ≤ y.1 + 1 ∧ x.2 ≤ y.2 + 1} = 1)
    (hfin : ∀ i ≤ d, ∫⁻ y, invS y ∂P (i, 0) ≠ ∞) (hpet : IsPetite P (invC c)) :
    IsPositiveHarris P ψ := by
  have hSm : Measurable invS := measurable_of_countable _
  have hlintV : ∀ μ : Measure (ℕ × ℕ), ∫⁻ y, invV β y ∂μ = (∫⁻ y, invS y ∂μ) * ENNReal.ofReal β⁻¹ :=
    fun μ => lintegral_mul_const _ hSm
  -- `b < ∞`
  have hfin0 : ∀ i, ∫⁻ y, invS y ∂P (i, 0) ≠ ∞ := fun i => by
    rcases le_or_gt i d with hi | hi
    · exact hfin i hi
    · have hae : ∀ᵐ y ∂P (i, 0), y = ((0 : ℕ), (0 : ℕ)) := by
        rw [ae_iff]
        change P (i, 0) {((0 : ℕ), (0 : ℕ))}ᶜ = 0
        rw [prob_compl_eq_zero_iff (measurableSet_singleton _)]; exact hA2 i hi
      rw [lintegral_congr_ae (g := fun _ => invS ((0 : ℕ), (0 : ℕ)))
        (hae.mono fun y hy => by rw [hy])]
      simp [invS]
  have hfinj : ∀ j, ∫⁻ y, invS y ∂P (0, j) ≠ ∞ := fun j => by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj]; exact hfin0 0
    · have hset : MeasurableSet {y : ℕ × ℕ | y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d} :=
        (Set.to_countable _).measurableSet
      have hae : ∀ᵐ y ∂P (0, j), y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d := by
        rw [ae_iff]
        have : {a : ℕ × ℕ | ¬ (a.2 = j ∧ j + 1 ≤ a.1 ∧ a.1 ≤ j + d)} =
            {y : ℕ × ℕ | y.2 = j ∧ j + 1 ≤ y.1 ∧ y.1 ≤ j + d}ᶜ := rfl
        rw [this, prob_compl_eq_zero_iff hset]; exact hA3 j hj
      refine ne_top_of_le_ne_top (b := ((2 * j + d : ℕ) : ℝ≥0∞))
        (ENNReal.natCast_ne_top _) ?_
      calc ∫⁻ y, invS y ∂P (0, j) ≤ ∫⁻ _y, ((2 * j + d : ℕ) : ℝ≥0∞) ∂P (0, j) :=
            lintegral_mono_ae (hae.mono fun y hy => by
              rw [invS]; exact_mod_cast (by omega : y.1 + y.2 ≤ 2 * j + d))
        _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hb : invB P β c ≠ ∞ := by
    rw [invB]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.sum_ne_top.2 fun i _ => ?_⟩, ENNReal.sum_ne_top.2 fun j _ => ?_⟩
    · rw [hlintV]; exact ENNReal.mul_ne_top (hfin0 i) ENNReal.ofReal_ne_top
    · rw [hlintV]; exact ENNReal.mul_ne_top (hfinj j) ENNReal.ofReal_ne_top
  refine (theorem_19_1_2 hψ (n := invN c) (measurable_of_countable _)
    (fun x => by unfold invN; split_ifs <;> omega) (measurable_of_countable _)
    (fun x => ENNReal.mul_ne_top (by simp [invS]) ENNReal.ofReal_ne_top) hb hpet
    (M := ((2 * c : ℕ) : ℝ≥0∞) * ENNReal.ofReal β⁻¹)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) (fun x hx => ?_)
    (invasion_stateDrift P hβ0 hβε hcd hcβ hc hA1 hA2 hA3 hLC)).1
  refine mul_le_mul' ?_ le_rfl
  rw [invS]
  refine Nat.cast_le.2 ?_
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

end MeynTweedie.GeneralizedDrift
