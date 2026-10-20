/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.LocalImplicit

/-!
# The local contraction argument

SLP §18.2, pp. 550–554. With `H` the local solution of §18.2 (7) (`LocalSolution`), the operator
`(Th)(k) = H[k, h²(k)]` (§18.2 (8), `Top`) acts on
`D_λ(I_ε) = {h : h(k*) = k*, |h(k) − h(k′)| ≤ λ|k − k′| on I_ε}` (`Dlam`), `I_ε = [k* − ε, k* + ε]`.
A fixed point of `T` solves the Euler equation (4) on `I_ε`.

* `local_constants`: for `λ ∈ (λ*, 1)`, constants `m₁ > H₁*`, `m₂ > H₂*` and `ε` with
  `m₁ + m₂λ² ≤ λ`, `m₂(1 + λ) < 1`, `m₁ + m₂ ≤ 1` and `H` `(m₁, m₂)`-Lipschitz on `I_ε × I_ε`.
* **Proposition 18.2** (`prop_18_2`, p. 550): for every `λ ∈ (λ*, 1)` there is `ε > 0` with
  `I_ε ⊆ I` and `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`.
* **Exercise 18.3** (`ex_18_3`, p. 551): `T` is (Lipschitz) continuous in the sup norm on
  `D_λ(I_ε)`; `ex_18_3_continuous` for the packaged operator on `C(I_ε)`.
* **Exercise 18.4** (p. 552): (a) `ex_18_4a` (monotone on nondecreasing members) and
  `ex_18_4a_mapsTo`; (b) `ex_18_4b` (repaired).
* **Proposition 18.3** (`prop_18_3`, `prop_18_3_contractingWith`, p. 552): for every
  `λ ∈ (λ*, 1)` there is `ε > 0` such that `T` is a contraction of `D_λ(I_ε)` (as a
  `ContractingWith` self-map of the closed subset `DC ⊆ C(I_ε)`); `prop_18_3_fixedPoint` gives
  the consequences on p. 553: a unique fixed point `g ∈ D_λ(I_ε)`, which solves (4) on `I_ε`, and
  `|g^t(k) − k*| ≤ λ^t |k − k*|` (local stability).
* **Proposition 18.4** (`prop_18_4`, p. 553): the fixed point is strictly increasing on `I_ε`.

`C(I_ε)` is `C(Jint ks ε, ℝ)` with the sup metric; a function on `I_ε` is extended to `ℝ` by
`Set.IccExtend` (`extendC`), so `TC` (the operator on `C(I_ε)`) agrees with `Top` on `I_ε`.

**Corrections.**
* (NOTE 18.2-D, p. 550.) `T` is not defined on all of `C(I)`: (8) needs `h(I) ⊆ I`. Here `Top`
  is defined for all functions, and only its values on `I_ε` for `h` mapping `I_ε` into itself
  (`Dlam.mapsTo`) are used. Verified, harmless.
* (NOTE 18.2-F, manual Ex. 18.3.) The manual's inequality
  `|h_n²(k) − h²(k)| ≤ λ|h_n(k) − h(k)|` is false (`ex_18_3_manual_counterexample`: on
  `[−1, 1]`, `h(k) = −λk`, `h_c(k) = −λk + c·max(k, 0)`, `0 < c ≤ 2λ`, at `k = −1`). The correct
  bound is `|h_n²(k) − h²(k)| ≤ (1 + λ)‖h_n − h‖` (`Top_sub_le`), which gives Exercise 18.3.
* (NOTE 18.2-G, Ex. 18.4a.) **False as stated**: `T` is not monotone on `D_λ(I_ε)`
  (`ex_18_4a_counterexample`: for every `λ ∈ (0, 1]` and `ε ≤ ε₀`, two members `h′ ≤ h` with
  `(Th)(k* + ε) < (Th′)(k* + ε)`). It is monotone on the nondecreasing members (`ex_18_4a`).
* (NOTE 18.2-H, Ex. 18.4b.) The constants `k* ± ε` are not in `D_λ(I_ε)`
  (`ex_18_4b_const_not_mem`). Repaired version `ex_18_4b`: on
  `E = {h : I_ε → I_ε nondecreasing, λ-Lipschitz}` (`Elam`), with `ε` chosen so that also
  `m₁ + m₂ ≤ 1`, `T` maps `E` into itself and is monotone there, `h₋ ≡ k* − ε` and
  `h₊ ≡ k* + ε` lie in `E` with `h₋ ≤ Th₋`, `Th₊ ≤ h₊`, the iterates `Tⁿh₋` increase and `Tⁿh₊`
  decrease, and both converge uniformly on `I_ε` (at rate `Kⁿ`) to the fixed point `g` of
  Proposition 18.3, which is the unique fixed point in `E`. (Convergence is proved with the
  contraction estimate rather than Theorem 17.7.)
* (NOTE 18.2-E, proof of Prop. 18.3.) The printed choice `m̂₂(1 + λ*) < δ` does not give
  `M₂(1 + λ) ≤ δ` since `λ > λ*` (`prop_18_3_printed_step_counterexample`). The fix replaces `λ*`
  by `λ`: `H₂*(1 + λ) < 1` (`LocalHyp.H2s_mul_lt_one`), used in `local_constants`.
* (NOTE 18.2-I, p. 553.) Uniqueness is within `D_λ(I_ε)` for the given `(λ, ε)`
  (`prop_18_3_fixedPoint`). Verified.
* (NOTE 18.2-J, p. 548.) A solution of (4) is taken as the definition of equilibrium; for the
  local solutions here the transversality condition holds because the paths are bounded and
  converge to `k*` (`tvc_of_bounded` in `IndirectApproach`). Verified, recorded.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- `D_λ(I_ε)` (p. 550), as a set of functions `ℝ → ℝ` (only values on `I_ε` matter):
`h(k*) = k*` and `h` is `λ`-Lipschitz on `I_ε`. -/
def Dlam (ks ε lam : ℝ) : Set (ℝ → ℝ) :=
  {h | h ks = ks ∧ ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |h k - h k'| ≤ lam * |k - k'|}

/-- The operator `(Th)(k) = H[k, h(h(k))]` of §18.2 (8). -/
def Top (H : ℝ → ℝ → ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun k => H k (h (h k))

/-- `H` is `(m₁, m₂)`-Lipschitz on `I_ε × I_ε`. -/
def HBound (H : ℝ → ℝ → ℝ) (ks ε m₁ m₂ : ℝ) : Prop :=
  ∀ x ∈ Jint ks ε, ∀ x' ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
    |H x z - H x' z'| ≤ m₁ * |x - x'| + m₂ * |z - z'|

/-- Members of `D_λ(I_ε)` (`λ ≤ 1`) map `I_ε` into itself. -/
theorem Dlam_mapsTo {ks ε lam : ℝ} {h : ℝ → ℝ} (hh : h ∈ Dlam ks ε lam) (hl1 : lam ≤ 1) :
    ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε := by
  intro k hk
  have hε : 0 ≤ ε := by linarith [hk.1, hk.2]
  have h1 := hh.2 k hk ks (center_mem_Jint hε)
  rw [hh.1] at h1
  have h2 := mem_Jint_iff.1 hk
  rw [mem_Jint_iff]
  linarith [mul_le_of_le_one_left (abs_nonneg (k - ks)) hl1]

/-- Membership in `D_λ(I_ε)` depends only on the values on `I_ε`. -/
theorem Dlam_congr {ks ε lam : ℝ} {h h' : ℝ → ℝ} (hε : 0 ≤ ε)
    (he : ∀ k ∈ Jint ks ε, h k = h' k) (hh : h ∈ Dlam ks ε lam) : h' ∈ Dlam ks ε lam :=
  ⟨by rw [← he ks (center_mem_Jint hε)]; exact hh.1, fun k hk k' hk' => by
    rw [← he k hk, ← he k' hk']; exact hh.2 k hk k' hk'⟩

/-! ### Basic estimates for `T` -/

/-- **Lipschitz bound for `Th`** (proof of Proposition 18.2). If `h` maps `I_ε` into itself and
is `λ`-Lipschitz there, `λ ≥ 0`, and `H` is `(m₁, m₂)`-Lipschitz, then `Th` is
`(m₁ + m₂λ²)`-Lipschitz on `I_ε`. -/
theorem Top_lipschitz {H : ℝ → ℝ → ℝ} {ks ε lam m₁ m₂ : ℝ} (hB : HBound H ks ε m₁ m₂)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) {h : ℝ → ℝ} (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε)
    (hL : ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |h k - h k'| ≤ lam * |k - k'|) :
    ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε,
      |Top H h k - Top H h k'| ≤ (m₁ + m₂ * lam ^ 2) * |k - k'| := by
  intro k hk k' hk'
  have h1 := hB k hk k' hk' _ (hmaps _ (hmaps k hk)) _ (hmaps _ (hmaps k' hk'))
  have h4 : |h (h k) - h (h k')| ≤ lam ^ 2 * |k - k'| :=
    calc |h (h k) - h (h k')| ≤ lam * |h k - h k'| := hL _ (hmaps k hk) _ (hmaps k' hk')
      _ ≤ lam * (lam * |k - k'|) := mul_le_mul_of_nonneg_left (hL k hk k' hk') hl0
      _ = lam ^ 2 * |k - k'| := by ring
  calc |Top H h k - Top H h k'| ≤ m₁ * |k - k'| + m₂ * |h (h k) - h (h k')| := h1
    _ ≤ m₁ * |k - k'| + m₂ * (lam ^ 2 * |k - k'|) := by
        linarith [mul_le_mul_of_nonneg_left h4 hm₂]
    _ = (m₁ + m₂ * lam ^ 2) * |k - k'| := by ring

/-- **`T(D_λ(I_ε)) ⊆ D_λ(I_ε)`** under `m₁ + m₂λ² ≤ λ` (proof of Proposition 18.2). -/
theorem Top_mem_Dlam {H : ℝ → ℝ → ℝ} {ks ε lam m₁ m₂ : ℝ} (hB : HBound H ks ε m₁ m₂)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hsum : m₁ + m₂ * lam ^ 2 ≤ lam)
    (hc : H ks ks = ks) {h : ℝ → ℝ} (hh : h ∈ Dlam ks ε lam) : Top H h ∈ Dlam ks ε lam := by
  refine ⟨by simp only [Top, hh.1, hc], fun k hk k' hk' => ?_⟩
  exact (Top_lipschitz hB hm₂ hl0 (Dlam_mapsTo hh hl1) hh.2 k hk k' hk').trans
    (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))

/-- **The contraction estimate** (proof of Proposition 18.3, Exercise 18.3). If `h, ĥ` map
`I_ε` into itself, `ĥ` is `λ`-Lipschitz there (`λ ≥ 0`), `|h − ĥ| ≤ D` on `I_ε`, and
`|H(x, z) − H(x, z′)| ≤ m₂|z − z′|`, then
`|h(h(k)) − ĥ(ĥ(k))| ≤ (1 + λ) D` and `|(Th)(k) − (Tĥ)(k)| ≤ m₂(1 + λ) D` on `I_ε`. -/
theorem Top_sub_le {H : ℝ → ℝ → ℝ} {ks ε lam m₂ D : ℝ}
    (hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε, |H x z - H x z'| ≤ m₂ * |z - z'|)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) {h hh : ℝ → ℝ} (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε)
    (hmaps' : ∀ k ∈ Jint ks ε, hh k ∈ Jint ks ε)
    (hL : ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |hh k - hh k'| ≤ lam * |k - k'|)
    (hD : ∀ k ∈ Jint ks ε, |h k - hh k| ≤ D) :
    ∀ k ∈ Jint ks ε, |h (h k) - hh (hh k)| ≤ (1 + lam) * D ∧
      |Top H h k - Top H hh k| ≤ m₂ * (1 + lam) * D := by
  intro k hk
  have h2 : |h (h k) - hh (hh k)| ≤ (1 + lam) * D :=
    calc |h (h k) - hh (hh k)| = |(h (h k) - hh (h k)) + (hh (h k) - hh (hh k))| := by ring_nf
      _ ≤ |h (h k) - hh (h k)| + |hh (h k) - hh (hh k)| := abs_add_le _ _
      _ ≤ D + lam * |h k - hh k| := add_le_add (hD _ (hmaps k hk))
          (hL _ (hmaps k hk) _ (hmaps' k hk))
      _ ≤ D + lam * D := by linarith [mul_le_mul_of_nonneg_left (hD k hk) hl0]
      _ = (1 + lam) * D := by ring
  refine ⟨h2, ?_⟩
  calc |Top H h k - Top H hh k| ≤ m₂ * |h (h k) - hh (hh k)| :=
        hHz k hk _ (hmaps _ (hmaps k hk)) _ (hmaps' _ (hmaps' k hk))
    _ ≤ m₂ * ((1 + lam) * D) := mul_le_mul_of_nonneg_left h2 hm₂
    _ = m₂ * (1 + lam) * D := by ring

/-- `T` is strictly increasing on `I_ε` at nondecreasing `h` mapping `I_ε` into itself
(proof of Proposition 18.4; it uses that `F` is strictly decreasing in its first and third
arguments and strictly increasing in its second, through the monotonicity of `H`). -/
theorem Top_strictMonoOn {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε : ℝ} (hεε₀ : ε ≤ ε₀) {h : ℝ → ℝ}
    (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) (hmono : MonotoneOn h (Jint ks ε)) :
    StrictMonoOn (Top H h) (Jint ks ε) := by
  intro k hk k' hk' hkk
  have hz := hmaps _ (hmaps k hk)
  have hz' := hmaps _ (hmaps k' hk')
  have hle : h (h k) ≤ h (h k') :=
    hmono (hmaps k hk) (hmaps k' hk') (hmono hk hk' hkk.le)
  have h1 : H k (h (h k)) < H k' (h (h k)) :=
    hH.strictMono_left k (Jint_mono hεε₀ hk) k' (Jint_mono hεε₀ hk') _ (Jint_mono hεε₀ hz) hkk
  have h2 : H k' (h (h k)) ≤ H k' (h (h k')) := by
    rcases eq_or_lt_of_le hle with he | hlt
    · rw [he]
    · exact (hH.strictMono_right k' (Jint_mono hεε₀ hk') _ (Jint_mono hεε₀ hz) _
        (Jint_mono hεε₀ hz') hlt).le
  exact h1.trans_le h2

/-! ### The constants of Propositions 18.2–18.3 -/

/-- **Choice of constants.** For `λ ∈ (λ*, 1)` there are `m₁, m₂ ≥ 0` and `ε ∈ (0, ε₀]` with
`m₁ + m₂λ² ≤ λ`, `m₂(1 + λ) < 1`, `m₁ + m₂ ≤ 1` and `H` `(m₁, m₂)`-Lipschitz on
`I_ε × I_ε`. (The condition `m₂(1 + λ) < 1` uses the corrected step of NOTE 18.2-E;
`m₁ + m₂ ≤ 1` is the extra condition of NOTE 18.2-H.) -/
theorem local_constants {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ m₁ m₂ ε, 0 < ε ∧ ε ≤ ε₀ ∧ 0 ≤ m₁ ∧ 0 ≤ m₂ ∧ m₁ + m₂ * lam ^ 2 ≤ lam ∧
      m₂ * (1 + lam) < 1 ∧ m₁ + m₂ ≤ 1 ∧ HBound H ks ε m₁ m₂ := by
  set H1 := -F1s β θ U f ks / F2s β θ U f ks with hH1
  set H2 := -F3s U θ f ks / F2s β θ U f ks with hH2
  have hH1p : 0 < H1 := L.H1s_pos
  have hH2p : 0 < H2 := L.H2s_pos
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  have g1 : 0 < lam - H1 - H2 * lam ^ 2 := by
    have := L.H_lt_lam hl hl1.le
    linarith
  have g2 : 0 < 1 - H2 * (1 + lam) := by
    have := L.H2s_mul_lt_one hl1.le
    linarith
  have g3 : 0 < 1 - H1 - H2 := by
    have := L.H_sum_lt_one
    linarith
  have hp1 : 0 < 1 + lam ^ 2 := by positivity
  have hp2 : 0 < 2 * (1 + lam) := by linarith
  set s := min ((lam - H1 - H2 * lam ^ 2) / (1 + lam ^ 2))
    (min ((1 - H2 * (1 + lam)) / (2 * (1 + lam))) ((1 - H1 - H2) / 2)) with hs
  have hsp : 0 < s := lt_min (div_pos g1 hp1) (lt_min (div_pos g2 hp2) (by linarith))
  have hs1 : s * (1 + lam ^ 2) ≤ lam - H1 - H2 * lam ^ 2 :=
    (le_div_iff₀ hp1).1 (min_le_left _ _)
  have hs2 : s * (2 * (1 + lam)) ≤ 1 - H2 * (1 + lam) :=
    (le_div_iff₀ hp2).1 ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : s ≤ (1 - H1 - H2) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ε, hε, hεε₀, hB⟩ := hH.lip_near (H1 + s) (H2 + s) (by linarith) (by linarith)
  refine ⟨H1 + s, H2 + s, ε, hε, hεε₀, by linarith, by linarith, by nlinarith, by nlinarith,
    by linarith, hB⟩

/-! ### Proposition 18.2 -/

/-- **Proposition 18.2** (p. 550). Under `LocalHyp` (Assumption 18.1 with `U″(c*) < 0`,
`f″(k*) < 0`) and with `H` the local solution of (7) on `I = I_{ε₀}`: for every
`λ ∈ (λ*, 1)` there is `ε > 0` with `I_ε ⊆ I` and `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`. -/
theorem prop_18_2 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, -, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  exact ⟨ε, hε, hεε₀, fun h hh => Top_mem_Dlam hB hm₂ hlpos.le hl1.le hsum hH.center hh⟩

/-! ### Exercise 18.3 -/

/-- **Exercise 18.3** (p. 551). `T` is continuous on `D_λ(I_ε)` in the sup norm: for any
`ε ≤ ε₀` and `λ ∈ [0, 1]` there is `C ≥ 0` with `‖Th − Tĥ‖ ≤ C ‖h − ĥ‖` (sup over `I_ε`);
`C = B₂(1 + λ)` where `B₂` is a Lipschitz constant of `H` in its second argument. (In particular
for the `ε` of Proposition 18.2.) -/
theorem ex_18_3 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ Dlam ks ε lam, ∀ hh ∈ Dlam ks ε lam, ∀ D : ℝ,
      (∀ k ∈ Jint ks ε, |h k - hh k| ≤ D) →
        ∀ k ∈ Jint ks ε, |Top H h k - Top H hh k| ≤ C * D := by
  obtain ⟨B₁, B₂, -, hB₂, hB⟩ := hH.lipschitz
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ B₂ * |z - z'| := fun x _ z _ z' _ => by
    simpa using hB x x z z'
  refine ⟨B₂ * (1 + lam), mul_nonneg hB₂ (by linarith), fun h hh hh' hh2 D hD k hk => ?_⟩
  exact (Top_sub_le hHz hB₂ hl0 (Dlam_mapsTo hh hl1) (Dlam_mapsTo hh2 hl1) hh2.2 hD k hk).2

/-- The functions of the counterexample to the manual's step in Exercise 18.3. -/
noncomputable def manualH (lam k : ℝ) : ℝ := -lam * k

/-- `h_c(k) = −λk + c·max(k, 0)`. -/
noncomputable def manualHc (lam c k : ℝ) : ℝ := -lam * k + c * max k 0

/-- **The manual's inequality in Exercise 18.3 is false** (NOTE 18.2-F). Let `0 < λ < 1`,
`0 < c ≤ 2λ` (e.g. `c = 2λ/n`), `k* = 0`, `ε = 1`. Then `h(k) = −λk` and
`h_c(k) = −λk + c·max(k, 0)` both lie in `D_λ([−1, 1])`, `‖h_c − h‖ ≤ c`, but at `k = −1`
`|h_c²(−1) − h²(−1)| ≤ λ|h_c(−1) − h(−1)|` fails (the left side is `cλ`, the right side `0`). -/
theorem ex_18_3_manual_counterexample {lam c : ℝ} (hl0 : 0 < lam) (hc0 : 0 < c)
    (hc : c ≤ 2 * lam) :
    manualH lam ∈ Dlam 0 1 lam ∧ manualHc lam c ∈ Dlam 0 1 lam ∧
      (∀ k ∈ Jint 0 1, |manualHc lam c k - manualH lam k| ≤ c) ∧
      ¬ (|manualHc lam c (manualHc lam c (-1)) - manualH lam (manualH lam (-1))| ≤
        lam * |manualHc lam c (-1) - manualH lam (-1)|) := by
  refine ⟨⟨by simp [manualH], fun k _ k' _ => ?_⟩, ⟨by simp [manualHc], fun k _ k' _ => ?_⟩,
    fun k hk => ?_, ?_⟩
  · simp only [manualH]
    rw [show -lam * k - -lam * k' = -lam * (k - k') by ring, abs_mul, abs_neg,
      abs_of_pos hl0]
  · simp only [manualHc]
    rw [abs_le]
    rcases le_total k' k with hkk | hkk
    · rw [abs_of_nonneg (by linarith : 0 ≤ k - k')]
      rcases le_total k 0 with hk0 | hk0 <;> rcases le_total k' 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
    · rw [abs_of_nonpos (by linarith : k - k' ≤ 0)]
      rcases le_total k 0 with hk0 | hk0 <;> rcases le_total k' 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
  · simp only [manualHc, manualH]
    have hk1 : k ≤ 1 := by have := hk.2; linarith
    rcases le_total k 0 with hk0 | hk0
    · rw [max_eq_right hk0]
      simp [hc0.le]
    · rw [max_eq_left hk0]
      rw [show -lam * k + c * k - -lam * k = c * k by ring, abs_of_nonneg (by positivity)]
      nlinarith
  · simp only [manualHc, manualH]
    have e1 : max (-1 : ℝ) 0 = 0 := by norm_num
    have e2 : max (-lam * -1 + c * 0) 0 = lam := by
      rw [show -lam * -1 + c * 0 = lam by ring, max_eq_left hl0.le]
    rw [e1, e2]
    rw [show -lam * (-lam * -1 + c * 0) + c * lam - -lam * (-lam * -1) = c * lam by ring,
      show -lam * -1 + c * 0 - -lam * -1 = 0 by ring, abs_zero, mul_zero,
      abs_of_pos (mul_pos hc0 hl0)]
    intro h
    linarith [mul_pos hc0 hl0]

/-! ### Exercise 18.4 (a) -/

/-- The first function of the counterexample to Exercise 18.4(a): `h(k) = k* − (λ/2)(k − k*)`. -/
noncomputable def ex184H (ks lam k : ℝ) : ℝ := ks - lam / 2 * (k - ks)

/-- The second function: slope `−λ/2` left of `k*`, `−λ` right of `k*`. -/
noncomputable def ex184H' (ks lam k : ℝ) : ℝ := ks - lam / 2 * (k - ks) - lam / 2 * max (k - ks) 0

/-- **Exercise 18.4(a) is false as stated** (NOTE 18.2-G). For every `λ ∈ (0, 1]` and every
`ε ∈ (0, ε₀]`, the functions `h = ex184H` and `h′ = ex184H'` lie in `D_λ(I_ε)` with `h′ ≤ h` on
`I_ε`, but `(Th)(k* + ε) < (Th′)(k* + ε)`: `h²(k* + ε) = k* + λ²ε/4 < k* + λ²ε/2 = h′²(k* + ε)`
and `H` is strictly increasing in its second argument. So `T` is not monotone on
`D_λ(I_ε)`. -/
theorem ex_18_4a_counterexample {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    ex184H ks lam ∈ Dlam ks ε lam ∧ ex184H' ks lam ∈ Dlam ks ε lam ∧
      (∀ k ∈ Jint ks ε, ex184H' ks lam k ≤ ex184H ks lam k) ∧
      Top H (ex184H ks lam) (ks + ε) < Top H (ex184H' ks lam) (ks + ε) := by
  refine ⟨⟨by simp [ex184H], fun k _ k' _ => ?_⟩, ⟨by simp [ex184H'], fun k _ k' _ => ?_⟩,
    fun k _ => ?_, ?_⟩
  · simp only [ex184H]
    rw [show ks - lam / 2 * (k - ks) - (ks - lam / 2 * (k' - ks)) = -(lam / 2) * (k - k') by
      ring, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < lam / 2)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  · simp only [ex184H']
    rw [abs_le]
    rcases le_total k' k with hkk | hkk
    · rw [abs_of_nonneg (by linarith : 0 ≤ k - k')]
      rcases le_total (k - ks) 0 with hk0 | hk0 <;>
        rcases le_total (k' - ks) 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
    · rw [abs_of_nonpos (by linarith : k - k' ≤ 0)]
      rcases le_total (k - ks) 0 with hk0 | hk0 <;>
        rcases le_total (k' - ks) 0 with hk0' | hk0' <;>
        simp only [max_eq_left, max_eq_right, hk0, hk0'] <;>
        constructor <;> nlinarith
  · simp only [ex184H, ex184H']
    have := le_max_right (k - ks) 0
    nlinarith
  · simp only [Top, ex184H, ex184H']
    have e1 : ks - lam / 2 * (ks + ε - ks) = ks - lam * ε / 2 := by ring
    have e2 : ks - lam / 2 * (ks - lam * ε / 2 - ks) = ks + lam ^ 2 * ε / 4 := by ring
    have e3 : max (ks + ε - ks) 0 = ε := by rw [show ks + ε - ks = ε by ring, max_eq_left hε.le]
    have e4 : ks - lam / 2 * (ks + ε - ks) - lam / 2 * ε = ks - lam * ε := by ring
    have e5 : max (ks - lam * ε - ks) 0 = 0 := by
      rw [max_eq_right]
      nlinarith
    have e6 : ks - lam / 2 * (ks - lam * ε - ks) - lam / 2 * 0 = ks + lam ^ 2 * ε / 2 := by ring
    rw [e3, e4, e1, e2, e5, e6]
    have hl2 : lam ^ 2 ≤ 1 := by nlinarith
    have hmem : ∀ t, 0 ≤ t → t ≤ 1 → ks + t * ε ∈ Jint ks ε₀ := fun t ht0 ht1 =>
      ⟨by nlinarith, by nlinarith⟩
    have m1 : ks + ε ∈ Jint ks ε₀ := by simpa using hmem 1 zero_le_one le_rfl
    have m2 : ks + lam ^ 2 * ε / 4 ∈ Jint ks ε₀ := by
      have := hmem (lam ^ 2 / 4) (by positivity) (by linarith)
      rwa [show lam ^ 2 / 4 * ε = lam ^ 2 * ε / 4 by ring] at this
    have m3 : ks + lam ^ 2 * ε / 2 ∈ Jint ks ε₀ := by
      have := hmem (lam ^ 2 / 2) (by positivity) (by linarith)
      rwa [show lam ^ 2 / 2 * ε = lam ^ 2 * ε / 2 by ring] at this
    exact hH.strictMono_right _ m1 _ m2 _ m3 (by nlinarith [mul_pos (pow_pos hl0 2) hε])

/-- **Exercise 18.4(a), corrected** (the manual's version). On nondecreasing members of
`D_λ(I_ε)` (`ε ≤ ε₀`, `λ ≤ 1`) `T` is monotone: `h ≤ ĥ` on `I_ε` implies `Th ≤ Tĥ` on `I_ε`. -/
theorem ex_18_4a {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε : ℝ} (hεε₀ : ε ≤ ε₀) {h hh : ℝ → ℝ}
    (hmaps : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) (hmaps' : ∀ k ∈ Jint ks ε, hh k ∈ Jint ks ε)
    (hmono : MonotoneOn h (Jint ks ε)) (hle : ∀ k ∈ Jint ks ε, h k ≤ hh k) :
    ∀ k ∈ Jint ks ε, Top H h k ≤ Top H hh k := by
  intro k hk
  have h1 : h (h k) ≤ hh (hh k) :=
    (hmono (hmaps k hk) (hmaps' k hk) (hle k hk)).trans (hle _ (hmaps' k hk))
  rcases eq_or_lt_of_le h1 with he | hlt
  · simp only [Top, he, le_refl]
  · exact (hH.strictMono_right k (Jint_mono hεε₀ hk) _ (Jint_mono hεε₀ (hmaps _ (hmaps k hk)))
      _ (Jint_mono hεε₀ (hmaps' _ (hmaps' k hk))) hlt).le

/-- **Exercise 18.4(a), second part** (manual). `T` maps nondecreasing functions mapping `I_ε`
into itself to (strictly) increasing functions on `I_ε`; with Proposition 18.2, `T` maps the
nondecreasing members of `D_λ(I_ε)` into themselves. -/
theorem ex_18_4a_mapsTo {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hεε₀ : ε ≤ ε₀) (hl1 : lam ≤ 1)
    (hT : ∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) {h : ℝ → ℝ}
    (hh : h ∈ Dlam ks ε lam) (hmono : MonotoneOn h (Jint ks ε)) :
    Top H h ∈ Dlam ks ε lam ∧ MonotoneOn (Top H h) (Jint ks ε) :=
  ⟨hT h hh, (Top_strictMonoOn hH hεε₀ (Dlam_mapsTo hh hl1) hmono).monotoneOn⟩

/-- **Exercise 18.4(b), the constants are not in `D_λ(I_ε)`** (NOTE 18.2-H): for `ε > 0`,
`h₋ ≡ k* − ε` and `h₊ ≡ k* + ε` violate `h(k*) = k*`. -/
theorem ex_18_4b_const_not_mem {ks ε lam : ℝ} (hε : 0 < ε) :
    (fun _ => ks - ε) ∉ Dlam ks ε lam ∧ (fun _ => ks + ε) ∉ Dlam ks ε lam :=
  ⟨fun h => by have := h.1; simp only at this; linarith,
    fun h => by have := h.1; simp only at this; linarith⟩

/-! ### Proposition 18.3 -/

/-- **The printed step of Proposition 18.3 is invalid** (NOTE 18.2-E): `m(1 + λ*) < δ < 1` with
`λ* < λ < 1` does not give `m(1 + λ) ≤ δ`; e.g. `λ* = 1/4`, `λ = 3/4`, `m = 1/2`, `δ = 3/4`. -/
theorem prop_18_3_printed_step_counterexample :
    ∃ ls l m δ : ℝ, 0 < ls ∧ ls < l ∧ l < 1 ∧ 0 < m ∧ m * (1 + ls) < δ ∧ δ < 1 ∧
      δ < m * (1 + l) :=
  ⟨1 / 4, 3 / 4, 1 / 2, 3 / 4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- **Proposition 18.3** (p. 552), estimate form. Under `LocalHyp` with `H` the local solution:
for every `λ ∈ (λ*, 1)` there is `ε ∈ (0, ε₀]` such that `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` and, for some
`K ∈ [0, 1)`, `‖Th − Tĥ‖ ≤ K ‖h − ĥ‖` (sup over `I_ε`) for `h, ĥ ∈ D_λ(I_ε)`; `K = m₂(1 + λ)`
(the corrected constant, NOTE 18.2-E). -/
theorem prop_18_3 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ (∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) ∧
      ∃ K, 0 ≤ K ∧ K < 1 ∧ ∀ h ∈ Dlam ks ε lam, ∀ hh ∈ Dlam ks ε lam, ∀ D : ℝ,
        (∀ k ∈ Jint ks ε, |h k - hh k| ≤ D) →
          ∀ k ∈ Jint ks ε, |Top H h k - Top H hh k| ≤ K * D := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  refine ⟨ε, hε, hεε₀, fun h hh => Top_mem_Dlam hB hm₂ hlpos.le hl1.le hsum hH.center hh,
    m₂ * (1 + lam), mul_nonneg hm₂ (by linarith), hK, fun h hh hh' hh2 D hD k hk => ?_⟩
  exact (Top_sub_le hHz hm₂ hlpos.le (Dlam_mapsTo hh hl1.le) (Dlam_mapsTo hh2 hl1.le) hh2.2
    hD k hk).2

/-! ### Packaging on `C(I_ε)` -/

/-- Extension of `h ∈ C(I_ε)` to `ℝ` (constant beyond the endpoints). -/
noncomputable def extendC {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) : ℝ → ℝ :=
  Set.IccExtend (by linarith : ks - ε ≤ ks + ε) h

/-- `extendC h = h` on `I_ε`. -/
theorem extendC_of_mem {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) {x : ℝ}
    (hx : x ∈ Jint ks ε) : extendC hε h x = h ⟨x, hx⟩ :=
  Set.IccExtend_of_mem _ _ hx

/-- `extendC h` is continuous. -/
theorem continuous_extendC {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) :
    Continuous (extendC hε h) :=
  h.continuous.Icc_extend'

/-- The operator `T` on `C(I_ε)`: `(Th)(k) = H[k, h(h(k))]`, with `h` extended to `ℝ`. -/
noncomputable def TC (H : ℝ → ℝ → ℝ) (hHc : Continuous fun q : ℝ × ℝ => H q.1 q.2)
    {ks ε : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) : C(Jint ks ε, ℝ) where
  toFun k := H (k : ℝ) (extendC hε h (extendC hε h k))
  continuous_toFun := hHc.comp (continuous_subtype_val.prodMk
    ((continuous_extendC hε h).comp ((continuous_extendC hε h).comp continuous_subtype_val)))

/-- On `I_ε`, `TC h` is `T` applied to the extension of `h`. -/
theorem extendC_TC (H : ℝ → ℝ → ℝ) (hHc : Continuous fun q : ℝ × ℝ => H q.1 q.2) {ks ε : ℝ}
    (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) {k : ℝ} (hk : k ∈ Jint ks ε) :
    extendC hε (TC H hHc hε h) k = Top H (extendC hε h) k := by
  rw [extendC_of_mem hε _ hk]
  rfl

/-- `D_λ(I_ε)` as a subset of `C(I_ε)`. -/
def DC (ks ε lam : ℝ) (hε : 0 < ε) : Set C(Jint ks ε, ℝ) :=
  {h | h ⟨ks, center_mem_Jint hε.le⟩ = ks ∧
    ∀ k k' : Jint ks ε, |h k - h k'| ≤ lam * |(k : ℝ) - k'|}

/-- `h ∈ DC ↔ extendC h ∈ D_λ(I_ε)`. -/
theorem mem_DC_iff {ks ε lam : ℝ} (hε : 0 < ε) (h : C(Jint ks ε, ℝ)) :
    h ∈ DC ks ε lam hε ↔ extendC hε h ∈ Dlam ks ε lam := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [extendC_of_mem hε h (center_mem_Jint hε.le)]; exact h1,
      fun k hk k' hk' => ?_⟩
    rw [extendC_of_mem hε h hk, extendC_of_mem hε h hk']
    exact h2 ⟨k, hk⟩ ⟨k', hk'⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← extendC_of_mem hε h (center_mem_Jint hε.le)]; exact h1,
      fun k k' => ?_⟩
    have := h2 k k.2 k' k'.2
    rwa [extendC_of_mem hε h k.2, extendC_of_mem hε h k'.2] at this

/-- `DC` is closed in `C(I_ε)`, hence complete. -/
theorem isClosed_DC (ks ε lam : ℝ) (hε : 0 < ε) : IsClosed (DC ks ε lam hε) := by
  simp only [DC, ofPred_and, ofPred_forall]
  refine IsClosed.inter (isClosed_eq (continuous_eval_const _) continuous_const)
    (isClosed_iInter fun k => isClosed_iInter fun k' => ?_)
  exact isClosed_le ((continuous_eval_const k).sub (continuous_eval_const k')).abs
    continuous_const

/-- The constant `k*` lies in `DC` (for `λ ≥ 0`). -/
theorem const_mem_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) :
    ContinuousMap.const (Jint ks ε) ks ∈ DC ks ε lam hε :=
  ⟨rfl, fun _ _ => by simp only [ContinuousMap.const_apply, sub_self, abs_zero]; positivity⟩

/-- `TC` maps `DC` into itself (Proposition 18.2). -/
theorem TC_mapsTo {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hsum : m₁ + m₂ * lam ^ 2 ≤ lam)
    (hB : HBound H ks ε m₁ m₂) :
    MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε) := by
  intro h hh
  rw [mem_DC_iff] at hh ⊢
  exact Dlam_congr hε.le (fun k hk => (extendC_TC H hH.continuous hε h hk).symm)
    (Top_mem_Dlam hB hm₂ hl0 hl1 hsum hH.center hh)

/-- The contraction estimate on `C(I_ε)`: `dist (Th) (Tĥ) ≤ m₂(1 + λ) dist h ĥ`. -/
theorem TC_dist_le {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hB : HBound H ks ε m₁ m₂) {h hh : C(Jint ks ε, ℝ)}
    (h1 : h ∈ DC ks ε lam hε) (h2 : hh ∈ DC ks ε lam hε) :
    dist (TC H hH.continuous hε h) (TC H hH.continuous hε hh) ≤
      m₂ * (1 + lam) * dist h hh := by
  rw [mem_DC_iff] at h1 h2
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  have hD : ∀ k ∈ Jint ks ε, |extendC hε h k - extendC hε hh k| ≤ dist h hh := by
    intro k hk
    rw [extendC_of_mem hε h hk, extendC_of_mem hε hh hk, ← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist _
  refine (ContinuousMap.dist_le (mul_nonneg (mul_nonneg hm₂ (by linarith)) dist_nonneg)).2
    fun k => ?_
  rw [Real.dist_eq]
  exact (Top_sub_le hHz hm₂ hl0 (Dlam_mapsTo h1 hl1) (Dlam_mapsTo h2 hl1) h2.2 hD k k.2).2

/-- **`T` is a contraction of `DC`** (`ContractingWith`), given `m₂(1 + λ) < 1`. -/
theorem TC_contractingWith {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hK : m₂ * (1 + lam) < 1) (hB : HBound H ks ε m₁ m₂)
    (hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε)) :
    ContractingWith (Real.toNNReal (m₂ * (1 + lam))) (hmaps.restrict _ _ _) := by
  have hK0 : 0 ≤ m₂ * (1 + lam) := mul_nonneg hm₂ (by linarith)
  refine ⟨Real.toNNReal_lt_one.2 hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.coe_toNNReal _ hK0, Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply,
    MapsTo.val_restrict_apply]
  exact TC_dist_le hH hε hl0 hl1 hm₂ hB x.2 y.2

/-- **Exercise 18.3, packaged**: the restriction of `T` to `DC` is continuous. -/
theorem ex_18_3_continuous {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hB : HBound H ks ε m₁ m₂)
    (hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε)) :
    Continuous (hmaps.restrict _ _ _) := by
  have hK0 : 0 ≤ m₂ * (1 + lam) := mul_nonneg hm₂ (by linarith)
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (m₂ * (1 + lam)))
    fun x y => ?_).continuous
  rw [Real.coe_toNNReal _ hK0, Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply,
    MapsTo.val_restrict_apply]
  exact TC_dist_le hH hε hl0 hl1 hm₂ hB x.2 y.2

/-- **Proposition 18.3** (p. 552), `ContractingWith` form: for every `λ ∈ (λ*, 1)` there is
`ε ∈ (0, ε₀]` such that `T` maps `DC = D_λ(I_ε) ⊆ C(I_ε)` into itself and is a contraction
there with modulus `K < 1`. -/
theorem prop_18_3_contractingWith {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ ε₀ ∧
      ∃ hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε),
        ∃ K : NNReal, K < 1 ∧ ContractingWith K (hmaps.restrict _ _ _) := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  have hmaps := TC_mapsTo hH hε hlpos.le hl1.le hm₂ hsum hB
  have hc := TC_contractingWith hH hε hlpos.le hl1.le hm₂ hK hB hmaps
  exact ⟨ε, hε, hεε₀, hmaps, _, hc.1, hc⟩

/-! ### Proposition 18.4 -/

/-- **Proposition 18.4** (p. 553). Let `(λ, I_ε)` (`0 ≤ λ ≤ 1`, `ε ≤ ε₀`) be such that `T` maps
`DC = D_λ(I_ε)` into itself and is a contraction there, and let `g ∈ DC` be its fixed point.
Then `g` is strictly increasing on `I_ε`. (Corollary 1 to Theorem 3.2: `T` maps the closed set
of nondecreasing members into the strictly increasing ones, so the limit of the iterates from
the constant `k*` is nondecreasing, and then `g = Tg` is strictly increasing.) -/
theorem prop_18_4 {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε)) {K : NNReal}
    (hK : ContractingWith K (hmaps.restrict _ _ _)) {g : C(Jint ks ε, ℝ)}
    (hg : g ∈ DC ks ε lam hε) (hfix : TC H hH.continuous hε g = g) :
    StrictMonoOn (extendC hε g) (Jint ks ε) := by
  have : Nonempty (DC ks ε lam hε) := ⟨⟨g, hg⟩⟩
  have : CompleteSpace (DC ks ε lam hε) := (isClosed_DC ks ε lam hε).isComplete.completeSpace_coe
  set T := hmaps.restrict _ _ _ with hT
  -- the closed set of nondecreasing members
  set D' : Set (DC ks ε lam hε) :=
    {h | ∀ p : {q : Jint ks ε × Jint ks ε // q.1 ≤ q.2}, (h : C(Jint ks ε, ℝ)) p.1.1 ≤
      (h : C(Jint ks ε, ℝ)) p.1.2} with hD'
  have hD'c : IsClosed D' := by
    simp only [hD', ofPred_forall]
    exact isClosed_iInter fun p => isClosed_le
      ((continuous_eval_const p.1.1).comp continuous_subtype_val)
      ((continuous_eval_const p.1.2).comp continuous_subtype_val)
  -- `T` maps nondecreasing members to strictly increasing (hence nondecreasing) ones
  have hmonoT : ∀ h : DC ks ε lam hε, h ∈ D' → T h ∈ D' := by
    intro h hh p
    have hmem := (mem_DC_iff hε _).1 h.2
    have hmono : MonotoneOn (extendC hε h.1) (Jint ks ε) := by
      intro x hx y hy hxy
      rw [extendC_of_mem hε _ hx, extendC_of_mem hε _ hy]
      exact hh ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
    have hsm := Top_strictMonoOn hH hεε₀ (Dlam_mapsTo hmem hl1) hmono
    have e1 := extendC_TC H hH.continuous hε (h : C(Jint ks ε, ℝ)) p.1.1.2
    have e2 := extendC_TC H hH.continuous hε (h : C(Jint ks ε, ℝ)) p.1.2.2
    rw [extendC_of_mem hε _ p.1.1.2] at e1
    rw [extendC_of_mem hε _ p.1.2.2] at e2
    rw [hT, MapsTo.val_restrict_apply]
    change TC H hH.continuous hε h p.1.1 ≤ TC H hH.continuous hε h p.1.2
    rw [e1, e2]
    exact hsm.monotoneOn p.1.1.2 p.1.2.2 p.2
  have hc : (⟨ContinuousMap.const (Jint ks ε) ks, const_mem_DC hε hl0⟩ : DC ks ε lam hε) ∈ D' :=
    fun p => le_rfl
  have hiter : ∀ n, T^[n] ⟨ContinuousMap.const (Jint ks ε) ks, const_mem_DC hε hl0⟩ ∈ D' := by
    intro n
    induction n with
    | zero => exact hc
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hmonoT _ ih
  have hgfix : (⟨g, hg⟩ : DC ks ε lam hε) = ContractingWith.fixedPoint T hK :=
    hK.fixedPoint_unique (Subtype.ext (by rw [hT, MapsTo.val_restrict_apply]; exact hfix))
  have hgD' : (⟨g, hg⟩ : DC ks ε lam hε) ∈ D' := by
    rw [hgfix]
    exact hD'c.mem_of_tendsto (hK.tendsto_iterate_fixedPoint _) (Eventually.of_forall hiter)
  have hmono : MonotoneOn (extendC hε g) (Jint ks ε) := by
    intro x hx y hy hxy
    rw [extendC_of_mem hε _ hx, extendC_of_mem hε _ hy]
    exact hgD' ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
  have hmem := (mem_DC_iff hε _).1 hg
  have hsm := Top_strictMonoOn hH hεε₀ (Dlam_mapsTo hmem hl1) hmono
  intro x hx y hy hxy
  have hx' : extendC hε g x = Top H (extendC hε g) x := by
    rw [← extendC_TC H hH.continuous hε g hx, hfix]
  have hy' : extendC hε g y = Top H (extendC hε g) y := by
    rw [← extendC_TC H hH.continuous hε g hy, hfix]
  rw [hx', hy']
  exact hsm hx hy hxy

/-! ### The fixed point -/

/-- **Uniqueness of fixed points** under the contraction estimate. If `h, g` map `I_ε` into
itself, `g` is `λ`-Lipschitz on `I_ε`, `m₂(1 + λ) < 1`, and both are fixed by `T` on `I_ε`, then
`h = g` on `I_ε`. -/
theorem eq_of_fixed {H : ℝ → ℝ → ℝ} {ks ε lam m₁ m₂ : ℝ} (hB : HBound H ks ε m₁ m₂)
    (hm₂ : 0 ≤ m₂) (hl0 : 0 ≤ lam) (hK : m₂ * (1 + lam) < 1) {h g : ℝ → ℝ}
    (hh : ∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) (hg : ∀ k ∈ Jint ks ε, g k ∈ Jint ks ε)
    (hgL : ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |g k - g k'| ≤ lam * |k - k'|)
    (hhf : ∀ k ∈ Jint ks ε, Top H h k = h k) (hgf : ∀ k ∈ Jint ks ε, Top H g k = g k) :
    ∀ k ∈ Jint ks ε, h k = g k := by
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  set K := m₂ * (1 + lam) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hm₂ (by linarith)
  have hbound : ∀ n : ℕ, ∀ k ∈ Jint ks ε, |h k - g k| ≤ K ^ n * (2 * ε) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have h1 := mem_Jint_iff.1 (hh k hk)
      have h2 := mem_Jint_iff.1 (hg k hk)
      rw [pow_zero, one_mul]
      calc |h k - g k| = |(h k - ks) - (g k - ks)| := by ring_nf
        _ ≤ |h k - ks| + |g k - ks| := abs_sub _ _
        _ ≤ 2 * ε := by linarith
    | succ n ih =>
      intro k hk
      have := (Top_sub_le hHz hm₂ hl0 hh hg hgL ih k hk).2
      rw [hhf k hk, hgf k hk] at this
      calc |h k - g k| ≤ K * (K ^ n * (2 * ε)) := this
        _ = K ^ (n + 1) * (2 * ε) := by ring
  intro k hk
  have hlim : Tendsto (fun n : ℕ => K ^ n * (2 * ε)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const (2 * ε)
  have h0 : |h k - g k| ≤ 0 := ge_of_tendsto' hlim fun n => hbound n k hk
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- **Existence of the fixed point** for given constants (Contraction Mapping Theorem on `DC`,
with Proposition 18.4): a `g ∈ D_λ(I_ε)` with `Tg = g` on `I_ε`, strictly increasing on
`I_ε`. -/
theorem exists_fixedPoint_of_bounds {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam m₁ m₂ : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hm₂ : 0 ≤ m₂) (hsum : m₁ + m₂ * lam ^ 2 ≤ lam)
    (hK : m₂ * (1 + lam) < 1) (hB : HBound H ks ε m₁ m₂) :
    ∃ g : ℝ → ℝ, g ∈ Dlam ks ε lam ∧ (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      StrictMonoOn g (Jint ks ε) := by
  have hmaps := TC_mapsTo hH hε hl0 hl1 hm₂ hsum hB
  have hc := TC_contractingWith hH hε hl0 hl1 hm₂ hK hB hmaps
  have : Nonempty (DC ks ε lam hε) :=
    ⟨⟨ContinuousMap.const (Jint ks ε) ks, const_mem_DC hε hl0⟩⟩
  have : CompleteSpace (DC ks ε lam hε) := (isClosed_DC ks ε lam hε).isComplete.completeSpace_coe
  set g0 := ContractingWith.fixedPoint _ hc with hg0
  have hfix : TC H hH.continuous hε g0.1 = g0.1 := by
    have := ContractingWith.fixedPoint_isFixedPt (f := hmaps.restrict _ _ _) hc
    rw [← hg0] at this
    have := congrArg Subtype.val this
    rwa [MapsTo.val_restrict_apply] at this
  refine ⟨extendC hε g0.1, (mem_DC_iff hε _).1 g0.2, fun k hk => ?_,
    prop_18_4 hH hε hεε₀ hl0 hl1 hmaps hc g0.2 hfix⟩
  rw [← extendC_TC H hH.continuous hε g0.1 hk, hfix]

/-- **Consequences of Proposition 18.3** (p. 553). For every `λ ∈ (λ*, 1)` there are
`ε ∈ (0, ε₀]` and `g ∈ D_λ(I_ε)` such that: `g = Tg` on `I_ε`; `g` solves the Euler equation (4)
`F[k, g(k), g²(k)] = 0` on `I_ε`; `g` is the unique fixed point of `T` in `D_λ(I_ε)`; `g` is
strictly increasing on `I_ε` (Proposition 18.4); and `|g^t(k) − k*| ≤ λ^t |k − k*|`, so
`k_t → k*` from every `k₀ ∈ I_ε` (local stability). -/
theorem prop_18_3_fixedPoint {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∃ g : ℝ → ℝ, g ∈ Dlam ks ε lam ∧
      (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      (∀ k ∈ Jint ks ε, Feq β θ U f k (g k) (g (g k)) = 0) ∧
      (∀ g' ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g' k = g' k) →
        ∀ k ∈ Jint ks ε, g' k = g k) ∧
      StrictMonoOn g (Jint ks ε) ∧
      ∀ k ∈ Jint ks ε, ∀ t : ℕ, |g^[t] k - ks| ≤ lam ^ t * |k - ks| := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨g, hg, hfix, hsm⟩ :=
    exists_fixedPoint_of_bounds hH hε hεε₀ hlpos.le hl1.le hm₂ hsum hK hB
  have hgm := Dlam_mapsTo hg hl1.le
  refine ⟨ε, hε, hεε₀, g, hg, hfix, fun k hk => ?_, fun g' hg' hfix' k hk => ?_, hsm,
    fun k hk t => ?_⟩
  · have h7 := hH.eq7 k (Jint_mono hεε₀ hk) _ (Jint_mono hεε₀ (hgm _ (hgm k hk)))
    have e : H k (g (g k)) = g k := hfix k hk
    rwa [e] at h7
  · exact eq_of_fixed hB hm₂ hlpos.le hK (Dlam_mapsTo hg' hl1.le) hgm hg.2 hfix' hfix k hk
  · have hiter : ∀ t : ℕ, g^[t] k ∈ Jint ks ε := by
      intro t
      induction t with
      | zero => exact hk
      | succ t ih => rw [Function.iterate_succ_apply']; exact hgm _ ih
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      have h1 := hg.2 _ (hiter t) ks (center_mem_Jint hε.le)
      rw [hg.1] at h1
      calc |g (g^[t] k) - ks| ≤ lam * |g^[t] k - ks| := h1
        _ ≤ lam * (lam ^ t * |k - ks|) := mul_le_mul_of_nonneg_left ih hlpos.le
        _ = lam ^ (t + 1) * |k - ks| := by ring

/-! ### Exercise 18.4 (b), repaired -/

/-- The set `E` of NOTE 18.2-H: nondecreasing, `λ`-Lipschitz maps of `I_ε` into itself. -/
def Elam (ks ε lam : ℝ) : Set (ℝ → ℝ) :=
  {h | (∀ k ∈ Jint ks ε, h k ∈ Jint ks ε) ∧ MonotoneOn h (Jint ks ε) ∧
    ∀ k ∈ Jint ks ε, ∀ k' ∈ Jint ks ε, |h k - h k'| ≤ lam * |k - k'|}

/-- **Exercise 18.4(b), repaired** (NOTE 18.2-H). For every `λ ∈ (λ*, 1)` there are
`ε ∈ (0, ε₀]` and `g` (the fixed point of Proposition 18.3, in `D_λ(I_ε) ∩ E`) such that, with
`h₋ ≡ k* − ε`, `h₊ ≡ k* + ε`:
(i) `T(E) ⊆ E` and `T` is monotone on `E`; (ii) `h₋, h₊ ∈ E`, `h₋ ≤ Th₋`, `Th₊ ≤ h₊` on `I_ε`;
(iii) `Tⁿh₋` is nondecreasing and `Tⁿh₊` nonincreasing in `n`; (iv) for some `K ∈ [0, 1)`,
`|Tⁿh₋ − g| ≤ Kⁿ·2ε` and `|Tⁿh₊ − g| ≤ Kⁿ·2ε` on `I_ε`, so both limits exist (uniformly) and
equal `g`, a fixed point of `T`; (v) `g` is the unique fixed point of `T` in `E`. -/
theorem ex_18_4b {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∃ g : ℝ → ℝ, ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧
      (∀ h ∈ Elam ks ε lam, Top H h ∈ Elam ks ε lam) ∧
      (∀ h ∈ Elam ks ε lam, ∀ hh ∈ Elam ks ε lam, (∀ k ∈ Jint ks ε, h k ≤ hh k) →
        ∀ k ∈ Jint ks ε, Top H h k ≤ Top H hh k) ∧
      (fun _ => ks - ε) ∈ Elam ks ε lam ∧ (fun _ => ks + ε) ∈ Elam ks ε lam ∧
      (∀ k ∈ Jint ks ε, ks - ε ≤ Top H (fun _ => ks - ε) k) ∧
      (∀ k ∈ Jint ks ε, Top H (fun _ => ks + ε) k ≤ ks + ε) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, (Top H)^[n] (fun _ => ks - ε) k ≤
        (Top H)^[n + 1] (fun _ => ks - ε) k) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, (Top H)^[n + 1] (fun _ => ks + ε) k ≤
        (Top H)^[n] (fun _ => ks + ε) k) ∧
      g ∈ Dlam ks ε lam ∧ g ∈ Elam ks ε lam ∧ (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, |(Top H)^[n] (fun _ => ks - ε) k - g k| ≤ K ^ n * (2 * ε)) ∧
      (∀ n : ℕ, ∀ k ∈ Jint ks ε, |(Top H)^[n] (fun _ => ks + ε) k - g k| ≤ K ^ n * (2 * ε)) ∧
      (∀ k ∈ Jint ks ε, Tendsto (fun n => (Top H)^[n] (fun _ => ks - ε) k) atTop (𝓝 (g k))) ∧
      (∀ k ∈ Jint ks ε, Tendsto (fun n => (Top H)^[n] (fun _ => ks + ε) k) atTop (𝓝 (g k))) ∧
      ∀ h ∈ Elam ks ε lam, (∀ k ∈ Jint ks ε, Top H h k = h k) → ∀ k ∈ Jint ks ε, h k = g k := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, hm₁, hm₂, hsum, hK, hm12, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨g, hg, hfix, hsm⟩ :=
    exists_fixedPoint_of_bounds hH hε hεε₀ hlpos.le hl1.le hm₂ hsum hK hB
  have hHz : ∀ x ∈ Jint ks ε, ∀ z ∈ Jint ks ε, ∀ z' ∈ Jint ks ε,
      |H x z - H x z'| ≤ m₂ * |z - z'| := fun x hx z hz z' hz' => by
    simpa using hB x hx x hx z hz z' hz'
  set K := m₂ * (1 + lam) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hm₂ (by linarith)
  have hks := center_mem_Jint (p := ks) hε.le
  -- (i) `T(E) ⊆ E`
  have hTE : ∀ h ∈ Elam ks ε lam, Top H h ∈ Elam ks ε lam := by
    rintro h ⟨hmaps, hmono, hL⟩
    refine ⟨fun k hk => ?_, (Top_strictMonoOn hH hεε₀ hmaps hmono).monotoneOn,
      fun k hk k' hk' => (Top_lipschitz hB hm₂ hlpos.le hmaps hL k hk k' hk').trans
        (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))⟩
    have h1 := hB k hk ks hks _ (hmaps _ (hmaps k hk)) ks hks
    rw [hH.center] at h1
    have h2 := mem_Jint_iff.1 hk
    have h3 := mem_Jint_iff.1 (hmaps _ (hmaps k hk))
    rw [mem_Jint_iff]
    have h4 := mul_le_mul_of_nonneg_left h2 hm₁
    have h5 := mul_le_mul_of_nonneg_left h3 hm₂
    have h6 := mul_le_mul_of_nonneg_right hm12 hε.le
    change |H k (h (h k)) - ks| ≤ ε
    linarith
  have hTmono : ∀ h ∈ Elam ks ε lam, ∀ hh ∈ Elam ks ε lam, (∀ k ∈ Jint ks ε, h k ≤ hh k) →
      ∀ k ∈ Jint ks ε, Top H h k ≤ Top H hh k := fun h hh hh' hh2 hle =>
    ex_18_4a hH hεε₀ hh.1 hh2.1 hh.2.1 hle
  have hconst : ∀ c ∈ Jint ks ε, (fun _ => c) ∈ Elam ks ε lam := fun c hc =>
    ⟨fun _ _ => hc, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ => by
      simp only [sub_self, abs_zero]; positivity⟩
  have hlo : ks - ε ∈ Jint ks ε := ⟨le_rfl, by linarith⟩
  have hhi : ks + ε ∈ Jint ks ε := ⟨by linarith, le_rfl⟩
  have hEm : ∀ n : ℕ, ∀ c ∈ Jint ks ε, (Top H)^[n] (fun _ => c) ∈ Elam ks ε lam := by
    intro n c hc
    induction n with
    | zero => exact hconst c hc
    | succ n ih => rw [Function.iterate_succ_apply']; exact hTE _ ih
  have hgE : g ∈ Elam ks ε lam := ⟨Dlam_mapsTo hg hl1.le, hsm.monotoneOn, hg.2⟩
  -- convergence bound
  have hconv : ∀ h ∈ Elam ks ε lam, ∀ n : ℕ, ∀ k ∈ Jint ks ε,
      |(Top H)^[n] h k - g k| ≤ K ^ n * (2 * ε) := by
    intro h hh n
    induction n with
    | zero =>
      intro k hk
      have h1 := mem_Jint_iff.1 (hh.1 k hk)
      have h2 := mem_Jint_iff.1 (hgE.1 k hk)
      rw [pow_zero, one_mul, Function.iterate_zero_apply]
      calc |h k - g k| = |(h k - ks) - (g k - ks)| := by ring_nf
        _ ≤ |h k - ks| + |g k - ks| := abs_sub _ _
        _ ≤ 2 * ε := by linarith
    | succ n ih =>
      intro k hk
      have hmem : (Top H)^[n] h ∈ Elam ks ε lam := by
        clear ih
        induction n with
        | zero => exact hh
        | succ n ih' => rw [Function.iterate_succ_apply']; exact hTE _ ih'
      have := (Top_sub_le hHz hm₂ hlpos.le hmem.1 hgE.1 hg.2 ih k hk).2
      rw [hfix k hk] at this
      rw [Function.iterate_succ_apply']
      calc |Top H ((Top H)^[n] h) k - g k| ≤ K * (K ^ n * (2 * ε)) := this
        _ = K ^ (n + 1) * (2 * ε) := by ring
  have hlim : Tendsto (fun n : ℕ => K ^ n * (2 * ε)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const (2 * ε)
  have htend : ∀ h ∈ Elam ks ε lam, ∀ k ∈ Jint ks ε,
      Tendsto (fun n => (Top H)^[n] h k) atTop (𝓝 (g k)) := by
    intro h hh k hk
    have h1 : Tendsto (fun n => (Top H)^[n] h k - g k) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hconv h hh n k hk) hlim
    simpa using h1.add_const (g k)
  refine ⟨ε, hε, hεε₀, g, K, hK0, hK, hTE, hTmono, hconst _ hlo, hconst _ hhi,
    fun k hk => ((hTE _ (hconst _ hlo)).1 k hk).1, fun k hk => ((hTE _ (hconst _ hhi)).1 k hk).2,
    ?_, ?_, hg, hgE, hfix, hconv _ (hconst _ hlo), hconv _ (hconst _ hhi),
    htend _ (hconst _ hlo), htend _ (hconst _ hhi), fun h hh hhf k hk =>
      eq_of_fixed hB hm₂ hlpos.le hK hh.1 hgE.1 hg.2 hhf hfix k hk⟩
  · intro n
    induction n with
    | zero => exact fun k hk => ((hTE _ (hconst _ hlo)).1 k hk).1
    | succ n ih =>
      intro k hk
      have e1 : (Top H)^[n + 1] (fun _ => ks - ε) = Top H ((Top H)^[n] (fun _ => ks - ε)) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : (Top H)^[n + 1 + 1] (fun _ => ks - ε) =
          Top H ((Top H)^[n + 1] (fun _ => ks - ε)) := Function.iterate_succ_apply' _ _ _
      rw [e2, e1]
      rw [e1] at ih
      exact hTmono _ (hEm n _ hlo) _ (hTE _ (hEm n _ hlo)) ih k hk
  · intro n
    induction n with
    | zero => exact fun k hk => ((hTE _ (hconst _ hhi)).1 k hk).2
    | succ n ih =>
      intro k hk
      have e1 : (Top H)^[n + 1] (fun _ => ks + ε) = Top H ((Top H)^[n] (fun _ => ks + ε)) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : (Top H)^[n + 1 + 1] (fun _ => ks + ε) =
          Top H ((Top H)^[n + 1] (fun _ => ks + ε)) := Function.iterate_succ_apply' _ _ _
      rw [e2, e1]
      rw [e1] at ih
      exact hTmono _ (hTE _ (hEm n _ hhi)) _ (hEm n _ hhi) ih k hk

end StokeyLucasPrescott.EquilibriaWithDistortions
