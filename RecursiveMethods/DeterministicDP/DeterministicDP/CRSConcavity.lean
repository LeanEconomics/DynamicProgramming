/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.ConstantReturnsDP
import DeterministicDP.QuasiConcavity
import DeterministicDP.ValueDifferentiability

/-!
# Quasi-concavity of the value function with constant returns

SLP Exercise 4.8c, p. 92: "Under what conditions is the fixed point `v` of `T` strictly
quasi-concave?" The answer proved here follows the hint (the proof of Theorem 4.8 and
Exercise 4.8a–b).

* `NonProp`: `x` and `x′` are not nonnegative multiples of one another.
* `crs_concave`: if `F` is concave on the (convex, Assumption 4.8) graph of `Γ`, strictly so
  across pairs with `NonProp` states, then `T` maps concave functions in `H(X)` to concave
  functions that are strictly concave across `NonProp` pairs.
* `ex_4_8c`: under these conditions the fixed point `v` is concave, and if `v(x) ≠ 0` for
  `x ≠ 0` it is strictly quasi-concave.
* `ex_4_8d` ("Under what conditions is `v` differentiable?"): in `ℝˡ`, at an interior `x₀` with a
  maximizer `y₀` interior to `Γ(x₀)` and `x ↦ F(x, y₀)` differentiable at `x₀`, `v` is
  differentiable at `x₀` with `Dv(x₀) = D_xF(x₀, y₀)` (the argument of Theorem 4.11).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E} {hX : IsCone X}
  {hC : Convex ℝ X} {Γ : X → Set X} {F : X × X → ℝ} {β α B : ℝ}

/-- Neither of `x`, `x′` is a nonnegative multiple of the other. -/
def NonProp (x x' : X) : Prop := (∀ a : ℝ, 0 ≤ a → x.1 ≠ a • x'.1) ∧ ∀ a : ℝ, 0 ≤ a → x'.1 ≠ a • x.1

/-- `F` is concave on the graph of `Γ`, strictly across pairs whose states are `NonProp`. -/
def ConcaveGraph (hC : Convex ℝ X) (Γ : X → Set X) (F : X × X → ℝ) : Prop :=
  ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y') ∧
    (NonProp x x' →
      θ * F (x, y) + (1 - θ) * F (x', y') < F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y'))

/-- `T` maps concave functions in `H(X)` to concave functions, strictly concave across
`NonProp` pairs. -/
theorem crs_concave (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    (h48 : Assumption48 hC Γ) (hF : ConcaveGraph hC Γ F) {f : X → ℝ} (hfc : Continuous f)
    (hf : IsConcaveS hC f) :
    IsConcaveS hC (crs Γ F β f) ∧ ∀ x x', NonProp x x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
      θ * crs Γ F β f x + (1 - θ) * crs Γ F β f x' < crs Γ F β f (cmb hC h0.le h1.le x x') := by
  -- the inequality at interior `θ`, strict for `NonProp` pairs
  have key : ∀ x x' (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
      θ * crs Γ F β f x + (1 - θ) * crs Γ F β f x' ≤ crs Γ F β f (cmb hC h0.le h1.le x x') ∧
      (NonProp x x' → θ * crs Γ F β f x + (1 - θ) * crs Γ F β f x' <
        crs Γ F β f (cmb hC h0.le h1.le x x')) := by
    intro x x' θ h0 h1
    obtain ⟨y, hy, hv, -⟩ := exists_crs_argmax h410 h411 hfc x
    obtain ⟨y', hy', hv', -⟩ := exists_crs_argmax h410 h411 hfc x'
    obtain ⟨-, -, -, hmax⟩ := exists_crs_argmax h410 h411 hfc (cmb hC h0.le h1.le x x')
    have hyθ := h48 x y x' y' hy hy' θ h0.le h1.le
    have hfy := mul_le_mul_of_nonneg_left (hf y y' θ h0.le h1.le) h411.β_pos.le
    have hm := hmax _ hyθ
    obtain ⟨hFw, hFs⟩ := hF x y x' y' hy hy' θ h0 h1
    rw [hv, hv']
    exact ⟨by nlinarith, fun hnp => by nlinarith [hFs hnp]⟩
  refine ⟨fun x x' θ h0 h1 => ?_, fun x x' hnp θ h0 h1 => (key x x' θ h0 h1).2 hnp⟩
  rcases h0.eq_or_lt with rfl | h0'
  · simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  rcases h1.eq_or_lt with rfl | h1'
  · simp only [one_mul, sub_self, zero_mul, add_zero]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  exact (key x x' θ h0' h1').1

/-- **Exercise 4.8c.** Under Assumptions 4.10–4.11 and 4.8, if `F` is concave on the graph of `Γ`
and strictly concave across `NonProp` pairs, then the fixed point `v ∈ H(X)` of `T` is concave;
if moreover `v(x) ≠ 0` for `x ≠ 0`, it is strictly quasi-concave. -/
theorem ex_4_8c (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    (h48 : Assumption48 hC Γ) (hF : ConcaveGraph hC Γ F) {v : X → ℝ} (hvH : InH hX v)
    (hv : crs Γ F β v = v) :
    IsConcaveS hC v ∧ ((∀ x : X, x.1 ≠ 0 → v x ≠ 0) → IsStrictQuasiConcaveS hC v) := by
  set T := crs Γ F β
  -- the iterates from `0` are concave and in `H(X)`
  have h0 : InH hX (0 : X → ℝ) := ⟨continuous_const, fun _ _ _ => by simp, 0, fun _ => by simp⟩
  have hiter : ∀ n, InH hX (T^[n] 0) ∧ IsConcaveS hC (T^[n] 0) := by
    intro n
    induction n with
    | zero => exact ⟨h0, fun _ _ _ _ _ => by simp⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ex_4_7b h410 h411 ih.1, (crs_concave h410 h411 h48 hF ih.1.1 ih.2).1⟩
  -- they converge pointwise to `v`
  obtain ⟨v', hv'H, hv', huniq, hrate, -, -⟩ := theorem_4_13 h410 h411
  have hvv' : v = v' := huniq v hvH hv
  have hpt : ∀ x, Tendsto (fun n => T^[n] 0 x) atTop (𝓝 (v x)) := fun x => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hαβ : 0 ≤ α * β := mul_nonneg h410.α_pos.le h411.β_pos.le
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hαβ h410.αβ_lt).mul_const
        (hnorm X (0 - v'))).mul_const ‖x.1‖)
    have h1 := abs_le_hnorm (inH_sub (hiter n).1 hvH) x
    have h2 := hrate 0 h0 n
    rw [zero_sub] at h2
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h1 ⊢
    rw [hvv'] at h1 ⊢
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  -- concavity passes to the limit
  have hvc : IsConcaveS hC v := fun x x' θ h0 h1 => le_of_tendsto_of_tendsto
    (((hpt x).const_mul θ).add ((hpt x').const_mul (1 - θ))) (hpt _)
    (Eventually.of_forall fun n => (hiter n).2 x x' θ h0 h1)
  refine ⟨hvc, fun hne x x' hxx' hle θ h0 h1 => ?_⟩
  have hstrict := (crs_concave h410 h411 h48 hF hvH.1 hvc).2
  have hv2 : crs Γ F β v = v := hv
  rw [hv2] at hstrict
  by_cases hnp : NonProp x x'
  · have := hstrict x x' hnp θ h0 h1
    nlinarith
  -- `x` and `x′` lie on a common ray: use homogeneity
  simp only [NonProp, not_and_or, not_forall, not_not] at hnp
  rcases hnp with ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩
  · -- `x = a x′`
    have hx'0 : x'.1 ≠ 0 := fun h => hxx' (Subtype.ext (by rw [hxa, h, smul_zero]))
    have ha1 : a ≠ 1 := fun h => hxx' (Subtype.ext (by rw [hxa, h, one_smul]))
    have hvx : v x = a * v x' := by
      have : x = csmul hX ha x' := Subtype.ext hxa
      rw [this, hvH.2.1]
    have hc : cmb hC h0.le h1.le x x' = csmul hX (by nlinarith : (0 : ℝ) ≤ θ * a + (1 - θ)) x' :=
      Subtype.ext (by simp only [cmb, csmul, hxa, smul_smul, add_smul])
    rw [hc, hvH.2.1]
    have hv' := hne x' hx'0
    rw [hvx] at hle
    have : (a - 1) * v x' ≠ 0 := mul_ne_zero (sub_ne_zero.2 ha1) hv'
    have hpos : 0 < (a - 1) * v x' := lt_of_le_of_ne (by nlinarith) (Ne.symm this)
    nlinarith
  · -- `x′ = a x`
    have hx0 : x.1 ≠ 0 := fun h => hxx' (Subtype.ext (by rw [hxa, h, smul_zero]))
    have ha1 : a ≠ 1 := fun h => hxx' (Subtype.ext (by rw [hxa, h, one_smul]))
    have hvx : v x' = a * v x := by
      have : x' = csmul hX ha x := Subtype.ext hxa
      rw [this, hvH.2.1]
    have hc : cmb hC h0.le h1.le x x' = csmul hX (by nlinarith : (0 : ℝ) ≤ θ + (1 - θ) * a) x :=
      Subtype.ext (by simp only [cmb, csmul, hxa, smul_smul, add_smul])
    rw [hc, hvH.2.1, hvx]
    have hv := hne x hx0
    rw [hvx] at hle
    have : (1 - a) * v x ≠ 0 := mul_ne_zero (sub_ne_zero.2 (Ne.symm ha1)) hv
    have hpos : 0 < (1 - a) * v x := lt_of_le_of_ne (by nlinarith) (Ne.symm this)
    nlinarith

/-- **Exercise 4.8d.** In `ℝˡ`, under the hypotheses of Exercise 4.8c, let `x₀ ∈ int X` and let
`y₀ ∈ G(x₀)` be interior to `Γ(x₀)`. If `x ↦ F(x, y₀)` has derivative `DF` at `x₀`, then `v` is
differentiable at `x₀` with derivative `DF`. -/
theorem ex_4_8d {l : ℕ} {X : Set (Fin l → ℝ)} {hX : IsCone X} {hC : Convex ℝ X}
    {Γ : X → Set X} {F : X × X → ℝ} (h410 : Assumption410 hX Γ β α)
    (h411 : Assumption411 hX Γ F β B) (h48 : Assumption48 hC Γ) (hF : ConcaveGraph hC Γ F)
    {v : X → ℝ} (hvH : InH hX v) (hv : crs Γ F β v = v) {x₀ y₀ : X}
    (hy₀ : y₀ ∈ argmax (obj F β v) Γ x₀) (hint : X ∈ 𝓝 x₀.1)
    (hg : y₀.1 ∈ interior (Subtype.val '' Γ x₀)) {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hFd : HasFDerivAt (liftS fun x => F (x, y₀)) DF x₀.1) :
    HasFDerivAt (liftS v) DF x₀.1 := by
  have hvc := (ex_4_8c h410 h411 h48 hF hvH hv).1
  have h43 : Assumption43 Γ := ⟨h410.nonempty, h410.compact, h410.lhc, h410.uhc⟩
  have hvx : ∀ x, v x = maxValue (obj F β v) Γ x := fun x => (congrFun hv x).symm
  set W : (Fin l → ℝ) → ℝ := fun x => liftS (fun x => F (x, y₀)) x + β * v y₀
  have heq : W x₀.1 = liftS v x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx x₀]
    exact hy₀.2
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS v x := by
    have h1 := eventually_mem_Γ (hS := hC) h43 h48 (x₀ := x₀) (g₀ := y₀) hg
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx ⟨x, hxS⟩]
    exact le_maxValue (continuousOn_obj' h411 hvH.1) (h410.compact _) (hx ⟨x, hxS⟩ rfl)
  exact theorem_4_10 (concaveOn_liftS hvc) hint (hFd.add_const _) heq hle

end StokeyLucasPrescott.DeterministicDP
