/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.Inventory

/-!
# Production and inventory accumulation: Exercise 10.5c

SLP §10.5, Exercise 10.5c, p. 299. Let `v` be the fixed point of the truncated operator of
`UpperBounded` for the inventory problem with `n ≤ N̄`, and `R = Ū/(1 − β)`.

* `inv_indep`: `v(x, ω)` does not depend on the current shock `ω` (Exercise 10.5b: the shocks
  are i.i.d., and `ω` enters neither the return nor the constraint).
* `inv_solves_2`: `v` solves the book's (2), where `n` ranges over all of `[0, ∞)`: inputs
  above `N̄` cost more than `R` and are never chosen.
* **Exercise 10.5c** (`ex_10_5c`): `v` is the unique bounded continuous solution, with
  `0 ≤ v ≤ R`; `v` is strictly increasing and strictly concave; the maximizing `(Y, N)` is unique
  and continuous in `x`; and `v′(x) = U′(x − Y(x))` where `U` is differentiable at
  `x − Y(x) > 0`. The book states the derivative without the proviso `Y(x) < x`; at `Y(x) = x`
  the envelope argument gives only a one-sided bound.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {U H c : ℝ → ℝ} {β Ubar Nbar ω₁ ω₂ : ℝ} {μ : Measure (Icc ω₁ ω₂)}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The right side of (2) at any `(y, n)`. -/
theorem inv_rhs (f : Ici (0 : ℝ) × Icc ω₁ ω₂ → ℝ) (s : Ici (0 : ℝ) × Icc ω₁ ω₂) (p : ℝ × ℝ) :
    rhs (invModel μ U H c β Nbar) f s p =
      U (s.1.1 - p.1) - H p.1 - c p.2 + β * ∫ ω', f (invφ (s.1, p, ω'), ω') ∂μ := rfl

omit [IsProbabilityMeasure μ] in
theorem integrable_inv [IsFiniteMeasure μ] (f : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ)
    (x : Ici (0 : ℝ)) (p : ℝ × ℝ) : Integrable (fun ω' => f (invφ (x, p, ω'), ω')) μ :=
  integrable_of_abs_le (f.continuous.comp ((continuous_invφ.comp (continuous_const.prodMk
    (continuous_const.prodMk continuous_id))).prodMk continuous_id)).measurable fun _ => by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _

theorem cmb_Ici_val {x x' : Ici (0 : ℝ)} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (cmb (convex_Ici (0 : ℝ)) h0 h1 x x').1 = θ * x.1 + (1 - θ) * x'.1 := by
  simp [cmb]

/-- The fixed point satisfies `0 ≤ v ≤ R`. -/
theorem inv_bounds (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) : ∀ s, 0 ≤ v s ∧ v s ≤ Ubar / (1 - β) := by
  have hd := h.upperDP μ
  have hb := truncModel_boundedDP hd (truncK_pos hd).le
  exact (corollary_1 (S' := {f | ∀ s, 0 ≤ f s ∧ f s ≤ Ubar / (1 - β)})
    (S'' := {f | ∀ s, 0 ≤ f s ∧ f s ≤ Ubar / (1 - β)}) (bellman_contraction _ hb) hv
    ⟨0, fun _ => ⟨le_rfl, div_nonneg h.Ubar_nonneg (by linarith [h.β_lt])⟩⟩
    (isClosed_bounds _) (truncT_mapsTo hd) (truncT_mapsTo hd)).1

/-- At the fixed point the maximum in (2) over `Γ` is attained and equals `v`. -/
theorem inv_max (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (s : Ici (0 : ℝ) × Icc ω₁ ω₂) :
    (∃ p ∈ invΓ Nbar s, v s = rhs (invModel μ U H c β Nbar) v s p) ∧
      ∀ p ∈ invΓ Nbar s, rhs (invModel μ U H c β Nbar) v s p ≤ v s := by
  obtain ⟨p, hp, hval, hmax⟩ := trunc_bellman_argmax (h.upperDP μ) (inv_bounds h hv) s
  rw [hv] at hval hmax
  exact ⟨⟨p, hp, hval⟩, hmax⟩

/-- **Exercise 10.5b.** The value does not depend on the current shock: `v(x, ω) = v(x, ω′)`. -/
theorem inv_indep (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (x : Ici (0 : ℝ)) (ω ω' : Icc ω₁ ω₂) :
    v (x, ω) = v (x, ω') := by
  have key : ∀ ω ω' : Icc ω₁ ω₂, v (x, ω) ≤ v (x, ω') := fun ω ω' => by
    obtain ⟨p, hp, hval⟩ := (inv_max h hv (x, ω)).1
    rw [hval]
    exact (inv_max h hv (x, ω')).2 p hp
  exact le_antisymm (key ω ω') (key ω' ω)

/-- `v` is strictly increasing in `x`: the plan optimal at `x` is feasible at `x′ > x` and gives
more consumption. -/
theorem inv_strictMono (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (ω : Icc ω₁ ω₂) : StrictMono fun x => v (x, ω) := by
  intro x x' hxx
  have hxx' : x.1 < x'.1 := hxx
  obtain ⟨p, hp, hval⟩ := (inv_max h hv (x, ω)).1
  have hp' : p ∈ invΓ Nbar (x', ω) := ⟨⟨hp.1.1, hp.1.2.trans hxx'.le⟩, hp.2⟩
  have hle := (inv_max h hv (x', ω)).2 p hp'
  dsimp only
  rw [hval]
  refine lt_of_lt_of_le ?_ hle
  rw [inv_rhs, inv_rhs]
  have hp1 : p.1 ≤ x.1 := hp.1.2
  have := h.U_mono (mem_Ici.2 (sub_nonneg.2 hp1)) (mem_Ici.2 (by linarith))
    (by linarith : x.1 - p.1 < x'.1 - p.1)
  have hE : ∫ ω', v (invφ (x', p, ω'), ω') ∂μ = ∫ ω', v (invφ (x, p, ω'), ω') ∂μ := rfl
  dsimp only at this ⊢
  rw [hE]
  linarith

/-- The return is concave in `(x, y, n)`, strictly when consumption, inventories or inputs
differ. -/
theorem inv_F_cmb (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {a₀ a₁ y₀ y₁ n₀ n₁ θ : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₁ : 0 ≤ a₁) (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁) (hn₀ : 0 ≤ n₀) (hn₁ : 0 ≤ n₁) (h0 : 0 < θ)
    (h1 : θ < 1) (hne : a₀ ≠ a₁ ∨ y₀ ≠ y₁ ∨ n₀ ≠ n₁) :
    θ * (U a₀ - H y₀ - c n₀) + (1 - θ) * (U a₁ - H y₁ - c n₁) <
      U (θ * a₀ + (1 - θ) * a₁) - H (θ * y₀ + (1 - θ) * y₁) - c (θ * n₀ + (1 - θ) * n₁) := by
  have h1' : 0 < 1 - θ := by linarith
  have hab : θ + (1 - θ) = 1 := by ring
  have hUw : θ * U a₀ + (1 - θ) * U a₁ ≤ U (θ * a₀ + (1 - θ) * a₁) := by
    simpa only [smul_eq_mul] using h.U_conc.concaveOn.2 (mem_Ici.2 ha₀) (mem_Ici.2 ha₁) h0.le
      h1'.le hab
  have hHw : H (θ * y₀ + (1 - θ) * y₁) ≤ θ * H y₀ + (1 - θ) * H y₁ := by
    simpa only [smul_eq_mul] using h.H_conv.convexOn.2 (mem_Ici.2 hy₀) (mem_Ici.2 hy₁) h0.le
      h1'.le hab
  have hcw : c (θ * n₀ + (1 - θ) * n₁) ≤ θ * c n₀ + (1 - θ) * c n₁ := by
    simpa only [smul_eq_mul] using h.c_conv.convexOn.2 (mem_Ici.2 hn₀) (mem_Ici.2 hn₁) h0.le
      h1'.le hab
  rcases hne with hne | hne | hne
  · have := h.U_conc.2 (mem_Ici.2 ha₀) (mem_Ici.2 ha₁) hne h0 h1' hab
    simp only [smul_eq_mul] at this
    linarith
  · have := h.H_conv.2 (mem_Ici.2 hy₀) (mem_Ici.2 hy₁) hne h0 h1' hab
    simp only [smul_eq_mul] at this
    linarith
  · have := h.c_conv.2 (mem_Ici.2 hn₀) (mem_Ici.2 hn₁) hne h0 h1' hab
    simp only [smul_eq_mul] at this
    linarith

/-- The continuation value is concave in `(y, n)` when `f(·, ω′)` is concave. -/
theorem inv_E_cmb (hω : 0 ≤ ω₁) {f : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hf : ∀ z, IsConcaveS (convex_Ici (0 : ℝ)) fun x => f (x, z)) (x₀ x₁ xθ : Ici (0 : ℝ))
    {p₀ p₁ : ℝ × ℝ} (hy₀ : 0 ≤ p₀.1) (hn₀ : 0 ≤ p₀.2) (hy₁ : 0 ≤ p₁.1) (hn₁ : 0 ≤ p₁.2) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * ∫ ω', f (invφ (x₀, p₀, ω'), ω') ∂μ + (1 - θ) * ∫ ω', f (invφ (x₁, p₁, ω'), ω') ∂μ ≤
      ∫ ω', f (invφ (xθ, (θ * p₀.1 + (1 - θ) * p₁.1, θ * p₀.2 + (1 - θ) * p₁.2), ω'), ω') ∂μ := by
  have i0 := integrable_inv (μ := μ) f x₀ p₀
  have i1 := integrable_inv (μ := μ) f x₁ p₁
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
    (i1.const_mul _)]
  refine integral_mono ((i0.const_mul θ).add (i1.const_mul _)) (integrable_inv f xθ _)
    fun ω' => ?_
  have h1' : 0 ≤ 1 - θ := by linarith
  have heq : invφ (xθ, (θ * p₀.1 + (1 - θ) * p₁.1, θ * p₀.2 + (1 - θ) * p₁.2), ω') =
      cmb (convex_Ici (0 : ℝ)) h0 h1 (invφ (x₀, p₀, ω')) (invφ (x₁, p₁, ω')) := by
    apply Subtype.ext
    rw [cmb_Ici_val, invφ_val _ _ _ hω hy₀ hn₀, invφ_val _ _ _ hω hy₁ hn₁,
      invφ_val _ _ _ hω (by dsimp only; positivity) (by dsimp only; positivity)]
    ring
  dsimp only
  rw [heq]
  exact hf ω' _ _ θ h0 h1

/-- **Exercise 10.5c** (strict concavity). `v(·, ω)` is strictly concave. -/
theorem inv_strictConcave (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ} (hv : truncT (h.upperDP μ) v = v) (ω : Icc ω₁ ω₂) :
    IsStrictConcaveS (convex_Ici (0 : ℝ)) fun x => v (x, ω) := by
  have hd := h.upperDP μ
  have hb := truncModel_boundedDP hd (truncK_pos hd).le
  set S' : Set (Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ) :=
    {f | ∀ s, 0 ≤ f s ∧ f s ≤ Ubar / (1 - β)} ∩
      {f | ∀ z, IsConcaveS (convex_Ici (0 : ℝ)) fun x => f (x, z)}
  have hclosed : IsClosed S' := (isClosed_bounds _).inter (isClosed_concaveX _)
  have hstrict : ∀ f ∈ S', ∀ z, IsStrictConcaveS (convex_Ici (0 : ℝ))
      fun x => truncT hd f (x, z) := by
    intro f hf z x₀ x₁ hne θ h0 h1
    obtain ⟨p₀, hp₀, hv₀, -⟩ := trunc_bellman_argmax hd hf.1 (x₀, z)
    obtain ⟨p₁, hp₁, hv₁, -⟩ := trunc_bellman_argmax hd hf.1 (x₁, z)
    set xθ := cmb (convex_Ici (0 : ℝ)) h0.le h1.le x₀ x₁
    have hxθ : xθ.1 = θ * x₀.1 + (1 - θ) * x₁.1 := cmb_Ici_val h0.le h1.le
    have h1' : 0 < 1 - θ := by linarith
    have hy₀ : p₀.1 ≤ x₀.1 := hp₀.1.2
    have hy₁ : p₁.1 ≤ x₁.1 := hp₁.1.2
    have hpθ : (θ * p₀.1 + (1 - θ) * p₁.1, θ * p₀.2 + (1 - θ) * p₁.2) ∈ invΓ Nbar (xθ, z) := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · dsimp only; nlinarith [hp₀.1.1, hp₁.1.1]
      · dsimp only; rw [hxθ]; nlinarith
      · dsimp only; nlinarith [hp₀.2.1, hp₁.2.1]
      · dsimp only; nlinarith [hp₀.2.2, hp₁.2.2]
    obtain ⟨-, -, -, hmax⟩ := trunc_bellman_argmax hd hf.1 (xθ, z)
    have hle := hmax _ hpθ
    dsimp only
    rw [hv₀, hv₁]
    refine lt_of_lt_of_le ?_ hle
    rw [inv_rhs, inv_rhs, inv_rhs]
    have hne' : x₀.1 - p₀.1 ≠ x₁.1 - p₁.1 ∨ p₀.1 ≠ p₁.1 ∨ p₀.2 ≠ p₁.2 := by
      by_cases ha : x₀.1 - p₀.1 = x₁.1 - p₁.1
      · by_cases hy : p₀.1 = p₁.1
        · exact absurd (Subtype.ext (by linarith) : x₀ = x₁) hne
        · exact Or.inr (Or.inl hy)
      · exact Or.inl ha
    have hF := inv_F_cmb h (sub_nonneg.2 hy₀) (sub_nonneg.2 hy₁) hp₀.1.1 hp₁.1.1 hp₀.2.1
      hp₁.2.1 h0 h1 hne'
    have hE := inv_E_cmb (μ := μ) h.ω_nonneg hf.2 x₀ x₁ xθ hp₀.1.1 hp₀.2.1 hp₁.1.1 hp₁.2.1 h0.le
      h1.le
    have harg : xθ.1 - (θ * p₀.1 + (1 - θ) * p₁.1) =
        θ * (x₀.1 - p₀.1) + (1 - θ) * (x₁.1 - p₁.1) := by rw [hxθ]; ring
    dsimp only
    rw [harg]
    nlinarith [mul_le_mul_of_nonneg_left hE h.β_pos.le]
  have hmaps : MapsTo (truncT hd) S' S' := fun f hf =>
    ⟨truncT_mapsTo hd hf.1, fun z => (hstrict f hf z).isConcaveS⟩
  have hv' := (corollary_1 (S' := S') (S'' := S') (bellman_contraction _ hb) hv
    ⟨0, fun _ => ⟨le_rfl, div_nonneg h.Ubar_nonneg (by linarith [h.β_lt])⟩,
      fun _ _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1
  have := hstrict v hv' ω
  rwa [hv] at this

/-- The objective of (2) is continuous on the graph of `Γ`. -/
theorem inv_continuousOn_objG (h : InvHyp U H c β Ubar Nbar ω₁ ω₂)
    (f : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ) :
    ContinuousOn (objG (invModel μ U H c β Nbar) f) (graph (invΓ Nbar)) := by
  have hd := h.upperDP μ
  set MM := invModel μ U H c β Nbar
  have hF : ContinuousOn (fun p : (Ici (0 : ℝ) × Icc ω₁ ω₂) × (ℝ × ℝ) =>
      MM.F (p.1.1, p.2, p.1.2)) (graph MM.Γ) :=
    (h.continuousOn_F μ).comp (continuous_fst.fst.prodMk
      (continuous_snd.prodMk continuous_fst.snd)).continuousOn fun p hp => hp
  have hE : ContinuousOn (fun p : (Ici (0 : ℝ) × Icc ω₁ ω₂) × (ℝ × ℝ) =>
      ∫ z', f (MM.φ (p.1.1, p.2, z'), z') ∂MM.Q p.1.2) (graph MM.Γ) :=
    (hd.contExp f f.continuous ⟨‖f‖, fun p => f.norm_coe_le_norm p⟩).comp
      ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd).continuousOn
      fun p hp => ⟨mem_domD MM hp, mem_univ _⟩
  exact hF.add (continuousOn_const.mul hE)

/-- At the fixed point, `max_{Γ(s)}` of the objective is `v(s)`. -/
theorem inv_maxValue (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (s : Ici (0 : ℝ) × Icc ω₁ ω₂) :
    maxValue (objG (invModel μ U H c β Nbar) v) (invΓ Nbar) s = v s := by
  obtain ⟨⟨p, hp, hval⟩, hmax⟩ := inv_max h hv s
  exact IsGreatest.csSup_eq ⟨⟨p, hp, hval.symm⟩, by rintro _ ⟨p', hp', rfl⟩; exact hmax p' hp'⟩

/-- **Exercise 10.5c** (the policy functions). The maximizing `(y, n)` is unique, and the policy
correspondence is the `argmax`; hence `(Y, N)` is a continuous function of the state. -/
theorem inv_policy (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) :
    UniqueArgmax (invΓ Nbar) (objG (invModel μ U H c β Nbar) v) ∧
      ∀ s, policy (invModel μ U H c β Nbar) v s =
        argmax (objG (invModel μ U H c β Nbar) v) (invΓ Nbar) s := by
  have hd := h.upperDP μ
  have hpol : ∀ s, policy (invModel μ U H c β Nbar) v s =
      argmax (objG (invModel μ U H c β Nbar) v) (invΓ Nbar) s := fun s => by
    ext p
    change p ∈ invΓ Nbar s ∧ v s = rhs _ v s p ↔ p ∈ invΓ Nbar s ∧ objG _ v (s, p) = _
    rw [inv_maxValue h hv s, eq_comm]
    rfl
  refine ⟨⟨hd.nonempty, hd.compact, hd.lhc, hd.uhc, inv_continuousOn_objG h v,
    fun s p₁ hp₁ p₂ hp₂ => ?_⟩, hpol⟩
  by_contra hne
  obtain ⟨x, z⟩ := s
  have hh0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  have e1 : rhs (invModel μ U H c β Nbar) v (x, z) p₁ = v (x, z) := by
    rw [← inv_maxValue h hv (x, z)]; exact hp₁.2
  have e2 : rhs (invModel μ U H c β Nbar) v (x, z) p₂ = v (x, z) := by
    rw [← inv_maxValue h hv (x, z)]; exact hp₂.2
  have hy₁ : p₁.1 ≤ x.1 := hp₁.1.1.2
  have hy₂ : p₂.1 ≤ x.1 := hp₂.1.1.2
  set pm : ℝ × ℝ := (1 / 2 * p₁.1 + (1 - 1 / 2) * p₂.1, 1 / 2 * p₁.2 + (1 - 1 / 2) * p₂.2)
  have hpm : pm ∈ invΓ Nbar (x, z) := by
    have a1 := hp₁.1; have a2 := hp₂.1
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [pm] <;> linarith [a1.1.1, a2.1.1, a1.2.1, a2.2.1,
      a1.2.2, a2.2.2]
  have hle := (inv_max h hv (x, z)).2 pm hpm
  have hne' : x.1 - p₁.1 ≠ x.1 - p₂.1 ∨ p₁.1 ≠ p₂.1 ∨ p₁.2 ≠ p₂.2 := by
    by_cases hy : p₁.1 = p₂.1
    · by_cases hn : p₁.2 = p₂.2
      · exact absurd (Prod.ext hy hn) hne
      · exact Or.inr (Or.inr hn)
    · exact Or.inr (Or.inl hy)
  have hF := inv_F_cmb h (sub_nonneg.2 hy₁) (sub_nonneg.2 hy₂) hp₁.1.1.1 hp₂.1.1.1 hp₁.1.2.1
    hp₂.1.2.1 hh0 hh1 hne'
  have hE := inv_E_cmb (μ := μ) h.ω_nonneg (fun z => (inv_strictConcave h hv z).isConcaveS) x x x
    hp₁.1.1.1 hp₁.1.2.1 hp₂.1.1.1 hp₂.1.2.1 hh0.le hh1.le
  rw [inv_rhs] at hle e1 e2
  have harg : x.1 - (1 / 2 * p₁.1 + (1 - 1 / 2) * p₂.1) =
      1 / 2 * (x.1 - p₁.1) + (1 - 1 / 2) * (x.1 - p₂.1) := by ring
  dsimp only [pm] at hle e1 e2
  rw [harg] at hle
  nlinarith [mul_le_mul_of_nonneg_left hE h.β_pos.le]

/-- `v` solves the book's (2): the supremum over all `0 ≤ y ≤ x` and `n ≥ 0`, without the
bound `N̄`. An input `n > N̄` costs `c(n) > R`, which exceeds any gain. -/
theorem inv_solves_2 (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) (s : Ici (0 : ℝ) × Icc ω₁ ω₂) :
    IsLUB (rhs (invModel μ U H c β Nbar) v s '' {p | p.1 ∈ Icc 0 s.1.1 ∧ 0 ≤ p.2}) (v s) := by
  obtain ⟨⟨p, hp, hval⟩, hmax⟩ := inv_max h hv s
  refine ⟨?_, fun b hb => hb ⟨p, ⟨hp.1, hp.2.1⟩, hval.symm⟩⟩
  rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
  rcases le_or_gt q.2 Nbar with hqN | hqN
  · exact hmax q ⟨hq1, hq2, hqN⟩
  · have hR := inv_bounds h hv
    have hE : ∫ ω', v (invφ (s.1, q, ω'), ω') ∂μ ≤ Ubar / (1 - β) := by
      have := integral_mono (integrable_inv (μ := μ) v s.1 q) (integrable_const (Ubar / (1 - β)))
        fun ω' => (hR _).2
      simpa using this
    have hcN : c Nbar ≤ c q.2 := h.c_mono.monotoneOn h.N_nonneg hq2 hqN.le
    have hF := h.F_le (p := (s.1, q, s.2)) hq1.2 hq1.1
    have hβ1 : 0 < 1 - β := by linarith [h.β_lt]
    have e : Ubar / (1 - β) = Ubar + β * (Ubar / (1 - β)) := by field_simp; ring
    have h0 := (hR s).1
    rw [inv_rhs]
    change U (s.1.1 - q.1) - H q.1 - c q.2 ≤ Ubar - c q.2 at hF
    nlinarith [mul_le_mul_of_nonneg_left hE h.β_pos.le, h.N_big]

/-- **Exercise 10.5c** (differentiability, Benveniste–Scheinkman). If `(y₀, n₀)` is optimal at
`(x₀, ω₀)` with positive consumption `x₀ − y₀ > 0`, and `U` is differentiable at `x₀ − y₀`,
then `v′(x₀) = U′(x₀ − y₀)`. -/
theorem inv_hasDerivAt (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) {v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ}
    (hv : truncT (h.upperDP μ) v = v) {x₀ : Ici (0 : ℝ)} {ω₀ : Icc ω₁ ω₂} {p : ℝ × ℝ}
    (hp : p ∈ policy (invModel μ U H c β Nbar) v (x₀, ω₀)) (hpos : p.1 < x₀.1) {U' : ℝ}
    (hU' : HasDerivAt U U' (x₀.1 - p.1)) :
    HasDerivAt (liftS fun x => v (x, ω₀)) U' x₀.1 := by
  have hp0 : 0 ≤ p.1 := hp.1.1.1
  set E := ∫ ω', v (invφ (x₀, p, ω'), ω') ∂μ
  have hL : HasDerivAt (fun x => U (x - p.1) - H p.1 - c p.2 + β * E) U' x₀.1 :=
    ((hU'.comp_sub_const x₀.1 p.1).sub_const (H p.1)).sub_const (c p.2) |>.add_const _
  refine hasDerivAt_of_concaveOn_of_le
    (concaveOn_liftS (inv_strictConcave h hv ω₀).isConcaveS) (Ici_mem_nhds (by linarith)) hL ?_ ?_
  · rw [liftS_of_mem _ x₀.2, hp.2, inv_rhs]
  · filter_upwards [Ioi_mem_nhds hpos] with x hx
    have hx0 : x ∈ Ici (0 : ℝ) := mem_Ici.2 (hp0.trans (le_of_lt hx))
    rw [liftS_of_mem _ hx0]
    exact (inv_max h hv (⟨x, hx0⟩, ω₀)).2 p ⟨⟨hp0, le_of_lt hx⟩, hp.1.2⟩

/-- **Exercise 10.5c**, bundled: `v` is the unique bounded continuous solution of (2) with
`n ≤ N̄`, `0 ≤ v ≤ R`, and it solves (2) over all `n ≥ 0`; `v` does not depend on the current
shock and is strictly increasing and strictly concave; `(Y, N)` is unique and continuous; and
`v′(x) = U′(x − Y(x))` where consumption is positive and `U` is differentiable. -/
theorem ex_10_5c (h : InvHyp U H c β Ubar Nbar ω₁ ω₂) :
    ∃ v : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ, truncT (h.upperDP μ) v = v ∧
      (∀ s, 0 ≤ v s ∧ v s ≤ Ubar / (1 - β)) ∧ SolvesFE (invModel μ U H c β Nbar) v ∧
      (∀ w : Ici (0 : ℝ) × Icc ω₁ ω₂ →ᵇ ℝ, SolvesFE (invModel μ U H c β Nbar) w → w = v) ∧
      (∀ s, IsLUB (rhs (invModel μ U H c β Nbar) v s '' {p | p.1 ∈ Icc 0 s.1.1 ∧ 0 ≤ p.2})
        (v s)) ∧
      (∀ x ω ω', v (x, ω) = v (x, ω')) ∧
      (∀ ω, StrictMono fun x => v (x, ω)) ∧
      (∀ ω, IsStrictConcaveS (convex_Ici (0 : ℝ)) fun x => v (x, ω)) ∧
      UniqueArgmax (invΓ Nbar) (objG (invModel μ U H c β Nbar) v) ∧
      Continuous (argmaxFn (invΓ Nbar) (objG (invModel μ U H c β Nbar) v)) ∧
      ∀ (x₀ : Ici (0 : ℝ)) (ω₀ : Icc ω₁ ω₂) (p : ℝ × ℝ) (U' : ℝ),
        p ∈ policy (invModel μ U H c β Nbar) v (x₀, ω₀) → p.1 < x₀.1 →
        HasDerivAt U U' (x₀.1 - p.1) → HasDerivAt (liftS fun x => v (x, ω₀)) U' x₀.1 := by
  obtain ⟨v, hv, hvR, -, -, hFE, huniq⟩ := upper_fixed (h.upperDP μ)
  have hpol := inv_policy h hv
  exact ⟨v, hv, hvR, hFE, huniq, inv_solves_2 h hv, inv_indep h hv, inv_strictMono h hv,
    inv_strictConcave h hv, hpol.1, hpol.1.continuous_argmaxFn,
    fun _ _ _ _ hp hpos hU' => inv_hasDerivAt h hv hp hpos hU'⟩

end StokeyLucasPrescott.StochasticApplications
