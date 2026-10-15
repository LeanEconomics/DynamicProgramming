/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.BoundedConcave

/-!
# Bounded returns: concave laws of motion, policy convergence, differentiability

SLP §9.2, pp. 265–267 and 269–270.

* `ex_9_7d_concave`: Exercise 9.7d with `φ(·, ·, z′)` concave (in the order of `X`), under the
  hypotheses of part (c) as well — `T` maps the closed set of functions concave and
  nondecreasing in `x` into the strictly concave, strictly increasing ones.
* `ex_9_7e`, `theorem_9_9`: from `v₀` concave in `x`, the policy functions `gₙ` of `vₙ = Tⁿv₀`
  converge to `g` pointwise, and uniformly if `S` is compact (Theorem 3.8).
* `ex_9_7f`, `theorem_9_10`: differentiability of `v(·, z₀)` at interior points
  (Benveniste–Scheinkman, Theorem 4.10).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] {SX : Set E} {SY : Set E'}
  {hX : Convex ℝ SX} {hY : Convex ℝ SY}
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
variable (M : Model SX SY Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- **Exercise 9.7d** (corrected, `φ(·, ·, z′)` concave). With the hypotheses of part (c) —
Assumptions 9.8 and 9.9 and `φ(·, y, z′)` nondecreasing — and
`θφ(x, y, z′) + (1 − θ)φ(x′, y′, z′) ≤ φ(θ(x, y) + (1 − θ)(x′, y′), z′)`, the fixed point `v(·, z)`
is strictly concave and strictly increasing. -/
theorem ex_9_7d_concave [PartialOrder E] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z'))
    (hφc : ∀ x y x' y' z' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      cmb hX h0 h1 (M.φ (x, y, z')) (M.φ (x', y', z')) ≤
        M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z'))
    {v : SX × Z →ᵇ ℝ} (hv : bellman M h v = v) (z : Z) :
    IsStrictConcaveS hX (fun x => v (x, z)) ∧ StrictMono fun x => v (x, z) := by
  set C' : Set (SX × Z →ᵇ ℝ) :=
    {f | ∀ z, IsConcaveS hX (fun x => f (x, z)) ∧ Monotone fun x => f (x, z)}
  have hclosed : IsClosed C' := by
    have h1 := isClosed_concaveX (Z := Z) hX
    have h2 := isClosed_pointwise_le (S := SX × Z) (ι := {q : SX × SX × Z // q.1 ≤ q.2.1})
      (fun q => (q.1.1, q.1.2.2)) (fun q => (q.1.2.1, q.1.2.2))
    convert h1.inter h2 using 1
    ext f
    exact ⟨fun hf => ⟨fun z => (hf z).1, fun q => (hf q.1.2.2).2 q.2⟩,
      fun hf z => ⟨hf.1 z, fun x x' hxx' => hf.2 ⟨(x, x', z), hxx'⟩⟩⟩
  have hmaps : ∀ f ∈ C', bellman M h f ∈ {g : SX × Z →ᵇ ℝ | ∀ z,
      IsStrictConcaveS hX (fun x => g (x, z)) ∧ StrictMono fun x => g (x, z)} := by
    intro f hf z
    refine ⟨bellman_maps_concave M h h910 h911 (fun x x' y y' z hy hy' θ h0 h1 => ?_) z,
      bellman_strictMono_x M h h98 h99 hφx (fun z => (hf z).2) z⟩
    have hyθ := h911 z x y x' y' hy hy' θ h0 h1
    have i0 := integrable_integrand M h f hy z
    have i1 := integrable_integrand M h f hy' z
    have iθ := integrable_integrand M h f hyθ z
    simp only [expV]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
      (i1.const_mul _)]
    refine integral_mono ((i0.const_mul θ).add (i1.const_mul _)) iθ fun z' => ?_
    change θ * f (M.φ (x, y, z'), z') + (1 - θ) * f (M.φ (x', y', z'), z') ≤
      f (M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z'), z')
    exact ((hf z').1 _ _ θ h0 h1).trans ((hf z').2 (hφc x y x' y' z' θ h0 h1))
  have := (corollary_1 (S' := C') (bellman_contraction M h) hv
    ⟨0, fun _ => ⟨fun _ _ _ _ _ => by simp, fun _ _ _ => le_rfl⟩⟩ hclosed
    (fun f hf z => ⟨((hmaps f hf) z).1.isConcaveS, ((hmaps f hf) z).2.monotone⟩) hmaps).2 z
  exact this

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- `|∫ v[φ(x, y, z′), z′] Q(z, dz′) − ∫ w[φ(x, y, z′), z′] Q(z, dz′)| ≤ ‖v − w‖`. -/
theorem abs_expV_sub_le (h : BoundedDP M) (v w : SX × Z →ᵇ ℝ) {s : SX × Z} {y : SY}
    (hy : y ∈ M.Γ s) : |expV M v s y - expV M w s y| ≤ dist v w := by
  rw [expV, expV, ← integral_sub (integrable_integrand M h v hy _)
    (integrable_integrand M h w hy _)]
  have := norm_integral_le_of_norm_le_const (μ := M.Q s.2) (C := dist v w)
    (f := fun z' => v (M.φ (s.1, y, z'), z') - w (M.φ (s.1, y, z'), z'))
    (Eventually.of_forall fun z' => by rw [← dist_eq_norm]; exact dist_coe_le_dist _)
  simpa [Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 9.7e** (policy convergence). Let `φ` be affine with `φ(x, ·, z′)` one-to-one, let
`v₀` be bounded, continuous and concave in `x`, and let `gₙ` be the policy function of
`vₙ = Tⁿv₀`. Then `gₙ → g` pointwise, and uniformly if `S` is compact. -/
theorem ex_9_7e [Nonempty SY] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman M h v = v) {v₀ : SX × Z →ᵇ ℝ} (hv₀ : ∀ z, IsConcaveS hX fun x => v₀ (x, z)) :
    (∀ s, Tendsto (fun n => argmaxFn M.Γ (objG M ((bellman M h)^[n] v₀)) s) atTop
      (𝓝 (argmaxFn M.Γ (objG M v) s))) ∧
    (CompactSpace (SX × Z) → TendstoUniformly
      (fun n => argmaxFn M.Γ (objG M ((bellman M h)^[n] v₀))) (argmaxFn M.Γ (objG M v)) atTop) := by
  set T := bellman M h
  have hmaps := fun (f : SX × Z →ᵇ ℝ) (hf : ∀ z, IsConcaveS hX fun x => f (x, z)) =>
    bellman_maps_concave M h h910 h911 (f := f) fun x x' y y' z hy hy' θ h0 h1 =>
      expV_comb M h haff hf hy hy' h0 h1 (h911 z x y x' y' hy hy' θ h0 h1)
  have hconc : ∀ n, ∀ z, IsConcaveS hX fun x => (T^[n] v₀) (x, z) := by
    intro n
    induction n with
    | zero => exact hv₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact fun z => (hmaps _ ih z).isConcaveS
  have hU : ∀ n, UniqueArgmax M.Γ (objG M (T^[n + 1] v₀)) := fun n => by
    have hsc : ∀ z, IsStrictConcaveS hX fun x => (T^[n + 1] v₀) (x, z) := by
      rw [Function.iterate_succ_apply']
      exact hmaps _ (hconc n)
    exact ⟨h.nonempty, h.compact, h.lhc, h.uhc, continuousOn_objG M h _,
      argmax_unique_of_strictConcave M h h910 h911 haff hinj hsc⟩
  have hUv := (ex_9_7d_policy M h h910 h911 haff hinj hv).1
  have hunif : TendstoUniformlyOn (fun n => objG M (T^[n + 1] v₀)) (objG M v) atTop
      (graph M.Γ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => M.β * (M.β ^ (n + 1) * dist v₀ v)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).comp
        (tendsto_add_atTop_nat 1)).mul_const (dist v₀ v) |>.const_mul M.β
      simpa using this
    obtain ⟨w, -, hwu, hwr⟩ := theorem_3_2 (bellman_contraction M h)
    rw [← hwu v hv] at hwr
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn p hp
    have hd : dist (T^[n + 1] v₀) v ≤ M.β ^ (n + 1) * dist v₀ v := hwr v₀ (n + 1)
    simp only [objG, rhs, Real.dist_eq]
    calc |M.F (p.1.1, p.2, p.1.2) + M.β * expV M v p.1 p.2 -
          (M.F (p.1.1, p.2, p.1.2) + M.β * expV M (T^[n + 1] v₀) p.1 p.2)|
        = M.β * |expV M v p.1 p.2 - expV M (T^[n + 1] v₀) p.1 p.2| := by
          rw [show M.F (p.1.1, p.2, p.1.2) + M.β * expV M v p.1 p.2 -
            (M.F (p.1.1, p.2, p.1.2) + M.β * expV M (T^[n + 1] v₀) p.1 p.2) =
            M.β * (expV M v p.1 p.2 - expV M (T^[n + 1] v₀) p.1 p.2) by ring, abs_mul,
            abs_of_pos h.β_pos]
      _ ≤ M.β * (M.β ^ (n + 1) * dist v₀ v) := by
          refine mul_le_mul_of_nonneg_left ?_ h.β_pos.le
          exact (abs_expV_sub_le M h _ _ hp).trans (by rw [dist_comm]; exact hd)
      _ < ε := hn
  refine ⟨fun s => ?_, fun _ => ?_⟩
  · exact (tendsto_add_atTop_iff_nat 1).1 (theorem_3_8 hUv hU hunif s)
  · have := theorem_3_8_uniform hUv hU hunif
    rw [Metric.tendstoUniformly_iff] at this ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (this ε hε)
    refine eventually_atTop.2 ⟨N + 1, fun n hn x => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact hN k (by omega) x

/-- **Theorem 9.9** (first formulation): from `v₀` concave in `x`, `gₙ → g` pointwise, uniformly
if `X` and `Z` are compact. -/
theorem theorem_9_9 [Nonempty SX] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : SX × Z → Set SX)
    (F : SX × SX × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h910 : Assumption910 hX hX (Model.first Q Γ F β))
    (h911 : Assumption911 hX hX (Model.first Q Γ F β)) {v : SX × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) {v₀ : SX × Z →ᵇ ℝ}
    (hv₀ : ∀ z, IsConcaveS hX fun x => v₀ (x, z)) :
    (∀ s, Tendsto (fun n => argmaxFn Γ (objG (Model.first Q Γ F β)
      ((bellman (Model.first Q Γ F β) h)^[n] v₀)) s) atTop
      (𝓝 (argmaxFn Γ (objG (Model.first Q Γ F β) v) s))) ∧
    (CompactSpace (SX × Z) → TendstoUniformly
      (fun n => argmaxFn Γ (objG (Model.first Q Γ F β)
        ((bellman (Model.first Q Γ F β) h)^[n] v₀)))
      (argmaxFn Γ (objG (Model.first Q Γ F β) v)) atTop) :=
  ex_9_7e (Model.first Q Γ F β) h h910 h911 (fun _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ hne => hne) hv hv₀

omit [MetricSpace Z] [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
/-- Under Assumption 9.11 the values of `Γ` are convex sets. -/
theorem convex_image_Γ (h911 : Assumption911 hX hY M) (s : SX × Z) :
    Convex ℝ (Subtype.val '' M.Γ s) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := h911 s.2 s.1 y s.1 y' hy hy' a ha (by linarith)
  rw [cmb_self] at this
  exact ⟨_, this, rfl⟩

omit [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
/-- If `g₀` is interior to `Γ(x₀, z₀) ⊆ ℝᵐ`, then `g₀ ∈ Γ(x, z₀)` for all `x` near `x₀`. -/
theorem eventually_mem_Γ {m : ℕ} {T : Set (Fin m → ℝ)} {hT : Convex ℝ T} (N : Model SX T Z)
    (hl : ∀ s, IsLHC N.Γ s) (h911 : Assumption911 hX hT N) {x₀ : SX} {z₀ : Z} {g₀ : T}
    (hg : g₀.1 ∈ interior (Subtype.val '' N.Γ (x₀, z₀))) :
    ∀ᶠ x in 𝓝 x₀, g₀ ∈ N.Γ (x, z₀) := by
  have hlhc : IsLHC (fun x => Subtype.val '' N.Γ (x, z₀)) x₀ := by
    refine ⟨(hl (x₀, z₀)).1.image _, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ xs hxs
    obtain ⟨N', ys, hys, hlim⟩ := (hl (x₀, z₀)).2 y hy (fun n => (xs n, z₀))
      (hxs.prodMk_nhds tendsto_const_nhds)
    exact ⟨N', fun n => (ys n).1, fun n hn => ⟨ys n, hys n hn, rfl⟩,
      (continuous_subtype_val.tendsto y).comp hlim⟩
  have hseq : ∀ xs : ℕ → SX, Tendsto xs atTop (𝓝 x₀) → ∀ᶠ n in atTop, g₀ ∈ N.Γ (xs n, z₀) :=
    fun xs hxs => (eventually_mem_of_mem_interior (fun x => convex_image_Γ N h911 (x, z₀))
      hlhc hg hxs).mono fun n ⟨y, hy, hyg⟩ => Subtype.ext hyg ▸ hy
  exact eventually_iff_seq_eventually.2 hseq

omit [MeasurableSpace E] in
/-- A function on `X ⊆ E` extended by zero. -/
noncomputable def liftS (f : SX → ℝ) (x : E) : ℝ := by
  classical exact if hx : x ∈ SX then f ⟨x, hx⟩ else 0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] in
theorem liftS_of_mem (f : SX → ℝ) {x : E} (hx : x ∈ SX) : liftS f x = f ⟨x, hx⟩ := by
  simp only [liftS, hx, ↓reduceDIte]

omit [MeasurableSpace E] in
/-- A concave function on `X` is concave on `X ⊆ E` after extension. -/
theorem concaveOn_liftS {f : SX → ℝ} (hf : IsConcaveS hX f) : ConcaveOn ℝ SX (liftS f) := by
  refine ⟨hX, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hmem : a • x + b • y ∈ SX := hX hx hy ha hb hab
  rw [liftS_of_mem f hx, liftS_of_mem f hy, liftS_of_mem f hmem, smul_eq_mul, smul_eq_mul]
  have := hf ⟨x, hx⟩ ⟨y, hy⟩ a ha ha1
  subst hb'
  exact this

/-- **Exercise 9.7f** with the neighbourhood condition as a hypothesis. Let `φ(x, y, z′)` not
depend on `x`, let `x₀ ∈ int X`, let `g₀ = g(x₀, z₀)` lie in `Γ(x, z₀)` for all `x` near `x₀`,
and let `x ↦ F(x, g₀, z₀)` have derivative `DF` at `x₀`. Then `v(·, z₀)` is differentiable at
`x₀` with derivative `DF`. -/
theorem ex_9_7f' [Nonempty SY] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman M h v = v) (hφx : ∀ x x' y z', M.φ (x, y, z') = M.φ (x', y, z'))
    {x₀ : SX} {z₀ : Z} (hint : SX ∈ 𝓝 x₀.1)
    (hev : ∀ᶠ x in 𝓝 x₀, argmaxFn M.Γ (objG M v) (x₀, z₀) ∈ M.Γ (x, z₀)) {DF : E →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x => M.F (x, argmaxFn M.Γ (objG M v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 := by
  set g₀ := argmaxFn M.Γ (objG M v) (x₀, z₀)
  obtain ⟨hU, -, -⟩ := ex_9_7d_policy M h h910 h911 haff hinj hv
  have hvc := ex_9_7d M h h910 h911 haff hv z₀
  set c := M.β * expV M v (x₀, z₀) g₀
  set W : E → ℝ := fun x => liftS (fun x => M.F (x, g₀, z₀)) x + c
  have hW : HasFDerivAt W DF x₀.1 := hF.add_const c
  have hg₀ := hU.argmaxFn_mem (x₀, z₀)
  have hvx : ∀ s, v s = maxValue (objG M v) M.Γ s := fun s => by
    rw [← bellman_apply M h, hv]
  have hexp : ∀ x : SX, expV M v (x, z₀) g₀ = expV M v (x₀, z₀) g₀ := fun x => by
    simp only [expV]
    congr 1
    funext z'
    rw [hφx x x₀]
  have heq : W x₀.1 = liftS (fun x => v (x, z₀)) x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx (x₀, z₀), ← hg₀.2]
    rfl
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS (fun x => v (x, z₀)) x := by
    have h1 := hev
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx (⟨x, hxS⟩, z₀)]
    have := le_maxValue (continuousOn_objG M h v) (h.compact _) (hx ⟨x, hxS⟩ rfl)
    simp only [objG, rhs] at this
    rw [hexp] at this
    exact this
  exact theorem_4_10 (concaveOn_liftS hvc.isConcaveS) hint hW heq hle

/-- **Exercise 9.7f.** As `ex_9_7f'`, for actions in `ℝᵐ` with `g(x₀, z₀) ∈ int Γ(x₀, z₀)`:
then `vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]`. -/
theorem ex_9_7f {m : ℕ} {T : Set (Fin m → ℝ)} {hT : Convex ℝ T} [Nonempty T]
    (N : Model SX T Z) [IsMarkovKernel N.Q] (h : BoundedDP N) (h910 : Assumption910 hX hT N)
    (h911 : Assumption911 hX hT N) (haff : IsAffineφ hX hT N)
    (hinj : ∀ x y y' z', y ≠ y' → N.φ (x, y, z') ≠ N.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman N h v = v) (hφx : ∀ x x' y z', N.φ (x, y, z') = N.φ (x', y, z'))
    {x₀ : SX} {z₀ : Z} (hint : SX ∈ 𝓝 x₀.1)
    (hg : (argmaxFn N.Γ (objG N v) (x₀, z₀)).1 ∈ interior (Subtype.val '' N.Γ (x₀, z₀)))
    {DF : E →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x => N.F (x, argmaxFn N.Γ (objG N v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 :=
  ex_9_7f' N h h910 h911 haff hinj hv hφx hint (eventually_mem_Γ N h.lhc h911 hg) hF

/-- **Theorem 9.10** (first formulation, `X ⊆ ℝˡ`). Under Assumptions 9.4–9.7 and 9.10–9.12, if
`x₀ ∈ int X` and `g(x₀, z₀) ∈ int Γ(x₀, z₀)`, then `v(·, z₀)` is differentiable at `x₀` with
`vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]`. -/
theorem theorem_9_10 {l : ℕ} {S : Set (Fin l → ℝ)} {hS : Convex ℝ S} [Nonempty S]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : S × Z → Set S)
    (F : S × S × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h910 : Assumption910 hS hS (Model.first Q Γ F β))
    (h911 : Assumption911 hS hS (Model.first Q Γ F β)) {v : S × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) {x₀ : S} {z₀ : Z} (hint : S ∈ 𝓝 x₀.1)
    (hg : (argmaxFn Γ (objG (Model.first Q Γ F β) v) (x₀, z₀)).1 ∈
      interior (Subtype.val '' Γ (x₀, z₀)))
    {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x =>
      F (x, argmaxFn Γ (objG (Model.first Q Γ F β) v) (x₀, z₀), z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 :=
  ex_9_7f (Model.first Q Γ F β) h h910 h911 (fun _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ hne => hne) hv (fun _ _ _ _ => rfl) hint hg hF

end StokeyLucasPrescott.StochasticApplications
