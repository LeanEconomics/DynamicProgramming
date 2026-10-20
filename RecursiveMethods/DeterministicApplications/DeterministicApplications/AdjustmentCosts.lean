/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.ConvexInvestment
import DeterministicApplications.GrowthDiscount
import DeterministicApplications.GrowthDifferentiability

/-!
# Investment with bounds, with convex adjustment costs, and short-run profits

SLP §5.9, pp. 112–113, continued. All three problems live on a compact state space `[0, K]`.

* **Exercise 5.9a with bounds** (`ex_5_9a_bounds`): with
  `(1 − δ)k ≤ y ≤ (1 − δ)k + a` and `K ≥ a/δ` (so `[0, K]` is invariant), there is a unique
  bounded continuous `v`; it is concave, and the policy is the target `ŷ = argmax [−qy + βv(y)]`
  pushed into the feasible interval.
* **Exercise 5.9b** (`ex_5_9b`): with a strictly convex cost `c` of gross investment and `f`
  strictly concave, Assumption 4.7 holds, so `v` is strictly concave and the policy `g` is a
  continuous function. `g` is nondecreasing (`ex_5_9b_mono`) and
  `g(k') − g(k) ≤ (1 − δ)(k' − k)` (`ex_5_9b_slope`): investment falls as capital rises, so
  capital adjusts gradually. Both are lattice arguments: no derivatives are used.
  `ex_5_9b_envelope`, `ex_5_9b_foc`, `ex_5_9b_euler`: `v'(k) = pf'(k) + (1 − δ)c'(i)`,
  `c'(i) = βv'(g(k))`, and the Euler equation
  `c'(g(k) − (1 − δ)k) = β[pf'(g(k)) + (1 − δ)c'(g(g(k)) − (1 − δ)g(k))]`, which at a steady
  state reads `c'(δk*)(1 − β(1 − δ)) = βpf'(k*)` (`ex_5_9b_steady`). With a linear cost the
  marginal cost of investing is constant and the firm jumps to its target (part a).
* **Exercise 5.9c**: short-run profit `Π(k) = max_{l ≥ 0} [pF(k, l) − wl]`.
  `labor_demand_exists`: labour demand exists if `F(k, ·)` is continuous and `F(k, l)/l → 0`;
  `labor_demand_unique`: it is unique if `F(k, ·)` is strictly concave. Then `Π(0) = 0` if
  `F(0, ·) = 0` (`profitPi_zero`), `Π` is nondecreasing if `F` is (`profitPi_mono`), concave if
  `F` is jointly concave (`profitPi_concave`), strictly concave if `F` is jointly strictly
  concave (`profitPi_strictConcave`), and `Π'(k) = pF_k(k, φ(k))` (`profitPi_deriv`).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

variable {f c : ℝ → ℝ} {p q δ β a K : ℝ}

/-- A concave function on `[0, K]` extends to a concave function on the real interval. -/
theorem concaveOn_liftR_of_concave {v : Icc (0 : ℝ) K → ℝ} (hv : IsConcaveS (convex_Icc 0 K) v) :
    ConcaveOn ℝ (Icc 0 K) (liftR K v) := by
  refine ⟨convex_Icc 0 K, fun x hx y hy s t hs ht hst => ?_⟩
  have ht' : t = 1 - s := by linarith
  subst ht'
  have hmem : s • x + (1 - s) • y ∈ Icc (0 : ℝ) K := convex_Icc 0 K hx hy hs ht hst
  rw [liftR_of_mem v hx, liftR_of_mem v hy, liftR_of_mem v hmem, smul_eq_mul, smul_eq_mul]
  exact hv ⟨x, hx⟩ ⟨y, hy⟩ s hs (by linarith)

/-- A continuous function on the compact `[0, K] × [0, K]` is bounded. -/
theorem exists_bound_Icc_prod {F : Icc (0 : ℝ) K × Icc (0 : ℝ) K → ℝ} (hF : Continuous F) :
    ∃ B, ∀ p, |F p| ≤ B := by
  have : CompactSpace (Icc (0 : ℝ) K) := isCompact_iff_compactSpace.1 isCompact_Icc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨B, fun p => by simpa [Real.norm_eq_abs] using hB p (mem_univ p)⟩

/-! ### Exercise 5.9a with bounds on investment -/

/-- The return `pf(k) − q[y − (1 − δ)k] = G(k) − qy` on `[0, K]`. -/
def investF (f : ℝ → ℝ) (p q δ K : ℝ) (pr : Icc (0 : ℝ) K × Icc (0 : ℝ) K) : ℝ :=
  investG f p q δ pr.1.1 - q * pr.2.1

/-- `Γ(k) = [(1 − δ)k, (1 − δ)k + a]`. -/
def boundedΓ (δ a K : ℝ) : Icc (0 : ℝ) K → Set (Icc (0 : ℝ) K) :=
  intervalΓ K (fun k => (1 - δ) * k) (fun k => (1 - δ) * k + a)

theorem bounded_assumption43 (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha : 0 ≤ a) (hK : a ≤ δ * K) :
    Assumption43 (boundedΓ δ a K) :=
  intervalΓ_assumption43 (continuousOn_const.mul continuousOn_id)
    ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
    (fun x hx => mul_nonneg (by linarith) hx.1) (fun x _ => by linarith)
    (fun x hx => by nlinarith [hx.2])

theorem bounded_assumption44 (hβ0 : 0 < β) (hβ1 : β < 1) (hf : ContinuousOn f (Icc 0 K)) :
    Assumption44 (boundedΓ δ a K) (investF f p q δ K) β := by
  have hc : Continuous (investF f p q δ K) :=
    ((continuous_const.mul (hf.comp_continuous (continuous_subtype_val.comp continuous_fst)
      fun pr => pr.1.2)).add (continuous_const.mul (continuous_subtype_val.comp
        continuous_fst))).sub (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  obtain ⟨B, hB⟩ := exists_bound_Icc_prod hc
  exact ⟨hc.continuousOn, ⟨B, fun pr _ => hB pr⟩, hβ0, hβ1⟩

/-- **Exercise 5.9a with bounds.** There is a unique bounded continuous `v`; it is concave; and
with `ŷ` maximizing `−qy + βv(y)` on `[0, K]`, the choice
`max{(1 − δ)k, min{ŷ, (1 − δ)k + a}}` is optimal at every `k`. -/
theorem ex_5_9a_bounds (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha : 0 ≤ a) (hK : a ≤ δ * K)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : 0 ≤ p) (hfc : ContinuousOn f (Icc 0 K))
    (hfcc : ConcaveOn ℝ (Icc 0 K) f) :
    ∃ v : Icc (0 : ℝ) K →ᵇ ℝ,
      bellman (bounded_assumption43 hδ0 hδ1 ha hK) (bounded_assumption44 (a := a) (p := p)
        (q := q) (δ := δ) hβ0 hβ1 hfc) v = v ∧
      (∀ w, bellman (bounded_assumption43 hδ0 hδ1 ha hK) (bounded_assumption44 (a := a) (p := p)
        (q := q) (δ := δ) hβ0 hβ1 hfc) w = w → w = v) ∧
      IsConcaveS (convex_Icc 0 K) v ∧
      ∃ yhat : Icc (0 : ℝ) K, ∀ k : Icc (0 : ℝ) K,
        ∀ hc : max ((1 - δ) * k.1) (min yhat.1 ((1 - δ) * k.1 + a)) ∈ Icc (0 : ℝ) K,
          (⟨_, hc⟩ : Icc (0 : ℝ) K) ∈
            argmax (obj (investF f p q δ K) β v) (boundedΓ δ a K) k := by
  have hK0 : 0 ≤ K := by nlinarith
  have : Nonempty (Icc (0 : ℝ) K) := ⟨⟨0, le_rfl, hK0⟩⟩
  have : CompactSpace (Icc (0 : ℝ) K) := isCompact_iff_compactSpace.1 isCompact_Icc
  set h43 := bounded_assumption43 hδ0 hδ1 ha hK
  set h44 := bounded_assumption44 (a := a) (p := p) (q := q) (δ := δ) hβ0 hβ1 hfc
  obtain ⟨v, hv, huniq, -⟩ := theorem_4_6 h43 h44
  -- `F` is concave on the graph and `Γ` has a convex graph
  have hF : ∀ x y x' y', y ∈ boundedΓ δ a K x → y' ∈ boundedΓ δ a K x' →
      ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * investF f p q δ K (x, y) + (1 - θ) * investF f p q δ K (x', y') ≤
        investF f p q δ K (cmb (convex_Icc 0 K) h0 h1 x x', cmb (convex_Icc 0 K) h0 h1 y y') := by
    intro x y x' y' _ _ θ h0 h1
    have hfw := hfcc.2 x.2 x'.2 h0 (sub_nonneg.2 h1) (by ring)
    simp only [smul_eq_mul] at hfw
    simp only [investF, investG, cmb, smul_eq_mul]
    nlinarith
  have h48 : Assumption48 (convex_Icc 0 K) (boundedΓ δ a K) := by
    intro x y x' y' hy hy' θ h0 h1
    have h1' : 0 ≤ 1 - θ := by linarith
    simp only [boundedΓ, intervalΓ, cmb, smul_eq_mul, mem_ofPred_eq] at hy hy' ⊢
    constructor <;> nlinarith [hy.1, hy.2, hy'.1, hy'.2]
  have hvc := fixed_concave_of_concaveF h43 h44 hF h48 hv
  -- the target `ŷ`
  set ψ : ℝ → ℝ := fun y => -(q * y) + β * liftR K v y
  have hψc : ConcaveOn ℝ (Icc 0 K) ψ :=
    ((LinearMap.mulLeft ℝ (-q)).concaveOn (convex_Icc 0 K)).add
      ((concaveOn_liftR_of_concave hvc).smul hβ0.le) |>.congr fun y _ => by
        simp [ψ, smul_eq_mul]
  have hψcont : ContinuousOn ψ (Icc 0 K) := by
    refine (continuousOn_const.mul continuousOn_id).neg.add (continuousOn_const.mul ?_)
    refine (v.continuous.comp (continuous_projIcc (h := hK0))).continuousOn.congr fun y hy => ?_
    rw [liftR_of_mem v hy, Function.comp_apply, projIcc_of_mem hK0 hy]
  obtain ⟨yh, hyh, hyhmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hK0) hψcont
  refine ⟨v, hv, huniq, hvc, ⟨yh, hyh⟩, fun k hc => ?_⟩
  have hl0 : 0 ≤ (1 - δ) * k.1 := mul_nonneg (by linarith) k.2.1
  have hlu : (1 - δ) * k.1 ≤ (1 - δ) * k.1 + a := by linarith
  have hsub : Icc ((1 - δ) * k.1) ((1 - δ) * k.1 + a) ⊆ Icc 0 K := fun z hz =>
    ⟨hl0.trans hz.1, hz.2.trans (by nlinarith [k.2.2])⟩
  have hmemΓ : (⟨_, hc⟩ : Icc (0 : ℝ) K) ∈ boundedΓ δ a K k :=
    ⟨le_max_left _ _, max_le hlu ((min_le_right _ _))⟩
  have hge : ∀ z ∈ boundedΓ δ a K k, obj (investF f p q δ K) β v (k, z) ≤
      obj (investF f p q δ K) β v (k, ⟨_, hc⟩) := fun z hz => by
    have := clamp_maximizes hψc hyh (fun y hy => hyhmax hy) hlu hsub (y := z.1) hz
    simp only [ψ, liftR_of_mem v z.2, liftR_of_mem v hc] at this
    simp only [obj, investF]
    linarith
  refine ⟨hmemΓ, le_antisymm (le_maxValue (continuousOn_obj h44 v.continuous) (h43.compact k)
    hmemΓ) ?_⟩
  obtain ⟨y, hy, hyv, -⟩ := exists_argmax (continuousOn_obj h44 v.continuous) (h43.compact k)
    (h43.nonempty k)
  rw [← hyv]
  exact hge y hy

/-! ### Exercise 5.9b: convex adjustment costs -/

/-- The return `pf(k) − c(y − (1 − δ)k)` on `[0, K]`. -/
def adjF (f c : ℝ → ℝ) (p δ K : ℝ) (pr : Icc (0 : ℝ) K × Icc (0 : ℝ) K) : ℝ :=
  p * f pr.1.1 - c (pr.2.1 - (1 - δ) * pr.1.1)

/-- `Γ(k) = [0, K]`. -/
def fullΓ (K : ℝ) : Icc (0 : ℝ) K → Set (Icc (0 : ℝ) K) := intervalΓ K (fun _ => 0) (fun _ => K)

theorem full_assumption43 (hK : 0 ≤ K) : Assumption43 (fullΓ K) :=
  intervalΓ_assumption43 continuousOn_const continuousOn_const (fun _ _ => le_rfl)
    (fun _ _ => hK) (fun _ _ => le_rfl)

theorem mem_fullΓ (k y : Icc (0 : ℝ) K) : y ∈ fullΓ K k := ⟨y.2.1, y.2.2⟩

theorem adj_assumption44 (hβ0 : 0 < β) (hβ1 : β < 1) (hf : ContinuousOn f (Icc 0 K))
    (hc : Continuous c) : Assumption44 (fullΓ K) (adjF f c p δ K) β := by
  have hcont : Continuous (adjF f c p δ K) :=
    (continuous_const.mul (hf.comp_continuous (continuous_subtype_val.comp continuous_fst)
      fun pr => pr.1.2)).sub (hc.comp ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))
  obtain ⟨B, hB⟩ := exists_bound_Icc_prod hcont
  exact ⟨hcont.continuousOn, ⟨B, fun pr _ => hB pr⟩, hβ0, hβ1⟩

/-- Assumption 4.7: `f` strictly concave and `c` convex. -/
theorem adj_a47 (hp : 0 < p) (hf : StrictConcaveOn ℝ (Icc 0 K) f) (hc : ConvexOn ℝ univ c) :
    Assumption47 (convex_Icc 0 K) (fullΓ K) (adjF f c p δ K) := by
  intro x y x' y' _ _ θ h0 h1
  have h1' : 0 ≤ 1 - θ := by linarith
  have hcw := hc.2 (mem_univ (y.1 - (1 - δ) * x.1)) (mem_univ (y'.1 - (1 - δ) * x'.1)) h0.le h1'
    (by ring)
  simp only [smul_eq_mul] at hcw
  have hfw := hf.concaveOn.2 x.2 x'.2 h0.le h1' (by ring)
  simp only [smul_eq_mul] at hfw
  have e : θ * y.1 + (1 - θ) * y'.1 - (1 - δ) * (θ * x.1 + (1 - θ) * x'.1) =
      θ * (y.1 - (1 - δ) * x.1) + (1 - θ) * (y'.1 - (1 - δ) * x'.1) := by ring
  simp only [adjF, cmb, smul_eq_mul, e]
  refine ⟨by nlinarith, fun hne => ?_⟩
  have hne' : x.1 ≠ x'.1 := fun he => hne (Subtype.ext he)
  have hfs := hf.2 x.2 x'.2 hne' h0 (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hfs
  nlinarith

theorem full_a48 : Assumption48 (convex_Icc 0 K) (fullΓ K) := fun _ y _ y' _ _ _ h0 h1 =>
  mem_fullΓ _ (cmb (convex_Icc 0 K) h0 h1 y y')

/-- The hypotheses of Exercise 5.9b. -/
structure AdjHyp (f c : ℝ → ℝ) (p δ β K : ℝ) : Prop where
  p_pos : 0 < p
  δ_pos : 0 < δ
  δ_lt : δ < 1
  β_pos : 0 < β
  β_lt : β < 1
  K_pos : 0 < K
  f_cont : ContinuousOn f (Icc 0 K)
  f_concave : StrictConcaveOn ℝ (Icc 0 K) f
  c_cont : Continuous c
  c_convex : ConvexOn ℝ univ c

theorem AdjHyp.h43 (h : AdjHyp f c p δ β K) : Assumption43 (fullΓ K) :=
  full_assumption43 h.K_pos.le

theorem AdjHyp.h44 (h : AdjHyp f c p δ β K) : Assumption44 (fullΓ K) (adjF f c p δ K) β :=
  adj_assumption44 h.β_pos h.β_lt h.f_cont h.c_cont

/-- **Exercise 5.9b.** `v` is strictly concave and the policy is a continuous function. -/
theorem ex_5_9b [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) :
    IsStrictConcaveS (convex_Icc 0 K) v ∧ UniqueArgmax (fullΓ K) (obj (adjF f c p δ K) β v) ∧
      Continuous (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)) := by
  obtain ⟨h1, h2, -, h4⟩ := theorem_4_8 h.h43 h.h44 (adj_a47 h.p_pos h.f_concave h.c_convex)
    full_a48 hv
  exact ⟨h1, h2, h4⟩

/-- **Exercise 5.9b.** The policy is nondecreasing. -/
theorem ex_5_9b_mono [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) :
    Monotone (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)) := by
  obtain ⟨-, hUA, -⟩ := ex_5_9b h hv
  intro k k' hkk'
  set g := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)
  by_contra hlt
  push Not at hlt
  have hk : k.1 ≤ k'.1 := hkk'
  have hlt' : (g k').1 < (g k).1 := hlt
  -- swapping the two choices helps by convexity of `c`, contradicting uniqueness
  have e1 := hUA.lt_of_ne (mem_fullΓ k (g k')) hlt.ne
  have e2 := hUA.lt_of_ne (mem_fullΓ k' (g k)) hlt.ne'
  have hex := concave_exchange (φ := fun z => -c z) (s := univ) h.c_convex.neg
    (p := (g k').1 - (1 - δ) * k'.1) (q := (g k').1 - (1 - δ) * k.1)
    (δ := (g k).1 - (g k').1) (mem_univ _) (mem_univ _)
    (by nlinarith [h.δ_lt]) (by linarith)
  simp only [obj, adjF] at e1 e2 hex
  rw [show (g k').1 - (1 - δ) * k.1 + ((g k).1 - (g k').1) = (g k).1 - (1 - δ) * k.1 by ring,
    show (g k').1 - (1 - δ) * k'.1 + ((g k).1 - (g k').1) = (g k).1 - (1 - δ) * k'.1 by ring]
    at hex
  linarith

/-- **Exercise 5.9b.** `g(k') − g(k) ≤ (1 − δ)(k' − k)`: gross investment `g(k) − (1 − δ)k`
falls as capital rises. -/
theorem ex_5_9b_slope [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k k' : Icc (0 : ℝ) K} (hkk' : k ≤ k') :
    (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k').1 -
        (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 ≤ (1 - δ) * (k'.1 - k.1) := by
  obtain ⟨hvs, hUA, -⟩ := ex_5_9b h hv
  have hvc := concaveOn_liftR hvs
  set g := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)
  have hk : k.1 ≤ k'.1 := hkk'
  have hgm := ex_5_9b_mono h hv hkk'
  have hgm' : (g k).1 ≤ (g k').1 := hgm
  by_contra hgt
  push Not at hgt
  set i := (g k).1 - (1 - δ) * k.1 with hi_def
  set i' := (g k').1 - (1 - δ) * k'.1 with hi'_def
  have hii : i < i' := by simp only [i, i']; linarith
  -- the exchanged choices `y₁ = i' + (1 − δ)k` at `k` and `y₂ = i + (1 − δ)k'` at `k'`
  have hy₁ : i' + (1 - δ) * k.1 ∈ Icc (0 : ℝ) K :=
    ⟨by simp only [i']; nlinarith [(g k).2.1, h.δ_lt], by simp only [i']; nlinarith [(g k').2.2,
      h.δ_lt]⟩
  have hy₂ : i + (1 - δ) * k'.1 ∈ Icc (0 : ℝ) K :=
    ⟨by simp only [i]; nlinarith [(g k).2.1, h.δ_lt], by simp only [i]; nlinarith [(g k').2.2,
      h.δ_lt]⟩
  have hne₁ : (⟨_, hy₁⟩ : Icc (0 : ℝ) K) ≠ g k := fun he => by
    have := congrArg Subtype.val he; simp only at this; linarith
  have hne₂ : (⟨_, hy₂⟩ : Icc (0 : ℝ) K) ≠ g k' := fun he => by
    have := congrArg Subtype.val he; simp only at this; linarith
  have e1 := hUA.lt_of_ne (mem_fullΓ k _) hne₁
  have e2 := hUA.lt_of_ne (mem_fullΓ k' _) hne₂
  -- concavity of `v`: `v(gₖ) + v(gₖ') ≤ v(y₁) + v(y₂)`
  have hex := concave_exchange hvc (p := (g k).1) (q := i' + (1 - δ) * k.1)
    (δ := (1 - δ) * (k'.1 - k.1)) (g k).2 (by
      rw [show i' + (1 - δ) * k.1 + (1 - δ) * (k'.1 - k.1) = (g k').1 by simp only [i']; ring]
      exact (g k').2) (by simp only [i, i'] at hii ⊢; linarith) (by nlinarith [h.δ_lt])
  rw [show i' + (1 - δ) * k.1 + (1 - δ) * (k'.1 - k.1) = (g k').1 by simp only [i']; ring,
    show (g k).1 + (1 - δ) * (k'.1 - k.1) = i + (1 - δ) * k'.1 by simp only [i]; ring,
    liftR_of_mem v (g k).2, liftR_of_mem v (g k').2, liftR_of_mem v hy₁,
    liftR_of_mem v hy₂] at hex
  simp only [Subtype.coe_eta] at hex
  simp only [obj, adjF] at e1 e2
  have r1 : i' + (1 - δ) * k.1 - (1 - δ) * k.1 = i' := by ring
  have r2 : i + (1 - δ) * k'.1 - (1 - δ) * k'.1 = i := by ring
  rw [r1] at e1
  rw [r2] at e2
  have hβ := h.β_pos
  nlinarith

/-- **Exercise 5.9b (envelope condition).** At an interior `k₀`,
`v'(k₀) = pf'(k₀) + (1 − δ)c'(g(k₀) − (1 − δ)k₀)`. -/
theorem ex_5_9b_envelope [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k₀ : Icc (0 : ℝ) K} (hk₀ : k₀.1 ∈ Ioo 0 K) {f' c' : ℝ}
    (hf' : HasDerivAt f f' k₀.1)
    (hc' : HasDerivAt c c' ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k₀).1 -
      (1 - δ) * k₀.1)) :
    HasDerivAt (liftR K v) (p * f' + (1 - δ) * c') k₀.1 := by
  obtain ⟨hvs, hUA, -⟩ := ex_5_9b h hv
  set g₀ := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k₀
  have hX : Icc (0 : ℝ) K ∈ 𝓝 k₀.1 := Icc_mem_nhds hk₀.1 hk₀.2
  set W : ℝ → ℝ := fun x => p * f x - c (g₀.1 - (1 - δ) * x) + β * v g₀
  have hW : HasDerivAt W (p * f' + (1 - δ) * c') k₀.1 := by
    have h2 : HasDerivAt (fun x => p * f x - c (g₀.1 - (1 - δ) * x) + β * v g₀)
        (p * f' - c' * (0 - (1 - δ) * 1)) k₀.1 :=
      ((hf'.const_mul p).sub (hc'.comp k₀.1 ((hasDerivAt_const k₀.1 g₀.1).sub
        ((hasDerivAt_id' k₀.1).const_mul (1 - δ))))).add_const (β * v g₀)
    convert h2 using 1
    ring
  have hvx : ∀ x, v x = maxValue (obj (adjF f c p δ K) β v) (fullΓ K) x := fun x => by
    rw [← bellman_apply h.h43 h.h44, hv]
  have heq : W k₀.1 = liftR K v k₀.1 := by
    rw [liftR_of_mem v k₀.2, Subtype.coe_eta, hvx k₀]
    exact (hUA.argmaxFn_mem k₀).2
  have hle : ∀ᶠ x in 𝓝 k₀.1, W x ≤ liftR K v x := by
    filter_upwards [hX] with x hx
    rw [liftR_of_mem v hx, hvx]
    exact le_maxValue (x := ⟨x, hx⟩) (z := g₀) (continuousOn_obj h.h44 v.continuous)
      (h.h43.compact _) (mem_fullΓ _ g₀)
  have := (theorem_4_10 (concaveOn_liftR hvs) hX hW.hasFDerivAt heq hle).hasDerivAt
  simpa using this

/-- **Exercise 5.9b (first-order condition).** At an interior `g(k)`,
`c'(g(k) − (1 − δ)k) = βv'(g(k))`. -/
theorem ex_5_9b_foc [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k : Icc (0 : ℝ) K}
    (hg : (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 ∈ Ioo 0 K) {c' v' : ℝ}
    (hc' : HasDerivAt c c' ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 -
      (1 - δ) * k.1))
    (hv' : HasDerivAt (liftR K v) v' (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1) :
    c' = β * v' := by
  obtain ⟨-, hUA, -⟩ := ex_5_9b h hv
  set g₀ := argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k
  set Φ : ℝ → ℝ := fun y => -c (y - (1 - δ) * k.1) + β * liftR K v y
  have hΦ : HasDerivAt Φ (-(c' * 1) + β * v') g₀.1 :=
    (hc'.comp g₀.1 ((hasDerivAt_id' g₀.1).sub_const ((1 - δ) * k.1))).neg.add
      (hv'.const_mul β)
  have hloc : IsLocalMax Φ g₀.1 := by
    filter_upwards [Icc_mem_nhds hg.1 hg.2] with y hy
    have hmem := (hUA.argmaxFn_mem k)
    have hle := le_maxValue (continuousOn_obj h.h44 v.continuous) (h.h43.compact k)
      (mem_fullΓ k ⟨y, hy⟩)
    rw [← hmem.2] at hle
    simp only [obj, adjF, Φ, liftR_of_mem v hy, liftR_of_mem v g₀.2, Subtype.coe_eta] at hle ⊢
    linarith
  have := hloc.hasDerivAt_eq_zero hΦ
  linarith

/-- **Exercise 5.9b (Euler equation).** With `g(k)` interior and the derivatives below,
`c'(g(k) − (1 − δ)k) = β[pf'(g(k)) + (1 − δ)c'(g(g(k)) − (1 − δ)g(k))]`. -/
theorem ex_5_9b_euler [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k : Icc (0 : ℝ) K}
    (hg : (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 ∈ Ioo 0 K) {f' c₀ c₁ : ℝ}
    (hf' : HasDerivAt f f' (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1)
    (hc₀ : HasDerivAt c c₀ ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 -
      (1 - δ) * k.1))
    (hc₁ : HasDerivAt c c₁ ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v)
      (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k)).1 -
      (1 - δ) * (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1)) :
    c₀ = β * (p * f' + (1 - δ) * c₁) :=
  ex_5_9b_foc h hv hg hc₀ (ex_5_9b_envelope h hv hg hf' hc₁)

/-- **Exercise 5.9b (steady state).** At an interior steady state `g(k*) = k*`,
`c'(δk*)(1 − β(1 − δ)) = βpf'(k*)`. -/
theorem ex_5_9b_steady [Nonempty (Icc (0 : ℝ) K)] (h : AdjHyp f c p δ β K)
    {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman h.h43 h.h44 v = v) {k : Icc (0 : ℝ) K}
    (hss : argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k = k) (hk : k.1 ∈ Ioo 0 K)
    {f' c' : ℝ} (hf' : HasDerivAt f f' k.1) (hc' : HasDerivAt c c' (δ * k.1)) :
    c' * (1 - β * (1 - δ)) = β * p * f' := by
  have e : (argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 - (1 - δ) * k.1 = δ * k.1 := by
    rw [hss]; ring
  have hc'' : HasDerivAt c c' ((argmaxFn (fullΓ K) (obj (adjF f c p δ K) β v) k).1 -
      (1 - δ) * k.1) := e ▸ hc'
  have e2 : k.1 - (1 - δ) * k.1 = δ * k.1 := by ring
  have := ex_5_9b_euler h hv (k := k) (by rw [hss]; exact hk) (by rw [hss]; exact hf') hc''
    (by rw [hss, hss, e2]; exact hc')
  linarith

/-! ### Exercise 5.9c: short-run profits -/

/-- `Π(k) = sup_{l ≥ 0} [pF(k, l) − wl]`. -/
noncomputable def profitPi (F : ℝ → ℝ → ℝ) (p w k : ℝ) : ℝ :=
  sSup ((fun l => p * F k l - w * l) '' Ici 0)

variable {F : ℝ → ℝ → ℝ} {w : ℝ}

/-- `Π(k)` equals the profit at a profit-maximizing labour input. -/
theorem profitPi_eq {k l : ℝ} (hl : 0 ≤ l)
    (hmax : ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l) :
    profitPi F p w k = p * F k l - w * l :=
  le_antisymm (csSup_le ⟨_, 0, mem_Ici.2 le_rfl, rfl⟩
    (by rintro _ ⟨l', hl', rfl⟩; exact hmax l' hl'))
    (le_csSup ⟨_, by rintro _ ⟨l', hl', rfl⟩; exact hmax l' hl'⟩ ⟨l, hl, rfl⟩)

/-- **Exercise 5.9c.** Labour demand exists if `F(k, ·)` is continuous with `F(k, l)/l → 0`. -/
theorem labor_demand_exists {k : ℝ} (hw : 0 < w) (hc : ContinuousOn (F k) (Ici 0))
    (hsub : Tendsto (fun l => F k l / l) atTop (𝓝 0)) :
    ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l := by
  have := exists_max_sublinear (g := fun l => p * F k l) (continuousOn_const.mul hc)
    (by simpa [mul_div_assoc] using hsub.const_mul p) hw
  simpa using this

/-- **Exercise 5.9c.** Labour demand is unique if `F(k, ·)` is strictly concave. -/
theorem labor_demand_unique {k l₁ l₂ : ℝ} (hp : 0 < p) (hF : StrictConcaveOn ℝ (Ici 0) (F k))
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hm₁ : ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l₁ - w * l₁)
    (hm₂ : ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l₂ - w * l₂) : l₁ = l₂ := by
  by_contra hne
  have hs := hF.2 (mem_Ici.2 h₁) (mem_Ici.2 h₂) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hs
  have e1 := hm₁ (1 / 2 * l₁ + 1 / 2 * l₂) (by positivity)
  have e2 := hm₂ l₁ h₁
  have e3 := hm₁ l₂ h₂
  nlinarith

/-- **Exercise 5.9c.** `Π(0) = 0` if `F(0, l) = 0` for all `l` and `w ≥ 0`. -/
theorem profitPi_zero (hw : 0 ≤ w) (hF0 : ∀ l, F 0 l = 0) : profitPi F p w 0 = 0 := by
  have := profitPi_eq (F := F) (p := p) (w := w) (k := 0) (l := 0) le_rfl fun l' hl' => by
    simp only [hF0, mul_zero, zero_sub, sub_zero]; nlinarith
  simpa [hF0] using this

/-- **Exercise 5.9c.** `Π` is nondecreasing if `F` is nondecreasing in `k` and `p ≥ 0`. -/
theorem profitPi_mono (hp : 0 ≤ p) (hF : ∀ l, 0 ≤ l → Monotone fun k => F k l)
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l)
    {k k' : ℝ} (hk : 0 ≤ k) (hkk' : k ≤ k') : profitPi F p w k ≤ profitPi F p w k' := by
  obtain ⟨l, hl, hlmax⟩ := hmax k hk
  obtain ⟨l', hl', hl'max⟩ := hmax k' (hk.trans hkk')
  rw [profitPi_eq hl hlmax, profitPi_eq hl' hl'max]
  have := hl'max l hl
  have := mul_le_mul_of_nonneg_left (hF l hl hkk') hp
  linarith

/-- **Exercise 5.9c.** `Π` is concave if `F` is jointly concave and `p ≥ 0`. -/
theorem profitPi_concave (hp : 0 ≤ p) (hF : ConcaveOn ℝ (Set.Ici 0 ×ˢ Set.Ici 0) fun z => F z.1 z.2)
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l) :
    ConcaveOn ℝ (Ici 0) (profitPi F p w) := by
  refine ⟨convex_Ici 0, fun k hk k' hk' s t hs ht hst => ?_⟩
  obtain ⟨l, hl, hlmax⟩ := hmax k hk
  obtain ⟨l', hl', hl'max⟩ := hmax k' hk'
  obtain ⟨lθ, hlθ, hlθmax⟩ := hmax (s • k + t • k') ((convex_Ici 0) hk hk' hs ht hst)
  rw [profitPi_eq hl hlmax, profitPi_eq hl' hl'max, profitPi_eq hlθ hlθmax]
  have hFc := hF.2 (show (k, l) ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk, hl⟩)
    (show (k', l') ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk', hl'⟩) hs ht hst
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hFc ⊢
  have hle := hlθmax (s * l + t * l') (by positivity)
  simp only [smul_eq_mul] at hle
  have := mul_le_mul_of_nonneg_left hFc hp
  nlinarith

/-- **Exercise 5.9c.** `Π` is strictly concave if `F` is jointly strictly concave and `p > 0`. -/
theorem profitPi_strictConcave (hp : 0 < p)
    (hF : StrictConcaveOn ℝ (Set.Ici 0 ×ˢ Set.Ici 0) fun z => F z.1 z.2)
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l) :
    StrictConcaveOn ℝ (Ici 0) (profitPi F p w) := by
  refine ⟨convex_Ici 0, fun k hk k' hk' hne s t hs ht hst => ?_⟩
  obtain ⟨l, hl, hlmax⟩ := hmax k hk
  obtain ⟨l', hl', hl'max⟩ := hmax k' hk'
  obtain ⟨lθ, hlθ, hlθmax⟩ := hmax (s • k + t • k') ((convex_Ici 0) hk hk' hs.le ht.le hst)
  rw [profitPi_eq hl hlmax, profitPi_eq hl' hl'max, profitPi_eq hlθ hlθmax]
  have hne' : (k, l) ≠ (k', l') := fun he => hne (congrArg Prod.fst he)
  have hFc := hF.2 (show (k, l) ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk, hl⟩)
    (show (k', l') ∈ Ici (0 : ℝ) ×ˢ Set.Ici 0 from ⟨hk', hl'⟩) hne' hs ht hst
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hFc ⊢
  have hle := hlθmax (s * l + t * l') (by positivity)
  simp only [smul_eq_mul] at hle
  have := mul_lt_mul_of_pos_left hFc hp
  nlinarith

/-- **Exercise 5.9c (envelope).** If `Π` is concave and `F(·, l₀)` is differentiable at an
interior `k₀`, where `l₀` is the labour demand, then `Π'(k₀) = pF_k(k₀, l₀)`. -/
theorem profitPi_deriv {k₀ l₀ Fk : ℝ} (hk₀ : 0 < k₀) (hl₀ : 0 ≤ l₀)
    (hconc : ConcaveOn ℝ (Ici 0) (profitPi F p w))
    (hmax : ∀ k, 0 ≤ k → ∃ l, 0 ≤ l ∧ ∀ l', 0 ≤ l' → p * F k l' - w * l' ≤ p * F k l - w * l)
    (hl₀max : ∀ l', 0 ≤ l' → p * F k₀ l' - w * l' ≤ p * F k₀ l₀ - w * l₀)
    (hFk : HasDerivAt (fun k => F k l₀) Fk k₀) :
    HasDerivAt (profitPi F p w) (p * Fk) k₀ := by
  set W : ℝ → ℝ := fun k => p * F k l₀ - w * l₀
  have hW : HasDerivAt W (p * Fk) k₀ := (hFk.const_mul p).sub_const _
  have heq : W k₀ = profitPi F p w k₀ := (profitPi_eq hl₀ hl₀max).symm
  have hle : ∀ᶠ k in 𝓝 k₀, W k ≤ profitPi F p w k := by
    filter_upwards [Ici_mem_nhds hk₀] with k hk
    obtain ⟨l, hl, hlmax⟩ := hmax k hk
    rw [profitPi_eq hl hlmax]
    exact hlmax l₀ hl₀
  have := (theorem_4_10 hconc (Ici_mem_nhds hk₀) hW.hasFDerivAt heq hle).hasDerivAt
  simpa using this

end StokeyLucasPrescott.DeterministicApplications
