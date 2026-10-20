import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Euler equations and transversality are sufficient

Stokey and Lucas (1989), Thm 4.15; Ekeland and Scheinkman (1986).

A reduced-form problem chooses a path `x_0, x_1, …` in a real vector space with
`(x_t, x_{t+1}) ∈ G` and `x_0` given, to maximize `∑ β^t F(x_t, x_{t+1})`. Concavity and
differentiability enter only through **supergradients**: linear `p_t`, `q_t` with
`F(a, b) ≤ F(x*_t, x*_{t+1}) + p_t(a − x*_t) + q_t(b − x*_{t+1})` for `(a, b) ∈ G`.

* `finite_horizon_bound`: with the **Euler equation** `q_t + βp_{t+1} = 0`, every feasible path
  satisfies `∑_{t<T} β^tF(x_t, x_{t+1}) + β^Tp_T(x_T)`
  `≤ ∑_{t<T} β^tF(x*_t, x*_{t+1}) + β^Tp_T(x*_T)`.
* `euler_tvc_sufficient`: if moreover `p_t(x_t) ≥ 0` along feasible paths (shadow prices and
  states nonnegative) and the **transversality condition** `β^tp_t(x*_t) → 0` holds, then `x*` is
  optimal in the catching-up sense, and its value is the largest whenever values are finite.

No differentiability, interiority or boundedness is assumed.
-/

open Filter Topology

namespace DPExtensions.EulerTransversality

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The value of the first `T` periods of a path, `∑_{t<T} β^tF(x_t, x_{t+1})`. -/
noncomputable def partialValue (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * F (x t) (x (t + 1))

/-- A path is feasible from `x_0` if it starts there and stays in the graph `G`. -/
def Feasible (G : Set (X × X)) (x0 : X) (x : ℕ → X) : Prop :=
  x 0 = x0 ∧ ∀ t, (x t, x (t + 1)) ∈ G

/-- **Catching-up optimality**: no feasible path is eventually ahead by more than any `ε > 0`. -/
def CatchingUp (G : Set (X × X)) (F : X → X → ℝ) (β : ℝ) (xs : ℕ → X) : Prop :=
  ∀ x, Feasible G (xs 0) x → ∀ ε > 0, ∀ᶠ T in atTop,
    partialValue F β x T ≤ partialValue F β xs T + ε

omit [AddCommGroup X] [Module ℝ X] in
theorem partialValue_succ (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) (T : ℕ) :
    partialValue F β x (T + 1) = partialValue F β x T + β ^ T * F (x T) (x (T + 1)) :=
  Finset.sum_range_succ _ _

/-- **The finite-horizon bound** from supergradients and the Euler equation. -/
theorem finite_horizon_bound {G : Set (X × X)} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    {xs : ℕ → X} {p q : ℕ → X →ₗ[ℝ] ℝ}
    (hsup : ∀ t, ∀ a b, (a, b) ∈ G →
      F a b ≤ F (xs t) (xs (t + 1)) + p t (a - xs t) + q t (b - xs (t + 1)))
    (heuler : ∀ t v, q t v + β * p (t + 1) v = 0) {x : ℕ → X} (hx : Feasible G (xs 0) x)
    (T : ℕ) :
    partialValue F β x T + β ^ T * p T (x T) ≤ partialValue F β xs T + β ^ T * p T (xs T) := by
  induction T with
  | zero => simp [partialValue, hx.1]
  | succ T ih =>
    rw [partialValue_succ, partialValue_succ]
    have h1 := hsup T (x T) (x (T + 1)) (hx.2 T)
    have h2 := heuler T (x (T + 1) - xs (T + 1))
    simp only [map_sub] at h1 h2
    have hb : 0 ≤ β ^ T := pow_nonneg hβ T
    have h3 := mul_le_mul_of_nonneg_left h1 hb
    rw [pow_succ]
    nlinarith

/-- **Euler equation and transversality are sufficient** for catching-up optimality, and for
optimality whenever the values are finite. -/
theorem euler_tvc_sufficient {G : Set (X × X)} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    {xs : ℕ → X} {p q : ℕ → X →ₗ[ℝ] ℝ}
    (hsup : ∀ t, ∀ a b, (a, b) ∈ G →
      F a b ≤ F (xs t) (xs (t + 1)) + p t (a - xs t) + q t (b - xs (t + 1)))
    (heuler : ∀ t v, q t v + β * p (t + 1) v = 0)
    (hnn : ∀ x, Feasible G (xs 0) x → ∀ t, 0 ≤ p t (x t))
    (htvc : Tendsto (fun t => β ^ t * p t (xs t)) atTop (𝓝 0)) :
    CatchingUp G F β xs ∧ ∀ x, Feasible G (xs 0) x →
      (Summable fun t => β ^ t * F (x t) (x (t + 1))) →
      (Summable fun t => β ^ t * F (xs t) (xs (t + 1))) →
      ∑' t, β ^ t * F (x t) (x (t + 1)) ≤ ∑' t, β ^ t * F (xs t) (xs (t + 1)) := by
  have hbound : ∀ x, Feasible G (xs 0) x → ∀ T,
      partialValue F β x T ≤ partialValue F β xs T + β ^ T * p T (xs T) := fun x hx T => by
    have h := finite_horizon_bound hβ hsup heuler hx T
    have := mul_nonneg (pow_nonneg hβ T) (hnn x hx T)
    linarith
  refine ⟨fun x hx ε hε => ?_, fun x hx hs hss => ?_⟩
  · filter_upwards [htvc.eventually (gt_mem_nhds hε)] with T hT
    linarith [hbound x hx T]
  · have h1 : Tendsto (partialValue F β x) atTop (𝓝 (∑' t, β ^ t * F (x t) (x (t + 1)))) :=
      hs.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun T => partialValue F β xs T + β ^ T * p T (xs T)) atTop
        (𝓝 (∑' t, β ^ t * F (xs t) (xs (t + 1)) + 0)) :=
      hss.hasSum.tendsto_sum_nat.add htvc
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 (hbound x hx)

end DPExtensions.EulerTransversality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The one-sector growth model: sufficiency, necessity and failure of the Euler equation alone

Capital `k_t ≥ 0` produces `f(k_t)`, split into consumption `c_t = f(k_t) − k_{t+1} ≥ 0` and next
period's capital; the planner maximizes `∑ β^t u(c_t)`. Utility `u` and technology `f` are
concave and increasing on `[0, ∞)`.

* `concave_tangent`: a concave function lies below its tangent line.
* `growth_sufficient`: along a feasible path, the Euler equation
  `u'(c_t) = βu'(c_{t+1})f'(k_{t+1})` and the transversality condition
  `β^tu'(c_t)f'(k_t)k_t → 0` imply catching-up optimality (Stokey and Lucas, 1989, Thm 4.15).
* `steady_state_optimal`: a steady state with `βf'(k̄) = 1` and `c̄ ≥ 0` is optimal from `k̄`.
* `growth_tvc_necessary`: conversely, for `β < 1`, `f(0) ≥ 0` and an optimal path with finite
  value, the transversality condition `β^tu'(c_t)k_{t+1} → 0` is necessary (Kamihigashi, 2001),
  by comparing the path with its own rescaling `λk_s` after a date `T`.
* `optimal_iff_tvc`: so an Euler path is optimal iff it satisfies the transversality condition.
* `euler_not_sufficient`: with `u(c) = c` and `f(k) = k/β`, the path that never consumes satisfies
  the Euler equation but not the transversality condition, and it is not optimal.
-/

open Filter Topology Set

namespace DPExtensions.EulerTransversality

/-- **A concave function lies below its tangent line.** -/
theorem concave_tangent {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f) {x y f' : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f f' x) : f y ≤ f x + f' * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have h1 := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at h1
    linarith
  · subst h
    simp
  · have h1 := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at h1
    linarith

/-- The one-sector growth model. -/
structure GrowthModel where
  /-- utility -/
  u : ℝ → ℝ
  /-- technology -/
  f : ℝ → ℝ
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  u_concave : ConcaveOn ℝ (Ici 0) u
  u_mono : MonotoneOn u (Ici 0)
  f_concave : ConcaveOn ℝ (Ici 0) f

namespace GrowthModel

variable (M : GrowthModel)

/-- The feasible graph: `k ≥ 0` and `0 ≤ k' ≤ f(k)`. -/
def G : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.2 ≤ M.f x.1}

/-- The return `u(f(k) − k')`. -/
noncomputable def F (k k' : ℝ) : ℝ := M.u (M.f k - k')

/-- Consumption along a capital path. -/
def c (k : ℕ → ℝ) (t : ℕ) : ℝ := M.f (k t) - k (t + 1)

/-- **Euler equation and transversality are sufficient** in the growth model. -/
theorem growth_sufficient {ks : ℕ → ℝ} (hks : ∀ t, (ks t, ks (t + 1)) ∈ M.G)
    {du df : ℕ → ℝ} (hdu : ∀ t, HasDerivAt M.u (du t) (M.c ks t))
    (hdf : ∀ t, HasDerivAt M.f (df t) (ks t)) (hdu0 : ∀ t, 0 ≤ du t) (hdf0 : ∀ t, 0 ≤ df t)
    (heuler : ∀ t, du t = M.β * du (t + 1) * df (t + 1))
    (htvc : Tendsto (fun t => M.β ^ t * (du t * df t * ks t)) atTop (𝓝 0)) :
    CatchingUp M.G M.F M.β ks := by
  refine (euler_tvc_sufficient M.β_pos.le (p := fun t => (du t * df t) • LinearMap.id)
    (q := fun t => (-du t) • LinearMap.id) (fun t a b hab => ?_) (fun t v => ?_)
    (fun x hx t => ?_) ?_).1
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, F]
    obtain ⟨ha, hb, hbf⟩ := hab
    obtain ⟨hk, hk', hkf⟩ := hks t
    simp only at ha hb hbf hk hk' hkf
    have hc : M.f a - b ∈ Ici 0 := mem_Ici.2 (by linarith)
    have hcs : M.c ks t ∈ Ici 0 := mem_Ici.2 (by simp only [c]; linarith)
    have h1 := concave_tangent M.u_concave hcs hc (hdu t)
    have h2 := concave_tangent M.f_concave (mem_Ici.2 hk) (mem_Ici.2 ha) (hdf t)
    simp only [c] at h1
    nlinarith [mul_le_mul_of_nonneg_left h2 (hdu0 t)]
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rw [heuler t]
    ring
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have : 0 ≤ x t := by
      rcases t with _ | t
      · rw [hx.1]
        exact (hks 0).1
      · exact (hx.2 t).2.1
    exact mul_nonneg (mul_nonneg (hdu0 t) (hdf0 t)) this
  · simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] using htvc

/-- **The modified golden rule**: for `β < 1`, a steady state `k̄ ≥ 0` with `βf'(k̄) = 1` and
`c̄ = f(k̄) − k̄ ≥ 0` is optimal from `k̄`. -/
theorem steady_state_optimal (hβ1 : M.β < 1) {kbar du df : ℝ} (hk : 0 ≤ kbar)
    (hc : kbar ≤ M.f kbar) (hdu : HasDerivAt M.u du (M.f kbar - kbar))
    (hdf : HasDerivAt M.f df kbar) (hdu0 : 0 ≤ du) (hdf0 : 0 ≤ df) (hmgr : M.β * df = 1) :
    CatchingUp M.G M.F M.β fun _ => kbar := by
  have hlim : Tendsto (fun t : ℕ => M.β ^ t * (du * df * kbar)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_pos.le hβ1).mul_const (du * df * kbar)
  exact M.growth_sufficient (fun _ => ⟨hk, hk, hc⟩) (du := fun _ => du) (df := fun _ => df)
    (fun _ => hdu) (fun _ => hdf) (fun _ => hdu0) (fun _ => hdf0)
    (fun _ => by rw [mul_assoc, mul_comm du, ← mul_assoc, hmgr, one_mul]) hlim

theorem c_nonneg {ks : ℕ → ℝ} (hks : ∀ t, (ks t, ks (t + 1)) ∈ M.G) (t : ℕ) : 0 ≤ M.c ks t := by
  have := (hks t).2.2
  simp only [c]
  linarith

/-- **Transversality is necessary** (Kamihigashi, 2001): if `β < 1`, `f(0) ≥ 0`, and a feasible
path is catching-up optimal with finite value `∑ β^tu(c_t)`, then `β^tu'(c_t)k_{t+1} → 0`. The
proof compares the path with the one that follows it to `T` and then scales capital by
`1 − h`: concavity bounds the later losses by `h ∑_{s>T} β^s(u(c_s) − u(0))`, and letting
`h → 0` gives `β^Tu'(c_T)k_{T+1} ≤ ∑_{s>T} β^s(u(c_s) − u(0)) → 0`. -/
theorem growth_tvc_necessary (hβ1 : M.β < 1) (hf0 : 0 ≤ M.f 0) {ks : ℕ → ℝ}
    (hks : ∀ t, (ks t, ks (t + 1)) ∈ M.G) (hopt : CatchingUp M.G M.F M.β ks)
    (hsum : Summable fun t => M.β ^ t * M.u (M.c ks t)) {du : ℕ → ℝ}
    (hdu : ∀ t, HasDerivAt M.u (du t) (M.c ks t)) (hdu0 : ∀ t, 0 ≤ du t) :
    Tendsto (fun t => M.β ^ t * du t * ks (t + 1)) atTop (𝓝 0) := by
  have hβ0 := M.β_pos.le
  set g : ℕ → ℝ := fun s => M.β ^ s * (M.u (M.c ks s) - M.u 0) with hgdef
  have hg0 : ∀ s, 0 ≤ g s := fun s =>
    mul_nonneg (pow_nonneg hβ0 s) (sub_nonneg.2 (M.u_mono (mem_Ici.2 le_rfl)
      (mem_Ici.2 (M.c_nonneg hks s)) (M.c_nonneg hks s)))
  have hgsum : Summable g := by
    have h := hsum.sub ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (M.u 0))
    refine h.congr fun s => ?_
    simp only [hgdef]
    ring
  set R : ℕ → ℝ := fun T => ∑' j, g (j + (T + 1)) with hRdef
  have hR : Tendsto R atTop (𝓝 0) := (tendsto_sum_nat_add g).comp (tendsto_add_atTop_nat 1)
  have hk0 : ∀ t, 0 ≤ ks t := fun t => (hks t).1
  -- the key bound at each date
  have hkey : ∀ T, M.β ^ T * du T * ks (T + 1) ≤ R T := by
    intro T
    set k := ks (T + 1)
    set c0 := M.c ks T
    have hβT : 0 < M.β ^ T := pow_pos M.β_pos T
    -- the comparison with the rescaled path, for `h ∈ (0, 1]`
    have hcomp : ∀ h : ℝ, 0 < h → h ≤ 1 →
        M.β ^ T * (M.u (c0 + h * k) - M.u c0) ≤ h * R T := by
      intro h hh0 hh1
      set y : ℕ → ℝ := fun s => if s ≤ T then ks s else (1 - h) * ks s with hydef
      have hy0 : y 0 = ks 0 := by simp [hydef]
      have hylate : ∀ s, T < s → y s = (1 - h) * ks s := fun s hs => by
        simp [hydef, show ¬ s ≤ T by omega]
      have hyearly : ∀ s, s ≤ T → y s = ks s := fun s hs => by simp [hydef, hs]
      have hscale : ∀ s, (1 - h) * M.f (ks s) ≤ M.f ((1 - h) * ks s) := by
        intro s
        have := M.f_concave.2 (mem_Ici.2 (hk0 s)) (mem_Ici.2 (le_refl (0 : ℝ)))
          (by linarith : (0 : ℝ) ≤ 1 - h) hh0.le (by ring : 1 - h + h = 1)
        simp only [smul_eq_mul, mul_zero, add_zero] at this
        nlinarith
      have hfeas : Feasible M.G (ks 0) y := by
        refine ⟨hy0, fun s => ?_⟩
        rcases lt_trichotomy s T with hs | hs | hs
        · rw [hyearly s hs.le, hyearly (s + 1) hs]
          exact hks s
        · subst hs
          rw [hyearly s le_rfl, hylate (s + 1) (by omega)]
          obtain ⟨h1, h2, h3⟩ := hks s
          exact ⟨h1, mul_nonneg (by linarith) h2, by nlinarith⟩
        · rw [hylate s hs, hylate (s + 1) (by omega)]
          obtain ⟨h1, h2, h3⟩ := hks s
          refine ⟨mul_nonneg (by linarith) h1, mul_nonneg (by linarith) h2, ?_⟩
          exact (mul_le_mul_of_nonneg_left h3 (by linarith)).trans (hscale s)
      -- later periods lose at most `h g_s`
      have hlate : ∀ s, T < s →
          -(h * g s) ≤ M.β ^ s * (M.F (y s) (y (s + 1)) - M.F (ks s) (ks (s + 1))) := by
        intro s hs
        rw [hylate s hs, hylate (s + 1) (by omega)]
        have hcs := M.c_nonneg hks s
        have hc1 : (1 - h) * M.c ks s ≤ M.f ((1 - h) * ks s) - (1 - h) * ks (s + 1) := by
          have := hscale s
          simp only [c]
          nlinarith
        have hmono := M.u_mono (mem_Ici.2 (mul_nonneg (by linarith) hcs))
          (mem_Ici.2 ((mul_nonneg (by linarith) hcs).trans hc1)) hc1
        have hconc := M.u_concave.2 (mem_Ici.2 hcs) (mem_Ici.2 (le_refl (0 : ℝ)))
          (by linarith : (0 : ℝ) ≤ 1 - h) hh0.le (by ring : 1 - h + h = 1)
        simp only [smul_eq_mul, mul_zero, add_zero] at hconc
        have hb := pow_nonneg hβ0 s
        have h1 : -(h * (M.u (M.c ks s) - M.u 0)) ≤
            M.u (M.f ((1 - h) * ks s) - (1 - h) * ks (s + 1)) - M.u (M.c ks s) := by linarith
        have h2 := mul_le_mul_of_nonneg_left h1 hb
        change -(h * (M.β ^ s * (M.u (M.c ks s) - M.u 0))) ≤
          M.β ^ s * (M.u (M.f ((1 - h) * ks s) - (1 - h) * ks (s + 1)) - M.u (M.c ks s))
        linarith
      -- the gap after `j` further periods
      have hPVT : partialValue M.F M.β y T = partialValue M.F M.β ks T :=
        Finset.sum_congr rfl fun s hs => by
          rw [hyearly s (by simp at hs; omega), hyearly (s + 1) (by simp at hs; omega)]
      have hgap : ∀ j, M.β ^ T * (M.u (c0 + h * k) - M.u c0) -
          h * ∑ i ∈ Finset.range j, g (i + (T + 1)) ≤
          partialValue M.F M.β y (T + 1 + j) - partialValue M.F M.β ks (T + 1 + j) := by
        intro j
        induction j with
        | zero =>
          simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, add_zero]
          rw [partialValue_succ, partialValue_succ, hPVT, hyearly T le_rfl,
            hylate (T + 1) (by omega)]
          simp only [F]
          have e : M.f (ks T) - (1 - h) * ks (T + 1) = c0 + h * k := by
            simp only [c0, k, c]
            ring
          rw [e]
          simp only [c0, c]
          linarith
        | succ j ih =>
          rw [Finset.sum_range_succ, show T + 1 + (j + 1) = (T + 1 + j) + 1 by ring,
            partialValue_succ, partialValue_succ]
          have := hlate (T + 1 + j) (by omega)
          rw [show j + (T + 1) = T + 1 + j by ring]
          nlinarith
      have hsumR : ∀ j, ∑ i ∈ Finset.range j, g (i + (T + 1)) ≤ R T := fun j =>
        ((summable_nat_add_iff (T + 1)).2 hgsum).sum_le_tsum _ fun i _ => hg0 _
      by_contra hcon
      push Not at hcon
      set δ := M.β ^ T * (M.u (c0 + h * k) - M.u c0) - h * R T
      have hδ : 0 < δ := by linarith
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hopt y hfeas (δ / 2) (half_pos hδ))
      have h1 := hN (T + 1 + N) (by omega)
      have h2 := hgap N
      have h3 := mul_le_mul_of_nonneg_left (hsumR N) hh0.le
      linarith
    -- let `h → 0`
    have hlin : HasDerivAt (fun h : ℝ => c0 + h * k) k 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add c0
    have hd : HasDerivAt (fun h : ℝ => M.u (c0 + h * k)) (du T * k) 0 :=
      (hdu T).comp_of_eq 0 hlin (by simp [c0])
    have hslope := hd.tendsto_slope_zero_right
    have hle : du T * k ≤ R T / M.β ^ T := by
      refine le_of_tendsto hslope ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with h hh
      obtain ⟨hh0, hh1⟩ := hh
      have := hcomp h hh0 hh1.le
      simp only [zero_add, zero_mul, add_zero, smul_eq_mul]
      rw [le_div_iff₀ hβT, inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ hh0]
      linarith
    rw [le_div_iff₀ hβT] at hle
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR (fun t => ?_) hkey
  exact mul_nonneg (mul_nonneg (pow_nonneg hβ0 t) (hdu0 t)) (hk0 (t + 1))

/-- **Optimality of an Euler path is equivalent to transversality**: for `β < 1`, `f(0) ≥ 0`, a
feasible path with finite value satisfying the Euler equation is catching-up optimal iff
`β^tu'(c_t)f'(k_t)k_t → 0`. -/
theorem optimal_iff_tvc (hβ1 : M.β < 1) (hf0 : 0 ≤ M.f 0) {ks : ℕ → ℝ}
    (hks : ∀ t, (ks t, ks (t + 1)) ∈ M.G) (hsum : Summable fun t => M.β ^ t * M.u (M.c ks t))
    {du df : ℕ → ℝ} (hdu : ∀ t, HasDerivAt M.u (du t) (M.c ks t))
    (hdf : ∀ t, HasDerivAt M.f (df t) (ks t)) (hdu0 : ∀ t, 0 ≤ du t) (hdf0 : ∀ t, 0 ≤ df t)
    (heuler : ∀ t, du t = M.β * du (t + 1) * df (t + 1)) :
    CatchingUp M.G M.F M.β ks ↔
      Tendsto (fun t => M.β ^ t * (du t * df t * ks t)) atTop (𝓝 0) := by
  refine ⟨fun hopt => ?_, M.growth_sufficient hks hdu hdf hdu0 hdf0 heuler⟩
  have h := M.growth_tvc_necessary hβ1 hf0 hks hopt hsum hdu hdu0
  rw [← tendsto_add_atTop_iff_nat 1]
  refine h.congr fun t => ?_
  rw [heuler t, pow_succ]
  ring

end GrowthModel

end DPExtensions.EulerTransversality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Euler equation alone is not sufficient

With linear utility `u(c) = c` and linear technology `f(k) = k/β`, every interior path satisfies
the Euler equation `u'(c_t) = βu'(c_{t+1})f'(k_{t+1})`, since `1 = β · 1 · (1/β)`. The path that
never consumes, `k_t = k₀/βᵗ`, satisfies it but violates the transversality condition
(`β^tu'(c_t)f'(k_t)k_t = k₀/β` for every `t`), and it is not optimal: consuming everything at
date `0` yields `k₀/β > 0`. The transversality condition cannot be dropped from
`growth_sufficient`.
-/

open Filter Topology Set

namespace DPExtensions.EulerTransversality

/-- The growth model with `u(c) = c` and `f(k) = k/β`. -/
noncomputable def linearModel (β : ℝ) (hβ : 0 < β) : GrowthModel where
  u := id
  f := fun k => k / β
  β := β
  β_pos := hβ
  u_concave := concaveOn_id (convex_Ici 0)
  u_mono := monotone_id.monotoneOn _
  f_concave := ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq (by
    simp only [smul_eq_mul]
    ring)⟩

/-- The path that never consumes. -/
noncomputable def hoarding (β k₀ : ℝ) (t : ℕ) : ℝ := k₀ / β ^ t

/-- **Euler without transversality is not sufficient.** -/
theorem euler_not_sufficient {β k₀ : ℝ} (hβ : 0 < β) (hk₀ : 0 < k₀) :
    (∀ t, (hoarding β k₀ t, hoarding β k₀ (t + 1)) ∈ (linearModel β hβ).G) ∧
    (∀ t, HasDerivAt (linearModel β hβ).u 1 ((linearModel β hβ).c (hoarding β k₀) t)) ∧
    (∀ t, HasDerivAt (linearModel β hβ).f (1 / β) (hoarding β k₀ t)) ∧
    (1 : ℝ) = β * 1 * (1 / β) ∧
    ¬ Tendsto (fun t => β ^ t * (1 * (1 / β) * hoarding β k₀ t)) atTop (𝓝 0) ∧
    ¬ CatchingUp (linearModel β hβ).G (linearModel β hβ).F β (hoarding β k₀) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have hnext : ∀ t, hoarding β k₀ (t + 1) = hoarding β k₀ t / β := fun t => by
    simp only [hoarding, pow_succ]
    field_simp
  have hpos : ∀ t, 0 < hoarding β k₀ t := fun t => div_pos hk₀ (pow_pos hβ t)
  refine ⟨fun t => ⟨(hpos t).le, (hpos (t + 1)).le, ?_⟩, fun t => hasDerivAt_id _,
    fun t => (hasDerivAt_id' _).div_const β, by field_simp,
    fun h => ?_, fun h => ?_⟩
  · simp only [linearModel, hnext t]
    exact le_rfl
  · have hc : (fun t => β ^ t * (1 * (1 / β) * hoarding β k₀ t)) = fun _ => k₀ / β := by
      funext t
      simp only [hoarding]
      field_simp
    rw [hc] at h
    have := tendsto_nhds_unique tendsto_const_nhds h
    exact (div_pos hk₀ hβ).ne' this
  · -- consume everything at date `0`
    set x : ℕ → ℝ := fun t => if t = 0 then k₀ else 0 with hxdef
    have hfeas : Feasible (linearModel β hβ).G (hoarding β k₀ 0) x := by
      refine ⟨by simp [hxdef, hoarding], fun t => ?_⟩
      rcases t with _ | t
      · simp only [hxdef, linearModel, GrowthModel.G]
        simp only [↓reduceIte, Nat.add_one_ne_zero]
        exact ⟨hk₀.le, le_rfl, div_nonneg hk₀.le hβ.le⟩
      · simp only [hxdef, linearModel, GrowthModel.G, Nat.add_one_ne_zero, ↓reduceIte]
        exact ⟨le_rfl, le_rfl, by simp⟩
    have hPVx : ∀ T, partialValue (linearModel β hβ).F β x (T + 1) = k₀ / β := by
      intro T
      induction T with
      | zero =>
        simp [partialValue, GrowthModel.F, linearModel, hxdef]
      | succ T ih =>
        rw [partialValue_succ, ih]
        simp [GrowthModel.F, linearModel, hxdef]
    have hPVs : ∀ T, partialValue (linearModel β hβ).F β (hoarding β k₀) T = 0 := by
      intro T
      refine Finset.sum_eq_zero fun t _ => ?_
      simp only [GrowthModel.F, linearModel, id, hnext t, sub_self, mul_zero]
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h x hfeas (k₀ / β / 2) (by positivity))
    have := hN (N + 1) (by omega)
    rw [hPVx, hPVs] at this
    have : 0 < k₀ / β := div_pos hk₀ hβ
    linarith

end DPExtensions.EulerTransversality

set_option linter.style.longLine false
#print axioms DPExtensions.EulerTransversality.partialValue
#print axioms DPExtensions.EulerTransversality.Feasible
#print axioms DPExtensions.EulerTransversality.CatchingUp
#print axioms DPExtensions.EulerTransversality.partialValue_succ
#print axioms DPExtensions.EulerTransversality.finite_horizon_bound
#print axioms DPExtensions.EulerTransversality.euler_tvc_sufficient
#print axioms DPExtensions.EulerTransversality.concave_tangent
#print axioms DPExtensions.EulerTransversality.GrowthModel
#print axioms DPExtensions.EulerTransversality.GrowthModel.mk
#print axioms DPExtensions.EulerTransversality.GrowthModel.u
#print axioms DPExtensions.EulerTransversality.GrowthModel.f
#print axioms DPExtensions.EulerTransversality.GrowthModel.β
#print axioms DPExtensions.EulerTransversality.GrowthModel.β_pos
#print axioms DPExtensions.EulerTransversality.GrowthModel.u_concave
#print axioms DPExtensions.EulerTransversality.GrowthModel.u_mono
#print axioms DPExtensions.EulerTransversality.GrowthModel.f_concave
#print axioms DPExtensions.EulerTransversality.GrowthModel.G
#print axioms DPExtensions.EulerTransversality.GrowthModel.F
#print axioms DPExtensions.EulerTransversality.GrowthModel.c
#print axioms DPExtensions.EulerTransversality.GrowthModel.growth_sufficient
#print axioms DPExtensions.EulerTransversality.GrowthModel.steady_state_optimal
#print axioms DPExtensions.EulerTransversality.GrowthModel.c_nonneg
#print axioms DPExtensions.EulerTransversality.GrowthModel.growth_tvc_necessary
#print axioms DPExtensions.EulerTransversality.GrowthModel.optimal_iff_tvc
#print axioms DPExtensions.EulerTransversality.linearModel
#print axioms DPExtensions.EulerTransversality.hoarding
#print axioms DPExtensions.EulerTransversality.euler_not_sufficient
