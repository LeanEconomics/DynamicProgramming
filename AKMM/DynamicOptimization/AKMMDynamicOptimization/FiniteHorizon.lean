/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.SequenceProblems
import DeterministicDP.EulerEquations
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Finite horizon: Result 1 and the finite-horizon neoclassical growth model

AKMM, §4.2.2–4.2.3, pp. 100–102. States are real, `Γ(x) = [x̲, γ(x)]`, and `F` has derivative
`D_t` at `(x*_t, x*_{t+1})` with partial derivatives `F₁ = D_t(1, 0)`, `F₂ = D_t(0, 1)`.

* `finite_telescope`: under the Euler equation (i) for `t < T`, the first-order terms of
  `Σ_{t≤T} βᵗ[F(x*_t, x*_{t+1}) − F(x_t, x_{t+1})]` telescope to `βᵀF₂(T)(x*_{T+1} − x_{T+1})`.
* **Result 1** (`result_1`): a concave `F` with the Euler equation (i) for `t < T` and the
  terminal condition (ii) `x*_{T+1} = x̲` gives a maximizer. The book's hypotheses that `F` is
  increasing in its first argument and that `x*` is interior are not needed; `F` decreasing in
  its second argument enters only through `F₂(T) ≤ 0` (`result_1_of_antitone`).
* The NGM return `u(f(k) + (1 − δ)k − k')` is concave in `(k, k')`, strictly when `u` and `f`
  are (fn. 4 and fn. 16; `ngm_return_concave`, `ngm_return_strictConcave`), with partial
  derivatives `u'(c)(f'(k) + 1 − δ)` and `−u'(c)` (`ngm_hasFDerivAt`).
* (P3): at a maximum `k_{T+1} = 0` ((4.8)–(4.9), `ngm_terminal_zero`); at an interior maximum the
  Euler equation (4.10) holds (`eq_4_10`, Fermat's theorem in place of the Lagrangian (4.7)); the
  Euler equation with `k_{T+1} = 0` is sufficient (`ngm_finite_sufficient`), and the solution is
  unique (`finite_unique_max`, `ngm_finite_unique`).

The tangent-plane inequality `concave_le_fderiv` is imported from SLP `DeterministicDP`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDP

/-- A linear map on `ℝ × ℝ` in terms of its partial derivatives:
`D(a, b) = aD(1, 0) + bD(0, 1)`. -/
theorem finite_fderiv_apply (D : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    D (a, b) = a * D (1, 0) + b * D (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The telescoping step** (AKMM, App. 4.A.3 adapted to a finite horizon). If `d₀ = 0` and the
Euler equation `F₂(t) + βF₁(t + 1) = 0` holds for `t < T`, then for `n ≤ T`
`Σ_{t≤n} βᵗD_t(d_t, d_{t+1}) = βⁿd_{n+1}F₂(n)`. -/
theorem finite_telescope (D : ℕ → ℝ × ℝ →L[ℝ] ℝ) {β : ℝ} (d : ℕ → ℝ) (hd0 : d 0 = 0) {T : ℕ}
    (heuler : ∀ t < T, D t (0, 1) + β * D (t + 1) (1, 0) = 0) :
    ∀ n ≤ T, ∑ t ∈ Finset.range (n + 1), β ^ t * D t (d t, d (t + 1)) =
      β ^ n * (d (n + 1) * D n (0, 1)) := by
  intro n hn
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, hd0]
    rw [finite_fderiv_apply]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega), finite_fderiv_apply (D (n + 1))]
    have he := heuler n (by omega)
    rw [pow_succ]
    linear_combination (β ^ n * d (n + 1)) * he

/-- **Result 1** (AKMM, p. 100). Let `F` be concave on a convex set `A` containing every pair
`(x_t, x_{t+1})` of the plans considered, with derivative `D_t` at `(x*_t, x*_{t+1})`. If `x*` is
feasible for `Γ(x) = [x̲, γ(x)]`, satisfies the Euler equation (i)
`F₂(x*_t, x*_{t+1}) + βF₁(x*_{t+1}, x*_{t+2}) = 0` for `t < T` and the terminal condition (ii)
`x*_{T+1} = x̲`, and `F₂(x*_T, x*_{T+1}) ≤ 0`, then `x*` maximizes the objective. -/
theorem result_1 {F : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)} (hA : ConcaveOn ℝ A F) {β : ℝ} (hβ : 0 ≤ β)
    {lo : ℝ} {γ : ℝ → ℝ} {x0 : ℝ} {T : ℕ} {xs : ℕ → ℝ}
    (hxs : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T xs) (hxsA : ∀ t ≤ T, (xs t, xs (t + 1)) ∈ A)
    (D : ℕ → ℝ × ℝ →L[ℝ] ℝ) (hD : ∀ t ≤ T, HasFDerivAt F (D t) (xs t, xs (t + 1)))
    (heuler : ∀ t < T, D t (0, 1) + β * D (t + 1) (1, 0) = 0) (hterm : xs (T + 1) = lo)
    (hF2 : D T (0, 1) ≤ 0) {x : ℕ → ℝ} (hx : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T x)
    (hxA : ∀ t ≤ T, (x t, x (t + 1)) ∈ A) :
    objective (fun a b => F (a, b)) β x T ≤ objective (fun a b => F (a, b)) β xs T := by
  set d : ℕ → ℝ := fun t => xs t - x t
  have hd0 : d 0 = 0 := by simp [d, hxs.1, hx.1]
  have htel := finite_telescope D d hd0 heuler T le_rfl
  have hterm' : ∀ t ∈ Finset.range (T + 1), β ^ t * F (x t, x (t + 1)) ≤
      β ^ t * F (xs t, xs (t + 1)) - β ^ t * D t (d t, d (t + 1)) := fun t ht => by
    have htT : t ≤ T := by have := Finset.mem_range.1 ht; omega
    have h := concave_le_fderiv hA (hxsA t htT) (hxA t htT) (hD t htT)
    have e : D t ((x t, x (t + 1)) - (xs t, xs (t + 1))) = -D t (d t, d (t + 1)) := by
      rw [← map_neg]; congr 1; ext <;> simp [d]
    rw [e] at h
    have := mul_le_mul_of_nonneg_left h (pow_nonneg hβ t)
    linarith
  have hsum := Finset.sum_le_sum hterm'
  rw [Finset.sum_sub_distrib, htel] at hsum
  have hdT : d (T + 1) ≤ 0 := by
    have := (hx.2 T le_rfl).1
    simp only [d, hterm]; linarith
  have : 0 ≤ β ^ T * (d (T + 1) * D T (0, 1)) :=
    mul_nonneg (pow_nonneg hβ T) (mul_nonneg_of_nonpos_of_nonpos hdT hF2)
  unfold objective
  linarith

/-- AKMM, p. 100: if `F` is decreasing in its second argument then `F₂ ≤ 0`, so the last
hypothesis of `result_1` follows from the book's monotonicity assumption. -/
theorem result_1_F2_nonpos {F : ℝ × ℝ → ℝ} {a b : ℝ} {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt F D (a, b)) (hdec : Antitone fun y => F (a, y)) : D (0, 1) ≤ 0 := by
  have hline : HasDerivAt (fun y : ℝ => ((a, y) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have hcomp : HasDerivAt (fun y => F (a, y)) (D (0, 1)) b := hD.comp_hasDerivAt b hline
  rw [← hcomp.deriv]
  exact hdec.deriv_nonpos

/-- **Result 1 with the book's monotonicity hypothesis** (AKMM, p. 100): `F` decreasing in its
second argument replaces `F₂(T) ≤ 0`. -/
theorem result_1_of_antitone {F : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)} (hA : ConcaveOn ℝ A F) {β : ℝ}
    (hβ : 0 ≤ β) (hdec : ∀ a, Antitone fun y => F (a, y)) {lo : ℝ} {γ : ℝ → ℝ} {x0 : ℝ} {T : ℕ}
    {xs : ℕ → ℝ} (hxs : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T xs)
    (hxsA : ∀ t ≤ T, (xs t, xs (t + 1)) ∈ A)
    (D : ℕ → ℝ × ℝ →L[ℝ] ℝ) (hD : ∀ t ≤ T, HasFDerivAt F (D t) (xs t, xs (t + 1)))
    (heuler : ∀ t < T, D t (0, 1) + β * D (t + 1) (1, 0) = 0) (hterm : xs (T + 1) = lo)
    {x : ℕ → ℝ} (hx : FeasibleT (fun x => Set.Icc lo (γ x)) x0 T x)
    (hxA : ∀ t ≤ T, (x t, x (t + 1)) ∈ A) :
    objective (fun a b => F (a, b)) β x T ≤ objective (fun a b => F (a, b)) β xs T :=
  result_1 hA hβ hxs hxsA D hD heuler hterm (result_1_F2_nonpos (hD T le_rfl) (hdec _)) hx hxA

/-- **AKMM, fn. 4 (p. 101) and fn. 16 (p. 124): the NGM return is jointly concave.** If `u` is
concave and nondecreasing on a convex upward-closed set `S` (`[0, ∞)` or `(0, ∞)`) and
`h(k) = f(k) + (1 − δ)k` is concave on `[0, ∞)`, then `(k, k') ↦ u(h(k) − k')` is concave on
`{(k, k') : k ≥ 0, h(k) − k' ∈ S}`, which is convex. No Hessian is needed. -/
theorem ngm_return_concave {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : ConcaveOn ℝ S u) (hmono : MonotoneOn u S)
    (hh : ConcaveOn ℝ (Set.Ici 0) h) :
    ConcaveOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ h p.1 - p.2 ∈ S} fun p => u (h p.1 - p.2) := by
  have hkey : ∀ p q : ℝ × ℝ, 0 ≤ p.1 → 0 ≤ q.1 → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * (h p.1 - p.2) + b * (h q.1 - q.2) ≤ h (a * p.1 + b * q.1) - (a * p.2 + b * q.2) := by
    intro p q hp hq a b ha hb hab
    have := hh.2 (Set.mem_Ici.2 hp) (Set.mem_Ici.2 hq) ha hb hab
    simp only [smul_eq_mul] at this
    linarith
  have hconv : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ h p.1 - p.2 ∈ S} := by
    intro p hp q hq a b ha hb hab
    refine ⟨by simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; nlinarith [hp.1, hq.1], ?_⟩
    have hin : a * (h p.1 - p.2) + b * (h q.1 - q.2) ∈ S := by
      have := hS hp.2 hq.2 ha hb hab
      simpa only [smul_eq_mul] using this
    refine hup _ hin _ ?_
    simpa only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      using hkey p q hp.1 hq.1 a b ha hb hab
  refine ⟨hconv, fun p hp q hq a b ha hb hab => ?_⟩
  have hin : a * (h p.1 - p.2) + b * (h q.1 - q.2) ∈ S := by
    have := hS hp.2 hq.2 ha hb hab
    simpa only [smul_eq_mul] using this
  have hmid := (hconv hp hq ha hb hab).2
  have h1 := hu.2 hp.2 hq.2 ha hb hab
  simp only [smul_eq_mul] at h1 ⊢
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hmid ⊢
  exact h1.trans (hmono hin hmid (hkey p q hp.1 hq.1 a b ha hb hab))

/-- **The NGM return is strictly concave** when `u` is strictly concave and strictly increasing
on `S` and `h` is strictly concave (AKMM, fn. 4, p. 101). -/
theorem ngm_return_strictConcave {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : StrictConcaveOn ℝ S u) (hmono : StrictMonoOn u S)
    (hh : StrictConcaveOn ℝ (Set.Ici 0) h) :
    StrictConcaveOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ h p.1 - p.2 ∈ S} fun p => u (h p.1 - p.2) := by
  have hc := ngm_return_concave hS hup hu.concaveOn hmono.monotoneOn hh.concaveOn
  refine ⟨hc.1, fun p hp q hq hpq a b ha hb hab => ?_⟩
  have hin : a * (h p.1 - p.2) + b * (h q.1 - q.2) ∈ S := by
    have := hS hp.2 hq.2 ha.le hb.le hab
    simpa only [smul_eq_mul] using this
  have hmid := (hc.1 hp hq ha.le hb.le hab).2
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hmid ⊢
  have hweak := hh.concaveOn.2 (Set.mem_Ici.2 hp.1) (Set.mem_Ici.2 hq.1) ha.le hb.le hab
  simp only [smul_eq_mul] at hweak
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
    have hne : h p.1 - p.2 ≠ h q.1 - q.2 := by rw [h1]; intro h; exact h2 (by linarith)
    have hs := hu.2 hp.2 hq.2 hne ha hb hab
    simp only [smul_eq_mul] at hs
    refine hs.trans_le (hmono.monotoneOn hin hmid ?_)
    linarith
  · have hstrict := hh.2 (Set.mem_Ici.2 hp.1) (Set.mem_Ici.2 hq.1) h1 ha hb hab
    simp only [smul_eq_mul] at hstrict
    have hw := hu.concaveOn.2 hp.2 hq.2 ha.le hb.le hab
    simp only [smul_eq_mul] at hw
    exact hw.trans_lt (hmono hin hmid (by linarith))

/-- AKMM, pp. 101, 110: the partial derivatives of the NGM return `u(h(k) − k')`, with
`h(k) = f(k) + (1 − δ)k`, are `F₁ = u'(c)h'(k)` and `F₂ = −u'(c)`. -/
theorem ngm_hasFDerivAt {u h : ℝ → ℝ} {k k' du dh : ℝ} (hu : HasDerivAt u du (h k - k'))
    (hh : HasDerivAt h dh k) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => u (h p.1 - p.2)) D (k, k') ∧
      D (1, 0) = du * dh ∧ D (0, 1) = -du := by
  have hin := (hh.hasFDerivAt.comp (k, k')
    (hasFDerivAt_fst (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ)))).sub
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ)))
  have hout := hu.hasFDerivAt.comp (k, k') hin
  refine ⟨_, hout, ?_, ?_⟩ <;> simp [mul_comm]

/-- AKMM, (P3), p. 101: a capital plan feasible from `k₀` up to `T`, with
`0 ≤ k_{t+1} ≤ h(k_t) = f(k_t) + (1 − δ)k_t`. -/
abbrev NGMFeasible (h : ℝ → ℝ) (k0 : ℝ) (T : ℕ) (k : ℕ → ℝ) : Prop :=
  FeasibleT (fun k => Set.Icc 0 (h k)) k0 T k

/-- The objective of (P3), `Σ_{t≤T} βᵗu(h(k_t) − k_{t+1})`. -/
noncomputable abbrev ngmObjective (u h : ℝ → ℝ) (β : ℝ) (k : ℕ → ℝ) (T : ℕ) : ℝ :=
  objective (fun a b => u (h a - b)) β k T

/-- **AKMM, (4.8)–(4.9), p. 102: the terminal condition `k_{T+1} = 0`.** If `u` is strictly
increasing on `[0, ∞)` and `β > 0`, a maximizer of (P3) leaves no capital after `T`. -/
theorem ngm_terminal_zero {u h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hu : StrictMonoOn u (Set.Ici 0))
    {k0 : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hks : NGMFeasible h k0 T ks)
    (hmax : ∀ k, NGMFeasible h k0 T k → ngmObjective u h β k T ≤ ngmObjective u h β ks T) :
    ks (T + 1) = 0 := by
  by_contra hne
  have hT := hks.2 T le_rfl
  have hpos : 0 < ks (T + 1) := lt_of_le_of_ne hT.1 (Ne.symm hne)
  have hz : NGMFeasible h k0 T (Function.update ks (T + 1) 0) := by
    refine ⟨by rw [Function.update_of_ne (by omega)]; exact hks.1, fun t ht => ?_⟩
    rcases eq_or_lt_of_le ht with rfl | hlt
    · rw [Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega)]
      exact ⟨le_rfl, hT.1.trans hT.2⟩
    · rw [Function.update_of_ne (show t + 1 ≠ T + 1 by omega),
        Function.update_of_ne (show t ≠ T + 1 by omega)]
      exact hks.2 t ht
  have h1 := hmax _ hz
  simp only [ngmObjective, objective] at h1
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h1
  have hsame : ∑ t ∈ Finset.range T, β ^ t * u (h (Function.update ks (T + 1) 0 t) -
      Function.update ks (T + 1) 0 (t + 1)) =
      ∑ t ∈ Finset.range T, β ^ t * u (h (ks t) - ks (t + 1)) :=
    Finset.sum_congr rfl fun t ht => by
      have := Finset.mem_range.1 ht
      rw [Function.update_of_ne (show t ≠ T + 1 by omega),
        Function.update_of_ne (show t + 1 ≠ T + 1 by omega)]
  rw [hsame, Function.update_self, Function.update_of_ne (show T ≠ T + 1 by omega)] at h1
  have hlt : u (h (ks T) - ks (T + 1)) < u (h (ks T) - 0) :=
    hu (Set.mem_Ici.2 (by linarith [hT.2])) (Set.mem_Ici.2 (by linarith [hT.2])) (by linarith)
  have := mul_lt_mul_of_pos_left hlt (pow_pos hβ T)
  linarith

/-- **AKMM, (4.10), p. 102: the Euler equation at an interior maximum.** If `k*` maximizes (P3)
and, at some `t < T`, `k*_{t+1} > 0` and consumption is positive at `t` and `t + 1`, then
`u'(c_t) = βu'(c_{t+1})(f'(k_{t+1}) + 1 − δ)` (here `h' = f' + 1 − δ`). This is (4.7) with
`μ_t = 0`, proved by Fermat's theorem in the direction `k_{t+1}`. -/
theorem eq_4_10 {u u' h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) {k0 : ℝ} {T : ℕ} {ks : ℕ → ℝ}
    (hks : NGMFeasible h k0 T ks)
    (hmax : ∀ k, NGMFeasible h k0 T k → ngmObjective u h β k T ≤ ngmObjective u h β ks T)
    {t : ℕ} (ht : t < T) (hk : 0 < ks (t + 1)) (hc0 : ks (t + 1) < h (ks t))
    (hc1 : ks (t + 2) < h (ks (t + 1)))
    (hu0 : HasDerivAt u (u' (h (ks t) - ks (t + 1))) (h (ks t) - ks (t + 1)))
    (hu1 : HasDerivAt u (u' (h (ks (t + 1)) - ks (t + 2))) (h (ks (t + 1)) - ks (t + 2)))
    {dh : ℝ} (hh : HasDerivAt h dh (ks (t + 1))) :
    u' (h (ks t) - ks (t + 1)) = β * u' (h (ks (t + 1)) - ks (t + 2)) * dh := by
  set y0 := ks (t + 1)
  set g : ℝ → ℝ := fun y => β ^ t * u (h (ks t) - y) + β ^ (t + 1) * u (h y - ks (t + 2))
  have hobj : ∀ y, ngmObjective u h β (Function.update ks (t + 1) y) T =
      ngmObjective u h β ks T + (g y - g y0) := by
    intro y
    simp only [ngmObjective, objective]
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_add_of_mem t (t + 1) (Finset.mem_range.2 (by omega))
      (Finset.mem_range.2 (by omega)) (by omega)]
    · rw [Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self,
        Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
      simp only [g, y0]
      ring
    · intro c _ hc
      rw [Function.update_of_ne (show c ≠ t + 1 from hc.2),
        Function.update_of_ne (show c + 1 ≠ t + 1 by omega), sub_self]
  have hloc : IsLocalMax g y0 := by
    have e1 : ∀ᶠ y in 𝓝 y0, 0 < y := lt_mem_nhds hk
    have e2 : ∀ᶠ y in 𝓝 y0, y < h (ks t) := gt_mem_nhds hc0
    have e3 : ∀ᶠ y in 𝓝 y0, ks (t + 2) < h y := hh.continuousAt.eventually (lt_mem_nhds hc1)
    filter_upwards [e1, e2, e3] with y hy1 hy2 hy3
    have hz : NGMFeasible h k0 T (Function.update ks (t + 1) y) := by
      refine ⟨by rw [Function.update_of_ne (by omega)]; exact hks.1, fun s hs => ?_⟩
      by_cases hst : s = t
      · subst hst
        rw [Function.update_self, Function.update_of_ne (show s ≠ s + 1 by omega)]
        exact ⟨hy1.le, hy2.le⟩
      by_cases hst' : s = t + 1
      · subst hst'
        rw [Function.update_self, Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)]
        exact ⟨(hks.2 (t + 1) (by omega)).1, hy3.le⟩
      rw [Function.update_of_ne (show s + 1 ≠ t + 1 by omega), Function.update_of_ne hst']
      exact hks.2 s hs
    have := hmax _ hz
    rw [hobj] at this
    linarith
  have hg : HasDerivAt g (β ^ t * (u' (h (ks t) - y0) * -1) +
      β ^ (t + 1) * (u' (h y0 - ks (t + 2)) * dh)) y0 := by
    have i1 : HasDerivAt (fun y => h (ks t) - y) (-1) y0 := by
      simpa using (hasDerivAt_id y0).const_sub (h (ks t))
    have i2 : HasDerivAt (fun y => h y - ks (t + 2)) dh y0 := hh.sub_const _
    exact ((hu0.comp y0 i1).const_mul _).add ((hu1.comp y0 i2).const_mul _)
  have h0 := hloc.hasDerivAt_eq_zero hg
  have hbt : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have : β ^ t * (u' (h (ks t) - y0) - β * u' (h y0 - ks (t + 2)) * dh) = 0 := by
    linear_combination -h0
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- **The Euler equation and `k_{T+1} = 0` are sufficient in (P3)** (AKMM, p. 102, via
Result 1). Let `u` be concave and nondecreasing on a convex upward-closed set `S` of consumption
levels and `h = f + (1 − δ)·id` concave on `[0, ∞)`. A feasible plan with consumption in `S`,
satisfying (4.10) for `t < T` and `k_{T+1} = 0`, maximizes (P3) among feasible plans with
consumption in `S`. -/
theorem ngm_finite_sufficient {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : ConcaveOn ℝ S u) (hmono : MonotoneOn u S)
    (hh : ConcaveOn ℝ (Set.Ici 0) h) {β : ℝ} (hβ : 0 ≤ β) {k0 : ℝ} (hk0 : 0 ≤ k0) {T : ℕ}
    {ks : ℕ → ℝ} (hks : NGMFeasible h k0 T ks) (hksS : ∀ t ≤ T, h (ks t) - ks (t + 1) ∈ S)
    {du dh : ℕ → ℝ} (hdu : ∀ t ≤ T, HasDerivAt u (du t) (h (ks t) - ks (t + 1)))
    (hdh : ∀ t ≤ T, HasDerivAt h (dh t) (ks t)) (hdu0 : 0 ≤ du T)
    (heuler : ∀ t < T, du t = β * du (t + 1) * dh (t + 1)) (hterm : ks (T + 1) = 0)
    {k : ℕ → ℝ} (hk : NGMFeasible h k0 T k) (hkS : ∀ t ≤ T, h (k t) - k (t + 1) ∈ S) :
    ngmObjective u h β k T ≤ ngmObjective u h β ks T := by
  have hex : ∀ t, ∃ D : ℝ × ℝ →L[ℝ] ℝ, t ≤ T →
      HasFDerivAt (fun p : ℝ × ℝ => u (h p.1 - p.2)) D (ks t, ks (t + 1)) ∧
        D (1, 0) = du t * dh t ∧ D (0, 1) = -du t := by
    intro t
    by_cases ht : t ≤ T
    · obtain ⟨D, hD⟩ := ngm_hasFDerivAt (hdu t ht) (hdh t ht)
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose D hD using hex
  have hnn : ∀ x : ℕ → ℝ, NGMFeasible h k0 T x → ∀ t ≤ T, 0 ≤ x t := by
    intro x hx t ht
    rcases t with _ | t
    · rw [hx.1]; exact hk0
    · exact (hx.2 t (by omega)).1
  refine result_1 (ngm_return_concave hS hup hu hmono hh) hβ hks
    (fun t ht => ⟨hnn ks hks t ht, hksS t ht⟩) D (fun t ht => (hD t ht).1)
    (fun t ht => ?_) hterm ?_ hk (fun t ht => ⟨hnn k hk t ht, hkS t ht⟩)
  · rw [(hD t ht.le).2.2, (hD (t + 1) ht).2.1, heuler t ht]
    ring
  · rw [(hD T le_rfl).2.2]
    linarith

/-- **Uniqueness of the maximizer** (AKMM, p. 101). Let `P` be a set of plans, all starting at
`x₀`, closed under midpoints, whose pairs `(x_t, x_{t+1})`, `t ≤ T`, lie in a set `A` on which `F`
is strictly concave. If `β > 0`, two maximizers over `P` agree on `0, …, T + 1`. -/
theorem finite_unique_max {F : ℝ × ℝ → ℝ} {A : Set (ℝ × ℝ)} (hA : StrictConcaveOn ℝ A F)
    {β : ℝ} (hβ : 0 < β) {T : ℕ} {x0 : ℝ} {P : Set (ℕ → ℝ)} (hP0 : ∀ x ∈ P, x 0 = x0)
    (hPA : ∀ x ∈ P, ∀ t ≤ T, (x t, x (t + 1)) ∈ A)
    (hPmid : ∀ x ∈ P, ∀ y ∈ P, (fun t => (x t + y t) / 2) ∈ P) {xs ys : ℕ → ℝ} (hxs : xs ∈ P)
    (hys : ys ∈ P)
    (hxmax : ∀ x ∈ P, objective (fun a b => F (a, b)) β x T ≤
      objective (fun a b => F (a, b)) β xs T)
    (hymax : ∀ x ∈ P, objective (fun a b => F (a, b)) β x T ≤
      objective (fun a b => F (a, b)) β ys T) :
    ∀ t ≤ T + 1, xs t = ys t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hne⟩ := hcon
  have hs0 : s ≠ 0 := by rintro rfl; exact hne (by rw [hP0 xs hxs, hP0 ys hys])
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  set m : ℕ → ℝ := fun t => (xs t + ys t) / 2
  have hm := hPmid xs hxs ys hys
  have hpair : ∀ r, ((m r, m (r + 1)) : ℝ × ℝ) =
      (1 / 2 : ℝ) • (xs r, xs (r + 1)) + (1 / 2 : ℝ) • (ys r, ys (r + 1)) := fun r => by
    ext <;> simp [m] <;> ring
  have hle : ∀ r ∈ Finset.range (T + 1), β ^ r * ((F (xs r, xs (r + 1)) +
      F (ys r, ys (r + 1))) / 2) ≤ β ^ r * F (m r, m (r + 1)) := fun r hr => by
    have hrT : r ≤ T := by have := Finset.mem_range.1 hr; omega
    have := hA.concaveOn.2 (hPA xs hxs r hrT) (hPA ys hys r hrT) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [← hpair] at this
    simp only [smul_eq_mul] at this
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ.le r)
  have hlt : β ^ t * ((F (xs t, xs (t + 1)) + F (ys t, ys (t + 1))) / 2) <
      β ^ t * F (m t, m (t + 1)) := by
    have hpne : ((xs t, xs (t + 1)) : ℝ × ℝ) ≠ (ys t, ys (t + 1)) := fun h =>
      hne (congrArg Prod.snd h)
    have := hA.2 (hPA xs hxs t (by omega)) (hPA ys hys t (by omega)) hpne
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [← hpair] at this
    simp only [smul_eq_mul] at this
    exact mul_lt_mul_of_pos_left (by linarith) (pow_pos hβ t)
  have hsum := Finset.sum_lt_sum hle ⟨t, Finset.mem_range.2 (by omega), hlt⟩
  have havg : ∑ r ∈ Finset.range (T + 1), β ^ r * ((F (xs r, xs (r + 1)) +
      F (ys r, ys (r + 1))) / 2) = (objective (fun a b => F (a, b)) β xs T +
        objective (fun a b => F (a, b)) β ys T) / 2 := by
    unfold objective
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [havg] at hsum
  have h1 := hxmax m hm
  have h2 := hxmax ys hys
  have h3 := hymax xs hxs
  unfold objective at h1 h2 h3 hsum
  linarith

/-- **Uniqueness in (P3)** (AKMM, p. 102: "there is a unique solution to the difference equation
(4.10)"). With `u` strictly concave and strictly increasing on `S` and `h` strictly concave, two
feasible plans with consumption in `S` that satisfy (4.10) for `t < T` and `k_{T+1} = 0` agree on
`0, …, T + 1`. -/
theorem ngm_finite_unique {u h : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S) (hu : StrictConcaveOn ℝ S u) (hmono : StrictMonoOn u S)
    (hh : StrictConcaveOn ℝ (Set.Ici 0) h) {β : ℝ} (hβ : 0 < β) {k0 : ℝ} (hk0 : 0 ≤ k0) {T : ℕ}
    {ks ks' : ℕ → ℝ} {du dh du' dh' : ℕ → ℝ}
    (hks : NGMFeasible h k0 T ks) (hksS : ∀ t ≤ T, h (ks t) - ks (t + 1) ∈ S)
    (hdu : ∀ t ≤ T, HasDerivAt u (du t) (h (ks t) - ks (t + 1)))
    (hdh : ∀ t ≤ T, HasDerivAt h (dh t) (ks t)) (hdu0 : 0 ≤ du T)
    (heuler : ∀ t < T, du t = β * du (t + 1) * dh (t + 1)) (hterm : ks (T + 1) = 0)
    (hks' : NGMFeasible h k0 T ks') (hksS' : ∀ t ≤ T, h (ks' t) - ks' (t + 1) ∈ S)
    (hdu' : ∀ t ≤ T, HasDerivAt u (du' t) (h (ks' t) - ks' (t + 1)))
    (hdh' : ∀ t ≤ T, HasDerivAt h (dh' t) (ks' t)) (hdu0' : 0 ≤ du' T)
    (heuler' : ∀ t < T, du' t = β * du' (t + 1) * dh' (t + 1)) (hterm' : ks' (T + 1) = 0) :
    ∀ t ≤ T + 1, ks t = ks' t := by
  set P : Set (ℕ → ℝ) := {k | NGMFeasible h k0 T k ∧ ∀ t ≤ T, h (k t) - k (t + 1) ∈ S}
  have hnn : ∀ x : ℕ → ℝ, NGMFeasible h k0 T x → ∀ t ≤ T, 0 ≤ x t := by
    intro x hx t ht
    rcases t with _ | t
    · rw [hx.1]; exact hk0
    · exact (hx.2 t (by omega)).1
  have hmid : ∀ x ∈ P, ∀ y ∈ P, (fun t => (x t + y t) / 2) ∈ P := by
    intro x hx y hy
    refine ⟨⟨by simp only [hx.1.1, hy.1.1]; ring, fun t ht => ?_⟩, fun t ht => ?_⟩ <;>
    · have hc := hh.concaveOn.2 (Set.mem_Ici.2 (hnn x hx.1 t ht)) (Set.mem_Ici.2 (hnn y hy.1 t ht))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc
      have e : (1 / 2 : ℝ) * x t + 1 / 2 * y t = (x t + y t) / 2 := by ring
      rw [e] at hc
      first
      | exact ⟨by linarith [(hx.1.2 t ht).1, (hy.1.2 t ht).1],
          by linarith [(hx.1.2 t ht).2, (hy.1.2 t ht).2]⟩
      | have hin := hS (hx.2 t ht) (hy.2 t ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        simp only [smul_eq_mul] at hin
        exact hup _ hin _ (by linarith)
  have hmaxP : ∀ ks₀ : ℕ → ℝ, ∀ du₀ dh₀ : ℕ → ℝ, NGMFeasible h k0 T ks₀ →
      (∀ t ≤ T, h (ks₀ t) - ks₀ (t + 1) ∈ S) →
      (∀ t ≤ T, HasDerivAt u (du₀ t) (h (ks₀ t) - ks₀ (t + 1))) →
      (∀ t ≤ T, HasDerivAt h (dh₀ t) (ks₀ t)) → 0 ≤ du₀ T →
      (∀ t < T, du₀ t = β * du₀ (t + 1) * dh₀ (t + 1)) → ks₀ (T + 1) = 0 →
      ∀ x ∈ P, ngmObjective u h β x T ≤ ngmObjective u h β ks₀ T :=
    fun ks₀ _ _ a b c d e f g x hx => ngm_finite_sufficient hS hup hu.concaveOn
      hmono.monotoneOn hh.concaveOn hβ.le hk0 a b c d e f g hx.1 hx.2
  exact finite_unique_max (ngm_return_strictConcave hS hup hu hmono hh) hβ (x0 := k0)
    (fun x hx => hx.1.1) (fun x hx t ht => ⟨hnn x hx.1 t ht, hx.2 t ht⟩) hmid
    ⟨hks, hksS⟩ ⟨hks', hksS'⟩
    (hmaxP ks du dh hks hksS hdu hdh hdu0 heuler hterm)
    (hmaxP ks' du' dh' hks' hksS' hdu' hdh' hdu0' heuler' hterm')

end AKMM.DynamicOptimization
