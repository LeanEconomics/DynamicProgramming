/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.OCMonotone

/-!
# Theorem 6.4.3: concavity and the policy function

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCConcave`), namespace renamed.

Miao, §6.4, pp. 176–178. Under Assumptions 6.4.1–6.4.12, `V_t(·, z)` is strictly concave and
`G_t` is a single-valued continuous function `g_t`.

* `CompConcave f`: `θ f(φ(x, a, z, z′), z′) + η f(φ(x′, a′, z, z′), z′) ≤
  f(φ(θx + ηx′, θa + ηa′, z, z′), z′)`, the property of `V_{t+1}` the induction needs. It holds
  when `f(·, z′)` is concave and nondecreasing and `φ` is concave (`compConcave_of_mono`; the
  book's remark that "we need `u_T` to be monotonic", p. 177), and when `f(·, z′)` is concave and
  `φ` is affine (`compConcave_of_affine`), with no monotonicity.
* `concave_core`: `V_t(·, z)` is strictly concave for all `t ≤ T` whenever every `V_{t+1}` that
  is strictly concave has `CompConcave`. **Strict concavity of `V_t` is correct as stated**: the
  strictness comes from `u_t`, strict in `x` by Assumption 6.4.10.
* `theorem_6_4_3_concave`: strict concavity under the book's Assumptions 6.4.1–6.4.12
  (monotonicity from Theorem 6.4.2).
* **Correction** (`theorem_6_4_3_counterexample`): `G_t` need not be single-valued. Assumption
  6.4.10 is strict only in `x`; if neither `u_t` nor `φ` depends on `a`, every feasible action is
  optimal although Assumptions 6.4.1–6.4.12 and 5.1.2 hold. `theorem_6_4_3` adds that
  `φ(x, ·, z, z′)` is one-to-one on `A` (true for `φ = a`) and uses `β > 0`; then `G_t = {g_t}`
  and `g_t` is continuous (`G_eq_singleton_core`, `continuousOn_g_core`).
* `theorem_6_4_3_affine`: the same conclusions with Assumptions 6.4.7–6.4.9 dropped when `φ` is
  affine in `(x, a)`; `theorem_6_4_3_phi_eq_a` is the case `φ(x, a, z, z′) = a` of p. 180.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {E F Z : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace Z] [MeasurableSpace E] [MeasurableSpace F]
  (M : OCModel E F Z)

/-- The composite `f(φ(·, ·, z, z′), z′)` is concave on `X × A`. -/
def CompConcave (f : E → Z → ℝ) : Prop :=
  ∀ z z', ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
    θ * f (M.φ x a z z') z' + η * f (M.φ x' a' z z') z' ≤
      f (M.φ (θ • x + η • x') (θ • a + η • a') z z') z'

/-- The composite `f(φ(x, ·, z, z′), z′)` is strictly concave on `A` for each `x`. -/
def CompStrictA (f : E → Z → ℝ) : Prop :=
  ∀ z z', ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, a ≠ a' → ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
    θ * f (M.φ x a z z') z' + η * f (M.φ x a' z z') z' < f (M.φ x (θ • a + η • a') z z') z'

/-- `φ(·, ·, z, z′)` is affine on `X × A`. -/
def PhiAffine : Prop :=
  ∀ z z', ∀ x ∈ M.X, ∀ x' ∈ M.X, ∀ a ∈ M.A, ∀ a' ∈ M.A, ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
    M.φ (θ • x + η • x') (θ • a + η • a') z z' = θ • M.φ x a z z' + η • M.φ x' a' z z'

/-- `φ(x, ·, z, z′)` is one-to-one on `A`. -/
def PhiInjA : Prop := ∀ z z', ∀ x ∈ M.X, Set.InjOn (fun a => M.φ x a z z') M.A

variable {M}

omit [MetricSpace Z] in
/-- Miao, p. 177: with `φ` concave (Assumption 6.4.12) and `f(·, z′)` concave and nondecreasing,
the composite `f(φ(·, ·, z, z′), z′)` is concave. -/
theorem compConcave_of_mono [PartialOrder E] (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) (h6412 : M.Assumption6412)
    {f : E → Z → ℝ} (hc : ∀ z', ConcaveOn ℝ M.X fun x => f x z')
    (hm : ∀ z', MonotoneOn (fun x => f x z') M.X) : M.CompConcave f := by
  intro z z' x hx x' hx' a ha a' ha' θ η hθ hη hs
  have hp := h645X x hx a ha z z'
  have hp' := h645X x' hx' a' ha' z z'
  have hq := h645X _ (h641.1 hx hx' hθ.le hη.le hs) _ (h642.1 ha ha' hθ.le hη.le hs) z z'
  have hmid := h641.1 hp hp' hθ.le hη.le hs
  refine le_trans ?_ (hm z' hmid hq (h6412 z z' x hx x' hx' a ha a' ha' θ η hθ hη hs))
  exact (hc z').2 hp hp' hθ.le hη.le hs

omit [MetricSpace Z] in
/-- With `φ` concave, `φ(x, ·, z, z′)` one-to-one and `f(·, z′)` strictly concave and
nondecreasing, `f(φ(x, ·, z, z′), z′)` is strictly concave. -/
theorem compStrictA_of_mono [PartialOrder E] (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) (h6412 : M.Assumption6412)
    (hinj : M.PhiInjA) {f : E → Z → ℝ} (hc : ∀ z', StrictConcaveOn ℝ M.X fun x => f x z')
    (hm : ∀ z', MonotoneOn (fun x => f x z') M.X) : M.CompStrictA f := by
  intro z z' x hx a ha a' ha' hne θ η hθ hη hs
  have hp := h645X x hx a ha z z'
  have hp' := h645X x hx a' ha' z z'
  have hq := h645X x hx _ (h642.1 ha ha' hθ.le hη.le hs) z z'
  have hmid := h641.1 hp hp' hθ.le hη.le hs
  have hφne : M.φ x a z z' ≠ M.φ x a' z z' := fun he => hne (hinj z z' x hx ha ha' he)
  have hle := h6412 z z' x hx x hx a ha a' ha' θ η hθ hη hs
  rw [Convex.combo_self hs] at hle
  exact lt_of_lt_of_le ((hc z').2 hp hp' hφne hθ hη hs) (hm z' hmid hq hle)

omit [MetricSpace Z] [MeasurableSpace E] [MeasurableSpace F] in
/-- With `φ` affine and `f(·, z′)` concave, the composite is concave; no monotonicity needed. -/
theorem compConcave_of_affine
    (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) (haff : M.PhiAffine)
    {f : E → Z → ℝ} (hc : ∀ z', ConcaveOn ℝ M.X fun x => f x z') : M.CompConcave f := by
  intro z z' x hx x' hx' a ha a' ha' θ η hθ hη hs
  rw [haff z z' x hx x' hx' a ha a' ha' θ η hθ hη hs]
  exact (hc z').2 (h645X x hx a ha z z') (h645X x' hx' a' ha' z z') hθ.le hη.le hs

omit [MetricSpace Z] [MeasurableSpace E] [MeasurableSpace F] in
/-- With `φ` affine and one-to-one in `a`, and `f(·, z′)` strictly concave, the composite is
strictly concave in `a`. -/
theorem compStrictA_of_affine (h645X : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X)
    (haff : M.PhiAffine) (hinj : M.PhiInjA) {f : E → Z → ℝ}
    (hc : ∀ z', StrictConcaveOn ℝ M.X fun x => f x z') : M.CompStrictA f := by
  intro z z' x hx a ha a' ha' hne θ η hθ hη hs
  have h := haff z z' x hx x hx a ha a' ha' θ η hθ hη hs
  rw [Convex.combo_self hs] at h
  rw [h]
  exact (hc z').2 (h645X x hx a ha z z') (h645X x hx a' ha' z z')
    (fun he => hne (hinj z z' x hx ha ha' he)) hθ hη hs

variable {P : (E → Z → ℝ) → Prop}

/-- Concavity passes through the expectation: from `CompConcave f`,
`θ h(x, a, z) + η h(x′, a′, z) ≤ h(θx + ηx′, θa + ηa′, z)` for the integrals `h`. -/
theorem cont_comb (h : M.Standing P) (h641 : M.Assumption641) (h642 : M.Assumption642) {t : ℕ}
    (ht : t < M.T) (hcc : M.CompConcave (M.V (t + 1))) {x x' : E} (hx : x ∈ M.X)
    (hx' : x' ∈ M.X) {a a' : F} (ha : a ∈ M.A) (ha' : a' ∈ M.A) (z : Z) {θ η : ℝ} (hθ : 0 < θ)
    (hη : 0 < η) (hs : θ + η = 1) :
    θ * M.cont (M.V (t + 1)) x a z + η * M.cont (M.V (t + 1)) x' a' z ≤
      M.cont (M.V (t + 1)) (θ • x + η • x') (θ • a + η • a') z := by
  have i1 := h.integrable ht hx ha z
  have i2 := h.integrable ht hx' ha' z
  have i3 := h.integrable ht (h641.1 hx hx' hθ.le hη.le hs) (h642.1 ha ha' hθ.le hη.le hs) z
  simp only [cont]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul θ)
    (i2.const_mul η)]
  exact integral_mono ((i1.const_mul θ).add (i2.const_mul η)) i3
    fun z' => hcc z z' x hx x' hx' a ha a' ha' θ η hθ hη hs

/-- **The concavity step of Theorem 6.4.3** (Miao, pp. 176–177): if every strictly concave
`V_{t+1}` has the composite-concavity property, then `V_t(·, z)` is strictly concave on `X` for
all `t ≤ T`. -/
theorem concave_core (h : M.Standing P) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (hβ : 0 ≤ M.β)
    (hCC : ∀ t < M.T, (∀ z, StrictConcaveOn ℝ M.X fun x => M.V (t + 1) x z) →
      M.CompConcave (M.V (t + 1))) :
    ∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z := by
  have key : ∀ k ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V (M.T - k) x z := by
    intro k
    induction k with
    | zero => intro _ z; rw [Nat.sub_zero, M.V_T_eq]; exact h6410.1 z
    | succ k ih =>
      intro hk z
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      set t := M.T - (k + 1)
      have hV : ∀ z, StrictConcaveOn ℝ M.X fun x => M.V (t + 1) x z := by
        rw [he]; exact ih (by omega)
      have hcc := hCC t ht hV
      refine ⟨h641.1, fun x hx x' hx' hne θ η hθ hη hs => ?_⟩
      obtain ⟨a, haΓ, hval⟩ := h.G_nonempty ht hx z
      obtain ⟨a', haΓ', hval'⟩ := h.G_nonempty ht hx' z
      have haA := h.a644.1 x hx z haΓ
      have haA' := h.a644.1 x' hx' z haΓ'
      have hθΓ := h6411 z x hx x' hx' a haΓ a' haΓ' θ η hθ hη hs
      have hxθ := h641.1 hx hx' hθ.le hη.le hs
      have hu := (h6410.2 t ht z x hx x' hx' a haA a' haA' θ η hθ hη hs).2 hne
      have hc := cont_comb h h641 h642 ht hcc hx hx' haA haA' z hθ hη hs
      simp only [smul_eq_mul]
      rw [← hval, ← hval']
      refine lt_of_lt_of_le ?_ (h.obj_le_V ht hxθ hθΓ)
      simp only [obj]
      nlinarith [mul_le_mul_of_nonneg_left hc hβ]
  intro t ht
  have := key (M.T - t) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self ht] at this

omit [MeasurableSpace E] in
/-- **Single-valuedness of `G_t`** (Miao, p. 177, corrected): if `β > 0` and every `V_{t+1}` gives
a composite strictly concave in `a`, then each `G_t(x, z)` has at most one element. -/
theorem G_subsingleton_core [IsMarkovKernel M.Q] (h : M.Standing P) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (hβ : 0 < M.β)
    (hSA : ∀ t < M.T, M.CompStrictA (M.V (t + 1))) :
    ∀ t < M.T, ∀ x ∈ M.X, ∀ z, (M.G t x z).Subsingleton := by
  intro t ht x hx z a ⟨haΓ, hva⟩ b ⟨hbΓ, hvb⟩
  by_contra hne
  have haA := h.a644.1 x hx z haΓ
  have hbA := h.a644.1 x hx z hbΓ
  have hh : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hmΓ := h6411 z x hx x hx a haΓ b hbΓ (1 / 2) (1 / 2) hpos hpos hh
  rw [Convex.combo_self hh] at hmΓ
  have hu := (h6410.2 t ht z x hx x hx a haA b hbA (1 / 2) (1 / 2) hpos hpos hh).1
  rw [Convex.combo_self hh] at hu
  -- the continuation value is strictly concave in `a`
  have hc : (1 / 2) * M.cont (M.V (t + 1)) x a z + (1 / 2) * M.cont (M.V (t + 1)) x b z <
      M.cont (M.V (t + 1)) x ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) z := by
    have i1 := h.integrable ht hx haA z
    have i2 := h.integrable ht hx hbA z
    have i3 := h.integrable ht hx (h642.1 haA hbA hpos.le hpos.le hh) z
    simp only [cont]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
      (i2.const_mul _)]
    exact integral_lt_integral_of_lt ((i1.const_mul _).add (i2.const_mul _)) i3
      fun z' => hSA t ht z z' x hx a haA b hbA hne _ _ hpos hpos hh
  have hle := h.obj_le_V ht hx hmΓ
  simp only [obj] at hle hva hvb
  nlinarith [mul_lt_mul_of_pos_left hc hβ]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F] in
/-- `G_t(x, z) = {g_t(x, z)}` when `G_t` is single-valued. -/
theorem G_eq_singleton_core [Nonempty F] (h : M.Standing P) {t : ℕ} (ht : t < M.T) {x : E}
    (hx : x ∈ M.X) {z : Z} (hsub : (M.G t x z).Subsingleton) : M.G t x z = {M.g t x z} :=
  hsub.eq_singleton_of_mem (h.g_mem ht hx z)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F] in
/-- A single-valued u.h.c. policy correspondence is a continuous function (SLP Ex 3.11a):
`g_t` is continuous on `X × Z`. -/
theorem continuousOn_g_core [Nonempty F] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hsub : ∀ x ∈ M.X, ∀ z, (M.G t x z).Subsingleton) :
    ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  have hG := (M.theorem_6_4_1 P h.expCont h.memP h.a644 h.a646).2 t ht
  have heq : M.Gs t = fun s => {M.g t s.1.1 s.1.2} := funext fun s =>
    G_eq_singleton_core h ht s.2.1 (hsub _ s.2.1 _)
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
  intro s
  have hu := (hG s).2.2
  rw [heq] at hu
  exact continuousAt_of_isUHC_singleton hu

/-- **Theorem 6.4.3 (Concavity)** (Miao, p. 176), strict concavity of `V_t`: under Assumptions
6.4.1–6.4.12 (with the standing hypotheses for 6.4.3–6.4.6) and `β ≥ 0`, `V_t(·, z)` is strictly
concave on `X` for every `z` and `t ≤ T`. -/
theorem theorem_6_4_3_concave [PartialOrder E] (h : M.Standing P) (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h647 : M.Assumption647) (h648 : M.Assumption648)
    (h649 : M.Assumption649) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (h6412 : M.Assumption6412) (hβ : 0 ≤ M.β) :
    ∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z := by
  have hmono := theorem_6_4_2 h h647 h648 h649 hβ
  refine concave_core h h641 h642 h6410 h6411 hβ fun t ht hV => ?_
  exact compConcave_of_mono h641 h642 h.a645.1 h6412 (fun z' => (hV z').concaveOn)
    fun z' => (hmono (t + 1) ht z').monotoneOn

/-- **Theorem 6.4.3 (Concavity)** (Miao, p. 176), corrected. Under Assumptions 6.4.1–6.4.12, with
`β > 0` and `φ(x, ·, z, z′)` one-to-one on `A`: `V_t(·, z)` is strictly concave for `t ≤ T`, and
for `t < T` the policy correspondence is a single-valued continuous function,
`G_t(x, z) = {g_t(x, z)}`. -/
theorem theorem_6_4_3 [PartialOrder E] [Nonempty F] [IsMarkovKernel M.Q] (h : M.Standing P)
    (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h647 : M.Assumption647) (h648 : M.Assumption648)
    (h649 : M.Assumption649) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (h6412 : M.Assumption6412) (hβ : 0 < M.β) (hinj : M.PhiInjA) :
    (∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z) ∧
      (∀ t < M.T, ∀ x ∈ M.X, ∀ z, M.G t x z = {M.g t x z}) ∧
      ∀ t < M.T, ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  have hconc := theorem_6_4_3_concave h h641 h642 h647 h648 h649 h6410 h6411 h6412 hβ.le
  have hmono := theorem_6_4_2 h h647 h648 h649 hβ.le
  have hsub := G_subsingleton_core h h642 h6410 h6411 hβ fun t ht =>
    compStrictA_of_mono h641 h642 h.a645.1 h6412 hinj (hconc (t + 1) ht)
      fun z' => (hmono (t + 1) ht z').monotoneOn
  exact ⟨hconc, fun t ht x hx z => G_eq_singleton_core h ht hx (hsub t ht x hx z),
    fun t ht => continuousOn_g_core h ht (hsub t ht)⟩

/-- **Theorem 6.4.3 without monotonicity** (Miao, p. 180): if `φ` is affine in `(x, a)` and
one-to-one in `a`, the conclusions hold without Assumptions 6.4.7–6.4.9 and 6.4.12. -/
theorem theorem_6_4_3_affine [Nonempty F] [IsMarkovKernel M.Q] (h : M.Standing P)
    (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (hβ : 0 < M.β) (haff : M.PhiAffine) (hinj : M.PhiInjA) :
    (∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z) ∧
      (∀ t < M.T, ∀ x ∈ M.X, ∀ z, M.G t x z = {M.g t x z}) ∧
      ∀ t < M.T, ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  have hconc := concave_core h h641 h642 h6410 h6411 hβ.le fun t _ hV =>
    compConcave_of_affine h.a645.1 haff fun z' => (hV z').concaveOn
  have hsub := G_subsingleton_core h h642 h6410 h6411 hβ fun t ht =>
    compStrictA_of_affine h.a645.1 haff hinj (hconc (t + 1) ht)
  exact ⟨hconc, fun t ht x hx z => G_eq_singleton_core h ht hx (hsub t ht x hx z),
    fun t ht => continuousOn_g_core h ht (hsub t ht)⟩

/-- **Theorem 6.4.3 for `φ(x, a, z, z′) = a`** (Miao, p. 180): when the action is next period's
state, Assumptions 6.4.7–6.4.9 can be dispensed with. -/
theorem theorem_6_4_3_phi_eq_a [Nonempty E] {M : OCModel E E Z} [IsMarkovKernel M.Q]
    (h : M.Standing P)
    (hφ : ∀ x a z z', M.φ x a z z' = a) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (hβ : 0 < M.β) :
    (∀ t ≤ M.T, ∀ z, StrictConcaveOn ℝ M.X fun x => M.V t x z) ∧
      (∀ t < M.T, ∀ x ∈ M.X, ∀ z, M.G t x z = {M.g t x z}) ∧
      ∀ t < M.T, ContinuousOn (fun p : E × Z => M.g t p.1 p.2) (M.X ×ˢ Set.univ) := by
  refine theorem_6_4_3_affine h h641 h642 h6410 h6411 hβ
    (fun z z' x _ x' _ a _ a' _ θ η _ _ _ => ?_) (fun z z' x _ a _ a' _ he => ?_)
  · simp only [hφ]
  · simpa only [hφ] using he

end OCModel

end Miao.IncompleteMarkets
