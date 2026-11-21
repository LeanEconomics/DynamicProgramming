/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.OCConcave
import InfiniteHorizonDP.OCDiffTools
import InfiniteHorizonDP.SLPEnvelope

/-!
# Theorem 6.4.4: differentiability, the envelope condition and the Euler equations

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCDifferentiable`), namespace renamed.

Miao, §6.4, pp. 178–180, for one-dimensional states and actions (`X, A ⊆ ℝ`; the book's
`n_x = n_a = 1`, the case of §6.5 and §6.6.2). The value functions are differentiable on `int X`
with the **envelope condition** (6.31)–(6.32) (`envRHS`), the **first-order condition** (6.33)
(`focRHS`) holds, and for `φ(x, a, z, z′) = a` these give the **Euler equations** of p. 180.

The proof is the book's: Benveniste–Scheinkman (SLP Theorem 4.10, `theorem_4_10`) applied to
`W(y) = u_t(y, z, a_t) + β ∫ V_{t+1}(φ(y, a_t, z, z′), z′) Q(z, dz′) ≤ V_t(y, z)`. **Corrections**
to the hypotheses, each needed by that argument:

* **Differentiating under `∫ Q(z, dz′)`** in (6.31) and (6.33) needs a domination. We use
  concavity: `y ↦ V_{t+1}(φ(y, a, z, z′), z′)` is concave (`CompConcave`), hence Lipschitz near
  `x_t` with a constant fixed by a uniform bound on `V_{t+1}(φ(y, b, z, z′), z′)` for `(y, b)`
  near `(x_t, a_t)` (`LocBounded`, `oc_hasDerivAt_integral_concave`). `LocBounded` holds when
  `Z` is compact (`locBounded_of_compact`), and when the `V_t` are bounded (case (i)).
* **Interiority must hold at every interior state, and the next state must be interior**
  (`InteriorPolicy`): the book assumes `x_t ∈ int X` and `g_t(x_t, z_t) ∈ int Γ(x_t, z_t)` at the
  point only, but (6.31) and (6.33) use the derivative of `V_{t+1}` at
  `x_{t+1} = φ(x_t, a_t, z_t, z_{t+1})`, which needs `x_{t+1} ∈ int X` and the induction
  hypothesis there.
* `g_t(x_t, z_t) ∈ int Γ(x_t, z_t)` gives `g_t(x_t, z_t) ∈ Γ(x, z_t)` for `x` near `x_t` only
  because `Γ` is convex-valued (Assumption 6.4.11) and l.h.c. (`eventually_mem_Γ`).
* (6.31) is stated for `t = 1, …, T − 1` but holds, and is used, for `t = 0` too.
* `V_t(·, z)` is continuously differentiable on `int X` because a differentiable concave function
  of one variable is (`oc_continuousOn_deriv_of_concave`); for `t = T` this needs only that
  `u_T(·, z)` is differentiable, as Assumption 6.4.13 says.

Main results: `theorem_6_4_4` (Assumptions 6.4.1–6.4.14), `theorem_6_4_4_phi_eq_a` and
`euler_equations` (`φ = a`, without Assumptions 6.4.7–6.4.9), built on `theorem_6_4_4_core`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology Metric

namespace OCModel

variable {Z : Type*} [MeasurableSpace Z] [MetricSpace Z] (M : OCModel ℝ ℝ Z)

/-- The right side of the **envelope condition (6.31)** at the action `a`:
`∂u_t(x, z, a)/∂x + β ∫ ∂V_{t+1}(φ(x, a, z, z′), z′)/∂x · ∂φ(x, a, z, z′)/∂x Q(z, dz′)`. -/
noncomputable def envRHS (t : ℕ) (x : ℝ) (z : Z) (a : ℝ) : ℝ :=
  deriv (fun y => M.u t y z a) x + M.β * ∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
    deriv (fun y => M.φ y a z z') x ∂M.Q z

/-- The right side of the **first-order condition (6.33)** at the action `a`:
`∂u_t(x, z, a)/∂a + β ∫ ∂V_{t+1}(φ(x, a, z, z′), z′)/∂x · ∂φ(x, a, z, z′)/∂a Q(z, dz′)`. -/
noncomputable def focRHS (t : ℕ) (x : ℝ) (z : Z) (a : ℝ) : ℝ :=
  deriv (fun b => M.u t x z b) a + M.β * ∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
    deriv (fun b => M.φ x b z z') a ∂M.Q z

/-- The domination hypothesis for (6.31) and (6.33): near an interior `(x, a)`,
`V_{t+1}(φ(y, b, z, z′), z′)` is bounded uniformly in `z′`. -/
def LocBounded : Prop :=
  ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ a ∈ interior M.A, ∃ r > 0, ∃ C,
    ∀ y ∈ ball x r, ∀ b ∈ ball a r, ∀ z', |M.V (t + 1) (M.φ y b z z') z'| ≤ C

/-- The interiority hypothesis of Theorem 6.4.4, corrected: at every interior state the policy
is interior to `Γ` and every next state is interior to `X`. -/
def InteriorPolicy : Prop :=
  ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
    M.g t x z ∈ interior (M.Γ x z) ∧ ∀ z', M.φ x (M.g t x z) z z' ∈ interior M.X

/-- The partial derivatives used in Theorem 6.4.4 exist on the interiors (they follow from
Assumptions 6.4.13–6.4.14, `partials_of`). -/
structure Partials : Prop where
  uT : ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.uT y z) x
  ux : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun y => M.u t y z a) x
  ua : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun b => M.u t x z b) a
  φx : ∀ z z', ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun y => M.φ y a z z') x
  φa : ∀ z z', ∀ x ∈ interior M.X, ∀ a ∈ interior M.A,
    DifferentiableAt ℝ (fun b => M.φ x b z z') a

variable {M}

omit [MetricSpace Z] in
/-- Assumptions 6.4.13 and 6.4.14 give the partial derivatives. -/
theorem partials_of (h6413 : M.Assumption6413) (h6414 : M.Assumption6414) : M.Partials := by
  have hopen : IsOpen (interior (M.X ×ˢ M.A)) := isOpen_interior
  have hmem : ∀ {x a}, x ∈ interior M.X → a ∈ interior M.A → (x, a) ∈ interior (M.X ×ˢ M.A) :=
    fun hx ha => by rw [interior_prod_eq]; exact ⟨hx, ha⟩
  have hu : ∀ t < M.T, ∀ z, ∀ {x a}, x ∈ interior M.X → a ∈ interior M.A →
      DifferentiableAt ℝ (fun p : ℝ × ℝ => M.u t p.1 z p.2) (x, a) := fun t ht z x a hx ha =>
    ((h6413.2 t ht z).differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds (hmem hx ha))
  have hφ : ∀ z z', ∀ {x a}, x ∈ interior M.X → a ∈ interior M.A →
      DifferentiableAt ℝ (fun p : ℝ × ℝ => M.φ p.1 p.2 z z') (x, a) := fun z z' x a hx ha =>
    (h6414 z z').differentiableAt (hopen.mem_nhds (hmem hx ha))
  refine ⟨fun z x hx => (h6413.1 z).differentiableAt (isOpen_interior.mem_nhds hx),
    fun t ht z x hx a ha => ?_, fun t ht z x hx a ha => ?_, fun z z' x hx a ha => ?_,
    fun z z' x hx a ha => ?_⟩
  · exact (hu t ht z hx ha).comp x (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, a)) x)
  · exact (hu t ht z hx ha).comp a (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (x, b)) a)
  · exact (hφ z z' hx ha).comp x (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y, a)) x)
  · exact (hφ z z' hx ha).comp a (by fun_prop : DifferentiableAt ℝ (fun b : ℝ => (x, b)) a)

omit [MeasurableSpace Z] [MetricSpace Z] in
/-- A concavity inequality with positive weights gives `ConcaveOn`. -/
theorem oc_concaveOn_of_pos {s : Set ℝ} (hs : Convex ℝ s) {f : ℝ → ℝ}
    (h : ∀ y₁ ∈ s, ∀ y₂ ∈ s, ∀ θ η : ℝ, 0 < θ → 0 < η → θ + η = 1 →
      θ * f y₁ + η * f y₂ ≤ f (θ * y₁ + η * y₂)) : ConcaveOn ℝ s f := by
  refine ⟨hs, fun y₁ hy₁ y₂ hy₂ θ η hθ hη hsum => ?_⟩
  simp only [smul_eq_mul]
  rcases hθ.eq_or_lt with rfl | hθ'
  · have : η = 1 := by linarith
    subst this; simp
  rcases hη.eq_or_lt with rfl | hη'
  · have : θ = 1 := by linarith
    subst this; simp
  exact h y₁ hy₁ y₂ hy₂ θ η hθ' hη' hsum

/-- **`g_t(x, z) ∈ int Γ(x, z)` gives `g_t(x, z) ∈ Γ(y, z)` for `y` near `x`** (Miao, p. 179),
for the convex-valued (Assumption 6.4.11) l.h.c. (Assumption 6.4.4) correspondence `Γ`. -/
theorem eventually_mem_Γ (h644 : M.Assumption644) (h6411 : M.Assumption6411) {x : ℝ}
    (hx : x ∈ interior M.X) {z : Z} {a : ℝ} (ha : a ∈ interior (M.Γ x z)) :
    ∀ᶠ y in 𝓝 x, y ∈ M.X ∧ a ∈ M.Γ y z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ha)
  have hb0 : a - ε / 2 ∈ M.Γ x z := hball (by
    rw [mem_ball, Real.dist_eq, show a - ε / 2 - a = -(ε / 2) by ring, abs_neg,
      abs_of_pos (half_pos hε)]; linarith)
  have hc0 : a + ε / 2 ∈ M.Γ x z := hball (by
    rw [mem_ball, Real.dist_eq, show a + ε / 2 - a = ε / 2 by ring, abs_of_pos (half_pos hε)]
    linarith)
  have hxX : M.X ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hx
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hfreq : ∃ᶠ y in 𝓝 x, y ∈ M.X ∧ a ∉ M.Γ y z :=
    (hne.and_eventually hxX).mono fun y ⟨h1, h2⟩ => ⟨h2, fun h => h1 ⟨h2, h⟩⟩
  obtain ⟨ys, hys, hmem⟩ := exists_seq_forall_of_frequently hfreq
  let s0 : ↥(M.X ×ˢ (Set.univ : Set Z)) := ⟨(x, z), mem_of_mem_nhds hxX, Set.mem_univ _⟩
  let ss : ℕ → ↥(M.X ×ˢ (Set.univ : Set Z)) := fun n => ⟨(ys n, z), (hmem n).1, Set.mem_univ _⟩
  have hss : Tendsto ss atTop (𝓝 s0) :=
    tendsto_subtype_rng.2 (hys.prodMk_nhds tendsto_const_nhds)
  obtain ⟨N1, bs, hbs, hblim⟩ := (h644.2 s0).2.1.2 _ hb0 ss hss
  obtain ⟨N2, cs, hcs, hclim⟩ := (h644.2 s0).2.1.2 _ hc0 ss hss
  have e1 : ∀ᶠ n in atTop, bs n < a := hblim.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ n in atTop, a < cs n := hclim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2, hb, hc⟩ :=
    ((eventually_ge_atTop N1).and ((eventually_ge_atTop N2).and (e1.and e2))).exists
  have hbΓ : bs n ∈ M.Γ (ys n) z := hbs n hn1
  have hcΓ : cs n ∈ M.Γ (ys n) z := hcs n hn2
  have hd : 0 < cs n - bs n := by linarith
  have hθ : 0 < (cs n - a) / (cs n - bs n) := div_pos (by linarith) hd
  have hη : 0 < (a - bs n) / (cs n - bs n) := div_pos (by linarith) hd
  have hs : (cs n - a) / (cs n - bs n) + (a - bs n) / (cs n - bs n) = 1 := by
    field_simp; ring
  have hcomb : ((cs n - a) / (cs n - bs n)) • bs n + ((a - bs n) / (cs n - bs n)) • cs n = a := by
    simp only [smul_eq_mul]; field_simp; ring
  have := h6411 z (ys n) (hmem n).1 (ys n) (hmem n).1 (bs n) hbΓ (cs n) hcΓ _ _ hθ hη hs
  rw [Convex.combo_self hs, hcomb] at this
  exact (hmem n).2 this

variable {P : (ℝ → Z → ℝ) → Prop}

/-- Differentiating the continuation value in `x` under `∫ Q(z, dz′)` (the second term of
(6.31)). -/
theorem hasDerivAt_cont_x [IsMarkovKernel M.Q] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials) {x : ℝ}
    (hx : x ∈ interior M.X) {a : ℝ} (ha : a ∈ interior M.A) (z : Z)
    (hnext : ∀ z', M.φ x a z z' ∈ interior M.X)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y) :
    HasDerivAt (fun y => M.cont (M.V (t + 1)) y a z)
      (∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
        deriv (fun y => M.φ y a z z') x ∂M.Q z) x := by
  obtain ⟨r₀, hr₀, C, hC⟩ := hbd t ht z x hx a ha
  obtain ⟨ε, hε, hεX⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hr : 0 < min r₀ ε := lt_min hr₀ hε
  have hsub : ∀ y ∈ ball x (min r₀ ε), y ∈ M.X := fun y hy =>
    hεX (ball_subset_ball (min_le_right _ _) hy)
  have haA : a ∈ M.A := interior_subset ha
  refine (oc_hasDerivAt_integral_concave (μ := M.Q z)
    (F := fun y z' => M.V (t + 1) (M.φ y a z z') z') hr (fun z' => ?_)
    (fun y hy z' => hC y (ball_subset_ball (min_le_left _ _) hy) a (mem_ball_self hr₀) z')
    (fun y hy => h.integrable ht (hsub y hy) haA z) (fun z' => ?_)).2
  · refine oc_concaveOn_of_pos (convex_ball _ _) fun y₁ hy₁ y₂ hy₂ θ η hθ hη hs => ?_
    have := hcc z z' y₁ (hsub y₁ hy₁) y₂ (hsub y₂ hy₂) a haA a haA θ η hθ hη hs
    rwa [Convex.combo_self hs, smul_eq_mul, smul_eq_mul] at this
  · exact (hD z' _ (hnext z')).hasDerivAt.comp x (hpar.φx z z' x hx a ha).hasDerivAt

/-- Differentiating the continuation value in `a` under `∫ Q(z, dz′)` (the second term of
(6.33)). -/
theorem hasDerivAt_cont_a [IsMarkovKernel M.Q] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials) {x : ℝ}
    (hx : x ∈ interior M.X) {a : ℝ} (ha : a ∈ interior M.A) (z : Z)
    (hnext : ∀ z', M.φ x a z z' ∈ interior M.X)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y) :
    HasDerivAt (fun b => M.cont (M.V (t + 1)) x b z)
      (∫ z', deriv (fun y => M.V (t + 1) y z') (M.φ x a z z') *
        deriv (fun b => M.φ x b z z') a ∂M.Q z) a := by
  obtain ⟨r₀, hr₀, C, hC⟩ := hbd t ht z x hx a ha
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ha)
  have hr : 0 < min r₀ ε := lt_min hr₀ hε
  have hsub : ∀ b ∈ ball a (min r₀ ε), b ∈ M.A := fun b hb =>
    hεA (ball_subset_ball (min_le_right _ _) hb)
  have hxX : x ∈ M.X := interior_subset hx
  refine (oc_hasDerivAt_integral_concave (μ := M.Q z)
    (F := fun b z' => M.V (t + 1) (M.φ x b z z') z') hr (fun z' => ?_)
    (fun b hb z' => hC x (mem_ball_self hr₀) b (ball_subset_ball (min_le_left _ _) hb) z')
    (fun b hb => h.integrable ht hxX (hsub b hb) z) (fun z' => ?_)).2
  · refine oc_concaveOn_of_pos (convex_ball _ _) fun b₁ hb₁ b₂ hb₂ θ η hθ hη hs => ?_
    have := hcc z z' x hxX x hxX b₁ (hsub b₁ hb₁) b₂ (hsub b₂ hb₂) θ η hθ hη hs
    rwa [Convex.combo_self hs, smul_eq_mul, smul_eq_mul] at this
  · exact (hD z' _ (hnext z')).hasDerivAt.comp a (hpar.φa z z' x hx a ha).hasDerivAt

/-- **The envelope condition (6.31)** at a date `t < T`, given differentiability of `V_{t+1}` on
`int X` (Miao, p. 179, by Benveniste–Scheinkman). -/
theorem envelope_step [IsMarkovKernel M.Q] (h : M.Standing P) (h6411 : M.Assumption6411)
    {t : ℕ} (ht : t < M.T) (hconc : ∀ z, ConcaveOn ℝ M.X fun x => M.V t x z)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials)
    (hint : M.InteriorPolicy)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y)
    (z : Z) {x : ℝ} (hx : x ∈ interior M.X) :
    HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x := by
  obtain ⟨hgΓ, hnext⟩ := hint t ht z x hx
  have hgA : M.g t x z ∈ interior M.A := interior_mono (h.a644.1 x (interior_subset hx) z) hgΓ
  have hW : HasDerivAt (fun y => M.obj t (M.V (t + 1)) y z (M.g t x z))
      (M.envRHS t x z (M.g t x z)) x :=
    (hpar.ux t ht z x hx _ hgA).hasDerivAt.add
      ((hasDerivAt_cont_x h ht hcc hbd hpar hx hgA z hnext hD).const_mul M.β)
  have heq : M.obj t (M.V (t + 1)) x z (M.g t x z) = M.V t x z :=
    (h.g_mem ht (interior_subset hx) z).2
  have hle : ∀ᶠ y in 𝓝 x, M.obj t (M.V (t + 1)) y z (M.g t x z) ≤ M.V t y z :=
    (eventually_mem_Γ h.a644 h6411 hx hgΓ).mono fun y ⟨hyX, hyΓ⟩ => h.obj_le_V ht hyX hyΓ
  rw [hasDerivAt_iff_hasFDerivAt] at hW ⊢
  exact theorem_4_10 (hconc z) (mem_interior_iff_mem_nhds.1 hx) hW heq hle

/-- **The first-order condition (6.33)** at a date `t < T` (Miao, p. 179): the derivative of the
objective of (6.29) in `a` vanishes at the interior maximizer `a_t = g_t(x_t, z_t)`. -/
theorem foc_step [IsMarkovKernel M.Q] (h : M.Standing P) {t : ℕ} (ht : t < M.T)
    (hcc : M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials)
    (hint : M.InteriorPolicy)
    (hD : ∀ z', ∀ y ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V (t + 1) y z') y)
    (z : Z) {x : ℝ} (hx : x ∈ interior M.X) : M.focRHS t x z (M.g t x z) = 0 := by
  obtain ⟨hgΓ, hnext⟩ := hint t ht z x hx
  have hgA : M.g t x z ∈ interior M.A := interior_mono (h.a644.1 x (interior_subset hx) z) hgΓ
  have hd : HasDerivAt (fun b => M.obj t (M.V (t + 1)) x z b) (M.focRHS t x z (M.g t x z))
      (M.g t x z) :=
    (hpar.ua t ht z x hx _ hgA).hasDerivAt.add
      ((hasDerivAt_cont_a h ht hcc hbd hpar hx hgA z hnext hD).const_mul M.β)
  have hmax : IsLocalMax (fun b => M.obj t (M.V (t + 1)) x z b) (M.g t x z) := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hgΓ] with b hb
    rw [(h.g_mem ht (interior_subset hx) z).2]
    exact h.obj_le_V ht (interior_subset hx) hb
  exact hmax.hasDerivAt_eq_zero hd

/-- **Theorem 6.4.4 (Differentiability)** (Miao, pp. 178–180), for one-dimensional states and
actions, in the form the proof uses. Suppose the standing hypotheses, Assumption 6.4.11, `V_t(·, z)`
concave for `t ≤ T`, every composite `V_{t+1}(φ(·, ·, z, z′), z′)` concave, the domination
`LocBounded`, the partial derivatives `Partials` and the interiority `InteriorPolicy`. Then for
`x ∈ int X`:
* `V_t(·, z)` is differentiable for `t ≤ T`, with derivative continuous on `int X`;
* (6.31) for `t = 0, 1, …, T − 1`: `V_t′(x, z) = envRHS t x z (g_t(x, z))`;
* (6.32): `V_T′(x, z) = ∂u_T(x, z)/∂x`;
* (6.33) for `t = 0, 1, …, T − 1`: `focRHS t x z (g_t(x, z)) = 0`. -/
theorem theorem_6_4_4_core [IsMarkovKernel M.Q] (h : M.Standing P) (h6411 : M.Assumption6411)
    (hconc : ∀ t ≤ M.T, ∀ z, ConcaveOn ℝ M.X fun x => M.V t x z)
    (hCC : ∀ t < M.T, M.CompConcave (M.V (t + 1))) (hbd : M.LocBounded) (hpar : M.Partials)
    (hint : M.InteriorPolicy) :
    (∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V t y z) x) ∧
      (∀ t ≤ M.T, ∀ z, ContinuousOn (deriv fun y => M.V t y z) (interior M.X)) ∧
      (∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
        HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x) ∧
      (∀ z, ∀ x ∈ interior M.X, HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x) ∧
      ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, M.focRHS t x z (M.g t x z) = 0 := by
  have hTd : ∀ z, ∀ x ∈ interior M.X,
      HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x := fun z x hx => by
    rw [M.V_T_eq]; exact (hpar.uT z x hx).hasDerivAt
  have key : ∀ k ≤ M.T, ∀ z, ∀ x ∈ interior M.X,
      DifferentiableAt ℝ (fun y => M.V (M.T - k) y z) x := by
    intro k
    induction k with
    | zero => intro _ z x hx; rw [Nat.sub_zero]; exact (hTd z x hx).differentiableAt
    | succ k ih =>
      intro hk z x hx
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      have hD : ∀ z', ∀ y ∈ interior M.X,
          DifferentiableAt ℝ (fun y => M.V (M.T - (k + 1) + 1) y z') y := by
        rw [he]; exact ih (by omega)
      exact (envelope_step h h6411 ht (hconc _ ht.le) (hCC _ ht) hbd hpar hint hD z
        hx).differentiableAt
  have hdiff : ∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X,
      DifferentiableAt ℝ (fun y => M.V t y z) x := fun t ht => by
    have := key (M.T - t) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self ht] at this
  refine ⟨hdiff, fun t ht z => ?_, fun t ht z x hx => ?_, hTd, fun t ht z x hx => ?_⟩
  · have hc := hconc t ht z
    exact oc_continuousOn_deriv_of_concave isOpen_interior
      (hc.subset interior_subset hc.1.interior) (hdiff t ht z)
  · exact envelope_step h h6411 ht (hconc t ht.le) (hCC t ht) hbd hpar hint
      (hdiff (t + 1) ht) z hx
  · exact foc_step h ht (hCC t ht) hbd hpar hint (hdiff (t + 1) ht) z hx

/-- `LocBounded` holds when `Z` is compact: `V_{t+1}(φ(y, b, z, z′), z′)` is continuous on the
compact set `B̄(x, r) × B̄(a, r) × Z ⊆ X × A × Z`. -/
theorem locBounded_of_compact [CompactSpace Z] (h : M.Standing P) : M.LocBounded := by
  intro t ht z x hx a ha
  obtain ⟨ε, hε, hεX⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ha)
  set r := min ε δ / 2
  have hm : 0 < min ε δ := lt_min hε hδ
  have hrdef : r = min ε δ / 2 := rfl
  have hr : 0 < r := by positivity
  have hrε : closedBall x r ⊆ M.X := fun y hy =>
    hεX (closedBall_subset_ball (by have := min_le_left ε δ; linarith) hy)
  have hrδ : closedBall a r ⊆ M.A := fun b hb =>
    hδA (closedBall_subset_ball (by have := min_le_right ε δ; linarith) hb)
  set K := closedBall x r ×ˢ closedBall a r ×ˢ (Set.univ : Set Z)
  have hK : IsCompact K := (isCompact_closedBall x r).prod
    ((isCompact_closedBall a r).prod isCompact_univ)
  have hφc : ContinuousOn (fun q : ℝ × ℝ × Z => M.φ q.1 q.2.1 z q.2.2) K :=
    h.a645.2.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk
      (continuous_const.prodMk continuous_snd.snd))).continuousOn
      fun q hq => ⟨hrε hq.1, hrδ hq.2.1, Set.mem_univ _⟩
  have hc : ContinuousOn (fun q : ℝ × ℝ × Z => M.V (t + 1) (M.φ q.1 q.2.1 z q.2.2) q.2.2) K :=
    (h.contV ht).comp (hφc.prodMk continuous_snd.snd.continuousOn) fun q hq =>
      ⟨h.a645.1 _ (hrε hq.1) _ (hrδ hq.2.1) _ _, Set.mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨r, hr, C, fun y hy b hb z' => ?_⟩
  have := hC (y, b, z') ⟨ball_subset_closedBall hy, ball_subset_closedBall hb, Set.mem_univ _⟩
  rwa [Real.norm_eq_abs] at this

/-- **Theorem 6.4.4 (Differentiability)** (Miao, p. 178), corrected, for `X, A ⊆ ℝ`. Under
Assumptions 6.4.1–6.4.14 (the standing hypotheses carrying 6.4.3–6.4.6), `β ≥ 0`, the
domination `LocBounded` (automatic for compact `Z`, `locBounded_of_compact`) and the interiority
`InteriorPolicy`: each `V_t(·, z)` is continuously differentiable on `int X`, the envelope
condition (6.31) holds for `t = 0, …, T − 1`, (6.32) holds, and the first-order condition (6.33)
holds for `t = 0, …, T − 1`. -/
theorem theorem_6_4_4 [IsMarkovKernel M.Q] (h : M.Standing P) (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h647 : M.Assumption647) (h648 : M.Assumption648)
    (h649 : M.Assumption649) (h6410 : M.Assumption6410) (h6411 : M.Assumption6411)
    (h6412 : M.Assumption6412) (h6413 : M.Assumption6413) (h6414 : M.Assumption6414)
    (hβ : 0 ≤ M.β) (hbd : M.LocBounded) (hint : M.InteriorPolicy) :
    (∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V t y z) x) ∧
      (∀ t ≤ M.T, ∀ z, ContinuousOn (deriv fun y => M.V t y z) (interior M.X)) ∧
      (∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
        HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x) ∧
      (∀ z, ∀ x ∈ interior M.X, HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x) ∧
      ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, M.focRHS t x z (M.g t x z) = 0 := by
  have hconc := theorem_6_4_3_concave h h641 h642 h647 h648 h649 h6410 h6411 h6412 hβ
  have hmono := theorem_6_4_2 h h647 h648 h649 hβ
  refine theorem_6_4_4_core h h6411 (fun t ht z => (hconc t ht z).concaveOn) (fun t ht => ?_)
    hbd (partials_of h6413 h6414) hint
  exact compConcave_of_mono h641 h642 h.a645.1 h6412 (fun z' => (hconc (t + 1) ht z').concaveOn)
    fun z' => (hmono (t + 1) ht z').monotoneOn

/-- **Theorem 6.4.4 for `φ(x, a, z, z′) = a`** (Miao, p. 180): Assumptions 6.4.7–6.4.9 (and
6.4.12, 6.4.14) can be dispensed with. The conclusions are those of `theorem_6_4_4`. -/
theorem theorem_6_4_4_phi_eq_a [IsMarkovKernel M.Q] (h : M.Standing P)
    (hφ : ∀ x a z z', M.φ x a z z' = a) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (h6413 : M.Assumption6413)
    (hβ : 0 ≤ M.β) (hbd : M.LocBounded) (hint : M.InteriorPolicy) :
    (∀ t ≤ M.T, ∀ z, ∀ x ∈ interior M.X, DifferentiableAt ℝ (fun y => M.V t y z) x) ∧
      (∀ t ≤ M.T, ∀ z, ContinuousOn (deriv fun y => M.V t y z) (interior M.X)) ∧
      (∀ t < M.T, ∀ z, ∀ x ∈ interior M.X,
        HasDerivAt (fun y => M.V t y z) (M.envRHS t x z (M.g t x z)) x) ∧
      (∀ z, ∀ x ∈ interior M.X, HasDerivAt (fun y => M.V M.T y z) (deriv (fun y => M.uT y z) x) x) ∧
      ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, M.focRHS t x z (M.g t x z) = 0 := by
  have haff : M.PhiAffine := fun z z' x _ x' _ a _ a' _ θ η _ _ _ => by simp only [hφ]
  have h6414 : M.Assumption6414 := fun z z' => by
    simp only [hφ]
    exact differentiable_snd.differentiableOn
  have hconc := concave_core h h641 h642 h6410 h6411 hβ fun t _ hV =>
    compConcave_of_affine h.a645.1 haff fun z' => (hV z').concaveOn
  exact theorem_6_4_4_core h h6411 (fun t ht z => (hconc t ht z).concaveOn)
    (fun t ht => compConcave_of_affine h.a645.1 haff fun z' => (hconc (t + 1) ht z').concaveOn)
    hbd (partials_of h6413 h6414) hint

/-- **The Euler equations** (Miao, p. 180): when `φ(x, a, z, z′) = a`, so that `x_{t+1} = a_t =
g_t(x_t, z_t)`, the first-order and envelope conditions combine into
`0 = ∂u_t(x_t, z_t, x_{t+1})/∂a + β E_t ∂u_{t+1}(x_{t+1}, z_{t+1}, x_{t+2})/∂x` for
`t = 0, …, T − 2`, with `x_{t+2} = g_{t+1}(x_{t+1}, z_{t+1})`, and
`0 = ∂u_{T−1}(x_{T−1}, z_{T−1}, x_T)/∂a + β E_{T−1} ∂u_T(x_T, z_T)/∂x`. -/
theorem euler_equations [IsMarkovKernel M.Q] (h : M.Standing P)
    (hφ : ∀ x a z z', M.φ x a z z' = a) (h641 : M.Assumption641) (h642 : M.Assumption642)
    (h6410 : M.Assumption6410) (h6411 : M.Assumption6411) (h6413 : M.Assumption6413)
    (hβ : 0 ≤ M.β) (hbd : M.LocBounded) (hint : M.InteriorPolicy) :
    (∀ t, t + 1 < M.T → ∀ z, ∀ x ∈ interior M.X,
      0 = deriv (fun b => M.u t x z b) (M.g t x z) + M.β * ∫ z',
        deriv (fun y => M.u (t + 1) y z' (M.g (t + 1) (M.g t x z) z')) (M.g t x z) ∂M.Q z) ∧
    ∀ t, t + 1 = M.T → ∀ z, ∀ x ∈ interior M.X,
      0 = deriv (fun b => M.u t x z b) (M.g t x z) + M.β * ∫ z',
        deriv (fun y => M.uT y z') (M.g t x z) ∂M.Q z := by
  obtain ⟨-, -, henv, hT, hfoc⟩ :=
    theorem_6_4_4_phi_eq_a h hφ h641 h642 h6410 h6411 h6413 hβ hbd hint
  have hdφa : ∀ x b z z', deriv (fun b' => M.φ x b' z z') b = 1 := fun x b z z' => by
    simp only [hφ, deriv_id'']
  have hdφx : ∀ y a z z', deriv (fun y' => M.φ y' a z z') y = 0 := fun y a z z' => by
    simp only [hφ, deriv_const']
  have hnext : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, ∀ z', M.g t x z ∈ interior M.X :=
    fun t ht z x hx z' => by simpa only [hφ] using (hint t ht z x hx).2 z'
  have hfoc' : ∀ t < M.T, ∀ z, ∀ x ∈ interior M.X, 0 = deriv (fun b => M.u t x z b) (M.g t x z) +
      M.β * ∫ z', deriv (fun y => M.V (t + 1) y z') (M.g t x z) ∂M.Q z := fun t ht z x hx => by
    have := hfoc t ht z x hx
    simp only [focRHS, hφ, deriv_id'', mul_one] at this
    exact this.symm
  refine ⟨fun t ht z x hx => ?_, fun t ht z x hx => ?_⟩
  · rw [hfoc' t (by omega) z x hx]
    congr 2
    refine integral_congr_ae (ae_of_all _ fun z' => ?_)
    have := (henv (t + 1) ht z' _ (hnext t (by omega) z x hx z')).deriv
    simp only [envRHS, hdφx, mul_zero, integral_zero, add_zero] at this
    exact this
  · rw [hfoc' t (by omega) z x hx]
    congr 2
    refine integral_congr_ae (ae_of_all _ fun z' => ?_)
    have := (hT z' _ (hnext t (by omega) z x hx z')).deriv
    rw [← ht] at this
    exact this

end OCModel

end Miao.InfiniteHorizonDP
