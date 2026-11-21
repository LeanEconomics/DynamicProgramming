/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.CSModel

/-!
# §6.6.2: monotonicity, concavity and the policy functions

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSProperties`), namespace renamed.

Miao, §6.6.2, p. 188 and Exercise 5, p. 189, the properties that need no derivatives. Under the
standing hypotheses `CSModel.Basic`:

* `strictMonoOn_v`: `v_n(·, z)` is strictly increasing on `[0, ∞)`;
* `strictConcaveOn_v`: `v_n(·, z)` is strictly concave on `[0, ∞)` (the book's "inherits the
  basic properties of `u`"; proved directly since Theorem 6.4.3 does not apply,
  `CSModel.not_assumption6410`);
* `sav_unique`: the maximizer is unique, so `s_n` and `g_n` are the policy functions;
* `continuousOn_sav`, `continuousOn_cons`: `s_n`, `g_n` are continuous on `[0, ∞) × Z`
  (single-valued u.h.c. policy, `continuousOn_g_core`);
* `monotoneOn_sav`, `monotoneOn_cons`: `s_n(·, z)` and `g_n(·, z)` are (weakly) increasing, by
  an exchange argument (strict concavity of `u` for `s_n`, of the continuation value for `g_n`);
  no differentiability is used, so these also hold without the Inada condition
  (Exercise 10).

The continuation value `ev n z s = ∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)` is strictly concave on
`[0, ∞)` (`strictConcaveOn_ev`). `cs_exchange` is the exchange inequality for strictly concave
functions.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

/-- The exchange inequality: if `f` is strictly concave, `a < b < d` and `a + d = b + c`, then
`f(a) + f(d) < f(b) + f(c)`. -/
theorem cs_exchange {S : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ S f) {a b c d : ℝ}
    (ha : a ∈ S) (hd : d ∈ S) (hab : a < b) (hbd : b < d)
    (hs : a + d = b + c) : f a + f d < f b + f c := by
  have had : a < d := hab.trans hbd
  have hda : 0 < d - a := sub_pos.2 had
  set θ := (d - b) / (d - a) with hθ
  set η := (b - a) / (d - a) with hη
  have hθp : 0 < θ := div_pos (sub_pos.2 hbd) hda
  have hηp : 0 < η := div_pos (sub_pos.2 hab) hda
  have hsum : θ + η = 1 := by rw [hθ, hη, ← add_div]; field_simp; ring
  have hb : θ * a + η * d = b := by rw [hθ, hη]; field_simp; ring
  have hc : η * a + θ * d = c := by
    have : η * a + θ * d = (θ + η) * (a + d) - (θ * a + η * d) := by ring
    rw [this, hsum, hb]; linarith
  have h1 := hf.2 ha hd had.ne hθp hηp hsum
  have h2 := hf.2 ha hd had.ne hηp hθp (by linarith)
  simp only [smul_eq_mul] at h1 h2
  rw [hb] at h1
  rw [hc] at h2
  have key : θ * f a + η * f d + (η * f a + θ * f d) = f a + f d := by
    linear_combination (f a + f d) * hsum
  linarith

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z] (M : CSModel Z)

/-- The **continuation value** `∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)` after saving `s`. -/
noncomputable def ev (n : ℕ) (z : Z) (s : ℝ) : ℝ :=
  ∫ z', M.v n (M.ρ z' * s + M.w z') z' ∂M.Q z

theorem obj_eq_ev (n : ℕ) {x : ℝ} (z : Z) {s : ℝ} (hs : s ≤ x) :
    M.obj n x z s = M.u (x - s) + M.β * M.ev n z s :=
  M.obj_eq n z hs

variable {M} [MetricSpace Z]

/-- The next states after saving `s ≥ 0` are in `[0, ∞)`. -/
theorem next_nonneg (h : M.Basic) {s : ℝ} (hs : 0 ≤ s) (z' : Z) : 0 ≤ M.ρ z' * s + M.w z' :=
  add_nonneg (mul_nonneg (h.ρ_pos z').le hs) (h.w_pos z').le

variable [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q]

/-- Strict concavity of `v_n(·, z′)` for every `z′` makes the continuation value strictly
concave on `[0, ∞)`. -/
theorem strictConcaveOn_ev (h : M.Basic) {n : ℕ}
    (hv : ∀ z', StrictConcaveOn ℝ (Set.Ici 0) fun x => M.v n x z') (z : Z) :
    StrictConcaveOn ℝ (Set.Ici 0) (M.ev n z) := by
  refine ⟨convex_Ici 0, fun s₁ hs₁ s₂ hs₂ hne θ η hθ hη hsum => ?_⟩
  have i1 := integrable_next h n (next_nonneg h hs₁) z
  have i2 := integrable_next h n (next_nonneg h hs₂) z
  have hs₃ : (0 : ℝ) ≤ θ • s₁ + η • s₂ :=
    (convex_Ici 0) hs₁ hs₂ hθ.le hη.le hsum
  have i3 := integrable_next h n (next_nonneg h hs₃) z
  simp only [smul_eq_mul, ev]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul θ)
    (i2.const_mul η)]
  refine integral_lt_integral_of_lt ((i1.const_mul θ).add (i2.const_mul η)) i3 fun z' => ?_
  have hp₁ := next_nonneg h hs₁ z'
  have hp₂ := next_nonneg h hs₂ z'
  have hne' : M.ρ z' * s₁ + M.w z' ≠ M.ρ z' * s₂ + M.w z' := fun he =>
    hne (mul_left_cancel₀ (h.ρ_pos z').ne' (by linarith))
  have := (hv z').2 hp₁ hp₂ hne' hθ hη hsum
  simp only [smul_eq_mul] at this
  have heq : θ * (M.ρ z' * s₁ + M.w z') + η * (M.ρ z' * s₂ + M.w z') =
      M.ρ z' * (θ * s₁ + η * s₂) + M.w z' := by
    linear_combination M.w z' * hsum
  rw [heq] at this
  exact this

/-- **`v_n(·, z)` is strictly increasing** on `[0, ∞)` (Miao, p. 188). -/
theorem strictMonoOn_v (h : M.Basic) (n : ℕ) (z : Z) :
    StrictMonoOn (fun x => M.v n x z) (Set.Ici 0) := by
  cases n with
  | zero => exact h.u_mono
  | succ n =>
    intro x hx x' hx' hxx'
    obtain ⟨hmem, hval⟩ := sav_mem h n hx z
    set s := M.sav (n + 1) x z
    have hs' : s ∈ Set.Icc 0 x' := ⟨hmem.1, hmem.2.trans hxx'.le⟩
    change M.v (n + 1) x z < M.v (n + 1) x' z
    rw [← hval]
    refine lt_of_lt_of_le ?_ (obj_le h n hs')
    rw [M.obj_eq_ev _ _ hmem.2, M.obj_eq_ev _ _ hs'.2]
    have : M.u (x - s) < M.u (x' - s) := h.u_mono (sub_nonneg.2 hmem.2)
      (sub_nonneg.2 hs'.2) (by linarith)
    linarith

/-- **`v_n(·, z)` is strictly concave** on `[0, ∞)` (Miao, p. 188), for every `n` and `z`. -/
theorem strictConcaveOn_v (h : M.Basic) (n : ℕ) :
    ∀ z, StrictConcaveOn ℝ (Set.Ici 0) fun x => M.v n x z := by
  induction n with
  | zero => intro z; exact h.u_conc
  | succ n ih =>
    intro z
    have hev := strictConcaveOn_ev h ih z
    refine ⟨convex_Ici 0, fun x₁ hx₁ x₂ hx₂ hne θ η hθ hη hsum => ?_⟩
    obtain ⟨hm₁, hv₁⟩ := sav_mem h n hx₁ z
    obtain ⟨hm₂, hv₂⟩ := sav_mem h n hx₂ z
    set s₁ := M.sav (n + 1) x₁ z
    set s₂ := M.sav (n + 1) x₂ z
    simp only [smul_eq_mul]
    have hs : s₁ ∈ Set.Ici (0 : ℝ) := hm₁.1
    have hs₂ : s₂ ∈ Set.Ici (0 : ℝ) := hm₂.1
    have hc₁ : x₁ - s₁ ∈ Set.Ici (0 : ℝ) := sub_nonneg.2 hm₁.2
    have hc₂ : x₂ - s₂ ∈ Set.Ici (0 : ℝ) := sub_nonneg.2 hm₂.2
    have hfeas : θ * s₁ + η * s₂ ∈ Set.Icc 0 (θ * x₁ + η * x₂) :=
      ⟨by nlinarith [hm₁.1, hm₂.1], by nlinarith [hm₁.2, hm₂.2]⟩
    have hle := obj_le h n (z := z) hfeas
    rw [M.obj_eq_ev _ _ hfeas.2] at hle
    rw [← hv₁, ← hv₂, M.obj_eq_ev _ _ hm₁.2, M.obj_eq_ev _ _ hm₂.2]
    have hcomb : θ * x₁ + η * x₂ - (θ * s₁ + η * s₂) = θ * (x₁ - s₁) + η * (x₂ - s₂) := by ring
    rw [hcomb] at hle
    have hβ := h.β_pos
    by_cases hss : s₁ = s₂
    · have hcne : x₁ - s₁ ≠ x₂ - s₂ := fun he => hne (by rw [hss] at he; linarith)
      have hu := h.u_conc.2 hc₁ hc₂ hcne hθ hη hsum
      simp only [smul_eq_mul] at hu
      have hevs : θ * M.ev n z s₁ + η * M.ev n z s₂ = M.ev n z (θ * s₁ + η * s₂) := by
        have hθη : θ * s₁ + η * s₁ = s₁ := by rw [← add_mul, hsum, one_mul]
        rw [← hss, ← add_mul, hsum, one_mul, hθη]
      nlinarith
    · have hu := h.u_conc.concaveOn.2 hc₁ hc₂ hθ.le hη.le hsum
      have he := hev.2 hs hs₂ hss hθ hη hsum
      simp only [smul_eq_mul] at hu he
      nlinarith

/-- **The optimal saving is unique** (Miao, p. 188): any feasible `s` attaining `v_{n+1}(x, z)` is
`s_{n+1}(x, z)`. -/
theorem sav_unique (h : M.Basic) (n : ℕ) {x : ℝ} {z : Z} {s : ℝ} (hs : s ∈ Set.Icc 0 x)
    (hval : M.obj n x z s = M.v (n + 1) x z) : s = M.sav (n + 1) x z := by
  have hx : 0 ≤ x := hs.1.trans hs.2
  obtain ⟨hm, hv⟩ := sav_mem h n hx z
  set s' := M.sav (n + 1) x z
  by_contra hne
  have hh : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hev := (strictConcaveOn_ev h (strictConcaveOn_v h n) z).2 hs.1 hm.1 hne hp hp hh
  have hu := h.u_conc.concaveOn.2 (sub_nonneg.2 hs.2 : x - s ∈ Set.Ici (0 : ℝ))
    (sub_nonneg.2 hm.2 : x - s' ∈ Set.Ici (0 : ℝ)) hp.le hp.le hh
  simp only [smul_eq_mul] at hev hu
  have hfeas : 1 / 2 * s + 1 / 2 * s' ∈ Set.Icc 0 x :=
    ⟨by linarith [hs.1, hm.1], by linarith [hs.2, hm.2]⟩
  have hle := obj_le h n (z := z) hfeas
  rw [M.obj_eq_ev _ _ hfeas.2] at hle
  rw [M.obj_eq_ev _ _ hs.2] at hval
  rw [M.obj_eq_ev _ _ hm.2] at hv
  have : x - (1 / 2 * s + 1 / 2 * s') = 1 / 2 * (x - s) + 1 / 2 * (x - s') := by ring
  rw [this] at hle
  nlinarith [h.β_pos]

/-- The policy correspondence of `toOC (n + 1)` at date `0` is single-valued. -/
theorem G_subsingleton (h : M.Basic) (n : ℕ) :
    ∀ x ∈ (M.toOC (n + 1)).X, ∀ z, ((M.toOC (n + 1)).G 0 x z).Subsingleton := by
  intro x _ z a ha b hb
  rw [mem_G] at ha hb
  rw [sav_unique h n ha.1 ha.2, sav_unique h n hb.1 hb.2]

/-- **`s_n` is continuous** on `[0, ∞) × Z` (Miao, p. 188; Theorem 6.4.3's continuity of the
single-valued policy). -/
theorem continuousOn_sav (h : M.Basic) (n : ℕ) :
    ContinuousOn (fun p : ℝ × Z => M.sav n p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  cases n with
  | zero => exact continuousOn_const
  | succ n =>
    have : IsMarkovKernel (M.toOC (n + 1)).Q := ‹IsMarkovKernel M.Q›
    exact OCModel.continuousOn_g_core (standing h (n + 1)) (Nat.succ_pos n) (G_subsingleton h n)

/-- **`g_n` is continuous** on `[0, ∞) × Z` (Miao, p. 188). -/
theorem continuousOn_cons (h : M.Basic) (n : ℕ) :
    ContinuousOn (fun p : ℝ × Z => M.cons n p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) :=
  continuous_fst.continuousOn.sub (continuousOn_sav h n)

/-- `0 ≤ s_n(x) ≤ x` for `x ≥ 0`. -/
theorem sav_mem' (h : M.Basic) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (z : Z) :
    M.sav n x z ∈ Set.Icc 0 x := by
  cases n with
  | zero => exact ⟨le_rfl, hx⟩
  | succ n => exact (sav_mem h n hx z).1

/-- **`s_n(·, z)` is increasing** (weakly) on `[0, ∞)` (Miao, p. 188), by the exchange argument
with the strict concavity of `u`. -/
theorem monotoneOn_sav (h : M.Basic) (n : ℕ) (z : Z) :
    MonotoneOn (fun x => M.sav n x z) (Set.Ici 0) := by
  cases n with
  | zero => exact fun _ _ _ _ _ => le_rfl
  | succ n =>
    intro x hx x' hx' hxx'
    change M.sav (n + 1) x z ≤ M.sav (n + 1) x' z
    rcases hxx'.eq_or_lt with rfl | hlt
    · exact le_rfl
    obtain ⟨hm, hv⟩ := sav_mem h n hx z
    obtain ⟨hm', hv'⟩ := sav_mem h n hx' z
    set s := M.sav (n + 1) x z
    set s' := M.sav (n + 1) x' z
    by_contra hcon
    push Not at hcon
    have hf1 : s' ∈ Set.Icc 0 x := ⟨hm'.1, by linarith [hm.2]⟩
    have hf2 : s ∈ Set.Icc 0 x' := ⟨hm.1, by linarith [hm.2]⟩
    have h1 := obj_le h n (z := z) hf1
    have h2 := obj_le h n (z := z) hf2
    rw [← hv, M.obj_eq_ev _ _ hf1.2, M.obj_eq_ev _ _ hm.2] at h1
    rw [← hv', M.obj_eq_ev _ _ hf2.2, M.obj_eq_ev _ _ hm'.2] at h2
    have hx := cs_exchange h.u_conc (sub_nonneg.2 hm.2 : x - s ∈ Set.Ici (0 : ℝ))
      (sub_nonneg.2 hm'.2 : x' - s' ∈ Set.Ici (0 : ℝ)) (b := x - s') (c := x' - s)
      (by linarith) (by linarith) (by ring)
    linarith

/-- **`g_n(·, z)` is increasing** (weakly) on `[0, ∞)` (Miao, p. 188), by the exchange argument
with the strict concavity of the continuation value. -/
theorem monotoneOn_cons (h : M.Basic) (n : ℕ) (z : Z) :
    MonotoneOn (fun x => M.cons n x z) (Set.Ici 0) := by
  cases n with
  | zero => exact fun _ _ _ _ h => by simpa [cons, sav] using h
  | succ n =>
    intro x hx x' hx' hxx'
    change M.cons (n + 1) x z ≤ M.cons (n + 1) x' z
    rcases hxx'.eq_or_lt with rfl | hlt
    · exact le_rfl
    obtain ⟨hm, hv⟩ := sav_mem h n hx z
    obtain ⟨hm', hv'⟩ := sav_mem h n hx' z
    simp only [cons]
    set s := M.sav (n + 1) x z
    set s' := M.sav (n + 1) x' z
    by_contra hcon
    push Not at hcon
    have hev := strictConcaveOn_ev h (strictConcaveOn_v h n) z
    -- at `x` consume `x' − s'`, at `x'` consume `x − s`
    have hf1 : x - (x' - s') ∈ Set.Icc 0 x := ⟨by linarith [hm.1], by linarith [hm'.2]⟩
    have hf2 : x' - (x - s) ∈ Set.Icc 0 x' := ⟨by linarith [hm.1], by linarith [hm.2]⟩
    have h1 := obj_le h n (z := z) hf1
    have h2 := obj_le h n (z := z) hf2
    rw [← hv, M.obj_eq_ev _ _ hf1.2, M.obj_eq_ev _ _ hm.2] at h1
    rw [← hv', M.obj_eq_ev _ _ hf2.2, M.obj_eq_ev _ _ hm'.2] at h2
    have h3 : x - (x - (x' - s')) = x' - s' := by ring
    have h4 : x' - (x' - (x - s)) = x - s := by ring
    rw [h3] at h1
    rw [h4] at h2
    have hx := cs_exchange hev (hm.1 : s ∈ Set.Ici (0 : ℝ)) (hm'.1 : s' ∈ Set.Ici (0 : ℝ))
      (b := x - (x' - s')) (c := x' - (x - s)) (by linarith) (by linarith) (by ring)
    nlinarith [h.β_pos]

end CSModel

end Miao.IncompleteMarkets
