/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.TighterLimitMPC

/-!
# A tighter borrowing limit raises the MPC at every horizon (Figure 11.2)

AKMM, §11.3.4, p. 306, Figure 11.2: when the credit limit tightens from `a₁` to `a₂ < a₁`, "their
marginal propensity to consume (the slope of the consumption function) increases". The module
`TighterLimitMPC` proved this for quadratic utility two periods before the end and, when `r = 0`,
at every horizon; its invariant, domination with shift `(a₁ − a₂)`, came back from one step of
backward induction with the smaller shift `(a₁ − a₂)/R`. Here the induction is closed for every
`R ≥ 1` and every horizon, for the expectation as certainty equivalent with factor `θ ≥ 1`, which
contains the book's quadratic case `βR = 1` (`θ = 1`, `cfn_quadratic`).

Write `Δ = a₁ − a₂`, `cₙ` for the loose and `c̃ₙ` for the tight consumption function. The invariant
is a pair:

* **the level bound** `cₙ(x) + (Δ − Δ/R) ≤ c̃ₙ(x + Δ)` (`cta_shift_full`): with `Δ` more cash the
  tight household consumes at least `(1 − 1/R)Δ` more than the loose one, a strengthening of the
  sharp shift bound `ctl_shift_sharp` (it propagates on its own, using `θ ≥ 1`);
* **`Δ`-domination** (`ctl_IncrDom` with shift `Δ`, `cta_incrDom_full`): the tight function shifted
  left by `Δ` rises at least as much as the loose one on every interval.

The level bound caps the gap between the two households' saving at the points the induction
compares at `Δ/R`, so the shift that the Euler equation passes back is at most `R · Δ/R = Δ`, and
`Δ`-domination returns `Δ`-domination (`cta_incr_step`). By concavity of the tight function,
`Δ`-domination gives domination at shift `0`, which is the MPC comparison at every horizon
(`cta_tight_mpc`) and the monotonicity of the fall in consumption (`cta_gap_antitone`), with a
concrete instance at `r = 1` (`cta_example_valid`, `cta_example_mpc`).

The level bound is the integrated form of an identity found from the infinitesimal problem: with
`η = ∂c/∂a` the derivative of consumption in the limit, `η − c′ + (R − 1)/(Rθ)` is nonpositive and
nonincreasing, because unconstrained it is `(1 − c′)·θE[·]` of its next-period value plus the
constant `(R − 1)(1 − θ)/(Rθ)`.

What is left: the factor `θ < 1` (no counterpart in quadratic utility; there the constant above is
positive and `Δ`-domination fails numerically) and CRRA utility beyond one period before the end.
For CRRA no shift domination can serve: one period before the end both households share the same
strictly concave unconstrained consumption function (when the income values differ), so
`τ`-domination already fails there for every `τ > 0`.
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- **The level bound** (expectation, `θ ≥ 1`, every horizon): with `Δ = a₁ − a₂` more cash in hand
the tight household consumes at least `(1 − 1/R)Δ` more than the loose one,
`cₙ(x) + (Δ − Δ/R) ≤ c̃ₙ(x + Δ)`. -/
theorem cta_shift_full (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) {x : ℝ} (hx : H.d ≤ x) :
    H.cons n x + ((H.b - b₂) - (H.b - b₂) / H.R) ≤
      (H.tighten b₂).cons n (x + (H.b - b₂)) := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  set Δ := H.b - b₂ with hΔ
  set e := Δ / H.R with he
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; linarith
  have he0 : 0 ≤ e := div_nonneg hΔ0 hR0.le
  have heΔ : e ≤ Δ := div_le_self hΔ0 hR1
  have hRe : H.R * e = Δ := by rw [he]; field_simp
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he, hΔ]; field_simp; ring
  have hw1 : ∑ i, H.w i = 1 := hV.2.2.2.2.2.2.2.2
  induction n generalizing x with
  | zero => simp only [cons]; linarith
  | succ n ih =>
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n (x + Δ)
    have hg₂ := cfn_cons_good hV₂ n
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set k := (H.tighten b₂).cons (n + 1) (x + Δ)
    have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
    have hint : k < x + Δ + b₂ / H.R := by
      have : c ≤ x + H.b / H.R := hK.1
      linarith
    have hek : k = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + Δ - k) := hK₂.2.2 hint
    have hce : c ≤ H.cont (H.cons n) (x - c) := hK.2.1
    -- the tight household saves more than `e` above the loose one
    have hσ : x - c + e < x + Δ - k := by linarith
    have hge : H.θ * ((∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i)) + (Δ - e)) ≤
        (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + Δ - k) := by
      simp only [cont, CfnHousehold.tighten, hM]
      refine mul_le_mul_of_nonneg_left ?_ hV.2.1.le
      have hsplit : (∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i)) + (Δ - e) =
          ∑ i, H.w i * (H.cons n (H.R * (x - c) + H.y i) + (Δ - e)) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
      rw [hsplit]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hV.2.2.2.2.2.2.2.1 i)
      have hz := cfn_arg_ge hV hs i
      have htd : (H.tighten b₂).d = H.d := rfl
      have hmv : H.R * (x - c) + H.y i + Δ ≤ H.R * (x + Δ - k) + H.y i := by
        nlinarith [mul_le_mul_of_nonneg_left hσ.le hR0.le]
      exact le_trans (ih hz) (hg₂.2.1 (Set.mem_Ici.2 (by rw [htd]; linarith))
        (Set.mem_Ici.2 (by rw [htd]; linarith)) hmv)
    have hcont : H.cont (H.cons n) (x - c) =
        H.θ * ∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i) := by
      simp only [cont, hM]
    have hθa : Δ - e ≤ H.θ * (Δ - e) := by nlinarith
    rw [hcont] at hce
    have : H.θ * ((∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i)) + (Δ - e)) =
        H.θ * ∑ i, H.w i * H.cons n (H.R * (x - c) + H.y i) + H.θ * (Δ - e) := by ring
    linarith

/-- **The domination step** (expectation, any `θ > 0`): `Δ`-domination with `n` periods left and
the level bound with `n + 1` periods left give `Δ`-domination with `n + 1` periods left. -/
theorem cta_incr_step (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (n : ℕ)
    (hP : ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂))
    (hS : ∀ x, H.d ≤ x → H.cons (n + 1) x + ((H.b - b₂) - (H.b - b₂) / H.R) ≤
      (H.tighten b₂).cons (n + 1) (x + (H.b - b₂))) :
    ctl_IncrDom (H.cons (n + 1)) ((H.tighten b₂).cons (n + 1)) H.d (H.b - b₂) := by
  intro x x' hx hxx
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hx' : H.d ≤ x' := le_trans hx hxx
  set Δ := H.b - b₂ with hΔ
  set e := Δ / H.R with he
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; linarith
  have hRe : H.R * e = Δ := by rw [he]; field_simp
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he, hΔ]; field_simp; ring
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hxΔ : H.d ≤ x + Δ := by linarith
  have hK := cfn_cons_kkt hV n x
  have hK' := cfn_cons_kkt hV n x'
  have hT := cfn_cons_kkt hV₂ n (x + Δ)
  have hT' := cfn_cons_kkt hV₂ n (x' + Δ)
  have hHT : ∀ (cn : ℝ → ℝ) s, H.cont cn s = (H.tighten b₂).cont cn s := fun _ _ => rfl
  have hS1 := hS x hx
  have hS2 := hS x' hx'
  set c := H.cons (n + 1) x
  set c' := H.cons (n + 1) x'
  set k := (H.tighten b₂).cons (n + 1) (x + Δ)
  set k' := (H.tighten b₂).cons (n + 1) (x' + Δ)
  have hk'le : k' ≤ x' + Δ + b₂ / H.R := hT'.1
  have hkle1 : k ≤ x + Δ + b₂ / H.R := hT.1
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hK.1 with hcb | hclt
  · -- the loose household is constrained at `x`: the level bound is attained there
    have : k = c + (Δ - e) := by linarith
    linarith
  rcases eq_or_lt_of_le hk'le with hbind | hint'
  · -- the tight household is constrained at `x' + Δ`, hence at `x + Δ`
    have hb' := cfn_binding_initial hV₂ n (by linarith : x + Δ ≤ x' + Δ) hbind
    have hlip := (cfn_cons_good hV (n + 1)).2.2.1 x x' hx hxx
    linarith [hb'.2]
  have hek' : k' = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' + Δ - k') := hT'.2.2 hint'
  have hec : c = H.cont (H.cons n) (x - c) := hK.2.2 hclt
  have hc'le : c' ≤ H.cont (H.cons n) (x' - c') := hK'.2.1
  have hkle : k ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + Δ - k) := hT.2.1
  have hsk : -(b₂ / H.R) ≤ x + Δ - k := cfn_save_ge hT.1
  have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
  have hss' : x - c ≤ x' - c' := (cfn_kkt_mono hV hg hK hK' hxx).2
  -- the saving gap `t` lies in `[0, e]`, by the level bound
  set t := (x + Δ - k) - (x - c) with ht
  have hkc : k ≤ c + Δ := by
    have h1 := cfn_tight_le hV hb₂ hb (n + 1) hxΔ
    have h2 := (cfn_cons_good hV (n + 1)).2.2.1 x (x + Δ) hx (by linarith)
    linarith
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hte : t ≤ e := by rw [ht]; linarith
  have hRt0 : 0 ≤ H.R * t := mul_nonneg hR0.le ht0
  have hRtΔ : H.R * t ≤ Δ := by
    rw [← hRe]; exact mul_le_mul_of_nonneg_left hte hR0.le
  have hm := cfn_cont_mono hV₂ hg₂ (by linarith : -(b₂ / H.R) ≤ (x' - c') + t)
    (by linarith : (x' - c') + t ≤ x' + Δ - k')
  have hdiff := ctl_cont_incr (H.tighten b₂) hM hV.2.1.le hV.2.2.2.2.2.2.2.1
    (f := H.cons n) (g := (H.tighten b₂).cons n) (s := x - c) (s' := x' - c')
    (σ := (x - c) + t) (σ' := (x' - c') + t) (fun i => by
      have hz := cfn_arg_ge hV hs i
      have h1 := ctl_incrDom_le hg₂.2.2.2.1 hP hRt0 hRtΔ hz
        (by nlinarith : H.R * (x - c) + H.y i ≤ H.R * (x' - c') + H.y i)
      have e1 : H.R * (x' - c' + t) + H.y i = H.R * (x' - c') + H.y i + H.R * t := by ring
      have e2 : H.R * (x - c + t) + H.y i = H.R * (x - c) + H.y i + H.R * t := by ring
      change H.cons n _ - H.cons n _ ≤ (H.tighten b₂).cons n _ - (H.tighten b₂).cons n _
      rw [show (H.tighten b₂).R = H.R from rfl, show (H.tighten b₂).y = H.y from rfl, e1, e2]
      exact h1)
  have hxt : x - c + t = x + Δ - k := by rw [ht]; ring
  rw [hxt] at hdiff
  rw [hHT] at hec hc'le
  linarith

/-- **`Δ`-domination at every horizon** (expectation, `θ ≥ 1`, any `R ≥ 1`). -/
theorem cta_incrDom_full (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) :
    ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂) := by
  induction n with
  | zero => exact ctl_incrDom_zero
  | succ n ih =>
    exact cta_incr_step hV hb₂ hb hM n ih fun x hx => cta_shift_full hV hb₂ hb hM hθ (n + 1) hx

/-- **AKMM, p. 306: a tighter limit raises the MPC at every horizon** (the expectation as certainty
equivalent with `θ ≥ 1`, which contains quadratic utility with `βR = 1`; any `r ≥ 0`): for every
number of periods left, on every interval of cash in hand the tight household's consumption rises
at least as much as the loose household's. -/
theorem cta_tight_mpc (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x)
    (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x := by
  have h := ctl_incrDom_le (cfn_cons_good (cfn_tighten_valid hV hb₂ hb) n).2.2.2.1
    (cta_incrDom_full hV hb₂ hb hM hθ n) le_rfl (by linarith : (0 : ℝ) ≤ H.b - b₂) hx hxx
  simpa only [add_zero] using h

/-- **The fall in consumption shrinks as wealth grows** (expectation, `θ ≥ 1`, every horizon, any
`r ≥ 0`): `cₙ(x) − c̃ₙ(x)` is nonincreasing — the form in which Figure 11.2 shows the MPC
comparison. -/
theorem cta_gap_antitone (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hθ : 1 ≤ H.θ) (n : ℕ) :
    AntitoneOn (fun x => H.cons n x - (H.tighten b₂).cons n x) (Set.Ici H.d) := by
  intro x hx x' _ hxx
  have := cta_tight_mpc hV hb₂ hb hM hθ n hx hxx
  simp only
  linarith

/-- **AKMM, p. 306, the book's case**: for the quadratic household (`βR = 1`, `M` the expectation,
`θ = 1`) a tighter limit raises the MPC on every interval at every horizon, for every `r ≥ 0`. -/
theorem cta_quadratic_tight_mpc {w y : ι → ℝ} {R b d ymax : ℝ}
    (hV : (cfn_quadratic w y R b d ymax).Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ b) (n : ℕ)
    {x x' : ℝ} (hx : d ≤ x) (hxx : x ≤ x') :
    (cfn_quadratic w y R b d ymax).cons n x' - (cfn_quadratic w y R b d ymax).cons n x ≤
      ((cfn_quadratic w y R b d ymax).tighten b₂).cons n x' -
        ((cfn_quadratic w y R b d ymax).tighten b₂).cons n x :=
  cta_tight_mpc hV hb₂ hb (ctl_quadratic_linear _ _ _ _ _ _) le_rfl n hx hxx

/-- **A concrete instance with `r = 1`**: the quadratic household with income `1` or `3` with equal
probability, `R = 2`, `a = 1/2`, `d = 1/2`, satisfies the standing assumptions. -/
theorem cta_example_valid :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).Valid := by
  refine cfn_quadratic_valid (fun _ => by norm_num) (by simp) (by norm_num) (by norm_num)
    (by norm_num) (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- **The instance**: for that household (`R = 2`), removing the borrowing limit's slack entirely
(`a₂ = 0`) raises the MPC on every interval at every horizon. -/
theorem cta_example_mpc (n : ℕ) {x x' : ℝ} (hx : 1 / 2 ≤ x) (hxx : x ≤ x') :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).cons n x' -
        (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).cons n x ≤
      ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x' -
        ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 2 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x :=
  cta_quadratic_tight_mpc cta_example_valid le_rfl (by norm_num) n hx hxx

end AKMM.Consumption
