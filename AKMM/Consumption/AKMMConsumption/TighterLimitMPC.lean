/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.ConsumptionShape

/-!
# A tighter borrowing limit raises the MPC with more periods left (Figure 11.2)

AKMM, §11.3.4, p. 306, Figure 11.2: when the credit limit tightens from `a₁` to `a₂ < a₁`, "their
marginal propensity to consume (the slope of the consumption function) increases". In the
finite-horizon household of `ConsumptionShape` (`CfnHousehold`) this is the statement that on every
interval of cash in hand the tight household's consumption rises at least as much as the loose
household's, i.e. that the fall in consumption `cₙ(x) − c̃ₙ(x)` is nonincreasing in `x`. The module
`ConsumptionShape` proved it one period before the end (`cfn_tight_mpc_last`). Here:

* **The sharp shift bound** (any certainty equivalent `M`): with `(a₁ − a₂)/R` more cash the tight
  household consumes at least as much as the loose one, `cₙ(x) ≤ c̃ₙ(x + (a₁ − a₂)/R)`
  (`ctl_shift_sharp`), so a tighter limit lowers consumption by at most `(a₁ − a₂)/R`, the amount
  it removes from the budget, at every horizon (`ctl_gap_le`).
* **The induction step** (quadratic utility: `M` the expectation, any `θ`, any `R ≥ 1`). Call
  `(cₙ, c̃ₙ)` *`τ`-dominated* if the tight function shifted left by `τ` rises at least as much as
  the loose one on every interval (`ctl_IncrDom`). If the period-`n` functions are
  `(a₁ − a₂)/R`-dominated, the tight MPC is at least the loose MPC on every interval with `n + 1`
  periods left (`ctl_mpc_step`); and `(a₁ − a₂)`-domination at `n` gives `(a₁ − a₂)/R`-domination
  at `n + 1` (`ctl_incr_step`). The proof follows Carroll–Holm–Kimball's backward induction, with
  the counterconcavity comparison of marginal values replaced by this shifted comparison of
  consumption functions, which is what the Euler equation passes back.
* **Two periods before the end**, for every `R ≥ 1` and `θ > 0` (`ctl_tight_mpc_two`).
* **Every horizon when `r = 0`** (`R = 1`; `ctl_tight_mpc_R_one`), with a concrete instance
  (`ctl_example_R_one_valid`, `ctl_example_mpc`).

What is left: for quadratic utility with `R > 1` and three or more periods left, the domination
step consumes `(a₁ − a₂)`-domination and returns only `(a₁ − a₂)/R`-domination, so the induction
does not close and the comparison is proved at horizons `1` and `2` only. For CRRA (the power mean)
the step's use of the linearity of the expectation (`ctl_cont_incr`) is not available, so beyond
`cfn_tight_mpc_last` nothing is proved. Carroll–Holm–Kimball's concavification theorem adds
constraints one date at a time in reverse chronological order; tightening the same limit at every
date is not of that form, so it does not settle these cases either. The quadratic case at every
horizon is closed in `TighterLimitAllHorizons` (`cta_tight_mpc`), with a level bound added to the
invariant.
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- `(f, g)` is `τ`-dominated on `[d, ∞)`: on every interval `[z, z']` the function `g` shifted
left by `τ` rises at least as much as `f`. With `f` the loose and `g` the tight consumption function
and `τ = 0` this is the MPC comparison of AKMM p. 306. -/
def ctl_IncrDom (f g : ℝ → ℝ) (d τ : ℝ) : Prop :=
  ∀ z z', d ≤ z → z ≤ z' → f z' - f z ≤ g (z' + τ) - g (z + τ)

/-- For a concave function, the rise over `[z, z']` shrinks as the interval is moved to the right:
`g(z' + b) − g(z + b) ≤ g(z' + a) − g(z + a)` for `0 ≤ a ≤ b`. -/
theorem ctl_concave_incr {g : ℝ → ℝ} {d z z' a b : ℝ} (hg : ConcaveOn ℝ (Set.Ici d) g)
    (hz : d ≤ z) (hzz : z ≤ z') (ha : 0 ≤ a) (hab : a ≤ b) :
    g (z' + b) - g (z + b) ≤ g (z' + a) - g (z + a) := by
  set D := (b - a) + (z' - z) with hD
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ D) with h0 | hpos
  · have h1 : b = a := by linarith
    have h2 : z' = z := by linarith
    rw [h1, h2]
  set lam := (z' - z) / D with hlam
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) hpos.le
  have hl1 : lam ≤ 1 := by rw [div_le_one hpos]; linarith
  have hp : z + a ∈ Set.Ici d := Set.mem_Ici.2 (by linarith)
  have hq : z' + b ∈ Set.Ici d := Set.mem_Ici.2 (by linarith)
  have hc1 := hg.2 hp hq hl0 (by linarith : 0 ≤ 1 - lam) (by ring)
  have hc2 := hg.2 hp hq (by linarith : 0 ≤ 1 - lam) hl0 (by ring)
  simp only [smul_eq_mul] at hc1 hc2
  have e1 : lam * (z + a) + (1 - lam) * (z' + b) = z + b := by
    have : lam * D = z' - z := by rw [hlam]; field_simp
    linear_combination -this
  have e2 : (1 - lam) * (z + a) + lam * (z' + b) = z' + a := by
    have : lam * D = z' - z := by rw [hlam]; field_simp
    linear_combination this
  rw [e1] at hc1
  rw [e2] at hc2
  linarith

/-- Domination at a larger shift gives domination at every smaller nonnegative shift, for a concave
tight function. -/
theorem ctl_incrDom_le {f g : ℝ → ℝ} {d τ a : ℝ} (hg : ConcaveOn ℝ (Set.Ici d) g)
    (hP : ctl_IncrDom f g d τ) (ha : 0 ≤ a) (haτ : a ≤ τ) {z z' : ℝ} (hz : d ≤ z)
    (hzz : z ≤ z') : f z' - f z ≤ g (z' + a) - g (z + a) :=
  le_trans (hP z z' hz hzz) (ctl_concave_incr hg hz hzz ha haτ)

omit [Fintype ι] in
/-- With the expectation as certainty equivalent, the Euler right-hand side passes comparisons of
increments through: if every state's increment of `g` dominates that of `f`, so does the Euler
right-hand side's. -/
theorem ctl_cont_incr (H : CfnHousehold ι) [Fintype ι] (hM : ∀ z, H.M z = ∑ i, H.w i * z i)
    (hθ : 0 ≤ H.θ) (hw : ∀ i, 0 ≤ H.w i) {f g : ℝ → ℝ} {s s' σ σ' : ℝ}
    (h : ∀ i, f (H.R * s' + H.y i) - f (H.R * s + H.y i) ≤
      g (H.R * σ' + H.y i) - g (H.R * σ + H.y i)) :
    H.cont f s' - H.cont f s ≤ H.cont g σ' - H.cont g σ := by
  simp only [cont, hM]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hθ
  rw [← mul_sub, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (h i) (hw i)

/-- **The sharp shift bound.** With `(a₁ − a₂)/R` more cash in hand the tight household consumes
at least as much as the loose one, at every horizon (any certainty equivalent). -/
theorem ctl_shift_sharp (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : H.cons n x ≤ (H.tighten b₂).cons n (x + (H.b - b₂) / H.R) := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have he0 : 0 ≤ (H.b - b₂) / H.R := div_nonneg (by linarith) hR0.le
  have hbe : b₂ / H.R + (H.b - b₂) / H.R = H.b / H.R := by field_simp; ring
  induction n generalizing x with
  | zero => simp only [cons]; linarith
  | succ n ih =>
    set e := (H.b - b₂) / H.R with he
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n (x + e)
    have hg₂ := cfn_cons_good hV₂ n
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set c₂ := (H.tighten b₂).cons (n + 1) (x + e)
    have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
    have hint : c₂ < x + e + b₂ / H.R := by linarith [hK.1]
    have he₂ : c₂ = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + e - c₂) := hK₂.2.2 hint
    have hge : H.cont (H.cons n) (x - c) ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n)
        (x + e - c₂) := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => (cfn_cons_good hV n).1 _
        (cfn_arg_ge hV hs i)) fun i => ?_) hV.2.1.le
      have hsi := cfn_arg_ge hV hs i
      have htd : (H.tighten b₂).d = H.d := rfl
      have hmv : H.R * (x - c) + H.y i + e ≤ H.R * (x + e - c₂) + H.y i := by nlinarith
      refine le_trans (ih hsi) (hg₂.2.1 (Set.mem_Ici.2 (by rw [htd]; linarith))
        (Set.mem_Ici.2 (by rw [htd]; linarith)) hmv)
    linarith [hK.2.1]

/-- **AKMM, p. 306: a tighter limit lowers consumption by at most `(a₁ − a₂)/R`**, the amount it
removes from the current budget, at every horizon: `0 ≤ cₙ(x) − c̃ₙ(x) ≤ (a₁ − a₂)/R`. -/
theorem ctl_gap_le (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : 0 ≤ H.cons n x - (H.tighten b₂).cons n x ∧
      H.cons n x - (H.tighten b₂).cons n x ≤ (H.b - b₂) / H.R := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have he0 : 0 ≤ (H.b - b₂) / H.R := div_nonneg (by linarith) hR0.le
  have h1 := cfn_tight_le hV hb₂ hb n hx
  have h2 := ctl_shift_sharp hV hb₂ hb n hx
  have h3 := (cfn_cons_good hV₂ n).2.2.1 x (x + (H.b - b₂) / H.R) hx (by linarith)
  constructor <;> linarith

omit [Fintype ι] in
/-- In the last period both households eat their cash: the pair `(c₀, c̃₀)` is `τ`-dominated for
every `τ`. -/
theorem ctl_incrDom_zero {b₂ τ : ℝ} :
    ctl_IncrDom (H.cons 0) ((H.tighten b₂).cons 0) H.d τ := by
  intro z z' _ _
  simp only [cons]
  linarith

/-- **The MPC induction step** (quadratic utility). If with `n` periods left the pair of
consumption functions is `(a₁ − a₂)/R`-dominated, then with `n + 1` periods left the tight MPC is at
least the loose MPC on every interval of cash in hand. -/
theorem ctl_mpc_step (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (n : ℕ)
    (hP : ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d ((H.b - b₂) / H.R)) {x x' : ℝ}
    (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons (n + 1) x' - H.cons (n + 1) x ≤
      (H.tighten b₂).cons (n + 1) x' - (H.tighten b₂).cons (n + 1) x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hx' : H.d ≤ x' := le_trans hx hxx
  set e := (H.b - b₂) / H.R with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) hR0.le
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he]; field_simp; ring
  have heR : e / H.R ≤ e := div_le_self he0 hR1
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hK := cfn_cons_kkt hV n x
  have hK' := cfn_cons_kkt hV n x'
  have hT := cfn_cons_kkt hV₂ n x
  have hT' := cfn_cons_kkt hV₂ n x'
  have hHT : ∀ (cn : ℝ → ℝ) s, H.cont cn s = (H.tighten b₂).cont cn s := fun _ _ => rfl
  set c := H.cons (n + 1) x
  set c' := H.cons (n + 1) x'
  set k := (H.tighten b₂).cons (n + 1) x
  set k' := (H.tighten b₂).cons (n + 1) x'
  have hk'le : k' ≤ x' + b₂ / H.R := hT'.1
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hk'le with hbind | hint'
  · -- the tight household is constrained at `x'`, hence at `x`
    have hb' := cfn_binding_initial hV₂ n hxx hbind
    have hlip := (cfn_cons_good hV (n + 1)).2.2.1 x x' hx hxx
    linarith [hb'.2]
  -- the tight household is unconstrained at `x'`, hence so is the loose one
  have hek' : k' = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' - k') := hT'.2.2 hint'
  have hc'lt : c' < x' + H.b / H.R := by
    by_contra hge
    push Not at hge
    have := cfn_tight_binds hV hb₂ hb n x' (le_antisymm hK'.1 hge)
    linarith
  have hec' : c' = H.cont (H.cons n) (x' - c') := hK'.2.2 hc'lt
  have hs' : -(H.b / H.R) ≤ x' - c' := cfn_save_ge hK'.1
  have hkc' : k' ≤ c' := cfn_tight_le hV hb₂ hb (n + 1) hx'
  -- the gap at `x'` is at most `e/R`
  have hγ' : c' - k' ≤ e / H.R := by
    by_contra hgt
    push Not at hgt
    have hRγ : e ≤ H.R * (c' - k') := by
      have := mul_lt_mul_of_pos_left hgt hR0
      rw [mul_div_cancel₀ _ hR0.ne'] at this; linarith
    have hcmp : H.cont (H.cons n) (x' - c') ≤
        (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' - k') := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => hg.1 _ (cfn_arg_ge hV hs' i))
        fun i => ?_) hV.2.1.le
      have hz := cfn_arg_ge hV hs' i
      have htd : (H.tighten b₂).d = H.d := rfl
      have hmv : H.R * (x' - c') + H.y i + e ≤ H.R * (x' - k') + H.y i := by nlinarith
      exact le_trans (ctl_shift_sharp hV hb₂ hb n hz) (hg₂.2.1
        (Set.mem_Ici.2 (by rw [htd]; linarith)) (Set.mem_Ici.2 (by rw [htd]; linarith)) hmv)
    have : 0 ≤ e / H.R := div_nonneg he0 hR0.le
    linarith
  rcases eq_or_lt_of_le hK.1 with hcb | hclt
  · -- the loose household is constrained at `x`, hence so is the tight one: the gap is `e`
    have hk := cfn_tight_binds hV hb₂ hb n x hcb
    have : c - k = e := by
      have hk' : k = x + b₂ / H.R := hk
      rw [hcb, hk']; linarith
    linarith
  -- the loose household is unconstrained at `x`
  have hec : c = H.cont (H.cons n) (x - c) := hK.2.2 hclt
  have hkle : k ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - k) := hT.2.1
  have hsk : -(b₂ / H.R) ≤ x - k := cfn_save_ge hT.1
  have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
  have hss' : x - c ≤ x' - c' := (cfn_kkt_mono hV hg hK hK' hxx).2
  have hkc : k ≤ c := cfn_tight_le hV hb₂ hb (n + 1) hx
  set γ' := c' - k' with hγ'def
  have hγ'0 : 0 ≤ γ' := by linarith
  have hm := cfn_cont_mono hV₂ hg₂ hsk (by linarith : x - k ≤ (x - c) + γ')
  have hRγ0 : 0 ≤ H.R * γ' := mul_nonneg hR0.le hγ'0
  have hRγe : H.R * γ' ≤ e := by
    have := mul_le_mul_of_nonneg_left hγ' hR0.le
    rwa [mul_div_cancel₀ _ hR0.ne'] at this
  have hdiff := ctl_cont_incr (H.tighten b₂) hM hV.2.1.le hV.2.2.2.2.2.2.2.1
    (f := H.cons n) (g := (H.tighten b₂).cons n) (s := x - c) (s' := x' - c')
    (σ := (x - c) + γ') (σ' := (x' - c') + γ') (fun i => by
      have hz := cfn_arg_ge hV hs i
      have h1 := ctl_incrDom_le hg₂.2.2.2.1 hP hRγ0 hRγe hz
        (by nlinarith : H.R * (x - c) + H.y i ≤ H.R * (x' - c') + H.y i)
      have e1 : H.R * (x' - c' + γ') + H.y i = H.R * (x' - c') + H.y i + H.R * γ' := by ring
      have e2 : H.R * (x - c + γ') + H.y i = H.R * (x - c) + H.y i + H.R * γ' := by ring
      change H.cons n _ - H.cons n _ ≤ (H.tighten b₂).cons n _ - (H.tighten b₂).cons n _
      rw [show (H.tighten b₂).R = H.R from rfl, show (H.tighten b₂).y = H.y from rfl, e1, e2]
      exact h1)
  have hx'k' : x' - c' + γ' = x' - k' := by rw [hγ'def]; ring
  rw [hx'k'] at hdiff
  rw [hHT] at hec hec'
  linarith

/-- **The domination step** (quadratic utility): `(a₁ − a₂)`-domination with `n` periods left gives
`(a₁ − a₂)/R`-domination with `n + 1` periods left. -/
theorem ctl_incr_step (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (n : ℕ)
    (hP : ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂)) :
    ctl_IncrDom (H.cons (n + 1)) ((H.tighten b₂).cons (n + 1)) H.d ((H.b - b₂) / H.R) := by
  intro x x' hx hxx
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hx' : H.d ≤ x' := le_trans hx hxx
  set e := (H.b - b₂) / H.R with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) hR0.le
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he]; field_simp; ring
  have hRe : H.R * e = H.b - b₂ := by rw [he]; field_simp
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hxe : H.d ≤ x + e := by linarith
  have hK := cfn_cons_kkt hV n x
  have hK' := cfn_cons_kkt hV n x'
  have hT := cfn_cons_kkt hV₂ n (x + e)
  have hT' := cfn_cons_kkt hV₂ n (x' + e)
  have hHT : ∀ (cn : ℝ → ℝ) s, H.cont cn s = (H.tighten b₂).cont cn s := fun _ _ => rfl
  have hsh := ctl_shift_sharp hV hb₂ hb (n + 1) hx
  have hsh' := ctl_shift_sharp hV hb₂ hb (n + 1) hx'
  set c := H.cons (n + 1) x
  set c' := H.cons (n + 1) x'
  set k := (H.tighten b₂).cons (n + 1) (x + e)
  set k' := (H.tighten b₂).cons (n + 1) (x' + e)
  have hk'le : k' ≤ x' + e + b₂ / H.R := hT'.1
  have hkle1 : k ≤ x + e + b₂ / H.R := hT.1
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hk'le with hbind | hint'
  · -- the tight household is constrained at `x' + e`, hence at `x + e`
    have hb' := cfn_binding_initial hV₂ n (by linarith : x + e ≤ x' + e) hbind
    have hlip := (cfn_cons_good hV (n + 1)).2.2.1 x x' hx hxx
    linarith [hb'.2]
  have hek' : k' = (H.tighten b₂).cont ((H.tighten b₂).cons n) (x' + e - k') := hT'.2.2 hint'
  rcases eq_or_lt_of_le hK.1 with hcb | hclt
  · -- the loose household is constrained at `x`: then `c̃(x + e) = c(x)`
    have : k = c := by linarith
    linarith
  have hec : c = H.cont (H.cons n) (x - c) := hK.2.2 hclt
  have hc'le : c' ≤ H.cont (H.cons n) (x' - c') := hK'.2.1
  have hkle : k ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (x + e - k) := hT.2.1
  have hsk : -(b₂ / H.R) ≤ x + e - k := cfn_save_ge hT.1
  have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
  have hss' : x - c ≤ x' - c' := (cfn_kkt_mono hV hg hK hK' hxx).2
  -- the saving gap `t` lies in `[0, e]`
  set t := (x + e - k) - (x - c) with ht
  have hkc : k ≤ c + e := by
    have h1 := cfn_tight_le hV hb₂ hb (n + 1) hxe
    have h2 := (cfn_cons_good hV (n + 1)).2.2.1 x (x + e) hx (by linarith)
    linarith
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hte : t ≤ e := by rw [ht]; linarith
  have hRt0 : 0 ≤ H.R * t := mul_nonneg hR0.le ht0
  have hRtΔ : H.R * t ≤ H.b - b₂ := by
    rw [← hRe]; exact mul_le_mul_of_nonneg_left hte hR0.le
  have hm := cfn_cont_mono hV₂ hg₂ (by linarith : -(b₂ / H.R) ≤ (x' - c') + t)
    (by linarith : (x' - c') + t ≤ x' + e - k')
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
  have hxt : x - c + t = x + e - k := by rw [ht]; ring
  rw [hxt] at hdiff
  rw [hHT] at hec hc'le
  linarith

/-- **AKMM, p. 306: a tighter limit raises the MPC two periods before the end** (quadratic utility,
any `R ≥ 1` and `θ > 0`): on every interval of cash in hand the tight household's consumption rises
at least as much as the loose household's. -/
theorem ctl_tight_mpc_two (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) {x x' : ℝ} (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons 2 x' - H.cons 2 x ≤ (H.tighten b₂).cons 2 x' - (H.tighten b₂).cons 2 x :=
  ctl_mpc_step hV hb₂ hb hM 1 (ctl_incr_step hV hb₂ hb hM 0 ctl_incrDom_zero) hx hxx

/-- With `R = 1` the pair of consumption functions is `(a₁ − a₂)`-dominated at every horizon
(quadratic utility). -/
theorem ctl_incrDom_R_one (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hR : H.R = 1) (n : ℕ) :
    ctl_IncrDom (H.cons n) ((H.tighten b₂).cons n) H.d (H.b - b₂) := by
  induction n with
  | zero => exact ctl_incrDom_zero
  | succ n ih =>
    have h := ctl_incr_step hV hb₂ hb hM n ih
    rwa [hR, div_one] at h

/-- **AKMM, p. 306: with `r = 0` a tighter limit raises the MPC at every horizon** (quadratic
utility): for every number of periods left, on every interval of cash in hand the tight household's
consumption rises at least as much as the loose household's. -/
theorem ctl_tight_mpc_R_one (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hR : H.R = 1) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x)
    (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x := by
  cases n with
  | zero => simp only [cons]; rfl
  | succ n =>
    have h := ctl_incrDom_R_one hV hb₂ hb hM hR n
    have he : (H.b - b₂) / H.R ≤ H.b - b₂ := by rw [hR, div_one]
    have hR0 : 0 < H.R := by rw [hR]; exact one_pos
    refine ctl_mpc_step hV hb₂ hb hM n (fun z z' hz hzz => ?_) hx hxx
    exact ctl_incrDom_le (cfn_cons_good (cfn_tighten_valid hV hb₂ hb) n).2.2.2.1 h
      (div_nonneg (by linarith) hR0.le) he hz hzz

/-- **The fall in consumption shrinks as wealth grows** (quadratic utility, `r = 0`, every horizon):
`cₙ(x) − c̃ₙ(x)` is nonincreasing — the form in which Figure 11.2 shows the MPC comparison. -/
theorem ctl_gap_antitone_R_one (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (hM : ∀ z, H.M z = ∑ i, H.w i * z i) (hR : H.R = 1) (n : ℕ) :
    AntitoneOn (fun x => H.cons n x - (H.tighten b₂).cons n x) (Set.Ici H.d) := by
  intro x hx x' _ hxx
  have := ctl_tight_mpc_R_one hV hb₂ hb hM hR n hx hxx
  simp only
  linarith

/-- The quadratic household's certainty equivalent is the expectation, so the theorems above
apply to it. -/
theorem ctl_quadratic_linear (w y : ι → ℝ) (R b d ymax : ℝ) (z : ι → ℝ) :
    (cfn_quadratic w y R b d ymax).M z = ∑ i, (cfn_quadratic w y R b d ymax).w i * z i := rfl

/-- **A concrete instance with `r = 0`**: the quadratic household with income `1` or `3` with equal
probability, `R = 1`, `a = 1/2`, `d = 1/2`, satisfies the standing assumptions. -/
theorem ctl_example_R_one_valid :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).Valid := by
  refine cfn_quadratic_valid (fun _ => by norm_num) (by simp) (by norm_num) (by norm_num)
    (by norm_num) (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

/-- **The instance**: for that household, removing the borrowing limit's slack entirely (`a₂ = 0`)
raises the MPC on every interval at every horizon. -/
theorem ctl_example_mpc (n : ℕ) {x x' : ℝ} (hx : 1 / 2 ≤ x) (hxx : x ≤ x') :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).cons n x' -
        (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).cons n x ≤
      ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x' -
        ((cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] 1 (1 / 2) (1 / 2) 3).tighten 0).cons
          n x :=
  ctl_tight_mpc_R_one ctl_example_R_one_valid le_rfl (by simp only [cfn_quadratic]; norm_num)
    (ctl_quadratic_linear _ _ _ _ _ _) rfl n hx hxx

end AKMM.Consumption
