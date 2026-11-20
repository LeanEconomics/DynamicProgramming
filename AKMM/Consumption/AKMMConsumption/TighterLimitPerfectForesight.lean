/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.TighterLimitAllHorizons

/-!
# A tighter limit raises the MPC without income risk, for every utility (Figure 11.2)

AKMM, §11.3.4, p. 306, Figure 11.2: "their marginal propensity to consume … increases" when the
credit limit tightens from `a₁` to `a₂`. Here income is deterministic (one income state), the
utility is arbitrary — CRRA with any `σ` and any `β`, so any `θ = (βR)^{−1/σ} > 0` — and the claim
is proved at every horizon and every `r ≥ 0` (`ctp_tight_mpc`, `ctp_gap_antitone`; for CRRA
`ctp_crra_tight_mpc`).

With one income state every certainty equivalent is the identity on positive values
(`ctp_cont_eq`), so the Euler condition is `c = θ·cₙ(R(x − c) + y)`. The invariant is a
comparison at equal consumption: *horizontal domination* (`ctp_Hor`). If the tight household
consumes at least as much at `ζ` as the loose one at `z`, and at most as much at `ζ′` as the loose
one at `z′`, then `ζ′ − ζ ≤ z′ − z`. In words: to raise consumption by a given amount the tight
household needs no more extra cash than the loose one. It holds in the last period
(`ctp_hor_zero`). It propagates because with one state the Euler condition maps equal
consumption today to equal consumption tomorrow (`ctp_hor_step`; where the loose household is
constrained, the sharp shift bound `ctl_shift_sharp` closes the case). Concavity of the tight
function then turns it into the MPC comparison (`ctp_mpc_of_hor`).

This route does not need `θ ≥ 1`, and does not extend to income risk: with several states,
equal consumption today does not give equal consumption tomorrow state by state.
-/

namespace AKMM.Consumption

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- `(f, g)` is *horizontally dominated* on `[d, ∞)`: if `g` at `ζ` is at least `f` at `z`, and
`g` at `ζ′` is at most `f` at `z′`, then `ζ′ − ζ ≤ z′ − z`. With `f` the loose and `g` the tight
consumption function: raising consumption by a given amount takes the tight household no more
extra cash than the loose one. -/
def ctp_Hor (f g : ℝ → ℝ) (d : ℝ) : Prop :=
  ∀ z z' ζ ζ', d ≤ z → z ≤ z' → d ≤ ζ → d ≤ ζ' → f z ≤ g ζ → g ζ' ≤ f z' → ζ' - ζ ≤ z' - z

/-- With one income state the Euler right-hand side is `θ·cₙ(Rs + y)` wherever `cₙ` is positive
there: every certainty equivalent is the identity on a single positive value. -/
theorem ctp_cont_eq [Unique ι] (hV : H.Valid) {cn : ℝ → ℝ} {s : ℝ}
    (hpos : 0 < cn (H.R * s + H.y default)) :
    H.cont cn s = H.θ * cn (H.R * s + H.y default) := by
  have hfun : (fun i => cn (H.R * s + H.y i)) = fun _ => cn (H.R * s + H.y default) := by
    funext i
    rw [Subsingleton.elim i default]
  simp only [cont, hfun, hV.1.2.1 _ hpos]

omit [Fintype ι] in
/-- In the last period both households eat their cash: horizontal domination holds. -/
theorem ctp_hor_zero {b₂ : ℝ} : ctp_Hor (H.cons 0) ((H.tighten b₂).cons 0) H.d := by
  intro z z' ζ ζ' _ _ _ _ h1 h2
  simp only [cons] at h1 h2
  linarith

/-- A consumption function rises at rate at least `κₙ > 0`: it is strictly increasing. -/
theorem ctp_cons_strict (hV : H.Valid) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x) (hxx : x < x') :
    H.cons n x < H.cons n x' := by
  have h := (cfn_cons_slope_bounds hV n hx hxx).1
  have hκ := (cfn_kappa_pos hV n).1
  have hd : 0 < x' - x := by linarith
  rw [le_div_iff₀ hd] at h
  nlinarith

/-- **The horizontal step** (one income state, any utility, any `θ > 0`): horizontal domination
with `n` periods left gives horizontal domination with `n + 1` periods left. -/
theorem ctp_hor_step [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ)
    (hP : ctp_Hor (H.cons n) ((H.tighten b₂).cons n) H.d) :
    ctp_Hor (H.cons (n + 1)) ((H.tighten b₂).cons (n + 1)) H.d := by
  intro x₁ x₂ ξ₁ ξ₂ hx₁ hx₁₂ hξ₁ hξ₂ h1 h2
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  have hθ := hV.2.1
  have hx₂ : H.d ≤ x₂ := le_trans hx₁ hx₁₂
  set e := (H.b - b₂) / H.R with he
  have hbe : b₂ / H.R + e = H.b / H.R := by rw [he]; field_simp; ring
  have hg := cfn_cons_good hV n
  have hg₂ := cfn_cons_good hV₂ n
  have hK₁ := cfn_cons_kkt hV n x₁
  have hK₂ := cfn_cons_kkt hV n x₂
  have hT₁ := cfn_cons_kkt hV₂ n ξ₁
  have hT₂ := cfn_cons_kkt hV₂ n ξ₂
  have hsh := ctl_shift_sharp hV hb₂ hb (n + 1) hx₂
  set c₁ := H.cons (n + 1) x₁
  set c₂ := H.cons (n + 1) x₂
  set k₁ := (H.tighten b₂).cons (n + 1) ξ₁
  set k₂ := (H.tighten b₂).cons (n + 1) ξ₂
  by_contra hlt
  push Not at hlt
  have hss : x₁ - c₁ ≤ x₂ - c₂ := (cfn_kkt_mono hV hg hK₁ hK₂ hx₁₂).2
  have hs₁ : -(H.b / H.R) ≤ x₁ - c₁ := cfn_save_ge hK₁.1
  have hs₂ : -(H.b / H.R) ≤ x₂ - c₂ := cfn_save_ge hK₂.1
  have hσ₁ : -(b₂ / H.R) ≤ ξ₁ - k₁ := cfn_save_ge hT₁.1
  have hσ₂ : -(b₂ / H.R) ≤ ξ₂ - k₂ := cfn_save_ge hT₂.1
  -- the tight household saves strictly more at `ξ₂` than at `ξ₁`, so it is unconstrained there
  have hgap : (x₂ - c₂) - (x₁ - c₁) < (ξ₂ - k₂) - (ξ₁ - k₁) := by linarith
  have hint : k₂ < ξ₂ + b₂ / H.R := by linarith
  have hek₂ : k₂ = (H.tighten b₂).cont ((H.tighten b₂).cons n) (ξ₂ - k₂) := hT₂.2.2 hint
  rcases eq_or_lt_of_le hK₁.1 with hcb | hclt
  · -- the loose household is constrained at `x₁`: then `ξ₁ ≥ x₁ + e` and `ξ₂ ≤ x₂ + e`
    have hξ₁e : x₁ + e ≤ ξ₁ := by
      have : k₁ ≤ ξ₁ + b₂ / H.R := hT₁.1
      linarith
    have hξ₂e : ξ₂ ≤ x₂ + e := by
      by_contra hgt
      push Not at hgt
      have hx₂e : H.d ≤ x₂ + e := by
        have : 0 ≤ e := div_nonneg (by linarith) hR0.le
        linarith
      have := ctp_cons_strict hV₂ (n + 1) hx₂e hgt
      linarith
    linarith
  -- the loose household is unconstrained at `x₁`: compare one period ahead
  have hec₁ : c₁ = H.cont (H.cons n) (x₁ - c₁) := hK₁.2.2 hclt
  have hc₂ : c₂ ≤ H.cont (H.cons n) (x₂ - c₂) := hK₂.2.1
  have hk₁ : k₁ ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n) (ξ₁ - k₁) := hT₁.2.1
  have hz₁ := cfn_arg_ge hV hs₁ default
  have hz₂ := cfn_arg_ge hV hs₂ default
  have hζ₁ := cfn_arg_ge hV₂ hσ₁ default
  have hζ₂ := cfn_arg_ge hV₂ hσ₂ default
  have htd : (H.tighten b₂).d = H.d := rfl
  have htR : (H.tighten b₂).R = H.R := rfl
  have hty : (H.tighten b₂).y = H.y := rfl
  rw [htd, htR, hty] at hζ₁ hζ₂
  rw [ctp_cont_eq hV (hg.1 _ hz₁)] at hec₁
  rw [ctp_cont_eq hV (hg.1 _ hz₂)] at hc₂
  rw [ctp_cont_eq hV₂ (by rw [htR, hty]; exact hg₂.1 _ hζ₁), htR, hty] at hk₁
  rw [ctp_cont_eq hV₂ (by rw [htR, hty]; exact hg₂.1 _ hζ₂), htR, hty] at hek₂
  have hθ' : (H.tighten b₂).θ = H.θ := rfl
  rw [hθ'] at hk₁ hek₂
  have hl1 : H.cons n (H.R * (x₁ - c₁) + H.y default) ≤
      (H.tighten b₂).cons n (H.R * (ξ₁ - k₁) + H.y default) := by
    have : H.θ * H.cons n (H.R * (x₁ - c₁) + H.y default) ≤
        H.θ * (H.tighten b₂).cons n (H.R * (ξ₁ - k₁) + H.y default) := by linarith
    exact le_of_mul_le_mul_left this hθ
  have hl2 : (H.tighten b₂).cons n (H.R * (ξ₂ - k₂) + H.y default) ≤
      H.cons n (H.R * (x₂ - c₂) + H.y default) := by
    have : H.θ * (H.tighten b₂).cons n (H.R * (ξ₂ - k₂) + H.y default) ≤
        H.θ * H.cons n (H.R * (x₂ - c₂) + H.y default) := by linarith
    exact le_of_mul_le_mul_left this hθ
  have hzz : H.R * (x₁ - c₁) + H.y default ≤ H.R * (x₂ - c₂) + H.y default := by nlinarith
  have hfin := hP _ _ _ _ hz₁ hzz hζ₁ hζ₂ hl1 hl2
  have : H.R * ((ξ₂ - k₂) - (ξ₁ - k₁)) ≤ H.R * ((x₂ - c₂) - (x₁ - c₁)) := by nlinarith
  have := le_of_mul_le_mul_left this hR0
  linarith

/-- **Horizontal domination at every horizon** (one income state, any utility, any `θ > 0`). -/
theorem ctp_hor_all [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) :
    ctp_Hor (H.cons n) ((H.tighten b₂).cons n) H.d := by
  induction n with
  | zero => exact ctp_hor_zero
  | succ n ih => exact ctp_hor_step hV hb₂ hb n ih

/-- **Horizontal domination gives the MPC comparison**, by concavity of the tight function and the
sharp shift bound. -/
theorem ctp_mpc_of_hor (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ)
    (hP : ctp_Hor (H.cons n) ((H.tighten b₂).cons n) H.d) {x x' : ℝ} (hx : H.d ≤ x)
    (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hx' : H.d ≤ x' := le_trans hx hxx
  set e := (H.b - b₂) / H.R with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) hR0.le
  have hg₂ := cfn_cons_good hV₂ n
  have hcont : ContinuousOn ((H.tighten b₂).cons n) (Set.Ici H.d) := cfn_good_continuousOn hg₂
  -- the points where the tight household consumes what the loose one does at `x` and `x'`
  have hfind : ∀ u, H.d ≤ u → ∃ ζ, u ≤ ζ ∧ ζ ≤ u + e ∧
      (H.tighten b₂).cons n ζ = H.cons n u := by
    intro u hu
    have hlo := cfn_tight_le hV hb₂ hb n hu
    have hhi := ctl_shift_sharp hV hb₂ hb n hu
    have hc : ContinuousOn ((H.tighten b₂).cons n) (Set.Icc u (u + e)) :=
      hcont.mono fun t ht => Set.mem_Ici.2 (le_trans hu ht.1)
    obtain ⟨ζ, hζ, hζv⟩ := intermediate_value_Icc (by linarith) hc ⟨hlo, hhi⟩
    exact ⟨ζ, hζ.1, hζ.2, hζv⟩
  obtain ⟨ζ, hζ1, -, hζv⟩ := hfind x hx
  obtain ⟨ζ', hζ'1, -, hζ'v⟩ := hfind x' hx'
  have hd := hP x x' ζ ζ' hx hxx (by linarith) (by linarith) hζv.ge hζ'v.le
  have hmono := cfn_cons_good hV n
  have hLx : H.cons n x ≤ H.cons n x' := hmono.2.1 hx hx' hxx
  have hζζ : ζ ≤ ζ' := by
    by_contra hlt
    push Not at hlt
    have := ctp_cons_strict hV₂ n (by linarith : H.d ≤ ζ') hlt
    linarith
  -- concavity: the rise over `[x, x + (ζ' − ζ)]` is at least that over `[ζ, ζ']`
  have hconc := ctl_concave_incr hg₂.2.2.2.1 hx (by linarith : x ≤ x + (ζ' - ζ)) le_rfl
    (by linarith : (0 : ℝ) ≤ ζ - x)
  have e1 : x + (ζ' - ζ) + (ζ - x) = ζ' := by ring
  have e2 : x + (ζ - x) = ζ := by ring
  rw [e1, e2, add_zero, add_zero] at hconc
  have hmon := hg₂.2.1 (Set.mem_Ici.2 (by linarith : H.d ≤ x + (ζ' - ζ))) (Set.mem_Ici.2 hx')
    (by linarith : x + (ζ' - ζ) ≤ x')
  linarith

/-- **AKMM, p. 306, without income risk: a tighter limit raises the MPC at every horizon** (one
income state, any certainty equivalent — every utility, CRRA with any `σ` and `β` included —
any `r ≥ 0`). -/
theorem ctp_tight_mpc [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ)
    {x x' : ℝ} (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons n x' - H.cons n x ≤ (H.tighten b₂).cons n x' - (H.tighten b₂).cons n x :=
  ctp_mpc_of_hor hV hb₂ hb n (ctp_hor_all hV hb₂ hb n) hx hxx

/-- **The fall in consumption shrinks as wealth grows** without income risk, at every horizon. -/
theorem ctp_gap_antitone [Unique ι] (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    (n : ℕ) : AntitoneOn (fun x => H.cons n x - (H.tighten b₂).cons n x) (Set.Ici H.d) := by
  intro x hx x' _ hxx
  have := ctp_tight_mpc hV hb₂ hb n hx hxx
  simp only
  linarith

/-- **AKMM, p. 306, CRRA without income risk**: for the CRRA household with one income value `y`,
any `β > 0`, `σ > 0` and `R ≥ 1` (so any `θ = (βR)^{−1/σ}`, `βR` above or below `1`), a tighter
limit raises the MPC on every interval of cash in hand at every horizon. -/
theorem ctp_crra_tight_mpc {β σ y R b d : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hR : 1 ≤ R) (hb : 0 ≤ b)
    (hd : 0 < d) (hy : d + b ≤ y) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hbb : b₂ ≤ b) (n : ℕ) {x x' : ℝ}
    (hx : d ≤ x) (hxx : x ≤ x') :
    (cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).cons n x' -
        (cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).cons n x ≤
      ((cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).tighten b₂).cons n x' -
        ((cfn_crra β σ (fun _ : Fin 1 => 1) (fun _ => y) R b d y).tighten b₂).cons n x :=
  ctp_tight_mpc (cfn_crra_valid hβ hσ (fun _ => zero_le_one) (by simp) hR hb hd (fun _ => hy)
    (fun _ => le_rfl)) hb₂ hbb n hx hxx

end AKMM.Consumption
