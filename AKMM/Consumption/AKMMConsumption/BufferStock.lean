/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.ConsumptionShape
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The buffer-stock target (Figure 11.4)

AKMM, §11.3.4, "Buffer-stock saving", pp. 310–311, Figure 11.4: when the discount rate exceeds
the interest rate there is a target level `x*` of cash in hand; above it the household
decumulates and below it it accumulates, and `x*` is stable — "wealth converges back toward
`x*`".

The model is the household of `ConsumptionShape` (i.i.d. income, borrowing limit `a`, finite
horizon, CRRA or quadratic utility), with expected next-period cash in hand
`E[xₜ₊₁ | xₜ = x] = R(x − cₙ(x)) + ȳ`, `ȳ = Σᵢ wᵢyᵢ` (`CfnHousehold.nextCash`).

* **The target** (`bsk_target`): if `θ ≥ 1` — for CRRA `βR ≤ 1`, the book's `ρ > r`
  (`cfn_crra_theta_ge_one_iff`) — and `d + a < ȳ`, then at every horizon `n` there is a unique
  `x* > d` with `E[x′ | x*] = x*`, `E[x′ | x] > x` for `d ≤ x < x*` and `E[x′ | x] < x` for
  `x > x*`. The proof: the expected change `R(x − c(x)) + ȳ − x` is convex because the consumption
  function is concave (`cfn_cons_concave`), positive at `d`, and eventually negative because the
  slope of consumption never falls below `κₙ` and `R(1 − κₙ) < 1` (`cfn_R_one_sub_kappa_lt`);
  a convex function with these properties crosses zero once (`bsk_convex_crossing`).
* **Stability** (`bsk_target_stable`): the expected-cash map is nondecreasing, so from below it
  moves up without overshooting `x*` and from above it moves down without undershooting, and its
  iterates converge to `x*` from every starting point (`bsk_iterate_tendsto`).

Departures: the book's model has permanent income shocks (cash in hand normalised by permanent
income) and a probability of zero income that makes the natural borrowing limit zero; here income
is i.i.d. with a positive floor and the borrowing limit `a ≥ 0` is imposed (with `a = 0` the
book's limit). With permanent shocks and growth the condition for a target is Carroll's growth
impatience condition rather than `ρ > r`; that model is not formalised. The target is that of the
`n`-period-ahead consumption function, at every `n`, because the horizon is finite. "Stable" is
read as convergence of the expected-cash dynamics `x ↦ E[x′ | x]`; the stochastic process itself
is not studied, and Figure 11.4's vertical axis (expected consumption growth) is not formalised.
-/

namespace AKMM.Consumption

open Filter Topology CfnHousehold

/-! ### Convex crossing and monotone iteration -/

/-- **A convex function that is positive at `d` and eventually negative crosses zero exactly
once**, from above. -/
theorem bsk_convex_crossing {e : ℝ → ℝ} {d : ℝ} (hconv : ConvexOn ℝ (Set.Ici d) e)
    (hcont : ContinuousOn e (Set.Ici d)) (hd : 0 < e d) {X : ℝ} (hX : ∀ x, X ≤ x → e x < 0) :
    ∃ xs, d < xs ∧ e xs = 0 ∧ (∀ x, d ≤ x → x < xs → 0 < e x) ∧ (∀ x, xs < x → e x < 0) := by
  -- once `e` is nonpositive it stays negative
  have hkey : ∀ z w, d ≤ z → z < w → e z ≤ 0 → e w < 0 := by
    intro z w hz hzw hez
    by_contra hge
    push Not at hge
    set v := max X (w + 1) with hv
    have hwv : w < v := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hs := hconv.slope_mono_adjacent (Set.mem_Ici.2 hz) (Set.mem_Ici.2 (by linarith)) hzw hwv
    have h1 : 0 ≤ (e w - e z) / (w - z) := div_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ e v - e w := by
      have := le_trans h1 hs
      rwa [le_div_iff₀ (by linarith), zero_mul] at this
    have := hX v (le_max_left _ _)
    linarith
  set X₀ := max X (d + 1) with hX₀
  have hdX : d ≤ X₀ := le_trans (by linarith) (le_max_right _ _)
  have hneg := hX X₀ (le_max_left _ _)
  obtain ⟨xs, hxs, hexs⟩ := intermediate_value_Icc' hdX (hcont.mono Set.Icc_subset_Ici_self)
    ⟨hneg.le, hd.le⟩
  have hdxs : d < xs := by
    rcases eq_or_lt_of_le hxs.1 with h | h
    · rw [← h] at hexs; linarith
    · exact h
  refine ⟨xs, hdxs, hexs, fun x hx hxx => ?_, fun x hxx => hkey xs x hdxs.le hxx hexs.le⟩
  by_contra hle
  push Not at hle
  have := hkey x xs hx hxx hle
  linarith

/-- **Monotone dynamics converge to the unique fixed point.** If `g` is continuous and
nondecreasing on `[d, ∞)`, maps it into itself, and has a fixed point `x*` with `g x > x` below
and `g x < x` above, then `gᵏ(x₀) → x*` for every `x₀ ≥ d`. -/
theorem bsk_iterate_tendsto {g : ℝ → ℝ} {d xs : ℝ} (hcont : ContinuousOn g (Set.Ici d))
    (hmono : MonotoneOn g (Set.Ici d)) (hmaps : ∀ x, d ≤ x → d ≤ g x) (hxs : d ≤ xs)
    (hfix : g xs = xs) (hbelow : ∀ x, d ≤ x → x < xs → x < g x)
    (habove : ∀ x, xs < x → g x < x) {x₀ : ℝ} (hx₀ : d ≤ x₀) :
    Tendsto (fun k => g^[k] x₀) atTop (𝓝 xs) := by
  set u : ℕ → ℝ := fun k => g^[k] x₀ with hu
  have hsucc : ∀ k, u (k + 1) = g (u k) := fun k => by
    simp only [hu, Function.iterate_succ_apply']
  have hmem : ∀ k, d ≤ u k := by
    intro k
    induction k with
    | zero => simpa [hu] using hx₀
    | succ k ih => rw [hsucc]; exact hmaps _ ih
  -- a limit point in `[d, ∞)` of the orbit is a fixed point
  have hfixL : ∀ L, d ≤ L → Tendsto u atTop (𝓝 L) → g L = L := by
    intro L hL hT
    have h1 : Tendsto (fun k => u (k + 1)) atTop (𝓝 L) := hT.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => g (u k)) atTop (𝓝 (g L)) :=
      (hcont L hL).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hT, Eventually.of_forall hmem⟩)
    have h3 : (fun k => u (k + 1)) = fun k => g (u k) := funext hsucc
    rw [h3] at h1
    exact tendsto_nhds_unique h2 h1
  rcases le_total x₀ xs with hlo | hhi
  · have hle : ∀ k, u k ≤ xs := by
      intro k
      induction k with
      | zero => simpa [hu] using hlo
      | succ k ih => rw [hsucc, ← hfix]; exact hmono (hmem k) hxs ih
    have hstep : ∀ k, u k ≤ u (k + 1) := by
      intro k
      rw [hsucc]
      rcases eq_or_lt_of_le (hle k) with h | h
      · rw [h, hfix]
      · exact (hbelow _ (hmem k) h).le
    have hbdd : BddAbove (Set.range u) := ⟨xs, by rintro _ ⟨k, rfl⟩; exact hle k⟩
    have hT := tendsto_atTop_ciSup (monotone_nat_of_le_succ hstep) hbdd
    have hLle : (⨆ k, u k) ≤ xs := ciSup_le hle
    have hLge : d ≤ ⨆ k, u k := le_trans (hmem 0) (le_ciSup hbdd 0)
    have hgL := hfixL _ hLge hT
    rcases eq_or_lt_of_le hLle with h | h
    · rwa [h] at hT
    · have := hbelow _ hLge h; linarith
  · have hge : ∀ k, xs ≤ u k := by
      intro k
      induction k with
      | zero => simpa [hu] using hhi
      | succ k ih => rw [hsucc, ← hfix]; exact hmono hxs (hmem k) ih
    have hstep : ∀ k, u (k + 1) ≤ u k := by
      intro k
      rw [hsucc]
      rcases eq_or_lt_of_le (hge k) with h | h
      · rw [← h, hfix]
      · exact (habove _ h).le
    have hbdd : BddBelow (Set.range u) := ⟨xs, by rintro _ ⟨k, rfl⟩; exact hge k⟩
    have hT := tendsto_atTop_ciInf (antitone_nat_of_succ_le hstep) hbdd
    have hLge : xs ≤ ⨅ k, u k := le_ciInf hge
    have hgL := hfixL _ (le_trans hxs hLge) hT
    rcases eq_or_lt_of_le hLge with h | h
    · rwa [← h] at hT
    · have := habove _ h; linarith

/-! ### The target in the household problem -/

/-- **Expected next-period cash in hand**, `E[xₜ₊₁ | xₜ = x] = R(x − cₙ(x)) + ȳ`. -/
noncomputable def CfnHousehold.nextCash {ι : Type*} [Fintype ι] (H : CfnHousehold ι) (n : ℕ)
    (x : ℝ) : ℝ := H.R * (x - H.cons n x) + ∑ i, H.w i * H.y i

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- Expected cash in hand is nondecreasing in current cash in hand. -/
theorem bsk_nextCash_mono (hV : H.Valid) (n : ℕ) : MonotoneOn (H.nextCash n) (Set.Ici H.d) := by
  intro x hx x' hx' hxx
  have h := (cfn_cons_good hV n).2.2.1 x x' hx hxx
  simp only [CfnHousehold.nextCash]
  have hR : 0 ≤ H.R := by linarith [hV.2.2.1]
  nlinarith

/-- Expected cash in hand is continuous on `[d, ∞)`. -/
theorem bsk_nextCash_continuousOn (hV : H.Valid) (n : ℕ) :
    ContinuousOn (H.nextCash n) (Set.Ici H.d) := by
  have hc := cfn_good_continuousOn (cfn_cons_good hV n)
  exact ((continuousOn_const.mul (continuousOn_id.sub hc)).add continuousOn_const)

/-- Expected cash in hand is at least `ȳ − a`. -/
theorem bsk_nextCash_ge (hV : H.Valid) (n : ℕ) (x : ℝ) :
    ∑ i, H.w i * H.y i - H.b ≤ H.nextCash n x := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have h := cfn_cons_le hV n x
  have h2 : -(H.b / H.R) ≤ x - H.cons n x := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hR0.le
  rw [mul_neg, mul_div_cancel₀ _ hR0.ne'] at h3
  simp only [CfnHousehold.nextCash]
  linarith

/-- **Figure 11.4: the buffer-stock target.** If `θ ≥ 1` (for CRRA `βR ≤ 1`: the discount rate is
at least the interest rate) and mean income exceeds `d + a`, then at every horizon there is a
target `x* > d`: expected cash in hand equals `x*` there, exceeds current cash in hand below `x*`
and falls short of it above `x*`; the target is the only fixed point. -/
theorem bsk_target (hV : H.Valid) (hθ1 : 1 ≤ H.θ) (hy : H.d + H.b < ∑ i, H.w i * H.y i)
    (n : ℕ) : ∃ xs, H.d < xs ∧ H.nextCash n xs = xs ∧
      (∀ x, H.d ≤ x → x < xs → x < H.nextCash n x) ∧ (∀ x, xs < x → H.nextCash n x < x) ∧
      (∀ x, H.d ≤ x → H.nextCash n x = x → x = xs) := by
  have hg := cfn_cons_good hV n
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  set ybar := ∑ i, H.w i * H.y i with hybar
  set e : ℝ → ℝ := fun x => H.nextCash n x - x with he
  -- convexity of the expected change, from concavity of consumption
  have hconv : ConvexOn ℝ (Set.Ici H.d) e := by
    refine ⟨convex_Ici _, fun x hx x' hx' μ ν hμ hν hμν => ?_⟩
    have hc := hg.2.2.2.1.2 hx hx' hμ hν hμν
    simp only [smul_eq_mul] at hc ⊢
    simp only [he, CfnHousehold.nextCash]
    have := mul_le_mul_of_nonneg_left hc hR0.le
    have hyb : ybar = μ * ybar + ν * ybar := by linear_combination -ybar * hμν
    nlinarith
  have hcont : ContinuousOn e (Set.Ici H.d) :=
    (bsk_nextCash_continuousOn hV n).sub continuousOn_id
  have hd : 0 < e H.d := by
    have := bsk_nextCash_ge hV n H.d
    simp only [he]
    linarith
  -- eventually negative: the slope of consumption is at least `κₙ` and `R(1 − κₙ) < 1`
  set α := 1 - H.R * (1 - H.kappa n) with hα
  have hα0 : 0 < α := by have := cfn_R_one_sub_kappa_lt hV hθ1 n; linarith
  have hX : ∀ x, max H.d (|ybar| / α + 1) ≤ x → e x < 0 := by
    intro x hx
    have hxd : H.d ≤ x := le_trans (le_max_left _ _) hx
    have hlow := (hg.2.2.2.2 x hxd).1
    have h1 : |ybar| / α + 1 ≤ x := le_trans (le_max_right _ _) hx
    have h2 : |ybar| + α ≤ α * x := by
      have := mul_le_mul_of_nonneg_left h1 hα0.le
      rw [mul_add, mul_div_cancel₀ _ hα0.ne', mul_one] at this
      linarith
    simp only [he, CfnHousehold.nextCash]
    have := mul_le_mul_of_nonneg_left hlow hR0.le
    nlinarith [le_abs_self ybar]
  obtain ⟨xs, hdxs, hexs, hlo, hhi⟩ := bsk_convex_crossing hconv hcont hd hX
  refine ⟨xs, hdxs, by simp only [he] at hexs; linarith, fun x hx hxx => ?_, fun x hxx => ?_,
    fun x hx hfx => ?_⟩
  · have := hlo x hx hxx; simp only [he] at this; linarith
  · have := hhi x hxx; simp only [he] at this; linarith
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hlo x hx h; simp only [he] at this; linarith
    · have := hhi x h; simp only [he] at this; linarith

/-- **Figure 11.4: the target is stable.** Under the assumptions of `bsk_target`, from below the
target expected cash in hand rises without overshooting, from above it falls without
undershooting, and the expected-cash dynamics converge to the target from every `x₀ ≥ d`. -/
theorem bsk_target_stable (hV : H.Valid) (hθ1 : 1 ≤ H.θ) (hy : H.d + H.b < ∑ i, H.w i * H.y i)
    (n : ℕ) : ∃ xs, H.d < xs ∧ H.nextCash n xs = xs ∧
      (∀ x, H.d ≤ x → x < xs → x < H.nextCash n x ∧ H.nextCash n x ≤ xs) ∧
      (∀ x, xs < x → xs ≤ H.nextCash n x ∧ H.nextCash n x < x) ∧
      ∀ x₀, H.d ≤ x₀ → Tendsto (fun k => (H.nextCash n)^[k] x₀) atTop (𝓝 xs) := by
  obtain ⟨xs, hdxs, hfix, hlo, hhi, -⟩ := bsk_target hV hθ1 hy n
  have hmono := bsk_nextCash_mono hV n
  have hmaps : ∀ x, H.d ≤ x → H.d ≤ H.nextCash n x := fun x _ => by
    have := bsk_nextCash_ge hV n x; linarith
  refine ⟨xs, hdxs, hfix, fun x hx hxx => ⟨hlo x hx hxx, ?_⟩, fun x hxx => ⟨?_, hhi x hxx⟩,
    fun x₀ hx₀ => bsk_iterate_tendsto (bsk_nextCash_continuousOn hV n) hmono hmaps hdxs.le hfix
      hlo hhi hx₀⟩
  · rw [← hfix]; exact hmono hx (Set.mem_Ici.2 hdxs.le) hxx.le
  · rw [← hfix]
    exact hmono (Set.mem_Ici.2 hdxs.le) (Set.mem_Ici.2 (by linarith : H.d ≤ x)) hxx.le

/-- **A concrete instance**: the quadratic household of `cfn_example_valid` with `βR = 1` has
mean income `2 > d + a = 1`, so it has a stable buffer-stock target at every horizon. -/
theorem bsk_example_target (n : ℕ) :
    ∃ xs, (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] (102 / 100) (1 / 2) (1 / 2) 3).d
      < xs ∧ (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] (102 / 100) (1 / 2) (1 / 2)
        3).nextCash n xs = xs := by
  obtain ⟨xs, h1, h2, -⟩ := bsk_target cfn_example_valid (by simp [cfn_quadratic])
    (by simp [cfn_quadratic, Fin.sum_univ_two]) n
  exact ⟨xs, h1, h2⟩

end AKMM.Consumption
