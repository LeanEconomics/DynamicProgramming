/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDRadner
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First-order conditions of the sequential problem

Miao, §13.4, p. 432 (the Arrow security prices from first-order conditions) and the first-order
conditions of Exercise 13.4, p. 452, for the discounted expected utility (13.1).

* `rd_EU_pert`: the change in (13.1) when consumption moves at a node and its successors only.
* `rd_euler_dir`: if `(c, θ)` is optimal and buying `ε d` more at `sᵗ` (for small `ε > 0`)
  keeps the strategy admissible, then the one-sided derivative is nonpositive:
  `−u′(cₜ) pₜ · d + β ∑ₛ Pr(s | sᵗ) u′(c_{t+1}) f_{t+1} · d ≤ 0`. Two-sided feasibility gives the
  Euler equation (`rd_euler_eq`).
* Arrow securities (p. 432): `rd_arrow_price`, `Q_t(s′|sᵗ) = β u′(c_{t+1}(sᵗ, s′)) Pr(s′|sᵗ)/
  u′(c_t(sᵗ))`, the same for every agent (`rd_arrow_price_common`).
* `rd_statePrice_of_euler`: the Euler equations make `q⁰_t = βᵗ Pr u′(c_t)/u′(c₀)` a state price
  process ((13.7) with (13.16)).
* **Exercise 13.4** (p. 452): first-order conditions for the three economies — borrowing
  constraints (`ex_13_4_BC_foc`), short-sales constraints (`ex_13_4_SC_foc`), debt constraints
  (`ex_13_4_DC_foc`, with rank `S`) — and their sufficiency together with the transversality
  conditions (13.39), (13.40), (13.38) (`ex_13_4_BC_suff`, `ex_13_4_SC_suff`, `ex_13_4_DC_suff`),
  and the equilibrium version (`ex_13_4_BC_eqm`). Necessity of the transversality conditions is
  not formalised.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

omit [Fintype S] in
/-- The localised strategy `rd_loc d h` pays `−pₜ · d` at `sᵗ`. -/
theorem rd_net_loc_self [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h : List S) :
    rd_net p f 0 (rd_loc d h) h = -(p h ⬝ᵥ d) := by
  cases h with
  | nil => simp [rd_net, rd_loc, rd_prev]
  | cons s g =>
    have : g ≠ s :: g := fun e => by simpa using congrArg List.length e
    simp [rd_net, rd_loc, rd_prev, this]

omit [Fintype S] in
/-- The localised strategy pays `f_{t+1}(sᵗ, s) · d` at the successor `(sᵗ, s)`. -/
theorem rd_net_loc_child [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h : List S)
    (s : S) : rd_net p f 0 (rd_loc d h) (s :: h) = f (s :: h) ⬝ᵥ d := by
  have : s :: h ≠ h := fun e => by simpa using congrArg List.length e
  simp [rd_net, rd_loc, rd_prev, rd_fz, this]

omit [Fintype S] in
/-- The localised strategy pays nothing elsewhere. -/
theorem rd_net_loc_other [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h g : List S)
    (hg : g ≠ h) (hg' : ∀ s, g ≠ s :: h) : rd_net p f 0 (rd_loc d h) g = 0 := by
  cases g with
  | nil => simp [rd_net, rd_loc, rd_prev, hg]
  | cons s g' =>
    have : g' ≠ h := by
      rintro rfl
      exact hg' s rfl
    simp [rd_net, rd_loc, rd_prev, hg, this]

/-- The localised strategy's cash flows are bounded. -/
theorem rd_net_loc_bdd [DecidableEq S] (p f : List S → J → ℝ) (d : J → ℝ) (h : List S)
    (g : List S) : |rd_net p f 0 (rd_loc d h) g| ≤ |p h ⬝ᵥ d| + ∑ s, |f (s :: h) ⬝ᵥ d| := by
  have h0 : 0 ≤ ∑ s, |f (s :: h) ⬝ᵥ d| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hgh : g = h
  · rw [hgh, rd_net_loc_self, abs_neg]
    linarith
  · by_cases hc : ∃ s, g = s :: h
    · obtain ⟨s, rfl⟩ := hc
      rw [rd_net_loc_child]
      have := Finset.single_le_sum (f := fun s => |f (s :: h) ⬝ᵥ d|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
      linarith [abs_nonneg (p h ⬝ᵥ d)]
    · push Not at hc
      rw [rd_net_loc_other p f d h g hgh hc, abs_zero]
      positivity

omit [Fintype S] [Fintype J] in
/-- Adding `ε` times the localised strategy to the carried-in portfolio. -/
theorem rd_prev_add_loc [DecidableEq S] (θ : List S → J → ℝ) (θm1 : J → ℝ) (ε : ℝ)
    (d : J → ℝ) (h g : List S) :
    rd_prev (θ + ε • rd_loc d h) θm1 g = rd_prev θ θm1 g + ε • rd_prev (rd_loc d h) 0 g := by
  cases g with
  | nil => simp [rd_prev]
  | cons s g => rfl

/-- The change in the expected utility (13.1) when consumption changes only at `sᵗ` and its
successors. -/
theorem rd_EU_pert (T : RDTree S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) {c c' : List S → ℝ} (hc : rd_LinfPos c)
    (hc' : rd_LinfPos c') (h : List S) (hsupp : ∀ g, g ≠ h → (∀ s, g ≠ s :: h) → c' g = c g) :
    rd_EU T β u c' - rd_EU T β u c =
      β ^ h.length * (T.Pr h * (u (c' h) - u (c h))) +
        β ^ (h.length + 1) * ∑ s, T.Pr (s :: h) * (u (c' (s :: h)) - u (c (s :: h))) := by
  classical
  obtain ⟨K, hK⟩ := rd_abs_u_le hu hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu hc'
  set G : List S → ℝ := fun g => T.Pr g * (u (c' g) - u (c g)) with hGdef
  have hne : ∀ s, h ≠ s :: h := fun s e => by simpa using congrArg List.length e
  have hG : ∀ g, G g = (if g = h then G h else 0) + ∑ s, if g = s :: h then G (s :: h) else 0 := by
    intro g
    by_cases hgh : g = h
    · subst hgh
      simp [hne]
    · by_cases hcs : ∃ s, g = s :: h
      · obtain ⟨s, rfl⟩ := hcs
        simp only [hgh, ↓reduceIte, zero_add, List.cons.injEq, and_true]
        rw [Finset.sum_ite_eq]
        simp
      · push Not at hcs
        simp [hgh, hcs, G, hsupp g hgh hcs]
  have hd : ∀ t, rd_dsum G [] t = (if h.length = t then G h else 0) +
      ∑ s, if h.length + 1 = t then G (s :: h) else 0 := by
    intro t
    rw [rd_dsum_congr hG, rd_dsum_add, rd_dsum_finsetSum, rd_dsum_ite]
    simp only [rd_dsum_ite, List.length_cons]
  rw [rd_EU, rd_EU, ← Summable.tsum_sub (rd_EU_summable T hβ0 hβ1 u hK')
    (rd_EU_summable T hβ0 hβ1 u hK)]
  have e1 : ∀ t, β ^ t * rd_dsum (fun g => T.Pr g * u (c' g)) [] t -
      β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t =
      (if t = h.length then β ^ h.length * G h else 0) +
        if t = h.length + 1 then β ^ (h.length + 1) * ∑ s, G (s :: h) else 0 := by
    intro t
    rw [← mul_sub, ← rd_dsum_sub]
    have : rd_dsum (fun g => T.Pr g * u (c' g) - T.Pr g * u (c g)) [] t = rd_dsum G [] t :=
      rd_dsum_congr (fun g => by simp only [G]; ring) _ _
    rw [this, hd]
    by_cases h1 : t = h.length
    · subst h1
      simp
    · by_cases h2 : t = h.length + 1
      · subst h2
        simp
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  simp only [e1]
  rw [Summable.tsum_add (hasSum_ite_eq _ _).summable (hasSum_ite_eq _ _).summable,
    tsum_ite_eq, tsum_ite_eq]

/-- Miao, p. 432 (first-order conditions), one-sided form. If `(c, θ)` maximises (13.1) subject
to (13.11) and `θ ∈ Θᵃ`, consumption is positive at `sᵗ` and its successors, and adding `ε d`
to the portfolio at `sᵗ` keeps the strategy admissible for small `ε > 0`, then
`−u′(cₜ) pₜ · d + β ∑ₛ Pr(s | sᵗ) u′(c_{t+1}) f_{t+1} · d ≤ 0`. -/
theorem rd_euler_dir [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Θa : Set (List S → J → ℝ)}
    {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 Θa) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (d : J → ℝ)
    (hΘ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), θ + ε • rd_loc d h ∈ Θa) :
    -(u' (c h) * (p h ⬝ᵥ d)) +
        β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d)) ≤ 0 := by
  set N := rd_net p f 0 (rd_loc d h)
  set a := h.length
  set ψ : ℝ → ℝ := fun ε => β ^ a * (T.Pr h * (u (c h + ε * -(p h ⬝ᵥ d)) - u (c h))) +
    β ^ (a + 1) * ∑ s, T.Pr (s :: h) * (u (c (s :: h) + ε * (f (s :: h) ⬝ᵥ d)) - u (c (s :: h)))
  set D := β ^ a * (T.Pr h * (u' (c h) * -(p h ⬝ᵥ d))) +
    β ^ (a + 1) * ∑ s, T.Pr (s :: h) * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d))
  have hlin : ∀ (x k : ℝ), 0 < x →
      HasDerivAt (fun ε : ℝ => u (x + ε * k)) (u' x * k) 0 := by
    intro x k hx
    have hl : HasDerivAt (fun ε : ℝ => x + ε * k) k 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add x
    have hu0 : HasDerivAt u (u' x) (x + 0 * k) := by simpa using hd x hx
    exact hu0.comp (0 : ℝ) hl
  have hψ : HasDerivAt ψ D 0 := by
    have h1 := (((hlin (c h) (-(p h ⬝ᵥ d)) hch).sub_const (u (c h))).const_mul
      (T.Pr h)).const_mul (β ^ a)
    have h2 := (HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
      ((hlin (c (s :: h)) (f (s :: h) ⬝ᵥ d) (hcs s)).sub_const (u (c (s :: h)))).const_mul
        (T.Pr (s :: h))).const_mul (β ^ (a + 1))
    exact h1.add h2
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ψ ε ≤ 0 := by
    have hc1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c h + ε * -(p h ⬝ᵥ d) := by
      have : Tendsto (fun ε : ℝ => c h + ε * -(p h ⬝ᵥ d)) (𝓝 0) (𝓝 (c h)) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (-(p h ⬝ᵥ d))).const_add (c h)
      exact this.eventually (lt_mem_nhds hch)
    have hc2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < c (s :: h) + ε * (f (s :: h) ⬝ᵥ d) := by
      refine Filter.eventually_all.2 fun s => ?_
      have : Tendsto (fun ε : ℝ => c (s :: h) + ε * (f (s :: h) ⬝ᵥ d)) (𝓝 0)
          (𝓝 (c (s :: h))) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (f (s :: h) ⬝ᵥ d)).const_add
          (c (s :: h))
      exact this.eventually (lt_mem_nhds (hcs s))
    filter_upwards [hΘ, nhdsWithin_le_nhds hc1, nhdsWithin_le_nhds hc2] with ε hθε h1 h2
    set c' : List S → ℝ := fun g => c g + ε * N g with hc'def
    have hne : ∀ s, h ≠ s :: h := fun s e => by simpa using congrArg List.length e
    have hc'h : c' h = c h + ε * -(p h ⬝ᵥ d) := by simp only [c', N, rd_net_loc_self]
    have hc's : ∀ s, c' (s :: h) = c (s :: h) + ε * (f (s :: h) ⬝ᵥ d) := fun s => by
      simp only [c', N, rd_net_loc_child]
    have hc'o : ∀ g, g ≠ h → (∀ s, g ≠ s :: h) → c' g = c g := fun g hg hg' => by
      simp only [c', N, rd_net_loc_other p f d h g hg hg', mul_zero, add_zero]
    have hfeas : rd_SeqFeas p f y θm1 Θa c' (θ + ε • rd_loc d h) := by
      obtain ⟨⟨⟨M, hM⟩, h0⟩, hB, -⟩ := hsol.1
      have hBd := rd_net_loc_bdd p f d h
      refine ⟨⟨⟨M + |ε| * (|p h ⬝ᵥ d| + ∑ s, |f (s :: h) ⬝ᵥ d|), fun g => ?_⟩, fun g => ?_⟩,
        ?_, hθε⟩
      · simp only [c']
        refine (abs_add_le _ _).trans (add_le_add (hM g) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hBd g) (abs_nonneg ε)
      · by_cases hgh : g = h
        · rw [hgh, hc'h]
          exact h1.le
        · by_cases hcs' : ∃ s, g = s :: h
          · obtain ⟨s, rfl⟩ := hcs'
            rw [hc's]
            exact (h2 s).le
          · push Not at hcs'
            rw [hc'o g hgh hcs']
            exact h0 g
      · rw [rd_budget_iff_net]
        intro g
        have hn := (rd_budget_iff_net p f y θm1 c θ).1 hB g
        simp only [rd_net, rd_prev_add_loc, dotProduct_add, dotProduct_smul, smul_eq_mul,
          Pi.add_apply, Pi.smul_apply] at hn ⊢
        simp only [c', N, rd_net]
        nlinarith [hn]
    have hle := hsol.2 _ _ hfeas
    have hpert := rd_EU_pert T hβ0.le hβ1 hu hsol.1.1 hfeas.1 h hc'o
    rw [hc'h] at hpert
    simp only [hc's] at hpert
    simp only [ψ]
    linarith
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hslope := hψ.tendsto_slope_zero_right
  have hDle : D ≤ 0 := by
    refine le_of_tendsto hslope ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
    rw [zero_add, hψ0, sub_zero, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt htpos)) ht
  have hPr := T.pos h
  have hD : D = β ^ a * T.Pr h * (-(u' (c h) * (p h ⬝ᵥ d)) +
      β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d))) := by
    simp only [D, Finset.mul_sum, mul_add]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp only [rd_condPr, pow_succ]
      field_simp
  rw [hD] at hDle
  have hpos : 0 < β ^ a * T.Pr h := mul_pos (pow_pos hβ0 a) hPr
  by_contra hcon
  push Not at hcon
  exact absurd hDle (not_le.2 (mul_pos hpos hcon))

/-- The marginal value of a portfolio direction: `−u′(cₜ) pₜ · d + β E_t[u′(c_{t+1}) f_{t+1} · d]`.
-/
noncomputable def rd_Phi (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ)
    (c : List S → ℝ) (h : List S) (d : J → ℝ) : ℝ :=
  -(u' (c h) * (p h ⬝ᵥ d)) + β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * (f (s :: h) ⬝ᵥ d))

/-- `rd_Phi` is linear in the direction. -/
theorem rd_Phi_eq (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ) (c : List S → ℝ)
    (h : List S) (d : J → ℝ) :
    rd_Phi T β u' p f c h d =
      ∑ j, (-(u' (c h) * p h j) +
        β * ∑ s, rd_condPr T h s * (u' (c (s :: h)) * f (s :: h) j)) * d j := by
  simp only [rd_Phi, dotProduct, Finset.mul_sum, Finset.sum_add_distrib, add_mul,
    Finset.sum_mul, ← Finset.sum_neg_distrib, neg_mul]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring

/-- `rd_Phi` of the negated direction. -/
theorem rd_Phi_neg (T : RDTree S) (β : ℝ) (u' : ℝ → ℝ) (p f : List S → J → ℝ) (c : List S → ℝ)
    (h : List S) (d : J → ℝ) : rd_Phi T β u' p f c h (-d) = -rd_Phi T β u' p f c h d := by
  simp only [rd_Phi_eq, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- **Euler equation** (Miao, p. 432). If adding `±ε d` at `sᵗ` keeps the strategy admissible for
small `ε`, the marginal value of `d` is zero:
`u′(cₜ) pₜ · d = β E_t[u′(c_{t+1}) f_{t+1} · d]`. -/
theorem rd_euler_eq [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Θa : Set (List S → J → ℝ)}
    {c : List S → ℝ} {θ : List S → J → ℝ}
    (hsol : rd_Solves (rd_EU T β u) (rd_SeqFeas p f y θm1 Θa) c θ)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (d : J → ℝ)
    (hΘ : ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc d h ∈ Θa) : rd_Phi T β u' p f c h d = 0 := by
  have h1 := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs d (nhdsWithin_le_nhds hΘ)
  have hΘ' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), θ + ε • rd_loc (-d) h ∈ Θa := by
    have : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_id.neg : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 (-0))).mono_left
        nhdsWithin_le_nhds
    filter_upwards [this.eventually hΘ] with ε hε
    have e : (-ε) • rd_loc d h = ε • rd_loc (-d) h := by
      funext g j
      simp [rd_loc]
      split_ifs <;> simp
    rwa [e] at hε
  have h2 := rd_euler_dir T hβ0 hβ1 hu hd hsol h hch hcs (-d) hΘ'
  have h1' : rd_Phi T β u' p f c h d ≤ 0 := h1
  have h2' : rd_Phi T β u' p f c h (-d) ≤ 0 := h2
  rw [rd_Phi_neg] at h2'
  linarith

omit [Fintype S] in
/-- Feasibility near `0` of the perturbed debt-constrained strategy when the debt constraints at
the successors of `sᵗ` are slack. -/
theorem rd_DC_slack [Finite S] [DecidableEq S] {f : List S → J → ℝ} {Dbar : List S → ℝ}
    {θ : List S → J → ℝ} (hθ : θ ∈ rd_ThetaDC f Dbar) (h : List S)
    (hslack : ∀ s, -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h) (d : J → ℝ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), θ + ε • rd_loc d h ∈ rd_ThetaDC f Dbar := by
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, -Dbar (s :: h) < f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)
      := by
    refine Filter.eventually_all.2 fun s => ?_
    have : Tendsto (fun ε : ℝ => f (s :: h) ⬝ᵥ θ h + ε * (f (s :: h) ⬝ᵥ d)) (𝓝 0)
        (𝓝 (f (s :: h) ⬝ᵥ θ h)) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (f (s :: h) ⬝ᵥ d)).const_add _
    exact this.eventually (lt_mem_nhds (hslack s))
  filter_upwards [hev] with ε hε g s
  by_cases hg : g = h
  · subst hg
    simp only [Pi.add_apply, Pi.smul_apply, rd_loc, ↓reduceIte, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    exact (hε s).le
  · simpa [rd_loc, hg] using hθ g s

/-- **Arrow security prices** (Miao, p. 432). With Arrow securities, nonbinding debt constraints
at the successors of `sᵗ` and positive consumption, the first-order conditions give
`Q_t(s′ | sᵗ) = β u′(c_{t+1}(sᵗ, s′)) Pr(s′ | sᵗ) / u′(c_t(sᵗ))`. -/
theorem rd_arrow_price [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u u' : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {Q : List S → S → ℝ} {y : List S → ℝ} {a0 : S → ℝ} {Dbar : List S → ℝ}
    {c : List S → ℝ} {a : List S → S → ℝ}
    (hsol : rd_Solves (rd_EU T β u)
      (rd_SeqFeas Q rd_arrowPayoff y a0 (rd_ThetaDC rd_arrowPayoff Dbar)) c a)
    (h : List S) (hch : 0 < c h) (hcs : ∀ s, 0 < c (s :: h)) (hu'0 : 0 < u' (c h))
    (hslack : ∀ s, -Dbar (s :: h) < a h s) (s' : S) :
    Q h s' = β * u' (c (s' :: h)) * rd_condPr T h s' / u' (c h) := by
  have hsl : ∀ s, -Dbar (s :: h) < rd_arrowPayoff (s :: h) ⬝ᵥ a h := fun s => by
    simpa [rd_arrowPayoff, dotProduct] using hslack s
  have := rd_euler_eq T hβ0 hβ1 hu hd hsol h hch hcs (Pi.single s' 1)
    (rd_DC_slack hsol.1.2.2 h hsl _)
  simp only [rd_Phi, dotProduct_single, mul_one] at this
  have e : ∑ s, rd_condPr T h s * (u' (c (s :: h)) * rd_arrowPayoff (s :: h) s') =
      rd_condPr T h s' * u' (c (s' :: h)) := by
    simp [rd_arrowPayoff]
  rw [e] at this
  field_simp
  linarith

/-- Miao, p. 432: "Under complete markets the above equation does not depend on `i`": two agents
facing the same Arrow prices have equal intertemporal marginal rates of substitution. -/
theorem rd_arrow_price_common [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u₁ u₁' u₂ u₂' : ℝ → ℝ} (hu₁ : MonotoneOn u₁ (Set.Ici 0))
    (hd₁ : ∀ x, 0 < x → HasDerivAt u₁ (u₁' x) x) (hu₂ : MonotoneOn u₂ (Set.Ici 0))
    (hd₂ : ∀ x, 0 < x → HasDerivAt u₂ (u₂' x) x)
    {Q : List S → S → ℝ} {y₁ y₂ : List S → ℝ} {a₁ a₂ : S → ℝ} {D₁ D₂ : List S → ℝ}
    {c₁ c₂ : List S → ℝ} {θ₁ θ₂ : List S → S → ℝ}
    (hs₁ : rd_Solves (rd_EU T β u₁)
      (rd_SeqFeas Q rd_arrowPayoff y₁ a₁ (rd_ThetaDC rd_arrowPayoff D₁)) c₁ θ₁)
    (hs₂ : rd_Solves (rd_EU T β u₂)
      (rd_SeqFeas Q rd_arrowPayoff y₂ a₂ (rd_ThetaDC rd_arrowPayoff D₂)) c₂ θ₂)
    (h : List S) (h1 : 0 < c₁ h) (h1s : ∀ s, 0 < c₁ (s :: h)) (h1' : 0 < u₁' (c₁ h))
    (h2 : 0 < c₂ h) (h2s : ∀ s, 0 < c₂ (s :: h)) (h2' : 0 < u₂' (c₂ h))
    (hsl₁ : ∀ s, -D₁ (s :: h) < θ₁ h s) (hsl₂ : ∀ s, -D₂ (s :: h) < θ₂ h s) (s' : S) :
    β * u₁' (c₁ (s' :: h)) * rd_condPr T h s' / u₁' (c₁ h) =
      β * u₂' (c₂ (s' :: h)) * rd_condPr T h s' / u₂' (c₂ h) := by
  rw [← rd_arrow_price T hβ0 hβ1 hu₁ hd₁ hs₁ h h1 h1s h1' hsl₁ s',
    ← rd_arrow_price T hβ0 hβ1 hu₂ hd₂ hs₂ h h2 h2s h2' hsl₂ s']

/-- (13.7) with (13.16) (Miao, pp. 419, 429): if the Euler equation holds at every node for every
security, `q⁰_t(sᵗ) = βᵗ Pr(sᵗ) u′(c_t(sᵗ)) / u′(c₀(s⁰))` is a state price process. -/
theorem rd_statePrice_of_euler [DecidableEq J] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) {u' : ℝ → ℝ}
    {p f : List S → J → ℝ} {c : List S → ℝ} (hu'0 : ∀ h, 0 < u' (c h))
    (heul : ∀ h j, rd_Phi T β u' p f c h (Pi.single j 1) = 0) :
    rd_StatePrice p f fun h => β ^ h.length * T.Pr h * u' (c h) / u' (c []) := by
  refine ⟨fun h => div_pos (mul_pos (mul_pos (pow_pos hβ0 _) (T.pos h)) (hu'0 h)) (hu'0 []),
    fun h j => ?_⟩
  have := heul h j
  simp only [rd_Phi, dotProduct_single, mul_one, rd_condPr] at this
  have hP := (T.pos h).ne'
  have hu := (hu'0 h).ne'
  have hu0 := (hu'0 []).ne'
  have hb := (pow_pos hβ0 h.length).ne'
  have e : u' (c h) * p h j =
      β * ∑ s, T.Pr (s :: h) / T.Pr h * (u' (c (s :: h)) * f (s :: h) j) := by
    linarith
  have hsum : ∑ s, β ^ (s :: h).length * T.Pr (s :: h) * u' (c (s :: h)) / u' (c []) *
      f (s :: h) j = β ^ h.length * T.Pr h / u' (c []) *
        (β * ∑ s, T.Pr (s :: h) / T.Pr h * (u' (c (s :: h)) * f (s :: h) j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [List.length_cons, pow_succ]
    field_simp
  rw [hsum, ← e]
  field_simp

end Miao.CompleteMarkets
