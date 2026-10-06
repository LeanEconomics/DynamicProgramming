/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearValuation.OrderFixedPoints
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Concavity and stability in one dimension

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.2.1 (pp. 214–216).

* Proposition 7.1.2: an increasing concave self-map `g` of `(0, ∞)` is globally
  stable if every `x > 0` lies between an `a` with `a < g(a)` and a `b` with
  `g(b) ≤ b`. Orbits are monotone and bounded, concave functions are continuous on
  open intervals, so orbits converge to fixed points; and concavity together with
  `a < g(a)` rules out two fixed points.
* Exercise 7.1.2: the Solow–Swan map `g(k) = sAkᵅ + (1 − δ)k` satisfies the
  conditions, with the threshold `k* = (sA/δ)^{1/(1−α)}`.
* Exercise 7.1.3: the condition `a < g(a)` cannot be weakened to `a ≤ g(a)`; the
  identity satisfies the weakened conditions and has a fixed point at every `x`.
* Exercise 7.1.4: `g(k) = sf(k) + (1 − δ)k` is globally stable for any positive,
  increasing, concave, differentiable `f` satisfying the Inada conditions, by the
  tangent-line bounds `f(a) − f(a/2) ≥ f'(a)a/2` and `f(b) ≤ f(c) + f'(c)(b − c)`.
* Exercise 7.1.5: the Fajgelbaum et al. (2017) uncertainty map
  `g(s) = ρ²(1/s + a/η²)⁻¹ + γ` is globally stable on `(0, ∞)`.
-/

open Filter Topology Function Set

namespace SargentStachurski.NonlinearValuation

/-! ### Proposition 7.1.2 -/

/-- The orbit of `x` under an increasing self-map of `(0, ∞)` converges to a fixed point when it is
bounded on the side it moves towards. -/
theorem exists_fixedPt_tendsto_of_concave {g : ℝ → ℝ} (hmaps : MapsTo g (Ioi 0) (Ioi 0))
    (hmono : MonotoneOn g (Ioi 0)) (hcont : ContinuousOn g (Ioi 0)) {x a b : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hxb : x ≤ b) (hga : a < g a) (hgb : g b ≤ b) :
    ∃ L, 0 < L ∧ g L = L ∧ Tendsto (fun k : ℕ => g^[k] x) atTop (𝓝 L) := by
  have hx : x ∈ Ioi (0 : ℝ) := lt_of_lt_of_le ha hax
  have hb : b ∈ Ioi (0 : ℝ) := lt_of_lt_of_le hx hxb
  have hmem : ∀ k, g^[k] x ∈ Ioi (0 : ℝ) := fun k => hmaps.iterate k hx
  -- the iterates stay in `[a, b]`
  have hup : ∀ k, g^[k] x ≤ b := by
    intro k
    induction k with
    | zero => simpa using hxb
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (hmono (hmem k) hb ih).trans hgb
  have hlo : ∀ k, a ≤ g^[k] x := by
    intro k
    induction k with
    | zero => simpa using hax
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hga.le.trans (hmono ha (hmem k) ih)
  -- a limit `L` of the orbit is a fixed point
  have hfix : ∀ L, 0 < L → Tendsto (fun k : ℕ => g^[k] x) atTop (𝓝 L) → g L = L := by
    intro L hL hlim
    have h1 : Tendsto (fun k : ℕ => g (g^[k] x)) atTop (𝓝 (g L)) :=
      ((hcont.continuousAt (Ioi_mem_nhds hL)).tendsto).comp hlim
    have h2 : Tendsto (fun k : ℕ => g (g^[k] x)) atTop (𝓝 L) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun k => ?_
      simp [iterate_succ_apply']
    exact tendsto_nhds_unique h1 h2
  rcases le_total x (g x) with hxg | hxg
  · -- increasing orbit
    have hmon : Monotone fun k : ℕ => g^[k] x := by
      refine monotone_nat_of_le_succ fun k => ?_
      induction k with
      | zero => simpa using hxg
      | succ k ih =>
        calc g^[k + 1] x = g (g^[k] x) := iterate_succ_apply' _ _ _
          _ ≤ g (g^[k + 1] x) := hmono (hmem k) (hmem (k + 1)) ih
          _ = g^[k + 1 + 1] x := (iterate_succ_apply' _ _ _).symm
    have hbdd : BddAbove (range fun k : ℕ => g^[k] x) := ⟨b, by rintro _ ⟨k, rfl⟩; exact hup k⟩
    have hlim := tendsto_atTop_ciSup hmon hbdd
    have hL : 0 < ⨆ k : ℕ, g^[k] x := lt_of_lt_of_le (hmem 0) (le_ciSup hbdd 0)
    exact ⟨_, hL, hfix _ hL hlim, hlim⟩
  · -- decreasing orbit
    have hanti : Antitone fun k : ℕ => g^[k] x := by
      refine antitone_nat_of_succ_le fun k => ?_
      induction k with
      | zero => simpa using hxg
      | succ k ih =>
        calc g^[k + 1 + 1] x = g (g^[k + 1] x) := iterate_succ_apply' _ _ _
          _ ≤ g (g^[k] x) := hmono (hmem (k + 1)) (hmem k) ih
          _ = g^[k + 1] x := (iterate_succ_apply' _ _ _).symm
    have hbdd : BddBelow (range fun k : ℕ => g^[k] x) := ⟨a, by rintro _ ⟨k, rfl⟩; exact hlo k⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hL : 0 < ⨅ k : ℕ, g^[k] x := lt_of_lt_of_le ha (le_ciInf hlo)
    exact ⟨_, hL, hfix _ hL hlim, hlim⟩

/-- **Proposition 7.1.2** (p. 214): if `g` is an increasing concave self-map of `(0, ∞)` and every
`x > 0` satisfies `a ≤ x ≤ b` for some `a, b > 0` with `a < g(a)` and `g(b) ≤ b`, then `g` is
globally stable on `(0, ∞)`. -/
theorem globallyStableOn_of_concave {g : ℝ → ℝ} (hmaps : MapsTo g (Ioi 0) (Ioi 0))
    (hmono : MonotoneOn g (Ioi 0)) (hconc : ConcaveOn ℝ (Ioi 0) g)
    (hab : ∀ x, 0 < x → ∃ a b, 0 < a ∧ a ≤ x ∧ x ≤ b ∧ a < g a ∧ g b ≤ b) :
    GloballyStableOn g (Ioi 0) := by
  have hcont : ContinuousOn g (Ioi 0) := by
    have := hconc.continuousOn_interior
    rwa [interior_Ioi] at this
  -- uniqueness: two fixed points `x ≤ y` coincide
  have huniq : ∀ x y, 0 < x → 0 < y → g x = x → g y = y → x ≤ y → x = y := by
    intro x y hx hy hgx hgy hxy
    by_contra hne
    have hlt : x < y := lt_of_le_of_ne hxy hne
    obtain ⟨a, -, ha, hax, -, hga, -⟩ := hab x hx
    set l := (y - x) / (y - a) with hl
    have hya : 0 < y - a := by linarith
    have hl0 : 0 < l := div_pos (by linarith) hya
    have hl1 : l ≤ 1 := (div_le_one hya).2 (by linarith)
    have hxeq : l * a + (1 - l) * y = x := by
      rw [hl]
      field_simp
      ring
    have h1 := hconc.2 (show a ∈ Ioi (0 : ℝ) from ha) (show y ∈ Ioi (0 : ℝ) from hy) hl0.le
      (by linarith) (by ring : l + (1 - l) = 1)
    simp only [smul_eq_mul, hxeq, hgx, hgy] at h1
    nlinarith [mul_lt_mul_of_pos_left hga hl0]
  obtain ⟨a, b, ha, hax, hxb, hga, hgb⟩ := hab 1 one_pos
  obtain ⟨L, hL, hgL, -⟩ := exists_fixedPt_tendsto_of_concave hmaps hmono hcont ha hax hxb hga hgb
  have huniq' : ∀ y, 0 < y → g y = y → y = L := fun y hy hgy => by
    rcases le_total y L with h | h
    · exact huniq y L hy hL hgy hgL h
    · exact (huniq L y hL hy hgL hgy h).symm
  refine ⟨L, hL, hgL, fun y hy hgy => huniq' y hy hgy, fun x hx => ?_⟩
  obtain ⟨a', b', ha', hax', hxb', hga', hgb'⟩ := hab x hx
  obtain ⟨L', hL', hgL', hlim⟩ :=
    exists_fixedPt_tendsto_of_concave hmaps hmono hcont ha' hax' hxb' hga' hgb'
  rwa [huniq' L' hL' hgL'] at hlim

/-! ### Exercise 7.1.2: the Solow–Swan model -/

/-- The Solow–Swan map `g(k) = sAkᵅ + (1 − δ)k` (Vol. 1, (1.19), Exercise 1.2.25). -/
noncomputable def solowSwan (s A α δ : ℝ) (k : ℝ) : ℝ := s * A * k ^ α + (1 - δ) * k

/-- Exercise 7.1.2 (p. 216): the Solow–Swan map with `A, s > 0`, `0 < α < 1` and `0 < δ < 1`
satisfies the conditions of Proposition 7.1.2, so it is globally stable on `(0, ∞)`. -/
theorem globallyStableOn_solowSwan {s A α δ : ℝ} (hs : 0 < s) (hA : 0 < A) (hα0 : 0 < α)
    (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) : GloballyStableOn (solowSwan s A α δ) (Ioi 0) := by
  have hsA : 0 < s * A := mul_pos hs hA
  set kstar : ℝ := (s * A / δ) ^ (1 - α)⁻¹ with hk
  have h1α : 0 < 1 - α := by linarith
  have hkpos : 0 < kstar := Real.rpow_pos_of_pos (div_pos hsA hδ0) _
  have hkpow : kstar ^ (1 - α) = s * A / δ :=
    Real.rpow_inv_rpow (div_pos hsA hδ0).le h1α.ne'
  -- `k = kᵅ k^{1−α}`
  have hsplit : ∀ k : ℝ, 0 < k → k = k ^ α * k ^ (1 - α) := fun k hk => by
    rw [← Real.rpow_add hk]
    simp
  -- below `k*` the map moves up, above `k*` it moves down
  have hup : ∀ k : ℝ, 0 < k → k < kstar → k < solowSwan s A α δ k := by
    intro k hk hlt
    have h1 : k ^ (1 - α) < s * A / δ := by
      rw [← hkpow]
      exact Real.rpow_lt_rpow hk.le hlt h1α
    have hkα : 0 < k ^ α := Real.rpow_pos_of_pos hk α
    have h2 : δ * k ^ (1 - α) < s * A := by
      rw [lt_div_iff₀ hδ0] at h1
      linarith
    have h3 : δ * k < s * A * k ^ α := by
      conv_lhs => rw [hsplit k hk]
      nlinarith [mul_lt_mul_of_pos_right h2 hkα]
    unfold solowSwan
    linarith
  have hdown : ∀ k : ℝ, 0 < k → kstar ≤ k → solowSwan s A α δ k ≤ k := by
    intro k hk hle
    have h1 : s * A / δ ≤ k ^ (1 - α) := by
      rw [← hkpow]
      exact Real.rpow_le_rpow hkpos.le hle h1α.le
    have hkα : 0 < k ^ α := Real.rpow_pos_of_pos hk α
    have h2 : s * A ≤ δ * k ^ (1 - α) := by
      rw [div_le_iff₀ hδ0] at h1
      linarith
    unfold solowSwan
    have h3 : s * A * k ^ α ≤ δ * (k ^ α * k ^ (1 - α)) := by nlinarith
    rw [← hsplit k hk] at h3
    linarith
  refine globallyStableOn_of_concave ?_ ?_ ?_ ?_
  · intro k hk
    have : 0 < k ^ α := Real.rpow_pos_of_pos hk α
    have hk' : (0 : ℝ) < k := hk
    change 0 < s * A * k ^ α + (1 - δ) * k
    nlinarith
  · intro k hk k' hk' hkk'
    unfold solowSwan
    have := Real.rpow_le_rpow (le_of_lt hk) hkk' hα0.le
    nlinarith
  · have h1 : ConcaveOn ℝ (Ioi 0) fun k : ℝ => k ^ α :=
      (Real.concaveOn_rpow hα0.le hα1.le).subset Ioi_subset_Ici_self (convex_Ioi 0)
    have h2 := (h1.smul hsA.le).add ((concaveOn_id (convex_Ioi (0 : ℝ))).smul (by linarith :
      (0 : ℝ) ≤ 1 - δ))
    refine h2.congr fun k _ => ?_
    simp [solowSwan, smul_eq_mul]
  · intro x hx
    refine ⟨min x (kstar / 2), max x kstar, lt_min hx (by positivity), min_le_left _ _,
      le_max_left _ _, hup _ (lt_min hx (by positivity)) ((min_le_right _ _).trans_lt
        (by linarith)), hdown _ (lt_of_lt_of_le hx (le_max_left _ _)) (le_max_right _ _)⟩

/-! ### Exercise 7.1.3 -/

/-- Exercise 7.1.3 (p. 216): the condition `a < g(a)` in Proposition 7.1.2 cannot be weakened to
`a ≤ g(a)`: the identity map is an increasing concave self-map of `(0, ∞)` satisfying the weakened
conditions, but it is not globally stable. -/
theorem not_globallyStableOn_id :
    MapsTo (id : ℝ → ℝ) (Ioi 0) (Ioi 0) ∧ MonotoneOn (id : ℝ → ℝ) (Ioi 0) ∧
      ConcaveOn ℝ (Ioi (0 : ℝ)) id ∧
      (∀ x : ℝ, 0 < x → ∃ a b : ℝ, 0 < a ∧ a ≤ x ∧ x ≤ b ∧ a ≤ id a ∧ id b ≤ b) ∧
      ¬ GloballyStableOn (id : ℝ → ℝ) (Ioi 0) := by
  refine ⟨fun x hx => hx, fun _ _ _ _ h => h, concaveOn_id (convex_Ioi 0),
    fun x hx => ⟨x, x, hx, le_rfl, le_rfl, le_rfl, le_rfl⟩, ?_⟩
  rintro ⟨u, -, -, huniq, -⟩
  have h1 := huniq 1 (mem_Ioi.2 one_pos) rfl
  have h2 := huniq 2 (mem_Ioi.2 two_pos) rfl
  linarith

/-! ### Exercise 7.1.4: Inada conditions -/

/-- Exercise 7.1.4 (p. 216): if `f` is strictly positive, increasing, concave and differentiable on
`(0, ∞)` with `f'(k) → ∞` as `k ↓ 0` and `f'(k) → 0` as `k → ∞`, and `0 < s, δ < 1`, then
`g(k) = sf(k) + (1 − δ)k` is globally stable on `(0, ∞)`. -/
theorem globallyStableOn_solow_inada {f : ℝ → ℝ} {s δ : ℝ} (hs0 : 0 < s) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hfpos : ∀ k, 0 < k → 0 < f k) (hfmono : MonotoneOn f (Ioi 0))
    (hfconc : ConcaveOn ℝ (Ioi 0) f) (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hinada0 : Tendsto (deriv f) (𝓝[>] 0) atTop) (hinada1 : Tendsto (deriv f) atTop (𝓝 0)) :
    GloballyStableOn (fun k => s * f k + (1 - δ) * k) (Ioi 0) := by
  refine globallyStableOn_of_concave ?_ ?_ ?_ ?_
  · intro k hk
    have := hfpos k hk
    have hk' : (0 : ℝ) < k := hk
    change 0 < s * f k + (1 - δ) * k
    nlinarith
  · intro k hk k' hk' hkk'
    have := hfmono hk hk' hkk'
    change s * f k + (1 - δ) * k ≤ s * f k' + (1 - δ) * k'
    nlinarith
  · have h2 := (hfconc.smul hs0.le).add ((concaveOn_id (convex_Ioi (0 : ℝ))).smul (by linarith :
      (0 : ℝ) ≤ 1 - δ))
    refine h2.congr fun k _ => ?_
    simp [smul_eq_mul]
  · intro x hx
    -- small `a`: `f'(a) ≥ 2δ/s`
    obtain ⟨ε, hε, hεP⟩ : ∃ ε > 0, ∀ k, 0 < k → k < ε → 2 * δ / s ≤ deriv f k := by
      have hev := hinada0.eventually (eventually_ge_atTop (2 * δ / s))
      rcases (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev with ⟨ε, hε, hεP⟩
      exact ⟨ε, hε, fun k hk hkε => hεP ⟨hk, by simpa using hkε⟩⟩
    -- large `c`: `f'(c) ≤ δ/(2s)`
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, ∀ c, c₀ ≤ c → deriv f c ≤ δ / (2 * s) := by
      have := hinada1.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < δ / (2 * s)))
      rw [eventually_atTop] at this
      exact this
    set a := min x (ε / 2) with ha
    have ha0 : 0 < a := lt_min hx (by positivity)
    have haε : a < ε := (min_le_right _ _).trans_lt (by linarith)
    set c := max c₀ 1 with hc
    have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    set b := max x (max (c + 1) (2 * s * f c / δ)) with hb
    have hcb : c < b := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans (le_max_right _ _))
    refine ⟨a, b, ha0, min_le_left _ _, le_max_left _ _, ?_, ?_⟩
    · -- `f(a) − f(a/2) ≥ f'(a)·a/2 ≥ δa/s`
      have h1 := hfconc.deriv_le_slope (mem_Ioi.2 (by positivity : (0 : ℝ) < a / 2))
        (show a ∈ Ioi (0 : ℝ) from ha0) (by linarith) (hfdiff a ha0)
      rw [slope_def_field] at h1
      have h2 := hεP a ha0 haε
      have h3 : a - a / 2 = a / 2 := by ring
      rw [h3, le_div_iff₀ (by positivity)] at h1
      have h4 := hfpos (a / 2) (by positivity)
      have h5 : 2 * δ / s * (a / 2) ≤ deriv f a * (a / 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h6 : 2 * δ / s * (a / 2) = δ * a / s := by field_simp
      have h7 : δ * a < s * f a := by
        rw [h6] at h5
        have := lt_of_le_of_lt (h5.trans h1) (by linarith : f a - f (a / 2) < f a)
        rwa [div_lt_iff₀ hs0, mul_comm (f a) s] at this
      change a < s * f a + (1 - δ) * a
      linarith
    · -- `f(b) ≤ f(c) + f'(c)(b − c)` and `f'(c) ≤ δ/(2s)`
      have h1 := hfconc.slope_le_deriv (show c ∈ Ioi (0 : ℝ) from hc0)
        (show b ∈ Ioi (0 : ℝ) from hc0.trans hcb) hcb (hfdiff c hc0)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
      have h2 := hc₀ c (le_max_left _ _)
      have hbc : 0 ≤ b - c := by linarith
      have h3 : deriv f c * (b - c) ≤ δ / (2 * s) * b := by
        have := mul_le_mul_of_nonneg_right h2 hbc
        have h4 : δ / (2 * s) * (b - c) ≤ δ / (2 * s) * b :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      have h5 : 2 * s * f c / δ ≤ b := (le_max_right _ _).trans (le_max_right _ _)
      rw [div_le_iff₀ hδ0] at h5
      have h6 : s * (δ / (2 * s) * b) = δ * b / 2 := by field_simp
      change s * f b + (1 - δ) * b ≤ b
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans' (le_refl _)) hs0.le]

/-! ### Exercise 7.1.5: aggregate uncertainty -/

/-- The law of motion of Fajgelbaum et al. (2017): `g(s) = ρ²(1/s + a/η²)⁻¹ + γ`. -/
noncomputable def fajgelbaum (ρ a η γ : ℝ) (s : ℝ) : ℝ := ρ ^ 2 * (1 / s + a / η ^ 2)⁻¹ + γ

/-- `s ↦ (1/s + c)⁻¹` is concave on `(0, ∞)` for `c ≥ 0`. -/
theorem concaveOn_inv_inv_add {c : ℝ} (hc : 0 ≤ c) :
    ConcaveOn ℝ (Ioi 0) fun s => (1 / s + c)⁻¹ := by
  refine ⟨convex_Ioi 0, fun x hx y hy p q hp hq hpq => ?_⟩
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hS : 0 < p * x + q * y := by
    have hm := lt_min hx' hy'
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left x y) hp,
      mul_le_mul_of_nonneg_left (min_le_right x y) hq]
  have hform : ∀ z : ℝ, 0 < z → (1 / z + c)⁻¹ = z / (1 + c * z) := fun z hz => by
    field_simp
  simp only [smul_eq_mul]
  rw [hform x hx', hform y hy', hform _ hS]
  have hq' : q = 1 - p := by linarith
  subst hq'
  have h1 : 0 < 1 + c * x := by positivity
  have h2 : 0 < 1 + c * y := by positivity
  have h3 : 0 < 1 + c * (p * x + (1 - p) * y) := by positivity
  have key : (p * x + (1 - p) * y) / (1 + c * (p * x + (1 - p) * y)) -
      (p * (x / (1 + c * x)) + (1 - p) * (y / (1 + c * y))) =
      c * p * (1 - p) * (y - x) ^ 2 / ((1 + c * x) * (1 + c * y) *
        (1 + c * (p * x + (1 - p) * y))) := by
    field_simp
    ring
  have hnn : 0 ≤ c * p * (1 - p) * (y - x) ^ 2 / ((1 + c * x) * (1 + c * y) *
      (1 + c * (p * x + (1 - p) * y))) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg (mul_nonneg hc hp) hq) (sq_nonneg _)
  linarith

/-- Exercise 7.1.5 (p. 216): for `a, η, γ > 0` and `0 < ρ < 1`, the map
`g(s) = ρ²(1/s + a/η²)⁻¹ + γ` is globally stable on `(0, ∞)`. -/
theorem globallyStableOn_fajgelbaum {ρ a η γ : ℝ} (hρ0 : 0 < ρ) (ha : 0 < a) (hη : 0 < η)
    (hγ : 0 < γ) : GloballyStableOn (fajgelbaum ρ a η γ) (Ioi 0) := by
  set c := a / η ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hpos : ∀ s : ℝ, 0 < s → 0 < (1 / s + c)⁻¹ := fun s hs => by positivity
  have hbound : ∀ s : ℝ, 0 < s → (1 / s + c)⁻¹ ≤ c⁻¹ := fun s hs =>
    inv_anti₀ hc0 (by have : 0 < 1 / s := (by positivity); linarith)
  refine globallyStableOn_of_concave ?_ ?_ ?_ ?_
  · intro s hs
    have := hpos s hs
    change 0 < ρ ^ 2 * (1 / s + a / η ^ 2)⁻¹ + γ
    rw [← hc]
    positivity
  · intro s hs t ht hst
    change ρ ^ 2 * (1 / s + a / η ^ 2)⁻¹ + γ ≤ ρ ^ 2 * (1 / t + a / η ^ 2)⁻¹ + γ
    rw [← hc]
    have hs' : (0 : ℝ) < s := hs
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 / t + c ≤ 1 / s + c := by
      have := one_div_le_one_div_of_le hs' hst
      linarith
    have h2 := inv_anti₀ (by have : 0 < 1 / t := (by positivity); linarith) h1
    nlinarith [sq_nonneg ρ]
  · have h := ((concaveOn_inv_inv_add hc0.le).smul (sq_nonneg ρ)).add_const γ
    refine h.congr fun s _ => ?_
    simp [fajgelbaum, smul_eq_mul, hc]
  · intro x hx
    refine ⟨min x (γ / 2), max x (ρ ^ 2 * c⁻¹ + γ), lt_min hx (by positivity), min_le_left _ _,
      le_max_left _ _, ?_, ?_⟩
    · have := hpos (min x (γ / 2)) (lt_min hx (by positivity))
      have hm : min x (γ / 2) ≤ γ / 2 := min_le_right _ _
      change min x (γ / 2) < ρ ^ 2 * (1 / min x (γ / 2) + a / η ^ 2)⁻¹ + γ
      rw [← hc]
      nlinarith [sq_nonneg ρ, mul_nonneg (sq_nonneg ρ) this.le]
    · have hb : 0 < max x (ρ ^ 2 * c⁻¹ + γ) := lt_of_lt_of_le hx (le_max_left _ _)
      have := hbound _ hb
      change ρ ^ 2 * (1 / max x (ρ ^ 2 * c⁻¹ + γ) + a / η ^ 2)⁻¹ + γ ≤ max x (ρ ^ 2 * c⁻¹ + γ)
      rw [← hc]
      have h2 := mul_le_mul_of_nonneg_left this (sq_nonneg ρ)
      linarith [le_max_right x (ρ ^ 2 * c⁻¹ + γ)]

end SargentStachurski.NonlinearValuation
