/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyOptimum

/-!
# The one-sector model under certainty: interest rates (Exercise 16.1(d))

SLP §16.1, p. 478. Let `(x⁰, x⁰, φ)` be a competitive equilibrium of the one-consumer, one-firm
economy of §16.1, with prices `p_t = φ(e_t)` (positive by `gc_price_pos`) and interest rates
`1 + r_t = p_t/p_{t+1}` (`gcRate`), and let `k` be a capital path supporting `x⁰`.

* `gcU_sub_of_eq_off_pair`: changing a consumption sequence only at dates `t`, `t + 1` changes `u`
  by the two discounted utility differences.
* `gc_consumer_foc` (the marginal rate of substitution): if `x⁰_t, x⁰_{t+1} > 0`, then
  `p_{t+1} U′(x⁰_t) = β U′(x⁰_{t+1}) p_t` — shifting consumption between `t` and `t + 1` at constant
  cost cannot raise `u`.
* `gc_firm_foc` (the marginal rate of transformation): if `y⁰_t, y⁰_{t+1}, k_{t+1} > 0`, then
  `p_t = p_{t+1} f′(k_{t+1})` — shifting output from `y_t` into `k_{t+1}` cannot raise profit.
* **Exercise 16.1(d)** (`ex_16_1d`): `1 + r_t = U′(x⁰_t)/(β U′(x⁰_{t+1})) = f′(k_{t+1})`, and
  (`ex_16_1d_unique`) any two competitive equilibria have the same allocation and the same
  relative prices `p_t/p_0`, hence the same interest rates.

**Correction.** The exercise needs an interior allocation (`x⁰_t > 0`, `k_{t+1} > 0`): at a corner
the first-order conditions are inequalities and do not pin down `p_{t+1}/p_t`. Interiority is a
hypothesis here (Exercise 5.1d gives sufficient conditions, e.g. `U′(0) = ∞`). The FOCs are proved
directly from (E2) and (E3) by one-dimensional perturbations, with no Lagrangian.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

variable {U f : ℝ → ℝ} {β khat kbar : ℝ}

/-- Changing a sequence in `X` only at dates `t` and `t + 1` changes `u` by
`βᵗ[U(z_t) − U(x_t)] + β^{t+1}[U(z_{t+1}) − U(x_{t+1})]`. -/
theorem gcU_sub_of_eq_off_pair (h : GrowthCertaintyHyp U f β khat kbar) {x z : BddSeq ℝ}
    (hx : x ∈ gcX) (hz : z ∈ gcX) {t : ℕ} (hzx : ∀ s, s ≠ t → s ≠ t + 1 → z s = x s) :
    gcU β U z - gcU β U x = β ^ t * (U (z t) - U (x t)) +
      β ^ (t + 1) * (U (z (t + 1)) - U (x (t + 1))) := by
  change ∑' s, β ^ s * U (z s) - ∑' s, β ^ s * U (x s) = _
  rw [← (gc_summable h hz).tsum_sub (gc_summable h hx),
    tsum_eq_sum (s := {t, t + 1}) fun s hs => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      rw [hzx s hs.1 hs.2, sub_self],
    Finset.sum_pair (by omega)]
  ring

/-- **The consumer's first-order condition** (marginal rate of substitution, Ex 16.1d). If `x⁰` is
utility-maximising on the budget set `{z ∈ X : φ(z) ≤ φ(x⁰)}` ((E2)), `x⁰_t, x⁰_{t+1} > 0` and `U`
is differentiable there, then `p_{t+1} U′(x⁰_t) = β U′(x⁰_{t+1}) p_t`. -/
theorem gc_consumer_foc (h : GrowthCertaintyHyp U f β khat kbar) {x₀ : BddSeq ℝ}
    (hx₀ : x₀ ∈ gcX) {φ : StrongDual ℝ (BddSeq ℝ)}
    (hE2 : ∀ z ∈ gcX, φ z ≤ φ x₀ → gcU β U z ≤ gcU β U x₀) {t : ℕ} (ht : 0 < x₀ t)
    (ht1 : 0 < x₀ (t + 1)) {d₀ d₁ : ℝ} (hd₀ : HasDerivAt U d₀ (x₀ t))
    (hd₁ : HasDerivAt U d₁ (x₀ (t + 1))) :
    φ (lp.single ∞ (t + 1) 1) * d₀ = β * d₁ * φ (lp.single ∞ t 1) := by
  set a := φ (lp.single ∞ (t + 1) 1) with ha
  set b := φ (lp.single ∞ t 1) with hb
  set z : ℝ → BddSeq ℝ := fun ε => x₀ + (-(ε * a)) • (lp.single ∞ t (1 : ℝ) : BddSeq ℝ) +
    (ε * b) • (lp.single ∞ (t + 1) (1 : ℝ) : BddSeq ℝ) with hz
  have hzc : ∀ ε s, z ε s = x₀ s + (if s = t then -(ε * a) else 0) +
      (if s = t + 1 then ε * b else 0) := fun ε s => by
    simp only [hz, gc_coord_add, gc_coord_smul, gc_coord_single]
    split_ifs <;> ring
  have hφz : ∀ ε, φ (z ε) = φ x₀ := fun ε => by
    simp only [hz, map_add, map_smul, smul_eq_mul, ← ha, ← hb]
    ring
  set g : ℝ → ℝ := fun ε => β ^ t * U (x₀ t - ε * a) + β ^ (t + 1) * U (x₀ (t + 1) + ε * b)
    with hg
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < x₀ t - ε * a ∧ 0 < x₀ (t + 1) + ε * b := by
    have c1 : Tendsto (fun ε : ℝ => x₀ t - ε * a) (𝓝 0) (𝓝 (x₀ t)) :=
      Continuous.tendsto' (by fun_prop) 0 _ (by simp)
    have c2 : Tendsto (fun ε : ℝ => x₀ (t + 1) + ε * b) (𝓝 0) (𝓝 (x₀ (t + 1))) :=
      Continuous.tendsto' (by fun_prop) 0 _ (by simp)
    exact (c1.eventually_const_lt ht).and (c2.eventually_const_lt ht1)
  have hmax : IsLocalMax g 0 := by
    filter_upwards [hev] with ε hε
    have hzX : z ε ∈ gcX := mem_gcX.2 fun s => by
      rw [hzc]
      have := mem_gcX.1 hx₀ s
      split_ifs with h1 h2 h2
      · exfalso; omega
      · subst h1; linarith [hε.1]
      · subst h2; linarith [hε.2]
      · linarith
    have hle := hE2 _ hzX (hφz ε).le
    have hdiff := gcU_sub_of_eq_off_pair h hx₀ hzX (t := t) fun s hs hs1 => by
      rw [hzc]; split_ifs <;> first | (exfalso; omega) | ring
    have e1 : z ε t = x₀ t - ε * a := by
      rw [hzc]; split_ifs <;> first | (exfalso; omega) | ring
    have e2 : z ε (t + 1) = x₀ (t + 1) + ε * b := by
      rw [hzc]; split_ifs <;> first | (exfalso; omega) | ring
    rw [e1, e2] at hdiff
    simp only [hg, sub_zero, zero_mul, add_zero]
    linarith
  have hd₀' : HasDerivAt U d₀ (x₀ t - 0 * a) := by simpa using hd₀
  have hd₁' : HasDerivAt U d₁ (x₀ (t + 1) + 0 * b) := by simpa using hd₁
  have hgd : HasDerivAt g (β ^ t * (d₀ * -(1 * a)) + β ^ (t + 1) * (d₁ * (1 * b))) 0 :=
    ((hd₀'.comp 0 (((hasDerivAt_id 0).mul_const a).const_sub (x₀ t))).const_mul (β ^ t)).add
      ((hd₁'.comp 0 (((hasDerivAt_id 0).mul_const b).const_add (x₀ (t + 1)))).const_mul
        (β ^ (t + 1)))
  have h0 := hmax.hasDerivAt_eq_zero hgd
  have hβt : 0 < β ^ t := pow_pos h.beta_pos t
  have : β ^ t * (β * d₁ * b - a * d₀) = 0 := by rw [← h0]; ring
  have := (mul_eq_zero.1 this).resolve_left hβt.ne'
  linarith

/-- **The firm's first-order condition** (marginal rate of transformation, Ex 16.1d). If `y⁰`
maximises profit on `Y` ((E3)), is supported by the capital path `k`, `y⁰_t, y⁰_{t+1}, k_{t+1} > 0`
and `f` is differentiable at `k_{t+1}`, then `p_t = p_{t+1} f′(k_{t+1})`. -/
theorem gc_firm_foc {y₀ : BddSeq ℝ}
    {φ : StrongDual ℝ (BddSeq ℝ)} (hE3 : ∀ w ∈ gcY f khat, φ w ≤ φ y₀) {k : ℕ → ℝ}
    (hy0 : ∀ t, 0 ≤ y₀ t) (hk0 : k 0 = khat) (hk : ∀ t, 0 ≤ k t)
    (hkf : ∀ t, k (t + 1) + y₀ t ≤ f (k t)) {t : ℕ} (ht : 0 < y₀ t) (ht1 : 0 < y₀ (t + 1))
    (hkt : 0 < k (t + 1)) {d : ℝ} (hd : HasDerivAt f d (k (t + 1))) :
    φ (lp.single ∞ t 1) = φ (lp.single ∞ (t + 1) 1) * d := by
  set a := φ (lp.single ∞ t 1) with ha
  set b := φ (lp.single ∞ (t + 1) 1) with hb
  set Δ : ℝ → ℝ := fun ε => f (k (t + 1) + ε) - f (k (t + 1)) with hΔ
  set w : ℝ → BddSeq ℝ := fun ε => y₀ + (-ε) • (lp.single ∞ t (1 : ℝ) : BddSeq ℝ) +
    Δ ε • (lp.single ∞ (t + 1) (1 : ℝ) : BddSeq ℝ) with hw
  have hwc : ∀ ε s, w ε s = y₀ s + (if s = t then -ε else 0) + (if s = t + 1 then Δ ε else 0) :=
    fun ε s => by
      simp only [hw, gc_coord_add, gc_coord_smul, gc_coord_single]
      split_ifs <;> ring
  set G : ℝ → ℝ := fun ε => -ε * a + Δ ε * b with hG
  have hφw : ∀ ε, φ (w ε) = φ y₀ + G ε := fun ε => by
    simp only [hw, hG, map_add, map_smul, smul_eq_mul, ← ha, ← hb]
    ring
  have hcont : Tendsto Δ (𝓝 0) (𝓝 0) := by
    have h1 : ContinuousAt (fun ε => f (k (t + 1) + ε)) 0 :=
      hd.continuousAt.comp_of_eq (by fun_prop : ContinuousAt (fun ε : ℝ => k (t + 1) + ε) 0)
        (by simp)
    simpa [hΔ] using h1.tendsto.sub_const (f (k (t + 1)))
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < y₀ t ∧ -k (t + 1) < ε ∧ -y₀ (t + 1) < Δ ε :=
    ((tendsto_id.eventually_lt_const ht).and (tendsto_id.eventually_const_lt (by linarith))).and
      (hcont.eventually_const_lt (by linarith)) |>.mono fun _ h => ⟨h.1.1, h.1.2, h.2⟩
  have hmax : IsLocalMax G 0 := by
    filter_upwards [hev] with ε hε
    set k' : ℕ → ℝ := Function.update k (t + 1) (k (t + 1) + ε) with hk'
    have hwY : w ε ∈ gcY f khat := by
      refine ⟨fun s => ?_, k', ?_, fun s => ?_, fun s => ?_⟩
      · rw [hwc]
        have := hy0 s
        split_ifs with h1 h2 h2
        · exfalso; omega
        · subst h1; linarith [hε.1]
        · subst h2; linarith [hε.2.2]
        · linarith
      · rw [hk', Function.update_of_ne (by omega), hk0]
      · rw [hk']
        by_cases hs : s = t + 1
        · subst hs
          rw [Function.update_self]
          linarith [hε.2.1]
        · rw [Function.update_of_ne hs]
          exact hk s
      · rw [hwc]
        have hk1 := hkf s
        by_cases hs : s = t
        · subst hs
          have e1 : k' (s + 1) = k (s + 1) + ε := by rw [hk', Function.update_self]
          have e2 : k' s = k s := by rw [hk', Function.update_of_ne (by omega)]
          rw [e1, e2]
          split_ifs <;> first | (exfalso; omega) | linarith
        · by_cases hs1 : s = t + 1
          · subst hs1
            have e1 : k' (t + 1 + 1) = k (t + 1 + 1) := by
              rw [hk', Function.update_of_ne (by omega)]
            have e2 : k' (t + 1) = k (t + 1) + ε := by rw [hk', Function.update_self]
            rw [e1, e2]
            split_ifs <;> first | (exfalso; omega) | (simp only [hΔ]; linarith)
          · have e1 : k' (s + 1) = k (s + 1) := by rw [hk', Function.update_of_ne (by omega)]
            have e2 : k' s = k s := by rw [hk', Function.update_of_ne hs1]
            rw [e1, e2]
            split_ifs
            linarith
    have := hE3 _ hwY
    rw [hφw] at this
    simp only [hG, hΔ, add_zero, sub_self, zero_mul, neg_zero]
    linarith
  have hd' : HasDerivAt (fun ε => f (k (t + 1) + ε)) d 0 := by
    have := hd
    rw [← add_zero (k (t + 1))] at this
    exact HasDerivAt.comp_const_add _ _ this
  have hGd : HasDerivAt G (-1 * a + d * b) 0 :=
    ((hasDerivAt_id (0 : ℝ)).neg.mul_const a).add ((hd'.sub_const (f (k (t + 1)))).mul_const b)
  have := hmax.hasDerivAt_eq_zero hGd
  linarith

/-- **Exercise 16.1(d)**: in a competitive equilibrium `(x⁰, x⁰, φ)` with an interior allocation
(`x⁰_t > 0`, supporting capital `k_{t+1} > 0`) and `U`, `f` differentiable,
`1 + r_t = p_t/p_{t+1} = f′(k_{t+1})` (marginal rate of transformation) and
`(1 + r_t) β U′(x⁰_{t+1}) = U′(x⁰_t)` (marginal rate of substitution). -/
theorem ex_16_1d (h : GrowthCertaintyHyp U f β khat kbar) {x₀ : BddSeq ℝ}
    {φ : StrongDual ℝ (BddSeq ℝ)}
    (hCE : CompetitiveEq (fun _ : Unit => gcX) (fun _ => gcU β U) (fun _ : Unit => gcY f khat)
      (fun _ => x₀) (fun _ => x₀) φ)
    {k : ℕ → ℝ} (hk0 : k 0 = khat) (hk : ∀ t, 0 ≤ k t) (hkf : ∀ t, k (t + 1) + x₀ t ≤ f (k t))
    (hint : ∀ t, 0 < x₀ t) (hkint : ∀ t, 0 < k (t + 1)) {dU df : ℝ → ℝ}
    (hdU : ∀ c, 0 < c → HasDerivAt U (dU c) c) (hdf : ∀ c, 0 < c → HasDerivAt f (df c) c)
    (t : ℕ) :
    1 + gcRate (fun s => φ (lp.single ∞ s 1)) t = df (k (t + 1)) ∧
      (1 + gcRate (fun s => φ (lp.single ∞ s 1)) t) * (β * dU (x₀ (t + 1))) = dU (x₀ t) := by
  have hp : ∀ s, 0 < φ (lp.single ∞ s 1) := gc_price_pos h hCE ()
  have hx₀ : x₀ ∈ gcX := hCE.1.1 ()
  have hfirm := gc_firm_foc (hCE.2.2 ()) (fun s => mem_gcX.1 hx₀ s) hk0 hk hkf (hint t)
    (hint (t + 1)) (hkint t) (hdf _ (hkint t))
  have hcons := gc_consumer_foc h hx₀ (hCE.2.1 ()) (hint t) (hint (t + 1)) (hdU _ (hint t))
    (hdU _ (hint (t + 1)))
  have hp1 := (hp (t + 1)).ne'
  simp only [gcRate, add_sub_cancel]
  constructor
  · rw [hfirm]
    field_simp
  · rw [div_mul_eq_mul_div, div_eq_iff hp1]
    linarith

/-- **Exercise 16.1(d), uniqueness**: any two competitive equilibria `(x⁰, x⁰, φ)`, `(x¹, x¹, φ′)`
have the same allocation (Ex 16.1a) and, if it is interior with interior supporting capital, the
same relative prices `p_t/p_0` and interest rates `r_t`. -/
theorem ex_16_1d_unique (h : GrowthCertaintyHyp U f β khat kbar) {x₀ x₁ : BddSeq ℝ}
    {φ φ' : StrongDual ℝ (BddSeq ℝ)}
    (hCE : CompetitiveEq (fun _ : Unit => gcX) (fun _ => gcU β U) (fun _ : Unit => gcY f khat)
      (fun _ => x₀) (fun _ => x₀) φ)
    (hCE' : CompetitiveEq (fun _ : Unit => gcX) (fun _ => gcU β U) (fun _ : Unit => gcY f khat)
      (fun _ => x₁) (fun _ => x₁) φ')
    {k : ℕ → ℝ} (hk0 : k 0 = khat) (hk : ∀ t, 0 ≤ k t) (hkf : ∀ t, k (t + 1) + x₀ t ≤ f (k t))
    (hint : ∀ t, 0 < x₀ t) (hkint : ∀ t, 0 < k (t + 1)) {dU df : ℝ → ℝ}
    (hdU : ∀ c, 0 < c → HasDerivAt U (dU c) c) (hdf : ∀ c, 0 < c → HasDerivAt f (df c) c) :
    x₁ = x₀ ∧ (∀ t, gcRate (fun s => φ' (lp.single ∞ s 1)) t =
      gcRate (fun s => φ (lp.single ∞ s 1)) t) ∧
      ∀ t, φ' (lp.single ∞ t 1) / φ' (lp.single ∞ 0 1) =
        φ (lp.single ∞ t 1) / φ (lp.single ∞ 0 1) := by
  have hx : x₁ = x₀ := ((ex_16_1a (ι := Unit) h).2.2 x₁ x₁ x₀ x₀ φ' φ hCE' hCE).1
  subst hx
  have hr : ∀ t, gcRate (fun s => φ' (lp.single ∞ s 1)) t =
      gcRate (fun s => φ (lp.single ∞ s 1)) t := fun t => by
    have h1 := (ex_16_1d h hCE' hk0 hk hkf hint hkint hdU hdf t).1
    have h2 := (ex_16_1d h hCE hk0 hk hkf hint hkint hdU hdf t).1
    linarith
  refine ⟨rfl, hr, fun t => ?_⟩
  rw [← gc_discount_prod (gc_price_pos h hCE' ()), ← gc_discount_prod (gc_price_pos h hCE ())]
  simp only [hr]

end StokeyLucasPrescott.EquilibriumApplications
