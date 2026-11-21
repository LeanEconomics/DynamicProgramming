/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.SaddlePathExistence

/-!
# The saddle path exists for every `δ ≤ 1`: a shooting argument

AKMM, App. 4.A.4, p. 834: "for a given `k₀`, the social planner chooses `c₀`. Once `c₀` is
chosen, the conditions (4.A.8) and (4.A.9) determine `(k₁, c₁)` ... It turns out that the social
planner has to choose `c₀` so that `(k₀, c₀)` is on the saddle path." The book asserts that the
saddle path exists. It is proved here in the difference system itself, for every `k₀ > 0` and
every `δ ≤ 1`, with no appeal to the optimum.

The forward map: `k_{t+1} = f(k_t) + (1 − δ)k_t − c_t`, and `c_{t+1} = (u')⁻¹(u'(c_t)/(βR_{t+1}))`,
`R = f'(k) + 1 − δ` (`saddleFwd`; `ui` is an inverse of `u'` on `(0, ∞)`, which exists when `u'`
is continuous, strictly decreasing and maps `(0, ∞)` onto `(0, ∞)`).

* The region where `k` falls to below `k̄` is left in finite time through `k ≤ 0`
  (`saddle_regionA_infeasible`); a positive path that never enters it nor the quadrant
  `k > k̄`, `c < c̄` converges to `(k̄, c̄)` (`saddle_trapped_converges`).
* The quadrant `k > k̄`, `c < c̄` is absorbing, so a forward path entering it is feasible forever
  (`saddle_fwd_quadrant`); a forward path is infeasible iff it enters the first region, through
  finitely many strict inequalities (`saddle_fwd_infeasible_iff`); infeasibility is inherited
  by higher `c₀` (`saddle_fwd_order`); each iterate is continuous in `c₀` (`saddle_fwd_cont`);
  small `c₀` are feasible (`saddle_fwd_small`).
* Shooting: `c* = inf{c₀ : infeasible}` is feasible, and its path enters neither region, so it
  converges (`saddle_fwd_exists`). With `saddle_path_iff` this gives the saddle path `g` with
  "convergence iff `c₀ = g(k₀)`" for every `k₀ > 0` (`saddle_path_general`); for log utility and
  Cobb–Douglas with `δ = 1`, `g(k) = (1 − αβ)Ak^α` (`saddle_path_general_logCobbDouglas`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real StokeyLucasPrescott.DeterministicDynamics

/-- The forward map of (4.A.8)–(4.A.9), AKMM, p. 834: from `(k₀, c₀)`, `k_{t+1} = f(k_t) +
(1 − δ)k_t − c_t` and `c_{t+1} = ui(u'(c_t)/(β(f'(k_{t+1}) + 1 − δ)))`, `ui` an inverse of `u'`. -/
noncomputable def saddleFwd (f f' u' ui : ℝ → ℝ) (β δ k0 c0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (k0, c0)
  | t + 1 =>
    ((f (saddleFwd f f' u' ui β δ k0 c0 t).1 + (1 - δ) * (saddleFwd f f' u' ui β δ k0 c0 t).1 -
        (saddleFwd f f' u' ui β δ k0 c0 t).2),
      ui (u' (saddleFwd f f' u' ui β δ k0 c0 t).2 /
        (β * (f' (f (saddleFwd f f' u' ui β δ k0 c0 t).1 +
          (1 - δ) * (saddleFwd f f' u' ui β δ k0 c0 t).1 -
            (saddleFwd f f' u' ui β δ k0 c0 t).2) + 1 - δ))))

/-- **AKMM, p. 834: the region where capital falls below `k̄` is left through `k ≤ 0`.** A path of
(4.A.8)–(4.A.9) with `k_t, c_t > 0` for all `t` never has `k_{T+1} < k_T` and `k_{T+1} < k̄`:
there `k` keeps falling and `c` rising (`saddle_regionA_absorbing`), so `u'(c_t)` falls
geometrically while `c_t < f(k_T) + (1 − δ)k_T` keeps it bounded below. -/
theorem saddle_regionA_infeasible {f f' u' : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hf' : StrictAntiOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0)) (hkbar : 0 < kbar)
    (h411 : 1 = β * (f' kbar + 1 - δ)) {k c : ℕ → ℝ} (hs : saddleSystem f f' u' β δ k c)
    (hk : ∀ t, 0 < k t) (hc : ∀ t, 0 < c t) {T : ℕ} (hfall : k (T + 1) < k T)
    (hlow : k (T + 1) < kbar) : False := by
  have habs : ∀ n, k (T + n + 1) < k (T + n) ∧ k (T + n + 1) < kbar := by
    intro n
    induction n with
    | zero => exact ⟨hfall, hlow⟩
    | succ n ih =>
      have := saddle_regionA_absorbing hβ hδ1 hf hfd hf'pos hf' hu'pos hu' hkbar h411 hs
        (t := T + n) (hk _) (hc _) (hc _) ih.1.le ih.2
      rw [show T + (n + 1) + 1 = T + n + 2 by omega, show T + (n + 1) = T + n + 1 by omega]
      exact ⟨this.2.1, this.2.2⟩
  have hdecT : ∀ n, k (T + n) ≤ k T := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (habs n).1.le.trans ih
  have hdec1 : ∀ n, k (T + n + 1) ≤ k (T + 1) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      have := (habs (n + 1)).1
      rw [show T + (n + 1) = T + n + 1 by omega] at this
      rw [show T + (n + 1) + 1 = T + n + 1 + 1 by omega]
      exact this.le.trans ih
  set r := f' (k (T + 1)) + 1 - δ with hrdef
  have hβr : 1 < β * r := by
    have h1 : f' kbar < f' (k (T + 1)) := hf' (Set.mem_Ioi.2 (hk _)) (Set.mem_Ioi.2 hkbar) hlow
    have := mul_lt_mul_of_pos_left h1 hβ
    rw [hrdef]; linarith
  have hstep : ∀ n, β * r * u' (c (T + n + 1)) ≤ u' (c (T + n)) := by
    intro n
    have he := (hs (T + n)).2
    have hR : r ≤ f' (k (T + n + 1)) + 1 - δ := by
      have := hf'.antitoneOn (Set.mem_Ioi.2 (hk _)) (Set.mem_Ioi.2 (hk _)) (hdec1 n)
      rw [hrdef]; linarith
    rw [he]
    have := mul_le_mul_of_nonneg_left hR (mul_pos hβ (hu'pos _ (hc (T + n + 1)))).le
    linarith
  have hgeo : ∀ n, (β * r) ^ n * u' (c (T + n)) ≤ u' (c T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := mul_le_mul_of_nonneg_left (hstep n) (pow_pos (by linarith : 0 < β * r) n).le
      rw [show T + (n + 1) = T + n + 1 by omega, pow_succ]
      calc (β * r) ^ n * (β * r) * u' (c (T + n + 1))
          = (β * r) ^ n * (β * r * u' (c (T + n + 1))) := by ring
        _ ≤ (β * r) ^ n * u' (c (T + n)) := this
        _ ≤ _ := ih
  set FT := f (k T) + (1 - δ) * k T with hFT
  have hFT0 : c T < FT := by have := (hs T).1; have := hk (T + 1); rw [hFT]; linarith
  have hlb : ∀ n, u' FT ≤ u' (c (T + n)) := by
    intro n
    have h1 := (hs (T + n)).1
    have h2 := hk (T + n + 1)
    have h3 := saddle_resources_mono hδ1 hf hfd hf'pos (hk _).le (hdecT n) (hk T)
    exact hu'.antitoneOn (Set.mem_Ioi.2 (hc _)) (Set.mem_Ioi.2 ((hc T).trans hFT0))
      (by rw [hFT]; linarith)
  have huFT := hu'pos _ ((hc T).trans hFT0)
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hβr).eventually_gt_atTop
    (u' (c T) / u' FT)).exists
  rw [div_lt_iff₀ huFT] at hn
  have := mul_le_mul_of_nonneg_left (hlb n) (pow_pos (by linarith : 0 < β * r) n).le
  linarith [hgeo n]

/-- **AKMM, p. 834: a trapped path converges.** Let `f(0) = 0`, `f` concave with derivative
`f' > 0` strictly decreasing and continuous on `(0, ∞)`, `δ ≤ 1`, `u' > 0` strictly decreasing
and continuous on `(0, ∞)`, `0 < β < 1`, (4.A.11). A path of (4.A.8)–(4.A.9) with `k, c > 0`
that never has `k_{t+1} < k_t` with `k_{t+1} < k̄`, and never `k_t > k̄` with `c_t < c̄`
(`c̄ = f(k̄) − δk̄`), converges to `(k̄, c̄)`: capital moves monotonically towards `k̄` and the
only limit compatible with the Euler equation is `k̄`. -/
theorem saddle_trapped_converges {f f' u' : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hf'pos : ∀ x, 0 < x → 0 < f' x)
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hf'c : ContinuousOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hu'c : ContinuousOn u' (Set.Ioi 0)) (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ))
    {k c : ℕ → ℝ} (hs : saddleSystem f f' u' β δ k c) (hk : ∀ t, 0 < k t) (hc : ∀ t, 0 < c t)
    (hnA : ∀ t, ¬ (k (t + 1) < k t ∧ k (t + 1) < kbar))
    (hnB : ∀ t, ¬ (kbar < k t ∧ c t < f kbar - δ * kbar)) :
    Tendsto k atTop (𝓝 kbar) ∧ Tendsto c atTop (𝓝 (f kbar - δ * kbar)) := by
  have hRbar : f' kbar + 1 - δ = 1 / β := by field_simp; linarith
  have h1β : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith
  have hφpos : ∀ x, 0 < x → x ≤ kbar → 0 < f x - δ * x := by
    intro x hx hxk
    have h1 := tangent_le hf (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 le_rfl) (hfd x hx)
    rw [hf0] at h1
    have h2 : f' kbar ≤ f' x := hf'.antitoneOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hkbar) hxk
    have h3 : δ < f' x := by linarith
    nlinarith [mul_pos hx (sub_pos.2 h3)]
  have hcbar : 0 < f kbar - δ * kbar := hφpos kbar hkbar le_rfl
  have hcfall : ∀ t, kbar < k (t + 1) → c (t + 1) < c t := fun t h =>
    ((saddle_arrows hβ hu'pos hu' hf' hkbar h411 (hk _) (hc t) (hc _) (hs t).1
      (hs t).2).2.2.2.2).2 h
  -- (a) capital never rises above `k̄`
  have hnB1 : ∀ t, ¬ (k t < k (t + 1) ∧ kbar < k (t + 1)) := by
    rintro T ⟨h1, h2⟩
    have habs : ∀ n, k (T + n) < k (T + n + 1) ∧ kbar < k (T + n + 1) := by
      intro n
      induction n with
      | zero => exact ⟨h1, h2⟩
      | succ n ih =>
        have hcf := hcfall (T + n) ih.2
        have hm := saddle_resources_mono hδ1 hf hfd hf'pos (hk _).le ih.1.le (hk (T + n + 1))
        have e1 := (hs (T + n)).1
        have e2 := (hs (T + n + 1)).1
        rw [show T + (n + 1) = T + n + 1 by omega]
        exact ⟨by linarith, by linarith⟩
    have hge : ∀ n, k (T + 1) ≤ k (T + 1 + n) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        have := (habs (n + 1)).1
        rw [show T + (n + 1) = T + 1 + n by omega] at this
        rw [show T + 1 + (n + 1) = T + 1 + n + 1 by omega]
        linarith [(habs (n + 1)).1]
    have hcge : ∀ n, f kbar - δ * kbar ≤ c (T + 1 + n) := by
      intro n
      have := hnB (T + 1 + n)
      push Not at this
      exact this (by linarith [hge n])
    set r := f' (k (T + 1)) + 1 - δ with hrdef
    have hr0 : 0 < r := by rw [hrdef]; linarith [hf'pos _ (hk (T + 1))]
    have hβr : β * r < 1 := by
      have h3 : f' (k (T + 1)) < f' kbar := hf' (Set.mem_Ioi.2 hkbar) (Set.mem_Ioi.2 (hk _)) h2
      have := mul_lt_mul_of_pos_left h3 hβ
      rw [hrdef]; linarith
    have hβr0 : 0 < β * r := mul_pos hβ hr0
    have hgeo : ∀ n, u' (c (T + 1)) ≤ (β * r) ^ n * u' (c (T + 1 + n)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have he := (hs (T + 1 + n)).2
        have hR : f' (k (T + 1 + n + 1)) + 1 - δ ≤ r := by
          have := hf'.antitoneOn (Set.mem_Ioi.2 (hk _)) (Set.mem_Ioi.2 (hk _))
            (show k (T + 1) ≤ k (T + 1 + n + 1) by
              have := hge (n + 1); rwa [show T + 1 + (n + 1) = T + 1 + n + 1 by omega] at this)
          rw [hrdef]; linarith
        have h1 : u' (c (T + 1 + n)) ≤ β * r * u' (c (T + 1 + n + 1)) := by
          rw [he]
          have := mul_le_mul_of_nonneg_left hR (mul_pos hβ (hu'pos _ (hc (T + 1 + n + 1)))).le
          linarith
        rw [show T + 1 + (n + 1) = T + 1 + n + 1 by omega, pow_succ]
        calc u' (c (T + 1)) ≤ (β * r) ^ n * u' (c (T + 1 + n)) := ih
          _ ≤ (β * r) ^ n * (β * r * u' (c (T + 1 + n + 1))) :=
            mul_le_mul_of_nonneg_left h1 (pow_pos hβr0 n).le
          _ = _ := by ring
    have hu1 := hu'pos _ (hc (T + 1))
    have hucb := hu'pos _ hcbar
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβr0.le hβr).eventually
      (gt_mem_nhds (div_pos hu1 hucb))).exists
    have h4 : u' (c (T + 1 + n)) ≤ u' (f kbar - δ * kbar) :=
      hu'.antitoneOn (Set.mem_Ioi.2 hcbar) (Set.mem_Ioi.2 (hc _)) (hcge n)
    rw [lt_div_iff₀ hucb] at hn
    have := mul_le_mul_of_nonneg_left h4 (pow_pos hβr0 n).le
    linarith [hgeo n]
  -- (b) `k_{t+1}` lies between `k_t` and `k̄`
  have hbtw : ∀ t, (k t ≤ k (t + 1) ∧ k (t + 1) ≤ kbar) ∨ (kbar ≤ k (t + 1) ∧ k (t + 1) ≤ k t) := by
    intro t
    have a := hnA t
    have b := hnB1 t
    push Not at a b
    rcases le_or_gt (k (t + 1)) kbar with h | h
    · rcases le_or_gt (k t) (k (t + 1)) with h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact Or.inr ⟨a h', h'.le⟩
    · refine Or.inr ⟨h.le, ?_⟩
      by_contra h'
      push Not at h'
      linarith [b h']
  -- the limit of capital is `k̄`
  have hclim : ∀ L, 0 < L → Tendsto k atTop (𝓝 L) →
      Tendsto c atTop (𝓝 (f L + (1 - δ) * L - L)) := by
    intro L hL hkL
    have h1 := (((hfd L hL).continuousAt.tendsto.comp hkL).add (hkL.const_mul (1 - δ))).sub
      (hkL.comp (tendsto_add_atTop_nat 1))
    refine h1.congr fun t => ?_
    simp only [Function.comp_apply]
    linarith [(hs t).1]
  have hfinish : ∀ L, 0 < L → Tendsto k atTop (𝓝 L) → 0 < f L + (1 - δ) * L - L → L = kbar := by
    intro L hL hkL hcpos
    have hcL := hclim L hL hkL
    have hu1 : Tendsto (fun t => u' (c t)) atTop (𝓝 (u' (f L + (1 - δ) * L - L))) :=
      (hu'c.continuousAt (Ioi_mem_nhds hcpos)).tendsto.comp hcL
    have hu2 : Tendsto (fun t => β * u' (c (t + 1)) * (f' (k (t + 1)) + 1 - δ)) atTop
        (𝓝 (β * u' (f L + (1 - δ) * L - L) * (f' L + 1 - δ))) :=
      ((hu1.comp (tendsto_add_atTop_nat 1)).const_mul β).mul
        ((((hf'c.continuousAt (Ioi_mem_nhds hL)).tendsto.comp
          (hkL.comp (tendsto_add_atTop_nat 1))).add_const 1).sub_const δ)
    have heq := tendsto_nhds_unique hu1 (hu2.congr fun t => ((hs t).2).symm)
    have h1 := eq_4_16_of_euler (hu'pos _ hcpos).ne' heq
    have h2 : f' L = f' kbar := by
      have : β * (f' L - f' kbar) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    exact hf'.injOn (Set.mem_Ioi.2 hL) (Set.mem_Ioi.2 hkbar) h2
  have hkconv : Tendsto k atTop (𝓝 kbar) := by
    rcases le_or_gt (k 0) kbar with h0 | h0
    · have hle : ∀ t, k t ≤ kbar := by
        intro t
        induction t with
        | zero => exact h0
        | succ t ih =>
          rcases hbtw t with h | h
          · exact h.2
          · linarith [h.2]
      have hm : Monotone k := monotone_nat_of_le_succ fun t => by
        rcases hbtw t with h | h
        · exact h.1
        · linarith [hle t, h.1]
      have hbdd : BddAbove (Set.range k) := ⟨kbar, by rintro _ ⟨t, rfl⟩; exact hle t⟩
      have hx := tendsto_atTop_ciSup hm hbdd
      have hL0 : 0 < ⨆ t, k t := (hk 0).trans_le (le_ciSup hbdd 0)
      have hLk : (⨆ t, k t) ≤ kbar := ciSup_le hle
      have hpos : 0 < f (⨆ t, k t) + (1 - δ) * (⨆ t, k t) - (⨆ t, k t) := by
        have := hφpos _ hL0 hLk; linarith
      rw [← hfinish _ hL0 hx hpos]
      exact hx
    · have hge : ∀ t, kbar ≤ k t := by
        intro t
        induction t with
        | zero => exact h0.le
        | succ t ih =>
          rcases hbtw t with h | h
          · linarith [h.1]
          · exact h.1
      have ha : Antitone k := antitone_nat_of_succ_le fun t => by
        rcases hbtw t with h | h
        · linarith [hge t, h.2, h.1, hge (t + 1)]
        · exact h.2
      have hbdd : BddBelow (Set.range k) := ⟨kbar, by rintro _ ⟨t, rfl⟩; exact hge t⟩
      have hx := tendsto_atTop_ciInf ha hbdd
      have hLk : kbar ≤ ⨅ t, k t := le_ciInf hge
      have hL0 : 0 < ⨅ t, k t := hkbar.trans_le hLk
      by_cases hall : ∀ t, kbar < k t
      · have hcge : ∀ t, f kbar - δ * kbar ≤ c t := fun t => by
          have := hnB t
          push Not at this
          exact this (hall t)
        have hcL := hclim _ hL0 hx
        have hpos : 0 < f (⨅ t, k t) + (1 - δ) * (⨅ t, k t) - (⨅ t, k t) :=
          hcbar.trans_le (ge_of_tendsto' hcL hcge)
        rw [← hfinish _ hL0 hx hpos]
        exact hx
      · push Not at hall
        obtain ⟨t0, ht0⟩ := hall
        have hconst : ∀ n, k (t0 + n) = kbar := by
          intro n
          induction n with
          | zero => exact le_antisymm ht0 (hge t0)
          | succ n ih =>
            have := ha (Nat.le_succ (t0 + n))
            rw [← Nat.add_succ] at this
            exact le_antisymm (this.trans ih.le) (hge _)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop t0] with t ht
        obtain ⟨n, rfl⟩ : ∃ n, t = t0 + n := ⟨t - t0, by omega⟩
        exact (hconst n).symm
  refine ⟨hkconv, ?_⟩
  have := hclim kbar hkbar hkconv
  rwa [show f kbar + (1 - δ) * kbar - kbar = f kbar - δ * kbar by ring] at this

/-- AKMM, p. 834: the forward map of (4.A.8)–(4.A.9). If `ui` inverts `u'` on `(0, ∞)`, a forward
path from `c₀ > 0` has `c_t > 0` while `k_1, …, k_t > 0`, and satisfies the Euler equation (4.A.9)
at every date with `k_{t+1}, c_t > 0`. -/
theorem saddle_fwd_path {f' u' ui : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y) {k c : ℕ → ℝ}
    (hrc : ∀ t, c (t + 1) = ui (u' (c t) / (β * (f' (k (t + 1)) + 1 - δ)))) (hc0 : 0 < c 0) :
    (∀ t, (∀ s, s ≤ t → 0 < k s) → 0 < c t) ∧
      (∀ t, 0 < k (t + 1) → 0 < c t →
        u' (c t) = β * u' (c (t + 1)) * (f' (k (t + 1)) + 1 - δ)) := by
  have hRpos : ∀ t, 0 < k (t + 1) → 0 < β * (f' (k (t + 1)) + 1 - δ) := fun t hk =>
    mul_pos hβ (by linarith [hf'pos _ hk])
  have harg : ∀ t, 0 < k (t + 1) → 0 < c t →
      0 < u' (c t) / (β * (f' (k (t + 1)) + 1 - δ)) :=
    fun t hk hc => div_pos (hu'pos _ hc) (hRpos t hk)
  refine ⟨fun t => ?_, fun t hk hc => ?_⟩
  · induction t with
    | zero => exact fun _ => hc0
    | succ t ih =>
      intro hks
      have hct := ih (fun s hs => hks s (by omega))
      rw [hrc]
      exact (hui _ (harg t (hks _ le_rfl) hct)).1
  · have h := (hui _ (harg t hk hc)).2
    have hR1 : 0 < f' (k (t + 1)) + 1 - δ := by linarith [hf'pos _ hk]
    rw [hrc t, h]
    field_simp

/-- AKMM, p. 834: a forward path from `k₀, c₀ > 0` is infeasible (some `k_t ≤ 0`) iff, while
capital is still positive, it reaches `k_{T+1} < k_T` with `k_{T+1} < k̄`
(`saddle_regionA_infeasible`, and the first exit). -/
theorem saddle_fwd_infeasible_iff {f f' u' ui : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β)
    (hδ1 : δ ≤ 1) (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hf' : StrictAntiOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y) (hkbar : 0 < kbar)
    (h411 : 1 = β * (f' kbar + 1 - δ)) {k c : ℕ → ℝ}
    (hrk : ∀ t, k (t + 1) = f (k t) + (1 - δ) * k t - c t)
    (hrc : ∀ t, c (t + 1) = ui (u' (c t) / (β * (f' (k (t + 1)) + 1 - δ)))) (hk0 : 0 < k 0)
    (hc0 : 0 < c 0) :
    (∃ T, (∀ s, s ≤ T → 0 < k s) ∧ k (T + 1) < k T ∧ k (T + 1) < kbar) ↔ ∃ t, k t ≤ 0 := by
  obtain ⟨hcpos, heul⟩ := saddle_fwd_path hβ hδ1 hf'pos hu'pos hui hrc hc0
  constructor
  · rintro ⟨T, -, h1, h2⟩
    by_contra hall
    push Not at hall
    have hc : ∀ t, 0 < c t := fun t => hcpos t fun s _ => hall s
    exact saddle_regionA_infeasible hβ hδ1 hf hfd hf'pos hf' hu'pos hu' hkbar h411
      (fun t => ⟨hrk t, heul t (hall _) (hc t)⟩) hall hc h1 h2
  · intro hex
    classical
    have hn0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h] at this
      linarith
    have hpos : ∀ s, s < Nat.find hex → 0 < k s := fun s hs => by
      have := Nat.find_min hex hs
      push Not at this
      exact this
    have hlast := Nat.find_spec hex
    refine ⟨Nat.find hex - 1, fun s hs => hpos s (by omega), ?_, ?_⟩
    · rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
      linarith [hpos (Nat.find hex - 1) (by omega)]
    · rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
      linarith

/-- **AKMM, Figure .3, p. 834: the quadrant `k > k̄`, `c < c̄` is absorbing.** There
`k_{t+1} = f(k_t) + (1 − δ)k_t − c_t > f(k̄) + (1 − δ)k̄ − c̄ = k̄` and `c` falls, so a forward
path that enters it while capital is positive keeps `k_t > k̄` and is feasible forever. -/
theorem saddle_fwd_quadrant {f f' u' ui : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hf' : StrictAntiOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y) (hkbar : 0 < kbar)
    (h411 : 1 = β * (f' kbar + 1 - δ)) {k c : ℕ → ℝ}
    (hrk : ∀ t, k (t + 1) = f (k t) + (1 - δ) * k t - c t)
    (hrc : ∀ t, c (t + 1) = ui (u' (c t) / (β * (f' (k (t + 1)) + 1 - δ)))) (hc0 : 0 < c 0)
    {T : ℕ} (hpos : ∀ s, s ≤ T → 0 < k s) (hkT : kbar < k T)
    (hcT : c T < f kbar - δ * kbar) : ∀ t, 0 < k t := by
  obtain ⟨hcpos, heul⟩ := saddle_fwd_path hβ hδ1 hf'pos hu'pos hui hrc hc0
  have hq : ∀ n, kbar < k (T + n) ∧ c (T + n) < f kbar - δ * kbar ∧ 0 < c (T + n) := by
    intro n
    induction n with
    | zero => exact ⟨hkT, hcT, hcpos T hpos⟩
    | succ n ih =>
      have hk : 0 < k (T + n) := hkbar.trans ih.1
      have h1 := tangent_le hf (Set.mem_Ici.2 hk.le) (Set.mem_Ici.2 hkbar.le) (hfd _ hk)
      have hgap : 0 < (f' (k (T + n)) + 1 - δ) * (k (T + n) - kbar) :=
        mul_pos (by linarith [hf'pos _ hk]) (by linarith [ih.1])
      have hk1 : kbar < k (T + n + 1) := by rw [hrk]; nlinarith [ih.2.1]
      have hk1' : 0 < k (T + n + 1) := hkbar.trans hk1
      have harg : 0 < u' (c (T + n)) / (β * (f' (k (T + n + 1)) + 1 - δ)) :=
        div_pos (hu'pos _ ih.2.2) (mul_pos hβ (by linarith [hf'pos _ hk1']))
      have hc1 : 0 < c (T + n + 1) := by rw [hrc]; exact (hui _ harg).1
      have hfall := ((saddle_arrows hβ hu'pos hu' hf' hkbar h411 hk1' ih.2.2 hc1 (hrk _)
        (heul _ hk1' ih.2.2)).2.2.2.2).2 hk1
      rw [show T + (n + 1) = T + n + 1 by omega]
      exact ⟨hk1, by linarith [ih.2.1], hc1⟩
  intro t
  rcases le_or_gt t T with h | h
  · exact hpos t h
  · obtain ⟨n, rfl⟩ : ∃ n, t = T + n := ⟨t - T, by omega⟩
    exact hkbar.trans (hq n).1

/-- **AKMM, p. 834: feasibility is inherited by lower `c₀`** (`saddle_order` for the forward
map). Two forward paths from the same `k₀` with `0 < c₀ < c₀'`: if the path from `c₀'` keeps
`k > 0`, so does the path from `c₀`. -/
theorem saddle_fwd_order {f f' u' ui : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    (hu' : StrictAntiOn u' (Set.Ioi 0)) (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y)
    {k c k' c' : ℕ → ℝ} (hrk : ∀ t, k (t + 1) = f (k t) + (1 - δ) * k t - c t)
    (hrc : ∀ t, c (t + 1) = ui (u' (c t) / (β * (f' (k (t + 1)) + 1 - δ))))
    (hrk' : ∀ t, k' (t + 1) = f (k' t) + (1 - δ) * k' t - c' t)
    (hrc' : ∀ t, c' (t + 1) = ui (u' (c' t) / (β * (f' (k' (t + 1)) + 1 - δ))))
    (h0 : k 0 = k' 0) (hc0 : 0 < c 0) (hcc : c 0 < c' 0) (hk' : ∀ t, 0 < k' t) :
    ∀ t, 0 < k t := by
  obtain ⟨hcpos, heul⟩ := saddle_fwd_path hβ hδ1 hf'pos hu'pos hui hrc hc0
  obtain ⟨hcpos', heul'⟩ := saddle_fwd_path hβ hδ1 hf'pos hu'pos hui hrc' (hc0.trans hcc)
  have hc' : ∀ t, 0 < c' t := fun t => hcpos' t fun s _ => hk' s
  have key : ∀ t, k' t ≤ k t ∧ c t < c' t ∧ 0 < c t := by
    intro t
    induction t with
    | zero => exact ⟨h0.symm.le, hcc, hc0⟩
    | succ t ih =>
      have hkt : 0 < k t := (hk' t).trans_le ih.1
      have hm := saddle_resources_mono hδ1 hf hfd hf'pos (hk' t).le ih.1 hkt
      have hk1 : k' (t + 1) < k (t + 1) := by rw [hrk, hrk']; linarith [ih.2.1]
      have hk1' : 0 < k (t + 1) := (hk' _).trans hk1
      have harg : 0 < u' (c t) / (β * (f' (k (t + 1)) + 1 - δ)) :=
        div_pos (hu'pos _ ih.2.2) (mul_pos hβ (by linarith [hf'pos _ hk1']))
      have hc1 : 0 < c (t + 1) := by rw [hrc]; exact (hui _ harg).1
      refine ⟨hk1.le, ?_, hc1⟩
      by_contra hle
      push Not at hle
      have hu1 : u' (c (t + 1)) ≤ u' (c' (t + 1)) :=
        hu'.antitoneOn (Set.mem_Ioi.2 (hc' _)) (Set.mem_Ioi.2 hc1) hle
      have hu0 : u' (c' t) < u' (c t) := hu' (Set.mem_Ioi.2 ih.2.2) (Set.mem_Ioi.2 (hc' t)) ih.2.1
      have hR : f' (k (t + 1)) ≤ f' (k' (t + 1)) :=
        deriv_le_of_concave hf (Set.mem_Ici.2 (hk' _).le) (Set.mem_Ici.2 hk1'.le) hk1.le
          (hfd _ (hk' _)) (hfd _ hk1')
      have e1 : β * u' (c (t + 1)) * (f' (k (t + 1)) + 1 - δ) ≤
          β * u' (c' (t + 1)) * (f' (k (t + 1)) + 1 - δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu1 hβ.le)
          (by linarith [hf'pos _ hk1'])
      have e2 : β * u' (c' (t + 1)) * (f' (k (t + 1)) + 1 - δ) ≤
          β * u' (c' (t + 1)) * (f' (k' (t + 1)) + 1 - δ) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_pos hβ (hu'pos _ (hc' _))).le
      linarith [heul t hk1' ih.2.2, heul' t (hk' _) (hc' t)]
  exact fun t => (hk' t).trans_le (key t).1

/-- AKMM, p. 834: each iterate of the forward map is continuous in `c₀` at a point `c₀ > 0`
whose path has `k_0, …, k_T > 0` (with `f'`, `u'`, `ui` continuous on `(0, ∞)`): `k_s`, `c_s`
for `s ≤ T` and `k_{T+1}`. -/
theorem saddle_fwd_cont {f f' u' ui : ℝ → ℝ} {β δ k0 : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hf'pos : ∀ x, 0 < x → 0 < f' x)
    (hf'c : ContinuousOn f' (Set.Ioi 0)) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    (hu'c : ContinuousOn u' (Set.Ioi 0)) (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y)
    (huic : ContinuousOn ui (Set.Ioi 0)) {K C : ℝ → ℕ → ℝ} (hK0 : ∀ x, K x 0 = k0)
    (hC0 : ∀ x, C x 0 = x) (hKs : ∀ x t, K x (t + 1) = f (K x t) + (1 - δ) * K x t - C x t)
    (hCs : ∀ x t, C x (t + 1) = ui (u' (C x t) / (β * (f' (K x (t + 1)) + 1 - δ))))
    {x0 : ℝ} (hx0 : 0 < x0) {T : ℕ} (hpos : ∀ s, s ≤ T → 0 < K x0 s) :
    ∀ s, s ≤ T → ContinuousAt (fun x => K x s) x0 ∧ ContinuousAt (fun x => C x s) x0 ∧
      ContinuousAt (fun x => K x (s + 1)) x0 := by
  have hcpos := (saddle_fwd_path hβ hδ1 hf'pos hu'pos hui (hCs x0) ((hC0 x0).symm ▸ hx0)).1
  have hKstep : ∀ s, 0 < K x0 s → ContinuousAt (fun x => K x s) x0 →
      ContinuousAt (fun x => C x s) x0 → ContinuousAt (fun x => K x (s + 1)) x0 := by
    intro s hk hK hC
    have e : (fun x => K x (s + 1)) = fun x => f (K x s) + (1 - δ) * K x s - C x s :=
      funext fun x => hKs x s
    rw [e]
    exact (((hfd _ hk).continuousAt.comp (f := fun x => K x s) hK).add (hK.const_mul _)).sub hC
  intro s
  induction s with
  | zero =>
    intro _
    have hK : ContinuousAt (fun x => K x 0) x0 := by
      rw [show (fun x => K x 0) = fun _ => k0 from funext hK0]; exact continuousAt_const
    have hC : ContinuousAt (fun x => C x 0) x0 := by
      rw [show (fun x => C x 0) = fun x => x from funext hC0]; exact continuousAt_id
    exact ⟨hK, hC, hKstep 0 (hpos 0 (Nat.zero_le _)) hK hC⟩
  | succ s ih =>
    intro hs
    obtain ⟨-, hC, hK1⟩ := ih (by omega)
    have hk1 := hpos (s + 1) hs
    have hc := hcpos s fun r hr => hpos r (by omega)
    have hR : 0 < β * (f' (K x0 (s + 1)) + 1 - δ) := mul_pos hβ (by linarith [hf'pos _ hk1])
    have harg := div_pos (hu'pos _ hc) hR
    have hargc : ContinuousAt (fun x => u' (C x s) / (β * (f' (K x (s + 1)) + 1 - δ))) x0 :=
      ((hu'c.continuousAt (Ioi_mem_nhds hc)).comp (f := fun x => C x s) hC).div
        (continuousAt_const.mul ((((hf'c.continuousAt (Ioi_mem_nhds hk1)).comp
          (f := fun x => K x (s + 1)) hK1).add
          continuousAt_const).sub continuousAt_const)) hR.ne'
    have hC1 : ContinuousAt (fun x => C x (s + 1)) x0 := by
      have e : (fun x => C x (s + 1)) =
          fun x => ui (u' (C x s) / (β * (f' (K x (s + 1)) + 1 - δ))) := funext fun x => hCs x s
      rw [e]
      exact (huic.continuousAt (Ioi_mem_nhds harg)).comp
        (f := fun x => u' (C x s) / (β * (f' (K x (s + 1)) + 1 - δ))) hargc
    exact ⟨hK1, hC1, hKstep (s + 1) hk1 hK1 hC1⟩

/-- AKMM, p. 834: small `c₀` are feasible. With `u'(c) → ∞` as `c → 0⁺`, as `c₀ → 0⁺` the
forward path tends, date by date, to pure accumulation `z_{t+1} = f(z_t) + (1 − δ)z_t` with
`u'(c_t) → ∞`; `z` exceeds `k̄` at some `N`, so for small `c₀` the path is in the absorbing
quadrant `k > k̄`, `c < c̄` at `N` (`saddle_fwd_quadrant`) and keeps `k > 0` forever. -/
theorem saddle_fwd_small {f f' u' ui : ℝ → ℝ} {β δ kbar k0 : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hf'pos : ∀ x, 0 < x → 0 < f' x)
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hf'c : ContinuousOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hinada : Tendsto u' (𝓝[>] 0) atTop) (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y)
    (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ)) (hk0 : 0 < k0)
    {K C : ℝ → ℕ → ℝ} (hK0 : ∀ x, K x 0 = k0) (hC0 : ∀ x, C x 0 = x)
    (hKs : ∀ x t, K x (t + 1) = f (K x t) + (1 - δ) * K x t - C x t)
    (hCs : ∀ x t, C x (t + 1) = ui (u' (C x t) / (β * (f' (K x (t + 1)) + 1 - δ)))) :
    ∃ x, 0 < x ∧ ∀ t, 0 < K x t := by
  have h1β : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith
  have hRbar : f' kbar + 1 - δ = 1 / β := by field_simp; linarith
  have hφpos : ∀ x, 0 < x → x ≤ kbar → 0 < f x - δ * x := by
    intro x hx hxk
    have h1 := tangent_le hf (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 le_rfl) (hfd x hx)
    rw [hf0] at h1
    have h2 : f' kbar ≤ f' x := hf'.antitoneOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hkbar) hxk
    have h3 : δ < f' x := by linarith
    nlinarith [mul_pos hx (sub_pos.2 h3)]
  have hFpos : ∀ y, 0 < y → 0 < f y + (1 - δ) * y := by
    intro y hy
    have h1 := tangent_le hf (Set.mem_Ici.2 hy.le) (Set.mem_Ici.2 le_rfl) (hfd y hy)
    rw [hf0] at h1
    nlinarith [mul_pos hy (hf'pos y hy), mul_nonneg (sub_nonneg.2 hδ1) hy.le]
  set z : ℕ → ℝ := fun t => (fun y => f y + (1 - δ) * y)^[t] k0 with hzdef
  have hz : ∀ t, z (t + 1) = f (z t) + (1 - δ) * z t := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hz0 : z 0 = k0 := rfl
  have hzpos : ∀ t, 0 < z t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hz]; exact hFpos _ ih
  obtain ⟨N, hN⟩ : ∃ N, kbar < z N := by
    by_contra h
    push Not at h
    have hm : Monotone z := monotone_nat_of_le_succ fun t => by
      rw [hz]; have := hφpos _ (hzpos t) (h t); linarith
    have hbdd : BddAbove (Set.range z) := ⟨kbar, by rintro _ ⟨t, rfl⟩; exact h t⟩
    have hx := tendsto_atTop_ciSup hm hbdd
    have hL0 : 0 < ⨆ t, z t := (hzpos 0).trans_le (le_ciSup hbdd 0)
    have hLk : (⨆ t, z t) ≤ kbar := ciSup_le h
    have h1 : Tendsto (fun t => z (t + 1)) atTop
        (𝓝 (f (⨆ t, z t) + (1 - δ) * (⨆ t, z t))) := by
      have := ((hfd _ hL0).continuousAt.tendsto.comp hx).add (hx.const_mul (1 - δ))
      exact this.congr fun t => (hz t).symm
    have h2 := tendsto_nhds_unique h1 (hx.comp (tendsto_add_atTop_nat 1))
    have := hφpos _ hL0 hLk
    linarith
  have hQ : ∀ t, Tendsto (fun x => K x t) (𝓝[>] 0) (𝓝 (z t)) ∧
      Tendsto (fun x => u' (C x t)) (𝓝[>] 0) atTop ∧
      ∀ᶠ x in 𝓝[>] (0 : ℝ), (∀ s, s ≤ t → 0 < K x s) ∧ 0 < C x t := by
    intro t
    induction t with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [show (fun x => K x 0) = fun _ => z 0 from funext fun x => (hK0 x).trans hz0.symm]
        exact tendsto_const_nhds
      · rw [show (fun x => u' (C x 0)) = u' from funext fun x => by rw [hC0]]
        exact hinada
      · filter_upwards [self_mem_nhdsWithin] with x hx
        refine ⟨fun s hs => ?_, by rw [hC0]; exact hx⟩
        rw [Nat.le_zero.1 hs, hK0]
        exact hk0
    | succ t ih =>
      obtain ⟨hKt, hut, hev⟩ := ih
      have hCt : Tendsto (fun x => C x t) (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_order.2 ⟨fun a ha => hev.mono fun x hx => ha.trans hx.2, fun b hb => ?_⟩
        filter_upwards [hut.eventually_gt_atTop (u' b), hev] with x h1 h2
        by_contra hge
        push Not at hge
        have := hu'.antitoneOn (Set.mem_Ioi.2 hb) (Set.mem_Ioi.2 h2.2) hge
        linarith
      have hKt1 : Tendsto (fun x => K x (t + 1)) (𝓝[>] 0) (𝓝 (z (t + 1))) := by
        have := (((hfd _ (hzpos t)).continuousAt.tendsto.comp hKt).add
          (hKt.const_mul (1 - δ))).sub hCt
        rw [sub_zero, ← hz t] at this
        exact this.congr fun x => (hKs x t).symm
      have hR0 : 0 < β * (f' (z (t + 1)) + 1 - δ) :=
        mul_pos hβ (by linarith [hf'pos _ (hzpos (t + 1))])
      have hR : Tendsto (fun x => β * (f' (K x (t + 1)) + 1 - δ)) (𝓝[>] 0)
          (𝓝 (β * (f' (z (t + 1)) + 1 - δ))) :=
        ((((hf'c.continuousAt (Ioi_mem_nhds (hzpos (t + 1)))).tendsto.comp hKt1).add_const
          1).sub_const δ).const_mul β
      have hev1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < K x (t + 1) :=
        hKt1.eventually (lt_mem_nhds (hzpos (t + 1)))
      have hu1 : Tendsto (fun x => u' (C x (t + 1))) (𝓝[>] 0) atTop := by
        have := hut.atTop_mul_pos (inv_pos.2 hR0) (hR.inv₀ hR0.ne')
        refine this.congr' ?_
        filter_upwards [hev, hev1] with x h1 h2
        have hRx : 0 < β * (f' (K x (t + 1)) + 1 - δ) := mul_pos hβ (by linarith [hf'pos _ h2])
        rw [hCs, (hui _ (div_pos (hu'pos _ h1.2) hRx)).2, div_eq_mul_inv]
      refine ⟨hKt1, hu1, ?_⟩
      filter_upwards [hev, hev1] with x h1 h2
      have hRx : 0 < β * (f' (K x (t + 1)) + 1 - δ) := mul_pos hβ (by linarith [hf'pos _ h2])
      refine ⟨fun s hs => ?_, by rw [hCs]; exact (hui _ (div_pos (hu'pos _ h1.2) hRx)).1⟩
      rcases Nat.lt_or_ge s (t + 1) with h | h
      · exact h1.1 s (by omega)
      · rw [show s = t + 1 by omega]; exact h2
  obtain ⟨hKN, huN, hevN⟩ := hQ N
  have hcbar : 0 < f kbar - δ * kbar := hφpos kbar hkbar le_rfl
  obtain ⟨x, hx0, hxK, hxu, hxev⟩ := ((eventually_mem_nhdsWithin.and
    ((hKN.eventually (lt_mem_nhds hN)).and ((huN.eventually_gt_atTop
      (u' (f kbar - δ * kbar))).and hevN)))).exists
  have hxC : C x N < f kbar - δ * kbar := by
    by_contra hge
    push Not at hge
    have := hu'.antitoneOn (Set.mem_Ioi.2 hcbar) (Set.mem_Ioi.2 hxev.2) hge
    linarith
  have hx0' : (0 : ℝ) < x := hx0
  exact ⟨x, hx0', saddle_fwd_quadrant hβ hδ1 hf hfd hf'pos hf' hu'pos hu' hui hkbar h411
    (hKs x) (hCs x) ((hC0 x).symm ▸ hx0') hxev.1 hxK hxC⟩

/-- **AKMM, p. 834: the shooting argument.** Under the hypotheses of `saddle_fwd_small` and
`saddle_trapped_converges`, with `ui` continuous on `(0, ∞)`, from every `k₀ > 0` some `c₀ > 0`
gives a forward path that stays positive and converges to `(k̄, c̄)`. It is
`c* = inf{c₀ > 0 : the path reaches k ≤ 0}`: that set is open (`saddle_fwd_cont`,
`saddle_fwd_infeasible_iff`), upward closed (`saddle_fwd_order`) and bounded below by a feasible
`c₀` (`saddle_fwd_small`), so `c*` is feasible; the quadrant `k > k̄`, `c < c̄` is open and
feasible (`saddle_fwd_quadrant`), so the path from `c*` never enters it; and a feasible path
that never enters the region `k_{t+1} < min(k_t, k̄)` nor that quadrant converges
(`saddle_trapped_converges`). -/
theorem saddle_fwd_exists {f f' u' ui : ℝ → ℝ} {β δ kbar k0 : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hf'pos : ∀ x, 0 < x → 0 < f' x)
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hf'c : ContinuousOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hu'c : ContinuousOn u' (Set.Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop)
    (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y) (huic : ContinuousOn ui (Set.Ioi 0))
    (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ)) (hk0 : 0 < k0)
    {K C : ℝ → ℕ → ℝ} (hK0 : ∀ x, K x 0 = k0) (hC0 : ∀ x, C x 0 = x)
    (hKs : ∀ x t, K x (t + 1) = f (K x t) + (1 - δ) * K x t - C x t)
    (hCs : ∀ x t, C x (t + 1) = ui (u' (C x t) / (β * (f' (K x (t + 1)) + 1 - δ)))) :
    ∃ x, 0 < x ∧ (∀ t, 0 < K x t) ∧ Tendsto (K x) atTop (𝓝 kbar) ∧
      Tendsto (C x) atTop (𝓝 (f kbar - δ * kbar)) := by
  have hc0 : ∀ x, 0 < x → 0 < C x 0 := fun x hx => (hC0 x).symm ▸ hx
  have hiff := fun x (hx : 0 < x) => saddle_fwd_infeasible_iff hβ hδ1 hf hfd hf'pos hf' hu'pos
    hu' hui hkbar h411 (hKs x) (hCs x) ((hK0 x).symm ▸ hk0) (hc0 x hx)
  set S := {x : ℝ | 0 < x ∧ ∃ t, K x t ≤ 0} with hSdef
  obtain ⟨xe, hxe0, hxe⟩ := saddle_fwd_small hβ hβ1 hδ1 hf0 hf hfd hf'pos hf' hf'c hu'pos hu'
    hinada hui hkbar h411 hk0 hK0 hC0 hKs hCs
  have hxeS : xe ∉ S := fun h => by obtain ⟨t, ht⟩ := h.2; linarith [hxe t]
  have hup : ∀ x ∈ S, ∀ y, x < y → y ∈ S := by
    intro x hx y hxy
    by_contra hy
    have hypos : ∀ t, 0 < K y t := by
      intro t
      by_contra h
      push Not at h
      exact hy ⟨hx.1.trans hxy, t, h⟩
    have := saddle_fwd_order hβ hδ1 hf hfd hf'pos hu'pos hu' hui (hKs x) (hCs x) (hKs y) (hCs y)
      ((hK0 x).trans (hK0 y).symm) (hc0 x hx.1) (by rw [hC0, hC0]; exact hxy) hypos
    obtain ⟨t, ht⟩ := hx.2
    linarith [this t]
  have hlow : ∀ x ∈ S, xe < x := by
    intro x hx
    by_contra h
    push Not at h
    rcases eq_or_lt_of_le h with h | h
    · exact hxeS (h ▸ hx)
    · exact hxeS (hup x hx xe h)
  have hFk0 : 0 < f k0 + (1 - δ) * k0 := by
    have h1 := tangent_le hf (Set.mem_Ici.2 hk0.le) (Set.mem_Ici.2 le_rfl) (hfd k0 hk0)
    rw [hf0] at h1
    nlinarith [mul_pos hk0 (hf'pos k0 hk0), mul_nonneg (sub_nonneg.2 hδ1) hk0.le]
  have hmem : f k0 + (1 - δ) * k0 ∈ S :=
    ⟨hFk0, 1, by rw [hKs, hK0, hC0]; linarith⟩
  have hne : S.Nonempty := ⟨_, hmem⟩
  have hbdd : BddBelow S := ⟨xe, fun x hx => (hlow x hx).le⟩
  have hcs : xe ≤ sInf S := le_csInf hne fun x hx => (hlow x hx).le
  have hcs0 : 0 < sInf S := hxe0.trans_le hcs
  have hopen : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, y ∈ S := by
    intro x hx
    obtain ⟨T, hTpos, h1, h2⟩ := (hiff x hx.1).2 hx.2
    have hcont := saddle_fwd_cont hβ hδ1 hfd hf'pos hf'c hu'pos hu'c hui huic hK0 hC0 hKs hCs
      hx.1 hTpos
    have hall : ∀ᶠ y in 𝓝 x, ∀ s ∈ {s : ℕ | s ≤ T}, 0 < K y s :=
      (Set.finite_le_nat T).eventually_all.2 fun s hs =>
        (hcont s hs).1.tendsto.eventually (lt_mem_nhds (hTpos s hs))
    have hlt1 : ∀ᶠ y in 𝓝 x, K y (T + 1) < K y T :=
      (hcont T le_rfl).2.2.tendsto.eventually_lt (hcont T le_rfl).1.tendsto h1
    have hlt2 : ∀ᶠ y in 𝓝 x, K y (T + 1) < kbar :=
      (hcont T le_rfl).2.2.tendsto.eventually (gt_mem_nhds h2)
    filter_upwards [hall, hlt1, hlt2, Ioi_mem_nhds hx.1] with y hy1 hy2 hy3 hy4
    exact ⟨hy4, (hiff y hy4).1 ⟨T, fun s hs => hy1 s hs, hy2, hy3⟩⟩
  have hcsS : sInf S ∉ S := by
    intro h
    obtain ⟨b, hb, hbS⟩ := (hopen _ h).exists_lt
    exact absurd (csInf_le hbdd hbS) (not_le.2 hb)
  have hcspos : ∀ t, 0 < K (sInf S) t := by
    intro t
    by_contra h
    push Not at h
    exact hcsS ⟨hcs0, t, h⟩
  obtain ⟨hcpos, heul⟩ := saddle_fwd_path hβ hδ1 hf'pos hu'pos hui (hCs (sInf S)) (hc0 _ hcs0)
  have hCpos : ∀ t, 0 < C (sInf S) t := fun t => hcpos t fun s _ => hcspos s
  have hsys : saddleSystem f f' u' β δ (K (sInf S)) (C (sInf S)) := fun t =>
    ⟨hKs _ t, heul t (hcspos _) (hCpos t)⟩
  have hnA : ∀ t, ¬ (K (sInf S) (t + 1) < K (sInf S) t ∧ K (sInf S) (t + 1) < kbar) :=
    fun t h => saddle_regionA_infeasible hβ hδ1 hf hfd hf'pos hf' hu'pos hu' hkbar h411 hsys
      hcspos hCpos h.1 h.2
  have hnB : ∀ t, ¬ (kbar < K (sInf S) t ∧ C (sInf S) t < f kbar - δ * kbar) := by
    rintro T ⟨h1, h2⟩
    have hcont := saddle_fwd_cont hβ hδ1 hfd hf'pos hf'c hu'pos hu'c hui huic hK0 hC0 hKs hCs
      hcs0 (T := T) fun s _ => hcspos s
    have hall : ∀ᶠ y in 𝓝 (sInf S), ∀ s ∈ {s : ℕ | s ≤ T}, 0 < K y s :=
      (Set.finite_le_nat T).eventually_all.2 fun s hs =>
        (hcont s hs).1.tendsto.eventually (lt_mem_nhds (hcspos s))
    have hk : ∀ᶠ y in 𝓝 (sInf S), kbar < K y T :=
      (hcont T le_rfl).1.tendsto.eventually (lt_mem_nhds h1)
    have hc : ∀ᶠ y in 𝓝 (sInf S), C y T < f kbar - δ * kbar :=
      (hcont T le_rfl).2.1.tendsto.eventually (gt_mem_nhds h2)
    obtain ⟨y, hy, hy1, hy2, hy3, hy4⟩ :=
      (hall.and (hk.and (hc.and (Ioi_mem_nhds hcs0)))).exists_gt
    have hyfeas := saddle_fwd_quadrant hβ hδ1 hf hfd hf'pos hf' hu'pos hu' hui hkbar h411
      (hKs y) (hCs y) (hc0 y hy4) (fun s hs => hy1 s hs) hy2 hy3
    obtain ⟨x, hxS, hxy⟩ := exists_lt_of_csInf_lt hne hy
    obtain ⟨t, ht⟩ := (hup x hxS y hxy).2
    linarith [hyfeas t]
  obtain ⟨hk, hc⟩ := saddle_trapped_converges hβ hβ1 hδ1 hf0 hf hfd hf'pos hf' hf'c hu'pos hu'
    hu'c hkbar h411 hsys hcspos hCpos hnA hnB
  exact ⟨sInf S, hcs0, hcspos, hk, hc⟩

/-- **AKMM, p. 834: the saddle path exists, and a path converges iff it starts on it.** Let
`0 < β < 1`, `δ ≤ 1`, `f(0) = 0`, `f` concave on `[0, ∞)` with derivative `f' > 0` strictly
decreasing and continuous on `(0, ∞)`, `u' > 0` strictly decreasing and continuous on `(0, ∞)`
with `u'(c) → ∞` as `c → 0⁺` and an inverse `ui` on `(0, ∞)` (continuous), and (4.A.11) at
`k̄ > 0`. Then there is `g` with `g(k₀) > 0` such that from every `k₀ > 0` a path starts at
`(k₀, g(k₀))` and converges to `(k̄, c̄)`, `c̄ = f(k̄) − δk̄`, and a path of (4.A.8)–(4.A.9) with
`k, c > 0` converges to `(k̄, c̄)` iff `c₀ = g(k₀)`. -/
theorem saddle_path_general {f f' u' ui : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hf'pos : ∀ x, 0 < x → 0 < f' x)
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hf'c : ContinuousOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hu'c : ContinuousOn u' (Set.Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop)
    (hui : ∀ y, 0 < y → 0 < ui y ∧ u' (ui y) = y) (huic : ContinuousOn ui (Set.Ioi 0))
    (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ)) :
    ∃ g : ℝ → ℝ, (∀ x, 0 < x → 0 < g x ∧ ∃ ks cs : ℕ → ℝ, saddleSystem f f' u' β δ ks cs ∧
      (∀ t, 0 < ks t) ∧ (∀ t, 0 < cs t) ∧ ks 0 = x ∧ cs 0 = g x ∧
      Tendsto ks atTop (𝓝 kbar) ∧ Tendsto cs atTop (𝓝 (f kbar - δ * kbar))) ∧
      ∀ k c : ℕ → ℝ, saddleSystem f f' u' β δ k c → (∀ t, 0 < k t) → (∀ t, 0 < c t) →
        ((Tendsto k atTop (𝓝 kbar) ∧ Tendsto c atTop (𝓝 (f kbar - δ * kbar))) ↔
          c 0 = g (k 0)) := by
  have hex : ∀ x, 0 < x → ∃ c0, 0 < c0 ∧ ∃ ks cs : ℕ → ℝ, saddleSystem f f' u' β δ ks cs ∧
      (∀ t, 0 < ks t) ∧ (∀ t, 0 < cs t) ∧ ks 0 = x ∧ cs 0 = c0 ∧
      Tendsto ks atTop (𝓝 kbar) ∧ Tendsto cs atTop (𝓝 (f kbar - δ * kbar)) := by
    intro x hx
    obtain ⟨c0, hc0, hpos, hk, hc⟩ := saddle_fwd_exists (k0 := x)
      (K := fun c t => (saddleFwd f f' u' ui β δ x c t).1)
      (C := fun c t => (saddleFwd f f' u' ui β δ x c t).2) hβ hβ1 hδ1 hf0 hf hfd hf'pos hf'
      hf'c hu'pos hu' hu'c hinada hui huic hkbar h411 hx (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)
    obtain ⟨hcpos, heul⟩ := saddle_fwd_path hβ hδ1 hf'pos hu'pos hui
      (k := fun t => (saddleFwd f f' u' ui β δ x c0 t).1)
      (c := fun t => (saddleFwd f f' u' ui β δ x c0 t).2) (fun _ => rfl) hc0
    exact ⟨c0, hc0, _, _, fun t => ⟨rfl, heul t (hpos _) (hcpos t fun s _ => hpos s)⟩, hpos,
      fun t => hcpos t fun s _ => hpos s, rfl, rfl, hk, hc⟩
  choose! g hg using hex
  refine ⟨g, fun x hx => (hg x hx), fun k c hs hk hc => ?_⟩
  exact saddle_path_iff (K := Set.Ioi 0) hβ hβ1 hδ1 hf hfd hf'pos hu'pos hu' h411
    (hf'c.continuousAt (Ioi_mem_nhds hkbar)) (fun x hx => (hg x hx).2) hs hk hc (hk 0)

/-- **AKMM, pp. 112 and 834: the check at `δ = 1`.** For log utility (`ui(y) = 1/y`), `f(k) = Ak^α`
and `δ = 1` all hypotheses of `saddle_path_general` hold, and the saddle path it produces is the
closed form `g(k) = (1 − αβ)Ak^α` (`saddle_logCobbDouglas`). -/
theorem saddle_path_general_logCobbDouglas {A α β : ℝ} (hA : 0 < A) (hα0 : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ g : ℝ → ℝ, (∀ x, 0 < x → g x = (1 - α * β) * A * x ^ α) ∧
      ∀ k c : ℕ → ℝ, saddleSystem (fun x => A * x ^ α) (fun x => α * A * x ^ (α - 1))
        (fun x => 1 / x) β 1 k c → (∀ t, 0 < k t) → (∀ t, 0 < c t) →
        ((Tendsto k atTop (𝓝 ((α * β * A) ^ (1 / (1 - α)))) ∧
          Tendsto c atTop (𝓝 (A * ((α * β * A) ^ (1 / (1 - α))) ^ α -
            1 * (α * β * A) ^ (1 / (1 - α))))) ↔ c 0 = g (k 0)) := by
  have hq : 0 < α * β * A := mul_pos (mul_pos hα0 hβ0) hA
  set kb := (α * β * A) ^ (1 / (1 - α)) with hkbdef
  have hkb : 0 < kb := rpow_pos_of_pos hq _
  have hsteady := example_4_5_steady hA hα0 hα1 hβ0
  have h411 : 1 = β * (α * A * kb ^ (α - 1) + 1 - 1) := by
    rw [add_sub_cancel_right]; exact hsteady.2
  have hf : ConcaveOn ℝ (Set.Ici 0) (fun x => A * x ^ α) :=
    (concaveOn_rpow hα0.le hα1.le).smul hA.le
  have hfd : ∀ x, 0 < x → HasDerivAt (fun x => A * x ^ α) (α * A * x ^ (α - 1)) x := by
    intro x hx
    have := (hasDerivAt_rpow_const (p := α) (Or.inl hx.ne')).const_mul A
    convert this using 1; ring
  have hf'pos : ∀ x, 0 < x → 0 < α * A * x ^ (α - 1) := fun x hx =>
    mul_pos (mul_pos hα0 hA) (rpow_pos_of_pos hx _)
  have hf' : StrictAntiOn (fun x => α * A * x ^ (α - 1)) (Set.Ioi 0) := by
    intro x hx y _ hxy
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow_of_neg hx hxy (by linarith)) (mul_pos hα0 hA)
  have hf'c : ContinuousOn (fun x => α * A * x ^ (α - 1)) (Set.Ioi 0) := fun x hx =>
    (continuousAt_const.mul (continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx)))).continuousWithinAt
  have hinvc : ContinuousOn (fun x : ℝ => 1 / x) (Set.Ioi 0) := fun x hx =>
    (continuousAt_const.div continuousAt_id (ne_of_gt hx)).continuousWithinAt
  have hu' : StrictAntiOn (fun x : ℝ => 1 / x) (Set.Ioi 0) := fun x hx _ _ hxy =>
    one_div_lt_one_div_of_lt hx hxy
  have hinada : Tendsto (fun x : ℝ => 1 / x) (𝓝[>] 0) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  have hui : ∀ y : ℝ, 0 < y → 0 < 1 / y ∧ 1 / (1 / y) = y := fun y hy =>
    ⟨one_div_pos.2 hy, one_div_one_div y⟩
  have hf0 : A * (0 : ℝ) ^ α = 0 := by rw [zero_rpow hα0.ne', mul_zero]
  obtain ⟨g, hgex, hgiff⟩ := saddle_path_general (f := fun x => A * x ^ α) (ui := fun y => 1 / y)
    hβ0 hβ1 le_rfl hf0 hf hfd hf'pos hf' hf'c (fun x hx => one_div_pos.2 hx) hu' hinvc hinada
    hui hinvc hkb h411
  refine ⟨g, fun x hx => ?_, hgiff⟩
  obtain ⟨-, ks, cs, hss, hks, hcs, hks0, hcs0, hksc, hcsc⟩ := hgex x hx
  have hcb : A * kb ^ α - 1 * kb = (1 - α * β) * A * kb ^ α := by
    have := hsteady.1
    rw [← hkbdef] at this
    nth_rewrite 2 [this]
    ring
  have h1 := ((saddle_logCobbDouglas hA hα0 hα1 hβ0 hβ1 hss hcs (hks 0)).1 hks).1
    ⟨hksc, by rw [← hcb]; exact hcsc⟩
  rw [← hcs0, h1, hks0]

end AKMM.DynamicOptimization
