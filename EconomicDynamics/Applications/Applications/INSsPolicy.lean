/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INCConvex

/-!
# The (s, S) policy for a c-convex function: Lemma 8.5.2

Miao, §8.5, pp. 264–269. For a function `G : ℝ → ℝ` (the book's `G_n(y) = L(y) + py + …`) the
ordering problem at stock `x` is `min_{y ≥ x} c·1_{y > x} + G(y)` (`in_fix c x y = c·1_{y>x}`).

* `in_Coercive`, `in_Sbar` (smallest global minimiser, the book's `S_n`), `in_sbar` (the
  smallest solution of (8.23), the book's `s_n`), with `in_Sbar_isLeast`, `in_sbar_isLeast`.
* For a minimiser `S`, a c-convex `G` (`c ≥ 0`) and `s` the least point with
  `G(s) ≤ c + G(S)`:
  `in_ss_le` (`s ≤ S`), `in_ss_gt` (`G(x) > c + G(S)` for `x < s`), `in_ss_eq` ((8.23):
  `G(s) = c + G(S)` when `G` is continuous at `s`), `in_ss_lt_of_pos` (`s < S` when `c > 0`),
  `in_ss_key` (`G(x) ≤ G(y) + c` for `s ≤ x ≤ y`), `in_ss_strictAnti` (`G` is decreasing on
  `(−∞, s]`, p. 269).
* **Lemma 8.5.2** (`lemma_8_5_2`): the (s, S) rule `in_ssPolicy s S x = S` if `x ≤ s`, `= x`
  otherwise, attains the minimum, and the minimum value is `G(max(x, s))` (`in_ss_value`).
* For Lemma 8.5.3: `x ↦ G(max(x, s))` is c-convex (`in_ss_cconvex_max`), continuous, satisfies
  `G(max(w, s)) ≤ c + G(max(w + a, s))` (`in_ss_P`), and inherits antitonicity
  (`in_ss_antitoneOn`).
* `c = 0` gives `s = S` (`in_sbar_eq_of_zero`).

**Departures.** The book's proof of Lemma 8.5.2 contains misprints (`(G(s_n) − G(x))/(s_n − s)`,
`G_n(x_n)`); we give our own proof of the same statement. The book says "optimal not to order
for all `x > s_n`"; at `x = s_n` the firm is indifferent, and our rule orders there, as the
book's `d_n` does. When `c = 0` the book's requirement `s_n < S_n` cannot hold (then
`s_n = S_n`), so `in_sbar` is the least `x ≤ ⋯` with `G(x) ≤ c + G(S)`, which is `< S` exactly
when `c > 0`.
-/

namespace Miao.Applications

open Filter Topology

/-- The fixed part of the ordering cost, `c·1_{y > x}` (Miao, p. 263). -/
noncomputable def in_fix (c x y : ℝ) : ℝ := if x < y then c else 0

/-- Coercivity, `G(y) → +∞` as `|y| → ∞` (Miao, Assumption 8.5.1, p. 263). -/
def in_Coercive (G : ℝ → ℝ) : Prop := Tendsto G atBot atTop ∧ Tendsto G atTop atTop

/-- The smallest global minimiser of `G` (Miao, p. 265: "Let `S_n` be the smallest minimizer"). -/
noncomputable def in_Sbar (G : ℝ → ℝ) : ℝ := sInf {x | ∀ y, G x ≤ G y}

/-- The smallest `s` with `G(s) ≤ c + G(S)`, `S = in_Sbar G` (Miao, (8.23), p. 265). -/
noncomputable def in_sbar (c : ℝ) (G : ℝ → ℝ) : ℝ := sInf {x | G x ≤ c + G (in_Sbar G)}

/-- The (s, S) rule: the stock after ordering, `S` if `x ≤ s` and `x` otherwise
(Miao, p. 268: `x + d(x)`). -/
noncomputable def in_ssPolicy (s S x : ℝ) : ℝ := if x ≤ s then S else x

theorem in_fix_nonneg {c : ℝ} (hc : 0 ≤ c) (x y : ℝ) : 0 ≤ in_fix c x y := by
  unfold in_fix; split_ifs <;> simp [hc]

theorem in_fix_le {c : ℝ} (hc : 0 ≤ c) (x y : ℝ) : in_fix c x y ≤ c := by
  unfold in_fix; split_ifs <;> simp [hc]

theorem in_fix_self (c x : ℝ) : in_fix c x x = 0 := by simp [in_fix]

theorem in_fix_of_lt (c : ℝ) {x y : ℝ} (h : x < y) : in_fix c x y = c := by
  simp [in_fix, h]

/-- A sublevel set of a function tending to `+∞` at `−∞` is bounded below. -/
theorem in_bddBelow_sublevel {G : ℝ → ℝ} (hG : Tendsto G atBot atTop) (K : ℝ) :
    BddBelow {x | G x ≤ K} := by
  obtain ⟨M, hM⟩ := Filter.eventually_atBot.1 (hG.eventually (eventually_gt_atTop K))
  refine ⟨M, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have := hM x hcon.le
  simp only [Set.mem_ofPred_eq] at hx
  linarith

/-- A continuous coercive function has a global minimiser. -/
theorem in_exists_min {G : ℝ → ℝ} (hc : Continuous G) (hG : in_Coercive G) :
    ∃ x, ∀ y, G x ≤ G y := by
  refine hc.exists_forall_le ?_
  rw [cocompact_eq_atBot_atTop]
  exact hG.1.sup hG.2

/-- `in_Sbar G` is the least global minimiser of a continuous coercive `G`. -/
theorem in_Sbar_isLeast {G : ℝ → ℝ} (hc : Continuous G) (hG : in_Coercive G) :
    IsLeast {x | ∀ y, G x ≤ G y} (in_Sbar G) := by
  obtain ⟨x₀, hx₀⟩ := in_exists_min hc hG
  have hcl : IsClosed {x | ∀ y, G x ≤ G y} := by
    have : {x | ∀ y, G x ≤ G y} = ⋂ y, {x | G x ≤ G y} := by ext; simp
    rw [this]
    exact isClosed_iInter fun y => isClosed_le hc continuous_const
  have hB : BddBelow {x | ∀ y, G x ≤ G y} :=
    (in_bddBelow_sublevel hG.1 (G x₀)).mono fun x hx => hx x₀
  exact ⟨hcl.csInf_mem ⟨x₀, hx₀⟩ hB, fun y hy => csInf_le hB hy⟩

/-- `in_sbar c G` is the least `x` with `G(x) ≤ c + G(S)`, `S = in_Sbar G`. -/
theorem in_sbar_isLeast {c : ℝ} (hc0 : 0 ≤ c) {G : ℝ → ℝ} (hc : Continuous G)
    (hG : in_Coercive G) : IsLeast {x | G x ≤ c + G (in_Sbar G)} (in_sbar c G) := by
  have hcl : IsClosed {x | G x ≤ c + G (in_Sbar G)} := isClosed_le hc continuous_const
  have hB := in_bddBelow_sublevel hG.1 (c + G (in_Sbar G))
  have hne : ({x | G x ≤ c + G (in_Sbar G)} : Set ℝ).Nonempty :=
    ⟨in_Sbar G, by simp only [Set.mem_ofPred_eq]; linarith⟩
  exact ⟨hcl.csInf_mem hne hB, fun y hy => csInf_le hB hy⟩

/-- `s ≤ S`. -/
theorem in_ss_le {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ} {s S : ℝ}
    (hs : IsLeast {x | G x ≤ c + G S} s) : s ≤ S :=
  hs.2 (by simp only [Set.mem_ofPred_eq]; linarith)

/-- For `x < s`, `G(x) > c + G(S)`: ordering up to `S` is strictly better (Miao, p. 268). -/
theorem in_ss_gt {c : ℝ} {G : ℝ → ℝ} {s S x : ℝ} (hs : IsLeast {x | G x ≤ c + G S} s)
    (hx : x < s) : c + G S < G x := by
  by_contra h
  push Not at h
  exact absurd (hs.2 h) (not_le.2 hx)

/-- Miao, (8.23), p. 265: `G(s) = c + G(S)` (for `G` continuous at `s`). -/
theorem in_ss_eq {c : ℝ} {G : ℝ → ℝ} {s S : ℝ} (hs : IsLeast {x | G x ≤ c + G S} s)
    (hcont : ContinuousAt G s) : G s = c + G S := by
  refine le_antisymm hs.1 ?_
  by_contra h
  push Not at h
  have hev : ∀ᶠ x in 𝓝[<] s, G x < c + G S :=
    (hcont.eventually (gt_mem_nhds h)).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
  have := in_ss_gt hs (Set.mem_Iio.1 hx2)
  linarith

/-- Miao, p. 265: when `c > 0`, `s < S`. -/
theorem in_ss_lt_of_pos {c : ℝ} (hc : 0 < c) {G : ℝ → ℝ} {s S : ℝ}
    (hs : IsLeast {x | G x ≤ c + G S} s) (hcont : ContinuousAt G s) : s < S := by
  rcases eq_or_lt_of_le (in_ss_le hc.le hs) with h | h
  · have := in_ss_eq hs hcont
    rw [h] at this
    linarith
  · exact h

/-- Miao, p. 268, proof of Lemma 8.5.2: `G(x) ≤ G(y) + c` for all `s ≤ x ≤ y`. -/
theorem in_ss_key {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ} (hcc : in_CConvex c G) {s S : ℝ}
    (hS : ∀ y, G S ≤ G y) (hs : IsLeast {x | G x ≤ c + G S} s) {x y : ℝ} (hsx : s ≤ x)
    (hxy : x ≤ y) : G x ≤ c + G y := by
  rcases le_or_gt x S with hxS | hxS
  · have h1 : G x ≤ c + G S := by
      rcases eq_or_lt_of_le hsx with h | h
      · rw [← h]; exact hs.1
      rcases eq_or_lt_of_le hxS with h' | h'
      · rw [h']; linarith
      by_contra hcon
      push Not at hcon
      have key := hcc x (S - x) (x - s) (sub_pos.2 h') (sub_pos.2 h)
      have e1 : x + (S - x) = S := by ring
      have e2 : x - (x - s) = s := by ring
      rw [e1, e2] at key
      have hsS : G s ≤ c + G S := hs.1
      have : 0 < (S - x) * ((G x - G s) / (x - s)) :=
        mul_pos (sub_pos.2 h') (div_pos (by linarith) (sub_pos.2 h))
      linarith
    linarith [hS y]
  · rcases eq_or_lt_of_le hxy with h | h
    · rw [h]; linarith
    have key := hcc x (y - x) (x - S) (sub_pos.2 h) (sub_pos.2 hxS)
    have e1 : x + (y - x) = y := by ring
    have e2 : x - (x - S) = S := by ring
    rw [e1, e2] at key
    have : 0 ≤ (y - x) * ((G x - G S) / (x - S)) :=
      mul_nonneg (sub_pos.2 h).le (div_nonneg (sub_nonneg.2 (hS x)) (sub_pos.2 hxS).le)
    linarith

/-- Miao, p. 269: `G` is (strictly) decreasing on `(−∞, s]`. -/
theorem in_ss_strictAnti {c : ℝ} {G : ℝ → ℝ} (hcc : in_CConvex c G) {s S : ℝ}
    (hs : IsLeast {x | G x ≤ c + G S} s) (hsS : s ≤ S) {x₁ x₂ : ℝ} (h12 : x₁ < x₂)
    (h2 : x₂ ≤ s) : G x₂ < G x₁ := by
  rcases eq_or_lt_of_le h2 with h | h
  · rw [h]
    have := in_ss_gt hs (h ▸ h12)
    have h1 : G s ≤ c + G S := hs.1
    linarith
  · have hx2 := in_ss_gt hs h
    have key := hcc x₂ (S - x₂) (x₂ - x₁) (by linarith) (sub_pos.2 h12)
    have e1 : x₂ + (S - x₂) = S := by ring
    have e2 : x₂ - (x₂ - x₁) = x₁ := by ring
    rw [e1, e2] at key
    by_contra hcon
    push Not at hcon
    have : 0 ≤ (S - x₂) * ((G x₂ - G x₁) / (x₂ - x₁)) :=
      mul_nonneg (by linarith) (div_nonneg (sub_nonneg.2 hcon) (sub_pos.2 h12).le)
    linarith

/-- **Lemma 8.5.2** (Miao, p. 268). Let `c ≥ 0`, `G` c-convex, `S` a global minimiser of `G` and
`s` the smallest solution of `G(s) ≤ c + G(S)` (so `G(s) = c + G(S)`, (8.23)). If `G` is
continuous, the (s, S) policy — order up to `S` if `x ≤ s`, do not order if `x > s` — is optimal:
`c·1_{y*>x} + G(y*) ≤ c·1_{y>x} + G(y)` for all `y ≥ x`, where `y* = in_ssPolicy s S x`. -/
theorem lemma_8_5_2 {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ} (hcont : Continuous G)
    (hcc : in_CConvex c G) {s S : ℝ}
    (hS : ∀ y, G S ≤ G y) (hs : IsLeast {x | G x ≤ c + G S} s) {x y : ℝ} (hxy : x ≤ y) :
    in_fix c x (in_ssPolicy s S x) + G (in_ssPolicy s S x) ≤ in_fix c x y + G y := by
  have hsS := in_ss_le hc hs
  unfold in_ssPolicy
  split_ifs with hx
  · have hlhs : in_fix c x S + G S ≤ c + G S := by linarith [in_fix_le hc x S]
    rcases eq_or_lt_of_le hxy with h | h
    · rw [← h, in_fix_self]
      rcases eq_or_lt_of_le hx with h' | h'
      · -- `x = s`: if `s < S` use `G(s) ≥ c + G(S)`; if `s = S` there is no order at all.
        rcases eq_or_lt_of_le hsS with h'' | h''
        · rw [h', h'', in_fix_self]
        · rw [in_fix_of_lt c (h' ▸ h''), h', in_ss_eq hs (hcont.continuousAt), zero_add]
      · linarith [in_ss_gt hs h']
    · rw [in_fix_of_lt c h]
      linarith [hS y]
  · push Not at hx
    rw [in_fix_self]
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h, in_fix_self]
    · rw [in_fix_of_lt c h]
      linarith [in_ss_key hc hcc hS hs hx.le hxy]

/-- Miao, (8.26), p. 270: the value of the (s, S) rule is `G(max(x, s))`, i.e. `c + G(S) = G(s)`
for `x ≤ s` and `G(x)` for `x > s`. -/
theorem in_ss_policy_value {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ} (hcont : Continuous G) {s S : ℝ}
    (hs : IsLeast {x | G x ≤ c + G S} s) (x : ℝ) :
    in_fix c x (in_ssPolicy s S x) + G (in_ssPolicy s S x) = G (max x s) := by
  have hsS := in_ss_le hc hs
  have heq := in_ss_eq hs hcont.continuousAt
  unfold in_ssPolicy
  split_ifs with hx
  · rw [max_eq_right hx, heq]
    rcases eq_or_lt_of_le (hx.trans hsS) with h | h
    · rw [h, in_fix_self]
      have : s = S := le_antisymm hsS (h ▸ hx)
      rw [this] at heq
      linarith
    · rw [in_fix_of_lt c h]
  · push Not at hx
    rw [max_eq_left hx.le, in_fix_self, zero_add]

/-- **Lemma 8.5.2** (Miao, p. 268), value form: `min_{y ≥ x} c·1_{y>x} + G(y) = G(max(x, s))`,
the minimum being attained by the (s, S) rule. -/
theorem in_ss_value {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ} (hcont : Continuous G)
    (hcc : in_CConvex c G) {s S : ℝ} (hS : ∀ y, G S ≤ G y)
    (hs : IsLeast {x | G x ≤ c + G S} s) (x : ℝ) :
    (⨅ y : Set.Ici x, (in_fix c x y + G y)) = G (max x s) := by
  have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
  have hB : BddBelow (Set.range fun y : Set.Ici x => in_fix c x y + G y) := by
    refine ⟨G S, ?_⟩
    rintro _ ⟨y, rfl⟩
    linarith [in_fix_nonneg hc x y, hS y]
  have hmem : in_ssPolicy s S x ∈ Set.Ici x := by
    unfold in_ssPolicy; split_ifs with h
    · exact Set.mem_Ici.2 (h.trans (in_ss_le hc hs))
    · exact Set.mem_Ici.2 le_rfl
  refine le_antisymm ?_ ?_
  · rw [← in_ss_policy_value hc hcont hs x]
    exact ciInf_le hB ⟨_, hmem⟩
  · refine le_ciInf fun y => ?_
    rw [← in_ss_policy_value hc hcont hs x]
    exact lemma_8_5_2 hc hcont hcc hS hs y.2

/-- Miao, p. 269, proof of Lemma 8.5.3: `x ↦ G(max(x, s))` is c-convex. -/
theorem in_ss_cconvex_max {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ} (hcc : in_CConvex c G) {s S : ℝ}
    (hS : ∀ y, G S ≤ G y) (hs : IsLeast {x | G x ≤ c + G S} s) :
    in_CConvex c (fun x => G (max x s)) := by
  intro x a b ha hb
  simp only
  have hsle : G s ≤ c + G S := hs.1
  rcases le_or_gt x s with hx | hx
  · rw [max_eq_right hx, max_eq_right (by linarith : x - b ≤ s)]
    simp only [sub_self, zero_div, mul_zero, sub_zero]
    linarith [hS (max (x + a) s)]
  · rw [max_eq_left hx.le, max_eq_left (by linarith : s ≤ x + a)]
    rcases le_or_gt s (x - b) with hxb | hxb
    · rw [max_eq_left hxb]
      exact hcc x a b ha hb
    · rw [max_eq_right hxb.le]
      rcases le_or_gt (G x) (G s) with hG | hG
      · have h1 := in_ss_key hc hcc hS hs hx.le (by linarith : x ≤ x + a)
        have : a * ((G x - G s) / b) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ha.le
            (div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le)
        linarith
      · have key := hcc x a (x - s) ha (sub_pos.2 hx)
        have e : x - (x - s) = s := by ring
        rw [e] at key
        have hq : (G x - G s) / b ≤ (G x - G s) / (x - s) :=
          div_le_div_of_nonneg_left (by linarith) (sub_pos.2 hx) (by linarith)
        have := mul_le_mul_of_nonneg_left hq ha.le
        linarith

/-- Miao, p. 270 and Lemma 8.5.5: `G(max(w, s)) ≤ c + G(max(w + a, s))` for `a ≥ 0`. -/
theorem in_ss_P {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ} (hcc : in_CConvex c G) {s S : ℝ}
    (hS : ∀ y, G S ≤ G y) (hs : IsLeast {x | G x ≤ c + G S} s) {w a : ℝ} (ha : 0 ≤ a) :
    G (max w s) ≤ c + G (max (w + a) s) :=
  in_ss_key hc hcc hS hs (le_max_right w s) (max_le_max (by linarith) le_rfl)

/-- If `G` is antitone on `(−∞, r]`, so is `x ↦ G(max(x, s))`. -/
theorem in_ss_antitoneOn {G : ℝ → ℝ} {r s : ℝ} (hG : AntitoneOn G (Set.Iic r)) :
    AntitoneOn (fun x => G (max x s)) (Set.Iic r) := by
  intro x₁ hx₁ x₂ hx₂ h12
  rcases le_or_gt (max x₂ s) r with h | h
  · exact hG (Set.mem_Iic.2 ((max_le_max h12 le_rfl).trans h)) (Set.mem_Iic.2 h)
      (max_le_max h12 le_rfl)
  · have hs : r < s := by
      rcases le_or_gt x₂ s with h' | h'
      · rw [max_eq_right h'] at h; exact h
      · rw [max_eq_left h'.le] at h; exact absurd (Set.mem_Iic.1 hx₂) (not_le.2 h)
    simp only
    rw [max_eq_right ((Set.mem_Iic.1 hx₁).trans hs.le),
      max_eq_right ((Set.mem_Iic.1 hx₂).trans hs.le)]

/-- Miao, Exercise 8.7, p. 288 (the `s = S` half): with no fixed cost, `c = 0`, the smallest
solution of (8.23) is the smallest minimiser, `in_sbar 0 G = in_Sbar G`. -/
theorem in_sbar_eq_of_zero {G : ℝ → ℝ} (hc : Continuous G) (hG : in_Coercive G) :
    in_sbar 0 G = in_Sbar G := by
  have hS := in_Sbar_isLeast hc hG
  unfold in_sbar
  have : {x | G x ≤ 0 + G (in_Sbar G)} = {x | ∀ y, G x ≤ G y} := by
    ext x
    simp only [Set.mem_ofPred_eq, zero_add]
    exact ⟨fun h y => h.trans (hS.1 y), fun h => h _⟩
  rw [this]
  rfl

end Miao.Applications
