/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.CGBestWorst
import DynamicGames.CGOnePeriod

/-!
# Exercise 21.6: a two-action credible-policy economy

Miao, Exercise 21.6 (c)–(f), pp. 771–772, for the economy `cg_r216`, `cg_C216` of
`CGOnePeriod` (`0, 1 = L, H`; competitive equilibria `(x_L, y_L)` and `(x_H, y_H)`; no
one-period Nash equilibrium, so Nash reversion is unavailable and punishments must come from
the worst SPE).

* `cg_ex216_V`: for `5/8 ≤ δ < 1` the SPE value set is `V = [1, 10]`; it is the value set of an
  explicit recursive strategy (`(x_L, y_L)` with reward `v/δ` below the threshold `15 − 14δ`,
  `(x_H, y_H)` with reward `(v − 10(1 − δ))/δ` above it, and the worst value `1` after any
  deviation).
* `ex_21_6_c`: the worst SPE value is `1 = min(max_y r(x_L, y), max_y r(x_H, y))`; every SPE
  attaining it starts with `(x_L, y_L)` and continues with value `1/δ`; the recursive strategy
  from the state `1` is such an SPE, its outcome path given by `definition_21_4_5`.
* `ex_21_6_d`: at `δ = 0.9` infinite repetition of the Ramsey outcome is an SPE path: play
  `(x_H, y_H)`, and after a deviation switch to the worst SPE (value `1`); the deviation pays
  `0.1 · 15 + 0.9 · 1 = 2.4 < 10`.
* `ex_21_6_e`: the best SPE value is `10` (for `5/8 ≤ δ < 1`).
* `ex_21_6_f`: if repetition of the Ramsey outcome is an SPE path then `δ > 5/14`, and it is one
  for every `δ ∈ [1/2, 1)` (stick-and-carrot between `10δ` and `10`). The bound `5/14` is what
  the deviation condition `10 ≥ 15(1 − δ) + δ v_min` gives with `v_min = 1`, but at `δ = 5/14`
  the value `1` is not an SPE value, so the threshold is not attained. Not formalised: the exact
  infimum of the set of such `δ` (it lies in `(5/14, 1/2]`).
-/

namespace Miao.DynamicGames

theorem cg_r216_abs_le (x y : Fin 2) : |cg_r216 x y| ≤ 15 := by
  fin_cases x <;> fin_cases y <;> norm_num [cg_r216, abs_le]

theorem cg_C216_mem {x y : Fin 2} : (x, y) ∈ cg_C216 ↔ x = y := Iff.rfl

/-- Every SPE value of Exercise 21.6 is at least `1` (any `δ ∈ [0, 1)`). -/
theorem cg_ex216_V_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r216 cg_C216, 1 ≤ v := by
  refine cg_V_lower hδ0 hδ1 cg_r216_abs_le ?_
  intro x y hxy
  rw [cg_C216_mem] at hxy
  subst hxy
  fin_cases x
  · exact ⟨1, by norm_num [cg_r216]⟩
  · exact ⟨0, by norm_num [cg_r216]⟩

/-- Every SPE value of Exercise 21.6 is at most the Ramsey value `10` (any `δ ∈ [0, 1)`). -/
theorem cg_ex216_V_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r216 cg_C216, v ≤ 10 := by
  intro v hv
  refine (cg_V_subset_Icc (a := 0) hδ0 hδ1 cg_r216_abs_le ?_ hv).2
  rintro ⟨x, y⟩ (hxy : x = y)
  subst hxy
  fin_cases x <;> norm_num [cg_r216]

/-- The action of the recursive strategy generating `[1, 10]`. -/
noncomputable def cg_ex216Z (δ v : ℝ) : Fin 2 := if v < 15 - 14 * δ then 0 else 1

/-- The on-path next state of the recursive strategy generating `[1, 10]`. -/
noncomputable def cg_ex216Next (δ v : ℝ) : ℝ :=
  if v < 15 - 14 * δ then v / δ else (v - (1 - δ) * 10) / δ

/-- The state map of the recursive strategy generating `[1, 10]`: the next state on path, the
worst value `1` after any deviation. -/
noncomputable def cg_ex216V (δ v : ℝ) (x y : Fin 2) : ℝ :=
  if x = cg_ex216Z δ v ∧ y = cg_ex216Z δ v then cg_ex216Next δ v else 1

/-- For `5/8 ≤ δ < 1`, every `v ∈ [1, 10]` is the value of an SPE of Exercise 21.6: the
recursive strategy `cg_ex216Z`, `cg_ex216V`. -/
theorem cg_ex216_recursive_spe {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ Set.Icc (1 : ℝ) 10,
      cg_IsSPE δ cg_r216 cg_C216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) v) ∧
      cg_U δ cg_r216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) v) = v := by
  have hδ0 : 0 < δ := by linarith
  have hpk : ∀ s ∈ Set.Icc (1 : ℝ) 10, (1 - δ) * cg_r216 (cg_ex216Z δ s) (cg_ex216Z δ s) +
      δ * cg_ex216V δ s (cg_ex216Z δ s) (cg_ex216Z δ s) = s := by
    intro s _
    simp only [cg_ex216V, and_self, ↓reduceIte]
    unfold cg_ex216Z cg_ex216Next
    split_ifs
    · norm_num [cg_r216]; field_simp
    · norm_num [cg_r216]; field_simp; ring
  refine cg_recursive_spe (K := 10) hδ0.le hδ1 cg_r216_abs_le ?_ ?_ hpk ?_ ?_
  · intro s hs
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  · intro s hs ξ η
    obtain ⟨hs1, hs2⟩ := hs
    unfold cg_ex216V
    split_ifs
    · unfold cg_ex216Next
      split_ifs with h1
      · constructor
        · rw [le_div_iff₀ hδ0]; linarith
        · rw [div_le_iff₀ hδ0]; linarith
      · push Not at h1
        constructor
        · rw [le_div_iff₀ hδ0]; linarith
        · rw [div_le_iff₀ hδ0]; linarith
    · constructor <;> norm_num
  · intro s _
    exact rfl
  · intro s hs y'
    obtain ⟨hs1, hs2⟩ := hs
    by_cases hy : y' = cg_ex216Z δ s
    · rw [hy]
      exact le_of_eq (hpk s ⟨hs1, hs2⟩)
    · have hV : cg_ex216V δ s (cg_ex216Z δ s) y' = 1 := by simp [cg_ex216V, hy]
      rw [hV]
      by_cases h1 : s < 15 - 14 * δ
      · have hz : cg_ex216Z δ s = 0 := by simp [cg_ex216Z, h1]
        rw [hz] at hy ⊢
        fin_cases y'
        · exact absurd rfl hy
        · norm_num [cg_r216]; linarith
      · have hz : cg_ex216Z δ s = 1 := by simp [cg_ex216Z, h1]
        rw [hz] at hy ⊢
        push Not at h1
        fin_cases y'
        · norm_num [cg_r216]; linarith
        · exact absurd rfl hy

/-- For `5/8 ≤ δ < 1`, the SPE value set of Exercise 21.6 is `V = [1, 10]`. -/
theorem cg_ex216_V {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    cg_V δ cg_r216 cg_C216 = Set.Icc 1 10 := by
  have hδ0 : 0 ≤ δ := by linarith
  ext v
  constructor
  · intro hv
    exact ⟨cg_ex216_V_ge hδ0 hδ1 v hv, cg_ex216_V_le hδ0 hδ1 v hv⟩
  · intro hv
    exact ⟨_, (cg_ex216_recursive_spe hδ hδ1 v hv).1, (cg_ex216_recursive_spe hδ hδ1 v hv).2⟩

/-- **Exercise 21.6 (c)** (Miao, p. 772), for `5/8 ≤ δ < 1` (which includes the `δ = 0.9` of
part (d)). The worst SPE value is `1`. Every SPE attaining it starts with `(x_L, y_L)` and
continues with value `1/δ`. The recursive strategy from the state `1` attains it; its outcome
path is `(z(v_t), z(v_t))` with `v_1 = 1`, `v_2 = 1/δ` and `v_{t+1}` the on-path next state
(`definition_21_4_5`). -/
theorem ex_21_6_c {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    IsLeast (cg_V δ cg_r216 cg_C216) 1 ∧
      (∀ σ, cg_IsSPE δ cg_r216 cg_C216 σ → cg_U δ cg_r216 σ = 1 →
        σ [] = (0, 0) ∧ cg_U δ cg_r216 (cg_cont σ [σ []]) = 1 / δ) ∧
      cg_IsSPE δ cg_r216 cg_C216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) ∧
      cg_U δ cg_r216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) = 1 ∧
      cg_path (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) 0 = (0, 0) ∧
      cg_recSeq (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1 1 = 1 / δ := by
  have hδ0 : 0 < δ := by linarith
  have h1 : (1 : ℝ) < 15 - 14 * δ := by linarith
  have hz1 : cg_ex216Z δ 1 = 0 := by simp [cg_ex216Z, h1]
  refine ⟨?_, fun σ hσ hv => ?_, (cg_ex216_recursive_spe hδ hδ1 1 ⟨le_rfl, by norm_num⟩).1,
    (cg_ex216_recursive_spe hδ hδ1 1 ⟨le_rfl, by norm_num⟩).2, ?_, ?_⟩
  · rw [cg_ex216_V hδ hδ1]; exact isLeast_Icc (by norm_num)
  · have hrec := cg_U_rec hδ0.le hδ1 cg_r216_abs_le σ
    have hroot := (hσ.root hδ0.le hδ1 cg_r216_abs_le).2
    have hC : σ [] ∈ cg_C216 := (hσ []).1
    have hmem : ∀ q, cg_U δ cg_r216 (cg_cont σ [q]) ∈ cg_V δ cg_r216 cg_C216 :=
      fun q => ⟨_, hσ.cont hδ0.le hδ1 cg_r216_abs_le _, rfl⟩
    rcases h : σ [] with ⟨x, y⟩
    rw [h] at hC hrec hroot
    rw [cg_C216_mem] at hC
    subst hC
    obtain rfl | rfl : x = 0 ∨ x = 1 := by fin_cases x <;> simp
    · refine ⟨rfl, ?_⟩
      rw [hv] at hrec
      norm_num [cg_r216] at hrec
      field_simp
      linarith
    · exfalso
      have := hroot 0
      have hge := cg_ex216_V_ge hδ0.le hδ1 _ (hmem ((1 : Fin 2), (0 : Fin 2)))
      rw [hv] at this
      norm_num [cg_r216] at this
      nlinarith
  · rw [(definition_21_4_5 _ _ _ 1 0).1]
    simp [cg_recSeq, hz1]
  · simp only [cg_recSeq, hz1, cg_ex216V, and_self, ↓reduceIte, cg_ex216Next, h1]

/-- The Ramsey outcome `(x_H, y_H)` forever. -/
def cg_ramseyPath216 : ℕ → Fin 2 × Fin 2 := fun _ => (1, 1)

theorem cg_ramseyPath216_Ut {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (t : ℕ) :
    cg_Ut δ cg_r216 cg_ramseyPath216 t = 10 := by
  unfold cg_Ut cg_ramseyPath216
  rw [cg_pathValue_const hδ0 hδ1]
  norm_num [cg_r216]

/-- For `5/8 ≤ δ < 1`, "play `(x_H, y_H)`; after any deviation switch to the worst SPE" is an
SPE whose path is the repeated Ramsey outcome. -/
theorem cg_ex216_ramsey_spe {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    cg_IsSPE δ cg_r216 cg_C216 (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) 0) ∧
      cg_path (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) 0) = cg_ramseyPath216 := by
  have hδ0 : 0 ≤ δ := by linarith
  have hw := cg_ex216_recursive_spe hδ hδ1 1 ⟨le_rfl, by norm_num⟩
  refine cg_follow_spe hδ0 hδ1 cg_r216_abs_le hw.1 (fun _ => rfl) ?_
  intro t η hη
  rw [hw.2, cg_ramseyPath216_Ut hδ0 hδ1]
  simp only [cg_ramseyPath216] at hη ⊢
  fin_cases η
  · norm_num [cg_r216]; linarith
  · exact absurd rfl hη

/-- **Exercise 21.6 (d)** (Miao, p. 772). At `δ = 0.9` infinite repetition of the Ramsey outcome
is sustainable as an SPE: play `(x_H, y_H)`; after any deviation switch to the worst SPE (value
`1`); the deviation pays `0.1 · 15 + 0.9 · 1 = 2.4 < 10`. -/
theorem ex_21_6_d :
    cg_IsSPE (9 / 10) cg_r216 cg_C216 (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z (9 / 10)) (cg_ex216Z (9 / 10)) (cg_ex216V (9 / 10)) 1) 0) ∧
      cg_path (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z (9 / 10)) (cg_ex216Z (9 / 10)) (cg_ex216V (9 / 10)) 1) 0) =
        cg_ramseyPath216 ∧
      (1 - 9 / 10 : ℝ) * cg_r216 1 0 + 9 / 10 * 1 = 12 / 5 :=
  ⟨(cg_ex216_ramsey_spe (by norm_num) (by norm_num)).1,
    (cg_ex216_ramsey_spe (by norm_num) (by norm_num)).2, by norm_num [cg_r216]⟩

/-- **Exercise 21.6 (e)** (Miao, p. 772): the best SPE value is the Ramsey value `10` (for
`5/8 ≤ δ < 1`). -/
theorem ex_21_6_e {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    IsGreatest (cg_V δ cg_r216 cg_C216) 10 := by
  rw [cg_ex216_V hδ hδ1]; exact isGreatest_Icc (by norm_num)

/-- At `δ = 5/14`, an SPE value below `10` is generated by `(x_L, y_L)` and the continuation
value `14v/5`. -/
theorem cg_ex216_step {v : ℝ} (hv : v ∈ cg_V (5 / 14) cg_r216 cg_C216) (hv10 : v < 10) :
    14 / 5 * v ∈ cg_V (5 / 14) cg_r216 cg_C216 := by
  have hδ0 : (0 : ℝ) ≤ 5 / 14 := by norm_num
  have hδ1 : (5 / 14 : ℝ) < 1 := by norm_num
  obtain ⟨x, y, w, ⟨hC, hw, hIC⟩, hvw⟩ := cg_V_subset_B hδ0 hδ1 cg_r216_abs_le hv
  rw [cg_C216_mem] at hC
  subst hC
  fin_cases x
  · have : 14 / 5 * v = w (0, 0) := by
      norm_num [cg_r216] at hvw
      linarith
    rw [this]
    exact hw _
  · exfalso
    have h1 := hIC 0
    have h2 := cg_ex216_V_ge hδ0 hδ1 _ (hw ((1 : Fin 2), (0 : Fin 2)))
    rw [← hvw] at h1
    norm_num [cg_r216] at h1
    linarith

/-- The stick-and-carrot recursive strategy on `{10δ, 10}` of Exercise 21.6 (f). -/
noncomputable def cg_ex216Z2 (v : ℝ) : Fin 2 := if v = 10 then 1 else 0

/-- Its state map: `10` after the prescribed pair, `10δ` otherwise. -/
noncomputable def cg_ex216V2 (δ v : ℝ) (x y : Fin 2) : ℝ :=
  if x = cg_ex216Z2 v ∧ y = cg_ex216Z2 v then 10 else 10 * δ

/-- **Exercise 21.6 (f)** (Miao, p. 772). If infinite repetition of the Ramsey outcome is an SPE
path then `δ > 5/14`; for every `δ ∈ [1/2, 1)` it is one (supported by the stick-and-carrot
strategy that punishes a deviation with one period of `(x_L, y_L)`, value `10δ`). -/
theorem ex_21_6_f :
    (∀ δ : ℝ, 0 ≤ δ → δ < 1 →
      (∃ σ, cg_IsSPE δ cg_r216 cg_C216 σ ∧ cg_path σ = cg_ramseyPath216) → 5 / 14 < δ) ∧
    (∀ δ : ℝ, 1 / 2 ≤ δ → δ < 1 →
      cg_IsSPE δ cg_r216 cg_C216 (cg_recStrat cg_ex216Z2 cg_ex216Z2 (cg_ex216V2 δ) 10) ∧
      cg_path (cg_recStrat cg_ex216Z2 cg_ex216Z2 (cg_ex216V2 δ) 10) = cg_ramseyPath216) := by
  constructor
  · rintro δ hδ0 hδ1 ⟨σ, hσ, hpath⟩
    have hU : cg_U δ cg_r216 σ = 10 := by
      have := cg_ramseyPath216_Ut hδ0 hδ1 0
      rw [cg_Ut_zero] at this
      unfold cg_U
      rw [hpath]
      exact this
    have h0 : σ [] = (1, 1) := congrFun hpath 0
    have hroot := (hσ.root hδ0 hδ1 cg_r216_abs_le).2 0
    have hmem : cg_U δ cg_r216 (cg_cont σ [((σ []).1, 0)]) ∈ cg_V δ cg_r216 cg_C216 :=
      ⟨_, hσ.cont hδ0 hδ1 cg_r216_abs_le _, rfl⟩
    have hge := cg_ex216_V_ge hδ0 hδ1 _ hmem
    rw [hU, h0] at hroot
    rw [h0] at hge hmem
    norm_num [cg_r216] at hroot
    by_contra hlt
    push Not at hlt
    have hδeq : δ = 5 / 14 := by nlinarith
    subst hδeq
    have hu1 : cg_U (5 / 14) cg_r216 (cg_cont σ [((1 : Fin 2), (0 : Fin 2))]) = 1 := by
      linarith
    rw [hu1] at hmem
    have h2 := cg_ex216_step hmem (by norm_num)
    have h3 := cg_ex216_step h2 (by norm_num)
    have h4 := cg_ex216_step h3 (by norm_num)
    have := cg_ex216_V_le hδ0 hδ1 _ h4
    norm_num at this
  · intro δ hδ hδ1
    have hδ0 : 0 ≤ δ := by linarith
    have hne : 10 * δ ≠ 10 := by intro h; linarith
    have hz10 : cg_ex216Z2 10 = 1 := by simp [cg_ex216Z2]
    have hzd : cg_ex216Z2 (10 * δ) = 0 := by simp [cg_ex216Z2, hne]
    have hspe := cg_recursive_spe (C := cg_C216) (K := 10) (S := {10 * δ, 10}) hδ0 hδ1
      cg_r216_abs_le (zh := cg_ex216Z2) (zg := cg_ex216Z2) (Vf := cg_ex216V2 δ) ?_ ?_ ?_ ?_ ?_
      10 (Or.inr rfl)
    · refine ⟨hspe.1, funext fun n => ?_⟩
      have hseq : ∀ m, cg_recSeq cg_ex216Z2 cg_ex216Z2 (cg_ex216V2 δ) 10 m = 10 := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          have e : cg_ex216V2 δ 10 (cg_ex216Z2 10) (cg_ex216Z2 10) = 10 := by
            simp [cg_ex216V2]
          simp only [cg_recSeq, e]
          exact ih
      rw [(definition_21_4_5 _ _ _ 10 n).1, hseq, hz10]
      rfl
    · intro s hs
      rcases hs with rfl | rfl
      · rw [abs_le]; constructor <;> linarith
      · norm_num
    · intro s _ ξ η
      unfold cg_ex216V2
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro s hs
      simp only [cg_ex216V2, and_self, ↓reduceIte]
      rcases hs with rfl | rfl
      · rw [hzd]; norm_num [cg_r216]; ring
      · rw [hz10]; norm_num [cg_r216]; ring
    · intro s _
      exact rfl
    · have r00 : cg_r216 0 0 = 0 := by norm_num [cg_r216]
      have r01 : cg_r216 0 1 = 1 := by norm_num [cg_r216]
      have r10 : cg_r216 1 0 = 15 := by norm_num [cg_r216]
      have r11 : cg_r216 1 1 = 10 := by norm_num [cg_r216]
      intro s hs y'
      obtain rfl | rfl : y' = 0 ∨ y' = 1 := by fin_cases y' <;> simp
      · rcases hs with rfl | rfl
        · have : cg_ex216V2 δ (10 * δ) (cg_ex216Z2 (10 * δ)) 0 = 10 := by
            simp [cg_ex216V2, hzd]
          rw [this, hzd, r00]
          linarith
        · have : cg_ex216V2 δ 10 (cg_ex216Z2 10) 0 = 10 * δ := by simp [cg_ex216V2, hz10]
          rw [this, hz10, r10]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * δ - 1) (by linarith : (0 : ℝ) ≤ 1 - δ)]
      · rcases hs with rfl | rfl
        · have : cg_ex216V2 δ (10 * δ) (cg_ex216Z2 (10 * δ)) 1 = 10 * δ := by
            simp [cg_ex216V2, hzd]
          rw [this, hzd, r01]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 10 * δ - 1)
            (by linarith : (0 : ℝ) ≤ 1 - δ)]
        · have : cg_ex216V2 δ 10 (cg_ex216Z2 10) 1 = 10 := by simp [cg_ex216V2, hz10]
          rw [this, hz10, r11]
          linarith

end Miao.DynamicGames
