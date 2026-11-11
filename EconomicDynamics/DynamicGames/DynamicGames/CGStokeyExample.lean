/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.CGBestWorst
import DynamicGames.CGOnePeriod

/-!
# Stokey's discrete monetary policy economy, repeated

Miao, Example 21.4.4 (p. 769) and Exercise 21.5 (p. 771): the economy of Example 21.4.2
(`cg_r422`, `cg_C422`; actions `0, 1, 2 = H, M, L`) repeated forever.

* `cg_stokey_V`: at `δ = 0.9` the SPE value set is exactly `V = [7, 9.7]` (lower bound from
  `cg_V_lower`, upper bound `max_C r = 9.7`, and the interval is the value set of an explicit
  recursive strategy). So `v_min = 7`, `v_max = 9.7`; `cg_stokey_vmin_formula` checks the
  book's recipe `v_min = r(h(y), H(h(y)))` with the binding continuation `v₁ = 70/9 ∈ V`.
* `example_21_4_4`: the path `q = (x_H, y_H), (x_M, y_M), (x_M, y_M), …` is self-enforcing at
  `δ = 0.9`, and the strategy "play `(x_L, y_L)` forever; after any deviation start `q`" is an
  SPE whose path is the repeated Ramsey outcome. The book's figures `72`, `71.8`, `94.8`, `97`
  are the values multiplied by `1/(1 − δ) = 10` (`example_21_4_4_arith`).
* `ex_21_5`: at `δ = 0.88` the path `q` is still self-enforcing but the strategy above is not
  an SPE; in fact no SPE has the repeated Ramsey outcome as its path.
* Counterexamples to statements of §§21.4.3–21.4.5 as printed, all at `δ = 0.9`:
  `cg_theorem_21_4_1_unbounded` (`B(ℝ) = ℝ ⊄ V`), `cg_proposition_21_4_1_counterexample`
  (the path `(x_L, y_M)` forever satisfies the inequality of Proposition 21.4.1 but is not
  competitive), `cg_definition_21_4_5_counterexample` (a recursive strategy satisfying
  (i)–(iii) at `v` that is not an SPE), `cg_example_21_4_5_counterexample` (the trigger strategy
  for the Ramsey outcome with `v^b = 9.7 > v^N = 8` is not an SPE) and
  `cg_example_21_4_6_counterexample` (a stick-and-carrot strategy satisfying the book's condition
  that is not an SPE).
-/

namespace Miao.DynamicGames

theorem cg_r422_abs_le (x y : Fin 3) : |cg_r422 x y| ≤ 30 := by
  fin_cases x <;> fin_cases y <;> norm_num [cg_r422, abs_le]

theorem cg_C422_mem {x y : Fin 3} : (x, y) ∈ cg_C422 ↔ x = y := Iff.rfl

/-- The action of the recursive strategy generating `[7, 9.7]` at `δ = 0.9`. -/
noncomputable def cg_stokeyZ (v : ℝ) : Fin 3 := if v ≤ 36 / 5 then 0 else if v ≤ 93 / 10
  then 1 else 2

/-- The on-path next state of the recursive strategy generating `[7, 9.7]` at `δ = 0.9`. -/
noncomputable def cg_stokeyNext (v : ℝ) : ℝ :=
  if v ≤ 36 / 5 then v * 10 / 9 else if v ≤ 93 / 10 then (v - 8 / 10) * 10 / 9
  else (v - 97 / 100) * 10 / 9

/-- The state map of the recursive strategy generating `[7, 9.7]` at `δ = 0.9`: the next state on
path, the worst value `7` after any deviation. -/
noncomputable def cg_stokeyV (v : ℝ) (x y : Fin 3) : ℝ :=
  if x = cg_stokeyZ v ∧ y = cg_stokeyZ v then cg_stokeyNext v else 7

/-- Every `v ∈ [7, 9.7]` is the value of an SPE at `δ = 0.9`: the recursive strategy
`cg_stokeyZ`, `cg_stokeyV`. -/
theorem cg_stokey_recursive_spe :
    ∀ v ∈ Set.Icc (7 : ℝ) (97 / 10),
      cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat cg_stokeyZ cg_stokeyZ cg_stokeyV v) ∧
      cg_U (9 / 10) cg_r422 (cg_recStrat cg_stokeyZ cg_stokeyZ cg_stokeyV v) = v := by
  refine cg_recursive_spe (K := 10) (by norm_num) (by norm_num) cg_r422_abs_le ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  · intro s hs ξ η
    obtain ⟨hs1, hs2⟩ := hs
    unfold cg_stokeyV
    split_ifs
    · unfold cg_stokeyNext
      split_ifs with h1 h2 <;> constructor <;> linarith
    · constructor <;> norm_num
  · intro s _
    simp only [cg_stokeyV, and_self, ↓reduceIte]
    unfold cg_stokeyZ cg_stokeyNext
    split_ifs <;> norm_num [cg_r422]
  · intro s _
    exact rfl
  · intro s hs y'
    obtain ⟨hs1, hs2⟩ := hs
    unfold cg_stokeyV
    by_cases h1 : s ≤ 36 / 5
    · have hz : cg_stokeyZ s = 0 := by simp [cg_stokeyZ, h1]
      have hn : cg_stokeyNext s = s * 10 / 9 := by simp [cg_stokeyNext, h1]
      rw [hz, hn]
      fin_cases y' <;> norm_num [cg_r422] <;> linarith
    · by_cases h2 : s ≤ 93 / 10
      · have hz : cg_stokeyZ s = 1 := by simp [cg_stokeyZ, h1, h2]
        have hn : cg_stokeyNext s = (s - 8 / 10) * 10 / 9 := by simp [cg_stokeyNext, h1, h2]
        rw [hz, hn]
        fin_cases y' <;> norm_num [cg_r422] <;> linarith
      · have hz : cg_stokeyZ s = 2 := by simp [cg_stokeyZ, h1, h2]
        have hn : cg_stokeyNext s = (s - 97 / 100) * 10 / 9 := by simp [cg_stokeyNext, h1, h2]
        rw [hz, hn]
        fin_cases y' <;> norm_num [cg_r422] <;> linarith

/-- In Example 21.4.2 every SPE value is at least `7 = r(x_H, H(x_H)) = min_y r(h(y), H(h(y)))`
(any discount factor). -/
theorem cg_stokey_V_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r422 cg_C422, 7 ≤ v := by
  refine cg_V_lower hδ0 hδ1 cg_r422_abs_le ?_
  intro x y hxy
  rw [cg_C422_mem] at hxy
  subst hxy
  refine ⟨1, ?_⟩
  fin_cases x <;> norm_num [cg_r422]

/-- In Example 21.4.2 every SPE value is at most the Ramsey value `9.7` (any discount factor). -/
theorem cg_stokey_V_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r422 cg_C422, v ≤ 97 / 10 := by
  intro v hv
  refine (cg_V_subset_Icc (a := 0) hδ0 hδ1 cg_r422_abs_le ?_ hv).2
  rintro ⟨x, y⟩ (hxy : x = y)
  subst hxy
  fin_cases x <;> norm_num [cg_r422]

/-- Example 21.4.2 repeated with `δ = 0.9`: the SPE value set is `V = [7, 9.7]`. -/
theorem cg_stokey_V : cg_V (9 / 10) cg_r422 cg_C422 = Set.Icc 7 (97 / 10) := by
  ext v
  constructor
  · intro hv
    exact ⟨cg_stokey_V_ge (by norm_num) (by norm_num) v hv,
      cg_stokey_V_le (by norm_num) (by norm_num) v hv⟩
  · intro hv
    exact ⟨_, (cg_stokey_recursive_spe v hv).1, (cg_stokey_recursive_spe v hv).2⟩

/-- At `δ = 0.9`, `v_min = 7` and `v_max = 9.7` in Example 21.4.2. -/
theorem cg_stokey_vmin_vmax :
    IsLeast (cg_V (9 / 10) cg_r422 cg_C422) 7 ∧ IsGreatest (cg_V (9 / 10) cg_r422 cg_C422) (97 / 10)
    := by
  rw [cg_stokey_V]
  exact ⟨isLeast_Icc (by norm_num), isGreatest_Icc (by norm_num)⟩

/-- Miao, p. 767, in Example 21.4.2 at `δ = 0.9`: `v_min = r(h(y_H), H(h(y_H))) = r(x_H, y_M) = 7`;
the binding continuation `v₁ = 70/9` (from `0.1 · 0 + 0.9 v₁ = 7`) lies in `V`, so the recipe
`cg_vmin_eq` applies. -/
theorem cg_stokey_vmin_formula : IsLeast (cg_V (9 / 10) cg_r422 cg_C422) 7 := by
  refine cg_vmin_eq (xs := 0) (ys := 0) (v₁ := 70 / 9) (by norm_num) (by norm_num) cg_r422_abs_le
    rfl ?_ ?_ ?_ ?_
  · intro y'; fin_cases y' <;> norm_num [cg_r422]
  · intro x y hxy
    rw [cg_C422_mem] at hxy
    subst hxy
    refine ⟨1, ?_⟩
    fin_cases x <;> norm_num [cg_r422]
  · rw [cg_stokey_V]; constructor <;> norm_num
  · norm_num [cg_r422]

/-- The path `(x_H, y_H), (x_M, y_M), (x_M, y_M), …` of Example 21.4.4. -/
def cg_stokeyPath : ℕ → Fin 3 × Fin 3 := fun t => if t = 0 then (0, 0) else (1, 1)

theorem cg_stokeyPath_Ut {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ t, cg_Ut δ cg_r422 cg_stokeyPath (t + 1) = 8) ∧ cg_Ut δ cg_r422 cg_stokeyPath 0 = δ * 8 := by
  have h1 : ∀ t, cg_Ut δ cg_r422 cg_stokeyPath (t + 1) = 8 := by
    intro t
    unfold cg_Ut
    have : (fun s => cg_stokeyPath (t + 1 + s)) = fun _ => (1, 1) := by
      funext s; simp [cg_stokeyPath]
    rw [this, cg_pathValue_const hδ0 hδ1]
    norm_num [cg_r422]
  refine ⟨h1, ?_⟩
  rw [cg_Ut_succ hδ0 hδ1 cg_r422_abs_le, h1]
  norm_num [cg_stokeyPath, cg_r422]

/-- The path `q` of Example 21.4.4 is self-enforcing whenever the first-period deviation to `y_M`
does not pay, `(1 − δ) · 7 + δ · 8δ ≤ 8δ` (i.e. `δ ≥ 7/8`). -/
theorem cg_stokeyPath_selfEnforcing {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : (1 - δ) * 7 + δ * (δ * 8) ≤ δ * 8) :
    cg_SelfEnforcing δ cg_r422 cg_C422 cg_stokeyPath := by
  obtain ⟨h1, h0⟩ := cg_stokeyPath_Ut hδ0 hδ1
  have hd1 : 0 ≤ 1 - δ := by linarith
  rw [proposition_21_4_2 hδ0 hδ1 cg_r422_abs_le]
  intro t
  rcases t with _ | t
  · refine ⟨rfl, fun y' hy' => ?_⟩
    rw [h0]
    fin_cases y'
    · exact absurd rfl hy'
    · norm_num [cg_stokeyPath, cg_r422]; linarith
    · norm_num [cg_stokeyPath, cg_r422]; nlinarith
  · refine ⟨rfl, fun y' _ => ?_⟩
    rw [h0, h1]
    have hδ8 : δ * (δ * 8) ≤ 8 := by nlinarith
    fin_cases y' <;> norm_num [cg_stokeyPath, cg_r422] <;> nlinarith

/-- The Ramsey path `(x_L, y_L)` forever. -/
def cg_ramseyPath422 : ℕ → Fin 3 × Fin 3 := fun _ => (2, 2)

/-- **Example 21.4.4** (Miao, p. 769). At `δ = 0.9`: (a) the path
`q = (x_H, y_H), (x_M, y_M), …` is self-enforcing, with value `0.9 · 8 = 7.2`; (b) the strategy
"play the Ramsey outcome `(x_L, y_L)`; after any deviation from this or any ongoing path,
start `q`" is an SPE whose path is the Ramsey outcome forever. -/
theorem example_21_4_4 :
    cg_SelfEnforcing (9 / 10) cg_r422 cg_C422 cg_stokeyPath ∧
      cg_Ut (9 / 10) cg_r422 cg_stokeyPath 0 = 36 / 5 ∧
      cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0)
        ∧ cg_path (cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0) = cg_ramseyPath422
    := by
  have hse := cg_stokeyPath_selfEnforcing (δ := 9 / 10) (by norm_num) (by norm_num) (by norm_num)
  have h0 := (cg_stokeyPath_Ut (δ := 9 / 10) (by norm_num) (by norm_num)).2
  refine ⟨hse, by rw [h0]; norm_num, ?_⟩
  refine cg_follow_spe (by norm_num) (by norm_num) cg_r422_abs_le hse (fun _ => rfl) ?_
  intro t η hη
  rw [cg_selfEnf_U, h0]
  have hc : cg_Ut (9 / 10) cg_r422 cg_ramseyPath422 t = 97 / 10 := by
    unfold cg_Ut cg_ramseyPath422
    rw [cg_pathValue_const (by norm_num) (by norm_num)]
    norm_num [cg_r422]
  rw [hc]
  simp only [cg_ramseyPath422] at hη ⊢
  fin_cases η
  · norm_num [cg_r422]
  · norm_num [cg_r422]
  · exact absurd rfl hη

/-- **Example 21.4.4** (Miao, p. 769), the book's arithmetic (values multiplied by
`1/(1 − δ) = 10`): `0 + 0.9 · 8/(1 − 0.9) = 72`, `7 + 0.9 · 72 = 71.8 < 72`,
`30 + 0.9 · 72 = 94.8 < 97 = 9.7/(1 − 0.9)`; normalised, `7.2`, `7.18`, `9.48`, `9.7`. -/
theorem example_21_4_4_arith :
    (0 : ℝ) + 0.9 * 8 / (1 - 0.9) = 72 ∧ (7 : ℝ) + 0.9 * 72 = 71.8 ∧ (71.8 : ℝ) < 72 ∧
      (30 : ℝ) + 0.9 * 72 = 94.8 ∧ (9.7 : ℝ) / (1 - 0.9) = 97 ∧ (94.8 : ℝ) < 97 ∧
      (1 - 0.9 : ℝ) * 7 + 0.9 * 7.2 = 7.18 ∧ (1 - 0.9 : ℝ) * 30 + 0.9 * 7.2 = 9.48 := by
  norm_num

/-- **Exercise 21.5** (Miao, p. 771). At `δ = 0.88`: the path `q` of Example 21.4.4 is still
self-enforcing, but the strategy of Example 21.4.4 no longer supports the Ramsey outcome (the
deviation to `y_M` pays `0.12 · 30 + 0.88 · 7.04 = 9.7952 > 9.7`); indeed no SPE has the
repeated Ramsey outcome as its path (every SPE value is `≥ 7` and
`0.12 · 30 + 0.88 · 7 = 9.76 > 9.7`). -/
theorem ex_21_5 :
    cg_SelfEnforcing (22 / 25) cg_r422 cg_C422 cg_stokeyPath ∧
      ¬ cg_IsSPE (22 / 25) cg_r422 cg_C422
        (cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0) ∧
      ¬ ∃ σ, cg_IsSPE (22 / 25) cg_r422 cg_C422 σ ∧ cg_path σ = cg_ramseyPath422 := by
  have hδ0 : (0 : ℝ) ≤ 22 / 25 := by norm_num
  have hδ1 : (22 / 25 : ℝ) < 1 := by norm_num
  have hc : ∀ σ : CGProfile (Fin 3) (Fin 3), cg_path σ = cg_ramseyPath422 →
      cg_U (22 / 25) cg_r422 σ = 97 / 10 := by
    intro σ hσ
    unfold cg_U
    rw [hσ]
    unfold cg_ramseyPath422
    rw [cg_pathValue_const hδ0 hδ1]
    norm_num [cg_r422]
  refine ⟨cg_stokeyPath_selfEnforcing hδ0 hδ1 (by norm_num), fun hspe => ?_, ?_⟩
  · have hroot := (hspe.root hδ0 hδ1 cg_r422_abs_le).2 1
    have hpath := (cg_follow_path cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0 0)
    have e : cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0 [] = (2, 2) := rfl
    rw [e, cg_follow_cont_single] at hroot
    have hne : ((2, 1) : Fin 3 × Fin 3) ≠ cg_ramseyPath422 0 := by
      simp [cg_ramseyPath422]
    simp only [hne, ↓reduceIte] at hroot
    rw [cg_selfEnf_U, (cg_stokeyPath_Ut hδ0 hδ1).2, cg_follow_U] at hroot
    have hc' : cg_Ut (22 / 25) cg_r422 cg_ramseyPath422 0 = 97 / 10 := by
      unfold cg_Ut cg_ramseyPath422
      rw [cg_pathValue_const hδ0 hδ1]
      norm_num [cg_r422]
    rw [hc'] at hroot
    norm_num [cg_r422] at hroot
  · rintro ⟨σ, hσ, hpath⟩
    have hroot := (hσ.root hδ0 hδ1 cg_r422_abs_le).2 1
    have h0 : σ [] = (2, 2) := by
      have := congrFun hpath 0
      exact this
    have hmem : cg_U (22 / 25) cg_r422 (cg_cont σ [((σ []).1, 1)]) ∈
        cg_V (22 / 25) cg_r422 cg_C422 := ⟨_, hσ.cont hδ0 hδ1 cg_r422_abs_le _, rfl⟩
    have hge := cg_stokey_V_ge hδ0 hδ1 _ hmem
    rw [hc σ hpath] at hroot
    rw [h0] at hroot hge
    norm_num [cg_r422] at hroot
    linarith

/-- Theorem 21.4.1 needs boundedness: in Example 21.4.2 at `δ = 0.9`, `B(ℝ) = ℝ` (any value is
generated by `(x_M, y_M)` with a suitable reward and a severe enough punishment), yet
`ℝ ⊄ V`. So `V` is not the largest fixed point of `B`, only the largest bounded one. -/
theorem cg_theorem_21_4_1_unbounded :
    cg_B (9 / 10) cg_r422 cg_C422 Set.univ = Set.univ ∧
      ¬ (Set.univ : Set ℝ) ⊆ cg_V (9 / 10) cg_r422 cg_C422 := by
  refine ⟨Set.eq_univ_of_forall fun v => ?_, fun h => ?_⟩
  · refine ⟨1, 1, fun q => if q = (1, 1) then (v - 8 / 10) * 10 / 9
      else (v - 8 / 10) * 10 / 9 - 100, ⟨rfl, fun _ => trivial, fun y' => ?_⟩, ?_⟩
    · fin_cases y' <;> norm_num [cg_r422] <;> linarith
    · norm_num [cg_r422]
  · have := cg_stokey_V_le (δ := 9 / 10) (by norm_num) (by norm_num) 10 (h trivial)
    norm_num at this

/-- Proposition 21.4.1 as printed (without `(x_t, y_t) ∈ C`) is false: in Example 21.4.2 at
`δ = 0.9`, where `v_min = 7`, the path `(x_L, y_M)` forever satisfies
`U_t ≥ (1 − δ) r(x_t, y') + δ v_min` for all `t`, `y'`, but it is not an SPE path. -/
theorem cg_proposition_21_4_1_counterexample :
    IsLeast (cg_V (9 / 10) cg_r422 cg_C422) 7 ∧
      (∀ t y', (1 - 9 / 10) * cg_r422 ((fun _ => ((2 : Fin 3), (1 : Fin 3))) t : Fin 3 × Fin 3).1 y'
        + 9 / 10 * 7 ≤ cg_Ut (9 / 10) cg_r422 (fun _ => ((2 : Fin 3), (1 : Fin 3))) t) ∧
      ¬ ∃ σ, cg_IsSPE (9 / 10) cg_r422 cg_C422 σ ∧
        cg_path σ = fun _ => ((2 : Fin 3), (1 : Fin 3)) := by
  refine ⟨cg_stokey_vmin_vmax.1, fun t y' => ?_, ?_⟩
  · have : cg_Ut (9 / 10) cg_r422 (fun _ => ((2 : Fin 3), (1 : Fin 3))) t = 30 := by
      unfold cg_Ut
      rw [cg_pathValue_const (by norm_num) (by norm_num)]
      norm_num [cg_r422]
    rw [this]
    fin_cases y' <;> norm_num [cg_r422]
  · rintro ⟨σ, hσ, hpath⟩
    have := hσ.path_mem (by norm_num) (by norm_num) cg_r422_abs_le 0
    rw [hpath] at this
    exact absurd (cg_C422_mem.1 this) (by decide)

/-- The household rule of the recursive strategy in `cg_definition_21_4_5_counterexample`. -/
noncomputable def cg_cexZh (s : ℝ) : Fin 3 := if s = 8 then 1 else 0

/-- The state map of the recursive strategy in `cg_definition_21_4_5_counterexample`: `8` after a
household outcome `x_M`, `0` otherwise. -/
noncomputable def cg_cexV (_s : ℝ) (x _y : Fin 3) : ℝ := if x = 1 then 8 else 0

/-- The SPE characterisation of recursive strategies (Miao, p. 770) as printed is false: in
Example 21.4.2 at `δ = 0.9`, the recursive strategy with `zʰ(8) = x_M`, `zʰ(v) = x_H` otherwise,
`zᵍ ≡ y_M`, `V(v, x, y) = 8` if `x = x_M` and `0` otherwise, satisfies `v = 8 ∈ V` and
(i)–(iii) at `v`, but it is not an SPE: after the history `(x_H, y_M)` the state is `0` and the
prescribed `(x_H, y_M)` is not a competitive equilibrium. -/
theorem cg_definition_21_4_5_counterexample :
    (8 : ℝ) ∈ cg_V (9 / 10) cg_r422 cg_C422 ∧ (cg_cexZh 8, (1 : Fin 3)) ∈ cg_C422 ∧
      (∀ y, cg_cexV 8 (cg_cexZh 8) y ∈ cg_V (9 / 10) cg_r422 cg_C422) ∧
      (8 : ℝ) = (1 - 9 / 10) * cg_r422 (cg_cexZh 8) 1 + 9 / 10 * cg_cexV 8 (cg_cexZh 8) 1 ∧
      (∀ y, (1 - 9 / 10) * cg_r422 (cg_cexZh 8) y + 9 / 10 * cg_cexV 8 (cg_cexZh 8) y ≤ 8) ∧
      ¬ cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat cg_cexZh (fun _ => 1) cg_cexV 8) := by
  have h8 : cg_cexZh 8 = 1 := by simp [cg_cexZh]
  have h8V : (8 : ℝ) ∈ cg_V (9 / 10) cg_r422 cg_C422 := by
    rw [cg_stokey_V]; constructor <;> norm_num
  refine ⟨h8V, by rw [h8]; rfl, fun y => ?_, ?_, fun y => ?_, fun hspe => ?_⟩
  · rw [h8]; simpa [cg_cexV] using h8V
  · rw [h8]; norm_num [cg_cexV, cg_r422]
  · rw [h8]; fin_cases y <;> norm_num [cg_cexV, cg_r422]
  · have := (hspe [((0 : Fin 3), (1 : Fin 3))]).1
    have e : cg_recStrat cg_cexZh (fun _ => 1) cg_cexV 8 [((0 : Fin 3), (1 : Fin 3))] =
        ((0 : Fin 3), (1 : Fin 3)) := by
      simp [cg_recStrat, cg_recState, cg_cexV, cg_cexZh]
    rw [e] at this
    exact absurd (cg_C422_mem.1 this) (by decide)

/-- Example 21.4.5 as printed is false: in Example 21.4.2 at `δ = 0.9`, the Ramsey value
`v^b = 9.7` exceeds the Nash value `v^N = 8`, but the trigger strategy supporting
`(x_L, y_L)` is not an SPE (deviating to `y_M` pays `0.1 · 30 + 0.9 · 8 = 10.2 > 9.7`). -/
theorem cg_example_21_4_5_counterexample :
    cg_r422 1 1 < cg_r422 2 2 ∧ cg_IsNash cg_C422 cg_r422 1 1 ∧
      ¬ cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat (cg_trigZh (cg_r422 2 2) 2 1)
        (cg_trigZg (cg_r422 2 2) 2 1) (cg_trigV (cg_r422 2 2) (cg_r422 1 1) 2 2) (cg_r422 2 2))
    := by
  have hδ0 : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hδ1 : (9 / 10 : ℝ) < 1 := by norm_num
  refine ⟨by norm_num [cg_r422], (example_21_4_2).2.2.1, fun hspe => ?_⟩
  have hval := cg_trigger_value (r := cg_r422) hδ0 hδ1 cg_r422_abs_le 2 1 2 1
  have hroot := (hspe.root hδ0 hδ1 cg_r422_abs_le).2 1
  have e : cg_recStrat (cg_trigZh (cg_r422 2 2) 2 1) (cg_trigZg (cg_r422 2 2) 2 1)
      (cg_trigV (cg_r422 2 2) (cg_r422 1 1) 2 2) (cg_r422 2 2) [] = ((2 : Fin 3), (2 : Fin 3)) := by
    simp [cg_recStrat, cg_recState, cg_trigZh, cg_trigZg]
  rw [e, cg_recStrat_cont_single] at hroot
  have hV : cg_trigV (cg_r422 2 2) (cg_r422 1 1) (2 : Fin 3) (2 : Fin 3) (cg_r422 2 2) 2 1 =
      cg_r422 1 1 := by
    simp [cg_trigV]
  dsimp only at hroot
  rw [hV, hval _ (Or.inr rfl), hval _ (Or.inl rfl)] at hroot
  norm_num [cg_r422] at hroot

/-- Example 21.4.6 as printed is incomplete: in Example 21.4.2 at `δ = 0.9`, with the stick
`(x_H, y_H)` and the carrot `(x_L, y_L)`, `ṽ = 0.1 · 0 + 0.9 · 9.7 = 8.73` satisfies the book's
condition `ṽ ≥ (1 − δ) r(x*, y') + δṽ` for all `y'`, but the stick-and-carrot strategy is not
an SPE: in the carrot phase deviating to `y_M` pays `0.1 · 30 + 0.9 · 8.73 = 10.857 > 9.7`. -/
theorem cg_example_21_4_6_counterexample :
    (∀ y', (1 - 9 / 10) * cg_r422 0 y' + 9 / 10 * ((1 - 9 / 10) * cg_r422 0 0 + 9 / 10 *
      cg_r422 2 2) ≤ (1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2) ∧
      ¬ cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat (cg_scZh (cg_r422 2 2) 2 0)
        (cg_scZg (cg_r422 2 2) 2 0)
        (cg_scV (cg_r422 2 2) ((1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2) 2 0 2 0)
        ((1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2)) := by
  have hδ0 : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hδ1 : (9 / 10 : ℝ) < 1 := by norm_num
  refine ⟨fun y' => by fin_cases y' <;> norm_num [cg_r422], fun hspe => ?_⟩
  have hval := cg_stickCarrot_value (r := cg_r422) hδ0 hδ1 cg_r422_abs_le 2 0 2 0
  set vR := cg_r422 2 2 with hvR
  set vt := (1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2 with hvt
  have hne : vt ≠ vR := by rw [hvt, hvR]; norm_num [cg_r422]
  have hc := hspe.cont hδ0 hδ1 cg_r422_abs_le [((0 : Fin 3), (0 : Fin 3))]
  have hV1 : cg_cont (cg_recStrat (cg_scZh vR 2 0) (cg_scZg vR 2 0) (cg_scV vR vt 2 0 2 0) vt)
      [((0 : Fin 3), (0 : Fin 3))] =
      cg_recStrat (cg_scZh vR 2 0) (cg_scZg vR 2 0) (cg_scV vR vt 2 0 2 0) vR := by
    rw [cg_recStrat_cont_single]
    congr 1
    simp [cg_scV, cg_scZh, cg_scZg, hne]
  rw [hV1] at hc
  have hroot := (hc.root hδ0 hδ1 cg_r422_abs_le).2 1
  have e : cg_recStrat (cg_scZh vR 2 0) (cg_scZg vR 2 0) (cg_scV vR vt 2 0 2 0) vR [] =
      ((2 : Fin 3), (2 : Fin 3)) := by
    simp [cg_recStrat, cg_recState, cg_scZh, cg_scZg]
  rw [e, cg_recStrat_cont_single] at hroot
  have hV2 : cg_scV vR vt (2 : Fin 3) 0 (2 : Fin 3) 0 vR 2 1 = vt := by
    simp [cg_scV, cg_scZh, cg_scZg]
  dsimp only at hroot
  rw [hV2, hval _ (Or.inr rfl), hval _ (Or.inl rfl), hvt, hvR] at hroot
  norm_num [cg_r422] at hroot

/-- The payoff of the two-action game used in `cg_proposition_21_4_2_counterexample`:
`r(T, T) = 1`, `r(F, F) = 0`, `r(x, y) = −10` off the diagonal. -/
noncomputable def cg_rBool (x y : Bool) : ℝ := if x = y then (if x then 1 else 0) else -10

/-- The competitive equilibria `(T, T)`, `(F, F)` of the two-action game. -/
def cg_CBool : Set (Bool × Bool) := {q | q.1 = q.2}

/-- The path `(T, T), (F, F), (F, F), …` of the two-action game. -/
def cg_pBool : ℕ → Bool × Bool := fun t => if t = 0 then (true, true) else (false, false)

theorem cg_rBool_abs_le (x y : Bool) : |cg_rBool x y| ≤ 10 := by
  cases x <;> cases y <;> norm_num [cg_rBool, abs_le]

/-- Proposition 21.4.2 as printed (`U_t ≥ (1 − δ) r(x_t, y') + δ U_1` for all `y'`, including
`y' = y_t`) is false: in the two-action game with `δ = 1/2`, the path
`(T, T), (F, F), (F, F), …` is self-enforcing (`U_1 = 1/2`, `U_t = 0` for `t ≥ 2`, and every
deviation earns `−10`), but at `t = 2`, `y' = y_2 = F` the printed inequality reads
`0 ≥ 1/2 · 0 + 1/2 · 1/2`. -/
theorem cg_proposition_21_4_2_counterexample :
    cg_SelfEnforcing (1 / 2) cg_rBool cg_CBool cg_pBool ∧
      ¬ ∀ t y', (1 - 1 / 2) * cg_rBool (cg_pBool t).1 y' + 1 / 2 * cg_Ut (1 / 2) cg_rBool cg_pBool 0
        ≤ cg_Ut (1 / 2) cg_rBool cg_pBool t := by
  have hδ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hδ1 : (1 / 2 : ℝ) < 1 := by norm_num
  have h1 : ∀ t, cg_Ut (1 / 2) cg_rBool cg_pBool (t + 1) = 0 := by
    intro t
    unfold cg_Ut
    have : (fun s => cg_pBool (t + 1 + s)) = fun _ => (false, false) := by
      funext s; simp [cg_pBool]
    rw [this, cg_pathValue_const hδ0 hδ1]
    simp [cg_rBool]
  have h0 : cg_Ut (1 / 2) cg_rBool cg_pBool 0 = 1 / 2 := by
    rw [cg_Ut_succ hδ0 hδ1 cg_rBool_abs_le, h1]
    norm_num [cg_pBool, cg_rBool]
  refine ⟨?_, fun h => ?_⟩
  · rw [proposition_21_4_2 hδ0 hδ1 cg_rBool_abs_le]
    intro t
    rcases t with _ | t
    · refine ⟨rfl, fun y' hy' => ?_⟩
      rw [h0]
      cases y'
      · norm_num [cg_pBool, cg_rBool]
      · simp [cg_pBool] at hy'
    · refine ⟨rfl, fun y' hy' => ?_⟩
      rw [h0, h1]
      cases y'
      · simp [cg_pBool] at hy'
      · norm_num [cg_pBool, cg_rBool]
  · have := h 1 false
    rw [h0, h1 0] at this
    norm_num [cg_pBool, cg_rBool] at this

end Miao.DynamicGames
