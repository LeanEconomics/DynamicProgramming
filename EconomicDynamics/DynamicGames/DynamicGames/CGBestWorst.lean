/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.CGValueSet

/-!
# The best and the worst SPE values

Miao, §21.4.4, pp. 766–769 (after Abreu 1988 and Stokey 1991), and Exercise 21.4.

* `cg_follow p τ`: follow the path `p`; after the first deviation from it (by anyone) switch to
  the profile `τ`, started afresh. `cg_follow_spe`: if `τ` is an SPE and no one-period
  government deviation from `p` beats `(1 − δ) r(x_t, y') + δ Uᵍ(τ)`, this is an SPE with
  path `p`.
* `proposition_21_4_1`, corrected: with `v_min` the least SPE value, `p` is an SPE path iff for
  all `t`, `(x_t, y_t) ∈ C` and `U_t ≥ (1 − δ) r(x_t, y') + δ v_min` for all `y'`. The book omits
  `(x_t, y_t) ∈ C`, without which the claim is false (`cg_proposition_21_4_1_counterexample`).
* `cg_selfEnf p`: the self-enforcing strategy (restart `p` after any deviation from the ongoing
  path); `cg_SelfEnforcing`. `proposition_21_4_2`, corrected: `p` is self-enforcing iff for all
  `t`, `(x_t, y_t) ∈ C` and `U_t ≥ (1 − δ) r(x_t, y') + δ U_1` for all `y' ≠ y_t`. As printed
  (all `y'`, no `C`) it is false (`cg_proposition_21_4_2_counterexample`): at `y' = y_t` the
  condition asks `U_{t+1} ≥ U_1`, which a self-enforcing path need not satisfy.
* `proposition_21_4_3`: the path of a worst SPE is self-enforcing. `ex_21_4` collects the three.
* The computation of `v_min` and `v_max` on pp. 767–768: `cg_vmin_eq` (if
  `c = max_{y'} r(x*, y')` at a competitive `(x*, y*)`, `c` is the lower bound of `cg_V_lower`,
  and the binding continuation `v₁` is in `V`, then `c = v_min`), `cg_v1_formula`, `cg_vmax`
  (the best SPE is self-rewarding: `v_max = max r(x, y)` over competitive `(x, y)` with
  `r(x, y) ≥ (1 − δ) r(x, y') + δ v_min`), and `cg_four_equations` (the four-equation system with
  `v₁ = v_max`: its solutions are SPE values).
* `cg_example_21_4_6_selfEnforcing`: the stick-and-carrot path `(x*, y*), (x^R, y^R), …` is
  self-enforcing (Miao, p. 771, "This equilibrium is self-enforcing").
-/

namespace Miao.DynamicGames

variable {X Y : Type*}

open Classical in
/-- Follow the path `p` from index `t`; after the first deviation from it switch to `τ`. -/
noncomputable def cg_follow (p : ℕ → X × Y) (τ : CGProfile X Y) : ℕ → CGProfile X Y
  | t, [] => p t
  | t, q :: h => if q = p t then cg_follow p τ (t + 1) h else τ h

open Classical in
theorem cg_follow_cont_single (p : ℕ → X × Y) (τ : CGProfile X Y) (t : ℕ) (q : X × Y) :
    cg_cont (cg_follow p τ t) [q] = if q = p t then cg_follow p τ (t + 1) else τ := by
  funext h
  by_cases hq : q = p t
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_follow]
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_follow, hq]

theorem cg_follow_cont (p : ℕ → X × Y) (τ : CGProfile X Y) (h : List (X × Y)) :
    ∀ t, (∃ t', cg_cont (cg_follow p τ t) h = cg_follow p τ t') ∨
      ∃ h', cg_cont (cg_follow p τ t) h = cg_cont τ h' := by
  induction h with
  | nil => exact fun t => Or.inl ⟨t, rfl⟩
  | cons q h ih =>
    intro t
    have e : cg_cont (cg_follow p τ t) (q :: h) = cg_cont (cg_cont (cg_follow p τ t) [q]) h := by
      rw [cg_cont_cont]; rfl
    rw [e, cg_follow_cont_single]
    by_cases hq : q = p t
    · simp only [hq, ↓reduceIte]
      exact ih (t + 1)
    · simp only [hq, ↓reduceIte]
      exact Or.inr ⟨h, rfl⟩

theorem cg_follow_path (p : ℕ → X × Y) (τ : CGProfile X Y) (n : ℕ) :
    ∀ t, cg_path (cg_follow p τ t) n = p (t + n) := by
  induction n with
  | zero => exact fun t => rfl
  | succ n ih =>
    intro t
    have e : cg_path (cg_follow p τ t) (n + 1) =
        cg_path (cg_cont (cg_follow p τ t) [p t]) n := rfl
    rw [e, cg_follow_cont_single]
    simp only [↓reduceIte]
    rw [ih, show t + 1 + n = t + (n + 1) by omega]

theorem cg_follow_U (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) (τ : CGProfile X Y) (t : ℕ) :
    cg_U δ r (cg_follow p τ t) = cg_Ut δ r p t := by
  unfold cg_U cg_Ut
  congr 1
  funext n
  exact cg_follow_path p τ n t

/-- Following a path with an SPE punishment: if `τ` is an SPE, `p` is competitive, and for all
`t` and `η ≠ y_t`, `(1 − δ) r(x_t, η) + δ Uᵍ(τ) ≤ U_t(p)`, then `cg_follow p τ 0` is an SPE with
path `p`. -/
theorem cg_follow_spe {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {p : ℕ → X × Y} {τ : CGProfile X Y} (hτ : cg_IsSPE δ r C τ)
    (hp : ∀ t, p t ∈ C)
    (hdev : ∀ t η, η ≠ (p t).2 → (1 - δ) * r (p t).1 η + δ * cg_U δ r τ ≤ cg_Ut δ r p t) :
    cg_IsSPE δ r C (cg_follow p τ 0) ∧ cg_path (cg_follow p τ 0) = p := by
  refine ⟨?_, funext fun n => by rw [cg_follow_path, zero_add]⟩
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  intro h
  rcases cg_follow_cont p τ h 0 with ⟨t, ht⟩ | ⟨h', ht⟩
  · rw [ht]
    have e : cg_follow p τ t [] = p t := rfl
    refine ⟨by rw [e]; exact hp t, fun η => ?_⟩
    rw [e, cg_follow_cont_single, cg_follow_U]
    by_cases hη : η = (p t).2
    · have hq : ((p t).1, η) = p t := by rw [hη]
      simp only [hq, ↓reduceIte]
      rw [cg_follow_U, cg_Ut_succ hδ0 hδ1 hM p t, hη]
    · have hq : ((p t).1, η) ≠ p t := by
        intro hq; apply hη; rw [← hq]
      simp only [hq, ↓reduceIte]
      exact hdev t η hη
  · rw [ht]
    exact (cg_isSPE_iff_oneShot hδ0 hδ1 hM τ).1 hτ h'

/-- **Proposition 21.4.1** (Miao, p. 766), corrected. Let `v_min` be the least SPE value. A path
`(x, y)` is an SPE path iff for all `t`, `(x_t, y_t)` is a competitive equilibrium and
`U_t(x, y) ≥ (1 − δ) r(x_t, y') + δ v_min` for all `y' ∈ Y`. (The book omits `(x_t, y_t) ∈ C`;
see `cg_proposition_21_4_1_counterexample`.) -/
theorem proposition_21_4_1 {δ M vmin : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin)
    (p : ℕ → X × Y) :
    (∃ σ, cg_IsSPE δ r C σ ∧ cg_path σ = p) ↔
      ∀ t, p t ∈ C ∧ ∀ y', (1 - δ) * r (p t).1 y' + δ * vmin ≤ cg_Ut δ r p t := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩ t
    refine ⟨hσ.path_mem hδ0 hδ1 hM t, fun y' => ?_⟩
    set ρ := cg_cont σ (cg_prefix (cg_path σ) t)
    have hρ : cg_IsSPE δ r C ρ := hσ.cont hδ0 hδ1 hM _
    have hpath := cg_path_cont_prefix σ t
    have h0 : ρ [] = cg_path σ t := by
      have := congrFun hpath 0
      rw [Nat.add_zero] at this
      exact this
    have hU : cg_U δ r ρ = cg_Ut δ r (cg_path σ) t := by
      unfold cg_U cg_Ut
      rw [hpath]
    have hroot := (hρ.root hδ0 hδ1 hM).2 y'
    rw [h0, hU] at hroot
    have hmem : cg_U δ r (cg_cont ρ [((cg_path σ t).1, y')]) ∈ cg_V δ r C :=
      ⟨_, hρ.cont hδ0 hδ1 hM _, rfl⟩
    have := mul_le_mul_of_nonneg_left (hmin.2 hmem) hδ0
    linarith
  · intro hp
    obtain ⟨τ, hτ, hτv⟩ := hmin.1
    refine ⟨cg_follow p τ 0, cg_follow_spe hδ0 hδ1 hM hτ (fun t => (hp t).1) ?_⟩
    intro t η _
    rw [hτv]
    exact (hp t).2 η

open Classical in
/-- The self-enforcing strategy of a path `p` (Miao, p. 767), from index `t`: play `p`; if anyone
deviates from the ongoing path, restart `p` from its beginning. -/
noncomputable def cg_selfEnf (p : ℕ → X × Y) : ℕ → CGProfile X Y
  | t, [] => p t
  | t, q :: h => if q = p t then cg_selfEnf p (t + 1) h else cg_selfEnf p 0 h

/-- A path is self-enforcing if its self-enforcing strategy is an SPE (Miao, p. 767). -/
def cg_SelfEnforcing (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (p : ℕ → X × Y) : Prop :=
  cg_IsSPE δ r C (cg_selfEnf p 0)

open Classical in
theorem cg_selfEnf_cont_single (p : ℕ → X × Y) (t : ℕ) (q : X × Y) :
    cg_cont (cg_selfEnf p t) [q] = if q = p t then cg_selfEnf p (t + 1) else cg_selfEnf p 0 := by
  funext h
  by_cases hq : q = p t
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_selfEnf]
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_selfEnf, hq]

theorem cg_selfEnf_cont (p : ℕ → X × Y) (h : List (X × Y)) :
    ∀ t, ∃ t', cg_cont (cg_selfEnf p t) h = cg_selfEnf p t' := by
  induction h with
  | nil => exact fun t => ⟨t, rfl⟩
  | cons q h ih =>
    intro t
    have e : cg_cont (cg_selfEnf p t) (q :: h) = cg_cont (cg_cont (cg_selfEnf p t) [q]) h := by
      rw [cg_cont_cont]; rfl
    rw [e, cg_selfEnf_cont_single]
    by_cases hq : q = p t
    · simp only [hq, ↓reduceIte]
      exact ih (t + 1)
    · simp only [hq, ↓reduceIte]
      exact ih 0

theorem cg_selfEnf_path (p : ℕ → X × Y) (n : ℕ) :
    ∀ t, cg_path (cg_selfEnf p t) n = p (t + n) := by
  induction n with
  | zero => exact fun t => rfl
  | succ n ih =>
    intro t
    have e : cg_path (cg_selfEnf p t) (n + 1) = cg_path (cg_cont (cg_selfEnf p t) [p t]) n := rfl
    rw [e, cg_selfEnf_cont_single]
    simp only [↓reduceIte]
    rw [ih, show t + 1 + n = t + (n + 1) by omega]

theorem cg_selfEnf_U (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) (t : ℕ) :
    cg_U δ r (cg_selfEnf p t) = cg_Ut δ r p t := by
  unfold cg_U cg_Ut
  congr 1
  funext n
  exact cg_selfEnf_path p n t

theorem cg_selfEnf_prefix (p : ℕ → X × Y) (t : ℕ) :
    cg_cont (cg_selfEnf p 0) (cg_prefix p t) = cg_selfEnf p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [cg_prefix_succ, ← cg_cont_cont, ih, cg_selfEnf_cont_single]
    simp

/-- The path of the self-enforcing strategy of `p` is `p`. -/
theorem cg_selfEnf_path_zero (p : ℕ → X × Y) : cg_path (cg_selfEnf p 0) = p :=
  funext fun n => by rw [cg_selfEnf_path, zero_add]

/-- **Proposition 21.4.2** (Miao, p. 767), corrected. The path `(x, y)` is a self-enforcing SPE
path iff for all `t`, `(x_t, y_t) ∈ C` and `U_t(x, y) ≥ (1 − δ) r(x_t, y') + δ U_1(x, y)` for all
`y' ≠ y_t`. (The book quantifies over all `y'` and omits `(x_t, y_t) ∈ C`; see
`cg_proposition_21_4_2_counterexample`.) -/
theorem proposition_21_4_2 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) :
    cg_SelfEnforcing δ r C p ↔ ∀ t, p t ∈ C ∧
      ∀ y', y' ≠ (p t).2 → (1 - δ) * r (p t).1 y' + δ * cg_Ut δ r p 0 ≤ cg_Ut δ r p t := by
  unfold cg_SelfEnforcing
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  constructor
  · intro hO t
    have h := hO (cg_prefix p t)
    rw [cg_selfEnf_prefix] at h
    refine ⟨h.1, fun y' hy' => ?_⟩
    have := h.2 y'
    have e : cg_selfEnf p t [] = p t := rfl
    have hq : ((p t).1, y') ≠ p t := by
      intro hq; apply hy'; rw [← hq]
    rw [e, cg_selfEnf_cont_single] at this
    simp only [hq, ↓reduceIte] at this
    rwa [cg_selfEnf_U, cg_selfEnf_U] at this
  · intro hp h
    obtain ⟨t, ht⟩ := cg_selfEnf_cont p h 0
    rw [ht]
    have e : cg_selfEnf p t [] = p t := rfl
    refine ⟨by rw [e]; exact (hp t).1, fun η => ?_⟩
    rw [e, cg_selfEnf_cont_single, cg_selfEnf_U]
    by_cases hη : η = (p t).2
    · have hq : ((p t).1, η) = p t := by rw [hη]
      simp only [hq, ↓reduceIte]
      rw [cg_selfEnf_U, cg_Ut_succ hδ0 hδ1 hM p t, hη]
    · have hq : ((p t).1, η) ≠ p t := by
        intro hq; apply hη; rw [← hq]
      simp only [hq, ↓reduceIte]
      rw [cg_selfEnf_U]
      exact (hp t).2 η hη

/-- **Proposition 21.4.3** (Miao, p. 767). The path of an SPE that attains the worst value
`v_min` is self-enforcing. -/
theorem proposition_21_4_3 {δ M vmin : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin)
    {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ) (hv : cg_U δ r σ = vmin) :
    cg_SelfEnforcing δ r C (cg_path σ) := by
  have h1 := (proposition_21_4_1 hδ0 hδ1 hM hmin (cg_path σ)).1 ⟨σ, hσ, rfl⟩
  have h0 : cg_Ut δ r (cg_path σ) 0 = vmin := by rw [cg_Ut_zero]; exact hv
  rw [proposition_21_4_2 hδ0 hδ1 hM]
  intro t
  refine ⟨(h1 t).1, fun y' _ => ?_⟩
  rw [h0]
  exact (h1 t).2 y'

/-- **Exercise 21.4** (Miao, p. 771): the three propositions of §21.4.4 (in their corrected
form). -/
theorem ex_21_4 {δ M vmin : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin) :
    (∀ p : ℕ → X × Y, (∃ σ, cg_IsSPE δ r C σ ∧ cg_path σ = p) ↔
      ∀ t, p t ∈ C ∧ ∀ y', (1 - δ) * r (p t).1 y' + δ * vmin ≤ cg_Ut δ r p t) ∧
    (∀ p : ℕ → X × Y, cg_SelfEnforcing δ r C p ↔ ∀ t, p t ∈ C ∧
      ∀ y', y' ≠ (p t).2 → (1 - δ) * r (p t).1 y' + δ * cg_Ut δ r p 0 ≤ cg_Ut δ r p t) ∧
    (∀ σ, cg_IsSPE δ r C σ → cg_U δ r σ = vmin → cg_SelfEnforcing δ r C (cg_path σ)) :=
  ⟨proposition_21_4_1 hδ0 hδ1 hM hmin, proposition_21_4_2 hδ0 hδ1 hM,
    fun _ hσ hv => proposition_21_4_3 hδ0 hδ1 hM hmin hσ hv⟩

/-- Miao, p. 767: computing `v_min`. If `(x*, y*)` is competitive, `c ≥ r(x*, y')` for all `y'`
(`c = r(x*, H(x*))`), every competitive `(x, y)` has a deviation `y'` with `r(x, y') ≥ c`
(`c = min_y r(h(y), H(h(y)))`), and the continuation `v₁` that makes the constraint bind,
`(1 − δ) r(x*, y*) + δ v₁ = c`, is an SPE value, then `c` is the least SPE value. -/
theorem cg_vmin_eq {δ M c v₁ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xs : X} {ys : Y} (hs : (xs, ys) ∈ C)
    (hcle : ∀ y', r xs y' ≤ c) (hlow : ∀ x y, (x, y) ∈ C → ∃ y', c ≤ r x y')
    (hv1 : v₁ ∈ cg_V δ r C) (heq : (1 - δ) * r xs ys + δ * v₁ = c) :
    IsLeast (cg_V δ r C) c := by
  classical
  refine ⟨cg_mem_V_of_mem_B_insert hδ0 hδ1 hM ?_, cg_V_lower hδ0 hδ1 hM hlow⟩
  refine ⟨xs, ys, fun q => if q = (xs, ys) then v₁ else c,
    ⟨hs, fun q => ?_, fun y' => ?_⟩, ?_⟩
  · dsimp only
    split_ifs
    · exact Or.inr hv1
    · exact Or.inl rfl
  · by_cases hy : y' = ys
    · subst hy; exact le_rfl
    · have hq : ((xs, y') : X × Y) ≠ (xs, ys) := by simp [hy]
      simp only [hq, ↓reduceIte]
      have := mul_le_mul_of_nonneg_left (hcle y') (by linarith : (0 : ℝ) ≤ 1 - δ)
      linarith
  · simp only [↓reduceIte]
    exact heq.symm

/-- Miao, p. 768: solving `(1 − δ) r(h(y_min), y_min) + δ v₁ = (1 − δ) r(h(y_min), H(h(y_min)))
+ δ v_min` for `v₁` gives `v₁ = ((1 − δ)/δ)[r(h, H(h)) − r(h, y_min)] + v_min`. -/
theorem cg_v1_formula {δ rmin rdev v₁ vmin : ℝ} (hδ : δ ≠ 0) :
    (1 - δ) * rmin + δ * v₁ = (1 - δ) * rdev + δ * vmin ↔
      v₁ = (1 - δ) / δ * (rdev - rmin) + vmin := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Miao, pp. 767–768: the best SPE is self-rewarding. Every competitive `(x, y)` with
`r(x, y) ≥ (1 − δ) r(x, y') + δ v_min` for all `y'` gives an SPE value `r(x, y)` (its
infinite repetition, with the worst SPE as punishment), and a greatest SPE value `v_max`, when
it exists, is the largest such `r(x, y)`. -/
theorem cg_vmax {δ M vmin vmax : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin) :
    {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧ v = r x y} ⊆
        cg_V δ r C ∧
      (IsGreatest (cg_V δ r C) vmax → IsGreatest
        {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧ v = r x y}
        vmax) := by
  classical
  have hF : {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧
      v = r x y} ⊆ cg_V δ r C := by
    rintro _ ⟨x, y, hC, hIC, rfl⟩
    refine cg_mem_V_of_mem_B_insert hδ0 hδ1 hM ⟨x, y, fun q => if q = (x, y) then r x y
      else vmin, ⟨hC, fun q => ?_, fun y' => ?_⟩, ?_⟩
    · dsimp only
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr hmin.1
    · by_cases hy : y' = y
      · subst hy; exact le_rfl
      · have hq : ((x, y') : X × Y) ≠ (x, y) := by simp [hy]
        simp only [hq, ↓reduceIte]
        have := hIC y'
        linarith
    · simp only [↓reduceIte]
      ring
  refine ⟨hF, fun hmax => ⟨?_, fun v hv => hmax.2 (hF hv)⟩⟩
  obtain ⟨σ, hσ, hσv⟩ := hmax.1
  have hrec := cg_U_rec hδ0 hδ1 hM σ
  have hcont : cg_U δ r (cg_cont σ [σ []]) ≤ vmax :=
    hmax.2 ⟨_, hσ.cont hδ0 hδ1 hM _, rfl⟩
  have h1 : 0 < 1 - δ := by linarith
  have hge : vmax ≤ r (σ []).1 (σ []).2 := by
    have := mul_le_mul_of_nonneg_left hcont hδ0
    nlinarith
  have hfeas : ∀ y', (1 - δ) * r (σ []).1 y' + δ * vmin ≤ r (σ []).1 (σ []).2 := by
    intro y'
    have hroot := (hσ.root hδ0 hδ1 hM).2 y'
    have hmem : cg_U δ r (cg_cont σ [((σ []).1, y')]) ∈ cg_V δ r C :=
      ⟨_, hσ.cont hδ0 hδ1 hM _, rfl⟩
    have := mul_le_mul_of_nonneg_left (hmin.2 hmem) hδ0
    linarith
  have hmemF : r (σ []).1 (σ []).2 ∈
      {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧ v = r x y} :=
    ⟨_, _, (hσ []).1, hfeas, rfl⟩
  have hle : r (σ []).1 (σ []).2 ≤ vmax := hmax.2 (hF hmemF)
  have : r (σ []).1 (σ []).2 = vmax := le_antisymm hle hge
  rw [← this]
  exact hmemF

/-- Miao, p. 768: the four equations for `v_max, v_min, y_max, y_min` when the worst SPE is
rewarded with `v₁ = v_max`. If `(x_min, y_min)`, `(x_max, y_max)` are competitive,
`v_min ≥ r(x_min, y')` for all `y'` (`v_min = r(h(y_min), H(h(y_min)))`),
`v_max = ((1 − δ)/δ)[v_min − r(x_min, y_min)] + v_min`, `v_max = r(x_max, y_max)` and
`r(x_max, y_max) ≥ (1 − δ) r(x_max, y') + δ v_min` for all `y'` (the fourth equation with `H`
the best response), then `v_min` and `v_max` are SPE values. -/
theorem cg_four_equations {δ M vmin vmax : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xmin xmax : X} {ymin ymax : Y}
    (hCmin : (xmin, ymin) ∈ C) (hCmax : (xmax, ymax) ∈ C) (hH : ∀ y', r xmin y' ≤ vmin)
    (h2 : vmax = (1 - δ) / δ * (vmin - r xmin ymin) + vmin) (h3 : vmax = r xmax ymax)
    (h4 : ∀ y', (1 - δ) * r xmax y' + δ * vmin ≤ r xmax ymax) :
    vmin ∈ cg_V δ r C ∧ vmax ∈ cg_V δ r C := by
  classical
  have hδ : δ ≠ 0 := hδ0.ne'
  have hv : (1 - δ) * r xmin ymin + δ * vmax = vmin := by
    rw [h2]; field_simp; ring
  set W : Set ℝ := {vmin, vmax}
  have hWb : Bornology.IsBounded W := (Set.finite_singleton vmax).insert vmin |>.isBounded
  have hSG : cg_SelfGenerating δ r C W := by
    intro v hvW
    rcases hvW with rfl | rfl
    · refine ⟨xmin, ymin, fun q => if q = (xmin, ymin) then vmax else v, ⟨hCmin, fun q => ?_,
        fun y' => ?_⟩, ?_⟩
      · dsimp only
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · by_cases hy : y' = ymin
        · subst hy; exact le_rfl
        · have hq : ((xmin, y') : X × Y) ≠ (xmin, ymin) := by simp [hy]
          simp only [hq, ↓reduceIte]
          have := mul_le_mul_of_nonneg_left (hH y') (by linarith : (0 : ℝ) ≤ 1 - δ)
          linarith
      · simp only [↓reduceIte]
        exact hv.symm
    · refine ⟨xmax, ymax, fun q => if q = (xmax, ymax) then v else vmin, ⟨hCmax, fun q => ?_,
        fun y' => ?_⟩, ?_⟩
      · dsimp only
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · by_cases hy : y' = ymax
        · subst hy; exact le_rfl
        · have hq : ((xmax, y') : X × Y) ≠ (xmax, ymax) := by simp [hy]
          simp only [hq, ↓reduceIte]
          have := h4 y'
          rw [h3]
          linarith
      · simp only [↓reduceIte]
        rw [h3]
        ring
  have hWV := cg_selfGenerating_subset_V hδ0.le hδ1 hM hWb hSG
  exact ⟨hWV (Or.inl rfl), hWV (Or.inr rfl)⟩

/-- Miao, p. 771: "This equilibrium is self-enforcing." Under the conditions of
`example_21_4_6`, the stick-and-carrot path `(x*, y*), (x^R, y^R), (x^R, y^R), …` is
self-enforcing. -/
theorem cg_example_21_4_6_selfEnforcing {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xR xs : X} {yR ys : Y}
    (hR : (xR, yR) ∈ C) (hs : (xs, ys) ∈ C)
    (hstick : ∀ y', (1 - δ) * r xs y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤
      (1 - δ) * r xs ys + δ * r xR yR)
    (hcarrot : ∀ y', (1 - δ) * r xR y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤ r xR yR) :
    cg_SelfEnforcing δ r C (fun t => if t = 0 then (xs, ys) else (xR, yR)) := by
  set p : ℕ → X × Y := fun t => if t = 0 then (xs, ys) else (xR, yR) with hp
  have hconst : ∀ t, cg_Ut δ r p (t + 1) = r xR yR := by
    intro t
    unfold cg_Ut
    have : (fun s => p (t + 1 + s)) = fun _ => (xR, yR) := by
      funext s; simp [hp]
    rw [this, cg_pathValue_const hδ0 hδ1]
  have h0 : cg_Ut δ r p 0 = (1 - δ) * r xs ys + δ * r xR yR := by
    rw [cg_Ut_succ hδ0 hδ1 hM p 0, hconst]
    simp [hp]
  rw [proposition_21_4_2 hδ0 hδ1 hM]
  intro t
  rcases t with _ | t
  · refine ⟨by simpa [hp] using hs, fun y' _ => ?_⟩
    rw [h0]
    simpa [hp] using hstick y'
  · refine ⟨by simpa [hp] using hR, fun y' _ => ?_⟩
    rw [h0, hconst]
    simpa [hp] using hcarrot y'

end Miao.DynamicGames
