/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.KUEpsteinZin
import RecursiveUtility.SSCertaintyEquivalents

/-!
# Exercise 20.1: Epstein–Zin utility with a finite horizon

Miao, Exercise 20.1, p. 735 (item 1 of §20.6): the Epstein–Zin utility (20.3) with horizon `T`,
`U_T(c) = c_T`, `U_t(c) = [(1 − β)c_t^{1−ρ} + β(E_t[U_{t+1}^{1−γ}])^{(1−ρ)/(1−γ)}]^{1/(1−ρ)}`.
The exercise asks to prove that `U_t` is strictly concave for `t < T` when `ρ > 0` and `γ > 0`.

* `ku_ezFin`, `ku_ezFin_T`, `ku_ezFin_succ`: the backward recursion; `ku_ezFin_pos`.
* `ku_ezFin_dynUtility`, `ku_ezFin_meas`: `U` is a dynamic utility (Definition 20.2.1) on the
  dates `t ≤ T`.
* `ku_ezFin_homog`: `U_t(λc) = λU_t(c)` (homotheticity).
* `ex_20_1`: `U_t` is concave on positive plans, for `0 ≤ ρ`, `0 ≤ γ` (`ρ, γ ≠ 1`), `0 < β < 1`.
* `ex_20_1_not_strict`: `U_t` is never strictly concave: by homogeneity it is linear along rays
  (`U_t(2c) = (U_t(c) + U_t(3c))/2`). The exercise's claim is false as printed; concavity is
  what holds.
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [Fintype S]

/-- The backward recursion of Exercise 20.1, indexed by the number `k` of periods to go. -/
noncomputable def ku_ezAux (P : Matrix S S ℝ) (β ρ γ : ℝ) (T : ℕ) (c : ℕ → (ℕ → S) → ℝ) :
    ℕ → (ℕ → S) → ℝ
  | 0 => c T
  | k + 1 => fun ω =>
      ku_ces β ρ (c (T - (k + 1)) ω) (ku_kpCE P γ (T - (k + 1)) (ku_ezAux P β ρ γ T c k) ω)

/-- Miao, Exercise 20.1: the finite-horizon Epstein–Zin utility `U_t(c)`. -/
noncomputable def ku_ezFin (P : Matrix S S ℝ) (β ρ γ : ℝ) (T : ℕ) (c : ℕ → (ℕ → S) → ℝ)
    (t : ℕ) : (ℕ → S) → ℝ :=
  ku_ezAux P β ρ γ T c (T - t)

theorem ku_ezFin_T (P : Matrix S S ℝ) (β ρ γ : ℝ) (T : ℕ) (c : ℕ → (ℕ → S) → ℝ) :
    ku_ezFin P β ρ γ T c T = c T := by
  simp [ku_ezFin, ku_ezAux]

/-- Miao, Exercise 20.1: `U_t = W(c_t, M_t(U_{t+1}))` for `t < T`. -/
theorem ku_ezFin_succ (P : Matrix S S ℝ) (β ρ γ : ℝ) {T t : ℕ} (c : ℕ → (ℕ → S) → ℝ)
    (ht : t < T) (ω : ℕ → S) :
    ku_ezFin P β ρ γ T c t ω =
      ku_ces β ρ (c t ω) (ku_kpCE P γ t (ku_ezFin P β ρ γ T c (t + 1)) ω) := by
  obtain ⟨k, hk⟩ : ∃ k, T - t = k + 1 := ⟨T - t - 1, by omega⟩
  have hk' : T - (t + 1) = k := by omega
  have ht' : T - (k + 1) = t := by omega
  simp only [ku_ezFin, hk, hk', ku_ezAux, ht']

/-- The set of positive consumption plans. -/
def ku_PosPlan (S : Type*) : Set (ℕ → (ℕ → S) → ℝ) := {c | ∀ t ω, 0 < c t ω}

omit [Fintype S] in
theorem ku_convex_PosPlan : Convex ℝ (ku_PosPlan S) := by
  intro x hx y hy a b ha hb hab t ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with h | h
  · subst h
    rw [zero_add] at hab
    subst hab
    simpa using hy t ω
  · exact add_pos_of_pos_of_nonneg (mul_pos h (hx t ω)) (mul_nonneg hb (hy t ω).le)

theorem ku_ezAux_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (T : ℕ) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ ku_PosPlan S) (k : ℕ) :
    ∀ ω, 0 < ku_ezAux P β ρ γ T c k ω := by
  induction k with
  | zero => exact hc T
  | succ k ih => exact fun ω => ku_ces_pos hβ0 hβ1 (hc _ ω) (ku_kpCE_pos hP γ ih _ ω)

theorem ku_ezFin_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (T : ℕ) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ ku_PosPlan S) (t : ℕ) (ω : ℕ → S) :
    0 < ku_ezFin P β ρ γ T c t ω :=
  ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc _ ω

/-- Miao, Definition 20.2.1 for Exercise 20.1: `U_t(c)` depends only on `c_s`, `s ≥ t`, for
`t ≤ T`. -/
theorem ku_ezFin_dynUtility (P : Matrix S S ℝ) (β ρ γ : ℝ) {T t : ℕ} (ht : t ≤ T)
    {c c' : ℕ → (ℕ → S) → ℝ} (h : ∀ s ≥ t, c s = c' s) :
    ku_ezFin P β ρ γ T c t = ku_ezFin P β ρ γ T c' t := by
  have key : ∀ k, k ≤ T - t → ku_ezAux P β ρ γ T c k = ku_ezAux P β ρ γ T c' k := by
    intro k
    induction k with
    | zero => exact fun _ => h T ht
    | succ k ih =>
      intro hk
      funext ω
      simp only [ku_ezAux, ih (by omega), h (T - (k + 1)) (by omega)]
  exact key _ le_rfl

/-- Miao, Definition 20.2.1 for Exercise 20.1: for an adapted plan, `U_t(c)` is
`F_t`-measurable (`t ≤ T`). -/
theorem ku_ezFin_meas (P : Matrix S S ℝ) (β ρ γ : ℝ) {T t : ℕ} (ht : t ≤ T)
    {c : ℕ → (ℕ → S) → ℝ} (hc : ku_Adapted c) : ku_Meas t (ku_ezFin P β ρ γ T c t) := by
  have key : ∀ k, k ≤ T → ku_Meas (T - k) (ku_ezAux P β ρ γ T c k) := by
    intro k
    induction k with
    | zero =>
      intro _
      change ku_Meas (T - 0) (c T)
      simpa using hc T
    | succ k ih =>
      intro hk ω ω' hωω
      have hm := ih (by omega)
      rw [show T - k = T - (k + 1) + 1 by omega] at hm
      have hm' : ku_Meas (T - (k + 1) + 1) fun ω => ku_ezAux P β ρ γ T c k ω ^ (1 - γ) :=
        fun ω ω' h => by
          change ku_ezAux P β ρ γ T c k ω ^ (1 - γ) = ku_ezAux P β ρ γ T c k ω' ^ (1 - γ)
          rw [hm ω ω' h]
      simp only [ku_ezAux, ku_kpCE]
      rw [hc _ ω ω' hωω, ku_E_meas P hm' ω ω' hωω]
  have := key (T - t) (by omega)
  rwa [show T - (T - t) = t by omega] at this

/-- `M_t(λx) = λM_t(x)` for the Kreps–Porteus certainty equivalent. -/
theorem ku_kpCE_homog {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1) (t : ℕ)
    {x : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω) {l : ℝ} (hl : 0 < l) (ω : ℕ → S) :
    ku_kpCE P γ t (fun ω' => l * x ω') ω = l * ku_kpCE P γ t x ω := by
  rw [ku_kpCE_eq_kpR, ku_kpCE_eq_kpR]
  have h := SS.posHomogeneous_kpR (sub_ne_zero.2 (Ne.symm hγ)) hP
    (fun s' => x (Function.update ω (t + 1) s')) (fun _ => hx _) l hl.le
    (fun s' => by simpa using mul_pos hl (hx _))
  have := congrFun h (ω t)
  convert this using 2

/-- Miao, p. 686 and Exercise 20.1: the finite-horizon Epstein–Zin utility is homogeneous of
degree one, `U_t(λc) = λU_t(c)`. -/
theorem ku_ezFin_homog {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (T : ℕ) {c : ℕ → (ℕ → S) → ℝ}
    (hc : c ∈ ku_PosPlan S) {l : ℝ} (hl : 0 < l) (t : ℕ) (ω : ℕ → S) :
    ku_ezFin P β ρ γ T (l • c) t ω = l * ku_ezFin P β ρ γ T c t ω := by
  have key : ∀ k ω, ku_ezAux P β ρ γ T (l • c) k ω = l * ku_ezAux P β ρ γ T c k ω := by
    intro k
    induction k with
    | zero => intro ω; rfl
    | succ k ih =>
      intro ω
      have hf : ku_ezAux P β ρ γ T (l • c) k = fun ω' => l * ku_ezAux P β ρ γ T c k ω' :=
        funext ih
      simp only [ku_ezAux, hf]
      rw [ku_kpCE_homog hP hγ _ (ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc k) hl,
        Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ku_ces_homog hρ hβ0.le hβ1.le hl (hc _ ω).le
          (ku_kpCE_pos hP γ (ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc k) _ ω).le]
  exact key _ ω

/-- The two-state "distribution" `(1 − β, β)`, under which `SS.kpR` is the CES aggregator. -/
def ku_Q (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun _ j => if j = 0 then 1 - β else β

theorem ku_Q_markov {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : SS.IsMarkov (ku_Q β) :=
  ⟨fun _ j => by unfold ku_Q; split_ifs <;> linarith,
    fun _ => by simp [ku_Q, Fin.sum_univ_two]⟩

theorem ku_ces_eq_kpR (β ρ x y : ℝ) :
    ku_ces β ρ x y = SS.kpR (1 - ρ) (ku_Q β) ![x, y] 0 := by
  simp [ku_ces, SS.kpR, ku_Q, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The CES aggregator is jointly concave on `(0, ∞)²` for `ρ ≥ 0`, `ρ ≠ 1`. -/
theorem ku_ces_concave {β ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hρ : ρ ≠ 1) (hρ0 : 0 ≤ ρ)
    {x x' y y' a b : ℝ} (hx : 0 < x) (hx' : 0 < x') (hy : 0 < y) (hy' : 0 < y') (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * ku_ces β ρ x y + b * ku_ces β ρ x' y' ≤ ku_ces β ρ (a * x + b * x') (a * y + b * y') := by
  have h := (SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hρ)) (by linarith)
    (ku_Q_markov hβ0 hβ1)).2 (x := ![x, y]) (y := ![x', y'])
    (fun i => by fin_cases i <;> simp [hx, hy]) (fun i => by fin_cases i <;> simp [hx', hy'])
    ha hb hab
  have h0 := h 0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
  rw [ku_ces_eq_kpR, ku_ces_eq_kpR, ku_ces_eq_kpR]
  convert h0 using 3
  ext i
  fin_cases i <;> simp

/-- **Exercise 20.1** (Miao, p. 735), corrected: for `0 < β < 1`, `ρ ≥ 0`, `γ ≥ 0`
(`ρ, γ ≠ 1`), the finite-horizon Epstein–Zin utility `U_t` is concave on positive plans, at every
node. -/
theorem ex_20_1 {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hρ0 : 0 ≤ ρ) (hγ : γ ≠ 1) (hγ0 : 0 ≤ γ) (T t : ℕ) (ω : ℕ → S) :
    ConcaveOn ℝ (ku_PosPlan S) fun c => ku_ezFin P β ρ γ T c t ω := by
  have key : ∀ k, ∀ c ∈ ku_PosPlan S, ∀ c' ∈ ku_PosPlan S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → ∀ ω, a * ku_ezAux P β ρ γ T c k ω + b * ku_ezAux P β ρ γ T c' k ω ≤
        ku_ezAux P β ρ γ T (a • c + b • c') k ω := by
    intro k
    induction k with
    | zero => intro c _ c' _ a b _ _ _ ω; simp [ku_ezAux]
    | succ k ih =>
      intro c hc c' hc' a b ha hb hab ω
      set t' := T - (k + 1)
      have hmix := ku_convex_PosPlan hc hc' ha hb hab
      set X := ku_ezAux P β ρ γ T c k
      set X' := ku_ezAux P β ρ γ T c' k
      set Y := ku_ezAux P β ρ γ T (a • c + b • c') k
      have hX := ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc k
      have hX' := ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc' k
      have hY := ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hmix k
      have hZ : ∀ ω, 0 < a * X ω + b * X' ω := fun ω => by
        have := ku_convex_PosPlan (S := S) (x := fun _ => X) (y := fun _ => X')
          (fun _ => hX) (fun _ => hX') ha hb hab 0 ω
        simpa using this
      -- monotonicity of `M` and the induction hypothesis
      have h1 : ku_kpCE P γ t' (fun ω => a * X ω + b * X' ω) ω ≤ ku_kpCE P γ t' Y ω :=
        ku_kpCE_mono hP hγ t' hY hZ ω fun s' _ => ih c hc c' hc' a b ha hb hab _
      -- concavity of `M`
      have h2 : a * ku_kpCE P γ t' X ω + b * ku_kpCE P γ t' X' ω ≤
          ku_kpCE P γ t' (fun ω => a * X ω + b * X' ω) ω := by
        rw [ku_kpCE_eq_kpR, ku_kpCE_eq_kpR, ku_kpCE_eq_kpR]
        have h := (SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hγ)) (by linarith) hP).2
          (x := fun s' => X (Function.update ω (t' + 1) s'))
          (y := fun s' => X' (Function.update ω (t' + 1) s')) (fun _ => hX _) (fun _ => hX' _)
          ha hb hab (ω t')
        exact h
      have hMX := ku_kpCE_pos hP γ hX t' ω
      have hMX' := ku_kpCE_pos hP γ hX' t' ω
      have hMZ : 0 < a * ku_kpCE P γ t' X ω + b * ku_kpCE P γ t' X' ω := by
        have := ku_convex_PosPlan (S := S) (x := fun _ _ => ku_kpCE P γ t' X ω)
          (y := fun _ _ => ku_kpCE P γ t' X' ω) (fun _ _ => hMX) (fun _ _ => hMX') ha hb hab
          0 ω
        simpa using this
      have hc0 : 0 < (a • c + b • c') t' ω := hmix t' ω
      have hmono := (ku_ces_strictMonoOn hρ hβ0 hβ1 hc0).monotoneOn
      have h3 := hmono hMZ (ku_kpCE_pos hP γ hY t' ω) (h2.trans h1)
      have h4 := ku_ces_concave hβ0.le hβ1.le hρ hρ0 (hc t' ω) (hc' t' ω) hMX hMX' ha hb hab
      simp only [ku_ezAux]
      have e : (a • c + b • c') t' ω = a * c t' ω + b * c' t' ω := by simp
      rw [e] at h3 ⊢
      exact h4.trans h3
  refine ⟨ku_convex_PosPlan, fun c hc c' hc' a b ha hb hab => ?_⟩
  simpa [ku_ezFin] using key _ c hc c' hc' a b ha hb hab ω

/-- **Exercise 20.1** (Miao, p. 735): the claim is false. `U_t` is homogeneous of degree one
(`ku_ezFin_homog`), so it is linear along rays: for the constant plan `c ≡ 1`,
`U_t((c + 3c)/2) = (U_t(c) + U_t(3c))/2`, and `U_t` is not strictly concave, for any `t`, `ρ`,
`γ`. -/
theorem ex_20_1_not_strict [Nonempty S] {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (T t : ℕ) (ω : ℕ → S) :
    ¬ StrictConcaveOn ℝ (ku_PosPlan S) fun c => ku_ezFin P β ρ γ T c t ω := by
  intro h
  set c : ℕ → (ℕ → S) → ℝ := fun _ _ => 1
  have hc : c ∈ ku_PosPlan S := fun _ _ => one_pos
  have h3c : (3 : ℝ) • c ∈ ku_PosPlan S := fun _ _ => by simp [c]
  have hne : c ≠ (3 : ℝ) • c := by
    intro he
    have := congrFun (congrFun he 0) ω
    simp [c] at this
  have hs := h.2 hc h3c hne (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (by norm_num)
  have e : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • ((3 : ℝ) • c) = (2 : ℝ) • c := by
    rw [smul_smul, ← add_smul]
    norm_num
  rw [e] at hs
  simp only [smul_eq_mul] at hs
  rw [ku_ezFin_homog hP hβ0 hβ1 hρ hγ T hc (by norm_num : (0 : ℝ) < 3),
    ku_ezFin_homog hP hβ0 hβ1 hρ hγ T hc (by norm_num : (0 : ℝ) < 2)] at hs
  linarith

end Miao.RecursiveUtility
