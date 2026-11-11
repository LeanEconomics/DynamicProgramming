/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AABasics

/-!
# Concavity of recursive utility

Miao, §20.3.1, pp. 704–705.

* Backward induction (p. 705): on a finite event tree, if the time aggregator `W` is jointly
  concave and increasing in its second argument and every conditional certainty equivalent `M_t` is
  concave and monotone, the recursive utility `U_t(c) = W(c_t, M_t(U_{t+1}(c)))`, `U_T = c_T`, is
  concave in the plan (`aa_recU_concaveOn`).
* The strict version asserted in the text (`W` strictly increasing and concave, `M` strictly
  concave ⇒ `U` strictly concave) is false: with `W(c, y) = c + βy`, perturbing consumption at a
  single node moves `U` affinely, whatever `M` is (`aa_recU_not_strictConcave`).
* The Epstein–Zin claim (p. 705): for `ρ > 0`, `γ > 0` (`ρ, γ ≠ 1`) and `U_T(c) = c_T`, `U_t` is
  concave (`aa_ezU_concaveOn`) and homogeneous of degree one (`aa_ezU_smul`), hence never strictly
  concave (`aa_ezU_not_strictConcave`): the book's "strictly concave" is false; it holds only
  across non-proportional plans.
* **Lemma 20.3.1** (Skiadas 2009). For `f : ℝ^l_{++} → ℝ` homogeneous of degree one, (i) concavity
  and (iii) superadditivity are equivalent (`lemma_20_3_1_i_iff_iii`), and imply (ii) the
  level-set condition `f(x) = f(y), x ≠ y ⇒ f(λx + (1 − λ)y) ≥ f(x)` (`lemma_20_3_1_i_ii`; the book
  prints `f(λx + (1 − λ))`). (ii) implies (i) and (iii) when `f > 0` (`lemma_20_3_1`), but not in
  general: `f(x) = φ(x₁ − x₂)` with `φ(s) = s + max(s, 0)` satisfies (ii) but neither (i) nor (iii)
  (`lemma_20_3_1_counterexample`).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- Recursive utility `U_t(c) = W(c_t, M_t(U_{t+1}(c)))` on the event tree, `U_T(c) = c_T`; `M h` is
the conditional certainty equivalent at the node `h`. -/
noncomputable def aa_recU (W : ℝ → ℝ → ℝ) (M : List S → (S → ℝ) → ℝ) (c : List S → ℝ) :
    ℕ → List S → ℝ
  | 0, h => c h
  | n + 1, h => W (c h) (M h fun s => aa_recU W M c n (s :: h))

/-- The positive plans. -/
def aa_posPlans (S : Type*) : Set (List S → ℝ) := {c | ∀ h, 0 < c h}

omit [Fintype S] in
theorem aa_posPlans_convex : Convex ℝ (aa_posPlans S) := by
  intro c hc c' hc' a b ha hb hab h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · nlinarith [mul_pos ha' (hc h), mul_nonneg hb (hc' h).le]
  · subst ha'
    rw [zero_add] at hab
    subst hab
    simpa using hc' h

omit [Fintype S] in
/-- **Concavity by backward induction** (Miao, p. 705). Suppose `W` is jointly concave on
`(0, ∞)²`, monotone in `y`, and positive; every `M_h` is concave and monotone on `(0, ∞)^S` and
positive. Then `U_n(·, h)` is positive and concave on positive plans, for every horizon `n` and
node `h`. -/
theorem aa_recU_concaveOn {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ}
    (hWc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) fun z : ℝ × ℝ => W z.1 z.2)
    (hWm : ∀ c, 0 < c → MonotoneOn (W c) (Set.Ioi 0))
    (hWp : ∀ c y, 0 < c → 0 < y → 0 < W c y)
    (hMc : ∀ h, ConcaveOn ℝ (SS.posCone S) (M h)) (hMm : ∀ h, MonotoneOn (M h) (SS.posCone S))
    (hMp : ∀ h x, x ∈ SS.posCone S → 0 < M h x) :
    ∀ n h, (∀ c ∈ aa_posPlans S, 0 < aa_recU W M c n h) ∧
      ConcaveOn ℝ (aa_posPlans S) fun c => aa_recU W M c n h := by
  intro n
  induction n with
  | zero =>
    intro h
    refine ⟨fun c hc => hc h, aa_posPlans_convex, fun c _ c' _ a b _ _ _ => ?_⟩
    simp [aa_recU]
  | succ n ih =>
    intro h
    have hpos : ∀ c ∈ aa_posPlans S, (fun s => aa_recU W M c n (s :: h)) ∈ SS.posCone S :=
      fun c hc s => (ih (s :: h)).1 c hc
    refine ⟨fun c hc => hWp _ _ (hc h) (hMp h _ (hpos c hc)), aa_posPlans_convex, ?_⟩
    intro c hc c' hc' a b ha hb hab
    simp only [aa_recU, smul_eq_mul]
    have hmix := aa_posPlans_convex hc hc' ha hb hab
    -- children: concavity of `U_n`
    have hchild : ∀ s, a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h) ≤
        aa_recU W M (a • c + b • c') n (s :: h) := fun s => by
      have := (ih (s :: h)).2.2 hc hc' ha hb hab
      simpa [smul_eq_mul] using this
    have hcomb : (fun s => a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h)) ∈
        SS.posCone S := SS.convex_posCone (hpos c hc) (hpos c' hc') ha hb hab
    have hM1 : a * M h (fun s => aa_recU W M c n (s :: h)) +
        b * M h (fun s => aa_recU W M c' n (s :: h)) ≤
          M h (fun s => a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h)) := by
      have := (hMc h).2 (hpos c hc) (hpos c' hc') ha hb hab
      simp only [smul_eq_mul] at this
      convert this using 2
    have hM2 : M h (fun s => a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h)) ≤
        M h (fun s => aa_recU W M (a • c + b • c') n (s :: h)) :=
      hMm h hcomb (hpos _ hmix) hchild
    have hy1 := hMp h _ (hpos c hc)
    have hy2 := hMp h _ (hpos c' hc')
    have hy3 : 0 < a * M h (fun s => aa_recU W M c n (s :: h)) +
        b * M h (fun s => aa_recU W M c' n (s :: h)) := by
      rcases ha.lt_or_eq with ha' | ha'
      · nlinarith [mul_pos ha' hy1, mul_nonneg hb hy2.le]
      · subst ha'
        rw [zero_add] at hab
        subst hab
        simpa using hy2
    have hW1 : a * W (c h) (M h fun s => aa_recU W M c n (s :: h)) +
        b * W (c' h) (M h fun s => aa_recU W M c' n (s :: h)) ≤
          W (a * c h + b * c' h) (a * M h (fun s => aa_recU W M c n (s :: h)) +
            b * M h (fun s => aa_recU W M c' n (s :: h))) := by
      have := hWc.2 (x := (c h, M h fun s => aa_recU W M c n (s :: h)))
        (y := (c' h, M h fun s => aa_recU W M c' n (s :: h))) ⟨hc h, hy1⟩ ⟨hc' h, hy2⟩ ha hb hab
      simpa [smul_eq_mul] using this
    have hch : (a • c + b • c') h = a * c h + b * c' h := by simp
    rw [hch]
    exact hW1.trans (hWm _ (by rw [← hch]; exact hmix h) hy3 (hMp h _ (hpos _ hmix))
      (hM1.trans hM2))

omit [Fintype S] in
/-- `U_n(c, g)` depends only on consumption at nodes of length at least `|g|`. -/
theorem aa_recU_congr (W : ℝ → ℝ → ℝ) (M : List S → (S → ℝ) → ℝ) {c c' : List S → ℝ} :
    ∀ n g, (∀ g', g.length ≤ g'.length → c g' = c' g') → aa_recU W M c n g = aa_recU W M c' n g
  | 0, g, hg => hg g le_rfl
  | n + 1, g, hg => by
    simp only [aa_recU]
    rw [hg g le_rfl]
    congr 2
    funext s
    exact aa_recU_congr W M n (s :: g) fun g' hg' => hg g' (by simp at hg'; omega)

omit [Fintype S] in
/-- **The strict version is false** (Miao, p. 705): with `W(c, y) = c + βy`, for any conditional
certainty equivalents `M`, `U_{n+1}(·, h)` is affine along perturbations of consumption at the node
`h`, so it is not strictly concave on the positive plans. -/
theorem aa_recU_not_strictConcave [Nonempty S] (β : ℝ) (M : List S → (S → ℝ) → ℝ) (n : ℕ)
    (h : List S) :
    ¬ StrictConcaveOn ℝ (aa_posPlans S) fun c => aa_recU (fun x y => x + β * y) M c (n + 1) h := by
  classical
  intro hsc
  set c : List S → ℝ := fun _ => 1 with hcdef
  set c' : List S → ℝ := Function.update c h 3 with hc'def
  have hc : c ∈ aa_posPlans S := fun _ => one_pos
  have hc' : c' ∈ aa_posPlans S := fun g => by
    simp only [hc'def, Function.update_apply]
    split_ifs <;> norm_num [hcdef]
  have hne : c ≠ c' := fun he => by
    have := congrFun he h
    simp [hc'def, hcdef] at this
  have key := hsc.2 hc hc' hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hagree : ∀ d : List S → ℝ, (∀ g, g ≠ h → d g = 1) → ∀ s,
      aa_recU (fun x y => x + β * y) M d n (s :: h) =
        aa_recU (fun x y => x + β * y) M c n (s :: h) := fun d hd s =>
    aa_recU_congr _ M n (s :: h) fun g' hg' => by
      rw [hd g' (fun he => by subst he; simp at hg')]
  have hmix : ∀ g, g ≠ h → ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • c') g = 1 := fun g hg => by
    simp [hc'def, hcdef, hg]
    norm_num
  have hc'1 : ∀ g, g ≠ h → c' g = 1 := fun g hg => by simp [hc'def, hcdef, hg]
  simp only [aa_recU, smul_eq_mul] at key
  rw [show (fun s => aa_recU (fun x y => x + β * y) M ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • c') n
      (s :: h)) = fun s => aa_recU (fun x y => x + β * y) M c n (s :: h) from
        funext (hagree _ hmix),
    show (fun s => aa_recU (fun x y => x + β * y) M c' n (s :: h)) =
      fun s => aa_recU (fun x y => x + β * y) M c n (s :: h) from funext (hagree _ hc'1)] at key
  simp [hc'def, hcdef] at key
  linarith

/-! ### Epstein–Zin -/

/-- The Epstein–Zin finite-horizon utility is the recursive utility with `W` the CES aggregator
and `M_h` the Kreps–Porteus certainty equivalent. -/
theorem aa_ezU_eq_recU (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) :
    ∀ n h, aa_ezU β ρ γ p c n h = aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c n h
  | 0, _ => rfl
  | n + 1, h => by
    simp only [aa_ezU, aa_recU]
    rw [show (fun s => aa_ezU β ρ γ p c n (s :: h)) =
      (fun s => aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c n (s :: h)) from
        funext fun s => aa_ezU_eq_recU β ρ γ p c n (s :: h)]

/-- The Kreps–Porteus certainty equivalent is concave on `(0, ∞)^S` for `γ ≥ 0`, `γ ≠ 1`. -/
theorem aa_KP_concaveOn [Nonempty S] {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≠ 1) {p : S → ℝ}
    (hp : SS.IsDistribution p) : ConcaveOn ℝ (SS.posCone S) (aa_KP γ p) := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have hP : SS.IsMarkov (fun (_ : S) (s : S) => p s : Matrix S S ℝ) :=
    ⟨fun _ s => hp.nonneg s, fun _ => hp.sum_eq_one⟩
  have h := SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hγ1)) (by linarith) hP
  have e : ∀ x, aa_KP γ p x = SS.kpR (1 - γ) (fun (_ : S) (s : S) => p s : Matrix S S ℝ) x s₀ :=
    fun x => by
      simp [aa_KP, SS.kpR, aa_E, Matrix.mulVec, dotProduct]
  refine ⟨SS.convex_posCone, fun x hx y hy a b ha hb hab => ?_⟩
  rw [e, e, e]
  exact h.2 hx hy ha hb hab s₀

/-- The CES aggregator is jointly concave on `(0, ∞)²` for `ρ ≥ 0`, `ρ ≠ 1`, `β ∈ [0, 1]`. -/
theorem aa_W_concaveOn {β ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≠ 1) :
    ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) fun z : ℝ × ℝ => aa_W β ρ z.1 z.2 := by
  set P : Matrix Bool Bool ℝ := fun _ b => if b then β else 1 - β with hPdef
  have hP : SS.IsMarkov P :=
    ⟨fun _ b => by cases b <;> simp [hPdef] <;> linarith, fun _ => by simp [hPdef]⟩
  have h := SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hρ1)) (by linarith) hP
  let v : ℝ × ℝ → Bool → ℝ := fun z b => if b then z.2 else z.1
  have e : ∀ z : ℝ × ℝ, aa_W β ρ z.1 z.2 = SS.kpR (1 - ρ) P (v z) true := fun z => by
    simp [aa_W, SS.kpR, Matrix.mulVec, dotProduct, hPdef, v, add_comm]
  have hv : ∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi 0, v z ∈ SS.posCone Bool := fun z hz b => by
    cases b
    · exact hz.1
    · exact hz.2
  have hlin : ∀ (z w : ℝ × ℝ) (a b : ℝ), v (a • z + b • w) = a • v z + b • v w := fun z w a b => by
    funext t
    cases t <;> simp [v]
  refine ⟨(convex_Ioi 0).prod (convex_Ioi 0), fun z hz w hw a b ha hb hab => ?_⟩
  dsimp only
  rw [e, e, e, hlin]
  exact h.2 (hv z hz) (hv w hw) ha hb hab true

/-- Miao, p. 705 (the corrected claim): for the Epstein–Zin utility (20.3) with a finite horizon,
`U_T(c) = c_T`, `ρ > 0` and `γ > 0` (`ρ, γ ≠ 1`, `β ∈ (0, 1)`), every `U_t` is concave on positive
plans. -/
theorem aa_ezU_concaveOn [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≠ 1) (hγ0 : 0 < γ) (hγ1 : γ ≠ 1) {p : List S → S → ℝ}
    (hp : ∀ h, SS.IsDistribution (p h)) (n : ℕ) (h : List S) :
    ConcaveOn ℝ (aa_posPlans S) fun c => aa_ezU β ρ γ p c n h := by
  have := (aa_recU_concaveOn (aa_W_concaveOn hβ0.le hβ1.le hρ0.le hρ1)
    (fun c hc => (aa_W_strictMonoOn hβ0 hβ1 hρ1 hc).monotoneOn)
    (fun c y hc hy => aa_W_pos hβ0 hβ1 hc hy) (fun h => aa_KP_concaveOn hγ0.le hγ1 (hp h))
    (fun h x hx y _ hxy => aa_KP_mono hγ1 (hp h) hx hxy)
    (fun h x hx => aa_KP_pos γ (hp h) hx) n h).2
  simpa only [aa_ezU_eq_recU] using this

/-- Homogeneity of degree one of the Epstein–Zin utility: `U_t(λc) = λU_t(c)` for `λ > 0`. -/
theorem aa_ezU_smul [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1)
    (hγ : γ ≠ 1) {p : List S → S → ℝ}
    (hp : ∀ h, SS.IsDistribution (p h)) {c : List S → ℝ} (hc : ∀ h, 0 < c h) {t : ℝ}
    (ht : 0 < t) : ∀ n h, aa_ezU β ρ γ p (t • c) n h = t * aa_ezU β ρ γ p c n h
  | 0, h => by simp [aa_ezU]
  | n + 1, h => by
    simp only [aa_ezU]
    rw [show (fun s => aa_ezU β ρ γ p (t • c) n (s :: h)) =
      (fun s => t * aa_ezU β ρ γ p c n (s :: h)) from
        funext fun s => aa_ezU_smul hβ0 hβ1 hρ hγ hp hc ht n (s :: h)]
    have hx : ∀ s, 0 < aa_ezU β ρ γ p c n (s :: h) := fun s => aa_ezU_pos hβ0 hβ1 hp hc n _
    have hE := aa_E_pos (hp h) fun s => Real.rpow_pos_of_pos (hx s) (1 - γ)
    have hK : aa_KP γ (p h) (fun s => t * aa_ezU β ρ γ p c n (s :: h)) =
        t * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) := by
      unfold aa_KP
      rw [show (fun s => (t * aa_ezU β ρ γ p c n (s :: h)) ^ (1 - γ)) =
        (fun s => t ^ (1 - γ) * aa_ezU β ρ γ p c n (s :: h) ^ (1 - γ)) from
          funext fun s => Real.mul_rpow ht.le (hx s).le, aa_E_smul,
        Real.mul_rpow (Real.rpow_nonneg ht.le _) hE.le]
      rw [Real.rpow_rpow_inv ht.le (sub_ne_zero.2 (Ne.symm hγ))]
    rw [hK]
    have hKp := aa_KP_pos γ (hp h) hx
    unfold aa_W
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.mul_rpow ht.le (hc h).le, Real.mul_rpow ht.le hKp.le]
    have hb : 0 ≤ (1 - β) * c h ^ (1 - ρ) +
        β * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) ^ (1 - ρ) :=
      add_nonneg (mul_nonneg (by linarith) (Real.rpow_pos_of_pos (hc h) _).le)
        (mul_nonneg hβ0.le (Real.rpow_pos_of_pos hKp _).le)
    rw [show (1 - β) * (t ^ (1 - ρ) * c h ^ (1 - ρ)) +
        β * (t ^ (1 - ρ) * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) ^ (1 - ρ)) =
      t ^ (1 - ρ) * ((1 - β) * c h ^ (1 - ρ) +
        β * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) ^ (1 - ρ)) by ring,
      Real.mul_rpow (Real.rpow_nonneg ht.le _) hb]
    rw [Real.rpow_rpow_inv ht.le (sub_ne_zero.2 (Ne.symm hρ))]

/-- **The Epstein–Zin utility is not strictly concave** (correction to Miao, p. 705): being
homogeneous of degree one, `U_t` is affine along every ray, so the claim "`U_t` is strictly
concave" fails for every horizon. -/
theorem aa_ezU_not_strictConcave [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) (n : ℕ) (h : List S) :
    ¬ StrictConcaveOn ℝ (aa_posPlans S) fun c => aa_ezU β ρ γ p c n h := by
  intro hsc
  set c : List S → ℝ := fun _ => 1 with hcdef
  have hc : c ∈ aa_posPlans S := fun _ => one_pos
  have h3 : (3 : ℝ) • c ∈ aa_posPlans S := fun g => by simp [hcdef]
  have hne : c ≠ (3 : ℝ) • c := fun he => by
    have := congrFun he []
    simp [hcdef] at this
  have key := hsc.2 hc h3 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hmix : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • ((3 : ℝ) • c) = (2 : ℝ) • c := by
    funext g; simp [hcdef]; norm_num
  simp only [smul_eq_mul] at key
  rw [hmix, aa_ezU_smul hβ0 hβ1 hρ hγ hp hc (by norm_num) n h,
    aa_ezU_smul hβ0 hβ1 hρ hγ hp hc (by norm_num) n h] at key
  linarith

/-! ### Lemma 20.3.1 -/

variable {ι : Type*}

/-- Homogeneity of degree one on `ℝ^l_{++}`. -/
def aa_Homogeneous1 (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x ∈ SS.posCone ι, ∀ t : ℝ, 0 < t → f (t • x) = t * f x

/-- Condition (ii) of Lemma 20.3.1 (with the book's misprint `f(λx + (1 − λ))` read as
`f(λx + (1 − λ)y)`). -/
def aa_LevelCond (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x ∈ SS.posCone ι, ∀ y ∈ SS.posCone ι, f x = f y → x ≠ y → ∀ l : ℝ, 0 < l → l < 1 →
    f x ≤ f (l • x + (1 - l) • y)

/-- Condition (iii) of Lemma 20.3.1: superadditivity. -/
def aa_Superadd (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x ∈ SS.posCone ι, ∀ y ∈ SS.posCone ι, f x + f y ≤ f (x + y)

/-- **Lemma 20.3.1**, (i) ⇔ (iii) (Miao, p. 705): a function homogeneous of degree one on
`ℝ^l_{++}` is concave iff it is superadditive. -/
theorem lemma_20_3_1_i_iff_iii {f : (ι → ℝ) → ℝ} (hf : aa_Homogeneous1 f) :
    ConcaveOn ℝ (SS.posCone ι) f ↔ aa_Superadd f := by
  constructor
  · intro hc x hx y hy
    have h := hc.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have hxy : x + y ∈ SS.posCone ι := fun i => add_pos (hx i) (hy i)
    have e : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) := by
      rw [smul_add]
    rw [e, hf _ hxy _ (by norm_num), smul_eq_mul, smul_eq_mul] at h
    linarith
  · intro hs
    refine ⟨SS.convex_posCone, fun x hx y hy a b ha hb hab => ?_⟩
    rcases ha.lt_or_eq with ha' | ha'
    · rcases hb.lt_or_eq with hb' | hb'
      · have hax := SS.smul_mem_posCone hx ha'
        have hby := SS.smul_mem_posCone hy hb'
        have := hs _ hax _ hby
        rwa [hf x hx a ha', hf y hy b hb'] at this
      · subst hb'
        rw [add_zero] at hab
        subst hab
        simp
    · subst ha'
      rw [zero_add] at hab
      subst hab
      simp

/-- **Lemma 20.3.1**, (i) ⇒ (ii) (Miao, p. 705). -/
theorem lemma_20_3_1_i_ii {f : (ι → ℝ) → ℝ} (hc : ConcaveOn ℝ (SS.posCone ι) f) :
    aa_LevelCond f := by
  intro x hx y hy hxy _ l hl0 hl1
  have := hc.2 hx hy hl0.le (by linarith : 0 ≤ 1 - l) (by ring)
  rw [smul_eq_mul, smul_eq_mul, ← hxy] at this
  linarith

/-- **Lemma 20.3.1** (Miao, p. 705; Skiadas 2009), for positive `f`: for `f : ℝ^l_{++} → (0, ∞)`
homogeneous of degree one, (i) concavity, (ii) the level-set condition and (iii) superadditivity
are equivalent. -/
theorem lemma_20_3_1 {f : (ι → ℝ) → ℝ} (hf : aa_Homogeneous1 f)
    (hpos : ∀ x ∈ SS.posCone ι, 0 < f x) :
    (ConcaveOn ℝ (SS.posCone ι) f ↔ aa_LevelCond f) ∧
      (ConcaveOn ℝ (SS.posCone ι) f ↔ aa_Superadd f) := by
  have hiii := lemma_20_3_1_i_iff_iii hf
  refine ⟨⟨lemma_20_3_1_i_ii, fun hii => hiii.2 ?_⟩, hiii⟩
  intro x hx y hy
  have hfx := hpos x hx
  have hfy := hpos y hy
  set x' := (f x)⁻¹ • x with hx'
  set y' := (f y)⁻¹ • y with hy'
  have hx'p : x' ∈ SS.posCone ι := SS.smul_mem_posCone hx (inv_pos.2 hfx)
  have hy'p : y' ∈ SS.posCone ι := SS.smul_mem_posCone hy (inv_pos.2 hfy)
  have hfx' : f x' = 1 := by rw [hf x hx _ (inv_pos.2 hfx), inv_mul_cancel₀ hfx.ne']
  have hfy' : f y' = 1 := by rw [hf y hy _ (inv_pos.2 hfy), inv_mul_cancel₀ hfy.ne']
  set l := f x / (f x + f y) with hl
  have hl0 : 0 < l := div_pos hfx (add_pos hfx hfy)
  have hl1 : l < 1 := by rw [hl, div_lt_one (add_pos hfx hfy)]; linarith
  have hsum : x + y = (f x + f y) • (l • x' + (1 - l) • y') := by
    rw [hx', hy', hl, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    have e1 : (f x + f y) * (f x / (f x + f y)) * (f x)⁻¹ = 1 := by field_simp
    have e2 : (f x + f y) * (1 - f x / (f x + f y)) * (f y)⁻¹ = 1 := by field_simp; ring
    rw [e1, e2, one_smul, one_smul]
  have hmixp : l • x' + (1 - l) • y' ∈ SS.posCone ι :=
    SS.convex_posCone hx'p hy'p hl0.le (by linarith) (by ring)
  have hmix1 : 1 ≤ f (l • x' + (1 - l) • y') := by
    by_cases hxy : x' = y'
    · rw [hxy, ← add_smul, show l + (1 - l) = 1 by ring, one_smul, hfy']
    · have := hii x' hx'p y' hy'p (by rw [hfx', hfy']) hxy l hl0 hl1
      rwa [hfx'] at this
  rw [hsum, hf _ hmixp _ (add_pos hfx hfy)]
  nlinarith

/-- The counterexample to Lemma 20.3.1 without positivity: `f(x) = φ(x₀ − x₁)` with
`φ(s) = s + max(s, 0)` on `ℝ²_{++}`. -/
noncomputable def aa_skiadasCex (x : Fin 2 → ℝ) : ℝ := (x 0 - x 1) + max (x 0 - x 1) 0

/-- **Lemma 20.3.1 fails without positivity** (Miao, p. 705): `f(x) = φ(x₀ − x₁)`,
`φ(s) = s + max(s, 0)`, is homogeneous of degree one and satisfies (ii) on `ℝ²_{++}`, but it is
neither superadditive (iii) nor concave (i): `f(2, 1) + f(1, 2) = 1 > 0 = f(3, 3)`. -/
theorem lemma_20_3_1_counterexample :
    aa_Homogeneous1 aa_skiadasCex ∧ aa_LevelCond aa_skiadasCex ∧ ¬ aa_Superadd aa_skiadasCex ∧
      ¬ ConcaveOn ℝ (SS.posCone (Fin 2)) aa_skiadasCex := by
  have hhom : aa_Homogeneous1 aa_skiadasCex := fun x _ t ht => by
    simp only [aa_skiadasCex, Pi.smul_apply, smul_eq_mul]
    have e : max (t * (x 0 - x 1)) 0 = t * max (x 0 - x 1) 0 := by
      rw [mul_max_of_nonneg _ _ ht.le, mul_zero]
    rw [← mul_sub, e]
    ring
  have hinj : ∀ d e : ℝ, d + max d 0 = e + max e 0 → d = e := fun d e h => by
    rcases le_total d 0 with hd | hd <;> rcases le_total e 0 with he | he <;>
      simp only [max_eq_right, max_eq_left, hd, he] at h <;> linarith
  have hsup : ¬ aa_Superadd aa_skiadasCex := fun h => by
    have := h ![2, 1] (fun i => by fin_cases i <;> norm_num) ![1, 2]
      (fun i => by fin_cases i <;> norm_num)
    simp [aa_skiadasCex] at this
    norm_num at this
  refine ⟨hhom, ?_, hsup, fun hc => hsup ((lemma_20_3_1_i_iff_iii hhom).1 hc)⟩
  intro x _ y _ hxy _ l _ _
  have hd := hinj _ _ hxy
  have : aa_skiadasCex (l • x + (1 - l) • y) = aa_skiadasCex x := by
    simp only [aa_skiadasCex, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : l * x 0 + (1 - l) * y 0 - (l * x 1 + (1 - l) * y 1) = x 0 - x 1 := by
      have : y 0 - y 1 = x 0 - x 1 := hd.symm
      nlinarith
    rw [this]
  rw [this]

end Miao.RecursiveUtility
