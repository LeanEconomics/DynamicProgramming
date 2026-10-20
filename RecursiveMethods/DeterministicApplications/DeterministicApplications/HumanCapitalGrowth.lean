/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.WeightedBellman
import DeterministicApplications.HumanCapital

/-!
# Growth with human capital

SLP §5.8, pp. 111–112: `max Σ βᵗU(f[k_tφ(k_{t+1}/k_t)])` subject to
`(1 − δ)k_t ≤ k_{t+1} ≤ (1 + λ)k_t`, with functional equation
`v(k) = max_{y ∈ Γ(k)} {U(f[kφ(y/k)]) + βv(y)}` on `k > 0`.

Returns grow with `k`, so `v` is not bounded; the book's "unique continuous function" is
unique among continuous functions with `|v(k)| ≤ C(1 + k)` (any `v` of the form `Ak^{ασ}` with
`ασ < 1` qualifies).

* `human_assumption43`: `Γ(k) = [(1 − δ)k, (1 + λ)k]` is nonempty, compact-valued and continuous.
* **Exercise 5.8a** (`ex_5_8a`): if `β(1 + λ) < 1`, exactly one continuous `v` with
  `|v(k)| ≤ C(1 + k)` solves the functional equation (the weighted contraction of
  `WeightedBellman`, weight `1 + k`, modulus `β(1 + λ)`). `U` and `f` need only be continuous
  and nondecreasing with `U(f(L)) ≤ A + BL`, which holds when `U ∘ f` is concave
  (`concave_linear_bound`).
* **Exercise 5.8b** (`ex_5_8b`): for `f(L) = L^α` and `U(c) = c^σ/σ`, `0 < α, σ < 1`,
  `v(k) = Ak^{ασ}` with `A > 0` (the sign of `σ`), and the policy `g(k) = θk` is optimal: human
  capital grows at a constant rate. `A` is the fixed point of
  `A ↦ max_x [φ(x)^{ασ}/σ + βAx^{ασ}]`, a contraction of modulus `β(1 + λ)^{ασ}`. For `σ < 0`,
  `U(0) = −∞` and the returns are unbounded below, so part (a) does not apply; that case is not
  covered.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {U f φ : ℝ → ℝ} {δ lam β : ℝ}

/-- `Γ(k) = [(1 − δ)k, (1 + λ)k]` satisfies Assumption 4.3 on `(0, ∞)`. -/
theorem human_assumption43 (hδ0 : 0 < δ) (hδ1 : δ < 1) (hlam : 0 < lam) :
    Assumption43 (humanΓ δ lam) := by
  have hI : (1 - δ) ≤ 1 + lam := by linarith
  have hself : ∀ k : PosR, k ∈ humanΓ δ lam k := fun k =>
    ⟨by nlinarith [k.2], by nlinarith [k.2]⟩
  -- the ratio `y/k` of a feasible pair lies in `I`
  have hratio : ∀ k y : PosR, y ∈ humanΓ δ lam k → y.1 / k.1 ∈ Icc (1 - δ) (1 + lam) :=
    fun k y hy => ⟨(le_div_iff₀ k.2).2 hy.1, (div_le_iff₀ k.2).2 hy.2⟩
  have hmk : ∀ (k : PosR) (x : ℝ), x ∈ Icc (1 - δ) (1 + lam) → 0 < x * k.1 := fun k x hx =>
    mul_pos (by linarith [hx.1]) k.2
  refine ⟨fun k => ⟨k, hself k⟩, fun k => ?_, fun k => ⟨⟨k, hself k⟩, fun y hy ks hks => ?_⟩,
    fun k => ⟨⟨k, hself k⟩, fun ks hks ys hys => ?_⟩⟩
  · -- compact: the image in `ℝ` is `[(1 − δ)k, (1 + λ)k]`
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' humanΓ δ lam k = Icc ((1 - δ) * k.1) ((1 + lam) * k.1) := by
      ext z
      refine ⟨fun ⟨y, hy, hz⟩ => hz ▸ hy, fun hz => ⟨⟨z, ?_⟩, hz, rfl⟩⟩
      exact lt_of_lt_of_le (mul_pos (by linarith) k.2) hz.1
    rw [this]
    exact isCompact_Icc
  · -- l.h.c.: `yₙ = (y/k)kₙ`
    have hx := hratio k y hy
    refine ⟨0, fun n => ⟨y.1 / k.1 * (ks n).1, hmk (ks n) _ hx⟩, fun n _ =>
      ⟨by simp only; nlinarith [(ks n).2, hx.1], by simp only; nlinarith [(ks n).2, hx.2]⟩, ?_⟩
    have := ((continuous_subtype_val.tendsto k).comp hks).const_mul (y.1 / k.1)
    rw [div_mul_cancel₀ _ k.2.ne'] at this
    exact tendsto_subtype_rng.2 this
  · -- u.h.c.: the ratios `yₙ/kₙ` have a convergent subsequence in `I`
    obtain ⟨x, hx, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq
      (x := fun n => (ys n).1 / (ks n).1) fun n => hratio _ _ (hys n)
    refine ⟨⟨x * k.1, hmk k x hx⟩, ⟨by simp only; nlinarith [k.2, hx.1],
      by simp only; nlinarith [k.2, hx.2]⟩, ψ, hψ, ?_⟩
    have hk := ((continuous_subtype_val.tendsto k).comp hks).comp hψ.tendsto_atTop
    have := hlim.mul hk
    refine tendsto_subtype_rng.2 (this.congr fun n => ?_)
    simp only [Function.comp_apply]
    field_simp [(ks (ψ n)).2.ne']

/-- The hypotheses of SLP §5.8 used here. -/
structure HCGrowthHyp (U f φ : ℝ → ℝ) (δ lam β : ℝ) : Prop where
  δ_pos : 0 < δ
  δ_lt : δ < 1
  lam_pos : 0 < lam
  β_pos : 0 < β
  discount : β * (1 + lam) < 1
  φ_cont : ContinuousOn φ (Icc (1 - δ) (1 + lam))
  φ_nonneg : ∀ x ∈ Icc (1 - δ) (1 + lam), 0 ≤ φ x
  φ_le_one : ∀ x ∈ Icc (1 - δ) (1 + lam), φ x ≤ 1
  f_cont : ContinuousOn f (Ici 0)
  f_nonneg : ∀ L, 0 ≤ L → 0 ≤ f L
  f_mono : MonotoneOn f (Ici 0)
  U_cont : ContinuousOn U (Ici 0)
  U_mono : MonotoneOn U (Ici 0)
  lin : ∃ A B, ∀ L, 0 ≤ L → U (f L) ≤ A + B * L

/-- `F(k, y) = U(f[kφ(y/k)])`. -/
noncomputable def hcF (U f φ : ℝ → ℝ) (p : PosR × PosR) : ℝ := U (f (p.1.1 * φ (p.2.1 / p.1.1)))

/-- The weight `1 + k`. -/
def hcW (k : PosR) : ℝ := 1 + k.1

/-- A concave nondecreasing function on `[0, ∞)` lies below a line. -/
theorem concave_linear_bound {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ici 0) g)
    (hm : MonotoneOn g (Ici 0)) : ∃ A B, ∀ L, 0 ≤ L → g L ≤ A + B * L := by
  set s := (g 1 - g (1 / 2)) / (1 / 2)
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.2 (hm (mem_Ici.2 (by norm_num))
    (mem_Ici.2 (by norm_num)) (by norm_num))) (by norm_num)
  refine ⟨g 1, s, fun L hL => ?_⟩
  rcases le_or_gt L 1 with hL1 | hL1
  · have := hm (mem_Ici.2 hL) (mem_Ici.2 zero_le_one) hL1
    nlinarith
  · have hadj := hg.slope_anti_adjacent (x := 1 / 2) (y := 1) (z := L) (mem_Ici.2 (by norm_num))
      (mem_Ici.2 hL) (by norm_num) hL1
    rw [div_le_iff₀ (by linarith)] at hadj
    nlinarith

/-- Under `HCGrowthHyp` the weighted framework applies with weight `1 + k` and modulus
`β(1 + λ)`. -/
theorem hc_weighted (h : HCGrowthHyp U f φ δ lam β) :
    WeightedHyp (humanΓ δ lam) (hcF U f φ) hcW β (β * (1 + lam)) := by
  have hratio : ∀ p ∈ graph (humanΓ δ lam), p.2.1 / p.1.1 ∈ Icc (1 - δ) (1 + lam) :=
    fun p hp => ⟨(le_div_iff₀ p.1.2).2 hp.1, (div_le_iff₀ p.1.2).2 hp.2⟩
  have hL : ∀ p ∈ graph (humanΓ δ lam), p.1.1 * φ (p.2.1 / p.1.1) ∈ Icc 0 p.1.1 := fun p hp =>
    ⟨mul_nonneg p.1.2.le (h.φ_nonneg _ (hratio p hp)),
      mul_le_of_le_one_right p.1.2.le (h.φ_le_one _ (hratio p hp))⟩
  have hxc : ContinuousOn (fun p : PosR × PosR => p.2.1 / p.1.1) (graph (humanΓ δ lam)) :=
    ((continuous_subtype_val.comp continuous_snd).div (continuous_subtype_val.comp continuous_fst)
      fun p => p.1.2.ne').continuousOn
  have hLc : ContinuousOn (fun p : PosR × PosR => p.1.1 * φ (p.2.1 / p.1.1))
      (graph (humanΓ δ lam)) :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.mul (h.φ_cont.comp hxc hratio)
  have hfc := h.f_cont.comp hLc fun p hp => mem_Ici.2 (hL p hp).1
  obtain ⟨A, B, hAB⟩ := h.lin
  refine ⟨human_assumption43 h.δ_pos h.δ_lt h.lam_pos,
    h.U_cont.comp hfc fun p hp => mem_Ici.2 (h.f_nonneg _ (hL p hp).1),
    continuous_const.add continuous_subtype_val, fun k => by simp only [hcW]; linarith [k.2],
    ⟨|U (f 0)| + |A| + |B|, fun p hp => ?_⟩, h.β_pos, h.discount, fun k y hy => ?_⟩
  · -- `U(f(0)) ≤ F ≤ U(f(k)) ≤ A + Bk`
    have hLp := hL p hp
    have hf0 := h.f_nonneg 0 le_rfl
    have hlo : U (f 0) ≤ hcF U f φ p :=
      h.U_mono (mem_Ici.2 hf0) (mem_Ici.2 (h.f_nonneg _ hLp.1))
        (h.f_mono (mem_Ici.2 le_rfl) (mem_Ici.2 hLp.1) hLp.1)
    have hhi : hcF U f φ p ≤ A + B * p.1.1 :=
      (h.U_mono (mem_Ici.2 (h.f_nonneg _ hLp.1)) (mem_Ici.2 (h.f_nonneg _ p.1.2.le))
        (h.f_mono (mem_Ici.2 hLp.1) (mem_Ici.2 p.1.2.le) hLp.2)).trans (hAB _ p.1.2.le)
    have hk := p.1.2
    have hB : B * p.1.1 ≤ |B| * p.1.1 := mul_le_mul_of_nonneg_right (le_abs_self B) hk.le
    have h1 := mul_nonneg (abs_nonneg (U (f 0))) hk.le
    have h2 := mul_nonneg (abs_nonneg A) hk.le
    have h3 := mul_nonneg (abs_nonneg B) hk.le
    have h4 := neg_abs_le (U (f 0))
    have h5 := le_abs_self A
    simp only [hcW]
    rw [abs_le]
    constructor
    · nlinarith [abs_nonneg A, abs_nonneg B]
    · nlinarith [abs_nonneg (U (f 0)), abs_nonneg B]
  · -- `β(1 + y) ≤ β(1 + λ)(1 + k)`
    have hy2 : y.1 ≤ (1 + lam) * k.1 := hy.2
    simp only [hcW]
    nlinarith [h.β_pos, h.lam_pos, k.2]

/-- **Exercise 5.8a.** If `β(1 + λ) < 1`, exactly one continuous `v` with `|v(k)| ≤ C(1 + k)`
solves the functional equation. -/
theorem ex_5_8a (h : HCGrowthHyp U f φ δ lam β) :
    ∃ v : PosR → ℝ, SolvesFE (humanΓ δ lam) (hcF U f φ) β v ∧ Continuous v ∧
      (∃ C, ∀ k, |v k| ≤ C * hcW k) ∧
      ∀ v' : PosR → ℝ, SolvesFE (humanΓ δ lam) (hcF U f φ) β v' → Continuous v' →
        (∃ C, ∀ k, |v' k| ≤ C * hcW k) → v' = v := by
  have : Nonempty PosR := ⟨⟨1, one_pos⟩⟩
  exact weighted_exists_unique (hc_weighted h)

/-! ### Exercise 5.8b: the power case -/

variable {α σ : ℝ}

/-- `k^p ≤ 1 + k` for `0 ≤ p ≤ 1` and `k ≥ 0`. -/
theorem rpow_le_one_add {k p : ℝ} (hk : 0 ≤ k) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : k ^ p ≤ 1 + k := by
  rcases le_or_gt k 1 with hk1 | hk1
  · linarith [Real.rpow_le_one hk hk1 hp0]
  · have := Real.rpow_le_rpow_of_exponent_le hk1.le hp1
    rw [Real.rpow_one] at this
    linarith

/-- The per-unit objective `φ(x)^{ασ}/σ + βAx^{ασ}`. -/
noncomputable def hcObj (φ : ℝ → ℝ) (α σ β A x : ℝ) : ℝ :=
  φ x ^ (α * σ) / σ + β * A * x ^ (α * σ)

/-- `Φ(A) = max_{x ∈ I} [φ(x)^{ασ}/σ + βAx^{ασ}]`. -/
noncomputable def hcPhi (φ : ℝ → ℝ) (δ lam α σ β A : ℝ) : ℝ :=
  sSup (hcObj φ α σ β A '' Icc (1 - δ) (1 + lam))

/-- **Exercise 5.8b.** With `f(L) = L^α`, `U(c) = c^σ/σ`, `0 < α, σ < 1`, `β(1 + λ) < 1` and
`φ(1 − δ) = 1`: there are `A > 0` and `θ ∈ [1 − δ, 1 + λ]` such that `v(k) = Ak^{ασ}` solves the
functional equation, it is the unique solution of part (a), and `y = θk` attains the maximum, so
human capital grows at the constant rate `θ`. -/
theorem ex_5_8b (h : HCGrowthHyp (fun c => c ^ σ / σ) (fun L => L ^ α) φ δ lam β)
    (hφ1 : φ (1 - δ) = 1) (hα0 : 0 < α) (hα1 : α < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ A > 0, ∃ θ ∈ Icc (1 - δ) (1 + lam),
      SolvesFE (humanΓ δ lam) (hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ) β
        (fun k => A * k.1 ^ (α * σ)) ∧
      (∀ v' : PosR → ℝ,
        SolvesFE (humanΓ δ lam) (hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ) β v' →
        Continuous v' → (∃ C, ∀ k, |v' k| ≤ C * hcW k) → v' = fun k => A * k.1 ^ (α * σ)) ∧
      ∀ (k : PosR) (hy : 0 < θ * k.1),
        hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ (k, ⟨θ * k.1, hy⟩) +
          β * (A * (θ * k.1) ^ (α * σ)) = A * k.1 ^ (α * σ) := by
  set p := α * σ
  set I := Icc (1 - δ) (1 + lam)
  have hp0 : 0 < p := mul_pos hα0 hσ0
  have hp1 : p < 1 := by
    have : α * σ < 1 * 1 := mul_lt_mul'' hα1 hσ1 hα0.le hσ0.le
    simpa using this
  have hδ0 := h.δ_pos
  have hδ1 := h.δ_lt
  have hlam := h.lam_pos
  have hβ1 : β < 1 := by nlinarith [h.discount, h.β_pos]
  have hIne : I.Nonempty := nonempty_Icc.2 (by linarith)
  have hIpos : ∀ x ∈ I, 0 < x := fun x hx => by linarith [hx.1]
  -- the per-unit objective and `Φ`
  have hcont : ∀ A, ContinuousOn (hcObj φ α σ β A) I := fun A =>
    ((h.φ_cont.rpow_const fun x hx => Or.inr hp0.le).div_const σ).add
      (continuousOn_const.mul (continuousOn_id.rpow_const fun x _ => Or.inr hp0.le))
  have hbdd : ∀ A, BddAbove (hcObj φ α σ β A '' I) := fun A =>
    (isCompact_Icc.image_of_continuousOn (hcont A)).bddAbove
  have hle : ∀ A, ∀ x ∈ I, hcObj φ α σ β A x ≤ hcPhi φ δ lam α σ β A := fun A x hx =>
    le_csSup (hbdd A) ⟨x, hx, rfl⟩
  have hxp : ∀ x ∈ I, 0 ≤ x ^ p ∧ x ^ p ≤ (1 + lam) ^ p := fun x hx =>
    ⟨Real.rpow_nonneg (hIpos x hx).le _, Real.rpow_le_rpow (hIpos x hx).le hx.2 hp0.le⟩
  have hlip : ∀ A A', hcPhi φ δ lam α σ β A ≤
      hcPhi φ δ lam α σ β A' + β * (1 + lam) ^ p * |A - A'| := fun A A' => by
    refine csSup_le (hIne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hle A' x hx
    obtain ⟨hx0, hx1⟩ := hxp x hx
    have h2 : β * (A - A') * x ^ p ≤ β * (1 + lam) ^ p * |A - A'| := by
      have := mul_le_mul (le_abs_self (A - A')) hx1 hx0 (abs_nonneg _)
      nlinarith [h.β_pos]
    simp only [hcObj] at h1 ⊢
    nlinarith
  -- `Φ` is a contraction of modulus `β(1 + λ)^{ασ}`
  have hρ1 : β * (1 + lam) ^ p < 1 := by
    have : (1 + lam) ^ p ≤ (1 + lam) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hp1.le
    rw [Real.rpow_one] at this
    nlinarith [h.β_pos, h.discount]
  have hcontr : IsContraction (hcPhi φ δ lam α σ β) (β * (1 + lam) ^ p) := by
    refine ⟨mul_pos h.β_pos (Real.rpow_pos_of_pos (by linarith) _), hρ1, fun A A' => ?_⟩
    rw [Real.dist_eq, Real.dist_eq, abs_le]
    have h1 := hlip A A'
    have h2 := hlip A' A
    rw [abs_sub_comm A' A] at h2
    constructor <;> linarith
  obtain ⟨A, hA, -, -⟩ := theorem_3_2 hcontr
  obtain ⟨θ, hθ, hθmax⟩ := isCompact_Icc.exists_isMaxOn hIne (hcont A)
  have hΦθ : hcPhi φ δ lam α σ β A = hcObj φ α σ β A θ :=
    le_antisymm (csSup_le (hIne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hθmax hx))
      (hle A θ hθ)
  -- `A > 0`
  have hApos : 0 < A := by
    have h1 := hle A (1 - δ) ⟨le_rfl, by linarith⟩
    rw [hA] at h1
    simp only [hcObj, hφ1, Real.one_rpow] at h1
    set t := (1 - δ) ^ (α * σ)
    have h2 : t ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hp0.le
    have h3 : 0 < 1 / σ := by positivity
    by_contra hneg
    push Not at hneg
    have h4 : A ≤ A * t := by nlinarith
    have h5 : β * A ≤ β * A * t := by nlinarith [h.β_pos]
    nlinarith [h.β_pos]
  -- the key identity: `F(k, y) + βAy^{ασ} = k^{ασ}[φ(x)^{ασ}/σ + βAx^{ασ}]`, `x = y/k`
  have hkey : ∀ (k y : PosR), y.1 / k.1 ∈ I →
      hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ (k, y) + β * (A * y.1 ^ p) =
        k.1 ^ p * hcObj φ α σ β A (y.1 / k.1) := fun k y hx => by
    have hφ0 := h.φ_nonneg _ hx
    have hk := k.2
    set x := y.1 / k.1
    have hyp : y.1 ^ p = x ^ p * k.1 ^ p := by
      rw [← Real.mul_rpow (hIpos _ hx).le hk.le, div_mul_cancel₀ _ hk.ne']
    simp only [hcF, hcObj]
    rw [← Real.rpow_mul (mul_nonneg hk.le hφ0), Real.mul_rpow hk.le hφ0, hyp]
    ring
  have hratio : ∀ k y : PosR, y ∈ humanΓ δ lam k → y.1 / k.1 ∈ I :=
    fun k y hy => ⟨(le_div_iff₀ k.2).2 hy.1, (div_le_iff₀ k.2).2 hy.2⟩
  have hsolve : SolvesFE (humanΓ δ lam) (hcF (fun c => c ^ σ / σ) (fun L => L ^ α) φ) β
      (fun k => A * k.1 ^ p) := by
    intro k
    have hkp : 0 ≤ k.1 ^ p := Real.rpow_nonneg k.2.le _
    set y : PosR := ⟨θ * k.1, mul_pos (hIpos θ hθ) k.2⟩
    have hyk : y.1 / k.1 = θ := mul_div_cancel_right₀ θ k.2.ne'
    refine ⟨⟨y, ⟨by simp only [y]; nlinarith [hθ.1, k.2], by simp only [y]; nlinarith [hθ.2, k.2]⟩,
      ?_⟩, fun z hz => ?_⟩
    · change A * k.1 ^ p = _ + β * (A * y.1 ^ p)
      rw [hkey k y (hyk ▸ hθ), hyk, ← hΦθ, hA, mul_comm]
    · change _ + β * (A * z.1 ^ p) ≤ A * k.1 ^ p
      rw [hkey k z (hratio k z hz), mul_comm A]
      refine mul_le_mul_of_nonneg_left ?_ hkp
      exact (hle A _ (hratio k z hz)).trans hA.le
  -- uniqueness from part (a)
  obtain ⟨v₀, -, -, -, huniq⟩ := ex_5_8a h
  have hcv : Continuous fun k : PosR => A * k.1 ^ p :=
    continuous_const.mul (continuous_subtype_val.rpow_const fun k => Or.inl k.2.ne')
  have hbv : ∃ C, ∀ k : PosR, |A * k.1 ^ p| ≤ C * hcW k := ⟨A, fun k => by
    rw [abs_of_nonneg (mul_nonneg hApos.le (Real.rpow_nonneg k.2.le _))]
    exact mul_le_mul_of_nonneg_left (rpow_le_one_add k.2.le hp0.le hp1.le) hApos.le⟩
  have hv₀ := huniq _ hsolve hcv hbv
  refine ⟨A, hApos, θ, hθ, hsolve, fun v' hv' hc' hb' => (huniq v' hv' hc' hb').trans hv₀.symm,
    fun k hy => ?_⟩
  have hyk : θ * k.1 / k.1 = θ := mul_div_cancel_right₀ θ k.2.ne'
  rw [hkey k ⟨θ * k.1, hy⟩ (by simp only; rw [hyk]; exact hθ)]
  simp only
  rw [hyk, ← hΦθ, hA, mul_comm]

end StokeyLucasPrescott.DeterministicApplications
