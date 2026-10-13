/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.ConstantReturns

/-!
# Dynamic programs with constant returns to scale

SLP §4.3, pp. 88–91.

* `Assumption410`: `Γ` is nonempty, compact-valued, continuous, has a conical graph, and
  `‖y‖ ≤ α‖x‖` for `y ∈ Γ(x)` with `αβ < 1`. `Assumption411`: `0 < β < 1` and `F` is continuous,
  homogeneous of degree one and `|F(x, y)| ≤ B(‖x‖ + ‖y‖)` on the graph.
* `ex_4_6a`: `‖x_t‖ ≤ αᵗ‖x₀‖` along feasible plans; `ex_4_6b`: Assumptions 4.1–4.2 hold;
  `ex_4_6c`: `|v*(x)| ≤ c‖x‖`.
* `crs` (`T`), `ex_4_7b`: `T` maps `H(X)` into itself; `crs_mono`, `crs_disc`: it is monotone and
  discounts by `αβ`.
* `theorem_4_13`: `T` has a unique fixed point `v ∈ H(X)`, `‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖`, and the
  policy correspondence is nonempty, compact-valued, u.h.c. and homogeneous of degree one.
* `crs_fixed_eq_vstar` (p. 89): `v = v*` by Theorem 4.3; `ex_4_6c_hom`: `v*` is homogeneous.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E} {hX : IsCone X}

/-- **Assumption 4.10.** -/
structure Assumption410 (hX : IsCone X) (Γ : X → Set X) (β α : ℝ) : Prop where
  convex : Convex ℝ X
  nonempty : ∀ x, (Γ x).Nonempty
  compact : ∀ x, IsCompact (Γ x)
  lhc : ∀ x, IsLHC Γ x
  uhc : ∀ x, IsUHC Γ x
  cone : ∀ x, ∀ y ∈ Γ x, ∀ (a : ℝ) (ha : 0 ≤ a), csmul hX ha y ∈ Γ (csmul hX ha x)
  α_pos : 0 < α
  αβ_lt : α * β < 1
  growth : ∀ x, ∀ y ∈ Γ x, ‖y.1‖ ≤ α * ‖x.1‖

/-- **Assumption 4.11.** -/
structure Assumption411 (hX : IsCone X) (Γ : X → Set X) (F : X × X → ℝ) (β B : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  cont : ContinuousOn F (graph Γ)
  hom : ∀ x, ∀ y ∈ Γ x, ∀ (a : ℝ) (ha : 0 ≤ a), F (csmul hX ha x, csmul hX ha y) = a * F (x, y)
  B_pos : 0 < B
  bdd : ∀ x, ∀ y ∈ Γ x, |F (x, y)| ≤ B * (‖x.1‖ + ‖y.1‖)

variable {Γ : X → Set X} {F : X × X → ℝ} {β α B : ℝ}

/-- **Exercise 4.6a.** Along a feasible plan, `‖x_t‖ ≤ αᵗ‖x₀‖`. -/
theorem ex_4_6a (h410 : Assumption410 hX Γ β α) {x₀ : X} {x : ℕ → X}
    (hx : x ∈ Feasible Γ x₀) (t : ℕ) : ‖(x t).1‖ ≤ α ^ t * ‖x₀.1‖ := by
  induction t with
  | zero => simp [hx.1]
  | succ t ih =>
    calc ‖(x (t + 1)).1‖ ≤ α * ‖(x t).1‖ := h410.growth _ _ (hx.2 t)
      _ ≤ α * (α ^ t * ‖x₀.1‖) := mul_le_mul_of_nonneg_left ih h410.α_pos.le
      _ = α ^ (t + 1) * ‖x₀.1‖ := by ring

/-- The bound `|βᵗF(x_t, x_{t+1})| ≤ B(1 + α)‖x₀‖(αβ)ᵗ` along feasible plans. -/
theorem abs_term_le (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {x₀ : X} {x : ℕ → X} (hx : x ∈ Feasible Γ x₀) (t : ℕ) :
    |β ^ t * F (x t, x (t + 1))| ≤ B * (1 + α) * ‖x₀.1‖ * (α * β) ^ t := by
  have h1 := ex_4_6a h410 hx t
  have h2 := ex_4_6a h410 hx (t + 1)
  have hβt : 0 ≤ β ^ t := pow_nonneg h411.β_pos.le t
  rw [abs_mul, abs_of_nonneg hβt]
  calc β ^ t * |F (x t, x (t + 1))| ≤ β ^ t * (B * (‖(x t).1‖ + ‖(x (t + 1)).1‖)) :=
        mul_le_mul_of_nonneg_left (h411.bdd _ _ (hx.2 t)) hβt
    _ ≤ β ^ t * (B * (α ^ t * ‖x₀.1‖ + α ^ (t + 1) * ‖x₀.1‖)) := by
        gcongr; exact h411.B_pos.le
    _ = B * (1 + α) * ‖x₀.1‖ * (α * β) ^ t := by rw [mul_pow, pow_succ]; ring

/-- **Exercise 4.6b.** Under Assumptions 4.10–4.11, Assumptions 4.1–4.2 hold. -/
theorem ex_4_6b (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) :
    Assumption41 Γ ∧ Assumption42 Γ (curryF F) β :=
  ⟨h410.nonempty, assumption42_of_summable_pos fun x₀ x hx =>
    summable_max_of_le_geometric (mul_nonneg h410.α_pos.le h411.β_pos.le) h410.αβ_lt
      (by have := h411.B_pos; have := h410.α_pos; positivity) fun t =>
        (le_abs_self _).trans (abs_term_le h410 h411 hx t)⟩

/-- **Exercise 4.6c.** `|v*(x)| ≤ c‖x‖` with `c = B(1 + α)/(1 − αβ)`. -/
theorem ex_4_6c (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) (x₀ : X) :
    ((-(B * (1 + α) / (1 - α * β) * ‖x₀.1‖) : ℝ) : EReal) ≤ vstar Γ (curryF F) β x₀ ∧
      vstar Γ (curryF F) β x₀ ≤ ((B * (1 + α) / (1 - α * β) * ‖x₀.1‖ : ℝ) : EReal) := by
  set c := B * (1 + α) / (1 - α * β)
  have hαβ : 0 ≤ α * β := mul_nonneg h410.α_pos.le h411.β_pos.le
  have h42 := (ex_4_6b h410 h411).2
  -- partial sums lie in `[−c‖x₀‖, c‖x₀‖]`
  have hps : ∀ x ∈ Feasible Γ x₀, ∀ n, |partialSum (curryF F) β x n| ≤ c * ‖x₀.1‖ := by
    intro x hx n
    have hsum := summable_geometric_of_lt_one hαβ h410.αβ_lt
    calc |partialSum (curryF F) β x n|
        ≤ ∑ t ∈ Finset.range (n + 1), |β ^ t * F (x t, x (t + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range (n + 1), B * (1 + α) * ‖x₀.1‖ * (α * β) ^ t :=
          Finset.sum_le_sum fun t _ => abs_term_le h410 h411 hx t
      _ = B * (1 + α) * ‖x₀.1‖ * ∑ t ∈ Finset.range (n + 1), (α * β) ^ t := by
          rw [Finset.mul_sum]
      _ ≤ B * (1 + α) * ‖x₀.1‖ * ∑' t, (α * β) ^ t := by
          refine mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun t _ => pow_nonneg hαβ t) ?_
          have := h411.B_pos; have := h410.α_pos; positivity
      _ = c * ‖x₀.1‖ := by rw [tsum_geometric_of_lt_one hαβ h410.αβ_lt]; simp only [c]; ring
  have htot : ∀ x ∈ Feasible Γ x₀, ((-(c * ‖x₀.1‖) : ℝ) : EReal) ≤ total (curryF F) β x ∧
      total (curryF F) β x ≤ ((c * ‖x₀.1‖ : ℝ) : EReal) := fun x hx =>
    ⟨ge_of_tendsto' (tendsto_total h42 hx) fun n =>
        EReal.coe_le_coe_iff.2 (neg_le_of_abs_le (hps x hx n)),
      le_of_tendsto' (tendsto_total h42 hx) fun n =>
        EReal.coe_le_coe_iff.2 (le_of_abs_le (hps x hx n))⟩
  obtain ⟨x, hx⟩ := feasible_nonempty h410.nonempty x₀
  exact ⟨(htot x hx).1.trans (le_biSup _ hx), iSup₂_le fun y hy => (htot y hy).2⟩

/-! ### The operator `T` on `H(X)` -/

/-- `(Tf)(x) = max_{y ∈ Γ(x)} [F(x, y) + βf(y)]`. -/
noncomputable def crs (Γ : X → Set X) (F : X × X → ℝ) (β : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  maxValue (obj F β f) Γ x

theorem continuousOn_obj' (h411 : Assumption411 hX Γ F β B) {f : X → ℝ} (hf : Continuous f) :
    ContinuousOn (obj F β f) (graph Γ) :=
  h411.cont.add (continuousOn_const.mul (hf.comp continuous_snd).continuousOn)

theorem exists_crs_argmax (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f : X → ℝ} (hf : Continuous f) (x : X) :
    ∃ y ∈ Γ x, crs Γ F β f x = F (x, y) + β * f y ∧
      ∀ z ∈ Γ x, F (x, z) + β * f z ≤ crs Γ F β f x := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_obj' h411 hf) (h410.compact x)
    (h410.nonempty x)
  exact ⟨y, hy, hval.symm, fun z hz => (hmax z hz).trans_eq hval⟩

/-- `Γ(0) = {0}`: the only feasible successor of the origin is the origin. -/
theorem eq_zero_of_mem_zero (h410 : Assumption410 hX Γ β α) {x y : X} (hx : x.1 = 0)
    (hy : y ∈ Γ x) : y.1 = 0 := by
  have := h410.growth x y hy
  rw [hx, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- **Exercise 4.7b.** Under Assumptions 4.10–4.11, `T` maps `H(X)` into itself. -/
theorem ex_4_7b (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) {f : X → ℝ}
    (hf : InH hX f) : InH hX (crs Γ F β f) := by
  refine ⟨(theorem_3_6 (continuousOn_obj' h411 hf.1) h410.compact h410.lhc h410.uhc).1,
    fun x a ha => ?_, B * (1 + α) + β * α * hnorm X f, fun x => ?_⟩
  · -- homogeneity
    obtain ⟨y, hy, hval, hmax⟩ := exists_crs_argmax h410 h411 hf.1 x
    obtain ⟨z, hz, hzval, hzmax⟩ := exists_crs_argmax h410 h411 hf.1 (csmul hX ha x)
    rcases ha.eq_or_lt with rfl | hpos
    · -- `Γ(0) = {0}` and `F(0, 0) = 0`
      have hz0 : z.1 = 0 := eq_zero_of_mem_zero h410 (by simp [csmul]) hz
      have hzeq : z = csmul hX le_rfl y := Subtype.ext (by simp [csmul, hz0])
      rw [hzval, hzeq, h411.hom x y hy, hf.2.1]
      ring
    · refine le_antisymm ?_ ?_
      · -- pull the maximizer back to `x`
        have hinv : 0 ≤ a⁻¹ := inv_nonneg.2 hpos.le
        have hz' : csmul hX hinv z ∈ Γ x := by
          have := h410.cone _ z hz a⁻¹ hinv
          have e : csmul hX hinv (csmul hX hpos.le x) = x := Subtype.ext (by
            simp [csmul, smul_smul, inv_mul_cancel₀ hpos.ne'])
          rwa [e] at this
        have hle := hmax _ hz'
        have e1 : csmul hX hpos.le (csmul hX hinv z) = z := Subtype.ext (by
          simp [csmul, smul_smul, mul_inv_cancel₀ hpos.ne'])
        have hF := h411.hom x _ hz' a hpos.le
        have hfz := hf.2.1 (csmul hX hinv z) a hpos.le
        rw [e1] at hF hfz
        rw [hzval, hF, hfz]
        nlinarith
      · have hF := h411.hom x y hy a hpos.le
        have hfy := hf.2.1 y a hpos.le
        have := hzmax _ (h410.cone x y hy a hpos.le)
        rw [hF, hfy] at this
        rw [hval]
        nlinarith
  · -- the bound `|Tf(x)| ≤ (B(1 + α) + βα‖f‖)‖x‖`
    obtain ⟨y, hy, hval, -⟩ := exists_crs_argmax h410 h411 hf.1 x
    have hy' := h410.growth x y hy
    have hfy := abs_le_hnorm hf y
    have hB := h411.bdd x y hy
    rw [hval]
    have hβ := h411.β_pos
    have hn := hnorm_nonneg (X := X) f
    calc |F (x, y) + β * f y| ≤ |F (x, y)| + β * |f y| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_pos hβ]
      _ ≤ B * (‖x.1‖ + α * ‖x.1‖) + β * (hnorm X f * (α * ‖x.1‖)) := by
          gcongr
          · exact hB.trans (mul_le_mul_of_nonneg_left (by linarith) h411.B_pos.le)
          · exact hfy.trans (mul_le_mul_of_nonneg_left hy' hn)
      _ = (B * (1 + α) + β * α * hnorm X f) * ‖x.1‖ := by ring

/-- `T` is monotone. -/
theorem crs_mono (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hfg : f ≤ g) :
    crs Γ F β f ≤ crs Γ F β g := fun x => by
  obtain ⟨y, hy, hval, -⟩ := exists_crs_argmax h410 h411 hf x
  obtain ⟨-, -, -, hmax⟩ := exists_crs_argmax h410 h411 hg x
  rw [hval]
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hfg y) h411.β_pos.le)).trans (hmax y hy)

/-- `T(f + a‖·‖) ≤ Tf + αβa‖·‖` (p. 91). -/
theorem crs_disc (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f : X → ℝ} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a) :
    crs Γ F β (fun x => f x + a * ‖x.1‖) ≤ fun x => crs Γ F β f x + α * β * a * ‖x.1‖ :=
  fun x => by
    have hc : Continuous fun x : X => f x + a * ‖x.1‖ :=
      hf.add (continuous_const.mul continuous_subtype_val.norm)
    obtain ⟨y, hy, hval, -⟩ := exists_crs_argmax h410 h411 hc x
    obtain ⟨-, -, -, hmax⟩ := exists_crs_argmax h410 h411 hf x
    rw [hval]
    have h1 := hmax y hy
    have h2 := mul_le_mul_of_nonneg_left (h410.growth x y hy) (mul_nonneg h411.β_pos.le ha)
    dsimp only
    nlinarith

/-- `T` is a contraction of modulus `αβ` on `H(X)` (Theorem 4.12). -/
theorem crs_contraction (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {f g : X → ℝ} (hf : InH hX f) (hg : InH hX g) :
    hnorm X (crs Γ F β f - crs Γ F β g) ≤ α * β * hnorm X (f - g) :=
  theorem_4_12 (mul_nonneg h410.α_pos.le h411.β_pos.le)
    (fun _ _ hf hg hfg => crs_mono h410 h411 hf.1 hg.1 hfg)
    (fun _ hf _ ha => crs_disc h410 h411 hf.1 ha) hf hg

/-- The triangle inequality for `‖f − h‖` on `H(X)`. -/
theorem hnorm_sub_le {f g h : X → ℝ} (hf : InH hX f) (hg : InH hX g) (hh : InH hX h) :
    hnorm X (f - h) ≤ hnorm X (f - g) + hnorm X (g - h) := by
  have := (ex_4_7a_norm (inH_sub hf hg) (inH_sub hg hh) 1).2.2.2
  rwa [sub_add_sub_cancel] at this

/-- **Theorem 4.13.** Under Assumptions 4.10–4.11, `T` has a unique fixed point `v ∈ H(X)`,
`‖Tⁿv₀ − v‖ ≤ (αβ)ⁿ‖v₀ − v‖` for `v₀ ∈ H(X)`, and the policy correspondence `G` is nonempty,
compact-valued, u.h.c. and homogeneous of degree one. -/
theorem theorem_4_13 (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) :
    ∃ v, InH hX v ∧ crs Γ F β v = v ∧ (∀ w, InH hX w → crs Γ F β w = w → w = v) ∧
      (∀ v₀, InH hX v₀ → ∀ n : ℕ,
        hnorm X ((crs Γ F β)^[n] v₀ - v) ≤ (α * β) ^ n * hnorm X (v₀ - v)) ∧
      (∀ x, (argmax (obj F β v) Γ x).Nonempty ∧ IsCompact (argmax (obj F β v) Γ x) ∧
        IsUHC (argmax (obj F β v) Γ) x) ∧
      ∀ x y (a : ℝ) (ha : 0 ≤ a), y ∈ argmax (obj F β v) Γ x →
        csmul hX ha y ∈ argmax (obj F β v) Γ (csmul hX ha x) := by
  set T := crs Γ F β
  set γ := α * β
  have hγ0 : 0 ≤ γ := mul_nonneg h410.α_pos.le h411.β_pos.le
  have hγ1 : γ < 1 := h410.αβ_lt
  have hTH : ∀ f, InH hX f → InH hX (T f) := fun f hf => ex_4_7b h410 h411 hf
  -- the iterates from `0`
  have h0 : InH hX (0 : X → ℝ) := ⟨continuous_const, fun _ _ _ => by simp, 0, fun _ => by simp⟩
  set fs : ℕ → X → ℝ := fun n => T^[n] 0
  have hfs : ∀ n, InH hX (fs n) := fun n => by
    induction n with
    | zero => exact h0
    | succ n ih => simp only [fs, Function.iterate_succ_apply']; exact hTH _ ih
  have hstep : ∀ n, hnorm X (fs (n + 1) - fs n) ≤ γ ^ n * hnorm X (fs 1 - fs 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : fs (n + 1 + 1) = T (fs (n + 1)) := Function.iterate_succ_apply' _ _ _
      have e2 : fs (n + 1) = T (fs n) := Function.iterate_succ_apply' _ _ _
      rw [e1, e2]
      calc hnorm X (T (T (fs n)) - T (fs n)) ≤ γ * hnorm X (T (fs n) - fs n) :=
            crs_contraction h410 h411 (e2 ▸ hfs (n + 1)) (hfs n)
        _ ≤ γ * (γ ^ n * hnorm X (fs 1 - fs 0)) := by
            rw [← e2]; exact mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * hnorm X (fs 1 - fs 0) := by ring
  -- Cauchy: `‖f_m − f_n‖ ≤ γⁿ/(1 − γ) ‖f₁ − f₀‖`
  have hgap : ∀ n k, hnorm X (fs (n + k) - fs n) ≤
      γ ^ n / (1 - γ) * hnorm X (fs 1 - fs 0) := by
    intro n k
    have hd := hnorm_nonneg (X := X) (fs 1 - fs 0)
    have hsum : ∀ k, hnorm X (fs (n + k) - fs n) ≤
        ∑ i ∈ Finset.range k, γ ^ (n + i) * hnorm X (fs 1 - fs 0) := by
      intro k
      induction k with
      | zero => simp [hnorm]
      | succ k ih =>
        rw [Finset.sum_range_succ]
        calc hnorm X (fs (n + (k + 1)) - fs n)
            ≤ hnorm X (fs (n + k + 1) - fs (n + k)) + hnorm X (fs (n + k) - fs n) :=
              hnorm_sub_le (hfs _) (hfs _) (hfs _)
          _ ≤ γ ^ (n + k) * hnorm X (fs 1 - fs 0) +
              ∑ i ∈ Finset.range k, γ ^ (n + i) * hnorm X (fs 1 - fs 0) :=
              add_le_add (hstep _) ih
          _ = _ := by ring
    refine (hsum k).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hd
    simp only [pow_add, ← Finset.mul_sum]
    rw [div_eq_mul_inv, ← tsum_geometric_of_lt_one hγ0 hγ1]
    exact mul_le_mul_of_nonneg_left ((summable_geometric_of_lt_one hγ0 hγ1).sum_le_tsum _
      fun i _ => pow_nonneg hγ0 i) (pow_nonneg hγ0 n)
  have hgeo : Tendsto (fun n => γ ^ n / (1 - γ) * hnorm X (fs 1 - fs 0)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).div_const (1 - γ)).mul_const
      (hnorm X (fs 1 - fs 0))
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hnorm X (fs m - fs n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hgeo).2 (ε / 2) (half_pos hε))
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmN : hnorm X (fs m - fs N) < ε / 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact (hgap N k).trans_lt (hN N le_rfl)
    have hnN : hnorm X (fs N - fs n) < ε / 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      have hsym := (ex_4_7a_norm (inH_sub (hfs (N + k)) (hfs N)) h0 (-1)).2.2.1
      rw [abs_neg, abs_one, one_mul, neg_smul, one_smul, neg_sub] at hsym
      rw [hsym]
      exact (hgap N k).trans_lt (hN N le_rfl)
    calc hnorm X (fs m - fs n) ≤ hnorm X (fs m - fs N) + hnorm X (fs N - fs n) :=
          hnorm_sub_le (hfs _) (hfs _) (hfs _)
      _ < ε := by linarith
  obtain ⟨v, hvH, hlim⟩ := ex_4_7a_complete hfs hcauchy
  -- `v` is a fixed point
  have hTv : T v = v := by
    have hb : ∀ n, hnorm X (T v - v) ≤ γ * hnorm X (fs n - v) + hnorm X (fs (n + 1) - v) := by
      intro n
      have e : fs (n + 1) = T (fs n) := Function.iterate_succ_apply' _ _ _
      calc hnorm X (T v - v) ≤ hnorm X (T v - fs (n + 1)) + hnorm X (fs (n + 1) - v) :=
            hnorm_sub_le (hTH v hvH) (hfs _) hvH
        _ ≤ γ * hnorm X (fs n - v) + hnorm X (fs (n + 1) - v) := by
            refine add_le_add ?_ le_rfl
            have hsym := (ex_4_7a_norm (inH_sub (hTH _ (hfs n)) (hTH v hvH)) h0 (-1)).2.2.1
            rw [abs_neg, abs_one, one_mul, neg_smul, one_smul, neg_sub] at hsym
            rw [e, hsym]
            exact crs_contraction h410 h411 (hfs n) hvH
    have hlim2 : Tendsto (fun n => γ * hnorm X (fs n - v) + hnorm X (fs (n + 1) - v)) atTop
        (𝓝 0) := by
      simpa using (hlim.const_mul γ).add (hlim.comp (tendsto_add_atTop_nat 1))
    have hz : hnorm X (T v - v) = 0 :=
      le_antisymm (ge_of_tendsto' hlim2 hb) (hnorm_nonneg _)
    exact sub_eq_zero.1 ((ex_4_7a_norm (inH_sub (hTH v hvH) hvH) h0 1).2.1.1 hz)
  -- uniqueness
  have huniq : ∀ w, InH hX w → T w = w → w = v := fun w hw hTw => by
    have h1 := crs_contraction h410 h411 hw hvH
    change hnorm X (T w - T v) ≤ _ at h1
    rw [hTw, hTv] at h1
    have hz : hnorm X (w - v) = 0 := by
      nlinarith [hnorm_nonneg (X := X) (w - v)]
    exact sub_eq_zero.1 ((ex_4_7a_norm (inH_sub hw hvH) h0 1).2.1.1 hz)
  refine ⟨v, hvH, hTv, huniq, fun v₀ hv₀ n => ?_, fun x => ?_, fun x y a ha hy => ?_⟩
  · -- the rate
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : InH hX (T^[n] v₀) := by
        clear ih
        induction n with
        | zero => exact hv₀
        | succ n ihn => rw [Function.iterate_succ_apply']; exact hTH _ ihn
      rw [Function.iterate_succ_apply']
      conv_lhs => rw [← hTv]
      calc hnorm X (T (T^[n] v₀) - T v) ≤ γ * hnorm X (T^[n] v₀ - v) :=
            crs_contraction h410 h411 hn hvH
        _ ≤ γ * (γ ^ n * hnorm X (v₀ - v)) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * hnorm X (v₀ - v) := by ring
  · exact (theorem_3_6 (continuousOn_obj' h411 hvH.1) h410.compact h410.lhc h410.uhc).2 x
  · -- homogeneity of `G`
    refine ⟨h410.cone x y hy.1 a ha, ?_⟩
    have hvx : v x = maxValue (obj F β v) Γ x := (congrFun hTv x).symm
    have hvax : v (csmul hX ha x) = maxValue (obj F β v) Γ (csmul hX ha x) :=
      (congrFun hTv _).symm
    rw [← hvax, hvH.2.1, hvx, ← hy.2]
    simp only [obj, h411.hom x y hy.1 a ha, hvH.2.1]
    ring

/-! ### The fixed point is the supremum function (p. 89) -/

/-- A fixed point of `T` in `H(X)` satisfies (FE) in `R̄`. -/
theorem satisfiesFE_crs (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {v : X → ℝ} (hvH : InH hX v) (hv : crs Γ F β v = v) :
    SatisfiesFE Γ (curryF F) β fun x => (v x : EReal) := by
  intro x
  obtain ⟨y, hy, hval, hmax⟩ := exists_crs_argmax h410 h411 hvH.1 x
  rw [hv] at hval hmax
  change (v x : EReal) = ⨆ y ∈ Γ x, ((curryF F x y : ℝ) : EReal) + (β : EReal) * (v y : EReal)
  refine le_antisymm ?_ (iSup₂_le fun z hz => ?_)
  · have := le_biSup (fun z => ((curryF F x z : ℝ) : EReal) + (β : EReal) * (v z : EReal)) hy
    refine le_trans ?_ this
    rw [hval, curryF, ← EReal.coe_mul, ← EReal.coe_add]
  · rw [curryF, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (hmax z hz)

/-- **p. 89.** Under Assumptions 4.10–4.11 the fixed point of `T` in `H(X)` is `v*`: along
feasible plans `|βⁿv(xₙ)| ≤ ‖v‖(αβ)ⁿ‖x₀‖ → 0`, so Theorem 4.3 applies. -/
theorem crs_fixed_eq_vstar (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B)
    {v : X → ℝ} (hvH : InH hX v) (hv : crs Γ F β v = v) :
    (fun x => (v x : EReal)) = vstar Γ (curryF F) β := by
  obtain ⟨h41, h42⟩ := ex_4_6b h410 h411
  refine theorem_4_3 h411.β_pos.le h41 h42 (satisfiesFE_crs h410 h411 hvH hv) fun x₀ x hx => ?_
  have hαβ : 0 ≤ α * β := mul_nonneg h410.α_pos.le h411.β_pos.le
  have hb : Tendsto (fun n => β ^ n * v (x n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => hnorm X v * ‖x₀.1‖ * (α * β) ^ n) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h411.β_pos.le n)]
      calc β ^ n * |v (x n)| ≤ β ^ n * (hnorm X v * (α ^ n * ‖x₀.1‖)) :=
            mul_le_mul_of_nonneg_left ((abs_le_hnorm hvH _).trans (mul_le_mul_of_nonneg_left
              (ex_4_6a h410 hx n) (hnorm_nonneg v))) (pow_nonneg h411.β_pos.le n)
        _ = hnorm X v * ‖x₀.1‖ * (α * β) ^ n := by rw [mul_pow]; ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hαβ h410.αβ_lt).const_mul
        (hnorm X v * ‖x₀.1‖)
  simpa only [EReal.coe_mul, EReal.coe_zero] using EReal.tendsto_coe.2 hb

/-- **Exercise 4.6c (homogeneity).** `v*` is homogeneous of degree one and real-valued, with
`|v*(x)| ≤ c‖x‖` (`ex_4_6c`): it is the fixed point of Theorem 4.13. -/
theorem ex_4_6c_hom (h410 : Assumption410 hX Γ β α) (h411 : Assumption411 hX Γ F β B) :
    ∃ v : X → ℝ, InH hX v ∧ vstar Γ (curryF F) β = fun x => (v x : EReal) := by
  obtain ⟨v, hvH, hv, -⟩ := theorem_4_13 h410 h411
  exact ⟨v, hvH, (crs_fixed_eq_vstar h410 h411 hvH hv).symm⟩

end StokeyLucasPrescott.DeterministicDP
