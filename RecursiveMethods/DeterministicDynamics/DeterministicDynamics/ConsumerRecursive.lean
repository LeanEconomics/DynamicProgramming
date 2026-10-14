/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.RecursivePreferences
import DeterministicDynamics.Envelope

/-!
# The consumer with recursive preferences

SLP §5.12, pp. 116–117: with prices `p ∈ ℝˡ₊₊`, `R = 1/(1 + r)` and wealth `A ≥ 0`, the
functional equation is `v(A) = max_{C ∈ Γ(A)} W(C, v[R⁻¹(A − p·C)])`,
`Γ(A) = {C ∈ ℝˡ₊ : p·C ≤ A}`.

* `budget_compact`, `budget_lhc`, `budget_uhc`: `Γ` is compact-valued and continuous.
* **Exercise 5.12b**: `ex_5_12b`: there is a unique bounded continuous solution `v`. With `W`
  concave and nonnegative and strictly concave in `C`, `v` is concave and demand
  `C = φ(p, A)` is a single-valued continuous function (`ex_5_12b_demand`); demand is
  homogeneous of degree zero in `(p, A)` (`ex_5_12b_homogeneous`).
* **Exercise 5.12c**: `ex_5_12c_envelope`: at an interior optimum (`C_i > 0`), `v` is
  differentiable with `v'(A) = W_{C_i}/p_i`, the marginal utility of a dollar spent on good `i`;
  so `W_{C_i}/p_i = W_{C_j}/p_j` for goods consumed (`ex_5_12c_intratemporal`), and
  `ex_5_12c_euler`: a dollar spent today on good `i` is worth what it buys tomorrow,
  `W_{C_i}/p_i = R⁻¹W_z·v'(A')`.
* **Exercise 5.12d**: `ex_5_12d`: with `h` strictly increasing, `W̃(C, a) = h(W[C, h⁻¹(a)])` gives
  the value `h ∘ v` and the same demand. `ex_5_12d_not_aggregator`: `W̃` need not be an aggregator:
  `W(C, z) = z/2` and `h(x) = x/(1 + x)` give `W̃(a) = a/(2 − a)`, which violates (W3).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ}

/-- Wealth `A ≥ 0`. -/
abbrev Wealth := ↥(Ici (0 : ℝ))

/-- `p·C`. -/
def spend (p C : Fin l → ℝ) : ℝ := ∑ i, p i * C i

/-- `Γ(A) = {C ≥ 0 : p·C ≤ A}`. -/
def budgetΓ (p : Fin l → ℝ) (A : Wealth) : Set (Fin l → ℝ) := {C | 0 ≤ C ∧ spend p C ≤ A.1}

/-- Next period's wealth `R⁻¹(A − p·C)`. -/
noncomputable def nextWealth (p : Fin l → ℝ) (R : ℝ) (A : ℝ) (C : Fin l → ℝ) : ℝ :=
  (A - spend p C) / R

/-- `v` on wealth extended to `ℝ` by `v(max{x, 0})`. -/
def vext (v : Wealth → ℝ) (x : ℝ) : ℝ := v ⟨max x 0, mem_Ici.2 (le_max_right _ _)⟩

theorem vext_of_nonneg (v : Wealth → ℝ) {x : ℝ} (hx : 0 ≤ x) : vext v x = v ⟨x, hx⟩ := by
  simp only [vext, max_eq_left hx]

theorem continuous_vext {v : Wealth → ℝ} (hv : Continuous v) : Continuous (vext v) :=
  hv.comp ((continuous_id.max continuous_const).subtype_mk _)

theorem abs_vext_le (v : Wealth →ᵇ ℝ) (x : ℝ) : |vext v x| ≤ ‖v‖ := by
  unfold vext
  simpa [Real.norm_eq_abs] using v.norm_coe_le_norm _

theorem continuous_spend (p : Fin l → ℝ) : Continuous (spend p) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

theorem spend_nonneg {p C : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hC : 0 ≤ C) : 0 ≤ spend p C :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp i).le (hC i)

theorem le_div_of_spend {p C : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hC : 0 ≤ C) {A : ℝ}
    (hs : spend p C ≤ A) (i : Fin l) : C i ≤ A / p i := by
  rw [le_div_iff₀ (hp i), mul_comm]
  exact (Finset.single_le_sum (f := fun j => p j * C j)
    (fun j _ => mul_nonneg (hp j).le (hC j)) (Finset.mem_univ i)).trans hs

theorem norm_le_of_budget {p C : Fin l → ℝ} (hp : ∀ i, 0 < p i) (hC : 0 ≤ C) {A : ℝ}
    (hA : 0 ≤ A) (hs : spend p C ≤ A) : ‖C‖ ≤ ∑ j, A / p j := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => div_nonneg hA (hp j).le)).2
    fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hC i)]
  exact (le_div_of_spend hp hC hs i).trans (Finset.single_le_sum
    (f := fun j => A / p j) (fun j _ => div_nonneg hA (hp j).le) (Finset.mem_univ i))

theorem budget_compact {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (A : Wealth) :
    IsCompact (budgetΓ p A) := by
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_le continuous_const continuous_id).inter
    (isClosed_le (continuous_spend p) continuous_const)) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin l → ℝ)) (r := ∑ j, A.1 / p j)).subset
    fun C hC => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_budget hp hC.1 A.2 hC.2

theorem zero_mem_budget (p : Fin l → ℝ) (A : Wealth) : (0 : Fin l → ℝ) ∈ budgetΓ p A :=
  ⟨le_rfl, by simp [spend, A.2.out]⟩

theorem budget_lhc {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (A : Wealth) : IsLHC (budgetΓ p) A := by
  refine ⟨⟨0, zero_mem_budget p A⟩, fun C hC As hAs => ?_⟩
  have hval := (continuous_subtype_val.tendsto A).comp hAs
  rcases eq_or_lt_of_le A.2.out with hA0 | hApos
  · -- `A = 0` forces `C = 0`
    have hC0 : C = 0 := by
      funext i
      have := le_div_of_spend hp hC.1 hC.2 i
      rw [← hA0, zero_div] at this
      exact le_antisymm this (hC.1 i)
    refine ⟨0, fun _ => 0, fun n _ => zero_mem_budget p _, ?_⟩
    rw [hC0]; exact tendsto_const_nhds
  · -- `Cₙ = min{1, Aₙ/A}·C`
    refine ⟨0, fun n => min 1 ((As n).1 / A.1) • C, fun n _ => ⟨?_, ?_⟩, ?_⟩
    · exact smul_nonneg (le_min zero_le_one (div_nonneg (As n).2.out A.2.out)) hC.1
    · have hlam0 : 0 ≤ min 1 ((As n).1 / A.1) := le_min zero_le_one (div_nonneg (As n).2.out
        A.2.out)
      have e : spend p (min 1 ((As n).1 / A.1) • C) = min 1 ((As n).1 / A.1) * spend p C := by
        simp only [spend, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      calc min 1 ((As n).1 / A.1) * spend p C ≤ min 1 ((As n).1 / A.1) * A.1 :=
            mul_le_mul_of_nonneg_left hC.2 hlam0
        _ ≤ (As n).1 / A.1 * A.1 := mul_le_mul_of_nonneg_right (min_le_right _ _) A.2.out
        _ = (As n).1 := div_mul_cancel₀ _ hApos.ne'
    · have h1 : Tendsto (fun n => min 1 ((As n).1 / A.1)) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).min (hval.div_const A.1)
        rwa [div_self hApos.ne', min_self] at this
      simpa using h1.smul_const C

theorem budget_uhc {p : Fin l → ℝ} (hp : ∀ i, 0 < p i) (A : Wealth) : IsUHC (budgetΓ p) A := by
  refine ⟨⟨0, zero_mem_budget p A⟩, fun As hAs Cs hCs => ?_⟩
  have hval := (continuous_subtype_val.tendsto A).comp hAs
  obtain ⟨B, hB⟩ := hval.bddAbove_range
  have hB0 : 0 ≤ B := (As 0).2.out.trans (hB ⟨0, rfl⟩)
  have hmem : ∀ n, Cs n ∈ Metric.closedBall (0 : Fin l → ℝ) (∑ j, B / p j) := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_of_budget hp (hCs n).1 (As n).2.out (hCs n).2).trans
      (Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hB ⟨n, rfl⟩) (hp j).le)
  obtain ⟨C, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  refine ⟨C, ⟨?_, ?_⟩, φ, hφ, hlim⟩
  · exact isClosed_le continuous_const continuous_id |>.mem_of_tendsto hlim
      (Eventually.of_forall fun n => (hCs (φ n)).1)
  · exact le_of_tendsto_of_tendsto (((continuous_spend p).tendsto C).comp hlim)
      (hval.comp hφ.tendsto_atTop) (Eventually.of_forall fun n => (hCs (φ n)).2)

/-! ### The operator -/

/-- The hypotheses for the consumer: prices, interest and an aggregator with (W1)–(W3). -/
structure ConsHyp (W : (Fin l → ℝ) → ℝ → ℝ) (p : Fin l → ℝ) (R β M : ℝ) : Prop where
  p_pos : ∀ i, 0 < p i
  R_pos : 0 < R
  β_pos : 0 < β
  β_lt : β < 1
  cont : Continuous fun q : (Fin l → ℝ) × ℝ => W q.1 q.2
  bdd : ∀ C, 0 ≤ C → |W C 0| ≤ M
  lip : ∀ C, 0 ≤ C → ∀ z z', |W C z - W C z'| ≤ β * |z - z'|

variable {W : (Fin l → ℝ) → ℝ → ℝ} {p : Fin l → ℝ} {R β M : ℝ}

/-- The objective `W(C, v[R⁻¹(A − p·C)])`. -/
noncomputable def consObj (W : (Fin l → ℝ) → ℝ → ℝ) (p : Fin l → ℝ) (R : ℝ) (v : Wealth → ℝ)
    (q : Wealth × (Fin l → ℝ)) : ℝ :=
  W q.2 (vext v (nextWealth p R q.1.1 q.2))

theorem continuous_consObj (h : ConsHyp W p R β M) {v : Wealth → ℝ} (hv : Continuous v) :
    Continuous (consObj W p R v) :=
  h.cont.comp (continuous_snd.prodMk ((continuous_vext hv).comp
    (((continuous_subtype_val.comp continuous_fst).sub ((continuous_spend p).comp
      continuous_snd)).div_const R)))

theorem abs_consObj_le (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) {A : Wealth}
    {C : Fin l → ℝ} (hC : C ∈ budgetΓ p A) : |consObj W p R v (A, C)| ≤ M + β * ‖v‖ := by
  have h1 := h.lip C hC.1 (vext v (nextWealth p R A.1 C)) 0
  have h2 := h.bdd C hC.1
  have h3 : |vext v (nextWealth p R A.1 C)| ≤ ‖v‖ := abs_vext_le v _
  rw [sub_zero] at h1
  have := abs_sub_abs_le_abs_sub (W C (vext v (nextWealth p R A.1 C))) (W C 0)
  simp only [consObj]
  nlinarith [h.β_pos]

theorem consMax_le (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    ‖maxValue (consObj W p R v) (budgetΓ p) A‖ ≤ M + β * ‖v‖ := by
  obtain ⟨C, hC, hval, -⟩ := exists_argmax (continuous_consObj h v.continuous).continuousOn
    (budget_compact h.p_pos A) ⟨0, zero_mem_budget p A⟩
  rw [← hval, Real.norm_eq_abs]
  exact abs_consObj_le h v hC

/-- `(Tv)(A) = max_{C ∈ Γ(A)} W(C, v[R⁻¹(A − p·C)])`. -/
noncomputable def consT (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) : Wealth →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun A => maxValue (consObj W p R v) (budgetΓ p) A)
    (theorem_3_6 (continuous_consObj h v.continuous).continuousOn (budget_compact h.p_pos)
      (budget_lhc h.p_pos) (budget_uhc h.p_pos)).1 (M + β * ‖v‖) (consMax_le h v)

theorem exists_consT_argmax (h : ConsHyp W p R β M) (v : Wealth →ᵇ ℝ) (A : Wealth) :
    ∃ C ∈ budgetΓ p A, consT h v A = consObj W p R v (A, C) ∧
      ∀ C' ∈ budgetΓ p A, consObj W p R v (A, C') ≤ consT h v A := by
  obtain ⟨C, hC, hval, hmax⟩ := exists_argmax (continuous_consObj h v.continuous).continuousOn
    (budget_compact h.p_pos A) ⟨0, zero_mem_budget p A⟩
  exact ⟨C, hC, hval.symm, fun C' hC' => (hmax C' hC').trans_eq hval⟩

theorem consT_contraction (h : ConsHyp W p R β M) : IsContraction (consT h) β := by
  refine ⟨h.β_pos, h.β_lt, fun v v' => (dist_le (mul_nonneg h.β_pos.le dist_nonneg)).2 fun A => ?_⟩
  obtain ⟨C, hC, hval, -⟩ := exists_consT_argmax h v A
  obtain ⟨C', hC', hval', -⟩ := exists_consT_argmax h v' A
  obtain ⟨-, -, -, hmax⟩ := exists_consT_argmax h v A
  obtain ⟨-, -, -, hmax'⟩ := exists_consT_argmax h v' A
  have hd : ∀ x, |vext v x - vext v' x| ≤ dist v v' := fun x => by
    simpa [Real.dist_eq, vext] using
      dist_coe_le_dist (f := v) (g := v') ⟨max x 0, mem_Ici.2 (le_max_right _ _)⟩
  have e1 := hmax C' hC'
  have e2 := hmax' C hC
  have l1 := h.lip C hC.1 (vext v (nextWealth p R A.1 C)) (vext v' (nextWealth p R A.1 C))
  have l2 := h.lip C' hC'.1 (vext v (nextWealth p R A.1 C')) (vext v' (nextWealth p R A.1 C'))
  have d1 := mul_le_mul_of_nonneg_left (hd (nextWealth p R A.1 C)) h.β_pos.le
  have d2 := mul_le_mul_of_nonneg_left (hd (nextWealth p R A.1 C')) h.β_pos.le
  rw [Real.dist_eq, abs_le]
  simp only [consObj] at hval hval' e1 e2
  constructor
  · rw [abs_le] at l2; linarith [l2.1, l2.2]
  · rw [abs_le] at l1; linarith [l1.1, l1.2]

/-- **Exercise 5.12b.** There is a unique bounded continuous solution `v` of (2). -/
theorem ex_5_12b (h : ConsHyp W p R β M) :
    ∃ v : Wealth →ᵇ ℝ, consT h v = v ∧ ∀ w, consT h w = w → w = v := by
  have : Nonempty (Wealth →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (consT_contraction h)
  exact ⟨v, hv, huniq⟩

/-! ### Concavity and demand -/

/-- With `W` concave and nonnegative on `ℝˡ₊ × ℝ₊`, `T` preserves nonnegative concave functions,
and the fixed point is nonnegative and concave. -/
theorem ex_5_12b_concave (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v) :
    (∀ A, 0 ≤ v A) ∧ IsConcaveS (convex_Ici 0) v := by
  have : Nonempty (Wealth →ᵇ ℝ) := ⟨0⟩
  have hWz : ∀ C, 0 ≤ C → MonotoneOn (W C) (Ici 0) := fun C hC => by
    refine monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
      fun z hz => hnn C z hC hz
    have := hconc.2 (show (C, z) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz⟩)
      (show (C, z') ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz'⟩) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at this
    exact this
  set S : Set (Wealth →ᵇ ℝ) := {u | (∀ A, 0 ≤ u A) ∧ IsConcaveS (convex_Ici 0) u}
  have hclosed : IsClosed S := by
    have : S = (⋂ A, {u : Wealth →ᵇ ℝ | 0 ≤ u A}) ∩ {u | IsConcaveS (convex_Ici 0) u} := by
      ext u; simp [S]
    rw [this]
    exact (isClosed_iInter fun A => isClosed_le continuous_const (continuous_eval_const A)).inter
      (isClosed_concave (convex_Ici 0))
  have hmaps : MapsTo (consT h) S S := fun u ⟨hu0, huc⟩ => by
    refine ⟨fun A => ?_, fun A A' θ h0 h1 => ?_⟩
    · obtain ⟨C, hC, hval, -⟩ := exists_consT_argmax h u A
      rw [hval]
      exact hnn _ _ hC.1 (hu0 ⟨max (nextWealth p R A.1 C) 0, mem_Ici.2 (le_max_right _ _)⟩)
    · obtain ⟨C, hC, hval, -⟩ := exists_consT_argmax h u A
      obtain ⟨C', hC', hval', -⟩ := exists_consT_argmax h u A'
      obtain ⟨-, -, -, hmax⟩ := exists_consT_argmax h u (cmb (convex_Ici 0) h0 h1 A A')
      set Cθ := θ • C + (1 - θ) • C'
      have h1' : (0 : ℝ) ≤ 1 - θ := by linarith
      have hCθ : Cθ ∈ budgetΓ p (cmb (convex_Ici 0) h0 h1 A A') := by
        refine ⟨add_nonneg (smul_nonneg h0 hC.1) (smul_nonneg h1' hC'.1), ?_⟩
        have e : spend p Cθ = θ * spend p C + (1 - θ) * spend p C' := by
          simp only [spend, Cθ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e]
        change _ ≤ θ • A.1 + (1 - θ) • A'.1
        simp only [smul_eq_mul]
        nlinarith [hC.2, hC'.2]
      have hm := hmax Cθ hCθ
      rw [hval, hval']
      refine le_trans ?_ hm
      -- next wealth is the mixture, and `v` is concave there
      have hn : 0 ≤ nextWealth p R A.1 C := div_nonneg (by linarith [hC.2]) h.R_pos.le
      have hn' : 0 ≤ nextWealth p R A'.1 C' := div_nonneg (by linarith [hC'.2]) h.R_pos.le
      have hmix : nextWealth p R (cmb (convex_Ici 0) h0 h1 A A').1 Cθ =
          θ * nextWealth p R A.1 C + (1 - θ) * nextWealth p R A'.1 C' := by
        have e : spend p Cθ = θ * spend p C + (1 - θ) * spend p C' := by
          simp only [spend, Cθ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        simp only [nextWealth, cmb, smul_eq_mul, e]
        field_simp
        ring
      have hvc := huc ⟨_, hn⟩ ⟨_, hn'⟩ θ h0 h1
      have hmixnn : 0 ≤ θ * nextWealth p R A.1 C + (1 - θ) * nextWealth p R A'.1 C' :=
        add_nonneg (mul_nonneg h0 hn) (mul_nonneg h1' hn')
      simp only [consObj, hmix, vext_of_nonneg u hn, vext_of_nonneg u hn',
        vext_of_nonneg u hmixnn]
      have hcm : cmb (convex_Ici 0) h0 h1 (⟨_, hn⟩ : Wealth) ⟨_, hn'⟩ =
          ⟨_, hmixnn⟩ := Subtype.ext (by simp [cmb])
      rw [hcm] at hvc
      have hWc := hconc.2 (show (C, u ⟨_, hn⟩) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from
        ⟨hC.1, hu0 _⟩) (show (C', u ⟨_, hn'⟩) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from
        ⟨hC'.1, hu0 _⟩) h0 h1' (by ring)
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hWc
      exact hWc.trans (hWz _ hCθ.1 (mem_Ici.2 (add_nonneg (mul_nonneg h0 (hu0 _))
        (mul_nonneg h1' (hu0 _)))) (mem_Ici.2 (hu0 _)) hvc)
  exact (corollary_1 (S' := S) (S'' := S) (consT_contraction h) hv
    ⟨0, fun _ => le_rfl, fun _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1

/-- **Exercise 5.12b.** If moreover `W` is strictly concave in `C` (strictly when `C ≠ C'`), demand
is single-valued and continuous in `A`. -/
theorem ex_5_12b_demand [Nonempty (Fin l → ℝ)] (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hstrict : ∀ C C' : Fin l → ℝ, 0 ≤ C → 0 ≤ C' → C ≠ C' → ∀ z z', 0 ≤ z → 0 ≤ z' →
      W ((1 / 2 : ℝ) • C + (1 / 2 : ℝ) • C') ((1 / 2) * z + (1 / 2) * z') >
        (1 / 2) * W C z + (1 / 2) * W C' z')
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v) :
    UniqueArgmax (budgetΓ p) (consObj W p R v) ∧
      Continuous (argmaxFn (budgetΓ p) (consObj W p R v)) := by
  obtain ⟨hv0, hvc⟩ := ex_5_12b_concave h hconc hnn hv
  have hWz : ∀ C, 0 ≤ C → MonotoneOn (W C) (Ici 0) := fun C hC => by
    refine monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
      fun z hz => hnn C z hC hz
    have := hconc.2 (show (C, z) ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz⟩)
      (show (C, z') ∈ {C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0 from ⟨hC, hz'⟩) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at this
    exact this
  have huniq : ∀ A, ∀ C₁ ∈ argmax (consObj W p R v) (budgetΓ p) A,
      ∀ C₂ ∈ argmax (consObj W p R v) (budgetΓ p) A, C₁ = C₂ := by
    intro A C₁ hC₁ C₂ hC₂
    by_contra hne
    set Cm := (1 / 2 : ℝ) • C₁ + (1 / 2 : ℝ) • C₂
    have hs : spend p Cm = 1 / 2 * spend p C₁ + 1 / 2 * spend p C₂ := by
      simp only [spend, Cm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hCm : Cm ∈ budgetΓ p A := ⟨add_nonneg (smul_nonneg (by norm_num) hC₁.1.1)
      (smul_nonneg (by norm_num) hC₂.1.1), by rw [hs]; linarith [hC₁.1.2, hC₂.1.2]⟩
    have hn₁ : 0 ≤ nextWealth p R A.1 C₁ := div_nonneg (by linarith [hC₁.1.2]) h.R_pos.le
    have hn₂ : 0 ≤ nextWealth p R A.1 C₂ := div_nonneg (by linarith [hC₂.1.2]) h.R_pos.le
    have hmix : nextWealth p R A.1 Cm =
        1 / 2 * nextWealth p R A.1 C₁ + 1 / 2 * nextWealth p R A.1 C₂ := by
      simp only [nextWealth, hs]; field_simp; ring
    have hmn : 0 ≤ 1 / 2 * nextWealth p R A.1 C₁ + 1 / 2 * nextWealth p R A.1 C₂ := by positivity
    have hvm := hvc ⟨_, hn₁⟩ ⟨_, hn₂⟩ (1 / 2) (by norm_num) (by norm_num)
    have hcm : cmb (convex_Ici 0) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (⟨_, hn₁⟩ : Wealth) ⟨_, hn₂⟩ = ⟨_, hmn⟩ :=
      Subtype.ext (by simp only [cmb, smul_eq_mul]; ring)
    rw [hcm] at hvm
    have hle := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos A) hCm
    have e1 := hC₁.2
    have e2 := hC₂.2
    simp only [consObj, hmix, vext_of_nonneg v hn₁, vext_of_nonneg v hn₂,
      vext_of_nonneg v hmn] at hle e1 e2
    have hst := hstrict C₁ C₂ hC₁.1.1 hC₂.1.1 hne _ _ (hv0 ⟨_, hn₁⟩) (hv0 ⟨_, hn₂⟩)
    have hz0 : 0 ≤ 1 / 2 * v ⟨_, hn₁⟩ + 1 / 2 * v ⟨_, hn₂⟩ :=
      add_nonneg (mul_nonneg (by norm_num) (hv0 _)) (mul_nonneg (by norm_num) (hv0 _))
    have hvm' : 1 / 2 * v ⟨_, hn₁⟩ + 1 / 2 * v ⟨_, hn₂⟩ ≤ v ⟨_, hmn⟩ := by
      have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [this] at hvm
      exact hvm
    have hmono := hWz Cm hCm.1 (mem_Ici.2 hz0) (mem_Ici.2 (hv0 _)) hvm'
    linarith
  have hUA : UniqueArgmax (budgetΓ p) (consObj W p R v) :=
    ⟨fun A => ⟨0, zero_mem_budget p A⟩, budget_compact h.p_pos, budget_lhc h.p_pos,
      budget_uhc h.p_pos, (continuous_consObj h v.continuous).continuousOn, huniq⟩
  exact ⟨hUA, hUA.continuous_argmaxFn⟩


/-! ### Homogeneity of degree zero -/

theorem ConsHyp.smul (h : ConsHyp W p R β M) {lam : ℝ} (hlam : 0 < lam) :
    ConsHyp W (lam • p) R β M :=
  ⟨fun i => by simpa using mul_pos hlam (h.p_pos i), h.R_pos, h.β_pos, h.β_lt, h.cont, h.bdd,
    h.lip⟩

theorem spend_smul (lam : ℝ) (p C : Fin l → ℝ) : spend (lam • p) C = lam * spend p C := by
  simp only [spend, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `A ↦ A/λ` on wealth. -/
noncomputable def scaleW (lam : ℝ) (hlam : 0 < lam) (A : Wealth) : Wealth :=
  ⟨A.1 / lam, mem_Ici.2 (div_nonneg A.2.out hlam.le)⟩

/-- **Exercise 5.12b.** Demand is homogeneous of degree zero in `(p, A)`: scaling prices and
wealth by `λ > 0` scales nothing. The value for `λp` is `A ↦ v(A/λ)`, the budget sets agree and
the objectives agree, so the demand correspondences coincide. -/
theorem ex_5_12b_homogeneous (h : ConsHyp W p R β M) {lam : ℝ} (hlam : 0 < lam)
    {v v' : Wealth →ᵇ ℝ} (hv : consT h v = v) (hv' : consT (h.smul hlam) v' = v')
    (A : Wealth) :
    v' A = v (scaleW lam hlam A) ∧ budgetΓ (lam • p) A = budgetΓ p (scaleW lam hlam A) ∧
      ∀ C, consObj W (lam • p) R v' (A, C) = consObj W p R v (scaleW lam hlam A, C) := by
  -- `w(A) = v(A/λ)` is a fixed point of the operator for `λp`
  set w : Wealth →ᵇ ℝ := v.compContinuous ⟨scaleW lam hlam,
    ((continuous_subtype_val.div_const lam).subtype_mk _)⟩
  have hw : ∀ A, w A = v (scaleW lam hlam A) := fun A => by
    simp only [w, BoundedContinuousFunction.compContinuous_apply]
    rfl
  have hΓ : ∀ A, budgetΓ (lam • p) A = budgetΓ p (scaleW lam hlam A) := fun A => by
    ext C
    simp only [budgetΓ, mem_ofPred_eq, spend_smul, scaleW]
    rw [le_div_iff₀ hlam, mul_comm]
  have hobj : ∀ (u : Wealth → ℝ) A C, consObj W (lam • p) R (fun B => u (scaleW lam hlam B))
      (A, C) = consObj W p R u (scaleW lam hlam A, C) := fun u A C => by
    simp only [consObj, vext, nextWealth, spend_smul, scaleW]
    congr 2
    refine Subtype.ext ?_
    simp only
    rw [← max_div_div_right hlam.le, zero_div]
    congr 1
    field_simp
  have hfix : consT (h.smul hlam) w = w := by
    ext A
    change maxValue (consObj W (lam • p) R w) (budgetΓ (lam • p)) A = w A
    rw [hw, ← hv]
    change _ = maxValue (consObj W p R v) (budgetΓ p) (scaleW lam hlam A)
    unfold maxValue
    rw [hΓ A]
    exact congrArg sSup (Set.image_congr fun C _ => hobj v A C)
  have hvw : v' = w := by
    have : Nonempty (Wealth →ᵇ ℝ) := ⟨0⟩
    obtain ⟨u, -, huniq, -⟩ := theorem_3_2 (consT_contraction (h.smul hlam))
    rw [huniq v' hv', huniq w hfix]
  refine ⟨by rw [hvw]; exact hw A, hΓ A, fun C => ?_⟩
  rw [hvw]
  exact hobj v A C

/-! ### Exercise 5.12c: differentiability and first-order conditions -/

theorem spend_add_smul_single (p C : Fin l → ℝ) (i : Fin l) (x : ℝ) :
    spend p (C + x • Pi.single i 1) = spend p C + p i * x := by
  simp only [spend, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- `vext v` is concave on `[0, ∞)` when `v` is. -/
theorem concaveOn_vext {v : Wealth → ℝ} (hv : IsConcaveS (convex_Ici 0) v) :
    ConcaveOn ℝ (Ici 0) (vext v) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hmem : a • x + (1 - a) • y ∈ Ici (0 : ℝ) := convex_Ici 0 hx hy ha hb hab
  rw [vext_of_nonneg v hx, vext_of_nonneg v hy, vext_of_nonneg v hmem, smul_eq_mul, smul_eq_mul]
  exact hv ⟨x, hx⟩ ⟨y, hy⟩ a ha (by linarith)

/-- **Exercise 5.12c (envelope).** At `A₀ > 0`, if `C*` is optimal with `C*_i > 0` and `W` has
partial derivative `W_{C_i}` in good `i` at `(C*, v(A₁))`, then `v'(A₀) = W_{C_i}/p_i`. -/
theorem ex_5_12c_envelope (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ : Wealth} (hA₀ : 0 < A₀.1) {C : Fin l → ℝ}
    (hC : C ∈ argmax (consObj W p R v) (budgetΓ p) A₀) {i : Fin l} (hCi : 0 < C i) {Wi : ℝ}
    (hW : HasDerivAt (fun x : ℝ => W (C + x • Pi.single i 1) (vext v (nextWealth p R A₀.1 C)))
      Wi (0 : ℝ)) :
    HasDerivAt (vext v) (Wi / p i) A₀.1 := by
  obtain ⟨-, hvc⟩ := ex_5_12b_concave h hconc hnn hv
  have hpi := h.p_pos i
  set z₁ := vext v (nextWealth p R A₀.1 C)
  set Wbar : ℝ → ℝ := fun A => W (C + ((A - A₀.1) / p i) • Pi.single i 1) z₁
  have hWbar : HasDerivAt Wbar (Wi * (1 / p i)) A₀.1 := by
    have hin : HasDerivAt (fun A : ℝ => (A - A₀.1) / p i) (1 / p i) A₀.1 := by
      simpa using ((hasDerivAt_id' A₀.1).sub_const A₀.1).div_const (p i)
    exact hW.comp_of_eq A₀.1 hin (by simp)
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W p R v) (budgetΓ p) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have heq : Wbar A₀.1 = vext v A₀.1 := by
    simp only [Wbar, sub_self, zero_div, zero_smul, add_zero]
    rw [vext_of_nonneg v A₀.2, Subtype.coe_eta, hvx]
    exact hC.2
  have hle : ∀ᶠ A in 𝓝 A₀.1, Wbar A ≤ vext v A := by
    filter_upwards [Ioi_mem_nhds (show A₀.1 - p i * C i < A₀.1 by nlinarith)] with A hA
    have hA' : A₀.1 - p i * C i < A := hA
    have hAnn : 0 ≤ A := by
      have := spend_nonneg h.p_pos hC.1.1
      have : p i * C i ≤ spend p C := Finset.single_le_sum (f := fun j => p j * C j)
        (fun j _ => mul_nonneg (h.p_pos j).le (hC.1.1 j)) (Finset.mem_univ i)
      linarith [hC.1.2]
    set Cn := C + ((A - A₀.1) / p i) • Pi.single i 1
    have hCn : Cn ∈ budgetΓ p ⟨A, hAnn⟩ := by
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj
          simp only [Cn, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
            Pi.zero_apply]
          rw [← sub_nonneg]
          have : 0 < A - (A₀.1 - p j * C j) := by linarith
          have h2 : C j + (A - A₀.1) / p j = (A - (A₀.1 - p j * C j)) / p j := by
            field_simp; ring
          rw [sub_zero, h2]
          positivity
        · have hji : (Pi.single i (1 : ℝ) : Fin l → ℝ) j = 0 := Pi.single_eq_of_ne hj 1
          simp only [Cn, Pi.add_apply, Pi.smul_apply, hji, smul_zero, add_zero, Pi.zero_apply]
          exact hC.1.1 j
      · simp only [Cn, spend_add_smul_single]
        rw [mul_div_cancel₀ _ hpi.ne']
        linarith [hC.1.2]
    have hnext : nextWealth p R A Cn = nextWealth p R A₀.1 C := by
      simp only [nextWealth, Cn, spend_add_smul_single, mul_div_cancel₀ _ hpi.ne']
      ring
    rw [vext_of_nonneg v hAnn, hvx]
    have := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos _) hCn
    simp only [consObj, hnext] at this
    exact this
  have := (theorem_4_10 (concaveOn_vext hvc) (Ici_mem_nhds hA₀) hWbar.hasFDerivAt heq
    hle).hasDerivAt
  simpa [div_eq_mul_inv] using this

/-- **Exercise 5.12c (across goods).** Goods consumed in positive amounts have equal marginal
utility per dollar: `W_{C_i}/p_i = W_{C_j}/p_j`. -/
theorem ex_5_12c_intratemporal (h : ConsHyp W p R β M)
    (hconc : ConcaveOn ℝ ({C : Fin l → ℝ | 0 ≤ C} ×ˢ Set.Ici 0) fun q => W q.1 q.2)
    (hnn : ∀ C z, 0 ≤ C → 0 ≤ z → 0 ≤ W C z) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ : Wealth} (hA₀ : 0 < A₀.1) {C : Fin l → ℝ}
    (hC : C ∈ argmax (consObj W p R v) (budgetΓ p) A₀) {i j : Fin l} (hCi : 0 < C i)
    (hCj : 0 < C j) {Wi Wj : ℝ}
    (hWi : HasDerivAt (fun x : ℝ => W (C + x • Pi.single i 1)
      (vext v (nextWealth p R A₀.1 C))) Wi (0 : ℝ))
    (hWj : HasDerivAt (fun x : ℝ => W (C + x • Pi.single j 1)
      (vext v (nextWealth p R A₀.1 C))) Wj (0 : ℝ)) :
    Wi / p i = Wj / p j :=
  (ex_5_12c_envelope h hconc hnn hv hA₀ hC hCi hWi).unique
    (ex_5_12c_envelope h hconc hnn hv hA₀ hC hCj hWj)

/-- **Exercise 5.12c (over time).** If saving is positive (`A₁ = R⁻¹(A₀ − p·C*) > 0`), `v` has
derivative `v₁'` at `A₁` and `W` is differentiable at `(C*, v(A₁))`, then moving a dollar from
good `i` today to wealth tomorrow does not pay: `W_{C_i}/p_i = R⁻¹ W_z v₁'`. -/
theorem ex_5_12c_euler (h : ConsHyp W p R β M) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {A₀ : Wealth} {C : Fin l → ℝ} (hC : C ∈ argmax (consObj W p R v) (budgetΓ p) A₀) {i : Fin l}
    (hCi : 0 < C i) (hA₁ : 0 < nextWealth p R A₀.1 C) {v₁' : ℝ}
    (hv₁ : HasDerivAt (vext v) v₁' (nextWealth p R A₀.1 C))
    {DW : (Fin l → ℝ) × ℝ →L[ℝ] ℝ}
    (hW : HasFDerivAt (fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) DW
      (C, vext v (nextWealth p R A₀.1 C))) :
    DW (Pi.single i 1, 0) / p i = DW (0, 1) * v₁' / R := by
  have hpi := h.p_pos i
  set A₁ := nextWealth p R A₀.1 C
  set c := -1 / p i
  set path : ℝ → (Fin l → ℝ) × ℝ := fun ε => (C + (c * ε) • Pi.single i 1, vext v (A₁ + ε / R))
  have hpath : HasDerivAt path ((c * 1) • Pi.single i 1, v₁' * (1 / R)) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · exact (((hasDerivAt_id' (0 : ℝ)).const_mul c).smul_const
        (Pi.single i 1 : Fin l → ℝ)).const_add C
    · have hin : HasDerivAt (fun ε : ℝ => A₁ + ε / R) (1 / R) 0 := by
        simpa using ((hasDerivAt_id' (0 : ℝ)).div_const R).const_add A₁
      exact hv₁.comp_of_eq (0 : ℝ) hin (by simp)
  have hcomp := hW.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp [path, A₁])
  have hvx : ∀ A : Wealth, v A = maxValue (consObj W p R v) (budgetΓ p) A := fun A =>
    (DFunLike.congr_fun hv A).symm
  have hRA : R * A₁ = A₀.1 - spend p C := by
    have hR0 := h.R_pos.ne'
    simp only [A₁, nextWealth]
    field_simp
  have hpc : ∀ ε, p i * (c * ε) = -ε := fun ε => by simp only [c]; field_simp
  -- the path is feasible near `0`, so its value has a local maximum at `0`
  have hloc : IsLocalMax ((fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) ∘ path) 0 := by
    have h1 : (0 : ℝ) < p i * C i := mul_pos hpi hCi
    have h2 : (0 : ℝ) < R * A₁ := mul_pos h.R_pos hA₁
    filter_upwards [Ioo_mem_nhds (show -(R * A₁) < 0 by linarith) h1] with ε hε
    set Cε := C + (c * ε) • Pi.single i 1
    have hCε : Cε ∈ budgetΓ p A₀ := by
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj
          simp only [Cε, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
            Pi.zero_apply]
          have : p j * (C j + c * ε) = p j * C j - ε := by rw [mul_add, hpc]; ring
          have h3 : 0 ≤ p j * (C j + c * ε) := by rw [this]; linarith [hε.2]
          exact (mul_nonneg_iff_of_pos_left hpi).1 h3
        · have hji : (Pi.single i (1 : ℝ) : Fin l → ℝ) j = 0 := Pi.single_eq_of_ne hj 1
          simp only [Cε, Pi.add_apply, Pi.smul_apply, hji, smul_zero, add_zero, Pi.zero_apply]
          exact hC.1.1 j
      · simp only [Cε, spend_add_smul_single, hpc]
        linarith [hε.1]
    have hnext : nextWealth p R A₀.1 Cε = A₁ + ε / R := by
      simp only [nextWealth, Cε, spend_add_smul_single, hpc]
      have hR0 := h.R_pos.ne'
      field_simp
      linarith [hRA]
    have hle := le_maxValue (continuous_consObj h v.continuous).continuousOn
      (budget_compact h.p_pos A₀) hCε
    have hL : ((fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) ∘ path) ε = consObj W p R v (A₀, Cε) := by
      simp only [Function.comp_apply, path, consObj, hnext, Cε]
    have hR0 : ((fun q : (Fin l → ℝ) × ℝ => W q.1 q.2) ∘ path) 0 =
        consObj W p R v (A₀, C) := by
      simp [path, consObj, A₁]
    rw [hL, hR0, hC.2]
    exact hle
  have h0 := hloc.hasDerivAt_eq_zero hcomp
  have hlin : DW ((c * 1) • Pi.single i 1, v₁' * (1 / R)) =
      c * DW (Pi.single i 1, 0) + v₁' * (1 / R) * DW (0, 1) := by
    rw [show ((c * 1) • Pi.single i 1, v₁' * (1 / R)) =
        c • ((Pi.single i 1 : Fin l → ℝ), (0 : ℝ)) +
          (v₁' * (1 / R)) • ((0 : Fin l → ℝ), (1 : ℝ)) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin] at h0
  simp only [c] at h0
  have hR := h.R_pos.ne'
  field_simp at h0 ⊢
  linarith

/-! ### Exercise 5.12d: monotone transformations of the aggregator -/

/-- **Exercise 5.12d.** With `h` strictly increasing and `h⁻¹ ∘ h = id`, the aggregator
`W̃(C, a) = h(W[C, h⁻¹(a)])` gives the value `h ∘ v` at every `A`, with the same optimal
choices: the demand functions coincide. -/
theorem ex_5_12d (h : ConsHyp W p R β M) {v : Wealth →ᵇ ℝ} (hv : consT h v = v)
    {hf hinv : ℝ → ℝ} (hmono : StrictMono hf) (hleft : ∀ x, hinv (hf x) = x) (A : Wealth) :
    maxValue (fun q => hf (W q.2 (hinv (vext (hf ∘ v) (nextWealth p R q.1.1 q.2)))))
        (budgetΓ p) A = hf (v A) ∧
      argmax (fun q => hf (W q.2 (hinv (vext (hf ∘ v) (nextWealth p R q.1.1 q.2)))))
        (budgetΓ p) A = argmax (consObj W p R v) (budgetΓ p) A := by
  have hfun : (fun q : Wealth × (Fin l → ℝ) =>
      hf (W q.2 (hinv (vext (hf ∘ v) (nextWealth p R q.1.1 q.2))))) =
      fun q => hf (consObj W p R v q) := by
    funext q
    simp only [consObj, vext, Function.comp_apply, hleft]
  rw [hfun]
  obtain ⟨C, hC, hval, hmax⟩ := exists_argmax (continuous_consObj h v.continuous).continuousOn
    (budget_compact h.p_pos A) ⟨0, zero_mem_budget p A⟩
  have hvA : v A = maxValue (consObj W p R v) (budgetΓ p) A := (DFunLike.congr_fun hv A).symm
  have hM : maxValue (fun q => hf (consObj W p R v q)) (budgetΓ p) A = hf (v A) := by
    rw [hvA, ← hval]
    refine (IsGreatest.csSup_eq ⟨⟨C, hC, rfl⟩, ?_⟩)
    rintro _ ⟨C', hC', rfl⟩
    exact hmono.monotone (hmax C' hC')
  refine ⟨hM, ?_⟩
  ext C'
  simp only [argmax, mem_ofPred_eq, hM, hvA]
  exact and_congr_right fun _ => hmono.injective.eq_iff

/-- **Exercise 5.12d.** `W̃` need not be an aggregator. `W(C, z) = z/2` satisfies (W1)–(W3) with
`β = 1/2`; with `h(x) = x/(1 + x)` (bounded, smooth, strictly increasing, `h(0) = 0`),
`W̃(C, a) = h(h⁻¹(a)/2) = a/(2 − a)` on `[0, 1)`, and between `a = 4/5` and `a = 9/10` it moves by
more than `a` does, so (W3) fails for every modulus below one. (`W̃` is not even defined for
`a ≥ 1`.) -/
theorem ex_5_12d_not_aggregator :
    let hf : ℝ → ℝ := fun x => x / (1 + x)
    let hinv : ℝ → ℝ := fun a => a / (1 - a)
    let Wt : ℝ → ℝ := fun a => hf (hinv a / 2)
    (∀ x, 0 ≤ x → hinv (hf x) = x) ∧ StrictMonoOn hf (Ici 0) ∧
      ∀ β' < 1, ¬ ∀ a ∈ Icc (0 : ℝ) (9 / 10), ∀ a' ∈ Icc (0 : ℝ) (9 / 10),
        |Wt a - Wt a'| ≤ β' * |a - a'| := by
  intro hf hinv Wt
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun β' hβ' hall => ?_⟩
  · simp only [hf, hinv]
    have : (1 + x) ≠ 0 := by linarith
    field_simp
    ring
  · simp only [hf]
    rw [div_lt_div_iff₀ (by linarith [mem_Ici.1 hx]) (by linarith [mem_Ici.1 hy])]
    nlinarith
  · have := hall (9 / 10) ⟨by norm_num, by norm_num⟩ (4 / 5) ⟨by norm_num, by norm_num⟩
    simp only [Wt, hf, hinv] at this
    norm_num [abs_of_pos] at this
    nlinarith

end StokeyLucasPrescott.DeterministicDynamics
