/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.LohGeneralFinite
import OwenScrambling.LohVariance
import OwenScrambling.LohCLT
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The product integrand on a scrambled `(0,m,2)`-net: node decomposition

Towards Loh's (2003) CLT for the non-additive integrand `f(x) = x₀ x₁` (post #2). Averaged
over the remainders, the scrambled-net estimator of `x₀ x₁` is `1/4 + S/n`, where
`S = Σ_i A₀(i) A₁(i)` and `A_j(i)` is the centred midpoint of the scrambled cell of point `i` in
coordinate `j`. Each `A_j` is a sum over the levels of the scramble of centred digits
(`scrDev`), digit `k` depending only on the level-`k` node of the tree of coordinate `j`. Given
the scramble `ρ₀` of coordinate `0`, `S` is a sum over the nodes `γ` of the tree of coordinate `1`
of terms `nodeTerm d ρ₀ γ (ρ₁ γ)`, each depending on a single node permutation and centred:
a sum of independent terms (`prodS_eq_sum_nodeTerm`, `unifAvg_nodeTerm`).

The weight of a node `γ` at level `k₁` is a sum over the points below `γ` of `A₀`. The net
property makes the levels of `A₀` above `m - k₁ - 1` cancel exactly (`sum_cdig_cellSet_eq_zero`),
and below that level distinct points use distinct nodes of the tree of coordinate `0`
(`eq_of_truncDigits_eq_cellSet`). So the weights are sums of independent centred terms of the
deep levels of `ρ₀` (`nodeW_eq_wwin`, `wwin_eq_sum`), with explicit second and fourth moment
bounds (`unifAvg_sq_wwin_le`, `unifAvg_pow_four_wwin_le`).

## Main results

* `cdig`, `sum_cdig`, `unifAvg_cdig`, `abs_cdig_le`: centred permuted digits.
* `mid_scramble`: the midpoint of a scrambled cell is `1/2 + scrDev ρ x`.
* `cellAvg_prodFn`, `sum_scrDev_net`, `integral_scrambledEstimate_prodFn`:
  `E[μ̂ | ρ] = 1/4 + S/n` for `x₀ x₁` and every `(0,m,2)`-net.
* `prodS_eq_sum_nodeTerm`, `unifAvg_nodeTerm`: the node decomposition of `S` given `ρ₀`.
* `card_agree_agree_net`, `sum_cdig_cellSet_eq_zero`, `eq_of_truncDigits_eq_cellSet`: the net
  combinatorics.
* `nodeW_eq_wwin`, `wwin_split`, `unifAvg_sq_wwin_le`, `unifAvg_pow_four_wwin_le`: the node
  weights as sums of independent terms of the deep levels, and their moments.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology

variable {b : ℕ}

/-- The **centred digit** `π c - (b - 1)/2` of a digit `c` under a permutation `π`. -/
noncomputable def cdig (pm : Equiv.Perm (Fin b)) (c : Fin b) : ℝ :=
  ((pm c : ℕ) : ℝ) - ((b : ℝ) - 1) / 2

/-- `Σ_{c < b} c = b (b - 1)/2`. -/
theorem sum_fin_cast_eq (b : ℕ) : ∑ c : Fin b, ((c : ℕ) : ℝ) = b * (b - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (i : ℝ)) b, sum_range_cast_id]

/-- The centred digits of a permutation sum to zero. -/
theorem sum_cdig (pm : Equiv.Perm (Fin b)) : ∑ c, cdig pm c = 0 := by
  unfold cdig
  rw [Finset.sum_sub_distrib, Equiv.sum_comp pm (fun c ↦ ((c : ℕ) : ℝ)), sum_fin_cast_eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **A uniformly permuted digit is centred**: `E_π[π c - (b-1)/2] = 0`. -/
theorem unifAvg_cdig (c : Fin b) : unifAvg (fun pm : Equiv.Perm (Fin b) ↦ cdig pm c) = 0 := by
  have h := sum_perm_apply (fun a : Fin b ↦ ((a : ℕ) : ℝ) - ((b : ℝ) - 1) / 2) c
  have hs : ∑ a : Fin b, (((a : ℕ) : ℝ) - ((b : ℝ) - 1) / 2) = 0 := sum_cdig (Equiv.refl _)
  rw [hs, mul_zero, Fintype.card_fin] at h
  have hb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos c).ne'
  have h0 : ∑ pm : Equiv.Perm (Fin b), cdig pm c = 0 := by
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 hb
    · exact h1
  unfold unifAvg
  rw [h0, mul_zero]

/-- `|π c - (b-1)/2| ≤ b/2`. -/
theorem abs_cdig_le (pm : Equiv.Perm (Fin b)) (c : Fin b) : |cdig pm c| ≤ (b : ℝ) / 2 := by
  unfold cdig
  have h1 : ((pm c : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast (pm c).isLt
  have h0 : (0 : ℝ) ≤ ((pm c : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

/-- The weight `b^{-(k+1)}` of digit `k`. -/
noncomputable def digWt (b k : ℕ) : ℝ := ((b : ℝ) ^ (k + 1))⁻¹

/-- Digit weights are positive. -/
theorem digWt_pos (hb : 0 < b) (k : ℕ) : 0 < digWt b k :=
  inv_pos.2 (pow_pos (Nat.cast_pos.2 hb) _)

/-- **The centred midpoint of a scrambled cell**, digit by digit:
`scrDev ρ x = Σ_k (σ(x)_k - (b-1)/2) b^{-(k+1)}`, digit `k` of the scrambled string being
`ρ (k, x|k) (x k)`. -/
noncomputable def scrDev {m : ℕ} (ρ : Scramble b m) (x : Fin m → Fin b) : ℝ :=
  ∑ k : Fin m, cdig (ρ (k, truncDigits k x)) (x k) * digWt b k

/-- The midpoint of the first `r` digits, digit by digit. -/
theorem prefixVal_mid {D : ℕ} (hb : 0 < b) (x : Fin D → Fin b) (r : ℕ) :
    ((prefixVal x r : ℝ) + 1 / 2) / (b : ℝ) ^ r - 1 / 2 =
      ∑ k ∈ Finset.range r, ((digitAt x k : ℝ) - ((b : ℝ) - 1) / 2) * digWt b k := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  induction r with
  | zero => simp [prefixVal]
  | succ r ih =>
      rw [Finset.sum_range_succ, ← ih]
      change (((b * prefixVal x r + digitAt x r : ℕ) : ℝ) + 1 / 2) / (b : ℝ) ^ (r + 1) - 1 / 2 =
        _
      unfold digWt
      push_cast
      field_simp
      ring

/-- **The midpoint of a scrambled cell** is `1/2 + scrDev ρ x`. -/
theorem mid_scramble (hb : 0 < b) {m : ℕ} (ρ : Scramble b m) (x : Fin m → Fin b) :
    ((cellVal (scramble ρ x) : ℝ) + 1 / 2) / (b : ℝ) ^ m = 1 / 2 + scrDev ρ x := by
  have h := prefixVal_mid hb (scramble ρ x) m
  have e : scrDev ρ x = ∑ k ∈ Finset.range m,
      ((digitAt (scramble ρ x) k : ℝ) - ((b : ℝ) - 1) / 2) * digWt b k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ((digitAt (scramble ρ x) k : ℝ) -
      ((b : ℝ) - 1) / 2) * digWt b k) m]
    unfold scrDev
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [digitAt_fin]
    rfl
  unfold cellVal
  rw [e, ← h]
  ring

/-- `∫ (cellVal x + w)/b^D dw = (cellVal x + 1/2)/b^D` over `w ~ U[0,1)`. -/
theorem integral_digitPoint {D : ℕ} (x : Fin D → Fin b) :
    ∫ w, digitPoint x w ∂uniformIco = ((cellVal x : ℝ) + 1 / 2) / (b : ℝ) ^ D := by
  have := isProbabilityMeasure_uniformIco
  have e : (fun w ↦ digitPoint x w) = fun w ↦ ((b : ℝ) ^ D)⁻¹ * ((cellVal x : ℝ) + w) :=
    funext fun w ↦ by unfold digitPoint; ring
  rw [e, integral_const_mul, integral_add (f := fun _ ↦ (cellVal x : ℝ)) (g := fun a ↦ a)
    (integrable_const _) (integrable_uniformIco_of_continuous (g := fun a ↦ a) continuous_id),
    integral_const, probReal_univ, one_smul, integral_id_uniformIco]
  ring

/-- **The cell average of `x₀ x₁`** is the product of the cell midpoints. -/
theorem cellAvg_prodFn {D : ℕ} (y : Fin 2 → Fin D → Fin b) :
    cellAvg prodFn y = (((cellVal (y 0) : ℝ) + 1 / 2) / (b : ℝ) ^ D) *
      (((cellVal (y 1) : ℝ) + 1 / 2) / (b : ℝ) ^ D) := by
  have := isProbabilityMeasure_uniformIco
  unfold cellAvg
  have e : (fun u : Fin 2 → ℝ ↦ prodFn (cellPoint y u)) =
      fun u ↦ digitPoint (y 0) (u 0) * digitPoint (y 1) (u 1) := rfl
  rw [e, ← integral_digitPoint, ← integral_digitPoint]
  exact integral_pi_eval_mul (ν := uniformIco)
    (measurable_digitPoint (y 0)).aestronglyMeasurable
    (measurable_digitPoint (y 1)).aestronglyMeasurable (by decide)

/-- `x₀ x₁` is measurable. -/
theorem measurable_prodFn : Measurable prodFn :=
  (measurable_pi_apply 0).mul (measurable_pi_apply 1)

/-- `x₀ x₁` is in `L²` of the cube. -/
theorem memLp_prodFn : MemLp prodFn 2 (uniformCube 2) := by
  have hU := isProbabilityMeasure_uniformCube 2
  refine MemLp.of_bound measurable_prodFn.aestronglyMeasurable 1 ?_
  filter_upwards [ae_mem_cube_uniformCube 2] with x hx
  rw [Real.norm_eq_abs, prodFn, abs_mul]
  have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
  have h1 : |x 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx 1).1], (hx 1).2.le⟩
  nlinarith [abs_nonneg (x 0), abs_nonneg (x 1)]

/-- **The centred midpoints of a scrambled `(0,m,s)`-net sum to zero** in each coordinate (the
scrambled coordinate visits every cell once). -/
theorem sum_scrDev_net (hb : 0 < b) {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (ρ : Fin s → Scramble b m)
    (j : Fin s) : ∑ i, scrDev (ρ j) (d i j) = 0 := by
  have hN : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pow_pos hb).ne'
  set G : Fin (b ^ m) → ℝ := fun c ↦ ((c : ℕ) + 1 / 2) / (b : ℝ) ^ m - 1 / 2 with hG
  have e : ∀ i, scrDev (ρ j) (d i j) = G (cellFin hb (scramble (ρ j) (d i j))) := fun i ↦ by
    rw [hG]
    change _ = ((cellVal (scramble (ρ j) (d i j)) : ℝ) + 1 / 2) / (b : ℝ) ^ m - 1 / 2
    rw [mid_scramble hb]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ e i,
    (bijective_cellFin_scramble hb hnet ρ j).sum_comp G, hG]
  simp only
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, sum_fin_cast_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- `S = Σ_i A₀(i) A₁(i)`, the product of the centred scrambled midpoints. -/
noncomputable def prodS {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ : Fin 2 → Scramble b m) : ℝ :=
  ∑ i, scrDev (ρ 0) (d i 0) * scrDev (ρ 1) (d i 1)

/-- **`E[μ̂ | ρ] = 1/4 + S/n` for `x₀ x₁`** on every scrambled `(0,m,2)`-net. -/
theorem integral_scrambledEstimate_prodFn (hb : 0 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (ρ : Fin 2 → Scramble b m) :
    ∫ u, scrambledEstimate prodFn d ρ u ∂(remLaw 2 (b ^ m)) =
      1 / 4 + prodS d ρ / ((b ^ m : ℕ) : ℝ) := by
  have hN : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pow_pos hb).ne'
  rw [integral_scrambledEstimate hb memLp_prodFn d ρ]
  have e : ∀ i, cellAvg prodFn (scrambleVec ρ (d i)) =
      (1 / 2 + scrDev (ρ 0) (d i 0)) * (1 / 2 + scrDev (ρ 1) (d i 1)) := fun i ↦ by
    rw [cellAvg_prodFn, ← mid_scramble hb, ← mid_scramble hb]
    rfl
  rw [Finset.sum_congr rfl fun i _ ↦ e i]
  have e2 : ∀ i, (1 / 2 + scrDev (ρ 0) (d i 0)) * (1 / 2 + scrDev (ρ 1) (d i 1)) =
      1 / 4 + scrDev (ρ 0) (d i 0) / 2 + scrDev (ρ 1) (d i 1) / 2 +
        scrDev (ρ 0) (d i 0) * scrDev (ρ 1) (d i 1) := fun i ↦ by ring
  rw [Finset.sum_congr rfl fun i _ ↦ e2 i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div (f := fun i ↦ scrDev (ρ 0) (d i 0)),
    ← Finset.sum_div (f := fun i ↦ scrDev (ρ 1) (d i 1)), sum_scrDev_net hb hnet ρ 0,
    sum_scrDev_net hb hnet ρ 1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold prodS
  field_simp
  ring

/-- The points below the node `γ = (k, t)` of the tree of coordinate `1`: those whose first `k`
digits in coordinate `1` are `t`. -/
def nodeSet {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (γ : Fin m × (Fin m → Option (Fin b))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ truncDigits γ.1 (d i 1) = γ.2

/-- The points below the child `c` of the node `γ`: digit `γ.1` of coordinate `1` is `c`. -/
def cellSet {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) : Finset (Fin n) :=
  (nodeSet d γ).filter fun i ↦ d i 1 γ.1 = c

/-- The **node weights** given `ρ₀`: `w_{γ,c} = Σ_{i below (γ, c)} A₀(i)`. -/
noncomputable def nodeW {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) : ℝ :=
  ∑ i ∈ cellSet d γ c, scrDev ρ₀ (d i 0)

/-- The **node term** of `S` given `ρ₀`, a function of the permutation `π` of the node `γ` of
the tree of coordinate `1`: `b^{-(k+1)} Σ_c (π c - (b-1)/2) w_{γ,c}`. -/
noncomputable def nodeTerm {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (pm : Equiv.Perm (Fin b)) : ℝ :=
  digWt b γ.1 * ∑ c, cdig pm c * nodeW d ρ₀ γ c

/-- Regrouping a node term by points. -/
theorem sum_cdig_mul_nodeW {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (pm : Equiv.Perm (Fin b)) :
    ∑ c, cdig pm c * nodeW d ρ₀ γ c =
      ∑ i ∈ nodeSet d γ, cdig pm (d i 1 γ.1) * scrDev ρ₀ (d i 0) := by
  unfold nodeW cellSet
  rw [← Finset.sum_fiberwise (nodeSet d γ) (fun i ↦ d i 1 γ.1)
    (fun i ↦ cdig pm (d i 1 γ.1) * scrDev ρ₀ (d i 0))]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [(Finset.mem_filter.1 hi).2]

/-- **Given `ρ₀`, `S` is a sum of node terms of `ρ₁`**: `S = Σ_γ nodeTerm d ρ₀ γ (ρ₁ γ)`, one
term for each node `γ` of the tree of coordinate `1`, depending only on its permutation. -/
theorem prodS_eq_sum_nodeTerm {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ : Fin 2 → Scramble b m) : prodS d ρ = ∑ γ, nodeTerm d (ρ 0) γ (ρ 1 γ) := by
  symm
  calc ∑ γ, nodeTerm d (ρ 0) γ (ρ 1 γ)
      = ∑ γ : Fin m × (Fin m → Option (Fin b)), digWt b γ.1 *
          ∑ i ∈ nodeSet d γ, cdig (ρ 1 γ) (d i 1 γ.1) * scrDev (ρ 0) (d i 0) :=
        Finset.sum_congr rfl fun γ _ ↦ by unfold nodeTerm; rw [sum_cdig_mul_nodeW]
    _ = ∑ k : Fin m, ∑ t : Fin m → Option (Fin b), digWt b k *
          ∑ i ∈ nodeSet d (k, t), cdig (ρ 1 (k, t)) (d i 1 k) * scrDev (ρ 0) (d i 0) :=
        Fintype.sum_prod_type _
    _ = ∑ k : Fin m, digWt b k *
          ∑ i, cdig (ρ 1 (k, truncDigits k (d i 1))) (d i 1 k) * scrDev (ρ 0) (d i 0) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_fiberwise Finset.univ (fun i ↦ truncDigits k (d i 1))
          (fun i ↦ cdig (ρ 1 (k, truncDigits k (d i 1))) (d i 1 k) * scrDev (ρ 0) (d i 0))]
        refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
        rw [(Finset.mem_filter.1 hi).2]
    _ = prodS d ρ := by
        unfold prodS
        rw [Finset.sum_congr rfl fun k _ ↦ Finset.mul_sum _ _ _, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [show scrDev (ρ 1) (d i 1) = ∑ k : Fin m,
          cdig (ρ 1 (k, truncDigits k (d i 1))) (d i 1 k) * digWt b k from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring

/-- **The node terms are centred** under a uniform permutation. -/
theorem unifAvg_nodeTerm {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) : unifAvg (nodeTerm d ρ₀ γ) = 0 := by
  unfold nodeTerm
  rw [unifAvg_const_mul, unifAvg_sum, Finset.sum_eq_zero, mul_zero]
  intro c _
  rw [show (fun pm : Equiv.Perm (Fin b) ↦ cdig pm c * nodeW d ρ₀ γ c) =
    fun pm ↦ nodeW d ρ₀ γ c * cdig pm c from funext fun pm ↦ mul_comm _ _, unifAvg_const_mul,
    unifAvg_cdig, mul_zero]

/-- **Points of a `(0,m,2)`-net in an elementary box with `r₀ + r₁ ≤ m`**, described by
prefixes `z₀, z₁`: exactly `b^{m - r₀ - r₁}`. -/
theorem card_agree_agree_net (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r₀ r₁ : ℕ} (hr : r₀ + r₁ ≤ m)
    (z₀ z₁ : Fin m → Fin b) :
    (Finset.univ.filter fun i ↦ Agree r₀ z₀ (d i 0) ∧ Agree r₁ z₁ (d i 1)).card =
      b ^ (m - r₀ - r₁) := by
  have hr0 : r₀ ≤ m := by omega
  have hr1 : r₁ ≤ m := by omega
  have h := card_box_net_of_le hb le_rfl hnet (r := ![r₀, r₁])
    (by rw [Fin.sum_univ_two]; simpa using hr) (a := ![prefixVal z₀ r₀, prefixVal z₁ r₁])
    (fun j ↦ by fin_cases j <;> simp [prefixVal_lt hb])
  rw [Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  rw [show m - r₀ - r₁ = m - (r₀ + r₁) by omega, ← h]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [eq_comm, prefixVal_eq_iff_agree hb hr0, eq_comm (a := prefixVal (d i 1) r₁),
    prefixVal_eq_iff_agree hb hr1]

/-- Agreement with a string whose digit `k` is replaced by `e`. -/
theorem agree_update_succ_iff {m : ℕ} (x y : Fin m → Fin b) (k : Fin m) (e : Fin b) :
    Agree ((k : ℕ) + 1) (Function.update x k e) y ↔ Agree k x y ∧ y k = e := by
  rw [agree_succ_iff k.isLt]
  have hk : (⟨(k : ℕ), k.isLt⟩ : Fin m) = k := Fin.eta k _
  rw [hk, Function.update_self]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l hl ↦ ?_, h2.symm⟩
    have := h1 l hl
    rwa [Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hl))] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun l hl ↦ ?_, h2.symm⟩
    rw [Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hl))]
    exact h1 l hl

/-- Agreement is symmetric (as an `iff`). -/
theorem agree_comm_iff {D r : ℕ} (x y : Fin D → Fin b) : Agree r x y ↔ Agree r y x :=
  ⟨agree_symm, agree_symm⟩

/-- **The shallow levels of `A₀` cancel below a node** (the net property): if
`k₀ + k₁ + 2 ≤ m`, the level-`k₀` centred digits of coordinate `0` sum to zero over the points
below any child of a level-`k₁` node of coordinate `1`, for every scramble `ρ₀`. -/
theorem sum_cdig_cellSet_eq_zero (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {k₀ k₁ : Fin m}
    (hk : (k₀ : ℕ) + k₁ + 2 ≤ m) (t : Fin m → Option (Fin b)) (c : Fin b) (ρ₀ : Scramble b m) :
    ∑ i ∈ cellSet d (k₁, t) c, cdig (ρ₀ (k₀, truncDigits k₀ (d i 0))) (d i 0 k₀) = 0 := by
  classical
  rw [← Finset.sum_fiberwise (cellSet d (k₁, t) c) (fun i ↦ truncDigits k₀ (d i 0))]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  set G := (cellSet d (k₁, t) c).filter fun i ↦ truncDigits k₀ (d i 0) = p with hG
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2]]
  rcases G.eq_empty_or_nonempty with hG0 | ⟨i₁, hi₁⟩
  · rw [hG0, Finset.sum_empty]
  have hi₁' := hi₁
  simp only [hG, cellSet, nodeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi₁'
  have hcount : ∀ e : Fin b, (G.filter fun i ↦ d i 0 k₀ = e).card =
      b ^ (m - ((k₀ : ℕ) + 1) - ((k₁ : ℕ) + 1)) := by
    intro e
    rw [← card_agree_agree_net hb hnet (by omega) (Function.update (d i₁ 0) k₀ e) (d i₁ 1)]
    congr 1
    ext i
    simp only [hG, cellSet, nodeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [agree_update_succ_iff, agree_succ_iff k₁.isLt, Fin.eta, ← hi₁'.1.1, ← hi₁'.1.2,
      ← hi₁'.2, truncDigits_eq_iff, truncDigits_eq_iff, agree_comm_iff (d i 1),
      agree_comm_iff (d i 0)]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h3, h4⟩, h1, h2.symm⟩
    · rintro ⟨⟨h3, h4⟩, h1, h2⟩
      exact ⟨⟨⟨h1, h2.symm⟩, h3⟩, h4⟩
  rw [← Finset.sum_fiberwise G (fun i ↦ d i 0 k₀)]
  calc ∑ e : Fin b, ∑ i ∈ G with d i 0 k₀ = e, cdig (ρ₀ (k₀, p)) (d i 0 k₀)
      = ∑ e : Fin b, ((b ^ (m - ((k₀ : ℕ) + 1) - ((k₁ : ℕ) + 1)) : ℕ) : ℝ) *
          cdig (ρ₀ (k₀, p)) e := by
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2],
          Finset.sum_const, hcount e, nsmul_eq_mul]
    _ = 0 := by rw [← Finset.mul_sum, sum_cdig, mul_zero]

/-- **Below a level-`k₁` node, distinct points use distinct deep nodes of coordinate `0`**: if
`k₀ + k₁ + 1 ≥ m`, two points below the same child of a level-`k₁` node with the same `k₀`-digit
prefix in coordinate `0` coincide. -/
theorem eq_of_truncDigits_eq_cellSet (hb : 0 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {k₁ : Fin m} {t : Fin m → Option (Fin b)} {c : Fin b} {i i' : Fin (b ^ m)}
    (hi : i ∈ cellSet d (k₁, t) c) (hi' : i' ∈ cellSet d (k₁, t) c) {k₀ : Fin m}
    (hk : m ≤ (k₀ : ℕ) + k₁ + 1) (h : truncDigits k₀ (d i 0) = truncDigits k₀ (d i' 0)) :
    i = i' := by
  simp only [cellSet, nodeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
  have hc := card_agree_net_of_ge hb le_rfl hnet (r := ![(k₀ : ℕ), (k₁ : ℕ) + 1])
    (by rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]; omega) i
  have hmem : ∀ i'', Agree k₀ (d i 0) (d i'' 0) → Agree ((k₁ : ℕ) + 1) (d i 1) (d i'' 1) →
      i'' ∈ Finset.univ.filter fun i'' ↦
        ∀ j, Agree (![(k₀ : ℕ), (k₁ : ℕ) + 1] j) (d i j) (d i'' j) := by
    intro i'' h0 h1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun j ↦ ?_⟩
    fin_cases j
    · exact h0
    · exact h1
  have h1 : Agree ((k₁ : ℕ) + 1) (d i 1) (d i' 1) := by
    rw [agree_succ_iff k₁.isLt, Fin.eta]
    exact ⟨truncDigits_eq_iff.1 (hi.1.trans hi'.1.symm), hi.2.trans hi'.2.symm⟩
  exact Finset.card_le_one.1 hc.le i (hmem i (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)) i'
    (hmem i' (truncDigits_eq_iff.1 h) h1)

/-- The levels `lo ≤ k < hi` of a tree of depth `m`. -/
def levelWin (m lo hi : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun k ↦ lo ≤ (k : ℕ) ∧ (k : ℕ) < hi

/-- The part of the node weight `w_{γ,c}` from the levels `lo ≤ k < hi` of `ρ₀`. -/
noncomputable def wwin {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) (lo hi : ℕ) : ℝ :=
  ∑ i ∈ cellSet d γ c, ∑ k ∈ levelWin m lo hi,
    cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k

/-- **Only the deep levels contribute to the node weights**: `w_{γ,c}` is its part from the
levels `k₀ ≥ m - k₁ - 1` of `ρ₀` (`k₁` the level of `γ`). -/
theorem nodeW_eq_wwin (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) :
    nodeW d ρ₀ γ c = wwin d ρ₀ γ c (m - γ.1 - 1) m := by
  classical
  obtain ⟨k₁, t⟩ := γ
  unfold nodeW wwin scrDev levelWin
  have hsplit : ∀ i, ∑ k : Fin m, cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ m - (k₁ : ℕ) - 1 ≤ (k : ℕ) ∧ (k : ℕ) < m),
        cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k +
      ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ ¬ (m - (k₁ : ℕ) - 1 ≤ (k : ℕ) ∧ (k : ℕ) < m)),
        cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k := fun i ↦
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib]
  have hz : ∑ i ∈ cellSet d (k₁, t) c,
      ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ ¬ (m - (k₁ : ℕ) - 1 ≤ (k : ℕ) ∧ (k : ℕ) < m)),
        cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.mem_filter] at hk
    have hk' : (k : ℕ) + k₁ + 2 ≤ m := by
      have := k.isLt
      have := k₁.isLt
      omega
    rw [← Finset.sum_mul, sum_cdig_cellSet_eq_zero hb hnet hk' t c ρ₀, zero_mul]
  rw [hz, add_zero]

/-- Splitting a window of levels. -/
theorem wwin_split {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) {lo mid hi : ℕ} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) : wwin d ρ₀ γ c lo hi = wwin d ρ₀ γ c lo mid + wwin d ρ₀ γ c mid hi := by
  unfold wwin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_filter_add_sum_filter_not (levelWin m lo hi) (fun k : Fin m ↦ (k : ℕ) < mid)]
  congr 1
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-- The coordinate term of a node weight: digit `k` of point `i` in coordinate `0`. -/
noncomputable def wX {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (q : Fin n × Fin m)
    (pm : Equiv.Perm (Fin b)) : ℝ :=
  cdig pm (d q.1 0 q.2) * digWt b q.2

/-- The node of the tree of coordinate `0` used by digit `k` of point `i`. -/
def wν {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (q : Fin n × Fin m) :
    Fin m × (Fin m → Option (Fin b)) :=
  (q.2, truncDigits q.2 (d q.1 0))

/-- A window part of a node weight as a sum of coordinate terms. -/
theorem wwin_eq_sum {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) (lo hi : ℕ) :
    wwin d ρ₀ γ c lo hi = ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, wX d q (ρ₀ (wν d q)) := by
  unfold wwin
  rw [Finset.sum_product]
  rfl

/-- **Distinct coordinate terms of a deep window use distinct nodes.** -/
theorem injOn_wν (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (γ : Fin m × (Fin m → Option (Fin b)))
    (c : Fin b) {lo hi : ℕ} (hlo : m ≤ lo + γ.1 + 1) :
    Set.InjOn (wν d) ↑(cellSet d γ c ×ˢ levelWin m lo hi) := by
  obtain ⟨k₁, t⟩ := γ
  change m ≤ lo + (k₁ : ℕ) + 1 at hlo
  intro q hq q' hq' heq
  rw [Finset.mem_coe, Finset.mem_product] at hq hq'
  unfold wν at heq
  have h2 : q.2 = q'.2 := (Prod.mk.inj heq).1
  have h3 := (Prod.mk.inj heq).2
  rw [← h2] at h3
  have hk : m ≤ (q.2 : ℕ) + k₁ + 1 := by
    have := (Finset.mem_filter.1 hq.2).2.1
    omega
  exact Prod.ext (eq_of_truncDigits_eq_cellSet hb hnet hq.1 hq'.1 hk h3) h2

/-- The coordinate terms are centred. -/
theorem unifAvg_wX {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (q : Fin n × Fin m) :
    unifAvg (wX d q) = 0 := by
  unfold wX
  rw [unifAvg_mul_const, unifAvg_cdig, zero_mul]

/-- The coordinate terms are bounded: `|wX| ≤ (b/2) b^{-(k+1)}`. -/
theorem abs_wX_le (hb : 0 < b) {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (q : Fin n × Fin m) (pm : Equiv.Perm (Fin b)) :
    |wX d q pm| ≤ (b : ℝ) / 2 * digWt b q.2 := by
  unfold wX
  rw [abs_mul, abs_of_pos (digWt_pos hb _)]
  exact mul_le_mul_of_nonneg_right (abs_cdig_le _ _) (digWt_pos hb _).le

/-- **The geometric bound** `Σ_{lo ≤ k < hi} b^{-2(k+1)} ≤ 2 b^{-2(lo+1)}` (`b ≥ 2`). -/
theorem sum_levelWin_digWt_sq_le (hb : 1 < b) (m lo hi : ℕ) :
    ∑ k ∈ levelWin m lo hi, digWt b k ^ 2 ≤ 2 * digWt b lo ^ 2 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set q : ℝ := ((b : ℝ) ^ 2)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (sq_nonneg _)
  have hq4 : q ≤ 1 / 4 := by
    rw [hq, one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith)
  have hw : ∀ k : ℕ, digWt b k ^ 2 = q * q ^ k := fun k ↦ by
    unfold digWt
    rw [hq, ← pow_succ', inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (k + 1) 2]
  have hmap : ∑ k ∈ levelWin m lo hi, digWt b k ^ 2 =
      ∑ k ∈ (levelWin m lo hi).map Fin.valEmbedding, digWt b k ^ 2 := by
    rw [Finset.sum_map]
    rfl
  have hsub : (levelWin m lo hi).map Fin.valEmbedding ⊆ Finset.Ico lo (lo + m) := by
    intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    rw [levelWin, Finset.mem_filter] at hk'
    rw [Finset.mem_Ico]
    have := k'.isLt
    simp only [Fin.valEmbedding_apply]
    omega
  rw [hmap]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ ↦ sq_nonneg _).trans ?_
  rw [Finset.sum_congr rfl fun k _ ↦ hw k, ← Finset.mul_sum, hw lo]
  have hg := geom_sum_Ico_le_of_lt_one (m := lo) (n := lo + m) hq0 (by linarith)
  have h12 : q ^ lo / (1 - q) ≤ 2 * q ^ lo := by
    rw [div_le_iff₀ (by linarith)]
    have := pow_nonneg hq0 lo
    nlinarith
  calc q * ∑ k ∈ Finset.Ico lo (lo + m), q ^ k ≤ q * (2 * q ^ lo) :=
        mul_le_mul_of_nonneg_left (hg.trans h12) hq0
    _ = 2 * (q * q ^ lo) := by ring

/-- **Second moment of a window of a node weight**:
`E[w²] ≤ #(cell) (b/2)² · 2 b^{-2(lo+1)}` for a deep window (`lo + k₁ + 1 ≥ m`). -/
theorem unifAvg_sq_wwin_le (hb : 1 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (γ : Fin m × (Fin m → Option (Fin b)))
    (c : Fin b) {lo hi : ℕ} (hlo : m ≤ lo + γ.1 + 1) :
    unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 2) ≤
      (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  rw [show (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 2) =
    fun ρ₀ ↦ (∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, wX d q (ρ₀ (wν d q))) ^ 2 from
    funext fun ρ₀ ↦ by rw [wwin_eq_sum],
    unifAvg_sq_sum_eq (injOn_wν hb0 hnet γ c hlo) (fun q _ ↦ unifAvg_wX d q)]
  calc ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, unifAvg (fun pm ↦ wX d q pm ^ 2)
      ≤ ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, ((b : ℝ) / 2) ^ 2 * digWt b q.2 ^ 2 := by
        refine Finset.sum_le_sum fun q _ ↦ ?_
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_wX_le hb0 d q pm) 2
    _ = (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 *
          ∑ k ∈ levelWin m lo hi, digWt b k ^ 2) := by
        rw [Finset.sum_product]
        dsimp only
        rw [Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum _ _ _).symm, Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2)) := by
        gcongr
        exact sum_levelWin_digWt_sq_le hb m lo hi

/-- **Fourth moment of a window of a node weight**: `E[w⁴] ≤ 3 (#(cell) (b/2)² ·
2 b^{-2(lo+1)})²` for a deep window. -/
theorem unifAvg_pow_four_wwin_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) {lo hi : ℕ} (hlo : m ≤ lo + γ.1 + 1) :
    unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 4) ≤
      3 * ((cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2))) ^ 2 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  rw [show (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 4) =
    fun ρ₀ ↦ (∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, wX d q (ρ₀ (wν d q))) ^ 4 from
    funext fun ρ₀ ↦ by rw [wwin_eq_sum]]
  refine (unifAvg_pow_four_sum_le (injOn_wν hb0 hnet γ c hlo) (fun q _ ↦ unifAvg_wX d q)
    (β := fun q ↦ (b : ℝ) / 2 * digWt b q.2) fun q _ pm ↦ abs_wX_le hb0 d q pm).trans ?_
  have hs : ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, ((b : ℝ) / 2 * digWt b q.2) ^ 2 ≤
      (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2)) := by
    rw [Finset.sum_product]
    dsimp only
    rw [Finset.sum_congr rfl fun x _ ↦ (Finset.sum_congr rfl fun k _ ↦ mul_pow _ _ 2).trans
      (Finset.mul_sum _ _ _).symm, Finset.sum_const, nsmul_eq_mul]
    gcongr
    exact sum_levelWin_digWt_sq_le hb m lo hi
  have h0 : 0 ≤ ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, ((b : ℝ) / 2 * digWt b q.2) ^ 2 :=
    Finset.sum_nonneg fun q _ ↦ sq_nonneg _
  gcongr

end RQMCMarkov.OwenScrambling
