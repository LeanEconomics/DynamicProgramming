/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.Concavity

/-!
# A seller with unknown demand

SLP §5.16, pp. 123–125: the reservation price `R` is uniform on `[A, B) ⊆ [0, 1)`. A price
`P ∈ [A, B]` sells with probability `q = (B − P)/(B − A)`, after which `R ∈ [P, B)`; otherwise
`R ∈ [A, P)`. On `D = {(A, B) : 0 ≤ A ≤ B ≤ 1}`,
`(Tf)(A, B) = sup_P {qP + β[(1 − q)f(A, P) + qf(P, B)]}`.

The book's formula divides by `B − A`, which vanishes on the diagonal of `D`. We parametrize by
the probability of sale `q ∈ [0, 1]`, with `P = (1 − q)B + qA`: this is the book's operator off the
diagonal, and it is continuous on all of `D` (on the diagonal it gives `A + βf(A, A)`).

* **Exercise 5.16a** (`ex_5_16a`): `T : C(D) → C(D)` is a contraction (Blackwell's conditions), and
  its fixed point `v` is homogeneous of degree one (`ex_5_16a_hom`, Corollary 1).
* **Exercise 5.16b**: with `w(a) = v(a, 1)`, `v(A, B) = Bw(A/B)` (`v_eq_w`), `w(1) = 1/(1 − β)`
  (`ex_5_16b_one`); `v` is jointly convex on `D` (`v_convex`), so `w` is weakly convex
  (`ex_5_16b_convex`); and `w` is strictly increasing (`ex_5_16b_strictMono`). For `v`: it is
  increasing in both bounds, convex, and at least `A/(1 − β)` (`v_ge`), the value of charging `A`
  forever.
* **Exercise 5.16c** (`ex_5_16c`): with `â = 1/(2 − β)`, setting `P = A` is optimal and
  `w(a) = a/(1 − β)` exactly when `a ≥ â`: on the region `A(2 − β) ≥ B` the bound `v ≤ A/(1 − β)` is
  preserved by `T` (both children stay in the region), while for `a < â` some `P > A` does
  strictly better.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- `D = {(A, B) : 0 ≤ A ≤ B ≤ 1}`. -/
def Dtri : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ 1}

abbrev DPt := ↥Dtri

/-- Probabilities of sale `q ∈ [0, 1]`. -/
abbrev Prob := ↥(Icc (0 : ℝ) 1)

theorem convex_Dtri : Convex ℝ Dtri := by
  intro x hx y hy a b ha hb hab
  simp only [Dtri, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2.1, hy.2.1], by nlinarith [hx.2.2, hy.2.2]⟩

/-- The price `P = (1 − q)B + qA`. -/
def priceQ (x : DPt) (q : Prob) : ℝ := (1 - q.1) * x.1.2 + q.1 * x.1.1

theorem priceQ_mem (x : DPt) (q : Prob) : x.1.1 ≤ priceQ x q ∧ priceQ x q ≤ x.1.2 := by
  have h1 := x.2.2.1
  have hq := q.2
  simp only [priceQ]
  constructor <;> nlinarith [hq.1, hq.2]

/-- The state after no sale: `(A, P)`. -/
def leftPt (x : DPt) (q : Prob) : DPt :=
  ⟨(x.1.1, priceQ x q), x.2.1, (priceQ_mem x q).1, (priceQ_mem x q).2.trans x.2.2.2⟩

/-- The state after a sale: `(P, B)`. -/
def rightPt (x : DPt) (q : Prob) : DPt :=
  ⟨(priceQ x q, x.1.2), x.2.1.trans (priceQ_mem x q).1, (priceQ_mem x q).2, x.2.2.2⟩

variable {β : ℝ}

/-- The objective `qP + β[(1 − q)f(A, P) + qf(P, B)]`. -/
def sellerObj (β : ℝ) (f : DPt → ℝ) (z : DPt × Prob) : ℝ :=
  z.2.1 * priceQ z.1 z.2 + β * ((1 - z.2.1) * f (leftPt z.1 z.2) + z.2.1 * f (rightPt z.1 z.2))

theorem sellerObj_apply (f : DPt → ℝ) (x : DPt) (q : Prob) :
    sellerObj β f (x, q) =
      q.1 * priceQ x q + β * ((1 - q.1) * f (leftPt x q) + q.1 * f (rightPt x q)) := rfl

theorem continuous_priceQ : Continuous fun z : DPt × Prob => priceQ z.1 z.2 := by
  unfold priceQ; fun_prop

theorem continuous_sellerObj {f : DPt → ℝ} (hf : Continuous f) :
    Continuous (sellerObj β f) := by
  have hl : Continuous fun z : DPt × Prob => leftPt z.1 z.2 :=
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_priceQ).subtype_mk _
  have hr : Continuous fun z : DPt × Prob => rightPt z.1 z.2 :=
    (continuous_priceQ.prodMk (continuous_snd.comp (continuous_subtype_val.comp
      continuous_fst))).subtype_mk _
  unfold sellerObj
  have hq : Continuous fun z : DPt × Prob => z.2.1 := continuous_subtype_val.comp continuous_snd
  exact (hq.mul continuous_priceQ).add (continuous_const.mul
    (((continuous_const.sub hq).mul (hf.comp hl)).add (hq.mul (hf.comp hr))))

theorem prob_lhc (x : DPt) : IsLHC (fun _ : DPt => (univ : Set Prob)) x :=
  ⟨univ_nonempty, fun y _ _ _ => ⟨0, fun _ => y, fun _ _ => mem_univ _, tendsto_const_nhds⟩⟩

theorem prob_uhc (x : DPt) : IsUHC (fun _ : DPt => (univ : Set Prob)) x := by
  refine ⟨univ_nonempty, fun xs _ ys _ => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  exact ⟨y, mem_univ _, φ, hφ, hlim⟩

theorem abs_sellerObj_le (hβ : 0 ≤ β) (f : DPt →ᵇ ℝ) (z : DPt × Prob) :
    |sellerObj β f z| ≤ 1 + β * ‖f‖ := by
  have hq := z.2.2
  have hP := priceQ_mem z.1 z.2
  have hA := z.1.2.1
  have hB := z.1.2.2.2
  have h1 : |f (leftPt z.1 z.2)| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _
  have h2 : |f (rightPt z.1 z.2)| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _
  have h3 : |(1 - z.2.1) * f (leftPt z.1 z.2) + z.2.1 * f (rightPt z.1 z.2)| ≤ ‖f‖ := by
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [hq.1, hq.2]
  have h4 : |z.2.1 * priceQ z.1 z.2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [hq.1, hq.2]
  unfold sellerObj
  calc _ ≤ |z.2.1 * priceQ z.1 z.2| + |β * ((1 - z.2.1) * f (leftPt z.1 z.2) +
        z.2.1 * f (rightPt z.1 z.2))| := abs_add_le _ _
    _ ≤ 1 + β * ‖f‖ := by
        rw [abs_mul β, abs_of_nonneg hβ]
        exact add_le_add h4 (mul_le_mul_of_nonneg_left h3 hβ)

/-- The operator `T` on `C(D)`. -/
noncomputable def sellerT (hβ : 0 ≤ β) (f : DPt →ᵇ ℝ) : DPt →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => maxValue (sellerObj β f) (fun _ => univ) x)
    (theorem_3_6 (continuous_sellerObj f.continuous).continuousOn (fun _ => isCompact_univ)
      prob_lhc prob_uhc).1 (1 + β * ‖f‖) fun x => by
        obtain ⟨q, -, hval, -⟩ := exists_argmax (Γ := fun _ : DPt => (univ : Set Prob))
          (continuous_sellerObj (β := β) f.continuous).continuousOn isCompact_univ (x := x)
          univ_nonempty
        rw [← hval, Real.norm_eq_abs]
        exact abs_sellerObj_le hβ f _

theorem exists_sellerT_argmax (hβ : 0 ≤ β) (f : DPt →ᵇ ℝ) (x : DPt) :
    ∃ q : Prob, sellerT hβ f x = sellerObj β f (x, q) ∧
      ∀ q' : Prob, sellerObj β f (x, q') ≤ sellerT hβ f x := by
  obtain ⟨q, -, hval, hmax⟩ := exists_argmax (Γ := fun _ : DPt => (univ : Set Prob))
    (continuous_sellerObj (β := β) f.continuous).continuousOn isCompact_univ (x := x)
    univ_nonempty
  exact ⟨q, hval.symm, fun q' => (hmax q' (mem_univ _)).trans_eq hval⟩

/-- **Exercise 5.16a.** `T` is a contraction of modulus `β`: Blackwell's conditions hold, since the
weights `1 − q` and `q` sum to one. -/
theorem sellerT_contraction (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsContraction (sellerT hβ0.le) β := by
  refine ⟨hβ0, hβ1, blackwell hβ0.le (fun f g hfg x => ?_) (fun f a ha x => ?_)⟩
  · obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨-, -, hmax⟩ := exists_sellerT_argmax hβ0.le g x
    change sellerT hβ0.le f x ≤ sellerT hβ0.le g x
    rw [hq]
    refine le_trans ?_ (hmax q)
    rw [sellerObj_apply, sellerObj_apply]
    have e1 : f (leftPt x q) ≤ g (leftPt x q) := hfg _
    have e2 : f (rightPt x q) ≤ g (rightPt x q) := hfg _
    have h1 := mul_le_mul_of_nonneg_left e1
      (mul_nonneg hβ0.le (by linarith [q.2.2] : (0 : ℝ) ≤ 1 - q.1))
    have h2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ0.le q.2.1)
    linarith
  · obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le (f + const DPt a) x
    obtain ⟨-, -, hmax⟩ := exists_sellerT_argmax hβ0.le f x
    change sellerT hβ0.le (f + const DPt a) x ≤ (sellerT hβ0.le f + const DPt (β * a)) x
    rw [hq, BoundedContinuousFunction.add_apply, const_apply]
    have := hmax q
    unfold sellerObj at this ⊢
    simp only [BoundedContinuousFunction.add_apply, const_apply]
    nlinarith

/-- **Exercise 5.16a.** `T` has a unique fixed point `v ∈ C(D)`. -/
theorem ex_5_16a (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ v : DPt →ᵇ ℝ, sellerT hβ0.le v = v ∧ ∀ w, sellerT hβ0.le w = w → w = v := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (sellerT_contraction hβ0 hβ1)
  exact ⟨v, hv, huniq⟩

/-- `λx = (λA, λB)` for `λ ∈ [0, 1]`. -/
def scalePt (lam : ℝ) (hl : lam ∈ Icc (0 : ℝ) 1) (x : DPt) : DPt :=
  ⟨(lam * x.1.1, lam * x.1.2), mul_nonneg hl.1 x.2.1, mul_le_mul_of_nonneg_left x.2.2.1 hl.1,
    by nlinarith [x.2.2.2, hl.2, x.2.1, x.2.2.1]⟩

/-- **Exercise 5.16a.** The fixed point is homogeneous of degree one: `v(λA, λB) = λv(A, B)`
(Corollary 1: `T` preserves the closed set of homogeneous functions). -/
theorem ex_5_16a_hom (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v)
    (lam : ℝ) (hl : lam ∈ Icc (0 : ℝ) 1) (x : DPt) : v (scalePt lam hl x) = lam * v x := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  set H : Set (DPt →ᵇ ℝ) :=
    {f | ∀ lam (hl : lam ∈ Icc (0 : ℝ) 1) x, f (scalePt lam hl x) = lam * f x}
  have hclosed : IsClosed H := by
    have : H = ⋂ lam, ⋂ (hl : lam ∈ Icc (0 : ℝ) 1), ⋂ x,
        {f : DPt →ᵇ ℝ | f (scalePt lam hl x) = lam * f x} := by ext f; simp [H]
    rw [this]
    exact isClosed_iInter fun lam => isClosed_iInter fun hl => isClosed_iInter fun x =>
      isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const x))
  have hscale : ∀ lam (hl : lam ∈ Icc (0 : ℝ) 1) x q,
      leftPt (scalePt lam hl x) q = scalePt lam hl (leftPt x q) ∧
      rightPt (scalePt lam hl x) q = scalePt lam hl (rightPt x q) ∧
      priceQ (scalePt lam hl x) q = lam * priceQ x q := fun lam hl x q => by
    refine ⟨Subtype.ext (Prod.ext ?_ ?_), Subtype.ext (Prod.ext ?_ ?_), ?_⟩ <;>
      simp only [leftPt, rightPt, scalePt, priceQ] <;> ring
  have hmaps : MapsTo (sellerT hβ0.le) H H := fun f hf lam hl x => by
    obtain ⟨q, hq, hmax⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨q', hq', hmax'⟩ := exists_sellerT_argmax hβ0.le f (scalePt lam hl x)
    have hobj : ∀ q, sellerObj β f (scalePt lam hl x, q) = lam * sellerObj β f (x, q) := fun q => by
      obtain ⟨h1, h2, h3⟩ := hscale lam hl x q
      simp only [sellerObj, h1, h2, h3, hf lam hl]
      ring
    refine le_antisymm ?_ ?_
    · rw [hq', hobj]
      exact mul_le_mul_of_nonneg_left (hmax q') hl.1
    · rw [hq, ← hobj]
      exact hmax' q
  exact (corollary_1 (S' := H) (S'' := H) (sellerT_contraction hβ0 hβ1) hv
    ⟨0, fun _ _ _ => by simp⟩ hclosed hmaps hmaps).1 lam hl x

/-! ### Exercise 5.16b -/

/-- The points `(a, 1)` and `(A, A)`. -/
def topPt (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : DPt := ⟨(a, 1), ha.1, ha.2, le_rfl⟩
def diagPt (A : ℝ) (hA : A ∈ Icc (0 : ℝ) 1) : DPt := ⟨(A, A), hA.1, le_rfl, hA.2⟩

/-- `w(a) = v(a, 1)`. -/
noncomputable def wSel (v : DPt → ℝ) (a : ℝ) : ℝ := by
  classical exact if ha : a ∈ Icc (0 : ℝ) 1 then v (topPt a ha) else 0

theorem fe_seller (hβ0 : 0 < β) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) (x : DPt) :
    (∃ q : Prob, v x = sellerObj β v (x, q)) ∧ ∀ q : Prob, sellerObj β v (x, q) ≤ v x := by
  obtain ⟨q, hq, hmax⟩ := exists_sellerT_argmax hβ0.le v x
  rw [hv] at hq hmax
  exact ⟨⟨q, hq⟩, hmax⟩

/-- Charging `A` (`q = 1`) is always available: `v(A, B) ≥ A + βv(A, B)`, so `v ≥ A/(1 − β)`. -/
theorem v_ge (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) (x : DPt) :
    x.1.1 / (1 - β) ≤ v x := by
  have := (fe_seller hβ0 hv x).2 ⟨1, by norm_num, le_rfl⟩
  have hr : rightPt x ⟨1, by norm_num, le_rfl⟩ = x := Subtype.ext (by simp [rightPt, priceQ])
  simp only [sellerObj, priceQ, hr, sub_self, zero_mul, one_mul, zero_add] at this
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Exercise 5.16b.** On the diagonal, `v(A, A) = A/(1 − β)`; in particular `w(1) = 1/(1 − β)`. -/
theorem ex_5_16b_one (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v)
    (A : ℝ) (hA : A ∈ Icc (0 : ℝ) 1) : v (diagPt A hA) = A / (1 - β) := by
  have hge := v_ge hβ0 hβ1 hv (diagPt A hA)
  refine le_antisymm ?_ hge
  obtain ⟨⟨q, hq⟩, -⟩ := fe_seller hβ0 hv (diagPt A hA)
  have hl : leftPt (diagPt A hA) q = diagPt A hA := Subtype.ext (by
    simp only [leftPt, diagPt, priceQ, Prod.mk.injEq, true_and]; ring)
  have hr : rightPt (diagPt A hA) q = diagPt A hA := Subtype.ext (by
    simp only [rightPt, diagPt, priceQ, Prod.mk.injEq, and_true]; ring)
  have hP : priceQ (diagPt A hA) q = A := by simp only [priceQ, diagPt]; ring
  rw [sellerObj, hl, hr, hP] at hq
  have := q.2
  rw [le_div_iff₀ (by linarith)]
  nlinarith [this.2, hA.1]

/-- With `B > 0`, `v(A, B) = Bw(A/B)`: the value depends on the ratio `a = A/B`. -/
theorem v_eq_w (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v)
    (x : DPt) (hB : 0 < x.1.2) : v x = x.1.2 * wSel v (x.1.1 / x.1.2) := by
  have ha : x.1.1 / x.1.2 ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg x.2.1 hB.le, (div_le_one hB).2 x.2.2.1⟩
  have hl : x.1.2 ∈ Icc (0 : ℝ) 1 := ⟨hB.le, x.2.2.2⟩
  have hx : scalePt x.1.2 hl (topPt _ ha) = x := Subtype.ext (by
    simp only [scalePt, topPt, mul_one]
    field_simp)
  simp only [wSel, ha, ↓reduceDIte]
  rw [← ex_5_16a_hom hβ0 hβ1 hv x.1.2 hl, hx]

/-- `f` is convex on `D`. -/
def IsConvexD (f : DPt → ℝ) : Prop :=
  ∀ x y : DPt, ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    f (cmb convex_Dtri h0 h1 x y) ≤ θ * f x + (1 - θ) * f y

/-- **Exercise 5.16b.** `v` is jointly convex on `D` (`T` preserves convexity: each objective is a
convex function of `(A, B)`, since `(A, P)` and `(P, B)` are linear in `(A, B)`). -/
theorem v_convex (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    IsConvexD v := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  set S : Set (DPt →ᵇ ℝ) := {f | IsConvexD f}
  have hclosed : IsClosed S := by
    have : S = ⋂ x, ⋂ y, ⋂ θ : ℝ, ⋂ (h0 : 0 ≤ θ), ⋂ (h1 : θ ≤ 1),
        {f : DPt →ᵇ ℝ | f (cmb convex_Dtri h0 h1 x y) ≤ θ * f x + (1 - θ) * f y} := by
      ext f; simp [S, IsConvexD]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun θ =>
      isClosed_iInter fun h0 => isClosed_iInter fun h1 => isClosed_le (continuous_eval_const _) ?_
    exact (continuous_const.mul (continuous_eval_const x)).add
      (continuous_const.mul (continuous_eval_const y))
  have hmix : ∀ (x y : DPt) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : Prob),
      leftPt (cmb convex_Dtri h0 h1 x y) q = cmb convex_Dtri h0 h1 (leftPt x q) (leftPt y q) ∧
      rightPt (cmb convex_Dtri h0 h1 x y) q = cmb convex_Dtri h0 h1 (rightPt x q) (rightPt y q) ∧
      priceQ (cmb convex_Dtri h0 h1 x y) q = θ * priceQ x q + (1 - θ) * priceQ y q :=
    fun x y θ h0 h1 q => by
      refine ⟨Subtype.ext (Prod.ext ?_ ?_), Subtype.ext (Prod.ext ?_ ?_), ?_⟩ <;>
        simp only [leftPt, rightPt, cmb, priceQ, smul_eq_mul, Prod.smul_fst, Prod.smul_snd,
          Prod.fst_add, Prod.snd_add] <;> ring
  have hmaps : MapsTo (sellerT hβ0.le) S S := fun f hf x y θ h0 h1 => by
    obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f (cmb convex_Dtri h0 h1 x y)
    obtain ⟨-, -, hx⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨-, -, hy⟩ := exists_sellerT_argmax hβ0.le f y
    rw [hq]
    obtain ⟨h1', h2', h3'⟩ := hmix x y θ h0 h1 q
    have e1 := hx q
    have e2 := hy q
    have c1 := hf (leftPt x q) (leftPt y q) θ h0 h1
    have c2 := hf (rightPt x q) (rightPt y q) θ h0 h1
    unfold sellerObj at e1 e2 ⊢
    rw [h1', h2', h3']
    have hq0 := q.2.1
    have hq1 := q.2.2
    have hb := hβ0.le
    have d1 := mul_le_mul_of_nonneg_left c1 (mul_nonneg hb (by linarith : (0 : ℝ) ≤ 1 - q.1))
    have d2 := mul_le_mul_of_nonneg_left c2 (mul_nonneg hb hq0)
    have m1 := mul_le_mul_of_nonneg_left e1 h0
    have m2 := mul_le_mul_of_nonneg_left e2 (by linarith : (0 : ℝ) ≤ 1 - θ)
    nlinarith
  exact (corollary_1 (S' := S) (S'' := S) (sellerT_contraction hβ0 hβ1) hv
    ⟨0, fun _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1

/-- **Exercise 5.16b.** `w` is weakly convex on `[0, 1]`. -/
theorem ex_5_16b_convex (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (wSel v) := by
  refine ⟨convex_Icc 0 1, fun a ha b hb s t hs ht hst => ?_⟩
  have hab : s • a + t • b ∈ Icc (0 : ℝ) 1 := convex_Icc 0 1 ha hb hs ht hst
  have ht' : t = 1 - s := by linarith
  subst ht'
  simp only [wSel, hab, ha, hb, ↓reduceDIte]
  have hc : cmb convex_Dtri hs (by linarith) (topPt a ha) (topPt b hb) = topPt _ hab :=
    Subtype.ext (by simp only [cmb, topPt, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; ring_nf)
  have := v_convex hβ0 hβ1 hv (topPt a ha) (topPt b hb) s hs (by linarith)
  rw [hc] at this
  simpa [smul_eq_mul] using this

/-- `v` is nondecreasing in the lower bound `A` (and in `B`), on `D`. -/
theorem v_mono (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    ∀ x y : DPt, x.1.1 ≤ y.1.1 → x.1.2 ≤ y.1.2 → v x ≤ v y := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  set S : Set (DPt →ᵇ ℝ) := {f | ∀ x y : DPt, x.1.1 ≤ y.1.1 → x.1.2 ≤ y.1.2 → f x ≤ f y}
  have hclosed : IsClosed S := by
    have : S = ⋂ x, ⋂ y, ⋂ (_ : x.1.1 ≤ y.1.1), ⋂ (_ : x.1.2 ≤ y.1.2),
        {f : DPt →ᵇ ℝ | f x ≤ f y} := by ext f; simp [S]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_le (continuous_eval_const x) (continuous_eval_const y)
  have hmaps : MapsTo (sellerT hβ0.le) S S := fun f hf x y h1 h2 => by
    obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f x
    obtain ⟨-, -, hmax⟩ := exists_sellerT_argmax hβ0.le f y
    rw [hq]
    refine le_trans ?_ (hmax q)
    have hP : priceQ x q ≤ priceQ y q := by
      simp only [priceQ]; have := q.2; nlinarith [this.1, this.2]
    have e1 : f (leftPt x q) ≤ f (leftPt y q) := hf (leftPt x q) (leftPt y q) h1 hP
    have e2 : f (rightPt x q) ≤ f (rightPt y q) := hf (rightPt x q) (rightPt y q) hP h2
    rw [sellerObj_apply, sellerObj_apply]
    have m1 := mul_le_mul_of_nonneg_left e1
      (mul_nonneg hβ0.le (by linarith [q.2.2] : (0 : ℝ) ≤ 1 - q.1))
    have m2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ0.le q.2.1)
    have m3 := mul_le_mul_of_nonneg_left hP q.2.1
    linarith
  exact (corollary_1 (S' := S) (S'' := S) (sellerT_contraction hβ0 hβ1) hv
    ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed hmaps hmaps).1

/-- **Exercise 5.16b.** `w` is strictly increasing. -/
theorem ex_5_16b_strictMono (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ}
    (hv : sellerT hβ0.le v = v) : StrictMonoOn (wSel v) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  simp only [wSel, ha, hb, ↓reduceDIte]
  obtain ⟨⟨q, hq⟩, -⟩ := fe_seller hβ0 hv (topPt a ha)
  have hmax := (fe_seller hβ0 hv (topPt b hb)).2 q
  have hP : priceQ (topPt a ha) q ≤ priceQ (topPt b hb) q := by
    simp only [priceQ, topPt]; have := q.2; nlinarith [this.1, this.2]
  have e1 := v_mono hβ0 hβ1 hv (leftPt (topPt a ha) q) (leftPt (topPt b hb) q) hab.le hP
  have e2 := v_mono hβ0 hβ1 hv (rightPt (topPt a ha) q) (rightPt (topPt b hb) q) hP le_rfl
  have hq0 := q.2.1
  rcases eq_or_lt_of_le hq0 with hq00 | hqpos
  · -- `q = 0`: `v(a, 1) = βv(a, 1)`, so `v(a, 1) = 0 < b/(1 − β) ≤ v(b, 1)`
    have hz : v (topPt a ha) = 0 := by
      have hl : leftPt (topPt a ha) q = topPt a ha := Subtype.ext (by
        simp only [leftPt, topPt, priceQ, ← hq00, Prod.mk.injEq, true_and]; ring)
      rw [sellerObj, hl, ← hq00] at hq
      simp only [zero_mul, sub_zero, one_mul, add_zero, zero_add] at hq
      have : (1 - β) * v (topPt a ha) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (by linarith)
    have : b / (1 - β) ≤ v (topPt b hb) := v_ge hβ0 hβ1 hv (topPt b hb)
    have hbpos : 0 < b / (1 - β) := div_pos (lt_of_le_of_lt ha.1 hab) (by linarith)
    linarith
  · -- `q > 0`: the same `q` earns strictly more at `b`
    have hPlt : priceQ (topPt a ha) q < priceQ (topPt b hb) q := by
      simp only [priceQ, topPt]; nlinarith
    rw [hq]
    rw [sellerObj_apply] at hmax ⊢
    have m1 := mul_le_mul_of_nonneg_left e1
      (mul_nonneg hβ0.le (by linarith [q.2.2] : (0 : ℝ) ≤ 1 - q.1))
    have m2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ0.le q.2.1)
    have m3 := mul_lt_mul_of_pos_left hPlt hqpos
    linarith

/-! ### Exercise 5.16c -/

/-- **Exercise 5.16c.** On the region `A(2 − β) ≥ B`, `v(A, B) = A/(1 − β)` and setting `P = A`
(`q = 1`) is optimal; off it (`a < â = 1/(2 − β)`), some price above `A` does strictly better, so
`v(A, B) > A/(1 − β)`. In terms of `w`: `w(a) = a/(1 − β)` exactly for `a ∈ [â, 1]`. -/
theorem ex_5_16c (hβ0 : 0 < β) (hβ1 : β < 1) {v : DPt →ᵇ ℝ} (hv : sellerT hβ0.le v = v) :
    (∀ x : DPt, x.1.2 ≤ x.1.1 * (2 - β) → v x = x.1.1 / (1 - β)) ∧
      (∀ x : DPt, x.1.1 * (2 - β) < x.1.2 → x.1.1 / (1 - β) < v x) := by
  have : Nonempty (DPt →ᵇ ℝ) := ⟨0⟩
  have h1β : 0 < 1 - β := by linarith
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · -- the bound `f ≤ A/(1 − β)` on the region is preserved by `T`
    set S : Set (DPt →ᵇ ℝ) := {f | ∀ x : DPt, x.1.2 ≤ x.1.1 * (2 - β) → f x ≤ x.1.1 / (1 - β)}
    have hclosed : IsClosed S := by
      have : S = ⋂ x : DPt, ⋂ (_ : x.1.2 ≤ x.1.1 * (2 - β)),
          {f : DPt →ᵇ ℝ | f x ≤ x.1.1 / (1 - β)} := by ext f; simp [S]
      rw [this]
      exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (continuous_eval_const x) continuous_const
    have hmaps : MapsTo (sellerT hβ0.le) S S := fun f hf x hx => by
      obtain ⟨q, hq, -⟩ := exists_sellerT_argmax hβ0.le f x
      rw [hq]
      have hP := priceQ_mem x q
      have hq0 := q.2.1
      have hq1 := q.2.2
      -- both children stay in the region
      have hl : f (leftPt x q) ≤ x.1.1 / (1 - β) := hf (leftPt x q) (by
        change priceQ x q ≤ x.1.1 * (2 - β)
        linarith [hP.2])
      have hr : f (rightPt x q) ≤ priceQ x q / (1 - β) := hf (rightPt x q) (by
        change x.1.2 ≤ priceQ x q * (2 - β)
        nlinarith [mul_le_mul_of_nonneg_right hP.1 (by linarith : (0 : ℝ) ≤ 2 - β)])
      rw [sellerObj_apply, le_div_iff₀ h1β]
      -- `qP + β(1 − q)A ≤ A` because `q(B − A) ≤ A(1 − β)` on the region
      have key : q.1 * priceQ x q + β * (1 - q.1) * x.1.1 ≤ x.1.1 := by
        have e : q.1 * priceQ x q + β * (1 - q.1) * x.1.1 - x.1.1 =
            (1 - q.1) * (q.1 * (x.1.2 - x.1.1) - x.1.1 * (1 - β)) := by
          simp only [priceQ]; ring
        have : q.1 * (x.1.2 - x.1.1) ≤ x.1.1 * (1 - β) := by
          have hBA : x.1.2 - x.1.1 ≤ x.1.1 * (1 - β) := by linarith
          have := x.2.2.1
          nlinarith
        nlinarith
      have m1 := mul_le_mul_of_nonneg_left hl (mul_nonneg hβ0.le (by linarith : (0 : ℝ) ≤ 1 - q.1))
      have m2 := mul_le_mul_of_nonneg_left hr (mul_nonneg hβ0.le hq0)
      have e1 : β * (1 - q.1) * (x.1.1 / (1 - β)) * (1 - β) = β * (1 - q.1) * x.1.1 := by
        field_simp
      have e2 : β * q.1 * (priceQ x q / (1 - β)) * (1 - β) = β * q.1 * priceQ x q := by
        field_simp
      have m1' := mul_le_mul_of_nonneg_right m1 h1β.le
      have m2' := mul_le_mul_of_nonneg_right m2 h1β.le
      linarith
    have hvS := (corollary_1 (S' := S) (S'' := S) (sellerT_contraction hβ0 hβ1) hv
      ⟨0, fun x _ => div_nonneg x.2.1 h1β.le⟩ hclosed hmaps hmaps).1
    exact le_antisymm (hvS x hx) (v_ge hβ0 hβ1 hv x)
  · -- a price just above `A` beats `A/(1 − β)`
    have hBA : x.1.1 * (1 - β) < x.1.2 - x.1.1 := by linarith
    have hBA0 : 0 < x.1.2 - x.1.1 := by nlinarith [x.2.1]
    -- choose `q < 1` with `q(B − A) > A(1 − β)`
    set q₀ := (1 + x.1.1 * (1 - β) / (x.1.2 - x.1.1)) / 2
    have hfrac : x.1.1 * (1 - β) / (x.1.2 - x.1.1) < 1 := (div_lt_one hBA0).2 hBA
    have hfrac0 : 0 ≤ x.1.1 * (1 - β) / (x.1.2 - x.1.1) :=
      div_nonneg (mul_nonneg x.2.1 h1β.le) hBA0.le
    have hq0 : 0 ≤ q₀ := by simp only [q₀]; linarith
    have hq1 : q₀ < 1 := by simp only [q₀]; linarith
    have hqgap : x.1.1 * (1 - β) < q₀ * (x.1.2 - x.1.1) := by
      have : x.1.1 * (1 - β) / (x.1.2 - x.1.1) < q₀ := by simp only [q₀]; linarith
      rwa [div_lt_iff₀ hBA0] at this
    set q : Prob := ⟨q₀, hq0, hq1.le⟩
    have hle := (fe_seller hβ0 hv x).2 q
    have hl : x.1.1 / (1 - β) ≤ v (leftPt x q) := v_ge hβ0 hβ1 hv (leftPt x q)
    have hr : priceQ x q / (1 - β) ≤ v (rightPt x q) := v_ge hβ0 hβ1 hv (rightPt x q)
    have hqv : (q : ℝ) = q₀ := rfl
    rw [sellerObj_apply, hqv] at hle
    rw [div_lt_iff₀ h1β]
    have e : q₀ * priceQ x q + β * (1 - q₀) * x.1.1 - x.1.1 =
        (1 - q₀) * (q₀ * (x.1.2 - x.1.1) - x.1.1 * (1 - β)) := by
      simp only [priceQ, q]; ring
    have hpos : 0 < (1 - q₀) * (q₀ * (x.1.2 - x.1.1) - x.1.1 * (1 - β)) :=
      mul_pos (by linarith) (by linarith)
    have m1 := mul_le_mul_of_nonneg_left hl (mul_nonneg hβ0.le (by linarith : (0 : ℝ) ≤ 1 - q₀))
    have m2 := mul_le_mul_of_nonneg_left hr (mul_nonneg hβ0.le hq0)
    have e1 : β * (1 - q₀) * (x.1.1 / (1 - β)) * (1 - β) = β * (1 - q₀) * x.1.1 := by field_simp
    have e2 : β * q₀ * (priceQ x q / (1 - β)) * (1 - β) = β * q₀ * priceQ x q := by field_simp
    have m1' := mul_le_mul_of_nonneg_right m1 h1β.le
    have m2' := mul_le_mul_of_nonneg_right m2 h1β.le
    have hle' := mul_le_mul_of_nonneg_right hle h1β.le
    linarith

end StokeyLucasPrescott.DeterministicApplications
