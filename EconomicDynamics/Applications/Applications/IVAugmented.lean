/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.IVQTheory
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# §8.6.3 Augmented adjustment costs

Miao, §8.6.3, pp. 281–287. Investment costs `C(I, K) = p_bI + φ(K) + Ψ(I, K)` for `I > 0`,
`0` for `I = 0`, `p_sI + φ(K) + Ψ(I, K)` for `I < 0` (`iv_C`), with `p_b > p_s ≥ 0`.

The book proceeds heuristically ("Interested readers are invited to make the arguments below more
rigorous"). We prove:

* **The Bellman equation (8.35)** as an identity of suprema: with `R(I) = π − C(I, K) +
  W((1 − δ)K + I)` (`W = βE[V(·, z′) | z]`), `sup_I R = max{Vⁱ, Vᵇ, Vˢ}` with `Vⁱ = R(0)`,
  `Vᵇ = sup_{I>0} R`, `Vˢ = sup_{I<0} R` (`eq_8_35`, `iv_C_eq_objective`).
* **(8.36)**: for `I ≠ 0`, `R(I) − R(0)` is the objective of (8.36) (`eq_8_36`), so the gain
  from adjusting is `ϕ = sup_{I≠0}(R(I) − R(0)) = max(Vᵇ, Vˢ) − Vⁱ` (`iv_phi_eq`), and
  `ϕ = 0` iff `Vⁱ = max(Vᵇ, Vˢ)`: (8.46)–(8.47) are the boundaries `ϕ = 0` (`eq_8_46_8_47`).
  **Correction**: as printed, (8.36) charges `φ(K)` also at `I = 0`; it must be charged only for
  `I ≠ 0` (counterexample `iv_eq_8_36_misprint` in `IVExample861`).
* **(8.37)**: the first-order Taylor expansion `W(x + I) − W(x) = QI + o(I)`
  (`eq_8_37_taylor`), and footnote 8: at an optimal `I* > 0`,
  `p_b + Ψ₁(I*, K) = βE[V₁((1 − δ)K + I*, z′) | z]` (`iv_footnote_8`).
* **(8.38)–(8.40)**, the static problem `ψ(Q, K) = max_I QI − p_sI1_{I<0} − p_bI1_{I>0} −
  Ψ(I, K)` (`iv_g`): sufficiency for convex `Ψ` (`eq_8_38`, `eq_8_39`, `eq_8_40`), necessity
  for strictly convex differentiable `Ψ` with `Ψ₁(0, K) = 0` (`iv_static_necessary`), and
  optimal investment weakly increasing in `Q`, with or without fixed costs
  (`iv_static_mono`).
* **(8.41)–(8.42)**: `Q(K, z) = βE[V₁((1 − δ)K, z′) | z]` decreases in `K` (concave `V`) and
  increases in `z` (`V₁` increasing in `z′`, monotone `P`) (`iv_q_monotone`); hence the buy
  and sell boundaries (largest solutions of `Q = p_b`, `Q = p_s`) increase with `z`
  (`iv_boundary_mono`); the buy / sell / inaction regions (`iv_buy_region`, `iv_sell_region`,
  `iv_inaction_region`, `iv_boundaries_ordered`).
* **Irreversibility** (`p_s = 0`): (8.42) has no solution when `Q > 0`
  (`iv_irreversible_no_sell_boundary`) and negative investment is never optimal
  (`iv_irreversible`).
* **Fixed costs (8.43)–(8.45)**: (8.38)–(8.40) remain necessary (`iv_fixed_foc_necessary`);
  with `Q₁, Q₂` the points where `ψ − φ` crosses zero, the investment rule (8.43)–(8.45)
  (`eq_8_43`, `eq_8_44`, `eq_8_45`), and fixed costs widen the inaction region,
  `Q₁ < p_s ≤ p_b < Q₂` (`iv_fixed_widens`).

Not formalised: the claims "it is intuitive that the firm will buy capital if `K < Kᵇ(z)` …"
and "these two boundaries are increasing functions of `z`" in the presence of fixed costs
(p. 287), which the book does not derive; the figures.
-/

namespace Miao.Applications

open Filter Topology

/-- The augmented adjustment cost `C(I, K)` (Miao, p. 281). -/
noncomputable def iv_C (pb ps : ℝ) (φ : ℝ → ℝ) (Ψ : ℝ × ℝ → ℝ) (I K : ℝ) : ℝ :=
  if 0 < I then pb * I + φ K + Ψ (I, K) else if I < 0 then ps * I + φ K + Ψ (I, K) else 0

/-- Miao, p. 281: when `Ψ(0, K) = 0`, `C(I, K)` is the cost in the firm's objective,
`p_bI1_{I≥0} + p_sI1_{I≤0} + φ(K)1_{I≠0} + Ψ(I, K)`. -/
theorem iv_C_eq_objective {pb ps : ℝ} {φ : ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ} (I K : ℝ)
    (hΨ0 : Ψ (0, K) = 0) :
    iv_C pb ps φ Ψ I K = (if 0 ≤ I then pb * I else 0) + (if I ≤ 0 then ps * I else 0)
      + (if I ≠ 0 then φ K else 0) + Ψ (I, K) := by
  unfold iv_C
  rcases lt_trichotomy I 0 with h | h | h
  · simp [h, h.le, h.ne, not_lt.2 h.le, not_le.2 h]
  · subst h; simp [hΨ0]
  · simp [h, h.le, h.ne', not_le.2 h]

/-- **The Bellman equation (8.35)** (Miao, p. 281): for `R` bounded above (the right side of the
Bellman equation as a function of `I`),
`sup_I R(I) = max{R(0), sup_{I>0} R(I), sup_{I<0} R(I)} = max{Vⁱ, Vᵇ, Vˢ}`. -/
theorem eq_8_35 {R : ℝ → ℝ} (hb : BddAbove (Set.range R)) :
    ⨆ I, R I = max (R 0) (max (⨆ I : Set.Ioi (0 : ℝ), R I) (⨆ I : Set.Iio (0 : ℝ), R I)) := by
  have hbi : BddAbove (Set.range fun I : Set.Ioi (0 : ℝ) => R I) :=
    hb.mono (Set.range_subset_iff.2 fun i => Set.mem_range_self (i : ℝ))
  have hbs : BddAbove (Set.range fun I : Set.Iio (0 : ℝ) => R I) :=
    hb.mono (Set.range_subset_iff.2 fun i => Set.mem_range_self (i : ℝ))
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have : Nonempty (Set.Iio (0 : ℝ)) := ⟨⟨-1, by norm_num⟩⟩
  apply le_antisymm
  · refine ciSup_le fun I => ?_
    rcases lt_trichotomy I 0 with h | h | h
    · exact le_max_of_le_right (le_max_of_le_right (le_ciSup hbs ⟨I, h⟩))
    · subst h; exact le_max_left _ _
    · exact le_max_of_le_right (le_max_of_le_left (le_ciSup hbi ⟨I, h⟩))
  · exact max_le (le_ciSup hb 0)
      (max_le (ciSup_le fun i => le_ciSup hb i) (ciSup_le fun i => le_ciSup hb i))

/-- The right side of the Bellman equation (8.35) as a function of investment `I`
(Miao, pp. 281–282): `R(I) = π(K, z) − C(I, K) + W((1 − δ)K + I)`, where
`W(K′) = βE[V(K′, z′) | z]`. -/
noncomputable def iv_R (pb ps : ℝ) (φ : ℝ → ℝ) (Ψ : ℝ × ℝ → ℝ) (prof : ℝ) (W : ℝ → ℝ)
    (δ K I : ℝ) : ℝ :=
  prof - iv_C pb ps φ Ψ I K + W ((1 - δ) * K + I)

/-- **(8.36)** (Miao, p. 282), corrected: for `I ≠ 0`, `R(I) − R(0)` is the objective of
(8.36), `W((1 − δ)K + I) − W((1 − δ)K) − p_sI1_{I<0} − p_bI1_{I>0} − φ(K) − Ψ(I, K)`.
(`R(0) = π + W((1 − δ)K) = Vⁱ`; at `I = 0` the objective is `0`, not `−φ(K)`.) -/
theorem eq_8_36 {pb ps : ℝ} {φ : ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ} {prof : ℝ} {W : ℝ → ℝ} {δ K I : ℝ}
    (hI : I ≠ 0) :
    iv_R pb ps φ Ψ prof W δ K I - iv_R pb ps φ Ψ prof W δ K 0 =
      W ((1 - δ) * K + I) - W ((1 - δ) * K) - (if I < 0 then ps * I else 0)
        - (if 0 < I then pb * I else 0) - φ K - Ψ (I, K) := by
  unfold iv_R iv_C
  rcases lt_or_gt_of_ne hI with h | h
  · simp [h, not_lt.2 h.le]; ring
  · simp [h, not_lt.2 h.le]; ring

/-- Miao, p. 287: the gain from adjusting, `ϕ = sup_{I≠0} (R(I) − R(0))`, equals
`max(Vᵇ, Vˢ) − Vⁱ`. -/
theorem iv_phi_eq {R : ℝ → ℝ} (hb : BddAbove (Set.range R)) :
    ⨆ I : {I : ℝ // I ≠ 0}, (R I - R 0) =
      max (⨆ I : Set.Ioi (0 : ℝ), R I) (⨆ I : Set.Iio (0 : ℝ), R I) - R 0 := by
  have hbi : BddAbove (Set.range fun I : Set.Ioi (0 : ℝ) => R I) :=
    hb.mono (Set.range_subset_iff.2 fun i => Set.mem_range_self (i : ℝ))
  have hbs : BddAbove (Set.range fun I : Set.Iio (0 : ℝ) => R I) :=
    hb.mono (Set.range_subset_iff.2 fun i => Set.mem_range_self (i : ℝ))
  have hbn : BddAbove (Set.range fun I : {I : ℝ // I ≠ 0} => R I - R 0) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M - R 0, Set.forall_mem_range.2 fun i => by
      have := hM (Set.mem_range_self (i : ℝ))
      linarith⟩
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have : Nonempty (Set.Iio (0 : ℝ)) := ⟨⟨-1, by norm_num⟩⟩
  have : Nonempty {I : ℝ // I ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  apply le_antisymm
  · refine ciSup_le fun I => ?_
    rcases lt_or_gt_of_ne I.2 with h | h
    · have := le_ciSup hbs ⟨I, h⟩
      have := le_max_right (⨆ I : Set.Ioi (0 : ℝ), R I) (⨆ I : Set.Iio (0 : ℝ), R I)
      simp only at *
      linarith
    · have := le_ciSup hbi ⟨I, h⟩
      have := le_max_left (⨆ I : Set.Ioi (0 : ℝ), R I) (⨆ I : Set.Iio (0 : ℝ), R I)
      simp only at *
      linarith
  · rw [sub_le_iff_le_add]
    refine max_le (ciSup_le fun i => ?_) (ciSup_le fun i => ?_)
    · have := le_ciSup hbn ⟨i, i.2.ne'⟩
      simp only at this
      linarith
    · have := le_ciSup hbn ⟨i, i.2.ne⟩
      simp only at this
      linarith

/-- **(8.46)–(8.47)** (Miao, p. 287): "equivalently, the two boundaries are determined by the
solutions to `ϕ(K, z) = 0`": `ϕ = 0` iff `Vⁱ = max(Vᵇ, Vˢ)` (indifference between inaction and
the better adjustment), and `ϕ ≤ 0` iff inaction is optimal, `V = Vⁱ`. -/
theorem eq_8_46_8_47 {R : ℝ → ℝ} (hb : BddAbove (Set.range R)) :
    (⨆ I : {I : ℝ // I ≠ 0}, (R I - R 0) = 0 ↔
      R 0 = max (⨆ I : Set.Ioi (0 : ℝ), R I) (⨆ I : Set.Iio (0 : ℝ), R I)) ∧
    (⨆ I : {I : ℝ // I ≠ 0}, (R I - R 0) ≤ 0 ↔ ⨆ I, R I = R 0) := by
  rw [iv_phi_eq hb, eq_8_35 hb]
  constructor
  · constructor <;> intro h <;> linarith
  · constructor
    · intro h; exact max_eq_left (by linarith)
    · intro h
      have := le_max_right (R 0)
        (max (⨆ I : Set.Ioi (0 : ℝ), R I) (⨆ I : Set.Iio (0 : ℝ), R I))
      linarith

/-- **(8.37)** (Miao, p. 282), the first-order Taylor approximation behind
`ϕ(K, z) ≃ max_I QI − …`: if `W(K′) = βE[V(K′, z′) | z]` is differentiable at `x = (1 − δ)K`
with derivative `Q = βE[V₁((1 − δ)K, z′) | z]`, then `W(x + I) − W(x) = QI + o(I)`. -/
theorem eq_8_37_taylor {W : ℝ → ℝ} {x Q : ℝ} (hW : HasDerivAt W Q x) :
    (fun I => W (x + I) - W x - Q * I) =o[𝓝 0] fun I => I := by
  have := hasDerivAt_iff_isLittleO_nhds_zero.1 hW
  simpa [smul_eq_mul, mul_comm] using this

/-- Footnote 8 (Miao, p. 283): if `I* > 0` is a local maximiser of the right side of the
Bellman equation, `W` is differentiable at `(1 − δ)K + I*` and `Ψ(·, K)` at `I*`, then
`p_b + Ψ₁(I*, K) = W′((1 − δ)K + I*) = βE[V₁((1 − δ)K + I*, z′) | z]`. -/
theorem iv_footnote_8 {pb ps : ℝ} {φ : ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ} {prof : ℝ} {W : ℝ → ℝ}
    {δ K I dW Ψ1 : ℝ} (hI : 0 < I) (hmax : IsLocalMax (iv_R pb ps φ Ψ prof W δ K) I)
    (hW : HasDerivAt W dW ((1 - δ) * K + I)) (hΨ : HasDerivAt (fun J => Ψ (J, K)) Ψ1 I) :
    pb + Ψ1 = dW := by
  have heq : ∀ᶠ J in 𝓝 I, iv_R pb ps φ Ψ prof W δ K J =
      prof - (pb * J + φ K + Ψ (J, K)) + W ((1 - δ) * K + J) := by
    filter_upwards [Ioi_mem_nhds hI] with J hJ
    simp [iv_R, iv_C, Set.mem_Ioi.1 hJ]
  have hW' : HasDerivAt (fun J => W ((1 - δ) * K + J)) dW I := by
    have hin : HasDerivAt (fun J : ℝ => (1 - δ) * K + J) 1 I := by
      simpa using (hasDerivAt_id I).const_add ((1 - δ) * K)
    have h := hW.comp I hin
    rw [mul_one] at h
    exact h
  have d : HasDerivAt (fun J => prof - (pb * J + φ K + Ψ (J, K)) + W ((1 - δ) * K + J))
      (0 - (pb * 1 + 0 + Ψ1) + dW) I :=
    ((hasDerivAt_const I prof).sub ((((hasDerivAt_id I).const_mul pb).add
      (hasDerivAt_const I (φ K))).add hΨ)).add hW'
  have hmax' : IsLocalMax (fun J => prof - (pb * J + φ K + Ψ (J, K)) + W ((1 - δ) * K + J)) I :=
    hmax.congr heq
  have := hmax'.hasDerivAt_eq_zero d
  linarith

/-- The objective of the static investment problem `ψ(Q, K)` (Miao, p. 282), for a fixed `K`
(`Ψ` stands for `Ψ(·, K)`): `QI − p_sI1_{I<0} − p_bI1_{I>0} − Ψ(I)`. -/
noncomputable def iv_g (pb ps : ℝ) (Ψ : ℝ → ℝ) (Q I : ℝ) : ℝ :=
  Q * I - (if 0 < I then pb * I else if I < 0 then ps * I else 0) - Ψ I

/-- The static objective with a fixed cost `φ` paid when `I ≠ 0` (Miao, pp. 285–286). -/
noncomputable def iv_gφ (pb ps φ : ℝ) (Ψ : ℝ → ℝ) (Q I : ℝ) : ℝ :=
  iv_g pb ps Ψ Q I - (if I = 0 then 0 else φ)

/-- `g ≤ (Q − p_b)I − Ψ(I)` everywhere, with equality for `I ≥ 0` (when `p_s ≤ p_b` and
`Ψ(0) = 0`). -/
theorem iv_g_le_buy {pb ps Q : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb) (hΨ0 : Ψ 0 = 0) (I : ℝ) :
    iv_g pb ps Ψ Q I ≤ (Q - pb) * I - Ψ I ∧ (0 ≤ I → iv_g pb ps Ψ Q I = (Q - pb) * I - Ψ I) := by
  unfold iv_g
  rcases lt_trichotomy I 0 with h | h | h
  · simp only [not_lt.2 h.le, h, ↓reduceIte]
    exact ⟨by nlinarith, fun h' => absurd h' (not_le.2 h)⟩
  · subst h; simp [hΨ0]
  · simp only [h, ↓reduceIte]
    exact ⟨by linarith, fun _ => by ring⟩

/-- `g ≤ (Q − p_s)I − Ψ(I)` everywhere, with equality for `I ≤ 0`. -/
theorem iv_g_le_sell {pb ps Q : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb) (hΨ0 : Ψ 0 = 0) (I : ℝ) :
    iv_g pb ps Ψ Q I ≤ (Q - ps) * I - Ψ I ∧ (I ≤ 0 → iv_g pb ps Ψ Q I = (Q - ps) * I - Ψ I) := by
  unfold iv_g
  rcases lt_trichotomy I 0 with h | h | h
  · simp only [not_lt.2 h.le, h, ↓reduceIte]
    exact ⟨by linarith, fun _ => by ring⟩
  · subst h; simp [hΨ0]
  · simp only [h, ↓reduceIte]
    exact ⟨by nlinarith, fun h' => absurd h' (not_le.2 h)⟩

/-- A concave function with zero derivative at `x` is maximised at `x`. -/
theorem iv_concave_max {f : ℝ → ℝ} (hf : ConcaveOn ℝ Set.univ f) {x : ℝ}
    (hd : HasDerivAt f 0 x) (y : ℝ) : f y ≤ f x := by
  have := eu_concave_le_fderiv hf (Set.mem_univ x) (Set.mem_univ y) hd.hasFDerivAt
  simpa using this

/-- **(8.38)** (Miao, p. 283), sufficiency: no fixed cost, `Ψ(·, K)` convex with `Ψ(0) = 0`,
`p_s ≤ p_b`. If `I* > 0` and `p_b + Ψ₁(I*) = Q` (possible only when `Q > p_b`, see
`iv_static_necessary`), then `I*` maximises `QI − p_sI1_{I<0} − p_bI1_{I>0} − Ψ(I)`. -/
theorem eq_8_38 {pb ps Q Is Ψ1 : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb) (hΨ0 : Ψ 0 = 0)
    (hconv : ConvexOn ℝ Set.univ Ψ) (hd : HasDerivAt Ψ Ψ1 Is) (hIs : 0 < Is)
    (hfoc : pb + Ψ1 = Q) (I : ℝ) : iv_g pb ps Ψ Q I ≤ iv_g pb ps Ψ Q Is := by
  have hc : ConcaveOn ℝ Set.univ (fun J => (Q - pb) * J - Ψ J) :=
    ((LinearMap.mulLeft ℝ (Q - pb)).concaveOn convex_univ).sub hconv
  have hd' : HasDerivAt (fun J => (Q - pb) * J - Ψ J) 0 Is := by
    have := ((hasDerivAt_id Is).const_mul (Q - pb)).sub hd
    rw [show (Q - pb) * 1 - Ψ1 = 0 by linarith] at this
    exact this
  rw [(iv_g_le_buy hp hΨ0 Is).2 hIs.le]
  exact (iv_g_le_buy hp hΨ0 I).1.trans (iv_concave_max hc hd' I)

/-- **(8.39)** (Miao, p. 283): no fixed cost, `Ψ ≥ 0`, `Ψ(0) = 0`. If `p_s ≤ Q ≤ p_b`,
`I* = 0` is optimal. -/
theorem eq_8_39 {pb ps Q : ℝ} {Ψ : ℝ → ℝ} (hΨ0 : Ψ 0 = 0) (hnn : ∀ I, 0 ≤ Ψ I)
    (h1 : ps ≤ Q) (h2 : Q ≤ pb) (I : ℝ) : iv_g pb ps Ψ Q I ≤ iv_g pb ps Ψ Q 0 := by
  unfold iv_g
  have := hnn I
  rcases lt_trichotomy I 0 with h | h | h
  · simp only [not_lt.2 h.le, h, ↓reduceIte, lt_irrefl, hΨ0]; nlinarith
  · subst h; exact le_rfl
  · simp only [h, ↓reduceIte, lt_irrefl, hΨ0]; nlinarith

/-- **(8.40)** (Miao, p. 283), sufficiency: if `I* < 0` and `p_s + Ψ₁(I*) = Q` (possible only
when `Q < p_s`), then `I*` is optimal. -/
theorem eq_8_40 {pb ps Q Is Ψ1 : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb) (hΨ0 : Ψ 0 = 0)
    (hconv : ConvexOn ℝ Set.univ Ψ) (hd : HasDerivAt Ψ Ψ1 Is) (hIs : Is < 0)
    (hfoc : ps + Ψ1 = Q) (I : ℝ) : iv_g pb ps Ψ Q I ≤ iv_g pb ps Ψ Q Is := by
  have hc : ConcaveOn ℝ Set.univ (fun J => (Q - ps) * J - Ψ J) :=
    ((LinearMap.mulLeft ℝ (Q - ps)).concaveOn convex_univ).sub hconv
  have hd' : HasDerivAt (fun J => (Q - ps) * J - Ψ J) 0 Is := by
    have := ((hasDerivAt_id Is).const_mul (Q - ps)).sub hd
    rw [show (Q - ps) * 1 - Ψ1 = 0 by linarith] at this
    exact this
  rw [(iv_g_le_sell hp hΨ0 Is).2 hIs.le]
  exact (iv_g_le_sell hp hΨ0 I).1.trans (iv_concave_max hc hd' I)

/-- **(8.38)–(8.40)** (Miao, p. 283), necessity: let `Ψ` be differentiable with `Ψ₁` strictly
increasing, `Ψ(0) = 0`, `Ψ₁(0) = 0`, and `p_s ≤ p_b`. If `I*` maximises the static objective,
then `I* > 0 → p_b + Ψ₁(I*) = Q ∧ Q > p_b`; `I* = 0 → p_s ≤ Q ≤ p_b`;
`I* < 0 → p_s + Ψ₁(I*) = Q ∧ Q < p_s`. Together with `eq_8_38`–`eq_8_40`: three regimes. -/
theorem iv_static_necessary {pb ps Q Is : ℝ} {Ψ Ψ1 : ℝ → ℝ} (hp : ps ≤ pb) (hΨ0 : Ψ 0 = 0)
    (hd : ∀ I, HasDerivAt Ψ (Ψ1 I) I) (hmono : StrictMono Ψ1) (hΨ10 : Ψ1 0 = 0)
    (hmax : ∀ I, iv_g pb ps Ψ Q I ≤ iv_g pb ps Ψ Q Is) :
    (0 < Is → pb + Ψ1 Is = Q ∧ pb < Q) ∧ (Is = 0 → ps ≤ Q ∧ Q ≤ pb) ∧
      (Is < 0 → ps + Ψ1 Is = Q ∧ Q < ps) := by
  have dbuy : ∀ x, HasDerivAt (fun J => (Q - pb) * J - Ψ J) ((Q - pb) - Ψ1 x) x := fun x => by
    have h := ((hasDerivAt_id x).const_mul (Q - pb)).sub (hd x)
    rw [mul_one] at h
    exact h
  have dsell : ∀ x, HasDerivAt (fun J => (Q - ps) * J - Ψ J) ((Q - ps) - Ψ1 x) x := fun x => by
    have h := ((hasDerivAt_id x).const_mul (Q - ps)).sub (hd x)
    rw [mul_one] at h
    exact h
  refine ⟨fun hIs => ?_, fun hIs => ?_, fun hIs => ?_⟩
  · have hloc : IsLocalMax (fun J => (Q - pb) * J - Ψ J) Is := by
      filter_upwards [Ioi_mem_nhds hIs] with J hJ
      rw [← (iv_g_le_buy hp hΨ0 J).2 (le_of_lt hJ), ← (iv_g_le_buy hp hΨ0 Is).2 hIs.le]
      exact hmax J
    have := hloc.hasDerivAt_eq_zero (dbuy Is)
    have := hmono hIs
    constructor <;> linarith
  · subst hIs
    have hr := (dbuy 0).tendsto_slope_zero_right
    have hl := (dsell 0).tendsto_slope_zero_left
    have h1 : (Q - pb) - Ψ1 0 ≤ 0 := by
      refine le_of_tendsto hr ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      have := hmax t
      rw [(iv_g_le_buy hp hΨ0 t).2 ht'.le, (iv_g_le_buy hp hΨ0 0).2 le_rfl] at this
      simp only [zero_add, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht'.le) (by linarith)
    have h2 : 0 ≤ (Q - ps) - Ψ1 0 := by
      refine ge_of_tendsto hl ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t < 0 := ht
      have := hmax t
      rw [(iv_g_le_sell hp hΨ0 t).2 ht'.le, (iv_g_le_sell hp hΨ0 0).2 le_rfl] at this
      simp only [zero_add, smul_eq_mul]
      exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 ht'.le) (by linarith)
    rw [hΨ10] at h1 h2
    constructor <;> linarith
  · have hloc : IsLocalMax (fun J => (Q - ps) * J - Ψ J) Is := by
      filter_upwards [Iio_mem_nhds hIs] with J hJ
      rw [← (iv_g_le_sell hp hΨ0 J).2 (le_of_lt hJ), ← (iv_g_le_sell hp hΨ0 Is).2 hIs.le]
      exact hmax J
    have := hloc.hasDerivAt_eq_zero (dsell Is)
    have := hmono hIs
    constructor <;> linarith

/-- Miao, p. 283 ("optimal investment is weakly increasing in `Q`"), for any objective of the
form `QI − c(I)`, in particular the static problem with or without fixed costs: if `I`
is optimal at `Q` and `I′` at `Q′ > Q`, then `I ≤ I′`. -/
theorem iv_static_mono {c : ℝ → ℝ} {Q Q' I I' : ℝ} (hQ : Q < Q')
    (hI : ∀ J, Q * J - c J ≤ Q * I - c I) (hI' : ∀ J, Q' * J - c J ≤ Q' * I' - c I') :
    I ≤ I' := by
  have h1 := hI I'
  have h2 := hI' I
  nlinarith

/-- Irreversibility (Miao, p. 284): with `p_s = 0` and `Q > 0`, negative investment is never
optimal: `g(I) < g(0)` for every `I < 0` (`Ψ ≥ 0`, `Ψ(0) = 0`). -/
theorem iv_irreversible {pb Q : ℝ} {Ψ : ℝ → ℝ} (hΨ0 : Ψ 0 = 0) (hnn : ∀ I, 0 ≤ Ψ I)
    (hQ : 0 < Q) {I : ℝ} (hI : I < 0) : iv_g pb 0 Ψ Q I < iv_g pb 0 Ψ Q 0 := by
  unfold iv_g
  have := hnn I
  simp only [not_lt.2 hI.le, hI, ↓reduceIte, lt_irrefl, hΨ0]
  nlinarith

/-- Irreversibility (Miao, p. 284): "in the special case of `p_s = 0`, equation (8.42) cannot
hold" when marginal Q is positive (`V₁ > 0`). -/
theorem iv_irreversible_no_sell_boundary {Z : Type*} {q : ℝ → Z → ℝ} (hq : ∀ K z, 0 < q K z)
    (z : Z) : ¬ ∃ K, q K z = 0 := by
  rintro ⟨K, hK⟩
  linarith [hq K z]

/-- **(8.41)–(8.42)** (Miao, p. 283): marginal Q at zero investment,
`Q(K, z) = βE[V₁((1 − δ)K, z′) | z]` (8.37), is decreasing in `K` if `V₁(·, z′)` is decreasing
(`V` concave) and increasing in `z` if `V₁(K, ·)` is increasing and the conditional expectation
`E` is monotone (`f ≤ g ⇒ Ef ≤ Eg`) and maps increasing functions to increasing functions (`P`
monotone). Here `1 − δ > 0`, `β ≥ 0`. -/
theorem iv_q_monotone {Z : Type*} [Preorder Z] {E : (Z → ℝ) → Z → ℝ} {V1 : ℝ → Z → ℝ}
    {β δ : ℝ} (hβ : 0 ≤ β) (hδ : δ < 1) (hEmono : ∀ f g, (∀ z', f z' ≤ g z') → ∀ z, E f z ≤ E g z)
    (hP : ∀ f, Monotone f → Monotone (E f)) (hconc : ∀ z', Antitone fun K => V1 K z')
    (hz : ∀ K, Monotone (V1 K)) :
    (∀ z, Antitone fun K => β * E (fun z' => V1 ((1 - δ) * K) z') z) ∧
      ∀ K, Monotone fun z => β * E (fun z' => V1 ((1 - δ) * K) z') z := by
  refine ⟨fun z K K' hKK' => ?_, fun K z z' hzz' => ?_⟩
  · refine mul_le_mul_of_nonneg_left (hEmono _ _ (fun z' => hconc z' ?_) z) hβ
    exact mul_le_mul_of_nonneg_left hKK' (by linarith)
  · exact mul_le_mul_of_nonneg_left (hP _ (hz _) hzz') hβ

/-- **(8.41)** (Miao, p. 283): "`Kᵇ(z)` increases with `z`". If `Q(K, z)` is decreasing in `K`
and increasing in `z`, the largest solution `Kᵇ(z)` of `p_b = Q(K, z)` is increasing in `z`
(the same holds for `Kˢ(z)`, (8.42), with `p_s`). -/
theorem iv_boundary_mono {Z : Type*} [Preorder Z] {q : ℝ → Z → ℝ} {p : ℝ} {Kb : Z → ℝ}
    (hanti : ∀ z, Antitone fun K => q K z) (hmono : ∀ K, Monotone (q K))
    (hKb : ∀ z, IsGreatest {K | q K z = p} (Kb z)) {z z' : Z} (hzz' : z ≤ z') :
    Kb z ≤ Kb z' := by
  by_contra hc
  have hlt : Kb z' < Kb z := lt_of_not_ge hc
  have h1 : p ≤ q (Kb z) z' := by
    have := hmono (Kb z) hzz'
    rw [show q (Kb z) z = p from (hKb z).1] at this
    exact this
  have h2 : q (Kb z) z' ≤ p := by
    have : q (Kb z) z' ≤ q (Kb z') z' := hanti z' hlt.le
    rw [show q (Kb z') z' = p from (hKb z').1] at this
    exact this
  have hsol : Kb z ∈ {K | q K z' = p} := le_antisymm h2 h1
  exact absurd ((hKb z').2 hsol) (not_le.2 hlt)

/-- The buy region (Miao, p. 283): if `Q(·, z)` is strictly decreasing and `Q(Kᵇ(z), z) = p_b`,
then below the boundary `Q > p_b` and the firm buys capital ((8.38)). -/
theorem iv_buy_region {q : ℝ → ℝ} {pb Kb K : ℝ} (hanti : StrictAnti q) (hKb : q Kb = pb)
    (hK : K < Kb) : pb < q K := hKb ▸ hanti hK

/-- The sell region (Miao, p. 283): above `Kˢ(z)`, `Q < p_s` and the firm sells capital
((8.40)). -/
theorem iv_sell_region {q : ℝ → ℝ} {ps Ks K : ℝ} (hanti : StrictAnti q) (hKs : q Ks = ps)
    (hK : Ks < K) : q K < ps := hKs ▸ hanti hK

/-- The inaction region (Miao, p. 284): between the boundaries `p_s ≤ Q ≤ p_b`, so the firm
neither invests nor disinvests ((8.39)). -/
theorem iv_inaction_region {q : ℝ → ℝ} {pb ps Kb Ks K : ℝ} (hanti : Antitone q)
    (hKb : q Kb = pb) (hKs : q Ks = ps) (h1 : Kb ≤ K) (h2 : K ≤ Ks) : ps ≤ q K ∧ q K ≤ pb :=
  ⟨hKs ▸ hanti h2, hKb ▸ hanti h1⟩

/-- The buy boundary lies below the sell boundary (Miao, Figure 8.8, p. 285): if
`p_s < p_b` and `Q(·, z)` is decreasing, `Kᵇ(z) < Kˢ(z)`. -/
theorem iv_boundaries_ordered {q : ℝ → ℝ} {pb ps Kb Ks : ℝ} (hanti : Antitone q)
    (hp : ps < pb) (hKb : q Kb = pb) (hKs : q Ks = ps) : Kb < Ks := by
  by_contra hc
  have := hanti (not_lt.1 hc)
  rw [hKb, hKs] at this
  linarith

/-- Fixed costs (Miao, p. 286): "(8.38)–(8.40) are still first-order necessary conditions". If
`I* ≠ 0` maximises the objective with fixed cost `φ ≥ 0`, it maximises the objective without
it and `g(I*) ≥ φ`; so `iv_static_necessary` applies to `I*`. -/
theorem iv_fixed_foc_necessary {pb ps φ Q Is : ℝ} {Ψ : ℝ → ℝ} (hΨ0 : Ψ 0 = 0) (hφ : 0 ≤ φ)
    (hIs : Is ≠ 0) (hmax : ∀ I, iv_gφ pb ps φ Ψ Q I ≤ iv_gφ pb ps φ Ψ Q Is) :
    (∀ I, iv_g pb ps Ψ Q I ≤ iv_g pb ps Ψ Q Is) ∧ φ ≤ iv_g pb ps Ψ Q Is := by
  have h0 : iv_g pb ps Ψ Q 0 = 0 := by simp [iv_g, hΨ0]
  have hm0 := hmax 0
  simp only [iv_gφ, hIs, ↓reduceIte, h0] at hm0
  refine ⟨fun I => ?_, by linarith⟩
  rcases eq_or_ne I 0 with h | h
  · subst h; rw [h0]; linarith
  · have := hmax I
    simp only [iv_gφ, h, hIs, ↓reduceIte] at this
    linarith

/-- **(8.43)** (Miao, p. 286): fixed cost `φ > 0`, `Ψ` convex, `Ψ(0) = 0`, `p_s ≤ p_b`. Let
`Q₂` be the upper zero of `ψ(·) − φ`: the buy-FOC solution `I₂ > 0` at `Q₂`
(`p_b + Ψ₁(I₂) = Q₂`) has `g_{Q₂}(I₂) = φ`. If `Q > Q₂` and `I* > 0` solves `p_b + Ψ₁(I*) = Q`,
then `I*` is optimal and strictly better than inaction. -/
theorem eq_8_43 {pb ps φ Q Q2 Is I2 Ψ1s : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb)
    (hΨ0 : Ψ 0 = 0) (hconv : ConvexOn ℝ Set.univ Ψ) (hds : HasDerivAt Ψ Ψ1s Is)
    (hIs : 0 < Is) (hfoc : pb + Ψ1s = Q) (hI2 : 0 < I2) (hQ2 : iv_g pb ps Ψ Q2 I2 = φ)
    (hQ : Q2 < Q) :
    (∀ I, iv_gφ pb ps φ Ψ Q I ≤ iv_gφ pb ps φ Ψ Q Is) ∧
      iv_gφ pb ps φ Ψ Q 0 < iv_gφ pb ps φ Ψ Q Is := by
  have hopt := eq_8_38 hp hΨ0 hconv hds hIs hfoc
  have h0 : iv_gφ pb ps φ Ψ Q 0 = 0 := by simp [iv_gφ, iv_g, hΨ0]
  have hval : φ < iv_g pb ps Ψ Q Is := by
    have h1 := hopt I2
    rw [(iv_g_le_buy hp hΨ0 I2).2 hI2.le] at h1
    rw [(iv_g_le_buy hp hΨ0 I2).2 hI2.le] at hQ2
    nlinarith
  have hs : iv_gφ pb ps φ Ψ Q Is = iv_g pb ps Ψ Q Is - φ := by
    simp [iv_gφ, hIs.ne']
  refine ⟨fun I => ?_, by rw [h0, hs]; linarith⟩
  rw [hs]
  rcases eq_or_ne I 0 with h | h
  · subst h; rw [h0]; linarith
  · simp only [iv_gφ, h, ↓reduceIte]
    linarith [hopt I]

/-- **(8.44)** (Miao, p. 286): with `Q₁` (sell-FOC solution `I₁ < 0`, `g_{Q₁}(I₁) = φ`) and
`Q₂` (buy-FOC solution `I₂ > 0`, `g_{Q₂}(I₂) = φ`), inaction is optimal for
`Q₁ ≤ Q ≤ Q₂`. -/
theorem eq_8_44 {pb ps φ Q Q1 Q2 I1 I2 Ψ11 Ψ12 : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb)
    (hΨ0 : Ψ 0 = 0) (hconv : ConvexOn ℝ Set.univ Ψ) (hd1 : HasDerivAt Ψ Ψ11 I1)
    (hd2 : HasDerivAt Ψ Ψ12 I2) (hI1 : I1 < 0) (hI2 : 0 < I2) (hfoc1 : ps + Ψ11 = Q1)
    (hfoc2 : pb + Ψ12 = Q2) (hQ1 : iv_g pb ps Ψ Q1 I1 = φ) (hQ2 : iv_g pb ps Ψ Q2 I2 = φ)
    (h1 : Q1 ≤ Q) (h2 : Q ≤ Q2) (I : ℝ) :
    iv_gφ pb ps φ Ψ Q I ≤ iv_gφ pb ps φ Ψ Q 0 := by
  have h0 : iv_gφ pb ps φ Ψ Q 0 = 0 := by simp [iv_gφ, iv_g, hΨ0]
  rw [h0]
  rcases lt_trichotomy I 0 with h | h | h
  · have hb := eq_8_40 hp hΨ0 hconv hd1 hI1 hfoc1 I
    rw [(iv_g_le_sell hp hΨ0 I).2 h.le] at hb
    rw [hQ1] at hb
    simp only [iv_gφ, h.ne, ↓reduceIte]
    rw [(iv_g_le_sell hp hΨ0 I).2 h.le]
    nlinarith
  · subst h; rw [h0]
  · have hb := eq_8_38 hp hΨ0 hconv hd2 hI2 hfoc2 I
    rw [(iv_g_le_buy hp hΨ0 I).2 h.le] at hb
    rw [hQ2] at hb
    simp only [iv_gφ, h.ne', ↓reduceIte]
    rw [(iv_g_le_buy hp hΨ0 I).2 h.le]
    nlinarith

/-- **(8.45)** (Miao, p. 286): if `Q < Q₁` and `I* < 0` solves `p_s + Ψ₁(I*) = Q`, then `I*` is
optimal and strictly better than inaction. -/
theorem eq_8_45 {pb ps φ Q Q1 Is I1 Ψ1s : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb)
    (hΨ0 : Ψ 0 = 0) (hconv : ConvexOn ℝ Set.univ Ψ) (hds : HasDerivAt Ψ Ψ1s Is)
    (hIs : Is < 0) (hfoc : ps + Ψ1s = Q) (hI1 : I1 < 0) (hQ1 : iv_g pb ps Ψ Q1 I1 = φ)
    (hQ : Q < Q1) :
    (∀ I, iv_gφ pb ps φ Ψ Q I ≤ iv_gφ pb ps φ Ψ Q Is) ∧
      iv_gφ pb ps φ Ψ Q 0 < iv_gφ pb ps φ Ψ Q Is := by
  have hopt := eq_8_40 hp hΨ0 hconv hds hIs hfoc
  have h0 : iv_gφ pb ps φ Ψ Q 0 = 0 := by simp [iv_gφ, iv_g, hΨ0]
  have hval : φ < iv_g pb ps Ψ Q Is := by
    have h1 := hopt I1
    rw [(iv_g_le_sell hp hΨ0 I1).2 hI1.le] at h1
    rw [(iv_g_le_sell hp hΨ0 I1).2 hI1.le] at hQ1
    nlinarith
  have hs : iv_gφ pb ps φ Ψ Q Is = iv_g pb ps Ψ Q Is - φ := by
    simp [iv_gφ, hIs.ne]
  refine ⟨fun I => ?_, by rw [h0, hs]; linarith⟩
  rw [hs]
  rcases eq_or_ne I 0 with h | h
  · subst h; rw [h0]; linarith
  · simp only [iv_gφ, h, ↓reduceIte]
    linarith [hopt I]

/-- Miao, p. 287: "the presence of fixed costs widens the inaction region". If `φ > 0`,
`Ψ ≥ 0`, and `Q₂` (with `I₂ > 0`, `g_{Q₂}(I₂) = φ`), `Q₁` (with `I₁ < 0`, `g_{Q₁}(I₁) = φ`) are
as in `eq_8_44`, then `Q₁ < p_s` and `p_b < Q₂`. -/
theorem iv_fixed_widens {pb ps φ Q1 Q2 I1 I2 : ℝ} {Ψ : ℝ → ℝ} (hp : ps ≤ pb) (hΨ0 : Ψ 0 = 0)
    (hnn : ∀ I, 0 ≤ Ψ I) (hφ : 0 < φ) (hI1 : I1 < 0) (hI2 : 0 < I2)
    (hQ1 : iv_g pb ps Ψ Q1 I1 = φ) (hQ2 : iv_g pb ps Ψ Q2 I2 = φ) : Q1 < ps ∧ pb < Q2 := by
  rw [(iv_g_le_sell hp hΨ0 I1).2 hI1.le] at hQ1
  rw [(iv_g_le_buy hp hΨ0 I2).2 hI2.le] at hQ2
  have := hnn I1
  have := hnn I2
  constructor
  · by_contra hc
    nlinarith [not_lt.1 hc]
  · by_contra hc
    nlinarith [not_lt.1 hc]

end Miao.Applications
