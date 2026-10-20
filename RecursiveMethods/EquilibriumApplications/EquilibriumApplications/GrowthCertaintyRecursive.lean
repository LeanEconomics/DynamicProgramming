/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyOptimum

/-!
# The one-sector model under certainty: the firm's and household's functional equations

SLP §16.1, pp. 478–481, Exercise 16.1(e). The state is the economy-wide capital `k ∈ K = [a, k_max]`
(`0 < a`), moving by `k′ = g(k)`; the price of a claim to one unit of next period's good is `q(k)`.

* The firm's equation (1): `ψ(k, z) = max_{0 ≤ z′ ≤ f(z)} {f(z) − z′ + q(k) ψ[g(k), z′]}` on
  `K × [0, k_max]` (`GcFirmBellman`), for data `GcFirmData`: `f`, `g`, `q` continuous, `q > 0` and
  the **uniform product bound** `Π_{s<n} q(gˢ(k)) ≤ M βⁿ` for all `k ∈ K`.
* `gcFirmT`, `gcFirmTB`: the operator of (1) on bounded continuous functions, written as a maximum
  over `z′ = s f(z)`, `s ∈ [0, 1]`; `gcFirmT_ge`, `gcFirmT_attained`: it is the maximum in (1).
* `gc_firmBellman_unique`: (1) has at most one **bounded** solution (continuity not needed):
  `|ψ − φ|(k, z) ≤ Π_{s<n} q(gˢ(k)) · sup |ψ − φ| ≤ M βⁿ sup |ψ − φ|`.
* `gc_firmTB_iterate_dist`, `gc_firmTB_contracting`: `Tⁿ` is a contraction of modulus `M βⁿ`.
* **Exercise 16.1(e), firm** (`ex_16_1e_firm`): there is exactly one bounded continuous `ψ`
  satisfying (1); if `f` is strictly concave, `ψ(k, ·)` is strictly concave, the policy `h` is
  single-valued (`gc_firm_policy_unique`) and continuous (`gc_firm_policy_continuous`).
* `gc_argmax_continuous`: the unique maximiser of a jointly continuous function over a
  continuously varying interval `[0, b(p)]` is continuous in `p` (used for `h` and `ω`).
* `ex_16_1e_not_contraction`: if `q(k₀) > 1` for some `k₀`, the operator `T` of (1) is **not** a
  contraction: `T(ψ + c) = Tψ + q(k) c`.

**Corrections.**
* (1) is not a contraction in general (`ex_16_1e_not_contraction`): `q(k) = 1/f′(g(k)) > 1` happens
  above the steady state (`GrowthCertaintyRecursiveEq.gc_logCD_q_gt_one`). The solutions manual's
  `T^M` argument uses a modulus `Q(k) = q(k)⋯q(g^M(k))` and an `M` that depend on `k`; the sup norm
  needs `sup_k Q(k) < 1` with one `M`. The uniform bound `Π_{s<n} q(gˢ(k)) ≤ M βⁿ` is what makes
  (1) well posed; for the equilibrium `q` it is proved in `GrowthCertaintyRecursiveEq`
  (`gc_planner_firmData`). The manual's product also has one factor too many (harmless).
* Uniqueness holds among all bounded solutions, not only continuous ones.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped BoundedContinuousFunction

/-! ### Continuity of a unique maximiser -/

/-- **Continuity of a unique maximiser.** If `G` is jointly continuous, `b ≥ 0` is continuous, and
for every `p` the point `h(p) ∈ [0, b(p)]` is the unique maximiser of `G(p, ·)` on `[0, b(p)]`, then
`h` is continuous (sequential argument: bounded subsequences, limits of maximisers maximise). -/
theorem gc_argmax_continuous {P : Type*} [TopologicalSpace P] [SequentialSpace P]
    {b : P → ℝ} (hb : Continuous b) (hb0 : ∀ p, 0 ≤ b p) {G : P → ℝ → ℝ}
    (hG : Continuous fun q : P × ℝ => G q.1 q.2) {h : P → ℝ} (hmem : ∀ p, h p ∈ Icc 0 (b p))
    (hmax : ∀ p, ∀ y ∈ Icc 0 (b p), G p y ≤ G p (h p))
    (huniq : ∀ p, ∀ y ∈ Icc 0 (b p), G p (h p) ≤ G p y → y = h p) : Continuous h := by
  refine continuous_iff_seqContinuous.2 fun x p hx => ?_
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hbx : Tendsto (fun n => b (x (ns n))) atTop (𝓝 (b p)) :=
    (hb.tendsto p).comp (hx.comp hns)
  obtain ⟨R, hR⟩ : ∃ R, ∀ n, b (x (ns n)) ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto _ hbx).bddAbove
    exact ⟨R, fun n => hR (mem_range_self n)⟩
  obtain ⟨c, -, φ, hφ, hc⟩ := tendsto_subseq_of_bounded (x := fun n => h (x (ns n)))
    (Metric.isBounded_Icc 0 R) fun n => ⟨(hmem _).1, (hmem _).2.trans (hR n)⟩
  have hxφ : Tendsto (fun n => x (ns (φ n))) atTop (𝓝 p) :=
    (hx.comp hns).comp hφ.tendsto_atTop
  have hbφ : Tendsto (fun n => b (x (ns (φ n)))) atTop (𝓝 (b p)) := hbx.comp hφ.tendsto_atTop
  have hcmem : c ∈ Icc 0 (b p) :=
    ⟨ge_of_tendsto' hc fun n => (hmem _).1, le_of_tendsto_of_tendsto' hc hbφ fun n => (hmem _).2⟩
  have hcmax : ∀ y ∈ Icc 0 (b p), G p y ≤ G p c := fun y hy => by
    have hw : Tendsto (fun n => min y (b (x (ns (φ n))))) atTop (𝓝 y) := by
      simpa [min_eq_left hy.2] using (tendsto_const_nhds (x := y)).min hbφ
    have h1 : Tendsto (fun n => G (x (ns (φ n))) (min y (b (x (ns (φ n)))))) atTop
        (𝓝 (G p y)) := (hG.tendsto (p, y)).comp (hxφ.prodMk_nhds hw)
    have h2 : Tendsto (fun n => G (x (ns (φ n))) (h (x (ns (φ n))))) atTop (𝓝 (G p c)) :=
      (hG.tendsto (p, c)).comp (hxφ.prodMk_nhds hc)
    exact le_of_tendsto_of_tendsto' h1 h2 fun n =>
      hmax _ _ ⟨le_min hy.1 (hb0 _), min_le_right _ _⟩
  have := huniq p c hcmem (hcmax _ (hmem p))
  exact ⟨φ, this ▸ hc⟩

/-! ### The firm's functional equation (1) -/

variable {a kmax : ℝ}

/-- The firm's choice `z′ = s f(z)` for `s ∈ [0, 1]`, as a point of `[0, k_max]` (clamped, so that
it is defined and continuous for all `s`). -/
noncomputable def gcZc (f : ℝ → ℝ) (z : Icc (0 : ℝ) kmax) (s : ℝ) : Icc (0 : ℝ) kmax :=
  projIcc 0 kmax (z.2.1.trans z.2.2) (s * f z)

/-- The objective of (1) at `(k, z)` with `z′ = s f(z)`. -/
noncomputable def gcFirmObj (f : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ)
    (ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ) (p : Icc a kmax × Icc (0 : ℝ) kmax) (s : ℝ) : ℝ :=
  f p.2 - gcZc f p.2 s + q p.1 * ψ (g p.1, gcZc f p.2 s)

/-- **The operator of (1)**:
`(Tψ)(k, z) = max_{s ∈ [0,1]} {f(z) − s f(z) + q(k) ψ(g(k), s f(z))}`. -/
noncomputable def gcFirmT (f : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ)
    (ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ) (p : Icc a kmax × Icc (0 : ℝ) kmax) : ℝ :=
  sSup (gcFirmObj f g q ψ p '' Icc 0 1)

variable (f : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) in
/-- The data of (1) (p. 479, Ex 16.1e): `f` maps `[0, k_max]` into itself continuously, the law of
motion `g : K → K` and the price `q : K → (0, ∞)` are continuous, and the discount factors along
the equilibrium path satisfy the uniform bound `Π_{s<n} q(gˢ(k)) ≤ M βⁿ`. -/
structure GcFirmData (β M : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  kmax_nonneg : 0 ≤ kmax
  f_cont : ContinuousOn f (Icc 0 kmax)
  f_nonneg : ∀ z ∈ Icc (0 : ℝ) kmax, 0 ≤ f z
  f_le : ∀ z ∈ Icc (0 : ℝ) kmax, f z ≤ kmax
  g_cont : Continuous g
  q_cont : Continuous q
  q_pos : ∀ k, 0 < q k
  prod_le : ∀ k n, ∏ s ∈ Finset.range n, q (g^[s] k) ≤ M * β ^ n

/-- The discount factor `Qₙ(k) = Π_{s<n} q(gˢ(k))` from the state `k` to `n` periods ahead. -/
noncomputable def gcDisc (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) (n : ℕ)
    (k : Icc a kmax) : ℝ :=
  ∏ s ∈ Finset.range n, q (g^[s] k)

/-- `Q₀ = 1`. -/
theorem gcDisc_zero (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) (k : Icc a kmax) :
    gcDisc g q 0 k = 1 := by simp [gcDisc]

/-- `Q_{n+1}(k) = q(k) Qₙ(g(k))`. -/
theorem gcDisc_succ (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) (n : ℕ)
    (k : Icc a kmax) : gcDisc g q (n + 1) k = q k * gcDisc g q n (g k) := by
  simp only [gcDisc, Finset.prod_range_succ', Function.iterate_succ_apply,
    Function.iterate_zero_apply]
  ring

/-- `Q_{n+1}(k) = Qₙ(k) q(gⁿ(k))`. -/
theorem gcDisc_succ' (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) (n : ℕ)
    (k : Icc a kmax) : gcDisc g q (n + 1) k = gcDisc g q n k * q (g^[n] k) := by
  simp only [gcDisc, Finset.prod_range_succ]

/-- `Qₙ > 0`. -/
theorem gcDisc_pos {f : ℝ → ℝ} {g : Icc a kmax → Icc a kmax} {q : Icc a kmax → ℝ} {β M : ℝ}
    (D : GcFirmData f g q β M) (n : ℕ) (k : Icc a kmax) : 0 < gcDisc g q n k :=
  Finset.prod_pos fun _ _ => D.q_pos _

variable {f : ℝ → ℝ} {g : Icc a kmax → Icc a kmax} {q : Icc a kmax → ℝ} {β M : ℝ}

/-- `M > 0`. -/
theorem GcFirmData.M_pos (D : GcFirmData f g q β M) [Nonempty (Icc a kmax)] : 0 < M := by
  have k : Icc a kmax := Classical.arbitrary _
  have := D.prod_le k 0
  simp only [Finset.range_zero, Finset.prod_empty, pow_zero, mul_one] at this
  linarith

/-- `0 ≤ f(z) ≤ k_max` on `[0, k_max]`. -/
theorem GcFirmData.f_mem (D : GcFirmData f g q β M) (z : Icc (0 : ℝ) kmax) :
    0 ≤ f z ∧ f z ≤ kmax := ⟨D.f_nonneg _ z.2, D.f_le _ z.2⟩

/-- The value of `z′ = s f(z)` for `s ∈ [0, 1]`. -/
theorem gcZc_val (D : GcFirmData f g q β M) (z : Icc (0 : ℝ) kmax) {s : ℝ} (hs : s ∈ Icc 0 1) :
    (gcZc f z s : ℝ) = s * f z := by
  have h0 := (D.f_mem z).1
  have hmem : s * f z ∈ Icc 0 kmax :=
    ⟨mul_nonneg hs.1 h0, (mul_le_of_le_one_left h0 hs.2).trans (D.f_mem z).2⟩
  simp only [gcZc, projIcc_of_mem _ hmem]

/-- `z ↦ f(z)` is continuous on `[0, k_max]`. -/
theorem GcFirmData.continuous_f (D : GcFirmData f g q β M) :
    Continuous fun z : Icc (0 : ℝ) kmax => f z :=
  D.f_cont.comp_continuous continuous_subtype_val fun z => z.2

/-- `(z, s) ↦ s f(z)` (clamped) is continuous. -/
theorem gcZc_continuous (D : GcFirmData f g q β M) :
    Continuous fun r : Icc (0 : ℝ) kmax × ℝ => gcZc f r.1 r.2 := by
  have : (fun r : Icc (0 : ℝ) kmax × ℝ => gcZc f r.1 r.2) =
      fun r => projIcc 0 kmax D.kmax_nonneg (r.2 * f r.1) := rfl
  rw [this]
  exact continuous_projIcc.comp (continuous_snd.mul (D.continuous_f.comp continuous_fst))

/-- The objective of (1) is jointly continuous in `((k, z), s)` for continuous `ψ`. -/
theorem gcFirmObj_continuous (D : GcFirmData f g q β M)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ} (hψ : Continuous ψ) :
    Continuous fun r : (Icc a kmax × Icc (0 : ℝ) kmax) × ℝ => gcFirmObj f g q ψ r.1 r.2 := by
  have hz : Continuous fun r : (Icc a kmax × Icc (0 : ℝ) kmax) × ℝ => gcZc f r.1.2 r.2 :=
    (gcZc_continuous D).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  unfold gcFirmObj
  exact ((D.continuous_f.comp (continuous_snd.comp continuous_fst)).sub
    (continuous_subtype_val.comp hz)).add ((D.q_cont.comp (continuous_fst.comp continuous_fst)).mul
    (hψ.comp ((D.g_cont.comp (continuous_fst.comp continuous_fst)).prodMk hz)))

/-- The objective of (1) at a fixed state is bounded above on `s ∈ [0, 1]`. -/
theorem gcFirmObj_bddAbove (D : GcFirmData f g q β M) {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψ : Continuous ψ) (p : Icc a kmax × Icc (0 : ℝ) kmax) :
    BddAbove (gcFirmObj f g q ψ p '' Icc 0 1) :=
  (isCompact_Icc.image ((gcFirmObj_continuous D hψ).comp
    (continuous_const.prodMk continuous_id))).bddAbove

/-- `Tψ` dominates every feasible choice in (1): for `0 ≤ z′ ≤ f(z)`,
`f(z) − z′ + q(k) ψ(g(k), z′) ≤ (Tψ)(k, z)`. -/
theorem gcFirmT_ge (D : GcFirmData f g q β M) {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψ : Continuous ψ) (p : Icc a kmax × Icc (0 : ℝ) kmax) (z' : Icc (0 : ℝ) kmax)
    (hz' : (z' : ℝ) ≤ f p.2) : f p.2 - z' + q p.1 * ψ (g p.1, z') ≤ gcFirmT f g q ψ p := by
  have h0 := (D.f_mem p.2).1
  set s := (z' : ℝ) / f p.2 with hs
  have hsm : s ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg z'.2.1 h0, div_le_one_of_le₀ hz' h0⟩
  have hzc : gcZc f p.2 s = z' := by
    apply Subtype.ext
    rw [gcZc_val D p.2 hsm]
    rcases h0.lt_or_eq with hlt | heq
    · rw [hs, div_mul_cancel₀ _ hlt.ne']
    · rw [← heq, mul_zero]
      exact le_antisymm z'.2.1 (hz'.trans heq.symm.le)
  have := le_csSup (gcFirmObj_bddAbove D hψ p) (mem_image_of_mem _ hsm)
  rwa [gcFirmObj, hzc] at this

/-- The maximum in (1) is attained: `(Tψ)(k, z) = f(z) − z′ + q(k) ψ(g(k), z′)` for some
`0 ≤ z′ ≤ f(z)`. -/
theorem gcFirmT_attained (D : GcFirmData f g q β M) {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψ : Continuous ψ) (p : Icc a kmax × Icc (0 : ℝ) kmax) :
    ∃ z' : Icc (0 : ℝ) kmax, (z' : ℝ) ≤ f p.2 ∧
      gcFirmT f g q ψ p = f p.2 - z' + q p.1 * ψ (g p.1, z') := by
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_sSup_image_eq (nonempty_Icc.2 zero_le_one)
    ((gcFirmObj_continuous D hψ).comp (continuous_const.prodMk continuous_id)).continuousOn
  refine ⟨gcZc f p.2 s, ?_, hmax⟩
  rw [gcZc_val D p.2 hs]
  exact mul_le_of_le_one_left (D.f_mem p.2).1 hs.2

/-- `Tψ` is continuous for continuous `ψ` (maximum over a fixed compact set). -/
theorem gcFirmT_continuous (D : GcFirmData f g q β M) {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψ : Continuous ψ) : Continuous (gcFirmT f g q ψ) :=
  isCompact_Icc.continuous_sSup (gcFirmObj_continuous D hψ)

/-- The operator of (1) on bounded continuous functions on the compact space `K × [0, k_max]`. -/
noncomputable def gcFirmTB (D : GcFirmData f g q β M)
    (ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ) : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨gcFirmT f g q ψ, gcFirmT_continuous D ψ.continuous⟩

/-- Values of `gcFirmTB`. -/
theorem gcFirmTB_apply (D : GcFirmData f g q β M) (ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ)
    (p : Icc a kmax × Icc (0 : ℝ) kmax) : gcFirmTB D ψ p = gcFirmT f g q ψ p := rfl

/-- `ψ` **satisfies (1)** (with "max"): every feasible `z′` gives at most `ψ(k, z)`, and some
feasible `z′` attains it. -/
def GcFirmBellman (f : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ)
    (ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ) : Prop :=
  ∀ p : Icc a kmax × Icc (0 : ℝ) kmax,
    (∀ z' : Icc (0 : ℝ) kmax, (z' : ℝ) ≤ f p.2 → f p.2 - z' + q p.1 * ψ (g p.1, z') ≤ ψ p) ∧
    ∃ z' : Icc (0 : ℝ) kmax, (z' : ℝ) ≤ f p.2 ∧ ψ p = f p.2 - z' + q p.1 * ψ (g p.1, z')

/-- **At most one bounded solution of (1)** (no continuity needed): by induction,
`|ψ − φ|(k, z) ≤ Qₙ(k) C ≤ M βⁿ C` for every `n`. -/
theorem gc_firmBellman_unique (D : GcFirmData f g q β M)
    {ψ φ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ} (hψ : GcFirmBellman f g q ψ)
    (hφ : GcFirmBellman f g q φ) {C : ℝ} (hC : ∀ p, |ψ p - φ p| ≤ C) : ψ = φ := by
  have key : ∀ n p, |ψ p - φ p| ≤ gcDisc g q n p.1 * C := by
    intro n
    induction n with
    | zero => intro p; rw [gcDisc_zero, one_mul]; exact hC p
    | succ n ih =>
      intro p
      obtain ⟨z₁, hz₁, hψp⟩ := (hψ p).2
      obtain ⟨z₂, hz₂, hφp⟩ := (hφ p).2
      have a1 := (hφ p).1 z₁ hz₁
      have a2 := (hψ p).1 z₂ hz₂
      have b1 := (abs_le.1 (ih (g p.1, z₁))).2
      have b2 := (abs_le.1 (ih (g p.1, z₂))).1
      have hq := D.q_pos p.1
      rw [gcDisc_succ]
      refine abs_le.2 ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left b2 hq.le]
      · nlinarith [mul_le_mul_of_nonneg_left b1 hq.le]
  funext p
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p)
  have hlim : Tendsto (fun n : ℕ => M * β ^ n * C) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one D.beta_pos.le D.beta_lt_one).const_mul
      M).mul_const C
  have : |ψ p - φ p| ≤ 0 := ge_of_tendsto' hlim fun n =>
    (key n p).trans (mul_le_mul_of_nonneg_right (D.prod_le p.1 n) hC0)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- One step of `T`: if `|a − b| ≤ C` at every `(g(k), z′)`, then `|Ta − Tb|(k, z) ≤ q(k) C`. -/
theorem gcFirmT_sub_le (D : GcFirmData f g q β M) {ψ φ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψ : Continuous ψ) (hφ : Continuous φ) (p : Icc a kmax × Icc (0 : ℝ) kmax) {C : ℝ}
    (hC : ∀ z', |ψ (g p.1, z') - φ (g p.1, z')| ≤ C) :
    |gcFirmT f g q ψ p - gcFirmT f g q φ p| ≤ q p.1 * C := by
  obtain ⟨z₁, hz₁, h1⟩ := gcFirmT_attained D hψ p
  obtain ⟨z₂, hz₂, h2⟩ := gcFirmT_attained D hφ p
  have a1 := gcFirmT_ge D hφ p z₁ hz₁
  have a2 := gcFirmT_ge D hψ p z₂ hz₂
  have b1 := (abs_le.1 (hC z₁)).2
  have b2 := (abs_le.1 (hC z₂)).1
  have hq := D.q_pos p.1
  refine abs_le.2 ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left b2 hq.le]
  · nlinarith [mul_le_mul_of_nonneg_left b1 hq.le]

/-- `|Tⁿψ − Tⁿφ|(k, z) ≤ Qₙ(k) ‖ψ − φ‖`. -/
theorem gc_firmTB_iterate_dist (D : GcFirmData f g q β M)
    (ψ φ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ) (n : ℕ) (p : Icc a kmax × Icc (0 : ℝ) kmax) :
    |(gcFirmTB D)^[n] ψ p - (gcFirmTB D)^[n] φ p| ≤ gcDisc g q n p.1 * dist ψ φ := by
  induction n generalizing p with
  | zero =>
    rw [gcDisc_zero, one_mul, Function.iterate_zero_apply, Function.iterate_zero_apply,
      ← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist p
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', gcFirmTB_apply,
      gcFirmTB_apply, gcDisc_succ, mul_assoc]
    exact gcFirmT_sub_le D (BoundedContinuousFunction.continuous _)
      (BoundedContinuousFunction.continuous _) p fun z' => ih (g p.1, z')

/-- Some iterate `T^N` is a contraction on the bounded continuous functions (modulus
`M β^N < 1`). -/
theorem gc_firmTB_contracting (D : GcFirmData f g q β M) [Nonempty (Icc a kmax)] :
    ∃ N : ℕ, ∃ K : NNReal, ContractingWith K (gcFirmTB D)^[N] := by
  have hM := D.M_pos
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hM) D.beta_lt_one
  have hMN : M * β ^ N < 1 := by
    calc M * β ^ N < M * M⁻¹ := mul_lt_mul_of_pos_left hN hM
      _ = 1 := mul_inv_cancel₀ hM.ne'
  have hnn : 0 ≤ M * β ^ N := mul_nonneg hM.le (pow_nonneg D.beta_pos.le N)
  refine ⟨N, ⟨M * β ^ N, hnn⟩, ?_, LipschitzWith.of_dist_le_mul fun ψ φ => ?_⟩
  · change M * β ^ N < 1
    exact hMN
  · refine (BoundedContinuousFunction.dist_le (mul_nonneg hnn dist_nonneg)).2 fun p => ?_
    rw [Real.dist_eq]
    exact (gc_firmTB_iterate_dist D ψ φ N p).trans
      (mul_le_mul_of_nonneg_right (D.prod_le p.1 N) dist_nonneg)

/-- A fixed point of `T` satisfies (1). -/
theorem gc_firmBellman_of_fixed (D : GcFirmData f g q β M)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : gcFirmTB D ψ = ψ) :
    GcFirmBellman f g q ψ := fun p => by
  have hp : ψ p = gcFirmT f g q ψ p := by rw [← gcFirmTB_apply D ψ p, hψ]
  refine ⟨fun z' hz' => hp ▸ gcFirmT_ge D ψ.continuous p z' hz', ?_⟩
  obtain ⟨z', hz', h⟩ := gcFirmT_attained D ψ.continuous p
  exact ⟨z', hz', hp.trans h⟩

/-- **Exercise 16.1(e), existence and uniqueness for the firm**: there is a bounded continuous `ψ`
satisfying (1), and every bounded solution of (1) equals it. -/
theorem ex_16_1e_firm_exists (D : GcFirmData f g q β M) [Nonempty (Icc a kmax)] :
    ∃ ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ, gcFirmTB D ψ = ψ ∧ GcFirmBellman f g q ψ ∧
      ∀ φ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ, (∃ C, ∀ p, |φ p| ≤ C) →
        GcFirmBellman f g q φ → φ = ψ := by
  obtain ⟨N, K, hK⟩ := gc_firmTB_contracting D
  set ψ := ContractingWith.fixedPoint _ hK
  have hfix : gcFirmTB D ψ = ψ := hK.isFixedPt_fixedPoint_iterate
  refine ⟨ψ, hfix, gc_firmBellman_of_fixed D hfix, fun φ ⟨C, hC⟩ hφ => ?_⟩
  refine gc_firmBellman_unique D hφ (gc_firmBellman_of_fixed D hfix) (C := C + ‖ψ‖) fun p => ?_
  have h1 := hC p
  have h2 : |ψ p| ≤ ‖ψ‖ := by
    rw [← Real.norm_eq_abs]
    exact ψ.norm_coe_le_norm p
  calc |φ p - ψ p| ≤ |φ p| + |ψ p| := abs_sub _ _
    _ ≤ C + ‖ψ‖ := add_le_add h1 h2

/-! ### Concavity of `ψ(k, ·)` and the firm's policy -/

/-- `ψ(k, ·)` is concave on `[0, k_max]`. -/
def GcConcaveZ (ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ) : Prop :=
  ∀ (k : Icc a kmax) (z₁ z₂ z : Icc (0 : ℝ) kmax) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    (z : ℝ) = θ * z₁ + (1 - θ) * z₂ → θ * ψ (k, z₁) + (1 - θ) * ψ (k, z₂) ≤ ψ (k, z)

/-- The convex combination `θ z₁ + (1 − θ) z₂` as a point of `[0, k_max]`. -/
def gcZcombo (z₁ z₂ : Icc (0 : ℝ) kmax) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Icc (0 : ℝ) kmax :=
  ⟨θ * z₁ + (1 - θ) * z₂, (convex_Icc (0 : ℝ) kmax) z₁.2 z₂.2 h0 (by linarith) (by ring)⟩

/-- `T` preserves concavity in `z` when `f` is concave. -/
theorem gcFirmT_concave (D : GcFirmData f g q β M) (hf : ConcaveOn ℝ (Icc 0 kmax) f)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ} (hψ : Continuous ψ) (hcv : GcConcaveZ ψ) :
    GcConcaveZ (gcFirmT f g q ψ) := by
  intro k z₁ z₂ z θ h0 h1 hz
  obtain ⟨w₁, hw₁, e₁⟩ := gcFirmT_attained D hψ (k, z₁)
  obtain ⟨w₂, hw₂, e₂⟩ := gcFirmT_attained D hψ (k, z₂)
  set w := gcZcombo w₁ w₂ h0 h1
  have hfz : θ * f z₁ + (1 - θ) * f z₂ ≤ f z := by
    have := hf.2 z₁.2 z₂.2 h0 (by linarith : 0 ≤ 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    rwa [hz]
  have hw : (w : ℝ) ≤ f z := by
    change θ * (w₁ : ℝ) + (1 - θ) * w₂ ≤ f z
    nlinarith
  have hge := gcFirmT_ge D hψ (k, z) w hw
  have hcw := hcv (g k) w₁ w₂ w θ h0 h1 rfl
  have hq := D.q_pos k
  rw [e₁, e₂]
  change θ * (f z₁ - w₁ + q k * ψ (g k, w₁)) + (1 - θ) * (f z₂ - w₂ + q k * ψ (g k, w₂)) ≤ _
  change f z - (θ * (w₁ : ℝ) + (1 - θ) * w₂) + q k * ψ (g k, w) ≤ gcFirmT f g q ψ (k, z) at hge
  nlinarith [mul_le_mul_of_nonneg_left hcw hq.le]

/-- The fixed point of `T` is concave in `z` when `f` is concave: it is the limit of the iterates
`T^{Nn}(0)`, all concave in `z`. -/
theorem gc_firm_fixed_concave (D : GcFirmData f g q β M) (hf : ConcaveOn ℝ (Icc 0 kmax) f)
    [Nonempty (Icc a kmax)] {N : ℕ} {K : NNReal} (hK : ContractingWith K (gcFirmTB D)^[N]) :
    GcConcaveZ ⇑(ContractingWith.fixedPoint (α := Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ)
      ((gcFirmTB D)^[N]) hK) := by
  have hit : ∀ m, GcConcaveZ ((gcFirmTB D)^[m] 0) := by
    intro m
    induction m with
    | zero =>
      intro k z₁ z₂ z θ _ _ _
      simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact gcFirmT_concave D hf (BoundedContinuousFunction.continuous _) ih
  have hlim := hK.tendsto_iterate_fixedPoint 0
  intro k z₁ z₂ z θ h0 h1 hz
  have ev : ∀ p, Tendsto (fun n => ((gcFirmTB D)^[N])^[n] 0 p) atTop
      (𝓝 (ContractingWith.fixedPoint ((gcFirmTB D)^[N]) hK p)) := fun p =>
    ((continuous_eval_const p).tendsto _).comp hlim
  refine le_of_tendsto_of_tendsto' (((ev (k, z₁)).const_mul θ).add ((ev (k, z₂)).const_mul
    (1 - θ))) (ev (k, z)) fun n => ?_
  rw [← Function.iterate_mul]
  exact hit _ k z₁ z₂ z θ h0 h1 hz

/-- With `f` strictly concave, the solution of (1) is **strictly** concave in `z`. -/
theorem gc_firm_strictConcave (D : GcFirmData f g q β M)
    (hf : StrictConcaveOn ℝ (Icc 0 kmax) f) {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψ : GcFirmBellman f g q ψ) (hcv : GcConcaveZ ψ) (k : Icc a kmax)
    (z₁ z₂ z : Icc (0 : ℝ) kmax) (hne : z₁ ≠ z₂) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (hz : (z : ℝ) = θ * z₁ + (1 - θ) * z₂) :
    θ * ψ (k, z₁) + (1 - θ) * ψ (k, z₂) < ψ (k, z) := by
  obtain ⟨w₁, hw₁, e₁⟩ := (hψ (k, z₁)).2
  obtain ⟨w₂, hw₂, e₂⟩ := (hψ (k, z₂)).2
  set w := gcZcombo w₁ w₂ h0.le h1.le
  have hfz : θ * f z₁ + (1 - θ) * f z₂ < f z := by
    have := hf.2 z₁.2 z₂.2 (fun h => hne (Subtype.ext h)) h0 (by linarith : 0 < 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    rwa [hz]
  have hw : (w : ℝ) ≤ f z := by
    change θ * (w₁ : ℝ) + (1 - θ) * w₂ ≤ f z
    nlinarith
  have hge := (hψ (k, z)).1 w hw
  have hcw := hcv (g k) w₁ w₂ w θ h0.le h1.le rfl
  have hq := D.q_pos k
  rw [e₁, e₂]
  change f z - (θ * (w₁ : ℝ) + (1 - θ) * w₂) + q k * ψ (g k, w) ≤ ψ (k, z) at hge
  nlinarith [mul_le_mul_of_nonneg_left hcw hq.le]

/-- **The firm's policy is single-valued**: with `ψ(k′, ·)` strictly concave, the maximiser in (1)
is unique. -/
theorem gc_firm_policy_unique (D : GcFirmData f g q β M) (hf : StrictConcaveOn ℝ (Icc 0 kmax) f)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ} (hψ : GcFirmBellman f g q ψ) (hcv : GcConcaveZ ψ)
    (p : Icc a kmax × Icc (0 : ℝ) kmax) {z₁ z₂ : Icc (0 : ℝ) kmax} (hz₁ : (z₁ : ℝ) ≤ f p.2)
    (hz₂ : (z₂ : ℝ) ≤ f p.2) (e₁ : ψ p = f p.2 - z₁ + q p.1 * ψ (g p.1, z₁))
    (e₂ : ψ p = f p.2 - z₂ + q p.1 * ψ (g p.1, z₂)) : z₁ = z₂ := by
  by_contra hne
  set w := gcZcombo z₁ z₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hw : (w : ℝ) ≤ f p.2 := by
    change 1 / 2 * (z₁ : ℝ) + (1 - 1 / 2) * z₂ ≤ f p.2
    linarith
  have hge := (hψ p).1 w hw
  have hlt := gc_firm_strictConcave D hf hψ hcv (g p.1) z₁ z₂ w hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) rfl
  have hq := D.q_pos p.1
  change f p.2 - (1 / 2 * (z₁ : ℝ) + (1 - 1 / 2) * z₂) + q p.1 * ψ (g p.1, w) ≤ ψ p at hge
  nlinarith [mul_lt_mul_of_pos_left hlt hq]

/-- The firm's policy `h(k, z)`: a maximiser in (1) (unique under strict concavity). -/
noncomputable def gcFirmPolicy {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψ : GcFirmBellman f g q ψ) (p : Icc a kmax × Icc (0 : ℝ) kmax) : Icc (0 : ℝ) kmax :=
  Classical.choose (hψ p).2

/-- The policy is feasible and attains (1). -/
theorem gcFirmPolicy_spec {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ} (hψ : GcFirmBellman f g q ψ)
    (p : Icc a kmax × Icc (0 : ℝ) kmax) :
    (gcFirmPolicy hψ p : ℝ) ≤ f p.2 ∧
      ψ p = f p.2 - gcFirmPolicy hψ p + q p.1 * ψ (g p.1, gcFirmPolicy hψ p) :=
  Classical.choose_spec (hψ p).2

/-- **The firm's policy is continuous** (Ex 16.1e), for `ψ` continuous and strictly concave in
`z`. -/
theorem gc_firm_policy_continuous (D : GcFirmData f g q β M)
    (hf : StrictConcaveOn ℝ (Icc 0 kmax) f) {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ}
    (hψc : Continuous ψ) (hψ : GcFirmBellman f g q ψ) (hcv : GcConcaveZ ψ) :
    Continuous (gcFirmPolicy hψ) := by
  have hk := D.kmax_nonneg
  set G : Icc a kmax × Icc (0 : ℝ) kmax → ℝ → ℝ := fun p y =>
    f p.2 - y + q p.1 * ψ (g p.1, projIcc 0 kmax hk y) with hG
  have hGc : Continuous fun r : (Icc a kmax × Icc (0 : ℝ) kmax) × ℝ => G r.1 r.2 :=
    ((D.continuous_f.comp (continuous_snd.comp continuous_fst)).sub continuous_snd).add
      ((D.q_cont.comp (continuous_fst.comp continuous_fst)).mul
        (hψc.comp ((D.g_cont.comp (continuous_fst.comp continuous_fst)).prodMk
          (continuous_projIcc.comp continuous_snd))))
  have hproj : ∀ p : Icc a kmax × Icc (0 : ℝ) kmax, ∀ (y : ℝ) (hy : y ∈ Icc 0 (f p.2)),
      projIcc 0 kmax hk y =
      ⟨y, hy.1, hy.2.trans (D.f_mem p.2).2⟩ := fun p y hy =>
    projIcc_of_mem _ ⟨hy.1, hy.2.trans (D.f_mem p.2).2⟩
  have hmem : ∀ p, (gcFirmPolicy hψ p : ℝ) ∈ Icc 0 (f p.2) := fun p =>
    ⟨(gcFirmPolicy hψ p).2.1, (gcFirmPolicy_spec hψ p).1⟩
  have hGh : ∀ p, G p (gcFirmPolicy hψ p) = ψ p := fun p => by
    simp only [hG, hproj p _ (hmem p)]
    exact (gcFirmPolicy_spec hψ p).2.symm
  have hcont := gc_argmax_continuous (b := fun p : Icc a kmax × Icc (0 : ℝ) kmax => f p.2)
    (D.continuous_f.comp continuous_snd) (fun p => (D.f_mem p.2).1) hGc
    (h := fun p => (gcFirmPolicy hψ p : ℝ)) hmem
    (fun p y hy => by
      rw [hGh]
      simp only [hG, hproj p y hy]
      exact (hψ p).1 ⟨y, hy.1, hy.2.trans (D.f_mem p.2).2⟩ hy.2)
    (fun p y hy hle => by
      rw [hGh] at hle
      have hle' : ψ p ≤ f p.2 - y + q p.1 * ψ (g p.1, ⟨y, hy.1, hy.2.trans (D.f_mem p.2).2⟩) := by
        simpa only [hG, hproj p y hy] using hle
      have e := le_antisymm ((hψ p).1 ⟨y, hy.1, hy.2.trans (D.f_mem p.2).2⟩ hy.2) hle'
      have := gc_firm_policy_unique D hf hψ hcv p (z₁ := ⟨y, hy.1, hy.2.trans (D.f_mem p.2).2⟩)
        hy.2 (gcFirmPolicy_spec hψ p).1 e.symm (gcFirmPolicy_spec hψ p).2
      exact congrArg Subtype.val this)
  exact Continuous.subtype_mk hcont _

/-- **Exercise 16.1(e), firm**: given the law of motion `g` and prices `q` with the uniform product
bound, there is exactly one bounded continuous `ψ` satisfying (1) (unique even among bounded
functions); if `f` is strictly concave, `ψ(k, ·)` is concave, the policy `h` is single-valued and
continuous. -/
theorem ex_16_1e_firm (D : GcFirmData f g q β M) (hf : StrictConcaveOn ℝ (Icc 0 kmax) f)
    [Nonempty (Icc a kmax)] :
    ∃ ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ, ∃ hψ : GcFirmBellman f g q ψ,
      (∀ φ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ, (∃ C, ∀ p, |φ p| ≤ C) →
        GcFirmBellman f g q φ → φ = ψ) ∧
      GcConcaveZ ψ ∧ Continuous (gcFirmPolicy hψ) ∧
      ∀ p (z' : Icc (0 : ℝ) kmax), (z' : ℝ) ≤ f p.2 →
        ψ p = f p.2 - z' + q p.1 * ψ (g p.1, z') → z' = gcFirmPolicy hψ p := by
  obtain ⟨N, K, hK⟩ := gc_firmTB_contracting D
  set ψ := ContractingWith.fixedPoint _ hK
  have hfix : gcFirmTB D ψ = ψ := hK.isFixedPt_fixedPoint_iterate
  have hψ := gc_firmBellman_of_fixed D hfix
  have hcv := gc_firm_fixed_concave D hf.concaveOn hK
  refine ⟨ψ, hψ, fun φ ⟨C, hC⟩ hφ => ?_, hcv,
    gc_firm_policy_continuous D hf ψ.continuous hψ hcv, fun p z' hz' e => ?_⟩
  · refine gc_firmBellman_unique D hφ hψ (C := C + ‖ψ‖) fun p => ?_
    have h2 : |ψ p| ≤ ‖ψ‖ := by
      rw [← Real.norm_eq_abs]
      exact ψ.norm_coe_le_norm p
    calc |φ p - ψ p| ≤ |φ p| + |ψ p| := abs_sub _ _
      _ ≤ C + ‖ψ‖ := add_le_add (hC p) h2
  · exact gc_firm_policy_unique D hf hψ hcv p hz' (gcFirmPolicy_spec hψ p).1 e
      (gcFirmPolicy_spec hψ p).2

/-- **(1) is not a contraction when `q(k₀) > 1`** (NOTE to Ex 16.1e): adding a constant `c > 0` to
`ψ` raises `Tψ` by `q(k) c`, so `‖T(ψ + c) − Tψ‖ ≥ q(k₀) c > c = ‖(ψ + c) − ψ‖`. -/
theorem ex_16_1e_not_contraction (D : GcFirmData f g q β M) (k₀ : Icc a kmax)
    (hq : 1 < q k₀) (ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ) [Nonempty (Icc (0 : ℝ) kmax)] :
    dist (ψ + BoundedContinuousFunction.const (Icc a kmax × Icc (0 : ℝ) kmax) (1 : ℝ)) ψ <
      dist (gcFirmTB D (ψ + BoundedContinuousFunction.const (Icc a kmax × Icc (0 : ℝ) kmax)
        (1 : ℝ))) (gcFirmTB D ψ) := by
  set c₁ := BoundedContinuousFunction.const (Icc a kmax × Icc (0 : ℝ) kmax) (1 : ℝ) with hc₁
  obtain ⟨z₀⟩ := (inferInstance : Nonempty (Icc (0 : ℝ) kmax))
  have hc : ∀ p, (ψ + c₁) p = ψ p + 1 := fun p => by
    simp [hc₁, BoundedContinuousFunction.const_apply]
  have hshift : ∀ p, gcFirmT f g q ⇑(ψ + c₁) p = gcFirmT f g q ψ p + q p.1 := fun p => by
    obtain ⟨z₁, hz₁, e₁⟩ := gcFirmT_attained D (ψ + c₁).continuous p
    obtain ⟨z₂, hz₂, e₂⟩ := gcFirmT_attained D ψ.continuous p
    have a1 := gcFirmT_ge D (ψ + c₁).continuous p z₂ hz₂
    have a2 := gcFirmT_ge D ψ.continuous p z₁ hz₁
    rw [hc] at e₁ a1
    apply le_antisymm <;> nlinarith
  have hd1 : dist (ψ + c₁) ψ ≤ 1 :=
    (BoundedContinuousFunction.dist_le zero_le_one).2 fun p => by
      rw [hc, Real.dist_eq, add_sub_cancel_left, abs_one]
  have hd2 : q k₀ ≤ dist (gcFirmTB D (ψ + c₁)) (gcFirmTB D ψ) := by
    have := BoundedContinuousFunction.dist_coe_le_dist (f := gcFirmTB D (ψ + c₁))
      (g := gcFirmTB D ψ) (k₀, z₀)
    rw [gcFirmTB_apply, gcFirmTB_apply, hshift, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos (D.q_pos k₀)] at this
    exact this
  linarith

end StokeyLucasPrescott.EquilibriumApplications
