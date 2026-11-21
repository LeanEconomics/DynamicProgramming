/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.OCDifferentiable

/-!
# The consumption-saving problem of §6.6.2: the model and existence

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSModel`), namespace renamed.

Miao, §6.6.2, pp. 186–188, and Exercises 6–7, p. 190. The consumer's cash on hand `x ≥ 0` is
split into consumption `c = x − s` and saving `s ∈ [0, x]`; next period's cash on hand is
`x′ = ρ(z′) s + w(z′)` where `z′` is next period's shock, drawn from `Q(z, ·)`. With
`ρ ≡ R` and `w(y) = y − rb` this is the book's `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`
(`cash_on_hand`, with `r = R − 1`); iid income is the constant kernel `Q(z, ·) = μ`
(`isFeller_const`); Exercise 6 is a general (Feller) kernel; Exercise 7 (Phelps) is
`ρ(z′) = R′`, `w ≡ y`.

* `CSModel`: the primitives `(u, β, Q, ρ, w)`.
* `CSModel.toOC T`: the problem as an optimal control model of §6.4 (`OCModel`) with horizon `T`:
  `X = A = [0, ∞)`, `Γ(x, z) = [0, x]`, `φ(x, s, z, z′) = ρ(z′)s + w(z′)`,
  `u_t(x, z, s) = u(max(x − s, 0))` (`= u(x − s)` on `Γ`), `u_T(x, z) = u(x)`.
* `CSModel.v n`: the time-to-go value functions `v_0 = u`,
  `v_n(x, z) = max_{s ∈ [0, x]} u(x − s) + β ∫ v_{n−1}(ρ(z′)s + w(z′), z′) Q(z, dz′)`
  (`v_zero`, `v_succ`); `V_t = v_{T−t}` for every horizon (`V_eq`).
* `CSModel.sav n`, `CSModel.cons n`: the saving and consumption policies `s_n`, `g_n`, with
  `s_0 = 0` and `g_0(x) = x`.
* `CSModel.Basic`: the standing hypotheses. They give the standing hypotheses of §6.4 (case (ii)
  of Assumption 6.4.3, `standing`), hence by **Theorem 6.4.1** every `v_n` is continuous on
  `[0, ∞) × Z` and the maximum is attained by `s_n` (`contV`, `sav_mem`, `obj_le`).

**Departures.** (1) The book's `u′′ < 0`, `u′ > 0`, `u′(0+) = ∞` make the logarithm admissible,
but consumption `c = 0` is feasible (`s = x`), so we need `u` finite and continuous on `[0, ∞)`
(`Basic.u_cont`). (2) For the first-order condition at `s = 0` and the Inada argument the next
cash on hand must stay away from `0`: `w > 0` (for the book, the cash floor `y_min − rb > 0`).
(3) **Theorem 6.4.3 does not apply** to this model: Assumption 6.4.10 asks `u_t(·, z, ·)` to be
strictly concave whenever `x ≠ x′`, but `u(x − s)` is constant along `x − s = c`
(`not_assumption6410`). Nor do Assumptions 6.4.7 and 6.4.13: `u_t` must be defined on all of
`X × A`, and by the Inada condition no concave differentiable extension of `u(x − s)` to `s > x`
exists. The properties of §6.6.2 are therefore proved directly (`CSProperties`,
`CSDifferentiable`), using Theorem 6.4.1 for existence and continuity.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology

/-- The **consumption-saving model** of Miao §6.6.2 (p. 187) in cash-on-hand form: utility `u`,
discount factor `β`, shock transition `Q`, and next period's cash on hand
`x′ = ρ(z′) s + w(z′)` after saving `s`. -/
structure CSModel (Z : Type*) [MeasurableSpace Z] where
  u : ℝ → ℝ
  β : ℝ
  Q : Kernel Z Z
  ρ : Z → ℝ
  w : Z → ℝ

/-- Miao, p. 187: with `x_t = R a_t + y_t + b`, `â_{t+1} = a_{t+1} + b` and `r = R − 1`, the
budget `c_t + a_{t+1} = R a_t + y_t` becomes `c_t + â_{t+1} = x_t`, and
`x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`; the borrowing limit `a_{t+1} ≥ −b` is `â_{t+1} ≥ 0`. -/
theorem cash_on_hand (R b a a' y y' c : ℝ) (hbud : c + a' = R * a + y) :
    c + (a' + b) = R * a + y + b ∧
      R * a' + y' + b = R * ((R * a + y + b) - c) + y' - (R - 1) * b ∧
      (-b ≤ a' ↔ 0 ≤ a' + b) := by
  refine ⟨by linarith, ?_, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have : a' = R * a + y - c := by linarith
  subst this
  ring

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z] (M : CSModel Z)

/-- The consumption-saving problem as an optimal control model of §6.4 with horizon `T`. -/
def toOC (T : ℕ) : OCModel ℝ ℝ Z where
  X := Set.Ici 0
  A := Set.Ici 0
  Q := M.Q
  Γ := fun x _ => Set.Icc 0 x
  φ := fun _ s _ z' => M.ρ z' * s + M.w z'
  u := fun _ x _ s => M.u (max (x - s) 0)
  uT := fun x _ => M.u x
  β := M.β
  T := T

/-- The **time-to-go value functions** `v_n` of Miao, p. 188. -/
noncomputable def v (n : ℕ) : ℝ → Z → ℝ := (M.toOC 0).W n

/-- The objective of the time-to-go Bellman equation:
`u(x − s) + β ∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)`. -/
noncomputable def obj (n : ℕ) (x : ℝ) (z : Z) (s : ℝ) : ℝ :=
  M.u (max (x - s) 0) + M.β * ∫ z', M.v n (M.ρ z' * s + M.w z') z' ∂M.Q z

/-- Miao, p. 188: `v_0 = u`. -/
theorem v_zero (x : ℝ) (z : Z) : M.v 0 x z = M.u x := rfl

/-- **The time-to-go Bellman equation** (Miao, p. 188):
`v_{n+1}(x, z) = sup_{s ∈ [0, x]} u(x − s) + β ∫ v_n(ρ(z′)s + w(z′), z′) Q(z, dz′)`. -/
theorem v_succ (n : ℕ) (x : ℝ) (z : Z) :
    M.v (n + 1) x z = sSup (M.obj n x z '' Set.Icc 0 x) := rfl

/-- The value functions of `toOC T` do not depend on the horizon. -/
theorem W_eq (T n : ℕ) : (M.toOC T).W n = M.v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OCModel.W]
    rw [ih]
    rfl

/-- Miao, p. 188: the value function of §6.4 at date `t` is the time-to-go value function with
`n = T − t`. -/
theorem V_eq (T t : ℕ) : (M.toOC T).V t = M.v (T - t) := M.W_eq T (T - t)

/-- The **saving policy** `s_n` (Miao, p. 188): `s_0 = 0`, and for `n ≥ 1` the selection `g_0`
from the policy correspondence of `toOC n`. -/
noncomputable def sav : ℕ → ℝ → Z → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => (M.toOC (n + 1)).g 0

/-- The **consumption policy** `g_n(x) = x − s_n(x)` (Miao, p. 188). -/
noncomputable def cons (n : ℕ) (x : ℝ) (z : Z) : ℝ := x - M.sav n x z

/-- **Exercise 6.5**, second property (Miao, p. 188): `g_0(x) = x` and `s_0(x) = 0`. -/
theorem ex_6_5_g0_s0 (x : ℝ) (z : Z) : M.cons 0 x z = x ∧ M.sav 0 x z = 0 :=
  ⟨sub_zero x, rfl⟩

/-- On the feasible set the reward is `u(x − s)`. -/
theorem obj_eq (n : ℕ) {x : ℝ} (z : Z) {s : ℝ} (hs : s ≤ x) :
    M.obj n x z s = M.u (x - s) + M.β * ∫ z', M.v n (M.ρ z' * s + M.w z') z' ∂M.Q z := by
  rw [obj, max_eq_left (sub_nonneg.2 hs)]

/-- Membership in the policy correspondence of `toOC (n + 1)` at date `0`. -/
theorem mem_G (n : ℕ) (x : ℝ) (z : Z) (s : ℝ) :
    s ∈ (M.toOC (n + 1)).G 0 x z ↔ s ∈ Set.Icc 0 x ∧ M.obj n x z s = M.v (n + 1) x z := by
  have h1 : (M.toOC (n + 1)).V (0 + 1) = M.v n := by rw [V_eq]; simp
  have h0 : (M.toOC (n + 1)).V 0 = M.v (n + 1) := by rw [V_eq]; simp
  simp only [OCModel.G, h1, h0]
  rfl

variable [MetricSpace Z]

/-- The **standing hypotheses** for §6.6.2: `β > 0`; `u` continuous, strictly increasing and
strictly concave on `[0, ∞)`; `ρ` and `w` continuous and positive (the cash floor); `Q` Feller. -/
structure Basic : Prop where
  β_pos : 0 < M.β
  u_cont : ContinuousOn M.u (Set.Ici 0)
  u_mono : StrictMonoOn M.u (Set.Ici 0)
  u_conc : StrictConcaveOn ℝ (Set.Ici 0) M.u
  ρ_cont : Continuous M.ρ
  ρ_pos : ∀ z, 0 < M.ρ z
  w_cont : Continuous M.w
  w_pos : ∀ z, 0 < M.w z
  feller : IsFeller M.Q

variable {M}

/-- `Γ(x, z) = [0, x]` is compact-valued and continuous on `X = [0, ∞)`
(Assumption 6.4.4). -/
theorem assumption644 (T : ℕ) : (M.toOC T).Assumption644 := by
  refine ⟨fun x _ _ => Set.Icc_subset_Ici_self, fun p => ?_⟩
  have hx0 : 0 ≤ p.1.1 := p.2.1
  have hne : (Set.Icc (0 : ℝ) p.1.1).Nonempty := ⟨0, le_rfl, hx0⟩
  have hfst : ∀ ps : ℕ → ↥((M.toOC T).X ×ˢ (Set.univ : Set Z)), Tendsto ps atTop (𝓝 p) →
      Tendsto (fun n => (ps n).1.1) atTop (𝓝 p.1.1) := fun ps hps =>
    ((continuous_fst.comp continuous_subtype_val).tendsto p).comp hps
  refine ⟨isCompact_Icc, ⟨hne, fun y hy ps hps => ?_⟩, ⟨hne, fun ps hps ys hys => ?_⟩⟩
  · refine ⟨0, fun n => min y (ps n).1.1, fun n _ => ⟨le_min hy.1 (ps n).2.1, min_le_right _ _⟩,
      ?_⟩
    have := (tendsto_const_nhds (x := y)).min (hfst ps hps)
    rwa [min_eq_left hy.2] at this
  · obtain ⟨B, hB⟩ := (hfst ps hps).bddAbove_range
    have hmem : ∀ n, ys n ∈ Set.Icc 0 B := fun n =>
      ⟨(hys n).1, (hys n).2.trans (hB ⟨n, rfl⟩)⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    refine ⟨y, ⟨ge_of_tendsto' hlim fun n => (hys (φ n)).1, ?_⟩, φ, hφ, hlim⟩
    exact le_of_tendsto_of_tendsto' hlim ((hfst ps hps).comp hφ.tendsto_atTop)
      fun n => (hys (φ n)).2

/-- The state transition `ρ(z′)s + w(z′)` maps `X × A` into `X` and is continuous
(Assumption 6.4.5). -/
theorem assumption645 (h : M.Basic) (T : ℕ) : (M.toOC T).Assumption645 := by
  refine ⟨fun x _ a ha z z' => ?_, ?_⟩
  · change 0 ≤ M.ρ z' * a + M.w z'
    exact add_nonneg (mul_nonneg (h.ρ_pos z').le ha) (h.w_pos z').le
  · change ContinuousOn (fun p : ℝ × ℝ × Z × Z => M.ρ p.2.2.2 * p.2.1 + M.w p.2.2.2) _
    exact ((h.ρ_cont.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      (continuous_fst.comp continuous_snd) |>.add
      (h.w_cont.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))).continuousOn

/-- The rewards `u(max(x − s, 0))` and `u(x)` are continuous (Assumption 6.4.6). -/
theorem assumption646 (h : M.Basic) (T : ℕ) : (M.toOC T).Assumption646 := by
  refine ⟨fun t _ => ?_, ?_⟩
  · change ContinuousOn (fun p : ℝ × Z × ℝ => M.u (max (p.1 - p.2.2) 0)) _
    have hc : Continuous fun p : ℝ × Z × ℝ => max (p.1 - p.2.2) 0 :=
      (continuous_fst.sub (continuous_snd.comp continuous_snd)).max continuous_const
    refine h.u_cont.comp hc.continuousOn fun p _ => ?_
    exact Set.mem_Ici.2 (le_max_right _ _)
  · change ContinuousOn (fun p : ℝ × Z => M.u p.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ)
    exact h.u_cont.comp continuous_fst.continuousOn fun p hp => hp.1

/-- An iid shock, the constant kernel `Q(z, ·) = μ`, is Feller. -/
theorem isFeller_const (μ : Measure Z) [IsProbabilityMeasure μ] :
    IsFeller (Kernel.const Z μ) := by
  intro f _ _
  have : markovOpR (Kernel.const Z μ) f = fun _ => ∫ z', f z' ∂μ := by
    funext z
    simp only [markovOpR, Kernel.const_apply]
  rw [this]
  exact continuous_const

variable [CompactSpace Z] [BorelSpace Z] [IsMarkovKernel M.Q]

/-- **The theory of §6.4 applies** (Theorem 6.4.1): for a compact shock space and a Feller `Q`,
`toOC T` satisfies the standing hypotheses of §6.4. -/
theorem standing (h : M.Basic) (T : ℕ) :
    (M.toOC T).Standing fun _ => True :=
  have : IsMarkovKernel (M.toOC T).Q := ‹IsMarkovKernel M.Q›
  OCModel.Standing.of_compact _ ⟨inferInstance, inferInstance, h.feller⟩ (assumption644 T)
    (assumption645 h T) (assumption646 h T)

/-- **Theorem 6.4.1 for §6.6.2** (Miao, p. 188): every `v_n` is continuous on `[0, ∞) × Z`. -/
theorem contV (h : M.Basic) (n : ℕ) :
    ContinuousOn (fun p : ℝ × Z => M.v n p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  have := (standing h n).contV (t := 0) (Nat.zero_le _)
  rwa [V_eq, Nat.sub_zero] at this

/-- The next-period continuation integrand is integrable whenever the next states are in
`[0, ∞)`. -/
theorem integrable_next (h : M.Basic) (n : ℕ) {s : ℝ} (hs : ∀ z', 0 ≤ M.ρ z' * s + M.w z')
    (z : Z) : Integrable (fun z' => M.v n (M.ρ z' * s + M.w z') z') (M.Q z) := by
  have hc : Continuous fun z' => M.v n (M.ρ z' * s + M.w z') z' := by
    exact (contV h n).comp_continuous (f := fun z' => (M.ρ z' * s + M.w z', z'))
      (((h.ρ_cont.mul continuous_const).add h.w_cont).prodMk continuous_id)
      fun z' => Set.mk_mem_prod (hs z') (Set.mem_univ _)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact integrable_of_abs_le hc.measurable fun z' => by
    have := hB z' (Set.mem_univ _)
    rwa [Real.norm_eq_abs] at this

/-- Every feasible saving does at most as well as `v_{n+1}` (Theorem 6.4.1). -/
theorem obj_le (h : M.Basic) (n : ℕ) {x : ℝ} {z : Z} {s : ℝ} (hs : s ∈ Set.Icc 0 x) :
    M.obj n x z s ≤ M.v (n + 1) x z := by
  have hx : x ∈ (M.toOC (n + 1)).X := hs.1.trans hs.2
  have := (standing h (n + 1)).obj_le_V (t := 0) (Nat.succ_pos _) hx (z := z) hs
  have h1 : (M.toOC (n + 1)).V (0 + 1) = M.v n := by rw [V_eq]; simp
  have h0 : (M.toOC (n + 1)).V 0 = M.v (n + 1) := by rw [V_eq]; simp
  rw [h1, h0] at this
  exact this

/-- **Existence of the optimal saving policy** (Theorem 6.4.1; Miao, p. 188): `s_{n+1}(x, z)`
is feasible and attains `v_{n+1}(x, z)`. -/
theorem sav_mem (h : M.Basic) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (z : Z) :
    M.sav (n + 1) x z ∈ Set.Icc 0 x ∧ M.obj n x z (M.sav (n + 1) x z) = M.v (n + 1) x z :=
  (M.mem_G n x z _).1 ((standing h (n + 1)).g_mem (t := 0) (Nat.succ_pos _) hx z)

/-- `v_{n+1}(x, z)` is the maximum of the objective over `[0, x]`. -/
theorem isMaxOn_sav (h : M.Basic) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (z : Z) :
    IsMaxOn (M.obj n x z) (Set.Icc 0 x) (M.sav (n + 1) x z) := fun s hs => by
  change M.obj n x z s ≤ M.obj n x z (M.sav (n + 1) x z)
  rw [(sav_mem h n hx z).2]
  exact obj_le h n hs

end CSModel

/-- **Theorem 6.4.3 does not apply to §6.6.2** (Miao, p. 188): Assumption 6.4.10 fails for
the reward `u(x − s)` whatever `u` is, since it is constant along `x − s = 1`. -/
theorem CSModel.not_assumption6410 {Z : Type*} [MeasurableSpace Z] [Nonempty Z] (M : CSModel Z)
    (T : ℕ) (hT : 0 < T) : ¬ (M.toOC T).Assumption6410 := by
  intro h
  obtain ⟨z⟩ := (inferInstance : Nonempty Z)
  have hX : ∀ x : ℝ, 0 ≤ x → x ∈ (M.toOC T).X := fun x hx => hx
  have := (h.2 0 hT z 1 (hX 1 one_pos.le) 2 (hX 2 two_pos.le) 0 (hX 0 le_rfl) 1
    (hX 1 one_pos.le) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  change 1 / 2 * M.u (max (1 - 0) 0) + 1 / 2 * M.u (max (2 - 1) 0) <
    M.u (max ((1 / 2 : ℝ) • (1 : ℝ) + (1 / 2 : ℝ) • 2 - ((1 / 2 : ℝ) • 0 + (1 / 2 : ℝ) • 1)) 0)
    at this
  norm_num at this
  linarith

end Miao.IncompleteMarkets
