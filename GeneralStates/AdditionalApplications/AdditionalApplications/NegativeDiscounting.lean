/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.Minimization
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Coase meets Bellman: optimality with negative discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.3.1 (pp. 273–281).

An agent faces a task of measure `x̂`; with `x` units left, effort `a` costs `c(a)` and leaves
`x − a`; losses are discounted by `δ > 1` (8.52). The cost `c` is strictly increasing, strictly
convex and continuously differentiable with `c(0) = 0 < c'(0)`.

The book assumes an `η ∈ (0, x̂)` with `c'(η) = δc'(0)` (8.53), which exists only when `x̂` is
large enough. We assume instead an `η > 0` with `c'(x) ≤ δc'(0) ⟺ x ≤ η` on `[0, x̂]`
(`η_spec`): (8.53) implies it (`η_spec_of_eq`), and such an `η` always exists (`η ≥ x̂` when
`c'(x̂) ≤ δc'(0)`), which is what makes the production chain results unconditional.

Value functions and policies are functions on `ℝ` that vanish off `[0, x̂]`.

* **Exercise 8.3.1**: the iterates (8.54) of `T_σ`.
* **Lemma 8.3.3**: each `T_σ` reaches its unique fixed point `v_σ` in `k₀ = ⌈x̂/η⌉` steps from
  every `v ∈ V`; hence `(V, 𝕋)` is order stable (Lemma A.5.19).
* **Lemma 8.3.4** (**Exercise 8.3.2**): every `v ∈ V₀` has a unique `v`-min-greedy policy, and it
  lies in `Σ`.
* **Lemma 8.3.5** (**Exercise 8.3.3**): `T` maps `V₀` into itself and `T^k v = v̄` for `k ≥ k₀`.
* **Theorem 8.3.6**: the fundamental min-optimality properties, `v̄ = v▿*`, the argmin
  characterisation of optimal policies, and uniqueness of the optimal policy.
* **Propositions 8.3.1 and 8.3.2** and **Definition 8.3.1**: the production chain equilibrium.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-- An order preserving map all of whose `k`-th iterates coincide is order stable, and every orbit
reaches its fixed point in `k` steps (Lemma A.5.19 in the form used by Lemma 8.3.3). -/
theorem orderStable_of_iterate_eq {V : Type*} [PartialOrder V] {S : V → V} (hS : Monotone S)
    {k : ℕ} (h : ∀ v w, S^[k] v = S^[k] w) (v₀ : V) :
    OrderStable S ∧ S (S^[k] v₀) = S^[k] v₀ ∧ (∀ w, S w = w → w = S^[k] v₀) ∧
      ∀ v n, k ≤ n → S^[n] v = S^[k] v₀ := by
  have hfix : S (S^[k] v₀) = S^[k] v₀ := by
    rw [← iterate_succ_apply' S k v₀, iterate_succ_apply, h (S v₀) v₀]
  have huniq : ∀ w, S w = w → w = S^[k] v₀ := fun w hw => by
    rw [← h w v₀]
    exact (iterate_fixed hw k).symm
  refine ⟨orderStable_of_up_down hfix (fun v hv => ?_) (fun v hv => ?_), hfix, huniq,
    fun v n hn => ?_⟩
  · rw [← h v v₀]
    exact hS.monotone_iterate_of_le_map hv (Nat.zero_le k)
  · rw [← h v v₀]
    exact hS.antitone_iterate_of_map_le hv (Nat.zero_le k)
  · rw [← Nat.sub_add_cancel hn, iterate_add_apply, h v v₀]
    exact iterate_fixed hfix _

/-- The negative-discounting problem of §8.3.1.2. -/
structure NegDiscount where
  /-- the effort cost -/
  c : ℝ → ℝ
  /-- the discount factor, `δ > 1` -/
  δ : ℝ
  one_lt_δ : 1 < δ
  /-- the size of the task -/
  xh : ℝ
  xh_pos : 0 < xh
  /-- the threshold below which the agent finishes the task at once -/
  η : ℝ
  η_pos : 0 < η
  c_zero : c 0 = 0
  differentiable : Differentiable ℝ c
  continuous_deriv : Continuous (deriv c)
  strictConvexOn : StrictConvexOn ℝ (Ici 0) c
  strictMonoOn : StrictMonoOn c (Ici 0)
  deriv_zero_pos : 0 < deriv c 0
  η_spec : ∀ x ∈ Set.Icc 0 xh, deriv c x ≤ δ * deriv c 0 ↔ x ≤ η

namespace NegDiscount

variable (N : NegDiscount)

theorem δ_pos : 0 < N.δ := one_pos.trans N.one_lt_δ

theorem zero_mem : (0 : ℝ) ∈ Set.Icc 0 N.xh := ⟨le_rfl, N.xh_pos.le⟩

theorem c_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : N.c a ≤ N.c b :=
  N.strictMonoOn.monotoneOn ha (ha.trans hab) hab

/-- (8.53) gives `η_spec`, since `c'` is strictly increasing. -/
theorem η_spec_of_eq {c : ℝ → ℝ} {δ xh η : ℝ} (hd : Differentiable ℝ c)
    (hc : StrictConvexOn ℝ (Ici 0) c) (hη : η ∈ Ioo 0 xh) (heq : deriv c η = δ * deriv c 0) :
    ∀ x ∈ Set.Icc 0 xh, deriv c x ≤ δ * deriv c 0 ↔ x ≤ η := fun x hx => by
  rw [← heq]
  exact (hc.strictMonoOn_deriv fun y _ => hd y).le_iff_le hx.1 (mem_Ici.2 hη.1.le)

/-- The number of steps `k₀ = ⌈x̂/η⌉` after which every policy has finished the task. -/
noncomputable def k0 : ℕ := ⌈N.xh / N.η⌉₊

/-- The policy set `Σ`: `0 ≤ σ(x) ≤ x`, `σ` and the effort `x − σ(x)` increasing, and
`σ(x) = 0 ⟺ x ≤ η`, all on `[0, x̂]`; `σ` vanishes off `[0, x̂]`. -/
@[ext]
structure Policy (N : NegDiscount) where
  /-- the remaining task after this period's effort -/
  σ : ℝ → ℝ
  mem : ∀ x ∈ Set.Icc 0 N.xh, σ x ∈ Set.Icc 0 x
  monotoneOn : MonotoneOn σ (Set.Icc 0 N.xh)
  monotoneOn_effort : MonotoneOn (fun x => x - σ x) (Set.Icc 0 N.xh)
  eq_zero_iff : ∀ x ∈ Set.Icc 0 N.xh, σ x = 0 ↔ x ≤ N.η
  zero_outside : ∀ x ∉ Set.Icc 0 N.xh, σ x = 0

namespace Policy

variable {N} (σ : N.Policy)

theorem mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) : σ.σ x ∈ Set.Icc 0 N.xh :=
  ⟨(σ.mem x hx).1, (σ.mem x hx).2.trans hx.2⟩

theorem iterate_mem {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (j : ℕ) :
    σ.σ^[j] x ∈ Set.Icc 0 N.xh := by
  induction j with
  | zero => exact hx
  | succ j ih =>
    rw [iterate_succ_apply']
    exact σ.mem_Icc ih

theorem map_zero : σ.σ 0 = 0 := by
  have h := σ.mem 0 N.zero_mem
  exact le_antisymm h.2 h.1

/-- Effort is at least `η` above `η`: `σ(x) ≤ (x − η) ∨ 0`. -/
theorem le_max_sub {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) : σ.σ x ≤ max 0 (x - N.η) := by
  by_cases h : x ≤ N.η
  · rw [(σ.eq_zero_iff x hx).2 h]
    exact le_max_left _ _
  · have hlt := not_le.1 h
    have hη : N.η ∈ Set.Icc 0 N.xh := ⟨N.η_pos.le, hlt.le.trans hx.2⟩
    have h1 : N.η - σ.σ N.η ≤ x - σ.σ x := σ.monotoneOn_effort hη hx hlt.le
    rw [(σ.eq_zero_iff N.η hη).2 le_rfl, sub_zero] at h1
    exact le_max_of_le_right (by linarith)

theorem iterate_le {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (k : ℕ) :
    σ.σ^[k] x ≤ max 0 (x - k * N.η) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    refine (σ.le_max_sub (σ.iterate_mem hx k)).trans (max_le (le_max_left _ _) ?_)
    rcases le_total 0 (x - k * N.η) with h0 | h0
    · rw [max_eq_right h0] at ih
      refine le_max_of_le_right ?_
      push_cast
      linarith
    · rw [max_eq_left h0] at ih
      exact le_max_of_le_left (by linarith [N.η_pos])

/-- Every orbit of `σ` reaches `0` within `k₀ = ⌈x̂/η⌉` steps. -/
theorem iterate_eq_zero {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) {k : ℕ} (hk : N.k0 ≤ k) :
    σ.σ^[k] x = 0 := by
  have h1 : N.xh ≤ k * N.η := by
    have : N.xh / N.η ≤ k := (Nat.le_ceil _).trans (Nat.cast_le.2 hk)
    rwa [div_le_iff₀ N.η_pos] at this
  have h2 := σ.iterate_le hx k
  rw [max_eq_left (by linarith [hx.2])] at h2
  exact le_antisymm h2 (σ.iterate_mem hx k).1

/-- `σ` is `1`-Lipschitz on `[0, x̂]`, by (ii) and (iii). -/
theorem abs_sub_le {x y : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (hy : y ∈ Set.Icc 0 N.xh) :
    |σ.σ x - σ.σ y| ≤ |x - y| := by
  rcases le_total x y with hxy | hxy
  · have h1 := σ.monotoneOn hx hy hxy
    have h2 : x - σ.σ x ≤ y - σ.σ y := σ.monotoneOn_effort hx hy hxy
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := σ.monotoneOn hy hx hxy
    have h2 : y - σ.σ y ≤ x - σ.σ x := σ.monotoneOn_effort hy hx hxy
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (by linarith)]
    linarith

theorem continuousOn : ContinuousOn σ.σ (Set.Icc 0 N.xh) :=
  (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    exact σ.abs_sub_le hx hy).continuousOn

end Policy

/-- The policy `x ↦ (x − η) ∨ 0`. -/
noncomputable def ση : N.Policy where
  σ := (Set.Icc 0 N.xh).indicator fun x => max 0 (x - N.η)
  mem x hx := by
    rw [Set.indicator_of_mem hx]
    exact ⟨le_max_left _ _, max_le hx.1 (by linarith [N.η_pos])⟩
  monotoneOn x hx y hy hxy := by
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact max_le_max le_rfl (by linarith)
  monotoneOn_effort x hx y hy hxy := by
    have e : ∀ z, z - max 0 (z - N.η) = min z N.η := fun z => by
      rw [← min_sub_sub_left, sub_zero, sub_sub_cancel]
    change x - (Set.Icc 0 N.xh).indicator _ x ≤ y - (Set.Icc 0 N.xh).indicator _ y
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, e, e]
    exact min_le_min hxy le_rfl
  eq_zero_iff x hx := by
    rw [Set.indicator_of_mem hx, max_eq_left_iff, sub_nonpos]
  zero_outside x hx := Set.indicator_of_notMem hx _

/-- The value space `V`: functions increasing on `[0, x̂]`, vanishing at `0` and off `[0, x̂]`. -/
abbrev Val (N : NegDiscount) :=
  {v : ℝ → ℝ // MonotoneOn v (Set.Icc 0 N.xh) ∧ v 0 = 0 ∧ ∀ x ∉ Set.Icc 0 N.xh, v x = 0}

/-- `(T_σ v)(x) = c(x − σ(x)) + δv(σ(x))` on `[0, x̂]`. -/
noncomputable def Tfun (σ v : ℝ → ℝ) : ℝ → ℝ :=
  (Set.Icc 0 N.xh).indicator fun x => N.c (x - σ x) + N.δ * v (σ x)

/-- The policy operator `T_σ` on `V`. -/
noncomputable def T (σ : N.Policy) (v : N.Val) : N.Val :=
  ⟨N.Tfun σ.σ v.1, fun x hx y hy hxy => by
    rw [Tfun, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact add_le_add (N.c_mono (sub_nonneg.2 (σ.mem x hx).2) (σ.monotoneOn_effort hx hy hxy))
      (mul_le_mul_of_nonneg_left (v.2.1 (σ.mem_Icc hx) (σ.mem_Icc hy) (σ.monotoneOn hx hy hxy))
        N.δ_pos.le), by
    rw [Tfun, Set.indicator_of_mem N.zero_mem, σ.map_zero, sub_zero, v.2.2.1, mul_zero, add_zero,
      N.c_zero], fun x hx => Set.indicator_of_notMem hx _⟩

theorem T_apply (σ : N.Policy) (v : N.Val) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    (N.T σ v).1 x = N.c (x - σ.σ x) + N.δ * v.1 (σ.σ x) := by
  change N.Tfun σ.σ v.1 x = _
  exact Set.indicator_of_mem hx _

/-- The ADP `(V, 𝕋)` of §8.3.1.2. -/
noncomputable def adp : ADP N.Val N.Policy where
  T := N.T
  mono σ v w hvw := fun x => by
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · change (N.T σ v).1 x ≤ (N.T σ w).1 x
      rw [N.T_apply σ v hx, N.T_apply σ w hx]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hvw _) N.δ_pos.le)
    · change (N.T σ v).1 x ≤ (N.T σ w).1 x
      rw [(N.T σ v).2.2.2 x hx, (N.T σ w).2.2.2 x hx]
  nonempty := ⟨N.ση⟩

/-- **Exercise 8.3.1** (p. 279), (8.54): `(T_σ^k v)(x) = ∑_{j<k} δ^j c(π(σ^j x)) + δ^k v(σ^k x)`,
with `π(x) = x − σ(x)`. -/
theorem exercise_8_3_1 (σ : N.Policy) (v : N.Val) (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 N.xh) :
    ((N.adp.T σ)^[k] v).1 x = ∑ j ∈ Finset.range k,
      N.δ ^ j * N.c (σ.σ^[j] x - σ.σ (σ.σ^[j] x)) + N.δ ^ k * v.1 (σ.σ^[k] x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    change (N.T σ _).1 x = _
    rw [N.T_apply σ _ hx, ih (σ.mem_Icc hx), Finset.sum_range_succ', mul_add, Finset.mul_sum]
    simp only [← iterate_succ_apply, iterate_zero, id_eq, pow_zero, one_mul, ← mul_assoc,
      ← pow_succ']
    ring

theorem iterate_k0_eq (σ : N.Policy) (v w : N.Val) :
    (N.adp.T σ)^[N.k0] v = (N.adp.T σ)^[N.k0] w := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Set.Icc 0 N.xh
  · rw [N.exercise_8_3_1 σ v _ hx, N.exercise_8_3_1 σ w _ hx, σ.iterate_eq_zero hx le_rfl,
      v.2.2.1, w.2.2.1]
  · rw [((N.adp.T σ)^[N.k0] v).2.2.2 x hx, ((N.adp.T σ)^[N.k0] w).2.2.2 x hx]

/-- The zero function, an element of `V`. -/
def zeroVal : N.Val := ⟨0, fun _ _ _ _ _ => le_rfl, rfl, fun _ _ => rfl⟩

/-- **Lemma 8.3.3** (p. 280): each `T_σ` has a unique fixed point `v_σ` in `V`, and
`T_σ^k v = v_σ` for all `v ∈ V` and `k ≥ k₀ = ⌈x̂/η⌉`. -/
theorem lemma_8_3_3 (σ : N.Policy) :
    ∃ vσ, N.adp.T σ vσ = vσ ∧ (∀ v, N.adp.T σ v = v → v = vσ) ∧
      ∀ v k, N.k0 ≤ k → (N.adp.T σ)^[k] v = vσ := by
  obtain ⟨-, hfix, huniq, hconv⟩ :=
    orderStable_of_iterate_eq (N.adp.mono σ) (N.iterate_k0_eq σ) N.zeroVal
  exact ⟨_, hfix, huniq, hconv⟩

/-- `(V, 𝕋)` is order stable (Lemma 8.3.3 and Lemma A.5.19). -/
theorem isOrderStable : N.adp.IsOrderStable := fun σ =>
  (orderStable_of_iterate_eq (N.adp.mono σ) (N.iterate_k0_eq σ) N.zeroVal).1

/-! ### The min-greedy policy (Lemma 8.3.4) -/

/-- `V₀`: convex and continuous on `[0, x̂]`, with `c'(0)x ≤ v(x) ≤ c(x)` there. -/
def InV0 (v : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Set.Icc 0 N.xh) v ∧ ContinuousOn v (Set.Icc 0 N.xh) ∧
    ∀ x ∈ Set.Icc 0 N.xh, deriv N.c 0 * x ≤ v x ∧ v x ≤ N.c x

/-- The objective `g(x, y) = c(x − y) + δv(y)` of the Bellman equation. -/
def g (v : ℝ → ℝ) (x y : ℝ) : ℝ := N.c (x - y) + N.δ * v y

/-- The tangent at `0`: `c'(0)z ≤ c(z)` for `z ≥ 0`. -/
theorem tangent_zero {z : ℝ} (hz : 0 ≤ z) : deriv N.c 0 * z ≤ N.c z := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [mul_zero, N.c_zero]
  · have h := N.strictConvexOn.convexOn.deriv_le_slope (mem_Ici.2 le_rfl) (mem_Ici.2 hz.le) hz
      (N.differentiable 0)
    rwa [slope_def_field, N.c_zero, sub_zero, sub_zero, le_div_iff₀ hz] at h

/-- Strict convexity in the form `c(p) + c(q) < c(a) + c(b)` for `a < p < b`,
`p + q = a + b`. -/
theorem four_point_strict {a b p q : ℝ} (ha : 0 ≤ a) (hap : a < p) (hpb : p < b)
    (hs : p + q = a + b) : N.c p + N.c q < N.c a + N.c b := by
  have hab : a < b := hap.trans hpb
  have hba : 0 < b - a := sub_pos.2 hab
  set t := (b - p) / (b - a) with ht
  have ht0 : 0 < t := div_pos (sub_pos.2 hpb) hba
  have ht1 : 0 < 1 - t := by
    rw [ht, one_sub_div hba.ne']
    exact div_pos (by linarith) hba
  have hp : t * a + (1 - t) * b = p := by
    rw [ht]
    field_simp
    ring
  have hq : (1 - t) * a + t * b = q := by
    rw [ht, show q = a + b - p by linarith]
    field_simp
    ring
  have h1 := N.strictConvexOn.2 (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab.ne ht0 ht1
    (by ring)
  have h2 := N.strictConvexOn.2 (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab.ne ht1 ht0
    (by ring)
  simp only [smul_eq_mul] at h1 h2
  rw [hp] at h1
  rw [hq] at h2
  linarith

/-- Convexity in the form `v(p) + v(q) ≤ v(a) + v(b)` for `a ≤ p, q ≤ b`, `p + q = a + b`. -/
theorem four_point {v : ℝ → ℝ} (hv : ConvexOn ℝ (Set.Icc 0 N.xh) v) {a b p q : ℝ}
    (ha : a ∈ Set.Icc 0 N.xh) (hb : b ∈ Set.Icc 0 N.xh) (hap : a ≤ p) (hpb : p ≤ b)
    (haq : a ≤ q) (hqb : q ≤ b) (hs : p + q = a + b) : v p + v q ≤ v a + v b := by
  rcases (hap.trans hpb).eq_or_lt with hab | hab
  · have hp : p = a := by linarith
    have hq : q = a := by linarith
    rw [hp, hq, ← hab]
  · have hba : 0 < b - a := sub_pos.2 hab
    set t := (b - p) / (b - a) with ht
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hpb) hba.le
    have ht1 : 0 ≤ 1 - t := by
      rw [ht, one_sub_div hba.ne']
      exact div_nonneg (by linarith) hba.le
    have hp : t * a + (1 - t) * b = p := by
      rw [ht]
      field_simp
      ring
    have hq : (1 - t) * a + t * b = q := by
      rw [ht, show q = a + b - p by linarith]
      field_simp
      ring
    have h1 := hv.2 ha hb ht0 ht1 (by ring)
    have h2 := hv.2 ha hb ht1 ht0 (by ring)
    simp only [smul_eq_mul] at h1 h2
    rw [hp] at h1
    rw [hq] at h2
    linarith

theorem v_zero {v : ℝ → ℝ} (hv : N.InV0 v) : v 0 = 0 := by
  have h := hv.2.2 0 N.zero_mem
  rw [mul_zero, N.c_zero] at h
  exact le_antisymm h.2 h.1

theorem exists_min {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    ∃ y ∈ Set.Icc 0 x, IsMinOn (N.g v x) (Set.Icc 0 x) y := by
  have hc : ContinuousOn (fun y => N.c (x - y) + N.δ * v y) (Set.Icc 0 x) :=
    (N.differentiable.continuous.comp (continuous_const.sub continuous_id)).continuousOn.add
      (continuousOn_const.mul (hv.2.1.mono (Icc_subset_Icc le_rfl hx.2)))
  exact isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hx.1) hc

/-- The minimiser of `g(x, ·)` on `[0, x]` is unique: `g(x, ·)` is strictly convex. -/
theorem unique_min {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) {y₁ y₂ : ℝ}
    (h₁ : y₁ ∈ Set.Icc 0 x) (h₂ : y₂ ∈ Set.Icc 0 x) (hm₁ : IsMinOn (N.g v x) (Set.Icc 0 x) y₁)
    (hm₂ : IsMinOn (N.g v x) (Set.Icc 0 x) y₂) : y₁ = y₂ := by
  by_contra hne
  wlog h : y₁ < y₂ generalizing y₁ y₂
  · exact this h₂ h₁ hm₂ hm₁ (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne))
  have hm : (y₁ + y₂) / 2 ∈ Set.Icc 0 x := ⟨by linarith [h₁.1], by linarith [h₂.2]⟩
  have hc := N.strictConvexOn.2 (mem_Ici.2 (sub_nonneg.2 h₁.2)) (mem_Ici.2 (sub_nonneg.2 h₂.2))
    (by intro e; exact hne (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hv' := hv.1.2 ⟨h₁.1, h₁.2.trans hx.2⟩ ⟨h₂.1, h₂.2.trans hx.2⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc hv'
  have e1 : 1 / 2 * (x - y₁) + 1 / 2 * (x - y₂) = x - (y₁ + y₂) / 2 := by ring
  have e2 : 1 / 2 * y₁ + 1 / 2 * y₂ = (y₁ + y₂) / 2 := by ring
  rw [e1] at hc
  rw [e2] at hv'
  have a1 := isMinOn_iff.1 hm₁ _ hm
  have a2 := isMinOn_iff.1 hm₁ _ h₂
  have a3 := isMinOn_iff.1 hm₂ _ h₁
  simp only [g] at a1 a2 a3
  nlinarith [N.δ_pos]

/-- A minimiser of `g(x, ·)` on `[0, x]`. -/
noncomputable def greedyFun (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  Classical.epsilon fun y => y ∈ Set.Icc 0 x ∧ IsMinOn (N.g v x) (Set.Icc 0 x) y

theorem greedy_spec {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    N.greedyFun v x ∈ Set.Icc 0 x ∧ IsMinOn (N.g v x) (Set.Icc 0 x) (N.greedyFun v x) := by
  obtain ⟨y, hy, hm⟩ := N.exists_min hv hx
  exact Classical.epsilon_spec (p := fun y => y ∈ Set.Icc 0 x ∧
    IsMinOn (N.g v x) (Set.Icc 0 x) y) ⟨y, hy, hm⟩

/-- (ii): the minimiser is increasing, since `g` has strictly decreasing differences. -/
theorem greedyFun_monotoneOn {v : ℝ → ℝ} (hv : N.InV0 v) :
    MonotoneOn (N.greedyFun v) (Set.Icc 0 N.xh) := by
  intro x₁ hx₁ x₂ hx₂ h12
  rcases h12.eq_or_lt with rfl | hlt
  · exact le_rfl
  by_contra hcon
  have hyx := not_le.1 hcon
  obtain ⟨s₁, m₁⟩ := N.greedy_spec hv hx₁
  obtain ⟨s₂, m₂⟩ := N.greedy_spec hv hx₂
  have hA := isMinOn_iff.1 m₁ (N.greedyFun v x₂) ⟨s₂.1, hyx.le.trans s₁.2⟩
  have hB := isMinOn_iff.1 m₂ (N.greedyFun v x₁) ⟨s₁.1, s₁.2.trans h12⟩
  have hC := N.four_point_strict (a := x₁ - N.greedyFun v x₁) (b := x₂ - N.greedyFun v x₂)
    (p := x₁ - N.greedyFun v x₂) (q := x₂ - N.greedyFun v x₁) (sub_nonneg.2 s₁.2)
    (by linarith) (by linarith) (by ring)
  simp only [g] at hA hB
  linarith

/-- (iii): the effort `x − σ(x)` is increasing, since `v` is convex and the minimiser unique. -/
theorem greedyFun_effort {v : ℝ → ℝ} (hv : N.InV0 v) :
    MonotoneOn (fun x => x - N.greedyFun v x) (Set.Icc 0 N.xh) := by
  intro x₁ hx₁ x₂ hx₂ h12
  change x₁ - N.greedyFun v x₁ ≤ x₂ - N.greedyFun v x₂
  rcases h12.eq_or_lt with rfl | hlt
  · exact le_rfl
  by_contra hcon
  have hax := not_le.1 hcon
  obtain ⟨s₁, m₁⟩ := N.greedy_spec hv hx₁
  obtain ⟨s₂, m₂⟩ := N.greedy_spec hv hx₂
  set y₁ := N.greedyFun v x₁
  set y₂ := N.greedyFun v x₂
  have hz₁ : x₁ - (x₂ - y₂) ∈ Set.Icc 0 x₁ := ⟨by linarith [s₁.1], by linarith [s₂.2]⟩
  have hz₂ : x₂ - (x₁ - y₁) ∈ Set.Icc 0 x₂ := ⟨by linarith [s₁.1], by linarith [s₁.2]⟩
  have hA := isMinOn_iff.1 m₁ _ hz₁
  have hB := isMinOn_iff.1 m₂ _ hz₂
  have hC := N.four_point hv.1 (a := y₁) (b := y₂) (p := x₁ - (x₂ - y₂)) (q := x₂ - (x₁ - y₁))
    ⟨s₁.1, s₁.2.trans hx₁.2⟩ ⟨s₂.1, s₂.2.trans hx₂.2⟩ (by linarith) (by linarith)
    (by linarith) (by linarith) (by ring)
  simp only [g, sub_sub_cancel] at hA hB
  have hδ := mul_le_mul_of_nonneg_left hC N.δ_pos.le
  -- `x₁ − (x₂ − y₂)` is also a minimiser at `x₁`
  have hmin : IsMinOn (N.g v x₁) (Set.Icc 0 x₁) (x₁ - (x₂ - y₂)) := isMinOn_iff.2 fun y hy => by
    have := isMinOn_iff.1 m₁ y hy
    simp only [g, sub_sub_cancel] at this ⊢
    nlinarith
  have := N.unique_min hv hx₁ hz₁ s₁ hmin m₁
  linarith

/-- (iv): the minimiser vanishes exactly when `x ≤ η`. -/
theorem greedyFun_eq_zero_iff {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ}
    (hx : x ∈ Set.Icc 0 N.xh) : N.greedyFun v x = 0 ↔ x ≤ N.η := by
  obtain ⟨s, m⟩ := N.greedy_spec hv hx
  have hv0 := N.v_zero hv
  constructor
  · intro h0
    by_contra hxη
    have hxη' := not_le.1 hxη
    have hx0 : 0 < x := N.η_pos.trans hxη'
    have hc' : N.δ * deriv N.c 0 < deriv N.c x := not_le.1 (mt (N.η_spec x hx).1 hxη)
    -- `c'(x − y) > δc'(y)` for small `y > 0`
    have hev : ∀ᶠ y in 𝓝 (0 : ℝ), N.δ * deriv N.c y < deriv N.c (x - y) :=
      ContinuousAt.eventually_lt (f := fun y => N.δ * deriv N.c y)
        (g := fun y => deriv N.c (x - y)) (continuous_const.mul N.continuous_deriv).continuousAt
        (N.continuous_deriv.comp (continuous_const.sub continuous_id)).continuousAt
        (by simpa using hc')
    have hlt : ∀ᶠ y in 𝓝 (0 : ℝ), y < x := Iio_mem_nhds hx0
    obtain ⟨y, ⟨h1, h2⟩, h3⟩ :=
      (((hev.and hlt).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have h3' : 0 < y := h3
    rw [h0] at m
    have hA := isMinOn_iff.1 m y ⟨h3'.le, h2.le⟩
    simp only [g, sub_zero, hv0, mul_zero, add_zero] at hA
    have hvy := (hv.2.2 y ⟨h3'.le, h2.le.trans hx.2⟩).2
    have s1 := N.strictConvexOn.deriv_lt_slope (mem_Ici.2 (by linarith : 0 ≤ x - y))
      (mem_Ici.2 hx.1) (by linarith : x - y < x) (N.differentiable _)
    rw [slope_def_field, sub_sub_cancel, lt_div_iff₀ h3'] at s1
    have s2 := N.strictConvexOn.slope_lt_deriv (mem_Ici.2 le_rfl) (mem_Ici.2 h3'.le) h3'
      (N.differentiable y)
    rw [slope_def_field, N.c_zero, sub_zero, sub_zero, div_lt_iff₀ h3'] at s2
    nlinarith [mul_lt_mul_of_pos_right h1 h3', mul_le_mul_of_nonneg_left hvy N.δ_pos.le,
      mul_lt_mul_of_pos_left s2 N.δ_pos]
  · intro hxη
    by_contra hne
    have hy : 0 < N.greedyFun v x := lt_of_le_of_ne s.1 (Ne.symm hne)
    have hA := isMinOn_iff.1 m 0 ⟨le_rfl, hx.1⟩
    simp only [g, sub_zero, hv0, mul_zero, add_zero] at hA
    have hvy := (hv.2.2 _ ⟨s.1, s.2.trans hx.2⟩).1
    have hc' := (N.η_spec x hx).2 hxη
    have s1 := N.strictConvexOn.slope_lt_deriv
      (mem_Ici.2 (sub_nonneg.2 s.2)) (mem_Ici.2 hx.1) (by linarith : x - N.greedyFun v x < x)
      (N.differentiable x)
    rw [slope_def_field, sub_sub_cancel, div_lt_iff₀ hy] at s1
    nlinarith [mul_le_mul_of_nonneg_right hc' hy.le, mul_le_mul_of_nonneg_left hvy N.δ_pos.le]

/-- The `v`-min-greedy policy of Lemma 8.3.4. -/
noncomputable def greedy {v : ℝ → ℝ} (hv : N.InV0 v) : N.Policy where
  σ := (Set.Icc 0 N.xh).indicator (N.greedyFun v)
  mem x hx := by
    rw [Set.indicator_of_mem hx]
    exact (N.greedy_spec hv hx).1
  monotoneOn x hx y hy hxy := by
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact N.greedyFun_monotoneOn hv hx hy hxy
  monotoneOn_effort x hx y hy hxy := by
    change x - (Set.Icc 0 N.xh).indicator _ x ≤ y - (Set.Icc 0 N.xh).indicator _ y
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact N.greedyFun_effort hv hx hy hxy
  eq_zero_iff x hx := by
    rw [Set.indicator_of_mem hx]
    exact N.greedyFun_eq_zero_iff hv hx
  zero_outside x hx := Set.indicator_of_notMem hx _

theorem greedy_isMinOn {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    IsMinOn (N.g v x) (Set.Icc 0 x) ((N.greedy hv).σ x) := by
  change IsMinOn (N.g v x) (Set.Icc 0 x) ((Set.Icc 0 N.xh).indicator (N.greedyFun v) x)
  rw [Set.indicator_of_mem hx]
  exact (N.greedy_spec hv hx).2

/-- **Lemma 8.3.4** (p. 280) and **Exercise 8.3.2**: for `v ∈ V₀` the policy attaining
`min_{0 ≤ a ≤ x} {c(x − a) + δv(a)}` at each `x` lies in `Σ` and is `v`-min-greedy, and
`(Tv)(x) = min_{0 ≤ a ≤ x} {c(x − a) + δv(a)}`. -/
theorem lemma_8_3_4 (v : N.Val) (hv : N.InV0 v.1) :
    N.adp.IsMinGreedy v (N.greedy hv) ∧ N.adp.IsMinBellmanValue v (N.adp.T (N.greedy hv) v) ∧
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g v.1 x) (Set.Icc 0 x) ((N.greedy hv).σ x) ∧
        (N.adp.T (N.greedy hv) v).1 x = N.g v.1 x ((N.greedy hv).σ x) := by
  have hg : N.adp.IsMinGreedy v (N.greedy hv) := fun τ x => by
    change (N.T _ v).1 x ≤ (N.T τ v).1 x
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · rw [N.T_apply _ _ hx, N.T_apply _ _ hx]
      exact isMinOn_iff.1 (N.greedy_isMinOn hv hx) _ (τ.mem x hx)
    · rw [(N.T _ v).2.2.2 x hx, (N.T τ v).2.2.2 x hx]
  refine ⟨hg, IsLeast.isGLB ⟨⟨_, rfl⟩, ?_⟩, fun x hx => ⟨N.greedy_isMinOn hv hx, N.T_apply _ _ hx⟩⟩
  rintro _ ⟨τ, rfl⟩
  exact hg τ

theorem exercise_8_3_2 (v : N.Val) (hv : N.InV0 v.1) :
    N.adp.IsMinGreedy v (N.greedy hv) ∧ N.adp.IsMinBellmanValue v (N.adp.T (N.greedy hv) v) ∧
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g v.1 x) (Set.Icc 0 x) ((N.greedy hv).σ x) ∧
        (N.adp.T (N.greedy hv) v).1 x = N.g v.1 x ((N.greedy hv).σ x) :=
  N.lemma_8_3_4 v hv

/-! ### The Bellman operator on `V₀` (Lemma 8.3.5) -/

/-- `V₀` as a type. -/
abbrev V0 (N : NegDiscount) := {v : N.Val // N.InV0 v.1}

theorem T_greedy_mem (v : N.V0) : N.InV0 (N.T (N.greedy v.2) v.1).1 := by
  set σ := N.greedy v.2
  have hval : ∀ x ∈ Set.Icc 0 N.xh, (N.T σ v.1).1 x = N.c (x - σ.σ x) + N.δ * v.1.1 (σ.σ x) :=
    fun x hx => N.T_apply σ v.1 hx
  refine ⟨⟨convex_Icc 0 N.xh, fun x₁ hx₁ x₂ hx₂ a b ha hb hab => ?_⟩, ?_, fun x hx => ?_⟩
  · have hxl : a * x₁ + b * x₂ ∈ Set.Icc 0 N.xh := by
      simpa only [smul_eq_mul] using convex_Icc 0 N.xh hx₁ hx₂ ha hb hab
    have hyl : a * σ.σ x₁ + b * σ.σ x₂ ∈ Set.Icc 0 (a * x₁ + b * x₂) :=
      ⟨by nlinarith [(σ.mem x₁ hx₁).1, (σ.mem x₂ hx₂).1],
        by nlinarith [(σ.mem x₁ hx₁).2, (σ.mem x₂ hx₂).2]⟩
    have hmin := isMinOn_iff.1 (N.greedy_isMinOn v.2 hxl) _ hyl
    have hc := N.strictConvexOn.convexOn.2 (mem_Ici.2 (sub_nonneg.2 (σ.mem x₁ hx₁).2))
      (mem_Ici.2 (sub_nonneg.2 (σ.mem x₂ hx₂).2)) ha hb hab
    have hv := v.2.1.2 (σ.mem_Icc hx₁) (σ.mem_Icc hx₂) ha hb hab
    simp only [smul_eq_mul] at hc hv ⊢
    rw [hval _ hxl, hval _ hx₁, hval _ hx₂]
    have e : a * x₁ + b * x₂ - (a * σ.σ x₁ + b * σ.σ x₂) =
        a * (x₁ - σ.σ x₁) + b * (x₂ - σ.σ x₂) := by ring
    simp only [g, e] at hmin
    nlinarith [mul_le_mul_of_nonneg_left hv N.δ_pos.le]
  · refine ContinuousOn.congr ?_ hval
    exact (N.differentiable.continuous.comp_continuousOn (continuousOn_id.sub σ.continuousOn)).add
      (continuousOn_const.mul (v.2.2.1.comp σ.continuousOn fun x hx => σ.mem_Icc hx))
  · rw [hval x hx]
    have hm := σ.mem x hx
    have hb := v.2.2.2 _ (σ.mem_Icc hx)
    have ht := N.tangent_zero (sub_nonneg.2 hm.2)
    have hmin := isMinOn_iff.1 (N.greedy_isMinOn v.2 hx) 0 ⟨le_rfl, hx.1⟩
    simp only [g, sub_zero, v.1.2.2.1, mul_zero, add_zero] at hmin
    refine ⟨?_, hmin⟩
    nlinarith [N.deriv_zero_pos, N.one_lt_δ, mul_nonneg N.deriv_zero_pos.le hm.1,
      mul_le_mul_of_nonneg_left hb.1 N.δ_pos.le]

/-- The Bellman operator `T` on `V₀`, `Tv = T_σ v` for the `v`-min-greedy `σ`. -/
noncomputable def bellman (v : N.V0) : N.V0 := ⟨N.T (N.greedy v.2) v.1, N.T_greedy_mem v⟩

theorem bellman_apply (v : N.V0) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    (N.bellman v).1.1 x = N.g v.1.1 x ((N.greedy v.2).σ x) :=
  N.T_apply _ _ hx

theorem bellman_le (v : N.V0) {x y : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (hy : y ∈ Set.Icc 0 x) :
    (N.bellman v).1.1 x ≤ N.g v.1.1 x y := by
  rw [N.bellman_apply v hx]
  exact isMinOn_iff.1 (N.greedy_isMinOn v.2 hx) y hy

/-- `c` itself (on `[0, x̂]`) lies in `V₀`. -/
noncomputable def cV0 : N.V0 :=
  ⟨⟨(Set.Icc 0 N.xh).indicator N.c, fun x hx y hy hxy => by
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      exact N.c_mono hx.1 hxy, by
      rw [Set.indicator_of_mem N.zero_mem, N.c_zero], fun x hx => Set.indicator_of_notMem hx _⟩,
    ⟨(N.strictConvexOn.convexOn.subset Icc_subset_Ici_self (convex_Icc 0 N.xh)).congr
        fun x hx => (Set.indicator_of_mem hx _).symm,
      N.differentiable.continuous.continuousOn.congr fun x hx => Set.indicator_of_mem hx _,
      fun x hx => by
        change deriv N.c 0 * x ≤ (Set.Icc 0 N.xh).indicator N.c x ∧
          (Set.Icc 0 N.xh).indicator N.c x ≤ N.c x
        rw [Set.indicator_of_mem hx]
        exact ⟨N.tangent_zero hx.1, le_rfl⟩⟩⟩

/-- `T^k v` does not depend on `v ∈ V₀` on `[0, kη]` (Exercise 8.3.3). -/
theorem bellman_iterate_agree (v w : N.V0) (k : ℕ) {x : ℝ} (hxk : x ≤ k * N.η) :
    (N.bellman^[k] v).1.1 x = (N.bellman^[k] w).1.1 x := by
  induction k generalizing x with
  | zero =>
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · have : x = 0 := le_antisymm (by simpa using hxk) hx.1
      rw [this, iterate_zero, id, id, v.1.2.2.1, w.1.2.2.1]
    · rw [(N.bellman^[0] v).1.2.2.2 x hx, (N.bellman^[0] w).1.2.2.2 x hx]
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · have key : ∀ p q : N.V0, (∀ z, z ≤ k * N.η → p.1.1 z = q.1.1 z) →
          (N.bellman p).1.1 x ≤ (N.bellman q).1.1 x := fun p q hpq => by
        rw [N.bellman_apply q hx]
        refine (N.bellman_le p hx ((N.greedy q.2).mem x hx)).trans (le_of_eq ?_)
        simp only [g]
        rw [hpq]
        refine ((N.greedy q.2).le_max_sub hx).trans
          (max_le (mul_nonneg (Nat.cast_nonneg k) N.η_pos.le) ?_)
        push_cast at hxk
        linarith
      exact le_antisymm (key _ _ fun z hz => ih hz) (key _ _ fun z hz => (ih hz).symm)
    · rw [(N.bellman _).1.2.2.2 x hx, (N.bellman _).1.2.2.2 x hx]

theorem bellman_iterate_k0 (v w : N.V0) : N.bellman^[N.k0] v = N.bellman^[N.k0] w := by
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  by_cases hx : x ∈ Set.Icc 0 N.xh
  · refine N.bellman_iterate_agree v w N.k0 (hx.2.trans ?_)
    have : N.xh / N.η ≤ N.k0 := Nat.le_ceil _
    rwa [div_le_iff₀ N.η_pos] at this
  · rw [(N.bellman^[N.k0] v).1.2.2.2 x hx, (N.bellman^[N.k0] w).1.2.2.2 x hx]

/-- **Lemma 8.3.5** (p. 280) and **Exercise 8.3.3**: `T` maps `V₀` into itself and has a unique
fixed point `v̄` in `V₀`; moreover `T^k v = v̄` for all `v ∈ V₀` and `k ≥ k₀ = ⌈x̂/η⌉`. -/
theorem lemma_8_3_5 : ∃ vbar : N.V0, N.bellman vbar = vbar ∧
    (∀ q, N.bellman q = q → q = vbar) ∧ ∀ v k, N.k0 ≤ k → N.bellman^[k] v = vbar := by
  have hfix : N.bellman (N.bellman^[N.k0] N.cV0) = N.bellman^[N.k0] N.cV0 := by
    rw [← iterate_succ_apply' N.bellman, iterate_succ_apply, N.bellman_iterate_k0 _ N.cV0]
  refine ⟨_, hfix, fun q hq => ?_, fun v k hk => ?_⟩
  · rw [← N.bellman_iterate_k0 q N.cV0]
    exact (iterate_fixed hq _).symm
  · rw [← Nat.sub_add_cancel hk, iterate_add_apply, N.bellman_iterate_k0 _ N.cV0]
    exact iterate_fixed hfix _

theorem exercise_8_3_3 : ∃ vbar : N.V0, N.bellman vbar = vbar ∧
    (∀ q, N.bellman q = q → q = vbar) ∧ ∀ v k, N.k0 ≤ k → N.bellman^[k] v = vbar :=
  N.lemma_8_3_5

/-! ### Optimality (Theorem 8.3.6) -/

/-- **Theorem 8.3.6** (p. 280): the fundamental min-optimality properties hold for `(V, 𝕋)`; the
unique fixed point `v̄` of `T` in `V₀` is the min-value function `v▿*`; a policy is optimal iff
`σ(x) ∈ argmin_{a ≤ x} {c(x − a) + δv▿*(a)}` for all `x`; and there is exactly one optimal
policy. -/
theorem theorem_8_3_6 : ∃ vbar : N.V0, N.bellman vbar = vbar ∧
    N.adp.MinFundamentalOptimality N.isOrderStable.wellPosed ∧
    N.adp.IsMinValueFunction vbar.1 ∧
    (∀ σ, N.adp.IsMinOptimal N.isOrderStable.wellPosed σ ↔
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g vbar.1.1 x) (Set.Icc 0 x) (σ.σ x)) ∧
    ∃! σ, N.adp.IsMinOptimal N.isOrderStable.wellPosed σ := by
  obtain ⟨vbar, hfix, -, -⟩ := N.lemma_8_3_5
  obtain ⟨hg, hglb, -⟩ := N.lemma_8_3_4 vbar.1 vbar.2
  have hT : N.adp.T (N.greedy vbar.2) vbar.1 = vbar.1 := congrArg Subtype.val hfix
  have hsolve : N.adp.SolvesMinBellman vbar.1 := by
    rw [hT] at hglb
    exact hglb
  have hVG : vbar.1 ∈ N.adp.VGmin := ⟨_, hg⟩
  have hMFO := N.isOrderStable.minFundamentalOptimality hVG hsolve
  obtain ⟨⟨σo, hσo⟩, ⟨v, hvmin, -, -, huniq⟩, hBP⟩ := hMFO
  have hveq : vbar.1 = v := huniq vbar.1 hVG hsolve
  subst hveq
  have hchar : ∀ σ, N.adp.IsMinGreedy vbar.1 σ ↔
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g vbar.1.1 x) (Set.Icc 0 x) (σ.σ x) := fun σ => by
    constructor
    · intro h x hx
      refine isMinOn_iff.2 fun y hy => ?_
      have h1 : (N.T σ vbar.1).1 x ≤ (N.T (N.greedy vbar.2) vbar.1).1 x := h _ x
      rw [N.T_apply _ _ hx, N.T_apply _ _ hx] at h1
      exact h1.trans (isMinOn_iff.1 (N.greedy_isMinOn vbar.2 hx) y hy)
    · intro h τ x
      change (N.T σ vbar.1).1 x ≤ (N.T τ vbar.1).1 x
      by_cases hx : x ∈ Set.Icc 0 N.xh
      · rw [N.T_apply _ _ hx, N.T_apply _ _ hx]
        exact isMinOn_iff.1 (h x hx) _ (τ.mem x hx)
      · rw [(N.T σ vbar.1).2.2.2 x hx, (N.T τ vbar.1).2.2.2 x hx]
  have hopt : ∀ σ, N.adp.IsMinOptimal N.isOrderStable.wellPosed σ ↔
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g vbar.1.1 x) (Set.Icc 0 x) (σ.σ x) := fun σ => by
    rw [hBP σ, ← hchar σ]
    constructor
    · rintro ⟨w, hw, hgw⟩
      rw [hw.unique hvmin] at hgw
      exact hgw
    · exact fun h => ⟨_, hvmin, h⟩
  refine ⟨vbar, hfix, ⟨⟨σo, hσo⟩, ⟨vbar.1, hvmin, hVG, hsolve, huniq⟩, hBP⟩, hvmin, hopt,
    σo, hσo, fun σ hσ => ?_⟩
  have h1 := (hopt σ).1 hσ
  have h2 := (hopt σo).1 hσo
  refine Policy.ext (funext fun x => ?_)
  by_cases hx : x ∈ Set.Icc 0 N.xh
  · exact N.unique_min vbar.2 hx (σ.mem x hx) (σo.mem x hx) (h1 x hx) (h2 x hx)
  · rw [σ.zero_outside x hx, σo.zero_outside x hx]

end NegDiscount

/-! ### The production chain (§8.3.1.1) -/

/-- The firm boundaries `t₀ = 1`, `tᵢ = tᵢ₋₁ − aᵢ` of an allocation. Firm `i + 1` in the book's
indexing carries out the range `a i`, from `boundary a (i + 1)` up to `boundary a i`. -/
def boundary (a : ℕ → ℝ) (i : ℕ) : ℝ := 1 - ∑ j ∈ Finset.range i, a j

/-- **Definition 8.3.1** (p. 275): `(p, A)` is an equilibrium for the production chain when `A` is
feasible (nonnegative, finitely many firms complete the good), (i) `p(0) = 0`, (ii) every firm
makes zero profit (8.47), and (iii) `p(s) − c(s − t) − δp(t) ≤ 0` for `0 ≤ t ≤ s ≤ 1`. -/
def IsChainEquilibrium (c : ℝ → ℝ) (δ : ℝ) (p : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ((∀ i, 0 ≤ a i) ∧ ∃ I, ∑ i ∈ Finset.range I, a i = 1) ∧ p 0 = 0 ∧
    (∀ i, p (boundary a i) - c (a i) - δ * p (boundary a (i + 1)) = 0) ∧
    ∀ s t, 0 ≤ t → t ≤ s → s ≤ 1 → p s - c (s - t) - δ * p t ≤ 0

/-- The production chain of §8.3.1.1: processing cost `c` (increasing, strictly convex, `C¹`,
`c(0) = 0 < c'(0)`) and transaction cost `δ > 1`. -/
structure ProductionChain where
  /-- the processing cost -/
  c : ℝ → ℝ
  /-- the transaction cost markup -/
  δ : ℝ
  one_lt_δ : 1 < δ
  c_zero : c 0 = 0
  differentiable : Differentiable ℝ c
  continuous_deriv : Continuous (deriv c)
  strictConvexOn : StrictConvexOn ℝ (Ici 0) c
  strictMonoOn : StrictMonoOn c (Ici 0)
  deriv_zero_pos : 0 < deriv c 0

namespace ProductionChain

variable (C : ProductionChain)

/-- A threshold `η` as in `NegDiscount.η_spec` always exists on `[0, 1]`: the solution of
`c'(η) = δc'(0)` when `δc'(0) ≤ c'(1)` (intermediate value theorem), and `η = 1` otherwise. -/
theorem exists_η : ∃ η, 0 < η ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, deriv C.c x ≤ C.δ * deriv C.c 0 ↔ x ≤ η := by
  have hmono := C.strictConvexOn.strictMonoOn_deriv fun x _ => C.differentiable x
  have hd0 : deriv C.c 0 < C.δ * deriv C.c 0 := lt_mul_left C.deriv_zero_pos C.one_lt_δ
  by_cases h : C.δ * deriv C.c 0 ≤ deriv C.c 1
  · obtain ⟨η, hη, heq⟩ :=
      intermediate_value_Icc zero_le_one C.continuous_deriv.continuousOn ⟨hd0.le, h⟩
    have hη0 : 0 < η := by
      rcases hη.1.eq_or_lt with h0 | h0
      · rw [← h0] at heq
        linarith
      · exact h0
    refine ⟨η, hη0, fun x hx => ?_⟩
    rw [← heq]
    exact hmono.le_iff_le (mem_Ici.2 hx.1) (mem_Ici.2 hη.1)
  · refine ⟨1, one_pos, fun x hx => ⟨fun _ => hx.2, fun _ => ?_⟩⟩
    exact (hmono.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 zero_le_one) hx.2).trans
      (not_le.1 h).le

/-- The negative-discounting problem with `x̂ = 1` whose value function is the equilibrium price
function. -/
noncomputable def toNeg : NegDiscount where
  c := C.c
  δ := C.δ
  one_lt_δ := C.one_lt_δ
  xh := 1
  xh_pos := one_pos
  η := C.exists_η.choose
  η_pos := C.exists_η.choose_spec.1
  c_zero := C.c_zero
  differentiable := C.differentiable
  continuous_deriv := C.continuous_deriv
  strictConvexOn := C.strictConvexOn
  strictMonoOn := C.strictMonoOn
  deriv_zero_pos := C.deriv_zero_pos
  η_spec := C.exists_η.choose_spec.2

/-- **Proposition 8.3.1** (p. 275), by Lemma 8.3.5 with `x̂ = 1`, where `V₀ = 𝒫`: (i) the operator
`(Tp)(s) = min_{t ≤ s} {c(s − t) + δp(t)}` of (8.48) maps `𝒫` into itself, (ii) it has a unique
fixed point `p*` in `𝒫`, and (iii) `T^k p → p*` uniformly for every `p ∈ 𝒫` (indeed
`T^k p = p*` for `k ≥ k₀`). -/
theorem proposition_8_3_1 :
    (∀ p : C.toNeg.V0, ∀ s ∈ Set.Icc (0 : ℝ) 1, IsLeast
      ((fun t => C.c (s - t) + C.δ * p.1.1 t) '' Set.Icc 0 s) ((C.toNeg.bellman p).1.1 s)) ∧
    ∃ pstar : C.toNeg.V0, C.toNeg.bellman pstar = pstar ∧
      (∀ q, C.toNeg.bellman q = q → q = pstar) ∧
      ∀ p : C.toNeg.V0,
        TendstoUniformly (fun k => (C.toNeg.bellman^[k] p).1.1) pstar.1.1 atTop := by
  obtain ⟨pstar, hfix, huniq, hconv⟩ := C.toNeg.lemma_8_3_5
  refine ⟨fun p s hs => ⟨⟨_, (C.toNeg.greedy p.2).mem s hs,
    (C.toNeg.bellman_apply p hs).symm⟩, ?_⟩, pstar, hfix, huniq, fun p => ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact C.toNeg.bellman_le p hs ht
  · refine Metric.tendstoUniformly_iff.2 fun ε hε => eventually_atTop.2 ⟨C.toNeg.k0,
      fun n hn x => ?_⟩
    rw [hconv p n hn, dist_self]
    exact hε

/-- **Proposition 8.3.2** (p. 276): with `t*` the equilibrium choice function (8.49) and
`t*_i = t*(t*_{i−1})`, `t*_0 = 1` (8.50), the number of firms `n* = inf{i : t*_i = 0}` is
well-defined and finite, and `(p*, A*)` with `a*_i = t*_{i−1} − t*_i` is an equilibrium. -/
theorem proposition_8_3_2 : ∃ pstar : C.toNeg.V0, C.toNeg.bellman pstar = pstar ∧
    (∃ n, (C.toNeg.greedy pstar.2).σ^[n] 1 = 0 ∧ ∀ i < n, (C.toNeg.greedy pstar.2).σ^[i] 1 ≠ 0) ∧
    IsChainEquilibrium C.c C.δ pstar.1.1
      (fun i => (C.toNeg.greedy pstar.2).σ^[i] 1 - (C.toNeg.greedy pstar.2).σ^[i + 1] 1) := by
  classical
  obtain ⟨pstar, hfix, -, -⟩ := C.toNeg.lemma_8_3_5
  refine ⟨pstar, hfix, ?_⟩
  set σ := C.toNeg.greedy pstar.2
  have h1 : (1 : ℝ) ∈ Set.Icc 0 C.toNeg.xh := ⟨zero_le_one, le_rfl⟩
  have hex : ∃ n, σ.σ^[n] 1 = 0 := ⟨_, σ.iterate_eq_zero h1 le_rfl⟩
  have hp : ∀ x ∈ Set.Icc 0 C.toNeg.xh,
      pstar.1.1 x = C.c (x - σ.σ x) + C.δ * pstar.1.1 (σ.σ x) := fun x hx =>
    calc pstar.1.1 x = (C.toNeg.bellman pstar).1.1 x := by rw [hfix]
      _ = _ := C.toNeg.bellman_apply pstar hx
  have hle : ∀ s t, 0 ≤ t → t ≤ s → s ≤ 1 → pstar.1.1 s ≤ C.c (s - t) + C.δ * pstar.1.1 t :=
    fun s t ht hts hs1 =>
    calc pstar.1.1 s = (C.toNeg.bellman pstar).1.1 s := by rw [hfix]
      _ ≤ _ := C.toNeg.bellman_le pstar ⟨ht.trans hts, hs1⟩ ⟨ht, hts⟩
  have hb : ∀ i, boundary (fun i => σ.σ^[i] 1 - σ.σ^[i + 1] 1) i = σ.σ^[i] 1 := fun i => by
    rw [boundary, Finset.sum_range_sub' (fun i => σ.σ^[i] 1), iterate_zero, id]
    ring
  refine ⟨⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩,
    ⟨fun i => ?_, Nat.find hex, ?_⟩, pstar.1.2.2.1, fun i => ?_, fun s t ht hts hs1 => ?_⟩
  · change 0 ≤ σ.σ^[i] 1 - σ.σ^[i + 1] 1
    rw [iterate_succ_apply']
    exact sub_nonneg.2 (σ.mem _ (σ.iterate_mem h1 i)).2
  · rw [Finset.sum_range_sub' (fun i => σ.σ^[i] 1), Nat.find_spec hex, iterate_zero, id, sub_zero]
  · beta_reduce
    rw [hb, hb, iterate_succ_apply', hp _ (σ.iterate_mem h1 i)]
    ring
  · linarith [hle s t ht hts hs1]

end ProductionChain

end SargentStachurski.AdditionalApplications
