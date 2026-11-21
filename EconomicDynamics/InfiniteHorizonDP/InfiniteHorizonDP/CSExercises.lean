/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.CSDifferentiable

/-!
# Exercises 6.5–6.7: the consumption-saving problem with iid income, Markov income and
# random returns

Copied from `EconomicDynamics/FiniteHorizonDP` (module `CSExercises`), namespace renamed.

Miao, §6.6.2, pp. 186–189 and Exercises 5–7, pp. 189–190, as instances of `CSModel`.

* `bookModel`: §6.6.2 with iid income `y ∈ [y_min, y_max]` drawn from `μ`, cash on hand
  `x′ = R s + y′ − rb`, `r = R − 1`. The standing hypotheses hold when `u` is continuous,
  strictly increasing and strictly concave on `[0, ∞)`, `β, R > 0` and `y_min − rb > 0`
  (`bookModel_basic`). With iid income the value functions do not depend on the current shock
  (`v_indep`), so the state is `x` alone, as the book says.
* **Exercise 6.5** (the properties of p. 188 and the comparison of p. 189): `ex_6_5_value`,
  `ex_6_5_v_deriv_mono`, `ex_6_5_policy_x`, `ex_6_5_policy_n`, `ex_6_5_foc`, `ex_6_5_compare`;
  the corrections `ex_6_5_sav_not_strict` and `ex_6_5_n_not_strict`.
* **Exercise 6.6** (`markovModel`, `ex_6_6`): Markov income on a compact state space with a Feller
  transition `Q`; the state is `(x, z)` and all the properties hold for each current income
  state, including the comparisons with the lowest and highest income paths.
* **Exercise 6.7** (Phelps 1962; `phelpsModel`, `ex_6_7`): `b = 0`, constant income `y > 0`,
  iid gross return `R′ ∈ [R_min, R_max]`, `R_min > 0`, so `x′ = R′ s + y`. All the properties
  except the comparisons hold.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace CSModel

variable {Z : Type*} [MeasurableSpace Z]

/-- With iid shocks (`Q(z, ·)` independent of `z`) the value functions do not depend on the
current shock (Miao, p. 188: one state variable `x_t` instead of `(a_t, y_t)`). -/
theorem v_indep (M : CSModel Z) (hQ : ∀ z z', M.Q z = M.Q z') (n : ℕ) (x : ℝ) (z z' : Z) :
    M.v n x z = M.v n x z' := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [v_succ, v_succ]
    congr 2
    funext s
    simp only [obj, hQ z z']

end CSModel

/-- **The consumption-saving model of §6.6.2** (Miao, p. 187): iid income `y` with distribution
`μ` on `[y_min, y_max]`, `x′ = R s + y′ − rb` with `r = R − 1`. -/
noncomputable def bookModel (u : ℝ → ℝ) (β R b ymin ymax : ℝ) (μ : Measure (Set.Icc ymin ymax)) :
    CSModel (Set.Icc ymin ymax) where
  u := u
  β := β
  Q := Kernel.const _ μ
  ρ := fun _ => R
  w := fun y => y.1 - (R - 1) * b

/-- The assumptions on `u` in §6.6.2 (p. 187), in the form used here: continuous, strictly
increasing and strictly concave on `[0, ∞)`, differentiable on `(0, ∞)`, `u′(0+) = ∞`. -/
structure CSUtility (u : ℝ → ℝ) : Prop where
  cont : ContinuousOn u (Set.Ici 0)
  mono : StrictMonoOn u (Set.Ici 0)
  conc : StrictConcaveOn ℝ (Set.Ici 0) u
  diff : ∀ c, 0 < c → DifferentiableAt ℝ u c
  inada : Tendsto (deriv u) (𝓝[>] 0) atTop

variable {u : ℝ → ℝ} {β R b ymin ymax : ℝ} {μ : Measure (Set.Icc ymin ymax)}

/-- The kernel of `bookModel` is Markov. -/
theorem bookModel_isMarkovKernel [IsProbabilityMeasure μ] :
    IsMarkovKernel (bookModel u β R b ymin ymax μ).Q := by
  change IsMarkovKernel (Kernel.const _ μ)
  infer_instance

/-- §6.6.2 satisfies the standing hypotheses when `β, R > 0` and `y_min − rb > 0`. -/
theorem bookModel_basic [IsProbabilityMeasure μ] (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) : (bookModel u β R b ymin ymax μ).Basic where
  β_pos := hβ
  u_cont := hu.cont
  u_mono := hu.mono
  u_conc := hu.conc
  ρ_cont := continuous_const
  ρ_pos := fun _ => hR
  w_cont := continuous_subtype_val.sub continuous_const
  w_pos := fun y => by
    change 0 < y.1 - (R - 1) * b
    linarith [y.2.1]
  feller := CSModel.isFeller_const μ

variable [IsProbabilityMeasure μ]

/-- **Exercise 6.5: the value functions** (Miao, p. 188). For §6.6.2, `v_n` is strictly
increasing and strictly concave on `[0, ∞)`, continuously differentiable on `(0, ∞)` with
`v_n′(x) = u′(g_n(x))`, and for `n ≥ 1` the optimal saving `s_n(x) ∈ [0, x]` exists and is the
unique maximizer. -/
theorem ex_6_5_value (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    StrictMonoOn (fun x => (bookModel u β R b ymin ymax μ).v n x z) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun x => (bookModel u β R b ymin ymax μ).v n x z) ∧
      (∀ x, 0 < x → HasDerivAt (fun y => (bookModel u β R b ymin ymax μ).v n y z)
        (deriv u ((bookModel u β R b ymin ymax μ).cons n x z)) x) ∧
      ContinuousOn (deriv fun y => (bookModel u β R b ymin ymax μ).v n y z) (Set.Ioi 0) ∧
      ∀ x, 0 ≤ x → ∀ s ∈ Set.Icc 0 x,
        ((bookModel u β R b ymin ymax μ).obj n x z s =
          (bookModel u β R b ymin ymax μ).v (n + 1) x z ↔
          s = (bookModel u β R b ymin ymax μ).sav (n + 1) x z) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    fun x hx => CSModel.hasDerivAt_v h hs n z hx, CSModel.continuousOn_deriv_v h hs n z,
    fun x hx s hsx => ⟨CSModel.sav_unique h n hsx, fun he => ?_⟩⟩
  rw [he]
  exact (CSModel.sav_mem h n hx z).2

/-- **Exercise 6.5: `v_n′(x)` is increasing in `n`** (Miao, p. 188), weakly. -/
theorem ex_6_5_v_deriv_mono (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => (bookModel u β R b ymin ymax μ).v n y z) x ≤
      deriv (fun y => (bookModel u β R b ymin ymax μ).v (n + 1) y z) x := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  exact CSModel.deriv_v_le (bookModel_basic hu hβ hR hfloor) ⟨hu.diff, hu.inada⟩ n z hx

/-- **Exercise 6.5: `g_n` and `s_n` are continuous and increasing in `x`** (Miao, p. 188):
`g_n` strictly, `s_n` weakly (`ex_6_5_sav_not_strict`). -/
theorem ex_6_5_policy_x (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    ContinuousOn (fun x => (bookModel u β R b ymin ymax μ).cons n x z) (Set.Ici 0) ∧
      ContinuousOn (fun x => (bookModel u β R b ymin ymax μ).sav n x z) (Set.Ici 0) ∧
      StrictMonoOn (fun x => (bookModel u β R b ymin ymax μ).cons n x z) (Set.Ici 0) ∧
      MonotoneOn (fun x => (bookModel u β R b ymin ymax μ).sav n x z) (Set.Ici 0) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  have hz : Continuous fun x : ℝ => (x, z) := continuous_id.prodMk continuous_const
  refine ⟨(CSModel.continuousOn_cons h n).comp hz.continuousOn fun x hx => ⟨hx, Set.mem_univ _⟩,
    (CSModel.continuousOn_sav h n).comp hz.continuousOn fun x hx => ⟨hx, Set.mem_univ _⟩,
    CSModel.strictMonoOn_cons h hs n z, CSModel.monotoneOn_sav h n z⟩

/-- **Correction to Exercise 6.5:** for `n ≥ 1`, `s_n` is not strictly increasing: the borrowing
constraint binds, `s_n(x) = 0`, for all small `x > 0`. -/
theorem ex_6_5_sav_not_strict (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    (∃ xb > 0, ∀ x ∈ Set.Ioc 0 xb, (bookModel u β R b ymin ymax μ).sav (n + 1) x z = 0) ∧
      ¬ StrictMonoOn (fun x => (bookModel u β R b ymin ymax μ).sav (n + 1) x z) (Set.Ici 0) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  exact ⟨CSModel.exists_sav_eq_zero h ⟨hu.diff, hu.inada⟩ n z,
    CSModel.not_strictMonoOn_sav h ⟨hu.diff, hu.inada⟩ n z⟩

/-- **Exercise 6.5: `g_n(x)` is decreasing in `n` and `s_n(x)` increasing in `n`** (Miao,
p. 188), weakly, for `x > 0`. -/
theorem ex_6_5_policy_n (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 < x) :
    (bookModel u β R b ymin ymax μ).cons (n + 1) x z ≤ (bookModel u β R b ymin ymax μ).cons n x z ∧
      (bookModel u β R b ymin ymax μ).sav n x z ≤
        (bookModel u β R b ymin ymax μ).sav (n + 1) x z := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  exact ⟨CSModel.cons_succ_le h ⟨hu.diff, hu.inada⟩ n z x hx,
    CSModel.sav_le_sav_succ h ⟨hu.diff, hu.inada⟩ n z hx⟩

/-- **Correction to Exercise 6.5:** the monotonicity in `n` is not strict: there are `x > 0`
with `g_{n+2}(x) = g_{n+1}(x)`, and with `g_1(x) = g_0(x)` (so also `v_1′(x) = v_0′(x)`). -/
theorem ex_6_5_n_not_strict (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) :
    (∃ x > 0, (bookModel u β R b ymin ymax μ).cons (n + 2) x z =
      (bookModel u β R b ymin ymax μ).cons (n + 1) x z) ∧
      ∃ x > 0, (bookModel u β R b ymin ymax μ).cons 1 x z =
        (bookModel u β R b ymin ymax μ).cons 0 x z := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  exact CSModel.exists_cons_succ_eq (bookModel_basic hu hβ hR hfloor) ⟨hu.diff, hu.inada⟩ n z

/-- **Exercise 6.5: the first-order and envelope conditions** (Miao, p. 188): for `x > 0`,
`v_{n+1}′(x) = u′(g_{n+1}(x)) ≥ βR E v_n′(R s_{n+1}(x) + y − rb)`, with equality if
`s_{n+1}(x) > 0`. -/
theorem ex_6_5_foc (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (n : ℕ) (z : Set.Icc ymin ymax) {x : ℝ} (hx : 0 < x) :
    deriv (fun y => (bookModel u β R b ymin ymax μ).v (n + 1) y z) x =
        deriv u ((bookModel u β R b ymin ymax μ).cons (n + 1) x z) ∧
      β * R * ∫ y', deriv (fun x' => (bookModel u β R b ymin ymax μ).v n x' y')
          (R * (bookModel u β R b ymin ymax μ).sav (n + 1) x z + y'.1 - (R - 1) * b) ∂μ ≤
        deriv u ((bookModel u β R b ymin ymax μ).cons (n + 1) x z) ∧
      (0 < (bookModel u β R b ymin ymax μ).sav (n + 1) x z →
        deriv u ((bookModel u β R b ymin ymax μ).cons (n + 1) x z) =
          β * R * ∫ y', deriv (fun x' => (bookModel u β R b ymin ymax μ).v n x' y')
            (R * (bookModel u β R b ymin ymax μ).sav (n + 1) x z + y'.1 - (R - 1) * b) ∂μ) := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  set M := bookModel u β R b ymin ymax μ
  have hev : ∀ s, M.β * M.evd n z s =
      β * R * ∫ y', deriv (fun x' => M.v n x' y') (R * s + y'.1 - (R - 1) * b) ∂μ := by
    intro s
    change β * ∫ y', deriv (fun x' => M.v n x' y') (R * s + (y'.1 - (R - 1) * b)) * R ∂μ = _
    rw [integral_mul_const]
    simp only [add_sub_assoc]
    ring
  obtain ⟨f1, f2⟩ := CSModel.foc h hs n hx z
  rw [hev] at f1 f2
  exact ⟨CSModel.deriv_v h hs (n + 1) z hx, f1, f2⟩

/-- **The comparison of p. 189** (Exercise 6.5): `c_t(x; y_max) ≥ c_t(x) ≥ c_t(x; y_min)`, with
`c_t = g_{T−t}` and `c_t(x; y)` the consumption policy when income is `y` in every period
(`detModel`). -/
theorem ex_6_5_compare (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hfloor : 0 < ymin - (R - 1) * b) (hy : ymin ≤ ymax) (n : ℕ) (z z'' : Set.Icc ymin ymax)
    {x : ℝ} (hx : 0 < x) :
    ((bookModel u β R b ymin ymax μ).detModel ⟨ymin, le_rfl, hy⟩).cons n x z'' ≤
        (bookModel u β R b ymin ymax μ).cons n x z ∧
      (bookModel u β R b ymin ymax μ).cons n x z ≤
        ((bookModel u β R b ymin ymax μ).detModel ⟨ymax, hy, le_rfl⟩).cons n x z'' := by
  have := bookModel_isMarkovKernel (u := u) (β := β) (R := R) (b := b) (μ := μ)
  have h := bookModel_basic (μ := μ) hu hβ hR hfloor
  have hs : (bookModel u β R b ymin ymax μ).Smooth := ⟨hu.diff, hu.inada⟩
  refine ⟨CSModel.cons_ge_low h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx,
    CSModel.cons_le_high h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx⟩
  · change ymin - (R - 1) * b ≤ z'.1 - (R - 1) * b
    linarith [z'.2.1]
  · change z'.1 - (R - 1) * b ≤ ymax - (R - 1) * b
    linarith [z'.2.2]

/-! ### Exercise 6.6: Markov income -/

/-- **Exercise 6.6** (Miao, p. 190): the problem of §6.6.2 with Markov income `y(z)`, `z ∈ Z`
following `Q`. The state is `(x, z)` with `x = Ra + y(z) + b`; next period
`x′ = R s + y(z′) − rb`. -/
def markovModel {Z : Type*} [MeasurableSpace Z] (u : ℝ → ℝ) (β R b : ℝ) (y : Z → ℝ)
    (Q : Kernel Z Z) : CSModel Z where
  u := u
  β := β
  Q := Q
  ρ := fun _ => R
  w := fun z => y z - (R - 1) * b

/-- **Exercise 6.6** (Miao, p. 190). For Markov income on a compact metric state space `Z`
(Feller `Q`, continuous income `y`, cash floor `y(z) − rb > 0`), for each current state `z`:
`v_n(·, z)` is strictly increasing, strictly concave and `C¹` on `(0, ∞)` with
`v_n′ = u′ ∘ g_n`; `g_n(·, z)` is strictly increasing and `s_n(·, z)` increasing; the first-order
condition holds with `E` the conditional expectation `∫ Q(z, dz′)`; `g_n` is decreasing and `s_n`
increasing in `n`; and consumption lies between the policies for the constant income paths at
the lowest and highest income states. -/
theorem ex_6_6 {Z : Type*} [MeasurableSpace Z] [MetricSpace Z] [CompactSpace Z] [BorelSpace Z]
    {y : Z → ℝ} {Q : Kernel Z Z} [IsMarkovKernel Q] (hu : CSUtility u) (hβ : 0 < β) (hR : 0 < R)
    (hy : Continuous y) (hfloor : ∀ z, 0 < y z - (R - 1) * b) (hQ : IsFeller Q) {zlo zhi : Z}
    (hlo : ∀ z, y zlo ≤ y z) (hhi : ∀ z, y z ≤ y zhi) (n : ℕ) (z : Z) :
    StrictMonoOn (fun x => (markovModel u β R b y Q).v n x z) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun x => (markovModel u β R b y Q).v n x z) ∧
      ContinuousOn (deriv fun x => (markovModel u β R b y Q).v n x z) (Set.Ioi 0) ∧
      (∀ x, 0 < x → deriv (fun x' => (markovModel u β R b y Q).v n x' z) x =
        deriv u ((markovModel u β R b y Q).cons n x z)) ∧
      StrictMonoOn (fun x => (markovModel u β R b y Q).cons n x z) (Set.Ici 0) ∧
      MonotoneOn (fun x => (markovModel u β R b y Q).sav n x z) (Set.Ici 0) ∧
      (∀ x, 0 < x →
        β * (markovModel u β R b y Q).evd n z ((markovModel u β R b y Q).sav (n + 1) x z) ≤
          deriv u ((markovModel u β R b y Q).cons (n + 1) x z) ∧
        (0 < (markovModel u β R b y Q).sav (n + 1) x z →
          deriv u ((markovModel u β R b y Q).cons (n + 1) x z) =
            β * (markovModel u β R b y Q).evd n z ((markovModel u β R b y Q).sav (n + 1) x z))) ∧
      (∀ x, 0 < x → (markovModel u β R b y Q).cons (n + 1) x z ≤
        (markovModel u β R b y Q).cons n x z) ∧
      ∀ x, 0 < x → ∀ z'', ((markovModel u β R b y Q).detModel zlo).cons n x z'' ≤
        (markovModel u β R b y Q).cons n x z ∧
        (markovModel u β R b y Q).cons n x z ≤ ((markovModel u β R b y Q).detModel zhi).cons n x z''
      := by
  have : IsMarkovKernel (markovModel u β R b y Q).Q := ‹IsMarkovKernel Q›
  have h : (markovModel u β R b y Q).Basic :=
    ⟨hβ, hu.cont, hu.mono, hu.conc, continuous_const, fun _ => hR,
      hy.sub continuous_const, hfloor, hQ⟩
  have hs : (markovModel u β R b y Q).Smooth := ⟨hu.diff, hu.inada⟩
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    CSModel.continuousOn_deriv_v h hs n z, fun x hx => CSModel.deriv_v h hs n z hx,
    CSModel.strictMonoOn_cons h hs n z, CSModel.monotoneOn_sav h n z,
    fun x hx => CSModel.foc h hs n hx z, fun x hx => CSModel.cons_succ_le h hs n z x hx,
    fun x hx z'' => ⟨CSModel.cons_ge_low h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx,
      CSModel.cons_le_high h hs (R := R) (fun _ => rfl) (fun z' => ?_) n z z'' x hx⟩⟩
  · change y zlo - (R - 1) * b ≤ y z' - (R - 1) * b
    linarith [hlo z']
  · change y z' - (R - 1) * b ≤ y zhi - (R - 1) * b
    linarith [hhi z']

/-! ### Exercise 6.7: Phelps (1962), random returns -/

/-- **Exercise 6.7** (Phelps 1962; Miao, p. 190): no borrowing (`b = 0`), constant income `y`,
iid gross return `R′ ∈ [R_min, R_max]` with distribution `ν`; `x′ = R′ s + y`. -/
noncomputable def phelpsModel (u : ℝ → ℝ) (β y Rmin Rmax : ℝ) (ν : Measure (Set.Icc Rmin Rmax)) :
    CSModel (Set.Icc Rmin Rmax) where
  u := u
  β := β
  Q := Kernel.const _ ν
  ρ := fun R' => R'.1
  w := fun _ => y

/-- **Exercise 6.7** (Phelps 1962; Miao, p. 190). With `R_min > 0` and `y > 0`: `v_n` is strictly
increasing, strictly concave and `C¹` on `(0, ∞)` with `v_n′ = u′ ∘ g_n`; the first-order
condition is `u′(g_{n+1}(x)) ≥ β E[R′ v_n′(R′ s_{n+1}(x) + y)]`, with equality if
`s_{n+1}(x) > 0`; `g_n` is strictly and `s_n` weakly increasing in `x`; the saving constraint
binds for small `x`; `g_n` is decreasing and `s_n` increasing in `n`. -/
theorem ex_6_7 {y Rmin Rmax : ℝ} {ν : Measure (Set.Icc Rmin Rmax)} [IsProbabilityMeasure ν]
    (hu : CSUtility u) (hβ : 0 < β) (hRmin : 0 < Rmin) (hy : 0 < y) (n : ℕ)
    (z : Set.Icc Rmin Rmax) :
    StrictMonoOn (fun x => (phelpsModel u β y Rmin Rmax ν).v n x z) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (fun x => (phelpsModel u β y Rmin Rmax ν).v n x z) ∧
      ContinuousOn (deriv fun x => (phelpsModel u β y Rmin Rmax ν).v n x z) (Set.Ioi 0) ∧
      (∀ x, 0 < x → deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' z) x =
        deriv u ((phelpsModel u β y Rmin Rmax ν).cons n x z)) ∧
      (∀ x, 0 < x →
        β * ∫ R', R'.1 * deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R')
            (R'.1 * (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z + y) ∂ν ≤
          deriv u ((phelpsModel u β y Rmin Rmax ν).cons (n + 1) x z) ∧
        (0 < (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z →
          deriv u ((phelpsModel u β y Rmin Rmax ν).cons (n + 1) x z) =
            β * ∫ R', R'.1 * deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R')
              (R'.1 * (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z + y) ∂ν)) ∧
      StrictMonoOn (fun x => (phelpsModel u β y Rmin Rmax ν).cons n x z) (Set.Ici 0) ∧
      MonotoneOn (fun x => (phelpsModel u β y Rmin Rmax ν).sav n x z) (Set.Ici 0) ∧
      (∃ xb > 0, ∀ x ∈ Set.Ioc 0 xb, (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z = 0) ∧
      ∀ x, 0 < x → (phelpsModel u β y Rmin Rmax ν).cons (n + 1) x z ≤
          (phelpsModel u β y Rmin Rmax ν).cons n x z ∧
        (phelpsModel u β y Rmin Rmax ν).sav n x z ≤ (phelpsModel u β y Rmin Rmax ν).sav (n + 1) x z
      := by
  have : IsMarkovKernel (phelpsModel u β y Rmin Rmax ν).Q := by
    change IsMarkovKernel (Kernel.const _ ν)
    infer_instance
  have h : (phelpsModel u β y Rmin Rmax ν).Basic :=
    ⟨hβ, hu.cont, hu.mono, hu.conc, continuous_subtype_val, fun R' => hRmin.trans_le R'.2.1,
      continuous_const, fun _ => hy, CSModel.isFeller_const ν⟩
  have hs : (phelpsModel u β y Rmin Rmax ν).Smooth := ⟨hu.diff, hu.inada⟩
  have hev : ∀ s, (phelpsModel u β y Rmin Rmax ν).evd n z s =
      ∫ R', R'.1 * deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R') (R'.1 * s + y) ∂ν :=
    fun s => by
      change ∫ R', deriv (fun x' => (phelpsModel u β y Rmin Rmax ν).v n x' R') (R'.1 * s + y) *
        R'.1 ∂ν = _
      simp only [mul_comm]
  refine ⟨CSModel.strictMonoOn_v h n z, CSModel.strictConcaveOn_v h n z,
    CSModel.continuousOn_deriv_v h hs n z, fun x hx => CSModel.deriv_v h hs n z hx,
    fun x hx => ?_, CSModel.strictMonoOn_cons h hs n z, CSModel.monotoneOn_sav h n z,
    CSModel.exists_sav_eq_zero h hs n z, fun x hx => ⟨CSModel.cons_succ_le h hs n z x hx,
      CSModel.sav_le_sav_succ h hs n z hx⟩⟩
  obtain ⟨f1, f2⟩ := CSModel.foc h hs n hx z
  rw [hev] at f1 f2
  exact ⟨f1, f2⟩

end Miao.InfiniteHorizonDP
