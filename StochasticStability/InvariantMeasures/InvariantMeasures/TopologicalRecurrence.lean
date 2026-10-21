/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvariantMeasures.NonEvanescence

/-!
# Topologically recurrent and transient states (MT §9.3)

Meyn and Tweedie, §9.3, pp. 208–213.

**Definitions** (p. 208). For a point `x*`:
* `IsTopRecurrent P x*`: `U(x*, O) = ∞` for every open neighbourhood `O` of `x*`;
  `IsTopTransient`: not topologically recurrent;
* `IsTopHarrisRecurrent P x*`: `Q(x*, O) = 1` for every open neighbourhood `O`
  (`IsTopHarrisRecurrent.isTopRecurrent`).

**Tools.**
* `occTime_split`, `occTime_le_add_shift`: `η_A = η_A^m + η_A ∘ θᵐ ≤ m + η_A ∘ θᵐ`;
  `occTime_le_shift_of_firstReturn`: on `{τ_O = m}` with `Φₘ ∉ O' ⊆ O`, `η_{O'} ≤ η_O ∘ θᵐ`.
* `measurableSet_stoppedField_stoppedState`: `{Φ_ζ ∈ B} ∈ 𝓕_ζ`.
* `isUniformlyTransient_of_occTime_ge` ((8.35)): `P_y(η_D ≥ k) ≤ 1 − c < 1` on `D` makes `D`
  uniformly transient.
* `exists_uniformlyTransient_nhds_of_infty`: the core of Proposition 9.3.4, (9.25)–(9.29).

**Results.**
* **Proposition 9.3.1** (`proposition_9_3_1`, p. 208): `x*` is topologically Harris recurrent iff
  `L(x*, O) = 1` for every open neighbourhood `O` (`T₁`, first countable).
* **Lemma 9.3.2** (`lemma_9_3_2`, p. 209): if `T(x*, B) > 0` for a continuous component `T` of
  `K_a`, some open `O ∋ x*` has `O ⇝ᵃ B` and `P_y(σ_B < ∞) ≥ δ > 0` on `O`.
* **Theorem 9.3.3** (`theorem_9_3_3`, p. 210): for a `ψ`-irreducible T-chain and a reachable
  `x*`, the chain is recurrent iff `x*` is topologically recurrent.
* **Proposition 9.3.4** (p. 211): (i) `proposition_9_3_4_i`, for a T-chain a topologically
  recurrent `x*` has `Q(x*, O) > 0` for every neighbourhood `O`; (ii) `proposition_9_3_4_ii`, if
  `P(x*, ·) ≪ T(x*, ·)` then `x*` is topologically Harris recurrent;
  `proposition_9_3_4_strongFeller`: for strong Feller chains topologically recurrent states are
  topologically Harris recurrent.
* **Theorem 9.3.5** (`theorem_9_3_5`, p. 212): for any chain on a second-countable `T₁` space,
  the set `N` of states that are not topologically Harris recurrent is transient.
* **Theorem 9.3.6** (`theorem_9_3_6`, p. 213), corrected: for a `ψ`-irreducible T-chain,
  `X = H ∪ N` as in Theorem 9.2.2, `R ⊆ H`, every `x* ∈ N` has an open neighbourhood `O` with
  `O ∩ N` uniformly transient, and every `x* ∈ N` with `T(x*, H) = 0` (in particular every state,
  when the chain is transient) is topologically transient.

**Corrections.**
* Lemma 9.3.2: "hence from Lemma 5.5.1, `O ⇝ B`" needs `a(0) = 0`. For the chain on `Bool` that
  jumps to `true`, `T = K_{δ₀} = I` is a continuous component (discrete topology) with
  `T(false, {false}) = 1`, but no neighbourhood `O` of `false` has `O ⇝ {false}`
  (`lemma_9_3_2_counterexample`). The statement proved replaces `L` by `P_y(σ_B < ∞)`, which is
  what Theorems 9.2.1, 9.3.3 and Proposition 9.3.4 use.
* Proposition 9.3.4: the proof's bound `P_x(τ_{Dₙ} ≤ m) > δ/2m` uses `L ≥ K_a`; here the first
  hitting time `σ_{Dₙ}` is used, and the bound is `P_x(σ_{Dₙ} ≤ m) ≥ ε`.
* Theorem 9.3.6: the claim that **every** state of `N` is topologically transient fails in
  general. The proof's set `O_δ = {T(·, H) > δ}` may meet `H`, and then it is not uniformly
  transient. `theorem_9_3_6_counterexample` (in `TopologicalExamples`) is a `ν`-irreducible
  T-chain on `ℕ∞ ⊕ ℕ` with a topologically recurrent state `x*` that lies in no maximal Harris
  set. What the proof does show is that `O_δ ∩ N` is uniformly transient; this, and topological
  transience when `T(x*, H) = 0`, are what `theorem_9_3_6` proves.
-/

namespace MeynTweedie.InvariantMeasures

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Occupation times along paths -/

omit [MeasurableSpace X] in
/-- `η_A = η_A^m + η_A ∘ θᵐ`. -/
theorem occTime_split (A : Set X) (m : ℕ) (ω : ℕ → X) :
    occTime A ω = occTimeN A m ω + occTime A (shift m ω) := by
  unfold occTime occTimeN
  rw [← Summable.sum_add_tsum_nat_add' (f := fun n => A.indicator 1 (ω (n + 1))) (k := m)
    ENNReal.summable]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [shift_apply]
  rw [show n + m + 1 = m + (n + 1) by omega]

omit [MeasurableSpace X] in
/-- `η_A ≤ m + η_A ∘ θᵐ`. -/
theorem occTime_le_add_shift (A : Set X) (m : ℕ) (ω : ℕ → X) :
    occTime A ω ≤ m + occTime A (shift m ω) := by
  rw [occTime_split A m ω]
  gcongr
  exact occTimeN_le A m ω

omit [MeasurableSpace X] in
/-- `η_A` is monotone in `A`. -/
theorem occTime_mono {A B : Set X} (h : A ⊆ B) (ω : ℕ → X) : occTime A ω ≤ occTime B ω :=
  ENNReal.tsum_le_tsum fun _ => indicator_le_indicator_of_subset h (fun _ => zero_le) _

omit [MeasurableSpace X] in
/-- On `{τ_O = m}` with `Φₘ ∉ O'` and `O' ⊆ O`, the visits to `O'` all happen after time `m`:
`η_{O'} ≤ η_O ∘ θᵐ`. -/
theorem occTime_le_shift_of_firstReturn {O O' : Set X} (hO' : O' ⊆ O) {ω : ℕ → X} {m : ℕ}
    (hm : firstReturn O ω = WithTop.some m) (hωm : ω m ∉ O') :
    occTime O' ω ≤ occTime O (shift m ω) := by
  rw [occTime_split O' m ω]
  have h0 : occTimeN O' m ω = 0 := by
    unfold occTimeN
    refine Finset.sum_eq_zero fun n hn => indicator_of_notMem (fun h => ?_) _
    rw [Finset.mem_range] at hn
    rcases Nat.lt_or_ge (n + 1) m with hlt | hge
    · exact (le_firstReturn_iff O ω m).1 hm.ge (n + 1) (by omega) hlt (hO' h)
    · rw [show n + 1 = m by omega] at h
      exact hωm h
  rw [h0, zero_add]
  exact occTime_mono hO' _

omit [MeasurableSpace X] in
/-- `Φ_{σ_B} ∈ B` on `{σ_B < ∞}`. -/
theorem stoppedState_firstHit_mem (B : Set X) {ω : ℕ → X} (hω : firstHit B ω ≠ ⊤) :
    stoppedState (firstHit B) ω ∈ B :=
  hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := B) (n := 0) hω

/-- `{Φ_ζ ∈ B} ∈ 𝓕_ζ^Φ`. -/
theorem measurableSet_stoppedField_stoppedState {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {B : Set X} (hB : MeasurableSet B) :
    MeasurableSet[hτ.measurableSpace] {ω | stoppedState τ ω ∈ B} := by
  rw [measurableSet_stoppedField_iff]
  refine ⟨measurable_stoppedState hτ hB, fun n => ?_⟩
  have : {ω | stoppedState τ ω ∈ B} ∩ {ω | τ ω = n} = {ω | ω n ∈ B} ∩ {ω | τ ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨stoppedState_of_eq h2 ▸ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(stoppedState_of_eq h2).symm ▸ h1, h2⟩
  rw [this]
  exact (measurableSet_coord_natFilt le_rfl hB).inter (hτ.measurableSet_eq_of_countable n)

/-- **(8.35)**: if `P_y(η_D ≥ k) ≤ 1 − c` for every `y ∈ D`, with `c > 0`, then `D` is uniformly
transient. -/
theorem isUniformlyTransient_of_occTime_ge (P : Kernel X X) [IsMarkovKernel P] {D : Set X}
    (hD : MeasurableSet D) (k : ℕ) {c : ℝ≥0∞} (hc : 0 < c)
    (h : ∀ y ∈ D, pathKernel P y {ω | (k : ℝ≥0∞) ≤ occTime D ω} ≤ 1 - c) :
    IsUniformlyTransient P D := by
  have hlt : 1 - c < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc.ne'
  have hret : ∀ x ∈ D, pathKernel P x {ω | returnTimeK D k ω ≠ ⊤} ≤ 1 - c := fun x hx =>
    (measure_mono fun ω hω => le_occTime_of_returnTimeK D k hω).trans (h x hx)
  obtain ⟨h1, -⟩ := proposition_8_3_1_iv P hD k hlt hret
  exact ⟨hD, (k : ℝ≥0∞) / (1 - (1 - c)), ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt hlt).ne', h1⟩

/-! ### Topological recurrence concepts -/

variable [TopologicalSpace X] in
/-- `x*` is **topologically recurrent** (MT p. 208) if `U(x*, O) = ∞` for every open
neighbourhood `O` of `x*`. -/
def IsTopRecurrent (P : Kernel X X) (x : X) : Prop :=
  ∀ O : Set X, IsOpen O → x ∈ O → potKernel P x O = ∞

variable [TopologicalSpace X] in
/-- `x*` is **topologically transient** (MT p. 208) if it is not topologically recurrent. -/
def IsTopTransient (P : Kernel X X) (x : X) : Prop := ¬ IsTopRecurrent P x

variable [TopologicalSpace X] in
/-- `x*` is **topologically Harris recurrent** (MT p. 208) if `Q(x*, O) = 1` for every open
neighbourhood `O` of `x*`. -/
def IsTopHarrisRecurrent (P : Kernel X X) [IsMarkovKernel P] (x : X) : Prop :=
  ∀ O : Set X, IsOpen O → x ∈ O → harrisQ P O x = 1

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- A topologically Harris recurrent state is topologically recurrent. -/
theorem IsTopHarrisRecurrent.isTopRecurrent {P : Kernel X X} [IsMarkovKernel P] {x : X}
    (h : IsTopHarrisRecurrent P x) : IsTopRecurrent P x := fun O hO hxO =>
  potKernel_eq_top_of_harrisQ_pos P hO.measurableSet (by rw [h O hO hxO]; exact one_pos)

/-! ### Proposition 9.3.1 -/

variable [TopologicalSpace X] [T1Space X] [FirstCountableTopology X] [OpensMeasurableSpace X] in
/-- **Proposition 9.3.1** (MT p. 208): `x*` is topologically Harris recurrent iff `L(x*, O) = 1`
for every open neighbourhood `O` of `x*`. -/
theorem proposition_9_3_1 (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    IsTopHarrisRecurrent P x ↔ ∀ O : Set X, IsOpen O → x ∈ O → hitProb P O x = 1 := by
  constructor
  · intro h O hO hx
    exact le_antisymm (hitProb_le_one _ _ _) ((h O hO hx).symm.le.trans (harrisQ_le_hitProb P O x))
  intro hL
  have := isMarkovKernel_pathKernel P
  -- a countable basis of open neighbourhoods shrinking to `x`
  obtain ⟨u, hu⟩ := (𝓝 x).exists_antitone_basis
  set Od : ℕ → Set X := fun d => interior (u d)
  have hOd_open : ∀ d, IsOpen (Od d) := fun d => isOpen_interior
  have hOd_mem : ∀ d, x ∈ Od d := fun d => mem_interior_iff_mem_nhds.2 (hu.mem d)
  have hOd_sep : ∀ y, y ≠ x → ∃ d, y ∉ Od d := by
    intro y hy
    obtain ⟨d, -, hd⟩ := hu.toHasBasis.mem_iff.1 (compl_singleton_mem_nhds hy.symm)
    exact ⟨d, fun h => hd (interior_subset h) rfl⟩
  -- `P_x(η_O ≥ j) = 1` for every `j` and every open neighbourhood `O`
  have key : ∀ j : ℕ, ∀ O : Set X, IsOpen O → x ∈ O →
      pathKernel P x {ω | (j : ℝ≥0∞) ≤ occTime O ω} = 1 := by
    intro j
    induction j with
    | zero => intro O _ _; simp
    | succ j ih =>
      intro O hO hxO
      have hOm := hO.measurableSet
      have hτ := (proposition_3_4_4 (X := X) hOm).1
      set g : X → ℝ≥0∞ := fun y => pathKernel P y {ω | (j : ℝ≥0∞) ≤ occTime O ω} with hgdef
      have hEm := measurableSet_le_occTime hOm (j : ℝ≥0∞)
      have hgm : Measurable g := Kernel.measurable_coe _ hEm
      have hg1 : ∀ y, g y ≤ 1 := fun y => prob_le_one
      have hgx : g x = 1 := ih O hO hxO
      have hT := measurableSet_firstReturn_ne_top (X := X) hOm
      have hgτ : Measurable fun ω => g (stoppedState (firstReturn O) ω) :=
        hgm.comp (measurable_stoppedState hτ)
      -- for each `d`, `g(Φ_τ) = 1` a.e. on `{τ < ∞, Φ_τ ∉ O_d}`
      have hd : ∀ d, pathKernel P x ({ω | stoppedState (firstReturn O) ω ∈ (Od d)ᶜ} ∩
          {ω | firstReturn O ω ≠ ⊤} ∩ {ω | g (stoppedState (firstReturn O) ω) < 1}) = 0 := by
        intro d
        set S := {ω | stoppedState (firstReturn O) ω ∈ (Od d)ᶜ} ∩ {ω | firstReturn O ω ≠ ⊤}
        have hSF := measurableSet_stoppedField_stoppedState hτ (hOd_open d).measurableSet.compl
        have hSm : MeasurableSet S := (hτ.measurableSpace_le _ hSF).inter hT
        have hi : Measurable ({ω : ℕ → X | (j : ℝ≥0∞) ≤ occTime O ω}.indicator
            (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hEm
        have hSM := strong_markov_lintegral P (Measure.dirac x) hτ hSF hi
        rw [pathMeasure_dirac] at hSM
        simp_rw [lintegral_indicator_one hEm] at hSM
        have hpre : MeasurableSet (shiftAt (firstReturn O) ⁻¹'
            {ω : ℕ → X | (j : ℝ≥0∞) ≤ occTime O ω}) := measurable_shiftAt hτ hEm
        have e : ∫⁻ ω in S, {ω : ℕ → X | (j : ℝ≥0∞) ≤ occTime O ω}.indicator 1
            (shiftAt (firstReturn O) ω) ∂pathKernel P x =
            pathKernel P x (S ∩ shiftAt (firstReturn O) ⁻¹'
              {ω : ℕ → X | (j : ℝ≥0∞) ≤ occTime O ω}) := by
          change ∫⁻ ω in S, (shiftAt (firstReturn O) ⁻¹'
            {ω : ℕ → X | (j : ℝ≥0∞) ≤ occTime O ω}).indicator 1 ω ∂pathKernel P x = _
          rw [lintegral_indicator_one hpre, Measure.restrict_apply hpre, inter_comm]
        rw [e] at hSM
        -- the visits to `O ∩ O_d` happen after `τ_O` on `S`
        set O' := O ∩ Od d
        have hO'm : MeasurableSet O' := hOm.inter (hOd_open d).measurableSet
        have h1 := ih O' (hO.inter (hOd_open d)) ⟨hxO, hOd_mem d⟩
        have hE'm := measurableSet_le_occTime hO'm (j : ℝ≥0∞)
        have hpath : S ∩ {ω | (j : ℝ≥0∞) ≤ occTime O' ω} ⊆
            S ∩ shiftAt (firstReturn O) ⁻¹' {ω | (j : ℝ≥0∞) ≤ occTime O ω} := by
          rintro ω ⟨⟨hω1, hω2⟩, hω3⟩
          refine ⟨⟨hω1, hω2⟩, ?_⟩
          obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hω2
          simp only [mem_preimage, mem_ofPred_eq]
          rw [shiftAt_of_eq hm.symm]
          have hωm : ω m ∉ O' := by
            rw [← stoppedState_of_eq hm.symm]; exact fun h => hω1 h.2
          exact hω3.trans (occTime_le_shift_of_firstReturn inter_subset_left hm.symm hωm)
        have hPS : pathKernel P x S ≤ ∫⁻ ω in S, g (stoppedState (firstReturn O) ω)
            ∂pathKernel P x := by
          calc pathKernel P x S = pathKernel P x (S ∩ {ω | (j : ℝ≥0∞) ≤ occTime O' ω}) :=
                (measure_inter_conull (by rw [prob_compl_eq_zero_iff hE'm]; exact h1)).symm
            _ ≤ _ := measure_mono hpath
            _ = _ := hSM
        have hfin : ∫⁻ ω in S, g (stoppedState (firstReturn O) ω) ∂pathKernel P x ≠ ∞ :=
          ne_top_of_le_ne_top (measure_ne_top (pathKernel P x) S)
            ((setLIntegral_mono measurable_const fun ω _ => hg1 _).trans (by simp))
        have hzero : ∫⁻ ω in S, (1 - g (stoppedState (firstReturn O) ω)) ∂pathKernel P x = 0 := by
          rw [lintegral_sub' hgτ.aemeasurable hfin (Eventually.of_forall fun ω => hg1 _),
            setLIntegral_const, one_mul]
          exact tsub_eq_zero_of_le hPS
        have hm' : Measurable fun ω => 1 - g (stoppedState (firstReturn O) ω) :=
          measurable_const.sub hgτ
        rw [lintegral_eq_zero_iff hm', EventuallyEq, ae_restrict_iff' hSm] at hzero
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hzero] with ω hω hmem
        have h0 := hω hmem.1
        simp only [Pi.zero_apply, tsub_eq_zero_iff_le] at h0
        exact absurd hmem.2 (not_lt.2 h0)
      -- hence `g(Φ_τ) = 1` a.e. on `{τ < ∞}`
      have hae : ∀ᵐ ω ∂pathKernel P x, ω ∈ {ω | firstReturn O ω ≠ ⊤} →
          g (stoppedState (firstReturn O) ω) = 1 := by
        have hnull : pathKernel P x ({ω | firstReturn O ω ≠ ⊤} ∩
            {ω | g (stoppedState (firstReturn O) ω) < 1}) = 0 := by
          refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hd)
          obtain ⟨hω1, hω2⟩ := hω
          have hne : stoppedState (firstReturn O) ω ≠ x := fun h => by
            simp only [mem_ofPred_eq] at hω2; rw [h, hgx] at hω2; exact lt_irrefl 1 hω2
          obtain ⟨d, hd'⟩ := hOd_sep _ hne
          exact mem_iUnion.2 ⟨d, ⟨⟨hd', hω1⟩, hω2⟩⟩
        rw [measure_eq_zero_iff_ae_notMem] at hnull
        filter_upwards [hnull] with ω hω hT'
        exact le_antisymm (hg1 _) (not_lt.1 fun h => hω ⟨hT', h⟩)
      rw [Nat.cast_succ, pathKernel_occTime_ge_succ P hOm x,
        setLIntegral_congr_fun_ae hT hae, setLIntegral_const, one_mul]
      exact hL O hO hxO
  intro O hO hxO
  rw [harrisQ_eq_occTime, setOf_occTime_eq_top]
  refine (prob_compl_eq_zero_iff (MeasurableSet.iInter fun k : ℕ =>
    measurableSet_le_occTime hO.measurableSet (k : ℝ≥0∞))).1 ?_
  rw [compl_iInter]
  refine measure_iUnion_null fun k => ?_
  rw [prob_compl_eq_zero_iff (measurableSet_le_occTime hO.measurableSet _)]
  exact key k O hO hxO

/-! ### Lemma 9.3.2 -/

variable [TopologicalSpace X] in
/-- **Lemma 9.3.2** (MT p. 209): if `T` is a continuous component of `K_a` and `T(x*, B) > 0`,
then there is an open neighbourhood `O` of `x*` with `O ⇝ᵃ B` and, uniformly on `O`,
`P_y(σ_B < ∞) ≥ δ > 0`. -/
theorem lemma_9_3_2 {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a)
    {T : Kernel X X} (hT : IsContinuousComponent P a T) {x : X} {B : Set X}
    (hB : MeasurableSet B) (hpos : 0 < T x B) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ SampledAccessible P a O B ∧
      ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ y ∈ O, δ ≤ hitProbZero P B y := by
  have hfin : T x B ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono (subset_univ B)).trans (hT.1 x))
  set δ := T x B / 2
  have hδ : 0 < δ := ENNReal.half_pos hpos.ne'
  refine ⟨{y | δ < T y B}, (hT.2.2 B hB).isOpen_preimage δ,
    ENNReal.half_lt_self hpos.ne' hfin, ⟨δ, hδ, fun y hy => hy.le.trans ((hT.2.1 y) B)⟩,
    δ, hδ, fun y hy => hy.le.trans (((hT.2.1 y) B).trans
      (sampledKernel_le_hitProbZero P ha hB y))⟩

/-- The kernel `I` on `Bool`. -/
noncomputable def boolIdKernel : Kernel Bool Bool := Kernel.id

/-- **Correction to Lemma 9.3.2** (MT p. 209): for the chain on `Bool` (discrete topology) that
jumps to `true`, `T = K_{δ₀} = I` is a continuous component with `T(false, {false}) = 1 > 0`, but
no open neighbourhood `O` of `false` has `O ⇝ {false}` in the sense of `L`. -/
theorem lemma_9_3_2_counterexample :
    haveI := isMarkovKernel_toTrueKernel
    IsContinuousComponent toTrueKernel (diracDist 0) boolIdKernel ∧
      (∀ x, 0 < boolIdKernel x univ) ∧ 0 < boolIdKernel false {false} ∧
      ¬ ∃ O : Set Bool, IsOpen O ∧ false ∈ O ∧ UnifAccessible toTrueKernel O {false} := by
  have := isMarkovKernel_toTrueKernel
  refine ⟨⟨fun x => by simp [boolIdKernel, Kernel.id_apply], fun x => ?_, fun A _ =>
    continuous_of_discreteTopology.lowerSemicontinuous⟩,
    fun x => by simp [boolIdKernel, Kernel.id_apply], by simp [boolIdKernel, Kernel.id_apply], ?_⟩
  · rw [sampledKernel_diracDist, pow_zero_apply, boolIdKernel, Kernel.id_apply]
  · rintro ⟨O, -, hO, δ, hδ, h⟩
    exact lemma_5_5_1_counterexample.2 ⟨δ, hδ, fun y hy => h y (mem_singleton_iff.1 hy ▸ hO)⟩

/-! ### Theorem 9.3.3 -/

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- If `T(x*, B) > 0` for a uniformly transient `B`, some open neighbourhood of `x*` is uniformly
transient (Lemma 9.3.2 and Proposition 8.3.2). -/
theorem exists_open_uniformlyTransient {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) {T : Kernel X X} (hT : IsContinuousComponent P a T) {x : X}
    {B : Set X} (hB : IsUniformlyTransient P B) (hpos : 0 < T x B) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ IsUniformlyTransient P O := by
  obtain ⟨O, hO, hxO, hacc, -⟩ := lemma_9_3_2 ha hT hB.1 hpos
  exact ⟨O, hO, hxO, proposition_8_3_2 P hB hO.measurableSet ha hacc⟩

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- If `X` is transient and `T` is a non-trivial continuous component at `x*`, then `x*` is
topologically transient. -/
theorem isTopTransient_of_transient {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) {T : Kernel X X} (hT : IsContinuousComponent P a T) {x : X}
    {N : Set X} (hN : IsTransientSet P N) (hTN : 0 < T x N) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ IsUniformlyTransient P O := by
  obtain ⟨B, hB, hcov⟩ := hN
  have : 0 < T x (⋃ j, B j) := hTN.trans_le (measure_mono hcov)
  obtain ⟨j, hj⟩ := exists_measure_pos_of_iUnion this
  exact exists_open_uniformlyTransient ha hT (hB j) hj

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- **Theorem 9.3.3** (MT p. 210): for a `ψ`-irreducible T-chain and a reachable point `x*`, the
chain is recurrent iff `x*` is topologically recurrent. -/
theorem theorem_9_3_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) {x : X} (hx : IsReachable P x) :
    IsRecurrentChain P ψ ↔ IsTopRecurrent P x := by
  constructor
  · intro hrec O hO hxO
    have hsupp := (lemma_6_1_4 hψ x).1 hx
    exact hrec.2 O hO.measurableSet
      ((Measure.mem_support_iff_forall x).1 hsupp O (hO.mem_nhds hxO)) x
  · intro htop
    rcases theorem_8_3_4 P hψ with hrec | htr
    · exact hrec
    · exfalso
      obtain ⟨a, T, ha, hTc, hTpos⟩ := hT
      obtain ⟨O, hO, hxO, hOut⟩ := isTopTransient_of_transient ha hTc htr.2
        (by simpa using hTpos x)
      obtain ⟨M, hM, hb⟩ := hOut.exists_bound
      exact hM (top_unique (htop O hO hxO ▸ hb x))

/-! ### Proposition 9.3.4 -/

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- The core of Proposition 9.3.4, (9.25)–(9.29): if `O` is an open neighbourhood of `x*` and
`T(x*, [O^∞]ᶜ) > 0`, where `O^∞ = {y : Q(y, O) = 1}`, then some open neighbourhood `O' ⊆ O` of
`x*` is uniformly transient. -/
theorem exists_uniformlyTransient_nhds_of_infty {P : Kernel X X} [IsMarkovKernel P]
    {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) {T : Kernel X X} (hT : IsContinuousComponent P a T)
    {O : Set X} (hO : IsOpen O) {x : X} (hxO : x ∈ O)
    (hpos : 0 < T x {y | harrisQ P O y = 1}ᶜ) :
    ∃ O' : Set X, IsOpen O' ∧ x ∈ O' ∧ O' ⊆ O ∧ IsUniformlyTransient P O' := by
  have := isMarkovKernel_pathKernel P
  have hOm := hO.measurableSet
  set Oinf := {y | harrisQ P O y = 1}
  -- `Dₙ = {y : P_y(η_O < n) > n⁻¹}`
  have hEn : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | occTime O ω < n} := fun n =>
    measurableSet_lt (measurable_occTime hOm) measurable_const
  set D : ℕ → Set X := fun n => {y | (n : ℝ≥0∞)⁻¹ < pathKernel P y {ω | occTime O ω < n}}
  have hDm : ∀ n, MeasurableSet (D n) := fun n =>
    measurableSet_lt measurable_const (Kernel.measurable_coe _ (hEn n))
  have hcov : Oinfᶜ ⊆ ⋃ n, D n := by
    intro y hy
    have hQ : harrisQ P O y < 1 := lt_of_le_of_ne (harrisQ_le_one P O y) hy
    set c := pathKernel P y {ω | occTime O ω < ∞}
    have hc : 0 < c := by
      have hset : {ω : ℕ → X | occTime O ω < ∞} = {ω | occTime O ω = ∞}ᶜ := by
        ext ω; simp [lt_top_iff_ne_top]
      have hm : MeasurableSet {ω : ℕ → X | occTime O ω = ∞} :=
        measurable_occTime hOm (measurableSet_singleton ∞)
      change 0 < pathKernel P y {ω | occTime O ω < ∞}
      rw [hset, prob_compl_eq_one_sub hm, ← harrisQ_eq_occTime]
      exact tsub_pos_of_lt hQ
    have hmono : Monotone fun n : ℕ => {ω : ℕ → X | occTime O ω < n} :=
      fun m n hmn ω (hω : occTime O ω < m) =>
        show occTime O ω < n from lt_of_lt_of_le hω (by exact_mod_cast hmn)
    have hU : (⋃ n : ℕ, {ω : ℕ → X | occTime O ω < n}) = {ω | occTime O ω < ∞} := by
      ext ω
      simp only [mem_iUnion, mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn⟩; exact hn.trans (ENNReal.natCast_lt_top n)
      · intro h
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h.ne
        exact ⟨n, hn⟩
    have htend := tendsto_measure_iUnion_atTop (μ := pathKernel P y) hmono
    rw [hU] at htend
    have hc2 : c / 2 < c := ENNReal.half_lt_self hc.ne' (measure_ne_top _ _)
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (htend.eventually (lt_mem_nhds hc2))
    obtain ⟨n₂, hn₂⟩ := ENNReal.exists_inv_nat_lt (ENNReal.half_pos hc.ne').ne'
    refine mem_iUnion.2 ⟨max n₁ n₂, ?_⟩
    calc ((max n₁ n₂ : ℕ) : ℝ≥0∞)⁻¹ ≤ (n₂ : ℝ≥0∞)⁻¹ :=
          ENNReal.inv_le_inv.2 (by exact_mod_cast le_max_right n₁ n₂)
      _ < c / 2 := hn₂
      _ < _ := hn₁ _ (le_max_left _ _)
  -- some `T(x*, Dₙ) > 0`
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion (hpos.trans_le (measure_mono hcov))
  obtain ⟨hε₁, hε₁t, h2ε₁⟩ := half_min_spec hn
  set ε₁ := 2⁻¹ * min (T x (D n)) 1
  set ε := 2⁻¹ * ε₁
  have hε : 0 < ε := ENNReal.mul_pos (by simp) hε₁.ne'
  have hεt : ε ≠ ∞ := ENNReal.mul_ne_top (by simp) hε₁t
  have h2ε : 2 * ε = ε₁ := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hε₁lt : ε₁ < T x (D n) := by
    calc ε₁ < ε₁ + ε₁ := ENNReal.lt_add_right hε₁t hε₁.ne'
      _ = 2 * ε₁ := (two_mul ε₁).symm
      _ ≤ _ := h2ε₁
  obtain ⟨m, hm⟩ := exists_tail_le ha hε
  set O' := O ∩ {y | ε₁ < T y (D n)}
  have hO' : IsOpen O' := hO.inter ((hT.2.2 _ (hDm n)).isOpen_preimage ε₁)
  refine ⟨O', hO', ⟨hxO, hε₁lt⟩, inter_subset_left, ?_⟩
  -- for `y ∈ O'`, `P_y(η_O < m + n) ≥ n⁻¹ ε`
  have hσ := (proposition_3_4_4 (X := X) (hDm n)).2
  have hlow : ∀ y ∈ O', (n : ℝ≥0∞)⁻¹ * ε ≤
      pathKernel P y {ω | occTime O ω < ((m + n : ℕ) : ℝ≥0∞)} := by
    intro y hy
    -- `P_y(σ_{Dₙ} ≤ m) ≥ ε`
    have h1 : ε ≤ ∑ k ∈ Finset.range m, a k * (P ^ k) y (D n) :=
      le_sum_head P m y (hDm n) hεt hm (h2ε.symm ▸ hy.2.le) ((hT.2.1 y) (D n))
    have hAF : MeasurableSet[hσ.measurableSpace] {ω | firstHit (D n) ω ≤ (m : ℕ)} :=
      hσ.measurableSet_le' m
    have hAm : MeasurableSet {ω : ℕ → X | firstHit (D n) ω ≤ (m : ℕ)} :=
      hσ.measurableSpace_le _ hAF
    have h2 : ∑ k ∈ Finset.range m, a k * (P ^ k) y (D n) ≤
        pathKernel P y {ω | firstHit (D n) ω ≤ (m : ℕ)} := by
      calc ∑ k ∈ Finset.range m, a k * (P ^ k) y (D n)
          ≤ ∑ k ∈ Finset.range m, a k * pathKernel P y {ω | firstHit (D n) ω ≤ (m : ℕ)} := by
            refine Finset.sum_le_sum fun k hk => mul_le_mul' le_rfl ?_
            rw [← pathKernel_coord_mem P y k (hDm n)]
            refine measure_mono fun ω hω => ?_
            simp only [mem_ofPred_eq] at hω ⊢
            exact (hittingAfter_le_of_mem (Nat.zero_le k) hω).trans
              (WithTop.coe_le_coe.2 (Finset.mem_range.1 hk).le)
        _ = (∑ k ∈ Finset.range m, a k) * pathKernel P y {ω | firstHit (D n) ω ≤ (m : ℕ)} := by
            rw [Finset.sum_mul]
        _ ≤ 1 * pathKernel P y {ω | firstHit (D n) ω ≤ (m : ℕ)} := by
            gcongr; exact (ENNReal.sum_le_tsum _).trans (le_of_eq ha)
        _ = _ := one_mul _
    -- the strong Markov property at `σ_{Dₙ}`
    have hi : Measurable ({ω : ℕ → X | occTime O ω < n}.indicator (1 : (ℕ → X) → ℝ≥0∞)) :=
      measurable_one.indicator (hEn n)
    have hSM := strong_markov_lintegral P (Measure.dirac y) hσ hAF hi
    rw [pathMeasure_dirac] at hSM
    simp_rw [lintegral_indicator_one (hEn n)] at hSM
    have hsub : {ω : ℕ → X | firstHit (D n) ω ≤ (m : ℕ)} ⊆ {ω | firstHit (D n) ω ≠ ⊤} :=
      fun ω hω h => by simp only [mem_ofPred_eq, h, top_le_iff] at hω; exact WithTop.coe_ne_top hω
    rw [inter_eq_left.2 hsub] at hSM
    have hpre : MeasurableSet (shiftAt (firstHit (D n)) ⁻¹' {ω : ℕ → X | occTime O ω < n}) :=
      measurable_shiftAt hσ (hEn n)
    have e : ∫⁻ ω in {ω | firstHit (D n) ω ≤ (m : ℕ)}, {ω : ℕ → X | occTime O ω < n}.indicator 1
        (shiftAt (firstHit (D n)) ω) ∂pathKernel P y =
        pathKernel P y ({ω | firstHit (D n) ω ≤ (m : ℕ)} ∩
          shiftAt (firstHit (D n)) ⁻¹' {ω : ℕ → X | occTime O ω < n}) := by
      change ∫⁻ ω in {ω | firstHit (D n) ω ≤ (m : ℕ)}, (shiftAt (firstHit (D n)) ⁻¹'
        {ω : ℕ → X | occTime O ω < n}).indicator 1 ω ∂pathKernel P y = _
      rw [lintegral_indicator_one hpre, Measure.restrict_apply hpre, inter_comm]
    rw [e] at hSM
    have h3 : (n : ℝ≥0∞)⁻¹ * pathKernel P y {ω | firstHit (D n) ω ≤ (m : ℕ)} ≤
        pathKernel P y ({ω | firstHit (D n) ω ≤ (m : ℕ)} ∩
          shiftAt (firstHit (D n)) ⁻¹' {ω : ℕ → X | occTime O ω < n}) := by
      rw [hSM, ← setLIntegral_const]
      refine setLIntegral_mono ((Kernel.measurable_coe _ (hEn n)).comp
        (measurable_stoppedState hσ)) fun ω hω => ?_
      exact (stoppedState_firstHit_mem (D n) (hsub hω)).le
    have h4 : {ω : ℕ → X | firstHit (D n) ω ≤ (m : ℕ)} ∩
        shiftAt (firstHit (D n)) ⁻¹' {ω : ℕ → X | occTime O ω < n} ⊆
        {ω | occTime O ω < ((m + n : ℕ) : ℝ≥0∞)} := by
      rintro ω ⟨h1, h2⟩
      simp only [mem_ofPred_eq, mem_preimage] at h1 h2 ⊢
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (hsub h1)
      rw [shiftAt_of_eq hs.symm] at h2
      have hsm : s ≤ m := by rw [← hs] at h1; exact WithTop.coe_le_coe.1 h1
      calc occTime O ω ≤ s + occTime O (shift s ω) := occTime_le_add_shift O s ω
        _ < s + n := ENNReal.add_lt_add_left (ENNReal.natCast_ne_top s) h2
        _ ≤ ((m + n : ℕ) : ℝ≥0∞) := by push_cast; gcongr
    calc (n : ℝ≥0∞)⁻¹ * ε ≤ (n : ℝ≥0∞)⁻¹ *
          pathKernel P y {ω | firstHit (D n) ω ≤ (m : ℕ)} := by gcongr; exact h1.trans h2
      _ ≤ _ := h3.trans (measure_mono h4)
  refine isUniformlyTransient_of_occTime_ge P hO'.measurableSet (m + n)
    (c := (n : ℝ≥0∞)⁻¹ * ε) (ENNReal.mul_pos (ENNReal.inv_ne_zero.2
      (ENNReal.natCast_ne_top n)) hε.ne') fun y hy => ?_
  have hlt := measurableSet_lt (measurable_occTime (X := X) hOm)
    (measurable_const (a := ((m + n : ℕ) : ℝ≥0∞)))
  calc pathKernel P y {ω | ((m + n : ℕ) : ℝ≥0∞) ≤ occTime O' ω}
      ≤ pathKernel P y {ω | occTime O ω < ((m + n : ℕ) : ℝ≥0∞)}ᶜ :=
        measure_mono fun ω hω => by
          simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hω ⊢
          exact hω.trans (occTime_mono inter_subset_left ω)
    _ = 1 - pathKernel P y {ω | occTime O ω < ((m + n : ℕ) : ℝ≥0∞)} :=
        prob_compl_eq_one_sub hlt
    _ ≤ 1 - (n : ℝ≥0∞)⁻¹ * ε := tsub_le_tsub_left (hlow y hy) 1

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- **Proposition 9.3.4 (i)** (MT p. 211): for a continuous component `T` of `K_a` with
`T(x*, X) > 0` (a T-chain), a topologically recurrent `x*` has `Q(x*, O) > 0` for every open
neighbourhood `O`. -/
theorem proposition_9_3_4_i {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) {T : Kernel X X} (hT : IsContinuousComponent P a T) {x : X}
    (hTx : 0 < T x univ) (htop : IsTopRecurrent P x) {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) :
    0 < harrisQ P O x := by
  have := isMarkovKernel_pathKernel P
  by_contra h0
  have hQ0 : harrisQ P O x = 0 := le_antisymm (not_lt.1 h0) zero_le
  have hOm := hO.measurableSet
  set Oinf := {y | harrisQ P O y = 1}
  have hOinf : MeasurableSet Oinf := measurable_harrisQ P hOm (measurableSet_singleton 1)
  -- `L(x*, O^∞) = 0`
  have hL0 : hitProb P Oinf x = 0 := by
    have hge := harrisQ_ge_stopping P hOm x (proposition_3_4_4 hOinf).1
    have hT' := measurableSet_firstReturn_ne_top (X := X) hOinf
    rw [hQ0] at hge
    refine le_antisymm ?_ zero_le
    calc hitProb P Oinf x = ∫⁻ _ in {ω | firstReturn Oinf ω ≠ ⊤}, 1 ∂pathKernel P x := by
          rw [setLIntegral_const, one_mul]; rfl
      _ = ∫⁻ ω in {ω | firstReturn Oinf ω ≠ ⊤}, harrisQ P O (stoppedState (firstReturn Oinf) ω)
            ∂pathKernel P x :=
          setLIntegral_congr_fun hT' fun ω hω => (stoppedState_firstReturn_mem Oinf hω).symm
      _ ≤ 0 := hge
  have hxnot : x ∉ Oinf := fun h => by
    have : harrisQ P O x = 1 := h
    rw [hQ0] at this; exact zero_ne_one this
  have hT0 : T x Oinf = 0 := le_antisymm (((hT.2.1 x) Oinf).trans
    ((sampledKernel_le_hitProbZero P ha hOinf x).trans_eq
      ((hitProbZero_of_notMem P hOinf hxnot).trans hL0))) zero_le
  have hpos : 0 < T x Oinfᶜ := by
    have : T x univ ≤ T x Oinf + T x Oinfᶜ := by
      rw [← union_compl_self Oinf]; exact measure_union_le _ _
    rw [hT0, zero_add] at this
    exact hTx.trans_le this
  obtain ⟨O', hO', hxO', -, hut⟩ := exists_uniformlyTransient_nhds_of_infty ha hT hO hxO hpos
  obtain ⟨M, hM, hb⟩ := hut.exists_bound
  exact hM (top_unique (htop O' hO' hxO' ▸ hb x))

variable [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- **Proposition 9.3.4 (ii)** (MT p. 211): if moreover `P(x*, ·) ≪ T(x*, ·)` (the book assumes
equivalence), a topologically recurrent `x*` is topologically Harris recurrent. -/
theorem proposition_9_3_4_ii {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) {T : Kernel X X} (hT : IsContinuousComponent P a T) {x : X}
    (hac : P x ≪ T x) (htop : IsTopRecurrent P x) : IsTopHarrisRecurrent P x := by
  intro O hO hxO
  by_contra hne
  have hOm := hO.measurableSet
  set Oinf := {y | harrisQ P O y = 1}
  have hOinf : MeasurableSet Oinf := measurable_harrisQ P hOm (measurableSet_singleton 1)
  have hP : 0 < P x Oinfᶜ := by
    by_contra h0
    have h0' : P x Oinfᶜ = 0 := le_antisymm (not_lt.1 h0) zero_le
    have h1 : P x Oinf = 1 := (prob_compl_eq_zero_iff hOinf).1 h0'
    apply hne
    refine le_antisymm (harrisQ_le_one P O x) ?_
    rw [harrisQ_eq_lintegral_pow P hOm x 1, pow_one]
    calc (1 : ℝ≥0∞) = ∫⁻ _ in Oinf, 1 ∂P x := by rw [setLIntegral_const, one_mul, h1]
      _ = ∫⁻ y in Oinf, harrisQ P O y ∂P x := setLIntegral_congr_fun hOinf fun y hy => hy.symm
      _ ≤ ∫⁻ y, harrisQ P O y ∂P x := setLIntegral_le_lintegral _ _
  have hpos : 0 < T x Oinfᶜ := pos_iff_ne_zero.2 fun h => hP.ne' (hac h)
  obtain ⟨O', hO', hxO', -, hut⟩ := exists_uniformlyTransient_nhds_of_infty ha hT hO hxO hpos
  obtain ⟨M, hM, hb⟩ := hut.exists_bound
  exact hM (top_unique (htop O' hO' hxO' ▸ hb x))

variable [TopologicalSpace X] [OpensMeasurableSpace X] [FirstCountableTopology X] in
/-- **Proposition 9.3.4**, last claim (MT p. 211): for a strong Feller chain, topologically
recurrent states are topologically Harris recurrent (`P` is its own continuous component). -/
theorem proposition_9_3_4_strongFeller {P : Kernel X X} [IsMarkovKernel P]
    (hP : IsStrongFeller P) {x : X} (htop : IsTopRecurrent P x) : IsTopHarrisRecurrent P x := by
  have hT : IsContinuousComponent P (diracDist 1) P :=
    ⟨isSubstochasticKernel_of_markov P, fun y => by rw [sampledKernel_diracDist, pow_one],
      (proposition_6_1_1_i_strong P).1 hP⟩
  exact proposition_9_3_4_ii (isSamplingDist_diracDist 1) hT (Measure.AbsolutelyContinuous.refl _)
    htop

/-! ### Theorem 9.3.5 -/

variable [TopologicalSpace X] [T1Space X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
/-- **Theorem 9.3.5** (MT p. 212): for any chain, `X = R ∪ N` where `R` is the set of
topologically Harris recurrent states and `N = Rᶜ` is transient. -/
theorem theorem_9_3_5 (P : Kernel X X) [IsMarkovKernel P] :
    IsTransientSet P {x | ¬ IsTopHarrisRecurrent P x} := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨f, hf⟩ := (hbc.insert ∅).exists_eq_range (insert_nonempty ∅ b)
  have hfopen : ∀ n, IsOpen (f n) := by
    intro n
    have : f n ∈ insert ∅ b := hf ▸ mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  -- `D n j = {y ∈ fₙ : L(y, fₙ) ≤ 1 − j⁻¹}`
  set D : ℕ → ℕ → Set X := fun n j => {y | y ∈ f n ∧ hitProb P (f n) y ≤ 1 - (j : ℝ≥0∞)⁻¹}
  have hDut : ∀ n j, IsUniformlyTransient P (D n j) := by
    intro n j
    have hfm := (hfopen n).measurableSet
    have hDm : MeasurableSet (D n j) := hfm.inter (measurable_hitProb P hfm measurableSet_Iic)
    have hε : 1 - (j : ℝ≥0∞)⁻¹ < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (by simp)
    have hbound := proposition_8_3_1_iii P hDm hε fun y hy =>
      (hitProb_mono P (fun _ h => h.1 : D n j ⊆ f n) y).trans hy.2
    exact ⟨hDm, (1 - (1 - (j : ℝ≥0∞)⁻¹))⁻¹, ENNReal.inv_ne_top.2 (tsub_pos_of_lt hε).ne',
      fun y _ => hbound y⟩
  refine ⟨fun k => D (Nat.unpair k).1 (Nat.unpair k).2, fun k => hDut _ _, fun x hx => ?_⟩
  simp only [mem_ofPred_eq] at hx
  rw [proposition_9_3_1 P x] at hx
  push Not at hx
  obtain ⟨O, hO, hxO, hL⟩ := hx
  have hlt : hitProb P O x < 1 := lt_of_le_of_ne (hitProb_le_one P O x) hL
  obtain ⟨v, hv, hxv, hvO⟩ := hb.exists_subset_of_mem_open hxO hO
  obtain ⟨n, hn⟩ : ∃ n, f n = v := by
    have : v ∈ range f := hf ▸ mem_insert_of_mem ∅ hv
    exact this
  have hlt' : hitProb P (f n) x < 1 := (hitProb_mono P (hn ▸ hvO) x).trans_lt hlt
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hlt').ne'
  refine mem_iUnion.2 ⟨Nat.pair n j, ?_⟩
  simp only [Nat.unpair_pair]
  refine ⟨hn ▸ hxv, ?_⟩
  exact ENNReal.le_sub_of_add_le_left (ne_top_of_lt hj)
    (by rw [add_comm]; exact (lt_tsub_iff_left.1 hj).le)

/-! ### Theorem 9.3.6 -/

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X] in
/-- A topologically Harris recurrent state is non-evanescent: `P_{x*}{Φ → ∞} = 0`. -/
theorem IsTopHarrisRecurrent.pathKernel_tendsToInfty {P : Kernel X X} [IsMarkovKernel P]
    {x : X} (h : IsTopHarrisRecurrent P x) : pathKernel P x tendsToInfty = 0 := by
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  have hQ := h (interior K) isOpen_interior (mem_interior_iff_mem_nhds.2 hKx)
  have hQK : harrisQ P K x = 1 := le_antisymm (harrisQ_le_one P K x)
    (hQ ▸ harrisQ_mono P interior_subset x)
  exact pathKernel_tendsToInfty_eq_zero P hK hK.measurableSet hQK

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 9.3.6** (MT p. 213), corrected: for a `ψ`-irreducible T-chain with continuous
component `T` of `K_a`, there is `H`, empty or a maximal Harris set, such that `N = Hᶜ` is
transient, every topologically Harris recurrent state lies in `H`, every `x* ∈ N` has an open
neighbourhood `O` with `O ∩ N` uniformly transient, and every `x* ∈ N` with `T(x*, H) = 0` is
topologically transient. When the chain is transient, `H = ∅` and every state is topologically
transient. -/
theorem theorem_9_3_6 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) {T : Kernel X X}
    (hT : IsContinuousComponent P a T) (hTpos : ∀ x, 0 < T x univ) :
    ∃ H : Set X, (H = ∅ ∨ IsMaximalHarrisSet P ψ H) ∧ IsTransientSet P Hᶜ ∧
      (∀ x, IsTopHarrisRecurrent P x → x ∈ H) ∧
      (∀ x ∉ H, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ IsUniformlyTransient P (O ∩ Hᶜ)) ∧
      (∀ x ∉ H, T x H = 0 → IsTopTransient P x) := by
  have hTch : IsTChain P := ⟨a, T, ha, hT, hTpos⟩
  obtain ⟨H, hH, hN, h914⟩ := theorem_9_2_2 hψ hTch
  have hHm : MeasurableSet H := by
    rcases hH with h | h
    · rw [h]; exact MeasurableSet.empty
    · exact h.1
  -- states with `T(x*, H) = 0` are topologically transient
  have hNE : ∀ x ∉ H, T x H = 0 →
      ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ IsUniformlyTransient P O := by
    intro x _ hTH
    have : 0 < T x Hᶜ := by
      have h1 : T x univ ≤ T x H + T x Hᶜ := by
        rw [← union_compl_self H]; exact measure_union_le _ _
      rw [hTH, zero_add] at h1
      exact (hTpos x).trans_le h1
    exact isTopTransient_of_transient ha hT hN this
  refine ⟨H, hH, hN, fun x hx => ?_, fun x hx => ?_, fun x hx hTH => ?_⟩
  · -- `R ⊆ H`
    have hL := h914 x
    rw [hx.pathKernel_tendsToInfty, tsub_zero] at hL
    rcases hH with h | h
    · exfalso
      rw [h] at hL
      have := isMarkovKernel_pathKernel P
      have h0 : hitProb P (∅ : Set X) x = 0 := by
        refine measure_mono_null (fun ω hω => ?_) measure_empty
        obtain ⟨n, -, hn⟩ := (firstReturn_ne_top_iff ∅ ω).1 hω
        exact hn
      rw [h0] at hL; exact zero_ne_one hL
    · have : x ∈ harrisInfty P H := hL
      rwa [h.2.2.2.1] at this
  · -- a neighbourhood whose trace on `N` is uniformly transient
    by_cases hTH : T x H = 0
    · obtain ⟨O, hO, hxO, hut⟩ := hNE x hx hTH
      exact ⟨O, hO, hxO, hut.mono (hO.measurableSet.inter hHm.compl) inter_subset_left⟩
    · rcases hH with h | h
      · rw [h] at hTH; simp at hTH
      obtain ⟨-, -, habs, -, -⟩ := h
      -- `O_δ = {T(·, H) > ε₁}`
      have hpos : 0 < T x H := pos_iff_ne_zero.2 hTH
      obtain ⟨hε₁, hε₁t, h2ε₁⟩ := half_min_spec hpos
      set ε₁ := 2⁻¹ * min (T x H) 1
      set ε := 2⁻¹ * ε₁
      have hε : 0 < ε := ENNReal.mul_pos (by simp) hε₁.ne'
      have hεt : ε ≠ ∞ := ENNReal.mul_ne_top (by simp) hε₁t
      have h2ε : 2 * ε = ε₁ := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      have hε₁lt : ε₁ < T x H := by
        calc ε₁ < ε₁ + ε₁ := ENNReal.lt_add_right hε₁t hε₁.ne'
          _ = 2 * ε₁ := (two_mul ε₁).symm
          _ ≤ _ := h2ε₁
      obtain ⟨M, hM⟩ := exists_tail_le ha hε
      set O := {y | ε₁ < T y H}
      have hO : IsOpen O := (hT.2.2 H hHm).isOpen_preimage ε₁
      refine ⟨O, hO, hε₁lt, isUniformlyTransient_of_escape (M := M) P hHm habs
        (hO.measurableSet.inter hHm.compl) inter_subset_right hε fun y hy => ?_⟩
      have h1 := le_sum_head P M y hHm hεt hM (h2ε.symm ▸ hy.1.le) ((hT.2.1 y) H)
      calc ε ≤ ∑ k ∈ Finset.range M, a k * (P ^ k) y H := h1
        _ ≤ ∑ k ∈ Finset.range M, a k * (P ^ M) y H :=
            Finset.sum_le_sum fun k hk => mul_le_mul' le_rfl
              (IsAbsorbing.pow_mono habs hHm y (Finset.mem_range.1 hk).le)
        _ = (∑ k ∈ Finset.range M, a k) * (P ^ M) y H := by rw [Finset.sum_mul]
        _ ≤ 1 * (P ^ M) y H := by gcongr; exact (ENNReal.sum_le_tsum _).trans (le_of_eq ha)
        _ = _ := one_mul _
  · -- topological transience when `T(x*, H) = 0`
    obtain ⟨O, hO, hxO, hut⟩ := hNE x hx hTH
    intro htop
    obtain ⟨M, hM, hb⟩ := hut.exists_bound
    exact hM (top_unique (htop O hO hxO ▸ hb x))

end MeynTweedie.InvariantMeasures
