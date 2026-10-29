/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DriftRegularity.DriftExamples
import DriftRegularity.ModelKernels

/-!
# The GI/G/1 queue with re-entry (MT §11.4.2)

Meyn and Tweedie, §11.4.2, pp. 274–276. Customers arrive at `0 = T₀ < T₁ < ⋯` with i.i.d.
interarrival times `∼ G` (mean `1/λ`), are served one at a time with i.i.d. service times `∼ H`
(mean `m = 1/μ`), and after each service leave with probability `r` or re-enter the queue with
probability `1 − r`. The chain is `Φₙ = (Nₙ, Rₙ)` on `ℤ₊ × ℝ₊` at the arrival instants `Tₙ−`:
`Nₙ` customers waiting (not counting the one in service) and residual service time `Rₙ`
(`Rₙ = 0` when the server is free).

**The model.** Inside an interarrival interval the queue is followed event by event on
configurations `(C, ρ, t, β)` (`QConfig`: customers in the system, residual service, time to the
next arrival, busy time so far); `cstep` completes the service in progress, decides re-entry, and
starts a fresh service, until the configuration is final (`QConfig.IsFinal`: the system is empty
or the service in progress outlasts the interval). The innovations of one interval (`QNoise`)
are the interarrival time `τ ∼ G`, a service time `s₀ ∼ H` for an arrival finding the server
free, and i.i.d. pairs `(sₖ, eₖ) ∼ H ⊗ Bernoulli(r)` (`exitLaw`) for the services started in the
interval; their law is `gig1rNoise G H r`. The step `gig1rStep` reads `Φₙ₊₁` off the first final
configuration (`qout`), and the chain is the random recursion `gig1rKernel G H r`.
* `gig1r_isMarkovChain`: `Φₙ₊₁ = F(Φₙ, ξₙ₊₁)` with i.i.d. innovations independent of `Φ₀` is a
  Markov chain with this kernel (MT p. 274; `isMarkovChain_of_iid`, from `ModelKernels`).
* `gig1rStep_eq`, `gig1rBusy_eq`: the state and the busy time `gig1rBusy` read off any final
  configuration; `gig1rNoise_not_final`: every interval ends almost surely when `H ≠ δ₀`
  (`sum_le_of_not_final`, `measure_sum_bdd_eq_zero`).

**Proposition 11.4.3** (`proposition_11_4_3`, p. 275). Under the load condition (11.32),
`ρ_r < 1`, i.e. `m/r < E T`, the chain is `δ_{[0]}`-irreducible, strongly aperiodic and
aperiodic, and every compact set is petite. The book's sketch for (11.33) is made precise with
the potential `Ψ(N, R) = R + N a` (`qpot`): for `a, δ > 0` with `H[0, a) > 0` and
`G(a + δ, ∞) > 0` (`exists_good_constants`), a good interval (`goodNoise`: `τ > a + δ`, the
first services shorter than `a`, all ending in departures) empties the queue or lowers `Ψ` by
more than `δ` (`good_step`), and has probability `goodProb > 0`; by induction
`P^{k+1}(x, [0]) ≥ ∏_{i ≤ k} goodProb(n + i)` on `{N ≤ n, Ψ ≤ kδ}` (`gig1r_reach_zero`), a
bound uniform on compact sets.

**Proposition 11.4.4** (`proposition_11_4_4`, p. 275). The expected work
`V(x) = E_x[W₀]` (`qworkV`) satisfies (11.34) with `k = 1` (after scaling by a constant), so
(V2) holds with a compact, hence petite, set and the chain is regular and positive Harris.
* `lintegral_cwork_cstep`, `lintegral_cwork_qcfg`: the expected remaining work plus the busy
  time (`cwork`) is preserved by each event, so it has mean `V(x)` at every event of an interval.
* `lintegral_qworkV_add_busy`: work conservation, `E_x[V(Φ₁)] + E[busy time] ≤ V(x) + m/r`
  (Fatou's lemma along the a.s. finite interval); this is (11.35) in expectation.
* `gig1rBusy_ge`: the busy time is at least `min(τ, R + s₁ + ⋯ + s_N)`; with
  `tendsto_integral_posPart_sub` and `ae_sum_unbounded`, the server is busy for all but `η` of
  the mean interval off a compact set, and `gig1r_drift` gives `E_x[V(Φ₁)] ≤ V(x) − c` there.

**Hypotheses.** `0 < r ≤ 1`; finite means of `G` and `H` (the book's `1/λ`, `1/μ`); and, for
Proposition 11.4.4, `E S > 0` (so that intervals end almost surely). Proposition 11.4.3 only uses
`E S < E T`, which the load condition implies.

**Not formalised.** The identification of this recursion with a queue built on a single
probability space from global sequences of interarrival times, service times and re-entry
decisions (the book asserts the Markov property); the book's monotonicity remark
`P_x(Φ_m = [0]) ≤ P_y(Φ_m = [0])` for `x ≥ y`, which the potential argument does not need.

**Corrections.** None. The book proves (11.34) for a `k`-skeleton with `(k/λ)(1 − ρ_r) ≥ 2`; one
step suffices once `V` is scaled.
-/

namespace MeynTweedie.DriftRegularity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### The model -/

/-- The re-entry decision: `true` (the customer leaves after its service) with probability `r`,
`false` (it re-enters the queue) with probability `1 − r`. -/
noncomputable def exitLaw (r : ℝ) : Measure Bool :=
  ENNReal.ofReal r • Measure.dirac true + ENNReal.ofReal (1 - r) • Measure.dirac false

/-- The re-entry law is a probability for `0 ≤ r ≤ 1`. -/
theorem isProbabilityMeasure_exitLaw {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsProbabilityMeasure (exitLaw r) := by
  constructor
  simp only [exitLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith), add_sub_cancel, ENNReal.ofReal_one]

/-- A configuration of the queue inside one interarrival interval: `(C, ρ, t, β)` with `C` the
number of customers in the system, `ρ` the residual service time of the customer in service
(meaningful when `C ≥ 1`), `t` the time left until the next arrival and `β` the time the server
has been busy so far in the interval. -/
abbrev QConfig : Type := ℕ × ℝ≥0 × ℝ≥0 × ℝ≥0

/-- The number of customers after a service completion: one fewer if the customer leaves. -/
def nextC (C : ℕ) (e : Bool) : ℕ := if e then C - 1 else C

/-- A configuration is **final** for the interval if the system is empty (`C = 0`) or the service
in progress outlasts the interval (`t < ρ`). -/
def QConfig.IsFinal (y : QConfig) : Prop := y.1 = 0 ∨ y.2.2.1 < y.2.1

/-- **One event inside an interval.** A final configuration stays put. Otherwise the service in
progress completes after time `ρ ≤ t`; the customer leaves (`e = true`) or re-enters the queue;
if the system is then empty the server idles, else the next customer starts a fresh service of
length `s`. -/
noncomputable def cstep (p : QConfig × (ℝ≥0 × Bool)) : QConfig :=
  open Classical in
  if p.1.1 = 0 ∨ p.1.2.2.1 < p.1.2.1 then p.1
  else if nextC p.1.1 p.2.2 = 0 then (0, 0, p.1.2.2.1 - p.1.2.1, p.1.2.2.2 + p.1.2.1)
  else (nextC p.1.1 p.2.2, p.2.1, p.1.2.2.1 - p.1.2.1, p.1.2.2.2 + p.1.2.1)

/-- The configuration just after the arrival at the start of an interval, from the state
`(N, R)` at the arrival instant `−` (queue length `N` excluding the customer in service,
residual service `R`, `R = 0` meaning the server is free), the interarrival time `τ` and a
fresh service time `s₀` (used when the server is free). -/
noncomputable def qinit (p : (ℕ × ℝ≥0) × (ℝ≥0 × ℝ≥0)) : QConfig :=
  open Classical in
  if 0 < p.1.2 then (p.1.1 + 2, p.1.2, p.2.1, 0) else (p.1.1 + 1, p.2.2, p.2.1, 0)

/-- The state `(N, R)` at the next arrival instant `−` read off a final configuration: `(0, 0)`
if the system is empty, else `C − 1` waiting customers and residual `ρ − t`. -/
noncomputable def qout (y : QConfig) : ℕ × ℝ≥0 :=
  open Classical in
  if y.1 = 0 then (0, 0) else (y.1 - 1, y.2.1 - y.2.2.1)

/-- The innovations of one interarrival interval: the interarrival time `τ`, a service time
`s₀` for an arriving customer who finds the server free, and the i.i.d. pairs `(sₖ, eₖ)` of
service times and re-entry decisions for the services started in the interval. -/
abbrev QNoise : Type := ℝ≥0 × ℝ≥0 × (ℕ → ℝ≥0 × Bool)

/-- The configurations of the interval started from `x` with innovations `ξ`. -/
noncomputable def qcfg (p : (ℕ × ℝ≥0) × QNoise) (k : ℕ) : QConfig :=
  orbit cstep (qinit (p.1, (p.2.1, p.2.2.1))) p.2.2.2 k

/-- Some configuration of the interval is final, or none is. -/
theorem exists_isFinal_or (p : (ℕ × ℝ≥0) × QNoise) :
    ∃ k, (qcfg p k).IsFinal ∨ ¬ ∃ j, (qcfg p j).IsFinal := by
  by_cases h : ∃ j, (qcfg p j).IsFinal
  · obtain ⟨j, hj⟩ := h
    exact ⟨j, Or.inl hj⟩
  · exact ⟨0, Or.inr h⟩

/-- **The step of the GI/G/1 queue with re-entry**: `Φₙ₊₁ = F(Φₙ, ξₙ₊₁)` is the state read off
the first final configuration of the interval (and `(0, 0)` from the initial configuration in
the null event that the interval never ends). -/
noncomputable def gig1rStep (p : (ℕ × ℝ≥0) × QNoise) : ℕ × ℝ≥0 :=
  open Classical in
  qout (qcfg p (Nat.find (exists_isFinal_or p)))

/-- The law of the innovations: `τ ∼ G`, `s₀ ∼ H`, `(sₖ, eₖ) ∼ (H ⊗ Bernoulli(r))^{⊗ℕ}`. -/
noncomputable def gig1rNoise (G H : Measure ℝ≥0) (r : ℝ) : Measure QNoise :=
  G.prod (H.prod (Measure.infinitePi fun _ : ℕ => H.prod (exitLaw r)))

/-- **The GI/G/1 queue with re-entry** (MT §11.4.2): the chain `Φₙ = (Nₙ, Rₙ)` on `ℤ₊ × ℝ₊`
at the arrival instants `Tₙ−`, as the random recursion driven by the interval innovations. -/
noncomputable def gig1rKernel (G H : Measure ℝ≥0) (r : ℝ) : Kernel (ℕ × ℝ≥0) (ℕ × ℝ≥0) :=
  recursionKernel (gig1rNoise G H r) gig1rStep

/-! ### Measurability -/

/-- The event step is measurable. -/
theorem measurable_cstep : Measurable cstep := by
  classical
  have hC : Measurable fun p : QConfig × (ℝ≥0 × Bool) => p.1.1 := measurable_fst.fst
  have hρ : Measurable fun p : QConfig × (ℝ≥0 × Bool) => p.1.2.1 := measurable_fst.snd.fst
  have ht : Measurable fun p : QConfig × (ℝ≥0 × Bool) => p.1.2.2.1 := measurable_fst.snd.snd.fst
  have hβ : Measurable fun p : QConfig × (ℝ≥0 × Bool) => p.1.2.2.2 := measurable_fst.snd.snd.snd
  have hs : Measurable fun p : QConfig × (ℝ≥0 × Bool) => p.2.1 := measurable_snd.fst
  have hn : Measurable fun p : QConfig × (ℝ≥0 × Bool) => nextC p.1.1 p.2.2 :=
    (measurable_of_countable fun q : ℕ × Bool => nextC q.1 q.2).comp
      (measurable_fst.fst.prodMk measurable_snd.snd)
  have hlt : MeasurableSet {p : QConfig × (ℝ≥0 × Bool) | p.1.2.2.1 < p.1.2.1} :=
    measurableSet_lt ht hρ
  refine Measurable.ite ((hC (measurableSet_singleton 0)).union hlt)
    measurable_fst (Measurable.ite (hn (measurableSet_singleton 0)) ?_ ?_)
  · exact measurable_const.prodMk (measurable_const.prodMk ((ht.sub hρ).prodMk (hβ.add hρ)))
  · exact hn.prodMk (hs.prodMk ((ht.sub hρ).prodMk (hβ.add hρ)))

/-- The initial configuration is measurable. -/
theorem measurable_qinit : Measurable qinit := by
  classical
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst.snd) ?_ ?_
  · exact (measurable_fst.fst.add_const 2).prodMk (measurable_fst.snd.prodMk
      (measurable_snd.fst.prodMk measurable_const))
  · exact (measurable_fst.fst.add_const 1).prodMk (measurable_snd.snd.prodMk
      (measurable_snd.fst.prodMk measurable_const))

/-- The read-off state is measurable. -/
theorem measurable_qout : Measurable qout := by
  classical
  refine Measurable.ite (measurable_fst (measurableSet_singleton 0)) measurable_const ?_
  exact ((measurable_of_countable fun C : ℕ => C - 1).comp measurable_fst).prodMk
    (measurable_snd.fst.sub measurable_snd.snd.fst)

/-- Each configuration of the interval is a measurable function of the state and innovations. -/
theorem measurable_qcfg (k : ℕ) : Measurable fun p : (ℕ × ℝ≥0) × QNoise => qcfg p k := by
  induction k with
  | zero =>
    exact measurable_qinit.comp (measurable_fst.prodMk
      (measurable_snd.fst.prodMk measurable_snd.snd.fst))
  | succ k ih =>
    exact measurable_cstep.comp (ih.prodMk
      ((measurable_pi_apply (k + 1)).comp measurable_snd.snd.snd))

/-- Being final is a measurable event. -/
theorem measurableSet_isFinal : MeasurableSet {y : QConfig | y.IsFinal} := by
  have hlt : MeasurableSet {y : QConfig | y.2.2.1 < y.2.1} :=
    measurableSet_lt measurable_snd.snd.fst measurable_snd.fst
  exact (measurable_fst (measurableSet_singleton 0)).union hlt

/-- The step of the queue is measurable. -/
theorem measurable_gig1rStep : Measurable gig1rStep := by
  classical
  have hB : MeasurableSet {p : (ℕ × ℝ≥0) × QNoise | ¬ ∃ j, (qcfg p j).IsFinal} := by
    have : {p : (ℕ × ℝ≥0) × QNoise | ¬ ∃ j, (qcfg p j).IsFinal} =
        (⋃ j, (fun p => qcfg p j) ⁻¹' {y | y.IsFinal})ᶜ := by
      ext p; simp
    rw [this]
    exact (MeasurableSet.iUnion fun j => (measurable_qcfg j) measurableSet_isFinal).compl
  have hp : ∀ k, MeasurableSet {p : (ℕ × ℝ≥0) × QNoise |
      (qcfg p k).IsFinal ∨ ¬ ∃ j, (qcfg p j).IsFinal} := fun k =>
    ((measurable_qcfg k) measurableSet_isFinal).union hB
  exact Measurable.find (fun k => measurable_qout.comp (measurable_qcfg k)) hp
    exists_isFinal_or

/-! ### The chain -/

/-- The innovation law is a probability. -/
theorem isProbabilityMeasure_gig1rNoise (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsProbabilityMeasure (gig1rNoise G H r) := by
  have := isProbabilityMeasure_exitLaw h0 h1
  unfold gig1rNoise
  infer_instance

/-- The kernel of the queue is a Markov kernel. -/
theorem isMarkovKernel_gig1rKernel (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsMarkovKernel (gig1rKernel G H r) := by
  have := isProbabilityMeasure_gig1rNoise G H h0 h1
  exact isMarkovKernel_recursionKernel _ measurable_gig1rStep

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- **`Φ` is a Markov chain** (MT p. 274): if `Φₙ₊₁ = F(Φₙ, ξₙ₊₁)` with the interval innovations
`ξ₁, ξ₂, …` i.i.d. with law `G ⊗ H ⊗ (H ⊗ Bernoulli(r))^{⊗ℕ}` and independent of `Φ₀ ∼ μ`, then
`Φ` is a Markov chain with kernel `gig1rKernel G H r` (`isMarkovChain_of_iid`). -/
theorem gig1r_isMarkovChain (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (μ : Measure (ℕ × ℝ≥0))
    [IsProbabilityMeasure μ] {pr : Measure Ω} [IsProbabilityMeasure pr]
    {Φ : ℕ → Ω → ℕ × ℝ≥0} {ξ : ℕ → Ω → QNoise} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = gig1rStep (Φ n ω, ξ (n + 1) ω)) (hinit : pr.map (Φ 0) = μ)
    (hξ : IsIIDNoise pr (Φ 0) ξ (gig1rNoise G H r)) :
    haveI := isMarkovKernel_gig1rKernel G H h0 h1
    IsMarkovChain (gig1rKernel G H r) μ pr Φ := by
  have := isProbabilityMeasure_gig1rNoise G H h0 h1
  exact isMarkovChain_of_iid μ _ measurable_gig1rStep hΦ0 hrec hinit hξ

/-! ### Final configurations -/

/-- A final configuration is left unchanged by the event step. -/
theorem cstep_of_isFinal {y : QConfig} (hy : y.IsFinal) (w : ℝ≥0 × Bool) :
    cstep (y, w) = y := by
  have h : y.1 = 0 ∨ y.2.2.1 < y.2.1 := hy
  unfold cstep
  simp only [h, ↓reduceIte]

/-- Once final, the configurations of the interval stay put. -/
theorem qcfg_of_isFinal {p : (ℕ × ℝ≥0) × QNoise} {k : ℕ} (hk : (qcfg p k).IsFinal) (j : ℕ) :
    qcfg p (k + j) = qcfg p k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change cstep (qcfg p (k + j), p.2.2.2 (k + j + 1)) = qcfg p k
    rw [ih, cstep_of_isFinal hk]

/-- **The step reads off any final configuration**: if the `k`-th configuration is final, then
`F(x, ξ) = out(y_k)`. -/
theorem gig1rStep_eq {p : (ℕ × ℝ≥0) × QNoise} {k : ℕ} (hk : (qcfg p k).IsFinal) :
    gig1rStep p = qout (qcfg p k) := by
  classical
  have hex : ∃ j, (qcfg p j).IsFinal := ⟨k, hk⟩
  have hspec := Nat.find_spec (exists_isFinal_or p)
  have hK : (qcfg p (Nat.find (exists_isFinal_or p))).IsFinal := hspec.resolve_right (not_not.2 hex)
  have hle : Nat.find (exists_isFinal_or p) ≤ k := Nat.find_min' _ (Or.inl hk)
  unfold gig1rStep
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj, qcfg_of_isFinal hK j]

/-- The event step from a configuration that is not final. -/
theorem cstep_of_not_isFinal {y : QConfig} (hy : ¬ y.IsFinal) (s : ℝ≥0) (e : Bool) :
    cstep (y, (s, e)) = if nextC y.1 e = 0 then (0, 0, y.2.2.1 - y.2.1, y.2.2.2 + y.2.1)
      else (nextC y.1 e, s, y.2.2.1 - y.2.1, y.2.2.2 + y.2.1) := by
  have h : ¬ (y.1 = 0 ∨ y.2.2.1 < y.2.1) := hy
  unfold cstep
  simp only [h, ↓reduceIte]

/-- The `(k + 1)`-th configuration is the event step of the `k`-th with the `(k + 1)`-th
innovation pair. -/
theorem qcfg_succ (p : (ℕ × ℝ≥0) × QNoise) (k : ℕ) :
    qcfg p (k + 1) = cstep (qcfg p k, p.2.2.2 (k + 1)) := rfl

/-- The initial configuration has `N + 1` or `N + 2` customers. -/
theorem qcfg_zero_fst (p : (ℕ × ℝ≥0) × QNoise) :
    (qcfg p 0).1 = if 0 < p.1.2 then p.1.1 + 2 else p.1.1 + 1 := by
  change (qinit (p.1, (p.2.1, p.2.2.1))).1 = _
  unfold qinit
  split_ifs <;> rfl

/-! ### Proposition 11.4.3: reaching the empty state -/

/-- The potential `Ψ(N, R) = R + N a` of the proof of Proposition 11.4.3. -/
noncomputable def qpot (a : ℝ) (x : ℕ × ℝ≥0) : ℝ := x.2 + x.1 * a

/-- The potential of a configuration, `ρ − t + (C − 1) a`; at a final busy configuration it is
the potential of the state read off. -/
noncomputable def cpot (a : ℝ) (y : QConfig) : ℝ := y.2.1 - y.2.2.1 + ((y.1 : ℝ) - 1) * a

/-- The good event of one interval (MT p. 274): the interarrival time exceeds `a + δ`, and the
first `n + 3` services started in the interval are shorter than `a` and end in departures. -/
def goodNoise (a δ : ℝ) (n : ℕ) : Set QNoise :=
  {ξ | a + δ < ξ.1 ∧ (ξ.2.1 : ℝ) < a ∧
    ∀ j ∈ Finset.Icc 1 (n + 2), ((ξ.2.2 j).1 : ℝ) < a ∧ (ξ.2.2 j).2 = true}

/-- **One good interval** (MT p. 274). If `N ≤ n` and the innovations are good, the queue either
empties or its potential `R + N a` drops by more than `δ`, with at most `n + 1` customers
waiting. -/
theorem good_step {a δ : ℝ} {n : ℕ} {x : ℕ × ℝ≥0} (hxn : x.1 ≤ n) {ξ : QNoise}
    (hξ : ξ ∈ goodNoise a δ n) :
    gig1rStep (x, ξ) = (0, 0) ∨
      (qpot a (gig1rStep (x, ξ)) < qpot a x - δ ∧ (gig1rStep (x, ξ)).1 ≤ n + 1) := by
  obtain ⟨hτ, hs0, hgood⟩ := hξ
  set p : (ℕ × ℝ≥0) × QNoise := (x, ξ) with hp
  set C₀ := (qcfg p 0).1 with hC₀def
  have hC₀ := qcfg_zero_fst p
  rw [← hC₀def] at hC₀
  have hC₀n : C₀ ≤ n + 2 := by
    rw [hC₀]; split_ifs <;> simp only [hp] <;> omega
  -- the initial potential
  have h0 : cpot a (qcfg p 0) < qpot a x - δ := by
    change cpot a (qinit (x, (ξ.1, ξ.2.1))) < _
    unfold qinit cpot qpot
    split_ifs with hR
    · simp only
      push_cast
      linarith
    · simp only
      have hR0 : (x.2 : ℝ) = 0 := by
        have : x.2 = 0 := le_antisymm (not_lt.1 hR) zero_le
        rw [this, NNReal.coe_zero]
      push_cast
      rw [hR0]
      linarith
  -- the invariant along the interval
  have hinv : ∀ k, k ≤ C₀ → (qcfg p k).1 = 0 ∨ (cpot a (qcfg p k) < qpot a x - δ ∧
      (qcfg p k).1 ≤ C₀ ∧ ((qcfg p k).IsFinal ∨ (qcfg p k).1 + k ≤ C₀)) := by
    intro k
    induction k with
    | zero => exact fun _ => Or.inr ⟨h0, le_rfl, Or.inr (by omega)⟩
    | succ k ih =>
      intro hk
      rw [qcfg_succ]
      rcases ih (by omega) with hz | ⟨hpot, hle, hfin | hcnt⟩
      · rw [cstep_of_isFinal (Or.inl hz)]; exact Or.inl hz
      · rw [cstep_of_isFinal hfin]; exact Or.inr ⟨hpot, hle, Or.inl hfin⟩
      · by_cases hfin : (qcfg p k).IsFinal
        · rw [cstep_of_isFinal hfin]; exact Or.inr ⟨hpot, hle, Or.inl hfin⟩
        · have hj := hgood (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
          obtain ⟨hs, he⟩ := hj
          have hpair : p.2.2.2 (k + 1) = ((ξ.2.2 (k + 1)).1, true) := by
            rw [hp]; exact Prod.ext rfl he
          rw [hpair, cstep_of_not_isFinal hfin]
          have hnf : ¬ ((qcfg p k).1 = 0 ∨ (qcfg p k).2.2.1 < (qcfg p k).2.1) := hfin
          push Not at hnf
          obtain ⟨hC1, hρt⟩ := hnf
          simp only [nextC, ↓reduceIte]
          split_ifs with hz
          · exact Or.inl rfl
          · refine Or.inr ⟨?_, by omega, Or.inr (by omega)⟩
            unfold cpot at hpot ⊢
            simp only
            rw [NNReal.coe_sub hρt, Nat.cast_sub (by omega : 1 ≤ (qcfg p k).1)]
            push_cast
            linarith
  -- at `k = C₀` the configuration is final
  have hfinal : (qcfg p C₀).IsFinal := by
    rcases hinv C₀ le_rfl with hz | ⟨-, -, hfin | hcnt⟩
    · exact Or.inl hz
    · exact hfin
    · exact Or.inl (by omega)
  rw [gig1rStep_eq hfinal]
  rcases hinv C₀ le_rfl with hz | ⟨hpot, hle, -⟩
  · left
    unfold qout
    simp only [hz, ↓reduceIte]
  · by_cases hz : (qcfg p C₀).1 = 0
    · left
      unfold qout
      simp only [hz, ↓reduceIte]
    · right
      have hlt : (qcfg p C₀).2.2.1 < (qcfg p C₀).2.1 := hfinal.resolve_left hz
      unfold qout
      simp only [hz, ↓reduceIte]
      refine ⟨?_, by omega⟩
      unfold qpot at hpot ⊢
      unfold cpot at hpot
      simp only
      rw [NNReal.coe_sub hlt.le, Nat.cast_sub (by omega : 1 ≤ (qcfg p C₀).1)]
      push_cast
      linarith

/-- The probability of the good event: `G(a + δ, ∞) H[0, a) (r H[0, a))^{n+2}`. -/
noncomputable def goodProb (G H : Measure ℝ≥0) (r a δ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  G {t | a + δ < (t : ℝ)} * (H {s | (s : ℝ) < a} *
    (H {s | (s : ℝ) < a} * ENNReal.ofReal r) ^ (n + 2))

/-- The good event is a product set. -/
theorem goodNoise_eq (a δ : ℝ) (n : ℕ) :
    goodNoise a δ n = {t : ℝ≥0 | a + δ < (t : ℝ)} ×ˢ ({s : ℝ≥0 | (s : ℝ) < a} ×ˢ
      Set.pi (Finset.Icc 1 (n + 2) : Set ℕ)
        (fun _ => {s : ℝ≥0 | (s : ℝ) < a} ×ˢ ({true} : Set Bool))) := by
  ext ξ
  simp only [goodNoise, mem_ofPred_eq, mem_prod, Set.mem_pi, Finset.coe_Icc, mem_Icc,
    Finset.mem_Icc, mem_singleton_iff]

/-- The good event is measurable. -/
theorem measurableSet_goodNoise (a δ : ℝ) (n : ℕ) : MeasurableSet (goodNoise a δ n) := by
  have hA : MeasurableSet {t : ℝ≥0 | a + δ < (t : ℝ)} :=
    measurableSet_lt measurable_const measurable_coe_nnreal_real
  have hB : MeasurableSet {s : ℝ≥0 | (s : ℝ) < a} :=
    measurableSet_lt measurable_coe_nnreal_real measurable_const
  rw [goodNoise_eq]
  exact hA.prod (hB.prod (MeasurableSet.pi (Finset.countable_toSet _)
    fun _ _ => hB.prod (measurableSet_singleton true)))

/-- The good event has probability `goodProb`. -/
theorem gig1rNoise_goodNoise (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (a δ : ℝ) (n : ℕ) :
    gig1rNoise G H r (goodNoise a δ n) = goodProb G H r a δ n := by
  have := isProbabilityMeasure_exitLaw h0 h1
  have hB : MeasurableSet {s : ℝ≥0 | (s : ℝ) < a} :=
    measurableSet_lt measurable_coe_nnreal_real measurable_const
  have hS : MeasurableSet ({s : ℝ≥0 | (s : ℝ) < a} ×ˢ ({true} : Set Bool)) :=
    hB.prod (measurableSet_singleton true)
  rw [goodNoise_eq, gig1rNoise, Measure.prod_prod, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun _ _ => hS)]
  simp only [Measure.prod_prod, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hT : exitLaw r {true} = ENNReal.ofReal r := by
    simp [exitLaw]
  rw [hT]
  rfl

/-- `goodProb` is positive when `G(a + δ, ∞) > 0`, `H[0, a) > 0` and `r > 0`. -/
theorem goodProb_pos {G H : Measure ℝ≥0} {r a δ : ℝ} (hG : 0 < G {t | a + δ < (t : ℝ)})
    (hH : 0 < H {s | (s : ℝ) < a}) (hr : 0 < r) (n : ℕ) : 0 < goodProb G H r a δ n := by
  unfold goodProb
  refine ENNReal.mul_pos hG.ne' (ENNReal.mul_pos hH.ne' (pow_ne_zero _ (ENNReal.mul_pos hH.ne'
    (ENNReal.ofReal_pos.2 hr).ne').ne')).ne'

/-- `P(x, ·)` integrates `f` as `E f(F(x, ξ))`. -/
theorem lintegral_gig1rKernel (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (x : ℕ × ℝ≥0)
    {f : ℕ × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂gig1rKernel G H r x = ∫⁻ ξ, f (gig1rStep (x, ξ)) ∂gig1rNoise G H r := by
  have := isProbabilityMeasure_gig1rNoise G H h0 h1
  rw [gig1rKernel, recursionKernel_apply _ measurable_gig1rStep x,
    lintegral_map (g := fun ξ => gig1rStep (x, ξ)) hf
      (measurable_gig1rStep.comp measurable_prodMk_left)]

/-- **Reaching `[0]` in `k + 1` steps** (proof of Proposition 11.4.3): if `N ≤ n` and
`R + N a ≤ kδ`, then `P^{k+1}(x, [0]) ≥ ∏_{i ≤ k} goodProb(n + i)`; by induction, each good
interval empties the queue or lowers the potential by `δ`, and from `[0]` a good interval
returns to `[0]`. -/
theorem gig1r_reach_zero (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {a δ : ℝ} (ha : 0 ≤ a)
    (hδ : 0 ≤ δ) (k : ℕ) : ∀ (n : ℕ) (x : ℕ × ℝ≥0), x.1 ≤ n → qpot a x ≤ k * δ →
      ∏ i ∈ Finset.range (k + 1), goodProb G H r a δ (n + i) ≤
        (gig1rKernel G H r ^ (k + 1)) x {((0 : ℕ), (0 : ℝ≥0))} := by
  have := isMarkovKernel_gig1rKernel G H h0 h1
  have := isProbabilityMeasure_gig1rNoise G H h0 h1
  have hZm : MeasurableSet ({((0 : ℕ), (0 : ℝ≥0))} : Set (ℕ × ℝ≥0)) := measurableSet_singleton _
  have hzero : qpot a ((0 : ℕ), (0 : ℝ≥0)) = 0 := by simp [qpot]
  have hstep : ∀ (n : ℕ) (x : ℕ × ℝ≥0) (j : ℕ) (c : ℝ≥0∞), x.1 ≤ n →
      (∀ ξ ∈ goodNoise a δ n,
        c ≤ (gig1rKernel G H r ^ j) (gig1rStep (x, ξ)) {((0 : ℕ), (0 : ℝ≥0))}) →
      goodProb G H r a δ n * c ≤
        (gig1rKernel G H r ^ (j + 1)) x {((0 : ℕ), (0 : ℝ≥0))} := by
    intro n x j c _ hc
    rw [pow_succ]
    change goodProb G H r a δ n * c ≤ ((gig1rKernel G H r ^ j) ∘ₖ gig1rKernel G H r) x _
    rw [Kernel.comp_apply' _ _ _ hZm,
      lintegral_gig1rKernel G H h0 h1 x (Kernel.measurable_coe _ hZm),
      ← gig1rNoise_goodNoise G H h0 h1 a δ n, mul_comm, ← setLIntegral_const]
    exact (setLIntegral_mono ((Kernel.measurable_coe _ hZm).comp
      (measurable_gig1rStep.comp measurable_prodMk_left)) hc).trans
      (setLIntegral_le_lintegral _ _)
  induction k with
  | zero =>
    intro n x hxn hx
    rw [Finset.prod_range_one, add_zero]
    have h := hstep n x 0 1 hxn fun ξ hξ => by
      rcases good_step hxn hξ with h | ⟨h, -⟩
      · rw [h, pow_zero]
        change (1 : ℝ≥0∞) ≤ Kernel.id ((0 : ℕ), (0 : ℝ≥0)) {((0 : ℕ), (0 : ℝ≥0))}
        rw [Kernel.id_apply, Measure.dirac_apply_of_mem (mem_singleton _)]
      · exfalso
        have : 0 ≤ qpot a (gig1rStep (x, ξ)) := by unfold qpot; positivity
        push_cast at hx
        linarith
    rwa [mul_one, zero_add] at h
  | succ k ih =>
    intro n x hxn hx
    rw [Finset.prod_range_succ']
    have h := hstep n x (k + 1) (∏ i ∈ Finset.range (k + 1), goodProb G H r a δ (n + 1 + i))
      hxn fun ξ hξ => by
        rcases good_step hxn hξ with h | ⟨h, hN⟩
        · rw [h]
          exact ih (n + 1) _ (Nat.zero_le _) (by rw [hzero]; positivity)
        · refine ih (n + 1) _ hN ?_
          push_cast at hx
          linarith
    calc (∏ i ∈ Finset.range (k + 1), goodProb G H r a δ (n + (i + 1))) *
          goodProb G H r a δ (n + 0) =
        goodProb G H r a δ n * ∏ i ∈ Finset.range (k + 1), goodProb G H r a δ (n + 1 + i) := by
          rw [mul_comm, add_zero]
          congr 1
          exact Finset.prod_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]
      _ ≤ _ := h

/-- If `E S < E T`, there are `a, δ > 0` with `H[0, a) > 0` and `G(a + δ, ∞) > 0` (MT p. 274:
"with positive probability each interarrival time exceeds each service time by `δ`"). -/
theorem exists_good_constants (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] (hG : Integrable (fun t : ℝ≥0 => (t : ℝ)) G)
    (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H)
    (hlt : ∫ s, (s : ℝ) ∂H < ∫ t, (t : ℝ) ∂G) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ 0 < G {t | a + δ < (t : ℝ)} ∧ 0 < H {s | (s : ℝ) < a} := by
  set m := ∫ s, (s : ℝ) ∂H with hm
  set T := ∫ t, (t : ℝ) ∂G with hT
  have hm0 : 0 ≤ m := integral_nonneg fun s => s.2
  refine ⟨(2 * m + T) / 3, (T - m) / 3, by linarith, by linarith, ?_, ?_⟩
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    have hae : ∀ᵐ t ∂G, ((t : ℝ≥0) : ℝ) ≤ (2 * m + T) / 3 + (T - m) / 3 := by
      rw [ae_iff]
      simpa only [not_le] using h0
    have := integral_mono_ae hG (integrable_const _) hae
    rw [integral_const, probReal_univ, one_smul] at this
    linarith
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    have hae : ∀ᵐ s ∂H, (2 * m + T) / 3 ≤ ((s : ℝ≥0) : ℝ) := by
      rw [ae_iff]
      simpa only [not_le] using h0
    have := integral_mono_ae (integrable_const _) hH hae
    rw [integral_const, probReal_univ, one_smul] at this
    linarith

/-- Under `E S < E T` every state reaches `[0]`: `P^{k+1}(x, [0]) > 0` for some `k`, with a lower
bound uniform over `{N ≤ n, R + N a ≤ kδ}`. -/
theorem gig1r_exists_reach (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hG : Integrable (fun t : ℝ≥0 => (t : ℝ)) G) (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H)
    (hlt : ∫ s, (s : ℝ) ∂H < ∫ t, (t : ℝ) ∂G) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ ∀ (k n : ℕ), ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ x : ℕ × ℝ≥0, x.1 ≤ n →
      qpot a x ≤ k * δ → ε ≤ (gig1rKernel G H r ^ (k + 1)) x {((0 : ℕ), (0 : ℝ≥0))} := by
  obtain ⟨a, δ, ha, hδ, hGa, hHa⟩ := exists_good_constants G H hG hH hlt
  refine ⟨a, δ, ha, hδ, fun k n => ⟨_, ?_, fun x hxn hx =>
    gig1r_reach_zero G H hr0.le hr1 ha.le hδ.le k n x hxn hx⟩⟩
  exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ =>
    (goodProb_pos hGa hHa hr0 _).ne')

/-- **Proposition 11.4.3** (MT p. 275). Under the load condition (11.32), `ρ_r = λ_r/μ < 1`,
i.e. `E S / r < E T`, the GI/G/1 queue with re-entry is `δ_{[0]}`-irreducible, strongly
aperiodic (`{[0]}` is a small set charged by its minorizing measure) and aperiodic, and every
compact subset of `ℤ₊ × ℝ₊` is petite (indeed small). Only `E S < E T` is used. -/
theorem proposition_11_4_3 (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hG : Integrable (fun t : ℝ≥0 => (t : ℝ)) G) (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H)
    (hload : (∫ s, (s : ℝ) ∂H) / r < ∫ t, (t : ℝ) ∂G) :
    haveI := isMarkovKernel_gig1rKernel G H hr0.le hr1
    IsPhiIrreducible (gig1rKernel G H r) (Measure.dirac ((0 : ℕ), (0 : ℝ≥0))) ∧
      IsMaximalIrreducibility (gig1rKernel G H r)
        (maxIrrMeasure (gig1rKernel G H r) (Measure.dirac ((0 : ℕ), (0 : ℝ≥0)))) ∧
      IsStronglyAperiodic (gig1rKernel G H r) ∧
      IsAperiodic (gig1rKernel G H r)
        (maxIrrMeasure (gig1rKernel G H r) (Measure.dirac ((0 : ℕ), (0 : ℝ≥0)))) ∧
      ∀ K : Set (ℕ × ℝ≥0), IsCompact K → IsPetite (gig1rKernel G H r) K := by
  have := isMarkovKernel_gig1rKernel G H hr0.le hr1
  set P := gig1rKernel G H r with hP
  set z : ℕ × ℝ≥0 := ((0 : ℕ), (0 : ℝ≥0)) with hz
  have hm0 : 0 ≤ ∫ s, (s : ℝ) ∂H := integral_nonneg fun s => s.2
  have hlt : ∫ s, (s : ℝ) ∂H < ∫ t, (t : ℝ) ∂G := by
    have : (∫ s, (s : ℝ) ∂H) / 1 ≤ (∫ s, (s : ℝ) ∂H) / r :=
      div_le_div_of_nonneg_left hm0 hr0 hr1
    rw [div_one] at this
    linarith
  obtain ⟨a, δ, ha, hδ, hreach⟩ := gig1r_exists_reach G H hr0 hr1 hG hH hlt
  have hZm : MeasurableSet ({z} : Set (ℕ × ℝ≥0)) := measurableSet_singleton _
  -- every state reaches `[0]`
  have hx : ∀ x : ℕ × ℝ≥0, ∃ k, 0 < (P ^ (k + 1)) x {z} := fun x => by
    obtain ⟨ε, hε, hb⟩ := hreach ⌈qpot a x / δ⌉₊ x.1
    refine ⟨⌈qpot a x / δ⌉₊, hε.trans_le (hb x le_rfl ?_)⟩
    have := Nat.le_ceil (qpot a x / δ)
    rwa [div_le_iff₀ hδ] at this
  have hirr : IsPhiIrreducible P (Measure.dirac z) := by
    refine isPhiIrreducible_of_pow_pos fun A hA hpos x => ?_
    have hzA : z ∈ A := by
      by_contra h
      rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨k, hk⟩ := hx x
    exact ⟨k + 1, hk.trans_le (measure_mono (singleton_subset_iff.2 hzA))⟩
  have hmax := isMaximalIrreducibility_maxIrrMeasure P hirr (Measure.dirac_ne_zero)
  -- `{[0]}` is small at time `1`
  obtain ⟨ε₀, hε₀, hb₀⟩ := hreach 0 0
  have hνz : 0 < (ε₀ • Measure.dirac z) {z} := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_singleton z), mul_one]
    exact hε₀
  have hν0 : ε₀ • Measure.dirac z ≠ 0 := fun h => by
    rw [h, Measure.coe_zero, Pi.zero_apply] at hνz
    exact lt_irrefl _ hνz
  have hsmall : IsSmallSet P 1 (ε₀ • Measure.dirac z) {z} := by
    refine ⟨hZm, one_pos, hν0, fun x hx' => ?_⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    refine Measure.le_intro fun B hB _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
    by_cases hzB : z ∈ B
    · rw [indicator_of_mem hzB, Pi.one_apply, mul_one]
      refine (hb₀ z le_rfl (by simp [hz, qpot])).trans ?_
      rw [zero_add]
      exact measure_mono (singleton_subset_iff.2 hzB)
    · rw [indicator_of_notMem hzB, mul_zero]
      exact zero_le
  have hψz : 0 < maxIrrMeasure P (Measure.dirac z) {z} := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := hmax.2.2 _ hirr h0
    rw [Measure.dirac_apply_of_mem (mem_singleton z)] at this
    exact one_ne_zero this
  refine ⟨hirr, hmax, ⟨_, _, hsmall, hνz⟩, ?_, fun K hK => ?_⟩
  · have hper := isPeriod_gcd P hmax hsmall hψz hνz
    have h1 := mem_smallTimes_of_isSmallSet hsmall
    have hd := setGcd_dvd (smallTimes_isAddClosed P hνz) h1 one_pos h1
    rwa [Nat.dvd_one.1 hd] at hper
  · -- a compact set is bounded, hence uniformly reaches `[0]`
    obtain ⟨n₀, hn₀⟩ := (hK.image continuous_fst).bddAbove
    obtain ⟨R₀, hR₀⟩ := (hK.image (NNReal.continuous_coe.comp continuous_snd)).bddAbove
    set k := ⌈(R₀ + n₀ * a) / δ⌉₊ with hk
    obtain ⟨ε, hε, hb⟩ := hreach k n₀
    have hν0' : ε • Measure.dirac z ≠ 0 := fun h => by
      have h1 : (ε • Measure.dirac z) {z} = ε := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_singleton z),
          mul_one]
      rw [h, Measure.coe_zero, Pi.zero_apply] at h1
      exact hε.ne' h1.symm
    have hKs : IsSmallSet P (k + 1) (ε • Measure.dirac z) K := by
      refine ⟨hK.isClosed.measurableSet, Nat.succ_pos k, hν0', fun x hxK => ?_⟩
      have hxn : x.1 ≤ n₀ := hn₀ ⟨x, hxK, rfl⟩
      have hxR : (x.2 : ℝ) ≤ R₀ := hR₀ ⟨x, hxK, rfl⟩
      have hq : qpot a x ≤ k * δ := by
        have h1 := Nat.le_ceil ((R₀ + n₀ * a) / δ)
        rw [div_le_iff₀ hδ] at h1
        have h2 : (x.1 : ℝ) * a ≤ n₀ * a :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hxn) ha.le
        unfold qpot
        rw [← hk] at h1
        linarith
      refine Measure.le_intro fun B hB _ => ?_
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
      by_cases hzB : z ∈ B
      · rw [indicator_of_mem hzB, Pi.one_apply, mul_one]
        exact (hb x hxn hq).trans (measure_mono (singleton_subset_iff.2 hzB))
      · rw [indicator_of_notMem hzB, mul_zero]
        exact zero_le
    exact IsSmall.isPetite ⟨_, _, hKs⟩

/-! ### Proposition 11.4.4: the expected work -/

/-- The expected remaining work of a configuration (MT p. 275): the residual `ρ` of the customer
in service, `(1 − r)m/r` for its expected re-entries, and `m/r` for each of the `C − 1` waiting
customers (`m = E S`); `0` for an empty system. -/
noncomputable def qwork (m r : ℝ) (y : QConfig) : ℝ :=
  open Classical in
  if y.1 = 0 then 0 else y.2.1 + ((y.1 : ℝ) - r) * (m / r)

/-- The expected remaining work plus the busy time so far: a martingale in event time. -/
noncomputable def cwork (m r : ℝ) (y : QConfig) : ℝ := qwork m r y + y.2.2.2

/-- **The expected work** `V(x) = E_x[W₀]` (MT p. 275): the expected total service time still
to be given to the customers present at `T₀+` (the arriving one included), from `(N, R)` at
`T₀−`: `(N + 1) m/r` if the server is free, `R + (N + 2 − r) m/r` otherwise. -/
noncomputable def qworkV (m r : ℝ) (x : ℕ × ℝ≥0) : ℝ :=
  open Classical in
  if x.2 = 0 then ((x.1 : ℝ) + 1) * (m / r) else x.2 + ((x.1 : ℝ) + 2 - r) * (m / r)

/-- The busy time of the server in an interval, read off a final configuration. -/
noncomputable def busyfin (y : QConfig) : ℝ :=
  open Classical in
  y.2.2.2 + if y.1 = 0 then 0 else y.2.2.1

/-- `cwork` is measurable. -/
theorem measurable_cwork (m r : ℝ) : Measurable (cwork m r) := by
  classical
  refine Measurable.add (Measurable.ite (measurable_fst (measurableSet_singleton 0))
    measurable_const ?_) (measurable_coe_nnreal_real.comp measurable_snd.snd.snd)
  exact (measurable_coe_nnreal_real.comp measurable_snd.fst).add
    ((((measurable_of_countable (fun C : ℕ => (C : ℝ))).comp measurable_fst).sub_const _).mul_const
      _)

/-- `cwork ≥ 0`. -/
theorem cwork_nonneg {m r : ℝ} (hm : 0 ≤ m) (hr0 : 0 < r) (hr1 : r ≤ 1) (y : QConfig) :
    0 ≤ cwork m r y := by
  unfold cwork qwork
  split_ifs with h
  · simp
  · have hC : (1 : ℝ) ≤ y.1 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    have : 0 ≤ ((y.1 : ℝ) - r) * (m / r) := mul_nonneg (by linarith) (div_nonneg hm hr0.le)
    positivity

/-- **The work identity at the end of an interval**: for a final configuration,
`V(out(y)) + busy(y) = cwork(y) + m/r`. -/
theorem qworkV_qout_add_busyfin (m r : ℝ) {y : QConfig} (hy : y.IsFinal) :
    qworkV m r (qout y) + busyfin y = cwork m r y + m / r := by
  unfold qworkV qout busyfin cwork qwork
  by_cases hC : y.1 = 0
  · simp only [hC, ↓reduceIte]
    push_cast
    ring
  · have hlt : y.2.2.1 < y.2.1 := hy.resolve_left hC
    have hne : y.2.1 - y.2.2.1 ≠ 0 := (tsub_pos_of_lt hlt).ne'
    simp only [hC, hne, ↓reduceIte]
    rw [NNReal.coe_sub hlt.le, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hC)]
    push_cast
    ring

/-- `∫ (c + d s) H(ds) = c + d m`. -/
theorem integral_const_add_mul_nnreal (H : Measure ℝ≥0) [IsProbabilityMeasure H]
    (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H) (c d : ℝ) :
    ∫ s, (c + d * (s : ℝ)) ∂H = c + d * ∫ s, (s : ℝ) ∂H := by
  rw [integral_add (integrable_const _) (hH.const_mul d), integral_const, integral_const_mul,
    probReal_univ, one_smul]

/-- `∫⁻ g d(Bernoulli(r)) = r g(true) + (1 − r) g(false)`. -/
theorem lintegral_exitLaw (r : ℝ) (g : Bool → ℝ≥0∞) :
    ∫⁻ e, g e ∂exitLaw r = ENNReal.ofReal r * g true + ENNReal.ofReal (1 - r) * g false := by
  rw [exitLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  rfl

/-- **One event preserves the expected work plus busy time**: `E cwork(step(y, (S, e))) =
cwork(y)` with `S ∼ H`, `e ∼ Bernoulli(r)` (a customer completing service leaves with
probability `r`; otherwise it re-enters, and each fresh service has mean `m`). -/
theorem lintegral_cwork_cstep (H : Measure ℝ≥0) [IsProbabilityMeasure H]
    (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (y : QConfig) :
    ∫⁻ w, ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r (cstep (y, w))) ∂H.prod (exitLaw r) =
      ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r y) := by
  have := isProbabilityMeasure_exitLaw hr0.le hr1
  set m := ∫ s, (s : ℝ) ∂H with hm
  have hm0 : 0 ≤ m := integral_nonneg fun s => s.2
  by_cases hfin : y.IsFinal
  · simp_rw [cstep_of_isFinal hfin]
    rw [lintegral_const, measure_univ, mul_one]
  have hnf : ¬ (y.1 = 0 ∨ y.2.2.1 < y.2.1) := hfin
  push Not at hnf
  obtain ⟨hC, hρt⟩ := hnf
  have hC1 : (1 : ℝ) ≤ y.1 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hC
  have hmr : 0 ≤ m / r := div_nonneg hm0 hr0.le
  -- the two branches
  set T : ℝ → ℝ := fun s => (if y.1 = 1 then 0 else s + ((y.1 : ℝ) - 1 - r) * (m / r)) +
    y.2.2.2 + y.2.1 with hT
  set Fb : ℝ → ℝ := fun s => s + ((y.1 : ℝ) - r) * (m / r) + y.2.2.2 + y.2.1 with hFb
  have hTe : ∀ s : ℝ≥0, cwork m r (cstep (y, (s, true))) = T s := fun s => by
    rw [cstep_of_not_isFinal hfin]
    simp only [nextC, ↓reduceIte, hT]
    by_cases h1 : y.1 = 1
    · simp only [h1, Nat.sub_self, ↓reduceIte, cwork, qwork]
      push_cast
      ring
    · have h2 : y.1 - 1 ≠ 0 := by omega
      simp only [h2, h1, ↓reduceIte, cwork, qwork]
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hC), NNReal.coe_add]
      push_cast
      ring
  have hFe : ∀ s : ℝ≥0, cwork m r (cstep (y, (s, false))) = Fb s := fun s => by
    rw [cstep_of_not_isFinal hfin]
    simp only [nextC, Bool.false_eq_true, ↓reduceIte, hC, hFb, cwork, qwork]
    rw [NNReal.coe_add]
    ring
  have hT0 : ∀ s : ℝ≥0, 0 ≤ T s := fun s => by
    simp only [hT]
    split_ifs with h1
    · positivity
    · have h2 : (2 : ℝ) ≤ y.1 := by
        have : 2 ≤ y.1 := by omega
        exact_mod_cast this
      have : 0 ≤ ((y.1 : ℝ) - 1 - r) * (m / r) := mul_nonneg (by linarith) hmr
      positivity
  have hF0 : ∀ s : ℝ≥0, 0 ≤ Fb s := fun s => by
    simp only [hFb]
    have : 0 ≤ ((y.1 : ℝ) - r) * (m / r) := mul_nonneg (by linarith) hmr
    positivity
  have hmeas : Measurable fun w : ℝ≥0 × Bool => ENNReal.ofReal (cwork m r (cstep (y, w))) :=
    ENNReal.measurable_ofReal.comp ((measurable_cwork m r).comp
      (measurable_cstep.comp measurable_prodMk_left))
  rw [lintegral_prod _ hmeas.aemeasurable]
  simp_rw [lintegral_exitLaw, hTe, hFe]
  have hpt : ∀ s : ℝ≥0, ENNReal.ofReal r * ENNReal.ofReal (T s) +
      ENNReal.ofReal (1 - r) * ENNReal.ofReal (Fb s) =
      ENNReal.ofReal (r * T s + (1 - r) * Fb s) := fun s => by
    rw [← ENNReal.ofReal_mul hr0.le, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (mul_nonneg hr0.le (hT0 s)) (mul_nonneg (by linarith) (hF0 s))]
  simp_rw [hpt]
  -- the integrand is affine in `s`
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℝ, ∀ s : ℝ, r * T s + (1 - r) * Fb s = c + d * s := by
    by_cases h1 : y.1 = 1
    · refine ⟨r * (y.2.2.2 + y.2.1) + (1 - r) * (((y.1 : ℝ) - r) * (m / r) + y.2.2.2 + y.2.1),
        1 - r, fun s => ?_⟩
      simp only [hT, hFb, h1, ↓reduceIte]
      push_cast
      ring
    · refine ⟨r * (((y.1 : ℝ) - 1 - r) * (m / r) + y.2.2.2 + y.2.1) +
        (1 - r) * (((y.1 : ℝ) - r) * (m / r) + y.2.2.2 + y.2.1), 1, fun s => ?_⟩
      simp only [hT, hFb, h1, ↓reduceIte]
      ring
  have hint : Integrable (fun s : ℝ≥0 => r * T s + (1 - r) * Fb s) H := by
    simp_rw [hcd]
    exact (integrable_const _).add (hH.const_mul d)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun s =>
    add_nonneg (mul_nonneg hr0.le (hT0 s)) (mul_nonneg (by linarith) (hF0 s)))]
  congr 1
  simp_rw [hcd]
  rw [integral_const_add_mul_nnreal H hH, ← hm]
  have hc : c + d * m = r * T m + (1 - r) * Fb m := (hcd m).symm
  rw [hc]
  have hr : r ≠ 0 := hr0.ne'
  simp only [hT, hFb, cwork, qwork, hC, ↓reduceIte]
  by_cases h1 : y.1 = 1
  · simp only [h1, ↓reduceIte]
    push_cast
    field_simp
    ring
  · simp only [h1, ↓reduceIte]
    field_simp
    ring

/-- The kernel of the event chain inside an interval. -/
noncomputable def cKernel (H : Measure ℝ≥0) (r : ℝ) : Kernel QConfig QConfig :=
  recursionKernel (H.prod (exitLaw r)) cstep

/-- The `k`-th configuration is a measurable function of the event innovations. -/
theorem measurable_orbit_cstep (y : QConfig) (k : ℕ) :
    Measurable fun ω : ℕ → ℝ≥0 × Bool => orbit cstep y ω k := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact measurable_cstep.comp (ih.prodMk (measurable_pi_apply (k + 1)))

/-- `cwork` is harmonic for the event chain: `∫ Pcᵏ(y, dz) cwork(z) = cwork(y)`. -/
theorem lintegral_cwork_cKernel_pow (H : Measure ℝ≥0) [IsProbabilityMeasure H]
    (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (k : ℕ) (y : QConfig) :
    ∫⁻ z, ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r z) ∂(cKernel H r ^ k) y =
      ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r y) := by
  have := isProbabilityMeasure_exitLaw hr0.le hr1
  have hf : Measurable fun z => ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r z) :=
    ENNReal.measurable_ofReal.comp (measurable_cwork _ r)
  induction k generalizing y with
  | zero =>
    rw [pow_zero]
    change ∫⁻ z, _ ∂(Kernel.id y) = _
    rw [Kernel.id_apply, lintegral_dirac' _ hf]
  | succ k ih =>
    rw [pow_succ]
    change ∫⁻ z, _ ∂((cKernel H r ^ k) ∘ₖ cKernel H r) y = _
    rw [Kernel.lintegral_comp _ _ _ hf]
    simp_rw [ih]
    rw [cKernel, recursionKernel_apply _ measurable_cstep y,
      lintegral_map (g := fun w => cstep (y, w)) hf
        (measurable_cstep.comp measurable_prodMk_left)]
    exact lintegral_cwork_cstep H hH hr0 hr1 y

/-- Along the configurations of an interval, `E cwork(yₖ) = cwork(y₀)`. -/
theorem lintegral_cwork_orbit (H : Measure ℝ≥0) [IsProbabilityMeasure H]
    (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (k : ℕ) (y : QConfig) :
    ∫⁻ ω, ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r (orbit cstep y ω k))
      ∂Measure.infinitePi (fun _ : ℕ => H.prod (exitLaw r)) =
      ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r y) := by
  have := isProbabilityMeasure_exitLaw hr0.le hr1
  have hf : Measurable fun z => ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r z) :=
    ENNReal.measurable_ofReal.comp (measurable_cwork _ r)
  rw [← lintegral_map (g := fun ω => orbit cstep y ω k) hf (measurable_orbit_cstep y k),
    law_orbit _ measurable_cstep y k]
  exact lintegral_cwork_cKernel_pow H hH hr0 hr1 k y

/-- **The expected work at every event of an interval** equals `V(x)`:
`E cwork(y_k) = V(x)` (averaging the initial configuration over `s₀ ∼ H`). -/
theorem lintegral_cwork_qcfg (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (k : ℕ) (x : ℕ × ℝ≥0) :
    ∫⁻ ξ, ENNReal.ofReal (cwork (∫ s, (s : ℝ) ∂H) r (qcfg (x, ξ) k)) ∂gig1rNoise G H r =
      ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r x) := by
  have := isProbabilityMeasure_exitLaw hr0.le hr1
  set m := ∫ s, (s : ℝ) ∂H with hm
  have hm0 : 0 ≤ m := integral_nonneg fun s => s.2
  have hf : Measurable fun ξ : QNoise => ENNReal.ofReal (cwork m r (qcfg (x, ξ) k)) :=
    ENNReal.measurable_ofReal.comp ((measurable_cwork m r).comp
      ((measurable_qcfg k).comp measurable_prodMk_left))
  rw [gig1rNoise, lintegral_prod _ hf.aemeasurable]
  have hinner : ∀ τ : ℝ≥0, ∫⁻ q, ENNReal.ofReal (cwork m r (qcfg (x, (τ, q)) k))
      ∂H.prod (Measure.infinitePi fun _ : ℕ => H.prod (exitLaw r)) =
      ENNReal.ofReal (qworkV m r x) := fun τ => by
    have hg : Measurable fun q : ℝ≥0 × (ℕ → ℝ≥0 × Bool) =>
        ENNReal.ofReal (cwork m r (qcfg (x, (τ, q)) k)) :=
      hf.comp measurable_prodMk_left
    rw [lintegral_prod _ hg.aemeasurable]
    have h1 : ∀ s₀ : ℝ≥0, ∫⁻ ω, ENNReal.ofReal (cwork m r (qcfg (x, (τ, s₀, ω)) k))
        ∂Measure.infinitePi (fun _ : ℕ => H.prod (exitLaw r)) =
        ENNReal.ofReal (cwork m r (qinit (x, (τ, s₀)))) := fun s₀ =>
      lintegral_cwork_orbit H hH hr0 hr1 k (qinit (x, (τ, s₀)))
    simp_rw [h1]
    unfold qinit qworkV
    by_cases hR : 0 < x.2
    · simp only [hR, ↓reduceIte, hR.ne', cwork, qwork, Nat.add_eq_zero_iff, two_ne_zero,
        and_false]
      rw [lintegral_const, measure_univ, mul_one]
      congr 1
      push_cast
      ring
    · have hR0 : x.2 = 0 := le_antisymm (not_lt.1 hR) zero_le
      have hq : ∀ s₀ : ℝ≥0, cwork m r (if 0 < x.2 then (x.1 + 2, x.2, τ, 0) else
          (x.1 + 1, s₀, τ, 0)) = ((x.1 : ℝ) + 1 - r) * (m / r) + 1 * (s₀ : ℝ) := fun s₀ => by
        simp only [hR, ↓reduceIte, cwork, qwork, Nat.add_one_ne_zero]
        push_cast
        ring
      simp_rw [hq]
      have hnn : 0 ≤ ((x.1 : ℝ) + 1 - r) * (m / r) :=
        mul_nonneg (by linarith [(Nat.cast_nonneg x.1 : (0 : ℝ) ≤ x.1)]) (div_nonneg hm0 hr0.le)
      have hint : Integrable (fun s : ℝ≥0 => ((x.1 : ℝ) + 1 - r) * (m / r) + 1 * (s : ℝ)) H :=
        (integrable_const _).add (hH.const_mul 1)
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun s => by
        positivity), integral_const_add_mul_nnreal H hH, ← hm]
      simp only [hR0, ↓reduceIte]
      congr 1
      have hr : r ≠ 0 := hr0.ne'
      field_simp
      ring
  simp_rw [hinner]
  rw [lintegral_const, measure_univ, mul_one]

/-- The busy time of the server during the interval, read off the first final configuration. -/
noncomputable def gig1rBusy (p : (ℕ × ℝ≥0) × QNoise) : ℝ :=
  open Classical in
  busyfin (qcfg p (Nat.find (exists_isFinal_or p)))

/-- The busy time reads off any final configuration. -/
theorem gig1rBusy_eq {p : (ℕ × ℝ≥0) × QNoise} {k : ℕ} (hk : (qcfg p k).IsFinal) :
    gig1rBusy p = busyfin (qcfg p k) := by
  classical
  have hex : ∃ j, (qcfg p j).IsFinal := ⟨k, hk⟩
  have hspec := Nat.find_spec (exists_isFinal_or p)
  have hK : (qcfg p (Nat.find (exists_isFinal_or p))).IsFinal := hspec.resolve_right (not_not.2 hex)
  have hle : Nat.find (exists_isFinal_or p) ≤ k := Nat.find_min' _ (Or.inl hk)
  unfold gig1rBusy
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj, qcfg_of_isFinal hK j]

/-- `busyfin` is measurable. -/
theorem measurable_busyfin : Measurable busyfin := by
  classical
  exact (measurable_coe_nnreal_real.comp measurable_snd.snd.snd).add
    (measurable_coe_nnreal_real.comp (Measurable.ite (measurable_fst (measurableSet_singleton 0))
      measurable_const measurable_snd.snd.fst))

/-- The busy time is measurable. -/
theorem measurable_gig1rBusy : Measurable gig1rBusy := by
  classical
  have hB : MeasurableSet {p : (ℕ × ℝ≥0) × QNoise | ¬ ∃ j, (qcfg p j).IsFinal} := by
    have : {p : (ℕ × ℝ≥0) × QNoise | ¬ ∃ j, (qcfg p j).IsFinal} =
        (⋃ j, (fun p => qcfg p j) ⁻¹' {y | y.IsFinal})ᶜ := by
      ext p; simp
    rw [this]
    exact (MeasurableSet.iUnion fun j => (measurable_qcfg j) measurableSet_isFinal).compl
  have hp : ∀ k, MeasurableSet {p : (ℕ × ℝ≥0) × QNoise |
      (qcfg p k).IsFinal ∨ ¬ ∃ j, (qcfg p j).IsFinal} := fun k =>
    ((measurable_qcfg k) measurableSet_isFinal).union hB
  exact Measurable.find (fun k => measurable_busyfin.comp (measurable_qcfg k)) hp
    exists_isFinal_or

/-! ### The interval ends almost surely -/

/-- **An interval that never ends uses little service**: if no configuration is final, the
fresh services `s₁, …, s_k` fit in the interarrival time, `s₁ + ⋯ + s_k ≤ τ`, for every `k`. -/
theorem sum_le_of_not_final {p : (ℕ × ℝ≥0) × QNoise} (h : ∀ k, ¬ (qcfg p k).IsFinal) (k : ℕ) :
    ∑ j ∈ Finset.range k, ((p.2.2.2 (j + 1)).1 : ℝ) ≤ p.2.1 := by
  -- `t_k − ρ_k + s₁ + ⋯ + s_k = τ − ρ₀`
  have hinv : ∀ k, ((qcfg p k).2.2.1 : ℝ) - (qcfg p k).2.1 +
      ∑ j ∈ Finset.range k, ((p.2.2.2 (j + 1)).1 : ℝ) = p.2.1 - (qcfg p 0).2.1 := by
    intro k
    induction k with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      change ((qinit (p.1, (p.2.1, p.2.2.1))).2.2.1 : ℝ) - _ = _
      unfold qinit
      split_ifs <;> rfl
    | succ k ih =>
      have hnf : ¬ ((qcfg p k).1 = 0 ∨ (qcfg p k).2.2.1 < (qcfg p k).2.1) := h k
      push Not at hnf
      have hstep := qcfg_succ p k
      rw [show p.2.2.2 (k + 1) = ((p.2.2.2 (k + 1)).1, (p.2.2.2 (k + 1)).2) from rfl,
        cstep_of_not_isFinal (h k)] at hstep
      by_cases hz : nextC (qcfg p k).1 (p.2.2.2 (k + 1)).2 = 0
      · exfalso
        simp only [hz, ↓reduceIte] at hstep
        exact h (k + 1) (Or.inl (by rw [hstep]))
      · simp only [hz, ↓reduceIte] at hstep
        rw [hstep, Finset.sum_range_succ]
        simp only
        rw [NNReal.coe_sub hnf.2]
        linarith
  have h1 := hinv k
  have h2 : (qcfg p k).2.1 ≤ (qcfg p k).2.2.1 := not_lt.1 fun hlt => h k (Or.inr hlt)
  have h3 : ((qcfg p k).2.1 : ℝ) ≤ (qcfg p k).2.2.1 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (qcfg p 0).2.1 := NNReal.coe_nonneg _
  linarith

/-- **Service sums are unbounded almost surely**: if `H[ε, ∞) > 0` for some `ε > 0`, then
`(H ⊗ Bernoulli(r))^{⊗ℕ}`-almost surely `s₁ + ⋯ + s_k → ∞`. -/
theorem measure_sum_bdd_eq_zero (H : Measure ℝ≥0) [IsProbabilityMeasure H] {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {ε : ℝ} (hε : 0 < ε) (hHε : 0 < H {s | ε ≤ (s : ℝ)}) (c : ℝ) :
    Measure.infinitePi (fun _ : ℕ => H.prod (exitLaw r))
      {ω | ∀ k, ∑ j ∈ Finset.range k, ((ω (j + 1)).1 : ℝ) ≤ c} = 0 := by
  have := isProbabilityMeasure_exitLaw hr0 hr1
  set μ := Measure.infinitePi (fun _ : ℕ => H.prod (exitLaw r)) with hμ
  have hsub : {ω : ℕ → ℝ≥0 × Bool | ∀ k, ∑ j ∈ Finset.range k, ((ω (j + 1)).1 : ℝ) ≤ c} ⊆
      ⋃ N : ℕ, {ω | ∀ j, N ≤ j → ((ω j).1 : ℝ) < ε} := by
    intro ω hω
    by_contra hc
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_forall, not_lt] at hc
    -- infinitely many services of length `≥ ε` make the sums unbounded
    have hL : ∀ L : ℕ, ∃ k, L * ε ≤ ∑ j ∈ Finset.range k, ((ω (j + 1)).1 : ℝ) := by
      intro L
      induction L with
      | zero => exact ⟨0, by simp⟩
      | succ L ih =>
        obtain ⟨k, hk⟩ := ih
        obtain ⟨j, hj, hjε⟩ := hc (k + 1)
        refine ⟨j, ?_⟩
        obtain ⟨i, rfl⟩ : ∃ i, j = k + 1 + i := ⟨j - (k + 1), by omega⟩
        have hsplit : ∑ l ∈ Finset.range (k + 1 + i), ((ω (l + 1)).1 : ℝ) =
            ∑ l ∈ Finset.range k, ((ω (l + 1)).1 : ℝ) +
              ∑ l ∈ Finset.Ico k (k + 1 + i), ((ω (l + 1)).1 : ℝ) := by
          rw [Finset.sum_range_add_sum_Ico _ (by omega)]
        have hlast : ((ω (k + 1 + i)).1 : ℝ) ≤
            ∑ l ∈ Finset.Ico k (k + 1 + i), ((ω (l + 1)).1 : ℝ) := by
          have hmem : k + i ∈ Finset.Ico k (k + 1 + i) := Finset.mem_Ico.2 ⟨by omega, by omega⟩
          have := Finset.single_le_sum (f := fun l => ((ω (l + 1)).1 : ℝ))
            (fun l _ => NNReal.coe_nonneg _) hmem
          simpa [show k + i + 1 = k + 1 + i by omega] using this
        rw [hsplit]
        push_cast
        linarith
    obtain ⟨L, hLc⟩ := exists_nat_gt (c / ε)
    obtain ⟨k, hk⟩ := hL L
    have := hω k
    rw [div_lt_iff₀ hε] at hLc
    linarith
  refine measure_mono_null hsub (measure_iUnion_null fun N => ?_)
  -- `μ(sₙ < ε for n ≥ N) ≤ H[0, ε)^M → 0`
  have hlt1 : H {s | (s : ℝ) < ε} < 1 := by
    have hc : {s : ℝ≥0 | (s : ℝ) < ε} = {s : ℝ≥0 | ε ≤ (s : ℝ)}ᶜ := by ext s; simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_le measurable_const measurable_coe_nnreal_real)]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hHε.ne'
  have hB : MeasurableSet ({s : ℝ≥0 | (s : ℝ) < ε} ×ˢ (univ : Set Bool)) :=
    (measurableSet_lt measurable_coe_nnreal_real measurable_const).prod MeasurableSet.univ
  have hbound : ∀ M : ℕ, μ {ω | ∀ j, N ≤ j → ((ω j).1 : ℝ) < ε} ≤ H {s | (s : ℝ) < ε} ^ M := by
    intro M
    calc μ {ω | ∀ j, N ≤ j → ((ω j).1 : ℝ) < ε}
        ≤ μ (Set.pi (Finset.Ico N (N + M) : Set ℕ)
            fun _ => {s : ℝ≥0 | (s : ℝ) < ε} ×ˢ (univ : Set Bool)) := by
          refine measure_mono fun ω hω j hj => ?_
          rw [Finset.coe_Ico, mem_Ico] at hj
          exact ⟨hω j hj.1, mem_univ _⟩
      _ = H {s | (s : ℝ) < ε} ^ M := by
          rw [hμ, Measure.infinitePi_pi _ (fun _ _ => hB)]
          simp only [Measure.prod_prod, measure_univ, mul_one, Finset.prod_const,
            Nat.card_Ico, Nat.add_sub_cancel_left]
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt1) hbound)
    zero_le

/-- **Every interval ends almost surely** (when `H ≠ δ₀`): the event that no configuration is
final is null. -/
theorem gig1rNoise_not_final (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hHε : 0 < H {s | ε ≤ (s : ℝ)}) (x : ℕ × ℝ≥0) :
    gig1rNoise G H r {ξ | ¬ ∃ k, (qcfg (x, ξ) k).IsFinal} = 0 := by
  have := isProbabilityMeasure_exitLaw hr0 hr1
  have hsub : {ξ : QNoise | ¬ ∃ k, (qcfg (x, ξ) k).IsFinal} ⊆ (univ : Set ℝ≥0) ×ˢ
      ((univ : Set ℝ≥0) ×ˢ ⋃ c : ℕ, {ω : ℕ → ℝ≥0 × Bool |
        ∀ k, ∑ j ∈ Finset.range k, ((ω (j + 1)).1 : ℝ) ≤ c}) := by
    intro ξ hξ
    push Not at hξ
    obtain ⟨c, hc⟩ := exists_nat_ge (ξ.1 : ℝ)
    exact ⟨mem_univ _, mem_univ _, mem_iUnion.2 ⟨c, fun k =>
      (sum_le_of_not_final (p := (x, ξ)) hξ k).trans hc⟩⟩
  refine measure_mono_null hsub ?_
  rw [gig1rNoise, Measure.prod_prod, Measure.prod_prod,
    measure_iUnion_null fun c : ℕ => measure_sum_bdd_eq_zero H hr0 hr1 hε hHε (c : ℝ)]
  simp

/-! ### The busy time and the drift of the expected work -/

/-- The initial configuration: residual `R` (busy server) or `s₀` (free server), no busy time
yet, and the whole interarrival time ahead. -/
theorem qcfg_zero_snd (p : (ℕ × ℝ≥0) × QNoise) :
    (qcfg p 0).2 = if 0 < p.1.2 then (p.1.2, p.2.1, 0) else (p.2.2.1, p.2.1, 0) := by
  change (qinit (p.1, (p.2.1, p.2.2.1))).2 = _
  unfold qinit
  split_ifs <;> rfl

/-- **The server is busy for at least `min(τ, R + s₁ + ⋯ + s_N)`** in an interval that ends:
before it can idle, all `N + 1` or `N + 2` customers present must be served once. -/
theorem gig1rBusy_ge {p : (ℕ × ℝ≥0) × QNoise} (hfin : ∃ k, (qcfg p k).IsFinal) :
    min (p.2.1 : ℝ) ((p.1.2 : ℝ) + ∑ j ∈ Finset.range p.1.1, ((p.2.2.2 (j + 1)).1 : ℝ)) ≤
      gig1rBusy p := by
  set C₀ := (qcfg p 0).1 with hC₀
  set σ : ℕ → ℝ := fun k => ((qcfg p 0).2.1 : ℝ) +
    ∑ j ∈ Finset.range k, ((p.2.2.2 (j + 1)).1 : ℝ) with hσ
  have hσmono : ∀ i j, i ≤ j → σ i ≤ σ j := fun i j hij => by
    simp only [hσ]
    exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
      fun l _ _ => NNReal.coe_nonneg _)
  have h0 := qcfg_zero_snd p
  -- the busy time plus the time left is `τ`
  have hI0 : ∀ k, ((qcfg p k).2.2.2 : ℝ) + (qcfg p k).2.2.1 = p.2.1 := by
    intro k
    induction k with
    | zero =>
      rw [h0]
      split_ifs <;> simp
    | succ k ih =>
      rw [qcfg_succ]
      by_cases hf : (qcfg p k).IsFinal
      · rw [cstep_of_isFinal hf]; exact ih
      · have hnf : ¬ ((qcfg p k).1 = 0 ∨ (qcfg p k).2.2.1 < (qcfg p k).2.1) := hf
        push Not at hnf
        rw [show p.2.2.2 (k + 1) = ((p.2.2.2 (k + 1)).1, (p.2.2.2 (k + 1)).2) from rfl,
          cstep_of_not_isFinal hf]
        split_ifs <;>
        · simp only
          rw [NNReal.coe_add, NNReal.coe_sub hnf.2]
          linarith
  -- the invariant
  have hI1 : ∀ k, ((qcfg p k).IsFinal ∧ ((qcfg p k).1 ≠ 0 ∨ σ (C₀ - 1) ≤ (qcfg p k).2.2.2)) ∨
      (¬ (qcfg p k).IsFinal ∧ ((qcfg p k).2.2.2 : ℝ) + (qcfg p k).2.1 = σ k ∧
        C₀ ≤ (qcfg p k).1 + k) := by
    intro k
    induction k with
    | zero =>
      by_cases hf : (qcfg p 0).IsFinal
      · refine Or.inl ⟨hf, Or.inl ?_⟩
        rw [← hC₀, hC₀, qcfg_zero_fst]
        split_ifs <;> omega
      · refine Or.inr ⟨hf, ?_, by omega⟩
        simp only [hσ, Finset.range_zero, Finset.sum_empty, add_zero]
        rw [h0]
        split_ifs <;> simp
    | succ k ih =>
      rw [qcfg_succ]
      rcases ih with ⟨hf, hb⟩ | ⟨hf, hb, hc⟩
      · rw [cstep_of_isFinal hf]; exact Or.inl ⟨hf, hb⟩
      · have hnf : ¬ ((qcfg p k).1 = 0 ∨ (qcfg p k).2.2.1 < (qcfg p k).2.1) := hf
        push Not at hnf
        rw [show p.2.2.2 (k + 1) = ((p.2.2.2 (k + 1)).1, (p.2.2.2 (k + 1)).2) from rfl,
          cstep_of_not_isFinal hf]
        have hnext : (qcfg p k).1 - 1 ≤ nextC (qcfg p k).1 (p.2.2.2 (k + 1)).2 := by
          unfold nextC; split_ifs <;> omega
        split_ifs with hz
        · refine Or.inl ⟨Or.inl rfl, Or.inr ?_⟩
          simp only
          rw [NNReal.coe_add, hb]
          exact hσmono _ _ (by omega)
        · by_cases hf' : QConfig.IsFinal (nextC (qcfg p k).1 (p.2.2.2 (k + 1)).2,
              (p.2.2.2 (k + 1)).1, (qcfg p k).2.2.1 - (qcfg p k).2.1,
              (qcfg p k).2.2.2 + (qcfg p k).2.1)
          · exact Or.inl ⟨hf', Or.inl hz⟩
          · refine Or.inr ⟨hf', ?_, by simp only; omega⟩
            simp only [hσ] at hb ⊢
            rw [NNReal.coe_add, Finset.sum_range_succ]
            linarith
  -- at the end of the interval
  obtain ⟨K, hK⟩ := hfin
  rw [gig1rBusy_eq hK]
  have hΛ : (p.1.2 : ℝ) + ∑ j ∈ Finset.range p.1.1, ((p.2.2.2 (j + 1)).1 : ℝ) ≤ σ (C₀ - 1) := by
    have hC := qcfg_zero_fst p
    rw [← hC₀] at hC
    simp only [hσ]
    rw [h0]
    by_cases hR : 0 < p.1.2
    · simp only [hR, ↓reduceIte] at hC ⊢
      rw [hC, show p.1.1 + 2 - 1 = p.1.1 + 1 by omega, Finset.sum_range_succ]
      linarith [NNReal.coe_nonneg (p.2.2.2 (p.1.1 + 1)).1]
    · have hR0 : p.1.2 = 0 := le_antisymm (not_lt.1 hR) zero_le
      simp only [hR, ↓reduceIte] at hC ⊢
      rw [hC, show p.1.1 + 1 - 1 = p.1.1 by omega, hR0, NNReal.coe_zero, zero_add]
      linarith [NNReal.coe_nonneg p.2.2.1]
  unfold busyfin
  rcases hI1 K with ⟨-, hb⟩ | ⟨hf, -⟩
  · by_cases hz : (qcfg p K).1 = 0
    · simp only [hz, ↓reduceIte, NNReal.coe_zero, add_zero]
      have := hb.resolve_left (not_not.2 hz)
      exact (min_le_right _ _).trans (hΛ.trans this)
    · simp only [hz, ↓reduceIte]
      rw [hI0 K]
      exact min_le_left _ _
  · exact absurd hK hf

/-- `V ≥ 0`. -/
theorem qworkV_nonneg {m r : ℝ} (hm : 0 ≤ m) (hr0 : 0 < r) (hr1 : r ≤ 1) (x : ℕ × ℝ≥0) :
    0 ≤ qworkV m r x := by
  have hmr : 0 ≤ m / r := div_nonneg hm hr0.le
  unfold qworkV
  split_ifs
  · positivity
  · have : 0 ≤ ((x.1 : ℝ) + 2 - r) * (m / r) :=
      mul_nonneg (by linarith [(Nat.cast_nonneg x.1 : (0 : ℝ) ≤ x.1)]) hmr
    positivity

/-- `V` is measurable. -/
theorem measurable_qworkV (m r : ℝ) : Measurable (qworkV m r) := by
  classical
  refine Measurable.ite (measurable_snd (measurableSet_singleton 0)) ?_ ?_
  · exact (((measurable_of_countable (fun C : ℕ => (C : ℝ))).comp measurable_fst).add_const
      _).mul_const _
  · exact (measurable_coe_nnreal_real.comp measurable_snd).add
      ((((measurable_of_countable (fun C : ℕ => (C : ℝ))).comp measurable_fst).add_const
        _).sub_const _ |>.mul_const _)

/-- **Work conservation in one interval** (the expectation form of (11.35)): with `H ≠ δ₀`,
`E_x[V(Φ₁)] + E[busy time in [T₀, T₁)] ≤ V(x) + m/r`. The proof is Fatou's lemma for the
event-time martingale `cwork` (`lintegral_cwork_qcfg`) along the a.s. finite interval. -/
theorem lintegral_qworkV_add_busy (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) {ε : ℝ} (hε : 0 < ε) (hHε : 0 < H {s | ε ≤ (s : ℝ)})
    (x : ℕ × ℝ≥0) :
    ∫⁻ ξ, ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r (gig1rStep (x, ξ))) ∂gig1rNoise G H r +
      ∫⁻ ξ, ENNReal.ofReal (gig1rBusy (x, ξ)) ∂gig1rNoise G H r ≤
      ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r x) +
        ENNReal.ofReal ((∫ s, (s : ℝ) ∂H) / r) := by
  have := isProbabilityMeasure_gig1rNoise G H hr0.le hr1
  set m := ∫ s, (s : ℝ) ∂H with hm
  have hm0 : 0 ≤ m := integral_nonneg fun s => s.2
  set Ξ := gig1rNoise G H r with hΞ
  set f : ℕ → QNoise → ℝ≥0∞ := fun k ξ => ENNReal.ofReal (cwork m r (qcfg (x, ξ) k)) with hf
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ENNReal.measurable_ofReal.comp ((measurable_cwork m r).comp
      ((measurable_qcfg k).comp measurable_prodMk_left))
  have hfin : ∀ᵐ ξ ∂Ξ, ∃ k, (qcfg (x, ξ) k).IsFinal :=
    ae_iff.2 (gig1rNoise_not_final G H hr0.le hr1 hε hHε x)
  have hVm : Measurable fun ξ => ENNReal.ofReal (qworkV m r (gig1rStep (x, ξ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_qworkV m r).comp
      (measurable_gig1rStep.comp measurable_prodMk_left))
  have hae : ∀ᵐ ξ ∂Ξ, ENNReal.ofReal (qworkV m r (gig1rStep (x, ξ))) +
      ENNReal.ofReal (gig1rBusy (x, ξ)) =
      Filter.liminf (fun k => f k ξ) atTop + ENNReal.ofReal (m / r) := by
    filter_upwards [hfin] with ξ hξ
    obtain ⟨K, hK⟩ := hξ
    have hlim : Filter.liminf (fun k => f k ξ) atTop = f K ξ := by
      refine (tendsto_atTop_of_eventually_const (i₀ := K) fun k hk => ?_).liminf_eq
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      simp only [hf]
      rw [qcfg_of_isFinal hK j]
    rw [hlim, gig1rStep_eq hK, gig1rBusy_eq hK,
      ← ENNReal.ofReal_add (qworkV_nonneg hm0 hr0 hr1 _) (by unfold busyfin; positivity),
      qworkV_qout_add_busyfin m r hK,
      ENNReal.ofReal_add (cwork_nonneg hm0 hr0 hr1 _) (div_nonneg hm0 hr0.le)]
  calc ∫⁻ ξ, ENNReal.ofReal (qworkV m r (gig1rStep (x, ξ))) ∂Ξ +
        ∫⁻ ξ, ENNReal.ofReal (gig1rBusy (x, ξ)) ∂Ξ
      = ∫⁻ ξ, (ENNReal.ofReal (qworkV m r (gig1rStep (x, ξ))) +
          ENNReal.ofReal (gig1rBusy (x, ξ))) ∂Ξ := (lintegral_add_left hVm _).symm
    _ = ∫⁻ ξ, (Filter.liminf (fun k => f k ξ) atTop + ENNReal.ofReal (m / r)) ∂Ξ :=
        lintegral_congr_ae hae
    _ = ∫⁻ ξ, Filter.liminf (fun k => f k ξ) atTop ∂Ξ + ENNReal.ofReal (m / r) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ Filter.liminf (fun k => ∫⁻ ξ, f k ξ ∂Ξ) atTop + ENNReal.ofReal (m / r) :=
        add_le_add (lintegral_liminf_le hfm) le_rfl
    _ = ENNReal.ofReal (qworkV m r x) + ENNReal.ofReal (m / r) := by
        have hconst : (fun k => ∫⁻ ξ, f k ξ ∂Ξ) = fun _ => ENNReal.ofReal (qworkV m r x) :=
          funext fun k => lintegral_cwork_qcfg G H hH hr0 hr1 k x
        rw [hconst, liminf_const]

/-- `E(τ − fₙ)⁺ → 0` when `0 ≤ τ` is integrable and eventually `fₙ ≥ τ` almost surely
(dominated convergence). -/
theorem tendsto_integral_posPart_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {τ : Ω → ℝ} (hτ : Integrable τ μ) (hτ0 : ∀ ω, 0 ≤ τ ω) {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hlim : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, τ ω ≤ f n ω) :
    Tendsto (fun n => ∫ ω, max (τ ω - f n ω) 0 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω => max (τ ω - f n ω) 0) (f := fun _ => 0) τ
    (fun n => (hτ.1.sub (hf n).aestronglyMeasurable).sup aestronglyMeasurable_const) hτ
    (fun n => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hf0 n ω]) (hτ0 ω))
    (hlim.mono fun ω hω => tendsto_const_nhds.congr' (hω.mono fun n hn => by
      simp only
      rw [max_eq_right (by linarith)]))
  simpa using h

/-- Almost surely under the innovation law, the service sums `s₁ + ⋯ + s_k` are unbounded. -/
theorem ae_sum_unbounded (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hHε : 0 < H {s | ε ≤ (s : ℝ)}) :
    ∀ᵐ ξ ∂gig1rNoise G H r, ∀ c : ℝ, ∃ k,
      c < ∑ j ∈ Finset.range k, ((ξ.2.2 (j + 1)).1 : ℝ) := by
  have := isProbabilityMeasure_exitLaw hr0 hr1
  rw [ae_iff]
  have hsub : {ξ : QNoise | ¬ ∀ c : ℝ, ∃ k, c < ∑ j ∈ Finset.range k,
      ((ξ.2.2 (j + 1)).1 : ℝ)} ⊆ (univ : Set ℝ≥0) ×ˢ ((univ : Set ℝ≥0) ×ˢ
        ⋃ c : ℕ, {ω : ℕ → ℝ≥0 × Bool | ∀ k, ∑ j ∈ Finset.range k, ((ω (j + 1)).1 : ℝ) ≤ c}) := by
    intro ξ hξ
    simp only [mem_ofPred_eq, not_forall, not_exists, not_lt] at hξ
    obtain ⟨c, hc⟩ := hξ
    obtain ⟨n, hn⟩ := exists_nat_ge c
    exact ⟨mem_univ _, mem_univ _, mem_iUnion.2 ⟨n, fun k => (hc k).trans hn⟩⟩
  refine measure_mono_null hsub ?_
  rw [gig1rNoise, Measure.prod_prod, Measure.prod_prod,
    measure_iUnion_null fun c : ℕ => measure_sum_bdd_eq_zero H hr0 hr1 hε hHε (c : ℝ)]
  simp

/-- If `E S > 0`, then `H[E S / 2, ∞) > 0`. -/
theorem measure_half_mean_le_pos (H : Measure ℝ≥0) [IsProbabilityMeasure H]
    (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H) (hm : 0 < ∫ s, (s : ℝ) ∂H) :
    0 < H {s | (∫ s, (s : ℝ) ∂H) / 2 ≤ (s : ℝ)} := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have hae : ∀ᵐ s ∂H, ((s : ℝ≥0) : ℝ) ≤ (∫ s, (s : ℝ) ∂H) / 2 := by
    rw [ae_iff]
    exact measure_mono_null (fun s hs => (not_le.1 hs).le) h0
  have := integral_mono_ae hH (integrable_const _) hae
  rw [integral_const, probReal_univ, one_smul] at this
  linarith

/-- **The drift of the expected work** (the core of Proposition 11.4.4). Under `E S > 0` and
the load condition `E S / r < E T`, there are a compact set `A` and `c > 0` such that
`E_x[V(Φ₁)] ≤ V(x) − c` (and `V(x) ≥ c`) off `A`, while `E_x[V(Φ₁)] ≤ V(x) + m/r` everywhere.
Off a large compact set the server is busy for almost the whole interval
(`gig1rBusy_ge`, `tendsto_integral_posPart_sub`), so the work drifts by about
`m/r − E T < 0` (`lintegral_qworkV_add_busy`). -/
theorem gig1r_drift (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hG : Integrable (fun t : ℝ≥0 => (t : ℝ)) G) (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H)
    (hm : 0 < ∫ s, (s : ℝ) ∂H) (hload : (∫ s, (s : ℝ) ∂H) / r < ∫ t, (t : ℝ) ∂G) :
    ∃ (A : Set (ℕ × ℝ≥0)) (c : ℝ), IsCompact A ∧ 0 < c ∧
      (∀ x ∉ A, c ≤ qworkV (∫ s, (s : ℝ) ∂H) r x ∧
        ∫⁻ y, ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r y) ∂gig1rKernel G H r x ≤
          ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r x - c)) ∧
      ∀ x, ∫⁻ y, ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r y) ∂gig1rKernel G H r x ≤
        ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r x + (∫ s, (s : ℝ) ∂H) / r) := by
  have := isProbabilityMeasure_exitLaw hr0.le hr1
  have := isProbabilityMeasure_gig1rNoise G H hr0.le hr1
  set m := ∫ s, (s : ℝ) ∂H with hmdef
  set T := ∫ t, (t : ℝ) ∂G with hTdef
  set Ξ := gig1rNoise G H r with hΞ
  have hmr : 0 ≤ m / r := div_nonneg hm.le hr0.le
  have hεpos : 0 < m / 2 := by linarith
  have hHε := measure_half_mean_le_pos H hH hm
  rw [← hmdef] at hHε
  have hVm : Measurable fun y => ENNReal.ofReal (qworkV m r y) :=
    ENNReal.measurable_ofReal.comp (measurable_qworkV m r)
  -- the basic work bound
  have hbase : ∀ x, ∫⁻ ξ, ENNReal.ofReal (qworkV m r (gig1rStep (x, ξ))) ∂Ξ +
      ∫⁻ ξ, ENNReal.ofReal (gig1rBusy (x, ξ)) ∂Ξ ≤
      ENNReal.ofReal (qworkV m r x + m / r) := fun x => by
    rw [ENNReal.ofReal_add (qworkV_nonneg hm.le hr0 hr1 x) hmr]
    exact lintegral_qworkV_add_busy G H hH hr0 hr1 hεpos hHε x
  have hPV : ∀ x, ∫⁻ y, ENNReal.ofReal (qworkV m r y) ∂gig1rKernel G H r x =
      ∫⁻ ξ, ENNReal.ofReal (qworkV m r (gig1rStep (x, ξ))) ∂Ξ := fun x =>
    lintegral_gig1rKernel G H hr0.le hr1 x hVm
  -- the interarrival time under `Ξ`
  have hτi : Integrable (fun ξ : QNoise => (ξ.1 : ℝ)) Ξ := hG.comp_fst _
  have hτint : ∫ ξ, (ξ.1 : ℝ) ∂Ξ = T := by
    rw [hΞ, gig1rNoise, integral_fun_fst (f := fun t : ℝ≥0 => (t : ℝ))]
    simp only [probReal_univ, one_smul]
    exact hTdef.symm
  have hτ0 : ∀ ξ : QNoise, 0 ≤ (ξ.1 : ℝ) := fun ξ => NNReal.coe_nonneg _
  -- the two tails
  set η := (T - m / r) / 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hsum_m : ∀ n, Measurable fun ξ : QNoise =>
      ∑ j ∈ Finset.range n, ((ξ.2.2 (j + 1)).1 : ℝ) := fun n =>
    Finset.measurable_sum _ fun j _ => measurable_coe_nnreal_real.comp
      (measurable_fst.comp ((measurable_pi_apply (j + 1)).comp measurable_snd.snd))
  have ht1 := tendsto_integral_posPart_sub Ξ hτi hτ0 (f := fun n _ => (n : ℝ))
    (fun n => measurable_const) (fun n _ => Nat.cast_nonneg n)
    (Eventually.of_forall fun ξ => eventually_atTop.2 ⟨⌈(ξ.1 : ℝ)⌉₊, fun n hn =>
      (Nat.le_ceil _).trans (by exact_mod_cast hn)⟩)
  have ht2 := tendsto_integral_posPart_sub Ξ hτi hτ0
    (f := fun n ξ => ∑ j ∈ Finset.range n, ((ξ.2.2 (j + 1)).1 : ℝ)) hsum_m
    (fun n ξ => Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _)
    ((ae_sum_unbounded G H hr0.le hr1 hεpos hHε).mono fun ξ hξ => by
      obtain ⟨k, hk⟩ := hξ (ξ.1 : ℝ)
      refine eventually_atTop.2 ⟨k, fun n hn => hk.le.trans ?_⟩
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        fun j _ _ => NNReal.coe_nonneg _)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tendsto_order.1 ht1).2 η hηpos)
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 ((tendsto_order.1 ht2).2 η hηpos)
  set A : Set (ℕ × ℝ≥0) := Iic n₂ ×ˢ Iic (n₁ : ℝ≥0) with hA
  have hAc : IsCompact A := (Set.finite_Iic n₂).isCompact.prod (by
    rw [← Set.Icc_bot]; exact isCompact_Icc)
  refine ⟨A, η, hAc, hηpos, fun x hx => ?_, fun x => ?_⟩
  swap
  · rw [hPV]
    exact le_self_add.trans (hbase x)
  -- off `A` the server is busy for most of the interval
  set Λ : QNoise → ℝ := fun ξ => (x.2 : ℝ) + ∑ j ∈ Finset.range x.1, ((ξ.2.2 (j + 1)).1 : ℝ)
    with hΛ
  have hΛm : Measurable Λ := measurable_const.add (hsum_m x.1)
  have htail : ∫ ξ, max ((ξ.1 : ℝ) - Λ ξ) 0 ∂Ξ ≤ η := by
    have hint : ∀ g : QNoise → ℝ, Measurable g → (∀ ξ, 0 ≤ g ξ) →
        Integrable (fun ξ => max ((ξ.1 : ℝ) - g ξ) 0) Ξ := fun g hg hg0 =>
      Integrable.mono' hτi (((measurable_coe_nnreal_real.comp measurable_fst).sub hg).max
        measurable_const).aestronglyMeasurable (Eventually.of_forall fun ξ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          exact max_le (by linarith [hg0 ξ]) (hτ0 ξ))
    have hΛ0 : ∀ ξ, 0 ≤ Λ ξ := fun ξ =>
      add_nonneg (NNReal.coe_nonneg _) (Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _)
    simp only [hA, mem_prod, mem_Iic, not_and_or, not_le] at hx
    rcases hx with hN | hR
    · refine le_trans (integral_mono (hint Λ hΛm hΛ0) (hint _ (hsum_m n₂)
        fun ξ => Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _) fun ξ => ?_) (hn₂ n₂ le_rfl).le
      refine max_le_max (sub_le_sub_left ?_ _) le_rfl
      simp only [hΛ]
      have : ∑ j ∈ Finset.range n₂, ((ξ.2.2 (j + 1)).1 : ℝ) ≤
          ∑ j ∈ Finset.range x.1, ((ξ.2.2 (j + 1)).1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN.le)
          fun j _ _ => NNReal.coe_nonneg _
      linarith [NNReal.coe_nonneg x.2]
    · refine le_trans (integral_mono (hint Λ hΛm hΛ0) (hint (fun _ => (n₁ : ℝ)) measurable_const
        fun _ => Nat.cast_nonneg _) fun ξ => ?_) (hn₁ n₁ le_rfl).le
      refine max_le_max (sub_le_sub_left ?_ _) le_rfl
      simp only [hΛ]
      have h1 : (n₁ : ℝ) ≤ x.2 := by exact_mod_cast hR.le
      linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.range x.1) =>
        NNReal.coe_nonneg (ξ.2.2 (j + 1)).1]
  -- the busy time has mean at least `E T − η`
  have hfin : ∀ᵐ ξ ∂Ξ, ∃ k, (qcfg (x, ξ) k).IsFinal :=
    ae_iff.2 (gig1rNoise_not_final G H hr0.le hr1 hεpos hHε x)
  have hmin_i : Integrable (fun ξ => min (ξ.1 : ℝ) (Λ ξ)) Ξ :=
    Integrable.mono' hτi ((measurable_coe_nnreal_real.comp measurable_fst).min
      hΛm).aestronglyMeasurable (Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hτ0 ξ) (add_nonneg (NNReal.coe_nonneg _)
          (Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _)))]
        exact min_le_left _ _)
  have hbusy : ENNReal.ofReal (T - η) ≤ ∫⁻ ξ, ENNReal.ofReal (gig1rBusy (x, ξ)) ∂Ξ := by
    have hmin0 : ∀ ξ : QNoise, 0 ≤ min (ξ.1 : ℝ) (Λ ξ) := fun ξ =>
      le_min (hτ0 ξ) (add_nonneg (NNReal.coe_nonneg _)
        (Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _))
    calc ENNReal.ofReal (T - η) ≤ ENNReal.ofReal (∫ ξ, min (ξ.1 : ℝ) (Λ ξ) ∂Ξ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsplit : ∀ ξ : QNoise, min (ξ.1 : ℝ) (Λ ξ) =
              (ξ.1 : ℝ) - max ((ξ.1 : ℝ) - Λ ξ) 0 := fun ξ => by
            rcases le_total (ξ.1 : ℝ) (Λ ξ) with h | h
            · rw [min_eq_left h, max_eq_right (by linarith)]; ring
            · rw [min_eq_right h, max_eq_left (by linarith)]; ring
          simp_rw [hsplit]
          have hint2 : Integrable (fun ξ : QNoise => max ((ξ.1 : ℝ) - Λ ξ) 0) Ξ :=
            Integrable.mono' hτi (((measurable_coe_nnreal_real.comp measurable_fst).sub
              hΛm).max measurable_const).aestronglyMeasurable (Eventually.of_forall fun ξ => by
                rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
                exact max_le (by linarith [hmin0 ξ, min_le_right (ξ.1 : ℝ) (Λ ξ)]) (hτ0 ξ))
          rw [integral_sub hτi hint2, hτint]
          linarith
      _ = ∫⁻ ξ, ENNReal.ofReal (min (ξ.1 : ℝ) (Λ ξ)) ∂Ξ :=
          ofReal_integral_eq_lintegral_ofReal hmin_i (Eventually.of_forall hmin0)
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (gig1rBusy (x, ξ)) ∂Ξ := by
          refine lintegral_mono_ae (hfin.mono fun ξ hξ => ENNReal.ofReal_le_ofReal ?_)
          exact gig1rBusy_ge (p := (x, ξ)) hξ
  -- the drift
  have hb := hbase x
  rw [hPV]
  have hTη : T - η = m / r + η := by rw [hη]; ring
  rw [hTη] at hbusy
  have h2 : ∫⁻ ξ, ENNReal.ofReal (qworkV m r (gig1rStep (x, ξ))) ∂Ξ +
      ENNReal.ofReal (m / r + η) ≤ ENNReal.ofReal (qworkV m r x + m / r) :=
    (add_le_add le_rfl hbusy).trans hb
  have hle : m / r + η ≤ qworkV m r x + m / r := by
    have := (le_add_self).trans h2
    rwa [ENNReal.ofReal_le_ofReal_iff (add_nonneg (qworkV_nonneg hm.le hr0 hr1 x) hmr)] at this
  refine ⟨by linarith, ?_⟩
  have h3 := ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top h2
  rwa [← ENNReal.ofReal_sub _ (by positivity), show qworkV m r x + m / r - (m / r + η) =
    qworkV m r x - η by ring] at h3

/-- `V(N, R) ≤ R + (N + 2) m/r`. -/
theorem qworkV_le {m r : ℝ} (hm : 0 ≤ m) (hr0 : 0 < r) (x : ℕ × ℝ≥0) :
    qworkV m r x ≤ x.2 + ((x.1 : ℝ) + 2) * (m / r) := by
  have hmr : 0 ≤ m / r := div_nonneg hm hr0.le
  unfold qworkV
  split_ifs
  · nlinarith [NNReal.coe_nonneg x.2]
  · nlinarith

/-- **Proposition 11.4.4** (MT p. 275). Under the load condition `ρ_r < 1`, i.e.
`E S / r < E T` (with `E S > 0`), the drift condition (11.34) holds with `k = 1` for the
expected work `V(x) = E_x[W₀]` scaled by `1/c`: there are a compact set `A` and `c > 0` with
`E_x[V(Φ₁)/c] + 1 ≤ V(x)/c` for `x ∉ A` and `sup_{x ∈ A} E_x[V(Φ₁)/c] < ∞`. Hence (V2) holds
with the petite set `A` (Proposition 11.4.3), and the GI/G/1 queue with re-entry is a regular
chain (Theorem 11.3.15), and positive Harris. -/
theorem proposition_11_4_4 (G H : Measure ℝ≥0) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hG : Integrable (fun t : ℝ≥0 => (t : ℝ)) G) (hH : Integrable (fun s : ℝ≥0 => (s : ℝ)) H)
    (hm : 0 < ∫ s, (s : ℝ) ∂H) (hload : (∫ s, (s : ℝ) ∂H) / r < ∫ t, (t : ℝ) ∂G) :
    haveI := isMarkovKernel_gig1rKernel G H hr0.le hr1
    ∃ (A : Set (ℕ × ℝ≥0)) (c : ℝ), IsCompact A ∧ 0 < c ∧
      (∀ x ∉ A, ∫⁻ y, ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r y / c)
          ∂gig1rKernel G H r x + 1 ≤ ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r x / c)) ∧
      (∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x ∈ A, ∫⁻ y, ENNReal.ofReal (qworkV (∫ s, (s : ℝ) ∂H) r y / c)
          ∂gig1rKernel G H r x ≤ M) ∧
      IsRegularChain (gig1rKernel G H r)
        (maxIrrMeasure (gig1rKernel G H r) (Measure.dirac ((0 : ℕ), (0 : ℝ≥0)))) ∧
      IsPositiveHarris (gig1rKernel G H r)
        (maxIrrMeasure (gig1rKernel G H r) (Measure.dirac ((0 : ℕ), (0 : ℝ≥0)))) := by
  have := isMarkovKernel_gig1rKernel G H hr0.le hr1
  set m := ∫ s, (s : ℝ) ∂H with hmdef
  set P := gig1rKernel G H r with hP
  obtain ⟨-, hψ, -, -, hpet⟩ := proposition_11_4_3 G H hr0 hr1 hG hH hload
  obtain ⟨A, c, hA, hc, hoff, hall⟩ := gig1r_drift G H hr0 hr1 hG hH hm hload
  have hmr : 0 ≤ m / r := div_nonneg hm.le hr0.le
  have hVm : Measurable fun y => ENNReal.ofReal (qworkV m r y) :=
    ENNReal.measurable_ofReal.comp (measurable_qworkV m r)
  set W : ℕ × ℝ≥0 → ℝ≥0∞ := fun y => ENNReal.ofReal (qworkV m r y / c) with hW
  have hWm : Measurable W :=
    ENNReal.measurable_ofReal.comp ((measurable_qworkV m r).div_const c)
  have hWeq : ∀ y, W y = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (qworkV m r y) := fun y => by
    rw [hW]
    simp only
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  have hPW : ∀ x, ∫⁻ y, W y ∂P x = ENNReal.ofReal c⁻¹ * ∫⁻ y, ENNReal.ofReal (qworkV m r y) ∂P x :=
    fun x => by simp_rw [hWeq]; rw [lintegral_const_mul _ hVm]
  have hoff' : ∀ x ∉ A, ∫⁻ y, W y ∂P x + 1 ≤ W x := fun x hx => by
    obtain ⟨hcV, hdr⟩ := hoff x hx
    rw [hPW]
    calc ENNReal.ofReal c⁻¹ * ∫⁻ y, ENNReal.ofReal (qworkV m r y) ∂P x + 1
        ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal (qworkV m r x - c) + 1 :=
          add_le_add (mul_le_mul' le_rfl hdr) le_rfl
      _ = ENNReal.ofReal (qworkV m r x / c - 1) + ENNReal.ofReal 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ENNReal.ofReal_one]
          congr 2
          field_simp
      _ = W x := by
          have h1 : 0 ≤ qworkV m r x / c - 1 := by
            rw [sub_nonneg, le_div_iff₀ hc, one_mul]; exact hcV
          rw [← ENNReal.ofReal_add h1 zero_le_one, sub_add_cancel]
  have hon : ∀ x, ∫⁻ y, W y ∂P x ≤ W x + ENNReal.ofReal (m / (r * c)) := fun x => by
    rw [hPW]
    calc ENNReal.ofReal c⁻¹ * ∫⁻ y, ENNReal.ofReal (qworkV m r y) ∂P x
        ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal (qworkV m r x + m / r) :=
          mul_le_mul' le_rfl (hall x)
      _ = W x + ENNReal.ofReal (m / (r * c)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), hW]
          simp only
          rw [← ENNReal.ofReal_add (div_nonneg (qworkV_nonneg hm.le hr0 hr1 x) hc.le)
            (div_nonneg hm.le (mul_pos hr0 hc).le)]
          congr 1
          field_simp
  -- the bound on `A`
  obtain ⟨n₀, hn₀⟩ := (hA.image continuous_fst).bddAbove
  obtain ⟨R₀, hR₀⟩ := (hA.image (NNReal.continuous_coe.comp continuous_snd)).bddAbove
  set b := ENNReal.ofReal (m / (r * c)) + 1 with hb
  have hdrift : DriftV2 P W b A := fun x => by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, hb, ← add_assoc]
      exact add_le_add (hon x) le_rfl
    · rw [indicator_of_notMem hx, add_zero]
      exact hoff' x hx
  have hreg : IsRegularChain P (maxIrrMeasure P (Measure.dirac ((0 : ℕ), (0 : ℝ≥0)))) :=
    (theorem_11_3_15 hψ).1.2 ⟨A, W, b, hpet A hA, hWm,
      ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩,
      fun x => ENNReal.ofReal_ne_top, hdrift⟩
  refine ⟨A, c, hA, hc, hoff', ⟨ENNReal.ofReal ((R₀ + ((n₀ : ℝ) + 2) * (m / r)) / c) +
    ENNReal.ofReal (m / (r * c)), ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩, fun x hx => ?_⟩, hreg, hreg.isPositiveHarris hψ⟩
  refine (hon x).trans (add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hxn : (x.1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀ ⟨x, hx, rfl⟩
  have hxR : (x.2 : ℝ) ≤ R₀ := hR₀ ⟨x, hx, rfl⟩
  refine div_le_div_of_nonneg_right ((qworkV_le hm.le hr0 x).trans ?_) hc.le
  nlinarith

end MeynTweedie.DriftRegularity
