/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.RenewalSkeletons

/-!
# The GI/G/1 queue as a ladder chain (MT §3.5.4)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/GIG1Embedding.lean`), with the namespace changed to
`MeynTweedie.VUniformErgodicity` and the imports to `InvariantMeasures.*` (via the `PseudoAtoms`
copy). The ladder kernel `ladderKernel` is
renamed `ladderChainKernel` here, since `ladderKernel` already names the Chapter 5 counterexample
kernel in `InvariantMeasures`.

Meyn and Tweedie, §3.5.4, p. 71: with `Nₙ` the number of customers just before the `n`-th
arrival and `Rₙ` the residual service time just after it, `Φₙ = (Nₙ, Rₙ)` is a Markov chain with
the ladder kernel (3.40), (3.42)–(3.43) ("it is easy to verify").

The queue is built from its primitives on the canonical space `ℝ^ℕ × ℝ^ℕ` with law
`G^{⊗ℕ} ⊗ H^{⊗ℕ}`: interarrival times (`arrT`), service times and first-come-first-served
departures (`depT`), the customer in service (`inService`), `Nₙ = queueN`, `Rₙ = queueR`.

* `gig1_step_eq`: pathwise, `(N_{n+1}, R_{n+1})` is the ladder step `gig1Step` from
  `(Nₙ, Rₙ)` driven by the next interarrival time and the services of the customers after the one
  in service.
* `gig1_law_past_future`: that future is independent of the past at the `n`-th arrival and is
  again `G^{⊗ℕ} ⊗ H^{⊗ℕ}`.
* `gig1Ladder_eq_map`: the law of one step from `(i, x)` is `gig1Ladder H G (i, x)`.
* `gig1_isMarkovChain`: `Φ` is a Markov chain with kernel `gig1Ladder H G` and initial law
  `δ₀ ⊗ H` (the first customer finds the system empty), via `isMarkovChain_of_regeneration` at
  the index of the customer in service.

Hypotheses: interarrival times are nonnegative (`G(−∞, 0) = 0`) and service times are positive
(`H(−∞, 0] = 0`).

**Correction.** MT call `Rₙ` the "total residual service time in the system at `Tₙ+`", but
(3.41)–(3.43) use the residual service of the customer in service (the forward recurrence time
of the service renewal process); with the total workload the transition law is not (3.42)–(3.43).
Here `Rₙ` is the residual service of the customer in service.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- Rearranging a product of four independent factors: `(μa ⊗ μb) ⊗ (μc ⊗ μd)` pushed by
`((a, b), (c, d)) ↦ ((a, c), (b, d))` is `(μa ⊗ μc) ⊗ (μb ⊗ μd)`. -/
theorem map_prod_prod_rearrange {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μa : Measure A) (μb : Measure B) (μc : Measure C)
    (μd : Measure D) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    ((μa.prod μb).prod (μc.prod μd)).map (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))) =
      (μa.prod μc).prod (μb.prod μd) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have e3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have e4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have e5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  have h := e5.comp (e4.comp (e3.comp (e2.comp e1)))
  convert h.map_eq using 2
  funext q
  rfl

/-- The arrival epochs `T₀ = 0`, `Tₙ = a₀ + ⋯ + a_{n−1}` of customers `0, 1, 2, …`, with
interarrival times `aᵢ` (MT (Q1), p. 40). -/
def arrT (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

/-- The departure epochs of a single-server first-come-first-served queue with service times
`sₘ` (MT (Q2)–(Q3)): `D₀ = s₀` and `D_{m+1} = max(Dₘ, T_{m+1}) + s_{m+1}`. -/
noncomputable def depT (a s : ℕ → ℝ) : ℕ → ℝ
  | 0 => s 0
  | m + 1 => max (depT a s m) (arrT a (m + 1)) + s (m + 1)

/-- The customer in service just after the `n`-th arrival: the first customer still present
at `Tₙ`. -/
noncomputable def inService (a s : ℕ → ℝ) (n : ℕ) : ℕ := sInf {m | arrT a n < depT a s m}

/-- `Nₙ`, the number of customers in the system just before the `n`-th arrival, `Tₙ−`
(MT p. 71). -/
noncomputable def queueN (a s : ℕ → ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun m => arrT a n < depT a s m).card

/-- `Rₙ`, the residual service time at `Tₙ+` of the customer then in service (MT p. 71). -/
noncomputable def queueR (a s : ℕ → ℝ) (n : ℕ) : ℝ := depT a s (inService a s n) - arrT a n

/-- `T_{n+1} = Tₙ + aₙ`. -/
theorem arrT_succ (a : ℕ → ℝ) (n : ℕ) : arrT a (n + 1) = arrT a n + a n :=
  Finset.sum_range_succ _ _

/-- Arrival epochs increase. -/
theorem arrT_mono {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) {m n : ℕ} (h : m ≤ n) : arrT a m ≤ arrT a n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => ha i

/-- Every customer leaves after arriving. -/
theorem arrT_lt_depT {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (m : ℕ) : arrT a m < depT a s m := by
  cases m with
  | zero => simpa [arrT, depT] using hs 0
  | succ m =>
    simp only [depT]
    have := hs (m + 1)
    have := le_max_right (depT a s m) (arrT a (m + 1))
    linarith

/-- Customers leave in order. -/
theorem depT_lt_succ {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (m : ℕ) :
    depT a s m < depT a s (m + 1) := by
  simp only [depT]
  have := hs (m + 1)
  have := le_max_left (depT a s m) (arrT a (m + 1))
  linarith

/-- Departure epochs increase. -/
theorem depT_mono {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) : Monotone (depT a s) :=
  monotone_nat_of_le_succ fun m => (depT_lt_succ hs m).le

/-- The customer in service at `Tₙ+` is present, has arrived, and all earlier customers have
left. -/
theorem inService_spec {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (n : ℕ) :
    arrT a n < depT a s (inService a s n) ∧ inService a s n ≤ n ∧
      ∀ m < inService a s n, depT a s m ≤ arrT a n := by
  have hex : ∃ m, arrT a n < depT a s m := ⟨n, arrT_lt_depT hs n⟩
  exact ⟨Nat.sInf_mem hex, Nat.sInf_le (arrT_lt_depT hs n),
    fun m hm => not_lt.1 (Nat.notMem_of_lt_sInf hm)⟩

/-- `Nₙ = n − cₙ`, where `cₙ` is the customer in service at `Tₙ+`. -/
theorem queueN_eq {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (n : ℕ) :
    queueN a s n = n - inService a s n := by
  obtain ⟨h1, h2, h3⟩ := inService_spec hs n
  have : (Finset.range n).filter (fun m => arrT a n < depT a s m) =
      Finset.Ico (inService a s n) n := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hm, hlt⟩
      refine ⟨?_, hm⟩
      by_contra hc
      exact absurd (h3 m (not_le.1 hc)) (not_le.2 hlt)
    · rintro ⟨hm1, hm2⟩
      exact ⟨hm2, lt_of_lt_of_le h1 (depT_mono hs hm1)⟩
  rw [queueN, this, Nat.card_Ico]

/-- The customer in service at successive arrivals does not decrease. -/
theorem inService_mono {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) {m n : ℕ}
    (h : m ≤ n) : inService a s m ≤ inService a s n := by
  obtain ⟨h1, -, -⟩ := inService_spec (a := a) hs n
  exact Nat.sInf_le (lt_of_le_of_lt (arrT_mono ha h) h1)

/-- After `Tₙ` the customers present leave at the renewal epochs started from the residual
service `Rₙ`, driven by the services of the customers waiting behind. -/
theorem depT_chain {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) {n : ℕ} :
    ∀ j, inService a s n + j ≤ n →
      depT a s (inService a s n + j) =
        arrT a n + resEpoch (queueR a s n) (tailSeq (inService a s n + 1) s) (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [queueR, resEpoch_succ_eq]
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    obtain ⟨h1, -, -⟩ := inService_spec (a := a) hs n
    have hle : arrT a (inService a s n + j + 1) ≤ depT a s (inService a s n + j) :=
      (arrT_mono ha (by omega)).trans (h1.le.trans (depT_mono hs (by omega)))
    rw [show inService a s n + (j + 1) = inService a s n + j + 1 by omega, depT,
      max_eq_left hle, ih', resEpoch_succ_eq, resEpoch_succ_eq, Finset.sum_range_succ]
    simp only [tailSeq]
    rw [show inService a s n + 1 + j = inService a s n + j + 1 by omega]
    ring

/-- The number of service completions within time `t` in the renewal process started with
residual service `x`. -/
noncomputable def numDone (x : ℝ) (σ : ℕ → ℝ) (t : ℝ) : ℕ := sInf {j | t < resEpoch x σ (j + 1)}

/-- One step of the GI/G/1 ladder chain: from `(i, x)` with interarrival time `α₀` and the
services `σ` of the following customers. -/
noncomputable def gig1Step (q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ))) : ℕ × ℝ :=
  if resEpoch q.1.2 q.2.2 (q.1.1 + 1) ≤ q.2.1 0 then (0, q.2.2 q.1.1)
  else (q.1.1 + 1 - numDone q.1.2 q.2.2 (q.2.1 0),
    resEpoch q.1.2 q.2.2 (numDone q.1.2 q.2.2 (q.2.1 0) + 1) - q.2.1 0)

/-- **The GI/G/1 recursion.** `(N_{n+1}, R_{n+1})` is the ladder step from `(Nₙ, Rₙ)` driven by
the next interarrival time and the services of the customers after the one in service. -/
theorem gig1_step_eq {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) (n : ℕ) :
    (queueN a s (n + 1), queueR a s (n + 1)) =
      gig1Step ((queueN a s n, queueR a s n), (tailSeq n a, tailSeq (inService a s n + 1) s)) := by
  set k := inService a s n with hkdef
  obtain ⟨h1, hkn, h3⟩ := inService_spec (a := a) hs n
  set x := queueR a s n
  set σ := tailSeq (k + 1) s
  have hN : queueN a s n = n - k := queueN_eq hs n
  have hchain := depT_chain (a := a) ha hs (n := n)
  have hT : arrT a (n + 1) = arrT a n + a n := arrT_succ a n
  have hdepn : depT a s n = arrT a n + resEpoch x σ (n - k + 1) := by
    have := hchain (n - k) (by omega)
    rwa [show k + (n - k) = n by omega] at this
  unfold gig1Step
  simp only [hN, tailSeq, add_zero]
  change _ = if resEpoch x σ (n - k + 1) ≤ a n then (0, σ (n - k)) else
    (n - k + 1 - numDone x σ (a n), resEpoch x σ (numDone x σ (a n) + 1) - a n)
  have hNe : queueN a s (n + 1) = n + 1 - inService a s (n + 1) := queueN_eq hs (n + 1)
  split_ifs with hcase
  · have hc : inService a s (n + 1) = n + 1 := by
      unfold inService
      rw [natSInf_eq_iff]
      left
      refine ⟨arrT_lt_depT hs (n + 1), fun m hm => not_lt.2 ?_⟩
      have := depT_mono (a := a) hs (show m ≤ n by omega)
      linarith
    rw [hNe, hc, queueR, hc, depT, hT, max_eq_right (by linarith)]
    simp only [Nat.sub_self, σ, tailSeq]
    congr 1
    rw [show k + 1 + (n - k) = n + 1 by omega]
    ring
  · have hℓ : numDone x σ (a n) ≤ n - k := Nat.sInf_le (not_le.1 hcase)
    have hℓspec : a n < resEpoch x σ (numDone x σ (a n) + 1) :=
      Nat.sInf_mem (s := {j | a n < resEpoch x σ (j + 1)})
        ⟨n - k, show a n < resEpoch x σ (n - k + 1) from not_le.1 hcase⟩
    have hℓmin : ∀ j < numDone x σ (a n), resEpoch x σ (j + 1) ≤ a n := fun j hj =>
      not_lt.1 (Nat.notMem_of_lt_sInf hj)
    have hc : inService a s (n + 1) = k + numDone x σ (a n) := by
      unfold inService
      rw [natSInf_eq_iff]
      left
      refine ⟨?_, fun m hm => not_lt.2 ?_⟩
      · rw [hchain _ (by omega), hT]
        linarith
      · by_cases hmk : m < k
        · have := h3 m hmk
          have := ha n
          linarith
        · obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
          rw [hchain j (by omega), hT]
          have := hℓmin j (by omega)
          linarith
    rw [hNe, hc, queueR, hc, hchain _ (by omega), hT]
    congr 1
    · omega
    · ring

/-- Evaluating a sequence of measurable maps at a measurable random index is measurable. -/
theorem measurable_comp_index {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {L : Ω → ℕ} (hL : Measurable L) {f : ℕ → Ω → X} (hf : ∀ n, Measurable (f n)) :
    Measurable fun ω => f (L ω) ω :=
  (measurable_from_prod_countable_right (f := fun p : ℕ × Ω => f p.1 p.2) hf).comp
    (hL.prodMk measurable_id)

/-- Arrival epochs are measurable. -/
theorem measurable_arrT (n : ℕ) : Measurable fun a : ℕ → ℝ => arrT a n :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- Departure epochs are measurable. -/
theorem measurable_depT (m : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => depT ω.1 ω.2 m := by
  induction m with
  | zero => exact (measurable_pi_apply 0).comp measurable_snd
  | succ m ih =>
    exact (ih.max ((measurable_arrT (m + 1)).comp measurable_fst)).add
      ((measurable_pi_apply (m + 1)).comp measurable_snd)

/-- The customer in service is a measurable random index. -/
theorem measurableSet_inService_eq (n k : ℕ) :
    MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) | inService ω.1 ω.2 n = k} :=
  measurableSet_natSInf_eq
    (P := fun (ω : (ℕ → ℝ) × (ℕ → ℝ)) m => arrT ω.1 n < depT ω.1 ω.2 m)
    (fun m => measurableSet_lt ((measurable_arrT n).comp measurable_fst) (measurable_depT m)) k

/-- The customer in service is measurable. -/
theorem measurable_inService (n : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => inService ω.1 ω.2 n :=
  measurable_to_countable' fun k => measurableSet_inService_eq n k

/-- `Nₙ` is measurable. -/
theorem measurable_queueN (n : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => queueN ω.1 ω.2 n := by
  have h : (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => queueN ω.1 ω.2 n) = fun ω =>
      ∑ m ∈ Finset.range n, if arrT ω.1 n < depT ω.1 ω.2 m then 1 else 0 := by
    funext ω
    rw [queueN, Finset.card_filter]
  rw [h]
  exact Finset.measurable_sum _ fun m _ => Measurable.ite
    (measurableSet_lt ((measurable_arrT n).comp measurable_fst) (measurable_depT m))
    measurable_const measurable_const

/-- `Rₙ` is measurable. -/
theorem measurable_queueR (n : ℕ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => queueR ω.1 ω.2 n :=
  (measurable_comp_index (measurable_inService n) (f := fun m ω => depT ω.1 ω.2 m)
    measurable_depT).sub ((measurable_arrT n).comp measurable_fst)

/-- The number of completions is measurable. -/
theorem measurable_numDone :
    Measurable fun q : ℝ × (ℝ × (ℕ → ℝ)) => numDone q.1 q.2.2 q.2.1 :=
  measurable_to_countable' fun k => measurableSet_natSInf_eq
    (P := fun (q : ℝ × (ℝ × (ℕ → ℝ))) j => q.2.1 < resEpoch q.1 q.2.2 (j + 1))
    (fun j => measurableSet_lt (measurable_fst.comp measurable_snd)
      ((measurable_resEpoch (j + 1)).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))) k

/-- The ladder step is measurable. -/
theorem measurable_gig1Step : Measurable gig1Step := by
  have hL : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.1.1 :=
    measurable_fst.comp measurable_fst
  have hx : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.1.2 :=
    measurable_snd.comp measurable_fst
  have ht : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.2.1 0 :=
    (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
  have hσ : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => q.2.2 :=
    measurable_snd.comp measurable_snd
  have hZ : ∀ j, Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) => resEpoch q.1.2 q.2.2 j :=
    fun j => (measurable_resEpoch j).comp (hx.prodMk hσ)
  have hℓ : Measurable fun q : (ℕ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
      numDone q.1.2 q.2.2 (q.2.1 0) :=
    measurable_numDone.comp (hx.prodMk (ht.prodMk hσ))
  refine measurable_comp_index hL (f := fun i q =>
    if resEpoch q.1.2 q.2.2 (i + 1) ≤ q.2.1 0 then ((0 : ℕ), q.2.2 i)
    else (i + 1 - numDone q.1.2 q.2.2 (q.2.1 0),
      resEpoch q.1.2 q.2.2 (numDone q.1.2 q.2.2 (q.2.1 0) + 1) - q.2.1 0)) fun i => ?_
  refine Measurable.ite (measurableSet_le (hZ (i + 1)) ht)
    (measurable_const.prodMk ((measurable_pi_apply i).comp hσ))
    ((measurable_of_countable (fun l : ℕ => i + 1 - l) |>.comp hℓ).prodMk
      ((measurable_comp_index hℓ (f := fun l q => resEpoch q.1.2 q.2.2 (l + 1))
        fun l => hZ (l + 1)).sub ht))

/-- The first `n + 1` arrival epochs only use the first `n` interarrival times. -/
theorem arrT_truncSeq {a : ℕ → ℝ} {n j : ℕ} (hj : j ≤ n) : arrT (truncSeq n a) j = arrT a j :=
  Finset.sum_congr rfl fun i hi => by
    have : i < n := by simp at hi; omega
    simp [truncSeq, this]

/-- The departures of the first `k + 1` customers only use their own services and the first
`n` interarrival times. -/
theorem depT_truncSeq {a s : ℕ → ℝ} {n k : ℕ} :
    ∀ m, m ≤ n → m ≤ k → depT (truncSeq n a) (truncSeq (k + 1) s) m = depT a s m := by
  intro m
  induction m with
  | zero =>
    intro _ _
    simp [depT, truncSeq]
  | succ m ih =>
    intro hmn hmk
    simp only [depT]
    rw [ih (by omega) (by omega), arrT_truncSeq hmn]
    simp [truncSeq, show m + 1 < k + 1 by omega]

/-- The customers in service at the first `n` arrivals are determined by the past at the
`n`-th arrival. -/
theorem inService_truncSeq {a s : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) {n j : ℕ}
    (hj : j ≤ n) :
    inService (truncSeq n a) (truncSeq (inService a s n + 1) s) j = inService a s j := by
  set k := inService a s n
  obtain ⟨h1, h2, h3⟩ := inService_spec (a := a) hs j
  have hjk : inService a s j ≤ k := inService_mono ha hs hj
  have hkn : k ≤ n := (inService_spec (a := a) hs n).2.1
  change sInf {m | arrT (truncSeq n a) j < depT (truncSeq n a) (truncSeq (k + 1) s) m} =
    inService a s j
  rw [natSInf_eq_iff]
  left
  refine ⟨?_, fun m hm => ?_⟩
  · rw [arrT_truncSeq hj, depT_truncSeq _ (by omega) hjk]
    exact h1
  · rw [arrT_truncSeq hj, depT_truncSeq _ (by omega) (by omega)]
    exact not_lt.2 (h3 m hm)

/-- The event `{cₙ = k}` is determined by the first `n` interarrival times and the first
`k + 1` services. -/
theorem inService_eq_iff_truncSeq {a s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (n k : ℕ) :
    inService a s n = k ↔
      (arrT (truncSeq n a) n < depT (truncSeq n a) (truncSeq (k + 1) s) k ∧
        ∀ m < k, depT (truncSeq n a) (truncSeq (k + 1) s) m ≤ arrT (truncSeq n a) n) := by
  rw [arrT_truncSeq le_rfl]
  by_cases hkn : k ≤ n
  · rw [depT_truncSeq _ hkn le_rfl]
    have e : (∀ m < k, depT (truncSeq n a) (truncSeq (k + 1) s) m ≤ arrT a n) ↔
        ∀ m < k, depT a s m ≤ arrT a n :=
      forall₂_congr fun m hm => by rw [depT_truncSeq _ (by omega) (by omega)]
    rw [e]
    unfold inService
    rw [natSInf_eq_iff]
    simp only [not_lt]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd (h n) (not_le.2 (arrT_lt_depT hs n))
    · exact Or.inl
  · constructor
    · intro h
      exact absurd (h ▸ (inService_spec (a := a) hs n).2.1) hkn
    · rintro ⟨-, h⟩
      have := h n (by omega)
      rw [depT_truncSeq _ le_rfl (by omega)] at this
      exact absurd this (not_le.2 (arrT_lt_depT hs n))

/-- Two measures on `ℕ × ℝ` agree if they agree on all sets `{j} × A`. -/
theorem measure_ext_nat_prod {μ ν : Measure (ℕ × ℝ)}
    (h : ∀ j (A : Set ℝ), MeasurableSet A → μ ({j} ×ˢ A) = ν ({j} ×ˢ A)) : μ = ν := by
  ext E hE
  have hE' : E = ⋃ j, ({j} : Set ℕ) ×ˢ (Prod.mk j ⁻¹' E) := by
    ext ⟨j, y⟩
    simp
  have hd : Pairwise fun a b =>
      Disjoint (({a} : Set ℕ) ×ˢ (Prod.mk a ⁻¹' E)) (({b} : Set ℕ) ×ˢ (Prod.mk b ⁻¹' E)) :=
    fun a b hab => Set.disjoint_left.2 fun p ha hb => hab (ha.1.symm.trans hb.1)
  have hm : ∀ j, MeasurableSet (({j} : Set ℕ) ×ˢ (Prod.mk j ⁻¹' E)) := fun j =>
    (measurableSet_singleton j).prod (measurable_prodMk_left hE)
  rw [hE', measure_iUnion hd hm, measure_iUnion hd hm]
  exact tsum_congr fun j => h j _ (measurable_prodMk_left hE)

/-- The ladder step as a function of the interarrival time and the services alone. -/
noncomputable def gig1Step0 (i : ℕ) (x : ℝ) (q : ℝ × (ℕ → ℝ)) : ℕ × ℝ :=
  gig1Step ((i, x), ((fun _ => q.1), q.2))

/-- If the `(i+1)`-th epoch is after `t`, at most `i` services are completed by `t`. -/
theorem numDone_le_of_lt {x t : ℝ} {σ : ℕ → ℝ} {i : ℕ} (h : t < resEpoch x σ (i + 1)) :
    numDone x σ t ≤ i := Nat.sInf_le h

/-- Exactly `m` services are completed by `t ≥ 0` iff `Zₘ ≤ t < Z_{m+1}`. -/
theorem numDone_eq_iff {x t : ℝ} {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, σ i) atTop atTop) (ht : 0 ≤ t) (m : ℕ) :
    numDone x σ t = m ↔ resEpoch x σ m ≤ t ∧ t < resEpoch x σ (m + 1) := by
  have h0 : resEpoch x σ 0 = 0 := rfl
  unfold numDone
  rw [natSInf_eq_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h, rfl⟩)
    · refine ⟨?_, h1⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [h0]
        exact ht
      · have := h2 (m - 1) (by omega)
        rw [show m - 1 + 1 = m by omega] at this
        exact not_lt.1 this
    · obtain ⟨m, hm⟩ := exists_resEpoch_gt (x := x) hdiv t
      exact absurd hm (h m)
  · rintro ⟨h1, h2⟩
    refine Or.inl ⟨h2, fun j hj => not_lt.2 ?_⟩
    exact (resEpoch_mono hσ (by omega) (show j + 1 ≤ m by omega)).trans h1

/-- At least `i + 1` services are completed by `t` iff exactly `j + i + 1` are, for one `j`. -/
theorem tsum_indicator_tail_eq {x t : ℝ} {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, σ i) atTop atTop) (i : ℕ) :
    ∑' j, (if resEpoch x σ (j + i + 1) ≤ t ∧ t < resEpoch x σ (j + i + 1 + 1) then
      (1 : ℝ≥0∞) else 0) = if resEpoch x σ (i + 1) ≤ t then 1 else 0 := by
  by_cases hti : resEpoch x σ (i + 1) ≤ t
  · simp only [hti, ite_true]
    have hex := exists_resEpoch_gt (x := x) hdiv t
    set ℓ := numDone x σ t
    have hℓ : t < resEpoch x σ (ℓ + 1) := Nat.sInf_mem hex
    have hℓmin : ∀ j < ℓ, resEpoch x σ (j + 1) ≤ t := fun j hj =>
      not_lt.1 (Nat.notMem_of_lt_sInf hj)
    have hiℓ : i + 1 ≤ ℓ := by
      by_contra hc
      have := resEpoch_mono (x := x) hσ (show 1 ≤ ℓ + 1 by omega) (show ℓ + 1 ≤ i + 1 by omega)
      linarith
    have hA : resEpoch x σ (ℓ - (i + 1) + i + 1) ≤ t := by
      have := hℓmin (ℓ - 1) (by omega)
      rwa [show ℓ - 1 + 1 = ℓ by omega, show ℓ = ℓ - (i + 1) + i + 1 by omega] at this
    have hB : t < resEpoch x σ (ℓ - (i + 1) + i + 1 + 1) := by
      rwa [show ℓ - (i + 1) + i + 1 + 1 = ℓ + 1 by omega]
    rw [tsum_eq_single (ℓ - (i + 1)) fun j hj => ?_]
    · simp [hA, hB]
    · have hne : ¬ (resEpoch x σ (j + i + 1) ≤ t ∧ t < resEpoch x σ (j + i + 1 + 1)) := by
        rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne hj with hlt | hgt
        · have := hℓmin (j + i + 1) (by omega)
          linarith
        · have := resEpoch_mono (x := x) hσ (show 1 ≤ ℓ + 1 by omega)
            (show ℓ + 1 ≤ j + i + 1 by omega)
          linarith
      simp only [hne, ite_false]
  · simp only [hti, ite_false]
    refine ENNReal.tsum_eq_zero.2 fun j => ?_
    have hne : ¬ (resEpoch x σ (j + i + 1) ≤ t ∧ t < resEpoch x σ (j + i + 1 + 1)) := by
      rintro ⟨h1, -⟩
      have := resEpoch_mono (x := x) hσ (show 1 ≤ i + 1 by omega)
        (show i + 1 ≤ j + i + 1 by omega)
      exact hti (this.trans h1)
    simp only [hne, ite_false]

/-- `gig1Step0` is measurable. -/
theorem measurable_gig1Step0 (i : ℕ) (x : ℝ) : Measurable (gig1Step0 i x) :=
  measurable_gig1Step.comp (measurable_const.prodMk
    ((measurable_pi_iff.2 fun _ => measurable_fst).prodMk measurable_snd))

/-- The queue length rises by at most one between arrivals. -/
theorem gig1Step0_fst_le (i : ℕ) (x : ℝ) (q : ℝ × (ℕ → ℝ)) : (gig1Step0 i x q).1 ≤ i + 1 := by
  unfold gig1Step0 gig1Step
  split_ifs <;> simp

/-- The queue is empty just before the next arrival iff all `i + 1` customers are served, and
then the new service is the next one. -/
theorem gig1Step0_mem_zero_iff (i : ℕ) (x : ℝ) (q : ℝ × (ℕ → ℝ)) (A : Set ℝ) :
    gig1Step0 i x q ∈ ({0} : Set ℕ) ×ˢ A ↔ resEpoch x q.2 (i + 1) ≤ q.1 ∧ q.2 i ∈ A := by
  unfold gig1Step0 gig1Step
  simp only
  split_ifs with h
  · simp [h]
  · simp only [mem_prod, mem_singleton_iff, h, false_and, iff_false, not_and]
    intro h1
    have := numDone_le_of_lt (x := x) (σ := q.2) (t := q.1) (not_le.1 h)
    omega

/-- The queue holds `j ≥ 1` customers before the next arrival iff exactly `i + 1 − j` services
are completed. -/
theorem gig1Step0_mem_iff {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i + 1) {x : ℝ}
    {q : ℝ × (ℕ → ℝ)} (ht : 0 ≤ q.1) (hσ : ∀ i, 0 ≤ q.2 i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, q.2 i) atTop atTop) (A : Set ℝ) :
    gig1Step0 i x q ∈ ({j} : Set ℕ) ×ˢ A ↔
      q ∈ Prod.mk x ⁻¹' gig1Set (i + 1 - j) A := by
  unfold gig1Step0 gig1Step
  simp only [gig1Set, mem_preimage, mem_ofPred_eq, mem_prod, mem_singleton_iff]
  split_ifs with h
  · simp only [show (0 : ℕ) ≠ j by omega, false_and, false_iff, not_and]
    intro h1 h2
    have := resEpoch_mono (x := x) hσ (show 1 ≤ i + 1 - j + 1 by omega)
      (show i + 1 - j + 1 ≤ i + 1 by omega)
    linarith
  · have hℓ := numDone_le_of_lt (x := x) (σ := q.2) (t := q.1) (not_le.1 h)
    constructor
    · rintro ⟨h1, h2⟩
      have hm : numDone x q.2 q.1 = i + 1 - j := by omega
      rw [hm] at h2
      exact ⟨((numDone_eq_iff hσ hdiv ht _).1 hm).1, ((numDone_eq_iff hσ hdiv ht _).1 hm).2, h2⟩
    · rintro ⟨h1, h2, h3⟩
      have hm := (numDone_eq_iff hσ hdiv ht (i + 1 - j)).2 ⟨h1, h2⟩
      rw [hm]
      exact ⟨by omega, h3⟩

/-- Almost surely the interarrival time is nonnegative and the service epochs increase to
infinity. -/
theorem ae_good_gig1 (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) :
    ∀ᵐ q ∂(G.prod (Measure.infinitePi fun _ : ℕ => H)),
      0 ≤ q.1 ∧ Tendsto (fun n => ∑ i ∈ Finset.range n, q.2 i) atTop atTop ∧
        ∀ i, 0 ≤ q.2 i := by
  have h1 : ∀ᵐ t ∂G, 0 ≤ t := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by
      ext a
      simp
    rw [this, hG0]
  have h1' := (measurePreserving_fst (μ := G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae h1
  have h2' := (measurePreserving_snd (μ := G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae
      (tendsto_partialSum_atTop_ae H hH0 hHpos)
  filter_upwards [h1', h2'] with q hq1 hq2
  exact ⟨hq1, hq2.1, hq2.2⟩

/-- **The GI/G/1 kernel is the law of one queue step**: `gig1Ladder H G (i, x)` (MT (3.40),
(3.42)–(3.43)) is the law of the ladder step from `(i, x)` with `T ∼ G` and i.i.d. services
`∼ H`. -/
theorem gig1Ladder_eq_map (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) (i : ℕ) (x : ℝ) :
    gig1Ladder H G (i, x) = (G.prod (Measure.infinitePi fun _ : ℕ => H)).map (gig1Step0 i x) := by
  set ν := Measure.infinitePi fun _ : ℕ => H
  set ρ := G.prod ν
  have hgood := ae_good_gig1 H G hH0 hHpos hG0
  refine measure_ext_nat_prod fun j A hA => ?_
  rw [Measure.map_apply (measurable_gig1Step0 i x) ((measurableSet_singleton j).prod hA)]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [gig1Ladder, eq_3_40_zero _ _ i x hA]
    change (∑' k, gig1Lambda H G (k + i + 1) x univ) * H A = _
    have hset : gig1Step0 i x ⁻¹' (({0} : Set ℕ) ×ˢ A) =
        (fun q : ℝ × (ℕ → ℝ) => ((q.1, truncSeq i q.2), tailSeq i q.2)) ⁻¹'
          ({p : ℝ × (ℕ → ℝ) | resEpoch x p.2 (i + 1) ≤ p.1} ×ˢ {y | y 0 ∈ A}) := by
      ext q
      rw [mem_preimage, gig1Step0_mem_zero_iff]
      simp only [mem_preimage, mem_prod, mem_ofPred_eq, tailSeq, add_zero]
      rw [resEpoch_truncSeq_of_le le_rfl]
    have hΦ : Measurable fun q : ℝ × (ℕ → ℝ) => ((q.1, truncSeq i q.2), tailSeq i q.2) :=
      (measurable_fst.prodMk ((measurable_truncSeq i).comp measurable_snd)).prodMk
        ((measurable_tailSeq i).comp measurable_snd)
    have hS1 : MeasurableSet {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 (i + 1) ≤ p.1} :=
      measurableSet_le ((measurable_resEpoch (i + 1)).comp
        (measurable_const.prodMk measurable_snd)) measurable_fst
    have hS2 : MeasurableSet {y : ℕ → ℝ | y 0 ∈ A} := (measurable_pi_apply 0) hA
    have hT : Measurable fun q : ℝ × (ℕ → ℝ) => (q.1, truncSeq i q.2) :=
      measurable_fst.prodMk ((measurable_truncSeq i).comp measurable_snd)
    rw [hset, ← Measure.map_apply hΦ (hS1.prod hS2), prod_map_trunc_tail G H i,
      Measure.prod_prod, infinitePi_measure_head H hA, Measure.map_apply hT hS1]
    congr 1
    have hpre : (fun q : ℝ × (ℕ → ℝ) => (q.1, truncSeq i q.2)) ⁻¹'
        {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 (i + 1) ≤ p.1} =
          {q : ℝ × (ℕ → ℝ) | resEpoch x q.2 (i + 1) ≤ q.1} := by
      ext q
      simp only [mem_preimage, mem_ofPred_eq]
      rw [resEpoch_truncSeq_of_le le_rfl]
    rw [hpre]
    have hk : ∀ k, gig1Lambda H G (k + i + 1) x univ =
        ∫⁻ q, (if resEpoch x q.2 (k + i + 1) ≤ q.1 ∧ q.1 < resEpoch x q.2 (k + i + 1 + 1)
          then (1 : ℝ≥0∞) else 0) ∂ρ := fun k => by
      change gig1LambdaMeasure H G (k + i + 1) x univ = _
      rw [gig1LambdaMeasure_apply H G _ x MeasurableSet.univ,
        ← lintegral_indicator_one (measurable_prodMk_left
          (measurableSet_gig1Set (k + i + 1) MeasurableSet.univ))]
      refine lintegral_congr fun q => ?_
      by_cases hq : resEpoch x q.2 (k + i + 1) ≤ q.1 ∧ q.1 < resEpoch x q.2 (k + i + 1 + 1)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hq),
          indicator_of_mem (show q ∈ Prod.mk x ⁻¹' gig1Set (k + i + 1) univ from
          ⟨hq.1, hq.2, mem_univ _⟩)]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hq),
          indicator_of_notMem (show q ∉ Prod.mk x ⁻¹' gig1Set (k + i + 1) univ from
          fun h => hq ⟨h.1, h.2.1⟩)]
    have hmk : ∀ k, AEMeasurable (fun q : ℝ × (ℕ → ℝ) =>
        if resEpoch x q.2 (k + i + 1) ≤ q.1 ∧ q.1 < resEpoch x q.2 (k + i + 1 + 1)
          then (1 : ℝ≥0∞) else 0) ρ := fun k => by
      have hZk : ∀ m, Measurable fun q : ℝ × (ℕ → ℝ) => resEpoch x q.2 m := fun m =>
        (measurable_resEpoch m).comp (measurable_const.prodMk measurable_snd)
      have hset : MeasurableSet {q : ℝ × (ℕ → ℝ) | resEpoch x q.2 (k + i + 1) ≤ q.1 ∧
          q.1 < resEpoch x q.2 (k + i + 1 + 1)} :=
        (measurableSet_le (hZk _) measurable_fst).inter (measurableSet_lt measurable_fst (hZk _))
      exact (Measurable.ite hset measurable_const measurable_const).aemeasurable
    rw [tsum_congr hk, ← lintegral_tsum hmk]
    have hS1' : MeasurableSet {q : ℝ × (ℕ → ℝ) | resEpoch x q.2 (i + 1) ≤ q.1} := hS1
    rw [← lintegral_indicator_one hS1']
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with q ⟨_, hdiv, hσ⟩
    rw [tsum_indicator_tail_eq hσ hdiv i]
    by_cases hq : resEpoch x q.2 (i + 1) ≤ q.1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hq), indicator_of_mem (show q ∈ {q : ℝ × (ℕ → ℝ) |
        resEpoch x q.2 (i + 1) ≤ q.1} from hq)]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hq),
        indicator_of_notMem (show q ∉ {q : ℝ × (ℕ → ℝ) |
        resEpoch x q.2 (i + 1) ≤ q.1} from hq)]
  · by_cases hji : j ≤ i + 1
    · rw [gig1Ladder, eq_3_40_mid _ _ hj hji x hA]
      change gig1LambdaMeasure H G (i + 1 - j) x A = _
      rw [gig1LambdaMeasure_apply H G _ x hA]
      refine measure_congr ?_
      filter_upwards [hgood] with q ⟨ht, hdiv, hσ⟩
      exact propext (gig1Step0_mem_iff hj hji ht hσ hdiv A).symm
    · rw [gig1Ladder, eq_3_40_up _ _ (by omega) x hA]
      symm
      convert measure_empty (μ := ρ)
      ext q
      simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro h
      have := gig1Step0_fst_le i x q
      omega

/-- The past at the `n`-th arrival (`n` interarrival times, `k + 1` services) is independent
of the future, which is again `G^{⊗ℕ} ⊗ H^{⊗ℕ}`. -/
theorem gig1_law_past_future (G H : Measure ℝ) [IsProbabilityMeasure G]
    [IsProbabilityMeasure H] (n k : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)).map
        (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ((truncSeq n ω.1, truncSeq (k + 1) ω.2),
          (tailSeq n ω.1, tailSeq (k + 1) ω.2))) =
      (((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)).map
        (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => (truncSeq n ω.1, truncSeq (k + 1) ω.2))).prod
        ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)) := by
  set μG := Measure.infinitePi fun _ : ℕ => G
  set μH := Measure.infinitePi fun _ : ℕ => H
  have hf : Measurable fun a : ℕ → ℝ => (truncSeq n a, tailSeq n a) :=
    (measurable_truncSeq n).prodMk (measurable_tailSeq n)
  have hg : Measurable fun s : ℕ → ℝ => (truncSeq (k + 1) s, tailSeq (k + 1) s) :=
    (measurable_truncSeq (k + 1)).prodMk (measurable_tailSeq (k + 1))
  have hr : Measurable fun q : ((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
      ((q.1.1, q.2.1), (q.1.2, q.2.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  have hc : (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ((truncSeq n ω.1, truncSeq (k + 1) ω.2),
      (tailSeq n ω.1, tailSeq (k + 1) ω.2))) =
      (fun q : ((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
        ((q.1.1, q.2.1), (q.1.2, q.2.2))) ∘
        Prod.map (fun a : ℕ → ℝ => (truncSeq n a, tailSeq n a))
          (fun s : ℕ → ℝ => (truncSeq (k + 1) s, tailSeq (k + 1) s)) := by
    funext ω
    rfl
  have hB : (μG.prod μH).map (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
      (truncSeq n ω.1, truncSeq (k + 1) ω.2)) =
      (μG.map (truncSeq n)).prod (μH.map (truncSeq (k + 1))) := by
    rw [Measure.map_prod_map _ _ (measurable_truncSeq n) (measurable_truncSeq (k + 1))]
    rfl
  rw [hc, ← Measure.map_map hr (hf.prodMap hg), ← Measure.map_prod_map _ _ hf hg,
    infinitePi_map_trunc_tail, infinitePi_map_trunc_tail, map_prod_prod_rearrange, hB]

/-- Almost surely interarrival times are nonnegative and services are positive. -/
theorem ae_good_queue (G H : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure H]
    (hG0 : G (Iio 0) = 0) (hH0 : H (Iic 0) = 0) :
    ∀ᵐ ω ∂((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)),
      (∀ i, 0 ≤ ω.1 i) ∧ ∀ i, 0 < ω.2 i := by
  have h1 : ∀ᵐ a ∂(Measure.infinitePi fun _ : ℕ => G), ∀ i, 0 ≤ a i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {a : ℕ → ℝ | ¬ 0 ≤ a i} = (fun a : ℕ → ℝ => a i) ⁻¹' Iio 0 := by
      ext a
      simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio,
      Measure.infinitePi_map_eval, hG0]
  have h2 : ∀ᵐ s ∂(Measure.infinitePi fun _ : ℕ => H), ∀ i, 0 < s i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {s : ℕ → ℝ | ¬ 0 < s i} = (fun s : ℕ → ℝ => s i) ⁻¹' Iic 0 := by
      ext s
      simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iic,
      Measure.infinitePi_map_eval, hH0]
  have h1' := (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae h1
  have h2' := (measurePreserving_snd (μ := Measure.infinitePi fun _ : ℕ => G)
    (ν := Measure.infinitePi fun _ : ℕ => H)).quasiMeasurePreserving.ae h2
  filter_upwards [h1', h2'] with ω hω1 hω2
  exact ⟨hω1, hω2⟩

/-- **The GI/G/1 queue embedded at arrivals is a Markov chain** (MT §3.5.4, p. 71). For
i.i.d. interarrival times `∼ G` on `[0, ∞)` and independent i.i.d. service times `∼ H` on
`(0, ∞)`, the process `Φₙ = (Nₙ, Rₙ)` is a Markov chain on `ℤ₊ × ℝ` with the ladder kernel
`gig1Ladder H G` and initial law `δ₀ ⊗ H`. -/
theorem gig1_isMarkovChain (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iic 0) = 0) (hG0 : G (Iio 0) = 0) :
    IsMarkovChain (gig1Ladder H G) ((Measure.dirac 0).prod H)
      ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H))
      (fun n ω => (queueN ω.1 ω.2 n, queueR ω.1 ω.2 n)) := by
  set P := (Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H)
  have hH0' : H (Iio 0) = 0 := measure_mono_null Iio_subset_Iic_self hH0
  have hHpos : 0 < H (Ioi 0) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hH0, tsub_zero]
    exact one_pos
  have hgood := ae_good_queue G H hG0 hH0
  have hΨ : ∀ n, Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
      (queueN ω.1 ω.2 n, queueR ω.1 ω.2 n) := fun n =>
    (measurable_queueN n).prodMk (measurable_queueR n)
  have h0 : P.map (fun ω => (queueN ω.1 ω.2 0, queueR ω.1 ω.2 0)) =
      (Measure.dirac 0).prod H := by
    have hae : (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => (queueN ω.1 ω.2 0, queueR ω.1 ω.2 0)) =ᵐ[P]
        Prod.map (fun _ : ℕ → ℝ => (0 : ℕ)) (fun s : ℕ → ℝ => s 0) := by
      filter_upwards [hgood] with ω ⟨_, hs⟩
      have hc : inService ω.1 ω.2 0 = 0 := Nat.le_zero.1 (inService_spec hs 0).2.1
      rw [queueN_eq hs, queueR, hc]
      simp [depT, arrT, Prod.map]
    rw [Measure.map_congr hae, ← Measure.map_prod_map _ _ measurable_const
      (measurable_pi_apply 0), Measure.map_const, measure_univ, one_smul,
      Measure.infinitePi_map_eval]
  refine isMarkovChain_of_regeneration P P _ _ hΨ h0
    (fun n ω => inService ω.1 ω.2 n) (fun n k => measurableSet_inService_eq n k)
    (fun n k ω => (truncSeq n ω.1, truncSeq (k + 1) ω.2))
    (fun n k => ((measurable_truncSeq n).comp measurable_fst).prodMk
      ((measurable_truncSeq (k + 1)).comp measurable_snd))
    (fun n k ω => (tailSeq n ω.1, tailSeq (k + 1) ω.2))
    (fun n k => ((measurable_tailSeq n).comp measurable_fst).prodMk
      ((measurable_tailSeq (k + 1)).comp measurable_snd))
    (fun n k => gig1_law_past_future G H n k) (S := univ) MeasurableSet.univ
    (fun n k => ?_) measurable_gig1Step (fun n => ?_) _ (fun ix => ?_)
  · refine ⟨{b : (ℕ → ℝ) × (ℕ → ℝ) | arrT b.1 n < depT b.1 b.2 k ∧
        ∀ m < k, depT b.1 b.2 m ≤ arrT b.1 n}, ?_,
      fun b j => ((j : ℕ) - inService b.1 b.2 j,
        depT b.1 b.2 (inService b.1 b.2 j) - arrT b.1 j), ?_, ?_⟩
    · have hset : {b : (ℕ → ℝ) × (ℕ → ℝ) | ∀ m < k, depT b.1 b.2 m ≤ arrT b.1 n} =
          ⋂ m, ⋂ (_ : m < k), {b | depT b.1 b.2 m ≤ arrT b.1 n} := by
        ext b
        simp
      have hT2 : MeasurableSet {b : (ℕ → ℝ) × (ℕ → ℝ) | ∀ m < k,
          depT b.1 b.2 m ≤ arrT b.1 n} := by
        rw [hset]
        exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
          measurableSet_le (measurable_depT m) ((measurable_arrT n).comp measurable_fst)
      exact (measurableSet_lt ((measurable_arrT n).comp measurable_fst) (measurable_depT k)).inter
        hT2
    · refine measurable_pi_iff.2 fun j => ?_
      exact ((measurable_of_countable (fun l : ℕ => (j : ℕ) - l)).comp
        (measurable_inService j)).prodMk ((measurable_comp_index (measurable_inService j)
          (f := fun m ω => depT ω.1 ω.2 m) measurable_depT).sub
            ((measurable_arrT j).comp measurable_fst))
    · filter_upwards [hgood] with ω ⟨ha, hs⟩
      obtain ⟨a, s⟩ := ω
      simp only at ha hs
      refine ⟨?_, fun hk j => ?_⟩
      · rw [inService_eq_iff_truncSeq hs n k]
        simp only [mem_univ, and_true]
      · have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.2
        subst hk
        simp only
        rw [inService_truncSeq ha hs hj, queueN_eq hs, arrT_truncSeq hj,
          depT_truncSeq _ ((inService_spec hs (j : ℕ)).2.1.trans hj)
            (inService_mono ha hs hj)]
        rfl
  · filter_upwards [hgood] with ω ⟨ha, hs⟩
    exact gig1_step_eq ha hs n
  · obtain ⟨i, x⟩ := ix
    simp only [mem_univ, ofPred_true, cond_univ]
    rw [gig1Ladder_eq_map H G hH0' hHpos hG0 i x]
    have hm : Measurable fun y : (ℕ → ℝ) × (ℕ → ℝ) => (y.1 0, y.2) :=
      ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
    have hlaw : P.map (fun y : (ℕ → ℝ) × (ℕ → ℝ) => (y.1 0, y.2)) =
        G.prod (Measure.infinitePi fun _ : ℕ => H) := by
      rw [show (fun y : (ℕ → ℝ) × (ℕ → ℝ) => (y.1 0, y.2)) =
          Prod.map (fun a : ℕ → ℝ => a 0) id from rfl,
        ← Measure.map_prod_map _ _ (measurable_pi_apply 0) measurable_id,
        Measure.infinitePi_map_eval, Measure.map_id]
    rw [← hlaw, Measure.map_map (measurable_gig1Step0 i x) hm]
    rfl

end MeynTweedie.VUniformErgodicity
