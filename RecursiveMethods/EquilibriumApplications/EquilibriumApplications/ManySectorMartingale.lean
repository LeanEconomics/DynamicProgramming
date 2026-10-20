/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorPricing
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Martingale.Basic

/-!
# The martingale property on the space of histories (SLP p. 485)

SLP §16.2, p. 485. The state of the many-sector growth model is `s_t = (x_t, z_t)`; next
period's state is `(g(x_t, z_t), z_{t+1})` with `z_{t+1} ∼ Q(z_t, ·)` (`msStateKernel`). The law of
the history `ω = (s₀, s₁, s₂, …)` started at `s₀ = (x₀, z₀)` is built by the Ionescu-Tulcea theorem
(Mathlib's `Kernel.traj`, `msPathM`), and `E_t` is conditional expectation given the natural
filtration `σ(s₀, …, s_t)` of the coordinate process (`Filtration.piLE`). With `m = U′ ∘ c`,
`w_{t+1} = β m(s_{t+1})(f(s_{t+1}) + q(s_{t+1})) − m(s_t) q(s_t)` (`msIncr`) and
`W_t = Σ_{s=1}^t w_s` (`msW`, `W_0 = 0`).

* `ms_markov_property`: `E[h(s_{t+1}) | s₀, …, s_t] = ∫ h dP(s_t, ·)` a.s. for integrable
  `h(s_{t+1})`; `ms_lintegral_succ`, `ms_lintegral_zero`: the unconditional identities
  `E h(s_{t+1}) = E ∫ h dP(s_t, ·)` and `E G(s₀) = G(s₀)` for nonnegative `h`, `G`.
* `msW_adapted`: `W_t` is a function of `(x_s, z_s)_{s ≤ t}`.
* `msW_integrable`: `W_t` is integrable when `U′(c_t) f_t` and `U′(c_t) q_t` are.
* `msIncr_condExp`: (3′) on the space of histories: `E[w_{t+1} | s₀, …, s_t] = 0` a.s.
* **The martingale property** (`ms_martingale`, p. 485): if `q` solves (3) (`MsEq3`) and
  `U′(c_t) f_t`, `U′(c_t) q_t` are integrable on the space of histories, `{W_t}` is a martingale.
* `ms_path_integrable_of_nonneg`, `ms_martingale_of_nonneg`: for `β > 0`, `U′ ≥ 0`, `f ≥ 0` and
  `q ≥ 0` the integrability is automatic (`E[U′(c_{t+1})(f_{t+1} + q_{t+1})] = E[U′(c_t)q_t]/β`),
  so `{W_t}` is a martingale with no further hypothesis.
* `ms_martingale_of_bounded`: the same when `U′(c) f` and `U′(c) q` are bounded (the book's NOTE).
* `ms_martingale_prices_path`, `ms_martingale_prices_path_of_nonneg`: with `U′(c_t) = U′(c_{t+1})`,
  `β = 1` and `f = 0`, `{q_t}` itself is a martingale.

**Correction.**
* (p. 485) "`{W_t}` is a martingale" needs integrability on the space of histories, which (3) at
  every state does not give (`ms_martingale_counterexample`): with `U′(c) ≡ 1`, `β = 1`, `f = 0`,
  shocks `(0, 0) → (n + 1, 0)` with probability `2^{-(n+1)}`, then `→ (n + 1, 1)` or
  `(n + 1, 2)` with probability `1/2`, and `q = ±2^{n+1}` there (`0` elsewhere), `q` solves (3)
  at every state but `E|W_2| = ∞`, so `W` is not a martingale. Integrability holds for
  nonnegative dividends and prices or bounded `U′(c) f`, `U′(c) q`, as above.
* The book indexes `{W_t}_{t ≥ 1}`; here `W_0 = 0` is included (the martingale property at `t = 0`
  is `E W_1 = 0`).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-! ### Paths of a Markov chain -/

variable {S : Type*} [MeasurableSpace S]

/-- The kernels `(s₀, …, sₙ) ↦ P(sₙ, ·)` that drive the path of the chain. -/
noncomputable def msTrajKernel (P : Kernel S S) (n : ℕ) : Kernel (Π _ : Finset.Iic n, S) S :=
  P.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

/-- The driving kernels are Markov. -/
theorem isMarkovKernel_msTrajKernel (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (msTrajKernel P n) := by
  unfold msTrajKernel
  infer_instance

/-- The law of the path `(s₀, s₁, s₂, …)` of the Markov chain with transition `P` started at `s₀`
(SLP §8.2), built by the Ionescu-Tulcea theorem. -/
noncomputable def msPathM (P : Kernel S S) [IsMarkovKernel P] (s₀ : S) : Measure (ℕ → S) :=
  @Kernel.traj (fun _ => S) _ (msTrajKernel P) (isMarkovKernel_msTrajKernel P) 0 (fun _ => s₀)

/-- The path law is a probability measure. -/
theorem isProbabilityMeasure_msPathM (P : Kernel S S) [IsMarkovKernel P] (s₀ : S) :
    IsProbabilityMeasure (msPathM P s₀) := by
  have := isMarkovKernel_msTrajKernel P
  unfold msPathM
  infer_instance

/-- The `k`-th coordinate is measurable for the σ-algebra of the coordinates `0, …, k`. -/
theorem ms_measurable_coord_piLE (k : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => S) k] fun ω : ℕ → S => ω k :=
  fun s hs => ⟨(fun x : Π _ : Set.Iic k, S => x ⟨k, Set.mem_Iic.2 le_rfl⟩) ⁻¹' s,
    measurable_pi_apply _ hs, rfl⟩

/-- **The Markov property** for integrable observables: if `h(σ_{t+1})` is integrable,
`E[h(σ_{t+1}) | σ₀, …, σ_t] = ∫ h dP(σ_t, ·)` a.s. -/
theorem ms_markov_property (P : Kernel S S) [IsMarkovKernel P] (s₀ : S) {h : S → ℝ}
    (hh : Measurable h) (t : ℕ)
    (hint : Integrable (fun ω : ℕ → S => h (ω (t + 1))) (msPathM P s₀)) :
    (msPathM P s₀)[fun ω => h (ω (t + 1)) | Filtration.piLE (X := fun _ : ℕ => S) t]
      =ᵐ[msPathM P s₀] fun ω => ∫ y, h y ∂P (ω t) := by
  have := isMarkovKernel_msTrajKernel P
  have hce := Kernel.condExp_traj (X := fun _ => S) (κ := msTrajKernel P) (Nat.zero_le t)
    (x₀ := fun _ => s₀) hint
  refine hce.trans (Eventually.of_forall fun ω => ?_)
  change ∫ y, h (y (t + 1)) ∂(Kernel.traj (msTrajKernel P) t) (Preorder.frestrictLe t ω) =
    ∫ y, h y ∂P (ω t)
  rw [← integral_map (φ := fun y : ℕ → S => y (t + 1)) (f := h)
    (measurable_pi_apply (t + 1)).aemeasurable hh.aestronglyMeasurable,
    ← Kernel.map_apply _ (measurable_pi_apply _), Kernel.map_traj_succ_self]
  rfl

/-- The one-step identity for nonnegative observables:
`E h(σ_{t+1}) = E ∫ h dP(σ_t, ·)`. -/
theorem ms_lintegral_succ (P : Kernel S S) [IsMarkovKernel P] (s₀ : S) {h : S → ℝ≥0∞}
    (hh : Measurable h) (t : ℕ) :
    ∫⁻ ω, h (ω (t + 1)) ∂msPathM P s₀ = ∫⁻ ω, ∫⁻ y, h y ∂P (ω t) ∂msPathM P s₀ := by
  have := isMarkovKernel_msTrajKernel P
  have hc := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => S) (κ := msTrajKernel P)
    (Nat.zero_le t) (x₀ := fun _ => s₀)
  have hF : Measurable fun x : ℕ → S => (Preorder.frestrictLe t x, x (t + 1)) :=
    (Preorder.measurable_frestrictLe t).prodMk (measurable_pi_apply _)
  have hG : Measurable fun y : Π _ : Finset.Iic t, S => ∫⁻ s, h s ∂msTrajKernel P t y :=
    hh.lintegral_kernel
  have e1 : ∫⁻ ω, h (ω (t + 1)) ∂msPathM P s₀ = ∫⁻ p, h p.2
      ∂(Kernel.partialTraj (X := fun _ => S) (msTrajKernel P) 0 t (fun _ => s₀) ⊗ₘ
        msTrajKernel P t) := by
    rw [hc, lintegral_map (f := fun p : (Π _ : Finset.Iic t, S) × S => h p.2)
      (hh.comp measurable_snd) hF]
    rfl
  rw [e1, Measure.lintegral_compProd (f := fun p : (Π _ : Finset.Iic t, S) × S => h p.2)
    (hh.comp measurable_snd), ← Kernel.traj_map_frestrictLe_apply (X := fun _ => S),
    lintegral_map hG (Preorder.measurable_frestrictLe t)]
  rfl

/-- The law of `σ₀` is `δ_{s₀}`. -/
theorem msPathM_map_zero (P : Kernel S S) [IsMarkovKernel P] (s₀ : S) :
    (msPathM P s₀).map (fun ω => ω 0) = Measure.dirac s₀ := by
  have := isMarkovKernel_msTrajKernel P
  have hg : Measurable fun x : Π _ : Finset.Iic 0, S => x ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  have hfr := Preorder.measurable_frestrictLe (X := fun _ : ℕ => S) 0
  have h1 := Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := msTrajKernel P) 0 0
  rw [Kernel.partialTraj_self] at h1
  have h3 := congrArg (fun η => (η (fun _ : Finset.Iic 0 => s₀)).map
    (fun x : Π _ : Finset.Iic 0, S => x ⟨0, Finset.mem_Iic.2 le_rfl⟩)) h1
  simp only [Kernel.map_apply _ hfr, Kernel.id_apply, Measure.map_dirac' hg,
    Measure.map_map hg hfr] at h3
  exact h3

/-- `E G(σ₀) = G(s₀)` for measurable `G ≥ 0`. -/
theorem ms_lintegral_zero (P : Kernel S S) [IsMarkovKernel P] (s₀ : S) {G : S → ℝ≥0∞}
    (hG : Measurable G) : ∫⁻ ω, G (ω 0) ∂msPathM P s₀ = G s₀ := by
  rw [← lintegral_map hG (measurable_pi_apply 0), msPathM_map_zero, lintegral_dirac' _ hG]

/-! ### The state chain of the growth model -/

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- The transition of the state `(x, z)`: next period's state is `(g(x, z), z′)` with
`z′ ∼ Q(z, ·)`. -/
noncomputable abbrev msStateKernel (Q : Kernel Z Z) (g : X × Z → X) (hg : Measurable g) :
    Kernel (X × Z) (X × Z) :=
  Kernel.deterministic g hg ×ₖ Q.comap Prod.snd measurable_snd

/-- `P((x, z), ·)` is the law of `(g(x, z), z′)`, `z′ ∼ Q(z, ·)`. -/
theorem msStateKernel_apply (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X}
    (hg : Measurable g) (s : X × Z) :
    msStateKernel Q g hg s = (Q s.2).map (Prod.mk (g s)) := by
  rw [Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply, Measure.dirac_prod]

/-- The book's `E_t`: for `h` measurable and integrable against `P((x, z), ·)`,
`∫ h dP((x, z), ·) = ∫ h(g(x, z), z′) Q(z, dz′)`. -/
theorem integral_msStateKernel (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X}
    (hg : Measurable g) {h : X × Z → ℝ} (hh : Measurable h) (s : X × Z) :
    ∫ y, h y ∂msStateKernel Q g hg s = ∫ z', h (g s, z') ∂Q s.2 := by
  rw [msStateKernel_apply Q hg s, integral_map measurable_prodMk_left.aemeasurable
    hh.aestronglyMeasurable]

/-- Integrability against `P((x, z), ·)` is integrability of `z′ ↦ h(g(x, z), z′)` against
`Q(z, ·)`. -/
theorem integrable_msStateKernel_iff (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X}
    (hg : Measurable g) {h : X × Z → ℝ} (hh : Measurable h) (s : X × Z) :
    Integrable h (msStateKernel Q g hg s) ↔ Integrable (fun z' => h (g s, z')) (Q s.2) := by
  rw [msStateKernel_apply Q hg s, integrable_map_measure hh.aestronglyMeasurable
    measurable_prodMk_left.aemeasurable]
  rfl

/-- The increment `w_{t+1} = β U′(c_{t+1})(f_{t+1} + q_{t+1}) − U′(c_t) q_t` along the path
`ω = ((x₀, z₀), (x₁, z₁), …)`, with `m = U′ ∘ c`. -/
def msIncr (β : ℝ) (m f q : X × Z → ℝ) (t : ℕ) (ω : ℕ → X × Z) : ℝ :=
  β * (m (ω (t + 1)) * (f (ω (t + 1)) + q (ω (t + 1)))) - m (ω t) * q (ω t)

/-- The book's `W_t = Σ_{s=1}^t w_s` (p. 485), with `W_0 = 0`. -/
def msW (β : ℝ) (m f q : X × Z → ℝ) (t : ℕ) (ω : ℕ → X × Z) : ℝ :=
  ∑ s ∈ Finset.range t, msIncr β m f q s ω

omit [MeasurableSpace X] [MeasurableSpace Z] in
/-- `W_{t+1} − W_t = w_{t+1}`. -/
theorem msW_succ_sub (β : ℝ) (m f q : X × Z → ℝ) (t : ℕ) :
    msW β m f q (t + 1) - msW β m f q t = msIncr β m f q t := by
  funext ω
  simp [msW, Finset.sum_range_succ]

/-- **`W_t` is adapted**: it is a function of `(x_s, z_s)_{s ≤ t}`. -/
theorem msW_adapted {β : ℝ} {m f q : X × Z → ℝ} (hm : Measurable m) (hf : Measurable f)
    (hq : Measurable q) :
    StronglyAdapted (Filtration.piLE (X := fun _ : ℕ => X × Z)) (msW β m f q) := by
  intro t
  have hc : ∀ k, k ≤ t → Measurable[Filtration.piLE (X := fun _ : ℕ => X × Z) t]
      fun ω : ℕ → X × Z => ω k := fun k hk =>
    (ms_measurable_coord_piLE k).mono (Filtration.piLE.mono hk) le_rfl
  refine Measurable.stronglyMeasurable ?_
  refine Finset.measurable_sum _ fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  have h1 := hc (s + 1) hs'
  have h0 := hc s hs'.le
  exact (((hm.comp h1).mul ((hf.comp h1).add (hq.comp h1))).const_mul β).sub
    ((hm.comp h0).mul (hq.comp h0))

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **`W_t` is integrable** when `U′(c_t) f_t` and `U′(c_t) q_t` are integrable on the space of
histories. -/
theorem msW_integrable {β : ℝ} {m f q : X × Z → ℝ}
    (hif : ∀ t, Integrable (fun ω => m (ω t) * f (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀)))
    (hiq : ∀ t, Integrable (fun ω => m (ω t) * q (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀)))
    (t : ℕ) : Integrable (msW β m f q t) (msPathM (msStateKernel Q g hg) (x₀, z₀)) := by
  refine integrable_finsetSum _ fun s _ => ?_
  refine ((((hif (s + 1)).add (hiq (s + 1))).const_mul β).sub (hiq s)).congr
    (Eventually.of_forall fun ω => ?_)
  simp only [msIncr, Pi.add_apply, Pi.sub_apply, mul_add]

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **(3′) on the space of histories**: if `q` solves (3), then
`E[w_{t+1} | (x_s, z_s)_{s ≤ t}] = 0` a.s. -/
theorem msIncr_condExp {β : ℝ} {m f q : X × Z → ℝ} (hm : Measurable m) (hf : Measurable f)
    (hq : Measurable q) (h : MsEq3 Q β m g f q)
    (hif : ∀ t, Integrable (fun ω => m (ω t) * f (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀)))
    (hiq : ∀ t, Integrable (fun ω => m (ω t) * q (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀)))
    (t : ℕ) :
    (msPathM (msStateKernel Q g hg) (x₀, z₀))[msIncr β m f q t |
      Filtration.piLE (X := fun _ : ℕ => X × Z) t] =ᵐ[msPathM (msStateKernel Q g hg) (x₀, z₀)]
      0 := by
  have := isProbabilityMeasure_msPathM (msStateKernel Q g hg) (x₀, z₀)
  set μ := msPathM (msStateKernel Q g hg) (x₀, z₀)
  have hΦm : Measurable fun s : X × Z => β * (m s * (f s + q s)) :=
    ((hm.mul (hf.add hq))).const_mul β
  have hΦ : Integrable (fun ω : ℕ → X × Z => β * (m (ω (t + 1)) * (f (ω (t + 1)) +
      q (ω (t + 1))))) μ :=
    (((hif (t + 1)).add (hiq (t + 1))).const_mul β).congr
      (Eventually.of_forall fun ω => by simp only [Pi.add_apply, mul_add])
  have h1 := ms_markov_property (msStateKernel Q g hg) (x₀, z₀) hΦm t hΦ
  have hΨm : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => X × Z) t]
      fun ω : ℕ → X × Z => m (ω t) * q (ω t) :=
    ((hm.comp (ms_measurable_coord_piLE t)).mul
      (hq.comp (ms_measurable_coord_piLE t))).stronglyMeasurable
  have h2 := condExp_of_stronglyMeasurable (μ := μ) (Filtration.piLE.le t) hΨm (hiq t)
  have h3 := condExp_sub (m := Filtration.piLE (X := fun _ : ℕ => X × Z) t) hΦ (hiq t)
  have he : msIncr β m f q t = (fun ω : ℕ → X × Z => β * (m (ω (t + 1)) * (f (ω (t + 1)) +
      q (ω (t + 1))))) - fun ω => m (ω t) * q (ω t) := rfl
  rw [he]
  filter_upwards [h3, h1] with ω e3 e1
  rw [e3, Pi.sub_apply, e1, h2, integral_msStateKernel Q hg hΦm, integral_const_mul]
  obtain ⟨-, -, e⟩ := h (ω t).1 (ω t).2
  rw [Prod.mk.eta] at e
  rw [← e, Pi.zero_apply, sub_self]

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **The martingale property** (SLP p. 485): if `q` solves (3) and `U′(c_t) f_t`,
`U′(c_t) q_t` are integrable on the space of histories, then `W_t = Σ_{s=1}^t w_s` is a
martingale for the natural filtration of the state process `(x_t, z_t)`. -/
theorem ms_martingale {β : ℝ} {m f q : X × Z → ℝ} (hm : Measurable m) (hf : Measurable f)
    (hq : Measurable q) (h : MsEq3 Q β m g f q)
    (hif : ∀ t, Integrable (fun ω => m (ω t) * f (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀)))
    (hiq : ∀ t, Integrable (fun ω => m (ω t) * q (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀))) :
    Martingale (msW β m f q) (Filtration.piLE (X := fun _ : ℕ => X × Z))
      (msPathM (msStateKernel Q g hg) (x₀, z₀)) := by
  have := isProbabilityMeasure_msPathM (msStateKernel Q g hg) (x₀, z₀)
  refine martingale_of_condExp_sub_eq_zero_nat (msW_adapted hm hf hq)
    (msW_integrable Q hg x₀ z₀ hif hiq) fun t => ?_
  rw [msW_succ_sub]
  exact msIncr_condExp Q hg x₀ z₀ hm hf hq h hif hiq t

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **Integrability is automatic for nonnegative dividends and prices**: if `β > 0`,
`U′(c) ≥ 0`, `f ≥ 0`, `q ≥ 0` and `q` solves (3), then `E[U′(c_{t+1})(f_{t+1} + q_{t+1})] =
E[U′(c_t) q_t]/β`, so `U′(c_t) f_t` and `U′(c_t) q_t` are integrable on the space of histories. -/
theorem ms_path_integrable_of_nonneg {β : ℝ} (hβ : 0 < β) {m f q : X × Z → ℝ}
    (hm : Measurable m) (hf : Measurable f) (hq : Measurable q) (hm0 : ∀ p, 0 ≤ m p)
    (hf0 : ∀ p, 0 ≤ f p) (hq0 : ∀ p, 0 ≤ q p) (h : MsEq3 Q β m g f q) :
    (∀ t, Integrable (fun ω => m (ω t) * f (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀))) ∧
      ∀ t, Integrable (fun ω => m (ω t) * q (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀)) := by
  set μ := msPathM (msStateKernel Q g hg) (x₀, z₀)
  set Φ : X × Z → ℝ := fun s => m s * (f s + q s)
  have hΦm : Measurable Φ := hm.mul (hf.add hq)
  have hΦ0 : ∀ s, 0 ≤ Φ s := fun s => mul_nonneg (hm0 s) (add_nonneg (hf0 s) (hq0 s))
  have hΦ : ∀ s, Integrable Φ (msStateKernel Q g hg s) := fun s => by
    obtain ⟨iq, iff, -⟩ := h s.1 s.2
    simp only [Prod.mk.eta] at iq iff
    rw [integrable_msStateKernel_iff Q hg hΦm]
    exact (iff.add iq).congr (Eventually.of_forall fun z' => by simp only [Φ, Pi.add_apply,
      mul_add])
  -- one step: `∫ Φ dP(s, ·) = m(s) q(s) / β ≤ Φ(s) / β`
  have hstep : ∀ s, ∫⁻ y, ENNReal.ofReal (Φ y) ∂msStateKernel Q g hg s ≤
      ENNReal.ofReal (Φ s) * ENNReal.ofReal β⁻¹ := fun s => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hΦ s) (Eventually.of_forall hΦ0),
      ← ENNReal.ofReal_mul (hΦ0 s), integral_msStateKernel Q hg hΦm]
    obtain ⟨-, -, e⟩ := h s.1 s.2
    rw [Prod.mk.eta] at e
    refine ENNReal.ofReal_le_ofReal ?_
    have : ∫ z', Φ (g s, z') ∂Q s.2 = m s * q s * β⁻¹ := by
      rw [e, mul_comm β, mul_assoc, mul_inv_cancel₀ hβ.ne', mul_one]
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hβ.le)
    simp only [Φ]
    nlinarith [hm0 s, hf0 s]
  have key : ∀ t, ∫⁻ ω, ENNReal.ofReal (Φ (ω t)) ∂μ < ∞ := by
    intro t
    induction t with
    | zero =>
      rw [ms_lintegral_zero _ _ (G := fun s => ENNReal.ofReal (Φ s))
        (ENNReal.measurable_ofReal.comp hΦm)]
      exact ENNReal.ofReal_lt_top
    | succ t ih =>
      rw [ms_lintegral_succ _ _ (h := fun s => ENNReal.ofReal (Φ s))
        (ENNReal.measurable_ofReal.comp hΦm)]
      refine lt_of_le_of_lt (lintegral_mono fun ω => hstep (ω t)) ?_
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ih ENNReal.ofReal_lt_top
  have hint : ∀ (t : ℕ) (k : X × Z → ℝ), Measurable k → (∀ s, 0 ≤ k s) → (∀ s, k s ≤ Φ s) →
      Integrable (fun ω : ℕ → X × Z => k (ω t)) μ := fun t k hk hk0 hkΦ => by
    refine ⟨(hk.comp (measurable_pi_apply t)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) (key t)
    rw [Real.enorm_eq_ofReal (hk0 _)]
    exact ENNReal.ofReal_le_ofReal (hkΦ _)
  refine ⟨fun t => hint t (fun s => m s * f s) (hm.mul hf)
    (fun s => mul_nonneg (hm0 s) (hf0 s)) fun s => ?_, fun t => hint t (fun s => m s * q s)
    (hm.mul hq) (fun s => mul_nonneg (hm0 s) (hq0 s)) fun s => ?_⟩
  · simp only [Φ]; nlinarith [hm0 s, hq0 s]
  · simp only [Φ]; nlinarith [hm0 s, hf0 s]

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **The martingale property for nonnegative dividends and prices** (SLP p. 485): if `β > 0`,
`U′(c) ≥ 0`, `f, q ≥ 0` and `q` solves (3), then `W_t` is a martingale on the space of histories,
with no further integrability assumption. -/
theorem ms_martingale_of_nonneg {β : ℝ} (hβ : 0 < β) {m f q : X × Z → ℝ}
    (hm : Measurable m) (hf : Measurable f) (hq : Measurable q) (hm0 : ∀ p, 0 ≤ m p)
    (hf0 : ∀ p, 0 ≤ f p) (hq0 : ∀ p, 0 ≤ q p) (h : MsEq3 Q β m g f q) :
    Martingale (msW β m f q) (Filtration.piLE (X := fun _ : ℕ => X × Z))
      (msPathM (msStateKernel Q g hg) (x₀, z₀)) :=
  have hi := ms_path_integrable_of_nonneg Q hg x₀ z₀ hβ hm hf hq hm0 hf0 hq0 h
  ms_martingale Q hg x₀ z₀ hm hf hq h hi.1 hi.2

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **The martingale property for bounded `U′(c) f` and `U′(c) q`** (the NOTE to p. 485): then
`W_t` is a martingale on the space of histories. -/
theorem ms_martingale_of_bounded {β : ℝ} {m f q : X × Z → ℝ} (hm : Measurable m)
    (hf : Measurable f) (hq : Measurable q) (h : MsEq3 Q β m g f q) {C : ℝ}
    (hCf : ∀ p, |m p * f p| ≤ C) (hCq : ∀ p, |m p * q p| ≤ C) :
    Martingale (msW β m f q) (Filtration.piLE (X := fun _ : ℕ => X × Z))
      (msPathM (msStateKernel Q g hg) (x₀, z₀)) := by
  have := isProbabilityMeasure_msPathM (msStateKernel Q g hg) (x₀, z₀)
  refine ms_martingale Q hg x₀ z₀ hm hf hq h (fun t => ?_) fun t => ?_
  · exact Integrable.of_bound ((hm.mul hf).comp (measurable_pi_apply t)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hCf _)
  · exact Integrable.of_bound ((hm.mul hq).comp (measurable_pi_apply t)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hCq _)

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **The martingale property of stock prices on the space of histories** (p. 485): with
constant marginal utility `m₀ > 0`, `β = 1` and no dividend, if `q` solves (3) and each `q_t` is
integrable, then `{q_t}` is a martingale for the natural filtration of `(x_t, z_t)`. -/
theorem ms_martingale_prices_path {m₀ : ℝ} (hm₀ : 0 < m₀) {q : X × Z → ℝ} (hq : Measurable q)
    (h : MsEq3 Q 1 (fun _ => m₀) g (fun _ => 0) q)
    (hiq : ∀ t, Integrable (fun ω => q (ω t)) (msPathM (msStateKernel Q g hg) (x₀, z₀))) :
    Martingale (fun t ω => q (ω t)) (Filtration.piLE (X := fun _ : ℕ => X × Z))
      (msPathM (msStateKernel Q g hg) (x₀, z₀)) := by
  have := isProbabilityMeasure_msPathM (msStateKernel Q g hg) (x₀, z₀)
  refine martingale_nat (fun t => (hq.comp (ms_measurable_coord_piLE t)).stronglyMeasurable) hiq
    fun t => ?_
  filter_upwards [ms_markov_property (msStateKernel Q g hg) (x₀, z₀) hq t (hiq (t + 1))]
    with ω e
  rw [e, integral_msStateKernel Q hg hq]
  have := ms_martingale_prices hm₀ h (ω t).1 (ω t).2
  rwa [Prod.mk.eta] at this

variable (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) (x₀ : X)
  (z₀ : Z) in
/-- **The martingale property of stock prices** for nonnegative prices: with constant marginal
utility `m₀ > 0`, `β = 1`, no dividend and `q ≥ 0` solving (3), `{q_t}` is a martingale on the
space of histories (integrability is automatic, `ms_path_integrable_of_nonneg`). -/
theorem ms_martingale_prices_path_of_nonneg {m₀ : ℝ} (hm₀ : 0 < m₀) {q : X × Z → ℝ}
    (hq : Measurable q) (hq0 : ∀ p, 0 ≤ q p) (h : MsEq3 Q 1 (fun _ => m₀) g (fun _ => 0) q) :
    Martingale (fun t ω => q (ω t)) (Filtration.piLE (X := fun _ : ℕ => X × Z))
      (msPathM (msStateKernel Q g hg) (x₀, z₀)) := by
  have hi := (ms_path_integrable_of_nonneg Q hg x₀ z₀ one_pos measurable_const measurable_const
    hq (fun _ => hm₀.le) (fun _ => le_rfl) hq0 h).2
  refine ms_martingale_prices_path Q hg x₀ z₀ hm₀ hq h fun t => ((hi t).const_mul m₀⁻¹).congr
    (Eventually.of_forall fun ω => ?_)
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ hm₀.ne', one_mul]

/-! ### Counterexample: (3) at every state does not make `W_t` integrable -/

/-- The weights `2^{-(n+1)}` on `ℕ`, a probability measure. -/
noncomputable def msCexNu : Measure ℕ :=
  Measure.sum fun n : ℕ => ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ • Measure.dirac n

/-- `Σ_n 2^{-(n+1)} = 1`. -/
theorem msCexNu_univ : msCexNu univ = 1 := by
  simp only [msCexNu, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  simp_rw [ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The shock transition of the counterexample on `Z = ℕ × ℕ`: from `(0, j)` jump to `(n + 1, 0)`
with probability `2^{-(n+1)}`; from `(k + 1, 0)` move to `(k + 1, 1)` or `(k + 1, 2)` with
probability `1/2` each; every other state is absorbing. -/
noncomputable def msCexQ (z : ℕ × ℕ) : Measure (ℕ × ℕ) :=
  if z.1 = 0 then msCexNu.map fun n => (n + 1, 0)
  else if z.2 = 0 then (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (z.1, 1) + Measure.dirac (z.1, 2))
  else Measure.dirac z

/-- The counterexample's shock kernel. -/
noncomputable def msCexKernel : Kernel (ℕ × ℕ) (ℕ × ℕ) := Kernel.ofFunOfCountable msCexQ

/-- The counterexample's shock kernel is Markov. -/
theorem isMarkovKernel_msCexKernel : IsMarkovKernel msCexKernel := by
  refine ⟨fun z => ⟨?_⟩⟩
  change msCexQ z univ = 1
  unfold msCexQ
  split_ifs with h1 h2
  · rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ, preimage_univ,
      msCexNu_univ]
  · simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  · exact measure_univ

/-- The counterexample's price: `q = ±2^{k+1}` at `(k + 1, 1)`, `(k + 1, 2)`, and `0` elsewhere. -/
noncomputable def msCexq (p : Unit × (ℕ × ℕ)) : ℝ :=
  if p.2.1 = 0 then 0 else if p.2.2 = 1 then 2 ^ p.2.1 else if p.2.2 = 2 then -2 ^ p.2.1 else 0

/-- The counterexample solves (3) at every state: `X = {∗}`, `U′(c) ≡ 1`, `β = 1`, `f = 0`,
`q = msCexq`. -/
theorem msCex_eq3 : MsEq3 (⇑msCexKernel) 1 (fun _ => 1) (fun _ => ()) (fun _ => 0) msCexq := by
  rintro ⟨⟩ ⟨k, j⟩
  refine ⟨?_, by simp, ?_⟩
  · change Integrable _ (msCexQ (k, j))
    unfold msCexQ
    split_ifs with h1 h2
    · rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
        (measurable_of_countable _).aemeasurable]
      simp [Function.comp_def, msCexq]
    · exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
        (by simp)
    · exact integrable_dirac (by simp)
  · simp only [one_mul, zero_add]
    change msCexq ((), (k, j)) = ∫ z', msCexq ((), z') ∂msCexQ (k, j)
    unfold msCexQ
    split_ifs with h1 h2
    · simp only at h1
      subst h1
      rw [integral_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
      simp [msCexq]
    · simp only at h1 h2
      subst h2
      rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
        (integrable_dirac (by simp)), integral_dirac, integral_dirac]
      simp [msCexq, h1]
    · rw [integral_dirac]

/-- **Counterexample (p. 485): `W_t` need not be a martingale.** A price process can solve (3)
at every state, with all the per-state integrability of `MsEq3`, and still have `W_2` not
integrable on the space of histories. Here `X = {∗}`, `U′(c) ≡ 1`, `β = 1`, `f = 0`, the shock
jumps from `(0, 0)` to `(n + 1, 0)` with probability `2^{-(n+1)}` and then to `(n + 1, 1)` or
`(n + 1, 2)` with probability `1/2` each, where `q = ±2^{n+1}`. Then `q_t = E_t q_{t+1}` at every
state, but `W_2 = q_2 − q_0` has `E|W_2| = Σ_n 2^{-(n+1)} 2^{n+1} = ∞`, so `W` is not a
martingale. -/
theorem ms_martingale_counterexample :
    haveI := isMarkovKernel_msCexKernel
    MsEq3 (⇑msCexKernel) 1 (fun _ => 1) (fun _ => ()) (fun _ => 0) msCexq ∧
      ¬ Integrable (msW 1 (fun _ => 1) (fun _ => 0) msCexq 2)
        (msPathM (msStateKernel msCexKernel (fun _ => ()) measurable_const) ((), (0, 0))) ∧
      ¬ Martingale (msW 1 (fun _ => 1) (fun _ => 0) msCexq)
        (Filtration.piLE (X := fun _ : ℕ => Unit × (ℕ × ℕ)))
        (msPathM (msStateKernel msCexKernel (fun _ => ()) measurable_const) ((), (0, 0))) := by
  have := isMarkovKernel_msCexKernel
  set P := msStateKernel msCexKernel (fun _ : Unit × (ℕ × ℕ) => ()) measurable_const
  set μ := msPathM P ((), (0, 0))
  have hnot : ¬ Integrable (msW 1 (fun _ => 1) (fun _ => 0) msCexq 2) μ := by
    intro hI
    set h : Unit × (ℕ × ℕ) → ℝ≥0∞ := fun s => ‖msCexq s‖ₑ
    have hG1 : ∀ n : ℕ, ∫⁻ y, h y ∂P ((), (n + 1, 0)) = 2 ^ (n + 1) := fun n => by
      rw [msStateKernel_apply msCexKernel measurable_const,
        lintegral_map (measurable_of_countable _) measurable_prodMk_left]
      change ∫⁻ z', h ((), z') ∂msCexQ (n + 1, 0) = _
      have hQ : msCexQ (n + 1, 0) =
          (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (n + 1, 1) + Measure.dirac (n + 1, 2)) := by
        simp [msCexQ]
      rw [hQ, lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac]
      simp only [h, msCexq]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, enorm_neg, enorm_pow,
        show (2 : ℕ) ≠ 1 by decide]
      rw [show ‖(2 : ℝ)‖ₑ = 2 by
          rw [Real.enorm_eq_ofReal zero_le_two, ENNReal.ofReal_ofNat],
        ← two_mul, smul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    have hG2 : ∫⁻ y, (∫⁻ y', h y' ∂P y) ∂P ((), (0, 0)) = ∞ := by
      rw [msStateKernel_apply msCexKernel measurable_const,
        lintegral_map (measurable_of_countable _) measurable_prodMk_left]
      change ∫⁻ z', (∫⁻ y', h y' ∂P ((), z')) ∂msCexQ (0, 0) = ∞
      have hQ : msCexQ (0, 0) = msCexNu.map fun n => (n + 1, 0) := by simp [msCexQ]
      rw [hQ, lintegral_map (measurable_of_countable _) (measurable_of_countable _), msCexNu,
        lintegral_sum_measure]
      simp_rw [lintegral_smul_measure, lintegral_dirac, hG1, smul_eq_mul]
      simp_rw [ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
      exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
    have hinf : ∫⁻ ω, h (ω 2) ∂μ = ∞ := by
      rw [ms_lintegral_succ P _ (h := h) (measurable_of_countable _) 1,
        ms_lintegral_succ P _ (h := fun y => ∫⁻ y', h y' ∂P y) (measurable_of_countable _) 0,
        ms_lintegral_zero P _ (G := fun y => ∫⁻ y'', (∫⁻ y', h y' ∂P y'') ∂P y)
          (measurable_of_countable _), hG2]
    have h0 : ∫⁻ ω, ‖msCexq (ω 0)‖ₑ ∂μ = 0 := by
      rw [ms_lintegral_zero P _ (G := fun s => ‖msCexq s‖ₑ) (measurable_of_countable _)]
      simp [msCexq]
    have hle : ∫⁻ ω, h (ω 2) ∂μ ≤ ∫⁻ ω, ‖msW 1 (fun _ => 1) (fun _ => 0) msCexq 2 ω‖ₑ ∂μ +
        ∫⁻ ω, ‖msCexq (ω 0)‖ₑ ∂μ := by
      have hmeas : Measurable fun ω : ℕ → Unit × (ℕ × ℕ) => ‖msCexq (ω 0)‖ₑ :=
        (measurable_of_countable (fun s : Unit × (ℕ × ℕ) => ‖msCexq s‖ₑ)).comp
          (measurable_pi_apply 0)
      refine le_trans (lintegral_mono fun ω => ?_) (le_of_eq (lintegral_add_right _ hmeas))
      have e : msCexq (ω 2) = msW 1 (fun _ => 1) (fun _ => 0) msCexq 2 ω + msCexq (ω 0) := by
        simp only [msW, msIncr, Finset.sum_range_succ, Finset.sum_range_zero]
        ring
      simp only [h]
      rw [e]
      exact enorm_add_le _ _
    rw [hinf, h0, add_zero] at hle
    exact absurd (lt_of_le_of_lt hle hI.2) (lt_irrefl _)
  exact ⟨msCex_eq3, hnot, fun hM => hnot (hM.integrable 2)⟩

end StokeyLucasPrescott.EquilibriumApplications
