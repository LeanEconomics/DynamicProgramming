/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AAConcavity
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Hom.Basic

/-!
# Comparative risk aversion

Miao, §20.3.2, pp. 705–706: comparative risk aversion of recursive utilities on the event tree
(finite horizon, `U_T = c_T`; `aa_recU` of `AAConcavity`).

* A plan is deterministic if consumption depends only on the date (`aa_Deterministic`); `U¹` is
  more risk averse than `U²` if `U²_t(b) > U²_t(c) ⇒ U¹_t(b) > U¹_t(c)` for deterministic `b`, at
  every node and horizon (`aa_MoreRiskAverse`); `U¹` is risk averse relative to a family of
  benchmarks (`aa_RiskAverse`, the book's definition).
* With a common aggregator, both utilities agree on deterministic plans
  (`aa_recU_deterministic`).
* **Proposition 20.3.1**, first part: for a common aggregator `W` strictly increasing in its second
  argument and conditional certainty equivalents with `M(k) = k`, `U¹` is more risk averse than
  `U²` iff `M¹_t ≤ M²_t` for all `t` (`proposition_20_3_1`).
* **Proposition 20.3.1**, second part ("standard risk theory", Pratt): for the expected-utility
  certainty equivalents `u_i⁻¹E u_i` on an interval `D`, `M¹ ≤ M²` for all lotteries iff
  `u₁ = φ ∘ u₂` with `φ` increasing and concave (`aa_pratt_of_concave`, `aa_concave_of_pratt`,
  `proposition_20_3_1_pratt`), so with `u_i` order isomorphisms of `ℝ` a concave `φ` makes `U¹` more
  risk averse (`proposition_20_3_1_ez`). Departure: the converse needs the certainty-equivalent
  comparison for all two-point lotteries; on a tree with given conditional probabilities the first
  part only yields it for those probabilities.
* The book's definition of risk aversion is never satisfied, since `c = b` is allowed
  (`aa_riskAverse_never`); and even for random `c` (`aa_RiskAverse'`), being more risk averse than a
  risk-neutral `U²` does not imply it (`aa_moreRiskAverse_not_riskAverse`).

Not formalised: comparative ambiguity aversion (the text only discusses the approaches of
Ghirardato–Marinacci and Epstein, without statements).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- A deterministic plan: consumption depends only on the date. -/
def aa_Deterministic (b : List S → ℝ) : Prop := ∀ h h' : List S, h.length = h'.length → b h = b h'

/-- `U¹` (certainty equivalents `M₁`) is more risk averse than `U²` (`M₂`), with common aggregator
`W`: whenever `U²` prefers a deterministic plan `b` to a plan `c`, so does `U¹`. -/
def aa_MoreRiskAverse (W : ℝ → ℝ → ℝ) (M₁ M₂ : List S → (S → ℝ) → ℝ) : Prop :=
  ∀ n h (b c : List S → ℝ), aa_Deterministic b →
    aa_recU W M₂ c n h < aa_recU W M₂ b n h → aa_recU W M₁ c n h < aa_recU W M₁ b n h

/-- The book's risk aversion: `U²_t(b) = U²_t(c) ⇒ U¹_t(b) > U¹_t(c)` for deterministic `b`, for
every benchmark `M₂` in the family `B`. -/
def aa_RiskAverse (W : ℝ → ℝ → ℝ) (M₁ : List S → (S → ℝ) → ℝ)
    (B : Set (List S → (S → ℝ) → ℝ)) : Prop :=
  ∀ M₂ ∈ B, ∀ n h (b c : List S → ℝ), aa_Deterministic b →
    aa_recU W M₂ c n h = aa_recU W M₂ b n h → aa_recU W M₁ c n h < aa_recU W M₁ b n h

/-- The certainty-equivalent property `M(k) = k`. -/
def aa_IsCE (M : List S → (S → ℝ) → ℝ) : Prop := ∀ h k, M h (fun _ => k) = k

omit [Fintype S] in
/-- A deterministic plan has the same utility at every node of a given date, and all utilities with
the aggregator `W` and certainty equivalents agree on it. -/
theorem aa_recU_deterministic [Nonempty S] (W : ℝ → ℝ → ℝ) {M₁ M₂ : List S → (S → ℝ) → ℝ}
    (h₁ : aa_IsCE M₁) (h₂ : aa_IsCE M₂) {b : List S → ℝ} (hb : aa_Deterministic b) :
    ∀ n (g g' : List S), g.length = g'.length → aa_recU W M₁ b n g = aa_recU W M₂ b n g' := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  intro n
  induction n with
  | zero => intro g g' hg; exact hb g g' hg
  | succ n ih =>
    intro g g' hg
    simp only [aa_recU]
    have e1 : (fun s => aa_recU W M₁ b n (s :: g)) = fun _ => aa_recU W M₁ b n (s₀ :: g) :=
      funext fun s => (ih (s :: g) (s₀ :: g) rfl).trans (ih (s₀ :: g) (s₀ :: g) rfl).symm |>.trans
        (by rw [ih (s₀ :: g) (s₀ :: g) rfl])
    have e2 : (fun s => aa_recU W M₂ b n (s :: g')) = fun _ => aa_recU W M₂ b n (s₀ :: g') :=
      funext fun s => ((ih (s₀ :: g') (s :: g') rfl).symm.trans (ih (s₀ :: g') (s₀ :: g') rfl))
    rw [e1, e2, h₁, h₂, hb g g' hg, ih (s₀ :: g) (s₀ :: g') (by simp [hg])]

omit [Fintype S] in
/-- With `M₁ ≤ M₂`, `M₁` monotone and `W` monotone in `y`, `U¹ ≤ U²` for every plan. -/
theorem aa_recU_le {W : ℝ → ℝ → ℝ} (hW : ∀ c, Monotone (W c)) {M₁ M₂ : List S → (S → ℝ) → ℝ}
    (hM₁ : ∀ h, Monotone (M₁ h)) (hle : ∀ h x, M₁ h x ≤ M₂ h x) (c : List S → ℝ) :
    ∀ n h, aa_recU W M₁ c n h ≤ aa_recU W M₂ c n h
  | 0, _ => le_rfl
  | n + 1, h => by
    simp only [aa_recU]
    exact hW _ ((hM₁ h fun s => aa_recU_le hW hM₁ hle c n (s :: h)).trans (hle h _))

omit [Fintype S] in
/-- **Proposition 20.3.1** (Miao, p. 706), first part. Let `U¹, U²` be recursive utilities with a
common aggregator `W`, strictly increasing in its second argument, and conditional certainty
equivalents `M₁, M₂` (`M(k) = k`), `M₁` monotone. Then `U¹` is more risk averse than `U²` iff
`M₁_t ≤ M₂_t` for all `t`. -/
theorem proposition_20_3_1 [Nonempty S] {W : ℝ → ℝ → ℝ} (hW : ∀ c, StrictMono (W c))
    {M₁ M₂ : List S → (S → ℝ) → ℝ} (h₁ : aa_IsCE M₁) (h₂ : aa_IsCE M₂)
    (hM₁ : ∀ h, Monotone (M₁ h)) :
    aa_MoreRiskAverse W M₁ M₂ ↔ ∀ h x, M₁ h x ≤ M₂ h x := by
  classical
  constructor
  · intro hra h x
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy2, hy1⟩ := exists_between hlt
    -- the plan with consumption `0` at the date of `h` and the continuation `x` after `h`
    let c : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: g' => if g' = h then x s else 0
    let b : List S → ℝ := fun g => if g.length = h.length then 0 else y
    have hb : aa_Deterministic b := fun g g' hg => by simp only [b, hg]
    have hch : c h = 0 := by
      rcases h with _ | ⟨s, g'⟩
      · rfl
      · simp only [c]
        split_ifs with he
        · exact absurd (congrArg List.length he) (by simp)
        · rfl
    have hcc : (fun s => c (s :: h)) = x := funext fun s => by simp [c]
    have hbb : (fun s => b (s :: h)) = fun _ => y := funext fun s => by simp [b]
    have hbh : b h = 0 := by simp [b]
    have hU2 : aa_recU W M₂ c 1 h < aa_recU W M₂ b 1 h := by
      simp only [aa_recU]
      rw [hcc, hbb, h₂, hch, hbh]
      exact hW 0 hy2
    have hU1 := hra 1 h b c hb hU2
    simp only [aa_recU] at hU1
    rw [hcc, hbb, h₁, hch, hbh] at hU1
    exact absurd (hW 0 hy1) (not_lt.2 hU1.le)
  · intro hle n h b c hb hlt
    have hdet := aa_recU_deterministic W h₂ h₁ hb n h h rfl
    calc aa_recU W M₁ c n h ≤ aa_recU W M₂ c n h :=
          aa_recU_le (fun c => (hW c).monotone) hM₁ hle c n h
      _ < aa_recU W M₂ b n h := hlt
      _ = aa_recU W M₁ b n h := hdet

omit [Fintype S] in
/-- Miao, p. 706: risk aversion as printed is never satisfied: taking `c = b` gives
`U²_t(b) = U²_t(b)` but not `U¹_t(b) > U¹_t(b)`. -/
theorem aa_riskAverse_never (W : ℝ → ℝ → ℝ) (M₁ : List S → (S → ℝ) → ℝ)
    {B : Set (List S → (S → ℝ) → ℝ)} (hB : B.Nonempty) : ¬ aa_RiskAverse W M₁ B := by
  intro h
  obtain ⟨M₂, hM₂⟩ := hB
  have := h M₂ hM₂ 0 [] (fun _ => 0) (fun _ => 0) (fun _ _ _ => rfl) rfl
  exact lt_irrefl _ this

/-- Risk aversion with the comparison restricted to random plans `c`. -/
def aa_RiskAverse' (W : ℝ → ℝ → ℝ) (M₁ : List S → (S → ℝ) → ℝ)
    (B : Set (List S → (S → ℝ) → ℝ)) : Prop :=
  ∀ M₂ ∈ B, ∀ n h (b c : List S → ℝ), aa_Deterministic b → ¬ aa_Deterministic c →
    aa_recU W M₂ c n h = aa_recU W M₂ b n h → aa_recU W M₁ c n h < aa_recU W M₁ b n h

/-- The risk-neutral certainty equivalent: the expectation under a fair coin. -/
noncomputable def aa_coinE : List Bool → (Bool → ℝ) → ℝ := fun _ x => aa_E (fun _ => 1 / 2) x

/-- **"More risk averse than a risk-neutral `U²`" does not imply risk aversion** (Miao, p. 706),
even with the comparison restricted to random plans: the risk-neutral utility itself
(`W(c, y) = c + y`, `M = E` under a fair coin) is more risk averse than itself, but it is
indifferent between the deterministic plan `0` and the random plan paying `±1` at date 1. -/
theorem aa_moreRiskAverse_not_riskAverse :
    aa_MoreRiskAverse (fun x y => x + y) aa_coinE aa_coinE ∧
      ¬ aa_RiskAverse' (fun x y => x + y) aa_coinE {aa_coinE} := by
  have hD : SS.IsDistribution (fun _ : Bool => (1 / 2 : ℝ)) := ⟨fun _ => by norm_num, by simp⟩
  have hCE : aa_IsCE aa_coinE := fun _ k => aa_E_const hD k
  refine ⟨(proposition_20_3_1 (fun c => fun y y' hy => by simpa using hy) hCE hCE
    (fun _ _ _ hxy => aa_E_mono hD hxy)).2 fun _ _ => le_rfl, fun h => ?_⟩
  let c : List Bool → ℝ := fun g => match g with
    | [s] => if s then 1 else -1
    | _ => 0
  have hc : ¬ aa_Deterministic c := fun hd => by
    have := hd [true] [false] rfl
    simp [c] at this
    norm_num at this
  have heq : aa_recU (fun x y => x + y) aa_coinE c 1 [] =
      aa_recU (fun x y => x + y) aa_coinE (fun _ => 0) 1 [] := by
    simp [aa_recU, aa_coinE, aa_E, c]
  have := h aa_coinE rfl 1 [] (fun _ => 0) c (fun _ _ _ => rfl) hc heq
  rw [heq] at this
  exact lt_irrefl _ this

/-! ### Expected-utility certainty equivalents: Pratt's theorem -/

/-- The certainty-equivalent comparison `u₁⁻¹E u₁ ≤ u₂⁻¹E u₂` for all lotteries on a finite state
space `T` with outcomes in `D`, written without inverses: if `u₁(m₁) = E u₁(x)` and
`u₂(m₂) = E u₂(x)` with `m₁, m₂ ∈ D` then `m₁ ≤ m₂`. -/
def aa_CELe (T : Type*) [Fintype T] (D : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ (p : T → ℝ), SS.IsDistribution p → ∀ x : T → ℝ, (∀ t, x t ∈ D) → ∀ m₁ ∈ D, ∀ m₂ ∈ D,
    u₁ m₁ = aa_E p (fun t => u₁ (x t)) → u₂ m₂ = aa_E p (fun t => u₂ (x t)) → m₁ ≤ m₂

/-- Pratt, the easy direction: if `u₁ = φ ∘ u₂` on `D` with `φ` strictly increasing and concave on
`u₂(D)`, then `u₁⁻¹E u₁ ≤ u₂⁻¹E u₂` (Jensen). -/
theorem aa_pratt_of_concave (T : Type*) [Fintype T] {D : Set ℝ} {u₁ u₂ : ℝ → ℝ}
    (hu₂ : StrictMonoOn u₂ D) {φ : ℝ → ℝ} (hφc : ConcaveOn ℝ (u₂ '' D) φ)
    (hφm : StrictMonoOn φ (u₂ '' D)) (hφ : ∀ x ∈ D, u₁ x = φ (u₂ x)) : aa_CELe T D u₁ u₂ := by
  intro p hp x hx m₁ hm₁ m₂ hm₂ h1 h2
  have hJ := hφc.le_map_sum (t := Finset.univ) (w := p) (p := fun t => u₂ (x t))
    (fun t _ => hp.nonneg t) hp.sum_eq_one (fun t _ => ⟨x t, hx t, rfl⟩)
  simp only [smul_eq_mul] at hJ
  have e1 : aa_E p (fun t => u₁ (x t)) = ∑ t, p t * φ (u₂ (x t)) := by
    unfold aa_E
    exact Finset.sum_congr rfl fun t _ => by dsimp only; rw [hφ _ (hx t)]
  rw [e1, hφ m₁ hm₁] at h1
  have h3 : φ (u₂ m₁) ≤ φ (u₂ m₂) := by
    rw [h1, h2]
    exact hJ
  exact (hu₂.le_iff_le hm₁ hm₂).1 ((hφm.le_iff_le ⟨_, hm₁, rfl⟩ ⟨_, hm₂, rfl⟩).1 h3)

/-- Pratt, the converse: on an interval `D`, with `u₁, u₂` continuous and strictly increasing, if
`u₁⁻¹E u₁ ≤ u₂⁻¹E u₂` for all two-point lotteries, then `u₁ = φ ∘ u₂` with `φ = u₁ ∘ u₂⁻¹`
strictly increasing and concave on `u₂(D)`. -/
theorem aa_concave_of_pratt {D : Set ℝ} (hD : Convex ℝ D) {u₁ u₂ : ℝ → ℝ}
    (hc₁ : ContinuousOn u₁ D) (hc₂ : ContinuousOn u₂ D) (hu₁ : StrictMonoOn u₁ D)
    (hu₂ : StrictMonoOn u₂ D) (hCE : aa_CELe Bool D u₁ u₂) :
    ∃ φ : ℝ → ℝ, ConcaveOn ℝ (u₂ '' D) φ ∧ StrictMonoOn φ (u₂ '' D) ∧ ∀ x ∈ D, u₁ x = φ (u₂ x) := by
  classical
  set φ : ℝ → ℝ := fun t => u₁ (Function.invFunOn u₂ D t) with hφdef
  have hinj := hu₂.injOn
  have hleft : ∀ x ∈ D, Function.invFunOn u₂ D (u₂ x) = x := fun x hx =>
    hinj.leftInvOn_invFunOn hx
  have hφ : ∀ x ∈ D, u₁ x = φ (u₂ x) := fun x hx => by rw [hφdef]; dsimp only; rw [hleft x hx]
  have hconv : ∀ {u : ℝ → ℝ}, ContinuousOn u D → Convex ℝ (u '' D) := fun hc =>
    ((hD.isPreconnected.image _ hc).ordConnected).convex
  refine ⟨φ, ⟨hconv hc₂, ?_⟩, ?_, hφ⟩
  · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ a b ha hb hab
    obtain ⟨m, hm, hme⟩ := hconv hc₂ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩ ha hb hab
    obtain ⟨m₁, hm₁, hme₁⟩ := hconv hc₁ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩ ha hb hab
    set p : Bool → ℝ := fun t => if t then a else b with hp
    set x : Bool → ℝ := fun t => if t then x₁ else x₂ with hx
    have hpD : SS.IsDistribution p :=
      ⟨fun t => by cases t <;> simp [hp, ha, hb], by simp [hp, hab]⟩
    have hle := hCE p hpD x (fun t => by cases t <;> simp [hx, hx₁, hx₂]) m₁ hm₁ m hm
      (by rw [hme₁]; simp [aa_E, hp, hx, smul_eq_mul])
      (by rw [hme]; simp [aa_E, hp, hx, smul_eq_mul])
    rw [← hme, ← hφ m hm, ← hφ x₁ hx₁, ← hφ x₂ hx₂]
    have := hu₁.monotoneOn hm₁ hm hle
    rw [hme₁] at this
    exact this
  · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hlt
    rw [← hφ x₁ hx₁, ← hφ x₂ hx₂]
    exact hu₁ hx₁ hx₂ ((hu₂.lt_iff_lt hx₁ hx₂).1 hlt)

/-- **Proposition 20.3.1** (Miao, p. 706), second part, for the certainty equivalents `u_i⁻¹E u_i`
on an interval `D` with continuous strictly increasing `u_i`: the comparison `M¹ ≤ M²` holds for all
lotteries iff `u₁ = φ ∘ u₂` with `φ` increasing and concave. -/
theorem proposition_20_3_1_pratt {D : Set ℝ} (hD : Convex ℝ D) {u₁ u₂ : ℝ → ℝ}
    (hc₁ : ContinuousOn u₁ D) (hc₂ : ContinuousOn u₂ D) (hu₁ : StrictMonoOn u₁ D)
    (hu₂ : StrictMonoOn u₂ D) :
    (∀ (T : Type) [Fintype T], aa_CELe T D u₁ u₂) ↔
      ∃ φ : ℝ → ℝ, ConcaveOn ℝ (u₂ '' D) φ ∧ StrictMonoOn φ (u₂ '' D) ∧
        ∀ x ∈ D, u₁ x = φ (u₂ x) :=
  ⟨fun h => aa_concave_of_pratt hD hc₁ hc₂ hu₁ hu₂ (h Bool),
    fun ⟨_, hφc, hφm, hφ⟩ T _ => aa_pratt_of_concave T hu₂ hφc hφm hφ⟩

/-- The expected-utility conditional certainty equivalent `M_h(x) = u⁻¹(E_{p h} u(x))` for an order
isomorphism `u` of `ℝ`. -/
noncomputable def aa_euCE (u : ℝ ≃o ℝ) (p : List S → S → ℝ) : List S → (S → ℝ) → ℝ :=
  fun h x => u.symm (aa_E (p h) fun s => u (x s))

theorem aa_euCE_isCE (u : ℝ ≃o ℝ) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) :
    aa_IsCE (aa_euCE u p) := fun h k => by
  simp [aa_euCE, aa_E_const (hp h)]

theorem aa_euCE_mono (u : ℝ ≃o ℝ) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h))
    (h : List S) : Monotone (aa_euCE u p h) := fun _ _ hxy =>
  u.symm.monotone (aa_E_mono (hp h) fun s => u.monotone (hxy s))

/-- **Proposition 20.3.1** (Miao, p. 706), the Epstein–Zin case: with a common aggregator strictly
increasing in `y` and expected-utility certainty equivalents `u_i⁻¹E_t u_i` (`u_i` order
isomorphisms of `ℝ`), if `u₁ = φ ∘ u₂` with `φ` increasing and concave then `U¹` is more risk averse
than `U²`. -/
theorem proposition_20_3_1_ez [Nonempty S] {W : ℝ → ℝ → ℝ} (hW : ∀ c, StrictMono (W c))
    (u₁ u₂ : ℝ ≃o ℝ) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) {φ : ℝ → ℝ}
    (hφc : ConcaveOn ℝ Set.univ φ) (hφm : StrictMono φ) (hφ : ∀ x, u₁ x = φ (u₂ x)) :
    aa_MoreRiskAverse W (aa_euCE u₁ p) (aa_euCE u₂ p) := by
  rw [proposition_20_3_1 hW (aa_euCE_isCE u₁ hp) (aa_euCE_isCE u₂ hp) (aa_euCE_mono u₁ hp)]
  intro h x
  have himg : (u₂ : ℝ → ℝ) '' Set.univ = Set.univ := Set.image_univ_of_surjective u₂.surjective
  refine aa_pratt_of_concave S (D := Set.univ) (u₂.strictMono.strictMonoOn _)
    (by rw [himg]; exact hφc) (by rw [himg]; exact hφm.strictMonoOn _) (fun x _ => hφ x)
    (p h) (hp h) x (fun _ => trivial) _ trivial _ trivial ?_ ?_
  · simp [aa_euCE]
  · simp [aa_euCE]

end Miao.RecursiveUtility
