/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Fixed points of monotone operators: Lemma 17.6, Theorem 17.7 and its Corollary

SLP §17.5, pp. 525–529. `C(X)` is the space of bounded continuous functions on `X` with the sup
norm, Mathlib's `X →ᵇ ℝ`, ordered pointwise. In the book `X ⊆ ℝˡ` is bounded; the only property
of `X` the proofs use is that it is totally bounded, so the results are stated for a pseudometric
space `X` with `TotallyBounded (univ : Set X)`. `totallyBounded_univ_of_isBounded` supplies this
for a bounded subset of `ℝˡ` (or of any proper space), seen as a subtype.

The book's equicontinuity of a family (p. 520: one `δ` for all `x, x'` and all members) is
Mathlib's `UniformEquicontinuous`; "`T(F)` is equicontinuous" is
`UniformEquicontinuous fun f : F => ⇑(T f)`. The operator is a map `T : C(X) → C(X)` with
`MapsTo T F F` and `ContinuousOn T F`; its values off `F` play no role.

* `isMonotoneOperator` (definition, p. 528) and `isMonotoneOperator_iff_monotoneOn`.
* `cauchySeq_of_uniformEquicontinuous`: on a totally bounded space a uniformly equicontinuous,
  pointwise Cauchy sequence in `C(X)` is Cauchy in the sup norm (the core of the proof of
  Lemma 17.6).
* **Lemma 17.6** (`lemma_17_6`, p. 526): `F` closed, `T : F → F` continuous, `T(F)`
  equicontinuous; if `Tⁿf₀` converges pointwise, it converges in the sup norm to a fixed point
  of `T` in `F`.
* **Theorem 17.7** (`theorem_17_7`, p. 528), with the two one-sided versions
  `theorem_17_7_of_le` (`f₀ ≤ Tf₀`, increasing iterates) and `theorem_17_7_of_ge`
  (`Tf₀ ≤ f₀`, decreasing iterates): `F` closed and bounded, `T` continuous and monotone on `F`,
  `T(F)` equicontinuous. Then `Tⁿf₀` converges in `C(X)` to a fixed point in `F`.
* **Corollary** (p. 529): `corollary_17_7_least` (iterating from a least element of `F` gives
  the least fixed point), `corollary_17_7_greatest` (from a greatest element, the greatest),
  `corollary_17_7` (every fixed point `h ∈ F` satisfies `f ≤ h ≤ g`) and
  `corollary_17_7_unique` (if the two limits coincide, it is the only fixed point in `F`).
* `theorem_17_7_of_isBounded`: Theorem 17.7 for a bounded `X ⊆ E`, `E` proper (e.g. `ℝˡ`).

**Remark (p. 528).** Theorem 17.7 is not Tarski's theorem: `F` need not be a complete lattice.
It is a monotone-iteration theorem: monotone bounded real sequences converge, and Lemma 17.6
turns pointwise convergence into convergence in `C(X)`. No convexity is used.

**Correction (proof of Lemma 17.6, (4), (8b), (9), p. 527; trivial).** Letting `Δ → 0` in
`|f(x') − f(x)| < ε + Δ` gives `≤ ε`, not `< ε`, so (9) is `≤ 3ε`. The proof here organises the
book's argument as a Cauchy estimate: `|fₙ(x) − fₘ(x)| ≤ |fₙ(x) − fₙ(xᵢ)| + |fₙ(xᵢ) − fₘ(xᵢ)| +
|fₘ(xᵢ) − fₘ(x)|` for a point `xᵢ` of a finite `δ`-net, which avoids step 1 (uniform continuity of
the limit) altogether; the limit exists because `C(X)` is complete.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set BoundedContinuousFunction

variable {X : Type*} [PseudoMetricSpace X]

/-- The order on `C(X)` is pointwise: `f ≤ g` iff `f x ≤ g x` for all `x` (p. 528). -/
theorem bcf_le_iff {f g : X →ᵇ ℝ} : f ≤ g ↔ ∀ x, f x ≤ g x := Iff.rfl

/-- SLP p. 528: `T : F → F` is a *monotone operator* if `f, g ∈ F` and `f ≥ g` imply `Tf ≥ Tg`,
where `f ≥ g` means `f(x) ≥ g(x)` for all `x`. -/
def isMonotoneOperator (F : Set (X →ᵇ ℝ)) (T : (X →ᵇ ℝ) → (X →ᵇ ℝ)) : Prop :=
  ∀ f ∈ F, ∀ g ∈ F, (∀ x, g x ≤ f x) → ∀ x, (T g) x ≤ (T f) x

/-- The book's monotone operators are Mathlib's `MonotoneOn T F` for the pointwise order. -/
theorem isMonotoneOperator_iff_monotoneOn {F : Set (X →ᵇ ℝ)} {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)} :
    isMonotoneOperator F T ↔ MonotoneOn T F :=
  ⟨fun h _ hg _ hf hgf => h _ hf _ hg hgf, fun h _ hf _ hg hgf => h hg hf hgf⟩

/-- On a totally bounded space, a uniformly equicontinuous sequence in `C(X)` that is Cauchy at
every point is Cauchy in the sup norm. This is the heart of the proof of Lemma 17.6, steps 1–2:
a finite `δ`-net reduces uniform estimates to finitely many points. -/
theorem cauchySeq_of_uniformEquicontinuous (hX : TotallyBounded (univ : Set X))
    {u : ℕ → X →ᵇ ℝ} (hequi : UniformEquicontinuous fun n => ⇑(u n))
    (hpt : ∀ x, CauchySeq fun n => u n x) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformEquicontinuous_iff.1 hequi (ε / 4) (by positivity)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hX δ hδ
  have hN : ∀ y ∈ t, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m y) (u n y) < ε / 4 :=
    fun y _ => Metric.cauchySeq_iff.1 (hpt y) _ (by positivity)
  choose! N hN using hN
  refine ⟨ht.toFinset.sup N, fun m hm n hn => ?_⟩
  have key : dist (u m) (u n) ≤ 3 * (ε / 4) := by
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ Metric.ball y δ := by
      simpa using hcover (mem_univ x)
    have hNy : N y ≤ ht.toFinset.sup N := Finset.le_sup (ht.mem_toFinset.2 hy)
    have hxy' : dist x y < δ := hxy
    have h1 := hu x y hxy' m
    have h2 := hN y hy m (le_trans hNy hm) n (le_trans hNy hn)
    have h3 := hu x y hxy' n
    calc dist (u m x) (u n x)
        ≤ dist (u m x) (u m y) + dist (u m y) (u n y) + dist (u n y) (u n x) :=
          dist_triangle4 _ _ _ _
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by
          rw [dist_comm (u n y)]
          gcongr
      _ = 3 * (ε / 4) := by ring
  linarith

/-- **Lemma 17.6** (SLP p. 526). Let `X` be totally bounded (e.g. a bounded subset of `ℝˡ`),
`F ⊆ C(X)` closed, `T : F → F` continuous with `T(F)` an equicontinuous family. If for some
`f₀ ∈ F` the sequence `Tⁿf₀` converges pointwise, then it converges in the sup norm to some
`f ∈ F`, and `f` is a fixed point of `T`. (No boundedness or convexity of `F` is needed.) -/
theorem lemma_17_6 (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)} (hF : IsClosed F)
    {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)} (hT : MapsTo T F F) (hTc : ContinuousOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (hpt : ∀ x, ∃ c, Tendsto (fun n => (T^[n] f₀) x) atTop (𝓝 c)) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := by
  have hmem : ∀ n, T^[n] f₀ ∈ F := fun n => hT.iterate n hf₀
  set u : ℕ → X →ᵇ ℝ := fun n => T^[n + 1] f₀ with hu_def
  have hu : ∀ n, u n = T (T^[n] f₀) := fun n => Function.iterate_succ_apply' T n f₀
  have hequi' : UniformEquicontinuous fun n => ⇑(u n) := by
    have := hequi.comp fun n => (⟨T^[n] f₀, hmem n⟩ : F)
    convert this using 2 with n
    simp [hu n]
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_uniformEquicontinuous hX hequi' fun x => ?_
    obtain ⟨c, hc⟩ := hpt x
    exact ((tendsto_add_atTop_iff_nat 1).2 hc).cauchySeq
  obtain ⟨f, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim' : Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := (tendsto_add_atTop_iff_nat 1).1 hlim
  have hfF : f ∈ F := hF.mem_of_tendsto hlim' (Eventually.of_forall hmem)
  have hT' : Tendsto (fun n => T (T^[n] f₀)) atTop (𝓝 (T f)) :=
    (hTc f hfF).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim', Eventually.of_forall hmem⟩)
  refine ⟨f, hfF, ?_, hlim'⟩
  have hlim2 : Tendsto (fun n => T (T^[n] f₀)) atTop (𝓝 f) := by
    have e : u = fun n => T (T^[n] f₀) := funext hu
    rwa [e] at hlim
  exact tendsto_nhds_unique hT' hlim2

/-- Monotone iteration: if `T` is monotone on `F`, `T` maps `F` to itself, `f₀ ∈ F` and
`f₀ ≤ Tf₀`, then `n ↦ Tⁿf₀` is increasing (proof of Theorem 17.7, p. 528). -/
theorem monotone_iterate_of_le {F : Set (X →ᵇ ℝ)} {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hmono : MonotoneOn T F) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀) : Monotone fun n => T^[n] f₀ := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => simpa using h
  | succ n ih =>
    calc T^[n + 1] f₀ = T (T^[n] f₀) := Function.iterate_succ_apply' T n f₀
      _ ≤ T (T^[n + 1] f₀) := hmono (hT.iterate n hf₀) (hT.iterate (n + 1) hf₀) ih
      _ = T^[n + 1 + 1] f₀ := (Function.iterate_succ_apply' T (n + 1) f₀).symm

/-- Monotone iteration downwards: if `Tf₀ ≤ f₀` then `n ↦ Tⁿf₀` is decreasing. -/
theorem antitone_iterate_of_ge {F : Set (X →ᵇ ℝ)} {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hmono : MonotoneOn T F) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : T f₀ ≤ f₀) : Antitone fun n => T^[n] f₀ := by
  refine antitone_nat_of_succ_le fun n => ?_
  induction n with
  | zero => simpa using h
  | succ n ih =>
    calc T^[n + 1 + 1] f₀ = T (T^[n + 1] f₀) := Function.iterate_succ_apply' T (n + 1) f₀
      _ ≤ T (T^[n] f₀) := hmono (hT.iterate (n + 1) hf₀) (hT.iterate n hf₀) ih
      _ = T^[n + 1] f₀ := (Function.iterate_succ_apply' T n f₀).symm

/-- A bounded set of `C(X)` is uniformly bounded pointwise. -/
theorem exists_abs_le_of_isBounded {F : Set (X →ᵇ ℝ)} (hFb : Bornology.IsBounded F) :
    ∃ C, ∀ f ∈ F, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hFb.exists_norm_le
  exact ⟨C, fun f hf x => (Real.norm_eq_abs _ ▸ f.norm_coe_le_norm x).trans (hC f hf)⟩

/-- **Theorem 17.7**, increasing case (SLP p. 528): `f₀ ≤ Tf₀`. The iterates `Tⁿf₀` increase
and converge in `C(X)` to a fixed point `f ∈ F` of `T`. -/
theorem theorem_17_7_of_le (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := by
  refine lemma_17_6 hX hF hT hTc hequi hf₀ fun x => ?_
  obtain ⟨C, hC⟩ := exists_abs_le_of_isBounded hFb
  have hm : Monotone fun n => (T^[n] f₀) x :=
    fun m n hmn => monotone_iterate_of_le hT hmono hf₀ h hmn x
  exact ⟨_, tendsto_atTop_ciSup hm ⟨C, by
    rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (hC _ (hT.iterate n hf₀) x)⟩⟩

/-- **Theorem 17.7**, decreasing case (SLP p. 528): `Tf₀ ≤ f₀`. -/
theorem theorem_17_7_of_ge (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : T f₀ ≤ f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) := by
  refine lemma_17_6 hX hF hT hTc hequi hf₀ fun x => ?_
  obtain ⟨C, hC⟩ := exists_abs_le_of_isBounded hFb
  have hm : Antitone fun n => (T^[n] f₀) x :=
    fun m n hmn => antitone_iterate_of_ge hT hmono hf₀ h hmn x
  exact ⟨_, tendsto_atTop_ciInf hm ⟨-C, by
    rintro _ ⟨n, rfl⟩
    exact neg_le_of_abs_le (hC _ (hT.iterate n hf₀) x)⟩⟩

/-- **Theorem 17.7** (SLP p. 528). Let `X` be totally bounded (e.g. a bounded subset of `ℝˡ`),
`F ⊆ C(X)` closed and bounded, `T : F → F` continuous and monotone, with `T(F)` an equicontinuous
family. If `f₀ ∈ F` satisfies `f₀ ≤ Tf₀` or `f₀ ≥ Tf₀`, then `f = lim Tⁿf₀` exists (in the sup
norm), `f ∈ F`, and `Tf = f`. -/
theorem theorem_17_7 (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀ ∨ T f₀ ≤ f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) :=
  h.elim (theorem_17_7_of_le hX hF hFb hT hTc hmono hequi hf₀)
    (theorem_17_7_of_ge hX hF hFb hT hTc hmono hequi hf₀)

/-- A limit in `C(X)` of functions lying below `h` lies below `h`. -/
theorem le_of_tendsto_bcf {u : ℕ → X →ᵇ ℝ} {f h : X →ᵇ ℝ} (hlim : Tendsto u atTop (𝓝 f))
    (hle : ∀ n, u n ≤ h) : f ≤ h := fun x =>
  le_of_tendsto' (((continuous_eval_const x).tendsto f).comp hlim) fun n => hle n x

/-- A limit in `C(X)` of functions lying above `h` lies above `h`. -/
theorem ge_of_tendsto_bcf {u : ℕ → X →ᵇ ℝ} {f h : X →ᵇ ℝ} (hlim : Tendsto u atTop (𝓝 f))
    (hle : ∀ n, h ≤ u n) : h ≤ f := fun x =>
  ge_of_tendsto' (((continuous_eval_const x).tendsto f).comp hlim) fun n => hle n x

/-- **Corollary to Theorem 17.7**, least element (SLP p. 529). Under the hypotheses of
Theorem 17.7, if `f₀` is a least element of `F` then `f = lim Tⁿf₀` exists, is a fixed point in
`F`, and `f ≤ h` for every fixed point `h ∈ F` of `T`: `f` is the least fixed point in `F`. -/
theorem corollary_17_7_least (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : X →ᵇ ℝ} (hf₀ : IsLeast F f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) ∧
      ∀ h ∈ F, T h = h → f ≤ h := by
  obtain ⟨f, hfF, hfix, hlim⟩ := theorem_17_7_of_le hX hF hFb hT hTc hmono hequi hf₀.1
    (hf₀.2 (hT hf₀.1))
  refine ⟨f, hfF, hfix, hlim, fun h hh hTh => le_of_tendsto_bcf hlim fun n => ?_⟩
  induction n with
  | zero => exact hf₀.2 hh
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hTh]
    exact hmono (hT.iterate n hf₀.1) hh ih

/-- **Corollary to Theorem 17.7**, greatest element (SLP p. 529): iterating from a greatest
element `g₀` of `F` converges to the greatest fixed point of `T` in `F`. -/
theorem corollary_17_7_greatest (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {g₀ : X →ᵇ ℝ}
    (hg₀ : IsGreatest F g₀) :
    ∃ g ∈ F, T g = g ∧ Tendsto (fun n => T^[n] g₀) atTop (𝓝 g) ∧
      ∀ h ∈ F, T h = h → h ≤ g := by
  obtain ⟨g, hgF, hfix, hlim⟩ := theorem_17_7_of_ge hX hF hFb hT hTc hmono hequi hg₀.1
    (hg₀.2 (hT hg₀.1))
  refine ⟨g, hgF, hfix, hlim, fun h hh hTh => ge_of_tendsto_bcf hlim fun n => ?_⟩
  induction n with
  | zero => exact hg₀.2 hh
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hTh]
    exact hmono hh (hT.iterate n hg₀.1) ih

/-- **Corollary to Theorem 17.7** (SLP p. 529). With `f₀` least and `g₀` greatest in `F`, the
limits `f = lim Tⁿf₀` and `g = lim Tⁿg₀` exist, are fixed points in `F`, and every fixed point
`h ∈ F` of `T` satisfies `f ≤ h ≤ g`. -/
theorem corollary_17_7 (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ g₀ : X →ᵇ ℝ}
    (hf₀ : IsLeast F f₀) (hg₀ : IsGreatest F g₀) :
    ∃ f ∈ F, ∃ g ∈ F, T f = f ∧ T g = g ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) ∧
      Tendsto (fun n => T^[n] g₀) atTop (𝓝 g) ∧ ∀ h ∈ F, T h = h → f ≤ h ∧ h ≤ g := by
  obtain ⟨f, hfF, hf, hfl, hfh⟩ := corollary_17_7_least hX hF hFb hT hTc hmono hequi hf₀
  obtain ⟨g, hgF, hg, hgl, hgh⟩ := corollary_17_7_greatest hX hF hFb hT hTc hmono hequi hg₀
  exact ⟨f, hfF, g, hgF, hf, hg, hfl, hgl, fun h hh hTh => ⟨hfh h hh hTh, hgh h hh hTh⟩⟩

/-- **Corollary to Theorem 17.7**, uniqueness test (SLP p. 529). If the iterates from the least
and from the greatest element of `F` have the same limit `f`, then `f` is the unique fixed point
of `T` in `F`. -/
theorem corollary_17_7_unique (hX : TotallyBounded (univ : Set X)) {F : Set (X →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (X →ᵇ ℝ) → (X →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ g₀ f : X →ᵇ ℝ}
    (hf₀ : IsLeast F f₀) (hg₀ : IsGreatest F g₀)
    (hfl : Tendsto (fun n => T^[n] f₀) atTop (𝓝 f))
    (hgl : Tendsto (fun n => T^[n] g₀) atTop (𝓝 f)) :
    f ∈ F ∧ T f = f ∧ ∀ h ∈ F, T h = h → h = f := by
  obtain ⟨f', hf'F, g', hg'F, hf', hg', hf'l, hg'l, hbetween⟩ :=
    corollary_17_7 hX hF hFb hT hTc hmono hequi hf₀ hg₀
  have e1 : f' = f := tendsto_nhds_unique hf'l hfl
  have e2 : g' = f := tendsto_nhds_unique hg'l hgl
  subst e1
  subst e2
  exact ⟨hf'F, hf', fun h hh hTh => le_antisymm (hbetween h hh hTh).2 (hbetween h hh hTh).1⟩

/-- A bounded subset of a proper space (e.g. a bounded `X ⊆ ℝˡ`), seen as a subtype, is totally
bounded. This is what the book's hypothesis "`X ⊆ ℝˡ` bounded" provides. -/
theorem totallyBounded_univ_of_isBounded {E : Type*} [PseudoMetricSpace E] [ProperSpace E]
    {S : Set E} (hS : Bornology.IsBounded S) : TotallyBounded (univ : Set S) := by
  have h : TotallyBounded S := hS.isCompact_closure.totallyBounded.subset subset_closure
  simpa using totallyBounded_preimage (isUniformInducing_val S) h

/-- **Theorem 17.7** with the book's hypothesis on the state space: `X` a bounded subset of a
proper space (e.g. `ℝˡ`), and `C(X) = X →ᵇ ℝ` on the subtype. -/
theorem theorem_17_7_of_isBounded {E : Type*} [PseudoMetricSpace E] [ProperSpace E] {S : Set E}
    (hS : Bornology.IsBounded S) {F : Set (S →ᵇ ℝ)}
    (hF : IsClosed F) (hFb : Bornology.IsBounded F) {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)}
    (hT : MapsTo T F F) (hTc : ContinuousOn T F) (hmono : MonotoneOn T F)
    (hequi : UniformEquicontinuous fun f : F => ⇑(T f)) {f₀ : S →ᵇ ℝ} (hf₀ : f₀ ∈ F)
    (h : f₀ ≤ T f₀ ∨ T f₀ ≤ f₀) :
    ∃ f ∈ F, T f = f ∧ Tendsto (fun n => T^[n] f₀) atTop (𝓝 f) :=
  theorem_17_7 (totallyBounded_univ_of_isBounded hS) hF hFb hT hTc hmono hequi hf₀ h

end StokeyLucasPrescott.EquilibriaWithDistortions
