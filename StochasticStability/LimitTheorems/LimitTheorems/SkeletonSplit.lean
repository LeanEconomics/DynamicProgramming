/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.SplitLimitTheorems
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Splitting an `m`-skeleton with the whole chain attached (MT §17.3.1, (17.21))

Meyn and Tweedie, §17.3.1, pp. 433–434. For `M : Minorization (P ^ m)`, a minorization
`Pᵐ(x, ·) ≥ δ ν` on `C` (which exists for some `m` for every `ψ`-irreducible chain on a countably
generated space, `theorem_5_2_3`), the split `m`-skeleton `(Φ_{nm}, Yₙ)` is put on one probability
space with the whole path `(Φₜ)` of the original chain. The book does this with the conditional
law (17.21): given `Φ_{nm} = x`, the level `Yₙ` and the next block `(Φ_{nm+1}, …, Φ_{(n+1)m})`
are drawn jointly from `δ r(x, y) P(x, dx₁) ⋯ P(x_{m−1}, dy)`, where `r(x, ·)` is the density of
`ν` with respect to `Pᵐ(x, ·)` on `C`.

**The construction.** The state space is `(Fin m → X) × Bool`: a state `Vₙ = (Bₙ, Yₙ)` is the
block `Bₙ = (Φ_{(n−1)m+1}, …, Φ_{nm})` of the original chain ending at time `nm` together with the
level `Yₙ` of the split skeleton at time `nm`; `skelState Vₙ = (Φ_{nm}, Yₙ)`.
* `blockKernel P m`: `K(x, ·)`, the law of `(Φ₁, …, Φₘ)` under `P_x`; `blockKernel_map_last`:
  its last entry has law `Pᵐ(x, ·)`.
* `skelDensity M x y = p(x, y)`, the book's `δ r(x, y)`: the kernel Radon–Nikodym derivative of
  `δν` with respect to `Pᵐ` (jointly measurable because `B(X)` is countably generated), capped at
  `1`; `setLIntegral_skelDensity`: `∫_A p(x, y) Pᵐ(x, dy) = δ ν(A)` on `C`.
* `blockW M`: `W(xᵢ, ·)`, the conditional law of the next block given `Φ_{nm} = x` and `Yₙ = i`;
  `blockW_map_last`: its last entry has law `ν` (bottom level) or `R(x, ·)` (top level), so that
  the skeleton moves by the split kernel of Chapter 5; `blockW_comp_splitK`: averaging over the
  coin at `x` gives back `K(x, ·)`.
* `skelKernel M`: the transition kernel of `(Vₙ)`: draw the next block from `W(skelState v, ·)`,
  then toss the `δ`-coin at its last entry; `skelInit M μ = λ_μ`, the initial law (the virtual
  block `(Φ₀, …, Φ₀)` and `Y₀` from `μ*`).

**Results.**
* `pathMeasure_map_lump`: a lumpable chain (`Q(v, ·) ∘ p⁻¹ = Q₀(p v, ·)`) has `p(Φₙ)` Markov with
  kernel `Q₀`.
* `skel_map_skelState`: under `P_{λ_μ}` the skeleton states `(Φ_{nm}, Yₙ)` form the split chain
  of `Pᵐ` started from `μ*`, so all of Chapters 5, 10 and 17.2 apply to it, with the atom
  `α̌ = C × {1}`.
* `pathMeasure_map_blockify`: the blocks of the original chain form a Markov chain.
* `skel_map_recover` (MT p. 434): the path `(Φₜ)` recovered from the blocks has law `P_μ`: the
  original chain is embedded in the split construction.

**Hypotheses.** `B(X)` is countably generated (for the jointly measurable density, as in
Chapter 5); `m ≥ 1` is passed as `[NeZero m]`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Blocks of the original chain -/

/-- The last entry `b_{m-1}` of a block `b = (b₀, …, b_{m−1})`. -/
def blockLast {m : ℕ} [NeZero m] (b : Fin m → X) : X :=
  b ⟨m - 1, Nat.sub_one_lt (NeZero.ne m)⟩

/-- `blockLast` is measurable. -/
theorem measurable_blockLast {m : ℕ} [NeZero m] : Measurable (blockLast (X := X) (m := m)) :=
  measurable_pi_apply _

omit [MeasurableSpace X] in
/-- The constant block has last entry `x`. -/
theorem blockLast_const {m : ℕ} [NeZero m] (x : X) : blockLast (fun _ : Fin m => x) = x :=
  rfl

/-- The first block `(ω₁, …, ωₘ)` of a path. -/
def blockMap (m : ℕ) (ω : ℕ → X) : Fin m → X := fun k => ω (k.val + 1)

/-- The block map is measurable. -/
theorem measurable_blockMap (m : ℕ) : Measurable (blockMap (X := X) m) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The block kernel `K(x, ·)`: the law of the block `(Φ₁, …, Φₘ)` under `P_x`. -/
noncomputable def blockKernel (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) :
    Kernel X (Fin m → X) :=
  (pathKernel P).map (blockMap m)

/-- `K(x, ·)` is the image of `P_x` under the block map. -/
theorem blockKernel_apply (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) (x : X) :
    blockKernel P m x = (pathKernel P x).map (blockMap m) :=
  Kernel.map_apply _ (measurable_blockMap m) x

/-- The block kernel is a transition kernel. -/
theorem isMarkovKernel_blockKernel (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) :
    IsMarkovKernel (blockKernel P m) := by
  have := isMarkovKernel_pathKernel P
  unfold blockKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_blockMap m)

/-- The block kernel is s-finite. -/
theorem isSFiniteKernel_blockKernel (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) :
    IsSFiniteKernel (blockKernel P m) := by
  have := isMarkovKernel_blockKernel P m
  infer_instance

/-- The last entry of the block has law `Pᵐ(x, ·)`. -/
theorem blockKernel_map_last (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) [NeZero m] (x : X) :
    (blockKernel P m x).map blockLast = (P ^ m) x := by
  rw [blockKernel_apply, Measure.map_map measurable_blockLast (measurable_blockMap m),
    ← pathKernel_map_coord]
  congr 1
  ext ω
  simp only [Function.comp_apply, blockLast, blockMap]
  congr 1
  have := NeZero.ne m
  omega

/-- The blocks of a path: `B₀ = (Φ₀, …, Φ₀)` and `B_{n+1} = (Φ_{nm+1}, …, Φ_{(n+1)m})`. -/
def blockify (m : ℕ) (ω : ℕ → X) : ℕ → Fin m → X
  | 0 => fun _ => ω 0
  | n + 1 => fun k => ω (m * n + k + 1)

/-- The path reassembled from its blocks: `Φ₀` is the last entry of `B₀`, and
`Φ_{nm+k+1}` is the entry `k` of `B_{n+1}`. -/
def unblock {m : ℕ} [NeZero m] (w : ℕ → Fin m → X) (t : ℕ) : X :=
  if t = 0 then blockLast (w 0) else w ((t - 1) / m + 1) ⟨(t - 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩

/-- The block decomposition is measurable. -/
theorem measurable_blockify (m : ℕ) : Measurable (blockify (X := X) m) := by
  refine measurable_pi_iff.2 fun n => ?_
  cases n with
  | zero => exact measurable_pi_iff.2 fun _ => measurable_pi_apply 0
  | succ n => exact measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- Reassembly is measurable. -/
theorem measurable_unblock {m : ℕ} [NeZero m] : Measurable (unblock (X := X) (m := m)) := by
  refine measurable_pi_iff.2 fun t => ?_
  by_cases ht : t = 0
  · simp only [unblock, ht, ↓reduceIte]
    exact measurable_blockLast.comp (measurable_pi_apply 0)
  · simp only [unblock, ht, ↓reduceIte]
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)

omit [MeasurableSpace X] in
/-- Reassembling the blocks of a path gives the path back. -/
theorem unblock_blockify {m : ℕ} [NeZero m] (ω : ℕ → X) : unblock (blockify m ω) = ω := by
  ext t
  by_cases ht : t = 0
  · subst ht; rfl
  · simp only [unblock, ht, ↓reduceIte, blockify]
    congr 1
    have := Nat.div_add_mod (t - 1) m
    omega

omit [MeasurableSpace X] in
/-- The last entry of the block `Bₙ` is `Φ_{nm}`. -/
theorem blockLast_blockify {m : ℕ} [NeZero m] (ω : ℕ → X) (n : ℕ) :
    blockLast (blockify m ω n) = ω (m * n) := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [blockify, blockLast]
    congr 1
    have := NeZero.pos m
    rw [Nat.mul_succ]
    omega

/-- **The blocks of the chain form a Markov chain**: under `P_μ`, `(Bₙ)ₙ` is a Markov chain with
transition kernel `b ↦ K(b_{m−1}, ·)` and initial law the law of `(Φ₀, …, Φ₀)`. -/
theorem pathMeasure_map_blockify (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) [NeZero m]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isMarkovKernel_blockKernel P m
    (pathMeasure P μ).map (blockify m) = pathMeasure ((blockKernel P m).comap blockLast
      measurable_blockLast) (μ.map fun x _ => x) := by
  have := isMarkovKernel_blockKernel P m
  have := isMarkovKernel_pathKernel P
  have hconst : Measurable fun (x : X) (_ : Fin m) => x :=
    measurable_pi_iff.2 fun _ => measurable_id
  have : IsProbabilityMeasure (μ.map fun x (_ : Fin m) => x) :=
    (Measure.isProbabilityMeasure_map_iff hconst.aemeasurable).2 inferInstance
  have hΨ : ∀ n, Measurable[skeletonFilt (X := X) m n] fun ω => blockify m ω n := by
    intro n
    cases n with
    | zero =>
      refine (@measurable_pi_iff (ℕ → X) (Fin m) (fun _ => X) (skeletonFilt m 0) _ _).2
        fun _ => ?_
      exact (measurable_coord_natFilt 0).mono ((natFilt (X := X)).mono (Nat.zero_le _)) le_rfl
    | succ n =>
      refine (@measurable_pi_iff (ℕ → X) (Fin m) (fun _ => X) (skeletonFilt m (n + 1)) _ _).2
        fun k => ?_
      refine (measurable_coord_natFilt (m * n + k + 1)).mono
        ((natFilt (X := X)).mono ?_) le_rfl
      have := k.2
      rw [Nat.mul_succ]
      omega
  have h := isMarkovChain_of_step (𝓖 := skeletonFilt m)
    ((blockKernel P m).comap blockLast measurable_blockLast) (μ.map fun x _ => x)
    (pr := pathMeasure P μ) (Ψ := fun n ω => blockify m ω n) hΨ ?_ ?_
  · exact law_eq_pathMeasure _ _ h
  · have : (fun ω : ℕ → X => blockify m ω 0) = (fun x (_ : Fin m) => x) ∘ fun ω => ω 0 := rfl
    rw [this, ← Measure.map_map hconst (measurable_pi_apply 0), pathMeasure_map_zero]
  · intro n G hG f hf
    have hH : Measurable fun ω : ℕ → X => f (blockMap m ω) := hf.comp (measurable_blockMap m)
    have h1 := markov_lintegral P μ (n := m * n) hG hH
    have h2 : ∀ ω : ℕ → X, blockMap m (shift (m * n) ω) = blockify m ω (n + 1) := fun ω => by
      ext k; simp only [blockMap, shift_apply, blockify]; congr 1
    simp only [h2] at h1
    rw [h1]
    refine setLIntegral_congr_fun ((skeletonFilt m).le n _ hG) fun ω _ => ?_
    rw [Kernel.comap_apply, blockLast_blockify, blockKernel_apply,
      lintegral_map hf (measurable_blockMap m)]

/-- The original path `(Φₜ)ₜ` read off a path of the chain on blocks. -/
def skelRecover {m : ℕ} [NeZero m] (ω : ℕ → (Fin m → X) × Bool) : ℕ → X :=
  unblock fun n => (ω n).1

/-- Recovery is measurable. -/
theorem measurable_skelRecover {m : ℕ} [NeZero m] :
    Measurable (skelRecover (X := X) (m := m)) :=
  measurable_unblock.comp (measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n))

/-! ### Lumpable chains -/

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] in
/-- If `Q(v, ·) ∘ p⁻¹ = Q₀(p v, ·)` for every `v`, the cylinder functions of `Q` on preimages are
those of `Q₀`: `cylFn Q n (p⁻¹ Aᵢ) v = cylFn Q₀ n A (p v)`. -/
theorem cylFn_lump (Q : Kernel S S) (Q₀ : Kernel T T) {p : S → T} (hp : Measurable p)
    (h : ∀ v, (Q v).map p = Q₀ (p v)) (n : ℕ) {A : ℕ → Set T} (hA : ∀ i, MeasurableSet (A i))
    (v : S) : cylFn Q n (fun i => p ⁻¹' A i) v = cylFn Q₀ n A (p v) := by
  induction n generalizing A v with
  | zero =>
    simp only [cylFn]
    by_cases hv : p v ∈ A 0 <;> simp [hv]
  | succ n ih =>
    simp only [cylFn]
    by_cases hv : p v ∈ A 0
    · rw [indicator_of_mem (show v ∈ p ⁻¹' A 0 from hv), indicator_of_mem hv]
      have hih : ∀ z, cylFn Q n (fun i => p ⁻¹' A (i + 1)) z = cylFn Q₀ n (fun i => A (i + 1))
          (p z) := fun z => ih (fun i => hA (i + 1)) z
      simp_rw [hih]
      rw [← lintegral_map (measurable_cylFn Q₀ n fun i => hA (i + 1)) hp, h]
    · rw [indicator_of_notMem (show v ∉ p ⁻¹' A 0 from hv), indicator_of_notMem hv]

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] in
/-- **A lumpable chain.** If `Q(v, ·) ∘ p⁻¹ = Q₀(p v, ·)` for every `v`, then `(p(Φₙ))ₙ` is a
Markov chain with kernel `Q₀`: `P^Q_λ ∘ (p^ℕ)⁻¹ = P^{Q₀}_{λ ∘ p⁻¹}`. -/
theorem pathMeasure_map_lump (Q : Kernel S S) [IsMarkovKernel Q] (Q₀ : Kernel T T)
    [IsMarkovKernel Q₀] {p : S → T} (hp : Measurable p) (h : ∀ v, (Q v).map p = Q₀ (p v))
    (μ : Measure S) [IsProbabilityMeasure μ] :
    (pathMeasure Q μ).map (fun ω n => p (ω n)) = pathMeasure Q₀ (μ.map p) := by
  have := isProbabilityMeasure_pathMeasure Q μ
  have hπ : Measurable fun (ω : ℕ → S) (n : ℕ) => p (ω n) :=
    measurable_pi_iff.2 fun n => hp.comp (measurable_pi_apply n)
  have : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((pathMeasure Q μ).map fun ω n => p (ω n)) :=
    (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
  refine theorem_3_4_1_unique Q₀ (μ.map p) _ fun n A hA => ?_
  rw [Measure.map_apply hπ (measurableSet_boxSet n hA)]
  have hpre : (fun (ω : ℕ → S) (n : ℕ) => p (ω n)) ⁻¹' boxSet n A =
      boxSet n (fun i => p ⁻¹' A i) := by
    ext ω; simp [boxSet]
  rw [hpre, pathMeasure_boxSet _ _ n fun i => hp (hA i),
    lintegral_map (measurable_cylFn Q₀ n hA) hp]
  exact lintegral_congr fun v => cylFn_lump Q Q₀ hp h n hA v

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] in
/-- The lumped chain from a single state: `P^Q_v ∘ (p^ℕ)⁻¹ = P^{Q₀}_{p v}`. -/
theorem pathKernel_map_lump (Q : Kernel S S) [IsMarkovKernel Q] (Q₀ : Kernel T T)
    [IsMarkovKernel Q₀] {p : S → T} (hp : Measurable p) (h : ∀ v, (Q v).map p = Q₀ (p v))
    (v : S) : (pathKernel Q v).map (fun ω n => p (ω n)) = pathKernel Q₀ (p v) := by
  have h1 := pathMeasure_map_lump Q Q₀ hp h (Measure.dirac v)
  rwa [pathMeasure_dirac, Measure.map_dirac' hp, pathMeasure_dirac] at h1

/-! ### The coin and the skeleton states -/

variable {P : Kernel X X} {m : ℕ}

/-- The coin at `y`: the level `Bool` drawn with `P(bottom) = r(y) = δ 1_C(y)`. -/
noncomputable def coinKernel (M : Minorization (P ^ m)) : Kernel X Bool := M.splitK.map Prod.snd

/-- The coin is a probability. -/
theorem isMarkovKernel_coinKernel (M : Minorization (P ^ m)) : IsMarkovKernel (coinKernel M) := by
  have := M.isMarkovKernel_splitK
  exact Kernel.IsMarkovKernel.map _ measurable_snd

/-- `∫ F d(coin y) = (1 − r(y)) F(0) + r(y) F(1)`. -/
theorem lintegral_coinKernel (M : Minorization (P ^ m)) (y : X) (F : Bool → ℝ≥0∞) :
    ∫⁻ i, F i ∂coinKernel M y = (1 - M.splitProb y) * F false + M.splitProb y * F true := by
  rw [coinKernel, Kernel.map_apply _ measurable_snd,
    lintegral_map (measurable_of_countable F) measurable_snd,
    M.lintegral_splitK y (f := fun z => F z.2) ((measurable_of_countable F).comp measurable_snd)]

/-- The state `(Φ_{nm}, Yₙ)` of the split `m`-skeleton read off a state `(b, i)` of the chain on
blocks: the last entry of the block and the level. -/
def skelState {m : ℕ} [NeZero m] (v : (Fin m → X) × Bool) : X × Bool := (blockLast v.1, v.2)

/-- `skelState` is measurable. -/
theorem measurable_skelState [NeZero m] : Measurable (skelState (X := X) (m := m)) :=
  (measurable_blockLast.comp measurable_fst).prodMk measurable_snd

/-- The virtual state `((x, …, x), i)` standing for the skeleton state `xᵢ` (used at time `0`,
where there is no preceding block). -/
def skelVirt {m : ℕ} (z : X × Bool) : (Fin m → X) × Bool := (fun _ => z.1, z.2)

/-- `skelVirt` is measurable. -/
theorem measurable_skelVirt : Measurable (skelVirt (X := X) (m := m)) :=
  (measurable_pi_iff.2 fun _ => measurable_fst).prodMk measurable_snd

omit [MeasurableSpace X] in
/-- `skelState ∘ skelVirt = id`. -/
theorem skelState_skelVirt [NeZero m] (z : X × Bool) :
    skelState (skelVirt (m := m) z) = z := rfl

/-- Toss the coin at the last entry of the block `b`: `b ↦ δ_b ⊗ coin(b_{m−1})`. -/
noncomputable def blockCoin [NeZero m] (M : Minorization (P ^ m)) :
    Kernel (Fin m → X) ((Fin m → X) × Bool) :=
  Kernel.deterministic id measurable_id ×ₖ (coinKernel M).comap blockLast measurable_blockLast

/-- `∫ F d(blockCoin b) = (1 − r(b_{m−1})) F(b, 0) + r(b_{m−1}) F(b, 1)`. -/
theorem lintegral_blockCoin [NeZero m] (M : Minorization (P ^ m)) (b : Fin m → X)
    {F : (Fin m → X) × Bool → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, F v ∂blockCoin M b = (1 - M.splitProb (blockLast b)) * F (b, false) +
      M.splitProb (blockLast b) * F (b, true) := by
  have := isMarkovKernel_coinKernel M
  rw [blockCoin, Kernel.lintegral_deterministic_prod _ _ _ hF, Kernel.comap_apply,
    lintegral_coinKernel]
  rfl

/-- The skeleton state after the coin: `blockCoin ∘ skelState⁻¹ = splitK ∘ last`. -/
theorem blockCoin_map_skelState [NeZero m] (M : Minorization (P ^ m)) :
    (blockCoin M).map skelState = M.splitK.comap blockLast measurable_blockLast := by
  ext b s hs
  rw [Kernel.map_apply' _ measurable_skelState _ hs, Kernel.comap_apply,
    ← lintegral_indicator_one (measurable_skelState hs),
    lintegral_blockCoin M b (measurable_one.indicator (measurable_skelState hs)),
    M.splitK_apply, M.splitMeas_apply _ hs]
  rfl

/-- The initial law `λ_μ` of the chain on blocks: the split skeleton starts from `μ*` (5.3), and
the time-`0` block is the virtual block `(Φ₀, …, Φ₀)`. -/
noncomputable def skelInit [NeZero m] (M : Minorization (P ^ m)) (μ : Measure X) :
    Measure ((Fin m → X) × Bool) :=
  (M.split μ).map skelVirt

/-- `λ_μ` is a probability measure. -/
theorem isProbabilityMeasure_skelInit [NeZero m] (M : Minorization (P ^ m)) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (skelInit M μ) := by
  have := M.isProbabilityMeasure_split μ
  exact (Measure.isProbabilityMeasure_map_iff measurable_skelVirt.aemeasurable).2 inferInstance

/-- The skeleton state of `λ_μ` is `μ*`. -/
theorem skelInit_map_skelState [NeZero m] (M : Minorization (P ^ m)) (μ : Measure X) :
    (skelInit M μ).map skelState = M.split μ := by
  rw [skelInit, Measure.map_map measurable_skelState measurable_skelVirt]
  exact Measure.map_id

/-! ### The densities of the split blocks -/

variable [MeasurableSpace.CountablyGenerated X]

/-- The coin probability `p(x, y) = min(1, d(δν)/dPᵐ(x, ·)(y))`: the conditional probability
that the split skeleton is on the bottom level at `x`, given that the `m`-step chain moves from `x`
to `y` (the book's `δ r(x, y)` in (17.21)). -/
noncomputable def skelDensity (M : Minorization (P ^ m)) (x y : X) : ℝ≥0∞ :=
  min 1 (Kernel.rnDeriv (Kernel.const X (M.δ • M.ν)) (P ^ m) x y)

/-- The coin probability is jointly measurable. -/
theorem measurable_skelDensity (M : Minorization (P ^ m)) :
    Measurable fun p : X × X => skelDensity M p.1 p.2 :=
  measurable_const.min (Kernel.measurable_rnDeriv _ _)

/-- `p ≤ 1`. -/
theorem skelDensity_le_one (M : Minorization (P ^ m)) (x y : X) : skelDensity M x y ≤ 1 :=
  min_le_left _ _

/-- For `x ∈ C`, `∫_A p(x, y) Pᵐ(x, dy) = δ ν(A)`. -/
theorem setLIntegral_skelDensity [IsMarkovKernel P] (M : Minorization (P ^ m)) {x : X}
    (hx : x ∈ M.C) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ y in A, skelDensity M x y ∂(P ^ m) x = M.δ * M.ν A := by
  have := isMarkovKernel_pow P m
  have := M.isFiniteMeasure_smul_ν
  have hle : M.δ • M.ν ≤ (P ^ m) x := M.le x hx
  have hac : Kernel.const X (M.δ • M.ν) x ≪ (P ^ m) x := by
    rw [Kernel.const_apply]; exact Measure.absolutelyContinuous_of_le hle
  have h1 := Kernel.setLIntegral_rnDeriv hac hA
  rw [Kernel.const_apply, Measure.smul_apply, smul_eq_mul] at h1
  rw [← h1]
  refine setLIntegral_congr_fun_ae hA ?_
  have h2 := Kernel.rnDeriv_eq_rnDeriv_measure (κ := Kernel.const X (M.δ • M.ν))
    (η := P ^ m) (a := x)
  have h3 := Measure.rnDeriv_le_one_of_le hle
  filter_upwards [h2, h3] with y hy2 hy3 _
  rw [skelDensity, min_eq_right]
  rw [hy2, Kernel.const_apply]
  exact hy3

/-! ### The block kernel of the split skeleton -/

/-- The density `δ⁻¹ p(x, b_{m−1})` of the block law on the bottom level. -/
noncomputable def topDensity [NeZero m] (M : Minorization (P ^ m)) (x : X) (b : Fin m → X) :
    ℝ≥0∞ :=
  M.δ⁻¹ * skelDensity M x (blockLast b)

/-- The density `(1 − δ)⁻¹ (1 − p(x, b_{m−1}))` of the block law on the top level. -/
noncomputable def botDensity [NeZero m] (M : Minorization (P ^ m)) (x : X) (b : Fin m → X) :
    ℝ≥0∞ :=
  (1 - M.δ)⁻¹ * (1 - skelDensity M x (blockLast b))

/-- The bottom-level density is jointly measurable. -/
theorem measurable_topDensity [NeZero m] (M : Minorization (P ^ m)) :
    Measurable (Function.uncurry (topDensity M)) :=
  measurable_const.mul ((measurable_skelDensity M).comp
    (measurable_fst.prodMk (measurable_blockLast.comp measurable_snd)))

/-- The top-level density is jointly measurable. -/
theorem measurable_botDensity [NeZero m] (M : Minorization (P ^ m)) :
    Measurable (Function.uncurry (botDensity M)) :=
  measurable_const.mul (measurable_const.sub ((measurable_skelDensity M).comp
    (measurable_fst.prodMk (measurable_blockLast.comp measurable_snd))))

/-- The block law on the bottom level at `x ∈ C`: `δ⁻¹ p(x, b_{m−1}) K(x, db)`. -/
noncomputable def blockTopC [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    Kernel X (Fin m → X) :=
  @Kernel.withDensity _ _ _ _ (blockKernel P m) (isSFiniteKernel_blockKernel P m) (topDensity M)

/-- The block law on the top level at `x ∈ C`: `(1 − δ)⁻¹ (1 − p(x, b_{m−1})) K(x, db)`. -/
noncomputable def blockBotC [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    Kernel X (Fin m → X) :=
  @Kernel.withDensity _ _ _ _ (blockKernel P m) (isSFiniteKernel_blockKernel P m) (botDensity M)

/-- `blockTopC` as a measure with density. -/
theorem blockTopC_apply [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) (x : X) :
    blockTopC M x = (blockKernel P m x).withDensity (topDensity M x) :=
  @Kernel.withDensity_apply _ _ _ _ _ (blockKernel P m) (isSFiniteKernel_blockKernel P m)
    (measurable_topDensity M) x

/-- `blockBotC` as a measure with density. -/
theorem blockBotC_apply [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) (x : X) :
    blockBotC M x = (blockKernel P m x).withDensity (botDensity M x) :=
  @Kernel.withDensity_apply _ _ _ _ _ (blockKernel P m) (isSFiniteKernel_blockKernel P m)
    (measurable_botDensity M) x

/-- On `C`, the last entry of a bottom-level block has law `ν`. -/
theorem blockTopC_map_last [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) {x : X}
    (hx : x ∈ M.C) : (blockTopC M x).map blockLast = M.ν := by
  ext A hA
  rw [Measure.map_apply measurable_blockLast hA, blockTopC_apply,
    withDensity_apply _ (measurable_blockLast hA)]
  have hp : Measurable fun y => skelDensity M x y :=
    (measurable_skelDensity M).comp (measurable_const.prodMk measurable_id)
  have h := setLIntegral_map (μ := blockKernel P m x) (f := fun y => M.δ⁻¹ * skelDensity M x y)
    hA (measurable_const.mul hp) measurable_blockLast
  simp only [topDensity]
  rw [← h, blockKernel_map_last, lintegral_const_mul _ hp, setLIntegral_skelDensity M hx hA,
    ← mul_assoc, ENNReal.inv_mul_cancel M.δ_pos.ne' M.δ_ne_top, one_mul]

/-- On `C`, the last entry of a top-level block has law `R(x, ·)`. -/
theorem blockBotC_map_last [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) {x : X}
    (hx : x ∈ M.C) : (blockBotC M x).map blockLast = M.resid x := by
  have := isMarkovKernel_pow P m
  have := isMarkovKernel_blockKernel P m
  ext A hA
  rw [Measure.map_apply measurable_blockLast hA, blockBotC_apply,
    withDensity_apply _ (measurable_blockLast hA)]
  have hp : Measurable fun y => skelDensity M x y :=
    (measurable_skelDensity M).comp (measurable_const.prodMk measurable_id)
  have h := setLIntegral_map (μ := blockKernel P m x)
    (f := fun y => (1 - M.δ)⁻¹ * (1 - skelDensity M x y)) hA
    (measurable_const.mul (measurable_const.sub hp)) measurable_blockLast
  have hp1 : Measurable fun y => 1 - skelDensity M x y := measurable_const.sub hp
  simp only [botDensity]
  rw [← h, blockKernel_map_last, lintegral_const_mul _ hp1,
    Minorization.resid_apply, M.residMeas_apply_of_mem hx hA]
  congr 1
  have := M.isProbabilityMeasure_ν
  rw [lintegral_sub hp, setLIntegral_skelDensity M hx hA, setLIntegral_one]
  · rw [setLIntegral_skelDensity M hx hA]
    exact ENNReal.mul_ne_top M.δ_ne_top (measure_ne_top _ _)
  · exact Eventually.of_forall fun y => skelDensity_le_one M x y

/-- The **block kernel of the split skeleton** `W(xᵢ, db)`: the conditional law of the block
`(Φ_{nm+1}, …, Φ_{(n+1)m})` given `Φ_{nm} = x` and the level `Yₙ = i` of the split `m`-skeleton
(17.21). On `C` it has density `δ⁻¹ p(x, ·)` (bottom level) or `(1 − δ)⁻¹ (1 − p(x, ·))` (top
level) with respect to `K(x, ·)`; off `C` the top level is `K(x, ·)`, and the bottom level
(which is never visited off `C`) is set to `ν` placed in the last entry. -/
noncomputable def blockW [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    Kernel (X × Bool) (Fin m → X) := by
  classical
  exact Kernel.piecewise (s := Prod.snd ⁻¹' {true})
    (measurable_snd (measurableSet_singleton true))
    ((Kernel.piecewise M.measurableSet_C (blockTopC M)
      (Kernel.const X (M.ν.map fun y (_ : Fin m) => y))).comap Prod.fst measurable_fst)
    ((Kernel.piecewise M.measurableSet_C (blockBotC M) (blockKernel P m)).comap Prod.fst
      measurable_fst)

/-- `W(x₁, ·)` for `x ∈ C`. -/
theorem blockW_true_of_mem [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) {x : X}
    (hx : x ∈ M.C) : blockW M (x, true) = blockTopC M x := by
  simp [blockW, Kernel.piecewise_apply, hx]

/-- `W(x₁, ·)` for `x ∉ C`. -/
theorem blockW_true_of_notMem [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) {x : X}
    (hx : x ∉ M.C) : blockW M (x, true) = M.ν.map fun y (_ : Fin m) => y := by
  simp [blockW, Kernel.piecewise_apply, hx]

/-- `W(x₀, ·)` for `x ∈ C`. -/
theorem blockW_false_of_mem [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) {x : X}
    (hx : x ∈ M.C) : blockW M (x, false) = blockBotC M x := by
  simp [blockW, Kernel.piecewise_apply, hx]

/-- `W(x₀, ·) = K(x, ·)` for `x ∉ C`. -/
theorem blockW_false_of_notMem [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) {x : X}
    (hx : x ∉ M.C) : blockW M (x, false) = blockKernel P m x := by
  simp [blockW, Kernel.piecewise_apply, hx]

/-- The last entry of the block has law `Q(xᵢ, ·)`: `W(xᵢ, ·) ∘ last⁻¹ = Q(xᵢ, ·)` (`ν` on the
bottom level, `R(x, ·)` on the top level), the endpoint marginal of (17.21). -/
theorem blockW_map_last [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    (blockW M).map blockLast = M.baseK := by
  ext1 z
  obtain ⟨x, i⟩ := z
  rw [Kernel.map_apply _ measurable_blockLast]
  have := isMarkovKernel_pow P m
  cases i with
  | false =>
    rw [Minorization.baseK_apply_false]
    by_cases hx : x ∈ M.C
    · rw [blockW_false_of_mem M hx, blockBotC_map_last M hx]
    · rw [blockW_false_of_notMem M hx, blockKernel_map_last, Minorization.resid_apply,
        M.residMeas_of_notMem hx]
  | true =>
    rw [Minorization.baseK_apply_true]
    by_cases hx : x ∈ M.C
    · rw [blockW_true_of_mem M hx, blockTopC_map_last M hx]
    · rw [blockW_true_of_notMem M hx, Measure.map_map measurable_blockLast
        (measurable_pi_iff.2 fun _ => measurable_id : Measurable fun (y : X) (_ : Fin m) => y)]
      exact Measure.map_id

/-- The block kernel of the split skeleton is a transition kernel. -/
theorem isMarkovKernel_blockW [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    IsMarkovKernel (blockW M) := by
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_baseK
  refine ⟨fun z => ⟨?_⟩⟩
  have h := congrArg (fun κ : Kernel (X × Bool) X => κ z univ) (blockW_map_last M)
  simp only [Kernel.map_apply' _ measurable_blockLast _ MeasurableSet.univ, preimage_univ,
    measure_univ] at h
  exact h

/-- **The mixture identity** `W ∘ₖ splitK = K`: tossing the coin at `x` and then drawing the
block from `W` is drawing the block from `K(x, ·)`; on `C`, `δ W(x₁, ·) + (1 − δ) W(x₀, ·) =
K(x, ·)`. This is the block form of `Q ∘ₖ splitK = P` (`baseK_comp_splitK`). -/
theorem blockW_comp_splitK [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    blockW M ∘ₖ M.splitK = blockKernel P m := by
  ext x A hA
  rw [Kernel.comp_apply' _ _ _ hA, M.lintegral_splitK x (Kernel.measurable_coe _ hA)]
  by_cases hx : x ∈ M.C
  · rw [blockW_false_of_mem M hx, blockW_true_of_mem M hx, M.splitProb_of_mem hx,
      blockBotC_apply, blockTopC_apply, withDensity_apply _ hA, withDensity_apply _ hA]
    have hp : Measurable fun b : Fin m → X => skelDensity M x (blockLast b) :=
      (measurable_skelDensity M).comp (measurable_const.prodMk measurable_blockLast)
    have hp1 : Measurable fun b : Fin m → X => 1 - skelDensity M x (blockLast b) :=
      measurable_const.sub hp
    simp only [botDensity, topDensity]
    rw [lintegral_const_mul _ hp1, lintegral_const_mul _ hp, ← mul_assoc,
      ← mul_assoc, ENNReal.mul_inv_cancel M.one_sub_δ_ne_zero
        (ENNReal.sub_ne_top ENNReal.one_ne_top),
      ENNReal.mul_inv_cancel M.δ_pos.ne' M.δ_ne_top, one_mul, one_mul,
      ← lintegral_add_left hp1]
    have : ∀ b : Fin m → X, 1 - skelDensity M x (blockLast b) + skelDensity M x (blockLast b) =
        1 := fun b => tsub_add_cancel_of_le (skelDensity_le_one M x _)
    simp_rw [this, setLIntegral_one]
  · rw [blockW_false_of_notMem M hx, M.splitProb_of_notMem hx]
    simp

/-! ### The chain on blocks -/

/-- The one-step kernel `(x, i) ↦ law of the next state (B, Y)`: draw the next block from
`W(xᵢ, ·)` and toss the coin at its last entry. -/
noncomputable def skelJ [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    Kernel (X × Bool) ((Fin m → X) × Bool) :=
  blockCoin M ∘ₖ blockW M

/-- The **split `m`-skeleton with its blocks**: the transition kernel of the chain
`Vₙ = (Bₙ, Yₙ)` on `(Fin m → X) × Bool`, where `Bₙ = (Φ_{(n−1)m+1}, …, Φ_{nm})` is the block of
the original chain ending at time `nm` and `Yₙ` the level of the split skeleton at time `nm`
(17.21). The transition depends on `Vₙ` only through the skeleton state `(Φ_{nm}, Yₙ)`. -/
noncomputable def skelKernel [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    Kernel ((Fin m → X) × Bool) ((Fin m → X) × Bool) :=
  (skelJ M).comap skelState measurable_skelState

/-- `V̌(v, ·) = J(skelState v, ·)`. -/
theorem skelKernel_apply [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (v : (Fin m → X) × Bool) : skelKernel M v = skelJ M (skelState v) := rfl

/-- The one-step kernel is a transition kernel. -/
theorem isMarkovKernel_skelJ [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    IsMarkovKernel (skelJ M) := by
  have := isMarkovKernel_coinKernel M
  have := isMarkovKernel_blockW M
  unfold skelJ blockCoin
  infer_instance

/-- The chain on blocks is a Markov chain. -/
theorem isMarkovKernel_skelKernel [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    IsMarkovKernel (skelKernel M) := by
  have := isMarkovKernel_skelJ M
  unfold skelKernel
  infer_instance

/-- `∫ F dJ(z, ·) = ∫ W(z, db) [(1 − r(b_{m−1})) F(b, 0) + r(b_{m−1}) F(b, 1)]`. -/
theorem lintegral_skelJ [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (z : X × Bool) {F : (Fin m → X) × Bool → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, F v ∂skelJ M z = ∫⁻ b, ((1 - M.splitProb (blockLast b)) * F (b, false) +
      M.splitProb (blockLast b) * F (b, true)) ∂blockW M z := by
  rw [skelJ, Kernel.lintegral_comp _ _ _ hF]
  exact lintegral_congr fun b => lintegral_blockCoin M b hF

/-- **Lumpability**: the skeleton state `(Φ_{(n+1)m}, Y_{n+1})` has, given the past, the law
`P̌(z, ·)` of the split chain of `Pᵐ` from `z = (Φ_{nm}, Yₙ)`:
`J(z, ·) ∘ skelState⁻¹ = P̌(z, ·)`. -/
theorem skelJ_map_skelState [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) :
    (skelJ M).map skelState = M.splitKernel := by
  rw [skelJ, Kernel.map_comp, blockCoin_map_skelState, ← Kernel.comp_map _ _ measurable_blockLast,
    blockW_map_last]
  rfl

/-- `V̌(v, ·) ∘ skelState⁻¹ = P̌(skelState v, ·)`. -/
theorem skelKernel_map_skelState [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (v : (Fin m → X) × Bool) : (skelKernel M v).map skelState = M.splitKernel (skelState v) := by
  rw [skelKernel_apply, ← Kernel.map_apply _ measurable_skelState, skelJ_map_skelState]

/-- **The split skeleton is embedded in the chain on blocks**: under `P_{λ_μ}`, the skeleton
states `(Φ_{nm}, Yₙ)` form the split chain of `Pᵐ` (Chapter 5) started from `μ*`. -/
theorem skel_map_skelState [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isMarkovKernel_skelKernel M
    haveI := isMarkovKernel_pow P m
    haveI := M.isMarkovKernel_splitKernel
    (pathMeasure (skelKernel M) (skelInit M μ)).map (fun ω n => skelState (ω n)) =
      pathMeasure M.splitKernel (M.split μ) := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := isProbabilityMeasure_skelInit M μ
  rw [pathMeasure_map_lump _ _ measurable_skelState (skelKernel_map_skelState M),
    skelInit_map_skelState]

/-! ### The original chain inside the split construction -/

/-- The cylinder functions of the chain on blocks, averaged over the coin at the last entry of the
current block, are those of the chain of blocks of `Φ`. -/
theorem skel_cylFn_fst [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m)) (n : ℕ)
    {A : ℕ → Set (Fin m → X)} (hA : ∀ i, MeasurableSet (A i)) (b : Fin m → X) :
    (1 - M.splitProb (blockLast b)) *
        cylFn (skelKernel M) n (fun i => Prod.fst ⁻¹' A i) (b, false) +
      M.splitProb (blockLast b) * cylFn (skelKernel M) n (fun i => Prod.fst ⁻¹' A i) (b, true) =
    cylFn ((blockKernel P m).comap blockLast measurable_blockLast) n A b := by
  induction n generalizing A b with
  | zero =>
    simp only [cylFn]
    by_cases hb : b ∈ A 0
    · rw [indicator_of_mem (show (b, false) ∈ Prod.fst ⁻¹' A 0 from hb),
        indicator_of_mem (show (b, true) ∈ Prod.fst ⁻¹' A 0 from hb), indicator_of_mem hb]
      simp only [Pi.one_apply, mul_one]
      exact tsub_add_cancel_of_le (M.splitProb_le_one _)
    · rw [indicator_of_notMem (show (b, false) ∉ Prod.fst ⁻¹' A 0 from hb),
        indicator_of_notMem (show (b, true) ∉ Prod.fst ⁻¹' A 0 from hb), indicator_of_notMem hb]
      simp
  | succ n ih =>
    simp only [cylFn]
    have hA' : ∀ i, MeasurableSet (A (i + 1)) := fun i => hA (i + 1)
    by_cases hb : b ∈ A 0
    · rw [indicator_of_mem (show (b, false) ∈ Prod.fst ⁻¹' A 0 from hb),
        indicator_of_mem (show (b, true) ∈ Prod.fst ⁻¹' A 0 from hb), indicator_of_mem hb]
      have key : ∀ i, ∫⁻ z, cylFn (skelKernel M) n (fun j => Prod.fst ⁻¹' A (j + 1)) z
          ∂skelKernel M (b, i) = ∫⁻ b', cylFn ((blockKernel P m).comap blockLast
            measurable_blockLast) n (fun j => A (j + 1)) b' ∂blockW M (blockLast b, i) := by
        intro i
        rw [skelKernel_apply, lintegral_skelJ M _ (measurable_cylFn _ n fun j =>
          measurable_fst (hA (j + 1)))]
        exact lintegral_congr fun b' => ih hA' b'
      rw [key, key, Kernel.comap_apply]
      have hg := measurable_cylFn ((blockKernel P m).comap blockLast measurable_blockLast) n hA'
      set g := cylFn ((blockKernel P m).comap blockLast measurable_blockLast) n
        (fun i => A (i + 1)) with hgdef
      rw [show (blockKernel P m) (blockLast b) = (blockW M ∘ₖ M.splitK) (blockLast b) by
        rw [blockW_comp_splitK], Kernel.lintegral_comp _ _ _ hg,
        M.lintegral_splitK _ hg.lintegral_kernel]
    · rw [indicator_of_notMem (show (b, false) ∉ Prod.fst ⁻¹' A 0 from hb),
        indicator_of_notMem (show (b, true) ∉ Prod.fst ⁻¹' A 0 from hb), indicator_of_notMem hb]
      simp

/-- **The blocks of the chain on blocks**: under `P_{λ_μ}`, the blocks `(Bₙ)ₙ` have the law of the
blocks of the original chain under `P_μ`. -/
theorem skel_map_blocks [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isMarkovKernel_skelKernel M
    haveI := isMarkovKernel_blockKernel P m
    (pathMeasure (skelKernel M) (skelInit M μ)).map (fun ω n => (ω n).1) =
      pathMeasure ((blockKernel P m).comap blockLast measurable_blockLast)
        (μ.map fun x _ => x) := by
  have := isMarkovKernel_skelKernel M
  have := isMarkovKernel_blockKernel P m
  have := isProbabilityMeasure_skelInit M μ
  have := isProbabilityMeasure_pathMeasure (skelKernel M) (skelInit M μ)
  have hconst : Measurable fun (x : X) (_ : Fin m) => x :=
    measurable_pi_iff.2 fun _ => measurable_id
  have : IsProbabilityMeasure (μ.map fun x (_ : Fin m) => x) :=
    (Measure.isProbabilityMeasure_map_iff hconst.aemeasurable).2 inferInstance
  have hπ : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  have : IsProbabilityMeasure ((pathMeasure (skelKernel M) (skelInit M μ)).map
      fun ω n => (ω n).1) := (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
  refine theorem_3_4_1_unique _ _ _ fun n A hA => ?_
  rw [Measure.map_apply hπ (measurableSet_boxSet n hA)]
  have hpre : (fun (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) => (ω n).1) ⁻¹' boxSet n A =
      boxSet n (fun i => Prod.fst ⁻¹' A i) := by
    ext ω; simp [boxSet]
  have hc := measurable_cylFn (skelKernel M) n fun i => measurable_fst (hA i)
  rw [hpre, pathMeasure_boxSet _ _ n fun i => measurable_fst (hA i), skelInit,
    lintegral_map hc measurable_skelVirt,
    M.lintegral_split μ (f := fun z => cylFn (skelKernel M) n (fun i => Prod.fst ⁻¹' A i)
      (skelVirt z)) (hc.comp measurable_skelVirt),
    lintegral_map (measurable_cylFn _ n hA) hconst]
  exact lintegral_congr fun x => skel_cylFn_fst M n hA (fun _ => x)

/-- **The original chain is embedded in the chain on blocks** (MT p. 433–434): the path
`(Φₜ)ₜ` recovered from the chain on blocks started from `λ_μ` has law `P_μ`. Together with
`skel_map_skelState`, the split `m`-skeleton and the original chain live on one probability
space. -/
theorem skel_map_recover [IsMarkovKernel P] [NeZero m] (M : Minorization (P ^ m))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isMarkovKernel_skelKernel M
    (pathMeasure (skelKernel M) (skelInit M μ)).map skelRecover = pathMeasure P μ := by
  have := isMarkovKernel_skelKernel M
  have hπ : Measurable fun (ω : ℕ → (Fin m → X) × Bool) (n : ℕ) => (ω n).1 :=
    measurable_pi_iff.2 fun n => measurable_fst.comp (measurable_pi_apply n)
  have h1 : skelRecover (X := X) (m := m) = unblock ∘ fun ω n => (ω n).1 := rfl
  rw [h1, ← Measure.map_map measurable_unblock hπ, skel_map_blocks,
    ← pathMeasure_map_blockify, Measure.map_map measurable_unblock (measurable_blockify m)]
  have h2 : (unblock ∘ blockify (X := X) m) = id := funext fun ω => unblock_blockify ω
  rw [h2, Measure.map_id]

end MeynTweedie.LimitTheorems
