/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.Concavity

/-!
# Investment with linear costs

SLP §5.9, pp. 112–113: a firm with technology `f` buys capital at price `q`, sells output at
price `p`, and solves `v(k) = max_{y ≥ 0} {pf(k) − q[y − (1 − δ)k] + βv(y)}`.

**Exercise 5.9a.** Write `G(k) = pf(k) + q(1 − δ)k`, so the return is `G(k) − qy`, and
`h(y) = βG(y) − qy`.

* `invest_fe`: if `y*` maximizes `h` on `[0, ∞)`, then `v(k) = G(k) + h(y*)/(1 − β)` solves the
  functional equation, and `y = y*` attains the maximum at every `k`: the firm jumps to `y*` at
  once, whatever its capital. No differentiability is needed.
* `invest_partialSum_le`, `invest_plan_tendsto`: on the sequence problem, every plan's partial
  sums are at most `v(k₀)`, and the plan `k_t = y*` (`t ≥ 1`) attains `v(k₀)` in the limit; so `v`
  is the supremum function (although `f` is unbounded, the problem telescopes).
* `exists_max_sublinear`: if `f(y)/y → 0`, a maximizer `y*` exists; `invest_euler`: at an interior
  `y*`, `q = β[pf'(y*) + (1 − δ)q]`.
* Investment is reversible: nothing requires `y ≥ (1 − δ)k`, so the firm can sell capital.
* **Bounds on investment** (`(1 − δ)k ≤ y ≤ (1 − δ)k + a`): `clamp_maximizes`: with `v` concave,
  the objective `−qy + βv(y)` does not depend on `k`, so the policy is its unconstrained
  maximizer `ŷ` pushed into `[(1 − δ)k, (1 − δ)k + a]`:
  `g(k) = (1 − δ)k + a` below `(ŷ − a)/(1 − δ)`, `ŷ` in between, and `(1 − δ)k` above
  `ŷ/(1 − δ)` (`bounded_policy`).
* Tools used again later: `intervalΓ_assumption43` (an interval correspondence on `[0, K]`
  satisfies Assumption 4.3) and `fixed_concave_of_concaveF` (with `F` concave on the graph, not
  necessarily strictly, the fixed point is concave).
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {f : ℝ → ℝ} {p q δ β : ℝ}

/-- `G(k) = pf(k) + q(1 − δ)k`. -/
def investG (f : ℝ → ℝ) (p q δ k : ℝ) : ℝ := p * f k + q * (1 - δ) * k

/-- `h(y) = βG(y) − qy`. -/
def investH (f : ℝ → ℝ) (p q δ β y : ℝ) : ℝ := β * investG f p q δ y - q * y

/-- **Exercise 5.9a.** `v(k) = G(k) + h(y*)/(1 − β)` solves the functional equation and `y*`
attains the maximum at every `k`. -/
theorem invest_fe (hβ1 : β < 1) {ystar : ℝ}
    (hmax : ∀ y, 0 ≤ y → investH f p q δ β y ≤ investH f p q δ β ystar) (k : ℝ) :
    (∀ y, 0 ≤ y → investG f p q δ k - q * y +
        β * (investG f p q δ y + investH f p q δ β ystar / (1 - β)) ≤
      investG f p q δ k + investH f p q δ β ystar / (1 - β)) ∧
    investG f p q δ k - q * ystar +
        β * (investG f p q δ ystar + investH f p q δ β ystar / (1 - β)) =
      investG f p q δ k + investH f p q δ β ystar / (1 - β) := by
  have h1β : (1 - β) ≠ 0 := by linarith
  have e : ∀ y, investG f p q δ k - q * y +
      β * (investG f p q δ y + investH f p q δ β ystar / (1 - β)) =
      investG f p q δ k + investH f p q δ β y + β * (investH f p q δ β ystar / (1 - β)) :=
    fun y => by simp only [investH]; ring
  have e2 : investH f p q δ β ystar + β * (investH f p q δ β ystar / (1 - β)) =
      investH f p q δ β ystar / (1 - β) := by field_simp; ring
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [e y]; linarith [hmax y hy]
  · rw [e ystar]; linarith

/-- The telescoping identity: `Σ_{t ≤ N} βᵗ[G(k_t) − qk_{t+1}] =
G(k₀) + Σ_{t < N} βᵗh(k_{t+1}) − βᴺqk_{N+1}`. -/
theorem invest_telescope (k : ℕ → ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * (investG f p q δ (k t) - q * k (t + 1)) =
      investG f p q δ (k 0) + ∑ t ∈ Finset.range N, β ^ t * investH f p q δ β (k (t + 1)) -
        β ^ N * (q * k (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [investH, pow_succ]
    ring

/-- **Exercise 5.9a.** Every plan with `k_t ≥ 0` has partial sums at most `v(k₀)`. -/
theorem invest_partialSum_le (hβ0 : 0 < β) (hβ1 : β < 1) (hq : 0 ≤ q) (hf0 : f 0 = 0)
    {ystar : ℝ} (hmax : ∀ y, 0 ≤ y → investH f p q δ β y ≤ investH f p q δ β ystar)
    {k : ℕ → ℝ} (hk : ∀ t, 0 ≤ k t) (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * (investG f p q δ (k t) - q * k (t + 1)) ≤
      investG f p q δ (k 0) + investH f p q δ β ystar / (1 - β) := by
  rw [invest_telescope]
  set M := investH f p q δ β ystar
  have hM0 : 0 ≤ M := by
    have := hmax 0 le_rfl
    simp only [investH, investG, hf0] at this
    simpa using this
  have hsum : ∑ t ∈ Finset.range N, β ^ t * investH f p q δ β (k (t + 1)) ≤
      ∑ t ∈ Finset.range N, β ^ t * M :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hmax _ (hk _)) (pow_nonneg hβ0.le t)
  have hgeom : ∑ t ∈ Finset.range N, β ^ t * M ≤ M / (1 - β) := by
    have h1 : 0 < 1 - β := by linarith
    have hs : ∑ t ∈ Finset.range N, β ^ t ≤ 1 / (1 - β) := by
      rw [le_div_iff₀ h1, geom_sum_mul_neg]
      linarith [pow_nonneg hβ0.le N]
    rw [← Finset.sum_mul]
    calc (∑ t ∈ Finset.range N, β ^ t) * M ≤ 1 / (1 - β) * M := mul_le_mul_of_nonneg_right hs hM0
      _ = M / (1 - β) := by ring
  have htail : 0 ≤ β ^ N * (q * k (N + 1)) :=
    mul_nonneg (pow_nonneg hβ0.le N) (mul_nonneg hq (hk _))
  linarith

/-- **Exercise 5.9a.** The plan `k₀, y*, y*, …` attains `v(k₀)` in the limit. -/
theorem invest_plan_tendsto (hβ0 : 0 < β) (hβ1 : β < 1) (ystar k₀ : ℝ) :
    Tendsto (fun N => ∑ t ∈ Finset.range (N + 1), β ^ t *
        (investG f p q δ (if t = 0 then k₀ else ystar) - q * ystar)) atTop
      (𝓝 (investG f p q δ k₀ + investH f p q δ β ystar / (1 - β))) := by
  have e : ∀ N, ∑ t ∈ Finset.range (N + 1), β ^ t *
      (investG f p q δ (if t = 0 then k₀ else ystar) - q * ystar) =
      investG f p q δ k₀ + ∑ t ∈ Finset.range N, β ^ t * investH f p q δ β ystar -
        β ^ N * (q * ystar) := fun N => by
    have := invest_telescope (f := f) (p := p) (q := q) (δ := δ) (β := β)
      (fun t => if t = 0 then k₀ else ystar) N
    simpa using this
  simp_rw [e]
  have h1 := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right (investH f p q δ β ystar)
  have h2 := h1.tendsto_sum_nat
  have h3 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (q * ystar)
  have := (h2.const_add (investG f p q δ k₀)).sub h3
  simp only [zero_mul, sub_zero] at this
  convert this using 2
  rw [div_eq_mul_inv, mul_comm]

/-- If `g(y)/y → 0` and `κ > 0`, then `g(y) − κy` attains its maximum on `[0, ∞)`. -/
theorem exists_max_sublinear {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0))
    (hsub : Tendsto (fun y => g y / y) atTop (𝓝 0)) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ystar, 0 ≤ ystar ∧ ∀ y, 0 ≤ y → g y - κ * y ≤ g ystar - κ * ystar := by
  -- beyond some `R ≥ 1`, `g(y) − κy < g(0)`
  have hev : ∀ᶠ y in atTop, g y / y < κ / 2 := hsub.eventually (gt_mem_nhds (by linarith))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hev
  set R := max (max R₀ 1) (2 * |g 0| / κ + 1)
  have hR1 : 1 ≤ R := (le_max_left _ _).trans' (le_max_right _ _)
  have hout : ∀ y, R < y → g y - κ * y < g 0 - κ * 0 := fun y hy => by
    have hy0 : 0 < y := by linarith
    have h1 := hR₀ y ((le_max_left _ _).trans ((le_max_left _ _).trans hy.le))
    rw [div_lt_iff₀ hy0] at h1
    have h2 : 2 * |g 0| / κ + 1 < y := (le_max_right _ _).trans_lt hy
    rw [div_add_one hκ.ne', div_lt_iff₀ hκ] at h2
    nlinarith [le_abs_self (g 0), neg_abs_le (g 0)]
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith : (0:ℝ) ≤ R))
    ((hg.mono Icc_subset_Ici_self).sub (continuousOn_const.mul continuousOn_id))
  refine ⟨y₀, hy₀.1, fun y hy => ?_⟩
  rcases le_or_gt y R with hyR | hyR
  · exact hmax ⟨hy, hyR⟩
  · exact (hout y hyR).le.trans (hmax ⟨le_rfl, by linarith⟩)

/-- **Exercise 5.9a.** At an interior maximizer the Euler equation `q = β[pf'(y*) + (1 − δ)q]`
holds. -/
theorem invest_euler {ystar f' : ℝ} (hpos : 0 < ystar)
    (hmax : ∀ y, 0 ≤ y → investH f p q δ β y ≤ investH f p q δ β ystar)
    (hf : HasDerivAt f f' ystar) : q = β * (p * f' + (1 - δ) * q) := by
  have hd : HasDerivAt (investH f p q δ β) (β * (p * f' + q * (1 - δ) * 1) - q * 1) ystar :=
    (((hf.const_mul p).add ((hasDerivAt_id' ystar).const_mul (q * (1 - δ)))).const_mul β).sub
      ((hasDerivAt_id' ystar).const_mul q)
  have hloc : IsLocalMax (investH f p q δ β) ystar := by
    filter_upwards [Ici_mem_nhds hpos] with y hy
    exact hmax y hy
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-! ### Bounds on investment -/

/-- A concave function is maximized over an interval `[l, u]` of its domain `s` at its maximizer
`ŷ` over `s` pushed into `[l, u]`. -/
theorem clamp_maximizes {s : Set ℝ} {ψ : ℝ → ℝ} (hψ : ConcaveOn ℝ s ψ) {yhat : ℝ}
    (hy0 : yhat ∈ s) (hmax : ∀ y ∈ s, ψ y ≤ ψ yhat) {l u : ℝ} (hlu : l ≤ u)
    (hsub : Icc l u ⊆ s) {y : ℝ} (hy : y ∈ Icc l u) : ψ y ≤ ψ (max l (min yhat u)) := by
  set c := max l (min yhat u)
  -- on either side of `ŷ`, concavity makes `ψ` monotone towards `ŷ`
  have key : ∀ a b, a ∈ s → a ≤ b → b ≤ yhat → ψ a ≤ ψ b := fun a b ha hab hb => by
    rcases eq_or_lt_of_le (hab.trans hb) with he | hlt
    · have : a = b := le_antisymm hab (he ▸ hb); rw [this]
    have hθ0 : 0 ≤ (yhat - b) / (yhat - a) := div_nonneg (by linarith) (by linarith)
    have hθ1 : (yhat - b) / (yhat - a) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have := hψ.2 ha hy0 hθ0 (sub_nonneg.2 hθ1) (by ring)
    simp only [smul_eq_mul] at this
    have e : (yhat - b) / (yhat - a) * a + (1 - (yhat - b) / (yhat - a)) * yhat = b := by
      field_simp; ring
    rw [e] at this
    have := hmax a ha
    nlinarith
  have key' : ∀ a b, a ∈ s → yhat ≤ b → b ≤ a → ψ a ≤ ψ b := fun a b ha hb hba => by
    rcases eq_or_lt_of_le (hb.trans hba) with he | hlt
    · have : a = b := le_antisymm (he ▸ hb) hba; rw [this]
    have hθ0 : 0 ≤ (b - yhat) / (a - yhat) := div_nonneg (by linarith) (by linarith)
    have hθ1 : (b - yhat) / (a - yhat) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have := hψ.2 ha hy0 hθ0 (sub_nonneg.2 hθ1) (by ring)
    simp only [smul_eq_mul] at this
    have e : (b - yhat) / (a - yhat) * a + (1 - (b - yhat) / (a - yhat)) * yhat = b := by
      field_simp; ring
    rw [e] at this
    have := hmax a ha
    nlinarith
  have hys := hsub hy
  rcases le_total yhat l with hyl | hyl
  · -- `ŷ ≤ l`: `c = l`, and `ψ` falls on `[l, u]`
    have hcl : c = l := max_eq_left ((min_le_left _ _).trans hyl)
    rw [hcl]
    exact key' y l hys hyl hy.1
  · rcases le_total yhat u with hyu | hyu
    · have hcy : c = yhat := by simp only [c, min_eq_left hyu, max_eq_right hyl]
      rw [hcy]; exact hmax y hys
    · -- `u ≤ ŷ`: `c = u`, and `ψ` rises on `[l, u]`
      have hcu : c = u := by simp only [c, min_eq_right hyu, max_eq_right hlu]
      rw [hcu]
      exact key y u hys hy.2 hyu

/-- **Exercise 5.9a with bounds on investment.** If `ψ(y) = −qy + βv(y)` is concave with
maximizer `ŷ`, the optimal choice under `(1 − δ)k ≤ y ≤ (1 − δ)k + a` is
`g(k) = max{(1 − δ)k, min{ŷ, (1 − δ)k + a}}`: maximal investment for
`k ≤ (ŷ − a)/(1 − δ)`, the target `ŷ` in between, and no gross investment for `k ≥ ŷ/(1 − δ)`. -/
theorem bounded_policy {v : ℝ → ℝ} (hψ : ConcaveOn ℝ (Ici 0) fun y => -(q * y) + β * v y)
    {yhat : ℝ} (hy0 : 0 ≤ yhat) (hmax : ∀ y, 0 ≤ y → -(q * y) + β * v y ≤ -(q * yhat) + β * v yhat)
    (hδ : δ < 1) {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) :
    (∀ y ∈ Icc ((1 - δ) * k) ((1 - δ) * k + a),
      investG f p q δ k - q * y + β * v y ≤
        investG f p q δ k - q * max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) +
          β * v (max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)))) ∧
    (k ≤ (yhat - a) / (1 - δ) → max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) =
      (1 - δ) * k + a) ∧
    ((yhat - a) / (1 - δ) ≤ k → k ≤ yhat / (1 - δ) →
      max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) = yhat) ∧
    (yhat / (1 - δ) ≤ k → max ((1 - δ) * k) (min yhat ((1 - δ) * k + a)) = (1 - δ) * k) := by
  have h1δ : 0 < 1 - δ := by linarith
  have hl : 0 ≤ (1 - δ) * k := mul_nonneg h1δ.le hk
  refine ⟨fun y hy => ?_, fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · have := clamp_maximizes hψ (mem_Ici.2 hy0) (fun y hy => hmax y hy) (by linarith)
      (fun z hz => mem_Ici.2 (hl.trans hz.1)) hy
    linarith
  · rw [le_div_iff₀ h1δ] at h
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [div_le_iff₀ h1δ] at h1
    rw [le_div_iff₀ h1δ] at h2
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  · rw [div_le_iff₀ h1δ] at h
    rw [max_eq_left ((min_le_left _ _).trans (by linarith))]

/-! ### Tools: interval correspondences and concave fixed points -/

/-- The interval correspondence `Γ(x) = [l(x), u(x)]` on `[0, K]`. -/
def intervalΓ (K : ℝ) (l u : ℝ → ℝ) (x : Icc (0 : ℝ) K) : Set (Icc (0 : ℝ) K) :=
  {y | l x.1 ≤ y.1 ∧ y.1 ≤ u x.1}

/-- An interval correspondence with continuous bounds `0 ≤ l ≤ u ≤ K` satisfies
Assumption 4.3. -/
theorem intervalΓ_assumption43 {K : ℝ} {l u : ℝ → ℝ} (hl : ContinuousOn l (Icc 0 K))
    (hu : ContinuousOn u (Icc 0 K)) (hl0 : ∀ x ∈ Icc 0 K, 0 ≤ l x)
    (hlu : ∀ x ∈ Icc 0 K, l x ≤ u x) (huK : ∀ x ∈ Icc 0 K, u x ≤ K) :
    Assumption43 (intervalΓ K l u) := by
  have hlc : Continuous fun x : Icc (0 : ℝ) K => l x.1 :=
    hl.comp_continuous continuous_subtype_val fun x => x.2
  have huc : Continuous fun x : Icc (0 : ℝ) K => u x.1 :=
    hu.comp_continuous continuous_subtype_val fun x => x.2
  have : CompactSpace (Icc (0 : ℝ) K) := isCompact_iff_compactSpace.1 isCompact_Icc
  set pt : Icc (0 : ℝ) K → Icc (0 : ℝ) K := fun x =>
    ⟨l x.1, hl0 x.1 x.2, (hlu x.1 x.2).trans (huK x.1 x.2)⟩
  have hpt : ∀ x, pt x ∈ intervalΓ K l u x := fun x => ⟨le_rfl, hlu x.1 x.2⟩
  refine ⟨fun x => ⟨pt x, hpt x⟩, fun x => ?_, fun x => ⟨⟨pt x, hpt x⟩, fun y hy xs hxs => ?_⟩,
    fun x => ⟨⟨pt x, hpt x⟩, fun xs hxs ys hys => ?_⟩⟩
  · exact ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).isCompact
  · -- l.h.c.: `yₙ = max{l(xₙ), min{y, u(xₙ)}}`
    refine ⟨0, fun n => ⟨max (l (xs n).1) (min y.1 (u (xs n).1)),
      le_max_of_le_left (hl0 _ (xs n).2),
      max_le ((hlu _ (xs n).2).trans (huK _ (xs n).2)) ((min_le_right _ _).trans
        (huK _ (xs n).2))⟩,
      fun n _ => ⟨le_max_left _ _, max_le (hlu _ (xs n).2) (min_le_right _ _)⟩, ?_⟩
    have hlim := ((hlc.tendsto x).comp hxs).max
      ((tendsto_const_nhds (x := y.1)).min ((huc.tendsto x).comp hxs))
    rw [min_eq_left hy.2, max_eq_right hy.1] at hlim
    exact tendsto_subtype_rng.2 hlim
  · -- u.h.c.: `X` is compact and the graph is closed
    obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
    have hxφ := hxs.comp hφ.tendsto_atTop
    have hyl := (continuous_subtype_val.tendsto y).comp hlim
    refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
    · exact le_of_tendsto_of_tendsto ((hlc.tendsto x).comp hxφ) hyl
        (Eventually.of_forall fun n => (hys (φ n)).1)
    · exact le_of_tendsto_of_tendsto hyl ((huc.tendsto x).comp hxφ)
        (Eventually.of_forall fun n => (hys (φ n)).2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- With `F` concave on the graph (the weak half of Assumption 4.7) and Assumption 4.8, `T`
preserves concavity. -/
theorem bellman_concave_of_concaveF {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ}
    (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (hF : ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hS h0 h1 x x', cmb hS h0 h1 y y'))
    (h48 : Assumption48 hS Γ) {g : S →ᵇ ℝ} (hg : IsConcaveS hS g) :
    IsConcaveS hS (bellman h43 h44 g) := by
  intro x x' θ h0 h1
  obtain ⟨y, hy, hyv, -⟩ := exists_bellman_argmax h43 h44 g x
  obtain ⟨y', hy', hyv', -⟩ := exists_bellman_argmax h43 h44 g x'
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax h43 h44 g (cmb hS h0 h1 x x')
  have hm := hmax _ (h48 x y x' y' hy hy' θ h0 h1)
  have hFc := hF x y x' y' hy hy' θ h0 h1
  have hgc := mul_le_mul_of_nonneg_left (hg y y' θ h0 h1) h44.β_pos.le
  rw [hyv, hyv']
  nlinarith

/-- With `F` concave on the graph and Assumption 4.8, the fixed point is concave. -/
theorem fixed_concave_of_concaveF [Nonempty S] {hS : Convex ℝ S} {Γ : S → Set S}
    {F : S × S → ℝ} (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (hF : ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hS h0 h1 x x', cmb hS h0 h1 y y'))
    (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ} (hv : bellman h43 h44 v = v) : IsConcaveS hS v :=
  (corollary_1 (S' := {g | IsConcaveS hS g}) (S'' := {g | IsConcaveS hS g})
    (bellman_contraction h43 h44) hv ⟨0, fun x x' θ _ _ => by simp⟩ (isClosed_concave hS)
    (fun _ hg => bellman_concave_of_concaveF h43 h44 hF h48 hg)
    (fun _ hg => bellman_concave_of_concaveF h43 h44 hF h48 hg)).1

end StokeyLucasPrescott.DeterministicDynamics
