/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.LogModel

/-!
# Human capital accumulation

SLP §5.7, pp. 109–110: a worker with skill `k` who chooses next period's skill `y` works the
fraction `φ(y/k)` of the period and earns `kφ(y/k)`; `(1 − δ)k ≤ y ≤ (1 + λ)k`, with `φ`
strictly decreasing and concave on `I = [1 − δ, 1 + λ]`, `φ(1 − δ) = 1` and `φ(1 + λ) = 0`. The
operator is `(Tf)(k) = max_{y ∈ Γ(k)} [kφ(y/k) + βf(y)]` and `v₀ = 0`.

* `humanT_linear`: `T(a·k) = M(a)·k`, `M(a) = max_{x ∈ I} [φ(x) + βax]`; so
  **Exercise 5.7a**: `Tⁿv₀ = aₙk` with `aₙ₊₁ = M(aₙ)` (`ex_5_7a_iterate`), `a₁ = 1`
  (`ex_5_7a_one`) and `aₙ₊₁ > aₙ` (`ex_5_7a_strictMono`).
* `ex_5_7a_bounded_iff`: `(aₙ)` is bounded iff `β(1 + λ) ≤ 1`, that is `λ ≤ r`. The manual
  answers `λ < r`; at `λ = r` the sequence is still bounded, by `−φ'(1 + λ)(1 + λ)`, because the
  tangent to the concave `φ` at `1 + λ` lies above `φ` (`slope_bound`).
* **Exercise 5.7b**: with `n` periods left the optimal growth factor `xₙ = y/k` maximizes
  `φ(x) + βaₙ₋₁x`. `growth_factor_mono`: it rises with the number of periods left (a Topkis
  argument), so over the life cycle the growth factor of human capital falls and the share
  `φ(xₙ)` of time spent working rises (`ex_5_7b_profile`). In the last period the worker does
  not invest (`ex_5_7b_last`). Minimal accumulation, once optimal, stays optimal, and maximal
  accumulation, once optimal, was optimal before (`ex_5_7b_corners`). Human capital is
  single-peaked: once it falls it keeps falling (`ex_5_7b_single_peaked`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

variable {φ : ℝ → ℝ} {δ lam β : ℝ}

/-- The hypotheses of SLP §5.7. -/
structure HumanHyp (φ : ℝ → ℝ) (δ lam β : ℝ) : Prop where
  δ_pos : 0 < δ
  δ_lt : δ < 1
  lam_pos : 0 < lam
  β_pos : 0 < β
  β_lt : β < 1
  φ_cont : ContinuousOn φ (Icc (1 - δ) (1 + lam))
  φ_anti : StrictAntiOn φ (Icc (1 - δ) (1 + lam))
  φ_concave : ConcaveOn ℝ (Icc (1 - δ) (1 + lam)) φ
  φ_left : φ (1 - δ) = 1
  φ_right : φ (1 + lam) = 0

/-- `Γ(k) = [(1 − δ)k, (1 + λ)k]` on `(0, ∞)`. -/
def humanΓ (δ lam : ℝ) (k : PosR) : Set PosR := {y | (1 - δ) * k.1 ≤ y.1 ∧ y.1 ≤ (1 + lam) * k.1}

/-- `(Tf)(k) = sup_{y ∈ Γ(k)} [kφ(y/k) + βf(y)]`. -/
noncomputable def humanT (φ : ℝ → ℝ) (δ lam β : ℝ) (f : PosR → ℝ) (k : PosR) : ℝ :=
  sSup ((fun y : PosR => k.1 * φ (y.1 / k.1) + β * f y) '' humanΓ δ lam k)

/-- The per-unit objective `φ(x) + βax`. -/
def humanObj (φ : ℝ → ℝ) (β a x : ℝ) : ℝ := φ x + β * a * x

/-- `M(a) = max_{x ∈ [1 − δ, 1 + λ]} [φ(x) + βax]`. -/
noncomputable def humanM (φ : ℝ → ℝ) (δ lam β a : ℝ) : ℝ :=
  sSup (humanObj φ β a '' Icc (1 - δ) (1 + lam))

/-- `a₀ = 0`, `aₙ₊₁ = M(aₙ)`. -/
noncomputable def humanA (φ : ℝ → ℝ) (δ lam β : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => humanM φ δ lam β (humanA φ δ lam β n)

/-- The maximizers of `φ(x) + βax` on `I`. -/
def humanArgmax (φ : ℝ → ℝ) (δ lam β a : ℝ) : Set ℝ :=
  {x | x ∈ Icc (1 - δ) (1 + lam) ∧
    ∀ x' ∈ Icc (1 - δ) (1 + lam), humanObj φ β a x' ≤ humanObj φ β a x}

theorem HumanHyp.I_nonempty (h : HumanHyp φ δ lam β) : (1 - δ) ≤ (1 + lam) := by
  linarith [h.δ_pos, h.lam_pos]

theorem HumanHyp.obj_cont (h : HumanHyp φ δ lam β) (a : ℝ) :
    ContinuousOn (humanObj φ β a) (Icc (1 - δ) (1 + lam)) :=
  h.φ_cont.add (continuousOn_const.mul continuousOn_id)

theorem HumanHyp.bddAbove (h : HumanHyp φ δ lam β) (a : ℝ) :
    BddAbove (humanObj φ β a '' Icc (1 - δ) (1 + lam)) :=
  (isCompact_Icc.image_of_continuousOn (h.obj_cont a)).bddAbove

/-- `M(a)` is attained. -/
theorem HumanHyp.exists_max (h : HumanHyp φ δ lam β) (a : ℝ) :
    ∃ x ∈ humanArgmax φ δ lam β a, humanM φ δ lam β a = humanObj φ β a x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 h.I_nonempty)
    (h.obj_cont a)
  refine ⟨x, ⟨hx, fun x' hx' => hmax hx'⟩, le_antisymm (csSup_le
    ((Set.nonempty_Icc.2 h.I_nonempty).image _) ?_) (le_csSup (h.bddAbove a) ⟨x, hx, rfl⟩)⟩
  rintro _ ⟨x', hx', rfl⟩
  exact hmax hx'

theorem HumanHyp.le_M (h : HumanHyp φ δ lam β) (a : ℝ) {x : ℝ}
    (hx : x ∈ Icc (1 - δ) (1 + lam)) : humanObj φ β a x ≤ humanM φ δ lam β a :=
  le_csSup (h.bddAbove a) ⟨x, hx, rfl⟩

/-- `T(a·k) = M(a)·k`: substitute `x = y/k`. -/
theorem humanT_linear (h : HumanHyp φ δ lam β) (a : ℝ) (k : PosR) :
    humanT φ δ lam β (fun y => a * y.1) k = humanM φ δ lam β a * k.1 := by
  have hk := k.2
  have hδ : 0 < 1 - δ := by linarith [h.δ_lt]
  have hval : ∀ y ∈ humanΓ δ lam k,
      k.1 * φ (y.1 / k.1) + β * (a * y.1) = k.1 * humanObj φ β a (y.1 / k.1) := fun y _ => by
    simp only [humanObj]; field_simp
  have hmem : ∀ y ∈ humanΓ δ lam k, y.1 / k.1 ∈ Icc (1 - δ) (1 + lam) := fun y hy =>
    ⟨(le_div_iff₀ hk).2 hy.1, (div_le_iff₀ hk).2 hy.2⟩
  have hub : ∀ z ∈ (fun y : PosR => k.1 * φ (y.1 / k.1) + β * (a * y.1)) '' humanΓ δ lam k,
      z ≤ humanM φ δ lam β a * k.1 := by
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    rw [hval y hy, mul_comm _ k.1]
    exact mul_le_mul_of_nonneg_left (h.le_M a (hmem y hy)) hk.le
  obtain ⟨x, hx, hM⟩ := h.exists_max a
  set y : PosR := ⟨k.1 * x, mul_pos hk (by linarith [hx.1.1])⟩
  have hy : y ∈ humanΓ δ lam k :=
    ⟨by simp only [y]; nlinarith [hx.1.1], by simp only [y]; nlinarith [hx.1.2]⟩
  refine le_antisymm (csSup_le ⟨_, y, hy, rfl⟩ hub) ?_
  refine le_trans ?_ (le_csSup ⟨_, hub⟩ ⟨y, hy, rfl⟩)
  simp only
  rw [hval y hy, hM]
  have : y.1 / k.1 = x := by simp only [y]; field_simp
  rw [this, mul_comm]

/-- **Exercise 5.7a.** `Tⁿv₀ = aₙk`. -/
theorem ex_5_7a_iterate (h : HumanHyp φ δ lam β) (n : ℕ) :
    (humanT φ δ lam β)^[n] (fun _ => 0) = fun k => humanA φ δ lam β n * k.1 := by
  induction n with
  | zero => funext k; simp [humanA]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext k
    rw [humanT_linear h]
    rfl

/-- **Exercise 5.7a.** `a₁ = max φ = φ(1 − δ) = 1`. -/
theorem ex_5_7a_one (h : HumanHyp φ δ lam β) : humanA φ δ lam β 1 = 1 := by
  change humanM φ δ lam β 0 = 1
  have hleft : (1 - δ) ∈ Icc (1 - δ) (1 + lam) := ⟨le_rfl, h.I_nonempty⟩
  refine le_antisymm (csSup_le ((Set.nonempty_Icc.2 h.I_nonempty).image _) ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    simp only [humanObj, mul_zero, zero_mul, add_zero]
    rw [← h.φ_left]
    exact h.φ_anti.antitoneOn hleft hx hx.1
  · have := h.le_M 0 hleft
    simpa [humanObj, h.φ_left] using this

/-- `M` is strictly increasing. -/
theorem humanM_strictMono (h : HumanHyp φ δ lam β) : StrictMono (humanM φ δ lam β) := by
  intro a a' haa'
  obtain ⟨x, hx, hM⟩ := h.exists_max a
  have hx0 : 0 < x := by linarith [hx.1.1, h.δ_lt]
  rw [hM]
  refine lt_of_lt_of_le ?_ (h.le_M a' hx.1)
  simp only [humanObj]
  have := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right haa' hx0) h.β_pos
  nlinarith

/-- **Exercise 5.7a.** `aₙ₊₁ > aₙ`. -/
theorem ex_5_7a_strictMono (h : HumanHyp φ δ lam β) : StrictMono (humanA φ δ lam β) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  induction n with
  | zero =>
    have := ex_5_7a_one h
    simp only [humanA] at this ⊢
    change (0 : ℝ) < humanM φ δ lam β 0
    rw [show humanM φ δ lam β 0 = humanA φ δ lam β 1 from rfl, ex_5_7a_one h]
    exact one_pos
  | succ n ih => exact humanM_strictMono h ih

theorem humanA_nonneg (h : HumanHyp φ δ lam β) (n : ℕ) : 0 ≤ humanA φ δ lam β n :=
  (ex_5_7a_strictMono h).monotone (Nat.zero_le n)

/-- `M(a) ≤ 1 + β(1 + λ)a` for `a ≥ 0`. -/
theorem humanM_le (h : HumanHyp φ δ lam β) {a : ℝ} (ha : 0 ≤ a) :
    humanM φ δ lam β a ≤ 1 + β * (1 + lam) * a := by
  obtain ⟨x, hx, hM⟩ := h.exists_max a
  rw [hM]
  have h1 : φ x ≤ 1 := by
    rw [← h.φ_left]; exact h.φ_anti.antitoneOn ⟨le_rfl, h.I_nonempty⟩ hx.1 hx.1.1
  have h2 : β * a * x ≤ β * a * (1 + lam) :=
    mul_le_mul_of_nonneg_left hx.1.2 (mul_nonneg h.β_pos.le ha)
  simp only [humanObj]
  linarith

/-- `M(a) ≥ β(1 + λ)a` (choose `x = 1 + λ`, where `φ = 0`). -/
theorem humanM_ge (h : HumanHyp φ δ lam β) (a : ℝ) : β * (1 + lam) * a ≤ humanM φ δ lam β a := by
  have := h.le_M a ⟨h.I_nonempty, le_rfl⟩
  simp only [humanObj, h.φ_right, zero_add] at this
  linarith

/-- The tangent at `1 + λ` lies above the concave `φ`: with left derivative `d` at `1 + λ`,
`φ(x) ≤ −d(1 + λ − x)` on `I`. -/
theorem slope_bound (h : HumanHyp φ δ lam β) {d : ℝ}
    (hd : HasDerivWithinAt φ d (Iio (1 + lam)) (1 + lam)) {x : ℝ}
    (hx : x ∈ Icc (1 - δ) (1 + lam)) : φ x ≤ -d * (1 + lam - x) := by
  set b := 1 + lam
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · rw [hxb, h.φ_right]; simp
  have hslope : Tendsto (slope φ b) (𝓝[<] b) (𝓝 d) := by
    have := hasDerivWithinAt_iff_tendsto_slope.1 hd
    rwa [sdiff_singleton_eq_self (show b ∉ Iio b from lt_irrefl b)] at this
  -- along `z ∈ (x, b)`: `slope(z, b)·(b − x) ≤ φ(b) − φ(x)`
  have hev : ∀ᶠ z in 𝓝[<] b, slope φ b z * (b - x) ≤ φ b - φ x := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hxb)] with z hz hzx
    have hz' : z < b := hz
    have hzx' : x < z := hzx
    have hzI : z ∈ Icc (1 - δ) (1 + lam) := ⟨hx.1.trans hzx'.le, hz'.le⟩
    have hadj := h.φ_concave.slope_anti_adjacent hx ⟨h.I_nonempty, le_rfl⟩ hzx' hz'
    rw [slope_def_field]
    have e1 : (φ z - φ b) / (z - b) = (φ b - φ z) / (b - z) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [e1]
    have hbz : 0 < b - z := by linarith
    have hzx0 : 0 < z - x := by linarith
    set s2 := (φ b - φ z) / (b - z)
    set s1 := (φ z - φ x) / (z - x)
    have e2 : φ b - φ z = s2 * (b - z) := by simp only [s2]; field_simp
    have e3 : φ z - φ x = s1 * (z - x) := by simp only [s1]; field_simp
    nlinarith
  have hlim := le_of_tendsto (hslope.mul_const (b - x)) hev
  rw [h.φ_right] at hlim
  linarith

/-- **Exercise 5.7a.** `(aₙ)` is bounded iff `β(1 + λ) ≤ 1`, i.e. `λ ≤ r` for `β = 1/(1 + r)`
(the manual's `λ < r` misses the boundary case). `φ` has a left derivative at `1 + λ`, as it does
when `φ` is continuously differentiable on `I`. -/
theorem ex_5_7a_bounded_iff (h : HumanHyp φ δ lam β) {d : ℝ}
    (hd : HasDerivWithinAt φ d (Iio (1 + lam)) (1 + lam)) :
    BddAbove (range (humanA φ δ lam β)) ↔ β * (1 + lam) ≤ 1 := by
  constructor
  · -- if `β(1 + λ) > 1`, then `aₙ₊₁ ≥ β(1 + λ)aₙ` and `a₁ = 1` force `aₙ → ∞`
    intro hb
    by_contra hgt
    push Not at hgt
    have hge : ∀ n, (β * (1 + lam)) ^ n ≤ humanA φ δ lam β (n + 1) := fun n => by
      induction n with
      | zero => simp [ex_5_7a_one h]
      | succ n ih =>
        rw [pow_succ]
        calc (β * (1 + lam)) ^ n * (β * (1 + lam)) ≤ humanA φ δ lam β (n + 1) * (β * (1 + lam)) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
          _ = β * (1 + lam) * humanA φ δ lam β (n + 1) := by ring
          _ ≤ humanA φ δ lam β (n + 2) := humanM_ge h _
    obtain ⟨B, hB⟩ := hb
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop B |>.exists
    exact absurd ((hge n).trans (hB ⟨n + 1, rfl⟩)) (not_le.2 hn)
  · intro hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- `β(1 + λ) = 1`: `a* = −d(1 + λ)` is a fixed point bound
      set s := -d
      have hs : ∀ x ∈ Icc (1 - δ) (1 + lam), φ x ≤ s * (1 + lam - x) := fun x hx =>
        slope_bound h hd hx
      have hs0 : 0 ≤ s := by
        have := hs (1 - δ) ⟨le_rfl, h.I_nonempty⟩
        rw [h.φ_left] at this
        nlinarith [h.δ_pos, h.lam_pos]
      have hM : humanM φ δ lam β (s * (1 + lam)) ≤ s * (1 + lam) := by
        obtain ⟨x, hx, hMx⟩ := h.exists_max (s * (1 + lam))
        rw [hMx]
        have := hs x hx.1
        simp only [humanObj]
        have e : β * (s * (1 + lam)) * x = s * x * (β * (1 + lam)) := by ring
        rw [e, heq]
        linarith
      refine ⟨s * (1 + lam), ?_⟩
      rintro _ ⟨n, rfl⟩
      induction n with
      | zero => exact mul_nonneg hs0 (by linarith [h.lam_pos])
      | succ n ih => exact ((humanM_strictMono h).monotone ih).trans hM
    · -- `β(1 + λ) < 1`: `aₙ ≤ 1/(1 − β(1 + λ))`
      refine ⟨1 / (1 - β * (1 + lam)), ?_⟩
      rintro _ ⟨n, rfl⟩
      have h1 : 0 < 1 - β * (1 + lam) := by linarith
      induction n with
      | zero => exact (div_pos one_pos h1).le
      | succ n ih =>
        have := humanM_le h (humanA_nonneg h n)
        change humanM φ δ lam β (humanA φ δ lam β n) ≤ 1 / (1 - β * (1 + lam))
        rw [le_div_iff₀ h1] at ih ⊢
        have hβl : 0 ≤ β * (1 + lam) := by nlinarith [h.β_pos, h.lam_pos]
        nlinarith [humanA_nonneg h n]

/-! ### Exercise 5.7b: the life-cycle profile -/

/-- **Monotone comparative statics.** A larger continuation slope `a' > a` calls for a weakly
larger growth factor. -/
theorem growth_factor_mono (h : HumanHyp φ δ lam β) {a a' x x' : ℝ} (haa' : a < a')
    (hx : x ∈ humanArgmax φ δ lam β a) (hx' : x' ∈ humanArgmax φ δ lam β a') : x ≤ x' := by
  by_contra hlt
  push Not at hlt
  have h1 := hx.2 x' hx'.1
  have h2 := hx'.2 x hx.1
  simp only [humanObj] at h1 h2
  have : 0 < β * (a' - a) * (x - x') := mul_pos (mul_pos h.β_pos (by linarith)) (by linarith)
  nlinarith

/-- **Exercise 5.7b.** In the last working period (`a₀ = 0`) the worker does not invest:
the only optimal growth factor is `1 − δ`, and he works full time. -/
theorem ex_5_7b_last (h : HumanHyp φ δ lam β) {x : ℝ}
    (hx : x ∈ humanArgmax φ δ lam β (humanA φ δ lam β 0)) : x = 1 - δ := by
  by_contra hne
  have hlt : 1 - δ < x := lt_of_le_of_ne hx.1.1 (Ne.symm hne)
  have h1 := hx.2 (1 - δ) ⟨le_rfl, h.I_nonempty⟩
  have h2 := h.φ_anti ⟨le_rfl, h.I_nonempty⟩ hx.1 hlt
  simp only [humanObj, humanA, mul_zero, zero_mul, add_zero] at h1
  linarith

/-- **Exercise 5.7b.** Let `xₙ` be optimal with `n + 1` periods left. Growth factors fall and
the working share `φ(xₙ)` rises as the worker ages (as `n` falls). -/
theorem ex_5_7b_profile (h : HumanHyp φ δ lam β) {x : ℕ → ℝ}
    (hx : ∀ n, x n ∈ humanArgmax φ δ lam β (humanA φ δ lam β n)) :
    Monotone x ∧ Antitone fun n => φ (x n) := by
  have hmono : Monotone x := monotone_nat_of_le_succ fun n =>
    growth_factor_mono h (ex_5_7a_strictMono h (Nat.lt_succ_self n)) (hx n) (hx (n + 1))
  exact ⟨hmono, fun m n hmn => h.φ_anti.antitoneOn (hx m).1 (hx n).1 (hmono hmn)⟩

/-- **Exercise 5.7b.** If minimal accumulation `1 − δ` is optimal with `n + 1` periods left, it
is optimal with fewer; if maximal accumulation `1 + λ` is optimal with `n + 1` periods left, it
is optimal with more. -/
theorem ex_5_7b_corners (h : HumanHyp φ δ lam β) {x : ℕ → ℝ}
    (hx : ∀ n, x n ∈ humanArgmax φ δ lam β (humanA φ δ lam β n)) {m n : ℕ} (hmn : m ≤ n) :
    (x n = 1 - δ → x m = 1 - δ) ∧ (x m = 1 + lam → x n = 1 + lam) := by
  have hmono := (ex_5_7b_profile h hx).1 hmn
  refine ⟨fun hn => le_antisymm (hn ▸ hmono) (hx m).1.1,
    fun hm => le_antisymm (hx n).1.2 (hm ▸ hmono)⟩

/-- **Exercise 5.7b.** Human capital is single-peaked over the life cycle: with growth factors
`g` falling with age, `k_{t+1} = g_t k_t` and `k > 0`, once human capital falls it keeps
falling. -/
theorem ex_5_7b_single_peaked {g k : ℕ → ℝ} (hg : Antitone g) (hk : ∀ t, k (t + 1) = g t * k t)
    (hpos : ∀ t, 0 < k t) {t : ℕ} (hfall : k (t + 1) ≤ k t) {s : ℕ} (hts : t ≤ s) :
    k (s + 1) ≤ k s := by
  have hgt : g t ≤ 1 := by
    rw [hk t] at hfall
    by_contra hlt
    push Not at hlt
    nlinarith [hpos t]
  have hgs := (hg hts).trans hgt
  rw [hk s]
  nlinarith [hpos s]

end StokeyLucasPrescott.DeterministicApplications
