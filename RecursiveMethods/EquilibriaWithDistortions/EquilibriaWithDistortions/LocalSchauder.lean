/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.LocalContraction
import EquilibriaWithDistortions.SchauderBoundedContinuous

/-!
# The Schauder route to the local equilibrium

SLP §18.2, p. 551. The book lists three routes to a fixed point of `(Th)(k) = H[k, h²(k)]` on
`D_λ(I_ε)`; the first is Schauder's theorem (Theorem 17.4): `I_ε` is bounded, `D_λ(I_ε)` is a
nonempty, closed, bounded and convex subset of `C(I_ε)` whose members are uniformly
`λ`-Lipschitz, hence equicontinuous; Proposition 18.2 gives `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`, and
Exercise 18.3 that `T` is continuous. This module carries the argument out.

* `convex_DC`: `D_λ(I_ε)` (`DC`, as a subset of `C(I_ε)`) is convex.
* `isBounded_DC`, `totallyBounded_DC`: it is bounded, and totally bounded, by the
  Arzelà–Ascoli lemma `totallyBounded_of_equicontinuous` (a uniformly `λ`-Lipschitz family is
  equicontinuous in the sense of p. 520), transported from `I_ε →ᵇ ℝ` to `C(I_ε)` by the
  isometry `ContinuousMap.isometryEquivBoundedOfCompact`.
* `continuousOn_TC`: `T` is continuous on `D_λ(I_ε)` (Exercise 18.3, from `TC_dist_le` with
  the global Lipschitz constants of `H`).
* `localSchauder_fixedPoint_of_mapsTo`: whenever `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` (`0 ≤ λ ≤ 1`,
  `ε ≤ ε₀`), `T` has a fixed point `g ∈ D_λ(I_ε)`, which solves the Euler equation (4) on `I_ε`
  (by `schauder_closed`, Schauder's theorem for a closed convex set with relatively compact
  image).
* **Proposition 18.2 + Schauder** (`prop_18_2_schauder`, p. 551): for every `λ ∈ (λ*, 1)` and
  the `ε` of Proposition 18.2, `T` has a fixed point in `D_λ(I_ε)` solving (4) on `I_ε`.
  No contraction estimate is used, so the book's first route works with the `ε` of
  Proposition 18.2 alone (Proposition 18.3 shrinks `ε` further to get a contraction).
* `prop_18_2_schauder_eq_contraction`: for an `ε` as in Proposition 18.3 (from
  `local_constants`), `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` and every fixed point of `T` in `D_λ(I_ε)`, in
  particular the one given by Schauder's theorem, equals the contraction fixed point
  (`exists_fixedPoint_of_bounds`, `eq_of_fixed`).

The book's statement of the route is correct; Exercise 18.3 supplies its continuity hypothesis
(with the manual's estimate corrected, `Top_sub_le`). Schauder's theorem gives existence only;
uniqueness needs the contraction route.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology Metric

/-- **`D_λ(I_ε)` is convex** in `C(I_ε)` (p. 551). -/
theorem convex_DC (ks ε lam : ℝ) (hε : 0 < ε) : Convex ℝ (DC ks ε lam hε) := by
  intro h hh h' hh' a b ha hb hab
  refine ⟨?_, fun k k' => ?_⟩
  · change a * h ⟨ks, center_mem_Jint hε.le⟩ + b * h' ⟨ks, center_mem_Jint hε.le⟩ = ks
    rw [hh.1, hh'.1, ← add_mul, hab, one_mul]
  · change |(a * h k + b * h' k) - (a * h k' + b * h' k')| ≤ lam * |(k : ℝ) - k'|
    have e : (a * h k + b * h' k) - (a * h k' + b * h' k') =
        a * (h k - h k') + b * (h' k - h' k') := by ring
    rw [e]
    calc |a * (h k - h k') + b * (h' k - h' k')|
        ≤ |a * (h k - h k')| + |b * (h' k - h' k')| := abs_add_le _ _
      _ = a * |h k - h k'| + b * |h' k - h' k'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (lam * |(k : ℝ) - k'|) + b * (lam * |(k : ℝ) - k'|) := by
          have := mul_le_mul_of_nonneg_left (hh.2 k k') ha
          have := mul_le_mul_of_nonneg_left (hh'.2 k k') hb
          linarith
      _ = lam * |(k : ℝ) - k'| := by rw [← add_mul, hab, one_mul]

/-- The members of `D_λ(I_ε)` are bounded by `|k*| + λε` (for `λ ≥ 0`). -/
theorem abs_le_of_mem_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) {h : C(Jint ks ε, ℝ)}
    (hh : h ∈ DC ks ε lam hε) (k : Jint ks ε) : |h k| ≤ |ks| + lam * ε := by
  have h1 := hh.2 k ⟨ks, center_mem_Jint hε.le⟩
  rw [hh.1] at h1
  have h2 : |(k : ℝ) - ks| ≤ ε := mem_Jint_iff.1 k.2
  have h3 := mul_le_mul_of_nonneg_left h2 hl0
  calc |h k| = |(h k - ks) + ks| := by ring_nf
    _ ≤ |h k - ks| + |ks| := abs_add_le _ _
    _ ≤ |ks| + lam * ε := by linarith

/-- **`D_λ(I_ε)` is bounded** in `C(I_ε)`. -/
theorem isBounded_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) :
    Bornology.IsBounded (DC ks ε lam hε) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨|ks| + lam * ε, fun h hh => ?_⟩
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun k => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_of_mem_DC hε hl0 hh k

/-- **`D_λ(I_ε)` is totally bounded** in `C(I_ε)` (Arzelà–Ascoli): its members are uniformly
`λ`-Lipschitz, so the family is equicontinuous in the sense of p. 520, and
`totallyBounded_of_equicontinuous` applies in `I_ε →ᵇ ℝ`, isometric to `C(I_ε)`. -/
theorem totallyBounded_DC {ks ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam) :
    TotallyBounded (DC ks ε lam hε) := by
  set e := ContinuousMap.isometryEquivBoundedOfCompact (Jint ks ε) ℝ with he
  have hX : TotallyBounded (univ : Set (Jint ks ε)) := isCompact_univ.totallyBounded
  have hbS : Bornology.IsBounded (e '' DC ks ε lam hε) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨|ks| + lam * ε, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun k => ?_
    rw [Real.norm_eq_abs]
    exact abs_le_of_mem_DC hε hl0 hh k
  have heq : ∀ η > 0, ∃ δ > 0, ∀ x y : Jint ks ε, dist x y < δ →
      ∀ g ∈ e '' DC ks ε lam hε, |g x - g y| < η := by
    intro η hη
    refine ⟨η / (lam + 1), div_pos hη (by linarith), fun x y hxy => ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    change |h x - h y| < η
    have hxy' : |(x : ℝ) - y| < η / (lam + 1) := by
      rwa [Subtype.dist_eq, Real.dist_eq] at hxy
    have h1 := hh.2 x y
    have h2 : lam * |(x : ℝ) - y| ≤ (lam + 1) * |(x : ℝ) - y| := by
      nlinarith [abs_nonneg ((x : ℝ) - y)]
    have h3 : (lam + 1) * |(x : ℝ) - y| < η := by
      rwa [lt_div_iff₀ (by linarith), mul_comm] at hxy'
    linarith
  have htb := totallyBounded_of_equicontinuous hX hbS heq
  have hpre := totallyBounded_preimage e.isometry.isUniformInducing htb
  refine hpre.subset fun h hh => ?_
  change e h ∈ e '' DC ks ε lam hε
  exact mem_image_of_mem e hh

/-- **Exercise 18.3 (continuity on `D_λ(I_ε)`)**, in the form needed for Schauder's theorem: the
operator `T` on `C(I_ε)` is continuous on `D_λ(I_ε)` (indeed Lipschitz there, with constant
`B₂(1 + λ)`, `B₂` a Lipschitz constant of `H` in its second argument). -/
theorem continuousOn_TC {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) : ContinuousOn (TC H hH.continuous hε) (DC ks ε lam hε) := by
  obtain ⟨B₁, B₂, -, hB₂, hB⟩ := hH.lipschitz
  have hHB : HBound H ks ε B₁ B₂ := fun x _ x' _ z _ z' _ => hB x x' z z'
  have hK0 : 0 ≤ B₂ * (1 + lam) := mul_nonneg hB₂ (by linarith)
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (B₂ * (1 + lam)))
    fun h hh h' hh' => ?_).continuousOn
  rw [Real.coe_toNNReal _ hK0]
  exact TC_dist_le hH hε hl0 hl1 hB₂ hHB hh hh'

/-- **The Schauder route** (p. 551). Let `H` be a local solution of (7) on `I_{ε₀}`,
`0 < ε ≤ ε₀`, `0 ≤ λ ≤ 1`, and suppose `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`. Then `T` has a fixed point
`g ∈ D_λ(I_ε)`, and `g` solves the Euler equation (4), `F[k, g(k), g²(k)] = 0`, on `I_ε`.
(Schauder's theorem, `schauder_closed`, on the nonempty closed convex set `D_λ(I_ε)` of the
Banach space `C(I_ε)`; `T` is continuous there (Exercise 18.3) and `T(D_λ(I_ε))` is relatively
compact because `D_λ(I_ε)` is totally bounded.) -/
theorem localSchauder_fixedPoint_of_mapsTo {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : LocalSolution β θ U f ks ε₀ H) {ε lam : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hT : ∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) :
    ∃ g ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
      ∀ k ∈ Jint ks ε, Feq β θ U f k (g k) (g (g k)) = 0 := by
  have hmaps : MapsTo (TC H hH.continuous hε) (DC ks ε lam hε) (DC ks ε lam hε) := by
    intro h hh
    rw [mem_DC_iff] at hh ⊢
    exact Dlam_congr hε.le (fun k hk => (extendC_TC H hH.continuous hε h hk).symm) (hT _ hh)
  have hcpt : IsCompact (closure (TC H hH.continuous hε '' DC ks ε lam hε)) :=
    ((totallyBounded_DC hε hl0).subset (image_subset_iff.2 hmaps)).closure.isCompact_of_isClosed
      isClosed_closure
  obtain ⟨g0, hg0, hfix⟩ := schauder_closed (isClosed_DC ks ε lam hε) (convex_DC ks ε lam hε)
    ⟨_, const_mem_DC hε hl0⟩ (continuousOn_TC hH hε hl0 hl1) hmaps hcpt
  have hg := (mem_DC_iff hε _).1 hg0
  have hfix' : ∀ k ∈ Jint ks ε, Top H (extendC hε g0) k = extendC hε g0 k := fun k hk => by
    rw [← extendC_TC H hH.continuous hε g0 hk, hfix]
  refine ⟨extendC hε g0, hg, hfix', fun k hk => ?_⟩
  have hgm := Dlam_mapsTo hg hl1
  have h7 := hH.eq7 k (Jint_mono hεε₀ hk) _ (Jint_mono hεε₀ (hgm _ (hgm k hk)))
  have e : H k (extendC hε g0 (extendC hε g0 k)) = extendC hε g0 k := hfix' k hk
  rwa [e] at h7

/-- **Proposition 18.2 with Schauder's theorem** (p. 551, the first of the book's three routes).
Under `LocalHyp` and with `H` the local solution of (7) on `I_{ε₀}`: for every `λ ∈ (λ*, 1)`
there is `ε ∈ (0, ε₀]` (the one of Proposition 18.2) such that `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` and `T`
has a fixed point `g ∈ D_λ(I_ε)`, which solves the Euler equation (4) on `I_ε`. -/
theorem prop_18_2_schauder {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ (∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) ∧
      ∃ g ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
        ∀ k ∈ Jint ks ε, Feq β θ U f k (g k) (g (g k)) = 0 := by
  obtain ⟨ε, hε, hεε₀, hT⟩ := prop_18_2 L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  exact ⟨ε, hε, hεε₀, hT, localSchauder_fixedPoint_of_mapsTo hH hε hεε₀ hlpos.le hl1.le hT⟩

/-- **The two routes agree.** For every `λ ∈ (λ*, 1)` there are `ε ∈ (0, ε₀]` and `g ∈ D_λ(I_ε)`
such that `T(D_λ(I_ε)) ⊆ D_λ(I_ε)`, `g` is the fixed point given by the Contraction Mapping
Theorem (Proposition 18.3), and every fixed point of `T` in `D_λ(I_ε)` (in particular the one
given by Schauder's theorem, `localSchauder_fixedPoint_of_mapsTo`) equals `g` on `I_ε`. -/
theorem prop_18_2_schauder_eq_contraction {β θ ks ε₀ : ℝ} {U f : ℝ → ℝ} {H : ℝ → ℝ → ℝ}
    (L : LocalHyp β θ U f ks) (hH : LocalSolution β θ U f ks ε₀ H) {lam : ℝ}
    (hl : lamStar β θ U f ks < lam) (hl1 : lam < 1) :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ (∀ h ∈ Dlam ks ε lam, Top H h ∈ Dlam ks ε lam) ∧
      ∃ g ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g k = g k) ∧
        ∀ g' ∈ Dlam ks ε lam, (∀ k ∈ Jint ks ε, Top H g' k = g' k) →
          ∀ k ∈ Jint ks ε, g' k = g k := by
  obtain ⟨m₁, m₂, ε, hε, hεε₀, -, hm₂, hsum, hK, -, hB⟩ := local_constants L hH hl hl1
  have hlpos : 0 < lam := (L.charPoly_roots.2.2.1).trans hl
  obtain ⟨g, hg, hfix, -⟩ :=
    exists_fixedPoint_of_bounds hH hε hεε₀ hlpos.le hl1.le hm₂ hsum hK hB
  refine ⟨ε, hε, hεε₀, fun h hh => Top_mem_Dlam hB hm₂ hlpos.le hl1.le hsum hH.center hh, g,
    hg, hfix, fun g' hg' hfix' k hk => ?_⟩
  exact eq_of_fixed hB hm₂ hlpos.le hK (Dlam_mapsTo hg' hl1.le) (Dlam_mapsTo hg hl1.le) hg.2
    hfix' hfix k hk

end StokeyLucasPrescott.EquilibriaWithDistortions
