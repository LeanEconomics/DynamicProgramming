/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.Welfare

/-!
# Hulten's theorem (AKMM §22.7.2, App. 22.A.5)

AKMM, §22.7.2, pp. 683–684, (22.31)–(22.32), and Appendix 22.A.5, pp. 894–896.

The economy has goods `G` and primary factors `V` (the appendix has labour only; the text and the
two-sector example also have capital), both finite; the commodity space is `G ⊕ V → ℝ`. Sector
`j` turns factors `ℓ ≥ 0` and intermediates `x ≥ 0` into `y ≤ aⱼFⱼ(ℓ, x)` of good `j`; the
representative consumer supplies the factor endowment inelastically and has utility `U(c)` over
goods. The competitive equilibrium and Pareto optimality are those of Stokey–Lucas–Prescott
Chapter 15 (`StokeyLucasPrescott.ParetoOptimaEquilibria`), and the **First Welfare Theorem**
(`theorem_15_3`) is imported.

* **Hulten's theorem (22.31), App. 22.A.5**: if the competitive equilibrium is locally nonsatiated,
  `U` is differentiable at `c` with gradient the goods prices (22.A.5, with the book's
  normalisation `λ = 1`) and linearly homogeneous, and the planner's value `V(aᵢ)` is
  differentiable in `aᵢ`, then `dV/daᵢ = pᵢyᵢ/aᵢ` (22.A.8), `V = U(c) = Σ pc` (22.A.6), and the
  elasticity of GDP with respect to `aᵢ` is the Domar weight `pᵢyᵢ/Σ pc` (`hulten`). The
  differentiability of the planner's value is an extra hypothesis (the book's envelope theorem
  presumes it); the proof uses only a lower bound: shifting the extra output of sector `i` to
  consumption is feasible.
* **The two-sector example (22.32)**: `Y = a₁(a₂K)^{1−γ}L^γ`, its elasticities `1` and `1 − γ`,
  the intermediate price and the Domar weights `1` and `1 − γ`, which differ from the value-added
  shares `γ` and `1 − γ` (`eq_22_32`, `hulten_example_prices`).
-/

open Filter Topology StokeyLucasPrescott.ParetoOptimaEquilibria

namespace AKMM.HeterogeneousFirms

variable {G V : Type*} [Fintype G] [Fintype V] [DecidableEq G]

/-- The net output vector of sector `j`: `y` of good `j`, minus intermediates `x` and factors
`ℓ`. -/
def hultenNet (j : G) (y : ℝ) (l : V → ℝ) (x : G → ℝ) : G ⊕ V → ℝ :=
  Sum.elim (fun g => (if g = j then y else 0) - x g) (fun v => -l v)

/-- AKMM, p. 894: the production set of sector `j`, `yⱼ ≤ aⱼFⱼ(ℓⱼ, xⱼ)`. -/
def hultenTech (F : G → (V → ℝ) → (G → ℝ) → ℝ) (a : G → ℝ) (j : G) : Set (G ⊕ V → ℝ) :=
  {z | ∃ y l x, 0 ≤ l ∧ 0 ≤ x ∧ y ≤ a j * F j l x ∧ z = hultenNet j y l x}

/-- AKMM, p. 894: the consumer's set: any goods bundle, with the factor endowment `e` supplied. -/
def hultenCons (e : V → ℝ) : Unit → Set (G ⊕ V → ℝ) :=
  fun _ => {z | ∀ v, z (Sum.inr v) = -e v}

/-- The consumer's utility `U` of the goods part of a bundle. -/
def hultenUtil (U : (G → ℝ) → ℝ) : Unit → (G ⊕ V → ℝ) → ℝ :=
  fun _ z => U fun g => z (Sum.inl g)

/-- The embedding of goods bundles in the commodity space. -/
noncomputable def hultenGoods : (G → ℝ) →L[ℝ] (G ⊕ V → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun d => Sum.elim d 0
      map_add' := fun d d' => by funext s; cases s <;> simp
      map_smul' := fun r d => by funext s; cases s <;> simp }

omit [Fintype V] [DecidableEq G] in
theorem hulten_goods_apply (d : G → ℝ) (s : G ⊕ V) :
    hultenGoods d s = Sum.elim d (0 : V → ℝ) s := rfl

omit [Fintype G] [DecidableEq G] in
/-- AKMM, App. 22.A.5, (22.A.6), p. 895: **GDP equals utility**. If `U` is linearly homogeneous
and differentiable at `c` with gradient the prices (22.A.5, `λ = 1`), then
`Y = Σ pᵢcᵢ = U(c)` (Euler's theorem). -/
theorem eq_22_A_6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → ℝ} {c : E}
    {L : E →L[ℝ] ℝ}
    (hU : HasFDerivAt U L c) (hhom : ∀ s : ℝ, 0 < s → U (s • c) = s * U c) : L c = U c := by
  have h1 : HasDerivAt (fun s : ℝ => U (s • c)) (L c) 1 := by
    have hs : HasDerivAt (fun s : ℝ => s • c) c 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const c
    have hU' : HasFDerivAt U L ((1 : ℝ) • c) := by rwa [one_smul]
    exact hU'.comp_hasDerivAt (1 : ℝ) hs
  have h2 : HasDerivAt (fun s : ℝ => U (s • c)) (U c) 1 := by
    have h : HasDerivAt (fun s : ℝ => s * U c) (U c) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (U c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hhom s hs
  exact h1.unique h2

/-- AKMM, (22.31), p. 683, and App. 22.A.5, pp. 894–896: **Hulten's theorem**. Let `(x, y)` be a
competitive equilibrium at prices `φ` of the economy with productivities `a`, locally
nonsatiated, with consumption `c` and sector `i` on its frontier, `yᵢ = aᵢFᵢ(ℓᵢ, xᵢ)`. Let `U` be
differentiable at `c` with gradient `pc ↦ φ(c)` (22.A.5) and linearly homogeneous, and let
`V(t)` be the planner's value when sector `i`'s productivity is `t` (the least upper bound of
feasible utilities), differentiable at `aᵢ` with derivative `D`. Then `V(aᵢ) = U(c) = Σpc`,
`D = pᵢyᵢ/aᵢ` (22.A.8) and `D·aᵢ/V(aᵢ) = pᵢyᵢ/Σpc`, the Domar weight. -/
theorem hulten {F : G → (V → ℝ) → (G → ℝ) → ℝ} {a : G → ℝ} {e : V → ℝ}
    {U : (G → ℝ) → ℝ} {xc : Unit → (G ⊕ V → ℝ)} {ys : G → (G ⊕ V → ℝ)}
    {φ : StrongDual ℝ (G ⊕ V → ℝ)}
    (hCE : CompetitiveEq (hultenCons e) (hultenUtil U) (hultenTech F a) xc ys φ)
    (hLNS : LocalNonsatiation (hultenCons e) (hultenUtil U))
    {i : G} {li : V → ℝ} {xi : G → ℝ} (hli : 0 ≤ li) (hxi : 0 ≤ xi)
    (hys : ys i = hultenNet i (a i * F i li xi) li xi)
    (hU : HasFDerivAt U (φ.comp hultenGoods) (fun g => xc () (Sum.inl g)))
    (hhom : ∀ s : ℝ, 0 < s → U (s • fun g => xc () (Sum.inl g)) =
      s * U (fun g => xc () (Sum.inl g)))
    {Vf : ℝ → ℝ} (hV : ∀ t, IsLUB {r | ∃ x' y', Feasible (hultenCons e)
      (hultenTech F (Function.update a i t)) x' y' ∧ r = hultenUtil U () (x' ())} (Vf t))
    {D : ℝ} (hVd : HasDerivAt Vf D (a i)) (ha : a i ≠ 0)
    (hY : φ (hultenGoods fun g => xc () (Sum.inl g)) ≠ 0) :
    Vf (a i) = U (fun g => xc () (Sum.inl g)) ∧
      U (fun g => xc () (Sum.inl g)) = φ (hultenGoods fun g => xc () (Sum.inl g)) ∧
      D = φ (hultenGoods (Pi.single i 1)) * (a i * F i li xi) / a i ∧
      D * a i / Vf (a i) = φ (hultenGoods (Pi.single i 1)) * (a i * F i li xi) /
        φ (hultenGoods fun g => xc () (Sum.inl g)) := by
  set c : G → ℝ := fun g => xc () (Sum.inl g) with hc
  set Fi := F i li xi
  set δ : G → ℝ := Pi.single i Fi
  -- the perturbed allocation: extra output of sector `i` goes to consumption
  let x' : ℝ → Unit → (G ⊕ V → ℝ) := fun t _ => xc () + hultenGoods ((t - a i) • δ)
  let y' : ℝ → G → (G ⊕ V → ℝ) := fun t => Function.update ys i (hultenNet i (t * Fi) li xi)
  have hnet : ∀ t, hultenNet i (t * Fi) li xi - hultenNet i (a i * Fi) li xi =
      hultenGoods ((t - a i) • δ) := fun t => by
    funext s
    cases s with
    | inl g =>
      simp only [hultenNet, Pi.sub_apply, Sum.elim_inl, hulten_goods_apply, Pi.smul_apply,
        smul_eq_mul, δ]
      by_cases hg : g = i
      · subst hg; simp; ring
      · simp [hg]
    | inr v => simp [hultenNet, hulten_goods_apply]
  have hfeas : ∀ t, Feasible (hultenCons e) (hultenTech F (Function.update a i t)) (x' t)
      (y' t) := fun t => by
    obtain ⟨⟨hX, hYs, hsum⟩, -, -⟩ := hCE
    refine ⟨fun u => ?_, fun j => ?_, ?_⟩
    · intro v
      have := hX () v
      simp only [x', Pi.add_apply, hulten_goods_apply, Sum.elim_inr, Pi.zero_apply, add_zero]
      exact this
    · by_cases hj : j = i
      · subst hj
        simp only [y', Function.update_self]
        exact ⟨t * Fi, li, xi, hli, hxi, by simp [Fi], rfl⟩
      · simp only [y', Function.update_of_ne hj]
        obtain ⟨y0, l0, x0, hl0, hx0, hy0, hz⟩ := hYs j
        exact ⟨y0, l0, x0, hl0, hx0, by rw [Function.update_of_ne hj]; exact hy0, hz⟩
    · have hsum' : ∑ j, y' t j = ∑ j, ys j + hultenGoods ((t - a i) • δ) := by
        rw [← hnet t, ← hys]
        simp only [y']
        rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
          (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
        abel
      rw [hsum']
      simp only [x', Finset.univ_unique, Finset.sum_singleton] at hsum ⊢
      rw [show (default : Unit) = () from rfl] at hsum
      rw [← sub_sub, ← hsum]
      abel
  -- the lower bound `W(t)`
  let W : ℝ → ℝ := fun t => U (c + (t - a i) • δ)
  have hWle : ∀ t, W t ≤ Vf t := fun t => by
    refine (hV t).1 ⟨x' t, y' t, hfeas t, ?_⟩
    simp only [W, hultenUtil, x']
    congr 1
  -- the First Welfare Theorem: the equilibrium utility is the planner's value
  have hPO := theorem_15_3 hLNS hCE
  have hVa : Vf (a i) = U c := by
    have hupd : Function.update a i (a i) = a := Function.update_eq_self i a
    have hgreat : IsGreatest {r | ∃ x' y', Feasible (hultenCons e)
        (hultenTech F (Function.update a i (a i))) x' y' ∧ r = hultenUtil U () (x' ())} (U c) := by
      rw [hupd]
      refine ⟨⟨xc, ys, hCE.1, rfl⟩, ?_⟩
      rintro r ⟨x'', y'', hF, rfl⟩
      by_contra hlt0
      have hlt := not_le.mp hlt0
      exact hPO.2 ⟨x'', y'', hF, fun u => by cases u; exact hlt.le, (), hlt⟩
    exact (hV (a i)).unique hgreat.isLUB
  have hWa : W (a i) = U c := by simp [W]
  -- `W` is differentiable with derivative `pᵢFᵢ`
  have hWd : HasDerivAt W (φ (hultenGoods δ)) (a i) := by
    have hl : HasDerivAt (fun t : ℝ => c + (t - a i) • δ) δ (a i) := by
      simpa using ((hasDerivAt_id (a i)).sub_const (a i)).smul_const δ |>.const_add c
    have hU2 : HasFDerivAt U (φ.comp hultenGoods) (c + (a i - a i) • δ) := by
      rw [sub_self, zero_smul, add_zero]; exact hU
    exact hU2.comp_hasDerivAt (a i) hl
  -- Fermat: `V − W` has a minimum at `aᵢ`
  have hmin : IsLocalMin (fun t => Vf t - W t) (a i) :=
    Filter.Eventually.of_forall fun t => by
      simp only
      rw [hVa, hWa, sub_self]; linarith [hWle t]
  have hD : D = φ (hultenGoods δ) := by
    have := hmin.hasDerivAt_eq_zero (hVd.sub hWd)
    linarith
  have hδ : δ = Fi • Pi.single i 1 := by
    funext g; simp [δ, Pi.single_apply]
  have hEuler := eq_22_A_6 hU hhom
  simp only [ContinuousLinearMap.comp_apply] at hEuler
  refine ⟨hVa, hEuler.symm, ?_, ?_⟩
  · rw [hD, hδ, map_smul, map_smul, smul_eq_mul]
    field_simp
  · rw [hD, hVa, ← hEuler, hδ, map_smul, map_smul, smul_eq_mul]
    field_simp

/-! ### The two-sector example -/

/-- AKMM, (22.32), p. 684: **the two-sector example**. With `Y = a₁(a₂K)^{1−γ}L^γ`, the
elasticities of `Y` with respect to `a₁` and `a₂` are `1` and `1 − γ`
(`dY/Y = da₁/a₁ + (1−γ)da₂/a₂`). -/
theorem eq_22_32 {γ K L a1 a2 : ℝ} (hK : 0 < K) (ha2 : 0 < a2) :
    HasDerivAt (fun t => t * (a2 * K) ^ (1 - γ) * L ^ γ) ((a2 * K) ^ (1 - γ) * L ^ γ) a1 ∧
      HasDerivAt (fun t => a1 * (t * K) ^ (1 - γ) * L ^ γ)
        ((1 - γ) * (a1 * (a2 * K) ^ (1 - γ) * L ^ γ) / a2) a2 := by
  constructor
  · simpa using ((hasDerivAt_id a1).mul_const ((a2 * K) ^ (1 - γ))).mul_const (L ^ γ)
  · have h1 : HasDerivAt (fun t => t * K) K a2 := by simpa using (hasDerivAt_id a2).mul_const K
    have h2 := h1.rpow_const (p := 1 - γ) (Or.inl (mul_pos ha2 hK).ne')
    have h3 := (h2.const_mul a1).mul_const (L ^ γ)
    convert h3 using 1
    rw [Real.rpow_sub_one (mul_pos ha2 hK).ne']
    field_simp

/-- AKMM, p. 684: **prices and Domar weights in the example**. With the intermediate price
`p = (1−γ)a₁x^{−γ}L^γ`, `x = a₂K`: sector 2's value added (= its sales) is `pa₂K = (1−γ)Y`,
sector 1's value added is `Y − px = γY`, so the Domar weights are `Y/Y = 1` and `1 − γ`, the
coefficients of (22.32), while the value-added share of sector 1 is `γ`. -/
theorem hulten_example_prices {γ K L a1 a2 : ℝ} (hK : 0 < K) (ha2 : 0 < a2) :
    (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K) =
        (1 - γ) * (a1 * (a2 * K) ^ (1 - γ) * L ^ γ) ∧
      a1 * (a2 * K) ^ (1 - γ) * L ^ γ - (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K) =
        γ * (a1 * (a2 * K) ^ (1 - γ) * L ^ γ) := by
  have hx : 0 < a2 * K := mul_pos ha2 hK
  have e : (a2 * K) ^ (-γ) * (a2 * K) = (a2 * K) ^ (1 - γ) := by
    rw [← Real.rpow_add_one hx.ne']; ring_nf
  constructor
  · calc (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K)
        = (1 - γ) * a1 * ((a2 * K) ^ (-γ) * (a2 * K)) * L ^ γ := by ring
      _ = _ := by rw [e]; ring
  · calc a1 * (a2 * K) ^ (1 - γ) * L ^ γ - (1 - γ) * a1 * (a2 * K) ^ (-γ) * L ^ γ * (a2 * K)
        = a1 * (a2 * K) ^ (1 - γ) * L ^ γ - (1 - γ) * a1 * ((a2 * K) ^ (-γ) * (a2 * K)) *
            L ^ γ := by ring
      _ = _ := by rw [e]; ring

end AKMM.HeterogeneousFirms
