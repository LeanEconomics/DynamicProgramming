/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMHeterogeneousFirms.Hulten

/-!
# Hulten's theorem: a concrete economy (AKMM App. 22.A.5)

A one-good, one-factor economy satisfies every hypothesis of `hulten`: technology `y ≤ Aℓ`,
labour endowment `1`, utility `U(c) = c`, price of the good `1` and wage `A`. The planner's value
is `V(t) = t`, and Hulten's theorem gives `dV/dA = 1` and the Domar weight `1`
(`hulten_one_sector`). This shows that the hypotheses of `hulten` are consistent.
-/

open Filter Topology StokeyLucasPrescott.ParetoOptimaEquilibria

namespace AKMM.HeterogeneousFirms

/-- The price functional of the one-sector economy: good at `1`, labour at `A`. -/
noncomputable def hultenOnePrice (A : ℝ) : StrongDual ℝ (Unit ⊕ Unit → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => z (Sum.inl ()) + A * z (Sum.inr ())
      map_add' := fun z z' => by simp only [Pi.add_apply]; ring
      map_smul' := fun r z => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem hulten_one_price_apply (A : ℝ) (z : Unit ⊕ Unit → ℝ) :
    hultenOnePrice A z = z (Sum.inl ()) + A * z (Sum.inr ()) := rfl

/-- AKMM, App. 22.A.5: **a concrete instance of Hulten's theorem**. In the economy with
`y ≤ Aℓ`, `ℓ̄ = 1`, `U(c) = c` and `A > 0`, the competitive equilibrium (`c = A`, `p = 1`,
`w = A`) satisfies all hypotheses of `hulten`, the planner's value is `V(t) = t`, and
Hulten's theorem gives `dV/dA = pY/A = 1` and the Domar weight `pY/Σpc = 1`. -/
theorem hulten_one_sector {A : ℝ} (hA : 0 < A) :
    (fun t : ℝ => t) A = (fun c : Unit → ℝ => c ()) (fun _ => A) ∧
      (1 : ℝ) = hultenOnePrice A (hultenGoods (Pi.single () 1)) * (A * 1) / A ∧
      (1 : ℝ) * A / A = hultenOnePrice A (hultenGoods (Pi.single () 1)) * (A * 1) /
        hultenOnePrice A (hultenGoods fun _ => A) := by
  set F : Unit → (Unit → ℝ) → (Unit → ℝ) → ℝ := fun _ l _ => l ()
  set a : Unit → ℝ := fun _ => A
  set e : Unit → ℝ := fun _ => 1
  set U : (Unit → ℝ) → ℝ := fun c => c ()
  set φ := hultenOnePrice A
  set z0 : Unit ⊕ Unit → ℝ := Sum.elim (fun _ => A) (fun _ => -1)
  set xc : Unit → (Unit ⊕ Unit → ℝ) := fun _ => z0
  set ys : Unit → (Unit ⊕ Unit → ℝ) := fun _ => hultenNet () (a () * F () (fun _ => 1) 0)
    (fun _ => 1) 0
  have hnet : ∀ (y : ℝ) (l x : Unit → ℝ), hultenNet () y l x =
      Sum.elim (fun _ => y - x ()) (fun _ => -l ()) := fun y l x => by
    funext s; cases s <;> simp [hultenNet]
  have hfeas0 : Feasible (hultenCons e) (hultenTech F a) xc ys := by
    refine ⟨fun _ v => by simp [xc, z0, e], fun j => ⟨a () * F () (fun _ => 1) 0, fun _ => 1, 0,
      fun _ => zero_le_one, le_rfl, le_rfl, rfl⟩, ?_⟩
    funext s
    cases s <;> simp [xc, ys, z0, hnet, a, F]
  have hCE : CompetitiveEq (hultenCons e) (hultenUtil U) (hultenTech F a) xc ys φ := by
    refine ⟨hfeas0, fun _ z hz hle => ?_, fun j w hw => ?_⟩
    · have hz' := hz ()
      simp only [φ, hulten_one_price_apply, hz', xc, z0, Sum.elim_inl, Sum.elim_inr, e] at hle
      simp only [hultenUtil, U, xc, z0, Sum.elim_inl]
      linarith
    · obtain ⟨y, l, x, hl, hx, hy, rfl⟩ := hw
      simp only [φ, hulten_one_price_apply, ys, hnet, Sum.elim_inl, Sum.elim_inr, a, F]
      have hx0 : (0 : ℝ) ≤ x () := hx ()
      have : y ≤ A * l () := hy
      simp only [Pi.zero_apply]
      linarith
  have hLNS : LocalNonsatiation (hultenCons e) (hultenUtil U) := by
    intro _ z hz
    refine ⟨fun n => z + (1 / ((n : ℝ) + 1)) • hultenGoods (fun _ => (1 : ℝ)), fun n => ?_,
      ?_, fun n => ?_⟩
    · intro v
      simp only [Pi.add_apply, Pi.smul_apply, hulten_goods_apply, Sum.elim_inr, Pi.zero_apply,
        smul_zero, add_zero]
      exact hz v
    · have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := (h.smul_const (hultenGoods (fun _ => (1 : ℝ)))).const_add z
      simpa using this
    · simp only [hultenUtil, U, Pi.add_apply, Pi.smul_apply, hulten_goods_apply, Sum.elim_inl,
        smul_eq_mul, mul_one]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hU : HasFDerivAt U (φ.comp hultenGoods) (fun g => xc () (Sum.inl g)) := by
    have : U = ⇑(φ.comp hultenGoods) := by
      funext c
      simp [U, φ, hulten_one_price_apply, hulten_goods_apply]
    rw [this]
    exact (φ.comp hultenGoods).hasFDerivAt
  have hhom : ∀ s : ℝ, 0 < s → U (s • fun g => xc () (Sum.inl g)) =
      s * U (fun g => xc () (Sum.inl g)) := fun s _ => by simp [U]
  have hV : ∀ t, IsLUB {r | ∃ x' y', Feasible (hultenCons e)
      (hultenTech F (Function.update a () t)) x' y' ∧ r = hultenUtil U () (x' ())} t := by
    intro t
    have hupd : Function.update a () t = fun _ => t := by
      funext u; cases u; simp
    rw [hupd]
    refine IsGreatest.isLUB ⟨⟨fun _ => Sum.elim (fun _ => t) (fun _ => -1),
      fun _ => hultenNet () (t * 1) (fun _ => 1) 0, ⟨fun _ v => by simp [e],
        fun j => ⟨t * 1, fun _ => 1, 0, fun _ => zero_le_one, le_rfl, by simp [F], rfl⟩, ?_⟩,
      by simp [hultenUtil, U]⟩, ?_⟩
    · funext s; cases s <;> simp [hnet]
    · rintro r ⟨x', y', ⟨hX, hYs, hsum⟩, rfl⟩
      obtain ⟨y, l, x, hl, hx, hy, hz⟩ := hYs ()
      have hs := congrFun hsum
      simp only [Finset.univ_unique, Finset.sum_singleton, Pi.sub_apply, Pi.zero_apply] at hs
      have h1 := hs (Sum.inr ())
      have h2 := hs (Sum.inl ())
      rw [show (default : Unit) = () from rfl, hz, hnet] at h1 h2
      simp only [Sum.elim_inr, Sum.elim_inl] at h1 h2
      have hxv := hX () ()
      simp only [e] at hxv
      have hl1 : l () = 1 := by linarith
      have hyt : y ≤ t := by
        have h' : y ≤ t * l () := hy
        rwa [hl1, mul_one] at h'
      have := hx ()
      simp only [hultenUtil, U]
      simp only [Pi.zero_apply] at this
      nlinarith
  have hVd : HasDerivAt (fun t : ℝ => t) 1 (a ()) := hasDerivAt_id' _
  have hY : φ (hultenGoods fun g => xc () (Sum.inl g)) ≠ 0 := by
    simp [φ, hulten_one_price_apply, hulten_goods_apply, xc, z0, hA.ne']
  have h := hulten hCE hLNS (i := ()) (li := fun _ => 1) (xi := 0)
    (fun _ => zero_le_one) le_rfl rfl hU hhom hV hVd hA.ne' hY
  simp only [a, F, xc, z0, Sum.elim_inl] at h
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

end AKMM.HeterogeneousFirms
