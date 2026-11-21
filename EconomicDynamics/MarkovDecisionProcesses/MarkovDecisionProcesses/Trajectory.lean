/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Histories
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The measure on infinite histories (Ionescu Tulcea)

Miao, §5.1, p. 139: "In the infinite-horizon case, the sequence of measures `μᵗ(s₀, ·; π)`,
`t = 1, 2, …`, induces a unique measure `μ^∞(s₀, ·; π)` on `S^∞`." The book attributes this to
the Kolmogorov extension theorem; it is the Ionescu Tulcea theorem, available in Mathlib as
`ProbabilityTheory.Kernel.traj`. The plan enters through the kernels
`κ_t(s₀, …, s_t) = P_{t+1}(s_t, π_t(s₁, …, s_t); ·)` (`trajKernel`).

* `muInf M s₀ π`: a probability measure on trajectories `ω = (s₀, s₁, s₂, …)` with `ω₀ = s₀`
  almost surely (`muInf_zero`).
* `muInf_marginal`: the law of `(s₁, …, s_t)` under `μ^∞` is `μᵗ(s₀, ·; π)` of (5.2).
* `muInf_unique`: `μ^∞` is the only measure on `S^ℕ` with these marginals.

Departure: the book's `S^∞` is the space of `(s₁, s₂, …)`; here the trajectory also carries the
initial state `s₀` (as in Mathlib), which is almost surely the given one.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The history `(s₁, …, s_t)` of a trajectory segment `(s₀, …, s_t)`. -/
def histOf (t : ℕ) (y : (i : Finset.Iic t) → S) : Fin t → S :=
  fun i => y ⟨i.val + 1, Finset.mem_Iic.2 (by omega)⟩

theorem measurable_histOf (t : ℕ) : Measurable (histOf (S := S) t) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_lastState₂ (t : ℕ) :
    Measurable fun p : S × (Fin t → S) => lastState p.1 p.2 := by
  cases t with
  | zero => exact measurable_fst
  | succ t => exact (measurable_pi_apply _).comp measurable_snd

/-- The kernel `κ_t(s₀, …, s_t) = P_{t+1}(s_t, π_t(s₁, …, s_t); ·)`. -/
noncomputable def trajKernel (M : MDP S A) (π : Plan S A) (hπ : ∀ t, Measurable (π t))
    (t : ℕ) : Kernel ((i : Finset.Iic t) → S) S :=
  (M.P t).comap (fun y => (lastState (y ⟨0, Finset.mem_Iic.2 (Nat.zero_le t)⟩) (histOf t y),
      π t (histOf t y)))
    (((measurable_lastState₂ t).comp ((measurable_pi_apply _).prodMk (measurable_histOf t))).prodMk
      ((hπ t).comp (measurable_histOf t)))

theorem isMarkovKernel_trajKernel (M : MDP S A) (hP : M.IsMarkov) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) : IsMarkovKernel (trajKernel M π hπ t) := by
  have := hP t
  unfold trajKernel
  infer_instance

/-- `μ^∞(s₀, ·; π)`, the distribution of the trajectory `(s₀, s₁, …)` (Miao, p. 139), given by
the Ionescu Tulcea theorem. -/
noncomputable def muInf (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) : Measure (ℕ → S) :=
  @Kernel.traj (fun _ => S) _ (trajKernel M π hπ) (isMarkovKernel_trajKernel M hP π hπ) 0
    fun _ => s₀

theorem isProbabilityMeasure_muInf (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) : IsProbabilityMeasure (muInf M hP s₀ π hπ) := by
  have := isMarkovKernel_trajKernel M hP π hπ
  unfold muInf
  infer_instance

/-- The pair `(s₀, (s₁, …, s_t))` of a trajectory segment. -/
def splitSeg (t : ℕ) (y : (i : Finset.Iic t) → S) : S × (Fin t → S) :=
  (y ⟨0, Finset.mem_Iic.2 (Nat.zero_le t)⟩, histOf t y)

theorem measurable_splitSeg (t : ℕ) : Measurable (splitSeg (S := S) t) :=
  (measurable_pi_apply _).prodMk (measurable_histOf t)

/-- The inverse of `splitSeg`. -/
def joinSeg (t : ℕ) (p : S × (Fin t → S)) : (i : Finset.Iic t) → S :=
  fun i => if h : i.1 = 0 then p.1 else
    p.2 ⟨i.1 - 1, by have := Finset.mem_Iic.1 i.2; omega⟩

theorem measurable_joinSeg (t : ℕ) : Measurable (joinSeg (S := S) t) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i.1 = 0
  · simp only [joinSeg, h, ↓reduceDIte]
    exact measurable_fst
  · simp only [joinSeg, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd

omit [MeasurableSpace S] in
theorem joinSeg_splitSeg (t : ℕ) (y : (i : Finset.Iic t) → S) : joinSeg t (splitSeg t y) = y := by
  funext i
  by_cases h : i.1 = 0
  · simp only [joinSeg, splitSeg, h, ↓reduceDIte]
    congr 1
    exact Subtype.ext h.symm
  · simp only [joinSeg, splitSeg, h, ↓reduceDIte, histOf]
    congr 1
    exact Subtype.ext (by simp; omega)

theorem splitSeg_IicProdIoc (t : ℕ) (y : (i : Finset.Iic t) → S) (s : S) :
    splitSeg (t + 1) (IicProdIoc (X := fun _ => S) t (t + 1)
      (y, (MeasurableEquiv.piSingleton (X := fun _ => S) t) s)) =
      (y ⟨0, Finset.mem_Iic.2 (Nat.zero_le t)⟩, Fin.snoc (histOf t y) s) := by
  refine Prod.ext ?_ ?_
  · simp [splitSeg, IicProdIoc]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [splitSeg, histOf, IicProdIoc, MeasurableEquiv.piSingleton]
    · simp only [splitSeg, histOf, IicProdIoc, Fin.snoc_castSucc, Fin.val_castSucc]
      have : j.1 + 1 ≤ t := j.2
      simp [this]

/-- The law of `(s₀, (s₁, …, s_t))` under the partial trajectory is `δ_{s₀} ⊗ μᵗ(s₀, ·; π)`. -/
theorem partialTraj_map_splitSeg (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    (@Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 t (fun _ => s₀)).map
      (splitSeg t) = (mu M s₀ π t).map fun h => (s₀, h) := by
  have hk := isMarkovKernel_trajKernel M hP π hπ
  have hm : ∀ t, Measurable fun h : Fin t → S => (s₀, h) :=
    fun _ => measurable_const.prodMk measurable_id
  induction t with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_splitSeg 0),
      mu_zero, Measure.map_dirac' (hm 0)]
    congr 1
    refine Prod.ext rfl ?_
    exact Subsingleton.elim _ _
  | succ t ih =>
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_splitSeg _), lintegral_map hf (hm _),
      mu_succ_lintegral M hP s₀ (hπ t) (f := fun h => f (s₀, h)) (hf.comp (hm _)),
      Kernel.partialTraj_succ_eq_comp (Nat.zero_le t), Kernel.partialTraj_succ_self,
      Kernel.lintegral_comp _ _ _ (g := fun z => f (splitSeg (t + 1) z))
        (hf.comp (measurable_splitSeg _))]
    have := hP t
    have hF : Measurable fun p : S × (Fin t → S) =>
        ∫⁻ s, f (p.1, Fin.snoc p.2 s) ∂M.P t (lastState p.1 p.2, π t p.2) := by
      have hk2 : Measurable fun p : S × (Fin t → S) => (lastState p.1 p.2, π t p.2) :=
        (measurable_lastState₂ t).prodMk ((hπ t).comp measurable_snd)
      exact (hf.comp (measurable_fst.fst.prodMk ((measurable_snoc t).comp
        (measurable_fst.snd.prodMk measurable_snd)))).lintegral_kernel_prod_right'
          (κ := (M.P t).comap _ hk2) |> fun h => h
    have hstep : ∀ y : (i : Finset.Iic t) → S,
        ∫⁻ z, f (splitSeg (t + 1) z) ∂((Kernel.id ×ₖ ((trajKernel M π hπ t).map
          (MeasurableEquiv.piSingleton (X := fun _ => S) t))).map
            (IicProdIoc (X := fun _ => S) t (t + 1))) y =
        (fun p : S × (Fin t → S) =>
          ∫⁻ s, f (p.1, Fin.snoc p.2 s) ∂M.P t (lastState p.1 p.2, π t p.2)) (splitSeg t y) := by
      intro y
      have hg1 : Measurable fun z => f (splitSeg (t + 1) z) := hf.comp (measurable_splitSeg _)
      have hg2 : Measurable fun p => f (splitSeg (t + 1)
          (IicProdIoc (X := fun _ => S) t (t + 1) p)) :=
        hg1.comp (measurable_IicProdIoc (X := fun _ => S) (m := t) (n := t + 1))
      have hg3 : Measurable fun b => f (splitSeg (t + 1)
          (IicProdIoc (X := fun _ => S) t (t + 1) (y, b))) :=
        hg2.comp (measurable_const.prodMk measurable_id)
      rw [Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => S)) _ hg1,
        Kernel.lintegral_prod _ _ _ hg2,
        Kernel.id_apply, lintegral_dirac' _ hg2.lintegral_prod_right',
        Kernel.lintegral_map _ (MeasurableEquiv.piSingleton (X := fun _ => S) t).measurable _
          hg3]
      simp only [splitSeg_IicProdIoc]
      rfl
    simp_rw [hstep]
    rw [← lintegral_map hF (measurable_splitSeg t), ih, lintegral_map hF (hm t)]

/-- The trajectory map `ω ↦ (ω₀, (ω₁, …, ω_t))`. -/
def splitTraj (t : ℕ) (ω : ℕ → S) : S × (Fin t → S) := (ω 0, fun i => ω (i.val + 1))

theorem measurable_splitTraj (t : ℕ) : Measurable (splitTraj (S := S) t) :=
  (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

omit [MeasurableSpace S] in
theorem splitTraj_eq (t : ℕ) : splitTraj (S := S) t = splitSeg t ∘ frestrictLe t := rfl

/-- The law of `(s₀, (s₁, …, s_t))` under `μ^∞` is `δ_{s₀} ⊗ μᵗ(s₀, ·; π)`. -/
theorem muInf_map_splitTraj (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    (muInf M hP s₀ π hπ).map (splitTraj t) = (mu M s₀ π t).map fun h => (s₀, h) := by
  have := isMarkovKernel_trajKernel M hP π hπ
  rw [splitTraj_eq, ← Measure.map_map (measurable_splitSeg t) (measurable_frestrictLe t), muInf,
    Kernel.traj_map_frestrictLe_apply, partialTraj_map_splitSeg M hP s₀ π hπ t]

/-- Miao, p. 139: the marginal of `μ^∞(s₀, ·; π)` on `(s₁, …, s_t)` is `μᵗ(s₀, ·; π)`. -/
theorem muInf_marginal (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (t : ℕ) :
    (muInf M hP s₀ π hπ).map (fun ω (i : Fin t) => ω (i.val + 1)) = mu M s₀ π t := by
  have h := congrArg (Measure.map Prod.snd) (muInf_map_splitTraj M hP s₀ π hπ t)
  have hm : Measurable fun h : Fin t → S => (s₀, h) := measurable_const.prodMk measurable_id
  have e : (Prod.snd ∘ fun h : Fin t → S => (s₀, h)) = id := rfl
  rw [Measure.map_map measurable_snd (measurable_splitTraj t), Measure.map_map measurable_snd hm,
    e, Measure.map_id] at h
  exact h

/-- Under `μ^∞(s₀, ·; π)` the initial state is `s₀` almost surely. -/
theorem muInf_zero (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) :
    (muInf M hP s₀ π hπ).map (fun ω => ω 0) = Measure.dirac s₀ := by
  have h := congrArg (Measure.map Prod.fst) (muInf_map_splitTraj M hP s₀ π hπ 0)
  have hm : Measurable fun h : Fin 0 → S => (s₀, h) := measurable_const.prodMk measurable_id
  rw [Measure.map_map measurable_fst (measurable_splitTraj 0), Measure.map_map measurable_fst hm,
    mu_zero, Measure.map_dirac' (measurable_fst.comp hm)] at h
  exact h

/-- Miao, p. 139: `μ^∞(s₀, ·; π)` is the **unique** measure on trajectories whose law of
`(s₀, (s₁, …, s_t))` is `δ_{s₀} ⊗ μᵗ(s₀, ·; π)` for every `t`. -/
theorem muInf_unique (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) (ν : Measure (ℕ → S))
    (hν : ∀ t, ν.map (splitTraj t) = (mu M s₀ π t).map fun h => (s₀, h)) :
    ν = muInf M hP s₀ π hπ := by
  have hk := isMarkovKernel_trajKernel M hP π hπ
  have hjs : ∀ n, joinSeg (S := S) n ∘ splitSeg n = id := fun n => funext (joinSeg_splitSeg n)
  have key : ∀ n, ν.map (frestrictLe n) =
      @Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀) := by
    intro n
    have e1 : ν.map (frestrictLe n) = (ν.map (splitTraj n)).map (joinSeg n) := by
      rw [splitTraj_eq, Measure.map_map (measurable_joinSeg n) ((measurable_splitSeg n).comp
        (measurable_frestrictLe n)), ← Function.comp_assoc, hjs, Function.id_comp]
    have e2 : @Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀) =
        ((@Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀)).map
          (splitSeg n)).map (joinSeg n) := by
      rw [Measure.map_map (measurable_joinSeg n) (measurable_splitSeg n), hjs, Measure.map_id]
    rw [e1, e2, hν n, partialTraj_map_splitSeg M hP s₀ π hπ n]
  have hpr : ∀ n, IsProbabilityMeasure
      (@Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀)) :=
    fun n => inferInstance
  have hfin : ∀ I, IsFiniteMeasure (inducedFamily (X := fun _ => S) (fun n =>
      @Kernel.partialTraj (fun _ => S) _ (trajKernel M π hπ) 0 n (fun _ => s₀)) I) := by
    intro I
    unfold inducedFamily
    infer_instance
  have hlim :=
    (isProjectiveLimit_nat_iff (Kernel.isProjectiveMeasureFamily_partialTraj _ _) ν).2
      fun n => by rw [inducedFamily_Iic]; exact key n
  exact hlim.unique (Kernel.isProjectiveLimit_trajFun _ 0 _)

end Miao.MarkovDecisionProcesses
