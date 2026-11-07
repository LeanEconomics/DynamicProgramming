/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.SIEuler

/-!
# §8.3.2: Lemmas 8.3.1 and 8.3.2 (the consumption and saving policies)

Miao, §8.3.2, pp. 249–251.

* **Lemma 8.3.1** (`lemma_8_3_1`): `c` is strictly increasing on `[x_min, ∞)` and for
  `x_min ≤ x < x′`, `0 ≤ â(x′) − â(x) < x′ − x`, with equality (in the first inequality) iff
  `â(x′) = â(x) = 0`. As the book remarks (p. 250), the proof uses neither `βR < 1` nor
  anything about uncertainty. Consequences: `â` is nondecreasing and `1`-Lipschitz, so `â` and
  `c` are continuous (`sav_lipschitz`, `continuousOn_sav`, `continuousOn_cons`); where the
  constraint does not bind, `â` is strictly increasing with slope `< 1`
  (`sav_strictMono_of_pos`, p. 250).
* `sav_eq_zero_iff`: the constraint binds at `x` iff `u′(x) ≥ βR E V′(y − rb)`.
* **Lemma 8.3.2** (Schechtman–Escudero; `lemma_8_3_2`): if `βR < 1` there is `x̂ > x_min`,
  the unique solution of `u′(x̂) = βR E V′(y − rb)`, with `â(x) = 0` for `x ≤ x̂` and `â(x) > 0`
  for `x > x̂`. The book argues by contradiction with a constraint that "never binds"; the proof
  here shows directly that the constraint binds at `x_min` (`sav_xmin`), from
  `βR E V′(y − rb) ≤ βR V′(x_min) < V′(x_min)`.
-/

namespace Miao.Applications

open MeasureTheory Filter Topology

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

/-- If `â(x) > 0` and `x < x′` then `â(x) < â(x′)` and `â(x′) − â(x) < x′ − x`. -/
theorem sav_lt_of_pos {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x < x') (hpos : 0 < S.sav x) :
    S.sav x < S.sav x' ∧ S.sav x' - S.sav x < x' - x := by
  have hx' : M.xmin ≤ x' := hx.trans hxx.le
  have hc := S.cons_pos hx
  have hc' := S.cons_pos hx'
  rw [cons_eq] at hc hc'
  have he := (S.euler hx).2 hpos
  rw [cons_eq] at he
  have hs0' := (S.sav_mem x' hx').1
  have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  have hlt : S.sav x < S.sav x' := by
    by_contra hcon
    push Not at hcon
    have h1 := S.euler_le hx'
    rw [cons_eq] at h1
    have h2 := S.D_strictAnti.antitoneOn (Set.mem_Ici.2 hs0') (Set.mem_Ici.2 hpos.le) hcon
    have h3 := M.du_anti (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hc') (by linarith : x - S.sav x <
      x' - S.sav x')
    nlinarith
  refine ⟨hlt, ?_⟩
  have he' := (S.euler hx').2 (hpos.trans hlt)
  rw [cons_eq] at he'
  have h2 := S.D_strictAnti (Set.mem_Ici.2 hpos.le) (Set.mem_Ici.2 hs0') hlt
  by_contra hcon
  push Not at hcon
  have h3 := M.du_anti.antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hc)
    (by linarith : x' - S.sav x' ≤ x - S.sav x)
  nlinarith

/-- If `â(x) = 0` and `x < x′` then `â(x′) < x′ − x`. -/
theorem sav_lt_of_zero {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x < x') (hzero : S.sav x = 0) :
    S.sav x' < x' - x := by
  have hx' : M.xmin ≤ x' := hx.trans hxx.le
  rcases (S.sav_mem x' hx').1.lt_or_eq with hpos | hz
  · by_contra hcon
    push Not at hcon
    have hc' := S.cons_pos hx'
    rw [cons_eq] at hc'
    have he' := (S.euler hx').2 hpos
    rw [cons_eq] at he'
    have h0 := S.euler_le hx
    rw [cons_eq, hzero, sub_zero] at h0
    have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
    have h1 := S.D_strictAnti.antitoneOn (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ x' - x))
      (Set.mem_Ici.2 hpos.le) hcon
    have h2 := S.D_strictAnti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤
      x' - x)) (by linarith : (0 : ℝ) < x' - x)
    have hx0 : 0 < x := M.xmin_pos.trans_le hx
    have h3 := M.du_anti.antitoneOn (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hx0)
      (by linarith : x' - S.sav x' ≤ x)
    nlinarith
  · rw [← hz]; linarith

/-- **Lemma 8.3.1** (Miao, p. 249). Let `β ∈ (0, 1)` and `R > 0`. The consumption policy `c` is
strictly increasing on `[x_min, ∞)`, and for `x_min ≤ x < x′`,
`0 ≤ â(x′) − â(x) < x′ − x`, with `â(x′) − â(x) = 0` iff `â(x′) = â(x) = 0`. -/
theorem lemma_8_3_1 : StrictMonoOn S.cons (Set.Ici M.xmin) ∧
    ∀ x x', M.xmin ≤ x → x < x' →
      0 ≤ S.sav x' - S.sav x ∧ S.sav x' - S.sav x < x' - x ∧
        (S.sav x' - S.sav x = 0 ↔ S.sav x' = 0 ∧ S.sav x = 0) := by
  refine ⟨fun x hx x' hx' hxx => ?_, fun x x' hx hxx => ?_⟩
  · have hx0 : M.xmin ≤ x := hx
    have hx0' : M.xmin ≤ x' := hx'
    have h1 := S.dV_strictAnti hx hx' hxx
    rw [S.envelope x hx0, S.envelope x' hx0'] at h1
    by_contra hcon
    push Not at hcon
    have := M.du_anti.antitoneOn (Set.mem_Ioi.2 (S.cons_pos hx0')) (Set.mem_Ioi.2
      (S.cons_pos hx0)) hcon
    rw [cons_eq, cons_eq] at this
    linarith
  · rcases (S.sav_mem x hx).1.lt_or_eq with hpos | hz
    · obtain ⟨h1, h2⟩ := S.sav_lt_of_pos hx hxx hpos
      refine ⟨by linarith, h2, ⟨fun h => by linarith, fun h => by linarith [h.1, h.2]⟩⟩
    · have h1 := S.sav_lt_of_zero hx hxx hz.symm
      have h0 := (S.sav_mem x' (hx.trans hxx.le)).1
      rw [← hz]
      refine ⟨by linarith, by linarith, ⟨fun h => ⟨by linarith, rfl⟩, fun h => by linarith [h.1]⟩⟩

/-- `â` is nondecreasing on `[x_min, ∞)`. -/
theorem sav_mono : MonotoneOn S.sav (Set.Ici M.xmin) := by
  intro x hx x' _ hxx
  rcases hxx.lt_or_eq with hlt | heq
  · linarith [((S.lemma_8_3_1).2 x x' hx hlt).1]
  · rw [heq]

/-- `c` is nondecreasing on `[x_min, ∞)`. -/
theorem cons_mono : MonotoneOn S.cons (Set.Ici M.xmin) := S.lemma_8_3_1.1.monotoneOn

/-- `0 ≤ â(x′) − â(x) ≤ x′ − x` for `x_min ≤ x ≤ x′`. -/
theorem sav_sub_bounds {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x ≤ x') :
    0 ≤ S.sav x' - S.sav x ∧ S.sav x' - S.sav x ≤ x' - x := by
  rcases hxx.lt_or_eq with hlt | heq
  · obtain ⟨h1, h2, -⟩ := (S.lemma_8_3_1).2 x x' hx hlt
    exact ⟨h1, h2.le⟩
  · subst heq; simp

/-- `0 ≤ c(x′) − c(x) ≤ x′ − x` for `x_min ≤ x ≤ x′`. -/
theorem cons_sub_bounds {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x ≤ x') :
    0 ≤ S.cons x' - S.cons x ∧ S.cons x' - S.cons x ≤ x' - x := by
  obtain ⟨h1, h2⟩ := S.sav_sub_bounds hx hxx
  rw [cons_eq, cons_eq]
  constructor <;> linarith

/-- `â` is `1`-Lipschitz on `[x_min, ∞)`. -/
theorem sav_lipschitz : LipschitzOnWith 1 S.sav (Set.Ici M.xmin) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total x x' with h | h
  · obtain ⟨h1, h2⟩ := S.sav_sub_bounds hx h
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h2
  · obtain ⟨h1, h2⟩ := S.sav_sub_bounds hx' h
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
    exact h2

/-- `â` is continuous on `[x_min, ∞)`. -/
theorem continuousOn_sav : ContinuousOn S.sav (Set.Ici M.xmin) :=
  S.sav_lipschitz.continuousOn

/-- `c` is continuous on `[x_min, ∞)`. -/
theorem continuousOn_cons : ContinuousOn S.cons (Set.Ici M.xmin) :=
  continuousOn_id.sub S.continuousOn_sav

/-- Miao, p. 250: where the borrowing constraint does not bind, the saving function is strictly
increasing with slope less than `1`: if `â(x) > 0` and `x < x′`, then
`â(x) < â(x′)` and `â(x′) − â(x) < x′ − x` (so also `c(x) < c(x′)`). -/
theorem sav_strictMono_of_pos {x x' : ℝ} (hx : M.xmin ≤ x) (hxx : x < x')
    (hpos : 0 < S.sav x) :
    S.sav x < S.sav x' ∧ S.sav x' - S.sav x < x' - x ∧ S.cons x < S.cons x' :=
  ⟨(S.sav_lt_of_pos hx hxx hpos).1, (S.sav_lt_of_pos hx hxx hpos).2,
    S.lemma_8_3_1.1 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hxx.le)) hxx⟩

/-- The borrowing constraint binds at `x` iff `u′(x) ≥ βR E V′(y − rb)`. -/
theorem sav_eq_zero_iff {x : ℝ} (hx : M.xmin ≤ x) :
    S.sav x = 0 ↔ M.β * M.R * S.D 0 ≤ M.du x := by
  constructor
  · intro h
    have := S.euler_le hx
    rwa [cons_eq, h, sub_zero] at this
  · intro h
    by_contra hne
    have hpos : 0 < S.sav x := lt_of_le_of_ne (S.sav_mem x hx).1 (Ne.symm hne)
    have he := (S.euler hx).2 hpos
    have hc := S.cons_pos hx
    rw [cons_eq] at he hc
    have hβR : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
    have h1 := S.D_strictAnti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hpos.le) hpos
    have h2 := M.du_anti (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 (M.xmin_pos.trans_le hx))
      (by linarith : x - S.sav x < x)
    nlinarith

/-- With `βR < 1` the constraint binds at `x_min`, and `u′(x_min) > βR E V′(y − rb)`. -/
theorem sav_xmin (hβR : M.β * M.R < 1) :
    S.sav M.xmin = 0 ∧ M.β * M.R * S.D 0 < M.du M.xmin := by
  have hD := S.D_le le_rfl
  have hdV := S.dV_pos le_rfl
  have hβR0 : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  have hK : M.β * M.R * S.D 0 < S.dV M.xmin := by nlinarith
  rw [S.envelope _ le_rfl] at hK
  have hz : S.sav M.xmin = 0 := by
    by_contra hne
    have hpos : 0 < S.sav M.xmin := lt_of_le_of_ne (S.sav_mem _ le_rfl).1 (Ne.symm hne)
    have he := (S.euler le_rfl).2 hpos
    rw [cons_eq] at he
    have h1 := S.D_strictAnti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hpos.le) hpos
    nlinarith
  rw [hz, sub_zero] at hK
  exact ⟨hz, hK⟩

/-- **Lemma 8.3.2** (Schechtman and Escudero (1977); Miao, p. 251). Let `βR < 1` (and
`x_min = y_min − rb > 0`). There is `x̂ > x_min` such that `â(x) = 0` if `x_min ≤ x ≤ x̂` and
`â(x) > 0` if `x > x̂`; `x̂` is the unique solution of `u′(x̂) = βR E V′(y − rb)`. -/
theorem lemma_8_3_2 (hβR : M.β * M.R < 1) :
    ∃ xhat, M.xmin < xhat ∧ M.du xhat = M.β * M.R * S.D 0 ∧
      (∀ z, 0 < z → M.du z = M.β * M.R * S.D 0 → z = xhat) ∧
      ∀ x, M.xmin ≤ x → (x ≤ xhat → S.sav x = 0) ∧ (xhat < x → 0 < S.sav x) := by
  obtain ⟨-, hK⟩ := S.sav_xmin hβR
  set K := M.β * M.R * S.D 0
  have hK0 : 0 < K := mul_pos (mul_pos M.β_pos M.R_pos) (S.D_pos le_rfl)
  obtain ⟨X, hX⟩ := (eventually_atTop.1 ((M.inada_top.eventually (gt_mem_nhds hK0)).and
    (eventually_gt_atTop M.xmin)))
  have hXX := hX (max X (M.xmin + 1)) (le_max_left _ _)
  set X' := max X (M.xmin + 1)
  have hcont : ContinuousOn M.du (Set.Icc M.xmin X') :=
    M.du_cont.mono fun z hz => Set.mem_Ioi.2 (M.xmin_pos.trans_le hz.1)
  obtain ⟨xhat, hxm, hxe⟩ := intermediate_value_Ioo' hXX.2.le hcont ⟨hXX.1, hK⟩
  have hpos : ∀ z, M.xmin ≤ z → 0 < z := fun z hz => M.xmin_pos.trans_le hz
  refine ⟨xhat, hxm.1, hxe, fun z hz hze => ?_, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases lt_trichotomy z xhat with hlt | heq | hgt
    · have := M.du_anti (Set.mem_Ioi.2 hz) (Set.mem_Ioi.2 (hpos _ hxm.1.le)) hlt; linarith
    · exact heq
    · have := M.du_anti (Set.mem_Ioi.2 (hpos _ hxm.1.le)) (Set.mem_Ioi.2 hz) hgt; linarith
  · refine (S.sav_eq_zero_iff hx).2 ?_
    change K ≤ M.du x
    rw [← hxe]
    exact M.du_anti.antitoneOn (Set.mem_Ioi.2 (hpos _ hx)) (Set.mem_Ioi.2 (hpos _ hxm.1.le)) h
  · have hlt := M.du_anti (Set.mem_Ioi.2 (hpos _ hxm.1.le)) (Set.mem_Ioi.2 (hpos _ hx)) h
    rw [hxe] at hlt
    have hne : S.sav x ≠ 0 := fun h0 => by
      have := (S.sav_eq_zero_iff hx).1 h0
      linarith
    exact lt_of_le_of_ne (S.sav_mem x hx).1 (Ne.symm hne)

end SIModel.Solution

end Miao.Applications
