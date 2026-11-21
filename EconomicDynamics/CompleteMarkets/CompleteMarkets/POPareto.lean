/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.POEventTree
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Pareto optimum

Miao, §13.2, pp. 417–418.

* `po_Feasible y c` is (13.2), with each `cⁱ ∈ L∞₊`; `po_ParetoOptimal` and `po_SolvesPlanner`
  are the definitions of the text.
* **Proposition 13.2.1** (`proposition_13_2_1`): an allocation is Pareto optimal iff it solves
  the planner's problem for some nonzero `λ ∈ ℝᴵ₊`. The "only if" part follows the book: the set
  `𝒰 = {U(x) − U(c) − z}` is convex because each `Uⁱ` is concave (`po_U_concave`), it misses the
  open positive orthant, and Hahn–Banach separates them (`po_planner_of_pareto`). The "if" part
  also follows the book, including the transfer from an agent with zero weight
  (`po_transfer_improvement`), which needs continuity of `uⁱ`. Hypotheses: concavity (only if)
  and continuity (if) of each `uⁱ` on `[0, ∞)`, as in Assumption 13.1.1, and `I ≥ 1`.
* The first-order conditions `λⁱ uⁱ'(cⁱ_t) = λʲ uʲ'(cʲ_t)` (`po_planner_foc`), derived by
  transferring consumption between two agents at one node; (13.3) (`eq_13_3`) and (13.4)
  (`eq_13_4`). The text omits that these hold at nodes of positive probability and for interior
  allocations.
* Risk sharing: consumption depends on the aggregate endowment only (`po_risk_sharing`,
  `po_consumption_fn_aggregate`), so with a Markov aggregate state there is no history dependence
  (`po_no_history_dependence`). The book's argument that (13.4) has one solution in `c¹` is
  replaced by the equivalent monotonicity argument; strictly decreasing marginal utilities
  (`po_strictAntiOn_deriv`, from Assumption 13.1.1) are what is used.
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- Miao, (13.2), p. 417: the allocation `c = (c¹, …, cᴵ)` is feasible for the endowments `y`:
each `cⁱ ∈ L∞₊` and `Σᵢ cⁱ_t(sᵗ) = Σᵢ yⁱ_t(sᵗ)` at every node. -/
def po_Feasible {ι S : Type*} [Fintype ι] (y c : ι → List S → ℝ) : Prop :=
  (∀ i, c i ∈ po_Lplus S) ∧ ∀ h, ∑ i, c i h = ∑ i, y i h

/-- Miao, §13.2, p. 417: `c` is Pareto optimal if it is feasible and no feasible allocation makes
every agent at least as well off and one agent strictly better off. -/
def po_ParetoOptimal {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (y c : ι → List S → ℝ) : Prop :=
  po_Feasible y c ∧ ¬ ∃ d, po_Feasible y d ∧ (∀ i, po_U E i (c i) ≤ po_U E i (d i)) ∧
    ∃ i, po_U E i (c i) < po_U E i (d i)

/-- Miao, §13.2, p. 417: `c` solves the social planner's problem with Pareto weights `λ`:
it maximises `Σᵢ λⁱ Uⁱ(cⁱ)` subject to (13.2). -/
def po_SolvesPlanner {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (y : ι → List S → ℝ) (lam : ι → ℝ) (c : ι → List S → ℝ) : Prop :=
  po_Feasible y c ∧ ∀ d, po_Feasible y d → ∑ i, lam i * po_U E i (d i) ≤ ∑ i, lam i * po_U E i (c i)

/-- Changing a summable family at one index changes its sum by the change at that index. -/
theorem po_tsum_update {S : Type*} [DecidableEq S] (f : List S → ℝ) (hf : Summable f)
    (h : List S) (v : ℝ) : ∑' k, Function.update f h v k = ∑' k, f k + (v - f h) := by
  have : Function.update f h v = fun k => f k + if k = h then v - f h else 0 := by
    funext k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  rw [this, hf.tsum_add (hasSum_ite_eq h _).summable, tsum_ite_eq]

/-- Changing a plan in `L∞₊` at one node to a nonnegative value stays in `L∞₊`. -/
theorem po_update_mem {S : Type*} [DecidableEq S] {x : List S → ℝ} (hx : x ∈ po_Lplus S)
    (h : List S) {v : ℝ} (hv : 0 ≤ v) : Function.update x h v ∈ po_Lplus S := by
  obtain ⟨hx0, B, hB⟩ := hx
  refine ⟨fun k => ?_, max B v, ?_⟩
  · by_cases hk : k = h
    · subst hk; simpa using hv
    · simpa [hk] using hx0 k
  · rintro _ ⟨k, rfl⟩
    by_cases hk : k = h
    · subst hk; simp
    · simp only [Function.update_apply, hk, ↓reduceIte]
      exact le_max_of_le_left (hB ⟨k, rfl⟩)

/-- Miao, (13.1): changing consumption at one node `h` from `x(h)` to `v` changes `Uⁱ` by
`βᵗ Pr(h) (uⁱ(v) − uⁱ(x(h)))`. -/
theorem po_U_update {ι S : Type*} [Fintype S] [DecidableEq S] (E : POEconomy ι S) (i : ι)
    {x : List S → ℝ} (hx : x ∈ po_Lplus S) (h : List S) (v : ℝ) :
    po_U E i (Function.update x h v) = po_U E i x + po_w E h * (E.u i v - E.u i (x h)) := by
  unfold po_U
  have : (fun k => po_w E k * E.u i (Function.update x h v k)) =
      Function.update (fun k => po_w E k * E.u i (x k)) h (po_w E h * E.u i v) := by
    funext k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  rw [this, po_tsum_update _ (eq_13_1 E i hx)]
  ring

/-- The allocation obtained from `c` by moving `δₖ` units to agent `k` at node `h`. -/
def po_perturb {ι S : Type*} [DecidableEq S] (c : ι → List S → ℝ) (h : List S) (δ : ι → ℝ) :
    ι → List S → ℝ :=
  fun k => Function.update (c k) h (c k h + δ k)

/-- Miao, (13.2): a transfer `δ` at one node with `Σₖ δₖ = 0` that keeps consumption
nonnegative preserves feasibility. -/
theorem po_perturb_feasible {ι S : Type*} [Fintype ι] [DecidableEq S]
    {y c : ι → List S → ℝ} (hc : po_Feasible y c) (h : List S) (δ : ι → ℝ)
    (hδ : ∑ k, δ k = 0) (hpos : ∀ k, 0 ≤ c k h + δ k) : po_Feasible y (po_perturb c h δ) := by
  refine ⟨fun k => po_update_mem (hc.1 k) h (hpos k), fun h' => ?_⟩
  unfold po_perturb
  by_cases hh : h' = h
  · subst hh
    simp only [Function.update_self]
    rw [Finset.sum_add_distrib, hδ, add_zero, hc.2]
  · simp only [Function.update_apply, hh, ↓reduceIte]
    exact hc.2 h'

/-- `L∞₊` is convex. -/
theorem po_Lplus_comb {S : Type*} {x x' : List S → ℝ} (hx : x ∈ po_Lplus S)
    (hx' : x' ∈ po_Lplus S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun h => a * x h + b * x' h) ∈ po_Lplus S := by
  obtain ⟨hx0, B, hB⟩ := hx
  obtain ⟨hx0', B', hB'⟩ := hx'
  refine ⟨fun h => by have := hx0 h; have := hx0' h; positivity, a * B + b * B', ?_⟩
  rintro _ ⟨h, rfl⟩
  exact add_le_add (mul_le_mul_of_nonneg_left (hB ⟨h, rfl⟩) ha)
    (mul_le_mul_of_nonneg_left (hB' ⟨h, rfl⟩) hb)

/-- Miao, §13.2, p. 417 ("`𝒰` is convex by the concavity of utility functions"): if `uⁱ` is
concave on `[0, ∞)` then `Uⁱ` is concave on `L∞₊`. -/
theorem po_U_concave {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.u i)) {x x' : List S → ℝ} (hx : x ∈ po_Lplus S)
    (hx' : x' ∈ po_Lplus S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * po_U E i x + b * po_U E i x' ≤ po_U E i (fun h => a * x h + b * x' h) := by
  unfold po_U
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((eq_13_1 E i hx).mul_left a).tsum_add ((eq_13_1 E i hx').mul_left b)]
  refine ((((eq_13_1 E i hx).mul_left a).add ((eq_13_1 E i hx').mul_left b))).tsum_le_tsum
    (fun h => ?_) (eq_13_1 E i (po_Lplus_comb hx hx' ha hb))
  have := hconc.2 (Set.mem_Ici.mpr (hx.1 h)) (Set.mem_Ici.mpr (hx'.1 h)) ha hb hab
  simp only [smul_eq_mul] at this
  nlinarith [po_w_nonneg E h]

/-- Miao, (13.1): `Uⁱ` is monotone on `L∞₊`. -/
theorem po_U_mono {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι) {x x' : List S → ℝ}
    (hx : x ∈ po_Lplus S) (hx' : x' ∈ po_Lplus S) (hle : ∀ h, x h ≤ x' h) :
    po_U E i x ≤ po_U E i x' :=
  (eq_13_1 E i hx).tsum_le_tsum (fun h => mul_le_mul_of_nonneg_left
    ((E.u_mono i).monotoneOn (Set.mem_Ici.mpr (hx.1 h)) (Set.mem_Ici.mpr (hx'.1 h)) (hle h))
    (po_w_nonneg E h)) (eq_13_1 E i hx')

/-- Miao, proof of Proposition 13.2.1, p. 417 ("if" part, first case): if `c` solves the
planner's problem with weights `λ ≥ 0`, no feasible `d` makes everyone weakly better off and an
agent with `λⁱ > 0` strictly better off. -/
theorem po_planner_improvement {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hc : po_SolvesPlanner E y lam c) {d : ι → List S → ℝ}
    (hd : po_Feasible y d) (hle : ∀ i, po_U E i (c i) ≤ po_U E i (d i))
    (hlt : ∃ i, 0 < lam i ∧ po_U E i (c i) < po_U E i (d i)) : False := by
  obtain ⟨i, hi, hlti⟩ := hlt
  have : ∑ k, lam k * po_U E k (c k) < ∑ k, lam k * po_U E k (d k) :=
    Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hlam k))
      ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left hlti hi⟩
  exact absurd (hc.2 d hd) (not_le.mpr this)

/-- Miao, §13.2: a solution of the planner's problem with strictly positive weights is Pareto
optimal. -/
theorem po_pareto_of_planner_pos {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ} (hlam : ∀ i, 0 < lam i)
    (hc : po_SolvesPlanner E y lam c) : po_ParetoOptimal E y c := by
  refine ⟨hc.1, ?_⟩
  rintro ⟨d, hd, hle, i, hi⟩
  exact po_planner_improvement E (fun k => (hlam k).le) hc hd hle ⟨i, hlam i, hi⟩

/-- Miao, proof of Proposition 13.2.1, p. 418 ("We then decrease `ĉⁱ` a little but raise some
other agent `j`'s consumption"): if `d` is feasible and `Uⁱ(dⁱ) > Uⁱ(cⁱ)` for a plan `cⁱ ∈ L∞₊`,
moving a little consumption from `i` to `j ≠ i` at one node keeps `i` above `Uⁱ(cⁱ)`, raises `j`
strictly, and leaves everyone else unchanged. Uses continuity of `uⁱ`. -/
theorem po_transfer_improvement {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y d : ι → List S → ℝ} (hd : po_Feasible y d) {i j : ι} (hij : i ≠ j)
    (hcont : ContinuousOn (E.u i) (Set.Ici 0)) {ci : List S → ℝ} (hci : ci ∈ po_Lplus S)
    (hgap : po_U E i ci < po_U E i (d i)) :
    ∃ d', po_Feasible y d' ∧ po_U E i ci ≤ po_U E i (d' i) ∧
      po_U E j (d j) < po_U E j (d' j) ∧ ∀ k, k ≠ i → k ≠ j → po_U E k (d' k) = po_U E k (d k) := by
  classical
  -- a node of positive weight where `dⁱ > 0`
  have h0mem : (fun _ : List S => (0 : ℝ)) ∈ po_Lplus S :=
    ⟨fun _ => le_rfl, 0, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  obtain ⟨h, hw, hpos⟩ : ∃ h, 0 < po_w E h ∧ 0 < d i h := by
    by_contra hne
    push Not at hne
    have heq : po_U E i (d i) = po_U E i (fun _ => 0) := by
      unfold po_U
      congr 1
      funext h
      rcases (po_w_nonneg E h).lt_or_eq with hw | hw
      · rw [le_antisymm (hne h hw) ((hd.1 i).1 h)]
      · rw [← hw, zero_mul, zero_mul]
    have := po_U_mono E i h0mem hci (fun h => hci.1 h)
    linarith
  set a := d i h
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousWithinAt_iff.mp (hcont a (Set.mem_Ici.mpr hpos.le))
    ((po_U E i (d i) - po_U E i ci) / po_w E h) (div_pos (by linarith) hw)
  set ε := min (δ / 2) a with hε
  have hε0 : 0 < ε := lt_min (by linarith) hpos
  have hεa : ε ≤ a := min_le_right _ _
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set t : ι → ℝ := fun k => (if k = j then ε else 0) - (if k = i then ε else 0) with ht
  have hti : t i = -ε := by simp [ht, hij]
  have htj : t j = ε := by simp [ht, hij.symm]
  have hto : ∀ k, k ≠ i → k ≠ j → t k = 0 := fun k hki hkj => by simp [ht, hki, hkj]
  have hsum : ∑ k, t k = 0 := by
    simp only [ht, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      sub_self]
  have hnn : ∀ k, 0 ≤ d k h + t k := by
    intro k
    by_cases hki : k = i
    · subst hki; rw [hti]; linarith
    by_cases hkj : k = j
    · subst hkj; rw [htj]; linarith [(hd.1 k).1 h]
    · rw [hto k hki hkj, add_zero]; exact (hd.1 k).1 h
  refine ⟨po_perturb d h t, po_perturb_feasible hd h t hsum hnn, ?_, ?_, ?_⟩
  · simp only [po_perturb]
    rw [po_U_update E i (hd.1 i) h, hti]
    have hdist := hδu (Set.mem_Ici.mpr (by linarith : 0 ≤ a + -ε))
      (by rw [Real.dist_eq]; rw [show a + -ε - a = -ε by ring, abs_neg, abs_of_pos hε0];
          exact hεδ)
    rw [Real.dist_eq, abs_lt] at hdist
    have h1 : po_w E h * (E.u i a - E.u i (a + -ε)) < po_U E i (d i) - po_U E i ci := by
      have := (lt_div_iff₀' hw).mp (by linarith [hdist.1] :
        E.u i a - E.u i (a + -ε) < (po_U E i (d i) - po_U E i ci) / po_w E h)
      linarith
    nlinarith
  · simp only [po_perturb]
    rw [po_U_update E j (hd.1 j) h, htj]
    have : E.u j (d j h) < E.u j (d j h + ε) :=
      E.u_mono j (Set.mem_Ici.mpr ((hd.1 j).1 h)) (Set.mem_Ici.mpr (by linarith [(hd.1 j).1 h]))
        (by linarith)
    nlinarith
  · intro k hki hkj
    simp only [po_perturb]
    rw [hto k hki hkj, add_zero, Function.update_eq_self]

/-- Miao, proof of Proposition 13.2.1, p. 417 ("only if" part): a Pareto optimal allocation solves
the planner's problem for some nonzero `λ ≥ 0`. The set `𝒰 = {U(x) − U(c) − z}` is convex and
misses the open positive orthant; a separating functional gives `λ`. -/
theorem po_planner_of_pareto {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι]
    (E : POEconomy ι S) (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i))
    {y c : ι → List S → ℝ} (hpo : po_ParetoOptimal E y c) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧ po_SolvesPlanner E y lam c := by
  classical
  set A : Set (ι → ℝ) := {v | ∃ x, po_Feasible y x ∧ ∀ i, v i ≤ po_U E i (x i) - po_U E i (c i)}
    with hA
  set Pos : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ioi 0 with hPos
  have hPosOpen : IsOpen Pos := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  have hPosConv : Convex ℝ Pos := convex_pi fun _ _ => convex_Ioi 0
  have hAconv : Convex ℝ A := by
    rintro v ⟨x, hx, hvx⟩ v' ⟨x', hx', hvx'⟩ a b ha hb hab
    refine ⟨fun i h => a * x i h + b * x' i h,
      ⟨fun i => po_Lplus_comb (hx.1 i) (hx'.1 i) ha hb, fun h => ?_⟩, fun i => ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hx'.2]
      rw [← add_mul, hab, one_mul]
    · have hcv := po_U_concave E i (hconc i) (hx.1 i) (hx'.1 i) ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hvx i) ha
      have h2 := mul_le_mul_of_nonneg_left (hvx' i) hb
      have hab' : a * po_U E i (c i) + b * po_U E i (c i) = po_U E i (c i) := by
        rw [← add_mul, hab, one_mul]
      linarith
  have hdisj : Disjoint Pos A := by
    rw [Set.disjoint_left]
    rintro v hv ⟨x, hx, hvx⟩
    apply hpo.2
    have hgt : ∀ i, po_U E i (c i) < po_U E i (x i) := fun i => by
      have := hv i (Set.mem_univ _)
      have := hvx i
      simp only [Set.mem_Ioi] at *
      linarith
    exact ⟨x, hx, fun i => (hgt i).le, Classical.arbitrary ι, hgt _⟩
  obtain ⟨f, u, hfPos, hfA⟩ := geometric_hahn_banach_open hPosConv hPosOpen hAconv hdisj
  set lam : ι → ℝ := fun i => -f (Pi.single i 1) with hlamdef
  have hf : ∀ v : ι → ℝ, f v = -∑ i, v i * lam i := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    simp only [hlamdef, mul_neg, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (v i) = v i • (Pi.single i 1 : ι → ℝ) by
      ext k; by_cases hk : k = i <;> simp [hk], map_smul, smul_eq_mul]
  have h0A : (0 : ι → ℝ) ∈ A := ⟨c, hpo.1, fun i => by simp⟩
  have hu0 : u ≤ 0 := by simpa using hfA 0 h0A
  have hone : (fun _ => (1 : ℝ)) ∈ Pos := fun _ _ => Set.mem_Ioi.mpr one_pos
  have hf1 : f (fun _ => 1) < u := hfPos _ hone
  have hu : 0 ≤ u := by
    by_contra hneg
    push Not at hneg
    have hf1neg : f (fun _ => 1) < 0 := lt_of_lt_of_le hf1 hu0
    set s := u / f (fun _ => 1) / 2
    have hs : 0 < s := by
      have : 0 < u / f (fun _ => 1) := div_pos_of_neg_of_neg hneg hf1neg
      positivity
    have hmem : (fun _ => s) ∈ Pos := fun _ _ => Set.mem_Ioi.mpr hs
    have h2 := hfPos _ hmem
    have : f (fun _ => s) = s * f (fun _ => 1) := by
      rw [show (fun _ : ι => s) = s • (fun _ : ι => (1 : ℝ)) by funext; simp, map_smul,
        smul_eq_mul]
    rw [this] at h2
    have : s * f (fun _ => 1) = u / 2 := by
      have hne : f (fun _ => 1) ≠ 0 := hf1neg.ne
      simp only [s]
      field_simp
    linarith
  refine ⟨lam, fun i => ?_, ?_, hpo.1, fun x hx => ?_⟩
  · have hmem : (-(Pi.single i 1 : ι → ℝ)) ∈ A := ⟨c, hpo.1, fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]⟩
    have := hfA _ hmem
    rw [map_neg] at this
    simp only [hlamdef]
    linarith
  · intro hz
    have := hf (fun _ => 1)
    rw [hz] at this
    simp at this
    linarith
  · have hmem : (fun i => po_U E i (x i) - po_U E i (c i)) ∈ A := ⟨x, hx, fun _ => le_rfl⟩
    have h1 := hfA _ hmem
    rw [hf] at h1
    have h2 : ∑ i, (po_U E i (x i) - po_U E i (c i)) * lam i ≤ 0 := by linarith
    simp only [sub_mul, Finset.sum_sub_distrib] at h2
    simp only [mul_comm (lam _)]
    linarith

/-- **Proposition 13.2.1** (Miao, p. 417). An allocation is Pareto optimal iff it solves the
social planner's problem for some nonzero weight `λ ∈ ℝᴵ₊`. Hypotheses (from Assumption 13.1.1):
each `uⁱ` is concave and continuous on `[0, ∞)`; there is at least one agent. -/
theorem proposition_13_2_1 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι]
    (E : POEconomy ι S) (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i))
    (hcont : ∀ i, ContinuousOn (E.u i) (Set.Ici 0)) (y c : ι → List S → ℝ) :
    po_ParetoOptimal E y c ↔
      ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧ po_SolvesPlanner E y lam c := by
  classical
  refine ⟨po_planner_of_pareto E hconc, ?_⟩
  rintro ⟨lam, hlam, hne, hc⟩
  refine ⟨hc.1, ?_⟩
  rintro ⟨d, hd, hle, i, hi⟩
  by_cases hli : 0 < lam i
  · exact po_planner_improvement E hlam hc hd hle ⟨i, hli, hi⟩
  have hli0 : lam i = 0 := le_antisymm (not_lt.mp hli) (hlam i)
  obtain ⟨j, hj⟩ : ∃ j, lam j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hjpos : 0 < lam j := lt_of_le_of_ne (hlam j) (Ne.symm hj)
  have hij : i ≠ j := fun h => hj (h ▸ hli0)
  obtain ⟨d', hd', hi', hj', hk'⟩ := po_transfer_improvement E hd hij (hcont i) (hc.1.1 i) hi
  refine po_planner_improvement E hlam hc hd' (fun k => ?_) ⟨j, hjpos, ?_⟩
  · by_cases hki : k = i
    · subst hki; exact hi'
    by_cases hkj : k = j
    · subst hkj; exact (hle k).trans hj'.le
    · rw [hk' k hki hkj]; exact hle k
  · exact (hle j).trans_lt hj'

/-- Miao, §13.2, p. 418 ("Using first-order conditions"): at a solution of the planner's
problem, for two agents `i ≠ j` with interior consumption at node `h`,
`βᵗ Pr(h) (λⁱ uⁱ'(cⁱ(h)) − λʲ uʲ'(cʲ(h))) = 0`. Derived by transferring `ε` units from `j` to
`i` at `h`: the planner's objective is maximal at `ε = 0`. -/
theorem po_planner_foc {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) {i j : ι} (hij : i ≠ j) (h : List S)
    (hi : 0 < c i h) (hj : 0 < c j h) (hdi : DifferentiableAt ℝ (E.u i) (c i h))
    (hdj : DifferentiableAt ℝ (E.u j) (c j h)) :
    po_w E h * (lam i * deriv (E.u i) (c i h) - lam j * deriv (E.u j) (c j h)) = 0 := by
  classical
  rcases (po_w_nonneg E h).lt_or_eq with hw | hw
  swap
  · rw [← hw, zero_mul]
  set φ : ℝ → ℝ := fun e => lam i * E.u i (c i h + e) + lam j * E.u j (c j h - e) with hφ
  have hmax : IsLocalMax φ 0 := by
    have hnhds : Set.Ioo (-min (c i h) (c j h)) (min (c i h) (c j h)) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by simp [hi, hj]) (lt_min hi hj)
    filter_upwards [hnhds] with e he
    obtain ⟨he1, he2⟩ := he
    have hmi := min_le_left (c i h) (c j h)
    have hmj := min_le_right (c i h) (c j h)
    set t : ι → ℝ := fun k => (if k = i then e else 0) - (if k = j then e else 0) with ht
    have hti : t i = e := by simp [ht, hij]
    have htj : t j = -e := by simp [ht, hij.symm]
    have hto : ∀ k, k ≠ i ∧ k ≠ j → t k = 0 := fun k hk => by simp [ht, hk.1, hk.2]
    have hsum : ∑ k, t k = 0 := by
      simp only [ht, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        sub_self]
    have hnn : ∀ k, 0 ≤ c k h + t k := by
      intro k
      by_cases hki : k = i
      · subst hki; rw [hti]; linarith
      by_cases hkj : k = j
      · subst hkj; rw [htj]; linarith
      · rw [hto k ⟨hki, hkj⟩, add_zero]; exact (hc.1.1 k).1 h
    have hopt := hc.2 _ (po_perturb_feasible hc.1 h t hsum hnn)
    simp only [po_perturb] at hopt
    simp only [po_U_update E _ (hc.1.1 _) h, mul_add, Finset.sum_add_distrib] at hopt
    have hcol : ∑ k, lam k * (po_w E h * (E.u k (c k h + t k) - E.u k (c k h))) =
        po_w E h * (φ e - φ 0) := by
      rw [Fintype.sum_eq_add i j hij (fun k hk => by rw [hto k hk, add_zero, sub_self,
        mul_zero, mul_zero]), hti, htj]
      simp only [hφ, add_zero, sub_zero, ← sub_eq_add_neg]
      ring
    rw [hcol] at hopt
    have : po_w E h * (φ e - φ 0) ≤ 0 := by linarith
    have := nonpos_of_mul_nonpos_right this hw
    linarith
  have hderiv : HasDerivAt φ (lam i * deriv (E.u i) (c i h) - lam j * deriv (E.u j) (c j h)) 0 := by
    have h1 : HasDerivAt (fun e => E.u i (c i h + e)) (deriv (E.u i) (c i h)) 0 := by
      exact HasDerivAt.comp_const_add (c i h) 0 (by simpa using hdi.hasDerivAt)
    have h2 : HasDerivAt (fun e => E.u j (c j h - e)) (-deriv (E.u j) (c j h)) 0 := by
      exact HasDerivAt.comp_const_sub (c j h) 0 (by simpa using hdj.hasDerivAt)
    have := (h1.const_mul (lam i)).add (h2.const_mul (lam j))
    convert this using 1
    ring
  rw [hmax.hasDerivAt_eq_zero hderiv, mul_zero]

/-- Miao, §13.2, p. 418: the first-order condition `uⁱ'(cⁱ_t) / uʲ'(cʲ_t) = λʲ / λⁱ` at a node of
positive probability, in multiplied-out form `λⁱ uⁱ'(cⁱ_t) = λʲ uʲ'(cʲ_t)` (all agents,
interior consumption). -/
theorem po_planner_foc_ratio {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) (h : List S) (hw : 0 < po_w E h)
    (hpos : ∀ k, 0 < c k h) (hdiff : ∀ k, DifferentiableAt ℝ (E.u k) (c k h)) (i j : ι) :
    lam i * deriv (E.u i) (c i h) = lam j * deriv (E.u j) (c j h) := by
  by_cases hij : i = j
  · rw [hij]
  have := po_planner_foc E hc hij h (hpos i) (hpos j) (hdiff i) (hdiff j)
  have := (mul_eq_zero.mp this).resolve_left hw.ne'
  linarith

/-- Miao, (13.3), p. 418: `cⁱ_t(sᵗ) = (uⁱ')⁻¹(λᵢ⁻¹ λ₁ u¹'(c¹_t(sᵗ)))`, with `(uⁱ')⁻¹` the inverse
of the marginal utility on `(0, ∞)` (which exists when `uⁱ'` is injective there, e.g. under
Assumption 13.1.1 by `po_strictAntiOn_deriv`). Also the equivalent
`uⁱ'(cⁱ_t) = λᵢ⁻¹ λ₁ u¹'(c¹_t)`. -/
theorem eq_13_3 {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) (hlam : ∀ i, 0 < lam i) (h : List S) (hw : 0 < po_w E h)
    (hpos : ∀ k, 0 < c k h) (hdiff : ∀ k, DifferentiableAt ℝ (E.u k) (c k h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) (i i₁ : ι) :
    deriv (E.u i) (c i h) = (lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h) ∧
      c i h = Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
        ((lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h)) := by
  have hfoc := po_planner_foc_ratio E hc h hw hpos hdiff i i₁
  have h1 : deriv (E.u i) (c i h) = (lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h) := by
    rw [mul_assoc, ← hfoc, ← mul_assoc, inv_mul_cancel₀ (hlam i).ne', one_mul]
  refine ⟨h1, ?_⟩
  have hex : ∃ a ∈ Set.Ioi (0 : ℝ), deriv (E.u i) a =
      (lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h) := ⟨c i h, hpos i, h1⟩
  exact hinj i (hpos i) (Function.invFunOn_mem hex) (h1.trans (Function.invFunOn_eq hex).symm)

/-- Miao, (13.4), p. 418: substituting (13.3) into (13.2),
`Σᵢ (uⁱ')⁻¹(λᵢ⁻¹ λ₁ u¹'(c¹_t(sᵗ))) = Σᵢ yⁱ_t(sᵗ)`, one equation in `c¹_t(sᵗ)`. -/
theorem eq_13_4 {ι S : Type*} [Fintype ι] [Fintype S]
    (E : POEconomy ι S) {y : ι → List S → ℝ} {lam : ι → ℝ} {c : ι → List S → ℝ}
    (hc : po_SolvesPlanner E y lam c) (hlam : ∀ i, 0 < lam i) (h : List S) (hw : 0 < po_w E h)
    (hpos : ∀ k, 0 < c k h) (hdiff : ∀ k, DifferentiableAt ℝ (E.u k) (c k h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) (i₁ : ι) :
    ∑ i, Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
        ((lam i)⁻¹ * lam i₁ * deriv (E.u i₁) (c i₁ h)) = ∑ i, y i h := by
  rw [← hc.1.2 h]
  exact Finset.sum_congr rfl fun i _ =>
    (eq_13_3 E hc hlam h hw hpos hdiff hinj i i₁).2.symm

/-- Miao, Assumption 13.1.1: the felicity function is differentiable at every positive
consumption level. -/
theorem po_differentiableAt {u : ℝ → ℝ} (hu : Assumption13_1_1 u) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ u x :=
  ((hu.2.2.1.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)

/-- Miao, Assumption 13.1.1: marginal utility is strictly decreasing on `(0, ∞)`, so `uⁱ'` is
invertible there, as (13.3) requires. -/
theorem po_strictAntiOn_deriv {u : ℝ → ℝ} (hu : Assumption13_1_1 u) :
    StrictAntiOn (deriv u) (Set.Ioi 0) :=
  (hu.2.2.2.1.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun _ hx => po_differentiableAt hu hx

/-- Miao, §13.2, p. 418 ("It shows that `c¹_t(sᵗ)` is a function of the aggregate endowment
only. As a result … any agent's consumption is also a function of the aggregate endowment
only"): if the planner's first-order conditions hold with positive weights at all nodes of
positive probability and marginal utilities are strictly decreasing, two such nodes with the
same aggregate endowment give every agent the same consumption. -/
theorem po_risk_sharing {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y c : ι → List S → ℝ} {lam : ι → ℝ} (hc : po_Feasible y c) (hlam : ∀ i, 0 < lam i)
    (hanti : ∀ i, StrictAntiOn (deriv (E.u i)) (Set.Ioi 0)) (hpos : ∀ i h, 0 < c i h)
    (hfoc : ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) =
      lam j * deriv (E.u j) (c j h))
    {h h' : List S} (hw : 0 < po_w E h) (hw' : 0 < po_w E h')
    (hy : ∑ i, y i h = ∑ i, y i h') (i : ι) : c i h = c i h' := by
  have key : ∀ g g', 0 < po_w E g → 0 < po_w E g' → c i g < c i g' →
      ∑ k, c k g < ∑ k, c k g' := by
    intro g g' hg hg' hlt
    have hd : deriv (E.u i) (c i g') < deriv (E.u i) (c i g) :=
      hanti i (hpos i g) (hpos i g') hlt
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨i, Finset.mem_univ _, hlt⟩
    have hk : deriv (E.u k) (c k g') < deriv (E.u k) (c k g) := by
      have e1 := hfoc g hg k i
      have e2 := hfoc g' hg' k i
      have : lam k * deriv (E.u k) (c k g') < lam k * deriv (E.u k) (c k g) := by
        rw [e1, e2]; exact mul_lt_mul_of_pos_left hd (hlam i)
      exact lt_of_mul_lt_mul_left this (hlam k).le
    refine le_of_lt (lt_of_not_ge fun hge => ?_)
    rcases hge.lt_or_eq with hlt' | heq
    · exact absurd (hanti k (hpos k g') (hpos k g) hlt') (not_lt.mpr hk.le)
    · rw [heq] at hk; exact lt_irrefl _ hk
  rcases lt_trichotomy (c i h) (c i h') with hlt | heq | hgt
  · have := key h h' hw hw' hlt
    rw [hc.2, hc.2, hy] at this
    exact absurd this (lt_irrefl _)
  · exact heq
  · have := key h' h hw' hw hgt
    rw [hc.2, hc.2, hy] at this
    exact absurd this (lt_irrefl _)

/-- Miao, §13.2, p. 418: under the hypotheses of `po_risk_sharing`, each agent's consumption is a
function `gᵢ` of the aggregate endowment `ȳ_t(sᵗ)` at the nodes of positive probability. -/
theorem po_consumption_fn_aggregate {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y c : ι → List S → ℝ} {lam : ι → ℝ} (hc : po_Feasible y c) (hlam : ∀ i, 0 < lam i)
    (hanti : ∀ i, StrictAntiOn (deriv (E.u i)) (Set.Ioi 0)) (hpos : ∀ i h, 0 < c i h)
    (hfoc : ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) =
      lam j * deriv (E.u j) (c j h)) :
    ∃ g : ι → ℝ → ℝ, ∀ i h, 0 < po_w E h → c i h = g i (∑ k, y k h) := by
  classical
  refine ⟨fun i a => if hx : ∃ h, 0 < po_w E h ∧ ∑ k, y k h = a then c i hx.choose else 0,
    fun i h hw => ?_⟩
  have hx : ∃ h', 0 < po_w E h' ∧ ∑ k, y k h' = ∑ k, y k h := ⟨h, hw, rfl⟩
  simp only [hx, ↓reduceDIte]
  exact po_risk_sharing E hc hlam hanti hpos hfoc hw hx.choose_spec.1 hx.choose_spec.2.symm i

/-- Miao, §13.2, p. 418 ("If the aggregate endowment is determined by an aggregate Markov state
variable, then individual consumption is a function of the state only. There is no history
dependence"): if `ȳ_t(sᵗ) = Y(z(sᵗ))` for a state `z(sᵗ)`, then `cⁱ_t(sᵗ) = Gᵢ(z(sᵗ))`. -/
theorem po_no_history_dependence {ι S Z : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y c : ι → List S → ℝ} {lam : ι → ℝ} (hc : po_Feasible y c) (hlam : ∀ i, 0 < lam i)
    (hanti : ∀ i, StrictAntiOn (deriv (E.u i)) (Set.Ioi 0)) (hpos : ∀ i h, 0 < c i h)
    (hfoc : ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) =
      lam j * deriv (E.u j) (c j h))
    (z : List S → Z) (Y : Z → ℝ) (hY : ∀ h, ∑ k, y k h = Y (z h)) :
    ∃ G : ι → Z → ℝ, ∀ i h, 0 < po_w E h → c i h = G i (z h) := by
  obtain ⟨g, hg⟩ := po_consumption_fn_aggregate E hc hlam hanti hpos hfoc
  exact ⟨fun i s => g i (Y s), fun i h hw => by rw [hg i h hw, hY]⟩

end Miao.CompleteMarkets
