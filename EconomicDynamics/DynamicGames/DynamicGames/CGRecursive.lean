/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.CGRepeated

/-!
# Recursive strategies

Miao, §21.4.5, pp. 769–771: strategies that use a state `v` (the promised continuation value) with
`x_t = zʰ(v_t)`, `y_t = zᵍ(v_t)`, `v_{t+1} = V(v_t, x_t, y_t)` (Definition 21.4.5), the trigger
strategy (Example 21.4.5) and the stick-and-carrot strategy (Example 21.4.6). The state map is
`Vf` here, since `V` names the SPE value set.

* `cg_recStrat zh zg Vf v` is the profile of a recursive strategy started at `v`; after a history
  it is the recursive strategy started at the state reached (`cg_recStrat_cont`), and its outcome
  path obeys the recursion of Definition 21.4.5 (`definition_21_4_5`).
* `cg_recStrat_value`: if the states move inside a bounded set `S` and satisfy promise keeping
  `s = (1 − δ) r(zʰ(s), zᵍ(s)) + δ V(s, zʰ(s), zᵍ(s))` on `S`, the state is the value.
* `cg_recursive_spe`: the corrected "if" half of the characterisation on p. 770. The book states
  conditions (i)–(iii) at the initial state only, and (ii) only for `V(v, zʰ(v), y)`; they must
  hold at every state of an invariant set, which must also be closed under the household-side
  deviations `V(s, ξ, η)` (every history is a subgame). The printed version is refuted in
  `CGExamples` (`cg_definition_21_4_5_counterexample`). The "only if" half holds as printed when
  states are promised values (`cg_recursive_spe_only_if`).
* `example_21_4_5`: the trigger strategy is an SPE with value `v^b` under the incentive constraint
  `(1 − δ) r(x^b, y') + δ v^N ≤ v^b`. The book's hypothesis `v^b > v^N` is neither sufficient
  (refuted in `CGExamples`) nor needed.
* `example_21_4_6`: the stick-and-carrot strategy is an SPE with value `ṽ`; besides the book's
  condition `ṽ ≥ (1 − δ) r(x*, y') + δṽ` it needs the carrot's own incentive constraint
  `v^R ≥ (1 − δ) r(x^R, y') + δṽ`, which the book omits (refuted in `CGExamples`).
-/

open Filter Topology

namespace Miao.DynamicGames

variable {X Y : Type*}

/-- The state reached after a history, from the initial state `v`. -/
def cg_recState (Vf : ℝ → X → Y → ℝ) (v : ℝ) (h : List (X × Y)) : ℝ :=
  h.foldl (fun s q => Vf s q.1 q.2) v

/-- The profile of the recursive strategy `(φ, v)` with `φ = (zʰ, zᵍ, V)` (Definition 21.4.5). -/
def cg_recStrat (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ) : CGProfile X Y :=
  fun h => (zh (cg_recState Vf v h), zg (cg_recState Vf v h))

theorem cg_recStrat_cont (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ)
    (h : List (X × Y)) :
    cg_cont (cg_recStrat zh zg Vf v) h = cg_recStrat zh zg Vf (cg_recState Vf v h) := by
  funext k
  simp [cg_cont, cg_recStrat, cg_recState, List.foldl_append]

theorem cg_recStrat_cont_single (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ)
    (q : X × Y) : cg_cont (cg_recStrat zh zg Vf v) [q] = cg_recStrat zh zg Vf (Vf v q.1 q.2) :=
  cg_recStrat_cont zh zg Vf v [q]

theorem cg_recState_mem {Vf : ℝ → X → Y → ℝ} {S : Set ℝ} (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (h : List (X × Y)) : ∀ v ∈ S, cg_recState Vf v h ∈ S := by
  induction h with
  | nil => exact fun v hv => hv
  | cons q h ih =>
    intro v hv
    exact ih _ (hinv v hv q.1 q.2)

/-- The state sequence `v_1 = v`, `v_{t+1} = V(v_t, zʰ(v_t), zᵍ(v_t))` (indexed from `0`). -/
def cg_recSeq (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) : ℝ → ℕ → ℝ
  | v, 0 => v
  | v, n + 1 => cg_recSeq zh zg Vf (Vf v (zh v) (zg v)) n

/-- **Definition 21.4.5** (recursive strategies, Miao, p. 769): the outcome path of `(φ, v)` is
`x_t = zʰ(v_t)`, `y_t = zᵍ(v_t)` with `v_1 = v` and `v_{t+1} = V(v_t, x_t, y_t)`. -/
theorem definition_21_4_5 (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ) (n : ℕ) :
    cg_path (cg_recStrat zh zg Vf v) n =
        (zh (cg_recSeq zh zg Vf v n), zg (cg_recSeq zh zg Vf v n)) ∧
      cg_recSeq zh zg Vf v 0 = v ∧
      cg_recSeq zh zg Vf v (n + 1) = Vf (cg_recSeq zh zg Vf v n)
        (zh (cg_recSeq zh zg Vf v n)) (zg (cg_recSeq zh zg Vf v n)) := by
  refine ⟨?_, rfl, ?_⟩
  · induction n generalizing v with
    | zero => rfl
    | succ n ih =>
      have e : cg_cont (cg_recStrat zh zg Vf v) [cg_recStrat zh zg Vf v []] =
          cg_recStrat zh zg Vf (Vf v (zh v) (zg v)) :=
        cg_recStrat_cont_single zh zg Vf v _
      have : cg_path (cg_recStrat zh zg Vf v) (n + 1) =
          cg_path (cg_recStrat zh zg Vf (Vf v (zh v) (zg v))) n := by
        rw [← e]; rfl
      rw [this, ih]
      rfl
  · induction n generalizing v with
    | zero => rfl
    | succ n ih => exact ih _

/-- Under promise keeping on a bounded invariant set `S`, the state of a recursive strategy is its
value: `Uᵍ(σ_s) = s` for `s ∈ S`. -/
theorem cg_recStrat_value {δ M K : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {zh : ℝ → X} {zg : ℝ → Y} {Vf : ℝ → X → Y → ℝ} {S : Set ℝ}
    (hK : ∀ s ∈ S, |s| ≤ K) (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (hpk : ∀ s ∈ S, (1 - δ) * r (zh s) (zg s) + δ * Vf s (zh s) (zg s) = s) :
    ∀ s ∈ S, cg_U δ r (cg_recStrat zh zg Vf s) = s := by
  have hrec : ∀ s, cg_U δ r (cg_recStrat zh zg Vf s) = (1 - δ) * r (zh s) (zg s) +
      δ * cg_U δ r (cg_recStrat zh zg Vf (Vf s (zh s) (zg s))) := fun s => by
    rw [cg_U_rec hδ0 hδ1 hM, cg_recStrat_cont_single]
    rfl
  have key : ∀ n : ℕ, ∀ s ∈ S, |cg_U δ r (cg_recStrat zh zg Vf s) - s| ≤ δ ^ n * (M + K) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h1 := cg_abs_U_le hδ0 hδ1 hM (cg_recStrat zh zg Vf s)
      have h2 := hK s hs
      simp only [pow_zero, one_mul]
      calc |cg_U δ r (cg_recStrat zh zg Vf s) - s| ≤ |cg_U δ r (cg_recStrat zh zg Vf s)| + |s| :=
            abs_sub _ _
        _ ≤ M + K := add_le_add h1 h2
    | succ n ih =>
      intro s hs
      have hs' := hinv s hs (zh s) (zg s)
      have e : cg_U δ r (cg_recStrat zh zg Vf s) - s =
          δ * (cg_U δ r (cg_recStrat zh zg Vf (Vf s (zh s) (zg s))) - Vf s (zh s) (zg s)) := by
        rw [hrec s]
        have := hpk s hs
        linarith
      rw [e, abs_mul, abs_of_nonneg hδ0]
      calc δ * |cg_U δ r (cg_recStrat zh zg Vf (Vf s (zh s) (zg s))) - Vf s (zh s) (zg s)|
          ≤ δ * (δ ^ n * (M + K)) := mul_le_mul_of_nonneg_left (ih _ hs') hδ0
        _ = δ ^ (n + 1) * (M + K) := by ring
  intro s hs
  have ht : Tendsto (fun n : ℕ => δ ^ n * (M + K)) atTop (𝓝 (0 * (M + K))) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _
  have := ge_of_tendsto' ht (fun n => key n s hs)
  rw [zero_mul] at this
  have := abs_nonpos_iff.1 this
  linarith

/-- Miao, p. 770, "if" half of the SPE characterisation of recursive strategies, corrected: if on
a bounded set `S` of states, closed under every `V(s, ξ, η)`, (i) `(zʰ(s), zᵍ(s)) ∈ C`, promise
keeping holds and (iii) `(1 − δ) r(zʰ(s), y) + δ V(s, zʰ(s), y) ≤ s` for all `y`, then from every
`v ∈ S` the recursive strategy is an SPE with value `v`. -/
theorem cg_recursive_spe {δ M K : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {zh : ℝ → X} {zg : ℝ → Y} {Vf : ℝ → X → Y → ℝ}
    {S : Set ℝ} (hK : ∀ s ∈ S, |s| ≤ K) (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (hpk : ∀ s ∈ S, (1 - δ) * r (zh s) (zg s) + δ * Vf s (zh s) (zg s) = s)
    (hC : ∀ s ∈ S, (zh s, zg s) ∈ C)
    (hIC : ∀ s ∈ S, ∀ y', (1 - δ) * r (zh s) y' + δ * Vf s (zh s) y' ≤ s) :
    ∀ v ∈ S, cg_IsSPE δ r C (cg_recStrat zh zg Vf v) ∧ cg_U δ r (cg_recStrat zh zg Vf v) = v := by
  have hval := cg_recStrat_value hδ0 hδ1 hM hK hinv hpk
  intro v hv
  refine ⟨?_, hval v hv⟩
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  intro h
  rw [cg_recStrat_cont]
  set s := cg_recState Vf v h
  have hs : s ∈ S := cg_recState_mem hinv h v hv
  refine ⟨hC s hs, fun η => ?_⟩
  have e : cg_recStrat zh zg Vf s [] = (zh s, zg s) := rfl
  rw [e, cg_recStrat_cont_single, hval s hs, hval _ (hinv s hs _ _)]
  exact hIC s hs η

/-- Miao, p. 770, "only if" half: if the states of a recursive strategy are promised values
(promise keeping on a bounded invariant `S ∋ v`) and `(φ, v)` is an SPE, then `v ∈ V`,
(i) `(zʰ(v), zᵍ(v)) ∈ C`, (ii) every `V(v, ξ, η) ∈ V` and (iii) the incentive constraint holds. -/
theorem cg_recursive_spe_only_if {δ M K : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {zh : ℝ → X} {zg : ℝ → Y} {Vf : ℝ → X → Y → ℝ}
    {S : Set ℝ} (hK : ∀ s ∈ S, |s| ≤ K) (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (hpk : ∀ s ∈ S, (1 - δ) * r (zh s) (zg s) + δ * Vf s (zh s) (zg s) = s) {v : ℝ}
    (hv : v ∈ S) (hspe : cg_IsSPE δ r C (cg_recStrat zh zg Vf v)) :
    v ∈ cg_V δ r C ∧ (zh v, zg v) ∈ C ∧ (∀ ξ η, Vf v ξ η ∈ cg_V δ r C) ∧
      ∀ y', (1 - δ) * r (zh v) y' + δ * Vf v (zh v) y' ≤ v := by
  have hval := cg_recStrat_value hδ0 hδ1 hM hK hinv hpk
  refine ⟨⟨_, hspe, hval v hv⟩, (hspe []).1, fun ξ η => ?_, fun y' => ?_⟩
  · refine ⟨_, hspe.cont hδ0 hδ1 hM [(ξ, η)], ?_⟩
    rw [cg_recStrat_cont_single]
    exact hval _ (hinv v hv ξ η)
  · have := (hspe.root hδ0 hδ1 hM).2 y'
    have e : cg_recStrat zh zg Vf v [] = (zh v, zg v) := rfl
    rw [e, cg_recStrat_cont_single, hval _ (hinv v hv _ _), hval v hv] at this
    exact this

open Classical in
/-- The household rule of the trigger strategy (Example 21.4.5). -/
noncomputable def cg_trigZh (vb : ℝ) (xb xN : X) : ℝ → X := fun v => if v = vb then xb else xN

open Classical in
/-- The government rule of the trigger strategy (Example 21.4.5). -/
noncomputable def cg_trigZg (vb : ℝ) (yb yN : Y) : ℝ → Y := fun v => if v = vb then yb else yN

open Classical in
/-- The state map of the trigger strategy (Example 21.4.5): `v^b` after `(v^b, x^b, y^b)`,
`v^N` otherwise. -/
noncomputable def cg_trigV (vb vN : ℝ) (xb : X) (yb : Y) : ℝ → X → Y → ℝ :=
  fun v x y => if v = vb ∧ x = xb ∧ y = yb then vb else vN

/-- The trigger strategy keeps its promises: on `{v^b, v^N}` the state is the value. -/
theorem cg_trigger_value {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (xb xN : X) (yb yN : Y) :
    ∀ s ∈ ({r xb yb, r xN yN} : Set ℝ), cg_U δ r (cg_recStrat (cg_trigZh (r xb yb) xb xN)
      (cg_trigZg (r xb yb) yb yN) (cg_trigV (r xb yb) (r xN yN) xb yb) s) = s := by
  classical
  refine cg_recStrat_value (K := |r xb yb| + |r xN yN|) hδ0 hδ1 hM ?_ ?_ ?_
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg (r xN yN)]
    · linarith [abs_nonneg (r xb yb)]
  · intro s _ ξ η
    unfold cg_trigV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    by_cases h : s = r xb yb
    · subst h
      simp [cg_trigZh, cg_trigZg, cg_trigV]
      ring
    · have hs' : s = r xN yN := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_trigZh, cg_trigZg, cg_trigV, h, false_and, ↓reduceIte]
      rw [← hs']
      ring

/-- **Example 21.4.5** (trigger strategy, Miao, p. 770), corrected. With a one-period Nash
equilibrium `(x^N, y^N)` and a competitive `(x^b, y^b)` satisfying the incentive constraint
`(1 − δ) r(x^b, y') + δ v^N ≤ v^b` for all `y'`, the trigger strategy (play `(x^b, y^b)` while the
state is `v^b`, revert to the Nash state `v^N` forever after any deviation) is an SPE with value
`v^b = r(x^b, y^b)`. The book assumes only `v^b > v^N`, which does not suffice
(`cg_example_21_4_5_counterexample`). -/
theorem example_21_4_5 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xb xN : X} {yb yN : Y} (hb : (xb, yb) ∈ C)
    (hN : (xN, yN) ∈ C) (hNash : ∀ y', r xN y' ≤ r xN yN)
    (hIC : ∀ y', (1 - δ) * r xb y' + δ * r xN yN ≤ r xb yb) :
    cg_IsSPE δ r C (cg_recStrat (cg_trigZh (r xb yb) xb xN) (cg_trigZg (r xb yb) yb yN)
        (cg_trigV (r xb yb) (r xN yN) xb yb) (r xb yb)) ∧
      cg_U δ r (cg_recStrat (cg_trigZh (r xb yb) xb xN) (cg_trigZg (r xb yb) yb yN)
        (cg_trigV (r xb yb) (r xN yN) xb yb) (r xb yb)) = r xb yb := by
  classical
  have h1 : 0 ≤ 1 - δ := by linarith
  refine cg_recursive_spe (K := |r xb yb| + |r xN yN|) (S := {r xb yb, r xN yN}) hδ0 hδ1 hM
    ?_ ?_ ?_ ?_ ?_ (r xb yb) (Or.inl rfl)
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg (r xN yN)]
    · linarith [abs_nonneg (r xb yb)]
  · intro s _ ξ η
    unfold cg_trigV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    by_cases h : s = r xb yb
    · subst h
      simp [cg_trigZh, cg_trigZg, cg_trigV]
      ring
    · have hs' : s = r xN yN := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_trigZh, cg_trigZg, cg_trigV, h, false_and, ↓reduceIte]
      rw [← hs']
      ring
  · intro s _
    by_cases h : s = r xb yb
    · simp only [cg_trigZh, cg_trigZg, h, ↓reduceIte]; exact hb
    · simp only [cg_trigZh, cg_trigZg, h, ↓reduceIte]; exact hN
  · intro s hs y'
    by_cases h : s = r xb yb
    · subst h
      by_cases hy : y' = yb
      · subst hy
        simp only [cg_trigZh, cg_trigV, and_self, ↓reduceIte]
        linarith
      · simp only [cg_trigZh, cg_trigV, hy, and_false, ↓reduceIte]
        exact hIC y'
    · have hs' : s = r xN yN := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_trigZh, cg_trigV, h, false_and, ↓reduceIte, ↓reduceIte]
      rw [hs']
      nlinarith [hNash y']

open Classical in
/-- The household rule of the stick-and-carrot strategy (Example 21.4.6). -/
noncomputable def cg_scZh (vR : ℝ) (xR xs : X) : ℝ → X := fun v => if v = vR then xR else xs

open Classical in
/-- The government rule of the stick-and-carrot strategy (Example 21.4.6). -/
noncomputable def cg_scZg (vR : ℝ) (yR ys : Y) : ℝ → Y := fun v => if v = vR then yR else ys

open Classical in
/-- The state map of the stick-and-carrot strategy (Example 21.4.6): `v^R` after the prescribed
pair, `ṽ` otherwise. -/
noncomputable def cg_scV (vR vt : ℝ) (xR xs : X) (yR ys : Y) : ℝ → X → Y → ℝ :=
  fun v x y => if x = cg_scZh vR xR xs v ∧ y = cg_scZg vR yR ys v then vR else vt

/-- The stick-and-carrot strategy keeps its promises: with `ṽ = (1 − δ) r(x*, y*) + δ v^R`, on
`{v^R, ṽ}` the state is the value. -/
theorem cg_stickCarrot_value {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (xR xs : X) (yR ys : Y) :
    ∀ s ∈ ({r xR yR, (1 - δ) * r xs ys + δ * r xR yR} : Set ℝ),
      cg_U δ r (cg_recStrat (cg_scZh (r xR yR) xR xs) (cg_scZg (r xR yR) yR ys)
        (cg_scV (r xR yR) ((1 - δ) * r xs ys + δ * r xR yR) xR xs yR ys) s) = s := by
  classical
  set vR := r xR yR
  set vt := (1 - δ) * r xs ys + δ * r xR yR
  refine cg_recStrat_value (K := |vR| + |vt|) hδ0 hδ1 hM ?_ ?_ ?_
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg vt]
    · linarith [abs_nonneg vR]
  · intro s _ ξ η
    unfold cg_scV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) (cg_scZg vR yR ys s) = vR := by
      simp [cg_scV]
    rw [hV]
    by_cases h : s = vR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      ring
    · have hs' : s = vt := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      rw [hs']

/-- **Example 21.4.6** (stick and carrot, Abreu 1988; Miao, pp. 770–771), corrected. Let the stick
`(x*, y*)` and the carrot `(x^R, y^R)` be competitive, `ṽ = (1 − δ) r(x*, y*) + δ v^R` with
`v^R = r(x^R, y^R)`. If `ṽ ≥ (1 − δ) r(x*, y') + δṽ` for all `y'` (the book's condition) and
`v^R ≥ (1 − δ) r(x^R, y') + δṽ` for all `y'` (the carrot's incentive constraint, which the book
omits), the stick-and-carrot strategy started at `ṽ` is an SPE with value `ṽ`. -/
theorem example_21_4_6 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xR xs : X} {yR ys : Y} (hR : (xR, yR) ∈ C)
    (hs : (xs, ys) ∈ C)
    (hstick : ∀ y', (1 - δ) * r xs y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤
      (1 - δ) * r xs ys + δ * r xR yR)
    (hcarrot : ∀ y', (1 - δ) * r xR y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤ r xR yR) :
    cg_IsSPE δ r C (cg_recStrat (cg_scZh (r xR yR) xR xs) (cg_scZg (r xR yR) yR ys)
        (cg_scV (r xR yR) ((1 - δ) * r xs ys + δ * r xR yR) xR xs yR ys)
        ((1 - δ) * r xs ys + δ * r xR yR)) ∧
      cg_U δ r (cg_recStrat (cg_scZh (r xR yR) xR xs) (cg_scZg (r xR yR) yR ys)
        (cg_scV (r xR yR) ((1 - δ) * r xs ys + δ * r xR yR) xR xs yR ys)
        ((1 - δ) * r xs ys + δ * r xR yR)) = (1 - δ) * r xs ys + δ * r xR yR := by
  classical
  set vR := r xR yR
  set vt := (1 - δ) * r xs ys + δ * r xR yR with hvt
  refine cg_recursive_spe (K := |vR| + |vt|) (S := {vR, vt}) hδ0 hδ1 hM ?_ ?_ ?_ ?_ ?_ vt
    (Or.inr rfl)
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg vt]
    · linarith [abs_nonneg vR]
  · intro s _ ξ η
    unfold cg_scV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) (cg_scZg vR yR ys s) = vR := by
      simp [cg_scV]
    rw [hV]
    by_cases h : s = vR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      ring
    · have hs' : s = vt := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      rw [hs']
  · intro s _
    by_cases h : s = vR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]; exact hR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]; exact hs
  · intro s hs' y'
    by_cases hy : y' = cg_scZg vR yR ys s
    · have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) y' = vR := by
        simp [cg_scV, hy]
      rw [hV, hy]
      by_cases h : s = vR
      · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
        linarith
      · have hs'' : s = vt := by
          rcases hs' with h' | h'
          · exact absurd h' h
          · exact h'
        simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
        rw [hs'']
    · have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) y' = vt := by
        simp [cg_scV, hy]
      rw [hV]
      by_cases h : s = vR
      · simp only [cg_scZh, h, ↓reduceIte]
        exact hcarrot y'
      · have hs'' : s = vt := by
          rcases hs' with h' | h'
          · exact absurd h' h
          · exact h'
        simp only [cg_scZh, h, ↓reduceIte]
        rw [hs'']
        exact hstick y'

end Miao.DynamicGames
