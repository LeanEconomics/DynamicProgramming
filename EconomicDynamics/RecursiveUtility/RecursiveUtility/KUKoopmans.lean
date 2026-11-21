/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Koopmans's utility (§20.1.1)

Miao §20.1.1, pp. 677–679. Consumption streams are sequences `c : ℕ → X` of bundles; the book's
space `L` of bounded sequences in `ℝˡ₊` is `ku_bddSeq K` (with `K = ℝˡ₊`), closed under the shift
`₁c` (`ku_shift`), the tails `ₜc` (`ku_tail`) and prepending a bundle (`ku_cons`):
`ku_bddSeq_closed`. Results are stated for any set `L` of streams with these closure properties.

* `eq_20_1`: the recursive representation `U(c) = W(u(c₀), U(₁c))` (20.1);
  `eq_20_1_additive`: the time-additive utility is an example.
* `ku_K1`, `ku_K2`, `ku_K3`: Koopmans's axioms (K1)–(K3).
* `ku_K1_of_recursive`, `ku_K2_of_recursive`, `ku_K3_iff_of_recursive`: a recursive
  representation satisfies (K1)–(K2) when `W` is strictly increasing in each argument, and (K3)
  iff `u` is not constant. The book's "any preference order with a recursive representation
  satisfies Koopmans's Axioms" is false without these conditions (`ku_K1_counterexample`,
  `ku_K3_counterexample`).
* `ku_koopmans_1960`: (K1)–(K2) give a recursive representation (Koopmans (1960), p. 678; the
  regularity of `W` is not addressed); `ku_ordinal_unique`: representations are unique up to a
  strictly increasing transformation.
* `definition_20_1_1`: dynamic consistency, with `U_t(c) = U(ₜc)`; `ku_dynConsistent_of_K1`
  ("Axiom (K1) ensures dynamic consistency") and `ku_dynConsistent_of_recursive`.
* `ku_IsSubjDiscount`: the subjective discount factor `β(x) = ∂W/∂U` at `(x, x, …)`.
* `example_20_1_1`, `example_20_1_1_epstein_hynes`: Uzawa and Epstein–Hynes utilities, with
  discount factors `β(u(c₀))` and `β(c₀)`.
* `example_20_1_2_const`, `example_20_1_2_discount`, `example_20_1_2_mrs`, `example_20_1_2`,
  `example_20_1_2_misprint`: for the CES aggregator `U(x, x, …) = x`, the discount factor is `β`,
  `MRS_{0,1} = (c₁/c₀)^ρ/β`, and `d log(c₁/c₀)/d log MRS_{0,1} = 1/ρ`. The printed formula
  `EIS = d log(c_s/c_t)/d log MRS_{s,t}` has the wrong sign: it gives `−1/ρ`.
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {X : Type*}

/-! ### Streams -/

/-- Miao, p. 677: the shifted stream `₁c = (c₁, c₂, …)`. -/
def ku_shift (c : ℕ → X) : ℕ → X := fun t => c (t + 1)

/-- Miao, p. 677: the tail `ₜc = (c_t, c_{t+1}, …)`. -/
def ku_tail (t : ℕ) (c : ℕ → X) : ℕ → X := fun s => c (s + t)

/-- The stream `(x, c₀, c₁, …)`, written `(x, ₁c)` in the book when `c` is a shifted stream. -/
def ku_cons (x : X) (c : ℕ → X) : ℕ → X := fun t => if t = 0 then x else c (t - 1)

theorem ku_cons_zero (x : X) (c : ℕ → X) : ku_cons x c 0 = x := rfl

theorem ku_shift_cons (x : X) (c : ℕ → X) : ku_shift (ku_cons x c) = c := by
  funext t
  simp [ku_shift, ku_cons]

theorem ku_cons_shift (c : ℕ → X) : ku_cons (c 0) (ku_shift c) = c := by
  funext t
  rcases t with _ | t
  · rfl
  · simp [ku_cons, ku_shift]

theorem ku_tail_zero (c : ℕ → X) : ku_tail 0 c = c := rfl

theorem ku_tail_succ (t : ℕ) (c : ℕ → X) : ku_tail (t + 1) c = ku_tail t (ku_shift c) := by
  funext s
  simp only [ku_tail, ku_shift]
  congr 1

/-- Miao, p. 677: the space `L` of streams in `K` bounded in `‖c‖_L = sup_t ‖c_t‖`. -/
def ku_bddSeq {E : Type*} [Norm E] (K : Set E) : Set (ℕ → E) :=
  {c | (∀ t, c t ∈ K) ∧ BddAbove (Set.range fun t => ‖c t‖)}

/-- `L` is closed under the shift, under prepending a bundle in `K`, and its streams start in
`K`. -/
theorem ku_bddSeq_closed {E : Type*} [Norm E] (K : Set E) :
    (∀ c ∈ ku_bddSeq K, ku_shift c ∈ ku_bddSeq K) ∧
      (∀ x ∈ K, ∀ c ∈ ku_bddSeq K, ku_cons x c ∈ ku_bddSeq K) ∧
      (∀ c ∈ ku_bddSeq K, c 0 ∈ K) := by
  refine ⟨fun c hc => ⟨fun t => hc.1 (t + 1), ?_⟩, fun x hx c hc => ⟨fun t => ?_, ?_⟩,
    fun c hc => hc.1 0⟩
  · obtain ⟨B, hB⟩ := hc.2
    exact ⟨B, by rintro _ ⟨t, rfl⟩; exact hB ⟨t + 1, rfl⟩⟩
  · rcases t with _ | t
    · exact hx
    · simpa [ku_cons] using hc.1 t
  · obtain ⟨B, hB⟩ := hc.2
    refine ⟨max B ‖x‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    rcases t with _ | t
    · exact le_max_right _ _
    · simpa [ku_cons] using le_max_of_le_left (hB ⟨t, rfl⟩)

/-! ### Recursive representations and Koopmans's axioms -/

/-- `U` represents the preference `pref` on `L`: `c ≽ c'` iff `U(c') ≤ U(c)`. -/
def ku_Represents (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) (U : (ℕ → X) → ℝ) :
    Prop :=
  ∀ c ∈ L, ∀ c' ∈ L, (pref c c' ↔ U c' ≤ U c)

/-- Miao, (20.1), p. 678: `U` is a recursive utility with time aggregator `W` and period utility
`u`: `U(c) = W(u(c₀), U(₁c))` for `c ∈ L`. -/
def eq_20_1 {Y : Type*} (L : Set (ℕ → X)) (U : (ℕ → X) → ℝ) (W : Y → ℝ → ℝ) (u : X → Y) :
    Prop :=
  ∀ c ∈ L, U c = W (u (c 0)) (U (ku_shift c))

/-- Miao, p. 678: the time-additive utility `U(c) = ∑ βᵗu(c_t)` satisfies (20.1) with
`W(a, y) = a + βy`, on any set of streams where the series converge. -/
theorem eq_20_1_additive (L : Set (ℕ → X)) (u : X → ℝ) (β : ℝ)
    (hsum : ∀ c ∈ L, Summable fun t => β ^ t * u (c t)) (hL : ∀ c ∈ L, ku_shift c ∈ L) :
    eq_20_1 L (fun c => ∑' t, β ^ t * u (c t)) (fun a y => a + β * y) u := by
  intro c hc
  have hs := hsum c hc
  have hs' := hsum _ (hL c hc)
  simp only
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, ku_shift, pow_succ]
  congr 1
  exact tsum_congr fun t => by ring

/-- Miao, p. 678, axiom (K1): stationarity, `(x, ₁c) ≽ (x, ₁c')` iff `₁c ≽ ₁c'`. -/
def ku_K1 (K : Set X) (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) : Prop :=
  ∀ x ∈ K, ∀ c ∈ L, ∀ c' ∈ L, (pref (ku_cons x c) (ku_cons x c') ↔ pref c c')

/-- Miao, p. 678, axiom (K2): limited independence,
`(x, ₁c) ≽ (x', ₁c)` iff `(x, ₁c') ≽ (x', ₁c')`. -/
def ku_K2 (K : Set X) (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) : Prop :=
  ∀ x ∈ K, ∀ x' ∈ K, ∀ c ∈ L, ∀ c' ∈ L,
    (pref (ku_cons x c) (ku_cons x' c) ↔ pref (ku_cons x c') (ku_cons x' c'))

/-- Miao, p. 678, axiom (K3): sensitivity, `(x, ₁c) ≻ (x', ₁c)` for some `₁c`, `x`, `x'`. -/
def ku_K3 (K : Set X) (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) : Prop :=
  ∃ c ∈ L, ∃ x ∈ K, ∃ x' ∈ K, pref (ku_cons x c) (ku_cons x' c) ∧
    ¬ pref (ku_cons x' c) (ku_cons x c)

/-- Miao, p. 678 (corrected): a recursive representation with `W` strictly increasing in its
second argument satisfies (K1). -/
theorem ku_K1_of_recursive {Y : Type*} {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} {W : Y → ℝ → ℝ} {u : X → Y}
    (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L) (hrep : ku_Represents L pref U)
    (hrec : eq_20_1 L U W u) (hW : ∀ a, StrictMono (W a)) : ku_K1 K L pref := by
  intro x hx c hc c' hc'
  rw [hrep _ (hcons x hx c hc) _ (hcons x hx c' hc'), hrep c hc c' hc',
    hrec _ (hcons x hx c hc), hrec _ (hcons x hx c' hc'), ku_shift_cons, ku_shift_cons,
    ku_cons_zero, ku_cons_zero]
  exact (hW (u x)).le_iff_le

/-- Miao, p. 678 (corrected): a recursive representation with `W` strictly increasing in its
first argument satisfies (K2). -/
theorem ku_K2_of_recursive {Y : Type*} [LinearOrder Y] {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} {W : Y → ℝ → ℝ} {u : X → Y}
    (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L) (hrep : ku_Represents L pref U)
    (hrec : eq_20_1 L U W u) (hW : ∀ y, StrictMono fun a => W a y) : ku_K2 K L pref := by
  intro x hx x' hx' c hc c' hc'
  rw [hrep _ (hcons x hx c hc) _ (hcons x' hx' c hc),
    hrep _ (hcons x hx c' hc') _ (hcons x' hx' c' hc'), hrec _ (hcons x hx c hc),
    hrec _ (hcons x' hx' c hc), hrec _ (hcons x hx c' hc'), hrec _ (hcons x' hx' c' hc')]
  simp only [ku_shift_cons, ku_cons_zero]
  exact ((hW (U c)).le_iff_le).trans ((hW (U c')).le_iff_le).symm

/-- Miao, p. 678 (corrected): for a recursive representation with `W` strictly increasing in its
first argument, (K3) holds iff the period utility `u` is not constant on `K` (and `L ≠ ∅`). -/
theorem ku_K3_iff_of_recursive {Y : Type*} [LinearOrder Y] {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} {W : Y → ℝ → ℝ} {u : X → Y}
    (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L) (hrep : ku_Represents L pref U)
    (hrec : eq_20_1 L U W u) (hW : ∀ y, StrictMono fun a => W a y) (hL : L.Nonempty) :
    ku_K3 K L pref ↔ ∃ x ∈ K, ∃ x' ∈ K, u x ≠ u x' := by
  have key : ∀ x ∈ K, ∀ x' ∈ K, ∀ c ∈ L,
      (pref (ku_cons x c) (ku_cons x' c) ↔ u x' ≤ u x) := by
    intro x hx x' hx' c hc
    rw [hrep _ (hcons x hx c hc) _ (hcons x' hx' c hc), hrec _ (hcons x hx c hc),
      hrec _ (hcons x' hx' c hc)]
    simp only [ku_shift_cons, ku_cons_zero]
    exact (hW (U c)).le_iff_le
  constructor
  · rintro ⟨c, hc, x, hx, x', hx', h1, h2⟩
    rw [key x hx x' hx' c hc] at h1
    rw [key x' hx' x hx c hc] at h2
    exact ⟨x, hx, x', hx', fun h => h2 (le_of_eq h)⟩
  · rintro ⟨x, hx, x', hx', hne⟩
    obtain ⟨c, hc⟩ := hL
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨c, hc, x', hx', x, hx, (key x' hx' x hx c hc).2 hlt.le,
        fun h => absurd ((key x hx x' hx' c hc).1 h) (not_le.2 hlt)⟩
    · exact ⟨c, hc, x, hx, x', hx', (key x hx x' hx' c hc).2 hlt.le,
        fun h => absurd ((key x' hx' x hx c hc).1 h) (not_le.2 hlt)⟩

/-- A constant stream lies in the book's `L` (with `K = ℝ₊`). -/
theorem ku_const_mem_bddSeq {a : ℝ} (ha : 0 ≤ a) :
    (fun _ : ℕ => a) ∈ ku_bddSeq (Set.Ici (0 : ℝ)) :=
  ⟨fun _ => ha, ⟨‖a‖, by rintro _ ⟨t, rfl⟩; exact le_rfl⟩⟩

/-- Counterexample (Miao, p. 678): a recursive representation need not satisfy (K1).
`U(c) = c₀` satisfies (20.1) with `W(a, y) = a`, `u = id`, on the book's `L ⊆ ℝ₊^ℕ`, but the
preference it represents is not stationary. -/
theorem ku_K1_counterexample :
    eq_20_1 (ku_bddSeq (Set.Ici (0 : ℝ))) (fun c => c 0) (fun a _ => a) id ∧
      ¬ ku_K1 (Set.Ici (0 : ℝ)) (ku_bddSeq (Set.Ici (0 : ℝ))) fun c c' => c' 0 ≤ c 0 := by
  refine ⟨fun c _ => rfl, fun h => ?_⟩
  have h1 := h 0 (Set.mem_Ici.2 (le_refl (0 : ℝ))) (fun _ => 0) (ku_const_mem_bddSeq le_rfl)
    (fun _ => 1)
    (ku_const_mem_bddSeq zero_le_one)
  simp only [ku_cons_zero, le_refl, true_iff] at h1
  norm_num at h1

/-- Counterexample (Miao, p. 678): a recursive representation need not satisfy (K3): `U ≡ 0`
satisfies (20.1) with `W ≡ 0`. -/
theorem ku_K3_counterexample :
    eq_20_1 (ku_bddSeq (Set.Ici (0 : ℝ))) (fun _ => (0 : ℝ)) (fun (_ : ℝ) _ => 0) id ∧
      ¬ ku_K3 (Set.Ici (0 : ℝ)) (ku_bddSeq (Set.Ici (0 : ℝ))) fun _ _ => (0 : ℝ) ≤ 0 := by
  refine ⟨fun _ _ => rfl, ?_⟩
  rintro ⟨_, _, _, _, _, _, _, h⟩
  exact h le_rfl

/-- Miao, p. 678 (Koopmans (1960)): if `U` represents a preference satisfying (K1) and (K2) on
`L`, then `U` has a recursive representation (20.1): `u(x) = U(x, d)` for a fixed `d ∈ L` and a
suitable `W`. (Axiom (K3) and the continuity of `W` are not needed for the algebra.) -/
theorem ku_koopmans_1960 {K : Set X} {L : Set (ℕ → X)} {pref : (ℕ → X) → (ℕ → X) → Prop}
    {U : (ℕ → X) → ℝ} (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L)
    (hshift : ∀ c ∈ L, ku_shift c ∈ L) (hhead : ∀ c ∈ L, c 0 ∈ K)
    (hrep : ku_Represents L pref U) (h1 : ku_K1 K L pref) (h2 : ku_K2 K L pref) {d : ℕ → X}
    (hd : d ∈ L) : ∃ (W : ℝ → ℝ → ℝ) (u : X → ℝ), eq_20_1 L U W u := by
  classical
  let u : X → ℝ := fun x => U (ku_cons x d)
  let W : ℝ → ℝ → ℝ := fun a b =>
    if h : ∃ p : X × (ℕ → X), p.1 ∈ K ∧ p.2 ∈ L ∧ u p.1 = a ∧ U p.2 = b then
      U (ku_cons h.choose.1 h.choose.2) else 0
  refine ⟨W, u, fun c hc => ?_⟩
  have hex : ∃ p : X × (ℕ → X), p.1 ∈ K ∧ p.2 ∈ L ∧ u p.1 = u (c 0) ∧
      U p.2 = U (ku_shift c) := ⟨(c 0, ku_shift c), hhead c hc, hshift c hc, rfl, rfl⟩
  have hW : W (u (c 0)) (U (ku_shift c)) = U (ku_cons hex.choose.1 hex.choose.2) := by
    simp only [W]
    split_ifs
    rfl
  rw [hW]
  obtain ⟨hxK, hcL, hux, hUc⟩ := hex.choose_spec
  set x := hex.choose.1
  set c' := hex.choose.2
  have hc0 := hhead c hc
  have hsc := hshift c hc
  -- `(x, d) ∼ (c₀, d)`, so by (K2) `(x, c') ∼ (c₀, c')`
  have e1 : U (ku_cons x c') = U (ku_cons (c 0) c') := by
    have ha := (hrep _ (hcons x hxK d hd) _ (hcons _ hc0 d hd)).2 (le_of_eq hux.symm)
    have hb := (hrep _ (hcons _ hc0 d hd) _ (hcons x hxK d hd)).2 (le_of_eq hux)
    have ha' := (h2 x hxK _ hc0 d hd c' hcL).1 ha
    have hb' := (h2 _ hc0 x hxK d hd c' hcL).1 hb
    exact le_antisymm ((hrep _ (hcons _ hc0 c' hcL) _ (hcons x hxK c' hcL)).1 hb')
      ((hrep _ (hcons x hxK c' hcL) _ (hcons _ hc0 c' hcL)).1 ha')
  -- `c' ∼ ₁c`, so by (K1) `(c₀, c') ∼ (c₀, ₁c)`
  have e2 : U (ku_cons (c 0) c') = U (ku_cons (c 0) (ku_shift c)) := by
    have ha := (hrep _ hcL _ hsc).2 (le_of_eq hUc.symm)
    have hb := (hrep _ hsc _ hcL).2 (le_of_eq hUc)
    have ha' := (h1 _ hc0 c' hcL _ hsc).2 ha
    have hb' := (h1 _ hc0 _ hsc c' hcL).2 hb
    exact le_antisymm ((hrep _ (hcons _ hc0 _ hsc) _ (hcons _ hc0 c' hcL)).1 hb')
      ((hrep _ (hcons _ hc0 c' hcL) _ (hcons _ hc0 _ hsc)).1 ha')
  rw [e1, e2, ku_cons_shift]

/-- Miao, p. 678: the representation is unique in the sense of ordinal utility: two utility
functions representing the same preference on `L` differ by a strictly increasing
transformation. -/
theorem ku_ordinal_unique {L : Set (ℕ → X)} {pref : (ℕ → X) → (ℕ → X) → Prop}
    {U U' : (ℕ → X) → ℝ} (hU : ku_Represents L pref U) (hU' : ku_Represents L pref U') :
    ∃ f : ℝ → ℝ, StrictMonoOn f (U '' L) ∧ ∀ c ∈ L, U' c = f (U c) := by
  classical
  let f : ℝ → ℝ := fun y => if h : ∃ c, c ∈ L ∧ U c = y then U' h.choose else 0
  have hf : ∀ c ∈ L, f (U c) = U' c := by
    intro c hc
    have hex : ∃ c', c' ∈ L ∧ U c' = U c := ⟨c, hc, rfl⟩
    simp only [f]
    split_ifs
    obtain ⟨h1, h2⟩ := hex.choose_spec
    have ha := (hU _ h1 _ hc).2 (le_of_eq h2.symm)
    have hb := (hU _ hc _ h1).2 (le_of_eq h2)
    exact le_antisymm ((hU' _ hc _ h1).1 hb) ((hU' _ h1 _ hc).1 ha)
  refine ⟨f, ?_, fun c hc => (hf c hc).symm⟩
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hlt
  rw [hf c₁ hc₁, hf c₂ hc₂]
  have h1 : ¬ pref c₁ c₂ := fun h => absurd ((hU _ hc₁ _ hc₂).1 h) (not_le.2 hlt)
  rw [hU' _ hc₁ _ hc₂] at h1
  exact not_le.1 h1

/-! ### Dynamic consistency -/

/-- **Definition 20.1.1** (Miao, p. 678). `U` is dynamically consistent on `L` if for all `t` and
streams `c, c'` with `c_s = c'_s` for `s < t`, `U_t(c) > U_t(c')` implies `U₀(c) > U₀(c')`, where
`U_t(c) = U(ₜc)`. -/
def definition_20_1_1 (L : Set (ℕ → X)) (U : (ℕ → X) → ℝ) : Prop :=
  ∀ t, ∀ c ∈ L, ∀ c' ∈ L, (∀ s < t, c s = c' s) → U (ku_tail t c') < U (ku_tail t c) →
    U c' < U c

/-- Miao, p. 678: a recursive utility (20.1) with `W` strictly increasing in its second argument
is dynamically consistent. -/
theorem ku_dynConsistent_of_recursive {Y : Type*} {L : Set (ℕ → X)} {U : (ℕ → X) → ℝ}
    {W : Y → ℝ → ℝ} {u : X → Y} (hshift : ∀ c ∈ L, ku_shift c ∈ L) (hrec : eq_20_1 L U W u)
    (hW : ∀ a, StrictMono (W a)) : definition_20_1_1 L U := by
  intro t
  induction t with
  | zero => exact fun c _ c' _ _ h => h
  | succ t ih =>
    intro c hc c' hc' heq hlt
    rw [ku_tail_succ, ku_tail_succ] at hlt
    have h1 := ih _ (hshift c hc) _ (hshift c' hc')
      (fun s hs => heq (s + 1) (by omega)) hlt
    rw [hrec c hc, hrec c' hc', ← heq 0 (by omega)]
    exact hW _ h1

/-- Miao, p. 678: "Axiom (K1) ensures dynamic consistency": if `U` represents a preference on `L`
that satisfies (K1), then `U` is dynamically consistent. -/
theorem ku_dynConsistent_of_K1 {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} (hshift : ∀ c ∈ L, ku_shift c ∈ L)
    (hhead : ∀ c ∈ L, c 0 ∈ K) (hrep : ku_Represents L pref U) (h1 : ku_K1 K L pref) :
    definition_20_1_1 L U := by
  intro t
  induction t with
  | zero => exact fun c _ c' _ _ h => h
  | succ t ih =>
    intro c hc c' hc' heq hlt
    rw [ku_tail_succ, ku_tail_succ] at hlt
    have hs := ih _ (hshift c hc) _ (hshift c' hc')
      (fun s hs => heq (s + 1) (by omega)) hlt
    have hn : ¬ pref (ku_shift c') (ku_shift c) := fun h =>
      absurd ((hrep _ (hshift c' hc') _ (hshift c hc)).1 h) (not_le.2 hs)
    rw [← h1 (c 0) (hhead c hc) _ (hshift c' hc') _ (hshift c hc)] at hn
    have e : ku_cons (c 0) (ku_shift c') = c' := by
      rw [heq 0 (by omega)]
      exact ku_cons_shift c'
    rw [e, ku_cons_shift, hrep c' hc' c hc] at hn
    exact not_le.1 hn

/-! ### The subjective discount factor and Examples 20.1.1–20.1.2 -/

/-- Miao, p. 678: `b` is the subjective discount factor `β(x) = ∂W(u, U)/∂U` at the constant
stream `(x, x, …)`. -/
def ku_IsSubjDiscount (W : ℝ → ℝ → ℝ) (u : X → ℝ) (U : (ℕ → X) → ℝ) (x : X) (b : ℝ) : Prop :=
  HasDerivAt (W (u x)) b (U fun _ => x)

/-- **Example 20.1.1** (Miao, p. 679), Uzawa (1968): `U(c) = u(c₀) + β(u(c₀))U(₁c)` is (20.1)
with `W(a, y) = a + β(a)y`, and the subjective discount factor at `(x, x, …)` is `β(u(x))`. -/
theorem example_20_1_1 (L : Set (ℕ → X)) (U : (ℕ → X) → ℝ) (u : X → ℝ) (β : ℝ → ℝ) :
    (eq_20_1 L U (fun a y => a + β a * y) u ↔
      ∀ c ∈ L, U c = u (c 0) + β (u (c 0)) * U (ku_shift c)) ∧
      ∀ x, ku_IsSubjDiscount (fun a y => a + β a * y) u U x (β (u x)) := by
  refine ⟨Iff.rfl, fun x => ?_⟩
  have h := ((hasDerivAt_id (U fun _ => x)).const_mul (β (u x))).const_add (u x)
  simp only [id, mul_one] at h
  exact h

/-- **Example 20.1.1** (Miao, p. 679), Epstein and Hynes (1983): for `U(c) = u(c₀) + β(c₀)U(₁c)`
the derivative of the aggregator `y ↦ u(x) + β(x)y` is the discount factor `β(x)`. -/
theorem example_20_1_1_epstein_hynes (u β : X → ℝ) (x : X) (y : ℝ) :
    HasDerivAt (fun y => u x + β x * y) (β x) y := by
  simpa using ((hasDerivAt_id y).const_mul (β x)).const_add (u x)

/-- The CES time aggregator `W(x, y) = ((1 − β)x^{1−ρ} + βy^{1−ρ})^{1/(1−ρ)}` of Example 20.1.2. -/
noncomputable def ku_ces (β ρ x y : ℝ) : ℝ :=
  ((1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ)) ^ (1 - ρ)⁻¹

theorem ku_ces_pos {β ρ x y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hx : 0 < x) (hy : 0 < y) :
    0 < ku_ces β ρ x y := by
  have h1 : 0 < 1 - β := by linarith
  have := Real.rpow_pos_of_pos hx (1 - ρ)
  have := Real.rpow_pos_of_pos hy (1 - ρ)
  exact Real.rpow_pos_of_pos (by positivity) _

/-- `W(x, y)^{1−ρ} = (1 − β)x^{1−ρ} + βy^{1−ρ}`. -/
theorem ku_ces_rpow {β ρ x y : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : ku_ces β ρ x y ^ (1 - ρ) = (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) := by
  have h1 : 0 ≤ 1 - β := by linarith
  have h2 := Real.rpow_nonneg hx (1 - ρ)
  have h3 := Real.rpow_nonneg hy (1 - ρ)
  exact Real.rpow_inv_rpow (by positivity) (sub_ne_zero.2 (Ne.symm hρ))

/-- The partial derivative `W_x = (1 − β)x^{−ρ}W^ρ` of the CES aggregator. -/
theorem ku_ces_hasDerivAt_x {β ρ x y : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' => ku_ces β ρ x' y) ((1 - β) * x ^ (-ρ) * ku_ces β ρ x y ^ ρ) x := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 < 1 - β := by linarith
  have hxa := Real.rpow_pos_of_pos hx (1 - ρ)
  have hya := Real.rpow_pos_of_pos hy (1 - ρ)
  set S := (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) with hS
  have hSpos : 0 < S := by positivity
  have hd : HasDerivAt (fun x' => (1 - β) * x' ^ (1 - ρ) + β * y ^ (1 - ρ))
      ((1 - β) * ((1 - ρ) * x ^ (1 - ρ - 1))) x :=
    ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul (1 - β)).add_const _
  have h2 := hd.rpow_const (p := (1 - ρ)⁻¹) (Or.inl hSpos.ne')
  refine HasDerivAt.congr_deriv h2 ?_
  have e1 : (1 : ℝ) - ρ - 1 = -ρ := by ring
  have e2 : ku_ces β ρ x y ^ ρ = S ^ ((1 - ρ)⁻¹ - 1) := by
    rw [show ku_ces β ρ x y = S ^ (1 - ρ)⁻¹ from rfl, ← Real.rpow_mul hSpos.le]
    congr 1
    field_simp
    ring
  rw [e1, e2]
  field_simp
  rfl

/-- The partial derivative `W_y = βy^{−ρ}W^ρ` of the CES aggregator. -/
theorem ku_ces_hasDerivAt_y {β ρ x y : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' => ku_ces β ρ x y') (β * y ^ (-ρ) * ku_ces β ρ x y ^ ρ) y := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 < 1 - β := by linarith
  have hxa := Real.rpow_pos_of_pos hx (1 - ρ)
  have hya := Real.rpow_pos_of_pos hy (1 - ρ)
  set S := (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) with hS
  have hSpos : 0 < S := by positivity
  have hd : HasDerivAt (fun y' => (1 - β) * x ^ (1 - ρ) + β * y' ^ (1 - ρ))
      (β * ((1 - ρ) * y ^ (1 - ρ - 1))) y :=
    ((Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul β).const_add _
  have h2 := hd.rpow_const (p := (1 - ρ)⁻¹) (Or.inl hSpos.ne')
  refine HasDerivAt.congr_deriv h2 ?_
  have e1 : (1 : ℝ) - ρ - 1 = -ρ := by ring
  have e2 : ku_ces β ρ x y ^ ρ = S ^ ((1 - ρ)⁻¹ - 1) := by
    rw [show ku_ces β ρ x y = S ^ (1 - ρ)⁻¹ from rfl, ← Real.rpow_mul hSpos.le]
    congr 1
    field_simp
    ring
  rw [e1, e2]
  field_simp
  rfl

/-- **Example 20.1.2** (Miao, p. 679): for the CES aggregator the only positive solution of
`u = W(x, u)` is `u = x`; so a positive recursive utility assigns `U(x, x, …) = x`. -/
theorem example_20_1_2_const {β ρ x u : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) (hu : 0 < u) (h : u = ku_ces β ρ x u) : u = x := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have e := congrArg (fun z => z ^ (1 - ρ)) h
  rw [ku_ces_rpow hρ hβ0.le hβ1.le hx.le hu.le] at e
  have e2 : u ^ (1 - ρ) = x ^ (1 - ρ) := by
    have : (1 - β) * u ^ (1 - ρ) = (1 - β) * x ^ (1 - ρ) := by linarith
    exact mul_left_cancel₀ (by linarith) this
  have := congrArg (fun z => z ^ (1 - ρ)⁻¹) e2
  rwa [Real.rpow_rpow_inv hu.le h1, Real.rpow_rpow_inv hx.le h1] at this

/-- **Example 20.1.2** (Miao, p. 679): the subjective discount factor of the CES aggregator is
`β`: `∂W/∂U` at `(x, U(x, x, …)) = (x, x)` equals `β`. -/
theorem example_20_1_2_discount {β ρ x : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) : HasDerivAt (fun y => ku_ces β ρ x y) β x := by
  have h := ku_ces_hasDerivAt_y hρ hβ0 hβ1 hx hx
  have hxx : ku_ces β ρ x x = x := by
    have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
    rw [ku_ces, show (1 - β) * x ^ (1 - ρ) + β * x ^ (1 - ρ) = x ^ (1 - ρ) by ring,
      Real.rpow_rpow_inv hx.le h1]
  rw [hxx, mul_assoc, ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, mul_one] at h
  exact h

theorem ku_shift_update_zero (c : ℕ → ℝ) (x : ℝ) :
    ku_shift (Function.update c 0 x) = ku_shift c := by
  funext t
  simp [ku_shift]

theorem ku_shift_update_succ (c : ℕ → ℝ) (s : ℕ) (x : ℝ) :
    ku_shift (Function.update c (s + 1) x) = Function.update (ku_shift c) s x := by
  funext t
  simp [ku_shift, Function.update_apply]

/-- **Example 20.1.2** (Miao, p. 679). Let `U` solve `U(c) = W(c₀, U(₁c))` with the CES aggregator
on a set `L` of positive streams closed under the shift and under changing one entry to a
positive number, with `U > 0` on `L`. Then the partial derivatives of `U` in `c₀` and `c₁` are
`∂U/∂c₀ = W_x(c₀, U(₁c))` and `∂U/∂c₁ = W_y(c₀, U(₁c))W_x(c₁, U(₂c))`, and
`MRS_{0,1} = (∂U/∂c₀)/(∂U/∂c₁) = c₀^{−ρ}/(βc₁^{−ρ})`. -/
theorem example_20_1_2_mrs {β ρ : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {L : Set (ℕ → ℝ)} {U : (ℕ → ℝ) → ℝ} (hpos : ∀ c ∈ L, ∀ t, 0 < c t)
    (hUpos : ∀ c ∈ L, 0 < U c) (hshift : ∀ c ∈ L, ku_shift c ∈ L)
    (hupd : ∀ c ∈ L, ∀ s, ∀ x, 0 < x → Function.update c s x ∈ L)
    (hrec : ∀ c ∈ L, U c = ku_ces β ρ (c 0) (U (ku_shift c))) {c : ℕ → ℝ} (hc : c ∈ L) :
    ∃ D₀ D₁ : ℝ, HasDerivAt (fun x => U (Function.update c 0 x)) D₀ (c 0) ∧
      HasDerivAt (fun x => U (Function.update c 1 x)) D₁ (c 1) ∧ 0 < D₀ ∧ 0 < D₁ ∧
      D₀ / D₁ = c 0 ^ (-ρ) / (β * c 1 ^ (-ρ)) := by
  have hc0 := hpos c hc 0
  have hc1 := hpos c hc 1
  have hs1 := hshift c hc
  have hs2 := hshift _ hs1
  have hU1 := hUpos _ hs1
  have hU2 := hUpos _ hs2
  set U₁ := U (ku_shift c)
  set U₂ := U (ku_shift (ku_shift c))
  have hU1rec : U₁ = ku_ces β ρ (c 1) U₂ := hrec _ hs1
  -- the date-0 partial
  have hev0 : (fun x => ku_ces β ρ x U₁) =ᶠ[𝓝 (c 0)] fun x => U (Function.update c 0 x) := by
    filter_upwards [lt_mem_nhds hc0] with x hx
    rw [hrec _ (hupd c hc 0 x hx), Function.update_self, ku_shift_update_zero]
  have hD0 := (ku_ces_hasDerivAt_x hρ hβ0 hβ1 hc0 hU1).congr_of_eventuallyEq hev0.symm
  -- the date-1 partial
  have hev1 : (fun x => ku_ces β ρ (c 0) (ku_ces β ρ x U₂)) =ᶠ[𝓝 (c 1)]
      fun x => U (Function.update c 1 x) := by
    filter_upwards [lt_mem_nhds hc1] with x hx
    have hm := hupd c hc 1 x hx
    have hm1 : Function.update (ku_shift c) 0 x ∈ L := hupd _ hs1 0 x hx
    rw [hrec _ hm, Function.update_of_ne zero_ne_one, show (1 : ℕ) = 0 + 1 from rfl,
      ku_shift_update_succ, hrec _ hm1, Function.update_self, ku_shift_update_zero]
  have hin := ku_ces_hasDerivAt_x hρ hβ0 hβ1 hc1 hU2
  rw [← hU1rec] at hin
  have hout := ku_ces_hasDerivAt_y hρ hβ0 hβ1 hc0 hU1
  have hout' : HasDerivAt (fun y' => ku_ces β ρ (c 0) y')
      (β * U₁ ^ (-ρ) * ku_ces β ρ (c 0) U₁ ^ ρ) (ku_ces β ρ (c 1) U₂) := by
    rw [← hU1rec]
    exact hout
  have hD1 := (hout'.comp (c 1) hin).congr_of_eventuallyEq hev1.symm
  refine ⟨_, _, hD0, hD1, ?_, ?_, ?_⟩
  · have := Real.rpow_pos_of_pos hc0 (-ρ)
    have := Real.rpow_pos_of_pos (ku_ces_pos (ρ := ρ) hβ0 hβ1 hc0 hU1) ρ
    have : 0 < 1 - β := by linarith
    positivity
  · have := Real.rpow_pos_of_pos hc1 (-ρ)
    have := Real.rpow_pos_of_pos hU1 (-ρ)
    have := Real.rpow_pos_of_pos (ku_ces_pos (ρ := ρ) hβ0 hβ1 hc0 hU1) ρ
    have := Real.rpow_pos_of_pos hU1 ρ
    have : 0 < 1 - β := by linarith
    positivity
  · have hW := Real.rpow_pos_of_pos (ku_ces_pos (ρ := ρ) hβ0 hβ1 hc0 hU1) ρ
    have hU1r : U₁ ^ (-ρ) * U₁ ^ ρ = 1 := by
      rw [← Real.rpow_add hU1, neg_add_cancel, Real.rpow_zero]
    have h1 := Real.rpow_pos_of_pos hc1 (-ρ)
    have h0 := Real.rpow_pos_of_pos hc0 (-ρ)
    have hb : 0 < 1 - β := by linarith
    calc (1 - β) * c 0 ^ (-ρ) * ku_ces β ρ (c 0) U₁ ^ ρ /
          (β * U₁ ^ (-ρ) * ku_ces β ρ (c 0) U₁ ^ ρ * ((1 - β) * c 1 ^ (-ρ) * U₁ ^ ρ))
        = c 0 ^ (-ρ) / (β * c 1 ^ (-ρ) * (U₁ ^ (-ρ) * U₁ ^ ρ)) := by
          field_simp
      _ = c 0 ^ (-ρ) / (β * c 1 ^ (-ρ)) := by rw [hU1r, mul_one]

/-- **Example 20.1.2** (Miao, p. 679): "EIS is equal to `1/ρ`". With
`MRS_{0,1} = c₀^{−ρ}/(βc₁^{−ρ})` (`example_20_1_2_mrs`), `log MRS_{0,1} = ρ log(c₁/c₀) − log β`, so
`log(c₁/c₀) = (log MRS_{0,1} + log β)/ρ` and `d log(c₁/c₀)/d log MRS_{0,1} = 1/ρ`. -/
theorem example_20_1_2 {β ρ c₀ c₁ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) :
    Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) = ρ * Real.log (c₁ / c₀) - Real.log β ∧
      (Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) + Real.log β) / ρ = Real.log (c₁ / c₀) ∧
      ∀ m, HasDerivAt (fun m => (m + Real.log β) / ρ) (1 / ρ) m := by
  have h0 : 0 < c₀ ^ (-ρ) := Real.rpow_pos_of_pos hc₀ _
  have h1 : 0 < c₁ ^ (-ρ) := Real.rpow_pos_of_pos hc₁ _
  have hlog : Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) = ρ * Real.log (c₁ / c₀) - Real.log β := by
    rw [Real.log_div h0.ne' (by positivity), Real.log_mul hβ.ne' h1.ne', Real.log_rpow hc₀,
      Real.log_rpow hc₁, Real.log_div hc₁.ne' hc₀.ne']
    ring
  refine ⟨hlog, ?_, fun m => ?_⟩
  · rw [hlog]
    field_simp
    ring
  · simpa using ((hasDerivAt_id m).add_const (Real.log β)).div_const ρ

/-- Miao, p. 679 (sign misprint): with the printed definition `EIS = d log(c_s/c_t)/d log MRS_{s,t}`
the CES aggregator gives `log(c₀/c₁) = −(log MRS_{0,1} + log β)/ρ`, whose derivative is `−1/ρ`,
not `1/ρ`. -/
theorem example_20_1_2_misprint {β ρ c₀ c₁ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) :
    -(Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) + Real.log β) / ρ = Real.log (c₀ / c₁) ∧
      ∀ m, HasDerivAt (fun m => -(m + Real.log β) / ρ) (-1 / ρ) m := by
  obtain ⟨_, h2, _⟩ := example_20_1_2 hβ hρ hc₀ hc₁
  refine ⟨?_, fun m => ?_⟩
  · rw [neg_div, h2, ← Real.log_inv, inv_div]
  · have h := (((hasDerivAt_id m).add_const (Real.log β)).div_const ρ).neg
    convert h using 1
    · funext m
      simp only [Pi.neg_apply, id]
      ring
    · ring

end Miao.RecursiveUtility
