/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.Semiconjugacy
import Mathlib.Data.ENat.Basic

/-!
# Strong order stability does not transfer under one-sided order continuity

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Lemma 5.2.2 (ii), Theorem 5.2.3 and
Theorem 5.2.4 (pp. 162–163).

The book's order continuity (§A.5.1.3) asks only that `vₙ ↑ v` imply `Svₙ ↑ Sv`. With that
reading the three results fail:

* `Fork` is a chain `a₀ > a₁ > a₂ > ⋯` above two incomparable minimal points `⊥₁, ⊥₂`, and
  `Chain = ℕ∞ᵒᵈ` is `0 > 1 > 2 > ⋯ > ⊤`. In both, every increasing sequence is eventually
  constant, so every order preserving map out of them is order continuous.
* `S(aₙ) = aₙ₊₁`, `S(⊥ᵢ) = ⊥₁` on `Fork` and `Ŝc = c + 1` on `Chain` are strongly semiconjugate
  under order preserving, order continuous maps `F, G`. `Ŝ` is strongly order stable, but
  `Sⁿa₀ = aₙ` decreases without an infimum (`⊥₁` and `⊥₂` are both maximal lower bounds), so `S`
  is not (`theorem_5_2_3_fails`): this contradicts Lemma 5.2.2 (ii) and Theorem 5.2.3.
* Reversing the order of `Chain` gives order-reversing `F, G` satisfying the hypothesis of
  Theorem 5.2.4 with the same conclusion failing (`theorem_5_2_4_fails`).

The proofs of the corrected statements in `Semiconjugacy` also use decreasing limits.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- If every increasing sequence in `V` is eventually constant, every order preserving map out of
`V` is order continuous. -/
theorem orderContinuous_of_stabilizes {V W : Type*} [PartialOrder V] [PartialOrder W]
    (hV : ∀ f : ℕ → V, Monotone f → ∃ n, ∀ m, n ≤ m → f m = f n) {S : V → W} (hS : Monotone S) :
    OrderContinuous S := by
  intro f v hf hl
  obtain ⟨n, hn⟩ := hV f hf
  have hv : v = f n := le_antisymm (hl.2 fun _ ⟨m, hm⟩ => hm ▸ (by
    rcases le_total m n with h | h
    · exact hf h
    · exact (hn m h).le)) (hl.1 ⟨n, rfl⟩)
  subst hv
  refine ⟨fun _ ⟨m, hm⟩ => hm ▸ (by
    rcases le_total m n with h | h
    · exact hS (hf h)
    · exact (congrArg S (hn m h)).le), fun b hb => hb ⟨n, rfl⟩⟩

namespace SemiconjCounterexample

/-- A decreasing chain `a₀ > a₁ > ⋯` above two incomparable minimal points `⊥₁` and `⊥₂`:
`inl n` is `aₙ`, `inr false` is `⊥₁` and `inr true` is `⊥₂`. -/
def Fork : Type := ℕ ⊕ Bool

/-- `aₙ`. -/
def Fork.a (n : ℕ) : Fork := Sum.inl n

/-- `⊥₁`. -/
def Fork.bot₁ : Fork := Sum.inr false

/-- `⊥₂`. -/
def Fork.bot₂ : Fork := Sum.inr true

/-- The order of `Fork`. -/
def Fork.le : Fork → Fork → Prop
  | Sum.inl m, Sum.inl n => n ≤ m
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr b, Sum.inr b' => b = b'
  | Sum.inl _, Sum.inr _ => False

theorem Fork.le_refl' : ∀ x : Fork, Fork.le x x
  | Sum.inl _ => le_rfl
  | Sum.inr _ => rfl

theorem Fork.le_trans' : ∀ x y z : Fork, Fork.le x y → Fork.le y z → Fork.le x z
  | Sum.inl _, Sum.inl _, Sum.inl _, h1, h2 => le_trans h2 h1
  | Sum.inr _, Sum.inl _, Sum.inl _, _, _ => trivial
  | Sum.inr _, Sum.inr _, Sum.inl _, _, _ => trivial
  | Sum.inr _, Sum.inr _, Sum.inr _, h1, h2 => h1.trans h2
  | Sum.inl _, Sum.inr _, _, h, _ => False.elim h
  | _, Sum.inl _, Sum.inr _, _, h => False.elim h

theorem Fork.le_antisymm' : ∀ x y : Fork, Fork.le x y → Fork.le y x → x = y
  | Sum.inl _, Sum.inl _, h1, h2 => congrArg Sum.inl (le_antisymm h2 h1)
  | Sum.inr _, Sum.inr _, h, _ => congrArg Sum.inr h
  | Sum.inl _, Sum.inr _, h, _ => False.elim h
  | Sum.inr _, Sum.inl _, _, h => False.elim h

/-- `Fork` as a partial order. -/
abbrev forkOrder : PartialOrder Fork where
  le := Fork.le
  le_refl := Fork.le_refl'
  le_trans := Fork.le_trans'
  le_antisymm := Fork.le_antisymm'

attribute [local instance] forkOrder

/-- `ℕ∞` with the reversed order: `0 > 1 > 2 > ⋯ > ⊤`. -/
abbrev Chain : Type := ℕ∞ᵒᵈ

/-- `Ŝc = c + 1` on `Chain`. -/
def shift (c : Chain) : Chain := OrderDual.toDual (OrderDual.ofDual c + 1)

/-- `F : Fork → Chain`, `aₙ ↦ n + 1`, `⊥ᵢ ↦ ⊤`. -/
def Fmap : Fork → Chain
  | Sum.inl n => OrderDual.toDual ((n : ℕ∞) + 1)
  | Sum.inr _ => OrderDual.toDual ⊤

/-- `G : Chain → Fork`, `n ↦ aₙ`, `⊤ ↦ ⊥₁`. -/
noncomputable def Gmap (c : Chain) : Fork :=
  if OrderDual.ofDual c = ⊤ then Fork.bot₁ else Fork.a (OrderDual.ofDual c).toNat

/-- `S : Fork → Fork`, `aₙ ↦ aₙ₊₁`, `⊥ᵢ ↦ ⊥₁`. -/
def Smap : Fork → Fork
  | Sum.inl n => Fork.a (n + 1)
  | Sum.inr _ => Fork.bot₁

theorem le_a_iff {m n : ℕ} : Fork.a m ≤ Fork.a n ↔ n ≤ m := Iff.rfl

theorem isStronglySemiconj : IsStronglySemiconj Smap shift Fmap Gmap := by
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rcases x with n | b
    · have h : ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl
      simp only [Smap, Fmap, Gmap, OrderDual.ofDual_toDual, h, ENat.natCast_ne_top, ite_false,
        ENat.toNat_natCast]
    · simp [Smap, Fmap, Gmap]
  · induction c using OrderDual.rec with
    | toDual e =>
      cases e using ENat.recTopCoe with
      | top => simp [shift, Fmap, Gmap, Fork.bot₁]
      | coe k => simp [shift, Fmap, Gmap, Fork.a]

theorem Fmap_mono : Monotone Fmap := by
  intro x y hxy
  rcases x with m | b <;> rcases y with n | b'
  all_goals first
    | exact (OrderDual.toDual_le_toDual.2 (by exact_mod_cast Nat.add_le_add_right hxy 1))
    | exact OrderDual.toDual_le_toDual.2 le_top
    | exact le_rfl
    | exact absurd hxy id

theorem Gmap_mono : Monotone Gmap := by
  intro c c' hcc'
  induction c using OrderDual.rec with
  | toDual e =>
  induction c' using OrderDual.rec with
  | toDual e' =>
  have h : e' ≤ e := OrderDual.toDual_le_toDual.1 hcc'
  cases e using ENat.recTopCoe with
  | top =>
    cases e' using ENat.recTopCoe with
    | top => exact le_rfl
    | coe j =>
      simp only [Gmap, OrderDual.ofDual_toDual, ENat.natCast_ne_top, ite_false, ite_true]
      exact trivial
  | coe k =>
    cases e' using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe j =>
      simp only [Gmap, OrderDual.ofDual_toDual, ENat.natCast_ne_top, ite_false,
        ENat.toNat_natCast]
      exact le_a_iff.2 (by exact_mod_cast h)

/-- Every increasing sequence in `Chain` is eventually constant. -/
theorem chain_stabilizes (f : ℕ → Chain) (hf : Monotone f) : ∃ n, ∀ m, n ≤ m → f m = f n := by
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition (α := Chain) ⟨f, hf⟩
  exact ⟨n, fun m hm => (hn m hm).symm⟩

/-- The rank of a point of `Fork` in `Chain`. -/
def rank : Fork → Chain
  | Sum.inl n => OrderDual.toDual (n : ℕ∞)
  | Sum.inr _ => OrderDual.toDual ⊤

theorem rank_strictMono : StrictMono rank := by
  intro x y hxy
  have hle : x ≤ y := hxy.le
  have hne : x ≠ y := hxy.ne
  rcases x with m | b <;> rcases y with n | b'
  · have h1 : n ≤ m := hle
    have h2 : n ≠ m := fun h => hne (by rw [h])
    exact OrderDual.toDual_lt_toDual.2 (by exact_mod_cast lt_of_le_of_ne h1 h2)
  · exact False.elim hle
  · exact OrderDual.toDual_lt_toDual.2 (ENat.natCast_lt_top _)
  · exact absurd (congrArg Sum.inr hle) hne

/-- Every increasing sequence in `Fork` is eventually constant. -/
theorem fork_stabilizes (f : ℕ → Fork) (hf : Monotone f) : ∃ n, ∀ m, n ≤ m → f m = f n := by
  obtain ⟨n, hn⟩ := chain_stabilizes (rank ∘ f) (rank_strictMono.monotone.comp hf)
  refine ⟨n, fun m hm => ?_⟩
  by_contra hne
  exact (rank_strictMono (lt_of_le_of_ne (hf hm) (Ne.symm hne))).ne (hn m hm).symm

theorem iterate_shift (c : Chain) (n : ℕ) :
    shift^[n] c = OrderDual.toDual (OrderDual.ofDual c + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    simp only [shift, OrderDual.ofDual_toDual, Nat.cast_succ, add_assoc]

theorem shift_stronglyOrderStable : StronglyOrderStable shift := by
  have htop : ∀ e : ℕ∞, e + 1 ≤ e → e = ⊤ := fun e he => by
    cases e using ENat.recTopCoe with
    | top => rfl
    | coe k => exact absurd (by exact_mod_cast he : k + 1 ≤ k) (by omega)
  refine ⟨OrderDual.toDual ⊤, by simp [shift], fun w hw => ?_, fun v hv => ?_, fun v _ => ?_⟩
  · change OrderDual.toDual (OrderDual.ofDual w + 1) = w at hw
    exact congrArg OrderDual.toDual (htop _ (le_of_eq (congrArg OrderDual.ofDual hw)))
  · have hv' : OrderDual.ofDual v = ⊤ := htop _ hv
    have hc : ∀ n, shift^[n] v = OrderDual.toDual ⊤ := fun n => by
      rw [iterate_shift, hv', top_add]
    refine ⟨fun a b _ => by dsimp only; rw [hc, hc], ?_⟩
    rw [show (fun n => shift^[n] v) = fun _ => OrderDual.toDual ⊤ from funext hc, Set.range_const]
    exact isLUB_singleton
  · refine ⟨fun a b hab => ?_, ?_⟩
    · dsimp only
      rw [iterate_shift, iterate_shift]
      exact OrderDual.toDual_le_toDual.2 (add_le_add le_rfl (by exact_mod_cast hab))
    · refine ⟨fun x _ => show OrderDual.ofDual x ≤ ⊤ from le_top, fun b hb => ?_⟩
      induction b using OrderDual.rec with
      | toDual e =>
      change ⊤ ≤ e
      cases e using ENat.recTopCoe with
      | top => exact le_rfl
      | coe k =>
        exfalso
        have := hb ⟨k + 1, rfl⟩
        dsimp only at this
        rw [iterate_shift] at this
        have h1 : OrderDual.ofDual v + ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) :=
          OrderDual.toDual_le_toDual.1 this
        have h2 : ((k + 1 : ℕ) : ℕ∞) ≤ k := le_trans le_add_self h1
        exact absurd (by exact_mod_cast h2 : k + 1 ≤ k) (by omega)

theorem iterate_Smap (n : ℕ) : Smap^[n] (.a 0) = .a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', ih]; rfl

theorem Smap_not_stronglyOrderStable : ¬ StronglyOrderStable Smap := by
  rintro ⟨u, -, huniq, -, hdown⟩
  have hu : Fork.bot₁ = u := huniq .bot₁ rfl
  subst hu
  obtain ⟨-, hglb⟩ := hdown (.a 0) (show Fork.a 1 ≤ Fork.a 0 from le_a_iff.2 (Nat.zero_le 1))
  have hlb : Fork.bot₂ ∈ lowerBounds (range fun n => Smap^[n] (Fork.a 0)) := by
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [iterate_Smap]
    trivial
  have h := hglb.2 hlb
  change (true : Bool) = false at h
  exact Bool.noConfusion h

/-- **Lemma 5.2.2 (ii) and Theorem 5.2.3 fail with the book's order continuity**: `(Fork, S)` and
`(Chain, Ŝ)` are strongly semiconjugate under order preserving, order continuous `F` and `G`,
and `Ŝ` is strongly order stable, but `S` is not. -/
theorem theorem_5_2_3_fails :
    IsStronglySemiconj Smap shift Fmap Gmap ∧ Monotone Fmap ∧ Monotone Gmap ∧
      OrderContinuous Fmap ∧ OrderContinuous Gmap ∧ StronglyOrderStable shift ∧
      ¬ StronglyOrderStable Smap :=
  ⟨isStronglySemiconj, Fmap_mono, Gmap_mono,
    orderContinuous_of_stabilizes fork_stabilizes Fmap_mono,
    orderContinuous_of_stabilizes chain_stabilizes Gmap_mono, shift_stronglyOrderStable,
    Smap_not_stronglyOrderStable⟩

/-- **Theorem 5.2.4 fails with its stated hypothesis on `G`**: reversing the order of `Chain`
gives order-reversing `F, G` with `wₙ ↓ w ⟹ Gwₙ ↑ Gw`, and `Ŝ` strongly order stable, but `S` is
not strongly order stable. -/
theorem theorem_5_2_4_fails :
    IsStronglySemiconj Smap (dualMap shift) (OrderDual.toDual ∘ Fmap) (Gmap ∘ OrderDual.ofDual) ∧
      Antitone (OrderDual.toDual ∘ Fmap) ∧ Antitone (Gmap ∘ OrderDual.ofDual) ∧
      AntiContinuousDown (Gmap ∘ OrderDual.ofDual) ∧ StronglyOrderStable (dualMap shift) ∧
      ¬ StronglyOrderStable Smap := by
  refine ⟨⟨isStronglySemiconj.1, fun c => congrArg OrderDual.toDual (isStronglySemiconj.2 _)⟩,
    fun _ _ h => Fmap_mono h, fun _ _ h => Gmap_mono h, fun f w hf hw => ?_,
    (stronglyOrderStable_dual_iff shift).2 shift_stronglyOrderStable,
    Smap_not_stronglyOrderStable⟩
  exact orderContinuous_of_stabilizes chain_stabilizes Gmap_mono (OrderDual.ofDual ∘ f)
    (OrderDual.ofDual w) (fun _ _ h => hf h) hw

end SemiconjCounterexample

end SargentStachurski.ADPTransformations
