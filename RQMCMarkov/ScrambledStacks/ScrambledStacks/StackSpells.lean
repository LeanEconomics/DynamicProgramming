/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.StackDyadic

/-! # Spells of the 7/8 chain driven by scrambled stacks (post #3, codes (ii) and (iii))

Post #3: with per-state Sobol stacks, digitally shifted (ii) or Owen-scrambled (iii), "in the
two-state chain every spell lasts exactly 8 periods, rather than being geometric with mean 8".
`MarkovDriving` proved this only for rotors (`rotor78_spells_not_geometric`). Here it is proved
for both randomisations, on the good event (probability one), in the corrected form below.

**Mechanism.** For `stackChain78` the departure `k` from state `0` leaves iff the stack point
exceeds `7/8`, i.e. (on the good event) iff its first 3 scrambled digits are `111`; from state
`1` it leaves iff the point is `≤ 1/8`, i.e. iff they are `000` (`stay78_iff`). The first 3
scrambled digits depend only on `k mod 8` and run over all of `{0,1}^3` on each aligned block of
8 (`StackNet`), so there is one residue `r_i < 8` such that departure `k` from `i` leaves iff
`k ≡ r_i (mod 8)` (`exists_leaveResidue78`), the same in every block.

**Spells.** In a stack path, a stay in state `i` uses consecutive entries of stack `i`
(`stackPath_stay_iff`), and a spell after the first one in `i` starts right after a leaving
departure (`not_stay_prev_of_spellStart`). Hence (`spells_stackChain78`), for every good flip
table, every starting state and every state `i`, there is `r < 8` with
* the first spell in `i` lasting exactly `r + 1` periods (`runLength = r + 1`), and
* every later spell in `i` lasting exactly `8` periods.
**Law of `r`** (`owen_firstSpell78`, `shift_firstSpell78`, and for a chain started in `i`
`owen_runLength_first78`, `shift_runLength_first78`): `r` is uniform on `{0, …, 7}` under Owen
scrambling and under the digital shift: the first spell length is uniform on `{1, …, 8}`, with
mean `4.5`, not geometric with mean `8`.

**Correction** (post #3, "every spell lasts exactly 8 periods"): every spell *except the first
one in each state* lasts exactly 8 periods; the first spell in state `i` lasts `r_i + 1` periods
with `r_i` uniform on `{0, …, 7}`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory Finset

/-! ### Dyadic comparisons and the leaving residue -/

/-- On non-eventually-constant digits, `x ≤ a / 2^m` iff the first `m` digits are below `a`. -/
theorem binaryVal_le_div_iff {b : ℕ → Bool} (hb : NotEventuallyConst b) (a m : ℕ) :
    binaryVal b ≤ (a : ℝ) / 2 ^ m ↔ digitPrefix b m < a := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  constructor
  · intro h
    by_contra hcon
    have hk : (a : ℝ) ≤ (digitPrefix b m : ℕ) := by exact_mod_cast not_lt.1 hcon
    have h2 := digitPrefix_div_lt_binaryVal hb m
    have h3 : (a : ℝ) / 2 ^ m ≤ (digitPrefix b m : ℝ) / 2 ^ m :=
      div_le_div_of_nonneg_right hk hp.le
    linarith
  · intro h
    have hk : ((digitPrefix b m : ℕ) : ℝ) + 1 ≤ a := by exact_mod_cast h
    exact (binaryVal_le_digitPrefix_add_one_div b m).trans
      (div_le_div_of_nonneg_right hk hp.le)

/-- The scrambled digit prefix that makes a departure from `i` leave: `111` (`= 7`) from
state `0`, `000` (`= 0`) from state `1`. -/
def leaveTarget78 (i : Fin 2) : ℕ := if i = 0 then 7 else 0

/-- `cs_{0,1} = 7/8` and `cs_{1,1} = 1/8` for `stackChain78`. -/
theorem cumProb_stackChain78_one (i : Fin 2) :
    cumProb stackChain78 i 1 = ((if i = 0 then 7 else 1 : ℕ) : ℝ) / 2 ^ 3 := by
  have h := cumProb_succ stackChain78 i 0
  simp only [Fin.val_zero, zero_add, cumProb_zero] at h
  rw [h]
  fin_cases i <;> simp [stackChain78] <;> norm_num

/-- From state `0` of the 7/8 chain a departure stays iff its first 3 scrambled digits are not
`111` (good event). -/
theorem stay78_zero_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (k : ℕ) :
    step stackChain78 0 (scrambledStack f 0 k) = 0 ↔
      digitPrefix (scrambledDigit (f 0) k) 3 ≠ 7 := by
  have hlt := step_lt_iff isStochastic_stackChain78 0 (scrambledStack_mem_Icc f 0 k).2
    (le_refl 1)
  have hc : cumProb stackChain78 0 1 = ((7 : ℕ) : ℝ) / 2 ^ 3 := by
    rw [cumProb_stackChain78_one]
    rfl
  rw [hc] at hlt
  have hb := binaryVal_le_div_iff (hf 0 k) 7 3
  have h8 : digitPrefix (scrambledDigit (f 0) k) 3 < 8 := digitPrefix_lt _ 3
  change ((step stackChain78 0 (binaryVal (scrambledDigit (f 0) k)) : ℕ) < 1 ↔
    binaryVal (scrambledDigit (f 0) k) ≤ ((7 : ℕ) : ℝ) / 2 ^ 3) at hlt
  change step stackChain78 0 (binaryVal (scrambledDigit (f 0) k)) = 0 ↔ _
  have key := hlt.trans hb
  rw [Fin.ext_iff, Fin.val_zero]
  omega

/-- From state `1` of the 7/8 chain a departure stays iff its first 3 scrambled digits are not
`000` (good event). -/
theorem stay78_one_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (k : ℕ) :
    step stackChain78 1 (scrambledStack f 1 k) = 1 ↔
      digitPrefix (scrambledDigit (f 1) k) 3 ≠ 0 := by
  have hlt := step_lt_iff isStochastic_stackChain78 1 (scrambledStack_mem_Icc f 1 k).2
    (le_refl 1)
  have hc : cumProb stackChain78 1 1 = ((1 : ℕ) : ℝ) / 2 ^ 3 := by
    rw [cumProb_stackChain78_one]
    rfl
  rw [hc] at hlt
  have hb := binaryVal_le_div_iff (hf 1 k) 1 3
  change ((step stackChain78 1 (binaryVal (scrambledDigit (f 1) k)) : ℕ) < 1 ↔
    binaryVal (scrambledDigit (f 1) k) ≤ ((1 : ℕ) : ℝ) / 2 ^ 3) at hlt
  change step stackChain78 1 (binaryVal (scrambledDigit (f 1) k)) = 1 ↔ _
  have key := hlt.trans hb
  have h2 := (step stackChain78 1 (binaryVal (scrambledDigit (f 1) k))).isLt
  rw [Fin.ext_iff, Fin.val_one]
  omega

/-- **When a departure stays** (good event): departure `k` from `i` stays in `i` iff the first
3 scrambled digits of stack point `k` differ from `leaveTarget78 i`. -/
theorem stay78_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin 2) (k : ℕ) :
    step stackChain78 i (scrambledStack f i k) = i ↔
      digitPrefix (scrambledDigit (f i) k) 3 ≠ leaveTarget78 i := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · exact stay78_zero_iff hf k
  · exact stay78_one_iff hf k

/-- **The leaving residue** (good event): there is `r < 8` such that departure `k` from `i`
leaves iff `k ≡ r (mod 8)`. -/
theorem exists_leaveResidue78 {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin 2) :
    ∃ r < 8, ∀ k, step stackChain78 i (scrambledStack f i k) ≠ i ↔ k % 8 = r := by
  have himg := image_digitPrefix_scrambledDigit_block (f i) 0 3
  have ht : leaveTarget78 i ∈ range (2 ^ 3) := by
    rw [mem_range]
    unfold leaveTarget78
    split_ifs <;> norm_num
  rw [← himg] at ht
  obtain ⟨r, hr, hrt⟩ := mem_image.1 ht
  simp only [zero_mul, zero_add] at hrt
  refine ⟨r, by simpa using hr, fun k => ?_⟩
  rw [Ne, stay78_iff hf i k, not_not, ← digitPrefix_scrambledDigit_mod (f i) k 3, ← hrt]
  constructor
  · intro h
    have := injOn_digitPrefix_scrambledDigit (f i) 3
      (mem_range.2 (Nat.mod_lt k (by norm_num))) hr h
    simpa using this
  · intro h
    rw [show 2 ^ 3 = 8 by norm_num, h]

/-! ### Runs in a stack path -/

variable {n : ℕ}

/-- While the path stays in `i`, its occupation count of `i` grows by one per period. -/
theorem occCount_add_of_forall_eq {S : Type*} [DecidableEq S] (path : ℕ → S) {i : S} {t : ℕ} :
    ∀ m, (∀ m' < m, path (t + m') = i) → occCount path i (t + m) = occCount path i t + m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [← add_assoc, occCount_succ, ih fun m' hm' => h m' (by omega), h m (by omega)]
    simp only [ite_true]
    ring

/-- **A stay uses consecutive stack entries**: from `path t = i`, the path stays in `i` at
`t, …, t + m` iff the departures `N_i(t), …, N_i(t) + m − 1` from `i` all stay. -/
theorem stackPath_stay_iff (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ) {i : Fin n}
    {t : ℕ} (ht : stackPath P x₀ v t = i) (m : ℕ) :
    (∀ m' ≤ m, stackPath P x₀ v (t + m') = i) ↔
      ∀ m' < m, step P i (v i (occCount (stackPath P x₀ v) i t + m')) = i := by
  induction m with
  | zero =>
    simp only [Nat.le_zero, forall_eq, add_zero, ht, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true]
  | succ m ih =>
    constructor
    · intro h m' hm'
      have hrun : ∀ m'' < m + 1, stackPath P x₀ v (t + m'') = i := fun m'' h'' => h m'' (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm' with hm' | rfl
      · exact (ih.1 fun m'' h'' => h m'' (by omega)) m' hm'
      · have hsucc := stackDrive_succ_of_eq (step P) x₀ v (h m' (by omega))
        rw [occCount_add_of_forall_eq _ m' fun m'' h'' => hrun m'' (by omega)] at hsucc
        rw [← hsucc]
        exact h (m' + 1) le_rfl
    · intro h m' hm'
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hm') with hm' | rfl
      · exact (ih.2 fun m'' h'' => h m'' (by omega)) m' (by omega)
      · have hprev := ih.2 fun m'' h'' => h m'' (by omega)
        have hsucc := stackDrive_succ_of_eq (step P) x₀ v (hprev m le_rfl)
        rw [occCount_add_of_forall_eq _ m fun m'' h'' => hprev m'' (by omega)] at hsucc
        rw [← add_assoc]
        exact hsucc.trans (h m (by omega))

/-- The exit step of a run: if the path is in `i` at `t, …, t + m`, then
`path (t + m + 1) = step P i (v i (N_i(t) + m))`. -/
theorem stackPath_exit_eq (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ) {i : Fin n}
    {t m : ℕ} (h : ∀ m' ≤ m, stackPath P x₀ v (t + m') = i) :
    stackPath P x₀ v (t + m + 1) = step P i (v i (occCount (stackPath P x₀ v) i t + m)) := by
  have hsucc := stackDrive_succ_of_eq (step P) x₀ v (h m le_rfl)
  rwa [occCount_add_of_forall_eq _ m fun m'' h'' => h m'' (by omega)] at hsucc

/-- The visit with index `k` exists before any time with `N_i(t) = k + 1`. -/
theorem exists_lt_occCount_eq {S : Type*} [DecidableEq S] (path : ℕ → S) (i : S) {k : ℕ} :
    ∀ t, occCount path i t = k + 1 → ∃ t' < t, path t' = i ∧ occCount path i t' = k := by
  intro t
  induction t with
  | zero => intro h; simp [occCount_zero] at h
  | succ t ih =>
    intro h
    rw [occCount_succ] at h
    by_cases hp : path t = i
    · simp only [hp, ite_true] at h
      exact ⟨t, by omega, hp, by omega⟩
    · simp only [hp, ite_false, add_zero] at h
      obtain ⟨t', ht', h1, h2⟩ := ih h
      exact ⟨t', by omega, h1, h2⟩

/-- **A spell starts right after a leaving departure**: if `t` starts a spell and `i` was
visited before `t`, the previous departure from `i` (index `N_i(t) − 1`) left `i`. -/
theorem not_stay_prev_of_spellStart (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ)
    {i : Fin n} {t : ℕ} (hs : IsSpellStart (stackPath P x₀ v) t)
    (hk : occCount (stackPath P x₀ v) i t ≠ 0) :
    step P i (v i (occCount (stackPath P x₀ v) i t - 1)) ≠ i := by
  set path := stackPath P x₀ v with hpath
  obtain ⟨k, hk1⟩ : ∃ k, occCount path i t = k + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hk).symm⟩
  obtain ⟨t', ht't, ht'i, ht'k⟩ := exists_lt_occCount_eq path i t hk1
  rw [hk1, Nat.add_sub_cancel, ← ht'k]
  intro hstay
  have hnext : path (t' + 1) = i := (stackDrive_succ_of_eq (step P) x₀ v ht'i).trans hstay
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt ht't) with hlt | heq
  · have h1 : occCount path i (t' + 2) ≤ occCount path i t := occCount_mono path i hlt
    have h2 : occCount path i (t' + 2) = k + 2 := by
      rw [occCount_succ, occCount_succ, ht'k, ht'i, hnext]
      simp
    omega
  · rcases hs with h0 | hprev
    · omega
    · apply hprev
      rw [← heq, Nat.succ_sub_one, ht'i]
      exact hnext.symm

/-! ### The spells of the 7/8 chain -/

/-- **Spells of the 7/8 chain driven by scrambled stacks** (post #3, codes (ii) and (iii)):
for every good flip table, starting state and state `i` there is `r < 8` such that the first
spell in `i` lasts exactly `r + 1` periods and every later spell in `i` lasts exactly `8`
periods (`runLength` censored at any `T` beyond the exit). -/
theorem spells_stackChain78 {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (x₀ i : Fin 2) :
    ∃ r < 8, (∀ k, step stackChain78 i (scrambledStack f i k) ≠ i ↔ k % 8 = r) ∧
      (∀ t T, stackPath stackChain78 x₀ (scrambledStack f) t = i →
        occCount (stackPath stackChain78 x₀ (scrambledStack f)) i t = 0 → t + (r + 1) < T →
          runLength (stackPath stackChain78 x₀ (scrambledStack f)) t T = r + 1) ∧
      (∀ t T, IsSpellStart (stackPath stackChain78 x₀ (scrambledStack f)) t →
        stackPath stackChain78 x₀ (scrambledStack f) t = i →
        occCount (stackPath stackChain78 x₀ (scrambledStack f)) i t ≠ 0 → t + 8 < T →
          runLength (stackPath stackChain78 x₀ (scrambledStack f)) t T = 8) := by
  obtain ⟨r, hr8, hr⟩ := exists_leaveResidue78 hf i
  set path := stackPath stackChain78 x₀ (scrambledStack f) with hpath
  refine ⟨r, hr8, hr, fun t T ht hk hT => ?_, fun t T hs ht hk hT => ?_⟩
  · -- first spell: departures `0, …, r − 1` stay, departure `r` leaves
    have hstay : ∀ m' ≤ r, path (t + m') = i := by
      refine (stackPath_stay_iff stackChain78 x₀ (scrambledStack f) ht r).2 fun m' hm' => ?_
      rw [hk, zero_add]
      by_contra hcon
      have := (hr m').1 hcon
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hexit : path (t + r + 1) ≠ i := by
      rw [hpath, stackPath_exit_eq stackChain78 x₀ (scrambledStack f) hstay, ← hpath, hk,
        zero_add]
      exact (hr r).2 (Nat.mod_eq_of_lt hr8)
    refine runLength_eq_of_exit hT (fun m hm => ?_) ?_
    · rw [hstay m (by omega), ← ht]
    · rw [ht, ← add_assoc]
      exact hexit
  · -- later spell: the previous departure left, so the next 7 stay and the 8th leaves
    have hprev := not_stay_prev_of_spellStart stackChain78 x₀ (scrambledStack f) hs hk
    have hres := (hr _).1 hprev
    set k := occCount path i t with hkdef
    have hkk : occCount (stackPath stackChain78 x₀ (scrambledStack f)) i t = k := rfl
    have hstay : ∀ m' ≤ 7, path (t + m') = i := by
      refine (stackPath_stay_iff stackChain78 x₀ (scrambledStack f) ht 7).2 fun m' hm' => ?_
      by_contra hcon
      have := (hr _).1 hcon
      omega
    have hexit : path (t + 7 + 1) ≠ i := by
      rw [hpath, stackPath_exit_eq stackChain78 x₀ (scrambledStack f) hstay, ← hpath]
      refine (hr _).2 ?_
      omega
    refine runLength_eq_of_exit hT (fun m hm => ?_) ?_
    · rw [hstay m (by omega), ht]
    · rw [ht]
      exact hexit

/-! ### The law of the first spell -/

/-- On the good event, "departures `0, …, r − 1` from `i` stay and departure `r` leaves" iff the
first 3 scrambled digits of stack point `r` are `leaveTarget78 i` (for `r < 8`). -/
theorem firstSpell78_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin 2) {r : ℕ}
    (hr8 : r < 8) :
    ((∀ m < r, step stackChain78 i (scrambledStack f i m) = i) ∧
        step stackChain78 i (scrambledStack f i r) ≠ i) ↔
      digitPrefix (scrambledDigit (f i) r) 3 = leaveTarget78 i := by
  obtain ⟨r₀, hr₀8, hr₀⟩ := exists_leaveResidue78 hf i
  constructor
  · rintro ⟨-, h⟩
    rw [Ne, stay78_iff hf i r, not_not] at h
    exact h
  · intro h
    have hleave : step stackChain78 i (scrambledStack f i r) ≠ i := by
      rw [Ne, stay78_iff hf i r, not_not]
      exact h
    have hrr : r = r₀ := by
      have := (hr₀ r).1 hleave
      rwa [Nat.mod_eq_of_lt hr8] at this
    refine ⟨fun m hm => ?_, hleave⟩
    by_contra hcon
    have := (hr₀ m).1 hcon
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- `2^{-3} = 1/8` in `ℝ≥0∞`. -/
theorem two_inv_pow_three : (2⁻¹ : ENNReal) ^ 3 = 8⁻¹ := by
  rw [← ENNReal.inv_pow]
  norm_num

/-- **The first spell under Owen scrambling is uniform** (post #3, code (iii)): for `r < 8`,
the probability that departures `0, …, r − 1` from `i` stay and departure `r` leaves is
`1/8`. -/
theorem owen_firstSpell78 (i : Fin 2) {r : ℕ} (hr8 : r < 8) :
    owenMeasure 2 {ω | (∀ m < r, step stackChain78 i (scrambledStack (owenTable ω) i m) = i) ∧
      step stackChain78 i (scrambledStack (owenTable ω) i r) ≠ i} = 8⁻¹ := by
  have hae : {ω : Fin 2 × ℕ × ℕ → Bool |
      (∀ m < r, step stackChain78 i (scrambledStack (owenTable ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (owenTable ω) i r) ≠ i} =ᵐ[owenMeasure 2]
      {ω | digitPrefix (scrambledDigit (owenTable ω i) r) 3 = leaveTarget78 i} :=
    (ae_isGoodTable_owen 2).mono fun ω hω => propext (firstSpell78_iff hω i hr8)
  rw [measure_congr hae, owen_digitPrefix_eq i r (by unfold leaveTarget78; split_ifs <;> norm_num),
    two_inv_pow_three]

/-- **The first spell under the digital shift is uniform** (post #3, code (ii)). -/
theorem shift_firstSpell78 (i : Fin 2) {r : ℕ} (hr8 : r < 8) :
    shiftMeasure 2 {ω | (∀ m < r, step stackChain78 i (scrambledStack (shiftFlips ω) i m) = i) ∧
      step stackChain78 i (scrambledStack (shiftFlips ω) i r) ≠ i} = 8⁻¹ := by
  have hae : {ω : Fin 2 × ℕ → Bool |
      (∀ m < r, step stackChain78 i (scrambledStack (shiftFlips ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (shiftFlips ω) i r) ≠ i} =ᵐ[shiftMeasure 2]
      {ω | digitPrefix (scrambledDigit (shiftFlips ω i) r) 3 = leaveTarget78 i} :=
    (ae_isGoodTable_shift 2).mono fun ω hω => propext (firstSpell78_iff hω i hr8)
  rw [measure_congr hae, shift_digitPrefix_eq i r (by unfold leaveTarget78; split_ifs <;> norm_num),
    two_inv_pow_three]

/-- For a chain started in `i`, the first spell has length `r + 1` iff departures
`0, …, r − 1` stay and departure `r` leaves. -/
theorem runLength_zero_stackPath_iff (P : Fin n → Fin n → ℝ) (i : Fin n) (v : Fin n → ℕ → ℝ)
    {r T : ℕ} (hT : r + 1 < T) :
    runLength (stackPath P i v) 0 T = r + 1 ↔
      (∀ m < r, step P i (v i m) = i) ∧ step P i (v i r) ≠ i := by
  have h0 : stackPath P i v 0 = i := stackDrive_zero _ _ _
  have hocc : occCount (stackPath P i v) i 0 = 0 := occCount_zero _ _
  rw [runLength_eq_iff (by omega), h0]
  simp only [zero_add]
  have hst := stackPath_stay_iff P i v h0 r
  simp only [hocc, zero_add] at hst
  constructor
  · rintro ⟨h1, h2⟩
    have hrun : ∀ m' ≤ r, stackPath P i v m' = i := fun m' hm' => h1 m' (by omega)
    refine ⟨hst.1 hrun, ?_⟩
    have := stackPath_exit_eq P i v (t := 0) (m := r) (by simpa using hrun)
    simp only [zero_add, hocc] at this
    rw [← this]
    exact h2
  · rintro ⟨h1, h2⟩
    have hrun := hst.2 h1
    refine ⟨fun m hm => hrun m (by omega), ?_⟩
    have := stackPath_exit_eq P i v (t := 0) (m := r) (by simpa using hrun)
    simp only [zero_add, hocc] at this
    rw [this]
    exact h2

/-- **First spell of the 7/8 chain started in `i`, Owen scrambling**: its length is uniform on
`{1, …, 8}`: `P(runLength = r + 1) = 1/8` for `r < 8` (censoring `T > r + 1`). -/
theorem owen_runLength_first78 (i : Fin 2) {r T : ℕ} (hr8 : r < 8) (hT : r + 1 < T) :
    owenMeasure 2 {ω | runLength (stackPath stackChain78 i (scrambledStack (owenTable ω))) 0 T =
      r + 1} = 8⁻¹ := by
  have e : {ω : Fin 2 × ℕ × ℕ → Bool |
      runLength (stackPath stackChain78 i (scrambledStack (owenTable ω))) 0 T = r + 1} =
      {ω | (∀ m < r, step stackChain78 i (scrambledStack (owenTable ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (owenTable ω) i r) ≠ i} := by
    ext ω
    exact runLength_zero_stackPath_iff stackChain78 i _ hT
  rw [e]
  exact owen_firstSpell78 i hr8

/-- **First spell of the 7/8 chain started in `i`, digital shift**: uniform on `{1, …, 8}`. -/
theorem shift_runLength_first78 (i : Fin 2) {r T : ℕ} (hr8 : r < 8) (hT : r + 1 < T) :
    shiftMeasure 2 {ω | runLength (stackPath stackChain78 i (scrambledStack (shiftFlips ω))) 0 T =
      r + 1} = 8⁻¹ := by
  have e : {ω : Fin 2 × ℕ → Bool |
      runLength (stackPath stackChain78 i (scrambledStack (shiftFlips ω))) 0 T = r + 1} =
      {ω | (∀ m < r, step stackChain78 i (scrambledStack (shiftFlips ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (shiftFlips ω) i r) ≠ i} := by
    ext ω
    exact runLength_zero_stackPath_iff stackChain78 i _ hT
  rw [e]
  exact shift_firstSpell78 i hr8

end RQMCMarkov.ScrambledStacks
