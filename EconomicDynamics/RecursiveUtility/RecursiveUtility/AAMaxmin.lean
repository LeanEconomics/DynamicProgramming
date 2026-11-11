/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AABasics

/-!
# Maxmin expected utility and recursive multiple priors

Miao, §20.2.2, pp. 691–693: the Ellsberg paradox, Gilboa–Schmeidler maxmin expected utility,
the recursive multiple-priors utility (20.7) of Epstein–Wang, Epstein–Schneider rectangularity
and Hayashi's generalisation.

* `aa_maxmin Q u = inf_{q ∈ Q} E_q u`, with `aa_maxmin_le`, `aa_le_maxmin`, attainment on finite
  sets of priors (`aa_maxmin_isLeast`) and the special case of one prior (`aa_maxmin_singleton`).
* The Ellsberg paradox (p. 692): no single prior strictly prefers urn 1 for both bets
  (`aa_ellsberg_no_prior`), while maxmin utility with an interval of priors for urn 2 does
  (`aa_ellsberg_maxmin`).
* The uncertainty aggregator `R_t` of (20.7) is monotone, translation invariant, positively
  homogeneous and superadditive (`aa_maxmin_mono`, `aa_maxmin_add_const`, `aa_maxmin_smul`,
  `aa_maxmin_superadditive`).
* (20.7) on the event tree with a finite horizon (`aa_rmpU`); Hayashi's form `W(c, R(U'))`
  (`aa_hayashiU`) contains it (`aa_hayashiU_additive`).
* Rectangularity (p. 693): with rectangular priors (one-step-ahead priors chosen node by node), the
  time-zero utility `min_P E^P[∑ βᵗ u(c_t)]` satisfies the recursion (20.7)
  (`aa_rmpU_isLeast_selection`, `aa_rectangular_recursion`); for a non-rectangular set it can fail
  (`aa_nonrectangular_counterexample`).

Departures: the book's (20.7) is on an infinite horizon with a Markov correspondence `P(·|s)`; here
it
is on a finite event tree, with sets of priors that are finite where a minimum must be attained.
The Choquet expected utility of footnote 1 is not formalised (cited, no derivation).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- The maxmin (Gilboa–Schmeidler) utility `U = inf_{q ∈ Q} ∫ u dq` over a set `Q` of priors. -/
noncomputable def aa_maxmin (Q : Set (S → ℝ)) (u : S → ℝ) : ℝ := sInf ((fun q => aa_E q u) '' Q)

/-- Expected utility under a distribution is bounded below by `−∑ |u|`. -/
theorem aa_E_ge_neg {q : S → ℝ} (hq : SS.IsDistribution q) (u : S → ℝ) :
    -∑ s, |u s| ≤ aa_E q u := by
  unfold aa_E
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have hq1 : q s ≤ 1 := by
    rw [← hq.sum_eq_one]
    exact Finset.single_le_sum (fun s _ => hq.nonneg s) (Finset.mem_univ s)
  have h1 : |q s * u s| ≤ |u s| := by
    rw [abs_mul, abs_of_nonneg (hq.nonneg s)]
    exact mul_le_of_le_one_left (abs_nonneg _) hq1
  linarith [neg_abs_le (q s * u s)]

theorem aa_maxmin_bdd {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q) (u : S → ℝ) :
    BddBelow ((fun q => aa_E q u) '' Q) :=
  ⟨-∑ s, |u s|, by rintro _ ⟨q, hq, rfl⟩; exact aa_E_ge_neg (hQ q hq) u⟩

/-- Maxmin utility is at most the expected utility under every prior in `Q`. -/
theorem aa_maxmin_le {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q) (u : S → ℝ)
    {q : S → ℝ} (hq : q ∈ Q) : aa_maxmin Q u ≤ aa_E q u :=
  csInf_le (aa_maxmin_bdd hQ u) ⟨q, hq, rfl⟩

/-- A lower bound for every prior is a lower bound for maxmin utility. -/
theorem aa_le_maxmin {Q : Set (S → ℝ)} (hne : Q.Nonempty) (u : S → ℝ) {k : ℝ}
    (hk : ∀ q ∈ Q, k ≤ aa_E q u) : k ≤ aa_maxmin Q u :=
  le_csInf (hne.image _) (by rintro _ ⟨q, hq, rfl⟩; exact hk q hq)

/-- On a finite nonempty set of priors the minimum is attained. -/
theorem aa_maxmin_attained {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hfin : Q.Finite) (hne : Q.Nonempty) (u : S → ℝ) :
    ∃ q ∈ Q, aa_maxmin Q u = aa_E q u := by
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image Q (fun q => aa_E q u) hfin hne
  exact ⟨q, hq, le_antisymm (aa_maxmin_le hQ u hq) (aa_le_maxmin hne u hmin)⟩

/-- Miao, p. 692: with one prior `Q = {p}`, maxmin utility is expected utility. -/
theorem aa_maxmin_singleton (p u : S → ℝ) : aa_maxmin {p} u = aa_E p u := by
  simp [aa_maxmin]

/-- Monotonicity of the uncertainty aggregator `R_t` of (20.7). -/
theorem aa_maxmin_mono {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q) (hne : Q.Nonempty)
    {x y : S → ℝ} (hxy : ∀ s, x s ≤ y s) : aa_maxmin Q x ≤ aa_maxmin Q y :=
  aa_le_maxmin hne y fun q hq => (aa_maxmin_le hQ x hq).trans (aa_E_mono (hQ q hq) hxy)

/-- Translation invariance `R(x + k) = R(x) + k`; in particular `R(k) = k`. -/
theorem aa_maxmin_add_const {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (x : S → ℝ) (k : ℝ) :
    aa_maxmin Q (fun s => x s + k) = aa_maxmin Q x + k := by
  have e : ∀ q ∈ Q, aa_E q (fun s => x s + k) = aa_E q x + k := fun q hq => by
    rw [aa_E_add, aa_E_const (hQ q hq)]
  apply le_antisymm
  · have : aa_maxmin Q (fun s => x s + k) - k ≤ aa_maxmin Q x :=
      aa_le_maxmin hne x fun q hq => by
        have := aa_maxmin_le hQ (fun s => x s + k) hq
        rw [e q hq] at this
        linarith
    linarith
  · exact aa_le_maxmin hne _ fun q hq => by
      rw [e q hq]
      linarith [aa_maxmin_le hQ x hq]

/-- The certainty-equivalent property `R(k) = k` of the maxmin aggregator. -/
theorem aa_maxmin_const {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (k : ℝ) : aa_maxmin Q (fun _ => k) = k := by
  have := aa_maxmin_add_const hQ hne (fun _ => 0) k
  have h0 : aa_maxmin Q (fun _ => (0 : ℝ)) = 0 := by
    apply le_antisymm
    · obtain ⟨q, hq⟩ := hne
      have := aa_maxmin_le hQ (fun _ => (0 : ℝ)) hq
      rwa [aa_E_const (hQ q hq)] at this
    · exact aa_le_maxmin hne _ fun q hq => by rw [aa_E_const (hQ q hq)]
  simpa [h0] using this

/-- Positive homogeneity `R(a x) = a R(x)` for `a ≥ 0`. -/
theorem aa_maxmin_smul {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (x : S → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    aa_maxmin Q (fun s => a * x s) = a * aa_maxmin Q x := by
  rcases ha.lt_or_eq with ha | ha
  · apply le_antisymm
    · have : aa_maxmin Q (fun s => a * x s) / a ≤ aa_maxmin Q x :=
        aa_le_maxmin hne x fun q hq => by
          rw [div_le_iff₀ ha, mul_comm, ← aa_E_smul]
          exact aa_maxmin_le hQ _ hq
      rwa [div_le_iff₀ ha, mul_comm] at this
    · exact aa_le_maxmin hne _ fun q hq => by
        rw [aa_E_smul]
        exact mul_le_mul_of_nonneg_left (aa_maxmin_le hQ x hq) ha.le
  · subst ha
    simp only [zero_mul]
    exact aa_maxmin_const hQ hne 0

/-- Superadditivity `R(x + y) ≥ R(x) + R(y)`, so with positive homogeneity `R` is concave. -/
theorem aa_maxmin_superadditive {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (x y : S → ℝ) :
    aa_maxmin Q x + aa_maxmin Q y ≤ aa_maxmin Q (fun s => x s + y s) :=
  aa_le_maxmin hne _ fun q hq => by
    rw [aa_E_add]
    exact add_le_add (aa_maxmin_le hQ x hq) (aa_maxmin_le hQ y hq)

/-! ### The Ellsberg paradox (p. 692) -/

/-- **The Ellsberg paradox** (Miao, p. 692): no subjective probability `(q_B, q_W)` on the colour of
the ball drawn from urn 2 makes an expected-utility maximiser strictly prefer urn 1 (known
composition `50/50`) both for the bet on black and for the bet on white. Here `a = u(100)`,
`b = u(0)`. -/
theorem aa_ellsberg_no_prior (a b qB qW : ℝ) (hq : qB + qW = 1) :
    ¬ (qB * a + qW * b < a / 2 + b / 2 ∧ qW * a + qB * b < a / 2 + b / 2) := by
  rintro ⟨h1, h2⟩
  have : (qB + qW) * (a + b) < a + b := by nlinarith
  rw [hq, one_mul] at this
  exact lt_irrefl _ this

/-- The priors on urn 2 (state `true` = black): all distributions with `q(black) ∈ [l, h]`. -/
def aa_ellsbergPriors (l h : ℝ) : Set (Bool → ℝ) :=
  {q | SS.IsDistribution q ∧ l ≤ q true ∧ q true ≤ h}

/-- The prior with `q(black) = r`. -/
def aa_ellsbergPrior (r : ℝ) : Bool → ℝ := fun b => if b then r else 1 - r

theorem aa_ellsbergPrior_isDistribution {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    SS.IsDistribution (aa_ellsbergPrior r) :=
  ⟨fun b => by cases b <;> simp [aa_ellsbergPrior] <;> linarith, by simp [aa_ellsbergPrior]⟩

theorem aa_E_bool (q u : Bool → ℝ) : aa_E q u = q true * u true + q false * u false := by
  simp [aa_E, add_comm]

/-- Maxmin utility of the bet on black from urn 2: `l u(100) + (1 − l) u(0)` (`u(100) ≥ u(0)`). -/
theorem aa_ellsberg_black {l h a b : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h) (hh : h ≤ 1) (hab : b ≤ a) :
    aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then a else b) = l * a + (1 - l) * b := by
  have hD : ∀ q ∈ aa_ellsbergPriors l h, SS.IsDistribution q := fun q hq => hq.1
  have hmem : aa_ellsbergPrior l ∈ aa_ellsbergPriors l h :=
    ⟨aa_ellsbergPrior_isDistribution hl (hlh.trans hh), by simp [aa_ellsbergPrior],
      by simp [aa_ellsbergPrior, hlh]⟩
  apply le_antisymm
  · have := aa_maxmin_le hD (fun c => if c then a else b) hmem
    simpa [aa_E_bool, aa_ellsbergPrior] using this
  · refine aa_le_maxmin ⟨_, hmem⟩ _ fun q hq => ?_
    have hs := hq.1.sum_eq_one
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton] at hs
    rw [aa_E_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [show q false = 1 - q true by linarith]
    nlinarith [mul_nonneg (sub_nonneg.2 hq.2.1) (sub_nonneg.2 hab)]

/-- Maxmin utility of the bet on white from urn 2: `(1 − h) u(100) + h u(0)` (`u(100) ≥ u(0)`). -/
theorem aa_ellsberg_white {l h a b : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h) (hh : h ≤ 1) (hab : b ≤ a) :
    aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then b else a) = (1 - h) * a + h * b := by
  have hD : ∀ q ∈ aa_ellsbergPriors l h, SS.IsDistribution q := fun q hq => hq.1
  have hmem : aa_ellsbergPrior h ∈ aa_ellsbergPriors l h :=
    ⟨aa_ellsbergPrior_isDistribution (hl.trans hlh) hh, by simp [aa_ellsbergPrior, hlh],
      by simp [aa_ellsbergPrior]⟩
  apply le_antisymm
  · have := aa_maxmin_le hD (fun c => if c then b else a) hmem
    simp only [aa_E_bool, aa_ellsbergPrior, ↓reduceIte, Bool.false_eq_true] at this
    linarith
  · refine aa_le_maxmin ⟨_, hmem⟩ _ fun q hq => ?_
    have hs := hq.1.sum_eq_one
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton] at hs
    rw [aa_E_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [show q false = 1 - q true by linarith]
    nlinarith [mul_nonneg (sub_nonneg.2 hq.2.2) (sub_nonneg.2 hab)]

/-- **The Ellsberg paradox resolved by maxmin utility** (Miao, pp. 692–693). With the known urn 1
(`50/50`, one prior) and priors `q(black) ∈ [l, h]` for urn 2, `l < 1/2 < h`, and
`u(100) > u(0)`, the maxmin decision maker strictly prefers urn 1 for the bet on black and for the
bet on white. -/
theorem aa_ellsberg_maxmin {l h a b : ℝ} (hl : 0 ≤ l) (hl2 : l < 1 / 2) (hh2 : 1 / 2 < h)
    (hh : h ≤ 1) (hab : b < a) :
    aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then a else b) <
        aa_maxmin {aa_ellsbergPrior (1 / 2)} (fun c => if c then a else b) ∧
      aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then b else a) <
        aa_maxmin {aa_ellsbergPrior (1 / 2)} (fun c => if c then b else a) := by
  have hlh : l ≤ h := by linarith
  rw [aa_ellsberg_black hl hlh hh hab.le, aa_ellsberg_white hl hlh hh hab.le,
    aa_maxmin_singleton, aa_maxmin_singleton, aa_E_bool, aa_E_bool]
  simp only [aa_ellsbergPrior, ↓reduceIte, Bool.false_eq_true]
  constructor <;> nlinarith

/-! ### Recursive multiple priors (20.7) and Hayashi's form -/

/-- **(20.7)** (Miao, p. 693) on a finite event tree:
`U_t = u(c_t) + β min_{π ∈ P(·|h)} E_π U_{t+1}`,
`U_T = u(c_T)`; `P h` is the set of one-step-ahead priors at the node `h`. -/
noncomputable def aa_rmpU (u : ℝ → ℝ) (β : ℝ) (P : List S → Set (S → ℝ)) (c : List S → ℝ) :
    ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h => u (c h) + β * aa_maxmin (P h) fun s => aa_rmpU u β P c n (s :: h)

/-- Hayashi's (2005) form `U_t = W(c_t, R_t(U_{t+1}))` (Miao, p. 693), terminal utility
`U_T = ψ(c_T)`. -/
noncomputable def aa_hayashiU (W : ℝ → ℝ → ℝ) (ψ : ℝ → ℝ) (P : List S → Set (S → ℝ))
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => ψ (c h)
  | n + 1, h => W (c h) (aa_maxmin (P h) fun s => aa_hayashiU W ψ P c n (s :: h))

/-- Miao, p. 693: Hayashi's form with the additive aggregator `W(c, y) = u(c) + βy` is (20.7). -/
theorem aa_hayashiU_additive (u : ℝ → ℝ) (β : ℝ) (P : List S → Set (S → ℝ)) (c : List S → ℝ) :
    ∀ n h, aa_hayashiU (fun x y => u x + β * y) u P c n h = aa_rmpU u β P c n h
  | 0, h => rfl
  | n + 1, h => by
    simp only [aa_hayashiU, aa_rmpU]
    rw [show (fun s => aa_hayashiU (fun x y => u x + β * y) u P c n (s :: h)) =
      (fun s => aa_rmpU u β P c n (s :: h)) from
        funext fun s => aa_hayashiU_additive u β P c n (s :: h)]

/-- Expected discounted utility under a selection `q` of one-step-ahead priors (one at every node):
`V_t = u(c_t) + β E_{q(h)} V_{t+1}`. -/
noncomputable def aa_selU (u : ℝ → ℝ) (β : ℝ) (q : List S → S → ℝ) (c : List S → ℝ) :
    ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h => u (c h) + β * ∑ s, q h s * aa_selU u β q c n (s :: h)

/-- Under a selection `q` the recursion computes `E^q[∑_{t ≤ n} βᵗ u(c_t)]`, the expected discounted
utility under the probability measure on the tree that `q` generates. -/
theorem aa_selU_eq_sum (u : ℝ → ℝ) (β : ℝ) (q : List S → S → ℝ) (c : List S → ℝ) (n : ℕ)
    (h : List S) : aa_selU u β q c n h =
      ∑ t ∈ Finset.range (n + 1), β ^ t * aa_Ex q t (fun h' => u (c h')) h := by
  rw [aa_linear_unroll q β (fun h' => u (c h')) (fun h' => u (c h')) (aa_selU u β q c)
    (fun _ => rfl) (fun _ _ => rfl) n h, Finset.sum_range_succ]

/-- **Rectangularity** (Miao, p. 693; Epstein and Schneider 2003). With finitely many priors at
every
node, the recursive multiple-priors utility (20.7) is the minimum, over all rectangular selections
of priors (`q h ∈ P h` at every node), of the expected discounted utility: the time-zero utility
`min_P E^P[∑ βᵗ u(c_t)]` over the rectangular set satisfies the recursion. -/
theorem aa_rmpU_isLeast_selection (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) {P : List S → Set (S → ℝ)}
    (hP : ∀ h, ∀ q ∈ P h, SS.IsDistribution q) (hfin : ∀ h, (P h).Finite)
    (hne : ∀ h, (P h).Nonempty) (c : List S → ℝ) (n : ℕ) (h : List S) :
    IsLeast {y | ∃ q : List S → S → ℝ, (∀ h', q h' ∈ P h') ∧ y = aa_selU u β q c n h}
      (aa_rmpU u β P c n h) := by
  classical
  -- the minimising selection
  let qstar : ℕ → List S → S → ℝ := fun m h' =>
    (aa_maxmin_attained (hP h') (hfin h') (hne h') fun s => aa_rmpU u β P c m (s :: h')).choose
  have hq_mem : ∀ m h', qstar m h' ∈ P h' := fun m h' =>
    (aa_maxmin_attained (hP h') (hfin h') (hne h')
      fun s => aa_rmpU u β P c m (s :: h')).choose_spec.1
  have hq_eq : ∀ m h', aa_maxmin (P h') (fun s => aa_rmpU u β P c m (s :: h')) =
      aa_E (qstar m h') fun s => aa_rmpU u β P c m (s :: h') := fun m h' =>
    (aa_maxmin_attained (hP h') (hfin h') (hne h')
      fun s => aa_rmpU u β P c m (s :: h')).choose_spec.2
  -- lower bound for every selection
  have hlow : ∀ (q : List S → S → ℝ), (∀ h', q h' ∈ P h') →
      ∀ m h', aa_rmpU u β P c m h' ≤ aa_selU u β q c m h' := by
    intro q hq m
    induction m with
    | zero => intro h'; exact le_rfl
    | succ m ih =>
      intro h'
      simp only [aa_rmpU, aa_selU]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hβ)
      exact (aa_maxmin_le (hP h') _ (hq h')).trans (aa_E_mono (hP h' _ (hq h')) fun s => ih _)
  -- the selection attaining the bound, along the remaining horizon from `h`
  let qsel : List S → S → ℝ := fun h' => qstar (n + h.length - h'.length - 1) h'
  have hattain : ∀ m h', h'.length + m = n + h.length →
      aa_rmpU u β P c m h' = aa_selU u β qsel c m h' := by
    intro m
    induction m with
    | zero => intro h' _; rfl
    | succ m ih =>
      intro h' hlen
      have hidx : n + h.length - h'.length - 1 = m := by omega
      simp only [aa_rmpU, aa_selU]
      rw [hq_eq m h']
      congr 2
      simp only [aa_E, qsel, hidx]
      exact Finset.sum_congr rfl fun s _ => by
        rw [ih (s :: h') (by simp only [List.length_cons]; omega)]
  exact ⟨⟨qsel, fun h' => hq_mem _ h', hattain n h (by omega)⟩,
    by rintro y ⟨q, hq, rfl⟩; exact hlow q hq n h⟩

/-- **Rectangularity, two periods** (Miao, p. 693). For priors `q₀ ∈ P₀` over the first shock and
`q₁(s) ∈ P₁(s)` over the second, the minimum of `E^Q x` over the rectangular set of products
`Q(s, s') = q₀(s)q₁(s)(s')` equals the recursive value
`min_{q₀} E_{q₀}[min_{q₁(s)} E_{q₁(s)} x(s, ·)]`. -/
theorem aa_rectangular_recursion {S' : Type*} [Fintype S'] {P₀ : Set (S → ℝ)}
    {P₁ : S → Set (S' → ℝ)} (hP₀ : ∀ q ∈ P₀, SS.IsDistribution q)
    (hP₁ : ∀ s, ∀ q ∈ P₁ s, SS.IsDistribution q) (hfin₀ : P₀.Finite) (hfin₁ : ∀ s, (P₁ s).Finite)
    (hne₀ : P₀.Nonempty) (hne₁ : ∀ s, (P₁ s).Nonempty) (x : S × S' → ℝ) :
    IsLeast {y | ∃ q₀ ∈ P₀, ∃ q₁ : S → S' → ℝ, (∀ s, q₁ s ∈ P₁ s) ∧
        y = aa_E (fun ω => q₀ ω.1 * q₁ ω.1 ω.2) x}
      (aa_maxmin P₀ fun s => aa_maxmin (P₁ s) fun s' => x (s, s')) := by
  classical
  have hprod : ∀ (q₀ : S → ℝ) (q₁ : S → S' → ℝ), aa_E (fun ω => q₀ ω.1 * q₁ ω.1 ω.2) x =
      aa_E q₀ fun s => aa_E (q₁ s) fun s' => x (s, s') := fun q₀ q₁ => by
    simp only [aa_E, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  let q₁ : S → S' → ℝ := fun s =>
    (aa_maxmin_attained (hP₁ s) (hfin₁ s) (hne₁ s) fun s' => x (s, s')).choose
  have hq₁ : ∀ s, q₁ s ∈ P₁ s ∧ aa_maxmin (P₁ s) (fun s' => x (s, s')) =
      aa_E (q₁ s) fun s' => x (s, s') := fun s =>
    (aa_maxmin_attained (hP₁ s) (hfin₁ s) (hne₁ s) fun s' => x (s, s')).choose_spec
  obtain ⟨q₀, hq₀, hq₀e⟩ := aa_maxmin_attained hP₀ hfin₀ hne₀
    fun s => aa_maxmin (P₁ s) fun s' => x (s, s')
  refine ⟨⟨q₀, hq₀, q₁, fun s => (hq₁ s).1, ?_⟩, ?_⟩
  · rw [hprod, hq₀e]
    congr 1
    funext s
    exact (hq₁ s).2
  · rintro y ⟨r₀, hr₀, r₁, hr₁, rfl⟩
    rw [hprod]
    exact (aa_maxmin_le hP₀ _ hr₀).trans
      (aa_E_mono (hP₀ r₀ hr₀) fun s => aa_maxmin_le (hP₁ s) _ (hr₁ s))

/-- The two full-state priors of the counterexample: the first shock is a fair coin, and the second
is `true` (resp. `false`) for sure. -/
noncomputable def aa_nrPrior (b : Bool) : Bool × Bool → ℝ := fun ω => if ω.2 = b then 1 / 2 else 0

/-- **Without rectangularity the recursion fails** (Miao, p. 693). For the set `{Q_true, Q_false}`
of
priors on `Bool × Bool` (`aa_nrPrior`) and the payoff `x(s, s') = 1{s = s'}`,
`min_Q E^Q x = 1/2`, while the recursion built from the same marginal (a fair coin) and the same
conditionals (`δ_true`, `δ_false` at either first shock) gives `0`. -/
theorem aa_nonrectangular_counterexample :
    aa_maxmin {aa_nrPrior true, aa_nrPrior false} (fun ω => if ω.1 = ω.2 then 1 else 0) = 1 / 2 ∧
      aa_maxmin {aa_ellsbergPrior (1 / 2)} (fun s =>
        aa_maxmin {aa_ellsbergPrior 1, aa_ellsbergPrior 0}
          fun s' => if s = s' then (1 : ℝ) else 0) = 0 := by
  have hE : ∀ b, aa_E (aa_nrPrior b) (fun ω => if ω.1 = ω.2 then (1 : ℝ) else 0) = 1 / 2 := by
    intro b
    cases b <;> simp [aa_E, aa_nrPrior, Fintype.sum_prod_type]
  have hD : ∀ q ∈ ({aa_nrPrior true, aa_nrPrior false} : Set (Bool × Bool → ℝ)),
      SS.IsDistribution q := by
    intro q hq
    rcases hq with rfl | rfl <;>
      exact ⟨fun ω => by unfold aa_nrPrior; positivity,
        by simp [aa_nrPrior, Fintype.sum_prod_type]⟩
  have hD' : ∀ q ∈ ({aa_ellsbergPrior 1, aa_ellsbergPrior 0} : Set (Bool → ℝ)),
      SS.IsDistribution q := by
    intro q hq
    rcases hq with rfl | rfl
    · exact aa_ellsbergPrior_isDistribution zero_le_one le_rfl
    · exact aa_ellsbergPrior_isDistribution le_rfl zero_le_one
  have hin : ∀ s : Bool, aa_maxmin {aa_ellsbergPrior 1, aa_ellsbergPrior 0}
      (fun s' => if s = s' then (1 : ℝ) else 0) = 0 := by
    intro s
    apply le_antisymm
    · cases s
      · have := aa_maxmin_le hD' (fun s' => if false = s' then (1 : ℝ) else 0)
          (Set.mem_insert _ _)
        simpa [aa_E_bool, aa_ellsbergPrior] using this
      · have := aa_maxmin_le hD' (fun s' => if true = s' then (1 : ℝ) else 0)
          (Set.mem_insert_of_mem _ rfl)
        simpa [aa_E_bool, aa_ellsbergPrior] using this
    · refine aa_le_maxmin ⟨_, Set.mem_insert _ _⟩ _ fun q hq => ?_
      unfold aa_E
      exact Finset.sum_nonneg fun s' _ => mul_nonneg ((hD' q hq).nonneg s') (by positivity)
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · have := aa_maxmin_le hD (fun ω => if ω.1 = ω.2 then (1 : ℝ) else 0) (Set.mem_insert _ _)
      rwa [hE] at this
    · refine aa_le_maxmin ⟨_, Set.mem_insert _ _⟩ _ fun q hq => ?_
      rcases hq with rfl | rfl <;> rw [hE]
  · simp only [hin, aa_maxmin_singleton]
    exact aa_E_const (aa_ellsbergPrior_isDistribution (by norm_num) (by norm_num)) 0

end Miao.RecursiveUtility
