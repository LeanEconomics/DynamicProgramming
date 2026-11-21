/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.HMFilter
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Control under partial information: the belief state

Miao, §10.2, pp. 340–341, for finite hidden states `X`, signals `Y` and actions `U` (the book's
"discrete states" case, where the posterior is finite-dimensional). The model `HMPOMDP` has the
transition kernel `a(x′ | z, u) = Pr(x_{t+1} = x′ | x_t = z, u_t = u)` (assumption (ii)), the signal
kernel `q(y | x′, u) = Pr(y_{t+1} = y | x_{t+1} = x′, u_t = u)` (assumption (iii)), rewards
`r(x, u, t)`, terminal reward `R` and discount `β`. The book's
`a_t(x′, y | z, u) = Pr(x_{t+1} = x′, y_{t+1} = y | x_t = z, u_t = u) = q(y | x′, u) a(x′ | z, u)`
is `hm_at` (`hm_at_sum`: it is a probability on `X × Y`).

* Expected total reward. A (deterministic, history-dependent) policy `σ` picks `u_k` from the
  signals `y₁, …, y_k` seen so far (past actions are themselves functions of past signals). For
  an initial (sub-)probability `m` on `x₀`, `hm_cw` is the probability of a state path
  `x₀ … x_n` and signal path `y₁ … y_n`, `hm_rew` the discounted reward
  `Σ_{k<n} βᵏ r(x_k, u_k, t + k) + βⁿ R(x_n)`, and `hm_J n t σ m` the expectation. The total
  mass is preserved (`hm_cw_mass`) and conditioning on the first period gives
  `J_{n+1}(σ, m) = Σₓ m(x) r(x, u₀, t) + β Σ_y J_n(σ_y, m′_y)` (`hm_J_succ`), where `m′_y` is the
  unnormalised posterior (`hm_nextM`).
* Posterior recursion (p. 341):
  `P*(x′) = Σₓ P(x) a_t(x′, y | x, u) / Σ_{x′} Σₓ P(x) a_t(x′, y | x, u)`
  (`hm_bayesNext`); for one period it is the conditional probability of `x₁` given `y₁` in the
  path model (`hm_posterior_one_step`).
* Bellman equation in beliefs (p. 341): `V(P, T) = Σₓ P(x) R(x)`,
  `V(P, t) = max_u [Σₓ P(x) r(x, u, t) + β Σₓ Σ_y Σ_z P(z) a_t(x, y | z, u) V(P*, t + 1)]`
  (`hm_V`, `hm_bookV`, `hm_bellman_terminal`, `hm_bellman`).
* The belief is a sufficient statistic: no history-dependent policy does better than `V(P, t)`
  (`hm_J_le_V`), the policy that maximises the right side of the Bellman equation at the
  current belief attains it (`hm_J_beliefPol`), so `V(P, t)` is the optimal expected reward over
  all history-dependent policies (`hm_value_isGreatest`).
-/

namespace Miao.PartialInformation

/-- Miao, p. 340: a finite partially observed control problem: transition kernel `a z u x`,
signal kernel `q x u y` (signal `y_{t+1}` given `x_{t+1}` and `u_t`), rewards `r x u t`,
terminal reward `R`, discount `β`. -/
structure HMPOMDP (X Y U : Type*) where
  /-- `a z u x = Pr(x_{t+1} = x | x_t = z, u_t = u)`. -/
  a : X → U → X → ℝ
  /-- `q x u y = Pr(y_{t+1} = y | x_{t+1} = x, u_t = u)`. -/
  q : X → U → Y → ℝ
  /-- Period reward `r(x, u, t)`. -/
  r : X → U → ℕ → ℝ
  /-- Terminal reward. -/
  R : X → ℝ
  /-- Discount factor. -/
  β : ℝ

variable {X Y U : Type*} [Fintype X] [Fintype Y] [Fintype U]

/-- Miao, p. 340: `a_t(x, y | z, u) = Pr(x_{t+1} = x, y_{t+1} = y | x_t = z, u_t = u)
= Pr(y_{t+1} | x_{t+1}, u_t) Pr(x_{t+1} | x_t, u_t)`. -/
def hm_at (M : HMPOMDP X Y U) (z : X) (u : U) (x : X) (y : Y) : ℝ := M.q x u y * M.a z u x

omit [Fintype U] in
/-- `a_t(·, · | z, u)` is a probability on `X × Y` when `a` and `q` are stochastic. -/
theorem hm_at_sum (M : HMPOMDP X Y U) (ha : ∀ z u, ∑ x, M.a z u x = 1)
    (hq : ∀ x u, ∑ y, M.q x u y = 1) (z : X) (u : U) : ∑ x, ∑ y, hm_at M z u x y = 1 := by
  simp only [hm_at, ← Finset.sum_mul, hq, one_mul, ha]

/-- The unnormalised posterior `m′(x′) = Σ_z m(z) a_t(x′, y | z, u)`. -/
def hm_nextM (M : HMPOMDP X Y U) (m : X → ℝ) (u : U) (y : Y) : X → ℝ :=
  fun x => ∑ z, m z * hm_at M z u x y

/-- The predictive probability of the signal, `Σ_{x′} Σ_z m(z) a_t(x′, y | z, u)`. -/
def hm_py (M : HMPOMDP X Y U) (m : X → ℝ) (u : U) (y : Y) : ℝ := ∑ x, hm_nextM M m u y x

/-- Miao, p. 341: the posterior
`P*(x′) = Σₓ P(x) a_t(x′, y | x, u) / Σ_{x′} Σₓ P(x) a_t(x′, y | x, u)`. -/
noncomputable def hm_bayesNext (M : HMPOMDP X Y U) (m : X → ℝ) (u : U) (y : Y) : X → ℝ :=
  fun x => hm_nextM M m u y x / hm_py M m u y

/-- Miao, p. 341: the value function in beliefs, by the number `n` of decision dates left at
calendar date `t`: `V₀(P) = Σₓ P(x) R(x)` and
`V_{n+1}(P, t) = max_u [Σₓ P(x) r(x, u, t) + β Σ_y Pr(y | P, u) V_n(P*, t + 1)]`. -/
noncomputable def hm_V [Nonempty U] (M : HMPOMDP X Y U) : ℕ → ℕ → (X → ℝ) → ℝ
  | 0, _, m => ∑ x, m x * M.R x
  | n + 1, t, m => Finset.univ.sup' Finset.univ_nonempty (fun u => ∑ x, m x * M.r x u t +
      M.β * ∑ y, hm_py M m u y * hm_V M n (t + 1) (hm_bayesNext M m u y))

/-- The right side of the Bellman equation at action `u`. -/
noncomputable def hm_obj [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) (u : U) : ℝ :=
  ∑ x, m x * M.r x u t + M.β * ∑ y, hm_py M m u y * hm_V M n (t + 1) (hm_bayesNext M m u y)

theorem hm_V_succ [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) :
    hm_V M (n + 1) t m = Finset.univ.sup' Finset.univ_nonempty (hm_obj M n t m) := rfl

/-- The book's `V(P, t)` for horizon `T`: `n = T − t` decisions remain. -/
noncomputable def hm_bookV [Nonempty U] (M : HMPOMDP X Y U) (T t : ℕ) (m : X → ℝ) : ℝ :=
  hm_V M (T - t) t m

omit [Fintype Y] [Fintype U] in
/-- Miao, p. 341: `V(P, T) = Σₓ P(x) R(x)`. -/
theorem hm_bellman_terminal [Fintype Y] [Fintype U] [Nonempty U] (M : HMPOMDP X Y U) (T : ℕ)
    (m : X → ℝ) : hm_bookV M T T m = ∑ x, m x * M.R x := by
  simp [hm_bookV, hm_V]

/-- Miao, p. 341 (the Bellman equation in beliefs): for `t < T`,
`V(P, t) = max_u [Σₓ P(x) r(x, u, t) + β Σₓ Σ_y Σ_z P(z) a_t(x, y | z, u) V(P*, t + 1)]`, with
`P* = hm_bayesNext P u y`. -/
theorem hm_bellman [Nonempty U] (M : HMPOMDP X Y U) (T t : ℕ) (ht : t < T) (m : X → ℝ) :
    hm_bookV M T t m = Finset.univ.sup' Finset.univ_nonempty (fun u => ∑ x, m x * M.r x u t +
      M.β * ∑ x, ∑ y, ∑ z, m z * hm_at M z u x y *
        hm_bookV M T (t + 1) (hm_bayesNext M m u y)) := by
  unfold hm_bookV
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  rw [hn, hn', hm_V]
  congr 1
  funext u
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [hm_py, hm_nextM, Finset.sum_mul]

/-- The first `k` signals of a signal path. -/
def hm_pre {n : ℕ} (ys : Fin n → Y) (k : Fin n) : Fin k → Y :=
  fun i => ys ⟨i, i.2.trans k.2⟩

/-- The probability of the state path `x₀ … x_n` and the signal path `y₁ … y_n` when `x₀ ~ m`
and the policy `σ` chooses `u_k = σ_k(y₁, …, y_k)`. -/
def hm_cw (M : HMPOMDP X Y U) (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ)
    (xs : Fin (n + 1) → X) (ys : Fin n → Y) : ℝ :=
  m (xs 0) * ∏ k : Fin n, hm_at M (xs k.castSucc) (σ k (hm_pre ys k)) (xs k.succ) (ys k)

/-- The discounted reward `Σ_{k<n} βᵏ r(x_k, u_k, t + k) + βⁿ R(x_n)` along a path. -/
def hm_rew (M : HMPOMDP X Y U) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (xs : Fin (n + 1) → X) (ys : Fin n → Y) : ℝ :=
  ∑ k : Fin n, M.β ^ (k : ℕ) * M.r (xs k.castSucc) (σ k (hm_pre ys k)) (t + k) +
    M.β ^ n * M.R (xs (Fin.last n))

/-- Miao, p. 340: the expected total reward `E[Σ_{k<n} βᵏ r(x_k, u_k, t + k) + βⁿ R(x_n)]` of the
policy `σ` from the initial law `m`. -/
def hm_J (M : HMPOMDP X Y U) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ) : ℝ :=
  ∑ xs : Fin (n + 1) → X, ∑ ys : Fin n → Y, hm_cw M n σ m xs ys * hm_rew M n t σ xs ys

/-- The continuation of `σ` after the first signal `y`. -/
def hm_shift (σ : (k : ℕ) → (Fin k → Y) → U) (y : Y) : (k : ℕ) → (Fin k → Y) → U :=
  fun k ys => σ (k + 1) (Fin.cons y ys)

/-- Splitting a sum over `(n + 1)`-tuples into the first entry and the rest. -/
theorem hm_sum_cons {α Z : Type*} [Fintype α] [AddCommMonoid Z] (n : ℕ)
    (F : (Fin (n + 1) → α) → Z) :
    ∑ xs, F xs = ∑ j, ∑ xs : Fin n → α, F (Fin.cons j xs) := by
  rw [← (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)),
    Fintype.sum_prod_type]
  rfl

omit [Fintype Y] [Fintype U] in
theorem hm_pre_cons_succ (σ : (k : ℕ) → (Fin k → Y) → U) {n : ℕ} (y : Y) (yr : Fin n → Y)
    (k : Fin n) :
    σ (k.succ : ℕ) (hm_pre (Fin.cons y yr) k.succ) = hm_shift σ y k (hm_pre yr k) := by
  change σ ((k : ℕ) + 1) (hm_pre (Fin.cons y yr) k.succ) = σ ((k : ℕ) + 1) (Fin.cons y _)
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

omit [Fintype Y] [Fintype U] in
theorem hm_pre_zero (σ : (k : ℕ) → (Fin k → Y) → U) {n : ℕ} (ys : Fin (n + 1) → Y) :
    σ ((0 : Fin (n + 1)) : ℕ) (hm_pre ys 0) = σ 0 Fin.elim0 := by
  change σ 0 _ = σ 0 _
  congr 1
  funext i
  exact i.elim0

omit [Fintype Y] [Fintype U] in
/-- One period of the path probability: summing out `x₀` leaves the path probability of the
continuation from the unnormalised posterior `m′_y`. -/
theorem hm_cw_cons_sum (M : HMPOMDP X Y U) (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) (xr : Fin (n + 1) → X) (y : Y) (yr : Fin n → Y) :
    ∑ x0, hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) =
      hm_cw M n (hm_shift σ y) (hm_nextM M m (σ 0 Fin.elim0) y) xr yr := by
  unfold hm_cw hm_nextM
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [Fin.prod_univ_succ]
  simp only [hm_pre_cons_succ, hm_pre_zero, Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one,
    ← Fin.succ_castSucc, Fin.cons_succ]
  have h1 : (Fin.cons x0 xr : Fin (n + 2) → X) 1 = xr 0 := rfl
  rw [h1]
  ring

omit [Fintype U] in
/-- Conditioning a path sum on the first period. -/
theorem hm_cw_decomp (M : HMPOMDP X Y U) (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) (G : Y → (Fin (n + 1) → X) → (Fin n → Y) → ℝ) :
    ∑ xs : Fin (n + 2) → X, ∑ ys : Fin (n + 1) → Y,
        hm_cw M (n + 1) σ m xs ys * G (ys 0) (Fin.tail xs) (Fin.tail ys) =
      ∑ y, ∑ xr, ∑ yr, hm_cw M n (hm_shift σ y) (hm_nextM M m (σ 0 Fin.elim0) y) xr yr *
        G y xr yr := by
  rw [hm_sum_cons (n := n + 1) (α := X)]
  simp only [hm_sum_cons (n := n) (α := Y) (Z := ℝ), Fin.cons_zero, Fin.tail_cons]
  calc _ = ∑ x0 : X, ∑ y : Y, ∑ xr : Fin (n + 1) → X, ∑ yr : Fin n → Y,
        hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) * G y xr yr :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ y : Y, ∑ x0 : X, ∑ xr : Fin (n + 1) → X, ∑ yr : Fin n → Y,
        hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) * G y xr yr := Finset.sum_comm
    _ = ∑ y : Y, ∑ xr : Fin (n + 1) → X, ∑ yr : Fin n → Y, ∑ x0 : X,
        hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) * G y xr yr :=
        Finset.sum_congr rfl (fun _ _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun xr _ =>
        Finset.sum_congr rfl (fun yr _ => by rw [← Finset.sum_mul, hm_cw_cons_sum])))

omit [Fintype U] in
/-- The path probabilities have total mass `Σₓ m(x)`. -/
theorem hm_cw_mass (M : HMPOMDP X Y U) (ha : ∀ z u, ∑ x, M.a z u x = 1)
    (hq : ∀ x u, ∑ y, M.q x u y = 1) :
    ∀ (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ),
      ∑ xs : Fin (n + 1) → X, ∑ ys : Fin n → Y, hm_cw M n σ m xs ys = ∑ x, m x
  | 0, σ, m => by
    simp only [hm_cw, Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_unique, one_nsmul]
    exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun _ => rfl))
  | n + 1, σ, m => by
    have h := hm_cw_decomp M n σ m (fun _ _ _ => 1)
    simp only [mul_one] at h
    rw [h]
    simp only [hm_cw_mass M ha hq n, hm_nextM]
    calc _ = ∑ x : X, ∑ y : Y, ∑ z : X, m z * hm_at M z (σ 0 Fin.elim0) x y := Finset.sum_comm
      _ = ∑ x : X, ∑ z : X, ∑ y : Y, m z * hm_at M z (σ 0 Fin.elim0) x y :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ z : X, ∑ x : X, ∑ y : Y, m z * hm_at M z (σ 0 Fin.elim0) x y := Finset.sum_comm
      _ = ∑ z, m z := Finset.sum_congr rfl (fun z _ => by
        simp only [← Finset.mul_sum]
        rw [hm_at_sum M ha hq, mul_one])

omit [Fintype X] [Fintype Y] [Fintype U] in
theorem hm_rew_cons (M : HMPOMDP X Y U) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (x0 : X) (xr : Fin (n + 1) → X) (y : Y) (yr : Fin n → Y) :
    hm_rew M (n + 1) t σ (Fin.cons x0 xr) (Fin.cons y yr) =
      M.r x0 (σ 0 Fin.elim0) t + M.β * hm_rew M n (t + 1) (hm_shift σ y) xr yr := by
  unfold hm_rew
  rw [Fin.sum_univ_succ]
  simp only [hm_pre_cons_succ, hm_pre_zero]
  have hl : (Fin.cons x0 xr : Fin (n + 2) → X) (Fin.last (n + 1)) = xr (Fin.last n) := by
    rw [← Fin.succ_last, Fin.cons_succ]
  have hc : ∀ k : Fin n, (Fin.cons x0 xr : Fin (n + 2) → X) k.succ.castSucc = xr k.castSucc :=
    fun k => by rw [← Fin.succ_castSucc, Fin.cons_succ]
  have h0 : (Fin.cons x0 xr : Fin (n + 2) → X) (Fin.castSucc 0) = x0 := rfl
  simp only [hl, hc, h0, Fin.val_zero, Fin.val_succ, pow_zero, one_mul, add_zero]
  rw [add_assoc, mul_add, Finset.mul_sum]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show t + ((k : ℕ) + 1) = t + 1 + k by omega, pow_succ]
    ring
  · ring

omit [Fintype U] in
/-- Miao, p. 340: conditioning on the first period,
`J_{n+1}(σ, m) = Σₓ m(x) r(x, u₀, t) + β Σ_y J_n(σ_y, m′_y)`. -/
theorem hm_J_succ (M : HMPOMDP X Y U) (ha : ∀ z u, ∑ x, M.a z u x = 1)
    (hq : ∀ x u, ∑ y, M.q x u y = 1) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) :
    hm_J M (n + 1) t σ m = ∑ x, m x * M.r x (σ 0 Fin.elim0) t +
      M.β * ∑ y, hm_J M n (t + 1) (hm_shift σ y) (hm_nextM M m (σ 0 Fin.elim0) y) := by
  have e1 : hm_J M (n + 1) t σ m =
      ∑ xs : Fin (n + 2) → X, ∑ ys : Fin (n + 1) → Y,
        hm_cw M (n + 1) σ (fun x => m x * M.r x (σ 0 Fin.elim0) t) xs ys +
      M.β * ∑ xs : Fin (n + 2) → X, ∑ ys : Fin (n + 1) → Y, hm_cw M (n + 1) σ m xs ys *
        hm_rew M n (t + 1) (hm_shift σ (ys 0)) (Fin.tail xs) (Fin.tail ys) := by
    unfold hm_J
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun xs _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ys _ => ?_)
    rw [← Fin.cons_self_tail xs, ← Fin.cons_self_tail ys, hm_rew_cons]
    simp only [hm_cw, Fin.cons_zero, Fin.tail_cons]
    ring
  rw [e1, hm_cw_mass M ha hq,
    hm_cw_decomp M n σ m (fun y xr yr => hm_rew M n (t + 1) (hm_shift σ y) xr yr)]
  rfl

omit [Fintype U] in
theorem hm_J_zero (M : HMPOMDP X Y U) (t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) : hm_J M 0 t σ m = ∑ x, m x * M.R x := by
  unfold hm_J hm_cw hm_rew
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.sum_empty, zero_add,
    pow_zero, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_nsmul]
  exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun _ => rfl))

omit [Fintype Y] [Fintype U] in
theorem hm_nextM_nonneg (M : HMPOMDP X Y U) (ha : ∀ z u x, 0 ≤ M.a z u x)
    (hq : ∀ x u y, 0 ≤ M.q x u y) (m : X → ℝ) (hm : ∀ x, 0 ≤ m x) (u : U) (y : Y) (x : X) :
    0 ≤ hm_nextM M m u y x :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (hm z) (mul_nonneg (hq _ _ _) (ha _ _ _)))

omit [Fintype Y] [Fintype U] in
theorem hm_nextM_smul (M : HMPOMDP X Y U) (c : ℝ) (m : X → ℝ) (u : U) (y : Y) :
    hm_nextM M (c • m) u y = c • hm_nextM M m u y := by
  funext x
  simp only [hm_nextM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [Fintype Y] [Fintype U] in
theorem hm_bayesNext_smul (M : HMPOMDP X Y U) {c : ℝ} (hc : c ≠ 0) (m : X → ℝ) (u : U)
    (y : Y) : hm_bayesNext M (c • m) u y = hm_bayesNext M m u y := by
  funext x
  simp only [hm_bayesNext, hm_py, hm_nextM_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- A positive multiple of a nonnegative function: `sup (c g) = c sup g` for `c ≥ 0`. -/
theorem hm_sup'_mul {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : s.sup' hs (fun i => c * g i) = c * s.sup' hs g := by
  apply le_antisymm
  · exact Finset.sup'_le hs _ (fun i hi => mul_le_mul_of_nonneg_left (Finset.le_sup' g hi) hc)
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs g
    rw [he]
    exact Finset.le_sup' (fun i => c * g i) hi

/-- The value function is positively homogeneous in the (unnormalised) belief. -/
theorem hm_V_smul [Nonempty U] (M : HMPOMDP X Y U) :
    ∀ (n t : ℕ) (m : X → ℝ) {c : ℝ}, 0 ≤ c → hm_V M n t (c • m) = c * hm_V M n t m
  | 0, t, m, c, _ => by
    simp only [hm_V, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  | n + 1, t, m, c, hc => by
    rw [hm_V_succ, hm_V_succ, ← hm_sup'_mul _ _ _ hc]
    congr 1
    funext u
    rcases hc.lt_or_eq with hc | hc
    · simp only [hm_obj, hm_bayesNext_smul M hc.ne', hm_py, hm_nextM_smul, Pi.smul_apply,
        smul_eq_mul, ← Finset.mul_sum, mul_assoc, mul_add, mul_left_comm c M.β]
    · subst hc
      simp [hm_obj, hm_py, hm_nextM]

/-- `Pr(y | m, u) V_n(P*_y) = V_n(m′_y)`: the value of the unnormalised posterior. -/
theorem hm_py_mul_V [Nonempty U] (M : HMPOMDP X Y U) (ha : ∀ z u x, 0 ≤ M.a z u x)
    (hq : ∀ x u y, 0 ≤ M.q x u y) (m : X → ℝ) (hm : ∀ x, 0 ≤ m x) (n t : ℕ) (u : U) (y : Y) :
    hm_py M m u y * hm_V M n t (hm_bayesNext M m u y) = hm_V M n t (hm_nextM M m u y) := by
  have hnn := hm_nextM_nonneg M ha hq m hm u y
  have hpy : 0 ≤ hm_py M m u y := Finset.sum_nonneg (fun x _ => hnn x)
  rcases hpy.lt_or_eq with hp | hp
  · rw [← hm_V_smul M n t _ hp.le]
    congr 1
    funext x
    simp only [hm_bayesNext, Pi.smul_apply, smul_eq_mul]
    field_simp
  · have h0 : hm_nextM M m u y = (0 : ℝ) • hm_nextM M m u y := by
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hnn x)).1 hp.symm x
        (Finset.mem_univ _)
      simp [this]
    rw [← hp, zero_mul, h0, hm_V_smul M n t _ le_rfl, zero_mul]

/-- Miao, p. 341 (the belief is a sufficient statistic, upper bound): every history-dependent
policy earns at most `V_n(m, t)` from a nonnegative initial law `m`. -/
theorem hm_J_le_V [Nonempty U] (M : HMPOMDP X Y U) (hβ : 0 ≤ M.β)
    (ha0 : ∀ z u x, 0 ≤ M.a z u x) (hq0 : ∀ x u y, 0 ≤ M.q x u y)
    (ha : ∀ z u, ∑ x, M.a z u x = 1) (hq : ∀ x u, ∑ y, M.q x u y = 1) :
    ∀ (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ), (∀ x, 0 ≤ m x) →
      hm_J M n t σ m ≤ hm_V M n t m
  | 0, t, σ, m, _ => by rw [hm_J_zero]; rfl
  | n + 1, t, σ, m, hm => by
    rw [hm_J_succ M ha hq, hm_V_succ]
    refine le_trans ?_ (Finset.le_sup' (hm_obj M n t m) (Finset.mem_univ (σ 0 Fin.elim0)))
    unfold hm_obj
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => ?_)) hβ)
    rw [hm_py_mul_V M ha0 hq0 m hm]
    exact hm_J_le_V M hβ ha0 hq0 ha hq n (t + 1) _ _ (hm_nextM_nonneg M ha0 hq0 m hm _ y)

/-- A maximiser of the right side of the Bellman equation at the belief `m`. -/
noncomputable def hm_greedy [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) : U :=
  (Finset.exists_mem_eq_sup' Finset.univ_nonempty (hm_obj M n t m)).choose

theorem hm_greedy_spec [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) :
    hm_V M (n + 1) t m = hm_obj M n t m (hm_greedy M n t m) :=
  (Finset.exists_mem_eq_sup' Finset.univ_nonempty (hm_obj M n t m)).choose_spec.2

/-- The belief policy of an `(n + 1)`-period problem: act greedily at the current belief, then
update the belief by Bayes' rule (`hm_nextM`) and continue. It depends on the signal history
only through the belief. -/
noncomputable def hm_beliefPol [Nonempty U] (M : HMPOMDP X Y U) :
    ℕ → ℕ → (X → ℝ) → (k : ℕ) → (Fin k → Y) → U
  | n, t, m, 0, _ => hm_greedy M n t m
  | n, t, m, k + 1, ys =>
      hm_beliefPol M (n - 1) (t + 1) (hm_nextM M m (hm_greedy M n t m) (ys 0)) k (Fin.tail ys)

theorem hm_shift_beliefPol [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) (y : Y) :
    hm_shift (hm_beliefPol M (n + 1) t m) y =
      hm_beliefPol M n (t + 1) (hm_nextM M m (hm_greedy M (n + 1) t m) y) := by
  funext k ys
  simp only [hm_shift, hm_beliefPol, Fin.cons_zero, Fin.tail_cons, Nat.add_sub_cancel]

/-- Miao, p. 341 (the belief is a sufficient statistic, attainment): the belief policy earns
exactly `V_{n+1}(m, t)`. -/
theorem hm_J_beliefPol [Nonempty U] (M : HMPOMDP X Y U)
    (ha0 : ∀ z u x, 0 ≤ M.a z u x) (hq0 : ∀ x u y, 0 ≤ M.q x u y)
    (ha : ∀ z u, ∑ x, M.a z u x = 1) (hq : ∀ x u, ∑ y, M.q x u y = 1) :
    ∀ (n t : ℕ) (m : X → ℝ), (∀ x, 0 ≤ m x) →
      hm_J M (n + 1) t (hm_beliefPol M n t m) m = hm_V M (n + 1) t m
  | 0, t, m, hm => by
    rw [hm_J_succ M ha hq, hm_greedy_spec, hm_obj]
    have hu : hm_beliefPol M 0 t m 0 Fin.elim0 = hm_greedy M 0 t m := rfl
    rw [hu]
    congr 2
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hm_J_zero, hm_py_mul_V M ha0 hq0 m hm]
    rfl
  | n + 1, t, m, hm => by
    rw [hm_J_succ M ha hq, hm_greedy_spec, hm_obj]
    have hu : hm_beliefPol M (n + 1) t m 0 Fin.elim0 = hm_greedy M (n + 1) t m := rfl
    rw [hu]
    congr 2
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hm_shift_beliefPol, hm_J_beliefPol M ha0 hq0 ha hq n (t + 1) _
      (hm_nextM_nonneg M ha0 hq0 m hm _ y), hm_py_mul_V M ha0 hq0 m hm]

/-- Miao, pp. 340–341: `V_n(m, t)` is the largest expected reward over all history-dependent
policies, and it is attained (by the belief policy when `n ≥ 1`). -/
theorem hm_value_isGreatest [Nonempty U] (M : HMPOMDP X Y U) (hβ : 0 ≤ M.β)
    (ha0 : ∀ z u x, 0 ≤ M.a z u x) (hq0 : ∀ x u y, 0 ≤ M.q x u y)
    (ha : ∀ z u, ∑ x, M.a z u x = 1) (hq : ∀ x u, ∑ y, M.q x u y = 1) (n t : ℕ)
    (m : X → ℝ) (hm : ∀ x, 0 ≤ m x) :
    IsGreatest (Set.range (fun σ : (k : ℕ) → (Fin k → Y) → U => hm_J M n t σ m))
      (hm_V M n t m) := by
  refine ⟨?_, ?_⟩
  · cases n with
    | zero => exact ⟨fun _ _ => Classical.arbitrary U, by simp only [hm_J_zero]; rfl⟩
    | succ n => exact ⟨hm_beliefPol M n t m, hm_J_beliefPol M ha0 hq0 ha hq n t m hm⟩
  · rintro _ ⟨σ, rfl⟩
    exact hm_J_le_V M hβ ha0 hq0 ha hq n t σ m hm

omit [Fintype U] in
/-- Miao, p. 341 (the posterior recursion as a conditional probability): in the one-period path
model, `Pr(x₁ = x′ | y₁ = y) = Σₓ m(x) a_t(x′, y | x, u) / Σ_{x′} Σₓ m(x) a_t(x′, y | x, u)`,
with `u = σ₀`. -/
theorem hm_posterior_one_step [DecidableEq X] [DecidableEq Y] (M : HMPOMDP X Y U)
    (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ) (x : X) (y : Y) :
    (∑ xs : Fin 2 → X, ∑ ys : Fin 1 → Y,
        if xs 1 = x ∧ ys 0 = y then hm_cw M 1 σ m xs ys else 0) /
      (∑ xs : Fin 2 → X, ∑ ys : Fin 1 → Y, if ys 0 = y then hm_cw M 1 σ m xs ys else 0) =
      hm_bayesNext M m (σ 0 Fin.elim0) y x := by
  have key : ∀ G : X → Y → Prop, ∀ [∀ a b, Decidable (G a b)],
      (∑ xs : Fin 2 → X, ∑ ys : Fin 1 → Y,
        if G (xs 1) (ys 0) then hm_cw M 1 σ m xs ys else 0) =
      ∑ y', ∑ x', if G x' y' then hm_nextM M m (σ 0 Fin.elim0) y' x' else 0 := by
    intro G _
    have h := hm_cw_decomp M 0 σ m (fun y' xr _ => if G (xr 0) y' then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at h
    refine Eq.trans h ?_
    refine Finset.sum_congr rfl (fun y' _ => ?_)
    rw [hm_sum_fin_one]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    simp [hm_cw]
  rw [key (fun x' y' => x' = x ∧ y' = y), key (fun _ y' => y' = y)]
  simp only [hm_bayesNext, hm_py]
  congr 1
  · rw [Finset.sum_eq_single y (fun b _ hb => Finset.sum_eq_zero (fun x' _ => by simp [hb]))
      (by simp)]
    simp
  · rw [Finset.sum_eq_single y (fun b _ hb => Finset.sum_eq_zero (fun x' _ => by simp [hb]))
      (by simp)]
    simp

end Miao.PartialInformation
