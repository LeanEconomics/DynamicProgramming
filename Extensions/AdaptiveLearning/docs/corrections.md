# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| E-stability (Evans and Honkapohja, 2001) | The ODE `θ̇ = T(θ) − θ` is locally asymptotically stable; for linear `T`, every eigenvalue of `B` has real part `< 1`. | A quadratic Lyapunov function: `Q` symmetric with `⟪Qx, x⟫ ≥ m‖x‖²` and `⟪Qx, Bx − x⟫ ≤ −κ‖x‖²` (`IsEStable`). In finite dimensions this is equivalent to the eigenvalue condition by Lyapunov's theorem, which is not formalised; the scalar case `β < 1` is proved directly (`isEStable_smul_iff`), and real eigenvalues `≥ 1` are shown to rule it out (`not_isEStable_of_eigen`). It is stated in any real Hilbert space. |
| Learning rule | Recursive least squares, `p^e_t` regressed on observables. | Steady-state learning, a regression on a constant: `a_{t+1} = a_t + γ_t(p_t − a_t)` (with `γ_t = 1/(t + 1)` the sample mean, `recursive_mean`), and its vector form for `θ ↦ μ + Bθ`. Any gains with `∑ γ = ∞`, `∑ γ² < ∞` are allowed. |
| Noise | i.i.d. shocks with finite variance. | Martingale differences with `𝔼[η_t² | ℱ_t] ≤ σ²` (cobweb) or `𝔼[‖W_k‖² | ℱ_k] ≤ C(1 + ‖θ_k‖²)` (vector case). |
| E-instability | E-unstable REE are learned with probability zero. | Proved for noiseless learning: the forecast error grows like `∏(1 + γ_t(β − 1))` (`learning_diverges`, `learning_diverges_of_eigen`). The probability-zero statement (Pemantle, 1990) is not formalised. |
