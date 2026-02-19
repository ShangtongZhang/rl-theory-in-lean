# RL Theory in Lean

## Installation

See [https://lean-lang.org/install/](https://lean-lang.org/install/) for a detailed tutorial on setting up Lean.  
Confirm that Lean is set up by ```lake --version```.

```
git clone git@github.com:ShangtongZhang/rl-theory-in-lean.git
cd rl-theory-in-lean
lake exe cache get
lake build
```

It is recommended to use this project with the Lean 4 extension of VSCode. 

## Paper
[Towards Formalizing Reinforcement Learning Theory](https://arxiv.org/abs/2511.03618)  
```bibtex
@article{zhang2025formalizing,
    title={Towards Formalizing Reinforcement Learning Theory},
    author={Shangtong Zhang},
    year={2025},
    journal={arXiv preprint arXiv:2511.03618}
}
```

## Main Results 

This project is organized by mirroring the structure of Mathlib so the counterparts can be upstreamed to Mathlib easily. Below are some main results when I first completed the project at this [commit](https://github.com/ShangtongZhang/rl-theory-in-lean/releases/tag/Lean-version-4.22.0-rc3). Items struck out are results that are no longer in the latest repo for various reasons (e.g., newer Mathlib now contains those results).

- Algorithm
  - [LinearTD.lean](RLTheory/Algorithm/LinearTD.lean)
    - **`[LinearTDIterates]`** - linear TD algorithm.
    - **`[DecreaseAlong]`** - $\ell_2$ norm qualifies a Lyapunov function for linear TD.
    - **`ae_tendsto_of_linearTD_iid`** — almost sure convergence of linear TD with i.i.d. samples.
    - **`ae_tendsto_of_linearTD_markov`** — almost sure convergence of linear TD with Markovian samples.
  - [QLearning.lean](RLTheory/Algorithm/QLearning.lean)
    - **`[QLearningIterates]`** — Q-learning algorithm.
    - **`[DecreaseAlong]`** - $\ell_p$ norm with a sufficiently large $p$ qualifies a Lyapunov function for Q-learning.
    - **`ae_tendsto_of_QLearning_iid`** — almost sure convergence of Q-learning with i.i.d. samples.
    - **`ae_tendsto_of_QLearning_markov`** — almost sure convergence of Q-learning with Markovian samples.
- StochasticApproximation
  - [Iterates.lean](RLTheory/StochasticApproximation/Iterates.lean) - stochastic approximation (SA) iterates and non-uniform bounds.
    - **`[Iterates]`** — a general form of SA iterates with Martingale difference noise and additional noise.
    - **`[IteratesOfResidual]`** — a specific form of SA iterates driven by residual of an operator.
    - **`[AdaptedOnSamplePath]`** — SA iterates are  completely determined by available information until current time step on every sample path.
  - [CondExp.lean](RLTheory/StochasticApproximation/CondExp.lean) 
    - **`condExp_iterates_update`** — computes the conditional expectation of SA iterates in the Ionescu-Tulcea probability space.
  - [Lyapunov.lean](RLTheory/StochasticApproximation/Lyapunov.lean) 
    - **`[LyapunovFunction]`** — desired properties for a function to be used as a Lyapunov function to analyze SA iterates.
  - [LpSpace.lean](RLTheory/StochasticApproximation/LpSpace.lean) - squared $\ell_p$ norm qualifies a Lyapunov function 
    - **`smooth_half_sq_Lp`** — squared $\ell_p$ norm is $p - 1$ smooth.
  - [Pathwise.lean](RLTheory/StochasticApproximation/Pathwise.lean) 
    - **`fundamental_inequality`** — recursive bounds of errors based on a Lyapunov function on an individual sample path.
  - [DiscreteGronwall.lean](RLTheory/StochasticApproximation/DiscreteGronwall.lean) — discrete Gronwall inequalities.
  - [MartingaleDifference.lean](RLTheory/StochasticApproximation/MartingaleDifference.lean)
    - **`ae_tendsto_of_iterates_mds_noise`** — convergence of SA iterates with Martingale difference noise.
  - [IIDSamples.lean](RLTheory/StochasticApproximation/IIDSamples.lean) 
    - **`ae_tendsto_of_iterates_iid_samples`** — convergence of SA iterates with i.i.d. samples.
  - [StepSize.lean](RLTheory/StochasticApproximation/StepSize.lean) 
    - **`anchors_of_inv_poly`** — inverse polynomial step size qualifies the [skeleton iterates](https://arxiv.org/abs/2411.13711) technique that can convert Markov noise to Martingale difference noise.
  - [MarkovSamples.lean](RLTheory/StochasticApproximation/MarkovSamples.lean)
    - **`ae_tendsto_of_iterates_markov_samples`** — convergence of SA iterates with Markovian samples.
    - **`ae_tendsto_of_iterates_markov_samples_of_inv_poly`** — specializes to inverse polynomial step size schedules.
- Data
  - ~~[Int/GCD.lean](RLTheory/Data/Int/GCD.lean)~~ 
    - **`all_but_finite_of_closed_under_add_and_gcd_one`** — if a set has gcd 1 and is close under addition, it then contains all large enough integers.
  - [Matrix/PosDef.lean](RLTheory/Data/Matrix/PosDef.lean) — positive definiteness (p.d.) for asymmetric real matrices.
    - **`posDefAsymm_iff'`** — a lower bound for the quadratic form of a p.d. matrix.
  - [Matrix/Stochastic.lean](RLTheory/Data/Matrix/Stochastic.lean) — stochastic vectors and row stochastic matrices.
    - **`smat_minorizable_with_large_pow`** — an irreducible and aperiodic stochastic matrix is Doeblin minorizable after sufficient powers.
    - **`smat_contraction_in_simplex`** - Doeblin minorization implies contraction in simplex 
    - **`stationary_distribution_exists`** - produces one stationary distribution via Cesaro limit.
    - **`stationary_distribution_uniquely_exists`** — stationary distribution uniquely exists under irreducibility and aperiodicity.
    - **`[GeometricMixing]`** - geometric mixing under irreducibility and aperiodicity.
- Probability
  - [MarkovChain/Defs.lean](RLTheory/Probability/MarkovChain/Defs.lean) — basics of time homogeneous Markov chains.
  - [MarkovChain/Finite/Defs.lean](RLTheory/Probability/MarkovChain/Finite/Defs.lean) — matrix representation of finite Markov chains 
  - [MarkovChain/Trajectory.lean](RLTheory/Probability/MarkovChain/Trajectory.lean) 
    - **`traj_prob`** — constructs the sample path space probability measure for Markov chains by the Ionescu-Tulcea theorem.
  - [Martingale/Convergence.lean](RLTheory/Probability/Martingale/Convergence.lean) 
    - **`ae_tendsto_zero_of_almost_supermartingale`** — Robbins-Siegmund theorem for the convergence of almost supermartingales.
- MarkovDecisionProcess
  - [MarkovRewardProcess.lean](RLTheory/MarkovDecisionProcess/MarkovRewardProcess.lean) — basics of finite MRPs.
    - **`[NegDefAsymm MRP.K]`** — negative definiteness of the matrix $D(\gamma P - I)$ 
  - [MarkovDecisionProcess.lean](RLTheory/MarkovDecisionProcess/MarkovDecisionProcess.lean) — basics of finite MDPs.
 
## Remarks
When I first completed the project at this [commit](https://github.com/ShangtongZhang/rl-theory-in-lean/releases/tag/Lean-version-4.22.0-rc3), the Lean toolchain has the version 4.22. At that time, I hated to have ``calc``, ``have``, and comments in the code so I tried my best to avoid them as much as possible, which I know is not good for readability. Later on, the Lean toolchain is bumped to 4.28 in this [PR](https://github.com/ShangtongZhang/rl-theory-in-lean/pull/1). According to the author of the PR, the code there is 100% generated via LLMs so that PR introduces lots of good coding style that increases readability (e.g., long ``calc``, many ``have``). An unavoidable consequence is that the coding style is now inconsistent across the project.
