# The Lieb–Robinson bound and exponential clustering on finite lattices in Lean 4

A machine-checked proof that information in a quantum spin system with local interactions
spreads at finite speed, built on Mathlib (with [Physlib](https://github.com/leanprover-community/physlib)
as a dependency).

**Paper:** [`paper/main.pdf`](paper/main.pdf) — *A Formal Proof of the Lieb–Robinson Bound and
Exponential Clustering on Finite Lattices in Lean 4* (Nichlas Löfdahl, Claude).

## Setting (`LiebRobinson/Basic.lean`)

- `LocalNet`: a C*-algebra `𝔄` with a subalgebra `𝔄_X` for each finite region `X ⊆ Λ`. The only
  axiom is that observables in disjoint regions commute, so no tensor products are needed.
- `Interaction`: self-adjoint terms `Φ Z ∈ 𝔄_Z`. The Hamiltonian is `H = ∑ Φ Z`, and the
  dynamics is `τ_t(A) = e^{itH} A e^{-itH}`.

## Results

| Lean name | Statement |
|---|---|
| `Interaction.norm_commutator_evolution_le` | `‖[τ_t A, B]‖ ≤ ‖[A,B]‖ + 2‖A‖ ∑_{Z∩X≠∅} ∫₀ᵗ ‖[τ_s Φ_Z, B]‖` |
| `Interaction.norm_commutator_evolution_le_of_far` | `‖[τ_t Φ_Z, B]‖ ≤ 2‖Φ_Z‖‖B‖ (2Jκt)^k / k!` if `Z` is `k` steps from `Y` |
| `Interaction.lieb_robinson_pow` | polynomial form of the bound |
| `Interaction.lieb_robinson_exp` | `‖[τ_t A, B]‖ ≤ 2‖A‖‖B‖ (n_X/κ) e^{vt - (n+1)}`, with `v = 2eJκ` |
| `Interaction.lieb_robinson` | `‖[τ_t A, B]‖ ≤ 2e‖A‖‖B‖ (n_X/κ) e^{vt - d(X,Y)/R}` for `t ≥ 0` |
| `Interaction.lieb_robinson_abs` | the same with `v\|t\|`, for all real `t` |
| `CondensedMatter.QuasiLocal.commute_inclMat_of_disjoint` | `M ⊗ 1` and `1 ⊗ N` commute for disjoint regions (Physlib model) |
| `CondensedMatter.QuasiLocal.Interaction.hamiltonian_toBox` | the abstract Hamiltonian of a box equals Physlib's |
| `CondensedMatter.QuasiLocal.Interaction.lieb_robinson` | the bound for Physlib's lattice model in a finite box (`LiebRobinson/Lattice.lean`) |

## Exponential clustering (`LiebRobinson/Clustering/`)

For observables on a finite-dimensional Hilbert space `ℋ` (`𝔄 = ℋ →L[ℂ] ℋ`) and a unique ground
state `Ω` with spectral gap `γ` (`GappedGroundState`):

| Lean name | Statement |
|---|---|
| `integral_gaussKernel` | `∫ e^{-αt²}(e^{-iωt}-1)/(it) dt = -√(π/α) ∫₀^ω e^{-σ²/(4α)} dσ` (Fubini + Gaussian Fourier transform) |
| `GappedGroundState.exists_expansion` | `⟨[τ_t A, B]⟩` is a sum of oscillations with frequencies `≥ γ` |
| `norm_sum_le_of_filter` | the positive-frequency part is controlled by `F` near `t = 0` |
| `Interaction.exponential_clustering` | `\|⟨AB⟩ - ⟨A⟩⟨B⟩\| ≤ (2/π)‖A‖‖B‖((n_X/κ)e^{-(n+1)/2} + (4eJκ/γ + √(2πeJκ/γ)) e^{-γ(n+1)/(8eJκ)})` |
| `Interaction.exponential_clustering_dist` | decay `e^{-μ d}` in the distance, `μ = min(1/2, γ/(8eJκ))/R` |

Here `J` bounds `‖Φ Z‖`, `R` is the range (the diameter of each non-zero term), `κ` bounds the
number of non-zero terms meeting any region, and `n_X` is the number of terms meeting `X`. None
of these constants depends on the size of the lattice.

The proof removes the norm-preserving part of the dynamics with the interaction picture
`U(t) = e^{itH} e^{-itH₁}`, so it needs no time-dependent propagator. It then iterates the
resulting integral inequality by induction on the distance in the overlap graph of the terms.

No `sorry`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

## Building

Lean `v4.35.0`, Physlib commit `3bfc7af`.

```bash
lake exe cache get
lake build
```

The paper builds with `cd paper && latexmk -pdf main`.
