# Kepler's first law and the Laplace–Runge–Lenz vector in Lean 4

A machine-checked formalization of the classical Kepler problem in [Lean 4](https://lean-lang.org)
on top of [Physlib](https://github.com/leanprover-community/physlib) and Mathlib.

**Paper:** [`paper/main.pdf`](paper/main.pdf) — *A Formal Proof of the Conservation of the
Laplace–Runge–Lenz Vector, Kepler's First Law and the Hidden so(4) Symmetry in Lean 4* (Nichlas Löfdahl, Claude).

## Results (`KeplerLRL/Kepler.lean`)

For a particle of mass `m` in the potential `V r = -k / r`, with `L = q × p` and
`A = p × L - (m k / ‖q‖) q`:

| Lean name | Statement |
|---|---|
| `lrlVector_eq` | `A = ⟪p,p⟫ q - ⟪q,p⟫ p - (m k/‖q‖) q` |
| `inner_lrlVector_angularMomentum` | `⟪A, L⟫ = 0` |
| `inner_lrlVector_position` | orbit equation `⟪A, q⟫ = ‖L‖² - m k ‖q‖` |
| `norm_lrlVector_sq` | `‖A‖² = (m k)² + 2 m H ‖L‖²` |
| `norm_lrlVector_lt_iff` | eccentricity `< 1` ⇔ `H < 0` (bound orbits are ellipses) |
| `poissonBracket_lrlVector_hamiltonian` | `{Aᵢ, H} = 0` away from the origin |
| `lrlVector_eq_of_hamiltonEqOp` | `A` is constant along solutions of Hamilton's equations |
| `inner_lrlVector_position_of_hamiltonEqOp` | Kepler's first law along trajectories |

## The hidden `so(4)` symmetry (`KeplerLRL/SO4.lean`)

Components along fixed vectors `a`, `b` (`X_a = ⟪a, X⟫`); `M = A / √(-2 m H)` and
`J± = (L ± M) / 2` on the bound region `H < 0`:

| Lean name | Statement |
|---|---|
| `poissonBracket_angularMomentum_angularMomentum` | `{L_a, L_b} = L_{a×b}` |
| `poissonBracket_lrlVector_angularMomentum` | `{A_a, L_b} = A_{a×b}` |
| `poissonBracket_lrlVector_lrlVector` | `{A_a, A_b} = -2 m H L_{a×b}` |
| `poissonBracket_angularMomentum_hamiltonian` | `{L_a, H} = 0` for any central force |
| `poissonBracket_scaledLrlVector_scaledLrlVector` | `{M_a, M_b} = L_{a×b}` |
| `poissonBracket_jPlus_jPlus`, `…_jMinus_jMinus` | `{J±_a, J±_b} = J±_{a×b}` |
| `poissonBracket_jPlus_jMinus` | `{J+_a, J-_b} = 0`, so `so(4) ≅ so(3) ⊕ so(3)` |
| `norm_jPlus_sq`, `norm_jMinus_sq` | Casimirs `‖J±‖² = -m k² / (8 H)` |
| `hamiltonian_eq_of_norm_jPlus` | `H = -m k² / (8 ‖J+‖²)` |

No `sorry`; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.

## Building

Requires [elan](https://github.com/leanprover/elan). Lean `v4.35.0`, Physlib commit `3bfc7af`.

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

From this folder. The paper builds with `cd paper && latexmk -pdf main`.

