# Kepler's first law and the Laplace–Runge–Lenz vector in Lean 4

A machine-checked formalization of the classical Kepler problem in [Lean 4](https://lean-lang.org)
on top of [Physlib](https://github.com/leanprover-community/physlib) and Mathlib.

**Paper:** [`paper/main.pdf`](paper/main.pdf) — *A Formal Proof of the Conservation of the
Laplace–Runge–Lenz Vector and Kepler's First Law in Lean 4* (Nichlas Lofdahl, Claude).

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

No `sorry`; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.

## Building

Requires [elan](https://github.com/leanprover/elan). Lean `v4.35.0`, Physlib commit `3bfc7af`.

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

From this folder. The paper builds with `cd paper && latexmk -pdf main`.

