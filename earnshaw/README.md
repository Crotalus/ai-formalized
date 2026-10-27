# Earnshaw's theorem in Lean 4

A harmonic function has no strict local minimum or maximum, so a static electric potential cannot
trap a charge in stable equilibrium. Machine-checked with Lean 4 and Mathlib.

**Paper:** [`paper/main.pdf`](paper/main.pdf) — *A Formal Proof of Earnshaw's Theorem in Lean 4*
(Nichlas Löfdahl, Claude).

## Results (`Earnshaw/Basic.lean`)

`E` is any finite-dimensional real inner product space with `dim E ≥ 1`.

| Lean name | Statement |
|---|---|
| `deriv_deriv_comp_line` | second derivative of `t ↦ g (z + t v)` at 0 is the Hessian `D²g(z)(v,v)` |
| `iteratedFDeriv_two_nonneg_of_isLocalMin` | Hessian is positive semidefinite at a local minimum |
| `laplacian_norm_sub_sq` | `Δ ‖· - x‖² = 2 dim E` |
| `not_posDef_hessian_of_laplacian_eq_zero` | `Δ f x = 0` ⇒ Hessian not positive definite (linear instability) |
| `HarmonicAt.not_isStrictLocalMin` / `…Max` | **Earnshaw's theorem** |
| `earnshaw` | a test charge `q` in a harmonic potential `V` on ℝ³ has no stable equilibrium |

No `sorry`, no warnings; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
The proof avoids the mean-value property (not yet in Mathlib) via a perturbation argument.

## Building

From this folder (Lean `v4.35.0`, Mathlib `56a0058`):

```bash
lake exe cache get
lake build
```

`scripts/check.sh` elaborates the file and lists remaining `sorry`s. Paper: `cd paper && latexmk -pdf main`.
