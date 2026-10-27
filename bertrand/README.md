# Bertrand's theorem in Lean 4

**Theorem (local Bertrand, after Herman / Féjoz–Kaczmarek).** Let `V` be smooth on radii `(a, b)`,
with every circular orbit there stable (`V' > 0`, `3V' + rV'' > 0`). If every orbit close enough to
a circular one is closed (apsidal angle ∈ πℚ), then `V'(r) = C / r²` (Newton) or `V'(r) = C r`
(Hooke) for some `C > 0`. Lean: `Bertrand.bertrand` in `Bertrand/Full.lean`.

**Paper:** [`paper/main.pdf`](paper/main.pdf) (Nichlas Löfdahl, Claude).

No `sorry`; `#print axioms Bertrand.bertrand` shows only `propext`, `Classical.choice`, `Quot.sound`.

## Files

| File | Content |
|---|---|
| `Chart.lean` | `apsidalAngle` (singular integral over the allowed component), `MorseChart` |
| `MorseLemma.lean` | C¹ Morse lemma via L'Hôpital + inverse function theorem |
| `ApsidalChart.lean` | apsidal angle = `∫ X'(√(2ε) sin θ) dθ`; continuity in the energy |
| `EffPot.lean` | effective potential, `U'' = 3 + rV''/V'`, rational ⇒ constant, ODE ⇒ power law |
| `NearCircular.lean` | **part I**: `forceLaw_of_closed_nearCircular` (power law, constant apsidal angle) |
| `SmoothChart.lean` | real Hadamard lemma (smooth `dslope`), smooth Morse chart |
| `ConstantPeriod.lean` | constant `∫ X'(σ sin θ) dθ` ⇒ `X''' 0 = 0` (Taylor/Peano) |
| `ChartDerivs.lean` | `X''' 0 = 0` ⇒ isochrony `5U'''² = 3U''U''''` |
| `PowerLaw.lean` | `U''`, `U'''`, `U''''` for a power law; isochrony ⇒ `p = -2 ∨ p = 1` |
| `Full.lean` | **Bertrand's theorem** `bertrand` |

## Building

From this folder (Lean `v4.35.0`, Mathlib `56a0058`): `lake exe cache get && lake build`.
`scripts/check.sh <file>` elaborates one file and lists remaining `sorry`s.

## Not (yet) formalized
- Closedness is defined via the apsidal angle; deriving this from Newton's equations is future work.
- The converse (Newton/Hooke satisfy the hypotheses) — checked numerically only.
