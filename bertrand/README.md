# Bertrand's theorem (part I) in Lean 4

**Closed near-circular orbits force a power law.** If every circular orbit with radius in `(a, b)`
is stable and every nearby orbit is closed (apsidal angle ∈ πℚ), then `3 + rV''/V' = β²` for a
constant rational `β > 0` and the force is a power law `V'(r) = C r^(β²-3)`. This is the first
half of Bertrand's theorem; part II (only β = 1, 2 survive) is in progress — see
[`BLUEPRINT.md`](BLUEPRINT.md).

**Paper:** [`paper/main.pdf`](paper/main.pdf) (Nichlas Löfdahl, Claude).

## Files

| File | Content |
|---|---|
| `Bertrand/Chart.lean` | `apsidalAngle` (singular integral over the allowed component), `MorseChart` |
| `Bertrand/MorseLemma.lean` | 1-D Morse lemma: `exists_morseChart` (via L'Hôpital + inverse function theorem) |
| `Bertrand/ApsidalChart.lean` | apsidal angle = `∫ X'(√(2ε) sin θ) dθ`; continuity in the energy |
| `Bertrand/EffPot.lean` | effective potential, `U'' = 3 + rV''/V'`, rational ⇒ constant, ODE ⇒ power law |
| `Bertrand/NearCircular.lean` | main theorem `forceLaw_of_closed_nearCircular` |

## Building

From this folder (Lean `v4.35.0`, Mathlib `56a0058`): `lake exe cache get && lake build`.
`scripts/check.sh <file>` elaborates one file and lists remaining `sorry`s.
