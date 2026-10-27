# Bertrand's theorem — formalization blueprint

Goal: Bertrand's theorem (only `V ∝ -1/r` and `V ∝ r²` give closed bounded orbits), staged.
Unit mass. Variable `x = M / r`; effective potential `U x = x²/2 + V (M/x)`; the radial motion in
the polar angle θ is an oscillation in `U`; apsidal angle Φ = half-period = `∫ dx / √(2(E - U))`
over the allowed component.

## Part I (this milestone): near-circular orbits closed ⇒ power law

`Bertrand/NearCircular.lean : forceLaw_of_closed_nearCircular`
Hypotheses on radii `(a, b)`: `V` C³, `V' > 0`, `3V' + rV'' > 0` (stable circular orbits),
every orbit near each circular orbit has Φ ∈ πℚ. Conclusion: ∃ β ∈ ℚ₊,
`3 + rV''/V' = β²` and `V' r = C r^(β²-3)`.

Files / owners:
- `Chart.lean` (shared, frozen): `apsidalAngle U Ω x₀ E` (integral over
  `connectedComponentIn (Ω ∩ {U < E}) x₀`), `MorseChart` structure.
- `MorseLemma.lean` (agent A1): `exists_morseChart` — C³, U'=0, U''>0 ⇒ chart with X'(0) = 1/√U''.
- `ApsidalChart.lean` (agent A2): `apsidalAngle_eq` (Φ = ∫_{-π/2}^{π/2} X'(√(2ε) sin θ) dθ),
  `exists_continuousOn_apsidalAngle` (Φ extends continuously to ε=0 with value π X'(0)).
- `EffPot.lean` (me): effPot calculus (U'(x₀)=0, U''(x₀)=3+rV''/V'), C³-ness, rational-valued
  continuous ⇒ constant, ODE `rV'' = pV'` ⇒ power law.
- `NearCircular.lean` (me): assembly.

Assembly proof: for each r: chart at x₀ = M/r; F continuous on [0,ρ²/2), equal to Φ(U₀+ε);
hclosed ⇒ F(ε) ∈ πℚ for small ε>0 ⇒ F constant on (0,ε₁) ⇒ F(0) = π/√U''(x₀) ∈ πℚ ⇒
√(3 + rV''/V') ∈ ℚ. Continuous + ℚ-valued on (a,b) ⇒ constant β. ODE ⇒ power law.

## Part II (next): power law with all bounded orbits closed ⇒ β ∈ {1, 2}

For `V' = C r^(β²-3)` on (0,∞): Φ(E) is constant = π/β for all bound energies (continuity +
rationality on the connected energy range). Compare with limits:
- α := β² - 2 > 0 (V ∝ r^α): E → ∞ gives Φ → π/2 ⇒ β = 2 (harmonic).
- -2 < α < 0: E → 0⁻ gives Φ → π/(2+α) = π/β² ⇒ β = 1 (Kepler).
- α = 0 (log potential) ⇒ β = √2 irrational, excluded in part I.
Needs: global Morse chart for single-well U, the two energy-limit integrals.

## Part III (later): trajectories

Orbits of the Newtonian ODE are closed iff Φ ∈ πℚ (θ-parametrisation, periodicity).

## References
- V. I. Arnold, Mathematical Methods of Classical Mechanics, §8 (problem on Bertrand).
- J. Bertrand, C. R. Acad. Sci. Paris 77 (1873) 849–853.
- J. Féjoz, L. Kaczmarek, Ergodic Theory Dynam. Systems 24 (2004) — rigorous local proof.
