/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Mathlib
/-!

# Apsidal angles and Morse charts

Shared definitions for the proof of Bertrand's theorem.

A particle in a one-dimensional potential well `U` with energy `E` oscillates between two turning
points; the time it takes (in the variable conjugate to the oscillation) to go from one turning
point to the other is
`∫ x in (allowed region around x₀), 1 / √(2 (E - U x))`.
For the radial motion of a central-force orbit written in the variable `x = M / r` with the polar
angle as "time", this integral is the **apsidal angle**: the angle swept between pericentre and
apocentre.

We define the allowed region as the connected component, containing the bottom of the well `x₀`,
of `{x ∈ Ω | U x < E}`. Outside it the integrand is irrelevant.

A **Morse chart** at `x₀` is a coordinate `s` in which `U = U x₀ + s² / 2`, given by its inverse
`X : s ↦ x`. Near a nondegenerate minimum of a `C³` function such a chart exists, and in it the
apsidal angle becomes a regular (non-singular) integral, which makes continuity in `E` and the
near-circular limit transparent.
-/

open Set Filter Topology Real

namespace Bertrand

/-- The apsidal angle (half-period) of oscillation in the potential `U`, restricted to the domain
`Ω`, at energy `E`, in the well containing `x₀`. -/
noncomputable def apsidalAngle (U : ℝ → ℝ) (Ω : Set ℝ) (x₀ E : ℝ) : ℝ :=
  ∫ x in connectedComponentIn (Ω ∩ {x | U x < E}) x₀, 1 / √(2 * (E - U x))

/-- A Morse chart for `U` at `x₀` inside `Ω`: a `C¹` map `X` from `(-ρ, ρ)` into `Ω` with positive
derivative and `X 0 = x₀`, such that `U (X s) = U x₀ + s² / 2`. -/
structure MorseChart (U : ℝ → ℝ) (Ω : Set ℝ) (x₀ : ℝ) where
  /-- The inverse chart, from the Morse coordinate `s` to the position `x`. -/
  X : ℝ → ℝ
  /-- The radius of the chart in the Morse coordinate. -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  X_zero : X 0 = x₀
  mapsTo : MapsTo X (Ioo (-ρ) ρ) Ω
  hasDerivAt : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt X (deriv X s) s
  deriv_pos : ∀ s ∈ Ioo (-ρ) ρ, 0 < deriv X s
  continuousOn_deriv : ContinuousOn (deriv X) (Ioo (-ρ) ρ)
  U_comp : ∀ s ∈ Ioo (-ρ) ρ, U (X s) = U x₀ + s ^ 2 / 2

end Bertrand
