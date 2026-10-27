/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.NearCircular
import Bertrand.PowerLaw
import Bertrand.SmoothChart
import Bertrand.ChartDerivs
import Bertrand.ConstantPeriod
/-!

# Bertrand's theorem

If on an interval of radii every circular orbit is stable and every orbit near a circular one is
closed, then the force is either Newton's inverse-square law or Hooke's law.

Part I (`forceLaw_of_closed_nearCircular`) shows the force is a power law `V' = C r ^ p` and that
the apsidal angle is constant near each circular orbit. In a smooth Morse chart the apsidal angle
is `∫ X' (√(2ε) sin θ) dθ = π X' 0 + (π/2) X''' 0 ε + o(ε)`, so constancy forces `X''' 0 = 0`
(`iteratedDeriv_three_eq_zero_of_integral_const`), which is the isochrony condition
`5 U'''² = 3 U'' U''''` (`MorseChart.isochrony_of_iteratedDeriv_three_eq_zero`). For a power law
this reads `(p + 2)(p - 1) = 0` (`powerLaw_eq_of_isochrony`).

This is the local form of Bertrand's theorem (cf. Féjoz–Kaczmarek, after Herman).
-/

open Set Filter Topology Real
open scoped ContDiff

namespace Bertrand

/-- **Bertrand's theorem.** Suppose that on the radii `(a, b)` the potential `V` is smooth, every
circular orbit is stable, and every orbit close enough to a circular one is closed (its apsidal
angle is a rational multiple of `π`). Then the force is either the inverse-square law
`V' r = C / r²` or Hooke's law `V' r = C r`, with `C > 0`. -/
theorem bertrand {V : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hV : ContDiffOn ℝ ∞ V (Ioo a b))
    (hpos : ∀ r ∈ Ioo a b, 0 < deriv V r)
    (hstab : ∀ r ∈ Ioo a b, 0 < 3 * deriv V r + r * iteratedDeriv 2 V r)
    (hclosed : ∀ r ∈ Ioo a b, ∀ᶠ E in 𝓝[>] (circularEnergy V r),
      ∃ q : ℚ, orbitApsidalAngle V a b r E = q * π) :
    ∃ C > 0, (∀ r ∈ Ioo a b, deriv V r = C / r ^ 2) ∨ (∀ r ∈ Ioo a b, deriv V r = C * r) := by
  have hV3 : ContDiffOn ℝ 3 V (Ioo a b) := hV.of_le (by norm_num)
  -- Part I: a power law, with constant apsidal angle near circular orbits.
  obtain ⟨β, hβ, ⟨C, hC, hpow⟩, hk⟩ :=
    forceLaw_of_closed_nearCircular ha hab hV3 hpos hstab hclosed
  have hβ' : (0 : ℝ) < β := by exact_mod_cast hβ
  obtain ⟨r, hr⟩ : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
  have hr0 : 0 < r := ha.trans hr.1
  have hkr : 0 < 3 + r * iteratedDeriv 2 V r / deriv V r := by rw [hk r hr]; positivity
  obtain ⟨⟨ε₂, hε₂, hconst⟩, -⟩ :=
    apsidalAngle_const_of_closed ha hab hV3 hr (hpos r hr) hkr (hclosed r hr)
  -- A smooth Morse chart at the circular orbit of radius `r`.
  have hM : 0 < angMom V r := Real.sqrt_pos.mpr (by have := hpos r hr; positivity)
  have hx₀ : angMom V r / r ∈ Ioo (angMom V r / b) (angMom V r / a) :=
    ⟨div_lt_div_of_pos_left hM hr0 hr.2, div_lt_div_of_pos_left hM ha hr.1⟩
  have hU := contDiffOn_effPot ha hab hM hV
  have hU2 := iteratedDeriv_two_effPot_circular ha hV3 hr (hpos r hr)
  obtain ⟨c, hcX, hc0⟩ := exists_smoothMorseChart isOpen_Ioo hx₀ hU
    (deriv_effPot_circular hr0 (hpos r hr)
      ((hV3.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num))) (hU2 ▸ hkr)
  -- In the chart, the constant apsidal angle is `∫ X' (√(2ε) sin θ) dθ = π X' 0`.
  have hint : ∀ ε ∈ Ioo 0 (min ε₂ (c.ρ ^ 2 / 2)),
      ∫ θ in -(π / 2)..π / 2, deriv c.X (√(2 * ε) * sin θ) = π * deriv c.X 0 := fun ε hε => by
    rw [← c.apsidalAngle_eq hε.1 (hε.2.trans_le (min_le_right _ _)), hc0, hU2]
    have h := hconst ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
    simp only [orbitApsidalAngle, circularEnergy] at h
    rw [h]
    ring
  have h3 := iteratedDeriv_three_eq_zero_of_integral_const c.ρ_pos
    (lt_min hε₂ (by have := c.ρ_pos; positivity)) hcX hint
  -- The isochrony condition for the power law leaves only `p = -2` or `p = 1`.
  have hiso := c.isochrony_of_iteratedDeriv_three_eq_zero isOpen_Ioo hU hcX h3
  obtain ⟨hu2, hu3, hu4⟩ := iteratedDeriv_effPot_powerLaw ha (hV3.differentiableOn (by norm_num))
    hr hC hpow
  rw [hu2, hu3, hu4] at hiso
  have hp3 : 0 < (β : ℝ) ^ 2 - 3 + 3 := by ring_nf; positivity
  refine ⟨C, hC, ?_⟩
  rcases powerLaw_eq_of_isochrony (by positivity) hp3 hiso with h | h
  · left
    intro y hy
    rw [hpow y hy, h, Real.rpow_neg (ha.trans hy.1).le, Real.rpow_two, div_eq_mul_inv]
  · right
    intro y hy
    rw [hpow y hy, h, Real.rpow_one]

end Bertrand
