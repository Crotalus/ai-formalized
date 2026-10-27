/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.EffPot
import Bertrand.MorseLemma
import Bertrand.ApsidalChart
/-!

# Bertrand's theorem, part I: closed near-circular orbits force a power law

If on an interval of radii every circular orbit is stable and every orbit near it is closed (its
apsidal angle is a rational multiple of `π`), then `√(3 + r V'' / V')` is a rational constant `β`
and the force is a power law, `V' r = C r ^ (β² - 3)`.

The proof combines the Morse lemma (`exists_morseChart`), the continuity of the apsidal angle in
the energy up to the circular orbit (`MorseChart.exists_continuousOn_apsidalAngle`), and the
computation `U'' = 3 + r V'' / V'` (`iteratedDeriv_two_effPot_circular`).
-/

open Set Filter Topology Real

namespace Bertrand

/-!

## D. Bertrand's theorem, part I

-/

/-- At a single radius: if the orbits near the stable circular orbit of radius `r` are closed,
then their apsidal angle is constant, equal to `π / √(U'')` with `U'' = 3 + r V'' / V'`, and this
is a rational multiple of `π`. -/
lemma apsidalAngle_const_of_closed {V : ℝ → ℝ} {a b r : ℝ} (ha : 0 < a) (hab : a < b)
    (hV : ContDiffOn ℝ 3 V (Ioo a b)) (hr : r ∈ Ioo a b) (hV' : 0 < deriv V r)
    (hk : 0 < 3 + r * iteratedDeriv 2 V r / deriv V r)
    (hclosed : ∀ᶠ E in 𝓝[>] (circularEnergy V r),
      ∃ q : ℚ, orbitApsidalAngle V a b r E = q * π) :
    (∃ ε₂ > 0, ∀ ε ∈ Ioo 0 ε₂, orbitApsidalAngle V a b r (circularEnergy V r + ε) =
      π / √(3 + r * iteratedDeriv 2 V r / deriv V r)) ∧
      ∃ q : ℚ, π / √(3 + r * iteratedDeriv 2 V r / deriv V r) = q * π := by
  have hr0 : 0 < r := ha.trans hr.1
  have hb : 0 < b := ha.trans hab
  have hM : 0 < angMom V r := Real.sqrt_pos.mpr (by positivity)
  have hx₀ : angMom V r / r ∈ Ioo (angMom V r / b) (angMom V r / a) :=
    ⟨div_lt_div_of_pos_left hM hr0 hr.2, div_lt_div_of_pos_left hM ha hr.1⟩
  have hU2 := iteratedDeriv_two_effPot_circular ha hV hr hV'
  obtain ⟨c, hc⟩ := exists_morseChart isOpen_Ioo hx₀ (contDiffOn_effPot ha hab hM hV)
    (deriv_effPot_circular hr0 hV' ((hV.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt
      (by norm_num))) (hU2 ▸ hk)
  obtain ⟨F, hFc, hF0, hFeq⟩ := c.exists_continuousOn_apsidalAngle
  -- Energies just above the circular one give closed orbits.
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hclosed
  set U₀ := circularEnergy V r
  set ε₂ := min (u - U₀) (c.ρ ^ 2 / 2) with hε₂
  have hε₂pos : 0 < ε₂ := lt_min (sub_pos.mpr hu) (by have := c.ρ_pos; positivity)
  have hFrat : ∀ ε ∈ Ioo 0 ε₂, ∃ q : ℚ, F ε / π = q := fun ε hε => by
    have hmin := min_le_left (u - U₀) (c.ρ ^ 2 / 2)
    have hmem : U₀ + ε ∈ Ioo U₀ u := ⟨by linarith [hε.1], by linarith [hε.2]⟩
    obtain ⟨q, hq⟩ := hsub hmem
    refine ⟨q, ?_⟩
    rw [← hFeq ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩]
    exact (div_eq_iff pi_ne_zero).mpr hq
  -- So `F / π` is constant on `(0, ε₂)`, and by continuity `F 0` is a rational multiple of `π`.
  have hsub' : Ioo 0 ε₂ ⊆ Ico 0 (c.ρ ^ 2 / 2) := fun ε hε =>
    ⟨hε.1.le, hε.2.trans_le (min_le_right _ _)⟩
  have hFdiv : ContinuousOn (fun ε => F ε / π) (Ioo 0 ε₂) :=
    (hFc.mono hsub').div_const π
  have hmid : ε₂ / 2 ∈ Ioo 0 ε₂ := ⟨by positivity, by linarith⟩
  obtain ⟨q, hq⟩ := hFrat _ hmid
  have hconst : ∀ ε ∈ Ioo 0 ε₂, F ε = F (ε₂ / 2) := fun ε hε => by
    have := eq_of_continuousOn_rat isPreconnected_Ioo hFdiv hFrat hε hmid
    field_simp at this
    exact this
  have hlim : Tendsto F (𝓝[Ioo 0 ε₂] 0) (𝓝 (F 0)) :=
    ((hFc 0 ⟨le_rfl, by have := c.ρ_pos; positivity⟩).mono hsub').tendsto
  have hlim' : Tendsto F (𝓝[Ioo 0 ε₂] 0) (𝓝 (F (ε₂ / 2))) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ε hε => (hconst ε hε).symm)
  have := left_nhdsWithin_Ioo_neBot hε₂pos
  have hF0' : F 0 = F (ε₂ / 2) := tendsto_nhds_unique hlim hlim'
  -- `F 0 = π / √(U'')`, so the apsidal angle is constant with that value.
  rw [hF0, hc, hU2] at hF0'
  refine ⟨⟨ε₂, hε₂pos, fun ε hε => ?_⟩, q, ?_⟩
  · rw [show orbitApsidalAngle V a b r (circularEnergy V r + ε) = F ε from
      hFeq ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩, hconst ε hε, ← hF0']
    ring
  · rw [show π / √(3 + r * iteratedDeriv 2 V r / deriv V r) = F (ε₂ / 2) by rw [← hF0']; ring]
    exact (div_eq_iff pi_ne_zero).mp hq

/-- At a single radius: if the orbits near the stable circular orbit of radius `r` are closed,
then `√(U'') = √(3 + r V'' / V')` is rational. -/
lemma sqrt_rat_of_closed {V : ℝ → ℝ} {a b r : ℝ} (ha : 0 < a) (hab : a < b)
    (hV : ContDiffOn ℝ 3 V (Ioo a b)) (hr : r ∈ Ioo a b) (hV' : 0 < deriv V r)
    (hk : 0 < 3 + r * iteratedDeriv 2 V r / deriv V r)
    (hclosed : ∀ᶠ E in 𝓝[>] (circularEnergy V r),
      ∃ q : ℚ, orbitApsidalAngle V a b r E = q * π) :
    ∃ q : ℚ, √(3 + r * iteratedDeriv 2 V r / deriv V r) = q := by
  obtain ⟨-, q, hq⟩ := apsidalAngle_const_of_closed ha hab hV hr hV' hk hclosed
  have hs := Real.sqrt_pos.mpr hk
  rw [div_eq_iff hs.ne'] at hq
  have h1 : √(3 + r * iteratedDeriv 2 V r / deriv V r) * q = 1 :=
    mul_right_cancel₀ pi_ne_zero (by linear_combination -hq)
  exact ⟨q⁻¹, by push_cast; exact eq_inv_of_mul_eq_one_left h1⟩

/-- **Bertrand's theorem, part I.** Suppose that on the radii `(a, b)` every circular orbit is
stable, and that every orbit close enough to a circular one is closed: its apsidal angle is a
rational multiple of `π`. Then there is a positive rational `β` with `3 + r V'' / V' = β²`
throughout, so the force is a power law `V' r = C r ^ (β² - 3)`. -/
theorem forceLaw_of_closed_nearCircular {V : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hV : ContDiffOn ℝ 3 V (Ioo a b))
    (hpos : ∀ r ∈ Ioo a b, 0 < deriv V r)
    (hstab : ∀ r ∈ Ioo a b, 0 < 3 * deriv V r + r * iteratedDeriv 2 V r)
    (hclosed : ∀ r ∈ Ioo a b, ∀ᶠ E in 𝓝[>] (circularEnergy V r),
      ∃ q : ℚ, orbitApsidalAngle V a b r E = q * π) :
    ∃ β : ℚ, 0 < β ∧ (∃ C > 0, ∀ r ∈ Ioo a b, deriv V r = C * r ^ ((β : ℝ) ^ 2 - 3)) ∧
      ∀ r ∈ Ioo a b, 3 + r * iteratedDeriv 2 V r / deriv V r = (β : ℝ) ^ 2 := by
  set k : ℝ → ℝ := fun r => 3 + r * iteratedDeriv 2 V r / deriv V r with hkdef
  have hk : ∀ r ∈ Ioo a b, 0 < k r := fun r hr => by
    have := hpos r hr
    simp only [hkdef]
    rw [show 3 + r * iteratedDeriv 2 V r / deriv V r =
      (3 * deriv V r + r * iteratedDeriv 2 V r) / deriv V r by field_simp]
    exact div_pos (hstab r hr) this
  -- Step 1: at every radius, `√(U'') = √(3 + r V'' / V')` is rational.
  have hrat : ∀ r ∈ Ioo a b, ∃ q : ℚ, √(k r) = q := fun r hr =>
    sqrt_rat_of_closed ha hab hV hr (hpos r hr) (hk r hr) (hclosed r hr)
  -- Step 2: it is continuous in `r`, hence constant.
  have hcont : ContinuousOn (fun r => √(k r)) (Ioo a b) := by
    have hV1 : ContDiffOn ℝ 2 (deriv V) (Ioo a b) := hV.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hV2 : ContinuousOn (iteratedDeriv 2 V) (Ioo a b) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact (hV1.deriv_of_isOpen isOpen_Ioo (by norm_num) (m := 1)).continuousOn
    exact (continuousOn_const.add ((continuousOn_id.mul hV2).div hV1.continuousOn
      fun r hr => (hpos r hr).ne')).sqrt
  obtain ⟨r₁, hr₁⟩ : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
  obtain ⟨β, hβ⟩ := hrat r₁ hr₁
  have hall : ∀ r ∈ Ioo a b, √(k r) = β := fun r hr =>
    (eq_of_continuousOn_rat isPreconnected_Ioo hcont hrat hr hr₁).trans hβ
  have hβpos : (0 : ℝ) < β := hβ ▸ Real.sqrt_pos.mpr (hk r₁ hr₁)
  have hksq : ∀ r ∈ Ioo a b, k r = (β : ℝ) ^ 2 := fun r hr => by
    rw [← hall r hr, Real.sq_sqrt (hk r hr).le]
  -- Step 3: `r V'' = (β² - 3) V'`, so `V'` is a power law.
  have hode : ∀ r ∈ Ioo a b, r * iteratedDeriv 2 V r = ((β : ℝ) ^ 2 - 3) * deriv V r :=
    fun r hr => by
      have h := hksq r hr
      have := (hpos r hr).ne'
      simp only [hkdef] at h
      field_simp at h
      linear_combination h
  obtain ⟨C, hC⟩ := deriv_eq_rpow_of_ode ha hV hode
  have hCpos : 0 < C := by
    have h := hpos r₁ hr₁
    rw [hC r₁ hr₁] at h
    exact pos_of_mul_pos_left h (Real.rpow_pos_of_pos (ha.trans hr₁.1) _).le
  exact ⟨β, by exact_mod_cast hβpos, ⟨C, hCpos, hC⟩, hksq⟩

end Bertrand
