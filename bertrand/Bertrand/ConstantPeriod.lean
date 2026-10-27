/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Mathlib
/-!

# A constant half-period forces a vanishing third derivative

For a smooth `X` near `0`, the average `∫ θ in -(π/2)..π/2, X' (σ sin θ)` equals
`π X' 0 + (π / 4) X''' 0 σ² + o(σ²)` (odd terms integrate to zero, `∫ sin² = π / 2`). Hence if it
equals `π X' 0` for all small `σ = √(2ε)`, then `X''' 0 = 0`.
-/

open Set Filter Topology Real
open scoped ContDiff

namespace Bertrand

/-- Peano form of Taylor's theorem to second order at `0`: for every `η > 0`, the remainder is
bounded by `η y²` near `0`. The linear coefficient is left existential since it is not needed. -/
lemma exists_taylor_two_bound {g : ℝ → ℝ} {ρ η : ℝ} (hρ : 0 < ρ)
    (hg : ContDiffOn ℝ 2 g (Ioo (-ρ) ρ)) (hη : 0 < η) :
    ∃ b δ, 0 < δ ∧ ∀ y, |y| < δ →
      |g y - (g 0 + b * y + iteratedDeriv 2 g 0 / 2 * y ^ 2)| ≤ η * y ^ 2 := by
  have h0 : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨neg_lt_zero.2 hρ, hρ⟩
  have hT := taylor_isLittleO (convex_Ioo _ _) h0 hg
  rw [nhdsWithin_eq_nhds.2 (Ioo_mem_nhds h0.1 h0.2)] at hT
  obtain ⟨δ, hδ, hδy⟩ := Metric.eventually_nhds_iff.1 (hT.def hη)
  refine ⟨iteratedDerivWithin 1 g (Ioo (-ρ) ρ) 0, δ, hδ, fun y hy => ?_⟩
  have h2 : iteratedDerivWithin 2 g (Ioo (-ρ) ρ) 0 = iteratedDeriv 2 g 0 :=
    iteratedDerivWithin_of_isOpen isOpen_Ioo h0
  have := hδy (y := y) (by simpa using hy)
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, h2, Real.norm_eq_abs] at this
  convert this using 2
  · norm_num; ring
  · simp [sq_abs]

/-- `∫ θ in -(π/2)..π/2, (a + b sin θ + c sin² θ) = π a + (π / 2) c`. -/
lemma integral_quadratic_sin (a b c : ℝ) :
    ∫ θ in -(π / 2)..π / 2, (a + b * sin θ + c * sin θ ^ 2) = π * a + π / 2 * c := by
  have hi : ∀ {f : ℝ → ℝ}, Continuous f →
      IntervalIntegrable f MeasureTheory.volume (-(π / 2)) (π / 2) :=
    fun hf => hf.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    intervalIntegral.integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_sin,
    integral_sin_sq]
  simp
  ring

/-- If `∫ θ in -(π/2)..π/2, X' (√(2ε) sin θ) = π X' 0` for all small `ε > 0`, then
`X''' 0 = 0`. -/
theorem iteratedDeriv_three_eq_zero_of_integral_const {X : ℝ → ℝ} {ρ ε₁ : ℝ} (hρ : 0 < ρ)
    (hε₁ : 0 < ε₁) (hX : ContDiffOn ℝ ∞ X (Ioo (-ρ) ρ))
    (h : ∀ ε ∈ Ioo 0 ε₁, ∫ θ in -(π / 2)..π / 2, deriv X (√(2 * ε) * sin θ) = π * deriv X 0) :
    iteratedDeriv 3 X 0 = 0 := by
  set g := deriv X
  set c := iteratedDeriv 2 g 0
  rw [iteratedDeriv_succ']
  have hg : ContDiffOn ℝ 2 g (Ioo (-ρ) ρ) := hX.deriv_of_isOpen isOpen_Ioo (by simp)
  by_contra hc
  have hc' : 0 < |c| := abs_pos.2 hc
  obtain ⟨b, δ, hδ, hδy⟩ := exists_taylor_two_bound hρ hg (η := |c| / 8) (by positivity)
  set σ := min (min (δ / 2) (ρ / 2)) √ε₁
  have hσ : 0 < σ := lt_min (lt_min (by positivity) (by positivity)) (Real.sqrt_pos.2 hε₁)
  have hσδ : σ < δ := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hσρ : σ < ρ := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hσε : σ ^ 2 / 2 ∈ Ioo 0 ε₁ := by
    refine ⟨by positivity, ?_⟩
    have : σ ^ 2 ≤ ε₁ := by
      calc σ ^ 2 ≤ √ε₁ ^ 2 := pow_le_pow_left₀ hσ.le (min_le_right _ _) 2
        _ = ε₁ := Real.sq_sqrt hε₁.le
    linarith
  have hI := h _ hσε
  rw [show 2 * (σ ^ 2 / 2) = σ ^ 2 by ring, Real.sqrt_sq hσ.le] at hI
  have hmem : ∀ θ, σ * sin θ ∈ Ioo (-ρ) ρ := fun θ => by
    have := abs_sin_le_one θ
    have : |σ * sin θ| < ρ := by
      rw [abs_mul, abs_of_pos hσ]; nlinarith [abs_nonneg (sin θ)]
    exact ⟨by linarith [neg_abs_le (σ * sin θ)], by linarith [le_abs_self (σ * sin θ)]⟩
  have hcont : Continuous fun θ => g (σ * sin θ) :=
    continuous_iff_continuousAt.2 fun θ =>
      ((hg.continuousOn.continuousAt (Ioo_mem_nhds (hmem θ).1 (hmem θ).2)).comp
        (f := fun θ => σ * sin θ) (by fun_prop) :)
  have hJ := integral_quadratic_sin (g 0) (b * σ) (c / 2 * σ ^ 2)
  have hR : ∫ θ in -(π / 2)..π / 2,
      (g (σ * sin θ) - (g 0 + b * σ * sin θ + c / 2 * σ ^ 2 * sin θ ^ 2)) =
        -(π / 4 * c * σ ^ 2) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), hI, hJ]
    ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (C := |c| / 8 * σ ^ 2)
    (f := fun θ => g (σ * sin θ) - (g 0 + b * σ * sin θ + c / 2 * σ ^ 2 * sin θ ^ 2))
    (a := -(π / 2)) (b := π / 2) fun θ _ => by
      have hy : |σ * sin θ| < δ := by
        rw [abs_mul, abs_of_pos hσ]; nlinarith [abs_sin_le_one θ, abs_nonneg (sin θ)]
      have := hδy _ hy
      rw [Real.norm_eq_abs]
      calc _ = |g (σ * sin θ) - (g 0 + b * (σ * sin θ) + c / 2 * (σ * sin θ) ^ 2)| := by
            ring_nf
        _ ≤ |c| / 8 * (σ * sin θ) ^ 2 := this
        _ ≤ |c| / 8 * σ ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [mul_pow]
            nlinarith [sin_sq_le_one θ, sq_nonneg σ]
  rw [hR, norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < π / 4),
    abs_of_pos (by positivity : (0:ℝ) < σ ^ 2),
    abs_of_pos (by linarith [pi_pos] : (0:ℝ) < π / 2 - -(π / 2))] at hbound
  nlinarith [pi_pos, mul_pos (mul_pos pi_pos hc') (pow_pos hσ 2)]

end Bertrand
