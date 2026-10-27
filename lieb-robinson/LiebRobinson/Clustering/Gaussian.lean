/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import Mathlib
/-!

# A Gaussian filter for positive frequencies

The integral of `e^{-αt²} (e^{-iωt} - 1) / (it)` over the real line, without the error function.

## i. Overview

The exponential clustering theorem separates positive from negative frequencies of a function of
time with the kernel `e^{-αt²} / (it)`. Since `(e^{-iωt} - 1) / (it) = -∫₀^ω e^{-iσt} dσ`, Fubini
and the Fourier transform of the Gaussian give

$$\int_ℝ e^{-αt²} \frac{e^{-iωt} - 1}{it} \, dt = -\sqrt{π/α} \int_0^ω e^{-σ²/(4α)} \, dσ.$$

For `ω ≥ γ > 0` the right-hand side is within `(2 √(πα) / γ) e^{-γ²/(4α)}` of `-π`, and it is odd
in `ω`. Neither the error function nor principal values appear.

## ii. Key results

- `LiebRobinson.gaussStep` : `∫₀^ω e^{-σ²/(4α)} dσ`.
- `LiebRobinson.gaussKernel` : the integrand `e^{-αt²} (e^{-iωt} - 1) / (it)`.
- `LiebRobinson.integral_gaussKernel` : the value of its integral.
- `LiebRobinson.gaussStep_tail` : the step is close to its limit for frequencies above `γ`.

## iii. Table of contents

- A. The Gaussian step
- B. The kernel and its integral

## iv. References

* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
-/

@[expose] public section

namespace LiebRobinson

open MeasureTheory

/-!

## A. The Gaussian step

-/

/-- The Gaussian step `∫₀^ω e^{-σ²/(4α)} dσ`. -/
noncomputable def gaussStep (α ω : ℝ) : ℝ := ∫ σ in (0 : ℝ)..ω, Real.exp (-σ ^ 2 / (4 * α))

/-- The Gaussian step is odd in the frequency. -/
lemma gaussStep_neg (α ω : ℝ) : gaussStep α (-ω) = -gaussStep α ω := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := ω)
    (fun σ : ℝ => Real.exp (-σ ^ 2 / (4 * α)))
  simp only [neg_sq, neg_zero] at h
  rw [gaussStep, gaussStep, intervalIntegral.integral_symm, h]

/-- The Gaussian `e^{-σ²/(4α)}` is integrable for `α > 0`. -/
lemma integrable_exp_neg_sq_div {α : ℝ} (hα : 0 < α) :
    Integrable fun σ : ℝ => Real.exp (-σ ^ 2 / (4 * α)) := by
  have h := integrable_exp_neg_mul_sq (b := (4 * α)⁻¹) (by positivity)
  refine h.congr (ae_of_all _ fun σ => ?_)
  simp only
  ring_nf

/-- The Gaussian tail bound `∫_ω^∞ e^{-σ²/(4α)} dσ ≤ (2α/ω) e^{-ω²/(4α)}` for `ω > 0`. -/
lemma integral_Ioi_exp_neg_sq_div_le {α ω : ℝ} (hα : 0 < α) (hω : 0 < ω) :
    ∫ σ in Set.Ioi ω, Real.exp (-σ ^ 2 / (4 * α)) ≤
      2 * α / ω * Real.exp (-ω ^ 2 / (4 * α)) := by
  have hderiv : ∀ σ ∈ Set.Ici ω, HasDerivAt (fun σ => -(2 * α / ω) * Real.exp (-σ ^ 2 / (4 * α)))
      (σ / ω * Real.exp (-σ ^ 2 / (4 * α))) σ := by
    intro σ _
    have := ((((hasDerivAt_pow 2 σ).neg).div_const (4 * α)).exp).const_mul (-(2 * α / ω))
    convert this using 1
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hlim : Filter.Tendsto (fun σ => -(2 * α / ω) * Real.exp (-σ ^ 2 / (4 * α)))
      Filter.atTop (nhds 0) := by
    have hsq := (Filter.tendsto_neg_atTop_atBot.comp
      (Filter.tendsto_pow_atTop two_ne_zero)).atBot_div_const (by positivity : 0 < 4 * α)
    have h := (Real.tendsto_exp_atBot.comp hsq).const_mul (-(2 * α / ω))
    simpa only [mul_zero, Function.comp_def] using h
  have hpos : ∀ σ ∈ Set.Ioi ω, 0 ≤ σ / ω * Real.exp (-σ ^ 2 / (4 * α)) := fun σ hσ =>
    mul_nonneg (div_nonneg (hω.trans hσ).le hω.le) (Real.exp_pos _).le
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  calc ∫ σ in Set.Ioi ω, Real.exp (-σ ^ 2 / (4 * α))
      ≤ ∫ σ in Set.Ioi ω, σ / ω * Real.exp (-σ ^ 2 / (4 * α)) := by
        refine setIntegral_mono_on (integrable_exp_neg_sq_div hα).integrableOn
          (integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim) measurableSet_Ioi
          fun σ hσ => ?_
        have : 1 ≤ σ / ω := by rw [le_div_iff₀ hω]; simpa using (Set.mem_Ioi.1 hσ).le
        nlinarith [Real.exp_pos (-σ ^ 2 / (4 * α))]
    _ = 2 * α / ω * Real.exp (-ω ^ 2 / (4 * α)) := by rw [hval]; ring

/-- For frequencies `ω ≥ γ > 0`, `√(π/α) ∫₀^ω e^{-σ²/(4α)} dσ` lies within
`(2 √(πα) / γ) e^{-γ²/(4α)}` below its limit `π`. -/
theorem gaussStep_tail {α γ ω : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hω : γ ≤ ω) :
    0 ≤ Real.pi - Real.sqrt (Real.pi / α) * gaussStep α ω ∧
      Real.pi - Real.sqrt (Real.pi / α) * gaussStep α ω ≤
        2 * Real.sqrt (Real.pi * α) / γ * Real.exp (-γ ^ 2 / (4 * α)) := by
  have hω0 : 0 < ω := hγ.trans_le hω
  have hI := integrable_exp_neg_sq_div hα
  have hhalf : ∫ σ in Set.Ioi (0 : ℝ), Real.exp (-σ ^ 2 / (4 * α)) = Real.sqrt (Real.pi * α) := by
    have h := integral_gaussian_Ioi (4 * α)⁻¹
    have e : Real.pi / (4 * α)⁻¹ = 2 ^ 2 * (Real.pi * α) := by field_simp; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)] at h
    convert h using 1
    · congr 1; ext σ; ring_nf
    · ring
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := ω) hI.integrableOn
    hI.integrableOn
  rw [hhalf] at hsplit
  have hpi : Real.sqrt (Real.pi / α) * Real.sqrt (Real.pi * α) = Real.pi := by
    rw [← Real.sqrt_mul (by positivity),
      show Real.pi / α * (Real.pi * α) = Real.pi ^ 2 by field_simp]
    exact Real.sqrt_sq Real.pi_pos.le
  have hsq : Real.sqrt (Real.pi / α) * α = Real.sqrt (Real.pi * α) := by
    rw [show Real.pi * α = Real.pi / α * α ^ 2 by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hα.le]
  have heq : Real.pi - Real.sqrt (Real.pi / α) * gaussStep α ω =
      Real.sqrt (Real.pi / α) * ∫ σ in Set.Ioi ω, Real.exp (-σ ^ 2 / (4 * α)) := by
    rw [gaussStep]
    linear_combination -hpi - Real.sqrt (Real.pi / α) * hsplit
  rw [heq]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _)
    (setIntegral_nonneg measurableSet_Ioi fun σ _ => (Real.exp_pos _).le), ?_⟩
  calc Real.sqrt (Real.pi / α) * ∫ σ in Set.Ioi ω, Real.exp (-σ ^ 2 / (4 * α))
      ≤ Real.sqrt (Real.pi / α) * (2 * α / ω * Real.exp (-ω ^ 2 / (4 * α))) :=
        mul_le_mul_of_nonneg_left (integral_Ioi_exp_neg_sq_div_le hα hω0) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (Real.pi * α) / ω * Real.exp (-ω ^ 2 / (4 * α)) := by
        rw [← hsq]; ring
    _ ≤ 2 * Real.sqrt (Real.pi * α) / γ * Real.exp (-γ ^ 2 / (4 * α)) := by
        gcongr

/-!

## B. The kernel and its integral

-/

/-- The kernel `e^{-αt²} (e^{-iωt} - 1) / (it)`, with value `0` at `t = 0`. -/
noncomputable def gaussKernel (α ω t : ℝ) : ℂ :=
  (Real.exp (-α * t ^ 2) : ℂ) * ((Complex.exp (-(ω * t) * Complex.I) - 1) / (t * Complex.I))

/-- `|e^{-αt²} (e^{-iωt} - 1) / (it)| ≤ |ω| e^{-αt²}`. -/
lemma norm_gaussKernel_le (α ω t : ℝ) : ‖gaussKernel α ω t‖ ≤ |ω| * Real.exp (-α * t ^ 2) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [gaussKernel]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(ω * t))
  rw [gaussKernel, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, mul_comm]
  gcongr
  rw [div_le_iff₀ (norm_pos_iff.2 ht)]
  convert h using 3
  · push_cast; ring_nf
  · simp

/-- The kernel is integrable. -/
lemma integrable_gaussKernel {α : ℝ} (hα : 0 < α) (ω : ℝ) : Integrable (gaussKernel α ω) := by
  refine ((integrable_exp_neg_mul_sq hα).const_mul |ω|).mono' ?_
    (ae_of_all _ (norm_gaussKernel_le α ω))
  unfold gaussKernel
  fun_prop

/-- For `t ≠ 0`, `(e^{-iωt} - 1) / (it) = -∫₀^ω e^{-iσt} dσ`. -/
lemma gaussKernel_eq_neg_integral (α ω : ℝ) {t : ℝ} (ht : t ≠ 0) :
    gaussKernel α ω t = -∫ σ in (0 : ℝ)..ω,
      (Real.exp (-α * t ^ 2) : ℂ) * Complex.exp (-(σ * t) * Complex.I) := by
  have hc : -((t : ℂ) * Complex.I) ≠ 0 := by simp [ht]
  have h := integral_exp_mul_complex (a := 0) (b := ω) hc
  have e : ∀ σ : ℝ, -((σ : ℂ) * t) * Complex.I = -((t : ℂ) * Complex.I) * σ :=
    fun σ => by ring
  simp_rw [intervalIntegral.integral_const_mul, e]
  rw [h, gaussKernel]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

/-- The Fourier transform of the Gaussian: `∫ e^{-αt²} e^{-iσt} dt = √(π/α) e^{-σ²/(4α)}`. -/
lemma integral_gauss_mul_exp {α : ℝ} (hα : 0 < α) (σ : ℝ) :
    ∫ t : ℝ, (Real.exp (-α * t ^ 2) : ℂ) * Complex.exp (-(σ * t) * Complex.I) =
      ((Real.sqrt (Real.pi / α) * Real.exp (-σ ^ 2 / (4 * α)) : ℝ) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (α : ℂ)) (by simpa using hα) (-(σ : ℂ))
  have e : ∀ t : ℝ, (Real.exp (-α * t ^ 2) : ℂ) * Complex.exp (-(σ * t) * Complex.I) =
      Complex.exp (Complex.I * -(σ : ℂ) * t) * Complex.exp (-(α : ℂ) * t ^ 2) := by
    intro t
    rw [mul_comm, Complex.ofReal_exp]
    push_cast
    ring_nf
  simp_rw [e, h]
  rw [Complex.ofReal_mul, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity),
    Complex.ofReal_exp]
  push_cast
  ring_nf

/-- `∫ e^{-αt²} (e^{-iωt} - 1) / (it) dt = -√(π/α) ∫₀^ω e^{-σ²/(4α)} dσ`. -/
theorem integral_gaussKernel {α : ℝ} (hα : 0 < α) (ω : ℝ) :
    ∫ t, gaussKernel α ω t = -((Real.sqrt (Real.pi / α) * gaussStep α ω : ℝ) : ℂ) := by
  have hae : (fun t => gaussKernel α ω t) =ᵐ[volume] fun t => -∫ σ in (0 : ℝ)..ω,
      (Real.exp (-α * t ^ 2) : ℂ) * Complex.exp (-(σ * t) * Complex.I) := by
    filter_upwards [Measure.ae_ne volume 0] with t ht
    exact gaussKernel_eq_neg_integral α ω ht
  have hint : Integrable (Function.uncurry fun (σ t : ℝ) =>
      (Real.exp (-α * t ^ 2) : ℂ) * Complex.exp (-(σ * t) * Complex.I))
      ((volume.restrict (Set.uIoc 0 ω)).prod volume) := by
    have : IsFiniteMeasure (volume.restrict (Set.uIoc 0 ω)) :=
      isFiniteMeasure_restrict.2 (by simp [Set.uIoc])
    refine ((integrable_exp_neg_mul_sq hα).comp_snd _).mono' (by fun_prop)
      (ae_of_all _ fun p => ?_)
    rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), ← Complex.ofReal_mul, ← Complex.ofReal_neg,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [integral_congr_ae hae, integral_neg, ← intervalIntegral_integral_swap hint]
  simp_rw [integral_gauss_mul_exp hα, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul, gaussStep]

end LiebRobinson
