/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import LiebRobinson.Clustering.Gaussian
/-!

# Extracting the positive-frequency part of a function of time

A finite sum of positive-frequency terms is small if the full function, which also has
negative-frequency terms, is small near `t = 0` and bounded.

## i. Overview

Let `F(t) = ∑ cᵢ (e^{-iωᵢt} - 1) - ∑ dᵢ (e^{iωᵢt} - 1)` with all `ωᵢ ≥ γ > 0` and
`∑ cᵢ = ∑ dᵢ`. Integrating `F` against the kernel `e^{-αt²} / (it)` gives, by the Gaussian
integral, `Q = -2π ∑ cᵢ + ∑ (cᵢ + dᵢ) εᵢ` with `0 ≤ εᵢ ≤ ε = (2 √(πα) / γ) e^{-γ²/(4α)}`. On the
other hand `|Q| ≤ ∫ e^{-αt²} |F(t)| / |t| dt`, which is small if `|F(t)| ≤ K₂ |t|^m` for
`|t| ≤ T` and `|F| ≤ K₁` everywhere. Hence `∑ cᵢ` is small.

## ii. Key results

- `LiebRobinson.norm_sum_le_of_filter` : the bound on `∑ cᵢ`.

## iii. Table of contents

- A. The filter estimate

## iv. References

* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
* M. B. Hastings and T. Koma, *Spectral gap and exponential decay of correlations*,
  Comm. Math. Phys. 265 (2006), 781–804.
-/

@[expose] public section

namespace LiebRobinson

open MeasureTheory Set Filter Topology

/-!

## A. The filter estimate

-/

/-- The Gaussian tail moment: for `T ≥ 0`, `t e^{-αt²}` is integrable on `(T, ∞)` with integral
`e^{-αT²} / (2α)`. -/
lemma integral_Ioi_mul_exp_neg_mul_sq {α T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) :
    IntegrableOn (fun t => t * Real.exp (-α * t ^ 2)) (Ioi T) ∧
      ∫ t in Ioi T, t * Real.exp (-α * t ^ 2) = Real.exp (-α * T ^ 2) / (2 * α) := by
  have hderiv : ∀ x ∈ Ici T, HasDerivAt (fun t => -(Real.exp (-α * t ^ 2) / (2 * α)))
      (x * Real.exp (-α * x ^ 2)) x := by
    intro x _
    convert (((hasDerivAt_pow 2 x).const_mul (-α)).exp.div_const (2 * α)).neg using 1
    field_simp
    ring
  have hpos : ∀ x ∈ Ioi T, 0 ≤ x * Real.exp (-α * x ^ 2) :=
    fun x hx => mul_nonneg (hT.trans hx.out.le) (Real.exp_pos _).le
  have hlim : Tendsto (fun t => -(Real.exp (-α * t ^ 2) / (2 * α))) atTop (𝓝 0) := by
    have := ((Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (neg_lt_zero.2 hα))).div_const (2 * α)).neg
    simpa using this
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  ring

/-- The half-line estimate behind the filter: if `f(t) ≤ K₁ e^{-αt²} / t` and
`f(t) ≤ K₂ t^(m-1)` for `t > 0`, then `∫_0^∞ f ≤ K₂ T^m / m + K₁ e^{-αT²} / (2αT²)`. -/
lemma setIntegral_Ioi_le_of_filter {f : ℝ → ℝ} (hfi : IntegrableOn f (Ioi 0)) {K₁ K₂ α T : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (hK₁ : 0 ≤ K₁) (hα : 0 < α) (hT : 0 < T)
    (h₁ : ∀ t, 0 < t → f t ≤ K₁ * Real.exp (-α * t ^ 2) / t)
    (h₂ : ∀ t, 0 < t → f t ≤ K₂ * t ^ (m - 1)) :
    ∫ t in Ioi 0, f t ≤ K₂ * T ^ m / m + K₁ * Real.exp (-α * T ^ 2) / (2 * α * T ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hgi, hg⟩ := integral_Ioi_mul_exp_neg_mul_sq hα hT.le
  rw [← Ioc_union_Ioi_eq_Ioi hT.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hfi.mono_set Ioc_subset_Ioi_self) (hfi.mono_set (Ioi_subset_Ioi hT.le))]
  gcongr
  · calc ∫ t in Ioc 0 T, f t ≤ ∫ t in Ioc 0 T, K₂ * t ^ n :=
          setIntegral_mono_on (hfi.mono_set Ioc_subset_Ioi_self)
            (continuous_const.mul (continuous_pow n)).integrableOn_Ioc measurableSet_Ioc
            fun t ht => by simpa using h₂ t ht.1
      _ = K₂ * T ^ (n + 1) / ↑(n + 1) := by
          rw [← intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_const_mul,
            integral_pow]
          push_cast
          ring
  · calc ∫ t in Ioi T, f t ≤ ∫ t in Ioi T, K₁ / T ^ 2 * (t * Real.exp (-α * t ^ 2)) := by
          refine setIntegral_mono_on (hfi.mono_set (Ioi_subset_Ioi hT.le)) (hgi.const_mul _)
            measurableSet_Ioi fun t ht => (h₁ t (hT.trans ht)).trans ?_
          have ht0 : 0 < t := hT.trans ht
          have hTt : T ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hT.le (le_of_lt ht) 2
          rw [div_le_iff₀ ht0]
          calc K₁ * Real.exp (-α * t ^ 2) ≤ K₁ * Real.exp (-α * t ^ 2) * (t ^ 2 / T ^ 2) :=
                le_mul_of_one_le_right (mul_nonneg hK₁ (Real.exp_pos _).le)
                  ((one_le_div (by positivity)).2 hTt)
            _ = K₁ / T ^ 2 * (t * Real.exp (-α * t ^ 2)) * t := by ring
      _ = K₁ * Real.exp (-α * T ^ 2) / (2 * α * T ^ 2) := by
          rw [integral_const_mul, hg]
          field_simp

/-- **The spectral filter.** Let `F(t) = ∑ cᵢ (e^{-iωᵢt} - 1) - ∑ dᵢ (e^{iωᵢt} - 1)` with all
frequencies `ωᵢ ≥ γ > 0`, `∑ cᵢ = ∑ dᵢ` and `∑ |cᵢ|, ∑ |dᵢ| ≤ M`. If `|F| ≤ K₁` everywhere and
`|F(t)| ≤ K₂ |t|^m` with `m ≥ 1`, then for all `α, T > 0`
`|∑ cᵢ| ≤ (2 K₂ T^m / m + K₁ e^{-αT²} / (αT²) + 2 M (2 √(πα) / γ) e^{-γ²/(4α)}) / (2π)`. -/
theorem norm_sum_le_of_filter {ι : Type*} [Fintype ι] {γ : ℝ} (hγ : 0 < γ) (ω : ι → ℝ)
    (hω : ∀ i, γ ≤ ω i) (c d : ι → ℂ) (hcd : ∑ i, c i = ∑ i, d i) {M : ℝ}
    (hc : ∑ i, ‖c i‖ ≤ M) (hd : ∑ i, ‖d i‖ ≤ M) (F : ℝ → ℂ)
    (hF : ∀ t, F t = ∑ i, c i * (Complex.exp (-(ω i * t) * Complex.I) - 1) -
      ∑ i, d i * (Complex.exp ((ω i * t) * Complex.I) - 1))
    {K₁ K₂ : ℝ} {m : ℕ} (hm : 1 ≤ m) (hK₁ : ∀ t, ‖F t‖ ≤ K₁) (hK₂ : ∀ t, ‖F t‖ ≤ K₂ * |t| ^ m)
    {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    ‖∑ i, c i‖ ≤ (2 * K₂ * T ^ m / m + K₁ * Real.exp (-α * T ^ 2) / (α * T ^ 2) +
      2 * M * (2 * Real.sqrt (Real.pi * α) / γ * Real.exp (-γ ^ 2 / (4 * α)))) /
        (2 * Real.pi) := by
  set ε := 2 * Real.sqrt (Real.pi * α) / γ * Real.exp (-γ ^ 2 / (4 * α))
  set G : ℝ → ℂ := fun t => (Real.exp (-α * t ^ 2) : ℂ) * (F t / (t * Complex.I))
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ 0)
  have hε0 : 0 ≤ ε := by positivity
  -- The integrand is a finite combination of Gaussian kernels.
  have hG : G = fun t => ∑ i, c i * gaussKernel α (ω i) t - ∑ i, d i * gaussKernel α (-ω i) t := by
    funext t
    simp only [G, gaussKernel, hF t]
    push_cast
    simp only [neg_mul, neg_neg, sub_div, Finset.sum_div, mul_sub, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring
  have hGi : Integrable G := by
    rw [hG]
    exact (integrable_finsetSum _ fun i _ => (integrable_gaussKernel hα _).const_mul _).sub
      (integrable_finsetSum _ fun i _ => (integrable_gaussKernel hα _).const_mul _)
  -- The Gaussian integral: `∫ G = -2π ∑ cᵢ + ∑ (cᵢ + dᵢ) εᵢ`.
  set e : ι → ℝ := fun i => Real.pi - Real.sqrt (Real.pi / α) * gaussStep α (ω i)
  have hQ : (2 * Real.pi : ℂ) * ∑ i, c i = ∑ i, (c i + d i) * (e i : ℂ) - ∫ t, G t := by
    have hs : ∀ i, ((Real.sqrt (Real.pi / α) * gaussStep α (ω i) : ℝ) : ℂ) = Real.pi - e i := by
      intro i
      simp only [e]
      push_cast
      ring
    rw [hG, integral_sub (integrable_finsetSum _ fun i _ =>
        (integrable_gaussKernel hα _).const_mul _)
      (integrable_finsetSum _ fun i _ => (integrable_gaussKernel hα _).const_mul _),
      integral_finsetSum _ fun i _ => (integrable_gaussKernel hα _).const_mul _,
      integral_finsetSum _ fun i _ => (integrable_gaussKernel hα _).const_mul _]
    simp only [integral_const_mul, integral_gaussKernel hα, gaussStep_neg, mul_neg,
      Complex.ofReal_neg, neg_neg, hs]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      show (2 * Real.pi : ℂ) * ∑ i, c i = ∑ i, (Real.pi * c i + Real.pi * d i) by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hcd]
        ring]
    exact Finset.sum_congr rfl fun i _ => by ring
  have herr : ‖∑ i, (c i + d i) * (e i : ℂ)‖ ≤ 2 * M * ε := by
    calc ‖∑ i, (c i + d i) * (e i : ℂ)‖ ≤ ∑ i, (‖c i‖ + ‖d i‖) * ε := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          obtain ⟨h0, h1⟩ := gaussStep_tail hα hγ (hω i)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
          exact mul_le_mul (norm_add_le _ _) h1 h0 (by positivity)
      _ ≤ 2 * M * ε := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib]
          nlinarith
  -- The time-domain bound on `∫ G`.
  have hnorm : ∀ s, ‖G s‖ = Real.exp (-α * s ^ 2) * ‖F s‖ / |s| := by
    intro s
    simp only [G]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
  have hhalf : ∀ f : ℝ → ℝ, IntegrableOn f (Ioi 0) →
      (∀ t, 0 < t → f t = Real.exp (-α * t ^ 2) * ‖F t‖ / t ∨
        f t = Real.exp (-α * t ^ 2) * ‖F (-t)‖ / t) →
      ∫ t in Ioi 0, f t ≤ K₂ * T ^ m / m + K₁ * Real.exp (-α * T ^ 2) / (2 * α * T ^ 2) := by
    intro f hfi hf
    refine setIntegral_Ioi_le_of_filter hfi hm hK₁0 hα hT (fun t ht => ?_) (fun t ht => ?_)
    · have key : ∀ u : ℝ, Real.exp (-α * t ^ 2) * ‖F u‖ / t ≤ K₁ * Real.exp (-α * t ^ 2) / t :=
        fun u => div_le_div_of_nonneg_right (by rw [mul_comm]; gcongr; exact hK₁ u) ht.le
      rcases hf t ht with h | h <;> rw [h] <;> exact key _
    · have key : ∀ u : ℝ, |u| = t →
          Real.exp (-α * t ^ 2) * ‖F u‖ / t ≤ K₂ * t ^ (m - 1) := by
        intro u hu
        rw [div_le_iff₀ ht]
        calc Real.exp (-α * t ^ 2) * ‖F u‖ ≤ 1 * ‖F u‖ := by
              gcongr
              exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
          _ ≤ K₂ * |u| ^ m := by rw [one_mul]; exact hK₂ u
          _ = K₂ * t ^ (m - 1) * t := by
              rw [hu, mul_assoc, ← pow_succ, Nat.sub_add_cancel hm]
      rcases hf t ht with h | h <;> rw [h]
      · exact key t (abs_of_pos ht)
      · exact key (-t) (by rw [abs_neg, abs_of_pos ht])
  have hQb : ‖∫ t, G t‖ ≤ 2 * K₂ * T ^ m / m + K₁ * Real.exp (-α * T ^ 2) / (α * T ^ 2) := by
    have hGn := hGi.norm
    calc ‖∫ t, G t‖ ≤ ∫ t, ‖G t‖ := norm_integral_le_integral_norm _
      _ = (∫ t in Ioi 0, ‖G (-t)‖) + ∫ t in Ioi 0, ‖G t‖ := by
          rw [integral_comp_neg_Ioi 0 (fun x => ‖G x‖), neg_zero,
            intervalIntegral.integral_Iic_add_Ioi hGn.integrableOn hGn.integrableOn]
      _ ≤ (K₂ * T ^ m / m + K₁ * Real.exp (-α * T ^ 2) / (2 * α * T ^ 2)) +
          (K₂ * T ^ m / m + K₁ * Real.exp (-α * T ^ 2) / (2 * α * T ^ 2)) := by
          refine add_le_add ?_ ?_
          · refine hhalf _ (hGn.comp_neg).integrableOn fun t ht => Or.inr ?_
            rw [hnorm, neg_sq, abs_neg, abs_of_pos ht]
          · refine hhalf _ hGn.integrableOn fun t ht => Or.inl ?_
            rw [hnorm, abs_of_pos ht]
      _ = 2 * K₂ * T ^ m / m + K₁ * Real.exp (-α * T ^ 2) / (α * T ^ 2) := by
          field_simp
          ring
  -- Combine.
  have h2 : ‖∑ i, c i‖ * (2 * Real.pi) ≤ ‖∑ i, (c i + d i) * (e i : ℂ)‖ + ‖∫ t, G t‖ := by
    calc ‖∑ i, c i‖ * (2 * Real.pi) = ‖(2 * Real.pi : ℂ) * ∑ i, c i‖ := by
          rw [norm_mul, mul_comm]
          norm_cast
          rw [Real.norm_of_nonneg (by positivity)]
      _ ≤ _ := by rw [hQ]; exact norm_sub_le _ _
  rw [le_div_iff₀ (by positivity)]
  linarith

end LiebRobinson
