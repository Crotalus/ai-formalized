/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.Chart
/-!

# The apsidal angle in a Morse chart

Given a Morse chart `X` at `x₀` (so `U (X s) = U x₀ + s² / 2`), for `0 < ε < ρ² / 2`:

1. the allowed region `connectedComponentIn (Ω ∩ {U < U x₀ + ε}) x₀` is
   `X '' Ioo (-√(2ε)) (√(2ε))`;
2. the substitution `x = X (√(2ε) sin θ)` turns the singular apsidal integral into the regular
   integral `∫ θ in -(π/2)..π/2, X' (√(2ε) sin θ)`;
3. hence the apsidal angle extends continuously to `ε = 0`, with value `π X' 0`.
-/

open Set Filter Topology Real

namespace Bertrand

namespace MorseChart

variable {U : ℝ → ℝ} {Ω : Set ℝ} {x₀ : ℝ}

/-- The inverse chart is continuous on `(-ρ, ρ)`. -/
lemma continuousOn_X (c : MorseChart U Ω x₀) : ContinuousOn c.X (Ioo (-c.ρ) c.ρ) :=
  fun s hs ↦ (c.hasDerivAt s hs).continuousAt.continuousWithinAt

/-- The inverse chart is strictly increasing on `(-ρ, ρ)`. -/
lemma strictMonoOn_X (c : MorseChart U Ω x₀) : StrictMonoOn c.X (Ioo (-c.ρ) c.ρ) :=
  strictMonoOn_of_deriv_pos (convex_Ioo _ _) c.continuousOn_X fun s hs ↦
    c.deriv_pos s (interior_subset hs)

/-- For `0 ≤ σ < ρ`, the point `σ sin θ` lies in the chart domain. -/
lemma mul_sin_mem (c : MorseChart U Ω x₀) {σ : ℝ} (hσ : 0 ≤ σ) (hσρ : σ < c.ρ) (θ : ℝ) :
    σ * sin θ ∈ Ioo (-c.ρ) c.ρ := by
  have h1 := neg_one_le_sin θ
  have h2 := sin_le_one θ
  constructor <;> nlinarith

/-- For `0 < σ < ρ`, the allowed region at energy `U x₀ + σ² / 2` is the image of
`(-π/2, π/2)` under `θ ↦ X (σ sin θ)`. -/
lemma connectedComponentIn_eq (c : MorseChart U Ω x₀) {σ : ℝ} (hσ : 0 < σ) (hσρ : σ < c.ρ) :
    connectedComponentIn (Ω ∩ {x | U x < U x₀ + σ ^ 2 / 2}) x₀ =
      (fun θ ↦ c.X (σ * sin θ)) '' Ioo (-(π / 2)) (π / 2) := by
  have h0 : (0 : ℝ) ∈ Ioo (-c.ρ) c.ρ := ⟨by linarith [c.ρ_pos], c.ρ_pos⟩
  have hσmem : σ ∈ Ioo (-c.ρ) c.ρ := ⟨by linarith, hσρ⟩
  have hnσmem : -σ ∈ Ioo (-c.ρ) c.ρ := ⟨by linarith, by linarith⟩
  -- at the turning points `X (±σ)` the energy is exactly `U x₀ + σ² / 2`
  have hturn : ∀ s ∈ Ioo (-c.ρ) c.ρ, s ^ 2 = σ ^ 2 →
      c.X s ∉ connectedComponentIn (Ω ∩ {x | U x < U x₀ + σ ^ 2 / 2}) x₀ := fun s hs hs2 h ↦ by
    have := (connectedComponentIn_subset _ _ h).2
    simp only [mem_ofPred_eq, c.U_comp s hs, hs2, lt_self_iff_false] at this
  apply Subset.antisymm
  · intro y hy
    have hC := isPreconnected_connectedComponentIn (F := Ω ∩ {x | U x < U x₀ + σ ^ 2 / 2})
      (x := x₀)
    have hx₀ : x₀ ∈ connectedComponentIn (Ω ∩ {x | U x < U x₀ + σ ^ 2 / 2}) x₀ :=
      mem_connectedComponentIn ⟨c.X_zero ▸ c.mapsTo h0, show U x₀ < U x₀ + σ ^ 2 / 2 by linarith [pow_pos hσ 2]⟩
    -- the component is an interval around `x₀` avoiding `X (±σ)`
    have hlt : y < c.X σ := by
      by_contra! h
      have : c.X 0 < c.X σ := c.strictMonoOn_X h0 hσmem hσ
      exact hturn σ hσmem rfl (hC.Icc_subset hx₀ hy ⟨c.X_zero.symm.trans_le this.le, h⟩)
    have hgt : c.X (-σ) < y := by
      by_contra! h
      have : c.X (-σ) < c.X 0 := c.strictMonoOn_X hnσmem h0 (by linarith)
      exact hturn (-σ) hnσmem (by ring)
        (hC.Icc_subset hy hx₀ ⟨h, this.le.trans_eq c.X_zero⟩)
    obtain ⟨s, hs, rfl⟩ := intermediate_value_Ioo (by linarith : -σ ≤ σ)
      (c.continuousOn_X.mono (Icc_subset_Ioo hnσmem.1 hσρ)) ⟨hgt, hlt⟩
    have h1 : -1 < s / σ := by rw [lt_div_iff₀ hσ]; linarith [hs.1]
    have h2 : s / σ < 1 := (div_lt_one hσ).2 hs.2
    refine ⟨arcsin (s / σ), ⟨neg_pi_div_two_lt_arcsin.2 h1, arcsin_lt_pi_div_two.2 h2⟩, ?_⟩
    simp only [sin_arcsin h1.le h2.le, mul_div_cancel₀ s hσ.ne']
  · refine (isPreconnected_Ioo.image _ ?_).subset_connectedComponentIn
      ⟨0, ⟨by linarith [pi_pos], by linarith [pi_pos]⟩, by simp [c.X_zero]⟩ ?_
    · exact (c.continuousOn_X.comp_continuous (by fun_prop)
        (c.mul_sin_mem hσ.le hσρ)).continuousOn
    · rintro _ ⟨θ, hθ, rfl⟩
      have hcos := cos_pos_of_mem_Ioo hθ
      refine ⟨c.mapsTo (c.mul_sin_mem hσ.le hσρ θ), ?_⟩
      simp only [mem_ofPred_eq, c.U_comp _ (c.mul_sin_mem hσ.le hσρ θ)]
      nlinarith [sin_sq_add_cos_sq θ, mul_pos hσ hσ, mul_pos hcos hcos]

/-- The substitution `x = X (σ sin θ)` regularizes the apsidal integral at energy
`U x₀ + σ² / 2`. -/
lemma apsidalAngle_eq_aux (c : MorseChart U Ω x₀) {σ : ℝ} (hσ : 0 < σ) (hσρ : σ < c.ρ) :
    apsidalAngle U Ω x₀ (U x₀ + σ ^ 2 / 2) =
      ∫ θ in -(π / 2)..π / 2, deriv c.X (σ * sin θ) := by
  have hmem := c.mul_sin_mem hσ.le hσρ
  have hderiv : ∀ θ ∈ Ioo (-(π / 2)) (π / 2), HasDerivWithinAt (fun θ ↦ c.X (σ * sin θ))
      (deriv c.X (σ * sin θ) * (σ * cos θ)) (Ioo (-(π / 2)) (π / 2)) θ := fun θ _ ↦
    ((c.hasDerivAt _ (hmem θ)).comp θ ((hasDerivAt_sin θ).const_mul σ)).hasDerivWithinAt
  have hinj : InjOn (fun θ ↦ c.X (σ * sin θ)) (Ioo (-(π / 2)) (π / 2)) := fun a ha b hb h ↦
    injOn_sin (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb)
      (mul_left_cancel₀ hσ.ne' (c.strictMonoOn_X.injOn (hmem a) (hmem b) h))
  rw [apsidalAngle, c.connectedComponentIn_eq hσ hσρ,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
    intervalIntegral.integral_of_le (by linarith [pi_pos]),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
  have hcos := cos_pos_of_mem_Ioo hθ
  have hd := c.deriv_pos _ (hmem θ)
  -- on the open interval, `2 (E - U) = (σ cos θ)²`
  have hsq : 2 * (U x₀ + σ ^ 2 / 2 - U (c.X (σ * sin θ))) = (σ * cos θ) ^ 2 := by
    rw [c.U_comp _ (hmem θ)]; linear_combination -σ ^ 2 * sin_sq_add_cos_sq θ
  simp only [hsq, sqrt_sq (mul_pos hσ hcos).le, abs_of_pos (mul_pos hd (mul_pos hσ hcos)),
    smul_eq_mul]
  field_simp

/-- In a Morse chart the apsidal angle at energy `U x₀ + ε` is the regular integral
`∫ θ in -(π/2)..π/2, X' (√(2ε) sin θ)`. -/
theorem apsidalAngle_eq (c : MorseChart U Ω x₀) {ε : ℝ} (hε : 0 < ε) (hερ : ε < c.ρ ^ 2 / 2) :
    apsidalAngle U Ω x₀ (U x₀ + ε) =
      ∫ θ in -(π / 2)..π / 2, deriv c.X (√(2 * ε) * sin θ) := by
  have h := c.apsidalAngle_eq_aux (sqrt_pos.2 (by linarith : 0 < 2 * ε))
    ((sqrt_lt' c.ρ_pos).2 (by linarith))
  rwa [sq_sqrt (by linarith), mul_div_cancel_left₀ _ two_ne_zero] at h

/-- The apsidal angle, as a function of the energy above the bottom of the well, extends
continuously to `0`, where it takes the value `π X' 0`. -/
theorem exists_continuousOn_apsidalAngle (c : MorseChart U Ω x₀) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Ico 0 (c.ρ ^ 2 / 2)) ∧ F 0 = π * deriv c.X 0 ∧
      ∀ ε ∈ Ioo 0 (c.ρ ^ 2 / 2), apsidalAngle U Ω x₀ (U x₀ + ε) = F ε := by
  refine ⟨fun ε ↦ ∫ θ in -(π / 2)..π / 2, deriv c.X (√(2 * ε) * sin θ), ?_, ?_,
    fun ε hε ↦ c.apsidalAngle_eq hε.1 hε.2⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    -- the integrand is jointly continuous on `Ico 0 (ρ² / 2) × ℝ`, since `|√(2ε) sin θ| < ρ`
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (e : Ico 0 (c.ρ ^ 2 / 2)) θ ↦ deriv c.X (√(2 * (e : ℝ)) * sin θ))
      (μ := MeasureTheory.volume) ?_ _ _
    exact c.continuousOn_deriv.comp_continuous (by fun_prop) fun p ↦
      c.mul_sin_mem (sqrt_nonneg _) ((sqrt_lt' c.ρ_pos).2 (by linarith [p.1.2.2])) p.2
  · simp

end MorseChart

end Bertrand
