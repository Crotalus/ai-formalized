/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.Chart
/-!

# Existence of a Morse chart at a nondegenerate minimum

One-dimensional Morse lemma: if `U` is `C³` near `x₀` with `U' x₀ = 0` and `U'' x₀ > 0`, there is
a `C¹` coordinate `s` near `x₀` with `U = U x₀ + s² / 2` and `s' x₀ = √(U'' x₀)`.

Proof sketch (only `C²` is used): let `q x = (U x - U x₀) / (x - x₀)²`; by L'Hôpital's rule
`q x → U'' x₀ / 2 > 0`. Put `s x = (x - x₀) √(2 q x)`, so `s² = 2 (U - U x₀)` near `x₀`. Then
`s' x₀ = √(U'' x₀)`, and for `x ≠ x₀`, differentiating `s²` gives `s' = U' / s
= (U' x / (x - x₀)) / √(2 q x) → U'' x₀ / √(U'' x₀)`, so `s` is `C¹` near `x₀` with `s' > 0`.
Hence `s` is a local diffeomorphism and its local inverse `X` is the required chart, with
`X' 0 = 1 / √(U'' x₀)`.
-/

open Set Filter Topology Real

namespace Bertrand

/-- The second difference quotient `(U x - U x₀) / (x - x₀)²` (equal to `0` at `x = x₀`). -/
noncomputable def secondQuot (U : ℝ → ℝ) (x₀ x : ℝ) : ℝ := (U x - U x₀) / (x - x₀) ^ 2

/-- The Morse coordinate `s x = (x - x₀) √(2 (U x - U x₀) / (x - x₀)²)`. -/
noncomputable def morseCoord (U : ℝ → ℝ) (x₀ x : ℝ) : ℝ := (x - x₀) * √(2 * secondQuot U x₀ x)

variable {U : ℝ → ℝ} {Ω : Set ℝ} {x₀ a : ℝ}

/-- `U' x / (x - x₀) → U'' x₀` when `U' x₀ = 0`. -/
lemma tendsto_deriv_div (h1 : deriv U x₀ = 0) (h2 : HasDerivAt (deriv U) a x₀) :
    Tendsto (fun x ↦ deriv U x / (x - x₀)) (𝓝[≠] x₀) (𝓝 a) := by
  have := hasDerivAt_iff_tendsto_slope.1 h2
  simp only [funext (slope_def_field (deriv U) x₀), h1, sub_zero] at this
  exact this

/-- `(U x - U x₀) / (x - x₀)² → U'' x₀ / 2`, by L'Hôpital's rule. -/
lemma tendsto_secondQuot (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω)
    (hd : ∀ x ∈ Ω, HasDerivAt U (deriv U x) x) (h1 : deriv U x₀ = 0)
    (h2 : HasDerivAt (deriv U) a x₀) :
    Tendsto (secondQuot U x₀) (𝓝[≠] x₀) (𝓝 (a / 2)) := by
  have hcU : Tendsto (fun x ↦ U x - U x₀) (𝓝 x₀) (𝓝 0) := by
    simpa using (hd x₀ hx₀).continuousAt.tendsto.sub_const (U x₀)
  have hcg : Tendsto (fun x ↦ (x - x₀) ^ 2) (𝓝 x₀) (𝓝 0) := by
    exact (by fun_prop : Continuous fun x : ℝ ↦ (x - x₀) ^ 2).tendsto' x₀ 0 (by simp)
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := deriv U) (g' := fun x ↦ 2 * (x - x₀)) ?_ ?_ ?_
    (tendsto_nhdsWithin_of_tendsto_nhds hcU) (tendsto_nhdsWithin_of_tendsto_nhds hcg) ?_
  · refine eventually_nhdsWithin_of_eventually_nhds ?_
    filter_upwards [hΩ.mem_nhds hx₀] with x hx
    exact (hd x hx).sub_const _
  · refine Eventually.of_forall fun x ↦ ?_
    simpa using ((hasDerivAt_id x).sub_const x₀).fun_pow 2
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero two_ne_zero (sub_ne_zero.2 hx)
  · convert (tendsto_deriv_div h1 h2).div_const 2 using 2 with x
    rw [div_div, mul_comm]

/-- The Morse coordinate has derivative `√(U'' x₀)` at `x₀`. -/
lemma hasDerivAt_morseCoord (hlim : Tendsto (secondQuot U x₀) (𝓝[≠] x₀) (𝓝 (a / 2))) :
    HasDerivAt (morseCoord U x₀) (√a) x₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have : Tendsto (fun x ↦ √(2 * secondQuot U x₀ x)) (𝓝[≠] x₀) (𝓝 (√a)) := by
    simpa [mul_div_cancel₀] using (hlim.const_mul 2).sqrt
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_def_field, morseCoord, morseCoord, sub_self, zero_mul, sub_zero,
    mul_div_cancel_left₀ _ (sub_ne_zero.2 hx)]

/-- Where the difference quotient is nonnegative (off `x₀`), `s² = 2 (U - U x₀)`. -/
lemma morseCoord_sq {x : ℝ} (hq : x ≠ x₀ → 0 < secondQuot U x₀ x) :
    morseCoord U x₀ x ^ 2 = 2 * (U x - U x₀) := by
  rcases eq_or_ne x x₀ with rfl | hx
  · simp [morseCoord]
  · have := hq hx
    rw [morseCoord, mul_pow, sq_sqrt (by positivity), secondQuot]
    field_simp [sub_ne_zero.2 hx]

/-- Off `x₀`, the derivative of the Morse coordinate is `U' / s`, from `s² = 2 (U - U x₀)`. -/
lemma hasDerivAt_morseCoord_of_ne {x : ℝ} (hx : x ≠ x₀) (hU : HasDerivAt U (deriv U x) x)
    (hq : ∀ᶠ y in 𝓝 x, y ≠ x₀ → 0 < secondQuot U x₀ y) :
    morseCoord U x₀ x ≠ 0 ∧ HasDerivAt (morseCoord U x₀) (deriv U x / morseCoord U x₀ x) x := by
  have hx' : x - x₀ ≠ 0 := sub_ne_zero.2 hx
  have hqx := hq.self_of_nhds hx
  have hs0 : morseCoord U x₀ x ≠ 0 := mul_ne_zero hx' (sqrt_pos.2 (mul_pos two_pos hqx)).ne'
  have hdiff : DifferentiableAt ℝ (morseCoord U x₀) x :=
    (differentiableAt_id.sub_const x₀).mul ((((hU.differentiableAt.sub_const (U x₀)).div
      ((differentiableAt_id.sub_const x₀).pow 2) (pow_ne_zero 2 hx')).const_mul 2).sqrt
      (mul_ne_zero two_ne_zero hqx.ne'))
  -- Differentiate `s² = 2 (U - U x₀)` and compare.
  have h₁ := hdiff.hasDerivAt.fun_pow 2
  have h₂ : HasDerivAt (fun y ↦ morseCoord U x₀ y ^ 2) (2 * deriv U x) x :=
    ((hU.sub_const (U x₀)).const_mul 2).congr_of_eventuallyEq
      (hq.mono fun y hy ↦ morseCoord_sq hy)
  have := h₁.unique h₂
  refine ⟨hs0, ?_⟩
  convert hdiff.hasDerivAt using 1
  field_simp
  norm_num at this
  linarith

/-- Near `x₀`, the Morse coordinate is `C¹` with positive derivative and `s² = 2 (U - U x₀)`. -/
lemma eventually_morseCoord (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω)
    (hd : ∀ x ∈ Ω, HasDerivAt U (deriv U x) x) (hc : ContinuousOn (deriv U) Ω)
    (h1 : deriv U x₀ = 0) (h2 : HasDerivAt (deriv U) a x₀) (ha : 0 < a) :
    ∀ᶠ x in 𝓝 x₀, x ∈ Ω ∧ HasDerivAt (morseCoord U x₀) (deriv (morseCoord U x₀) x) x ∧
      ContinuousAt (deriv (morseCoord U x₀)) x ∧ 0 < deriv (morseCoord U x₀) x ∧
      morseCoord U x₀ x ^ 2 = 2 * (U x - U x₀) := by
  set s := morseCoord U x₀
  have hlim := tendsto_secondQuot hΩ hx₀ hd h1 h2
  have hs := hasDerivAt_morseCoord hlim
  have hP : ∀ᶠ x in 𝓝 x₀, x ∈ Ω ∧ (x ≠ x₀ → 0 < secondQuot U x₀ x) :=
    Filter.Eventually.and (hΩ.mem_nhds hx₀)
      (eventually_nhdsWithin_iff.1 (hlim.eventually (eventually_gt_nhds (half_pos ha))))
  -- At every point near `x₀` other than `x₀`, `s' = U' / s`, which is continuous there.
  have hne : ∀ᶠ x in 𝓝 x₀, x ≠ x₀ → HasDerivAt s (deriv s x) x ∧ ContinuousAt (deriv s) x ∧
      deriv s x = deriv U x / s x := by
    filter_upwards [hP.eventually_nhds] with x hx hxne
    have hxΩ := hx.self_of_nhds.1
    have key := hasDerivAt_morseCoord_of_ne hxne (hd x hxΩ) (hx.mono fun _ h ↦ h.2)
    have heq : deriv s =ᶠ[𝓝 x] fun y ↦ deriv U y / s y := by
      filter_upwards [hx.eventually_nhds, isOpen_ne.mem_nhds hxne] with y hy hyne
      exact (hasDerivAt_morseCoord_of_ne hyne (hd y hy.self_of_nhds.1)
        (hy.mono fun _ h ↦ h.2)).2.deriv
    refine ⟨key.2.differentiableAt.hasDerivAt, ?_, heq.self_of_nhds⟩
    exact ((hc.continuousAt (hΩ.mem_nhds hxΩ)).div key.2.continuousAt key.1).congr heq.symm
  -- At `x₀`, `s' = (U' / (x - x₀)) / √(2 q) → a / √a = √a = s' x₀`.
  have hcont : ContinuousAt (deriv s) x₀ := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hs.deriv, ← div_sqrt]
    have hsq : Tendsto (fun x ↦ √(2 * secondQuot U x₀ x)) (𝓝[≠] x₀) (𝓝 (√a)) := by
      simpa [mul_div_cancel₀] using (hlim.const_mul 2).sqrt
    refine ((tendsto_deriv_div h1 h2).div hsq (sqrt_pos.2 ha).ne').congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hne, self_mem_nhdsWithin]
      with x hx hxne
    rw [(hx hxne).2.2, show s x = (x - x₀) * √(2 * secondQuot U x₀ x) from rfl, div_mul_eq_div_div]
    rfl
  have hpos : ∀ᶠ x in 𝓝 x₀, 0 < deriv s x :=
    hcont.eventually (eventually_gt_nhds (by rw [hs.deriv]; exact sqrt_pos.2 ha))
  filter_upwards [hP, hne, hpos] with x hx hxne hxpos
  refine ⟨hx.1, ?_, ?_, hxpos, morseCoord_sq hx.2⟩
  · rcases eq_or_ne x x₀ with rfl | h
    · exact hs.differentiableAt.hasDerivAt
    · exact (hxne h).1
  · rcases eq_or_ne x x₀ with rfl | h
    · exact hcont
    · exact (hxne h).2.1

/-- Inverting a coordinate `s` with `s x₀ = 0`, `s' x₀ = d > 0`, which near `x₀` is `C¹` with
positive derivative and satisfies `s² = 2 (U - U x₀)`, gives a Morse chart with `X' 0 = 1 / d`. -/
lemma exists_morseChart_of_coord {s : ℝ → ℝ} {d : ℝ} (hs0 : s x₀ = 0)
    (hs : HasStrictDerivAt s d x₀) (hd : 0 < d)
    (hG : ∀ᶠ x in 𝓝 x₀, x ∈ Ω ∧ HasDerivAt s (deriv s x) x ∧ ContinuousAt (deriv s) x ∧
      0 < deriv s x ∧ s x ^ 2 = 2 * (U x - U x₀)) :
    ∃ c : MorseChart U Ω x₀, deriv c.X 0 = 1 / d := by
  set e := (hs.hasStrictFDerivAt_equiv hd.ne').toOpenPartialHomeomorph s
  have hsrc : x₀ ∈ e.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hex : e x₀ = 0 := hs0
  have he0 : e.symm 0 = x₀ := by simpa [hex] using e.left_inv hsrc
  have h0t : (0 : ℝ) ∈ e.target := hex ▸ e.map_source hsrc
  have hsymm := (e.continuousAt_symm h0t).tendsto
  rw [he0] at hsymm
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
    (Filter.Eventually.and (e.open_target.mem_nhds h0t) (hsymm.eventually hG))
  have hmem : ∀ σ ∈ Ioo (-ρ) ρ, σ ∈ e.target ∧ _ := fun σ hσ ↦
    hball (by rw [Real.dist_0_eq_abs, abs_lt]; exact hσ)
  -- `X = e.symm` has derivative `1 / s' (X σ)` on `(-ρ, ρ)`.
  have hX : ∀ σ ∈ Ioo (-ρ) ρ, HasDerivAt e.symm (deriv s (e.symm σ))⁻¹ σ := fun σ hσ ↦
    e.hasDerivAt_symm (hmem σ hσ).1 (hmem σ hσ).2.2.2.2.1.ne' (hmem σ hσ).2.2.1
  refine ⟨⟨e.symm, ρ, hρ, he0, fun σ hσ ↦ (hmem σ hσ).2.1, fun σ hσ ↦ ?_, fun σ hσ ↦ ?_,
    fun σ hσ ↦ ?_, fun σ hσ ↦ ?_⟩, ?_⟩
  · rw [(hX σ hσ).deriv]; exact hX σ hσ
  · rw [(hX σ hσ).deriv]; exact inv_pos.2 (hmem σ hσ).2.2.2.2.1
  · have heq : (fun τ ↦ (deriv s (e.symm τ))⁻¹) =ᶠ[𝓝 σ] deriv e.symm :=
      Filter.Eventually.mono (isOpen_Ioo.mem_nhds hσ) fun τ hτ ↦ (hX τ hτ).deriv.symm
    exact (((hmem σ hσ).2.2.2.1.comp (e.continuousAt_symm (hmem σ hσ).1)).inv₀
      (hmem σ hσ).2.2.2.2.1.ne').congr heq |>.continuousWithinAt
  · have h := (hmem σ hσ).2.2.2.2.2
    have hσ' : s (e.symm σ) = σ := e.right_inv (hmem σ hσ).1
    rw [hσ'] at h
    linarith
  · have := hX 0 ⟨neg_lt_zero.2 hρ, hρ⟩
    rw [this.deriv, he0, hs.hasDerivAt.deriv, one_div]

/-- **One-dimensional Morse lemma.** At a nondegenerate minimum of a `C³` function there is a Morse
chart, whose derivative at the origin is `1 / √(U'' x₀)`. -/
theorem exists_morseChart {U : ℝ → ℝ} {Ω : Set ℝ} {x₀ : ℝ} (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω)
    (hU : ContDiffOn ℝ 3 U Ω) (h1 : deriv U x₀ = 0) (h2 : 0 < iteratedDeriv 2 U x₀) :
    ∃ c : MorseChart U Ω x₀, deriv c.X 0 = 1 / √(iteratedDeriv 2 U x₀) := by
  -- Extract `C²` information: `U` and `U'` are differentiable on `Ω`, `U'` continuous.
  obtain ⟨hdU, -, hU2⟩ := (contDiffOn_succ_iff_deriv_of_isOpen (n := 2) hΩ).1 hU
  have hdd : DifferentiableOn ℝ (deriv U) Ω := hU2.differentiableOn (by norm_num)
  have hd : ∀ x ∈ Ω, HasDerivAt U (deriv U x) x := fun x hx ↦
    (hdU.differentiableAt (hΩ.mem_nhds hx)).hasDerivAt
  have h2' : HasDerivAt (deriv U) (iteratedDeriv 2 U x₀) x₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hdd.differentiableAt (hΩ.mem_nhds hx₀)).hasDerivAt
  have hG := eventually_morseCoord hΩ hx₀ hd hU2.continuousOn h1 h2' h2
  have hs := hasDerivAt_morseCoord (tendsto_secondQuot hΩ hx₀ hd h1 h2')
  refine exists_morseChart_of_coord (by simp [morseCoord]) ?_ (sqrt_pos.2 h2) hG
  -- `s` is differentiable near `x₀` with `s'` continuous at `x₀`, hence strictly differentiable.
  have := hasStrictDerivAt_of_hasDerivAt_of_continuousAt (hG.mono fun x hx ↦ hx.2.1)
    (hG.self_of_nhds.2.2.1)
  rwa [hs.deriv] at this

end Bertrand
