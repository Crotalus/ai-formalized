/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.MorseLemma
/-!

# A smooth Morse chart

If `U` is smooth near a nondegenerate minimum `x₀`, there is a Morse chart whose inverse
coordinate `X` is smooth. The key input is Hadamard's lemma: for smooth `f`, the difference
quotient `dslope f a` is smooth; applied twice it shows that
`q x = (U x - U x₀) / (x - x₀)²` (with `q x₀ = U'' x₀ / 2`) is smooth, hence so is the Morse
coordinate `s x = (x - x₀) √(2 q x)`, and its local inverse.

Hadamard's lemma is proved in integral form, `dslope f a x = ∫ t in 0..1, f' (a + t (x - a))`,
with smoothness of parameter-dependent integrals obtained by differentiating under the integral
sign. Since `U` is only smooth on `Ω`, it is first replaced by a globally smooth function agreeing
with it near `x₀` (via a bump function).
-/

open Set Filter Topology Real
open scoped ContDiff

namespace Bertrand

/-- The partial derivative `∂H/∂x (x, t)` of a function of two real variables. -/
noncomputable def partialFst (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ H p (1, 0)

/-- The partial derivative of a smooth function is smooth. -/
lemma contDiff_partialFst {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (partialFst H) :=
  (hH.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- Differentiation under the integral sign for `x ↦ ∫ t in 0..1, H (x, t)`. -/
lemma hasDerivAt_integral_param {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ 1 H) (x : ℝ) :
    HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..1, H (y, t))
      (∫ t in (0 : ℝ)..1, partialFst H (x, t)) x := by
  have hcont : Continuous (partialFst H) :=
    (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hslice : ∀ y : ℝ, Continuous fun t : ℝ ↦ (y, t) := fun y ↦
    continuous_const.prodMk continuous_id
  -- A uniform bound for `∂H/∂x` on the compact set `closedBall x 1 ×ˢ [0, 1]`.
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod isCompact_Icc).exists_bound_of_continuousOn
    hcont.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ ↦ C)
    (F := fun y t ↦ H (y, t)) (F' := fun y t ↦ partialFst H (y, t))
    (Metric.closedBall_mem_nhds x one_pos)
    (Eventually.of_forall fun y ↦ (hH.continuous.comp (hslice y)).aestronglyMeasurable)
    ((hH.continuous.comp (hslice x)).intervalIntegrable 0 1)
    (hcont.comp (hslice x)).aestronglyMeasurable ?_ intervalIntegrable_const ?_).2
  · refine Eventually.of_forall fun t ht y hy ↦ hC (y, t) ⟨hy, ?_⟩
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · refine Eventually.of_forall fun t _ y _ ↦ ?_
    exact ((hH.differentiable one_ne_zero (y, t)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_id y).prodMk (hasDerivAt_const y t)))

/-- Integrating a smooth function of two variables over `t ∈ [0, 1]` gives a smooth function. -/
lemma contDiff_integral_param {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, H (x, t)) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing H with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x ↦
      (hasDerivAt_integral_param (hH.of_le (by simp)) x).continuousAt)
  | succ n ih =>
    have hd := hasDerivAt_integral_param (hH.of_le (by simp))
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (hd x).differentiableAt, by simp, ?_⟩
    rw [funext fun x ↦ (hd x).deriv]
    exact ih (contDiff_partialFst hH)

/-- Hadamard's lemma, integral form: `dslope f a x = ∫ t in 0..1, f' (a + t (x - a))`. -/
lemma dslope_eq_integral {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a x : ℝ) :
    dslope f a x = ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a)) := by
  rcases eq_or_ne x a with rfl | hx
  · simp [dslope_same]
  rw [dslope_of_ne _ hx, slope_def_field]
  have hcd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t ↦ f (a + t * (x - a))) (f' := fun t ↦ deriv f (a + t * (x - a)) * (x - a))
    (a := 0) (b := 1) (fun t _ ↦ by
      have h1 : HasDerivAt (fun t ↦ a + t * (x - a)) (x - a) t := by
        simpa using ((hasDerivAt_id t).mul_const (x - a)).const_add a
      exact (hf.differentiable one_ne_zero _).hasDerivAt.comp t h1)
    (((hcd.comp (by fun_prop : Continuous fun t : ℝ ↦ a + t * (x - a))).mul
      continuous_const).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const] at hftc
  simp only [one_mul, zero_mul, add_zero, add_sub_cancel] at hftc
  rw [← hftc, mul_div_cancel_right₀ _ (sub_ne_zero.2 hx)]

/-- **Hadamard's lemma**: the difference quotient of a smooth function is smooth. -/
lemma contDiff_dslope {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) : ContDiff ℝ ∞ (dslope f a) := by
  rw [funext (dslope_eq_integral (hf.of_le (by simp)) a)]
  exact contDiff_integral_param (H := fun p ↦ deriv f (a + p.2 * (p.1 - a)))
    ((contDiff_infty_iff_deriv.1 hf).2.comp (by fun_prop))


variable {U : ℝ → ℝ} {Ω : Set ℝ} {x₀ : ℝ}

/-- A function smooth on an open set agrees near any of its points with a globally smooth
function (multiply by a bump function supported in the set). -/
lemma exists_contDiff_eventuallyEq (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω) (hU : ContDiffOn ℝ ∞ U Ω) :
    ∃ V : ℝ → ℝ, ContDiff ℝ ∞ V ∧ V =ᶠ[𝓝 x₀] U := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  let φ : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun x ↦ φ x * U x, contDiff_iff_contDiffAt.2 fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ Ω
    · exact φ.contDiffAt.mul (hU.contDiffAt (hΩ.mem_nhds hx))
    -- Outside `Ω` we are away from `closedBall x₀ (r / 2) ⊇ support φ`, where the product is `0`.
    have hxb : x ∉ Metric.closedBall x₀ (r / 2) := fun h ↦
      hx (hrΩ (Metric.closedBall_subset_ball (by linarith) h))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hxb] with y hy
    have : φ y = 0 := Function.notMem_support.1 fun h ↦
      hy (Metric.ball_subset_closedBall (φ.support_eq ▸ h))
    simp [this]
  · filter_upwards [Metric.closedBall_mem_nhds x₀ (by positivity : 0 < r / 4)] with y hy
    simp [φ.one_of_mem_closedBall hy]

/-- The second difference quotient `(U x - U x₀) / (x - x₀)²` extends smoothly across `x₀`, with
value `U'' x₀ / 2` there (Hadamard's lemma applied twice). -/
lemma exists_smooth_secondQuot (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω) (hU : ContDiffOn ℝ ∞ U Ω)
    (h1 : deriv U x₀ = 0) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧ q x₀ = iteratedDeriv 2 U x₀ / 2 ∧
      ∀ᶠ x in 𝓝 x₀, x ≠ x₀ → q x = secondQuot U x₀ x := by
  obtain ⟨V, hV, hVU⟩ := exists_contDiff_eventuallyEq hΩ hx₀ hU
  have hq := contDiff_dslope (contDiff_dslope hV x₀) x₀
  have hV1 : deriv V x₀ = 0 := hVU.deriv_eq ▸ h1
  have hqeq : ∀ᶠ x in 𝓝 x₀, x ≠ x₀ → dslope (dslope V x₀) x₀ x = secondQuot U x₀ x := by
    filter_upwards [hVU] with x hx hne
    rw [dslope_of_ne _ hne, slope_def_field, dslope_same, hV1, dslope_of_ne _ hne,
      slope_def_field, hx, hVU.self_of_nhds, secondQuot]
    field_simp [sub_ne_zero.2 hne]
    ring
  refine ⟨_, hq, ?_, hqeq⟩
  -- The value at `x₀` is the limit of the quotient, computed by L'Hôpital in `MorseLemma`.
  obtain ⟨hdU, -, hU2⟩ := (contDiffOn_succ_iff_deriv_of_isOpen (n := 2) hΩ).1
    (hU.of_le (by simp))
  have hd : ∀ x ∈ Ω, HasDerivAt U (deriv U x) x := fun x hx ↦
    (hdU.differentiableAt (hΩ.mem_nhds hx)).hasDerivAt
  have h2' : HasDerivAt (deriv U) (iteratedDeriv 2 U x₀) x₀ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hU2.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hx₀)).hasDerivAt
  refine tendsto_nhds_unique (hq.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((tendsto_secondQuot hΩ hx₀ hd h1 h2').congr' ?_)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hqeq, self_mem_nhdsWithin] with x h hx
  exact (h hx).symm


/-- Inverting a coordinate `s` with `s x₀ = 0`, `s' x₀ = d > 0`, which near `x₀` is smooth with
positive derivative and satisfies `s² = 2 (U - U x₀)`, gives a Morse chart with smooth `X` and
`X' 0 = 1 / d`. (Smooth analogue of `exists_morseChart_of_coord`.) -/
lemma exists_smoothMorseChart_of_coord {s : ℝ → ℝ} {d : ℝ} (hs0 : s x₀ = 0)
    (hs : HasStrictDerivAt s d x₀) (hd : 0 < d)
    (hG : ∀ᶠ x in 𝓝 x₀, x ∈ Ω ∧ ContDiffAt ℝ ∞ s x ∧ ContinuousAt (deriv s) x ∧
      0 < deriv s x ∧ s x ^ 2 = 2 * (U x - U x₀)) :
    ∃ c : MorseChart U Ω x₀, ContDiffOn ℝ ∞ c.X (Ioo (-c.ρ) c.ρ) ∧ deriv c.X 0 = 1 / d := by
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
  have hsd : ∀ σ ∈ Ioo (-ρ) ρ, HasDerivAt s (deriv s (e.symm σ)) (e.symm σ) := fun σ hσ ↦
    ((hmem σ hσ).2.2.1.differentiableAt (by simp)).hasDerivAt
  -- `X = e.symm` has derivative `1 / s' (X σ)` on `(-ρ, ρ)`.
  have hX : ∀ σ ∈ Ioo (-ρ) ρ, HasDerivAt e.symm (deriv s (e.symm σ))⁻¹ σ := fun σ hσ ↦
    e.hasDerivAt_symm (hmem σ hσ).1 (hmem σ hσ).2.2.2.2.1.ne' (hsd σ hσ)
  refine ⟨⟨e.symm, ρ, hρ, he0, fun σ hσ ↦ (hmem σ hσ).2.1, fun σ hσ ↦ ?_, fun σ hσ ↦ ?_,
    fun σ hσ ↦ ?_, fun σ hσ ↦ ?_⟩, fun σ hσ ↦ ?_, ?_⟩
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
  -- Smoothness of the inverse of a smooth map with nonvanishing derivative.
  · exact (e.contDiffAt_symm_deriv (hmem σ hσ).2.2.2.2.1.ne' (hmem σ hσ).1 (hsd σ hσ)
      (hmem σ hσ).2.2.1).contDiffWithinAt
  · have := hX 0 ⟨neg_lt_zero.2 hρ, hρ⟩
    rw [this.deriv, he0, hs.hasDerivAt.deriv, one_div]

/-- **Smooth one-dimensional Morse lemma.** -/
theorem exists_smoothMorseChart {U : ℝ → ℝ} {Ω : Set ℝ} {x₀ : ℝ} (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω)
    (hU : ContDiffOn ℝ ∞ U Ω) (h1 : deriv U x₀ = 0) (h2 : 0 < iteratedDeriv 2 U x₀) :
    ∃ c : MorseChart U Ω x₀, ContDiffOn ℝ ∞ c.X (Ioo (-c.ρ) c.ρ) ∧
      deriv c.X 0 = 1 / √(iteratedDeriv 2 U x₀) := by
  obtain ⟨q, hq, hqx₀, hqeq⟩ := exists_smooth_secondQuot hΩ hx₀ hU h1
  have h2q : 2 * q x₀ = iteratedDeriv 2 U x₀ := by rw [hqx₀]; ring
  -- The Morse coordinate `s x = (x - x₀) √(2 q x)` is smooth wherever `q > 0`.
  set s : ℝ → ℝ := fun x ↦ (x - x₀) * √(2 * q x)
  set W := {x | 0 < q x}
  have hW : IsOpen W := isOpen_lt continuous_const hq.continuous
  have hx₀W : x₀ ∈ W := show 0 < q x₀ by linarith
  have hsqrt : ∀ x ∈ W, ContDiffAt ℝ ∞ (fun y ↦ √(2 * q y)) x := fun x hx ↦
    (contDiffAt_const.mul hq.contDiffAt).sqrt (by have : 0 < q x := hx; positivity)
  have hsW : ∀ x ∈ W, ContDiffAt ℝ ∞ s x := fun x hx ↦
    (contDiffAt_id.sub contDiffAt_const).mul (hsqrt x hx)
  have hcW : ContinuousOn (deriv s) W :=
    ContDiffOn.continuousOn_deriv_of_isOpen (fun x hx ↦ (hsW x hx).contDiffWithinAt) hW (by simp)
  have hs' : HasDerivAt s (√(iteratedDeriv 2 U x₀)) x₀ := by
    have := ((hasDerivAt_id' x₀).sub_const x₀).fun_mul
      ((hsqrt x₀ hx₀W).differentiableAt (by simp)).hasDerivAt
    convert this using 1
    simp [h2q]
  have hpos : ∀ᶠ x in 𝓝 x₀, 0 < deriv s x :=
    (hcW.continuousAt (hW.mem_nhds hx₀W)).eventually
      (eventually_gt_nhds (by rw [hs'.deriv]; exact sqrt_pos.2 h2))
  have hstrict := (hsW x₀ hx₀W).hasStrictDerivAt (by simp)
  rw [hs'.deriv] at hstrict
  refine exists_smoothMorseChart_of_coord (by simp [s]) hstrict (sqrt_pos.2 h2) ?_
  filter_upwards [hΩ.mem_nhds hx₀, hW.mem_nhds hx₀W, hpos, hqeq] with x hxΩ hxW hxpos hxq
  refine ⟨hxΩ, hsW x hxW, hcW.continuousAt (hW.mem_nhds hxW), hxpos, ?_⟩
  -- Off `x₀`, `s` is the Morse coordinate of `MorseLemma`, so `s² = 2 (U - U x₀)`.
  have hsm : s x = morseCoord U x₀ x := by
    rcases eq_or_ne x x₀ with rfl | hne
    · simp [s, morseCoord]
    · simp [s, morseCoord, hxq hne]
  rw [hsm]
  exact morseCoord_sq fun hne ↦ hxq hne ▸ hxW

end Bertrand
