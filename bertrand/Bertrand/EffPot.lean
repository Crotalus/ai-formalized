/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.Chart
/-!

# The effective potential of a central-force orbit

A particle of unit mass moves in a central potential `V`. With angular momentum `M` and the
variable `x = M / r`, the radial motion as a function of the polar angle is an oscillation in the
effective potential `U x = x² / 2 + V (M / x)`. A circular orbit of radius `r` has `M² = r³ V' r`;
it sits at the critical point `x₀ = M / r` of `U`, where `U'' x₀ = 3 + r V'' r / V' r`.

This file also contains two auxiliary facts used in part I of Bertrand's theorem: a continuous
rational-valued function on a preconnected set is constant, and the solutions of
`r V'' = p V'` are power laws.
-/

open Set Filter Topology Real

namespace Bertrand

/-- The effective potential, in the variable `x = M / r`, of a unit mass with angular momentum `M`
in the central potential `V`. -/
noncomputable def effPot (V : ℝ → ℝ) (M x : ℝ) : ℝ := x ^ 2 / 2 + V (M / x)

/-- The angular momentum of the circular orbit of radius `r`: `M² = r³ V' r`. -/
noncomputable def angMom (V : ℝ → ℝ) (r : ℝ) : ℝ := √(r ^ 3 * deriv V r)

/-- The energy of the circular orbit of radius `r`. -/
noncomputable def circularEnergy (V : ℝ → ℝ) (r : ℝ) : ℝ :=
  effPot V (angMom V r) (angMom V r / r)

/-- The apsidal angle of the orbit with energy `E` and the angular momentum of the circular orbit of
radius `r`, for motion confined to radii in `(a, b)`. -/
noncomputable def orbitApsidalAngle (V : ℝ → ℝ) (a b r E : ℝ) : ℝ :=
  apsidalAngle (effPot V (angMom V r)) (Ioo (angMom V r / b) (angMom V r / a)) (angMom V r / r) E

/-!

## A. Calculus of the effective potential

-/

/-- The derivative of the effective potential. -/
lemma hasDerivAt_effPot {V : ℝ → ℝ} {M x : ℝ} (hx : x ≠ 0)
    (hV : DifferentiableAt ℝ V (M / x)) :
    HasDerivAt (effPot V M) (x - M / x ^ 2 * deriv V (M / x)) x := by
  have hinv : HasDerivAt (fun y : ℝ => M / y) (-(M / x ^ 2)) x := by
    have := (hasDerivAt_inv hx).const_mul M
    simp only [div_eq_mul_inv] at this ⊢
    convert this using 1
    ring
  have h := ((hasDerivAt_pow 2 x).div_const 2).add (hV.hasDerivAt.comp x hinv)
  convert h using 1
  · rfl
  · push_cast
    ring

/-- The circular orbit is a critical point of the effective potential. -/
lemma deriv_effPot_circular {V : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hV' : 0 < deriv V r)
    (hV : DifferentiableAt ℝ V r) :
    deriv (effPot V (angMom V r)) (angMom V r / r) = 0 := by
  have hM : 0 < angMom V r := Real.sqrt_pos.mpr (by positivity)
  have hM2 : angMom V r ^ 2 = r ^ 3 * deriv V r := Real.sq_sqrt (by positivity)
  have hMr : angMom V r / (angMom V r / r) = r := by field_simp
  rw [(hasDerivAt_effPot (by positivity) (by rwa [hMr])).deriv, hMr]
  field_simp
  rw [hM2]
  ring

/-- At the circular orbit, `U'' = 3 + r V'' / V'`. -/
lemma iteratedDeriv_two_effPot_circular {V : ℝ → ℝ} {a b r : ℝ} (ha : 0 < a)
    (hV : ContDiffOn ℝ 3 V (Ioo a b)) (hr : r ∈ Ioo a b) (hV' : 0 < deriv V r) :
    iteratedDeriv 2 (effPot V (angMom V r)) (angMom V r / r) =
      3 + r * iteratedDeriv 2 V r / deriv V r := by
  set M := angMom V r with hMdef
  have hr0 : 0 < r := ha.trans hr.1
  have hM : 0 < M := Real.sqrt_pos.mpr (by positivity)
  have hM2 : M ^ 2 = r ^ 3 * deriv V r := Real.sq_sqrt (by positivity)
  set x₀ := M / r with hx₀
  have hx0 : 0 < x₀ := by positivity
  have hMr : M / x₀ = r := by rw [hx₀]; field_simp
  -- `V'` is differentiable on `(a, b)`.
  have hV1 : ContDiffOn ℝ 2 (deriv V) (Ioo a b) := hV.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdV : ∀ y ∈ Ioo a b, HasDerivAt (deriv V) (iteratedDeriv 2 V y) y := fun y hy => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hV1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  -- Near `x₀`, the derivative of `U` is `x - M / x² V' (M / x)`.
  have hcont : ContinuousAt (fun x : ℝ => M / x) x₀ := continuousAt_const.div continuousAt_id hx0.ne'
  have hnhds : Ioo a b ∈ 𝓝 (M / x₀) := by
    rw [hMr]
    exact isOpen_Ioo.mem_nhds hr
  have hev : ∀ᶠ x in 𝓝 x₀, x ≠ 0 ∧ M / x ∈ Ioo a b :=
    (eventually_ne_nhds hx0.ne').and (hcont.preimage_mem_nhds hnhds)
  have hD : deriv (effPot V M) =ᶠ[𝓝 x₀] fun x => x - M / x ^ 2 * deriv V (M / x) :=
    hev.mono fun x hx => (hasDerivAt_effPot hx.1 ((hV.contDiffAt (isOpen_Ioo.mem_nhds hx.2)
      ).differentiableAt (by norm_num))).deriv
  have hinv : HasDerivAt (fun y : ℝ => M / y) (-(M / x₀ ^ 2)) x₀ := by
    have := (hasDerivAt_inv hx0.ne').const_mul M
    simp only [div_eq_mul_inv] at this ⊢
    convert this using 1
    ring
  have hsq : HasDerivAt (fun y : ℝ => M / y ^ 2) (-(2 * M / x₀ ^ 3)) x₀ := by
    have := ((hasDerivAt_pow 2 x₀).inv (by positivity)).const_mul M
    simp only [div_eq_mul_inv] at this ⊢
    convert this using 1
    field_simp
    ring
  have hcomp : HasDerivAt (fun y => deriv V (M / y)) (iteratedDeriv 2 V r * -(M / x₀ ^ 2)) x₀ :=
    (hdV r hr).comp_of_eq x₀ hinv hMr.symm
  have h := (hasDerivAt_id x₀).sub (hsq.mul hcomp)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hD.deriv_eq]
  rw [show deriv (fun x => x - M / x ^ 2 * deriv V (M / x)) x₀ = 1 - (-(2 * M / x₀ ^ 3) *
    deriv V (M / x₀) + M / x₀ ^ 2 * (iteratedDeriv 2 V r * -(M / x₀ ^ 2))) from h.deriv, hMr, hx₀]
  field_simp
  linear_combination (-(2 * deriv V r + r * iteratedDeriv 2 V r)) * hM2

/-- The effective potential is `C³` on the radii `(a, b)`. -/
lemma contDiffOn_effPot {V : ℝ → ℝ} {a b M : ℝ} (ha : 0 < a) (hab : a < b) (hM : 0 < M)
    (hV : ContDiffOn ℝ 3 V (Ioo a b)) :
    ContDiffOn ℝ 3 (effPot V M) (Ioo (M / b) (M / a)) := by
  have hb : 0 < b := ha.trans hab
  have hpos : ∀ x ∈ Ioo (M / b) (M / a), 0 < x := fun x hx => (div_pos hM hb).trans hx.1
  have hmaps : MapsTo (fun x : ℝ => M / x) (Ioo (M / b) (M / a)) (Ioo a b) := fun x hx => by
    have hx0 := hpos x hx
    have h1 := (lt_div_iff₀ ha).mp hx.2
    have h2 := (div_lt_iff₀ hb).mp hx.1
    exact ⟨(lt_div_iff₀ hx0).mpr (by linarith), (div_lt_iff₀ hx0).mpr (by linarith)⟩
  show ContDiffOn ℝ 3 (fun x => x ^ 2 / 2 + V (M / x)) _
  exact ((contDiffOn_id.pow 2).div_const 2).add
    (hV.comp (contDiffOn_const.div contDiffOn_id fun x hx => (hpos x hx).ne') hmaps)

/-!

## B. Rational-valued continuous functions

-/

/-- A continuous function with rational values on a preconnected set is constant there. -/
lemma eq_of_continuousOn_rat {f : ℝ → ℝ} {s : Set ℝ} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (hq : ∀ x ∈ s, ∃ q : ℚ, f x = q) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    f x = f y := by
  -- If `f x ≠ f y`, the image would contain an interval, hence an irrational number.
  by_contra hne
  have himg : IsPreconnected (f '' s) := hs.image f hf
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn h
    obtain ⟨w, hw, hwz⟩ := himg.Icc_subset (mem_image_of_mem f hx) (mem_image_of_mem f hy)
      ⟨hxz.le, hzy.le⟩
    obtain ⟨q, hq⟩ := hq w hw
    exact hz ⟨q, by rw [← hq, hwz]⟩
  · obtain ⟨z, hz, hyz, hzx⟩ := exists_irrational_btwn h
    obtain ⟨w, hw, hwz⟩ := himg.Icc_subset (mem_image_of_mem f hy) (mem_image_of_mem f hx)
      ⟨hyz.le, hzx.le⟩
    obtain ⟨q, hq⟩ := hq w hw
    exact hz ⟨q, by rw [← hq, hwz]⟩

/-!

## C. Power laws

-/

/-- If `r V'' r = p V' r` on `(a, b)`, then `V'` is a power law there. -/
lemma deriv_eq_rpow_of_ode {V : ℝ → ℝ} {a b p : ℝ} (ha : 0 < a) (hV : ContDiffOn ℝ 3 V (Ioo a b))
    (hode : ∀ r ∈ Ioo a b, r * iteratedDeriv 2 V r = p * deriv V r) :
    ∃ C : ℝ, ∀ r ∈ Ioo a b, deriv V r = C * r ^ p := by
  rcases (Ioo a b).eq_empty_or_nonempty with he | ⟨r₁, hr₁⟩
  · exact ⟨0, by simp [he]⟩
  have hpos : ∀ r ∈ Ioo a b, 0 < r := fun r hr => ha.trans hr.1
  have hV1 : ContDiffOn ℝ 2 (deriv V) (Ioo a b) := hV.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdV : ∀ r ∈ Ioo a b, HasDerivAt (deriv V) (iteratedDeriv 2 V r) r := fun r hr => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hV1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  -- `h r = V' r * r ^ (-p)` has derivative `r ^ (-p) / r * (r V'' - p V') = 0`.
  have hh : ∀ r ∈ Ioo a b, HasDerivAt (fun r => deriv V r * r ^ (-p))
      (iteratedDeriv 2 V r * r ^ (-p) + deriv V r * (-p * r ^ (-p - 1))) r := fun r hr =>
    (hdV r hr).mul (Real.hasDerivAt_rpow_const (Or.inl (hpos r hr).ne'))
  have hzero : ∀ r ∈ Ioo a b,
      iteratedDeriv 2 V r * r ^ (-p) + deriv V r * (-p * r ^ (-p - 1)) = 0 := fun r hr => by
    have hr0 := hpos r hr
    rw [Real.rpow_sub_one hr0.ne']
    have := hode r hr
    field_simp
    linear_combination r ^ (-p) * this
  have hconst : ∀ r ∈ Ioo a b, deriv V r * r ^ (-p) = deriv V r₁ * r₁ ^ (-p) := fun r hr =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun y hy => (hh y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hh y hy).deriv, hzero y hy]; rfl) hr hr₁
  refine ⟨deriv V r₁ * r₁ ^ (-p), fun r hr => ?_⟩
  have hr0 := hpos r hr
  rw [← hconst r hr, mul_assoc, ← Real.rpow_add hr0, neg_add_cancel, Real.rpow_zero, mul_one]

end Bertrand
