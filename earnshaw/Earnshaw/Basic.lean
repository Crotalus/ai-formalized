/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Earnshaw's theorem

A harmonic function has no strict local minimum and no strict local maximum. Physically: a static
electric potential in a charge-free region cannot trap a charged particle in stable equilibrium.

## i. Overview

Let `E` be a finite-dimensional real inner product space of positive dimension and `f : E → ℝ` a
function which is harmonic near `x` (`C²` with `Δ f = 0` on a neighbourhood). We prove:

* the Hessian of `f` at `x` is never positive definite (linear instability);
* `f` has no strict local minimum and no strict local maximum at `x` (Earnshaw's theorem).

The second statement does not follow from the first: a strict minimum may have a degenerate
Hessian. Since Mathlib does not yet provide the mean-value property or maximum principle for
harmonic functions on `ℝⁿ`, the proof is a perturbation argument. If `x` were a strict local
minimum, then `f ≥ f x + δ` on a small sphere around `x`, and `g = f - ε ‖· - x‖²` with
`ε = δ / (2 r²)` would attain its minimum over the closed ball at an interior point `z`. There the
second-order necessary condition forces `Δ g z ≥ 0`, but `Δ g z = -2 ε dim E < 0`.

## ii. Key results

- `iteratedFDeriv_two_nonneg_of_isLocalMin` : second-order necessary condition for a minimum.
- `not_posDef_hessian_of_laplacian_eq_zero` : the Hessian at a point with `Δ f = 0` is not
  positive definite.
- `HarmonicAt.not_isStrictLocalMin`, `HarmonicAt.not_isStrictLocalMax` : Earnshaw's theorem.
- `earnshaw` : a test charge in a harmonic electrostatic potential has no strict local minimum of
  potential energy.

## iii. Table of contents

- A. Second derivatives along lines
- B. The second-order necessary condition
- C. The Laplacian of the squared distance
- D. Linear instability
- E. Earnshaw's theorem

## iv. References

* S. Earnshaw, *On the nature of the molecular forces which regulate the constitution of the
  luminiferous ether*, Trans. Camb. Phil. Soc. 7 (1842) 97–112.
* L. C. Evans, *Partial Differential Equations*, 2nd ed. (weak maximum principle).
-/

open Filter Set Metric InnerProductSpace Laplacian
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!

## A. Second derivatives along lines

-/

omit [FiniteDimensional ℝ E] in
/-- For a function which is `C²` at `z`, the second derivative of its restriction to the line
`t ↦ z + t v` at `t = 0` is the Hessian evaluated at `(v, v)`. -/
lemma deriv_deriv_comp_line {g : E → ℝ} {z : E} (hg : ContDiffAt ℝ 2 g z) (v : E) :
    deriv (deriv fun t : ℝ => g (z + t • v)) 0 = iteratedFDeriv ℝ 2 g z ![v, v] := by
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => z + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hcont : Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by
    have := (hline 0).continuousAt.tendsto
    simpa using this
  -- `g` is differentiable near `z`, so the first derivative along the line is `Dg(z + t v) v`.
  have hdiff : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hd : deriv (fun t : ℝ => g (z + t • v)) =ᶠ[𝓝 0]
      fun t => fderiv ℝ g (z + t • v) v :=
    (hcont.eventually hdiff).mono fun t ht => (ht.hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  rw [hd.deriv_eq]
  -- The derivative of `Dg` at `z` exists since `g` is `C²`.
  have hD : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h := (hD.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) (by simp)).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  simpa using h.deriv

/-!

## B. The second-order necessary condition

-/

omit [FiniteDimensional ℝ E] in
/-- At a local minimum of a function which is `C²` there, the Hessian is positive semidefinite. -/
lemma iteratedFDeriv_two_nonneg_of_isLocalMin {g : E → ℝ} {z : E} (hg : ContDiffAt ℝ 2 g z)
    (hmin : IsLocalMin g z) (v : E) : 0 ≤ iteratedFDeriv ℝ 2 g z ![v, v] := by
  rw [← deriv_deriv_comp_line hg v]
  set φ : ℝ → ℝ := fun t => g (z + t • v) with hφ
  have hcont : ContinuousAt (fun t : ℝ => z + t • v) 0 := by fun_prop
  have hφmin : IsLocalMin φ 0 :=
    IsLocalMin.comp_continuous (g := fun t : ℝ => z + t • v) (by simpa using hmin) hcont
  have hφcont : ContinuousAt φ 0 :=
    ContinuousAt.comp_of_eq hg.continuousAt hcont (by simp)
  by_contra hneg
  push Not at hneg
  -- By the second-derivative test `0` would also be a local maximum, so `φ` is locally constant.
  have hφmax := isLocalMax_of_deriv_deriv_neg hneg hφmin.deriv_eq_zero hφcont
  have hconst : φ =ᶠ[𝓝 0] fun _ => φ 0 :=
    (hφmin.and hφmax).mono fun t ht => le_antisymm ht.2 ht.1
  have hderiv : deriv φ =ᶠ[𝓝 0] fun _ => 0 :=
    hconst.eventuallyEq_nhds.mono fun t ht => by rw [ht.deriv_eq, deriv_const]
  rw [hderiv.deriv_eq, deriv_const] at hneg
  exact lt_irrefl _ hneg

/-- At a local minimum of a function which is `C²` there, the Laplacian is non-negative. -/
lemma laplacian_nonneg_of_isLocalMin {g : E → ℝ} {z : E} (hg : ContDiffAt ℝ 2 g z)
    (hmin : IsLocalMin g z) : 0 ≤ Δ g z := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact Finset.sum_nonneg fun i _ => iteratedFDeriv_two_nonneg_of_isLocalMin hg hmin _

/-!

## C. The Laplacian of the squared distance

-/

omit [FiniteDimensional ℝ E] in
/-- The Hessian of `y ↦ ‖y - x‖²` at any point, evaluated at `(v, v)`, is `2 ‖v‖²`. -/
lemma iteratedFDeriv_two_norm_sub_sq (x z v : E) :
    iteratedFDeriv ℝ 2 (fun y => ‖y - x‖ ^ 2) z ![v, v] = 2 * ‖v‖ ^ 2 := by
  have hg : ContDiffAt ℝ 2 (fun y : E => ‖y - x‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const)
  rw [← deriv_deriv_comp_line hg v]
  have h : (fun t : ℝ => ‖z + t • v - x‖ ^ 2) =
      fun t => ‖z - x‖ ^ 2 + 2 * t * ⟪z - x, v⟫_ℝ + t ^ 2 * ‖v‖ ^ 2 := by
    funext t
    rw [show z + t • v - x = (z - x) + t • v by abel, norm_add_sq_real, norm_smul,
      inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h1 : deriv (fun t : ℝ => ‖z - x‖ ^ 2 + 2 * t * ⟪z - x, v⟫_ℝ + t ^ 2 * ‖v‖ ^ 2) =
      fun t => 2 * ⟪z - x, v⟫_ℝ + 2 * t * ‖v‖ ^ 2 := by
    funext t
    have := (((hasDerivAt_id t).const_mul 2).mul_const ⟪z - x, v⟫_ℝ).const_add (‖z - x‖ ^ 2)
      |>.add ((hasDerivAt_pow 2 t).mul_const (‖v‖ ^ 2))
    exact this.deriv.trans (by ring)
  have h2 : HasDerivAt (fun t : ℝ => 2 * ⟪z - x, v⟫_ℝ + 2 * t * ‖v‖ ^ 2) (2 * ‖v‖ ^ 2) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (‖v‖ ^ 2)).const_add
      (2 * ⟪z - x, v⟫_ℝ)
  rw [h, h1, h2.deriv]

/-- The Laplacian of `y ↦ ‖y - x‖²` is `2 dim E` everywhere. -/
lemma laplacian_norm_sub_sq (x z : E) :
    Δ (fun y => ‖y - x‖ ^ 2) z = 2 * Module.finrank ℝ E := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_norm_sub_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-!

## D. Linear instability

-/

/-- If the Laplacian of `f` vanishes at `x`, the Hessian of `f` at `x` is not positive definite:
an equilibrium of a harmonic potential is never linearly stable. -/
lemma not_posDef_hessian_of_laplacian_eq_zero [Nontrivial E] {f : E → ℝ} {x : E}
    (h : Δ f x = 0) : ¬ ∀ v ≠ 0, 0 < iteratedFDeriv ℝ 2 f x ![v, v] := by
  intro hpos
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis] at h
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hsum := Finset.sum_pos (fun i _ => hpos _ ((stdOrthonormalBasis ℝ E).orthonormal.ne_zero i))
    (Finset.univ_nonempty (α := Fin (Module.finrank ℝ E)))
  exact hsum.ne' h

/-!

## E. Earnshaw's theorem

-/

/-- **Earnshaw's theorem**, minimum version: a function which is harmonic near `x` does not have a
strict local minimum at `x`. -/
theorem HarmonicAt.not_isStrictLocalMin [Nontrivial E] {f : E → ℝ} {x : E}
    (hf : HarmonicAt f x) : ¬ ∀ᶠ y in 𝓝[≠] x, f x < f y := by
  intro hstrict
  -- Choose `r` such that `f` is harmonic on, and `x` a strict minimum of, `closedBall x r`.
  obtain ⟨ε₁, hε₁, hH⟩ := Metric.eventually_nhds_iff.mp hf.eventually
  obtain ⟨ε₂, hε₂, hS⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hstrict)
  set r := min ε₁ ε₂ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrH : ∀ y ∈ closedBall x r, HarmonicAt f y := fun y hy =>
    hH (lt_of_le_of_lt (mem_closedBall.mp hy) (by rw [hr]; linarith [min_le_left ε₁ ε₂]))
  have hrS : ∀ y ∈ sphere x r, f x < f y := fun y hy =>
    hS (by rw [mem_sphere.mp hy, hr]; linarith [min_le_right ε₁ ε₂])
      (by intro h; rw [mem_singleton_iff.mp h, mem_sphere, dist_self] at hy; exact hr0.ne hy)
  have hcontf : ContinuousOn f (closedBall x r) := fun y hy =>
    (hrH y hy).1.continuousAt.continuousWithinAt
  -- On the sphere, `f ≥ f x + δ` for some `δ > 0`.
  obtain ⟨y₀, hy₀, hmin₀⟩ := (isCompact_sphere x r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr0.le) (hcontf.mono sphere_subset_closedBall)
  set δ := f y₀ - f x with hδ
  have hδ0 : 0 < δ := sub_pos.mpr (hrS y₀ hy₀)
  -- The perturbed function `g = f - ε ‖· - x‖²` is strictly superharmonic.
  set ε := δ / (2 * r ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  set g : E → ℝ := f - ε • fun y => ‖y - x‖ ^ 2 with hg
  have hcontg : ContinuousOn g (closedBall x r) :=
    hcontf.sub (continuousOn_const.smul (by fun_prop))
  obtain ⟨z, hz, hminz⟩ := (isCompact_closedBall x r).exists_isMinOn
    ⟨x, mem_closedBall_self hr0.le⟩ hcontg
  -- The minimum of `g` is not on the sphere, so it is an interior local minimum.
  have hgz : g z ≤ f x := by simpa [hg] using hminz (mem_closedBall_self hr0.le)
  have hzball : z ∈ ball x r := by
    refine mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hz) fun hzr => ?_)
    have hzs : z ∈ sphere x r := mem_sphere.mpr hzr
    have h1 : f y₀ ≤ f z := hmin₀ hzs
    have h2 : g z = f z - ε * r ^ 2 := by simp [hg, ← dist_eq_norm, hzr]
    have h3 : ε * r ^ 2 = δ / 2 := by rw [hε]; field_simp
    linarith
  have hlocal : IsLocalMin g z :=
    hminz.isLocalMin (mem_of_superset (isOpen_ball.mem_nhds hzball) ball_subset_closedBall)
  -- Compare the Laplacian of `g` at `z` with the second-order condition.
  have hfz := hrH z hz
  have hq : ContDiffAt ℝ 2 (fun y : E => ‖y - x‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const)
  have hq' : ContDiffAt ℝ 2 (ε • fun y : E => ‖y - x‖ ^ 2) z := hq.const_smul ε
  have hnonneg : 0 ≤ Δ g z := laplacian_nonneg_of_isLocalMin (hfz.1.sub hq') hlocal
  rw [hg, hfz.1.laplacian_sub hq', laplacian_smul ε hq, hfz.2.self_of_nhds,
    laplacian_norm_sub_sq] at hnonneg
  have hdim : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  simp only [Pi.zero_apply, smul_eq_mul, zero_sub] at hnonneg
  nlinarith

/-- **Earnshaw's theorem**, maximum version: a function which is harmonic near `x` does not have a
strict local maximum at `x`. -/
theorem HarmonicAt.not_isStrictLocalMax [Nontrivial E] {f : E → ℝ} {x : E}
    (hf : HarmonicAt f x) : ¬ ∀ᶠ y in 𝓝[≠] x, f y < f x := fun h =>
  HarmonicAt.not_isStrictLocalMin (HarmonicAt.neg hf) (h.mono fun _ hy => by simpa using hy)

/-- **Earnshaw's theorem** for electrostatics: if the electrostatic potential `V` is harmonic near
`x` (no charge there), then for any charge `q`, the potential energy `q V` of a test charge does
not have a strict local minimum at `x`, so `x` is not a point of stable equilibrium. -/
theorem earnshaw {V : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hV : HarmonicAt V x) (q : ℝ) : ¬ ∀ᶠ y in 𝓝[≠] x, q * V x < q * V y :=
  HarmonicAt.not_isStrictLocalMin (HarmonicAt.const_smul (c := q) hV)
