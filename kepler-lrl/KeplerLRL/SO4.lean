/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import KeplerLRL.Kepler
/-!

# The hidden `so(4)` symmetry of the Kepler problem

The Poisson algebra of the angular momentum and the Laplace–Runge–Lenz vector.

## i. Overview

For the Kepler problem with Hamiltonian `H`, angular momentum `L = q × p` and Laplace–Runge–Lenz
vector `A`, the components along fixed vectors `a`, `b` satisfy

$$\{L_a, L_b\} = L_{a × b}, \qquad \{A_a, L_b\} = A_{a × b}, \qquad
  \{A_a, A_b\} = -2 m H \, L_{a × b},$$

where `X_a = ⟪a, X⟫`. Taking `a`, `b` to be basis vectors gives the familiar relations
`{Lᵢ, Lⱼ} = εᵢⱼₖ Lₖ`, `{Aᵢ, Lⱼ} = εᵢⱼₖ Aₖ` and `{Aᵢ, Aⱼ} = -2 m H εᵢⱼₖ Lₖ`.

On the bound region `H < 0` the rescaled vector `M = A / √(-2 m H)` satisfies
`{M_a, M_b} = L_{a × b}`. The combinations `J± = (L ± M) / 2` then form two commuting copies of
`so(3)`, so `L` and `M` together generate `so(4) ≅ so(3) ⊕ so(3)`. The two Casimirs are
`⟪L, M⟫ = 0` and `‖J±‖² = -m k² / (8 H)`, which expresses the energy through the `so(4)`
Casimir: the classical counterpart of Pauli's derivation of the hydrogen spectrum.

## ii. Key results

- `CentralForce.poissonBracket_angularMomentum_angularMomentum` : `{L_a, L_b} = L_{a × b}`.
- `CentralForce.poissonBracket_lrlVector_angularMomentum` : `{A_a, L_b} = A_{a × b}`.
- `CentralForce.poissonBracket_lrlVector_lrlVector` : `{A_a, A_b} = -2 m H L_{a × b}`.
- `CentralForce.poissonBracket_scaledLrlVector_scaledLrlVector` : `{M_a, M_b} = L_{a × b}`.
- `CentralForce.poissonBracket_jPlus_jPlus`, `CentralForce.poissonBracket_jMinus_jMinus`,
  `CentralForce.poissonBracket_jPlus_jMinus` : `so(4) ≅ so(3) ⊕ so(3)`.
- `CentralForce.norm_jPlus_sq`, `CentralForce.norm_jMinus_sq` : `‖J±‖² = -m k² / (8 H)`.

## iii. Table of contents

- A. Preliminaries
  - A.1. The cross product
  - A.2. A chain rule for the Poisson bracket
- B. Gradients of the components
- C. The Poisson algebra of `L`, `A` and `H`
- D. The rescaled Laplace–Runge–Lenz vector
- E. The `so(4)` algebra
- F. The Casimirs

## iv. References

* W. Pauli, *Über das Wasserstoffspektrum vom Standpunkt der neuen Quantenmechanik*,
  Z. Phys. 36 (1926), 336–363.
* H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, Sections 9.7–9.8.
* M. Bander and C. Itzykson, *Group theory and the hydrogen atom (I)*, Rev. Mod. Phys. 38 (1966),
  330–345.
-/

@[expose] public section

namespace ClassicalMechanics

namespace CentralForce

open InnerProductSpace Matrix

/-!

## A. Preliminaries

### A.1. The cross product

-/

/-- The cross product `a × b` on `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def euclideanCross (a b : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (a.ofLp ⨯₃ b.ofLp)

/-- The cross product is antisymmetric. -/
lemma euclideanCross_anticomm (a b : EuclideanSpace ℝ (Fin 3)) :
    euclideanCross b a = -euclideanCross a b := by
  ext i
  fin_cases i <;> simp [euclideanCross, cross_apply] <;> ring

/-- The Binet–Cauchy identity `⟪a × b, q × p⟫ = ⟪a, q⟫ ⟪b, p⟫ - ⟪a, p⟫ ⟪b, q⟫`. -/
lemma inner_euclideanCross_angularMomentum (a b p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪euclideanCross a b, angularMomentum p q⟫_ℝ = ⟪a, q⟫_ℝ * ⟪b, p⟫_ℝ - ⟪a, p⟫_ℝ * ⟪b, q⟫_ℝ := by
  simp [euclideanCross, angularMomentum, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-!

### A.2. A chain rule for the Poisson bracket

-/

/-- The chain rule `{φ ∘ f, g} = φ'(f) {f, g}` for the Poisson bracket. -/
lemma poissonBracket_comp_left {φ : ℝ → ℝ} {φ' : ℝ}
    {f g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {p q : EuclideanSpace ℝ (Fin 3)} (hφ : HasDerivAt φ φ' (f p q))
    (hfp : DifferentiableAt ℝ (fun p' => f p' q) p)
    (hfq : DifferentiableAt ℝ (fun q' => f p q') q) :
    poissonBracket (fun p' q' => φ (f p' q')) g p q = φ' * poissonBracket f g p q := by
  simp only [poissonBracket]
  rw [(hφ.comp_hasGradientAt hfq.hasGradientAt).gradient,
    (hφ.comp_hasGradientAt hfp.hasGradientAt).gradient]
  simp only [real_inner_smul_left]
  ring

/-- The Poisson bracket of `(f₁ + s f₂) / 2` and `(g₁ + t g₂) / 2`, expanded bilinearly. -/
lemma poissonBracket_half_add {f₁ f₂ g₁ g₂ : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) → ℝ}
    {p q : EuclideanSpace ℝ (Fin 3)} (s t : ℝ)
    (hf₁p : DifferentiableAt ℝ (fun p' => f₁ p' q) p)
    (hf₁q : DifferentiableAt ℝ (fun q' => f₁ p q') q)
    (hf₂p : DifferentiableAt ℝ (fun p' => f₂ p' q) p)
    (hf₂q : DifferentiableAt ℝ (fun q' => f₂ p q') q)
    (hg₁p : DifferentiableAt ℝ (fun p' => g₁ p' q) p)
    (hg₁q : DifferentiableAt ℝ (fun q' => g₁ p q') q)
    (hg₂p : DifferentiableAt ℝ (fun p' => g₂ p' q) p)
    (hg₂q : DifferentiableAt ℝ (fun q' => g₂ p q') q) :
    poissonBracket (fun p' q' => 1 / 2 * (f₁ p' q' + s * f₂ p' q'))
      (fun p' q' => 1 / 2 * (g₁ p' q' + t * g₂ p' q')) p q =
      1 / 4 * (poissonBracket f₁ g₁ p q + t * poissonBracket f₁ g₂ p q +
        s * poissonBracket f₂ g₁ p q + s * t * poissonBracket f₂ g₂ p q) := by
  rw [poissonBracket_eq_of_hasGradientAt
    ((hf₁p.hasGradientAt.add (hf₂p.hasGradientAt.const_mul s)).const_mul (1 / 2))
    ((hf₁q.hasGradientAt.add (hf₂q.hasGradientAt.const_mul s)).const_mul (1 / 2))
    ((hg₁p.hasGradientAt.add (hg₂p.hasGradientAt.const_mul t)).const_mul (1 / 2))
    ((hg₁q.hasGradientAt.add (hg₂q.hasGradientAt.const_mul t)).const_mul (1 / 2))]
  simp only [poissonBracket, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-!

## B. Gradients of the components

-/

/-- The component of the Laplace–Runge–Lenz vector along `a` is
`⟪p, p⟫ ⟪a, q⟫ - ⟪q, p⟫ ⟪a, p⟫ - (m k / ‖q‖) ⟪a, q⟫`. -/
lemma inner_lrlVector_eq (m k : ℝ) (a p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪a, lrlVector m k p q⟫_ℝ =
      ⟪p, p⟫_ℝ * ⟪a, q⟫_ℝ - ⟪q, p⟫_ℝ * ⟪a, p⟫_ℝ - m * k / ‖q‖ * ⟪a, q⟫_ℝ := by
  simp only [lrlVector_eq, inner_sub_right, real_inner_smul_right]

/-- The momentum gradient of `L_a = ⟪a, q × p⟫` is `a × q`. -/
lemma hasGradientAt_inner_angularMomentum_momentum (a p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun p' => ⟪a, angularMomentum p' q⟫_ℝ) (euclideanCross a q) p := by
  have h : (fun p' => ⟪a, angularMomentum p' q⟫_ℝ) = fun p' => ⟪euclideanCross a q, p'⟫_ℝ := by
    funext p'
    simp [euclideanCross, angularMomentum, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  rw [h]
  exact hasGradientAt_inner_left _ p

/-- The position gradient of `L_a = ⟪a, q × p⟫` is `p × a`. -/
lemma hasGradientAt_inner_angularMomentum_position (a p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun q' => ⟪a, angularMomentum p q'⟫_ℝ) (euclideanCross p a) q := by
  have h : (fun q' => ⟪a, angularMomentum p q'⟫_ℝ) = fun q' => ⟪euclideanCross p a, q'⟫_ℝ := by
    funext q'
    simp [euclideanCross, angularMomentum, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  rw [h]
  exact hasGradientAt_inner_left _ q

/-- The momentum gradient of `A_a` is `2 ⟪a, q⟫ p - ⟪a, p⟫ q - ⟪q, p⟫ a`. -/
lemma hasGradientAt_inner_lrlVector_momentum (m k : ℝ) (a p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun p' => ⟪a, lrlVector m k p' q⟫_ℝ)
      ((2 * ⟪a, q⟫_ℝ) • p - ⟪a, p⟫_ℝ • q - ⟪q, p⟫_ℝ • a) p := by
  simp only [inner_lrlVector_eq]
  convert (((hasGradientAt_inner_self p).mul (hasGradientAt_const p ⟪a, q⟫_ℝ)).sub
    ((hasGradientAt_inner_left q p).mul (hasGradientAt_inner_left a p))).sub
    (hasGradientAt_const p (m * k / ‖q‖ * ⟪a, q⟫_ℝ)) using 1
  module

/-- Away from the centre of force, the position gradient of `A_a` is
`⟪p, p⟫ a - ⟪a, p⟫ p - (m k / ‖q‖) a + (m k ⟪a, q⟫ / ‖q‖³) q`. -/
lemma hasGradientAt_inner_lrlVector_position (m k : ℝ) (a p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    HasGradientAt (fun q' => ⟪a, lrlVector m k p q'⟫_ℝ)
      (⟪p, p⟫_ℝ • a - ⟪a, p⟫_ℝ • p - (m * k / ‖q‖) • a + (m * k * ⟪a, q⟫_ℝ / ‖q‖ ^ 3) • q) q := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hinv : HasGradientAt (fun q' : EuclideanSpace ℝ (Fin 3) => m * k / ‖q'‖)
      ((m * k * -(‖q‖ ^ 2)⁻¹) • (‖q‖⁻¹ • q)) q := by
    simp only [div_eq_mul_inv]
    exact HasDerivAt.comp_hasGradientAt (φ := fun r => m * k * r⁻¹) (hasGradientAt_norm hq)
      ((hasDerivAt_inv hq').const_mul (m * k))
  simp only [inner_lrlVector_eq]
  convert (((hasGradientAt_const q ⟪p, p⟫_ℝ).mul (hasGradientAt_inner_left a q)).sub
    ((hasGradientAt_inner_right p q).mul (hasGradientAt_const q ⟪a, p⟫_ℝ))).sub
    (hinv.mul (hasGradientAt_inner_left a q)) using 1
  simp only [smul_zero, add_zero, zero_add, smul_smul]
  field_simp
  module

/-!

## C. The Poisson algebra of `L`, `A` and `H`

-/

/-- The angular momentum generates rotations: `{L_a, L_b} = L_{a × b}`. -/
lemma poissonBracket_angularMomentum_angularMomentum (a b p q : EuclideanSpace ℝ (Fin 3)) :
    poissonBracket (fun p q => ⟪a, angularMomentum p q⟫_ℝ)
      (fun p q => ⟪b, angularMomentum p q⟫_ℝ) p q =
      ⟪euclideanCross a b, angularMomentum p q⟫_ℝ := by
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_inner_angularMomentum_momentum a p q)
    (hasGradientAt_inner_angularMomentum_position a p q)
    (hasGradientAt_inner_angularMomentum_momentum b p q)
    (hasGradientAt_inner_angularMomentum_position b p q)]
  simp [euclideanCross, angularMomentum, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- Away from the centre of force, the Laplace–Runge–Lenz vector transforms as a vector under
rotations: `{A_a, L_b} = A_{a × b}`. -/
lemma poissonBracket_lrlVector_angularMomentum (m k : ℝ) (a b p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (fun p q => ⟪a, lrlVector m k p q⟫_ℝ)
      (fun p q => ⟪b, angularMomentum p q⟫_ℝ) p q =
      ⟪euclideanCross a b, lrlVector m k p q⟫_ℝ := by
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_inner_lrlVector_momentum m k a p q)
    (hasGradientAt_inner_lrlVector_position m k a p hq)
    (hasGradientAt_inner_angularMomentum_momentum b p q)
    (hasGradientAt_inner_angularMomentum_position b p q), inner_lrlVector_eq]
  simp [euclideanCross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- Away from the centre of force, `{A_a, A_b} = -2 m H L_{a × b}`. -/
lemma poissonBracket_lrlVector_lrlVector (m k : ℝ) (hm : 0 < m) (a b p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (fun p q => ⟪a, lrlVector m k p q⟫_ℝ)
      (fun p q => ⟪b, lrlVector m k p q⟫_ℝ) p q =
      -2 * m * (kepler m k hm).hamiltonian p q * ⟪euclideanCross a b, angularMomentum p q⟫_ℝ := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_inner_lrlVector_momentum m k a p q)
    (hasGradientAt_inner_lrlVector_position m k a p hq)
    (hasGradientAt_inner_lrlVector_momentum m k b p q)
    (hasGradientAt_inner_lrlVector_position m k b p hq),
    inner_euclideanCross_angularMomentum, kepler_hamiltonian]
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
  field_simp
  ring

/-- For any central force, `{L_a, H} = 0`: every component of the angular momentum is
conserved. -/
lemma poissonBracket_angularMomentum_hamiltonian (S : CentralForce)
    (a p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (fun p q => ⟪a, angularMomentum p q⟫_ℝ) S.hamiltonian p q = 0 := by
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_inner_angularMomentum_momentum a p q)
    (hasGradientAt_inner_angularMomentum_position a p q) (S.hasGradientAt_hamiltonian_momentum p q)
    (S.hasGradientAt_hamiltonian_position p hq)]
  simp [euclideanCross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- Away from the centre of force, `{A_a, H} = 0` for the Kepler problem. -/
lemma poissonBracket_inner_lrlVector_hamiltonian (m k : ℝ) (hm : 0 < m)
    (a p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (fun p q => ⟪a, lrlVector m k p q⟫_ℝ) (kepler m k hm).hamiltonian p q = 0 := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hH := (kepler m k hm).hasGradientAt_hamiltonian_position p hq
  rw [kepler_deriv_V m k hm hq'] at hH
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_inner_lrlVector_momentum m k a p q)
    (hasGradientAt_inner_lrlVector_position m k a p hq)
    ((kepler m k hm).hasGradientAt_hamiltonian_momentum p q) hH]
  simp only [kepler, inner_sub_left, inner_add_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm]
  field_simp
  ring

/-!

## D. The rescaled Laplace–Runge–Lenz vector

-/

/-- The scale factor `1 / √(-2 m E)` as a function of the energy `E`. -/
noncomputable def lrlScale (m E : ℝ) : ℝ := (Real.sqrt (-2 * m * E))⁻¹

/-- The scale factor is differentiable at every negative energy. -/
lemma hasDerivAt_lrlScale {m E : ℝ} (hm : 0 < m) (hE : E < 0) :
    HasDerivAt (lrlScale m) (deriv (lrlScale m) E) E := by
  have hpos : 0 < -2 * m * E := by nlinarith
  have hs : Real.sqrt (-2 * m * E) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  exact ((((hasDerivAt_id E).const_mul (-2 * m)).sqrt (by simpa using hpos.ne')).inv
    (by simpa using hs)).differentiableAt.hasDerivAt

/-- At a negative energy `E`, the scale factor satisfies `lrlScale m E ^ 2 * (-2 m E) = 1`. -/
lemma lrlScale_sq {m E : ℝ} (hm : 0 < m) (hE : E < 0) :
    lrlScale m E ^ 2 * (-2 * m * E) = 1 := by
  have hpos : 0 < -2 * m * E := by nlinarith
  rw [lrlScale, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- On the bound region `H < 0`, the rescaled Laplace–Runge–Lenz vector `M = A / √(-2 m H)`. -/
noncomputable def scaledLrlVector (m k : ℝ) (hm : 0 < m) (p q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  lrlScale m ((kepler m k hm).hamiltonian p q) • lrlVector m k p q

/-- The component `M_a` is the scale factor times `A_a`. -/
lemma inner_scaledLrlVector (m k : ℝ) (hm : 0 < m) (a : EuclideanSpace ℝ (Fin 3)) :
    (fun p q => ⟪a, scaledLrlVector m k hm p q⟫_ℝ) =
      fun p q => lrlScale m ((kepler m k hm).hamiltonian p q) * ⟪a, lrlVector m k p q⟫_ℝ := by
  funext p q
  rw [scaledLrlVector, real_inner_smul_right]

section differentiability

variable (m k : ℝ) (hm : 0 < m) (a p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)}

/-- On the bound region, the scale factor is differentiable in the momentum. -/
lemma differentiableAt_lrlScale_momentum
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    DifferentiableAt ℝ (fun p' => lrlScale m ((kepler m k hm).hamiltonian p' q)) p :=
  ((hasDerivAt_lrlScale hm hH).comp_hasGradientAt
    ((kepler m k hm).hasGradientAt_hamiltonian_momentum p q)).differentiableAt

/-- On the bound region, the scale factor is differentiable in the position. -/
lemma differentiableAt_lrlScale_position (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    DifferentiableAt ℝ (fun q' => lrlScale m ((kepler m k hm).hamiltonian p q')) q :=
  ((hasDerivAt_lrlScale hm hH).comp_hasGradientAt
    ((kepler m k hm).hasGradientAt_hamiltonian_position p hq)).differentiableAt

/-- On the bound region, `M_a` is differentiable in the momentum. -/
lemma differentiableAt_scaledLrlVector_momentum
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    DifferentiableAt ℝ (fun p' => ⟪a, scaledLrlVector m k hm p' q⟫_ℝ) p := by
  simp only [scaledLrlVector, real_inner_smul_right]
  exact (differentiableAt_lrlScale_momentum m k hm p hH).mul
    (hasGradientAt_inner_lrlVector_momentum m k a p q).differentiableAt

/-- On the bound region, `M_a` is differentiable in the position. -/
lemma differentiableAt_scaledLrlVector_position (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    DifferentiableAt ℝ (fun q' => ⟪a, scaledLrlVector m k hm p q'⟫_ℝ) q := by
  simp only [scaledLrlVector, real_inner_smul_right]
  exact (differentiableAt_lrlScale_position m k hm p hq hH).mul
    (hasGradientAt_inner_lrlVector_position m k a p hq).differentiableAt

end differentiability

/-- On the bound region, `{M_a, M_b} = L_{a × b}`. -/
lemma poissonBracket_scaledLrlVector_scaledLrlVector (m k : ℝ) (hm : 0 < m)
    (a b p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    poissonBracket (fun p q => ⟪a, scaledLrlVector m k hm p q⟫_ℝ)
      (fun p q => ⟪b, scaledLrlVector m k hm p q⟫_ℝ) p q =
      ⟪euclideanCross a b, angularMomentum p q⟫_ℝ := by
  have hHp := ((kepler m k hm).hasGradientAt_hamiltonian_momentum p q).differentiableAt
  have hHq := ((kepler m k hm).hasGradientAt_hamiltonian_position p hq).differentiableAt
  have hcp := differentiableAt_lrlScale_momentum m k hm p hH
  have hcq := differentiableAt_lrlScale_position m k hm p hq hH
  have hAp (c) := (hasGradientAt_inner_lrlVector_momentum m k c p q).differentiableAt
  have hAq (c) := (hasGradientAt_inner_lrlVector_position m k c p hq).differentiableAt
  have hcA (c) : poissonBracket (fun p q => lrlScale m ((kepler m k hm).hamiltonian p q))
      (fun p q => ⟪c, lrlVector m k p q⟫_ℝ) p q = 0 := by
    rw [poissonBracket_comp_left (hasDerivAt_lrlScale hm hH) hHp hHq, poissonBracket_antisymm,
      poissonBracket_inner_lrlVector_hamiltonian m k hm c p hq]
    ring
  rw [inner_scaledLrlVector, inner_scaledLrlVector,
    poissonBracket_mul_left _ _ _ p q hcp (hAp a) hcq (hAq a),
    poissonBracket_mul_right _ _ _ p q hcp (hAp b) hcq (hAq b),
    poissonBracket_mul_right _ _ _ p q hcp (hAp b) hcq (hAq b),
    poissonBracket_self, hcA, poissonBracket_antisymm (fun p q => ⟪a, lrlVector m k p q⟫_ℝ), hcA,
    poissonBracket_lrlVector_lrlVector m k hm a b p hq]
  linear_combination ⟪euclideanCross a b, angularMomentum p q⟫_ℝ * lrlScale_sq hm hH

/-- On the bound region, `{M_a, L_b} = M_{a × b}`. -/
lemma poissonBracket_scaledLrlVector_angularMomentum (m k : ℝ) (hm : 0 < m)
    (a b p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    poissonBracket (fun p q => ⟪a, scaledLrlVector m k hm p q⟫_ℝ)
      (fun p q => ⟪b, angularMomentum p q⟫_ℝ) p q =
      ⟪euclideanCross a b, scaledLrlVector m k hm p q⟫_ℝ := by
  have hHp := ((kepler m k hm).hasGradientAt_hamiltonian_momentum p q).differentiableAt
  have hHq := ((kepler m k hm).hasGradientAt_hamiltonian_position p hq).differentiableAt
  rw [inner_scaledLrlVector,
    poissonBracket_mul_left _ _ _ p q (differentiableAt_lrlScale_momentum m k hm p hH)
      (hasGradientAt_inner_lrlVector_momentum m k a p q).differentiableAt
      (differentiableAt_lrlScale_position m k hm p hq hH)
      (hasGradientAt_inner_lrlVector_position m k a p hq).differentiableAt,
    poissonBracket_comp_left (hasDerivAt_lrlScale hm hH) hHp hHq, poissonBracket_antisymm,
    poissonBracket_angularMomentum_hamiltonian _ b p hq,
    poissonBracket_lrlVector_angularMomentum m k a b p hq, scaledLrlVector, real_inner_smul_right]
  ring

/-- On the bound region, `{L_a, M_b} = M_{a × b}`. -/
lemma poissonBracket_angularMomentum_scaledLrlVector (m k : ℝ) (hm : 0 < m)
    (a b p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    poissonBracket (fun p q => ⟪a, angularMomentum p q⟫_ℝ)
      (fun p q => ⟪b, scaledLrlVector m k hm p q⟫_ℝ) p q =
      ⟪euclideanCross a b, scaledLrlVector m k hm p q⟫_ℝ := by
  rw [poissonBracket_antisymm, poissonBracket_scaledLrlVector_angularMomentum m k hm b a p hq hH,
    euclideanCross_anticomm, inner_neg_left, neg_neg]

/-!

## E. The `so(4)` algebra

-/

/-- On the bound region, `J₊ = (L + M) / 2`. -/
noncomputable def jPlus (m k : ℝ) (hm : 0 < m) (p q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  (1 / 2 : ℝ) • (angularMomentum p q + scaledLrlVector m k hm p q)

/-- On the bound region, `J₋ = (L - M) / 2`. -/
noncomputable def jMinus (m k : ℝ) (hm : 0 < m) (p q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  (1 / 2 : ℝ) • (angularMomentum p q - scaledLrlVector m k hm p q)

/-- The component `J₊_a` is `(L_a + M_a) / 2`. -/
lemma inner_jPlus (m k : ℝ) (hm : 0 < m) (a : EuclideanSpace ℝ (Fin 3)) :
    (fun p q => ⟪a, jPlus m k hm p q⟫_ℝ) = fun p q =>
      1 / 2 * (⟪a, angularMomentum p q⟫_ℝ + 1 * ⟪a, scaledLrlVector m k hm p q⟫_ℝ) := by
  funext p q
  rw [jPlus, real_inner_smul_right, inner_add_right, one_mul]

/-- The component `J₋_a` is `(L_a - M_a) / 2`. -/
lemma inner_jMinus (m k : ℝ) (hm : 0 < m) (a : EuclideanSpace ℝ (Fin 3)) :
    (fun p q => ⟪a, jMinus m k hm p q⟫_ℝ) = fun p q =>
      1 / 2 * (⟪a, angularMomentum p q⟫_ℝ + -1 * ⟪a, scaledLrlVector m k hm p q⟫_ℝ) := by
  funext p q
  rw [jMinus, real_inner_smul_right, inner_sub_right]
  ring

/-- The Poisson brackets of `(L_a + s M_a) / 2` and `(L_b + t M_b) / 2` on the bound region. -/
lemma poissonBracket_half_angularMomentum_add_scaledLrlVector (m k : ℝ) (hm : 0 < m) (s t : ℝ)
    (a b p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    poissonBracket
      (fun p q => 1 / 2 * (⟪a, angularMomentum p q⟫_ℝ + s * ⟪a, scaledLrlVector m k hm p q⟫_ℝ))
      (fun p q => 1 / 2 * (⟪b, angularMomentum p q⟫_ℝ + t * ⟪b, scaledLrlVector m k hm p q⟫_ℝ))
      p q = 1 / 4 * ((1 + s * t) * ⟪euclideanCross a b, angularMomentum p q⟫_ℝ +
        (s + t) * ⟪euclideanCross a b, scaledLrlVector m k hm p q⟫_ℝ) := by
  rw [poissonBracket_half_add s t
    (hasGradientAt_inner_angularMomentum_momentum a p q).differentiableAt
    (hasGradientAt_inner_angularMomentum_position a p q).differentiableAt
    (differentiableAt_scaledLrlVector_momentum m k hm a p hH)
    (differentiableAt_scaledLrlVector_position m k hm a p hq hH)
    (hasGradientAt_inner_angularMomentum_momentum b p q).differentiableAt
    (hasGradientAt_inner_angularMomentum_position b p q).differentiableAt
    (differentiableAt_scaledLrlVector_momentum m k hm b p hH)
    (differentiableAt_scaledLrlVector_position m k hm b p hq hH),
    poissonBracket_angularMomentum_angularMomentum,
    poissonBracket_angularMomentum_scaledLrlVector m k hm a b p hq hH,
    poissonBracket_scaledLrlVector_angularMomentum m k hm a b p hq hH,
    poissonBracket_scaledLrlVector_scaledLrlVector m k hm a b p hq hH]
  ring

/-- On the bound region, `{J₊_a, J₊_b} = J₊_{a × b}`. -/
lemma poissonBracket_jPlus_jPlus (m k : ℝ) (hm : 0 < m) (a b p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) (hH : (kepler m k hm).hamiltonian p q < 0) :
    poissonBracket (fun p q => ⟪a, jPlus m k hm p q⟫_ℝ) (fun p q => ⟪b, jPlus m k hm p q⟫_ℝ) p q =
      ⟪euclideanCross a b, jPlus m k hm p q⟫_ℝ := by
  rw [inner_jPlus, inner_jPlus,
    poissonBracket_half_angularMomentum_add_scaledLrlVector m k hm 1 1 a b p hq hH,
    jPlus, real_inner_smul_right, inner_add_right]
  ring

/-- On the bound region, `{J₋_a, J₋_b} = J₋_{a × b}`. -/
lemma poissonBracket_jMinus_jMinus (m k : ℝ) (hm : 0 < m) (a b p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) (hH : (kepler m k hm).hamiltonian p q < 0) :
    poissonBracket (fun p q => ⟪a, jMinus m k hm p q⟫_ℝ)
      (fun p q => ⟪b, jMinus m k hm p q⟫_ℝ) p q =
      ⟪euclideanCross a b, jMinus m k hm p q⟫_ℝ := by
  rw [inner_jMinus, inner_jMinus,
    poissonBracket_half_angularMomentum_add_scaledLrlVector m k hm (-1) (-1) a b p hq hH,
    jMinus, real_inner_smul_right, inner_sub_right]
  ring

/-- On the bound region, `{J₊_a, J₋_b} = 0`: the two copies of `so(3)` commute. -/
lemma poissonBracket_jPlus_jMinus (m k : ℝ) (hm : 0 < m) (a b p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) (hH : (kepler m k hm).hamiltonian p q < 0) :
    poissonBracket (fun p q => ⟪a, jPlus m k hm p q⟫_ℝ)
      (fun p q => ⟪b, jMinus m k hm p q⟫_ℝ) p q = 0 := by
  rw [inner_jPlus, inner_jMinus,
    poissonBracket_half_angularMomentum_add_scaledLrlVector m k hm 1 (-1) a b p hq hH]
  ring

/-!

## F. The Casimirs

-/

/-- The rescaled Laplace–Runge–Lenz vector is orthogonal to the angular momentum. -/
lemma inner_scaledLrlVector_angularMomentum (m k : ℝ) (hm : 0 < m)
    (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪scaledLrlVector m k hm p q, angularMomentum p q⟫_ℝ = 0 := by
  rw [scaledLrlVector, real_inner_smul_left, inner_lrlVector_angularMomentum, mul_zero]

/-- On the bound region, `‖L‖² + ‖M‖² = -m k² / (2 H)`. -/
lemma norm_angularMomentum_sq_add_norm_scaledLrlVector_sq (m k : ℝ) (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    ‖angularMomentum p q‖ ^ 2 + ‖scaledLrlVector m k hm p q‖ ^ 2 =
      -(m * k ^ 2) / (2 * (kepler m k hm).hamiltonian p q) := by
  have h := lrlScale_sq hm hH
  rw [scaledLrlVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_lrlVector_sq m k hm p hq, angularMomentumSq, eq_div_iff (by linarith)]
  linear_combination (-(m * k ^ 2) - 2 * (kepler m k hm).hamiltonian p q *
    ‖angularMomentum p q‖ ^ 2) * h

/-- On the bound region, the `so(3)` Casimir of `J₊` is `‖J₊‖² = -m k² / (8 H)`. -/
lemma norm_jPlus_sq (m k : ℝ) (hm : 0 < m) (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) (hH : (kepler m k hm).hamiltonian p q < 0) :
    ‖jPlus m k hm p q‖ ^ 2 = -(m * k ^ 2) / (8 * (kepler m k hm).hamiltonian p q) := by
  have h := norm_angularMomentum_sq_add_norm_scaledLrlVector_sq m k hm p hq hH
  have hH0 : (kepler m k hm).hamiltonian p q ≠ 0 := hH.ne
  rw [jPlus, norm_smul, mul_pow, norm_add_sq_real, real_inner_comm,
    inner_scaledLrlVector_angularMomentum, mul_zero, add_zero, h]
  norm_num
  field_simp
  ring

/-- On the bound region, the `so(3)` Casimir of `J₋` is `‖J₋‖² = -m k² / (8 H)`. -/
lemma norm_jMinus_sq (m k : ℝ) (hm : 0 < m) (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) (hH : (kepler m k hm).hamiltonian p q < 0) :
    ‖jMinus m k hm p q‖ ^ 2 = -(m * k ^ 2) / (8 * (kepler m k hm).hamiltonian p q) := by
  have h := norm_angularMomentum_sq_add_norm_scaledLrlVector_sq m k hm p hq hH
  have hH0 : (kepler m k hm).hamiltonian p q ≠ 0 := hH.ne
  rw [jMinus, norm_smul, mul_pow, norm_sub_sq_real, real_inner_comm,
    inner_scaledLrlVector_angularMomentum, mul_zero, sub_zero, h]
  norm_num
  field_simp
  ring

/-- On the bound region, the energy is determined by the `so(4)` Casimir:
`H = -m k² / (8 ‖J₊‖²)`. -/
lemma hamiltonian_eq_of_norm_jPlus (m k : ℝ) (hm : 0 < m) (hk : k ≠ 0)
    (p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0)
    (hH : (kepler m k hm).hamiltonian p q < 0) :
    (kepler m k hm).hamiltonian p q = -(m * k ^ 2) / (8 * ‖jPlus m k hm p q‖ ^ 2) := by
  have h := norm_jPlus_sq m k hm p hq hH
  have hJ : ‖jPlus m k hm p q‖ ^ 2 ≠ 0 := by
    rw [h]
    exact div_ne_zero (by simp [hm.ne', hk]) (by linarith)
  rw [h]
  field_simp

end CentralForce

end ClassicalMechanics
