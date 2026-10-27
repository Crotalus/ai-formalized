/-
Copyright (c) 2026 Nichlas Lofdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Lofdahl
-/
module

public import PhyslibAlpha.ClassicalMechanics.CentralForce.AngularMomentum
/-!

# The Kepler problem

The inverse-square central force, its Laplace–Runge–Lenz vector, and the conic orbit equation.

## i. Overview

The Kepler problem is the central-force system with potential `V r = -k / r`. Besides the energy
and the angular momentum `L = q × p`, it conserves the Laplace–Runge–Lenz (LRL) vector

$$A = p × L - \frac{m k}{\|q\|} q.$$

The LRL vector is orthogonal to `L`, so it lies in the orbital plane, and its inner product with
the position gives the orbit equation `⟪A, q⟫ = ‖L‖² - m k ‖q‖`. Writing `θ` for the angle between
`A` and `q`, this is the conic `‖q‖ = (‖L‖² / (m k)) / (1 + e cos θ)` with eccentricity
`e = ‖A‖ / (m k)`. The relation `‖A‖² = (m k)² + 2 m H ‖L‖²` then shows that bound orbits
(`H < 0`) are ellipses (`e < 1`).

## ii. Key results

- `CentralForce.kepler` : the Kepler problem as a central-force system.
- `CentralForce.lrlVector` : the Laplace–Runge–Lenz vector.
- `CentralForce.inner_lrlVector_position` : the orbit equation `⟪A, q⟫ = ‖L‖² - m k ‖q‖`.
- `CentralForce.norm_lrlVector_sq` : `‖A‖² = (m k)² + 2 m H ‖L‖²`.
- `CentralForce.poissonBracket_lrlVector_hamiltonian` : the LRL vector is conserved.
- `CentralForce.inner_lrlVector_position_of_hamiltonEqOp` : Kepler's first law along a solution of
  Hamilton's equations.

## iii. Table of contents

- A. The Kepler problem
- B. The Laplace–Runge–Lenz vector
  - B.1. Algebraic identities
  - B.2. The orbit equation and the eccentricity
- C. Conservation of the Laplace–Runge–Lenz vector
  - C.1. Gradients
  - C.2. Poisson bracket with the Hamiltonian
- D. Motion along a trajectory

## iv. References

* H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, Section 3.9.
-/

@[expose] public section

namespace ClassicalMechanics

namespace CentralForce

open InnerProductSpace Matrix
open scoped ContDiff

/-!

## A. The Kepler problem

-/

/-- The Kepler problem: a particle of mass `m` in the inverse-square potential `V r = -k / r`.
The force is attractive for `k > 0`. -/
noncomputable def kepler (m k : ℝ) (hm : 0 < m) : CentralForce where
  m := m
  V := fun r => -k / r
  m_pos := hm
  contDiffOn_V := contDiffOn_const.div contDiffOn_id fun _ hr => (Set.mem_Ioi.mp hr).ne'

/-- The Hamiltonian of the Kepler problem is `⟪p, p⟫ / (2 m) - k / ‖q‖`. -/
lemma kepler_hamiltonian (m k : ℝ) (hm : 0 < m) (p q : EuclideanSpace ℝ (Fin 3)) :
    (kepler m k hm).hamiltonian p q = (1 / (2 * m)) * ⟪p, p⟫_ℝ - k / ‖q‖ := by
  simp only [hamiltonian, kepler]
  ring

/-- Away from the origin, the derivative of the Kepler potential `V r = -k / r` is `k / r²`. -/
lemma kepler_deriv_V (m k : ℝ) (hm : 0 < m) {r : ℝ} (hr : r ≠ 0) :
    deriv (kepler m k hm).V r = k / r ^ 2 := by
  show deriv (fun r => -k / r) r = _
  simp only [div_eq_mul_inv]
  rw [((hasDerivAt_inv hr).const_mul (-k)).deriv]
  ring

/-!

## B. The Laplace–Runge–Lenz vector

-/

/-- The Laplace–Runge–Lenz vector `A = p × L - (m k / ‖q‖) q` of the Kepler problem with mass `m`
and coupling `k`, as a function on phase space. -/
noncomputable def lrlVector (m k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (p.ofLp ⨯₃ (angularMomentum p q).ofLp) - (m * k / ‖q‖) • q

/-!

### B.1. Algebraic identities

-/

/-- Expanding the triple product, `A = ⟪p, p⟫ q - ⟪q, p⟫ p - (m k / ‖q‖) q`. -/
lemma lrlVector_eq (m k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    lrlVector m k p q = ⟪p, p⟫_ℝ • q - ⟪q, p⟫_ℝ • p - (m * k / ‖q‖) • q := by
  ext i
  fin_cases i <;>
  simp [lrlVector, angularMomentum, cross_apply, PiLp.inner_apply, Fin.sum_univ_three,
    EuclideanSpace.norm_sq_eq] <;> ring

/-- The Laplace–Runge–Lenz vector is orthogonal to the angular momentum, so lies in the orbital
plane. -/
lemma inner_lrlVector_angularMomentum (m k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪lrlVector m k p q, angularMomentum p q⟫_ℝ = 0 := by
  simp [lrlVector_eq, angularMomentum, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-!

### B.2. The orbit equation and the eccentricity

-/

/-- The orbit equation `⟪A, q⟫ = ‖L‖² - m k ‖q‖`. Along a trajectory `A` and `‖L‖²` are
constant, so this is the polar equation of a conic with focus at the centre of force. -/
lemma inner_lrlVector_position (m k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪lrlVector m k p q, q⟫_ℝ = angularMomentumSq p q - m * k * ‖q‖ := by
  rw [lrlVector_eq, angularMomentumSq_eq]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm p q]
  rcases eq_or_ne ‖q‖ 0 with hq | hq
  · simp [hq]
    ring
  · field_simp

/-- The squared magnitude of the Laplace–Runge–Lenz vector is `(m k)² + 2 m H ‖L‖²`. -/
lemma norm_lrlVector_sq (m k : ℝ) (hm : 0 < m) (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    ‖lrlVector m k p q‖ ^ 2 =
      (m * k) ^ 2 + 2 * m * (kepler m k hm).hamiltonian p q * angularMomentumSq p q := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [← real_inner_self_eq_norm_sq, lrlVector_eq, kepler_hamiltonian, angularMomentumSq_eq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, real_inner_comm p q]
  field_simp
  ring

/-- For an attractive force and non-zero angular momentum, the eccentricity `‖A‖ / (m k)` is less
than one exactly when the energy is negative: bound orbits are ellipses. -/
lemma norm_lrlVector_lt_iff (m k : ℝ) (hm : 0 < m) (hk : 0 < k) (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) (hL : angularMomentumSq p q ≠ 0) :
    ‖lrlVector m k p q‖ < m * k ↔ (kepler m k hm).hamiltonian p q < 0 := by
  have hL' : 0 < angularMomentumSq p q :=
    lt_of_le_of_ne (by unfold angularMomentumSq; positivity) (Ne.symm hL)
  rw [← sq_lt_sq₀ (norm_nonneg _) (mul_pos hm hk).le, norm_lrlVector_sq m k hm p hq]
  constructor <;> intro h <;> nlinarith [mul_pos hm hL']

/-!

## C. Conservation of the Laplace–Runge–Lenz vector

-/

/-!

### C.1. Gradients

-/

/-- The momentum gradient of the component `A i` is `2 qᵢ p - pᵢ q - ⟪q, p⟫ eᵢ`. -/
lemma hasGradientAt_lrlVector_momentum (m k : ℝ) (i : Fin 3) (p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun p' => lrlVector m k p' q i)
      ((2 * q i) • p - p i • q - ⟪q, p⟫_ℝ • EuclideanSpace.single i 1) p := by
  simp only [lrlVector_eq, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  convert (((hasGradientAt_inner_self p).mul (hasGradientAt_const p (q i))).sub
    ((hasGradientAt_inner_left q p).mul (hasGradientAt_coord i p))).sub
    (hasGradientAt_const p (m * k / ‖q‖ * q i)) using 1
  module

/-- Away from the centre of force, the position gradient of the component `A i` is
`⟪p, p⟫ eᵢ - pᵢ p - (m k / ‖q‖) eᵢ + (m k qᵢ / ‖q‖³) q`. -/
lemma hasGradientAt_lrlVector_position (m k : ℝ) (i : Fin 3) (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    HasGradientAt (fun q' => lrlVector m k p q' i)
      (⟪p, p⟫_ℝ • EuclideanSpace.single i 1 - p i • p - (m * k / ‖q‖) • EuclideanSpace.single i 1
        + (m * k * q i / ‖q‖ ^ 3) • q) q := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hinv : HasGradientAt (fun q' : EuclideanSpace ℝ (Fin 3) => m * k / ‖q'‖)
      ((m * k * -(‖q‖ ^ 2)⁻¹) • (‖q‖⁻¹ • q)) q := by
    simp only [div_eq_mul_inv]
    exact HasDerivAt.comp_hasGradientAt (φ := fun r => m * k * r⁻¹) (hasGradientAt_norm hq)
      ((hasDerivAt_inv hq').const_mul (m * k))
  simp only [lrlVector_eq, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  convert (((hasGradientAt_const q ⟪p, p⟫_ℝ).mul (hasGradientAt_coord i q)).sub
    ((hasGradientAt_inner_right p q).mul (hasGradientAt_const q (p i)))).sub
    (hinv.mul (hasGradientAt_coord i q)) using 1
  simp only [smul_zero, add_zero, zero_add, smul_smul]
  field_simp
  module

/-!

### C.2. Poisson bracket with the Hamiltonian

-/

/-- Away from the centre of force, every component of the Laplace–Runge–Lenz vector
Poisson-commutes with the Kepler Hamiltonian, so the LRL vector is conserved by the motion. -/
lemma poissonBracket_lrlVector_hamiltonian (m k : ℝ) (hm : 0 < m) (i : Fin 3)
    (p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (fun p' q' => lrlVector m k p' q' i) (kepler m k hm).hamiltonian p q = 0 := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hH := (kepler m k hm).hasGradientAt_hamiltonian_position p hq
  rw [kepler_deriv_V m k hm hq'] at hH
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_lrlVector_momentum m k i p q)
    (hasGradientAt_lrlVector_position m k i p hq)
    ((kepler m k hm).hasGradientAt_hamiltonian_momentum p q) hH]
  simp only [kepler, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul, real_inner_self_eq_norm_sq,
    real_inner_comm p q]
  field_simp
  ring

/-!

## D. Motion along a trajectory

-/

open Time in
/-- A phase-space observable which Poisson-commutes with a time-independent Hamiltonian along a
solution of Hamilton's equations is constant along that solution. -/
lemma eq_of_poissonBracket_eq_zero {H f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {p q : Time → EuclideanSpace ℝ (Fin 3)} (heq : hamiltonEqOp (fun _ => H) p q = 0)
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q)
    (hf : ∀ t, DifferentiableAt ℝ (Function.uncurry f) (p t, q t))
    (hpb : ∀ t, poissonBracket f H (p t) (q t) = 0) (t s : Time) :
    f (p t) (q t) = f (p s) (q s) := by
  have hd (τ : ℝ) : HasDerivAt (fun σ : ℝ => f (p ⟨σ⟩) (q ⟨σ⟩)) 0 τ := by
    have hdiff : DifferentiableAt ℝ (Function.uncurry f ∘ fun t => (p t, q t)) (⟨τ⟩ : Time) :=
      DifferentiableAt.comp (f := fun t : Time => (p t, q t)) _ (hf ⟨τ⟩) ((hp _).prodMk (hq _))
    have h := hasDerivAt_mk_of_differentiableAt (f := fun t => f (p t) (q t)) hdiff
    rwa [(deriv_comp_eq_poissonBracket (fun _ => H) p q f ⟨τ⟩ heq (hp _) (hq _) (hf _)).trans
      (hpb _)] at h
  exact is_const_of_deriv_eq_zero (fun τ => (hd τ).differentiableAt)
    (fun τ => (hd τ).deriv) t.val s.val

/-- Away from the centre of force, each component of the Laplace–Runge–Lenz vector is
differentiable on phase space. -/
lemma differentiableAt_lrlVector (m k : ℝ) (i : Fin 3)
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} (hx : x.2 ≠ 0) :
    DifferentiableAt ℝ (Function.uncurry fun p q => lrlVector m k p q i) x := by
  have h : (Function.uncurry fun p q => lrlVector m k p q i) =
      fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ⟪x.1, x.1⟫_ℝ * x.2 i - ⟪x.2, x.1⟫_ℝ * x.1 i - m * k / ‖x.2‖ * x.2 i := by
    funext x
    simp only [Function.uncurry, lrlVector_eq, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [h]
  have c₁ : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      x.1 i) x := (hasGradientAt_coord i x.1).differentiableAt.comp x differentiableAt_fst
  have c₂ : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      x.2 i) x := (hasGradientAt_coord i x.2).differentiableAt.comp x differentiableAt_snd
  have hn := differentiableAt_snd.norm ℝ hx
  fun_prop (disch := exact norm_ne_zero_iff.mpr hx)

/-- Along a solution of Hamilton's equations for the Kepler problem which avoids the centre of
force, the Laplace–Runge–Lenz vector is constant. -/
lemma lrlVector_eq_of_hamiltonEqOp (m k : ℝ) (hm : 0 < m) {p q : Time → EuclideanSpace ℝ (Fin 3)}
    (heq : hamiltonEqOp (fun _ => (kepler m k hm).hamiltonian) p q = 0)
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) (hq0 : ∀ t, q t ≠ 0) (t s : Time) :
    lrlVector m k (p t) (q t) = lrlVector m k (p s) (q s) := by
  ext i
  exact eq_of_poissonBracket_eq_zero (f := fun p q => lrlVector m k p q i) heq hp hq
    (fun t => differentiableAt_lrlVector m k i (hq0 t))
    (fun t => poissonBracket_lrlVector_hamiltonian m k hm i (p t) (hq0 t)) t s

/-- Along a solution of Hamilton's equations for the Kepler problem which avoids the centre of
force, the squared angular momentum is constant. -/
lemma angularMomentumSq_eq_of_hamiltonEqOp (m k : ℝ) (hm : 0 < m)
    {p q : Time → EuclideanSpace ℝ (Fin 3)}
    (heq : hamiltonEqOp (fun _ => (kepler m k hm).hamiltonian) p q = 0)
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) (hq0 : ∀ t, q t ≠ 0) (t s : Time) :
    angularMomentumSq (p t) (q t) = angularMomentumSq (p s) (q s) :=
  eq_of_poissonBracket_eq_zero heq hp hq
    (fun _ => contDiff_angularMomentumSq.differentiable (by simp) _)
    (fun t => (kepler m k hm).poissonBracket_angularMomentumSq_hamiltonian (p t) (hq0 t)) t s

/-- Kepler's first law: along a solution of Hamilton's equations for the Kepler problem which
avoids the centre of force, the position satisfies `⟪A₀, q⟫ = ‖L₀‖² - m k ‖q‖` for the
Laplace–Runge–Lenz vector `A₀` and angular momentum `L₀` at any fixed time `t₀`. This is the
polar equation of a conic with a focus at the centre of force. -/
lemma inner_lrlVector_position_of_hamiltonEqOp (m k : ℝ) (hm : 0 < m)
    {p q : Time → EuclideanSpace ℝ (Fin 3)}
    (heq : hamiltonEqOp (fun _ => (kepler m k hm).hamiltonian) p q = 0)
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) (hq0 : ∀ t, q t ≠ 0) (t₀ t : Time) :
    ⟪lrlVector m k (p t₀) (q t₀), q t⟫_ℝ = angularMomentumSq (p t₀) (q t₀) - m * k * ‖q t‖ := by
  rw [lrlVector_eq_of_hamiltonEqOp m k hm heq hp hq hq0 t₀ t,
    angularMomentumSq_eq_of_hamiltonEqOp m k hm heq hp hq hq0 t₀ t, inner_lrlVector_position]

end CentralForce

end ClassicalMechanics
