/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import Mathlib
/-!

# Local nets, interactions and the Heisenberg dynamics

The setting of the Lieb–Robinson bound on a finite lattice.

## i. Overview

The observables of a quantum spin system on a finite set of sites `Λ` form a C*-algebra `𝔄`. To
each region `X ⊆ Λ` belongs a subalgebra `𝔄_X` of observables localized in `X`. The only
property of the localization used in the Lieb–Robinson bound is that observables in disjoint
regions commute, which avoids tensor products entirely.

An interaction assigns to each region `Z` a self-adjoint observable `Φ Z ∈ 𝔄_Z`. Its Hamiltonian
is `H = ∑_Z Φ Z` and the Heisenberg dynamics is `τ_t(A) = e^{itH} A e^{-itH}`.

## ii. Key results

- `LiebRobinson.LocalNet` : subalgebras indexed by regions, commuting on disjoint regions.
- `LiebRobinson.Interaction` : a family of local self-adjoint terms.
- `LiebRobinson.Interaction.evolution` : the Heisenberg dynamics `τ_t`.
- `LiebRobinson.Interaction.norm_evolution_le` : `τ_t` does not increase norms.

## iii. Table of contents

- A. The commutator
- B. Unitary exponentials
- C. Local nets and interactions
- D. The Heisenberg dynamics

## iv. References

* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
-/

@[expose] public section

namespace LiebRobinson

open NormedSpace

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

/-!

## A. The commutator

-/

/-- The commutator `[a, b] = a b - b a`. -/
def commutator {R : Type*} [Ring R] (a b : R) : R := a * b - b * a

lemma commutator_eq_zero_of_commute {R : Type*} [Ring R] {a b : R} (h : Commute a b) :
    commutator a b = 0 :=
  sub_eq_zero.mpr h.eq

lemma commutator_zero_left {R : Type*} [Ring R] (b : R) : commutator 0 b = 0 := by
  simp [commutator]

/-- `‖[a, b]‖ ≤ 2 ‖a‖ ‖b‖`. -/
lemma norm_commutator_le (a b : 𝔄) : ‖commutator a b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  calc ‖commutator a b‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖a‖ * ‖b‖ := by ring

/-!

## B. Unitary exponentials

-/

/-- The exponential `e^{itK}`, for real time `t`. -/
noncomputable def expI (K : 𝔄) (t : ℝ) : 𝔄 := exp (t • (Complex.I • K))

lemma expI_mul_expI_neg (K : 𝔄) (t : ℝ) : expI K t * expI K (-t) = 1 := by
  let : NormedAlgebra ℚ 𝔄 := .restrictScalars ℚ ℂ 𝔄
  rw [expI, expI, ← exp_add_of_commute (((Commute.refl _).smul_left t).smul_right (-t)),
    ← add_smul, add_neg_cancel, zero_smul, exp_zero]

lemma expI_neg_mul_expI (K : 𝔄) (t : ℝ) : expI K (-t) * expI K t = 1 := by
  simpa using expI_mul_expI_neg K (-t)

/-- For self-adjoint `K`, `e^{itK}` is unitary. -/
lemma expI_mem_unitary {K : 𝔄} (hK : IsSelfAdjoint K) (t : ℝ) : expI K t ∈ unitary 𝔄 := by
  let : NormedAlgebra ℚ 𝔄 := .restrictScalars ℚ ℂ 𝔄
  refine exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr ?_)
  simp [star_smul, hK.star_eq]

/-- For self-adjoint `K`, `‖e^{itK}‖ ≤ 1`. -/
lemma norm_expI_le {K : 𝔄} (hK : IsSelfAdjoint K) (t : ℝ) : ‖expI K t‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial 𝔄 with h | h
  · simp [Subsingleton.elim (expI K t) 0]
  · exact (CStarRing.norm_of_mem_unitary (expI_mem_unitary hK t)).le

lemma hasDerivAt_expI (K : 𝔄) (t : ℝ) :
    HasDerivAt (expI K) (expI K t * (Complex.I • K)) t :=
  hasDerivAt_exp_smul_const (Complex.I • K) t

lemma hasDerivAt_expI' (K : 𝔄) (t : ℝ) :
    HasDerivAt (expI K) ((Complex.I • K) * expI K t) t :=
  hasDerivAt_exp_smul_const' (Complex.I • K) t

lemma continuous_expI (K : 𝔄) : Continuous (expI K) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_expI K t).continuousAt

lemma commute_expI {a K : 𝔄} (h : Commute a K) (t : ℝ) : Commute a (expI K t) :=
  ((h.smul_right Complex.I).smul_right t).exp_right

/-!

## C. Local nets and interactions

-/

/-- A net of local algebras on the sites `Λ`: a subalgebra of observables for each region, such
that observables in disjoint regions commute. -/
structure LocalNet (Λ 𝔄 : Type*) [CStarAlgebra 𝔄] where
  /-- The algebra of observables localized in a region. -/
  alg : Finset Λ → Subalgebra ℂ 𝔄
  /-- Observables in disjoint regions commute. -/
  commute_of_disjoint : ∀ {X Y : Finset Λ}, Disjoint X Y →
    ∀ a ∈ alg X, ∀ b ∈ alg Y, Commute a b

variable {Λ : Type*} {N : LocalNet Λ 𝔄}

/-- An interaction: a self-adjoint observable `Φ Z ∈ 𝔄_Z` for every region `Z`. -/
structure Interaction (N : LocalNet Λ 𝔄) where
  /-- The interaction term of a region. -/
  Φ : Finset Λ → 𝔄
  /-- Each term is localized in its region. -/
  mem_alg : ∀ Z, Φ Z ∈ N.alg Z
  /-- Each term is self-adjoint. -/
  isSelfAdjoint : ∀ Z, IsSelfAdjoint (Φ Z)

namespace Interaction

variable [Fintype Λ] (I : Interaction N)

/-- The Hamiltonian `H = ∑_Z Φ Z`. -/
noncomputable def hamiltonian : 𝔄 := ∑ Z : Finset Λ, I.Φ Z

lemma isSelfAdjoint_hamiltonian : IsSelfAdjoint I.hamiltonian :=
  isSelfAdjoint_sum _ fun Z _ => I.isSelfAdjoint Z

/-!

## D. The Heisenberg dynamics

-/

/-- The Heisenberg dynamics `τ_t(A) = e^{itH} A e^{-itH}`. -/
noncomputable def evolution (t : ℝ) (A : 𝔄) : 𝔄 :=
  expI I.hamiltonian t * A * expI I.hamiltonian (-t)

lemma evolution_zero (A : 𝔄) : I.evolution 0 A = A := by
  simp [evolution, expI]

@[simp]
lemma evolution_zero_right (t : ℝ) : I.evolution t 0 = 0 := by
  simp [evolution]

lemma evolution_mul (t : ℝ) (A B : 𝔄) :
    I.evolution t (A * B) = I.evolution t A * I.evolution t B := by
  simp only [evolution, mul_assoc]
  rw [← mul_assoc (expI _ (-t)), expI_neg_mul_expI, one_mul]

lemma evolution_commutator (t : ℝ) (A B : 𝔄) :
    I.evolution t (commutator A B) = commutator (I.evolution t A) (I.evolution t B) := by
  rw [commutator, commutator, ← evolution_mul, ← evolution_mul]
  simp only [evolution, mul_sub, sub_mul]

lemma evolution_neg_evolution (t : ℝ) (A : 𝔄) : I.evolution (-t) (I.evolution t A) = A := by
  simp only [evolution, neg_neg, ← mul_assoc, expI_neg_mul_expI, one_mul]
  rw [mul_assoc, expI_neg_mul_expI, mul_one]

/-- The dynamics does not increase norms. -/
lemma norm_evolution_le (t : ℝ) (A : 𝔄) : ‖I.evolution t A‖ ≤ ‖A‖ := by
  have h := I.isSelfAdjoint_hamiltonian
  calc ‖I.evolution t A‖ ≤ ‖expI I.hamiltonian t‖ * ‖A‖ * ‖expI I.hamiltonian (-t)‖ :=
        (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ 1 * ‖A‖ * 1 := by gcongr <;> exact norm_expI_le h _
    _ = ‖A‖ := by ring

lemma continuous_evolution (A : 𝔄) : Continuous fun t => I.evolution t A :=
  ((continuous_expI _).mul continuous_const).mul ((continuous_expI _).comp continuous_neg)

/-- For fixed `A` and `B`, the function `t ↦ ‖[τ_t(A), B]‖` is continuous. -/
lemma continuous_norm_commutator_evolution (A B : 𝔄) :
    Continuous fun t => ‖commutator (I.evolution t A) B‖ :=
  (((I.continuous_evolution A).mul continuous_const).sub
    (continuous_const.mul (I.continuous_evolution A))).norm

end Interaction

end LiebRobinson
