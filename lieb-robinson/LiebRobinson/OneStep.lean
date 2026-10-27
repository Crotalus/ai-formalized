/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import LiebRobinson.Basic
/-!

# The basic integral inequality

For `A ∈ 𝔄_X`, the commutator `[τ_t(A), B]` grows only through the interaction terms that touch
`X`.

## i. Overview

Split the Hamiltonian as `H = H₁ + H₂`, where `H₂` collects the terms whose region meets `X` and
`H₁` the others. Then `H₁` commutes with `A`, so with `U(t) = e^{itH} e^{-itH₁}` we get
`τ_t(A) = U A U⁻¹` and `‖[τ_t(A), B]‖ = ‖[A, U⁻¹ B U]‖`. The derivative of `W(t) = U⁻¹ B U` is
`-i e^{itH₁} [H₂, τ_{-t}(B)] e^{-itH₁}`, whose norm is at most `‖[τ_t(H₂), B]‖`. Integrating gives

$$‖[τ_t(A), B]‖ ≤ ‖[A, B]‖ + 2 ‖A‖ \sum_{Z ∩ X ≠ ∅} \int_0^t ‖[τ_s(Φ_Z), B]‖ \, ds.$$

This removes the norm-preserving part of the dynamics without a time-dependent propagator: only
exponentials of fixed operators appear.

## ii. Key results

- `LiebRobinson.Interaction.touching` : the regions meeting `X`.
- `LiebRobinson.Interaction.norm_commutator_evolution_le` : the integral inequality.

## iii. Table of contents

- A. Regions touching a region
- B. The integral inequality

## iv. References

* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
-/

@[expose] public section

namespace LiebRobinson

variable {𝔄 : Type*} [CStarAlgebra 𝔄] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  {N : LocalNet Λ 𝔄}

/-!

## A. Regions touching a region

-/

/-- The regions `Z` meeting `X`. -/
def touching (X : Finset Λ) : Finset (Finset Λ) :=
  Finset.univ.filter fun Z => (Z ∩ X).Nonempty

/-!

## B. The integral inequality

-/

/-- The commutator is additive over finite sums in its first argument. -/
lemma commutator_sum_left {R ι : Type*} [Ring R] (s : Finset ι) (f : ι → R) (b : R) :
    commutator (∑ i ∈ s, f i) b = ∑ i ∈ s, commutator (f i) b := by
  simp only [commutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The commutator is additive in its second argument. -/
lemma commutator_sub_right {R : Type*} [Ring R] (a b c : R) :
    commutator a b - commutator a c = commutator a (b - c) := by
  simp only [commutator, mul_sub, sub_mul]
  abel

/-- Conjugating by elements of norm at most one does not increase the norm. -/
lemma norm_mul_mul_le {u v : 𝔄} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (x : 𝔄) :
    ‖u * x * v‖ ≤ ‖x‖ :=
  calc ‖u * x * v‖ ≤ ‖u‖ * ‖x‖ * ‖v‖ := norm_mul₃_le
    _ ≤ 1 * ‖x‖ * 1 := by gcongr
    _ = ‖x‖ := by ring

/-- At time zero, `e^{itK}` is the identity. -/
lemma expI_zero (K : 𝔄) : expI K 0 = 1 := by
  simp [expI]

/-- The derivative of `t ↦ e^{-itK}`. -/
lemma hasDerivAt_expI_neg (K : 𝔄) (t : ℝ) :
    HasDerivAt (fun s => expI K (-s)) (-((Complex.I • K) * expI K (-t))) t := by
  simpa [Function.comp_def] using (hasDerivAt_expI' K (-t)).scomp t (hasDerivAt_neg t)

namespace Interaction

variable (I : Interaction N)

omit [DecidableEq Λ] in
/-- The dynamics is additive over finite sums. -/
lemma evolution_sum {ι : Type*} (s : Finset ι) (t : ℝ) (f : ι → 𝔄) :
    I.evolution t (∑ i ∈ s, f i) = ∑ i ∈ s, I.evolution t (f i) := by
  simp only [evolution, Finset.mul_sum, Finset.sum_mul]

/-- **The basic integral inequality.** For `A ∈ 𝔄_X` and `t ≥ 0`,
`‖[τ_t(A), B]‖ ≤ ‖[A, B]‖ + 2 ‖A‖ ∑_{Z ∩ X ≠ ∅} ∫₀ᵗ ‖[τ_s(Φ_Z), B]‖ ds`. -/
theorem norm_commutator_evolution_le {X : Finset Λ} {A : 𝔄} (hA : A ∈ N.alg X) (B : 𝔄)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖commutator (I.evolution t A) B‖ ≤ ‖commutator A B‖ +
      2 * ‖A‖ * ∑ Z ∈ touching X, ∫ s in (0 : ℝ)..t, ‖commutator (I.evolution s (I.Φ Z)) B‖ := by
  set H := I.hamiltonian with hH
  set H₂ := ∑ Z ∈ touching X, I.Φ Z with hH₂def
  set H₁ := ∑ Z ∈ Finset.univ.filter (fun Z => ¬(Z ∩ X).Nonempty), I.Φ Z
  have hsplit : H = H₂ + H₁ := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsa₁ : IsSelfAdjoint H₁ := isSelfAdjoint_sum _ fun Z _ => I.isSelfAdjoint Z
  have hsa : IsSelfAdjoint H := I.isSelfAdjoint_hamiltonian
  have hAH₁ : Commute A H₁ := by
    refine Commute.sum_right _ _ _ fun Z hZ => ?_
    have hZX : Disjoint X Z := by
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
      simpa [Finset.not_nonempty_iff_eq_empty] using (Finset.mem_filter.mp hZ).2
    exact N.commute_of_disjoint hZX A hA (I.Φ Z) (I.mem_alg Z)
  -- the interaction picture
  let U : ℝ → 𝔄 := fun s => expI H s * expI H₁ (-s)
  let V : ℝ → 𝔄 := fun s => expI H₁ s * expI H (-s)
  let W : ℝ → 𝔄 := fun s => V s * B * U s
  have hUV : U t * V t = 1 := by
    simp only [U, V]
    rw [mul_assoc, ← mul_assoc (expI H₁ (-t)), expI_neg_mul_expI, one_mul, expI_mul_expI_neg]
  have hevo : I.evolution t A = U t * A * V t := by
    have hc := (commute_expI hAH₁ (-t)).eq
    calc I.evolution t A = expI H t * (A * (expI H₁ (-t) * expI H₁ t)) * expI H (-t) := by
          rw [expI_neg_mul_expI, mul_one]; rfl
      _ = expI H t * (A * expI H₁ (-t)) * expI H₁ t * expI H (-t) := by simp only [mul_assoc]
      _ = U t * A * V t := by rw [hc]; simp only [U, V, mul_assoc]
  have hU : ‖U t‖ ≤ 1 :=
    calc ‖U t‖ ≤ ‖expI H t‖ * ‖expI H₁ (-t)‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by gcongr <;> exact norm_expI_le ‹_› _
      _ = 1 := one_mul 1
  have hV : ‖V t‖ ≤ 1 :=
    calc ‖V t‖ ≤ ‖expI H₁ t‖ * ‖expI H (-t)‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by gcongr <;> exact norm_expI_le ‹_› _
      _ = 1 := one_mul 1
  have hconj : commutator (I.evolution t A) B = U t * commutator A (W t) * V t := by
    calc commutator (I.evolution t A) B
        = U t * A * V t * B * (U t * V t) - (U t * V t) * B * U t * A * V t := by
          rw [hUV, hevo, commutator]; noncomm_ring
      _ = U t * commutator A (W t) * V t := by simp only [W, commutator]; noncomm_ring
  have hW0 : W 0 = B := by simp [W, U, V, expI_zero]
  -- the derivative of `W`
  have hderiv : ∀ s, HasDerivAt W (expI H₁ s *
      commutator (I.evolution (-s) B) (Complex.I • H₂) * expI H₁ (-s)) s := by
    intro s
    have hV' := (hasDerivAt_expI H₁ s).mul (hasDerivAt_expI_neg H s)
    have hU' := (hasDerivAt_expI H s).mul (hasDerivAt_expI_neg H₁ s)
    convert (hV'.mul_const B).mul hU' using 1
    have hh : Complex.I • H = Complex.I • H₂ + Complex.I • H₁ := by rw [hsplit, smul_add]
    simp only [Pi.mul_apply, evolution, commutator, neg_neg, ← hH, hh]
    generalize Complex.I • H₁ = a
    generalize Complex.I • H₂ = c
    noncomm_ring
  -- the derivative is bounded by the commutators of the touching terms
  set g : ℝ → ℝ := fun s => ∑ Z ∈ touching X, ‖commutator (I.evolution s (I.Φ Z)) B‖ with hg
  have hbound : ∀ s, ‖expI H₁ s * commutator (I.evolution (-s) B) (Complex.I • H₂) *
      expI H₁ (-s)‖ ≤ g s := by
    intro s
    have hsmul : commutator (I.evolution (-s) B) (Complex.I • H₂) =
        -(Complex.I • commutator H₂ (I.evolution (-s) B)) := by
      simp only [commutator, mul_smul_comm, smul_mul_assoc, smul_sub, neg_sub]
    have hτ : commutator H₂ (I.evolution (-s) B) =
        I.evolution (-s) (commutator (I.evolution s H₂) B) := by
      rw [evolution_commutator, evolution_neg_evolution]
    calc _ ≤ ‖commutator (I.evolution (-s) B) (Complex.I • H₂)‖ :=
          norm_mul_mul_le (norm_expI_le hsa₁ s) (norm_expI_le hsa₁ (-s)) _
      _ = ‖I.evolution (-s) (commutator (I.evolution s H₂) B)‖ := by
          rw [hsmul, norm_neg, norm_smul, Complex.norm_I, one_mul, hτ]
      _ ≤ ‖commutator (I.evolution s H₂) B‖ := I.norm_evolution_le _ _
      _ ≤ g s := by
          rw [hH₂def, I.evolution_sum, commutator_sum_left]
          exact norm_sum_le _ _
  -- integrate the derivative bound
  have hgc : Continuous g :=
    continuous_finsetSum _ fun Z _ => I.continuous_norm_commutator_evolution _ _
  have hint : ‖W t - B‖ ≤ ∫ s in (0 : ℝ)..t, g s := by
    exact image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun s => W s - B)
      (fun x _ => ((hderiv x).sub_const B).continuousAt.continuousWithinAt)
      (fun x _ => ((hderiv x).sub_const B).hasDerivWithinAt) (by simp [hW0])
      (fun x => (hgc.integral_hasStrictDerivAt 0 x).hasDerivAt) (fun x _ => hbound x)
      ⟨ht, le_rfl⟩
  calc ‖commutator (I.evolution t A) B‖ ≤ ‖commutator A (W t)‖ := by
        rw [hconj]; exact norm_mul_mul_le hU hV _
    _ = ‖commutator A B + commutator A (W t - B)‖ := by
        rw [← commutator_sub_right, add_sub_cancel]
    _ ≤ ‖commutator A B‖ + 2 * ‖A‖ * ‖W t - B‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_commutator_le _ _) _)
    _ ≤ ‖commutator A B‖ + 2 * ‖A‖ * ∫ s in (0 : ℝ)..t, g s := by gcongr
    _ = _ := by
        rw [hg, intervalIntegral.integral_finsetSum fun Z _ =>
          (I.continuous_norm_commutator_evolution _ _).intervalIntegrable _ _]

end Interaction

end LiebRobinson
