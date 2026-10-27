/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import LiebRobinson.Basic
/-!

# Gapped ground states and the spectral expansion of correlations

In a finite-dimensional system with a unique ground state and a spectral gap `γ`, ground-state
correlation functions are finite sums of oscillations with frequencies at least `γ`.

## i. Overview

Let `H` be a self-adjoint operator on a finite-dimensional Hilbert space with a normalized
eigenvector `Ω`, `H Ω = E₀ Ω`, such that `⟪φ, H φ⟫ ≥ (E₀ + γ) ‖φ‖²` for `φ ⊥ Ω`. Expanding in an
eigenbasis `φₙ` of `H` with energies `E₀ + ωₙ`, the connected correlation is
`⟨AB⟩ - ⟨A⟩⟨B⟩ = ∑ cₙ` with `cₙ = ⟪Ω, A φₙ⟫ ⟪φₙ, B Ω⟫` summed over `φₙ ⊥ Ω`, and

$$⟨Ω, [τ_t(A), B] Ω⟩ = ⟨Ω, [A, B] Ω⟩ + \sum_n c_n (e^{-iω_n t} - 1) - \sum_n d_n (e^{iω_n t} - 1),$$

with `dₙ = ⟪Ω, B φₙ⟫ ⟪φₙ, A Ω⟫`, all relevant `ωₙ ≥ γ`, and `∑ |cₙ|, ∑ |dₙ| ≤ ‖A‖ ‖B‖` by
Cauchy–Schwarz.

## ii. Key results

- `LiebRobinson.GappedGroundState` : a unique ground state with spectral gap `γ`.
- `LiebRobinson.GappedGroundState.corr` : the connected correlation `⟨AB⟩ - ⟨A⟩⟨B⟩`.
- `LiebRobinson.GappedGroundState.exists_expansion` : the spectral expansion.

## iii. Table of contents

- A. Gapped ground states
- B. The spectral expansion

## iv. References

* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
-/

@[expose] public section

namespace LiebRobinson

open scoped InnerProductSpace

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-!

## A. Gapped ground states

-/

/-- A unique ground state of `H` with spectral gap `γ`: a unit vector `Ω` with `H Ω = E₀ Ω` and
`⟪φ, H φ⟫ ≥ (E₀ + γ) ‖φ‖²` for every `φ` orthogonal to `Ω`. -/
structure GappedGroundState (H : ℋ →L[ℂ] ℋ) (γ : ℝ) where
  /-- The ground state. -/
  Ω : ℋ
  /-- The ground state is normalized. -/
  norm_Ω : ‖Ω‖ = 1
  /-- The ground state energy. -/
  E₀ : ℝ
  /-- The ground state is an eigenvector. -/
  apply_Ω : H Ω = (E₀ : ℂ) • Ω
  /-- The spectral gap above the ground state. -/
  gap : ∀ φ : ℋ, ⟪Ω, φ⟫_ℂ = 0 → (E₀ + γ) * ‖φ‖ ^ 2 ≤ (⟪φ, H φ⟫_ℂ).re

namespace GappedGroundState

variable {H : ℋ →L[ℂ] ℋ} {γ : ℝ} (G : GappedGroundState H γ)

/-- The connected correlation `⟨AB⟩ - ⟨A⟩⟨B⟩` in the ground state. -/
noncomputable def corr (A B : ℋ →L[ℂ] ℋ) : ℂ :=
  ⟪G.Ω, (A * B) G.Ω⟫_ℂ - ⟪G.Ω, A G.Ω⟫_ℂ * ⟪G.Ω, B G.Ω⟫_ℂ

omit [CompleteSpace ℋ] in
/-- An operator moves the ground state by at most its operator norm. -/
lemma norm_apply_Ω_le (X : ℋ →L[ℂ] ℋ) : ‖X G.Ω‖ ≤ ‖X‖ :=
  (X.le_opNorm _).trans_eq (by rw [G.norm_Ω, mul_one])

omit [CompleteSpace ℋ] in
/-- The ground-state expectation is bounded by the operator norm. -/
lemma norm_inner_le (X : ℋ →L[ℂ] ℋ) : ‖⟪G.Ω, X G.Ω⟫_ℂ‖ ≤ ‖X‖ := by
  calc ‖⟪G.Ω, X G.Ω⟫_ℂ‖ ≤ ‖G.Ω‖ * ‖X G.Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖X‖ := by rw [G.norm_Ω, one_mul]; exact G.norm_apply_Ω_le X

/-!

## B. The spectral expansion

-/

/-- The exponential of an operator acts on an eigenvector as the exponential of its eigenvalue. -/
lemma exp_apply_of_apply_eq_smul {K : ℋ →L[ℂ] ℋ} {v : ℋ} {μ : ℂ} (h : K v = μ • v) :
    NormedSpace.exp K v = Complex.exp μ • v := by
  have hpow : ∀ k : ℕ, (K ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, h, smul_smul, ← pow_succ]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) K).mapL
    (ContinuousLinearMap.apply ℂ ℋ v)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const v
  rw [← Complex.exp_eq_exp_ℂ] at h2
  refine h1.unique ?_
  convert h2 using 1
  ext k
  simp [hpow, smul_smul]

/-- `e^{isH}` acts on an eigenvector of `H` with eigenvalue `μ` as the phase `e^{isμ}`. -/
lemma expI_apply_of_apply_eq_smul {v : ℋ} {μ : ℝ} (hv : H v = (μ : ℂ) • v) (s : ℝ) :
    expI H s v = Complex.exp (s * μ * Complex.I) • v := by
  refine exp_apply_of_apply_eq_smul ?_
  simp only [smul_apply, hv, RCLike.real_smul_eq_coe_smul (K := ℂ),
    smul_smul]
  congr 1
  simp only [Complex.coe_algebraMap]
  ring

/-- The commutator is unchanged by shifting both arguments by scalars. -/
lemma commutator_sub_smul_one {R : Type*} [Ring R] [Algebra ℂ R] (X Y : R) (a b : ℂ) :
    commutator (X - a • 1) (Y - b • 1) = commutator X Y := by
  simp only [commutator, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub, smul_smul, mul_comm b a]
  abel

omit [CompleteSpace ℋ] in
/-- The ground state is normalized, in inner-product form. -/
lemma inner_Ω_self : ⟪G.Ω, G.Ω⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, G.norm_Ω]
  simp

omit [CompleteSpace ℋ] in
/-- Removing the `Ω`-component of a vector leaves a vector orthogonal to `Ω`. -/
lemma inner_Ω_sub_smul (x : ℋ) : ⟪G.Ω, x - ⟪G.Ω, x⟫_ℂ • G.Ω⟫_ℂ = 0 := by
  rw [inner_sub_right, inner_smul_right, G.inner_Ω_self, mul_one, sub_self]

omit [CompleteSpace ℋ] in
/-- Removing the `Ω`-component of a vector does not increase its norm. -/
lemma norm_sub_smul_le (x : ℋ) : ‖x - ⟪G.Ω, x⟫_ℂ • G.Ω‖ ≤ ‖x‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
    (x - ⟪G.Ω, x⟫_ℂ • G.Ω) (⟪G.Ω, x⟫_ℂ • G.Ω)
    (by rw [inner_smul_right, inner_eq_zero_symm.mp (G.inner_Ω_sub_smul x), mul_zero])
  rw [sub_add_cancel] at h
  nlinarith [norm_nonneg (x - ⟪G.Ω, x⟫_ℂ • G.Ω), norm_nonneg x, norm_nonneg (⟪G.Ω, x⟫_ℂ • G.Ω)]

/-- The ground-state matrix elements of an operator shifted by its expectation are those of the
`Ω`-orthogonal part of `X† Ω`. -/
lemma inner_Ω_sub_smul_one_apply (X : ℋ →L[ℂ] ℋ) (z : ℋ) :
    ⟪G.Ω, (X - ⟪G.Ω, X G.Ω⟫_ℂ • 1) z⟫_ℂ =
      ⟪X.adjoint G.Ω - ⟪G.Ω, X.adjoint G.Ω⟫_ℂ • G.Ω, z⟫_ℂ := by
  rw [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right, inner_sub_left,
    inner_smul_left, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm,
    ContinuousLinearMap.adjoint_inner_left]

/-- An eigenvector of `H` with eigenvalue `μ` overlaps the ground state only if `μ = E₀`. -/
lemma inner_Ω_mul_ofReal (hH : IsSelfAdjoint H) {v : ℋ} {μ : ℝ} (hv : H v = (μ : ℂ) • v) :
    ⟪G.Ω, v⟫_ℂ * μ = ⟪G.Ω, v⟫_ℂ * G.E₀ := by
  have h := hH.isSymmetric G.Ω v
  simp only [ContinuousLinearMap.coe_coe, G.apply_Ω, hv, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal] at h
  linear_combination -h

/-- On an eigenvector of `H` overlapping the ground state, any function of the eigenvalue may be
evaluated at `E₀` instead. -/
lemma inner_Ω_mul_apply (hH : IsSelfAdjoint H) {v : ℋ} {μ : ℝ} (hv : H v = (μ : ℂ) • v)
    (f : ℝ → ℂ) : ⟪G.Ω, v⟫_ℂ * f μ = ⟪G.Ω, v⟫_ℂ * f G.E₀ := by
  by_cases h0 : ⟪G.Ω, v⟫_ℂ = 0
  · simp [h0]
  · rw [Complex.ofReal_injective (mul_left_cancel₀ h0 (G.inner_Ω_mul_ofReal hH hv))]

/-- An eigenvector of `H` with eigenvalue below `E₀ + γ` is a multiple of the ground state. -/
lemma eq_inner_smul_Ω_of_lt (hH : IsSelfAdjoint H) {v : ℋ} {μ : ℝ} (hv : H v = (μ : ℂ) • v)
    (hμ : μ < G.E₀ + γ) : v = ⟪G.Ω, v⟫_ℂ • G.Ω := by
  set ψ := v - ⟪G.Ω, v⟫_ℂ • G.Ω with hψ
  have hHψ : H ψ = (μ : ℂ) • ψ := by
    rw [hψ, map_sub, map_smul, hv, G.apply_Ω, smul_sub, smul_smul, smul_smul, mul_comm (μ : ℂ),
      G.inner_Ω_mul_ofReal hH hv]
  have hgap := G.gap ψ (G.inner_Ω_sub_smul v)
  rw [hHψ, inner_smul_right, inner_self_eq_norm_sq_to_K] at hgap
  replace hgap := hgap.trans_eq (c := μ * ‖ψ‖ ^ 2)
    (by simp only [Complex.coe_algebraMap]; norm_cast)
  have h0 : ‖ψ‖ ^ 2 ≤ 0 := by nlinarith
  have hψ0 : ψ = 0 := by
    rw [← norm_eq_zero]
    exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h0 (sq_nonneg _))
  exact sub_eq_zero.mp hψ0

/-- Vectors orthogonal to the ground state are orthogonal to the eigenvectors of `H` with
eigenvalue below `E₀ + γ`. -/
lemma inner_eq_zero_of_lt (hH : IsSelfAdjoint H) {v : ℋ} {μ : ℝ} (hv : H v = (μ : ℂ) • v)
    (hμ : μ < G.E₀ + γ) {x : ℋ} (hx : ⟪G.Ω, x⟫_ℂ = 0) : ⟪x, v⟫_ℂ = 0 := by
  rw [G.eq_inner_smul_Ω_of_lt hH hv hμ, inner_smul_right, inner_eq_zero_symm.mp hx, mul_zero]

omit [CompleteSpace ℋ] in
/-- **Cauchy–Schwarz** for the expansion coefficients of two vectors in an orthonormal basis. -/
lemma sum_norm_inner_mul_inner_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ ℋ)
    (x y : ℋ) : ∑ i, ‖⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  simp_rw [norm_mul]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_
  rw [b.sum_sq_norm_inner_left, b.sum_sq_norm_inner_right, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

/-- Matrix elements of `e^{isH}` in an eigenbasis of `H`. -/
lemma inner_expI_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ ℋ) {e : ι → ℝ}
    (hb : ∀ i, H (b i) = (e i : ℂ) • b i) (s : ℝ) (x y : ℋ) :
    ⟪x, expI H s y⟫_ℂ = ∑ i, ⟪x, b i⟫_ℂ * ⟪b i, y⟫_ℂ * Complex.exp (s * e i * Complex.I) := by
  conv_lhs => rw [← b.sum_repr' y]
  simp only [map_sum, map_smul, expI_apply_of_apply_eq_smul (hb _), inner_sum, inner_smul_right,
    smul_smul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `⟪Ω, e^{isH} z⟫ = e^{isE₀} ⟪Ω, z⟫`. -/
lemma inner_Ω_expI_apply (hH : IsSelfAdjoint H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ ℋ) {e : ι → ℝ} (hb : ∀ i, H (b i) = (e i : ℂ) • b i) (s : ℝ)
    (z : ℋ) : ⟪G.Ω, expI H s z⟫_ℂ = Complex.exp (s * G.E₀ * Complex.I) * ⟪G.Ω, z⟫_ℂ := by
  rw [inner_expI_apply b hb, ← b.sum_inner_mul_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_right_comm, G.inner_Ω_mul_apply hH (hb i) fun μ => Complex.exp (s * μ * Complex.I)]
  ring

/-- The ground-state commutator function in terms of the shifted vectors `u = A'† Ω`,
`w = B' Ω`, `w' = B'† Ω` and `u' = A' Ω`, where `X' = X - ⟨X⟩`. -/
lemma inner_commutator_expI (hH : IsSelfAdjoint H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ ℋ) {e : ι → ℝ} (hb : ∀ i, H (b i) = (e i : ℂ) • b i)
    (A B : ℋ →L[ℂ] ℋ) (t : ℝ) :
    ⟪G.Ω, (commutator (expI H t * A * expI H (-t)) B) G.Ω⟫_ℂ =
      Complex.exp (t * G.E₀ * Complex.I) *
          ⟪A.adjoint G.Ω - ⟪G.Ω, A.adjoint G.Ω⟫_ℂ • G.Ω,
            expI H (-t) (B G.Ω - ⟪G.Ω, B G.Ω⟫_ℂ • G.Ω)⟫_ℂ -
        Complex.exp (-t * G.E₀ * Complex.I) *
          ⟪B.adjoint G.Ω - ⟪G.Ω, B.adjoint G.Ω⟫_ℂ • G.Ω,
            expI H t (A G.Ω - ⟪G.Ω, A G.Ω⟫_ℂ • G.Ω)⟫_ℂ := by
  have hconj : expI H t * A * expI H (-t) - ⟪G.Ω, A G.Ω⟫_ℂ • 1 =
      expI H t * (A - ⟪G.Ω, A G.Ω⟫_ℂ • 1) * expI H (-t) := by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, expI_mul_expI_neg]
  rw [← commutator_sub_smul_one _ B ⟪G.Ω, A G.Ω⟫_ℂ ⟪G.Ω, B G.Ω⟫_ℂ, hconj]
  have hA' := G.inner_Ω_sub_smul_one_apply A
  have hB' := G.inner_Ω_sub_smul_one_apply B
  have hAΩ : (A - ⟪G.Ω, A G.Ω⟫_ℂ • 1) G.Ω = A G.Ω - ⟪G.Ω, A G.Ω⟫_ℂ • G.Ω := by simp
  have hBΩ : (B - ⟪G.Ω, B G.Ω⟫_ℂ • 1) G.Ω = B G.Ω - ⟪G.Ω, B G.Ω⟫_ℂ • G.Ω := by simp
  generalize A - ⟪G.Ω, A G.Ω⟫_ℂ • 1 = A' at hA' hAΩ ⊢
  generalize B - ⟪G.Ω, B G.Ω⟫_ℂ • 1 = B' at hB' hBΩ ⊢
  simp only [commutator, sub_apply, mul_apply_eq_comp, inner_sub_right]
  rw [G.inner_Ω_expI_apply hH b hb, hA', hB', expI_apply_of_apply_eq_smul G.apply_Ω, map_smul,
    hAΩ, hBΩ, map_smul, inner_smul_right]
  push_cast
  ring

/-- **The spectral expansion.** In finite dimension, the ground-state commutator function
`t ↦ ⟪Ω, [τ_t(A), B] Ω⟫` is a sum of oscillations with frequencies at least `γ`, whose
positive-frequency amplitudes add up to the connected correlation. -/
theorem exists_expansion [FiniteDimensional ℂ ℋ] (hH : IsSelfAdjoint H) (A B : ℋ →L[ℂ] ℋ) :
    ∃ (n : ℕ) (ω : Fin n → ℝ) (c d : Fin n → ℂ), (∀ i, γ ≤ ω i) ∧
      ∑ i, ‖c i‖ ≤ ‖A‖ * ‖B‖ ∧ ∑ i, ‖d i‖ ≤ ‖A‖ * ‖B‖ ∧
      G.corr A B = ∑ i, c i ∧
      ⟪G.Ω, (commutator A B) G.Ω⟫_ℂ = ∑ i, c i - ∑ i, d i ∧
      ∀ t : ℝ, ⟪G.Ω, (commutator (expI H t * A * expI H (-t)) B) G.Ω⟫_ℂ =
        ⟪G.Ω, (commutator A B) G.Ω⟫_ℂ +
          (∑ i, c i * (Complex.exp (-(ω i * t) * Complex.I) - 1) -
            ∑ i, d i * (Complex.exp ((ω i * t) * Complex.I) - 1)) := by
  have hT := hH.isSymmetric
  set b := hT.eigenvectorBasis (rfl : Module.finrank ℂ ℋ = _)
  set e := hT.eigenvalues (rfl : Module.finrank ℂ ℋ = _)
  have hb : ∀ i, H (b i) = (e i : ℂ) • b i := hT.apply_eigenvectorBasis rfl
  set u := A.adjoint G.Ω - ⟪G.Ω, A.adjoint G.Ω⟫_ℂ • G.Ω with hu
  set w := B G.Ω - ⟪G.Ω, B G.Ω⟫_ℂ • G.Ω with hw
  set w' := B.adjoint G.Ω - ⟪G.Ω, B.adjoint G.Ω⟫_ℂ • G.Ω with hw'
  set u' := A G.Ω - ⟪G.Ω, A G.Ω⟫_ℂ • G.Ω with hu'
  have hlow : ∀ i, e i - G.E₀ < γ → ⟪u, b i⟫_ℂ = 0 ∧ ⟪w', b i⟫_ℂ = 0 := fun i hi =>
    ⟨G.inner_eq_zero_of_lt hH (hb i) (by linarith) (G.inner_Ω_sub_smul _),
      G.inner_eq_zero_of_lt hH (hb i) (by linarith) (G.inner_Ω_sub_smul _)⟩
  have hnorm : ∀ X : ℋ →L[ℂ] ℋ, ‖X.adjoint G.Ω - ⟪G.Ω, X.adjoint G.Ω⟫_ℂ • G.Ω‖ ≤ ‖X‖ :=
    fun X => (G.norm_sub_smul_le _).trans
      ((G.norm_apply_Ω_le _).trans_eq (ContinuousLinearMap.adjoint.norm_map X))
  have hnorm' : ∀ X : ℋ →L[ℂ] ℋ, ‖X G.Ω - ⟪G.Ω, X G.Ω⟫_ℂ • G.Ω‖ ≤ ‖X‖ :=
    fun X => (G.norm_sub_smul_le _).trans (G.norm_apply_Ω_le _)
  have hF : ∀ t : ℝ, ⟪G.Ω, (commutator (expI H t * A * expI H (-t)) B) G.Ω⟫_ℂ =
      ∑ i, ⟪u, b i⟫_ℂ * ⟪b i, w⟫_ℂ * Complex.exp (-(max (e i - G.E₀) γ * t) * Complex.I) -
        ∑ i, ⟪w', b i⟫_ℂ * ⟪b i, u'⟫_ℂ * Complex.exp ((max (e i - G.E₀) γ * t) * Complex.I) := by
    intro t
    rw [G.inner_commutator_expI hH b hb, ← hu, ← hw, ← hw', ← hu', inner_expI_apply b hb,
      inner_expI_apply b hb, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
    · rcases lt_or_ge (e i - G.E₀) γ with hi | hi
      · simp only [(hlow i hi).1, zero_mul, mul_zero]
      · rw [max_eq_left hi, mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
    · rcases lt_or_ge (e i - G.E₀) γ with hi | hi
      · simp only [(hlow i hi).2, zero_mul, mul_zero]
      · rw [max_eq_left hi, mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
  have h0 : ⟪G.Ω, (commutator A B) G.Ω⟫_ℂ =
      ∑ i, ⟪u, b i⟫_ℂ * ⟪b i, w⟫_ℂ - ∑ i, ⟪w', b i⟫_ℂ * ⟪b i, u'⟫_ℂ := by
    simpa [expI] using hF 0
  refine ⟨_, fun i => max (e i - G.E₀) γ, fun i => ⟪u, b i⟫_ℂ * ⟪b i, w⟫_ℂ,
    fun i => ⟪w', b i⟫_ℂ * ⟪b i, u'⟫_ℂ, fun i => le_max_right _ _,
    (sum_norm_inner_mul_inner_le b u w).trans
      (mul_le_mul (hnorm A) (hnorm' B) (norm_nonneg _) (norm_nonneg _)),
    (sum_norm_inner_mul_inner_le b w' u').trans
      ((mul_le_mul (hnorm B) (hnorm' A) (norm_nonneg _) (norm_nonneg _)).trans_eq
        (mul_comm _ _)), ?_, h0, fun t => ?_⟩
  · rw [b.sum_inner_mul_inner, hu, ← G.inner_Ω_sub_smul_one_apply]
    simp [corr, hw, G.norm_Ω, mul_apply_eq_comp]
    ring
  · rw [hF t, h0]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    ring

end GappedGroundState

end LiebRobinson
