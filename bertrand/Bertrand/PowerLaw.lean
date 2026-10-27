/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.EffPot
/-!

# The effective potential of a power-law force

For `V' r = C r ^ p`, the derivative of the effective potential is `U' x = x - K x ^ q` with
`K = C M ^ (p + 1)` and `q = -(p + 2)`. At the circular orbit `x₀` (where `K x₀ ^ q = x₀`) this
gives `U'' = p + 3`, `U''' = -(p + 2)(p + 3) / x₀` and `U'''' = (p + 2)(p + 3)(p + 4) / x₀²`.
The second-order isochrony condition `5 U'''² = 3 U'' U''''` then reads
`(p + 2)(p + 3)²(p - 1) = 0`, which leaves only `p = -2` (Newton) and `p = 1` (Hooke).
-/

open Set Filter Topology Real

namespace Bertrand

/-!

## A. Derivatives of `x - K x ^ q`

-/

section RpowDerivs

variable (K q : ℝ)

/-- `x - K x ^ q`. -/
noncomputable def rpowG₀ : ℝ → ℝ := fun y => y - K * y ^ q
/-- Its first derivative `1 - K q x ^ (q - 1)`. -/
noncomputable def rpowG₁ : ℝ → ℝ := fun y => 1 - K * q * y ^ (q - 1)
/-- Its second derivative `-K q (q - 1) x ^ (q - 2)`. -/
noncomputable def rpowG₂ : ℝ → ℝ := fun y => -(K * q * (q - 1)) * y ^ (q - 2)
/-- Its third derivative `-K q (q - 1) (q - 2) x ^ (q - 3)`. -/
noncomputable def rpowG₃ : ℝ → ℝ := fun y => -(K * q * (q - 1) * (q - 2)) * y ^ (q - 3)

variable {K q}

lemma hasDerivAt_rpowG₀ {y : ℝ} (hy : 0 < y) : HasDerivAt (rpowG₀ K q) (rpowG₁ K q y) y := by
  have h := (hasDerivAt_id y).sub
    ((Real.hasDerivAt_rpow_const (p := q) (Or.inl hy.ne')).const_mul K)
  exact h.congr_deriv (by simp only [rpowG₁]; ring_nf)

lemma hasDerivAt_rpowG₁ {y : ℝ} (hy : 0 < y) : HasDerivAt (rpowG₁ K q) (rpowG₂ K q y) y := by
  have h := (hasDerivAt_const y (1 : ℝ)).sub
    ((Real.hasDerivAt_rpow_const (p := q - 1) (Or.inl hy.ne')).const_mul (K * q))
  rw [show q - 1 - 1 = q - 2 by ring] at h
  exact (h.congr_deriv (by simp only [rpowG₂]; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => by simp only [rpowG₁, Pi.sub_apply])

lemma hasDerivAt_rpowG₂ {y : ℝ} (hy : 0 < y) : HasDerivAt (rpowG₂ K q) (rpowG₃ K q y) y := by
  have h := (Real.hasDerivAt_rpow_const (p := q - 2) (Or.inl hy.ne')).const_mul
    (-(K * q * (q - 1)))
  rw [show q - 2 - 1 = q - 3 by ring] at h
  exact h.congr_deriv (by simp only [rpowG₃]; ring)

lemma deriv_rpowG₀_eventuallyEq {x : ℝ} (hx : 0 < x) : deriv (rpowG₀ K q) =ᶠ[𝓝 x] rpowG₁ K q :=
  (eventually_gt_nhds hx).mono fun _ hy => (hasDerivAt_rpowG₀ hy).deriv

lemma deriv_rpowG₁_eventuallyEq {x : ℝ} (hx : 0 < x) : deriv (rpowG₁ K q) =ᶠ[𝓝 x] rpowG₂ K q :=
  (eventually_gt_nhds hx).mono fun _ hy => (hasDerivAt_rpowG₁ hy).deriv

/-- The first three derivatives of `x - K x ^ q` at a positive point. -/
lemma iteratedDeriv_rpowG₀ {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 (rpowG₀ K q) x = rpowG₁ K q x ∧
    iteratedDeriv 2 (rpowG₀ K q) x = rpowG₂ K q x ∧
    iteratedDeriv 3 (rpowG₀ K q) x = rpowG₃ K q x := by
  refine ⟨by rw [iteratedDeriv_one, (hasDerivAt_rpowG₀ hx).deriv], ?_, ?_⟩
  · rw [iteratedDeriv_succ', (deriv_rpowG₀_eventuallyEq hx).iteratedDeriv_eq, iteratedDeriv_one,
      (hasDerivAt_rpowG₁ hx).deriv]
  · rw [iteratedDeriv_succ', (deriv_rpowG₀_eventuallyEq hx).iteratedDeriv_eq, iteratedDeriv_succ',
      (deriv_rpowG₁_eventuallyEq hx).iteratedDeriv_eq, iteratedDeriv_one,
      (hasDerivAt_rpowG₂ hx).deriv]

end RpowDerivs

/-!

## B. The effective potential of a power law

-/

/-- For a power-law force, `M / x² · V' (M / x) = C M ^ (p + 1) x ^ (-(p + 2))`. -/
lemma powerLaw_term {C p M x : ℝ} (hM : 0 < M) (hx : 0 < x) :
    M / x ^ 2 * (C * (M / x) ^ p) = C * M ^ (p + 1) * x ^ (-(p + 2)) := by
  rw [Real.div_rpow hM.le hx.le, Real.rpow_add_one hM.ne', Real.rpow_neg hx.le,
    Real.rpow_add hx, Real.rpow_two]
  field_simp

/-- For a power-law force `V' r = C r ^ p`, the second, third and fourth derivatives of the
effective potential at the circular orbit of radius `r`. -/
lemma iteratedDeriv_effPot_powerLaw {V : ℝ → ℝ} {a b C p r : ℝ} (ha : 0 < a)
    (hV : DifferentiableOn ℝ V (Ioo a b)) (hr : r ∈ Ioo a b) (hC : 0 < C)
    (hpow : ∀ y ∈ Ioo a b, deriv V y = C * y ^ p) :
    iteratedDeriv 2 (effPot V (angMom V r)) (angMom V r / r) = p + 3 ∧
    iteratedDeriv 3 (effPot V (angMom V r)) (angMom V r / r) =
      -((p + 2) * (p + 3)) / (angMom V r / r) ∧
    iteratedDeriv 4 (effPot V (angMom V r)) (angMom V r / r) =
      (p + 2) * (p + 3) * (p + 4) / (angMom V r / r) ^ 2 := by
  set M := angMom V r with hMdef
  have hr0 : 0 < r := ha.trans hr.1
  have hV' : 0 < deriv V r := by rw [hpow r hr]; exact mul_pos hC (Real.rpow_pos_of_pos hr0 _)
  have hM : 0 < M := Real.sqrt_pos.mpr (by positivity)
  set x₀ := M / r with hx₀def
  have hx₀ : 0 < x₀ := by positivity
  have hMr : M / x₀ = r := by rw [hx₀def]; field_simp
  set K := C * M ^ (p + 1)
  set q := -(p + 2) with hq
  -- Near `x₀`, `U' = x - K x ^ q`.
  have hcont : ContinuousAt (fun x : ℝ => M / x) x₀ :=
    continuousAt_const.div continuousAt_id hx₀.ne'
  have hnhds : Ioo a b ∈ 𝓝 (M / x₀) := by rw [hMr]; exact isOpen_Ioo.mem_nhds hr
  have hD : deriv (effPot V M) =ᶠ[𝓝 x₀] rpowG₀ K q :=
    ((eventually_gt_nhds hx₀).and (hcont.preimage_mem_nhds hnhds)).mono fun x hx => by
      rw [(hasDerivAt_effPot hx.1.ne' ((hV _ hx.2).differentiableAt
        (isOpen_Ioo.mem_nhds hx.2))).deriv, hpow _ hx.2, powerLaw_term hM hx.1]
      rfl
  -- The circular orbit: `K x₀ ^ q = x₀`.
  have hcirc : K * x₀ ^ q = x₀ := by
    have h0 := deriv_effPot_circular hr0 hV' ((hV r hr).differentiableAt (isOpen_Ioo.mem_nhds hr))
    rw [hD.self_of_nhds] at h0
    simp only [rpowG₀] at h0
    linarith
  obtain ⟨_, h2, h3⟩ := iteratedDeriv_rpowG₀ (K := K) (q := q) hx₀
  have hU (n : ℕ) : iteratedDeriv (n + 1) (effPot V M) x₀ = iteratedDeriv n (rpowG₀ K q) x₀ := by
    rw [iteratedDeriv_succ', hD.iteratedDeriv_eq]
  have hxq : x₀ ^ (-(p + 2)) ≠ 0 := (Real.rpow_pos_of_pos hx₀ _).ne'
  have hK : K = x₀ / x₀ ^ q := (eq_div_iff (Real.rpow_pos_of_pos hx₀ q).ne').mpr hcirc
  refine ⟨?_, ?_, ?_⟩
  · rw [hU 1, iteratedDeriv_one, (hasDerivAt_rpowG₀ hx₀).deriv]
    simp only [rpowG₁]
    rw [Real.rpow_sub_one hx₀.ne', hK, hq]
    field_simp
    ring
  · rw [hU 2, h2]
    simp only [rpowG₂]
    rw [Real.rpow_sub hx₀, Real.rpow_two, hK, hq]
    field_simp
    ring
  · rw [hU 3, h3]
    simp only [rpowG₃]
    rw [Real.rpow_sub hx₀, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hK, hq]
    field_simp
    ring

/-- For a power law with `p + 3 > 0`, the isochrony condition `5 U'''² = 3 U'' U''''` at the
circular orbit forces `p = -2` or `p = 1`. -/
lemma powerLaw_eq_of_isochrony {p x₀ : ℝ} (hx₀ : x₀ ≠ 0) (hp : 0 < p + 3)
    (h : 5 * (-((p + 2) * (p + 3)) / x₀) ^ 2 =
      3 * (p + 3) * ((p + 2) * (p + 3) * (p + 4) / x₀ ^ 2)) :
    p = -2 ∨ p = 1 := by
  field_simp at h
  have h' : (p + 2) * (p - 1) = 0 := by linear_combination h / 2
  rcases mul_eq_zero.mp h' with h'' | h''
  · left; linarith
  · right; linarith

end Bertrand
