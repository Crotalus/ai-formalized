/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license.
Authors: Nichlas Löfdahl, Claude (Anthropic)
-/
import Bertrand.Chart
/-!

# Third derivative of a Morse chart

Differentiating `U (X s) = U x₀ + s² / 2` up to four times at `s = 0` and writing
`uₖ = U⁽ᵏ⁾ x₀` gives `u₂ X'² = 1`, `X'' = -u₃ X'² / (3 u₂)` and
`X''' = (5 u₃² - 3 u₂ u₄) / (12 u₂⁴ X')`. In particular `X''' 0 = 0` forces the classical
second-order isochrony condition `5 u₃² = 3 u₂ u₄`.
-/

open Set Filter Topology Real
open scoped ContDiff

namespace Bertrand

namespace MorseChart

variable {U : ℝ → ℝ} {Ω : Set ℝ} {x₀ : ℝ}

/-- On an open set, every iterated derivative of a smooth function has the next one as its
derivative. -/
theorem hasDerivAt_iteratedDeriv_of_contDiffOn {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (k : ℕ) {s : ℝ} (hs : s ∈ S) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f s) s := by
  have hd := hf.differentiableOn_iteratedDerivWithin (m := k)
    (by exact_mod_cast ENat.natCast_lt_top k) hS.uniqueDiffOn s hs
  have heq : iteratedDerivWithin k f S =ᶠ[𝓝 s] iteratedDeriv k f :=
    eventuallyEq_of_mem (hS.mem_nhds hs) (iteratedDerivWithin_of_isOpen hS)
  rw [iteratedDeriv_succ]
  exact ((hd.differentiableAt (hS.mem_nhds hs)).congr_of_eventuallyEq heq.symm).hasDerivAt

/-- Two functions that agree on an open set containing `s` have the same derivative at `s`. -/
theorem eq_of_hasDerivAt_of_eqOn {f g : ℝ → ℝ} {f' g' s : ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hs : s ∈ S) (hfg : EqOn f g S) (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    f' = g' :=
  hf.unique (hg.congr_of_eventuallyEq (eventuallyEq_of_mem (hS.mem_nhds hs) hfg))

/-- If the third derivative of a smooth Morse chart vanishes at the origin, then
`5 U'''² = 3 U'' U''''` at the bottom of the well. -/
theorem isochrony_of_iteratedDeriv_three_eq_zero (c : MorseChart U Ω x₀) (hΩ : IsOpen Ω)
    (hU : ContDiffOn ℝ ∞ U Ω) (hX : ContDiffOn ℝ ∞ c.X (Ioo (-c.ρ) c.ρ))
    (h3 : iteratedDeriv 3 c.X 0 = 0) :
    5 * iteratedDeriv 3 U x₀ ^ 2 = 3 * iteratedDeriv 2 U x₀ * iteratedDeriv 4 U x₀ := by
  set I := Ioo (-c.ρ) c.ρ
  have hIo : IsOpen I := isOpen_Ioo
  have h0 : (0 : ℝ) ∈ I := ⟨neg_lt_zero.2 c.ρ_pos, c.ρ_pos⟩
  -- derivatives of `X` and of `U` along `X`
  have dX (k : ℕ) {s : ℝ} (hs : s ∈ I) := hasDerivAt_iteratedDeriv_of_contDiffOn hIo hX k hs
  have dU (k : ℕ) {s : ℝ} (hs : s ∈ I) :
      HasDerivAt (fun t => iteratedDeriv k U (c.X t))
        (iteratedDeriv (k + 1) U (c.X s) * iteratedDeriv 1 c.X s) s := by
    have h1 := dX 0 hs
    simp only [iteratedDeriv_zero] at h1
    exact (hasDerivAt_iteratedDeriv_of_contDiffOn hΩ hU k (c.mapsTo hs)).comp s h1
  -- (1) `U' (X s) X' s = s`
  have E1 : EqOn (fun s => iteratedDeriv 1 U (c.X s) * iteratedDeriv 1 c.X s) id I := by
    intro s hs
    have h := dU 0 hs
    simp only [iteratedDeriv_zero] at h
    exact eq_of_hasDerivAt_of_eqOn hIo hs (fun t ht => c.U_comp t ht) h
      (by simpa using ((hasDerivAt_pow 2 s).div_const 2).const_add (U x₀))
  -- (2) `U'' X'² + U' X'' = 1`
  have E2 : EqOn (fun s => iteratedDeriv 2 U (c.X s) * iteratedDeriv 1 c.X s ^ 2 +
      iteratedDeriv 1 U (c.X s) * iteratedDeriv 2 c.X s) 1 I := by
    intro s hs
    have h := eq_of_hasDerivAt_of_eqOn hIo hs E1 ((dU 1 hs).mul (dX 1 hs)) (hasDerivAt_id s)
    simp only [Pi.one_apply]
    linear_combination h
  -- (3) `U''' X'³ + 3 U'' X' X'' + U' X''' = 0`
  have E3 : EqOn (fun s => iteratedDeriv 3 U (c.X s) * iteratedDeriv 1 c.X s ^ 3 +
      3 * iteratedDeriv 2 U (c.X s) * iteratedDeriv 1 c.X s * iteratedDeriv 2 c.X s +
      iteratedDeriv 1 U (c.X s) * iteratedDeriv 3 c.X s) 0 I := by
    intro s hs
    have h := eq_of_hasDerivAt_of_eqOn hIo hs E2
      (((dU 2 hs).mul ((dX 1 hs).pow 2)).add ((dU 1 hs).mul (dX 2 hs)))
      (hasDerivAt_const s (1 : ℝ))
    simp only [Pi.zero_apply, Pi.pow_apply] at h ⊢
    linear_combination h
  -- (4) differentiate (3) once more, at `s = 0`
  have E4 := eq_of_hasDerivAt_of_eqOn hIo h0 E3
    ((((dU 3 h0).mul ((dX 1 h0).pow 3)).add
      ((((dU 2 h0).const_mul 3).mul (dX 1 h0)).mul (dX 2 h0))).add
      ((dU 1 h0).mul (dX 3 h0)))
    (hasDerivAt_const 0 (0 : ℝ))
  have e1 := E1 h0
  have e2 := E2 h0
  have e3 := E3 h0
  simp only [c.X_zero, id, Pi.one_apply, Pi.zero_apply, Pi.pow_apply] at e1 e2 e3 E4
  have hx1 : iteratedDeriv 1 c.X 0 ≠ 0 := by
    rw [iteratedDeriv_one]; exact (c.deriv_pos 0 h0).ne'
  -- `U' x₀ = 0` from (1) at `s = 0`, since `X' 0 ≠ 0`
  have hu1 : iteratedDeriv 1 U x₀ = 0 := (mul_eq_zero.1 e1).resolve_right hx1
  rw [hu1, h3] at E4
  rw [hu1] at e2 e3
  norm_num at E4 e2 e3
  set x₁ := deriv c.X 0
  set x₂ := iteratedDeriv 2 c.X 0
  set u₂ := iteratedDeriv 2 U x₀
  set u₃ := iteratedDeriv 3 U x₀
  set u₄ := iteratedDeriv 4 U x₀
  have hx₂ : x₂ = -u₃ * x₁ ^ 4 / 3 := by linear_combination (x₁ * e3 - 3 * x₂ * e2) / 3
  rw [hx₂] at E4
  -- with `p = u₂ x₁² = 1`, `E4` reads `u₄ x₁⁴ - 2 u₃² x₁⁶ + u₂ u₃² x₁⁸ / 3 = 0`
  set p := u₂ * x₁ ^ 2
  linear_combination (-3 * u₂ ^ 3) * E4 + (3 * u₂ * u₄ * (p + 1) - 6 * u₃ ^ 2 * (p ^ 2 + p + 1) +
    u₃ ^ 2 * (p ^ 3 + p ^ 2 + p + 1)) * e2

end MorseChart

end Bertrand
