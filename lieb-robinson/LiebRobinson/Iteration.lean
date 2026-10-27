/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import LiebRobinson.OneStep
/-!

# Iterating the integral inequality

Commutators with `B ∈ 𝔄_Y` stay small until a chain of overlapping interaction terms reaches `Y`.

## i. Overview

Fix `B ∈ 𝔄_Y` and write `f_Z(t) = ‖[τ_t(Φ_Z), B]‖`. Applied to `A = Φ_Z`, the basic integral
inequality reads `f_Z(t) ≤ f_Z(0) + 2 ‖Φ_Z‖ ∑_{Z' ∩ Z ≠ ∅} ∫₀ᵗ f_{Z'}`, and `f_Z(0) = 0` whenever
`Z` is disjoint from `Y`. The predicate `Far Y k Z` says that every chain of overlapping non-zero
terms from `Z` to `Y` has at least `k` steps after `Z`. With `‖Φ_Z‖ ≤ J` and at most `κ` non-zero
terms meeting any region, induction on `k` gives

$$f_Z(t) ≤ 2 ‖Φ_Z‖ ‖B‖ \frac{(2 J κ t)^k}{k!} \quad \text{if } \mathrm{Far}\,Y\,k\,Z,$$

and one more application of the integral inequality gives the bound for `[τ_t(A), B]`. Since
`x^m / m! ≤ e^{e x - m}`, this has the Lieb–Robinson form `e^{v t - m}` with `v = 2 e J κ`.

## ii. Key results

- `LiebRobinson.Interaction.neighbours` : the non-zero terms meeting a region.
- `LiebRobinson.Interaction.Far` : graph distance to `Y` in the overlap graph of the terms.
- `LiebRobinson.Interaction.norm_commutator_evolution_le_of_far` : the bound for `f_Z`.
- `LiebRobinson.Interaction.lieb_robinson_pow` : the polynomial form of the bound.
- `LiebRobinson.Interaction.lieb_robinson_exp` : the exponential form of the bound.

## iii. Table of contents

- A. Neighbours and distance in the overlap graph
- B. The bound for the interaction terms
- C. The Lieb–Robinson bound

## iv. References

* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
-/

@[expose] public section

namespace LiebRobinson

variable {𝔄 : Type*} [CStarAlgebra 𝔄] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  {N : LocalNet Λ 𝔄}

namespace Interaction

variable (I : Interaction N)

/-!

## A. Neighbours and distance in the overlap graph

-/

open Classical in
/-- The regions `Z'` meeting `Z` whose interaction term is non-zero. -/
noncomputable def neighbours (Z : Finset Λ) : Finset (Finset Λ) :=
  Finset.univ.filter fun Z' => (Z' ∩ Z).Nonempty ∧ I.Φ Z' ≠ 0

/-- `Far Y k Z`: every chain `Z = Z₀, Z₁, …, Zⱼ` of regions with non-zero terms, consecutive regions
overlapping and `Zⱼ` meeting `Y`, has `j ≥ k`. -/
def Far (Y : Finset Λ) : ℕ → Finset Λ → Prop
  | 0, _ => True
  | k + 1, Z => I.Φ Z = 0 ∨ (Disjoint Z Y ∧ ∀ Z', (Z' ∩ Z).Nonempty → Far Y k Z')

/-!

## B. The bound for the interaction terms

-/

/-- The integrated sum over the regions touching `X`, given a bound
`‖[τ_s(Φ_{Z'}), B]‖ ≤ 2 ‖Φ_{Z'}‖ ‖B‖ (2 J κ s)^k / k!` on each region `Z'` meeting `X`. -/
lemma sum_integral_le {X : Finset Λ} {B : 𝔄} {J : ℝ} {κ : ℕ} (hJ0 : 0 ≤ J)
    (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J) (k : ℕ)
    (hf : ∀ Z', (Z' ∩ X).Nonempty → ∀ {s : ℝ}, 0 ≤ s →
      ‖commutator (I.evolution s (I.Φ Z')) B‖ ≤
        2 * ‖I.Φ Z'‖ * ‖B‖ * (2 * J * κ * s) ^ k / k.factorial)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ Z' ∈ touching X, ∫ s in (0 : ℝ)..t, ‖commutator (I.evolution s (I.Φ Z')) B‖ ≤
      (I.neighbours X).card *
        (2 * J * ‖B‖ * (2 * J * κ) ^ k * t ^ (k + 1) / (k + 1).factorial) := by
  have hsub : I.neighbours X ⊆ touching X := by
    intro Z' h
    simp only [neighbours, touching, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact h.1
  rw [← Finset.sum_subset hsub ?_]
  · rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun Z' hZ' => ?_
    have hZ'X : (Z' ∩ X).Nonempty := by
      simp only [neighbours, Finset.mem_filter, Finset.mem_univ, true_and] at hZ'
      exact hZ'.1
    have hc : 0 ≤ 2 * J * κ := by positivity
    calc ∫ s in (0 : ℝ)..t, ‖commutator (I.evolution s (I.Φ Z')) B‖
        ≤ ∫ s in (0 : ℝ)..t, 2 * J * ‖B‖ * (2 * J * κ) ^ k / k.factorial * s ^ k := by
          refine intervalIntegral.integral_mono_on ht
            ((I.continuous_norm_commutator_evolution _ _).intervalIntegrable _ _)
            ((by fun_prop : Continuous fun s : ℝ =>
              2 * J * ‖B‖ * (2 * J * κ) ^ k / k.factorial * s ^ k).intervalIntegrable _ _)
            fun s hs => ?_
          calc ‖commutator (I.evolution s (I.Φ Z')) B‖
              ≤ 2 * ‖I.Φ Z'‖ * ‖B‖ * (2 * J * κ * s) ^ k / k.factorial := hf Z' hZ'X hs.1
            _ ≤ 2 * J * ‖B‖ * (2 * J * κ * s) ^ k / k.factorial := by
              have : 0 ≤ (2 * J * κ * s) ^ k := pow_nonneg (mul_nonneg hc hs.1) k
              gcongr
              exact hJ Z'
            _ = 2 * J * ‖B‖ * (2 * J * κ) ^ k / k.factorial * s ^ k := by ring
      _ = 2 * J * ‖B‖ * (2 * J * κ) ^ k * t ^ (k + 1) / (k + 1).factorial := by
          rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
          push_cast
          field_simp
          ring
  · intro Z' hZ' hn
    have h0 : I.Φ Z' = 0 := by
      simp only [neighbours, touching, Finset.mem_filter, Finset.mem_univ, true_and,
        not_and, not_not] at hZ' hn
      exact hn hZ'
    simp [h0, commutator_zero_left]

/-- If `Z` is at distance at least `k` from `Y` in the overlap graph, then
`‖[τ_t(Φ_Z), B]‖ ≤ 2 ‖Φ_Z‖ ‖B‖ (2 J κ t)^k / k!`. -/
theorem norm_commutator_evolution_le_of_far {Y : Finset Λ} {B : 𝔄} (hB : B ∈ N.alg Y)
    {J : ℝ} {κ : ℕ} (hJ0 : 0 ≤ J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J) (hκ : ∀ Z, (I.neighbours Z).card ≤ κ)
    (k : ℕ) {Z : Finset Λ} (hZ : I.Far Y k Z) {t : ℝ} (ht : 0 ≤ t) :
    ‖commutator (I.evolution t (I.Φ Z)) B‖ ≤
      2 * ‖I.Φ Z‖ * ‖B‖ * (2 * J * κ * t) ^ k / k.factorial := by
  induction k generalizing Z t with
  | zero =>
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    exact (norm_commutator_le _ _).trans (by gcongr; exact I.norm_evolution_le _ _)
  | succ k ih =>
    rcases hZ with h0 | ⟨hZY, hfar⟩
    · simp [h0, commutator_zero_left]
    have h1 := I.norm_commutator_evolution_le (I.mem_alg Z) B ht
    rw [commutator_eq_zero_of_commute (N.commute_of_disjoint hZY _ (I.mem_alg Z) _ hB),
      norm_zero, zero_add] at h1
    have h2 := I.sum_integral_le hJ0 hJ k (fun Z' hZ' _ hs => ih (hfar Z' hZ') hs) ht
    have hg : 0 ≤ 2 * J * ‖B‖ * (2 * J * κ) ^ k * t ^ (k + 1) / (k + 1).factorial := by
      positivity
    calc ‖commutator (I.evolution t (I.Φ Z)) B‖
        ≤ 2 * ‖I.Φ Z‖ * ((I.neighbours Z).card *
          (2 * J * ‖B‖ * (2 * J * κ) ^ k * t ^ (k + 1) / (k + 1).factorial)) := by
          refine h1.trans ?_
          gcongr
      _ ≤ 2 * ‖I.Φ Z‖ * (κ *
          (2 * J * ‖B‖ * (2 * J * κ) ^ k * t ^ (k + 1) / (k + 1).factorial)) := by
          gcongr
          exact_mod_cast hκ Z
      _ = 2 * ‖I.Φ Z‖ * ‖B‖ * (2 * J * κ * t) ^ (k + 1) / (k + 1).factorial := by ring

/-!

## C. The Lieb–Robinson bound

-/

/-- **The Lieb–Robinson bound, polynomial form.** If every region meeting `X` is at distance at
least `n` from `Y` in the overlap graph, then for `t ≥ 0`
`‖[τ_t(A), B]‖ ≤ 2 ‖A‖ ‖B‖ · |neighbours X| · 2 J (2 J κ)^n t^{n+1} / (n+1)!`. -/
theorem lieb_robinson_pow {X Y : Finset Λ} {A B : 𝔄} (hA : A ∈ N.alg X) (hB : B ∈ N.alg Y)
    (hXY : Disjoint X Y) {J : ℝ} {κ : ℕ} (hJ0 : 0 ≤ J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J)
    (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) {n : ℕ}
    (hn : ∀ Z, (Z ∩ X).Nonempty → I.Far Y n Z) {t : ℝ} (ht : 0 ≤ t) :
    ‖commutator (I.evolution t A) B‖ ≤
      2 * ‖A‖ * ‖B‖ * (I.neighbours X).card * (2 * J) * (2 * J * κ) ^ n *
        t ^ (n + 1) / (n + 1).factorial := by
  have h1 := I.norm_commutator_evolution_le hA B ht
  rw [commutator_eq_zero_of_commute (N.commute_of_disjoint hXY _ hA _ hB), norm_zero,
    zero_add] at h1
  have h2 := I.sum_integral_le hJ0 hJ n
    (fun Z hZ _ hs => I.norm_commutator_evolution_le_of_far hB hJ0 hJ hκ n (hn Z hZ) hs) ht
  calc ‖commutator (I.evolution t A) B‖
      ≤ 2 * ‖A‖ * ((I.neighbours X).card *
        (2 * J * ‖B‖ * (2 * J * κ) ^ n * t ^ (n + 1) / (n + 1).factorial)) := by
        refine h1.trans ?_
        gcongr
    _ = _ := by ring

/-- `x^m / m! ≤ e^{e x - m}` for `x ≥ 0`. -/
lemma pow_div_factorial_le_exp_sub {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ m / m.factorial ≤ Real.exp (Real.exp 1 * x - m) := by
  have h := Real.pow_div_factorial_le_exp _ (mul_nonneg (Real.exp_pos 1).le hx) m
  rw [mul_pow, ← Real.exp_nat_mul, mul_one] at h
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  calc x ^ m / m.factorial * Real.exp m = Real.exp m * x ^ m / m.factorial := by ring
    _ ≤ _ := h

/-- **The Lieb–Robinson bound, exponential form.** Under the hypotheses of `lieb_robinson_pow`,
with `κ > 0` and Lieb–Robinson velocity `v = 2 e J κ`,
`‖[τ_t(A), B]‖ ≤ 2 ‖A‖ ‖B‖ (|neighbours X| / κ) e^{v t - (n + 1)}`. -/
theorem lieb_robinson_exp {X Y : Finset Λ} {A B : 𝔄} (hA : A ∈ N.alg X) (hB : B ∈ N.alg Y)
    (hXY : Disjoint X Y) {J : ℝ} {κ : ℕ} (hκ0 : 0 < κ) (hJ0 : 0 ≤ J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J)
    (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) {n : ℕ}
    (hn : ∀ Z, (Z ∩ X).Nonempty → I.Far Y n Z) {t : ℝ} (ht : 0 ≤ t) :
    ‖commutator (I.evolution t A) B‖ ≤
      2 * ‖A‖ * ‖B‖ * ((I.neighbours X).card / κ) *
        Real.exp (2 * Real.exp 1 * J * κ * t - (n + 1)) := by
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ0
  have hx : 0 ≤ 2 * J * κ * t := by positivity
  calc ‖commutator (I.evolution t A) B‖
      ≤ 2 * ‖A‖ * ‖B‖ * (I.neighbours X).card * (2 * J) * (2 * J * κ) ^ n *
        t ^ (n + 1) / (n + 1).factorial := I.lieb_robinson_pow hA hB hXY hJ0 hJ hκ hn ht
    _ = 2 * ‖A‖ * ‖B‖ * ((I.neighbours X).card / κ) *
        ((2 * J * κ * t) ^ (n + 1) / (n + 1).factorial) := by
        field_simp
        ring
    _ ≤ 2 * ‖A‖ * ‖B‖ * ((I.neighbours X).card / κ) *
        Real.exp (Real.exp 1 * (2 * J * κ * t) - (n + 1 : ℕ)) := by
        gcongr
        exact pow_div_factorial_le_exp_sub hx (n + 1)
    _ = _ := by
        push_cast
        ring_nf

end Interaction

end LiebRobinson
