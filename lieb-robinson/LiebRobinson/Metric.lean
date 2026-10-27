/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import LiebRobinson.Iteration
/-!

# The Lieb–Robinson bound on a metric lattice

For interactions of finite range on a set of sites with a metric, the commutator of observables
at distance `d` is exponentially small in `d` until time of order `d / v`.

## i. Overview

If every non-zero interaction term has diameter at most `R`, a chain of `j + 1` overlapping terms
spans a distance of at most `(j + 1) R`. Hence regions at distance `d` from `Y` are `Far` from `Y`
for chains of length about `d / R`, and the exponential form of the bound becomes

$$‖[τ_t(A), B]‖ ≤ 2 e ‖A‖ ‖B‖ \frac{|\mathrm{neighbours}\,X|}{κ} e^{v t - d / R},
  \qquad v = 2 e J κ.$$

The constants depend only on the strength `J`, the range `R`, the local coordination `κ` of the
interaction and the number of terms meeting `X`, not on the size of the lattice.

## ii. Key results

- `LiebRobinson.Interaction.far_of_dist` : distance in the metric bounds distance in the overlap
  graph.
- `LiebRobinson.Interaction.lieb_robinson` : the Lieb–Robinson bound for `t ≥ 0`.
- `LiebRobinson.Interaction.lieb_robinson_abs` : the bound `e^{v |t| - d / R}` for all times.

## iii. Table of contents

- A. Distance in the overlap graph
- B. The Lieb–Robinson bound
- C. Negative times

## iv. References

* E. H. Lieb and D. W. Robinson, *The finite group velocity of quantum spin systems*,
  Comm. Math. Phys. 28 (1972), 251–257.
* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
-/

@[expose] public section

namespace LiebRobinson

variable {𝔄 : Type*} [CStarAlgebra 𝔄] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  [PseudoMetricSpace Λ] {N : LocalNet Λ 𝔄}

namespace Interaction

variable (I : Interaction N)

/-!

## A. Distance in the overlap graph

-/

omit [Fintype Λ] in
/-- If the non-zero terms have diameter at most `R ≥ 0` and every point of `Z` is at distance
more than `k R` from `Y`, then `Z` is at distance at least `k` from `Y` in the overlap graph. -/
lemma far_of_dist {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ Z, I.Φ Z ≠ 0 → ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ R) {Y : Finset Λ} (k : ℕ)
    {Z : Finset Λ} (hZ : ∀ z ∈ Z, ∀ y ∈ Y, k * R < dist z y) : I.Far Y k Z := by
  induction k generalizing Z with
  | zero => exact trivial
  | succ k ih =>
    by_cases h0 : I.Φ Z = 0
    · exact Or.inl h0
    refine Or.inr ⟨Finset.disjoint_left.mpr fun z hz hzY => ?_, fun Z' hZ' => ?_⟩
    · have h := hZ z hz z hzY
      rw [dist_self] at h
      have : (0 : ℝ) ≤ (k + 1 : ℕ) * R := by positivity
      linarith
    by_cases h0' : I.Φ Z' = 0
    · cases k with
      | zero => exact trivial
      | succ j => exact Or.inl h0'
    refine ih fun z' hz' y hy => ?_
    obtain ⟨w, hw⟩ := hZ'
    rw [Finset.mem_inter] at hw
    have h1 := hR Z' h0' w hw.1 z' hz'
    have h2 := hZ w hw.2 y hy
    have h3 := dist_triangle w z' y
    push_cast at h2
    linarith

/-!

## B. The Lieb–Robinson bound

-/

/-- **The Lieb–Robinson bound.** Let the interaction have strength `‖Φ_Z‖ ≤ J`, range `R > 0`
(non-zero terms have diameter at most `R`) and coordination `κ > 0` (at most `κ` non-zero terms
meet any region). If every point of `X` is at distance at least `d > 0` from every point of `Y`,
then for `A ∈ 𝔄_X`, `B ∈ 𝔄_Y` and `t ≥ 0`,
`‖[τ_t(A), B]‖ ≤ 2 e ‖A‖ ‖B‖ (|neighbours X| / κ) e^{v t - d / R}` with `v = 2 e J κ`. -/
theorem lieb_robinson {X Y : Finset Λ} {A B : 𝔄} (hA : A ∈ N.alg X) (hB : B ∈ N.alg Y)
    {J R d : ℝ} {κ : ℕ} (hκ0 : 0 < κ) (hJ0 : 0 ≤ J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J)
    (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) (hR0 : 0 < R)
    (hR : ∀ Z, I.Φ Z ≠ 0 → ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ R)
    (hd0 : 0 < d) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) {t : ℝ} (ht : 0 ≤ t) :
    ‖commutator (I.evolution t A) B‖ ≤
      2 * Real.exp 1 * ‖A‖ * ‖B‖ * ((I.neighbours X).card / κ) *
        Real.exp (2 * Real.exp 1 * J * κ * t - d / R) := by
  have hq : 0 < d / R := div_pos hd0 hR0
  have hceil := Nat.ceil_lt_add_one (R := ℝ) hq.le
  have hle := Nat.le_ceil (d / R)
  obtain ⟨n, hn_def⟩ : ∃ n, n = ⌈d / R⌉₊ - 2 := ⟨_, rfl⟩
  have hn2 : (⌈d / R⌉₊ : ℝ) ≤ n + 2 := by exact_mod_cast (by omega : ⌈d / R⌉₊ ≤ n + 2)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr fun x hx hxY => by
    have h := hd x hx x hxY
    rw [dist_self] at h
    linarith
  have hn : ∀ Z, (Z ∩ X).Nonempty → I.Far Y n Z := by
    intro Z hZX
    cases n with
    | zero => exact trivial
    | succ j =>
      by_cases h0 : I.Φ Z = 0
      · exact Or.inl h0
      refine far_of_dist I hR0.le hR _ fun z hz y hy => ?_
      obtain ⟨x, hx⟩ := hZX
      rw [Finset.mem_inter] at hx
      have h1 := hR Z h0 x hx.1 z hz
      have h2 := hd x hx.2 y hy
      have h3 := dist_triangle x z y
      have h4 : (j + 3 : ℝ) < d / R + 1 := by
        have : ⌈d / R⌉₊ = j + 3 := by omega
        rw [this] at hceil
        push_cast at hceil
        exact hceil
      have h5 : (j + 2 : ℝ) < d / R := by linarith
      rw [lt_div_iff₀ hR0] at h5
      push_cast
      linarith
  calc ‖commutator (I.evolution t A) B‖
      ≤ 2 * ‖A‖ * ‖B‖ * ((I.neighbours X).card / κ) *
        Real.exp (2 * Real.exp 1 * J * κ * t - (n + 1)) :=
        I.lieb_robinson_exp hA hB hXY hκ0 hJ0 hJ hκ hn ht
    _ ≤ 2 * ‖A‖ * ‖B‖ * ((I.neighbours X).card / κ) *
        (Real.exp 1 * Real.exp (2 * Real.exp 1 * J * κ * t - d / R)) := by
        gcongr
        rw [← Real.exp_add, Real.exp_le_exp]
        linarith
    _ = _ := by ring

/-!

## C. Negative times

-/

/-- The interaction `-Φ`, which generates the same dynamics backwards in time. -/
def neg : Interaction N where
  Φ Z := -I.Φ Z
  mem_alg Z := neg_mem (I.mem_alg Z)
  isSelfAdjoint Z := (I.isSelfAdjoint Z).neg

omit [DecidableEq Λ] [PseudoMetricSpace Λ] in
/-- The Hamiltonian of `-Φ` is `-H`. -/
lemma hamiltonian_neg : I.neg.hamiltonian = -I.hamiltonian := by
  simp [hamiltonian, neg, Finset.sum_neg_distrib]

omit [DecidableEq Λ] [PseudoMetricSpace Λ] in
/-- The dynamics of `-Φ` is the dynamics of `Φ` run backwards. -/
lemma evolution_neg (t : ℝ) (A : 𝔄) : I.neg.evolution t A = I.evolution (-t) A := by
  simp [evolution, expI, hamiltonian_neg, smul_neg, neg_smul]

omit [PseudoMetricSpace Λ] in
/-- `-Φ` and `Φ` have the same non-zero terms. -/
lemma neighbours_neg : I.neg.neighbours = I.neighbours := by
  funext Z
  ext Z'
  simp only [neighbours, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [neg]

/-- **The Lieb–Robinson bound for all times.** Under the hypotheses of `lieb_robinson`, for every
real `t`, `‖[τ_t(A), B]‖ ≤ 2 e ‖A‖ ‖B‖ (|neighbours X| / κ) e^{v |t| - d / R}`. -/
theorem lieb_robinson_abs {X Y : Finset Λ} {A B : 𝔄} (hA : A ∈ N.alg X) (hB : B ∈ N.alg Y)
    {J R d : ℝ} {κ : ℕ} (hκ0 : 0 < κ) (hJ0 : 0 ≤ J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J)
    (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) (hR0 : 0 < R)
    (hR : ∀ Z, I.Φ Z ≠ 0 → ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ R)
    (hd0 : 0 < d) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) (t : ℝ) :
    ‖commutator (I.evolution t A) B‖ ≤
      2 * Real.exp 1 * ‖A‖ * ‖B‖ * ((I.neighbours X).card / κ) *
        Real.exp (2 * Real.exp 1 * J * κ * |t| - d / R) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact I.lieb_robinson hA hB hκ0 hJ0 hJ hκ hR0 hR hd0 hd ht
  · have h := I.neg.lieb_robinson hA hB hκ0 hJ0 (fun Z => by simpa [neg] using hJ Z)
      (by simpa [neighbours_neg] using hκ) hR0 (fun Z hZ => hR Z (by simpa [neg] using hZ))
      hd0 hd (neg_nonneg.mpr ht)
    rwa [evolution_neg, neg_neg, neighbours_neg, ← abs_of_nonpos ht] at h

end Interaction

end LiebRobinson
