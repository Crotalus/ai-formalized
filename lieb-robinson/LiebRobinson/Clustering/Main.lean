/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import LiebRobinson.Clustering.Filter
public import LiebRobinson.Clustering.Spectral
public import LiebRobinson.Metric
/-!

# Exponential clustering in gapped ground states

In a quantum lattice system with a unique gapped ground state, connected correlations of local
observables decay exponentially with distance.

## i. Overview

Let the observables act on a finite-dimensional Hilbert space `ℋ`, so `𝔄 = ℋ →L[ℂ] ℋ`, and let
the Hamiltonian of a local interaction have a unique ground state `Ω` with spectral gap `γ`. For
`A ∈ 𝔄_X` and `B ∈ 𝔄_Y` with `X`, `Y` disjoint, the function `F(t) = ⟪Ω, [τ_t(A), B] Ω⟫` has the
spectral expansion of `Spectral`, with positive-frequency part summing to the connected
correlation `⟨AB⟩ - ⟨A⟩⟨B⟩`. The Lieb–Robinson bound gives `|F(t)| ≤ K₂ |t|^{n+1}`, and always
`|F| ≤ 2 ‖A‖ ‖B‖`, so the filter estimate of `Filter` bounds the correlation. Choosing the
filter parameters `T = (n + 1) / (4 e J κ)` and `α = γ / (2 T)` gives

$$|⟨AB⟩ - ⟨A⟩⟨B⟩| ≤ \frac{2}{π} ‖A‖ ‖B‖ \left( \frac{n_X}{κ} e^{-(n+1)/2}
  + \left( \frac{4 e J κ}{γ} + \sqrt{\frac{2 π e J κ}{γ}} \right)
  e^{-γ (n+1) / (8 e J κ)} \right),$$

and, on a metric lattice with range `R`, decay at rate `min(1/2, γ / (8 e J κ)) / R` in the
distance.

## ii. Key results

- `LiebRobinson.Interaction.norm_corr_le_of_far` : the bound with free filter parameters.
- `LiebRobinson.Interaction.exponential_clustering` : exponential decay in the graph distance.
- `LiebRobinson.Interaction.exponential_clustering_dist` : exponential decay in the distance.

## iii. Table of contents

- A. The bound with free parameters
- B. Exponential clustering

## iv. References

* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
* M. B. Hastings and T. Koma, *Spectral gap and exponential decay of correlations*,
  Comm. Math. Phys. 265 (2006), 781–804.
-/

@[expose] public section

namespace LiebRobinson

open scoped InnerProductSpace

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [FiniteDimensional ℂ ℋ] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  {N : LocalNet Λ (ℋ →L[ℂ] ℋ)}

namespace Interaction

variable (I : Interaction N)

/-!

## A. The bound with free parameters

-/

omit [FiniteDimensional ℂ ℋ] [Fintype Λ] in
/-- `-Φ` and `Φ` have the same distances in the overlap graph. -/
lemma far_neg (Y : Finset Λ) (k : ℕ) (Z : Finset Λ) : I.neg.Far Y k Z ↔ I.Far Y k Z := by
  induction k generalizing Z with
  | zero => exact Iff.rfl
  | succ k ih =>
    simp only [Far, ih]
    simp [neg]

omit [FiniteDimensional ℂ ℋ] in
/-- The polynomial Lieb–Robinson bound for all times: under the hypotheses of
`lieb_robinson_pow`, for every real `t`,
`‖[τ_t(A), B]‖ ≤ 2 ‖A‖ ‖B‖ |neighbours X| 2J (2Jκ)^n / (n+1)! · |t|^{n+1}`. -/
lemma lieb_robinson_pow_abs {X Y : Finset Λ} {A B : ℋ →L[ℂ] ℋ} (hA : A ∈ N.alg X)
    (hB : B ∈ N.alg Y) (hXY : Disjoint X Y) {J : ℝ} {κ : ℕ} (hJ0 : 0 ≤ J)
    (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J) (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) {n : ℕ}
    (hn : ∀ Z, (Z ∩ X).Nonempty → I.Far Y n Z) (t : ℝ) :
    ‖commutator (I.evolution t A) B‖ ≤
      2 * ‖A‖ * ‖B‖ * (I.neighbours X).card * (2 * J) * (2 * J * κ) ^ n /
        (n + 1).factorial * |t| ^ (n + 1) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    calc _ ≤ _ := I.lieb_robinson_pow hA hB hXY hJ0 hJ hκ hn ht
      _ = _ := by ring
  · have h := I.neg.lieb_robinson_pow hA hB hXY hJ0 (fun Z => by simpa [neg] using hJ Z)
      (by simpa [neighbours_neg] using hκ) (fun Z hZ => (I.far_neg Y n Z).mpr (hn Z hZ))
      (neg_nonneg.mpr ht)
    rw [evolution_neg, neg_neg, neighbours_neg] at h
    rw [abs_of_nonpos ht]
    calc _ ≤ _ := h
      _ = _ := by ring

/-- **Clustering with free filter parameters.** For a gapped ground state and observables in
disjoint regions `X`, `Y` with every region meeting `X` at distance at least `n` from `Y` in the
overlap graph, for all `α, T > 0`, with `K = 2 ‖A‖ ‖B‖ |neighbours X| 2J (2Jκ)^n / (n+1)!`,
`|⟨AB⟩ - ⟨A⟩⟨B⟩| ≤ (2 K T^{n+1} / (n+1) + 2 ‖A‖ ‖B‖ e^{-αT²} / (αT²)
  + 2 ‖A‖ ‖B‖ (2 √(πα) / γ) e^{-γ²/(4α)}) / (2π)`. -/
theorem norm_corr_le_of_far {γ : ℝ} (hγ : 0 < γ) (G : GappedGroundState I.hamiltonian γ)
    {X Y : Finset Λ} {A B : ℋ →L[ℂ] ℋ} (hA : A ∈ N.alg X) (hB : B ∈ N.alg Y)
    (hXY : Disjoint X Y) {J : ℝ} {κ : ℕ} (hJ0 : 0 ≤ J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J)
    (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) {n : ℕ}
    (hn : ∀ Z, (Z ∩ X).Nonempty → I.Far Y n Z) {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    ‖G.corr A B‖ ≤
      (2 * (2 * ‖A‖ * ‖B‖ * (I.neighbours X).card * (2 * J) * (2 * J * κ) ^ n /
          (n + 1).factorial) * T ^ (n + 1) / (n + 1) +
        2 * ‖A‖ * ‖B‖ * Real.exp (-α * T ^ 2) / (α * T ^ 2) +
        2 * (‖A‖ * ‖B‖) *
          (2 * Real.sqrt (Real.pi * α) / γ * Real.exp (-γ ^ 2 / (4 * α)))) / (2 * Real.pi) := by
  obtain ⟨m, ω, c, d, hω, hc, hd, hcorr, h0, hF⟩ :=
    G.exists_expansion I.isSelfAdjoint_hamiltonian A B
  have hcomm : commutator A B = 0 :=
    commutator_eq_zero_of_commute (N.commute_of_disjoint hXY _ hA _ hB)
  rw [hcomm] at h0 hF
  simp only [zero_apply, inner_zero_right, zero_add] at h0 hF
  have hcd : ∑ i, c i = ∑ i, d i := sub_eq_zero.mp h0.symm
  have h := norm_sum_le_of_filter hγ ω hω c d hcd hc hd
    (fun t => ⟪G.Ω, (commutator (I.evolution t A) B) G.Ω⟫_ℂ) hF (m := n + 1) (by omega)
    (K₁ := 2 * ‖A‖ * ‖B‖)
    (fun t => (G.norm_inner_le _).trans ((norm_commutator_le _ _).trans
      (by gcongr; exact I.norm_evolution_le t A)))
    (fun t => (G.norm_inner_le _).trans (I.lieb_robinson_pow_abs hA hB hXY hJ0 hJ hκ hn t))
    hα hT
  rw [hcorr]
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

/-!

## B. Exponential clustering

-/

/-- **The exponential clustering theorem.** For a gapped ground state, observables in disjoint
regions with every region meeting `X` at distance at least `n` from `Y` in the overlap graph, and
an interaction of strength `J > 0` and coordination `κ > 0`,
`|⟨AB⟩ - ⟨A⟩⟨B⟩| ≤ (2/π) ‖A‖ ‖B‖ ((n_X/κ) e^{-(n+1)/2}
  + (4eJκ/γ + √(2πeJκ/γ)) e^{-γ(n+1)/(8eJκ)})`. -/
theorem exponential_clustering {γ : ℝ} (hγ : 0 < γ) (G : GappedGroundState I.hamiltonian γ)
    {X Y : Finset Λ} {A B : ℋ →L[ℂ] ℋ} (hA : A ∈ N.alg X) (hB : B ∈ N.alg Y)
    (hXY : Disjoint X Y) {J : ℝ} {κ : ℕ} (hκ0 : 0 < κ) (hJ0 : 0 < J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J)
    (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) {n : ℕ}
    (hn : ∀ Z, (Z ∩ X).Nonempty → I.Far Y n Z) :
    ‖G.corr A B‖ ≤ 2 / Real.pi * ‖A‖ * ‖B‖ *
      ((I.neighbours X).card / κ * Real.exp (-(n + 1) / 2) +
        (4 * Real.exp 1 * J * κ / γ + Real.sqrt (2 * Real.pi * Real.exp 1 * J * κ / γ)) *
          Real.exp (-γ * (n + 1) / (8 * Real.exp 1 * J * κ))) := by
  have hk : (0 : ℝ) < κ := by exact_mod_cast hκ0
  have he := Real.exp_pos 1
  have hπ := Real.pi_pos
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hab : 0 ≤ ‖A‖ * ‖B‖ := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (n + 1) / (4 * Real.exp 1 * J * κ) := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = γ / (2 * T) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  set E := Real.exp (-γ * (n + 1) / (8 * Real.exp 1 * J * κ)) with hE
  have hαT : α * T ^ 2 = γ * (n + 1) / (8 * Real.exp 1 * J * κ) := by
    rw [hα, hT]; field_simp; ring
  have hE₂ : Real.exp (-α * T ^ 2) = E := by
    rw [hE, neg_mul, hαT]; congr 1; ring
  have hE₃ : Real.exp (-γ ^ 2 / (4 * α)) = E := by
    rw [hE]; congr 1; rw [hα, hT]; field_simp; ring
  have hx : Real.exp 1 * (2 * J * κ * T) - ((n + 1 : ℕ) : ℝ) = -(n + 1) / 2 := by
    rw [hT]; push_cast; field_simp; ring
  have hαle : α ≤ 2 * Real.exp 1 * J * κ * γ := by
    have : α = 2 * Real.exp 1 * J * κ * γ / (n + 1) := by rw [hα, hT]; field_simp; ring
    rw [this]
    exact div_le_self (by positivity) hn1
  have hsq : Real.sqrt (2 * Real.pi * Real.exp 1 * J * κ / γ) =
      Real.sqrt (Real.pi * (2 * Real.exp 1 * J * κ * γ)) / γ := by
    rw [show 2 * Real.pi * Real.exp 1 * J * κ / γ =
        Real.pi * (2 * Real.exp 1 * J * κ * γ) / γ ^ 2 by field_simp,
      Real.sqrt_div' _ (sq_nonneg γ), Real.sqrt_sq hγ.le]
  have h₁ : 2 * (2 * ‖A‖ * ‖B‖ * (I.neighbours X).card * (2 * J) * (2 * J * κ) ^ n /
      (n + 1).factorial) * T ^ (n + 1) / (n + 1) ≤
      4 * (‖A‖ * ‖B‖) * ((I.neighbours X).card / κ * Real.exp (-(n + 1) / 2)) := by
    have hy : 0 ≤ (2 * J * κ * T) ^ (n + 1) / (n + 1).factorial := by positivity
    calc _ = 4 * (‖A‖ * ‖B‖) * ((I.neighbours X).card / κ) *
          ((2 * J * κ * T) ^ (n + 1) / (n + 1).factorial) / (n + 1) := by
          field_simp
          ring
      _ ≤ 4 * (‖A‖ * ‖B‖) * ((I.neighbours X).card / κ) *
          ((2 * J * κ * T) ^ (n + 1) / (n + 1).factorial) :=
          div_le_self (by positivity) hn1
      _ ≤ 4 * (‖A‖ * ‖B‖) * ((I.neighbours X).card / κ) *
          Real.exp (Real.exp 1 * (2 * J * κ * T) - ((n + 1 : ℕ) : ℝ)) := by
          gcongr
          exact pow_div_factorial_le_exp_sub (by positivity) (n + 1)
      _ = _ := by rw [hx]; ring
  have h₂ : 2 * ‖A‖ * ‖B‖ * Real.exp (-α * T ^ 2) / (α * T ^ 2) ≤
      4 * (‖A‖ * ‖B‖) * (4 * Real.exp 1 * J * κ / γ * E) := by
    have hs : 0 < α * T ^ 2 := by positivity
    have hE0 : 0 < E := Real.exp_pos _
    rw [hE₂, div_le_iff₀ hs]
    calc 2 * ‖A‖ * ‖B‖ * E = 2 * (‖A‖ * ‖B‖) * E * 1 := by ring
      _ ≤ 2 * (‖A‖ * ‖B‖) * E * (n + 1) := by gcongr
      _ = _ := by rw [hαT]; field_simp; ring
  have h₃ : 2 * (‖A‖ * ‖B‖) *
      (2 * Real.sqrt (Real.pi * α) / γ * Real.exp (-γ ^ 2 / (4 * α))) ≤
      4 * (‖A‖ * ‖B‖) * (Real.sqrt (2 * Real.pi * Real.exp 1 * J * κ / γ) * E) := by
    rw [hE₃, hsq]
    have hE0 : 0 < E := Real.exp_pos _
    calc _ = 4 * (‖A‖ * ‖B‖) * (Real.sqrt (Real.pi * α) / γ * E) := by ring
      _ ≤ _ := by gcongr
  refine (I.norm_corr_le_of_far hγ G hA hB hXY hJ0.le hJ hκ hn hα0 hT0).trans ?_
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by field_simp; ring

omit [FiniteDimensional ℂ ℋ] [Fintype Λ] in
/-- On a metric lattice with interaction range `R > 0`, supports at distance at least `d > 0` are
disjoint, and every region meeting `X` is at distance at least `n` from `Y` in the overlap graph
for some `n` with `d / R ≤ n + 2`. -/
lemma exists_far_of_dist [PseudoMetricSpace Λ] {X Y : Finset Λ} {R d : ℝ} (hR0 : 0 < R)
    (hR : ∀ Z, I.Φ Z ≠ 0 → ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ R)
    (hd0 : 0 < d) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) :
    Disjoint X Y ∧ ∃ n : ℕ, d / R ≤ n + 2 ∧ ∀ Z, (Z ∩ X).Nonempty → I.Far Y n Z := by
  have hq : 0 < d / R := div_pos hd0 hR0
  have hceil := Nat.ceil_lt_add_one (R := ℝ) hq.le
  have hle := Nat.le_ceil (d / R)
  obtain ⟨n, hn_def⟩ : ∃ n, n = ⌈d / R⌉₊ - 2 := ⟨_, rfl⟩
  have hn2 : (⌈d / R⌉₊ : ℝ) ≤ n + 2 := by exact_mod_cast (by omega : ⌈d / R⌉₊ ≤ n + 2)
  refine ⟨Finset.disjoint_left.mpr fun x hx hxY => ?_, n, hle.trans hn2, ?_⟩
  · have h := hd x hx x hxY
    rw [dist_self] at h
    linarith
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

/-- **Exponential clustering on a metric lattice.** Under the hypotheses of `lieb_robinson`, for a
gapped ground state, connected correlations decay exponentially in the distance `d` between the
supports, at rate `min(1/2, γ / (8eJκ)) / R`. -/
theorem exponential_clustering_dist [PseudoMetricSpace Λ] {γ : ℝ} (hγ : 0 < γ)
    (G : GappedGroundState I.hamiltonian γ) {X Y : Finset Λ} {A B : ℋ →L[ℂ] ℋ}
    (hA : A ∈ N.alg X) (hB : B ∈ N.alg Y) {J R d : ℝ} {κ : ℕ} (hκ0 : 0 < κ) (hJ0 : 0 < J)
    (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J) (hκ : ∀ Z, (I.neighbours Z).card ≤ κ) (hR0 : 0 < R)
    (hR : ∀ Z, I.Φ Z ≠ 0 → ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ R)
    (hd0 : 0 < d) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) :
    ‖G.corr A B‖ ≤ 2 / Real.pi * ‖A‖ * ‖B‖ *
      ((I.neighbours X).card / κ * Real.exp (1 / 2) * Real.exp (-d / (2 * R)) +
        (4 * Real.exp 1 * J * κ / γ + Real.sqrt (2 * Real.pi * Real.exp 1 * J * κ / γ)) *
          Real.exp (γ / (8 * Real.exp 1 * J * κ)) *
          Real.exp (-γ * d / (8 * Real.exp 1 * J * κ * R))) := by
  obtain ⟨hXY, n, hdn, hn⟩ := I.exists_far_of_dist hR0 hR hd0 hd
  have hk : (0 : ℝ) < κ := by exact_mod_cast hκ0
  have he := Real.exp_pos 1
  have hπ := Real.pi_pos
  have h₁ : Real.exp (-(n + 1) / 2) ≤ Real.exp (1 / 2) * Real.exp (-d / (2 * R)) := by
    rw [← Real.exp_add, Real.exp_le_exp,
      show -d / (2 * R) = -(d / R) / 2 by field_simp]
    linarith
  have h₂ : Real.exp (-γ * (n + 1) / (8 * Real.exp 1 * J * κ)) ≤
      Real.exp (γ / (8 * Real.exp 1 * J * κ)) *
        Real.exp (-γ * d / (8 * Real.exp 1 * J * κ * R)) := by
    have hu : 0 ≤ γ / (8 * Real.exp 1 * J * κ) := by positivity
    have key := mul_le_mul_of_nonneg_left hdn hu
    rw [← Real.exp_add, Real.exp_le_exp,
      show -γ * (n + 1) / (8 * Real.exp 1 * J * κ) =
        -(γ / (8 * Real.exp 1 * J * κ) * (n + 1)) by ring,
      show -γ * d / (8 * Real.exp 1 * J * κ * R) =
        -(γ / (8 * Real.exp 1 * J * κ) * (d / R)) by field_simp]
    linarith
  calc _ ≤ _ := I.exponential_clustering hγ G hA hB hXY hκ0 hJ0 hJ hκ hn
    _ ≤ 2 / Real.pi * ‖A‖ * ‖B‖ *
      ((I.neighbours X).card / κ * (Real.exp (1 / 2) * Real.exp (-d / (2 * R))) +
        (4 * Real.exp 1 * J * κ / γ + Real.sqrt (2 * Real.pi * Real.exp 1 * J * κ / γ)) *
          (Real.exp (γ / (8 * Real.exp 1 * J * κ)) *
            Real.exp (-γ * d / (8 * Real.exp 1 * J * κ * R)))) := by gcongr
    _ = _ := by ring

end Interaction

end LiebRobinson
