/-
Copyright (c) 2026 Nichlas Löfdahl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nichlas Löfdahl
-/
module

public import LiebRobinson.Metric
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Interaction
/-!

# The Lieb–Robinson bound for a lattice spin system

The abstract theory applies to the concrete lattice model of Physlib: the operators of a finite box
of an arbitrary, possibly infinite, set of sites.

## i. Overview

In Physlib the operators of a finite region `X` of the sites are the matrices `Alg Ω X` on the
configurations of `X`, and a larger region `Λ ⊇ X` contains them through `M ↦ M ⊗ 1`. Operators
lifted from disjoint regions commute: the product of `M ⊗ 1` and `1 ⊗ N` has the explicit entries
`M_{c c''} N_{c c''}` on pairs of configurations agreeing outside `X ∪ Y`, in either order.

Fix a finite box `Λ₀`. With the operator norm of `ℓ²` on configurations, `Alg Ω Λ₀` is a
C*-algebra, and the lifts of the operators of the regions `X ⊆ Λ₀` form a local net on the sites
of `Λ₀`. An interaction of Physlib restricts to an interaction on this net whose Hamiltonian is
the Physlib Hamiltonian `H_{Λ₀} = ∑_{X ⊆ Λ₀} Φ X ⊗ 1` of the box, and the Lieb–Robinson bound
holds for its dynamics, with constants independent of the box.

## ii. Key results

- `CondensedMatter.QuasiLocal.commute_inclMat_of_disjoint` : lifts from disjoint regions commute.
- `CondensedMatter.QuasiLocal.boxNet` : the local net of a finite box.
- `CondensedMatter.QuasiLocal.Interaction.toBox` : an interaction restricted to a finite box.
- `CondensedMatter.QuasiLocal.Interaction.hamiltonian_toBox` : its Hamiltonian is the Physlib
  Hamiltonian of the box.
- `CondensedMatter.QuasiLocal.Interaction.lieb_robinson` : the Lieb–Robinson bound in a box.

## iii. Table of contents

- A. Lifts from disjoint regions commute
- B. The local net of a finite box
- C. Interactions in a finite box
- D. The Lieb–Robinson bound in a finite box

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.2.
* B. Nachtergaele and R. Sims, *Lieb–Robinson bounds and the exponential clustering theorem*,
  Comm. Math. Phys. 265 (2006), 119–130.
-/

@[expose] public section

namespace CondensedMatter

namespace QuasiLocal

open scoped Matrix Matrix.Norms.L2Operator

variable {S : Type*} [DecidableEq S]
variable {Ω : S → Type*} [∀ s, Fintype (Ω s)] [∀ s, DecidableEq (Ω s)]

/-!

## A. Lifts from disjoint regions commute

-/

omit [∀ s, Fintype (Ω s)] [∀ s, DecidableEq (Ω s)] in
/-- For disjoint `X, Y ⊆ Λ`, the only configuration `c'` agreeing with `c` outside `X` and with
`c''` outside `Y` is `c''` on `X` and `c` elsewhere. -/
lemma glue_restr_eq_of_agree {X Y Λ : Finset S} (hX : X ≤ Λ) (hY : Y ≤ Λ) (hd : Disjoint X Y)
    {c c' c'' : Cfg Ω Λ} (h₁ : Agree hX c c') (h₂ : Agree hY c' c'') :
    c' = glue hX c (restr hX c'') := by
  funext y
  by_cases hy : y.1 ∈ X
  · simp only [glue, hy, ↓reduceDIte]
    exact h₂ y (Finset.disjoint_left.mp hd hy)
  · simp only [glue, hy, ↓reduceDIte]
    exact (h₁ y hy).symm

/-- For disjoint `X, Y ⊆ Λ`, the product `(M ⊗ 1) (1 ⊗ N)` has the entry `M_{c c''} N_{c c''}`
(restricted to `X` and `Y` respectively) on configurations agreeing outside `X ∪ Y`, and `0` on
the others. -/
lemma inclMat_mul_inclMat_of_disjoint {X Y Λ : Finset S} (hX : X ≤ Λ) (hY : Y ≤ Λ)
    (hd : Disjoint X Y) (M : Alg Ω X) (N : Alg Ω Y) :
    inclMat hX M * inclMat hY N = Matrix.of fun c c'' =>
      if ∀ y : ↥Λ, y.1 ∉ X → y.1 ∉ Y → c y = c'' y then
        M (restr hX c) (restr hX c'') * N (restr hY c) (restr hY c'')
      else 0 := by
  ext c c''
  rw [Matrix.mul_apply, Finset.sum_eq_single (glue hX c (restr hX c''))]
  · have hag : Agree hX c (glue hX c (restr hX c'')) := agree_glue hX c _
    have hrY : restr hY (glue hX c (restr hX c'')) = restr hY c := by
      funext y
      simp [glue, Finset.disjoint_right.mp hd y.2]
    have hiff : Agree hY (glue hX c (restr hX c'')) c'' ↔
        ∀ y : ↥Λ, y.1 ∉ X → y.1 ∉ Y → c y = c'' y := by
      refine ⟨fun h y hyX hyY => ?_, fun h y hyY => ?_⟩
      · simpa [glue, hyX] using h y hyY
      · by_cases hyX : y.1 ∈ X
        · simp [glue, hyX]
        · simpa [glue, hyX] using h y hyX hyY
    simp only [inclMat_apply, hag, ↓reduceIte, restr_glue, hrY, Matrix.of_apply]
    by_cases h : ∀ y : ↥Λ, y.1 ∉ X → y.1 ∉ Y → c y = c'' y
    · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
    · rw [ite_eq_right (mt hiff.1 h), ite_eq_right h, mul_zero]
  · intro c' _ hc'
    simp only [inclMat_apply]
    by_cases h₁ : Agree hX c c'
    · by_cases h₂ : Agree hY c' c''
      · exact absurd (glue_restr_eq_of_agree hX hY hd h₁ h₂) hc'
      · simp [h₂]
    · simp [h₁]
  · simp

/-- **Lifts of operators of disjoint regions commute.** -/
lemma commute_inclMat_of_disjoint {X Y Λ : Finset S} (hX : X ≤ Λ) (hY : Y ≤ Λ)
    (hd : Disjoint X Y) (M : Alg Ω X) (N : Alg Ω Y) :
    Commute (inclMat hX M) (inclMat hY N) := by
  change inclMat hX M * inclMat hY N = inclMat hY N * inclMat hX M
  rw [inclMat_mul_inclMat_of_disjoint hX hY hd, inclMat_mul_inclMat_of_disjoint hY hX hd.symm]
  ext c c''
  simp only [Matrix.of_apply]
  by_cases h : ∀ y : ↥Λ, y.1 ∉ X → y.1 ∉ Y → c y = c'' y
  · have h' : ∀ y : ↥Λ, y.1 ∉ Y → y.1 ∉ X → c y = c'' y := fun y hY hX => h y hX hY
    rw [ite_eq_left h, ite_eq_left h', mul_comm]
  · have h' : ¬∀ y : ↥Λ, y.1 ∉ Y → y.1 ∉ X → c y = c'' y := fun h' => h fun y hX hY => h' y hY hX
    rw [ite_eq_right h, ite_eq_right h']

/-!

## B. The local net of a finite box

-/

/-- The region of the sites of `S` underlying a region of the sites of a box. -/
def boxRegion {Λ₀ : Finset S} (X : Finset ↥Λ₀) : Finset S := X.map (Function.Embedding.subtype _)

omit [DecidableEq S] in
/-- A site of the box lies in the underlying region of `X` exactly when it lies in `X`. -/
lemma mem_boxRegion {Λ₀ : Finset S} {X : Finset ↥Λ₀} {x : ↥Λ₀} : x.1 ∈ boxRegion X ↔ x ∈ X :=
  Finset.mem_map' _

omit [DecidableEq S] in
/-- The underlying region of a region of a box lies in the box. -/
lemma boxRegion_subset {Λ₀ : Finset S} (X : Finset ↥Λ₀) : boxRegion X ⊆ Λ₀ := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  exact y.2

omit [DecidableEq S] in
/-- Disjoint regions of a box have disjoint underlying regions. -/
lemma disjoint_boxRegion {Λ₀ : Finset S} {X Y : Finset ↥Λ₀} (h : Disjoint X Y) :
    Disjoint (boxRegion X) (boxRegion Y) :=
  (Finset.disjoint_map _).2 h

/-- The regions of a box `Λ₀` are the subsets of `Λ₀`. -/
def boxRegionEquiv (Λ₀ : Finset S) : Finset ↥Λ₀ ≃ ↥Λ₀.powerset where
  toFun X := ⟨boxRegion X, Finset.mem_powerset.2 (boxRegion_subset X)⟩
  invFun Z := Z.1.subtype (· ∈ Λ₀)
  left_inv X := by ext x; simp [mem_boxRegion]
  right_inv Z := Subtype.ext (Finset.subtype_map_of_mem fun _ hx => Finset.mem_powerset.1 Z.2 hx)

variable (Ω) in
/-- **The local net of a finite box** `Λ₀`: the algebra of a region `X` of the box consists of
the operators `M ⊗ 1` with `M` an operator of `X`. The algebra `Alg Ω Λ₀` carries the operator
norm of `ℓ²` on the configurations of the box. -/
noncomputable def boxNet (Λ₀ : Finset S) : LiebRobinson.LocalNet ↥Λ₀ (Alg Ω Λ₀) where
  alg X := (inclStarAlg (Ω := Ω) (boxRegion_subset X)).toAlgHom.range
  commute_of_disjoint {X Y} hXY := by
    rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
    exact commute_inclMat_of_disjoint _ _ (disjoint_boxRegion hXY) M N

/-- The lift of an operator of a region `X ⊆ Λ₀` belongs to the algebra of the region of the box
underlying `X`. -/
lemma inclMat_mem_boxNet {Λ₀ X : Finset S} (hX : X ⊆ Λ₀) (A : Alg Ω X) :
    inclMat hX A ∈ (boxNet Ω Λ₀).alg (X.subtype (· ∈ Λ₀)) := by
  have h : X ⊆ boxRegion (X.subtype (· ∈ Λ₀)) := fun x hx =>
    (mem_boxRegion (x := ⟨x, hX hx⟩)).2 (Finset.mem_subtype.2 hx)
  refine ⟨inclMat h A, ?_⟩
  change inclMat _ (inclMat h A) = inclMat hX A
  rw [← inclMat_trans]

/-- The lift `M ↦ M ⊗ 1` does not increase the operator norm. -/
lemma norm_inclMat_le {X Y : Finset S} (h : X ≤ Y) (M : Alg Ω X) : ‖inclMat h M‖ ≤ ‖M‖ :=
  NonUnitalStarAlgHom.norm_apply_le (inclStarAlg h) M

/-!

## C. Interactions in a finite box

-/

/-- **An interaction restricted to a finite box** `Λ₀`: the term of a region `X` of the box is
`Φ X ⊗ 1`. -/
noncomputable def Interaction.toBox (I : Interaction Ω) (Λ₀ : Finset S) :
    LiebRobinson.Interaction (boxNet Ω Λ₀) where
  Φ X := inclMat (boxRegion_subset X) (I.Φ (boxRegion X))
  mem_alg X := ⟨I.Φ (boxRegion X), rfl⟩
  isSelfAdjoint X := (I.isHermitian (boxRegion X)).isSelfAdjoint.map (inclStarAlg _)

/-- **The Hamiltonian of the restriction to a box is the Physlib Hamiltonian of the box.** -/
lemma Interaction.hamiltonian_toBox (I : Interaction Ω) (Λ₀ : Finset S) :
    (I.toBox Λ₀).hamiltonian = I.hamiltonian Λ₀ :=
  Fintype.sum_equiv (boxRegionEquiv Λ₀) _ _ fun _ => rfl

/-- The dynamics of the restriction to a box is generated by the Physlib Hamiltonian of the
box. -/
lemma Interaction.evolution_toBox (I : Interaction Ω) (Λ₀ : Finset S) (t : ℝ) (A : Alg Ω Λ₀) :
    (I.toBox Λ₀).evolution t A =
      LiebRobinson.expI (I.hamiltonian Λ₀) t * A * LiebRobinson.expI (I.hamiltonian Λ₀) (-t) := by
  rw [LiebRobinson.Interaction.evolution, hamiltonian_toBox]

/-!

## D. The Lieb–Robinson bound in a finite box

-/

/-- **The Lieb–Robinson bound in a finite box.** Let the interaction have strength
`‖Φ_Z‖ ≤ J` and range `R > 0` (non-zero terms have diameter at most `R`), and let at most `κ > 0`
non-zero terms inside the box `Λ₀` meet any region of the box. If `X, Y ⊆ Λ₀` are at distance at
least `d > 0`, then for operators `A` of `X`, `B` of `Y` and `t ≥ 0`,
`‖[τ_t(A ⊗ 1), B ⊗ 1]‖ ≤ 2 e ‖A‖ ‖B‖ (|neighbours X| / κ) e^{v t - d / R}` with `v = 2 e J κ`,
where `τ_t` is generated by the Hamiltonian `H_{Λ₀}` of the box. -/
theorem Interaction.lieb_robinson [PseudoMetricSpace S] (I : Interaction Ω) {Λ₀ X Y : Finset S}
    (hX : X ⊆ Λ₀) (hY : Y ⊆ Λ₀) (A : Alg Ω X) (B : Alg Ω Y) {J R d : ℝ} {κ : ℕ} (hκ0 : 0 < κ)
    (hJ0 : 0 ≤ J) (hJ : ∀ Z, ‖I.Φ Z‖ ≤ J) (hκ : ∀ Z, ((I.toBox Λ₀).neighbours Z).card ≤ κ)
    (hR0 : 0 < R) (hR : ∀ Z, I.Φ Z ≠ 0 → ∀ x ∈ Z, ∀ y ∈ Z, dist x y ≤ R) (hd0 : 0 < d)
    (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ dist x y) {t : ℝ} (ht : 0 ≤ t) :
    ‖LiebRobinson.commutator
        (LiebRobinson.expI (I.hamiltonian Λ₀) t * inclMat hX A *
          LiebRobinson.expI (I.hamiltonian Λ₀) (-t)) (inclMat hY B)‖ ≤
      2 * Real.exp 1 * ‖A‖ * ‖B‖ *
        (((I.toBox Λ₀).neighbours (X.subtype (· ∈ Λ₀))).card / κ) *
        Real.exp (2 * Real.exp 1 * J * κ * t - d / R) := by
  rw [← evolution_toBox]
  refine ((I.toBox Λ₀).lieb_robinson (inclMat_mem_boxNet hX A) (inclMat_mem_boxNet hY B) hκ0
    hJ0 (fun Z => (norm_inclMat_le _ _).trans (hJ _)) hκ hR0 ?_ hd0 ?_ ht).trans ?_
  · intro Z hZ x hx y hy
    have h0 : I.Φ (boxRegion Z) ≠ 0 := fun h => hZ <| by
      change inclMat _ (I.Φ (boxRegion Z)) = 0
      rw [h]
      exact map_zero (inclStarAlg (Ω := Ω) (boxRegion_subset Z))
    exact hR _ h0 _ (mem_boxRegion.2 hx) _ (mem_boxRegion.2 hy)
  · intro x hx y hy
    exact hd _ (Finset.mem_subtype.1 hx) _ (Finset.mem_subtype.1 hy)
  · gcongr
    · exact norm_inclMat_le hX A
    · exact norm_inclMat_le hY B

end QuasiLocal

end CondensedMatter
