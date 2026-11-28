import Mathlib

/-! # Finite quadratic Gauss reciprocity -/

noncomputable section

namespace Masullo.QRH.MeanSquare

namespace DeloupTuraev

variable {n : ℕ}

/-- Columns of `B` in an orthonormal frame generate the lattice `B ℤⁿ`. -/
def lattice (B : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  Set.range (fun x : Fin n → ℤ => B.mulVec (fun j => (x j : ℝ)))

/-- One lift of each coset of `L'` in `L`. -/
def Representatives (L L' : Set (Fin n → ℝ)) (s : Finset (Fin n → ℝ)) : Prop :=
  (↑s : Set _) ⊆ L ∧ ∀ x ∈ L, ∃! u : s, x - u.val ∈ L'

/-- The difference between the positive and negative indices of the real quadratic form of `H`. -/
def signature (H : Matrix (Fin n) (Fin n) ℝ) : ℤ :=
  (sigPos H.toQuadraticForm' : ℤ) - (sigNeg H.toQuadraticForm' : ℤ)

/-- The complex phase `exp(πi t)`. -/
def phase (t : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * t)

end DeloupTuraev

open DeloupTuraev

/-- F. Deloup and V. Turaev, *On reciprocity*, J. Pure Appl. Algebra 208 (2007), 153–158,
Theorem 1, equation (3) under (1), arXiv:math/0512050 p. 1. The numbering is the journal's;
the arXiv version states the result as an unnumbered theorem. In orthonormal coordinates `B`
has the basis of `W` as columns, so `(Bᵀ)⁻¹` gives the basis of the dual and its determinant
gives the dual covolume. The two finite sets choose arbitrary lifts in the two lattices.
<https://arxiv.org/pdf/math/0512050#page=1> -/
def DeloupTuraevTheorem1 : Prop :=
  ∀ (n : ℕ) (B H : Matrix (Fin n) (Fin n) ℝ), B.det ≠ 0 → H.det ≠ 0 → H.IsSymm →
    ∀ (ψ : Fin n → ℝ) (r : ℕ), 0 < r →
    let W := lattice B
    let dualBasis := B.transpose⁻¹
    let dual := lattice dualBasis
    let Z := Set.range (Int.cast : ℤ → ℝ)
    (∀ y ∈ dual, H.mulVec y ∈ dual) →
    (∀ x ∈ W, ∀ x' ∈ W, r / 2 * dotProduct x (H.mulVec x) ∈ Z ∧
      dotProduct x (H.mulVec x') ∈ Z ∧ r * dotProduct x ψ ∈ Z) →
    (∀ y ∈ dual, ∀ y' ∈ dual, r / 2 * dotProduct y (H.mulVec y) ∈ Z ∧
      dotProduct y ((r : ℝ) • y') ∈ Z ∧ r * dotProduct y ψ ∈ Z) →
    ∀ s t : Finset (Fin n → ℝ), Representatives W ((fun x => (r : ℝ) • x) '' W) s →
      Representatives dual (H.mulVec '' dual) t →
      (|dualBasis.det| : ℝ) * ∑ x ∈ s,
          phase ((dotProduct x (H.mulVec x) + 2 * r * dotProduct x ψ) / r) =
        ((Real.sqrt |H.det|)⁻¹ : ℝ) * phase ((signature H : ℝ) / 4) *
          ((r : ℝ) ^ ((n : ℝ) / 2) : ℝ) *
          ∑ y ∈ t, phase (-(r : ℝ) * dotProduct (y + ψ) (H⁻¹.mulVec (y + ψ)))

end Masullo.QRH.MeanSquare
