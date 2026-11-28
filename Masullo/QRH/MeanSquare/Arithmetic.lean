import Masullo.QRH.MeanSquare.Eisenstein
import Masullo.QRH.IdealMoebius

/-! # Radial Poisson summation and cubic reciprocity over the Eisenstein integers -/

noncomputable section

open NumberField Ideal MeasureTheory

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The radial Fourier transform in Gao–Zhao's coordinates `x + y(1 + ω)`. The product
measure `dx dy` assigns mass one to the coordinate unit square. -/
def gaoZhaoTransform (W : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  ∫ xy : ℝ × ℝ, let z : ℂ := xy.1 + xy.2 * (1 + eisEmbedding eisOmega)
    W (Complex.normSq z) * differentCharacter (-t * z)

/-- P. Gao and L. Zhao, *The large sieve with power moduli in imaginary quadratic number fields*,
Int. J. Number Theory 18 (2022), §2.2, Lemma 2.3, arXiv:2101.00811v2 p. 4.
This is their specialization to field discriminant `−3`, including the zero Fourier frequency.
<https://arxiv.org/pdf/2101.00811v2#page=4> -/
def GaoZhaoLemma23 : Prop :=
  ∀ (W : SchwartzMap ℝ ℂ) (X : ℝ), 0 < X → ∀ r n : 𝓔, n ≠ 0 →
    let N := fun m : 𝓔 => Complex.normSq (eisEmbedding m)
    ∃ s : ℂ,
      HasSum (fun m : {m : 𝓔 // n ∣ m - r} => W (N m.val / X)) (X / N n * s) ∧
      HasSum (fun k : 𝓔 => gaoZhaoTransform W (Real.sqrt (N k * X / N n)) *
        differentCharacter (eisEmbedding k * eisEmbedding r / eisEmbedding n)) s

/-- A. Dunn and M. Radziwiłł, *Bias in cubic Gauss sums: Patterson's conjecture*, Ann. of Math.
200 (2024), §1.2, (1.4)–(1.5), arXiv:2109.07463v3 p. 4. The supplementary laws read the
coefficients of `λ²` and `λ³` in a primary denominator modulo `9`.
<https://arxiv.org/pdf/2109.07463v3#page=4> -/
def DunnRadziwillReciprocity : Prop :=
  (∀ a b : 𝓔, eisPrimary a → eisPrimary b → cubicSymbol a b = cubicSymbol b a) ∧
  (∀ (d : 𝓔) (h j : ℤ), h ∈ Set.Icc (-1) 1 → j ∈ Set.Icc (-1) 1 →
    (9 : 𝓔) ∣ d - (1 + h * eisLambda ^ 2 + j * eisLambda ^ 3) →
      eisEmbedding (cubicSymbol eisOmega d) = eisEmbedding eisOmega ^ h ∧
      eisEmbedding (cubicSymbol eisLambda d) = eisEmbedding eisOmega ^ (-j))

/-- Reciprocity at the primary generator `−2` of the inert prime over `2`. -/
theorem cubicSymbol_neg_two (h : DunnRadziwillReciprocity) {a : 𝓔} (ha : eisPrimary a) :
    cubicSymbol (-2) a = cubicSymbol a (-2) :=
  h.1 _ _ ⟨-1, by ring⟩ ha

/-- A. Dunn and M. Radziwiłł, *Bias in cubic Gauss sums: Patterson's conjecture*, Ann. of Math.
200 (2024), §1.2, (1.7)–(1.8), arXiv:2109.07463v3 p. 4. Here `pattersonGauss 1 c` has the trace
character of (1.7), and division by `|c|` normalizes it.
<https://arxiv.org/pdf/2109.07463v3#page=4> -/
def DunnRadziwillGaussCube : Prop :=
  ∀ c : 𝓔, eisPrimary c → (pattersonGauss 1 c / (‖eisEmbedding c‖ : ℝ)) ^ 3 =
    (idealMoebius (span {c}) : ℂ) * eisEmbedding c / (‖eisEmbedding c‖ : ℝ)

/-- The normalized Gauss sum at a primary prime cubes to the negative of the prime's phase. -/
theorem gaussCube_at_prime (h : DunnRadziwillGaussCube) {p : 𝓔} (hp : Prime p)
    (hprim : eisPrimary p) : (pattersonGauss 1 p / (‖eisEmbedding p‖ : ℝ)) ^ 3 =
      -eisEmbedding p / (‖eisEmbedding p‖ : ℝ) := by
  have hP : Prime (span {p}) := (prime_iff_isPrime (by simpa using hp.ne_zero)).2
    ((span_singleton_prime hp.ne_zero).2 hp)
  simpa [idealMoebius, hP.squarefree, UniqueFactorizationMonoid.normalizedFactors_irreducible
    hP.irreducible] using h p hprim

end Masullo.QRH.MeanSquare
