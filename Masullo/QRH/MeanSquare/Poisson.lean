import Masullo.QRH.MeanSquare.Arithmetic
import Masullo.QRH.MeanSquare.Forms

/-! # Common inputs to the two Poisson reductions

These are proof obligations for the sextic family. See (1)–(3) of the audit's
manuscript and Lemmas 4.1–4.2, pp. 13–14 of OpenAI, *The Quasi-Riemann
Hypothesis* (5 October 2026).
-/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- Interchanging the two coprime columns conjugates the character. -/
def pairCharacter (b c : Ideal 𝓔) (x : 𝓔) : ℂ := conj (sextic b x) * sextic c x

/-- The primitive Gauss sum for this pair, with additive shift one. -/
def pairGauss (b c : Ideal 𝓔) : ℂ :=
  (∑ᶠ x : 𝓔 ⧸ (b * c), pairCharacter b c (Quotient.out x) *
    differentCharacter (eisEmbedding (Quotient.out x) / eisEmbedding (generator (b * c)))) /
    Real.sqrt (absNorm (b * c))

/-- Primitive Poisson (1) for the paired character, with a squarefree exclusion.
The inner lattice sums include zero, also when the conductor is one. -/
def PrimitivePoisson : Prop := open Classical in
  ∀ (b c g : Ideal 𝓔), Starred b → Starred c → Starred g →
    IsCoprime b c → IsCoprime g (b * c) → ∀ (P : SchwartzMap ℝ ℂ) (Y : ℝ), 0 < Y →
    (∑' y : 𝓔, if IsCoprime (span {y}) g then
      P (elementNorm y / Y) * pairCharacter b c y else 0) =
      (Y : ℂ) * pairGauss b c / Real.sqrt (absNorm (b * c)) *
        ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g},
          (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e.val : ℂ) *
            ∑' h : 𝓔, conj (pairCharacter b c h) * gaoZhaoTransform P
              (Real.sqrt (Y * elementNorm h / ((absNorm e.val : ℝ) * absNorm (b * c))))

/-- Direct and reverse Gauss-to-Möbius conversion. The two corrections are fixed
functions on pairs of residues modulo 72. Their domains and all their values are
independent of the lengths. The last equality is the coprime product formula for `a`. -/
def PairedGaussIdentities : Prop :=
  ∃ A B : (𝓔 ⧸ span {(72 : 𝓔)}) → (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ,
    ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      let r := fun n => Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n)
      (idealMoebius b : ℂ) * idealMoebius c * pairGauss b c =
        gaussCoefficient b * conj (gaussCoefficient c) * A (r b) (r c) ∧
      gaussCoefficient b * conj (gaussCoefficient c) * pairGauss c b =
        (idealMoebius b : ℂ) * idealMoebius c * B (r b) (r c) ∧
      gaussCoefficient (b * c) = gaussCoefficient b * gaussCoefficient c * sextic c (generator
        b) ^ 4

end Masullo.QRH.MeanSquare
