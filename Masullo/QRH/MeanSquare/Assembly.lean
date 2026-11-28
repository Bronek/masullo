import Masullo.QRH.MeanSquare.Family
import Masullo.QRH.MeanSquare.GaussNorm
import Masullo.QRH.MeanSquare.GaussPair
import Masullo.QRH.MeanSquare.PrimeRows
import Masullo.QRH.MeanSquare.Reciprocity
import Masullo.QRH.MeanSquare.Sieve
import Masullo.QRH.MeanSquare.Theta

/-! # Proof obligations between the printed inputs and estimate (A) -/

namespace Masullo.QRH.MeanSquare

/-- The classical statements used in the reduction. Each field's defining
proposition gives its source and its normalization. -/
structure PrintedInputs : Prop where
  largeSieve : GoldmakherLouvel (CyclotomicField 3 ℚ)
  theta : PattersonTheorem81
  cosetPoisson : GaoZhaoLemma23
  cubicReciprocity : DunnRadziwillReciprocity
  cubicGaussCube : DunnRadziwillGaussCube
  quadraticGauss : DeloupTuraevTheorem1
  besselMellin : DLMFBesselMellin
  besselDecay : DLMFBesselAsymptotic
  besselDeriv : DLMFBesselDerivAsymptotic
  gammaVertical : DLMFGammaVertical

/-- Compose the printed inputs with the outstanding arithmetic and analytic reductions.
Each arrow names a proof still needed to obtain (A) from `PrintedInputs` alone. -/
theorem meanSquareA_of_reductions (h : PrintedInputs)
    (poisson : GaoZhaoLemma23 → PrimitivePoisson)
    (reflection : PattersonTheorem81 → DunnRadziwillReciprocity → DeloupTuraevTheorem1 →
      DLMFBesselMellin →
      DLMFBesselAsymptotic → DLMFBesselDerivAsymptotic → DLMFGammaVertical →
      QuadraticSieve primaryQuadraticSymbol → CompletedEstimate)
    (invert : GaussCoefficientBound → CompletedEstimate → CubeTailEstimate)
    (transfer : PrimitivePoisson → PairedGaussIdentities → GaussCoefficientBound → TransferEstimate)
    (firstPoisson : PrimitivePoisson → PairedGaussIdentities → GaussCoefficientBound →
      GapEstimate → FullRowEstimate) :
    Masullo.QRH.MeanSquareA := by
  have h7 := quadraticSieve_of_goldmakherLouvel h.largeSieve (eisensteinFamilyRealizes h.quadraticGauss)
  have h5 := reflection h.theta h.cubicReciprocity h.quadraticGauss h.besselMellin h.besselDecay
    h.besselDeriv h.gammaVertical h7
  have hp := poisson h.cosetPoisson
  have hg := pairedGaussIdentities h.cubicReciprocity h.cubicGaussCube h.quadraticGauss
  have hn := gaussCoefficientBound
  have h₁ := unitRowEstimate_of_gaussCoefficientBound hn
  have h4 := gapEstimate_of_tail_transfer h₁ (invert hn h5) (transfer hp hg hn)
  exact meanSquareA_of_fullRows (firstPoisson hp hg hn h4)

end Masullo.QRH.MeanSquare
