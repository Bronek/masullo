import Masullo.QRH.MeanSquare.CubeTail
import Masullo.QRH.MeanSquare.DualAssembly
import Masullo.QRH.MeanSquare.Family
import Masullo.QRH.MeanSquare.GaussNorm
import Masullo.QRH.MeanSquare.GaussPair
import Masullo.QRH.MeanSquare.PrimitivePoisson
import Masullo.QRH.MeanSquare.PrimeRows
import Masullo.QRH.MeanSquare.Reciprocity
import Masullo.QRH.MeanSquare.Reflection
import Masullo.QRH.MeanSquare.Sieve
import Masullo.QRH.MeanSquare.Theta

/-! # Proof obligations between the printed inputs and estimate (A) -/

namespace Masullo.QRH.MeanSquare

/-- The classical statements used in the reduction. Each field's defining
proposition gives its source and its normalization. -/
structure PrintedInputs : Prop where
  largeSieve : GoldmakherLouvel (CyclotomicField 3 ℚ)
  theta : PattersonTheorem81
  cubicReciprocity : DunnRadziwillReciprocity
  cubicGaussCube : DunnRadziwillGaussCube
  quadraticGauss : DeloupTuraevTheorem1
  besselMellin : DLMFBesselMellin
  gammaVertical : DLMFGammaVertical

/-- Compose the printed inputs with the outstanding analytic reduction.
The `transfer` arrow names the proof still needed to obtain (A) from `PrintedInputs` alone. -/
theorem meanSquareA_of_reductions (h : PrintedInputs)
    (transfer : PrimitivePoisson → PairedGaussIdentities → GaussCoefficientBound →
      TransferEstimate) :
    Masullo.QRH.MeanSquareA := by
  have h7 :=
    quadraticSieve_of_goldmakherLouvel h.largeSieve (eisensteinFamilyRealizes h.quadraticGauss)
  have h5 := completedEstimate_of_reflection h.theta h.cubicReciprocity h.quadraticGauss
    h.besselMellin h.gammaVertical h7
  have hp := primitivePoisson
  have hg := pairedGaussIdentities h.cubicReciprocity h.cubicGaussCube h.quadraticGauss
  have hn := gaussCoefficientBound
  have h₁ := unitRowEstimate_of_gaussCoefficientBound hn
  have h4 := gapEstimate_of_tail_transfer h₁ (cubeTailEstimate_of_completedEstimate hn h5)
    (transfer hp hg hn)
  exact meanSquareA_of_fullRows (fullRowEstimate_of_gapEstimate hg h4)

end Masullo.QRH.MeanSquare
