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
import Masullo.QRH.MeanSquare.TransferProof

/-! # Estimate (A) from the printed inputs -/

namespace Masullo.QRH.MeanSquare

/-- The classical statements used in the reduction. Each field's defining
proposition gives its source and its normalization. The Goldmakher–Louvel input fixes the
Eisenstein family. The family-uniform implied constant printed in Theorem 1.1 fails for
general Definition 1 families. In arXiv v2, §4, duality costs `|G|`. The steps of the
printed proof checked here also use the conductor bound and support, the nonprincipality of
products at distinct indices, and multiplicativity in the index. `EisensteinGoldmakherLouvel`
names those steps, the fixed `|G|` and the theorems proving these properties for the
Eisenstein characters, and the step of Lemma 7.2 that relies on a fact not proved here. -/
structure PrintedInputs : Prop where
  largeSieve : EisensteinGoldmakherLouvel
  theta : PattersonTheorem81
  cubicReciprocity : DunnRadziwillReciprocity
  cubicGaussCube : DunnRadziwillGaussCube
  quadraticGauss : DeloupTuraevTheorem1
  besselMellin : DLMFBesselMellin
  gammaVertical : DLMFGammaVertical

/-- Estimate (A) from the printed inputs alone. -/
theorem meanSquareA_of_printedInputs (h : PrintedInputs) : Masullo.QRH.MeanSquareA := by
  have h7 := quadraticSieve_of_goldmakherLouvel h.largeSieve h.quadraticGauss
  have h5 := completedEstimate_of_reflection h.theta h.cubicReciprocity h.quadraticGauss
    h.besselMellin h.gammaVertical h7
  have hg := pairedGaussIdentities h.cubicReciprocity h.cubicGaussCube h.quadraticGauss
  have hn := gaussCoefficientBound
  have h₁ := unitRowEstimate_of_gaussCoefficientBound hn
  have h4 := gapEstimate_of_tail_transfer h₁ (cubeTailEstimate_of_completedEstimate hn h5)
    (transferEstimate hg)
  exact meanSquareA_of_fullRows (fullRowEstimate_of_gapEstimate hg h4)

/-- The trace identity at every width above 5/12, from the printed inputs alone. -/
theorem hasTrace_of_printedInputs (h : PrintedInputs) {a : ℝ} (ha : 5 / 12 < a)
    (φ : TestFunction) :
    Trace.HasTrace (Trace.induced (by linarith : (0 : ℝ) < a) φ) φ.efFunctional :=
  Masullo.QRH.hasTrace_of_meanSquareA (meanSquareA_of_printedInputs h) ha φ

end Masullo.QRH.MeanSquare
