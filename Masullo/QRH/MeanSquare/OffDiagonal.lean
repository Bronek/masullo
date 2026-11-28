import Masullo.QRH.MeanSquare.Transfer
import Masullo.QRH.MeanSquare.DilatedSeparation
import Masullo.QRH.MeanSquare.FirstPoisson

/-!
# Toward the off-diagonal estimate

Pieces of the bound `OffDiagonalEstimate rowMajorant` from `GapEstimate`.

* `residueMultiplicative` discharges the residue hypotheses of the exclusion shift
  `dualMeanSquareCoprime_le`.
-/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

/-- The generator and the sextic symbol are multiplicative away from `6`. -/
theorem residueMultiplicative : ResidueMultiplicative :=
  ⟨generator_mul, fun h6 a b => powerResidueSymbol_six_mul h6 a b⟩

end Masullo.QRH.MeanSquare
