import Masullo.QRH.MeanSquare.ReflectionBranchBudget
import Masullo.QRH.MeanSquare.ReflectionBranchSum
import Masullo.QRH.MeanSquare.ReflectionBranchTerm

/-! # The completed estimate from Patterson reflection and the quadratic large sieve -/

noncomputable section

open NumberField Ideal Finset Complex

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

namespace ReflectionSieve

open ReflectionInversion ReflectionRowInversion

/-- Each fixed active set gives a finite sum of kernel branches on one class
of squarefree rows. All dependence on the row in the fixed Fourier scalars
is carried by the row multiplier. -/
theorem fixedBranchConversion {τ : ℂ → ℂ} (ht : PattersonCoefficients τ) (hΓ : DLMFGammaVertical) :
    FixedBranchConversion τ := by
  classical
  intro I
  refine ⟨BranchBudget.B,BranchBudget.one_le_B,?_⟩
  intro K X W hK hX hW t y T G ht₀ hy hT hG hTt hGy h D r F hF R q a hR
  let j := fun p => exponent T G p % 6
  let ψ := fun m => classWeight D r F (ReflectionCRT.red (8*eisLambda^9) m)
  have hgood := BranchBudget.primes_good hT hG hF
  have hψ (m) : ‖ψ m‖ ≤ 1 := norm_classWeight_le D r (fun p hp => (hgood p hp).1) _
  have hH : 0 < BranchBudget.H := zero_lt_one.trans_le BranchBudget.one_le_H
  let v (u : 𝓔ˣ) (i : Fin 2) (η : TameAssignment j F) : KernelBranchData BranchBudget.B K X t y :=
    let hb := BranchBudget.of_active hK hX ht₀ hy hT hG hTt hGy D F hF i η
    { rows := R
      rowClass := q
      rows_subset := fun _ hk => (hR _ hk).1
      rows_class := fun _ hk => (hR _ hk).2.2.2.2.1
      primes := F
      primes_subset := hb.primes_subset
      choice := BranchBudget.choice F η.val
      simple := hb.simple
      a := BranchBudget.a F η.val
      Q := BranchBudget.Q D F
      N := BranchBudget.N i F η.val
      L := BranchBudget.L F η.val
      K_pos := zero_lt_one.trans_le hK
      X_pos := zero_lt_one.trans_le hX
      Q_pos := hb.Q_pos
      N_pos := hb.N_pos
      L_pos := hb.L_pos
      amplitude_nonneg := hb.amplitude_nonneg
      amplitude := hb.amplitude
      length := hb.length
      c := fun h b n => BranchBudget.H * branchColumn τ ψ F j η.val u i h b n
      d := fun h b k => a k / BranchBudget.H * branchRow F η.val u i h b k
      columns := by
        intro h b _ n _
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hH.le]
        exact mul_le_mul_of_nonneg_left (norm_branchColumn ht hψ F hgood j η.val
          (Fintype.mem_piFinset.mp η.property) u i h b n) hH.le
      row_phases := by
        intro h b _ k hk
        rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hH.le]
        exact (mul_le_mul ((div_le_one hH).mpr (hR k hk).2.2.2.2.2) (norm_branchRow F η.val u i h b k)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _) }
  refine ⟨fun u i η => makeKernelBranch (v u i η), fun _ _ _ => Subset.rfl,?_⟩
  intro k hk
  have hk₆ := (hR k hk).2.1.1
  rw [branchSum_extracted ht hΓ (hW.of_le (by decide : 6 ≤ 14)) (zero_lt_one.trans_le hX) hk₆ D r T G F hgood]
  simp_rw [Finset.mul_sum]
  refine sum_congr (ext fun _ => by simp) fun u _ => sum_congr rfl fun i _ => sum_congr rfl fun η _ => ?_
  rw [makeKernelBranch_rowValue _ hΓ hW (show k ∈ (v u i η).rows from hk), ← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [extendIndex_indexTerm_eq_rawKernelTerm τ W X (BranchBudget.Q D F) _ ψ hk₆
    (norm_conductor D F k) F j η.val u i z.1 z.2.1 z.2.2]
  exact (rawKernelTerm_scale W X (BranchBudget.Q D F) (BranchBudget.N i F η.val) (BranchBudget.L F η.val)
    hH a (branchColumn τ ψ F j η.val u i) (branchRow F η.val u i) k z.1 z.2.1 z.2.2).symm

end ReflectionSieve

/-- Estimate (5) follows from the normalized Patterson expansion, the two
reciprocity inputs, the Bessel Mellin transform, vertical gamma growth and (7). -/
theorem completedEstimate_of_reflection (hθ : PattersonTheorem81) (hR : DunnRadziwillReciprocity)
    (quad : DeloupTuraevTheorem1) (hB : DLMFBesselMellin) (hΓ : DLMFGammaVertical)
    (sieve : QuadraticSieve primaryQuadraticSymbol) : CompletedEstimate := by
  obtain ⟨_,τ,_,_,ht,he,hχ⟩ := hθ
  exact ReflectionRows.completedEstimate_of_squarefree
    (ReflectionSieve.squarefreeCompletedEstimate_of_branches quad sieve hΓ
      (ReflectionSieve.squarefreeBranchRepresentation_of_conversion he ht hχ hB hΓ hR quad
        (ReflectionSieve.fixedBranchConversion ht hΓ)))

end Masullo.QRH.MeanSquare
