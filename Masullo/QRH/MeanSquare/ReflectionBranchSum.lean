import Masullo.QRH.MeanSquare.ReflectionBranchIdentity
import Masullo.QRH.MeanSquare.ReflectionBranchVector
import Masullo.QRH.MeanSquare.ReflectionFamilyAssembly

/-! # Identifying the fixed-active-set row with the extracted kernel series -/

noncomputable section

open NumberField Ideal Finset Complex UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare.ReflectionSieve

open ReflectionInversion ReflectionRowInversion

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- Put a row-dependent scalar of bounded modulus into the row multiplier.
The common positive bound is carried by the column coefficient. -/
theorem rawKernelTerm_scale (W : ℝ → ℂ) (X Q N L : ℝ) {H : ℝ} (hH : 0 < H)
    (a : Idl → ℂ) (c d : ℕ → Idl → Idl → ℂ) (k : Idl) (h : ℕ) (b n : Idl) :
    rawKernelTerm W X Q N L (fun m b n => H*c m b n) (fun m b k => a k/H*d m b k) k h b n =
      a k * rawKernelTerm W X Q N L c d k h b n := by
  dsimp [rawKernelTerm]
  have he : (H:ℂ) ≠ 0 := ofReal_ne_zero.mpr hH.ne'
  field_simp

/-- Fixed factors in the denominator of the reflected kernel. -/
theorem norm_conductor {h : RayResidue 7} (D : FixedCusp h) (F : Finset Idl) (k : Idl) :
    ‖eisEmbedding (D.c*(generator k * ∏ p ∈ F, generator p))‖^2 =
      ((elementNorm D.c : ℝ)*(∏ p ∈ F, (absNorm p : ℝ))) * (absNorm k : ℝ) := by
  rw [norm_eisEmbedding_sq]
  exact_mod_cast branch_denominator_norm D k F

/-- The finite choices in the arithmetic expansion are taken outside the
absolutely convergent ideal sums. This form matches the branch count in (16). -/
theorem branchSum_extracted {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (hΓ : DLMFGammaVertical) {J : TestInterval} {W : ℝ → ℂ} (hw : UnitTest J 6 W)
    {X : ℝ} (hX : 0 < X) {k : Idl} (hk : AwayFromSix k) {h : RayResidue 7} (D : FixedCusp h)
    (r : ReflectionCRT.Residue (72*eisLambda^7)) (T G : Idl) (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p) :
    let j := fun p => exponent T G p % 6
    let ψ := fun m => classWeight D r F (ReflectionCRT.red (8*eisLambda^9) m)
    let c := D.c * (generator k * ∏ p ∈ F, generator p)
    branchSum D r T G F hk τ W X =
      ∑ u : 𝓔ˣ, ∑ i : Fin 2, ∑ η : TameAssignment j F,
        ∑' z : ReflectedColumns, extendIndex (indexTerm τ W X c ψ hk F j η.val) u i z.1
          (extractedB F η.val*z.2.1.val) (extractedN F η.val*z.2.2.val) := by
  classical
  intro j ψ c
  have hc : c ≠ 0 := by
    have hd {p : Idl} (hp : p ≠ 0) : generator p ≠ 0 := fun hh => hp (by simpa [hh] using (span_generator p).symm)
    exact mul_ne_zero D.c_ne_zero (mul_ne_zero (hd hk.1) (prod_ne_zero_iff.mpr fun p hp => hd (hF p hp).1.1))
  have hs := split_dual_row ht hΓ hw hX hc (ψ := ψ) (fun m => norm_classWeight_le D r (fun p hp => (hF p hp).1) _) hk F hF j
  change branchSum D r T G F hk τ W X = _
  apply hs.trans
  rw [← (Fintype.piFinset (fun p : F => TameBranch.activeChoices (j p))).sum_coe_sort]
  simp_rw [tsum_fintype,extract_indexTerm _ _ _ _ _ hk F hF]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]

end Masullo.QRH.MeanSquare.ReflectionSieve
