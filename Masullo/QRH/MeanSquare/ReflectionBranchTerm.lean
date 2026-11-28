import Masullo.QRH.MeanSquare.ReflectionBranchIdentity
import Masullo.QRH.MeanSquare.ReflectionBranchVector

/-! # The extracted coefficients of a reflected squarefree branch -/

noncomputable section

open NumberField Ideal Finset Complex
open scoped Classical

namespace Masullo.QRH.MeanSquare.ReflectionSieve

open ReflectionInversion TameBranch

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- The column coefficient of (15), after replacing the two extracted ideals
by their residual squarefree and cube variables. -/
def branchColumn (τ : ℂ → ℂ) (ψ : 𝓔 → ℂ) (F : Finset Idl) (j : Idl → ℕ) (e : F → TameBranch)
    (u : 𝓔ˣ) (i : Fin 2) (h : ℕ) (b n : Idl) : ℂ :=
  extendIndex (fun x => (ψ x.numerator * pieceProduct F j e x * x.amplitude τ) /
    (Real.sqrt (absNorm (twoPart i * extractedN F e)) * (absNorm (extractedB F e) : ℂ)))
    u i h (extractedB F e*b) (extractedN F e*n)

/-- The quadratic twist of the unit, ramified factors and the full cube ideal. -/
def branchRow (F : Finset Idl) (e : F → TameBranch) (u : 𝓔ˣ) (i : Fin 2)
    (h : ℕ) (b k : Idl) : ℂ :=
  if hk : AwayFromSix k then quadraticResidue hk (eisLambda^h*u*generator (twoPart i*extractedN F e)*
    generator (extractedB F e*b)) else 0

theorem norm_branchRow (F : Finset Idl) (e : F → TameBranch) (u : 𝓔ˣ) (i : Fin 2)
    (h : ℕ) (b k : Idl) : ‖branchRow F e u i h b k‖ ≤ 1 := by
  rw [branchRow]
  split
  · exact norm_quadratic_le _ _
  · simp

theorem twoPart_ne_zero (i : Fin 2) : twoPart i ≠ 0 :=
  pow_ne_zero _ (by simp : span {(-2:𝓔)} ≠ 0)

theorem norm_branchColumn {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ) {ψ : 𝓔 → ℂ}
    (hψ : ∀ m, ‖ψ m‖ ≤ 1) (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p)
    (j : Idl → ℕ) (e : F → TameBranch) (he : ∀ p : F, e p ∈ activeChoices (j p.val))
    (u : 𝓔ˣ) (i : Fin 2) (h : ℕ) (b n : Idl) :
    ‖branchColumn τ ψ F j e u i h b n‖ ≤ Real.sqrt (∏ p : F, (e p).weightSq (absNorm p.val)) := by
  have hgood := extracted_coprime F e (fun p hp => (hF p hp).1)
  have hD := absNorm_one_le hgood.1.1
  have hB := absNorm_one_le hgood.2.1
  have hI := absNorm_one_le (twoPart_ne_zero i)
  have hN : (absNorm (extractedN F e) : ℝ) ≤ absNorm (twoPart i * extractedN F e) := by
    rw [map_mul,Nat.cast_mul]
    exact le_mul_of_one_le_left (by positivity) hI
  have hden : 0 < Real.sqrt (absNorm (extractedN F e)) * (absNorm (extractedB F e) : ℝ) :=
    mul_pos (Real.sqrt_pos.mpr (by linarith)) (by linarith)
  rw [branchColumn,extendIndex]
  split
  next hs =>
    let x : ReflectedIndex := ⟨h,u,twoPart i*(extractedN F e*n),extractedB F e*b,hs.2.1,hs.2.2.1,hs.1⟩
    have hmul : ‖ψ x.numerator * pieceProduct F j e x * x.amplitude τ‖ ≤ ‖pieceProduct F j e x‖ := by
      rw [norm_mul,norm_mul]
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (x.norm_amplitude hτ)).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hψ _))
    rw [norm_div, norm_mul (↑(Real.sqrt (absNorm (twoPart i*extractedN F e))) : ℂ)
      (absNorm (extractedB F e) : ℂ),Complex.norm_real,Complex.norm_natCast,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    refine (?_ : _ ≤ ‖pieceProduct F j e x‖ / (Real.sqrt (absNorm (extractedN F e)) * (absNorm (extractedB F e):ℝ))).trans
      (idealPiece_product_bound F hF j e he x)
    exact div_le_div₀ (norm_nonneg _) hmul hden (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hN) (by positivity))
  · simp

private theorem quadratic_cube {k : Idl} (hk : AwayFromSix k) (y : 𝓔) :
    quadraticResidue hk (y^3) = quadraticResidue hk y := by
  rw [map_pow]
  by_cases h : IsCoprime k (span {y})
  · rw [pow_succ,quadraticResidue_sq hk h,one_mul]
  · have hz : quadraticResidue hk y = 0 := by_contra fun h' => h ((quadraticResidue_ne_zero hk).mp h')
    simp [hz]

set_option maxHeartbeats 1000000 in
/-- The zero-extended Patterson term on a branch equals the raw kernel term,
including its row multiplier, quadratic squarefree column and rescaled kernel argument. -/
theorem extendIndex_indexTerm_eq_rawKernelTerm (τ : ℂ → ℂ) (W : ℝ → ℂ) (X Q : ℝ) (c : 𝓔) (ψ : 𝓔 → ℂ)
    {k : Idl} (hk : AwayFromSix k) (hc : ‖eisEmbedding c‖^2 = Q*absNorm k)
    (F : Finset Idl) (j : Idl → ℕ) (e : F → TameBranch) (u : 𝓔ˣ) (i : Fin 2) (h : ℕ) (b n : Idl) :
    extendIndex (indexTerm τ W X c ψ hk F j e) u i h (extractedB F e*b) (extractedN F e*n) =
      rawKernelTerm W X Q (absNorm (twoPart i*extractedN F e)) (absNorm (extractedB F e))
        (branchColumn τ ψ F j e u i) (branchRow F e u i) k h b n := by
  let D := extractedN F e
  let B := extractedB F e
  by_cases hs : Squarefree (twoPart i*(D*n)) ∧ IsCoprime (twoPart i*(D*n)) (span {3}) ∧
      IsCoprime (B*b) (span {3}) ∧ Starred (D*n)
  · let x : ReflectedIndex := ⟨h,u,twoPart i*(D*n),B*b,hs.2.1,hs.2.2.1,hs.1⟩
    let A := twoPart i*D
    have hx : x.n = A*n := mul_assoc .. |>.symm
    have hc₃ : IsCoprime (A*n) (span {3}) := hx ▸ x.coprime_n
    have hgn := generator_mul (hc₃.of_isCoprime_of_dvd_left (dvd_mul_right A n))
      (hc₃.of_isCoprime_of_dvd_left (dvd_mul_left n A))
    have hnum : x.numerator = (eisLambda^h*u*generator A) * generator n * generator (B*b)^3 := by
      rw [ReflectedIndex.numerator,hx,hgn]
      change eisLambda^h*(u*(generator A*generator n * generator (B*b)^3)) = _
      ring
    have hquad : quadraticResidue hk x.numerator =
        branchRow F e u i h b k * primaryQuadraticSymbol n k := by
      rw [branchRow,dite_eq_left hk,hnum,map_mul,quadratic_cube,map_mul]
      rw [show primaryQuadraticSymbol n k = quadraticResidue hk (generator n) from (quadraticResidue_apply ..).symm]
      rw [map_mul (quadraticResidue hk) (eisLambda^h*u*generator (twoPart i*extractedN F e))]
      dsimp only [A,D,B]
      ac_rfl
    have hNs : (absNorm x.n : ℝ) = (absNorm A:ℝ) * absNorm n := by rw [hx,map_mul,Nat.cast_mul]
    have hBs : (absNorm x.b : ℝ) = (absNorm B:ℝ) * absNorm b := by change (absNorm (B*b):ℝ) = _; rw [map_mul,Nat.cast_mul]
    have hBz : (absNorm x.b : ℂ) = (absNorm B:ℂ) * absNorm b := by exact_mod_cast hBs
    have hNsqrt : (Real.sqrt (absNorm x.n) : ℂ) = (Real.sqrt (absNorm A) : ℂ) * Real.sqrt (absNorm n) := by
      rw [hNs,Real.sqrt_mul (by positivity),Complex.ofReal_mul]
    have harg : normSq (pattersonFrequency x.numerator)*X/(‖eisEmbedding c‖^2)^2 =
        (3:ℝ)^((h:ℤ)-3) * absNorm n * (absNorm b:ℝ)^3 * absNorm A * (absNorm B:ℝ)^3*X/(Q*absNorm k)^2 := by
      rw [x.normSq_frequency,hc,hNs,hBs]
      change (3:ℝ)^((h:ℤ)-3)*((absNorm A:ℝ)*absNorm n)*((absNorm B:ℝ)*absNorm b)^3*X/_ = _
      ring
    rw [extendIndex,dite_eq_left hs,rawKernelTerm,branchColumn,extendIndex,dite_eq_left hs]
    change (ψ x.numerator * pieceProduct F j e x) * quadraticResidue hk x.numerator * dualMode τ W X c x.numerator = _
    rw [dualMode,x.angularCoefficient_div_sqrt, mul_zero, show pattersonCharacter 0 = 1 by simp [pattersonCharacter],
      mul_one,harg,hNsqrt,hBz,hquad]
    change (ψ x.numerator * pieceProduct F j e x) * (branchRow F e u i h b k * primaryQuadraticSymbol n k) *
      (((((3:ℝ)^(-((h:ℝ)-3)/3):ℝ):ℂ) * x.amplitude τ /
        ((Real.sqrt (absNorm A):ℂ)*Real.sqrt (absNorm n)*((absNorm B:ℂ)*absNorm b))) * _) = _
    ring
  · rw [extendIndex,dite_eq_right hs,rawKernelTerm,branchColumn,extendIndex,dite_eq_right hs]
    simp

end Masullo.QRH.MeanSquare.ReflectionSieve
