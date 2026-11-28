import Masullo.QRH.MeanSquare.TransferCount
import Masullo.QRH.MeanSquare.TransferSecond
import Masullo.QRH.MeanSquare.Majorant
import Masullo.QRH.MeanSquare.TransferBlocks

/-!
# Proof of `TransferEstimate`

The Schwartz function from `exists_transferMajorant` bounds the row indicator on `[0, 1]`.
The first Poisson pass uses `exists_firstPass_le` and `firstDual_le_secondInput`.
The second uses `exists_passBound` and `secondDual_le`.
The coprime children are then bounded by `exists_coprimeBlocks_le`. The remaining divisor
counts of `TransferCount.lean` cost `D^ε`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma passRows_pos {X : ℝ} {r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (hr : r ∈ passRows X) :
    (0 : ℝ) < absNorm (r.1 * r.2.1) ∧ (0 : ℝ) < absNorm r.2.1 ∧
      (0 : ℝ) < absNorm (r.1 * r.2.1 * r.2.2) := by
  classical
  obtain ⟨hg, he⟩ := passRows_ne_bot hr
  have hv : r.2.2 ≠ ⊥ := by
    unfold passRows at hr
    exact (Finset.mem_filter.mp hr).2.2.1.1.1
  have pos : ∀ {n : Ideal 𝓔}, n ≠ ⊥ → (0 : ℝ) < absNorm n := fun hn => by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hn (absNorm_eq_zero_iff.mp h))
  refine ⟨pos hg, pos he, ?_⟩
  rw [map_mul, Nat.cast_mul]
  exact mul_pos (pos hg) (pos hv)

private lemma secondWeight_mul_secondScale {hi K L F target : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hF : 0 < F) {r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (hg : (0 : ℝ) < absNorm (r.1 * r.2.1))
    (he : (0 : ℝ) < absNorm r.2.1) :
    secondWeight K L F r * secondScale hi K L F target r =
      max 1 (4 * hi ^ 2) * target / (L * absNorm (r.1 * r.2.1)) := by
  unfold secondWeight secondScale
  field_simp

private lemma rpow_four_mul {A D C₀ ε : ℝ} (hA : 0 ≤ A) (hD : 0 < D) (hC₀ : 0 < C₀) :
    ((A * D ^ (5 * C₀)) ^ (ε / (20 * C₀))) ^ 4 = A ^ (4 * (ε / (20 * C₀))) * D ^ ε := by
  rw [← Real.rpow_mul_natCast (by positivity), Real.mul_rpow hA (by positivity),
    ← Real.rpow_mul hD.le]
  congr 2
  · push_cast; ring
  · field_simp; ring

/-- Proposition 5.4 of the October preprint in the form `TransferEstimate`: two Poisson passes
and a divisor-weighted count reduce the transfer to the coprime children. -/
theorem transferEstimate (hpg : PairedGaussIdentities) : TransferEstimate := by
  intro C₀ hC₀ ε hε m I
  classical
  obtain ⟨P, hPim, hPre, hPone, hPT⟩ := exists_transferMajorant
  have hP : IsRowMajorant P := ⟨hPim, hPre, hPone⟩
  have hT : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0 := fun t ht =>
    hPT t (by rw [abs_of_nonneg (by linarith)]; exact ht)
  obtain ⟨Corr, hconv⟩ := exists_gaussConversion_second hpg
  obtain ⟨C1, hC1, h1⟩ := exists_firstPass_le hpg I (m + 1) hP hT
  obtain ⟨C2, hC2, h2⟩ := exists_passBound residueMultiplicative I (m + 1) hP hT Corr
  obtain ⟨C3, hC3, h3⟩ := exists_coprimeBlocks_le hpg I m
  have hC₀0 : 0 < C₀ := by linarith
  set s : ℝ := ε / (20 * C₀) with hs_def
  have hs : 0 < s := by positivity
  obtain ⟨Cd, hCd, hd⟩ := exists_card_dyadicStarred_le
  obtain ⟨Ct, hCt, ht⟩ := exists_sum_two_pow_le hs
  obtain ⟨Cr, hCr, hr⟩ := exists_sum_passRows_le hs
  obtain ⟨Ch, hCh, hh⟩ := exists_sum_four_pow_le hs
  obtain ⟨Cl, hCl, hl⟩ := exists_natLog_le hs
  obtain ⟨Cp, hCp, hp⟩ := exists_card_idealDivisors_pair_le hs
  obtain ⟨Cs, hCs, hsp⟩ := exists_card_idealDivisors_span_le hs
  have hhi : 0 < I.hi := I.pos.trans_le I.ordered
  set c : ℝ := max 1 (4 * I.hi ^ 2) with hc_def
  have hc : 1 ≤ c := le_max_left _ _
  set A : ℝ := 4 * (1 + I.hi) ^ 3 with hA_def
  have hhiA : 1 + I.hi ≤ A := by
    have : 1 + I.hi ≤ (1 + I.hi) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    rw [hA_def]; nlinarith
  have hA : 1 ≤ A := by linarith
  set K0 : ℝ := C1 * Cd * Ct * I.hi + C1 * Cs * C2 * c * Ct * Cr * I.hi +
    C1 * Cs * C2 * Cp * c * C3 * Cl * Ch with hK0_def
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨K0 * A ^ (4 * s), by positivity,
    fun D K L F target B ξ W hD hK hL hF hKt hLF htD hB hch hW => ?_⟩
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hK0' : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hF0 : 0 < F := by linarith
  have ht1 : 1 ≤ target := hK.trans hKt
  have ht0 : 0 < target := by linarith
  have hLt : L ≤ target := le_trans (le_mul_of_one_le_right hL0.le hF) hLF
  have hFt : F ≤ target := le_trans (le_mul_of_one_le_left hF0.le hL) hLF
  have hDC : D ^ C₀ ≤ D ^ (5 * C₀) := Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
  set Q : ℝ := A * D ^ (5 * C₀) with hQ_def
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hD1 (by linarith))
  have hhiL : I.hi * L ≤ Q :=
    calc I.hi * L ≤ (1 + I.hi) * target := mul_le_mul (by linarith) hLt hL0.le (by linarith)
      _ ≤ Q := mul_le_mul hhiA (htD.trans hDC) ht0.le (by linarith)
  set Λ : ℝ := 4 * I.hi ^ 3 * L ^ 3 * F ^ 2 / K with hΛ_def
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛ : Λ ≤ Q := by
    have h5 : target ^ 5 ≤ D ^ (5 * C₀) := by
      calc target ^ 5 ≤ (D ^ C₀) ^ 5 := pow_le_pow_left₀ ht0.le htD 5
        _ = D ^ (5 * C₀) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; push_cast; ring_nf
    have hLF5 : L ^ 3 * F ^ 2 ≤ target ^ 5 := by
      calc L ^ 3 * F ^ 2 ≤ target ^ 3 * target ^ 2 := by gcongr
        _ = target ^ 5 := by ring
    have hhi3 : 4 * I.hi ^ 3 ≤ A := by
      rw [hA_def]; gcongr; linarith
    calc Λ ≤ 4 * I.hi ^ 3 * L ^ 3 * F ^ 2 := div_le_self (by positivity) hK
      _ = 4 * I.hi ^ 3 * (L ^ 3 * F ^ 2) := by ring
      _ ≤ A * D ^ (5 * C₀) := mul_le_mul hhi3 (hLF5.trans h5) (by positivity) (by linarith)
  set q : ℝ := Q ^ s with hq_def
  have hq1 : 1 ≤ q := Real.one_le_rpow hQ1 hs.le
  have hle : ∀ x, 0 ≤ x → x ≤ Q → x ^ s ≤ q := fun x hx hxQ => Real.rpow_le_rpow hx hxQ hs.le
  have hW' : UnitTest I (m + 1) W := hW.of_le (by omega)
  set T1 : ℝ := Cs * Λ ^ s with hT1_def
  set T2 : ℝ := Cp * (I.hi * L) ^ s with hT2_def
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  set lg : ℝ := (Nat.log 2 ⌊I.hi * L⌋₊ + 1 : ℝ) with hlg_def
  have hlg0 : 0 ≤ lg := by positivity
  set H : ℝ := ∑ r ∈ starredLe (I.hi * L),
    (4 : ℝ) ^ Multiset.card (normalizedFactors r) / absNorm r with hH_def
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun _ _ => by positivity
  set M3 : ℝ := c * target * C3 * lg * (1 + B) * H with hM3_def
  have hM30 : 0 ≤ M3 := by positivity
  set Z2 : ℝ := ∑ r ∈ passRows (I.hi * L),
    secondWeight K L F r * secondScale I.hi K L F target r *
      ∑ g ∈ starredLe (I.hi * secondLength L r),
        (2 : ℝ) ^ Multiset.card (normalizedFactors g) with hZ2_def
  have hrow : ∀ r ∈ passRows (I.hi * L), 0 ≤ secondWeight K L F r ∧
      0 < secondScale I.hi K L F target r ∧ 0 < secondLength L r ∧
      0 ≤ I.hi * secondLength L r := by
    intro r hr
    obtain ⟨hg, he, hgv⟩ := passRows_pos hr
    unfold secondWeight secondScale secondLength
    exact ⟨by positivity, by positivity, by positivity, by positivity⟩
  have hZ20 : 0 ≤ Z2 := Finset.sum_nonneg fun r hr => by
    have := hrow r hr
    exact mul_nonneg (mul_nonneg this.1 this.2.1.le) (Finset.sum_nonneg fun _ _ => by positivity)
  set M1 : ℝ := T1 * (C2 * Z2 + C2 * (T2 * M3)) with hM1_def
  have hM10 : 0 ≤ M1 := by positivity
  -- The second dual form, through the coprime children.
  have hM2 : ∀ U, UnitTest I (m + 1) U → ∀ ξ' ξ'' : RayCharacter,
      secondDual ξ ξ' ξ'' U I.hi K L F target ≤ T2 * M3 := by
    intro U hU ξ' ξ''
    have hUs : ∀ t, U t ≠ 0 → t ≤ I.hi := fun t h0 =>
      (hU.2.1 (subset_tsupport U (Function.mem_support.mpr h0))).2
    refine (secondDual_le ξ ξ' ξ'' U hhi hK0' hL0 hF0 ht0 hUs hT20
      (fun a b ha hb hab => hp a b (I.hi * L) ha hb hab)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hT20
    have hM3' : M3 = ∑ r ∈ starredLe (I.hi * L), c * target * absNorm r / L ^ 2 *
        (C3 * lg * 4 ^ Multiset.card (normalizedFactors r) * (1 + B) *
          (L / absNorm r) ^ 2) := by
      rw [hM3_def, hH_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr0 : (absNorm r : ℝ) ≠ 0 := by
        have := ((mem_starredLe (by positivity)).mp hr).2.1.1
        exact_mod_cast fun h => this (absNorm_eq_zero_iff.mp h)
      field_simp
    rw [hM3']
    refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact h3 K L F target B _ _ r hK0' hL hF hKt hB hch hU.conj
      ((mem_starredLe (by positivity)).mp hr).2
  -- The second pass.
  have hS2 : ∀ U, UnitTest I (m + 1) U → ∀ ξ' : RayCharacter,
      secondInput ξ ξ' U P I.hi K L F target ≤ C2 * Z2 + C2 * (T2 * M3) := by
    intro U hU ξ'
    exact h2 (passRows (I.hi * L)) (secondWeight K L F) (secondScale I.hi K L F target)
      (secondLength L) (fun r => I.hi * secondLength L r) (κ := moebiusTwist) (κ' := conjGauss)
      (fun r => secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2)) (p := 0) (p' := 2)
      (V := fun t => conj (U t)) (M := T2 * M3) twistMul_moebiusTwist
      (twistMul_conjGauss hpg) (fun r => twistMul_secondTwist ξ ξ' _ _ _) hconv
      norm_moebiusTwist_le norm_conjGauss_le (fun r n => norm_secondTwist_le ξ ξ' _ _ _ n)
      hU.conj hrow (by positivity) (fun U' hU' ξ'' => hM2 U' hU' ξ' ξ'')
  -- The first pass.
  have hM1 : ∀ U, UnitTest I (m + 1) U → ∀ ξ', firstDual ξ ξ' U I.hi K L F ≤ M1 := by
    intro U hU ξ'
    refine (firstDual_le_secondInput hP ξ ξ' U hhi hK0' hL0 hF0 hLF hT10
      (fun y hy hyΛ => hsp y Λ hy hyΛ)).trans
      (mul_le_mul_of_nonneg_left (hS2 U hU ξ') hT10)
  have hmain := h1 K L F ξ W hK0' hL0 hF0 hW' hM10 hM1
  -- The counts.
  have hZ1 : (L * F)⁻¹ * K * (dyadicStarred F).card *
      ∑ g ∈ starredLe (I.hi * L), (2 : ℝ) ^ Multiset.card (normalizedFactors g) ≤
        Cd * Ct * I.hi * target * q := by
    calc (L * F)⁻¹ * K * (dyadicStarred F).card *
          ∑ g ∈ starredLe (I.hi * L), (2 : ℝ) ^ Multiset.card (normalizedFactors g)
        ≤ (L * F)⁻¹ * K * (Cd * F) * (Ct * (I.hi * L) * q) := by
          gcongr
          · exact hd F hF
          · exact ht _ Q (by positivity) hhiL hQ1
      _ = Cd * Ct * I.hi * K * q := by field_simp
      _ ≤ Cd * Ct * I.hi * target * q := by gcongr
  have hZ2 : Z2 ≤ c * Ct * Cr * I.hi * target * q ^ 2 := by
    calc Z2 ≤ ∑ r ∈ passRows (I.hi * L), c * target * Ct * q / L *
          ((absNorm (r.1 * r.2.1) : ℝ)⁻¹ * (I.hi * L / absNorm (r.1 * r.2.1 * r.2.2))) := by
          refine Finset.sum_le_sum fun r hr => ?_
          obtain ⟨hg, he, hgv⟩ := passRows_pos hr
          have hlen : I.hi * secondLength L r ≤ Q := by
            refine le_trans ?_ hhiL
            unfold secondLength
            gcongr
            refine div_le_self hL0.le ?_
            have := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by exact_mod_cast hgv))
            exact_mod_cast this
          have hcount := ht _ Q (hrow r hr).2.2.2 hlen hQ1
          rw [secondWeight_mul_secondScale hK0' hL0 hF0 hg he]
          calc c * target / (L * absNorm (r.1 * r.2.1)) *
                ∑ g ∈ starredLe (I.hi * secondLength L r),
                  (2 : ℝ) ^ Multiset.card (normalizedFactors g)
              ≤ c * target / (L * absNorm (r.1 * r.2.1)) *
                  (Ct * (I.hi * secondLength L r) * q) := by gcongr
            _ = _ := by unfold secondLength; field_simp
      _ = c * target * Ct * q / L * ∑ r ∈ passRows (I.hi * L),
          (absNorm (r.1 * r.2.1) : ℝ)⁻¹ * (I.hi * L / absNorm (r.1 * r.2.1 * r.2.2)) := by
          rw [Finset.mul_sum]
      _ ≤ c * target * Ct * q / L * (Cr * (I.hi * L) * q) := by
          gcongr
          exact hr _ Q (by positivity) hhiL hQ1
      _ = c * Ct * Cr * I.hi * target * q ^ 2 := by field_simp
  have hM3b : M3 ≤ c * target * C3 * (Cl * q) * (1 + B) * (Ch * q) := by
    rw [hM3_def]
    gcongr
    · exact hl _ Q (by positivity) hhiL hQ1
    · exact hh _ Q (by positivity) hhiL hQ1
  have hT1b : T1 ≤ Cs * q := by rw [hT1_def]; gcongr; exact hle _ hΛ0 hΛ
  have hT2b : T2 ≤ Cp * q := by rw [hT2_def]; gcongr; exact hle _ (by positivity) hhiL
  -- Collect the powers of `q`.
  have hB1 : 1 ≤ 1 + B := by linarith
  set R : ℝ := target * (1 + B) * q ^ 4 with hR_def
  have hq14 : target * q ≤ R := by
    rw [hR_def]
    have : q ≤ q ^ 4 := le_self_pow₀ hq1 (by norm_num)
    calc target * q = target * 1 * q := by ring
      _ ≤ target * (1 + B) * q ^ 4 := by gcongr
  have hq34 : target * q ^ 3 ≤ R := by
    rw [hR_def]
    have : q ^ 3 ≤ q ^ 4 := pow_le_pow_right₀ hq1 (by norm_num)
    calc target * q ^ 3 = target * 1 * q ^ 3 := by ring
      _ ≤ target * (1 + B) * q ^ 4 := by gcongr
  have e1 : C1 * ((L * F)⁻¹ * K * (dyadicStarred F).card *
      ∑ g ∈ starredLe (I.hi * L), (2 : ℝ) ^ Multiset.card (normalizedFactors g)) ≤
        C1 * Cd * Ct * I.hi * R := by
    calc _ ≤ C1 * (Cd * Ct * I.hi * target * q) := by gcongr
      _ = C1 * (Cd * Ct * I.hi * (target * q)) := by ring
      _ ≤ C1 * (Cd * Ct * I.hi * R) := by gcongr
      _ = _ := by ring
  have e2 : C1 * M1 ≤ (C1 * Cs * C2 * c * Ct * Cr * I.hi +
      C1 * Cs * C2 * Cp * c * C3 * Cl * Ch) * R := by
    calc C1 * M1 ≤ C1 * (Cs * q * (C2 * (c * Ct * Cr * I.hi * target * q ^ 2) +
          C2 * (Cp * q * (c * target * C3 * (Cl * q) * (1 + B) * (Ch * q))))) := by
          rw [hM1_def]; gcongr
      _ = C1 * Cs * C2 * c * Ct * Cr * I.hi * (target * q ^ 3) +
          C1 * Cs * C2 * Cp * c * C3 * Cl * Ch * R := by rw [hR_def]; ring
      _ ≤ C1 * Cs * C2 * c * Ct * Cr * I.hi * R +
          C1 * Cs * C2 * Cp * c * C3 * Cl * Ch * R := by gcongr
      _ = _ := by ring
  have hfin : K0 * A ^ (4 * s) * D ^ ε * target * (1 + B) = K0 * R := by
    have hq4 : q ^ 4 = A ^ (4 * s) * D ^ ε := rpow_four_mul (A := A) (by linarith) hD0 hC₀0
    rw [hR_def, hq4]
    ring
  rw [hfin, hK0_def]
  linarith

end Masullo.QRH.MeanSquare
