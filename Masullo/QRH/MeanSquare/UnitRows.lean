import Masullo.QRH.MeanSquare.Descent

/-! # The terminal estimate in the mean-square descent -/

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The normalized cubic Gauss coefficient has norm at most one on good squarefree ideals. -/
def GaussCoefficientBound : Prop :=
  ∀ n : Ideal 𝓔, Starred n → ‖gaussCoefficient n‖ ≤ 1

private lemma norm_primeSextic_le (a : 𝓔) (p : Ideal 𝓔) :
    ‖eisEmbedding (primePowerResidueSymbol 6 a p)‖ ≤ 1 := by
  classical
  unfold primePowerResidueSymbol
  split_ifs with h₀ h
  · simp
  · have hpow := congrArg eisEmbedding h.choose_spec.1
    rw [map_pow, map_one] at hpow
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hpow⟩).norm_eq_one.le
  · simp

lemma norm_sextic_le_one (n : Ideal 𝓔) (k : 𝓔) : ‖sextic n k‖ ≤ 1 := by
  classical
  unfold sextic powerResidueSymbol
  split_ifs
  · simp
  generalize normalizedFactors n = s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_primeSextic_le k p)).trans ih

lemma norm_twist_le_one (ξ : RayCharacter) (k : 𝓔) (f n : Ideal 𝓔) :
    ‖twist ξ k f n‖ ≤ 1 := by
  classical
  unfold twist
  split_ifs
  swap
  · simp
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_sextic_le_one ..)
  let x := Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n)
  change ‖ξ x‖ ≤ 1
  by_cases hx : IsUnit x
  · let := Ring.HasFiniteQuotients.finiteQuotient (I := span {(72 : 𝓔)}) (by simp)
    have hpow := pow_card_eq_one' (x := hx.unit)
    have hχ := congrArg (fun u : (𝓔 ⧸ span {(72 : 𝓔)})ˣ => ξ (u : 𝓔 ⧸ _)) hpow
    simp only [Units.val_pow_eq_pow_val, hx.unit_spec, map_pow, Units.val_one, map_one] at hχ
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, Nat.card_pos, hχ⟩).norm_eq_one.le
  · simp [ξ.map_nonunit hx]

/-- The column vanishes when its support would require an ideal of norm less than one. -/
theorem columnSum_eq_zero_of_short {I : TestInterval} {j : ℕ} {W : ℝ → ℂ} (hW : UnitTest I j W)
    {L : ℝ} (hL : 0 < L) (hcut : I.hi * L < 1)
    (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) : columnSum ξ W L k f = 0 := by
  have hz (n : {n : Ideal 𝓔 // Starred n}) : W (absNorm n.1 / L) = 0 := by
    by_contra h
    have hx := (hW.2.1 (subset_tsupport W h)).2
    have hN : 1 ≤ (absNorm n.1 : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr n.2.1.1)
    linarith [(div_le_iff₀ hL).mp hx]
  simp [columnSum, hz]

theorem norm_columnSum_le {I : TestInterval} {W : ℝ → ℂ} {X : ℝ}
    (hg : GaussCoefficientBound) (hW : UnitTest I 0 W) (hX : 0 < X)
    (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) :
    ‖columnSum ξ W X k f‖ ≤ (idealsLe (max I.hi 1 * X)).card := by
  classical
  let s := idealsLe (max I.hi 1 * X)
  let t := s.preimage (Subtype.val : {n : Ideal 𝓔 // Starred n} → Ideal 𝓔)
    Subtype.val_injective.injOn
  have hR := le_max_right I.hi 1
  have hsub {y : ℝ} (hy : W y ≠ 0) : y ∈ Set.Icc I.lo I.hi := hW.2.1 (subset_tsupport W hy)
  have hnorm (y : ℝ) : ‖W y‖ ≤ 1 := by
    by_cases hy : W y = 0
    · simp [hy]
    · simpa using hW.2.2 0 le_rfl y (hsub hy)
  unfold columnSum
  rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
  · calc
      _ ≤ ∑ n ∈ t, ‖gaussCoefficient n * twist ξ k f n * W (absNorm n.1 / X)‖ := norm_sum_le ..
      _ ≤ ∑ _n ∈ t, (1 : ℝ) := Finset.sum_le_sum fun n _ => by
        simp only [norm_mul]
        have hcoef := (mul_le_of_le_one_left (norm_nonneg _) (hg n n.2)).trans
          (norm_twist_le_one ξ k f n)
        exact (mul_le_of_le_one_left (norm_nonneg _) hcoef).trans (hnorm _)
      _ ≤ (s.card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_le_card_of_injOn Subtype.val
          (fun n hn => Finset.mem_preimage.mp hn) Subtype.val_injective.injOn
  · intro n hn
    apply Finset.mem_preimage.mpr
    apply (mem_idealsLe (by positivity : 0 ≤ max I.hi 1 * X)).mpr
    have hy : W (absNorm n.1 / X) ≠ 0 := right_ne_zero_of_mul (Function.mem_support.mp hn)
    exact (div_le_iff₀ (by linarith : 0 < X)).mp ((hsub hy).2.trans (le_max_left _ _))

/-- Counting the columns and the finitely many unit rows gives the terminal estimate. -/
theorem unitRowEstimate_of_gaussCoefficientBound (hg : GaussCoefficientBound) : UnitRowEstimate := by
  classical
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  have hA₀ : 0 ≤ A := by
    have := hA 1 le_rfl
    linarith [(Nat.cast_nonneg (idealsLe 1).card : (0 : ℝ) ≤ _)]
  intro I
  let R := max I.hi 1
  let U : ℝ := (elementRows 1).card
  have hR : 1 ≤ R := le_max_right _ _
  have hU : 0 ≤ U := Nat.cast_nonneg _
  refine ⟨2 * A * U * (A * R) ^ 2, by positivity, ?_⟩
  intro X F ξ W hX hF hW
  have hcol (k : 𝓔) (f : Ideal 𝓔) : ‖columnSum ξ W X k f‖ ≤ A * (R * X) :=
    (norm_columnSum_le hg hW (by linarith : 0 < X) ξ k f).trans
      (hA _ (by nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hX)]))
  have hinner (f : Ideal 𝓔) : (∑ k ∈ elementRows 1, ‖columnSum ξ W X k f‖ ^ 2) ≤
      U * (A * (R * X)) ^ 2 := by
    simpa [U, nsmul_eq_mul] using Finset.sum_le_card_nsmul (elementRows 1)
      (fun k => ‖columnSum ξ W X k f‖ ^ 2) ((A * (R * X)) ^ 2)
      (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hcol k f) 2)
  unfold dualMeanSquare
  refine (div_le_iff₀ (by positivity)).mpr ?_
  calc
    _ ≤ ∑ _ ∈ _, U * (A * (R * X)) ^ 2 := Finset.sum_le_sum fun f _ => hinner f
    _ ≤ A * (2 * F) * (U * (A * (R * X)) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact (Nat.cast_le.mpr (Finset.card_filter_le ..)).trans (hA _ (by linarith))
    _ = 2 * A * U * (A * R) ^ 2 * X ^ 2 * F := by ring
    _ ≤ 2 * A * U * (A * R) ^ 2 * X ^ 2 * (F * F) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = _ := by ring

end Masullo.QRH.MeanSquare
