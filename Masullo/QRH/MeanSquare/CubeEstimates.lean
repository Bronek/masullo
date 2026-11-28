import Masullo.QRH.MeanSquare.UnitRows

/-! # Bounds for the rows in inverse cube completion -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The dyadic ideals and element rows in the parent mean square. -/
def cubeRows (K F : ℝ) : Finset (Ideal 𝓔 × 𝓔) := open Classical in
  ((idealsLe (2 * F)).filter (fun f =>
    Starred f ∧ F ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * F)) ×ˢ elementRows K

private theorem count_constants :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x → ((idealsLe x).card : ℝ) ≤ A * x := by
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  refine ⟨A, ?_, hA⟩
  have h := hA 1 le_rfl
  linarith [(Nat.cast_nonneg (idealsLe 1).card : (0 : ℝ) ≤ _)]

theorem cubeRows_normalizedColumn (ξ : RayCharacter) (W : ℝ → ℂ) (K L F : ℝ)
    (hL : 0 < L) (hF : 0 < F) :
    (∑ p ∈ cubeRows K F, ‖columnSum ξ W L p.2 p.1 / (Real.sqrt L : ℂ)‖ ^ 2) =
      F * dualMeanSquare ξ W K L F := by
  classical
  simp only [cubeRows, Finset.sum_product, norm_div, div_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg L), Real.sq_sqrt hL.le, ← Finset.sum_div,
    dualMeanSquare]
  field_simp

/-- The long uncompleted column is controlled by its child mean square. -/
theorem cube_child_bound {ξ : RayCharacter} {W : ℝ → ℂ} {K L F B : ℝ}
    (hL : 0 < L) (hF : 0 < F) (h : dualMeanSquare ξ W K L F ≤ B) :
    (∑ p ∈ cubeRows K F, ‖columnSum ξ W L p.2 p.1 / (Real.sqrt L : ℂ)‖ ^ 2) ≤ F * B := by
  rw [cubeRows_normalizedColumn ξ W K L F hL hF]
  gcongr

/-- Lengths at most one have bounded normalized columns. Counting the pairs of rows
then gives a bound proportional to `F K`. -/
theorem cube_small_bound (hg : GaussCoefficientBound) (I : TestInterval) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K L F : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
    1 ≤ K → 0 < L → L ≤ 1 → 1 ≤ F → UnitTest I 0 W →
    (∑ p ∈ cubeRows K F, ‖columnSum ξ W L p.2 p.1 / (Real.sqrt L : ℂ)‖ ^ 2) ≤ F * (C * K) := by
  classical
  obtain ⟨A, hA, hcount⟩ := count_constants
  let R := max I.hi 1
  let U : ℝ := Nat.card 𝓔ˣ
  have hR : 1 ≤ R := le_max_right _ _
  have hU : 0 ≤ U := Nat.cast_nonneg _
  refine ⟨2 * A ^ 2 * U * (A * R) ^ 2 * R, by positivity, ?_⟩
  intro K L F ξ W hK hL hL₁ hF hW
  by_cases hcut : R * L < 1
  · have hshort : I.hi * L < 1 := (mul_le_mul_of_nonneg_right (le_max_left _ _) hL.le).trans_lt hcut
    simp only [columnSum_eq_zero_of_short hW hL hshort, zero_div, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  have hLo : 1 ≤ R * L := le_of_not_gt hcut
  have hcol (k : 𝓔) (f : Ideal 𝓔) : ‖columnSum ξ W L k f‖ ≤ A * R := calc
    _ ≤ ((idealsLe (R * L)).card : ℝ) := norm_columnSum_le hg hW hL ξ k f
    _ ≤ A * (R * L) := hcount _ hLo
    _ ≤ A * R := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by linarith) hL₁) hA
  have hentry (p : Ideal 𝓔 × 𝓔) : ‖columnSum ξ W L p.2 p.1 / (Real.sqrt L : ℂ)‖ ^ 2 ≤
    (A * R) ^ 2 * R := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hL.le]
    refine (div_le_iff₀ hL).mpr ((pow_le_pow_left₀ (norm_nonneg _) (hcol _ _) 2).trans ?_)
    rw [mul_assoc]
    exact le_mul_of_one_le_right (sq_nonneg _) hLo
  have hkcard := Nat.cast_le (α := ℝ).mpr (card_elementRows_le K)
  rw [Nat.cast_mul] at hkcard
  have hc : ((cubeRows K F).card : ℝ) ≤ (A * (2 * F)) * (A * K * U) := by
    rw [cubeRows, Finset.card_product, Nat.cast_mul]
    refine mul_le_mul ((Nat.cast_le.mpr (Finset.card_filter_le ..)).trans
      (hcount _ (by linarith))) ?_
      (Nat.cast_nonneg _) (by positivity)
    exact hkcard.trans (mul_le_mul_of_nonneg_right (hcount _ hK) hU)
  calc
    _ ≤ ∑ _ ∈ cubeRows K F, (A * R) ^ 2 * R := Finset.sum_le_sum fun p _ => hentry p
    _ = ((cubeRows K F).card : ℝ) * ((A * R) ^ 2 * R) := by simp
    _ ≤ _ := (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring)

/-- Completed columns in the initial cube range use the bound at length `X/u`. -/
theorem cube_completed_bound (h : CompletedEstimate) {C₀ e : ℝ} (hC₀ : 1 ≤ C₀) (he : 0 < e) :
    ∃ j : ℕ, ∀ I : TestInterval, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (D K X F u : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
    2 ≤ D → 1 ≤ K → 1 ≤ X → 1 ≤ F → K ≤ X * F → X * F ≤ D ^ C₀ →
    1 ≤ u → u ≤ min X (X ^ 2 / K ^ 2) → UnitTest I j W →
    (∑ p ∈ cubeRows K F, ‖completedSum ξ W (X/u) p.2 p.1‖ ^ 2) ≤ F * (C * D ^ e * (X * F)) := by
  classical
  obtain ⟨A, hA, hcount⟩ := count_constants
  obtain ⟨j, hj⟩ := h (C₀ + 1) (by linarith) e he
  refine ⟨j, fun I => ?_⟩
  obtain ⟨C, hC, hcomp⟩ := hj I
  refine ⟨6 * A * C, by positivity, ?_⟩
  intro D K X F u ξ W hD hK hX hF hKX hsize hu hcut hW
  have hD₀ : 0 < D := by linarith
  have hD₁ : 1 ≤ D := by linarith
  have hu₀ : 0 < u := by linarith
  have hX₀ : 0 < X := by linarith
  have hL : 1 ≤ X / u := (one_le_div hu₀).mpr (hcut.trans (min_le_left ..))
  have hD' := Real.rpow_le_rpow_of_exponent_le hD₁ (show C₀ ≤ C₀ + 1 by linarith)
  have hL' := (div_le_self hX₀.le hu).trans
    ((le_mul_of_one_le_right hX₀.le hF).trans (hsize.trans hD'))
  have hF' : 2 * F ≤ D ^ (C₀ + 1) := calc
    _ ≤ D * D ^ C₀ := mul_le_mul hD ((le_mul_of_one_le_left (by linarith) hX).trans hsize)
      (by linarith) hD₀.le
    _ = _ := by rw [Real.rpow_add hD₀, Real.rpow_one, mul_comm]
  let fs := (idealsLe (2 * F)).filter (fun f => Starred f ∧ F ≤ (absNorm f : ℝ) ∧
    (absNorm f : ℝ) < 2 * F)
  have hscale : u*K^2 / X ≤ X := (div_le_iff₀ hX₀).mpr (by
    simpa [sq] using (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < K))).mp (hcut.trans
      (min_le_right ..)))
  have inner (f : Ideal 𝓔) (hf : f ∈ fs) :
      (∑ k ∈ elementRows K, ‖completedSum ξ W (X/u) k f‖ ^ 2) ≤ C * D ^ e * (3 * (X*F)) := by
    obtain ⟨_, hsf, _, hN⟩ := Finset.mem_filter.mp hf
    refine (hcomp D K (X/u) f ξ W hD hK (hKX.trans (hsize.trans hD')) hL hL' hsf
      (hN.le.trans hF') hW).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have ht : K^2 * (absNorm f : ℝ) / (X/u) ≤ X * (2*F) := calc
      _ = (u*K^2 / X) * absNorm f := by field_simp
      _ ≤ _ := mul_le_mul hscale hN.le (Nat.cast_nonneg _) hX₀.le
    linarith
  have hfcard : (fs.card : ℝ) ≤ A * (2*F) :=
    (Nat.cast_le.mpr (Finset.card_filter_le ..)).trans (hcount _ (by linarith))
  rw [cubeRows, Finset.sum_product]
  calc
    _ ≤ ∑ _ ∈ fs, C * D ^ e * (3 * (X*F)) := Finset.sum_le_sum inner
    _ = (fs.card : ℝ) * (C * D ^ e * (3 * (X*F))) := by simp
    _ ≤ _ := (mul_le_mul_of_nonneg_right hfcard (by positivity)).trans_eq (by ring)

end Masullo.QRH.MeanSquare
