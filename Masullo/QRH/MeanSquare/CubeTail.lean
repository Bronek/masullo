import Masullo.QRH.MeanSquare.CubeInversion
import Masullo.QRH.MeanSquare.CubeEstimates
import Masullo.QRH.MeanSquare.CubeWeights

/-! # Estimate for the inverse cube tail -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private theorem weighted_rows_bound {ι κ : Type*} (s : Finset ι) (rows : Finset κ)
    (u : ι → ℝ) (w v : ι → κ → ℂ) {H V : ℝ} (hV : 0 ≤ V)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hm : ∑ i ∈ s, u i ≤ H)
    (hw : ∀ i ∈ s, ∀ x ∈ rows, ‖w i x‖ ≤ u i)
    (hv : ∀ i ∈ s, ∑ x ∈ rows, ‖v i x‖ ^ 2 ≤ V) :
    ∑ x ∈ rows, ‖∑ i ∈ s, w i x * v i x‖ ^ 2 ≤ H ^ 2 * V := by
  have hm₀ := Finset.sum_nonneg hu
  refine (sum_norm_weighted_sum_sq_le s rows u w v hu hw).trans ?_
  calc
    _ ≤ (∑ i ∈ s, u i) * ∑ i ∈ s, u i * V :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hv i hi) (hu i hi)) hm₀
    _ = (∑ i ∈ s, u i) ^ 2 * V := by rw [← Finset.sum_mul]; ring
    _ ≤ H ^ 2 * V := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm₀ hm 2) hV

private theorem sum_sub_sq_le {κ : Type*} (s : Finset κ) (a b : κ → ℂ) :
    ∑ x ∈ s, ‖a x - b x‖ ^ 2 ≤
      2 * ((∑ x ∈ s, ‖a x‖ ^ 2) + ∑ x ∈ s, ‖b x‖ ^ 2) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le ..) 2).trans
    (by nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)])

/-- The completed columns cost one harmonic sum. Each uncompleted tail column carries
two such sums, from the Möbius ideal and the completing ideal. -/
private theorem truncated_rows_bound {I : TestInterval} {j : ℕ} {W : ℝ → ℂ} (hW : UnitTest I j W)
    (ξ : RayCharacter) {X Y K F H V : ℝ} (hX : 0 < X) (hY : 1 ≤ Y) (hYX : Y ≤ max I.hi 1 * X)
    (hH : 1 ≤ H) (hV : 0 ≤ V)
    (hm : ∀ s : Finset (Ideal 𝓔), (∀ b ∈ s, (absNorm b : ℝ) ≤ max I.hi 1 * X) →
      ∑ b ∈ s, 1 / (absNorm b : ℝ) ≤ H)
    (hc : ∀ b ∈ cubeIdeals Y, ∑ p ∈ cubeRows K F,
      ‖completedSum ξ W (X / cubeNorm b) p.2 p.1‖ ^ 2 ≤ V)
    (ht : ∀ b : Ideal 𝓔, AwayFromSix b → Y < cubeNorm b →
      ∑ p ∈ cubeRows K F, ‖normalizedColumn ξ W (X / cubeNorm b) p.2 p.1‖ ^ 2 ≤ V) :
    ∑ p ∈ cubeRows K F, ‖normalizedColumn ξ W X p.2 p.1‖ ^ 2 ≤ 4 * H ^ 4 * V := by
  classical
  let rows := cubeRows K F
  let S := cubeIdeals Y
  let T (b : Ideal 𝓔) := (cubeIdeals (max I.hi 1 * X / cubeNorm b)).filter (fun d =>
    Y < cubeNorm (b * d))
  let u (b : Ideal 𝓔) := 1 / (absNorm b : ℝ)
  let w (b : Ideal 𝓔) (p : Ideal 𝓔 × 𝓔) := cubeWeight ξ p.2 p.1 b
  let μw (b : Ideal 𝓔) (p : Ideal 𝓔 × 𝓔) := (idealMoebius b : ℂ) * w b p
  let c (b : Ideal 𝓔) (p : Ideal 𝓔 × 𝓔) := completedSum ξ W (X / cubeNorm b) p.2 p.1
  let v (b : Ideal 𝓔) (p : Ideal 𝓔 × 𝓔) := normalizedColumn ξ W (X / cubeNorm b) p.2 p.1
  let t (b : Ideal 𝓔) (p : Ideal 𝓔 × 𝓔) := ∑ d ∈ T b, w d p * v (b * d) p
  have hle {Z : ℝ} {b : Ideal 𝓔} (hb : b ∈ cubeIdeals Z) : (absNorm b : ℝ) ≤ Z :=
    (le_self_pow₀ (absNorm_one_le (mem_cubeIdeals.mp hb).1.1) (by decide : 3 ≠ 0)).trans
      (mem_cubeIdeals.mp hb).2
  have hS : ∑ b ∈ S, u b ≤ H := hm S fun _ hb => (hle hb).trans hYX
  have hμ (b : Ideal 𝓔) (hb : b ∈ S) (p : Ideal 𝓔 × 𝓔) (_hp : p ∈ rows) : ‖μw b p‖ ≤ u b := by
    simpa only [u, one_div] using norm_moebius_cubeWeight_le ξ p.2 p.1 (mem_cubeIdeals.mp hb).1
  have hcomp := weighted_rows_bound S rows u μw c hV (by intros; positivity [u]) hS hμ hc
  have htail (b : Ideal 𝓔) (hb : b ∈ S) : ∑ p ∈ rows, ‖t b p‖ ^ 2 ≤ H ^ 2 * V := by
    have hb' := (mem_cubeIdeals.mp hb).1
    have hT : ∑ d ∈ T b, u d ≤ H := hm _ fun d hd =>
      (hle (Finset.mem_filter.mp hd).1).trans (div_le_self (by positivity) (cubeNorm_one_le hb'))
    apply weighted_rows_bound (T b) rows u w (fun d => v (b * d)) hV (by intros; positivity [u]) hT
    · intro d hd p _
      simpa only [u, one_div] using norm_cubeWeight_le ξ p.2 p.1
        (mem_cubeIdeals.mp (Finset.mem_filter.mp hd).1).1
    · exact fun d hd => ht (b * d) (hb'.mul (mem_cubeIdeals.mp (Finset.mem_filter.mp hd).1).1)
        (Finset.mem_filter.mp hd).2
  have hrest := weighted_rows_bound S rows u μw t (mul_nonneg (sq_nonneg H) hV)
    (by intros; positivity [u]) hS hμ htail
  have hrep (p : Ideal 𝓔 × 𝓔) : normalizedColumn ξ W X p.2 p.1 =
      (∑ b ∈ S, μw b p * c b p) - ∑ b ∈ S, μw b p * t b p := by
    simpa only [t, S, T, μw, w, c, v, Finset.mul_sum, mul_assoc] using truncated_cube_inversion hW
      hX hY hYX ξ p.2 p.1
  simp_rw [hrep]
  refine (sum_sub_sq_le rows _ _).trans ?_
  have hle' : H ^ 2 ≤ H ^ 4 := pow_le_pow_right₀ hH (by decide : 2 ≤ 4)
  nlinarith [mul_le_mul_of_nonneg_right hle' hV]

/-- Invert cube completion up to the cutoff `min X (X²/K²)`. -/
theorem cubeTailEstimate_of_completedEstimate (hg : GaussCoefficientBound)
    (completed : CompletedEstimate) :
    CubeTailEstimate := by
  classical
  intro C₀ hC₀ ε hε
  let e := ε / 5
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨j, hj⟩ := cube_completed_bound completed hC₀ he
  refine ⟨j, fun I => ?_⟩
  let R := max I.hi 1
  have hR : 1 ≤ R := le_max_right _ _
  obtain ⟨A, hA, hA'⟩ := ideal_harmonic_envelope hC₀ he R hR
  obtain ⟨C, hC, hcomp⟩ := hj I
  obtain ⟨G, hG, hsmall⟩ := cube_small_bound hg I
  let J := 1 + C + G
  have hJ : 1 ≤ J := by dsimp [J]; linarith
  refine ⟨4 * (1 + A) ^ 4 * J, by positivity, ?_⟩
  intro D K X F B ξ W hD hK hX hF hKX hsize hW hB hchild
  let Y := min X (X ^ 2 / K ^ 2)
  let d := D ^ e
  have hd : 1 ≤ d := Real.one_le_rpow (by linarith) he.le
  let H := (1 + A) * d
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by linarith) hd
  let V := J * d * (X * F + B)
  have hXF : 0 ≤ X * F := by positivity
  have hV₀ : 0 ≤ V := by dsimp [V]; positivity
  have hJu : 1 ≤ J * d := one_le_mul_of_one_le_of_one_le hJ hd
  have hsm : G * K ≤ V := calc
    _ ≤ G * (X * F) := mul_le_mul_of_nonneg_left hKX hG
    _ ≤ (J * d) * (X * F + B) :=
      mul_le_mul ((le_mul_of_one_le_right (by dsimp [J]; linarith) hd).trans'
        (by dsimp [J]; linarith))
        (by linarith) hXF (by positivity)
  have hBV : B ≤ V := (show B ≤ X * F + B by linarith).trans (le_mul_of_one_le_left
    (by positivity) hJu)
  have hCV : C * d * (X * F) ≤ V := mul_le_mul
    (mul_le_mul_of_nonneg_right (by dsimp [J]; linarith : C ≤ J) (by linarith)) (by linarith) hXF
      (by positivity)
  have hchild' (b : Ideal 𝓔) (hb : AwayFromSix b) (hY : Y < cubeNorm b) :
      (∑ p ∈ cubeRows K F, ‖normalizedColumn ξ W (X / cubeNorm b) p.2 p.1‖ ^ 2) ≤ F * V := by
    have hL : 0 < X / cubeNorm b := div_pos (by linarith) (zero_lt_one.trans_le
      (cubeNorm_one_le hb))
    by_cases h₁ : 1 < X / cubeNorm b
    · exact (cube_child_bound hL (by linarith) (hchild b hb hY h₁)).trans
        (mul_le_mul_of_nonneg_left hBV (by linarith))
    · exact (hsmall K _ F ξ W hK hL (le_of_not_gt h₁) hF (hW.of_le (Nat.zero_le _))).trans
        (mul_le_mul_of_nonneg_left hsm (by linarith))
  have hrows : (∑ p ∈ cubeRows K F, ‖normalizedColumn ξ W X p.2 p.1‖ ^ 2) ≤ 4 * H ^
    4 * (F * V) := by
    by_cases hY : 1 ≤ Y
    · have hYX : Y ≤ R * X := (min_le_left ..).trans (le_mul_of_one_le_left (by linarith) hR)
      refine truncated_rows_bound hW ξ (by linarith) hY hYX hH (by positivity) ?_ ?_ hchild'
      · intro s hs
        exact (hA' hD hX ((le_mul_of_one_le_right (by linarith) hF).trans hsize) s hs).trans
          (mul_le_mul_of_nonneg_right (by linarith) (by linarith) : A * d ≤ H)
      · intro b hb
        exact (hcomp D K X F _ ξ W hD hK hX hF hKX hsize (cubeNorm_one_le (mem_cubeIdeals.mp hb).1)
          (mem_cubeIdeals.mp hb).2 hW).trans (mul_le_mul_of_nonneg_left hCV (by linarith))
    · have h := hchild' 1 ⟨one_ne_zero,
        isCoprime_one_left⟩ (by rw [cubeNorm_one]; exact lt_of_not_ge hY)
      rw [cubeNorm_one, div_one] at h
      exact h.trans (le_mul_of_one_le_left (by positivity) (by nlinarith [one_le_pow₀ hH (n := 4)]))
  change (∑ p ∈ cubeRows K F, ‖columnSum ξ W X p.2 p.1 / (Real.sqrt X : ℂ)‖ ^ 2) ≤ _ at hrows
  rw [cubeRows_normalizedColumn _ _ _ _ _ (by linarith) (by linarith)] at hrows
  have hE := (mul_le_mul_iff_right₀ (by linarith : 0 < F)).mp
    (hrows.trans_eq (show _ = F * (4 * H ^ 4 * V) by ring))
  have hε' : d ^ 5 = D ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ D)]
    congr 1
    dsimp [e]; norm_num
  refine hE.trans_eq ?_
  rw [← hε']
  dsimp only [H, V]
  ring

end Masullo.QRH.MeanSquare
