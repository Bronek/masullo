import WeilExplicit.DensityDisk
import WeilExplicit.DensityMeanSquare
import WeilExplicit.ZeroCount

/-!
# Counting zeros to the right of the critical line in a dyadic shell

Fix `0 < δ ≤ 1/8`. Each zero `ρ` with `Re ρ ≥ 1/2 + 2δ` and `T ≤ Im ρ ≤ 2T` makes the mollified
zeta function equal to `-1` at the centre of the disc of radius `δ` about `ρ`, so that disc
carries at least `π δ²` of the mean square of `mollified δ T`. The discs lie in the rectangle
`[1/2 + δ, 2] × [T - 1, 2T + 1]` and overlap at most `O(log T)` times, so the number of such
zeros is `O(log T · T^{1-δ²/3})`.

Part of a Carlson-type mean-square zero-density argument due to OpenAI Codex (E36),
formalised by Claude.
-/

namespace WeilExplicit

open Complex MeasureTheory Set Metric Real

theorem differentiable_mollifier (U : ℕ) : Differentiable ℂ (mollifier U) := by
  intro s
  unfold mollifier
  refine DifferentiableAt.fun_sum fun d hd ↦ (differentiableAt_const _).mul
    (differentiableAt_id.neg.const_cpow (Or.inl ?_))
  have := (Finset.mem_Icc.mp hd).1
  exact_mod_cast (by omega : d ≠ 0)

theorem differentiableAt_mollified (δ T : ℝ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (mollified δ T) s :=
  ((differentiableAt_riemannZeta hs).mul (differentiable_mollifier _ s)).sub_const 1

theorem measurable_mollified (δ T : ℝ) : Measurable (mollified δ T) :=
  measurable_of_continuousOn_compl_singleton 1 fun _ hs ↦
    (differentiableAt_mollified δ T hs).continuousAt.continuousWithinAt

/-- The rectangle `[1/2 + δ, 2] × [T - 1, 2T + 1]` carrying the discs about zeros at height `T`. -/
def densRect (δ T : ℝ) : Set ℂ := re ⁻¹' Icc (1 / 2 + δ) 2 ∩ im ⁻¹' Icc (T - 1) (2 * T + 1)

theorem measurableSet_densRect (δ T : ℝ) : MeasurableSet (densRect δ T) :=
  (measurableSet_Icc.preimage Complex.measurable_re).inter
    (measurableSet_Icc.preimage Complex.measurable_im)

/-- The mean square of `mollified δ T` over `densRect δ T`. -/
theorem rect_mean_square {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    ∃ C, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      ∫⁻ z in densRect δ T, ‖mollified δ T z‖ₑ ^ 2 ≤ ENNReal.ofReal (C * T ^ (1 - δ ^ 2 / 3)) := by
  obtain ⟨C, hC⟩ := mean_square_mollified hδ hδ'
  refine ⟨2 * max C 0, by positivity, fun T hT ↦ ?_⟩
  set h : ℂ → ENNReal := fun z ↦ ‖mollified δ T z‖ₑ ^ 2
  have hθ : 0 ≤ max C 0 * T ^ (1 - δ ^ 2 / 3) := by positivity
  calc ∫⁻ z in densRect δ T, h z
      = ∫⁻ p in Icc (1 / 2 + δ) 2 ×ˢ Icc (T - 1) (2 * T + 1), h (p.1 + p.2 * I) := by
        rw [show densRect δ T =
            measurableEquivRealProd ⁻¹' (Icc (1 / 2 + δ) 2 ×ˢ Icc (T - 1) (2 * T + 1)) by
          ext z; rfl]
        simpa only [measurableEquivRealProd_apply, re_add_im] using
          Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
            measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ ↦ h (p.1 + p.2 * I))
            (Icc (1 / 2 + δ) 2 ×ˢ Icc (T - 1) (2 * T + 1))
    _ ≤ ∫⁻ u in Icc (1 / 2 + δ) 2, ∫⁻ t in Icc (T - 1) (2 * T + 1), h (u + t * I) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_le _
    _ ≤ ∫⁻ u in Icc (1 / 2 + δ) 2, ENNReal.ofReal (max C 0 * T ^ (1 - δ ^ 2 / 3)) :=
        setLIntegral_mono' measurableSet_Icc fun u hu ↦ (hC T hT u hu.1 hu.2).trans
          (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
    _ = ENNReal.ofReal (max C 0 * T ^ (1 - δ ^ 2 / 3)) * ENNReal.ofReal (2 - (1 / 2 + δ)) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ = ENNReal.ofReal (max C 0 * T ^ (1 - δ ^ 2 / 3) * (2 - (1 / 2 + δ))) :=
        (ENNReal.ofReal_mul hθ).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- The number of zeros with `Re ρ ≥ 1/2 + 2δ` and `T ≤ Im ρ ≤ 2T`, counted in any finite
family, is `O(log(2T + 4) · T^{1-δ²/3})`. -/
theorem shell_card_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    ∃ B, ∀ T : ℝ, 2 ≤ T → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ stripZeros ∧ 1 / 2 + 2 * δ ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ 2 * T) →
      (S.card : ℝ) ≤ B * (Real.log (2 * T + 4) * T ^ (1 - δ ^ 2 / 3)) := by
  classical
  obtain ⟨C, hC0, hC⟩ := rect_mean_square hδ hδ'
  set K := 16 / Real.log (21 / 20)
  have hK : 0 < K := div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨K * C / (π * δ ^ 2), fun T hT S hS ↦ ?_⟩
  set h : ℂ → ENNReal := fun z ↦ ‖mollified δ T z‖ₑ ^ 2
  have hm : Measurable h := (measurable_mollified δ T).enorm.pow_const 2
  set N := K * Real.log (2 * T + 4)
  have hN : 0 ≤ N := mul_nonneg hK.le (Real.log_nonneg (by linarith))
  have hdisc : ∀ ρ ∈ S, ENNReal.ofReal (π * δ ^ 2) ≤ ∫⁻ z, (ball ρ δ).indicator h z := by
    intro ρ hρ
    obtain ⟨⟨hz, -, -⟩, -, hlo, -⟩ := hS ρ hρ
    rw [lintegral_indicator measurableSet_ball]
    refine disk_lower (measurable_mollified δ T) hδ (fun z hz' ↦ ?_) ?_
    · refine (differentiableAt_mollified δ T fun he ↦ ?_).differentiableWithinAt
      have h2 : |(z - ρ).im| ≤ δ :=
        (abs_im_le_norm _).trans (by rwa [mem_closedBall, dist_eq_norm] at hz')
      rw [he, sub_im, one_im, abs_le] at h2
      linarith [h2.2]
    · simp [mollified, hz]
  have hpt : ∀ z, ∑ ρ ∈ S, (ball ρ δ).indicator h z ≤
      (densRect δ T).indicator (fun z ↦ ENNReal.ofReal N * h z) z := by
    intro z
    have hsum : ∑ ρ ∈ S, (ball ρ δ).indicator h z =
        ((S.filter fun ρ ↦ z ∈ ball ρ δ).card : ENNReal) * h z := by
      simp [indicator, ← Finset.sum_filter, nsmul_eq_mul]
    rw [hsum]
    by_cases hz : z ∈ densRect δ T
    · rw [indicator_of_mem hz]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw := window_zero_count z.im (S.filter fun ρ ↦ z ∈ ball ρ δ) fun ρ hρ ↦ by
        obtain ⟨hρS, hρb⟩ := Finset.mem_filter.mp hρ
        obtain ⟨⟨-, h0, h1⟩, -⟩ := hS ρ hρS
        refine ⟨h0, h1, ?_⟩
        have hd := (abs_im_le_norm (ρ - z)).trans_lt (show ‖ρ - z‖ < δ by
          rwa [← dist_eq_norm, dist_comm])
        exact hd.le.trans (by linarith)
      have him := hz.2
      simp only [mem_preimage, mem_Icc] at him
      calc ((S.filter fun ρ ↦ z ∈ ball ρ δ).card : ℝ)
          = ∑ ρ ∈ S.filter fun ρ ↦ z ∈ ball ρ δ, (1 : ℝ) := by simp
        _ ≤ ∑ ρ ∈ S.filter fun ρ ↦ z ∈ ball ρ δ, (zeroMult ρ : ℝ) :=
            Finset.sum_le_sum fun ρ hρ ↦ by
              exact_mod_cast zeroMult_pos (hS ρ (Finset.mem_filter.mp hρ).1).1
        _ ≤ K * Real.log (|z.im| + 3) := hw
        _ ≤ N := by
            refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hK.le
            rw [abs_of_pos (by linarith)]; linarith
    · rw [indicator_of_notMem hz]
      have he : (S.filter fun ρ ↦ z ∈ ball ρ δ) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun ρ hρ hzb ↦ hz ?_
        obtain ⟨⟨-, -, h1⟩, hre, hlo, hhi⟩ := hS ρ hρ
        have hd : ‖z - ρ‖ < δ := by rwa [mem_ball, dist_eq_norm] at hzb
        have h1' := (abs_re_le_norm (z - ρ)).trans hd.le
        have h2' := (abs_im_le_norm (z - ρ)).trans hd.le
        simp only [sub_re, sub_im, abs_le] at h1' h2'
        simp only [densRect, mem_inter_iff, mem_preimage, mem_Icc]
        refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]
  have hchain : (S.card : ENNReal) * ENNReal.ofReal (π * δ ^ 2) ≤
      ENNReal.ofReal N * ENNReal.ofReal (C * T ^ (1 - δ ^ 2 / 3)) := by
    calc (S.card : ENNReal) * ENNReal.ofReal (π * δ ^ 2)
        = ∑ ρ ∈ S, ENNReal.ofReal (π * δ ^ 2) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ρ ∈ S, ∫⁻ z, (ball ρ δ).indicator h z := Finset.sum_le_sum hdisc
      _ = ∫⁻ z, ∑ ρ ∈ S, (ball ρ δ).indicator h z :=
          (lintegral_finsetSum S fun ρ _ ↦ hm.indicator measurableSet_ball).symm
      _ ≤ ∫⁻ z, (densRect δ T).indicator (fun z ↦ ENNReal.ofReal N * h z) z := lintegral_mono hpt
      _ = ENNReal.ofReal N * ∫⁻ z in densRect δ T, h z := by
          rw [lintegral_indicator (measurableSet_densRect δ T), lintegral_const_mul _ hm]
      _ ≤ _ := by gcongr; exact hC T hT
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul hN, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hpd : 0 < π * δ ^ 2 := by positivity
  rw [show K * C / (π * δ ^ 2) * (Real.log (2 * T + 4) * T ^ (1 - δ ^ 2 / 3)) =
    N * (C * T ^ (1 - δ ^ 2 / 3)) / (π * δ ^ 2) by simp only [N]; ring, le_div_iff₀ hpd]
  exact hchain

end WeilExplicit
