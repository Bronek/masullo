import Masullo.QRH.MeanSquare.Forms
import Masullo.QRH.MeanSquare.ReflectionMellin

/-! # Vertical decay of the Mellin transforms of the admissible tests -/

noncomputable section

open Complex Set MeasureTheory Filter Asymptotics
open scoped ContDiff Topology

namespace Masullo.QRH.MeanSquare

theorem UnitTest.derivative {I : TestInterval} {m : ℕ} {W : ℝ → ℂ} (h : UnitTest I (m+1) W) :
    UnitTest I m (deriv W) := by
  refine ⟨(contDiff_infty_iff_deriv.mp h.1).2, tsupport_deriv_subset.trans h.2.1,
    fun j hj x hx => ?_⟩
  rw [← iteratedDeriv_succ']
  exact h.2.2 _ (Nat.succ_le_succ hj) _ hx

private theorem mellin_eq_test_interval {I : TestInterval} {W : ℝ → ℂ}
    (hs : tsupport W ⊆ Icc I.lo I.hi) (s : ℂ) :
    mellin W s = ∫ x in (I.lo / 2)..(I.hi + 1), (x : ℂ) ^ (s - 1) * W x := by
  have h₁ := I.pos
  have h₂ := I.ordered
  have hz {x : ℝ} (hx : x ∉ Icc I.lo I.hi) : W x = 0 :=
    by_contra fun h => hx (hs (subset_tsupport _ h))
  rw [mellin, intervalIntegral.integral_of_le (by linarith)]
  simp only [smul_eq_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioi 0) (fun x hx => mul_eq_zero_of_right _ (hz (fun h => hx (lt_of_lt_of_le h₁ h.1)))),
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc _ _)
      (fun x hx => mul_eq_zero_of_right _ (hz (fun h =>
        hx ⟨by linarith [h.1], by linarith [h.2]⟩)))]

private theorem cpow_continuousOn_test (I : TestInterval) (s : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ s) (uIcc (I.lo / 2) (I.hi + 1)) := by
  have := I.pos
  have := I.ordered
  rw [uIcc_of_le (by linarith)]
  exact fun x hx => (continuousAt_ofReal_cpow_const _ _
    (Or.inr (by linarith [hx.1]))).continuousWithinAt

/-- Integration by parts with both endpoints outside the support. -/
theorem UnitTest.mellin_deriv {I : TestInterval} {m : ℕ} {W : ℝ → ℂ} (h : UnitTest I (m+1) W)
    (s : ℂ) : mellin (deriv W) (s+1) = -s * mellin W s := by
  have h₁ := I.pos
  have h₂ := I.ordered
  let a := I.lo / 2
  let b := I.hi + 1
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have hpow (x : ℝ) (hx : x ∈ Ioo (min a b) (max a b)) :
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ s) (s * x ^ (s - 1)) x := by
    have hx₀ : x ≠ 0 := by rw [min_eq_left hab] at hx; dsimp [a] at hx; linarith [hx.1]
    by_cases he : s = 0
    · simpa [he] using hasDerivAt_const x (1 : ℂ)
    exact hasDerivAt_ofReal_cpow_const hx₀ he
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (cpow_continuousOn_test I s) h.1.continuous.continuousOn hpow
    (fun x _ => (h.1.differentiable (by simp) x).hasDerivAt)
    ((continuousOn_const.mul (cpow_continuousOn_test I (s-1))).intervalIntegrable)
    (h.derivative.1.continuous.intervalIntegrable _ _)
  have hz {x : ℝ} (hx : x ∉ Icc I.lo I.hi) : W x = 0 :=
    by_contra fun h' => hx (h.2.1 (subset_tsupport _ h'))
  have ha : W (I.lo / 2) = 0 := hz (by intro hx; linarith [hx.1])
  have hb : W (I.hi + 1) = 0 := hz (by intro hx; linarith [hx.2])
  rw [mellin_eq_test_interval h.derivative.2.1, mellin_eq_test_interval h.2.1, add_sub_cancel_right]
  simp only [ha, hb, mul_zero, sub_self, zero_sub, mul_assoc,
    intervalIntegral.integral_const_mul] at H
  simpa only [neg_mul] using H

private theorem mellin_test_bound (I : TestInterval) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ W : ℝ → ℂ, UnitTest I 0 W → ∀ s : ℂ, s.re ∈ Icc a b → ‖mellin W s‖ ≤ C := by
  have h₁ := I.pos
  have h₂ := I.ordered
  let B := Icc (I.lo / 2) (I.hi + 1) ×ˢ Icc a b
  have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C,hC⟩ := hB.exists_bound_of_continuousOn (f := fun p : ℝ × ℝ => p.1 ^ (p.2 - 1))
    (continuous_fst.continuousOn.rpow (continuous_snd.sub continuous_const).continuousOn
      (fun p hp => Or.inl (by linarith [hp.1.1] : p.1 ≠ 0)))
  refine ⟨max C 0 * |I.hi + 1 - I.lo / 2|, by positivity, fun W hW s hs => ?_⟩
  rw [mellin_eq_test_interval hW.2.1]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le (by linarith)] at hx
  have hx₀ : 0 < x := by linarith [hx.1]
  have hw : ‖W x‖ ≤ 1 := by
    by_cases hh : W x = 0
    · simp [hh]
    simpa using hW.2.2 0 le_rfl x (hW.2.1 (subset_tsupport _ hh))
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx₀, sub_re, one_re]
  have he := hC (x,s.re) ⟨⟨hx.1.le,hx.2⟩,hs⟩
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)] at he
  exact (mul_le_of_le_one_right (Real.rpow_nonneg hx₀.le _) hw).trans (he.trans (le_max_left ..))

/-- A single constant bounds the Mellin transform on a closed vertical strip
for every test in the prescribed derivative unit ball. -/
theorem UnitTest.mellin_strip_decay (I : TestInterval) (m : ℕ) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ W : ℝ → ℂ, UnitTest I m W → ∀ s : ℂ, s.re ∈ Icc a b →
      ‖mellin W s‖ * (1 + |s.im|) ^ m ≤ C := by
  induction m generalizing a b with
  | zero => simpa only [pow_zero, mul_one] using mellin_test_bound I a b
  | succ m ih =>
    obtain ⟨C,hC,h₀⟩ := mellin_test_bound I a b
    obtain ⟨D,hD,h₁⟩ := ih (a+1) (b+1)
    refine ⟨max (C * 2 ^ (m+1)) (2 * D), (by positivity : 0 ≤ C * 2 ^ (m+1)).trans
      (le_max_left ..), fun W hW s hs => ?_⟩
    by_cases ht : |s.im| ≤ 1
    · apply le_trans _ (le_max_left ..)
      exact mul_le_mul (h₀ W (hW.of_le (Nat.zero_le _)) s hs)
        (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) hC
    have he := h₁ (deriv W) hW.derivative (s+1) (by simpa using hs)
    rw [hW.mellin_deriv, norm_mul, norm_neg] at he
    simp only [add_im, one_im, add_zero] at he
    have ht' : 1 + |s.im| ≤ 2 * ‖s‖ := by linarith [s.abs_im_le_norm]
    apply le_trans _ (le_max_right ..)
    calc
      _ = (1 + |s.im|) * (‖mellin W s‖ * (1 + |s.im|) ^ m) := by ring
      _ ≤ 2 * ‖s‖ * (‖mellin W s‖ * (1 + |s.im|) ^ m) :=
        mul_le_mul_of_nonneg_right ht' (by positivity)
      _ = 2 * (‖s‖ * ‖mellin W s‖ * (1 + |s.im|) ^ m) := by ring
      _ ≤ 2 * D := by linarith

/-- The Mellin transform of a positive compactly supported test is entire. -/
theorem UnitTest.mellin_entire {I : TestInterval} {m : ℕ} {W : ℝ → ℂ} (h : UnitTest I m W) :
    Differentiable ℂ (mellin W) := by
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (h.1.continuous.locallyIntegrable.locallyIntegrableOn _)
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop I.hi] with x hx
    simp [image_eq_zero_of_notMem_tsupport (f := W) (fun ht => hx.not_ge (h.2.1 ht).2)]
  · linarith
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds I.pos)] with x hx
    simp [image_eq_zero_of_notMem_tsupport (f := W) (fun ht =>
      (show x < I.lo from hx).not_ge (h.2.1 ht).1)]
  · linarith

end Masullo.QRH.MeanSquare
