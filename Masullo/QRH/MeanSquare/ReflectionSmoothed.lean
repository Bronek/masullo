import Masullo.QRH.MeanSquare.ReflectionFunctionalEquation
import Masullo.QRH.MeanSquare.ReflectionStrip
import Mathlib.Analysis.MellinInversion

/-! # The smoothed Patterson reflection identity at one congruence cusp -/

noncomputable section

open NumberField Complex MeasureTheory Set Filter Asymptotics
open scoped ComplexConjugate Topology

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Index := {m : 𝓔 // m ≠ 0}

private local instance : Countable 𝓔 := by
  apply Function.Surjective.countable (f := fun p : ℤ × ℤ => (p.1 : 𝓔) + p.2 * eisOmega)
  intro m
  obtain ⟨a, b, h⟩ := eisInteger_coordinates m
  exact ⟨(a,b), h.symm⟩

private def line (x y : ℝ) : ℂ := x + y * I
private abbrev mass (m : Index) : ℝ := normSq (pattersonFrequency m)

private theorem mass_pos (m : Index) : 0 < mass m := normSq_pos.mpr (div_ne_zero
  (fun hz => m.property (eisEmbedding_injective (hz.trans (map_zero _).symm)))
  (pow_ne_zero _ (fun hz => eisLambda_prime.ne_zero (eisEmbedding_injective (hz.trans (map_zero
    _).symm)))))

/-- The coefficient including its additive translation and its angular factor. -/
def pattersonAngularCoefficient (τ : ℂ → ℂ) (barred : Bool) (z : ℂ) (m : 𝓔) : ℂ :=
  let μ := pattersonFrequency m
  (conj (τ μ) / 27 * pattersonCharacter (μ*z)) *
    (conj (if barred then μ else conj μ) / ‖μ‖)

private theorem angular_norm (τ : ℂ → ℂ) (barred : Bool) (z : ℂ) (m : Index) :
    ‖pattersonAngularCoefficient τ barred z m‖ = ‖conj (τ (pattersonFrequency m)) / 27‖ := by
  have hm := norm_ne_zero_iff.mpr ((normSq_pos.mp (mass_pos m)))
  cases barred <;> simp [pattersonAngularCoefficient, norm_pattersonCharacter, hm]

private theorem summable_angular {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (barred : Bool) (z : ℂ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun m : Index => ‖pattersonAngularCoefficient τ barred z m‖ * mass m ^ (-σ) := by
  apply ((ht.summable_normalized_dirichlet hσ).subtype (· ≠ 0)).congr
  intro m
  rw [angular_norm]
  rfl

private theorem dirichlet_eq_tsum (τ : ℂ → ℂ) (barred : Bool) (z s : ℂ) :
    pattersonCuspDirichlet τ barred z s =
      ∑' m : Index, pattersonAngularCoefficient τ barred z m * (mass m : ℂ) ^ (-s) := rfl

private theorem line_norm_cpow {q : ℝ} (hq : 0 < q) (σ y : ℝ) :
    ‖(q : ℂ) ^ (-line σ y)‖ = q ^ (-σ) := by
  simp [line, norm_cpow_eq_rpow_re_of_pos hq]

private theorem integral_dirichlet_line {ι : Type*} [Countable ι] (a : ι → ℂ) (q : ι → ℝ)
    (hq : ∀ i, 0 < q i) (σ : ℝ) (ha : Summable fun i => ‖a i‖ * q i ^ (-σ))
    (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ y : ℝ, F y * ∑' i, a i * (q i : ℂ) ^ (-line σ y)) =
      ∑' i, a i * ∫ y : ℝ, F y * (q i : ℂ) ^ (-line σ y) := by
  let M := fun (i : ι) (y : ℝ) => F y * (a i * (q i : ℂ) ^ (-line σ y))
  have hn (i : ι) (y : ℝ) : ‖M i y‖ = (‖a i‖ * q i ^ (-σ)) * ‖F y‖ := by
    simp only [M, norm_mul, line_norm_cpow (hq i)]; ring
  have hi (i : ι) : Integrable (M i) := by
    have hc : Continuous fun y : ℝ => a i * (q i : ℂ) ^ (-line σ y) := by
      unfold line
      fun_prop (disch := exact ofReal_ne_zero.mpr (hq i).ne')
    apply (hF.norm.const_mul (‖a i‖ * q i ^ (-σ))).mono' (hF.1.mul hc.aestronglyMeasurable)
    exact ae_of_all _ fun y => (hn i y).le
  have hs : Summable fun i => ∫ y : ℝ, ‖M i y‖ := by
    simpa only [hn, integral_const_mul] using ha.mul_right (∫ y, ‖F y‖)
  calc
    _ = ∫ y, ∑' i, M i y := by simp only [M, tsum_mul_left]
    _ = ∑' i, ∫ y, M i y := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [← integral_const_mul]
      apply integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp [M]
      ring

private theorem test_mellin_integrable {J : TestInterval} {m : ℕ} {W : ℝ → ℂ}
    (h : UnitTest J m W) (σ : ℝ) : MellinConvergent W σ := by
  apply mellinConvergent_of_isBigO_rpow (a := σ+1) (b := σ-1)
    (h.1.continuous.locallyIntegrable.locallyIntegrableOn _)
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop J.hi] with x hx
    simp [image_eq_zero_of_notMem_tsupport (f := W) (fun ht => hx.not_ge (h.2.1 ht).2)]
  · simp
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds J.pos)] with x hx
    simp [image_eq_zero_of_notMem_tsupport (f := W) (fun ht => (show x < J.lo from hx).not_ge (h.2.1
      ht).1)]
  · simp

private theorem integrable_vertical_bound {F : ℝ → ℂ} (hF : Continuous F) {C : ℝ}
    (h : ∀ y, ‖F y‖ * (1 + |y|)^2 ≤ C) : Integrable F := by
  apply (integrable_inv_one_add_sq.const_mul C).mono' hF.aestronglyMeasurable
  refine ae_of_all _ ?_
  intro y
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg y, sq_abs y] : 1+y^2 ≤ (1+|y|)^2)
    (norm_nonneg _)).trans (h y)

private theorem test_vertical_integrable {J : TestInterval} {W : ℝ → ℂ}
    (hW : UnitTest J 2 W) (σ : ℝ) : VerticalIntegrable (mellin W) σ := by
  obtain ⟨C, -, hC⟩ := UnitTest.mellin_strip_decay J 2 σ σ
  apply integrable_vertical_bound (hW.mellin_entire.continuous.comp (by fun_prop)) (C := C)
  intro y
  simpa using hC W hW (σ + y*I) (by simp)

private theorem pos_div_cpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x/y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (div_pos hx hy).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), cpow_def_of_ne_zero (ofReal_ne_zero.mpr
      hy.ne'),
    ← ofReal_log (div_pos hx hy).le, ← ofReal_log hx.le, ← ofReal_log hy.le,
    Real.log_div hx.ne' hy.ne', ofReal_sub, sub_mul, exp_sub]

/-- Sum of the translated angular coefficients against the original test at scale `X`. -/
def pattersonSmoothed (τ : ℂ → ℂ) (z : ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' m : Index, pattersonAngularCoefficient τ true z m * W (mass m / X) / Real.sqrt X

private def smoothedIntegrand (τ : ℂ → ℂ) (z : ℂ) (W : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (X : ℂ) ^ s / Real.sqrt X * continuedPattersonDirichlet τ true z s

private theorem smoothed_right_integral (hB : DLMFBesselMellin) {τ : ℂ →
    ℂ} (ht : PattersonCoefficients τ)
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 2 W) (z : ℂ) {X : ℝ} (hX : 0 < X) :
    pattersonSmoothed τ z W X =
      (∫ y : ℝ, smoothedIntegrand τ z W X (line (3/2) y)) / (2*Real.pi) := by
  let σ : ℝ := 3/2
  let F := fun y : ℝ => mellin W (line σ y) * (X : ℂ) ^ (line σ y) / (Real.sqrt X : ℂ)
  have hF : Integrable F := by
    have hc : Continuous F := (hW.mellin_entire.continuous.comp (by unfold line; fun_prop)).mul
      (g := fun y : ℝ => (X : ℂ) ^ (line σ y)) (by
        unfold line; fun_prop (disch := exact ofReal_ne_zero.mpr hX.ne')) |>.div_const _
    apply ((test_vertical_integrable hW σ).norm.mul_const (X^σ /
      Real.sqrt X)).mono' hc.aestronglyMeasurable
    apply ae_of_all
    intro y
    dsimp only [F]
    rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hX]
    simp [line, abs_of_nonneg (Real.sqrt_nonneg X), mul_div_assoc]
  have hr : (∫ y : ℝ, smoothedIntegrand τ z W X (line σ y)) =
      ∑' m : Index, pattersonAngularCoefficient τ true z m * ∫ y : ℝ, F y * (mass m : ℂ) ^
        (-line σ y) := by
    rw [← integral_dirichlet_line _ _ mass_pos σ (summable_angular ht true z (by norm_num [σ]))
      F hF]
    apply integral_congr_ae (ae_of_all _ fun y => ?_)
    unfold smoothedIntegrand
    rw [ht.continued_eq_dirichlet hB true z (by norm_num [line, σ]), dirichlet_eq_tsum]
  change _ = (∫ y : ℝ, smoothedIntegrand τ z W X (line σ y)) / _
  rw [hr, ← tsum_div_const]
  apply tsum_congr
  intro m
  let q := mass m
  have hq := mass_pos m
  have hx := div_pos hq hX
  have HM := mellinInv_mellin_eq σ W hx (test_mellin_integrable hW σ) (test_vertical_integrable
    hW σ)
    hW.1.continuous.continuousAt
  have he (y : ℝ) : F y * (q : ℂ) ^ (-line σ y) =
      (1/(Real.sqrt X : ℂ)) * (((q/X : ℝ) : ℂ) ^ (-line σ y) * mellin W (line σ y)) := by
    dsimp only [F]
    rw [pos_div_cpow hq hX, cpow_neg, cpow_neg]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  change _ = _ * (∫ y, F y * (q : ℂ) ^ (-line σ y)) / _
  simp only [he, integral_const_mul]
  dsimp only [mellinInv, smul_eq_mul] at HM
  change (1/(2*Real.pi) : ℝ) • (∫ y, ((q/X : ℝ) : ℂ) ^ (-line σ y) * mellin W (line σ y)) = _ at HM
  rw [real_smul, ofReal_div, ofReal_one, ofReal_mul, ofReal_ofNat] at HM
  rw [← HM]
  ring


private def kernelScale (X N : ℝ) : ℝ := (2*Real.pi)^4 * X / N^2

private theorem sqrt_cpow {X : ℝ} (hX : 0 < X) : (Real.sqrt X : ℂ) = (X : ℂ) ^ (1/2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hX.le]
  push_cast
  rfl

private theorem natPow_cpow {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℂ) :
    ((x ^ n : ℝ) : ℂ) ^ t = (x : ℂ) ^ ((n : ℂ)*t) := by
  rw [← Real.rpow_natCast, ← cpow_mul_ofReal_nonneg hx.le]
  push_cast
  rfl

private theorem conductor_powers {X N : ℝ} (hX : 0 < X) (hN : 0 < N) (t : ℂ) :
    (X : ℂ) ^ (1/2-t) / Real.sqrt X * (N : ℂ) ^ (2*t) * ((2*Real.pi : ℝ) : ℂ) ^ (-4*t) =
      ((kernelScale X N : ℝ) : ℂ) ^ (-t) := by
  have hp : 0 < 2*Real.pi := by positivity
  have hx : (X : ℂ) ^ (1/2-t) / Real.sqrt X = (X : ℂ) ^ (-t) := by
    rw [sqrt_cpow hX, show 1/2-t = 1/2 + -t by ring, cpow_add _ _ (ofReal_ne_zero.mpr hX.ne')]
    apply mul_div_cancel_left₀
    exact fun hz => hX.ne' (ofReal_eq_zero.mp (((cpow_eq_zero_iff _ _).mp hz).1))
  rw [hx, kernelScale, pos_div_cpow (mul_pos (pow_pos hp _) hX) (pow_pos hN _),
    ofReal_mul ((2*Real.pi)^4) X, ofReal_mul_cpow (pow_pos hp 4).le, natPow_cpow hp, natPow_cpow hN]
  push_cast
  rw [show (2:ℂ)*(-t) = -(2*t) by ring, cpow_neg (N : ℂ)]
  simp only [div_eq_mul_inv, inv_inv]
  rw [show (4:ℂ)*(-t) = -4*t by ring]
  ring

private def leftIntegrand (W : ℝ → ℂ) (X N y : ℝ) : ℂ :=
  reflectionKernelAmplitude W 0 (line 1 y) * (kernelScale X N : ℂ) ^ (-line 1 y)

private theorem leftIntegrand_bound (hΓ : DLMFGammaVertical) {J : TestInterval} {W : ℝ → ℂ}
    (hW : UnitTest J 6 W) {X N : ℝ} (hX : 0 < X) (hN : 0 < N) :
    ∃ C ≥ (0:ℝ), ∀ y : ℝ, ‖leftIntegrand W X N y‖ * (1+|y|)^2 ≤ C := by
  have hS : 0 < kernelScale X N := by dsimp [kernelScale]; positivity
  obtain ⟨C, hC, h⟩ := norm_reflectionKernelAmplitude hΓ (a := 1) (b := 1) (by norm_num) 0 J
  have htest : UnitTest J (0 + ⌈4*max (1 : ℝ) 0⌉₊ + 2) W := by norm_num; exact hW
  refine ⟨C * (kernelScale X N) ^ (-(1:ℝ)), by positivity, ?_⟩
  intro y
  have H := h W htest (line 1 y) (by simp [line])
  simp only [line, add_im, ofReal_im, zero_add, mul_I_im, ofReal_re] at H
  rw [leftIntegrand, norm_mul, line_norm_cpow hS, mul_right_comm]
  exact mul_le_mul_of_nonneg_right H (by positivity)

private theorem leftIntegrand_integrable (hΓ : DLMFGammaVertical) {J : TestInterval} {W : ℝ → ℂ}
    (hW : UnitTest J 6 W) {X N : ℝ} (hX : 0 < X) (hN : 0 < N) : Integrable (leftIntegrand W X N)
      := by
  obtain ⟨C, -, hC⟩ := leftIntegrand_bound hΓ hW hX hN
  apply integrable_vertical_bound _ hC
  apply Continuous.mul
  · apply continuous_iff_continuousAt.mpr
    intro y
    exact (differentiableAt_reflectionKernelAmplitude hW 0 (t := line 1 y)
      (by norm_num [line])).continuousAt.comp (by unfold line; fun_prop)
  · have hS : 0 < kernelScale X N := by dsimp [kernelScale]; positivity
    dsimp only [line]
    fun_prop (disch := exact ofReal_ne_zero.mpr hS.ne')

private theorem smoothed_left_value {τ : ℂ → ℂ} {z z' η : ℂ} {X N : ℝ} (hX : 0 < X)
    (hN : 0 < N) (W : ℝ → ℂ)
    (hFE : ∀ s : ℂ, s.re < 0 → continuedPattersonDirichlet τ true z s =
      η * (N : ℂ) ^ (1-2*s) * (reflectionGammaFactor (1-s) / reflectionGammaFactor s) *
        pattersonCuspDirichlet τ false z' (1-s)) (y : ℝ) :
    smoothedIntegrand τ z W X (line (-(1/2)) (-y)) =
      η * (leftIntegrand W X N y * pattersonCuspDirichlet τ false z' (line (3/2) y)) := by
  let t := line 1 y
  have hst : line (-(1/2)) (-y) = 1/2-t := by dsimp [line, t]; push_cast; ring
  have hdt : line (3/2) y = 1/2+t := by dsimp [line, t]; push_cast; ring
  rw [smoothedIntegrand, hFE _ (by norm_num [line]), hst, hdt,
    show 1-(1/2-t) =
      1/2+t by ring, show 1-2*(1/2-t) = 2*t by ring, reflectionGammaFactor_centered_ratio]
  dsimp only [leftIntegrand, reflectionKernelAmplitude]
  change _ = η * (((-t)^0 * mellin W (1/2-t) * reflectionGammaRatio t *
    (kernelScale X N : ℂ) ^ (-t)) * _)
  rw [← conductor_powers hX hN t]
  ring

set_option maxHeartbeats 700000 in
private theorem smoothed_left_integral (hΓ : DLMFGammaVertical) {τ : ℂ →
    ℂ} (ht : PattersonCoefficients τ)
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 6 W) {z z' η : ℂ} {X N : ℝ}
    (hX : 0 < X) (hN : 0 < N)
    (hFE : ∀ s : ℂ, s.re < 0 → continuedPattersonDirichlet τ true z s =
      η * (N : ℂ) ^ (1-2*s) * (reflectionGammaFactor (1-s) / reflectionGammaFactor s) *
        pattersonCuspDirichlet τ false z' (1-s)) :
    (∫ y : ℝ, smoothedIntegrand τ z W X (line (-(1/2)) y)) / (2*Real.pi) =
      η * ∑' m : Index, pattersonAngularCoefficient τ false z' m / Real.sqrt (mass m) *
        reflectionKernel W 0 0 (mass m*X / N^2) := by
  let S := kernelScale X N
  have hS : 0 < S := by dsimp [S, kernelScale]; positivity
  let F := leftIntegrand W X N
  let A := pattersonAngularCoefficient τ false z'
  have htest : UnitTest J (0 + ⌈4*max (1 : ℝ) 0⌉₊ + 2) W := by norm_num; exact hW
  have hi : (∫ y : ℝ, smoothedIntegrand τ z W X (line (-(1/2)) y)) =
      η * ∑' m : Index, A m * ∫ y : ℝ, F y * (mass m : ℂ) ^ (-line (3/2) y) := by
    rw [← integral_dirichlet_line _ _ mass_pos (3/2) (summable_angular ht false z' (by norm_num)) F
      (leftIntegrand_integrable hΓ hW hX hN), ← integral_const_mul]
    rw [← integral_neg_eq_self (f := fun y : ℝ => smoothedIntegrand τ z W X (line (-(1/2)) y))]
    apply integral_congr_ae (ae_of_all _ fun y => ?_)
    rw [smoothed_left_value hX hN W hFE, dirichlet_eq_tsum]
  rw [hi, mul_div_assoc, ← tsum_div_const]
  congr 1
  apply tsum_congr
  intro m
  let q := mass m
  have hq : 0 < q := mass_pos m
  rw [reflectionKernel_shift hΓ (a := 0) (b := 1) (by norm_num) (by norm_num) 0 htest (by
    positivity)]
  have hterm (y : ℝ) : F y * (q : ℂ) ^ (-line (3/2) y) =
      (1/(Real.sqrt q : ℂ)) * (reflectionKernelAmplitude W 0 (line 1 y) *
        (((2*Real.pi)^4*(q*X / N^2) : ℝ) : ℂ) ^ (-line 1 y)) := by
    have he : -line (3/2) y = -(1/2 : ℂ) + -line 1 y := by dsimp [line]; push_cast; ring
    have hs : (2*Real.pi)^4*(q*X/N^2) = S*q := by dsimp [S,kernelScale]; ring
    rw [he, cpow_add _ _ (ofReal_ne_zero.mpr hq.ne'), cpow_neg (q : ℂ) (1/2), sqrt_cpow hq,
      hs, ofReal_mul, ofReal_mul_cpow hS.le]
    dsimp [F, leftIntegrand, S]
    ring
  change A m * (∫ y : ℝ, F y * (q : ℂ) ^ (-line (3/2) y)) / _ = _
  simp only [hterm, integral_const_mul, reflectionKernel]
  change _ = A m / Real.sqrt q * ((∫ y, reflectionKernelAmplitude W 0 (line 1 y) *
    (((2*Real.pi)^4*(q*X/N^2) : ℝ) : ℂ) ^ (-line 1 y)) / _)
  ring


private theorem angular_column_bound {τ : ℂ → ℂ} (ht : PattersonCoefficients τ) (barred : Bool)
    (z : ℂ) : ∃ B ≥ (0:ℝ), ∀ y : ℝ, ‖pattersonCuspDirichlet τ barred z (line (3/2) y)‖ ≤ B := by
  let g := fun m : Index => ‖pattersonAngularCoefficient τ barred z m‖ * mass m ^ (-(3/2:ℝ))
  have hg : Summable g := summable_angular ht barred z (by norm_num)
  refine ⟨∑' m, g m, tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (mass_pos
    m).le _)), ?_⟩
  intro y
  rw [dirichlet_eq_tsum]
  apply (norm_tsum_le_tsum_norm _).trans_eq
  · apply tsum_congr
    intro m
    simp only [norm_mul, line_norm_cpow (mass_pos m), g]
  · simpa only [norm_mul, line_norm_cpow (mass_pos _), g] using hg

private theorem smoothed_boundary_right (hB : DLMFBesselMellin) {τ : ℂ →
    ℂ} (ht : PattersonCoefficients τ)
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 2 W) (z : ℂ) {X : ℝ} (hX : 0 < X) :
    ∃ C ≥ (0:ℝ), ∀ y : ℝ, ‖smoothedIntegrand τ z W X (line (3/2) y)‖ * (1+|y|)^2 ≤ C := by
  obtain ⟨B, hB', hD⟩ := angular_column_bound ht true z
  obtain ⟨C, hC, hT⟩ := UnitTest.mellin_strip_decay J 2 (3/2) (3/2)
  let H := X ^ (3/2:ℝ) / Real.sqrt X
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨C*H*B, by positivity, ?_⟩
  intro y
  have h := hT W hW (line (3/2) y) (by simp [line])
  change _ * (1 + |(line (3/2) y).im|)^2 ≤ C at h
  simp only [line, add_im, ofReal_im, zero_add, mul_I_im, ofReal_re] at h
  rw [smoothedIntegrand, ht.continued_eq_dirichlet hB true z (by norm_num [line])]
  simp only [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hX, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg X), line, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero,
      add_zero]
  calc
    _ = (‖mellin W (line (3/2) y)‖ * (1+|y|)^2) * H * ‖pattersonCuspDirichlet τ true z (line (3/2)
      y)‖ := by
      dsimp only [H,line]; ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right h hH) (hD y) (norm_nonneg _) (mul_nonneg hC hH)

private theorem smoothed_boundary_left (hΓ : DLMFGammaVertical) {τ : ℂ →
    ℂ} (ht : PattersonCoefficients τ)
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 6 W) {z z' η : ℂ} {X N : ℝ}
    (hX : 0 < X) (hN : 0 < N)
    (hFE : ∀ s : ℂ, s.re < 0 → continuedPattersonDirichlet τ true z s =
      η * (N : ℂ) ^ (1-2*s) * (reflectionGammaFactor (1-s) / reflectionGammaFactor s) *
        pattersonCuspDirichlet τ false z' (1-s)) :
    ∃ C ≥ (0:ℝ), ∀ y : ℝ, ‖smoothedIntegrand τ z W X (line (-(1/2)) y)‖ * (1+|y|)^2 ≤ C := by
  obtain ⟨B, hB, hD⟩ := angular_column_bound ht false z'
  obtain ⟨C, hC, hF⟩ := leftIntegrand_bound hΓ hW hX hN
  refine ⟨‖η‖ * C * B, by positivity, ?_⟩
  intro y
  have h := smoothed_left_value hX hN W hFE (-y)
  rw [neg_neg] at h
  rw [h, norm_mul, norm_mul]
  calc
    _ = ‖η‖ * (‖leftIntegrand W X N (-y)‖ * (1+|-y|)^2) *
        ‖pattersonCuspDirichlet τ false z' (line (3/2) (-y))‖ := by rw [abs_neg]; ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hF _) (norm_nonneg _))
      (hD _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC)

private theorem smoothed_strip_growth (hΓ : DLMFGammaVertical) {τ : ℂ → ℂ}
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 0 W) {z : ℂ} {X : ℝ} (hX : 0 < X)
    (hc : ∃ M : ℝ, ∀ s : ℂ, s.re ∈ Icc (-(1/2:ℝ)) (3/2) → ‖completedPattersonCusp τ true z s‖ ≤ M) :
    ∃ C A : ℝ, ∀ s : ℂ, s.re ∈ Icc (-(1/2:ℝ)) (3/2) →
      ‖smoothedIntegrand τ z W X s‖ ≤ C * Real.exp (A*|s.im|) := by
  obtain ⟨M, hM⟩ := hc
  obtain ⟨G, A, hG, hΓ'⟩ := norm_inv_reflectionGammaFactor_strip hΓ
  obtain ⟨T, hT, hW'⟩ := UnitTest.mellin_strip_decay J 0 (-(1/2)) (3/2)
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-(1/2:ℝ)) (3/2))
    (Real.continuous_const_rpow hX.ne').continuousOn
  let L := max 0 P / Real.sqrt X
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨T * L * (‖(4:ℂ)/I‖ * max 0 M * G), A, ?_⟩
  intro s hs
  have hWb : ‖mellin W s‖ ≤ T := by simpa using hW' W hW s hs
  have hXb : X ^ s.re / Real.sqrt X ≤ L := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg X)
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hX.le _)] using (hP s.re
      hs).trans (le_max_right 0 P)
  rw [smoothedIntegrand, continuedPattersonDirichlet]
  simp only [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hX, norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg X)]
  calc
    _ = (‖mellin W s‖ * (X ^ s.re / Real.sqrt X)) *
        ((‖(4:ℂ)‖ / ‖I‖) * ‖completedPattersonCusp τ true z s‖ * ‖(reflectionGammaFactor s)⁻¹‖) :=
          by ring
    _ ≤ (T*L) * ((‖(4:ℂ)‖ / ‖I‖) * max 0 M * (G * Real.exp (A*|s.im|))) := by
      gcongr
      · exact (hM _ hs).trans (le_max_right ..)
      · exact hΓ' _ hs
    _ = _ := by ring

/-- Smoothed reflection at a congruence cusp. The original test is divided by
`√X`, and the dual test is evaluated at `Nμ X/(Nc)²` with coefficient `1/√(Nμ)`. -/
theorem PattersonExpansion.smoothed_reflection {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    {χ : 𝓔 → 𝓔 → ℂ} (hχ : PattersonAutomorphyWith χ θ) (hB : DLMFBesselMellin)
    (hΓ : DLMFGammaVertical) {a b c d : 𝓔} (hdet : a*d-b*c=1) (ha : eisPrimary a)
    (hb : (3:𝓔) ∣ b) (hc₃ : (3:𝓔) ∣ c) (hd : eisPrimary d) (hc : c ≠ 0)
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 6 W) {X : ℝ} (hX : 0 < X) :
    pattersonSmoothed τ (eisEmbedding a/eisEmbedding c) W X =
      pattersonCuspScalar (fun a c => conj (χ a c)) a c *
        ∑' m : {m : 𝓔 // m ≠ 0},
          pattersonAngularCoefficient τ false (-eisEmbedding d/eisEmbedding c) m /
              Real.sqrt (normSq (pattersonFrequency m)) *
            reflectionKernel W 0 0 (normSq (pattersonFrequency m)*X/(‖eisEmbedding c‖^2)^2) := by
  let z := eisEmbedding a / eisEmbedding c
  let z' := -eisEmbedding d / eisEmbedding c
  let N := ‖eisEmbedding c‖^2
  let η := pattersonCuspScalar (fun a c => conj (χ a c)) a c
  have hc' := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  have hN : 0 < N := by dsimp [N]; positivity
  have hFE (s : ℂ) (hs : s.re < 0) := he.continued_eq_dual ht hχ hB hdet ha hb hc₃ hd hc hs
  let F := smoothedIntegrand τ z W X
  have hdF : Differentiable ℂ F := by
    have hpow := differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hX.ne'))
    have hdL := he.continued_entire ht hχ hdet ha hb hc₃ hd hc
    exact ((hW.mellin_entire.mul hpow).div_const _).mul hdL
  have h₀ := hW.of_le (by decide : 0 ≤ 6)
  have h₂ := hW.of_le (by decide : 2 ≤ 6)
  have hstrip := he.norm_completed_on_strip ht hχ hdet ha hb hc₃ hd hc (-(1/2)) (3/2)
  have hshift := integral_vertical_eq_of_exp_growth (F := F) (by norm_num : -(1/2:ℝ) < 3/2) hdF
    (smoothed_strip_growth hΓ h₀ hX hstrip) (smoothed_boundary_left hΓ ht hW hX hN hFE)
    (smoothed_boundary_right hB ht h₂ z hX)
  exact (smoothed_right_integral hB ht h₂ z hX).trans
    ((congrArg (· / (2*Real.pi : ℂ)) hshift.symm).trans (smoothed_left_integral hΓ ht hW hX hN hFE))


/-- The frequency sum in the smoothed dual formula is absolutely convergent. -/
theorem PattersonCoefficients.summable_smoothed_dual {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (hΓ : DLMFGammaVertical) {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 6 W)
    (z : ℂ) {X N : ℝ} (hX : 0 < X) (hN : 0 < N) :
    Summable fun m : {m : 𝓔 // m ≠ 0} =>
      ‖pattersonAngularCoefficient τ false z m / Real.sqrt (normSq (pattersonFrequency m)) *
        reflectionKernel W 0 0 (normSq (pattersonFrequency m)*X/N^2)‖ := by
  have htest : UnitTest J (0 + ⌈4*max (1:ℝ) 0⌉₊ + 2) W := by norm_num; exact hW
  obtain ⟨C, hC, hK⟩ := norm_reflectionKernel hΓ (σ := 1) (by norm_num) 0 J
  let T := X / N^2
  have hT : 0 < T := div_pos hX (pow_pos hN _)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((summable_angular ht false z (by
    norm_num : 1 < (3/2:ℝ))).mul_right (C / T))
  intro m
  let q := mass m
  have hq : 0 < q := mass_pos m
  have hs : normSq (pattersonFrequency m)*X/N^2 = q*T := by dsimp only [q,mass,T]; ring
  rw [hs, reflectionKernel_shift hΓ (a := 0) (b := 1) (by norm_num) (by norm_num) 0 htest (mul_pos
    hq hT)]
  rw [norm_mul, norm_div, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left (hK W htest _ (mul_pos hq hT)) (by positivity)).trans_eq
  change ‖pattersonAngularCoefficient τ false z m‖ / Real.sqrt q * (C * (q*T)^(-(1:ℝ))) =
    (‖pattersonAngularCoefficient τ false z m‖ * q^(-(3/2:ℝ))) * (C/T)
  rw [Real.rpow_neg (mul_pos hq hT).le, Real.rpow_one, Real.sqrt_eq_rpow,
    show -(3/2:ℝ) = -(1/2)-1 by norm_num, Real.rpow_sub_one hq.ne', Real.rpow_neg hq.le]
  ring

end Masullo.QRH.MeanSquare
