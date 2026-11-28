import Masullo.QRH.MeanSquare.ReflectionTest
import WeilExplicit.RectangleLimit

/-! # Contour shifts for the gamma quotient in the reflected weight -/

noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology

namespace Masullo.QRH.MeanSquare

/-- The `j`th logarithmic derivative contributes `(-t)^j`. The shift by
one half incorporates the square root in the original radial test. -/
def reflectionKernelAmplitude (W : ℝ → ℂ) (j : ℕ) (t : ℂ) : ℂ :=
  (-t) ^ j * mellin W (1/2 - t) * reflectionGammaRatio t

theorem differentiableAt_reflectionKernelAmplitude {I : TestInterval} {m : ℕ} {W : ℝ → ℂ}
    (hW : UnitTest I m W) (j : ℕ) {t : ℂ} (ht : -(5/6 : ℝ) < t.re) :
    DifferentiableAt ℂ (reflectionKernelAmplitude W j) t := by
  exact ((differentiableAt_id.neg.pow _).mul ((hW.mellin_entire _).comp t
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1/2-z) t))).mul
      (differentiableAt_reflectionGammaRatio ht)

/-- The derivative order needed to integrate all the way across the strip
is uniform in the test interval. -/
theorem norm_reflectionKernelAmplitude (hΓ : DLMFGammaVertical) {a b : ℝ}
    (ha : -(5/6 : ℝ) < a) (j : ℕ) (I : TestInterval) :
    let m := j + ⌈4 * max b 0⌉₊ + 2
    ∃ C ≥ (0 : ℝ), ∀ W, UnitTest I m W → ∀ t : ℂ, t.re ∈ Icc a b →
      ‖reflectionKernelAmplitude W j t‖ * (1 + |t.im|) ^ 2 ≤ C := by
  let n := ⌈4 * max b 0⌉₊
  obtain ⟨A,hA,hW⟩ := UnitTest.mellin_strip_decay I (j+n+2) (1/2-b) (1/2-a)
  obtain ⟨B,hB,hR⟩ := norm_reflectionGammaRatio_on_strip hΓ (b := b) ha
  let R := 1 + max |a| |b|
  have hR₀ : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨R ^ j * B * A, by positivity, fun W hw t ht => ?_⟩
  let T := 1 + |t.im|
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t.im]
  have hT₀ := zero_le_one.trans hT
  have hw' := hW W hw (1/2 - t) (by
    norm_num [sub_re] at *
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hi : ((1/2 : ℂ) - t).im = -t.im := by norm_num [sub_im]
  rw [hi, abs_neg] at hw'
  have hpow : (1 + |t.im|) ^ (4 * max b 0) ≤ T ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT (Nat.le_ceil _)
  have hγ := (hR t ht).trans (mul_le_mul_of_nonneg_left hpow hB.le)
  have hre : |t.re| ≤ max |a| |b| := by
    rw [abs_le]
    exact ⟨by linarith [ht.1, le_max_left |a| |b|, neg_abs_le a],
      by linarith [ht.2, le_max_right |a| |b|, le_abs_self b]⟩
  have hnorm : ‖t‖ ≤ R * T := by
    apply (norm_le_abs_re_add_abs_im t).trans
    dsimp [R,T]
    nlinarith [mul_nonneg ((abs_nonneg a).trans (le_max_left |a| |b|)) (abs_nonneg t.im)]
  simp only [reflectionKernelAmplitude, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ ((R*T)^j * ‖mellin W (1/2-t)‖ * (B*T^n)) * T^2 := by
      gcongr
    _ = R^j * B * (‖mellin W (1/2-t)‖ * T^(j+n+2)) := by simp only [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw' (by positivity)

/-- Moving a vertical integral across a holomorphic strip with a uniform
integrable majorant. -/
theorem integral_vertical_eq_of_strip {F : ℂ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hC : 0 ≤ C) (hd : ∀ t : ℂ, t.re ∈ Icc a b → DifferentiableAt ℂ F t)
    (h : ∀ t : ℂ, t.re ∈ Icc a b → ‖F t‖ ≤ C / (1 + t.im^2)) :
    (∫ y : ℝ, F (a + y*Complex.I)) = ∫ y : ℝ, F (b + y*Complex.I) := by
  have hi (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun y : ℝ => F (x + y*Complex.I)) := by
    have hc : Continuous (fun y : ℝ => F (x + y*Complex.I)) := continuous_iff_continuousAt.mpr
      fun y => (hd _ (by simpa using hx)).continuousAt.comp (by fun_prop)
    apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
    exact ae_of_all _ fun y =>
      by simpa [div_eq_mul_inv] using h (x + y*Complex.I) (by simpa using hx)
  have H := WeilExplicit.rectIntegral_tendsto (f := F) tendsto_natCast_atTop_atTop
    (hi a ⟨le_rfl,hab⟩) (hi b ⟨hab,le_rfl⟩) (B := C) (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      intro t ht hy
      rw [uIcc_of_le hab] at ht
      apply (h t ht).trans
      apply div_le_div_of_nonneg_left hC (by exact_mod_cast (by omega : 0 < n))
      rw [← sq_abs t.im, hy]
      nlinarith [sq_nonneg ((n:ℝ)-1)])
  have hz (n : ℕ) : WeilExplicit.rectIntegral F a b (-(n:ℝ)) n = 0 := by
    apply WeilExplicit.rectIntegral_eq_zero
    exact fun t ht => (hd t ((uIcc_of_le hab) ▸ ht.1)).differentiableWithinAt
  simp_rw [hz] at H
  have hlim := tendsto_nhds_unique H tendsto_const_nhds
  have he : (∫ y : ℝ, F (b + y*Complex.I)) = ∫ y : ℝ, F (a + y*Complex.I) := by
    simpa [sub_eq_zero, Complex.I_ne_zero] using hlim
  exact he.symm

/-- Reflected radial weight on a vertical line. Its argument includes the
frequency scale; the positive factor `(2π)^4` belongs to the Mellin quotient. -/
def reflectionKernel (W : ℝ → ℂ) (j : ℕ) (σ x : ℝ) : ℂ :=
  (∫ y : ℝ, let t : ℂ := σ + y*Complex.I
    reflectionKernelAmplitude W j t * (((2 * Real.pi)^4 * x : ℝ) : ℂ) ^ (-t)) / (2 * Real.pi)

/-- A contour can move inside the half-plane above the first gamma pole. -/
theorem reflectionKernel_shift (hΓ : DLMFGammaVertical) {a b : ℝ} (hab : a ≤ b)
    (ha : -(5/6 : ℝ) < a) (j : ℕ) {I : TestInterval} {W : ℝ → ℂ}
    (hW : UnitTest I (j + ⌈4 * max b 0⌉₊ + 2) W) {x : ℝ} (hx : 0 < x) :
    reflectionKernel W j a x = reflectionKernel W j b x := by
  let X := (2 * Real.pi)^4 * x
  have hX : 0 < X := by dsimp [X]; positivity
  obtain ⟨C,hC,hA⟩ := norm_reflectionKernelAmplitude hΓ ha (b := b) j I
  have hcont : Continuous (fun t : ℝ => X ^ (-t)) :=
    (Real.continuous_const_rpow hX.ne').comp continuous_neg
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hcont.continuousOn
  let F := fun t : ℂ => reflectionKernelAmplitude W j t * (X : ℂ) ^ (-t)
  have hf := integral_vertical_eq_of_strip (F := F) hab (mul_nonneg hC (le_max_right M 0))
    (fun t ht => (differentiableAt_reflectionKernelAmplitude hW j (ha.trans_le ht.1)).mul
      (differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hX.ne')))) (by
    intro t ht
    have hm := hM t.re ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hX.le _)] at hm
    rw [le_div_iff₀ (by positivity)]
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, neg_re]
    have hn := hA W hW t ht
    calc
      _ = X ^ (-t.re) * (‖reflectionKernelAmplitude W j t‖ * (1 + t.im ^ 2)) := by ring
      _ ≤ max M 0 * (‖reflectionKernelAmplitude W j t‖ * (1 + |t.im|)^2) := by
        gcongr
        · exact hm.trans (le_max_left ..)
        · nlinarith [sq_abs t.im, abs_nonneg t.im]
      _ ≤ _ := by rw [mul_comm C]; gcongr)
  exact congrArg (fun q : ℂ => q / (2 * Real.pi)) hf

/-- On its own line the reflected weight is bounded by `x^(-σ)`, uniformly
over the derivative unit ball and over all positive scales. -/
theorem norm_reflectionKernel (hΓ : DLMFGammaVertical) {σ : ℝ} (hσ : -(5/6 : ℝ) < σ)
    (j : ℕ) (I : TestInterval) :
    ∃ C ≥ (0 : ℝ), ∀ W, UnitTest I (j + ⌈4 * max σ 0⌉₊ + 2) W → ∀ x : ℝ, 0 < x →
      ‖reflectionKernel W j σ x‖ ≤ C * x ^ (-σ) := by
  obtain ⟨B,hB,hA⟩ := norm_reflectionKernelAmplitude hΓ (b := σ) hσ j I
  let H (y : ℝ) := (1 + y^2)⁻¹
  have hH : 0 ≤ ∫ y, H y := integral_nonneg (fun y => by dsimp [H]; positivity)
  let S : ℝ := (2*Real.pi)^4
  have hS : 0 < S := by dsimp [S]; positivity
  refine ⟨(B * S ^ (-σ) * (∫ y, H y)) / (2 * Real.pi), by positivity, fun W hw x hx => ?_⟩
  let C := B * (S*x) ^ (-σ)
  have hC : 0 ≤ C := mul_nonneg hB (Real.rpow_nonneg (mul_pos hS hx).le _)
  let F (y : ℝ) := reflectionKernelAmplitude W j (σ + y*Complex.I) *
    ((S*x : ℝ) : ℂ) ^ (-(σ+y*Complex.I))
  have hbound (y : ℝ) : ‖F y‖ ≤ C * H y := by
    have hm := hA W hw (σ + y*Complex.I) (by simp)
    simp only [add_im, ofReal_im, zero_add, mul_I_im, ofReal_re] at hm
    dsimp only [F, C, H]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (mul_pos hS hx), neg_re]
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
    calc
      _ ≤ (B / (1+y^2)) * (S*x)^(-σ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (mul_pos hS hx).le _)
        apply (le_div_iff₀ (by positivity)).mpr
        exact (mul_le_mul_of_nonneg_left (by nlinarith [sq_abs y, abs_nonneg y])
          (norm_nonneg (reflectionKernelAmplitude W j (σ+y*Complex.I)))).trans hm
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul C) (ae_of_all _
    hbound)
  change ‖∫ y, F y‖ ≤ _ at hh
  rw [integral_const_mul] at hh
  change ‖(∫ y, F y) / (2 * (Real.pi : ℂ))‖ ≤ _
  rw [norm_div, norm_mul, norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  refine (div_le_div_of_nonneg_right hh (by positivity)).trans_eq ?_
  dsimp only [C, H]
  rw [Real.mul_rpow hS.le hx.le]
  ring

/-- The contour moments are the actual derivatives in the logarithm of the
positive argument. On the central line the oscillatory factor has modulus one. -/
theorem hasDerivAt_reflectionKernel_log (hΓ : DLMFGammaVertical) {I : TestInterval}
    {W : ℝ → ℂ} (j : ℕ) (hw : UnitTest I (j+3) W) (u : ℝ) :
    HasDerivAt (fun t : ℝ => reflectionKernel W j 0 (Real.exp t))
      (reflectionKernel W (j+1) 0 (Real.exp u)) u := by
  let S := (2 * Real.pi)^4
  have hS : (0 : ℝ) < S := by dsimp [S]; positivity
  let t (y : ℝ) := (y : ℂ)*Complex.I
  let F (k : ℕ) (v y : ℝ) := reflectionKernelAmplitude W k (t y) *
    Complex.exp ((Real.log S + (v : ℂ)) * (-t y))
  have hrepr (k : ℕ) (v : ℝ) :
      reflectionKernel W k 0 (Real.exp v) = (∫ y : ℝ, F k v y) / (2 * Real.pi) := by
    unfold reflectionKernel
    apply congrArg (fun q : ℂ => q / (2 * Real.pi))
    apply integral_congr_ae (ae_of_all _ fun y => ?_)
    change reflectionKernelAmplitude W k ((0 : ℂ) + t y) * ((S * Real.exp v : ℝ) : ℂ) ^ (-((0 : ℂ) +
      t y)) = F k v y
    rw [zero_add]
    unfold F
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hS (Real.exp_pos v)).ne'),
      ← Complex.ofReal_log (mul_pos hS (Real.exp_pos v)).le, Real.log_mul hS.ne' (Real.exp_pos
        v).ne',
      Real.log_exp, ofReal_add]
  have hdiff (k : ℕ) (v y : ℝ) : HasDerivAt (fun x => F k x y) (F (k+1) v y) v := by
    have H := ((((Complex.ofRealCLM.hasDerivAt (x := v)).const_add (↑(Real.log S) : ℂ)).mul_const
      (-t y)).cexp).const_mul (reflectionKernelAmplitude W k (t y))
    convert H using 1
    · rfl
    · dsimp [F, reflectionKernelAmplitude]
      ring
  have hmeas (k : ℕ) (v : ℝ) : AEStronglyMeasurable (F k v) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact continuous_iff_continuousAt.mpr (fun y =>
        (differentiableAt_reflectionKernelAmplitude hw k
          (t := t y) (by simp [t])).continuousAt.comp (by dsimp [t]; fun_prop))
    · dsimp [t]
      fun_prop
  have hmajor (k : ℕ) (hk : k ≤ j+1) :
      ∃ B ≥ (0 : ℝ), ∀ v y, ‖F k v y‖ ≤ B * (1 + y^2)⁻¹ := by
    obtain ⟨B,hB,hA⟩ := norm_reflectionKernelAmplitude hΓ (a := 0) (b := 0) (by norm_num) k I
    refine ⟨B,hB,fun v y => ?_⟩
    have hk' : k + ⌈4 * max (0 : ℝ) 0⌉₊ + 2 ≤ j+3 := by norm_num; omega
    have hm := hA W (hw.of_le hk') (t y) (by simp [t])
    simp only [t, mul_I_im, ofReal_re] at hm
    dsimp [F,t]
    rw [Complex.norm_mul, Complex.norm_exp]
    have he : ((↑(Real.log S) + (v : ℂ)) * (-(y * Complex.I))).re = 0 := by simp [mul_re]
    rw [he, Real.exp_zero, mul_one]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_left (show 1+y^2 ≤ (1+|y|)^2 by
      nlinarith [sq_abs y, abs_nonneg y]) (norm_nonneg _)).trans hm
  obtain ⟨B,_,h₀⟩ := hmajor j (by omega)
  obtain ⟨C,_,h₁⟩ := hmajor (j+1) le_rfl
  have hi := (integrable_inv_one_add_sq.const_mul B).mono' (hmeas j u) (ae_of_all _ (h₀ u))
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F j) (F' := F (j+1))
    (s := univ) (univ_mem) (.of_forall (hmeas j)) hi (hmeas (j+1) u)
    (ae_of_all _ fun y v _ => h₁ v y) (integrable_inv_one_add_sq.const_mul C)
    (ae_of_all _ fun y v _ => hdiff j v y)
  simp only [hrepr]
  exact H.2.div_const _

/-- Each fixed number of logarithmic derivatives has simultaneous small-
and large-argument bounds with a test derivative order independent of the interval. -/
theorem reflectionKernel_log_decay (hΓ : DLMFGammaVertical) (j : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ m : ℕ, ∀ I : TestInterval, ∃ C ≥ (0 : ℝ), ∀ W, UnitTest I m W → ∀ u : ℝ,
      ‖iteratedDeriv j (fun v : ℝ => reflectionKernel W 0 0 (Real.exp v)) u‖ ≤
        C * min ((Real.exp u) ^ (1/4 : ℝ)) ((Real.exp u) ^ (-A)) := by
  let n := ⌈4 * max A 0⌉₊
  refine ⟨j+n+3, fun I => ?_⟩
  obtain ⟨B,hB,hsmall⟩ := norm_reflectionKernel hΓ (σ := -(1/4)) (by norm_num) j I
  obtain ⟨D,hD,hlarge⟩ := norm_reflectionKernel hΓ (σ := A) (by linarith) j I
  refine ⟨max B D, hB.trans (le_max_left ..), fun W hw u => ?_⟩
  have hm (k : ℕ) (hk : k ≤ j) : iteratedDeriv k (fun v : ℝ => reflectionKernel W 0 0 (Real.exp
    v)) =
      fun v => reflectionKernel W k 0 (Real.exp v) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      exact funext fun v => (hasDerivAt_reflectionKernel_log hΓ k (hw.of_le (by omega)) v).deriv
  rw [hm j le_rfl, mul_min_of_nonneg _ _ (hB.trans (le_max_left B D)), le_min_iff]
  have hs : UnitTest I (j+2) W := hw.of_le (by omega)
  have hl : UnitTest I (j + n + 2) W := hw.of_le (by omega)
  have hshift := reflectionKernel_shift hΓ (a := -(1/4)) (b := 0) (by norm_num)
    (by norm_num) j (by simpa using hs) (Real.exp_pos u)
  have hshift' := reflectionKernel_shift hΓ hA (by norm_num) j hl (Real.exp_pos u)
  dsimp only
  constructor
  · rw [← hshift]
    apply le_trans (hsmall _ (by norm_num at *; exact hs) _ (Real.exp_pos u))
    simp only [neg_neg]
    gcongr
    exact le_max_left ..
  · rw [hshift']
    apply (hlarge _ hl _ (Real.exp_pos u)).trans
    gcongr
    exact le_max_right ..

end Masullo.QRH.MeanSquare
