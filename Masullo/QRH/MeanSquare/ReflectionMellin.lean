import Masullo.QRH.MeanSquare.SpecialFunctions
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Mellin normalization and inversion at a reflected cusp -/

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

/-- Archimedean factor of the horizontally differentiated Patterson series. -/
def reflectionGammaFactor (s : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * s) * Gamma (s + 1 / 3) * Gamma (s + 2 / 3)

private lemma bessel_scale_factor (s : ℂ) {r : ℝ} (hr : 0 < r) :
    ((2 * Real.pi : ℝ) : ℂ) * ((4 * Real.pi * r : ℝ) : ℂ) ^ (-(2*s + 1)) * (2 : ℂ) ^ (2*s - 1) =
      1 / 4 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * s) * (r : ℂ) ^ (-2 * s) / r := by
  let p := 2 * Real.pi
  have hp : 0 < p := by dsimp [p]; positivity
  have hs (t : ℂ) : ((4 * Real.pi * r : ℝ) : ℂ) ^ t =
      (2 : ℂ) ^ t * (p : ℂ) ^ t * (r : ℂ) ^ t := by
    rw [show 4 * Real.pi * r = (2 : ℝ) * (p * r) by dsimp [p]; ring,
      ofReal_mul, ofReal_mul_cpow (by norm_num : (0 : ℝ) ≤ 2), ofReal_mul, ofReal_mul_cpow hp.le]
    push_cast
    ring
  have ht : (2 : ℂ) ^ (-(2*s + 1)) * 2 ^ (2*s - 1) = 1/4 := by
    rw [← cpow_add _ _ (by norm_num), show -(2*s+1) + (2*s-1) = -(2 : ℂ) by ring, cpow_neg]
    norm_num
  have hx (a : ℝ) (ha : 0 < a) : (a : ℂ) ^ (-(2*s+1)) = (a : ℂ) ^ (-2*s) / a := by
    rw [show -(2*s+1) = -2*s - 1 by ring, cpow_sub _ _ (ofReal_ne_zero.mpr ha.ne'), cpow_one]
  rw [hs]
  change (p : ℂ) * _ * _ = 1/4 * (p : ℂ) ^ (-2*s) * _ / _
  calc
    _ = (2 : ℂ) ^ (-(2*s+1)) * 2 ^ (2*s-1) * (p * (p : ℂ) ^ (-(2*s+1))) *
          (r : ℂ) ^ (-(2*s+1)) := by ring
    _ = _ := by
      rw [ht, hx p hp, hx r hr, mul_div_cancel₀ _ (ofReal_ne_zero.mpr hp.ne')]
      ring

/-- The Mellin transform of one nonzero horizontal mode, including its angular factor.
The constant `a` can include both the Fourier coefficient and its translation phase. -/
theorem hasMellin_horizontalMode (h : DLMFBesselMellin) {s : ℂ} (hs : -(1 / 3 : ℝ) < s.re)
    {l : ℂ} (hl : l ≠ 0) (a : ℂ) :
    HasMellin (fun v : ℝ => (2 * (Real.pi : ℂ) * I * conj l * a) *
      (v * besselK (1/3) (4 * Real.pi * ‖l‖ * v))) (2 * s)
      (I / 4 * reflectionGammaFactor s * a * (conj l / ‖l‖) * (normSq l : ℂ) ^ (-s)) := by
  have hr := norm_pos_iff.mpr hl
  have hb := besselMellin_oneThird_scaled h hs (show 0 < 4 * Real.pi * ‖l‖ by positivity)
  let f := fun v : ℝ => besselK (1/3) (4 * Real.pi * ‖l‖ * v)
  have hc : MellinConvergent (fun v : ℝ => (v : ℂ) ^ (1 : ℂ) • f v) (2*s) :=
    MellinConvergent.cpow_smul.mpr hb.1
  have hh := hasMellin_const_smul hc (2 * (Real.pi : ℂ) * I * conj l * a)
  rw [mellin_cpow_smul, show mellin f (2*s+1) = _ from hb.2] at hh
  simp only [cpow_one, smul_eq_mul] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hnorm : (normSq l : ℂ) ^ (-s) = (‖l‖ : ℂ) ^ (-2*s) := by
    rw [normSq_eq_norm_sq, sq, ofReal_mul, ofReal_mul_cpow hr.le, ← cpow_add _ _ (ofReal_ne_zero.mpr
      hr.ne')]
    congr 1
    ring
  rw [hnorm, reflectionGammaFactor]
  have ht := bessel_scale_factor s hr
  push_cast at ht
  push_cast
  linear_combination I * conj l * a * Gamma (s + 1/3) * Gamma (s + 2/3) * ht

/-- The change of height `v ↦ 1/(N v)` in the Mellin integral interchanges `s` and
`1-s`. The scalar `η` includes the angular part of the horizontal Jacobian. -/
theorem mellin_cusp_reflection (f g : ℝ → ℂ) {N : ℝ} (hN : 0 < N) (η s : ℂ)
    (hfg : ∀ v : ℝ, 0 < v → f v = η / (N * (v : ℂ) ^ 2) * g ((N*v)⁻¹)) :
    mellin f (2*s) = η * (N : ℂ) ^ (1 - 2*s) * mellin g (2*(1-s)) := by
  let G := fun v : ℝ => g v⁻¹
  have he : mellin f (2*s) =
      mellin (fun v : ℝ => (η / N) • ((v : ℂ) ^ (-2 : ℂ) • G (N*v))) (2*s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [hfg v hv]
    simp only [G, smul_eq_mul, cpow_neg, cpow_ofNat]
    ring
  rw [he, mellin_const_smul, mellin_cpow_smul, mellin_comp_mul_left _ _ hN]
  dsimp only [G]
  rw [mellin_comp_inv]
  rw [show -(2*s+-2) = 2*(1-s) by ring]
  have hn : (N : ℂ) ^ (2*(1-s)) = (N : ℂ) ^ (1-2*s) * N := by
    rw [show 2*(1-s) = (1-2*s) + 1 by ring, cpow_add _ _ (ofReal_ne_zero.mpr hN.ne'), cpow_one]
  simp only [smul_eq_mul, hn]
  field_simp [ofReal_ne_zero.mpr hN.ne']



open Filter Asymptotics
open scoped Topology

/-- Exponential decay in the height and in its reciprocal makes the Mellin transform
entire and its defining integral convergent at every complex parameter. -/
theorem mellin_of_exponential_cusp_decay {f : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf : LocallyIntegrableOn f (Ioi 0))
    (htop : f =O[atTop] fun v : ℝ => Real.exp (-a*v))
    (h₀ : f =O[𝓝[>] 0] fun v : ℝ => Real.exp (-b / v)) :
    (∀ s : ℂ, MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  have hpow (c : ℝ) : f =O[𝓝[>] 0] fun v : ℝ => v ^ (-c) := by
    apply h₀.trans
    refine ((isLittleO_exp_neg_mul_rpow_atTop hb c).isBigO.comp_tendsto
      tendsto_inv_nhdsGT_zero).congr' (.of_forall fun v => ?_)
        (eventually_mem_nhdsWithin.mono fun v hv => ?_)
    · simp [div_eq_mul_inv]
    · simp [Function.comp_apply, Real.inv_rpow hv.out.le, Real.rpow_neg hv.out.le]
  exact ⟨fun s => mellinConvergent_of_isBigO_rpow_exp ha hf htop (hpow (s.re - 1)) (by linarith),
    fun s => mellin_differentiableAt_of_isBigO_rpow_exp ha hf htop (hpow (s.re - 1)) (by linarith)⟩

/-- Absolute convergence at the two real endpoints uniformly bounds the Mellin
integral throughout the intervening closed strip. -/
theorem norm_mellin_le_on_strip {f : ℝ → ℂ} {a b : ℝ}
    (ha : MellinConvergent f a) (hb : MellinConvergent f b) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → ‖mellin f s‖ ≤ C := by
  let F := fun (s : ℂ) (v : ℝ) => (v : ℂ) ^ (s - 1) • f v
  let M := fun v : ℝ => ‖F a v‖ + ‖F b v‖
  have hM : IntegrableOn M (Ioi 0) := Integrable.add ha.norm hb.norm
  refine ⟨∫ v in Ioi 0, M v, fun s hs => norm_integral_le_of_norm_le hM ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : 0 < v)
  dsimp only [M, F]
  simp only [norm_smul, norm_cpow_eq_rpow_re_of_pos hv, sub_re, one_re, ofReal_re]
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rcases le_total v 1 with hv₁ | hv₁
  · exact (Real.rpow_le_rpow_of_exponent_ge hv hv₁ (by linarith [hs.1])).trans
      (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le hv₁ (by linarith [hs.2])).trans
      (le_add_of_nonneg_left (by positivity))

/-- The quotient of gamma factors in the separated kernel on the contour `Re t = x`. -/
def reflectionGammaRatio (t : ℂ) : ℂ :=
  Gamma (5/6 + t) * Gamma (7/6 + t) / (Gamma (5/6 - t) * Gamma (7/6 - t))

/-- Uniform vertical estimate for the gamma quotient on every bounded strip. -/
theorem norm_reflectionGammaRatio_le (h : DLMFGammaVertical) (B : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ x y : ℝ, |x| ≤ B → T ≤ |y| →
      ‖reflectionGammaRatio (x + y * I)‖ ≤ 9 * |y| ^ (4*x) := by
  obtain ⟨T, hT⟩ := h (B + 2) (1 / 2) (by norm_num)
  refine ⟨max 1 T, le_max_left .., ?_⟩
  intro x y hx hy
  have hy₁ := (le_max_left 1 T).trans hy
  have hy₀ : 0 < |y| := by linarith
  have hyT := (le_max_right 1 T).trans hy
  let M := fun a : ℝ => Real.sqrt (2 * Real.pi) * |y| ^ (a - 1 / 2) *
    Real.exp (-Real.pi * |y| / 2)
  have hM (a : ℝ) : 0 < M a := by dsimp [M]; positivity
  have hupper (a : ℝ) (ha : |a| ≤ B + 2) : ‖Gamma (a + y * I)‖ ≤ 3 / 2 * M a := by
    have hat := (abs_lt.mp (hT a y ha hyT)).2
    change ‖Gamma (a + y * I)‖ / M a - 1 < 1 / 2 at hat
    have hu : ‖Gamma (a + y * I)‖ / M a ≤ 3 / 2 := by linarith
    exact (div_le_iff₀ (hM a)).mp hu
  have hlower (b : ℝ) (hb : |b| ≤ B + 2) : 1 / 2 * M b ≤ ‖Gamma (b - y * I)‖ := by
    have hbt := (abs_lt.mp (hT b (-y) hb (by simpa using hyT))).1
    rw [abs_neg, ofReal_neg, neg_mul, ← sub_eq_add_neg] at hbt
    change -(1/2 : ℝ) < ‖Gamma (b - y * I)‖ / M b - 1 at hbt
    have hl : 1/2 ≤ ‖Gamma (b - y * I)‖ / M b := by linarith
    exact (le_div_iff₀ (hM b)).mp hl
  have hshift (c : ℝ) (hc : |c| ≤ 2) :
      ‖Gamma ((c : ℂ) + (x + y*I))‖ ≤
        (3 * |y| ^ (2*x)) * ‖Gamma ((c : ℂ) - (x + y*I))‖ := by
    have hp : |c+x| ≤ B+2 := (abs_add_le ..).trans (by linarith)
    have hm : |c-x| ≤ B+2 := by
      rw [sub_eq_add_neg]
      exact (abs_add_le ..).trans (by rw [abs_neg]; linarith)
    have hu := hupper (c+x) hp
    have hl := hlower (c-x) hm
    rw [ofReal_add] at hu
    rw [ofReal_sub] at hl
    rw [← add_assoc]
    rw [show (c : ℂ) - (x + y*I) = c - x - y*I by ring]
    have he : |y| ^ (2*x) * M (c-x) = M (c+x) := by
      dsimp [M]
      rw [show c+x-1/2 = 2*x + (c-x-1/2) by ring, Real.rpow_add hy₀]
      ring
    calc
      _ ≤ 3 / 2 * M (c+x) := hu
      _ = (3 * |y| ^ (2*x)) * (1/2 * M (c-x)) := by rw [← he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have h₅ := hshift (5/6) (by norm_num)
  have h₇ := hshift (7/6) (by norm_num)
  push_cast at h₅ h₇
  have hprod := mul_le_mul h₅ h₇ (norm_nonneg _) (by positivity)
  rw [reflectionGammaRatio, norm_div, norm_mul, norm_mul]
  apply div_le_of_le_mul₀ (by positivity) (by positivity)
  calc
    _ ≤ _ := hprod
    _ = _ := by
      rw [show 4*x = 2*x + 2*x by ring, Real.rpow_add hy₀]
      ring


/-- The numerator has no poles in the half-plane needed for the contour shift.
Reciprocal gamma is entire, including at the poles of the denominator. -/
theorem differentiableAt_reflectionGammaRatio {t : ℂ} (ht : -(5/6 : ℝ) < t.re) :
    DifferentiableAt ℂ reflectionGammaRatio t := by
  have hd (c : ℝ) (hc : 5/6 ≤ c) :
      DifferentiableAt ℂ (fun z : ℂ => Gamma ((c : ℂ) + z)) t := by
    apply (differentiableAt_Gamma _ ?_).comp t (by fun_prop)
    intro m hm
    have he := congrArg re hm
    simp only [add_re, ofReal_re, neg_re, natCast_re] at he
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hi (c : ℂ) : DifferentiableAt ℂ (fun z : ℂ => (Gamma (c-z))⁻¹) t :=
    differentiable_one_div_Gamma.differentiableAt.comp t (by fun_prop)
  have h₅ := hd (5/6) (by norm_num)
  have h₇ := hd (7/6) (by norm_num)
  push_cast at h₅ h₇
  convert (h₅.mul h₇).mul ((hi (7/6)).mul (hi (5/6))) using 1
  ext z
  simp only [reflectionGammaRatio, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]

/-- Polynomial growth throughout each closed substrip of `Re t > -5/6`. -/
theorem norm_reflectionGammaRatio_on_strip (h : DLMFGammaVertical) {a b : ℝ}
    (ha : -(5/6 : ℝ) < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℂ, t.re ∈ Icc a b →
      ‖reflectionGammaRatio t‖ ≤ C * (1 + |t.im|) ^ (4 * max b 0) := by
  obtain ⟨T, hT, hfar⟩ := norm_reflectionGammaRatio_le h (max |a| |b|)
  let R := reProdIm (Icc a b) (Icc (-T) T)
  have hR : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hR.exists_bound_of_continuousOn (f := reflectionGammaRatio)
    (fun t ht => (differentiableAt_reflectionGammaRatio
      (ha.trans_le ((mem_reProdIm.mp ht).1.1))).continuousAt.continuousWithinAt)
  refine ⟨max 9 C, (by positivity : (0 : ℝ) < 9).trans_le (le_max_left ..), ?_⟩
  intro t ht
  have he : 0 ≤ 4 * max b 0 := by positivity
  have hy : 1 ≤ 1 + |t.im| := by have := abs_nonneg t.im; linarith
  by_cases hf : T ≤ |t.im|
  · have hx : |t.re| ≤ max |a| |b| := by
      rw [abs_le]
      constructor
      · linarith [le_max_left |a| |b|, neg_abs_le a, ht.1]
      · linarith [le_max_right |a| |b|, le_abs_self b, ht.2]
    have hh := hfar _ _ hx hf
    rw [re_add_im] at hh
    calc
      _ ≤ 9 * |t.im| ^ (4 * t.re) := hh
      _ ≤ 9 * |t.im| ^ (4 * max b 0) := by
        gcongr
        · exact hT.trans hf
        · exact ht.2.trans (le_max_left ..)
      _ ≤ _ := by
        gcongr
        · exact le_max_left ..
        · linarith
  · have htR : t ∈ R := ⟨ht, abs_le.mp (le_of_not_ge hf)⟩
    exact (hC _ htR).trans ((le_max_right 9 C).trans
      (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hy he)))

end Masullo.QRH.MeanSquare
