import Masullo.QRH.MeanSquare.ReflectionKernel
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # Growth and contour shifting for the uncompleted Patterson series -/

noncomputable section

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

namespace Masullo.QRH.MeanSquare

/-- Exponential growth on a strip suffices for a contour shift if both boundary
integrands decay quadratically. Apply Phragmén–Lindelöf after multiplication
by a quadratic with both zeros to the left of the strip. -/
theorem integral_vertical_eq_of_exp_growth {F : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hd : Differentiable ℂ F)
    (hg : ∃ C A : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖F z‖ ≤ C * Real.exp (A*|z.im|))
    (ha : ∃ C ≥ (0:ℝ), ∀ y : ℝ, ‖F (a+y*Complex.I)‖*(1+|y|)^2 ≤ C)
    (hb : ∃ C ≥ (0:ℝ), ∀ y : ℝ, ‖F (b+y*Complex.I)‖*(1+|y|)^2 ≤ C) :
    (∫ y : ℝ, F (a + y*Complex.I)) = ∫ y : ℝ, F (b + y*Complex.I) := by
  obtain ⟨C,A,hg⟩ := hg
  obtain ⟨U,hU,ha⟩ := ha
  obtain ⟨V,hV,hb⟩ := hb
  let p (z : ℂ) := z - a + 1
  let G (z : ℂ) := F z * p z ^ 2
  let D := b-a+1
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hn (z : ℂ) (hz : z.re ∈ Icc a b) : ‖p z‖ ≤ D*(1+|z.im|) := by
    apply (norm_le_abs_re_add_abs_im _).trans
    simp only [p,add_re,sub_re,ofReal_re,one_re,add_im,sub_im,ofReal_im,
      one_im,sub_zero,add_zero,abs_of_nonneg (show 0 ≤ z.re-a+1 by linarith [hz.1])]
    dsimp [D]
    nlinarith [hz.2,mul_nonneg (sub_nonneg.mpr hab.le) (abs_nonneg z.im)]
  have hpoly (z : ℂ) (hz : z.re ∈ Icc a b) :
      ‖G z‖ ≤ D^2 * (‖F z‖*(1+|z.im|)^2) := by
    rw [show ‖G z‖ = ‖F z‖ * ‖p z‖^2 by simp [G]]
    calc
      _ ≤ ‖F z‖ * (D*(1+|z.im|))^2 := by gcongr; exact hn z hz
      _ = _ := by ring
  have hedge (x : ℝ) (hx : x ∈ Icc a b) {E : ℝ}
      (he : ∀ y : ℝ, ‖F (x+y*Complex.I)‖*(1+|y|)^2 ≤ E) (z : ℂ) (hz : z.re=x) :
      ‖G z‖ ≤ D^2 * E := by
    apply (hpoly z (hz ▸ hx)).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
    simpa [← hz] using he z.im
  let c := Real.pi / (b-a) / 2
  have hπ : 0 < Real.pi / (b-a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hc : 0 < c := by dsimp [c]; positivity
  let M := max A 0 + 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpl (z : ℂ) (hz : z.re ∈ Icc a b) : ‖G z‖ ≤ D^2 * max U V := by
    apply PhragmenLindelof.vertical_strip (f := G) (a := a) (b := b)
      ((hd.mul (by dsimp [p]; fun_prop : Differentiable ℂ (fun z => p z ^ 2))).diffContOnCl)
      _ _ _ hz.1 hz.2
    · refine ⟨c,by dsimp [c]; linarith,M/c,IsBigO.of_bound (D^2*max C 0) ?_⟩
      apply eventually_inf_principal.mpr
      apply Eventually.of_forall
      intro w hw
      have hw' := Ioo_subset_Icc_self hw
      have h₁ : (1+|w.im|)^2 ≤ Real.exp (2*|w.im|) := by
        rw [two_mul, Real.exp_add, ← sq]
        exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp |w.im|]) 2
      have h₂ : A*|w.im| + 2*|w.im| ≤ M/c * Real.exp (c*|w.im|) := calc
        _ ≤ M*|w.im| := by dsimp [M]; nlinarith [mul_le_mul_of_nonneg_right (le_max_left A 0) (abs_nonneg w.im)]
        _ = M/c * (c*|w.im|) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (c*|w.im|)]) (div_nonneg hM hc.le)
      calc
        _ ≤ D^2*(‖F w‖*(1+|w.im|)^2) := hpoly w hw'
        _ ≤ D^2*((max C 0 * Real.exp (A*|w.im|))*Real.exp (2*|w.im|)) := by
          gcongr
          exact (hg w hw').trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_pos _).le)
        _ = (D^2*max C 0)*Real.exp (A*|w.im|+2*|w.im|) := by rw [Real.exp_add]; ring
        _ ≤ _ := by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; gcongr
    · intro w hw
      exact (hedge a ⟨le_rfl,hab.le⟩ ha w hw).trans (by gcongr; exact le_max_left ..)
    · intro w hw
      exact (hedge b ⟨hab.le,le_rfl⟩ hb w hw).trans (by gcongr; exact le_max_right ..)
  apply integral_vertical_eq_of_strip hab.le (C := D^2*max U V) (by positivity) (fun z _ => hd z)
  intro z hz
  rw [le_div_iff₀ (by positivity)]
  apply le_trans _ (hpl z hz)
  dsimp only [G]
  rw [norm_mul,norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [p]
  nlinarith [hz.1,sq_nonneg (z.re-a)]

private theorem reciprocal_gamma_growth (h : DLMFGammaVertical) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc (-(1/2:ℝ)) 3 →
      ‖(Gamma z)⁻¹‖ ≤ C * Real.exp ((1+Real.pi/2)*|z.im|) := by
  obtain ⟨T,hT⟩ := h 3 (1/2) (by norm_num)
  let R := max 1 T
  let K := reProdIm (Icc (-(1/2:ℝ)) 3) (Icc (-R) R)
  have hk : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨U,hU⟩ := hk.exists_bound_of_continuousOn differentiable_one_div_Gamma.continuous.continuousOn
  let B := 2 / Real.sqrt (2*Real.pi)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨max B U,hB.le.trans (le_max_left ..),fun z hz => ?_⟩
  let y := |z.im|
  by_cases hy : R ≤ y
  · have hy₁ : 1 ≤ y := (le_max_left ..).trans hy
    have hy₀ : 0 < y := zero_lt_one.trans_le hy₁
    let M := Real.sqrt (2*Real.pi) * y^(z.re-1/2) * Real.exp (-Real.pi*y/2)
    have hM : 0 < M := by dsimp [M]; positivity
    have low := (abs_lt.mp (hT z.re z.im (abs_le.mpr ⟨by linarith [hz.1],hz.2⟩)
      ((le_max_right ..).trans hy))).1
    rw [re_add_im] at low
    change -(1/2 : ℝ) < ‖Gamma z‖ / M - 1 at low
    have hl : M/2 ≤ ‖Gamma z‖ := by
      have := (le_div_iff₀ hM).mp (show (1/2:ℝ) ≤ ‖Gamma z‖/M by linarith)
      linarith
    have hpow : y^(-(1:ℝ)) ≤ y^(z.re-1/2) := Real.rpow_le_rpow_of_exponent_le hy₁ (by linarith [hz.1])
    have hinv : (y^(z.re-1/2))⁻¹ ≤ y := by
      rw [Real.rpow_neg_one] at hpow
      apply (inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hy₀ _)).mpr
      exact (inv_le_iff_one_le_mul₀ hy₀).mp hpow |>.trans_eq (mul_comm ..)
    rw [norm_inv]
    calc
      _ ≤ (M/2)⁻¹ := inv_anti₀ (by positivity) hl
      _ = B * (y^(z.re-1/2))⁻¹ * Real.exp (Real.pi*y/2) := by
        dsimp [M,B]
        rw [show -Real.pi*y/2 = -(Real.pi*y/2) by ring,Real.exp_neg]
        group
      _ ≤ B * Real.exp y * Real.exp (Real.pi*y/2) := by
        gcongr
        exact hinv.trans (by linarith [Real.add_one_le_exp y])
      _ = B * Real.exp ((1+Real.pi/2)*y) := by
        rw [mul_assoc,← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_pos _).le
  · have hzK : z ∈ K := ⟨hz,abs_le.mp (le_of_not_ge hy)⟩
    exact (hU z hzK).trans ((le_max_right B U).trans (le_mul_of_one_le_right (hB.le.trans (le_max_left ..))
      (Real.one_le_exp (by positivity))))

/-- On the strip used in smoothed reflection, the reciprocal of the completed
archimedean factor grows at most exponentially with height. -/
theorem norm_inv_reflectionGammaFactor_strip (h : DLMFGammaVertical) :
    ∃ C A : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-(1/2:ℝ)) (3/2) →
      ‖(reflectionGammaFactor z)⁻¹‖ ≤ C * Real.exp (A*|z.im|) := by
  obtain ⟨B,hB,hγ⟩ := reciprocal_gamma_growth h
  let p := 2*Real.pi
  have hp : 1 ≤ p := by dsimp [p]; linarith [Real.pi_gt_three]
  let A := 1+Real.pi/2
  refine ⟨B^2*p^3,2*A,by positivity, fun z hz => ?_⟩
  have hg (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1) : ‖(Gamma (z+c))⁻¹‖ ≤ B*Real.exp (A*|z.im|) := by
    simpa [A] using hγ (z+c) (by simp only [add_re,ofReal_re,mem_Icc]; constructor <;> linarith [hz.1,hz.2])
  have h₁ := hg (1/3) (by norm_num) (by norm_num)
  have h₂ := hg (2/3) (by norm_num) (by norm_num)
  push_cast at h₁ h₂
  have hw : ‖((p : ℂ)^(-2*z))⁻¹‖ ≤ p^3 := by
    rw [norm_inv,norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hp)]
    have he : (-2*z).re = -(2*z.re) := by simp
    rw [he,Real.rpow_neg (zero_le_one.trans hp),inv_inv,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hp (by norm_num; linarith [hz.2])
  simp only [reflectionGammaFactor,mul_inv_rev,norm_mul]
  change _ * (_ * ‖((p : ℂ)^(-2*z))⁻¹‖) ≤ _
  calc
    _ ≤ (B*Real.exp (A*|z.im|))*((B*Real.exp (A*|z.im|))*p^3) := by gcongr
    _ = _ := by rw [show 2*A*|z.im| = A*|z.im|+A*|z.im| by ring,Real.exp_add]; ring

end Masullo.QRH.MeanSquare
