import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Angular Fourier mean-square estimates

Plancherel's identity for the angular Fourier integral of an integrable, square-integrable
function, and a mean-square bound for Dirichlet polynomials of length at most the height.

Part of a Carlson-type mean-square zero-density argument due to OpenAI Codex (E36),
formalised by Claude; this module was written by Codex.
-/

open MeasureTheory FourierTransform SchwartzMap Real Complex
open scoped FourierTransform SchwartzMap TemperedDistribution RealInnerProductSpace ContDiff
namespace WeilExplicit

theorem fourier_ae {g : ℝ → ℂ} (hi : Integrable g) (h2 : MemLp g 2) :
    𝓕 g =ᵐ[volume] ⇑(𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) := by
  have hc : Continuous (𝓕 g) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable
    (Lp.memLp _ |>.locallyIntegrable (by norm_num))
  intro h hdiff hsupp
  let φ : 𝓢(ℝ, ℂ) := (hsupp.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ h) by fun_prop)
  have hp := congrArg (fun F : 𝓢'(ℝ, ℂ) ↦ F φ) (Lp.fourier_toTemperedDistribution_eq (h2.toLp g))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hp
  have hpair : ∫ x, 𝓕 φ x • g x = ∫ x, φ x • 𝓕 g x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      continuous_fourierChar continuous_inner φ.integrable hi
  calc
    _ = ∫ x, φ x • 𝓕 g x := by simp [φ]
    _ = ∫ x, 𝓕 φ x • g x := hpair.symm
    _ = ∫ x, 𝓕 φ x • h2.toLp g x := integral_congr_ae <|
      h2.coeFn_toLp.symm.mono fun x hx ↦ congrArg (fun z ↦ 𝓕 φ x • z) hx
    _ = _ := by simpa [φ] using hp


theorem plancherel {g : ℝ → ℂ} (hi : Integrable g) (h2 : MemLp g 2) :
    Integrable (fun t ↦ ‖𝓕 g t‖ ^ 2) ∧ ∫ t, ‖𝓕 g t‖ ^ 2 = ∫ v, ‖g v‖ ^ 2 := by
  let f := h2.toLp g
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 f
  have hF := fourier_ae hi h2
  have heq : (fun t ↦ ‖𝓕 g t‖ ^ 2) =ᵐ[volume] fun t ↦ ‖F t‖ ^ 2 :=
    hF.mono fun t ht ↦ congrArg (fun z ↦ ‖z‖ ^ 2) ht
  refine ⟨(Lp.memLp F).norm.integrable_sq.congr heq.symm, ?_⟩
  have hs : ∫ t, ‖F t‖ ^ 2 = ∫ v, ‖f v‖ ^ 2 := by
    apply Complex.ofRealLI.injective
    have h : inner ℂ F F = inner ℂ f f := Lp.inner_fourier_eq f f
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h
    simp only [inner_self_eq_norm_sq_to_K] at h
    simp only [← LinearIsometry.integral_comp_comm]
    convert! h using 2 <;> ext x <;> norm_cast
  exact (integral_congr_ae heq).trans (hs.trans (integral_congr_ae <|
    h2.coeFn_toLp.mono fun t ht ↦ congrArg (fun z ↦ ‖z‖ ^ 2) ht))

theorem freq (g : ℝ → ℂ) (t : ℝ) :
    (∫ v, g v * cexp (-(v * t) * I)) = 𝓕 g ((2 * π)⁻¹ * t) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

theorem raw_plancherel {g : ℝ → ℂ} (hi : Integrable g) (h2 : Integrable fun v ↦ ‖g v‖ ^ 2) :
    let F := fun t : ℝ ↦ ∫ v, g v * cexp (-(v * t) * I)
    Integrable (fun t ↦ ‖F t‖ ^ 2) ∧ ∫ t, ‖F t‖ ^ 2 = 2 * π * ∫ v, ‖g v‖ ^ 2 := by
  dsimp only
  simp_rw [freq]
  obtain ⟨hint, heq⟩ := 
    plancherel hi ((memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).2 h2)
  refine ⟨hint.comp_mul_left' (by positivity), ?_⟩
  rw [Measure.integral_comp_mul_left (fun x ↦ ‖𝓕 g x‖ ^ 2), inv_inv, abs_of_pos (by positivity),
    smul_eq_mul, heq]

open Set Finset

private noncomputable def phase (v t : ℝ) : ℂ := cexp (-(v * t) * I)

private theorem block_lower {a t : ℝ} (ha : 0 < a) (ht : |t| * a ≤ 1) :
    a / 2 ≤ ‖∫ v in Ioc 0 a, phase v t‖ := by
  have hc : Continuous (phase · t) := by unfold phase; fun_prop
  refine le_trans ?_ (Complex.re_le_norm _)
  have hre := integral_re (𝕜 := ℂ) (μ := volume.restrict (Ioc 0 a)) hc.integrableOn_Ioc
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  calc a / 2 = ∫ _v : ℝ in Ioc 0 a, (1/2 : ℝ) := by
         simp [measureReal_def, Real.volume_Ioc, ha.le, smul_eq_mul]; ring
       _ ≤ _ := by
         apply setIntegral_mono_on continuous_const.integrableOn_Ioc
           (Complex.continuous_re.comp hc).integrableOn_Ioc measurableSet_Ioc
         intro v hv
         have hv' : |v * t| ≤ 1 := by rw [abs_mul, abs_of_pos hv.1, mul_comm]; exact
           (mul_le_mul_of_nonneg_left hv.2 (abs_nonneg _)).trans ht
         have hcos := Real.one_sub_sq_div_two_le_cos (x := v * t)
         change (1:ℝ)/2 ≤ (phase v t).re
         simp only [phase, ← ofReal_mul, ← ofReal_neg, exp_ofReal_mul_I_re, Real.cos_neg]
         nlinarith [sq_abs (v*t), sq_nonneg (1 - |v*t|), mul_self_le_mul_self (abs_nonneg _) hv']

theorem block_mean {ι : Type*} (s : Finset ι) (freqs : ι → ℝ) (b : ι → ℂ)
    {a : ℝ} (ha : 0 < a) (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Ioc (freqs i) (freqs i + a)) (Ioc (freqs j) (freqs j + a)))
    {l r : ℝ} (hI : ∀ t ∈ Icc l r, |t| * a ≤ 1) :
    ∫ t in Icc l r, ‖∑ i ∈ s, b i * cexp (-(freqs i * t) * I)‖ ^ 2 ≤
      8 * π / a * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  classical
  let J i := Ioc (freqs i) (freqs i + a)
  let g i := (J i).indicator (fun _ ↦ b i)
  let G v := ∑ i ∈ s, g i v
  have hg (i) : Integrable (g i) :=
    (continuous_const.integrableOn_Ioc (a := freqs i) (b := freqs i + a)).integrable_indicator
      measurableSet_Ioc
  have hG : Integrable G := integrable_finsetSum _ fun i _ ↦ hg i
  let q i := (J i).indicator fun _ ↦ ‖b i‖ ^ 2
  have hq (i) : Integrable (q i) :=
    (continuous_const.integrableOn_Ioc (a := freqs i) (b := freqs i + a)).integrable_indicator
      measurableSet_Ioc
  have hGq (v) : ‖G v‖ ^ 2 = ∑ i ∈ s, q i v := by
    by_cases h : ∃ i ∈ s, v ∈ J i
    · obtain ⟨i, hi, hvi⟩ := h
      have h0 j (hj : j ∈ s) (hji : j ≠ i) : v ∉ J j :=
        fun hvj ↦ Set.disjoint_left.mp (hdis j hj i hi hji) hvj hvi
      have hg0 (j) (hj : j ∈ s) (hji : j ≠ i) : g j v = 0 := indicator_of_notMem (h0 j hj hji) _
      have hq0 (j) (hj : j ∈ s) (hji : j ≠ i) : q j v = 0 := indicator_of_notMem (h0 j hj hji) _
      rw [show G v = g i v from sum_eq_single_of_mem i hi hg0, sum_eq_single_of_mem i hi hq0]
      simp [g, q, hvi]
    · push Not at h
      rw [show G v = 0 from sum_eq_zero fun i hi ↦ indicator_of_notMem (h i hi) _,
        sum_eq_zero (fun i hi ↦ indicator_of_notMem (h i hi) _ : ∀ i ∈ s, q i v = 0)]
      simp
  have hG2 : Integrable fun v ↦ ‖G v‖ ^ 2 := by
    simp_rw [hGq]; exact integrable_finsetSum _ fun i _ ↦ hq i
  have hsum : ∫ v, ‖G v‖ ^ 2 = a * ∑ i ∈ s, ‖b i‖ ^ 2 := by
    simp_rw [hGq]; rw [integral_finsetSum _ fun i _ ↦ hq i, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    simp [q, J, integral_indicator measurableSet_Ioc, measureReal_def, Real.volume_Ioc, ha.le,
      smul_eq_mul]
  let H t := ∫ v, G v * phase v t
  let A t := ∫ v in Ioc 0 a, phase v t
  let D t := ∑ i ∈ s, b i * phase (freqs i) t
  have hHD t : H t = D t * A t := by
    dsimp [H, G, D, A]
    simp_rw [sum_mul]
    have hint (i : ι) : Integrable fun v ↦ g i v * phase v t := by
      refine (hg i).mul_bdd (c := 1) (by unfold phase; fun_prop) (.of_forall fun v ↦ ?_)
      exact le_of_eq
        (by simp [phase, ← ofReal_mul, ← ofReal_neg, norm_exp_ofReal_mul_I] : ‖phase v t‖ = 1)
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    refine sum_congr rfl fun i _ ↦ ?_
    have htrans : (∫ v in Ioc (freqs i) (freqs i + a), b i * phase v t) =
        ∫ v in 0..a, b i * phase (v + freqs i) t := by
      rw [intervalIntegral.integral_comp_add_right (fun v ↦ b i * phase v t), zero_add, add_comm a,
        intervalIntegral.integral_of_le (by linarith)]
    rw [← intervalIntegral.integral_of_le ha.le]
    simp_rw [g, ← indicator_mul_left (J i) (fun _ ↦ b i) (fun x ↦ phase x t)]
    rw [integral_indicator (s := J i) measurableSet_Ioc, htrans,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [phase, ofReal_add]
    rw [show -((v + freqs i : ℂ) * t) * I = -(freqs i * t) * I + -(v * t) * I by ring,
      Complex.exp_add]
    ring
  obtain ⟨hi, he⟩ := raw_plancherel hG hG2
  change Integrable (fun t ↦ ‖H t‖ ^ 2) at hi
  change ∫ t, ‖H t‖ ^ 2 = _ at he
  rw [hsum] at he
  calc ∫ t in Icc l r, ‖D t‖ ^ 2 ≤ ∫ t in Icc l r, (2/a)^2 * ‖H t‖ ^ 2 := by
         refine integral_mono_of_nonneg (.of_forall fun _ ↦ sq_nonneg _)
           (hi.const_mul _).integrableOn ?_
         filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
         rw [hHD, norm_mul]
         have hA : a/2 ≤ ‖A t‖ := block_lower ha (hI t ht)
         have h : 1 ≤ 2/a * ‖A t‖ := by field_simp; linarith
         nlinarith [mul_le_mul_of_nonneg_left ((one_le_pow₀ h : (1:ℝ) ≤ (2/a * ‖A t‖)^2))
           (sq_nonneg ‖D t‖)]
       _ ≤ ∫ t, (2/a)^2 * ‖H t‖ ^ 2 :=
         setIntegral_le_integral (hi.const_mul _) (.of_forall fun _ ↦ by positivity)
       _ = _ := by rw [integral_const_mul, he]; field_simp; ring
theorem dir_mean (N : ℕ) (b : ℕ → ℂ) {T : ℝ} (hT : 2 ≤ T) (hN : (N : ℝ) ≤ T) :
    ∫ t in Set.Icc (T - 1) (2*T + 1),
        ‖∑ i ∈ Finset.Icc 1 N, b i * cexp (-(Real.log i * t) * I)‖ ^ 2 ≤
      24 * π * T * ∑ i ∈ Finset.Icc 1 N, ‖b i‖ ^ 2 := by
  let a := (3*T)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hlo {i j : ℕ} (hi : i ∈ Finset.Icc 1 N) (hj : j ∈ Finset.Icc 1 N) (hij : i < j) :
      Real.log i + a ≤ Real.log j := by
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast ((Finset.mem_Icc.mp hi).1.trans hij.le)
    have hjT : (j : ℝ) ≤ T := (Nat.cast_le.mpr (Finset.mem_Icc.mp hj).2).trans hN
    have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hj0 hi0)
    rw [Real.log_div hj0.ne' hi0.ne', inv_div] at hlog
    have h1 : a ≤ 1 / (j : ℝ) := by
      rw [one_div]; exact inv_anti₀ hj0 (by linarith)
    have h2 : 1 / (j : ℝ) ≤ 1 - i / (j : ℝ) := by field_simp; linarith
    linarith
  have h := block_mean (Finset.Icc 1 N) (fun i : ℕ ↦ Real.log i) b ha (fun i hi j hj hne ↦ by
    rcases lt_or_gt_of_ne hne with hh | hh
    · exact Set.Ioc_disjoint_Ioc_of_le (hlo hi hj hh)
    · exact (Set.Ioc_disjoint_Ioc_of_le (hlo hj hi hh)).symm)
    (l := T-1) (r := 2*T+1) (fun t ht ↦ by
      rw [abs_of_nonneg (by linarith [ht.1]), show t*a = t/(3*T) by rfl, div_le_one (by positivity)]
      linarith [ht.2])
  rwa [show 8 * π / a = 24 * π * T by dsimp only [a]; rw [div_inv_eq_mul]; ring] at h

end WeilExplicit
