import Masullo.QRH.MeanSquare.ReflectionCusp
import Masullo.QRH.MeanSquare.ReflectionDecay
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Differentiation of Patterson's expansion at positive height -/

noncomputable section

open NumberField MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private def kIntegrand (x t : ℝ) : ℂ :=
  (Real.exp (-x * Real.cosh t) * Real.cosh (t / 3) : ℝ)

private theorem besselK_eq_kIntegral (x : ℝ) :
    besselK (1 / 3) x = ∫ t in Ioi 0, kIntegrand x t := by
  unfold besselK kIntegrand
  congr 1
  funext t
  rw [Complex.ofReal_mul, Complex.ofReal_cosh, Complex.ofReal_div, Complex.ofReal_ofNat]
  congr 2
  ring

private def kDerivIntegrand (x t : ℝ) : ℂ := -Real.cosh t * kIntegrand x t

private theorem hasDerivAt_kIntegrand (x t : ℝ) :
    HasDerivAt (kIntegrand · t) (kDerivIntegrand x t) x := by
  have h := (((hasDerivAt_id x).neg.mul_const (Real.cosh t)).exp.mul_const (Real.cosh (t / 3))).ofReal_comp
  convert h using 1 <;> dsimp [kDerivIntegrand, kIntegrand]
  push_cast
  ring

/-- An integrable bound for the Bessel integrand and its height derivative,
uniformly for x ≥ 4δ and t ≥ 0. -/
private theorem kIntegrand_bounds {δ x t : ℝ} (hδ : 0 < δ) (hx : 4 * δ ≤ x) (ht : 0 ≤ t) :
    ‖kIntegrand x t‖ ≤ δ⁻¹ ^ 2 * Real.exp (-δ * t) ∧
    ‖kDerivIntegrand x t‖ ≤ δ⁻¹ ^ 2 * Real.exp (-δ * t) := by
  let u := Real.cosh t
  let w := Real.cosh (t / 3)
  have hu : 1 ≤ u := Real.one_le_cosh _
  have ht' : t ≤ u := (Real.self_le_sinh_iff.mpr ht).trans (Real.sinh_lt_cosh t).le
  have hw : w ≤ u := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ t / 3), abs_of_nonneg ht]
    linarith
  have hwu : 0 ≤ w := (Real.cosh_pos _).le
  have hu₀ : 0 ≤ u := zero_le_one.trans hu
  have hexp : u ≤ δ⁻¹ * Real.exp (δ * u) := by
    rw [inv_mul_eq_div, le_div_iff₀ hδ]
    linarith [Real.add_one_le_exp (δ * u)]
  have hcalc : u ^ 2 * Real.exp (-x * u) ≤ δ⁻¹ ^ 2 * Real.exp (-δ * t) := by
    calc
      _ ≤ (δ⁻¹ * Real.exp (δ * u)) ^ 2 * Real.exp (-x * u) := by gcongr
      _ = δ⁻¹ ^ 2 * Real.exp ((2 * δ - x) * u) := by
        rw [mul_pow, pow_two (Real.exp _), mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hx) hu₀,
          mul_nonneg hδ.le (sub_nonneg.mpr ht'), mul_nonneg hδ.le hu₀]
  have h₁ : ‖kIntegrand x t‖ = Real.exp (-x * u) * w := by
    change ‖((Real.exp (-x * u) * w : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hwu)]
  have h₂ : ‖kDerivIntegrand x t‖ = u * (Real.exp (-x * u) * w) := by
    change ‖-(u : ℂ) * kIntegrand x t‖ = _
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu₀, h₁]
  rw [h₁, h₂]
  constructor
  · apply le_trans _ hcalc
    nlinarith [mul_le_mul_of_nonneg_left hw (Real.exp_pos (-x * u)).le,
      mul_nonneg (sub_nonneg.mpr hu) (mul_nonneg hu₀ (Real.exp_pos (-x * u)).le)]
  · apply le_trans _ hcalc
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (mul_nonneg hu₀ (Real.exp_pos (-x * u)).le)]

/-- Differentiation under the defining integral for order one third. -/
theorem hasDerivAt_besselK_oneThird {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselK (1 / 3)) (∫ t in Ioi 0, kDerivIntegrand x t) x := by
  let δ := x / 8
  have hδ : 0 < δ := by positivity
  let bound (t : ℝ) := δ⁻¹ ^ 2 * Real.exp (-δ * t)
  have hB : IntegrableOn bound (Ioi 0) := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hδ) 0).const_mul _
  let μ := volume.restrict (Ioi (0 : ℝ))
  have ha : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hmeas (y : ℝ) : AEStronglyMeasurable (kIntegrand y) μ := by
    exact (by unfold kIntegrand; fun_prop : Continuous (kIntegrand y)).aestronglyMeasurable
  have hmeas' (y : ℝ) : AEStronglyMeasurable (kDerivIntegrand y) μ := by
    exact (by unfold kDerivIntegrand kIntegrand; fun_prop : Continuous (kDerivIntegrand y)).aestronglyMeasurable
  have hI : Integrable (kIntegrand x) μ := hB.mono' (hmeas _) (ha.mono fun t ht =>
    (kIntegrand_bounds hδ (by dsimp [δ]; linarith) ht.le).1)
  have hs : Ioi (4 * δ) ∈ 𝓝 x := Ioi_mem_nhds (by dsimp [δ]; linarith)
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := kIntegrand) hs
    (Eventually.of_forall hmeas) hI (hmeas' x) (ha.mono fun t ht y hy =>
      (kIntegrand_bounds hδ (le_of_lt hy) ht.le).2) hB
    (ae_of_all _ fun t y _ => hasDerivAt_kIntegrand y t)
  change HasDerivAt (fun y => besselK (1 / 3) y) _ _
  simpa only [besselK_eq_kIntegral] using hder.2

theorem differentiableAt_besselK_oneThird {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (besselK (1 / 3)) x :=
  (hasDerivAt_besselK_oneThird hx).differentiableAt

/-- The integral and its derivative decay exponentially, with one constant for
all arguments bounded away from zero. -/
theorem exists_besselK_oneThird_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 8 * δ ≤ x →
      ‖besselK (1 / 3) x‖ ≤ C * Real.exp (-(x / 2)) ∧
      ‖deriv (besselK (1 / 3)) x‖ ≤ C * Real.exp (-(x / 2)) := by
  let B (t : ℝ) := δ⁻¹ ^ 2 * Real.exp (-δ * t)
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hB : Integrable B μ := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hδ) 0).const_mul _
  have hB₀ (t : ℝ) : 0 ≤ B t := by dsimp [B]; positivity
  refine ⟨∫ t, B t ∂μ, integral_nonneg hB₀, ?_⟩
  intro x hx
  have hx₀ : 0 < x := by linarith
  rw [besselK_eq_kIntegral, (hasDerivAt_besselK_oneThird hx₀).deriv]
  have hb (t : ℝ) (ht : 0 < t) :
      ‖kIntegrand x t‖ ≤ B t * Real.exp (-(x / 2)) ∧
      ‖kDerivIntegrand x t‖ ≤ B t * Real.exp (-(x / 2)) := by
    have hs : kIntegrand x t = kIntegrand (x / 2) t * Real.exp (-(x / 2) * Real.cosh t) := by
      unfold kIntegrand
      rw [← Complex.ofReal_mul]
      congr 1
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring
    have he : Real.exp (-(x / 2) * Real.cosh t) ≤ Real.exp (-(x / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hx₀.le (sub_nonneg.mpr (Real.one_le_cosh t))])
    have h₁ := kIntegrand_bounds hδ (x := x / 2) (by linarith) ht.le
    have hs' : kDerivIntegrand x t =
        kDerivIntegrand (x / 2) t * Real.exp (-(x / 2) * Real.cosh t) := by
      rw [kDerivIntegrand, kDerivIntegrand, hs, mul_assoc]
    rw [hs, hs', norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact ⟨mul_le_mul h₁.1 he (Real.exp_pos _).le (hB₀ _),
      mul_le_mul h₁.2 he (Real.exp_pos _).le (hB₀ _)⟩
  have hL (f : ℝ → ℂ) (hh : ∀ᵐ t ∂μ, ‖f t‖ ≤ B t * Real.exp (-(x / 2))) :
      ‖∫ t, f t ∂μ‖ ≤ (∫ t, B t ∂μ) * Real.exp (-(x / 2)) :=
    (norm_integral_le_of_norm_le (hB.mul_const _) hh).trans_eq (integral_mul_const _ _)
  have ha : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  exact ⟨hL _ (ha.mono fun t ht => (hb t ht).1), hL _ (ha.mono fun t ht => (hb t ht).2)⟩

theorem norm_pattersonCharacter (z : ℂ) : ‖pattersonCharacter z‖ = 1 := by
  simp [pattersonCharacter, Complex.norm_exp, Complex.mul_re]

/-- The horizontal derivative of an absolutely convergent Fourier series whose
first frequency moments also converge absolutely. -/
theorem hasDerivAt_patterson_sum {ι : Type*} (l a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) (ha₁ : Summable fun i => ‖a i‖ * ‖l i‖) (z u : ℂ) :
    HasDerivAt (fun t : ℝ => ∑' i, a i * pattersonCharacter (l i * (z + t * u)))
      (∑' i, a i * pattersonCharacter (l i * z) *
        (4 * Real.pi * Complex.I * ((l i * u).re : ℂ))) 0 := by
  let f (i : ι) (t : ℝ) := a i * pattersonCharacter (l i * (z + t * u))
  let g (i : ι) (t : ℝ) := f i t * (4 * Real.pi * Complex.I * ((l i * u).re : ℂ))
  have hd (i : ι) (t : ℝ) : HasDerivAt (f i) (g i t) t := by
    have H := hasDerivAt_patterson_mode (a i) (l i) (z + t * u) u
    let q (s : ℝ) := s - t
    have hq : HasDerivAt q 1 t := (hasDerivAt_id t).sub_const t
    have hq₀ : q t = 0 := sub_self _
    rw [← hq₀] at H
    have H' := H.scomp t hq
    rw [one_smul] at H'
    apply H'.congr_of_eventuallyEq
    filter_upwards with s
    dsimp [f, q]
    push_cast
    ring_nf
  have hg (i : ι) (t : ℝ) : ‖g i t‖ ≤ ‖a i‖ * ‖l i‖ * (4 * Real.pi * ‖u‖) := by
    simp only [g, f, norm_mul, norm_pattersonCharacter, mul_one, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hRe := Complex.abs_re_le_norm (l i * u)
    rw [norm_mul] at hRe
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖a i‖ * (4 * Real.pi * (‖l i‖ * ‖u‖)) := by gcongr
      _ = _ := by ring
  have h₀ : Summable fun i => f i 0 := ha.of_norm_bounded fun i => by
    simp [f, norm_pattersonCharacter]
  have H := hasDerivAt_tsum (ha₁.mul_right (4 * Real.pi * ‖u‖)) hd hg h₀ 0
  simpa only [g, f, Complex.ofReal_zero, zero_mul, add_zero] using H

private abbrev U := ℂ × ℝ

private def thetaTerm (l a : ℂ) (p : U) : ℂ :=
  a * ((p.2 : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖l‖ * p.2) *
    pattersonCharacter (l * p.1))

private theorem fderiv_thetaTerm {l a : ℂ} (hl : l ≠ 0) (p : U) (hp : 0 < p.2) :
    DifferentiableAt ℝ (thetaTerm l a) p ∧
    ‖fderiv ℝ (thetaTerm l a) p‖ ≤
      let k := 4 * Real.pi * ‖l‖
      let K := besselK (1 / 3)
      ‖a‖ * (p.2 * ‖K (k*p.2)‖ * k +
        (‖K (k*p.2)‖ + p.2 * k * ‖deriv K (k*p.2)‖)) := by
  let k := 4 * Real.pi * ‖l‖
  let K := besselK (1 / 3)
  have hk : 0 < k := by dsimp [k]; positivity
  let V (v : ℝ) := (v : ℂ) * K (k * v)
  let V' := ((1 : ℂ) * K (k*p.2) + (p.2 : ℂ) * ((k : ℝ) • deriv K (k*p.2)))
  have hK := (differentiableAt_besselK_oneThird (mul_pos hk hp)).hasDerivAt
  have hKV : HasDerivAt (fun v => K (k*v)) ((k : ℝ) • deriv K (k*p.2)) p.2 := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hK.scomp p.2 ((hasDerivAt_id p.2).const_mul k))
  have hV : HasDerivAt V V' p.2 := (hasDerivAt_id p.2).ofReal_comp.mul hKV
  let vert := ContinuousLinearMap.snd ℝ ℂ ℝ
  have hdV := hV.hasFDerivAt.comp p vert.hasFDerivAt
  let reL := Complex.reCLM.comp (l • ContinuousLinearMap.fst ℝ ℂ ℝ)
  let E (s : ℝ) := Complex.exp (2 * Real.pi * Complex.I * (2 * s : ℝ))
  have hE := (((hasDerivAt_id (reL p)).const_mul 2).ofReal_comp.const_mul
    (2 * Real.pi * Complex.I)).cexp
  have hdE := hE.hasFDerivAt.comp p reL.hasFDerivAt
  have hd := (hdV.mul hdE).const_mul a
  change HasFDerivAt (thetaTerm l a) _ p at hd
  refine ⟨hd.differentiableAt, ?_⟩
  have hre : ‖reL‖ ≤ ‖l‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [Complex.reCLM_norm, one_mul, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ..)
  have hPhase : E (reL p) = pattersonCharacter (l * p.1) := rfl
  have h₁ : ‖ContinuousLinearMap.toSpanSingleton ℝ V' ∘L vert‖ ≤
      ‖K (k*p.2)‖ + p.2 * k * ‖deriv K (k*p.2)‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    apply (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ..)).trans
    dsimp only [V']
    apply (norm_add_le ..).trans
    simp only [one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le,
      norm_smul, Real.norm_of_nonneg hk.le, mul_assoc, le_refl]
  have h₂ : ‖ContinuousLinearMap.toSpanSingleton ℝ
      (E (reL p) * (2 * Real.pi * Complex.I * ((2 * 1 : ℝ) : ℂ))) ∘L reL‖ ≤ k := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [ContinuousLinearMap.norm_toSpanSingleton, norm_mul, hPhase, norm_pattersonCharacter, one_mul]
    simp only [mul_one, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_ofNat]
    dsimp [k]
    nlinarith [mul_le_mul_of_nonneg_left hre Real.pi_pos.le]
  rw [hd.fderiv, norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
  apply (norm_add_le ..).trans
  rw [norm_smul, norm_smul]
  change ‖V p.2‖ * _ + ‖E (reL p)‖ * _ ≤ _
  rw [hPhase, norm_pattersonCharacter, one_mul]
  have hVn : ‖V p.2‖ = p.2 * ‖K (k*p.2)‖ := by
    simp only [V, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
  rw [hVn]
  exact add_le_add (mul_le_mul_of_nonneg_left h₂ (by positivity)) h₁

private abbrev PattersonIndex := {m : 𝓔 // m ≠ 0}

private theorem frequency_pos (m : PattersonIndex) : 0 < ‖pattersonFrequency m‖ := by
  rw [pattersonFrequency, norm_pos_iff]
  apply div_ne_zero
  · exact (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr m.2
  · exact pow_ne_zero _ ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr eisLambda_prime.ne_zero)

set_option maxHeartbeats 1000000 in
private theorem exists_thetaTerm_majorant {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    {v : ℝ} (hv : 0 < v) :
    ∃ g : PattersonIndex → ℝ, Summable g ∧ ∀ (m : PattersonIndex) (p : U), p.2 ∈ Ioo (v/2) (2*v) →
      ‖fderiv ℝ (thetaTerm (pattersonFrequency m) (τ (pattersonFrequency m))) p‖ ≤ g m := by
  let L := ‖eisEmbedding eisLambda ^ 3‖
  have hL : 0 < L := norm_pos_iff.mpr (pow_ne_zero _
    ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr eisLambda_prime.ne_zero))
  let δ := Real.pi * v / L / 4
  have hδ : 0 < δ := by positivity
  obtain ⟨C, hC, hB⟩ := exists_besselK_oneThird_bound hδ
  let b := Real.pi * v
  have hb : 0 < b := mul_pos Real.pi_pos hv
  let S (s : ℝ) (m : 𝓔) :=
    ‖pattersonFrequency m‖ ^ s * Real.exp (-b * ‖pattersonFrequency m‖)
  have hS (s : ℝ) : Summable (fun m : PattersonIndex => S s m) :=
    (summable_pattersonFrequency_rpow_exp s hb).subtype _
  let g (m : PattersonIndex) := 27*C*S (1/3) m + (27*C*(16*Real.pi*v))*S (1/3+1) m
  refine ⟨g, ((hS _).mul_left _).add ((hS _).mul_left _), ?_⟩
  intro m p h
  let l := pattersonFrequency m
  let t := ‖l‖
  let k := 4 * Real.pi * t
  have ht₀ : 0 < t := frequency_pos m
  have hk : 0 < k := by dsimp [k]; positivity
  have hp : 0 < p.2 := by linarith [h.1]
  have hmin : 1 / L ≤ t := by
    change 1 / L ≤ ‖eisEmbedding m.1 / eisEmbedding eisLambda ^ 3‖
    rw [norm_div]
    exact div_le_div_of_nonneg_right (one_le_norm_eisEmbedding m.2) hL.le
  have hb' : 8*δ ≤ k*p.2 := calc
    _ = (4*Real.pi*(1/L))*(v/2) := by dsimp [δ]; ring
    _ ≤ k*p.2 := by dsimp [k]; gcongr; exact h.1.le
  let E := C * Real.exp (-b * t)
  have hE : 0 ≤ E := mul_nonneg hC (Real.exp_pos _).le
  have hb'' : C * Real.exp (-(k*p.2/2)) ≤ E := by
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have hr := mul_le_mul_of_nonneg_left h.1.le (mul_nonneg Real.pi_pos.le ht₀.le)
    dsimp [b, k]
    linarith
  have hK := (hB _ hb').1.trans hb''
  have hK' := (hB _ hb').2.trans hb''
  have hτ : ‖τ l‖ ≤ 27*t ^ (1/3 : ℝ) := by
    have H := ht.norm_normalized_le l
    rw [norm_div, Complex.norm_ofNat, Complex.norm_conj, div_le_iff₀ (by norm_num : (0 : ℝ) < 27),
      mul_comm] at H
    exact H
  have hd := (fderiv_thetaTerm (a := τ l) (norm_pos_iff.mp ht₀) p hp).2
  apply hd.trans
  change ‖τ l‖ * (p.2 * ‖besselK (1/3) (k*p.2)‖ * k +
      (‖besselK (1/3) (k*p.2)‖ + p.2*k*‖deriv (besselK (1/3)) (k*p.2)‖)) ≤ _
  calc
    _ ≤ (27*t^(1/3 : ℝ)) * ((2*v)*E*k + (E + (2*v)*k*E)) := by gcongr <;> exact h.2.le
    _ = g m := by
      change _ = 27*C*(t^(1/3 : ℝ)*Real.exp (-b*t)) +
        (27*C*(16*Real.pi*v))*(t^(1/3+1 : ℝ)*Real.exp (-b*t))
      rw [Real.rpow_add ht₀, Real.rpow_one]
      dsimp [E, k]
      ring

/-- The full Patterson expansion is jointly real differentiable in horizontal
position and height throughout the upper half-space. -/
theorem PattersonExpansion.differentiableAt_uncurry {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    DifferentiableAt ℝ (Function.uncurry θ) (z, v) := by
  let F (m : PattersonIndex) := thetaTerm (pattersonFrequency m) (τ (pattersonFrequency m))
  let Ω : Set U := univ ×ˢ Ioo (v/2) (2*v)
  have hΩ : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have hconn : IsPreconnected Ω := isPreconnected_univ.prod isPreconnected_Ioo
  have hvΩ : (z, v) ∈ Ω := ⟨mem_univ _, by constructor <;> linarith⟩
  obtain ⟨g, hg, hbound⟩ := exists_thetaTerm_majorant ht hv
  have hsum (p : U) (hp : 0 < p.2) :
      HasSum (fun m : PattersonIndex => F m p) (θ p.1 p.2 - σ * (p.2 ^ (2/3 : ℝ) : ℝ)) := by
    apply (he p.1 p.2 hp).congr_fun
    intro m
    dsimp [F, thetaTerm, pattersonFrequency]
    ring
  have hd (m : PattersonIndex) (p : U) (hp : p ∈ Ω) : DifferentiableAt ℝ (F m) p :=
    (fderiv_thetaTerm (norm_pos_iff.mp (frequency_pos m)) p (by linarith [hp.2.1])).1
  have H := hasFDerivAt_tsum_of_isPreconnected hg hΩ hconn
    (fun m p hp => (hd m p hp).hasFDerivAt) (fun m p hp => hbound m p hp.2) hvΩ
    (hsum _ hv).summable hvΩ
  have hconst : DifferentiableAt ℝ (fun p : U => (σ : ℂ) * (p.2 ^ (2/3 : ℝ) : ℝ)) (z,v) := by
    apply DifferentiableAt.const_mul
    have hp' : DifferentiableAt ℝ (fun q : U => q.2 ^ (2/3 : ℝ)) (z,v) := by
      change DifferentiableAt ℝ ((fun x : ℝ => x ^ (2/3 : ℝ)) ∘ Prod.snd) _
      apply DifferentiableAt.comp
      · exact (Real.hasDerivAt_rpow_const (x := v) (p := 2/3) (Or.inl hv.ne')).differentiableAt
      · exact differentiableAt_snd
    exact Complex.ofRealCLM.differentiableAt.comp _ hp'
  apply (H.differentiableAt.add hconst).congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hvΩ] with p hp
  change θ p.1 p.2 = (∑' m, F m p) + _
  rw [(hsum _ (by linarith [hp.2.1])).tsum_eq, sub_add_cancel]

/-- Amplitude before attaching the horizontal Fourier character in the normalized expansion. -/
def normalizedThetaMode (τ : ℂ → ℂ) (v : ℝ) (m : 𝓔) : ℂ :=
  conj (τ (pattersonFrequency m)) / 27 * v *
    besselK (1 / 3) (4 * Real.pi * ‖pattersonFrequency m‖ * v)

theorem PattersonCoefficients.summable_normalizedThetaMode {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    {v : ℝ} (hv : 0 < v) (s : ℝ) :
    Summable fun m : 𝓔 => ‖normalizedThetaMode τ v m‖ * ‖pattersonFrequency m‖ ^ s := by
  obtain ⟨C, hC, hB⟩ := exists_besselK_oneThird_bound (δ := 1) zero_lt_one
  have hb : 0 < 2 * Real.pi * v := by positivity
  have hk : 0 < 4 * Real.pi * v := by positivity
  apply ((summable_pattersonFrequency_rpow_exp (1/3 + s) hb).mul_left (v*C)).of_norm_bounded_eventually
  filter_upwards [tendsto_norm_pattersonFrequency.eventually_ge_atTop (8/(4*Real.pi*v)),
    tendsto_norm_pattersonFrequency.eventually_gt_atTop 0] with m hm hm₀
  set t := ‖pattersonFrequency m‖
  have hT : 8*1 ≤ 4*Real.pi*t*v := by
    have := (div_le_iff₀ hk).mp hm
    dsimp [t]
    linarith
  have hK := (hB _ hT).1
  rw [Real.norm_of_nonneg (by positivity), normalizedThetaMode, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hv.le]
  calc
    _ ≤ t ^ (1/3 : ℝ) * v * (C * Real.exp (-(4*Real.pi*t*v/2))) * t^s := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul _ hK (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (ht.norm_normalized_le _) hv.le
    _ = _ := by rw [Real.rpow_add hm₀, show -(4*Real.pi*t*v/2) = -(2*Real.pi*v)*t by ring]; ring

/-- The directional sum obtained by differentiating the normalized expansion converges absolutely. -/
theorem PattersonCoefficients.summable_normalized_horizontal {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (z u : ℂ) {v : ℝ} (hv : 0 < v) :
    Summable fun m : {m : 𝓔 // m ≠ 0} => normalizedThetaMode τ v m *
      pattersonCharacter (pattersonFrequency m * z) *
      (4 * Real.pi * Complex.I * ((pattersonFrequency m * u).re : ℂ)) := by
  have hs := ((ht.summable_normalizedThetaMode hv 1).subtype (· ≠ 0)).mul_right (4*Real.pi*‖u‖)
  apply hs.of_norm_bounded
  intro m
  dsimp only [Function.comp_apply]
  simp only [norm_mul, norm_pattersonCharacter, mul_one, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs, Real.rpow_one]
  have hRe := Complex.abs_re_le_norm (pattersonFrequency m * u)
  rw [norm_mul] at hRe
  calc
    _ ≤ ‖normalizedThetaMode τ v m‖ * (4 * Real.pi * (‖pattersonFrequency m‖ * ‖u‖)) := by gcongr
    _ = _ := by ring

theorem PattersonExpansion.hasDerivAt_normalized_horizontal {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ) (z u : ℂ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun t : ℝ => conj (θ (z + t*u) v) / 27)
      (∑' m : {m : 𝓔 // m ≠ 0}, normalizedThetaMode τ v m * pattersonCharacter (pattersonFrequency m*z) *
        (4 * Real.pi * Complex.I * ((pattersonFrequency m*u).re : ℂ))) 0 := by
  have ha : Summable fun m : PattersonIndex => ‖normalizedThetaMode τ v m‖ := by
    simpa only [Function.comp_def, Real.rpow_zero, mul_one] using
      (ht.summable_normalizedThetaMode hv 0).subtype (· ≠ 0)
  have ha₁ : Summable fun m : PattersonIndex => ‖normalizedThetaMode τ v m‖ * ‖pattersonFrequency m‖ := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (ht.summable_normalizedThetaMode hv 1).subtype (· ≠ 0)
  have H := hasDerivAt_patterson_sum _ _ ha ha₁ z u
  have H' := H.add_const ((σ / 27 : ℝ) * (v ^ (2/3 : ℝ) : ℝ) : ℂ)
  apply H'.congr_of_eventuallyEq
  filter_upwards with t
  have hsum := ((he.conj_div ht) (z+t*u) v hv).tsum_eq
  change (∑' m : PattersonIndex, normalizedThetaMode τ v m *
    pattersonCharacter (pattersonFrequency m*(z+t*u))) = _ at hsum
  rw [hsum]
  push_cast
  ring

end Masullo.QRH.MeanSquare
