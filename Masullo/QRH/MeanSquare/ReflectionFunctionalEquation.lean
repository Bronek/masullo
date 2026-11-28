import Masullo.QRH.MeanSquare.ReflectionSeries
import Masullo.QRH.MeanSquare.ReflectionDifferentiation

/-! # Completed Dirichlet series at the congruence cusps of Patterson's theta function -/

noncomputable section

open NumberField Complex MeasureTheory Set Filter Asymptotics
open scoped ComplexConjugate Topology

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev FrequencyIndex := {m : 𝓔 // m ≠ 0}
private local instance : Countable 𝓔 := by
  apply Function.Surjective.countable (f := fun p : ℤ × ℤ => (p.1 : 𝓔) + p.2 * eisOmega)
  intro m
  obtain ⟨a, b, hab⟩ := eisInteger_coordinates m
  exact ⟨(a, b), hab.symm⟩

private def orientedFrequency (barred : Bool) (μ : ℂ) : ℂ := if barred then μ else conj μ

private def cuspCoefficient (τ : ℂ → ℂ) (z μ : ℂ) : ℂ :=
  conj (τ μ) / 27 * pattersonCharacter (μ * z)

private theorem norm_cuspCoefficient (τ : ℂ → ℂ) (z μ : ℂ) :
    ‖cuspCoefficient τ z μ‖ = ‖conj (τ μ) / 27‖ := by
  simp [cuspCoefficient, pattersonCharacter, norm_exp, mul_re]

private theorem norm_orientedFrequency (barred : Bool) (μ : ℂ) :
    ‖orientedFrequency barred μ‖ = ‖μ‖ := by cases barred <;> simp [orientedFrequency]

private theorem normSq_orientedFrequency (barred : Bool) (μ : ℂ) :
    normSq (orientedFrequency barred μ) = normSq μ := by cases barred <;> simp [orientedFrequency]

private theorem index_ne_zero (m : FrequencyIndex) : pattersonFrequency m ≠ 0 := by
  apply div_ne_zero
  · exact fun hz => m.property (eisEmbedding_injective (hz.trans (map_zero _).symm))
  · exact pow_ne_zero _ (fun hz => eisLambda_prime.ne_zero (eisEmbedding_injective (hz.trans
      (map_zero _).symm)))

/-- Fourier series of the normalized Wirtinger derivative at horizontal location `z`.
The conjugate derivative carries the conjugate angular factor. -/
def pattersonHorizontalSeries (τ : ℂ → ℂ) (barred : Bool) (z : ℂ) (v : ℝ) : ℂ :=
  ∑' m : FrequencyIndex, horizontalMode (orientedFrequency barred (pattersonFrequency m))
    (cuspCoefficient τ z (pattersonFrequency m)) v

/-- Angular Dirichlet series of the corresponding translated derivative. -/
def pattersonCuspDirichlet (τ : ℂ → ℂ) (barred : Bool) (z s : ℂ) : ℂ :=
  ∑' m : FrequencyIndex, let μ := pattersonFrequency m
    cuspCoefficient τ z μ * (conj (orientedFrequency barred μ) / ‖μ‖) * (normSq μ : ℂ) ^ (-s)

/-- The completed cusp series is the Mellin integral of the theta derivative. -/
def completedPattersonCusp (τ : ℂ → ℂ) (barred : Bool) (z s : ℂ) : ℂ :=
  mellin (pattersonHorizontalSeries τ barred z) (2*s)

/-- On its half-plane of absolute convergence the completed translate has the
gamma factors of the Bessel transform and the exact scalar `i/4`. -/
theorem PattersonCoefficients.completed_eq_dirichlet {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (h : DLMFBesselMellin) (barred : Bool) (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    completedPattersonCusp τ barred z s =
      I / 4 * reflectionGammaFactor s * pattersonCuspDirichlet τ barred z s := by
  let L := fun m : FrequencyIndex => orientedFrequency barred (pattersonFrequency m)
  let A := fun m : FrequencyIndex => cuspCoefficient τ z (pattersonFrequency m)
  have hn (m : FrequencyIndex) : L m ≠ 0 := by
    cases barred <;> simp [L, orientedFrequency, index_ne_zero m]
  have H := mellin_tsum_horizontalMode (s := s) h (by linarith) L A hn
  have hsum := (ht.summable_normalized_dirichlet hs).comp_injective
    (Subtype.coe_injective (p := fun m : 𝓔 => m ≠ 0))
  apply (H ?_).trans
  · simp only [L, A, norm_orientedFrequency, normSq_orientedFrequency, pattersonCuspDirichlet]
  · apply hsum.congr
    intro m
    simp only [L, A, norm_cuspCoefficient, normSq_orientedFrequency, Function.comp_apply]

/-- The unit angular factor supplied by a cusp matrix, including its multiplier. -/
def pattersonCuspScalar (χ : 𝓔 → 𝓔 → ℂ) (a c : 𝓔) : ℂ :=
  -χ a c * (‖eisEmbedding c‖ ^ 2 : ℝ) / eisEmbedding c ^ 2

private theorem mellin_at_cusp (χ : 𝓔 → 𝓔 → ℂ) (f g : ℝ → ℂ) {a c : 𝓔} (hc : c ≠ 0)
    (hfg : ∀ v : ℝ, 0 < v → f v = -χ a c / (eisEmbedding c ^ 2 * (v : ℂ) ^ 2) *
      g ((‖eisEmbedding c‖ ^ 2*v)⁻¹)) (s : ℂ) :
    mellin f (2*s) = pattersonCuspScalar χ a c * ((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) ^ (1-2*s) *
      mellin g (2*(1-s)) := by
  have hC := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  apply mellin_cusp_reflection f g (N := ‖eisEmbedding c‖ ^ 2) (by positivity)
  intro v hv
  rw [hfg _ hv]
  have hN : ((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (pow_ne_zero _
    (norm_ne_zero_iff.mpr hC))
  unfold pattersonCuspScalar
  field_simp


private theorem mellin_entire_at_cusp {f g : ℝ → ℂ} {N : ℝ} (hN : 0 < N) (K : ℂ)
    (hc : LocallyIntegrableOn f (Ioi 0))
    (hf : ∀ p : ℝ, f =O[atTop] fun v : ℝ => v ^ p)
    (hg : ∀ p : ℝ, g =O[atTop] fun v : ℝ => v ^ p)
    (hfg : ∀ v : ℝ, 0 < v → f v = K / (v : ℂ) ^ 2 * g ((N*v)⁻¹)) :
    Differentiable ℂ (fun s : ℂ => mellin f (2*s)) ∧ ∀ s : ℂ, MellinConvergent f (2*s) := by
  have hu : Tendsto (fun v : ℝ => (N*v)⁻¹) (𝓝[>] 0) atTop := by
    simpa only [mul_inv_rev, mul_comm] using tendsto_inv_nhdsGT_zero.const_mul_atTop
      (inv_pos.mpr hN)
  have h₀ (q : ℝ) : f =O[𝓝[>] 0] fun v : ℝ => v ^ q := by
    obtain ⟨C, -, hC⟩ := (hg (-(q+2))).exists_nonneg
    refine isBigO_iff.mpr ⟨‖K‖ * C * N ^ (q+2), ?_⟩
    filter_upwards [hu.eventually hC.bound, eventually_mem_nhdsWithin] with v hvB (hv : 0 < v)
    rw [hfg v hv, norm_mul, norm_div, norm_pow, norm_real, Real.norm_of_nonneg hv.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hv.le _)]
    have hnv : 0 < N*v := mul_pos hN hv
    simp only [Real.inv_rpow hnv.le, Real.rpow_neg hnv.le, inv_inv, Real.mul_rpow hN.le
      hv.le] at hvB
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hv.le
      _))] at hvB
    calc
      _ ≤ (‖K‖ / v^2) * (C * (N ^ (q+2) * v ^ (q+2))) := mul_le_mul_of_nonneg_left hvB (by
        positivity)
      _ = _ := by rw [Real.rpow_add hv, Real.rpow_two]; field_simp
  have hd (s : ℂ) := mellin_differentiableAt_of_isBigO_rpow hc (hf (-(s.re+1)))
    (lt_add_one s.re) (h₀ (-(s.re-1))) (by linarith : s.re-1 < s.re)
  exact ⟨fun s => (hd (2*s)).comp s (by fun_prop), fun s =>
    mellinConvergent_of_isBigO_rpow hc (hf (-((2*s).re+1))) (lt_add_one (2*s).re)
      (h₀ (-((2*s).re-1))) (by linarith)⟩


private def horizontalTerm (τ : ℂ → ℂ) (barred : Bool) (z : ℂ) (m : FrequencyIndex) (v : ℝ) : ℂ :=
  horizontalMode (orientedFrequency barred (pattersonFrequency m)) (cuspCoefficient τ z
    (pattersonFrequency m)) v

private theorem horizontal_majorant {τ : ℂ → ℂ} (ht : PattersonCoefficients τ) (barred : Bool) (z
    : ℂ)
    (hK : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, δ ≤ x →
      ‖besselK (1/3) x‖ ≤ C * Real.exp (-(x/2))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℝ, 0 < b ∧ ∃ g : FrequencyIndex → ℝ, Summable g ∧ (∀ m, 0 ≤ g m) ∧
      ∀ m v, δ ≤ v → ‖horizontalTerm τ barred z m v‖ ≤ g m * (v * Real.exp (-b*v)) := by
  let R := ‖eisEmbedding eisLambda ^ 3‖
  have hl : eisEmbedding eisLambda ≠ 0 :=
    fun hz => eisLambda_prime.ne_zero (eisEmbedding_injective (hz.trans (map_zero _).symm))
  have hR : 0 < R := norm_pos_iff.mpr (pow_ne_zero _ hl)
  let b := Real.pi * R⁻¹
  have hb : 0 < b := mul_pos Real.pi_pos (inv_pos.mpr hR)
  obtain ⟨C, hC, hK⟩ := hK (4*b*δ) (by positivity)
  let g := fun m : FrequencyIndex => (2*Real.pi*C) *
    (‖pattersonFrequency m‖ ^ (1/3+1 : ℝ) * Real.exp (-(Real.pi*δ)*‖pattersonFrequency m‖))
  have hsum := ((summable_pattersonFrequency_rpow_exp (1/3+1)
    (mul_pos Real.pi_pos hδ)).subtype (· ≠ 0)).mul_left (2*Real.pi*C)
  refine ⟨b, hb, g, hsum, fun m => by dsimp [g]; positivity, ?_⟩
  intro m v hv
  let t := ‖pattersonFrequency m‖
  have ht₀ : 0 < t := norm_pos_iff.mpr (index_ne_zero m)
  have hgap : R⁻¹ ≤ t := by
    change R⁻¹ ≤ ‖eisEmbedding m / eisEmbedding eisLambda ^ 3‖
    rw [norm_div, ← one_div]
    exact div_le_div_of_nonneg_right (one_le_norm_eisEmbedding m.property) hR.le
  have hb' : b ≤ Real.pi * t := mul_le_mul_of_nonneg_left hgap Real.pi_pos.le
  have harg : 4*b*δ ≤ 4*Real.pi*t*v := by
    rw [show 4*Real.pi*t*v = 4*(Real.pi*t)*v by ring]
    gcongr
  have hv₀ := hδ.trans_le hv
  have hexp : Real.exp (-(4*Real.pi*t*v/2)) ≤
      Real.exp (-(Real.pi*δ)*t) * Real.exp (-b*v) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hb' hv₀.le,
      mul_le_mul_of_nonneg_left hv (mul_pos Real.pi_pos ht₀).le]
  have hkn := (hK _ harg).trans (mul_le_mul_of_nonneg_left hexp hC)
  simp only [horizontalTerm, horizontalMode, norm_mul, norm_I, norm_conj, norm_cuspCoefficient,
    norm_orientedFrequency, Complex.norm_real, Real.norm_of_nonneg hv₀.le,
    Real.norm_of_nonneg Real.pi_pos.le, norm_ofNat, mul_one]
  change 2*Real.pi*t*‖conj (τ (pattersonFrequency m))/27‖ * (v * ‖besselK (1/3)
    (4*Real.pi*t*v)‖) ≤ _
  calc
    _ ≤ 2*Real.pi*t*t^(1/3:ℝ) * (v * (C * (Real.exp (-(Real.pi*δ)*t) * Real.exp (-b*v)))) := by
      gcongr
      exact ht.norm_normalized_le _
    _ = _ := by dsimp only [g]; rw [Real.rpow_add ht₀, Real.rpow_one]; dsimp [t]; ring

private theorem horizontalSeries_analytic {τ : ℂ → ℂ} (ht : PattersonCoefficients τ) (barred :
    Bool) (z : ℂ)
    (hK : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, δ ≤ x →
      ‖besselK (1/3) x‖ ≤ C * Real.exp (-(x/2)))
    (hcont : ∀ x : ℝ, 0 < x → ContinuousAt (besselK (1/3)) x) :
    LocallyIntegrableOn (pattersonHorizontalSeries τ barred z) (Ioi 0) ∧
      ∀ p : ℝ, pattersonHorizontalSeries τ barred z =O[atTop] fun v : ℝ => v ^ p := by
  refine ⟨ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi, ?_⟩
  · intro v (hv : 0 < v)
    obtain ⟨b, hb, g, hg, hpos, hB⟩ := horizontal_majorant ht barred z hK (δ := v/2) (by positivity)
    let U := Ioo (v/2) (2*v)
    have hvU : v ∈ U := ⟨by linarith, by linarith⟩
    have hc : ContinuousOn (pattersonHorizontalSeries τ barred z) U := by
      apply continuousOn_tsum (f := horizontalTerm τ barred z) (u := fun m => g m * (2*v))
      · intro m u hu
        have hu₀ : 0 < u := by linarith [hu.1]
        have ht₀ := norm_pos_iff.mpr (index_ne_zero m)
        have hf := hcont (4*Real.pi*‖pattersonFrequency m‖*u) (by positivity)
        change ContinuousWithinAt (fun w : ℝ => _ * ((w : ℂ) * besselK (1/3)
          (4*Real.pi*‖orientedFrequency barred (pattersonFrequency m)‖*w))) U u
        rw [norm_orientedFrequency]
        exact (ContinuousAt.const_mul ((continuous_ofReal.continuousAt).mul
          (hf.comp (by fun_prop))) _).continuousWithinAt
      · exact hg.mul_right _
      · intro m u hu
        apply (hB m u hu.1.le).trans
        have hu₀ : 0 ≤ u := by linarith [hu.1]
        have he := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le)
          hu₀)
        exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right hu₀ he).trans hu.2.le) (hpos m)
    exact ((hc v hvU).continuousAt (isOpen_Ioo.mem_nhds hvU)).continuousWithinAt
  · intro p
    obtain ⟨b, hb, g, hg, hpos, hB⟩ := horizontal_majorant ht barred z hK (δ := 1) zero_lt_one
    have hres : pattersonHorizontalSeries τ barred z =O[atTop] fun v : ℝ => v * Real.exp (-b*v)
      := by
      refine isBigO_iff.mpr ⟨∑' m, g m, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with v hv
      have hv₀ : 0 ≤ v := by linarith
      rw [Real.norm_of_nonneg (mul_nonneg hv₀ (Real.exp_pos _).le), ← tsum_mul_right]
      have hbnd := hg.mul_right (v * Real.exp (-b*v))
      have hsum := Summable.of_nonneg_of_le (fun m => norm_nonneg (horizontalTerm τ barred z m v))
        (fun m => hB m v hv) hbnd
      exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum (fun m => hB m v hv) hbnd)
    apply hres.trans
    have he := (isLittleO_exp_neg_mul_rpow_atTop hb (p-1)).isBigO
    have hv : (fun v : ℝ => v) =O[atTop] fun v : ℝ => v ^ (1:ℝ) := by simp [isBigO_refl]
    refine (hv.mul he).congr' (.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_gt_atTop 0] with v hv₀
    rw [← Real.rpow_add hv₀, show 1+(p-1) = p by ring]


private def horizontalSlope (θ : ℂ → ℝ → ℂ) (z : ℂ) (v : ℝ) (u : ℂ) : ℂ :=
  deriv (fun t : ℝ => conj (θ (z + t*u) v) / 27) 0

private theorem horizontalSeries_eq_slope {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ) (barred : Bool) (z : ℂ)
    {v : ℝ} (hv : 0 < v) : pattersonHorizontalSeries τ barred z v =
      (horizontalSlope θ z v 1 + (if barred then I else -I) * horizontalSlope θ z v I) / 2 := by
  let D := fun (u : ℂ) (m : FrequencyIndex) => normalizedThetaMode τ v m *
    pattersonCharacter (pattersonFrequency m*z) * (4*Real.pi*I*((pattersonFrequency m*u).re : ℂ))
  have h (u : ℂ) : HasSum (D u) (horizontalSlope θ z v u) := by
    rw [horizontalSlope, (he.hasDerivAt_normalized_horizontal ht z u hv).deriv]
    exact (ht.summable_normalized_horizontal z u hv).hasSum
  refine (tsum_congr fun m => ?_).trans (((h 1).add ((h I).mul_left (if barred then I else
    -I))).div_const 2).tsum_eq
  change horizontalTerm τ barred z m v = _
  let μ := pattersonFrequency m
  have hc : conj μ = (μ.re : ℂ) - μ.im*I := by apply Complex.ext <;> simp
  have hu : μ = (μ.re : ℂ) + μ.im*I := (Complex.re_add_im _).symm
  simp only [horizontalTerm, horizontalMode, norm_orientedFrequency, cuspCoefficient,
    D, normalizedThetaMode, mul_one, mul_I_re, ofReal_neg]
  change 2*Real.pi*I*conj (orientedFrequency barred μ)*_ * _ =
    (_ * (4*Real.pi*I*(μ.re : ℂ)) + _ * (_ * (4*Real.pi*I*(-(μ.im : ℂ))))) / 2
  cases barred
  · simp only [Bool.false_eq_true, ite_false, orientedFrequency, conj_conj]
    conv_lhs => arg 1; arg 1; arg 2; rw [hu]
    ring
  · simp only [ite_true, orientedFrequency, hc]
    ring

/-- The normalized theta derivative at a congruence cusp is the opposite
angular derivative at the reciprocal height, with Patterson's conjugate multiplier. -/
theorem PattersonExpansion.horizontalSeries_at_cusp {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    {χ : 𝓔 → 𝓔 → ℂ} (hχ : PattersonAutomorphyWith χ θ) {a b c d : 𝓔}
    (hdet : a*d-b*c=1) (ha : eisPrimary a) (hb : (3:𝓔) ∣ b)
    (hc₃ : (3:𝓔) ∣ c) (hd : eisPrimary d) (hc : c ≠ 0) {v : ℝ} (hv : 0 < v) :
    pattersonHorizontalSeries τ true (eisEmbedding a / eisEmbedding c) v =
      -conj (χ a c) / (eisEmbedding c ^ 2 * (v : ℂ) ^ 2) *
        pattersonHorizontalSeries τ false (-eisEmbedding d / eisEmbedding c)
          ((‖eisEmbedding c‖^2 * v)⁻¹) := by
  let z := -eisEmbedding d / eisEmbedding c
  let w := (‖eisEmbedding c‖^2 * v)⁻¹
  let Θ := fun (p : ℂ × ℝ) => conj (θ p.1 p.2) / 27
  have hc' := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  have hw : 0 < w := by dsimp [w]; positivity
  have H : DifferentiableAt ℝ Θ (z,w) := by
    change DifferentiableAt ℝ (fun p : ℂ × ℝ => conj ((Function.uncurry θ) p) / (27:ℂ)) (z,w)
    simp only [div_eq_mul_inv]
    apply DifferentiableAt.mul_const
    exact Complex.differentiable_conj.differentiableAt.comp _ (he.differentiableAt_uncurry ht z hw)
  let L := fderiv ℝ Θ (z,w)
  have hL : HasFDerivAt Θ L (z,w) := H.hasFDerivAt
  have hs (u : ℂ) : horizontalSlope θ z w u = L (u,0) := by
    let P := fun t : ℝ => (z + t*u,w)
    have hP : HasDerivAt P (u,0) 0 := by
      convert (((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const u).const_add z).prodMk
        (hasDerivAt_const (0:ℝ) w) using 1 <;> simp [P]
    have h₀ : P 0 = (z,w) := by simp [P]
    have hL' : HasFDerivAt Θ L (P 0) := h₀ ▸ hL
    exact (hL'.comp_hasDerivAt 0 hP).deriv
  have h := (hχ.conj_div 27).horizontalBarDeriv_at_cusp hdet ha hb hc₃ hd hc hv hL
  rw [horizontalSeries_eq_slope he ht true _ hv, horizontalSeries_eq_slope he ht false _ hw]
  change _ = _ * ((horizontalSlope θ z w 1 + -I * horizontalSlope θ z w I) / 2)
  rw [hs 1, hs I, neg_mul, ← sub_eq_add_neg]
  exact h

/-- Functional equation of the translated, completed angular Dirichlet series. -/
theorem PattersonExpansion.completed_functionalEquation {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    {χ : 𝓔 → 𝓔 → ℂ} (hχ : PattersonAutomorphyWith χ θ) {a b c d : 𝓔}
    (hdet : a*d-b*c=1) (ha : eisPrimary a) (hb : (3:𝓔) ∣ b)
    (hc₃ : (3:𝓔) ∣ c) (hd : eisPrimary d) (hc : c ≠ 0) (s : ℂ) :
    completedPattersonCusp τ true (eisEmbedding a / eisEmbedding c) s =
      pattersonCuspScalar (fun a c => conj (χ a c)) a c *
        ((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) ^ (1-2*s) *
        completedPattersonCusp τ false (-eisEmbedding d / eisEmbedding c) (1-s) :=
  mellin_at_cusp (fun a c => conj (χ a c))
    (pattersonHorizontalSeries τ true (eisEmbedding a / eisEmbedding c))
    (pattersonHorizontalSeries τ false (-eisEmbedding d / eisEmbedding c)) (a := a) hc
    (fun _ hv => he.horizontalSeries_at_cusp ht hχ hdet ha hb hc₃ hd hc hv) s

/-- The completed translate is entire and its defining Mellin integral converges everywhere. -/
theorem PattersonExpansion.completed_entire {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    {χ : 𝓔 → 𝓔 → ℂ} (hχ : PattersonAutomorphyWith χ θ) {a b c d : 𝓔}
    (hdet : a*d-b*c=1) (ha : eisPrimary a) (hb : (3:𝓔) ∣ b)
    (hc₃ : (3:𝓔) ∣ c) (hd : eisPrimary d) (hc : c ≠ 0) :
    Differentiable ℂ (completedPattersonCusp τ true (eisEmbedding a / eisEmbedding c)) ∧
      ∀ s : ℂ, MellinConvergent
        (pattersonHorizontalSeries τ true (eisEmbedding a / eisEmbedding c)) (2*s) := by
  have hK (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, δ ≤ x →
      ‖besselK (1/3) x‖ ≤ C * Real.exp (-(x/2)) := by
    obtain ⟨C, hC, hB⟩ := exists_besselK_oneThird_bound (δ := δ/8) (by positivity)
    exact ⟨C, hC, fun x hx => (hB x (by linarith)).1⟩
  have hseries (b : Bool) (z : ℂ) := horizontalSeries_analytic ht b z hK
    (fun _ hx => (differentiableAt_besselK_oneThird hx).continuousAt)
  have hC := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  exact mellin_entire_at_cusp (N := ‖eisEmbedding c‖ ^ 2) (by positivity)
    (-conj (χ a c) / eisEmbedding c ^ 2) (hseries true _).1 (hseries true _).2 (hseries false _).2
    (fun v hv => by rw [he.horizontalSeries_at_cusp ht hχ hdet ha hb hc₃ hd hc hv]; ring)


/-- The continuation of the angular Dirichlet series, with the two reciprocal
gamma factors evaluated by their entire extensions. -/
def continuedPattersonDirichlet (τ : ℂ → ℂ) (barred : Bool) (z s : ℂ) : ℂ :=
  (4 / I) * completedPattersonCusp τ barred z s * (reflectionGammaFactor s)⁻¹

private theorem differentiable_inv_reflectionGammaFactor :
    Differentiable ℂ (fun s => (reflectionGammaFactor s)⁻¹) := by
  let a : ℂ := ((2*Real.pi : ℝ) : ℂ)
  have ha : a ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hpow : Differentiable ℂ (fun s : ℂ => (a ^ (-2*s))⁻¹) :=
    ((by fun_prop : Differentiable ℂ (fun s : ℂ => -2*s)).const_cpow (Or.inl ha)).inv
      (fun _ hh => ha ((cpow_eq_zero_iff _ _).mp hh).1)
  have hG (c : ℂ) : Differentiable ℂ (fun s : ℂ => (Gamma (s+c))⁻¹) :=
    differentiable_one_div_Gamma.comp (differentiable_id.add_const c)
  convert (hG (2/3)).mul ((hG (1/3)).mul hpow) using 1
  ext s
  simp only [reflectionGammaFactor, mul_inv_rev, Pi.mul_apply, a]

theorem PattersonCoefficients.continued_eq_dirichlet {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (h : DLMFBesselMellin) (barred : Bool) (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    continuedPattersonDirichlet τ barred z s = pattersonCuspDirichlet τ barred z s := by
  have hne : reflectionGammaFactor s ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro hz
        exact (ofReal_ne_zero.mpr (by positivity : 2*Real.pi ≠ 0)) ((cpow_eq_zero_iff _ _).mp hz).1
      · apply Gamma_ne_zero_of_re_pos
        simp only [add_re, div_ofNat_re, one_re]
        linarith
    · apply Gamma_ne_zero_of_re_pos
      norm_num [add_re, div_ofNat_re]
      linarith
  rw [continuedPattersonDirichlet, ht.completed_eq_dirichlet h barred z hs]
  field_simp

/-- At a congruence cusp the uncompleted Dirichlet series has an entire continuation. -/
theorem PattersonExpansion.continued_entire {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    {χ : 𝓔 → 𝓔 → ℂ} (hχ : PattersonAutomorphyWith χ θ) {a b c d : 𝓔}
    (hdet : a*d-b*c=1) (ha : eisPrimary a) (hb : (3:𝓔) ∣ b)
    (hc₃ : (3:𝓔) ∣ c) (hd : eisPrimary d) (hc : c ≠ 0) :
    Differentiable ℂ (continuedPattersonDirichlet τ true (eisEmbedding a / eisEmbedding c)) := by
  have h := (he.completed_entire ht hχ hdet ha hb hc₃ hd hc).1
  exact (h.const_mul (4/I)).mul differentiable_inv_reflectionGammaFactor

/-- In the left half-plane the reflected series converges absolutely and
carries the gamma quotient, the conductor power, and the angular cusp scalar. -/
theorem PattersonExpansion.continued_eq_dual {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    {χ : 𝓔 → 𝓔 → ℂ} (hχ : PattersonAutomorphyWith χ θ) (hB : DLMFBesselMellin)
    {a b c d : 𝓔} (hdet : a*d-b*c=1) (ha : eisPrimary a) (hb : (3:𝓔) ∣ b)
    (hc₃ : (3:𝓔) ∣ c) (hd : eisPrimary d) (hc : c ≠ 0) {s : ℂ} (hs : s.re < 0) :
    continuedPattersonDirichlet τ true (eisEmbedding a / eisEmbedding c) s =
      pattersonCuspScalar (fun a c => conj (χ a c)) a c *
        ((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) ^ (1-2*s) *
        (reflectionGammaFactor (1-s) / reflectionGammaFactor s) *
        pattersonCuspDirichlet τ false (-eisEmbedding d / eisEmbedding c) (1-s) := by
  have hs' : 1 < (1-s).re := by rw [sub_re, one_re]; linarith
  rw [continuedPattersonDirichlet, he.completed_functionalEquation ht hχ hdet ha hb hc₃ hd hc,
    ht.completed_eq_dirichlet hB false _ hs']
  ring_nf
  rw [mul_inv_cancel₀ I_ne_zero, one_mul]


/-- After centering at one half, the archimedean ratio is the contour
gamma quotient times the dilation factor `(2π)^(-4t)`. -/
theorem reflectionGammaFactor_centered_ratio (t : ℂ) :
    reflectionGammaFactor (1/2+t) / reflectionGammaFactor (1/2-t) =
      ((2*Real.pi : ℝ) : ℂ) ^ (-4*t) * reflectionGammaRatio t := by
  let p : ℂ := ((2*Real.pi : ℝ) : ℂ)
  have hp : p ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hx : p ^ (-2*(1/2+t)) / p ^ (-2*(1/2-t)) = p ^ (-4*t) := by
    rw [← cpow_sub _ _ hp]
    congr 1
    ring
  unfold reflectionGammaFactor reflectionGammaRatio
  rw [show 1/2+t+1/3 = 5/6+t by ring, show 1/2+t+2/3 = 7/6+t by ring,
    show 1/2-t+1/3 = 5/6-t by ring, show 1/2-t+2/3 = 7/6-t by ring]
  rw [← hx]
  simp only [div_eq_mul_inv, mul_inv_rev, p]
  ring

/-- The scalar at the normalized Patterson cusp has modulus one. -/
theorem norm_pattersonCuspScalar {a b c d : 𝓔} (hdet : a*d-b*c=1)
    (ha : eisPrimary a) (hc : c ≠ 0) :
    ‖pattersonCuspScalar (fun a c => conj (pattersonMultiplier a c)) a c‖ = 1 := by
  classical
  have hab : IsCoprime a c := ⟨d, -b, by linear_combination hdet⟩
  let n := Ideal.span {a}
  have hn : n ≠ ⊥ := by simpa [n] using ha.ne_zero
  let := Ring.HasFiniteQuotients.finiteQuotient hn
  let := Fintype.ofFinite (𝓔 ⧸ n)
  let χ := cubicChar hn ha.coprime_three
  have hu : IsUnit (Ideal.Quotient.mk n c) := (isUnit_mk_iff_coprime_span n c).mpr
    ((Ideal.isCoprime_span_singleton_iff a c).mpr hab)
  have hχ : ‖χ hu.unit‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity
    hu.unit)
  have hmult : ‖pattersonMultiplier a c‖ = 1 := by
    simpa only [χ, hu.unit_spec, cubicChar_mk, pattersonMultiplier, ite_eq_right hc,
      cubicSymbol] using hχ
  have hC := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  simp [pattersonCuspScalar, hmult, norm_pow, hC]


theorem PattersonExpansion.norm_completed_on_strip {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    {χ : 𝓔 → 𝓔 → ℂ} (hχ : PattersonAutomorphyWith χ θ) {a b c d : 𝓔}
    (hdet : a*d-b*c=1) (ha : eisPrimary a) (hb : (3:𝓔) ∣ b)
    (hc₃ : (3:𝓔) ∣ c) (hd : eisPrimary d) (hc : c ≠ 0) (u v : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc u v →
      ‖completedPattersonCusp τ true (eisEmbedding a / eisEmbedding c) s‖ ≤ C := by
  have h := (he.completed_entire ht hχ hdet ha hb hc₃ hd hc).2
  obtain ⟨C, hC⟩ := norm_mellin_le_on_strip (a := 2*u) (b := 2*v)
    (by simpa only [ofReal_mul, ofReal_ofNat] using h u)
    (by simpa only [ofReal_mul, ofReal_ofNat] using h v)
  refine ⟨C, fun s hs => hC (2*s) ?_⟩
  simpa only [two_mul, add_re, mem_Icc] using
    And.intro (add_le_add hs.1 hs.1) (add_le_add hs.2 hs.2)

/-- Patterson's theorem supplies one coefficient function whose translated Dirichlet
series continue to entire functions and satisfy the reflected formula at every cusp. -/
theorem PattersonTheorem81.exists_cusp_continuation (h : PattersonTheorem81) (hB :
    DLMFBesselMellin) :
    ∃ τ : ℂ → ℂ, PattersonCoefficients τ ∧ ∀ a b c d : 𝓔,
      a*d-b*c=1 → eisPrimary a → (3:𝓔) ∣ b → (3:𝓔) ∣ c → eisPrimary d → c ≠ 0 →
      let z := eisEmbedding a / eisEmbedding c
      let z' := -eisEmbedding d / eisEmbedding c
      let η := pattersonCuspScalar (fun a c => conj (pattersonMultiplier a c)) a c
      ‖η‖ = 1 ∧ Differentiable ℂ (continuedPattersonDirichlet τ true z) ∧
        (∀ s : ℂ, 1 < s.re → continuedPattersonDirichlet τ true z s = pattersonCuspDirichlet τ true
          z s) ∧
        ∀ s : ℂ, s.re < 0 → continuedPattersonDirichlet τ true z s =
          η * ((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) ^ (1-2*s) *
            (reflectionGammaFactor (1-s) / reflectionGammaFactor s) * pattersonCuspDirichlet τ false
              z' (1-s) := by
  obtain ⟨σ, τ, θ, -, ht, he, hχ⟩ := h
  refine ⟨τ, ht, ?_⟩
  intro a b c d hdet ha hb hc₃ hd hc
  exact ⟨norm_pattersonCuspScalar hdet ha hc, he.continued_entire ht hχ hdet ha hb hc₃ hd hc,
    fun _ hs => ht.continued_eq_dirichlet hB true _ hs,
    fun _ hs => he.continued_eq_dual ht hχ hB hdet ha hb hc₃ hd hc hs⟩

end Masullo.QRH.MeanSquare
