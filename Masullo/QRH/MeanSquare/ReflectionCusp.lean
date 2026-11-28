import Masullo.QRH.MeanSquare.GaussPhase
import Masullo.QRH.MeanSquare.Primary
import Masullo.QRH.MeanSquare.Theta

/-! # Centered coordinates at the surviving cusps of Patterson's series -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- Complete a reduced fraction with primary numerator and denominator divisible by
three to a cusp matrix in the principal congruence group. -/
theorem exists_patterson_cusp_matrix {a c : 𝓔} (hac : IsCoprime a c)
    (ha : eisPrimary a) (hc : (3 : 𝓔) ∣ c) :
    ∃ b d : 𝓔, a * d - b * c = 1 ∧ (3 : 𝓔) ∣ b ∧ eisPrimary d := by
  have ha3 := hac.of_isCoprime_of_dvd_right hc
  obtain ⟨d, t, he⟩ := ha3.mul_right hac
  have hd : a * d - (-3 * t) * c = 1 := by linear_combination he
  refine ⟨-3 * t, d, hd, ⟨-t, by ring⟩, ?_⟩
  rw [eisPrimary_iff_mk_eq_one]
  have h := congrArg (Ideal.Quotient.mk (span {(3 : 𝓔)})) he
  have h3 : Ideal.Quotient.mk (span {(3 : 𝓔)}) 3 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (subset_span (by simp))
  simpa only [map_add, map_mul, map_one, h3, zero_mul, mul_zero, add_zero,
    (eisPrimary_iff_mk_eq_one _).mp ha, mul_one] using h

/-- Horizontal and vertical coordinates of a determinant-one matrix applied
at horizontal displacement `z` from its pole. -/
theorem patterson_cusp_coordinates {a b c d : ℂ} (hdet : a * d - b * c = 1)
    (hc : c ≠ 0) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    let w := z - d / c
    let den := ‖c * w + d‖ ^ 2 + ‖c‖ ^ 2 * v ^ 2
    ((a * w + b) * conj (c * w + d) + a * conj c * v ^ 2) / den =
      a / c - conj z / (c ^ 2 * (v ^ 2 + (‖z‖ : ℂ) ^ 2)) ∧
    v / den = v / (‖c‖ ^ 2 * (v ^ 2 + ‖z‖ ^ 2)) := by
  dsimp only
  have hcz : c * (z - d / c) + d = c * z := by field_simp; ring
  rw [hcz, norm_mul, mul_pow, map_mul]
  have hr : 0 < v ^ 2 + ‖z‖ ^ 2 := by positivity
  have hr' : (v : ℂ) ^ 2 + (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hr.ne'
  have hc' : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hc)
  have hden : ‖c‖ ^ 2 * ‖z‖ ^ 2 + ‖c‖ ^ 2 * v ^ 2 = ‖c‖ ^ 2 * (v ^ 2 + ‖z‖ ^ 2) := by ring
  rw [hden]
  refine ⟨?_, rfl⟩
  push_cast
  field_simp [hr', hc']
  rw [← Complex.mul_conj' z, ← Complex.mul_conj' c]
  linear_combination -c * conj c * conj z * hdet

/-- The horizontal cusp displacement under inversion. -/
def cuspOffset (c z : ℂ) (v : ℝ) : ℂ := -conj z / (c ^ 2 * ((v ^ 2 + ‖z‖ ^ 2 : ℝ) : ℂ))

/-- The corresponding height under inversion. -/
def cuspHeight (c z : ℂ) (v : ℝ) : ℝ := v / (‖c‖ ^ 2 * (v ^ 2 + ‖z‖ ^ 2))

private theorem cusp_radius_inv {c : ℂ} (hc : c ≠ 0) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    cuspHeight c z v ^ 2 + ‖cuspOffset c z v‖ ^ 2 =
      (‖c‖ ^ 4 * (v ^ 2 + ‖z‖ ^ 2))⁻¹ := by
  have hR : 0 < v ^ 2 + ‖z‖ ^ 2 := by positivity
  have hC := norm_ne_zero_iff.mpr hc
  simp only [cuspHeight, cuspOffset, norm_div, norm_neg, Complex.norm_conj, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  field_simp

private theorem cusp_involutive {c : ℂ} (hc : c ≠ 0) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    cuspOffset c (cuspOffset c z v) (cuspHeight c z v) = z ∧
      cuspHeight c (cuspOffset c z v) (cuspHeight c z v) = v := by
  have hR : 0 < v ^ 2 + ‖z‖ ^ 2 := by positivity
  have hC := norm_ne_zero_iff.mpr hc
  have hC' : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hC
  have hR' : ((v ^ 2 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  constructor
  · rw [cuspOffset, cusp_radius_inv hc z hv]
    simp only [cuspOffset, map_div₀, map_neg, Complex.conj_conj, map_mul, map_pow,
      Complex.conj_ofReal, neg_neg, neg_div, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_pow]
    have hcn : conj c ≠ 0 := by simpa using hc
    field_simp
    linear_combination z * ((‖c‖ : ℂ) ^ 2 + c * conj c) * (Complex.mul_conj' c).symm
  · rw [cuspHeight, cusp_radius_inv hc z hv, cuspHeight]
    field_simp

/-- The automorphy equation in the coordinates centered at `a/c`. -/
theorem PattersonAutomorphyWith.at_cusp {χ : 𝓔 → 𝓔 → ℂ} {θ : ℂ → ℝ → ℂ}
    (h : PattersonAutomorphyWith χ θ) {a b c d : 𝓔} (hdet : a * d - b * c = 1)
    (ha : eisPrimary a) (hb : (3 : 𝓔) ∣ b) (hc₃ : (3 : 𝓔) ∣ c) (hd : eisPrimary d)
    (hc : c ≠ 0) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    θ (eisEmbedding a / eisEmbedding c + z) v =
      χ a c * θ (cuspOffset (eisEmbedding c) z v - eisEmbedding d / eisEmbedding c)
        (cuspHeight (eisEmbedding c) z v) := by
  have hC := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  have hD : eisEmbedding a * eisEmbedding d - eisEmbedding b * eisEmbedding c = 1 := by
    simpa only [map_sub, map_mul, map_one] using congrArg eisEmbedding hdet
  let u := cuspOffset (eisEmbedding c) z v
  let t := cuspHeight (eisEmbedding c) z v
  have ht : 0 < t := by dsimp [t, cuspHeight]; positivity
  have hm := h a b c d hdet ha hb hc₃ hd (u - eisEmbedding d / eisEmbedding c) t ht
  have he := patterson_cusp_coordinates hD hC u ht
  dsimp only at he hm
  rw [he.1, he.2] at hm
  change θ (eisEmbedding a / eisEmbedding c - _) (cuspHeight (eisEmbedding c) u t) = _ at hm
  have hi := cusp_involutive hC z hv
  change cuspOffset (eisEmbedding c) u t = z ∧ cuspHeight (eisEmbedding c) u t = v at hi
  rw [hi.2] at hm
  convert hm using 3
  rw [← hi.1]
  simp only [cuspOffset, Complex.ofReal_add, Complex.ofReal_pow, neg_div, sub_eq_add_neg]

/-- At the cusp center the horizontal tangent is antilinear and the height
derivative vanishes in every horizontal direction. -/
theorem hasDerivAt_cusp_path {c : ℂ} (hc : c ≠ 0) {v : ℝ} (hv : 0 < v) (u : ℂ) :
    HasDerivAt (fun t : ℝ => cuspOffset c (t * u) v) (-conj u / (c ^ 2 * v ^ 2)) 0 ∧
    HasDerivAt (fun t : ℝ => cuspHeight c (t * u) v) 0 0 := by
  have hrad : HasDerivAt (fun t : ℝ => v ^ 2 + ‖(t : ℂ) * u‖ ^ 2) 0 0 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simpa using (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖u‖ ^ 2)).const_add (v ^ 2)
  have hR : (v ^ 2 + ‖((0 : ℝ) : ℂ) * u‖ ^ 2 : ℝ) ≠ 0 := by simpa using hv.ne'
  have hcR : (c ^ 2 * ((v ^ 2 + ‖((0 : ℝ) : ℂ) * u‖ ^ 2 : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc) (Complex.ofReal_ne_zero.mpr hR)
  constructor
  · simp only [cuspOffset, map_mul, Complex.conj_ofReal]
    have hn := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (conj u)).neg
    convert hn.div
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ hrad).const_mul (c ^ 2)) hcR using 1
    · rfl
    · simp
      field_simp
  · have hn := (hasDerivAt_const (0 : ℝ) v).div (hrad.const_mul (‖c‖ ^ 2))
      (mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hc)) hR)
    convert hn using 1
    · rfl
    · simp

/-- Directional derivative of the theta translate expressed at the reflected
point. The real derivative of the height contributes zero. -/
theorem PattersonAutomorphyWith.hasDerivAt_at_cusp {χ : 𝓔 → 𝓔 → ℂ} {θ : ℂ → ℝ → ℂ}
    (h : PattersonAutomorphyWith χ θ) {a b c d : 𝓔} (hdet : a * d - b * c = 1)
    (ha : eisPrimary a) (hb : (3 : 𝓔) ∣ b) (hc₃ : (3 : 𝓔) ∣ c) (hd : eisPrimary d)
    (hc : c ≠ 0) {v : ℝ} (hv : 0 < v) (u : ℂ) {L : ℂ × ℝ →L[ℝ] ℂ}
    (hL : HasFDerivAt (Function.uncurry θ) L
      (-eisEmbedding d / eisEmbedding c, (‖eisEmbedding c‖ ^ 2 * v)⁻¹)) :
    HasDerivAt (fun t : ℝ => θ (eisEmbedding a / eisEmbedding c + t * u) v)
      (χ a c * L (-conj u / (eisEmbedding c ^ 2 * v ^ 2), 0)) 0 := by
  let C := eisEmbedding c
  let D := eisEmbedding d
  have hC : C ≠ 0 := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  let path (t : ℝ) := (cuspOffset C (t * u) v - D / C, cuspHeight C (t * u) v)
  have h₀ : path 0 = (-D / C, (‖C‖ ^ 2 * v)⁻¹) := by
    simp [path, cuspOffset, cuspHeight, hv.ne', pow_two, mul_inv_rev, div_eq_mul_inv,
      mul_assoc]
  obtain ⟨hz, ht⟩ := hasDerivAt_cusp_path hC hv u
  have hp := (hz.sub_const (D / C)).prodMk ht
  have hL' : HasFDerivAt (Function.uncurry θ) L (path 0) := h₀ ▸ hL
  have hh := (hL'.comp_hasDerivAt 0 hp).const_mul (χ a c)
  simpa only [Function.comp_apply, path, Function.uncurry_apply_pair,
    h.at_cusp hdet ha hb hc₃ hd hc _ hv] using hh

/-- Wirtinger's horizontal derivative at fixed height. -/
def horizontalBarDeriv (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (deriv (fun t : ℝ => F (z + t * 1)) 0 +
    Complex.I * deriv (fun t : ℝ => F (z + t * Complex.I)) 0) / 2

private theorem horizontal_linear (L : ℂ × ℝ →L[ℝ] ℂ) (q : ℂ) :
    L (q, 0) + Complex.I * L (-Complex.I * q, 0) =
      q * (L (1, 0) - Complex.I * L (Complex.I, 0)) := by
  have split (z : ℂ) : L (z, 0) =
      z.re * L (1, 0) + z.im * L (Complex.I, 0) := by
    have hz : (z, (0 : ℝ)) = z.re • ((1 : ℂ), (0 : ℝ)) + z.im • (Complex.I, (0 : ℝ)) := by
      ext <;> simp [Complex.real_smul]
    rw [hz, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [split q, split (-Complex.I * q)]
  simp only [neg_mul, Complex.neg_re, Complex.neg_im, Complex.I_mul_re, Complex.I_mul_im, neg_neg,
    Complex.ofReal_neg]
  conv_rhs => rw [← Complex.re_add_im q]
  linear_combination q.im * L (Complex.I, 0) * (Complex.I_mul_I)

/-- The horizontal derivative at a surviving translate is the opposite
Wirtinger derivative at the reciprocal height, multiplied by the cusp Jacobian. -/
theorem PattersonAutomorphyWith.horizontalBarDeriv_at_cusp {χ : 𝓔 → 𝓔 → ℂ} {θ : ℂ → ℝ → ℂ}
    (h : PattersonAutomorphyWith χ θ) {a b c d : 𝓔} (hdet : a * d - b * c = 1)
    (ha : eisPrimary a) (hb : (3 : 𝓔) ∣ b) (hc₃ : (3 : 𝓔) ∣ c) (hd : eisPrimary d)
    (hc : c ≠ 0) {v : ℝ} (hv : 0 < v) {L : ℂ × ℝ →L[ℝ] ℂ}
    (hL : HasFDerivAt (Function.uncurry θ) L
      (-eisEmbedding d / eisEmbedding c, (‖eisEmbedding c‖ ^ 2 * v)⁻¹)) :
    horizontalBarDeriv (fun z => θ z v) (eisEmbedding a / eisEmbedding c) =
      -χ a c / (eisEmbedding c ^ 2 * v ^ 2) *
        ((L (1, 0) - Complex.I * L (Complex.I, 0)) / 2) := by
  let q : ℂ := -1 / (eisEmbedding c ^ 2 * v ^ 2)
  rw [horizontalBarDeriv,
    (h.hasDerivAt_at_cusp hdet ha hb hc₃ hd hc hv 1 hL).deriv,
    (h.hasDerivAt_at_cusp hdet ha hb hc₃ hd hc hv Complex.I hL).deriv]
  simp only [map_one, Complex.conj_I, neg_neg]
  rw [show Complex.I / (eisEmbedding c ^ 2 * v ^ 2) = -Complex.I * q by dsimp [q]; ring]
  change (χ a c * L (q, 0) + _) / 2 = _
  linear_combination (χ a c / 2) * horizontal_linear L q

theorem hasDerivAt_patterson_mode (a l z u : ℂ) :
    HasDerivAt (fun t : ℝ => a * pattersonCharacter (l * (z + t * u)))
      (a * pattersonCharacter (l * z) * (4 * Real.pi * Complex.I * ((l * u).re : ℂ))) 0 := by
  have hr (t : ℝ) : (l * (z + t * u)).re = (l * z).re + t * (l * u).re := by
    rw [mul_add, show l * (t * u) = t * (l * u) by ring, Complex.add_re]
    simp [Complex.mul_re]
  have H := (((hasDerivAt_id (0 : ℝ)).mul_const (l * u).re).const_add (l*z).re).const_mul 2
  have hh := ((H.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp).const_mul a
  simp only [pattersonCharacter, hr]
  convert hh using 1
  · rfl
  · simp only [id_eq, zero_mul, add_zero, one_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring

/-- Horizontal differentiation of a single trace frequency supplies its
conjugate, with the trace normalization `2πi`. -/
theorem horizontalBarDeriv_patterson_mode (a l z : ℂ) :
    horizontalBarDeriv (fun w => a * pattersonCharacter (l * w)) z =
      2 * Real.pi * Complex.I * conj l * (a * pattersonCharacter (l * z)) := by
  rw [horizontalBarDeriv, (hasDerivAt_patterson_mode a l z 1).deriv,
    (hasDerivAt_patterson_mode a l z Complex.I).deriv]
  have hconj : conj l = (l.re : ℂ) - l.im * Complex.I := by
    apply Complex.ext <;> simp
  rw [mul_one, Complex.mul_I_re, Complex.ofReal_neg, hconj]
  ring

end Masullo.QRH.MeanSquare
