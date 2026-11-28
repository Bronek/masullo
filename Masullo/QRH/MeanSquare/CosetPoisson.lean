import Masullo.QRH.MeanSquare.Arithmetic
import Masullo.Lattice.Eisenstein

/-! # Poisson summation on a residue class of the Eisenstein integers

The fixed embedding `eisEmbedding` identifies `𝓔` with the lattice `ℤ[ω] ⊂ ℂ` and the residue
class `r + n𝓔` with the coset `σ(r) + σ(n) ℤ[ω]`. Poisson summation on `σ(n) ℤ[ω]`
(`Masullo.Lattice.tsum_eisLattice_comp_add`) applied to `z ↦ W (|z|² / X)` gives `GaoZhaoLemma23`.
Summing it over the residues modulo `(m)` against a function of period `(m)` gives
`hasSum_twisted_poisson`.
-/

noncomputable section

open NumberField MeasureTheory Masullo.Lattice
open scoped ComplexConjugate SchwartzMap FourierTransform RealInnerProductSpace

namespace Masullo.QRH.MeanSquare

local notation "K" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K

private theorem cyclotomicThree' : IsCyclotomicExtension {3} ℚ K := by
  let : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

attribute [local instance] cyclotomicThree'

/-! ### The Eisenstein integers as the lattice `ℤ[ω]` -/

lemma eisEmbedding_eisOmega : eisEmbedding eisOmega = omega := by
  rw [eisEmbedding_omega, omega_eq_exp]

/-- Every Eisenstein integer is `a + b ω` with integers `a, b`. -/
lemma exists_int_eq_add_mul_eisOmega (k : 𝓔) : ∃ a b : ℤ, k = a + b * eisOmega := by
  let pb := (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis
  obtain ⟨f, hf, rfl⟩ := pb.exists_eq_aeval k
  have hdim : pb.dim = 2 := by
    rw [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime Nat.prime_three]
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)]
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  simp [pb, eisOmega, add_comm]

lemma eisEmbedding_injective : Function.Injective eisEmbedding :=
  eisFieldEmbedding.toRingHom.injective.comp (FaithfulSMul.algebraMap_injective 𝓔 K)

lemma eisEmbedding_mem_eisLattice (k : 𝓔) : eisEmbedding k ∈ eisLattice 1 := by
  obtain ⟨a, b, rfl⟩ := exists_int_eq_add_mul_eisOmega k
  exact mem_eisLattice.mpr ⟨a, b, by simp [eisEmbedding_eisOmega]⟩

/-- `eisEmbedding` as a bijection from `𝓔` onto `ℤ[ω]`. -/
def eisLatticeEquiv : 𝓔 ≃ eisLattice 1 :=
  Equiv.ofBijective (fun k ↦ ⟨eisEmbedding k, eisEmbedding_mem_eisLattice k⟩)
    ⟨fun _ _ h ↦ eisEmbedding_injective (congrArg Subtype.val h), fun z ↦ by
      obtain ⟨a, b, hz⟩ := mem_eisLattice.mp z.2
      exact ⟨a + b * eisOmega, Subtype.ext <| by simp [hz, eisEmbedding_eisOmega]⟩⟩

@[simp] lemma coe_eisLatticeEquiv (k : 𝓔) : (eisLatticeEquiv k : ℂ) = eisEmbedding k := rfl

/-- Multiplication by `q ≠ 0` maps `ℤ[ω]` onto `q ℤ[ω]`. -/
def eisLatticeMulEquiv {q : ℂ} (hq : q ≠ 0) : eisLattice 1 ≃ eisLattice q where
  toFun z := ⟨q * z, by
    obtain ⟨a, b, hz⟩ := mem_eisLattice.mp z.2
    exact mem_eisLattice.mpr ⟨a, b, by rw [hz, one_mul]⟩⟩
  invFun z := ⟨z / q, by
    obtain ⟨a, b, hz⟩ := mem_eisLattice.mp z.2
    exact mem_eisLattice.mpr ⟨a, b, by rw [hz, mul_div_cancel_left₀ _ hq, one_mul]⟩⟩
  left_inv z := Subtype.ext (mul_div_cancel_left₀ _ hq)
  right_inv z := Subtype.ext (mul_div_cancel₀ _ hq)

@[simp] lemma coe_eisLatticeMulEquiv {q : ℂ} (hq : q ≠ 0) (z : eisLattice 1) :
    (eisLatticeMulEquiv hq z : ℂ) = q * z := rfl

lemma conj_omega : conj omega = -1 - omega := by
  apply Complex.ext <;> simp [omega]; norm_num

/-- `z ↦ -z̄` preserves `ℤ[ω]`. -/
def eisLatticeNegConj : eisLattice 1 ≃ eisLattice 1 where
  toFun z := ⟨-conj (z : ℂ), by
    obtain ⟨a, b, hz⟩ := mem_eisLattice.mp z.2
    refine mem_eisLattice.mpr ⟨b - a, b, ?_⟩
    rw [hz]; simp [conj_omega]; ring⟩
  invFun z := ⟨-conj (z : ℂ), by
    obtain ⟨a, b, hz⟩ := mem_eisLattice.mp z.2
    refine mem_eisLattice.mpr ⟨b - a, b, ?_⟩
    rw [hz]; simp [conj_omega]; ring⟩
  left_inv z := by simp
  right_inv z := by simp

@[simp] lemma coe_eisLatticeNegConj (z : eisLattice 1) :
    (eisLatticeNegConj z : ℂ) = -conj (z : ℂ) := rfl

/-! ### The radial Schwartz function and its Fourier transform -/

/-- `z ↦ W (|z|² / X)` as a Schwartz function on `ℂ`. -/
def radialSchwartz (W : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℝ (g := fun z : ℂ ↦ X⁻¹ * ‖z‖ ^ 2) (by fun_prop)
    ⟨1, 1 + X, fun z ↦ by
      rw [Real.norm_of_nonneg (by positivity), pow_one]
      have : X * (X⁻¹ * ‖z‖ ^ 2) = ‖z‖ ^ 2 := by field_simp
      nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z,
        mul_nonneg (inv_nonneg.mpr hX.le) (sq_nonneg ‖z‖)]⟩ W

lemma radialSchwartz_apply (W : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) (z : ℂ) :
    radialSchwartz W hX z = W (Complex.normSq z / X) := by
  simp [radialSchwartz, Complex.normSq_eq_norm_sq, div_eq_inv_mul]

/-- The real-linear map `z ↦ c (Re z + Im z (1 + ω))`. -/
def eisCoordMap (c : ℂ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.mulLeft ℝ c).comp (Complex.reLm.smulRight 1 + Complex.imLm.smulRight (1 + omega)))

lemma eisCoordMap_apply (c z : ℂ) : eisCoordMap c z = c * (z.re + z.im * (1 + omega)) := by
  simp only [eisCoordMap, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    Function.comp_apply, LinearMap.mulLeft_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    Complex.reLm_coe, Complex.imLm_coe, Complex.real_smul, mul_one]

lemma det_eisCoordMap (c : ℂ) :
    (eisCoordMap c).det = Complex.normSq c * (√3 / 2) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
  simp [eisCoordMap_apply, omega, Complex.normSq_apply]
  ring

lemma eisCoordMap_injective {c : ℂ} (hc : c ≠ 0) : Function.Injective (eisCoordMap c) := by
  intro z w h
  rw [eisCoordMap_apply, eisCoordMap_apply] at h
  have h' := mul_left_cancel₀ hc h
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp [omega] at hre him
  have : z.im = w.im := by nlinarith [sqrt_three_pos]
  apply Complex.ext <;> [linarith; exact this]

/-- The Fourier transform of `z ↦ W (|z|² / X)` in Gao–Zhao's coordinates. -/
theorem fourier_radialSchwartz (W : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) (ξ : ℂ) :
    𝓕 (radialSchwartz W hX) ξ = X * (√3 / 2) * gaoZhaoTransform W (√X * ‖ξ‖ * (√3 / 2)) := by
  obtain ⟨c, hc, hcξ⟩ : ∃ c : ℂ, Complex.normSq c = X ∧ conj c * ξ = Complex.I * (√X * ‖ξ‖) := by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · exact ⟨√X, by simp [Complex.normSq_ofReal, Real.mul_self_sqrt hX.le], by simp⟩
    refine ⟨-Complex.I * (√X * ‖ξ‖) / conj ξ, ?_, ?_⟩
    · rw [map_div₀, map_mul, Complex.normSq_conj, Complex.normSq_neg, Complex.normSq_I]
      rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq ξ]
      have : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
      field_simp
      rw [Complex.normSq_ofReal, Real.sq_sqrt hX.le]
      ring
    · rw [map_div₀, Complex.conj_conj, map_mul, map_neg, Complex.conj_I, map_mul,
        Complex.conj_ofReal, Complex.conj_ofReal]
      field_simp
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; linarith
  have hsurj : Function.Surjective (eisCoordMap c) :=
    LinearMap.injective_iff_surjective.mp (eisCoordMap_injective hc0)
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, ← Measure.restrict_univ (μ := volume),
    ← Set.image_univ_of_surjective hsurj,
    integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x _ ↦ (eisCoordMap c).hasFDerivWithinAt) (eisCoordMap_injective hc0).injOn,
    Measure.restrict_univ, det_eisCoordMap, hc, abs_of_pos (by positivity), integral_smul,
    gaoZhaoTransform, ← Complex.volume_preserving_equiv_real_prod.integral_comp']
  rw [Complex.real_smul]
  push_cast
  congr 1
  congr 1 with z
  simp only [Complex.measurableEquivRealProd_apply, eisEmbedding_eisOmega, radialSchwartz_apply,
    Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, differentCharacter]
  rw [eisCoordMap_apply, mul_comm (Complex.exp _)]
  set w : ℂ := ↑z.re + ↑z.im * (1 + omega)
  have h1 : Complex.normSq (c * w) / X = Complex.normSq w := by
    rw [Complex.normSq_mul, hc]; field_simp
  have h2 : ⟪c * w, ξ⟫ = √X * ‖ξ‖ * w.im := by
    rw [Complex.inner, map_mul, show ξ * (conj c * conj w) = conj w * (conj c * ξ) by ring, hcξ]
    simp
    ring
  have h3 : (-(↑√X * ↑‖ξ‖ * (↑√3 / 2) : ℂ) * w).im = -(√X * ‖ξ‖ * (√3 / 2)) * w.im := by
    rw [show (↑√X * ↑‖ξ‖ * (↑√3 / 2) : ℂ) = ((√X * ‖ξ‖ * (√3 / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_neg, Complex.im_ofReal_mul]
  rw [h1, h2, h3]
  congr 2
  have := sqrt_three_pos.ne'
  push_cast
  field_simp

/-! ### The coset formula -/

lemma kappa_eq : kappa = ((-2 / √3 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [kappa]

lemma norm_kappa : ‖kappa‖ = 2 / √3 := by
  rw [kappa_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, neg_div,
    abs_neg, abs_of_pos (by positivity [sqrt_three_pos])]

/-- The radius of the dual vector `κ (-ā) / d̄` in Gao–Zhao's normalisation. -/
lemma sqrt_mul_norm_dual {X : ℝ} (hX : 0 < X) (a : ℂ) {d : ℂ} (hd : d ≠ 0) :
    √X * ‖kappa * -conj a / conj d‖ * (√3 / 2) =
      √(Complex.normSq a * X / Complex.normSq d) := by
  have h3 := sqrt_three_pos.ne'
  have hd' : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  rw [norm_div, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_conj, norm_kappa,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    show ‖a‖ ^ 2 * X / ‖d‖ ^ 2 = (√X * ‖a‖ / ‖d‖) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt hX.le]; ring,
    Real.sqrt_sq (by positivity)]
  field_simp

/-- The phase of the dual vector `κ (-ā) / d̄` at `b` is the different character of `ab/d`. -/
lemma fourierChar_inner_dual (a b d : ℂ) :
    (𝐞 ⟪kappa * -conj a / conj d, b⟫ : ℂ) = differentCharacter (a * b / d) := by
  have h3 := sqrt_three_pos.ne'
  have hre : (b * conj (kappa * -conj a / conj d)).re = 2 * (a * b / d).im / √3 := by
    rw [map_div₀, map_mul, map_neg, Complex.conj_conj, Complex.conj_conj,
      show b * (conj kappa * -a / d) = -conj kappa * (a * b / d) by ring, kappa_eq, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    simp only [mul_neg, neg_neg, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.mul_im]
    field_simp
    ring
  rw [Real.fourierChar_apply, differentCharacter, Complex.inner, hre]
  congr 1
  push_cast
  ring

/-- Gao–Zhao, Lemma 2.3, for the Eisenstein integers. -/
theorem gaoZhaoLemma23 : GaoZhaoLemma23 := by
  intro W X hX r n hn N
  have hq : eisEmbedding n ≠ 0 := (map_ne_zero_iff _ eisEmbedding_injective).mpr hn
  set q := eisEmbedding n with hq_def
  set f := radialSchwartz W hX
  have : Fact (q ≠ 0) := ⟨hq⟩
  have hκ : kappa / conj q ≠ 0 := div_ne_zero kappa_ne_zero ((map_ne_zero _).mpr hq)
  let e₁ : 𝓔 ≃ {m : 𝓔 // n ∣ m - r} :=
    Equiv.ofBijective (fun j ↦ ⟨r + n * j, ⟨j, by ring⟩⟩)
      ⟨fun j j' h ↦ mul_left_cancel₀ hn (add_left_cancel (congrArg Subtype.val h)), fun m ↦ by
        obtain ⟨j, hj⟩ := m.2
        exact ⟨j, Subtype.ext (show r + n * j = m.val by rw [← hj]; ring)⟩⟩
  let e₂ : 𝓔 ≃ eisLattice q := eisLatticeEquiv.trans (eisLatticeMulEquiv hq)
  let e₃ : 𝓔 ≃ eisLattice 1 := eisLatticeEquiv.trans eisLatticeNegConj
  let a : 𝓔 → ℂ := fun k ↦ gaoZhaoTransform W (√(N k * X / N n)) *
    differentCharacter (eisEmbedding k * eisEmbedding r / eisEmbedding n)
  have hL : (fun m : {m : 𝓔 // n ∣ m - r} ↦ W (N m.val / X)) ∘ e₁ =
      (fun ℓ : eisLattice q ↦ f (eisEmbedding r + ℓ)) ∘ e₂ := by
    ext j
    change W (N (r + n * j) / X) = f (eisEmbedding r + q * eisEmbedding j)
    simp [N, f, radialSchwartz_apply, q]
  have hR : ∀ k, 𝓕 f (kappa * (e₃ k : ℂ) / conj q) *
      𝐞 ⟪kappa * (e₃ k : ℂ) / conj q, eisEmbedding r⟫ = (X * (√3 / 2) : ℂ) * a k := by
    intro k
    simp only [e₃, Equiv.trans_apply, coe_eisLatticeNegConj,
      coe_eisLatticeEquiv, f, fourier_radialSchwartz, sqrt_mul_norm_dual hX _ hq,
      fourierChar_inner_dual, a, N, q]
    ring
  have hsR : Summable fun m : eisLattice 1 ↦
      𝓕 f (kappa * m / conj q) * 𝐞 ⟪kappa * m / conj q, eisEmbedding r⟫ := by
    have : Fact (kappa / conj q ≠ 0) := ⟨hκ⟩
    obtain ⟨g, hg, hfg⟩ :=
      SchwartzMap.exists_summable_norm_comp_add_le (eisLattice (kappa / conj q)) (𝓕 f) 0
    refine (hg.comp_injective (eisLatticeMulEquiv hκ).injective).of_norm_bounded fun m ↦ ?_
    have h := hfg (eisLatticeMulEquiv hκ m) 0 (by simp)
    rw [zero_add, coe_eisLatticeMulEquiv, div_mul_eq_mul_div] at h
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact h
  have hsA : Summable a := by
    have := e₃.summable_iff.mpr hsR
    simp only [Function.comp_def, hR] at this
    exact (summable_mul_left_iff (mul_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne')
      (div_ne_zero (Complex.ofReal_ne_zero.mpr sqrt_three_pos.ne') two_ne_zero))).mp this
  refine ⟨∑' k, a k, ?_, hsA.hasSum⟩
  have hsL : Summable fun ℓ : eisLattice q ↦ f (eisEmbedding r + ℓ) := by
    obtain ⟨g, hg, hfg⟩ := SchwartzMap.exists_summable_norm_comp_add_le (eisLattice q) f
      ‖eisEmbedding r‖
    exact hg.of_norm_bounded fun ℓ ↦ hfg ℓ _ le_rfl
  rw [← e₁.hasSum_iff, hL, e₂.hasSum_iff]
  convert hsL.hasSum using 1
  rw [tsum_eisLattice_comp_add hq f, ← e₃.tsum_eq]
  simp_rw [hR]
  rw [tsum_mul_left]
  have := sqrt_three_pos.ne'
  have : Complex.normSq q ≠ 0 := Complex.normSq_eq_zero.not.mpr hq
  simp only [N, q] at *
  push_cast
  field_simp

/-! ### Twisting by a periodic function -/

/-- The finite Fourier transform `∑_{x mod I} χ(x) e(Tr(k x / (m √-3)))`, for `I = (m)`. -/
def twistedGauss (χ : 𝓔 → ℂ) (I : Ideal 𝓔) (m k : 𝓔) : ℂ :=
  ∑ᶠ x : 𝓔 ⧸ I, χ (Quotient.out x) *
    differentCharacter (eisEmbedding k * eisEmbedding (Quotient.out x) / eisEmbedding m)

/-- Poisson summation on `𝓔` twisted by a function `χ` of period `I = (m)`: the sum of
`W(N y / X) χ(y)` is `X / N m` times the sum of the transform against the finite Fourier
transform of `χ`. Both sums converge. -/
theorem hasSum_twisted_poisson (W : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) {I : Ideal 𝓔} {m : 𝓔}
    (hm : Ideal.span {m} = I) (hI : I ≠ ⊥) {χ : 𝓔 → ℂ}
    (hχ : ∀ y y', y - y' ∈ I → χ y = χ y') :
    let N := fun y : 𝓔 ↦ Complex.normSq (eisEmbedding y)
    Summable (fun k ↦ gaoZhaoTransform W (√(N k * X / N m)) * twistedGauss χ I m k) ∧
      HasSum (fun y ↦ W (N y / X) * χ y)
        (X / N m * ∑' k, gaoZhaoTransform W (√(N k * X / N m)) * twistedGauss χ I m k) := by
  intro N
  have hm0 : m ≠ 0 := by rintro rfl; exact hI (by simpa using hm.symm)
  have : Finite (𝓔 ⧸ I) := (Ideal.absNorm_ne_zero_iff I).mp (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  let : Fintype (𝓔 ⧸ I) := Fintype.ofFinite _
  have hdvd : ∀ y y' : 𝓔, m ∣ y - y' ↔ Ideal.Quotient.mk I y = Ideal.Quotient.mk I y' := by
    intro y y'
    rw [Ideal.Quotient.eq, ← hm, Ideal.mem_span_singleton]
  let t : (𝓔 ⧸ I) → 𝓔 → ℂ := fun x k ↦ gaoZhaoTransform W (√(N k * X / N m)) *
    differentCharacter (eisEmbedding k * eisEmbedding (Quotient.out x) / eisEmbedding m)
  have hx : ∀ x, Summable (t x) ∧ HasSum (Set.indicator {y | m ∣ y - Quotient.out x}
      fun y ↦ W (N y / X)) (X / N m * ∑' k, t x k) := by
    intro x
    obtain ⟨s, h₁, h₂⟩ := gaoZhaoLemma23 W X hX (Quotient.out x) m hm0
    rw [h₂.tsum_eq]
    exact ⟨h₂.summable, (hasSum_subtype_iff_indicator (s := {y | m ∣ y - Quotient.out x})).mp h₁⟩
  have hG : ∀ k, gaoZhaoTransform W (√(N k * X / N m)) * twistedGauss χ I m k =
      ∑ x, χ (Quotient.out x) * t x k := by
    intro k
    rw [twistedGauss, finsum_eq_sum_of_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  simp_rw [hG]
  refine ⟨summable_sum fun x _ ↦ (hx x).1.mul_left (χ (Quotient.out x)), ?_⟩
  have hT : ∑' k, ∑ x, χ (Quotient.out x) * t x k = ∑ x, ∑' k, χ (Quotient.out x) * t x k :=
    Summable.tsum_finsetSum fun x _ ↦ (hx x).1.mul_left _
  rw [hT, Finset.mul_sum]
  convert hasSum_sum fun x (_ : x ∈ Finset.univ) ↦ (hx x).2.mul_left (χ (Quotient.out x))
    using 1
  · ext y
    rw [Finset.sum_eq_single (Ideal.Quotient.mk I y)]
    · rw [Set.indicator_of_mem (by
        simp only [Set.mem_ofPred_eq, hdvd, Ideal.Quotient.mk_out])]
      rw [hχ (Quotient.out _) y (by
        rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]), mul_comm]
    · intro x _ hx'
      rw [Set.indicator_of_notMem (by
        simp only [Set.mem_ofPred_eq, hdvd, Ideal.Quotient.mk_out]; exact Ne.symm hx'), mul_zero]
    · simp
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [tsum_mul_left]
    ring

end Masullo.QRH.MeanSquare
