import Masullo.QRH.MeanSquare.Eisenstein
import Masullo.QRH.MeanSquare.Rows
import Masullo.Lattice.Eisenstein

/-! # The trace and different characters on the Eisenstein integers -/

noncomputable section

open NumberField Ideal Complex

namespace Masullo.QRH.MeanSquare

local notation "K" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

lemma eisInteger_coordinates (x : 𝓔) : ∃ a b : ℤ, x = a + b * eisOmega := by
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let p := hζ.integralPowerBasis
  have hd : p.dim = 2 := hζ.integralPowerBasis_dim.trans (by decide)
  let B := p.basis.reindex (finCongr hd)
  refine ⟨B.repr x 0, B.repr x 1, ?_⟩
  have h₀ : B 0 = 1 := by simp [B, Module.Basis.reindex_apply, PowerBasis.coe_basis, finCongr]
  have h₁ : B 1 = eisOmega := by
    simp [B, Module.Basis.reindex_apply, PowerBasis.coe_basis, finCongr, p, eisOmega]
  simpa only [Fin.sum_univ_two, h₀, h₁, zsmul_eq_mul, mul_one] using (B.sum_repr x).symm

lemma eisEmbedding_lambda : eisEmbedding eisLambda = (Real.sqrt 3 : ℂ) * I := by
  rw [eisLambda, map_add, map_one, map_mul, map_ofNat, eisEmbedding_omega,
    ← Masullo.Lattice.omega_eq_exp]
  apply Complex.ext <;> norm_num [Masullo.Lattice.omega]
  ring

lemma eisLambda_sq : eisLambda ^ 2 = -3 := by
  have h : eisOmega ^ 2 + eisOmega + 1 = 0 :=
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)
  unfold eisLambda
  linear_combination 4 * h

/-- The character used in the Patterson Gauss sum. -/
def traceCharacter (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (2 * z.re : ℝ))

lemma differentCharacter_add (z w : ℂ) :
    differentCharacter (z + w) = differentCharacter z * differentCharacter w := by
  unfold differentCharacter
  rw [← Complex.exp_add, Complex.add_im]
  congr 1
  push_cast
  ring

lemma traceCharacter_add (z w : ℂ) :
    traceCharacter (z + w) = traceCharacter z * traceCharacter w := by
  unfold traceCharacter
  rw [← Complex.exp_add, Complex.add_re]
  congr 1
  push_cast
  ring

@[simp] lemma differentCharacter_eisEmbedding (x : 𝓔) :
    differentCharacter (eisEmbedding x) = 1 := by
  obtain ⟨a, b, rfl⟩ := eisInteger_coordinates x
  unfold differentCharacter
  rw [map_add, map_mul, map_intCast, map_intCast, eisEmbedding_omega,
    ← Masullo.Lattice.omega_eq_exp]
  have h : 2 * ((a : ℂ) + b * Masullo.Lattice.omega).im / √3 = b := by
    simp [Masullo.Lattice.omega]
    field_simp
  rw [h, Complex.ofReal_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I b

lemma differentCharacter_lambda_mul (z : ℂ) :
    differentCharacter (eisEmbedding eisLambda * z) = traceCharacter z := by
  unfold differentCharacter traceCharacter
  rw [eisEmbedding_lambda]
  congr 2
  simp [Complex.mul_im, Complex.mul_re]
  field_simp

theorem differentCharacter_eq_traceCharacter_div (z : ℂ) :
    differentCharacter z = traceCharacter (z / eisEmbedding eisLambda) := by
  have h : eisEmbedding eisLambda ≠ 0 := by
    rw [eisEmbedding_lambda]
    exact mul_ne_zero (by exact_mod_cast Masullo.Lattice.sqrt_three_pos.ne') Complex.I_ne_zero
  rw [← differentCharacter_lambda_mul, mul_div_cancel₀ _ h]

@[simp] lemma traceCharacter_eisEmbedding (x : 𝓔) : traceCharacter (eisEmbedding x) = 1 := by
  rw [← differentCharacter_lambda_mul, ← map_mul, differentCharacter_eisEmbedding]

lemma eisEmbedding_injective : Function.Injective eisEmbedding :=
  eisFieldEmbedding.injective.comp RingOfIntegers.coe_injective

lemma differentCharacter_div_congr {x y c : 𝓔} (h : c ∣ x - y) :
    differentCharacter (eisEmbedding x / eisEmbedding c) =
      differentCharacter (eisEmbedding y / eisEmbedding c) := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨k, hk⟩ := h
  have hne : eisEmbedding c ≠ 0 :=
    fun he => hc (eisEmbedding_injective (he.trans (map_zero _).symm))
  rw [sub_eq_iff_eq_add.mp hk, map_add, map_mul, add_div, mul_div_cancel_left₀ _ hne,
    differentCharacter_add, differentCharacter_eisEmbedding, one_mul]

private lemma integral_im_of_differentCharacter_eq_one {z : ℂ} (hz : differentCharacter z = 1) :
    ∃ b : ℤ, 2 * z.im = b * √3 := by
  obtain ⟨b, hb⟩ := Complex.exp_eq_one_iff.mp hz
  refine ⟨b, (div_eq_iff Masullo.Lattice.sqrt_three_pos.ne').mp ?_⟩
  rw [mul_comm (2 * (Real.pi : ℂ) * I)] at hb
  have he := mul_right_cancel₀ (by simp [Real.pi_ne_zero] : 2 * (Real.pi : ℂ) * I ≠ 0) hb
  exact_mod_cast he

/-- The different character pairs the quotient by `(c)` perfectly with itself. -/
lemma dvd_of_forall_differentCharacter_eq_one {c x : 𝓔} (hc : c ≠ 0)
    (h : ∀ y : 𝓔, differentCharacter (eisEmbedding (y * x) / eisEmbedding c) = 1) :
    c ∣ x := by
  let z := eisEmbedding x / eisEmbedding c
  obtain ⟨b, hb⟩ := integral_im_of_differentCharacter_eq_one (z := z) (by simpa [z] using h 1)
  have hω := eisEmbedding_omega.trans Masullo.Lattice.omega_eq_exp.symm
  obtain ⟨a, ha⟩ := integral_im_of_differentCharacter_eq_one
    (z := (1 + Masullo.Lattice.omega) * z) (by
      have hy := h (1 + eisOmega)
      rw [map_mul, map_add, map_one, hω, mul_div_assoc] at hy
      exact hy)
  have he : z = eisEmbedding (a + b * eisOmega) := by
    rw [map_add, map_mul, map_intCast, map_intCast, hω]
    simp only [Masullo.Lattice.omega, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.one_re,
      Complex.one_im] at ha
    apply Complex.ext <;> simp [Masullo.Lattice.omega]
    · apply mul_right_cancel₀ Masullo.Lattice.sqrt_three_pos.ne'
      nlinarith [Masullo.Lattice.sq_sqrt_three]
    · linarith
  refine ⟨a + b * eisOmega, eisEmbedding_injective ?_⟩
  have hc' : eisEmbedding c ≠ 0 :=
    fun he => hc (eisEmbedding_injective (he.trans (map_zero _).symm))
  rw [map_mul, mul_comm]
  exact (div_eq_iff hc').mp he

private lemma differentCharacter_eq_of_mk_eq {n : Ideal 𝓔} {x y : 𝓔}
    (h : Ideal.Quotient.mk n x = Ideal.Quotient.mk n y) :
    differentCharacter (eisEmbedding x / eisEmbedding (generator n)) =
      differentCharacter (eisEmbedding y / eisEmbedding (generator n)) := by
  apply differentCharacter_div_congr
  rw [← mem_span_singleton, span_generator]
  exact Ideal.Quotient.eq.mp h

/-- The different character with denominator the chosen generator of `n`. -/
def quotientDifferentCharacter (n : Ideal 𝓔) : AddChar (𝓔 ⧸ n) ℂ where
  toFun x := differentCharacter (eisEmbedding (Quotient.out x) / eisEmbedding (generator n))
  map_zero_eq_one' := by
    trans differentCharacter (eisEmbedding 0 / eisEmbedding (generator n))
    · apply differentCharacter_eq_of_mk_eq
      rw [Ideal.Quotient.mk_out, map_zero]
    · simp [differentCharacter]
  map_add_eq_mul' x y := by
    trans differentCharacter (eisEmbedding (Quotient.out x + Quotient.out y) /
      eisEmbedding (generator n))
    · apply differentCharacter_eq_of_mk_eq
      rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]
    · rw [map_add, add_div, differentCharacter_add]

theorem quotientDifferentCharacter_apply (n : Ideal 𝓔) (x : 𝓔 ⧸ n) :
    quotientDifferentCharacter n x =
      differentCharacter (eisEmbedding (Quotient.out x) / eisEmbedding (generator n)) := rfl

@[simp] theorem quotientDifferentCharacter_mk (n : Ideal 𝓔) (x : 𝓔) :
    quotientDifferentCharacter n (Ideal.Quotient.mk n x) =
      differentCharacter (eisEmbedding x / eisEmbedding (generator n)) :=
  differentCharacter_eq_of_mk_eq (Ideal.Quotient.mk_out _)

theorem quotientDifferentCharacter_isPrimitive {n : Ideal 𝓔} (hn : n ≠ ⊥) :
    (quotientDifferentCharacter n).IsPrimitive := by
  have hc : generator n ≠ 0 := fun hc => hn (by simpa [hc] using (span_generator n).symm)
  intro a ha h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← span_generator n, mem_span_singleton]
  apply dvd_of_forall_differentCharacter_eq_one hc
  intro y
  have he := DFunLike.congr_fun h (Ideal.Quotient.mk n y)
  simpa only [AddChar.mulShift_apply, ← map_mul, quotientDifferentCharacter_mk, one_apply,
    mul_comm x y] using he

end Masullo.QRH.MeanSquare
