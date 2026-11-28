import Masullo.QRH.MeanSquare.Primary
import Masullo.QRH.MeanSquare.Residue

/-! # The quadratic character at the prime above three -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "K" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private abbrev rootSpec := IsCyclotomicExtension.zeta_spec 3 ℚ K

/-- The ramified prime ideal above three. -/
def lambdaIdeal : Ideal 𝓔 := span {eisOmega - 1}

theorem lambdaIdeal_prime : Prime lambdaIdeal := by
  have hp : Prime (eisOmega - 1) := rootSpec.zeta_sub_one_prime'
  exact (prime_iff_isPrime (by simpa [lambdaIdeal] using hp.ne_zero)).mpr
    ((span_singleton_prime hp.ne_zero).mpr hp)

theorem lambdaIdeal_dvd_three : lambdaIdeal ∣ span {(3 : 𝓔)} :=
  span_singleton_dvd_span_singleton_iff_dvd.mpr rootSpec.toInteger_sub_one_dvd_prime'

private def lambdaResidueEquiv : (𝓔 ⧸ lambdaIdeal) ≃+* ZMod 3 := by
  let := Ring.HasFiniteQuotients.finiteQuotient lambdaIdeal_prime.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ lambdaIdeal)
  refine (ZMod.ringEquivOfPrime _ (by decide : Nat.Prime 3) ?_).symm
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (𝓔 ⧸ span {rootSpec.toInteger - 1}) = 3
  rw [rootSpec.card_quotient_toInteger_sub_one,
    rootSpec.norm_toInteger_sub_one_of_prime_ne_two' (by decide)]
  decide

lemma absNorm_lambdaIdeal : absNorm lambdaIdeal = 3 := by
  rw [absNorm_eq_natCard, Nat.card_congr lambdaResidueEquiv.toEquiv, Nat.card_zmod]

private def lambdaResidue : 𝓔 →+* ZMod 3 :=
  lambdaResidueEquiv.toRingHom.comp (Ideal.Quotient.mk lambdaIdeal)

private def modThreeSign : ZMod 3 →*₀ ℂ :=
  ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)).toMonoidWithZeroHom

/-- The zero-extended quadratic character modulo `ω - 1`. -/
def lambdaSign : 𝓔 →*₀ ℂ := modThreeSign.comp lambdaResidue.toMonoidWithZeroHom

theorem lambdaSign_congr {x y : 𝓔} (h : eisOmega - 1 ∣ x - y) : lambdaSign x = lambdaSign y :=
  congrArg (fun t => modThreeSign (lambdaResidueEquiv t))
    ((Ideal.Quotient.eq (I := lambdaIdeal)).mpr (mem_span_singleton.mpr h))

@[simp] theorem lambdaSign_eq_zero_iff {x : 𝓔} : lambdaSign x = 0 ↔ eisOmega - 1 ∣ x := by
  have h (z : ZMod 3) : modThreeSign z = 0 ↔ z = 0 := by
    change ((quadraticChar (ZMod 3) z : ℤ) : ℂ) = 0 ↔ _
    rw [Int.cast_eq_zero, quadraticChar_eq_zero_iff]
  change modThreeSign (lambdaResidueEquiv (Ideal.Quotient.mk lambdaIdeal x)) = 0 ↔ _
  rw [h, EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
    lambdaIdeal, mem_span_singleton]

theorem lambdaSign_ne_zero_iff {x : 𝓔} : lambdaSign x ≠ 0 ↔ IsCoprime lambdaIdeal (span {x}) := by
  have hP := (Ideal.prime_iff_isPrime lambdaIdeal_prime.ne_zero).mp lambdaIdeal_prime
  let : lambdaIdeal.IsMaximal := hP.isMaximal lambdaIdeal_prime.ne_zero
  let := Ideal.Quotient.field lambdaIdeal
  rw [← isUnit_mk_iff_coprime_span, isUnit_iff_ne_zero, ne_eq, ne_eq,
    Ideal.Quotient.eq_zero_iff_mem, lambdaIdeal, mem_span_singleton, lambdaSign_eq_zero_iff]

theorem lambdaSign_eq_one_of_dvd_sub_one {x : 𝓔} (h : eisOmega - 1 ∣ x - 1) : lambdaSign x = 1 :=
  (lambdaSign_congr h).trans (map_one _)

@[simp] theorem lambdaSign_neg_one : lambdaSign (-1) = -1 := by
  change modThreeSign (lambdaResidue (-1)) = -1
  rw [map_neg, map_one]
  change ((quadraticChar (ZMod 3) (-1) : ℤ) : ℂ) = -1
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr ?_]
  · norm_num
  · rintro ⟨t, ht⟩
    fin_cases t <;> exact absurd ht (by decide)

@[simp] theorem lambdaSign_neg (x : 𝓔) : lambdaSign (-x) = -lambdaSign x := by
  rw [← neg_one_mul x, map_mul, lambdaSign_neg_one, neg_one_mul]

theorem lambdaSign_eq_neg_one_of_dvd_add_one {x : 𝓔} (h : eisOmega - 1 ∣ x + 1) :
    lambdaSign x = -1 :=
  (lambdaSign_congr (y := -1) (by simpa using h)).trans lambdaSign_neg_one

theorem lambdaSign_eq_one_of_eisPrimary {x : 𝓔} (hx : eisPrimary x) : lambdaSign x = 1 :=
  lambdaSign_eq_one_of_dvd_sub_one (rootSpec.toInteger_sub_one_dvd_prime'.trans hx)

@[simp] theorem lambdaSign_eisOmega : lambdaSign eisOmega = 1 :=
  lambdaSign_eq_one_of_dvd_sub_one dvd_rfl

theorem lambdaSign_sq_of_not_dvd {x : 𝓔} (hx : ¬ eisOmega - 1 ∣ x) : lambdaSign x ^ 2 = 1 := by
  rcases IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one rootSpec x with
    h | h | h
  · exact (hx h).elim
  · rw [lambdaSign_eq_one_of_dvd_sub_one h, one_pow]
  · rw [lambdaSign_eq_neg_one_of_dvd_add_one h]; norm_num

theorem lambdaSign_sq {x : 𝓔} (hx : IsCoprime lambdaIdeal (span {x})) : lambdaSign x ^ 2 = 1 :=
  lambdaSign_sq_of_not_dvd (lambdaSign_eq_zero_iff.not.mp (lambdaSign_ne_zero_iff.mpr hx))

/-- A quadratic character of the Eisenstein integers is trivial on every unit if it is
trivial at `-1`. Otherwise multiplying by the character at the ramified prime makes it
trivial on every unit. -/
private theorem quadratic_unit_rules (χ : 𝓔 →* ℂ) (hω : χ eisOmega = 1) (u : 𝓔ˣ) :
    (χ (-1) = 1 → χ u = 1) ∧ (χ (-1) ≠ 1 → χ u * lambdaSign u = 1) := by
  have hneg : χ (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  have units := IsCyclotomicExtension.Rat.Three.Units.mem rootSpec u
  let η : 𝓔ˣ := (rootSpec.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : 𝓔) = eisOmega := rfl
  change u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at units
  simp only [List.mem_cons, List.not_mem_nil, or_false] at units
  have negOmega : -eisOmega = (-1 : 𝓔) * eisOmega := (neg_one_mul _).symm
  have negOmegaSq : -(eisOmega ^ 2) = (-1 : 𝓔) * eisOmega ^ 2 := (neg_one_mul _).symm
  have signs := (sq_eq_one_iff.mp hneg)
  rcases units with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Units.val_one, Units.val_neg, Units.val_pow_eq_pow_val, hη, negOmega, negOmegaSq,
      map_mul, map_pow, map_one, hω, lambdaSign_eisOmega, lambdaSign_neg_one, one_pow,
        mul_one] <;> grind [sq_eq_one_iff]

/-- The cube of the sextic character and its ramified correction on the six units. -/
theorem sextic_cubed_unit {n : Ideal 𝓔} (hn : AwayFromSix n) (u : 𝓔ˣ) :
    (sextic n (-1) ^ 3 = 1 → sextic n u ^ 3 = 1) ∧
    (sextic n (-1) ^ 3 ≠ 1 → sextic n u ^ 3 * lambdaSign u = 1) := by
  let χ := ((sexticChar hn ^ 3).toMonoidHom).comp (Ideal.Quotient.mk n).toMonoidHom
  have hχ (x : 𝓔) : χ x = sextic n x ^ 3 := by
    change (sexticChar hn ^ 3) (Ideal.Quotient.mk n x) = _
    rw [MulChar.pow_apply' _ (by decide : 3 ≠ 0), sexticChar_apply_mk]
  have hω : χ eisOmega = 1 := by
    rw [hχ, ← sexticChar_apply_mk hn, ← map_pow, ← map_pow, omega_primitive.pow_eq_one,
      map_one, map_one]
  simpa only [hχ] using quadratic_unit_rules χ hω u

end Masullo.QRH.MeanSquare
