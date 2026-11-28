import Masullo.QRH.MeanSquare.FamilyCharacter
import Masullo.QRH.MeanSquare.FamilyReciprocity

/-! # The quadratic Hecke family for the primary Eisenstein symbol -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma away_of_coprime_seventyTwo {n : Ideal 𝓔} (hn : n ≠ 0)
    (hc : IsCoprime n (span {72})) : AwayFromSix n :=
  ⟨hn, hc.of_isCoprime_of_dvd_right (span_singleton_dvd_span_singleton_iff_dvd.mpr ⟨12, by norm_num⟩)⟩

private lemma minus_one_sq {a : Ideal 𝓔} (ha : AwayFromSix a) :
    quadraticResidue ha (-1) ^ 2 = 1 := by
  rw [← map_pow]; norm_num

/-- Equal classes have identical ramified corrections. Their product is the primitive
uncorrected character of conductor `a * b`. -/
private theorem same_class_product (quad : DeloupTuraevTheorem1) {a b : Ideal 𝓔}
    (ha : Starred a) (hb : Starred b) (h : IsCoprime a b) (he : familyClass a = familyClass b) :
    ∃ ψ : Ideal 𝓔 →*₀ ℂ, IsPrimitiveRayCharacter (a * b) ψ ∧
      ∀ d, d ≠ 0 → IsCoprime d (a * b) → IsCoprime d (quadraticConductor a) →
        IsCoprime d (quadraticConductor b) →
        ψ d = quadraticIdealCharacter ha.1 d * star (quadraticIdealCharacter hb.1 d) := by
  classical
  have hab : Starred (a * b) := ⟨ha.1.mul hb.1, squarefree_mul_iff.mpr ⟨h.isRelPrime, ha.2, hb.2⟩⟩
  have hε := sextic_neg_one_cube_eq_of_familyClass_eq quad ha hb he
  have hprod : sextic (a * b) (-1) ^ 3 = 1 := by
    rw [← quadraticResidue_apply hab.1, quadraticResidue_den_mul ha.1 hb.1]
    rw [quadraticResidue_apply, quadraticResidue_apply, hε, ← sq]
    simpa only [quadraticResidue_apply] using minus_one_sq hb.1
  refine ⟨quadraticIdealCharacter hab.1, ?_, ?_⟩
  · simpa only [quadraticConductor, ite_eq_left hprod] using quadraticIdealCharacter_primitive hab
  intro d hd _ _ hdb
  have hreal : star (quadraticIdealCharacter hb.1 d) = quadraticIdealCharacter hb.1 d := by
    rcases sq_eq_one_iff.mp (quadraticIdealCharacter_sq hb.1 hd hdb) with he | he <;> simp [he]
  rw [hreal, quadraticIdealCharacter_apply _ hd, quadraticIdealCharacter_apply _ hd,
    quadraticIdealCharacter_apply _ hd, correctedQuadratic, ite_eq_left hprod,
    quadraticResidue_den_mul ha.1 hb.1]
  by_cases hx : sextic b (-1) ^ 3 = 1
  · simp [correctedQuadratic, hx, hε]
  · rw [quadraticConductor, ite_eq_right hx] at hdb
    have hram : IsCoprime lambdaIdeal (span {generator d}) := by
      rw [span_generator]
      exact hdb.of_mul_right_right.symm
    simp only [correctedQuadratic, hε, ite_eq_right hx, MonoidHom.mul_apply,
      show ∀ x : 𝓔, lambdaSign.toMonoidHom x = lambdaSign x from fun _ => rfl]
    linear_combination -(quadraticResidue ha.1 (generator d) * quadraticResidue hb.1 (generator d)) *
      lambdaSign_sq hram

/-- The primitive quadratic characters at the squarefree good ideals realize the
primary residue symbol, including its zeros at common factors. -/
theorem eisensteinFamilyRealizes (quad : DeloupTuraevTheorem1) :
    EisensteinFamilyRealizes primaryQuadraticSymbol := by
  classical
  let χ (a : Ideal 𝓔) : Ideal 𝓔 →*₀ ℂ :=
    if ha : AwayFromSix a then quadraticIdealCharacter ha else quadraticIdealCharacter
      (show AwayFromSix 1 from ⟨one_ne_zero, isCoprime_one_left⟩)
  have hχ {a : Ideal 𝓔} (ha : AwayFromSix a) : χ a = quadraticIdealCharacter ha := dite_eq_left ha
  refine ⟨χ, quadraticConductor, ⟨?_, ?_⟩, ?_⟩
  · intro a hsf hc
    have ha : Starred a := ⟨away_of_coprime_seventyTwo hsf.ne_zero hc, hsf⟩
    rw [hχ ha.1]
    exact ⟨quadraticIdealCharacter_primitive ha, fun _ => quadraticIdealCharacter_sq ha.1⟩
  · refine ⟨QuadraticFamilyClass, inferInstance, inferInstance, familyClass, familySign,
      familyClass_one, ?_, familySign_sq, ?_⟩
    · intro a b ha hb hca hcb
      exact familyClass_mul (away_of_coprime_seventyTwo ha hca) (away_of_coprime_seventyTwo hb hcb)
    · intro a b hsa hca hsb hcb hab
      have ha : Starred a := ⟨away_of_coprime_seventyTwo hsa.ne_zero hca, hsa⟩
      have hb : Starred b := ⟨away_of_coprime_seventyTwo hsb.ne_zero hcb, hsb⟩
      rw [hχ ha.1, hχ hb.1, quadraticIdealCharacter_good ha.1 hb.1, quadraticIdealCharacter_good hb.1 ha.1]
      exact ⟨primaryQuadraticSymbol_reciprocity quad ha hb hab, same_class_product quad ha hb hab⟩
  · intro a b hsa hca hsb hcb
    have ha := away_of_coprime_seventyTwo hsa.ne_zero hca
    have hb := away_of_coprime_seventyTwo hsb.ne_zero hcb
    rw [hχ hb, quadraticIdealCharacter_good hb ha]

end Masullo.QRH.MeanSquare
