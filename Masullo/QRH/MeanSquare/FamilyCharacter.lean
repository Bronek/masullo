import Masullo.QRH.MeanSquare.FamilyLambda
import Masullo.QRH.MeanSquare.FamilyPrimitive
import Masullo.QRH.MeanSquare.FamilySymbol

/-! # The primitive ideal character of a squarefree quadratic residue symbol -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

open Classical in
/-- The ramified prime at three occurs exactly when the symbol is odd on units. -/
def quadraticConductor (n : Ideal 𝓔) : Ideal 𝓔 :=
  if sextic n (-1) ^ 3 = 1 then n else n * lambdaIdeal

open Classical in
def correctedQuadratic {n : Ideal 𝓔} (hn : AwayFromSix n) : 𝓔 →* ℂ :=
  if sextic n (-1) ^ 3 = 1 then quadraticResidue hn else quadraticResidue hn * lambdaSign.toMonoidHom

@[simp] private lemma lambdaSign_toMonoidHom (x : 𝓔) : lambdaSign.toMonoidHom x = lambdaSign x := rfl

private lemma correctedQuadratic_units {n : Ideal 𝓔} (hn : AwayFromSix n) (v : 𝓔ˣ) :
    correctedQuadratic hn v = 1 := by
  classical
  obtain ⟨h₁, h₂⟩ := sextic_cubed_unit hn v
  by_cases h : sextic n (-1) ^ 3 = 1
  · simpa [correctedQuadratic, h, quadraticResidue_apply] using h₁ h
  · simpa [correctedQuadratic, h, quadraticResidue_apply] using h₂ h

def quadraticIdealCharacter {n : Ideal 𝓔} (hn : AwayFromSix n) : Ideal 𝓔 →*₀ ℂ :=
  idealCharacterOfElement (correctedQuadratic hn) (correctedQuadratic_units hn)

lemma quadraticIdealCharacter_apply {n a : Ideal 𝓔} (hn : AwayFromSix n) (ha : a ≠ 0) :
    quadraticIdealCharacter hn a = correctedQuadratic hn (generator a) :=
  idealCharacterOfElement_apply _ _ ha

lemma quadraticIdealCharacter_good {n a : Ideal 𝓔} (hn : AwayFromSix n) (ha : AwayFromSix a) :
    quadraticIdealCharacter hn a = primaryQuadraticSymbol a n := by
  classical
  rw [quadraticIdealCharacter_apply hn ha.1]
  have hl := lambdaSign_eq_one_of_eisPrimary (eisPrimary_generator ha.coprime_three)
  unfold correctedQuadratic
  split <;> simp only [MonoidHom.mul_apply, lambdaSign_toMonoidHom, hl, mul_one,
    quadraticResidue_apply, sextic, primaryQuadraticSymbol]

lemma quadraticIdealCharacter_isRay {n : Ideal 𝓔} (hn : AwayFromSix n) :
    IsRayCharacter (quadraticConductor n) (quadraticIdealCharacter hn) := by
  classical
  refine isRayCharacter_of_element ?_ _ (correctedQuadratic_units hn) ?_ ?_
  · unfold quadraticConductor
    split <;> first | exact hn.1 | exact mul_ne_zero hn.1 lambdaIdeal_prime.ne_zero
  · intro x
    by_cases h : sextic n (-1) ^ 3 = 1
    · simpa [correctedQuadratic, quadraticConductor, h] using (quadraticResidue_ne_zero hn (x := x))
    · simp only [correctedQuadratic, quadraticConductor, ite_eq_right h, MonoidHom.mul_apply,
        lambdaSign_toMonoidHom, mul_ne_zero_iff, quadraticResidue_ne_zero hn,
        lambdaSign_ne_zero_iff, IsCoprime.mul_left_iff]
  · intro x hx
    by_cases h : sextic n (-1) ^ 3 = 1
    · rw [quadraticConductor, ite_eq_left h] at hx
      rw [correctedQuadratic, ite_eq_left h, quadraticResidue_congr hn hx, map_one]
    · rw [quadraticConductor, ite_eq_right h] at hx
      rw [correctedQuadratic, ite_eq_right h, MonoidHom.mul_apply,
        quadraticResidue_congr hn (Ideal.mul_le_left hx), map_one, one_mul]
      exact lambdaSign_eq_one_of_dvd_sub_one (mem_span_singleton.mp (Ideal.mul_le_right hx))

lemma quadraticIdealCharacter_sq {n a : Ideal 𝓔} (hn : AwayFromSix n)
    (ha : a ≠ 0) (hc : IsCoprime a (quadraticConductor n)) :
    quadraticIdealCharacter hn a ^ 2 = 1 := by
  classical
  rw [quadraticIdealCharacter_apply hn ha]
  have hxa : span {generator a} = a := span_generator a
  by_cases h : sextic n (-1) ^ 3 = 1
  · rw [quadraticConductor, ite_eq_left h] at hc
    rw [correctedQuadratic, ite_eq_left h]
    exact quadraticResidue_sq hn (hxa.symm ▸ hc.symm)
  · rw [quadraticConductor, ite_eq_right h] at hc
    rw [correctedQuadratic, ite_eq_right h, MonoidHom.mul_apply, mul_pow,
      quadraticResidue_sq hn (hxa.symm ▸ hc.of_mul_right_left.symm), one_mul]
    exact lambdaSign_sq (hxa.symm ▸ hc.of_mul_right_right.symm)

private lemma prime_test_nonzero {P m : Ideal 𝓔} (hp : Prime P) {x : 𝓔}
    (hc : IsCoprime (span {x}) (P * m)) : x ≠ 0 := by
  rintro rfl
  have h := hc.of_mul_right_left
  exact hp.not_isUnit (isCoprime_zero_left.mp (by simpa only [span_singleton_zero, Ideal.zero_eq_bot] using h))

private lemma quadratic_prime_test {P m n : Ideal 𝓔} (hn : AwayFromSix n)
    (hp : Prime P) (hP : AwayFromSix P) (hc : IsCoprime P m)
    (hlocal : ∀ x : 𝓔, x - 1 ∈ m → correctedQuadratic hn x = quadraticResidue hP x) :
    ∃ x : 𝓔, IsCoprime (span {x}) (P * m) ∧ x - 1 ∈ m ∧ quadraticIdealCharacter hn (span {x}) ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_sexticChar_cube_ne_one hP hp
  obtain ⟨x, hx, hm, hxm⟩ := exists_prime_test hc z
  refine ⟨x, hxm, hm, ?_⟩
  rw [quadraticIdealCharacter, idealCharacterOfElement_span _ _ (prime_test_nonzero hp hxm), hlocal x hm]
  change (sexticChar hP ^ 3) (Ideal.Quotient.mk P x) ≠ 1
  rwa [hx, MulChar.pow_apply' _ (by decide : 3 ≠ 0)]

private lemma coprime_factors {p m : Ideal 𝓔} (h : Squarefree (p * m)) : IsCoprime p m :=
  isCoprime_iff_sup_eq.mpr <| Ideal.isUnit_iff.mp <| IsRelPrime.of_squarefree_mul h
    (dvd_iff_le.mpr le_sup_left) (dvd_iff_le.mpr le_sup_right)

private lemma away_of_dvd {a n : Ideal 𝓔} (hn : AwayFromSix n) (h : a ∣ n) : AwayFromSix a :=
  ⟨ne_zero_of_dvd_ne_zero hn.1 h, hn.2.of_isCoprime_of_dvd_left h⟩

/-- Each prime of `n` contributes its nontrivial quadratic character. In the odd case
the ramified prime contributes the character modulo `ω - 1`, detected by `-1`. -/
theorem quadraticIdealCharacter_primitive {n : Ideal 𝓔} (hn : Starred n) :
    IsPrimitiveRayCharacter (quadraticConductor n) (quadraticIdealCharacter hn.1) := by
  classical
  apply isPrimitiveRayCharacter_of_prime_tests (quadraticIdealCharacter_isRay hn.1)
  intro P m hp hfac
  rw [hfac]
  have hram := hn.1.coprime_three.of_isCoprime_of_dvd_right lambdaIdeal_dvd_three
  by_cases he : sextic n (-1) ^ 3 = 1
  · rw [quadraticConductor, ite_eq_left he] at hfac
    have hP := away_of_dvd hn.1 (show P ∣ n from ⟨m, hfac⟩)
    have hm := away_of_dvd hn.1 (show m ∣ n from hfac ▸ dvd_mul_left m P)
    apply quadratic_prime_test hn.1 hp hP (coprime_factors (hfac ▸ hn.2))
    intro x hx
    rw [correctedQuadratic, ite_eq_left he]
    subst n
    rw [quadraticResidue_den_mul hP hm, quadraticResidue_congr hm hx, map_one, mul_one]
  · rw [quadraticConductor, ite_eq_right he] at hfac
    have hsf : Squarefree (P * m) := hfac ▸ squarefree_mul_iff.mpr ⟨hram.isRelPrime, hn.2, lambdaIdeal_prime.squarefree⟩
    have hcop := coprime_factors hsf
    rcases hp.dvd_or_dvd (show P ∣ n * lambdaIdeal from ⟨m, hfac⟩) with hpn | hpl
    · obtain ⟨d, hd⟩ := hpn
      have hP := away_of_dvd hn.1 (show P ∣ n from ⟨d, hd⟩)
      have hd' := away_of_dvd hn.1 (show d ∣ n from hd ▸ dvd_mul_left d P)
      have hm : d * lambdaIdeal = m := mul_left_cancel₀ hp.ne_zero (by rwa [hd, mul_assoc] at hfac)
      apply quadratic_prime_test hn.1 hp hP hcop
      intro x hx
      rw [← hm] at hx
      rw [correctedQuadratic, ite_eq_right he, MonoidHom.mul_apply]
      subst n
      rw [quadraticResidue_den_mul hP hd', quadraticResidue_congr hd' (Ideal.mul_le_left hx),
        map_one, mul_one, show lambdaSign.toMonoidHom x = 1 from
          lambdaSign_eq_one_of_dvd_sub_one (mem_span_singleton.mp (Ideal.mul_le_right hx)), mul_one]
    · have heq : P = lambdaIdeal := associated_iff_eq.mp (hp.associated_of_dvd lambdaIdeal_prime hpl)
      subst P
      have hm : n = m := mul_left_cancel₀ lambdaIdeal_prime.ne_zero (by rwa [mul_comm n] at hfac)
      obtain ⟨x, hx, hx₁, hxc⟩ := exists_prime_test hcop (-1)
      refine ⟨x, hxc, hx₁, ?_⟩
      rw [quadraticIdealCharacter, idealCharacterOfElement_span _ _ (prime_test_nonzero lambdaIdeal_prime hxc),
        correctedQuadratic, ite_eq_right he, MonoidHom.mul_apply, quadraticResidue_congr hn.1 (hm.symm ▸ hx₁),
        map_one, one_mul]
      have hxneg : Ideal.Quotient.mk lambdaIdeal x = Ideal.Quotient.mk _ (-1) := by simpa using hx
      change lambdaSign x ≠ 1
      rw [lambdaSign_congr (mem_span_singleton.mp (Ideal.Quotient.eq.mp hxneg)), lambdaSign_neg_one]
      norm_num

end Masullo.QRH.MeanSquare
