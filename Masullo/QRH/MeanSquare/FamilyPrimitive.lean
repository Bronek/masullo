import Masullo.QRH.MeanSquare.GaussJacobi
import Masullo.QRH.MeanSquare.Sieve

/-! # Local tests for primitivity of ideal characters -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

variable {K : Type} [Field K] [NumberField K]

/-- A nontrivial principal-ideal value on the kernel of reduction from `f` to
`m` rules out the smaller conductor `m`. Testing one such value for every
factorization `f = P * m` with `P` prime rules out every proper divisor. -/
theorem isPrimitiveRayCharacter_of_prime_tests {f : Ideal (𝓞 K)} {χ : Ideal (𝓞 K) →*₀ ℂ}
    (hχ : IsRayCharacter f χ)
    (htest : ∀ P m : Ideal (𝓞 K), Prime P → f = P * m →
      ∃ x : 𝓞 K, IsCoprime (span {x}) f ∧ x - 1 ∈ m ∧ χ (span {x}) ≠ 1) :
    IsPrimitiveRayCharacter f χ := by
  refine ⟨hχ, ?_⟩
  rintro d ⟨a, hf⟩ ψ hψ heq
  by_cases ha : IsUnit a
  · simpa [isUnit_iff_eq_one.mp ha] using hf.symm
  have ha₀ : a ≠ 0 := fun h => hχ.1 (by simpa [h] using hf)
  obtain ⟨P, hp, b, hab⟩ := WfDvdMonoid.exists_irreducible_factor ha ha₀
  have hfactor : f = P * (d * b) := by rw [hf, hab]; ac_rfl
  have hp' := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  obtain ⟨x, hx, hm, hval⟩ := htest P (d * b) hp' hfactor
  have hx₀ : x ≠ 0 := by
    rintro rfl
    have hu : IsUnit f := isCoprime_zero_left.mp
      (by simpa only [span_singleton_zero, Ideal.zero_eq_bot] using hx)
    exact hp.not_isUnit (isUnit_of_dvd_unit ⟨_, hfactor⟩ hu)
  exact (hval ((heq _ (by simpa using hx₀) hx).symm.trans
    (hψ.2.2 x hx₀ (Ideal.mul_le_left hm)))).elim

/-- Lift an arbitrary unit residue modulo `P` to an element congruent to one
modulo `m`. Its principal ideal is coprime to the full product. -/
theorem exists_prime_test {R : Type*} [CommRing R] {P m : Ideal R} (h : IsCoprime P m)
    (z : (R ⧸ P)ˣ) : ∃ x : R, Ideal.Quotient.mk P x = z ∧ x - 1 ∈ m ∧
      IsCoprime (span {x}) (P * m) := by
  let e := quotientMulEquivQuotientProd P m h
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm ((z : R ⧸ P), 1))
  have he : e (Ideal.Quotient.mk (P * m) x) = ((z : R ⧸ P), 1) := by rw [hx, e.apply_symm_apply]
  have hP : Ideal.Quotient.mk P x = z := by simpa [e] using congrArg Prod.fst he
  have hm : Ideal.Quotient.mk m x = 1 := by simpa [e] using congrArg Prod.snd he
  refine ⟨x, hP, Ideal.Quotient.eq.mp (hm.trans (map_one _).symm), ?_⟩
  apply IsCoprime.mul_right
  · exact ((isUnit_mk_iff_coprime_span P x).mp (hP ▸ z.isUnit)).symm
  · exact ((isUnit_mk_iff_coprime_span m x).mp (hm ▸ isUnit_one)).symm

/-- For a squarefree conductor, nontrivial local characters give the required
prime tests by Chinese remaindering. Only their values on lifts congruent to one
at the complementary conductor are needed. -/
theorem isPrimitiveRayCharacter_of_local_characters {f : Ideal (𝓞 K)} {χ : Ideal (𝓞 K) →*₀ ℂ}
    (hχ : IsRayCharacter f χ) (hf : Squarefree f)
    (hlocal : ∀ P m : Ideal (𝓞 K), Prime P → f = P * m →
      ∃ ρ : MulChar ((𝓞 K) ⧸ P) ℂ, ρ ≠ 1 ∧
        ∀ x : 𝓞 K, IsCoprime (span {x}) f → x - 1 ∈ m → χ (span {x}) = ρ (Ideal.Quotient.mk P x)) :
    IsPrimitiveRayCharacter f χ := by
  apply isPrimitiveRayCharacter_of_prime_tests hχ
  intro P m hp hfactor
  obtain ⟨ρ, hρ, hval⟩ := hlocal P m hp hfactor
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hρ
  have hcop : IsCoprime P m := isCoprime_iff_sup_eq.mpr <| Ideal.isUnit_iff.mp <|
    IsRelPrime.of_squarefree_mul (hfactor ▸ hf) (dvd_iff_le.mpr le_sup_left)
      (dvd_iff_le.mpr le_sup_right)
  obtain ⟨x, hx, hm, hc⟩ := exists_prime_test hcop u
  rw [← hfactor] at hc
  exact ⟨x, hc, hm, by rwa [hval _ hc hm, hx]⟩

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The quadratic residue character at a good prime has order two. -/
theorem orderOf_sexticChar_cube {P : Ideal 𝓔} (hP : AwayFromSix P) (hp : Prime P) :
    orderOf (sexticChar hP ^ 3) = 2 := by
  rw [orderOf_pow' _ (by decide : 3 ≠ 0), orderOf_sexticChar_prime hP hp]
  decide

theorem sexticChar_cube_ne_one {P : Ideal 𝓔} (hP : AwayFromSix P) (hp : Prime P) :
    sexticChar hP ^ 3 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by decide) (by rw [orderOf_sexticChar_prime hP hp]; decide)

theorem exists_sexticChar_cube_ne_one {P : Ideal 𝓔} (hP : AwayFromSix P) (hp : Prime P) :
    ∃ u : (𝓔 ⧸ P)ˣ, (sexticChar hP) (u : 𝓔 ⧸ P) ^ 3 ≠ 1 := by
  simpa only [MulChar.pow_apply' _ (by decide : 3 ≠ 0)] using
    MulChar.ne_one_iff.mp (sexticChar_cube_ne_one hP hp)

end Masullo.QRH.MeanSquare
