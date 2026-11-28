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

/-- The conductor norm bound used for the initial estimate in Goldmakher–Louvel, §4. -/
theorem absNorm_quadraticConductor_le (b : Ideal 𝓔) :
    absNorm (quadraticConductor b) ≤ 3 * absNorm b := by
  unfold quadraticConductor
  split
  · omega
  · rw [map_mul, absNorm_lambdaIdeal, Nat.mul_comm]

open Classical in
def correctedQuadratic {n : Ideal 𝓔} (hn : AwayFromSix n) : 𝓔 →* ℂ :=
  if sextic n (-1) ^ 3 = 1 then quadraticResidue hn else quadraticResidue hn
    * lambdaSign.toMonoidHom

@[simp] private lemma lambdaSign_toMonoidHom (x : 𝓔) : lambdaSign.toMonoidHom x =
    lambdaSign x := rfl

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

private theorem correctedQuadratic_primary {n : Ideal 𝓔} (hn : AwayFromSix n) {x : 𝓔}
    (hx : eisPrimary x) : correctedQuadratic hn x = quadraticResidue hn x := by
  classical
  unfold correctedQuadratic
  split <;> simp only [MonoidHom.mul_apply, lambdaSign_toMonoidHom,
    lambdaSign_eq_one_of_eisPrimary hx, mul_one]

lemma quadraticIdealCharacter_good {n a : Ideal 𝓔} (hn : AwayFromSix n) (ha : AwayFromSix a) :
    quadraticIdealCharacter hn a = primaryQuadraticSymbol a n := by
  rw [quadraticIdealCharacter_apply hn ha.1,
    correctedQuadratic_primary hn (eisPrimary_generator ha.coprime_three)]
  exact quadraticResidue_apply hn _

/-- The character is multiplicative in its index on ideals prime to six, as used in
Goldmakher–Louvel, proof of Lemma 5.1, and §6.1, to split off a common factor of two indices. -/
theorem quadraticIdealCharacter_mul {g b a : Ideal 𝓔} (hg : AwayFromSix g) (hb : AwayFromSix b)
    (ha : AwayFromSix a) :
    quadraticIdealCharacter (hg.mul hb) a =
      quadraticIdealCharacter hg a * quadraticIdealCharacter hb a := by
  have hx := eisPrimary_generator ha.coprime_three
  rw [quadraticIdealCharacter_apply _ ha.1, quadraticIdealCharacter_apply _ ha.1,
    quadraticIdealCharacter_apply _ ha.1, correctedQuadratic_primary _ hx,
    correctedQuadratic_primary _ hx, correctedQuadratic_primary _ hx,
    quadraticResidue_den_mul]

/-- Every prime of `n` divides the conductor. -/
theorem dvd_quadraticConductor (n : Ideal 𝓔) : n ∣ quadraticConductor n := by
  unfold quadraticConductor
  split
  · exact dvd_rfl
  · exact dvd_mul_right n _

/-- The conductor has no prime outside `n` other than the ramified prime above three. -/
theorem quadraticConductor_dvd (n : Ideal 𝓔) : quadraticConductor n ∣ n * lambdaIdeal := by
  unfold quadraticConductor
  split
  · exact dvd_mul_right n _
  · exact dvd_rfl

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

/-- On ideals prime to six the character vanishes exactly at the ideals sharing a prime with
the index. The duality step of Goldmakher–Louvel, §4, Lemma 4.5, needs this zero set. -/
theorem quadraticIdealCharacter_eq_zero_iff {n a : Ideal 𝓔} (hn : AwayFromSix n)
    (ha : AwayFromSix a) : quadraticIdealCharacter hn a = 0 ↔ ¬ IsCoprime a n := by
  have hl : IsCoprime a lambdaIdeal :=
    ha.coprime_three.of_isCoprime_of_dvd_right lambdaIdeal_dvd_three
  have h := ((quadraticIdealCharacter_isRay hn).2.1 a).not
  rw [not_not, not_and_or, not_not, or_iff_right (show a ≠ 0 from ha.1)] at h
  rw [h, not_iff_not]
  exact ⟨fun hc => hc.of_isCoprime_of_dvd_right (dvd_quadraticConductor n),
    fun hc => (hc.mul_right hl).of_isCoprime_of_dvd_right (quadraticConductor_dvd n)⟩

private lemma prime_test_nonzero {P m : Ideal 𝓔} (hp : Prime P) {x : 𝓔}
    (hc : IsCoprime (span {x}) (P * m)) : x ≠ 0 := by
  rintro rfl
  have h := hc.of_mul_right_left
  exact hp.not_isUnit (isCoprime_zero_left.mp
    (by simpa only [span_singleton_zero, Ideal.zero_eq_bot] using h))

private lemma quadratic_prime_test {P m n : Ideal 𝓔} (hn : AwayFromSix n)
    (hp : Prime P) (hP : AwayFromSix P) (hc : IsCoprime P m)
    (hlocal : ∀ x : 𝓔, x - 1 ∈ m → correctedQuadratic hn x = quadraticResidue hP x) :
    ∃ x : 𝓔, IsCoprime (span {x}) (P * m) ∧ x - 1 ∈ m ∧ quadraticIdealCharacter hn
      (span {x}) ≠ 1 := by
  obtain ⟨z, hz⟩ := exists_sexticChar_cube_ne_one hP hp
  obtain ⟨x, hx, hm, hxm⟩ := exists_prime_test hc z
  refine ⟨x, hxm, hm, ?_⟩
  rw [quadraticIdealCharacter, idealCharacterOfElement_span _ _ (prime_test_nonzero hp
    hxm), hlocal x hm]
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
    have hsf : Squarefree (P * m) := hfac ▸ squarefree_mul_iff.mpr ⟨hram.isRelPrime,
      hn.2, lambdaIdeal_prime.squarefree⟩
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
    · have heq : P = lambdaIdeal := associated_iff_eq.mp (hp.associated_of_dvd
        lambdaIdeal_prime hpl)
      subst P
      have hm : n = m := mul_left_cancel₀ lambdaIdeal_prime.ne_zero (by rwa [mul_comm n] at hfac)
      obtain ⟨x, hx, hx₁, hxc⟩ := exists_prime_test hcop (-1)
      refine ⟨x, hxc, hx₁, ?_⟩
      rw [quadraticIdealCharacter, idealCharacterOfElement_span _ _ (prime_test_nonzero
        lambdaIdeal_prime hxc),
        correctedQuadratic, ite_eq_right he, MonoidHom.mul_apply, quadraticResidue_congr hn.1
          (hm.symm ▸ hx₁),
        map_one, one_mul]
      have hxneg : Ideal.Quotient.mk lambdaIdeal x = Ideal.Quotient.mk _ (-1) := by simpa using hx
      change lambdaSign x ≠ 1
      rw [lambdaSign_congr (mem_span_singleton.mp (Ideal.Quotient.eq.mp hxneg)), lambdaSign_neg_one]
      norm_num

open UniqueFactorizationMonoid in
private theorem quadraticIdealCharacter_separate {b c : Ideal 𝓔} (hb : Starred b) (hc : Starred c)
    (hbc : ¬ b ∣ c) :
    ∃ a : Ideal 𝓔, AwayFromSix a ∧ IsCoprime a b ∧ IsCoprime a c ∧
      quadraticIdealCharacter hb.1 a = -1 ∧ quadraticIdealCharacter hc.1 a = 1 := by
  classical
  have hP : ∃ P : Ideal 𝓔, Prime P ∧ P ∣ b ∧ ¬ P ∣ c := by
    by_contra! h
    apply hbc
    apply (dvd_iff_normalizedFactors_le_normalizedFactors hb.1.1 hc.1.1).mpr
    apply (Multiset.le_iff_subset ((squarefree_iff_nodup_normalizedFactors hb.1.1).mp hb.2)).mpr
    intro P hPb
    obtain ⟨hp, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hb.1.1).mp hPb
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hc.1.1).mpr ⟨hp, h P hp hdiv⟩
  obtain ⟨P, hp, ⟨d, hbd⟩, hPc⟩ := hP
  have hP := away_of_dvd hb.1 (show P ∣ b from ⟨d, hbd⟩)
  have hd := away_of_dvd hb.1 (hbd ▸ dvd_mul_left d P)
  have hcop : IsCoprime P c := isCoprime_iff_sup_eq.mpr <| Ideal.isUnit_iff.mp <|
    (hp.irreducible.isRelPrime_iff_not_dvd.mpr hPc)
      (dvd_iff_le.mpr le_sup_left) (dvd_iff_le.mpr le_sup_right)
  let m := d * (c * span {(6 : 𝓔)})
  have hPm : IsCoprime P m := (coprime_factors (hbd ▸ hb.2)).mul_right (hcop.mul_right hP.2)
  have hprim {x : 𝓔} (hx : x - 1 ∈ m) : eisPrimary x :=
    dvd_trans (show (3 : 𝓔) ∣ 6 from ⟨2, by norm_num⟩)
      (mem_span_singleton.mp (Ideal.mul_le_right (Ideal.mul_le_right hx)))
  obtain ⟨x, hx, hxm, hxne⟩ := quadratic_prime_test hb.1 hp hP hPm (fun x hx => by
    rw [correctedQuadratic_primary hb.1 (hprim hx)]
    subst b
    rw [quadraticResidue_den_mul hP hd, quadraticResidue_congr hd (Ideal.mul_le_left hx),
      map_one, mul_one])
  have hx₀ := prime_test_nonzero hp hx
  obtain ⟨hxP, hxm'⟩ := IsCoprime.mul_right_iff.mp hx
  obtain ⟨hxd, hxc₆⟩ := IsCoprime.mul_right_iff.mp hxm'
  obtain ⟨hxc, hx₆⟩ := IsCoprime.mul_right_iff.mp hxc₆
  have hxa : IsCoprime (span {x}) b := hbd ▸ hxP.mul_right hxd
  have hgood : AwayFromSix (span {x}) := ⟨by simpa using hx₀, hx₆⟩
  have hxval (n : Ideal 𝓔) (hn : AwayFromSix n) :
      quadraticIdealCharacter hn (span {x}) = quadraticResidue hn x := by
    rw [quadraticIdealCharacter, idealCharacterOfElement_span _ _ hx₀,
      correctedQuadratic_primary hn (hprim hxm)]
  refine ⟨_, hgood, hxa, hxc, ?_, ?_⟩
  · have hs : quadraticIdealCharacter hb.1 (span {x}) ^ 2 = 1 := by
      rw [hxval b hb.1]; exact quadraticResidue_sq hb.1 hxa.symm
    exact (sq_eq_one_iff.mp hs).resolve_left hxne
  · rw [hxval c hc.1, quadraticResidue_congr hc.1 (Ideal.mul_le_left (Ideal.mul_le_right
      hxm)), map_one]

/-- For distinct squarefree indices `b ≠ c`, the product of `quadraticIdealCharacter` at `b`
and the conjugate at `c` has value `-1` on an ideal coprime to six and to both indices, as
required in Goldmakher–Louvel, §4, (E₂). The family form is
`eisensteinQuadraticCharacter_product_nonprincipal`. -/
theorem quadraticIdealCharacter_product_nonprincipal {b c : Ideal 𝓔}
    (hb : Starred b) (hc : Starred c) (hne : b ≠ c) :
    ∃ a : Ideal 𝓔, AwayFromSix a ∧ IsCoprime a b ∧ IsCoprime a c ∧
      quadraticIdealCharacter hb.1 a * star (quadraticIdealCharacter hc.1 a) = -1 := by
  by_cases hbc : b ∣ c
  · have hcb : ¬ c ∣ b := fun h => hne (le_antisymm (le_of_dvd h) (le_of_dvd hbc))
    obtain ⟨a, ha, hac, hab, he, hf⟩ := quadraticIdealCharacter_separate hc hb hcb
    exact ⟨a, ha, hab, hac, by simp [he, hf]⟩
  · obtain ⟨a, ha, hab, hac, he, hf⟩ := quadraticIdealCharacter_separate hb hc hbc
    exact ⟨a, ha, hab, hac, by simp [he, hf]⟩

end Masullo.QRH.MeanSquare
