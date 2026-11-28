import Masullo.QRH.MeanSquare.Forms

/-! # Cubic and sextic residue characters -/

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

theorem omega_primitive : IsPrimitiveRoot eisOmega 3 :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)).toInteger_isPrimitiveRoot

theorem neg_omega_primitive : IsPrimitiveRoot (-eisOmega) 6 := by
  have h := (Polynomial.isRoot_cyclotomic_iff.mpr omega_primitive)
  rw [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] at h
  apply Polynomial.isRoot_cyclotomic_iff.mp
  simpa [Polynomial.cyclotomic_six, Polynomial.IsRoot.def] using h

theorem primitive_mod_prime {P : Ideal 𝓔} (hp : Prime P) {d : ℕ} [NeZero d]
    (hd : (d : 𝓔) ∉ P) {ζ : 𝓔} (hζ : IsPrimitiveRoot ζ d) :
    IsPrimitiveRoot (Ideal.Quotient.mk P ζ) d := by
  let : P.IsPrime := (Ideal.prime_iff_isPrime hp.ne_zero).mp hp
  let f := Ideal.Quotient.mk P
  have : NeZero ((d : ℕ) : 𝓔 ⧸ P) := ⟨fun h => hd (Ideal.Quotient.eq_zero_iff_mem.mp
    ((map_natCast f d).trans h))⟩
  apply Polynomial.isRoot_cyclotomic_iff.mp
  simpa only [Polynomial.map_cyclotomic] using
    (Polynomial.isRoot_cyclotomic_iff.mpr hζ).map f

theorem order_dvd_norm_sub_one {P : Ideal 𝓔} (hp : Prime P) {d : ℕ} [NeZero d]
    {ζ : 𝓔} (hz : IsPrimitiveRoot (Ideal.Quotient.mk P ζ) d) : d ∣ absNorm P - 1 := by
  let : P.IsMaximal := ((Ideal.prime_iff_isPrime hp.ne_zero).mp hp).isMaximal hp.ne_zero
  let := Ideal.Quotient.field P
  let := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ P)
  apply hz.dvd_of_pow_eq_one
  simpa only [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card] using
    FiniteField.pow_card_sub_one_eq_one _ (hz.ne_zero (NeZero.ne d))

private theorem root_lift_unique {P : Ideal 𝓔} {d : ℕ} [NeZero d]
    {ζ u v : 𝓔} (hζ : IsPrimitiveRoot ζ d) (hz : IsPrimitiveRoot (Ideal.Quotient.mk P ζ) d)
    (hu : u ^ d = 1) (hv : v ^ d = 1)
    (he : Ideal.Quotient.mk P u = Ideal.Quotient.mk P v) : u = v := by
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hu
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hv
  simp only [map_pow] at he
  rw [hz.pow_inj hi hj he]

theorem primePowerResidueSymbol_spec {P : Ideal 𝓔} (hp : Prime P)
    {d : ℕ} [NeZero d] (hd : (d : 𝓔) ∉ P) {ζ : 𝓔} (hζ : IsPrimitiveRoot ζ d)
    {a : 𝓔} (ha : a ∉ P) :
    primePowerResidueSymbol d a P ^ d = 1 ∧ Ideal.Quotient.mk P (primePowerResidueSymbol d a P) =
      Ideal.Quotient.mk P a ^ ((absNorm P - 1) / d) := by
  classical
  let : P.IsMaximal := ((Ideal.prime_iff_isPrime hp.ne_zero).mp hp).isMaximal hp.ne_zero
  let := Ideal.Quotient.field P
  let := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ P)
  let f := Ideal.Quotient.mk P
  have hz := primitive_mod_prime hp hd hζ
  have hdiv := order_dvd_norm_sub_one hp hz
  have hq : (f a ^ ((absNorm P - 1) / d)) ^ d = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hdiv]
    simpa only [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one _ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h) : f a ≠ 0)
  obtain ⟨i, _, hi⟩ := hz.eq_pow_of_pow_eq_one hq
  have hw : ∃ u : 𝓔, u ^ d = 1 ∧ a ^ ((absNorm P - 1) / d) - u ∈ P :=
    ⟨ζ ^ i, by rw [pow_right_comm, hζ.pow_eq_one, one_pow],
      Ideal.Quotient.eq.mp (by simpa only [map_pow] using hi.symm)⟩
  rw [primePowerResidueSymbol, ite_eq_right ha, dite_eq_left hw]
  exact ⟨hw.choose_spec.1, by simpa only [map_pow] using (Ideal.Quotient.eq.mpr hw.choose_spec.2).symm⟩

private theorem primePowerResidueSymbol_mul {P : Ideal 𝓔} (hp : Prime P)
    {d : ℕ} [NeZero d] (hd : (d : 𝓔) ∉ P) {ζ : 𝓔} (hζ : IsPrimitiveRoot ζ d)
    (a b : 𝓔) : primePowerResidueSymbol d (a * b) P =
      primePowerResidueSymbol d a P * primePowerResidueSymbol d b P := by
  classical
  have hP := (Ideal.prime_iff_isPrime hp.ne_zero).mp hp
  by_cases ha : a ∈ P
  · simp [primePowerResidueSymbol, ha, P.mul_mem_right b ha]
  by_cases hb : b ∈ P
  · simp [primePowerResidueSymbol, hb, P.mul_mem_left a hb]
  have hab := fun h => (hP.mem_or_mem h).elim ha hb
  obtain ⟨hau, haeq⟩ := primePowerResidueSymbol_spec hp hd hζ ha
  obtain ⟨hbu, hbeq⟩ := primePowerResidueSymbol_spec hp hd hζ hb
  obtain ⟨habu, habeq⟩ := primePowerResidueSymbol_spec hp hd hζ hab
  exact root_lift_unique hζ (primitive_mod_prime hp hd hζ) habu (by simp [mul_pow, hau, hbu])
    (by simp [habeq, haeq, hbeq, mul_pow])

private theorem primePowerResidueSymbol_sq {P : Ideal 𝓔} (hp : Prime P) (h6 : (6 : 𝓔) ∉ P)
    (a : 𝓔) : primePowerResidueSymbol 6 a P ^ 2 = primePowerResidueSymbol 3 a P := by
  classical
  by_cases ha : a ∈ P
  · simp [primePowerResidueSymbol, ha]
  have h3 : (3 : 𝓔) ∉ P := fun h => h6 (by convert P.mul_mem_left 2 h using 1; norm_num)
  obtain ⟨hu, he⟩ := primePowerResidueSymbol_spec hp h6 neg_omega_primitive ha
  obtain ⟨hv, hf⟩ := primePowerResidueSymbol_spec hp h3 omega_primitive ha
  have hd := order_dvd_norm_sub_one hp (primitive_mod_prime hp h6 neg_omega_primitive)
  apply root_lift_unique omega_primitive (primitive_mod_prime hp h3 omega_primitive) _ hv
  · rw [map_pow, he, hf, ← pow_mul]
    congr 1
    obtain ⟨j, hj⟩ := hd
    rw [hj, Nat.mul_comm 6 j, Nat.mul_div_cancel _ (by decide : 0 < 6),
      show j * 6 = j * 2 * 3 by omega, Nat.mul_div_cancel _ (by decide : 0 < 3)]
  · simpa only [← pow_mul] using hu

private theorem factor_notMem {n P : Ideal 𝓔} {a : 𝓔}
    (hp : Prime P) (hd : P ∣ n) (hc : IsCoprime n (span {a})) : a ∉ P :=
  fun ha => hp.not_isUnit
    (hc.isUnit_of_dvd' hd (dvd_iff_le.mpr ((span_singleton_le_iff_mem _).mpr ha)))

/-- The symbols multiply in the denominator, including multiplicities at common primes. -/
theorem powerResidueSymbol_mul_right (d : ℕ) (a : 𝓔) (m n : Ideal 𝓔) :
    powerResidueSymbol d a (m * n) = powerResidueSymbol d a m * powerResidueSymbol d a n := by
  classical
  by_cases hm : m = ⊥
  · simp [hm, powerResidueSymbol]
  by_cases hn : n = ⊥
  · simp [hn, powerResidueSymbol]
  simp [powerResidueSymbol, hm, hn, normalizedFactors_mul hm hn]

/-- The numerator can be evaluated at any representative modulo its denominator. -/
theorem powerResidueSymbol_congr {d : ℕ} {n : Ideal 𝓔} {a b : 𝓔}
    (h : Ideal.Quotient.mk n a = Ideal.Quotient.mk n b) :
    powerResidueSymbol d a n = powerResidueSymbol d b n := by
  classical
  by_cases hn : n = ⊥
  · simp [powerResidueSymbol, hn]
  simp only [powerResidueSymbol, ite_eq_right hn]
  apply congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro P hP
  have hd := ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP).2
  have he := Ideal.Quotient.eq.mpr ((dvd_iff_le.mp hd) (Ideal.Quotient.eq.mp h))
  have hm : a ∈ P ↔ b ∈ P := by simp only [← Ideal.Quotient.eq_zero_iff_mem, he]
  unfold primePowerResidueSymbol
  simp only [hm, ← Ideal.Quotient.eq, map_pow, he]

private theorem residueSymbol_mul {d : ℕ} [NeZero d] {ζ : 𝓔} (hζ : IsPrimitiveRoot ζ d)
    {n : Ideal 𝓔} (hd : IsCoprime n (span {(d : 𝓔)})) (a b : 𝓔) :
    powerResidueSymbol d (a * b) n = powerResidueSymbol d a n * powerResidueSymbol d b n := by
  classical
  by_cases hn : n = ⊥
  · simp [powerResidueSymbol, hn]
  simp only [powerResidueSymbol, ite_eq_right hn, ← Multiset.prod_map_mul]
  apply congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro P hP
  obtain ⟨hp, hpn⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
  exact primePowerResidueSymbol_mul hp (factor_notMem hp hpn hd) hζ a b

theorem powerResidueSymbol_six_mul {n : Ideal 𝓔} (h6 : IsCoprime n (span {6})) (a b : 𝓔) :
    powerResidueSymbol 6 (a * b) n = powerResidueSymbol 6 a n * powerResidueSymbol 6 b n :=
  residueSymbol_mul neg_omega_primitive h6 a b

theorem powerResidueSymbol_three_mul {n : Ideal 𝓔} (h3 : IsCoprime n (span {3})) (a b : 𝓔) :
    powerResidueSymbol 3 (a * b) n = powerResidueSymbol 3 a n * powerResidueSymbol 3 b n :=
  residueSymbol_mul omega_primitive h3 a b

/-- Squaring a sextic symbol gives the cubic symbol with the same denominator. -/
theorem powerResidueSymbol_six_sq {n : Ideal 𝓔} (h6 : IsCoprime n (span {6})) (a : 𝓔) :
    powerResidueSymbol 6 a n ^ 2 = powerResidueSymbol 3 a n := by
  classical
  by_cases hn : n = ⊥
  · simp [powerResidueSymbol, hn]
  simp only [powerResidueSymbol, ite_eq_right hn, ← Multiset.prod_map_pow]
  apply congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro P hP
  obtain ⟨hp, hpn⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
  exact primePowerResidueSymbol_sq hp (factor_notMem hp hpn h6) a

private theorem local_sixth {P : Ideal 𝓔} (hp : Prime P) (h6 : (6 : 𝓔) ∉ P)
    (k : 𝓔) (hk : k ∉ P) : primePowerResidueSymbol 6 (k ^ 6) P = 1 := by
  have hP := (Ideal.prime_iff_isPrime hp.ne_zero).mp hp
  obtain ⟨hu, he⟩ := primePowerResidueSymbol_spec hp h6 neg_omega_primitive
    (show k ^ 6 ∉ P from fun h => hk (hP.mem_of_pow_mem _ h))
  obtain ⟨hv, hf⟩ := primePowerResidueSymbol_spec hp h6 neg_omega_primitive hk
  apply root_lift_unique neg_omega_primitive (primitive_mod_prime hp h6 neg_omega_primitive) hu
    (one_pow _)
  rw [he, map_pow, pow_right_comm, ← hf, ← map_pow, hv]

open Classical in
/-- A sixth-power numerator gives the coprimality indicator at every nonzero denominator prime
to six. Prime factors are counted with multiplicity, so this includes nonsquarefree denominators. -/
theorem powerResidueSymbol_sixth {n : Ideal 𝓔} (hn : n ≠ ⊥) (h6 : IsCoprime n (span {6}))
    (k : 𝓔) : powerResidueSymbol 6 (k ^ 6) n = if IsCoprime n (span {k}) then 1 else 0 := by
  classical
  rw [powerResidueSymbol, ite_eq_right hn]
  by_cases hc : IsCoprime n (span {k})
  · rw [ite_eq_left hc]
    refine Multiset.prod_eq_one (fun x hx => ?_)
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨hp, hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
    exact local_sixth hp (factor_notMem hp hd h6) k (factor_notMem hp hd hc)
  · rw [ite_eq_right hc]
    obtain ⟨P, hm, hle⟩ := exists_le_maximal _ (mt isCoprime_iff_sup_eq.mpr hc)
    have hd : P ∣ n := dvd_iff_le.mpr (le_sup_left.trans hle)
    have hP : P ≠ ⊥ := fun h => hn (by simpa [h] using (dvd_iff_le.mp hd))
    have hp : Prime P := (Ideal.prime_iff_isPrime hP).mpr hm.isPrime
    have hk : k ∈ P := (span_singleton_le_iff_mem _).mp (le_sup_right.trans hle)
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨P,
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mpr ⟨hp, hd⟩, by
      simp [primePowerResidueSymbol, P.pow_mem_of_mem hk 6 (by decide)]⟩)

open Classical in
/-- On good denominators the sixth power of the symbol detects invertible numerators. -/
theorem powerResidueSymbol_six_pow_six {n : Ideal 𝓔} (hn : n ≠ ⊥)
    (h6 : IsCoprime n (span {6})) (a : 𝓔) :
    powerResidueSymbol 6 a n ^ 6 = if IsCoprime n (span {a}) then 1 else 0 := by
  rw [← powerResidueSymbol_sixth hn h6]
  simp only [show (6 : ℕ) = 3 + 3 by decide, pow_add, pow_three, powerResidueSymbol_six_mul h6]

/-- A coprime numerator is invertible in the quotient by the denominator. -/
lemma isUnit_mk_iff_coprime_span {R : Type*} [CommRing R] (n : Ideal R) (a : R) :
    IsUnit (Ideal.Quotient.mk n a) ↔ IsCoprime n (span {a}) := by
  rw [isUnit_iff_dvd_one, Ideal.isCoprime_iff_exists]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨1 - a * b, Ideal.Quotient.eq_zero_iff_mem.mp ?_, a * b,
      mem_span_singleton.mpr (dvd_mul_right a b), sub_add_cancel _ _⟩
    simp [hx.symm, map_one, map_sub, map_mul]
  · rintro ⟨i, hi, j, hj, h⟩
    obtain ⟨b, rfl⟩ := mem_span_singleton.mp hj
    refine ⟨Ideal.Quotient.mk n b, ?_⟩
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hi] using congrArg (Ideal.Quotient.mk n) h.symm

/-- The sextic symbol as a multiplicative character on the quotient by a good ideal. -/
noncomputable def sexticChar {n : Ideal 𝓔} (hn : AwayFromSix n) : MulChar (𝓔 ⧸ n) ℂ := by
  classical
  let χ := fun x : 𝓔 ⧸ n => sextic n (Quotient.out x)
  have hχ (a : 𝓔) : χ (Ideal.Quotient.mk n a) = sextic n a :=
    congrArg eisEmbedding (powerResidueSymbol_congr (Ideal.Quotient.mk_out _))
  refine { toFun := χ, map_one' := ?_, map_mul' := ?_, map_nonunit' := ?_ }
  · rw [← map_one (Ideal.Quotient.mk n), hχ]
    have h := powerResidueSymbol_sixth hn.1 hn.2 1
    have hc : IsCoprime n (span {(1 : 𝓔)}) := (isUnit_mk_iff_coprime_span n 1).mp (by simp)
    simpa only [sextic, one_pow, ite_eq_left hc, map_one] using congrArg eisEmbedding h
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [← map_mul, hχ, sextic, powerResidueSymbol_six_mul hn.2]
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hc := (isUnit_mk_iff_coprime_span n a).mpr.mt hx
    have hz : powerResidueSymbol 6 a n ^ 6 = 0 := by
      simpa [hc] using powerResidueSymbol_six_pow_six hn.1 hn.2 a
    simp [hχ, sextic, eq_zero_of_pow_eq_zero hz]

@[simp] theorem sexticChar_apply_mk {n : Ideal 𝓔} (hn : AwayFromSix n) (a : 𝓔) :
    sexticChar hn (Ideal.Quotient.mk n a) = sextic n a :=
  congrArg eisEmbedding (powerResidueSymbol_congr (Ideal.Quotient.mk_out _))

@[simp] theorem norm_sextic_of_coprime {n : Ideal 𝓔} (hn : AwayFromSix n) {a : 𝓔}
    (ha : IsCoprime n (span {a})) : ‖sextic n a‖ = 1 := by
  have h := congrArg eisEmbedding (powerResidueSymbol_six_pow_six hn.1 hn.2 a)
  simp only [ite_eq_left ha, map_pow, map_one] at h
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, h⟩).norm_eq_one

end Masullo.QRH.MeanSquare
