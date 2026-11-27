import Masullo.QRH.MeanSquare.Eisenstein

/-! # The sextic symbol on a sixth-power row -/

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private theorem omega_primitive : IsPrimitiveRoot eisOmega 3 :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)).toInteger_isPrimitiveRoot

private theorem neg_omega_primitive : IsPrimitiveRoot (-eisOmega) 6 := by
  have h := (Polynomial.isRoot_cyclotomic_iff.mpr omega_primitive)
  rw [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] at h
  apply Polynomial.isRoot_cyclotomic_iff.mp
  simpa [Polynomial.cyclotomic_six, Polynomial.IsRoot.def] using h

private theorem local_sixth {P : Ideal 𝓔} (hp : Prime P) (h6 : (6 : 𝓔) ∉ P)
    (k : 𝓔) (hk : k ∉ P) : primePowerResidueSymbol 6 (k ^ 6) P = 1 := by
  classical
  have hP := (Ideal.prime_iff_isPrime hp.ne_zero).mp hp
  let : P.IsMaximal := hP.isMaximal hp.ne_zero
  let := Ideal.Quotient.field P
  let := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ P)
  let f := Ideal.Quotient.mk P
  have : NeZero ((6 : ℕ) : 𝓔 ⧸ P) := ⟨by
    simpa only [Nat.cast_ofNat, ← map_ofNat f 6, f, ne_eq, Ideal.Quotient.eq_zero_iff_mem] using h6⟩
  have hz : IsPrimitiveRoot (f (-eisOmega)) 6 := by
    apply Polynomial.isRoot_cyclotomic_iff.mp
    simpa only [Polynomial.map_cyclotomic] using
      (Polynomial.isRoot_cyclotomic_iff.mpr neg_omega_primitive).map f
  have hF (a : 𝓔 ⧸ P) (ha : a ≠ 0) : a ^ (absNorm P - 1) = 1 := by
    simpa only [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one a ha
  have hdiv := hz.dvd_of_pow_eq_one _ (hF _ (hz.ne_zero (by decide)))
  have hpow : f ((k ^ 6) ^ ((absNorm P - 1) / 6)) = 1 := by
    rw [← pow_mul, Nat.mul_div_cancel' hdiv, map_pow]
    exact hF _ (fun h => hk (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hw : ∃ u : 𝓔, u ^ 6 = 1 ∧ (k ^ 6) ^ ((absNorm P - 1) / 6) - u ∈ P :=
    ⟨1, one_pow _, Ideal.Quotient.eq.mp (hpow.trans (map_one f).symm)⟩
  have hchosen : f hw.choose = 1 := (Ideal.Quotient.eq.mpr hw.choose_spec.2).symm.trans hpow
  obtain ⟨i, hi, heq⟩ := neg_omega_primitive.eq_pow_of_pow_eq_one hw.choose_spec.1
  have hi0 : 6 ∣ i := hz.dvd_of_pow_eq_one _ (by rw [← map_pow, heq, hchosen])
  have hi' : i = 0 := by omega
  have hk' : k ^ 6 ∉ P := fun h => hk (hP.mem_of_pow_mem _ h)
  simpa [primePowerResidueSymbol, hk', hw, hi'] using heq.symm

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
    have hmem (a : 𝓔) (h : IsCoprime n (span {a})) : a ∉ P := fun ha => hp.not_isUnit
      (h.isUnit_of_dvd' hd (dvd_iff_le.mpr ((span_singleton_le_iff_mem _).mpr ha)))
    exact local_sixth hp (hmem 6 h6) k (hmem k hc)
  · rw [ite_eq_right hc]
    obtain ⟨P, hm, hle⟩ := exists_le_maximal _ (mt isCoprime_iff_sup_eq.mpr hc)
    have hd : P ∣ n := dvd_iff_le.mpr (le_sup_left.trans hle)
    have hP : P ≠ ⊥ := fun h => hn (by simpa [h] using (dvd_iff_le.mp hd))
    have hp : Prime P := (Ideal.prime_iff_isPrime hP).mpr hm.isPrime
    have hk : k ∈ P := (span_singleton_le_iff_mem _).mp (le_sup_right.trans hle)
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨P,
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mpr ⟨hp, hd⟩, by
      simp [primePowerResidueSymbol, P.pow_mem_of_mem hk 6 (by decide)]⟩)

end Masullo.QRH.MeanSquare
