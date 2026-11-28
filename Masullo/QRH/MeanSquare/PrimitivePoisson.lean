import Masullo.QRH.MeanSquare.GaussJacobi
import Masullo.QRH.MeanSquare.PrimitivePoissonSteps

/-! # The primitive Poisson formula for the paired sextic character

For coprime squarefree `b, c` prime to six, `χ = pairCharacter b c` is a primitive character
modulo `n = b c`. Its finite Fourier transform separates as
`twistedGauss χ n (generator n) k = conj (χ k) · √(N n) · pairGauss b c`
(`twistedGauss_pairCharacter`). A Möbius exclusion over the divisors of `g` combined with
`hasSum_twisted_poisson` gives `primitivePoisson`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma generator_mem' (n : Ideal 𝓔) : generator n ∈ n :=
  (span_singleton_le_iff_mem n).mp (span_generator n).le

/-! ### The sextic symbol and the paired character -/

lemma sextic_one {n : Ideal 𝓔} (hn : AwayFromSix n) : sextic n 1 = 1 := by
  have h := sexticChar_apply_mk hn 1
  rw [map_one, map_one] at h
  exact h.symm

lemma sextic_congr {n : Ideal 𝓔} {x y : 𝓔} (h : x - y ∈ n) : sextic n x = sextic n y :=
  congrArg eisEmbedding (powerResidueSymbol_congr (Ideal.Quotient.eq.mpr h))

lemma sextic_mul {n : Ideal 𝓔} (hn : AwayFromSix n) (x y : 𝓔) :
    sextic n (x * y) = sextic n x * sextic n y := by
  simp only [sextic, powerResidueSymbol_six_mul hn.2, map_mul]

lemma sextic_mul_right (m n : Ideal 𝓔) (x : 𝓔) : sextic (m * n) x = sextic m x * sextic n x := by
  simp only [sextic, powerResidueSymbol_mul_right, map_mul]

lemma sextic_eq_zero {n : Ideal 𝓔} (hn : AwayFromSix n) {x : 𝓔}
    (hx : ¬ IsCoprime n (span {x})) : sextic n x = 0 := by
  rw [← sexticChar_apply_mk hn]
  exact MulChar.map_nonunit _ fun h => hx ((isUnit_mk_iff_coprime_span n x).mp h)

lemma pairCharacter_congr {b c : Ideal 𝓔} {x y : 𝓔} (h : x - y ∈ b * c) :
    pairCharacter b c x = pairCharacter b c y := by
  rw [pairCharacter, pairCharacter, sextic_congr (Ideal.mul_le_right h),
    sextic_congr (Ideal.mul_le_left h)]

lemma pairCharacter_mul {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c) (x y : 𝓔) :
    pairCharacter b c (x * y) = pairCharacter b c x * pairCharacter b c y := by
  simp only [pairCharacter, sextic_mul hb, sextic_mul hc, map_mul]
  ring

lemma pairCharacter_one {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c) :
    pairCharacter b c 1 = 1 := by
  simp [pairCharacter, sextic_one hb, sextic_one hc]

lemma norm_pairCharacter {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c) {x : 𝓔}
    (hx : IsCoprime (b * c) (span {x})) : ‖pairCharacter b c x‖ = 1 := by
  rw [pairCharacter, norm_mul, Complex.norm_conj,
    norm_sextic_of_coprime hb (hx.of_isCoprime_of_dvd_left (dvd_mul_right b c)),
    norm_sextic_of_coprime hc (hx.of_isCoprime_of_dvd_left (dvd_mul_left c b)), one_mul]

lemma pairCharacter_eq_zero {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c) {x : 𝓔}
    (hx : ¬ IsCoprime (b * c) (span {x})) : pairCharacter b c x = 0 := by
  by_cases h : IsCoprime b (span {x})
  · simp [pairCharacter, sextic_eq_zero hc fun h' => hx (h.mul_left h')]
  · simp [pairCharacter, sextic_eq_zero hb h]

/-! ### Separation of the twisted Gauss sum -/

/-- Substituting `x ↦ a x` for `a` invertible modulo `n` in a sum over residues. -/
private lemma finsum_quotient_mul {n : Ideal 𝓔} {f : 𝓔 → ℂ}
    (hf : ∀ x y, x - y ∈ n → f x = f y) {a : 𝓔} (ha : IsCoprime n (span {a})) :
    ∑ᶠ x : 𝓔 ⧸ n, f (Quotient.out x) = ∑ᶠ x : 𝓔 ⧸ n, f (a * Quotient.out x) := by
  let u := ((isUnit_mk_iff_coprime_span n a).mpr ha).unit
  refine (finsum_comp_equiv u.mulLeft).symm.trans (finsum_congr fun x => hf _ _ ?_)
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, Units.mulLeft_apply, IsUnit.unit_spec, map_mul,
    Ideal.Quotient.mk_out]

private lemma twistedGauss_eq (b c : Ideal 𝓔) (k : 𝓔) :
    twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k =
      ∑ᶠ x : 𝓔 ⧸ (b * c), pairCharacter b c (Quotient.out x) *
        differentCharacter
          (eisEmbedding (k * Quotient.out x) / eisEmbedding (generator (b * c))) := by
  simp only [twistedGauss, map_mul]

private lemma generator_dvd_of_mem {n : Ideal 𝓔} {x : 𝓔} (h : x ∈ n) : generator n ∣ x := by
  rwa [← mem_span_singleton, span_generator]

/-- The twisted Gauss sum depends only on the frequency modulo `b c`. -/
private lemma twistedGauss_congr (b c : Ideal 𝓔) {k k' : 𝓔} (h : k - k' ∈ b * c) :
    twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k =
      twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k' := by
  rw [twistedGauss_eq, twistedGauss_eq]
  refine finsum_congr fun x => ?_
  rw [differentCharacter_div_congr (y := k' * Quotient.out x) (generator_dvd_of_mem ?_)]
  rw [← sub_mul]
  exact Ideal.mul_mem_right _ _ h

/-- Substituting `x ↦ a x` multiplies the frequency by `a`. -/
private lemma twistedGauss_mul {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c)
    {a : 𝓔} (ha : IsCoprime (b * c) (span {a})) (k : 𝓔) :
    twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k =
      pairCharacter b c a *
        twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) (k * a) := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient (hb.mul hc).1
  let := Fintype.ofFinite (𝓔 ⧸ (b * c))
  rw [twistedGauss_eq, twistedGauss_eq, finsum_quotient_mul (n := b * c) (a := a)
    (f := fun y => pairCharacter b c y *
      differentCharacter (eisEmbedding (k * y) / eisEmbedding (generator (b * c)))) ?_ ha]
  · simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, pairCharacter_mul hb hc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show k * (a * Quotient.out x) = k * a * Quotient.out x by ring]
    ring
  · intro x y h
    rw [pairCharacter_congr h,
      differentCharacter_div_congr (y := k * y) (generator_dvd_of_mem ?_)]
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ h

private lemma sqrt_absNorm_ne_zero {n : Ideal 𝓔} (hn : n ≠ ⊥) : Real.sqrt (absNorm n) ≠ 0 :=
  (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr hn)))).ne'

private lemma twistedGauss_one {b c : Ideal 𝓔} (h : b * c ≠ ⊥) :
    twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) 1 =
      Real.sqrt (absNorm (b * c)) * pairGauss b c := by
  rw [pairGauss, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (sqrt_absNorm_ne_zero h)),
    twistedGauss_eq]
  simp only [one_mul]

/-- At an invertible frequency the substitution `x ↦ k⁻¹ x` extracts `conj (χ k)`. -/
theorem twistedGauss_pairCharacter_of_coprime {b c : Ideal 𝓔} (hb : AwayFromSix b)
    (hc : AwayFromSix c) {k : 𝓔} (hk : IsCoprime (b * c) (span {k})) :
    twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k =
      conj (pairCharacter b c k) *
        twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) 1 := by
  obtain ⟨v, hv⟩ := ((isUnit_mk_iff_coprime_span _ k).mpr hk).exists_right_inv
  obtain ⟨k', rfl⟩ := Ideal.Quotient.mk_surjective v
  have h1 : k * k' - 1 ∈ b * c := Ideal.Quotient.eq.mp (by rw [map_mul, hv, map_one])
  have hk' : IsCoprime (b * c) (span {k'}) :=
    (isUnit_mk_iff_coprime_span _ k').mp
      (IsUnit.of_mul_eq_one (Ideal.Quotient.mk (b * c) k) ((mul_comm _ _).trans hv))
  have hχ : pairCharacter b c k * pairCharacter b c k' = 1 := by
    rw [← pairCharacter_mul hb hc, pairCharacter_congr h1, pairCharacter_one hb hc]
  have hconj : conj (pairCharacter b c k) = pairCharacter b c k' := by
    have hn : conj (pairCharacter b c k) * pairCharacter b c k = 1 := by
      rw [Complex.conj_mul', norm_pairCharacter hb hc hk]
      norm_num
    calc conj (pairCharacter b c k)
        = conj (pairCharacter b c k) * (pairCharacter b c k * pairCharacter b c k') := by
          rw [hχ, mul_one]
      _ = pairCharacter b c k' := by rw [← mul_assoc, hn, one_mul]
  rw [hconj, twistedGauss_mul hb hc hk', twistedGauss_congr b c h1]

/-- A frequency sharing a prime with a squarefree `b` admits a substitution that multiplies
`sextic b` by a nontrivial value and fixes `sextic c` and the frequency. -/
private lemma exists_twist {b c P : Ideal 𝓔} (hb : Starred b) (hc : AwayFromSix c)
    (hbc : IsCoprime b c) (hP : Prime P) (hPb : P ∣ b) :
    ∃ a : 𝓔, IsCoprime (b * c) (span {a}) ∧ (∀ k ∈ P, k * (a - 1) ∈ b * c) ∧
      sextic b a ≠ 1 ∧ sextic c a = 1 := by
  obtain ⟨b', rfl⟩ := hPb
  have hP6 : AwayFromSix P :=
    ⟨hP.ne_zero, hb.1.2.of_isCoprime_of_dvd_left (dvd_mul_right P b')⟩
  have hb' : AwayFromSix b' :=
    ⟨right_ne_zero_of_mul hb.1.1, hb.1.2.of_isCoprime_of_dvd_left (dvd_mul_left b' P)⟩
  have hPb' : IsCoprime P b' := isCoprime_iff_sup_eq.mpr <| Ideal.isUnit_iff.mp <|
    IsRelPrime.of_squarefree_mul hb.2 (dvd_iff_le.mpr le_sup_left) (dvd_iff_le.mpr le_sup_right)
  have hr : IsCoprime P (b' * c) :=
    hPb'.mul_right (hbc.of_isCoprime_of_dvd_left (dvd_mul_right P b'))
  have hne : sexticChar hP6 ≠ 1 := fun h => by
    have := orderOf_sexticChar_prime hP6 hP
    rw [h, orderOf_one] at this
    norm_num at this
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (u : 𝓔 ⧸ P)
  obtain ⟨p, hp, q, hq, hpq⟩ := isCoprime_iff_exists.mp hr
  have ha1 : t * q + p - 1 ∈ b' * c := by
    rw [show t * q + p - 1 = (t - 1) * q by linear_combination hpq]
    exact Ideal.mul_mem_left _ _ hq
  have hat : Ideal.Quotient.mk P (t * q + p) = u := by
    rw [← ht, Ideal.Quotient.eq, show t * q + p - t = (1 - t) * p by linear_combination t * hpq]
    exact Ideal.mul_mem_left _ _ hp
  have hmk1 : Ideal.Quotient.mk (b' * c) (t * q + p) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact ha1
  refine ⟨t * q + p, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [mul_assoc]
    refine IsCoprime.mul_left ((isUnit_mk_iff_coprime_span _ _).mp ?_)
      ((isUnit_mk_iff_coprime_span _ _).mp ?_)
    · rw [hat]; exact u.isUnit
    · rw [hmk1]; exact isUnit_one
  · rw [mul_assoc]
    exact Ideal.mul_mem_mul hk ha1
  · rw [sextic_mul_right, sextic_congr (Ideal.mul_le_left ha1), sextic_one hb',
      ← sexticChar_apply_mk hP6, hat, mul_one]
    exact hu
  · rw [sextic_congr (Ideal.mul_le_right ha1), sextic_one hc]

/-- At a frequency sharing a prime with `b c` the twisted Gauss sum vanishes. -/
theorem twistedGauss_pairCharacter_of_not_coprime {b c : Ideal 𝓔} (hb : Starred b)
    (hc : Starred c) (hbc : IsCoprime b c) {k : 𝓔} (hk : ¬ IsCoprime (b * c) (span {k})) :
    twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k = 0 := by
  obtain ⟨P, hm, hle⟩ := exists_le_maximal _ (mt isCoprime_iff_sup_eq.mpr hk)
  have hd : P ∣ b * c := dvd_iff_le.mpr (le_sup_left.trans hle)
  have hP0 : P ≠ ⊥ := fun h => (hb.1.mul hc.1).1 (by simpa [h] using dvd_iff_le.mp hd)
  have hP : Prime P := (Ideal.prime_iff_isPrime hP0).mpr hm.isPrime
  have hkP : k ∈ P := (span_singleton_le_iff_mem _).mp (le_sup_right.trans hle)
  obtain ⟨a, ha, hka, hχ⟩ : ∃ a : 𝓔, IsCoprime (b * c) (span {a}) ∧ k * (a - 1) ∈ b * c ∧
      pairCharacter b c a ≠ 1 := by
    rcases hP.dvd_or_dvd hd with h | h
    · obtain ⟨a, ha, hka, hs, hs'⟩ := exists_twist hb hc.1 hbc hP h
      refine ⟨a, ha, hka k hkP, fun h1 => hs ?_⟩
      rw [pairCharacter, hs', mul_one] at h1
      simpa using congrArg conj h1
    · obtain ⟨a, ha, hka, hs, hs'⟩ := exists_twist hc hb.1 hbc.symm hP h
      rw [mul_comm c b] at ha hka
      refine ⟨a, ha, hka k hkP, fun h1 => hs ?_⟩
      rwa [pairCharacter, hs', map_one, one_mul] at h1
  have h := twistedGauss_mul hb.1 hc.1 ha k
  rw [twistedGauss_congr b c (show k * a - k ∈ b * c by rw [← mul_sub_one]; exact hka)] at h
  have h' : (1 - pairCharacter b c a) *
      twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hχ.symm)

/-- The twisted Gauss sum of the primitive paired character separates into the conjugate
character and the normalized Gauss sum. This includes conductor one. -/
theorem twistedGauss_pairCharacter {b c : Ideal 𝓔} (hb : Starred b) (hc : Starred c)
    (hbc : IsCoprime b c) (k : 𝓔) :
    twistedGauss (pairCharacter b c) (b * c) (generator (b * c)) k =
      conj (pairCharacter b c k) * (Real.sqrt (absNorm (b * c)) * pairGauss b c) := by
  by_cases hk : IsCoprime (b * c) (span {k})
  · rw [twistedGauss_pairCharacter_of_coprime hb.1 hc.1 hk, twistedGauss_one (hb.1.mul hc.1).1]
  · rw [twistedGauss_pairCharacter_of_not_coprime hb hc hbc hk,
      pairCharacter_eq_zero hb.1 hc.1 hk, map_zero, zero_mul]

/-! ### Poisson summation over the multiples of an ideal -/

private lemma normSq_generator (e : Ideal 𝓔) :
    Complex.normSq (eisEmbedding (generator e)) = absNorm e := by
  rw [Complex.normSq_eq_norm_sq, norm_eisEmbedding_generator, Real.sq_sqrt (Nat.cast_nonneg _)]

private lemma absNorm_pos {n : Ideal 𝓔} (hn : n ≠ ⊥) : (0 : ℝ) < absNorm n :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn))

/-- Poisson summation for the paired character over the multiples of `e`, at length `Y`. -/
theorem hasSum_pairCharacter_multiples {b c e : Ideal 𝓔} (hb : Starred b) (hc : Starred c)
    (hbc : IsCoprime b c) (he : e ≠ ⊥) (P : SchwartzMap ℝ ℂ) {Y : ℝ} (hY : 0 < Y) :
    HasSum (fun y : 𝓔 => open Classical in
        if e ∣ span {y} then P (elementNorm y / Y) * pairCharacter b c y else 0)
      ((Y : ℂ) * pairGauss b c / Real.sqrt (absNorm (b * c)) *
        (pairCharacter b c (generator e) / (absNorm e : ℂ) *
          ∑' h : 𝓔, conj (pairCharacter b c h) * gaoZhaoTransform P
            (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c)))))) := by
  classical
  have hn : b * c ≠ ⊥ := (hb.1.mul hc.1).1
  have hNe := absNorm_pos he
  have hNn := absNorm_pos hn
  have hX : 0 < Y / absNorm e := div_pos hY hNe
  obtain ⟨-, hP⟩ := hasSum_twisted_poisson P hX (span_generator (b * c)) hn
    (χ := pairCharacter b c) fun y y' h => pairCharacter_congr h
  simp only [twistedGauss_pairCharacter hb hc hbc, normSq_generator] at hP
  have hg0 : generator e ≠ 0 := by
    intro h
    apply he
    rw [← span_generator e, h, Ideal.span_singleton_eq_bot]
  have hmem : ∀ y, e ∣ span {y} ↔ ∃ y', y = generator e * y' := by
    intro y
    rw [dvd_iff_le, span_singleton_le_iff_mem]
    constructor
    · exact generator_dvd_of_mem
    · rintro ⟨y', rfl⟩
      exact Ideal.mul_mem_right _ _ (generator_mem' e)
  rw [← (mul_right_injective₀ hg0).hasSum_iff fun y hy => by
    rw [ite_eq_right fun h => hy (((hmem y).mp h).imp fun y' h => h.symm)]]
  convert hP.mul_left (pairCharacter b c (generator e)) using 1
  · funext y'
    simp only [Function.comp_apply]
    rw [ite_eq_left ((hmem _).mpr ⟨y', rfl⟩), pairCharacter_mul hb.1 hc.1, elementNorm_eq_normSq,
      map_mul, Complex.normSq_mul, normSq_generator,
      show (absNorm e : ℝ) * Complex.normSq (eisEmbedding y') / Y =
        Complex.normSq (eisEmbedding y') / (Y / absNorm e) by field_simp]
    ring
  · have hS : (∑' k : 𝓔, gaoZhaoTransform P
          (√(Complex.normSq (eisEmbedding k) * (Y / absNorm e) / absNorm (b * c))) *
          (conj (pairCharacter b c k) * (√(absNorm (b * c) : ℝ) * pairGauss b c))) =
        (∑' h : 𝓔, conj (pairCharacter b c h) * gaoZhaoTransform P
          (√(Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))) *
          (√(absNorm (b * c) : ℝ) * pairGauss b c) := by
      rw [← tsum_mul_right]
      refine tsum_congr fun k => ?_
      rw [elementNorm_eq_normSq, show Complex.normSq (eisEmbedding k) * (Y / absNorm e) /
        absNorm (b * c) = Y * Complex.normSq (eisEmbedding k) / (absNorm e * absNorm (b * c)) by
          ring]
      ring
    rw [hS]
    have hs : ((√(absNorm (b * c) : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sqrt_absNorm_ne_zero hn)
    have hsq : ((absNorm (b * c) : ℕ) : ℂ) = ((√(absNorm (b * c) : ℝ) : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    have he' : ((absNorm e : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr he)
    push_cast
    rw [hsq]
    field_simp

/-! ### Möbius exclusion over the divisors of a squarefree ideal -/

private lemma prime_of_mem_factors {g P : Ideal 𝓔} (hP : P ∈ (normalizedFactors g).toFinset) :
    Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

private lemma normalizedFactors_prod_subset {g : Ideal 𝓔} {s : Finset (Ideal 𝓔)}
    (hs : s ⊆ (normalizedFactors g).toFinset) : normalizedFactors (∏ P ∈ s, P) = s.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact normalizedFactors_prod_of_prime fun P hP => prime_of_mem_factors (hs hP)

private lemma idealMoebius_prod_subset {g : Ideal 𝓔} {s : Finset (Ideal 𝓔)}
    (hs : s ⊆ (normalizedFactors g).toFinset) : idealMoebius (∏ P ∈ s, P) = (-1) ^ s.card := by
  have h0 : ∏ P ∈ s, P ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun P hP => (prime_of_mem_factors (hs hP)).ne_zero
  have hsq : Squarefree (∏ P ∈ s, P) := by
    rw [squarefree_iff_nodup_normalizedFactors h0, normalizedFactors_prod_subset hs]
    exact s.nodup
  simp only [idealMoebius, hsq, ↓reduceIte, normalizedFactors_prod_subset hs, Finset.card_val]

private lemma prod_factors_eq {g : Ideal 𝓔} (hg : Squarefree g) :
    ∏ P ∈ (normalizedFactors g).toFinset, P = g := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val,
    ((squarefree_iff_nodup_normalizedFactors hg.ne_zero).1 hg).dedup]
  exact associated_iff_eq.1 (prod_normalizedFactors hg.ne_zero)

/-- The divisors of a squarefree ideal are the products of sets of its prime factors. -/
private lemma dvd_iff_mem_image {g e : Ideal 𝓔} (hg : Squarefree g) :
    e ∣ g ↔ e ∈ (normalizedFactors g).toFinset.powerset.image (fun s => ∏ P ∈ s, P) := by
  rw [Finset.mem_image]
  constructor
  · intro h
    have he0 : e ≠ 0 := fun h0 => hg.ne_zero (zero_dvd_iff.mp (h0 ▸ h))
    refine ⟨(normalizedFactors e).toFinset, Finset.mem_powerset.mpr fun P hP => ?_,
      prod_factors_eq (Squarefree.squarefree_of_dvd h hg)⟩
    rw [Multiset.mem_toFinset] at hP ⊢
    exact Multiset.subset_of_le
      ((dvd_iff_normalizedFactors_le_normalizedFactors he0 hg.ne_zero).mp h) hP
  · rintro ⟨s, hs, rfl⟩
    exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp hs)).trans
      (prod_factors_eq hg).dvd

/-- A finite sum over the divisors of a squarefree ideal, indexed by sets of prime factors. -/
lemma finsum_dvd_eq_sum {g : Ideal 𝓔} (hg : Squarefree g) (f : Ideal 𝓔 → ℂ) :
    ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g}, f e =
      ∑ s ∈ (normalizedFactors g).toFinset.powerset, f (∏ P ∈ s, P) := by
  classical
  have hset : {e : Ideal 𝓔 | e ∣ g} =
      ↑((normalizedFactors g).toFinset.powerset.image (fun s => ∏ P ∈ s, P)) :=
    Set.ext fun e => dvd_iff_mem_image hg
  calc ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g}, f e = ∑ᶠ e ∈ {e : Ideal 𝓔 | e ∣ g}, f e :=
        finsum_set_coe_eq_finsum_mem (f := f) {e : Ideal 𝓔 | e ∣ g}
    _ = _ := by rw [hset, finsum_mem_coe_finset]
    _ = _ := by
      refine Finset.sum_image fun s hs t ht hst => Finset.val_injective ?_
      have h := congrArg normalizedFactors hst
      rwa [normalizedFactors_prod_subset (Finset.mem_powerset.mp hs),
        normalizedFactors_prod_subset (Finset.mem_powerset.mp ht)] at h

open Classical in
/-- Möbius inversion of the coprimality indicator over the divisors of a squarefree ideal. -/
lemma sum_moebius_dvd {g : Ideal 𝓔} (hg : g ≠ ⊥) (y : 𝓔) :
    ∑ s ∈ (normalizedFactors g).toFinset.powerset,
      (if ∏ P ∈ s, P ∣ span {y} then (idealMoebius (∏ P ∈ s, P) : ℂ) else 0) =
      if IsCoprime (span {y}) g then 1 else 0 := by
  set F := (normalizedFactors g).toFinset
  set Fy := F.filter (· ∣ span {y})
  have h1 : ∀ s ∈ F.powerset,
      (if ∏ P ∈ s, P ∣ span {y} then (idealMoebius (∏ P ∈ s, P) : ℂ) else 0) =
        if s ⊆ Fy then (((-1 : ℤ) ^ s.card : ℤ) : ℂ) else 0 := by
    intro s hs
    have hs' := Finset.mem_powerset.mp hs
    have hiff : ∏ P ∈ s, P ∣ span {y} ↔ s ⊆ Fy := by
      constructor
      · intro h P hP
        exact Finset.mem_filter.mpr ⟨hs' hP, (Finset.dvd_prod_of_mem _ hP).trans h⟩
      · intro h
        exact Finset.prod_primes_dvd _ (fun P hP => prime_of_mem_factors (hs' hP))
          fun P hP => (Finset.mem_filter.mp (h hP)).2
    rw [if_congr hiff rfl rfl, idealMoebius_prod_subset hs']
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have hfil : F.powerset.filter (· ⊆ Fy) = Fy.powerset := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans (Finset.filter_subset _ _), h⟩⟩
  rw [hfil, ← Int.cast_sum, Finset.sum_powerset_neg_one_pow_card]
  have hiff : Fy = ∅ ↔ IsCoprime (span {y}) g := by
    rw [Finset.eq_empty_iff_forall_notMem]
    constructor
    · intro h
      by_contra hc
      obtain ⟨M, hm, hle⟩ := exists_le_maximal _ (mt isCoprime_iff_sup_eq.mpr hc)
      have hgM : g ≤ M := le_sup_right.trans hle
      have hM0 : M ≠ ⊥ := fun h0 => hg (eq_bot_iff.mpr (h0 ▸ hgM))
      have hP : Prime M := (Ideal.prime_iff_isPrime hM0).mpr hm.isPrime
      exact h M (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
        ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hg).mpr ⟨hP, dvd_iff_le.mpr hgM⟩),
        dvd_iff_le.mpr (le_sup_left.trans hle)⟩)
    · intro hc P hP
      obtain ⟨hPF, hPy⟩ := Finset.mem_filter.mp hP
      exact (prime_of_mem_factors hPF).not_isUnit
        (hc.isUnit_of_dvd' hPy (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPF)))
  by_cases h : IsCoprime (span {y}) g <;> simp [hiff, h]

/-! ### The primitive Poisson formula -/

/-- Primitive Poisson summation for the paired character with the squarefree exclusion. -/
theorem primitivePoisson : PrimitivePoisson := by
  classical
  intro b c g hb hc hg hbc _ P Y hY
  set F := (normalizedFactors g).toFinset
  have hne : ∀ s ∈ F.powerset, ∏ Q ∈ s, Q ≠ ⊥ := fun s hs =>
    Finset.prod_ne_zero_iff.2 fun Q hQ =>
      (prime_of_mem_factors (Finset.mem_powerset.mp hs hQ)).ne_zero
  have hsum := hasSum_sum (s := F.powerset) fun s hs =>
    (hasSum_pairCharacter_multiples hb hc hbc (hne s hs) P hY).mul_left
      (idealMoebius (∏ Q ∈ s, Q) : ℂ)
  have hfun : (fun y : 𝓔 => if IsCoprime (span {y}) g then
      P (elementNorm y / Y) * pairCharacter b c y else 0) = fun y =>
      ∑ s ∈ F.powerset, (idealMoebius (∏ Q ∈ s, Q) : ℂ) * (if ∏ Q ∈ s, Q ∣ span {y} then
        P (elementNorm y / Y) * pairCharacter b c y else 0) := by
    funext y
    calc _ = (if IsCoprime (span {y}) g then (1 : ℂ) else 0) *
          (P (elementNorm y / Y) * pairCharacter b c y) := by split_ifs <;> simp
      _ = _ := by
        rw [← sum_moebius_dvd hg.1.1 y, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs <;> simp
  have hD := finsum_dvd_eq_sum hg.2 fun e =>
    (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e : ℂ) *
      ∑' h : 𝓔, conj (pairCharacter b c h) * gaoZhaoTransform P
        (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))
  beta_reduce at hD
  rw [hfun, hsum.tsum_eq, hD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

end Masullo.QRH.MeanSquare
