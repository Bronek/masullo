import Masullo.QRH.MeanSquare.GaussProduct

/-! # Quadratic duplication of Gauss sums over odd finite fields -/

noncomputable section

open Finset

namespace Masullo.QRH.MeanSquare

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Completing the square in the Jacobi sum gives the quadratic twist of a
nontrivial multiplicative character. -/
theorem jacobiSum_duplication {χ : MulChar F ℂ} (hχ : χ ≠ 1) (hF : ringChar F ≠ 2) :
    χ 4 * jacobiSum χ χ = jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) := by
  let φ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hcount (t : F) : ((univ.filter (fun x : F => x ^ 2 = t)).card : ℂ) = φ t + 1 := by
    change _ = ((quadraticChar F t : ℤ) : ℂ) + 1
    have hc := quadraticChar_card_sqrts hF t
    rw [Set.toFinset_ofPred] at hc
    exact_mod_cast hc
  have hs : ∑ t : F, χ (1 - t) = 0 :=
    ((Equiv.subLeft 1).sum_comp χ).trans (χ.sum_eq_zero_of_ne_one hχ)
  calc
    χ 4 * jacobiSum χ χ = ∑ x : F, χ (1 - (1 - 2 * x) ^ 2) := by
      rw [jacobiSum, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← map_mul, ← map_mul]
      congr 1
      ring
    _ = ∑ y : F, χ (1 - y ^ 2) := by
      exact (((Equiv.mulLeft₀ 2 (Ring.two_ne_zero hF)).trans (Equiv.subLeft 1)).sum_comp
        (fun y => χ (1 - y ^ 2)))
    _ = ∑ t : F, (φ t + 1) * χ (1 - t) := by
      rw [← univ.sum_fiberwise' (fun x : F => x ^ 2) (fun t => χ (1 - t))]
      simp only [sum_const, nsmul_eq_mul, hcount]
    _ = jacobiSum φ χ := by simp only [add_mul, one_mul, sum_add_distrib, hs, add_zero, jacobiSum]
    _ = _ := jacobiSum_comm ..

/-- The quadratic Hasse–Davenport product formula, for an arbitrary primitive
additive character. Here all Gauss sums are unnormalized. -/
theorem gaussSum_duplication {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hF : ringChar F ≠ 2) (hχ : χ ≠ 1) (hχ₂ : χ ^ 2 ≠ 1)
    (htwist : χ * (quadraticChar F).ringHomComp (Int.castRingHom ℂ) ≠ 1) :
    let φ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
    χ 4 * gaussSum χ ψ * gaussSum (χ * φ) ψ = gaussSum (χ ^ 2) ψ * gaussSum φ ψ := by
  let φ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  change χ 4 * gaussSum χ ψ * gaussSum (χ * φ) ψ = gaussSum (χ ^ 2) ψ * gaussSum φ ψ
  have hχχ := jacobiSum_mul_nontrivial (show χ * χ ≠ 1 by simpa [sq] using hχ₂) ψ
  have hχφ := jacobiSum_mul_nontrivial htwist ψ
  change gaussSum (χ * φ) ψ * jacobiSum χ φ = _ at hχφ
  rw [← jacobiSum_duplication hχ hF] at hχφ
  rw [← sq] at hχχ
  apply mul_left_cancel₀ (gaussSum_ne_zero_of_nontrivial (by exact_mod_cast Fintype.card_ne_zero) hχ hψ)
  linear_combination χ 4 * gaussSum (χ * φ) ψ * (-hχχ) + gaussSum (χ ^ 2) ψ * hχφ

lemma cubic_power_eq_quadraticChar {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    (hF : ringChar F ≠ 2) : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  let φ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hφ : φ ≠ 1 := (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hF)
  have hthree : χ ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by decide) (by omega)
  have value {ξ : MulChar F ℂ} (hn : ξ ≠ 1) (hs : ξ ^ 2 = 1) : ξ g = -1 := by
    have h := DFunLike.congr_fun hs (g : F)
    rw [MulChar.pow_apply' _ two_ne_zero, MulChar.one_apply g.isUnit] at h
    refine (sq_eq_one_iff.mp h).resolve_left ?_
    intro he
    apply hn
    exact (MulChar.eq_iff hg _ _).mpr (by simpa only [MulChar.one_apply g.isUnit] using he)
  apply (MulChar.eq_iff hg _ _).mpr
  have hsix := pow_orderOf_eq_one χ
  rw [hχ] at hsix
  rw [value hthree (by simpa only [← pow_mul] using hsix)]
  exact (value hφ ((quadraticChar_isQuadratic F).comp _).sq_eq_one).symm

/-- At a character of order six, the quadratic duplication formula expresses the
normalized sextic Gauss sum in terms of the cubic and quadratic ones. -/
theorem normalized_gaussSum_sextic {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hχ : orderOf χ = 6)
    (hF : ringChar F ≠ 2) (hψ : ψ.IsPrimitive) :
    let γ := fun j : ℕ => gaussSum (χ ^ j) ψ / (Real.sqrt (Fintype.card F) : ℂ)
    χ 4 * γ 1 = γ 2 ^ 2 * γ 3 := by
  have hn (j : ℕ) (h₀ : j ≠ 0) (hj : j < 6) : χ ^ j ≠ 1 :=
    pow_ne_one_of_lt_orderOf h₀ (hχ ▸ hj)
  have h₁ : χ ≠ 1 := by simpa using hn 1 one_ne_zero (by decide)
  have hφ := cubic_power_eq_quadraticChar hχ hF
  have h_four : χ * χ ^ 3 = χ ^ 4 := by rw [← pow_succ']
  have hdup := gaussSum_duplication hψ hF h₁ (hn 2 (by decide) (by decide))
    (by rw [← hφ, h_four]; exact hn 4 (by decide) (by decide))
  dsimp only at hdup
  rw [← hφ, h_four] at hdup
  have hord : orderOf (χ ^ 2) = 3 := by rw [orderOf_pow' _ two_ne_zero, hχ]; decide
  have hc := gaussSum_mul_gaussSum_pow_orderOf_sub_one (hn 2 (by decide) (by decide)) hψ
  have hminus : (χ ^ 2) (-1 : F) = 1 := by
    rw [MulChar.pow_apply' _ two_ne_zero, ← map_pow]
    simp
  rw [hord, ← pow_mul, hminus, one_mul] at hc
  change gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 4) ψ = (Fintype.card F : ℂ) at hc
  have hr : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = Fintype.card F := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  have hp : (Real.sqrt (Fintype.card F) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos : (0 : ℝ) < _)).ne'
  dsimp only
  rw [pow_one]
  field_simp
  rw [hr]
  linear_combination gaussSum (χ ^ 2) ψ * hdup - χ 4 * gaussSum χ ψ * hc

open NumberField Ideal UniqueFactorizationMonoid

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma six_notMem {P : Ideal 𝓔} (hp : Prime P) (hP : AwayFromSix P) : (6 : 𝓔) ∉ P :=
  fun h => hp.not_isUnit (hP.2.isUnit_of_dvd (dvd_iff_le.mpr ((span_singleton_le_iff_mem _).mpr h)))

theorem ringChar_quotient_ne_two {P : Ideal 𝓔} (hp : Prime P) (hP : AwayFromSix P) :
    ringChar (𝓔 ⧸ P) ≠ 2 := by
  intro hc
  have h₂ : (2 : 𝓔 ⧸ P) = 0 := (ringChar.spec _ 2).mpr (hc ▸ dvd_rfl)
  apply six_notMem hp hP
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_ofNat]
  calc (6 : 𝓔 ⧸ P) = 2 * 3 := by norm_num
       _ = 0 := by rw [show (2 : 𝓔 ⧸ P) = 0 from h₂, zero_mul]

/-- The local residue character takes values of exact order six. -/
theorem orderOf_sexticChar_prime {P : Ideal 𝓔} (hP : AwayFromSix P) (hp : Prime P) :
    orderOf (sexticChar hP) = 6 := by
  classical
  let : P.IsMaximal := ((Ideal.prime_iff_isPrime hp.ne_zero).mp hp).isMaximal hp.ne_zero
  let := Ideal.Quotient.field P
  let := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ P)
  have hs (x : (𝓔 ⧸ P)ˣ) : sexticChar hP (x : 𝓔 ⧸ P) ^ 6 = 1 := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x : 𝓔 ⧸ P)
    have hc := (isUnit_mk_iff_coprime_span P a).mp (ha.symm ▸ x.isUnit)
    rw [← ha, sexticChar_apply_mk, sextic, ← map_pow, powerResidueSymbol_six_pow_six hP.1 hP.2,
      ite_eq_left hc, map_one]
  have hpow : sexticChar hP ^ 6 = 1 := MulChar.ext fun x => by
    simpa only [MulChar.pow_apply' _ (by decide : 6 ≠ 0), MulChar.one_apply x.isUnit] using hs x
  apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓔 ⧸ P)ˣ)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (g : 𝓔 ⧸ P)
  have hq := order_dvd_norm_sub_one hp (primitive_mod_prime hp (six_notMem hp hP) neg_omega_primitive)
  have hgN : orderOf (g : 𝓔 ⧸ P) = absNorm P - 1 := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Ideal.absNorm_eq_natCard]
  have hg₀ : orderOf (g : 𝓔 ⧸ P) ≠ 0 := by rw [orderOf_units]; exact (orderOf_pos g).ne'
  have hj := orderOf_pow_orderOf_div hg₀ (hgN ▸ hq)
  rw [hgN] at hj
  obtain ⟨_, ha'⟩ := primePowerResidueSymbol_spec hp (six_notMem hp hP) neg_omega_primitive
    (show a ∉ P from fun h => g.ne_zero (ha.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h)))
  rw [ha] at ha'
  rw [← ha'] at hj
  apply hj ▸ orderOf_dvd_of_pow_eq_one ?_
  rw [← map_pow]
  have hpos : orderOf (sexticChar hP) ≠ 0 := (isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hpow⟩).orderOf_pos.ne'
  have hv := DFunLike.congr_fun (pow_orderOf_eq_one (sexticChar hP)) (g : 𝓔 ⧸ P)
  rw [MulChar.pow_apply' _ hpos, MulChar.one_apply g.isUnit, ← ha, sexticChar_apply_mk, sextic] at hv
  simp only [powerResidueSymbol, ite_eq_right hP.1, normalizedFactors_irreducible hp.irreducible,
    normalize_eq, Multiset.map_singleton, Multiset.prod_singleton] at hv
  rw [← map_pow] at hv
  rw [eisEmbedding_injective (hv.trans (map_one _).symm), map_one]

/-- A primitive additive character turns the local quadratic character Gauss sum
into the exponential sum of the square map. -/
theorem gaussSum_three_eq_sum_sq_prime {P : Ideal 𝓔} (hP : AwayFromSix P) (hp : Prime P)
    [Fintype (𝓔 ⧸ P)] (ψ : AddChar (𝓔 ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum (sexticChar hP ^ 3) ψ = ∑ x, ψ (x ^ 2) := by
  classical
  let : P.IsMaximal := ((Ideal.prime_iff_isPrime hp.ne_zero).mp hp).isMaximal hp.ne_zero
  let := Ideal.Quotient.field P
  let φ := (quadraticChar (𝓔 ⧸ P)).ringHomComp (Int.castRingHom ℂ)
  have hcount (t : 𝓔 ⧸ P) : ((univ.filter (fun x : 𝓔 ⧸ P => x ^ 2 = t)).card : ℂ) = φ t + 1 := by
    change _ = ((quadraticChar _ t : ℤ) : ℂ) + 1
    have h := quadraticChar_card_sqrts (ringChar_quotient_ne_two hp hP) t
    rw [Set.toFinset_ofPred] at h
    exact_mod_cast h
  rw [cubic_power_eq_quadraticChar (orderOf_sexticChar_prime hP hp) (ringChar_quotient_ne_two hp hP),
    ← univ.sum_fiberwise' (fun x : 𝓔 ⧸ P => x ^ 2) ψ]
  have hn : ψ ≠ 1 := fun h => hψ one_ne_zero (by simp [h])
  simp only [sum_const, nsmul_eq_mul, hcount, add_mul, one_mul, sum_add_distrib,
    AddChar.sum_eq_zero_of_ne_one hn, add_zero]
  rfl

lemma normalizedGauss_eq_gaussSum {n : Ideal 𝓔} (hn : AwayFromSix n) [Fintype (𝓔 ⧸ n)]
    {j : ℕ} (hj : j ≠ 0) :
    normalizedGauss n j = gaussSum (sexticChar hn ^ j) (quotientDifferentCharacter n) /
      (Real.sqrt (absNorm n) : ℂ) := by
  simp only [normalizedGauss, finsum_eq_sum_of_fintype, gaussSum, MulChar.pow_apply' _ hj]
  rfl

private theorem normalizedGauss_duplication_prime {P : Ideal 𝓔} (hP : AwayFromSix P) (hp : Prime P) :
    sextic P 4 * normalizedGauss P 1 = normalizedGauss P 2 ^ 2 * normalizedGauss P 3 := by
  classical
  let : P.IsMaximal := ((Ideal.prime_iff_isPrime hp.ne_zero).mp hp).isMaximal hp.ne_zero
  let := Ideal.Quotient.field P
  let := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ P)
  have h := normalized_gaussSum_sextic (orderOf_sexticChar_prime hP hp) (ringChar_quotient_ne_two hp hP)
    (quotientDifferentCharacter_isPrimitive hP.1)
  have he : sexticChar hP 4 = sextic P 4 := by rw [← map_ofNat (Ideal.Quotient.mk P) 4, sexticChar_apply_mk]
  simpa only [normalizedGauss_eq_gaussSum hP one_ne_zero, normalizedGauss_eq_gaussSum hP two_ne_zero,
    normalizedGauss_eq_gaussSum hP (by decide : 3 ≠ 0), he, absNorm_eq_natCard, Nat.card_eq_fintype_card] using h

@[simp] theorem normalizedGauss_one (j : ℕ) : normalizedGauss (1 : Ideal 𝓔) j = 1 := by
  classical
  let : Subsingleton (𝓔 ⧸ (1 : Ideal 𝓔)) := Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
  let := Fintype.ofFinite (𝓔 ⧸ (1 : Ideal 𝓔))
  rw [normalizedGauss, finsum_eq_sum_of_fintype, Fintype.sum_subsingleton _ 0]
  simp [sextic, Ideal.one_eq_top]

/-- Induction on a squarefree conductor by adjoining one new good prime at a time. -/
theorem Starred.induction_on_prime_mul {Q : Ideal 𝓔 → Prop} {n : Ideal 𝓔} (hn : Starred n)
    (h₁ : Q 1)
    (hmul : ∀ {p a}, Prime p → AwayFromSix p → AwayFromSix a → IsCoprime p a → Q a → Q (p * a)) :
    Q n := by
  revert hn
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => (h.1.1 rfl).elim
  | h₂ a hu => exact fun _ => isUnit_iff_eq_one.mp hu ▸ h₁
  | h₃ a p ha hp ih =>
    intro h
    have ha' : AwayFromSix a := ⟨ha, h.1.2.of_isCoprime_of_dvd_left (dvd_mul_left a p)⟩
    have hp' : AwayFromSix p := ⟨hp.ne_zero, h.1.2.of_isCoprime_of_dvd_left (dvd_mul_right p a)⟩
    have hc : IsCoprime p a := isCoprime_iff_sup_eq.mpr <| Ideal.isUnit_iff.mp <|
      IsRelPrime.of_squarefree_mul h.2 (dvd_iff_le.mpr le_sup_left) (dvd_iff_le.mpr le_sup_right)
    exact hmul hp hp' ha' hc (ih ⟨ha', h.2.of_mul_right⟩)

/-- Quadratic duplication for the sextic, cubic and quadratic Gauss sums on any
squarefree conductor coprime to six. -/
theorem normalizedGauss_duplication {n : Ideal 𝓔} (hn : Starred n) :
    sextic n 4 * normalizedGauss n 1 = normalizedGauss n 2 ^ 2 * normalizedGauss n 3 := by
  refine hn.induction_on_prime_mul (Q := fun I => sextic I 4 * normalizedGauss I 1 =
    normalizedGauss I 2 ^ 2 * normalizedGauss I 3) ?_ ?_
  · rw [normalizedGauss_one, normalizedGauss_one, normalizedGauss_one]
    simp [sextic, Ideal.one_eq_top]
  · intro p a hp hp' ha' hc htail
    have h6 {b c : Ideal 𝓔} (hb : AwayFromSix b) (h : IsCoprime b c) :
        sextic b (generator c) ^ 6 = 1 := by
      have hc : IsCoprime b (span {generator c}) := by rwa [span_generator]
      rw [sextic, ← map_pow, powerResidueSymbol_six_pow_six hb.1 hb.2, ite_eq_left hc, map_one]
    have hcross : (sextic p (generator a) * sextic a (generator p)) ^ 6 = 1 := by
      rw [mul_pow, h6 hp' hc, h6 ha' hc.symm, mul_one]
    have hprime := normalizedGauss_duplication_prime hp' hp
    have hfour : sextic (p * a) 4 = sextic p 4 * sextic a 4 := by
      simp [sextic, powerResidueSymbol_mul_right]
    rw [hfour, normalizedGauss_mul hp' ha' hc one_ne_zero, normalizedGauss_mul hp' ha' hc two_ne_zero,
      normalizedGauss_mul hp' ha' hc (by decide : 3 ≠ 0), pow_one]
    calc
      _ = (sextic p 4 * normalizedGauss p 1) * (sextic a 4 * normalizedGauss a 1) *
          (sextic p (generator a) * sextic a (generator p)) := by ring
      _ = _ := by
        rw [hprime, htail]
        linear_combination -(normalizedGauss p 2 ^ 2 * normalizedGauss a 2 ^ 2 *
          normalizedGauss p 3 * normalizedGauss a 3 * (sextic p (generator a) * sextic a (generator p))) * hcross

private theorem norm_normalizedGauss_prime {P : Ideal 𝓔} (hP : AwayFromSix P) (hp : Prime P)
    {j : ℕ} (hj : j ≠ 0) (h₆ : j < 6) : ‖normalizedGauss P j‖ = 1 := by
  classical
  let : P.IsMaximal := ((Ideal.prime_iff_isPrime hp.ne_zero).mp hp).isMaximal hp.ne_zero
  let := Ideal.Quotient.field P
  let := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ P)
  have hχ : sexticChar hP ^ j ≠ 1 :=
    pow_ne_one_of_lt_orderOf hj (by rwa [orderOf_sexticChar_prime hP hp])
  have h := gaussSum_mul_gaussSum_eq_card hχ (quotientDifferentCharacter_isPrimitive hP.1)
  rw [← star_gaussSum_eq, Complex.star_def, Complex.mul_conj'] at h
  have hs : ‖gaussSum (sexticChar hP ^ j) (quotientDifferentCharacter P)‖ ^ 2 = (absNorm P : ℝ) := by
    rw [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card]
    exact_mod_cast h
  have hpos : 0 < (absNorm P : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hp.ne_zero)
  rw [normalizedGauss_eq_gaussSum hP hj, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_eq_one_iff_eq (Real.sqrt_pos.mpr hpos).ne').mpr
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Every nontrivial power of the sextic character has a unit-norm normalized Gauss
sum on a good squarefree conductor. -/
theorem norm_normalizedGauss_eq_one {n : Ideal 𝓔} (hn : Starred n) {j : ℕ}
    (hj : j ≠ 0) (h₆ : j < 6) : ‖normalizedGauss n j‖ = 1 := by
  refine hn.induction_on_prime_mul (Q := fun I => ‖normalizedGauss I j‖ = 1)
    (by rw [normalizedGauss_one, norm_one]) ?_
  intro p a hp hp' ha' hc ih
  have h {b c : Ideal 𝓔} (hb : AwayFromSix b) (hbc : IsCoprime b c) :
      ‖sextic b (generator c)‖ = 1 :=
    norm_sextic_of_coprime hb (by rwa [span_generator])
  rw [normalizedGauss_mul hp' ha' hc hj, norm_mul, norm_pow, norm_mul, norm_mul,
    norm_normalizedGauss_prime hp' hp hj h₆, ih, h hp' hc, h ha' hc.symm]
  simp

theorem norm_normalizedGauss_two_eq_one {n : Ideal 𝓔} (hn : Starred n) :
    ‖normalizedGauss n 2‖ = 1 := norm_normalizedGauss_eq_one hn (by decide) (by decide)

/-- The angular factor preserves the norm of the cubic Gauss coefficient. -/
theorem norm_gaussCoefficient_eq_one {n : Ideal 𝓔} (hn : Starred n) : ‖gaussCoefficient n‖ = 1 := by
  rw [gaussCoefficient_eq, norm_mul, Complex.norm_conj, norm_angularFactor_eq_one hn.1.1,
    norm_normalizedGauss_two_eq_one hn, one_mul]

end Masullo.QRH.MeanSquare
