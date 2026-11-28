import Masullo.QRH.MeanSquare.GaussNorm
import Masullo.QRH.MeanSquare.ThetaSupport
import Masullo.QRH.MeanSquare.Primary

/-! # Bounds on the coefficients of the Patterson expansion -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma cubicSymbol_ne_zero_iff {n : Ideal 𝓔} (hn : n ≠ ⊥)
    (h₃ : IsCoprime n (span {3})) (a : 𝓔) :
    powerResidueSymbol 3 a n ≠ 0 ↔ IsCoprime n (span {a}) := by
  classical
  rw [powerResidueSymbol, ite_eq_right hn]
  constructor
  · intro h
    by_contra hc
    apply h
    obtain ⟨P, hm, hle⟩ := exists_le_maximal _ (mt isCoprime_iff_sup_eq.mpr hc)
    have hd : P ∣ n := dvd_iff_le.mpr (le_sup_left.trans hle)
    have hP : P ≠ ⊥ := fun h => hn (by simpa [h] using (dvd_iff_le.mp hd))
    have hp : Prime P := (Ideal.prime_iff_isPrime hP).mpr hm.isPrime
    have ha : a ∈ P := (span_singleton_le_iff_mem _).mp (le_sup_right.trans hle)
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨P,
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mpr ⟨hp, hd⟩,
      by simp [primePowerResidueSymbol, ha]⟩)
  · intro hc
    apply Multiset.prod_ne_zero
    intro hz
    obtain ⟨P,hm,hz⟩ := Multiset.mem_map.mp hz
    obtain ⟨hp,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hm
    have hnot {z : 𝓔} (h : IsCoprime n (span {z})) : z ∉ P := fun hz =>
      hp.not_isUnit (h.isUnit_of_dvd' hd (dvd_iff_le.mpr ((span_singleton_le_iff_mem _).mpr hz)))
    have hpow := (primePowerResidueSymbol_spec hp (hnot h₃) omega_primitive (hnot hc)).1
    simp [hz] at hpow

/-- The cubic residue character on any nonzero denominator prime to three.
This includes the inert prime above two. -/
def cubicChar {n : Ideal 𝓔} (hn : n ≠ ⊥) (h₃ : IsCoprime n (span {3})) :
    MulChar (𝓔 ⧸ n) ℂ := by
  let f (x : 𝓔 ⧸ n) := eisEmbedding (powerResidueSymbol 3 (Quotient.out x) n)
  have hf (a : 𝓔) : f (Ideal.Quotient.mk n a) = eisEmbedding (powerResidueSymbol 3 a n) :=
    congrArg eisEmbedding (powerResidueSymbol_congr (Ideal.Quotient.mk_out _))
  have hmul (x y : 𝓔 ⧸ n) : f (x * y) = f x * f y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, hf, hf, hf, powerResidueSymbol_three_mul h₃, map_mul]
  have hunit (x : 𝓔 ⧸ n) : f x ≠ 0 ↔ IsUnit x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hf, ← map_zero eisEmbedding, eisEmbedding_injective.ne_iff, cubicSymbol_ne_zero_iff hn h₃,
      isUnit_mk_iff_coprime_span]
  refine { toFun := f, map_mul' := hmul, map_one' := ?_,
           map_nonunit' := fun x hx => not_ne_iff.mp (mt (hunit x).mp hx) }
  have he : f 1 * f 1 = f 1 * 1 := by simpa only [one_mul, mul_one] using (hmul 1 1).symm
  exact mul_left_cancel₀ ((hunit _).mpr isUnit_one) he

@[simp] theorem cubicChar_mk {n : Ideal 𝓔} (hn : n ≠ ⊥) (h₃ : IsCoprime n (span {3})) (a : 𝓔) :
    cubicChar hn h₃ (Ideal.Quotient.mk n a) = eisEmbedding (powerResidueSymbol 3 a n) :=
  congrArg eisEmbedding (powerResidueSymbol_congr (Ideal.Quotient.mk_out _))

theorem eisPrimary.coprime_three {c : 𝓔} (hc : eisPrimary c) : IsCoprime (span {c}) (span {3}) := by
  rw [isCoprime_comm, ← isUnit_mk_iff_coprime_span, (eisPrimary_iff_mk_eq_one _).mp hc]
  exact isUnit_one

theorem eisPrimary.ne_zero {c : 𝓔} (hc : eisPrimary c) : c ≠ 0 :=
  fun he => hc.lambda_not_dvd (he ▸ dvd_zero _)

set_option maxHeartbeats 1200000 in
/-- Square-root cancellation holds for the trace-character Gauss sum at every
primary denominator and every shift invertible modulo it. -/
theorem norm_pattersonGauss_le {a c : 𝓔} (hc : eisPrimary c)
    (ha : IsUnit (Ideal.Quotient.mk (span {c}) a)) : ‖pattersonGauss a c‖ ≤ ‖eisEmbedding c‖ := by
  classical
  by_cases he : c = 1
  · simp [he]
  let n := span {c}
  have hn : n ≠ ⊥ := by simpa [n] using hc.ne_zero
  let := Ring.HasFiniteQuotients.finiteQuotient hn
  let := Fintype.ofFinite (𝓔 ⧸ n)
  let χ := cubicChar hn hc.coprime_three
  let ψ := quotientDifferentCharacter n
  let f := Ideal.Quotient.mk n
  have hf : IsUnit (f eisLambda) := by
    apply (isUnit_mk_iff_coprime_span _ _).mpr
    apply hc.coprime_three.of_isCoprime_of_dvd_right
    exact span_singleton_dvd_span_singleton_iff_dvd.mpr
      ⟨-eisLambda, by rw [mul_neg, ← sq, eisLambda_sq, neg_neg]⟩
  have hu : IsUnit (f (eisLambda * a)) := by rw [map_mul]; exact hf.mul ha
  have hg : generator n = c := generator_eq_of_eisPrimary rfl hc
  have hgp : pattersonGauss a c = gaussSum χ (ψ.mulShift (f (eisLambda * a))) := by
    rw [pattersonGauss, ite_eq_right he, finsum_eq_sum_of_fintype, gaussSum]
    apply Finset.sum_congr rfl
    intro x _
    change _ * _ = eisEmbedding (powerResidueSymbol 3 (Quotient.out x) n) * _
    congr 1
    have ht : f (eisLambda * a) * x = f ((eisLambda * a) * Quotient.out x) := by
      rw [map_mul f (eisLambda * a), Ideal.Quotient.mk_out]
    rw [AddChar.mulShift_apply, ht]
    change _ = quotientDifferentCharacter n (Ideal.Quotient.mk n _)
    rw [quotientDifferentCharacter_mk, hg, map_mul, map_mul]
    change traceCharacter _ = differentCharacter _
    rw [← differentCharacter_lambda_mul]
    congr 1
    ring
  have hbound := norm_gaussSum_le_sqrt_card χ (quotientDifferentCharacter_isPrimitive hn)
  have heq := congrArg norm (gaussSum_mulShift χ ψ hu.unit)
  have huχ : ‖χ hu.unit‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity _)
  rw [hu.unit_spec, norm_mul, ← hu.unit_spec, huχ, one_mul, hu.unit_spec] at heq
  rw [hgp, heq]
  rwa [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard, ← norm_eisEmbedding_sq,
    Real.sqrt_sq (norm_nonneg _)] at hbound

theorem norm_pattersonPhase (r : Fin 3) : ‖pattersonPhase r‖ = 1 := by
  fin_cases r <;> norm_num [pattersonPhase, Complex.norm_exp, Complex.div_re, Complex.mul_re]

private theorem isUnit_row_shift (r : PattersonRow) (i : Fin 3) :
    IsUnit (Ideal.Quotient.mk (span {r.c}) (eisOmega ^ (i : ℕ) * eisLambda ^ 2)) := by
  rw [map_mul, map_pow, map_pow]
  apply IsUnit.mul ((omega_primitive.isUnit (by decide)).map _ |>.pow _)
  apply IsUnit.pow
  apply (isUnit_mk_iff_coprime_span _ _).mpr
  apply r.primary_c.coprime_three.of_isCoprime_of_dvd_right
  exact span_singleton_dvd_span_singleton_iff_dvd.mpr
    ⟨-eisLambda, by rw [mul_neg, ← sq, eisLambda_sq, neg_neg]⟩

/-- With μ = u λᵐ c d³, the normalized coefficient is at most 3^(m/6)|d|. -/
theorem PattersonRow.norm_normalized_coefficient_le (r : PattersonRow) :
    ‖conj r.coefficient / 27‖ ≤
      3 ^ (((r.layer.lambdaExponent : ℝ) - 3) / 6) * ‖eisEmbedding r.d‖ := by
  obtain ⟨l,c,d,hc,hd,hs⟩ := r
  have hc0 : 0 < ‖eisEmbedding c‖ := norm_pos_iff.mpr
    (fun h => hc.ne_zero (eisEmbedding_injective (h.trans (map_zero _).symm)))
  have hcommon {a : 𝓔} (ha : IsUnit (Ideal.Quotient.mk (span {c}) a)) :
      ‖pattersonGauss a c‖ * ‖eisEmbedding d / eisEmbedding c‖ ≤ ‖eisEmbedding d‖ := by
    rw [norm_div]
    calc
      _ ≤ ‖eisEmbedding c‖ * (‖eisEmbedding d‖ / ‖eisEmbedding c‖) :=
        mul_le_mul_of_nonneg_right (norm_pattersonGauss_le hc ha) (by positivity)
      _ = _ := by field_simp
  have h27 : (27 : ℝ) = 3 ^ (3 : ℝ) := by norm_num
  cases l with
  | unshifted j =>
    have h := hcommon (a := 1) (by simp)
    simp only [PattersonRow.coefficient, PattersonLayer.lambdaExponent, norm_div, Complex.norm_conj,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg
        (by norm_num : (0 : ℝ) ≤ 3) _),
      Real.norm_of_nonneg (norm_nonneg _), Complex.norm_ofNat, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ ‖eisEmbedding d‖ * (3 ^ (((j : ℝ) + 5) / 2) / 27) := by
        rw [norm_div] at h
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity))
          (by norm_num : 0 ≤ (27 : ℝ))).trans_eq (mul_div_assoc ..)
      _ = _ := by
        rw [h27, ← Real.rpow_sub (by norm_num : 0 < (3 : ℝ)), mul_comm]
        congr 2
        ring
  | shifted k i =>
    have h := hcommon (isUnit_row_shift ⟨.shifted k i, c, d, hc, hd, hs⟩ i)
    simp only [PattersonRow.coefficient, PattersonLayer.lambdaExponent, norm_div, Complex.norm_conj,
      norm_mul, norm_pattersonPhase, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _), Real.norm_of_nonneg
        (norm_nonneg _),
      Complex.norm_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ ‖eisEmbedding d‖ * (3 ^ (((k : ℝ) + 1) / 2 + 2) / 27) := by
        rw [norm_div] at h
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity))
          (by norm_num : 0 ≤ (27 : ℝ))).trans_eq (mul_div_assoc ..)
      _ ≤ _ := by
        rw [h27, ← Real.rpow_sub (by norm_num : 0 < (3 : ℝ)), mul_comm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ))
        linarith

private theorem norm_lambda : ‖eisEmbedding eisLambda‖ = (3 : ℝ) ^ (1 / 2 : ℝ) := by
  rw [eisEmbedding_lambda, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow]

private theorem norm_layer_unit (l : PattersonLayer) : ‖eisEmbedding l.unitFactor‖ = 1 := by
  cases l with
  | unshifted => simp [PattersonLayer.unitFactor]
  | shifted k i =>
    simp [PattersonLayer.unitFactor, norm_pow, eisEmbedding_omega, Complex.norm_exp, Complex.mul_re]

theorem PattersonRow.norm_frequency (r : PattersonRow) :
    ‖r.frequency‖ = 3 ^ (((r.layer.lambdaExponent : ℝ) - 3) / 2) *
      ‖eisEmbedding r.c‖ * ‖eisEmbedding r.d‖ ^ 3 := by
  rw [r.frequency_eq_div]
  simp only [norm_div, PattersonRow.numerator, map_mul, map_pow, norm_mul, norm_pow, norm_lambda,
    norm_layer_unit, one_mul]
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_mul_natCast
    (by norm_num : (0 : ℝ) ≤ 3)]
  rw [show ((r.layer.lambdaExponent : ℝ) - 3) / 2 =
      (1 / 2 : ℝ) * r.layer.lambdaExponent - (1 / 2 : ℝ) * 3 by ring,
    Real.rpow_sub (by norm_num : 0 < (3 : ℝ))]
  ring_nf

theorem one_le_norm_eisEmbedding {c : 𝓔} (hc : c ≠ 0) : 1 ≤ ‖eisEmbedding c‖ := by
  have hc' : 1 ≤ absNorm (span {c}) := Nat.one_le_iff_ne_zero.mpr (by simp [hc])
  have hs : (1 : ℝ) ≤ ‖eisEmbedding c‖ ^ 2 := by
    rw [norm_eisEmbedding_sq]
    exact_mod_cast hc'
  nlinarith [norm_nonneg (eisEmbedding c)]

theorem PattersonRow.norm_normalized_coefficient_le_frequency (r : PattersonRow) :
    ‖conj r.coefficient / 27‖ ≤ ‖r.frequency‖ ^ (1 / 3 : ℝ) := by
  apply r.norm_normalized_coefficient_le.trans
  rw [r.norm_frequency, mul_assoc]
  calc
    _ = ((3 : ℝ) ^ (((r.layer.lambdaExponent : ℝ) - 3) / 2) *
        ‖eisEmbedding r.d‖ ^ 3) ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_natCast (x := ‖eisEmbedding r.d‖) 3,
        ← Real.rpow_mul (norm_nonneg _)]
      rw [show ((r.layer.lambdaExponent : ℝ) - 3) / 2 * (1 / 3) =
        ((r.layer.lambdaExponent : ℝ) - 3) / 6 by ring]
      norm_num
    _ ≤ _ := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      gcongr
      exact le_mul_of_one_le_left (by positivity) (one_le_norm_eisEmbedding r.primary_c.ne_zero)

/-- The signed coefficient table, extended by zero, has at most cube-root growth. -/
theorem PattersonCoefficients.norm_normalized_le {τ : ℂ → ℂ}
    (ht : PattersonCoefficients τ) (μ : ℂ) :
    ‖conj (τ μ) / 27‖ ≤ ‖μ‖ ^ (1 / 3 : ℝ) := by
  classical
  by_cases hs : ∃ r : PattersonRow, μ = r.frequency ∨ μ = -r.frequency
  · obtain ⟨r, rfl | rfl⟩ := hs
    · simpa only [(ht.1 r).1] using r.norm_normalized_coefficient_le_frequency
    · simpa only [(ht.1 r).2, norm_neg] using r.norm_normalized_coefficient_le_frequency
  · push Not at hs
    rw [ht.2 μ hs]
    simp [Real.rpow_nonneg (norm_nonneg _) _]

open Filter Asymptotics

/-- The zero-term asymptotic expansion already bounds the function by an
exponential at large positive arguments. This also applies to the expansion
for the derivative. -/
theorem HasHankelExpansion.eventually_norm_le_exp {F : ℝ → ℂ} {a : ℕ → ℂ}
    (h : HasHankelExpansion F a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ‖F x‖ ≤ C * Real.exp (-x) := by
  obtain ⟨C, hC, hbd⟩ := (h 0).exists_nonneg
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbd.bound, eventually_ge_atTop Real.pi] with x hx hxπ
  have hx₀ := Real.pi_pos.trans_le hxπ
  have hroot : Real.sqrt (Real.pi / (2 * x)) ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, (div_le_iff₀ (by positivity)).mpr (by nlinarith)⟩
  have hp : 0 < besselLeading x := by unfold besselLeading; positivity
  have hF : ‖F x‖ / besselLeading x ≤ C := by
    simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, inv_one, norm_one, mul_one,
      norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le] using hx
  calc
    _ ≤ C * besselLeading x := (div_le_iff₀ hp).mp hF
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (Real.exp_pos _).le hroot) hC

/-- The integral index in Patterson's λ⁻³ lattice. -/
def pattersonFrequency (m : 𝓔) : ℂ := eisEmbedding m / eisEmbedding eisLambda ^ 3

private theorem lambda_emb_ne_zero : eisEmbedding eisLambda ≠ 0 :=
  fun h => eisLambda_prime.ne_zero (eisEmbedding_injective (h.trans (map_zero _).symm))

private abbrev frequencyLattice := Masullo.Lattice.eisLattice (1 / eisEmbedding eisLambda ^ 3)

private instance : Fact ((1 : ℂ) / eisEmbedding eisLambda ^ 3 ≠ 0) :=
  ⟨by simp [lambda_emb_ne_zero]⟩

private instance : DiscreteTopology frequencyLattice := by unfold frequencyLattice; infer_instance

private instance : IsZLattice ℝ frequencyLattice := by unfold frequencyLattice; infer_instance

private def frequencyIndex : 𝓔 ↪ frequencyLattice where
  toFun m := ⟨pattersonFrequency m, by
    obtain ⟨a, b, rfl⟩ := eisInteger_coordinates m
    apply Masullo.Lattice.mem_eisLattice.mpr
    refine ⟨a, b, ?_⟩
    simp only [pattersonFrequency, map_add, map_mul, map_intCast, eisEmbedding_omega,
      Masullo.Lattice.omega_eq_exp]
    ring⟩
  inj' _ _ h := eisEmbedding_injective ((div_left_inj₀ (pow_ne_zero _ lambda_emb_ne_zero)).mp
    (congrArg Subtype.val h))

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
theorem tendsto_norm_pattersonFrequency :
    Tendsto (fun m : 𝓔 => ‖pattersonFrequency m‖) cofinite atTop := by
  let : DiscreteTopology frequencyLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology frequencyLattice)
  have hclosed : IsClosed ((frequencyLattice : Submodule ℤ ℂ) : Set ℂ) :=
    frequencyLattice.toAddSubgroup.isClosed_of_discreteTopology
  have h : Tendsto (fun x : frequencyLattice => ‖(x : ℂ)‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding hclosed.isClosedEmbedding_subtypeVal
  change Tendsto ((fun x : frequencyLattice => ‖(x : ℂ)‖) ∘ frequencyIndex) cofinite atTop
  exact h.comp frequencyIndex.injective.tendsto_cofinite

set_option maxHeartbeats 1500000 in
theorem summable_pattersonFrequency_rpow {s : ℝ} (hs : s < -2) :
    Summable fun m : 𝓔 => ‖pattersonFrequency m‖ ^ s := by
  have hdim : Module.finrank ℤ frequencyLattice = 2 := by
    rw [ZLattice.rank ℝ frequencyLattice, Complex.finrank_real_complex]
  have h := ZLattice.summable_norm_rpow frequencyLattice s (by simpa [hdim] using hs)
  change Summable ((fun x : frequencyLattice => ‖x‖ ^ s) ∘ frequencyIndex)
  exact h.comp_injective frequencyIndex.injective

/-- Exponential damping sums any real power of the frequency norm on λ⁻³𝓔. -/
theorem summable_pattersonFrequency_rpow_exp (s : ℝ) {A : ℝ} (hA : 0 < A) :
    Summable fun m : 𝓔 => ‖pattersonFrequency m‖ ^ s * Real.exp (-A * ‖pattersonFrequency m‖) := by
  have hzero := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s + 3) A hA
  apply (summable_pattersonFrequency_rpow (s := -3) (by norm_num)).of_norm_bounded_eventually
  filter_upwards [(hzero.comp tendsto_norm_pattersonFrequency).eventually_le_const
    (by norm_num : (0 : ℝ) < 1),
    tendsto_norm_pattersonFrequency.eventually_gt_atTop 0] with m hm hm₀
  set t := ‖pattersonFrequency m‖
  change t ^ (s + 3) * Real.exp (-A * t) ≤ 1 at hm
  rw [Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hm₀ (3 : ℝ))).mp
  calc
    _ = t ^ (s + 3) * Real.exp (-A * t) := by rw [Real.rpow_add hm₀]; ring
    _ ≤ 1 := hm
    _ = _ := by rw [← Real.rpow_add hm₀]; norm_num

/-- The Bessel-weighted absolute terms, including any fixed extra frequency power
from horizontal differentiation, have a summable majorant uniformly at heights
bounded below. Finitely many low frequencies are excluded from the asymptotic estimate. -/
theorem PattersonCoefficients.exists_summable_hankel_majorant {τ : ℂ → ℂ}
    (ht : PattersonCoefficients τ)
    {F : ℝ → ℂ} {a : ℕ → ℂ} (hF : HasHankelExpansion F a) (s : ℝ) {A₀ : ℝ} (hA : 0 < A₀) :
    ∃ g : 𝓔 → ℝ, Summable g ∧ ∀ᶠ m in cofinite, ∀ A : ℝ, A₀ ≤ A →
      ‖conj (τ (pattersonFrequency m)) / 27‖ * ‖pattersonFrequency m‖ ^ s *
        ‖F (A * ‖pattersonFrequency m‖)‖ ≤ g m := by
  obtain ⟨C, hC, hB⟩ := hF.eventually_norm_le_exp
  obtain ⟨T, hT⟩ := eventually_atTop.mp hB
  refine ⟨_, (summable_pattersonFrequency_rpow_exp (1 / 3 + s) hA).mul_left C, ?_⟩
  filter_upwards [tendsto_norm_pattersonFrequency.eventually_ge_atTop (T / A₀),
    tendsto_norm_pattersonFrequency.eventually_gt_atTop 0] with m hm hm₀
  intro A hAA
  set t := ‖pattersonFrequency m‖
  have hAt : A₀ * t ≤ A * t := mul_le_mul_of_nonneg_right hAA hm₀.le
  have hTt : T ≤ A * t := le_trans (by simpa [mul_comm] using (div_le_iff₀ hA).mp hm) hAt
  calc
    _ ≤ (t ^ (1 / 3 : ℝ) * t ^ s) * (C * Real.exp (-(A * t))) := by
      apply mul_le_mul _ (hT _ hTt) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (ht.norm_normalized_le _) (by positivity)
    _ ≤ (t ^ (1 / 3 : ℝ) * t ^ s) * (C * Real.exp (-(A₀ * t))) := by
      gcongr
    _ = _ := by rw [← Real.rpow_add hm₀, neg_mul] ; ring

/-- Absolute convergence of the differentiated Bessel series at every positive height. -/
theorem PattersonCoefficients.summable_hankel {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    {F : ℝ → ℂ} {a : ℕ → ℂ} (hF : HasHankelExpansion F a) (s : ℝ) {A : ℝ} (hA : 0 < A) :
    Summable fun m : 𝓔 => ‖conj (τ (pattersonFrequency m)) / 27‖ * ‖pattersonFrequency m‖ ^ s *
      ‖F (A * ‖pattersonFrequency m‖)‖ := by
  obtain ⟨g, hg, hm⟩ := ht.exists_summable_hankel_majorant hF s hA
  apply hg.of_norm_bounded_eventually
  filter_upwards [hm] with m hm
  simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ ‖conj (τ (pattersonFrequency m)) / 27‖ *
    ‖pattersonFrequency m‖ ^ s * ‖F (A * ‖pattersonFrequency m‖)‖)] using hm A le_rfl

end Masullo.QRH.MeanSquare
