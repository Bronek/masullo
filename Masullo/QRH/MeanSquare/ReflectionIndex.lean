import Masullo.QRH.MeanSquare.ReflectionCompletion
import Masullo.QRH.MeanSquare.ReflectionSmoothed

/-! # Reindexing the reflected Patterson expansion by its squarefree and cube ideals -/

noncomputable section

open NumberField Ideal Complex
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- Integral exponent of λ, unit, squarefree ideal and cube ideal of a dual frequency.
The coefficient table assigns zero to the unused combinations of exponent and unit. -/
structure ReflectedIndex where
  exponent : ℕ
  unit : 𝓔ˣ
  n : Ideal 𝓔
  b : Ideal 𝓔
  coprime_n : IsCoprime n (span {3})
  coprime_b : IsCoprime b (span {3})
  squarefree_n : Squarefree n

namespace ReflectedIndex

def numerator (x : ReflectedIndex) : 𝓔 :=
  eisLambda^x.exponent * (x.unit * (generator x.n * generator x.b ^ 3))

theorem numerator_ne (x : ReflectedIndex) : x.numerator ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ eisLambda_prime.ne_zero) (mul_ne_zero x.unit.ne_zero
    (mul_ne_zero (eisPrimary_generator x.coprime_n).ne_zero
      (pow_ne_zero _ (eisPrimary_generator x.coprime_b).ne_zero)))

private theorem valuation (x : ReflectedIndex) : emultiplicity eisLambda x.numerator = x.exponent := by
  have hu : ¬ eisLambda ∣ (x.unit : 𝓔) := fun h =>
    eisLambda_prime.not_isUnit (isUnit_of_dvd_unit h x.unit.isUnit)
  have hb : ¬ eisLambda ∣ generator x.b ^ 3 := fun h =>
    (eisPrimary_generator x.coprime_b).lambda_not_dvd (eisLambda_prime.dvd_of_dvd_pow h)
  simp only [numerator,emultiplicity_mul eisLambda_prime,emultiplicity_pow_self_of_prime eisLambda_prime,
    emultiplicity_eq_zero.mpr hu,emultiplicity_eq_zero.mpr (eisPrimary_generator x.coprime_n).lambda_not_dvd,
    emultiplicity_eq_zero.mpr hb,add_zero]

theorem numerator_injective : Function.Injective numerator := by
  rintro ⟨j,u,n,b,hn,hb,hs⟩ ⟨i,v,k,d,hk,hd,hk'⟩ he
  have hj := congrArg (emultiplicity eisLambda) he
  rw [valuation,valuation] at hj
  obtain rfl : j = i := by exact_mod_cast hj
  have h := mul_left_cancel₀ (pow_ne_zero j eisLambda_prime.ne_zero) he
  change (u:𝓔) * (generator n * generator b ^ 3) = (v:𝓔) * (generator k * generator d ^ 3) at h
  have hI := congrArg (fun m : 𝓔 => span {m}) h
  simp only [span_singleton_mul_left_unit u.isUnit,span_singleton_mul_left_unit v.isUnit,
    ← span_singleton_mul_span_singleton,← span_singleton_pow,span_generator] at hI
  have hnz {a : Ideal 𝓔} (h : IsCoprime a (span {3})) : a ≠ 0 := by
    intro ha
    exact (eisPrimary_generator h).ne_zero (span_singleton_eq_bot.mp ((span_generator a).trans ha))
  obtain ⟨rfl,rfl⟩ := squarefree_mul_cube_inj (hnz hn) (hnz hb) (hnz hk) (hnz hd) hs hk' hI
  obtain rfl : u = v := Units.ext (mul_right_cancel₀
    (mul_ne_zero (eisPrimary_generator hn).ne_zero (pow_ne_zero _ (eisPrimary_generator hb).ne_zero)) h)
  rfl

/-- Encode a signed row of Patterson's original coefficient table. -/
def ofRow (r : PattersonRow) (neg : Bool) : ReflectedIndex where
  exponent := r.layer.lambdaExponent
  unit := if neg then -r.layer.isUnit_unitFactor.unit else r.layer.isUnit_unitFactor.unit
  n := span {r.c}
  b := span {r.d}
  coprime_n := r.primary_c.coprime_three
  coprime_b := r.primary_d.coprime_three
  squarefree_n := squarefree_span_singleton.mpr r.squarefree_c

theorem numerator_ofRow (r : PattersonRow) (neg : Bool) :
    (ofRow r neg).numerator = if neg then -r.numerator else r.numerator := by
  cases neg <;> simp [ofRow,numerator,PattersonRow.numerator,generator_eq_of_eisPrimary rfl r.primary_c,
    generator_eq_of_eisPrimary rfl r.primary_d,mul_assoc]

private theorem frequency_injective : Function.Injective pattersonFrequency := fun _ _ he =>
  eisEmbedding_injective ((div_left_inj₀ (pow_ne_zero 3
    ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr eisLambda_prime.ne_zero))).mp he)

/-- Every nonzero dual coefficient is covered once by the indexed ideals. -/
theorem exists_signed_row {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ) {m : 𝓔}
    (h : τ (pattersonFrequency m) ≠ 0) :
    ∃ (r : PattersonRow) (neg : Bool), (ofRow r neg).numerator = m := by
  obtain ⟨r, hr⟩ : ∃ r : PattersonRow, pattersonFrequency m = r.frequency ∨ pattersonFrequency m = -r.frequency := by
    by_contra! hx
    exact h (hτ.2 _ hx)
  rcases hr with hr | hr
  · refine ⟨r,false,frequency_injective ?_⟩
    simpa only [numerator_ofRow,Bool.false_eq_true,ite_false,← r.frequency_eq_div,pattersonFrequency] using hr.symm
  · refine ⟨r,true,frequency_injective ?_⟩
    simpa only [numerator_ofRow,ite_true,pattersonFrequency,map_neg,neg_div,← r.frequency_eq_div] using hr.symm

/-- Reindex a reflected sum, including weights depending on the full integral numerator. -/
theorem tsum_coefficients {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ) (w : 𝓔 → ℂ) :
    (∑' m : {m : 𝓔 // m ≠ 0}, conj (τ (pattersonFrequency m))/27 * w m) =
      ∑' x : ReflectedIndex, conj (τ (pattersonFrequency x.numerator))/27 * w x.numerator := by
  let f (x : ReflectedIndex) : {m : 𝓔 // m ≠ 0} := ⟨x.numerator,x.numerator_ne⟩
  have hf : Function.Injective f := fun _ _ he => numerator_injective (congrArg Subtype.val he)
  apply (hf.tsum_eq ?_).symm
  intro m hm
  have ht : τ (pattersonFrequency m.val) ≠ 0 := fun he => hm (by simp [he])
  obtain ⟨r,neg,h⟩ := exists_signed_row hτ ht
  exact ⟨ofRow r neg,Subtype.ext h⟩

/-- The exact scale in (15), including the first possible numerator exponent zero. -/
theorem normSq_frequency (x : ReflectedIndex) : normSq (pattersonFrequency x.numerator) =
    (3 : ℝ)^((x.exponent : ℤ)-3) * absNorm x.n * (absNorm x.b : ℝ)^3 := by
  have hlambda : ‖eisEmbedding eisLambda‖ ^ 2 = 3 := by
    rw [eisEmbedding_lambda,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num)]
  have hu : ‖eisEmbedding (x.unit : 𝓔)‖^2 = 1 := by
    rw [norm_eisEmbedding_sq,span_singleton_eq_top.mpr x.unit.isUnit]; simp
  have hn (n : Ideal 𝓔) : ‖eisEmbedding (generator n)‖^2 = absNorm n := by
    rw [norm_eisEmbedding_sq,span_generator]
  simp only [normSq_eq_norm_sq,pattersonFrequency,numerator,norm_div,map_mul,map_pow,norm_mul,norm_pow,
    div_pow,mul_pow]
  rw [pow_right_comm _ x.exponent 2,pow_right_comm _ 3 2,pow_right_comm _ 3 2,hlambda,hu,hn,hn,one_mul,
    zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0),zpow_natCast]
  ring

theorem norm_coefficient (x : ReflectedIndex) {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ) :
    ‖conj (τ (pattersonFrequency x.numerator))/27‖ ≤
      (3:ℝ)^(((x.exponent:ℝ)-3)/6) * Real.sqrt (absNorm x.b) := by
  by_cases h : τ (pattersonFrequency x.numerator) = 0
  · simp only [h,map_zero,zero_div,norm_zero]; positivity
  obtain ⟨r,neg,hr⟩ := exists_signed_row hτ h
  obtain rfl := numerator_injective hr
  have hg := generator_eq_of_eisPrimary rfl r.primary_d
  have hb : Real.sqrt (absNorm (span {r.d})) = ‖eisEmbedding r.d‖ := by rw [← norm_eisEmbedding_generator,hg]
  change _ ≤ (3:ℝ)^(((r.layer.lambdaExponent:ℝ)-3)/6)*Real.sqrt (absNorm (span {r.d}))
  rw [hb,numerator_ofRow]
  cases neg <;> simp only [Bool.false_eq_true,ite_false,ite_true,pattersonFrequency,map_neg,neg_div,
    ← r.frequency_eq_div,(hτ.1 r).1,(hτ.1 r).2] <;> exact r.norm_normalized_coefficient_le

/-- The coefficient in (15) after extracting the powers of three, the
squarefree norm and the cube norm, before the remaining tame factors. -/
def amplitude (x : ReflectedIndex) (τ : ℂ → ℂ) : ℂ :=
  (conj (τ (pattersonFrequency x.numerator))/27) /
    (((3:ℝ)^(((x.exponent:ℝ)-3)/6) * Real.sqrt (absNorm x.b) : ℝ) : ℂ) *
    (pattersonFrequency x.numerator / ‖pattersonFrequency x.numerator‖)

theorem norm_amplitude (x : ReflectedIndex) {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ) :
    ‖x.amplitude τ‖ ≤ 1 := by
  have hf : pattersonFrequency x.numerator ≠ 0 := fun he =>
    x.numerator_ne (frequency_injective (by simpa [pattersonFrequency] using he))
  have hden : 0 < Real.sqrt (absNorm x.b) := by
    rw [← norm_eisEmbedding_generator]
    exact norm_pos_iff.mpr ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr
      (eisPrimary_generator x.coprime_b).ne_zero)
  let D := (3:ℝ)^(((x.exponent:ℝ)-3)/6)*Real.sqrt (absNorm x.b)
  have hD : 0 < D := mul_pos (by positivity) hden
  change ‖((conj (τ (pattersonFrequency x.numerator))/27) / (D:ℂ)) *
    (pattersonFrequency x.numerator / ‖pattersonFrequency x.numerator‖)‖ ≤ 1
  rw [norm_mul, norm_div, norm_div (pattersonFrequency x.numerator), Complex.norm_real,
    Complex.norm_real,Real.norm_of_nonneg hD.le,Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hf),mul_one]
  exact (div_le_one hD).mpr (x.norm_coefficient hτ)

/-- The full coefficient divided by the square root of the dual frequency norm
has exactly the three explicit weights of (15). -/
theorem angularCoefficient_div_sqrt (x : ReflectedIndex) (τ : ℂ → ℂ) (z : ℂ) :
    pattersonAngularCoefficient τ false z x.numerator / Real.sqrt (normSq (pattersonFrequency x.numerator)) =
      (((3:ℝ)^(-((x.exponent:ℝ)-3)/3) : ℝ) : ℂ) * x.amplitude τ *
        pattersonCharacter (pattersonFrequency x.numerator * z) /
        (Real.sqrt (absNorm x.n) * (absNorm x.b : ℂ)) := by
  let m := (x.exponent:ℝ)-3
  let N : ℝ := absNorm x.n
  let B : ℝ := absNorm x.b
  have hpos {a : Ideal 𝓔} (ha : IsCoprime a (span {3})) : 0 < Real.sqrt (absNorm a) := by
    rw [← norm_eisEmbedding_generator]
    exact norm_pos_iff.mpr ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr (eisPrimary_generator ha).ne_zero)
  have hN : 0 < Real.sqrt N := hpos x.coprime_n
  have hB : 0 < Real.sqrt B := hpos x.coprime_b
  have hp (r : ℝ) : 0 < (3:ℝ)^r := Real.rpow_pos_of_pos (by norm_num) _
  have hnorm : Real.sqrt (normSq (pattersonFrequency x.numerator)) =
      (3:ℝ)^(m/2) * Real.sqrt N * B * Real.sqrt B := by
    rw [x.normSq_frequency]
    change Real.sqrt ((3:ℝ)^((x.exponent:ℤ)-3) * N * B^3) = _
    have hz : (3:ℝ)^((x.exponent:ℤ)-3) = (3:ℝ)^m := by
      rw [← Real.rpow_intCast]; congr 1; dsimp [m]; push_cast; rfl
    have hbb : 0 ≤ B := Nat.cast_nonneg _
    rw [hz,Real.sqrt_mul (by positivity),Real.sqrt_mul (hp _).le,
      show B^3 = B^2*B by ring,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hbb,
      Real.sqrt_eq_rpow ((3:ℝ)^m), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    dsimp only [N,B]
    rw [show m*(1/2)=m/2 by ring]
    ring
  have he : (3:ℝ)^(-m/3) * (3:ℝ)^(m/2) = (3:ℝ)^(m/6) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]; congr 1; ring
  have hB₀ : B ≠ 0 := (Real.sqrt_pos.mp hB).ne'
  rw [hnorm]
  simp only [pattersonAngularCoefficient,Bool.false_eq_true,ite_false,conj_conj,amplitude]
  change _ = (((3:ℝ)^(-m/3) : ℝ) : ℂ) * ((_/(((3:ℝ)^(m/6)*Real.sqrt B : ℝ):ℂ))*_) * _ /
    (Real.sqrt N * (B:ℂ))
  push_cast
  have hc := congrArg Complex.ofReal he
  push_cast at hc
  have hq (r : ℝ) : ((((3:ℝ)^r : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr (hp r).ne'
  field_simp [hq,hN.ne',hB.ne',hB₀]
  rw [← hc,neg_div]
  ring

end ReflectedIndex

end Masullo.QRH.MeanSquare
