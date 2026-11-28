import Masullo.QRH.MeanSquare.ThetaTranslate
import Masullo.QRH.MeanSquare.ReflectionTame
import Masullo.QRH.MeanSquare.ReflectionDecay

/-! # Chinese remaindering of the translated and reflected Patterson phases -/

noncomputable section

open NumberField Ideal Finset
open scoped BigOperators Function

namespace Masullo.QRH.MeanSquare.ReflectionCRT

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

abbrev Residue (d : 𝓔) := 𝓔 ⧸ span {d}
abbrev red (d : 𝓔) := Ideal.Quotient.mk (span {d})

private theorem mk_eq_iff {d a b : 𝓔} : red d a = red d b ↔ d ∣ a - b :=
  Ideal.Quotient.eq.trans Ideal.mem_span_singleton

private theorem mk_zero_iff {d a : 𝓔} : red d a = 0 ↔ d ∣ a :=
  Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

private theorem unit_mk_iff {d a : 𝓔} : IsUnit (red d a) ↔ IsCoprime d a :=
  (isUnit_mk_iff_coprime_span _ _).trans (isCoprime_span_singleton_iff _ _)

def residueUnit {d a : 𝓔} (h : IsCoprime d a) : (Residue d)ˣ :=
  (unit_mk_iff.mpr h).unit

@[simp] theorem residueUnit_val {d a : 𝓔} (h : IsCoprime d a) :
    (residueUnit h : Residue d) = red d a := (unit_mk_iff.mpr h).unit_spec

/-- The primitive different character with the exact denominator in the cusp shift. -/
def phase (d : 𝓔) : AddChar (Residue d) ℂ where
  toFun x := differentCharacter (eisEmbedding (Quotient.out x) / eisEmbedding d)
  map_zero_eq_one' := by
    have h : red d (Quotient.out (0 : Residue d)) = red d 0 := by simp [red, Ideal.Quotient.mk_out]
    rw [differentCharacter_div_congr (mk_eq_iff.mp h)]
    simp [differentCharacter]
  map_add_eq_mul' x y := by
    have h : red d (Quotient.out (x+y)) = red d (Quotient.out x + Quotient.out y) := by
      simp [red, Ideal.Quotient.mk_out]
    rw [differentCharacter_div_congr (mk_eq_iff.mp h), map_add, add_div, differentCharacter_add]

@[simp] theorem phase_mk (d m : 𝓔) :
    phase d (red d m) = differentCharacter (eisEmbedding m / eisEmbedding d) :=
  differentCharacter_div_congr (mk_eq_iff.mp (Ideal.Quotient.mk_out _))

theorem phase_eq_quotientDifferentCharacter {d : 𝓔} (hd : eisPrimary d) :
    phase d = quotientDifferentCharacter (span {d}) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientDifferentCharacter_mk, generator_eq_of_eisPrimary rfl hd]
  exact phase_mk d a

private lemma prime_symbol_four (x : 𝓔) (P : Ideal 𝓔) :
    primePowerResidueSymbol 3 x P ^ 4 = primePowerResidueSymbol 3 x P := by
  classical
  unfold primePowerResidueSymbol
  split_ifs with _ h
  · simp
  · rw [pow_succ, h.choose_spec.1, one_mul]
  · simp

private lemma symbol_four (x a : 𝓔) : cubicSymbol x a ^ 4 = cubicSymbol x a := by
  classical
  simp only [cubicSymbol, powerResidueSymbol]
  split_ifs
  · simp
  · simp only [← Multiset.prod_map_pow, prime_symbol_four]

private def evalCubic {a : 𝓔} (ha : eisPrimary a) : 𝓔 →* ℂ :=
  (cubicChar (by simpa using ha.ne_zero) ha.coprime_three).toMonoidHom.comp (red a).toMonoidHom

private lemma evalCubic_apply {a : 𝓔} (ha : eisPrimary a) (x : 𝓔) :
    evalCubic ha x = eisEmbedding (cubicSymbol x a) :=
  cubicChar_mk (by simpa using ha.ne_zero) ha.coprime_three x

private lemma evalCubic_neg_one {a : 𝓔} (ha : eisPrimary a) : evalCubic ha (-1) = 1 := by
  have h₂ : evalCubic ha (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  have h₄ : evalCubic ha (-1) ^ 4 = evalCubic ha (-1) := by
    rw [evalCubic_apply, ← map_pow, symbol_four]
  rwa [show (4 : ℕ) = 2 * 2 by decide, pow_mul, h₂, one_pow, eq_comm] at h₄

private instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private lemma evalCubic_unit_congr (hR : DunnRadziwillReciprocity) {a b : 𝓔}
    (ha : eisPrimary a) (hb : eisPrimary b) (h₉ : (9 : 𝓔) ∣ b-a) (u : 𝓔ˣ) :
    evalCubic ha u = evalCubic hb u := by
  let spec := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  let η : 𝓔ˣ := (spec.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : 𝓔) = eisOmega := rfl
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem spec u
  change u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  have hω : evalCubic ha eisOmega = evalCubic hb eisOmega := by
    rw [evalCubic_apply, evalCubic_apply, (cubic_supplements_congr hR ha h₉).2]
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Units.val_one, Units.val_neg, Units.val_pow_eq_pow_val, hη, map_one, map_pow,
      show -eisOmega = (-1 : 𝓔)*eisOmega by ring,
      show -(eisOmega^2) = (-1 : 𝓔)*eisOmega^2 by ring, map_mul, evalCubic_neg_one, one_mul, hω]

/-- At a fixed nonzero numerator c, the cubic symbol on primary denominators
is constant on classes modulo 9c. Strip the λ power, make the remaining
generator primary, then apply the two supplementary laws and reciprocity. -/
theorem fixed_symbol_congr (hR : DunnRadziwillReciprocity) {c a b : 𝓔}
    (hc : c ≠ 0) (ha : eisPrimary a) (hb : eisPrimary b) (hab : 9*c ∣ b-a) :
    eisEmbedding (cubicSymbol c a) = eisEmbedding (cubicSymbol c b) := by
  have h₉ := (dvd_mul_right (9 : 𝓔) c).trans hab
  obtain ⟨t, he, ht⟩ := (FiniteMultiplicity.of_prime_left eisLambda_prime
    hc).exists_eq_pow_mul_and_not_dvd
  have hLt : IsCoprime eisLambda t := eisLambda_prime.irreducible.coprime_iff_not_dvd.mpr ht
  have ht₃ : IsCoprime t (3 : 𝓔) := by
    have hpow : IsCoprime t (eisLambda ^ 2) := hLt.symm.pow_right
    rw [eisLambda_sq] at hpow
    simpa only [neg_neg] using hpow.neg_right
  obtain ⟨k,hkt,hk⟩ := exists_primary_generator ((isCoprime_span_singleton_iff _ _).mpr ht₃)
  obtain ⟨u, hu⟩ := span_singleton_eq_span_singleton.mp hkt
  have hLam : evalCubic ha eisLambda = evalCubic hb eisLambda := by
    rw [evalCubic_apply, evalCubic_apply, (cubic_supplements_congr hR ha h₉).1]
  have hkdiv : k ∣ b-a := (show k ∣ t from ⟨u,hu.symm⟩).trans
    ((show t ∣ c from he ▸ dvd_mul_left _ _).trans ((dvd_mul_left _ _).trans hab))
  have hχ : evalCubic ha k = evalCubic hb k := by
    rw [evalCubic_apply, evalCubic_apply, hR.1 _ _ hk ha, hR.1 _ _ hk hb]
    exact congrArg eisEmbedding (powerResidueSymbol_congr (mk_eq_iff.mpr hkdiv)).symm
  rw [← evalCubic_apply ha, ← evalCubic_apply hb, he, ← hu]
  simp only [map_mul, map_pow, hLam, hχ, evalCubic_unit_congr hR ha hb h₉ u]

/-- Data for the reduced fixed shift and its pairwise coprime active denominators. -/
structure Moduli (ι : Type*) where
  a₀ : 𝓔
  c₀ : 𝓔
  p : ι → 𝓔
  c₀_ne_zero : c₀ ≠ 0
  primary_a₀ : eisPrimary a₀
  three_dvd_c₀ : (3 : 𝓔) ∣ c₀
  fixed_coprime : IsCoprime a₀ c₀
  primary_p (i : ι) : eisPrimary (p i)
  tame_coprime (i : ι) : IsCoprime (p i) (eisLambda ^ 2 * c₀)
  pairwise : Pairwise (IsCoprime on p)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Moduli

variable (S : Moduli ι)

def D := eisLambda ^ 2 * S.c₀

def r := ∏ i, S.p i

def cofactor (i : ι) := ∏ j ∈ univ.erase i, S.p j

theorem prime_mul_cofactor (i : ι) : S.p i * S.cofactor i = S.r :=
  univ.mul_prod_erase _ (mem_univ i)

omit [Fintype ι] [DecidableEq ι] in
theorem D_ne_zero : S.D ≠ 0 := mul_ne_zero (pow_ne_zero _ eisLambda_prime.ne_zero) S.c₀_ne_zero

omit [DecidableEq ι] in
theorem r_ne_zero : S.r ≠ 0 :=
  prod_ne_zero_iff.mpr fun i _ => fun h => (S.primary_p i).lambda_not_dvd (h ▸ dvd_zero _)

omit [DecidableEq ι] in
theorem coprime_D_r : IsCoprime S.D S.r := IsCoprime.prod_right fun i _ => (S.tame_coprime i).symm

omit [Fintype ι] [DecidableEq ι] in
theorem coprime_D_a₀ : IsCoprime S.D S.a₀ := by
  rw [D, eisLambda_sq, neg_mul]
  exact (S.fixed_coprime.of_isCoprime_of_dvd_right S.three_dvd_c₀).symm.mul_left
    S.fixed_coprime.symm
    |>.neg_left

private theorem coprime_cofactor (i : ι) : IsCoprime (S.p i) (S.cofactor i) :=
  IsCoprime.prod_right fun _ hj => S.pairwise (ne_of_mem_erase hj).symm

def sigma (i : ι) : (Residue (S.p i))ˣ :=
  residueUnit ((S.tame_coprime i).mul_right (S.coprime_cofactor i))

def epsilon (i : ι) : (Residue (S.p i))ˣ := -(S.sigma i ^ 2)⁻¹

/-- With a primary fixed numerator and primary prime generators this numerator
is primary for every tuple of representatives. -/
def numerator (h : ι → 𝓔) : 𝓔 :=
  S.a₀ * S.r + S.D * ∑ i, h i * S.cofactor i

theorem numerator_mod_fixed (h : ι → 𝓔) :
    red S.D (S.numerator h) = red S.D (S.a₀ * S.r) := by
  simp [numerator, mk_zero_iff.mpr (dvd_refl S.D)]

private theorem cofactor_zero {i j : ι} (hij : i ≠ j) :
    red (S.p i) (S.cofactor j) = 0 :=
  mk_zero_iff.mpr (dvd_prod_of_mem _ (mem_erase.mpr ⟨hij, mem_univ _⟩))

theorem numerator_mod_prime (h : ι → 𝓔) (i : ι) :
    red (S.p i) (S.numerator h) = (S.sigma i : Residue (S.p i)) * red (S.p i) (h i) := by
  have hr : red (S.p i) S.r = 0 := mk_zero_iff.mpr ⟨_, (S.prime_mul_cofactor i).symm⟩
  simp only [numerator, map_add, map_mul, hr, mul_zero, zero_add, map_sum]
  rw [sum_eq_single i (fun j _ hji => by rw [S.cofactor_zero hji.symm, mul_zero])
    (fun hi => (hi (mem_univ i)).elim)]
  rw [sigma, residueUnit_val, map_mul]
  dsimp only [D]
  ring

theorem numerator_primary (h : ι → 𝓔) : eisPrimary (S.numerator h) := by
  have hr : eisPrimary S.r := by
    rw [eisPrimary_iff_mk_eq_one, r, map_prod]
    exact prod_eq_one fun i _ => (eisPrimary_iff_mk_eq_one _).mp (S.primary_p i)
  rw [eisPrimary_iff_mk_eq_one]
  have hD : red (3 : 𝓔) S.D = 0 := mk_zero_iff.mpr (dvd_mul_of_dvd_right S.three_dvd_c₀ _)
  simp only [numerator, map_add, map_mul, hD, zero_mul, add_zero,
    (eisPrimary_iff_mk_eq_one _).mp S.primary_a₀, (eisPrimary_iff_mk_eq_one _).mp hr, mul_one]

theorem numerator_coprime (h : ι → 𝓔) (hh : ∀ i, IsUnit (red (S.p i) (h i))) :
    IsCoprime (S.numerator h) (S.c₀*S.r) := by
  apply IsCoprime.mul_right
  · apply IsCoprime.of_isCoprime_of_dvd_right (y := S.D) _ (dvd_mul_left _ _)
    apply IsCoprime.symm
    rw [← unit_mk_iff, S.numerator_mod_fixed, map_mul]
    exact (unit_mk_iff.mpr S.coprime_D_a₀).mul (unit_mk_iff.mpr S.coprime_D_r)
  · apply IsCoprime.prod_right
    intro i _
    apply IsCoprime.symm
    rw [← unit_mk_iff, S.numerator_mod_prime]
    exact (S.sigma i).isUnit.mul (hh i)

theorem exists_matrix (h : ι → 𝓔) (hh : ∀ i, IsUnit (red (S.p i) (h i))) :
    ∃ b d : 𝓔, S.numerator h * d - b * (S.c₀*S.r) = 1 ∧ (3 : 𝓔) ∣ b ∧ eisPrimary d :=
  exists_patterson_cusp_matrix (S.numerator_coprime h hh) (S.numerator_primary h)
    (dvd_mul_of_dvd_left S.three_dvd_c₀ _)

private theorem emb_ne_zero {a : 𝓔} (ha : a ≠ 0) : eisEmbedding a ≠ 0 :=
  (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr ha

theorem shift_eq (h : ι → 𝓔) :
    eisEmbedding (S.numerator h) / eisEmbedding (S.c₀ * S.r) =
      eisEmbedding S.a₀ / eisEmbedding S.c₀ +
        eisEmbedding eisLambda ^ 2 * ∑ i, eisEmbedding (h i) / eisEmbedding (S.p i) := by
  simp only [numerator, D, map_add, map_mul, map_pow, map_sum, add_div, Finset.mul_sum]
  congr 1
  · field_simp [emb_ne_zero S.r_ne_zero]
  · rw [Finset.sum_div]
    apply sum_congr rfl
    intro i _
    have hpi : S.p i ≠ 0 := fun h => (S.primary_p i).lambda_not_dvd (h ▸ dvd_zero _)
    have hcof : S.cofactor i ≠ 0 := fun h => S.r_ne_zero (by
      rw [← S.prime_mul_cofactor i, h, mul_zero])
    rw [← S.prime_mul_cofactor i, map_mul]
    field_simp [emb_ne_zero S.c₀_ne_zero, emb_ne_zero hpi, emb_ne_zero hcof]

omit [Fintype ι] [DecidableEq ι] in
/-- Lift a prescribed unit at a tame prime to a numerator divisible by any
coprime fixed modulus. -/
theorem exists_lift (i : ι) (M : 𝓔) (hM : IsCoprime (S.p i) M) (u : (Residue (S.p i))ˣ) :
    ∃ x : 𝓔, M ∣ x ∧ red (S.p i) x = u := by
  let v := residueUnit hM
  let y : Residue (S.p i) := ↑(v⁻¹ * u)
  refine ⟨M * Quotient.out y, dvd_mul_right _ _, ?_⟩
  rw [map_mul, Ideal.Quotient.mk_out]
  change red (S.p i) M * (↑(v⁻¹ * u) : Residue (S.p i)) = _
  rw [← residueUnit_val hM]
  exact_mod_cast Units.mul_inv_cancel_left v u

theorem numerator_congr (M : 𝓔) (h : ι → 𝓔) (hh : ∀ i, M ∣ h i) :
    red M (S.numerator h) = red M (S.a₀ * S.r) := by
  simp only [numerator, map_add, map_mul, map_sum]
  simp [fun i => mk_zero_iff.mpr (hh i)]

private theorem crt_congr {x y₀ : 𝓔} {y : ι → 𝓔}
    (h₀ : red S.D x = red S.D (y₀*S.r))
    (hi : ∀ i, red (S.p i) x = red (S.p i) (y i * (S.D * S.cofactor i))) :
    S.D * S.r ∣ x - (y₀ * S.r + ∑ i, y i * (S.D * S.cofactor i)) := by
  apply S.coprime_D_r.mul_dvd
  · apply mk_eq_iff.mp
    simpa [map_sum, mk_zero_iff.mpr (dvd_refl S.D)] using h₀
  · apply Fintype.prod_dvd_of_coprime S.pairwise
    intro i
    apply mk_eq_iff.mp
    have hr : red (S.p i) S.r = 0 := mk_zero_iff.mpr ⟨_, (S.prime_mul_cofactor i).symm⟩
    simp only [map_add, map_mul, hr, mul_zero, zero_add, map_sum]
    rw [sum_eq_single i (fun j _ hji => by rw [S.cofactor_zero hji.symm, mul_zero, mul_zero])
      (fun hi => (hi (mem_univ i)).elim)]
    simpa using hi i

private lemma differentCharacter_sum (f : ι → ℂ) :
    differentCharacter (∑ i, f i) = ∏ i, differentCharacter (f i) := by
  induction (univ : Finset ι) using Finset.induction_on with
  | empty => simp [differentCharacter]
  | insert i t hi h => rw [sum_insert hi, prod_insert hi, differentCharacter_add, h]

/-- CRT splitting for the different character on D times the tame conductor. -/
theorem phase_split {x : 𝓔} (y₀ : Residue S.D) (y : ∀ i, Residue (S.p i))
    (h₀ : red S.D x = y₀ * red S.D S.r)
    (hi : ∀ i, red (S.p i) x = y i * red (S.p i) (S.D * S.cofactor i)) :
    differentCharacter (eisEmbedding x / eisEmbedding (S.D * S.r)) =
      phase S.D y₀ * ∏ i, phase (S.p i) (y i) := by
  let t₀ := Quotient.out y₀
  let t (i : ι) := Quotient.out (y i)
  have he := S.crt_congr (x := x) (y₀ := t₀) (y := t)
    (by simpa [t₀, red, Ideal.Quotient.mk_out] using h₀)
    (fun i => by simpa [t, red, Ideal.Quotient.mk_out] using hi i)
  rw [differentCharacter_div_congr he]
  have hfrac : eisEmbedding (t₀*S.r + ∑ i, t i * (S.D * S.cofactor i)) / eisEmbedding (S.D*S.r) =
      eisEmbedding t₀ / eisEmbedding S.D + ∑ i, eisEmbedding (t i) / eisEmbedding (S.p i) := by
    simp only [map_add, map_sum, map_mul, add_div, sum_div]
    congr 1
    · field_simp [emb_ne_zero S.r_ne_zero]
    · apply sum_congr rfl
      intro i _
      have hp : S.p i ≠ 0 := fun h => (S.primary_p i).lambda_not_dvd (h ▸ dvd_zero _)
      have hco : S.cofactor i ≠ 0 := fun h => S.r_ne_zero (by
        rw [← S.prime_mul_cofactor i, h, mul_zero])
      rw [← S.prime_mul_cofactor i, map_mul]
      field_simp [emb_ne_zero S.D_ne_zero, emb_ne_zero hp, emb_ne_zero hco]
  rw [hfrac, differentCharacter_add, differentCharacter_sum]
  rfl

/-- Before reflection, the trace phase at the common-denominator cusp splits
into the fixed translate and the tame additive Fourier characters. -/
theorem input_phase (h : ι → 𝓔) (m : 𝓔) :
    pattersonCharacter ((eisEmbedding m / eisEmbedding eisLambda ^ 3) *
        (eisEmbedding (S.numerator h) / eisEmbedding (S.c₀*S.r))) =
      pattersonCharacter ((eisEmbedding m / eisEmbedding eisLambda ^ 3) *
        (eisEmbedding S.a₀ / eisEmbedding S.c₀)) *
        ∏ i, phase (S.p i) (red (S.p i) (h i) * red (S.p i) m) := by
  let t := eisEmbedding m / eisEmbedding eisLambda^3
  change traceCharacter (t * _) = traceCharacter (t * _) * _
  rw [S.shift_eq, mul_add, traceCharacter_add]
  congr 1
  rw [← differentCharacter_lambda_mul, ← mul_assoc, ← mul_assoc, Finset.mul_sum,
    differentCharacter_sum]
  apply prod_congr rfl
  intro i _
  rw [← map_mul, phase_mk, map_mul]
  congr 1
  dsimp [t]
  field_simp [emb_ne_zero eisLambda_prime.ne_zero]

private theorem unit_inverse_of_eq_one {R : Type*} [CommRing R] (u : Rˣ) {x : R}
    (h : (u : R) * x = 1) : x = (↑u⁻¹ : R) := by
  calc
    _ = ↑u⁻¹ * ((u : R) * x) := by simp
    _ = _ := by rw [h, mul_one]

private theorem fixed_residue {R : Type*} [CommRing R] (A r : Rˣ) (d m : R)
    (h : (↑(A*r) : R) * d = 1) :
    -(d*m) = (-(↑((A*r^2)⁻¹) : R) * m) * (r : R) := by
  have he : (A*r)⁻¹ = (A*r^2)⁻¹ * r := by
    apply inv_eq_of_mul_eq_one_left
    rw [mul_assoc, show r*(A*r) = A*r^2 by rw [pow_two]; ac_rfl, inv_mul_cancel]
  rw [unit_inverse_of_eq_one _ h, he, Units.val_mul]
  ring

private theorem prime_residue {R : Type*} [CommRing R] (σ u : Rˣ) (d m : R)
    (h : (↑(σ*u) : R) * d = 1) :
    -(d*m) = (↑(-(σ^2)⁻¹ : Rˣ) * m * (↑u⁻¹ : R)) * (σ : R) := by
  have he : (σ*u)⁻¹ = (σ^2)⁻¹ * u⁻¹ * σ := by simp [pow_two, mul_assoc, mul_comm]
  rw [unit_inverse_of_eq_one _ h, he]
  push_cast
  ring

/-- The fixed character is indexed only by the fixed numerator and the class of
the tame conductor modulo D. -/
def fixedPhase (D : 𝓔) (A r : Residue D) (m : 𝓔) : ℂ :=
  phase D (-Ring.inverse (A*r^2) * red D m)

/-- The reflected additive phase splits with σᵢ = D r/pᵢ and εᵢ = −σᵢ⁻².
Its fixed factor is independent of all tame Fourier representatives. -/
theorem dual_phase (u : ∀ i, (Residue (S.p i))ˣ) (h : ι → 𝓔)
    (hu : ∀ i, red (S.p i) (h i) = u i) {b d : 𝓔}
    (hdet : S.numerator h * d - b * (S.c₀*S.r) = 1) (hb : (3 : 𝓔) ∣ b) (m : 𝓔) :
    pattersonCharacter ((eisEmbedding m / eisEmbedding eisLambda ^ 3) *
        (-eisEmbedding d / eisEmbedding (S.c₀*S.r))) =
      fixedPhase S.D (red S.D S.a₀) (red S.D S.r) m *
        ∏ i, phase (S.p i) ((S.epsilon i : Residue (S.p i)) * red (S.p i) m *
          (↑(u i)⁻¹ : Residue (S.p i))) := by
  have harg : pattersonCharacter ((eisEmbedding m / eisEmbedding eisLambda ^ 3) *
        (-eisEmbedding d / eisEmbedding (S.c₀*S.r))) =
      differentCharacter (eisEmbedding (-(d*m)) / eisEmbedding (S.D*S.r)) := by
    rw [differentCharacter_eq_traceCharacter_div]
    change traceCharacter _ = traceCharacter _
    congr 1
    simp only [D, map_neg, map_mul, map_pow]
    field_simp
  rw [harg]
  let A := residueUnit S.coprime_D_a₀
  let R := residueUnit S.coprime_D_r
  let f := red S.D
  have hAR : (↑(A*R) : Residue S.D) * f d = 1 := by
    have hbc : f (b*(S.c₀*S.r)) = 0 := by
      obtain ⟨t,ht⟩ := hb
      apply mk_zero_iff.mpr
      exact ⟨-t*S.r, by rw [D, ht, eisLambda_sq]; ring⟩
    have he := congrArg f (sub_eq_iff_eq_add.mp hdet)
    simp only [map_add, map_one, hbc, add_zero] at he
    simpa only [map_mul, S.numerator_mod_fixed, Units.val_mul, A, R, residueUnit_val, f] using (show
      red S.D (S.numerator h * d) = 1 from he)
  have hf : (↑(A * R^2) : Residue S.D) = f S.a₀ * f S.r ^ 2 := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, A, R, residueUnit_val, f]
  unfold fixedPhase
  rw [← hf, Ring.inverse_unit]
  apply S.phase_split
  · simpa only [map_neg, map_mul, R, residueUnit_val] using fixed_residue A R (f d) (f m) hAR
  · intro i
    let g := red (S.p i)
    have hr : g S.r = 0 := mk_zero_iff.mpr ⟨_, (S.prime_mul_cofactor i).symm⟩
    have had : (↑(S.sigma i * u i) : Residue (S.p i)) * g d = 1 := by
      have he := congrArg g (sub_eq_iff_eq_add.mp hdet)
      change red (S.p i) _ = red (S.p i) _ at he
      have hr' : red (S.p i) S.r = 0 := hr
      simpa only [map_mul, map_add, map_one, hr', mul_zero, add_zero, S.numerator_mod_prime, hu,
        Units.val_mul, g] using he
    have he := prime_residue (S.sigma i) (u i) (g d) (g m) had
    change g (-(d*m)) = _ * g (S.D * S.cofactor i)
    rw [map_neg, map_mul g d]
    simpa only [epsilon, sigma, residueUnit_val, D, g] using he

/-- All local Fourier tuples admit representatives divisible by a prescribed
coprime modulus and matrices with the common denominator c₀r. -/
theorem exists_matrices (M : 𝓔) (hM : ∀ i, IsCoprime (S.p i) M) :
    ∃ (H : (∀ i, (Residue (S.p i))ˣ) → ι → 𝓔) (b d : (∀ i, (Residue (S.p i))ˣ) → 𝓔),
      ∀ u, (∀ i, M ∣ H u i ∧ red (S.p i) (H u i) = u i) ∧
        red M (S.numerator (H u)) = red M (S.a₀*S.r) ∧
        S.numerator (H u) * d u - b u * (S.c₀*S.r) = 1 ∧ (3 : 𝓔) ∣ b u ∧ eisPrimary (d u) := by
  choose lift hl using S.exists_lift
  let H (u : ∀ i, (Residue (S.p i))ˣ) (i : ι) := lift i M (hM i) (u i)
  have Hspec (u : ∀ i, (Residue (S.p i))ˣ) (i : ι) :
      M ∣ H u i ∧ red (S.p i) (H u i) = u i := hl i M (hM i) (u i)
  have ex (u : ∀ i, (Residue (S.p i))ˣ) := S.exists_matrix (H u)
    (fun i => (Hspec u i).2 ▸ (u i).isUnit)
  choose b d hd using ex
  exact ⟨H, b, d, fun u => ⟨Hspec u, S.numerator_congr _ _ (fun i => (Hspec u i).1), hd u⟩⟩

omit [Fintype ι] in
private theorem cubicSymbol_prod (a : 𝓔) (t : Finset ι) :
    cubicSymbol a (∏ i ∈ t, S.p i) = ∏ i ∈ t, cubicSymbol a (S.p i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [prod_insert hi, prod_insert hi, ← ih, cubicSymbol, ← span_singleton_mul_span_singleton,
      powerResidueSymbol_mul_right]
    rfl

open scoped ComplexConjugate in
/-- Cubic reciprocity splits the Kubota multiplier into its fixed factor and
the inverse square of the local sextic characters. -/
theorem multiplier_split (hR : DunnRadziwillReciprocity) (hgood : ∀ i, AwayFromSix (span {S.p i}))
    (h : ι → 𝓔) :
    conj (pattersonMultiplier (S.numerator h) (S.c₀*S.r)) =
      conj (eisEmbedding (cubicSymbol S.c₀ (S.numerator h))) *
        ∏ i, ((sexticChar (hgood i)) ^ 2)⁻¹ (red (S.p i) (S.numerator h)) := by
  have ha := S.numerator_primary h
  have hr : eisPrimary S.r := by
    rw [eisPrimary_iff_mk_eq_one, r, map_prod]
    exact prod_eq_one fun i _ => (eisPrimary_iff_mk_eq_one _).mp (S.primary_p i)
  have h₃ : IsCoprime (span {S.numerator h}) (span {3}) :=
    (isUnit_mk_iff_coprime_span _ _).mp (by
      rw [(eisPrimary_iff_mk_eq_one _).mp ha]; exact isUnit_one) |>.symm
  rw [pattersonMultiplier, ite_eq_right (mul_ne_zero S.c₀_ne_zero S.r_ne_zero)]
  rw [show cubicSymbol (S.c₀*S.r) (S.numerator h) =
      cubicSymbol S.c₀ (S.numerator h) * cubicSymbol S.r (S.numerator h) from
      powerResidueSymbol_three_mul h₃ _ _, hR.1 _ _ hr ha, r, S.cubicSymbol_prod _ univ,
    map_mul, map_mul, map_prod, map_prod]
  congr 1
  apply prod_congr rfl
  intro i _
  let P := span {S.p i}
  let := Ring.HasFiniteQuotients.finiteQuotient (hgood i).1
  let χ := sexticChar (hgood i)
  have he : eisEmbedding (cubicSymbol (S.numerator h) (S.p i)) =
      (χ^2) (red (S.p i) (S.numerator h)) := by
    rw [MulChar.pow_apply' _ two_ne_zero]
    change _ = eisEmbedding (powerResidueSymbol 6 _ _) ^ 2
    rw [← map_pow, powerResidueSymbol_six_sq (hgood i).2]
    exact congrArg eisEmbedding (powerResidueSymbol_congr (Ideal.Quotient.mk_out _)).symm
  rw [he]
  exact MulChar.star_apply' _ _

attribute [local instance] Ideal.Quotient.field


open scoped ComplexConjugate in
/-- Joint Fourier contribution of the active primes at one fixed frequency and
active conductor, before summing the tame components separately. -/
def activeBlock [∀ i, (span {S.p i}).IsMaximal]
    [∀ i, Fintype (Residue (S.p i))] [∀ i, DecidableEq (Residue (S.p i))]
    (hgood : ∀ i, AwayFromSix (span {S.p i})) (j : ι → ℕ)
    (H : (∀ i, (Residue (S.p i))ˣ) → ι → 𝓔) (d : (∀ i, (Residue (S.p i))ˣ) → 𝓔) (m : 𝓔) : ℂ :=
  (∑ u : ∀ i, (Residue (S.p i))ˣ,
      (∏ i, ReflectionTame.coefficient ((sexticChar (hgood i)) ^ j i) (phase (S.p i)) (u i)) *
      conj (pattersonMultiplier (S.numerator (H u)) (S.c₀*S.r)) *
      pattersonCharacter ((eisEmbedding m / eisEmbedding eisLambda ^ 3) *
        (-eisEmbedding (d u) / eisEmbedding (S.c₀*S.r))))

open scoped ComplexConjugate in
/-- Summing the reflected phases and multipliers over active tuples produces
the exact local sums evaluated in the tame table. -/
theorem sum_dual_phase_eq_activeSum [∀ i, (span {S.p i}).IsMaximal]
    [∀ i, Fintype (Residue (S.p i))] [∀ i, DecidableEq (Residue (S.p i))]
    (hR : DunnRadziwillReciprocity) (hgood : ∀ i, AwayFromSix (span {S.p i})) (j : ι → ℕ)
    (H : (∀ i, (Residue (S.p i))ˣ) → ι → 𝓔) (b d : (∀ i, (Residue (S.p i))ˣ) → 𝓔)
    (hH : ∀ u i, red (S.p i) (H u i) = u i)
    (hdet : ∀ u, S.numerator (H u)*d u - b u*(S.c₀*S.r) = 1) (hb : ∀ u, (3 : 𝓔) ∣ b u)
    (κ : ℂ) (hκ : ∀ u, conj (eisEmbedding (cubicSymbol S.c₀ (S.numerator (H u)))) = κ) (m : 𝓔) :
    S.activeBlock hgood j H d m =
    κ * fixedPhase S.D (red S.D S.a₀) (red S.D S.r) m *
      ∏ i, ReflectionTame.activeSum (sexticChar (hgood i)) (j i) (phase (S.p i))
        (S.sigma i) (S.epsilon i) (red (S.p i) m) := by
  simp only [activeBlock, ReflectionTame.activeSum, Fintype.prod_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro u _
  rw [S.multiplier_split hR hgood, hκ u, S.dual_phase u (H u) (hH u) (hdet u) (hb u) m]
  simp only [S.numerator_mod_prime, hH, Units.val_inv_eq_inv_val, Finset.prod_mul_distrib]
  ring

open scoped ComplexConjugate in
/-- Both fixed factors can be read from the tame conductor modulo 9c₀. -/
def fixedWeight (c₀ a₀ r m : 𝓔) : ℂ :=
  let D := eisLambda^2*c₀
  conj (eisEmbedding (cubicSymbol c₀ (a₀*r))) * fixedPhase D (red D a₀) (red D r) m

theorem fixedWeight_congr (hR : DunnRadziwillReciprocity) {c₀ a₀ r r' : 𝓔} (hc : c₀ ≠ 0)
    (ha : eisPrimary a₀) (hr : eisPrimary r) (hr' : eisPrimary r')
    (h : red (9*c₀) r = red (9*c₀) r') (m : 𝓔) : fixedWeight c₀ a₀ r m = fixedWeight c₀ a₀ r' m
      := by
  have hcub := fixed_symbol_congr hR hc (ha.mul hr) (ha.mul hr')
    (show 9*c₀ ∣ a₀*r'-a₀*r by rw [← mul_sub]; exact dvd_mul_of_dvd_right (mk_eq_iff.mp h.symm) _)
  have hred : red (eisLambda^2*c₀) r = red (eisLambda^2*c₀) r' :=
    mk_eq_iff.mpr ((show eisLambda^2*c₀ ∣ 9*c₀ from ⟨-3, by rw [eisLambda_sq]; ring⟩).trans
      (mk_eq_iff.mp h))
  simp only [fixedWeight, hcub, hred]

omit [Fintype ι] [DecidableEq ι] in
theorem coprime_fixed_modulus (i : ι) : IsCoprime (S.p i) (9*S.c₀) := by
  have h := S.tame_coprime i
  rw [eisLambda_sq, neg_mul] at h
  have h' : IsCoprime (S.p i) (3*S.c₀) := by simpa only [neg_neg] using h.neg_right
  have ht := IsCoprime.mul_right_iff.mp h'
  rw [show (9 : 𝓔) = 3^2 by norm_num]
  exact ht.1.pow_right.mul_right ht.2

open scoped ComplexConjugate in
/-- For tame lifts divisible by the fixed modulus 9c₀, equation (13) evaluates
the entire active block up to a scalar of norm one independent of m. -/
theorem activeBlock_eq_factor [∀ i, (span {S.p i}).IsMaximal]
    [∀ i, Fintype (Residue (S.p i))] [∀ i, DecidableEq (Residue (S.p i))]
    (hR : DunnRadziwillReciprocity) (hgood : ∀ i, AwayFromSix (span {S.p i}))
    (hp : ∀ i, Prime (span {S.p i})) (j : ι → ℕ) (hj : ∀ i, j i < 6)
    (H : (∀ i, (Residue (S.p i))ˣ) → ι → 𝓔) (b d : (∀ i, (Residue (S.p i))ˣ) → 𝓔)
    (hH : ∀ u i, red (S.p i) (H u i) = u i) (hM : ∀ u i, 9*S.c₀ ∣ H u i)
    (hdet : ∀ u, S.numerator (H u)*d u - b u*(S.c₀*S.r) = 1) (hb : ∀ u, (3 : 𝓔) ∣ b u) :
    ∃ C : ℂ, ‖C‖ = 1 ∧ ∀ m : 𝓔,
      S.activeBlock hgood j H d m = C * fixedWeight S.c₀ S.a₀ S.r m *
        ∏ i, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m) := by
  have hψ (i : ι) : (phase (S.p i)).IsPrimitive := by
    rw [phase_eq_quotientDifferentCharacter (S.primary_p i)]
    exact quotientDifferentCharacter_isPrimitive (hgood i).1
  choose C hC hval using fun i => ReflectionTame.activeSum_eq_phase_mul_factor
    (orderOf_sexticChar_prime (hgood i) (hp i)) (hψ i) (hj i) (S.sigma i) (S.epsilon i)
  refine ⟨∏ i, C i, by simp [norm_prod, hC], fun m => ?_⟩
  have hr : eisPrimary S.r := by
    rw [eisPrimary_iff_mk_eq_one, r, map_prod]
    exact prod_eq_one fun i _ => (eisPrimary_iff_mk_eq_one _).mp (S.primary_p i)
  have hκ (u : ∀ i, (Residue (S.p i))ˣ) :
      conj (eisEmbedding (cubicSymbol S.c₀ (S.numerator (H u)))) =
        conj (eisEmbedding (cubicSymbol S.c₀ (S.a₀*S.r))) := by
    apply congrArg
    apply fixed_symbol_congr hR S.c₀_ne_zero (S.numerator_primary _) (S.primary_a₀.mul hr)
    exact mk_eq_iff.mp (S.numerator_congr _ _ (hM u)).symm
  rw [S.sum_dual_phase_eq_activeSum hR hgood j H b d hH hdet hb _ hκ]
  simp only [hval, prod_mul_distrib, fixedWeight, D]
  ac_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem fixedWeight_congr_frequency {c₀ a₀ r m n : 𝓔}
    (hm : red (eisLambda^2*c₀) m = red (eisLambda^2*c₀) n) :
    fixedWeight c₀ a₀ r m = fixedWeight c₀ a₀ r n := by
  simp only [fixedWeight, fixedPhase, hm]

/-- The same two exceptional moduli suffice for all fixed Fourier frequencies:
the conductor class is read modulo 72λ⁷ and the dual frequency modulo 8λ⁹. -/
theorem fixedWeight_congr_uniform (hR : DunnRadziwillReciprocity) {c₀ a₀ r r' m m' : 𝓔}
    (hc : c₀ ≠ 0) (hcL : c₀ ∣ 8*eisLambda^7) (ha : eisPrimary a₀)
    (hr : eisPrimary r) (hr' : eisPrimary r')
    (h : red (72*eisLambda^7) r = red (72*eisLambda^7) r')
    (hm : red (8*eisLambda^9) m = red (8*eisLambda^9) m') :
    fixedWeight c₀ a₀ r m = fixedWeight c₀ a₀ r' m' := by
  obtain ⟨k,hk⟩ := hcL
  have hd₁ : 9*c₀ ∣ 72*eisLambda^7 := ⟨k, by linear_combination 9*hk⟩
  have hd₂ : eisLambda^2*c₀ ∣ 8*eisLambda^9 := ⟨k, by linear_combination eisLambda^2*hk⟩
  exact (fixedWeight_congr hR hc ha hr hr' (mk_eq_iff.mpr (hd₁.trans (mk_eq_iff.mp h))) m).trans
    (fixedWeight_congr_frequency (mk_eq_iff.mpr (hd₂.trans (mk_eq_iff.mp hm))))

omit [DecidableEq ι] in
theorem norm_fixedWeight (m : 𝓔) : ‖fixedWeight S.c₀ S.a₀ S.r m‖ = 1 := by
  classical
  have hr : eisPrimary S.r := by
    rw [eisPrimary_iff_mk_eq_one, r, map_prod]
    exact prod_eq_one fun i _ => (eisPrimary_iff_mk_eq_one _).mp (S.primary_p i)
  have ha := S.primary_a₀.mul hr
  let n := span {S.a₀*S.r}
  have hn : n ≠ ⊥ := by simpa [n] using ha.ne_zero
  let := Ring.HasFiniteQuotients.finiteQuotient hn
  let := Fintype.ofFinite (𝓔 ⧸ n)
  let χ := cubicChar hn ha.coprime_three
  have hu : IsUnit (red (S.a₀*S.r) S.c₀) := unit_mk_iff.mpr
    (S.fixed_coprime.mul_left (S.coprime_D_r.symm.of_isCoprime_of_dvd_right (dvd_mul_left _ _)))
  have hc : ‖eisEmbedding (cubicSymbol S.c₀ (S.a₀*S.r))‖ = 1 := by
    change ‖eisEmbedding (powerResidueSymbol 3 S.c₀ n)‖ = 1
    have hu' : IsUnit (Ideal.Quotient.mk n S.c₀) := hu
    rw [← cubicChar_mk hn ha.coprime_three, ← hu'.unit_spec]
    exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity _)
  have hphase (d : 𝓔) (x : Residue d) : ‖phase d x‖ = 1 := by
    change ‖differentCharacter _‖ = 1
    simp [differentCharacter, Complex.norm_exp, Complex.mul_re]
  simp [fixedWeight, fixedPhase, hc, hphase]

/-- The lifts and matrices needed for the finite local table always exist and
all rows in the block have the same denominator c₀r. -/
theorem exists_activeBlock_eq_factor [∀ i, (span {S.p i}).IsMaximal]
    [∀ i, Fintype (Residue (S.p i))] [∀ i, DecidableEq (Residue (S.p i))]
    (hR : DunnRadziwillReciprocity) (hgood : ∀ i, AwayFromSix (span {S.p i}))
    (hp : ∀ i, Prime (span {S.p i})) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ (H : (∀ i, (Residue (S.p i))ˣ) → ι → 𝓔) (b d : (∀ i, (Residue (S.p i))ˣ) → 𝓔) (C : ℂ),
      ‖C‖ = 1 ∧ (∀ u, (∀ i, red (S.p i) (H u i) = u i) ∧
        S.numerator (H u)*d u - b u*(S.c₀*S.r) = 1 ∧ (3 : 𝓔) ∣ b u ∧ eisPrimary (d u)) ∧
      ∀ m : 𝓔, S.activeBlock hgood j H d m = C * fixedWeight S.c₀ S.a₀ S.r m *
        ∏ i, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m) := by
  obtain ⟨H, b, d, hs⟩ := S.exists_matrices (9*S.c₀) S.coprime_fixed_modulus
  obtain ⟨C, hC, he⟩ := S.activeBlock_eq_factor hR hgood hp j hj H b d
    (fun u i => ((hs u).1 i).2) (fun u i => ((hs u).1 i).1) (fun u => (hs u).2.2.1)
    (fun u => (hs u).2.2.2.1)
  exact ⟨H, b, d, C, hC, fun u => ⟨fun i => ((hs u).1 i).2, (hs u).2.2⟩, he⟩

end Moduli

/-- A surviving fixed Fourier translate has a reduced primary numerator and a
denominator dividing the original exceptional modulus. -/
theorem exists_fixed_cusp {W : RayResidue 7 → ℂ}
    (hW : ∀ g : RayResidue 3 → ℂ, ∑ x, W x * g (rayReduction x) = 0)
    {h : RayResidue 7} (hh : rayFourierCoeff 7 W h ≠ 0) :
    ∃ a c : 𝓔, c ≠ 0 ∧ eisPrimary a ∧ (3 : 𝓔) ∣ c ∧ IsCoprime a c ∧
      c ∣ 8 * eisLambda^7 ∧ rayShift h = eisEmbedding a / eisEmbedding c := by
  obtain ⟨a,b,c,d,hc,hdet,ha,_,h₃,_,he⟩ :=
    exists_rayShift_cusp hW hh 0 (r := 1) one_ne_zero isCoprime_one_right
  have he' : rayShift h = eisEmbedding a / eisEmbedding c := by simpa using he
  have hcop : IsCoprime a c := ⟨d, -b, by linear_combination hdet⟩
  have hL : (8 : 𝓔) * eisLambda^7 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _
    eisLambda_prime.ne_zero)
  have he'' := (div_eq_div_iff
    ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hL)
    ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc)).mp he'
  have cross : (eisLambda^2 * Quotient.out h) * c = a * (8 * eisLambda^7) :=
    eisEmbedding_injective (by simpa only [map_mul] using he'')
  exact ⟨a,c,hc,ha,h₃,hcop,hcop.symm.dvd_of_dvd_mul_left ⟨_, cross.symm.trans (mul_comm _ _)⟩,he'⟩

/-- Every good prime is coprime to both the fixed reduced denominator and its
additional different factor in the reflected phase. -/
theorem good_coprime_fixed {p c₀ : 𝓔} (hp : AwayFromSix (span {p})) (hc : c₀ ∣ 8*eisLambda^7) :
    IsCoprime p (eisLambda^2*c₀) := by
  have h₆ := (isCoprime_span_singleton_iff _ _).mp hp.2
  have h₂ := h₆.of_isCoprime_of_dvd_right (show (2 : 𝓔) ∣ 6 from ⟨3, by norm_num⟩)
  have hL := h₆.of_isCoprime_of_dvd_right (show eisLambda ∣ (6 : 𝓔) from
    ⟨-2*eisLambda,
      by rw [show eisLambda*(-2*eisLambda) = -2 * eisLambda^2 by ring, eisLambda_sq]; norm_num⟩)
  have h₈ : IsCoprime p (8 : 𝓔) := by
    rw [show (8 : 𝓔) = 2^3 by norm_num]
    exact h₂.pow_right
  exact hL.pow_right.mul_right ((h₈.mul_right hL.pow_right).of_isCoprime_of_dvd_right hc)

end Masullo.QRH.MeanSquare.ReflectionCRT
