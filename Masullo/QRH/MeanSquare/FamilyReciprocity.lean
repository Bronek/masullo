import Masullo.QRH.MeanSquare.GaussPair
import Masullo.QRH.MeanSquare.Sieve

/-! # The reciprocity sign for the primary quadratic Hecke family -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
local notation "R₄" => 𝓔 ⧸ span {(4 : 𝓔)}

/-- Unit classes of primary generators modulo four. -/
abbrev QuadraticFamilyClass := R₄ˣ

instance : Finite QuadraticFamilyClass := by
  let := Ring.HasFiniteQuotients.finiteQuotient (I := span {(4 : 𝓔)}) (by simp)
  infer_instance

/-- On good ideals the class is the residue of the primary generator modulo four. -/
def familyClass (n : Ideal 𝓔) : QuadraticFamilyClass := open Classical in
  if h : IsUnit (Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator n)) then h.unit else 1

private lemma familyClass_val {n : Ideal 𝓔} (hn : AwayFromSix n) :
    (familyClass n : R₄) = Ideal.Quotient.mk _ (generator n) := by
  have h₂ : IsCoprime n (span {(2 : 𝓔)}) := hn.2.of_isCoprime_of_dvd_right
    (span_singleton_dvd_span_singleton_iff_dvd.mpr ⟨3, by norm_num⟩)
  have h₄ : IsCoprime n (span {(4 : 𝓔)}) := by
    simpa only [span_singleton_pow, show (2 : 𝓔) ^ 2 = 4 by norm_num] using h₂.pow_right (n := 2)
  have hu := (isUnit_mk_iff_coprime_span (span {(4 : 𝓔)}) (generator n)).mpr
    (by rwa [span_generator, isCoprime_comm])
  rw [familyClass, dite_eq_left hu, IsUnit.unit_spec]

@[simp] theorem familyClass_one : familyClass (1 : Ideal 𝓔) = 1 := by
  apply Units.ext
  rw [familyClass_val (show AwayFromSix 1 from ⟨one_ne_zero, isCoprime_one_left⟩),
    generator_one, map_one, Units.val_one]

theorem familyClass_mul {a b : Ideal 𝓔} (ha : AwayFromSix a) (hb : AwayFromSix b) :
    familyClass (a * b) = familyClass a * familyClass b := by
  apply Units.ext
  rw [familyClass_val (ha.mul hb), generator_mul ha.coprime_three hb.coprime_three, map_mul,
    Units.val_mul, familyClass_val ha, familyClass_val hb]

private lemma quadraticGauss_ne_zero {n : Ideal 𝓔} (hn : Starred n) :
    normalizedGauss n 3 ≠ 0 := by
  intro hz
  have h := norm_normalizedGauss_eq_one hn (j := 3) (by decide) (by decide)
  simp [hz] at h

private lemma familyClass_gauss (quad : DeloupTuraevTheorem1) {n : Ideal 𝓔} (hn : Starred n) :
    DeloupTuraev.quadraticRayValue (familyClass n : R₄) = normalizedGauss n 3 := by
  rw [familyClass_val hn.1, DeloupTuraev.quadraticRayValue_mk quad hn.1.1,
    normalizedGauss_three_eq_quadraticExponentialSum hn]

private def gaussRatio (u v : QuadraticFamilyClass) : ℂ :=
  DeloupTuraev.quadraticRayValue ((u : R₄) * (v : R₄)) /
    (DeloupTuraev.quadraticRayValue u * DeloupTuraev.quadraticRayValue v)

/-- The root-of-unity correction in quadratic reciprocity. -/
def familySign (u v : QuadraticFamilyClass) : ℂ := open Classical in
  if gaussRatio u v = -1 then -1 else 1

theorem familySign_sq (u v : QuadraticFamilyClass) : familySign u v ^ 2 = 1 := by
  classical
  unfold familySign
  split <;> norm_num

private lemma symbol_sq {a b : Ideal 𝓔} (hb : AwayFromSix b) (h : IsCoprime b a) :
    primaryQuadraticSymbol a b ^ 2 = 1 := by
  have hc : IsCoprime b (span {generator a}) := by rwa [span_generator]
  simp only [primaryQuadraticSymbol, ← pow_mul, ← map_pow, powerResidueSymbol_six_pow_six hb.1 hb.2,
    ite_eq_left hc, map_one]

/-- Interchanging two coprime, squarefree ideals changes the primary quadratic symbol
by the fixed sign of their classes modulo four. -/
theorem primaryQuadraticSymbol_reciprocity (quad : DeloupTuraevTheorem1) {a b : Ideal 𝓔}
    (ha : Starred a) (hb : Starred b) (h : IsCoprime a b) :
    primaryQuadraticSymbol b a = primaryQuadraticSymbol a b *
      familySign (familyClass a) (familyClass b) := by
  classical
  have hab : Starred (a * b) := ⟨ha.1.mul hb.1, squarefree_mul_iff.mpr ⟨h.isRelPrime, ha.2, hb.2⟩⟩
  have hr : gaussRatio (familyClass a) (familyClass b) =
      primaryQuadraticSymbol b a * primaryQuadraticSymbol a b := by
    rw [gaussRatio, ← Units.val_mul, ← familyClass_mul ha.1 hb.1, familyClass_gauss quad hab,
      familyClass_gauss quad ha, familyClass_gauss quad hb, normalizedGauss_mul ha.1 hb.1 h
        (by decide : 3 ≠ 0),
      mul_div_cancel_left₀ _ (mul_ne_zero (quadraticGauss_ne_zero ha)
        (quadraticGauss_ne_zero hb)), mul_pow]
    rfl
  have hx := symbol_sq ha.1 h
  have hy := symbol_sq hb.1 h.symm
  have hs : (gaussRatio (familyClass a) (familyClass b)) ^
    2 = 1 := by rw [hr, mul_pow, hx, hy, one_mul]
  have hsign : familySign (familyClass a) (familyClass b) = gaussRatio (familyClass a)
    (familyClass b) := by
    rcases sq_eq_one_iff.mp hs with he | he <;> norm_num [familySign, he]
  rw [hsign, hr]
  linear_combination -(primaryQuadraticSymbol b a) * hy

/-- Equal classes have the same quadratic character at the unit `-1`. -/
theorem sextic_neg_one_cube_eq_of_familyClass_eq (quad : DeloupTuraevTheorem1) {a b : Ideal 𝓔}
    (ha : Starred a) (hb : Starred b) (he : familyClass a = familyClass b) :
    sextic a (-1) ^ 3 = sextic b (-1) ^ 3 := by
  have hg : normalizedGauss a 3 = normalizedGauss b 3 := by
    rw [← familyClass_gauss quad ha, he, familyClass_gauss quad hb]
  have hc := quadraticGauss_conj ha.1
  rw [hg] at hc
  have hnonzero : conj (normalizedGauss b 3) ≠ 0 := (map_ne_zero _).mpr (quadraticGauss_ne_zero hb)
  have heq := mul_right_cancel₀ hnonzero (hc.trans (quadraticGauss_conj hb.1).symm)
  exact congrArg (· ^ 3) ((starRingEnd ℂ).injective heq)

end Masullo.QRH.MeanSquare
