import Mathlib

/-! # Eisenstein integers and residue symbols for the mean square -/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare

local notation "K" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K

private theorem cyclotomicThree : IsCyclotomicExtension {3} ℚ K := by
  let : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

attribute [local instance] cyclotomicThree

/-- The integral primitive cube root used in the basis `1, ω`. -/
def eisOmega : 𝓔 := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

/-- The generator `√(-3) = 1 + 2ω` of the different. -/
def eisLambda : 𝓔 := 1 + 2 * eisOmega

/-- Primary elements are congruent to `1` modulo `3`. -/
def eisPrimary (a : 𝓔) : Prop := 3 ∣ a - 1

/-- The embedding that sends `ω` to `exp(2πi/3)`. -/
def eisFieldEmbedding : K →ₐ[ℚ] ℂ :=
  ((IsCyclotomicExtension.zeta_spec 3 ℚ K).embeddingsEquivPrimitiveRoots ℂ
    (Polynomial.cyclotomic.irreducible_rat (by decide))).symm
    ⟨_, (mem_primitiveRoots (by decide : 0 < 3)).2 (Complex.isPrimitiveRoot_exp 3 (by decide))⟩

/-- The restriction of `eisFieldEmbedding` to the ring of integers. -/
def eisEmbedding : 𝓔 →+* ℂ := eisFieldEmbedding.toRingHom.comp (algebraMap 𝓔 K)

lemma eisEmbedding_omega : eisEmbedding eisOmega = Complex.exp (2 * Real.pi * Complex.I / 3) := by
  let e := (IsCyclotomicExtension.zeta_spec 3 ℚ K).embeddingsEquivPrimitiveRoots ℂ
    (Polynomial.cyclotomic.irreducible_rat (by decide))
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The additive character `exp(2πi Tr(z/√(-3)))` in the fixed embedding. -/
def differentCharacter (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (2 * z.im / Real.sqrt 3 : ℝ))

/-- At a good prime `P`, lift the residue `a ^ ((NP - 1) / d)` to a `d`th root of unity.
The value is zero at a multiple of `P`. On the good primes used here the lift is unique. -/
def primePowerResidueSymbol (d : ℕ) (a : 𝓔) (P : Ideal 𝓔) : 𝓔 := by
  classical
  exact if a ∈ P then 0 else
    if h : ∃ u : 𝓔, u ^ d = 1 ∧ a ^ ((absNorm P - 1) / d) - u ∈ P then h.choose else 0

/-- Extend the prime symbol multiplicatively in the denominator, counting each prime factor
with its multiplicity. For the unit ideal this is the empty product. -/
def powerResidueSymbol (d : ℕ) (a : 𝓔) (I : Ideal 𝓔) : 𝓔 :=
  if I = ⊥ then 0 else ((normalizedFactors I).map (primePowerResidueSymbol d a)).prod

/-- The Eisenstein cubic residue symbol `(a/b)₃`. -/
def cubicSymbol (a b : 𝓔) : 𝓔 := powerResidueSymbol 3 a (span {b})

@[simp] theorem powerResidueSymbol_top (d : ℕ) (a : 𝓔) : powerResidueSymbol d a ⊤ = 1 := by
  rw [powerResidueSymbol, ite_eq_right top_ne_bot, ← Ideal.one_eq_top, normalizedFactors_one,
    Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem cubicSymbol_one (a : 𝓔) : cubicSymbol a 1 = 1 := by simp [cubicSymbol]

open Classical in
/-- Unnormalized cubic Gauss sum with the trace character `exp(2πi Tr(a x / c))`.
For `c = 1` take `0` as the representative of its single residue class. -/
def pattersonGauss (a c : 𝓔) : ℂ :=
  if c = 1 then 1 else ∑ᶠ x : 𝓔 ⧸ span {c}, eisEmbedding (cubicSymbol (Quotient.out x) c) *
    Complex.exp (2 * Real.pi * Complex.I *
      (2 * (eisEmbedding a * eisEmbedding (Quotient.out x) / eisEmbedding c).re : ℝ))

@[simp] theorem pattersonGauss_one (a : 𝓔) : pattersonGauss a 1 = 1 := by simp [pattersonGauss]

end Masullo.QRH.MeanSquare
