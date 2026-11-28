import Masullo.QRH.MeanSquare.Sieve
import Masullo.QRH.MeanSquare.Residue
import Masullo.QRH.MeanSquare.Primary

/-! # Quadratic residue characters on elements and principal ideals -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The quadratic character on elements with denominator `n`. At the unit ideal it
has value one on every element. -/
def quadraticResidue {n : Ideal 𝓔} (hn : AwayFromSix n) : 𝓔 →* ℂ :=
  (sexticChar hn ^ 3).toMonoidHom.comp (Ideal.Quotient.mk n).toMonoidHom

lemma quadraticResidue_apply {n : Ideal 𝓔} (hn : AwayFromSix n) (x : 𝓔) :
    quadraticResidue hn x = sextic n x ^ 3 := by
  simp [quadraticResidue, MulChar.pow_apply' _ (by decide : 3 ≠ 0)]

lemma quadraticResidue_den_mul {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c) (x : 𝓔) :
    quadraticResidue (hb.mul hc) x = quadraticResidue hb x * quadraticResidue hc x := by
  simp only [quadraticResidue_apply, sextic, powerResidueSymbol_mul_right, map_mul, mul_pow]

lemma quadraticResidue_congr {n : Ideal 𝓔} (hn : AwayFromSix n) {x y : 𝓔} (h : x - y ∈ n) :
    quadraticResidue hn x = quadraticResidue hn y :=
  DFunLike.congr_arg (sexticChar hn ^ 3) (Ideal.Quotient.eq.mpr h)

lemma quadraticResidue_ne_zero {n : Ideal 𝓔} (hn : AwayFromSix n) {x : 𝓔} :
    quadraticResidue hn x ≠ 0 ↔ IsCoprime n (span {x}) := by
  rw [← isUnit_mk_iff_coprime_span]
  change (sexticChar hn ^ 3) (Ideal.Quotient.mk n x) ≠ 0 ↔ _
  constructor
  · exact fun h => by_contra fun hu => h (MulChar.map_nonunit _ hu)
  · exact fun hu => (hu.map (sexticChar hn ^ 3)).ne_zero

lemma quadraticResidue_sq {n : Ideal 𝓔} (hn : AwayFromSix n) {x : 𝓔}
    (hx : IsCoprime n (span {x})) : quadraticResidue hn x ^ 2 = 1 := by
  rw [quadraticResidue_apply, ← pow_mul, sextic, ← map_pow]
  simp only [show 3 * 2 = 6 by decide, powerResidueSymbol_six_pow_six hn.1 hn.2,
    ite_eq_left hx, map_one]

/-- A multiplicative function trivial on units descends to principal ideals. Its value
at the zero ideal is set to zero, including for the trivial character. -/
def idealCharacterOfElement (F : 𝓔 →* ℂ) (hF : ∀ u : 𝓔ˣ, F u = 1) : Ideal 𝓔 →*₀ ℂ where
  toFun a := if a = 0 then 0 else F (generator a)
  map_zero' := by simp
  map_one' := by rw [ite_eq_right one_ne_zero, generator_one, map_one]
  map_mul' a b := by
    classical
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [ite_eq_right ha, ite_eq_right hb, ite_eq_right (mul_ne_zero ha hb)]
    have h : Associated (generator a * generator b) (generator (a * b)) := by
      apply span_singleton_eq_span_singleton.mp
      rw [← span_singleton_mul_span_singleton, span_generator, span_generator, span_generator]
    obtain ⟨u, hu⟩ := h
    rw [← hu, map_mul, hF, mul_one, map_mul]

lemma idealCharacterOfElement_apply (F : 𝓔 →* ℂ) (hF : ∀ u : 𝓔ˣ, F u = 1)
    {a : Ideal 𝓔} (ha : a ≠ 0) : idealCharacterOfElement F hF a = F (generator a) := by
  exact ite_eq_right ha

lemma idealCharacterOfElement_span (F : 𝓔 →* ℂ) (hF : ∀ u : 𝓔ˣ, F u = 1) {x : 𝓔} (hx : x ≠ 0) :
    idealCharacterOfElement F hF (span {x}) = F x := by
  rw [idealCharacterOfElement_apply _ _ (by simpa using hx)]
  obtain ⟨u, hu⟩ := span_singleton_eq_span_singleton.mp (span_generator (span {x}))
  calc
    F (generator (span {x})) = F (generator (span {x}) * (u : 𝓔)) := by rw [map_mul, hF, mul_one]
    _ = _ := congrArg F hu

lemma isRayCharacter_of_element {f : Ideal 𝓔} (hf : f ≠ 0) (F : 𝓔 →* ℂ)
    (hF : ∀ u : 𝓔ˣ, F u = 1) (hs : ∀ x, F x ≠ 0 ↔ IsCoprime f (span {x}))
    (hr : ∀ x, x - 1 ∈ f → F x = 1) : IsRayCharacter f (idealCharacterOfElement F hF) := by
  refine ⟨hf, ?_, fun x hx h => (idealCharacterOfElement_span F hF hx).trans (hr x h)⟩
  intro a
  by_cases ha : a = 0
  · subst a
    simp only [map_zero, ne_eq, not_true_eq_false, false_and]
  rw [idealCharacterOfElement_apply F hF ha, hs, span_generator, isCoprime_comm]
  exact (and_iff_right ha).symm

end Masullo.QRH.MeanSquare
