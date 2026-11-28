import Masullo.QRH.MeanSquare.GaussCube
import Masullo.QRH.MeanSquare.Theta

/-! # The primary cube coefficients in the reflected sum -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The two balanced ternary digits in the cubic supplementary laws parametrize
the primary classes modulo nine. -/
theorem eisPrimary.exists_digits_mod_nine {x : 𝓔} (hx : eisPrimary x) :
    ∃ h ∈ Set.Icc (-1 : ℤ) 1, ∃ j ∈ Set.Icc (-1 : ℤ) 1,
      (9 : 𝓔) ∣ x - (1 + h * eisLambda ^ 2 + j * eisLambda ^ 3) := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨a, b, rfl⟩ := eisInteger_coordinates y
  let j := (b + 1) % 3 - 1
  let h := (-a - j + 1) % 3 - 1
  have hj : j ∈ Set.Icc (-1 : ℤ) 1 := by change -1 ≤ (b + 1) % 3 - 1 ∧ _; omega
  have hh : h ∈ Set.Icc (-1 : ℤ) 1 := by change -1 ≤ (-a-j+1) % 3 - 1 ∧ _; omega
  have ha : 3 * ((a + h + j) / 3) = a + h + j := by dsimp [h]; omega
  have hb : 3 * ((b + 2 * j) / 3) = b + 2 * j := by dsimp [j]; omega
  refine ⟨h, hh, j, hj, (↑((a + h + j) / 3) : 𝓔) + ↑((b + 2 * j) / 3) * eisOmega, ?_⟩
  have ha' := congrArg (fun z : ℤ => (z : 𝓔)) ha
  have hb' := congrArg (fun z : ℤ => (z : 𝓔)) hb
  push_cast at ha' hb'
  rw [pow_succ eisLambda 2, eisLambda_sq, eisLambda]
  linear_combination hy - 3 * ha' - 3 * eisOmega * hb'

/-- At primary denominators the two ramified cubic symbols descend to the
same modulus nine, including composite denominators. -/
theorem cubic_supplements_congr (hR : DunnRadziwillReciprocity) {x y : 𝓔}
    (hx : eisPrimary x) (hxy : (9 : 𝓔) ∣ y - x) :
    cubicSymbol eisLambda x = cubicSymbol eisLambda y ∧
      cubicSymbol eisOmega x = cubicSymbol eisOmega y := by
  obtain ⟨h, hh, j, hj, hx'⟩ := hx.exists_digits_mod_nine
  have hy := dvd_add hxy hx'
  rw [sub_add_sub_cancel] at hy
  have h₁ := hR.2 x h j hh hj hx'
  have h₂ := hR.2 y h j hh hj hy
  exact ⟨eisEmbedding_injective (h₁.2.trans h₂.2.symm),
    eisEmbedding_injective (h₁.1.trans h₂.1.symm)⟩

theorem twist_mul (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) {a b : Ideal 𝓔}
    (ha : AwayFromSix a) (hb : AwayFromSix b) :
    twist ξ k f (a * b) = twist ξ k f a * twist ξ k f b := by
  classical
  simp only [twist, ite_eq_left (ha.mul hb), ite_eq_left ha, ite_eq_left hb,
    generator_mul ha.coprime_three hb.coprime_three, sextic, powerResidueSymbol_mul_right, map_mul]
  ring

/-- Inserting a cube in the denominator leaves the cubic correction unchanged. -/
theorem lambda_cubic_mul_cube {n b : Ideal 𝓔} (hn : AwayFromSix n) (hb : AwayFromSix b) :
    eisEmbedding (powerResidueSymbol 3 eisLambda (n * b ^ 3)) = sextic n eisLambda ^ 2 := by
  have hb₆ : sextic b eisLambda ^ 6 = 1 := by
    simp only [sextic, ← map_pow, powerResidueSymbol_six_pow_six hb.1 hb.2,
      ite_eq_left (coprime_span_lambda hb), map_one]
  simp only [pow_three, powerResidueSymbol_mul_right, map_mul,
    ← powerResidueSymbol_six_sq hn.2, ← powerResidueSymbol_six_sq hb.2, map_pow]
  change sextic n eisLambda ^ 2 * (sextic b eisLambda ^ 2 * (sextic b eisLambda ^ 2 *
    sextic b eisLambda ^ 2)) = _
  rw [show sextic b eisLambda ^ 2 * (sextic b eisLambda ^ 2 * sextic b eisLambda ^ 2) =
      sextic b eisLambda ^ 6 by ring, hb₆, mul_one]

/-- At a primary frequency `nb³`, the corrected theta coefficient supplies both
the squarefree Gauss coefficient and the two twists of the cube completion. -/
theorem PattersonCoefficients.twisted_primary_cube {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ)
    (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) {n b : Ideal 𝓔} (hn : Starred n)
    (hb : AwayFromSix b) :
    let a := n * b ^ 3
    conj (angularFactor a) * (conj (τ (eisEmbedding (generator a))) / 27) *
        eisEmbedding (powerResidueSymbol 3 eisLambda a) * twist ξ k f a =
      ‖eisEmbedding (generator b)‖ * gaussCoefficient n * twist ξ k f n *
        (conj (angularFactor b) * twist ξ k f b) ^ 3 := by
  dsimp only
  have hsf : Squarefree (generator n) :=
    squarefree_span_singleton.mp (by simpa only [span_generator] using hn.2)
  have ht := hτ.normalized_primary_cube (eisPrimary_generator hn.1.coprime_three)
    (eisPrimary_generator hb.coprime_three) hsf
  have hb₂ := hb.mul hb
  have hb₃ := hb.mul hb₂
  rw [lambda_cubic_mul_cube hn.1 hb, pow_three,
    generator_mul hn.1.coprime_three hb₃.coprime_three,
    generator_mul hb.coprime_three hb₂.coprime_three,
    generator_mul hb.coprime_three hb.coprime_three]
  simp only [map_mul, ← pow_three, map_pow]
  rw [pow_three b, ht, norm_div, gaussCoefficient_eq_pattersonGauss hn.1,
    angularFactor_mul hn.1 hb₃, angularFactor_mul hb hb₂, angularFactor_mul hb hb,
    twist_mul ξ k f hn.1 hb₃, twist_mul ξ k f hb hb₂, twist_mul ξ k f hb hb]
  simp only [map_mul, Complex.ofReal_div]
  ring

end Masullo.QRH.MeanSquare
