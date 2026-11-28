import Masullo.QRH.MeanSquare.DualTail

/-!
# Assembly of the nonzero dual frequencies

`GapEstimate` gives `DualTailEstimate rowMajorant`.

* `mainSplitTerm_eq`: a main dual term of a Möbius split `(b, e, v, m₁, m₂)` at the row `h`
  is a combination over ray characters of a row weight `splitRowWeight` and a block summand
  `blockTerm` at `ρ = (e, v, h)`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-- The row weight of `ρ = (e, v, h)` in a block with column length `X`. -/
def splitRowWeight (ξ η : RayCharacter) (Y X : ℝ) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) : ℂ :=
  (idealMoebius ρ.1 : ℂ) * idealMoebius ρ.2.1 *
    ((Y / ((absNorm ρ.1 : ℝ) * absNorm ρ.2.1 * X) : ℝ) : ℂ) *
    (gaussCoefficient ρ.2.1 * conj (gaussCoefficient ρ.2.1) *
      ξ (Ideal.Quotient.mk _ (generator ρ.2.1)) *
      conj (η (Ideal.Quotient.mk _ (generator ρ.2.1))) *
      (sextic ρ.2.1 ρ.2.2 * conj (sextic ρ.2.1 ρ.2.2)))

/-- The kernel shift `½ log (Y N h / (N e N v² X²))` of `ρ = (e, v, h)`. -/
def rowShift (Y X : ℝ) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) : ℝ :=
  Real.log (Y * elementNorm ρ.2.2 / ((absNorm ρ.1 : ℝ) * (absNorm ρ.2.1 : ℝ) ^ 2 * X ^ 2)) / 2

/-- The summand of a block in `exists_block_le`, at the shift `rowShift`. -/
def blockTerm (P : SchwartzMap ℝ ℂ) (χ W : ℝ → ℂ) (ξ η : RayCharacter) (b : Ideal 𝓔)
    (Y X F : ℝ) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) (m₁ m₂ : Ideal 𝓔) : ℂ :=
  blockCoefficient ξ b ρ m₁ * conj (blockCoefficient η b ρ m₂) *
    (conj (W (absNorm (ρ.1 * ρ.2.1) / F * (absNorm m₁ / X))) *
      W (absNorm (ρ.1 * ρ.2.1) / F * (absNorm m₂ / X)) *
      cutDualKernel P χ (rowShift Y X ρ) (Real.log (absNorm m₁ / X) + Real.log (absNorm m₂ / X)))

lemma natCast_absNorm_pos {I : Ideal 𝓔} (hI : I ≠ ⊥) : (0 : ℝ) < absNorm I := by
  exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hI)

/-- A main dual term of the Möbius split `(b, e, v, m₁, m₂)` at the row `h`, as a combination
of row weights and block summands at `ρ = (e, v, h)`, for `X F = D' / N b` and
`W(x / D) = W'(x / D')`, wherever the cut `χ` is `e^{-s/2}`. -/
theorem mainSplitTerm_eq (hres : ResidueMultiplicative)
    (hmul : ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      gaussCoefficient (b * c) = gaussCoefficient b * gaussCoefficient c *
        sextic c (generator b) ^ 4)
    {A : Q₇₂ → Q₇₂ → ℂ} {α : RayCharacter → RayCharacter → ℂ}
    (hα : ∀ x y : Q₇₂, IsUnit x → IsUnit y → A x y = ∑ ξ, ∑ η, α ξ η * ξ x * conj (η y))
    (P : SchwartzMap ℝ ℂ) {χ W W' : ℝ → ℂ} {D D' Y X F : ℝ} {b e v m₁ m₂ : Ideal 𝓔} {h : 𝓔}
    (hg : Starred (b * e)) (hz₂ : Starred (v * m₁)) (hz₁ : Starred (v * m₂))
    (hco : IsCoprime (b * e) (v * m₁ * (v * m₂))) (hh : h ≠ 0) (hY : 0 < Y) (hX : 0 < X)
    (hF : 0 < F) (hXF : X * F = D' / absNorm b) (hW : ∀ x, W (x / D) = W' (x / D'))
    (hχ : conj (W' (absNorm (e * v) / F * (absNorm m₁ / X))) *
        W' (absNorm (e * v) / F * (absNorm m₂ / X)) ≠ 0 →
      χ (Real.log (absNorm m₁ / X) + Real.log (absNorm m₂ / X)) =
        (Real.exp (-((Real.log (absNorm m₁ / X) + Real.log (absNorm m₂ / X)) / 2)) : ℂ)) :
    (idealMoebius v : ℂ) * (splitWeight A W D Y (b * e, v * m₂, v * m₁) *
      ((idealMoebius e : ℂ) * pairCharacter (v * m₁) (v * m₂) (generator e) /
        (absNorm e : ℂ) * (conj (pairCharacter (v * m₁) (v * m₂) h) * gaoZhaoTransform P
          (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂)))))))) =
      ∑ ξ, ∑ η, α ξ η * splitRowWeight ξ η Y X (e, v, h) *
        blockTerm P χ W' ξ η b Y X F (e, v, h) m₁ m₂ := by
  classical
  have hb : Starred b := hg.of_mul_left
  have he : AwayFromSix e := hg.of_mul_right.1
  have hv : Starred v := hz₂.of_mul_left
  have hm₁ : Starred m₁ := hz₂.of_mul_right
  have hm₂ : Starred m₂ := hz₁.of_mul_right
  have hvm₁ : IsCoprime v m₁ := isCoprime_of_squarefree_mul hz₂.2
  have hvm₂ : IsCoprime v m₂ := isCoprime_of_squarefree_mul hz₁.2
  have hce : IsCoprime e (v * m₁ * (v * m₂)) := hco.of_mul_left_right
  have hev : IsCoprime e v := hce.of_mul_right_left.of_mul_right_left
  have hem₁ : IsCoprime e m₁ := hce.of_mul_right_left.of_mul_right_right
  have hem₂ : IsCoprime e m₂ := hce.of_mul_right_right.of_mul_right_right
  have hbm₁ : IsCoprime m₁ b := hco.of_mul_left_left.of_mul_right_left.of_mul_right_right.symm
  have hbm₂ : IsCoprime m₂ b := hco.of_mul_left_left.of_mul_right_right.of_mul_right_right.symm
  have hNb := natCast_absNorm_pos hb.1.1
  have hNe := natCast_absNorm_pos he.1
  have hNv := natCast_absNorm_pos hv.1.1
  have hN₁ := natCast_absNorm_pos hm₁.1.1
  have hN₂ := natCast_absNorm_pos hm₂.1.1
  have hNh : (0 : ℝ) < elementNorm h := by
    exact_mod_cast Nat.pos_of_ne_zero
      (absNorm_eq_zero_iff.not.mpr (span_singleton_eq_bot.not.mpr hh))
  have hD' : D' = X * F * absNorm b := by rw [hXF]; field_simp
  have hWm : ∀ m : Ideal 𝓔, W (absNorm (b * e * (v * m)) / D) =
      W' (absNorm (e * v) / F * (absNorm m / X)) := fun m => by
    rw [hW, hD']
    congr 1
    simp only [map_mul, Nat.cast_mul]
    field_simp
  set x₁ := (absNorm m₁ : ℝ) / X
  set x₂ := (absNorm m₂ : ℝ) / X
  have hx₁ : 0 < x₁ := div_pos hN₁ hX
  have hx₂ : 0 < x₂ := div_pos hN₂ hX
  set q := Y * elementNorm h / ((absNorm e : ℝ) * (absNorm v : ℝ) ^ 2 * X ^ 2)
  have hq : 0 < q := by positivity
  have hN : (absNorm (v * m₁ * (v * m₂)) : ℝ) = ((absNorm v : ℝ) * X) ^ 2 * (x₁ * x₂) := by
    simp only [map_mul, Nat.cast_mul, x₁, x₂]
    field_simp
  have hk : ((Y : ℂ) / (Real.sqrt (absNorm (v * m₁ * (v * m₂))) : ℂ)) * gaoZhaoTransform P
      (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂))))) =
      ((Y / ((absNorm v : ℝ) * X) : ℝ) : ℂ) *
        (((Real.sqrt (x₁ * x₂) : ℝ) : ℂ)⁻¹ * gaoZhaoTransform P (Real.sqrt (q / (x₁ * x₂)))) := by
    have harg : Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂))) =
        q / (x₁ * x₂) := by
      rw [hN]
      simp only [q]
      field_simp
    rw [harg, hN, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    push_cast
    field_simp
  set w₁ := W' (absNorm (e * v) / F * x₁)
  set w₂ := W' (absNorm (e * v) / F * x₂)
  have hk2 : conj w₁ * w₂ * (((Y : ℂ) / (Real.sqrt (absNorm (v * m₁ * (v * m₂))) : ℂ)) *
      gaoZhaoTransform P
        (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂)))))) =
      conj w₁ * w₂ * (((Y / ((absNorm v : ℝ) * X) : ℝ) : ℂ) *
        cutDualKernel P χ (rowShift Y X (e, v, h)) (Real.log x₁ + Real.log x₂)) := by
    by_cases hw : conj w₁ * w₂ = 0
    · rw [hw, zero_mul, zero_mul]
    rw [hk, gaoZhaoTransform_eq_cutDualKernel P hq hx₁ hx₂ (hχ hw)]
    rfl
  have hm := mainSummand_eq hres hmul hα he hv hm₁ hm₂ hvm₁ hvm₂ hev hem₁ hem₂ h
  calc _ = (idealMoebius v : ℂ) * idealMoebius e / (absNorm e : ℂ) *
        (gaussCoefficient (v * m₁) * conj (gaussCoefficient (v * m₂)) *
          A (Ideal.Quotient.mk _ (generator (v * m₁)))
            (Ideal.Quotient.mk _ (generator (v * m₂))) *
          (pairCharacter (v * m₁) (v * m₂) (generator e) *
            conj (pairCharacter (v * m₁) (v * m₂) h))) *
        (conj w₁ * w₂ * (((Y : ℂ) / (Real.sqrt (absNorm (v * m₁ * (v * m₂))) : ℂ)) *
          gaoZhaoTransform P (Real.sqrt (Y * elementNorm h /
            ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂))))))) := by
        simp only [splitWeight, hWm, w₁, w₂, x₁, x₂]
        ring
    _ = _ := by
        rw [hm, hk2]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
        simp only [splitRowWeight, blockTerm, blockCoefficient, hbm₁, hbm₂, ite_true, w₁, w₂,
          x₁, x₂]
        push_cast
        ring

end Masullo.QRH.MeanSquare
