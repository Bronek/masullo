import Masullo.QRH.MeanSquare.TransferTail

/-!
# The bound of a Poisson pass

* `sum_passDual_tail_eq_rows`: the nonzero dual frequencies of a pass as a sum over dual rows
  `(r, h)` and ray characters of bilinear forms in two dual columns.
* `norm_passCoefficient_le`: the coefficient of a dual row is at most the row weight times the
  size of the ray-character expansion coefficient.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-- The coefficient of the dual row `(r, h)` for the ray characters `ξ, η`. -/
def passCoefficient (κ κ' φ : Ideal 𝓔 → ℂ) (p : ℕ) (α : RayCharacter → RayCharacter → ℂ)
    (ℓ Y : ℝ) (r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) (h : 𝓔) (ξ η : RayCharacter) : ℂ :=
  (idealMoebius r.2.2 : ℂ) * ((idealMoebius r.2.1 : ℂ) / (absNorm r.2.1 : ℂ) * α ξ η *
    passRowFactor κ κ' φ p ξ η (r.1 * r.2.1) r.2.1 r.2.2 h *
      ((Y * absNorm (r.1 * r.2.1) / ℓ : ℝ) : ℂ))

/-- The bilinear form of the dual row `(r, h)` in the dual columns of `ξ` and `η`. -/
def passForm (κ' φ : Ideal 𝓔 → ℂ) (p p' : ℕ) (P : SchwartzMap ℝ ℂ) (V : ℝ → ℂ) (ℓ Y X : ℝ)
    (r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) (h : 𝓔) (ξ η : RayCharacter) : ℂ :=
  ∑ x₁ ∈ passCols X r, ∑ x₂ ∈ passCols X r,
    dualCoeff κ' φ p p' ξ (r.1 * r.2.1) r.2.1 r.2.2 h x₁ *
      conj (dualCoeff κ' φ p p' η (r.1 * r.2.1) r.2.1 r.2.2 h x₂) *
      sepKernel P V (absNorm (r.1 * r.2.1 * (r.2.2 * x₁)) / ℓ)
        (absNorm (r.1 * r.2.1 * (r.2.2 * x₂)) / ℓ) (passScale Y ℓ (r.1 * r.2.1) r.2.1 h)

lemma sum_sum_sum_comm {α β γ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ)
    (f : α → β → γ → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c := by
  calc _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The nonzero dual frequencies of a pass as a sum over the dual rows `(r, h)` and pairs of ray
characters. -/
theorem sum_passDual_tail_eq_rows (hres : ResidueMultiplicative)
    {κ κ' φ : Ideal 𝓔 → ℂ} {p p' : ℕ} (hκ' : TwistMul κ' p') (hφ : TwistMul φ 0)
    {Corr : Q₇₂ → Q₇₂ → ℂ} {α : RayCharacter → RayCharacter → ℂ}
    (hα : ∀ x y : Q₇₂, IsUnit x → IsUnit y → Corr x y = ∑ ξ, ∑ η, α ξ η * ξ x * conj (η y))
    {P : SchwartzMap ℝ ℂ} (hP : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0) {V : ℝ → ℂ} {hi : ℝ}
    (hV : ∀ x, V x ≠ 0 → x ≤ hi) {ℓ Y X : ℝ} (hℓ : 0 < ℓ) (hY : 0 < Y) (hX : 0 ≤ X) :
    ∑ t ∈ passSplits X, passDual κ κ' φ p Corr V ℓ Y t * dualExclusionTail P Y t.2.2 t.2.1 t.1 =
      ∑ r ∈ passRows X, ∑ h ∈ elementRows (passCap hi Y ℓ (r.1 * r.2.1) r.2.1), ∑ ξ, ∑ η,
        passCoefficient κ κ' φ p α ℓ Y r h ξ η *
          passForm κ' φ p p' P V ℓ Y X r h ξ η := by
  classical
  rw [sum_passDual_tail_eq κ κ' φ p Corr V P ℓ Y hX]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := (Finset.mem_filter.mp (by unfold passRows at hr; exact hr)).2
  have hcol : ∀ x ∈ passCols X r, Starred x ∧ IsCoprime r.2.2 x := fun x hx => by
    unfold passCols at hx
    obtain ⟨-, hs, hco, -⟩ := Finset.mem_filter.mp hx
    exact ⟨hs, hco.of_mul_left_right⟩
  have hg : r.1 * r.2.1 ≠ ⊥ := hr'.1.1.1
  have he : r.2.1 ≠ ⊥ := right_ne_zero_of_mul hg
  have inner : ∀ x₁ ∈ passCols X r, ∀ x₂ ∈ passCols X r,
      (idealMoebius r.2.2 : ℂ) *
        (passDual κ κ' φ p Corr V ℓ Y (r.1 * r.2.1, r.2.2 * x₁, r.2.2 * x₂) *
          tailFrequencies P Y (r.2.2 * x₁) (r.2.2 * x₂) r.2.1) =
      ∑ h ∈ elementRows (passCap hi Y ℓ (r.1 * r.2.1) r.2.1), ∑ ξ, ∑ η,
        passCoefficient κ κ' φ p α ℓ Y r h ξ η *
          (dualCoeff κ' φ p p' ξ (r.1 * r.2.1) r.2.1 r.2.2 h x₁ *
            conj (dualCoeff κ' φ p p' η (r.1 * r.2.1) r.2.1 r.2.2 h x₂) *
            sepKernel P V (absNorm (r.1 * r.2.1 * (r.2.2 * x₁)) / ℓ)
              (absNorm (r.1 * r.2.1 * (r.2.2 * x₂)) / ℓ)
              (passScale Y ℓ (r.1 * r.2.1) r.2.1 h)) := by
    intro x₁ hx₁ x₂ hx₂
    rw [passDual_mul_tailFrequencies_eq hres hκ' hφ hα hP hV hℓ hY hg he hr'.2.1
      (hcol x₁ hx₁).1 (hcol x₂ hx₂).1 (hcol x₁ hx₁).2 (hcol x₂ hx₂).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    simp only [passCoefficient]
    ring
  rw [Finset.sum_congr rfl fun x₁ hx₁ => Finset.sum_congr rfl fun x₂ hx₂ => inner x₁ hx₁ x₂ hx₂,
    sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun η _ => ?_
  simp only [passForm, Finset.mul_sum]

lemma norm_rayCharacter_le (ξ : RayCharacter) (x : Q₇₂) : ‖ξ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · let := Ring.HasFiniteQuotients.finiteQuotient (I := span {(72 : 𝓔)}) (by simp)
    have hpow := pow_card_eq_one' (x := hx.unit)
    have hχ := congrArg (fun u : Q₇₂ˣ => ξ (u : Q₇₂)) hpow
    simp only [Units.val_pow_eq_pow_val, hx.unit_spec, map_pow, Units.val_one, map_one] at hχ
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, Nat.card_pos, hχ⟩).norm_eq_one.le
  · simp [ξ.map_nonunit hx]

private lemma mul_le_one_of_le {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 := by
  nlinarith

lemma norm_mul_conj_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * conj b‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg a, norm_nonneg b]

lemma norm_passRowFactor_le {κ κ' φ : Ideal 𝓔 → ℂ} (hκ : ∀ n, ‖κ n‖ ≤ 1)
    (hκ' : ∀ n, ‖κ' n‖ ≤ 1) (hφ : ∀ n, ‖φ n‖ ≤ 1) (p : ℕ) (ξ η : RayCharacter)
    (g e v : Ideal 𝓔) (h : 𝓔) : ‖passRowFactor κ κ' φ p ξ η g e v h‖ ≤ 1 := by
  have hs : ∀ n y, ‖sextic n y ^ p‖ ≤ 1 := fun n y => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_sextic_le_one _ _)
  unfold passRowFactor
  refine (norm_mul_le _ _).trans (mul_le_one_of_le ?_ (norm_nonneg _)
    (norm_mul_conj_le_one (norm_sextic_le_one _ _) (norm_sextic_le_one _ _)))
  refine (norm_mul_le _ _).trans (mul_le_one_of_le ?_ (norm_nonneg _)
    (norm_mul_conj_le_one (norm_sextic_le_one _ _) (norm_sextic_le_one _ _)))
  refine (norm_mul_le _ _).trans (mul_le_one_of_le ?_ (norm_nonneg _)
    (norm_mul_conj_le_one (hs _ _) (hs _ _)))
  refine (norm_mul_le _ _).trans (mul_le_one_of_le ?_ (norm_nonneg _)
    (norm_mul_conj_le_one (norm_rayCharacter_le _ _) (norm_rayCharacter_le _ _)))
  refine (norm_mul_le _ _).trans (mul_le_one_of_le ?_ (norm_nonneg _)
    (norm_mul_conj_le_one (hφ _) (hφ _)))
  refine (norm_mul_le _ _).trans (mul_le_one_of_le ?_ (norm_nonneg _)
    (norm_mul_conj_le_one (hκ' _) (hκ' _)))
  refine (norm_mul_le _ _).trans (mul_le_one_of_le ?_ (norm_nonneg _)
    (norm_mul_conj_le_one (hφ _) (hφ _)))
  exact norm_mul_conj_le_one (hκ _) (hκ _)

lemma norm_passCoefficient_le {κ κ' φ : Ideal 𝓔 → ℂ} (hκ : ∀ n, ‖κ n‖ ≤ 1)
    (hκ' : ∀ n, ‖κ' n‖ ≤ 1) (hφ : ∀ n, ‖φ n‖ ≤ 1) (p : ℕ)
    (α : RayCharacter → RayCharacter → ℂ) {ℓ Y : ℝ} (hℓ : 0 < ℓ) (hY : 0 < Y)
    (r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) (h : 𝓔) (ξ η : RayCharacter) :
    ‖passCoefficient κ κ' φ p α ℓ Y r h ξ η‖ ≤
      ‖α ξ η‖ * (Y * absNorm (r.1 * r.2.1) / (ℓ * absNorm r.2.1)) := by
  have hR := norm_passRowFactor_le hκ hκ' hφ p ξ η (r.1 * r.2.1) r.2.1 r.2.2 h
  have hμ : ∀ n : Ideal 𝓔, ‖(idealMoebius n : ℂ)‖ ≤ 1 := norm_idealMoebius_le
  have hW : ‖(((Y * absNorm (r.1 * r.2.1) / ℓ : ℝ)) : ℂ)‖ = Y * absNorm (r.1 * r.2.1) / ℓ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have he : ‖(idealMoebius r.2.1 : ℂ) / (absNorm r.2.1 : ℂ)‖ ≤ (absNorm r.2.1 : ℝ)⁻¹ := by
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (hμ _)
  unfold passCoefficient
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hW]
  calc _ ≤ 1 * ((absNorm r.2.1 : ℝ)⁻¹ * ‖α ξ η‖ * 1 * (Y * absNorm (r.1 * r.2.1) / ℓ)) := by
        gcongr
        exact hμ _
    _ = _ := by
        rcases eq_or_ne (absNorm r.2.1 : ℝ) 0 with h0 | h0
        · simp [h0]
        · field_simp

end Masullo.QRH.MeanSquare
