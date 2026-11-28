import Masullo.QRH.MeanSquare.CubeInversion
import Masullo.QRH.MeanSquare.TransferTail

/-!
# The bound of a Poisson pass

* `sum_passDual_tail_eq_rows`: the nonzero dual frequencies of a pass as a sum over dual rows
  `(r, h)` and ray characters of bilinear forms in two dual columns.
* `norm_passCoefficient_le`: the coefficient of a dual row is at most the row weight times the
  size of the ray-character expansion coefficient.
* `exists_passBound`: a weighted family of `P`-weighted mean squares of pass columns is bounded
  by its zero frequencies and by the mean squares of the dual columns, uniformly over tests.
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

/-- Joint separation of weighted bilinear forms whose columns depend on the row. -/
theorem exists_transferSeparated_weighted (I : TestInterval) (j : ℕ) (P : SchwartzMap ℝ ℂ)
    (hP : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0) : ∃ C ≥ (0 : ℝ),
    ∀ {R N : Type} (rows : Finset R) (cols : R → Finset N) (ω : R → ℝ) (d₁ d₂ : R → N → ℂ)
      (x : R → N → ℝ) (W : ℝ → ℂ) (A : R → ℝ) {M₁ M₂ : ℝ}, 0 ≤ M₁ → 0 ≤ M₂ →
      UnitTest I j W → (∀ ρ ∈ rows, 0 ≤ ω ρ ∧ 0 < A ρ) →
      (∀ U, UnitTest I j U →
        ∑ ρ ∈ rows, ω ρ * ‖∑ n ∈ cols ρ, d₁ ρ n * U (x ρ n)‖ ^ 2 ≤ M₁) →
      (∀ U, UnitTest I j U →
        ∑ ρ ∈ rows, ω ρ * ‖∑ n ∈ cols ρ, d₂ ρ n * U (x ρ n)‖ ^ 2 ≤ M₂) →
      ∑ ρ ∈ rows, ω ρ * ‖∑ n₁ ∈ cols ρ, ∑ n₂ ∈ cols ρ, d₁ ρ n₁ * conj (d₂ ρ n₂) *
        (W (x ρ n₁) * conj (W (x ρ n₂)) * ((((√(x ρ n₁ * x ρ n₂))⁻¹ : ℝ) : ℂ) *
          gaoZhaoTransform P (√(A ρ / (x ρ n₁ * x ρ n₂)))))‖ ≤ C * (M₁ + M₂) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_transferSeparated_le₂ I j P hP
  refine ⟨C, hC0, ?_⟩
  intro R N rows cols ω d₁ d₂ x W A M₁ M₂ hM₁ hM₂ hW hρ h₁ h₂
  set T := rows.biUnion cols
  have hred : ∀ ρ ∈ rows, ∀ f : N → ℂ,
      ∑ n ∈ T, (if n ∈ cols ρ then f n else 0) = ∑ n ∈ cols ρ, f n := fun ρ hρ' f => by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem cols hρ')]
  set c : (R → N → ℂ) → R → N → ℂ := fun d ρ n =>
    ((√(ω ρ) : ℝ) : ℂ) * (if n ∈ cols ρ then d ρ n else 0)
  have hω : ∀ ρ ∈ rows, ((√(ω ρ) : ℝ) : ℂ) * conj ((√(ω ρ) : ℝ) : ℂ) = (ω ρ : ℂ) :=
    fun ρ hρ' => by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hρ ρ hρ').1]
  have hlin : ∀ (d : R → N → ℂ) (U : ℝ → ℂ), ∀ ρ ∈ rows,
      ‖∑ n ∈ T, c d ρ n * U (x ρ n)‖ ^ 2 = ω ρ * ‖∑ n ∈ cols ρ, d ρ n * U (x ρ n)‖ ^ 2 := by
    intro d U ρ hρ'
    have : ∑ n ∈ T, c d ρ n * U (x ρ n) =
        ((√(ω ρ) : ℝ) : ℂ) * ∑ n ∈ T, (if n ∈ cols ρ then d ρ n * U (x ρ n) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [c]
      split_ifs <;> ring
    rw [this, hred ρ hρ', norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg
      (Real.sqrt_nonneg _), Real.sq_sqrt (hρ ρ hρ').1]
  have hM : ∀ (d : R → N → ℂ) {M : ℝ}, (∀ U, UnitTest I j U →
      ∑ ρ ∈ rows, ω ρ * ‖∑ n ∈ cols ρ, d ρ n * U (x ρ n)‖ ^ 2 ≤ M) →
      ∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ T, c d ρ n * U (x ρ n)‖ ^ 2 ≤ M := by
    intro d M hd U hU
    rw [Finset.sum_congr rfl fun ρ hρ' => hlin d U ρ hρ']
    exact hd U hU
  have hmain := hC rows T (c d₁) (c d₂) x W A hM₁ hM₂ hW (fun ρ hρ' => (hρ ρ hρ').2)
    (hM d₁ h₁) (hM d₂ h₂)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun ρ hρ' => ?_) hmain
  set K : N → N → ℂ := fun n₁ n₂ => W (x ρ n₁) * conj (W (x ρ n₂)) *
    ((((√(x ρ n₁ * x ρ n₂))⁻¹ : ℝ) : ℂ) * gaoZhaoTransform P (√(A ρ / (x ρ n₁ * x ρ n₂))))
  have : ∑ n₁ ∈ T, ∑ n₂ ∈ T, c d₁ ρ n₁ * conj (c d₂ ρ n₂) * K n₁ n₂ =
      (ω ρ : ℂ) * ∑ n₁ ∈ cols ρ, ∑ n₂ ∈ cols ρ, d₁ ρ n₁ * conj (d₂ ρ n₂) * K n₁ n₂ := by
    rw [Finset.mul_sum, ← hred ρ hρ']
    refine Finset.sum_congr rfl fun n₁ _ => ?_
    split_ifs with hn₁
    · rw [Finset.mul_sum, ← hred ρ hρ']
      refine Finset.sum_congr rfl fun n₂ _ => ?_
      simp only [c, hn₁, ite_true, ← hω ρ hρ']
      split_ifs <;> simp only [map_mul, map_zero] <;> ring
    · simp [c, hn₁]
  rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ ρ hρ').1]

lemma sum_sum_sum_sum_comm {α β γ δ M : Type*} [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (A : Finset α) (B : α → Finset β) (f : α → β → γ → δ → M) :
    ∑ a ∈ A, ∑ b ∈ B a, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a ∈ A, ∑ b ∈ B a, f a b c d := by
  calc _ = ∑ a ∈ A, ∑ c, ∑ d, ∑ b ∈ B a, f a b c d := Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma passRows_ne_bot {X : ℝ} {r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (hr : r ∈ passRows X) :
    r.1 * r.2.1 ≠ ⊥ ∧ r.2.1 ≠ ⊥ := by
  classical
  have hs : r.1 * r.2.1 ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using (Finset.mem_filter.mp hr).2.1.2.ne_zero
  exact ⟨hs, fun h => hs (by rw [h, mul_bot])⟩

/-- A weighted family of `P`-weighted mean squares of pass columns is bounded by its zero
frequencies and by the mean squares of the dual columns, uniformly over tests. -/
theorem exists_passBound (hres : ResidueMultiplicative) (I : TestInterval) (j : ℕ)
    {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) (hT : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0)
    (Corr : Q₇₂ → Q₇₂ → ℂ) : ∃ C ≥ (0 : ℝ),
    ∀ {Ω : Type} (O : Finset Ω) (w Y ℓ X : Ω → ℝ) {κ κ' : Ideal 𝓔 → ℂ}
      (φ : Ω → Ideal 𝓔 → ℂ) {p p' : ℕ} {V : ℝ → ℂ} {M : ℝ},
      TwistMul κ p → TwistMul κ' p' → (∀ o, TwistMul (φ o) 0) → GaussConversion κ κ' Corr →
      (∀ n, ‖κ n‖ ≤ 1) → (∀ n, ‖κ' n‖ ≤ 1) → (∀ o n, ‖φ o n‖ ≤ 1) → UnitTest I j V →
      (∀ o ∈ O, 0 ≤ w o ∧ 0 < Y o ∧ 0 < ℓ o ∧ 0 ≤ X o) → 0 ≤ M →
      (∀ U, UnitTest I j U → ∀ ξ : RayCharacter,
        ∑ o ∈ O, ∑ r ∈ passRows (X o),
          ∑ h ∈ elementRows (passCap I.hi (Y o) (ℓ o) (r.1 * r.2.1) r.2.1),
            w o * (Y o * absNorm (r.1 * r.2.1) / (ℓ o * absNorm r.2.1)) *
              ‖∑ x ∈ passCols (X o) r, dualCoeff κ' (φ o) p p' ξ (r.1 * r.2.1) r.2.1 r.2.2 h x *
                U (absNorm (r.1 * r.2.1 * (r.2.2 * x)) / ℓ o)‖ ^ 2 ≤ M) →
      ∑ o ∈ O, w o * ∑' y : 𝓔, (P (elementNorm y / Y o)).re *
          ‖passColumn κ (φ o) V (ℓ o) (X o) y‖ ^ 2 ≤
        C * ∑ o ∈ O, w o * Y o *
            ∑ g ∈ starredLe (X o), (2 : ℝ) ^ Multiset.card (normalizedFactors g) + C * M := by
  classical
  obtain ⟨α, hα⟩ := exists_rayCharacter_expansion Corr
  obtain ⟨Cs, hCs0, hCs⟩ := exists_transferSeparated_weighted I j P hT
  set Aα : ℝ := ∑ ξ, ∑ η, ‖α ξ η‖ with hAα
  set K₀ : ℝ := ‖Corr (Ideal.Quotient.mk _ (generator ⊤)) (Ideal.Quotient.mk _ (generator ⊤))‖ *
    ‖gaoZhaoTransform P 0‖ with hK₀
  have hAα0 : 0 ≤ Aα := by positivity
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨2 * Cs * Aα + K₀, by positivity, ?_⟩
  intro Ω O w Y ℓ X κ κ' φ p p' V M hκ hκ' hφ hconv hκn hκ'n hφn hV hO hM hMean
  have hV0 : ∀ x, x ∉ Set.Icc I.lo I.hi → V x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hV.2.1 h')
  have hVn : ∀ x, ‖V x‖ ≤ 1 := fun x => by
    by_cases hx : x ∈ Set.Icc I.lo I.hi
    · simpa using hV.2.2 0 (Nat.zero_le _) x hx
    · rw [hV0 x hx, norm_zero]; exact zero_le_one
  have hVs : ∀ x, V x ≠ 0 → x ≤ I.hi := fun x hx => by
    by_contra h; exact hx (hV0 x fun h' => h h'.2)
  set Wt : Ω → Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → ℝ := fun o r =>
    Y o * absNorm (r.1 * r.2.1) / (ℓ o * absNorm r.2.1) with hWt
  set S : ℝ := ∑ o ∈ O, w o * Y o *
    ∑ g ∈ starredLe (X o), (2 : ℝ) ^ Multiset.card (normalizedFactors g) with hS
  set E : Ω → Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → Finset 𝓔 := fun o r =>
    elementRows (passCap I.hi (Y o) (ℓ o) (r.1 * r.2.1) r.2.1) with hE
  set F : Ω → Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → 𝓔 → RayCharacter → RayCharacter → ℝ :=
    fun o r h ξ η => ‖passForm κ' (φ o) p p' P V (ℓ o) (Y o) (X o) r h ξ η‖ with hF
  have hform : ∀ ξ η, ∑ o ∈ O, w o * ∑ r ∈ passRows (X o), ∑ h ∈ E o r, Wt o r * F o r h ξ η ≤
      Cs * (M + M) := by
    intro ξ η
    set rows := O.sigma fun o => (passRows (X o)).sigma fun r => E o r
    have hpos : ∀ ρ ∈ rows, 0 ≤ w ρ.1 * Wt ρ.1 ρ.2.1 ∧
        0 < passScale (Y ρ.1) (ℓ ρ.1) (ρ.2.1.1 * ρ.2.1.2.1) ρ.2.1.2.1 ρ.2.2 := by
      intro ρ hρ
      obtain ⟨o, r, h⟩ := ρ
      simp only [rows, Finset.mem_sigma] at hρ
      obtain ⟨ho, hr, hh⟩ := hρ
      obtain ⟨hw, hY, hℓ, -⟩ := hO o ho
      obtain ⟨hg, he⟩ := passRows_ne_bot hr
      have hcap : 0 ≤ passCap I.hi (Y o) (ℓ o) (r.1 * r.2.1) r.2.1 := by
        unfold passCap; positivity
      have hh0 := ((mem_elementRows hcap).mp hh).1
      have hNh : 0 < (elementNorm h : ℝ) :=
        zero_lt_one.trans_le (absNorm_one_le (mt span_singleton_eq_bot.mp hh0))
      have hNg : 0 < (absNorm (r.1 * r.2.1) : ℝ) := zero_lt_one.trans_le (absNorm_one_le hg)
      have hNe : 0 < (absNorm r.2.1 : ℝ) := zero_lt_one.trans_le (absNorm_one_le he)
      refine ⟨mul_nonneg hw (by simp only [Wt]; positivity), ?_⟩
      simp only [passScale]; positivity
    have hm : ∀ ζ : RayCharacter, ∀ U, UnitTest I j U → ∑ ρ ∈ rows, w ρ.1 * Wt ρ.1 ρ.2.1 *
        ‖∑ n ∈ passCols (X ρ.1) ρ.2.1, dualCoeff κ' (φ ρ.1) p p' ζ (ρ.2.1.1 * ρ.2.1.2.1)
          ρ.2.1.2.1 ρ.2.1.2.2 ρ.2.2 n *
          U (absNorm (ρ.2.1.1 * ρ.2.1.2.1 * (ρ.2.1.2.2 * n)) / ℓ ρ.1)‖ ^ 2 ≤ M := by
      intro ζ U hU
      refine le_of_eq_of_le ?_ (hMean U hU ζ)
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.sum_sigma]
    have key := hCs rows (fun ρ => passCols (X ρ.1) ρ.2.1) (fun ρ => w ρ.1 * Wt ρ.1 ρ.2.1)
      (fun ρ n => dualCoeff κ' (φ ρ.1) p p' ξ (ρ.2.1.1 * ρ.2.1.2.1) ρ.2.1.2.1 ρ.2.1.2.2 ρ.2.2 n)
      (fun ρ n => dualCoeff κ' (φ ρ.1) p p' η (ρ.2.1.1 * ρ.2.1.2.1) ρ.2.1.2.1 ρ.2.1.2.2 ρ.2.2 n)
      (fun ρ n => absNorm (ρ.2.1.1 * ρ.2.1.2.1 * (ρ.2.1.2.2 * n)) / ℓ ρ.1) V
      (fun ρ => passScale (Y ρ.1) (ℓ ρ.1) (ρ.2.1.1 * ρ.2.1.2.1) ρ.2.1.2.1 ρ.2.2) hM hM hV hpos
      (hm ξ) (hm η)
    refine le_of_eq_of_le ?_ key
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [F, passForm, sepKernel]
    ring
  have htail : ∀ o ∈ O, ‖∑ t ∈ passSplits (X o), passDual κ κ' (φ o) p Corr V (ℓ o) (Y o) t *
      dualExclusionTail P (Y o) t.2.2 t.2.1 t.1‖ ≤
      ∑ ξ, ∑ η, ‖α ξ η‖ * ∑ r ∈ passRows (X o), ∑ h ∈ E o r, Wt o r * F o r h ξ η := by
    intro o ho
    obtain ⟨-, hY, hℓ, hX⟩ := hO o ho
    rw [sum_passDual_tail_eq_rows hres hκ' (hφ o) hα hT hVs hℓ hY hX]
    calc _ ≤ ∑ r ∈ passRows (X o), ∑ h ∈ E o r, ∑ ξ, ∑ η, ‖α ξ η‖ * (Wt o r * F o r h ξ η) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η _ => ?_)
          rw [norm_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (norm_passCoefficient_le hκn hκ'n (hφn o) p α hℓ hY r h ξ η) (norm_nonneg _)
      _ = _ := by
          rw [sum_sum_sum_sum_comm]
          simp only [Finset.mul_sum]
  have hzero : ∀ o ∈ O, ‖∑ t ∈ passSplits (X o), passDual κ κ' (φ o) p Corr V (ℓ o) (Y o) t *
      passZero P t‖ ≤ K₀ * (Y o *
        ∑ g ∈ starredLe (X o), (2 : ℝ) ^ Multiset.card (normalizedFactors g)) := by
    intro o ho
    obtain ⟨-, hY, -, hX⟩ := hO o ho
    refine (norm_sum_passZero_le hκn hκ'n (hφn o) hVn P (ℓ o) hY.le hX).trans (le_of_eq ?_)
    rw [hK₀]; ring
  calc _ ≤ ∑ o ∈ O, (w o * ∑ ξ, ∑ η, ‖α ξ η‖ *
          ∑ r ∈ passRows (X o), ∑ h ∈ E o r, Wt o r * F o r h ξ η + K₀ * (w o * Y o *
            ∑ g ∈ starredLe (X o), (2 : ℝ) ^ Multiset.card (normalizedFactors g))) := by
        refine Finset.sum_le_sum fun o ho => ?_
        obtain ⟨hw, hY, -, hX⟩ := hO o ho
        rw [tsum_passColumn_eq_add hP hY hκ (hφ o) hconv V (ℓ o) hX]
        calc _ ≤ w o * (‖∑ t ∈ passSplits (X o), passDual κ κ' (φ o) p Corr V (ℓ o) (Y o) t *
              dualExclusionTail P (Y o) t.2.2 t.2.1 t.1‖ + ‖∑ t ∈ passSplits (X o),
                passDual κ κ' (φ o) p Corr V (ℓ o) (Y o) t * passZero P t‖) :=
              mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (norm_add_le _ _)) hw
          _ ≤ _ := by
              rw [mul_add]
              exact add_le_add (mul_le_mul_of_nonneg_left (htail o ho) hw)
                ((mul_le_mul_of_nonneg_left (hzero o ho) hw).trans_eq (by ring))
    _ = ∑ ξ, ∑ η, ‖α ξ η‖ * ∑ o ∈ O, w o *
          ∑ r ∈ passRows (X o), ∑ h ∈ E o r, Wt o r * F o r h ξ η + K₀ * S := by
        rw [Finset.sum_add_distrib, hS, Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ξ _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun o _ =>
            Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun h _ => by ring
    _ ≤ ∑ ξ, ∑ η, ‖α ξ η‖ * (Cs * (M + M)) + K₀ * S := by
        gcongr with ξ _ η _
        exact hform ξ η
    _ = 2 * Cs * Aα * M + K₀ * S := by
        simp only [← Finset.sum_mul, hAα]
        ring
    _ ≤ _ := by
        have hS0 : 0 ≤ S := Finset.sum_nonneg fun o ho => by
          obtain ⟨hw, hY, -, -⟩ := hO o ho
          positivity
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCs0) hAα0) hS0,
          mul_nonneg hK₀0 hM]

end Masullo.QRH.MeanSquare
