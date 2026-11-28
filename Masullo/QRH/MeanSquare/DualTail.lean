import Masullo.QRH.MeanSquare.OffDiagonal

/-!
# The nonzero dual frequencies

Steps toward `DualTailEstimate rowMajorant` from `GapEstimate`.

* `exists_rayCharacter_expansion`: a function on pairs of residues modulo `72` is, on pairs of
  units, a combination of `ξ(x) conj η(y)` over ray characters `ξ, η`.
* `exists_dilated_separated_le₂`: the separation of dilated kernels for a pair of coefficient
  families, by four-term polarization.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open MeasureTheory Set
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-! ### Ray characters separate units -/

instance : Finite Q₇₂ :=
  (Ideal.absNorm_ne_zero_iff _).mp (Ideal.absNorm_eq_zero_iff.not.mpr
    (span_singleton_eq_bot.not.mpr (by norm_num)))

instance : Fintype Q₇₂ := Fintype.ofFinite _

instance : Fintype RayCharacter := Fintype.ofFinite _

lemma sum_rayCharacter_apply (u : Q₇₂ˣ) : open Classical in
    ∑ ξ : RayCharacter, ξ u = if u = 1 then (Fintype.card RayCharacter : ℂ) else 0 := by
  classical
  split_ifs with hu
  · simp [hu]
  · obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q₇₂ ℂ
      (a := (u : Q₇₂)) (by simpa [Units.val_eq_one] using hu)
    have h : ∑ ξ : RayCharacter, ξ u = χ u * ∑ ξ : RayCharacter, ξ u := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft χ) (fun ξ : RayCharacter => χ u * ξ u)
        (fun ξ : RayCharacter => ξ u) fun ξ => by simp).symm
    have : (1 - χ u) * ∑ ξ : RayCharacter, ξ u = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hχ))

lemma sum_rayCharacter_mul_conj (u v : Q₇₂ˣ) : open Classical in
    ∑ ξ : RayCharacter, ξ u * conj (ξ v) =
      if u = v then (Fintype.card RayCharacter : ℂ) else 0 := by
  classical
  have h : ∀ ξ : RayCharacter, ξ u * conj (ξ v) = ξ ↑(u * v⁻¹) := fun ξ => by
    rw [← RCLike.star_def, MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
      Units.val_mul, map_mul]
  simp_rw [h, sum_rayCharacter_apply, mul_inv_eq_one]

/-- A function on pairs of residues is, on pairs of units, a combination of products of ray
characters. -/
theorem exists_rayCharacter_expansion (A : Q₇₂ → Q₇₂ → ℂ) :
    ∃ α : RayCharacter → RayCharacter → ℂ, ∀ x y : Q₇₂, IsUnit x → IsUnit y →
      A x y = ∑ ξ : RayCharacter, ∑ η : RayCharacter, α ξ η * ξ x * conj (η y) := by
  classical
  set N : ℂ := (Fintype.card RayCharacter : ℂ)
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun ξ η => (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ * conj (ξ x₀) * η y₀) / N ^ 2,
    fun x y hx hy => ?_⟩
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have hexp : ∑ ξ : RayCharacter, ∑ η : RayCharacter,
      (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ * conj (ξ x₀) * η y₀) / N ^ 2 * ξ u * conj (η v) =
      (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ *
        (∑ ξ : RayCharacter, ξ u * conj (ξ x₀)) *
        (∑ η : RayCharacter, η y₀ * conj (η v))) / N ^ 2 := by
    have h4 : ∀ f : RayCharacter → RayCharacter → Q₇₂ˣ → Q₇₂ˣ → ℂ,
        ∑ ξ, ∑ η, ∑ x, ∑ y, f ξ η x y = ∑ x, ∑ y, ∑ ξ, ∑ η, f ξ η x y := by
      intro f
      calc _ = ∑ ξ, ∑ x, ∑ η, ∑ y, f ξ η x y := Finset.sum_congr rfl fun ξ _ => Finset.sum_comm
        _ = ∑ ξ, ∑ x, ∑ y, ∑ η, f ξ η x y := Finset.sum_congr rfl fun ξ _ =>
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ x, ∑ ξ, ∑ y, ∑ η, f ξ η x y := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine (h4 _).trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ξ _ => ?_))
    ring
  rw [hexp]
  simp_rw [sum_rayCharacter_mul_conj]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  field_simp
  rfl

/-- The primary generator of an ideal prime to six is a unit modulo `72`. -/
lemma isUnit_mk_generator {n : Ideal 𝓔} (hn : AwayFromSix n) :
    IsUnit (Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n)) := by
  rw [isUnit_mk_iff_coprime_span, span_generator]
  have h3 : IsCoprime (span {(6 : 𝓔)} ^ 3) n := (hn.2.symm.pow_left)
  rw [span_singleton_pow, Ideal.isCoprime_iff_sup_eq] at h3
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← h3]
  refine sup_le_sup_right (span_singleton_le_span_singleton.mpr ⟨3, by norm_num⟩) _

/-! ### Polarized separation -/

/-- Four-term polarization: `4 a conj b' = ∑_ω ω (a + ω b) conj (a' + ω b')` over the fourth
roots of unity `ω`. -/
lemma polarization (a b a' b' : ℂ) :
    4 * (a * conj b') = ∑ k : Fin 4, ![1, Complex.I, -1, -Complex.I] k *
      ((a + ![1, Complex.I, -1, -Complex.I] k * b) *
        conj (a' + ![1, Complex.I, -1, -Complex.I] k * b')) := by
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, map_mul, map_neg,
    Complex.conj_I, map_one]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  nlinarith [norm_add_le a b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]

/-- `exists_dilated_separated_le` for two coefficient families `c₁, c₂` with mean squares at
most `M₁, M₂`. -/
theorem exists_dilated_separated_le₂ {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) {L : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    ∃ (I : TestInterval) (C : ℝ), 0 ≤ C ∧
      ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c₁ c₂ : R → N → ℂ) (x : N → ℝ)
        (ℓ : R → ℝ) (ψ : R → ℝ → ℂ) {A M₁ M₂ : ℝ}, 0 ≤ A → 0 ≤ M₁ → 0 ≤ M₂ →
        (∀ n ∈ cols, 0 < x n) → (∀ ρ ∈ rows, ℓ ρ ∈ Icc 0 L) →
        (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₁ ρ n * U (x n)‖ ^ 2 ≤ M₁) →
        (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₂ ρ n * U (x n)‖ ^ 2 ≤ M₂) →
        (∀ ρ ∈ rows, ContDiff ℝ (2 * j + 2) (ψ ρ)) →
        (∀ ρ ∈ rows, ∀ k ≤ 2 * j + 2, Integrable (iteratedDeriv k (ψ ρ))) →
        (∀ ρ ∈ rows, ∫ v, ‖ψ ρ v‖ ≤ A) →
        (∀ ρ ∈ rows, ∫ v, ‖iteratedDeriv (2 * j + 2) (ψ ρ) v‖ ≤ A) →
        ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) *
          (w (ℓ ρ + Real.log (x n₁)) * conj (w (ℓ ρ + Real.log (x n₂))) *
            ψ ρ (Real.log (x n₁) + Real.log (x n₂)))‖ ≤ C * A * (M₁ + M₂) := by
  obtain ⟨I, C, hC, h⟩ := exists_dilated_separated_le hw hwc hL j
  refine ⟨I, 2 * C, by positivity, fun {R N} rows cols c₁ c₂ x ℓ ψ A M₁ M₂ hA hM₁ hM₂ hx hℓ
    h₁ h₂ hψ hψi hψA hψA' => ?_⟩
  set u : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I] with hu_def
  have hu : ∀ k, ‖u k‖ = 1 := by intro k; fin_cases k <;> simp [u]
  set K : R → N → N → ℂ := fun ρ n₁ n₂ => w (ℓ ρ + Real.log (x n₁)) *
    conj (w (ℓ ρ + Real.log (x n₂))) * ψ ρ (Real.log (x n₁) + Real.log (x n₂)) with hK
  set d : Fin 4 → R → N → ℂ := fun k ρ n => c₁ ρ n + u k * c₂ ρ n
  have hd : ∀ k, ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) *
      K ρ n₁ n₂‖ ≤ C * A * (2 * M₁ + 2 * M₂) := by
    intro k
    refine h rows cols (d k) x ℓ ψ hA (by positivity) hx hℓ (fun U hU => ?_) hψ hψi hψA hψA'
    calc ∑ ρ ∈ rows, ‖∑ n ∈ cols, d k ρ n * U (x n)‖ ^ 2
        ≤ ∑ ρ ∈ rows, (2 * ‖∑ n ∈ cols, c₁ ρ n * U (x n)‖ ^ 2 +
            2 * ‖∑ n ∈ cols, c₂ ρ n * U (x n)‖ ^ 2) := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          have : ∑ n ∈ cols, d k ρ n * U (x n) = ∑ n ∈ cols, c₁ ρ n * U (x n) +
              u k * ∑ n ∈ cols, c₂ ρ n * U (x n) := by
            simp only [d, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun n _ => by ring
          rw [this]
          refine (norm_add_sq_le_two _ _).trans ?_
          rw [norm_mul, hu, one_mul]
      _ ≤ 2 * M₁ + 2 * M₂ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          linarith [h₁ U hU, h₂ U hU]
  have hpt : ∀ ρ, ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂ =
      (1 / 4 : ℂ) * ∑ k : Fin 4, u k *
        ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂ := by
    intro ρ
    have e : ∀ n₁ n₂, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂ = (1 / 4 : ℂ) *
        ∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂) := by
      intro n₁ n₂
      rw [show (∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂)) =
          (∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂))) * K ρ n₁ n₂ by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring]
      rw [show (∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂))) =
          4 * (c₁ ρ n₁ * conj (c₂ ρ n₂)) from
        (polarization (c₁ ρ n₁) (c₂ ρ n₁) (c₁ ρ n₂) (c₂ ρ n₂)).symm]
      ring
    simp only [e, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n₁ _ => ?_
    rw [Finset.sum_comm]
  calc ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂‖
      ≤ ∑ ρ ∈ rows, (1 / 4) * ∑ k : Fin 4,
          ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂‖ := by
        refine Finset.sum_le_sum fun ρ _ => ?_
        rw [hpt, norm_mul]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
        simp [hu]
    _ = (1 / 4) * ∑ k : Fin 4, ∑ ρ ∈ rows,
          ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (1 / 4) * ∑ _k : Fin 4, C * A * (2 * M₁ + 2 * M₂) := by
        gcongr with k; exact hd k
    _ = 2 * C * A * (M₁ + M₂) := by simp; ring

end Masullo.QRH.MeanSquare
