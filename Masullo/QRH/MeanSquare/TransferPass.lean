import Masullo.QRH.MeanSquare.DualTail
import Masullo.QRH.MeanSquare.TransferKernel

/-!
# A Poisson pass of the transfer estimate

Tools shared by the two Poisson passes of `TransferEstimate`.

* `sum_norm_bilinear_le_polar`: four-term polarization reduces a bilinear form with two
  coefficient families to four quadratic forms.
* `exists_transferSeparated_le₂`: the separation `exists_transferSeparated_le` of the
  band-limited first-Poisson kernel for two coefficient families and row-dependent column
  positions `x ρ n`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open MeasureTheory Set
open scoped ComplexConjugate ContDiff SchwartzMap

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-! ### Polarized separation with row-dependent positions -/

/-- The fourth roots of unity of the polarization. -/
def polarUnit : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

lemma norm_polarUnit (k : Fin 4) : ‖polarUnit k‖ = 1 := by
  fin_cases k <;> simp [polarUnit]

/-- A bilinear form in `c₁, conj c₂` is a quarter of four quadratic forms in
`c₁ + ω c₂`. -/
lemma sum_norm_bilinear_le_polar {R N : Type*} (rows : Finset R) (cols : Finset N)
    (c₁ c₂ : R → N → ℂ) (K : R → N → N → ℂ) :
    ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂‖ ≤
      (1 / 4) * ∑ k : Fin 4, ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols,
        (c₁ ρ n₁ + polarUnit k * c₂ ρ n₁) * conj (c₁ ρ n₂ + polarUnit k * c₂ ρ n₂) *
          K ρ n₁ n₂‖ := by
  set d : Fin 4 → R → N → ℂ := fun k ρ n => c₁ ρ n + polarUnit k * c₂ ρ n
  have hpt : ∀ ρ, ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂ =
      (1 / 4 : ℂ) * ∑ k : Fin 4, polarUnit k *
        ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂ := by
    intro ρ
    have e : ∀ n₁ n₂, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂ = (1 / 4 : ℂ) *
        ∑ k : Fin 4, polarUnit k * (d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂) := by
      intro n₁ n₂
      rw [show (∑ k : Fin 4, polarUnit k * (d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂)) =
          (∑ k : Fin 4, polarUnit k * (d k ρ n₁ * conj (d k ρ n₂))) * K ρ n₁ n₂ by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring]
      rw [show (∑ k : Fin 4, polarUnit k * (d k ρ n₁ * conj (d k ρ n₂))) =
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
        simp [norm_polarUnit]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- The mean square of `c₁ + ω c₂` with `|ω| = 1`. -/
lemma sum_norm_sq_add_le {R N : Type*} (rows : Finset R) (cols : Finset N)
    (c₁ c₂ : R → N → ℂ) (V : R → N → ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    ∑ ρ ∈ rows, ‖∑ n ∈ cols, (c₁ ρ n + u * c₂ ρ n) * V ρ n‖ ^ 2 ≤
      2 * ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₁ ρ n * V ρ n‖ ^ 2 +
        2 * ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₂ ρ n * V ρ n‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ρ _ => ?_
  have : ∑ n ∈ cols, (c₁ ρ n + u * c₂ ρ n) * V ρ n = ∑ n ∈ cols, c₁ ρ n * V ρ n +
      u * ∑ n ∈ cols, c₂ ρ n * V ρ n := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [this]
  refine (norm_add_sq_le_two _ _).trans ?_
  rw [norm_mul, hu, one_mul]

/-- `exists_transferSeparated_le` with row-dependent column positions `x ρ n`. -/
theorem exists_transferSeparated_le' (I : TestInterval) (j : ℕ) (P : 𝓢(ℝ, ℂ))
    (hP : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0) : ∃ C ≥ (0 : ℝ),
    ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c : R → N → ℂ) (x : R → N → ℝ)
      (W : ℝ → ℂ) (A : R → ℝ) {M : ℝ}, 0 ≤ M →
      UnitTest I j W → (∀ ρ ∈ rows, 0 < A ρ) →
      (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * U (x ρ n)‖ ^ 2 ≤ M) →
      ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
        (W (x ρ n₁) * conj (W (x ρ n₂)) * ((((√(x ρ n₁ * x ρ n₂))⁻¹ : ℝ) : ℂ) *
          gaoZhaoTransform P (√(A ρ / (x ρ n₁ * x ρ n₂)))))‖ ≤ C * M := by
  classical
  obtain ⟨C, hC, h⟩ := exists_transferSeparated_le I j P hP
  refine ⟨C, hC, fun {R N} rows cols c x W A M hM hW hA hU => ?_⟩
  -- Columns indexed by pairs `(ρ', n)`, with coefficient zero unless `ρ' = ρ`.
  set c' : R → R × N → ℂ := fun ρ p => if p.1 = ρ then c ρ p.2 else 0
  set x' : R × N → ℝ := fun p => x p.1 p.2
  have hsum : ∀ ρ ∈ rows, ∀ G : R × N → ℂ,
      ∑ p ∈ rows ×ˢ cols, (if p.1 = ρ then G p else 0) = ∑ n ∈ cols, G (ρ, n) := by
    intro ρ hρ G
    rw [Finset.sum_product, Finset.sum_eq_single ρ]
    · exact Finset.sum_congr rfl fun n _ => by simp
    · intro ρ' _ hne
      exact Finset.sum_eq_zero fun n _ => by simp [hne]
    · exact fun h => absurd hρ h
  have key := h rows (rows ×ˢ cols) c' x' W W A hM hW hW hA (fun U hU' => by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun ρ hρ => ?_) (hU U hU')
    rw [← hsum ρ hρ fun p => c ρ p.2 * U (x' p)]
    congr 2
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.1 = ρ <;> simp [c', hp])
  refine le_of_eq_of_le (Finset.sum_congr rfl fun ρ hρ => ?_) key
  congr 1
  set Kf : R × N → R × N → ℂ := fun p q => W (x' p) * conj (W (x' q)) *
    ((((√(x' p * x' q))⁻¹ : ℝ) : ℂ) * gaoZhaoTransform P (√(A ρ / (x' p * x' q))))
  have inner : ∀ p, ∑ q ∈ rows ×ˢ cols, c' ρ p * conj (c' ρ q) * Kf p q =
      if p.1 = ρ then ∑ m ∈ cols, c ρ p.2 * conj (c ρ m) * Kf p (ρ, m) else 0 := by
    intro p
    split_ifs with hp
    · rw [← hsum ρ hρ fun q => c ρ p.2 * conj (c ρ q.2) * Kf p q]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q.1 = ρ <;> simp [c', hp, hq]
    · exact Finset.sum_eq_zero fun q _ => by simp [c', hp]
  rw [Finset.sum_congr rfl fun p _ => inner p,
    hsum ρ hρ fun p => ∑ m ∈ cols, c ρ p.2 * conj (c ρ m) * Kf p (ρ, m)]

/-- `exists_transferSeparated_le` for two coefficient families and row-dependent column
positions. -/
theorem exists_transferSeparated_le₂ (I : TestInterval) (j : ℕ) (P : 𝓢(ℝ, ℂ))
    (hP : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0) : ∃ C ≥ (0 : ℝ),
    ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c₁ c₂ : R → N → ℂ)
      (x : R → N → ℝ) (W : ℝ → ℂ) (A : R → ℝ) {M₁ M₂ : ℝ}, 0 ≤ M₁ → 0 ≤ M₂ →
      UnitTest I j W → (∀ ρ ∈ rows, 0 < A ρ) →
      (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₁ ρ n * U (x ρ n)‖ ^ 2 ≤ M₁) →
      (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₂ ρ n * U (x ρ n)‖ ^ 2 ≤ M₂) →
      ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) *
        (W (x ρ n₁) * conj (W (x ρ n₂)) * ((((√(x ρ n₁ * x ρ n₂))⁻¹ : ℝ) : ℂ) *
          gaoZhaoTransform P (√(A ρ / (x ρ n₁ * x ρ n₂)))))‖ ≤ C * (M₁ + M₂) := by
  obtain ⟨C, hC, h⟩ := exists_transferSeparated_le' I j P hP
  refine ⟨2 * C, by positivity,
    fun {R N} rows cols c₁ c₂ x W A M₁ M₂ hM₁ hM₂ hW hA h₁ h₂ => ?_⟩
  refine (sum_norm_bilinear_le_polar rows cols c₁ c₂ _).trans ?_
  have hk : ∀ k : Fin 4, ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols,
      (c₁ ρ n₁ + polarUnit k * c₂ ρ n₁) * conj (c₁ ρ n₂ + polarUnit k * c₂ ρ n₂) *
        (W (x ρ n₁) * conj (W (x ρ n₂)) * ((((√(x ρ n₁ * x ρ n₂))⁻¹ : ℝ) : ℂ) *
          gaoZhaoTransform P (√(A ρ / (x ρ n₁ * x ρ n₂)))))‖ ≤
        C * (2 * M₁ + 2 * M₂) := fun k =>
    h rows cols (fun ρ n => c₁ ρ n + polarUnit k * c₂ ρ n) x W A (by positivity) hW hA
      fun U hU => (sum_norm_sq_add_le rows cols c₁ c₂ (fun ρ n => U (x ρ n))
        (norm_polarUnit k)).trans (by linarith [h₁ U hU, h₂ U hU])
  calc (1 / 4) * ∑ k : Fin 4, _ ≤ (1 / 4) * ∑ _k : Fin 4, C * (2 * M₁ + 2 * M₂) := by
        gcongr with k; exact hk k
    _ = 2 * C * (M₁ + M₂) := by simp; ring

end Masullo.QRH.MeanSquare
