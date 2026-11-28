import Masullo.QRH.MeanSquare.TransferFirst
import Masullo.QRH.MeanSquare.TransferRegroup
import Masullo.QRH.MeanSquare.DualTail

/-!
# Counting bounds for the transfer

Polynomial-saving bounds on the divisor-weighted sums that remain after the two Poisson passes of
`TransferEstimate`. Each sum over ideals of norm at most `X` is bounded by a power of any
`Y ≥ max 1 X`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma one_le_absNorm_real {n : Ideal 𝓔} (hn : n ≠ ⊥) : (1 : ℝ) ≤ (absNorm n : ℝ) := by
  have : absNorm n ≠ 0 := fun h => hn (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

private lemma card_starredLe_le :
    ∃ K ≥ (0 : ℝ), ∀ X : ℝ, 0 ≤ X → ((starredLe X).card : ℝ) ≤ K * X := by
  classical
  obtain ⟨K, hK⟩ := exists_card_idealsLe_le
  have hK0 : 0 ≤ K := by
    have := hK 1 le_rfl
    linarith [(Nat.cast_nonneg (idealsLe 1).card : (0 : ℝ) ≤ _)]
  refine ⟨K, hK0, fun X hX => ?_⟩
  by_cases h1 : X < 1
  · have : starredLe X = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
      obtain ⟨h, hs⟩ := (mem_starredLe hX).mp hn
      linarith [one_le_absNorm_real hs.1.1]
    rw [this]; simpa using mul_nonneg hK0 hX
  · refine le_trans ?_ (hK X (not_lt.mp h1))
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

private lemma starredLe_subset {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    starredLe X ⊆ idealsLe Y := fun _ hn =>
  (mem_idealsLe (hX.trans hXY)).mpr (((mem_starredLe hX).mp hn).1.trans hXY)

theorem exists_card_dyadicStarred_le :
    ∃ C ≥ (0 : ℝ), ∀ F : ℝ, 1 ≤ F → ((dyadicStarred F).card : ℝ) ≤ C * F := by
  classical
  obtain ⟨K, hK⟩ := exists_card_idealsLe_le
  have hK0 : 0 ≤ K := by
    have := hK 1 le_rfl
    linarith [(Nat.cast_nonneg (idealsLe 1).card : (0 : ℝ) ≤ _)]
  refine ⟨2 * K, by positivity, fun F hF => ?_⟩
  have h1 : (dyadicStarred F).card ≤ (idealsLe (2 * F)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h2 := hK (2 * F) (by linarith)
  calc ((dyadicStarred F).card : ℝ) ≤ (idealsLe (2 * F)).card := by exact_mod_cast h1
    _ ≤ K * (2 * F) := h2
    _ = 2 * K * F := by ring

theorem exists_sum_two_pow_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ X Y : ℝ, 0 ≤ X → X ≤ Y → 1 ≤ Y →
      ∑ g ∈ starredLe X, (2 : ℝ) ^ Multiset.card (normalizedFactors g) ≤ C * X * Y ^ s := by
  obtain ⟨C, hC, hτ⟩ := two_pow_card_normalizedFactors_le hs
  obtain ⟨K, hK, hcard⟩ := card_starredLe_le
  refine ⟨C * K, by positivity, fun X Y hX hXY hY => ?_⟩
  have hY0 : 0 ≤ Y ^ s := Real.rpow_nonneg (by linarith) _
  have hterm : ∀ g ∈ starredLe X, (2 : ℝ) ^ Multiset.card (normalizedFactors g) ≤ C * Y ^ s := by
    intro g hg
    obtain ⟨hn, hsq⟩ := (mem_starredLe hX).mp hg
    refine (hτ g hsq.1.1 hsq.2).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hn.trans hXY) hs.le
  calc _ ≤ ∑ g ∈ starredLe X, C * Y ^ s := Finset.sum_le_sum hterm
    _ = (starredLe X).card * (C * Y ^ s) := by simp
    _ ≤ (K * X) * (C * Y ^ s) :=
        mul_le_mul_of_nonneg_right (hcard X hX) (by positivity)
    _ = C * K * X * Y ^ s := by ring

theorem exists_sum_passRows_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ X Y : ℝ, 0 ≤ X → X ≤ Y → 1 ≤ Y →
      ∑ r ∈ passRows X, ((absNorm (r.1 * r.2.1) : ℝ))⁻¹ *
        (X / absNorm (r.1 * r.2.1 * r.2.2)) ≤ C * X * Y ^ s := by
  classical
  obtain ⟨C, hC, hS⟩ := exists_sum_inv_absNorm_le (show 0 < s / 3 by positivity)
  refine ⟨C ^ 3, by positivity, fun X Y hX hXY hY => ?_⟩
  set S : ℝ := ∑ b ∈ idealsLe X, (absNorm b : ℝ)⁻¹ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hSY : S ≤ C * Y ^ (s / 3) := by
    refine le_trans ?_ (hS Y hY)
    exact Finset.sum_le_sum_of_subset_of_nonneg (idealsLe_mono hXY)
      fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hterm : ∀ r ∈ passRows X, ((absNorm (r.1 * r.2.1) : ℝ))⁻¹ *
        (X / absNorm (r.1 * r.2.1 * r.2.2)) ≤
      X * ((absNorm r.1 : ℝ)⁻¹ * (absNorm r.2.1 : ℝ)⁻¹ * (absNorm r.2.2 : ℝ)⁻¹) := by
    intro r hr
    obtain ⟨-, h1, h2, -⟩ := Finset.mem_filter.mp hr
    have hb : r.1 ≠ ⊥ := fun h => h1.1.1 (by rw [h]; simp)
    have he : r.2.1 ≠ ⊥ := fun h => h1.1.1 (by rw [h]; simp)
    have hv : r.2.2 ≠ ⊥ := h2.1.1
    have hbe := one_le_absNorm_real h1.1.1
    have hw : (0 : ℝ) ≤ X * ((absNorm r.1 : ℝ)⁻¹ * (absNorm r.2.1 : ℝ)⁻¹ *
        (absNorm r.2.2 : ℝ)⁻¹) := by positivity
    have heq : X / (absNorm (r.1 * r.2.1 * r.2.2) : ℝ) = X * ((absNorm r.1 : ℝ)⁻¹ *
        (absNorm r.2.1 : ℝ)⁻¹ * (absNorm r.2.2 : ℝ)⁻¹) := by
      rw [map_mul, map_mul]; push_cast
      rw [div_eq_mul_inv, mul_inv, mul_inv]
    rw [heq]
    calc _ ≤ 1 *
          (X * ((absNorm r.1 : ℝ)⁻¹ * (absNorm r.2.1 : ℝ)⁻¹ * (absNorm r.2.2 : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hbe) hw
      _ = _ := one_mul _
  have hsub : passRows X ⊆ idealsLe X ×ˢ (idealsLe X ×ˢ idealsLe X) :=
    fun r hr => (Finset.mem_filter.mp hr).1
  have hcube : ∑ r ∈ idealsLe X ×ˢ (idealsLe X ×ˢ idealsLe X),
      X * ((absNorm r.1 : ℝ)⁻¹ * (absNorm r.2.1 : ℝ)⁻¹ * (absNorm r.2.2 : ℝ)⁻¹) =
      X * S ^ 3 := by
    rw [← Finset.mul_sum, Finset.sum_product]
    congr 1
    simp only [Finset.sum_product, hSdef, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  calc _ ≤ ∑ r ∈ passRows X, X * ((absNorm r.1 : ℝ)⁻¹ * (absNorm r.2.1 : ℝ)⁻¹ *
        (absNorm r.2.2 : ℝ)⁻¹) := Finset.sum_le_sum hterm
    _ ≤ ∑ r ∈ idealsLe X ×ˢ (idealsLe X ×ˢ idealsLe X), X * ((absNorm r.1 : ℝ)⁻¹ *
        (absNorm r.2.1 : ℝ)⁻¹ * (absNorm r.2.2 : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = X * S ^ 3 := hcube
    _ ≤ X * (C * Y ^ (s / 3)) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hSY 3) hX
    _ = C ^ 3 * X * Y ^ s := by
        have : (Y ^ (s / 3)) ^ 3 = Y ^ s := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
        rw [mul_pow, this]; ring

theorem exists_sum_four_pow_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ X Y : ℝ, 0 ≤ X → X ≤ Y → 1 ≤ Y →
      ∑ r ∈ starredLe X, (4 : ℝ) ^ Multiset.card (normalizedFactors r) / absNorm r ≤
        C * Y ^ s := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := two_pow_card_normalizedFactors_le (show 0 < s / 4 by positivity)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_sum_inv_absNorm_le (show 0 < s / 2 by positivity)
  refine ⟨C₁ ^ 2 * C₂, by positivity, fun X Y hX hXY hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hterm : ∀ r ∈ starredLe X, (4 : ℝ) ^ Multiset.card (normalizedFactors r) /
      absNorm r ≤ C₁ ^ 2 * Y ^ (s / 2) * (absNorm r : ℝ)⁻¹ := by
    intro r hr
    obtain ⟨hn, hsq⟩ := (mem_starredLe hX).mp hr
    have h4 : (4 : ℝ) ^ Multiset.card (normalizedFactors r) =
        ((2 : ℝ) ^ Multiset.card (normalizedFactors r)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hb : (2 : ℝ) ^ Multiset.card (normalizedFactors r) ≤ C₁ * Y ^ (s / 4) :=
      (h₁ r hsq.1.1 hsq.2).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hn.trans hXY) (by positivity)) hC₁)
    have hsq2 : (Y ^ (s / 4)) ^ 2 = Y ^ (s / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; congr 1; push_cast; ring
    rw [div_eq_mul_inv, h4]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
    calc _ ≤ (C₁ * Y ^ (s / 4)) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
      _ = C₁ ^ 2 * Y ^ (s / 2) := by rw [mul_pow, hsq2]
  calc _ ≤ ∑ r ∈ starredLe X, C₁ ^ 2 * Y ^ (s / 2) * (absNorm r : ℝ)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = C₁ ^ 2 * Y ^ (s / 2) * ∑ r ∈ starredLe X, (absNorm r : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ C₁ ^ 2 * Y ^ (s / 2) * (C₂ * Y ^ (s / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans ?_ (h₂ Y hY)
        exact Finset.sum_le_sum_of_subset_of_nonneg (starredLe_subset hX hXY)
          fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
    _ = C₁ ^ 2 * C₂ * Y ^ s := by
        have : Y ^ (s / 2) * Y ^ (s / 2) = Y ^ s := by
          rw [← Real.rpow_add hY0]; congr 1; ring
        calc _ = C₁ ^ 2 * C₂ * (Y ^ (s / 2) * Y ^ (s / 2)) := by ring
          _ = _ := by rw [this]

theorem exists_natLog_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ X Y : ℝ, 0 ≤ X → X ≤ Y → 1 ≤ Y →
      (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) ≤ C * Y ^ s := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / (s * Real.log 2) + 1, by positivity, fun X Y hX hXY hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hYs : 1 ≤ Y ^ s := Real.one_le_rpow hY hs.le
  set k := Nat.log 2 ⌊X⌋₊ with hk
  have h2k : (2 : ℝ) ^ k ≤ Y := by
    by_cases h0 : ⌊X⌋₊ = 0
    · rw [hk, h0]; simpa using hY
    · have : 2 ^ k ≤ ⌊X⌋₊ := Nat.pow_log_le_self 2 h0
      have h' : ((2 ^ k : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h'.trans ((Nat.floor_le hX).trans hXY)
  have hlog : (k : ℝ) * Real.log 2 ≤ Real.log Y := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2k
  have hly : Real.log Y ≤ Y ^ s / s := Real.log_le_rpow_div hY0.le hs
  have hk' : (k : ℝ) ≤ Y ^ s / (s * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc (k : ℝ) * (s * Real.log 2) = s * ((k : ℝ) * Real.log 2) := by ring
      _ ≤ s * (Y ^ s / s) := mul_le_mul_of_nonneg_left (hlog.trans hly) hs.le
      _ = Y ^ s := by field_simp
  calc (k + 1 : ℝ) ≤ Y ^ s / (s * Real.log 2) + 1 := by linarith
    _ ≤ Y ^ s / (s * Real.log 2) + Y ^ s := by linarith
    _ = (1 / (s * Real.log 2) + 1) * Y ^ s := by ring

/-- The divisor bound in the form `secondDual_le` uses. -/
theorem exists_card_idealDivisors_pair_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ (a b : Ideal 𝓔) (Y : ℝ), a ≠ ⊥ → b ≠ ⊥ → (absNorm a : ℝ) * absNorm b ≤ Y →
      ((idealDivisors a).card : ℝ) * ((idealDivisors b).card : ℝ) ^ 4 ≤ C * Y ^ s := by
  obtain ⟨C, hC, hτ⟩ := card_idealDivisors_le (show 0 < s / 4 by positivity)
  refine ⟨C ^ 5, by positivity, fun a b Y ha hb hab => ?_⟩
  have ha1 := one_le_absNorm_real ha
  have hb1 := one_le_absNorm_real hb
  have hA := hτ a ha
  have hB := hτ b hb
  have hB4 : ((idealDivisors b).card : ℝ) ^ 4 ≤ (C * (absNorm b : ℝ) ^ (s / 4)) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hB 4
  have hbb : ((absNorm b : ℝ) ^ (s / 4)) ^ 4 = (absNorm b : ℝ) ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  have haa : (absNorm a : ℝ) ^ (s / 4) ≤ (absNorm a : ℝ) ^ s :=
    Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
  have hab' : ((absNorm a : ℝ) * absNorm b) ^ s = (absNorm a : ℝ) ^ s * (absNorm b : ℝ) ^ s :=
    Real.mul_rpow (by linarith) (by linarith)
  have hYs : ((absNorm a : ℝ) * absNorm b) ^ s ≤ Y ^ s :=
    Real.rpow_le_rpow (by positivity) hab hs.le
  have hp1 : 0 ≤ (absNorm b : ℝ) ^ s := by positivity
  calc ((idealDivisors a).card : ℝ) * ((idealDivisors b).card : ℝ) ^ 4
      ≤ (C * (absNorm a : ℝ) ^ (s / 4)) * (C * (absNorm b : ℝ) ^ (s / 4)) ^ 4 :=
        mul_le_mul hA hB4 (by positivity) (by positivity)
    _ = C ^ 5 * ((absNorm a : ℝ) ^ (s / 4) * ((absNorm b : ℝ) ^ (s / 4)) ^ 4) := by ring
    _ ≤ C ^ 5 * ((absNorm a : ℝ) ^ s * (absNorm b : ℝ) ^ s) := by
        rw [hbb]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haa hp1) (by positivity)
    _ ≤ C ^ 5 * Y ^ s := by rw [← hab']; exact mul_le_mul_of_nonneg_left hYs (by positivity)

/-- The divisor bound in the form `firstDual_le_secondInput` uses. -/
theorem exists_card_idealDivisors_span_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ (y : 𝓔) (Y : ℝ), y ≠ 0 → (elementNorm y : ℝ) ≤ Y →
      ((idealDivisors (span {y})).card : ℝ) ≤ C * Y ^ s := by
  obtain ⟨C, hC, hτ⟩ := card_idealDivisors_le hs
  refine ⟨C, hC, fun y Y hy hY => ?_⟩
  have hne : span {y} ≠ (⊥ : Ideal 𝓔) := by
    rw [Ne, span_singleton_eq_bot]; exact hy
  refine (hτ _ hne).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hY hs.le

end Masullo.QRH.MeanSquare
