import Masullo.QRH.StageB

/-! # Weighted square sums in cube inversion -/

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

/-- Cauchy–Schwarz for row-dependent coefficients with a common majorant. -/
theorem sum_norm_weighted_sum_sq_le {ι κ : Type*} (s : Finset ι) (rows : Finset κ)
    (u : ι → ℝ) (w v : ι → κ → ℂ) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hw : ∀ i ∈ s, ∀ x ∈ rows, ‖w i x‖ ≤ u i) :
    ∑ x ∈ rows, ‖∑ i ∈ s, w i x * v i x‖ ^ 2 ≤
      (∑ i ∈ s, u i) * ∑ i ∈ s, u i * ∑ x ∈ rows, ‖v i x‖ ^ 2 := by
  have hrow (x : κ) (hx : x ∈ rows) :
      ‖∑ i ∈ s, w i x * v i x‖ ^ 2 ≤ (∑ i ∈ s, u i) * ∑ i ∈ s, u i * ‖v i x‖ ^ 2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2).trans
      (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hu (fun i hi => mul_nonneg (hu i hi) (sq_nonneg _)) ?_)
    intro i hi
    rw [norm_mul, mul_pow]
    calc
      _ ≤ u i ^ 2 * ‖v i x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hw i hi x hx) 2) (sq_nonneg _)
      _ = _ := by ring
  refine (Finset.sum_le_sum hrow).trans_eq ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.mul_sum]

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private theorem dyadic_harmonic_sum {A : ℝ}
    (hA : ∀ x : ℝ, 1 ≤ x → ((idealsLe x).card : ℝ) ≤ A * x) (m : ℕ) :
    ∑ b ∈ idealsLe ((2 : ℝ) ^ m), 1 / (absNorm b : ℝ) ≤ A * (1 + 2 * m) := by
  classical
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero, add_zero, mul_one]
    refine le_trans ?_ (by simpa using hA 1 le_rfl)
    calc
      _ ≤ ∑ _ ∈ idealsLe 1, (1 : ℝ) := by
        refine Finset.sum_le_sum fun b _ => ?_
        by_cases hb : absNorm b = 0
        · simp [hb]
        · have hn : (1 : ℝ) ≤ absNorm b := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb
          simpa using one_div_le_one_div_of_le one_pos hn
      _ = _ := by simp
  | succ m ih =>
    let M : ℝ := 2 ^ m
    have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
    have hMp : 0 < M := by linarith
    let S := idealsLe (M * 2) \ idealsLe M
    have hs : idealsLe M ⊆ idealsLe (M * 2) := idealsLe_mono (by linarith)
    have hband : ∑ b ∈ S, 1 / (absNorm b : ℝ) ≤ 2 * A := calc
      _ ≤ ∑ _ ∈ S, 1 / M := by
        apply Finset.sum_le_sum
        intro b hb
        have hn : M < (absNorm b : ℝ) :=
          lt_of_not_ge fun h => (Finset.mem_sdiff.mp hb).2 ((mem_idealsLe hMp.le).mpr h)
        exact one_div_le_one_div_of_le hMp hn.le
      _ = (S.card : ℝ) / M := by simp [div_eq_mul_inv]
      _ ≤ (A * (M * 2)) / M := by
        apply div_le_div_of_nonneg_right _ hMp.le
        exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.sdiff_subset : S ⊆ _))).trans
          (hA _ (by linarith))
      _ = 2 * A := by field_simp
    rw [pow_succ, ← Finset.sum_sdiff hs]
    have hh := add_le_add hband ih
    calc
      _ ≤ 2 * A + A * (1 + 2 * (m : ℝ)) := hh
      _ = _ := by push_cast; ring

/-- The linear ideal count bounds the harmonic sum up to `R X` by any positive power of `D`
when `X ≤ D ^ C₀`. The bound applies to every subset of the norm cutoff. -/
theorem ideal_harmonic_envelope {C₀ δ : ℝ} (hC₀ : 1 ≤ C₀) (hδ : 0 < δ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C ≥ (0 : ℝ), ∀ {D X : ℝ}, 2 ≤ D → 1 ≤ X → X ≤ D ^ C₀ → ∀ s : Finset (Ideal 𝓔),
      (∀ b ∈ s, (absNorm b : ℝ) ≤ R * X) → ∑ b ∈ s, 1 / (absNorm b : ℝ) ≤ C * D ^ δ := by
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  have hA₀ : 0 ≤ A :=
    (Nat.cast_nonneg (idealsLe 1).card).trans (by simpa using hA 1 le_rfl)
  let η := δ / C₀
  have hC₀' : 0 < C₀ := by linarith
  have hη : 0 < η := div_pos hδ hC₀'
  let r : ℝ := 2 ^ η
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hη
  let L := 3 + 2 / (r - 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨A * L * R ^ η, by positivity, ?_⟩
  intro D X hD hX hXD s hs
  obtain ⟨m, hm, htop⟩ := exists_nat_pow_near (one_le_mul_of_one_le_of_one_le hR hX) (by norm_num : (1 : ℝ) < 2)
  have hsub : s ⊆ idealsLe ((2 : ℝ) ^ (m + 1)) := fun b hb =>
    (mem_idealsLe (by positivity)).mpr ((hs b hb).trans htop.le)
  have hb : (m : ℝ) ≤ r ^ m / (r - 1) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith [one_add_mul_sub_le_pow (by linarith : -1 ≤ r) m]
  have hlinear : 1 + 2 * ((m + 1 : ℕ) : ℝ) ≤ L * r ^ m := by
    have h₁ := one_le_pow₀ hr.le (n := m)
    dsimp [L]
    push_cast
    nlinarith [show 2 * (r ^ m / (r - 1)) = 2 / (r - 1) * r ^ m by ring]
  have hp : r ^ m ≤ R ^ η * D ^ δ := calc
    _ = ((2 : ℝ) ^ m) ^ η := by
      dsimp [r]
      rw [← Real.rpow_mul_natCast (by norm_num), mul_comm, Real.rpow_natCast_mul (by norm_num)]
    _ ≤ (R * D ^ C₀) ^ η := Real.rpow_le_rpow (by positivity)
      (hm.trans (mul_le_mul_of_nonneg_left hXD (by linarith))) hη.le
    _ = _ := by
      rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul (by linarith : 0 ≤ D)]
      congr 2
      dsimp [η]
      field_simp
  calc
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ _ := dyadic_harmonic_sum hA (m + 1)
    _ ≤ A * (L * r ^ m) := mul_le_mul_of_nonneg_left hlinear hA₀
    _ = (A * L) * r ^ m := by ring
    _ ≤ (A * L) * (R ^ η * D ^ δ) := mul_le_mul_of_nonneg_left hp (mul_nonneg hA₀ hL)
    _ = _ := by ring

end Masullo.QRH.MeanSquare
