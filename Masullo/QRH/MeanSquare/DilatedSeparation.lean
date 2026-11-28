import Masullo.QRH.MeanSquare.KernelSeparation
import Masullo.QRH.MeanSquare.DualKernel

/-! # Separation of dilated log-product kernels

`exists_separated_le` separates kernels `W₁(x₁) conj W₂(x₂) ψ_ρ(log x₁ + log x₂)` with fixed
tests. In the dual blocks of the first Poisson step the tests are dilated by a factor
depending on the row, `w(ℓ_ρ + log x)`. The Mellin expansion of `w` writes the dilated tests
as integrals of the twisted tests `x^{2πiτ}` against a Schwartz weight, and the row
dependence becomes a unimodular factor `e^{2πiτℓ_ρ}`. The main result is
`exists_dilated_separated_le`.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ComplexConjugate ContDiff Real SchwartzMap ENNReal

namespace Masullo.QRH.MeanSquare

private lemma one_add_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + a ^ n) := by gcongr; linarith

/-- A unit test equal to a positive constant on a given compact interval of `(0, ∞)`. -/
theorem exists_unitTest_eq_const {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (j : ℕ) :
    ∃ (I : TestInterval) (W₀ : ℝ → ℂ) (c₀ : ℝ), 0 < c₀ ∧ UnitTest I j W₀ ∧
      ∀ x ∈ Icc a b, W₀ x = c₀ := by
  let φ : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 2 + a / 4, (b - a) / 2 + a / 2, by linarith, by linarith⟩
  let W₁ : ℝ → ℂ := fun x => (φ x : ℂ)
  have hW₁ : ContDiff ℝ ∞ W₁ := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hW₁c : HasCompactSupport W₁ := φ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hb : ∀ i, ∃ C, ∀ x, ‖iteratedDeriv i W₁ x‖ ≤ C := fun i =>
    (hW₁.continuous_iteratedDeriv i (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (IsCompact.of_isClosed_subset hW₁c (isClosed_tsupport _)
        (tsupport_iteratedDeriv_subset W₁ i))
  choose B hB using hb
  set S : ℝ := 1 + ∑ i ∈ Finset.range (j + 1), max (B i) 0
  have hS : 0 < S := by positivity
  refine ⟨⟨a / 2, b + a / 2, by linarith, by linarith⟩, fun x => (S⁻¹ : ℂ) * W₁ x, S⁻¹,
    inv_pos.mpr hS, ⟨contDiff_const.mul hW₁, ?_, fun i hi x _ => ?_⟩, fun x hx => ?_⟩
  · refine (tsupport_mul_subset_right).trans ?_
    have : tsupport W₁ ⊆ tsupport φ := tsupport_comp_subset Complex.ofReal_zero _
    refine this.trans ?_
    rw [φ.tsupport_eq, Real.closedBall_eq_Icc]
    exact Icc_subset_Icc (by simp only [φ]; linarith) (by simp only [φ]; linarith)
  · rw [iteratedDeriv_const_mul_field, norm_mul, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hS.le), inv_mul_le_iff₀ hS]
    refine (hB i x).trans ((le_max_left (B i) 0).trans ?_)
    have : max (B i) 0 ≤ ∑ i ∈ Finset.range (j + 1), max (B i) 0 :=
      Finset.single_le_sum (f := fun i => max (B i) 0) (fun _ _ => le_max_right _ _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    linarith
  · have h1 : φ x = 1 := φ.one_of_mem_closedBall (by
      rw [Real.closedBall_eq_Icc]
      exact ⟨by simp only [φ]; linarith [hx.1], by simp only [φ]; linarith [hx.2]⟩)
    simp [W₁, h1]


/-- Separation of the dilated kernels `w(ℓ_ρ + log x₁) conj w(ℓ_ρ + log x₂) ψ_ρ(log x₁x₂)`
with `ℓ_ρ ∈ [0, L]`. The interval `I` of the unit tests depends only on `w`, `L` and `j`, and
the hypotheses on the `ψ_ρ` are those of `exists_separated_le`. -/
theorem exists_dilated_separated_le {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) {L : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    ∃ (I : TestInterval) (C : ℝ), 0 ≤ C ∧
      ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c : R → N → ℂ) (x : N → ℝ)
        (ℓ : R → ℝ) (ψ : R → ℝ → ℂ) {A M : ℝ}, 0 ≤ A → 0 ≤ M →
        (∀ n ∈ cols, 0 < x n) → (∀ ρ ∈ rows, ℓ ρ ∈ Icc 0 L) →
        (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * U (x n)‖ ^ 2 ≤ M) →
        (∀ ρ ∈ rows, ContDiff ℝ (2 * j + 2) (ψ ρ)) →
        (∀ ρ ∈ rows, ∀ k ≤ 2 * j + 2, Integrable (iteratedDeriv k (ψ ρ))) →
        (∀ ρ ∈ rows, ∫ v, ‖ψ ρ v‖ ≤ A) →
        (∀ ρ ∈ rows, ∫ v, ‖iteratedDeriv (2 * j + 2) (ψ ρ) v‖ ≤ A) →
        ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
          (w (ℓ ρ + Real.log (x n₁)) * conj (w (ℓ ρ + Real.log (x n₂))) *
            ψ ρ (Real.log (x n₁) + Real.log (x n₂)))‖ ≤ C * A * M := by
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, 0 ≤ R₀ ∧ ∀ t, w t ≠ 0 → |t| ≤ R₀ := by
    obtain ⟨R₀, hR⟩ := hwc.isCompact.isBounded.subset_closedBall 0
    refine ⟨max R₀ 0, le_max_right _ _, fun t ht => ?_⟩
    have := hR (subset_tsupport w ht)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨I, W₀, c₀, hc₀, hW₀, hW₀1⟩ := exists_unitTest_eq_const (Real.exp_pos (-R₀ - L))
    (Real.exp_le_exp.mpr (by linarith [hR₀.1] : -R₀ - L ≤ R₀)) j
  -- The Mellin weight of `w`.
  let F : 𝓢(ℝ, ℂ) := 𝓕 (hwc.toSchwartzMap hw)
  have hinv : ∀ s, w s = ∫ τ, Complex.exp (↑(2 * π * τ * s) * Complex.I) * F τ := by
    have hint : ∀ k ≤ 2, Integrable (iteratedDeriv k w) := fun k _ =>
      (hw.continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
        (IsCompact.of_isClosed_subset hwc (isClosed_tsupport _)
          (tsupport_iteratedDeriv_subset w k))
    exact (fourier_decay_and_inversion le_rfl (hw.of_le (by simp)) hint).2.2
  obtain ⟨Ct, hCt1, hCt⟩ := exists_twistTest_unitTest I j
  obtain ⟨Cs, hCs0, hCs⟩ := exists_separated_le I j
  let g : ℝ → ℝ := fun τ => c₀⁻¹ * (Ct * (1 + |2 * π * τ|) ^ j)
  have hg0 : ∀ τ, 0 ≤ g τ := fun τ => by positivity
  let U : ℝ → ℝ → ℂ := fun τ y =>
    ((Ct * (1 + |2 * π * τ|) ^ j)⁻¹ : ℝ) * twistTest (2 * π * τ) W₀ y
  let V : ℝ → ℝ → ℂ := fun τ y => (c₀⁻¹ : ℂ) * twistTest (2 * π * τ) W₀ y
  have hVU : ∀ τ y, V τ y = g τ * U τ y := fun τ y => by
    have : (0 : ℝ) < Ct * (1 + |2 * π * τ|) ^ j := by positivity
    have hne : ((Ct * (1 + |2 * π * τ|) ^ j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    simp only [V, U, g]
    rw [← mul_assoc]
    congr 1
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv, mul_assoc,
      mul_inv_cancel₀ hne, mul_one]
  have hU : ∀ τ, UnitTest I j (U τ) := fun τ => hCt (2 * π * τ) W₀ hW₀
  have hW₀le : ∀ y, ‖W₀ y‖ ≤ 1 := fun y => by
    by_cases hy : y ∈ tsupport W₀
    · simpa using hW₀.2.2 0 (Nat.zero_le _) y (hW₀.2.1 hy)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]; exact zero_le_one
  have hVle : ∀ τ y, ‖V τ y‖ ≤ c₀⁻¹ := fun τ y => by
    simp only [V, twistTest, norm_mul, norm_logCharacter, mul_one, ← Complex.ofReal_inv,
      Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hc₀.le)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hc₀.le) (hW₀le y)
  have hVc : ∀ y, Continuous fun τ => V τ y := fun y => by
    simp only [V, twistTest, logCharacter]
    fun_prop
  have hFg : Integrable (fun τ => ‖F τ‖ * g τ) := by
    refine ((F.integrable.norm.add
      ((F.integrable_pow_mul volume j).const_mul ((2 * π) ^ j))).const_mul
      (c₀⁻¹ * Ct * 2 ^ j)).mono'
      (by simp only [g]; exact (F.continuous.norm.mul (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hg0 τ))]
    show ‖F τ‖ * g τ ≤ c₀⁻¹ * Ct * 2 ^ j * (‖F τ‖ + (2 * π) ^ j * (‖τ‖ ^ j * ‖F τ‖))
    have h1 := one_add_pow_le |2 * π * τ| (abs_nonneg _) j
    have h2 : |2 * π * τ| ^ j = (2 * π) ^ j * ‖τ‖ ^ j := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), mul_pow]
    rw [h2] at h1
    have hc : 0 ≤ c₀⁻¹ * Ct := by positivity
    calc ‖F τ‖ * g τ = c₀⁻¹ * Ct * (‖F τ‖ * (1 + |2 * π * τ|) ^ j) := by simp only [g]; ring
      _ ≤ c₀⁻¹ * Ct * (‖F τ‖ * (2 ^ j * (1 + (2 * π) ^ j * ‖τ‖ ^ j))) := by gcongr
      _ = _ := by ring
  set Kg := ∫ τ, ‖F τ‖ * g τ
  have hKg : 0 ≤ Kg := integral_nonneg fun τ => mul_nonneg (norm_nonneg _) (hg0 τ)
  refine ⟨I, Cs * Kg ^ 2, by positivity, ?_⟩
  intro R N rows cols c x ℓ ψ A M hA hM hx hℓ hUM hψ hψi hA0 hAn
  let e : ℝ → ℝ → ℂ := fun τ l => Complex.exp (↑(2 * π * τ * l) * Complex.I)
  have he : ∀ τ l, ‖e τ l‖ = 1 := fun τ l => Complex.norm_exp_ofReal_mul_I _
  let a : R → N → ℝ → ℂ := fun ρ n τ => F τ * e τ (ℓ ρ) * V τ (x n)
  have hrep : ∀ ρ ∈ rows, ∀ n ∈ cols, w (ℓ ρ + Real.log (x n)) = ∫ τ, a ρ n τ := by
    intro ρ hρ n hn
    have hpt : ∀ τ, a ρ n τ = ((c₀⁻¹ : ℂ) * W₀ (x n)) *
        (Complex.exp (↑(2 * π * τ * (ℓ ρ + Real.log (x n))) * Complex.I) * F τ) := fun τ => by
      simp only [a, e, V, twistTest, logCharacter]
      rw [show (↑(2 * π * τ * (ℓ ρ + Real.log (x n))) * Complex.I : ℂ) =
        ↑(2 * π * τ * ℓ ρ) * Complex.I + ↑(Real.log (x n)) * (↑(2 * π * τ) * Complex.I) by
          push_cast; ring, Complex.exp_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, ← hinv]
    by_cases h0 : w (ℓ ρ + Real.log (x n)) = 0
    · rw [h0, mul_zero]
    · have hmem : x n ∈ Icc (Real.exp (-R₀ - L)) (Real.exp R₀) := by
        have h1 := hR₀.2 _ h0
        have h2 := hℓ ρ hρ
        rw [abs_le] at h1
        have hxn := hx n hn
        constructor
        · rw [← Real.exp_log hxn]; exact Real.exp_le_exp.mpr (by linarith [h2.1, h2.2, h1.1])
        · rw [← Real.exp_log hxn]; exact Real.exp_le_exp.mpr (by linarith [h2.1, h1.2])
      rw [hW₀1 _ hmem, inv_mul_cancel₀ (by exact_mod_cast hc₀.ne'), one_mul]
  have hacont : ∀ ρ n, Continuous (a ρ n) := fun ρ n => by
    simp only [a, e]
    exact (F.continuous.mul (by fun_prop)).mul (hVc _)
  have hale : ∀ ρ n τ, ‖a ρ n τ‖ ≤ ‖F τ‖ * c₀⁻¹ := fun ρ n τ => by
    simp only [a, norm_mul, he, mul_one]
    exact mul_le_mul_of_nonneg_left (hVle _ _) (norm_nonneg _)
  have haint : ∀ ρ n, Integrable (a ρ n) := fun ρ n =>
    (F.integrable.norm.mul_const c₀⁻¹).mono' (hacont ρ n).aestronglyMeasurable
      (Filter.Eventually.of_forall (hale ρ n))
  have haint' : ∀ ρ n, Integrable (fun τ => conj (a ρ n τ)) := fun ρ n =>
    (F.integrable.norm.mul_const c₀⁻¹).mono'
      (Complex.continuous_conj.comp (hacont ρ n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by rw [Complex.norm_conj]; exact hale ρ n τ)
  let Bv : R → ℝ → ℝ → ℂ := fun ρ τ₁ τ₂ => ∑ n₁ ∈ cols, ∑ n₂ ∈ cols,
    c ρ n₁ * conj (c ρ n₂) *
      (V τ₁ (x n₁) * conj (V τ₂ (x n₂)) * ψ ρ (Real.log (x n₁) + Real.log (x n₂)))
  let H : R → ℝ → ℝ → ℂ := fun ρ τ₁ τ₂ =>
    F τ₁ * e τ₁ (ℓ ρ) * conj (F τ₂ * e τ₂ (ℓ ρ)) * Bv ρ τ₁ τ₂
  have hT : ∀ ρ ∈ rows, (∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
      (w (ℓ ρ + Real.log (x n₁)) * conj (w (ℓ ρ + Real.log (x n₂))) *
        ψ ρ (Real.log (x n₁) + Real.log (x n₂)))) = ∫ τ₁, ∫ τ₂, H ρ τ₁ τ₂ := by
    intro ρ hρ
    let K : N → N → ℂ := fun n₁ n₂ =>
      c ρ n₁ * conj (c ρ n₂) * ψ ρ (Real.log (x n₁) + Real.log (x n₂))
    have hin : ∀ n₁ n₂ τ₁, ∫ τ₂, K n₁ n₂ * (a ρ n₁ τ₁ * conj (a ρ n₂ τ₂)) =
        K n₁ n₂ * a ρ n₁ τ₁ * ∫ τ₂, conj (a ρ n₂ τ₂) := fun n₁ n₂ τ₁ => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun τ₂ => by ring)
    have h1 : ∀ n₁ ∈ cols, ∀ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
        (w (ℓ ρ + Real.log (x n₁)) * conj (w (ℓ ρ + Real.log (x n₂))) *
          ψ ρ (Real.log (x n₁) + Real.log (x n₂))) =
        ∫ τ₁, ∫ τ₂, K n₁ n₂ * (a ρ n₁ τ₁ * conj (a ρ n₂ τ₂)) := by
      intro n₁ h₁ n₂ h₂
      rw [integral_congr_ae (Filter.Eventually.of_forall (hin n₁ n₂)), integral_mul_const,
        integral_const_mul, hrep ρ hρ n₁ h₁, hrep ρ hρ n₂ h₂, integral_conj]
      simp only [K]
      ring
    have hint1 : ∀ n₁ n₂, Integrable fun τ₁ => ∫ τ₂, K n₁ n₂ * (a ρ n₁ τ₁ * conj (a ρ n₂ τ₂)) :=
      fun n₁ n₂ => (((haint ρ n₁).const_mul (K n₁ n₂)).mul_const
        (∫ τ₂, conj (a ρ n₂ τ₂))).congr (Filter.Eventually.of_forall fun τ₁ =>
          (hin n₁ n₂ τ₁).symm)
    have hint2 : ∀ n₁ n₂ τ₁, Integrable fun τ₂ => K n₁ n₂ * (a ρ n₁ τ₁ * conj (a ρ n₂ τ₂)) :=
      fun n₁ n₂ τ₁ => ((haint' ρ n₂).const_mul (K n₁ n₂ * a ρ n₁ τ₁)).congr
        (Filter.Eventually.of_forall fun τ₂ => by ring)
    rw [Finset.sum_congr rfl fun n₁ h₁ => Finset.sum_congr rfl fun n₂ h₂ => h1 n₁ h₁ n₂ h₂]
    rw [Finset.sum_congr rfl fun n₁ _ => (integral_finsetSum _ fun n₂ _ => hint1 n₁ n₂).symm,
      ← integral_finsetSum _ fun n₁ _ => integrable_finsetSum _ fun n₂ _ => hint1 n₁ n₂]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ₁ => ?_)
    simp only
    rw [Finset.sum_congr rfl fun n₁ _ => (integral_finsetSum _ fun n₂ _ => hint2 n₁ n₂ τ₁).symm,
      ← integral_finsetSum _ fun n₁ _ => integrable_finsetSum _ fun n₂ _ => hint2 n₁ n₂ τ₁]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ₂ => ?_)
    simp only [H, Bv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    simp only [K, a, map_mul]
    ring
  have hBv : ∀ ρ τ₁ τ₂, Bv ρ τ₁ τ₂ = ((g τ₁ * g τ₂ : ℝ) : ℂ) * ∑ n₁ ∈ cols, ∑ n₂ ∈ cols,
      c ρ n₁ * conj (c ρ n₂) *
        (U τ₁ (x n₁) * conj (U τ₂ (x n₂)) * ψ ρ (Real.log (x n₁) + Real.log (x n₂))) := by
    intro ρ τ₁ τ₂
    simp only [Bv, hVU, Finset.mul_sum, map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    push_cast
    ring
  have hBsum : ∀ τ₁ τ₂, ∑ ρ ∈ rows, ‖Bv ρ τ₁ τ₂‖ ≤ g τ₁ * g τ₂ * (Cs * A * M) := by
    intro τ₁ τ₂
    have hgg : 0 ≤ g τ₁ * g τ₂ := mul_nonneg (hg0 τ₁) (hg0 τ₂)
    simp only [hBv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hgg]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (hCs rows cols c x (U τ₁) (U τ₂) ψ hA hM (hU τ₁) (hU τ₂) hUM hψ hψi hA0 hAn) hgg
  have hBvc : ∀ ρ, Continuous (Function.uncurry (Bv ρ)) := by
    intro ρ
    simp only [Bv, V, twistTest, logCharacter]
    fun_prop
  let G : R → ℝ → ℝ → ℝ≥0∞ := fun ρ τ₁ τ₂ => ENNReal.ofReal (‖F τ₁‖ * ‖F τ₂‖ * ‖Bv ρ τ₁ τ₂‖)
  have hGm : ∀ ρ, Measurable (Function.uncurry (G ρ)) := fun ρ =>
    ENNReal.measurable_ofReal.comp (Continuous.measurable
      (f := fun p : ℝ × ℝ => ‖F p.1‖ * ‖F p.2‖ * ‖Bv ρ p.1 p.2‖)
      (((F.continuous.comp continuous_fst).norm.mul
        (F.continuous.comp continuous_snd).norm).mul (hBvc ρ).norm))
  have hTle : ∀ ρ ∈ rows, ENNReal.ofReal ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
      (w (ℓ ρ + Real.log (x n₁)) * conj (w (ℓ ρ + Real.log (x n₂))) *
        ψ ρ (Real.log (x n₁) + Real.log (x n₂)))‖ ≤ ∫⁻ τ₁, ∫⁻ τ₂, G ρ τ₁ τ₂ := by
    intro ρ hρ
    rw [hT ρ hρ, ofReal_norm]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun τ₁ => ?_)
    refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun τ₂ => ?_)
    rw [← ofReal_norm]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    simp only [H, norm_mul, Complex.norm_conj, he, mul_one]
  have hpt : ∀ τ₁ τ₂, ∑ ρ ∈ rows, G ρ τ₁ τ₂ ≤
      ENNReal.ofReal (‖F τ₁‖ * g τ₁) * ENNReal.ofReal (Cs * A * M) *
        ENNReal.ofReal (‖F τ₂‖ * g τ₂) := by
    intro τ₁ τ₂
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ← ENNReal.ofReal_mul
      (mul_nonneg (norm_nonneg _) (hg0 τ₁)), ← ENNReal.ofReal_mul (by
        exact mul_nonneg (mul_nonneg (norm_nonneg _) (hg0 τ₁)) (by positivity))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.mul_sum]
    calc ‖F τ₁‖ * ‖F τ₂‖ * ∑ ρ ∈ rows, ‖Bv ρ τ₁ τ₂‖
        ≤ ‖F τ₁‖ * ‖F τ₂‖ * (g τ₁ * g τ₂ * (Cs * A * M)) :=
          mul_le_mul_of_nonneg_left (hBsum τ₁ τ₂) (by positivity)
      _ = _ := by ring
  have hKgl : ∫⁻ τ, ENNReal.ofReal (‖F τ‖ * g τ) = ENNReal.ofReal Kg :=
    (ofReal_integral_eq_lintegral_ofReal hFg
      (Filter.Eventually.of_forall fun τ => mul_nonneg (norm_nonneg _) (hg0 τ))).symm
  have htot : ENNReal.ofReal (∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
      (w (ℓ ρ + Real.log (x n₁)) * conj (w (ℓ ρ + Real.log (x n₂))) *
        ψ ρ (Real.log (x n₁) + Real.log (x n₂)))‖) ≤
      ENNReal.ofReal (Cs * Kg ^ 2 * A * M) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
    calc _ ≤ ∑ ρ ∈ rows, ∫⁻ τ₁, ∫⁻ τ₂, G ρ τ₁ τ₂ := Finset.sum_le_sum hTle
      _ = ∫⁻ τ₁, ∑ ρ ∈ rows, ∫⁻ τ₂, G ρ τ₁ τ₂ :=
          (lintegral_finsetSum _ fun ρ _ => (hGm ρ).lintegral_prod_right').symm
      _ = ∫⁻ τ₁, ∫⁻ τ₂, ∑ ρ ∈ rows, G ρ τ₁ τ₂ := lintegral_congr fun τ₁ =>
          (lintegral_finsetSum _ fun ρ _ => (hGm ρ).of_uncurry_left).symm
      _ ≤ ∫⁻ τ₁, ∫⁻ τ₂, ENNReal.ofReal (‖F τ₁‖ * g τ₁) * ENNReal.ofReal (Cs * A * M) *
            ENNReal.ofReal (‖F τ₂‖ * g τ₂) :=
          lintegral_mono fun τ₁ => lintegral_mono fun τ₂ => hpt τ₁ τ₂
      _ = ENNReal.ofReal Kg * ENNReal.ofReal (Cs * A * M) * ENNReal.ofReal Kg := by
          simp_rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top), hKgl]
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hKgl]
      _ = _ := by
          rw [← ENNReal.ofReal_mul hKg, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at htot
  linarith

end Masullo.QRH.MeanSquare
