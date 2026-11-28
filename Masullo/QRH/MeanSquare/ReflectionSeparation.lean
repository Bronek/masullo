import Masullo.QRH.MeanSquare.ReflectionKernel
import Masullo.QRH.MeanSquare.ReflectionSieve

/-! # Mellin separation on a dyadic block of reflected coefficients -/

noncomputable section

open Complex MeasureTheory Set Finset NumberField Ideal

namespace Masullo.QRH.MeanSquare

/-- On a block with lower scale `z₀`, integrate on the line zero or three.
The Mellin power of the normalized column norm is then bounded by one,
and the row factor carries the decay in `z₀`. -/
theorem reflectionKernel_separate (hΓ : DLMFGammaVertical) (I : TestInterval) :
    ∃ C ≥ (0 : ℝ), ∀ W : ℝ → ℂ, UnitTest I 14 W → ∀ z₀ : ℝ, 0 < z₀ →
      ∃ P Q : ℝ → ℝ → ℂ,
        (∀ x ≥ (1 : ℝ), Continuous (P x) ∧ ∀ y, ‖P x y‖ ≤ 1) ∧
        (∀ r ≥ z₀, Continuous (Q r) ∧ ∀ y,
          ‖Q r y‖ ≤ C / (1+z₀)^3 / (1+|y|)^2) ∧
        ∀ x ≥ (1 : ℝ), ∀ r ≥ z₀, reflectionKernel W 0 0 (x*r) =
          ∫ y : ℝ, Q r y * P x y := by
  obtain ⟨B,hB,hbound⟩ := norm_reflectionKernelAmplitude hΓ (a := 0) (b := 3) (by norm_num) 0 I
  let S := (2 * Real.pi)^4
  have hS : (1 : ℝ) ≤ S := one_le_pow₀ (by linarith [Real.pi_gt_three])
  refine ⟨8*B,by positivity, fun W hw z₀ hz => ?_⟩
  let σ : ℝ := if z₀ ≤ 1 then 0 else 3
  have hσ : σ ∈ Icc (0 : ℝ) 3 := by dsimp [σ]; split <;> norm_num
  let t := fun y : ℝ => (σ : ℂ) + y * Complex.I
  let P := fun (x y : ℝ) => (x : ℂ) ^ (-t y)
  let Q := fun (r y : ℝ) => (reflectionKernelAmplitude W 0 (t y) * ((S*r : ℝ) : ℂ) ^ (-t y)) /
    (2 * Real.pi)
  have ht : Continuous t := by dsimp [t]; fun_prop
  have hpcont {x : ℝ} (hx : 0 < x) : Continuous (P x) := by
    exact ht.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have htre (y : ℝ) : (t y).re = σ := by simp [t]
  have htim (y : ℝ) : (t y).im = y := by simp [t]
  refine ⟨P,Q,fun x hx => ⟨hpcont (by linarith), fun y => ?_⟩, fun r hr => ⟨?_, fun y => ?_⟩,
    fun x hx r hr => ?_⟩
  · rw [show ‖P x y‖ = x ^
      (-σ) by simp [P, norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x), htre]]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hσ.1)
  · apply Continuous.div_const
    apply Continuous.mul
    · exact continuous_iff_continuousAt.mpr fun y =>
        (differentiableAt_reflectionKernelAmplitude hw 0
          (t := t y) (by rw [htre]; linarith [hσ.1])).continuousAt.comp ht.continuousAt
    · exact hpcont (x := S*r) (by have := hz.trans_le hr; positivity)
  · have hSr : 0 < S*r := mul_pos (zero_lt_one.trans_le hS) (hz.trans_le hr)
    have hker : (S*r) ^ (-σ) * (1+z₀)^3 ≤ 8 := by
      dsimp only [σ]
      split_ifs with hs
      · rw [neg_zero, Real.rpow_zero, one_mul]
        calc
          _ ≤ (2:ℝ)^3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
          _ = 8 := by norm_num
      · rw [Real.rpow_neg hSr.le, Real.rpow_ofNat, inv_mul_eq_div]
        apply (div_le_iff₀ (pow_pos hSr 3)).mpr
        have hs' := le_mul_of_one_le_left (hz.trans_le hr).le hS
        have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1+z₀) (by linarith : 1+z₀ ≤ 2*(S*r)) 3
        linarith [show (2*(S*r))^3 = 8*(S*r)^3 by ring]
    have hA := hbound W (by norm_num; exact hw) (t y) (htre y ▸ hσ)
    rw [htim] at hA
    simp only [Q, norm_div, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, norm_cpow_eq_rpow_re_of_pos hSr, neg_re, htre]
    have hπ : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
    apply (div_le_self (by positivity) hπ).trans
    rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    calc
      _ = (‖reflectionKernelAmplitude W 0 (t y)‖ * (1+|y|)^2) * ((S*r)^(-σ)*(1+z₀)^3) := by ring
      _ ≤ B * 8 := mul_le_mul hA hker (by positivity) hB
      _ = _ := by ring
  · have hx₀ : 0 < x := by linarith
    have hr₀ := hz.trans_le hr
    have h₁ := reflectionKernel_shift hΓ hσ.1 (by norm_num) 0
      (I := I) (W := W) (hw.of_le (by
        have hceil : ⌈4 * max σ 0⌉₊ ≤ 12 :=
          Nat.ceil_le.mpr (by rw [max_eq_left hσ.1]; norm_num; linarith [hσ.2])
        omega)) (mul_pos hx₀ hr₀)
    rw [h₁, reflectionKernel, ← integral_div]
    apply integral_congr_ae (ae_of_all _ fun y => ?_)
    have hprod : (S * (x*r) : ℝ) = (S*r) * x := by ring
    change (reflectionKernelAmplitude W 0 (t y) * ((S*(x*r) : ℝ) : ℂ) ^ (-t y)) /
      (2*Real.pi) = Q r y * P x y
    rw [hprod, Complex.ofReal_mul, Complex.ofReal_mul_cpow (mul_nonneg (zero_lt_one.trans_le
      hS).le hr₀.le)]
    dsimp only [P,Q]
    ring

namespace ReflectionSieve

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The reflected block with its kernel evaluated at the product of the row scale
and the normalized column norm. -/
def kernelBlock (W : ℝ → ℂ) (V : ℝ) (S T : Finset (Ideal 𝓔))
    (c d : Ideal 𝓔 → Ideal 𝓔 → ℂ) (u : Ideal 𝓔 → Ideal 𝓔 → ℝ) (k : Ideal 𝓔) : ℂ :=
  ∑ b ∈ T, (absNorm b : ℂ)⁻¹ * ∑ n ∈ S,
    (d b k * (c b n / Real.sqrt (absNorm n)) * primaryQuadraticSymbol n k) *
      reflectionKernel W 0 0 ((absNorm n / V) * u b k)

/-- Estimate (7) for the original product kernel in a dyadic reflected block.
The cube and row may affect the scale, while the coefficient of the squarefree
column is independent of the row. -/
theorem kernel_dyadic_block (quad : DeloupTuraevTheorem1)
    (sieve : QuadraticSieve primaryQuadraticSymbol) (hΓ : DLMFGammaVertical)
    (I : TestInterval) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C ≥ (0 : ℝ), ∀ W : ℝ → ℂ, UnitTest I 14 W → ∀ {K V B Y a : ℝ},
    1 ≤ K → 1 ≤ V → 1 ≤ B → 0 < Y → 0 ≤ a →
    ∀ (m : ℤ) (g : QuadraticFamilyClass) (R S T : Finset (Ideal 𝓔)),
      R ⊆ sieveIdeals (span {6}) K → S ⊆ dyadicSieveIdeals (span {6}) V →
      (∀ k ∈ R, familyClass k = g) → (∀ b ∈ T, (absNorm b : ℝ) ∈ Ico B (2 * B)) →
    ∀ (c d : Ideal 𝓔 → Ideal 𝓔 → ℂ) (u : Ideal 𝓔 → Ideal 𝓔 → ℝ),
      (∀ b ∈ T, ∀ n ∈ S, ‖c b n‖ ≤ a) → (∀ b ∈ T, ∀ k ∈ R, ‖d b k‖ ≤ 1) →
      (∀ b ∈ T, ∀ k ∈ R, kernelScale m V B Y ≤ u b k) →
      (3 : ℝ) ^ (-(m : ℝ) / 3) * Real.sqrt (∑ k ∈ R, ‖kernelBlock W V S T c d u k‖ ^ 2) ≤
        C * a * (3 : ℝ) ^ (-(m : ℝ) / 3) * (K * V) ^ ρ *
          (Real.sqrt K + Real.sqrt V) / (1 + kernelScale m V B Y) ^ 3 := by
  classical
  obtain ⟨C,hC,hblock⟩ := separated_dyadic_block quad sieve hρ
  obtain ⟨H,hH,hsep⟩ := reflectionKernel_separate hΓ I
  refine ⟨C*H,by positivity,?_⟩
  intro W hw K V B Y a hK hV hB hY ha m g R S T hR hS hg hT c d u hc hd hu
  let z := kernelScale m V B Y
  have hz : 0 < z := by dsimp [z,kernelScale]; positivity
  obtain ⟨P,Q,hP,hQ,he⟩ := hsep W hw z hz
  let x (n : Ideal 𝓔) := (absNorm n : ℝ) / V
  have hx (n) (hn : n ∈ S) : 1 ≤ x n := (one_le_div (by linarith)).mpr (mem_filter.mp (hS hn)).2.1
  let Z b t n := c b n * P (x n) t
  let A b t k := d b k * Q (u b k) t
  have hZ b (hb : b ∈ T) t n (hn : n ∈ S) : ‖Z b t n‖ ≤ a := by
    rw [show ‖Z b t n‖ = _ by exact norm_mul ..]
    exact (mul_le_mul (hc b hb n hn) ((hP _ (hx n hn)).2 t) (norm_nonneg _) ha).trans_eq (mul_one a)
  have hA b (hb : b ∈ T) t k (hk : k ∈ R) :
      ‖A b t k‖ ≤ H/(1+z)^3/(1+|t|)^2 := by
    dsimp [A]
    rw [norm_mul]
    exact (mul_le_mul (hd b hb k hk) ((hQ _ (hu b hb k hk)).2 t) (norm_nonneg _)
      (by norm_num)).trans_eq (one_mul _)
  let w b k n := d b k * (c b n / (Real.sqrt (absNorm n) : ℂ)) * primaryQuadraticSymbol n k
  let f b k n t := w b k n * (Q (u b k) t * P (x n) t)
  have hi b (hb : b ∈ T) k (hk : k ∈ R) n (hn : n ∈ S) : Integrable (f b k n) := by
    apply Integrable.const_mul
    apply ((integrable_inv_one_add_sq.const_mul (H/(1+z)^3))).mono'
    · exact ((hQ _ (hu b hb k hk)).1.mul (hP _ (hx n hn)).1).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro t
      rw [norm_mul]
      calc
        _ ≤ H/(1+z)^3/(1+|t|)^2 * 1 := mul_le_mul ((hQ _ (hu b hb k hk)).2 t)
          ((hP _ (hx n hn)).2 t) (norm_nonneg _) (by positivity)
        _ ≤ _ := by
          rw [mul_one, ← div_eq_mul_inv]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [abs_nonneg t,sq_abs t]
  have hs b k t : A b t k * column S (Z b) t k = ∑ n ∈ S, f b k n t := by
    rw [column, Finset.mul_sum]
    apply sum_congr rfl
    intro n _
    dsimp [A,Z,f,w]
    ring
  have hI b (hb : b ∈ T) k (hk : k ∈ R) :
      Integrable (fun t => A b t k * column S (Z b) t k) := by
    simp_rw [hs]
    exact integrable_finsetSum S (hi b hb k hk)
  have hval k (hk : k ∈ R) : block S T Z A k = kernelBlock W V S T c d u k := by
    apply sum_congr rfl
    intro b hb
    apply congrArg ((absNorm b : ℂ)⁻¹ * ·)
    simp_rw [hs]
    rw [integral_finsetSum S (hi b hb k hk)]
    apply sum_congr rfl
    intro n hn
    rw [he _ (hx n hn) _ (hu b hb k hk), ← integral_const_mul]
  have h := hblock hK hV hB hY ha hH m g R S T hR hS hg hT Z A hZ hA hI
  rw [Finset.sum_congr rfl (fun k hk => congrArg (fun v : ℂ => ‖v‖^2) (hval k hk))] at h
  convert h using 1
  ring

end ReflectionSieve

end Masullo.QRH.MeanSquare
