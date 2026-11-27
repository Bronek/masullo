import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The Möbius mollifier

`partialZeta X s = ∑_{n ≤ X} n^{-s}` and `mollifier U s = ∑_{d ≤ U} μ(d) d^{-s}`. Their product
minus one is a Dirichlet polynomial of length `U X` whose coefficients `mollCoeff U X n` vanish for
`n ≤ U ≤ X` and are bounded by the number of divisors. With `∑ τ(n)² n^{-α} ≤ (∑ m^{-α})⁴`, the
weighted square sum of the coefficients on `Re s ≥ 1/2 + δ` is at most `U^{-δ}` times a constant.

Part of a Carlson-type mean-square zero-density argument due to OpenAI Codex (E36),
formalised by Claude.
-/

namespace WeilExplicit

open Complex Finset

/-- Truncated Dirichlet series of zeta. -/
noncomputable def partialZeta (X : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Icc 1 X, (n : ℂ) ^ (-s)

/-- The Möbius mollifier of length `U`. -/
noncomputable def mollifier (U : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 U, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s)

/-- Coefficients of `partialZeta X * mollifier U - 1`. -/
noncomputable def mollCoeff (U X n : ℕ) : ℂ :=
  (∑ p ∈ Icc 1 U ×ˢ Icc 1 X with p.1 * p.2 = n, (ArithmeticFunction.moebius p.1 : ℂ)) -
    if n = 1 then 1 else 0

theorem partialZeta_mul_mollifier_sub_one {U X : ℕ} (hU : 1 ≤ U) (hX : 1 ≤ X) (s : ℂ) :
    partialZeta X s * mollifier U s - 1 =
      ∑ n ∈ Icc 1 (U * X), mollCoeff U X n * (n : ℂ) ^ (-s) := by
  have hmaps : ∀ p ∈ Icc 1 U ×ˢ Icc 1 X, p.1 * p.2 ∈ Icc 1 (U * X) := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_product.mp hp
    obtain ⟨a1, a2⟩ := mem_Icc.mp h1
    obtain ⟨b1, b2⟩ := mem_Icc.mp h2
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul a2 b2⟩
  have hprod : partialZeta X s * mollifier U s =
      ∑ p ∈ Icc 1 U ×ˢ Icc 1 X, (ArithmeticFunction.moebius p.1 : ℂ) *
        ((p.1 * p.2 : ℕ) : ℂ) ^ (-s) := by
    rw [partialZeta, mollifier, mul_comm, sum_mul_sum, sum_product]
    refine sum_congr rfl fun d _ ↦ sum_congr rfl fun e _ ↦ ?_
    rw [Nat.cast_mul, natCast_mul_natCast_cpow]; ring
  have hone : (1 : ℂ) = ∑ n ∈ Icc 1 (U * X), (if n = 1 then (1 : ℂ) else 0) * (n : ℂ) ^ (-s) := by
    rw [sum_eq_single 1 (fun n _ hn ↦ by simp [hn]) (fun h ↦ absurd
      (mem_Icc.mpr ⟨le_rfl, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))⟩) h)]
    simp
  rw [hprod, hone, ← sum_fiberwise_of_maps_to hmaps, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [mollCoeff, sub_mul, sum_mul]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  rw [(mem_filter.mp hp).2]

private theorem filter_eq_antidiagonal {U X n : ℕ} (hn : 1 ≤ n) (hnU : n ≤ U) (hUX : U ≤ X) :
    {p ∈ Icc 1 U ×ˢ Icc 1 X | p.1 * p.2 = n} = n.divisorsAntidiagonal := by
  ext ⟨a,b⟩
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · grind
  · rintro ⟨rfl, hp⟩
    have ha : 0 < a := by grind
    have hb : 0 < b := by grind
    exact ⟨⟨⟨ha, (Nat.le_mul_of_pos_right a hb).trans hnU⟩, hb,
      (Nat.le_mul_of_pos_left b ha).trans (hnU.trans hUX)⟩, rfl⟩

theorem mollCoeff_eq_zero {U X n : ℕ} (hn : 1 ≤ n) (hnU : n ≤ U) (hUX : U ≤ X) :
    mollCoeff U X n = 0 := by
  rw [mollCoeff, filter_eq_antidiagonal hn hnU hUX, sub_eq_zero,
      Nat.sum_divisorsAntidiagonal (fun d _ ↦ (ArithmeticFunction.moebius d : ℂ))]
  have h := DFunLike.congr_fun (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ)) n
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] using h

theorem norm_mollCoeff_le {U X n : ℕ} (hn : 1 < n) :
    ‖mollCoeff U X n‖ ≤ (n.divisors.card : ℝ) := by
  rw [mollCoeff, if_neg hn.ne', sub_zero]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p ∈ Icc 1 U ×ˢ Icc 1 X with p.1 * p.2 = n, ‖(ArithmeticFunction.moebius p.1 : ℂ)‖
      ≤ ∑ p ∈ Icc 1 U ×ˢ Icc 1 X with p.1 * p.2 = n, (1 : ℝ) := by
        refine sum_le_sum fun p _ ↦ ?_
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = (({p ∈ Icc 1 U ×ˢ Icc 1 X | p.1 * p.2 = n}).card : ℝ) := by simp
    _ ≤ (n.divisorsAntidiagonal.card : ℝ) := by
        refine Nat.cast_le.mpr (card_le_card fun p hp ↦ ?_)
        exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hp).2, by omega⟩
    _ = (n.divisors.card : ℝ) := by rw [← Nat.map_div_right_divisors, card_map]

section
open ArithmeticFunction

private theorem divisors_card_submul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a*b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  let S := a.divisors ×ˢ b.divisors
  have h : (a*b).divisors ⊆ S.image (fun p ↦ p.1 * p.2) := by
    intro d hd
    obtain ⟨x, y, hx, hy, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hd)
    exact mem_image.mpr ⟨(x,y), mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hx, ha⟩, Nat.mem_divisors.mpr ⟨hy, hb⟩⟩, rfl⟩
  exact (card_le_card h).trans (card_image_le.trans (by simp [S]))

private theorem sum_conv_le (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (K : ℕ) :
    ∑ n ∈ Ioc 0 K, (f * f) n ≤ (∑ n ∈ Ioc 0 K, f n)^2 := by
  rw [sum_Ioc_mul_eq_sum_prod_filter, sq, sum_mul_sum,
    ← sum_product (f := fun p : ℕ × ℕ ↦ f p.1 * f p.2)]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ ↦ mul_nonneg (hf _) (hf _)

/-- The finite weighted divisor-square sum is bounded by the fourth power of the partial sum. -/
theorem sum_card_divisors_sq_le (K : ℕ) (α : ℝ) :
    ∑ n ∈ Icc 1 K, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-α) ≤
      (∑ m ∈ Icc 1 K, (m : ℝ) ^ (-α)) ^ 4 := by
  let w : ArithmeticFunction ℝ := ⟨fun n ↦ if n = 0 then 0 else (n : ℝ)^(-α), by simp⟩
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; split <;> positivity
  have hmul {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) : w p.1 * w p.2 = w n := by
    obtain ⟨rfl, h⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    simp [w, left_ne_zero_of_mul h, right_ne_zero_of_mul h, h, Real.mul_rpow, Nat.cast_nonneg]
  have hcard (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, card_map]
  have hww (n : ℕ) : (w*w) n = n.divisors.card * w n := by
    simp only [ArithmeticFunction.mul_apply, sum_congr rfl (fun p hp ↦ hmul hp), sum_const,
      nsmul_eq_mul, hcard]
  have nn (n : ℕ) : 0 ≤ (w*w) n := hww n ▸ mul_nonneg (Nat.cast_nonneg _) (hw n)
  have hI : Icc 1 K = Ioc 0 K := by ext; simp [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  rw [hI]
  have hn (n : ℕ) (hn : n ∈ Ioc 0 K) : w n = (n : ℝ)^(-α) := by simp [w, (mem_Ioc.mp hn).1.ne']
  simp_rw [← sum_congr rfl hn]
  calc ∑ n ∈ Ioc 0 K, (n.divisors.card : ℝ)^2 * (n : ℝ)^(-α)
      ≤ ∑ n ∈ Ioc 0 K, ((w*w)*(w*w)) n := by
        refine sum_le_sum fun n h ↦ ?_
        rw [← hn n h, ArithmeticFunction.mul_apply]
        calc (n.divisors.card : ℝ)^2 * w n
            = ∑ _p ∈ n.divisorsAntidiagonal, n.divisors.card * w n := by
               rw [sum_const, nsmul_eq_mul, hcard]; ring
             _ ≤ _ := sum_le_sum fun p hp ↦ by
               obtain ⟨hprod, hpos⟩ := Nat.mem_divisorsAntidiagonal.mp hp
               rw [hww, hww, mul_mul_mul_comm, hmul hp]
               apply mul_le_mul_of_nonneg_right _ (hw n)
               rw [← hprod] at hpos ⊢
               exact_mod_cast
                divisors_card_submul (left_ne_zero_of_mul hpos) (right_ne_zero_of_mul hpos)
    _ ≤ _ := (sum_conv_le (w*w) nn K).trans <|
      (pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ nn _) (sum_conv_le w hw K) 2).trans_eq (by ring)

end

/-- The constant `(∑ m^{-(1+δ)})⁴` bounding divisor-square sums. -/
noncomputable def divisorConst (δ : ℝ) : ℝ := (∑' m : ℕ, (m : ℝ) ^ (-(1 + δ))) ^ 4

/-- The weighted square sum of the mollified coefficients on `Re s ≥ 1/2 + δ`. -/
theorem sum_mollCoeff_sq_le {U X : ℕ} (hU : 1 ≤ U) (hUX : U ≤ X) {δ u : ℝ} (hδ : 0 < δ)
    (hu : 1 / 2 + δ ≤ u) :
    ∑ n ∈ Icc 1 (U * X), ‖mollCoeff U X n‖ ^ 2 * (n : ℝ) ^ (-(2 * u)) ≤
      (U : ℝ) ^ (-δ) * divisorConst δ := by
  have hsum : Summable fun m : ℕ ↦ (m : ℝ) ^ (-(1 + δ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hpart : ∑ m ∈ Icc 1 (U * X), (m : ℝ) ^ (-(1 + δ)) ≤ ∑' m : ℕ, (m : ℝ) ^ (-(1 + δ)) :=
    hsum.sum_le_tsum _ fun m _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  calc ∑ n ∈ Icc 1 (U * X), ‖mollCoeff U X n‖ ^ 2 * (n : ℝ) ^ (-(2 * u))
      ≤ ∑ n ∈ Icc 1 (U * X), (U : ℝ) ^ (-δ) *
          (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(1 + δ))) := by
        refine sum_le_sum fun n hn ↦ ?_
        have hn1 := (mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        by_cases hnU : n ≤ U
        · rw [mollCoeff_eq_zero hn1 hnU hUX]
          calc ‖(0 : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * u)) = 0 := by simp
            _ ≤ _ := by positivity
        push Not at hnU
        have hUn : (U : ℝ) ≤ n := by exact_mod_cast hnU.le
        have h1 : ‖mollCoeff U X n‖ ^ 2 ≤ ((n.divisors.card : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_mollCoeff_le (by omega)) 2
        have h2 : (n : ℝ) ^ (-(2 * u)) ≤ (U : ℝ) ^ (-δ) * (n : ℝ) ^ (-(1 + δ)) := by
          calc (n : ℝ) ^ (-(2 * u)) ≤ (n : ℝ) ^ (-δ + -(1 + δ)) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
            _ = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (-(1 + δ)) := Real.rpow_add hn0 _ _
            _ ≤ (U : ℝ) ^ (-δ) * (n : ℝ) ^ (-(1 + δ)) := by
                exact mul_le_mul_of_nonneg_right
                  (Real.rpow_le_rpow_of_nonpos hU0 hUn (by linarith)) (by positivity)
        calc ‖mollCoeff U X n‖ ^ 2 * (n : ℝ) ^ (-(2 * u))
            ≤ ((n.divisors.card : ℝ)) ^ 2 * ((U : ℝ) ^ (-δ) * (n : ℝ) ^ (-(1 + δ))) := by
              gcongr
          _ = _ := by ring
    _ = (U : ℝ) ^ (-δ) * ∑ n ∈ Icc 1 (U * X), ((n.divisors.card : ℝ)) ^ 2 *
          (n : ℝ) ^ (-(1 + δ)) := by rw [mul_sum]
    _ ≤ (U : ℝ) ^ (-δ) * divisorConst δ := by
        gcongr
        refine (sum_card_divisors_sq_le _ _).trans ?_
        rw [divisorConst]
        gcongr
        exact sum_nonneg fun m _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _

end WeilExplicit
