import Masullo.Tail
import WeilExplicit.DensityWeighted

/-!
# The trace on average over modulations

The modulation of a test function `φ` by `τ` is `x ↦ x ^ (iτ) φ(x)`; its transform is `φ̂` shifted
by `iτ`. Fix `a > 0` and put `κ = min (a / 2) (1 / 8) ^ 2 / 3`. Weil's functional at the
modulation of `φ` by `τ`, minus the trace at width `a`, is the sum of `φ̂(ρ - 1/2 + iτ)` over the
zeros at distance at least `a` from the critical line, with multiplicity. Its absolute value has
mean `O(T^(-κ) log² (2T))` over `τ ∈ [-T, T]`, for every `T ≥ 2`, unconditionally.

Each zero of height at most `2T` contributes at most `π M` to the integral, where `M` bounds the
quartic decay of `φ̂`, and there are `O(T^(1-κ) log² T)` of them with multiplicity
(`WeilExplicit.exterior_mult_le`). The other zeros contribute `O(1 / T²)` at each `τ`. The estimate
excludes no zero: on paper, one zero contributes `O(1 / T)` to the mean. `measure_modulate_le` is
the corresponding Markov bound on the set of `τ` where the difference is large.

A Claude Fable subagent proposed this averaged form; OpenAI Codex supplied the unconditional proof
from the existing density estimate; Claude formalised it.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Masullo

namespace TestFunction

/-- The modulation `x ↦ x ^ (iτ) φ(x)`. -/
noncomputable def modulate (φ : TestFunction) (τ : ℝ) : TestFunction := φ.tilt (I * τ)

lemma modulate_zero (φ : TestFunction) : φ.modulate 0 = φ := by
  cases φ
  simp [modulate, tilt]

/-- Modulation by `τ` shifts the transform by `iτ`. -/
lemma hat_modulate (φ : TestFunction) (τ : ℝ) (z : ℂ) :
    (φ.modulate τ).hat z = φ.hat (z + I * τ) :=
  φ.hat_tilt _ z

end TestFunction

namespace Trace

/-- At the modulation by `τ`, the sum over the exterior zeros of `φ̂(ρ - 1/2 + iτ)`. -/
lemma hasSum_exterior_modulate {a : ℝ} (ha : 0 < a) (φ : TestFunction) (τ : ℝ) {s : ℂ}
    (hs : HasTrace (induced ha (φ.modulate τ)) s) :
    HasSum ((exterior a).indicator fun ρ : ℂ =>
      (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2 + I * τ)) ((φ.modulate τ).efFunctional - s) := by
  simpa only [TestFunction.hat_modulate] using hasSum_exterior ha hs

/-- `1 + |z|² ≤ 2 (1 + τ²) (1 + |z + iτ|²)`. -/
private lemma one_add_normSq_le (z : ℂ) (τ : ℝ) :
    1 + normSq z ≤ 2 * (1 + τ ^ 2) * (1 + normSq (z + I * τ)) := by
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  nlinarith [sq_nonneg (z.im + 2 * τ), sq_nonneg τ, sq_nonneg z.re, sq_nonneg (z.im + τ),
    mul_nonneg (sq_nonneg τ) (sq_nonneg z.re), mul_nonneg (sq_nonneg τ) (sq_nonneg (z.im + τ))]

private lemma normSq_div_I (z : ℂ) : normSq (z / I) = normSq z := by simp

/-- Quartic decay of the transform at the modulated zeros in the strip. -/
private lemma exists_modulated_hat_bound (φ : TestFunction) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {ρ : ℂ}, ρ ∈ stripZeros → ∀ τ : ℝ,
      ‖(zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2 + I * τ)‖ ≤
        zeroMult ρ * (M / (1 + normSq (ρ - 1 / 2 + I * τ)) ^ 2) := by
  obtain ⟨M, hM, hφ⟩ := φ.exists_hat_bound
  refine ⟨M, hM, fun {ρ} hρ τ => ?_⟩
  rw [norm_mul, norm_natCast]
  refine mul_le_mul_of_nonneg_left (hφ _ ?_) (Nat.cast_nonneg _)
  have h1 := hρ.2.1
  have h2 := hρ.2.2
  simp only [add_re, sub_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, abs_le]
  norm_num
  constructor <;> linarith

/-- **The discrepancy is continuous in the modulation.** For `0 < a`, a test function `φ` and trace
values `s τ` at width `a` of the modulations of `φ`, the map
`τ ↦ ‖Weil's functional at φ.modulate τ - s τ‖` is continuous. -/
theorem continuous_modulate_sub {a : ℝ} (ha : 0 < a) (φ : TestFunction) (s : ℝ → ℂ)
    (hs : ∀ τ, HasTrace (induced ha (φ.modulate τ)) (s τ)) :
    Continuous fun τ => ‖(φ.modulate τ).efFunctional - s τ‖ := by
  classical
  obtain ⟨M, hM, hhat⟩ := exists_modulated_hat_bound φ
  let f (τ : ℝ) (ρ : ℂ) : ℂ :=
    (exterior a).indicator (fun ρ : ℂ => (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2 + I * τ)) ρ
  have hF (τ : ℝ) : (φ.modulate τ).efFunctional - s τ = ∑' ρ, f τ ρ :=
    (hasSum_exterior_modulate ha φ τ (hs τ)).tsum_eq.symm
  have hns (ρ : ℂ) (τ : ℝ) : 0 < 1 + normSq (ρ - 1 / 2 + I * τ) := by
    linarith [normSq_nonneg (ρ - 1 / 2 + I * τ)]
  have hpos (x : ℝ) (hx : 1 ≤ x) : M / x ^ 2 ≤ M / x :=
    div_le_div_of_nonneg_left hM (by linarith) (by nlinarith)
  have hcont (T : ℝ) (hT : 0 ≤ T) :
      ContinuousOn (fun τ => ‖(φ.modulate τ).efFunctional - s τ‖) (uIcc (-T) T) := by
    simp only [hF]
    refine (continuousOn_tsum
      (u := fun ρ => 2 * (1 + T ^ 2) * M * stripZeros.indicator zeroWeight ρ) (fun ρ => ?_)
      (hasSum_zeroWeight.summable.mul_left _) fun ρ τ hτ => ?_).norm
    · simp only [f, indicator_apply]
      split_ifs
      · exact (continuous_const.mul (φ.continuous_hat.comp (by fun_prop))).continuousOn
      · exact continuousOn_const
    · rw [uIcc_of_le (by linarith)] at hτ
      have hτ2 : τ ^ 2 ≤ T ^ 2 := sq_le_sq' hτ.1 hτ.2
      simp only [f, indicator_apply]
      split_ifs with h1 h2
      · refine (hhat h1.1 τ).trans ?_
        have hp := one_add_normSq_le (ρ - 1 / 2) τ
        have hq := hns ρ τ
        simp only [zeroWeight, normSq_div_I]
        have hN := normSq_nonneg (ρ - 1 / 2)
        have hN' := normSq_nonneg (ρ - 1 / 2 + I * τ)
        calc (zeroMult ρ : ℝ) * (M / (1 + normSq (ρ - 1 / 2 + I * τ)) ^ 2)
            ≤ zeroMult ρ * (M / (1 + normSq (ρ - 1 / 2 + I * τ))) := by
              exact mul_le_mul_of_nonneg_left (hpos _ (by linarith)) (Nat.cast_nonneg _)
          _ ≤ zeroMult ρ * (2 * (1 + T ^ 2) * M / (1 + normSq (ρ - 1 / 2))) := by
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              rw [div_le_div_iff₀ hq (by linarith)]
              have hp' : 1 + normSq (ρ - 1 / 2) ≤
                  2 * (1 + T ^ 2) * (1 + normSq (ρ - 1 / 2 + I * τ)) :=
                hp.trans (by gcongr)
              nlinarith [mul_le_mul_of_nonneg_left hp' hM]
          _ = _ := by ring
      · exact absurd h1.1 h2
      all_goals
        rw [norm_zero]
        first
          | exact mul_nonneg (by positivity) (zeroWeight_nonneg ρ)
          | exact le_of_eq (mul_zero _).symm
  refine continuous_iff_continuousAt.2 fun τ => ?_
  have h := hcont (|τ| + 1) (by positivity)
  rw [uIcc_of_le (by linarith [abs_nonneg τ])] at h
  exact h.continuousAt
    (Icc_mem_nhds (by linarith [neg_abs_le τ]) (by linarith [le_abs_self τ]))


/-- **The trace on average over modulations.** For `0 < a` and a test function `φ` there is `C` such
that for every `T ≥ 2`, the absolute difference between Weil's functional and the trace at width
`a`, at the modulation of `φ` by `τ`, is integrable over `τ ∈ [-T, T]` with mean at most
`C T^(-κ) log² (2T)`, where `κ = min (a / 2) (1 / 8) ^ 2 / 3`. The trace values `s τ` are unique
(`HasTrace.unique`) and exist (`exists_hasTrace_induced`). -/
theorem mean_modulate_le {a : ℝ} (ha : 0 < a) (φ : TestFunction) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ s : ℝ → ℂ,
      (∀ τ, HasTrace (induced ha (φ.modulate τ)) (s τ)) →
      IntervalIntegrable (fun τ => ‖(φ.modulate τ).efFunctional - s τ‖) volume (-T) T ∧
      (2 * T)⁻¹ * ∫ τ in -T..T, ‖(φ.modulate τ).efFunctional - s τ‖ ≤
        C * T ^ (-(min (a / 2) (1 / 8) ^ 2 / 3)) * Real.log (2 * T) ^ 2 := by
  classical
  set κ := min (a / 2) (1 / 8) ^ 2 / 3
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 := by
    have : min (a / 2) (1 / 8) ≤ 1 / 8 := min_le_right _ _
    have h0 : 0 < min (a / 2) (1 / 8) := lt_min (by linarith) (by norm_num)
    simp only [κ]; nlinarith
  obtain ⟨M, hM, hhat⟩ := exists_modulated_hat_bound φ
  obtain ⟨A, hA, hcount⟩ := WeilExplicit.exterior_mult_le ha
  set W := ∑' ρ : stripZeros, zeroWeight ρ
  have hW : 0 ≤ W := tsum_nonneg fun _ => zeroWeight_nonneg _
  refine ⟨9 * Real.pi * M * A + 8 * M * W, by positivity, fun T hT s hs => ?_⟩
  have hT0 : 0 < T := by linarith
  have hpos (x : ℝ) (hx : 1 ≤ x) : M / x ^ 2 ≤ M / x :=
    div_le_div_of_nonneg_left hM (by linarith) (by nlinarith)
  have hint : IntervalIntegrable (fun τ => ‖(φ.modulate τ).efFunctional - s τ‖) volume (-T) T :=
    (continuous_modulate_sub ha φ s hs).intervalIntegrable _ _
  refine ⟨hint, ?_⟩
  -- the pointwise majorant
  set S := (finite_outerZerosUpTo a (2 * T)).toFinset
  let g (τ : ℝ) : ℝ :=
    ∑ ρ ∈ S, M * zeroMult ρ * (1 + (τ + ρ.im) ^ 2)⁻¹ + 8 * M * W / (1 + T ^ 2)
  have hg : Continuous g := by
    refine (continuous_finsetSum _ fun ρ _ => continuous_const.mul ?_).add continuous_const
    exact (by fun_prop : Continuous fun τ : ℝ => 1 + (τ + ρ.im) ^ 2).inv₀ fun τ => by positivity
  have hle : ∀ τ ∈ Icc (-T) T, ‖(φ.modulate τ).efFunctional - s τ‖ ≤ g τ := by
    intro τ hτ
    have hτ' : |τ| ≤ T := abs_le.2 hτ
    have hr := hasSum_remainder (T := 2 * T) ha (hs τ)
    simp only [TestFunction.hat_modulate] at hr
    have key := HasSum.norm_le_of_bounded hr (hasSum_zeroWeight.mul_left (8 * M / (1 + T ^ 2)))
      fun ρ => by
      by_cases hρ : ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2| ∧ 2 * T < |ρ.im|
      · rw [indicator_of_mem (by exact hρ), indicator_of_mem hρ.1]
        refine (hhat hρ.1 τ).trans ?_
        have hi : |ρ.im| / 2 ≤ |ρ.im + τ| := by
          have := abs_sub_abs_le_abs_sub ρ.im (-τ)
          rw [abs_neg, sub_neg_eq_add] at this
          linarith
        have hi2 : ρ.im ^ 2 / 4 ≤ (ρ.im + τ) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hi 2
          rw [div_pow, sq_abs, sq_abs] at this
          linarith
        have hT2 : T ^ 2 ≤ (ρ.im + τ) ^ 2 := by
          have h3 : T ≤ |ρ.im + τ| := by linarith
          have := pow_le_pow_left₀ hT0.le h3 2
          rwa [sq_abs] at this
        have hb2 : (ρ.re - 1 / 2) ^ 2 ≤ 1 / 4 := by
          have h1 := hρ.1.2.1
          have h2 := hρ.1.2.2
          nlinarith
        have e1 : normSq (ρ - 1 / 2 + I * τ) = (ρ.re - 1 / 2) ^ 2 + (ρ.im + τ) ^ 2 := by
          simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, I_re, I_im,
            ofReal_re, ofReal_im]
          norm_num
          ring
        have e2 : normSq ((ρ - 1 / 2) / I) = (ρ.re - 1 / 2) ^ 2 + ρ.im ^ 2 := by
          rw [normSq_div_I, normSq_apply]
          simp only [sub_re, sub_im]
          norm_num
          ring
        simp only [zeroWeight, e1, e2]
        have hX : (1 + T ^ 2) * (1 + ((ρ.re - 1 / 2) ^ 2 + ρ.im ^ 2)) ≤
            8 * (1 + ((ρ.re - 1 / 2) ^ 2 + (ρ.im + τ) ^ 2)) ^ 2 := by
          have h1 : 1 + T ^ 2 ≤ 1 + ((ρ.re - 1 / 2) ^ 2 + (ρ.im + τ) ^ 2) := by
            nlinarith [sq_nonneg (ρ.re - 1 / 2)]
          have h2 : 1 + ((ρ.re - 1 / 2) ^ 2 + ρ.im ^ 2) ≤
              8 * (1 + ((ρ.re - 1 / 2) ^ 2 + (ρ.im + τ) ^ 2)) := by
            nlinarith [sq_nonneg (ρ.re - 1 / 2)]
          have := mul_le_mul h1 h2 (by positivity) (by positivity)
          linarith
        have key2 : M / (1 + ((ρ.re - 1 / 2) ^ 2 + (ρ.im + τ) ^ 2)) ^ 2 ≤
            8 * M / (1 + T ^ 2) / (1 + ((ρ.re - 1 / 2) ^ 2 + ρ.im ^ 2)) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hX hM]
        calc _ ≤ (zeroMult ρ : ℝ) *
              (8 * M / (1 + T ^ 2) / (1 + ((ρ.re - 1 / 2) ^ 2 + ρ.im ^ 2))) :=
            mul_le_mul_of_nonneg_left key2 (Nat.cast_nonneg _)
          _ = _ := by ring
      · rw [indicator_of_notMem (by exact hρ), norm_zero]
        exact mul_nonneg (by positivity) (indicator_nonneg (fun ρ _ => zeroWeight_nonneg ρ) _)
    set D := ∑ ρ ∈ S, (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2 + I * τ)
    have hD : ‖D‖ ≤ ∑ ρ ∈ S, M * zeroMult ρ * (1 + (τ + ρ.im) ^ 2)⁻¹ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
      have hρ' := (finite_outerZerosUpTo a (2 * T)).mem_toFinset.1 hρ
      refine (hhat hρ'.1 τ).trans ?_
      have e1 : normSq (ρ - 1 / 2 + I * τ) = (ρ.re - 1 / 2) ^ 2 + (τ + ρ.im) ^ 2 := by
        simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, I_re, I_im,
          ofReal_re, ofReal_im]
        norm_num
        ring
      rw [e1, mul_comm M, mul_assoc, ← div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ((hpos _ (by nlinarith)).trans ?_) (Nat.cast_nonneg _)
      exact div_le_div_of_nonneg_left hM (by positivity) (by nlinarith)
    calc ‖(φ.modulate τ).efFunctional - s τ‖
        = ‖D + ((φ.modulate τ).efFunctional - s τ - D)‖ := by rw [add_sub_cancel]
      _ ≤ ‖D‖ + ‖(φ.modulate τ).efFunctional - s τ - D‖ := norm_add_le _ _
      _ ≤ g τ := by
          refine add_le_add hD (key.trans_eq ?_)
          ring
  -- integrate the majorant
  have hmono := intervalIntegral.integral_mono_on (by linarith) hint (hg.intervalIntegrable _ _)
    hle
  have hgint : ∫ τ in -T..T, g τ ≤
      Real.pi * M * ∑ ρ ∈ S, (zeroMult ρ : ℝ) + 2 * T * (8 * M * W / (1 + T ^ 2)) := by
    have hcf (ρ : ℂ) : Continuous fun τ : ℝ => M * zeroMult ρ * (1 + (τ + ρ.im) ^ 2)⁻¹ :=
      continuous_const.mul ((by fun_prop : Continuous fun τ : ℝ => 1 + (τ + ρ.im) ^ 2).inv₀
        fun τ => by positivity)
    simp only [g]
    rw [intervalIntegral.integral_add
      ((continuous_finsetSum _ fun ρ _ => hcf ρ).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_finsetSum
      fun ρ _ => (hcf ρ).intervalIntegrable _ _, intervalIntegral.integral_const, smul_eq_mul,
      Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun ρ _ => ?_) (le_of_eq (by ring))
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right
      (fun x => (1 + x ^ 2)⁻¹), integral_inv_one_add_sq]
    have h1 := Real.arctan_lt_pi_div_two (T + ρ.im)
    have h2 := Real.neg_pi_div_two_lt_arctan (-T + ρ.im)
    have hm : 0 ≤ M * (zeroMult ρ : ℝ) := by positivity
    calc M * (zeroMult ρ : ℝ) * (Real.arctan (T + ρ.im) - Real.arctan (-T + ρ.im))
        ≤ M * zeroMult ρ * Real.pi := by gcongr; linarith
      _ = _ := by ring
  -- the count and the final arithmetic
  have hN := hcount (2 * T) (by linarith) S fun ρ hρ => by
    have := (finite_outerZerosUpTo a (2 * T)).mem_toFinset.1 hρ
    exact ⟨this.1, this.2.1, this.2.2⟩
  rw [show 1 - min (a / 2) (1 / 8) ^ 2 / 3 = 1 - κ from rfl] at hN
  have hlog : Real.log (2 * (2 * T) + 4) ≤ 3 * Real.log (2 * T) := by
    rw [← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    norm_num
    nlinarith
  have hl0 : 1 ≤ Real.log (2 * T) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hpow : (2 * T) ^ (1 - κ) / (2 * T) ≤ T ^ (-κ) := by
    rw [← Real.rpow_sub_one (by linarith), show 1 - κ - 1 = -κ by ring]
    exact Real.rpow_le_rpow_of_nonpos hT0 (by linarith) (by linarith)
  have hTk : 1 / (1 + T ^ 2) ≤ T ^ (-κ) * Real.log (2 * T) ^ 2 := by
    have h1 : T ^ (-1 : ℝ) ≤ T ^ (-κ) := Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : 1 / (1 + T ^ 2) ≤ T⁻¹ := by
      rw [one_div]; exact inv_anti₀ hT0 (by nlinarith)
    have h3 : 0 ≤ T ^ (-κ) := by positivity
    nlinarith [one_le_pow₀ (n := 2) hl0]
  have hTk' : 0 ≤ T ^ (-κ) := by positivity
  have hcnt : (2 * T)⁻¹ * (Real.pi * M * ∑ ρ ∈ S, (zeroMult ρ : ℝ)) ≤
      9 * Real.pi * M * A * T ^ (-κ) * Real.log (2 * T) ^ 2 := by
    have hl2 : Real.log (2 * (2 * T) + 4) ^ 2 ≤ 9 * Real.log (2 * T) ^ 2 := by
      have := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 2
      linarith [show (3 * Real.log (2 * T)) ^ 2 = 9 * Real.log (2 * T) ^ 2 by ring]
    calc (2 * T)⁻¹ * (Real.pi * M * ∑ ρ ∈ S, (zeroMult ρ : ℝ))
        ≤ (2 * T)⁻¹ * (Real.pi * M * (A * ((2 * T) ^ (1 - κ) *
            Real.log (2 * (2 * T) + 4) ^ 2))) := by gcongr
      _ = Real.pi * M * A * ((2 * T) ^ (1 - κ) / (2 * T)) * Real.log (2 * (2 * T) + 4) ^ 2 := by
          field_simp
      _ ≤ Real.pi * M * A * T ^ (-κ) * (9 * Real.log (2 * T) ^ 2) := by gcongr
      _ = _ := by ring
  have hfar : (2 * T)⁻¹ * (2 * T * (8 * M * W / (1 + T ^ 2))) ≤
      8 * M * W * T ^ (-κ) * Real.log (2 * T) ^ 2 := by
    calc (2 * T)⁻¹ * (2 * T * (8 * M * W / (1 + T ^ 2))) = 8 * M * W * (1 / (1 + T ^ 2)) := by
          field_simp
      _ ≤ 8 * M * W * (T ^ (-κ) * Real.log (2 * T) ^ 2) :=
          mul_le_mul_of_nonneg_left hTk (by positivity)
      _ = _ := by ring
  calc (2 * T)⁻¹ * ∫ τ in -T..T, ‖(φ.modulate τ).efFunctional - s τ‖
      ≤ (2 * T)⁻¹ * (Real.pi * M * ∑ ρ ∈ S, (zeroMult ρ : ℝ) +
          2 * T * (8 * M * W / (1 + T ^ 2))) := by
        gcongr
        exact hmono.trans hgint
    _ ≤ _ := by
        rw [mul_add]
        refine (add_le_add hcnt hfar).trans_eq ?_
        ring

/-- **Sharpness of the averaged trace.** For `0 < a`, a test function `φ` and trace values `s τ`
at width `a` of the modulations of `φ`: if the unnormalised integrals
`∫ τ in -T..T, ‖Weil's functional at φ.modulate τ - s τ‖` fall below every `ε > 0` for arbitrarily
large `T`, then the trace identity `s τ = Weil's functional at φ.modulate τ` holds at every `τ`.
The integrand is continuous and nonnegative, and the integral is nondecreasing in `T`. -/
theorem trace_eq_of_integral_small {a : ℝ} (ha : 0 < a) (φ : TestFunction) (s : ℝ → ℂ)
    (hs : ∀ τ, HasTrace (induced ha (φ.modulate τ)) (s τ))
    (h : ∀ ε : ℝ, 0 < ε → ∀ T₀ : ℝ, ∃ T, T₀ ≤ T ∧
      ∫ τ in -T..T, ‖(φ.modulate τ).efFunctional - s τ‖ ≤ ε) (τ₀ : ℝ) :
    s τ₀ = (φ.modulate τ₀).efFunctional := by
  by_contra hne
  have hg := continuous_modulate_sub ha φ s hs
  have hx : 0 < ‖(φ.modulate τ₀).efFunctional - s τ₀‖ :=
    norm_pos_iff.2 fun h0 => hne (sub_eq_zero.1 h0).symm
  have hR : -(|τ₀| + 1) < |τ₀| + 1 := by linarith [abs_nonneg τ₀]
  have hpos := intervalIntegral.integral_pos hR hg.continuousOn (fun _ _ => norm_nonneg _)
    ⟨τ₀, ⟨by linarith [neg_abs_le τ₀], by linarith [le_abs_self τ₀]⟩, hx⟩
  obtain ⟨T, hT, hle⟩ := h _ (half_pos hpos) (|τ₀| + 1)
  have := intervalIntegral.integral_mono_interval (by linarith) hR.le hT
    (Eventually.of_forall fun _ => norm_nonneg _) (hg.intervalIntegrable (μ := volume) (-T) T)
  linarith

/-- **Markov's inequality.** With `C` and `κ` as in `mean_modulate_le`, the set of `τ ∈ (-T, T]`
where the difference has absolute value at least `ε` has measure at most
`2 C T^(1-κ) log² (2T) / ε`. -/
theorem measure_modulate_le {a : ℝ} (ha : 0 < a) (φ : TestFunction) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ s : ℝ → ℂ,
      (∀ τ, HasTrace (induced ha (φ.modulate τ)) (s τ)) → ∀ ε : ℝ,
      ε * volume.real ({τ | ε ≤ ‖(φ.modulate τ).efFunctional - s τ‖} ∩ Ioc (-T) T) ≤
        C * T ^ (1 - min (a / 2) (1 / 8) ^ 2 / 3) * Real.log (2 * T) ^ 2 := by
  obtain ⟨C, hC, h⟩ := mean_modulate_le ha φ
  refine ⟨2 * C, by positivity, fun T hT s hs ε => ?_⟩
  obtain ⟨hint, hmean⟩ := h T hT s hs
  have hT0 : 0 < T := by linarith
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc (-T) T))
    (Eventually.of_forall fun τ => norm_nonneg _) hint.1 ε
  simp only [measureReal_def, Measure.restrict_apply' measurableSet_Ioc] at hm
  rw [← intervalIntegral.integral_of_le (by linarith)] at hm
  rw [inv_mul_le_iff₀ (by linarith)] at hmean
  refine (hm.trans hmean).trans_eq ?_
  rw [show 1 - min (a / 2) (1 / 8) ^ 2 / 3 = 1 + -(min (a / 2) (1 / 8) ^ 2 / 3) by ring,
    Real.rpow_add hT0, Real.rpow_one]
  ring

end Trace

end Masullo
