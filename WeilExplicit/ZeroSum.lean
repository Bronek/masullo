import WeilExplicit.ZeroCount
import Mathlib.Analysis.PSeries

/-! # Absolute convergence of the inverse-square sum -/

namespace WeilExplicit

open Complex Real

private theorem floor_weight_le (z : ℂ) (n : ℤ) (hn : ⌊z.im⌋ = n) :
    (|(n : ℝ)| + 1)^2 ≤ 8 * (1 + normSq ((z - 1/2) / I)) := by
  subst n
  have hdist : |(⌊z.im⌋ : ℝ) - z.im| ≤ 1 :=
    abs_le.mpr ⟨by linarith [Int.lt_floor_add_one z.im], by linarith [Int.floor_le z.im]⟩
  have habs : |(⌊z.im⌋ : ℝ)| + 1 ≤ |z.im| + 2 := by
    linarith [abs_sub_abs_le_abs_sub (⌊z.im⌋ : ℝ) z.im]
  have hs := sq_le_sq₀ (show 0 ≤ |(⌊z.im⌋ : ℝ)| + 1 by positivity)
    (show 0 ≤ |z.im| + 2 by positivity) |>.mpr habs
  rw [normSq_div, normSq_I, div_one, normSq_apply]
  norm_num
  nlinarith [sq_abs z.im, sq_nonneg (|z.im| - 2), sq_nonneg (z.re - 1/2)]

private theorem log_window_le (n : ℤ) :
    Real.log (|(n : ℝ) + 1/2| + 3) ≤ 4 * √(|(n : ℝ)| + 1) := by
  have h : |(n : ℝ) + 1/2| + 3 ≤ 4 * (|(n : ℝ)| + 1) := by
    have := abs_add_le (n : ℝ) (1/2)
    norm_num at this
    linarith [abs_nonneg (n : ℝ)]
  calc
    _ ≤ Real.log (4 * (|(n : ℝ)| + 1)) := Real.log_le_log (by positivity) h
    _ ≤ _ := by
      have := Real.log_le_rpow_div (show 0 ≤ 4 * (|(n : ℝ)| + 1) by positivity) one_half_pos
      rw [← sqrt_eq_rpow, sqrt_mul (by norm_num),
        show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]] at this
      linarith

/-- The strip zeros with their analytic multiplicities have finite inverse-square mass. -/
theorem summable_zeroMult_div_one_add_normSq :
    Summable fun ρ : stripZeros ↦ (zeroMult ρ : ℝ) /
      (1 + normSq (((ρ : ℂ) - 1/2) / I)) := by
  classical
  let A : ℝ := 16 / Real.log (21/20)
  have hA : 0 < A := div_pos (by norm_num) (Real.log_pos (by norm_num))
  let g (n : ℤ) := 32 * A * (1 / (|(n : ℝ)| + 1) ^ (3/2 : ℝ))
  have hg : Summable g := by
    apply Summable.mul_left
    rw [summable_int_iff_summable_nat_and_neg]
    have h := (Real.summable_one_div_nat_add_rpow 1 (3/2)).mpr (by norm_num)
    have ha (n : ℕ) : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_pos (by positivity)
    simpa [abs_of_nonneg, ha] using And.intro h h
  let w (ρ : stripZeros) := (zeroMult ρ : ℝ) / (1 + normSq (((ρ : ℂ) - 1/2) / I))
  let ord (ρ : stripZeros) := ⌊(ρ : ℂ).im⌋
  apply summable_of_sum_le (c := ∑' n, g n)
    (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (add_nonneg zero_le_one (normSq_nonneg _)))
  intro S
  change ∑ ρ ∈ S, w ρ ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to (fun i ↦ Finset.mem_image_of_mem (s := S) ord) w]
  refine (Finset.sum_le_sum fun n _ ↦ ?_).trans
    (hg.sum_le_tsum _ fun n _ ↦ by dsimp [g]; positivity)
  let F := S.filter fun ρ ↦ ord ρ = n
  let e := Function.Embedding.subtype (· ∈ stripZeros)
  have hcount := window_zero_count ((n : ℝ) + 1/2) (F.map e) (by
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hz
    have hn : ⌊(ρ : ℂ).im⌋ = n := (Finset.mem_filter.mp hρ).2
    refine ⟨ρ.property.2.1, ρ.property.2.2, abs_le.mpr ⟨?_, ?_⟩⟩
    all_goals dsimp [e]; subst n
    · linarith [Int.floor_le (ρ : ℂ).im]
    · linarith [Int.lt_floor_add_one (ρ : ℂ).im])
  rw [Finset.sum_map] at hcount
  let q := |(n : ℝ)| + 1
  have hq : 0 < q := by dsimp [q]; positivity
  calc
    ∑ ρ ∈ F, w ρ ≤ ∑ ρ ∈ F, (zeroMult ρ : ℝ) * (8 / q^2) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hf := floor_weight_le ρ n (Finset.mem_filter.mp hρ).2
      dsimp [w]
      rw [div_eq_mul_inv]
      gcongr
      apply (le_div_iff₀ (sq_pos_of_pos hq)).mpr
      rwa [inv_mul_le_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (normSq_nonneg _)), mul_comm]
    _ = (∑ ρ ∈ F, (zeroMult ρ : ℝ)) * (8 / q^2) := (Finset.sum_mul ..).symm
    _ ≤ (A * (4 * √q)) * (8 / q^2) := by
      gcongr
      exact hcount.trans (mul_le_mul_of_nonneg_left (log_window_le n) hA.le)
    _ = g n := by
      change _ = 32 * A * (1 / q ^ (3/2 : ℝ))
      rw [sqrt_eq_rpow, show (3/2 : ℝ) = 2 - 1/2 by norm_num, Real.rpow_sub hq, Real.rpow_two]
      simp only [one_div, inv_div]
      ring

end WeilExplicit
