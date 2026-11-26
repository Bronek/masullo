import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Controls for the zero-density summation

`summable_inv_im_of_half_lt` passes from a shell count `O(log T · T^{1-δ²/3})` to summability of
`1 / Im ρ`. An upper bound of order `T / log T` alone allows divergent reciprocal sums: the model
ordinates `γ_n = n log(n + 1)` satisfy `#{n : γ_n ≤ T} ≤ √T + 2T / log T`, and `∑ 1 / γ_n`
diverges. The summation uses the power saving `T^{-δ²/3}` of the shell count.

The statement is not claimed for `σ ≤ 1/2`: the proof needs `δ = (min σ (3/4) - 1/2) / 2 > 0`
both for the disc radius and for the saving exponent `δ²/3`.

Part of a Carlson-type mean-square zero-density argument due to OpenAI Codex (E36),
formalised by Claude.
-/

namespace WeilExplicit.DensityControls

open Real

/-- The model ordinates `n log(n + 1)` have divergent reciprocal sum. -/
theorem model_not_summable : ¬ Summable fun n : ℕ ↦ 1 / ((n : ℝ) * Real.log (n + 1)) := by
  set f : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) * Real.log (n + 1))
  have hlog : ∀ n : ℕ, 0 ≤ Real.log ((n : ℝ) + 1) := fun n ↦
    Real.log_nonneg (by have := n.cast_nonneg (α := ℝ); linarith)
  have h0 : ∀ n, 0 ≤ f n := fun n ↦ by have := hlog n; simp only [f]; positivity
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hlm : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul hmn' (Real.log_le_log (by linarith) (by linarith)) hlm.le (by linarith))
  rw [← summable_condensed_iff_of_nonneg h0 hmono]
  intro hs
  have hb : ∀ k : ℕ, 1 / (Real.log 2 * ((k : ℝ) + 1)) ≤ (2 : ℝ) ^ k * f (2 ^ k) := by
    intro k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hl : 0 < Real.log ((2 : ℝ) ^ k + 1) := Real.log_pos (by linarith)
    simp only [f]
    push_cast
    rw [show (2 : ℝ) ^ k * (1 / ((2 : ℝ) ^ k * Real.log (2 ^ k + 1))) =
      1 / Real.log (2 ^ k + 1) by field_simp]
    refine one_div_le_one_div_of_le hl ?_
    rw [mul_comm, show ((k : ℝ) + 1) * Real.log 2 = Real.log (2 ^ (k + 1)) by
      rw [Real.log_pow]; push_cast; ring]
    exact Real.log_le_log (by positivity) (by rw [pow_succ]; linarith)
  have hsum : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := by
    have := (hs.of_nonneg_of_le (fun k ↦ by positivity) hb).mul_left (Real.log 2)
    refine this.congr fun k ↦ ?_
    have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp (by
    simpa [Nat.cast_add, Nat.cast_one] using hsum))

/-- An upper bound for the counting function of the model ordinates. -/
theorem model_count_le {T : ℝ} (hT : 1 < T) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ (n : ℝ) * Real.log (n + 1) ≤ T) :
    (S.card : ℝ) ≤ √T + 2 * T / Real.log T := by
  have hlT : 0 < Real.log T := Real.log_pos hT
  set M := √T + 2 * T / Real.log T
  have hn : ∀ n ∈ S, (n : ℝ) ≤ M := by
    intro n hnS
    obtain ⟨hn1, hnT⟩ := hS n hnS
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h2 : 0 ≤ 2 * T / Real.log T := by positivity
    by_cases hs : (n : ℝ) < √T
    · simp only [M]; linarith
    · push Not at hs
      have hsq : Real.log T / 2 ≤ Real.log (n + 1) := by
        calc Real.log T / 2 = Real.log √T := by
              rw [Real.log_sqrt (by linarith)]
          _ ≤ Real.log (n + 1) :=
              Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) (by linarith)
      have hl : 0 < Real.log (n + 1) := by linarith
      have : (n : ℝ) ≤ 2 * T / Real.log T := by
        rw [le_div_iff₀ hlT]
        nlinarith
      simp only [M]
      linarith [Real.sqrt_nonneg T]
  have hsub : S ⊆ Finset.Icc 1 ⌊M⌋₊ := fun n hnS ↦
    Finset.mem_Icc.mpr ⟨(hS n hnS).1, Nat.le_floor (hn n hnS)⟩
  calc (S.card : ℝ) ≤ (Finset.Icc 1 ⌊M⌋₊).card := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌊M⌋₊ := by simp
    _ ≤ M := Nat.floor_le (by positivity)

end WeilExplicit.DensityControls
