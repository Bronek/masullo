import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Finite support of the prime term -/

namespace WeilExplicit

/-- Once log n leaves the support interval, both reflected test-function values vanish. -/
theorem prime_sum_finite_support {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    (fun n : ℕ ↦ ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))).HasFiniteSupport := by
  obtain ⟨B, _, hB⟩ := hk.exists_pos_le_norm
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp B)
  apply (Set.finite_Iio N).subset
  intro n hn
  by_contra! h
  have hn' : Real.exp B < n := hN.trans_le (Nat.cast_le.mpr (not_lt.mp h))
  have hlog := (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hn')).mpr hn'
  have hp := hB (Real.log n) (hlog.le.trans (le_abs_self _))
  have hm := hB (-Real.log n) (by simpa using hlog.le.trans (le_abs_self (Real.log n)))
  simp [Function.mem_support, hp, hm] at hn

end WeilExplicit
