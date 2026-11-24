import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The Dirichlet series on the half-plane `2 ≤ re s` -/

namespace WeilExplicit

open Complex Real

/-- The tail of the Dirichlet series is majorized by the tail of the Basel series. -/
theorem norm_zeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ π ^ 2 / 6 - 1 := by
  have hs' : 1 < s.re := by linarith
  have h := (Complex.summable_one_div_nat_cpow.mpr hs').sum_add_tsum_nat_add 2
  rw [← zeta_eq_tsum_one_div_nat_cpow hs'] at h
  simp [Finset.sum_range_succ, Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs')] at h
  have h₂ := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  rw [hasSum_zeta_two.tsum_eq] at h₂
  simp [Finset.sum_range_succ] at h₂
  rw [← h, add_sub_cancel_left, ← h₂, add_sub_cancel_left]
  have hsum := (summable_nat_add_iff 2).2 hasSum_zeta_two.summable
  have hn := ((summable_nat_add_iff 2).2 (Complex.summable_one_div_nat_cpow.mpr hs')).norm
  suffices bound : ‖∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℂ) ^ s‖ ≤
      ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 by simpa [one_div] using bound
  refine (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum ?_ hsum)
  intro n
  simp only [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 2)]
  rw [← Real.rpow_two]
  gcongr
  exact_mod_cast (by omega : 1 ≤ n + 2)

/-- A uniform lower bound, in particular at the centers of the Jensen discs. -/
theorem one_third_le_norm_riemannZeta {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 3 ≤ ‖riemannZeta s‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (riemannZeta s)
  rw [norm_one, norm_sub_rev] at h
  have hπ := sq_lt_sq' (by linarith [Real.pi_pos] : -(3.15 : ℝ) < π) Real.pi_lt_d2
  linarith [norm_zeta_sub_one_le hs]

end WeilExplicit
