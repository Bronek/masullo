import Mathlib.Analysis.Complex.JensenFormula

/-! # Counting finite families of zeros with Jensen's inequality -/

namespace WeilExplicit

open Metric MeromorphicOn

/-- Jensen's bound for the sum of analytic multiplicities over any finite subset
of the smaller disc. The outer circle may pass through zeros. -/
theorem sum_orders_le {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall c r) :
    ∑ z ∈ S, (analyticOrderNatAt f z : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  classical
  have HR := abs_of_pos (hr.trans hrR)
  have Hr := abs_of_pos hr
  have hj := AnalyticOnNhd.sum_divisor_le (f := f) (c := c) (r := r) (R := R)
    (by rwa [Hr]) (by rwa [Hr, HR]) hM (by rwa [HR]) hc (by rwa [HR])
  rw [Hr] at hj
  let D := divisor f (closedBall c r)
  have hD := D.finiteSupport (isCompact_closedBall c r)
  have ha := hf.mono (closedBall_subset_closedBall hrR.le)
  have hz (z : ℂ) (hz : z ∈ S) : D z = (analyticOrderNatAt f z : ℤ) := by
    rw [show D z = _ from ha.divisor_apply (hS z hz)]
    cases h : analyticOrderAt f z <;> simp [analyticOrderNatAt, h]
  have hle : ∑ z ∈ S, D z ≤ ∑ᶠ z, D z := by
    rw [finsum_eq_sum_of_support_subset _ (s := S ∪ hD.toFinset)
      (by intro z hz'; exact Finset.mem_union_right _ (hD.mem_toFinset.mpr hz'))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      fun z _ _ ↦ ha.divisor_nonneg z
  have hh : (∑ z ∈ S, D z : ℤ) = ∑ z ∈ S, (analyticOrderNatAt f z : ℤ) := Finset.sum_congr rfl hz
  rw [hh] at hle
  exact (by exact_mod_cast hle : ∑ z ∈ S, (analyticOrderNatAt f z : ℝ)
    ≤ ((∑ᶠ z, D z : ℤ) : ℝ)).trans hj

end WeilExplicit
