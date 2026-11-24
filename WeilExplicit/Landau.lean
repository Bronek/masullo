import WeilExplicit.RemoveZeros
import WeilExplicit.LogDerivative
import Mathlib.Analysis.Complex.AbsMax

/-! # Landau's local partial fractions for the logarithmic derivative -/

namespace WeilExplicit

open Complex Metric Set

/-- Landau's estimate for the zeta counting discs. Zeros up to radius 5/3 contribute their
polar terms on radius 8/5. The bound on radius 7/4 costs at most log 24 per removed zero. -/
theorem landau_disc {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c x : ℂ}
    (S : Finset ℂ) (hS : ∀ a, a ∈ S ↔ a ∈ closedBall c (5/3) ∧ f a = 0)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ z ∈ sphere c (7/4), ‖f z‖ ≤ Real.exp B * ‖f c‖)
    (hx : dist x c ≤ 8/5) (hxn : x ∉ S) :
    ‖logDeriv f x - ∑ a ∈ S, (analyticOrderNatAt f a : ℂ) / (x - a)‖ ≤
      3000 * (B + (∑ a ∈ S, (analyticOrderNatAt f a : ℝ)) * Real.log 24) := by
  classical
  let m := analyticOrderNatAt f
  let N := ∑ a ∈ S, m a
  let P (z : ℂ) := ∏ a ∈ S, (z - a) ^ m a
  have hdP : Differentiable ℂ P := by dsimp [P]; fun_prop
  have hfx : f x ≠ 0 := fun e ↦ hxn ((hS x).mpr ⟨mem_closedBall.mpr (by linarith), e⟩)
  have ha : AnalyticOnNhd ℂ f univ := fun z _ ↦ hf.analyticAt z
  obtain ⟨g, hg, hgn, hfg⟩ := factor_finset_orders S hf fun a _ ↦
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ x) (mem_univ a)
      (by rw [(hf.analyticAt x).analyticOrderAt_eq_zero.mpr hfx]; simp)
  have heq (z : ℂ) : ‖f z‖ = ‖P z‖ * ‖g z‖ := by rw [hfg z, norm_mul]
  have hn (z : ℂ) (hz : z ∈ ball c (5/3)) : g z ≠ 0 := by
    intro h
    apply hgn z ((hS z).mpr ⟨ball_subset_closedBall hz, by simp [hfg z, h]⟩) h
  have hc : ‖P c‖ ≤ 2 ^ N := by
    simp only [P, N, Complex.norm_prod, norm_pow, ← Finset.prod_pow_eq_pow_sum]
    gcongr with a ha
    have := mem_closedBall.mp ((hS a).mp ha).1
    rw [← dist_eq_norm, dist_comm]
    linarith
  have hM (z : ℂ) (hz : z ∈ sphere c (7/4)) : (1/12 : ℝ)^N ≤ ‖P z‖ := by
    simp only [P, N, Complex.norm_prod, norm_pow, ← Finset.prod_pow_eq_pow_sum]
    gcongr with a ha
    rw [← dist_eq_norm]
    linarith [dist_triangle z a c, mem_sphere.mp hz, mem_closedBall.mp ((hS a).mp ha).1]
  have hb (z : ℂ) (hz : z ∈ ball c (5/3)) : ‖g z‖ ≤ Real.exp B * 24^N * ‖g c‖ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball c (7/4))
      (isBounded_ball) hg.diffContOnCl
    · rw [frontier_ball _ (by norm_num : (7/4 : ℝ) ≠ 0)]
      intro w hw
      have h := hbound w hw
      rw [heq w, heq c] at h
      have h' : (1/12 : ℝ)^N * ‖g w‖ ≤ Real.exp B * (2^N * ‖g c‖) := by
        calc
          _ ≤ ‖P w‖ * ‖g w‖ := by gcongr; exact hM w hw
          _ ≤ _ := h.trans (by gcongr)
      rw [one_div, inv_pow, inv_mul_le_iff₀ (by positivity)] at h'
      convert! h' using 1
      rw [show (24 : ℝ) = 12 * 2 by norm_num, mul_pow]
      ring
    · exact subset_closure (ball_subset_ball (by norm_num : (5/3 : ℝ) ≤ 7/4) hz)
  have hlog (z : ℂ) (hz : z ∈ ball c (5/3)) :
      Real.log ‖g z‖ - Real.log ‖g c‖ ≤ B + N * Real.log 24 := by
    have H := Real.log_le_log (norm_pos_iff.mpr (hn z hz)) (hb z hz)
    rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr (hn c (mem_ball_self (by norm_num)))),
      Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow] at H
    linarith
  have hD := norm_logDeriv_le_of_log_norm_sub_le (x := x) (d := 1/30) (by norm_num)
    (show 0 < B + N * Real.log 24 by positivity) (by linarith) hg.differentiableOn hn hlog
  have hx' : x ∈ ball c (5/3) := mem_ball.mpr (by linarith)
  have hne (a : ℂ) (ha : a ∈ S) : (x - a) ^ m a ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem ha hxn).symm)
  have hP : logDeriv P x = ∑ a ∈ S, (m a : ℂ) / (x - a) := by
    rw [show P = (fun z ↦ ∏ a ∈ S, (z - a) ^ m a) from rfl,
      logDeriv_prod (f := fun a z ↦ (z - a) ^ m a) hne (by intros; fun_prop)]
    apply Finset.sum_congr rfl
    intro a _
    rw [logDeriv_fun_pow (f := fun z : ℂ ↦ z - a) (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  change ‖logDeriv f x - ∑ a ∈ S, (m a : ℂ) / (x - a)‖ ≤
    3000 * (B + (∑ a ∈ S, (m a : ℝ)) * Real.log 24)
  rw [show f = (fun z ↦ P z * g z) from funext hfg,
    logDeriv_mul x (Finset.prod_ne_zero_iff.mpr hne) (hn x hx') (hdP x) (hg x), hP,
    add_sub_cancel_left]
  simp only [N, Nat.cast_sum] at hD
  convert! hD using 1
  ring

end WeilExplicit
