import WeilExplicit.Growth
import WeilExplicit.Jensen
import WeilExplicit.LowerBound
import WeilExplicit.Zeros

/-! # Jensen discs and unit windows for zeta zeros -/

namespace WeilExplicit

open Complex Metric Set Filter Real
open scoped Topology

/-- Away from one, pole-removed zeta equals (s−1)ζ(s). -/
theorem zeta₁_eq_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

/-- Removing the pole at one preserves all other analytic orders. -/
theorem zeta₁_order {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta₁ s = analyticOrderAt riemannZeta s := by
  have h : riemannZeta₁ =ᶠ[𝓝 s] (fun z : ℂ ↦ z - 1) * riemannZeta :=
    (eventually_ne_nhds hs).mono fun _ hz ↦ zeta₁_eq_mul hz
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) s := by fun_prop
  rw [analyticOrderAt_congr h, analyticOrderAt_mul ha (analyticOn_riemannZeta s hs),
    ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs), zero_add]

/-- The pole removed zeta function is polynomially bounded on the outer Jensen disc. -/
theorem norm_zeta₁_on_disc (t : ℝ) {z : ℂ} (hz : z ∈ closedBall (2 + t * I) (7/4)) :
    ‖riemannZeta₁ z‖ ≤ 5 * (|t| + 5)^2 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have ht := (abs_re_le_norm (z - (2 + t * I))).trans hz
  norm_num at ht
  have hre : 1/4 ≤ z.re := by linarith [(abs_le.mp ht).1]
  have hc : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by simpa using norm_add_le (2 : ℂ) (t * I)
  have hnorm : ‖z‖ ≤ |t| + 4 := by linarith [norm_sub_norm_le z (2 + t * I)]
  have hn₁ : ‖z - 1‖ ≤ |t| + 5 := by linarith [norm_sub_le z 1, norm_one (α := ℂ)]
  by_cases h : z = 1
  · simp [h]
    nlinarith [abs_nonneg t, sq_nonneg (|t|)]
  rw [zeta₁_eq_mul h, norm_mul]
  grw [norm_zeta_le (by linarith) h]
  rw [mul_add, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))]
  have hdiv : ‖z‖ / z.re ≤ 4 * (|t| + 5) := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hre) (show 0 ≤ |t| + 5 by positivity)]
  grw [hn₁, hdiv, hnorm]
  nlinarith [abs_nonneg t, sq_nonneg (|t|)]

/-- On the half-plane Re s ≥ 2 the pole-removed zeta has norm at least one third. -/
theorem one_third_le_norm_zeta₁ {s : ℂ} (hs : 2 ≤ s.re) : 1/3 ≤ ‖riemannZeta₁ s‖ := by
  have h₁ : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [zeta₁_eq_mul h₁, norm_mul]
  apply (one_third_le_norm_riemannZeta hs).trans (le_mul_of_one_le_left (norm_nonneg _) ?_)
  exact le_trans (by simp; linarith : 1 ≤ (s-1).re) (re_le_norm _)

/-- Uniform multiplicity bound in a disc covering the right half of a unit window. -/
theorem disc_zero_count (t : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall (2 + t * I) (5/3) ∧ z ≠ 1) :
    ∑ z ∈ S, (zeroMult z : ℝ) ≤ (8 / Real.log (21/20)) * Real.log (|t| + 3) := by
  let c : ℂ := 2 + t * I
  have hc : c.re = 2 := by simp [c]
  have hlow := one_third_le_norm_zeta₁ hc.ge
  let M := 5 * (|t| + 5)^2
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t, sq_nonneg (|t|)]
  have hJ := sum_orders_le (c := c) (f := riemannZeta₁) (r := 5/3) (R := 7/4)
    (by norm_num) (by norm_num) hM (fun z _ ↦ differentiable_riemannZeta₁.analyticAt z)
    (norm_pos_iff.mp (by linarith)) (fun z hz ↦ norm_zeta₁_on_disc t (sphere_subset_closedBall hz))
    S (fun z hz ↦ (hS z hz).1)
  have hsubst : ∑ z ∈ S, (zeroMult z : ℝ) = ∑ z ∈ S, (analyticOrderNatAt riemannZeta₁ z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    simp only [zeroMult, analyticOrderNatAt, zeta₁_order (hS z hz).2]
  rw [hsubst]
  apply hJ.trans
  norm_num1
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (log_nonneg (by norm_num))
  rw [show (8 : ℝ) * Real.log (|t| + 3) = Real.log ((|t| + 3)^8) by rw [Real.log_pow]; norm_num]
  apply Real.log_le_log (div_pos (by linarith) (by linarith))
  apply (div_le_iff₀ (by linarith)).mpr
  have hpoly : 3 * M ≤ (|t| + 3)^8 := by
    dsimp [M]
    apply sub_nonneg.mp
    ring_nf
    positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (pow_nonneg (show 0 ≤ |t| + 3 by positivity) 8)]

/-- The right half of a unit window fits within radius 8/5 of its center on Re s = 2. -/
theorem dist_window_center_le {s : ℂ} {t : ℝ} (ha : 1/2 ≤ s.re) (hb : s.re ≤ 2)
    (ht : |s.im - t| ≤ 1/2) : dist s (2 + t * I) ≤ 8/5 := by
  rw [dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (by norm_num), ← normSq_eq_norm_sq, normSq_apply]
  norm_num
  nlinarith [mul_nonneg (by linarith : 0 ≤ s.re - 1/2) (by linarith : 0 ≤ 7/2 - s.re),
    sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2]

/-- A closed unit window has logarithmically bounded total multiplicity.
The estimate applies to every finite subfamily. -/
theorem window_zero_count (t : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1/2) :
    ∑ z ∈ S, (zeroMult z : ℝ) ≤ (16 / Real.log (21/20)) * Real.log (|t| + 3) := by
  classical
  let R := S.filter fun z ↦ 1/2 ≤ z.re
  let L := S.filter fun z ↦ ¬ 1/2 ≤ z.re
  have hR := disc_zero_count t R (by
    intro z hz
    obtain ⟨hzS, ha⟩ := Finset.mem_filter.mp hz
    obtain ⟨_, hb, ht⟩ := hS z hzS
    exact ⟨mem_closedBall.mpr ((dist_window_center_le ha (by linarith) ht).trans (by norm_num)),
      fun h ↦ by simp [h] at hb⟩)
  let e : ℂ ↪ ℂ := ⟨fun z ↦ 1 - z, sub_right_injective⟩
  have hL := disc_zero_count (-t) (L.map e) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨hzS, ha⟩ := Finset.mem_filter.mp hz
    obtain ⟨hb, _, ht⟩ := hS z hzS
    change 1 - z ∈ _ ∧ 1 - z ≠ 1
    refine ⟨mem_closedBall.mpr ((dist_window_center_le ?_ ?_ ?_).trans (by norm_num)), fun h ↦ ?_⟩
    · simp only [Complex.sub_re, one_re]; linarith
    · simp only [Complex.sub_re, one_re]; linarith
    · simpa only [sub_im, one_im, zero_sub, neg_sub_neg, abs_sub_comm t] using ht
    · have := congrArg Complex.re h
      simp at this
      linarith)
  rw [Finset.sum_map, abs_neg] at hL
  have hchange : ∑ z ∈ L, (zeroMult (e z) : ℝ) = ∑ z ∈ L, (zeroMult z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨ha, hb, _⟩ := hS z (Finset.mem_filter.mp hz).1
    rw [show e z = 1 - z from rfl, zeroMult_one_sub ha hb]
  rw [hchange] at hL
  have hsplit := S.sum_filter_add_sum_filter_not (fun z : ℂ ↦ 1/2 ≤ z.re) (fun z ↦ (zeroMult z : ℝ))
  change (∑ z ∈ R, _) + (∑ z ∈ L, _) = _ at hsplit
  rw [← hsplit, show (16 : ℝ) / Real.log (21/20) =
    8 / Real.log (21/20) + 8 / Real.log (21/20) by ring, add_mul]
  exact add_le_add hR hL

end WeilExplicit
