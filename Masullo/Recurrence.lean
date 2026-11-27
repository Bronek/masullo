import Masullo.Window
import WeilExplicit.DensityWeighted
import Mathlib.Analysis.Complex.AbsMax

/-!
# Self-recurrence rules out zeros

Zeta is self-recurrent with positive upper density on `θ < re s < 1` when, for every closed disc
`K` in that strip and every `ε > 0`, the shifts `τ ∈ [0, T]` with `‖ζ(s + iτ) - ζ(s)‖ < ε` on all
of `K` have measure at least `c T`, for some `c > 0` and arbitrarily large `T`. For `θ ≥ 1/2` this
rules out zeros with real part greater than `θ` (`riemannZeta_ne_zero_of_selfRecurrent`), so the
trace identity holds for every test function at every width `a > θ - 1/2`
(`trace_eq_efFunctional_of_selfRecurrent`). The implication is one-way: self-recurrence is not
asserted for any `θ`.

A zero `ρ` in the strip is the centre of a closed disc `K` in the strip with no other zero, and
`ζ` has a positive minimum modulus `m` on its boundary. At a shift `τ` within `m / 2` on `K`,
`‖ζ(ρ + iτ)‖ < m / 2` while `‖ζ‖ > m / 2` on the boundary of `K + iτ`, so by the maximum principle
for `1 / ζ` there is a zero in `K + iτ`. Those shifts are covered by intervals of length `2r`, one
per zero at distance at least `re ρ - r - 1/2 > 0` from the critical line and of height `O(T)`,
where `r` is the radius of `K`. There are `o(T)` of them (`WeilExplicit.exterior_mult_le`).
-/

open Complex Set Filter Topology Metric MeasureTheory Asymptotics

namespace Masullo.Recurrence

/-- Zeta is self-recurrent with positive upper density on `θ < re s < 1`: for every closed disc
in the strip and every `ε > 0` there is `c > 0` such that, for arbitrarily large `T`, the shifts
`τ ∈ [0, T]` with `‖ζ(s + iτ) - ζ(s)‖ < ε` at every point `s` of the disc have measure at least
`c T`. -/
def SelfRecurrent (θ : ℝ) : Prop :=
  ∀ z : ℂ, ∀ r : ℝ, closedBall z r ⊆ {s : ℂ | θ < s.re ∧ s.re < 1} → ∀ ε > 0, ∃ c > 0,
    ∃ᶠ T in atTop, ENNReal.ofReal (c * T) ≤ volume {τ ∈ Icc (0 : ℝ) T |
      ∀ s ∈ closedBall z r, ‖riemannZeta (s + τ * I) - riemannZeta s‖ < ε}

/-- For `κ < 1`, `x^κ log² (2x + 4) = o(x)`. -/
theorem isLittleO_rpow_mul_log_sq {κ : ℝ} (hκ : κ < 1) :
    (fun x : ℝ => x ^ κ * Real.log (2 * x + 4) ^ 2) =o[atTop] fun x => x := by
  have h1 : (fun x : ℝ => Real.log (2 * x + 4) ^ 2) =O[atTop] fun x => Real.log x ^ 2 := by
    refine IsBigO.of_bound 4 ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have h0 : 0 ≤ Real.log (2 * x + 4) := Real.log_nonneg (by linarith)
    have h2 := Real.log_le_log (by linarith) (show 2 * x + 4 ≤ x ^ 2 by nlinarith)
    rw [Real.log_pow] at h2
    have h3 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    push_cast at h2
    nlinarith
  have h2 : (fun x : ℝ => Real.log x ^ 2) =o[atTop] fun x => x ^ (1 - κ) := by
    simpa [Real.rpow_two] using isLittleO_log_rpow_rpow_atTop 2 (sub_pos.2 hκ)
  refine ((isBigO_refl (fun x : ℝ => x ^ κ) atTop).mul_isLittleO
    (h1.trans_isLittleO h2)).congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_add hx]
  simp

/-- For `κ < 1` and `c > 0`, eventually `B (T + b)^κ log² (2(T + b) + 4) < c T`. -/
theorem eventually_rpow_mul_log_sq_lt {κ : ℝ} (hκ : κ < 1) (B b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, B * ((T + b) ^ κ * Real.log (2 * (T + b) + 4) ^ 2) < c * T := by
  have h := (isLittleO_rpow_mul_log_sq hκ).comp_tendsto
    (tendsto_atTop_add_const_right _ b tendsto_id)
  have hO : (fun T : ℝ => T + b) =O[atTop] fun T => T := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop |b|] with T hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith [neg_abs_le b])]
    linarith [le_abs_self T, neg_abs_le b, le_abs_self b]
  have := ((h.trans_isBigO hO).const_mul_left B).bound (half_pos hc)
  filter_upwards [this, eventually_ge_atTop 1] with T hT hT1
  simp only [Function.comp_apply, id, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < T)]
    at hT
  have hcT : 0 < c * T := mul_pos hc (by linarith)
  linarith [le_abs_self (B * ((T + b) ^ κ * Real.log (2 * (T + b) + 4) ^ 2))]

/-- **Self-recurrence rules out zeros.** For `θ ≥ 1/2`, if zeta is self-recurrent with positive
upper density on `θ < re s < 1`, it has no zero with real part greater than `θ`. -/
theorem riemannZeta_ne_zero_of_selfRecurrent {θ : ℝ} (hθ : 1 / 2 ≤ θ) (h : SelfRecurrent θ) :
    ∀ z : ℂ, θ < z.re → riemannZeta z ≠ 0 := by
  intro ρ hρθ hρ0
  have hρ1 : ρ.re < 1 := not_le.1 fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hρ0
  have hne1 : ρ ≠ 1 := fun e => by simp [e] at hρ1
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hne1
  have hiso : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 :=
    han.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun hz => WeilExplicit.zeta_order_ne_top hne1 (analyticOrderAt_eq_top.2 hz)
  obtain ⟨r0, hr0, hball⟩ := Metric.mem_nhdsWithin_iff.1 hiso
  set r := min (r0 / 2) (min ((ρ.re - θ) / 2) ((1 - ρ.re) / 2))
  have hr : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hr1 : r ≤ r0 / 2 := min_le_left _ _
  have hr2 : r ≤ (ρ.re - θ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (1 - ρ.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hre (s : ℂ) (hs : s ∈ closedBall ρ r) : |s.re - ρ.re| ≤ r := by
    rw [← sub_re]; exact (abs_re_le_norm _).trans (mem_closedBall_iff_norm.1 hs)
  have him (s : ℂ) (hs : s ∈ closedBall ρ r) : |s.im - ρ.im| ≤ r := by
    rw [← sub_im]; exact (abs_im_le_norm _).trans (mem_closedBall_iff_norm.1 hs)
  have hsub : closedBall ρ r ⊆ {s : ℂ | θ < s.re ∧ s.re < 1} := fun s hs => by
    have := abs_le.1 (hre s hs)
    exact ⟨by linarith, by linarith⟩
  have hs1 (s : ℂ) (hs : s ∈ closedBall ρ r) (τ : ℝ) : s + τ * I ≠ 1 := fun e => by
    have := congrArg re e
    simp at this
    linarith [(hsub hs).2]
  have hsph (s : ℂ) (hs : s ∈ sphere ρ r) : riemannZeta s ≠ 0 := by
    refine hball ⟨mem_ball.2 (by rw [mem_sphere.1 hs]; linarith), fun e => ?_⟩
    rw [mem_singleton_iff.1 e, mem_sphere, dist_self] at hs
    exact hr.ne hs
  have hcont : ContinuousOn (fun s => ‖riemannZeta s‖) (sphere ρ r) := fun s hs => by
    have := hs1 s (sphere_subset_closedBall hs) 0
    simp only [ofReal_zero, zero_mul, add_zero] at this
    exact (differentiableAt_riemannZeta this).continuousAt.norm.continuousWithinAt
  obtain ⟨s0, hs0, hmin⟩ :=
    (isCompact_sphere ρ r).exists_isMinOn (NormedSpace.sphere_nonempty.2 hr.le) hcont
  set m := ‖riemannZeta s0‖
  have hm : 0 < m := norm_pos_iff.2 (hsph s0 hs0)
  obtain ⟨c, hc, hfreq⟩ := h ρ r hsub (m / 2) (half_pos hm)
  -- a good shift moves a zero into the disc
  have hcover (τ : ℝ)
      (hτ : ∀ s ∈ closedBall ρ r, ‖riemannZeta (s + τ * I) - riemannZeta s‖ < m / 2) :
      ∃ s ∈ closedBall ρ r, riemannZeta (s + τ * I) = 0 := by
    by_contra! hnz
    have hd : DiffContOnCl ℂ (fun s => (riemannZeta (s + τ * I))⁻¹) (ball ρ r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball ρ hr.ne']
      intro s hs
      have hz : DifferentiableAt ℂ (fun s => riemannZeta (s + τ * I)) s :=
        (differentiableAt_riemannZeta (hs1 s hs τ)).comp s (differentiableAt_id.add_const _)
      exact (hz.inv (hnz s hs)).differentiableWithinAt
    have hb := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (C := 2 / m)
      ?_ (subset_closure (mem_ball_self hr))
    · have h0 := hτ ρ (mem_closedBall_self hr.le)
      rw [hρ0, sub_zero] at h0
      have hpos : 0 < ‖riemannZeta (ρ + τ * I)‖ :=
        norm_pos_iff.2 (hnz ρ (mem_closedBall_self hr.le))
      rw [norm_inv, inv_le_comm₀ hpos (by positivity), inv_div] at hb
      linarith
    · rw [frontier_ball ρ hr.ne']
      intro s hs
      have h1 := hτ s (sphere_subset_closedBall hs)
      have h2 : m ≤ ‖riemannZeta s‖ := hmin hs
      have h3 := norm_sub_norm_le (riemannZeta s) (riemannZeta (s + τ * I))
      rw [norm_sub_rev] at h3
      have h4 : m / 2 < ‖riemannZeta (s + τ * I)‖ := by linarith
      rw [norm_inv, inv_le_comm₀ (by linarith) (by positivity), inv_div]
      exact h4.le
  -- counting the shifted zeros
  set a := ρ.re - r - 1 / 2
  have ha : 0 < a := by simp only [a]; linarith
  obtain ⟨A, hA, hcount⟩ := WeilExplicit.exterior_mult_le ha
  set κ := 1 - min (a / 2) (1 / 8) ^ 2 / 3
  have hκ : κ < 1 := by
    have : 0 < min (a / 2) (1 / 8) := lt_min (by linarith) (by norm_num)
    simp only [κ]; nlinarith
  set b := |ρ.im| + r + 2
  obtain ⟨T, hT, hTlt, hT0⟩ := (hfreq.and_eventually
    ((eventually_rpow_mul_log_sq_lt hκ (2 * r * A) b hc).and (eventually_ge_atTop 0))).exists
  set X := T + b
  have hX : 2 ≤ X := by simp only [X, b]; linarith [abs_nonneg ρ.im]
  have hfin := ((isCompact_Icc (a := ρ.re - r) (b := ρ.re + r)).reProdIm
    (isCompact_Icc (a := -X) (b := X))).inter_riemannZetaZeros_finite
  set Z := hfin.toFinset
  have hcov : {τ ∈ Icc (0 : ℝ) T |
      ∀ s ∈ closedBall ρ r, ‖riemannZeta (s + τ * I) - riemannZeta s‖ < m / 2} ⊆
      ⋃ w ∈ Z, Icc (w.im - ρ.im - r) (w.im - ρ.im + r) := by
    rintro τ ⟨hτ, hgood⟩
    obtain ⟨s, hs, hz⟩ := hcover τ hgood
    have h1 := abs_le.1 (hre s hs)
    have h2 := abs_le.1 (him s hs)
    have h3 := abs_le.1 (le_refl |ρ.im|)
    refine mem_iUnion₂.2 ⟨s + τ * I, hfin.mem_toFinset.2 ⟨mem_reProdIm.2 ⟨?_, ?_⟩, hz⟩, ?_⟩
    · simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
      constructor <;> linarith
    · simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, X, b]
      constructor <;> nlinarith [hτ.1, hτ.2]
    · simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
      constructor <;> linarith
  have hvol := (measure_mono (μ := volume) hcov).trans (measure_biUnion_finset_le Z _)
  simp only [Real.volume_Icc] at hvol
  rw [← ENNReal.ofReal_sum_of_nonneg fun w _ => by linarith] at hvol
  have hle := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun w _ => by linarith)).1
    (hT.trans hvol)
  have hmult : ∑ w ∈ Z, (zeroMult w : ℝ) ≤ A * (X ^ κ * Real.log (2 * X + 4) ^ 2) := by
    refine hcount X hX Z fun w hw => ?_
    obtain ⟨hw, hz⟩ := hfin.mem_toFinset.1 hw
    obtain ⟨hwre, hwim⟩ := mem_reProdIm.1 hw
    refine ⟨⟨hz, by linarith [hwre.1], by linarith [hwre.2]⟩, ?_, abs_le.2 hwim⟩
    rw [abs_of_nonneg (by linarith [hwre.1])]
    linarith [hwre.1, show a = ρ.re - r - 1 / 2 from rfl]
  have hsum : ∑ w ∈ Z, ((w.im - ρ.im + r) - (w.im - ρ.im - r)) ≤
      2 * r * ∑ w ∈ Z, (zeroMult w : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hw, hz⟩ := hfin.mem_toFinset.1 hw
    obtain ⟨hwre, -⟩ := mem_reProdIm.1 hw
    have : (1 : ℝ) ≤ zeroMult w := Nat.one_le_cast.2
      (WeilExplicit.zeroMult_pos ⟨hz, by linarith [hwre.1], by linarith [hwre.2]⟩)
    nlinarith
  have : c * T ≤ 2 * r * A * (X ^ κ * Real.log (2 * X + 4) ^ 2) := by
    calc c * T ≤ _ := hle
      _ ≤ _ := hsum
      _ ≤ 2 * r * (A * (X ^ κ * Real.log (2 * X + 4) ^ 2)) := by gcongr
      _ = _ := by ring
  exact absurd hTlt (not_lt.2 this)

/-- **The trace identity from self-recurrence.** For `θ ≥ 1/2`, if zeta is self-recurrent with
positive upper density on `θ < re s < 1`, the trace at every width `a > θ - 1/2` is Weil's
functional for every test function. -/
theorem trace_eq_efFunctional_of_selfRecurrent {θ a : ℝ} (hθ : 1 / 2 ≤ θ)
    (h : SelfRecurrent θ) (ha : 0 < a) (hθa : θ - 1 / 2 < a) (φ : TestFunction) :
    Trace.HasTrace (Trace.induced ha φ) φ.efFunctional :=
  Window.trace_eq_efFunctional_of_ne_zero ha hθa (riemannZeta_ne_zero_of_selfRecurrent hθ h) φ

end Masullo.Recurrence
