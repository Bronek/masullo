import Masullo.Window

/-!
# Smoothed sums and zeros of zeta

Let `b` have an absolutely convergent Dirichlet series on `Re s > 1` with
`L(b, s) ζ(s) G(s) = 1` there, for some `G` holomorphic on `Re s > β`, where `β ≥ 0`. If for
every smooth `W` with compact support in `(0, ∞)` the smoothed sum `∑ b n W (n / D)` is
`O(D ^ β)` for `D ≥ 1`, then zeta has no zeros in `Re s > β`. This is
`riemannZeta_ne_zero_of_smoothedBound`, a smoothed form of Landau's criterion; the converse is not
asserted.

The proof takes a test function `W` with `mellin W ρ ≠ 0`. The Mellin transform of
`g t = ∑ b n W (n t)` is `L(b, s) mellin W s` on `Re s > 1` (classical), and the bound makes it
holomorphic on `Re s > β`. On the quarter plane `Re s > β, Im s > 0`, which avoids the pole of
zeta, `mellin g · ζ · G` agrees with `mellin W` by the identity theorem, so a zero `ρ` there would
make `mellin W ρ` vanish. Zeros below the real axis reduce to this case by conjugation; real zeros
in `(0, 1)` are excluded separately (`Window.riemannZeta_ofReal_ne_zero`).

For `b = μ ∗ χ₃μ` (`eisensteinMoebius`), `G` is the Dirichlet L-function of `χ₃`, which is entire,
and the criterion gives the trace identity of `Masullo.Trace` at every width `a > 0` with
`a > β - 1/2` (`hasTrace_of_smoothedBound`).
-/

open MeasureTheory Complex Set Filter Topology Asymptotics
open scoped ContDiff ComplexConjugate LSeries.notation ArithmeticFunction.Moebius

namespace Masullo.Smoothed

/-- `∑ b n W (n / D)`. -/
noncomputable def smoothedSum (b : ℕ → ℂ) (W : ℝ → ℂ) (D : ℝ) : ℂ := ∑' n : ℕ, b n * W (n / D)

/-- For every smooth `W` with compact support in `(0, ∞)`, the smoothed sum is `O(D ^ β)` for
`D ≥ 1`, with a constant depending on `W`. -/
def SmoothedBound (b : ℕ → ℂ) (β : ℝ) : Prop :=
  ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
    ∃ C, ∀ D : ℝ, 1 ≤ D → ‖smoothedSum b W D‖ ≤ C * D ^ β

section Criterion

variable {b : ℕ → ℂ} {W : ℝ → ℂ} {R : ℝ}

private lemma isBigO_of_eventually_zero {l : Filter ℝ} {f : ℝ → ℂ} {k : ℝ → ℝ}
    (h : ∀ᶠ t in l, f t = 0) : f =O[l] k :=
  IsBigO.of_bound 0 (h.mono fun t ht => by simp [ht])

private lemma integral_rpow_norm_comp_mul (W : ℝ → ℂ) (σ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖W (c * t)‖ =
      c ^ (-σ) * ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖W t‖ := by
  have h := integral_comp_mul_left_Ioi (fun u => u ^ (σ - 1) * ‖W u‖) 0 hc
  rw [mul_zero] at h
  calc ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖W (c * t)‖
      = ∫ t in Ioi (0 : ℝ), c ^ (1 - σ) * ((c * t) ^ (σ - 1) * ‖W (c * t)‖) :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht => by
          rw [Real.mul_rpow hc.le (le_of_lt ht), ← mul_assoc, ← mul_assoc, ← Real.rpow_add hc,
            show 1 - σ + (σ - 1) = 0 by ring, Real.rpow_zero, one_mul]
    _ = c ^ (-σ) * ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖W t‖ := by
      rw [integral_const_mul, h, smul_eq_mul, ← mul_assoc, ← Real.rpow_neg_one,
        ← Real.rpow_add hc, show 1 - σ + -1 = -σ by ring]

private lemma tsum_eq_sum_range (hR : ∀ x, R < x → W x = 0) {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    ∑' n : ℕ, b n * W (n * t) = ∑ n ∈ Finset.range (⌈R / ε⌉₊ + 1), b n * W (n * t) := by
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have h1 : R / ε < n := by
    have h2 := Nat.le_ceil (R / ε)
    have h3 : ((⌈R / ε⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h3
    linarith
  rw [div_lt_iff₀ hε] at h1
  rw [hR _ (h1.trans_le (by gcongr)), mul_zero]

private lemma continuousOn_tsum (hW : Continuous W) (hR : ∀ x, R < x → W x = 0) :
    ContinuousOn (fun t : ℝ => ∑' n : ℕ, b n * W (n * t)) (Ioi 0) := by
  intro t₀ ht₀
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.congr
    (f := fun t : ℝ => ∑ n ∈ Finset.range (⌈R / (t₀ / 2)⌉₊ + 1), b n * W (n * t))
    (by fun_prop) ?_
  filter_upwards [lt_mem_nhds (half_lt_self (mem_Ioi.1 ht₀))] with t ht
  exact (tsum_eq_sum_range hR (half_pos (mem_Ioi.1 ht₀)) ht.le).symm

private lemma false_of_zero {G : ℂ → ℂ} {β : ℝ}
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable b s)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries b s * riemannZeta s * G s = 1)
    (hG : ∀ s : ℂ, β < s.re → DifferentiableAt ℂ G s)
    (h : SmoothedBound b β) {ρ : ℂ} (hρ : β < ρ.re) (him : 0 < ρ.im)
    (hz : riemannZeta ρ = 0) : False := by
  obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero ρ
  set W := φ.toFun
  have hW0 : ∀ x, x ≤ 1 → W x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => (not_lt.2 hx) (φ.tsupport_subset h')
  obtain ⟨R, hR'⟩ := φ.hasCompactSupport.isCompact.bddAbove
  have hR : ∀ x, R < x → W x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => (not_le.2 hx) (hR' h')
  have hconv : ∀ s : ℂ, MellinConvergent W s := fun s =>
    mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
      (φ.contDiff.continuous.locallyIntegrable.locallyIntegrableOn _)
      (isBigO_of_eventually_zero ((eventually_gt_atTop R).mono hR)) (lt_add_one _)
      (isBigO_of_eventually_zero (by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with t ht
        exact hW0 t (le_of_lt ht)))
      (sub_one_lt _)
  set g : ℝ → ℂ := fun t => ∑' n : ℕ, b n * W (n * t)
  have hg_top : ∀ᶠ t in atTop, g t = 0 := by
    filter_upwards [eventually_gt_atTop (max R 0)] with t ht
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hW0 0 zero_le_one]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [hR, mul_zero]
      nlinarith [le_max_left R 0, le_max_right R 0]
  have hg_bot : g =O[𝓝[>] 0] (· ^ (-β)) := by
    obtain ⟨C, hC⟩ := h W φ.contDiff φ.hasCompactSupport
      (φ.tsupport_subset.trans (Ioi_subset_Ioi zero_le_one))
    refine IsBigO.of_bound C ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ⟨ht0, ht1⟩
    have := hC t⁻¹ ((one_le_inv₀ ht0).2 ht1.le)
    simp only [smoothedSum, div_inv_eq_mul, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le] at this
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
  have hdiff : ∀ s : ℂ, β < s.re → DifferentiableAt ℂ (mellin g) s := fun s hs =>
    mellin_differentiableAt_of_isBigO_rpow
      ((continuousOn_tsum φ.contDiff.continuous hR).locallyIntegrableOn measurableSet_Ioi)
      (isBigO_of_eventually_zero hg_top) (lt_add_one s.re) hg_bot hs
  have hid : ∀ s : ℂ, 1 < s.re → mellin g s = LSeries b s * mellin W s := by
    intro s hs
    have hterm : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (b n * W (n * t)) =
        LSeries.term b s n * mellin W s := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hW0 0 zero_le_one]
      · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
        have h1 := mellin_comp_mul_left W s hn'
        simp only [mellin, smul_eq_mul] at h1
        rw [LSeries.term_of_ne_zero hn, mellin]
        calc ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (b n * W (n * t))
            = b n * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * W (n * t) := by
              rw [← integral_const_mul]
              congr 1
              ext t
              ring
          _ = _ := by
              rw [h1, ofReal_natCast, cpow_neg]
              simp only [smul_eq_mul]
              ring
    have hint : ∀ n : ℕ, Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * (b n * W (n * t)))
        (volume.restrict (Ioi 0)) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hW0 0 zero_le_one]
      · have h1 := (MellinConvergent.comp_mul_left
          (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))).2 (hconv s)
        refine (h1.const_mul (b n)).congr (Eventually.of_forall fun t => ?_)
        simp only [smul_eq_mul]
        ring
    have hnorm : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * (b n * W (n * t))‖ =
        ‖LSeries.term b s n‖ * ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * ‖W t‖ := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hW0 0 zero_le_one]
      · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
        calc ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * (b n * W (n * t))‖
            = ‖b n‖ * ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * ‖W (n * t)‖ := by
              rw [← integral_const_mul]
              refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
              simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
              ring
          _ = ‖LSeries.term b s n‖ * ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * ‖W t‖ := by
              rw [integral_rpow_norm_comp_mul W _ hn', LSeries.norm_term_eq, if_neg hn,
                Real.rpow_neg hn'.le, div_eq_mul_inv]
              ring
    have hsumm : Summable fun n : ℕ =>
        ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * (b n * W (n * t))‖ := by
      simp_rw [hnorm]
      exact (hsum s hs).norm.mul_right _
    calc mellin g s = ∫ t in Ioi (0 : ℝ), ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (b n * W (n * t)) := by
          rw [mellin]
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [g, smul_eq_mul, tsum_mul_left]
      _ = ∑' n : ℕ, ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (b n * W (n * t)) :=
          (integral_tsum_of_summable_integral_norm hint hsumm).symm
      _ = LSeries b s * mellin W s := by
          rw [tsum_congr hterm, LSeries, tsum_mul_right]
  set U : Set ℂ := {s | β < s.re} ∩ {s | 0 < s.im}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)
  have h1 : AnalyticOnNhd ℂ (fun s => mellin g s * riemannZeta s * G s) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hU
    have hs1 : s ≠ 1 := fun e => by simp [U, e] at hs
    exact (((hdiff s hs.1).mul (differentiableAt_riemannZeta hs1)).mul
      (hG s hs.1)).differentiableWithinAt
  have h2 : AnalyticOnNhd ℂ (mellin W) U :=
    (φ.differentiable_hat.differentiableOn : DifferentiableOn ℂ (mellin W) U).analyticOnNhd hU
  set z₀ : ℂ := ((max β 1 + 1 : ℝ) : ℂ) + I
  have hz₀re : z₀.re = max β 1 + 1 := by simp [z₀]
  have hz₀ : z₀ ∈ U := ⟨show β < z₀.re by rw [hz₀re]; linarith [le_max_left β 1], by simp [z₀]⟩
  have heq := h1.eqOn_of_preconnected_of_eventuallyEq h2
    ((convex_halfSpace_re_gt β).inter (convex_halfSpace_im_gt 0)).isPreconnected hz₀ (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < z₀.re by rw [hz₀re]; linarith [le_max_right β 1])] with s hs
      rw [hid s hs, mul_comm (LSeries b s), mul_assoc, mul_assoc, ← mul_assoc (LSeries b s),
        hL s hs, mul_one])
  have := heq (show ρ ∈ U from ⟨hρ, him⟩)
  simp only [hz, mul_zero, zero_mul] at this
  exact hφ this.symm

/-- **Smoothed Landau criterion.** If the Dirichlet series of `b` inverts `ζ · G` on `Re s > 1`,
with `G` holomorphic on `Re s > β`, then a smoothed bound `O(D ^ β)` with `β ≥ 0` rules out zeros
of zeta in `Re s > β`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_smoothedBound {b : ℕ → ℂ} {G : ℂ → ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable b s)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries b s * riemannZeta s * G s = 1)
    (hG : ∀ s : ℂ, β < s.re → DifferentiableAt ℂ G s)
    (h : SmoothedBound b β) {ρ : ℂ} (hρ : β < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hz
  rcases le_or_gt 1 ρ.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  rcases lt_trichotomy ρ.im 0 with hi | hi | hi
  · refine false_of_zero hsum hL hG h (ρ := conj ρ) (by simpa using hρ) (by simpa using hi) ?_
    rw [riemannZeta_conj, hz, map_zero]
  · have e : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [hi])
    refine Window.riemannZeta_ofReal_ne_zero (hβ.trans_lt hρ) h1 ?_
    rwa [← e]
  · exact false_of_zero hsum hL hG h hρ hi hz

end Criterion

/-! ### The Dedekind zeta function of `ℚ(√-3)` -/

/-- The nontrivial Dirichlet character mod `3`, as the quadratic character of `ZMod 3`. -/
noncomputable def chi3 : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

lemma chi3_ne_one : chi3 ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).2
    (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; decide))

/-- `μ ∗ μχ₃`: the Dirichlet series is `1 / (ζ(s) L(s, χ₃))`, the inverse of the Dedekind zeta
function of `ℚ(√-3)`. Here `χ₃` is `chi3`. -/
noncomputable def eisensteinMoebius : ℕ → ℂ := ↗μ ⍟ (↗chi3 * ↗μ)

/-- The smoothed criterion for `μ ∗ μχ₃`, with `G = L(·, χ₃)`. -/
theorem riemannZeta_ne_zero_of_smoothedBound_eisenstein {β : ℝ} (hβ : 0 ≤ β)
    (h : SmoothedBound eisensteinMoebius β) {ρ : ℂ} (hρ : β < ρ.re) : riemannZeta ρ ≠ 0 := by
  refine riemannZeta_ne_zero_of_smoothedBound (G := DirichletCharacter.LFunction chi3) hβ
    (fun s hs => ?_) (fun s hs => ?_)
    (fun s _ => DirichletCharacter.differentiable_LFunction chi3_ne_one s) h hρ
  · have hμ := ArithmeticFunction.LSeriesSummable_moebius_iff.2 hs
    exact hμ.convolution (DirichletCharacter.LSeriesSummable_mul chi3 hμ)
  · have hμ := ArithmeticFunction.LSeriesSummable_moebius_iff.2 hs
    rw [eisensteinMoebius, LSeries_convolution' hμ (DirichletCharacter.LSeriesSummable_mul chi3 hμ),
      DirichletCharacter.LFunction_eq_LSeries _ hs, ← LSeries_one_eq_riemannZeta hs]
    linear_combination (LSeries ↗chi3 s * LSeries (↗chi3 * ↗μ) s) *
      LSeries_one_mul_Lseries_moebius hs + DirichletCharacter.LSeries.mul_mu_eq_one chi3 hs

/-- The trace identity at every width `a > 0` with `a > β - 1/2`. -/
theorem hasTrace_of_smoothedBound {β a : ℝ} (hβ : 0 ≤ β) (ha : 0 < a) (hab : β - 1 / 2 < a)
    (h : SmoothedBound eisensteinMoebius β) (φ : TestFunction) :
    Trace.HasTrace (Trace.induced ha φ) φ.efFunctional :=
  Window.trace_eq_efFunctional_of_ne_zero ha hab
    (fun _ hz => riemannZeta_ne_zero_of_smoothedBound_eisenstein hβ h hz) φ

end Masullo.Smoothed
