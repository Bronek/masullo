import Mathlib

/-!
# Strength of the vanishing of the off-critical zero sum

The vanishing of `∑ N(ρ) φ̂(ρ - 1/2)` over zeta zeros with `|Re ρ - 1/2| ≥ a`, for every smooth `φ`
with compact support in `(1, ∞)`, is equivalent to the absence of such zeros. For all `a > 0`
together it is equivalent to the Riemann hypothesis.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Masullo

/-! ### Exponential sums -/

section ExpSum

variable {ι : Type*} {l c : ι → ℂ}

/-- The range of a family with no finite accumulation point is closed. -/
lemma isOpen_compl_range (hd : ∀ z, ∃ r > 0, ∀ i, l i ≠ z → r ≤ ‖z - l i‖) :
    IsOpen (range l)ᶜ := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨r, hr, h⟩ := hd z
  refine ⟨r, hr, ?_⟩
  rintro w hw ⟨i, rfl⟩
  have := h i fun e => hz ⟨i, e⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hw
  linarith

/-- Away from its poles, `∑ cᵢ / (s - lᵢ)` is holomorphic. -/
lemma differentiableOn_cauchySum (hd : ∀ z, ∃ r > 0, ∀ i, l i ≠ z → r ≤ ‖z - l i‖)
    (hc : Summable fun i => ‖c i‖) :
    DifferentiableOn ℂ (fun s => ∑' i, c i / (s - l i)) (range l)ᶜ := by
  intro z hz
  obtain ⟨r, hr, h⟩ := hd z
  have key : ∀ i, ∀ w ∈ Metric.ball z (r / 2), r / 2 ≤ ‖w - l i‖ := by
    intro i w hw
    have h1 := h i fun e => hz ⟨i, e⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hw
    have := norm_add_le (z - w) (w - l i)
    rw [sub_add_sub_cancel] at this
    linarith
  have hD := differentiableOn_tsum_of_summable_norm (F := fun i s => c i / (s - l i))
    (U := Metric.ball z (r / 2)) (hc.div_const (r / 2))
    (fun i w hw => by
      have : w - l i ≠ 0 := norm_pos_iff.1 (by linarith [key i w hw])
      fun_prop (disch := exact this))
    Metric.isOpen_ball
    (fun i w hw => by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (key i w hw))
  exact ((hD z (Metric.mem_ball_self (by positivity))).differentiableAt
    (Metric.ball_mem_nhds z (by positivity))).differentiableWithinAt

/-- The Laplace transform of a vanishing exponential sum vanishes. -/
lemma cauchySum_eq_zero [Countable ι] {B : ℝ} (hB : ∀ i, (l i).re ≤ B)
    (hc : Summable fun i => ‖c i‖)
    (h : ∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * l i)) 0) {s : ℂ} (hs : B < s.re) :
    ∑' i, c i / (s - l i) = 0 := by
  have hre : ∀ i, (l i - s).re < 0 := fun i => by rw [sub_re]; linarith [hB i]
  have hint : ∀ i, IntegrableOn (fun x : ℝ => c i * exp ((l i - s) * x)) (Ioi 0) := fun i =>
    (integrableOn_exp_mul_complex_Ioi (hre i) 0).const_mul _
  have hval : ∀ i, ∫ x in Ioi (0 : ℝ), c i * exp ((l i - s) * x) = c i / (s - l i) := by
    intro i
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hre i)]
    rw [← neg_sub s (l i), neg_div_neg_eq]
    simp [div_eq_mul_inv]
  have hn : ∀ i, ∫ x in Ioi (0 : ℝ), ‖c i * exp ((l i - s) * x)‖ ≤ ‖c i‖ / (s.re - B) := by
    intro i
    have e : ∀ x : ℝ, ‖c i * exp ((l i - s) * x)‖ = ‖c i‖ * Real.exp ((l i - s).re * x) := by
      intro x
      rw [norm_mul, norm_exp, re_mul_ofReal]
    simp_rw [e]
    rw [integral_const_mul, integral_exp_mul_Ioi (hre i), mul_zero, Real.exp_zero, neg_div,
      ← div_neg, mul_one_div]
    refine div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) ?_
    rw [sub_re]; linarith [hB i]
  have hsum := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun i x => c i * exp ((l i - s) * x)) hint
    (Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) hn
      (hc.div_const _))
  have hz : ∫ x in Ioi (0 : ℝ), ∑' i, c i * exp ((l i - s) * x) = 0 := by
    rw [setIntegral_congr_fun (g := fun _ => 0) measurableSet_Ioi, integral_zero]
    intro x hx
    have h2 := (h x (le_of_lt hx)).mul_right (exp (-s * x))
    rw [zero_mul] at h2
    refine (h2.congr_fun fun i => ?_).tsum_eq
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [hz] at hsum
  simp_rw [hval] at hsum
  exact hsum.tsum_eq

/-- An absolutely convergent exponential sum that vanishes on `[0, ∞)`, and whose exponents have
no finite accumulation point and bounded real parts, has only zero coefficients. -/
theorem eq_zero_of_hasSum_exp [Countable ι] (hl : Function.Injective l) {B : ℝ}
    (hB : ∀ i, (l i).re ≤ B) (hd : ∀ z, ∃ r > 0, ∀ i, l i ≠ z → r ≤ ‖z - l i‖)
    (h : ∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * l i)) 0) (j : ι) : c j = 0 := by
  classical
  have hc : Summable fun i => ‖c i‖ := by simpa using (h 0 le_rfl).summable.norm
  have hU := isOpen_compl_range hd
  have hA : AnalyticOnNhd ℂ (fun s => ∑' i, c i / (s - l i)) (range l)ᶜ :=
    (differentiableOn_cauchySum hd hc).analyticOnNhd hU
  have hconn : IsPreconnected (range l)ᶜ :=
    ((countable_range l).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hp : (((B + 1 : ℝ) : ℂ)) ∈ (range l)ᶜ := by
    rintro ⟨i, hi⟩
    have := hB i
    rw [hi, ofReal_re] at this
    linarith
  have hF : EqOn (fun s => ∑' i, c i / (s - l i)) 0 (range l)ᶜ := by
    refine hA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hp ?_
    have : {s : ℂ | B < s.re} ∈ 𝓝 ((B + 1 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [this] with s hs using cauchySum_eq_zero hB hc h hs
  obtain ⟨r, hr, hj⟩ := hd (l j)
  set M := ∑' i, ‖c i‖ / (r / 2)
  have hM : Summable fun i => ‖c i‖ / (r / 2) := hc.div_const _
  have bound : ∀ s, s ≠ l j → ‖s - l j‖ < r / 2 → ‖c j‖ ≤ ‖s - l j‖ * M := by
    intro s hs hsr
    have far : ∀ i, i ≠ j → r / 2 ≤ ‖s - l i‖ := by
      intro i hi
      have h1 := hj i fun e => hi (hl e)
      have := norm_add_le (l j - s) (s - l i)
      rw [sub_add_sub_cancel, norm_sub_rev (l j) s] at this
      linarith
    have hsU : s ∈ (range l)ᶜ := by
      rintro ⟨i, rfl⟩
      have := far i fun e => hs (by rw [e])
      simp at this
      linarith
    have le : ∀ i, ‖if i = j then 0 else c i / (s - l i)‖ ≤ ‖c i‖ / (r / 2) := by
      intro i
      split_ifs with e
      · simp only [norm_zero]; positivity
      · rw [norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (far i e)
    have hne : s - l j ≠ 0 := sub_ne_zero.2 hs
    have hS : Summable fun i => c i / (s - l i) := by
      have h1 : Summable fun i => if i = j then 0 else c i / (s - l i) :=
        Summable.of_norm_bounded hM le
      refine h1.congr_cofinite ?_
      filter_upwards [(finite_singleton j).compl_mem_cofinite] with i hi
      exact if_neg hi
    have h0 := hF hsU
    simp only [Pi.zero_apply] at h0
    rw [hS.tsum_eq_add_tsum_ite j] at h0
    have h1 : ‖c j / (s - l j)‖ ≤ M := by
      rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
      exact tsum_of_norm_bounded hM.hasSum le
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hne)] at h1
    linarith
  have hlim : Tendsto (fun s => ‖s - l j‖ * M) (𝓝[≠] (l j)) (𝓝 0) := by
    have : Continuous fun s => ‖s - l j‖ * M := by fun_prop
    simpa using (this.tendsto (l j)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] (l j), ‖c j‖ ≤ ‖s - l j‖ * M := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (l j) (half_pos hr))] with s h1 h2
    exact bound s h1 (by simpa [dist_eq_norm] using h2)
  exact norm_le_zero_iff.1 (ge_of_tendsto hlim hev)

end ExpSum

/-! ### Test functions -/

/-- Smooth functions `ℝ → ℂ` with compact support in `(1, ∞)`. -/
structure TestFunction where
  /-- The underlying function. -/
  toFun : ℝ → ℂ
  contDiff : ContDiff ℝ ∞ toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ Ioi 1

namespace TestFunction

/-- The Mellin transform `φ̂(z) = ∫₀^∞ φ(t) t^z dt/t`. -/
noncomputable def hat (φ : TestFunction) (z : ℂ) : ℂ := mellin φ.toFun z

lemma hat_eq (φ : TestFunction) (z : ℂ) :
    φ.hat z = ∫ t in Ioi (0 : ℝ), φ.toFun t * (t : ℂ) ^ z / t := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt ht)
  simp only [smul_eq_mul, cpow_sub _ _ this, cpow_one]
  ring

/-- The multiplicative translate `t ↦ φ(t e^{-x})`, for `x ≥ 0`. -/
noncomputable def translate (φ : TestFunction) (x : ℝ) (hx : 0 ≤ x) : TestFunction where
  toFun t := φ.toFun (Real.exp (-x) * t)
  contDiff := φ.contDiff.comp (by fun_prop)
  hasCompactSupport :=
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ _ (Real.exp_pos (-x)).ne')
  tsupport_subset := by
    intro t ht
    have h1 := φ.tsupport_subset
      (tsupport_comp_subset_preimage φ.toFun (f := fun t => Real.exp (-x) * t) (by fun_prop) ht)
    simp only [mem_Ioi] at h1 ⊢
    have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 := Real.exp_pos (-x)
    by_contra h4
    nlinarith

lemma hat_translate (φ : TestFunction) (x : ℝ) (hx : 0 ≤ x) (z : ℂ) :
    (φ.translate x hx).hat z = exp (x * z) * φ.hat z := by
  unfold hat translate
  rw [mellin_comp_mul_left _ _ (Real.exp_pos _), smul_eq_mul]
  congr 1
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos (-x)).ne'), ← ofReal_log
    (Real.exp_pos _).le, Real.log_exp]
  push_cast
  ring_nf

/-- The Mellin transform does not vanish identically on test functions at any point. -/
lemma exists_hat_ne_zero (z : ℂ) : ∃ φ : TestFunction, φ.hat z ≠ 0 := by
  let b : ContDiffBump (2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hbs : tsupport (b : ℝ → ℝ) ⊆ Ioi 1 := by
    rw [b.tsupport_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq] at ht
    have := (abs_le.1 ht).1
    change -(1 / 2 : ℝ) ≤ _ at this
    rw [mem_Ioi]; linarith
  let f : ℝ → ℂ := fun t => (b t : ℂ) * exp (-z * Real.log t)
  have hsub : tsupport f ⊆ tsupport (b : ℝ → ℝ) := by
    refine closure_mono fun t ht => ?_
    simp only [Function.mem_support, f] at ht ⊢
    intro h
    simp [h] at ht
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t ∈ tsupport f
    · have ht0 : t ≠ 0 := by
        have : (1 : ℝ) < t := hbs (hsub ht)
        linarith
      have h1 : ContDiffAt ℝ ∞ (fun t => (b t : ℂ)) t :=
        ofRealCLM.contDiff.contDiffAt.comp t b.contDiffAt
      have h2 : ContDiffAt ℝ ∞ (fun t => ((Real.log t : ℝ) : ℂ)) t :=
        ofRealCLM.contDiff.contDiffAt.comp t (Real.contDiffAt_log.2 ht0)
      exact h1.mul (contDiffAt_const.mul h2).cexp
    · have : f =ᶠ[𝓝 t] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 ht
      exact contDiffAt_const.congr_of_eventuallyEq this
  refine ⟨⟨f, hf, b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport f) hsub,
    hsub.trans hbs⟩, ?_⟩
  have e : mellin f z = ∫ t in Ioi (0 : ℝ), ((b t / t : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt ht)
    simp only [f, smul_eq_mul, cpow_def_of_ne_zero ht', ← ofReal_log (le_of_lt ht)]
    rw [mul_left_comm, ← Complex.exp_add,
      show (Real.log t : ℂ) * (z - 1) + -z * Real.log t = ((-Real.log t : ℝ) : ℂ) by
        push_cast; ring, ← ofReal_exp, Real.exp_neg, Real.exp_log ht]
    push_cast
    rfl
  change mellin f z ≠ 0
  rw [e, integral_complex_ofReal, ofReal_ne_zero]
  have hcont : Continuous fun t : ℝ => b t / t := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport (b : ℝ → ℝ)
    · have : (1 : ℝ) < t := hbs ht
      exact b.continuous.continuousAt.div continuousAt_id (by simp; linarith)
    · have hev : (fun t : ℝ => b t / t) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 ht] with u hu
        simp [hu]
      exact continuousAt_const.congr hev.symm
  have hcomp : HasCompactSupport fun t : ℝ => b t / t :=
    b.hasCompactSupport.mono fun t ht => by
      simp only [Function.mem_support] at ht ⊢
      exact fun h => ht (by simp [h])
  have hpos : 0 < ∫ t in Ioi (0 : ℝ), b t / t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · refine lt_of_lt_of_le ?_ (measure_mono (s := Metric.ball (2 : ℝ) (1 / 2)) ?_)
      · exact Metric.measure_ball_pos _ _ (by norm_num)
      · intro t ht
        have hb : b t ≠ 0 := by
          rw [← Function.mem_support, b.support_eq]; exact ht
        have : (1 : ℝ) < t := hbs (subset_tsupport _ hb)
        exact ⟨div_ne_zero hb (by linarith), by simp; linarith⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_nonneg b.nonneg (le_of_lt ht)
    · exact (hcont.integrable_of_hasCompactSupport hcomp).integrableOn
  exact hpos.ne'

end TestFunction

/-! ### Zeros of zeta -/

/-- Zeros of `ζ` in the open critical strip. -/
def stripZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- Zeros in the critical strip at distance at least `a` from the critical line. -/
def outerZeros (a : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2|}

/-- Zeros in the critical strip at distance less than `a` from the critical line. -/
def innerZeros (a : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.re - 1 / 2| < a}

/-- The multiplicity of `ρ` as a zero of `ζ`: its analytic order. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- The sum over zeros at distance at least `a` from the critical line converges to `0` on every
test function. -/
def ZeroSumVanishes (a : ℝ) : Prop :=
  ∀ φ : TestFunction,
    HasSum (fun ρ : outerZeros a => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) 0

/-- Around every point there is a punctured disc free of zeta zeros. -/
lemma exists_isolating_radius (z : ℂ) :
    ∃ r > 0, ∀ ρ, riemannZeta ρ = 0 → ρ ≠ z → r ≤ ‖z - ρ‖ := by
  have h := isClosed_and_discrete_iff.1
    ⟨isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros⟩ z
  rw [disjoint_principal_right, Metric.mem_nhdsWithin_iff] at h
  obtain ⟨r, hr, h⟩ := h
  refine ⟨r, hr, fun ρ h0 hne => ?_⟩
  by_contra hlt
  refine h ⟨?_, hne⟩ (mem_riemannZetaZeros.2 h0)
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  exact not_le.1 hlt

lemma countable_zeros : riemannZetaZeros.Countable := by
  have := isDiscrete_riemannZetaZeros.to_subtype
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

/-- Multiplicities are positive at zeros. -/
theorem zeroMult_pos {ρ : ℂ} (h : riemannZeta ρ = 0) : 0 < zeroMult ρ := by
  have h1 : ρ ≠ 1 := fun e => riemannZeta_one_ne_zero (e ▸ h)
  have hA : AnalyticAt ℂ riemannZeta ρ :=
    analyticOn_riemannZeta ρ h1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, hA.analyticOrderAt_eq_zero, not_not]; exact h
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hev
    obtain ⟨r, hr, hiso⟩ := exists_isolating_radius ρ
    have hev2 : ∀ᶠ z in 𝓝[≠] ρ, False := by
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds ρ hr)] with z hz hzne hzb
      have := hiso z hz hzne
      rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hzb
      linarith
    exact (Filter.eventually_false_iff_eq_bot.1 hev2 ▸ (inferInstance : (𝓝[≠] ρ).NeBot)).ne rfl
  rw [← Nat.cast_analyticOrderNatAt hnetop] at hne0
  exact Nat.pos_of_ne_zero (by exact_mod_cast hne0)

/-! ### The equivalences -/

/-- **Theorem A.** The outer zero sum vanishes iff there are no outer zeros. -/
theorem zeroSumVanishes_iff (a : ℝ) :
    ZeroSumVanishes a ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2| := by
  constructor
  · rintro h ⟨ρ₀, hρ₀⟩
    obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero (ρ₀ - 1 / 2)
    have : Countable (outerZeros a) :=
      (countable_zeros.mono fun ρ hρ => mem_riemannZetaZeros.2 hρ.1).to_subtype
    have key := eq_zero_of_hasSum_exp (l := fun ρ : outerZeros a => (ρ : ℂ) - 1 / 2)
      (c := fun ρ => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) (B := 1 / 2)
      (fun x y e => Subtype.ext (sub_left_injective e))
      (fun ρ => by
        have := ρ.2.2.2.1
        norm_num
        linarith)
      (fun z => by
        obtain ⟨r, hr, hiso⟩ := exists_isolating_radius (z + 1 / 2)
        refine ⟨r, hr, fun ρ hne => ?_⟩
        have := hiso ρ ρ.2.1 fun e => hne (by rw [e]; ring)
        rwa [show z - ((ρ : ℂ) - 1 / 2) = z + 1 / 2 - ρ by ring])
      (fun x hx => by
        have := h (φ.translate x hx)
        simp_rw [TestFunction.hat_translate] at this
        convert this using 2
        ring) ⟨ρ₀, hρ₀⟩
    rcases mul_eq_zero.1 key with h0 | h0
    · exact (zeroMult_pos hρ₀.1).ne' (by exact_mod_cast h0)
    · exact hφ h0
  · intro h φ
    have : IsEmpty (outerZeros a) := ⟨fun ρ => h ⟨ρ, ρ.2⟩⟩
    exact hasSum_empty

/-- A zero of `ζ` with nonpositive real part is a negative even integer. -/
lemma eq_trivial_of_re_nonpos {s : ℂ} (h : riemannZeta s = 0) (hs : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hw : 1 ≤ (1 - s).re := by simp; linarith
  have hw1 : 1 - s ≠ 1 := by
    intro e
    have : s = 0 := by linear_combination -e
    rw [this, riemannZeta_zero] at h
    norm_num at h
  have hn : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n e
    rw [e] at hw
    simp at hw
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have fe := riemannZeta_one_sub hn hw1
  rw [sub_sub_cancel, h] at fe
  have hG : Gamma (1 - s) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hz : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw
  have hp : (2 * Real.pi : ℂ) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    have : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    tauto
  have hcos : cos (Real.pi * (1 - s) / 2) = 0 := by
    by_contra hc
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hp) hG) hc) hz) fe.symm
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hk' : s = -2 * k := by
    have : (Real.pi : ℂ) * (s + 2 * k) = 0 := by linear_combination -2 * hk
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hpi
    · linear_combination h
  have hk0 : 0 < k := by
    have h1 : s.re = -2 * (k : ℝ) := by rw [hk']; simp
    have h2 : k ≠ 0 := by
      rintro rfl
      simp at hk'
      simp [hk'] at hw1
    have h3 : (0 : ℝ) ≤ k := by linarith
    have : (0 : ℤ) ≤ k := by exact_mod_cast h3
    omega
  refine ⟨(k - 1).toNat, ?_⟩
  have : (((k - 1).toNat : ℤ) : ℂ) = (k - 1 : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at this
  rw [this, hk']
  push_cast
  ring

/-- **Theorem B.** The outer zero sums vanish for all `a > 0` iff the Riemann hypothesis holds. -/
theorem forall_zeroSumVanishes_iff_riemannHypothesis :
    (∀ a > 0, ZeroSumVanishes a) ↔ RiemannHypothesis := by
  constructor
  · intro h s hs htriv _
    by_contra hne
    have hpos : 0 < |s.re - 1 / 2| := abs_pos.2 (sub_ne_zero.2 hne)
    refine (zeroSumVanishes_iff _).1 (h _ hpos) ⟨s, hs, ?_, ?_, le_rfl⟩
    · by_contra hre
      exact htriv (eq_trivial_of_re_nonpos hs (not_lt.1 hre))
    · by_contra hre
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hre) hs
  · intro h a ha
    rw [zeroSumVanishes_iff]
    rintro ⟨ρ, h0, hre0, hre1, hab⟩
    have : ρ.re = 1 / 2 := by
      refine h ρ h0 ?_ ?_
      · rintro ⟨n, rfl⟩
        simp at hre0
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      · rintro rfl
        simp at hre1
    rw [this] at hab
    simp at hab
    linarith

/-! ### Assembly -/

/-- If a functional `G` equals both the full zero sum and the sum over zeros at distance less than
`a` from the critical line, then the outer zero sum vanishes. -/
theorem zeroSumVanishes_of_full_of_inner (a : ℝ) (G : TestFunction → ℂ)
    (hfull : ∀ φ : TestFunction,
      HasSum (fun ρ : stripZeros => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) (G φ))
    (hinner : ∀ φ : TestFunction,
      HasSum (fun ρ : innerZeros a => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) (G φ)) :
    ZeroSumVanishes a := by
  intro φ
  let f : ℂ → ℂ := fun ρ => (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2)
  have h1 : HasSum (stripZeros.indicator f) (G φ) := hasSum_subtype_iff_indicator.1 (hfull φ)
  have h2 : HasSum ((innerZeros a).indicator f) (G φ) := hasSum_subtype_iff_indicator.1 (hinner φ)
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine (hasSum_subtype_iff_indicator (f := f) (s := outerZeros a)).2 ?_
  refine h3.congr_fun fun ρ => ?_
  by_cases hS : ρ ∈ stripZeros
  · by_cases hI : |ρ.re - 1 / 2| < a
    · have hi : ρ ∈ innerZeros a := ⟨hS.1, hS.2.1, hS.2.2, hI⟩
      have ho : ρ ∉ outerZeros a := fun h => absurd hI (not_lt.2 h.2.2.2)
      simp [hS, hi, ho]
    · have hi : ρ ∉ innerZeros a := fun h => hI h.2.2.2
      have ho : ρ ∈ outerZeros a := ⟨hS.1, hS.2.1, hS.2.2, not_lt.1 hI⟩
      simp [hS, hi, ho]
  · have hi : ρ ∉ innerZeros a := fun h => hS ⟨h.1, h.2.1, h.2.2.1⟩
    have ho : ρ ∉ outerZeros a := fun h => hS ⟨h.1, h.2.1, h.2.2.1⟩
    simp [hS, hi, ho]

end Masullo
