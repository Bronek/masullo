import Mathlib
import WeilExplicit.Zeros

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

/-- The Laplace transform of an absolutely convergent exponential sum, term by term. -/
lemma hasSum_cauchySum [Countable ι] {B : ℝ} (hB : ∀ i, (l i).re ≤ B)
    (hc : Summable fun i => ‖c i‖) {F : ℝ → ℂ}
    (h : ∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * l i)) (F x)) {s : ℂ} (hs : B < s.re) :
    HasSum (fun i => c i / (s - l i)) (∫ x in Ioi (0 : ℝ), F x * exp (-(s * x))) := by
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
  simp_rw [hval] at hsum
  rwa [setIntegral_congr_fun (g := fun x : ℝ => ∑' i, c i * exp ((l i - s) * x))
    measurableSet_Ioi fun x hx => ?_]
  refine (((h x (le_of_lt hx)).mul_right (exp (-(s * x)))).congr_fun fun i => ?_).tsum_eq.symm
  rw [mul_assoc, ← Complex.exp_add]
  ring_nf

/-- The Laplace transform of a vanishing exponential sum vanishes. -/
lemma cauchySum_eq_zero [Countable ι] {B : ℝ} (hB : ∀ i, (l i).re ≤ B)
    (hc : Summable fun i => ‖c i‖)
    (h : ∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * l i)) 0) {s : ℂ} (hs : B < s.re) :
    ∑' i, c i / (s - l i) = 0 := by
  simpa using (hasSum_cauchySum (F := 0) hB hc h hs).tsum_eq

/-- An absolutely convergent exponential sum that vanishes on `[0, ∞)`, and whose exponents have
no finite accumulation point and bounded real parts, has only zero coefficients. -/
theorem eq_zero_of_hasSum_exp [Countable ι] (hl : Function.Injective l) {B : ℝ}
    (hB : ∀ i, (l i).re ≤ B) (hd : ∀ z, ∃ r > 0, ∀ i, l i ≠ z → r ≤ ‖z - l i‖)
    (h : ∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * l i)) 0) (j : ι) : c j = 0 := by
  classical
  have hc : Summable fun i => ‖c i‖ := by simpa using (h 0 le_rfl).summable.norm
  -- continue `c j + (s - l j) ∑_{i ≠ j} c i / (s - l i)` across the other exponents
  let J := {i // i ∉ ({j} : Finset ι)}
  let l' (i : J) := l i
  have hd' : ∀ z, ∃ r > 0, ∀ i, l' i ≠ z → r ≤ ‖z - l' i‖ := fun z =>
    let ⟨r, hr, h⟩ := hd z; ⟨r, hr, fun i => h i⟩
  let G (s : ℂ) := c j + (s - l j) * ∑' i : J, c i / (s - l' i)
  have hA : AnalyticOnNhd ℂ G (range l')ᶜ := analyticOnNhd_const.add
    ((analyticOnNhd_id.sub analyticOnNhd_const).mul ((differentiableOn_cauchySum
      (c := fun i : J => c i) hd' (hc.subtype _)).analyticOnNhd (isOpen_compl_range hd')))
  have hconn : IsPreconnected (range l')ᶜ :=
    ((countable_range l').isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hp : (((B + 1 : ℝ) : ℂ)) ∈ (range l')ᶜ := by
    rintro ⟨i, hi⟩
    have := hB i
    rw [show l i = _ from hi, ofReal_re] at this
    linarith
  have hG : EqOn G 0 (range l')ᶜ := by
    refine hA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hp ?_
    have : {s : ℂ | B < s.re} ∈ 𝓝 ((B + 1 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [this] with s hs
    have hne : s - l j ≠ 0 := fun e => by
      have := hB j
      rw [← sub_eq_zero.1 e] at this
      linarith
    have h0 := hasSum_cauchySum (F := 0) hB hc h hs
    simp only [Pi.zero_apply, zero_mul, integral_zero] at h0
    have e := h0.summable.sum_add_tsum_subtype_compl {j}
    rw [Finset.sum_singleton, h0.tsum_eq] at e
    have e' : c j = (s - l j) * (c j / (s - l j)) := (mul_div_cancel₀ _ hne).symm
    simp only [G, Pi.zero_apply]
    linear_combination e' + (s - l j) * e
  have hj : l j ∈ (range l')ᶜ := fun ⟨i, hi⟩ => i.2 (Finset.mem_singleton.2 (hl hi))
  simpa [G] using hG hj

end ExpSum

/-- The Mellin transform in the logarithmic variable. -/
lemma Spectrum.mellin_eq_integral (h : ℝ → ℂ) (s : ℂ) :
    mellin h s = ∫ x : ℝ, h (Real.exp x) * exp (s * x) := by
  rw [mellin_eq_fourier, Real.fourier_eq', ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hin : inner ℝ (-u) (s.im / (2 * Real.pi)) = s.im / (2 * Real.pi) * -u := rfl
  simp only [neg_neg, smul_eq_mul, real_smul, hin]
  rw [ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  have h2 : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  conv_rhs => rw [← re_add_im s]
  push_cast
  field_simp
  ring

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

/-- The values are nonnegative real numbers. -/
def Nonneg (φ : TestFunction) : Prop := ∀ x, 0 ≤ (φ.toFun x).re ∧ (φ.toFun x).im = 0

/-- The tilt `x ↦ x ^ w φ(x)`. -/
noncomputable def tilt (φ : TestFunction) (w : ℂ) : TestFunction where
  toFun t := φ.toFun t * exp (w * (Real.log t : ℂ))
  contDiff := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t ∈ tsupport φ.toFun
    · have ht0 : t ≠ 0 := by
        have : (1 : ℝ) < t := φ.tsupport_subset ht
        linarith
      have h2 : ContDiffAt ℝ ∞ (fun t => ((Real.log t : ℝ) : ℂ)) t :=
        ofRealCLM.contDiff.contDiffAt.comp t (Real.contDiffAt_log.2 ht0)
      exact φ.contDiff.contDiffAt.mul (contDiffAt_const.mul h2).cexp
    · have : φ.toFun =ᶠ[𝓝 t] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 ht
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [this] with x hx
      simp [hx]
  hasCompactSupport := φ.hasCompactSupport.mul_right
  tsupport_subset := (tsupport_mul_subset_left).trans φ.tsupport_subset

/-- Tilting by `w` shifts the transform by `w`. -/
lemma hat_tilt (φ : TestFunction) (w z : ℂ) : (φ.tilt w).hat z = φ.hat (z + w) := by
  unfold hat mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt ht)
  simp only [tilt, smul_eq_mul]
  rw [show z + w - 1 = z - 1 + w by ring, cpow_add _ _ ht', cpow_def_of_ne_zero ht' w,
    ← ofReal_log (le_of_lt ht)]
  ring_nf

lemma Nonneg.tilt {φ : TestFunction} (h : φ.Nonneg) (r : ℝ) : (φ.tilt r).Nonneg := fun x => by
  have e : φ.toFun x = ((φ.toFun x).re : ℂ) := Complex.ext rfl (by simp [(h x).2])
  have e2 : (φ.tilt r).toFun x = (((φ.toFun x).re * Real.exp (r * Real.log x) : ℝ) : ℂ) := by
    simp only [TestFunction.tilt]
    conv_lhs => rw [e]
    push_cast
    rfl
  rw [e2, ofReal_re, ofReal_im]
  exact ⟨mul_nonneg (h x).1 (Real.exp_pos _).le, rfl⟩

/-- Some nonnegative test function has transform nonzero at `1`. -/
lemma exists_nonneg_hat_one : ∃ φ : TestFunction, φ.Nonneg ∧ φ.hat 1 ≠ 0 := by
  let b : ContDiffBump (2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hbs : tsupport (b : ℝ → ℝ) ⊆ Ioi 1 := by
    rw [b.tsupport_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq] at ht
    have := (abs_le.1 ht).1
    change -(1 / 2 : ℝ) ≤ _ at this
    rw [mem_Ioi]; linarith
  refine ⟨⟨fun t => (b t : ℂ), ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left (g := ofReal) rfl,
    (closure_mono fun t ht => by simpa using ht).trans hbs⟩,
    fun x => ⟨by simpa using b.nonneg, by simp⟩, ?_⟩
  have e : mellin (fun t => (b t : ℂ)) 1 = ∫ t in Ioi (0 : ℝ), ((b t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp
  change mellin _ 1 ≠ 0
  rw [e, integral_complex_ofReal, ofReal_ne_zero]
  refine ne_of_gt ((setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => b.nonneg)
    (b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport).integrableOn).2 ?_)
  rw [b.support_eq]
  refine (Metric.measure_ball_pos _ _ b.rOut_pos).trans_le (measure_mono fun t ht => ⟨ht, ?_⟩)
  exact zero_lt_one.trans (mem_Ioi.1 (hbs (subset_tsupport _ (b.support_eq.symm ▸ ht))))

/-- The Mellin transform does not vanish identically on test functions at any point. -/
lemma exists_hat_ne_zero (z : ℂ) : ∃ φ : TestFunction, φ.hat z ≠ 0 := by
  obtain ⟨b, -, hb⟩ := exists_nonneg_hat_one
  exact ⟨b.tilt (1 - z), by rwa [hat_tilt, add_sub_cancel]⟩

end TestFunction

/-! ### Zeros of zeta

`stripZeros` (the zeros in the open critical strip) and `zeroMult` (the analytic multiplicity of a
zero) are defined in `WeilExplicit.Zeros` and exported here. -/

export WeilExplicit (stripZeros zeroMult)

/-- Zeros in the critical strip at distance at least `a` from the critical line. -/
def outerZeros (a : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2|}

/-- Zeros in the critical strip at distance less than `a` from the critical line. -/
def innerZeros (a : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.re - 1 / 2| < a}

lemma innerZeros_subset (a : ℝ) : innerZeros a ⊆ stripZeros := fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

lemma abs_sub_half_lt_half {ρ : ℂ} (hρ : ρ ∈ stripZeros) : |ρ.re - 1 / 2| < 1 / 2 :=
  abs_lt.2 ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩

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
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, (analyticOn_riemannZeta ρ h1).analyticOrderAt_eq_zero, not_not]; exact h
  rw [← Nat.cast_analyticOrderNatAt (WeilExplicit.zeta_order_ne_top h1)] at hne0
  exact Nat.pos_of_ne_zero (by exact_mod_cast hne0)

/-! ### The equivalences -/

/-- A weight on zeros in the critical strip vanishes on `S` if its sums over `S` against all test
functions vanish. -/
lemma weight_eq_zero_of_hasSum {S : Set ℂ} (hS : S ⊆ stripZeros) {w : ℂ → ℂ}
    (h : ∀ φ : TestFunction, HasSum (fun ρ : S => w ρ * φ.hat ((ρ : ℂ) - 1 / 2)) 0)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ S) : w ρ₀ = 0 := by
  obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero (ρ₀ - 1 / 2)
  have : Countable S :=
    (countable_zeros.mono fun ρ hρ => mem_riemannZetaZeros.2 (hS hρ).1).to_subtype
  have key := eq_zero_of_hasSum_exp (l := fun ρ : S => (ρ : ℂ) - 1 / 2)
    (c := fun ρ => w ρ * φ.hat ((ρ : ℂ) - 1 / 2)) (B := 1 / 2)
    (fun x y e => Subtype.ext (sub_left_injective e))
    (fun ρ => by
      have := (hS ρ.2).2.2
      norm_num
      linarith)
    (fun z => by
      obtain ⟨r, hr, hiso⟩ := exists_isolating_radius (z + 1 / 2)
      refine ⟨r, hr, fun ρ hne => ?_⟩
      have := hiso ρ (hS ρ.2).1 fun e => hne (by rw [e]; ring)
      rwa [show z - ((ρ : ℂ) - 1 / 2) = z + 1 / 2 - ρ by ring])
    (fun x hx => by
      have := h (φ.translate x hx)
      simp_rw [TestFunction.hat_translate] at this
      convert this using 2
      ring) ⟨ρ₀, hρ₀⟩
  exact (mul_eq_zero.1 key).resolve_right hφ

/-- **Theorem A.** The outer zero sum vanishes iff there are no outer zeros. -/
theorem zeroSumVanishes_iff (a : ℝ) :
    ZeroSumVanishes a ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2| := by
  refine ⟨fun h ⟨ρ, hρ⟩ => (zeroMult_pos hρ.1).ne' ?_, fun h φ => ?_⟩
  · exact_mod_cast weight_eq_zero_of_hasSum (S := outerZeros a) (w := fun ρ => (zeroMult ρ : ℂ))
      (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩) h hρ
  · have : IsEmpty (outerZeros a) := ⟨fun ρ => h ⟨ρ, ρ.2⟩⟩
    exact hasSum_empty

/-- A zero of `ζ` with nonpositive real part is a negative even integer. -/
lemma eq_trivial_of_re_nonpos {s : ℂ} (h : riemannZeta s = 0) (hs : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at h
  have hw : 1 ≤ (1 - s).re := by simp; linarith
  have hw0 : 1 - s ≠ 0 := ne_zero_of_re_pos (lt_of_lt_of_le zero_lt_one hw)
  have hz := riemannZeta_ne_zero_of_one_le_re hw
  rw [riemannZeta_def_of_ne_zero hw0, completedRiemannZeta_one_sub] at hz
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp (h.resolve_left (fun e => hz (by simp [e])))
  cases n with
  | zero => simp_all
  | succ k => exact ⟨k, by simpa [Nat.cast_add, neg_mul] using hn⟩

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

/-- A sum over the zeros in the strip minus the sum over those at distance less than `a` from the
critical line is the sum over the others. -/
lemma hasSum_outer_of_full_inner {a : ℝ} {f : ℂ → ℂ} {u v : ℂ}
    (hf : HasSum (fun z : stripZeros => f z) u) (hi : HasSum (fun z : innerZeros a => f z) v) :
    HasSum (fun z : outerZeros a => f z) (u - v) := by
  refine (hasSum_subtype_iff_indicator (f := f)).2 (((hasSum_subtype_iff_indicator (f := f)).1
    hf).sub ((hasSum_subtype_iff_indicator (f := f)).1 hi) |>.congr_fun fun ρ => ?_)
  simp only [indicator_apply, innerZeros, outerZeros, stripZeros, mem_ofPred_eq]
  split_ifs <;> grind

/-- If a functional `G` equals both the full zero sum and the sum over zeros at distance less than
`a` from the critical line, then the outer zero sum vanishes. -/
theorem zeroSumVanishes_of_full_of_inner (a : ℝ) (G : TestFunction → ℂ)
    (hfull : ∀ φ : TestFunction,
      HasSum (fun ρ : stripZeros => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) (G φ))
    (hinner : ∀ φ : TestFunction,
      HasSum (fun ρ : innerZeros a => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) (G φ)) :
    ZeroSumVanishes a := fun φ => by
  simpa only [sub_self] using hasSum_outer_of_full_inner
    (f := fun ρ => (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2)) (hfull φ) (hinner φ)

end Masullo
