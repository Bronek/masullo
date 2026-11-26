import Masullo.Modulation
import Masullo.Window

/-!
# Nonnegative probes on windows

`L(t)` is the functional of Weil's explicit formula at the translate by `t ≥ 0` of a nonnegative
test function. For every `a ≥ 0` and `δ > 0`, bounds `L(t) ≤ C e ^ (a t)`, with `C` depending on the
test function, on windows `[U, (1 + δ) U]` with `U` arbitrarily large, are together equivalent to
the trace identities of `Trace.trace_eq_efFunctional_iff` at all widths `a' > a`, and to there
being no zeros in the critical strip at distance more than `a` from the critical line. Neither side
is asserted.

The bound follows from the trace identity at `a'` for the translates, with a constant that does not
depend on `a'`. The converse applies Landau's theorem on windows to `-L(t) ≥ -C e ^ (a t)`: the
Mellin transform of a nonnegative function is nonnegative at real points.

One test function suffices. Landau's theorem sees each zero at which the transform of the test
function does not vanish (`re_sub_half_le_of_windowBound`), and some nonnegative test function has
transform nonvanishing at every zero in the strip (`TestFunction.exists_nonneg_forall_hat_ne_zero`).
Its window bounds alone are equivalent to the absence of zeros at distance more than `a`
(`windowBound_iff`).
-/

open MeasureTheory Complex Set Filter Topology Metric
open scoped ContDiff ComplexConjugate

namespace Masullo

/-! ### Exponential sums bounded on windows -/

section ExpSum

variable {ι : Type*} {l c : ι → ℂ} {a B C δ : ℝ} {F : ℝ → ℝ}

lemma finite_range_inter (hd : ∀ z, ∃ r > 0, ∀ i, l i ≠ z → r ≤ ‖z - l i‖) (s : ℂ) (r : ℝ) :
    (range l ∩ closedBall s r).Finite := by
  by_contra h
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact h (isCompact_closedBall s r)
    inter_subset_right
  obtain ⟨r, hr, hi⟩ := hd x
  obtain ⟨_, ⟨hne, ⟨i, rfl⟩, -⟩, hb⟩ :=
    ((accPt_iff_frequently.1 hx).and_eventually (ball_mem_nhds x hr)).exists
  exact (hi i hne).not_gt (by rwa [← dist_eq_norm, dist_comm])

/-- **Landau's theorem for exponential sums.** If a real, absolutely convergent sum of exponentials
with nonzero coefficients, and with distinct exponents that have real parts bounded above and no
finite accumulation point, is at most `C e ^ (a t)` on arbitrarily late windows `[U, (1 + δ) U]`,
for one `δ > 0`, and the coefficients at real exponents above `a` have positive real part, then no
exponent has real part above `a`. -/
theorem re_le_of_window (hl : Function.Injective l) (hB : ∀ i, (l i).re ≤ B)
    (hd : ∀ z, ∃ r > 0, ∀ i, l i ≠ z → r ≤ ‖z - l i‖) (hc : ∀ i, c i ≠ 0)
    (hF : ∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * l i)) (F x)) (ha : 0 ≤ a)
    (hpos : ∀ i, (l i).im = 0 → a < (l i).re → 0 < (c i).re) (hδ : 0 < δ)
    (hw : ∀ X, ∃ U ≥ X, ∀ t ∈ Icc U ((1 + δ) * U), 0 ≤ t → F t ≤ C * Real.exp (a * t)) (i : ι) :
    (l i).re ≤ a := by
  have hs : Summable fun i => ‖c i‖ := by simpa using (hF 0 le_rfl).summable.norm
  have : Countable ι := countable_univ_iff.1 (hs.of_norm.countable_support.mono fun i _ => hc i)
  set f : ℝ → ℝ := fun u => -(∑' i, c i * exp (u * l i)).re
  have hf {u : ℝ} (hu : 0 ≤ u) : f u = -F u := by
    simp only [f, (hF u hu).tsum_eq, ofReal_re]
  have hm : Measurable f := by unfold f; fun_prop
  have hg (u : ℝ) (hu : 0 ≤ u) : |f u| ≤ (∑' i, ‖c i‖) * Real.exp (B * u) := by
    rw [hf hu, abs_neg, ← Real.norm_eq_abs, ← norm_real, ← (hF u hu).tsum_eq, ← tsum_mul_right]
    refine tsum_of_norm_bounded (hs.mul_right _).hasSum fun i => ?_
    rw [norm_mul, norm_exp, re_ofReal_mul, mul_comm u]
    gcongr
    exact hB i
  have hsum (s : ℂ) : Summable fun i => c i / (s - l i) := by
    obtain ⟨r, hr, hi⟩ := hd s
    refine .of_norm_bounded (hs.div_const r) fun i => ?_
    rcases eq_or_ne (l i) s with e | e
    · simp only [e, sub_self, div_zero, norm_zero]
      positivity
    · rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr (hi i e)
  have key : Landau.Continues f (fun s => -∑' i, c i / (s - l i))
      {z | z ∈ range l ∧ a < z.re} (fun z => -Function.extend l c 0 z) (∑' i, ‖c i‖) B a :=
    { measurable := hm
      growth := hg
      laplace s h := by
        rw [(hasSum_cauchySum hB hs hF h).tsum_eq, ← integral_neg]
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        simp only [hf (le_of_lt hu)]
        push_cast
        ring
      analytic s h hZ := (((differentiableOn_cauchySum hd hs).analyticOnNhd
        (isOpen_compl_range hd)) s fun hr => hZ ⟨hr, h⟩).fun_neg
      finite s r := (finite_range_inter hd s r).subset (inter_subset_inter_left _ fun _ h => h.1)
      re_mem := by
        rintro _ ⟨⟨i, rfl⟩, h⟩
        exact ⟨h, hB i⟩
      residue_ne_zero := by
        rintro _ ⟨⟨i, rfl⟩, -⟩
        rw [hl.extend_apply]
        exact neg_ne_zero.2 (hc i)
      pole := by
        rintro _ ⟨⟨i, rfl⟩, h⟩
        have hd' : ∀ z, ∃ r > 0, ∀ j : ({i}ᶜ : Set ι), l j ≠ z → r ≤ ‖z - l j‖ := fun z =>
          (hd z).imp fun r hr => ⟨hr.1, fun j => hr.2 j⟩
        have hA := (differentiableOn_cauchySum (c := fun j : ({i}ᶜ : Set ι) => c j) hd'
          (hs.subtype _)).analyticOnNhd (isOpen_compl_range hd') (l i) (by
            rintro ⟨j, hj⟩
            exact j.2 (hl hj))
        refine ⟨_, hA.fun_neg, .of_forall fun s => ?_⟩
        have e := (hsum s).tsum_subtype_add_tsum_subtype_compl {i}
        rw [tsum_singleton i fun i => c i / (s - l i)] at e
        simp only [← e, hl.extend_apply]
        ring }
  by_contra h
  refine (key.eq_empty_of_window (C := C) ha ?_ hδ fun X => ?_).subset
    (⟨⟨i, rfl⟩, not_le.1 h⟩ : l i ∈ {z | z ∈ range l ∧ a < z.re})
  · rintro _ ⟨⟨i, rfl⟩, h⟩ him
    rw [hl.extend_apply, neg_re, neg_lt_zero]
    exact hpos i him h
  · obtain ⟨U, hU, h⟩ := hw (max X 0)
    obtain ⟨h1, h2⟩ := max_le_iff.1 hU
    refine ⟨U, h1, fun u hu => ?_⟩
    rw [hf (h2.trans hu.1), neg_le_neg_iff]
    exact h u hu (h2.trans hu.1)

end ExpSum

/-! ### Nonnegative probes -/

namespace TestFunction

/-- The values are nonnegative real numbers. -/
def Nonneg (φ : TestFunction) : Prop := ∀ x, 0 ≤ (φ.toFun x).re ∧ (φ.toFun x).im = 0

variable {φ : TestFunction}

lemma Nonneg.translate (h : φ.Nonneg) {t : ℝ} (ht : 0 ≤ t) : (φ.translate t ht).Nonneg :=
  fun _ => h _

lemma hat_eq_integral (φ : TestFunction) (z : ℂ) :
    φ.hat z = ∫ u : ℝ, φ.pull u * exp (z * u) := by
  rw [← Trace.jet_pull, Synthesis.jet_zero]

lemma Nonneg.conj_toFun (h : φ.Nonneg) (x : ℝ) : conj (φ.toFun x) = φ.toFun x :=
  conj_eq_iff_im.2 (h x).2

lemma Nonneg.conj_hat (h : φ.Nonneg) (z : ℂ) : conj (φ.hat z) = φ.hat (conj z) := by
  simp only [hat_eq_integral, ← integral_conj, map_mul, pull, h.conj_toFun, ← exp_conj, conj_ofReal]

lemma Nonneg.hat_ofReal_re (h : φ.Nonneg) (x : ℝ) : 0 ≤ (φ.hat x).re := by
  have e : φ.hat x = ∫ u : ℝ, (((φ.pull u).re * Real.exp (x * u) : ℝ) : ℂ) := by
    rw [hat_eq_integral]
    congr 1 with u
    rw [pull, ← conj_eq_iff_re.1 (h.conj_toFun (Real.exp u))]
    simp
  rw [e, integral_complex_ofReal, ofReal_re]
  exact integral_nonneg fun u => mul_nonneg (h _).1 (Real.exp_pos _).le

lemma digamma_conj (z : ℂ) : digamma (conj z) = conj (digamma z) := by
  have e : conj ∘ Gamma ∘ conj = Gamma := funext fun z => by simp [Gamma_conj]
  have h := congrFun (deriv_conj_conj (f := Gamma)) (conj z)
  rw [e] at h
  simp [digamma, logDeriv_apply, h, Gamma_conj]

lemma Nonneg.efFunctional_im (h : φ.Nonneg) : φ.efFunctional.im = 0 := by
  rw [← conj_eq_iff_im]
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  have h4 : conj (4 : ℂ) = 4 := map_ofNat _ 4
  have e1 : conj (-1 / 2 : ℂ) = -1 / 2 := by simp [h2]
  have e2 : conj (1 / 2 : ℂ) = 1 / 2 := by simp [h2]
  have e3 : conj (1 / (2 * Real.pi) : ℂ) = 1 / (2 * Real.pi) := by simp [h2]
  simp only [efFunctional, map_add, map_sub, map_mul, conj_tsum, h.conj_hat, e1, e2, e3,
    conj_ofReal, h.conj_toFun, ← integral_conj]
  congr 2
  rw [← integral_neg_eq_self]
  congr 1 with r
  have e4 : (1 / 4 + I * ((-r : ℝ) : ℂ) / 2 : ℂ) = conj (1 / 4 + I * r / 2) := by
    simp [h2, h4]
  rw [e4, digamma_conj, conj_re]
  simp

/-- The Mellin transform does not vanish identically on nonnegative test functions at any point. -/
lemma exists_nonneg_hat_ne_zero (z : ℂ) : ∃ φ : TestFunction, φ.Nonneg ∧ φ.hat z ≠ 0 := by
  let g : ℝ → ℝ := fun t => (exp (z * (Real.log t - Real.log 2 : ℝ))).re
  have hg : ContinuousAt g 2 := by
    have := Real.continuousAt_log (x := 2) (by norm_num)
    fun_prop
  obtain ⟨ε, hε, hgε⟩ := Metric.eventually_nhds_iff_ball.1
    (hg.eventually (lt_mem_nhds (a := 0) (by simp [g])))
  let b : ContDiffBump (2 : ℝ) := ⟨min ε (1 / 2) / 2, min ε (1 / 2), by positivity,
    half_lt_self (by positivity)⟩
  let φ : TestFunction := ⟨fun t => (b t : ℂ), ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left (g := ofReal) rfl, by
      refine (closure_mono fun t ht => ?_ : _ ⊆ tsupport (b : ℝ → ℝ)).trans ?_
      · simpa using ht
      · intro t ht
        have h1 := (abs_le.1 (mem_closedBall.1 (b.tsupport_eq.subset ht))).1
        have : b.rOut ≤ 1 / 2 := min_le_right _ _
        rw [mem_Ioi]
        linarith⟩
  refine ⟨φ, fun x => ⟨by simpa [φ] using b.nonneg, by simp [φ]⟩, fun h0 => ?_⟩
  have hc : Continuous fun u : ℝ => φ.pull u * exp (z * (u - Real.log 2 : ℝ)) :=
    φ.pull_contDiff.continuous.mul (by fun_prop)
  have hi := hc.integrable_of_hasCompactSupport (μ := volume) φ.pull_hasCompactSupport.mul_right
  have hre (u : ℝ) : (φ.pull u * exp (z * (u - Real.log 2 : ℝ))).re =
      b (Real.exp u) * g (Real.exp u) := by
    simp only [φ, pull, g, re_ofReal_mul, Real.log_exp]
  have hp : 0 < ∫ u : ℝ, (φ.pull u * exp (z * (u - Real.log 2 : ℝ))).re := by
    refine (continuous_re.comp hc).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := Real.log 2) (φ.pull_hasCompactSupport.mul_right.comp_left (g := re) rfl)
      (fun u => ?_) ?_
    · simp only [hre, Pi.zero_apply]
      by_cases hu : Real.exp u ∈ ball (2 : ℝ) b.rOut
      · exact mul_nonneg b.nonneg (hgε _ (ball_subset_ball (min_le_left _ _) hu)).le
      · rw [b.zero_of_le_dist (not_lt.1 hu), zero_mul]
    · have : b 2 = 1 := b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)
      exact (hre _).trans_ne (by simp [Real.exp_log, this, g])
  have e : ∫ u : ℝ, φ.pull u * exp (z * (u - Real.log 2 : ℝ)) =
      φ.hat z * exp (-(z * Real.log 2)) := by
    rw [hat_eq_integral, ← integral_mul_const]
    congr 1 with u
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  have h1 := reCLM.integral_comp_comm hi
  simp only [reCLM_apply, e, h0, zero_mul, zero_re] at h1
  exact hp.ne' h1

lemma Nonneg.tilt (h : φ.Nonneg) (r : ℝ) : (φ.tilt r).Nonneg := fun x => by
  have e : φ.toFun x = ((φ.toFun x).re : ℂ) := Complex.ext rfl (by simp [(h x).2])
  have e2 : (φ.tilt r).toFun x = (((φ.toFun x).re * Real.exp (r * Real.log x) : ℝ) : ℂ) := by
    simp only [TestFunction.tilt]
    conv_lhs => rw [e]
    push_cast
    rfl
  rw [e2, ofReal_re, ofReal_im]
  exact ⟨mul_nonneg (h x).1 (Real.exp_pos _).le, rfl⟩

/-- A transform that does not vanish at one point vanishes at countably many points. -/
lemma countable_hat_eq_zero {z₀ : ℂ} (h : φ.hat z₀ ≠ 0) : {z | φ.hat z = 0}.Countable := by
  rcases (φ.differentiable_hat.differentiableOn.analyticOnNhd isOpen_univ)
    |>.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h0 | h0
  · exact absurd (h0 (mem_univ z₀)) h
  · have := (isDiscrete_of_codiscreteWithin (s := {z | φ.hat z = 0}) h0).to_subtype
    simpa using (TopologicalSpace.separableSpace_iff_countable.1 inferInstance :
      Countable ({z | φ.hat z = 0} ∩ univ : Set ℂ))

/-- **A universal probe.** Some nonnegative test function has transform nonzero at `ρ - 1/2` for
every zero `ρ` in the critical strip. It is a nonnegative bump tilted by a real power `x ^ r`,
whose transform is that of the bump shifted by `r`; the transform of the bump has countably many
zeros and there are countably many zeros in the strip, so all but countably many `r` qualify. -/
theorem exists_nonneg_forall_hat_ne_zero :
    ∃ φ : TestFunction, φ.Nonneg ∧ ∀ ρ ∈ stripZeros, φ.hat (ρ - 1 / 2) ≠ 0 := by
  obtain ⟨b, hb, hb0⟩ := exists_nonneg_hat_ne_zero 0
  have hB : (⋃ ρ ∈ stripZeros, (fun r : ℝ => ρ - 1 / 2 + r) ⁻¹' {z | b.hat z = 0}).Countable :=
    (countable_zeros.mono fun ρ hρ => mem_riemannZetaZeros.2 hρ.1).biUnion fun ρ _ =>
      (countable_hat_eq_zero hb0).preimage ((add_right_injective _).comp ofReal_injective)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r ∉ ⋃ ρ ∈ stripZeros,
      (fun r : ℝ => ρ - 1 / 2 + r) ⁻¹' {z | b.hat z = 0} := by
    by_contra! h
    exact Cardinal.not_countable_real (hB.mono fun r _ => h r)
  refine ⟨b.tilt r, hb.tilt r, fun ρ hρ h0 => hr (mem_iUnion₂.2 ⟨ρ, hρ, ?_⟩)⟩
  rwa [hat_tilt] at h0

end TestFunction

/-! ### The equivalence -/

open Trace

/-- The translates of `φ` have `L(t) ≤ C e ^ (a t)`, for some `C`, on arbitrarily late windows
`[U, (1 + δ) U]`. -/
def TestFunction.WindowBound (φ : TestFunction) (a δ : ℝ) : Prop :=
  ∃ C, ∀ X, ∃ U ≥ X, ∀ t ∈ Icc U ((1 + δ) * U), ∀ ht : 0 ≤ t,
    (φ.translate t ht).efFunctional.re ≤ C * Real.exp (a * t)

/-- The translates of every nonnegative test function have `L(t) ≤ C e ^ (a t)`, for some `C`, on
arbitrarily late windows `[U, (1 + δ) U]`. -/
def ProbeBound (a δ : ℝ) : Prop := ∀ φ : TestFunction, φ.Nonneg → φ.WindowBound a δ

variable {a δ : ℝ}

/-- The trace identity for one translate bounds its functional, with a constant that depends
neither on the translate nor on the width. -/
lemma norm_efFunctional_le_of_trace (ha : 0 < a) (φ : TestFunction) {t : ℝ} (ht : 0 ≤ t)
    (h : HasTrace (induced ha (φ.translate t ht)) (φ.translate t ht).efFunctional) :
    ‖(φ.translate t ht).efFunctional‖ ≤
      (∑' ρ : stripZeros, ‖(zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)‖) * Real.exp (a * t) := by
  obtain ⟨s, h1, h2⟩ := exists_hasTrace_induced ha (φ.translate t ht)
  rw [h.unique h1, ← h2.tsum_eq, ← tsum_mul_right]
  have hs := φ.hasSum_full.summable.norm.mul_right (Real.exp (a * t))
  have hinj := inclusion_injective (innerZeros_subset a)
  have hle (ρ : innerZeros a) : ‖(zeroMult ρ : ℂ) * (φ.translate t ht).hat ((ρ : ℂ) - 1 / 2)‖ ≤
      ‖(zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)‖ * Real.exp (a * t) := by
    rw [TestFunction.hat_translate, mul_left_comm, norm_mul, norm_exp, re_ofReal_mul, mul_comm,
      mul_comm t]
    gcongr
    exact (abs_lt.1 (Spectrum.abs_re_lt_of_mem ρ.2)).2.le
  exact (tsum_of_norm_bounded (hs.comp_injective hinj).hasSum hle).trans
    (tsum_comp_le_tsum_of_inj hs (fun ρ => by positivity) hinj)

/-- One nonnegative test function with transform nonzero at `ρ₀ - 1/2` and with the window bounds
leaves the zero `ρ₀` at most `a` to the right of the critical line. -/
lemma re_sub_half_le_of_windowBound (ha : 0 ≤ a) (hδ : 0 < δ) {φ : TestFunction}
    (hφ : φ.Nonneg) (h : φ.WindowBound a δ) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ stripZeros)
    (hne : φ.hat (ρ₀ - 1 / 2) ≠ 0) : ρ₀.re - 1 / 2 ≤ a := by
  obtain ⟨C, hC⟩ := h
  let S : Set stripZeros := Function.support fun ρ => φ.hat ((ρ : ℂ) - 1 / 2)
  have key := re_le_of_window (ι := S) (l := fun ρ => (ρ : ℂ) - 1 / 2)
    (c := fun ρ => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) (B := 1 / 2) (a := a) (C := C)
    (F := fun t => (φ.translate |t| (abs_nonneg t)).efFunctional.re)
    (fun x y e => Subtype.ext (Subtype.ext (sub_left_injective e)))
    (fun ρ => by
      have := ρ.1.2.2.2
      norm_num
      linarith)
    (fun z => by
      obtain ⟨r, hr, hiso⟩ := exists_isolating_radius (z + 1 / 2)
      refine ⟨r, hr, fun ρ hne => ?_⟩
      have := hiso ρ ρ.1.2.1 fun e => hne (by rw [e]; ring)
      rwa [show z - ((ρ : ℂ) - 1 / 2) = z + 1 / 2 - ρ by ring])
    (fun ρ => mul_ne_zero (Nat.cast_ne_zero.2 (zeroMult_pos ρ.1.2.1).ne') ρ.2)
    (fun x hx => by
      have h0 := (φ.translate |x| (abs_nonneg x)).hasSum_full
      rw [← conj_eq_iff_re.1 (conj_eq_iff_im.2 (hφ.translate (abs_nonneg x)).efFunctional_im)]
        at h0
      refine ((hasSum_subtype_iff_of_support_subset fun ρ hρ => ?_).2 (h0.congr_fun
        fun ρ : stripZeros => ?_ : HasSum (fun ρ : stripZeros =>
          (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2) * exp (x * ((ρ : ℂ) - 1 / 2))) _))
      · exact right_ne_zero_of_mul (left_ne_zero_of_mul hρ)
      · rw [TestFunction.hat_translate, abs_of_nonneg hx]
        ring)
    ha (fun ρ him _ => ?_) hδ (fun X => ?_) ⟨⟨ρ₀, hρ₀⟩, hne⟩
  · simpa using key
  · have e : (ρ : ℂ) - 1 / 2 = (((ρ : ℂ) - 1 / 2).re : ℝ) := Complex.ext rfl (by simpa using him)
    have h1 := hφ.hat_ofReal_re ((ρ : ℂ) - 1 / 2).re
    have h2 := hφ.conj_hat ((ρ : ℂ) - 1 / 2)
    rw [e, conj_ofReal, ← e, conj_eq_iff_im] at h2
    rw [← e] at h1
    rw [← ofReal_natCast, re_ofReal_mul]
    exact mul_pos (Nat.cast_pos.2 (zeroMult_pos ρ.1.2.1))
      (h1.lt_of_ne fun h3 => ρ.2 (Complex.ext h3.symm h2))
  · obtain ⟨U, hU, hb⟩ := hC X
    refine ⟨U, hU, fun t ht h0 => ?_⟩
    simp only [abs_of_nonneg h0]
    exact hb t ht h0

/-- The trace identities at all widths above `a` give the window bounds of every test function. -/
lemma windowBound_of_trace (ha : 0 ≤ a)
    (h : ∀ (a' : ℝ) (h : a < a') (φ : TestFunction),
      HasTrace (induced (ha.trans_lt h) φ) φ.efFunctional) (φ : TestFunction) :
    φ.WindowBound a δ := by
  refine ⟨∑' ρ : stripZeros, ‖(zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)‖,
    fun X => ⟨X, le_rfl, fun t _ ht => ?_⟩⟩
  refine (re_le_norm _).trans (ge_of_tendsto (x := 𝓝[>] a) ?_
    (eventually_mem_nhdsWithin.mono fun a' ha' =>
      norm_efFunctional_le_of_trace (ha.trans_lt ha') φ ht (h a' ha' _)))
  exact (by fun_prop : Continuous fun x : ℝ => _ * Real.exp (x * t)).continuousWithinAt

/-- **One probe.** For a nonnegative test function whose transform is nonzero at `ρ - 1/2` for
every zero `ρ` in the critical strip, its window bounds hold iff there are no zeros in the critical
strip at distance more than `a` from the critical line. Neither side is asserted. -/
theorem windowBound_iff (ha : 0 ≤ a) (hδ : 0 < δ) {φ : TestFunction} (hφ : φ.Nonneg)
    (hne : ∀ ρ ∈ stripZeros, φ.hat (ρ - 1 / 2) ≠ 0) : φ.WindowBound a δ ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a < |ρ.re - 1 / 2| := by
  refine ⟨fun h => ?_, fun h => windowBound_of_trace ha (fun a' ha' =>
    (trace_eq_efFunctional_iff (ha.trans_lt ha')).2 ?_) φ⟩
  · have right {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ stripZeros) : ρ₀.re - 1 / 2 ≤ a :=
      re_sub_half_le_of_windowBound ha hδ hφ h hρ₀ (hne ρ₀ hρ₀)
    rintro ⟨ρ, h0, h1, h2, h3⟩
    obtain ⟨ρ', h0', h1', h2', h4⟩ := Window.exists_zero_gt_half_add_of_abs h0 h1 h2 h3
    exact h4.not_ge (right ⟨h0', h1', h2'⟩)
  · rintro ⟨ρ, h0, h1, h2, h3⟩
    exact h ⟨ρ, h0, h1, h2, ha'.trans_le h3⟩

/-- Some nonnegative test function has window bounds iff there are no zeros in the critical strip
at distance more than `a` from the critical line. Neither side is asserted. -/
theorem exists_windowBound_iff (ha : 0 ≤ a) (hδ : 0 < δ) : ∃ φ : TestFunction, φ.Nonneg ∧
    (φ.WindowBound a δ ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a < |ρ.re - 1 / 2|) :=
  have ⟨φ, hφ, hne⟩ := TestFunction.exists_nonneg_forall_hat_ne_zero
  ⟨φ, hφ, windowBound_iff ha hδ hφ hne⟩

/-- The window bounds leave no zeros in the critical strip at distance more than `a` from the
critical line. -/
theorem not_exists_zero_of_probeBound (ha : 0 ≤ a) (hδ : 0 < δ) (h : ProbeBound a δ) :
    ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a < |ρ.re - 1 / 2| :=
  have ⟨φ, hφ, hne⟩ := TestFunction.exists_nonneg_forall_hat_ne_zero
  (windowBound_iff ha hδ hφ hne).1 (h φ hφ)

/-- **Theorem P.** The trace identities at all widths above `a` hold iff the functional of the
explicit formula on translates of nonnegative test functions is `O(e ^ (a t))`, from above and on
arbitrarily late windows. Neither side is asserted. -/
theorem trace_eq_efFunctional_iff_probeBound (ha : 0 ≤ a) (hδ : 0 < δ) :
    (∀ (a' : ℝ) (h : a < a') (φ : TestFunction),
      HasTrace (induced (ha.trans_lt h) φ) φ.efFunctional) ↔ ProbeBound a δ := by
  refine ⟨fun h φ _ => windowBound_of_trace ha h φ, fun h a' ha' => ?_⟩
  refine (trace_eq_efFunctional_iff (ha.trans_lt ha')).2 ?_
  rintro ⟨ρ, h0, h1, h2, h3⟩
  exact not_exists_zero_of_probeBound ha hδ h ⟨ρ, h0, h1, h2, ha'.trans_le h3⟩

/-- The window bounds hold iff there are no zeros in the critical strip at distance more than `a`
from the critical line; zeros at distance `a` are allowed. Neither side is asserted. -/
theorem probeBound_iff (ha : 0 ≤ a) (hδ : 0 < δ) : ProbeBound a δ ↔
    ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a < |ρ.re - 1 / 2| := by
  refine ⟨not_exists_zero_of_probeBound ha hδ, fun h =>
    (trace_eq_efFunctional_iff_probeBound ha hδ).1 fun a' ha' => ?_⟩
  refine (trace_eq_efFunctional_iff (ha.trans_lt ha')).2 ?_
  rintro ⟨ρ, h0, h1, h2, h3⟩
  exact h ⟨ρ, h0, h1, h2, ha'.trans_le h3⟩

/-- The trace identity at the one width `a` gives the window bounds with exponent `a`. The converse
is not asserted: the bounds allow zeros at distance `a` from the critical line. -/
theorem probeBound_of_trace (ha : 0 < a)
    (h : ∀ φ : TestFunction, HasTrace (induced ha φ) φ.efFunctional) : ProbeBound a δ :=
  fun φ _ => ⟨_, fun X => ⟨X, le_rfl, fun _ _ ht =>
    (re_le_norm _).trans (norm_efFunctional_le_of_trace ha φ ht (h _))⟩⟩

/-- For any one `δ > 0`, the bounds on windows by constants hold iff the Riemann hypothesis holds.
Neither side is asserted. -/
theorem probeBound_zero_iff_riemannHypothesis (hδ : 0 < δ) :
    ProbeBound 0 δ ↔ RiemannHypothesis := by
  rw [← trace_eq_efFunctional_iff_probeBound le_rfl hδ,
    ← forall_innerExpansion_iff_riemannHypothesis]
  exact forall₂_congr fun a' ha' =>
    (trace_eq_efFunctional_iff ha').trans (innerExpansion_iff a').symm

/-- For any one `δ > 0`, some nonnegative test function has bounds on windows by constants iff the
Riemann hypothesis holds. Neither side is asserted. -/
theorem exists_windowBound_zero_iff_riemannHypothesis (hδ : 0 < δ) :
    ∃ φ : TestFunction, φ.Nonneg ∧ (φ.WindowBound 0 δ ↔ RiemannHypothesis) :=
  have ⟨φ, hφ, h⟩ := exists_windowBound_iff le_rfl hδ
  ⟨φ, hφ, h.trans ((probeBound_iff le_rfl hδ).symm.trans
    (probeBound_zero_iff_riemannHypothesis hδ))⟩

end Masullo
