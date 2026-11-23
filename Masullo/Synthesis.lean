import Masullo.Spectrum
import Zeta23.WeilEF.GoodHeights

/-!
# Spectral synthesis for the theta span

`V a`, the closed span of the theta functions in `W a`, is the closed ideal `J a` cut out by the
zeros of zeta at distance less than `a` from the critical line, with multiplicity. It is also the
closed span of the translates of one theta function. Both hold for every `a > 0`; no position or
simplicity of any zero is assumed or concluded.

The core `integral_eq_zero_of_order_le` is a duality argument for a rapidly decaying `h` with
transform `X`. If `y` annihilates the translates of `h`, then so does the correlation `p` of `y`
with `u`. The Carleman transform of the right half of the convolution of `p` with `h` is an entire
`G`, equal to `X` times one-sided Laplace transforms of `p` outside the strip, and to a multiple of
the transform of `u` plus a multiple of `X` inside. Hence `G / X` is entire. Lower bounds for `X`
along a sequence of heights and the maximum principle make it bounded, so it vanishes, and then
`p 0 = ∫ y u = 0`.

For zeta the seed is `(4π²x⁴ - 6πx²) e^{-πx²}`, whose theta function has transform `ξ(1/2 + z)`. The
heights come from a bound for `ζ'/ζ` and an elementary lower bound for the Gamma function.
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace SchwartzMap FourierTransform ComplexConjugate ENNReal

namespace Masullo.Synthesis

open Spectrum

/-! ### Bilateral Laplace transforms -/

/-- `u` is integrable against `e^{σx + c|x|}` for some `c > 0`. -/
def ConvAt (u : ℝ → ℂ) (σ : ℝ) : Prop :=
  ∃ c > 0, Integrable fun x : ℝ => (Real.exp (σ * x + c * |x|) : ℂ) * u x

variable {u h k w y : ℝ → ℂ} {a σ : ℝ}

lemma ConvAt.aesm (hu : ConvAt u σ) : AEStronglyMeasurable u := by
  obtain ⟨c, -, h⟩ := hu
  have h1 : Continuous fun x : ℝ => (Real.exp (-(σ * x + c * |x|)) : ℂ) := by fun_prop
  refine (h1.aestronglyMeasurable.mul h.aestronglyMeasurable).congr
    (Eventually.of_forall fun x => ?_)
  change (Real.exp (-(σ * x + c * |x|)) : ℂ) * ((Real.exp (σ * x + c * |x|) : ℂ) * u x) = u x
  rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, ofReal_one, one_mul]

lemma ConvAt.eventually {z : ℂ} (hu : ConvAt u z.re) : ∀ᶠ w : ℂ in 𝓝 z, ConvAt u w.re := by
  have hm := hu.aesm
  obtain ⟨c, hc, h⟩ := hu
  filter_upwards [Metric.ball_mem_nhds z (half_pos hc)] with w hw
  refine ⟨c / 2, by positivity, h.mono ?_ (Eventually.of_forall fun x => ?_)⟩
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (Real.exp (w.re * x + c / 2 * |x|) : ℂ)).aestronglyMeasurable.mul hm
  · simp only [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have h1 := (abs_re_le_norm (w - z)).trans (mem_ball_iff_norm.1 hw).le
    have h2 := re_mul_le (z := w - z) h1 x
    rw [sub_re, sub_mul] at h2
    linarith

lemma exists_weight_le (m : ℕ) {c : ℝ} (hc : 0 < c) : ∃ C, ∀ z w : ℂ, |(w - z).re| ≤ c / 2 → ∀ x : ℝ,
    ‖(x : ℂ) ^ m * exp (w * x)‖ ≤ C * Real.exp (z.re * x + c * |x|) := by
  obtain ⟨C, hC⟩ := pow_mul_exp_le m (half_pos hc)
  refine ⟨C, fun z w hw x => ?_⟩
  rw [norm_pow_mul_exp]
  have h2 := re_mul_le (z := w - z) hw x
  rw [sub_re, sub_mul] at h2
  have h3 : Real.exp (w.re * x) ≤ Real.exp (-(c / 2) * |x|) * Real.exp (z.re * x + c * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  calc _ ≤ |x| ^ m * (Real.exp (-(c / 2) * |x|) * Real.exp (z.re * x + c * |x|)) := by gcongr
    _ = (|x| ^ m * Real.exp (-(c / 2) * |x|)) * Real.exp (z.re * x + c * |x|) := by ring
    _ ≤ _ := by gcongr; exact hC x

lemma ConvAt.hasDerivAt {z : ℂ} (hu : ConvAt u z.re) (m : ℕ) :
    Integrable (fun x : ℝ => u x * ((x : ℂ) ^ m * exp (z * x))) ∧
      HasDerivAt (jet u m) (jet u (m + 1) z) z := by
  have hm := hu.aesm
  obtain ⟨c, hc, h⟩ := hu
  have hmeas : ∀ (m : ℕ) (w : ℂ),
      AEStronglyMeasurable fun x : ℝ => u x * ((x : ℂ) ^ m * exp (w * x)) := fun m w =>
    hm.mul (by fun_prop : Continuous fun x : ℝ => (x : ℂ) ^ m * exp (w * x)).aestronglyMeasurable
  have key : ∀ m : ℕ, ∃ C, ∀ w : ℂ, |(w - z).re| ≤ c / 2 → ∀ x : ℝ,
      ‖u x * ((x : ℂ) ^ m * exp (w * x))‖ ≤
        C * ‖(Real.exp (z.re * x + c * |x|) : ℂ) * u x‖ := fun m => by
    obtain ⟨C, hC⟩ := exists_weight_le m hc
    refine ⟨C, fun w hw x => ?_⟩
    rw [norm_mul, norm_mul _ (u x), norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      mul_comm ‖u x‖, ← mul_assoc]
    gcongr
    exact hC z w hw x
  have hi : Integrable (fun x : ℝ => u x * ((x : ℂ) ^ m * exp (z * x))) := by
    obtain ⟨C, hC⟩ := key m
    exact (h.norm.const_mul C).mono' (hmeas m z)
      (Eventually.of_forall (hC z (by simp; positivity)))
  obtain ⟨C, hC⟩ := key (m + 1)
  refine ⟨hi, (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z (half_pos hc)) (Eventually.of_forall (hmeas m)) hi (hmeas (m + 1) z)
    (Eventually.of_forall fun x w hw => hC w ?_ x) (h.norm.const_mul C)
    (Eventually.of_forall fun x w _ => ?_)).2⟩
  · exact (abs_re_le_norm (w - z)).trans (mem_ball_iff_norm.1 hw).le
  · have h := (((hasDerivAt_id w).mul_const (x : ℂ)).cexp.const_mul ((x : ℂ) ^ m)).const_mul (u x)
    refine h.congr_deriv ?_
    simp only [id, pow_succ]
    ring

lemma ConvAt.integrable {z : ℂ} (hu : ConvAt u z.re) :
    Integrable fun x : ℝ => u x * exp (z * x) := by
  simpa using (hu.hasDerivAt 0).1

lemma ConvAt.analyticAt {z : ℂ} (hu : ConvAt u z.re) : AnalyticAt ℂ (jet u 0) z :=
  Complex.analyticAt_iff_eventually_differentiableAt.2
    (hu.eventually.mono fun _ hw => (hw.hasDerivAt 0).2.differentiableAt)

lemma ConvAt.iteratedDeriv {z : ℂ} (hu : ConvAt u z.re) (m : ℕ) :
    _root_.iteratedDeriv m (jet u 0) z = jet u m z := by
  have key : ∀ m : ℕ, _root_.iteratedDeriv m (jet u 0) =ᶠ[𝓝 z] jet u m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iteratedDeriv_succ]
      filter_upwards [ih.deriv, hu.eventually] with w hw hw'
      rw [hw, (hw'.hasDerivAt m).2.deriv]
  exact (key m).eq_of_nhds

lemma jet_zero (u : ℝ → ℂ) (z : ℂ) : jet u 0 z = ∫ x : ℝ, u x * exp (z * x) := by simp [jet]

/-! ### Correlations -/

/-- The correlation `∫ k(x) h(x - t) dx`. -/
noncomputable def cross (k h : ℝ → ℂ) (t : ℝ) : ℂ := ∫ x, k x * h (x - t)

lemma jet_cross {z : ℂ} (hk : Integrable fun x : ℝ => k x * exp (-z * x))
    (hh : Integrable fun x : ℝ => h x * exp (z * x)) :
    Integrable (fun t : ℝ => cross k h t * exp (-z * t)) ∧
      jet (cross k h) 0 (-z) = jet k 0 (-z) * jet h 0 z := by
  have hh' : Integrable fun x : ℝ => h (-x) * exp (-z * x) := by
    simpa using hh.comp_neg
  have e : ∀ t : ℝ, convolution (fun x : ℝ => k x * exp (-z * x))
      (fun x : ℝ => h (-x) * exp (-z * x)) (ContinuousLinearMap.mul ℂ ℂ) volume t =
      cross k h t * exp (-z * t) := by
    intro t
    rw [convolution, cross, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.mul_apply', neg_sub]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h1 := hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hh'
  have h2 := integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hk hh'
  simp only [ContinuousLinearMap.mul_apply'] at h2
  refine ⟨h1.congr (Eventually.of_forall e), ?_⟩
  rw [jet_zero, jet_zero, jet_zero, ← integral_congr_ae (Eventually.of_forall e), h2,
    ← integral_neg_eq_self (fun x : ℝ => h x * exp (z * x))]
  simp

/-- `h` decays faster than every exponential. -/
structure Rapid (h : ℝ → ℂ) : Prop where
  aesm : AEStronglyMeasurable h
  decay : ∀ b : ℝ, ∃ C, ∀ x, ‖h x‖ ≤ C * Real.exp (-b * |x|)

lemma Rapid.convAt (hh : Rapid h) (σ : ℝ) : ConvAt h σ := by
  obtain ⟨C, hC⟩ := hh.decay (|σ| + 2)
  refine ⟨1, one_pos, ((integrable_exp_neg_mul_abs one_pos).const_mul C).mono'
    ((by fun_prop : Continuous fun x : ℝ => (Real.exp (σ * x + 1 * |x|) : ℂ)).aestronglyMeasurable.mul
      hh.aesm) (Eventually.of_forall fun x => ?_)⟩
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 := hC x
  have h2 : Real.exp (σ * x + 1 * |x|) * Real.exp (-(|σ| + 2) * |x|) ≤ Real.exp (-1 * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : σ * x ≤ |σ| * |x| := by rw [← abs_mul]; exact le_abs_self _
    linarith
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  calc _ ≤ Real.exp (σ * x + 1 * |x|) * (C * Real.exp (-(|σ| + 2) * |x|)) := by gcongr
    _ = C * (Real.exp (σ * x + 1 * |x|) * Real.exp (-(|σ| + 2) * |x|)) := by ring
    _ ≤ _ := by gcongr

/-- Transforms of rapidly decaying functions are bounded on vertical strips. -/
lemma Rapid.exists_norm_jet_le (hh : Rapid h) (b : ℝ) :
    ∃ B, ∀ z : ℂ, |z.re| ≤ b → ‖jet h 0 z‖ ≤ B := by
  obtain ⟨C, hC⟩ := hh.decay (b + 1)
  refine ⟨∫ x : ℝ, C * Real.exp (-1 * |x|), fun z hz => ?_⟩
  rw [jet_zero]
  refine norm_integral_le_of_norm_le ((integrable_exp_neg_mul_abs one_pos).const_mul C)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_exp, show (z * x).re = z.re * x by simp]
  have h2 : Real.exp (-(b + 1) * |x|) * Real.exp (z.re * x) ≤ Real.exp (-1 * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have := re_mul_le hz x
    linarith
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  calc _ ≤ C * Real.exp (-(b + 1) * |x|) * Real.exp (z.re * x) := by gcongr; exact hC x
    _ = C * (Real.exp (-(b + 1) * |x|) * Real.exp (z.re * x)) := by ring
    _ ≤ _ := by gcongr

/-- The right half of a function. -/
noncomputable abbrev pos (w : ℝ → ℂ) : ℝ → ℂ := (Ioi 0).indicator w

/-- The left half of a function. -/
noncomputable abbrev neg (w : ℝ → ℂ) : ℝ → ℂ := (Iic 0).indicator w

lemma pos_add_neg (w : ℝ → ℂ) (x : ℝ) : pos w x + neg w x = w x := by
  rcases le_or_gt x 0 with hx | hx
  · simp [pos, neg, hx, not_lt.2 hx]
  · simp [pos, neg, hx, not_le.2 hx]

/-- Functions of exponential type `a` in the mean. -/
def Tempered (a : ℝ) (w : ℝ → ℂ) : Prop :=
  ∀ b > a, Integrable fun x : ℝ => (Real.exp (-b * |x|) : ℂ) * w x

lemma Tempered.aesm (hw : Tempered a w) : AEStronglyMeasurable w := by
  have h := hw (a + 1) (by linarith)
  have h1 : Continuous fun x : ℝ => (Real.exp ((a + 1) * |x|) : ℂ) := by fun_prop
  refine (h1.aestronglyMeasurable.mul h.aestronglyMeasurable).congr
    (Eventually.of_forall fun x => ?_)
  change (Real.exp ((a + 1) * |x|) : ℂ) * ((Real.exp (-(a + 1) * |x|) : ℂ) * w x) = w x
  rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, ofReal_one,
    one_mul]

lemma Tempered.convAt_pos (hw : Tempered a w) {z : ℂ} (hz : a < z.re) : ConvAt (pos w) (-z).re := by
  refine ⟨(z.re - a) / 2, by linarith,
    ((hw ((z.re + a) / 2) (by linarith)).indicator measurableSet_Ioi (s := Ioi 0)).congr
    (Eventually.of_forall fun x => ?_)⟩
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [pos, indicator_of_mem hx, neg_re, abs_of_pos (mem_Ioi.1 hx)]
    congr 3; ring
  · simp [pos, indicator_of_notMem hx]

lemma Tempered.convAt_neg (hw : Tempered a w) {z : ℂ} (hz : z.re < -a) : ConvAt (neg w) (-z).re := by
  refine ⟨(-z.re - a) / 2, by linarith,
    ((hw ((-z.re + a) / 2) (by linarith)).indicator measurableSet_Iic (s := Iic 0)).congr
    (Eventually.of_forall fun x => ?_)⟩
  by_cases hx : x ∈ Iic (0 : ℝ)
  · simp only [neg, indicator_of_mem hx, neg_re, abs_of_nonpos (mem_Iic.1 hx)]
    congr 3; ring
  · simp [neg, indicator_of_notMem hx]

lemma cross_half_le (hw : Tempered a w) (hh : Rapid h) {b : ℝ} (hab : a < b) : ∃ C,
    (∀ t ≤ 0, ‖cross (pos w) h t‖ ≤ C * Real.exp (-b * |t|)) ∧
      ∀ t, 0 ≤ t → ‖cross (neg w) h t‖ ≤ C * Real.exp (-b * |t|) := by
  obtain ⟨C, hC⟩ := hh.decay b
  have hi := ((hw b hab).norm.const_mul C)
  have key : ∀ (s : Set ℝ) (t : ℝ), (∀ x ∈ s, |x - t| = |x| + |t|) →
      ‖cross (s.indicator w) h t‖ ≤
        (∫ x : ℝ, C * ‖(Real.exp (-b * |x|) : ℂ) * w x‖) * Real.exp (-b * |t|) := by
    intro s t hst
    rw [cross, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hi.mul_const _) (Eventually.of_forall fun x => ?_)
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 0)
      simpa using this
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc _ ≤ ‖w x‖ * (C * Real.exp (-b * |x - t|)) := by gcongr; exact hC _
        _ = _ := by rw [hst x hx, mul_add, Real.exp_add]; ring
    · rw [indicator_of_notMem hx, zero_mul, norm_zero]
      positivity
  refine ⟨_, fun t ht => key _ t fun x hx => ?_, fun t ht => key _ t fun x hx => ?_⟩
  · rw [abs_of_pos (mem_Ioi.1 hx), abs_of_nonpos ht, abs_of_nonneg (by linarith [mem_Ioi.1 hx])]; ring
  · rw [abs_of_nonpos (mem_Iic.1 hx), abs_of_nonneg ht, abs_of_nonpos (by linarith [mem_Iic.1 hx])]
    ring

lemma integrable_cross_integrand (hw : Tempered a w) (hh : Rapid h) (t : ℝ) :
    Integrable fun x => w x * h (x - t) := by
  set b := |a| + 1
  obtain ⟨C, hC⟩ := hh.decay b
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  refine ((hw b (by linarith [le_abs_self a])).norm.const_mul (C * Real.exp (b * |t|))).mono'
    (hw.aesm.mul (hh.aesm.comp_measurePreserving (measurePreserving_sub_right volume t)))
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : Real.exp (-b * |x - t|) ≤ Real.exp (b * |t|) * Real.exp (-b * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h2 : |x| ≤ |x - t| + |t| := by simpa using abs_add_le (x - t) t
    have : 0 ≤ b := by positivity
    nlinarith
  calc _ ≤ ‖w x‖ * (C * (Real.exp (b * |t|) * Real.exp (-b * |x|))) := by
        gcongr; exact (hC _).trans (by gcongr)
    _ = _ := by ring

lemma integrable_indicator_mul {g : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : Integrable fun x => w x * g x) : Integrable fun x => s.indicator w x * g x :=
  (h.indicator hs).congr (Eventually.of_forall fun _ => indicator_mul_left s w g)

lemma cross_pos_eq (hw : Tempered a w) (hh : Rapid h) (h0 : ∀ t, cross w h t = 0) (t : ℝ) :
    cross (pos w) h t = -cross (neg w) h t := by
  have h1 := integrable_cross_integrand hw hh t
  rw [eq_neg_iff_add_eq_zero, cross, cross, ← integral_add
    (integrable_indicator_mul measurableSet_Ioi h1)
    (integrable_indicator_mul measurableSet_Iic h1), ← h0 t, cross]
  simp only [← add_mul, pos_add_neg]

/-- The **Carleman transform**: if `w` annihilates the translates of `h`, the correlation of its
right half with `h` decays rapidly at both ends. -/
lemma rapid_cross (hw : Tempered a w) (hh : Rapid h) (h0 : ∀ t, cross w h t = 0) :
    Rapid (cross (pos w) h) := by
  constructor
  · set z : ℂ := ((|a| + 1 : ℝ) : ℂ)
    have hz : a < z.re := by simp only [z, ofReal_re]; linarith [le_abs_self a]
    have h1 := (jet_cross (hw.convAt_pos hz).integrable (hh.convAt _).integrable).1
    refine (h1.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ =>
      exp (z * t)).aestronglyMeasurable).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]
    rw [mul_assoc, ← Complex.exp_add]
    simp
  · intro b
    obtain ⟨C, hC1, hC2⟩ := cross_half_le hw hh (b := max b (|a| + 1))
      (lt_max_of_lt_right (by linarith [le_abs_self a]))
    refine ⟨C, fun t => ?_⟩
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC1 0 le_rfl)
      simpa using this
    have h1 : C * Real.exp (-max b (|a| + 1) * |t|) ≤ C * Real.exp (-b * |t|) := by
      gcongr; exact le_max_left _ _
    rcases le_total t 0 with ht | ht
    · exact (hC1 t ht).trans h1
    · rw [cross_pos_eq hw hh h0, norm_neg]
      exact (hC2 t ht).trans h1

lemma jet_cross_pos (hw : Tempered a w) (hh : Rapid h) {z : ℂ} (hz : a < z.re) :
    jet (cross (pos w) h) 0 (-z) = jet (pos w) 0 (-z) * jet h 0 z :=
  (jet_cross (hw.convAt_pos hz).integrable (hh.convAt _).integrable).2

lemma jet_cross_neg (hw : Tempered a w) (hh : Rapid h) (h0 : ∀ t, cross w h t = 0) {z : ℂ}
    (hz : z.re < -a) : jet (cross (pos w) h) 0 (-z) = -jet (neg w) 0 (-z) * jet h 0 z := by
  rw [neg_mul, ← (jet_cross (hw.convAt_neg hz).integrable (hh.convAt _).integrable).2, jet_zero,
    jet_zero, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [cross_pos_eq hw hh h0, neg_mul]


/-! ### Correlations of weighted `L²` functions -/

section Weighted

variable {f g : ℝ → ℂ}

lemma memLp_shift (hf : MemLp f 2) (τ : ℝ) : MemLp (fun s => f (s - τ)) 2 :=
  hf.comp_measurePreserving (measurePreserving_sub_right volume τ)

lemma integrable_mul_shift (hg : MemLp g 2) (hf : MemLp f 2) (τ : ℝ) :
    Integrable (fun s => g s * f (s - τ)) ∧
      ∫ s, ‖g s * f (s - τ)‖ ≤ (eLpNorm g 2).toReal * (eLpNorm f 2).toReal := by
  have hi : Integrable (fun s => g s * f (s - τ)) := hg.integrable_mul (memLp_shift hf τ)
  refine ⟨hi, ?_⟩
  have h1 := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    (memLp_shift hf τ).1 hg.1
  have h2 : eLpNorm (fun s => f (s - τ)) 2 = eLpNorm f 2 :=
    eLpNorm_comp_measurePreserving hf.1 (measurePreserving_sub_right volume τ)
  rw [h2, eLpNorm_one_eq_lintegral_enorm] at h1
  rw [integral_norm_eq_lintegral_enorm hi.1, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hg.2.ne hf.2.ne) h1

/-- The weight `e^{a(|s| - |s - τ| - |τ|)}`, which is at most `1`. -/
noncomputable def damp (a τ s : ℝ) : ℝ := Real.exp (a * (|s| - |s - τ| - |τ|))

lemma damp_pos (a τ s : ℝ) : 0 < damp a τ s := Real.exp_pos _

lemma damp_le (ha : 0 ≤ a) (τ s : ℝ) : damp a τ s ≤ 1 := by
  rw [damp, Real.exp_le_one_iff]
  have : |s| ≤ |s - τ| + |τ| := by simpa using abs_add_le (s - τ) τ
  nlinarith

lemma continuous_damp (a : ℝ) : Continuous fun p : ℝ × ℝ => damp a p.1 p.2 := by
  unfold damp; fun_prop

/-- The damped correlation of two `L²` functions. -/
noncomputable def bil (a : ℝ) (g f : ℝ → ℂ) (τ : ℝ) : ℂ := ∫ s, damp a τ s * (g s * f (s - τ))

lemma integrable_bil (ha : 0 ≤ a) (hg : MemLp g 2) (hf : MemLp f 2) (τ : ℝ) :
    Integrable fun s => (damp a τ s : ℂ) * (g s * f (s - τ)) := by
  have hc : Continuous fun s => (damp a τ s : ℂ) :=
    continuous_ofReal.comp ((continuous_damp a).comp (by fun_prop : Continuous fun s => (τ, s)))
  refine (integrable_mul_shift hg hf τ).1.mono
    (hc.aestronglyMeasurable.mul (integrable_mul_shift hg hf τ).1.1) (Eventually.of_forall fun s => ?_)
  rw [norm_mul, norm_real, Real.norm_of_nonneg (damp_pos a τ s).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (damp_le ha τ s)

lemma norm_bil_le (ha : 0 ≤ a) (hg : MemLp g 2) (hf : MemLp f 2) (τ : ℝ) :
    ‖bil a g f τ‖ ≤ (eLpNorm g 2).toReal * (eLpNorm f 2).toReal := by
  refine (norm_integral_le_of_norm_le (integrable_mul_shift hg hf τ).1.norm
    (Eventually.of_forall fun s => ?_)).trans (integrable_mul_shift hg hf τ).2
  rw [norm_mul, norm_real, Real.norm_of_nonneg (damp_pos a τ s).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (damp_le ha τ s)

lemma exists_approx (hf : MemLp f 2) {δ : ℝ} (hδ : 0 < δ) : ∃ f' : ℝ → ℂ, HasCompactSupport f' ∧
    Continuous f' ∧ MemLp f' 2 ∧ (eLpNorm (f - f') 2).toReal ≤ δ ∧
      (eLpNorm f' 2).toReal ≤ (eLpNorm f 2).toReal + δ := by
  obtain ⟨f', h1, h2, h3, h4⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by simp)
    (ε := ENNReal.ofReal δ) (by simpa using hδ)
  have h5 : (eLpNorm (f - f') 2).toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ.le h2
  refine ⟨f', h1, h3, h4, h5, ?_⟩
  have h6 : eLpNorm f' 2 ≤ eLpNorm f 2 + eLpNorm (f - f') 2 := by
    have := eLpNorm_sub_le (μ := volume) (p := 2) hf.1 (hf.sub h4).1 (by norm_num)
    rwa [sub_sub_cancel] at this
  have h7 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.2.ne, (hf.sub h4).2.ne⟩) h6
  rw [ENNReal.toReal_add hf.2.ne (hf.sub h4).2.ne] at h7
  linarith

lemma continuous_bil (a : ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) (hf : Continuous f) :
    Continuous (bil a g f) := by
  have e : bil a g f = fun τ => ∫ s in tsupport g, (damp a τ s : ℂ) * (g s * f (s - τ)) := by
    funext τ
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hs, zero_mul, mul_zero]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ hgc.isCompact
  have := continuous_damp a
  exact (by fun_prop : Continuous fun p : ℝ × ℝ => (damp a p.1 p.2 : ℂ) * (g p.2 * f (p.2 - p.1)))

lemma hasCompactSupport_bil (a : ℝ) (hg : HasCompactSupport g) (hf : HasCompactSupport f) :
    HasCompactSupport (bil a g f) := by
  refine HasCompactSupport.intro
    ((IsCompact.prod hg hf).image (continuous_fst.sub continuous_snd)) fun τ hτ => ?_
  rw [bil, integral_congr_ae (g := fun _ => 0), integral_zero]
  refine Eventually.of_forall fun s => ?_
  by_cases h1 : s ∈ tsupport g
  · have h2 : s - τ ∉ tsupport f := fun h => hτ ⟨(s, s - τ), ⟨h1, h⟩, by simp⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

lemma exists_bil_approx (ha : 0 ≤ a) (hg : MemLp g 2) (hf : MemLp f 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ → ℂ, Continuous q ∧ HasCompactSupport q ∧ ∀ τ, ‖bil a g f τ - q τ‖ ≤ ε := by
  set N := (eLpNorm g 2).toReal + (eLpNorm f 2).toReal + 1
  have hN : 0 < N := by positivity
  set δ := min 1 (ε / N)
  have hδ : 0 < δ := by positivity
  obtain ⟨f', f1, f2, f3, f4, f5⟩ := exists_approx hf hδ
  obtain ⟨g', g1, g2, g3, g4, -⟩ := exists_approx hg hδ
  refine ⟨bil a g' f', continuous_bil a g2 g1 f2, hasCompactSupport_bil a g1 f1, fun τ => ?_⟩
  have e : bil a g f τ - bil a g' f' τ = bil a g (f - f') τ + bil a (g - g') f' τ := by
    rw [bil, bil, bil, bil, ← integral_sub (integrable_bil ha hg hf τ) (integrable_bil ha g3 f3 τ),
      ← integral_add (integrable_bil ha hg (hf.sub f3) τ) (integrable_bil ha (hg.sub g3) f3 τ)]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [e]
  have h1 := norm_bil_le ha hg (hf.sub f3) τ
  have h2 := norm_bil_le ha (hg.sub g3) f3 τ
  have h3 : δ * N ≤ ε := (mul_le_mul_of_nonneg_right (min_le_right _ _) hN.le).trans
    (div_mul_cancel₀ ε hN.ne').le
  have h4 : δ ≤ 1 := min_le_left _ _
  have h5 : (0 : ℝ) ≤ (eLpNorm g 2).toReal := ENNReal.toReal_nonneg
  have h6 : (0 : ℝ) ≤ (eLpNorm f 2).toReal := ENNReal.toReal_nonneg
  calc _ ≤ (eLpNorm g 2).toReal * δ + δ * ((eLpNorm f 2).toReal + δ) := by
        refine (norm_add_le _ _).trans (add_le_add (h1.trans (by gcongr)) (h2.trans ?_))
        gcongr
    _ ≤ δ * N := by simp only [N]; nlinarith
    _ ≤ ε := h3

/-- The damped correlation is continuous and vanishes at infinity. -/
lemma bil_continuous (ha : 0 ≤ a) (hg : MemLp g 2) (hf : MemLp f 2) :
    Continuous (bil a g f) ∧ Tendsto (bil a g f) (cocompact ℝ) (𝓝 0) := by
  constructor
  · refine continuous_of_uniform_approx_of_continuous fun v hv => ?_
    obtain ⟨ε, hε, hv⟩ := Metric.mem_uniformity_dist.1 hv
    obtain ⟨q, h1, -, h3⟩ := exists_bil_approx ha hg hf (half_pos hε)
    refine ⟨q, h1, fun τ => hv ?_⟩
    rw [dist_eq_norm]
    linarith [h3 τ]
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨q, -, h2, h3⟩ := exists_bil_approx ha hg hf (half_pos hε)
    filter_upwards [h2.isCompact.compl_mem_cocompact] with τ hτ
    have := h3 τ
    rw [image_eq_zero_of_notMem_tsupport hτ, sub_zero] at this
    rw [dist_zero_right]
    linarith

end Weighted

/-- `u` and `y` are dual: one is `e^{-a|x|}` and the other `e^{a|x|}` times an `L²` function. -/
structure Dual (a : ℝ) (y u : ℝ → ℂ) : Prop where
  left : MemLp (fun x => (Real.exp (-a * |x|) : ℂ) * y x) 2
  right : MemLp (fun x => (Real.exp (a * |x|) : ℂ) * u x) 2

lemma aesm_of_exp_mul {c : ℝ} (h : AEStronglyMeasurable fun x => (Real.exp (c * |x|) : ℂ) * u x) :
    AEStronglyMeasurable u := by
  have h1 : Continuous fun x : ℝ => (Real.exp (-(c * |x|)) : ℂ) := by fun_prop
  refine (h1.aestronglyMeasurable.mul h).congr (Eventually.of_forall fun x => ?_)
  change (Real.exp (-(c * |x|)) : ℂ) * ((Real.exp (c * |x|) : ℂ) * u x) = u x
  rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, ofReal_one, one_mul]

/-- The correlation exists and grows at most like `e^{a|τ|}`. -/
structure CrossBound (a : ℝ) (y u : ℝ → ℂ) (K : ℝ) : Prop where
  aesm_left : AEStronglyMeasurable y
  aesm_right : AEStronglyMeasurable u
  integrable : ∀ τ, Integrable fun s => y s * u (s - τ)
  le : ∀ τ, ∫ s, ‖y s * u (s - τ)‖ ≤ K * Real.exp (a * |τ|)

namespace Dual

lemma cross_integrand (a : ℝ) (y u : ℝ → ℂ) (τ s : ℝ) : y s * u (s - τ) = Real.exp (a * |τ|) * (damp a τ s *
    ((Real.exp (-a * |s|) : ℂ) * y s * ((Real.exp (a * |s - τ|) : ℂ) * u (s - τ)))) := by
  rw [damp]
  have : Real.exp (a * |τ|) * Real.exp (a * (|s| - |s - τ| - |τ|)) * Real.exp (-a * |s|) *
      Real.exp (a * |s - τ|) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff]; ring
  have h2 := congrArg (fun r : ℝ => (r : ℂ)) this
  simp only [ofReal_mul, ofReal_one] at h2
  linear_combination -(y s * u (s - τ)) * h2

lemma cross_eq (a : ℝ) (y u : ℝ → ℂ) (τ : ℝ) : cross y u τ = Real.exp (a * |τ|) *
    bil a (fun x => (Real.exp (-a * |x|) : ℂ) * y x) (fun x => (Real.exp (a * |x|) : ℂ) * u x) τ := by
  rw [cross, bil, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall (cross_integrand a y u τ))

variable (hd : Dual a y u)
include hd

lemma crossBound (ha : 0 ≤ a) : ∃ K, CrossBound a y u K := by
  refine ⟨(eLpNorm (fun x => (Real.exp (-a * |x|) : ℂ) * y x) 2).toReal *
    (eLpNorm (fun x => (Real.exp (a * |x|) : ℂ) * u x) 2).toReal, aesm_of_exp_mul hd.left.1, aesm_of_exp_mul hd.right.1, fun τ => ?_, fun τ => ?_⟩
  · simp only [cross_integrand a y u τ]
    exact (integrable_bil ha hd.left hd.right τ).const_mul _
  · simp only [cross_integrand a y u τ, norm_mul (Real.exp (a * |τ|) : ℂ), norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [integral_const_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right (le_trans ?_ (integrable_mul_shift hd.left hd.right τ).2)
      (Real.exp_pos _).le
    refine integral_mono (integrable_bil ha hd.left hd.right τ).norm
      (integrable_mul_shift hd.left hd.right τ).1.norm fun s => ?_
    simp only
    rw [norm_mul (damp a τ s : ℂ), norm_real, Real.norm_of_nonneg (damp_pos a τ s).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (damp_le ha τ s)

lemma continuous_cross (ha : 0 ≤ a) : Continuous (cross y u) := by
  have := (bil_continuous ha hd.left hd.right).1
  rw [show cross y u = _ from funext (cross_eq a y u)]
  fun_prop

lemma tendsto_cross (ha : 0 ≤ a) :
    Tendsto (fun τ => Real.exp (-a * |τ|) * ‖cross y u τ‖) (cocompact ℝ) (𝓝 0) := by
  have h := (bil_continuous ha hd.left hd.right).2.norm
  rw [norm_zero] at h
  refine h.congr fun τ => ?_
  rw [cross_eq a y u, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc,
    ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]

lemma tempered : Tempered a y := fun b hb => by
  have h1 : MemLp (fun x : ℝ => (Real.exp (-(b - a) * |x|) : ℂ)) 2 := by
    have hc : Continuous fun x : ℝ => (Real.exp (-(b - a) * |x|) : ℂ) := by fun_prop
    rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
    refine (integrable_exp_neg_mul_abs (c := 2 * (b - a)) (by linarith)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  refine (h1.integrable_mul hd.left).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add]
  congr 3; ring

lemma convAt {σ : ℝ} (hσ : |σ| < a) : ConvAt u σ := by
  set c := (a - |σ|) / 2
  have hc : 0 < c := by simp only [c]; linarith
  refine ⟨c, hc, ?_⟩
  have h1 : MemLp (fun x : ℝ => (Real.exp (σ * x + c * |x| - a * |x|) : ℂ)) 2 := by
    have hc' : Continuous fun x : ℝ => (Real.exp (σ * x + c * |x| - a * |x|) : ℂ) := by fun_prop
    rw [memLp_two_iff_integrable_sq_norm hc'.aestronglyMeasurable]
    refine (integrable_exp_neg_mul_abs (c := 2 * c) (by linarith)).mono'
      (hc'.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simp only [norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have : σ * x ≤ |σ| * |x| := by rw [← abs_mul]; exact le_abs_self _
    simp only [c] at *
    push_cast
    nlinarith
  refine (h1.integrable_mul hd.right).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add]
  congr 3; ring

end Dual

lemma CrossBound.indicator {K : ℝ} (hb : CrossBound a y u K) {s : Set ℝ} (hs : MeasurableSet s) :
    CrossBound a (s.indicator y) u K := by
  have hi : ∀ τ, Integrable fun x => s.indicator y x * u (x - τ) := fun τ =>
    integrable_indicator_mul (g := fun x => u (x - τ)) hs (hb.integrable τ)
  refine ⟨hb.aesm_left.indicator hs, hb.aesm_right, hi, fun τ => le_trans ?_ (hb.le τ)⟩
  refine integral_mono (hi τ).norm (hb.integrable τ).norm fun x => ?_
  simp only [norm_mul]
  gcongr
  exact norm_indicator_le_norm_self _ _

lemma CrossBound.norm_le {K : ℝ} (hb : CrossBound a y u K) (τ : ℝ) :
    ‖cross y u τ‖ ≤ K * Real.exp (a * |τ|) := (norm_integral_le_integral_norm _).trans (hb.le τ)

/-- Correlations with two functions commute. -/
lemma cross_comm {K : ℝ} (hb : CrossBound a y u K) (hh : Rapid h) (t : ℝ) :
    cross (cross y u) h t = cross (cross y h) u t := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => y p.2 * u (p.2 - p.1) * h (p.1 - t))
      (volume.prod volume) := by
    refine (hb.aesm_left.comp_snd.mul (hb.aesm_right.comp_quasiMeasurePreserving ?_)).mul
      ((hh.aesm.comp_measurePreserving (measurePreserving_sub_right volume t)).comp_fst)
    exact (quasiMeasurePreserving_sub_of_right_invariant volume volume).comp
      Measure.measurePreserving_swap.quasiMeasurePreserving
  have hi : Integrable (fun p : ℝ × ℝ => y p.2 * u (p.2 - p.1) * h (p.1 - t))
      (volume.prod volume) := by
    refine (integrable_prod_iff hm).2
      ⟨Eventually.of_forall fun τ => (hb.integrable τ).mul_const (h (τ - t)), ?_⟩
    obtain ⟨C, hC⟩ := hh.decay (|a| + 1)
    refine ((integrable_exp_neg_mul_abs one_pos).const_mul
      (K * C * Real.exp ((|a| + 1) * |t|))).mono' hm.norm.integral_prod_right'
      (Eventually.of_forall fun τ => ?_)
    simp only [norm_mul _ (h _), integral_mul_const]
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (integral_nonneg fun s => norm_nonneg _)]
    have h1 : Real.exp (a * |τ|) * Real.exp (-(|a| + 1) * |τ - t|) ≤
        Real.exp ((|a| + 1) * |t|) * Real.exp (-1 * |τ|) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h2 : |τ| ≤ |τ - t| + |t| := by simpa using abs_add_le (τ - t) t
      nlinarith [le_abs_self a, abs_nonneg a, abs_nonneg τ]
    have hK : 0 ≤ K := by simpa using (integral_nonneg fun s => norm_nonneg _).trans (hb.le 0)
    have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
    calc _ ≤ K * Real.exp (a * |τ|) * (C * Real.exp (-(|a| + 1) * |τ - t|)) := by
          gcongr
          · exact hb.le τ
          · exact hC _
      _ = K * C * (Real.exp (a * |τ|) * Real.exp (-(|a| + 1) * |τ - t|)) := by ring
      _ ≤ K * C * (Real.exp ((|a| + 1) * |t|) * Real.exp (-1 * |τ|)) := by gcongr
      _ = _ := by ring
  have hs : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + t - p.2))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (g := fun s x : ℝ => s + t - x) (MeasurePreserving.id volume)
      (by fun_prop) (Eventually.of_forall fun s => (Measure.measurePreserving_sub_left volume (s + t)).map_eq)
  have hi' : Integrable (fun p : ℝ × ℝ => y p.1 * u (p.2 - t) * h (p.1 - p.2))
      (volume.prod volume) := by
    refine ((hs.integrable_comp hi.swap.1).2 hi.swap).congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Prod.swap]
    congr 2
    · congr 1; ring
    · ring
  calc cross (cross y u) h t = ∫ τ, ∫ s, y s * u (s - τ) * h (τ - t) := by
        simp only [cross, integral_mul_const]
    _ = ∫ s, ∫ τ, y s * u (s - τ) * h (τ - t) := integral_integral_swap hi
    _ = ∫ s, ∫ x, y s * u (x - t) * h (s - x) := by
        refine integral_congr_ae (Eventually.of_forall fun s => ?_)
        simp only
        rw [← integral_sub_left_eq_self _ volume (s + t)]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        congr 2
        · congr 1; ring
        · ring
    _ = ∫ x, ∫ s, y s * u (x - t) * h (s - x) := integral_integral_swap hi'
    _ = _ := by
        simp only [cross, ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        refine integral_congr_ae (Eventually.of_forall fun s => ?_)
        simp only
        ring


/-! ### Division of entire functions -/

lemma exists_entire_quotient {X G : ℂ → ℂ} (hX : Differentiable ℂ X) (hG : Differentiable ℂ G)
    (hne : ∀ z, analyticOrderAt X z ≠ ⊤) (h : ∀ z, analyticOrderAt X z ≤ analyticOrderAt G z) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z, G z = X z * F z := by
  have hm : MeromorphicOn (G / X) univ := fun z _ =>
    (hG.analyticAt z).meromorphicAt.div (hX.analyticAt z).meromorphicAt
  let F := toMeromorphicNFOn (G / X) univ
  have hev : ∀ z, F =ᶠ[𝓝[≠] z] G / X := fun z =>
    hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have hF : Differentiable ℂ F := fun z => by
    refine AnalyticAt.differentiableAt (((meromorphicNFOn_toMeromorphicNFOn (G / X) univ)
      (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_)
    rw [meromorphicOrderAt_congr (hev z), div_eq_mul_inv,
      meromorphicOrderAt_mul (hG.analyticAt z).meromorphicAt (hX.analyticAt z).meromorphicAt.inv,
      meromorphicOrderAt_inv, (hG.analyticAt z).meromorphicOrderAt_eq,
      (hX.analyticAt z).meromorphicOrderAt_eq]
    have h1 := h z
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (hne z)
    rw [← hn] at h1 ⊢
    induction hG' : analyticOrderAt G z using ENat.recTopCoe with
    | top => simp
    | coe m =>
      rw [hG'] at h1
      have h2 : n ≤ m := by exact_mod_cast h1
      have h3 : (0 : ℤ) ≤ (m : ℤ) + -(n : ℤ) := by omega
      change (0 : WithTop ℤ) ≤ ((m : ℤ) : WithTop ℤ) + -((n : ℤ) : WithTop ℤ)
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
      exact_mod_cast h3
  refine ⟨F, hF, fun z => ?_⟩
  have h0 : ∀ᶠ w in 𝓝[≠] z, X w ≠ 0 := by
    rcases (hX.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.2 h) (hne z)
    · exact h
  have h1 : G =ᶠ[𝓝[≠] z] fun w => X w * F w := by
    filter_upwards [h0, hev z] with w hw hw'
    rw [hw', Pi.div_apply, mul_div_cancel₀ _ hw]
  exact tendsto_nhds_unique (hG.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (((hX.mul hF).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' h1.symm)

/-- If the quotient `G / X` is `o(1/η)` along a ray ending at `z`, it has no pole at `z`. -/
lemma order_le_of_tendsto {X G : ℂ → ℂ} {z : ℂ} {d : ℂ} (hd : d ≠ 0) {Q : ℝ → ℂ}
    (hX : AnalyticAt ℂ X z) (hG : AnalyticAt ℂ G z) (hne : analyticOrderAt X z ≠ ⊤)
    (hQ : ∀ η : ℝ, 0 < η → G (z + η * d) = Q η * X (z + η * d))
    (hlim : Tendsto (fun η : ℝ => η * ‖Q η‖) (𝓝[>] 0) (𝓝 0)) :
    analyticOrderAt X z ≤ analyticOrderAt G z := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne_top
  rw [← hm, ← hn] at hlt
  have hnm : n < m := by exact_mod_cast hlt
  obtain ⟨g, hg, hg0, hg1⟩ := hG.analyticOrderAt_eq_natCast.1 hn.symm
  obtain ⟨x, hx, -, hx1⟩ := hX.analyticOrderAt_eq_natCast.1 hm.symm
  have hray : Tendsto (fun η : ℝ => z + η * d) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous fun η : ℝ => z + η * d := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ η : ℝ in 𝓝[>] 0, ‖g (z + η * d)‖ =
      η ^ (m - n - 1) * ‖d‖ ^ (m - n) * ‖x (z + η * d)‖ * (η * ‖Q η‖) := by
    filter_upwards [hray.eventually hg1, hray.eventually hx1, self_mem_nhdsWithin] with η e1 e2 hη
    have hη' : (0 : ℝ) < η := hη
    have e3 := hQ η hη'
    rw [e1, e2] at e3
    simp only [add_sub_cancel_left, smul_eq_mul] at e3
    have hne' : ((η : ℂ) * d) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero (by exact_mod_cast hη'.ne') hd)
    have e4 : g (z + η * d) = Q η * (((η : ℂ) * d) ^ (m - n) * x (z + η * d)) := by
      refine mul_left_cancel₀ hne' ?_
      rw [e3]
      nth_rw 1 [← Nat.add_sub_cancel' hnm.le]
      rw [pow_add]
      ring
    rw [e4, norm_mul, norm_mul, norm_pow, norm_mul, norm_real, Real.norm_of_nonneg hη'.le]
    obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, mul_pow]
    ring
  have h2 : Tendsto (fun η : ℝ => η ^ (m - n - 1) * ‖d‖ ^ (m - n) * ‖x (z + η * d)‖ * (η * ‖Q η‖))
      (𝓝[>] 0) (𝓝 (0 ^ (m - n - 1) * ‖d‖ ^ (m - n) * ‖x z‖ * 0)) := by
    refine Tendsto.mul (Tendsto.mul (Tendsto.mul ?_ tendsto_const_nhds) ?_) hlim
    · exact ((continuous_pow _).tendsto 0).mono_left nhdsWithin_le_nhds
    · exact (hx.continuousAt.tendsto.comp hray).norm
  rw [mul_zero] at h2
  exact hg0 (norm_eq_zero.1 (tendsto_nhds_unique
    ((hg.continuousAt.tendsto.comp hray).norm.congr' h1) h2))

/-- A Phragmén–Lindelöf principle: subgaussian growth along a sequence of heights. -/
lemma norm_le_of_heights {F : ℂ → ℂ} (hF : Differentiable ℂ F) {b M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ z : ℂ, |z.re| = b → ‖F z‖ ≤ M)
    (hh : ∀ ε > 0, ∀ R : ℝ, ∃ T ≥ R, ∀ z : ℂ, |z.im| = T → |z.re| ≤ b →
      ‖F z‖ ≤ M * Real.exp (ε * T ^ 2)) {z : ℂ} (hz : |z.re| ≤ b) : ‖F z‖ ≤ M := by
  have hnorm : ∀ (ε : ℝ) (w : ℂ), ‖F w * exp (ε * w ^ 2)‖ =
      ‖F w‖ * Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) := fun ε w => by
    rw [norm_mul, norm_exp, re_ofReal_mul, sq w, mul_re]; ring_nf
  have key : ∀ ε > 0, ‖F z‖ * Real.exp (ε * (z.re ^ 2 - z.im ^ 2)) ≤ M * Real.exp (ε * b ^ 2) := by
    intro ε hε
    obtain ⟨T, hT, hTF⟩ := hh ε hε (|z.im| + 1)
    have hb : 0 ≤ b := (abs_nonneg _).trans hz
    rcases hb.eq_or_lt with hb0 | hb0
    · have h0 : |z.re| = b := le_antisymm hz (hb0 ▸ abs_nonneg _)
      have h1 := hv z h0
      rw [← sq_abs z.re, h0]
      gcongr
      nlinarith [sq_nonneg z.im]
    have hT0 : 0 < T := by linarith [abs_nonneg z.im]
    rw [← hnorm]
    have hcl : closure (Ioo (-b) b ×ℂ Ioo (-T) T) = Icc (-b) b ×ℂ Icc (-T) T := by
      rw [closure_reProdIm, closure_Ioo (by linarith), closure_Ioo (by linarith)]
    refine norm_le_of_forall_mem_frontier_norm_le
      (f := fun w => F w * exp (ε * w ^ 2)) (U := Ioo (-b) b ×ℂ Ioo (-T) T)
      ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _))
      (Differentiable.diffContOnCl (by fun_prop)) (fun w hw => ?_) ?_
    · rw [hnorm]
      have hmem := hcl ▸ frontier_subset_closure hw
      rw [mem_reProdIm, mem_Icc, mem_Icc, ← abs_le, ← abs_le] at hmem
      have hre : w.re ^ 2 ≤ b ^ 2 := sq_le_sq.2 (by rw [abs_of_pos hb0]; exact hmem.1)
      have hfr : |w.re| = b ∨ |w.im| = T := by
        by_contra hcon
        rw [not_or] at hcon
        have hint : w ∈ Ioo (-b) b ×ℂ Ioo (-T) T := by
          rw [mem_reProdIm, mem_Ioo, mem_Ioo, ← abs_lt, ← abs_lt]
          exact ⟨lt_of_le_of_ne hmem.1 hcon.1, lt_of_le_of_ne hmem.2 hcon.2⟩
        have hop : IsOpen (Ioo (-b) b ×ℂ Ioo (-T) T) := isOpen_Ioo.reProdIm isOpen_Ioo
        rw [hop.frontier_eq] at hw
        exact hw.2 hint
      rcases hfr with h1 | h1
      · have := hv w h1
        gcongr
        nlinarith [sq_nonneg w.im]
      · calc _ ≤ M * Real.exp (ε * T ^ 2) * Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) := by
              gcongr; exact hTF w h1 hmem.1
          _ = M * Real.exp (ε * w.re ^ 2) := by
              rw [mul_assoc, ← Real.exp_add, ← sq_abs w.im, h1]; ring_nf
          _ ≤ _ := by gcongr
    · rw [hcl, mem_reProdIm, mem_Icc, mem_Icc, ← abs_le, ← abs_le]
      exact ⟨hz, by linarith⟩
  have hl : Tendsto (fun ε : ℝ => ‖F z‖ * Real.exp (ε * (z.re ^ 2 - z.im ^ 2))) (𝓝[>] 0)
      (𝓝 ‖F z‖) := by
    have : Continuous fun ε : ℝ => ‖F z‖ * Real.exp (ε * (z.re ^ 2 - z.im ^ 2)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun ε : ℝ => M * Real.exp (ε * b ^ 2)) (𝓝[>] 0) (𝓝 M) := by
    have : Continuous fun ε : ℝ => M * Real.exp (ε * b ^ 2) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hl hr (eventually_mem_nhdsWithin.mono key)

/-! ### One-sided transforms -/

/-- Continuous functions that are `o(e^{a|x|})`. -/
structure Little (a : ℝ) (p : ℝ → ℂ) (K : ℝ) : Prop where
  continuous : Continuous p
  le : ∀ τ, ‖p τ‖ ≤ K * Real.exp (a * |τ|)
  tendsto : Tendsto (fun τ => Real.exp (-a * |τ|) * ‖p τ‖) (cocompact ℝ) (𝓝 0)

section Little

variable {p : ℝ → ℂ} {K : ℝ}

lemma tempered_of_le (hp : AEStronglyMeasurable p) (hK : ∀ τ, ‖p τ‖ ≤ K * Real.exp (a * |τ|)) :
    Tempered a p := fun b hb => by
  refine ((integrable_exp_neg_mul_abs (sub_pos.2 hb)).const_mul K).mono'
    ((by fun_prop : Continuous fun x : ℝ => (Real.exp (-b * |x|) : ℂ)).aestronglyMeasurable.mul hp)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc _ ≤ Real.exp (-b * |x|) * (K * Real.exp (a * |x|)) := by gcongr; exact hK x
    _ = K * (Real.exp (-b * |x|) * Real.exp (a * |x|)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

lemma Little.tempered (hp : Little a p K) : Tempered a p :=
  tempered_of_le hp.continuous.aestronglyMeasurable hp.le

lemma Little.reflect (hp : Little a p K) : Little a (fun x => p (-x)) K where
  continuous := hp.continuous.comp continuous_neg
  le τ := by simpa using hp.le (-τ)
  tendsto := by
    have := hp.tendsto.comp (Homeomorph.neg ℝ).isClosedEmbedding.tendsto_cocompact
    simpa [Function.comp_def] using this

lemma jet_neg (w : ℝ → ℂ) (z : ℂ) : jet (neg w) 0 z = jet (pos fun x => w (-x)) 0 (-z) := by
  rw [jet_zero, jet_zero, ← integral_neg_eq_self]
  have h4 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  refine integral_congr_ae (h4.mono fun x hx => ?_)
  rcases lt_or_gt_of_ne hx with h | h
  · simp [neg, pos, not_lt.2 h.le, h]
  · simp [neg, pos, h, h.le]

lemma norm_jet_le {z : ℂ} {η : ℝ} (hz : z.re = a + η) :
    ‖jet (pos p) 0 (-z)‖ ≤
      ∫ τ in Ioi (0 : ℝ), Real.exp (-a * |τ|) * ‖p τ‖ * Real.exp (-η * τ) := by
  rw [jet_zero, ← integral_indicator measurableSet_Ioi]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun τ => ?_)))
  by_cases h : τ ∈ Ioi (0 : ℝ)
  · simp only [pos, indicator_of_mem h, norm_mul, norm_exp, abs_of_pos (mem_Ioi.1 h)]
    rw [mul_comm (Real.exp _) ‖p τ‖, mul_assoc, ← Real.exp_add]
    congr 2
    simp [hz]; ring
  · simp [pos, indicator_of_notMem h]

lemma Little.norm_jet_le_div (hp : Little a p K) {z : ℂ} (hz : a < z.re) :
    ‖jet (pos p) 0 (-z)‖ ≤ K / (z.re - a) := by
  have hη := sub_pos.2 hz
  refine (norm_jet_le (p := p) (a := a) (η := z.re - a) (by ring)).trans ?_
  have e : ∫ τ in Ioi (0 : ℝ), K * Real.exp (-(z.re - a) * τ) = K / (z.re - a) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]
  rw [← e]
  refine integral_mono_of_nonneg (Eventually.of_forall fun τ => by positivity)
    ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul K) (Eventually.of_forall fun τ => ?_)
  simp only
  gcongr
  rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]
  exact hp.le τ

/-- An Abelian estimate at the edge of the half-plane of convergence. -/
lemma Little.tendsto_jet (hp : Little a p K) {z : ℂ} (hz : z.re = a) :
    Tendsto (fun η : ℝ => η * ‖jet (pos p) 0 (-(z + η))‖) (𝓝[>] 0) (𝓝 0) := by
  set r : ℝ → ℝ := fun τ => Real.exp (-a * |τ|) * ‖p τ‖
  have hr : Continuous r := by have := hp.continuous; fun_prop
  have hr0 : ∀ τ, 0 ≤ r τ := fun τ => by positivity
  have hrK : ∀ τ, r τ ≤ K := fun τ => by
    simp only [r]
    rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]
    exact hp.le τ
  have h1 : Tendsto (fun η : ℝ => ∫ s in Ioi (0 : ℝ), r (η⁻¹ * s) * Real.exp (-s)) (𝓝[>] 0)
      (𝓝 (∫ s in Ioi (0 : ℝ), 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => K * Real.exp (-s))
      (Eventually.of_forall fun η => ?_) (Eventually.of_forall fun η =>
        Eventually.of_forall fun s => ?_) ?_ ?_
    · exact (by fun_prop : Continuous fun s => r (η⁻¹ * s) * Real.exp (-s)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_of_nonneg (hr0 _), Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
      exact hrK _
    · simpa using (integrableOn_exp_mul_Ioi (neg_one_lt_zero (R := ℝ)) 0).const_mul K
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have h2 : Tendsto (fun η : ℝ => η⁻¹ * s) (𝓝[>] 0) (cocompact ℝ) :=
        (tendsto_inv_nhdsGT_zero.atTop_mul_const (mem_Ioi.1 hs)).mono_right atTop_le_cocompact
      have h3 := (hp.tendsto.comp h2).mul_const (Real.exp (-s))
      rwa [zero_mul] at h3
  rw [integral_zero] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with η hη
    have : (0 : ℝ) < η := hη
    positivity
  · filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : (0 : ℝ) < η := hη
    have h2 := norm_jet_le (p := p) (z := z + η) (η := η) (a := a) (by simp [hz])
    have h3 := integral_comp_mul_left_Ioi (fun s => r (η⁻¹ * s) * Real.exp (-s)) 0 hη'
    rw [mul_zero, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hη'.ne'] at h3
    rw [← h3]
    refine mul_le_mul_of_nonneg_left (h2.trans (le_of_eq ?_)) hη'.le
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    simp only [r]
    rw [inv_mul_cancel_left₀ hη'.ne', neg_mul η]

/-- The one-sided Laplace transform determines a continuous function. -/
lemma Little.eq_zero (hp : Little a p K) (h : ∀ z : ℂ, a < z.re → jet (pos p) 0 (-z) = 0) {τ : ℝ}
    (hτ : 0 < τ) : p τ = 0 := by
  set f : ℝ → ℂ := fun x => pos p x * exp (-((a + 1 : ℝ) : ℂ) * x)
  have hf : Integrable f := by
    have := hp.tempered.convAt_pos (z := ((a + 1 : ℝ) : ℂ)) (by simp)
    exact this.integrable
  have hF : 𝓕 f = fun _ => 0 := by
    funext ξ
    rw [Real.fourier_real_eq_integral_exp_smul, ← h (((a + 1 : ℝ) : ℂ) + (2 * Real.pi * ξ : ℝ) * I)
      (by simp), jet_zero]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [f, smul_eq_mul]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hc : ContinuousAt f τ := by
    refine ContinuousAt.mul (hp.continuous.continuousAt.congr ?_) (by fun_prop)
    filter_upwards [Ioi_mem_nhds hτ] with x hx
    rw [pos, indicator_of_mem hx]
  have h1 := hf.fourierInv_fourier_eq (by rw [hF]; exact integrable_zero _ _ _) hc
  rw [hF, Real.fourierInv_eq'] at h1
  simp only [smul_zero, integral_zero, f, pos, indicator_of_mem (mem_Ioi.2 hτ)] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_right (exp_ne_zero _)

end Little

/-! ### Spectral synthesis -/

lemma Dual.indicator (hd : Dual a y u) {s : Set ℝ} (hs : MeasurableSet s) :
    Dual a (s.indicator y) u where
  left := (hd.left.indicator hs).ae_eq (Eventually.of_forall fun _ =>
    indicator_mul_right s (fun x : ℝ => (Real.exp (-a * |x|) : ℂ)) y)
  right := hd.right

/-- A correlation decays where the shift moves away from the support. -/
lemma Dual.exists_norm_cross_le (hd : Dual a y u) : ∃ K, 0 ≤ K ∧ ∀ (s : Set ℝ) (τ : ℝ),
    (∀ x ∈ s, |x - τ| = |x| + |τ|) →
      ‖cross (s.indicator y) u τ‖ ≤ K * Real.exp (-a * |τ|) := by
  obtain ⟨hi, hle⟩ := integrable_mul_shift hd.left hd.right 0
  refine ⟨(eLpNorm (fun x => (Real.exp (-a * |x|) : ℂ) * y x) 2).toReal *
    (eLpNorm (fun x => (Real.exp (a * |x|) : ℂ) * u x) 2).toReal, by positivity,
    fun s τ hsτ => ?_⟩
  obtain ⟨hi, hle⟩ := integrable_mul_shift hd.left hd.right τ
  rw [mul_comm]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le)
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hi.norm.const_mul _) (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, cross_integrand a y u, norm_mul, norm_mul (damp a τ x : ℂ), norm_real,
      norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (damp_pos a τ x).le,
      ← mul_assoc, damp, ← Real.exp_add, hsτ x hx]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (norm_nonneg _)
  · rw [indicator_of_notMem hx, zero_mul, norm_zero]
    positivity

/-- In the strip, the Carleman transform of `cross y u` is a multiple of the transform of `u`, up to
an analytic multiple of the transform of `h`. -/
lemma Dual.exists_local_split (hd : Dual a y u) (ha : 0 < a) (hh : Rapid h)
    (h0 : ∀ t, cross y h t = 0) {z : ℂ} (hz : |z.re| < a) : ∃ A : ℂ → ℂ, AnalyticAt ℂ A z ∧
      (fun w => jet (cross (pos (cross y u)) h) 0 (-w)) =ᶠ[𝓝 z]
        fun w => jet (cross (pos y) h) 0 (-w) * jet u 0 w + A w * jet h 0 w := by
  obtain ⟨K, hb⟩ := hd.crossBound ha.le
  have hdp : Dual a (pos y) u := hd.indicator measurableSet_Ioi
  have hbp : CrossBound a (pos y) u K := hb.indicator measurableSet_Ioi
  have hp : Tempered a (pos (cross y u)) := tempered_of_le (K := K)
    ((hd.continuous_cross ha.le).aestronglyMeasurable.indicator measurableSet_Ioi)
    fun τ => (norm_indicator_le_norm_self _ _).trans (hb.norm_le τ)
  have hq : Tempered a (cross (pos y) u) := tempered_of_le
    (hdp.continuous_cross ha.le).aestronglyMeasurable hbp.norm_le
  set D : ℝ → ℂ := fun τ => pos (cross y u) τ - cross (pos y) u τ with hD
  have hDm : AEStronglyMeasurable D := hp.aesm.sub hq.aesm
  obtain ⟨C, hC, hle⟩ := hd.exists_norm_cross_le
  have hDle : ∀ τ, ‖D τ‖ ≤ C * Real.exp (-a * |τ|) := fun τ => by
    rcases lt_or_ge 0 τ with hτ | hτ
    · have e : D τ = cross (neg y) u τ := by
        simp only [hD, pos, indicator_of_mem (mem_Ioi.2 hτ)]
        rw [sub_eq_iff_eq_add', cross, cross, cross, ← integral_add (hbp.integrable τ)
          ((hb.indicator measurableSet_Iic).integrable τ)]
        simp only [← add_mul, pos_add_neg]
      rw [e]
      refine hle _ τ fun x hx => ?_
      rw [abs_of_nonpos (mem_Iic.1 hx), abs_of_pos hτ,
        abs_of_nonpos (by linarith [mem_Iic.1 hx])]
      ring
    · have e : D τ = -cross (pos y) u τ := by
        simp [hD, pos, not_lt.2 hτ]
      rw [e, norm_neg]
      refine hle _ τ fun x hx => ?_
      rw [abs_of_pos (mem_Ioi.1 hx), abs_of_nonpos hτ, abs_of_nonneg (by linarith [mem_Ioi.1 hx])]
      ring
  have hDc : ∀ w : ℂ, |w.re| < a → ConvAt D (-w).re := fun w hw => by
    set c := (a - |w.re|) / 2
    have hc : 0 < c := by simp only [c]; linarith
    refine ⟨c, hc, ((integrable_exp_neg_mul_abs hc).const_mul C).mono'
      ((by fun_prop : Continuous fun x : ℝ =>
        (Real.exp ((-w).re * x + c * |x|) : ℂ)).aestronglyMeasurable.mul hDm)
      (Eventually.of_forall fun x => ?_)⟩
    rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp ((-w).re * x + c * |x|) * Real.exp (-a * |x|) ≤ Real.exp (-c * |x|) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have := re_mul_le (z := -w) (b := |w.re|) (by simp) x
      simp only [c] at *
      nlinarith
    calc _ ≤ Real.exp ((-w).re * x + c * |x|) * (C * Real.exp (-a * |x|)) := by
          gcongr; exact hDle x
      _ = C * (Real.exp ((-w).re * x + c * |x|) * Real.exp (-a * |x|)) := by ring
      _ ≤ _ := by gcongr
  refine ⟨fun w => jet D 0 (-w), (hDc z hz).analyticAt.comp analyticAt_id.neg, ?_⟩
  filter_upwards [(isOpen_lt continuous_re.abs continuous_const).mem_nhds hz] with w hw
  obtain ⟨i1, e1⟩ := jet_cross (hDc w hw).integrable (hh.convAt w.re).integrable
  obtain ⟨i2, e2⟩ := jet_cross ((rapid_cross hd.tempered hh h0).convAt (-w).re).integrable
    (hd.convAt hw).integrable
  rw [← e1, ← e2, jet_zero, jet_zero, jet_zero, ← integral_add i2 i1]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [← add_mul]
  congr 1
  rw [← cross_comm hbp hh, cross, cross, cross, ← integral_add (integrable_cross_integrand hq hh t)
    ((integrable_cross_integrand hp hh t).sub (integrable_cross_integrand hq hh t) |>.congr
      (Eventually.of_forall fun x => (sub_mul _ _ _).symm))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- **Spectral synthesis.** Suppose `h` decays faster than every exponential and its transform `X`
has subgaussian lower bounds along a sequence of heights. If `y` annihilates the translates of `h`,
it annihilates every `u` in the predual whose transform vanishes at the zeros of `X` in the open
strip to their orders. -/
theorem integral_eq_zero_of_order_le (ha : 0 < a) (hh : Rapid h) (hd : Dual a y u)
    (hheights : ∃ b > a, ∀ ε > 0, ∀ R : ℝ, ∃ T ≥ R, ∀ z : ℂ, |z.im| = T → |z.re| ≤ b →
      Real.exp (-ε * T ^ 2) ≤ ‖jet h 0 z‖)
    (h0 : ∀ t, cross y h t = 0)
    (hord : ∀ z : ℂ, |z.re| < a → analyticOrderAt (jet h 0) z ≤ analyticOrderAt (jet u 0) z) :
    ∫ x, y x * u x = 0 := by
  set X := jet h 0
  set p := cross y u
  obtain ⟨K, hb⟩ := hd.crossBound ha.le
  have hp : Little a p K := ⟨hd.continuous_cross ha.le, hb.norm_le, hd.tendsto_cross ha.le⟩
  have hp0 : ∀ t, cross p h t = 0 := fun t => by
    rw [cross_comm hb hh, cross]
    simp only [h0, zero_mul, integral_zero]
  have hXd : Differentiable ℂ X := fun z => ((hh.convAt z.re).hasDerivAt 0).2.differentiableAt
  have hGp := rapid_cross hp.tempered hh hp0
  have hGy := rapid_cross hd.tempered hh h0
  set G : ℂ → ℂ := fun z => jet (cross (pos p) h) 0 (-z)
  have hGd : Differentiable ℂ G := fun z =>
    ((hGp.convAt (-z).re).hasDerivAt 0).2.differentiableAt.comp z differentiableAt_id.neg
  have hright : ∀ z : ℂ, a < z.re → G z = jet (pos p) 0 (-z) * X z := fun z hz =>
    jet_cross_pos hp.tempered hh hz
  have hleft : ∀ z : ℂ, z.re < -a → G z = -jet (neg p) 0 (-z) * X z := fun z hz =>
    jet_cross_neg hp.tempered hh hp0 hz
  -- orders
  have hne : ∀ z, analyticOrderAt X z ≠ ⊤ := fun z htop => by
    have hX0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      fun w => hXd.analyticAt w).1 htop
    obtain ⟨b, hab, H⟩ := hheights
    obtain ⟨T, hT, HT⟩ := H 1 one_pos 0
    have h1 := HT (T * I) (by simpa using hT) (by simp; linarith)
    rw [hX0, Pi.zero_apply, norm_zero] at h1
    exact absurd h1 (not_le.2 (Real.exp_pos _))
  have hmul : ∀ {z : ℂ} {Q : ℂ → ℂ}, AnalyticAt ℂ Q z → (G =ᶠ[𝓝 z] fun w => Q w * X w) →
      analyticOrderAt X z ≤ analyticOrderAt G z := fun {z Q} hQ hev => by
    rw [analyticOrderAt_congr hev]
    change _ ≤ analyticOrderAt (Q * X) z
    rw [analyticOrderAt_mul hQ (hXd.analyticAt z)]
    exact le_add_self
  have hstrip : ∀ z : ℂ, |z.re| < a → ∃ A : ℂ → ℂ, AnalyticAt ℂ A z ∧
      G =ᶠ[𝓝 z] fun w => jet (cross (pos y) h) 0 (-w) * jet u 0 w + A w * X w :=
    fun z hz => hd.exists_local_split ha hh h0 hz
  have horder : ∀ z, analyticOrderAt X z ≤ analyticOrderAt G z := by
    intro z
    rcases lt_trichotomy |z.re| a with hz | hz | hz
    · obtain ⟨A, hA, hev⟩ := hstrip z hz
      have hU : AnalyticAt ℂ (jet u 0) z := (hd.convAt hz).analyticAt
      have hg : AnalyticAt ℂ (fun w => jet (cross (pos y) h) 0 (-w)) z :=
        (hGy.convAt (-z).re).analyticAt.comp analyticAt_id.neg
      rw [analyticOrderAt_congr hev]
      refine le_trans (le_min ?_ ?_) le_analyticOrderAt_add
      · change _ ≤ analyticOrderAt ((fun w => jet (cross (pos y) h) 0 (-w)) * jet u 0) z
        rw [analyticOrderAt_mul hg hU]
        exact (hord z hz).trans le_add_self
      · change _ ≤ analyticOrderAt (A * X) z
        rw [analyticOrderAt_mul hA (hXd.analyticAt z)]
        exact le_add_self
    · rcases abs_choice z.re with h1 | h1
      · refine order_le_of_tendsto (d := 1) one_ne_zero (Q := fun η => jet (pos p) 0 (-(z + η)))
          (hXd.analyticAt z) (hGd.analyticAt z) (hne z) (fun η hη => ?_)
          (hp.tendsto_jet (h1 ▸ hz))
        rw [mul_one]
        exact hright _ (by simp; linarith)
      · refine order_le_of_tendsto (d := -1) (by simp)
          (Q := fun η => -jet (pos fun x => p (-x)) 0 (-(-z + η)))
          (hXd.analyticAt z) (hGd.analyticAt z) (hne z) (fun η hη => ?_) ?_
        · rw [hleft _ (by simp; linarith), jet_neg]
          ring_nf
        · simpa using hp.reflect.tendsto_jet (z := -z) (by rw [neg_re]; linarith)
    · rcases lt_abs.1 hz with h1 | h1
      · refine hmul (Q := fun w => jet (pos p) 0 (-w))
          ((hp.tempered.convAt_pos h1).analyticAt.comp analyticAt_id.neg) ?_
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds h1] with w hw
        exact hright w hw
      · have h2 : z.re < -a := by linarith
        refine hmul (Q := fun w => -jet (neg p) 0 (-w))
          ((hp.tempered.convAt_neg h2).analyticAt.comp analyticAt_id.neg).neg ?_
        filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds h2] with w hw
        exact hleft w hw
  -- the quotient is entire and bounded
  obtain ⟨F, hF, hFG⟩ := exists_entire_quotient hXd hGd hne horder
  have hcancel : ∀ {z : ℂ} {Q : ℂ → ℂ}, AnalyticAt ℂ Q z → (G =ᶠ[𝓝 z] fun w => Q w * X w) →
      F z = Q z := fun {z Q} hQ hev => by
    have h1 : ∀ᶠ w in 𝓝[≠] z, X w ≠ 0 :=
      ((hXd.analyticAt z).eventually_eq_zero_or_eventually_ne_zero).resolve_left
        fun h => hne z (analyticOrderAt_eq_top.2 h)
    refine tendsto_nhds_unique (l := 𝓝[≠] z) (f := F) (hF.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hQ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_)
    filter_upwards [h1, nhdsWithin_le_nhds hev] with w hw hw'
    rw [hFG, mul_comm] at hw'
    exact (mul_right_cancel₀ hw hw').symm
  have hFr : ∀ z : ℂ, a < z.re → F z = jet (pos p) 0 (-z) := fun z hz => by
    refine hcancel (Q := fun w => jet (pos p) 0 (-w))
      ((hp.tempered.convAt_pos hz).analyticAt.comp analyticAt_id.neg) ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with w hw
    exact hright w hw
  have hFl : ∀ z : ℂ, z.re < -a → F z = -jet (pos fun x => p (-x)) 0 (-(-z)) := fun z hz => by
    rw [← jet_neg]
    refine hcancel (Q := fun w => -jet (neg p) 0 (-w))
      ((hp.tempered.convAt_neg hz).analyticAt.comp analyticAt_id.neg).neg ?_
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hz] with w hw
    exact hleft w hw
  obtain ⟨b, hab, H⟩ := hheights
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hp.le 0)
  have hout : ∀ z : ℂ, b ≤ |z.re| → ‖F z‖ ≤ K / (b - a) := fun z hz => by
    have hba : 0 < b - a := by linarith
    rcases le_abs.1 hz with h1 | h1
    · rw [hFr z (by linarith)]
      exact (hp.norm_jet_le_div (by linarith)).trans (by gcongr)
    · rw [hFl z (by linarith), norm_neg]
      refine (hp.reflect.norm_jet_le_div (by rw [neg_re]; linarith)).trans ?_
      rw [neg_re]
      gcongr
  obtain ⟨B, hB⟩ := hGp.exists_norm_jet_le b
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp; linarith))
  set M := max B (K / (b - a))
  have hbound : ∀ z, ‖F z‖ ≤ M := fun z => by
    rcases le_total |z.re| b with hz | hz
    · refine norm_le_of_heights hF (le_max_of_le_left hB0)
        (fun w hw => (hout w hw.ge).trans (le_max_right _ _)) (fun ε hε R => ?_) hz
      obtain ⟨T, hT, HT⟩ := H ε hε R
      refine ⟨T, hT, fun w hw hwb => ?_⟩
      have h1 := HT w hw hwb
      have h2 : ‖X w‖ * ‖F w‖ ≤ M := by
        rw [← norm_mul, ← hFG]
        exact (hB (-w) (by simpa using hwb)).trans (le_max_left _ _)
      have h3 : Real.exp (-ε * T ^ 2) * ‖F w‖ ≤ M :=
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans h2
      rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at h3
      linarith
    · exact (hout z hz).trans (le_max_right _ _)
  -- hence zero
  have hF0 : ∀ z, F z = 0 := fun z => by
    have h1 : ∀ x : ℝ, a < x → ‖F z‖ ≤ K / (x - a) := fun x hx => by
      rw [hF.apply_eq_apply_of_bounded (Metric.isBounded_iff_subset_closedBall 0 |>.2
        ⟨M, by rintro _ ⟨w, rfl⟩; simpa using hbound w⟩) z x, hFr x (by simpa using hx)]
      exact hp.norm_jet_le_div (by simpa using hx)
    have h2 : Tendsto (fun x : ℝ => K / (x - a)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
    exact norm_le_zero_iff.1 (ge_of_tendsto h2 ((eventually_gt_atTop a).mono h1))
  have hpz : ∀ τ : ℝ, 0 < τ → p τ = 0 := fun τ hτ =>
    hp.eq_zero (fun z hz => by rw [← hFr z hz, hF0]) hτ
  have h3 : p 0 = 0 := by
    refine tendsto_nhds_unique (hp.continuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))) (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with τ hτ using (hpz τ hτ).symm
  simpa [p, cross] using h3

/-! ### The seed -/

/-- A polynomial times the Gaussian `e^{-πx²}`. -/
noncomputable def polyGauss (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  P.eval (x : ℂ) * exp (-Real.pi * (x : ℂ) ^ 2)

lemma hasDerivAt_polyGauss (P : Polynomial ℂ) (x : ℝ) : HasDerivAt (polyGauss P)
    (polyGauss (P.derivative - Polynomial.C (2 * Real.pi : ℂ) * Polynomial.X * P) x) x := by
  have h1 : HasDerivAt (fun z : ℂ => P.eval z * exp (-Real.pi * z ^ 2)) _ (x : ℂ) :=
    (P.hasDerivAt _).mul ((((hasDerivAt_id (x : ℂ)).pow 2).const_mul (-Real.pi : ℂ)).cexp)
  refine h1.comp_ofReal.congr_deriv ?_
  simp [polyGauss]
  ring

lemma exists_iteratedDeriv_polyGauss (n : ℕ) (P : Polynomial ℂ) :
    ∃ Q, iteratedDeriv n (polyGauss P) = polyGauss Q := by
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih
    rw [iteratedDeriv_succ, hQ]
    exact ⟨_, funext fun x => (hasDerivAt_polyGauss Q x).deriv⟩

lemma contDiff_polyGauss (P : Polynomial ℂ) : ContDiff ℝ (⊤ : ℕ∞) (polyGauss P) :=
  contDiff_of_differentiable_iteratedDeriv fun m _ => by
    obtain ⟨Q, hQ⟩ := exists_iteratedDeriv_polyGauss m P
    rw [hQ]
    exact fun x => (hasDerivAt_polyGauss Q x).differentiableAt

lemma polyGauss_decay (k : ℕ) (P : Polynomial ℂ) : ∃ C, ∀ x : ℝ, |x| ^ k * ‖polyGauss P x‖ ≤ C := by
  have hg : ∀ x : ℝ, ‖exp (-Real.pi * (x : ℂ) ^ 2)‖ ≤
      Real.exp Real.pi * Real.exp (-Real.pi * |x|) := fun x => by
    rw [norm_exp, ← Real.exp_add, Real.exp_le_exp,
      show (-(Real.pi : ℂ) * (x : ℂ) ^ 2).re = -Real.pi * |x| ^ 2 by
        rw [sq_abs, ← ofReal_neg, ← ofReal_pow, ← ofReal_mul, ofReal_re]]
    nlinarith [Real.pi_pos, sq_nonneg (|x| - 1), abs_nonneg x]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨C, hC⟩ := hP
    obtain ⟨D, hD⟩ := hQ
    refine ⟨C + D, fun x => ?_⟩
    have e : polyGauss (P + Q) x = polyGauss P x + polyGauss Q x := by
      simp [polyGauss, add_mul]
    rw [e]
    calc _ ≤ |x| ^ k * (‖polyGauss P x‖ + ‖polyGauss Q x‖) := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hC x) (hD x)
  | monomial n c =>
    obtain ⟨C, hC⟩ := pow_mul_exp_le (k + n) Real.pi_pos
    refine ⟨‖c‖ * Real.exp Real.pi * C, fun x => ?_⟩
    rw [polyGauss, Polynomial.eval_monomial, norm_mul, norm_mul, norm_pow, norm_real,
      Real.norm_eq_abs]
    calc _ ≤ |x| ^ k * (‖c‖ * |x| ^ n * (Real.exp Real.pi * Real.exp (-Real.pi * |x|))) := by
          gcongr; exact hg x
      _ = ‖c‖ * Real.exp Real.pi * (|x| ^ (k + n) * Real.exp (-Real.pi * |x|)) := by
          rw [pow_add]; ring
      _ ≤ _ := by gcongr; exact hC x

open Polynomial in
/-- The seed `(4π²x⁴ - 6πx²) e^{-πx²}`. -/
noncomputable def seed : 𝓢(ℝ, ℂ) where
  toFun := polyGauss (C (4 * Real.pi ^ 2 : ℂ) * X ^ 4 - C (6 * Real.pi : ℂ) * X ^ 2)
  smooth' := contDiff_polyGauss _
  decay' k n := by
    obtain ⟨Q, hQ⟩ := exists_iteratedDeriv_polyGauss n
      (C (4 * Real.pi ^ 2 : ℂ) * X ^ 4 - C (6 * Real.pi : ℂ) * X ^ 2)
    obtain ⟨D, hD⟩ := polyGauss_decay k Q
    refine ⟨D, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hQ, Real.norm_eq_abs]
    exact hD x

lemma seed_apply (x : ℝ) : seed x =
    (4 * Real.pi ^ 2 * (x : ℂ) ^ 4 - 6 * Real.pi * (x : ℂ) ^ 2) * exp (-Real.pi * (x : ℂ) ^ 2) := by
  change polyGauss _ x = _
  simp [polyGauss]

/-- The archimedean factor `π^{-s/2} Γ(s/2 + 1)`. -/
noncomputable def arch (s : ℂ) : ℂ := (1 / (Real.pi : ℂ)) ^ (s / 2) * Gamma (s / 2 + 1)

lemma one_div_pi_ne : (1 / (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]

lemma mellin_seed {s : ℂ} (hs : 0 < s.re) : mellin seed s = (s - 1) * arch s := by
  set g : ℝ → ℂ := fun u => (4 * Real.pi ^ 2 * (u : ℂ) ^ 2 - 6 * Real.pi * u) * exp (-(Real.pi * u))
  have e1 : mellin seed s = mellin (fun t : ℝ => g (t ^ (2 : ℝ))) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [g, seed_apply, Real.rpow_two]
    push_cast
    ring_nf
  have hw : 0 < (s / 2).re := by
    rw [show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring, re_ofReal_mul]; linarith
  have key : ∀ k : ℂ, 0 < k.re → IntegrableOn (fun t : ℝ => (t : ℂ) ^ (k - 1) *
      exp (-(Real.pi * t))) (Ioi 0) := fun k hk => by
    by_contra h
    have h1 := Complex.integral_cpow_mul_exp_neg_mul_Ioi hk Real.pi_pos
    rw [integral_undef h] at h1
    exact mul_ne_zero ((cpow_ne_zero_iff_of_exponent_ne_zero (by rintro rfl; simp at hk)).2
      one_div_pi_ne) (Gamma_ne_zero_of_re_pos hk) h1.symm
  have h2 : 0 < (s / 2 + 2).re := by rw [add_re]; norm_num; linarith
  have h3 : 0 < (s / 2 + 1).re := by rw [add_re]; norm_num; linarith
  have e2 : mellin g (s / 2) = 4 * Real.pi ^ 2 * ((1 / Real.pi) ^ (s / 2 + 2) * Gamma (s / 2 + 2)) -
      6 * Real.pi * ((1 / Real.pi) ^ (s / 2 + 1) * Gamma (s / 2 + 1)) := by
    rw [← Complex.integral_cpow_mul_exp_neg_mul_Ioi h2 Real.pi_pos,
      ← Complex.integral_cpow_mul_exp_neg_mul_Ioi h3 Real.pi_pos, ← integral_const_mul,
      ← integral_const_mul, ← integral_sub ((key _ h2).const_mul _) ((key _ h3).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt ht)
    simp only [g, smul_eq_mul]
    rw [show s / 2 + 2 - 1 = (s / 2 - 1) + (2 : ℕ) by push_cast; ring,
      show s / 2 + 1 - 1 = (s / 2 - 1) + (1 : ℕ) by push_cast; ring, cpow_add _ _ ht0,
      cpow_add _ _ ht0, cpow_natCast, cpow_natCast]
    ring
  have e3 : Gamma (s / 2 + 2) = (s / 2 + 1) * Gamma (s / 2 + 1) := by
    rw [show s / 2 + 2 = (s / 2 + 1) + 1 by ring, Gamma_add_one]
    intro h
    rw [h] at h3
    simp at h3
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [e1, mellin_comp_rpow, ofReal_ofNat, e2, e3, arch,
    show s / 2 + 2 = s / 2 + (2 : ℕ) by push_cast; ring, cpow_add _ _ one_div_pi_ne,
    cpow_add _ _ one_div_pi_ne, cpow_natCast, cpow_one, real_smul]
  push_cast
  rw [abs_of_pos two_pos]
  push_cast
  field_simp
  ring

lemma thetaClass_seed : ThetaClass seed where
  even x := by
    simp only [seed_apply, ofReal_neg, neg_sq, show (-(x : ℂ)) ^ 4 = (x : ℂ) ^ 4 by ring]
  zero := by simp [seed_apply]
  integral := by
    have h1 : mellin seed 1 = ∫ x in Ioi (0 : ℝ), seed x := by simp [mellin]
    have h2 : ∫ x in Iic (0 : ℝ), seed x = ∫ x in Ioi (0 : ℝ), seed x := by
      have := integral_comp_neg_Iic (0 : ℝ) fun x => seed x
      rw [neg_zero] at this
      rw [← this]
      simp only [seed_apply, ofReal_neg, neg_sq, (by intro x; ring : ∀ x : ℂ, (-x) ^ 4 = x ^ 4)]
    rw [← intervalIntegral.integral_Iic_add_Ioi seed.integrable.integrableOn
      seed.integrable.integrableOn, h2, ← h1, mellin_seed (by simp)]
    simp

lemma arch_ne_zero {s : ℂ} (hs : 0 < s.re) : arch s ≠ 0 := by
  refine mul_ne_zero (by simp [cpow_eq_zero_iff, Real.pi_ne_zero]) (Gamma_ne_zero_of_re_pos ?_)
  rw [show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring, add_re, re_ofReal_mul, one_re]
  linarith

lemma arch_eq {s : ℂ} (hs : s ≠ 0) : arch s = s / 2 * Gammaℝ s := by
  rw [arch, Gamma_add_one _ (div_ne_zero hs two_ne_zero), Gammaℝ_def, one_div, inv_cpow,
    ← cpow_neg, neg_div]
  · ring
  · rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne

/-- The transform of the theta function of the seed. -/
noncomputable abbrev xi : ℂ → ℂ := jet (theta seed) 0

lemma xi_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : xi (s - 1 / 2) = zetaNum s * arch s := by
  have h := sub_one_mul_jet thetaClass_seed hs
  rw [mellin_seed hs, mul_left_comm] at h
  exact mul_left_cancel₀ (sub_ne_zero.2 hs1) h

lemma xi_eq_completed {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xi (s - 1 / 2) = s * (s - 1) / 2 * completedRiemannZeta s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [xi_eq hs hs1, zetaNum_of_ne hs1, arch_eq h0, riemannZeta_def_of_ne_zero h0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

lemma xi_neg (z : ℂ) : xi (-z) = xi z := by
  have hd := differentiable_jet thetaClass_seed 0
  have h := AnalyticOnNhd.eq_of_eventuallyEq (f := fun z => xi (-z)) (g := xi) (z₀ := 0)
    (fun w _ => (hd.comp differentiable_neg).analyticAt w) (fun w _ => hd.analyticAt w) ?_
  · exact congrFun h z
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / 2 by norm_num)] with w hw
    have h1 := (abs_re_le_norm w).trans_lt (mem_ball_zero_iff.1 hw)
    rw [abs_lt] at h1
    have hne : ∀ s : ℂ, s.re < 1 → s ≠ 1 := by rintro s hs rfl; simp at hs
    have e1 := xi_eq_completed (s := 1 / 2 + w) (by norm_num; linarith)
      (hne _ (by norm_num; linarith))
    have e2 := xi_eq_completed (s := 1 - (1 / 2 + w)) (by norm_num; linarith)
      (hne _ (by norm_num; linarith))
    rw [completedRiemannZeta_one_sub] at e2
    rw [show -w = 1 - (1 / 2 + w) - 1 / 2 by ring, e2]
    rw [add_sub_cancel_left] at e1
    rw [e1]
    ring

/-- The transform of the theta function of the seed is the Riemann `ξ` function. -/
theorem xi_eq_riemann {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi (s - 1 / 2) = s * (s - 1) / 2 * completedRiemannZeta s := by
  rcases lt_or_ge 0 s.re with hs | hs
  · exact xi_eq_completed hs hs1
  · have h := xi_eq_completed (s := 1 - s) (by simp; linarith) (fun h => hs0 (by linear_combination -h))
    rw [completedRiemannZeta_one_sub] at h
    rw [← xi_neg, show -(s - 1 / 2) = 1 - s - 1 / 2 by ring, h]
    ring

/-- In the half-plane `Re s > 0`, the order of `ξ` is the multiplicity of the zeta zero. -/
lemma analyticOrderAt_xi {s : ℂ} (hs : 0 < s.re) : analyticOrderAt xi (s - 1 / 2) = zeroMult s := by
  have h := analyticOrderAt_jet thetaClass_seed hs
  have hA : AnalyticAt ℂ arch s := by
    refine DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re}) (fun w hw => ?_)
      ((isOpen_lt continuous_const continuous_re).mem_nhds hs)
    have h1 : DifferentiableAt ℂ Gamma (w / 2 + 1) := by
      refine differentiableAt_Gamma _ fun m hm => ?_
      have := congrArg re hm
      rw [show w / 2 = ((1 / 2 : ℝ) : ℂ) * w by push_cast; ring, add_re, re_ofReal_mul, one_re] at this
      simp at this
      have hw' : 0 < w.re := hw
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (1 / (Real.pi : ℂ)) ^ (w / 2)) w :=
      (differentiableAt_id.div_const 2).const_cpow (.inl one_div_pi_ne)
    exact (h2.mul (h1.comp w (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w / 2 + 1) w)))
      |>.differentiableWithinAt
  have hM : analyticOrderAt (mellin seed) s = analyticOrderAt (fun w : ℂ => w - 1) s := by
    rw [analyticOrderAt_congr (g := (fun w : ℂ => w - 1) * arch), analyticOrderAt_mul (by fun_prop) hA,
      hA.analyticOrderAt_eq_zero.2 (arch_ne_zero hs), add_zero]
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with w hw
    exact mellin_seed hw
  rw [hM, analyticOrderAt_zetaNum, add_comm] at h
  exact WithTop.add_right_cancel (analyticOrderAt_sub_one_ne_top s) h

/-- The order of `ξ` at `z` is the multiplicity of the zero `1/2 + z`, if it lies in the strip. -/
lemma lt_analyticOrderAt_xi {z : ℂ} {m : ℕ} (hm : m < analyticOrderAt xi z) :
    m < zeroMult (1 / 2 + z) ∧ 1 / 2 + z ∈ stripZeros := by
  have key : ∀ s : ℂ, 0 < s.re → (m : ℕ∞) < analyticOrderAt xi (s - 1 / 2) →
      m < zeroMult s ∧ riemannZeta s = 0 ∧ s.re < 1 := fun s hs h => by
    rw [analyticOrderAt_xi hs] at h
    have h1 : m < zeroMult s := by exact_mod_cast h
    have hz : riemannZeta s = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_zero_of_lt h1)
    exact ⟨h1, hz, not_le.1 fun h => riemannZeta_ne_zero_of_one_le_re h hz⟩
  have hre : (1 / 2 + z).re = 1 / 2 + z.re := by norm_num
  rcases lt_or_ge (-1 / 2) z.re with hz | hz
  · have h0 : 0 < (1 / 2 + z).re := by rw [hre]; linarith
    obtain ⟨h1, h2, h3⟩ := key (1 / 2 + z) h0 (by rwa [add_sub_cancel_left])
    exact ⟨h1, h2, h0, h3⟩
  · have e : analyticOrderAt xi z = analyticOrderAt xi (-z) := by
      have h := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun w : ℂ => -w) (z₀ := z)
        (by fun_prop) (by simp)
      rw [← h]
      exact analyticOrderAt_congr (Eventually.of_forall fun w => (xi_neg w).symm)
    obtain ⟨-, -, h3⟩ := key (1 / 2 - z) (by norm_num; linarith)
      (by rw [show 1 / 2 - z - 1 / 2 = -z by ring, ← e]; exact hm)
    norm_num at h3
    linarith

/-! ### Heights -/

lemma norm_Gamma_le {z : ℂ} (hz : 0 < z.re) : ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, Real.Gamma_eq_integral hz, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq
    (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

/-- An elementary lower bound for the Gamma function. -/
lemma exists_le_norm_Gamma : ∃ c > 0, ∀ w : ℂ, 1 ≤ |w.im| → -1 / 2 ≤ w.re →
    c * Real.exp (-Real.pi * |w.im|) ≤ ‖Gamma w‖ := by
  have hc : ContinuousOn Real.Gamma (Icc (1 / 2) (3 / 2)) := fun x hx =>
    (Real.differentiableAt_Gamma fun m => by
      have h1 : (0 : ℝ) < x := by linarith [hx.1]
      have h2 := Nat.cast_nonneg (α := ℝ) m
      linarith).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hc).bddAbove
  have hB' : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), Real.Gamma x ≤ B := fun x hx => hB ⟨x, hx, rfl⟩
  have hBpos : 0 < B := (Real.Gamma_pos_of_pos one_pos).trans_le (hB' 1 (by norm_num))
  refine ⟨1 / B, by positivity, ?_⟩
  have key : ∀ n : ℕ, ∀ w : ℂ, 1 ≤ |w.im| → -1 / 2 ≤ w.re → w.re ≤ 1 / 2 + n →
      1 / B * Real.exp (-Real.pi * |w.im|) ≤ ‖Gamma w‖ := by
    intro n
    induction n with
    | zero =>
      intro w h1 h2 h3
      have him : w.im ≠ 0 := fun h => by rw [h] at h1; norm_num at h1
      have hsub : (1 - w).re = 1 - w.re := by simp
      have hne : ∀ v : ℂ, v.im ≠ 0 → Gamma v ≠ 0 := fun v hv => Gamma_ne_zero fun m hm => by
        rw [hm] at hv; simp at hv
      have hprod := Gamma_mul_Gamma_one_sub w
      have hs : sin (Real.pi * w) ≠ 0 := fun h => by
        rw [h, div_zero] at hprod
        exact mul_ne_zero (hne w him) (hne (1 - w) (by simpa using him)) hprod
      have hsin : ‖sin (Real.pi * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
        have h4 : ∀ v : ℂ, ‖exp (v * I)‖ ≤ Real.exp |v.im| := fun v => by
          rw [norm_exp, Real.exp_le_exp]
          simpa using neg_le_abs v.im
        have h5 : |((Real.pi : ℂ) * w).im| = Real.pi * |w.im| := by
          rw [im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos]
        rw [sin, norm_div, norm_mul, norm_I, mul_one, norm_ofNat, div_le_iff₀ two_pos, ← h5]
        refine (norm_sub_le _ _).trans ?_
        have h6 := h4 (-(Real.pi * w))
        rw [neg_im, abs_neg] at h6
        linarith [h4 (Real.pi * w)]
      have hG : ‖Gamma (1 - w)‖ ≤ B := by
        refine (norm_Gamma_le (by rw [hsub]; norm_num at h3; linarith)).trans
          (hB' _ ?_)
        rw [hsub]
        norm_num at h3
        constructor <;> linarith
      have h7 : Real.pi ≤ ‖Gamma w‖ * B * Real.exp (Real.pi * |w.im|) := by
        have h8 := congrArg norm hprod
        rw [norm_mul, norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le,
          eq_div_iff (norm_ne_zero_iff.2 hs)] at h8
        calc _ = _ := h8.symm
          _ ≤ _ := by gcongr
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity), ← mul_assoc]
      linarith [Real.pi_gt_three]
    | succ n ih =>
      intro w h1 h2 h3
      rcases le_total w.re (1 / 2 + n) with h | h
      · exact ih w h1 h2 h
      · have hw : w - 1 ≠ 0 := fun hw => by
          have := congrArg im hw
          simp at this
          rw [this] at h1
          norm_num at h1
        have h4 := ih (w - 1) (by simpa using h1)
          (by simp; linarith [Nat.cast_nonneg (α := ℝ) n]) (by push_cast at h3; simp; linarith)
        have h5 : Gamma w = (w - 1) * Gamma (w - 1) := by
          rw [← Gamma_add_one _ hw, sub_add_cancel]
        rw [sub_im, one_im, sub_zero] at h4
        rw [h5, norm_mul]
        have h6 : 1 ≤ ‖w - 1‖ := h1.trans (by simpa using abs_im_le_norm (w - 1))
        exact h4.trans (le_mul_of_one_le_left (norm_nonneg _) h6)
  intro w h1 h2
  obtain ⟨n, hn⟩ := exists_nat_ge w.re
  exact key n w h1 h2 (by linarith)

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith : 0 < x))
  rw [Real.log_sqrt (by linarith)] at h1
  have h2 := Real.log_nonneg hx
  have h3 := Real.sq_sqrt (by linarith : 0 ≤ x)
  have h4 := Real.sqrt_nonneg x
  nlinarith

/-- A lower bound for zeta along a sequence of heights, from a bound for `ζ'/ζ`. -/
lemma exists_le_norm_zeta : ∃ C > 0, ∀ j : ℕ, 7 ≤ j → ∃ T : ℝ, j ≤ T ∧ T ≤ j + 1 ∧
    ∀ s : ℂ, |s.im| = T → 1 / 2 ≤ s.re → Real.exp (-C * (T + 3)) / 3 ≤ ‖riemannZeta s‖ := by
  obtain ⟨C, hC, H⟩ := Zeta23.WeilEF.good_heights_at
  refine ⟨8 * C, by positivity, fun j hj => ?_⟩
  obtain ⟨T, hjT, hT, HT⟩ := H j hj
  have hj7 : (7 : ℝ) ≤ j := by exact_mod_cast hj
  refine ⟨T, hjT, hT, fun s him hs => ?_⟩
  have him' : s.im = T ∨ s.im = -T := by
    rcases abs_choice s.im with h | h
    · exact .inl (h ▸ him)
    · exact .inr (by linarith)
  have hfar : ∀ w : ℂ, 2 ≤ w.re → 1 / 3 ≤ ‖riemannZeta w‖ := fun w hw => by
    exact Zeta23.RvM.one_third_lt_two_sub_pi_sq_div_six.le.trans
      (Zeta23.RvM.norm_riemannZeta_ge_of_two_le_re hw)
  have hexp : Real.exp (-(8 * C) * (T + 3)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  rcases le_total 2 s.re with h2 | h2
  · linarith [hfar s h2]
  set K := C * Real.log ((j : ℝ) + 3) ^ 2
  set path : ℝ → ℂ := fun x => ((s.re + x : ℝ) : ℂ) + s.im * I
  have hpre : ∀ x, (path x).re = s.re + x := fun x => by simp [path]
  have hpim : ∀ x, (path x).im = s.im := fun x => by simp [path]
  have hder : ∀ x, HasDerivAt (fun x => riemannZeta (path x)) (deriv riemannZeta (path x)) x :=
    fun x => by
      have hne : path x ≠ 1 := fun h => by
        have := congrArg im h
        rw [hpim, one_im] at this
        rw [this, abs_zero] at him
        linarith
      have h1 : HasDerivAt path 1 x := by
        have := (((hasDerivAt_id x).const_add s.re).ofReal_comp).add_const ((s.im : ℂ) * I)
        exact this.congr_deriv ofReal_one
      exact ((differentiableAt_riemannZeta hne).hasDerivAt.comp x h1).congr_deriv (mul_one _)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖riemannZeta s‖) (K := K) (ε := 0)
    (a := 0) (b := 2 - s.re) (f := fun x => riemannZeta (path x))
    (fun x _ => (hder x).continuousAt.continuousWithinAt)
    (fun x _ => (hder x).hasDerivWithinAt) (by simp [path, re_add_im]) (fun x hx => by
      have hz := HT (path x) (by rwa [hpim]) (by rw [hpre]; linarith [hx.1])
        (by rw [hpre]; linarith [hx.2])
      have h1 := hz.2
      rw [logDeriv_apply, norm_div, div_le_iff₀ (norm_pos_iff.2 hz.1)] at h1
      rwa [add_zero]) (2 - s.re) ⟨by linarith, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hg
  have h3 := hfar (path (2 - s.re)) (by rw [hpre]; linarith)
  have hK : K * (2 - s.re) ≤ 8 * C * (T + 3) := by
    have h4 := log_sq_le (by linarith : 1 ≤ (j : ℝ) + 3)
    have h5 : K ≤ C * (4 * (T + 3)) := by
      refine mul_le_mul_of_nonneg_left (h4.trans ?_) hC.le
      linarith
    have h6 : 0 ≤ K := by positivity
    nlinarith
  have h7 : 1 / 3 ≤ ‖riemannZeta s‖ * Real.exp (8 * C * (T + 3)) :=
    (h3.trans hg).trans (by gcongr)
  rw [neg_mul, Real.exp_neg, ← one_div, div_div, div_le_iff₀ (by positivity)]
  linarith

lemma exists_heights_xi (b : ℝ) : ∀ ε > 0, ∀ R : ℝ, ∃ T ≥ R, ∀ z : ℂ, |z.im| = T → |z.re| ≤ b →
    Real.exp (-ε * T ^ 2) ≤ ‖xi z‖ := by
  intro ε hε R
  obtain ⟨c, hc, hG⟩ := exists_le_norm_Gamma
  obtain ⟨C, hC, hZ⟩ := exists_le_norm_zeta
  set c' := Real.exp (-Real.log Real.pi * (b + 1)) * c / 3
  have hc' : 0 < c' := by positivity
  set K := 4 * C + Real.pi
  obtain ⟨j, hj⟩ := exists_nat_ge (max R (max 7 ((|Real.log c'| + K) / ε)))
  have hj1 := (le_max_left _ _).trans hj
  have hj2 := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hj3 := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  obtain ⟨T, hjT, -, HT⟩ := hZ j (by exact_mod_cast hj2)
  have hT7 : 7 ≤ T := hj2.trans hjT
  have key : ∀ z : ℂ, |z.im| = T → 0 ≤ z.re → z.re ≤ b → Real.exp (-ε * T ^ 2) ≤ ‖xi z‖ := by
    intro z him h0 hb
    have hre : (1 / 2 + z).re = 1 / 2 + z.re := by norm_num
    have him' : (1 / 2 + z).im = z.im := by norm_num
    have hhalf : (1 / 2 + z) / 2 = ((1 / 2 : ℝ) : ℂ) * (1 / 2 + z) := by push_cast; ring
    have hne : 1 / 2 + z ≠ 1 := fun h => by
      rw [h, one_im] at him'
      rw [← him', abs_zero] at him
      linarith
    have e := xi_eq (s := 1 / 2 + z) (by rw [hre]; linarith) hne
    rw [add_sub_cancel_left, zetaNum_of_ne hne, arch] at e
    have h1 : 1 ≤ ‖1 / 2 + z - 1‖ := by
      refine le_trans ?_ (abs_im_le_norm _)
      rw [sub_im, him', one_im, sub_zero, him]
      linarith
    have h2 : Real.exp (-C * (T + 3)) / 3 ≤ ‖riemannZeta (1 / 2 + z)‖ :=
      HT _ (by rw [him', him]) (by rw [hre]; linarith)
    have h3 : Real.exp (-Real.log Real.pi * (b + 1)) ≤
        ‖(1 / (Real.pi : ℂ)) ^ ((1 / 2 + z) / 2)‖ := by
      rw [show (1 / (Real.pi : ℂ)) = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; ring,
        norm_cpow_eq_rpow_re_of_pos (by positivity), hhalf, re_ofReal_mul, hre,
        Real.rpow_def_of_pos (by positivity), Real.log_inv, Real.exp_le_exp]
      have := Real.log_nonneg (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
      nlinarith
    have hi : ((1 / 2 + z) / 2 + 1).im = z.im / 2 := by
      rw [hhalf, add_im, im_ofReal_mul, him', one_im]; ring
    have h4 := hG ((1 / 2 + z) / 2 + 1) (by rw [hi, abs_div, him, abs_two]; linarith)
      (by rw [hhalf, add_re, re_ofReal_mul, hre, one_re]; linarith)
    rw [hi, abs_div, him, abs_two] at h4
    have h5 : c' * Real.exp (-K * T) ≤ ‖xi z‖ := by
      rw [e, norm_mul, norm_mul, norm_mul]
      calc c' * Real.exp (-K * T) ≤ 1 * (Real.exp (-C * (T + 3)) / 3) *
            (Real.exp (-Real.log Real.pi * (b + 1)) * (c * Real.exp (-Real.pi * (T / 2)))) := by
            have h6 : Real.exp (-K * T) ≤ Real.exp (-C * (T + 3)) * Real.exp (-Real.pi * (T / 2)) := by
              rw [← Real.exp_add, Real.exp_le_exp]
              simp only [K]
              nlinarith [Real.pi_pos]
            calc _ ≤ c' * (Real.exp (-C * (T + 3)) * Real.exp (-Real.pi * (T / 2))) := by gcongr
              _ = _ := by simp only [c']; ring
        _ ≤ _ := by gcongr
    refine le_trans ?_ h5
    rw [← Real.exp_log hc', ← Real.exp_add, Real.exp_le_exp]
    have h7 : (|Real.log c'| + K) ≤ T * ε := (div_le_iff₀ hε).1 (hj3.trans hjT)
    have h8 := neg_abs_le (Real.log c')
    have h9 := abs_nonneg (Real.log c')
    nlinarith
  refine ⟨T, hj1.trans hjT, fun z him hz => ?_⟩
  rcases le_total 0 z.re with h | h
  · exact key z him h ((le_abs_self _).trans hz)
  · rw [← xi_neg]
    exact key (-z) (by simpa using him) (by simpa using h) (by rw [neg_re]; exact (neg_le_abs _).trans hz)

/-! ### The closed ideal -/

/-- The closed subspace of `W a` on which, at every zero `ρ` at distance less than `a` from the
critical line, the moments of index less than `n ρ` vanish. -/
noncomputable def ideal (a : ℝ) (n : ℂ → ℕ) : Submodule ℂ (W a) :=
  ⨅ (ρ : ℂ) (hρ : ρ ∈ innerZeros a) (m : ℕ) (_ : m < n ρ),
    LinearMap.ker (moment (abs_re_lt_of_mem hρ) m).toLinearMap

/-- The closed ideal cut out by the zeros of zeta, with multiplicity. -/
noncomputable abbrev J (a : ℝ) : Submodule ℂ (W a) := ideal a zeroMult

lemma mem_ideal {n : ℂ → ℕ} {u : W a} : u ∈ ideal a n ↔
    ∀ (ρ : ℂ) (hρ : ρ ∈ innerZeros a), ∀ m < n ρ, moment (abs_re_lt_of_mem hρ) m u = 0 := by
  simp [ideal, Submodule.mem_iInf]

/-- The span of the translates of the theta function of the seed. -/
noncomputable def translateSpan (a : ℝ) : Submodule ℂ (W a) :=
  Submodule.span ℂ {u : W a | ∃ t : ℝ, u =ᵐ[wt a] fun x => theta seed (x - t)}

lemma theta_translate (t : ℝ) : ∃ f, ThetaClass f ∧ ∀ x, theta f x = theta seed (x - t) := by
  have hi := thetaClass_seed.integral
  refine ⟨(Real.exp (-t / 2) : ℂ) • dilate (Real.exp (-t)) (Real.exp_pos _) seed, ?_, fun x => ?_⟩
  · refine ⟨fun x => ?_, ?_, ?_⟩
    · simp [dilate_apply, thetaClass_seed.even]
    · simp [dilate_apply, thetaClass_seed.zero]
    · simp only [smul_apply, dilate_apply, smul_eq_mul]
      rw [integral_const_mul, Measure.integral_comp_mul_left, hi]
      simp
  · simp only [theta, smul_apply, dilate_apply, smul_eq_mul, tsum_mul_left]
    rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add]
    have e1 : x / 2 + -t / 2 = (x - t) / 2 := by ring
    have e2 : ∀ n : ℕ, Real.exp (-t) * ((n + 1) * Real.exp x) = (n + 1) * Real.exp (x - t) :=
      fun n => by rw [sub_eq_add_neg x t, Real.exp_add]; ring
    simp only [e1, e2]

lemma translateSpan_closure_le (a : ℝ) : (translateSpan a).topologicalClosure ≤ V a := by
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro u ⟨t, hu⟩
  obtain ⟨f, hf, h⟩ := theta_translate t
  exact ⟨f, hf, hu.trans (Eventually.of_forall fun x => (h x).symm)⟩

lemma rapid_theta_seed : Rapid (theta seed) where
  aesm := (measurable_theta seed).aestronglyMeasurable
  decay b := by
    obtain ⟨C, hC, h⟩ := exists_theta_le thetaClass_seed ⌈b⌉₊
    refine ⟨C, fun x => (h x).trans ?_⟩
    gcongr
    exact Nat.le_ceil b

lemma absolutelyContinuous_wt (a : ℝ) : volume ≪ wt a :=
  Measure.ae_le_iff_absolutelyContinuous.1 fun _ hp => ae_wt_iff.1 hp

lemma integrable_weight_mul_sq (hu : MemLp u 2 (wt a)) :
    Integrable fun x => 2 * Real.cosh (2 * a * x) * ‖u x‖ ^ 2 := by
  have h := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  rw [wt, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at h
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.cosh (2 * a * x)),
    smul_eq_mul]

lemma dual_of_mem (ha : 0 < a) (v u : W a) :
    Dual a (fun x => ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * conj (v x)) u := by
  have hv := (Lp.memLp v).1.mono_ac (absolutelyContinuous_wt a)
  have hu := (Lp.memLp u).1.mono_ac (absolutelyContinuous_wt a)
  constructor
  · have hm : AEStronglyMeasurable fun x : ℝ => (Real.exp (-a * |x|) : ℂ) *
        (((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * conj (v x)) :=
      (by fun_prop : Continuous fun x : ℝ => (Real.exp (-a * |x|) : ℂ)).aestronglyMeasurable.mul
        ((by fun_prop : Continuous fun x : ℝ =>
          ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ)).aestronglyMeasurable.mul
          (continuous_conj.comp_aestronglyMeasurable hv))
    refine (memLp_two_iff_integrable_sq_norm hm).2 (((integrable_weight_mul_sq (Lp.memLp v)).const_mul 2).mono'
      (hm.norm.pow 2) (Eventually.of_forall fun x => ?_))
    have hw := weight_le ha x
    have hp : 0 < 2 * Real.cosh (2 * a * x) := by positivity
    rw [norm_mul, norm_mul, norm_real, norm_real, RCLike.norm_conj, Real.norm_of_nonneg hp.le,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have e : Real.exp (-a * |x|) ^ 2 * Real.exp (2 * a * |x|) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_eq_one_iff]; push_cast; ring
    calc _ = Real.exp (-a * |x|) ^ 2 * (2 * Real.cosh (2 * a * x)) *
          (2 * Real.cosh (2 * a * x) * ‖v x‖ ^ 2) := by ring
      _ ≤ Real.exp (-a * |x|) ^ 2 * (2 * Real.exp (2 * a * |x|)) *
          (2 * Real.cosh (2 * a * x) * ‖v x‖ ^ 2) := by gcongr
      _ = _ := by linear_combination 2 * (2 * Real.cosh (2 * a * x) * ‖v x‖ ^ 2) * e
  · have hm : AEStronglyMeasurable fun x : ℝ => (Real.exp (a * |x|) : ℂ) * u x :=
      (by fun_prop : Continuous fun x : ℝ => (Real.exp (a * |x|) : ℂ)).aestronglyMeasurable.mul hu
    refine (memLp_two_iff_integrable_sq_norm hm).2 ((integrable_weight_mul_sq (Lp.memLp u)).mono'
      (hm.norm.pow 2) (Eventually.of_forall fun x => ?_))
    rw [norm_mul, norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      mul_pow, ← Real.exp_nat_mul]
    gcongr
    refine le_trans (le_of_eq ?_) (exp_le_weight x)
    push_cast
    ring_nf

lemma inner_eq_integral (v u : W a) : inner ℂ v u =
    ∫ x, ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * conj (v x) * u x := by
  rw [L2.inner_def, integral_wt]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply]
  ring

lemma V_le_J (a : ℝ) : V a ≤ J a := fun u hu => mem_ideal.2 fun ρ hρ m hm =>
  (moment_vanishes_iff (abs_re_lt_of_mem hρ) m).2
    (by rw [add_sub_cancel]; exact ⟨hρ, hm⟩) u hu

lemma J_le_closure (ha : 0 < a) : J a ≤ (translateSpan a).topologicalClosure := by
  intro u hu
  rw [mem_ideal] at hu
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro v hv
  have hd := dual_of_mem ha v u
  rw [inner_eq_integral]
  refine integral_eq_zero_of_order_le ha rapid_theta_seed hd
    ⟨a + 1, by linarith, exists_heights_xi (a + 1)⟩ (fun t => ?_) fun z hz => ?_
  · obtain ⟨f, hf, h⟩ := theta_translate t
    have hL := memLp_theta ha hf
    have h1 : hL.toLp ∈ translateSpan a := Submodule.subset_span
      ⟨t, hL.coeFn_toLp.trans (Eventually.of_forall h)⟩
    have h2 := (Submodule.mem_orthogonal' _ _).1 hv _ h1
    rw [inner_eq_integral] at h2
    rw [cross, ← h2]
    refine integral_congr_ae ?_
    filter_upwards [ae_wt_iff.1 hL.coeFn_toLp] with x hx
    rw [hx, h]
  · by_contra! hlt
    have hconv := hd.convAt hz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne_top
    have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (jet u 0) z := by
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hconv.analyticAt).2 fun m hm => ?_
      rw [hconv.iteratedDeriv]
      have h2 : (m : ℕ∞) < analyticOrderAt xi z :=
        lt_of_le_of_lt (by rw [← hn]; exact_mod_cast Nat.lt_succ_iff.1 hm) hlt
      obtain ⟨h3, h4⟩ := lt_analyticOrderAt_xi h2
      have h5 := hu (1 / 2 + z) ⟨h4.1, h4.2.1, h4.2.2, by simpa using hz⟩ m h3
      rwa [moment_apply, add_sub_cancel_left] at h5
    rw [← hn] at h1
    have : n + 1 ≤ n := by exact_mod_cast h1
    omega

/-- **Spectral synthesis.** The closed theta span is the closed ideal cut out by the zeros of zeta
at distance less than `a` from the critical line, with multiplicity. -/
theorem V_eq_J (ha : 0 < a) : V a = J a :=
  (V_le_J a).antisymm ((J_le_closure ha).trans (translateSpan_closure_le a))

/-- The closed theta span is generated by the translates of one theta function. -/
theorem V_eq_closure_translateSpan (ha : 0 < a) : V a = (translateSpan a).topologicalClosure :=
  ((V_le_J a).trans (J_le_closure ha)).antisymm (translateSpan_closure_le a)

/-- The closed theta span is never trivial. -/
theorem V_ne_bot (ha : 0 < a) : V a ≠ ⊥ := by
  intro e
  have hL := memLp_theta ha thetaClass_seed
  have h1 : hL.toLp ∈ V a := Submodule.le_topologicalClosure _ (Submodule.subset_span
    ⟨seed, thetaClass_seed, hL.coeFn_toLp⟩)
  rw [e, Submodule.mem_bot, Lp.eq_zero_iff_ae_eq_zero] at h1
  have h2 := ae_wt_iff.1 (hL.coeFn_toLp.symm.trans h1)
  have h3 : xi (2 - 1 / 2) = 0 := by
    rw [xi, jet_zero, integral_eq_zero_of_ae]
    filter_upwards [h2] with x hx
    rw [hx]
    simp
  rw [xi_eq (by simp) (by norm_num), zetaNum_of_ne (by norm_num)] at h3
  exact mul_ne_zero (mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_le_re (by simp)))
    (arch_ne_zero (by simp)) h3

/-- The ideal is proper when there is a zero at distance less than `a` from the critical line. -/
theorem J_ne_top (ha : 0 < a) {ρ : ℂ} (hρ : ρ ∈ innerZeros a) : J a ≠ ⊤ :=
  V_eq_J ha ▸ V_ne_top hρ

/-! ### Negative controls -/

/-- The transform of a rapidly decaying function can be divided by `z - c` at a zero `c`. -/
lemma exists_divided (hh : Rapid h) {c : ℂ} (h0 : jet h 0 c = 0) :
    ∃ u, Rapid u ∧ ∀ z, (z - c) * jet u 0 z = jet h 0 z := by
  set y : ℝ → ℂ := fun x => exp (c * x)
  have hy : Tempered |c.re| y := fun b hb => by
    refine (integrable_exp_neg_mul_abs (sub_pos.2 hb)).mono'
      (by fun_prop : Continuous fun x : ℝ => (Real.exp (-b * |x|) : ℂ) * exp (c * x)
        ).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_exp, ← Real.exp_add,
      Real.exp_le_exp, re_mul_ofReal]
    linarith [re_mul_le (le_refl |c.re|) x]
  have hc : ∀ t, cross y h t = 0 := fun t => by
    rw [cross, ← integral_add_right_eq_self _ t]
    have e : ∀ x : ℝ, y (x + t) * h (x + t - t) = exp (c * t) * (h x * exp (c * x)) := fun x => by
      simp only [y, add_sub_cancel_right, ofReal_add, mul_add, Complex.exp_add]
      ring
    simp only [e]
    rw [integral_const_mul, ← jet_zero, h0, mul_zero]
  have hg := rapid_cross hy hh hc
  set g := cross (pos y) h
  have hr : Rapid fun x => g (-x) :=
    ⟨hg.aesm.comp_measurePreserving (Measure.measurePreserving_neg volume), fun b => by
      obtain ⟨C, hC⟩ := hg.decay b
      exact ⟨C, fun x => by simpa using hC (-x)⟩⟩
  refine ⟨_, hr, fun z => ?_⟩
  have hd : ∀ {k}, Rapid k → Differentiable ℂ (jet k 0) := fun hk z =>
    ((hk.convAt z.re).hasDerivAt 0).2.differentiableAt
  have hl : Differentiable ℂ fun z => (z - c) * jet (fun x => g (-x)) 0 z :=
    (differentiable_id.sub_const c).mul (hd hr)
  refine congrFun (AnalyticOnNhd.eq_of_eventuallyEq (z₀ := ((|c.re| + 1 : ℝ) : ℂ))
    (fun w _ => hl.analyticAt w) (fun w _ => (hd hh).analyticAt w) ?_) z
  filter_upwards [(isOpen_lt (continuous_const (y := |c.re|)) continuous_re).mem_nhds
    (show |c.re| < _ by simp)] with w hw
  have hw' : |c.re| < w.re := hw
  have e1 : jet (fun x => g (-x)) 0 w = jet g 0 (-w) := by
    rw [jet_zero, jet_zero, ← integral_neg_eq_self]
    simp
  have hneg : (c - w).re < 0 := by rw [sub_re]; linarith [le_abs_self c.re]
  have hcw : w - c ≠ 0 := fun h => by
    rw [← neg_sub, h] at hneg
    simp at hneg
  have e2 : jet (pos y) 0 (-w) = 1 / (w - c) := by
    have e3 : ∀ x : ℝ, pos y x * exp (-w * x) = (Ioi 0).indicator (fun x : ℝ => exp ((c - w) * x)) x :=
      fun x => by
        rcases le_or_gt x 0 with hx | hx
        · simp [pos, not_lt.2 hx]
        · simp only [pos, indicator_of_mem (mem_Ioi.2 hx), y, ← Complex.exp_add]
          congr 1
          ring
    rw [jet_zero]
    simp only [e3]
    rw [integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi hneg,
      ← neg_sub w c]
    rw [ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
  rw [e1, jet_cross_pos hy hh hw', e2, ← mul_assoc, mul_one_div_cancel hcw, one_mul]

lemma Rapid.memLp (ha : 0 < a) (hu : Rapid u) : MemLp u 2 (wt a) := by
  obtain ⟨C, h⟩ := hu.decay (a + 1)
  refine memLp_wt hu.aesm ((integrable_exp_neg_mul_abs two_pos).const_mul (2 * C ^ 2)) fun x => ?_
  have h1 : ‖u x‖ ^ 2 ≤ (C * Real.exp (-(a + 1) * |x|)) ^ 2 := by gcongr; exact h x
  have h2 : Real.exp (2 * a * |x|) * Real.exp (-(a + 1) * |x|) ^ 2 = Real.exp (-2 * |x|) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc _ ≤ 2 * Real.exp (2 * a * |x|) * (C * Real.exp (-(a + 1) * |x|)) ^ 2 :=
        mul_le_mul (weight_le ha x) h1 (by positivity) (by positivity)
    _ = 2 * C ^ 2 * (Real.exp (2 * a * |x|) * Real.exp (-(a + 1) * |x|) ^ 2) := by ring
    _ = _ := by rw [h2]

lemma analyticOrderAt_xi_of_mem {ρ : ℂ} (hρ : ρ ∈ innerZeros a) :
    analyticOrderAt xi (ρ - 1 / 2) = zeroMult ρ := analyticOrderAt_xi hρ.2.1

/-- The orders in the definition of the ideal are sharp: raising or lowering the order at a single
zero, in particular dropping the zero, changes the subspace. -/
theorem V_eq_ideal_iff (ha : 0 < a) {n : ℂ → ℕ} :
    V a = ideal a n ↔ ∀ ρ ∈ innerZeros a, n ρ = zeroMult ρ := by
  constructor
  · intro e ρ hρ
    have hle : ∀ ρ ∈ innerZeros a, n ρ ≤ zeroMult ρ := fun ρ hρ => not_lt.1 fun hlt =>
      moment_zeroMult_not_vanishing hρ fun u hu => mem_ideal.1 (e ▸ hu) ρ hρ _ hlt
    refine (hle ρ hρ).antisymm (not_lt.1 fun hlt => ?_)
    have h0 : xi (ρ - 1 / 2) = 0 := by
      refine apply_eq_zero_of_analyticOrderAt_ne_zero ?_
      rw [analyticOrderAt_xi_of_mem hρ]
      exact_mod_cast (zeroMult_pos hρ.1).ne'
    obtain ⟨u, hu, hdiv⟩ := exists_divided rapid_theta_seed h0
    have hL := hu.memLp ha
    have hmom : ∀ {z : ℂ} (hz : |z.re| < a) (m : ℕ), moment hz m hL.toLp =
        iteratedDeriv m (jet u 0) z := fun {z} hz m => by
      rw [moment_apply, (hu.convAt z.re).iteratedDeriv, jet]
      refine integral_congr_ae ?_
      filter_upwards [ae_wt_iff.1 hL.coeFn_toLp] with x hx
      rw [hx]
    have hord : ∀ ρ' ∈ innerZeros a, analyticOrderAt (fun w => w - (ρ - 1 / 2)) (ρ' - 1 / 2) +
        analyticOrderAt (jet u 0) (ρ' - 1 / 2) = zeroMult ρ' := fun ρ' hρ' => by
      rw [← analyticOrderAt_mul (by fun_prop) (hu.convAt _).analyticAt,
        ← analyticOrderAt_xi_of_mem hρ']
      exact analyticOrderAt_congr (Eventually.of_forall hdiv)
    have hone : analyticOrderAt (fun w => w - (ρ - 1 / 2)) (ρ - 1 / 2) = 1 :=
      AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by fun_prop) (by simp) (by simp)
    have hmem : hL.toLp ∈ ideal a n := mem_ideal.2 fun ρ' hρ' m hm => by
      rw [hmom]
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := n ρ')
        (hu.convAt _).analyticAt).1 ?_ m hm
      have h1 := hord ρ' hρ'
      rcases eq_or_ne ρ' ρ with rfl | hne
      · rw [hone] at h1
        refine (ENat.add_le_add_iff_left (k := 1) (by simp)).1 ?_
        rw [h1, add_comm]
        exact_mod_cast hlt
      · rw [(by fun_prop : AnalyticAt ℂ (fun w => w - (ρ - 1 / 2)) (ρ' - 1 / 2)
          ).analyticOrderAt_eq_zero.2 (by simpa [sub_eq_zero] using hne), zero_add] at h1
        rw [h1]
        exact_mod_cast hle ρ' hρ'
    rw [← e, V_eq_J ha, mem_ideal] at hmem
    have h2 : (zeroMult ρ : ℕ∞) ≤ analyticOrderAt (jet u 0) (ρ - 1 / 2) :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hu.convAt _).analyticAt).2
        fun m hm => (hmom _ m).symm.trans (hmem ρ hρ m hm)
    have h3 := hord ρ hρ
    rw [hone] at h3
    have h4 : ((1 + zeroMult ρ : ℕ) : ℕ∞) ≤ zeroMult ρ := by
      rw [← h3]
      push_cast
      rw [← h3] at h2 ⊢
      gcongr
    have : 1 + zeroMult ρ ≤ zeroMult ρ := by exact_mod_cast h4
    omega
  · intro h
    rw [V_eq_J ha]
    ext u
    simp only [mem_ideal]
    exact forall₂_congr fun ρ hρ => by rw [h ρ hρ]

end Masullo.Synthesis
