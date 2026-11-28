import Masullo.Seed

/-!
# Moments that annihilate the theta span

`W a` is the `L²` space of the measure `2 cosh (2 a x) dx` and `V a` is the closed span of the theta
functions in it. For `|Re z| < a` the moments `u ↦ ∫ u(x) x^m e^{zx} dx` are continuous on `W a`.
They annihilate `V a` exactly when `ζ` has a zero of order greater than `m` at `1/2 + z` in the
critical strip. "Spectrum" means this set of annihilating exponential-polynomial moments; no
operator on the quotient, resolvent or operator spectrum is defined here.
Nothing here restricts a zero.

At a zero the moments vanish by the product formula for the transform of a theta function.
Conversely, the moments of the translates by `t` of one theta function are polynomials in `t` whose
coefficients are the moments of that function, up to a nonzero factor. Its transform is `ξ`, so they
vanish for all `t` only to the order of the zero.

The realisation of zeta zeros on a quotient by theta functions is due to Connes (1999) and Meyer
(2005), in the weighted setting of Masullo. The attributions to Connes and Meyer are recalled; the
sources were not consulted.
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace SchwartzMap FourierTransform ComplexConjugate ENNReal

namespace Masullo.Spectrum

open Synthesis

variable {f : 𝓢(ℝ, ℂ)}

/-- The moments at `z` annihilate all theta functions up to the order of the zero. The converse uses
the translates of one theta function only. -/
lemma forall_jet_eq_zero_iff (z : ℂ) (m : ℕ) :
    (∀ f, ThetaClass f → jet (theta f) m z = 0) ↔
      m < zeroMult (1 / 2 + z) ∧ 1 / 2 + z ∈ stripZeros := by
  constructor
  · intro h
    have hs := thetaClass_seed.rapid.convAt z.re
    let P : Polynomial ℂ := ∑ l ∈ Finset.range (m + 1),
      Polynomial.monomial (m - l) ((m.choose l : ℂ) * jet (theta seed) l z)
    have hP : P = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot P
        ((infinite_range_of_injective ofReal_injective).mono ?_)
      rintro _ ⟨t, rfl⟩
      obtain ⟨f, hf, e⟩ := theta_translate t
      have h1 := h f hf
      rw [show theta f = fun x => theta seed (x - t) from funext e,
        jet_translate fun l => (hs.hasDerivAt l).1] at h1
      simp only [mul_assoc, ← Finset.mul_sum] at h1
      refine (Eq.trans ?_ ((mul_eq_zero.1 h1).resolve_left (exp_ne_zero _)))
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      exact Finset.sum_congr rfl fun l _ => by ring
    refine lt_analyticOrderAt_xi ?_
    refine (by exact_mod_cast m.lt_succ_self : (m : ℕ∞) < (m + 1 : ℕ)).trans_le
      ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hs.analyticAt).2 fun l hl => ?_)
    rw [hs.iteratedDeriv]
    have h1 := congrArg (fun p : Polynomial ℂ => p.coeff (m - l)) hP
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single_of_mem l (Finset.mem_range.2 hl) fun k hk hkl =>
      if_neg (by have := Finset.mem_range.1 hk; omega), if_pos rfl] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (by exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.1 hl)).ne')
  · rintro ⟨hm, hz⟩ f hf
    have hA := hf.rapid.convAt z.re
    rw [← hA.iteratedDeriv]
    refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (n := zeroMult (1 / 2 + z)) hA.analyticAt).1 ?_ m hm
    have h1 := analyticOrderAt_jet hf hz.2.1
    have hne : 1 / 2 + z ≠ 1 := fun e => by
      have := hz.2.2
      rw [e] at this
      simp at this
    rw [analyticOrderAt_zetaNum, add_sub_cancel_left, (by fun_prop : AnalyticAt ℂ
      (fun w : ℂ => w - 1) (1 / 2 + z)).analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hne),
      zero_add] at h1
    rw [h1]
    exact le_self_add

/-! ### The Hilbert space and its functionals -/

/-- The measure `2 cosh (2 a x) dx`. -/
noncomputable def wt (a : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (2 * Real.cosh (2 * a * x))

/-- The weighted `L²` space, in the logarithmic variable. -/
noncomputable abbrev W (a : ℝ) := Lp ℂ 2 (wt a)

/-- The closed span of the theta functions. -/
noncomputable def V (a : ℝ) : Submodule ℂ (W a) :=
  (Submodule.span ℂ {u : W a | ∃ f, ThetaClass f ∧ u =ᵐ[wt a] theta f}).topologicalClosure

lemma exp_le_weight {a : ℝ} (x : ℝ) : Real.exp (2 * a * |x|) ≤ 2 * Real.cosh (2 * a * x) := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · linarith [Real.exp_pos (-(2 * a * x))]
  · rw [mul_neg]; linarith [Real.exp_pos (2 * a * x)]

lemma weight_le (a x : ℝ) : 2 * Real.cosh (2 * a * x) ≤ 2 * Real.exp (2 * |a| * |x|) := by
  have e : |2 * a * x| = 2 * |a| * |x| := by simp [abs_mul]
  have h1 := Real.exp_le_exp.2 (e ▸ le_abs_self (2 * a * x))
  have h2 := Real.exp_le_exp.2 (e ▸ neg_le_abs (2 * a * x))
  rw [Real.cosh_eq]
  linarith

lemma integral_wt (a : ℝ) (g : ℝ → ℂ) :
    ∫ x, g x ∂wt a = ∫ x, ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * g x := by
  rw [wt, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.cosh (2 * a * x)), real_smul]

lemma ae_wt_iff {a : ℝ} {p : ℝ → Prop} : (∀ᵐ x ∂wt a, p x) ↔ ∀ᵐ x, p x := by
  rw [wt, ae_withDensity_iff (by fun_prop)]
  refine eventually_congr (Eventually.of_forall fun x => ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact ⟨fun h => h (by positivity), fun h _ => h⟩

lemma memLp_wt {a : ℝ} {g : ℝ → ℂ} (hg : AEStronglyMeasurable g) {b : ℝ → ℝ} (hb : Integrable b)
    (h : ∀ x, 2 * Real.cosh (2 * a * x) * ‖g x‖ ^ 2 ≤ b x) : MemLp g 2 (wt a) := by
  have hg' : AEStronglyMeasurable g (wt a) := hg.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [memLp_two_iff_integrable_sq_norm hg', wt,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine hb.mono' (((by fun_prop : Measurable fun x => ENNReal.ofReal
    (2 * Real.cosh (2 * a * x))).ennreal_toReal.aestronglyMeasurable).smul (hg.norm.pow 2))
    (Eventually.of_forall fun x => ?_)
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact h x

/-- Rapidly decaying functions lie in every `W a`. -/
lemma _root_.Masullo.Synthesis.Rapid.memLp {u : ℝ → ℂ} (hu : Rapid u) (a : ℝ) :
    MemLp u 2 (wt a) := by
  obtain ⟨C, h⟩ := hu.decay (|a| + 1)
  refine memLp_wt hu.aesm ((integrable_exp_neg_mul_abs two_pos).const_mul (2 * C ^ 2)) fun x => ?_
  have h1 : ‖u x‖ ^ 2 ≤ (C * Real.exp (-(|a| + 1) * |x|)) ^ 2 := by gcongr; exact h x
  have h2 : Real.exp (2 * |a| * |x|) * Real.exp (-(|a| + 1) * |x|) ^ 2 = Real.exp (-2 * |x|) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc _ ≤ 2 * Real.exp (2 * |a| * |x|) * (C * Real.exp (-(|a| + 1) * |x|)) ^ 2 :=
        mul_le_mul (weight_le a x) h1 (by positivity) (by positivity)
    _ = 2 * C ^ 2 * (Real.exp (2 * |a| * |x|) * Real.exp (-(|a| + 1) * |x|) ^ 2) := by ring
    _ = _ := by rw [h2]

/-- Every theta function lies in every `W a`. -/
lemma memLp_theta (a : ℝ) (hf : ThetaClass f) : MemLp (theta f) 2 (wt a) := hf.rapid.memLp a

/-- The Riesz representative of a moment, as a function. -/
noncomputable def kernel (a : ℝ) (m : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  conj ((x : ℂ) ^ m * exp (z * x)) / ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ)

lemma memLp_kernel {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) : MemLp (kernel a m z) 2 (wt a) := by
  have hc : 0 < 2 * (a - |z.re|) := by linarith
  have hpos : ∀ x : ℝ, 0 < 2 * Real.cosh (2 * a * x) := fun x => by positivity
  refine memLp_wt (Measurable.aestronglyMeasurable ?_) (integrable_pow_mul_exp (2 * m) hc)
    fun x => ?_
  · have : Measurable fun z : ℂ => conj z := continuous_conj.measurable
    exact (this.comp (by fun_prop)).div (by fun_prop)
  rw [kernel, norm_div, RCLike.norm_conj, norm_pow_mul_exp, norm_real,
    Real.norm_of_nonneg (hpos x).le, div_pow, mul_div_assoc', sq (2 * Real.cosh _),
    mul_div_mul_left _ _ (hpos x).ne', div_le_iff₀ (hpos x), mul_pow, ← pow_mul, mul_comm m,
    mul_assoc, ← Real.exp_nat_mul]
  have h1 : Real.exp ((2 : ℕ) * (z.re * x)) ≤
      Real.exp (-(2 * (a - |z.re|)) * |x|) * Real.exp (2 * a * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have := re_mul_le (le_refl |z.re|) x
    push_cast
    linarith
  gcongr
  exact h1.trans (by gcongr; exact exp_le_weight x)

/-- The Riesz representative of a moment, as a vector of `W a`. -/
noncomputable abbrev riesz {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) : W a :=
  (memLp_kernel hz m).toLp _

/-- The moment as a continuous functional on `W a`. -/
noncomputable def moment {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) : W a →L[ℂ] ℂ :=
  innerSL ℂ (riesz hz m)

lemma moment_apply {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) (u : W a) :
    moment hz m u = ∫ x : ℝ, u x * ((x : ℂ) ^ m * exp (z * x)) := by
  rw [moment, innerSL_apply_apply, L2.inner_def, integral_wt]
  refine integral_congr_ae ?_
  filter_upwards [ae_wt_iff.1 (memLp_kernel hz m).coeFn_toLp] with x hx
  have hpos : ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (by positivity)
  rw [hx, RCLike.inner_apply, kernel, map_div₀, conj_conj, conj_ofReal]
  field_simp

/-- The moments of a rapidly decaying function are the derivatives of its transform. -/
lemma moment_toLp {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) {u : ℝ → ℂ} (hu : Rapid u) :
    moment hz m (hu.memLp a).toLp = iteratedDeriv m (jet u 0) z := by
  rw [moment_apply, (hu.convAt z.re).iteratedDeriv, jet]
  refine integral_congr_ae ?_
  filter_upwards [ae_wt_iff.1 (hu.memLp a).coeFn_toLp] with x hx
  rw [hx]

/-- No moment is the zero functional. -/
lemma moment_ne_zero {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) : moment hz m ≠ 0 := by
  intro h
  have h1 : (memLp_kernel hz m).toLp _ = 0 := by
    have h2 := congrArg (fun L => L ((memLp_kernel hz m).toLp _)) h
    rw [moment, innerSL_apply_apply] at h2
    exact inner_self_eq_zero.1 h2
  rw [Lp.eq_zero_iff_ae_eq_zero] at h1
  have h3 := ae_wt_iff.1 ((memLp_kernel hz m).coeFn_toLp.symm.trans h1)
  have h4 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  obtain ⟨x, hx, hx0⟩ := (h3.and h4).exists
  have hpos : (0 : ℝ) < 2 * Real.cosh (2 * a * x) := by positivity
  have hx' : kernel a m z x = 0 := hx
  rw [kernel, div_eq_zero_iff, map_eq_zero, mul_eq_zero] at hx'
  rcases hx' with (h5 | h5) | h5
  · exact hx0 (by exact_mod_cast eq_zero_of_pow_eq_zero h5)
  · exact exp_ne_zero _ h5
  · exact hpos.ne' (by exact_mod_cast h5)

lemma moment_vanishes_iff_jet {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) :
    (∀ u ∈ V a, moment hz m u = 0) ↔ ∀ f, ThetaClass f → jet (theta f) m z = 0 := by
  have hjet : ∀ (u : W a) f, u =ᵐ[wt a] theta f → moment hz m u = jet (theta f) m z := by
    intro u f hu
    rw [moment_apply, jet]
    refine integral_congr_ae ?_
    filter_upwards [ae_wt_iff.1 hu] with x hx
    rw [hx]
  constructor
  · intro h f hf
    have hmem := memLp_theta a hf
    rw [← hjet (hmem.toLp _) f hmem.coeFn_toLp]
    exact h _ (Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨f, hf, hmem.coeFn_toLp⟩))
  · intro h u hu
    have hle : V a ≤ LinearMap.ker (moment hz m).toLinearMap := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
        (moment hz m).isClosed_ker
      rintro v ⟨f, hf, hv⟩
      exact (hjet v f hv).trans (h f hf)
    exact hle hu

/-! ### The annihilating moments -/

/-- **Theorem S.** For `|Re z| < a` the `m`-th moment at `z` annihilates `V a` iff `1/2 + z` is a
zero of `ζ` in the critical strip, of multiplicity greater than `m`. -/
theorem moment_vanishes_iff {a : ℝ} {z : ℂ} (hz : |z.re| < a) (m : ℕ) :
    (∀ u ∈ V a, moment hz m u = 0) ↔
      1 / 2 + z ∈ innerZeros a ∧ m < zeroMult (1 / 2 + z) := by
  rw [moment_vanishes_iff_jet, forall_jet_eq_zero_iff, and_comm]
  refine and_congr_left fun _ => ⟨fun h => ⟨h.1, h.2.1, h.2.2, ?_⟩, fun h => ⟨h.1, h.2.1, h.2.2.1⟩⟩
  simpa using hz

/-- For `a ≤ 1/2` the strip condition is automatic. -/
theorem moment_vanishes_iff_of_le_half {a : ℝ} (ha : a ≤ 1 / 2) {z : ℂ} (hz : |z.re| < a) (m : ℕ) :
    (∀ u ∈ V a, moment hz m u = 0) ↔ m < zeroMult (1 / 2 + z) := by
  rw [moment_vanishes_iff]
  refine and_iff_right_of_imp fun h => ?_
  have h0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_zero_of_lt h)
  have hre : (1 / 2 + z).re = 1 / 2 + z.re := by norm_num
  have := abs_lt.1 hz
  exact ⟨h0, by rw [hre]; linarith, by rw [hre]; linarith, by simpa using hz⟩

/-- The characters that annihilate `V a` are the zeros at distance less than `a` from the critical
line. -/
theorem moment_zero_vanishes_iff {a : ℝ} {z : ℂ} (hz : |z.re| < a) :
    (∀ u ∈ V a, moment hz 0 u = 0) ↔ 1 / 2 + z ∈ innerZeros a := by
  rw [moment_vanishes_iff]
  exact and_iff_left_of_imp fun h => zeroMult_pos h.1

lemma abs_re_lt_of_mem {a : ℝ} {ρ : ℂ} (h : ρ ∈ innerZeros a) : |(ρ - 1 / 2).re| < a := by
  simpa using h.2.2.2

/-- A zero at distance less than `a` from the critical line makes the quotient nonzero. -/
theorem V_ne_top {a : ℝ} {ρ : ℂ} (h : ρ ∈ innerZeros a) : V a ≠ ⊤ := by
  intro e
  refine moment_ne_zero (abs_re_lt_of_mem h) 0 (ContinuousLinearMap.ext fun u => ?_)
  exact (moment_zero_vanishes_iff (abs_re_lt_of_mem h)).2 (by simpa using h) u (by simp [e])

/-! ### Negative controls -/

/-- The bound on `m` is sharp: at a zero, the moment whose index is the multiplicity does not
annihilate `V a`. -/
theorem moment_zeroMult_not_vanishing {a : ℝ} {ρ : ℂ} (h : ρ ∈ innerZeros a) :
    ¬ ∀ u ∈ V a, moment (abs_re_lt_of_mem h) (zeroMult ρ) u = 0 := by
  rw [moment_vanishes_iff]
  simp

/-- The strip condition in `moment_vanishes_iff` cannot be dropped: at the trivial zero `-2` the
multiplicity is positive, yet the character does not annihilate `V 3`. -/
theorem trivial_zero_not_vanishing : 0 < zeroMult (-2) ∧ ∃ hz : |(-2 - 1 / 2 : ℂ).re| < 3,
    ¬ ∀ u ∈ V 3, moment hz 0 u = 0 := by
  refine ⟨?_, by norm_num [abs_lt], ?_⟩
  · rw [show (-2 : ℂ) = -2 * ((0 : ℕ) + 1) by norm_num]
    exact zeroMult_pos (riemannZeta_neg_two_mul_nat_add_one 0)
  · rw [moment_zero_vanishes_iff]
    intro h
    have := h.2.1
    norm_num at this

end Masullo.Spectrum
