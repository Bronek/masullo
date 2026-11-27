import Masullo.Spectrum
import WeilExplicit.GoodHeights
import WeilExplicit.LowerBound

/-!
# Spectral synthesis for the theta span

`V a`, the closed span of the theta functions in `W a`, is the closed subspace `J a` on which the
moments at the zeros of zeta at distance less than `a` from the critical line vanish, up to
multiplicity. It is also the closed span of the translates of one theta function. Both hold for
every `a > 0`. Nothing here restricts a zero: the zeros in `J a` may lie anywhere in the strip
`|Re ρ - 1/2| < a`, and zeros on its edges or outside it impose no condition.

`ideal` names an intersection of kernels of moments. It is a closed subspace; no algebra structure
and no convolution-ideal property is established.

The proof is the duality theorem of `Masullo.Synthesis.Duality` applied to the seed of
`Masullo.Seed`, whose theta function has transform `ξ(1/2 + z)`: if `v` is orthogonal to the
translates, correlate it with `u`, cut that correlation at `0`, and correlate its right half with
the seed. The heights come from a bound for `ζ'/ζ` and an elementary lower bound for the Gamma
function. For `a > 0` the theorem gives the orthogonal complement of `V a` as the closed span of the
Riesz vectors of the moments; it gives no basis and no expansion.

The bound for `ζ'/ζ` at good heights is `WeilExplicit.good_heights`. The theta span follows the
spectral realisations of Connes (1999) and Meyer (2005) (recalled; sources not consulted). The
Carleman transform and the duality method are credited in `Masullo.Synthesis.Duality`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace SchwartzMap FourierTransform ComplexConjugate ENNReal

namespace Masullo.Synthesis

open Spectrum

variable {u h : ℝ → ℂ} {a : ℝ}

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
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity),
        ← mul_assoc]
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
  obtain ⟨C, hC, H⟩ := WeilExplicit.good_heights
  refine ⟨8 * C, by positivity, fun j hj => ?_⟩
  obtain ⟨T, hjT, hT, HT⟩ := H j hj
  have hj7 : (7 : ℝ) ≤ j := by exact_mod_cast hj
  refine ⟨T, hjT, hT, fun s him hs => ?_⟩
  have hfar : ∀ w : ℂ, 2 ≤ w.re → 1 / 3 ≤ ‖riemannZeta w‖ := fun w hw =>
    WeilExplicit.one_third_le_norm_riemannZeta hw
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
            have h6 : Real.exp (-K * T) ≤
                Real.exp (-C * (T + 3)) * Real.exp (-Real.pi * (T / 2)) := by
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
    exact key (-z) (by simpa using him) (by simpa using h)
      (by rw [neg_re]; exact (neg_le_abs _).trans hz)

/-! ### The closed subspace of the zeros -/

/-- The closed subspace of `W a` on which, at every zero `ρ` at distance less than `a` from the
critical line, the moments of index less than `n ρ` vanish. -/
noncomputable def ideal (a : ℝ) (n : ℂ → ℕ) : Submodule ℂ (W a) :=
  ⨅ (ρ : ℂ) (hρ : ρ ∈ innerZeros a) (m : ℕ) (_ : m < n ρ),
    LinearMap.ker (moment (abs_re_lt_of_mem hρ) m).toLinearMap

/-- The closed subspace cut out by the zeros of zeta, with multiplicity. -/
noncomputable abbrev J (a : ℝ) : Submodule ℂ (W a) := ideal a zeroMult

lemma mem_ideal {n : ℂ → ℕ} {u : W a} : u ∈ ideal a n ↔
    ∀ (ρ : ℂ) (hρ : ρ ∈ innerZeros a), ∀ m < n ρ, moment (abs_re_lt_of_mem hρ) m u = 0 := by
  simp [ideal, Submodule.mem_iInf]

/-- The span of the translates of the theta function of the seed. -/
noncomputable def translateSpan (a : ℝ) : Submodule ℂ (W a) :=
  Submodule.span ℂ {u : W a | ∃ t : ℝ, u =ᵐ[wt a] fun x => theta seed (x - t)}

lemma translateSpan_closure_le (a : ℝ) : (translateSpan a).topologicalClosure ≤ V a := by
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro u ⟨t, hu⟩
  obtain ⟨f, hf, h⟩ := theta_translate t
  exact ⟨f, hf, hu.trans (Eventually.of_forall fun x => (h x).symm)⟩

lemma rapid_theta_seed : Rapid (theta seed) := thetaClass_seed.rapid

lemma absolutelyContinuous_wt (a : ℝ) : volume ≪ wt a :=
  Measure.ae_le_iff_absolutelyContinuous.1 fun _ hp => ae_wt_iff.1 hp

lemma integrable_weight_mul_sq (hu : MemLp u 2 (wt a)) :
    Integrable fun x => 2 * Real.cosh (2 * a * x) * ‖u x‖ ^ 2 := by
  have h := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  rw [wt, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at h
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.cosh (2 * a * x)),
    smul_eq_mul]

lemma dual_of_mem (ha : 0 < a) (v u : W a) :
    Dual a (fun x => ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * conj (v x)) u := by
  have hv := (Lp.memLp v).aestronglyMeasurable.mono_ac (absolutelyContinuous_wt a)
  have hu := (Lp.memLp u).aestronglyMeasurable.mono_ac (absolutelyContinuous_wt a)
  constructor
  · have hm : AEStronglyMeasurable fun x : ℝ => (Real.exp (-a * |x|) : ℂ) *
        (((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * conj (v x)) :=
      (by fun_prop : Continuous fun x : ℝ => (Real.exp (-a * |x|) : ℂ)).aestronglyMeasurable.mul
        ((by fun_prop : Continuous fun x : ℝ =>
          ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ)).aestronglyMeasurable.mul
          (continuous_conj.comp_aestronglyMeasurable hv))
    refine (memLp_two_iff_integrable_sq_norm hm).2
      (((integrable_weight_mul_sq (Lp.memLp v)).const_mul 2).mono'
      (hm.norm.pow 2) (Eventually.of_forall fun x => ?_))
    have hw := weight_le a x
    rw [abs_of_pos ha] at hw
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
    rw [norm_mul, norm_real, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity),
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
    have hL := memLp_theta a hf
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
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hconv.analyticAt).2
        fun m hm => ?_
      rw [hconv.iteratedDeriv]
      have h2 : (m : ℕ∞) < analyticOrderAt xi z :=
        lt_of_le_of_lt (by rw [← hn]; exact_mod_cast Nat.lt_succ_iff.1 hm) hlt
      obtain ⟨h3, h4⟩ := lt_analyticOrderAt_xi h2
      have h5 := hu (1 / 2 + z) ⟨h4.1, h4.2.1, h4.2.2, by simpa using hz⟩ m h3
      rwa [moment_apply, add_sub_cancel_left] at h5
    rw [← hn] at h1
    have : n + 1 ≤ n := by exact_mod_cast h1
    omega

/-- **Spectral synthesis.** The closed theta span is the closed subspace cut out by the zeros of
zeta at distance less than `a` from the critical line, with multiplicity. -/
theorem V_eq_J (ha : 0 < a) : V a = J a :=
  (V_le_J a).antisymm ((J_le_closure ha).trans (translateSpan_closure_le a))

/-- The closed theta span is generated by the translates of one theta function. -/
theorem V_eq_closure_translateSpan (ha : 0 < a) : V a = (translateSpan a).topologicalClosure :=
  ((V_le_J a).trans (J_le_closure ha)).antisymm (translateSpan_closure_le a)

/-- The closed theta span is never trivial. -/
theorem V_ne_bot (a : ℝ) : V a ≠ ⊥ := by
  intro e
  have hL := memLp_theta a thetaClass_seed
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

/-- `J a` is proper when there is a zero at distance less than `a` from the critical line. -/
theorem J_ne_top {ρ : ℂ} (hρ : ρ ∈ innerZeros a) : J a ≠ ⊤ :=
  V_eq_J ((abs_nonneg _).trans_lt hρ.2.2.2) ▸ V_ne_top hρ

/-- The closed theta span is everything iff there is no zero at distance less than `a` from the
critical line. Neither side is asserted. -/
theorem V_eq_top_iff (ha : 0 < a) : V a = ⊤ ↔ innerZeros a = ∅ := by
  refine ⟨fun h => eq_empty_of_forall_notMem fun ρ hρ => V_ne_top hρ h, fun h => ?_⟩
  rw [V_eq_J ha, Submodule.eq_top_iff']
  exact fun u => mem_ideal.2 fun ρ hρ => by simp [h] at hρ

/-- The Riesz vectors of the moments at the zeros, up to multiplicity, span a dense subspace of the
orthogonal complement of the closed theta span. -/
theorem orthogonal_V_eq (ha : 0 < a) : (V a)ᗮ = (Submodule.span ℂ {v : W a | ∃ (ρ : ℂ)
    (hρ : ρ ∈ innerZeros a), ∃ m < zeroMult ρ,
      v = riesz (abs_re_lt_of_mem hρ) m}).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  congr 1
  rw [V_eq_J ha]
  ext u
  rw [mem_ideal, Submodule.mem_orthogonal]
  refine ⟨fun h v hv => ?_, fun h ρ hρ m hm => h _ (Submodule.subset_span ⟨ρ, hρ, m, hm, rfl⟩)⟩
  refine Submodule.span_induction (p := fun v _ => inner ℂ v u = 0) ?_ (inner_zero_left _)
    (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero])
    (fun r x _ hx => by rw [inner_smul_left, hx, mul_zero]) hv
  rintro _ ⟨ρ, hρ, m, hm, rfl⟩
  exact h ρ hρ m hm

/-! ### Independence of the moments -/

lemma analyticOrderAt_xi_of_mem {ρ : ℂ} (hρ : ρ ∈ innerZeros a) :
    analyticOrderAt xi (ρ - 1 / 2) = zeroMult ρ := analyticOrderAt_xi hρ.2.1

/-- The moments at the zeros are independent: each is nonzero on a function annihilated by all the
moments at other zeros, up to multiplicity, and by the lower moments at the same zero. -/
lemma exists_separating {ρ : ℂ} (hρ : ρ ∈ innerZeros a) {m : ℕ} (hm : m < zeroMult ρ) :
    ∃ u : W a, moment (abs_re_lt_of_mem hρ) m u ≠ 0 ∧ ∀ (ρ' : ℂ) (hρ' : ρ' ∈ innerZeros a),
      ∀ l < zeroMult ρ', (ρ' = ρ → l < m) → moment (abs_re_lt_of_mem hρ') l u = 0 := by
  set c := ρ - 1 / 2
  have hord : ∀ (n : ℕ) (u : ℝ → ℂ), Rapid u → (∀ z, (z - c) ^ n * jet u 0 z = xi z) →
      ∀ ρ' ∈ innerZeros a, analyticOrderAt (fun w => (w - c) ^ n) (ρ' - 1 / 2) +
        analyticOrderAt (jet u 0) (ρ' - 1 / 2) = zeroMult ρ' := fun n u hu h ρ' hρ' => by
    rw [← analyticOrderAt_mul (by fun_prop) (hu.convAt _).analyticAt,
      ← analyticOrderAt_xi_of_mem hρ']
    exact analyticOrderAt_congr (Eventually.of_forall h)
  have hone : analyticOrderAt (fun w => w - c) c = 1 :=
    AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by fun_prop) (by simp) (by simp)
  have hpow : ∀ n : ℕ, analyticOrderAt (fun w => (w - c) ^ n) c = n := fun n => by
    have := analyticOrderAt_pow (f := fun w => w - c) (z₀ := c) (by fun_prop) n
    rw [hone, nsmul_one] at this
    exact this
  have hdiv : ∀ n ≤ zeroMult ρ, ∃ u, Rapid u ∧ ∀ z, (z - c) ^ n * jet u 0 z = xi z := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨_, rapid_theta_seed, fun z => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨u, hu, h⟩ := ih (by omega)
      have h0 : jet u 0 c = 0 := by
        refine apply_eq_zero_of_analyticOrderAt_ne_zero fun e => ?_
        have h1 := hord n u hu h ρ hρ
        rw [hpow, e, add_zero] at h1
        have : n = zeroMult ρ := by exact_mod_cast h1
        omega
      obtain ⟨u', hu', h'⟩ := exists_divided hu h0
      exact ⟨u', hu', fun z => by rw [pow_succ, mul_assoc, h', h]⟩
  obtain ⟨u, hu, h⟩ := hdiv (zeroMult ρ - m) (Nat.sub_le _ _)
  have hρm : analyticOrderAt (jet u 0) c = m := by
    have h1 := hord _ u hu h ρ hρ
    rw [hpow] at h1
    change _ + analyticOrderAt (jet u 0) c = _ at h1
    generalize analyticOrderAt (jet u 0) c = o at h1 ⊢
    induction o using ENat.recTopCoe with
    | top => simp at h1
    | coe o =>
      have : zeroMult ρ - m + o = zeroMult ρ := by exact_mod_cast h1
      exact_mod_cast (by omega : o = m)
  have hder := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hu.convAt c.re).analyticAt).1 hρm
  refine ⟨(hu.memLp a).toLp, (moment_toLp _ m hu).trans_ne hder.2, fun ρ' hρ' l hl hlt => ?_⟩
  rw [moment_toLp _ l hu]
  rcases eq_or_ne ρ' ρ with rfl | hne
  · exact hder.1 l (hlt rfl)
  · have h1 := hord _ u hu h ρ' hρ'
    rw [(by fun_prop : AnalyticAt ℂ (fun w => (w - c) ^ (zeroMult ρ - m)) (ρ' - 1 / 2)
      ).analyticOrderAt_eq_zero.2 (pow_ne_zero _ (by simpa [c, sub_eq_zero] using hne)),
      zero_add] at h1
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (hu.convAt _).analyticAt).1 h1.ge l hl

/-! ### Negative control -/

/-- The orders in the definition of `J a` are sharp: raising or lowering the order at a single
zero, in particular dropping the zero, changes the subspace. -/
theorem V_eq_ideal_iff (ha : 0 < a) {n : ℂ → ℕ} :
    V a = ideal a n ↔ ∀ ρ ∈ innerZeros a, n ρ = zeroMult ρ := by
  constructor
  · intro e ρ hρ
    have hle : ∀ ρ ∈ innerZeros a, n ρ ≤ zeroMult ρ := fun ρ hρ => not_lt.1 fun hlt =>
      moment_zeroMult_not_vanishing hρ fun u hu => mem_ideal.1 (e ▸ hu) ρ hρ _ hlt
    refine (hle ρ hρ).antisymm (not_lt.1 fun hlt => ?_)
    have hm : zeroMult ρ - 1 < zeroMult ρ := by omega
    obtain ⟨u, hu, hsep⟩ := exists_separating hρ hm
    have hmem : u ∈ ideal a n := mem_ideal.2 fun ρ' hρ' m hm' =>
      hsep ρ' hρ' m (hm'.trans_le (hle ρ' hρ')) (by rintro rfl; omega)
    rw [← e, V_eq_J ha, mem_ideal] at hmem
    exact hu (hmem ρ hρ _ hm)
  · intro h
    rw [V_eq_J ha]
    ext u
    simp only [mem_ideal]
    exact forall₂_congr fun ρ hρ => by rw [h ρ hρ]

end Masullo.Synthesis
