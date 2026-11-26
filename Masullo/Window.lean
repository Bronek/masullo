import Masullo.Landau
import Masullo.Trace

/-!
# The window criterion

`windowSum x` is a smoothed prime counting function minus its main term. A one-sided bound
`windowSum x ≤ C x ^ θ` on windows `[Y, Y ^ (1 + δ)]` with `Y` arbitrarily large rules out zeros of
zeta in `Re s > θ`. The implication is one-way: no converse is stated, and the bound is not asserted
for any `θ < 1`.

The generic argument is `Masullo.Landau.Continues.eq_empty_of_window`. In the transform at `1`,
`-x log x` cancels the double pole and `(1 + γ) x` the simple pole that remains.
-/

open MeasureTheory Complex Set Filter Topology Metric
open ArithmeticFunction (vonMangoldt_nonneg LSeriesSummable_vonMangoldt
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div vonMangoldt_mul_zeta)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo.Window

open Landau Spectrum WeilExplicit

/-- `∑_{n ≤ x} Λ(n) (x / n - 1) - x log x + (1 + γ) x`. -/
noncomputable def windowSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x +
    (1 + Real.eulerMascheroniConstant) * x

/-! ### The Laplace transform -/

/-- A term of the prime sum in the logarithmic variable; it vanishes for `u ≤ log n`. -/
noncomputable def term (n : ℕ) (u : ℝ) : ℝ := Λ n * max (Real.exp u / n - 1) 0

lemma term_nonneg (n : ℕ) (u : ℝ) : 0 ≤ term n u := mul_nonneg vonMangoldt_nonneg (le_max_right _ _)

lemma hasSum_term (u : ℝ) : HasSum (fun n => term n u)
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, Λ n * (Real.exp u / n - 1)) := by
  have e : ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, Λ n * (Real.exp u / n - 1) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, term n u := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have h3 : (0 : ℝ) < n := by exact_mod_cast h1
    rw [term, max_eq_left]
    rw [sub_nonneg, one_le_div h3]
    exact (Nat.le_floor_iff (Real.exp_pos u).le).1 h2
  rw [e]
  refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | h1
  · simp [term]
  · have h2 : ⌊Real.exp u⌋₊ < n := by simpa [Nat.one_le_iff_ne_zero, h1.ne'] using hn
    rw [term, max_eq_right, mul_zero]
    rw [sub_nonpos, div_le_one (by exact_mod_cast h1)]
    exact ((Nat.floor_lt (Real.exp_pos u).le).1 h2).le

lemma laplace_mul_exp {s : ℂ} (h : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u))) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u)) = 1 / (s - 1) ^ 2 := by
  have e (u : ℝ) : ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u)) = u * cexp (-((s - 1) * u)) := by
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  simp_rw [e]
  have hz : 0 < (s - 1).re := by simpa using h
  have hne : s - 1 ≠ 0 := fun h0 => by simp [h0] at hz
  generalize s - 1 = z at hz hne
  have hi : IntegrableOn (fun u : ℝ => (u : ℂ) * cexp (-(z * u))) (Ioi 0) := by
    simpa using integrable_kernel (f := fun _ => 1) (A := 1) (c := 0) measurable_const
      (by simp) 1 hz
  refine ⟨hi, ?_⟩
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => -(u / z + 1 / z ^ 2) * cexp (-(z * u)))
      (u * cexp (-(z * u))) u := by
    have h1 : HasDerivAt (fun u : ℝ => -((u : ℂ) / z + 1 / z ^ 2)) (-(1 / z)) u :=
      ((ofRealCLM.hasDerivAt.div_const z).add_const _).neg
    have h2 : HasDerivAt (fun u : ℝ => cexp (-(z * u))) (cexp (-(z * u)) * -(z * 1)) u :=
      ((ofRealCLM.hasDerivAt.const_mul z).neg).cexp
    refine (h1.mul h2).congr_deriv ?_
    field_simp
    ring
  have ht : Tendsto (fun u : ℝ => -(u / z + 1 / z ^ 2) * cexp (-(z * u))) atTop (𝓝 0) := by
    have lim (j : ℕ) : Tendsto (fun u : ℝ => (u : ℂ) ^ j * cexp (-(z * u))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero j z.re hz).congr' ?_
      filter_upwards [eventually_ge_atTop 0] with u hu
      simp [norm_exp, abs_of_nonneg hu]
    have := ((lim 1).const_mul (-(1 / z))).add ((lim 0).const_mul (-(1 / z ^ 2)))
    simp only [mul_zero, add_zero] at this
    exact this.congr fun u => by ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) hi ht]
  simp

lemma laplace_term {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (fun u : ℝ => (term n u : ℂ) * cexp (-(s * u))) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (term n u : ℂ) * cexp (-(s * u)) =
        LSeries.term (fun n => (Λ n : ℂ)) s n * (1 / (s * (s - 1))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [term]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have e : (fun u : ℝ => (term n u : ℂ) * cexp (-(s * u))) = (Ioi (Real.log n)).indicator
      fun u : ℝ => (Λ n / n : ℂ) * (cexp (1 * u) * cexp (-(s * u))) -
        Λ n * (cexp (0 * u) * cexp (-(s * u))) := by
    ext u
    by_cases hu : u ∈ Ioi (Real.log n)
    · rw [indicator_of_mem hu, term, max_eq_left]
      · push_cast
        rw [zero_mul, Complex.exp_zero, one_mul]
        ring
      · rw [sub_nonneg, one_le_div hn0, ← Real.log_le_iff_le_exp hn0]
        exact (mem_Ioi.1 hu).le
    · rw [indicator_of_notMem hu, term, max_eq_right]
      · simp
      · rw [sub_nonpos, div_le_one hn0, ← Real.le_log_iff_exp_le hn0]
        exact not_lt.1 hu
  obtain ⟨i1, v1⟩ := laplace_exp (a := 1) (s := s) (by simpa) (Real.log n)
  obtain ⟨i0, v0⟩ := laplace_exp (a := 0) (s := s) (by simpa using by linarith) (Real.log n)
  have hi := (i1.const_mul (Λ n / n : ℂ)).sub (i0.const_mul (Λ n : ℂ))
  rw [e]
  refine ⟨?_, ?_⟩
  · exact ((integrable_indicator_iff measurableSet_Ioi).2 hi).integrableOn
  · rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi hlog),
      integral_sub (i1.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul,
      v1, v0]
    have hs0 : s ≠ 0 := fun h => by norm_num [h] at hs
    have hs1 : s - 1 ≠ 0 := fun h => by simp [sub_eq_zero.1 h] at hs
    have hpow : (n : ℂ) ^ s ≠ 0 := by simp [cpow_eq_zero_iff, hnc]
    have h0 : cexp ((0 - s) * Real.log n) = ((n : ℂ) ^ s)⁻¹ := by
      rw [cpow_def_of_ne_zero hnc, ← Complex.exp_neg, natCast_log]
      ring_nf
    have h1 : cexp ((1 - s) * Real.log n) = n * ((n : ℂ) ^ s)⁻¹ := by
      rw [sub_mul, one_mul, sub_eq_add_neg, Complex.exp_add, ← neg_mul, ← zero_sub, h0, natCast_log,
        exp_log hnc]
    rw [h0, h1, LSeries.term_of_ne_zero hn.ne']
    field_simp
    ring

lemma laplace_sum {s : ℂ} (hs : 1 < s.re) : ∫ u in Ioi (0 : ℝ),
    ((∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, Λ n * (Real.exp u / n - 1) : ℝ) : ℂ) * cexp (-(s * u)) =
      -deriv riemannZeta s / riemannZeta s * (1 / (s * (s - 1))) := by
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (n : ℕ) (u : ℝ) => (term n u : ℂ) * cexp (-(s * u)))
    (fun n => (laplace_term hs n).1) ?_
  · have pt (u : ℝ) := ((hasSum_ofReal ).2 (hasSum_term u)).mul_right (cexp (-(s * u)))
    simp only [fun u => (pt u).tsum_eq, (laplace_term hs _).2] at h
    rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    exact h.unique ((LSeriesSummable_vonMangoldt hs).hasSum.mul_right _)
  · have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa
    rw [← summable_ofReal]
    refine ((LSeriesSummable_vonMangoldt hσ).mul_right
      (1 / ((s.re : ℂ) * (s.re - 1)))).congr fun n => ?_
    rw [← (laplace_term hσ n).2, ← integral_complex_ofReal]
    congr 1 with u
    rw [norm_mul, norm_exp, norm_real, Real.norm_of_nonneg (term_nonneg n u)]
    simp

/-! ### The continuation -/

/-- Numerator of the continued transform of `windowSum (e ^ u)`, whose denominator is
`s (s - 1)`. -/
noncomputable def num (s : ℂ) : ℂ :=
  (1 + Real.eulerMascheroniConstant) * s - 1 - logDeriv zetaNum s

/-- The continuation of the Laplace transform of `-windowSum (e ^ u)`. -/
noncomputable def continuation (s : ℂ) : ℂ := -(dslope num 1 s / s)

lemma zetaNum_ne_zero {s : ℂ} (h : riemannZeta s ≠ 0) : zetaNum s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [zetaNum]
  · rw [zetaNum_of_ne hs]
    exact mul_ne_zero (sub_ne_zero.2 hs) h

lemma num_one : num 1 = 0 := by
  have h : HasDerivAt zetaNum Real.eulerMascheroniConstant 1 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine tendsto_riemannZeta_sub_one_div.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : s - 1 ≠ 0 := sub_ne_zero.2 hs
    rw [slope_def_field, zetaNum_of_ne hs, zetaNum, Function.update_self]
    field_simp
  rw [num, logDeriv_apply, h.deriv]
  simp [zetaNum]

lemma analyticAt_linear (s : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (1 + (Real.eulerMascheroniConstant : ℂ)) * s - 1) s := by fun_prop

lemma analyticAt_num {s : ℂ} (h : riemannZeta s ≠ 0) : AnalyticAt ℂ num s := by
  have h1 := differentiable_zetaNum.analyticAt s
  exact (analyticAt_linear s).sub (h1.deriv.div h1 (zetaNum_ne_zero h))

lemma continuation_of_ne {s : ℂ} (hs : s ≠ 1) : continuation s = -(num s / (s * (s - 1))) := by
  rw [continuation, dslope_of_ne _ hs, slope_def_field, num_one, sub_zero, div_div, mul_comm s]

lemma analyticAt_continuation {s : ℂ} (h0 : s ≠ 0) (h : riemannZeta s ≠ 0) :
    AnalyticAt ℂ continuation s := by
  refine (AnalyticAt.div (g := fun s : ℂ => s) ?_ analyticAt_id h0).fun_neg
  rcases eq_or_ne s 1 with rfl | hs1
  · exact analyticAt_dslope_self (analyticAt_num h)
  · refine (((analyticAt_num h).sub analyticAt_const).div (by fun_prop)
      (sub_ne_zero.2 hs1) : AnalyticAt ℂ (fun z => (num z - num 1) / (z - 1)) s).congr ?_
    filter_upwards [eventually_ne_nhds hs1] with z hz
    rw [dslope_of_ne _ hz, slope_def_field]
    rfl

lemma continuation_pole {ρ : ℂ} (h0 : ρ ≠ 0) (h : riemannZeta ρ = 0) :
    ∃ g, AnalyticAt ℂ g ρ ∧ ∀ᶠ s in 𝓝[≠] ρ,
      continuation s = zeroMult ρ / (ρ * (ρ - 1)) / (s - ρ) + g s := by
  have h1 : ρ ≠ 1 := fun e => riemannZeta_one_ne_zero (e ▸ h)
  have hd := differentiable_zetaNum.analyticAt ρ
  obtain ⟨g, hg, hg0, hfac⟩ := hd.analyticOrderAt_eq_natCast.1 (analyticOrderAt_zetaNum ρ)
  have hp : AnalyticAt ℂ (fun s : ℂ => (zeroMult ρ : ℂ) / (s * (s - 1))) ρ :=
    analyticAt_const.div (g := fun s : ℂ => s * (s - 1)) (by fun_prop)
      (mul_ne_zero h0 (sub_ne_zero.2 h1))
  refine ⟨fun s => dslope (fun s : ℂ => (zeroMult ρ : ℂ) / (s * (s - 1))) ρ s -
    ((1 + Real.eulerMascheroniConstant) * s - 1 - logDeriv g s) / (s * (s - 1)),
    (analyticAt_dslope_self hp).sub (((analyticAt_linear ρ).sub (hg.deriv.div hg hg0)).div
      (g := fun s : ℂ => s * (s - 1)) (by fun_prop) (mul_ne_zero h0 (sub_ne_zero.2 h1))), ?_⟩
  filter_upwards [hfac.eventually_nhds.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
    (eventually_ne_nhds h1).filter_mono nhdsWithin_le_nhds,
    (eventually_ne_nhds h0).filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with s hs hne hs1 hs0 hgs hga
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 hne
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hlog : logDeriv zetaNum s = zeroMult ρ / (s - ρ) + logDeriv g s := by
    have : zetaNum =ᶠ[𝓝 s] fun z => (z - ρ) ^ zeroMult ρ * g z := hs
    rw [logDeriv_apply, this.deriv_eq, this.eq_of_nhds, ← logDeriv_apply,
      logDeriv_mul (f := fun z => (z - ρ) ^ zeroMult ρ) s (pow_ne_zero _ hsρ) hgs
        (by fun_prop) hga.differentiableAt,
      logDeriv_fun_pow (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  rw [continuation_of_ne hs1, num, hlog, dslope_of_ne _ hne, slope_def_field]
  field_simp
  ring

/-! ### The criterion -/

/-- `∑ Λ(n) (x / n - 1) ≤ ∑ Λ(n) ⌊x / n⌋ = log ⌊x⌋! ≤ x log x`. -/
lemma sum_sub_mul_log_nonpos {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x ≤ 0 := by
  have hx0 : 0 ≤ x := by linarith
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have e := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum Λ ⌊x⌋₊
  rw [vonMangoldt_mul_zeta] at e
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n * ((⌊x⌋₊ / n : ℕ) : ℝ) := by
    refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
    rw [← Nat.floor_div_natCast]
    linarith [Nat.lt_floor_add_one (x / n)]
  have h2 : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log n ≤ x * Real.log x := by
    refine (Finset.sum_le_card_nsmul _ _ (Real.log x) fun n hn => ?_).trans ?_
    · obtain ⟨h3, h4⟩ := Finset.mem_Ioc.1 hn
      exact Real.log_le_log (by exact_mod_cast h3) ((Nat.cast_le.2 h4).trans hfl)
    · rw [Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hfl (Real.log_nonneg hx)
  simp only [ArithmeticFunction.log_apply] at e
  linarith

lemma abs_windowSum_le {x : ℝ} (hx : 1 ≤ x) : |windowSum x| ≤ 4 * x ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) := Finset.sum_nonneg fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    exact mul_nonneg vonMangoldt_nonneg (sub_nonneg.2 ((one_le_div (by exact_mod_cast h1)).2
      ((Nat.le_floor_iff hx0.le).1 h2)))
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx0) hx0.le
  have hx2 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx (by decide)
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hγ' := mul_le_mul_of_nonneg_right Real.eulerMascheroniConstant_lt_two_thirds.le hx0.le
  have hγ0 := mul_nonneg (by linarith : 0 ≤ Real.eulerMascheroniConstant) hx0.le
  have hx1 := le_self_pow₀ hx (by norm_num : 3 ≠ 0)
  rw [windowSum, abs_le]
  constructor <;> nlinarith [sum_sub_mul_log_nonpos hx]

lemma measurable_windowSum : Measurable fun u : ℝ => windowSum (Real.exp u) := by
  have : Measurable fun u : ℝ => ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, Λ n * (Real.exp u / n - 1) := by
    simp_rw [← fun u => (hasSum_term u).tsum_eq]
    unfold term
    fun_prop
  unfold windowSum
  fun_prop

lemma laplace_windowSum {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun u : ℝ => (windowSum (Real.exp u) : ℂ) * cexp (-(s * u))) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (windowSum (Real.exp u) : ℂ) * cexp (-(s * u)) =
        num s / (s * (s - 1)) := by
  have hs1 : s ≠ 1 := fun e => by norm_num [e] at hs
  have hs0 : s ≠ 0 := fun e => by norm_num [e] at hs
  have h1 : 1 < s.re := by linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1.le
  have hi : IntegrableOn (fun u : ℝ => (windowSum (Real.exp u) : ℂ) * cexp (-(s * u))) (Ioi 0) := by
    simpa using integrable_kernel (A := 4) (c := 3) measurable_windowSum (fun u hu => by
      simpa [← Real.exp_nat_mul] using abs_windowSum_le (Real.one_le_exp hu)) 0 hs
  obtain ⟨i1, v1⟩ := laplace_exp (a := 1) (s := s) (by simpa) 0
  obtain ⟨i2, v2⟩ := laplace_mul_exp h1
  have hS := laplace_sum h1
  have e (u : ℝ) :
      ((∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, Λ n * (Real.exp u / n - 1) : ℝ) : ℂ) * cexp (-(s * u)) =
        windowSum (Real.exp u) * cexp (-(s * u)) + ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u)) -
          (1 + Real.eulerMascheroniConstant) * (cexp (1 * u) * cexp (-(s * u))) := by
    rw [windowSum, Real.log_exp]
    push_cast
    rw [one_mul]
    ring
  have hlog : logDeriv zetaNum s = 1 / (s - 1) + logDeriv riemannZeta s := by
    have : zetaNum =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z :=
      (eventually_ne_nhds hs1).mono fun z hz => zetaNum_of_ne hz
    rw [logDeriv_apply, this.deriv_eq, this.eq_of_nhds, ← logDeriv_apply,
      logDeriv_mul (f := fun z => z - 1) s (sub_ne_zero.2 hs1) hz
        (by fun_prop) (differentiableAt_riemannZeta hs1)]
    simp [logDeriv_apply]
  refine ⟨hi, ?_⟩
  simp only [e] at hS
  rw [integral_sub (by exact hi.add i2) (i1.const_mul _), integral_add hi i2, integral_const_mul,
    v1, v2, ofReal_zero, mul_zero, Complex.exp_zero] at hS
  rw [eq_sub_of_add_eq (eq_add_of_sub_eq hS), num, hlog, logDeriv_apply]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  field_simp
  ring

lemma re_lt_one_of_zero {ρ : ℂ} (h : riemannZeta ρ = 0) : ρ.re < 1 :=
  lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 h

lemma continues {θ : ℝ} (hθ : 0 ≤ θ) :
    Continues (fun u => -windowSum (Real.exp u)) continuation {ρ | θ < ρ.re ∧ riemannZeta ρ = 0}
      (fun ρ => zeroMult ρ / (ρ * (ρ - 1))) 4 3 θ where
  measurable := measurable_windowSum.neg
  growth u hu := by simpa [← Real.exp_nat_mul] using abs_windowSum_le (Real.one_le_exp hu)
  laplace s hs := by
    rw [continuation_of_ne fun e => by norm_num [e] at hs, ← (laplace_windowSum hs).2,
      ← integral_neg]
    congr 1 with u
    push_cast
    ring
  analytic s hs hZ := analyticAt_continuation (ne_zero_of_re_pos (hθ.trans_lt hs))
    fun h => hZ ⟨hs, h⟩
  finite s r := ((isCompact_closedBall s r).inter_riemannZetaZeros_finite).subset
    fun ρ h => ⟨h.2, h.1.2⟩
  re_mem ρ h := ⟨h.1, (re_lt_one_of_zero h.2).le.trans (by norm_num)⟩
  residue_ne_zero ρ h := by
    have h1 : ρ ≠ 1 := fun e => riemannZeta_one_ne_zero (e ▸ h.2)
    have hm : 0 < zeroMult ρ := zeroMult_pos h.2
    exact div_ne_zero (by exact_mod_cast hm.ne')
      (mul_ne_zero (ne_zero_of_re_pos (hθ.trans_lt h.1)) (sub_ne_zero.2 h1))
  pole ρ h := continuation_pole (ne_zero_of_re_pos (hθ.trans_lt h.1)) h.2

/-- The residue at a real zero is negative. -/
lemma residue_re_neg {ρ : ℂ} (hr : 0 < ρ.re) (hz : riemannZeta ρ = 0) (hi : ρ.im = 0) :
    ((zeroMult ρ : ℂ) / (ρ * (ρ - 1))).re < 0 := by
  lift ρ to ℝ using hi
  rw [← ofReal_natCast, ← ofReal_one, ← ofReal_sub, ← ofReal_mul, ← ofReal_div, ofReal_re]
  refine div_neg_of_pos_of_neg (by exact_mod_cast zeroMult_pos hz) (mul_neg_of_pos_of_neg hr ?_)
  exact sub_neg.2 (by simpa using re_lt_one_of_zero hz)

/-- A one-sided power bound `F x ≤ C x ^ θ` on `[Y, Y ^ (1 + δ)]` is, in the variable `u = log x`,
the bound `-F (e ^ u) ≥ -C e ^ (θ u)` on `[log Y, (1 + δ) log Y]`. -/
lemma window_exp {F : ℝ → ℝ} {θ δ C : ℝ}
    (h : ∀ X, ∃ Y ≥ X, ∀ x ∈ Icc Y (Y ^ (1 + δ)), F x ≤ C * x ^ θ) (X : ℝ) :
    ∃ U ≥ X, ∀ u ∈ Icc U ((1 + δ) * U), -(C * Real.exp (θ * u)) ≤ -F (Real.exp u) := by
  obtain ⟨Y, hY, hw⟩ := h (Real.exp X)
  have hY0 : 0 < Y := (Real.exp_pos X).trans_le hY
  refine ⟨Real.log Y, (Real.le_log_iff_exp_le hY0).2 hY, fun u hu => ?_⟩
  have := hw (Real.exp u) ⟨(Real.log_le_iff_le_exp hY0).1 hu.1, by
    rw [Real.rpow_def_of_pos hY0, mul_comm]
    exact Real.exp_le_exp.2 hu.2⟩
  rw [← Real.exp_mul, mul_comm u] at this
  linarith

/-- **Window criterion.** A one-sided power bound with exponent `θ ≥ 0` on arbitrarily late windows
`[Y, Y ^ (1 + δ)]` rules out zeros of zeta to the right of `θ`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_window {θ δ C : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (h : ∀ X, ∃ Y ≥ X, ∀ x ∈ Icc Y (Y ^ (1 + δ)), windowSum x ≤ C * x ^ θ) {ρ : ℂ}
    (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := fun h0 =>
  ((continues hθ).eq_empty_of_window hθ (fun _ hρ hi => residue_re_neg (hθ.trans_lt hρ.1) hρ.2 hi)
    hδ (window_exp h) ▸ ⟨hρ, h0⟩ : ρ ∈ (∅ : Set ℂ)).elim

/-- Absence of zeros of zeta in `Re s > θ` gives the trace identity of `trace_eq_efFunctional_iff`
at every positive width `a > θ - 1 / 2`. -/
theorem trace_eq_efFunctional_of_ne_zero {θ a : ℝ} (ha : 0 < a) (hθa : θ - 1 / 2 < a)
    (h : ∀ z : ℂ, θ < z.re → riemannZeta z ≠ 0) (φ : TestFunction) :
    Trace.HasTrace (Trace.induced ha φ) φ.efFunctional := by
  refine (Trace.trace_eq_efFunctional_iff ha).2 ?_ φ
  rintro ⟨ρ, h0, h1, h2, h3⟩
  rcases le_abs'.1 h3 with h4 | h4
  · refine h (1 - ρ) (by simp; linarith) ?_
    have h5 : 0 < zeroMult (1 - ρ) := zeroMult_one_sub h1 h2 ▸ zeroMult_pos h0
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h5.ne'
  · exact h ρ (by linarith) h0

end Masullo.Window
