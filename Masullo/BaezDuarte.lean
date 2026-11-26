import Masullo.Window

/-!
# Báez-Duarte's natural approximant

For `N ≥ 1` put `g_N = ∑_{k ≤ N} μ(k) / k` and, on `(0, 1]`,
`E_N(x) = 1 + ∑_{k ≤ N} μ(k) {1 / (k x)} - N g_N {1 / (N x)}`, Báez-Duarte's natural approximant
(`approx`). It vanishes on `(1 / N, 1]`, by `∑_{k ≤ u} μ(k) ⌊u / k⌋ = 1` for `u ≥ 1`
(`approx_eq_zero`).

For `0 < α ≤ 1` and `0 < Re s`, `s ≠ 1`, the Mellin transform on `(0, 1]` of `{α / x}` is
`α / (s - 1) - α ^ s ζ(s) / s` (`integral_cpow_mul_fract`). The coefficients `α = 1 / k` of the
fractional parts in `E_N - 1` have `α`-weighted sum `g_N - N g_N / N = 0`, so at every zero `ρ` of
zeta with `0 < Re ρ` the Mellin transform of `E_N` is `1 / ρ`, for every `N`
(`integral_cpow_mul_approx`).

`MellinBound σ C` says that `∫_0^1 |E_N(x)| x ^ (σ - 1) dx ≤ C` for arbitrarily large `N`. For
`σ > 0` it rules out zeros of zeta in `Re s > σ` (`riemannZeta_ne_zero_of_mellinBound`): at a zero
`ρ` with `β = Re ρ > σ`, the weight `x ^ (β - σ)` is at most `N ^ (σ - β)` on the support
`(0, 1 / N]` of `E_N`, so `1 / |ρ| ≤ N ^ (σ - β) C`, which fails for large `N`. The converse is not
formalised; whether absence of zeros in `Re s > θ`, with `θ < 1`, gives the bound for some
`σ < 1` is not checked here.
The hypothesis `σ > 0` makes `|E_N(x)| x ^ (σ - 1)` integrable; without it the integral could take
its junk value `0`. The bound holds at `σ = 1` (`Controls.mellinBound_one`), where the criterion
says nothing; it is not proved here for any `σ < 1`.

OpenAI Codex proposed this form, after Báez-Duarte; Claude formalised it.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ArithmeticFunction.Moebius

namespace Masullo.BaezDuarte

/-- `g_N = ∑_{k ≤ N} μ(k) / k`. -/
noncomputable def mobiusSum (N : ℕ) : ℝ := ∑ k ∈ Finset.Ioc 0 N, (μ k : ℝ) / k

/-- Báez-Duarte's natural approximant
`E_N(x) = 1 + ∑_{k ≤ N} μ(k) {1 / (k x)} - N g_N {1 / (N x)}`. -/
noncomputable def approx (N : ℕ) (x : ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.Ioc 0 N, (μ k : ℝ) * Int.fract (1 / (k * x)) -
    N * mobiusSum N * Int.fract (1 / (N * x))

/-! ### Vanishing on `(1 / N, 1]` -/

/-- `∑_{k ≤ M} μ(k) ⌊M / k⌋ = 1` for `M ≥ 1`. -/
lemma sum_moebius_mul_div {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Ioc 0 M, (μ k : ℤ) * ((M / k : ℕ) : ℤ) = 1 := by
  rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum, ArithmeticFunction.moebius_mul_coe_zeta]
  simp only [ArithmeticFunction.one_apply]
  rw [Finset.sum_ite_eq' (Finset.Ioc 0 M) 1, if_pos (Finset.mem_Ioc.2 ⟨one_pos, hM⟩)]

/-- `∑_{k ≤ M} μ(k) ⌊M / k⌋ = 1` in `ℝ`, for `M ≥ 1`. -/
lemma sum_moebius_mul_div_real {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Ioc 0 M, (μ k : ℝ) * ((M / k : ℕ) : ℝ) = 1 := by
  have := congrArg (Int.cast : ℤ → ℝ) (sum_moebius_mul_div hM)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_one] using this

private lemma one_div_mul (k x : ℝ) : 1 / (k * x) = 1 / x / k := by
  rw [div_div, mul_comm]

/-- `E_N` vanishes on `(1 / N, 1]`. -/
theorem approx_eq_zero {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 1 / N < x) (hx1 : x ≤ 1) :
    approx N x = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := (by positivity : (0 : ℝ) < 1 / N).trans hx
  set u := 1 / x with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hx0]; linarith
  have huN : u < N := by
    rw [hu, div_lt_iff₀ hx0]
    rwa [div_lt_iff₀ hN', mul_comm] at hx
  set M := ⌊u⌋₊
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using hu1)
  have hMN : M ≤ N := ((Nat.floor_lt (by linarith)).2 huN).le
  have hk : ∀ k ∈ Finset.Ioc 0 N, (μ k : ℝ) * Int.fract (1 / (k * x)) =
      u * ((μ k : ℝ) / k) - (μ k : ℝ) * ((M / k : ℕ) : ℝ) := by
    intro k _
    rw [one_div_mul, ← hu, Int.fract, ← Int.natCast_floor_eq_floor (by positivity),
      Nat.floor_div_natCast, Int.cast_natCast]
    ring
  have hNx : Int.fract (1 / (N * x)) = u / N := by
    rw [one_div_mul, ← hu]
    exact Int.fract_eq_self.2 ⟨by positivity, (div_lt_one hN').2 huN⟩
  have hsum : ∑ k ∈ Finset.Ioc 0 N, (μ k : ℝ) * ((M / k : ℕ) : ℝ) = 1 := by
    rw [← Finset.sum_subset (Finset.Ioc_subset_Ioc_right hMN)]
    · exact sum_moebius_mul_div_real hM1
    · intro k hk hkM
      simp only [Finset.mem_Ioc, not_and, not_le] at hk hkM
      rw [Nat.div_eq_of_lt (hkM hk.1), Nat.cast_zero, mul_zero]
  rw [approx, Finset.sum_congr rfl hk, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hNx,
    ← mobiusSum]
  field_simp
  ring

/-! ### The Mellin transform -/

private lemma integrableOn_cpow_mul_fract {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (-s - 1) * ((Int.fract y : ℝ) : ℂ)) (Ioi a) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha).mono'
  · exact (Measurable.mul (by fun_prop : Measurable fun y : ℝ => (y : ℂ) ^ (-s - 1))
      (Complex.measurable_ofReal.comp measurable_fract)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := ha.trans hy
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, sub_re, neg_re, one_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg y)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hy0.le _) (Int.fract_lt_one y).le

private lemma integrableOn_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    (intervalIntegral.intervalIntegrable_cpow' (by simpa using hs))

/-- `∫_0^1 x ^ (s - 1) dx = 1 / s` for `0 < Re s`. -/
private lemma integral_Ioc_cpow {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) = 1 / s := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (.inl (by simpa)),
    sub_add_cancel, ofReal_zero, zero_cpow (ne_zero_of_re_pos hs)]
  simp

private lemma integrableOn_cpow_mul_fract' {s : ℂ} (hs : 0 < s.re) (α : ℝ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * ((Int.fract (α / x) : ℝ) : ℂ))
      (Ioc 0 1) := by
  refine (integrableOn_cpow hs).norm.mono' ?_ ?_
  · exact (Measurable.mul (by fun_prop : Measurable fun x : ℝ => (x : ℂ) ^ (s - 1))
      (Complex.measurable_ofReal.comp (measurable_fract.comp
        (measurable_const.div measurable_id)))).aestronglyMeasurable
  · refine .of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Int.fract_lt_one _).le

/-- The Mellin transform on `(0, 1]` of `{α / x}`, for `0 < α ≤ 1`, is
`α / (s - 1) - α ^ s ζ(s) / s` on `Re s > 0`, `s ≠ 1`. -/
theorem integral_cpow_mul_fract {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) * ((Int.fract (α / x) : ℝ) : ℂ) =
      α / (s - 1) - (α : ℂ) ^ s * riemannZeta s / s := by
  set H : ℝ → ℂ := (Ici α).indicator fun y => ((Int.fract y : ℝ) : ℂ)
  have h1 : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) * ((Int.fract (α / x) : ℝ) : ℂ) =
      mellin (fun x => (fun t => H t⁻¹) (α⁻¹ * x)) s := by
    rw [mellin, ← Ioi_inter_Iic, inter_comm, ← Measure.restrict_restrict measurableSet_Iic,
      ← integral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    have e : (α⁻¹ * x)⁻¹ = α / x := by field_simp
    simp only [H, e, smul_eq_mul, indicator_apply, mem_Ici, mem_Iic,
      le_div_iff₀ hx0, mul_le_iff_le_one_right hα]
    split_ifs <;> simp
  have h2 : mellin H (-s) = ∫ y in Ioi α, (y : ℂ) ^ (-s - 1) * ((Int.fract y : ℝ) : ℂ) := by
    simp only [mellin, H, smul_eq_mul, ← indicator_mul_right (Ici α)
      (fun y : ℝ => (y : ℂ) ^ (-s - 1))]
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.2 (Ici_subset_Ioi.2 hα), integral_Ici_eq_integral_Ioi]
  have h3 : ∫ y in α..1, (y : ℂ) ^ (-s - 1) * ((Int.fract y : ℝ) : ℂ) =
      (1 - (α : ℂ) ^ (-s + 1)) / (-s + 1) := by
    rw [intervalIntegral.integral_congr_ae (g := fun y : ℝ => (y : ℂ) ^ (-s)) ?_,
      integral_cpow (.inr ⟨fun h => hs1 (by linear_combination -h), ?_⟩)]
    · simp
    · rw [mem_uIcc]
      rintro (⟨h, -⟩ | ⟨h, -⟩) <;> linarith
    · filter_upwards [compl_mem_ae_iff.2 (measure_singleton (1 : ℝ))] with y hy1 hy
      rw [uIoc_of_le hα1] at hy
      have hy0 : 0 < y := hα.trans hy.1
      rw [Int.fract_eq_self.2 ⟨hy0.le, lt_of_le_of_ne hy.2 hy1⟩]
      conv_rhs => rw [← sub_add_cancel (-s) 1, cpow_add _ _ (ofReal_ne_zero.2 hy0.ne'), cpow_one]
  have hpow : ((α⁻¹ : ℝ) : ℂ) ^ (-s) = (α : ℂ) ^ s := by
    rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hα.le]; exact Real.pi_pos.ne),
      cpow_neg, inv_inv]
  have hpow' : (α : ℂ) ^ s * (α : ℂ) ^ (-s + 1) = α := by
    rw [← cpow_add _ _ (ofReal_ne_zero.2 hα.ne')]
    simp
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hs1'' : -s + 1 ≠ 0 := fun h => hs1' (by linear_combination -h)
  rw [h1, mellin_comp_mul_left (fun t => H t⁻¹) s (inv_pos.2 hα), mellin_comp_inv, h2, hpow,
    ← intervalIntegral.integral_interval_add_Ioi (integrableOn_cpow_mul_fract hα hs)
      (integrableOn_cpow_mul_fract one_pos hs), h3,
    WeilExplicit.zeta_eq_fractional_part_integral hs hs1, smul_eq_mul, mul_add, mul_div_assoc',
    mul_sub, mul_one, hpow']
  field_simp
  ring

/-- At a zero `ρ` of zeta with `0 < Re ρ`, the Mellin transform on `(0, 1]` of `E_N` is `1 / ρ`,
for every `N ≥ 1`. -/
theorem integral_cpow_mul_approx {N : ℕ} (hN : 0 < N) {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (h0 : riemannZeta ρ = 0) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * (approx N x : ℂ) = 1 / ρ := by
  set F : ℝ → ℝ → ℂ := fun α x => (x : ℂ) ^ (ρ - 1) * ((Int.fract (α / x) : ℝ) : ℂ)
  have e : (fun x : ℝ => (x : ℂ) ^ (ρ - 1) * (approx N x : ℂ)) = fun x : ℝ =>
      (x : ℂ) ^ (ρ - 1) + ∑ k ∈ Finset.Ioc 0 N, (μ k : ℂ) * F (k : ℝ)⁻¹ x -
        (N : ℂ) * (mobiusSum N : ℂ) * F (N : ℝ)⁻¹ x := by
    ext x
    have hkx : ∀ k : ℝ, 1 / (k * x) = k⁻¹ / x := fun k => by
      rw [one_div, mul_inv, div_eq_mul_inv]
    simp only [approx, F, hkx]
    push_cast
    rw [mul_sub, mul_add, mul_one, Finset.mul_sum]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
    · ring
  have hF : ∀ k : ℕ, 0 < k → ∫ x in Ioc (0 : ℝ) 1, F (k : ℝ)⁻¹ x = ((k : ℝ)⁻¹ : ℂ) / (ρ - 1) := by
    intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [integral_cpow_mul_fract (by positivity) (inv_le_one_of_one_le₀ hk') hρ hρ1, h0]
    simp
  rw [e, integral_sub, integral_add, integral_finsetSum, integral_Ioc_cpow hρ, integral_const_mul,
    hF N hN, Finset.sum_congr rfl fun k hk => by
      rw [integral_const_mul, hF k (Finset.mem_Ioc.1 hk).1]]
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
    simp only [mobiusSum]
    push_cast
    rw [show ∑ k ∈ Finset.Ioc 0 N, (μ k : ℂ) * (((k : ℂ))⁻¹ / (ρ - 1)) =
        (∑ k ∈ Finset.Ioc 0 N, (μ k : ℂ) / k) / (ρ - 1) by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring]
    field_simp
    ring
  · exact fun k _ => (integrableOn_cpow_mul_fract' hρ _).const_mul _
  · exact integrableOn_cpow hρ
  · exact integrable_finsetSum _ fun k _ => (integrableOn_cpow_mul_fract' hρ _).const_mul _
  · exact (integrableOn_cpow hρ).add
      (integrable_finsetSum _ fun k _ => (integrableOn_cpow_mul_fract' hρ _).const_mul _)
  · exact (integrableOn_cpow_mul_fract' hρ _).const_mul _

/-! ### The criterion -/

lemma measurable_approx (N : ℕ) : Measurable (approx N) := by
  unfold approx
  refine (measurable_const.add (Finset.measurable_sum _ fun k _ => ?_)).sub ?_
  · exact (measurable_fract.comp (by fun_prop)).const_mul _
  · exact (measurable_fract.comp (by fun_prop)).const_mul _

/-- `|E_N|` is bounded by `1 + N + N |g_N|`. -/
lemma abs_approx_le (N : ℕ) (x : ℝ) : |approx N x| ≤ 1 + N + N * |mobiusSum N| := by
  have hf : ∀ y : ℝ, |Int.fract y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (Int.fract_nonneg y)]; exact (Int.fract_lt_one y).le
  have hs : |∑ k ∈ Finset.Ioc 0 N, (μ k : ℝ) * Int.fract (1 / (k * x))| ≤ N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun k _ => ?_).trans (by simp)
    rw [abs_mul]
    exact mul_le_one₀ (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one) (abs_nonneg _)
      (hf _)
  have hl : |(N : ℝ) * mobiusSum N * Int.fract (1 / (N * x))| ≤ N * |mobiusSum N| := by
    rw [abs_mul, abs_mul, Nat.abs_cast]
    exact mul_le_of_le_one_right (by positivity) (hf _)
  unfold approx
  refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) hl)
  rw [abs_one]
  linarith

lemma integrableOn_abs_approx {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    IntegrableOn (fun x => |approx N x| * x ^ (σ - 1)) (Ioc 0 1) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (σ - 1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine (hp.const_mul (1 + N + N * |mobiusSum N|)).mono' ?_ ?_
  · exact ((measurable_approx N).abs.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    exact mul_le_mul_of_nonneg_right (abs_approx_le N x) (Real.rpow_nonneg hx.1.le _)

/-- For arbitrarily large `N`, `∫_0^1 |E_N(x)| x ^ (σ - 1) dx ≤ C`. -/
def MellinBound (σ C : ℝ) : Prop :=
  ∀ M : ℕ, ∃ N ≥ M, ∫ x in Ioc (0 : ℝ) 1, |approx N x| * x ^ (σ - 1) ≤ C

/-- `MellinBound` is monotone in `σ` on `σ > 0`: `x ^ (σ' - 1) ≤ x ^ (σ - 1)` on `(0, 1]`. -/
theorem MellinBound.mono {σ σ' C : ℝ} (hσ : 0 < σ) (h : σ ≤ σ') (hb : MellinBound σ C) :
    MellinBound σ' C := by
  intro M
  obtain ⟨N, hN, hI⟩ := hb M
  refine ⟨N, hN, le_trans ?_ hI⟩
  refine setIntegral_mono_on (integrableOn_abs_approx (hσ.trans_le h) N)
    (integrableOn_abs_approx hσ N) measurableSet_Ioc fun x hx => ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)) (abs_nonneg _)

/-- `MellinBound σ C` with `σ > 0` rules out zeros of zeta to the right of `σ`. The converse is
not asserted. -/
theorem riemannZeta_ne_zero_of_mellinBound {σ C : ℝ} (hσ : 0 < σ) (h : MellinBound σ C)
    {ρ : ℂ} (hρ : σ < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro h0
  have hρ1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero h0
  have hρ0 : 0 < ρ.re := hσ.trans hρ
  have hpos : 0 < ‖ρ‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (ne_zero_of_re_pos hρ0))
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (σ - ρ.re) * C) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < ρ.re - σ)).comp
      tendsto_natCast_atTop_atTop).mul_const C
    simpa using this
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 _ hpos)
  obtain ⟨N, hN, hb⟩ := h (max M 1)
  have hN1 : 0 < N := le_of_max_le_right hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  refine (hM N (le_of_max_le_left hN)).not_ge ?_
  calc ‖ρ‖⁻¹ = ‖∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * (approx N x : ℂ)‖ := by
        rw [integral_cpow_mul_approx hN1 hρ0 hρ1 h0, norm_div, norm_one, one_div]
    _ ≤ ∫ x in Ioc (0 : ℝ) 1, ‖(x : ℂ) ^ (ρ - 1) * (approx N x : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioc (0 : ℝ) 1, (N : ℝ) ^ (σ - ρ.re) * (|approx N x| * x ^ (σ - 1)) := by
        refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _)
          ((integrableOn_abs_approx hσ N).const_mul _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, sub_re, one_re, Complex.norm_real,
          Real.norm_eq_abs]
        rcases le_or_gt x (1 / N) with hxN | hxN
        · have e : x ^ (ρ.re - 1) = x ^ (ρ.re - σ) * x ^ (σ - 1) := by
            rw [← Real.rpow_add hx.1]; ring_nf
          have hle : x ^ (ρ.re - σ) ≤ (N : ℝ) ^ (σ - ρ.re) := by
            rw [show σ - ρ.re = -(ρ.re - σ) by ring, Real.rpow_neg hN'.le,
              ← Real.inv_rpow hN'.le, ← one_div]
            exact Real.rpow_le_rpow hx.1.le hxN (by linarith)
          rw [e]
          have := mul_le_mul_of_nonneg_right hle
            (mul_nonneg (abs_nonneg (approx N x)) (Real.rpow_nonneg hx.1.le (σ - 1)))
          linarith
        · rw [approx_eq_zero hN1 hxN hx.2]
          simp
    _ = (N : ℝ) ^ (σ - ρ.re) * ∫ x in Ioc (0 : ℝ) 1, |approx N x| * x ^ (σ - 1) :=
        integral_const_mul _ _
    _ ≤ (N : ℝ) ^ (σ - ρ.re) * C := mul_le_mul_of_nonneg_left hb (by positivity)

/-- `MellinBound σ C` with `0 < σ < 1 / 2 + a` gives the trace identity of
`trace_eq_efFunctional_iff` at width `a`. The converse is not asserted. -/
theorem trace_eq_efFunctional_of_mellinBound {σ C a : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hσa : σ - 1 / 2 < a) (h : MellinBound σ C) (φ : TestFunction) :
    Trace.HasTrace (Trace.induced ha φ) φ.efFunctional :=
  Window.trace_eq_efFunctional_of_ne_zero ha hσa
    (fun _ => riemannZeta_ne_zero_of_mellinBound hσ h) φ

end Masullo.BaezDuarte
