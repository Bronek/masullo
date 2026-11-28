import Masullo.QRH.MeanSquare.KernelSeparation
import Masullo.QRH.MeanSquare.Majorant

/-! # The first-Poisson kernel in logarithmic coordinates

After the first Poisson step the bilinear form in the columns `x₁, x₂` has kernel
`W₁(x₁) conj W₂(x₂) (x₁x₂)^{-1/2} T(√(A/(x₁x₂)))` with `T = gaoZhaoTransform P` and a
row-dependent scale `A > 0`. In the variable `s = log x₁ + log x₂` this is
`ψ_A(s) = e^{-s/2} T(√A e^{-s/2})`, cut off smoothly outside the range of `s` on `I × I`.

If `T` vanishes on `[1, ∞)`, then `T(√A e^{-s/2})` is the translate by `log A` of the fixed
function `σ ↦ T(e^{-σ/2})`, which vanishes for `σ ≤ 0` and has bounded derivatives. So the
`L¹` norms of the derivatives of `ψ_A` are bounded uniformly in `A`
(`exists_transferKernel_bounds`), and `exists_transferSeparated_le` separates the kernel.
-/

noncomputable section

open MeasureTheory Set Function Filter
open scoped ComplexConjugate Nat ContDiff Topology SchwartzMap

namespace Masullo.QRH.MeanSquare

/-- The radial transform `gaoZhaoTransform P`, as a function of a real frequency, is a
Schwartz function. -/
theorem exists_schwartz_eq_gaoZhaoTransform (P : 𝓢(ℝ, ℂ)) :
    ∃ S : 𝓢(ℝ, ℂ), ∀ t, S t = gaoZhaoTransform P t := by
  have h3 : (0 : ℝ) < √3 := by positivity
  set a : ℝ := 2 / √3
  have ha : 1 ≤ a := by
    rw [le_div_iff₀ h3, one_mul]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  set g : ℝ →L[ℝ] ℂ := a • Complex.ofRealCLM
  have hg : ∀ t, g t = ((a * t : ℝ) : ℂ) := fun t => by
    simp [g, Complex.ofRealCLM_apply]
  set F : 𝓢(ℂ, ℂ) := FourierTransform.fourier (radialSchwartz P one_pos)
  refine ⟨(a : ℂ) • SchwartzMap.compCLM ℝ (g := g) g.hasTemperateGrowth
    ⟨1, 1, fun t => ?_⟩ F, fun t => ?_⟩
  · rw [hg, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < a), pow_one, one_mul]
    nlinarith [abs_nonneg t]
  · rw [smul_apply, SchwartzMap.compCLM_apply, comp_apply, hg, smul_eq_mul]
    have h := fourier_radialSchwartz P one_pos ((a * t : ℝ) : ℂ)
    have hn : √1 * ‖((a * t : ℝ) : ℂ)‖ * (√3 / 2) = |t| := by
      rw [Real.sqrt_one, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < a)]
      simp only [a]
      field_simp
    have habs : gaoZhaoTransform P |t| = gaoZhaoTransform P t := by
      rcases le_total 0 t with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_nonpos h0, Majorant.gaoZhaoTransform_neg]
    rw [hn, habs] at h
    change (a : ℂ) * F _ = _
    rw [h, Complex.ofReal_one, one_mul, ← mul_assoc]
    have : (a : ℂ) * ((√3 : ℝ) / 2 : ℂ) = 1 := by
      simp only [a]
      push_cast
      field_simp
    rw [this, one_mul]

private lemma iteratedDeriv_exp_const_mul (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun σ : ℝ => Real.exp (c * σ)) = fun σ => c ^ n * Real.exp (c * σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext σ
    have h : HasDerivAt (fun σ : ℝ => Real.exp (c * σ)) (Real.exp (c * σ) * (c * 1)) σ :=
      ((hasDerivAt_id σ).const_mul c).exp
    rw [deriv_const_mul _ h.differentiableAt, h.deriv]
    ring

/-- `σ ↦ S(e^{-σ/2})`: the kernel profile before translation by `log A`. -/
def logProfile (S : 𝓢(ℝ, ℂ)) (σ : ℝ) : ℂ := S (Real.exp (-(1 / 2) * σ))

lemma contDiff_logProfile (S : 𝓢(ℝ, ℂ)) : ContDiff ℝ ∞ (logProfile S) :=
  (S.smooth ⊤).comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

/-- If `S` vanishes on `[1, ∞)`, then `σ ↦ S(e^{-σ/2})` has bounded derivatives. -/
lemma exists_norm_iteratedFDeriv_logProfile_le (S : 𝓢(ℝ, ℂ)) (hS : ∀ t, 1 ≤ t → S t = 0)
    (n : ℕ) : ∃ B ≥ (0 : ℝ), ∀ i ≤ n, ∀ σ, ‖iteratedFDeriv ℝ i (logProfile S) σ‖ ≤ B := by
  set CS : ℝ := ∑ i ∈ Finset.range (n + 1), SchwartzMap.seminorm ℝ 0 i S
  have hCS : 0 ≤ CS := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  refine ⟨n ! * CS * 3 ^ n, by positivity, fun i hi σ => ?_⟩
  rcases lt_or_ge σ 0 with hσ | hσ
  · have h0 : logProfile S =ᶠ[𝓝 σ] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hσ] with τ hτ
      refine hS _ ?_
      exact Real.one_le_exp (by nlinarith [mem_Iio.1 hτ])
    rw [(h0.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity
  · set U : Set ℝ := Ioi (-1)
    have hσU : σ ∈ U := mem_Ioi.2 (by linarith)
    set f : ℝ → ℝ := fun σ => Real.exp (-(1 / 2) * σ)
    have hf : ContDiff ℝ ∞ f := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    rw [← iteratedFDerivWithin_of_isOpen i isOpen_Ioi hσU]
    have h := norm_iteratedFDerivWithin_comp_le (g := ⇑S) (f := f) (t := univ) (s := U) (n := i)
      (N := ∞) (S.smooth ⊤).contDiffOn hf.contDiffOn (by exact_mod_cast le_top)
      uniqueDiffOn_univ isOpen_Ioi.uniqueDiffOn (mapsTo_univ _ _) hσU (C := CS) (D := 3)
      (fun k hk => by
        rw [iteratedFDerivWithin_univ]
        exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ S k _).trans
          (Finset.single_le_sum (f := fun i => SchwartzMap.seminorm ℝ 0 i S)
            (fun _ _ => apply_nonneg _ _) (Finset.mem_range.2 (by omega))))
      (fun k hk _ => by
        rw [iteratedFDerivWithin_of_isOpen k isOpen_Ioi hσU,
          norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul, norm_mul,
          norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h1 : |(-(1 / 2) : ℝ)| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (by norm_num [abs_of_pos])
        have h2 : Real.exp (-(1 / 2) * σ) ≤ 3 := by
          have := Real.exp_one_lt_d9
          have h3 : Real.exp (-(1 / 2) * σ) ≤ Real.exp 1 :=
            Real.exp_le_exp.2 (by nlinarith [mem_Ioi.1 hσU])
          linarith
        calc |(-(1 / 2) : ℝ)| ^ k * Real.exp (-(1 / 2) * σ) ≤ 1 * 3 :=
              mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
          _ = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk)
    refine h.trans ?_
    have : (i ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le hi
    have h3 : (3 : ℝ) ^ i ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hi
    gcongr

lemma log_lo_le_log_hi (I : TestInterval) : Real.log I.lo ≤ Real.log I.hi :=
  Real.log_le_log I.pos I.ordered

/-- A smooth cutoff equal to `1` at `log x₁ + log x₂` for all `x₁, x₂ ∈ I`. -/
def logCutoff (I : TestInterval) : ContDiffBump (Real.log I.lo + Real.log I.hi) :=
  ⟨Real.log I.hi - Real.log I.lo + 1, Real.log I.hi - Real.log I.lo + 2,
    by linarith [log_lo_le_log_hi I], by linarith⟩

/-- The weight `χ(s) e^{-s/2}`. -/
def logWeight (I : TestInterval) (s : ℝ) : ℂ :=
  ((logCutoff I s * Real.exp (-(1 / 2) * s) : ℝ) : ℂ)

lemma contDiff_logWeight (I : TestInterval) : ContDiff ℝ ∞ (logWeight I) :=
  Complex.ofRealCLM.contDiff.comp ((logCutoff I).contDiff.mul
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))

lemma hasCompactSupport_logWeight (I : TestInterval) : HasCompactSupport (logWeight I) :=
  (logCutoff I).hasCompactSupport.mono' fun s hs => subset_tsupport _ fun h =>
    hs (by simp [logWeight, h])

/-- The kernel `ψ_A(s) = χ(s) e^{-s/2} S(√A e^{-s/2})`, written for all real `A` through
`log A`; for `A > 0` it is the first-Poisson kernel (`transferKernel_log_add`). -/
def transferKernel (I : TestInterval) (S : 𝓢(ℝ, ℂ)) (A s : ℝ) : ℂ :=
  logWeight I s * logProfile S (s - Real.log A)

private lemma sqrt_eq_exp {y : ℝ} (hy : 0 < y) : √y = Real.exp (1 / 2 * Real.log y) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, mul_comm]

/-- On `I × I` the kernel is `(x₁x₂)^{-1/2} S(√(A/(x₁x₂)))`. -/
lemma transferKernel_log_add (I : TestInterval) (S : 𝓢(ℝ, ℂ)) {A x₁ x₂ : ℝ} (hA : 0 < A)
    (h₁ : x₁ ∈ Icc I.lo I.hi) (h₂ : x₂ ∈ Icc I.lo I.hi) :
    transferKernel I S A (Real.log x₁ + Real.log x₂) =
      (((√(x₁ * x₂))⁻¹ : ℝ) : ℂ) * S (√(A / (x₁ * x₂))) := by
  have hx₁ : 0 < x₁ := I.pos.trans_le h₁.1
  have hx₂ : 0 < x₂ := I.pos.trans_le h₂.1
  have l₁ := Real.log_le_log I.pos h₁.1
  have l₁' := Real.log_le_log hx₁ h₁.2
  have l₂ := Real.log_le_log I.pos h₂.1
  have l₂' := Real.log_le_log hx₂ h₂.2
  have hχ : logCutoff I (Real.log x₁ + Real.log x₂) = 1 := by
    refine (logCutoff I).one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have hr : (logCutoff I).rIn = Real.log I.hi - Real.log I.lo + 1 := rfl
    rw [hr]
    constructor <;> linarith
  have hmul : Real.log (x₁ * x₂) = Real.log x₁ + Real.log x₂ :=
    Real.log_mul hx₁.ne' hx₂.ne'
  rw [transferKernel, logWeight, logProfile, hχ, one_mul, sqrt_eq_exp (by positivity),
    sqrt_eq_exp (by positivity), ← Real.exp_neg, Real.log_div hA.ne' (by positivity), hmul]
  congr 3 <;> ring

private lemma exists_bound_forall_le {f : ℕ → ℝ → ℝ} (n : ℕ)
    (h : ∀ i ≤ n, ∃ C, ∀ s, f i s ≤ C) : ∃ C ≥ (0 : ℝ), ∀ i ≤ n, ∀ s, f i s ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := h 0 le_rfl
    exact ⟨max C 0, le_max_right _ _, fun i hi s => by
      obtain rfl := Nat.le_zero.1 hi; exact (hC s).trans (le_max_left _ _)⟩
  | succ n ih =>
    obtain ⟨C, hC0, hC⟩ := ih fun i hi => h i (hi.trans n.le_succ)
    obtain ⟨C', hC'⟩ := h (n + 1) le_rfl
    refine ⟨max C C', hC0.trans (le_max_left _ _), fun i hi s => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
    · exact (hC i (Nat.lt_succ_iff.1 hi') s).trans (le_max_left _ _)
    · obtain rfl := le_antisymm hi hi'; exact (hC' s).trans (le_max_right _ _)

/-- If `S` vanishes on `[1, ∞)`, the kernels `ψ_A` are smooth and the `L¹` norms of their
first `n` derivatives are bounded uniformly in `A`. -/
theorem exists_transferKernel_bounds (I : TestInterval) (S : 𝓢(ℝ, ℂ))
    (hS : ∀ t, 1 ≤ t → S t = 0) (n : ℕ) : ∃ B ≥ (0 : ℝ), ∀ A : ℝ,
      ContDiff ℝ ∞ (transferKernel I S A) ∧ ∀ k ≤ n,
        Integrable (iteratedDeriv k (transferKernel I S A)) ∧
          ∫ s, ‖iteratedDeriv k (transferKernel I S A) s‖ ≤ B := by
  have hw := contDiff_logWeight I
  have hwc := hasCompactSupport_logWeight I
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_bound_forall_le (f := fun i s =>
      ‖iteratedFDeriv ℝ i (logWeight I) s‖) n fun i _ =>
    (hw.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hwc.iteratedFDeriv i)
  obtain ⟨BG, hBG0, hBG⟩ := exists_norm_iteratedFDeriv_logProfile_le S hS n
  set K := tsupport (logWeight I)
  set Mb : ℝ := 2 ^ n * Φ * BG
  refine ⟨Mb * volume.real K, by positivity, fun A => ?_⟩
  have hG : ContDiff ℝ ∞ fun s => logProfile S (s - Real.log A) :=
    (contDiff_logProfile S).comp (contDiff_id.sub contDiff_const)
  have hψ : ContDiff ℝ ∞ (transferKernel I S A) := hw.mul hG
  refine ⟨hψ, fun k hk => ?_⟩
  have hpt : ∀ s, ‖iteratedDeriv k (transferKernel I S A) s‖ ≤ Mb := by
    intro s
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    refine (norm_iteratedFDeriv_mul_le hw hG s (by exact_mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (logWeight I) s‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun s => logProfile S (s - Real.log A)) s‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ * BG := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [iteratedFDeriv_comp_sub]
          gcongr
          · exact hΦ i (hi'.trans hk) s
          · exact hBG _ (by omega) _
      _ = 2 ^ k * Φ * BG := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose k
      _ ≤ Mb := by
          simp only [Mb]
          gcongr
          · norm_num
  have hzero : ∀ s, s ∉ K → iteratedDeriv k (transferKernel I S A) s = 0 := by
    intro s hs
    rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_eq_zero]
    by_contra h
    exact hs (tsupport_mul_subset_left (support_iteratedFDeriv_subset k h))
  have hsupp : HasCompactSupport (iteratedDeriv k (transferKernel I S A)) :=
    hwc.mono' fun s hs => by_contra fun h => hs (hzero s h)
  refine ⟨(hψ.continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    hsupp, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun s hs => by
    rw [hzero s hs, norm_zero]]
  refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const
    hwc.isCompact.measure_lt_top fun s _ => ?_)
  rw [norm_norm]
  exact hpt s

/-- Separation of the first-Poisson kernel `(x₁x₂)^{-1/2} T(√(A_ρ/(x₁x₂)))`, with
`T = gaoZhaoTransform P` vanishing on `[1, ∞)` and a scale `A_ρ > 0` for each row. The
constant depends only on `I`, `j` and `P`, not on the scales. -/
theorem exists_transferSeparated_le (I : TestInterval) (j : ℕ) (P : 𝓢(ℝ, ℂ))
    (hP : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0) : ∃ C ≥ (0 : ℝ),
    ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c : R → N → ℂ) (x : N → ℝ)
      (W₁ W₂ : ℝ → ℂ) (A : R → ℝ) {M : ℝ}, 0 ≤ M →
      UnitTest I j W₁ → UnitTest I j W₂ → (∀ ρ ∈ rows, 0 < A ρ) →
      (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * U (x n)‖ ^ 2 ≤ M) →
      ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
        (W₁ (x n₁) * conj (W₂ (x n₂)) *
          ((((√(x n₁ * x n₂))⁻¹ : ℝ) : ℂ) * gaoZhaoTransform P (√(A ρ / (x n₁ * x n₂)))))‖ ≤ C *
          M := by
  obtain ⟨S, hSeq⟩ := exists_schwartz_eq_gaoZhaoTransform P
  have hS : ∀ t, 1 ≤ t → S t = 0 := fun t ht => by rw [hSeq, hP t ht]
  obtain ⟨B, hB0, hB⟩ := exists_transferKernel_bounds I S hS (2 * j + 2)
  obtain ⟨C, hC0, hC⟩ := exists_separated_le I j
  refine ⟨C * B, by positivity, ?_⟩
  intro R N rows cols c x W₁ W₂ A M hM hW₁ hW₂ hA hU
  have key := hC rows cols c x W₁ W₂ (fun ρ => transferKernel I S (A ρ)) hB0 hM hW₁ hW₂ hU
    (fun ρ _ => (hB (A ρ)).1.of_le (WithTop.coe_le_coe.2 le_top))
    (fun ρ _ k hk => ((hB (A ρ)).2 k hk).1)
    (fun ρ _ => by simpa using ((hB (A ρ)).2 0 (Nat.zero_le _)).2)
    (fun ρ _ => ((hB (A ρ)).2 _ le_rfl).2)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun ρ hρ => ?_) key
  congr 1
  refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
  by_cases h₁ : W₁ (x n₁) = 0
  · simp [h₁]
  by_cases h₂ : W₂ (x n₂) = 0
  · simp [h₂]
  rw [transferKernel_log_add I S (hA ρ hρ) (hW₁.2.1 (subset_tsupport _ h₁))
    (hW₂.2.1 (subset_tsupport _ h₂)), hSeq]

end Masullo.QRH.MeanSquare
