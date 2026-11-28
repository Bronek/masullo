import Masullo.QRH.MeanSquare.CosetPoisson

/-! # Logarithmic derivatives of the dual kernel

A Schwartz function restricted to a ray, `r ↦ f(eʳ v)`, has all its derivatives bounded
on `ℝ`: the derivative in `r` is the Euler operator `x ↦ Df(x) x`, which preserves the
Schwartz space. Applied to the Fourier transform of a radial Schwartz function, this bounds
every derivative of `r ↦ gaoZhaoTransform P (eʳ)` uniformly, as the separation of the dual
kernel requires.
-/

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff

namespace Masullo.QRH.MeanSquare

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Euler operator `x ↦ Df(x) x` on Schwartz functions. -/
def schwartzEuler (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.id ℝ (V →L[ℝ] ℂ))
    Function.HasTemperateGrowth.id (SchwartzMap.fderivCLM ℝ V ℂ f)

lemma schwartzEuler_apply (f : 𝓢(V, ℂ)) (x : V) : schwartzEuler f x = fderiv ℝ f x x := rfl

/-- The restriction of `f` to the ray through `v`, in the logarithmic coordinate. -/
def schwartzRay (f : 𝓢(V, ℂ)) (v : V) (r : ℝ) : ℂ := f (Real.exp r • v)

lemma hasDerivAt_schwartzRay (f : 𝓢(V, ℂ)) (v : V) (r : ℝ) :
    HasDerivAt (schwartzRay f v) (schwartzRay (schwartzEuler f) v r) r := by
  have hv : HasDerivAt (fun r : ℝ => Real.exp r • v) (Real.exp r • v) r := by
    simpa using (Real.hasDerivAt_exp r).smul_const v
  exact (f.differentiableAt (x := Real.exp r • v)).hasFDerivAt.comp_hasDerivAt r hv

lemma deriv_schwartzRay (f : 𝓢(V, ℂ)) (v : V) :
    deriv (schwartzRay f v) = schwartzRay (schwartzEuler f) v :=
  funext fun r => (hasDerivAt_schwartzRay f v r).deriv

lemma iteratedDeriv_schwartzRay (f : 𝓢(V, ℂ)) (v : V) (i : ℕ) :
    iteratedDeriv i (schwartzRay f v) = schwartzRay (schwartzEuler^[i] f) v := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ', deriv_schwartzRay, ih, Function.iterate_succ_apply]

lemma contDiff_schwartzRay (f : 𝓢(V, ℂ)) (v : V) : ContDiff ℝ ∞ (schwartzRay f v) :=
  (f.smooth ⊤).comp (Real.contDiff_exp.smul contDiff_const)

/-- Every derivative of a Schwartz function along a ray, in the logarithmic coordinate, is
bounded on `ℝ`. -/
theorem exists_norm_iteratedDeriv_schwartzRay_le (f : 𝓢(V, ℂ)) (v : V) (i : ℕ) :
    ∃ C, ∀ r, ‖iteratedDeriv i (schwartzRay f v) r‖ ≤ C := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (schwartzEuler^[i] f), fun r => ?_⟩
  rw [iteratedDeriv_schwartzRay]
  exact SchwartzMap.norm_le_seminorm ℝ _ _

/-- `r ↦ gaoZhaoTransform P (eʳ)` is a Schwartz function along a ray. -/
theorem exists_gaoZhaoTransform_exp_eq (P : 𝓢(ℝ, ℂ)) :
    ∃ (F : 𝓢(ℂ, ℂ)) (v : ℂ), ∀ r, gaoZhaoTransform P (Real.exp r) = schwartzRay F v r := by
  have h3 : (0 : ℝ) < √3 := by positivity
  refine ⟨((2 / √3 : ℝ) : ℂ) • 𝓕 (radialSchwartz P one_pos), ((2 / √3 : ℝ) : ℂ), fun r => ?_⟩
  have hξ : ‖Real.exp r • (((2 / √3 : ℝ) : ℂ))‖ = 2 / √3 * Real.exp r := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos r).le,
      Real.norm_of_nonneg (by positivity), mul_comm]
  have hF := fourier_radialSchwartz P one_pos (Real.exp r • (((2 / √3 : ℝ) : ℂ)))
  rw [hξ, Real.sqrt_one, one_mul, show 2 / √3 * Real.exp r * (√3 / 2) = Real.exp r by
    field_simp] at hF
  have h1 : ((2 / √3 : ℝ) : ℂ) * ((√3 : ℂ) / 2) = 1 := by
    push_cast
    field_simp
  rw [schwartzRay, smul_apply, hF, smul_eq_mul, Complex.ofReal_one, one_mul,
    ← mul_assoc, h1, one_mul]

/-- The kernel `r ↦ gaoZhaoTransform P (eʳ)` in the logarithmic coordinate. -/
def logDualKernel (P : 𝓢(ℝ, ℂ)) (r : ℝ) : ℂ := gaoZhaoTransform P (Real.exp r)

lemma contDiff_logDualKernel (P : 𝓢(ℝ, ℂ)) : ContDiff ℝ ∞ (logDualKernel P) := by
  obtain ⟨F, v, hF⟩ := exists_gaoZhaoTransform_exp_eq P
  rw [show logDualKernel P = schwartzRay F v from funext hF]
  exact contDiff_schwartzRay F v

/-- Every logarithmic derivative `(t ∂ₜ)ⁱ` of the dual kernel is bounded on `t > 0`. -/
theorem exists_norm_iteratedDeriv_logDualKernel_le (P : 𝓢(ℝ, ℂ)) (i : ℕ) :
    ∃ C, ∀ r, ‖iteratedDeriv i (logDualKernel P) r‖ ≤ C := by
  obtain ⟨F, v, hF⟩ := exists_gaoZhaoTransform_exp_eq P
  rw [show logDualKernel P = schwartzRay F v from funext hF]
  exact exists_norm_iteratedDeriv_schwartzRay_le F v i


/-- Cut off by a smooth compactly supported `χ`, a smooth function with bounded derivatives
composed with an affine map has derivatives bounded uniformly in the shift `a`. -/
theorem exists_norm_iteratedDeriv_mul_comp_le {G χ : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ i, ∃ C, ∀ r, ‖iteratedDeriv i G r‖ ≤ C) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (c : ℝ) (n : ℕ) :
    ∃ B, ∀ a s, ‖iteratedDeriv n (fun s => χ s * G (a + c * s)) s‖ ≤ B := by
  choose CG hCG using hGb
  have hχb : ∀ i, ∃ C, ∀ s, ‖iteratedFDeriv ℝ i χ s‖ ≤ C := fun i =>
    (hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv i)
  choose Cχ hCχ using hχb
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cχ i * (|c| ^ (n - i) * CG (n - i)),
    fun a s => ?_⟩
  have hGa : ContDiff ℝ ∞ (fun s => G (a + c * s)) :=
    hG.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_mul_le hχ hGa s (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have hcomp : ‖iteratedFDeriv ℝ (n - i) (fun s => G (a + c * s)) s‖ ≤
      |c| ^ (n - i) * CG (n - i) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have h1 : (fun s => G (a + c * s)) = fun s => (fun r => G (a + r)) (c * s) := rfl
    rw [h1, iteratedDeriv_comp_const_smul (f := fun r => G (a + r))
      ((hG.comp (contDiff_const.add contDiff_id)).of_le (WithTop.coe_le_coe.mpr le_top)) c,
      iteratedDeriv_comp_const_add, norm_smul, norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hCG _ _) (by positivity)
  have hχi := hCχ i s
  have h0 : 0 ≤ Cχ i := (norm_nonneg _).trans hχi
  gcongr

lemma tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (k : ℕ) :
    tsupport (iteratedDeriv k f) ⊆ tsupport f :=
  closure_minimal (fun s hs => support_iteratedFDeriv_subset (𝕜 := ℝ) k (fun h0 => hs (by
    rw [iteratedDeriv_eq_iteratedFDeriv, h0]; rfl))) (isClosed_tsupport f)

/-- The dual kernel in the variable `s = log x₁ + log x₂`, at the shift `a = (log u)/2`,
cut off by `χ`. -/
def cutDualKernel (P : 𝓢(ℝ, ℂ)) (χ : ℝ → ℂ) (a s : ℝ) : ℂ :=
  χ s * logDualKernel P (a + (-1 / 2 : ℝ) * s)

/-- The cut-off dual kernels are smooth and their derivatives through order `n` have `L¹`
norms bounded uniformly in the shift. -/
theorem exists_cutDualKernel_bounds (P : 𝓢(ℝ, ℂ)) {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (n : ℕ) :
    ∃ A ≥ (0 : ℝ), ∀ a, ContDiff ℝ ∞ (cutDualKernel P χ a) ∧
      ∀ k ≤ n, MeasureTheory.Integrable (iteratedDeriv k (cutDualKernel P χ a)) ∧
        ∫ s, ‖iteratedDeriv k (cutDualKernel P χ a) s‖ ≤ A := by
  have hb : ∀ k, ∃ B, ∀ a s, ‖iteratedDeriv k (cutDualKernel P χ a) s‖ ≤ B := fun k =>
    exists_norm_iteratedDeriv_mul_comp_le (contDiff_logDualKernel P)
      (exists_norm_iteratedDeriv_logDualKernel_le P) hχ hχc _ k
  choose B hB using hb
  set K := tsupport χ
  have hK : MeasureTheory.volume K < ⊤ := hχc.isCompact.measure_lt_top
  refine ⟨∑ k ∈ Finset.range (n + 1), max (B k) 0 * MeasureTheory.volume.real K,
    by positivity, fun a => ?_⟩
  have hsm : ContDiff ℝ ∞ (cutDualKernel P χ a) :=
    hχ.mul ((contDiff_logDualKernel P).comp (contDiff_const.add (contDiff_const.mul contDiff_id)))
  refine ⟨hsm, fun k hk => ?_⟩
  have hsub : tsupport (iteratedDeriv k (cutDualKernel P χ a)) ⊆ K :=
    (tsupport_iteratedDeriv_subset _ k).trans tsupport_mul_subset_left
  have hcs : HasCompactSupport (iteratedDeriv k (cutDualKernel P χ a)) :=
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) hsub
  have hcont : Continuous (iteratedDeriv k (cutDualKernel P χ a)) :=
    hsm.continuous_iteratedDeriv k (by exact_mod_cast le_top)
  refine ⟨hcont.integrable_of_hasCompactSupport hcs, ?_⟩
  have hzero : ∀ s ∉ K, ‖iteratedDeriv k (cutDualKernel P χ a) s‖ = 0 := fun s hs => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hs (hsub h)), norm_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have h1 := MeasureTheory.norm_setIntegral_le_of_norm_le_const hK
    (f := fun s => ‖iteratedDeriv k (cutDualKernel P χ a) s‖) (C := max (B k) 0)
    (fun s _ => by rw [norm_norm]; exact (hB k a s).trans (le_max_left _ _))
  rw [Real.norm_of_nonneg (MeasureTheory.setIntegral_nonneg_of_ae_restrict (by
    exact Filter.Eventually.of_forall fun _ => norm_nonneg _) |>.ge |> fun h => h)] at h1
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun k => max (B k) 0 * MeasureTheory.volume.real K)
    (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

end Masullo.QRH.MeanSquare
