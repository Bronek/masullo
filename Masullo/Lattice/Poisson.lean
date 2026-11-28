import Mathlib

/-!
# Poisson summation over a lattice

For a full-rank `ℤ`-lattice `L` in a finite-dimensional real inner product space `V` and a
Schwartz function `f : V → ℂ`,
`∑ ℓ ∈ L, f (x + ℓ) = covol(L)⁻¹ ∑ ξ ∈ L*, 𝓕 f ξ e(⟪ξ, x⟫)`,
where `𝓕 f ξ = ∫ e(-⟪v, ξ⟫) f v` is Mathlib's Fourier transform, `e(t) = e^{2πit}` and
`L* = {ξ | ∀ ℓ ∈ L, ⟪ξ, ℓ⟫ ∈ ℤ}`.

## Main results

* `Masullo.Lattice.dual`, `Masullo.Lattice.mem_dual`: the dual lattice.
* `Masullo.Lattice.tsum_comp_add_eq_tsum_dual`: Poisson summation at `x`.
* `Masullo.Lattice.tsum_eq_tsum_dual`: Poisson summation at `0`.
* `Masullo.Lattice.tsum_comp_add_eq_tsum_dualVec`: the same, with `L*` in coordinates.

## Proof

Through a `ℤ`-basis of `L`, the periodisation `∑ ℓ, f (· + ℓ)` becomes a continuous function on
the unit torus. Unfolding the integral over a fundamental domain computes its Fourier coefficients
as `covol(L)⁻¹ 𝓕 f` on `L*`; these are summable, so the multivariate Fourier series
(`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`) converges to it pointwise. This is the
argument of Mathlib's one-dimensional `Real.tsum_eq_tsum_fourier`, and of Stein–Weiss,
*Introduction to Fourier analysis on Euclidean spaces*, Ch. VII, Cor. 2.6 (recalled; the source
was not consulted).
-/

open MeasureTheory Set Filter Topology Module
open scoped InnerProductSpace SchwartzMap FourierTransform RealInnerProductSpace ENNReal

namespace Masullo.Lattice

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Decay of Schwartz functions along a lattice -/

/-- A Schwartz function is bounded by a multiple of `(1 + ‖x‖) ^ (-k)`. -/
lemma SchwartzMap.exists_norm_le_inv_one_add_pow (f : 𝓢(V, ℂ)) (k : ℕ) :
    ∃ C, ∀ x, ‖f x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f,
    fun x ↦ ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero] at h
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

variable [FiniteDimensional ℝ V]

/-- Translates of a Schwartz function are summable over a discrete subgroup, uniformly on
balls. -/
lemma SchwartzMap.exists_summable_norm_comp_add_le (L : Submodule ℤ V) [DiscreteTopology L]
    (f : 𝓢(V, ℂ)) (R : ℝ) :
    ∃ g : L → ℝ, Summable g ∧ ∀ ℓ : L, ∀ v : V, ‖v‖ ≤ R → ‖f (v + ℓ)‖ ≤ g ℓ := by
  set k := finrank ℤ L + 1
  obtain ⟨C, hC⟩ := SchwartzMap.exists_norm_le_inv_one_add_pow f k
  set R' := max R 0
  refine ⟨fun ℓ ↦ C * (1 + R') ^ k * ((1 + ‖(ℓ : V)‖) ^ k)⁻¹, ?_, fun ℓ v hv ↦ ?_⟩
  · refine Summable.mul_left _
      ((ZLattice.summable_norm_rpow L (-k) ?_).of_norm_bounded_eventually ?_)
    · simp [k]
    · filter_upwards [eventually_cofinite_ne 0] with ℓ hℓ
      have hℓ' : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
      rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hℓ'.le, Real.rpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hℓ'.le (by simp) _)
  · have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 0)
      exact nonneg_of_mul_nonneg_left this (by positivity)
    refine (hC _).trans ?_
    dsimp only
    rw [mul_assoc]
    gcongr
    have h1 : ‖(ℓ : V)‖ ≤ ‖v + ℓ‖ + R' := by
      have := norm_sub_le (v + ℓ) v
      rw [add_sub_cancel_left] at this
      linarith [le_max_left R 0]
    have h2 : (1 + ‖(ℓ : V)‖) ^ k ≤ ((1 + R') * (1 + ‖v + ℓ‖)) ^ k := by
      gcongr
      nlinarith [norm_nonneg (v + ℓ), le_max_right R 0]
    have h3 : 0 < 1 + R' := by positivity
    calc ((1 + ‖v + ℓ‖) ^ k)⁻¹ = (1 + R') ^ k * (((1 + R') * (1 + ‖v + ℓ‖)) ^ k)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ _ := by gcongr

/-! ### Periodisation -/

variable (L : Submodule ℤ V) [DiscreteTopology L]

lemma summable_norm_restrict_comp_addRight (f : 𝓢(V, ℂ)) (K : TopologicalSpace.Compacts V) :
    Summable fun ℓ : L ↦
      ‖((⟨f, f.continuous⟩ : C(V, ℂ)).comp (ContinuousMap.addRight (ℓ : V))).restrict K‖ := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  obtain ⟨g, hg, hfg⟩ := SchwartzMap.exists_summable_norm_comp_add_le L f (max R 0)
  have hg0 : ∀ ℓ, 0 ≤ g ℓ := fun ℓ ↦ (norm_nonneg _).trans (hfg ℓ 0 (by simp))
  refine hg.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ℓ ↦ ?_
  refine (ContinuousMap.norm_le _ (hg0 ℓ)).mpr fun x ↦ hfg ℓ x ?_
  exact (mem_closedBall_zero_iff.mp (hR x.2)).trans (le_max_left _ _)

/-- The periodisation `x ↦ ∑ ℓ ∈ L, f (x + ℓ)` of a Schwartz function. -/
noncomputable def periodize (f : 𝓢(V, ℂ)) : C(V, ℂ) :=
  ∑' ℓ : L, (⟨f, f.continuous⟩ : C(V, ℂ)).comp (ContinuousMap.addRight (ℓ : V))

lemma periodize_apply (f : 𝓢(V, ℂ)) (x : V) : periodize L f x = ∑' ℓ : L, f (x + ℓ) := by
  rw [periodize]
  exact ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (summable_norm_restrict_comp_addRight L f)) x |>.symm

lemma periodize_add (f : 𝓢(V, ℂ)) (x : V) {ℓ₀ : V} (h : ℓ₀ ∈ L) :
    periodize L f (x + ℓ₀) = periodize L f x := by
  simp_rw [periodize_apply]
  calc ∑' ℓ : L, f (x + ℓ₀ + ℓ) = ∑' ℓ : L, f (x + ↑(ℓ + ⟨ℓ₀, h⟩)) := by
        congr 1 with ℓ
        simp only [Submodule.coe_add]
        congr 1
        abel
    _ = ∑' ℓ : L, f (x + ℓ) := (Equiv.addRight (⟨ℓ₀, h⟩ : L)).tsum_eq fun ℓ : L ↦ f (x + ℓ)

/-! ### Coordinates and the torus -/

variable [IsZLattice ℝ L]

local notation "ι" => Free.ChooseBasisIndex ℤ L

/-- A real basis of `V` that is a `ℤ`-basis of `L`. -/
noncomputable def latticeBasis : Basis ι ℝ V := (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

lemma latticeBasis_apply (i : ι) : latticeBasis L i = Free.chooseBasis ℤ L i :=
  Basis.ofZLatticeBasis_apply ℝ L _ i

lemma latticeBasis_repr_apply (ℓ : L) (i : ι) :
    (latticeBasis L).repr ℓ i = (Free.chooseBasis ℤ L).repr ℓ i :=
  Basis.ofZLatticeBasis_repr_apply ℝ L _ ℓ i

omit [IsZLattice ℝ L] in
lemma isOpenQuotientMap_torusMk :
    IsOpenQuotientMap (fun (t : ι → ℝ) (i : ι) ↦ (t i : UnitAddCircle)) :=
  IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk

omit [IsZLattice ℝ L] in
/-- The projection of coordinate space onto the unit torus. -/
noncomputable abbrev torusMk : C(ι → ℝ, UnitAddTorus ι) :=
  ⟨_, (isOpenQuotientMap_torusMk L).continuous⟩

lemma latticeBasis_equivFun_symm_mem (k : ι → ℤ) :
    (latticeBasis L).equivFun.symm (fun i ↦ (k i : ℝ)) ∈ L := by
  rw [Basis.equivFun_symm_apply]
  refine sum_mem fun i _ ↦ ?_
  rw [Int.cast_smul_eq_zsmul, latticeBasis_apply]
  exact zsmul_mem (Free.chooseBasis ℤ L i).2 _

lemma periodize_comp_factorsThrough (f : 𝓢(V, ℂ)) :
    Function.FactorsThrough
      ((periodize L f).comp ⟨_, (latticeBasis L).equivFun.symm.toContinuousLinearEquiv.continuous⟩)
      (torusMk L) := by
  intro s t hst
  have hk : ∀ i, ∃ k : ℤ, k • (1 : ℝ) = t i - s i := fun i ↦ by
    rw [← AddCircle.coe_eq_zero_iff, AddCircle.coe_sub, sub_eq_zero]
    exact (congrFun hst i).symm
  choose k hk using hk
  have ht : t = s + fun i ↦ (k i : ℝ) := by
    ext i
    have := hk i
    rw [zsmul_eq_mul, mul_one] at this
    simp only [Pi.add_apply]
    linarith
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ht, map_add]
  exact (periodize_add L f _ (latticeBasis_equivFun_symm_mem L k)).symm

/-- The periodisation of `f`, read on the unit torus through the coordinates of `L`. -/
noncomputable def torusPeriodize (f : 𝓢(V, ℂ)) : C(UnitAddTorus ι, ℂ) :=
  (isOpenQuotientMap_torusMk L).isQuotientMap.lift _ (periodize_comp_factorsThrough L f)

lemma torusPeriodize_mk (f : 𝓢(V, ℂ)) (t : ι → ℝ) :
    torusPeriodize L f (fun i ↦ (t i : UnitAddCircle)) =
      periodize L f ((latticeBasis L).equivFun.symm t) :=
  DFunLike.congr_fun ((isOpenQuotientMap_torusMk L).isQuotientMap.lift_comp _
    (periodize_comp_factorsThrough L f)) t

/-! ### The dual basis -/

lemma fourierChar_intCast (m : ℤ) : 𝐞 (m : ℝ) = 1 := by
  ext
  rw [Real.fourierChar_apply, Circle.coe_one, ← Complex.exp_int_mul_two_pi_mul_I m]
  congr 1
  push_cast
  ring

omit [FiniteDimensional ℝ V] in
lemma innerₗ_nondegenerate : (innerₗ V : LinearMap.BilinForm ℝ V).Nondegenerate :=
  ⟨fun v hv ↦ inner_self_eq_zero.mp (hv v), fun v hv ↦ inner_self_eq_zero.mp (hv v)⟩

open Classical in
/-- The basis of `V` dual to `latticeBasis L` for the inner product. -/
noncomputable def dualLatticeBasis : Basis ι ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate (latticeBasis L)

lemma inner_dualLatticeBasis (i : ι) (v : V) :
    ⟪dualLatticeBasis L i, v⟫ = (latticeBasis L).repr v i := by
  classical
  conv_lhs => rw [← (latticeBasis L).sum_repr v]
  simp_rw [inner_sum, real_inner_smul_right]
  have h (j : ι) : ⟪dualLatticeBasis L i, latticeBasis L j⟫ = if j = i then 1 else 0 := by
    rw [dualLatticeBasis]
    convert LinearMap.BilinForm.apply_dualBasis_left innerₗ_nondegenerate (latticeBasis L) i j
    rfl
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The point `∑ i, n i • dualLatticeBasis L i` of the dual lattice. -/
noncomputable def dualVec (n : ι → ℤ) : V := ∑ i, (n i : ℝ) • dualLatticeBasis L i

lemma inner_dualVec (n : ι → ℤ) (v : V) :
    ⟪dualVec L n, v⟫ = ∑ i, n i * (latticeBasis L).repr v i := by
  simp [dualVec, sum_inner, real_inner_smul_left, inner_dualLatticeBasis]

lemma fourierChar_inner_dualVec_add (n : ι → ℤ) (v : V) {ℓ : V} (hℓ : ℓ ∈ L) :
    𝐞 (-⟪ℓ + v, dualVec L n⟫) = 𝐞 (-⟪v, dualVec L n⟫) := by
  have hrepr (i : ι) : (latticeBasis L).repr ℓ i = (Free.chooseBasis ℤ L).repr ⟨ℓ, hℓ⟩ i :=
    latticeBasis_repr_apply L ⟨ℓ, hℓ⟩ i
  rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, real_inner_comm, inner_dualVec]
  simp_rw [hrepr]
  norm_cast
  rw [fourierChar_intCast, one_mul]

/-! ### The dual lattice -/

omit [DiscreteTopology L] [IsZLattice ℝ L] [FiniteDimensional ℝ V] in
/-- The dual lattice `{ξ | ∀ ℓ ∈ L, ⟪ξ, ℓ⟫ ∈ ℤ}`. -/
noncomputable def dual (L : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) L

omit [DiscreteTopology L] [IsZLattice ℝ L] [FiniteDimensional ℝ V] in
lemma mem_dual {ξ : V} : ξ ∈ dual L ↔ ∀ ℓ ∈ L, ∃ m : ℤ, (m : ℝ) = ⟪ξ, ℓ⟫ := by
  simp only [dual, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    algebraMap_int_eq, eq_intCast]
  rfl

lemma dual_eq_span : dual L = Submodule.span ℤ (range (dualLatticeBasis L)) := by
  classical
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ V)
    innerₗ_nondegenerate (latticeBasis L)
  rw [show Submodule.span ℤ (range (latticeBasis L)) = L from
    (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L] at h
  rw [dual, h, dualLatticeBasis]

lemma coe_restrictScalars_equivFun_symm (n : ι → ℤ) :
    (((dualLatticeBasis L).restrictScalars ℤ).equivFun.symm n : V) = dualVec L n := by
  simp [Basis.equivFun_symm_apply, dualVec, Basis.restrictScalars_apply, Int.cast_smul_eq_zsmul]

/-- The coordinates `ι → ℤ` of the dual lattice in the dual basis. -/
noncomputable def dualEquiv : (ι → ℤ) ≃ dual L :=
  ((dualLatticeBasis L).restrictScalars ℤ).equivFun.symm.toEquiv.trans
    (LinearEquiv.ofEq _ _ (dual_eq_span L).symm).toEquiv

lemma coe_dualEquiv (n : ι → ℤ) : (dualEquiv L n : V) = dualVec L n := by
  rw [← coe_restrictScalars_equivFun_symm]
  rfl

/-! ### Fourier coefficients of the periodisation -/

omit [FiniteDimensional ℝ V] [DiscreteTopology L] [IsZLattice ℝ L] in
lemma mFourier_mk {κ : Type*} [Fintype κ] (n : κ → ℤ) (t : κ → ℝ) :
    UnitAddTorus.mFourier n (fun i ↦ (t i : UnitAddCircle)) = 𝐞 (∑ i, n i * t i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, AddCircle.fourier_coe_apply,
    Real.fourierChar_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

variable [MeasurableSpace V] [BorelSpace V]

lemma map_equivFun_volume :
    Measure.map (latticeBasis L).equivFun volume =
      ENNReal.ofReal (ZLattice.covolume L) • volume := by
  have he : Measurable (latticeBasis L).equivFun :=
    (latticeBasis L).equivFun.toContinuousLinearEquiv.continuous.measurable
  ext A hA
  rw [Measure.map_apply he hA, smul_apply, smul_eq_mul]
  have h := ZLattice.volume_image_eq_volume_div_covolume' L (Free.chooseBasis ℤ L)
    (s := (latticeBasis L).equivFun ⁻¹' A) (hA.preimage he).nullMeasurableSet
  rw [← latticeBasis, Set.image_preimage_eq _ (latticeBasis L).equivFun.surjective] at h
  rw [h, ENNReal.mul_div_cancel]
  · exact (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos L)).ne'
  · exact ENNReal.ofReal_ne_top

lemma integral_eq_covolume_inv_mul (h : (ι → ℝ) → ℂ) :
    ∫ t, h t = (ZLattice.covolume L : ℂ)⁻¹ * ∫ v, h ((latticeBasis L).equivFun v) := by
  let e : V ≃ᵐ (ι → ℝ) :=
    (latticeBasis L).equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have h1 : ∫ v, h ((latticeBasis L).equivFun v) = ∫ t, h t ∂(Measure.map e volume) :=
    (integral_map_equiv e h).symm
  have hc := ZLattice.covolume_pos L
  rw [h1, show Measure.map e volume = _ from map_equivFun_volume L, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, Complex.real_smul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_mul]

lemma setIntegral_fundamentalDomain_periodize (f : 𝓢(V, ℂ)) (n : ι → ℤ) :
    ∫ v in ZSpan.fundamentalDomain (latticeBasis L),
      (𝐞 (-⟪v, dualVec L n⟫) : ℂ) * periodize L f v = 𝓕 f (dualVec L n) := by
  have : VAddInvariantMeasure L V volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup V volume)
  have : MeasurableConstVAdd L V := (inferInstance : MeasurableConstVAdd L.toAddSubgroup V)
  have hFD := ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) (volume : Measure V)
  rw [← latticeBasis] at hFD
  set ξ := dualVec L n
  have hint : Integrable fun v : V ↦ 𝐞 (-⟪v, ξ⟫) • f v :=
    (Real.fourierIntegral_convergent_iff ξ).mpr f.integrable
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, hFD.integral_eq_tsum'' _ hint]
  have hterm (ℓ : L) (v : V) :
      𝐞 (-⟪ℓ +ᵥ v, ξ⟫) • f (ℓ +ᵥ v) = (𝐞 (-⟪v, ξ⟫) : ℂ) * f (v + ℓ) := by
    rw [Submodule.vadd_def, vadd_eq_add, fourierChar_inner_dualVec_add L n v ℓ.2,
      Circle.smul_def, smul_eq_mul, add_comm]
  simp_rw [hterm, periodize_apply, ← tsum_mul_left]
  refine integral_tsum (fun ℓ ↦ by fun_prop) ?_
  have hl := hFD.lintegral_eq_tsum'' fun v ↦ ‖f v‖ₑ
  have hfin : ∫⁻ v, ‖f v‖ₑ < ∞ := f.integrable.2
  rw [hl] at hfin
  refine ne_of_lt (lt_of_eq_of_lt ?_ hfin)
  congr 1 with ℓ
  congr 1 with v
  simp [Submodule.vadd_def, vadd_eq_add, add_comm]

lemma mFourierCoeff_torusPeriodize (f : 𝓢(V, ℂ)) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodize L f) n =
      (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 f (dualVec L n) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      univ.pi fun _ ↦ Ioc 0 1 := by
    ext; simp
  have hae : (univ.pi fun _ : ι ↦ Ioc (0 : ℝ) 1) =ᵐ[volume] univ.pi fun _ ↦ Ico (0 : ℝ) 1 := by
    rw [volume_pi]
    exact (Measure.univ_pi_Ioc_ae_eq_Icc (f := 0) (g := 1)).trans
      (Measure.univ_pi_Ico_ae_eq_Icc (f := 0) (g := 1)).symm
  rw [hset, setIntegral_congr_set hae,
    ← integral_indicator (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico),
    integral_eq_covolume_inv_mul L, ← setIntegral_fundamentalDomain_periodize L f n,
    ← integral_indicator (ZSpan.fundamentalDomain_measurableSet _)]
  congr 1
  congr 1 with v
  have hmem : (latticeBasis L).equivFun v ∈ univ.pi (fun _ ↦ Ico (0 : ℝ) 1) ↔
      v ∈ ZSpan.fundamentalDomain (latticeBasis L) := by
    simp [ZSpan.mem_fundamentalDomain]
  by_cases hv : v ∈ ZSpan.fundamentalDomain (latticeBasis L)
  · rw [indicator_of_mem (hmem.2 hv), indicator_of_mem hv, torusPeriodize_mk,
      LinearEquiv.symm_apply_apply, mFourier_mk, smul_eq_mul, real_inner_comm, inner_dualVec]
    simp [Finset.sum_neg_distrib]
  · rw [indicator_of_notMem (hmem.not.2 hv), indicator_of_notMem hv]

lemma summable_fourier_dualVec (f : 𝓢(V, ℂ)) :
    Summable fun n : ι → ℤ ↦ ‖𝓕 f (dualVec L n)‖ := by
  set L' := Submodule.span ℤ (range (dualLatticeBasis L))
  obtain ⟨g, hg, hfg⟩ := SchwartzMap.exists_summable_norm_comp_add_le L' (𝓕 f) 0
  let e := ((dualLatticeBasis L).restrictScalars ℤ).equivFun.symm.toEquiv
  refine (hg.comp_injective e.injective).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  have := hfg (e n) 0 (by simp)
  rwa [zero_add, show ((e n : L') : V) = dualVec L n from
    coe_restrictScalars_equivFun_symm L n] at this

/-! ### Poisson summation -/

/-- **Poisson summation** over a full-rank lattice, with the dual lattice in coordinates. -/
theorem tsum_comp_add_eq_tsum_dualVec (f : 𝓢(V, ℂ)) (x : V) :
    ∑' ℓ : L, f (x + ℓ) =
      (ZLattice.covolume L : ℂ)⁻¹ * ∑' n : ι → ℤ, 𝓕 f (dualVec L n) * 𝐞 ⟪dualVec L n, x⟫ := by
  have hsum : Summable (UnitAddTorus.mFourierCoeff (torusPeriodize L f)) := by
    simp_rw [funext (mFourierCoeff_torusPeriodize L f)]
    exact ((summable_fourier_dualVec L f).of_norm).mul_left _
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (fun i ↦ ((latticeBasis L).equivFun x i : UnitAddCircle))
  rw [torusPeriodize_mk, LinearEquiv.symm_apply_apply, periodize_apply] at h
  rw [← h.tsum_eq, ← tsum_mul_left]
  congr 1 with n
  rw [mFourierCoeff_torusPeriodize, mFourier_mk, smul_eq_mul, mul_assoc, inner_dualVec]
  simp [Basis.equivFun_apply]

/-- **Poisson summation** over a full-rank lattice `L` in a real inner product space:
`∑ ℓ ∈ L, f (x + ℓ) = covol(L)⁻¹ ∑ ξ ∈ L*, 𝓕 f ξ e(⟪ξ, x⟫)`. -/
theorem tsum_comp_add_eq_tsum_dual (f : 𝓢(V, ℂ)) (x : V) :
    ∑' ℓ : L, f (x + ℓ) =
      (ZLattice.covolume L : ℂ)⁻¹ * ∑' ξ : dual L, 𝓕 f ξ * 𝐞 ⟪(ξ : V), x⟫ := by
  rw [tsum_comp_add_eq_tsum_dualVec, ← (dualEquiv L).tsum_eq]
  simp_rw [coe_dualEquiv]

/-- **Poisson summation** over a full-rank lattice at the origin. -/
theorem tsum_eq_tsum_dual (f : 𝓢(V, ℂ)) :
    ∑' ℓ : L, f ℓ = (ZLattice.covolume L : ℂ)⁻¹ * ∑' ξ : dual L, 𝓕 f ξ := by
  simpa using tsum_comp_add_eq_tsum_dual L f 0

end Masullo.Lattice
