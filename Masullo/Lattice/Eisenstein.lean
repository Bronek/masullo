import Masullo.Lattice.Poisson

/-!
# Poisson summation on the Eisenstein integers

For `q ≠ 0` the lattice `q ℤ[ω] ⊂ ℂ`, `ω = e^{2πi/3}`, has covolume `|q|² √3/2` and dual
lattice `κ q̄⁻¹ ℤ[ω]` with `κ = 2/√-3 = -2i/√3`, for the real inner product
`⟪z, w⟫ = Re (z̄ w)` of `ℂ`. Poisson summation over the coset `a + q ℤ[ω]` is
`tsum_eisLattice_comp_add` at `x + a`.

## Main results

* `Masullo.Lattice.covolume_eisLattice`: `covol(q ℤ[ω]) = |q|² √3/2`.
* `Masullo.Lattice.mem_dual_eisLattice`: `(q ℤ[ω])* = κ q̄⁻¹ ℤ[ω]`.
* `Masullo.Lattice.tsum_eisLattice_comp_add`: Poisson summation on `q ℤ[ω]`.
* `Masullo.Lattice.tsum_eis_comp_add`: Poisson summation on `ℤ[ω]`.
-/

open MeasureTheory Set Module Complex
open scoped InnerProductSpace SchwartzMap FourierTransform RealInnerProductSpace ComplexConjugate

namespace Masullo.Lattice

/-- The cube root of unity `ω = e^{2πi/3} = -1/2 + (√3/2) i`. -/
noncomputable def omega : ℂ := ⟨-1 / 2, √3 / 2⟩

/-- `κ = 2 / √-3 = -2i/√3`, so that the dual of `ℤ[ω]` is `κ ℤ[ω]`. -/
noncomputable def kappa : ℂ := ⟨0, -2 / √3⟩

lemma sqrt_three_pos : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)

lemma sq_sqrt_three : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma omega_eq_exp : omega = cexp (2 * Real.pi * I / 3) := by
  have h : 2 * Real.pi * I / 3 = ((Real.pi - Real.pi / 3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> norm_num [omega]

/-! ### The lattices `q ℤ[ω]` -/

/-- The lattice `q ℤ[ω] = ℤ q + ℤ q ω`. -/
noncomputable def eisLattice (q : ℂ) : Submodule ℤ ℂ := Submodule.span ℤ (range ![q, q * omega])

lemma mem_eisLattice {q z : ℂ} : z ∈ eisLattice q ↔ ∃ a b : ℤ, z = q * (a + b * omega) := by
  rw [eisLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c 0, c 1, by simp [Fin.sum_univ_two, zsmul_eq_mul]; ring⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨![a, b], by simp [Fin.sum_univ_two, zsmul_eq_mul]; ring⟩

lemma linearIndependent_eis {q : ℂ} (hq : q ≠ 0) : LinearIndependent ℝ ![q, q * omega] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rw [Complex.real_smul, Complex.real_smul] at h
  have h' : (s : ℂ) + t * omega = 0 := by
    have : q * (s + t * omega) = 0 := by rw [← h]; ring
    exact (mul_eq_zero.mp this).resolve_left hq
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp only [omega, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, zero_re, zero_im]
    at hre him
  have ht : t = 0 := by
    have : t * (√3 / 2) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (by positivity)
  exact ⟨by rw [ht] at hre; linarith, ht⟩

/-- The real basis `(q, q ω)` of `ℂ`. -/
noncomputable def eisBasis {q : ℂ} (hq : q ≠ 0) : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_eis hq)
    (by simp [Complex.finrank_real_complex])

lemma eisLattice_eq_span {q : ℂ} (hq : q ≠ 0) :
    eisLattice q = Submodule.span ℤ (range (eisBasis hq)) := by
  rw [eisBasis, coe_basisOfLinearIndependentOfCardEqFinrank, eisLattice]

instance {q : ℂ} [hq : Fact (q ≠ 0)] : DiscreteTopology (eisLattice q) := by
  rw [eisLattice_eq_span hq.out]; infer_instance

instance {q : ℂ} [hq : Fact (q ≠ 0)] : IsZLattice ℝ (eisLattice q) := by
  simp_rw [eisLattice_eq_span hq.out]; infer_instance

/-- `covol(q ℤ[ω]) = |q|² √3/2`. -/
theorem covolume_eisLattice {q : ℂ} (hq : q ≠ 0) :
    ZLattice.covolume (eisLattice q) = normSq q * (√3 / 2) := by
  have : Fact (q ≠ 0) := ⟨hq⟩
  let b : Basis (Fin 2) ℤ (eisLattice q) :=
    ((eisBasis hq).restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (eisLattice_eq_span hq).symm)
  have hb : Subtype.val ∘ b = ![q, q * omega] := by
    ext i
    change (((eisBasis hq).restrictScalars ℤ i : ℂ)) = _
    rw [Basis.restrictScalars_apply, eisBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume b basisOneI, hb,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume),
    ← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis, measureReal_def,
    OrthonormalBasis.volume_parallelepiped, ENNReal.toReal_one, mul_one, Basis.det_apply,
    Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, Complex.toBasis_orthonormalBasisOneI, coe_basisOneI_repr]
  simp [omega, normSq_apply]
  rw [abs_of_nonneg (by nlinarith [sqrt_three_pos.le, mul_self_nonneg q.re, mul_self_nonneg q.im])]
  ring

/-! ### The dual lattice -/

lemma conj_eq_kappa_mul (w : ℂ) : conj w = kappa * (-(w * omega).re + w.re * omega) := by
  have h3 := sq_sqrt_three
  have h0 := sqrt_three_pos.ne'
  apply Complex.ext <;> simp [kappa, omega] <;> field_simp

lemma inner_kappa_mul_div (q : ℂ) (hq : q ≠ 0) (a b c d : ℝ) :
    ⟪kappa * (a + b * omega) / conj q, q * (c + d * omega)⟫ = b * c - a * d := by
  have h3 := sq_sqrt_three
  have h0 := sqrt_three_pos.ne'
  have e : q * (c + d * omega) * conj (kappa * (a + b * omega) / conj q) =
      (c + d * omega) * conj (kappa * (a + b * omega)) := by
    rw [map_div₀, conj_conj]
    field_simp
  rw [Complex.inner, e]
  simp [kappa, omega]
  field_simp
  nlinarith

lemma kappa_ne_zero : kappa ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [kappa, sqrt_three_pos.ne'] at this

lemma kappa_mul_mem_dual {q : ℂ} (hq : q ≠ 0) {m : ℂ} (hm : m ∈ eisLattice 1) :
    kappa * m / conj q ∈ dual (eisLattice q) := by
  obtain ⟨a, b, rfl⟩ := mem_eisLattice.mp hm
  rw [mem_dual]
  intro ℓ hℓ
  obtain ⟨c, d, rfl⟩ := mem_eisLattice.mp hℓ
  refine ⟨b * c - a * d, ?_⟩
  have := inner_kappa_mul_div q hq a b c d
  push_cast at this ⊢
  rw [one_mul, this]

lemma div_kappa_mem {q : ℂ} {ξ : ℂ} (hξ : ξ ∈ dual (eisLattice q)) :
    conj q * ξ / kappa ∈ eisLattice 1 := by
  rw [mem_dual] at hξ
  obtain ⟨m₁, hm₁⟩ := hξ q (Submodule.subset_span ⟨0, rfl⟩)
  obtain ⟨m₂, hm₂⟩ := hξ (q * omega) (Submodule.subset_span ⟨1, rfl⟩)
  rw [Complex.inner] at hm₁ hm₂
  rw [show q * omega * conj ξ = q * conj ξ * omega by ring] at hm₂
  have h := conj_eq_kappa_mul (q * conj ξ)
  rw [← hm₁, ← hm₂, map_mul, conj_conj] at h
  rw [mem_eisLattice]
  refine ⟨-m₂, m₁, ?_⟩
  rw [h, mul_div_cancel_left₀ _ kappa_ne_zero]
  push_cast
  ring

/-- `L(q)* = κ q̄⁻¹ ℤ[ω]`: multiplication by `κ / q̄` maps `ℤ[ω]` onto the dual of `q ℤ[ω]`. -/
noncomputable def eisDualEquiv {q : ℂ} (hq : q ≠ 0) : eisLattice 1 ≃ dual (eisLattice q) where
  toFun m := ⟨kappa * m / conj q, kappa_mul_mem_dual hq m.2⟩
  invFun ξ := ⟨conj q * ξ / kappa, div_kappa_mem ξ.2⟩
  left_inv m := by
    have hq' : conj q ≠ 0 := (map_ne_zero _).mpr hq
    ext; simp only; field_simp [kappa_ne_zero]
  right_inv ξ := by
    have hq' : conj q ≠ 0 := (map_ne_zero _).mpr hq
    ext; simp only; field_simp [kappa_ne_zero]

lemma mem_dual_eisLattice {q : ℂ} (hq : q ≠ 0) {ξ : ℂ} :
    ξ ∈ dual (eisLattice q) ↔ ∃ m ∈ eisLattice 1, ξ = kappa * m / conj q :=
  ⟨fun h ↦ ⟨_, ((eisDualEquiv hq).symm ⟨ξ, h⟩).2,
      (congrArg Subtype.val ((eisDualEquiv hq).apply_symm_apply ⟨ξ, h⟩)).symm⟩,
    fun ⟨_, hm, h⟩ ↦ h ▸ kappa_mul_mem_dual hq hm⟩

/-! ### Poisson summation on `q ℤ[ω]` -/

/-- **Poisson summation** on `q ℤ[ω] ⊂ ℂ`, `q ≠ 0`, with `κ = 2/√-3`:
`∑ ℓ ∈ q ℤ[ω], f (x + ℓ) = (|q|² √3/2)⁻¹ ∑ m ∈ ℤ[ω], 𝓕 f (κ m / q̄) e(⟪κ m / q̄, x⟫)`. -/
theorem tsum_eisLattice_comp_add {q : ℂ} (hq : q ≠ 0) (f : 𝓢(ℂ, ℂ)) (x : ℂ) :
    ∑' ℓ : eisLattice q, f (x + ℓ) =
      ((normSq q * (√3 / 2) : ℝ) : ℂ)⁻¹ *
        ∑' m : eisLattice 1, 𝓕 f (kappa * m / conj q) * 𝐞 ⟪kappa * m / conj q, x⟫ := by
  have : Fact (q ≠ 0) := ⟨hq⟩
  rw [tsum_comp_add_eq_tsum_dual, ← covolume_eisLattice hq, ← (eisDualEquiv hq).tsum_eq]
  rfl

/-- **Poisson summation** on the Eisenstein integers `ℤ[ω]`, of covolume `√3/2`, whose dual
lattice is `κ ℤ[ω]`. -/
theorem tsum_eis_comp_add (f : 𝓢(ℂ, ℂ)) (x : ℂ) :
    ∑' ℓ : eisLattice 1, f (x + ℓ) =
      (2 / √3 : ℂ) * ∑' m : eisLattice 1, 𝓕 f (kappa * m) * 𝐞 ⟪kappa * m, x⟫ := by
  have h := tsum_eisLattice_comp_add one_ne_zero f x
  simp only [map_one, div_one, one_mul] at h
  rw [h]
  congr 1
  push_cast
  field_simp

end Masullo.Lattice
