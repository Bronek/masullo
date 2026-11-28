import Masullo.QRH.MeanSquare.RayProjection
import Masullo.QRH.MeanSquare.ReflectionCusp

/-! # Fourier inversion of the exceptional ray weight at Patterson's cusp -/

noncomputable section

open NumberField Ideal Finset
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private theorem rayPhase_mul (k : ℕ) (h : 𝓔) (x : RayResidue k) :
    rayPhase k 1 (Ideal.Quotient.mk _ h * x) = rayPhase k h x := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [← map_mul, rayPhase_mk, one_mul]

/-- Use the given generator `8λᵏ` for the additive different pairing. -/
def rayAddChar (k : ℕ) : AddChar (RayResidue k) ℂ where
  toFun := rayPhase k 1
  map_zero_eq_one' := by
    rw [← map_zero (Ideal.Quotient.mk (rayModulus k)), rayPhase_mk]; simp [differentCharacter]
  map_add_eq_mul' x y := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_add, rayPhase_mk, rayPhase_mk, rayPhase_mk, one_mul, one_mul, one_mul,
      map_add, add_div, differentCharacter_add]

theorem rayAddChar_isPrimitive (k : ℕ) : (rayAddChar k).IsPrimitive := by
  rintro a ha h
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective a
  apply ha
  rw [Ideal.Quotient.eq_zero_iff_mem, rayModulus, mem_span_singleton]
  apply dvd_of_forall_differentCharacter_eq_one (by simp [eisLambda_prime.ne_zero])
  intro n
  have hh := DFunLike.congr_fun h (Ideal.Quotient.mk (rayModulus k) n)
  simpa only [AddChar.mulShift_apply, rayAddChar, AddChar.coe_mk, rayPhase_mul, rayPhase_mk,
    one_apply, mul_comm n m] using hh

/-- The finite inverse transform uses positive phases in the expansion. -/
def rayFourierCoeff (k : ℕ) (W : RayResidue k → ℂ) (h : RayResidue k) : ℂ :=
  (∑ y, W y * rayAddChar k (-(h * y))) / Fintype.card (RayResidue k)

private theorem inversion {R : Type*} [CommRing R] [Fintype R] (W : R → ℂ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (x : R) :
    ∑ h, ((∑ y, W y * ψ (-(h * y))) / Fintype.card R) * ψ (h * x) = W x := by
  classical
  have hcard : (Fintype.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ = (∑ h : R, ∑ y, W y * ψ (h * (x - y))) / Fintype.card R := by
      rw [sum_div]
      apply sum_congr rfl
      intro h _
      rw [div_mul_eq_mul_div, sum_mul]
      congr 1
      apply sum_congr rfl
      intro y _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑ y, W y * (if x - y = 0 then Fintype.card R else 0 : ℕ)) /
        Fintype.card R := by
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro y _
      rw [← mul_sum, AddChar.sum_mulShift _ hψ]
    _ = _ := by simp [sub_eq_zero, Nat.cast_ite, mul_ite, hcard]

theorem rayFourier_inversion (k : ℕ) (W : RayResidue k → ℂ) (x : RayResidue k) :
    ∑ h, rayFourierCoeff k W h * rayAddChar k (h * x) = W x :=
  inversion W _ (rayAddChar_isPrimitive k) x

theorem rayFourierCoeff_support {W : RayResidue 7 → ℂ}
    (hW : ∀ g : RayResidue 3 → ℂ, ∑ x, W x * g (rayReduction x) = 0)
    {h : 𝓔} (hh : rayFourierCoeff 7 W (Ideal.Quotient.mk _ h) ≠ 0) :
    ¬ eisLambda ^ 4 ∣ h := by
  have h' : ∑ x, W x * rayPhase 7 (-h) x ≠ 0 := by
    intro hzero
    apply hh
    simp only [rayFourierCoeff, ← neg_mul, ← map_neg, rayAddChar, AddChar.coe_mk, rayPhase_mul,
      hzero, zero_div]
  simpa only [dvd_neg] using rayFourier_ne_zero hW h'

/-- Displacement converting a residue phase on the integral numerator to a
trace phase on the frequency in `λ⁻³𝓔`. -/
def rayShift (h : RayResidue 7) : ℂ :=
  eisEmbedding (eisLambda ^ 2 * Quotient.out h) / eisEmbedding (8 * eisLambda ^ 7)

theorem rayAddChar_eq_translate (h : RayResidue 7) (m : 𝓔) :
    rayAddChar 7 (h * Ideal.Quotient.mk _ m) =
      pattersonCharacter ((eisEmbedding m / eisEmbedding eisLambda ^ 3) * rayShift h) := by
  have hLambda := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr eisLambda_prime.ne_zero
  change rayPhase 7 1 _ = _
  nth_rw 1 [← Ideal.Quotient.mk_out h]
  rw [rayPhase_mul, rayPhase_mk, differentCharacter_eq_traceCharacter_div]
  unfold rayShift
  change traceCharacter _ = traceCharacter _
  congr 1
  simp only [map_mul, map_pow, map_ofNat]
  field_simp

/-- Translating the theta expansion realizes an arbitrary finite ray weight.
The constant term is multiplied by its value at the zero frequency. -/
theorem PattersonExpansion.ray_translates {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (hθ : PattersonExpansion θ τ σ) (W : RayResidue 7 → ℂ) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    HasSum (fun m : {m : 𝓔 // m ≠ 0} =>
      let l := eisEmbedding m.val / eisEmbedding eisLambda ^ 3
      W (Ideal.Quotient.mk (rayModulus 7) m.val) *
        (τ l * v * besselK (1 / 3) (4 * Real.pi * ‖l‖ * v) * pattersonCharacter (l * z)))
      ((∑ h, rayFourierCoeff 7 W h * θ (z + rayShift h) v) - W 0 *
        (σ * (v ^ (2 / 3 : ℝ) : ℝ))) := by
  have hh := hasSum_sum (s := (univ : Finset (RayResidue 7))) (fun h _ =>
    (hθ (z + rayShift h) v hv).mul_left (rayFourierCoeff 7 W h))
  have h₀ : ∑ h, rayFourierCoeff 7 W h = W 0 := by
    simpa only [mul_zero, AddChar.map_zero_eq_one, mul_one] using rayFourier_inversion 7 W 0
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, h₀] at hh
  refine hh.congr_fun (fun m => ?_)
  let l := eisEmbedding m.val / eisEmbedding eisLambda ^ 3
  let A := τ l * v * besselK (1 / 3) (4 * Real.pi * ‖l‖ * v) * pattersonCharacter (l * z)
  calc
    W (Ideal.Quotient.mk _ m.val) * A =
        ∑ h, rayFourierCoeff 7 W h * rayAddChar 7 (h * Ideal.Quotient.mk _ m.val) * A := by
      rw [← sum_mul, rayFourier_inversion]
    _ = _ := by
      refine sum_congr rfl fun h _ => ?_
      have hadd (x y : ℂ) : pattersonCharacter (x+y) = pattersonCharacter x *
        pattersonCharacter y :=
        traceCharacter_add x y
      change _ = _ * (τ l * v * _ * pattersonCharacter (l * (z + rayShift h)))
      rw [mul_add, hadd, rayAddChar_eq_translate]
      dsimp only [A, l]
      ring

/-- Adding any tame shift to a surviving Fourier translate still gives a
cusp of Γ(3). The unit used to make its numerator primary scales both entries. -/
theorem exists_rayShift_cusp {W : RayResidue 7 → ℂ}
    (hW : ∀ g : RayResidue 3 → ℂ, ∑ x, W x * g (rayReduction x) = 0)
    {h : RayResidue 7} (hh : rayFourierCoeff 7 W h ≠ 0) (z : 𝓔)
    {r : 𝓔} (hr : r ≠ 0) (hrLambda : IsCoprime eisLambda r) :
    ∃ a b c d : 𝓔, c ≠ 0 ∧ a * d - b * c = 1 ∧ eisPrimary a ∧
      (3 : 𝓔) ∣ b ∧ (3 : 𝓔) ∣ c ∧ eisPrimary d ∧
        rayShift h + eisEmbedding z / eisEmbedding r = eisEmbedding a / eisEmbedding c := by
  let L := 8 * eisLambda ^ 7
  let H := Quotient.out h * r + 8 * eisLambda ^ 5 * z
  have hL : L ≠ 0 := by simp [L, eisLambda_prime.ne_zero]
  have hh' : ¬ eisLambda ^ 4 ∣ Quotient.out h :=
    rayFourierCoeff_support hW (by rwa [Ideal.Quotient.mk_out])
  have hH : ¬ eisLambda ^ 4 ∣ H := by
    intro hd
    have hz : eisLambda ^ 4 ∣ 8 * eisLambda ^ 5 * z := ⟨8 * eisLambda * z, by ring⟩
    have hm : eisLambda ^ 4 ∣ Quotient.out h * r := by
      simpa only [H, add_sub_cancel_right] using dvd_sub hd hz
    exact hh' (hrLambda.pow_left.dvd_of_dvd_mul_right hm)
  obtain ⟨a,c,g,hac,hnum,hden⟩ := UniqueFactorizationMonoid.exists_reduced_factors'
    (eisLambda ^ 2 * H) (L * r) (mul_ne_zero hL hr)
  have hc : c ≠ 0 := fun e => (mul_ne_zero hL hr) (by simpa [e] using hden.symm)
  have he : eisLambda ^ 2 * H * c = (a * r) * L := by
    rw [← hnum, show a * r * L = a * (L * r) by ring, ← hden]
    ring
  have hc₃ : (3 : 𝓔) ∣ c := by
    simpa only [eisLambda_sq, neg_dvd] using rayShift_denominator hH he
  have hcop := hac.isCoprime
  have ha₃ := hcop.of_isCoprime_of_dvd_right hc₃
  obtain ⟨a', haspan, hap⟩ := exists_primary_generator ((isCoprime_span_singleton_iff a 3).mpr ha₃)
  obtain ⟨u, rfl⟩ := span_singleton_eq_span_singleton.mp haspan.symm
  have hc' : IsCoprime (a * ↑u) (c * ↑u) :=
    (isCoprime_mul_unit_right_right u.isUnit _ _).mpr
      ((isCoprime_mul_unit_right_left u.isUnit _ _).mpr hcop)
  have h₃' := dvd_mul_of_dvd_left hc₃ (u : 𝓔)
  obtain ⟨b,d,hd,hb,hp⟩ := exists_patterson_cusp_matrix hc' hap h₃'
  refine ⟨_, b, _, d, mul_ne_zero hc u.ne_zero, hd, hap, hb, h₃', hp, ?_⟩
  have nz (x : 𝓔) (hx : x ≠ 0) : eisEmbedding x ≠ 0 :=
    (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hx
  have cross : (eisLambda ^ 2 * Quotient.out h * r + z * L) * c = (a * r) * L := by
    convert he using 1
    dsimp [H, L]
    ring
  have hm := congrArg eisEmbedding cross
  simp only [map_mul, map_add, map_pow] at hm
  change eisEmbedding (eisLambda ^ 2 * Quotient.out h) / eisEmbedding L + _ = _
  rw [map_mul eisEmbedding a, map_mul eisEmbedding c, mul_div_mul_right _ _ (nz _ u.ne_zero),
    map_mul eisEmbedding (eisLambda ^ 2), map_pow]
  rw [div_add_div _ _ (nz L hL) (nz r hr)]
  apply (div_eq_div_iff (mul_ne_zero (nz L hL) (nz r hr)) (nz c hc)).mpr
  linear_combination hm

end Masullo.QRH.MeanSquare
