import Masullo.QRH.MeanSquare.GaussJacobi

/-! # Tame Fourier coefficients in the cubic theta reflection -/

noncomputable section

namespace Masullo.QRH.MeanSquare.ReflectionTame

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Additive Fourier coefficient of a zero-extended multiplicative character. -/
def coefficient (η : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  gaussSum η (ψ.mulShift (-h)) / Fintype.card F

omit [DecidableEq F] in
private lemma card_units_cast :
    (Nat.card Fˣ : ℂ) = (Fintype.card F : ℂ) - 1 := by
  have h := Nat.card_eq_card_units_add_one F
  rw [Nat.card_eq_fintype_card (α := F)] at h
  exact eq_sub_of_add_eq (by exact_mod_cast h.symm)

omit [DecidableEq F] in
theorem coefficient_zero (η : MulChar F ℂ) (ψ : AddChar F ℂ) :
    coefficient η ψ 0 = if η = 1 then ((Fintype.card F : ℂ) - 1) / Fintype.card F else 0 := by
  rw [coefficient, neg_zero, AddChar.mulShift_zero]
  split_ifs with h
  · rw [h, gaussSum_one_one, card_units_cast]
  · rw [gaussSum_one_right h, zero_div]

omit [DecidableEq F] in
private lemma coefficient_unit (η : MulChar F ℂ) (ψ : AddChar F ℂ) (h : Fˣ) :
    coefficient η ψ h = (η⁻¹ (-1) * gaussSum η ψ / Fintype.card F) * η⁻¹ h := by
  rw [coefficient, show -(h : F) = ((-h : Fˣ) : F) by simp, gaussSum_mulShift_eq]
  rw [show ((-h : Fˣ) : F) = (-1 : F) * (h : F) by simp, map_mul]
  ring

/-- The active term at a prime, including the conjugate Kubota multiplier. -/
def activeSum (χ : MulChar F ℂ) (j : ℕ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (m : F) : ℂ :=
  ∑ h : Fˣ, coefficient (χ ^ j) ψ h * (χ ^ 2)⁻¹ ((σ : F) * h) *
    ψ ((ε : F) * m * (h : F)⁻¹)

private lemma activeSum_eq (χ : MulChar F ℂ) (j : ℕ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (m : F) :
    activeSum χ j ψ σ ε m =
      ((χ ^ j)⁻¹ (-1) * (χ ^ 2)⁻¹ σ * gaussSum (χ ^ j) ψ / Fintype.card F) *
        gaussSum (χ ^ (j + 2)) (ψ.mulShift ((ε : F) * m)) := by
  let θ := χ ^ (j + 2)
  let f (y : F) := θ y * ψ ((ε : F) * m * y)
  have hu : ∑ h : Fˣ, f h = ∑ y : F, f y := by
    apply Fintype.sum_of_injective Units.val Units.val_injective _ _ _ (fun _ => rfl)
    intro y hy
    have : y = 0 := by
      by_contra hn
      exact hy ⟨Units.mk0 y hn, rfl⟩
    simp [this, f, MulChar.map_zero]
  have hinv : ∑ h : Fˣ, f ((h : F)⁻¹) = ∑ h : Fˣ, f h := by
    simpa using Equiv.sum_comp (Equiv.inv Fˣ) (fun h : Fˣ => f h)
  rw [activeSum, show gaussSum (χ ^ (j + 2)) (ψ.mulShift ((ε : F) * m)) = ∑ y : F, f y by rfl,
    ← hu, ← hinv, Finset.mul_sum]
  refine sum_congr rfl fun h _ => ?_
  simp only [coefficient_unit, map_mul, f, θ, pow_add, MulChar.mul_apply,
    MulChar.inv_apply' (χ ^ j) (h : F), MulChar.inv_apply' (χ ^ 2) (h : F)]
  ring

private lemma gauss_shift {η : MulChar F ℂ} (hη : η ≠ 1) (ψ : AddChar F ℂ) (m : F) :
    gaussSum η (ψ.mulShift m) = η⁻¹ m * gaussSum η ψ := by
  by_cases hm : m = 0
  · simp [hm, AddChar.mulShift_zero, gaussSum_one_right hη, MulChar.map_zero]
  · exact gaussSum_mulShift_eq η ψ (Units.mk0 m hm)

private lemma principal_shift {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (ε : Fˣ) (m : F) :
    gaussSum (1 : MulChar F ℂ) (ψ.mulShift ((ε : F) * m)) =
      (if m = 0 then (Fintype.card F : ℂ) - 1 else -1) := by
  by_cases hm : m = 0
  · rw [hm, mul_zero, AddChar.mulShift_zero, gaussSum_one_one, card_units_cast]
    simp
  · simp [hm, gaussSum_one_left (hψ (mul_ne_zero ε.ne_zero hm))]

omit [DecidableEq F] in
private lemma norm_gauss {η : MulChar F ℂ} (hη : η ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum η ψ‖ = Real.sqrt (Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hη hψ
  rw [← star_gaussSum_eq, Complex.star_def, Complex.mul_conj'] at h
  have hsq : ‖gaussSum η ψ‖ ^ 2 = (Fintype.card F : ℝ) := by exact_mod_cast h
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

private lemma norm_char (η : MulChar F ℂ) (u : Fˣ) : ‖η (u : F)‖ = 1 :=
  Complex.norm_eq_one_of_mem_rootsOfUnity (η.apply_mem_rootsOfUnity u)

/-- The three column factors, with the principal character at power zero still
extended by zero at nonunits. -/
def factor (χ : MulChar F ℂ) (j : ℕ) (m : F) : ℂ :=
  if j = 4 then (if m = 0 then (Fintype.card F : ℂ) - 1 else -1) / Real.sqrt (Fintype.card F)
  else if j = 0 then (χ ^ 2)⁻¹ m / Real.sqrt (Fintype.card F)
  else (χ ^ (j + 2))⁻¹ m

/-- Fourier inversion with the same primitive character used on the reflected side. -/
theorem inversion (η : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (x : F) :
    ∑ h : F, coefficient η ψ h * ψ (h * x) = η x := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ = (∑ h : F, ∑ y : F, η y * ψ (h * (x - y))) / Fintype.card F := by
      rw [Finset.sum_div]
      refine sum_congr rfl fun h _ => ?_
      rw [coefficient, div_mul_eq_mul_div, gaussSum, sum_mul]
      congr 1
      refine sum_congr rfl fun y _ => ?_
      rw [mul_assoc, AddChar.mulShift_apply, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑ y : F, η y * (if x - y = 0 then Fintype.card F else 0 : ℕ)) / Fintype.card F := by
      rw [sum_comm]
      congr 1
      refine sum_congr rfl fun y _ => ?_
      rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
    _ = _ := by
      simp [sub_eq_zero, Nat.cast_ite, mul_ite, hq]

omit [DecidableEq F] in
/-- Only exponent zero admits an inactive prime. -/
theorem coefficient_zero_pow {χ : MulChar F ℂ} (hχ : orderOf χ = 6) (ψ : AddChar F ℂ)
    {j : ℕ} (hj : j < 6) :
    coefficient (χ ^ j) ψ 0 = if j = 0 then 1 - (Fintype.card F : ℂ)⁻¹ else 0 := by
  rw [coefficient_zero]
  split_ifs with h₁ h₂ h₂
  · have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  · exact (pow_ne_one_of_lt_orderOf h₂ (by rwa [hχ]) h₁).elim
  · simp [h₂] at h₁
  · rfl

omit [DecidableEq F] in
/-- The nonzero Fourier modes of the principal character have weight `-1/q`. -/
theorem coefficient_one_unit {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (u : Fˣ) :
    coefficient 1 ψ u = -(Fintype.card F : ℂ)⁻¹ := by
  have hψ₁ : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ (one_ne_zero : (1 : F) ≠ 0)
  rw [coefficient_unit, inv_one, MulChar.one_apply isUnit_neg_one, MulChar.one_apply_coe,
    gaussSum_one_left hψ₁]
  ring

omit [DecidableEq F] in
private lemma norm_gauss_div_sqrt {η : MulChar F ℂ} (hη : η ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum η ψ / (Real.sqrt (Fintype.card F) : ℂ)‖ = 1 := by
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  rw [norm_div, norm_gauss hη hψ]
  simp [abs_of_pos hpos, hpos.ne']

/-- Nonzero Fourier modes of a nonprincipal character have a common phase
times the inverse character divided by the square root of the field order. -/
theorem coefficient_nontrivial_unit {η : MulChar F ℂ} (hη : η ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ∃ C : ℂ, ‖C‖ = 1 ∧ ∀ u : Fˣ, coefficient η ψ u = C * η⁻¹ u / Real.sqrt (Fintype.card F) := by
  let r : ℂ := Real.sqrt (Fintype.card F)
  have hrq : r ^ 2 = (Fintype.card F : ℂ) := by
    dsimp [r]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_natCast]
  refine ⟨η⁻¹ (-1) * (gaussSum η ψ / r), ?_, ?_⟩
  · have hneg : ‖η⁻¹ (-1 : F)‖ = 1 := by simpa using norm_char η⁻¹ (-1 : Fˣ)
    rw [norm_mul, hneg, norm_gauss_div_sqrt hη hψ, one_mul]
  · intro u
    change _ = _ / r
    rw [coefficient_unit, ← hrq]
    ring

/-- Each active sum is a unit scalar times its column factor. The scalar
can depend on the prime data and the two CRT units, and is uniform in `m`. -/
theorem activeSum_eq_phase_mul_factor {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {j : ℕ} (hj : j < 6) (σ ε : Fˣ) :
    ∃ C : ℂ, ‖C‖ = 1 ∧ ∀ m : F, activeSum χ j ψ σ ε m = C * factor χ j m := by
  let r : ℂ := Real.sqrt (Fintype.card F)
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hrq : r ^ 2 = (Fintype.card F : ℂ) := by
    dsimp [r]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_natCast]
  have phase (η : MulChar F ℂ) (hη : η ≠ 1) : ‖gaussSum η ψ / r‖ = 1 :=
    norm_gauss_div_sqrt hη hψ
  have hminus (η : MulChar F ℂ) : ‖η (-1 : F)‖ = 1 := by simpa using norm_char η (-1 : Fˣ)
  have htwo : χ ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by decide) (by rw [hχ]; decide)
  have hψ₁ : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ (one_ne_zero : (1 : F) ≠ 0)
  by_cases h0 : j = 0
  · subst j
    refine ⟨-((χ ^ 2)⁻¹ σ * (χ ^ 2)⁻¹ ε * (gaussSum (χ ^ 2) ψ / r)), ?_, ?_⟩
    · rw [norm_neg, norm_mul, norm_mul, norm_char, norm_char, phase _ htwo]
      norm_num
    · intro m
      rw [activeSum_eq, pow_zero, zero_add, inv_one, MulChar.one_apply isUnit_neg_one,
        gaussSum_one_left hψ₁, gauss_shift htwo, map_mul]
      simp only [factor, reduceCtorEq, ↓reduceIte]
      change _ = _ * (_ / r)
      rw [← hrq]
      field_simp

  have hjχ : χ ^ j ≠ 1 := pow_ne_one_of_lt_orderOf h0 (by rwa [hχ])
  by_cases h4 : j = 4
  · subst j
    have h6 : χ ^ (4 + 2) = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    refine ⟨(χ ^ 4)⁻¹ (-1) * (χ ^ 2)⁻¹ σ * (gaussSum (χ ^ 4) ψ / r), ?_, ?_⟩
    · rw [norm_mul, norm_mul, hminus, norm_char, phase _ hjχ]
      norm_num
    · intro m
      rw [activeSum_eq, h6, principal_shift hψ]
      change _ = _ * (_ / r)
      have hscalar (z x y : ℂ) : x * y / (Fintype.card F : ℂ) * z = x * (y / r) * (z / r) := by
        rw [← hrq]
        field_simp
      apply hscalar
  have hθ : χ ^ (j + 2) ≠ 1 := by
    intro h
    have hd := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hχ] at hd
    omega
  refine ⟨(χ ^ j)⁻¹ (-1) * (χ ^ 2)⁻¹ σ * (χ ^ (j + 2))⁻¹ ε *
    (gaussSum (χ ^ j) ψ / r) * (gaussSum (χ ^ (j + 2)) ψ / r), ?_, ?_⟩
  · simp only [norm_mul, hminus, norm_char, phase _ hjχ, phase _ hθ, one_mul]
  · intro m
    rw [activeSum_eq, gauss_shift hθ, map_mul]
    simp only [factor, h4, h0, ↓reduceIte]
    rw [← hrq]
    field_simp

/-- A prime appearing to exponent one on the original side contributes the
quadratic symbol on the reflected side. -/
theorem factor_one {χ : MulChar F ℂ} (hχ : orderOf χ = 6) (hF : ringChar F ≠ 2) (m : F) :
    factor χ 1 m = (quadraticChar F m : ℂ) := by
  have hinv : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    simpa [hχ] using pow_orderOf_eq_one χ
  change (χ ^ 3)⁻¹ m = _
  rw [hinv, cubic_power_eq_quadraticChar hχ hF]
  rfl

/-- At a frequency `u n b³` the varying part of the quadratic twist is the symbol of `n b`. -/
theorem factor_one_mul_cube {χ : MulChar F ℂ} (hχ : orderOf χ = 6) (hF : ringChar F ≠ 2)
    (u : Fˣ) (n b : F) :
    factor χ 1 ((u : F) * n * b ^ 3) = (quadraticChar F u : ℂ) * (quadraticChar F (n * b) : ℂ) := by
  have hb : quadraticChar F b ^ 3 = quadraticChar F b := by
    by_cases hb : b = 0
    · simp [hb]
    · rw [pow_succ, quadraticChar_sq_one hb, one_mul]
  rw [factor_one hχ hF]
  simp only [map_mul, map_pow, hb, Int.cast_mul, mul_assoc]

/-- The exceptional factor splits according to which of the squarefree part and the cube
part of the frequency is divisible by the prime. -/
theorem factor_four_mul_cube (χ : MulChar F ℂ) (u : Fˣ) (n b : F) :
    factor χ 4 ((u : F) * n * b ^ 3) =
      (-1 + (if n = 0 then (Fintype.card F : ℂ) else 0) +
        (if n ≠ 0 ∧ b = 0 then (Fintype.card F : ℂ) else 0)) / Real.sqrt (Fintype.card F) := by
  by_cases hn : n = 0 <;> by_cases hb : b = 0 <;> simp [factor, hn, hb, u.ne_zero, sub_eq_neg_add]

end Masullo.QRH.MeanSquare.ReflectionTame
