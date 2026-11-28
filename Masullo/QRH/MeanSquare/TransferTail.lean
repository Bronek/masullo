import Masullo.QRH.MeanSquare.TransferRegroup

/-!
# The nonzero dual frequencies of a Poisson pass

* `sum_passDual_tail_eq`: the nonzero frequencies of the converted gcd splits, after Möbius
  inversion of the coprimality of the cofactors, are a sum over the dual rows `passRows` and
  pairs of dual columns `passCols`.
-/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

open Classical in
/-- The nonzero frequencies of the divisor `e` in the dual of `(g, z₁, z₂)`. -/
def tailFrequencies (P : SchwartzMap ℝ ℂ) (Y : ℝ) (z₁ z₂ e : Ideal 𝓔) : ℂ :=
  (idealMoebius e : ℂ) * pairCharacter z₂ z₁ (generator e) / (absNorm e : ℂ) *
    ∑' h : 𝓔, if h = 0 then 0 else conj (pairCharacter z₂ z₁ h) * gaoZhaoTransform P
      (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (z₂ * z₁))))

/-- The nonzero frequencies of the converted gcd splits as a sum over dual rows and columns. -/
theorem sum_passDual_tail_eq (κ κ' φ : Ideal 𝓔 → ℂ) (p : ℕ) (Corr : Q₇₂ → Q₇₂ → ℂ)
    (V : ℝ → ℂ) (P : SchwartzMap ℝ ℂ) (ℓ Y : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ t ∈ passSplits X, passDual κ κ' φ p Corr V ℓ Y t * dualExclusionTail P Y t.2.2 t.2.1 t.1 =
      ∑ r ∈ passRows X, ∑ x₁ ∈ passCols X r, ∑ x₂ ∈ passCols X r,
        (idealMoebius r.2.2 : ℂ) *
          (passDual κ κ' φ p Corr V ℓ Y (r.1 * r.2.1, r.2.2 * x₁, r.2.2 * x₂) *
            tailFrequencies P Y (r.2.2 * x₁) (r.2.2 * x₂) r.2.1) := by
  classical
  set H : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → Ideal 𝓔 → ℂ := fun t e =>
    if (absNorm (t.1 * t.2.1) : ℝ) ≤ X ∧ (absNorm (t.1 * t.2.2) : ℝ) ≤ X then
      passDual κ κ' φ p Corr V ℓ Y t * tailFrequencies P Y t.2.1 t.2.2 e else 0
  have h1 : ∑ t ∈ passSplits X, passDual κ κ' φ p Corr V ℓ Y t *
      dualExclusionTail P Y t.2.2 t.2.1 t.1 =
      ∑ t ∈ gcdSplitsLe X, ∑ e ∈ idealDivisors t.1, H t e := by
    unfold passSplits
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hg : t.1 ≠ ⊥ := by
      unfold gcdSplitsLe at ht
      exact (Finset.mem_filter.mp ht).2.1.1.1
    simp only [H]
    split_ifs with hc
    · rw [← Finset.mul_sum]
      congr 1
      unfold dualExclusionTail tailFrequencies
      convert finsum_dvd_eq_sum_idealDivisors hg (fun e => tailFrequencies P Y t.2.1 t.2.2 e)
        using 1 <;> simp only [tailFrequencies]
    · simp
  rw [h1, sum_gcdSplitsLe_eq hX]
  rw [← sum_moebiusSplitsLe_eq hX]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [H]
  split_ifs <;> simp

/-- The band-limited kernel of a pair of dual columns at positions `a, b` and scale `A`. -/
def sepKernel (P : SchwartzMap ℝ ℂ) (V : ℝ → ℂ) (a b A : ℝ) : ℂ :=
  V a * conj (V b) * ((((√(a * b))⁻¹ : ℝ) : ℂ) * gaoZhaoTransform P (√(A / (a * b))))

/-- The cap on the dual rows `h` of the row `(g, e)`. -/
def passCap (hi Y ℓ : ℝ) (g e : Ideal 𝓔) : ℝ :=
  hi ^ 2 * absNorm e * ℓ ^ 2 / (Y * (absNorm g : ℝ) ^ 2)

/-- The dual scale of the row `(g, e, h)`. -/
def passScale (Y ℓ : ℝ) (g e : Ideal 𝓔) (h : 𝓔) : ℝ :=
  Y * elementNorm h * (absNorm g : ℝ) ^ 2 / (absNorm e * ℓ ^ 2)

/-- One Möbius split of the nonzero frequencies, as finitely many dual rows `h` of two dual
columns with a band-limited kernel. -/
theorem passDual_mul_tailFrequencies_eq (hres : ResidueMultiplicative)
    {κ κ' φ : Ideal 𝓔 → ℂ} {p p' : ℕ} (hκ' : TwistMul κ' p') (hφ : TwistMul φ 0)
    {Corr : Q₇₂ → Q₇₂ → ℂ} {α : RayCharacter → RayCharacter → ℂ}
    (hα : ∀ x y : Q₇₂, IsUnit x → IsUnit y → Corr x y = ∑ ξ, ∑ η, α ξ η * ξ x * conj (η y))
    {P : SchwartzMap ℝ ℂ} (hP : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0) {V : ℝ → ℂ} {hi : ℝ}
    (hV : ∀ x, V x ≠ 0 → x ≤ hi) {ℓ Y : ℝ} (hℓ : 0 < ℓ) (hY : 0 < Y)
    {g e v x₁ x₂ : Ideal 𝓔} (hg : g ≠ ⊥) (he : e ≠ ⊥) (hv : Starred v) (h₁ : Starred x₁)
    (h₂ : Starred x₂) (hv₁ : IsCoprime v x₁) (hv₂ : IsCoprime v x₂) :
    passDual κ κ' φ p Corr V ℓ Y (g, v * x₁, v * x₂) *
        tailFrequencies P Y (v * x₁) (v * x₂) e =
      ∑ h ∈ elementRows (passCap hi Y ℓ g e), ∑ ξ, ∑ η,
        ((idealMoebius e : ℂ) / (absNorm e : ℂ) * α ξ η * passRowFactor κ κ' φ p ξ η g e v h *
          ((Y * absNorm g / ℓ : ℝ) : ℂ)) *
        (dualCoeff κ' φ p p' ξ g e v h x₁ * conj (dualCoeff κ' φ p p' η g e v h x₂)) *
        sepKernel P V (absNorm (g * (v * x₁)) / ℓ) (absNorm (g * (v * x₂)) / ℓ)
          (passScale Y ℓ g e h) := by
  classical
  have npos : ∀ {I : Ideal 𝓔}, I ≠ ⊥ → (0 : ℝ) < absNorm I := fun {I} hI => by
    have : absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hs₁ := Starred.mul_of_isCoprime hv h₁ hv₁
  have hs₂ := Starred.mul_of_isCoprime hv h₂ hv₂
  have hG := npos hg
  have hNe := npos he
  have hn : (0 : ℝ) < absNorm ((v * x₂) * (v * x₁)) := npos (mul_ne_zero hs₂.1.1 hs₁.1.1)
  have h1 : (0 : ℝ) < absNorm (g * (v * x₁)) := npos (mul_ne_zero hg hs₁.1.1)
  have h2 : (0 : ℝ) < absNorm (g * (v * x₂)) := npos (mul_ne_zero hg hs₂.1.1)
  set a : ℝ := absNorm (g * (v * x₁)) / ℓ with ha
  set b : ℝ := absNorm (g * (v * x₂)) / ℓ with hb
  set n : ℝ := ((absNorm ((v * x₂) * (v * x₁)) : ℕ) : ℝ) with hn_def
  set G : ℝ := ((absNorm g : ℕ) : ℝ) with hG_def
  set Ne : ℝ := ((absNorm e : ℕ) : ℝ) with hNe_def
  have hapos : 0 < a := div_pos h1 hℓ
  have hbpos : 0 < b := div_pos h2 hℓ
  have hprod : G ^ 2 * n = a * b * ℓ ^ 2 := by
    simp only [ha, hb, hn_def, hG_def, map_mul, Nat.cast_mul]
    field_simp
  by_cases hVab : V a = 0 ∨ V b = 0
  · have hz : V a * conj (V b) = 0 := by
      rcases hVab with h | h <;> simp [h]
    have e1 : passDual κ κ' φ p Corr V ℓ Y (g, v * x₁, v * x₂) = 0 := by
      simp only [passDual]
      rw [← ha, ← hb, hz]
      simp
    rw [e1, zero_mul]
    symm
    refine Finset.sum_eq_zero fun h _ => Finset.sum_eq_zero fun ξ _ => Finset.sum_eq_zero
      fun η _ => ?_
    simp [sepKernel, hz]
  · push Not at hVab
    have hae : a ≤ hi := hV a hVab.1
    have hbe : b ≤ hi := hV b hVab.2
    have hcap : 0 ≤ passCap hi Y ℓ g e := by
      unfold passCap
      have : 0 ≤ hi := hae.trans' hapos.le
      positivity
    have hsq : ∀ h : 𝓔, h ≠ 0 → h ∉ elementRows (passCap hi Y ℓ g e) →
        gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / (Ne * n))) = 0 := by
      intro h h0 hmem
      have hlt : passCap hi Y ℓ g e < elementNorm h := by
        by_contra hc
        exact hmem ((mem_elementRows hcap).mpr ⟨h0, not_lt.mp hc⟩)
      apply hP
      rw [Real.one_le_sqrt]
      rw [one_le_div (by positivity)]
      have e1 : passCap hi Y ℓ g e * (Y * G ^ 2) = hi ^ 2 * Ne * ℓ ^ 2 := by
        have hG' : (absNorm g : ℝ) = G := rfl
        have hN' : (absNorm e : ℝ) = Ne := rfl
        simp only [passCap, hG', hN']
        field_simp
      have e2 : G ^ 2 * n ≤ hi ^ 2 * ℓ ^ 2 := by
        rw [hprod]
        have h3 : a * b ≤ hi ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right h3 (by positivity)
      have e3 := mul_lt_mul_of_pos_right hlt (by positivity : 0 < Y * G ^ 2)
      have e4 := mul_le_mul_of_nonneg_left e2 hNe.le
      have e5 : G ^ 2 * (Ne * n) ≤ G ^ 2 * (Y * elementNorm h) := by nlinarith
      exact le_of_mul_le_mul_left e5 (by positivity)
    have hsq' : Real.sqrt (a * b) = G * Real.sqrt n / ℓ := by
      have : a * b = (G * Real.sqrt n / ℓ) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hn.le]
        field_simp
        linarith
      rw [this, Real.sqrt_sq (by positivity)]
    have hreal : Y / Real.sqrt n = Y * G / ℓ * (Real.sqrt (a * b))⁻¹ := by
      rw [hsq']
      have := Real.sqrt_pos.mpr hn
      field_simp
    have hY' : (Y : ℂ) / (Real.sqrt n : ℝ) =
        ((Y * G / ℓ : ℝ) : ℂ) * (((Real.sqrt (a * b))⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← hreal]
      push_cast
      rfl
    have hscale : ∀ h : 𝓔, passScale Y ℓ g e h / (a * b) =
        Y * elementNorm h / (Ne * n) := by
      intro h
      have hab : a * b = G ^ 2 * n / ℓ ^ 2 := by
        rw [eq_div_iff (by positivity), ← hprod]
      rw [hab]
      have hG' : (absNorm g : ℝ) = G := rfl
      have hN' : (absNorm e : ℝ) = Ne := rfl
      simp only [passScale, hG', hN']
      field_simp
    have htsum : (∑' h : 𝓔, if h = 0 then (0 : ℂ) else conj (pairCharacter (v * x₂) (v * x₁) h) *
        gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / (Ne * n)))) =
        ∑ h ∈ elementRows (passCap hi Y ℓ g e), conj (pairCharacter (v * x₂) (v * x₁) h) *
          gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / (Ne * n))) := by
      rw [tsum_eq_sum (s := elementRows (passCap hi Y ℓ g e))]
      · refine Finset.sum_congr rfl fun h hh => ?_
        have h0 : h ≠ 0 := ((mem_elementRows hcap).mp hh).1
        simp [h0]
      · intro h hh
        by_cases h0 : h = 0
        · simp [h0]
        · simp [h0, hsq h h0 hh]
    unfold tailFrequencies passDual
    simp only
    rw [htsum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have key := splitSummand_mul_eq (κ := κ) (p := p) (p' := p') hres hκ' hφ hα hv h₁ h₂
      hv₁ hv₂ (g := g) (e := e) h
    have hL : splitSummand κ κ' φ p Corr g (v * x₁) (v * x₂) *
        (V a * conj (V b)) * ((Y : ℂ) / (Real.sqrt n : ℝ)) *
        ((idealMoebius e : ℂ) * pairCharacter (v * x₂) (v * x₁) (generator e) / (absNorm e : ℂ) *
          (conj (pairCharacter (v * x₂) (v * x₁) h) *
            gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / (Ne * n))))) =
        (splitSummand κ κ' φ p Corr g (v * x₁) (v * x₂) *
          (pairCharacter (v * x₂) (v * x₁) (generator e) *
            conj (pairCharacter (v * x₂) (v * x₁) h))) *
        ((idealMoebius e : ℂ) / (absNorm e : ℂ) * (V a * conj (V b)) *
          ((Y : ℂ) / (Real.sqrt n : ℝ)) *
          gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / (Ne * n)))) := by
      ring
    rw [hL, key, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [sepKernel, hscale h, hY']
    ring

end Masullo.QRH.MeanSquare
