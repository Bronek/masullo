import Masullo.QRH.MeanSquare.GaussPhase
import Masullo.QRH.MeanSquare.Residue
import Masullo.QRH.MeanSquare.UnitRows

/-! # The norm bound for the cubic Gauss coefficient -/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

section FiniteRing

variable {R : Type*} [CommRing R] [Fintype R]

/-- Parseval for the translates of a primitive additive character of a finite ring. -/
private lemma sum_norm_fourier_sq (f : R → ℂ) {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) :
    ∑ k : R, ‖∑ x : R, f x * ψ (k * x)‖ ^ 2 = Fintype.card R * ∑ x, ‖f x‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  have hterm (k x y : R) : f x * ψ (k * x) * (conj (f y) * conj (ψ (k * y))) =
      f x * conj (f y) * ψ (k * (x - y)) := by
    rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm ..)
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
  simp [Finset.mul_sum, mul_comm]

/-- A primitive additive character gives the square-root bound for every multiplicative
character. Its Gauss sums at unit frequencies all have the same norm. -/
lemma norm_gaussSum_le_sqrt_card (χ : MulChar R ℂ) {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ≤ Real.sqrt (Fintype.card R) := by
  classical
  let S := Finset.univ.filter (IsUnit : R → Prop)
  have hp : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (show S.Nonempty from ⟨1, by simp [S]⟩)
  have hnorm (u : Rˣ) : ‖χ u‖ = 1 :=
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
  have hmass : ∑ x : R, ‖χ x‖ ^ 2 = (S.card : ℝ) := by
    rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun x _ hx => by
      by_contra h
      exact hx (by simp [χ.map_nonunit h]))]
    exact (Finset.sum_congr (g := fun _ => (1 : ℝ)) rfl fun x hx => by
      have hu := (Finset.mem_filter.mp hx).2
      rw [← hu.unit_spec, hnorm, one_pow]).trans (by simp [S])
  have hunit (k : R) (hk : k ∈ S) :
      ‖gaussSum χ ψ‖ = ‖∑ x : R, χ x * ψ (k * x)‖ := by
    obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hk).2
    simpa only [norm_mul, hnorm, one_mul, gaussSum, AddChar.mulShift_apply] using
      (congrArg norm (gaussSum_mulShift χ ψ u)).symm
  have hle : (S.card : ℝ) * ‖gaussSum χ ψ‖ ^ 2 ≤ Fintype.card R * S.card := calc
    _ = ∑ _ ∈ S, ‖gaussSum χ ψ‖ ^ 2 := by simp
    _ = _ := Finset.sum_congr rfl fun x hx => congrArg (· ^ 2) (hunit x hx)
    _ ≤ ∑ k : R, ‖∑ x : R, χ x * ψ (k * x)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ = _ := (sum_norm_fourier_sq χ hψ).trans (by rw [hmass])
  rw [mul_comm (Fintype.card R : ℝ)] at hle
  exact Real.le_sqrt_of_sq_le ((mul_le_mul_iff_right₀ hp).mp hle)

end FiniteRing

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The normalized cubic Gauss coefficient is bounded at every nonzero ideal prime to six. -/
theorem norm_gaussCoefficient_le_one {n : Ideal 𝓔} (hn : AwayFromSix n) :
    ‖gaussCoefficient n‖ ≤ 1 := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient hn.1
  let := Fintype.ofFinite (𝓔 ⧸ n)
  have hN : 0 < (absNorm n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hn.1)
  have h := norm_gaussSum_le_sqrt_card (sexticChar hn ^ 2) (quotientDifferentCharacter_isPrimitive
    hn.1)
  rw [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard] at h
  have hα : ‖angularFactor n‖ ≤ 1 := by
    simp [angularFactor, div_self_le_one]
  unfold gaussCoefficient
  rw [finsum_eq_sum_of_fintype]
  change ‖conj (angularFactor n) / (Real.sqrt (absNorm n) : ℂ) *
    ∑ x : 𝓔 ⧸ n, (sexticChar hn x) ^ 2 * quotientDifferentCharacter n x‖ ≤ 1
  simp_rw [← MulChar.pow_apply' _ (by decide : 2 ≠ 0)]
  rw [← gaussSum, norm_mul, norm_div, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_mul_eq_mul_div, div_le_one (Real.sqrt_pos.mpr hN)]
  exact (mul_le_of_le_one_left (norm_nonneg _) hα).trans h

theorem gaussCoefficientBound : GaussCoefficientBound :=
  fun _ hn => norm_gaussCoefficient_le_one hn.1

end Masullo.QRH.MeanSquare
