import Masullo.QRH.MeanSquare.Eisenstein
import Masullo.QRH.MeanSquare.Rows

/-! # Primary generators of Eisenstein ideals -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "K" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K

private instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

private abbrev rootSpec := IsCyclotomicExtension.zeta_spec 3 ℚ K
private abbrev omegaUnit : 𝓔ˣ := (rootSpec.toInteger_isPrimitiveRoot.isUnit (by decide)).unit

private lemma ramified_square : (eisOmega - 1) ^ 2 = -3 * eisOmega := by
  have h : eisOmega ^ 2 + eisOmega + 1 = 0 :=
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one rootSpec
  linear_combination h

private lemma ramified_square_associated : Associated ((eisOmega - 1) ^ 2) (3 : 𝓔) := by
  symm
  exact ⟨-omegaUnit, by rw [ramified_square]; change 3 * -eisOmega = _; ring⟩

private lemma not_unit_three : ¬ IsUnit (3 : 𝓔) := fun h =>
  rootSpec.zeta_sub_one_prime'.not_isUnit (isUnit_of_dvd_unit
    rootSpec.toInteger_sub_one_dvd_prime' h)

/-- Primary elements reduce to the identity in the quotient by three. -/
lemma eisPrimary_iff_mk_eq_one (x : 𝓔) :
    eisPrimary x ↔ Ideal.Quotient.mk (span {(3 : 𝓔)}) x = 1 := by
  rw [← map_one (Ideal.Quotient.mk (span {(3 : 𝓔)})), Ideal.Quotient.eq, mem_span_singleton]
  rfl

lemma eisPrimary.mul {x y : 𝓔} (hx : eisPrimary x) (hy : eisPrimary y) : eisPrimary (x * y) := by
  simp only [eisPrimary_iff_mk_eq_one] at *
  rw [map_mul, hx, hy, mul_one]

private lemma unit_eq_one_of_primary {u : 𝓔ˣ} (hu : eisPrimary (u : 𝓔)) : u = 1 := by
  have hcong : (eisOmega - 1) ^ 2 ∣ (u : 𝓔) - 1 := ramified_square_associated.dvd.trans hu
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent rootSpec u
      ⟨1, by rw [Int.cast_one]; exact hcong⟩ with h | h
  · exact h
  · subst u
    have hd : (3 : 𝓔) ∣ (-1 - 1 : 𝓔) + 3 := dvd_add hu dvd_rfl
    norm_num at hd
    exact (not_unit_three (isUnit_of_dvd_one hd)).elim

private lemma exists_unit_congr_of_dvd_sub_one (x : 𝓔) (h : eisOmega - 1 ∣ x - 1) :
    ∃ u : 𝓔ˣ, (3 : 𝓔) ∣ x - u := by
  obtain ⟨y, hy⟩ := h
  have reduce (z : 𝓔) (hz : eisOmega - 1 ∣ z) : (3 : 𝓔) ∣ (eisOmega - 1) * z := by
    obtain ⟨w, rfl⟩ := hz
    exact ramified_square_associated.dvd'.trans ⟨w, by ring⟩
  rcases IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one rootSpec y with
      h₀ | h₁ | hm
  · exact ⟨1, hy ▸ reduce y h₀⟩
  · refine ⟨omegaUnit, ?_⟩
    change (3 : 𝓔) ∣ x - eisOmega
    convert reduce _ h₁ using 1
    linear_combination hy
  · refine ⟨omegaUnit ^ 2, ?_⟩
    change (3 : 𝓔) ∣ x - eisOmega ^ 2
    have hω : eisOmega ^ 2 + eisOmega + 1 = 0 :=
      IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one rootSpec
    convert dvd_add (reduce _ hm) (dvd_mul_right (3 : 𝓔) 1) using 1
    linear_combination hy - hω

private lemma exists_unit_congr {x : 𝓔} (hx : IsCoprime x 3) : ∃ u : 𝓔ˣ, (3 : 𝓔) ∣ x - u := by
  rcases IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one rootSpec x with
      h₀ | h₁ | hm
  · exact (rootSpec.zeta_sub_one_prime'.not_isUnit
      (hx.isUnit_of_dvd' h₀ rootSpec.toInteger_sub_one_dvd_prime')).elim
  · exact exists_unit_congr_of_dvd_sub_one x h₁
  · obtain ⟨u, hu⟩ := exists_unit_congr_of_dvd_sub_one (-x)
      (by rw [show -x - 1 = -(x + 1) by ring]; exact hm.neg_right)
    refine ⟨-u, ?_⟩
    simpa only [Units.val_neg, sub_neg_eq_add, neg_sub, add_comm] using hu.neg_right

/-- Every ideal coprime to three admits a generator congruent to one modulo three. -/
theorem exists_primary_generator {I : Ideal 𝓔} (hI : IsCoprime I (span {3})) :
    ∃ x : 𝓔, span {x} = I ∧ eisPrimary x := by
  have hx : IsCoprime (generator I) 3 := by
    rwa [← isCoprime_span_singleton_iff, span_generator]
  obtain ⟨u, hu⟩ := exists_unit_congr hx
  refine ⟨generator I * ↑u⁻¹, ?_, ?_⟩
  · have h : Associated (generator I) (generator I * ↑u⁻¹) := ⟨u⁻¹, rfl⟩
    exact (span_singleton_eq_span_singleton.mpr h).symm.trans (span_generator I)
  change (3 : 𝓔) ∣ generator I * ↑u⁻¹ - 1
  simpa [sub_mul] using dvd_mul_of_dvd_left hu (↑u⁻¹ : 𝓔)

theorem eisPrimary_generator {I : Ideal 𝓔} (hI : IsCoprime I (span {3})) :
    eisPrimary (generator I) := by
  classical
  have h : ∃ x : 𝓔, span {x} = I ∧ (3 : 𝓔) ∣ x - 1 := exists_primary_generator hI
  unfold generator
  rw [dite_eq_left h]
  exact h.choose_spec.2

/-- Primary associates are equal. -/
theorem eq_of_associated_of_eisPrimary {x y : 𝓔} (h : Associated x y)
    (hx : eisPrimary x) (hy : eisPrimary y) : x = y := by
  obtain ⟨u, rfl⟩ := h
  rw [eisPrimary_iff_mk_eq_one, map_mul, (eisPrimary_iff_mk_eq_one x).1 hx, one_mul] at hy
  rw [unit_eq_one_of_primary ((eisPrimary_iff_mk_eq_one _).2 hy), Units.val_one, mul_one]

theorem generator_eq_of_eisPrimary {x : 𝓔} {I : Ideal 𝓔} (hspan : span {x} = I)
    (hx : eisPrimary x) : generator I = x := by
  classical
  have h : ∃ a : 𝓔, span {a} = I ∧ (3 : 𝓔) ∣ a - 1 := ⟨x, hspan, hx⟩
  apply eq_of_associated_of_eisPrimary
    (span_singleton_eq_span_singleton.mp ((span_generator I).trans hspan.symm)) _ hx
  unfold generator
  rw [dite_eq_left h]
  exact h.choose_spec.2

@[simp] theorem generator_one : generator (1 : Ideal 𝓔) = 1 :=
  generator_eq_of_eisPrimary (by simp) (by simp [eisPrimary])

theorem generator_mul {I J : Ideal 𝓔} (hI : IsCoprime I (span {3})) (hJ : IsCoprime J (span {3})) :
    generator (I * J) = generator I * generator J :=
  generator_eq_of_eisPrimary (by
    rw [← span_singleton_mul_span_singleton, span_generator, span_generator])
    ((eisPrimary_generator hI).mul (eisPrimary_generator hJ))

open InfinitePlace in
theorem norm_eisEmbedding_sq (x : 𝓔) : ‖eisEmbedding x‖ ^ 2 = (absNorm (span {x}) : ℝ) := by
  classical
  let : IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex K (n := 3) (by decide)
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp (by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
      IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3]
    decide)
  have h := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk eisFieldEmbedding.toRingHom),
    IsTotallyComplex.mult_eq, ← Algebra.coe_norm_int] at h
  change ‖eisEmbedding x‖ ^ 2 = _ at h
  rw [absNorm_span_singleton]
  simpa only [Rat.cast_abs, Rat.cast_intCast, Nat.cast_natAbs, Int.cast_abs] using h

theorem norm_eisEmbedding_generator (I : Ideal 𝓔) :
    ‖eisEmbedding (generator I)‖ = Real.sqrt (absNorm I) := by
  rw [← span_generator I, ← norm_eisEmbedding_sq, Real.sqrt_sq (norm_nonneg _), span_generator]

end Masullo.QRH.MeanSquare
