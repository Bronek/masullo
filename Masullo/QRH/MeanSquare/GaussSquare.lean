import Masullo.QRH.MeanSquare.GaussJacobi
import Masullo.QRH.MeanSquare.GaussQuadratic

/-! # Quadratic Gauss sums at squarefree Eisenstein denominators -/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

section Product

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]

private lemma primitive_components (e : R ≃+* A × B) {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) :
    let φ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
    (φ.compAddMonoidHom (AddMonoidHom.inl A B)).IsPrimitive ∧
    (φ.compAddMonoidHom (AddMonoidHom.inr A B)).IsPrimitive := by
  constructor
  · intro k hk he
    apply hψ (a := e.symm (k, 0)) (by simpa using hk)
    ext t
    have ht := DFunLike.congr_fun he (e t).1
    change ψ (e.symm (k * (e t).1, 0)) = 1 at ht
    rw [AddChar.mulShift_apply, one_apply]
    convert ht using 2
    apply e.injective
    simp [Prod.ext_iff]
  · intro k hk he
    apply hψ (a := e.symm (0, k)) (by simpa using hk)
    ext t
    have ht := DFunLike.congr_fun he (e t).2
    change ψ (e.symm (0, k * (e t).2)) = 1 at ht
    rw [AddChar.mulShift_apply, one_apply]
    convert ht using 2
    apply e.injective
    simp [Prod.ext_iff]

variable [Fintype R] [Fintype A] [Fintype B]

/-- The square-exponential identity multiplies under a ring product. -/
private lemma gaussSum_sq_of_prod (e : R ≃+* A × B) (χ : MulChar R ℂ)
    (χ₁ : MulChar A ℂ) (χ₂ : MulChar B ℂ)
    (hχ : ∀ z, χ z = χ₁ (e z).1 * χ₂ (e z).2)
    (h₁ : ∀ φ : AddChar A ℂ, φ.IsPrimitive → gaussSum χ₁ φ = ∑ x, φ (x ^ 2))
    (h₂ : ∀ φ : AddChar B ℂ, φ.IsPrimitive → gaussSum χ₂ φ = ∑ x, φ (x ^ 2))
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) : gaussSum χ ψ = ∑ x, ψ (x ^ 2) := by
  let φ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  let φ₁ := φ.compAddMonoidHom (AddMonoidHom.inl A B)
  let φ₂ := φ.compAddMonoidHom (AddMonoidHom.inr A B)
  have hφ (x : A) (y : B) : ψ (e.symm (x,y)) = φ₁ x * φ₂ y := by
    change φ (x, y) = φ (x, 0) * φ (0, y)
    rw [← φ.map_add_eq_mul]
    simp
  have hp := primitive_components e hψ
  calc
    gaussSum χ ψ = (gaussSum χ₁ φ₁) * (gaussSum χ₂ φ₂) := by
      simp only [gaussSum, Finset.sum_mul_sum]
      rw [← e.symm.toEquiv.sum_comp (fun z => χ z * ψ z), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      change χ (e.symm (x, y)) * ψ (e.symm (x, y)) = _
      rw [hχ, e.apply_symm_apply, hφ]
      ring
    _ = (∑ x, φ₁ (x ^ 2)) * ∑ y, φ₂ (y ^ 2) := by rw [h₁ _ hp.1, h₂ _ hp.2]
    _ = ∑ z : R, ψ (z ^ 2) := by
      rw [← e.symm.toEquiv.sum_comp (fun z => ψ (z ^ 2)), Fintype.sum_prod_type]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      change φ₁ (x ^ 2) * φ₂ (y ^ 2) = ψ ((e.symm (x, y)) ^ 2)
      rw [← map_pow, show (x, y) ^ 2 = (x ^ 2, y ^ 2) by simp [sq, Prod.mk_mul_mk]]
      exact (hφ _ _).symm

end Product

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- A primitive character on a squarefree quotient gives the same Gauss sum from the
quadratic residue symbol and from the squaring map. -/
theorem gaussSum_three_eq_sum_sq (n : Ideal 𝓔) : ∀ (hn : Starred n) [Fintype (𝓔 ⧸ n)]
    (ψ : AddChar (𝓔 ⧸ n) ℂ), ψ.IsPrimitive → gaussSum (sexticChar hn.1 ^ 3) ψ = ∑ x, ψ (x ^ 2) := by
  classical
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hn; exact (hn.1.1 rfl).elim
  | h₂ n hu =>
    intro hn _ ψ _
    let : Subsingleton (𝓔 ⧸ n) := Ideal.Quotient.subsingleton_iff.mpr (Ideal.isUnit_iff.mp hu)
    simp [gaussSum, Fintype.sum_subsingleton _ (1 : 𝓔 ⧸ n)]
  | h₃ a p ha hp ih =>
    intro hn _ ψ hψ
    have hb : AwayFromSix p := ⟨hp.ne_zero, hn.1.2.of_mul_left_left⟩
    have hc : AwayFromSix a := ⟨ha, hn.1.2.of_mul_left_right⟩
    have hpa : IsCoprime p a := isCoprime_iff_sup_eq.mpr (Ideal.isUnit_iff.mp
      (IsRelPrime.of_squarefree_mul hn.2 (dvd_iff_le.mpr le_sup_left)
        (dvd_iff_le.mpr le_sup_right)))
    let := Ring.HasFiniteQuotients.finiteQuotient hb.1
    let := Ring.HasFiniteQuotients.finiteQuotient hc.1
    let := Fintype.ofFinite (𝓔 ⧸ p)
    let := Fintype.ofFinite (𝓔 ⧸ a)
    apply gaussSum_sq_of_prod (quotientMulEquivQuotientProd p a hpa) _
      (sexticChar hb ^ 3) (sexticChar hc ^ 3) _ (gaussSum_three_eq_sum_sq_prime hb hp) (ih ⟨hc,
        hn.2.of_mul_right⟩) ψ hψ
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [MulChar.pow_apply' _ (by decide : 3 ≠ 0), sextic, powerResidueSymbol_mul_right, mul_pow]

theorem normalizedGauss_three_eq_quadraticExponentialSum {n : Ideal 𝓔} (hn : Starred n) :
    normalizedGauss n 3 = DeloupTuraev.quadraticExponentialSum n := by
  let := Ring.HasFiniteQuotients.finiteQuotient hn.1.1
  let := Fintype.ofFinite (𝓔 ⧸ n)
  rw [normalizedGauss_eq_gaussSum hn.1 (by decide : 3 ≠ 0),
    gaussSum_three_eq_sum_sq n hn _ (quotientDifferentCharacter_isPrimitive hn.1.1),
    DeloupTuraev.quadraticExponentialSum, finsum_eq_sum_of_fintype]

end Masullo.QRH.MeanSquare
