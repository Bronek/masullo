import Masullo.QRH.MeanSquare.CosetPoisson
import Masullo.QRH.MeanSquare.Poisson

/-! # Steps toward the primitive Poisson formula

`elementNorm_eq_normSq` identifies the ideal norm of `(y)` with `|σ(y)|²` in the fixed
embedding, the normalisation of `GaoZhaoLemma23` and `hasSum_twisted_poisson`.
-/

noncomputable section

open NumberField
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "K" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K

private theorem cyclotomicThree'' : IsCyclotomicExtension {3} ℚ K := by
  let : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

attribute [local instance] cyclotomicThree''

/-- The norm of `K / ℚ` is `σ(x) σ̄(x)` in the fixed embedding. -/
lemma algebraMap_norm_eq_mul_conj (x : K) :
    algebraMap ℚ ℂ (Algebra.norm ℚ x) = eisFieldEmbedding x * conj (eisFieldEmbedding x) := by
  classical
  let σ₁ : K →ₐ[ℚ] ℂ := (Complex.conjAe.restrictScalars ℚ).toAlgHom.comp eisFieldEmbedding
  have hne : eisFieldEmbedding ≠ σ₁ := by
    intro h
    have h' := congrArg (fun σ : K →ₐ[ℚ] ℂ ↦ σ (eisOmega : K)) h
    simp only [σ₁, AlgHom.comp_apply] at h'
    have h'' : eisEmbedding eisOmega = conj (eisEmbedding eisOmega) := h'
    rw [eisEmbedding_eisOmega, conj_omega] at h''
    have := congrArg Complex.im h''
    simp [Masullo.Lattice.omega] at this
    linarith [Masullo.Lattice.sqrt_three_pos]
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by
    rw [AlgHom.card, IsCyclotomicExtension.Rat.finrank 3 K, Nat.totient_prime Nat.prime_three]
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {eisFieldEmbedding, σ₁} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ, huniv, Finset.prod_pair hne]
  rfl

/-- The ideal norm of `(y)` is `|σ(y)|²`. -/
lemma elementNorm_eq_normSq (y : 𝓔) : (elementNorm y : ℝ) = Complex.normSq (eisEmbedding y) := by
  have h : ((Algebra.norm ℤ y : ℤ) : ℂ) = (Complex.normSq (eisEmbedding y) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm, ← Rat.cast_intCast,
      Algebra.coe_norm_int, ← eq_ratCast (algebraMap ℚ ℂ), algebraMap_norm_eq_mul_conj]
    rfl
  have h' : ((Algebra.norm ℤ y : ℤ) : ℝ) = Complex.normSq (eisEmbedding y) := by
    exact_mod_cast h
  rw [elementNorm, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, h',
    abs_of_nonneg (Complex.normSq_nonneg _)]

end Masullo.QRH.MeanSquare
