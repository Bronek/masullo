import Masullo.QRH.MeanSquare.CubeInversion
import Masullo.QRH.MeanSquare.ReflectionCoefficients
import Masullo.QRH.MeanSquare.ThetaSupport

/-! # Reindexing the completed sum by the primary frequencies of Patterson's series -/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Good := {n : Ideal 𝓔 // AwayFromSix n}
private abbrev Sf := {n : Ideal 𝓔 // Starred n}

private def cubeIndex (p : Good × Sf) : Good :=
  ⟨p.2.val * p.1.val ^ 3, by rw [pow_three]; exact p.2.property.1.mul (p.1.property.mul
    (p.1.property.mul p.1.property))⟩

/-- The squarefree factor and the completing cube are determined by the
prime exponents, including primes dividing both factors. -/
theorem squarefree_mul_cube_inj {a b c d : Ideal 𝓔} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (ha' : Squarefree a) (hc' : Squarefree c)
    (h : a * b ^ 3 = c * d ^ 3) : a = c ∧ b = d := by
  classical
  have hF := congrArg normalizedFactors h
  simp only [normalizedFactors_mul ha (pow_ne_zero _ hb), normalizedFactors_mul hc (pow_ne_zero _ hd),
    normalizedFactors_pow] at hF
  have ha₁ := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors ha).mp ha')
  have hc₁ := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hc).mp hc')
  have counts (p : Ideal 𝓔) : (normalizedFactors a).count p = (normalizedFactors c).count p ∧
      (normalizedFactors b).count p = (normalizedFactors d).count p := by
    have he := congrArg (Multiset.count p) hF
    simp only [Multiset.count_add, Multiset.count_nsmul] at he
    have := ha₁ p
    have := hc₁ p
    omega
  have recover {x y : Ideal 𝓔} (hx : x ≠ 0) (hy : y ≠ 0)
      (he : normalizedFactors x = normalizedFactors y) : x = y := by
    rw [← (associated_iff_eq.mp (prod_normalizedFactors hx)), he,
      associated_iff_eq.mp (prod_normalizedFactors hy)]
  exact ⟨recover ha hc (Multiset.ext.mpr fun p => (counts p).1),
    recover hb hd (Multiset.ext.mpr fun p => (counts p).2)⟩

private theorem cubeIndex_injective : Function.Injective cubeIndex := by
  rintro ⟨b,a⟩ ⟨d,c⟩ h
  have he := squarefree_mul_cube_inj a.property.1.1 b.property.1 c.property.1.1 d.property.1
    a.property.2 c.property.2 (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext he.2) (Subtype.ext he.1)

private theorem cubeIndex_mem_range {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ) (m : Good)
    (hm : τ (eisEmbedding (generator m.val)) ≠ 0) : m ∈ Set.range cubeIndex := by
  have hp := eisPrimary_generator m.property.coprime_three
  obtain ⟨c,d,_,_,hs,hc⟩ := hτ.exists_primary_cube hp.lambda_not_dvd hm
  let n : Ideal 𝓔 := span {c}
  let b : Ideal 𝓔 := span {d}
  have he : m.val = n * b ^ 3 := by
    rw [← span_generator m.val]
    rcases hc with h | h <;> rw [h] <;>
      simp only [span_singleton_neg, n, b, span_singleton_pow, span_singleton_mul_span_singleton]
  have good {i : Ideal 𝓔} (hi : i ∣ m.val) : AwayFromSix i :=
    ⟨ne_zero_of_dvd_ne_zero m.property.1 hi, m.property.2.of_isCoprime_of_dvd_left hi⟩
  have hn := good (show n ∣ m.val by rw [he]; exact dvd_mul_right ..)
  have hb := good (show b ∣ m.val by
    rw [he]
    exact (dvd_pow_self b (by decide : 3 ≠ 0)).trans (dvd_mul_left ..))
  exact ⟨(⟨b,hb⟩, ⟨n,hn,squarefree_span_singleton.mpr hs⟩), Subtype.ext he.symm⟩

/-- Sum once over each primary frequency with its normalized conjugate
coefficient. This is the ideal form of the original side of Mellin reflection. -/
theorem completedSum_eq_primary_theta {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ)
    {I : TestInterval} {j : ℕ} {W : ℝ → ℂ} (hW : UnitTest I j W) {X : ℝ} (hX : 0 < X)
    (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) :
    completedSum ξ W X k f = ∑ᶠ m : {m : Ideal 𝓔 // AwayFromSix m},
      conj (angularFactor m.val) * (conj (τ (eisEmbedding (generator m.val))) / 27) *
        eisEmbedding (powerResidueSymbol 3 eisLambda m.val) * twist ξ k f m.val *
        W (absNorm m.val / X) / Real.sqrt X := by
  classical
  let F (m : Good) : ℂ := conj (angularFactor m.val) * (conj (τ (eisEmbedding (generator m.val))) / 27) *
    eisEmbedding (powerResidueSymbol 3 eisLambda m.val) * twist ξ k f m.val *
    W (absNorm m.val / X) / Real.sqrt X
  have hf : Function.HasFiniteSupport F := by
    have hT := ((idealsLe (I.hi * X)).finite_toSet).preimage
      (Subtype.val_injective (p := AwayFromSix)).injOn
    apply hT.subset
    intro m hm
    have hw : W (absNorm m.val / X) ≠ 0 := fun h => hm (by simp [F, h])
    have hx := (hW.2.1 (subset_tsupport _ hw)).2
    exact (mem_idealsLe (mul_nonneg (I.pos.le.trans I.ordered) hX.le)).mpr ((div_le_iff₀ hX).mp hx)
  have hfc : Function.HasFiniteSupport (F ∘ cubeIndex) := by
    unfold Function.HasFiniteSupport
    rw [Function.support_comp_eq_preimage]
    exact hf.preimage cubeIndex_injective.injOn
  have hs : Function.support F ⊆ Set.range cubeIndex := by
    intro m hm
    apply cubeIndex_mem_range hτ
    exact fun h => hm (by simp [F,h])
  change _ = ∑ᶠ m, F m
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional Good) hf, ← cubeIndex_injective.tsum_eq hs]
  change _ = ∑' p, (F ∘ cubeIndex) p
  rw [tsum_eq_finsum hfc, finsum_curry _ hfc]
  unfold completedSum
  refine finsum_congr (fun b => ?_)
  simp only [columnSum, div_eq_mul_inv, finsum_mul, mul_finsum]
  refine finsum_congr (fun n => ?_)
  have hN : 0 < (absNorm b.val : ℝ) := lt_of_lt_of_le zero_lt_one (absNorm_one_le b.property.1)
  have hN' : (absNorm b.val : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsqrt : Real.sqrt ((absNorm b.val : ℝ) ^ 3) =
      (absNorm b.val : ℝ) * Real.sqrt (absNorm b.val) := by
    rw [pow_succ, Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
  dsimp only [Function.comp_apply, cubeIndex, F]
  rw [← div_eq_mul_inv X]
  rw [hτ.twisted_primary_cube ξ k f n.property b.property, norm_eisEmbedding_generator,
    Real.sqrt_div hX.le, hsqrt, map_mul, map_pow]
  push_cast
  have harg : (absNorm n.val : ℝ) * (X / (absNorm b.val : ℝ) ^ 3)⁻¹ =
      absNorm n.val * (absNorm b.val : ℝ) ^ 3 / X := by rw [inv_div]; ring
  rw [harg]
  field_simp

end Masullo.QRH.MeanSquare
