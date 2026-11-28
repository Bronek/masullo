import Masullo.QRH.MeanSquare.ReflectionCompletion
import Masullo.QRH.MeanSquare.ReflectionSmoothed
import Masullo.QRH.MeanSquare.ThetaTranslate
import Masullo.QRH.MeanSquare.ReflectionTwist

/-! # Fixed ray projection of the completed Patterson column -/

noncomputable section

open NumberField Ideal Complex Filter Set
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Good := {n : Ideal 𝓔 // AwayFromSix n}
private abbrev Index := {m : 𝓔 // m ≠ 0}

/-- A test of compact support leaves finitely many numerators in the frequency lattice. -/
theorem pattersonTest_hasFiniteSupport {I : TestInterval} {j : ℕ} {V : ℝ → ℂ}
    (hV : UnitTest I j V) {X : ℝ} (hX : 0 < X) :
    Function.HasFiniteSupport (fun m : {m : 𝓔 // m ≠ 0} =>
      V (normSq (pattersonFrequency m)/X)) := by
  have hT := tendsto_norm_pattersonFrequency.eventually_gt_atTop (Real.sqrt (I.hi * X))
  have he : ∀ᶠ m in cofinite, V (normSq (pattersonFrequency m) / X) = 0 := by
    filter_upwards [hT] with m hm
    by_contra hn
    have hx := (hV.2.1 (subset_tsupport _ hn)).2
    rw [normSq_eq_norm_sq, div_le_iff₀ hX] at hx
    have hIX : 0 ≤ I.hi*X := mul_nonneg (I.pos.le.trans I.ordered) hX.le
    have := Real.sq_sqrt hIX
    nlinarith [sq_lt_sq' (by linarith [Real.sqrt_nonneg (I.hi*X)]) hm]
  exact (eventually_cofinite.mp he).preimage (Subtype.val_injective (p := fun m : 𝓔 => m ≠ 0)).injOn

/-- Projected column before finite Fourier inversion at the fixed and tame moduli. -/
def projectedPattersonSum (τ : ℂ → ℂ) (φ : RayResidue 7 → ℂ) (T : 𝓔 → ℂ)
    (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' m : Index, (φ (Ideal.Quotient.mk (rayModulus 7) m) * T m) *
    (pattersonAngularCoefficient τ true 0 m * V (normSq (pattersonFrequency m) / X) / Real.sqrt X)

private def primaryIndex (n : Good) : Index :=
  ⟨eisLambda ^ 3 * generator n.val, mul_ne_zero (pow_ne_zero _ eisLambda_prime.ne_zero)
    (eisPrimary_generator n.property.coprime_three).ne_zero⟩

private theorem primaryIndex_injective : Function.Injective primaryIndex := by
  intro m n h
  have hg : generator m.val = generator n.val :=
    mul_left_cancel₀ (pow_ne_zero _ eisLambda_prime.ne_zero) (congrArg Subtype.val h)
  exact Subtype.ext ((span_generator _).symm.trans ((congrArg (fun a : 𝓔 =>
    span {a}) hg).trans (span_generator _)))

private theorem pattersonFrequency_cube_mul (a : 𝓔) :
    pattersonFrequency (eisLambda ^ 3 * a) = eisEmbedding a := by
  have hl : eisEmbedding eisLambda ≠ 0 := fun h =>
    eisLambda_prime.ne_zero (eisEmbedding_injective (h.trans (map_zero _).symm))
  simp [pattersonFrequency, hl]

private theorem good_span_iff {a : 𝓔} (ha : eisPrimary a) :
    AwayFromSix (span {a}) ↔ IsUnit (Ideal.Quotient.mk (span {(6:𝓔)}) a) := by
  rw [isUnit_mk_iff_coprime_span, isCoprime_comm]
  exact and_iff_right (by simpa using ha.ne_zero)

private theorem outside_good (m : Index) {w : RayResidue 7 → ℂ} {ψ : (𝓔 ⧸ span {(72:𝓔)}) → ℂ}
    (hw : ∀ a : 𝓔, w (Ideal.Quotient.mk (rayModulus 7) (eisLambda^3*a)) = primaryRayWeight ψ a)
    (hs : ∀ x, w x ≠ 0 → rayDivides 3 x)
    (hm : w (Ideal.Quotient.mk (rayModulus 7) m) ≠ 0) :
    m ∈ Set.range primaryIndex := by
  classical
  obtain ⟨a, ha⟩ := (rayDivides_mk (by decide) _).mp (hs _ hm)
  rw [ha, hw] at hm
  have hg : eisPrimary a ∧ IsUnit (Ideal.Quotient.mk (span {(6:𝓔)}) a) := by
    by_contra h
    exact hm (by simp [primaryRayWeight, h])
  refine ⟨⟨span {a}, (good_span_iff hg.1).mpr hg.2⟩, Subtype.ext ?_⟩
  change eisLambda^3 * generator (span {a}) = m.val
  rw [generator_eq_of_eisPrimary rfl hg.1, ← ha]

private theorem completed_eq_projected {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ)
    {φ w : RayResidue 7 → ℂ} {ψ : (𝓔 ⧸ span {(72:𝓔)}) → ℂ}
    (hw : ∀ a : 𝓔, w (Ideal.Quotient.mk (rayModulus 7) (eisLambda^3*a)) = primaryRayWeight ψ a)
    (hs : ∀ x, w x ≠ 0 → rayDivides 3 x)
    (hφ : ∀ x, ¬ rayFourthLayer x → φ x = w x)
    (T : 𝓔 → ℂ) {I : TestInterval} {j : ℕ} {V : ℝ → ℂ}
    (hV : UnitTest I j V) {X : ℝ} (hX : 0 < X) (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔)
    (hfac : ∀ n : Ideal 𝓔, AwayFromSix n → twist ξ k f n =
      ψ (Ideal.Quotient.mk _ (generator n)) * T (eisLambda^3 * generator n)) :
    completedSum ξ V X k f = projectedPattersonSum τ φ T V X := by
  classical
  let F := fun m : Index => (w (Ideal.Quotient.mk (rayModulus 7) m) * T m) *
    (pattersonAngularCoefficient τ true 0 m * V (normSq (pattersonFrequency m) / X) / Real.sqrt X)
  have hF : Function.HasFiniteSupport F := (pattersonTest_hasFiniteSupport hV hX).subset
    (fun m hm => fun hz => hm (by simp [F,hz]))
  have hfin : Function.HasFiniteSupport (F ∘ primaryIndex) := by
    unfold Function.HasFiniteSupport
    rw [Function.support_comp_eq_preimage]
    exact hF.preimage primaryIndex_injective.injOn
  have hsupport : Function.support F ⊆ Set.range primaryIndex := fun m hm =>
    outside_good m hw hs (fun hz => hm (by simp [F,hz]))
  have hchange : projectedPattersonSum τ φ T V X = ∑' m, F m := by
    apply tsum_congr
    intro m
    by_cases hl : rayFourthLayer (Ideal.Quotient.mk (rayModulus 7) m)
    · obtain ⟨h₄,h₅⟩ := (rayFourthLayer_mk _).mp hl
      have hz : τ (pattersonFrequency m) = 0 := hτ.zero_of_lambda_four h₄ h₅
      simp [F, pattersonAngularCoefficient, hz]
    · rw [hφ _ hl]
  rw [hchange, ← primaryIndex_injective.tsum_eq hsupport]
  change _ = ∑' n : Good, (F ∘ primaryIndex) n
  rw [tsum_eq_finsum hfin, completedSum_eq_primary_theta hτ hV hX]
  apply finsum_congr
  intro n
  let a := generator n.val
  have hp := eisPrimary_generator n.property.coprime_three
  have hu : IsUnit (Ideal.Quotient.mk (span {(6:𝓔)}) a) :=
    (good_span_iff hp).mp (by simpa only [span_generator] using n.property)
  have hN : normSq (eisEmbedding a) = absNorm n.val := by
    rw [normSq_eq_norm_sq, norm_eisEmbedding_sq, span_generator]
  dsimp only [Function.comp_apply, F, primaryIndex]
  rw [hw, pattersonFrequency_cube_mul, hN, pattersonAngularCoefficient, pattersonFrequency_cube_mul,
    primaryRayWeight, ite_eq_left ⟨hp,hu⟩, cubicSymbol, span_generator, hfac _ n.property]
  simp only [mul_zero, pattersonCharacter, zero_re, mul_zero, ofReal_zero, exp_zero, mul_one,
    angularFactor, map_div₀, conj_ofReal, ite_true]
  ring


private theorem norm_primaryRayWeight_le_one {ψ : (𝓔 ⧸ span {(72:𝓔)}) → ℂ}
    (hψ : ∀ r, ‖ψ r‖ ≤ 1) (a : 𝓔) : ‖primaryRayWeight ψ a‖ ≤ 1 := by
  classical
  unfold primaryRayWeight
  split_ifs with h
  · have hn := (good_span_iff h.1).mpr h.2
    rw [norm_mul, cubicSymbol, ← powerResidueSymbol_six_sq hn.2, map_pow, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_sextic_le_one _
      _))).trans (hψ _)
  · simp

private theorem norm_lift_le_one {w : RayResidue 7 → ℂ} {ψ : (𝓔 ⧸ span {(72:𝓔)}) → ℂ}
    (hw : ∀ a : 𝓔, w (Ideal.Quotient.mk (rayModulus 7) (eisLambda^3*a)) = primaryRayWeight ψ a)
    (hs : ∀ x, w x ≠ 0 → rayDivides 3 x) (hψ : ∀ r, ‖ψ r‖ ≤ 1) (x : RayResidue 7) :
    ‖w x‖ ≤ 1 := by
  by_cases hz : w x = 0
  · simp [hz]
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, ha⟩ := (rayDivides_mk (by decide) m).mp (hs _ hz)
  rw [ha, hw]
  exact norm_primaryRayWeight_le_one hψ _

open scoped Classical in
/-- One fixed projector works for all scales and tests having the same fixed ray function.
The zero fiber sums exclude the cusps with insufficient ramification at three. -/
theorem exists_completedSum_projection (hR : DunnRadziwillReciprocity)
    (ψ : (𝓔 ⧸ span {(72:𝓔)}) → ℂ) :
    ∃ φ : RayResidue 7 → ℂ,
      (∀ y, ∑ x with rayReduction x = y, φ x = 0) ∧
      (∀ g : RayResidue 3 → ℂ, ∑ x, φ x * g (rayReduction x) = 0) ∧
      ((∀ r, ‖ψ r‖ ≤ 1) → ∀ x, ‖φ x‖ ≤ 1 + Fintype.card (RayResidue 7)) ∧
      ∀ {τ : ℂ → ℂ}, PattersonCoefficients τ → ∀ T : 𝓔 → ℂ,
      ∀ {I : TestInterval} {j : ℕ} {V : ℝ → ℂ}, UnitTest I j V → ∀ {X : ℝ}, 0 < X →
      ∀ (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔),
        (∀ n : Ideal 𝓔, AwayFromSix n → twist ξ k f n =
          ψ (Ideal.Quotient.mk _ (generator n)) * T (eisLambda^3 * generator n)) →
        completedSum ξ V X k f = projectedPattersonSum τ φ T V X := by
  obtain ⟨w, hw, hs⟩ := exists_primaryRayWeight hR ψ
  obtain ⟨φ, hφ, hzero, horth, hbound⟩ := exists_rayProjection w hs
  refine ⟨φ, hzero, horth, ?_, ?_⟩
  · intro hψ x
    apply (hbound x).trans
    have H := norm_lift_le_one hw hs hψ
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun z _ => H z)
    simpa using add_le_add (H x) hsum
  intro τ hτ T I j V hV X hX ξ k f hfac
  exact completed_eq_projected hτ hw hs hφ T hV hX ξ k f hfac


/-- Product of the zero-extended tame local factors on the integral numerator. -/
def numeratorTameProduct (P : Finset (Ideal 𝓔)) (e : Ideal 𝓔 → ℕ) (m : 𝓔) : ℂ :=
  ∏ p ∈ P, ReflectionTwist.localFactor p (e p) m

theorem numeratorTameProduct_mul (P : Finset (Ideal 𝓔)) (e : Ideal 𝓔 → ℕ)
    (hP : ∀ p ∈ P, AwayFromSix p) (a b : 𝓔) :
    numeratorTameProduct P e (a*b) = numeratorTameProduct P e a * numeratorTameProduct P e b := by
  classical
  rw [numeratorTameProduct, numeratorTameProduct, numeratorTameProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [ReflectionTwist.localFactor, dite_eq_left (hP p hp), ReflectionTwist.tame, map_mul]

/-- Switching from the primary element to its integral numerator multiplies the
tame product by a fixed scalar of modulus one. -/
theorem norm_numeratorTameProduct_lambda_cube (P : Finset (Ideal 𝓔)) (e : Ideal 𝓔 → ℕ)
    (hP : ∀ p ∈ P, AwayFromSix p) : ‖numeratorTameProduct P e (eisLambda^3)‖ = 1 := by
  classical
  rw [numeratorTameProduct, norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  have hg := hP p hp
  let := Ring.HasFiniteQuotients.finiteQuotient hg.1
  let := Fintype.ofFinite (𝓔 ⧸ p)
  let u := ((isUnit_mk_iff_coprime_span p eisLambda).mpr (coprime_span_lambda hg)).unit
  let χ := sexticChar hg ^ (e p % 6)
  have hu : (u : 𝓔 ⧸ p) = Ideal.Quotient.mk p eisLambda := IsUnit.unit_spec _
  have hh : ‖χ (u^3 : (𝓔 ⧸ p)ˣ)‖ = 1 := norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity _)
  simpa only [ReflectionTwist.localFactor, dite_eq_left hg, ReflectionTwist.tame, map_pow,
    χ, Units.val_pow_eq_pow_val, hu] using hh

theorem projectedPattersonSum_const_mul (τ : ℂ → ℂ) (φ : RayResidue 7 → ℂ) (T : 𝓔 → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (u : ℂ) :
    projectedPattersonSum τ φ (fun m => u*T m) V X = u * projectedPattersonSum τ φ T V X := by
  unfold projectedPattersonSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  ring

open scoped Classical in
/-- One fixed ray projector suffices for every finite tame product with the same
exceptional character. The correction for `λ³` is an exterior unit scalar. -/
theorem exists_tameProduct_projection (hR : DunnRadziwillReciprocity)
    (ψ : (𝓔 ⧸ span {(72:𝓔)}) → ℂ) :
    ∃ φ : RayResidue 7 → ℂ,
      (∀ g : RayResidue 3 → ℂ, ∑ x, φ x * g (rayReduction x) = 0) ∧
      ((∀ r, ‖ψ r‖ ≤ 1) → ∀ x, ‖φ x‖ ≤ 1 + Fintype.card (RayResidue 7)) ∧
      ∀ {τ : ℂ → ℂ}, PattersonCoefficients τ → ∀ (P : Finset (Ideal 𝓔)) (e : Ideal 𝓔 → ℕ),
      (∀ p ∈ P, AwayFromSix p) → ∀ {I : TestInterval} {j : ℕ} {V : ℝ → ℂ}, UnitTest I j V →
      ∀ {X : ℝ}, 0 < X → ∀ (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔),
        (∀ n : Ideal 𝓔, AwayFromSix n → twist ξ k f n =
          ψ (Ideal.Quotient.mk _ (generator n)) * numeratorTameProduct P e (generator n)) →
        completedSum ξ V X k f = (numeratorTameProduct P e (eisLambda^3))⁻¹ *
          projectedPattersonSum τ φ (numeratorTameProduct P e) V X := by
  obtain ⟨φ, -, horth, hbnd, hproj⟩ := exists_completedSum_projection hR ψ
  refine ⟨φ, horth, hbnd, ?_⟩
  intro τ ht P e hP I j V hV X hX ξ k f hfac
  let T := numeratorTameProduct P e
  have hne : T (eisLambda^3) ≠ 0 := norm_ne_zero_iff.mp
    ((norm_numeratorTameProduct_lambda_cube P e hP).trans_ne one_ne_zero)
  rw [← projectedPattersonSum_const_mul]
  apply hproj ht _ hV hX ξ k f
  intro n hn
  rw [hfac n hn, numeratorTameProduct_mul P e hP, inv_mul_cancel_left₀ hne]

end Masullo.QRH.MeanSquare
