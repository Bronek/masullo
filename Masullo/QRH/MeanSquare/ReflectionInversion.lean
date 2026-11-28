import Masullo.QRH.MeanSquare.ReflectionCRT
import Masullo.QRH.MeanSquare.ReflectionSmoothed
import Masullo.QRH.MeanSquare.ReflectionProjection

/-! # Finite Fourier inversion of the smoothed Patterson series -/

noncomputable section

open NumberField Ideal Finset Complex
open scoped ComplexConjugate Function

namespace Masullo.QRH.MeanSquare.ReflectionInversion

open ReflectionCRT
local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Index := {m : 𝓔 // m ≠ 0}

def inputMode (τ : ℂ → ℂ) (V : ℝ → ℂ) (X : ℝ) (m : 𝓔) : ℂ :=
  pattersonAngularCoefficient τ true 0 m * V (normSq (pattersonFrequency m) / X) / Real.sqrt X

def dualMode (τ : ℂ → ℂ) (V : ℝ → ℂ) (X : ℝ) (c : 𝓔) (m : 𝓔) : ℂ :=
  pattersonAngularCoefficient τ false 0 m / Real.sqrt (normSq (pattersonFrequency m)) *
    reflectionKernel V 0 0 (normSq (pattersonFrequency m)*X/(‖eisEmbedding c‖^2)^2)

private def angularScalar (c : 𝓔) : ℂ := -(‖eisEmbedding c‖^2 : ℝ) / eisEmbedding c^2

private lemma angularScalar_norm {c : 𝓔} (hc : c ≠ 0) : ‖angularScalar c‖ = 1 := by
  have hz := norm_ne_zero_iff.mpr ((map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc)
  simp [angularScalar, norm_pow, hz]

private lemma angular_translate (τ : ℂ → ℂ) (barred : Bool) (z : ℂ) (m : 𝓔) :
    pattersonAngularCoefficient τ barred z m =
      pattersonCharacter (pattersonFrequency m*z) * pattersonAngularCoefficient τ barred 0 m := by
  simp only [pattersonAngularCoefficient, mul_zero, pattersonCharacter, zero_re, mul_zero,
    ofReal_zero, exp_zero, mul_one]
  ring

private theorem finite_linear {ι α : Type*} [Fintype ι] (C : ι → ℂ) (f : ι → α → ℂ)
    (hf : ∀ i, Summable (f i)) :
    (∑' m, ∑ i, C i * f i m) = ∑ i, C i * ∑' m, f i m := by
  rw [Summable.tsum_finsetSum (f := fun i m => C i * f i m)
    (fun i _ => (hf i).mul_left _)]
  simp_rw [tsum_mul_left]

private lemma input_finite {V : ℝ → ℂ} {X : ℝ}
    (h : Function.HasFiniteSupport fun m : Index => V (normSq (pattersonFrequency m)/X))
    (τ : ℂ → ℂ) (g : 𝓔 → ℂ) :
    Summable fun m : Index => g m * inputMode τ V X m := by
  apply summable_of_hasFiniteSupport
  apply h.subset
  intro m hm
  contrapose hm
  simp only [Function.notMem_support] at hm ⊢
  simp [inputMode, hm]

private lemma smoothed_input (τ : ℂ → ℂ) (V : ℝ → ℂ) (X : ℝ) (z : ℂ) :
    pattersonSmoothed τ z V X =
      ∑' m : Index, pattersonCharacter (pattersonFrequency m*z) * inputMode τ V X m := by
  apply tsum_congr
  intro m
  rw [angular_translate]
  unfold inputMode
  ring

attribute [local instance] Ideal.Quotient.field

section Active

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Moduli ι)
variable [∀ i, (span {S.p i}).IsMaximal] [∀ i, Fintype (Residue (S.p i))]
variable [∀ i, DecidableEq (Residue (S.p i))]

/-- Contribution of the nonzero Fourier coordinates at a single prime. -/
def activeInput {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (j : ℕ) (ψ : AddChar F ℂ) (x : F) : ℂ :=
  ∑ u : Fˣ, ReflectionTame.coefficient (χ^j) ψ u * ψ ((u : F)*x)

/-- Smoothed reflection for one fixed translate and one fixed active set. The
scalar depends on the row and is independent of the dual frequency and test. -/
theorem smoothed_active {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    (hχ : PattersonAutomorphyWith pattersonMultiplier θ) (hB : DLMFBesselMellin) (hΓ : DLMFGammaVertical)
    (hR : DunnRadziwillReciprocity) (hgood : ∀ i, AwayFromSix (span {S.p i}))
    (hp : ∀ i, Prime (span {S.p i})) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ C : ℂ, ‖C‖ = 1 ∧ ∀ {J : TestInterval} {V : ℝ → ℂ} {X : ℝ}, UnitTest J 6 V → 0 < X →
      Function.HasFiniteSupport (fun m : Index => V (normSq (pattersonFrequency m)/X)) →
      (∑' m : Index, (pattersonCharacter (pattersonFrequency m*(eisEmbedding S.a₀/eisEmbedding S.c₀)) *
        ∏ i, activeInput (sexticChar (hgood i)) (j i) (phase (S.p i)) (red (S.p i) m)) *
        inputMode τ V X m) =
      C * ∑' m : Index, (Moduli.fixedWeight S.c₀ S.a₀ S.r m *
        ∏ i, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m)) *
        dualMode τ V X (S.c₀*S.r) m := by
  obtain ⟨H,b,d,C,hC,hm,hf⟩ := S.exists_activeBlock_eq_factor hR hgood hp j hj
  let c := S.c₀*S.r
  have hc : c ≠ 0 := mul_ne_zero S.c₀_ne_zero S.r_ne_zero
  refine ⟨angularScalar c*C, by rw [norm_mul, angularScalar_norm hc, hC, one_mul], ?_⟩
  intro J V X hV hX hfin
  let A (u : ∀ i, (Residue (S.p i))ˣ) := S.numerator (H u)
  let coeff (u : ∀ i, (Residue (S.p i))ˣ) :=
    ∏ i, ReflectionTame.coefficient ((sexticChar (hgood i))^(j i)) (phase (S.p i)) (u i)
  let Z (u : ∀ i, (Residue (S.p i))ˣ) := eisEmbedding (A u)/eisEmbedding c
  let Z' (u : ∀ i, (Residue (S.p i))ˣ) := -eisEmbedding (d u)/eisEmbedding c
  let M (u : ∀ i, (Residue (S.p i))ˣ) := conj (pattersonMultiplier (A u) c)
  let Φ (z : ℂ) (m : Index) := pattersonCharacter (pattersonFrequency m*z)
  have hpre (m : Index) :
      pattersonCharacter (pattersonFrequency m*(eisEmbedding S.a₀/eisEmbedding S.c₀)) *
        (∏ i, activeInput (sexticChar (hgood i)) (j i) (phase (S.p i)) (red (S.p i) m)) =
      ∑ u, coeff u * Φ (Z u) m := by
    simp only [activeInput, Fintype.prod_sum, Finset.mul_sum]
    apply sum_congr rfl
    intro u _
    have h := S.input_phase (H u) m
    rw [show Φ (Z u) m = _ from h]
    simp only [(hm u).1, prod_mul_distrib, coeff, pattersonFrequency]
    ring
  have hone (u : ∀ i, (Residue (S.p i))ˣ) :
      pattersonSmoothed τ (Z u) V X =
      angularScalar c * M u * ∑' m : Index, Φ (Z' u) m * dualMode τ V X c m := by
    rw [he.smoothed_reflection ht hχ hB hΓ (hm u).2.1 (S.numerator_primary _) (hm u).2.2.1
      (dvd_mul_of_dvd_left S.three_dvd_c₀ _) (hm u).2.2.2 hc hV hX]
    congr 1
    · dsimp [pattersonCuspScalar, angularScalar, M]
      push_cast
      ring
    · apply tsum_congr
      intro m
      rw [angular_translate]
      dsimp only [dualMode, Φ, Z']
      ring
  have hsumdual (u : ∀ i, (Residue (S.p i))ˣ) :
      Summable fun m : Index => Φ (Z' u) m * dualMode τ V X c m := by
    have h := (ht.summable_smoothed_dual hΓ hV (Z' u) hX (show 0 < ‖eisEmbedding c‖^2 by
      have := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
      positivity)).of_norm
    apply h.congr
    intro m
    rw [angular_translate]
    dsimp only [dualMode, Φ]
    ring
  calc
    _ = ∑' m : Index, ∑ u, coeff u * (Φ (Z u) m * inputMode τ V X m) := by
      apply tsum_congr
      intro m
      rw [hpre, sum_mul]
      simp only [mul_assoc]
    _ = ∑ u, coeff u * pattersonSmoothed τ (Z u) V X := by
      rw [finite_linear coeff _ (fun u => input_finite hfin τ (fun m => pattersonCharacter (pattersonFrequency m*Z u)))]
      simp only [smoothed_input]
    _ = angularScalar c * ∑' m : Index, S.activeBlock hgood j H d m * dualMode τ V X c m := by
      simp_rw [hone]
      rw [show (∑' m : Index, S.activeBlock hgood j H d m * dualMode τ V X c m) =
        ∑ u, (coeff u * M u) * ∑' m : Index, Φ (Z' u) m * dualMode τ V X c m from ?_]
      · rw [Finset.mul_sum]
        apply sum_congr rfl
        intro u _
        ring
      · rw [← finite_linear _ _ hsumdual]
        apply tsum_congr
        intro m
        rw [Moduli.activeBlock, sum_mul]
        apply sum_congr rfl
        intro u _
        dsimp only [coeff, M, Φ, A, c, Z', pattersonFrequency]
        ring
    _ = _ := by
      simp_rw [hf, mul_assoc]
      rw [tsum_mul_left, ← mul_assoc]

private def inactive {F : Type*} [Fintype F] (j : ℕ) : ℂ :=
  if j = 0 then 1 - (Fintype.card F : ℂ)⁻¹ else 0

private lemma split_prime {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 6) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {j : ℕ} (hj : j < 6) (x : F) :
    (χ^j) x = activeInput χ j ψ x + inactive (F := F) j := by
  let f (h : F) := ReflectionTame.coefficient (χ^j) ψ h * ψ (h*x)
  calc
    _ = ∑ h, f h := (ReflectionTame.inversion (χ^j) hψ x).symm
    _ = _ := by
      rw [Fintype.sum_eq_add_sum_subtype_ne f 0,
        ← unitsEquivNeZero.sum_comp (fun u : {h : F // h ≠ 0} => f u)]
      simp [f, ReflectionTame.coefficient_zero_pow hχ ψ hj, activeInput, inactive, add_comm]

/-- Product of the Fourier coefficients at zero outside an active set. -/
def inactiveWeight (p : ι → 𝓔) [∀ i, Fintype (Residue (p i))] (j : ι → ℕ) (s : Finset ι) : ℂ :=
  ∏ i ∈ sᶜ, inactive (F := Residue (p i)) (j i)

theorem inactiveWeight_eq_zero {p : ι → 𝓔} [∀ i, Fintype (Residue (p i))] {j : ι → ℕ}
    {s : Finset ι} {i : ι} (hi : i ∉ s) (hj : j i ≠ 0) : inactiveWeight p j s = 0 :=
  Finset.prod_eq_zero (Finset.mem_compl.mpr hi) (by simp [inactive, hj])

theorem norm_inactiveWeight_le_one {p : ι → 𝓔} [∀ i, Fintype (Residue (p i))]
    (j : ι → ℕ) (s : Finset ι) : ‖inactiveWeight p j s‖ ≤ 1 := by
  rw [inactiveWeight, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  by_cases hj : j i = 0
  · have hq : 1 ≤ (Fintype.card (Residue (p i)) : ℝ) := by exact_mod_cast Fintype.card_pos
    have hle : (Fintype.card (Residue (p i)) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
    simp only [inactive, hj, ↓reduceIte]
    rw [← ofReal_natCast, ← ofReal_inv, ← ofReal_one, ← ofReal_sub,
      norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact sub_le_self _ (by positivity)
  · simp [inactive, hj]

private def restrict (s : Finset ι) : Moduli s where
  a₀ := S.a₀
  c₀ := S.c₀
  p i := S.p i.1
  c₀_ne_zero := S.c₀_ne_zero
  primary_a₀ := S.primary_a₀
  three_dvd_c₀ := S.three_dvd_c₀
  fixed_coprime := S.fixed_coprime
  primary_p i := S.primary_p i.1
  tame_coprime i := S.tame_coprime i.1
  pairwise _ _ hik := S.pairwise (fun h => hik (Subtype.ext h))

/-- Fourier inversion at all tame primes, grouped by the subset with nonzero
Fourier coordinate. The inactive scalar vanishes unless every omitted exponent is zero. -/
theorem smoothed_tame {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    (hχ : PattersonAutomorphyWith pattersonMultiplier θ) (hB : DLMFBesselMellin) (hΓ : DLMFGammaVertical)
    (hR : DunnRadziwillReciprocity) (hgood : ∀ i, AwayFromSix (span {S.p i}))
    (hp : ∀ i, Prime (span {S.p i})) (j : ι → ℕ) (hj : ∀ i, j i < 6) :
    ∃ C : Finset ι → ℂ, (∀ s, ‖C s‖ = 1) ∧ ∀ {J : TestInterval} {V : ℝ → ℂ} {X : ℝ},
      UnitTest J 6 V → 0 < X →
      Function.HasFiniteSupport (fun m : Index => V (normSq (pattersonFrequency m)/X)) →
      (∑' m : Index, (pattersonCharacter (pattersonFrequency m*(eisEmbedding S.a₀/eisEmbedding S.c₀)) *
        ∏ i, (sexticChar (hgood i) ^ j i) (red (S.p i) m)) * inputMode τ V X m) =
      ∑ s : Finset ι, inactiveWeight S.p j s * C s * ∑' m : Index,
        (Moduli.fixedWeight S.c₀ S.a₀ (∏ i ∈ s, S.p i) m *
        ∏ i ∈ s, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m)) *
        dualMode τ V X (S.c₀*∏ i ∈ s, S.p i) m := by
  let (s : Finset ι) (i : s) : (span {(restrict S s).p i}).IsMaximal :=
    inferInstanceAs ((span {S.p i.1}).IsMaximal)
  let (s : Finset ι) (i : s) : Fintype (Residue ((restrict S s).p i)) :=
    inferInstanceAs (Fintype (Residue (S.p i.1)))
  let (s : Finset ι) (i : s) : DecidableEq (Residue ((restrict S s).p i)) :=
    inferInstanceAs (DecidableEq (Residue (S.p i.1)))
  choose C hC heq using fun s : Finset ι => smoothed_active (restrict S s) he ht hχ hB hΓ hR
    (fun i => hgood i.1) (fun i => hp i.1) (fun i => j i.1) (fun i => hj i.1)
  refine ⟨C, hC, ?_⟩
  intro J V X hV hX hfin
  let P (m : 𝓔) := pattersonCharacter (pattersonFrequency m*(eisEmbedding S.a₀/eisEmbedding S.c₀))
  let A (i : ι) (m : 𝓔) := activeInput (sexticChar (hgood i)) (j i) (phase (S.p i)) (red (S.p i) m)
  have hψ (i : ι) : (phase (S.p i)).IsPrimitive := by
    rw [phase_eq_quotientDifferentCharacter (S.primary_p i)]
    exact quotientDifferentCharacter_isPrimitive (hgood i).1
  calc
    _ = ∑' m : Index, ∑ s : Finset ι,
        inactiveWeight S.p j s * ((P m * ∏ i ∈ s, A i m) * inputMode τ V X m) := by
      apply tsum_congr
      intro m
      simp_rw [fun i => split_prime (orderOf_sexticChar_prime (hgood i) (hp i)) (hψ i) (hj i)
        (red (S.p i) m)]
      rw [Fintype.prod_add, Finset.mul_sum, Finset.sum_mul]
      apply sum_congr rfl
      intro s _
      dsimp only [inactiveWeight, P, A]
      ring
    _ = ∑ s : Finset ι, inactiveWeight S.p j s *
        ∑' m : Index, (P m * ∏ i ∈ s, A i m) * inputMode τ V X m :=
      finite_linear _ _ fun s => input_finite hfin τ (fun m => P m * ∏ i ∈ s, A i m)
    _ = _ := by
      apply sum_congr rfl
      intro s _
      rw [mul_assoc]
      congr 1
      have h := heq s hV hX hfin
      change (∑' m : Index, (P m * ∏ i : s, A i.1 m) * inputMode τ V X m) =
        C s * ∑' m : Index, (Moduli.fixedWeight S.c₀ S.a₀ (∏ i : s, S.p i) m *
          ∏ i : s, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m)) *
          dualMode τ V X (S.c₀ * ∏ i : s, S.p i) m at h
      have hA (m : 𝓔) : (∏ i : s, A i.1 m) = ∏ i ∈ s, A i m :=
        prod_finset_coe (fun i => A i m) s
      have hF (m : 𝓔) :
          (∏ i : s, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m)) =
            ∏ i ∈ s, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m) :=
        prod_finset_coe (fun i => ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (S.p i) m)) s
      have hr : (∏ i : s, S.p i) = ∏ i ∈ s, S.p i := prod_finset_coe S.p s
      simp_rw [hA, hF, hr] at h
      exact h

end Active

/-- Surviving characters of the fixed exceptional quotient. -/
abbrev RaySupport (φ : RayResidue 7 → ℂ) := {h : RayResidue 7 // rayFourierCoeff 7 φ h ≠ 0}

open scoped Classical

/-- A reduced representative of a fixed exceptional translate, independent of the tame primes. -/
structure FixedCusp (h : RayResidue 7) where
  a : 𝓔
  c : 𝓔
  c_ne_zero : c ≠ 0
  primary : eisPrimary a
  three_dvd : (3 : 𝓔) ∣ c
  coprime : IsCoprime a c
  dvd_modulus : c ∣ 8*eisLambda^7
  shift_eq : rayShift h = eisEmbedding a / eisEmbedding c

def fixedCusp {φ : RayResidue 7 → ℂ}
    (hφ : ∀ g : RayResidue 3 → ℂ, ∑ x, φ x * g (rayReduction x) = 0) (h : RaySupport φ) :
    FixedCusp h.1 := Classical.choice (by
  obtain ⟨a,c,hc,ha,h₃,hac,hd,he⟩ := exists_fixed_cusp hφ h.2
  exact ⟨⟨a,c,hc,ha,h₃,hac,hd,he⟩⟩)

private lemma ray_inversion (φ : RayResidue 7 → ℂ) (m : 𝓔) :
    φ (Ideal.Quotient.mk (rayModulus 7) m) =
      ∑ h : RaySupport φ, rayFourierCoeff 7 φ h.1 * pattersonCharacter (pattersonFrequency m*rayShift h.1) := by
  let f (h : RayResidue 7) := rayFourierCoeff 7 φ h * rayAddChar 7 (h*Ideal.Quotient.mk _ m)
  have he := Fintype.sum_subtype_add_sum_subtype (fun h => rayFourierCoeff 7 φ h ≠ 0) f
  have hz : ∀ h : {h : RayResidue 7 // ¬ rayFourierCoeff 7 φ h ≠ 0}, f h = 0 :=
    fun h => by simp [f, not_ne_iff.mp h.2]
  rw [sum_eq_zero (fun i _ => hz i), add_zero] at he
  rw [← rayFourier_inversion 7 φ _, ← he]
  simp only [f, rayAddChar_eq_translate, pattersonFrequency]

section Projected

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → 𝓔)
variable [∀ i, (span {p i}).IsMaximal] [∀ i, Fintype (Residue (p i))]
variable [∀ i, DecidableEq (Residue (p i))]

/-- Equation (14) for a projected Patterson sum. The fixed representatives are
chosen once for each surviving exceptional Fourier character. Each row has one
unit scalar, the explicit inactive coefficient, and the product of the tame table entries. -/
theorem projected_inversion {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    (hχ : PattersonAutomorphyWith pattersonMultiplier θ) (hB : DLMFBesselMellin) (hΓ : DLMFGammaVertical)
    (hR : DunnRadziwillReciprocity) (hgood : ∀ i, AwayFromSix (span {p i}))
    (hprime : ∀ i, Prime (span {p i})) (hprimary : ∀ i, eisPrimary (p i))
    (hcop : Pairwise (IsCoprime on p)) (j : ι → ℕ) (hj : ∀ i, j i < 6)
    {φ : RayResidue 7 → ℂ} (hφ : ∀ g : RayResidue 3 → ℂ, ∑ x, φ x * g (rayReduction x) = 0) :
    ∃ C : RaySupport φ → Finset ι → ℂ, (∀ h s, ‖C h s‖ = 1) ∧
      ∀ {J : TestInterval} {V : ℝ → ℂ} {X : ℝ}, UnitTest J 6 V → 0 < X →
        projectedPattersonSum τ φ (fun m => ∏ i, (sexticChar (hgood i)^j i) (red (p i) m)) V X =
        ∑ h : RaySupport φ, rayFourierCoeff 7 φ h.1 * ∑ s : Finset ι,
          inactiveWeight p j s * C h s * ∑' m : Index,
          (Moduli.fixedWeight (fixedCusp hφ h).c (fixedCusp hφ h).a (∏ i ∈ s, p i) m *
            ∏ i ∈ s, ReflectionTame.factor (sexticChar (hgood i)) (j i) (red (p i) m)) *
            dualMode τ V X ((fixedCusp hφ h).c * ∏ i ∈ s, p i) m := by
  let S (h : RaySupport φ) : Moduli ι :=
    ⟨(fixedCusp hφ h).a, (fixedCusp hφ h).c, p, (fixedCusp hφ h).c_ne_zero, (fixedCusp hφ h).primary,
      (fixedCusp hφ h).three_dvd, (fixedCusp hφ h).coprime, hprimary,
      fun i => good_coprime_fixed (hgood i) (fixedCusp hφ h).dvd_modulus, hcop⟩
  choose C hC heq using fun h : RaySupport φ => smoothed_tame (S h) he ht hχ hB hΓ hR hgood hprime j hj
  refine ⟨C, hC, ?_⟩
  intro J V X hV hX
  have hfin := pattersonTest_hasFiniteSupport hV hX
  let T (m : 𝓔) := ∏ i, (sexticChar (hgood i)^j i) (red (p i) m)
  let F (h : RaySupport φ) (m : 𝓔) := pattersonCharacter (pattersonFrequency m*rayShift h.1) * T m
  calc
    _ = ∑' m : Index, ∑ h : RaySupport φ, rayFourierCoeff 7 φ h.1 * (F h m * inputMode τ V X m) := by
      unfold projectedPattersonSum
      apply tsum_congr
      intro m
      rw [ray_inversion φ (m : 𝓔), sum_mul, sum_mul]
      apply sum_congr rfl
      intro h _
      dsimp only [F, T, inputMode]
      ring
    _ = ∑ h : RaySupport φ, rayFourierCoeff 7 φ h.1 * ∑' m : Index, F h m * inputMode τ V X m :=
      finite_linear _ _ fun h => input_finite hfin τ (F h)
    _ = _ := by
      apply sum_congr rfl
      intro h _
      congr 1
      simpa only [F, T, (fixedCusp hφ h).shift_eq, S] using heq h hV hX hfin

end Projected

/-- A tame table entry expressed on an ideal and its integral numerator. -/
def idealFactor {q : Ideal 𝓔} (hq : AwayFromSix q) (j : ℕ) (m : 𝓔) : ℂ :=
  if j = 4 then (if m ∈ q then (absNorm q : ℂ)-1 else -1) / Real.sqrt (absNorm q)
  else if j = 0 then (sexticChar hq ^ 2)⁻¹ (Ideal.Quotient.mk q m) / Real.sqrt (absNorm q)
  else (sexticChar hq ^ (j+2))⁻¹ (Ideal.Quotient.mk q m)

theorem factor_eq_idealFactor {q : Ideal 𝓔} [q.IsMaximal] [Fintype (𝓔 ⧸ q)]
    [DecidableEq (𝓔 ⧸ q)] (hq : AwayFromSix q) (j : ℕ) (m : 𝓔) :
    ReflectionTame.factor (sexticChar hq) j (Ideal.Quotient.mk q m) = idealFactor hq j m := by
  rw [ReflectionTame.factor, idealFactor, Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card]
  simp only [Ideal.Quotient.eq_zero_iff_mem]

/-- Inactive coefficients for a finite set of prime ideals, expressed by their absolute norms. -/
def idealInactive {P : Finset (Ideal 𝓔)} (e : Ideal 𝓔 → ℕ) (s : Finset P) : ℂ :=
  ∏ q ∈ sᶜ, if e q % 6 = 0 then 1-(absNorm q.val : ℂ)⁻¹ else 0

/-- The row formula for the tame numerator product used in the completed-sum projection. -/
theorem projected_tameProduct {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    (hχ : PattersonAutomorphyWith pattersonMultiplier θ) (hB : DLMFBesselMellin) (hΓ : DLMFGammaVertical)
    (hR : DunnRadziwillReciprocity) (P : Finset (Ideal 𝓔)) (e : Ideal 𝓔 → ℕ)
    (hgood : ∀ q ∈ P, AwayFromSix q) (hprime : ∀ q ∈ P, Prime q)
    {φ : RayResidue 7 → ℂ} (hφ : ∀ g : RayResidue 3 → ℂ, ∑ x, φ x * g (rayReduction x) = 0) :
    ∃ C : RaySupport φ → Finset P → ℂ, (∀ h s, ‖C h s‖ = 1) ∧
      ∀ {J : TestInterval} {V : ℝ → ℂ} {X : ℝ}, UnitTest J 6 V → 0 < X →
        projectedPattersonSum τ φ (numeratorTameProduct P e) V X =
        ∑ h : RaySupport φ, rayFourierCoeff 7 φ h.1 * ∑ s : Finset P,
          idealInactive e s * C h s * ∑' m : Index,
          (Moduli.fixedWeight (fixedCusp hφ h).c (fixedCusp hφ h).a (∏ q ∈ s, generator q) m *
            ∏ q ∈ s, idealFactor (hgood q q.2) (e q % 6) m) *
            dualMode τ V X ((fixedCusp hφ h).c * ∏ q ∈ s, generator q) m := by
  let p (q : P) := generator q.val
  have hg (q : P) : AwayFromSix (span {p q}) := by simpa only [p, span_generator] using hgood q q.2
  have hp (q : P) : Prime (span {p q}) := by simpa only [p, span_generator] using hprime q q.2
  let (q : P) : (span {p q}).IsMaximal := ((Ideal.prime_iff_isPrime (hp q).ne_zero).mp (hp q)).isMaximal (hp q).ne_zero
  let (q : P) : Finite (Residue (p q)) := Ring.HasFiniteQuotients.finiteQuotient (hp q).ne_zero
  let (q : P) : Fintype (Residue (p q)) := Fintype.ofFinite _
  have hc : Pairwise (IsCoprime on p) := by
    intro i k hik
    apply (isCoprime_span_singleton_iff _ _).mp
    apply Ideal.isCoprime_of_isMaximal
    simpa only [p, span_generator, ne_eq, Subtype.val_inj] using hik
  let j (q : P) := e q % 6
  obtain ⟨C,hC,heq⟩ := projected_inversion p he ht hχ hB hΓ hR hg hp
    (fun i => eisPrimary_generator (hgood i i.2).coprime_three) hc j (fun _ => Nat.mod_lt _ (by decide)) hφ
  have hpre (q : P) (m : 𝓔) :
      (sexticChar (hg q)^j q) (red (p q) m) = ReflectionTwist.localFactor q (e q) m := by
    calc
      _ = ReflectionTwist.localFactor (span {p q}) (e q) m := by
        simp only [ReflectionTwist.localFactor, hg q, ↓reduceDIte, ReflectionTwist.tame, j, red]
      _ = _ := by simp only [p, span_generator]
  have hfac (q : P) (m : 𝓔) :
      ReflectionTame.factor (sexticChar (hg q)) (j q) (red (p q) m) = idealFactor (hgood q q.2) (j q) m := by
    rw [factor_eq_idealFactor]
    generalize_proofs h
    simp only [p, span_generator]
  have hzero (s : Finset P) : inactiveWeight p j s = idealInactive e s := by
    simp only [inactiveWeight, idealInactive, inactive, j]
    apply prod_congr rfl
    intro q _
    have hcard : Fintype.card (Residue (p q)) = absNorm q.val := by
      rw [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard]
      simp only [p, span_generator]
    rw [hcard]
  refine ⟨C,hC,?_⟩
  intro J V X hV hX
  have htame (m : 𝓔) : (∏ q : P, ReflectionTwist.localFactor q (e q) m) = numeratorTameProduct P e m :=
    prod_finset_coe (fun q => ReflectionTwist.localFactor q (e q) m) P
  simpa only [hpre, htame, hzero, hfac, p, j] using heq hV hX

end Masullo.QRH.MeanSquare.ReflectionInversion
