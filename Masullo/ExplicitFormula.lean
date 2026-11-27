import WeilExplicit.ExplicitFormula
import WeilExplicit.Convergence
import WeilExplicit.PrimeSupport
import Masullo.Strength

/-!
# The full zero expansion and the inner one

`TestFunction.hasSum_full` is Weil's explicit formula on the test functions of
`Masullo.Strength`. It holds unconditionally and restricts no zero. `innerExpansion_iff` measures
the claim that zeros close to the critical line alone account for the same functional.
-/

open Complex Set MeasureTheory
open scoped ContDiff FourierTransform

namespace Masullo
namespace TestFunction

/-- The logarithmic pullback `u ↦ φ(e^u)`. -/
noncomputable def pull (φ : TestFunction) (u : ℝ) : ℂ := φ.toFun (Real.exp u)

lemma pull_contDiff (φ : TestFunction) : ContDiff ℝ 2 φ.pull :=
  (contDiff_infty.1 φ.contDiff 2).comp Real.contDiff_exp

lemma pull_zero (φ : TestFunction) {u : ℝ} (hu : u ≤ 0) : φ.pull u = 0 := by
  by_contra h
  have := φ.tsupport_subset (subset_tsupport _ (Function.mem_support.2 h))
  exact absurd (mem_Ioi.1 this) (not_lt.2 (Real.exp_le_one_iff.2 hu))

lemma pull_hasCompactSupport (φ : TestFunction) : HasCompactSupport φ.pull := by
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.isCompact.bddAbove
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := M)) fun u hu => ?_
  by_contra h
  have h1 := hM (subset_tsupport _ (Function.mem_support.2 h))
  refine hu ⟨le_of_not_gt fun h0 => h (φ.pull_zero h0.le), ?_⟩
  linarith [Real.add_one_le_exp u]

lemma transform_pull (φ : TestFunction) (z : ℂ) :
    WeilExplicit.transform φ.pull (z / I) = φ.hat z := by
  simpa only [hat, pull, WeilExplicit.transform, mul_div_cancel₀ _ I_ne_zero,
    mul_div_cancel_left₀ _ I_ne_zero] using (Spectrum.mellin_eq_integral φ.toFun z).symm

/-- The transform is entire. -/
lemma differentiable_hat (φ : TestFunction) : Differentiable ℂ φ.hat := by
  have h := (WeilExplicit.differentiable_transform φ.pull_contDiff.continuous
    φ.pull_hasCompactSupport).comp (differentiable_id.div_const I)
  exact (funext fun z => (transform_pull φ z).symm : φ.hat = _) ▸ h

lemma continuous_hat (φ : TestFunction) : Continuous φ.hat :=
  φ.differentiable_hat.continuous

/-- A transform that does not vanish at one point vanishes at countably many points. -/
lemma countable_hat_eq_zero {z₀ : ℂ} {φ : TestFunction} (h : φ.hat z₀ ≠ 0) :
    {z | φ.hat z = 0}.Countable := by
  rcases (φ.differentiable_hat.differentiableOn.analyticOnNhd isOpen_univ)
    |>.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h0 | h0
  · exact absurd (h0 (mem_univ z₀)) h
  · have := (isDiscrete_of_codiscreteWithin (s := {z | φ.hat z = 0}) h0).to_subtype
    simpa using (TopologicalSpace.separableSpace_iff_countable.1 inferInstance :
      Countable ({z | φ.hat z = 0} ∩ univ : Set ℂ))

/-- Some nonnegative test function has transform nonzero on a given countable set. It is a
nonnegative bump tilted by a real power `x ^ r`, whose transform is that of the bump shifted by
`r`; the transform of the bump has countably many zeros, so all but countably many `r` qualify. -/
lemma exists_nonneg_hat_ne_zero_on {S : Set ℂ} (hS : S.Countable) :
    ∃ φ : TestFunction, φ.Nonneg ∧ ∀ z ∈ S, φ.hat z ≠ 0 := by
  obtain ⟨b, hb, hb1⟩ := exists_nonneg_hat_one
  have hB : (⋃ z ∈ S, (fun r : ℝ => z + r) ⁻¹' {w | b.hat w = 0}).Countable :=
    hS.biUnion fun z _ =>
      (countable_hat_eq_zero hb1).preimage ((add_right_injective _).comp ofReal_injective)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r ∉ ⋃ z ∈ S, (fun r : ℝ => z + r) ⁻¹' {w | b.hat w = 0} := by
    by_contra! h
    exact Cardinal.not_countable_real (hB.mono fun r _ => h r)
  refine ⟨b.tilt r, hb.tilt r, fun z hz h0 => hr (mem_iUnion₂.2 ⟨z, hz, ?_⟩)⟩
  rwa [hat_tilt] at h0

/-- The functional of Weil's explicit formula: two pole terms, the prime powers weighted by the
von Mangoldt function, and the archimedean term as an integral over the critical line, with the
real part of the digamma function at `1/4 + i r / 2` and `log π`. -/
noncomputable def efFunctional (φ : TestFunction) : ℂ :=
  φ.hat (-1 / 2) + φ.hat (1 / 2)
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * φ.toFun n
  + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ,
      φ.hat (I * r) * (((digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ)

lemma pull_prime_term (φ : TestFunction) (n : ℕ) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (φ.pull (Real.log n) + φ.pull (-Real.log n)) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * φ.toFun n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : φ.pull (-Real.log n) = 0 :=
      φ.pull_zero (neg_nonpos.2 (Real.log_nonneg (by exact_mod_cast hn)))
    rw [h2, add_zero, pull, Real.exp_log h1]

lemma pull_archimedean (φ : TestFunction) (r : ℝ) :
    WeilExplicit.transform φ.pull r = φ.hat (I * r) := by
  rw [← transform_pull, mul_div_cancel_left₀ _ I_ne_zero]

/-- The prime terms of `efFunctional` have finite support. -/
lemma efFunctional_primeTerm_hasFiniteSupport (φ : TestFunction) :
    (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * φ.toFun n)
      |>.HasFiniteSupport := by
  have h := WeilExplicit.prime_sum_finite_support φ.pull_hasCompactSupport
  simpa only [pull_prime_term] using h

/-- The archimedean integrand of `efFunctional` is integrable. -/
lemma efFunctional_integrable (φ : TestFunction) :
    Integrable fun r : ℝ =>
      φ.hat (I * r) * (((digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ) := by
  simpa only [pull_archimedean] using
    WeilExplicit.integrable_archimedean φ.pull_contDiff φ.pull_hasCompactSupport

lemma explicit_rhs_pull (φ : TestFunction) :
    WeilExplicit.transform φ.pull (I / 2) + WeilExplicit.transform φ.pull (-I / 2) -
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (φ.pull (Real.log n) + φ.pull (-Real.log n))) +
      (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, WeilExplicit.transform φ.pull t *
        (((digamma (1 / 4 + I * t / 2)).re - Real.log Real.pi : ℝ) : ℂ) = φ.efFunctional := by
  have e1 : I / 2 = (-1 / 2 : ℂ) / I := by
    rw [eq_div_iff I_ne_zero, div_mul_eq_mul_div, I_mul_I]
  have e2 : -I / 2 = (1 / 2 : ℂ) / I := by
    rw [eq_div_iff I_ne_zero, div_mul_eq_mul_div, neg_mul, I_mul_I, neg_neg]
  rw [e1, e2, transform_pull, transform_pull, efFunctional]
  simp only [pull_prime_term, pull_archimedean]

/-- **Weil's explicit formula.** The sum over all zeros in the critical strip, with multiplicity,
converges absolutely to `efFunctional φ`. The analytic input is `WeilExplicit.explicit_formula`. -/
theorem hasSum_full (φ : TestFunction) :
    HasSum (fun ρ : stripZeros => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2))
      φ.efFunctional := by
  have h := WeilExplicit.explicit_formula φ.pull_contDiff φ.pull_hasCompactSupport
  rw [explicit_rhs_pull] at h
  refine h.congr_fun fun ρ => ?_
  rw [transform_pull]

end TestFunction

/-- The zeros at distance less than `a` from the critical line account for the whole explicit
formula functional. -/
def InnerExpansion (a : ℝ) : Prop :=
  ∀ φ : TestFunction,
    HasSum (fun ρ : innerZeros a => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) φ.efFunctional

/-- **Theorem C.** The inner expansion holds at width `a` iff there are no zeros in the critical
strip at distance at least `a` from the critical line. -/
theorem innerExpansion_iff (a : ℝ) :
    InnerExpansion a ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2| := by
  refine ⟨fun h => (zeroSumVanishes_iff a).1
    (zeroSumVanishes_of_full_of_inner a _ TestFunction.hasSum_full h), fun h φ => ?_⟩
  have e : innerZeros a = stripZeros := by
    ext ρ
    refine ⟨fun hρ => innerZeros_subset a hρ, fun hρ => ⟨hρ.1, hρ.2.1, hρ.2.2, ?_⟩⟩
    exact lt_of_not_ge fun hge => h ⟨ρ, hρ.1, hρ.2.1, hρ.2.2, hge⟩
  rw [e]
  exact φ.hasSum_full

/-- The inner expansion holds at every positive width iff the Riemann hypothesis holds. -/
theorem forall_innerExpansion_iff_riemannHypothesis :
    (∀ a > 0, InnerExpansion a) ↔ RiemannHypothesis := by
  rw [← forall_zeroSumVanishes_iff_riemannHypothesis]
  simp only [innerExpansion_iff, zeroSumVanishes_iff]

end Masullo
