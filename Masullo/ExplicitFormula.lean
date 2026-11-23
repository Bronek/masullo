import Zeta23.WeilEF.Main
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

lemma paperFT_pull (φ : TestFunction) (z : ℂ) :
    Zeta23.paperFT φ.pull (z / I) = φ.hat z := by
  rw [hat, mellin_eq_fourier, Real.fourier_eq', ← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hin : inner ℝ (-u) (z.im / (2 * Real.pi)) = z.im / (2 * Real.pi) * -u := rfl
  simp only [pull, neg_neg, smul_eq_mul, real_smul, hin]
  rw [ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  have h2 : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [mul_div_cancel₀ _ I_ne_zero]
  conv_lhs => rw [← re_add_im z]
  push_cast
  field_simp
  ring

/-- The functional of Weil's explicit formula: two pole terms, the prime powers weighted by the
von Mangoldt function, and the archimedean term as an integral over the critical line. -/
noncomputable def efFunctional (φ : TestFunction) : ℂ :=
  φ.hat (-1 / 2) + φ.hat (1 / 2)
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * φ.toFun n
  + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, φ.hat (I * r) * (Zeta23.EF.gammaBracket r : ℂ)

lemma literatureRHS_pull (φ : TestFunction) :
    Zeta23.EF.literatureRHS φ.pull = φ.efFunctional := by
  unfold Zeta23.EF.literatureRHS efFunctional
  have e1 : I / 2 = (-1 / 2 : ℂ) / I := by
    rw [eq_div_iff I_ne_zero, div_mul_eq_mul_div, I_mul_I]
  have e2 : -I / 2 = (1 / 2 : ℂ) / I := by
    rw [eq_div_iff I_ne_zero, div_mul_eq_mul_div, neg_mul, I_mul_I, neg_neg]
  rw [e1, e2, paperFT_pull, paperFT_pull]
  congr 2
  · refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (0 : ℝ) < n := by exact_mod_cast hn
      have h2 : φ.pull (-Real.log n) = 0 :=
        φ.pull_zero (neg_nonpos.2 (Real.log_nonneg (by exact_mod_cast hn)))
      rw [h2, add_zero, pull, Real.exp_log h1]
  · congr 1
    funext r
    rw [← paperFT_pull, mul_div_cancel_left₀ _ I_ne_zero]

/-- **Weil's explicit formula.** The sum over all zeros in the critical strip, with multiplicity,
converges absolutely to `efFunctional φ`. The analytic input is `EF_lit_zetaZeroConfig` from the
`Zeta23` package. -/
theorem hasSum_full (φ : TestFunction) :
    HasSum (fun ρ : stripZeros => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2))
      φ.efFunctional := by
  obtain ⟨hs, he⟩ := Zeta23.WeilEF.EF_lit_zetaZeroConfig φ.pull φ.pull_contDiff
    φ.pull_hasCompactSupport
  have h := hs.hasSum
  rw [he, literatureRHS_pull] at h
  refine h.congr_fun fun ρ => ?_
  rw [← paperFT_pull]
  rfl

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
    refine ⟨fun hρ => ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩, fun hρ => ⟨hρ.1, hρ.2.1, hρ.2.2, ?_⟩⟩
    exact lt_of_not_ge fun hge => h ⟨ρ, hρ.1, hρ.2.1, hρ.2.2, hge⟩
  rw [e]
  exact φ.hasSum_full

/-- The inner expansion holds at every positive width iff the Riemann hypothesis holds. -/
theorem forall_innerExpansion_iff_riemannHypothesis :
    (∀ a > 0, InnerExpansion a) ↔ RiemannHypothesis := by
  rw [← forall_zeroSumVanishes_iff_riemannHypothesis]
  simp only [innerExpansion_iff, zeroSumVanishes_iff]

end Masullo
