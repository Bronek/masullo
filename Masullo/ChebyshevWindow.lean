import Masullo.DirichletWindow

/-!
# The window criterion for Chebyshev's function

`ψ x = ∑_{n ≤ x} Λ(n)`. `WindowBound (fun x => ψ x - x) θ δ C` says that for arbitrarily large `Y`
there is a sign `ε = ±1` with `ε (ψ x - x) ≤ C x ^ θ` for all `x ∈ [Y, Y ^ (1 + δ)]`. With `θ ≥ 0`
it rules out zeros of zeta in `Re s > θ` (`riemannZeta_ne_zero_of_psiWindow`). The Laplace
transform of `ψ (e ^ u) - e ^ u` is `-ζ'(s) / (s ζ(s)) - 1 / (s - 1)`, which is
`-(1 + zetaNum'(s) / zetaNum(s)) / s` with `zetaNum s = (s - 1) ζ(s)`: the pole at `1` cancels, and
in `Re s > 0` the poles are the zeros of zeta, with residue `-m / ρ` at a zero of multiplicity `m`.
The argument is `Masullo.DirichletWindow.riemannZeta_ne_zero_of_continues`.

The exponent is exact: on paper the Riemann hypothesis gives `|ψ x - x| ≤ C x ^ θ` for every
`θ > 1 / 2`. That direction is not formalised.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt
open ArithmeticFunction (vonMangoldt_nonneg vonMangoldt_le_log
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div)

namespace Masullo.ChebyshevWindow

open Landau Window Spectrum WeilExplicit DirichletWindow

lemma psi_eq_partialSum (x : ℝ) : Chebyshev.psi x = partialSum (fun n => Λ n) x := by
  rw [Chebyshev.psi, partialSum, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

lemma psi_le_sq {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ x ^ 2 := by
  have hf := Nat.floor_le hx
  calc Chebyshev.psi x ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (⌊x⌋₊ : ℝ) := Finset.sum_le_sum fun n hn =>
        vonMangoldt_le_log.trans ((Real.log_le_self (Nat.cast_nonneg n)).trans
          (by exact_mod_cast (Finset.mem_Ioc.1 hn).2))
    _ = ⌊x⌋₊ * ⌊x⌋₊ := by simp
    _ ≤ x ^ 2 := by rw [sq]; exact mul_le_mul hf hf (Nat.cast_nonneg _) hx

/-- The Laplace transform of `ψ (e ^ u)` is `-ζ'(s) / (s ζ(s))` for `Re s > 2`. -/
lemma integral_psi {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (Chebyshev.psi (Real.exp u) : ℂ) * cexp (-(s * u)) =
      -deriv riemannZeta s / riemannZeta s / s := by
  simp_rw [psi_eq_partialSum]
  rw [integral_partialSum_of_isBigO zero_le_two ?_ (by simpa using hs),
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith)]
  refine Asymptotics.IsBigO.of_bound 1 (.of_forall fun n => ?_)
  rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_of_nonneg (by positivity), Real.rpow_two]
  simpa [psi_eq_partialSum, partialSum, Complex.norm_real, abs_of_nonneg vonMangoldt_nonneg]
    using psi_le_sq (Nat.cast_nonneg n)

/-- The continuation of the Laplace transform of `-ε (ψ (e ^ u) - e ^ u)`. -/
noncomputable def continuation (ε : ℝ) (s : ℂ) : ℂ := ε * (1 + logDeriv zetaNum s) / s

lemma continues {θ ε : ℝ} (hθ : 0 ≤ θ) (hε : ε ≠ 0) :
    ContinuesMero (fun u => -(ε * (Chebyshev.psi (Real.exp u) - Real.exp u))) (continuation ε)
      {ρ | θ < ρ.re ∧ riemannZeta ρ = 0} |ε| 2 θ where
  measurable := by
    have := (measurable_partialSum (b := fun n => Λ n)).comp Real.measurable_exp
    simp_rw [psi_eq_partialSum]
    unfold Function.comp at this
    fun_prop
  growth u hu := by
    have h1 := psi_le_sq (Real.exp_pos u).le
    have h2 := Chebyshev.psi_nonneg (Real.exp u)
    have h3 : Real.exp u ≤ Real.exp (2 * u) := Real.exp_le_exp.2 (by linarith)
    rw [← Real.exp_nat_mul] at h1
    rw [abs_neg, abs_mul]
    refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg ε) <;>
      push_cast at h1 <;> linarith [Real.exp_pos u]
  laplace s hs := by
    have hs1 : s ≠ 1 := fun e => by norm_num [e] at hs
    have hz := riemannZeta_ne_zero_of_one_le_re (by linarith : 1 ≤ s.re)
    obtain ⟨i1, v1⟩ := laplace_exp (a := 1) (s := s) (by simpa using hs.trans' one_lt_two) 0
    have i2 := integrable_kernel (A := 1) (c := 2) (f := fun u => Chebyshev.psi (Real.exp u))
      (by simp_rw [psi_eq_partialSum]; exact (measurable_partialSum).comp Real.measurable_exp)
      (fun u _ => by
        have := psi_le_sq (Real.exp_pos u).le
        rw [← Real.exp_nat_mul] at this
        rw [abs_of_nonneg (Chebyshev.psi_nonneg _), one_mul]
        exact_mod_cast this) 0 hs
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at i2
    rw [ofReal_zero, mul_zero, Complex.exp_zero] at v1
    have e : ∫ u in Ioi (0 : ℝ),
        ((-(ε * (Chebyshev.psi (Real.exp u) - Real.exp u)) : ℝ) : ℂ) * cexp (-(s * u)) =
          -ε * ((∫ u in Ioi (0 : ℝ), (Chebyshev.psi (Real.exp u) : ℂ) * cexp (-(s * u))) -
          ∫ u in Ioi (0 : ℝ), cexp (1 * u) * cexp (-(s * u))) := by
      rw [← integral_sub i2 i1, ← integral_const_mul]
      congr 1 with u
      push_cast
      rw [one_mul]
      ring
    rw [e, integral_psi hs, v1, continuation, logDeriv_zetaNum hs1 hz, logDeriv_apply]
    have hs0 : s ≠ 0 := fun e => by norm_num [e] at hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    field_simp
    ring
  analytic s hs hZ := by
    have h0 : s ≠ 0 := fun e => by simp [e] at hs; linarith
    have hd := differentiable_zetaNum.analyticAt s
    exact (analyticAt_const.mul (analyticAt_const.add (hd.deriv.div hd
      (zetaNum_ne_zero fun h => hZ ⟨hs, h⟩)))).div analyticAt_id h0
  finite s r := ((isCompact_closedBall s r).inter_riemannZetaZeros_finite).subset
    fun ρ h => ⟨h.2, h.1.2⟩
  re_mem ρ h := ⟨h.1, (re_lt_one_of_zero h.2).le.trans one_le_two⟩
  pole ρ h := by
    have h0 : ρ ≠ 0 := fun e => by have := h.1; simp [e] at this; linarith
    obtain ⟨g, hg, hg0, hlog⟩ := exists_logDeriv_zetaNum ρ
    refine ⟨0, fun s => ε * ((1 + logDeriv g s) * (s - ρ) + zeroMult ρ) / s,
      ((analyticAt_const.mul (((analyticAt_const.add (hg.deriv.div hg hg0)).mul
        (by fun_prop)).add analyticAt_const)).div analyticAt_id h0), ?_, ?_⟩
    · simpa using ⟨⟨hε, (zeroMult_pos h.2).ne'⟩, h0⟩
    filter_upwards [hlog, self_mem_nhdsWithin,
      (eventually_ne_nhds h0).filter_mono nhdsWithin_le_nhds] with s hs hne hs0
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 hne
    rw [continuation, hs]
    field_simp
    ring

/-- A window bound on `ψ x - x` with `θ ≥ 0` rules out zeros of zeta to the right of `θ`. The
converse is not asserted. -/
theorem riemannZeta_ne_zero_of_psiWindow {θ δ C : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (h : WindowBound (fun x => Chebyshev.psi x - x) θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 :=
  riemannZeta_ne_zero_of_continues hθ hδ (fun _ hε => continues hθ hε) h hρ

end Masullo.ChebyshevWindow
