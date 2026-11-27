import Masullo.DirichletWindow

/-!
# A sign-only window criterion: the Jordan totient of negative order

For `0 ≤ τ ≤ 1` let `jordan τ = μ * (n ↦ n ^ (-τ))`, the Jordan totient of order `-τ`, so that
`jordan τ n = n ^ (-τ) ∏_{p ∣ n} (1 - p ^ τ)`. At a prime power
`jordan τ (p ^ (k + 1)) = p ^ (-(k + 1) τ) - p ^ (-k τ)`, hence `|jordan τ n| ≤ 1`, and
`∑ jordan τ n n ^ (-s) = ζ(s + τ) / ζ(s)` for `Re s > 1`. The numerator `ζ(s + τ)` is analytic and
nonzero on `Re s > 1 - τ`, so `Masullo.DirichletWindow.riemannZeta_ne_zero_of_windowBound` applies
with `θ = 1 - τ` and `C = 0`: a sign of the partial sums on late windows, with no bound on their
size, rules out zeros of zeta to the right of `1 - τ` (`riemannZeta_ne_zero_of_jordanSign`).

On paper a partial converse holds. Let `Θ` be the supremum of the real parts of the nontrivial
zeros. If `Θ < 1 - τ`, then `∑_{n ≤ x} jordan τ n ~ x ^ (1 - τ) / ((1 - τ) ζ(1 - τ))`, which is
eventually negative. So
`Θ < 1` if and only if, for some `0 < τ < 1`, these partial sums are eventually negative. That
direction is not formalised. At `τ = 1` the conclusion would exclude the zeros on the critical
line, so the hypothesis fails there for every `δ`. At `τ = 0`, `jordan 0` is the unit of Dirichlet
convolution and the hypothesis holds with `ε = -1` (`Masullo/JordanControls.lean`).

The window argument is Kaczorowski and Pintz, *Oscillatory properties of arithmetical functions.
I*, Acta Math. Hungar. 48 (1986), Theorem 1.
-/

open Complex Set
open scoped ArithmeticFunction.Moebius
open ArithmeticFunction

namespace Masullo.Jordan

/-- `n ↦ n ^ (-τ)` on `n ≥ 1`. -/
noncomputable def powNeg (τ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ (-τ), if_pos rfl⟩

lemma powNeg_apply {τ : ℝ} {n : ℕ} (hn : n ≠ 0) : powNeg τ n = (n : ℝ) ^ (-τ) := if_neg hn

lemma isMultiplicative_powNeg (τ : ℝ) : (powNeg τ).IsMultiplicative := by
  refine ⟨by simp [powNeg_apply], fun {m n} _ => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [powNeg]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [powNeg]
  rw [powNeg_apply (mul_ne_zero hm hn), powNeg_apply hm, powNeg_apply hn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

lemma powNeg_mem {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) : 0 ≤ powNeg τ n ∧ powNeg τ n ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [powNeg]
  rw [powNeg_apply hn]
  exact ⟨by positivity, Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn) (by linarith)⟩

/-- The Jordan totient of order `-τ`, `μ * (n ↦ n ^ (-τ))`. -/
noncomputable def jordan (τ : ℝ) : ArithmeticFunction ℝ := (μ : ArithmeticFunction ℝ) * powNeg τ

lemma jordan_prime_pow {τ : ℝ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    jordan τ (p ^ (k + 1)) = powNeg τ (p ^ (k + 1)) - powNeg τ (p ^ k) := by
  rw [jordan, mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => (μ : ArithmeticFunction ℝ) a * powNeg τ b), Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by
      rw [intCoe_apply, moebius_apply_prime_pow hp (by omega), if_neg (by omega)]; simp]
  simp [intCoe_apply, moebius_apply_prime hp, pow_succ', Nat.mul_div_cancel_left _ hp.pos]
  ring

lemma abs_jordan_le {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) : |jordan τ n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hm := isMultiplicative_moebius.intCast.mul (isMultiplicative_powNeg τ)
  rw [jordan, hm.multiplicative_factorization _ hn, Finsupp.prod, Finset.abs_prod]
  refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun p hp => ?_
  have hp := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  generalize n.factorization p = k
  rcases k with _ | k
  · simp [hm.map_one]
  rw [← jordan, jordan_prime_pow hp, abs_le]
  have := powNeg_mem hτ (p ^ (k + 1))
  have := powNeg_mem hτ (p ^ k)
  constructor <;> linarith

open scoped LSeries.notation in
/-- `∑ jordan τ n n ^ (-s) = ζ(s + τ) / ζ(s)` for `Re s > 1` and `τ ≥ 0`. -/
lemma LSeries_jordan {τ : ℝ} (hτ : 0 ≤ τ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (jordan τ n : ℂ)) s = riemannZeta (s + τ) / riemannZeta s := by
  have hs' : 1 < (s + τ).re := by simp; linarith
  have hw : LSeries.term (fun n => (powNeg τ n : ℂ)) s = LSeries.term 1 (s + τ) := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, powNeg_apply hn, Pi.one_apply,
      ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg, cpow_neg, cpow_add _ _ hn']
    field_simp
  have hW : LSeries (fun n => (powNeg τ n : ℂ)) s = riemannZeta (s + τ) := by
    rw [LSeries, hw]
    exact LSeries_one_eq_riemannZeta hs'
  have e : (fun n => (jordan τ n : ℂ)) = (↗μ ⍟ fun n => (powNeg τ n : ℂ)) := by
    ext n
    simp [LSeries.convolution_def, jordan, mul_apply, intCoe_apply]
  have hmul := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hmul
  rw [e, LSeries_convolution' (LSeriesSummable_moebius_iff.2 hs)
    (by unfold LSeriesSummable; rw [hw]; exact LSeriesSummable_one_iff.2 hs'), hW,
    eq_div_iff (riemannZeta_ne_zero_of_one_le_re hs.le)]
  linear_combination riemannZeta (s + τ) * hmul

lemma analyticAt_riemannZeta_add {τ : ℝ} {s : ℂ} (h : s + τ ≠ 1) :
    AnalyticAt ℂ (fun z => riemannZeta (z + τ)) s := by
  have ho : IsOpen {z : ℂ | z + τ ≠ 1} := isOpen_ne_fun (by fun_prop) continuous_const
  refine DifferentiableOn.analyticAt (fun z hz => ?_) (ho.mem_nhds h)
  exact ((differentiableAt_riemannZeta hz).comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z + τ) z)).differentiableWithinAt

/-- For `0 ≤ τ ≤ 1`: if for arbitrarily large `Y` some sign `ε = ±1` has
`ε ∑_{n ≤ x} jordan τ n ≤ 0` for all `x ∈ [Y, Y ^ (1 + δ)]`, then zeta has no zeros to the right
of `1 - τ`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_jordanSign {τ δ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ)
    (h : ∀ X, ∃ Y ≥ X, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ x ∈ Icc Y (Y ^ (1 + δ)), ε * DirichletWindow.partialSum (jordan τ) x ≤ 0)
    {ρ : ℂ} (hρ : 1 - τ < ρ.re) : riemannZeta ρ ≠ 0 :=
  DirichletWindow.riemannZeta_ne_zero_of_windowBound (b := jordan τ)
    (K := fun s => riemannZeta (s + τ)) (C := 0) (by linarith) hδ (abs_jordan_le hτ0)
    (fun s hs => LSeries_jordan hτ0 hs)
    (fun s hs => analyticAt_riemannZeta_add fun e => by
      have := congrArg re e; simp at this; linarith)
    (fun s hs _ => riemannZeta_ne_zero_of_one_le_re (by simp; linarith))
    (fun X => by simpa using h X) hρ

end Masullo.Jordan
