import Masullo.Dyadic
import Masullo.WindowControls

/-!
# Controls for the dyadic window criterion

The dyadic window bounds at `θ = 1`, which hold unconditionally; windows of length zero, whose
bounds hold even if the conclusion fails; and a function to which every
hypothesis of `Landau.Continues.eq_empty_of_window` applies after the dyadic combination, except the
sign of the residue at a real pole.
-/

open MeasureTheory Complex Set Filter Topology Metric
open ArithmeticFunction (vonMangoldt_nonneg)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo.Window.Controls

open Landau Landau.Continues

lemma dyadicSum_nonneg (X : ℝ) : 0 ≤ dyadicSum X := Finset.sum_nonneg fun _ _ =>
  mul_nonneg vonMangoldt_nonneg (weight_nonneg _)

lemma dyadicSum_le {X : ℝ} (hX : 0 < X) : dyadicSum X ≤ (Real.log 4 + 4) * X := by
  refine le_trans ?_ (Chebyshev.psi_le_const_mul_self hX.le)
  refine Finset.sum_le_sum fun _ _ =>
    mul_le_of_le_one_right vonMangoldt_nonneg (weight_le_one _)

lemma abs_dyadicDiff_le {x : ℝ} (hx : 0 < x) : |dyadicDiff x| ≤ 2 * (Real.log 4 + 4) * x := by
  have h1 := dyadicSum_le hx
  have h2 := dyadicSum_le (X := 2 * x) (by linarith)
  rw [abs_le, dyadicDiff]
  constructor <;> linarith [dyadicSum_nonneg x, dyadicSum_nonneg (2 * x)]

/-- The upper dyadic bound holds at `θ = 1`, where zero-freeness is already unconditional. -/
theorem dyadicDiff_le_window : ∀ X, ∃ Y ≥ X, ∀ x ∈ Icc Y (Y ^ (1 + (1 : ℝ))),
    dyadicDiff x ≤ (2 * (Real.log 4 + 4)) * x ^ (1 : ℝ) := fun X =>
  ⟨max X 1, le_max_left _ _, fun x hx => by
    simpa using le_of_abs_le (abs_dyadicDiff_le (by linarith [(le_max_right X 1).trans hx.1]))⟩

/-- The lower dyadic bound holds at `θ = 1`. -/
theorem le_dyadicDiff_window : ∀ X, ∃ Y ≥ X, ∀ x ∈ Icc Y (Y ^ (1 + (1 : ℝ))),
    -((2 * (Real.log 4 + 4)) * x ^ (1 : ℝ)) ≤ dyadicDiff x := fun X =>
  ⟨max X 1, le_max_left _ _, fun x hx => by
    simpa using neg_le_of_abs_le (abs_dyadicDiff_le (by linarith [(le_max_right X 1).trans hx.1]))⟩

/-- If zeta has a zero in `Re s > θ`, the upper bound with `C = 0` still holds at arbitrarily late
points: windows of length zero do not suffice. -/
theorem singleton_window_insufficient {θ : ℝ} {ρ : ℂ} (hθ : 0 ≤ θ) (hz : riemannZeta ρ = 0)
    (hρ : θ < ρ.re) : ∀ X, ∃ Y ≥ X, dyadicDiff Y ≤ 0 := by
  intro X
  by_contra! hh
  refine riemannZeta_ne_zero_of_le_dyadicDiff (C := 0) hθ zero_lt_one (fun T => ?_) hρ hz
  refine ⟨max T X, le_max_left _ _, fun x hx => ?_⟩
  simpa using (hh x ((le_max_right _ _).trans hx.1)).le

/-- The dyadic combination of `e ^ (u / 2)` is nonnegative on all late windows and its transform has
a pole at `1 / 2` with a positive residue: it satisfies every hypothesis but the sign. -/
theorem dyadic_sign_needed : ∃ (H κ : ℂ → ℂ) (A : ℝ),
    Continues (dyadic fun u => Real.exp (1 / 2 * u)) H {((1 / 2 : ℝ) : ℂ)} κ A 1 0 ∧
      0 < (κ (1 / 2 : ℝ)).re ∧
        ∀ u > 3 * Real.log 2, 0 ≤ dyadic (fun u => Real.exp (1 / 2 * u)) u := by
  have h : Continues (fun u => Real.exp (1 / 2 * u)) (fun s => 1 / (s - (1 / 2 : ℝ)))
      {((1 / 2 : ℝ) : ℂ)} (fun _ => 1) 1 1 0 :=
    ⟨by fun_prop, fun u hu => by
        rw [Real.abs_exp, one_mul]
        exact Real.exp_le_exp.2 (by linarith), fun s hs => by
        obtain ⟨-, v⟩ := laplace_exp (a := (1 / 2 : ℝ)) (s := s)
          (by rw [ofReal_re]; linarith) 0
        rw [ofReal_zero, mul_zero, Complex.exp_zero] at v
        rw [← v]
        simp, fun s _ hs => analyticAt_div_sub hs,
      fun s r => (finite_singleton _).subset inter_subset_left,
      fun ρ hρ => by rw [mem_singleton_iff.1 hρ, ofReal_re]; norm_num,
      fun _ _ => one_ne_zero, fun ρ hρ =>
      ⟨0, analyticAt_const, .of_forall fun s => by simp [mem_singleton_iff.1 hρ]⟩⟩
  have hg : 0 < gain (1 / 2) := gain_pos (by norm_num) (by norm_num)
  obtain ⟨H, κ, A, hc, hκ⟩ := h.dyadic_continues zero_le_one fun ρ hρ => by
    rw [mem_singleton_iff.1 hρ, ofReal_re]
    norm_num
  refine ⟨H, κ, A, hc, by rw [hκ, mul_one, ofReal_re]; exact hg, fun u hu => ?_⟩
  have hs (v : ℝ) : Real.exp (1 / 2 * (v - Real.log 2)) =
      Real.exp (1 / 2 * v) * Real.exp (-(1 / 2 * Real.log 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have e : dyadic (fun u => Real.exp (1 / 2 * u)) u = Real.exp (1 / 2 * u) * gain (1 / 2) := by
    rw [dyadic_apply _ hu, hs (u - Real.log 2 - Real.log 2), hs (u - Real.log 2), hs u, gain]
    ring
  rw [e]
  positivity

/-- The weight does not vanish: its value at `1 / 2` is `1`. -/
lemma weight_half : weight (1 / 2) = 1 := by norm_num [weight, ramp]

end Masullo.Window.Controls
