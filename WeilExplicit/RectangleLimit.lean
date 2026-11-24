import WeilExplicit.Rectangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Limits of boundary integrals on expanding rectangles -/

namespace WeilExplicit

open MeasureTheory Set Complex Filter
open scoped Topology

/-- Uniform decay of order 1/T on the horizontal segments leaves the two full line integrals. -/
theorem rectIntegral_tendsto {f : ℂ → ℂ} {a b : ℝ} {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (ha : Integrable (fun t : ℝ ↦ f (a+t*I))) (hb : Integrable (fun t : ℝ ↦ f (b+t*I)))
    {B : ℝ} (h : ∀ᶠ j in atTop, ∀ z : ℂ, z.re ∈ uIcc a b → |z.im| = T j → ‖f z‖ ≤ B / T j) :
    Tendsto (fun j ↦ rectIntegral f a b (-T j) (T j)) atTop
      (𝓝 (I*(∫ t : ℝ, f (b+t*I)) - I*(∫ t : ℝ, f (a+t*I)))) := by
  have hh (y : ℕ → ℝ) (hy : ∀ᶠ j in atTop, |y j| = T j) :
      Tendsto (fun j ↦ ∫ x : ℝ in a..b, f (x+y j*I)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun j ↦ B / T j * |b-a|)
    · filter_upwards [h, hy] with j hj hj'
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      exact fun x hx ↦ hj _ (by simpa using uIoc_subset_uIcc hx) (by simpa using hj')
    · simpa using (hT.const_div_atTop B).mul_const |b-a|
  have hpos := hT.eventually (eventually_ge_atTop 0)
  have hlow := hh (fun j ↦ -T j) (hpos.mono fun j hj ↦ by simp [abs_of_nonneg hj])
  have hhigh := hh T (hpos.mono fun _ hj ↦ abs_of_nonneg hj)
  have va := intervalIntegral_tendsto_integral ha (tendsto_neg_atTop_atBot.comp hT) hT
  have vb := intervalIntegral_tendsto_integral hb (tendsto_neg_atTop_atBot.comp hT) hT
  simpa [rectIntegral] using (((hlow.sub hhigh).add (vb.const_mul I)).sub (va.const_mul I))

end WeilExplicit
