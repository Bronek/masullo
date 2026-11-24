import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

/-! # Removing finitely many zeros from an entire function -/

namespace WeilExplicit

open Complex Filter
open scoped Topology

private theorem remove_one_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ)
    (ha : analyticOrderAt f a ≠ ⊤) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g a ≠ 0 ∧
      ∀ z, f z = (z - a) ^ analyticOrderNatAt f a * g z := by
  classical
  obtain ⟨u, hu, hu₀, heq⟩ := (hf.analyticAt a).analyticOrderAt_ne_top.mp ha
  let q (z : ℂ) := f z / (z - a) ^ analyticOrderNatAt f a
  let g := Function.update q a (u a)
  have hgu : g =ᶠ[𝓝 a] u := by
    filter_upwards [heq] with z hz
    by_cases h : z = a
    · simp [g, h]
    · simp [g, q, h, hz, smul_eq_mul, sub_ne_zero.mpr h]
  refine ⟨g, fun z ↦ ?_, by simpa [g] using hu₀, fun z ↦ ?_⟩
  · by_cases h : z = a
    · subst z; exact (hu.congr hgu.symm).differentiableAt
    · have hq : g =ᶠ[𝓝 z] q :=
        (eventually_ne_nhds h).mono fun _ hx ↦ Function.update_of_ne hx ..
      exact ((hf z).div ((differentiableAt_id.sub_const a).pow _)
        (pow_ne_zero _ (sub_ne_zero.mpr h))).congr_of_eventuallyEq hq
  · by_cases h : z = a
    · subst z
      simpa [g, smul_eq_mul] using heq.self_of_nhds
    · simp [g, q, h, mul_div_cancel₀, pow_ne_zero _ (sub_ne_zero.mpr h)]

/-- Divide out the full analytic multiplicity at each point of a finite set.
The residual function is entire and nonzero at the specified points. -/
theorem factor_finset_orders (S : Finset ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfin : ∀ a ∈ S, analyticOrderAt f a ≠ ⊤) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ a ∈ S, g a ≠ 0) ∧
      ∀ z, f z = (∏ a ∈ S, (z - a) ^ analyticOrderNatAt f a) * g z := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨u, hu, hua, hfu⟩ := remove_one_zero hf a (hfin _ (Finset.mem_insert_self ..))
    let p (z : ℂ) := (z - a) ^ analyticOrderNatAt f a
    have hp (b : ℂ) : AnalyticAt ℂ p b := by dsimp [p]; fun_prop
    have horder (b : ℂ) (hb : b ∈ S) : analyticOrderAt f b = analyticOrderAt u b := by
      have hn : p b ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hb ha))
      rw [show f = p * u from funext hfu, analyticOrderAt_mul (hp b) (hu.analyticAt b),
        (hp b).analyticOrderAt_eq_zero.mpr hn, zero_add]
    obtain ⟨g, hg, hgS, hug⟩ := ih hu fun b hb ↦ horder b hb ▸ hfin b (Finset.mem_insert_of_mem hb)
    refine ⟨g, hg, ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · intro h
        apply hua
        rw [hug b, h, mul_zero]
      · exact hgS b hb
    · intro z
      rw [hfu z, hug z, Finset.prod_insert ha, mul_assoc]
      congr 2
      exact Finset.prod_congr rfl fun b hb ↦ by simp [analyticOrderNatAt, horder b hb]

end WeilExplicit
