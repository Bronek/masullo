import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.Order

/-! # Zeros in the open critical strip -/

namespace WeilExplicit

open Complex Set Filter
open scoped Topology

/-- Zeros of zeta in the open critical strip. -/
def stripZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- Analytic multiplicity of a zero of zeta. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- Away from its pole, zeta has finite analytic order. -/
theorem zeta_order_ne_top {s : ℂ} (hs : s ≠ 1) : analyticOrderAt riemannZeta s ≠ ⊤ := by
  apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (x := 2) (by simp) hs
  rw [(analyticOn_riemannZeta 2 (by simp)).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_le_re (by norm_num))]
  simp

/-- Every zero in the open critical strip has positive analytic multiplicity. -/
theorem zeroMult_pos {ρ : ℂ} (hρ : ρ ∈ stripZeros) : 0 < zeroMult ρ := by
  have h₁ : ρ ≠ 1 := fun h ↦ by simpa [h] using hρ.2.2
  apply Nat.pos_of_ne_zero
  intro h
  have hn := Nat.cast_analyticOrderNatAt (zeta_order_ne_top h₁)
  change analyticOrderNatAt riemannZeta ρ = 0 at h
  simp only [h, Nat.cast_zero] at hn
  exact (analyticOn_riemannZeta ρ h₁).analyticOrderAt_eq_zero.mp hn.symm hρ.1

/-- Completed zeta is analytic away from its poles at zero and one. -/
theorem analyticAt_completedZeta {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds h₀, eventually_ne_nhds h₁] with z hz hz'
  exact differentiableAt_completedZeta hz hz'

/-- Removing the Gamma factor preserves the order in the open strip. -/
theorem zeta_order_eq_completed {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    analyticOrderAt riemannZeta s = analyticOrderAt completedRiemannZeta s := by
  have hs : s ≠ 0 := fun h ↦ by simp [h] at h₀
  have hs' : s ≠ 1 := fun h ↦ by simp [h] at h₁
  have hcomp := analyticAt_completedZeta hs hs'
  have hΓ := differentiable_Gammaℝ_inv.analyticAt s
  have heq : riemannZeta =ᶠ[𝓝 s] completedRiemannZeta * (fun z ↦ (Gammaℝ z)⁻¹) := by
    filter_upwards [eventually_ne_nhds hs] with z hz
    simp [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hcomp hΓ,
    hΓ.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h₀)), add_zero]

/-- Reflection in the functional equation preserves analytic multiplicities. -/
theorem zeroMult_one_sub {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    zeroMult (1 - s) = zeroMult s := by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s := by fun_prop
  have hd : deriv (fun z : ℂ ↦ 1 - z) s ≠ 0 := by simp
  have ho := analyticOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta) hg hd
  simp only [Function.comp_def, completedRiemannZeta_one_sub] at ho
  simp only [zeroMult, analyticOrderNatAt,
    zeta_order_eq_completed (s := 1 - s) (by simpa using h₁) (by simpa using h₀),
    zeta_order_eq_completed h₀ h₁, ← ho]

end WeilExplicit
