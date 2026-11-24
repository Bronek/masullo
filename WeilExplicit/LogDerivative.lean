import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # The logarithmic derivative on a zero-free disc -/

namespace WeilExplicit

open Complex Metric Set Real

open scoped ComplexConjugate in
/-- Conjugation equivariance passes from a complex function to its logarithmic derivative. -/
theorem logDeriv_conj {f : ℂ → ℂ} (hf : ∀ z, f (conj z) = conj (f z)) (s : ℂ) :
    logDeriv f (conj s) = conj (logDeriv f s) := by
  have he : conj ∘ f ∘ conj = f := by ext z; simp [hf]
  have hd := congrFun (deriv_conj_conj (f := f)) (conj s)
  rw [he] at hd
  simp [logDeriv_apply, hd, hf]

/-- A branch of the logarithm of `g / g c` normalized at the center. -/
theorem exists_normalized_log {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R)) (hn : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ L : ℂ → ℂ, L c = 0 ∧ ∀ z ∈ ball c R,
      HasDerivAt L (logDeriv g z) z ∧ exp (L z) * g c = g z := by
  have hd : DifferentiableOn ℂ (logDeriv g) (ball c R) :=
    (hg.deriv isOpen_ball).div hg hn
  obtain ⟨L, hLc, hL⟩ := hd.isExactOn_ball.with_val_at c 0
  let F (z : ℂ) := g z * exp (-L z)
  have hF (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt F 0 z := by
    have hgz := hg.differentiableAt (isOpen_ball.mem_nhds hz)
    convert! hgz.hasDerivAt.mul (hL z hz).neg.cexp using 1
    simp only [logDeriv_apply]
    field_simp [hn z hz]
    ring
  refine ⟨L, hLc, fun z hz ↦ ⟨hL z hz, ?_⟩⟩
  have heq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
    (fun z hz ↦ (hF z hz).differentiableAt.differentiableWithinAt) (fun z hz ↦ (hF z hz).deriv)
    hz (mem_ball_self hR)
  simpa [F, hLc, Complex.exp_neg, ← div_eq_mul_inv,
    eq_div_iff (Complex.exp_ne_zero _), mul_comm] using heq.symm

/-- The Borel–Carathéodory theorem bounds the normalized logarithm on a zero-free disc.
Cauchy's estimate on a circle of radius `d` then bounds the logarithmic derivative. -/
theorem norm_logDeriv_le_of_log_norm_sub_le {c x : ℂ} {R d M : ℝ} {g : ℂ → ℂ}
    (hd : 0 < d) (hM : 0 < M) (hx : dist x c + 2*d ≤ R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hn : ∀ z ∈ ball c R, g z ≠ 0)
    (hlog : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M) :
    ‖logDeriv g x‖ ≤ 2 * M * R / d ^ 2 := by
  have hR : 0 < R := by linarith [show 0 ≤ dist x c from dist_nonneg]
  have hxc : x ∈ ball c R := by rw [mem_ball]; linarith
  obtain ⟨L, hLc, hL⟩ := exists_normalized_log hR hg hn
  let f (w : ℂ) := L (w + c)
  have shift (w : ℂ) (hw : w ∈ ball 0 R) : w + c ∈ ball c R := by simpa using hw
  have hdiff : DifferentiableOn ℂ f (ball 0 R) := fun w hw ↦
    ((hL _ (shift w hw)).1.differentiableAt.comp w
      (differentiableAt_id.add_const c)).differentiableWithinAt
  have hre : MapsTo f (ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    have hw' := shift w hw
    have he := congrArg norm (hL _ hw').2
    rw [norm_mul, norm_exp] at he
    have hlogs := congrArg Real.log he
    rw [Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr (hn c (mem_ball_self hR))),
      Real.log_exp] at hlogs
    change (L (w + c)).re ≤ M
    linarith [hlog _ hw']
  have hsub (z : ℂ) (hz : z ∈ closedBall x d) : dist z c ≤ R - d := by
    have := dist_triangle z x c
    linarith [mem_closedBall.mp hz]
  have hdL : DifferentiableOn ℂ L (ball c R) :=
    fun z hz ↦ (hL z hz).1.differentiableAt.differentiableWithinAt
  rw [← (hL x hxc).1.deriv]
  have hC := norm_deriv_le_of_forall_mem_sphere_norm_le (f := L) (c := x) hd
    (hdL.diffContOnCl_ball (fun z hz ↦ (mem_ball.mpr (by linarith [hsub z hz]))))
      (C := 2 * M * R / d)
  refine (hC fun z hz ↦ ?_).trans_eq (by ring)
  have hz' := hsub z (sphere_subset_closedBall hz)
  rw [dist_eq_norm] at hz'
  have hw : z - c ∈ ball 0 R := mem_ball_zero_iff.mpr (by linarith)
  have hB := borelCaratheodory_zero hM hdiff hre hR hw (by simpa [f] using hLc)
  simp only [f, sub_add_cancel] at hB
  apply hB.trans
  gcongr <;> linarith

end WeilExplicit
