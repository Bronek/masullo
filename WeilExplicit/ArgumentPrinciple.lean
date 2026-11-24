import WeilExplicit.Rectangle
import WeilExplicit.RemoveZeros
import Mathlib.Analysis.Calculus.LogDeriv

/-! # The weighted argument principle for an entire function on a rectangle -/

namespace WeilExplicit

open Complex Set

/-- The boundary integral commutes with finite sums of functions continuous on the boundary. -/
theorem rectIntegral_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {a b l u : ℝ}
    (h : ∀ i ∈ S, ContinuousOn (F i) (rectBoundary a b l u)) :
    rectIntegral (fun z ↦ ∑ i ∈ S, F i z) a b l u = ∑ i ∈ S, rectIntegral (F i) a b l u := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectIntegral]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [rectIntegral_add (h _ (Finset.mem_insert_self ..))
      (continuousOn_finsetSum _ (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))]

/-- The full order is removed at each zero in the box. Cauchy's formula applied to the
resulting simple fractions gives the weighted sum of orders. -/
theorem rectIntegral_logDeriv {f H : ℂ → ℂ} (hf : Differentiable ℂ f) (hH : Differentiable ℂ H)
    {a b l u : ℝ} (S : Finset ℂ)
    (hint : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ l < p.im ∧ p.im < u)
    (hall : ∀ z ∈ uIcc a b ×ℂ uIcc l u, f z = 0 → z ∈ S)
    (hfin : ∀ p ∈ S, analyticOrderAt f p ≠ ⊤) :
    rectIntegral (fun z ↦ H z * logDeriv f z) a b l u =
      (2*Real.pi*I) * ∑ p ∈ S, (analyticOrderNatAt f p : ℂ) * H p := by
  classical
  let m := analyticOrderNatAt f
  obtain ⟨g, hg, hgS, hfg⟩ := factor_finset_orders S hf hfin
  have hn {z} (hz : z ∈ uIcc a b ×ℂ uIcc l u) : g z ≠ 0 := by
    intro e
    exact hgS z (hall z hz (by rw [hfg z, e, mul_zero])) e
  have hnz {z} (hz : z ∈ rectBoundary a b l u) {p} (hp : p ∈ S) : z-p ≠ 0 := by
    obtain ⟨ha,hb,hl,hu⟩ := hint p hp
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (interior_notMem_rectBoundary ha hb hl hu))
  let F (p z : ℂ) := (m p : ℂ) * (H z / (z-p))
  have hF (p) (hp : p ∈ S) : ContinuousOn (F p) (rectBoundary a b l u) :=
    continuousOn_const.mul (hH.continuous.continuousOn.div (continuousOn_id.sub continuousOn_const)
      (fun _ hz ↦ hnz hz hp))
  have hR : DifferentiableOn ℂ (fun z ↦ H z * logDeriv g z) (uIcc a b ×ℂ uIcc l u) :=
    hH.differentiableOn.mul (hg.deriv.differentiableOn.div hg.differentiableOn (fun _ hz ↦ hn hz))
  have he {z} (hz : z ∈ rectBoundary a b l u) :
      H z * logDeriv f z = (∑ p ∈ S, F p z) + H z * logDeriv g z := by
    let P (w : ℂ) := ∏ p ∈ S, (w-p)^m p
    have hp (p) (h : p ∈ S) := pow_ne_zero (m p) (hnz hz h)
    have hd : Differentiable ℂ P := by dsimp [P]; fun_prop
    rw [show f = fun w ↦ P w * g w from funext hfg,
      logDeriv_mul z (Finset.prod_ne_zero_iff.mpr hp)
        (hn (rectBoundary_subset _ _ _ _ hz)) (hd z) (hg z),
      show P = (fun w ↦ ∏ p ∈ S, (w-p)^m p) from rfl,
      logDeriv_prod (f := fun p w ↦ (w-p)^m p) hp (by intros; fun_prop),
      mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [logDeriv_fun_pow (f := fun w : ℂ ↦ w-p) (by fun_prop)]
    simp [F, logDeriv_apply, div_eq_mul_inv]
    ring
  rw [rectIntegral_congr (fun _ hz ↦ he hz),
    rectIntegral_add (continuousOn_finsetSum _ hF) (hR.continuousOn.mono (rectBoundary_subset ..)),
    rectIntegral_eq_zero hR, add_zero, rectIntegral_sum S F hF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨ha,hb,hl,hu⟩ := hint p hp
  dsimp only [F]
  rw [rectIntegral_const_mul, rectIntegral_cauchy hH ha hb hl hu]
  ring

end WeilExplicit
