import WeilExplicit.Completed
import WeilExplicit.ArgumentPrinciple

/-! # The completed-zeta residue identity at a good height -/

namespace WeilExplicit

open WeilExplicit (xi)

open Complex Set Filter
open scoped Topology

private theorem finite_window (T : ℝ) : {ρ : stripZeros | |(ρ:ℂ).im| < T}.Finite := by
  have h := (isCompact_Icc (a := (0:ℝ)) (b := 1)).reProdIm (isCompact_Icc (a := -T) (b := T))
  apply (h.inter_riemannZetaZeros_finite.preimage (f := (Subtype.val : stripZeros → ℂ))
    Subtype.val_injective.injOn).subset
  intro ρ hρ
  exact ⟨⟨⟨ρ.property.2.1.le, ρ.property.2.2.le⟩, (abs_le.mp hρ.le)⟩, ρ.property.1⟩

/-- The unordered finite window retains the subtype used by the infinite sum. -/
noncomputable def zeroWindow (T : ℝ) : Finset stripZeros := (finite_window T).toFinset

/-- The finite zero window contains precisely the strip zeros of absolute height less than T. -/
@[simp] theorem mem_zeroWindow {T : ℝ} {ρ : stripZeros} : ρ ∈ zeroWindow T ↔ |(ρ:ℂ).im| < T :=
  Set.Finite.mem_toFinset _

/-- As T grows, the zero windows eventually contain every finite set of strip zeros. -/
theorem tendsto_zeroWindow : Tendsto zeroWindow atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro a b hab ρ hρ
    exact mem_zeroWindow.mpr ((mem_zeroWindow.mp hρ).trans_le hab)
  · intro ρ
    exact ⟨|(ρ:ℂ).im| + 1, mem_zeroWindow.mpr (by linarith)⟩

/-- A good horizontal segment and its reflection exclude all zeros from the two edges. -/
theorem xi_ne_zero_at_height {T : ℝ}
    (hgood : ∀ z : ℂ, |z.im| = T → 1/2 ≤ z.re → z.re ≤ 2 → riemannZeta z ≠ 0)
    {s : ℂ} (hs : |s.im| = T) : xi s ≠ 0 := by
  intro e
  have h := xi_eq_zero_iff.mp e
  by_cases hb : 1/2 ≤ s.re
  · exact hgood s hs hb (by linarith [h.2.2]) h.1
  · have hr := xi_eq_zero_iff.mp ((xi_one_sub s).trans e)
    exact hgood (1-s) (by simpa using hs) (by simp; linarith) (by linarith [hr.2.2]) hr.1

/-- The two subtracted pole terms and all enclosed zeros, before passing to the limit. -/
theorem completed_rectangle {H : ℂ → ℂ} (hH : Differentiable ℂ H) {T : ℝ} (hT : 0 < T)
    (hgood : ∀ z : ℂ, |z.im| = T → 1/2 ≤ z.re → z.re ≤ 2 → riemannZeta z ≠ 0) :
    rectIntegral (fun z ↦ H z * logDeriv completedRiemannZeta z) (-1) 2 (-T) T =
      (2*Real.pi*I) * ((∑ ρ ∈ zeroWindow T, (zeroMult ρ : ℂ) * H ρ) - H 0 - H 1) := by
  classical
  let S := (zeroWindow T).map (Function.Embedding.subtype (· ∈ stripZeros))
  have hS {z : ℂ} : z ∈ S ↔ z ∈ stripZeros ∧ |z.im| < T := by
    simp [S, Finset.mem_map, and_comm]
  have hbox {p : ℂ} (hp : p ∈ S) : -1 < p.re ∧ p.re < 2 ∧ -T < p.im ∧ p.im < T := by
    obtain ⟨hz,ht⟩ := hS.mp hp
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2], abs_lt.mp ht⟩
  have hall {z : ℂ} (hz : z ∈ uIcc (-1) 2 ×ℂ uIcc (-T) T) (he : xi z = 0) : z ∈ S := by
    have hl := hz.2
    rw [uIcc_of_le (by linarith)] at hl
    exact hS.mpr ⟨xi_eq_zero_iff.mp he, lt_of_le_of_ne (abs_le.mpr hl)
      (fun e ↦ xi_ne_zero_at_height hgood e he)⟩
  have hxi := rectIntegral_logDeriv differentiable_xi hH S (fun _ ↦ hbox) (fun _ ↦ hall)
    (fun p hp ↦ by
      have hz := (hS.mp hp).1
      rw [xi_order_eq hz]
      exact zeta_order_ne_top (fun h ↦ by simpa [h] using hz.2.2))
  have hsum : (∑ p ∈ S, (analyticOrderNatAt xi p : ℂ) * H p) =
      ∑ ρ ∈ zeroWindow T, (zeroMult ρ : ℂ) * H ρ := by
    simp only [S, Finset.sum_map, Function.Embedding.subtype_apply]
    exact Finset.sum_congr rfl fun ρ _ ↦ by
      simp [zeroMult, analyticOrderNatAt, xi_order_eq ρ.property]
  rw [hsum] at hxi
  let B := rectBoundary (-1) 2 (-T) T
  have notB (p : ℂ) (hr : -1 < p.re ∧ p.re < 2) (hi : p.im = 0) : p ∉ B :=
    interior_notMem_rectBoundary hr.1 hr.2 (by linarith) (by linarith)
  have h₀ : (0:ℂ) ∉ B := notB 0 (by norm_num) rfl
  have h₁ : (1:ℂ) ∉ B := notB 1 (by norm_num) rfl
  have hn {z : ℂ} (hz : z ∈ B) : xi z ≠ 0 := by
    intro e
    obtain ⟨ha,hb,hl,hu⟩ := hbox (hall (rectBoundary_subset _ _ _ _ hz) e)
    exact interior_notMem_rectBoundary ha hb hl hu hz
  have hx : ContinuousOn (fun z ↦ H z * logDeriv xi z) B :=
    hH.continuous.continuousOn.mul (differentiable_xi.deriv.continuous.continuousOn.div
      differentiable_xi.continuous.continuousOn (fun _ ↦ hn))
  let Q (p z : ℂ) := -1 * (H z/(z-p))
  have hQ {p} (hp : p ∉ B) : ContinuousOn (Q p) B :=
    continuousOn_const.mul (hH.continuous.continuousOn.div (continuousOn_id.sub continuousOn_const)
      (fun _ hz ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hp)))
  have he {z : ℂ} (hz : z ∈ B) :
      H z * logDeriv completedRiemannZeta z = (H z * logDeriv xi z + Q 0 z) + Q 1 z := by
    rw [logDeriv_completed_eq_xi (ne_of_mem_of_not_mem hz h₀) (ne_of_mem_of_not_mem hz h₁) (hn hz)]
    simp only [Q, sub_zero, div_eq_mul_inv]
    ring
  rw [rectIntegral_congr (fun _ hz ↦ he hz),
    rectIntegral_add (f := fun z ↦ H z * logDeriv xi z + Q 0 z) (hx.add (hQ h₀)) (hQ h₁),
    rectIntegral_add hx (hQ h₀), hxi]
  simp only [Q, rectIntegral_const_mul,
    rectIntegral_cauchy hH (a := -1) (b := 2) (l := -T) (u := T)
      (p := 0) (by norm_num) (by norm_num)
    (by simpa using hT) (by simpa using hT),
    rectIntegral_cauchy hH (a := -1) (b := 2) (l := -T) (u := T)
      (p := 1) (by norm_num) (by norm_num)
    (by simpa using hT) (by simpa using hT)]
  ring

end WeilExplicit
