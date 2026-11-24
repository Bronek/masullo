import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Cauchy integration on a rectangle -/

namespace WeilExplicit

open Complex MeasureTheory Set

/-- Counterclockwise boundary integral on a rectangle with real and imaginary endpoints. -/
noncomputable def rectIntegral (f : ℂ → ℂ) (a b l u : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x+l*I)) - (∫ x : ℝ in a..b, f (x+u*I)) +
  I*(∫ y : ℝ in l..u, f (b+y*I)) - I*(∫ y : ℝ in l..u, f (a+y*I))

/-- Cauchy–Goursat gives zero boundary integral for a function differentiable on the rectangle. -/
theorem rectIntegral_eq_zero {f : ℂ → ℂ} {a b l u : ℝ}
    (hf : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc l u)) : rectIntegral f a b l u = 0 := by
  simpa [rectIntegral, smul_eq_mul] using
    integral_boundary_rect_eq_zero_of_differentiableOn f (a+l*I) (b+u*I) (by simpa)

/-- The four closed sides, including the corners. -/
def rectBoundary (a b l u : ℝ) : Set ℂ :=
  (uIcc a b ×ℂ {l,u}) ∪ ({a,b} ×ℂ uIcc l u)

/-- Each side of the rectangle lies in the closed product of its coordinate intervals. -/
theorem rectBoundary_subset (a b l u : ℝ) :
    rectBoundary a b l u ⊆ uIcc a b ×ℂ uIcc l u := by
  rintro z (⟨hr,hi⟩ | ⟨hr,hi⟩)
  · refine ⟨hr, ?_⟩
    rcases (show z.im = l ∨ z.im = u from hi) with h|h <;> simp [h]
  · refine ⟨?_, hi⟩
    rcases (show z.re = a ∨ z.re = b from hr) with h|h <;> simp [h]

private theorem horiz_mem {a b l u x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ ({l,u} : Set ℝ)) :
    (x:ℂ)+y*I ∈ rectBoundary a b l u :=
  Or.inl (by simpa [mem_reProdIm] using And.intro hx hy)

private theorem vert_mem {a b l u x y : ℝ} (hx : x ∈ ({a,b} : Set ℝ)) (hy : y ∈ uIcc l u) :
    (x:ℂ)+y*I ∈ rectBoundary a b l u :=
  Or.inr (by simpa [mem_reProdIm] using And.intro hx hy)

/-- Agreement on the four edges gives equal boundary integrals. -/
theorem rectIntegral_congr {f g : ℂ → ℂ} {a b l u : ℝ} (h : EqOn f g (rectBoundary a b l u)) :
    rectIntegral f a b l u = rectIntegral g a b l u := by
  have H {y : ℝ} (hy : y ∈ ({l,u}:Set ℝ)) :
      (∫ t : ℝ in a..b, f (t+y*I)) = ∫ t : ℝ in a..b, g (t+y*I) :=
    intervalIntegral.integral_congr fun _ ht ↦ h (horiz_mem ht hy)
  have V {x : ℝ} (hx : x ∈ ({a,b}:Set ℝ)) :
      (∫ t : ℝ in l..u, f (x+t*I)) = ∫ t : ℝ in l..u, g (x+t*I) :=
    intervalIntegral.integral_congr fun _ ht ↦ h (vert_mem hx ht)
  simp only [rectIntegral, H (y := l) (by simp), H (y := u) (by simp),
    V (x := b) (by simp), V (x := a) (by simp)]

/-- The rectangle integral is additive for functions continuous on its boundary. -/
theorem rectIntegral_add {f g : ℂ → ℂ} {a b l u : ℝ}
    (hf : ContinuousOn f (rectBoundary a b l u)) (hg : ContinuousOn g (rectBoundary a b l u)) :
    rectIntegral (fun z ↦ f z + g z) a b l u = rectIntegral f a b l u + rectIntegral g a b l u := by
  have H {F : ℂ → ℂ} (hF : ContinuousOn F (rectBoundary a b l u)) {y : ℝ}
      (hy : y ∈ ({l,u} : Set ℝ)) :
      IntervalIntegrable (fun x : ℝ ↦ F (x+y*I)) volume a b :=
    (hF.comp (by fun_prop) (fun _ hx ↦ horiz_mem hx hy)).intervalIntegrable
  have V {F : ℂ → ℂ} (hF : ContinuousOn F (rectBoundary a b l u)) {x : ℝ}
      (hx : x ∈ ({a,b} : Set ℝ)) :
      IntervalIntegrable (fun y : ℝ ↦ F (x+y*I)) volume l u :=
    (hF.comp (by fun_prop) (fun _ hy ↦ vert_mem hx hy)).intervalIntegrable
  simp only [rectIntegral,
    intervalIntegral.integral_add (H hf (y := l) (by simp)) (H hg (y := l) (by simp)),
    intervalIntegral.integral_add (H hf (y := u) (by simp)) (H hg (y := u) (by simp)),
    intervalIntegral.integral_add (V hf (x := b) (by simp)) (V hg (x := b) (by simp)),
    intervalIntegral.integral_add (V hf (x := a) (by simp)) (V hg (x := a) (by simp))]
  ring

/-- A constant complex factor can be pulled out of the rectangle integral. -/
theorem rectIntegral_const_mul (f : ℂ → ℂ) (v : ℂ) (a b l u : ℝ) :
    rectIntegral (fun z ↦ v*f z) a b l u = v*rectIntegral f a b l u := by
  simp only [rectIntegral, intervalIntegral.integral_const_mul]
  ring

/-- Strict inequalities in both coordinates place a point off all four edges. -/
theorem interior_notMem_rectBoundary {a b l u : ℝ} {p : ℂ}
    (ha : a < p.re) (hb : p.re < b) (hl : l < p.im) (hu : p.im < u) :
    p ∉ rectBoundary a b l u := by
  simp [rectBoundary, mem_reProdIm, ha.ne', hb.ne, hl.ne', hu.ne]

private theorem segment_log {A D : ℂ} {a b : ℝ}
    (h : ∀ t ∈ uIcc a b, A+t*D ∈ slitPlane) :
    D*(∫ t : ℝ in a..b, (A+t*D)⁻¹) = log (A+b*D) - log (A+a*D) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have hd : HasDerivAt (fun z : ℂ ↦ log (A+z*D)) ((A+t*D)⁻¹ * D) (t:ℂ) := by
      simpa [Function.comp_def] using (hasDerivAt_log (h t ht)).comp (t:ℂ)
        (((hasDerivAt_id _).mul_const D).const_add A)
    simpa [mul_comm D] using hd.comp_ofReal
  · apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul ((by fun_prop : Continuous fun t : ℝ ↦ A+t*D).continuousOn.inv₀
      (fun t ht ↦ slitPlane_ne_zero (h t ht)))

private theorem log_neg_above {z : ℂ} (h : 0 < z.im) :
    log (-z) = log z - Real.pi*I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos h, ofReal_sub]
  ring

private theorem log_neg_below {z : ℂ} (h : z.im < 0) :
    log (-z) = log z + Real.pi*I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg h, ofReal_add]
  ring

/-- The principal logarithm on three sides and its rotation on the left compute the winding
integral at an interior point. -/
theorem rectIntegral_inv_sub {p : ℂ} {a b l u : ℝ}
    (ha : a < p.re) (hb : p.re < b) (hl : l < p.im) (hu : p.im < u) :
    rectIntegral (fun z ↦ (z-p)⁻¹) a b l u = 2*Real.pi*I := by
  let v (x y : ℝ) := (x:ℂ)+y*I-p
  have hor (y : ℝ) (hy : y ≠ p.im) :
      (∫ t : ℝ in a..b, (v t y)⁻¹) = log (v b y) - log (v a y) := by
    have h := segment_log (A := y*I-p) (D := 1) (a := a) (b := b) (fun t _ ↦ by
      apply Or.inr
      simpa using sub_ne_zero.mpr hy)
    simpa [v, add_comm, sub_eq_add_neg, add_left_comm, add_assoc] using h
  have right : I*(∫ t : ℝ in l..u, (v b t)⁻¹) = log (v b u) - log (v b l) := by
    have h := segment_log (A := (b:ℂ)-p) (D := I) (a := l) (b := u) (fun t _ ↦ by
      apply Or.inl
      simpa using sub_pos.mpr hb)
    simpa [v, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have left : I*(∫ t : ℝ in l..u, (v a t)⁻¹) = log (-v a u) - log (-v a l) := by
    have h := segment_log (A := -((a:ℂ)-p)) (D := -I) (a := l) (b := u) (fun t _ ↦ by
      apply Or.inl
      simpa using sub_pos.mpr ha)
    have he (t : ℝ) : -((a:ℂ)-p) + t*(-I) = -v a t := by dsimp [v]; ring
    simpa only [he, inv_neg, intervalIntegral.integral_neg, neg_mul_neg] using h
  rw [show rectIntegral (fun z ↦ (z-p)⁻¹) a b l u =
    (∫ x : ℝ in a..b, (v x l)⁻¹) - (∫ x : ℝ in a..b, (v x u)⁻¹) +
    I*(∫ y : ℝ in l..u, (v b y)⁻¹) - I*(∫ y : ℝ in l..u, (v a y)⁻¹) by rfl,
    hor l hl.ne, hor u hu.ne', right, left, log_neg_above, log_neg_below]
  · ring
  · simpa [v] using sub_neg.mpr hl
  · simpa [v] using sub_pos.mpr hu

/-- Cauchy's integral formula on the rectangle for an entire weight. -/
theorem rectIntegral_cauchy {H : ℂ → ℂ} (hH : Differentiable ℂ H) {p : ℂ} {a b l u : ℝ}
    (ha : a < p.re) (hb : p.re < b) (hl : l < p.im) (hu : p.im < u) :
    rectIntegral (fun z ↦ H z / (z-p)) a b l u = H p * (2*Real.pi*I) := by
  have hD : Differentiable ℂ (dslope H p) := differentiableOn_univ.mp
    ((differentiableOn_dslope Filter.univ_mem).mpr hH.differentiableOn)
  have hp := interior_notMem_rectBoundary ha hb hl hu
  have hne {z} (hz : z ∈ rectBoundary a b l u) : z-p ≠ 0 :=
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hp)
  rw [rectIntegral_congr (g := fun z ↦ dslope H p z + H p * (z-p)⁻¹) (fun z hz ↦ ?_),
    rectIntegral_add (g := fun z ↦ H p * (z-p)⁻¹) hD.continuous.continuousOn
      (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ (fun _ hz ↦ hne hz))),
    rectIntegral_eq_zero hD.differentiableOn, zero_add, rectIntegral_const_mul,
    rectIntegral_inv_sub ha hb hl hu]
  change H z / (z-p) = dslope H p z + H p * (z-p)⁻¹
  rw [dslope_of_ne _ (ne_of_mem_of_not_mem hz hp), slope_def_module, smul_eq_mul]
  field_simp [hne hz]
  ring

end WeilExplicit
