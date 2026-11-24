import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Spacing a height away from finitely many ordinates -/

namespace WeilExplicit

open Set MeasureTheory

/-- A unit interval contains a point separated from every member of a finite
family. Repeated ordinates are allowed. -/
theorem exists_separated_height {α : Type*} (S : Finset α) (y : α → ℝ) (j : ℝ) :
    ∃ T ∈ Icc j (j + 1), ∀ a ∈ S, 1 / (2 * (S.card + 1 : ℝ)) ≤ |T - y a| := by
  classical
  let d := 1 / (2 * (S.card + 1 : ℝ))
  have hd : 0 < d := by dsimp [d]; positivity
  by_contra! h
  have hcover : Icc j (j + 1) ⊆ ⋃ a ∈ S, Ioo (y a - d) (y a + d) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := h x hx
    exact mem_iUnion₂.mpr ⟨a, ha, by change |x - y a| < d at hxa; rw [abs_lt] at hxa
                                     exact ⟨by linarith, by linarith⟩⟩
  have hv := (measure_mono (μ := volume) hcover).trans
    (measure_biUnion_finset_le S (fun a ↦ Ioo (y a - d) (y a + d)))
  simp only [Real.volume_Icc, Real.volume_Ioo, add_sub_cancel_left,
    show ∀ a, y a + d - (y a - d) = 2*d
    from fun _ ↦ by ring, Finset.sum_const, nsmul_eq_mul] at hv
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hv
  dsimp [d] at hv
  field_simp at hv
  linarith

end WeilExplicit
