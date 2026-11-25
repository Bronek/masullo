import Masullo.Probe

/-!
# Controls for the nonnegative probes

Counterexamples to `re_le_of_window` without the sign of the coefficients and with the inequality
reversed; and the window bounds at `a = 1 / 2`, which hold unconditionally.
-/

open Complex Set

namespace Masullo.Probe.Controls

lemma hasSum_single (c : ℝ) (x : ℝ) :
    HasSum (fun _ : Unit => (c : ℂ) * exp (x * 1)) ((c * Real.exp x : ℝ) : ℂ) := by
  simp

/-- All hypotheses of `re_le_of_window` but the sign of the coefficient at the real exponent `1`
hold for `- e ^ x`, at `a = 0`, on every window. -/
theorem positivity_needed : ∃ (c : Unit → ℂ) (F : ℝ → ℝ), (∀ i, c i ≠ 0) ∧
    (∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * (fun _ : Unit => (1 : ℂ)) i)) (F x)) ∧
      (∀ t, F t ≤ 0 * Real.exp (0 * t)) ∧ ¬ ∀ i, ((fun _ : Unit => (1 : ℂ)) i).re ≤ 0 :=
  ⟨fun _ => (-1 : ℝ), fun x => -1 * Real.exp x, by simp, fun x _ => hasSum_single (-1) x,
    fun t => by simpa using (Real.exp_pos t).le, by simp⟩

/-- All hypotheses of `re_le_of_window` but the direction of the inequality hold for `e ^ x`, at
`a = 0`, on every window. -/
theorem direction_needed : ∃ (c : Unit → ℂ) (F : ℝ → ℝ), (∀ i, c i ≠ 0) ∧
    (∀ x : ℝ, 0 ≤ x → HasSum (fun i => c i * exp (x * (fun _ : Unit => (1 : ℂ)) i)) (F x)) ∧
      (∀ i, 0 < (c i).re) ∧ (∀ t, 0 * Real.exp (0 * t) ≤ F t) ∧
        ¬ ∀ i, ((fun _ : Unit => (1 : ℂ)) i).re ≤ 0 :=
  ⟨fun _ => (1 : ℝ), fun x => 1 * Real.exp x, by simp, fun x _ => hasSum_single 1 x, by simp,
    fun t => by simpa using (Real.exp_pos t).le, by simp⟩

/-- The exponents of both counterexamples are isolated. -/
example (z : ℂ) : ∃ r > 0, ∀ i, (fun _ : Unit => (1 : ℂ)) i ≠ z →
    r ≤ ‖z - (fun _ : Unit => (1 : ℂ)) i‖ := by
  rcases eq_or_ne z 1 with rfl | h
  · exact ⟨1, one_pos, fun i hi => absurd rfl hi⟩
  · exact ⟨_, norm_pos_iff.2 (sub_ne_zero.2 h), fun _ _ => le_rfl⟩

/-- At `a = 1 / 2` the window bounds hold unconditionally. -/
theorem probeBound_half (δ : ℝ) : ProbeBound (1 / 2) δ :=
  probeBound_of_trace (by norm_num) Trace.hasTrace_induced_half

end Masullo.Probe.Controls
