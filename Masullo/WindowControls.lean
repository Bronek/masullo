import Masullo.Window

/-!
# Controls for the window criterion

Counterexamples to `Landau.Continues.eq_empty_of_window` with a hypothesis dropped; the window bound
for `windowSum` without one of its terms, and at `θ = 1`; and a function with sign changes to which
the criterion applies.
-/

open MeasureTheory Complex Set Filter Topology Metric
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo.Window.Controls

open Landau

/-- A single simple pole at `p` with residue `a`. -/
lemma pole_div {a p : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p) :
    ∃ h, AnalyticAt ℂ h p ∧ ∀ᶠ s in 𝓝[≠] p, a / (s - p) + g s = a / (s - p) + h s :=
  ⟨g, hg, .of_forall fun _ => rfl⟩

lemma analyticAt_div_sub {a p s : ℂ} (h : s ≠ p) : AnalyticAt ℂ (fun z => a / (z - p)) s :=
  analyticAt_const.div (g := fun z : ℂ => z - p) (by fun_prop) (sub_ne_zero.2 h)

/-- The transform of `e ^ u cos u` has simple poles at `1 ± i`, and these are its only ones. -/
lemma continues_exp_cos : Continues (fun u => Real.exp u * Real.cos u)
    (fun s => 1 / 2 / (s - (1 + I)) + 1 / 2 / (s - (1 - I))) {1 + I, 1 - I} (fun _ => 1 / 2)
      1 1 0 where
  measurable := by fun_prop
  growth u _ := by
    rw [abs_mul, Real.abs_exp, one_mul, one_mul]
    exact mul_le_of_le_one_right (Real.exp_pos u).le (Real.abs_cos_le_one u)
  laplace s hs := by
    obtain ⟨i1, v1⟩ := laplace_exp (a := 1 + I) (s := s) (by simpa) 0
    obtain ⟨i2, v2⟩ := laplace_exp (a := 1 - I) (s := s) (by simpa) 0
    rw [ofReal_zero, mul_zero, Complex.exp_zero] at v1 v2
    rw [div_eq_mul_one_div _ (s - (1 + I)), div_eq_mul_one_div _ (s - (1 - I)), ← v1, ← v2,
      ← integral_const_mul, ← integral_const_mul,
      ← integral_add (i1.const_mul _) (i2.const_mul _)]
    congr 1 with u
    push_cast
    rw [show (1 + I) * (u : ℂ) = u + u * I by ring, show (1 - I) * (u : ℂ) = u + -u * I by ring,
      Complex.exp_add, Complex.exp_add, Complex.cos]
    ring
  analytic s _ hs := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hs
    exact (analyticAt_div_sub hs.1).add (analyticAt_div_sub hs.2)
  finite s r := (toFinite _).subset inter_subset_left
  re_mem ρ hρ := by rcases hρ with rfl | rfl <;> simp
  residue_ne_zero _ _ := by norm_num
  pole ρ hρ := by
    have hI : (1 + I : ℂ) ≠ 1 - I := fun e => by
      have := congrArg Complex.im e
      norm_num at this
    rcases hρ with rfl | rfl
    · exact pole_div (analyticAt_div_sub hI)
    · simp_rw [add_comm (1 / 2 / (_ - (1 + I)))]
      exact pole_div (analyticAt_div_sub hI.symm)

/-- Windows of length zero do not suffice, even for a smooth function: `e ^ u cos u` is positive at
`2 π n` and all the other hypotheses hold. -/
theorem window_length_needed : ∃ (f : ℝ → ℝ) (H κ : ℂ → ℂ) (Z : Set ℂ) (A c : ℝ),
    Continues f H Z κ A c 0 ∧ (∀ ρ ∈ Z, ρ.im = 0 → (κ ρ).re < 0) ∧
      (∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + 0) * U), 0 ≤ f u) ∧ Z ≠ ∅ := by
  refine ⟨_, _, _, _, _, _, continues_exp_cos, ?_, fun X => ?_, (insert_nonempty _ _).ne_empty⟩
  · rintro ρ (rfl | rfl) h <;> simp at h
  · obtain ⟨n, hn⟩ := exists_nat_ge X
    refine ⟨n * (2 * Real.pi), ?_, fun u hu => ?_⟩
    · nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [add_zero, one_mul, Icc_self, mem_singleton_iff] at hu
    simp only [hu, Real.cos_nat_mul_two_pi, mul_one]
    positivity

/-- The sign of the residues at real poles is needed: `e ^ u` is positive everywhere. -/
theorem residue_sign_needed : ∃ (f : ℝ → ℝ) (H κ : ℂ → ℂ) (Z : Set ℂ) (A c : ℝ),
    Continues f H Z κ A c 0 ∧ (∀ u, 0 ≤ f u) ∧ Z ≠ ∅ := by
  refine ⟨Real.exp, fun s => 1 / (s - 1), fun _ => 1, {1}, 1, 1,
    ⟨by fun_prop, fun u _ => by simp, fun s hs => ?_, fun s _ hs => analyticAt_div_sub hs,
      fun s r => (finite_singleton (1 : ℂ)).subset inter_subset_left,
      fun ρ hρ => by simp [mem_singleton_iff.1 hρ], fun _ _ => one_ne_zero, fun ρ hρ =>
      ⟨0, analyticAt_const, .of_forall fun s => by simp [mem_singleton_iff.1 hρ]⟩⟩,
    fun u => (Real.exp_pos u).le, singleton_ne_empty _⟩
  obtain ⟨-, v⟩ := laplace_exp (a := 1) (s := s) (by simpa) 0
  rw [ofReal_zero, mul_zero, Complex.exp_zero] at v
  simpa using v.symm

/-- Without the term `(1 + γ) x` the one-sided bound holds for every `x ≥ 1` and every exponent,
with constant `0`. A criterion that omitted that term would exclude every zero with positive real
part. -/
theorem window_without_linear_term (θ δ : ℝ) : ∀ X, ∃ Y ≥ X, 1 < Y ∧ ∀ x ∈ Icc Y (Y ^ (1 + δ)),
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x ≤ 0 * x ^ θ := fun X =>
  ⟨max X 2, le_max_left _ _, one_lt_two.trans_le (le_max_right _ _), fun x hx => by
    have := (le_max_right X 2).trans hx.1
    rw [zero_mul]
    exact sum_sub_mul_log_nonpos (by linarith)⟩

/-- The window bound holds for `windowSum` at `θ = 1`, where the criterion says nothing. -/
theorem windowSum_window : ∀ X, ∃ Y ≥ X, 1 < Y ∧ ∀ x ∈ Icc Y (Y ^ (1 + (1 : ℝ))),
    windowSum x ≤ (1 + Real.eulerMascheroniConstant) * x ^ (1 : ℝ) := fun X =>
  ⟨max X 2, le_max_left _ _, one_lt_two.trans_le (le_max_right _ _), fun x hx => by
    have := (le_max_right X 2).trans hx.1
    rw [Real.rpow_one, windowSum]
    linarith [sum_sub_mul_log_nonpos (x := x) (by linarith)]⟩

/-! ### A function with windows and sign changes -/

/-- `cos (log u)` satisfies the window hypothesis and has no poles in `Re s > 1 / 2`. -/
lemma continues_cos_log : Continues (fun u => Real.cos (Real.log u))
    (fun s => ∫ u in Ioi (0 : ℝ), (Real.cos (Real.log u) : ℂ) * cexp (-(s * u))) ∅ (fun _ => 0)
      1 1 (1 / 2) where
  measurable := by fun_prop
  growth u hu := (Real.abs_cos_le_one _).trans (by simpa using hu)
  laplace _ _ := by simp
  analytic s hs _ := by
    have hp : HasFPowerSeriesAt (fun w : ℂ => ∫ u in Ioi (0 : ℝ),
        ((Real.cos (Real.log u) : ℝ) : ℂ) * cexp (-((s - w) * u)))
        (FormalMultilinearSeries.ofScalars ℂ
          fun k => coeff (fun u => Real.cos (Real.log u)) k s) 0 := by
      rw [hasFPowerSeriesAt_iff]
      filter_upwards [ball_mem_nhds (0 : ℂ) (by linarith : (0 : ℝ) < s.re - 0)] with w hw
      simpa [FormalMultilinearSeries.coeff_ofScalars, mul_comm] using
        hasSum_coeff (f := fun u => Real.cos (Real.log u)) (A := 1) (c := 0) (by fun_prop)
          (fun u _ => by simpa using Real.abs_cos_le_one (Real.log u)) (mem_ball_zero_iff.1 hw)
    have ha : AnalyticAt ℂ (fun w : ℂ => ∫ u in Ioi (0 : ℝ),
        ((Real.cos (Real.log u) : ℝ) : ℂ) * cexp (-((s - w) * u))) (s - s) := by
      simpa using hp.analyticAt
    have hb : AnalyticAt ℂ (fun w : ℂ => s - w) s := by fun_prop
    simpa [Function.comp_def] using ha.comp hb
  finite _ _ := by simp
  re_mem := by simp
  residue_ne_zero := by simp
  pole := by simp

/-- The window hypothesis does not force eventual nonnegativity. -/
theorem windows_with_sign_changes :
    (∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + 1) * U), 0 ≤ Real.cos (Real.log u)) ∧
      ∀ X, ∃ u ≥ X, Real.cos (Real.log u) = -1 := by
  refine ⟨fun X => ?_, fun X => ?_⟩ <;> obtain ⟨n, hn⟩ := exists_nat_ge X
  · have hv : X ≤ n * (2 * Real.pi) := by
      nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine ⟨Real.exp (n * (2 * Real.pi)), by linarith [Real.add_one_le_exp (n * (2 * Real.pi))],
      fun u hu => ?_⟩
    have hu0 : 0 < u := (Real.exp_pos _).trans_le hu.1
    have hl := (Real.le_log_iff_exp_le hu0).2 hu.1
    have hh : Real.log u ≤ n * (2 * Real.pi) + Real.pi / 2 := by
      rw [Real.log_le_iff_le_exp hu0, Real.exp_add]
      have h2 : 1 + 1 ≤ Real.exp (Real.pi / 2) := by
        linarith [Real.pi_gt_three, Real.add_one_le_exp (Real.pi / 2)]
      exact hu.2.trans (by rw [mul_comm (1 + 1)]; gcongr)
    rw [← Real.cos_sub_nat_mul_two_pi _ n]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  · refine ⟨Real.exp (Real.pi + n * (2 * Real.pi)), ?_, by simp [Real.cos_add_nat_mul_two_pi]⟩
    nlinarith [Real.add_one_le_exp (Real.pi + n * (2 * Real.pi)), Real.pi_gt_three,
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The criterion applies to it. -/
example : (∅ : Set ℂ) = ∅ :=
  continues_cos_log.eq_empty_of_window (by norm_num) (by simp) one_pos windows_with_sign_changes.1

end Masullo.Window.Controls
