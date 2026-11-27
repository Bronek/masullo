import Masullo.Trace

/-!
# The trace and Weil's functional up to a finite height

Weil's functional of the translate of a test function by `t`, minus its trace at width `a`, is the
sum over the zeros in the critical strip at distance at least `a` from the critical line. Keeping
the terms of absolute height at most `T` leaves an error of norm at most
`C e ^ (t / 2) / (1 + T ^ 2)`, with one `C` for all `a > 0` and `t, T ≥ 0`. Nothing here restricts
the location of any zero.
-/

open Complex Set Filter Topology
open scoped ContDiff

namespace Masullo

namespace TestFunction

/-- Four integrations by parts: quartic decay of the transform in the centred strip. -/
lemma exists_hat_bound (φ : TestFunction) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, |z.re| ≤ 1 / 2 →
    ‖φ.hat z‖ ≤ M / (1 + normSq z) ^ 2 := by
  have hk : ContDiff ℝ 4 φ.pull := (contDiff_infty.1 φ.contDiff 4).comp Real.contDiff_exp
  have hk1 : ContDiff ℝ 3 (deriv φ.pull) := hk.deriv'
  have hk2 : ContDiff ℝ 2 (deriv (deriv φ.pull)) := hk1.deriv'
  have hs := φ.pull_hasCompactSupport
  obtain ⟨A, hA, h0⟩ := WeilExplicit.transform_decay φ.pull_contDiff hs (1 / 2)
  obtain ⟨B, hB, h2⟩ := WeilExplicit.transform_decay hk2 hs.deriv.deriv (1 / 2)
  refine ⟨A + B, add_nonneg hA hB, fun z hz => ?_⟩
  have e : normSq (z / I) = normSq z := by simp
  have hi : |(z / I).im| ≤ 1 / 2 := by simpa using hz
  have a0 := h0 _ hi
  have a2 := h2 _ hi
  have hn : 0 < 1 + normSq z := by linarith [normSq_nonneg z]
  rw [WeilExplicit.transform_deriv (hk1.of_le (by norm_num)) hs.deriv,
    WeilExplicit.transform_deriv (hk.of_le (by norm_num)) hs, transform_pull, e,
    mul_div_cancel₀ _ I_ne_zero, ← mul_assoc, norm_mul, neg_mul_neg, ← sq, norm_pow,
    ← normSq_eq_norm_sq, le_div_iff₀ hn] at a2
  rw [transform_pull, e, le_div_iff₀ hn] at a0
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end TestFunction

namespace Trace

/-- Zeros at distance at least `a` from the critical line, of height at most `T`. -/
def outerZerosUpTo (a T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2| ∧ |ρ.im| ≤ T}

lemma finite_outerZerosUpTo (a T : ℝ) : (outerZerosUpTo a T).Finite := by
  have hc := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm (isCompact_Icc (a := -T) (b := T))
  exact hc.inter_riemannZetaZeros_finite.subset fun ρ h =>
    ⟨⟨⟨h.1.2.1.le, h.1.2.2.le⟩, abs_le.mp h.2.2⟩, h.1.1⟩

/-- Zeros in the critical strip at distance at least `a` from the critical line. -/
def exterior (a : ℝ) : Set ℂ := {ρ | ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2|}

/-- Weil's functional minus the trace at width `a` is the sum over the exterior zeros. -/
lemma hasSum_exterior {a : ℝ} (ha : 0 < a) {φ : TestFunction} {s : ℂ}
    (hs : HasTrace (induced ha φ) s) :
    HasSum ((exterior a).indicator fun ρ : ℂ => (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2))
      (φ.efFunctional - s) := by
  obtain ⟨s', h1, h2⟩ := exists_hasTrace_induced ha φ
  obtain rfl := h1.unique hs
  have e : exterior a = outerZeros a :=
    Set.ext fun _ => by simp [exterior, outerZeros, stripZeros, and_assoc]
  rw [e, ← hasSum_subtype_iff_indicator]
  exact hasSum_outer_of_full_inner (f := fun ρ => (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2))
    φ.hasSum_full h2

/-- After removal of the trace and of the finite sum, Weil's functional is the sum over the
remaining zeros. -/
lemma hasSum_remainder {a T : ℝ} (ha : 0 < a) {φ : TestFunction} {s : ℂ}
    (hs : HasTrace (induced ha φ) s) :
    HasSum ({ρ | ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2| ∧ T < |ρ.im|}.indicator
      fun ρ : ℂ => (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2)) (φ.efFunctional - s -
        ∑ ρ ∈ (finite_outerZerosUpTo a T).toFinset, (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2)) := by
  classical
  set f : ℂ → ℂ := fun ρ => (zeroMult ρ : ℂ) * φ.hat (ρ - 1 / 2)
  have h := (hasSum_subtype_iff_indicator (f := f)).1
    ((finite_outerZerosUpTo a T).toFinset.hasSum f)
  rw [Finite.coe_toFinset] at h
  refine ((hasSum_exterior ha hs).sub h).congr_fun fun ρ => ?_
  simp only [indicator_apply, exterior, outerZerosUpTo, mem_ofPred_eq]
  split_ifs <;> grind

/-- `zeroMult ρ / (1 + |ρ - 1/2|²)`, summable over the zeros in the strip. -/
noncomputable def zeroWeight (ρ : ℂ) : ℝ := (zeroMult ρ : ℝ) / (1 + normSq ((ρ - 1 / 2) / I))

lemma zeroWeight_nonneg (ρ : ℂ) : 0 ≤ zeroWeight ρ :=
  div_nonneg (Nat.cast_nonneg _) (add_nonneg zero_le_one (normSq_nonneg _))

lemma hasSum_zeroWeight :
    HasSum (stripZeros.indicator zeroWeight) (∑' ρ : stripZeros, zeroWeight ρ) :=
  (hasSum_subtype_iff_indicator (f := zeroWeight)).1
    WeilExplicit.summable_zeroMult_div_one_add_normSq.hasSum

/-- **The trace formula up to height `T`.** At the translate of `φ` by `t`, Weil's functional is the
trace at width `a` plus the finite sum over the zeros of height at most `T` at distance at least `a`
from the critical line, up to `C e ^ (t / 2) / (1 + T ^ 2)`, with `C` depending on `φ` only. -/
theorem exists_bound (φ : TestFunction) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) (T : ℝ), 0 ≤ T → ∀ s : ℂ,
      HasTrace (induced ha (φ.translate t ht)) s →
      ‖(φ.translate t ht).efFunctional - s - ∑ ρ ∈ (finite_outerZerosUpTo a T).toFinset,
        (zeroMult ρ : ℂ) * (φ.hat (ρ - 1 / 2) * exp (t * (ρ - 1 / 2)))‖ ≤
          C * Real.exp (t / 2) / (1 + T ^ 2) := by
  obtain ⟨M, hM, hφ⟩ := φ.exists_hat_bound
  refine ⟨M * ∑' ρ : stripZeros, zeroWeight ρ,
    mul_nonneg hM (tsum_nonneg fun _ => zeroWeight_nonneg _), fun a ha t ht T hT s hs => ?_⟩
  have key := HasSum.norm_le_of_bounded (hasSum_remainder (T := T) ha hs)
    (hasSum_zeroWeight.mul_left (M * Real.exp (t / 2) / (1 + T ^ 2))) fun ρ => ?_
  · simp only [TestFunction.hat_translate, mul_comm (exp _)] at key
    exact key.trans_eq (by ring)
  · by_cases hρ : ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2| ∧ T < |ρ.im|
    · rw [indicator_of_mem (by exact hρ), indicator_of_mem hρ.1, TestFunction.hat_translate,
        norm_mul, norm_mul, norm_natCast, norm_exp]
      have hr : |(ρ - 1 / 2).re| ≤ 1 / 2 := by
        norm_num [abs_le]
        constructor <;> linarith [hρ.1.2.1, hρ.1.2.2]
      have h1 : Real.exp (t * (ρ - 1 / 2) : ℂ).re ≤ Real.exp (t / 2) := by
        rw [Real.exp_le_exp, re_ofReal_mul]
        nlinarith [(abs_le.1 hr).2]
      have h2 := hφ _ hr
      have hsq : T ^ 2 ≤ ‖ρ - 1 / 2‖ ^ 2 := by
        gcongr
        exact hρ.2.2.le.trans (by simpa using abs_im_le_norm (ρ - 1 / 2))
      simp only [zeroWeight, normSq_eq_norm_sq, norm_div, norm_I, div_one] at h2 ⊢
      calc _ ≤ (zeroMult ρ : ℝ) * (Real.exp (t / 2) *
              (M / ((1 + T ^ 2) * (1 + ‖ρ - 1 / 2‖ ^ 2)))) := by
            gcongr
            refine h2.trans ?_
            rw [sq (1 + _)]
            gcongr
        _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    · rw [indicator_of_notMem (by exact hρ), norm_zero]
      exact mul_nonneg (by positivity) (indicator_nonneg (fun ρ _ => zeroWeight_nonneg ρ) _)

/-- If every zero in the critical strip of height at most `T` is at distance less than `a` from
the critical line, then the trace at width `a` is Weil's functional up to the same error. -/
theorem exists_bound_of_height (φ : TestFunction) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) (T : ℝ), 0 ≤ T →
      (∀ ρ ∈ stripZeros, |ρ.im| ≤ T → |ρ.re - 1 / 2| < a) → ∀ s : ℂ,
        HasTrace (induced ha (φ.translate t ht)) s →
          ‖(φ.translate t ht).efFunctional - s‖ ≤ C * Real.exp (t / 2) / (1 + T ^ 2) := by
  obtain ⟨C, hC, h⟩ := exists_bound φ
  refine ⟨C, hC, fun a ha t ht T hT hz s hs => ?_⟩
  have he : (finite_outerZerosUpTo a T).toFinset = ∅ := by
    rw [Finite.toFinset_eq_empty, eq_empty_iff_forall_notMem]
    exact fun ρ hρ => (hz ρ hρ.1 hρ.2.2).not_ge hρ.2.1
  simpa only [he, Finset.sum_empty, sub_zero] using h a ha t ht T hT s hs

/-! ### Controls -/

/-- At `a ≥ 1 / 2` the finite sum is empty and the error is zero. -/
theorem outerZerosUpTo_eq_empty {a : ℝ} (ha : 1 / 2 ≤ a) (T : ℝ) : outerZerosUpTo a T = ∅ ∧
    ∀ φ : TestFunction, HasTrace (induced (by linarith : 0 < a) φ) φ.efFunctional :=
  ⟨eq_empty_iff_forall_notMem.2 fun _ hρ =>
    ((abs_sub_half_lt_half hρ.1).trans_le ha).not_ge hρ.2.1, hasTrace_of_half_le ha⟩

/-- Without the finite sum, the bound of `exists_bound` at one width `a` holds for every test
function iff the critical strip has no zeros at distance at least `a` from the critical line: one
such zero makes it fail for some test function already at `t = 0`, since a nonzero error independent
of `T` is not `O(1 / (1 + T ^ 2))`. Neither side is asserted. -/
theorem bound_without_sum_iff {a : ℝ} (ha : 0 < a) :
    (∀ φ : TestFunction, ∃ C : ℝ, ∀ (t : ℝ) (ht : 0 ≤ t) (T : ℝ), 2 ≤ T → ∀ s : ℂ,
      HasTrace (induced ha (φ.translate t ht)) s →
        ‖(φ.translate t ht).efFunctional - s‖ ≤ C * Real.exp (t / 2) / (1 + T ^ 2)) ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2| := by
  rw [← trace_eq_efFunctional_iff ha]
  refine ⟨fun h φ => ?_, fun h φ => ⟨0, fun t ht T _ s hs => by
    rw [(h _).unique hs, sub_self, norm_zero, zero_mul, zero_div]⟩⟩
  obtain ⟨C, hC⟩ := h φ
  obtain ⟨s, hs, -⟩ := exists_hasTrace_induced ha φ
  have e : φ.translate 0 le_rfl = φ := by simp [TestFunction.translate]
  have hl : Tendsto (fun T : ℝ => C * Real.exp (0 / 2) / (1 + T ^ 2)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)).const_div_atTop _
  have h0 := ge_of_tendsto hl ((eventually_ge_atTop 2).mono fun T hT =>
    hC 0 le_rfl T hT s (by rwa [e]))
  rw [e, norm_le_zero_iff, sub_eq_zero] at h0
  rwa [h0]

/-- Changing the weight of one zero changes the finite sum by its transform value. -/
lemma sum_change_weight {a T : ℝ} {ρ : ℂ} (hρ : ρ ∈ Masullo.outerZeros a) (hT : |ρ.im| ≤ T)
    (φ : TestFunction) (η : ℂ) :
    (∑ z ∈ (finite_outerZerosUpTo a T).toFinset,
      ((zeroMult z : ℂ) + if z = ρ then η else 0) * φ.hat (z - 1 / 2)) =
    (∑ z ∈ (finite_outerZerosUpTo a T).toFinset, (zeroMult z : ℂ) * φ.hat (z - 1 / 2)) +
      η * φ.hat (ρ - 1 / 2) := by
  classical
  have hm : ρ ∈ (finite_outerZerosUpTo a T).toFinset :=
    (finite_outerZerosUpTo a T).mem_toFinset.2 ⟨⟨hρ.1, hρ.2.1, hρ.2.2.1⟩, hρ.2.2.2, hT⟩
  simp [add_mul, Finset.sum_add_distrib, ite_mul, hm]

/-- Changing one exterior coefficient by a nonzero complex number spoils the uniform bound,
already for some untranslated test. At all heights in the assertion the zero is included. -/
theorem coefficient_needed {a : ℝ} (ha : 0 < a) {ρ : ℂ} (hρ : ρ ∈ Masullo.outerZeros a) {η : ℂ}
    (hη : η ≠ 0) :
    ∃ (φ : TestFunction) (s : ℂ), HasTrace (induced ha φ) s ∧
      ¬ ∃ C : ℝ, ∀ T ≥ max 2 |ρ.im|,
        ‖φ.efFunctional - s - ∑ z ∈ (finite_outerZerosUpTo a T).toFinset,
           ((zeroMult z : ℂ) + if z = ρ then η else 0) * φ.hat (z - 1 / 2)‖ ≤ C / (1 + T ^ 2) := by
  obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero (ρ - 1 / 2)
  obtain ⟨s, hs, _⟩ := exists_hasTrace_induced ha φ
  refine ⟨φ, s, hs, ?_⟩
  rintro ⟨C, hC⟩
  obtain ⟨K, _, hK⟩ := exists_bound φ
  have e : φ.translate 0 le_rfl = φ := by simp [TestFunction.translate]
  let R (T : ℝ) := φ.efFunctional - s - ∑ z ∈ (finite_outerZerosUpTo a T).toFinset,
    (zeroMult z : ℂ) * φ.hat (z - 1 / 2)
  let v := η * φ.hat (ρ - 1 / 2)
  have hbound (T : ℝ) (hT : max 2 |ρ.im| ≤ T) : ‖v‖ ≤ (K + C) / (1 + T ^ 2) := by
    have h0 : 0 ≤ T := (abs_nonneg _).trans ((le_max_right _ _).trans hT)
    have hi : ‖R T‖ ≤ K / (1 + T ^ 2) := by
      simpa [R, e] using hK a ha 0 le_rfl T h0 s (by rwa [e])
    have hj := hC T hT
    rw [sum_change_weight hρ ((le_max_right _ _).trans hT) φ η, ← sub_sub] at hj
    change ‖R T - v‖ ≤ C / (1 + T ^ 2) at hj
    calc
      ‖v‖ = ‖R T - (R T - v)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖R T‖ + ‖R T - v‖ := norm_sub_le _ _
      _ ≤ _ := by rw [add_div]; exact add_le_add hi hj
  have hl : Tendsto (fun T : ℝ => (K + C) / (1 + T ^ 2)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)).const_div_atTop _
  have hn := ge_of_tendsto hl ((eventually_ge_atTop (max 2 |ρ.im|)).mono hbound)
  exact mul_ne_zero hη hφ (norm_le_zero_iff.1 hn)

end Trace

end Masullo
