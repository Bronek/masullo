import Masullo.QRH.MeanSquare.ReflectionTest
import Masullo.QRH.MeanSquare.DualKernel

/-! # Mean squares of dilated tests

A test `U` dilated by a factor `d ∈ [1, 2]` differs from `U` by the integral of
`y * U'(s y)` over `s ∈ [1, d]`.  The functions `y ↦ y * U'(s y)`, rescaled by an explicit
constant, are unit tests on the interval with its lower end halved.  This bounds the mean
squares of the dilated tests by those of undilated tests with one derivative fewer. -/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

/-- The test interval with its lower end halved. -/
def TestInterval.halve (I : TestInterval) : TestInterval :=
  ⟨I.lo / 2, I.hi, by linarith [I.pos], by linarith [I.pos, I.ordered]⟩

private lemma norm_iteratedDeriv_le_one {I : TestInterval} {m : ℕ} {U : ℝ → ℂ}
    (hU : UnitTest I m U) {i : ℕ} (hi : i ≤ m) (z : ℝ) : ‖iteratedDeriv i U z‖ ≤ 1 := by
  by_cases hz : z ∈ Icc I.lo I.hi
  · exact hU.2.2 i hi z hz
  · rw [image_eq_zero_of_notMem_tsupport
      (fun h => hz (hU.2.1 (tsupport_iteratedDeriv_subset U i h))), norm_zero]
    exact zero_le_one

private lemma unitTest_halve_of_unitTest {I : TestInterval} {m : ℕ} {U : ℝ → ℂ}
    (hU : UnitTest I m U) : UnitTest I.halve m U := by
  refine ⟨hU.1, hU.2.1.trans (Icc_subset_Icc (by show I.lo / 2 ≤ I.lo; linarith [I.pos]) le_rfl),
    fun i hi y _ => norm_iteratedDeriv_le_one hU hi y⟩

/-- The `k + 1`-st derivative of `y ↦ y • g y`. -/
private lemma iteratedDeriv_smul_id_succ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (k : ℕ) (y : ℝ) :
    iteratedDeriv (k + 1) (fun y : ℝ => y • g y) y =
      y • iteratedDeriv (k + 1) g y + ((k : ℝ) + 1) • iteratedDeriv k g y := by
  induction k generalizing g y with
  | zero =>
    have hgd : HasDerivAt g (deriv g y) y := (hg.differentiable (by simp) y).hasDerivAt
    have hd : HasDerivAt (fun y : ℝ => y • g y) (y • deriv g y + (1 : ℝ) • g y) y :=
      (hasDerivAt_id' y).smul hgd
    rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_zero, hd.deriv]
    simp
  | succ k ih =>
    have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
    have h : deriv (fun y : ℝ => y • g y) = fun y => g y + y • deriv g y := by
      funext y
      have hgd : HasDerivAt g (deriv g y) y := (hg.differentiable (by simp) y).hasDerivAt
      have hd : HasDerivAt (fun y : ℝ => y • g y) (y • deriv g y + (1 : ℝ) • g y) y :=
        (hasDerivAt_id' y).smul hgd
      rw [hd.deriv, add_comm, one_smul]
    have hle : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hc2 : ContDiffAt ℝ (k + 1 : ℕ) (fun y : ℝ => y • deriv g y) y :=
      (contDiff_id.smul hg').contDiffAt.of_le hle
    rw [iteratedDeriv_succ', h, iteratedDeriv_fun_add (f := g) (g := fun y : ℝ => y • deriv g y)
      (hg.contDiffAt.of_le hle) hc2, ih (deriv g) hg' y,
      ← iteratedDeriv_succ', ← iteratedDeriv_succ' (n := k) (f := g)]
    push_cast
    module

/-- The test `y ↦ y * U'(s y)` is a smooth function; written with real scalar multiplication. -/
private def scaledTest (U : ℝ → ℂ) (s : ℝ) (y : ℝ) : ℂ := y • deriv U (s * y)

private lemma contDiff_scaledTest {U : ℝ → ℂ} (hU : ContDiff ℝ ∞ U) (s : ℝ) :
    ContDiff ℝ ∞ (scaledTest U s) := by
  have hd : ContDiff ℝ ∞ (deriv U) := (contDiff_infty_iff_deriv.mp hU).2
  exact contDiff_id.smul (hd.comp (contDiff_const.mul contDiff_id))

private lemma iteratedDeriv_scaledTest {U : ℝ → ℂ} (hU : ContDiff ℝ ∞ U) (s : ℝ) (k : ℕ)
    (y : ℝ) : iteratedDeriv (k + 1) (scaledTest U s) y =
      y • (s ^ (k + 1) • iteratedDeriv (k + 2) U (s * y)) +
        ((k : ℝ) + 1) • (s ^ k • iteratedDeriv (k + 1) U (s * y)) := by
  have hd : ContDiff ℝ ∞ (deriv U) := (contDiff_infty_iff_deriv.mp hU).2
  have hg : ContDiff ℝ ∞ (fun y => deriv U (s * y)) := hd.comp (contDiff_const.mul contDiff_id)
  have hsc : ∀ m : ℕ, iteratedDeriv m (fun y => deriv U (s * y)) =
      fun y => s ^ m • iteratedDeriv (m + 1) U (s * y) := fun m => by
    rw [iteratedDeriv_comp_const_smul (hd.of_le (by exact_mod_cast le_top)), iteratedDeriv_succ']
  have := iteratedDeriv_smul_id_succ _ hg k y
  rw [hsc, hsc] at this
  exact this

private lemma norm_scaledTest_deriv_le {I : TestInterval} {j : ℕ} {U : ℝ → ℂ}
    (hU : UnitTest I (j + 1) U) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) {k : ℕ} (hk : k ≤ j) {y : ℝ}
    (hy : y ∈ Icc (I.lo / 2) I.hi) :
    ‖iteratedDeriv k (scaledTest U s) y‖ ≤ 2 ^ j * (I.hi + j + 1) := by
  have hy0 : 0 ≤ y := by linarith [hy.1, I.pos]
  have hyh : y ≤ I.hi := hy.2
  have hhi : 0 ≤ I.hi := hy0.trans hyh
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hs2 : s ≤ 2 := hs.2
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  cases k with
  | zero =>
    rw [iteratedDeriv_zero]
    have := norm_iteratedDeriv_le_one hU (i := 1) (by omega) (s * y)
    rw [iteratedDeriv_one] at this
    simp only [scaledTest, norm_smul, Real.norm_eq_abs, abs_of_nonneg hy0]
    calc y * ‖deriv U (s * y)‖ ≤ I.hi * 1 := by gcongr
      _ ≤ 2 ^ j * (I.hi + j + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  | succ k =>
    rw [iteratedDeriv_scaledTest hU.1]
    have h2 := norm_iteratedDeriv_le_one hU (i := k + 2) (by omega) (s * y)
    have h3 := norm_iteratedDeriv_le_one hU (i := k + 1) (by omega) (s * y)
    have hk2 : (2 : ℝ) ^ (k + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hk
    have hk3 : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    have hkj : ((k : ℝ) + 1) ≤ j := by exact_mod_cast hk
    have hsp : s ^ (k + 1) ≤ 2 ^ (k + 1) := pow_le_pow_left₀ hs0 hs2 _
    have hsq : s ^ k ≤ 2 ^ k := pow_le_pow_left₀ hs0 hs2 _
    have hsp0 : 0 ≤ s ^ (k + 1) := by positivity
    have hsq0 : 0 ≤ s ^ k := by positivity
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hy0,
      abs_of_nonneg hsp0, abs_of_nonneg hsq0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)]
    have e1 : y * (s ^ (k + 1) * ‖iteratedDeriv (k + 2) U (s * y)‖) ≤ I.hi * 2 ^ j := by
      calc _ ≤ I.hi * (2 ^ (k + 1) * 1) := by gcongr
        _ ≤ _ := by nlinarith
    have e2 : ((k : ℝ) + 1) * (s ^ k * ‖iteratedDeriv (k + 1) U (s * y)‖) ≤ j * 2 ^ j := by
      calc _ ≤ ((k : ℝ) + 1) * (2 ^ k * 1) := by gcongr
        _ ≤ _ := by nlinarith
    nlinarith

private lemma unitTest_scaled {I : TestInterval} {j : ℕ} {U : ℝ → ℂ} (hU : UnitTest I (j + 1) U)
    {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) :
    UnitTest I.halve j fun y => (((2 ^ j * (I.hi + j + 1) : ℝ)⁻¹ : ℝ) : ℂ) * scaledTest U s y := by
  have hK : 0 < (2 : ℝ) ^ j * (I.hi + j + 1) := by
    have := I.pos
    have := I.ordered
    exact mul_pos (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hV := contDiff_scaledTest hU.1 s
  refine ⟨contDiff_const.mul hV, ?_, fun k hk y hy => ?_⟩
  · refine tsupport_mul_subset_right.trans (closure_minimal (fun y hy => ?_) isClosed_Icc)
    have hne : deriv U (s * y) ≠ 0 := fun h => hy (by simp [scaledTest, h])
    have hmem : s * y ∈ Icc I.lo I.hi :=
      hU.2.1 (tsupport_deriv_subset (subset_tsupport _ hne))
    have hlo := I.pos
    have hy0 : 0 < y := by
      by_contra hneg
      nlinarith [hmem.1, hs.1, hs.2]
    refine ⟨?_, ?_⟩
    · show I.lo / 2 ≤ y
      nlinarith [hmem.1, hs.2]
    · show y ≤ I.hi
      nlinarith [hmem.2, hs.1]
  · have hc : ContDiffAt ℝ k (scaledTest U s) y :=
      hV.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_const_mul _ hc, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (inv_nonneg.2 hK.le)]
    have := norm_scaledTest_deriv_le hU hs hk hy
    calc _ ≤ ((2 : ℝ) ^ j * (I.hi + j + 1))⁻¹ * (2 ^ j * (I.hi + j + 1)) := by gcongr
      _ = 1 := inv_mul_cancel₀ hK.ne'

/-- Cauchy–Schwarz on an interval of length one. -/
private lemma sq_intervalIntegral_le {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ s in (1 : ℝ)..2, g s) ^ 2 ≤ ∫ s in (1 : ℝ)..2, g s ^ 2 := by
  set m := ∫ s in (1 : ℝ)..2, g s with hm
  have h0 : 0 ≤ ∫ s in (1 : ℝ)..2, (g s - m) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  have hexp : ∀ s, (g s - m) ^ 2 = (g s ^ 2 - (2 * m) * g s) + m ^ 2 := fun s => by ring
  have c1 : IntervalIntegrable (fun s => g s ^ 2) volume 1 2 :=
    (by fun_prop : Continuous fun s => g s ^ 2).intervalIntegrable _ _
  have c2 : IntervalIntegrable (fun s => 2 * m * g s) volume 1 2 :=
    (by fun_prop : Continuous fun s => 2 * m * g s).intervalIntegrable _ _
  simp_rw [hexp] at h0
  rw [intervalIntegral.integral_add (c1.sub c2) intervalIntegrable_const,
    intervalIntegral.integral_sub c1 c2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, ← hm] at h0
  norm_num at h0
  nlinarith

/-- Mean squares of tests dilated by a row-dependent factor `d ρ ∈ [1, 2]` are controlled by
the mean squares of undilated tests with one derivative fewer, on the halved interval. -/
theorem exists_dilated_meanSquare_le (I : TestInterval) (j : ℕ) : ∃ C ≥ (0 : ℝ),
    ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c : R → N → ℂ) (x : N → ℝ)
      (d : R → ℝ) {M : ℝ}, (∀ ρ ∈ rows, d ρ ∈ Set.Icc 1 2) →
      (∀ V, UnitTest I.halve j V → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * V (x n)‖ ^ 2 ≤ M) →
      ∀ U, UnitTest I (j + 1) U →
        ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * U (d ρ * x n)‖ ^ 2 ≤ C * M := by
  set K : ℝ := 2 ^ j * (I.hi + j + 1) with hKdef
  have hK : 0 < K := by
    have := I.pos
    have := I.ordered
    exact mul_pos (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  refine ⟨2 + 2 * K ^ 2, by positivity, ?_⟩
  intro R N rows cols c x d M hd hM U hU
  have hdU : Continuous (deriv U) := (contDiff_infty_iff_deriv.mp hU.1).2.continuous
  -- the integrand
  set H : R → ℝ → ℂ := fun ρ s => ∑ n ∈ cols, c ρ n * ((x n : ℝ) • deriv U (s * x n)) with hH
  have hHc : ∀ ρ, Continuous (H ρ) := fun ρ =>
    continuous_finsetSum _ fun n _ => by fun_prop
  -- fundamental theorem of calculus, one column
  have hftc : ∀ (y e : ℝ), U (e * y) = U y + ∫ s in (1 : ℝ)..e, y • deriv U (s * y) := by
    intro y e
    have hder : ∀ s ∈ uIcc (1 : ℝ) e, HasDerivAt (fun s => U (s * y)) (y • deriv U (s * y)) s :=
      fun s _ => by
        have h1 : HasDerivAt U (deriv U (s * y)) (s * y) :=
          (hU.1.differentiable (by simp) _).hasDerivAt
        have h2 : HasDerivAt (fun s : ℝ => s * y) y s := by
          simpa using (hasDerivAt_id' s).mul_const y
        exact h1.scomp s h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((by fun_prop : Continuous fun s : ℝ => y • deriv U (s * y)).intervalIntegrable _ _)]
    simp
  -- the representation of each row
  have hrep : ∀ ρ ∈ rows, ∑ n ∈ cols, c ρ n * U (d ρ * x n) =
      ∑ n ∈ cols, c ρ n * U (x n) + ∫ s in (1 : ℝ)..(d ρ), H ρ s := by
    intro ρ _
    simp only [hH]
    rw [intervalIntegral.integral_finsetSum fun n _ =>
      (by fun_prop : Continuous fun s : ℝ => c ρ n * ((x n : ℝ) • deriv U (s * x n))
        ).intervalIntegrable _ _]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hftc (x n) (d ρ), mul_add]
  -- pointwise bound on the integrand
  have hpt : ∀ s ∈ Icc (1 : ℝ) 2, ∑ ρ ∈ rows, ‖H ρ s‖ ^ 2 ≤ K ^ 2 * M := by
    intro s hs
    have h := hM _ (unitTest_scaled hU hs)
    have he : ∀ ρ, H ρ s = (K : ℂ) * ∑ n ∈ cols, c ρ n *
        ((((K⁻¹ : ℝ)) : ℂ) * scaledTest U s (x n)) := fun ρ => by
      simp only [hH, scaledTest, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
      push_cast
      field_simp
    simp_rw [he, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real, Real.norm_of_nonneg
      hK.le]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  -- assemble
  have hrow : ∀ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * U (d ρ * x n)‖ ^ 2 ≤
      2 * ‖∑ n ∈ cols, c ρ n * U (x n)‖ ^ 2 + 2 * ∫ s in (1 : ℝ)..2, ‖H ρ s‖ ^ 2 := by
    intro ρ hρ
    obtain ⟨hd1, hd2⟩ := hd ρ hρ
    rw [hrep ρ hρ]
    set a := ∑ n ∈ cols, c ρ n * U (x n)
    set b := ∫ s in (1 : ℝ)..(d ρ), H ρ s
    have hn : ‖b‖ ≤ ∫ s in (1 : ℝ)..2, ‖H ρ s‖ :=
      (intervalIntegral.norm_integral_le_integral_norm hd1).trans
        (intervalIntegral.integral_mono_interval le_rfl hd1 hd2
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((hHc ρ).norm.intervalIntegrable _ _))
    have hcs := sq_intervalIntegral_le (hHc ρ).norm
    have hb : ‖b‖ ^ 2 ≤ ∫ s in (1 : ℝ)..2, ‖H ρ s‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
    have hab := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), pow_le_pow_left₀ (norm_nonneg _) hab 2]
  have hA := hM U (unitTest_halve_of_unitTest (m := j) (U := U)
    ⟨hU.1, hU.2.1, fun i hi y hy => hU.2.2 i (by omega) y hy⟩)
  have hint : ∑ ρ ∈ rows, ∫ s in (1 : ℝ)..2, ‖H ρ s‖ ^ 2 ≤ K ^ 2 * M := by
    rw [← intervalIntegral.integral_finsetSum (f := fun ρ s => ‖H ρ s‖ ^ 2) fun ρ _ =>
      ((hHc ρ).norm.pow 2).intervalIntegrable _ _]
    calc _ ≤ ∫ s in (1 : ℝ)..2, K ^ 2 * M :=
          intervalIntegral.integral_mono_on (by norm_num)
            (f := fun s => ∑ ρ ∈ rows, ‖H ρ s‖ ^ 2)
            ((continuous_finsetSum _ fun ρ _ => (hHc ρ).norm.pow 2).intervalIntegrable _ _)
            intervalIntegrable_const hpt
      _ = K ^ 2 * M := by rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
  calc _ ≤ ∑ ρ ∈ rows, (2 * ‖∑ n ∈ cols, c ρ n * U (x n)‖ ^ 2 +
          2 * ∫ s in (1 : ℝ)..2, ‖H ρ s‖ ^ 2) := Finset.sum_le_sum hrow
    _ = 2 * ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * U (x n)‖ ^ 2 +
          2 * ∑ ρ ∈ rows, ∫ s in (1 : ℝ)..2, ‖H ρ s‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (2 + 2 * K ^ 2) * M := by nlinarith

end Masullo.QRH.MeanSquare
