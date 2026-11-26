import Masullo.Dyadic

/-!
# The Liouville window criterion

`liouvilleSum x = ∑_{n ≤ x} λ(n)`, with `λ(n) = (-1) ^ Ω(n)` the Liouville function.
`WindowBound θ δ C` says that for arbitrarily large `Y` there is a sign `ε = ±1` with
`ε liouvilleSum x ≤ C x ^ θ` for all `x ∈ [Y, Y ^ (1 + δ)]`. For `θ ≥ 1 / 2` it rules out zeros of
zeta in `Re s > θ` (`riemannZeta_ne_zero_of_windowBound`). The exponent is exact: on paper the
Riemann hypothesis gives `|liouvilleSum x| ≤ C x ^ θ` for every `θ > 1 / 2`. That direction is not
formalised.

The Laplace transform of `liouvilleSum (e ^ u)` is `ζ(2s) / (s ζ(s))`, from the Euler product of
`∑ λ(n) n ^ (-s)`. Its poles in `Re s > 1 / 2` are the zeros of zeta, of their full multiplicity, so
the generic argument is `Masullo.Landau.ContinuesMero.eq_empty_of_window`. Zeta has no zeros in
`(0, 1)`, so no sign condition at real poles arises.

`MeanBound θ δ C` bounds short-interval increments instead. For arbitrarily large `Y` there are a
width `0 < h ≤ Y ^ θ` and a sign `ε = ±1`, both fixed for the window, such that the integral from
`Y` to `x` of the positive part of `ε (liouvilleSum (t + h) - liouvilleSum t) / h` is at most
`C x ^ θ` for every `x ∈ [Y, Y ^ (1 + δ)]`. The integral is cumulative from `Y`; the same bound on
each block `[y, 2 y]` starting in the window implies it (`BlockMeanBound.meanBound`). It also rules
out zeros in `Re s > θ` (`riemannZeta_ne_zero_of_meanBound`), but its exponent is not faithful. The
positive part discards cancellation: increments of size `√h` would make the integral of order
`x h ^ (-1 / 2) ≥ x ^ (1 - θ / 2)`, so the hypothesis is expected to hold only for `θ` above about
`2 / 3`, and it is a quasi-Riemann-hypothesis criterion. The average `smoothSum h` of
`liouvilleSum` over `[x, x + h]` is within `h + 1` of `liouvilleSum x` and its derivative is the
increment, so splitting the window at `Y ^ (1 + δ / 2)` gives `WindowBound θ (δ / (2 + δ))`.

Both hypotheses hold at `θ = 1` (`Masullo/LiouvilleControls.lean`); neither is proved here for any
`θ < 1`.

OpenAI Codex proposed the Liouville form of the trace gap; a Claude Fable subagent proposed the
route through Landau's argument with poles of finite order; Claude formalised it.
-/


open MeasureTheory Complex Set Filter Topology Metric
open ArithmeticFunction (liouville liouville_apply liouville_apply_one liouville_apply_mul)

namespace Masullo.Liouville

open Landau Window Spectrum WeilExplicit

/-- `∑_{n ≤ x} λ(n)`. -/
noncomputable def liouvilleSum (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (liouville n : ℝ)

lemma abs_liouville_le (n : ℕ) : |(liouville n : ℝ)| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [liouville_apply hn]
    simp

lemma norm_liouville_le (n : ℕ) : ‖(liouville n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact abs_liouville_le n

lemma liouville_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [liouville_apply hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp, pow_one]

/-! ### The Dirichlet series -/

/-- `n ↦ λ(n) n ^ (-s)` is completely multiplicative. -/
noncomputable def summandHom (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := (liouville n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp
  map_one' := by simp [liouville_apply_one]
  map_mul' m n := by
    simp only [liouville_apply_mul, Int.cast_mul, Nat.cast_mul, natCast_mul_natCast_cpow]
    ring

lemma summable_summandHom {s : ℂ} (hs : 1 < s.re) :
    Summable fun n => ‖summandHom s n‖ :=
  (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
    simp only [summandHom, riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_liouville_le n)

lemma hasProd_LSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 + (p : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => (liouville n : ℂ)) s) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_summandHom hs)
  have e : ∑' n, summandHom s n =
      LSeries (fun n => (liouville n : ℂ)) s := by
    simp only [summandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
      LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]
  rw [e] at h
  refine h.congr_fun fun p => ?_
  simp [summandHom, liouville_prime p.prop]

/-- `∑ λ(n) n ^ (-s) = ζ(2s) / ζ(s)` for `Re s > 1`. -/
lemma LSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (liouville n : ℂ)) s = riemannZeta (2 * s) / riemannZeta s := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  rw [eq_div_iff (riemannZeta_ne_zero_of_one_le_re hs.le)]
  refine ((hasProd_LSeries_liouville hs).mul (riemannZeta_eulerProduct_hasProd hs)).unique
    ((riemannZeta_eulerProduct_hasProd h2).congr_fun fun p => ?_)
  rw [show -(2 * s) = 2 * -s by ring, cpow_ofNat_mul, ← mul_inv]
  congr 1
  ring

/-! ### The Laplace transform -/

lemma measurable_liouvilleSum : Measurable liouvilleSum :=
  (measurable_from_nat (f := fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (liouville n : ℝ))).comp
    Nat.measurable_floor

lemma abs_liouvilleSum_le {x : ℝ} (hx : 0 ≤ x) : |liouvilleSum x| ≤ x := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun n _ => abs_liouville_le n).trans ?_
  simpa using Nat.floor_le hx

lemma cpow_ofReal_exp (u : ℝ) (w : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ w = cexp (u * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'), ← ofReal_log
    (Real.exp_pos u).le, Real.log_exp]

lemma integrableOn_liouvilleSum {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => (liouvilleSum (Real.exp u) : ℂ) * cexp (-(s * u))) (Ioi 0) := by
  simpa using integrable_kernel (A := 1) (c := 1)
    (measurable_liouvilleSum.comp Real.measurable_exp)
    (fun u _ => by simpa using abs_liouvilleSum_le (Real.exp_pos u).le) 0 hs

/-- The Laplace transform of `liouvilleSum (e ^ u)` is `ζ(2s) / (s ζ(s))` for `Re s > 1`. -/
lemma integral_liouvilleSum {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (liouvilleSum (Real.exp u) : ℂ) * cexp (-(s * u)) =
      riemannZeta (2 * s) / riemannZeta s / s := by
  have hO : (fun n => ∑ k ∈ Finset.Icc 1 n, ‖(liouville k : ℂ)‖) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (.of_forall fun n => ?_)
    rw [Real.rpow_one, one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
      Real.norm_natCast]
    calc _ ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun k _ => norm_liouville_le k
      _ = n := by simp
  have h := LSeries_eq_mul_integral' (fun n => (liouville n : ℂ)) zero_le_one (by simpa) hO
  have e := integral_comp_exp_Ioi
    (fun y : ℝ => (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (liouville k : ℂ)) * (y : ℂ) ^ (-(s + 1))) 0
  rw [Real.exp_zero] at e
  rw [← e, LSeries_liouville hs] at h
  rw [h, mul_div_cancel_left₀ _ (ne_zero_of_one_lt_re hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [real_smul, cpow_ofReal_exp, liouvilleSum, ofReal_exp]
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  ring_nf

/-! ### The continuation -/

/-- The continuation of the Laplace transform of `C e ^ (θ u) - ε liouvilleSum (e ^ u)`. -/
noncomputable def continuation (C θ ε : ℝ) (s : ℂ) : ℂ :=
  C / (s - θ) - ε * (riemannZeta (2 * s) * (s - 1) / (s * zetaNum s))

lemma continuation_eq {C θ ε : ℝ} {s : ℂ} (hs : 1 < s.re) :
    continuation C θ ε s = C / (s - θ) - ε * (riemannZeta (2 * s) / riemannZeta s / s) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 fun e => by simp [e] at hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  have h0 := ne_zero_of_one_lt_re hs
  rw [continuation, zetaNum_of_ne (sub_ne_zero.1 hs1)]
  field_simp

lemma analyticAt_riemannZeta_two {s : ℂ} (h : 2 * s ≠ 1) :
    AnalyticAt ℂ (fun z => riemannZeta (2 * z)) s := by
  have ho : IsOpen {z : ℂ | 2 * z ≠ 1} := isOpen_ne_fun (by fun_prop) continuous_const
  refine DifferentiableOn.analyticAt (fun z hz => ?_) (ho.mem_nhds h)
  exact ((differentiableAt_riemannZeta hz).comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 2 * z) z)).differentiableWithinAt

lemma two_mul_ne_one {θ : ℝ} (hθ : 1 / 2 ≤ θ) {s : ℂ} (hs : θ < s.re) : 2 * s ≠ 1 :=
  fun e => by have := congrArg re e; simp at this; linarith

lemma analyticAt_continuation {C θ ε : ℝ} (hθ : 1 / 2 ≤ θ) {s : ℂ} (hs : θ < s.re)
    (h : riemannZeta s ≠ 0) : AnalyticAt ℂ (continuation C θ ε) s := by
  have h0 : s ≠ 0 := fun e => by simp [e] at hs; linarith
  have hθs : s - θ ≠ 0 := sub_ne_zero.2 fun e => by simp [e] at hs
  exact (analyticAt_const.div (g := fun s : ℂ => s - θ) (by fun_prop) hθs).sub
    (analyticAt_const.mul (((analyticAt_riemannZeta_two (two_mul_ne_one hθ hs)).mul
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) s)).div
      (analyticAt_id.mul (differentiable_zetaNum.analyticAt s)) (mul_ne_zero h0
        (zetaNum_ne_zero h))))

lemma continues {C θ ε : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hε : ε ≠ 0) :
    ContinuesMero (fun u => C * Real.exp (θ * u) - ε * liouvilleSum (Real.exp u))
      (continuation C θ ε) {ρ | θ < ρ.re ∧ riemannZeta ρ = 0} (|C| + |ε|) 1 θ where
  measurable := by
    have := measurable_liouvilleSum.comp Real.measurable_exp
    unfold Function.comp at this
    fun_prop
  growth u hu := by
    have h1 := abs_liouvilleSum_le (Real.exp_pos u).le
    have h2 : Real.exp (θ * u) ≤ Real.exp (1 * u) := Real.exp_le_exp.2 (by nlinarith)
    calc |C * Real.exp (θ * u) - ε * liouvilleSum (Real.exp u)|
        ≤ |C| * Real.exp (θ * u) + |ε| * |liouvilleSum (Real.exp u)| := by
          refine (abs_sub _ _).trans_eq ?_
          rw [abs_mul, abs_mul, Real.abs_exp]
      _ ≤ |C| * Real.exp (1 * u) + |ε| * Real.exp (1 * u) := by
          gcongr
          rwa [one_mul]
      _ = _ := by ring
  laplace s hs := by
    obtain ⟨i1, v1⟩ := laplace_exp (a := θ) (s := s) (by simp; linarith) 0
    rw [ofReal_zero, mul_zero, Complex.exp_zero] at v1
    have e (u : ℝ) : ((C * Real.exp (θ * u) - ε * liouvilleSum (Real.exp u) : ℝ) : ℂ) *
        cexp (-(s * u)) = C * (cexp (θ * u) * cexp (-(s * u))) -
          ε * ((liouvilleSum (Real.exp u) : ℂ) * cexp (-(s * u))) := by
      push_cast
      ring
    simp_rw [e]
    rw [integral_sub (i1.const_mul _) ((integrableOn_liouvilleSum hs).const_mul _),
      integral_const_mul, integral_const_mul, v1, integral_liouvilleSum hs, continuation_eq hs]
    ring
  analytic s hs hZ := analyticAt_continuation hθ hs fun h => hZ ⟨hs, h⟩
  finite s r := ((isCompact_closedBall s r).inter_riemannZetaZeros_finite).subset
    fun ρ h => ⟨h.2, h.1.2⟩
  re_mem ρ h := ⟨h.1, by
    by_contra hlt
    exact riemannZeta_ne_zero_of_one_le_re (by linarith) h.2⟩
  pole ρ h := by
    have h0 : ρ ≠ 0 := fun e => by have := h.1; simp [e] at this; linarith
    have h1 : ρ ≠ 1 := fun e => riemannZeta_one_ne_zero (e ▸ h.2)
    have hθρ : ρ - θ ≠ 0 := sub_ne_zero.2 fun e => by have := h.1; simp [e] at this
    have h2 := two_mul_ne_one hθ h.1
    have hz2 : riemannZeta (2 * ρ) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; linarith [h.1])
    obtain ⟨g, hg, hg0, hfac⟩ := (differentiable_zetaNum.analyticAt ρ).analyticOrderAt_eq_natCast.1
      (analyticOrderAt_zetaNum ρ)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (zeroMult_pos h.2).ne'
    refine ⟨n, fun s => (s - ρ) ^ (n + 1) * (C / (s - θ)) -
      ε * (riemannZeta (2 * s) * (s - 1) / (s * g s)), ?_, ?_, ?_⟩
    · exact ((by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s - ρ) ^ (n + 1)) ρ).mul
        (analyticAt_const.div (g := fun s : ℂ => s - θ) (by fun_prop) hθρ)).sub
        (analyticAt_const.mul (((analyticAt_riemannZeta_two h2).mul
          (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ)).div (analyticAt_id.mul hg)
          (mul_ne_zero h0 hg0)))
    · simp only [sub_self, zero_pow (Nat.succ_ne_zero n), zero_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero (ofReal_ne_zero.2 hε)
        (div_ne_zero (mul_ne_zero hz2 (sub_ne_zero.2 h1)) (mul_ne_zero h0 hg0))
    · filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        (eventually_ne_nhds h0).filter_mono nhdsWithin_le_nhds,
        (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
        ((continuous_sub_right (θ : ℂ)).continuousAt.eventually_ne hθρ).filter_mono
          nhdsWithin_le_nhds] with s hs hne hs0 hgs hsθ
      have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 hne
      rw [continuation, hs, hn, smul_eq_mul]
      field_simp


/-! ### The window criterion -/

/-- For arbitrarily large `Y` there is a sign `ε = ±1`, which may depend on `Y`, with
`ε liouvilleSum x ≤ C x ^ θ` for all `x ∈ [Y, Y ^ (1 + δ)]`. -/
def WindowBound (θ δ C : ℝ) : Prop :=
  ∀ X, ∃ Y ≥ X, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ x ∈ Icc Y (Y ^ (1 + δ)), ε * liouvilleSum x ≤ C * x ^ θ

/-- `WindowBound θ δ C` with `θ ≥ 1 / 2` rules out zeros of zeta to the right of `θ`. The converse
is not asserted. -/
theorem riemannZeta_ne_zero_of_windowBound {θ δ C : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ)
    (h : WindowBound θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  rcases le_or_gt 1 θ with hθ1 | hθ1
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)
  -- one sign occurs for arbitrarily large `Y`
  obtain ⟨ε, hε, hw⟩ : ∃ ε : ℝ, ε ≠ 0 ∧ ∀ X, ∃ Y ≥ X,
      ∀ x ∈ Icc Y (Y ^ (1 + δ)), ε * liouvilleSum x ≤ C * x ^ θ := by
    by_contra hne
    push Not at hne
    obtain ⟨X₁, hX₁⟩ := hne 1 one_ne_zero
    obtain ⟨X₂, hX₂⟩ := hne (-1) (by norm_num)
    obtain ⟨Y, hY, ε, hε, hb⟩ := h (max X₁ X₂)
    rcases hε with rfl | rfl
    · obtain ⟨x, hx, hlt⟩ := hX₁ Y (le_of_max_le_left hY)
      exact (hb x hx).not_gt hlt
    · obtain ⟨x, hx, hlt⟩ := hX₂ Y (le_of_max_le_right hY)
      exact (hb x hx).not_gt hlt
  have hZ := (continues (C := C) hθ hθ1 hε).eq_empty_of_window (by linarith) ?_ hδ ?_
  · exact fun h0 => (hZ ▸ ⟨hρ, h0⟩ : ρ ∈ (∅ : Set ℂ)).elim
  · rintro ρ ⟨hr, hz⟩ hi
    lift ρ to ℝ using hi
    have h1 : ρ < 1 := lt_of_not_ge fun h1 =>
      riemannZeta_ne_zero_of_one_le_re (by simpa using h1) hz
    exact (riemannZeta_ofReal_ne_zero (by simp at hr; linarith) h1 hz).elim
  · intro X
    obtain ⟨Y, hY, hw⟩ := hw (Real.exp X)
    have hY0 : 0 < Y := (Real.exp_pos X).trans_le hY
    refine ⟨Real.log Y, (Real.le_log_iff_exp_le hY0).2 hY, fun u hu => ?_⟩
    have := hw (Real.exp u) ⟨(Real.log_le_iff_le_exp hY0).1 hu.1, by
      rw [Real.rpow_def_of_pos hY0, mul_comm]
      exact Real.exp_le_exp.2 hu.2⟩
    rw [← Real.exp_mul, mul_comm u] at this
    linarith

/-! ### A one-sided short-interval mean

`smoothSum h x` averages `liouvilleSum` over `[x, x + h]`. It differs from `liouvilleSum x` by at
most `h + 1`, and its derivative is the short-interval increment `(L (x + h) - L x) / h`. -/

/-- For arbitrarily large `Y` there are a width `0 < h ≤ Y ^ θ` and a sign `ε = ±1`, which may
depend on `Y` but are fixed across its window, such that the integral from `Y` to `x` of the
positive part of `ε (liouvilleSum (t + h) - liouvilleSum t) / h` is at most `C x ^ θ` for every
`x ∈ [Y, Y ^ (1 + δ)]`. The integral is cumulative from `Y`, not over a block ending at `x`. -/
def MeanBound (θ δ C : ℝ) : Prop :=
  ∀ X, ∃ Y ≥ X, ∃ h : ℝ, 0 < h ∧ h ≤ Y ^ θ ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ x ∈ Icc Y (Y ^ (1 + δ)),
      ∫ t in Y..x, max (ε * (liouvilleSum (t + h) - liouvilleSum t) / h) 0 ≤ C * x ^ θ

/-- `(1 / h) ∫_x^{x + h} liouvilleSum`. -/
noncomputable def smoothSum (h x : ℝ) : ℝ := (∫ t in x..x + h, liouvilleSum t) / h

lemma abs_liouvilleSum_le_abs (x : ℝ) : |liouvilleSum x| ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · exact (abs_liouvilleSum_le hx).trans (le_abs_self x)
  · simp [liouvilleSum, Nat.floor_eq_zero.2 (hx.trans one_pos)]

lemma intervalIntegrable_liouvilleSum (h a b : ℝ) :
    IntervalIntegrable (fun x => liouvilleSum (x + h)) volume a b := by
  refine (intervalIntegrable_const (c := |a| + |b| + |h|)).mono_fun
    (measurable_liouvilleSum.comp (measurable_add_const h)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_uIoc).2 (.of_forall fun x hx => ?_))
  have h1 : -(|a| + |b|) ≤ min a b :=
    le_min (by linarith [neg_abs_le a, abs_nonneg b]) (by linarith [neg_abs_le b, abs_nonneg a])
  have h2 : max a b ≤ |a| + |b| :=
    max_le (by linarith [le_abs_self a, abs_nonneg b]) (by linarith [le_abs_self b, abs_nonneg a])
  have hx' : |x| ≤ |a| + |b| := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simp only [Real.norm_eq_abs]
  refine (abs_liouvilleSum_le_abs (x + h)).trans ((abs_add_le x h).trans (le_trans ?_
    (le_abs_self _)))
  linarith

lemma intervalIntegrable_increment (ε h a b : ℝ) :
    IntervalIntegrable (fun x => ε * (liouvilleSum (x + h) - liouvilleSum x) / h) volume a b :=
  (((intervalIntegrable_liouvilleSum h a b).sub
    (by simpa using intervalIntegrable_liouvilleSum 0 a b)).const_mul ε).div_const h

/-- The change of `smoothSum h` over `[u, v]` is the integral of the increment. -/
lemma smoothSum_sub (h u v : ℝ) : smoothSum h v - smoothSum h u =
    (∫ x in u..v, (liouvilleSum (x + h) - liouvilleSum x)) / h := by
  have hL (a b : ℝ) : IntervalIntegrable liouvilleSum volume a b := by
    simpa using intervalIntegrable_liouvilleSum 0 a b
  rw [smoothSum, smoothSum, ← sub_div, intervalIntegral.integral_sub
    (intervalIntegrable_liouvilleSum h u v) (hL u v),
    intervalIntegral.integral_comp_add_right (fun x => liouvilleSum x)]
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hL u (u + h)) (hL (u + h) (v + h))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hL u v) (hL v (v + h))
  congr 1
  linarith

lemma abs_liouvilleSum_sub_le {x t : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t) :
    |liouvilleSum t - liouvilleSum x| ≤ t - x + 1 := by
  have hf : ⌊x⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hxt
  have e : liouvilleSum t - liouvilleSum x =
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊t⌋₊, (liouville n : ℝ) := by
    have hI (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [liouvilleSum, liouvilleSum, hI, hI,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hf]
    ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ =>
    abs_liouville_le n).trans ?_)
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.cast_sub hf]
  linarith [Nat.floor_le (hx.trans hxt), Nat.lt_floor_add_one x]

lemma abs_smoothSum_sub_le {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) :
    |smoothSum h x - liouvilleSum x| ≤ h + 1 := by
  have e : smoothSum h x - liouvilleSum x =
      (∫ t in x..x + h, (liouvilleSum t - liouvilleSum x)) / h := by
    rw [intervalIntegral.integral_sub (by simpa using intervalIntegrable_liouvilleSum 0 x (x + h))
      intervalIntegrable_const, intervalIntegral.integral_const, smoothSum, smul_eq_mul]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + h)
    (C := h + 1) (f := fun t => liouvilleSum t - liouvilleSum x) fun t ht => by
      rw [uIoc_of_le (by linarith)] at ht
      exact (abs_liouvilleSum_sub_le hx ht.1.le).trans (by linarith [ht.2])
  simpa [Real.norm_eq_abs, abs_of_pos hh, mul_comm] using this

/-- Across `[u, v] ⊆ [Y, x]`, `ε smoothSum h` increases by at most the integral over `[Y, x]` of
the positive part of `ε (liouvilleSum (t + h) - liouvilleSum t) / h`. -/
lemma mul_smoothSum_sub_le {ε h Y u v x : ℝ} (hu : Y ≤ u) (huv : u ≤ v) (hv : v ≤ x) :
    ε * smoothSum h v - ε * smoothSum h u ≤
      ∫ t in Y..x, max (ε * (liouvilleSum (t + h) - liouvilleSum t) / h) 0 := by
  have hg := intervalIntegrable_increment ε h
  rw [← mul_sub, smoothSum_sub, mul_div_assoc', ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_div]
  calc (∫ t in u..v, ε * (liouvilleSum (t + h) - liouvilleSum t) / h)
      ≤ ∫ t in u..v, max (ε * (liouvilleSum (t + h) - liouvilleSum t) / h) 0 :=
        intervalIntegral.integral_mono_on huv (hg u v) ⟨(hg u v).1.pos_part, (hg u v).2.pos_part⟩
          fun _ _ => le_max_left _ _
    _ ≤ _ := intervalIntegral.integral_mono_interval hu huv hv
          (.of_forall fun _ => le_max_right _ _) ⟨(hg Y x).1.pos_part, (hg Y x).2.pos_part⟩

/-- The cumulative one-sided mean bound on `[Y, Y ^ (1 + δ)]` gives a one-sided pointwise bound
`(|C| + 2) x ^ θ` on a window `[Z, Z ^ (1 + δ / (2 + δ))]` inside it. Split at
`M = Y ^ (1 + δ / 2)`. If `ε smoothSum h m ≤ 0` for some `m ∈ [Y, M]`, then `ε liouvilleSum` is
bounded above on `[m, m ^ (1 + δ / (2 + δ))]`; otherwise `-ε liouvilleSum` is bounded above on
`[Y, Y ^ (1 + δ / (2 + δ))]`. -/
lemma window_of_mean {ε θ δ C Y h : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (hY : 1 < Y) (hh : 0 < h)
    (hhY : h ≤ Y ^ θ) (hε : ε = 1 ∨ ε = -1)
    (hI : ∀ x ∈ Icc Y (Y ^ (1 + δ)),
      ∫ t in Y..x, max (ε * (liouvilleSum (t + h) - liouvilleSum t) / h) 0 ≤ C * x ^ θ) :
    ∃ Z ≥ Y, ∃ ε' : ℝ, (ε' = 1 ∨ ε' = -1) ∧
      ∀ x ∈ Icc Z (Z ^ (1 + δ / (2 + δ))), ε' * liouvilleSum x ≤ (|C| + 2) * x ^ θ := by
  set M := Y ^ (1 + δ / 2)
  have hY0 : 0 < Y := by linarith
  have hMd : M ^ (1 + δ / (2 + δ)) = Y ^ (1 + δ) := by
    rw [← Real.rpow_mul hY0.le]
    congr 1
    field_simp
    ring
  have hYd : Y ^ (1 + δ / (2 + δ)) ≤ M := by
    refine Real.rpow_le_rpow_of_exponent_le hY.le ?_
    have : δ / (2 + δ) ≤ δ / 2 := div_le_div_of_nonneg_left hδ.le two_pos (by linarith)
    linarith
  have hε1 : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hpt {x : ℝ} (hx : Y ≤ x) : |ε * smoothSum h x - ε * liouvilleSum x| ≤ h + 1 := by
    rw [← mul_sub, abs_mul, hε1, one_mul]
    exact abs_smoothSum_sub_le hh (by linarith)
  have hxθ {x : ℝ} (hx : Y ≤ x) : h + 1 ≤ 2 * x ^ θ := by
    have h1 := Real.rpow_le_rpow hY0.le hx hθ
    have h2 := Real.one_le_rpow (hY.le.trans hx) hθ
    linarith
  have hC {x : ℝ} (hx : Y ≤ x) : C * x ^ θ ≤ |C| * x ^ θ ∧ 0 ≤ |C| * x ^ θ := by
    have := Real.rpow_nonneg (hY0.le.trans hx) θ
    exact ⟨mul_le_mul_of_nonneg_right (le_abs_self C) this, mul_nonneg (abs_nonneg C) this⟩
  by_cases hm : ∃ m ∈ Icc Y M, ε * smoothSum h m ≤ 0
  · obtain ⟨m, hm, hm0⟩ := hm
    refine ⟨m, hm.1, ε, hε, fun x hx => ?_⟩
    have hYx := hm.1.trans hx.1
    have hxt : x ≤ Y ^ (1 + δ) :=
      hx.2.trans (hMd ▸ Real.rpow_le_rpow (by linarith [hm.1]) hm.2 (by positivity))
    have h1 := mul_smoothSum_sub_le (ε := ε) (h := h) hm.1 hx.1 le_rfl
    have h2 := hI x ⟨hYx, hxt⟩
    have h3 := (abs_le.1 (hpt hYx)).1
    linarith [hxθ hYx, hC hYx]
  · push Not at hm
    refine ⟨Y, le_rfl, -ε, by rcases hε with rfl | rfl <;> norm_num, fun x hx => ?_⟩
    have h0 := hm x ⟨hx.1, hx.2.trans hYd⟩
    have h3 := (abs_le.1 (hpt hx.1)).2
    linarith [hxθ hx.1, hC hx.1]

/-- `MeanBound θ δ C` with `θ ≥ 1 / 2` rules out zeros of zeta to the right of `θ`, through
`WindowBound θ (δ / (2 + δ)) (|C| + 2)`. The converse is not asserted, and the hypothesis is not
expected for `θ` below about `2 / 3`. -/
theorem riemannZeta_ne_zero_of_meanBound {θ δ C : ℝ} (hθ : 1 / 2 ≤ θ) (hδ : 0 < δ)
    (hI : MeanBound θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 :=
  riemannZeta_ne_zero_of_windowBound (C := |C| + 2) hθ (by positivity : 0 < δ / (2 + δ))
    (fun X => by
      obtain ⟨Y, hY, h, hh, hhY, ε, hε, hw⟩ := hI (max X 2)
      obtain ⟨Z, hZ, hw'⟩ := window_of_mean (by linarith) hδ
        (by linarith [le_max_right X 2] : 1 < Y) hh hhY hε hw
      exact ⟨Z, (le_max_left X 2).trans (hY.trans hZ), hw'⟩) hρ

/-- `MeanBound` with the integral taken over each block `[y, 2 y]` starting in the window, rather
than cumulatively from `Y`. -/
def BlockMeanBound (θ δ C : ℝ) : Prop :=
  ∀ X, ∃ Y ≥ X, ∃ h : ℝ, 0 < h ∧ h ≤ Y ^ θ ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      ∫ t in y..2 * y, max (ε * (liouvilleSum (t + h) - liouvilleSum t) / h) 0 ≤ C * y ^ θ

/-- The block form gives the cumulative one: the blocks `[2 ^ j Y, 2 ^ (j + 1) Y]` covering `[Y, x]`
contribute a geometric series dominated by its last term. -/
theorem BlockMeanBound.meanBound {θ δ C : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hB : BlockMeanBound θ δ C) : MeanBound θ δ (C * 2 ^ θ / (2 ^ θ - 1)) := by
  intro X
  obtain ⟨Y, hY, h, hh, hhY, ε, hε, hb⟩ := hB (max X 1)
  have hY1 : 1 ≤ Y := (le_max_right X 1).trans hY
  refine ⟨Y, (le_max_left X 1).trans hY, h, hh, hhY, ε, hε, fun x hx => ?_⟩
  set K := C * 2 ^ θ / (2 ^ θ - 1)
  have h2 : 1 < (2 : ℝ) ^ θ := Real.one_lt_rpow one_lt_two hθ
  have hKe : K * (2 ^ θ - 1) = C * 2 ^ θ := div_mul_cancel₀ _ (by linarith)
  have hK : C ≤ K := by nlinarith
  have hg (a b : ℝ) : IntervalIntegrable
      (fun t => max (ε * (liouvilleSum (t + h) - liouvilleSum t) / h) 0) volume a b :=
    ⟨(intervalIntegrable_increment ε h a b).1.pos_part,
      (intervalIntegrable_increment ε h a b).2.pos_part⟩
  have hblock (n : ℕ) : 2 ^ n * Y ≤ Y ^ (1 + δ) → ∫ t in Y..2 * (2 ^ n * Y),
      max (ε * (liouvilleSum (t + h) - liouvilleSum t) / h) 0 ≤ K * (2 ^ n * Y) ^ θ := by
    induction n with
    | zero =>
      intro hn
      rw [pow_zero, one_mul] at hn ⊢
      exact (hb Y ⟨le_rfl, hn⟩).trans (by gcongr)
    | succ n ih =>
      rw [show (2 : ℝ) ^ (n + 1) * Y = 2 * (2 ^ n * Y) by ring]
      intro hn
      have hz : Y ≤ 2 ^ n * Y := le_mul_of_one_le_left (by linarith) (one_le_pow₀ one_le_two)
      have hz2 : (2 * (2 ^ n * Y)) ^ θ = 2 ^ θ * (2 ^ n * Y) ^ θ :=
        Real.mul_rpow zero_le_two (by positivity)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hg _ _) (hg _ _), hz2]
      have h1 := ih (by linarith)
      have h3 := hb _ ⟨by linarith, hn⟩
      rw [hz2] at h3
      linear_combination h1 + h3 - (2 ^ n * Y) ^ θ * hKe
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ((one_le_div (by linarith)).2 hx.1) one_lt_two
  rw [le_div_iff₀ (by linarith)] at hn1
  rw [div_lt_iff₀ (by linarith), pow_succ, mul_comm _ (2 : ℝ), mul_assoc] at hn2
  refine (intervalIntegral.integral_mono_interval le_rfl hx.1 hn2.le
    (.of_forall fun _ => le_max_right _ _) (hg _ _)).trans
    ((hblock n (hn1.trans hx.2)).trans ?_)
  gcongr

end Masullo.Liouville
