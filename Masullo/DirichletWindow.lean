import Masullo.Dyadic

/-!
# The window criterion for a Dirichlet numerator

Let `b : ℕ → ℝ` with `|b n| ≤ 1` and `partialSum b x = ∑_{n ≤ x} b n`, and suppose
`∑ b n n ^ (-s) = K s / ζ s` for `Re s > 1`, with `K` analytic at each point of `Re s > θ` and
nonzero at the zeros of zeta there, `0 ≤ θ`. `WindowBound (partialSum b) θ δ C` says that for
arbitrarily large `Y` there is a sign `ε = ±1` with `ε partialSum b x ≤ C x ^ θ` for all
`x ∈ [Y, Y ^ (1 + δ)]`. It rules out zeros of zeta in `Re s > θ`
(`riemannZeta_ne_zero_of_windowBound`). The Laplace transform of `partialSum b (e ^ u)` is
`K s / (s ζ s)`, whose poles in `Re s > θ` are the zeros of zeta of their full multiplicity, so the
argument is `Masullo.Landau.ContinuesMero.eq_empty_of_window`.

The statement is a case of Kaczorowski and Pintz, *Oscillatory properties of arithmetical
functions. I*, Acta Math. Hungar. 48 (1986), Theorem 1 and Corollary 4.

Both conditions on `K` are load-bearing. For `b = 1`, with `K = ζ ^ 2`, the window bound holds at
`θ = 0`, `C = 0`, `ε = -1`, since `-partialSum b x ≤ 0`; the transform `ζ s / s` has a pole at
`s = 1`, which holomorphy of `K` at `1` excludes (this `K` also vanishes at the zeros). For
`b = 0`, with `K = 0`, every window bound holds and only nonvanishing at the zeros fails. Neither
is a Lean negative test, since that would need a proved zero of zeta in the strip.

For `θ ≥ 1 - 1 / m` the bound at the perfect `m`-th powers of each window gives it at every point
of the window with a larger constant (`PowerWindowBound.windowBound`), since `|b n| ≤ 1` bounds
the increments between consecutive powers.

The Möbius case `K = 1` is `riemannZeta_ne_zero_of_mertensWindow`. Its hypothesis holds at `θ = 1`
with `C = 1`, since `|partialSum b x| ≤ x` (`Masullo/DirichletWindowControls.lean`); it is not
proved here for any `θ < 1`.
-/

open MeasureTheory Complex Set Filter Topology Metric
open scoped ArithmeticFunction.Moebius

namespace Masullo.DirichletWindow

open Landau Window Spectrum WeilExplicit

/-- `∑_{n ≤ x} b n`. -/
noncomputable def partialSum (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n

variable {b : ℕ → ℝ} {K : ℂ → ℂ}

lemma measurable_partialSum : Measurable (partialSum b) :=
  (measurable_from_nat (f := fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, b n)).comp Nat.measurable_floor

lemma abs_partialSum_le (hb : ∀ n, |b n| ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    |partialSum b x| ≤ x := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun n _ => hb n).trans ?_
  simpa using Nat.floor_le hx

lemma cpow_ofReal_exp (u : ℝ) (w : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ w = cexp (u * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'), ← ofReal_log
    (Real.exp_pos u).le, Real.log_exp]

/-- With partial sums of `|b n|` of order `n ^ r`, the Laplace transform of `partialSum b (e ^ u)`
is `L(b, s) / s` for `Re s > r`. -/
lemma integral_partialSum_of_isBigO {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n => ∑ k ∈ Finset.Icc 1 n, ‖(b k : ℂ)‖) =O[atTop] fun n => (n : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) :
    ∫ u in Ioi (0 : ℝ), (partialSum b (Real.exp u) : ℂ) * cexp (-(s * u)) =
      LSeries (fun n => (b n : ℂ)) s / s := by
  have h := LSeries_eq_mul_integral' (fun n => (b n : ℂ)) hr hs hO
  have e := integral_comp_exp_Ioi
    (fun y : ℝ => (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (b k : ℂ)) * (y : ℂ) ^ (-(s + 1))) 0
  rw [Real.exp_zero] at e
  rw [← e] at h
  rw [h, mul_div_cancel_left₀ _ (ne_zero_of_re_pos (hr.trans_lt hs))]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [real_smul, cpow_ofReal_exp, partialSum, ofReal_exp]
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  ring_nf

/-- The Laplace transform of `partialSum b (e ^ u)` is `K s / (s ζ s)` for `Re s > 1`. -/
lemma integral_partialSum (hb : ∀ n, |b n| ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s = K s / riemannZeta s)
    {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (partialSum b (Real.exp u) : ℂ) * cexp (-(s * u)) =
      K s / riemannZeta s / s := by
  rw [integral_partialSum_of_isBigO zero_le_one ?_ (by simpa using hs), hL s hs]
  refine Asymptotics.IsBigO.of_bound 1 (.of_forall fun n => ?_)
  rw [Real.rpow_one, one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_natCast]
  calc _ ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => by simpa [Real.norm_eq_abs] using hb k
    _ = n := by simp

/-! ### The continuation -/

/-- The continuation of the Laplace transform of `-ε partialSum b (e ^ u)`. -/
noncomputable def continuation (K : ℂ → ℂ) (ε : ℝ) (s : ℂ) : ℂ :=
  -(ε * (K s * (s - 1) / (s * zetaNum s)))

lemma continuation_eq {ε : ℝ} {s : ℂ} (hs : 1 < s.re) :
    continuation K ε s = -(ε * (K s / riemannZeta s / s)) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 fun e => by simp [e] at hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  have h0 := ne_zero_of_one_lt_re hs
  rw [continuation, zetaNum_of_ne (sub_ne_zero.1 hs1)]
  field_simp

lemma continues {θ ε : ℝ} (hθ : 0 ≤ θ) (hε : ε ≠ 0) (hb : ∀ n, |b n| ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s = K s / riemannZeta s)
    (hK : ∀ s : ℂ, θ < s.re → AnalyticAt ℂ K s)
    (hne : ∀ s : ℂ, θ < s.re → riemannZeta s = 0 → K s ≠ 0) :
    ContinuesMero (fun u => -(ε * partialSum b (Real.exp u))) (continuation K ε)
      {ρ | θ < ρ.re ∧ riemannZeta ρ = 0} |ε| 1 θ where
  measurable := by
    have := (measurable_partialSum (b := b)).comp Real.measurable_exp
    unfold Function.comp at this
    fun_prop
  growth u hu := by
    rw [abs_neg, abs_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (abs_partialSum_le hb (Real.exp_pos u).le) (abs_nonneg ε)
  laplace s hs := by
    rw [continuation_eq hs, ← integral_partialSum hb hL hs, ← integral_const_mul, ← integral_neg]
    congr 1 with u
    push_cast
    ring
  analytic s hs hZ := by
    have h0 : s ≠ 0 := fun e => by simp [e] at hs; linarith
    exact (analyticAt_const.mul (((hK s hs).mul
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) s)).div
      (analyticAt_id.mul (differentiable_zetaNum.analyticAt s))
      (mul_ne_zero h0 (zetaNum_ne_zero (fun h => hZ ⟨hs, h⟩))))).fun_neg
  finite s r := ((isCompact_closedBall s r).inter_riemannZetaZeros_finite).subset
    fun ρ h => ⟨h.2, h.1.2⟩
  re_mem ρ h := ⟨h.1, (re_lt_one_of_zero h.2).le⟩
  pole ρ h := by
    have h0 : ρ ≠ 0 := fun e => by have := h.1; simp [e] at this; linarith
    have h1 : ρ ≠ 1 := fun e => riemannZeta_one_ne_zero (e ▸ h.2)
    have hz2 := hne ρ h.1 h.2
    obtain ⟨g, hg, hg0, hfac⟩ := (differentiable_zetaNum.analyticAt ρ).analyticOrderAt_eq_natCast.1
      (analyticOrderAt_zetaNum ρ)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (zeroMult_pos h.2).ne'
    refine ⟨n, fun s => -(ε * (K s * (s - 1) / (s * g s))),
      (analyticAt_const.mul (((hK ρ h.1).mul
        (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ)).div (analyticAt_id.mul hg)
          (mul_ne_zero h0 hg0))).fun_neg, neg_ne_zero.2 (mul_ne_zero (ofReal_ne_zero.2 hε)
        (div_ne_zero (mul_ne_zero hz2 (sub_ne_zero.2 h1)) (mul_ne_zero h0 hg0))), ?_⟩
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
      (eventually_ne_nhds h0).filter_mono nhdsWithin_le_nhds,
      (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds] with s hs hne hs0 hgs
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 hne
    rw [continuation, hs, hn, smul_eq_mul]
    field_simp

/-! ### The window criterion -/

/-- For arbitrarily large `Y` there is a sign `ε = ±1`, which may depend on `Y`, with
`ε S x ≤ C x ^ θ` for all `x ∈ [Y, Y ^ (1 + δ)]`. -/
def WindowBound (S : ℝ → ℝ) (θ δ C : ℝ) : Prop :=
  ∀ X, ∃ Y ≥ X, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ x ∈ Icc Y (Y ^ (1 + δ)), ε * S x ≤ C * x ^ θ

/-- A window bound on `S` rules out zeros of zeta to the right of `θ` once, for each sign `ε`,
some `H ε` continues the Laplace transform of `-ε S (e ^ u)` with poles exactly at those zeros. -/
lemma riemannZeta_ne_zero_of_continues {S : ℝ → ℝ} {H : ℝ → ℂ → ℂ} {A : ℝ → ℝ} {θ δ C c : ℝ}
    (hθ : 0 ≤ θ) (hδ : 0 < δ) (hc : ∀ ε : ℝ, ε ≠ 0 → ContinuesMero
      (fun u => -(ε * S (Real.exp u))) (H ε) {ρ | θ < ρ.re ∧ riemannZeta ρ = 0} (A ε) c θ)
    (h : WindowBound S θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  obtain ⟨ε, hε, hw⟩ := cofinal_sign h
  replace hε : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hZ := (hc ε hε).eq_empty_of_window_ge hθ ?_ hδ (window_exp (F := fun x => ε * S x) hw)
  · exact fun h0 => (hZ ▸ ⟨hρ, h0⟩ : ρ ∈ (∅ : Set ℂ)).elim
  · rintro ρ ⟨hr, hz⟩ hi
    lift ρ to ℝ using hi
    exact (riemannZeta_ofReal_ne_zero (by simp at hr; linarith)
      (by simpa using re_lt_one_of_zero hz) hz).elim

/-- A window bound on the partial sums of `b`, whose Dirichlet series is `K / ζ` with `K`
analytic and nonzero at the zeros of zeta in `Re s > θ`, rules out zeros of zeta to the right of
`θ`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_windowBound {θ δ C : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hb : ∀ n, |b n| ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s = K s / riemannZeta s)
    (hK : ∀ s : ℂ, θ < s.re → AnalyticAt ℂ K s)
    (hne : ∀ s : ℂ, θ < s.re → riemannZeta s = 0 → K s ≠ 0)
    (h : WindowBound (partialSum b) θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 :=
  riemannZeta_ne_zero_of_continues hθ hδ (fun _ hε => continues hθ hε hb hL hK hne) h hρ

lemma abs_moebius_le (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- A window bound on the Mertens function `∑_{n ≤ x} μ(n)` with `θ ≥ 0` rules out zeros of zeta
to the right of `θ`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_mertensWindow {θ δ C : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (h : WindowBound (partialSum fun n => (μ n : ℝ)) θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  refine riemannZeta_ne_zero_of_windowBound (K := fun _ => 1) hθ hδ abs_moebius_le
    (fun s hs => ?_) (fun _ _ => analyticAt_const) (fun _ _ _ => one_ne_zero) h hρ
  have hmul := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs, mul_comm] at hmul
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_le_re hs.le)).2 (by simpa using hmul)

/-! ### Sampling at perfect powers

Between consecutive `m`-th powers `j ^ m ≤ x < (j + 1) ^ m` the partial sum moves by at most
`(j + 1) ^ m - j ^ m ≤ m (j + 1) ^ (m - 1)`, which is `O(x ^ θ)` for `θ ≥ 1 - 1 / m`. -/

lemma abs_partialSum_sub_le (hb : ∀ n, |b n| ≤ 1) {u v : ℕ} (h : u ≤ v) :
    |partialSum b v - partialSum b u| ≤ v - u := by
  have hI (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
  simp only [partialSum, Nat.floor_natCast, hI]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le u) h, add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ => hb n).trans ?_)
  simp [Nat.cast_sub h]

lemma nonneg_of_one_sub_inv_le {m : ℕ} {θ : ℝ} (hm : 1 ≤ m) (hθ : 1 - 1 / m ≤ θ) : 0 ≤ θ := by
  have := (div_le_one (by positivity)).2 (by exact_mod_cast hm : (1 : ℝ) ≤ m)
  linarith

lemma pow_sub_one_le_rpow {m : ℕ} {θ j x : ℝ} (hm : 1 ≤ m) (hθ : 1 - 1 / m ≤ θ) (hj : 1 ≤ j)
    (hx : j ^ m ≤ x) : j ^ (m - 1) ≤ x ^ θ := by
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc j ^ (m - 1) = (j ^ m) ^ (1 - 1 / (m : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
          Nat.cast_sub hm]
        congr 1
        field_simp
        ring
    _ ≤ (j ^ m) ^ θ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hj) hθ
    _ ≤ x ^ θ := Real.rpow_le_rpow (by positivity) hx (nonneg_of_one_sub_inv_le hm hθ)

/-- For arbitrarily large `Y` there is a sign `ε = ±1`, which may depend on `Y`, with
`ε S (j ^ m) ≤ C (j ^ m) ^ θ` at every perfect `m`-th power `j ^ m ∈ [Y, Y ^ (1 + δ)]`. -/
def PowerWindowBound (S : ℝ → ℝ) (m : ℕ) (θ δ C : ℝ) : Prop :=
  ∀ X, ∃ Y ≥ X, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ j : ℕ, (j : ℝ) ^ m ∈ Icc Y (Y ^ (1 + δ)) → ε * S ((j : ℝ) ^ m) ≤ C * ((j : ℝ) ^ m) ^ θ

/-- For `|b n| ≤ 1` and `θ ≥ 1 - 1 / m`, a window bound at the perfect `m`-th powers is a window
bound at every point of the same windows. Each `x` lies within `(j + 1) ^ m - j ^ m` of a power
`j ^ m ≤ x` or `(j + 1) ^ m > x` in its window, and the late windows contain both. -/
theorem PowerWindowBound.windowBound {m : ℕ} {θ δ C : ℝ} (hm : 1 ≤ m) (hθ : 1 - 1 / m ≤ θ)
    (hδ : 0 < δ) (hb : ∀ n, |b n| ≤ 1) (h : PowerWindowBound (partialSum b) m θ δ C) :
    WindowBound (partialSum b) θ δ ((max C 0 + m) * (2 ^ m) ^ θ) := by
  intro X
  obtain ⟨Y, hY, ε, hε, hw⟩ := h (max X (max 1 (((2 : ℝ) ^ m) ^ (1 / δ))))
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYδ : 2 ^ m * Y ≤ Y ^ (1 + δ) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc (2 : ℝ) ^ m = (((2 : ℝ) ^ m) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ Y ^ δ := Real.rpow_le_rpow (by positivity)
          ((le_max_right _ _).trans ((le_max_right _ _).trans hY)) hδ.le
  refine ⟨Y, (le_max_left _ _).trans hY, ε, hε, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := hY1.trans hx.1
  have hm0 : m ≠ 0 := by omega
  set N := ⌊x⌋₊
  set j := Nat.nthRoot m N
  have hjN : j ^ m ≤ N := Nat.pow_nthRoot_le_iff.2 (.inl hm0)
  have hNj : N < (j + 1) ^ m := Nat.lt_pow_nthRoot_add_one hm0 N
  have hj1 : 1 ≤ j := (Nat.le_nthRoot_iff hm0).2 (by rw [one_pow]; exact Nat.le_floor (by simpa))
  have hjx : (j : ℝ) ^ m ≤ x := (by exact_mod_cast hjN : (j : ℝ) ^ m ≤ N).trans (Nat.floor_le
    (by linarith))
  have hxj : x < ((j + 1 : ℕ) : ℝ) ^ m := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hNj)
  have hj2' : ((j + 1 : ℕ) : ℝ) ^ m ≤ 2 ^ m * (j : ℝ) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by push_cast; linarith [(by exact_mod_cast hj1 : (1 : ℝ) ≤ j)]) m
  have hj2 : ((j + 1 : ℕ) : ℝ) ^ m ≤ 2 ^ m * x := hj2'.trans (by gcongr)
  have hinc : ((j + 1 : ℕ) : ℝ) ^ m - (j : ℝ) ^ m ≤ m * (2 ^ m * x) ^ θ := by
    have h1 := abs_pow_sub_pow_le ((j : ℝ) + 1) j m
    rw [add_sub_cancel_left, abs_one, one_mul, Nat.abs_cast,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1), max_eq_left (by linarith)] at h1
    push_cast
    refine (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    exact pow_sub_one_le_rpow hm hθ (by linarith [(by exact_mod_cast hj1 : (1 : ℝ) ≤ j)])
      (by simpa using hj2)
  obtain ⟨J, hJw, hJ, hJx⟩ : ∃ J : ℕ, (J : ℝ) ^ m ∈ Icc Y (Y ^ (1 + δ)) ∧
      |partialSum b N - partialSum b ((J : ℝ) ^ m)| ≤ ((j + 1 : ℕ) : ℝ) ^ m - (j : ℝ) ^ m ∧
      (J : ℝ) ^ m ≤ 2 ^ m * x := by
    by_cases hYj : Y ≤ (j : ℝ) ^ m
    · refine ⟨j, ⟨hYj, hjx.trans hx.2⟩, ?_, by nlinarith [pow_pos (two_pos (α := ℝ)) m]⟩
      have := abs_partialSum_sub_le hb hjN
      push_cast at this ⊢
      linarith [(by exact_mod_cast hNj.le : (N : ℝ) ≤ ((j : ℝ) + 1) ^ m)]
    · refine ⟨j + 1, ⟨by linarith [hx.1], ?_⟩, ?_, hj2⟩
      · exact hj2'.trans ((mul_le_mul_of_nonneg_left (not_le.1 hYj).le (by positivity)).trans hYδ)
      · have := abs_partialSum_sub_le hb hNj.le
        rw [abs_sub_comm] at this
        push_cast at this ⊢
        linarith [(by exact_mod_cast hjN : (j : ℝ) ^ m ≤ N)]
  have hS : partialSum b x = partialSum b N := by simp [partialSum, N]
  have hε1 : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hd : ε * (partialSum b N - partialSum b ((J : ℝ) ^ m)) ≤ m * (2 ^ m * x) ^ θ :=
    (le_abs_self _).trans (by rw [abs_mul, hε1, one_mul]; exact hJ.trans hinc)
  have hC : C * ((J : ℝ) ^ m) ^ θ ≤ max C 0 * (2 ^ m * x) ^ θ :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hJx
        (nonneg_of_one_sub_inv_le hm hθ)) (le_max_right C 0))
  rw [hS, mul_assoc, ← Real.mul_rpow (by positivity) (by linarith)]
  linarith [hw J hJw]

/-- A window bound at the perfect `m`-th powers on the partial sums of `b`, with `θ ≥ 1 - 1 / m`
and the hypotheses of `riemannZeta_ne_zero_of_windowBound`, rules out zeros of zeta to the right
of `θ`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_powerWindowBound {m : ℕ} {θ δ C : ℝ} (hm : 1 ≤ m)
    (hθ : 1 - 1 / m ≤ θ) (hδ : 0 < δ) (hb : ∀ n, |b n| ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s = K s / riemannZeta s)
    (hK : ∀ s : ℂ, θ < s.re → AnalyticAt ℂ K s)
    (hne : ∀ s : ℂ, θ < s.re → riemannZeta s = 0 → K s ≠ 0)
    (h : PowerWindowBound (partialSum b) m θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 :=
  riemannZeta_ne_zero_of_windowBound (nonneg_of_one_sub_inv_le hm hθ) hδ hb hL hK hne
    (h.windowBound hm hθ hδ hb) hρ

/-- A window bound on the Mertens function at the perfect `m`-th powers, with `θ ≥ 1 - 1 / m`,
rules out zeros of zeta to the right of `θ`. For squares at `θ = 1 / 2` it is the Riemann
hypothesis. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_mertensPowerWindow {m : ℕ} {θ δ C : ℝ} (hm : 1 ≤ m)
    (hθ : 1 - 1 / m ≤ θ) (hδ : 0 < δ)
    (h : PowerWindowBound (partialSum fun n => (μ n : ℝ)) m θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 :=
  riemannZeta_ne_zero_of_mertensWindow (nonneg_of_one_sub_inv_le hm hθ) hδ
    (h.windowBound hm hθ hδ abs_moebius_le) hρ

end Masullo.DirichletWindow
