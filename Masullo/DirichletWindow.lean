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

/-- The Laplace transform of `partialSum b (e ^ u)` is `K s / (s ζ s)` for `Re s > 1`. -/
lemma integral_partialSum (hb : ∀ n, |b n| ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s = K s / riemannZeta s)
    {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (partialSum b (Real.exp u) : ℂ) * cexp (-(s * u)) =
      K s / riemannZeta s / s := by
  have hO : (fun n => ∑ k ∈ Finset.Icc 1 n, ‖(b k : ℂ)‖) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (.of_forall fun n => ?_)
    rw [Real.rpow_one, one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
      Real.norm_natCast]
    calc _ ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by simpa [Real.norm_eq_abs] using hb k
      _ = n := by simp
  have h := LSeries_eq_mul_integral' (fun n => (b n : ℂ)) zero_le_one (by simpa) hO
  have e := integral_comp_exp_Ioi
    (fun y : ℝ => (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (b k : ℂ)) * (y : ℂ) ^ (-(s + 1))) 0
  rw [Real.exp_zero] at e
  rw [← e, hL s hs] at h
  rw [h, mul_div_cancel_left₀ _ (ne_zero_of_one_lt_re hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [real_smul, cpow_ofReal_exp, partialSum, ofReal_exp]
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  ring_nf

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

/-- A window bound on the partial sums of `b`, whose Dirichlet series is `K / ζ` with `K`
analytic and nonzero at the zeros of zeta in `Re s > θ`, rules out zeros of zeta to the right of
`θ`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_windowBound {θ δ C : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hb : ∀ n, |b n| ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s = K s / riemannZeta s)
    (hK : ∀ s : ℂ, θ < s.re → AnalyticAt ℂ K s)
    (hne : ∀ s : ℂ, θ < s.re → riemannZeta s = 0 → K s ≠ 0)
    (h : WindowBound (partialSum b) θ δ C) {ρ : ℂ} (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  -- one sign occurs for arbitrarily large `Y`
  obtain ⟨ε, hε, hw⟩ : ∃ ε : ℝ, ε ≠ 0 ∧ ∀ X, ∃ Y ≥ X,
      ∀ x ∈ Icc Y (Y ^ (1 + δ)), ε * partialSum b x ≤ C * x ^ θ := by
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
  have hZ := (continues hθ hε hb hL hK hne).eq_empty_of_window_ge (by linarith) ?_ hδ
    (window_exp (F := fun x => ε * partialSum b x) hw)
  · exact fun h0 => (hZ ▸ ⟨hρ, h0⟩ : ρ ∈ (∅ : Set ℂ)).elim
  · rintro ρ ⟨hr, hz⟩ hi
    lift ρ to ℝ using hi
    exact (riemannZeta_ofReal_ne_zero (by simp at hr; linarith)
      (by simpa using re_lt_one_of_zero hz) hz).elim

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

end Masullo.DirichletWindow
