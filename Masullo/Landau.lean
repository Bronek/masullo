import Mathlib

/-!
# Landau's theorem on windows

Let `f` be real with at most exponential growth and `θ ≥ 0`. Let its Laplace transform continue
meromorphically to `Re s > θ` with simple poles, finitely many in each disc of the plane, and let
every real pole there have a residue with negative real part. If, for a fixed `δ > 0`, `f ≥ 0` on
windows `[U, (1 + δ) U]` with `U` arbitrarily large, then there are no poles in `Re s > θ`. This is
a one-way implication; it asserts nothing about the sign of `f` outside the windows.

The Taylor coefficients of the transform at `σ + i t` are integrals of `f` against the kernels
`u ^ k e ^ (-σ u) / k!`, which concentrate at `u = k / σ`. When `k / σ` is inside a window, the
coefficient at `σ` bounds those at every `σ + i t`, up to an error below the scale set by the poles.

See `CREDITS.md` for the sources of the idea.
-/

open MeasureTheory Complex Set Filter Topology Metric

namespace Masullo.Landau

/-! ### Laplace transform and Taylor coefficients -/

lemma integral_gamma_kernel {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), u ^ k / k.factorial * Real.exp (-(b * u)) = 1 / b ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := k + 1) (by positivity) hb
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  simp_rw [div_mul_eq_mul_div, integral_div, h]
  rw [div_eq_iff (by positivity), ← Nat.cast_succ, Real.rpow_natCast, one_div_pow]

lemma integrable_gamma_kernel {b : ℝ} (hb : 0 < b) (k : ℕ) : IntegrableOn
    (fun u : ℝ => u ^ k / k.factorial * Real.exp (-(b * u))) (Ioi 0) := by
  refine not_imp_comm.1 integral_undef ?_
  rw [integral_gamma_kernel hb]
  positivity

/-- The `k`-th coefficient in `w` at `0` of the Laplace transform of `f` at `s - w`. -/
noncomputable def coeff (f : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((u ^ k / k.factorial * f u : ℝ) : ℂ) * cexp (-(s * u))

variable {f : ℝ → ℝ} {A c : ℝ}

lemma norm_kernel {u : ℝ} (hu : 0 < u) (k : ℕ) (s : ℂ) :
    ‖((u ^ k / k.factorial * f u : ℝ) : ℂ) * cexp (-(s * u))‖ =
      u ^ k / k.factorial * |f u| * Real.exp (-(s.re * u)) := by
  rw [norm_mul, norm_real, norm_exp, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  simp

lemma norm_kernel_le (hA : ∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u)) {u : ℝ} (hu : 0 < u)
    (k : ℕ) (s : ℂ) : ‖((u ^ k / k.factorial * f u : ℝ) : ℂ) * cexp (-(s * u))‖ ≤
      A * (u ^ k / k.factorial * Real.exp (-((s.re - c) * u))) := by
  rw [norm_kernel hu]
  calc _ ≤ u ^ k / k.factorial * (A * Real.exp (c * u)) * Real.exp (-(s.re * u)) := by
        gcongr; exact hA u hu.le
    _ = _ := by rw [show -((s.re - c) * u) = c * u + -(s.re * u) by ring, Real.exp_add]; ring

lemma integrable_kernel (hf : Measurable f) (hA : ∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u))
    (k : ℕ) {s : ℂ} (hs : c < s.re) : IntegrableOn
      (fun u : ℝ => ((u ^ k / k.factorial * f u : ℝ) : ℂ) * cexp (-(s * u))) (Ioi 0) :=
  ((integrable_gamma_kernel (sub_pos.2 hs) k).const_mul A).mono' (by fun_prop)
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ hu => norm_kernel_le hA hu k s)

lemma hasSum_coeff (hf : Measurable f) (hA : ∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u))
    {s w : ℂ} (hw : ‖w‖ < s.re - c) : HasSum (fun k => coeff f k s * w ^ k)
      (∫ u in Ioi (0 : ℝ), (f u : ℂ) * cexp (-((s - w) * u))) := by
  have hb : 0 < s.re - c := (norm_nonneg w).trans_lt hw
  have hs : c < s.re := sub_pos.1 hb
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (k : ℕ) (u : ℝ) => ((u ^ k / k.factorial * f u : ℝ) : ℂ) * cexp (-(s * u)) * w ^ k)
    (fun k => (integrable_kernel hf hA k hs).mul_const _) ?_
  · have pt (u : ℝ) : ∑' k : ℕ, ((u ^ k / k.factorial * f u : ℝ) : ℂ) * cexp (-(s * u)) * w ^ k =
        f u * cexp (-((s - w) * u)) := by
      have e := (NormedSpace.expSeries_div_hasSum_exp (w * u)).mul_left
        ((f u : ℂ) * cexp (-(s * u)))
      rw [← exp_eq_exp_ℂ, mul_assoc, ← Complex.exp_add,
        show -(s * u) + w * u = -((s - w) * u) by ring] at e
      refine (e.congr_fun fun k => ?_).tsum_eq
      push_cast
      ring
    simp only [integral_mul_const, pt] at h
    exact h
  · refine .of_nonneg_of_le (fun k => integral_nonneg fun u => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one (by positivity) ((div_lt_one hb).2 hw)).mul_left
        (A / (s.re - c)))
    simp_rw [norm_mul _ (w ^ k), integral_mul_const]
    calc _ ≤ (∫ u in Ioi (0 : ℝ), A * (u ^ k / k.factorial * Real.exp (-((s.re - c) * u)))) *
          ‖w ^ k‖ := by
          refine mul_le_mul_of_nonneg_right (setIntegral_mono_on (integrable_kernel hf hA k hs).norm
            ((integrable_gamma_kernel hb k).const_mul A) measurableSet_Ioi
            fun u hu => norm_kernel_le hA hu k s) (norm_nonneg _)
      _ = _ := by
          rw [integral_const_mul, integral_gamma_kernel hb, norm_pow, div_pow, pow_succ]
          field_simp

/-- Cauchy's estimate for a series that represents a function near the centre of a disc. -/
lemma exists_coeff_le {D : ℕ → ℂ} {h : ℂ → ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hd : DifferentiableOn ℂ h (ball 0 R)) (hs : ∀ᶠ w in 𝓝 0, HasSum (fun k => D k * w ^ k) (h w)) :
    ∃ M, ∀ k, ‖D k‖ * r ^ k ≤ M := by
  obtain ⟨r', h1, h2⟩ := exists_between hrR
  lift r to NNReal using hr.le
  lift r' to NNReal using r.2.trans h1.le
  have p1 := (hd.mono (closedBall_subset_ball h2)).hasFPowerSeriesOnBall (R := r')
    (hr.trans h1)
  have p2 : HasFPowerSeriesAt h (FormalMultilinearSeries.ofScalars ℂ D) 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [hs] with w hw
    simpa [FormalMultilinearSeries.coeff_ofScalars, mul_comm] using hw
  have e := p1.hasFPowerSeriesAt.eq_formalMultilinearSeries p2
  obtain ⟨M, -, hM⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius
    (FormalMultilinearSeries.ofScalars ℂ D) (r := r)
    ((ENNReal.coe_lt_coe.2 h1).trans_le (e ▸ p1.r_le))
  refine ⟨M, fun k => ?_⟩
  simpa [FormalMultilinearSeries.norm_apply_eq_norm_coef] using hM k

/-- Off the window `[U, V]` the sign of `f` costs at most two exponentially small terms. -/
lemma norm_coeff_le (hf : Measurable f) (hA : ∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u))
    {σ l U V : ℝ} (hl : 0 ≤ l) (hlσ : 0 < σ - c - l) (hw : ∀ u ∈ Icc U V, 0 ≤ f u) (k : ℕ) (t : ℝ) :
    ‖coeff f k (σ + t * I)‖ ≤ (coeff f k σ).re +
      2 * A * (Real.exp (-(l * V)) / (σ - c - l) ^ (k + 1) +
        Real.exp (l * U) / (σ - c + l) ^ (k + 1)) := by
  have hA0 : 0 ≤ A := by simpa using (abs_nonneg _).trans (hA 0 le_rfl)
  have hl' : 0 < σ - c + l := by linarith
  have hσ : c < σ := by linarith
  have pt (u : ℝ) (hu : 0 ≤ u) : |f u| ≤ f u + 2 * A * Real.exp (c * u) *
      (Real.exp (-(l * V)) * Real.exp (l * u) + Real.exp (l * U) * Real.exp (-(l * u))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    by_cases h : 0 ≤ f u
    · rw [abs_of_nonneg h]
      have : 0 ≤ 2 * A * Real.exp (c * u) := by positivity
      exact le_add_of_nonneg_right (by positivity)
    · have h1 : 1 ≤ Real.exp (-(l * V) + l * u) + Real.exp (l * U + -(l * u)) := by
        by_cases hU : U ≤ u
        · have hV : V ≤ u := by by_contra hV; exact h (hw u ⟨hU, (not_le.1 hV).le⟩)
          have := Real.one_le_exp (x := -(l * V) + l * u) (by nlinarith)
          linarith [Real.exp_pos (l * U + -(l * u))]
        · have := Real.one_le_exp (x := l * U + -(l * u)) (by nlinarith [not_le.1 hU])
          linarith [Real.exp_pos (-(l * V) + l * u)]
      have h2 := hA u hu
      rw [abs_of_neg (not_le.1 h)] at h2 ⊢
      have h3 : 2 * (A * Real.exp (c * u)) * 1 ≤ 2 * (A * Real.exp (c * u)) *
        (Real.exp (-(l * V) + l * u) + Real.exp (l * U + -(l * u))) := by gcongr
      linarith
  have hre : (coeff f k σ).re =
      ∫ u in Ioi (0 : ℝ), u ^ k / k.factorial * f u * Real.exp (-(σ * u)) := by
    rw [coeff, ← ofReal_re (∫ u in Ioi (0 : ℝ), _), ← integral_complex_ofReal]
    push_cast
    rfl
  have i0 : IntegrableOn
      (fun u : ℝ => u ^ k / k.factorial * f u * Real.exp (-(σ * u))) (Ioi 0) := by
    refine (integrable_kernel hf hA k (s := σ) (by simpa)).re.congr (.of_forall fun u => ?_)
    simp only [← ofReal_mul, ← ofReal_neg, ← ofReal_exp]
    rfl
  have i1 := ((integrable_gamma_kernel hlσ k).const_mul (Real.exp (-(l * V)))).add
    ((integrable_gamma_kernel hl' k).const_mul (Real.exp (l * U)))
  have hi := integral_add i0 (i1.const_mul (2 * A))
  rw [integral_const_mul, integral_add' ((integrable_gamma_kernel hlσ k).const_mul _)
    ((integrable_gamma_kernel hl' k).const_mul _), integral_const_mul, integral_const_mul,
    integral_gamma_kernel hlσ, integral_gamma_kernel hl', ← hre, mul_one_div, mul_one_div] at hi
  rw [← hi]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (integrable_kernel hf hA k (by simpa)).norm (i0.add (i1.const_mul (2 * A)))
    measurableSet_Ioi fun u hu => ?_)
  rw [norm_kernel hu]
  calc _ ≤ u ^ k / k.factorial * (f u + 2 * A * Real.exp (c * u) *
      (Real.exp (-(l * V)) * Real.exp (l * u) + Real.exp (l * U) * Real.exp (-(l * u)))) *
        Real.exp (-(σ * u)) := by
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero]
        have := mem_Ioi.1 hu
        gcongr
        exact pt u this.le
    _ = _ := by
        simp only [Pi.add_apply]
        rw [show -((σ - c - l) * u) = c * u + l * u + -(σ * u) by ring,
          show -((σ - c + l) * u) = c * u + -(l * u) + -(σ * u) by ring]
        simp only [Real.exp_add]
        ring

/-- The error of `norm_coeff_le` is of order `σ ^ (-k)` when the window contains
`[ν k / σ, μ k / σ]`, for fixed `ν < 1 < μ` and every large `σ`. -/
lemma exists_error_le (hf : Measurable f) (hA : ∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u))
    {μ ν : ℝ} (hμ : 1 < μ) (hν : ν < 1) (hν0 : 0 < ν) : ∀ᶠ σ : ℝ in atTop, ∃ B, ∀ k : ℕ,
      (∀ u ∈ Icc (ν * k / σ) (μ * k / σ), 0 ≤ f u) →
        ∀ t : ℝ, ‖coeff f k (σ + t * I)‖ ≤ (coeff f k σ).re + B / σ ^ k := by
  have hA0 : 0 ≤ A := by simpa using (abs_nonneg _).trans (hA 0 le_rfl)
  obtain ⟨η, hη, hη'⟩ := exists_between (a₁ := (0 : ℝ)) (a₂ := min ((μ - 1) / μ) ((1 - ν) / ν))
    (lt_min (by apply div_pos <;> linarith) (by apply div_pos <;> linarith))
  obtain ⟨h1, h2⟩ := lt_min_iff.1 hη'
  rw [lt_div_iff₀ (by linarith)] at h1 h2
  have e1 : 0 < (1 - η) * (1 + η * μ) - 1 := by nlinarith
  have e2 : 0 < (1 + η) * (1 - η * ν) - 1 := by nlinarith
  filter_upwards [eventually_gt_atTop 0,
    eventually_ge_atTop (c * (1 + η * μ) / ((1 - η) * (1 + η * μ) - 1)),
    eventually_ge_atTop (c * (1 - η * ν) / ((1 + η) * (1 - η * ν) - 1))] with σ hσ g1 g2
  rw [div_le_iff₀ ‹_›] at g1 g2
  have p1 : 0 < 1 + η * μ := by nlinarith
  have p2 : 0 < 1 - η * ν := by nlinarith
  have q1 : 0 < σ - c - η * σ := pos_of_mul_pos_left (b := 1 + η * μ) (by nlinarith) p1.le
  have q2 : 0 < σ - c + η * σ := by nlinarith
  refine ⟨2 * A * (1 / (σ - c - η * σ) + 1 / (σ - c + η * σ)), fun k hw t =>
    (norm_coeff_le hf hA (by positivity : 0 ≤ η * σ) q1 hw k t).trans ?_⟩
  -- each tail is `(b e ^ x) ^ (-k) / b` with `b e ^ x ≥ b (1 + x) ≥ σ`
  have tail (b x : ℝ) (hb : 0 < b) (hx : σ ≤ b * (1 + x)) :
      Real.exp (-(x * k)) / b ^ (k + 1) ≤ 1 / b / σ ^ k := by
    have h : σ ^ k ≤ b ^ k * Real.exp (x * k) := by
      rw [mul_comm x, Real.exp_nat_mul, ← mul_pow]
      gcongr
      exact hx.trans (by gcongr; linarith [Real.add_one_le_exp x])
    rw [Real.exp_neg, div_div, pow_succ, inv_eq_one_div, div_div]
    exact one_div_le_one_div_of_le (by positivity)
      (by linarith [mul_le_mul_of_nonneg_left h hb.le])
  rw [mul_div_assoc _ _ (σ ^ k), add_div]
  gcongr _ + 2 * A * (?_ + ?_)
  · rw [show η * σ * (μ * k / σ) = η * μ * k by field_simp]
    exact tail _ _ q1 (by linarith)
  · rw [show η * σ * (ν * k / σ) = -(-(η * ν) * k) by field_simp]
    exact tail _ _ q2 (by linarith)

/-- Windows of fixed ratio contain `[ν k / σ, μ k / σ]` for arbitrarily large `k`. -/
lemma frequently_window {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hw : ∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ f u) : ∃ᶠ k : ℕ in atTop,
      ∀ u ∈ Icc (1 / (1 + δ / 2) * k / σ) ((1 + δ) / (1 + 3 * δ / 4) * k / σ), 0 ≤ f u := by
  rw [frequently_atTop]
  intro K
  obtain ⟨U, hU, h⟩ := hw (max (K / σ) (4 / (σ * δ)))
  obtain ⟨h1, h2⟩ := max_le_iff.1 hU
  rw [div_le_iff₀ (by positivity)] at h1 h2
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) (hU.le.trans' (le_max_right _ _))
  have k1 := Nat.le_ceil (σ * U * (1 + δ / 2))
  have k2 := (Nat.ceil_lt_add_one (a := σ * U * (1 + δ / 2)) (by positivity)).le
  refine ⟨⌈σ * U * (1 + δ / 2)⌉₊, ?_, fun u hu => h u ⟨le_trans ?_ hu.1, hu.2.trans ?_⟩⟩
  · exact Nat.cast_le.1 (h1.trans (by nlinarith [mul_pos (mul_pos hσ hU0) hδ]) : (K : ℝ) ≤ _)
  · rw [le_div_iff₀ hσ, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ hσ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

/-! ### The criterion -/

/-- `H` continues the Laplace transform of `f` from `Re s > c` to `Re s > θ`, and its poles there
are simple and form the locally finite set `Z`, with residue `κ ρ` at `ρ`. -/
structure Continues (f : ℝ → ℝ) (H : ℂ → ℂ) (Z : Set ℂ) (κ : ℂ → ℂ) (A c θ : ℝ) : Prop where
  measurable : Measurable f
  growth : ∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u)
  laplace : ∀ s : ℂ, c < s.re → H s = ∫ u in Ioi (0 : ℝ), (f u : ℂ) * cexp (-(s * u))
  analytic : ∀ s : ℂ, θ < s.re → s ∉ Z → AnalyticAt ℂ H s
  finite : ∀ (s : ℂ) (r : ℝ), (Z ∩ closedBall s r).Finite
  re_mem : ∀ ρ ∈ Z, ρ.re ∈ Ioc θ c
  residue_ne_zero : ∀ ρ ∈ Z, κ ρ ≠ 0
  pole : ∀ ρ ∈ Z, ∃ g, AnalyticAt ℂ g ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, H s = κ ρ / (s - ρ) + g s

lemma exists_nearest {Z : Set ℂ} (hZ : ∀ (s : ℂ) (r : ℝ), (Z ∩ closedBall s r).Finite)
    (hne : Z.Nonempty) (s : ℂ) : ∃ ρ ∈ Z, ∀ z ∈ Z, dist ρ s ≤ dist z s := by
  obtain ⟨ρ0, h0⟩ := hne
  obtain ⟨ρ, h1, h2⟩ := Set.exists_min_image _ (dist · s) (hZ s (dist ρ0 s))
    ⟨ρ0, h0, mem_closedBall.2 le_rfl⟩
  refine ⟨ρ, h1.1, fun z hz => ?_⟩
  by_cases h : dist z s ≤ dist ρ0 s
  · exact h2 z ⟨hz, h⟩
  · exact (mem_closedBall.1 h1.2).trans (not_le.1 h).le

namespace Continues

variable {H κ : ℂ → ℂ} {Z : Set ℂ} {θ : ℝ}

lemma exists_coeff_sub_le (h : Continues f H Z κ A c θ) {s ρ a : ℂ} {K : ℂ → ℂ} {R r : ℝ}
    (hs : c < s.re) (hρ : ρ ≠ s) (hr : 0 < r) (hrR : r < R) (hK : DifferentiableOn ℂ K (ball s R))
    (hKH : ∀ᶠ z in 𝓝 s, K z = H z - a / (z - ρ)) :
    ∃ M, ∀ k, ‖coeff f k s - a / (s - ρ) ^ (k + 1)‖ ≤ M / r ^ k := by
  have hρ' : s - ρ ≠ 0 := sub_ne_zero.2 hρ.symm
  have hcont : Tendsto (fun w : ℂ => s - w) (𝓝 0) (𝓝 s) := by
    simpa using Continuous.tendsto (f := fun w : ℂ => s - w) (by fun_prop) 0
  obtain ⟨M, hM⟩ := exists_coeff_le (D := fun k => coeff f k s - a / (s - ρ) ^ (k + 1))
    (h := fun w => K (s - w)) hr hrR
    (hK.comp (by fun_prop) fun w hw => by simpa [dist_eq_norm] using hw) (by
      filter_upwards [hcont.eventually hKH, ball_mem_nhds (0 : ℂ) (sub_pos.2 hs),
        ball_mem_nhds (0 : ℂ) (norm_pos_iff.2 hρ')] with w h1 h2 h3
      rw [mem_ball_zero_iff] at h2 h3
      have e1 := hasSum_coeff h.measurable h.growth h2
      rw [← h.laplace _ (by have := (abs_le.1 (abs_re_le_norm w)).2; simp; linarith)] at e1
      have h4 : ‖w / (s - ρ)‖ < 1 := by rwa [norm_div, div_lt_one (norm_pos_iff.2 hρ')]
      have e2 := (hasSum_geometric_of_norm_lt_one h4).mul_left (a / (s - ρ))
      have h5 : s - ρ - w ≠ 0 := sub_ne_zero.2 fun e => by simp [e] at h3
      rw [h1]
      have e : a / (s - w - ρ) = a / (s - ρ) * (1 - w / (s - ρ))⁻¹ := by
        rw [one_sub_div hρ', sub_right_comm s w]
        field_simp
      rw [e]
      refine (e1.sub e2).congr_fun fun k => ?_
      rw [div_pow, pow_succ]
      field_simp)
  exact ⟨M, fun k => (le_div_iff₀ (by positivity)).2 (hM k)⟩

lemma exists_coeff_le (h : Continues f H Z κ A c θ) {s : ℂ} {R r : ℝ} (hs : c < s.re) (hr : 0 < r)
    (hrR : r < R) (hR : R ≤ s.re - θ) (hZ : ∀ z ∈ Z, R ≤ dist z s) :
    ∃ M, ∀ k, ‖coeff f k s‖ ≤ M / r ^ k := by
  have := h.exists_coeff_sub_le (a := 0) (ρ := s + 1) (K := H) hs (by simp) hr hrR
    (fun z hz => (h.analytic z ?_ fun hzZ =>
      (hZ z hzZ).not_gt hz).differentiableAt.differentiableWithinAt) (by simp)
  · simpa using this
  · have := (abs_lt.1 ((abs_re_le_norm _).trans_lt (mem_ball_iff_norm.1 hz))).1
    simp at this
    linarith

lemma exists_coeff_sub_pole_le (h : Continues f H Z κ A c θ) {s ρ : ℂ} (hs : c < s.re) (hρ : ρ ∈ Z)
    (hlt : dist ρ s < s.re - θ) (huniq : ∀ z ∈ Z, z ≠ ρ → dist ρ s < dist z s) :
    ∃ R > dist ρ s, ∃ M, ∀ k, ‖coeff f k s - κ ρ / (s - ρ) ^ (k + 1)‖ ≤ M / R ^ k := by
  have hne : ρ ≠ s := fun e => by have := (h.re_mem ρ hρ).2; rw [e] at this; linarith
  obtain ⟨R, h1, h2, h3⟩ : ∃ R > dist ρ s, R ≤ s.re - θ ∧ ∀ z ∈ Z, z ≠ ρ → R ≤ dist z s := by
    rcases (Z \ {ρ}).eq_empty_or_nonempty with he | hn
    · exact ⟨_, hlt, le_rfl, fun z hz hzρ => absurd (he ▸ ⟨hz, hzρ⟩ : z ∈ (∅ : Set ℂ)) (by simp)⟩
    · obtain ⟨z, hz, hmin⟩ := exists_nearest (fun s r => (h.finite s r).subset
        (inter_subset_inter_left _ sdiff_subset)) hn s
      exact ⟨min (s.re - θ) (dist z s), lt_min hlt (huniq z hz.1 hz.2), min_le_left _ _,
        fun w hw hwρ => (min_le_right _ _).trans (hmin w ⟨hw, hwρ⟩)⟩
  obtain ⟨r, hr, hrR⟩ := exists_between h1
  obtain ⟨g, hg, hgH⟩ := h.pole ρ hρ
  refine ⟨r, hr, h.exists_coeff_sub_le (K := Function.update (fun z => H z - κ ρ / (z - ρ)) ρ (g ρ))
    hs hne (dist_nonneg.trans_lt hr) hrR (fun z hz => DifferentiableAt.differentiableWithinAt ?_)
    ?_⟩
  · rcases eq_or_ne z ρ with rfl | hzρ
    · refine hg.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [eventually_nhdsWithin_iff.1 hgH] with w hw
      rcases eq_or_ne w z with rfl | hwz
      · simp
      · rw [Function.update_of_ne hwz, hw hwz, add_sub_cancel_left]
    · have hre := (abs_lt.1 ((abs_re_le_norm _).trans_lt (mem_ball_iff_norm.1 hz))).1
      rw [sub_re] at hre
      have hzZ : z ∉ Z := fun hzZ => (h3 z hzZ hzρ).not_gt hz
      have hH := (h.analytic z (by linarith) hzZ).differentiableAt
      refine DifferentiableAt.congr_of_eventuallyEq (f := fun z => H z - κ ρ / (z - ρ)) ?_
        ((eventually_ne_nhds hzρ).mono fun w hw => Function.update_of_ne hw _ _)
      exact hH.sub ((differentiableAt_const _).div (by fun_prop) (sub_ne_zero.2 hzρ))
  · exact (eventually_ne_nhds hne.symm).mono fun w hw => Function.update_of_ne hw _ _

end Continues

lemma false_of_frequently {a r R₁ R₂ R₃ M₁ M₂ M₃ : ℝ} (ha : 0 < a) (hr : 0 < r) (h1 : r < R₁)
    (h2 : r < R₂) (h3 : r < R₃)
    (h : ∃ᶠ k : ℕ in atTop, a / r ^ (k + 1) ≤ M₁ / R₁ ^ k + M₂ / R₂ ^ k + M₃ / R₃ ^ k) : False := by
  have lim {M R : ℝ} (hR : r < R) : Tendsto (fun k : ℕ => M / R ^ k * r ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr.le (hr.trans hR).le)
      ((div_lt_one (hr.trans hR)).2 hR)).const_mul M
    simp_rw [mul_zero, div_pow] at this
    exact this.congr fun k => by ring
  have := ((lim (M := M₁) h1).add (lim (M := M₂) h2)).add (lim (M := M₃) h3)
  simp only [add_zero] at this
  obtain ⟨k, hk, hk'⟩ := (h.and_eventually (this.eventually_lt_const (div_pos ha hr))).exists
  have := mul_le_mul_of_nonneg_right hk (pow_pos hr k).le
  rw [pow_succ, div_mul_eq_div_div_swap, div_mul_cancel₀ _ (pow_pos hr k).ne'] at this
  linarith

/-- **Landau's theorem on windows.** If `f ≥ 0` on arbitrarily late windows `[U, (1 + δ) U]` and the
residues of its Laplace transform at real poles have negative real part, then the transform is
analytic in `Re s > θ`. -/
theorem Continues.eq_empty_of_window {H κ : ℂ → ℂ} {Z : Set ℂ} {θ δ : ℝ}
    (h : Continues f H Z κ A c θ) (hθ : 0 ≤ θ) (hκ : ∀ ρ ∈ Z, ρ.im = 0 → (κ ρ).re < 0) (hδ : 0 < δ)
    (hw : ∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ f u) : Z = ∅ := by
  by_contra hne
  obtain ⟨ρ₀, h₀⟩ := nonempty_iff_ne_empty.2 hne
  have hβ := (h.re_mem ρ₀ h₀).1
  obtain ⟨σ, ⟨⟨B, hB⟩, hσc⟩, hσ0, hσ⟩ := (((exists_error_le h.measurable h.growth
    (μ := (1 + δ) / (1 + 3 * δ / 4)) (ν := 1 / (1 + δ / 2))
    ((one_lt_div (by positivity)).2 (by linarith)) ((div_lt_one (by positivity)).2 (by linarith))
    (by positivity)).and (eventually_gt_atTop c)).and ((eventually_gt_atTop (ρ₀.re)).and
      (eventually_gt_atTop (ρ₀.re + ρ₀.im ^ 2 / (ρ₀.re - θ))))).exists
  have hσθ : θ < σ := hβ.trans hσ0
  have hfar : dist ρ₀ σ < σ - θ := by
    rw [← lt_sub_iff_add_lt', div_lt_iff₀ (sub_pos.2 hβ)] at hσ
    rw [dist_eq_re_im, Real.sqrt_lt' (by linarith), ofReal_re, ofReal_im]
    nlinarith
  have hre (t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  have hfreq := frequently_window hδ (hθ.trans_lt hσθ) hw
  -- a point of the vertical line with a unique nearest pole is impossible if the coefficients
  -- at `σ` are of smaller order
  have key (t : ℝ) (ρ : ℂ) (hρ : ρ ∈ Z) (hlt : dist ρ (σ + t * I) < σ - θ)
      (huniq : ∀ z ∈ Z, z ≠ ρ → dist ρ (σ + t * I) < dist z (σ + t * I)) (R M : ℝ)
      (hR : dist ρ (σ + t * I) < R) (hM : ∀ k, (coeff f k σ).re ≤ M / R ^ k) : False := by
    obtain ⟨R₁, hR₁, M₁, hM₁⟩ := h.exists_coeff_sub_pole_le (by simpa) hρ (by simpa) huniq
    have hpos : 0 < dist ρ (σ + t * I) := dist_pos.2 fun e => by
      have := (h.re_mem ρ hρ).2
      rw [e, hre] at this
      linarith
    refine false_of_frequently (M₁ := M₁) (M₂ := M) (M₃ := B)
      (norm_pos_iff.2 (h.residue_ne_zero ρ hρ)) hpos hR₁ hR (by linarith : _ < σ)
      (hfreq.mono fun k hk => ?_)
    have e : ‖κ ρ / (σ + t * I - ρ) ^ (k + 1)‖ = ‖κ ρ‖ / dist ρ (σ + t * I) ^ (k + 1) := by
      rw [norm_div, norm_pow, dist_comm, dist_eq_norm]
    have := norm_sub_norm_le (κ ρ / (σ + t * I - ρ) ^ (k + 1)) (coeff f k (σ + t * I))
    rw [norm_sub_rev (κ ρ / _), e] at this
    linarith [hM₁ k, hB k hk t, hM k]
  obtain ⟨ρ, hρ, hmin⟩ := exists_nearest h.finite ⟨ρ₀, h₀⟩ σ
  have hρlt := (hmin ρ₀ h₀).trans_lt hfar
  by_cases hA : ∃ z ∈ Z, σ - z.re < dist ρ σ
  · -- some pole is closer to the vertical line than any pole is to `σ`
    obtain ⟨z, hz, hzlt⟩ := hA
    have hsep (x y : ℂ) (hx : x ∈ Z) (hy : y ∈ Z) (hxy : x ≠ y) :
        {t : ℝ | dist x (σ + t * I) = dist y (σ + t * I)}.Subsingleton := by
      intro t ht t' ht'
      simp only [mem_ofPred_eq, dist_eq_re_im, hre] at ht ht'
      rw [Real.sqrt_inj (by positivity) (by positivity)] at ht ht'
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
        add_zero] at ht ht'
      have h1 : (t - t') * (x.im - y.im) = 0 := by linarith
      rcases mul_eq_zero.1 h1 with h1 | h1
      · linarith
      · have h2 : (x.re - y.re) * (x.re - σ + (y.re - σ)) = 0 := by
          rw [sub_eq_zero.1 h1] at ht
          linarith
        rcases mul_eq_zero.1 h2 with h2 | h2
        · exact absurd (Complex.ext (by linarith) (by linarith)) hxy
        · linarith [(h.re_mem x hx).2, (h.re_mem y hy).2]
    have hcZ : Z.Countable := by
      refine (countable_iUnion fun n : ℕ => (h.finite 0 n).countable).mono fun x hx => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge (dist x 0)
      exact mem_iUnion.2 ⟨n, hx, hn⟩
    have hbad : (⋃ x ∈ Z, ⋃ y ∈ Z,
        {t : ℝ | x ≠ y ∧ dist x (σ + t * I) = dist y (σ + t * I)}).Countable :=
      hcZ.biUnion fun x hx => hcZ.biUnion fun y hy => by
        by_cases hxy : x = y
        · simp [hxy]
        · simpa [hxy] using (hsep x y hx hy hxy).countable
    have hopen : IsOpen {t : ℝ | dist z (σ + t * I) < dist ρ σ} :=
      isOpen_lt (by fun_prop) continuous_const
    obtain ⟨t, ht1, ht2⟩ := (hbad.dense_compl ℝ).inter_open_nonempty _ hopen ⟨z.im, by
      have : 0 < σ - z.re := by linarith [(h.re_mem z hz).2]
      rw [mem_ofPred_eq, dist_eq_re_im]
      simpa [← abs_sub_comm σ, Real.sqrt_sq_eq_abs, abs_of_pos this] using hzlt⟩
    obtain ⟨ρ₁, hρ₁, hmin₁⟩ := exists_nearest h.finite ⟨ρ₀, h₀⟩ (σ + t * I)
    have hlt : dist ρ₁ (σ + t * I) < dist ρ σ := (hmin₁ z hz).trans_lt ht1
    obtain ⟨R, hR1, hR2⟩ := exists_between hlt
    obtain ⟨M, hM⟩ := h.exists_coeff_le (s := σ) hσc (dist_nonneg.trans_lt hR1) hR2 hρlt.le hmin
    refine key t ρ₁ hρ₁ (hlt.trans hρlt) (fun x hx hxρ => (hmin₁ x hx).lt_of_ne fun e => ht2 ?_) R M
      hR1 fun k => (re_le_norm _).trans (hM k)
    exact mem_biUnion hρ₁ (mem_biUnion hx ⟨hxρ.symm, e⟩)
  · -- the nearest pole to `σ` is real, and its sign is wrong
    push Not at hA
    have hreal (z : ℂ) (hz : z ∈ Z) (he : dist z σ = dist ρ σ) : z = ((σ - dist ρ σ : ℝ) : ℂ) := by
      have h1 := hA z hz
      have h2 : σ - z.re ≤ dist z σ := by
        rw [dist_comm, dist_eq_norm]
        simpa using re_le_norm (σ - z)
      have h3 : dist z σ ^ 2 = (z.re - σ) ^ 2 + z.im ^ 2 := by
        rw [dist_eq_re_im, Real.sq_sqrt (by positivity)]
        simp
      have h4 : σ - z.re = dist ρ σ := by linarith
      apply Complex.ext
      · simp [← h4]
      · rw [he, ← h4] at h3
        simpa using (by nlinarith : z.im ^ 2 = 0)
    have huniq (z : ℂ) (hz : z ∈ Z) (hzρ : z ≠ ρ) : dist ρ σ < dist z σ :=
      (hmin z hz).lt_of_ne fun e => hzρ ((hreal z hz e.symm).trans (hreal ρ hρ rfl).symm)
    obtain ⟨R, hR, M, hM⟩ := h.exists_coeff_sub_pole_le (s := σ) hσc hρ (by simpa) huniq
    refine key 0 ρ hρ (by simpa) (by simpa) R M (by simpa) fun k => ?_
    have e : (κ ρ / (σ - ρ) ^ (k + 1)).re = (κ ρ).re / dist ρ σ ^ (k + 1) := by
      have : (σ : ℂ) - ρ = (dist ρ σ : ℝ) := by
        conv_lhs => rw [hreal ρ hρ rfl]
        simp
      rw [this, ← ofReal_pow, div_ofReal_re]
    have h1 := (re_le_norm _).trans (hM k)
    rw [sub_re, e] at h1
    have h2 : (κ ρ).re / dist ρ σ ^ (k + 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (hκ ρ hρ (by rw [hreal ρ hρ rfl]; simp)).le (by positivity)
    linarith

end Masullo.Landau
