import Mathlib

/-!
# Landau's theorem on windows

Let `f` be real with at most exponential growth and `θ ≥ 0`. Let its Laplace transform continue
meromorphically to `Re s > θ` with poles of finite order, finitely many in each disc of the plane,
and let every real pole there have a leading Laurent coefficient with negative real part. If, for a
fixed `δ > 0`, `f ≥ 0` on windows `[U, (1 + δ) U]` with `U` arbitrarily large, then there are no
poles in `Re s > θ`. This is a one-way implication; it asserts nothing about the sign of `f` outside
the windows. `Continues` records the case of simple poles with given residues and
`ContinuesMero` the general one; the theorem is `ContinuesMero.eq_empty_of_window`.

The Taylor coefficients of the transform at `σ + i t` are integrals of `f` against the kernels
`u ^ k e ^ (-σ u) / k!`, which concentrate at `u = k / σ`. When `k / σ` is inside a window, the
coefficient at `σ` bounds those at every `σ + i t`, up to an error below the scale set by the poles.
A pole of order `m + 1` at `ρ` contributes Taylor coefficients of size `k ^ m / |σ - ρ| ^ k`,
dominated by the term of its leading Laurent coefficient.

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

lemma laplace_exp {a s : ℂ} (h : a.re < s.re) (c : ℝ) :
    IntegrableOn (fun u : ℝ => cexp (a * u) * cexp (-(s * u))) (Ioi c) ∧
      ∫ u in Ioi c, cexp (a * u) * cexp (-(s * u)) = cexp ((a - s) * c) / (s - a) := by
  have e (u : ℝ) : cexp (a * u) * cexp (-(s * u)) = cexp ((a - s) * u) := by
    rw [← Complex.exp_add]
    ring_nf
  have h' : (a - s).re < 0 := by simpa using h
  simp_rw [e]
  refine ⟨integrableOn_exp_mul_complex_Ioi h' c, ?_⟩
  rw [integral_exp_mul_complex_Ioi h', ← neg_sub s a, div_neg, neg_div, neg_neg]

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

/-- `H` continues the Laplace transform of `f` from `Re s > c` to `Re s > θ`, and its poles there
have finite order and form the locally finite set `Z`. At `ρ ∈ Z` the transform is
`g s / (s - ρ) ^ (m + 1)` with `g` analytic at `ρ` and `g ρ ≠ 0`. -/
structure ContinuesMero (f : ℝ → ℝ) (H : ℂ → ℂ) (Z : Set ℂ) (A c θ : ℝ) : Prop where
  measurable : Measurable f
  growth : ∀ u, 0 ≤ u → |f u| ≤ A * Real.exp (c * u)
  laplace : ∀ s : ℂ, c < s.re → H s = ∫ u in Ioi (0 : ℝ), (f u : ℂ) * cexp (-(s * u))
  analytic : ∀ s : ℂ, θ < s.re → s ∉ Z → AnalyticAt ℂ H s
  finite : ∀ (s : ℂ) (r : ℝ), (Z ∩ closedBall s r).Finite
  re_mem : ∀ ρ ∈ Z, ρ.re ∈ Ioc θ c
  pole : ∀ ρ ∈ Z, ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
    ∀ᶠ s in 𝓝[≠] ρ, H s = g s / (s - ρ) ^ (m + 1)

lemma exists_nearest {Z : Set ℂ} (hZ : ∀ (s : ℂ) (r : ℝ), (Z ∩ closedBall s r).Finite)
    (hne : Z.Nonempty) (s : ℂ) : ∃ ρ ∈ Z, ∀ z ∈ Z, dist ρ s ≤ dist z s := by
  obtain ⟨ρ0, h0⟩ := hne
  obtain ⟨ρ, h1, h2⟩ := Set.exists_min_image _ (dist · s) (hZ s (dist ρ0 s))
    ⟨ρ0, h0, mem_closedBall.2 le_rfl⟩
  refine ⟨ρ, h1.1, fun z hz => ?_⟩
  by_cases h : dist z s ≤ dist ρ0 s
  · exact h2 z ⟨hz, h⟩
  · exact (mem_closedBall.1 h1.2).trans (not_le.1 h).le

/-- A simple pole with residue `κ ρ` is `g s / (s - ρ)` with `g ρ = κ ρ`. -/
lemma Continues.exists_pole {H κ : ℂ → ℂ} {Z : Set ℂ} {θ : ℝ} (h : Continues f H Z κ A c θ)
    {ρ : ℂ} (hρ : ρ ∈ Z) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ = κ ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, H s = g s / (s - ρ) ^ (0 + 1) := by
  obtain ⟨g, hg, hH⟩ := h.pole ρ hρ
  refine ⟨fun s => κ ρ + (s - ρ) * g s, by fun_prop, by simp, ?_⟩
  filter_upwards [hH, self_mem_nhdsWithin] with s hs hne
  rw [hs, zero_add, pow_one]
  field_simp [sub_ne_zero.2 hne]

lemma Continues.toMero {H κ : ℂ → ℂ} {Z : Set ℂ} {θ : ℝ} (h : Continues f H Z κ A c θ) :
    ContinuesMero f H Z A c θ where
  measurable := h.measurable
  growth := h.growth
  laplace := h.laplace
  analytic := h.analytic
  finite := h.finite
  re_mem := h.re_mem
  pole ρ hρ := by
    obtain ⟨g, hg, hgρ, hH⟩ := h.exists_pole hρ
    exact ⟨0, g, hg, hgρ ▸ h.residue_ne_zero ρ hρ, hH⟩

/-- Scaling `f` by `b ≠ 0` scales the transform and the residues by `b`. -/
lemma Continues.const_mul {H κ : ℂ → ℂ} {Z : Set ℂ} {θ : ℝ} (h : Continues f H Z κ A c θ)
    {b : ℝ} (hb : b ≠ 0) :
    Continues (fun u => b * f u) (fun s => b * H s) Z (fun ρ => b * κ ρ) (|b| * A) c θ where
  measurable := h.measurable.const_mul b
  growth u hu := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.growth u hu) (abs_nonneg b)
  laplace s hs := by
    rw [h.laplace s hs, ← integral_const_mul]
    congr 1 with u
    push_cast
    ring
  analytic s hs hZ := analyticAt_const.mul (h.analytic s hs hZ)
  finite := h.finite
  re_mem := h.re_mem
  residue_ne_zero ρ hρ := mul_ne_zero (ofReal_ne_zero.2 hb) (h.residue_ne_zero ρ hρ)
  pole ρ hρ := by
    obtain ⟨k, hk, he⟩ := h.pole ρ hρ
    exact ⟨fun s => b * k s, analyticAt_const.mul hk, he.mono fun s hs => by rw [hs]; ring⟩

/-- Adding `C / (s - θ)` to `g s / (s - ρ) ^ (m + 1)`, with `θ < re ρ`, keeps the order and the
leading coefficient of the pole. -/
lemma exists_pole_add {H g : ℂ → ℂ} {ρ : ℂ} {m : ℕ} {θ : ℝ} (C : ℂ) (hρ : θ < ρ.re)
    (hg : AnalyticAt ℂ g ρ) (hH : ∀ᶠ s in 𝓝[≠] ρ, H s = g s / (s - ρ) ^ (m + 1)) :
    ∃ g' : ℂ → ℂ, AnalyticAt ℂ g' ρ ∧ g' ρ = g ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, C / (s - θ) + H s = g' s / (s - ρ) ^ (m + 1) := by
  have hθρ : ρ - θ ≠ 0 := sub_ne_zero.2 fun e => by simp [e] at hρ
  refine ⟨fun s => C * (s - ρ) ^ (m + 1) / (s - θ) + g s,
    ((by fun_prop : AnalyticAt ℂ (fun s : ℂ => C * (s - ρ) ^ (m + 1)) ρ).div
      (by fun_prop) hθρ).add hg, by simp, ?_⟩
  filter_upwards [hH, self_mem_nhdsWithin,
    ((continuous_sub_right (θ : ℂ)).continuousAt.eventually_ne hθρ).filter_mono
      nhdsWithin_le_nhds] with s hs hne hsθ
  have : s - ρ ≠ 0 := sub_ne_zero.2 hne
  rw [hs]
  field_simp

/-- Adding `C e ^ (θ u)` to `f` adds `C / (s - θ)` to the transform and keeps the poles. -/
lemma ContinuesMero.add_exp {H : ℂ → ℂ} {Z : Set ℂ} {θ : ℝ} (h : ContinuesMero f H Z A c θ)
    (hθc : θ ≤ c) (C : ℝ) : ContinuesMero (fun u => C * Real.exp (θ * u) + f u)
      (fun s => C / (s - θ) + H s) Z (|C| + A) c θ where
  measurable := by
    have := h.measurable
    fun_prop
  growth u hu := by
    have h1 := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hθc hu)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Real.abs_exp, add_mul]
    gcongr
    exact h.growth u hu
  laplace s hs := by
    obtain ⟨i1, v1⟩ := laplace_exp (a := θ) (s := s) (by simp; linarith) 0
    have i2 := integrable_kernel h.measurable h.growth 0 hs
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at i2
    rw [ofReal_zero, mul_zero, Complex.exp_zero] at v1
    rw [h.laplace s hs, div_eq_mul_one_div, ← v1, ← integral_const_mul,
      ← integral_add (i1.const_mul _) i2]
    congr 1 with u
    push_cast
    ring
  analytic s hs hZ := (analyticAt_const.div (g := fun s : ℂ => s - θ) (by fun_prop)
    (sub_ne_zero.2 fun e => by simp [e] at hs)).add (h.analytic s hs hZ)
  finite := h.finite
  re_mem := h.re_mem
  pole ρ hρ := by
    obtain ⟨m, g, hg, hg0, hH⟩ := h.pole ρ hρ
    obtain ⟨g', hg', he, hH'⟩ := exists_pole_add C (h.re_mem ρ hρ).1 hg hH
    exact ⟨m, g', hg', he ▸ hg0, hH'⟩

/-! ### Principal parts -/

lemma analyticAt_dslope_self {p : ℂ → ℂ} {a : ℂ} (h : AnalyticAt ℂ p a) :
    AnalyticAt ℂ (dslope p a) a := by
  have hs := h.eventually_analyticAt
  exact ((differentiableOn_dslope hs).2 fun z hz =>
    hz.differentiableAt.differentiableWithinAt).analyticAt hs

/-- `g z / (z - ρ) ^ (m + 1)` is a principal part with leading coefficient `g ρ` plus a function
analytic at `ρ`. -/
lemma exists_principal {g : ℂ → ℂ} {ρ : ℂ} (hg : AnalyticAt ℂ g ρ) (m : ℕ) :
    ∃ a : ℕ → ℂ, a m = g ρ ∧ ∃ g₂ : ℂ → ℂ, AnalyticAt ℂ g₂ ρ ∧ ∀ z, z ≠ ρ →
      g z / (z - ρ) ^ (m + 1) = ∑ j ∈ Finset.range (m + 1), a j / (z - ρ) ^ (j + 1) + g₂ z := by
  induction m generalizing g with
  | zero =>
    refine ⟨fun _ => g ρ, rfl, dslope g ρ, analyticAt_dslope_self hg, fun z hz => ?_⟩
    rw [dslope_of_ne _ hz, slope_def_field]
    simp only [zero_add, pow_one, Finset.range_one, Finset.sum_singleton]
    field_simp [sub_ne_zero.2 hz]
    ring
  | succ m ih =>
    obtain ⟨a, -, g₂, hg₂, he⟩ := ih (analyticAt_dslope_self hg)
    refine ⟨Function.update a (m + 1) (g ρ), by simp, g₂, hg₂, fun z hz => ?_⟩
    have hs : ∑ j ∈ Finset.range (m + 1), Function.update a (m + 1) (g ρ) j / (z - ρ) ^ (j + 1) =
        ∑ j ∈ Finset.range (m + 1), a j / (z - ρ) ^ (j + 1) :=
      Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (by simp at hj; omega)]
    have hd : g z = g ρ + (z - ρ) * dslope g ρ z := by
      rw [dslope_of_ne _ hz, slope_def_field]
      field_simp [sub_ne_zero.2 hz]
      ring
    rw [Finset.sum_range_succ, hs, Function.update_self,
      show ∀ x y w : ℂ, x + y + w = x + w + y from fun _ _ _ => by ring, ← he z hz, hd]
    field_simp [sub_ne_zero.2 hz]
    ring

/-- The `k`-th Taylor coefficient at `ρ + e` of `∑_{j ≤ m} a j / (z - ρ) ^ (j + 1)`. -/
noncomputable def principal (a : ℕ → ℂ) (m : ℕ) (e : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), a j * (k + j).choose j / e ^ (k + j + 1)

lemma hasSum_principal (a : ℕ → ℂ) (m : ℕ) {e w : ℂ} (hw : ‖w‖ < ‖e‖) :
    HasSum (fun k => principal a m e k * w ^ k)
      (∑ j ∈ Finset.range (m + 1), a j / (e - w) ^ (j + 1)) := by
  have he : e ≠ 0 := norm_pos_iff.1 ((norm_nonneg w).trans_lt hw)
  have hew : e - w ≠ 0 := sub_ne_zero.2 fun h => by rw [h] at hw; exact lt_irrefl _ hw
  have hr : ‖w / e‖ < 1 := by rwa [norm_div, div_lt_one (norm_pos_iff.2 he)]
  simp_rw [principal, Finset.sum_mul]
  refine hasSum_sum fun j _ => ?_
  have e1 : a j / (e - w) ^ (j + 1) = a j / e ^ (j + 1) * (1 / (1 - w / e) ^ (j + 1)) := by
    rw [one_sub_div he, div_pow]
    field_simp
  rw [e1]
  refine ((hasSum_choose_mul_geometric_of_norm_lt_one j hr).mul_left _).congr_fun fun k => ?_
  rw [div_pow]
  field_simp
  ring

lemma choose_mul_le {k j m : ℕ} (hj : j < m) :
    (k + j).choose j * (k + 1) ≤ (k + m).choose m * m := by
  have h1 := Nat.add_one_mul_choose_eq (k + j) j
  have h2 : (k + j + 1).choose (j + 1) ≤ (k + m).choose m := by
    rw [show k + j + 1 = k + (j + 1) by omega, ← Nat.choose_symm_add, ← Nat.choose_symm_add]
    exact Nat.choose_le_choose k (by omega)
  calc (k + j).choose j * (k + 1) ≤ (k + j).choose j * (k + j + 1) := by gcongr; omega
    _ = (k + j + 1).choose (j + 1) * (j + 1) := by rw [mul_comm, h1]
    _ ≤ _ := Nat.mul_le_mul h2 hj

/-- The terms below the leading one are smaller by a factor of order `1 / k`. -/
lemma norm_principal_sub_le (a : ℕ → ℂ) (m k : ℕ) {e : ℂ} (he : e ≠ 0) :
    ‖principal a m e k - a m * (k + m).choose m / e ^ (k + m + 1)‖ ≤
      (k + m).choose m / ‖e‖ ^ (k + 1) *
        (m / (k + 1) * ∑ j ∈ Finset.range m, ‖a j‖ / ‖e‖ ^ j) := by
  have hd : 0 < ‖e‖ := norm_pos_iff.2 he
  rw [principal, Finset.sum_range_succ, add_sub_cancel_right, Finset.mul_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hc : ((k + j).choose j : ℝ) * (k + 1) ≤ (k + m).choose m * m := by
    exact_mod_cast choose_mul_le (Finset.mem_range.1 hj)
  have e1 : ‖a j * (k + j).choose j / e ^ (k + j + 1)‖ =
      ‖a j‖ / ‖e‖ ^ j / ‖e‖ ^ (k + 1) * (k + j).choose j := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    ring
  have e2 : (k + m).choose m / ‖e‖ ^ (k + 1) * (m / (k + 1) * (‖a j‖ / ‖e‖ ^ j)) =
      ‖a j‖ / ‖e‖ ^ j / ‖e‖ ^ (k + 1) * ((k + m).choose m * m / (k + 1)) := by
    ring
  rw [e1, e2]
  gcongr
  rw [le_div_iff₀ (by positivity)]
  exact hc

/-- Eventually the relative size `m / (k + 1) * ∑ ‖a j‖ / d ^ j` of the lower terms in
`norm_principal_sub_le` is below any `q > 0`. -/
lemma eventually_lower_le (a : ℕ → ℂ) (m : ℕ) {d q : ℝ} (hd : 0 ≤ d) (hq : 0 < q) :
    ∀ᶠ k : ℕ in atTop, (m : ℝ) / (k + 1) * ∑ j ∈ Finset.range m, ‖a j‖ / d ^ j ≤ q := by
  have hB : 0 ≤ ∑ j ∈ Finset.range m, ‖a j‖ / d ^ j := Finset.sum_nonneg fun j _ => by positivity
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat
    ((m : ℝ) * ∑ j ∈ Finset.range m, ‖a j‖ / d ^ j)).eventually (gt_mem_nhds hq),
    eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  refine le_trans ?_ hk.le
  rw [div_mul_eq_mul_div]
  gcongr
  linarith

lemma eventually_le_norm_principal (a : ℕ → ℂ) (m : ℕ) {e : ℂ} (he : e ≠ 0) (ha : a m ≠ 0) :
    ∀ᶠ k : ℕ in atTop, ‖a m‖ / (2 * ‖e‖ ^ m) / ‖e‖ ^ (k + 1) ≤ ‖principal a m e k‖ := by
  have hd : 0 < ‖e‖ := norm_pos_iff.2 he
  have ha' : 0 < ‖a m‖ := norm_pos_iff.2 ha
  filter_upwards [eventually_lower_le a m hd.le (by positivity : 0 < ‖a m‖ / (2 * ‖e‖ ^ m))]
    with k hk'
  set B := ∑ j ∈ Finset.range m, ‖a j‖ / ‖e‖ ^ j
  have h1 := norm_principal_sub_le a m k he
  have h2 := norm_sub_norm_le (a m * (k + m).choose m / e ^ (k + m + 1)) (principal a m e k)
  rw [norm_sub_rev] at h2
  have s3 : ‖a m‖ / ‖e‖ ^ m = 2 * (‖a m‖ / (2 * ‖e‖ ^ m)) := by field_simp
  have e3 : ‖a m * (k + m).choose m / e ^ (k + m + 1)‖ =
      (k + m).choose m / ‖e‖ ^ (k + 1) * (2 * (‖a m‖ / (2 * ‖e‖ ^ m))) := by
    rw [← s3, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    ring
  have hC : (1 : ℝ) ≤ (k + m).choose m := by exact_mod_cast Nat.choose_pos (by omega)
  have s1 : ‖a m‖ / (2 * ‖e‖ ^ m) / ‖e‖ ^ (k + 1) ≤
      (k + m).choose m / ‖e‖ ^ (k + 1) * (‖a m‖ / (2 * ‖e‖ ^ m)) := by
    calc _ = 1 / ‖e‖ ^ (k + 1) * (‖a m‖ / (2 * ‖e‖ ^ m)) := by ring
      _ ≤ _ := by gcongr
  have s2 : (k + m).choose m / ‖e‖ ^ (k + 1) * (m / (k + 1) * B) ≤
      (k + m).choose m / ‖e‖ ^ (k + 1) * (‖a m‖ / (2 * ‖e‖ ^ m)) := by gcongr
  rw [e3] at h2
  linarith

lemma eventually_re_principal_nonpos (a : ℕ → ℂ) (m : ℕ) {d : ℝ} (hd : 0 < d)
    (ha : (a m).re < 0) : ∀ᶠ k : ℕ in atTop, (principal a m d k).re ≤ 0 := by
  have hn : ‖(d : ℂ)‖ = d := by simp [abs_of_pos hd]
  filter_upwards [eventually_lower_le a m hd.le
    (div_pos (by linarith) (by positivity) : 0 < -(a m).re / d ^ m)] with k hk'
  set B := ∑ j ∈ Finset.range m, ‖a j‖ / d ^ j
  have h1 := norm_principal_sub_le a m k (e := d) (by exact_mod_cast hd.ne')
  rw [hn] at h1
  have h2 := re_le_norm (principal a m d k - a m * (k + m).choose m / (d : ℂ) ^ (k + m + 1))
  rw [sub_re] at h2
  have e3 : (a m * (k + m).choose m / (d : ℂ) ^ (k + m + 1)).re =
      (k + m).choose m / d ^ (k + 1) * ((a m).re / d ^ m) := by
    rw [← ofReal_natCast, ← ofReal_pow, mul_div_assoc, ← ofReal_div, re_mul_ofReal]
    ring
  have s2 : (k + m).choose m / d ^ (k + 1) * (m / (k + 1) * B) ≤
      (k + m).choose m / d ^ (k + 1) * (-(a m).re / d ^ m) := by gcongr
  have s3 : (k + m).choose m / d ^ (k + 1) * (-(a m).re / d ^ m) =
      -((k + m).choose m / d ^ (k + 1) * ((a m).re / d ^ m)) := by ring
  linarith

namespace ContinuesMero

variable {H : ℂ → ℂ} {Z : Set ℂ} {θ : ℝ}

lemma dist_pos_of_mem (h : ContinuesMero f H Z A c θ) {s ρ : ℂ} (hs : c < s.re) (hρ : ρ ∈ Z) :
    0 < dist ρ s :=
  dist_pos.2 fun e => by have := (h.re_mem ρ hρ).2; rw [e] at this; linarith

lemma exists_coeff_sub_le (h : ContinuesMero f H Z A c θ) {s : ℂ} {p K : ℂ → ℂ} {P : ℕ → ℂ}
    {R r : ℝ} (hs : c < s.re) (hr : 0 < r) (hrR : r < R) (hK : DifferentiableOn ℂ K (ball s R))
    (hKH : ∀ᶠ z in 𝓝 s, K z = H z - p z)
    (hp : ∀ᶠ w in 𝓝 0, HasSum (fun k => P k * w ^ k) (p (s - w))) :
    ∃ M, ∀ k, ‖coeff f k s - P k‖ ≤ M / r ^ k := by
  have hcont : Tendsto (fun w : ℂ => s - w) (𝓝 0) (𝓝 s) := by
    simpa using Continuous.tendsto (f := fun w : ℂ => s - w) (by fun_prop) 0
  obtain ⟨M, hM⟩ := exists_coeff_le (D := fun k => coeff f k s - P k)
    (h := fun w => K (s - w)) hr hrR
    (hK.comp (by fun_prop) fun w hw => by simpa [dist_eq_norm] using hw) (by
      filter_upwards [hcont.eventually hKH, ball_mem_nhds (0 : ℂ) (sub_pos.2 hs), hp]
        with w h1 h2 h3
      rw [mem_ball_zero_iff] at h2
      have e1 := hasSum_coeff h.measurable h.growth h2
      rw [← h.laplace _ (by have := (abs_le.1 (abs_re_le_norm w)).2; simp; linarith)] at e1
      rw [h1]
      exact (e1.sub h3).congr_fun fun k => by ring)
  exact ⟨M, fun k => (le_div_iff₀ (by positivity)).2 (hM k)⟩

lemma exists_coeff_le (h : ContinuesMero f H Z A c θ) {s : ℂ} {R r : ℝ} (hs : c < s.re)
    (hr : 0 < r) (hrR : r < R) (hR : R ≤ s.re - θ) (hZ : ∀ z ∈ Z, R ≤ dist z s) :
    ∃ M, ∀ k, ‖coeff f k s‖ ≤ M / r ^ k := by
  have := h.exists_coeff_sub_le (p := fun _ => 0) (P := fun _ => 0) (K := H) hs hr hrR
    (fun z hz => (h.analytic z ?_ fun hzZ =>
      (hZ z hzZ).not_gt hz).differentiableAt.differentiableWithinAt) (by simp)
    (by simp [hasSum_zero])
  · simpa using this
  · have := (abs_lt.1 ((abs_re_le_norm _).trans_lt (mem_ball_iff_norm.1 hz))).1
    simp at this
    linarith

/-- Near the nearest pole the coefficients at `s` follow those of the principal part. -/
lemma exists_coeff_sub_pole_le (h : ContinuesMero f H Z A c θ) {s ρ : ℂ} {m : ℕ}
    {g : ℂ → ℂ} (hs : c < s.re) (hρ : ρ ∈ Z) (hg : AnalyticAt ℂ g ρ)
    (hH : ∀ᶠ z in 𝓝[≠] ρ, H z = g z / (z - ρ) ^ (m + 1)) (hlt : dist ρ s < s.re - θ)
    (huniq : ∀ z ∈ Z, z ≠ ρ → dist ρ s < dist z s) : ∃ a : ℕ → ℂ, a m = g ρ ∧
      ∃ R > dist ρ s, ∃ M, ∀ k, ‖coeff f k s - principal a m (s - ρ) k‖ ≤ M / R ^ k := by
  have hne : ρ ≠ s := dist_pos.1 (h.dist_pos_of_mem hs hρ)
  obtain ⟨R, h1, h2, h3⟩ : ∃ R > dist ρ s, R ≤ s.re - θ ∧ ∀ z ∈ Z, z ≠ ρ → R ≤ dist z s := by
    rcases (Z \ {ρ}).eq_empty_or_nonempty with he | hn
    · exact ⟨_, hlt, le_rfl, fun z hz hzρ => absurd (he ▸ ⟨hz, hzρ⟩ : z ∈ (∅ : Set ℂ)) (by simp)⟩
    · obtain ⟨z, hz, hmin⟩ := exists_nearest (fun s r => (h.finite s r).subset
        (inter_subset_inter_left _ sdiff_subset)) hn s
      exact ⟨min (s.re - θ) (dist z s), lt_min hlt (huniq z hz.1 hz.2), min_le_left _ _,
        fun w hw hwρ => (min_le_right _ _).trans (hmin w ⟨hw, hwρ⟩)⟩
  obtain ⟨r, hr, hrR⟩ := exists_between h1
  obtain ⟨a, ha, g₂, hg₂, hexp⟩ := exists_principal hg m
  refine ⟨a, ha, r, hr, h.exists_coeff_sub_le
    (p := fun z => ∑ j ∈ Finset.range (m + 1), a j / (z - ρ) ^ (j + 1))
    (K := Function.update (fun z => H z - ∑ j ∈ Finset.range (m + 1), a j / (z - ρ) ^ (j + 1))
      ρ (g₂ ρ))
    hs (dist_nonneg.trans_lt hr) hrR (fun z hz => DifferentiableAt.differentiableWithinAt ?_)
    ?_ ?_⟩
  · rcases eq_or_ne z ρ with rfl | hzρ
    · refine hg₂.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [eventually_nhdsWithin_iff.1 hH] with w hw
      rcases eq_or_ne w z with rfl | hwz
      · simp
      · rw [Function.update_of_ne hwz, hw hwz, hexp w hwz, add_sub_cancel_left]
    · have hre := (abs_lt.1 ((abs_re_le_norm _).trans_lt (mem_ball_iff_norm.1 hz))).1
      rw [sub_re] at hre
      have hzZ : z ∉ Z := fun hzZ => (h3 z hzZ hzρ).not_gt hz
      have hH' := (h.analytic z (by linarith) hzZ).differentiableAt
      refine DifferentiableAt.congr_of_eventuallyEq
        (f := fun z => H z - ∑ j ∈ Finset.range (m + 1), a j / (z - ρ) ^ (j + 1)) ?_
        ((eventually_ne_nhds hzρ).mono fun w hw => Function.update_of_ne hw _ _)
      exact hH'.sub (DifferentiableAt.fun_sum fun j _ => (differentiableAt_const (a j)).div
        ((differentiableAt_id.sub_const ρ).pow (j + 1)) (pow_ne_zero _ (sub_ne_zero.2 hzρ)))
  · exact (eventually_ne_nhds hne.symm).mono fun w hw => Function.update_of_ne hw _ _
  · filter_upwards [ball_mem_nhds (0 : ℂ) (norm_pos_iff.2 (sub_ne_zero.2 hne.symm))] with w hw
    rw [mem_ball_zero_iff] at hw
    simpa only [sub_right_comm s w ρ] using hasSum_principal a m hw

end ContinuesMero

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


/-- **Landau's theorem on windows**, for poles of finite order. If `f ≥ 0` on arbitrarily late
windows `[U, (1 + δ) U]`, and at each real pole the transform is `g s / (s - ρ) ^ (m + 1)` for some
`g` with `Re (g ρ) < 0`, then the transform is analytic in `Re s > θ`. -/
theorem ContinuesMero.eq_empty_of_window {H : ℂ → ℂ} {Z : Set ℂ} {θ δ : ℝ}
    (h : ContinuesMero f H Z A c θ) (hθ : 0 ≤ θ)
    (hneg : ∀ ρ ∈ Z, ρ.im = 0 → ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧ (g ρ).re < 0 ∧
      ∀ᶠ s in 𝓝[≠] ρ, H s = g s / (s - ρ) ^ (m + 1))
    (hδ : 0 < δ) (hw : ∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ f u) : Z = ∅ := by
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
      (hR : dist ρ (σ + t * I) < R) (hM : ∀ᶠ k : ℕ in atTop, (coeff f k σ).re ≤ M / R ^ k) :
      False := by
    obtain ⟨m, g, hg, hg0, hH⟩ := h.pole ρ hρ
    obtain ⟨a, ha, R₁, hR₁, M₁, hM₁⟩ :=
      h.exists_coeff_sub_pole_le (by simpa) hρ hg hH (by simpa) huniq
    have ha0 : a m ≠ 0 := by rw [ha]; exact hg0
    have hpos := h.dist_pos_of_mem (s := σ + t * I) (by simpa) hρ
    have hd : ‖σ + t * I - ρ‖ = dist ρ (σ + t * I) := by rw [dist_comm, dist_eq_norm]
    have he : σ + t * I - ρ ≠ 0 := by rw [← norm_pos_iff, hd]; exact hpos
    have ha' : 0 < ‖a m‖ := norm_pos_iff.2 ha0
    refine false_of_frequently (M₁ := M₁) (M₂ := M) (M₃ := B)
      (a := ‖a m‖ / (2 * dist ρ (σ + t * I) ^ m)) (by positivity) hpos hR₁ hR
      (by linarith : _ < σ) ((hfreq.and_eventually
        ((eventually_le_norm_principal a m he ha0).and hM)).mono fun k ⟨hk, hlow, hMk⟩ => ?_)
    rw [hd] at hlow
    have := norm_sub_norm_le (principal a m (σ + t * I - ρ) k) (coeff f k (σ + t * I))
    rw [norm_sub_rev (principal a m _ k)] at this
    linarith [hM₁ k, hB k hk t]
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
      hR1 (.of_forall fun k => (re_le_norm _).trans (hM k))
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
    obtain ⟨m, g, hg, hgre, hH⟩ := hneg ρ hρ (by rw [hreal ρ hρ rfl]; simp)
    obtain ⟨a, ha, R, hR, M, hM⟩ :=
      h.exists_coeff_sub_pole_le (s := σ) hσc hρ hg hH (by simpa) huniq
    have hσρ : (σ : ℂ) - ρ = (dist ρ σ : ℝ) := by
      conv_lhs => rw [hreal ρ hρ rfl]
      simp
    have hpos := h.dist_pos_of_mem (s := σ) (by simpa) hρ
    refine key 0 ρ hρ (by simpa) (by simpa) R M (by simpa) ?_
    filter_upwards [eventually_re_principal_nonpos a m hpos (by rw [ha]; exact hgre)] with k hk
    have h1 := (re_le_norm _).trans (hM k)
    rw [sub_re, hσρ] at h1
    linarith

/-- `ContinuesMero.eq_empty_of_window` with `f ≥ -C e ^ (θ u)` on the windows in place of
`f ≥ 0`. -/
theorem ContinuesMero.eq_empty_of_window_ge {H : ℂ → ℂ} {Z : Set ℂ} {θ δ C : ℝ}
    (h : ContinuesMero f H Z A c θ) (hθ : 0 ≤ θ)
    (hneg : ∀ ρ ∈ Z, ρ.im = 0 → ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧ (g ρ).re < 0 ∧
      ∀ᶠ s in 𝓝[≠] ρ, H s = g s / (s - ρ) ^ (m + 1)) (hδ : 0 < δ)
    (hw : ∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + δ) * U), -(C * Real.exp (θ * u)) ≤ f u) : Z = ∅ := by
  by_contra hne
  obtain ⟨ρ₀, h₀⟩ := nonempty_iff_ne_empty.2 hne
  refine hne ((h.add_exp ((h.re_mem ρ₀ h₀).1.le.trans (h.re_mem ρ₀ h₀).2) C).eq_empty_of_window
    hθ (fun ρ hρ hi => ?_) hδ fun X => ?_)
  · obtain ⟨m, g, hg, hre, hH⟩ := hneg ρ hρ hi
    obtain ⟨g', hg', he, hH'⟩ := exists_pole_add C (h.re_mem ρ hρ).1 hg hH
    exact ⟨m, g', hg', he ▸ hre, hH'⟩
  · obtain ⟨U, hU, hu⟩ := hw X
    exact ⟨U, hU, fun u hu' => by linarith [hu u hu']⟩

/-- **Landau's theorem on windows.** If `f ≥ -C e ^ (θ u)` on arbitrarily late windows
`[U, (1 + δ) U]` and the residues of its Laplace transform at real poles have negative real part,
then the transform is analytic in `Re s > θ`. -/
theorem Continues.eq_empty_of_window {H κ : ℂ → ℂ} {Z : Set ℂ} {θ δ C : ℝ}
    (h : Continues f H Z κ A c θ) (hθ : 0 ≤ θ) (hκ : ∀ ρ ∈ Z, ρ.im = 0 → (κ ρ).re < 0) (hδ : 0 < δ)
    (hw : ∀ X, ∃ U ≥ X, ∀ u ∈ Icc U ((1 + δ) * U), -(C * Real.exp (θ * u)) ≤ f u) : Z = ∅ :=
  h.toMero.eq_empty_of_window_ge hθ (fun ρ hρ hi => by
    obtain ⟨g, hg, hgρ, hH⟩ := h.exists_pole hρ
    exact ⟨0, g, hg, hgρ ▸ hκ ρ hρ hi, hH⟩) hδ hw

end Masullo.Landau
