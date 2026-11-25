import Masullo.Window

/-!
# The dyadic window criterion

`dyadicSum X` is a sum of `Λ(n)` over `X / 4 < n < X` with a nonnegative continuous weight, and
`dyadicDiff X = dyadicSum (2 X) - 2 dyadicSum X`. Expressed in terms of `windowSum`, it is a
combination of four scales that cancels both `X` and `X log X`, so that no main term is
subtracted. A one-sided bound
`dyadicDiff X ≤ C X ^ θ`, or `- C X ^ θ ≤ dyadicDiff X`, on windows `[Y, Y ^ (1 + δ)]` with `Y`
arbitrarily large rules out zeros of zeta in `Re s > θ`. The implications are one-way: no converse
is stated, and neither bound is asserted for any `θ < 1`.

On the Laplace transform in `u = log (2 X)` the combination multiplies by `(1 - 2 ^ (-s)) (1 - 2 ^ (1 - s)) ^ 2`, which
has no zeros in `0 < Re s < 1` and is positive at real points there. The upper bound uses this sign;
the lower bound uses that zeta has no zeros in `(0, 1)`.
-/

open MeasureTheory Complex Set Filter Topology Metric
open ArithmeticFunction (vonMangoldt_nonneg)
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo.Landau.Continues

/-- `f u - a * f (u - log 2)` for `u > log 2`, and `f u` for `u ≤ log 2`. -/
noncomputable def delay (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  f u - a * (Ioi (Real.log 2)).indicator (fun u => f (u - Real.log 2)) u

lemma delay_of_lt (a : ℝ) (f : ℝ → ℝ) {u : ℝ} (hu : Real.log 2 < u) :
    delay a f u = f u - a * f (u - Real.log 2) := by
  rw [delay, indicator_of_mem (mem_Ioi.2 hu)]

/-- The multiplier of the transform under `delay a`. -/
noncomputable def factor (a : ℝ) (s : ℂ) : ℂ := 1 - a * cexp (-(s * Real.log 2))

lemma factor_ofReal (a x : ℝ) : factor a x = ((1 - a * Real.exp (-(x * Real.log 2)) : ℝ) : ℂ) := by
  simp [factor]

lemma factor_ne_zero {a : ℝ} {s : ℂ} (h : |a| * Real.exp (-(s.re * Real.log 2)) ≠ 1) :
    factor a s ≠ 0 := fun e => h (by
  have := (congrArg norm (sub_eq_zero.1 e)).symm
  rwa [norm_mul, norm_real, norm_exp, neg_re, re_mul_ofReal, Real.norm_eq_abs, norm_one] at this)

variable {f : ℝ → ℝ} {H κ : ℂ → ℂ} {Z : Set ℂ} {A c θ : ℝ}

/-- `delay a` multiplies the transform and its residues by `1 - a 2 ^ (-s)`, and preserves
`Continues` if this has no zeros in `Z`. -/
lemma delay_continues (h : Continues f H Z κ A c θ) (hc : 0 ≤ c) {a : ℝ}
    (ha : ∀ ρ ∈ Z, factor a ρ ≠ 0) : Continues (delay a f) (fun s => factor a s * H s) Z
      (fun ρ => factor a ρ * κ ρ) (A + |a| * A) c θ := by
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hA : 0 ≤ A := by simpa using (abs_nonneg _).trans (h.growth 0 le_rfl)
  have hfac (s : ℂ) : AnalyticAt ℂ (factor a) s := by
    unfold factor
    fun_prop
  set g := (Ioi (Real.log 2)).indicator fun u => f (u - Real.log 2)
  have hm : Measurable g :=
    (h.measurable.comp (measurable_id.sub_const _)).indicator measurableSet_Ioi
  have hg (u : ℝ) (hu : 0 ≤ u) : |g u| ≤ A * Real.exp (c * u) := by
    by_cases hu' : u ∈ Ioi (Real.log 2)
    · rw [show g u = f (u - Real.log 2) from indicator_of_mem hu' _]
      refine (h.growth _ (sub_nonneg.2 (mem_Ioi.1 hu').le)).trans ?_
      gcongr
      linarith
    · rw [show g u = 0 from indicator_of_notMem hu' _, abs_zero]
      positivity
  refine ⟨h.measurable.sub (hm.const_mul a), fun u hu => ?_, fun s hs => ?_,
    fun s hs hZ => (hfac s).mul (h.analytic s hs hZ), h.finite, h.re_mem,
    fun ρ hρ => mul_ne_zero (ha ρ hρ) (h.residue_ne_zero ρ hρ), fun ρ hρ => ?_⟩
  · refine (abs_sub _ _).trans ?_
    rw [abs_mul, add_mul, mul_assoc]
    exact add_le_add (h.growth u hu) (mul_le_mul_of_nonneg_left (hg u hu) (abs_nonneg a))
  · have i1 := integrable_kernel h.measurable h.growth 0 hs
    have i2 := integrable_kernel hm hg 0 hs
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at i1 i2
    have e : ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-(s * u)) =
        cexp (-(s * Real.log 2)) * H s := by
      simp_rw [g, ← ofRealHom_eq_coe, map_indicator, ofRealHom_eq_coe,
        ← indicator_mul_left _ _ (fun u : ℝ => cexp (-(s * u)))]
      rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi hL),
        h.laplace s hs, ← integral_const_mul,
        ← (measurePreserving_sub_right volume (Real.log 2)).setIntegral_preimage_emb
          (MeasurableEquiv.subRight _).measurableEmbedding _ (Ioi 0),
        preimage_sub_const_Ioi, zero_add]
      congr 1 with u
      rw [Function.comp_apply, ofRealHom_eq_coe, ofReal_sub, mul_left_comm, ← Complex.exp_add]
      ring_nf
    simp_rw [delay, Complex.ofReal_sub, Complex.ofReal_mul, sub_mul, mul_assoc]
    rw [integral_sub i1 (i2.const_mul _), integral_const_mul, e, ← h.laplace s hs, factor]
    ring
  · obtain ⟨k, hk, he⟩ := h.pole ρ hρ
    refine ⟨fun s => κ ρ * dslope (factor a) ρ s + factor a s * k s,
      (analyticAt_const.mul (Window.analyticAt_dslope (hfac ρ))).add ((hfac ρ).mul hk), ?_⟩
    filter_upwards [he, self_mem_nhdsWithin] with s hs hne
    have : s - ρ ≠ 0 := sub_ne_zero.2 hne
    rw [hs, dslope_of_ne _ hne, slope_def_field]
    field_simp
    ring

lemma const_mul (h : Continues f H Z κ A c θ) {b : ℝ} (hb : b ≠ 0) :
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

/-- `delay 1` and twice `delay 2`. -/
noncomputable def dyadic (f : ℝ → ℝ) : ℝ → ℝ := delay 2 (delay 2 (delay 1 f))

lemma dyadic_apply (f : ℝ → ℝ) {u : ℝ} (hu : 3 * Real.log 2 < u) :
    dyadic f u = f u - 5 * f (u - Real.log 2) + 8 * f (u - Real.log 2 - Real.log 2) -
      4 * f (u - Real.log 2 - Real.log 2 - Real.log 2) := by
  have hL := Real.log_pos one_lt_two
  rw [dyadic, delay_of_lt _ _ (by linarith), delay_of_lt _ _ (by linarith),
    delay_of_lt _ _ (by linarith), delay_of_lt _ _ (by linarith), delay_of_lt _ _ (by linarith),
    delay_of_lt _ _ (by linarith), delay_of_lt _ _ (by linarith)]
  ring

/-- The multiplier `(1 - 2 ^ (-s)) (1 - 2 ^ (1 - s)) ^ 2` at a real point. -/
noncomputable def gain (x : ℝ) : ℝ :=
  (1 - Real.exp (-(x * Real.log 2))) * (1 - 2 * Real.exp (-(x * Real.log 2))) ^ 2

lemma exp_bounds {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    Real.exp (-(x * Real.log 2)) < 1 ∧ 1 < 2 * Real.exp (-(x * Real.log 2)) := by
  have hL := Real.log_pos one_lt_two
  refine ⟨by rw [Real.exp_lt_one_iff]; nlinarith, ?_⟩
  rw [show 2 * Real.exp (-(x * Real.log 2)) = Real.exp (Real.log 2 - x * Real.log 2) by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log two_pos], Real.one_lt_exp_iff]
  nlinarith

lemma gain_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < gain x := by
  obtain ⟨h2, h3⟩ := exp_bounds h0 h1
  exact mul_pos (by linarith) (sq_pos_of_neg (by linarith))

lemma dyadic_continues (h : Continues f H Z κ A c θ) (hc : 0 ≤ c)
    (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1) : ∃ H' κ' A', Continues (dyadic f) H' Z κ' A' c θ ∧
      ∀ β : ℝ, κ' β = gain β * κ β := by
  have h1 ρ (hρ : ρ ∈ Z) : factor 1 ρ ≠ 0 := factor_ne_zero (by
    simpa using (exp_bounds (hZ ρ hρ).1 (hZ ρ hρ).2).1.ne)
  have h2 ρ (hρ : ρ ∈ Z) : factor 2 ρ ≠ 0 := factor_ne_zero (by
    simpa using (exp_bounds (hZ ρ hρ).1 (hZ ρ hρ).2).2.ne')
  refine ⟨_, _, _, ((h.delay_continues hc h1).delay_continues hc h2).delay_continues hc h2,
    fun β => ?_⟩
  simp only [factor_ofReal, gain]
  push_cast
  ring

end Masullo.Landau.Continues

namespace Masullo.Window

open Landau Landau.Continues Spectrum WeilExplicit

/-! ### The dyadic sums -/

/-- `max (1 / y - 1) 0`, for `y > 0`. -/
noncomputable def ramp (y : ℝ) : ℝ := max (1 / y - 1) 0

/-- `ramp y - 3 ramp (2 y) + 2 ramp (4 y)`: as a function of `1 / y`, a tent with base `[1, 4]` and
its vertex at `2`. -/
noncomputable def weight (y : ℝ) : ℝ := ramp y - 3 * ramp (2 * y) + 2 * ramp (4 * y)

lemma weight_eq (y : ℝ) : weight y = max (min (1 / y - 1) (2 - 1 / y / 2)) 0 := by
  have e (k : ℝ) : 1 / (k * y) = 1 / y / k := by rw [mul_comm, div_div]
  rw [weight, ramp, ramp, ramp, e, e]
  generalize 1 / y = t
  clear e
  rcases le_total t 1 with h | h <;> rcases le_total t 2 with h' | h' <;>
    rcases le_total t 4 with h'' | h'' <;> grind

lemma weight_nonneg (y : ℝ) : 0 ≤ weight y := weight_eq y ▸ le_max_right _ _

lemma weight_le_one (y : ℝ) : weight y ≤ 1 := by
  rw [weight_eq]
  grind

lemma weight_pos_iff {y : ℝ} (hy : 0 < y) : 0 < weight y ↔ 1 / 4 < y ∧ y < 1 := by
  rw [weight_eq, lt_max_iff, or_iff_left (lt_irrefl _), lt_min_iff, sub_pos, sub_pos,
    one_lt_div hy, div_div, div_lt_iff₀ (by positivity), and_comm]
  exact and_congr_left' ⟨fun h => by linarith, fun h => by linarith⟩

/-- `∑_{n ≤ X} Λ(n) weight (n / X)`. -/
noncomputable def dyadicSum (X : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n * weight (n / X)

/-- The difference of `dyadicSum` at two scales. -/
noncomputable def dyadicDiff (X : ℝ) : ℝ := dyadicSum (2 * X) - 2 * dyadicSum X

lemma sum_ramp {x k : ℝ} (hx : 0 < x) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * ramp (k * (n / x)) =
      ∑ n ∈ Finset.Icc 1 ⌊x / k⌋₊, Λ n * (x / k / n - 1) := by
  have hk0 : 0 < k := by linarith
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_mono (div_le_self hx.le hk)))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have h3 : (0 : ℝ) < n := by exact_mod_cast h1
    have h4 := (Nat.le_floor_iff (by positivity)).1 h2
    rw [ramp, show 1 / (k * (n / x)) = x / k / n by field_simp, max_eq_left]
    rwa [sub_nonneg, one_le_div h3]
  · intro n h1 h2
    have h3 : 1 ≤ n := (Finset.mem_Icc.1 h1).1
    have h4 : (0 : ℝ) < n := by exact_mod_cast h3
    have h5 : x / k < n := (Nat.floor_lt (by positivity)).1 (by simpa [h3] using h2)
    rw [ramp, show 1 / (k * (n / x)) = x / k / n by field_simp, max_eq_right, mul_zero]
    rw [sub_nonpos, div_le_one h4]
    exact h5.le

lemma dyadicSum_eq {x : ℝ} (hx : 0 < x) : dyadicSum x =
    windowSum x - 3 * windowSum (x / 2) + 2 * windowSum (x / 4) + x * Real.log 2 / 2 := by
  have h1 := sum_ramp hx le_rfl
  have h2 := sum_ramp hx one_le_two
  have h4 := sum_ramp hx (by norm_num : (1 : ℝ) ≤ 4)
  simp only [one_mul, div_one] at h1
  have e : dyadicSum x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * ramp (n / x) -
      3 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * ramp (2 * (n / x)) +
      2 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * ramp (4 * (n / x)) := by
    rw [dyadicSum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [weight]; ring
  rw [e, h1, h2, h4, windowSum, windowSum, windowSum, Real.log_div hx.ne' (by norm_num),
    Real.log_div hx.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The combination annihilates the main terms of `windowSum`. -/
lemma dyadicDiff_eq {x : ℝ} (hx : 0 < x) : dyadicDiff (4 * x) =
    windowSum (8 * x) - 5 * windowSum (4 * x) + 8 * windowSum (2 * x) - 4 * windowSum x := by
  rw [dyadicDiff, dyadicSum_eq (by positivity), dyadicSum_eq (by positivity)]
  ring_nf

/-! ### The criterion -/

/-- Zeta has no zeros in `(0, 1)`. -/
lemma riemannZeta_ofReal_ne_zero {b : ℝ} (hb : 0 < b) (h1 : b < 1) : riemannZeta (b : ℂ) ≠ 0 := by
  rw [zeta_eq_fractional_part_integral (by simpa) (by exact_mod_cast h1.ne)]
  have E : ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-(b : ℂ) - 1) * ((Int.fract x : ℝ) : ℂ) =
      ((∫ x : ℝ in Ioi 1, x ^ (-b - 1) * Int.fract x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    push_cast
    rw [ofReal_cpow (by linarith [mem_Ioi.1 hx] : 0 ≤ x)]
    push_cast
    rfl
  rw [E, ← ofReal_mul, ← ofReal_one, ← ofReal_sub, ← ofReal_div, ← ofReal_sub, ofReal_ne_zero]
  refine (sub_neg.2 ?_).ne
  exact (div_neg_of_pos_of_neg hb (by linarith)).trans_le (mul_nonneg hb.le
    (setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (mem_Ioi.1 hx).le) _) (Int.fract_nonneg x)))

/-- The sign of `ε` matters only if zeta has real zeros beyond `θ`. -/
lemma ne_zero_of_dyadic_window {θ δ C ε : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hε : ε ≠ 0)
    (hβ : ∀ β : ℝ, θ < β → β < 1 → riemannZeta β = 0 → 0 < ε)
    (h : ∀ X, ∃ Y ≥ X, 1 < Y ∧ ∀ x ∈ Icc Y (Y ^ (1 + δ)), ε * dyadicDiff x ≤ C * x ^ θ) {ρ : ℂ}
    (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  rcases le_or_gt 1 θ with hθ1 | hθ1
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hlt {z : ℂ} (hz : riemannZeta z = 0) : z.re < 1 :=
    not_le.1 fun hle => riemannZeta_ne_zero_of_one_le_re hle hz
  have hgain := gain_pos hθ hθ1
  set L := Real.log 2 with hLdef
  have hL : 0 < L := Real.log_pos one_lt_two
  set B := ε⁻¹ * C * Real.exp (-(L * θ)) / gain θ with hB
  obtain ⟨H, κ, A, hc, hκ⟩ := ((continues (C := B) hθ hθ1).dyadic_continues
    (by norm_num) fun ρ hρ => ⟨hθ.trans hρ.1, hlt hρ.2⟩)
  have hZ := (hc.const_mul hε).eq_empty_of_window (δ := δ / 2) hθ.le ?_ (by positivity) ?_
  · exact fun h0 => (hZ ▸ ⟨hρ, h0⟩ : ρ ∈ (∅ : Set ℂ)).elim
  · rintro ρ ⟨hr, hz⟩ hi
    lift ρ to ℝ using hi
    rw [re_ofReal_mul, hκ, re_ofReal_mul]
    exact mul_neg_of_pos_of_neg (hβ _ hr (hlt hz) hz) (mul_neg_of_pos_of_neg
      (gain_pos (hθ.trans hr) (hlt hz)) (residue_re_neg (hθ.trans hr) hz rfl))
  · intro X
    obtain ⟨Y, hY, hY1, hw⟩ := h (Real.exp (max X (3 * L)))
    have hY0 : 0 < Y := by linarith
    obtain ⟨hX, hL3⟩ := max_le_iff.1 ((Real.le_log_iff_exp_le hY0).2 hY)
    refine ⟨Real.log Y + L, by linarith, fun u hu => ?_⟩
    have hu1 : 3 * L < u := by linarith [hu.1]
    have hw1 := hw (Real.exp (u - L)) ⟨(Real.log_le_iff_le_exp hY0).1 (by linarith [hu.1]), by
      rw [Real.rpow_def_of_pos hY0]
      exact Real.exp_le_exp.2 (by nlinarith [hu.2])⟩
    have hd := dyadicDiff_eq (Real.exp_pos (u - L - L - L))
    have hb : B * gain θ = ε⁻¹ * C * Real.exp (-(θ * L)) := by
      rw [hB, div_mul_cancel₀ _ hgain.ne', mul_comm L]
    have hmain : dyadic (fun u => B * Real.exp (θ * u) - windowSum (Real.exp u)) u =
        ε⁻¹ * (C * Real.exp (u - L) ^ θ) - dyadicDiff (Real.exp (u - L)) := by
      rw [dyadic_apply _ hu1, ← hLdef, ← Real.exp_mul, mul_comm (u - L) θ]
      simp only [gain, ← hLdef, mul_sub, Real.exp_sub, Real.exp_neg,
        show Real.exp L = 2 from Real.exp_log two_pos] at hb hd ⊢
      ring_nf at hd ⊢
      linear_combination Real.exp (θ * u) * hb + hd
    rw [hmain, mul_sub, mul_inv_cancel_left₀ hε]
    linarith

/-- **Dyadic window criterion.** For fixed `θ > 0`, `δ > 0` and `C`, an upper bound `C x ^ θ` on
arbitrarily late windows `[Y, Y ^ (1 + δ)]` rules out zeros of zeta to the right of `θ`. The converse is not
asserted. -/
theorem riemannZeta_ne_zero_of_dyadicDiff_le {θ δ C : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (h : ∀ X, ∃ Y ≥ X, 1 < Y ∧ ∀ x ∈ Icc Y (Y ^ (1 + δ)), dyadicDiff x ≤ C * x ^ θ) {ρ : ℂ}
    (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 :=
  ne_zero_of_dyadic_window hθ hδ one_ne_zero (fun _ _ _ _ => one_pos) (by simpa using h) hρ

/-- For fixed `θ > 0`, `δ > 0` and `C`, a lower bound `- C x ^ θ` on arbitrarily late windows
`[Y, Y ^ (1 + δ)]` rules out zeros of zeta to the right of `θ`. The converse is not asserted. -/
theorem riemannZeta_ne_zero_of_le_dyadicDiff {θ δ C : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (h : ∀ X, ∃ Y ≥ X, 1 < Y ∧ ∀ x ∈ Icc Y (Y ^ (1 + δ)), -(C * x ^ θ) ≤ dyadicDiff x) {ρ : ℂ}
    (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 :=
  ne_zero_of_dyadic_window (ε := -1) hθ hδ (by norm_num)
    (fun _ h1 h2 h3 => (riemannZeta_ofReal_ne_zero (hθ.trans h1) h2 h3).elim)
    (by simpa [neg_le] using h) hρ

/-- The dyadic window bound with `θ < 1 / 2 + a` gives the trace identity of
`trace_eq_efFunctional_iff` at width `a`. The converse is not asserted. -/
theorem trace_eq_efFunctional_of_dyadicDiff_le {θ δ C a : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (ha : 0 < a)
    (hθa : θ - 1 / 2 < a)
    (h : ∀ X, ∃ Y ≥ X, 1 < Y ∧ ∀ x ∈ Icc Y (Y ^ (1 + δ)), dyadicDiff x ≤ C * x ^ θ)
    (φ : TestFunction) : Trace.HasTrace (Trace.induced ha φ) φ.efFunctional :=
  trace_eq_efFunctional_of_ne_zero ha hθa
    (fun _ => riemannZeta_ne_zero_of_dyadicDiff_le hθ hδ h) φ

/-- The lower dyadic window bound with `θ < 1 / 2 + a` gives the trace identity of
`trace_eq_efFunctional_iff` at width `a`. The converse is not asserted. -/
theorem trace_eq_efFunctional_of_le_dyadicDiff {θ δ C a : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (ha : 0 < a)
    (hθa : θ - 1 / 2 < a)
    (h : ∀ X, ∃ Y ≥ X, 1 < Y ∧ ∀ x ∈ Icc Y (Y ^ (1 + δ)), -(C * x ^ θ) ≤ dyadicDiff x)
    (φ : TestFunction) : Trace.HasTrace (Trace.induced ha φ) φ.efFunctional :=
  trace_eq_efFunctional_of_ne_zero ha hθa
    (fun _ => riemannZeta_ne_zero_of_le_dyadicDiff hθ hδ h) φ

end Masullo.Window
