import Masullo.Runs

/-!
# From a one-sided mean of the second difference of `ψ` to a fixed-ratio window

Let `psiDiff x = ψ (2x) - 5 ψ x + 8 ψ (x/2) - 4 ψ (x/4)`, with `ψ` Chebyshev's function. For
`u, v ≥ 4`, `dyadicDiff v / v - dyadicDiff u / u` is the integral of `psiDiff x / x ^ 2` over
`[u, v]` (`dyadicDiff_div_sub`). This comes from Abel summation in the form
`∑_{n ≤ y} Λ(n) (1/n - 1/y) = ∫_1^y ψ t / t ^ 2` and a change of scale in each of the four terms.

So a bound `C Y ^ (1 + θ)` on the integral of the negative part of `psiDiff` over `[Y, 2Y]`
makes `dyadicDiff x / x` decrease by at most `C Y ^ (θ - 1)` across that interval. Split at
`m = √2 Y`. If `dyadicDiff m ≥ 0`, then `dyadicDiff ≥ -C' x ^ θ` on `[m, 2Y]`; otherwise
`dyadicDiff ≤ C' x ^ θ` on `[Y, m]`, with `C' = C / 2 ^ (θ - 1)`. Both windows have ratio `√2`.
The positive part works in the same way with the signs exchanged. For arbitrarily large `Y`
and `θ < 1` this is the hypothesis of `trace_width_of_bound` (`trace_width_of_mean`).
The mean bound holds at `θ = 1` (`Controls.mean_at_exponent_one`); it is not proved here for
any `θ < 1`.

OpenAI Codex proposed this passage from a one-sided mean to a window; Claude formalised it.
-/

open MeasureTheory (volume)
open Set intervalIntegral
open scoped ArithmeticFunction.vonMangoldt

namespace Masullo.Mean

open Window WeilExplicit

local notation "ψ" => Chebyshev.psi

/-- `ψ (2 x) - 5 ψ x + 8 ψ (x / 2) - 4 ψ (x / 4)`. -/
noncomputable def psiDiff (x : ℝ) : ℝ :=
  ψ (2 * x) - 5 * ψ x + 8 * ψ (x / 2) - 4 * ψ (x / 4)

/-- `∫_1^y ψ t / t ^ 2`. -/
noncomputable def psiInt (y : ℝ) : ℝ := ∫ t in 1..y, ψ t / t ^ 2

lemma intervalIntegrable_psi_comp {g : ℝ → ℝ} (hg : Monotone g) (a b : ℝ) :
    IntervalIntegrable (fun x => ψ (g x)) volume a b :=
  (Chebyshev.psi_mono.comp hg).intervalIntegrable

lemma intervalIntegrable_psiDiff (a b : ℝ) : IntervalIntegrable psiDiff volume a b :=
  (((intervalIntegrable_psi_comp (fun _ _ h => by linarith) a b).sub
    ((intervalIntegrable_psi_comp monotone_id a b).const_mul 5)).add
    ((intervalIntegrable_psi_comp (fun _ _ h => by linarith) a b).const_mul 8)).sub
    ((intervalIntegrable_psi_comp (fun _ _ h => by linarith) a b).const_mul 4)

lemma intervalIntegrable_div_sq {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable (fun x => f x / x ^ 2) volume a b := by
  simp_rw [div_eq_mul_inv]
  refine hf.mul_continuousOn ((continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 ?_)
  rcases mem_uIcc.1 hx with h | h <;> linarith [h.1]

lemma rampSum_eq {y : ℝ} (hy : 1 ≤ y) : rampSum y = y * psiInt y := by
  have hy0 : 0 < y := by linarith
  have hd : deriv (fun t : ℝ => t⁻¹) = fun t => -(t ^ 2)⁻¹ := deriv_inv'
  have A := sum_mul_eq_sub_integral_mul₀ (fun n => (Λ n : ℝ)) (f := fun t => t⁻¹) (by simp) y
    (fun t ht => differentiableAt_inv (by linarith [ht.1])) (by
      rw [hd]
      exact (((continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.1])).neg
        ).integrableOn_Icc)
  have hsub (g : ℕ → ℝ) (h0 : g 0 = 0) (N : ℕ) :
      ∑ n ∈ Finset.Icc 1 N, g n = ∑ n ∈ Finset.Icc 0 N, g n :=
    Finset.sum_subset (Finset.Icc_subset_Icc_left zero_le_one) fun n hn hn' => by
      obtain rfl : n = 0 := by simp only [Finset.mem_Icc] at hn hn'; omega
      exact h0
  simp_rw [hd, ← Chebyshev.psi_eq_sum_Icc, ← integral_of_le hy, neg_mul, integral_neg,
    sub_neg_eq_add] at A
  rw [← hsub _ (by simp)] at A
  have hint : ∫ t in 1..y, ψ t / t ^ 2 = ∫ t in 1..y, (t ^ 2)⁻¹ * ψ t :=
    integral_congr fun t _ => div_eq_inv_mul _ _
  have A' : ∫ t in 1..y, (t ^ 2)⁻¹ * ψ t =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℝ)⁻¹ * Λ n - y⁻¹ * ψ y := by linarith
  rw [rampSum, psiInt, hint, A', Chebyshev.psi_eq_sum_Icc, ← hsub _ (by simp), mul_sub,
    ← mul_assoc, mul_inv_cancel₀ hy0.ne', one_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  field_simp

/-- `dyadicDiff` is the same four-scale combination of `rampSum` as `psiDiff` is of `ψ`. -/
lemma dyadicDiff_eq_rampSum {x : ℝ} (hx : 0 < x) : dyadicDiff x =
    rampSum (2 * x) - 5 * rampSum x + 8 * rampSum (x / 2) - 4 * rampSum (x / 4) := by
  rw [dyadicDiff, dyadicSum_eq_rampSum (by positivity), dyadicSum_eq_rampSum hx,
    show 2 * x / 2 = x by ring, show 2 * x / 4 = x / 2 by ring]
  ring

lemma dyadicDiff_div {x : ℝ} (hx : 4 ≤ x) : dyadicDiff x / x =
    2 * psiInt (2 * x) - 5 * psiInt x + 4 * psiInt (x / 2) - psiInt (x / 4) := by
  have hx0 : 0 < x := by linarith
  rw [dyadicDiff_eq_rampSum hx0, rampSum_eq (by linarith), rampSum_eq (by linarith),
    rampSum_eq (by linarith), rampSum_eq (by linarith)]
  field_simp
  ring

lemma mul_psiInt_sub {c u v : ℝ} (hc : 0 < c) (hu : 0 < u) (hv : 0 < v) :
    c * (psiInt (c * v) - psiInt (c * u)) = ∫ s in u..v, ψ (c * s) / s ^ 2 := by
  have hi {y : ℝ} (hy : 0 < y) : IntervalIntegrable (fun t => ψ t / t ^ 2) volume 1 y :=
    intervalIntegrable_div_sq (intervalIntegrable_psi_comp monotone_id 1 y) one_pos hy
  have e : (fun s => ψ (c * s) / s ^ 2) = fun s => c ^ 2 * (ψ (c * s) / (c * s) ^ 2) := by
    funext s
    rw [mul_pow, mul_div_assoc', mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')]
  have hc' := integral_comp_mul_left (a := u) (b := v) (fun t => ψ t / t ^ 2) hc.ne'
  rw [psiInt, psiInt, integral_interval_sub_left (hi (by positivity)) (hi (by positivity)), e,
    integral_const_mul, hc', smul_eq_mul]
  field_simp

/-- `dyadicDiff x / x` has density `psiDiff x / x ^ 2`. -/
lemma dyadicDiff_div_sub {u v : ℝ} (hu : 4 ≤ u) (hv : 4 ≤ v) :
    dyadicDiff v / v - dyadicDiff u / u = ∫ s in u..v, psiDiff s / s ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hI (c : ℝ) (hc : 0 ≤ c) : IntervalIntegrable (fun s => ψ (c * s) / s ^ 2) volume u v :=
    intervalIntegrable_div_sq (intervalIntegrable_psi_comp
      (fun _ _ h => mul_le_mul_of_nonneg_left h hc) u v) hu0 hv0
  have hpt (s : ℝ) : psiDiff s / s ^ 2 = ψ (2 * s) / s ^ 2 - 5 * (ψ (1 * s) / s ^ 2) +
      8 * (ψ (2⁻¹ * s) / s ^ 2) - 4 * (ψ (4⁻¹ * s) / s ^ 2) := by
    rw [psiDiff, one_mul, ← div_eq_inv_mul, ← div_eq_inv_mul]
    ring
  simp_rw [hpt]
  rw [integral_sub (((hI 2 (by norm_num)).sub ((hI 1 (by norm_num)).const_mul 5)).add
      ((hI 2⁻¹ (by norm_num)).const_mul 8)) ((hI 4⁻¹ (by norm_num)).const_mul 4),
    integral_add ((hI 2 (by norm_num)).sub ((hI 1 (by norm_num)).const_mul 5))
      ((hI 2⁻¹ (by norm_num)).const_mul 8),
    integral_sub (hI 2 (by norm_num)) ((hI 1 (by norm_num)).const_mul 5),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← mul_psiInt_sub two_pos hu0 hv0, ← mul_psiInt_sub one_pos hu0 hv0,
    ← mul_psiInt_sub (by norm_num) hu0 hv0, ← mul_psiInt_sub (by norm_num) hu0 hv0,
    dyadicDiff_div hu, dyadicDiff_div hv]
  simp only [one_mul, div_eq_inv_mul]
  ring

/-- Across `[Y, 2Y]`, `ε dyadicDiff x / x` decreases by at most the mean of the negative part of
`ε psiDiff`, scaled by `1 / Y ^ 2`. -/
lemma le_mul_sub {ε Y u v : ℝ} (hY : 4 ≤ Y) (hu : Y ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * Y) :
    -((∫ x in Y..2 * Y, max (-(ε * psiDiff x)) 0) / Y ^ 2) ≤
      ε * (dyadicDiff v / v - dyadicDiff u / u) := by
  have hY0 : 0 < Y := by linarith
  have hg (a b : ℝ) :
      IntervalIntegrable (fun x => max (-(ε * psiDiff x)) 0) volume a b := by
    have h := ((intervalIntegrable_psiDiff a b).const_mul ε).neg
    exact ⟨h.1.pos_part, h.2.pos_part⟩
  rw [dyadicDiff_div_sub (by linarith) (by linarith), ← integral_const_mul]
  calc -((∫ x in Y..2 * Y, max (-(ε * psiDiff x)) 0) / Y ^ 2)
      ≤ -((∫ x in u..v, max (-(ε * psiDiff x)) 0) / Y ^ 2) := by
        gcongr
        exact integral_mono_interval hu huv hv
          (.of_forall fun _ => le_max_right _ _) (hg _ _)
    _ = ∫ x in u..v, -(max (-(ε * psiDiff x)) 0 / Y ^ 2) := by
        rw [integral_neg, integral_div]
    _ ≤ ∫ x in u..v, ε * (psiDiff x / x ^ 2) := by
        refine integral_mono_on huv ((hg u v).div_const _).neg
          ((intervalIntegrable_div_sq (intervalIntegrable_psiDiff u v) (by linarith)
            (by linarith)).const_mul ε) fun x hx => ?_
        have hx2 : Y ^ 2 ≤ x ^ 2 := by gcongr; linarith [hx.1]
        have h1 : max (-(ε * psiDiff x)) 0 / x ^ 2 ≤ max (-(ε * psiDiff x)) 0 / Y ^ 2 :=
          div_le_div_of_nonneg_left (le_max_right _ _) (by positivity) hx2
        have h2 : -max (-(ε * psiDiff x)) 0 / x ^ 2 ≤ ε * psiDiff x / x ^ 2 :=
          div_le_div_of_nonneg_right (neg_le.1 (le_max_left _ _)) (sq_nonneg x)
        rw [neg_div] at h2
        rw [← mul_div_assoc]
        linarith

lemma mul_div_le_rpow {θ C Y x : ℝ} (hθ : θ ≤ 1) (hC : 0 ≤ C) (hY : 0 < Y) (hx : Y ≤ x)
    (hx2 : x ≤ 2 * Y) : x * (C * Y ^ (1 + θ) / Y ^ 2) ≤ C / 2 ^ (θ - 1) * x ^ θ := by
  have hx0 : 0 < x := hY.trans_le hx
  have e : Y ^ (1 + θ) / Y ^ 2 = Y ^ (θ - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hY]
    norm_num
    ring_nf
  have h : Y ^ (θ - 1) ≤ (x / 2) ^ (θ - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  rw [Real.div_rpow hx0.le zero_le_two, Real.rpow_sub_one hx0.ne'] at h
  rw [mul_div_assoc, e]
  calc x * (C * Y ^ (θ - 1)) = C * (x * Y ^ (θ - 1)) := by ring
    _ ≤ C * (x * (x ^ θ / x / 2 ^ (θ - 1))) := by gcongr
    _ = C / 2 ^ (θ - 1) * x ^ θ := by field_simp

/-- A bound `C Y ^ (1 + θ)` on the integral over `[Y, 2Y]` of the negative part of `ε psiDiff`
bounds `ε dyadicDiff` below by `-C' x ^ θ` on `[√2 Y, 2Y]` or above by `C' x ^ θ` on `[Y, √2 Y]`,
with `C' = C / 2 ^ (θ - 1)`. -/
lemma window_of_mean {ε θ C Y : ℝ} (hθ : θ < 1) (hY : 4 ≤ Y)
    (h : (∫ x in Y..2 * Y, max (-(ε * psiDiff x)) 0) ≤ C * Y ^ (1 + θ)) :
    (∀ x ∈ Icc (√2 * Y) (√2 * (√2 * Y)), -(C / 2 ^ (θ - 1) * x ^ θ) ≤ ε * dyadicDiff x) ∨
      ∀ x ∈ Icc Y (√2 * Y), ε * dyadicDiff x ≤ C / 2 ^ (θ - 1) * x ^ θ := by
  have hY0 : 0 < Y := by linarith
  set I := ∫ x in Y..2 * Y, max (-(ε * psiDiff x)) 0
  have hI : 0 ≤ I := integral_nonneg (by linarith) fun _ _ => le_max_right _ _
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (by positivity)).1 (hI.trans h)
  have hK {x : ℝ} (hx : Y ≤ x) (hx2 : x ≤ 2 * Y) : x * (I / Y ^ 2) ≤ C / 2 ^ (θ - 1) * x ^ θ :=
    (mul_le_mul_of_nonneg_left (by gcongr) (by linarith)).trans
      (mul_div_le_rpow hθ.le hC hY0 hx hx2)
  have hs := Real.sq_sqrt zero_le_two
  have hs1 := Real.one_lt_sqrt_two
  have hm1 : Y ≤ √2 * Y := by nlinarith
  have hm2 : √2 * Y ≤ 2 * Y := by nlinarith
  have hmm : √2 * (√2 * Y) = 2 * Y := by rw [← mul_assoc, ← sq, hs]
  have hD {x : ℝ} (hx : Y ≤ x) : ε * dyadicDiff x = x * (ε * (dyadicDiff x / x)) := by
    field_simp [(hY0.trans_le hx).ne']
  by_cases hm : 0 ≤ ε * (dyadicDiff (√2 * Y) / (√2 * Y))
  · refine .inl fun x hx => ?_
    have hx1 : Y ≤ x := hm1.trans hx.1
    have h1 := le_mul_sub (ε := ε) hY hm1 hx.1 (hmm ▸ hx.2)
    rw [hD hx1]
    nlinarith [hK hx1 (hmm ▸ hx.2)]
  · refine .inr fun x hx => ?_
    have h1 := le_mul_sub (ε := ε) hY hx.1 hx.2 hm2
    rw [hD hx.1]
    nlinarith [hK hx.1 (hx.2.trans hm2), hY0.trans_le hx.1]

/-- If, for one exponent `θ < 1` and arbitrarily large `Y`, the integral over `[Y, 2Y]` of the
negative part of `psiDiff`, or of its positive part, is at most `C Y ^ (1 + θ)`, the trace
identity holds for all tests at some positive width below `1/2`. The hypothesis normalises the
mean over `[Y, 2Y]` as `C Y ^ θ`, matching the pointwise exponent of `trace_width_of_bound`; the
sign may depend on `Y`. -/
theorem trace_width_of_mean {θ C : ℝ} (hθ : θ < 1)
    (h : ∀ Y₀, ∃ Y ≥ Y₀, (∫ x in Y..2 * Y, max (-psiDiff x) 0) ≤ C * Y ^ (1 + θ) ∨
      (∫ x in Y..2 * Y, max (psiDiff x) 0) ≤ C * Y ^ (1 + θ)) :
    ∃ a, ∃ ha : 0 < a, a < 1 / 2 ∧
      ∀ φ : TestFunction, Trace.HasTrace (Trace.induced ha φ) φ.efFunctional := by
  refine Runs.trace_width_of_bound Real.one_lt_sqrt_two hθ (C := C / 2 ^ (θ - 1)) fun Y₀ => ?_
  obtain ⟨Y, hY, hI⟩ := h (max Y₀ 4)
  have hY4 := le_of_max_le_right hY
  have hY₀ := le_of_max_le_left hY
  have hm1 : Y ≤ √2 * Y := by nlinarith [Real.one_lt_sqrt_two]
  rcases hI with hI | hI
  · rcases window_of_mean (ε := 1) hθ hY4 (by simpa using hI) with hw | hw
    · exact ⟨_, hY₀.trans hm1, .inl fun x hx => by linarith [hw x hx]⟩
    · exact ⟨Y, hY₀, .inr fun x hx => by linarith [hw x hx]⟩
  · rcases window_of_mean (ε := -1) hθ hY4 (by simpa using hI) with hw | hw
    · exact ⟨_, hY₀.trans hm1, .inr fun x hx => by linarith [hw x hx]⟩
    · exact ⟨Y, hY₀, .inl fun x hx => by linarith [hw x hx]⟩

namespace Controls

/-- The mean hypothesis of `trace_width_of_mean` holds at `θ = 1`, by Chebyshev's bound, for
the negative part at every `Y ≥ 1`; so it carries information only through `θ < 1`. -/
theorem mean_at_exponent_one : ∀ Y₀, ∃ Y ≥ Y₀,
    (∫ x in Y..2 * Y, max (-psiDiff x) 0) ≤ 18 * (Real.log 4 + 4) * Y ^ (1 + 1 : ℝ) ∨
      (∫ x in Y..2 * Y, max (psiDiff x) 0) ≤ 18 * (Real.log 4 + 4) * Y ^ (1 + 1 : ℝ) := by
  intro Y₀
  set Y := max Y₀ 1
  have hY : 1 ≤ Y := le_max_right _ _
  have hL : 0 < Real.log 4 + 4 := by positivity
  refine ⟨Y, le_max_left _ _, .inl ?_⟩
  have hg := (intervalIntegrable_psiDiff Y (2 * Y)).neg
  calc (∫ x in Y..2 * Y, max (-psiDiff x) 0)
      ≤ ∫ _ in Y..2 * Y, 18 * (Real.log 4 + 4) * Y := by
        refine integral_mono_on (by linarith) ⟨hg.1.pos_part, hg.2.pos_part⟩
          intervalIntegrable_const fun x hx => max_le ?_ (by positivity)
        have h1 := Chebyshev.psi_le_const_mul_self (x := x) (by linarith [hx.1])
        have h2 := Chebyshev.psi_mono (show x / 4 ≤ x by linarith [hx.1])
        have := Chebyshev.psi_nonneg (2 * x)
        have := Chebyshev.psi_nonneg (x / 2)
        rw [psiDiff]
        nlinarith [hx.2]
    _ = 18 * (Real.log 4 + 4) * Y ^ (1 + 1 : ℝ) := by
        rw [integral_const, smul_eq_mul, show (1 + 1 : ℝ) = 2 by norm_num, Real.rpow_two]
        ring

end Controls

end Masullo.Mean
