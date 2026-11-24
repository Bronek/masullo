import WeilExplicit.ZeroCount
import WeilExplicit.Landau
import WeilExplicit.Spacing

/-! # Simultaneous good heights for the logarithmic derivative of zeta -/

namespace WeilExplicit

open Complex Metric Set Filter
open scoped Topology ComplexConjugate

private theorem norm_logDeriv_zeta_le_reg {s : ℂ} (ht : 1 ≤ |s.im|) (hn : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta s‖ ≤ ‖logDeriv riemannZeta₁ s‖ + 1 := by
  have h : s ≠ 1 := by intro h; norm_num [h] at ht
  have hreg := (logDeriv_congr_nhds
    ((eventually_ne_nhds h).mono fun _ hw ↦ zeta₁_eq_mul hw)).self_of_nhds
  rw [logDeriv_mul (f := fun z : ℂ ↦ z - 1) (g := riemannZeta) s (sub_ne_zero.mpr h) hn
    (by fun_prop) (differentiableAt_riemannZeta h)] at hreg
  have hnorm : 1 ≤ ‖s - 1‖ := ht.trans (by simpa using abs_im_le_norm (s - 1))
  have hterm : ‖logDeriv (fun z : ℂ ↦ z - 1) s‖ ≤ 1 := by
    simpa [logDeriv_apply] using inv_le_one_of_one_le₀ hnorm
  have := norm_sub_le (logDeriv riemannZeta₁ s) (logDeriv (fun z : ℂ ↦ z - 1) s)
  rw [hreg, add_sub_cancel_left] at this
  rw [hreg]
  exact this.trans (add_le_add le_rfl hterm)

/-- A separation δ from every zero in the counting disc bounds the polar sum by the total
multiplicity divided by δ. The outer-circle bound controls the analytic remainder. -/
theorem norm_logDeriv_zeta_of_separation {c s : ℂ} (Z : Finset ℂ)
    (hZ : ∀ a, a ∈ Z ↔ a ∈ closedBall c (5/3) ∧ riemannZeta a = 0)
    (hpole : 1 ∉ closedBall c (5/3)) (ht : 1 ≤ |s.im|) (hx : dist s c ≤ 8/5)
    {δ B : ℝ} (hδ : 0 < δ) (hsep : ∀ a ∈ Z, δ ≤ ‖s-a‖) (hB : 0 < B)
    (hbound : ∀ z ∈ sphere c (7/4), ‖riemannZeta₁ z‖ ≤ Real.exp B * ‖riemannZeta₁ c‖) :
    let N := ∑ a ∈ Z, (zeroMult a : ℝ)
    riemannZeta s ≠ 0 ∧
      ‖logDeriv riemannZeta s‖ ≤ N/δ + 3000*(B + N*Real.log 24) + 1 := by
  intro N
  have hn₁ {a : ℂ} (ha : a ∈ closedBall c (5/3)) : a ≠ 1 := ne_of_mem_of_not_mem ha hpole
  have hreg (a : ℂ) : a ∈ Z ↔ a ∈ closedBall c (5/3) ∧ riemannZeta₁ a = 0 := by
    rw [hZ]; apply and_congr_right; intro ha
    simp [zeta₁_eq_mul (hn₁ ha), sub_ne_zero.mpr (hn₁ ha)]
  have hsZ : s ∉ Z := fun hs ↦ hδ.not_ge (by simpa using hsep s hs)
  have hsn : riemannZeta s ≠ 0 := fun h ↦ hsZ ((hZ s).mpr ⟨mem_closedBall.mpr (by linarith), h⟩)
  have H := landau_disc differentiable_riemannZeta₁ Z hreg hB hbound hx hsZ
  have hm {a} (ha : a ∈ Z) : analyticOrderNatAt riemannZeta₁ a = zeroMult a := by
    simp [analyticOrderNatAt, zeroMult, zeta₁_order (hn₁ ((hZ a).mp ha).1)]
  simp only [Finset.sum_congr rfl (fun a ha ↦ congrArg ((↑) : ℕ → ℝ) (hm ha))] at H
  let P := ∑ a ∈ Z, (analyticOrderNatAt riemannZeta₁ a : ℂ) / (s-a)
  have hP : ‖P‖ ≤ N/δ := by
    apply (norm_sum_le ..).trans
    rw [show N/δ = ∑ a ∈ Z, (zeroMult a : ℝ)/δ from Finset.sum_div ..]
    apply Finset.sum_le_sum
    intro a ha
    rw [norm_div, Complex.norm_natCast, hm ha]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep a ha)
  change ‖logDeriv riemannZeta₁ s - P‖ ≤ 3000*(B + N*Real.log 24) at H
  exact ⟨hsn, by linarith [norm_logDeriv_zeta_le_reg ht hsn,
    norm_le_norm_sub_add (logDeriv riemannZeta₁ s) P]⟩

private theorem separated_window_bound : ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ), 7 ≤ j → ∀ (Z : Finset ℂ),
    (∀ a, a ∈ Z ↔ a ∈ closedBall (2 + ((j : ℝ) + 1/2 : ℝ)*I) (5/3) ∧ riemannZeta a = 0) →
    ∀ s : ℂ, j ≤ s.im → s.im ≤ j+1 → 1/2 ≤ s.re → s.re ≤ 2 →
      (∀ a ∈ Z, 1/(2*((Z.card:ℝ)+1)) ≤ |s.im-a.im|) →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C*Real.log ((j:ℝ)+3)^2 := by
  classical
  let K := 16 / Real.log (21/20)
  have hK : 0 < K := div_pos (by norm_num) (Real.log_pos (by norm_num))
  let C := 2*K*(K+1) + 3000*(6 + K*Real.log 24) + 1
  refine ⟨C, by dsimp [C]; positivity, fun j hj Z hZ s hT hT' ha hb hsep ↦ ?_⟩
  have hj' : 7 ≤ (j : ℝ) := by exact_mod_cast hj
  let L := Real.log ((j : ℝ) + 3)
  have hL : 1 ≤ L := (Real.le_log_iff_exp_le (by positivity)).mpr (by linarith [Real.exp_one_lt_d9])
  let t := (j : ℝ) + 1/2
  let c : ℂ := 2 + t * I
  have hat : |t| = t := abs_of_nonneg (by dsimp [t]; positivity)
  have hc : c.re = 2 := by simp [c]
  have him (z : ℂ) (hz : z ∈ closedBall c (5/3)) : 1 ≤ z.im := by
    have h := (abs_im_le_norm (z - c)).trans (mem_closedBall_iff_norm.mp hz)
    simp only [c, sub_im, add_im, mul_I_im, ofReal_re] at h
    norm_num at h
    dsimp [t] at h
    linarith [(abs_le.mp h).1]
  have hn₁ (z : ℂ) (hz : z ∈ closedBall c (5/3)) : z ≠ 1 := by
    intro h; have := him z hz; norm_num [h] at this
  let N := ∑ a ∈ Z, (zeroMult a : ℝ)
  have hN : N ≤ K * L := by
    have H := disc_zero_count t Z fun a ha ↦ ⟨((hZ a).mp ha).1, hn₁ a ((hZ a).mp ha).1⟩
    have hl : Real.log (|t|+3) ≤ 2*L := by
      rw [hat, show 2*L = Real.log (((j : ℝ)+3)^2) by simp [L, Real.log_pow]]
      apply Real.log_le_log (by dsimp [t]; positivity)
      dsimp [t]; nlinarith [sq_nonneg (j : ℝ)]
    apply H.trans
    dsimp [K]
    calc
      _ ≤ 8 / Real.log (21/20) * (2 * L) := by gcongr
      _ = _ := by ring
  have hcard : (Z.card : ℝ) ≤ N := by
    change _ ≤ ∑ a ∈ Z, _
    rw [show (Z.card : ℝ) = ∑ _a ∈ Z, (1 : ℝ) by simp]
    apply Finset.sum_le_sum
    intro a ha
    obtain ⟨hdisc, hz⟩ := (hZ a).mp ha
    have hr := (abs_re_le_norm (a - c)).trans (mem_closedBall_iff_norm.mp hdisc)
    rw [sub_re, hc] at hr
    have hstrip : a ∈ stripZeros := ⟨hz, by linarith [(abs_le.mp hr).1],
      lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩
    exact_mod_cast (zeroMult_pos hstrip : 1 ≤ zeroMult a)
  have hx : dist s c ≤ 8/5 := dist_window_center_le ha hb
    (abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩)
  have hδ (a : ℂ) (ha : a ∈ Z) : 1/(2*((Z.card : ℝ)+1)) ≤ ‖s-a‖ :=
    (hsep a ha).trans (by simpa [sub_im] using abs_im_le_norm (s-a))
  have hcen := one_third_le_norm_zeta₁ hc.ge
  have hB : ∀ z ∈ sphere c (7/4), ‖riemannZeta₁ z‖ ≤ Real.exp (6*L) * ‖riemannZeta₁ c‖ := by
    intro z hz
    apply (norm_zeta₁_on_disc t (sphere_subset_closedBall hz)).trans
    rw [show (6:ℝ)*L = Real.log (((j : ℝ)+3)^6) by simp [L, Real.log_pow],
      Real.exp_log (by positivity), hat]
    have hq : t+5 ≤ 2*((j : ℝ)+3) := by dsimp [t]; linarith
    have hp : 60 ≤ ((j : ℝ)+3)^4 := by
      nlinarith [show (10 : ℝ)^4 ≤ ((j : ℝ)+3)^4 by gcongr; linarith]
    have hpow : ((j : ℝ)+3)^6 = ((j : ℝ)+3)^2 * ((j : ℝ)+3)^4 := by ring
    rw [hpow]
    calc
      _ ≤ 5 * (2*((j : ℝ)+3))^2 := by gcongr
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg ((j : ℝ)+3)),
          mul_le_mul_of_nonneg_left hcen
            (show 0 ≤ ((j : ℝ)+3)^2 * ((j : ℝ)+3)^4 by positivity)]
  obtain ⟨hsn,hd⟩ := norm_logDeriv_zeta_of_separation Z hZ
    (fun hz ↦ hn₁ 1 hz rfl) (by linarith [le_abs_self s.im]) hx (by positivity) hδ
    (show 0 < 6*L by linarith) hB
  change ‖logDeriv riemannZeta s‖ ≤ N/(1/(2*((Z.card:ℝ)+1))) + 3000*(6*L+N*Real.log 24)+1 at hd
  simp only [one_div, div_inv_eq_mul] at hd
  have hlin : 6*L + N*Real.log 24 ≤ (6+K*Real.log 24)*L := by
    nlinarith [mul_le_mul_of_nonneg_right hN (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 24))]
  have hquad : N * (2*(Z.card+1 : ℝ)) ≤ (K*L)*(2*((K+1)*L)) := by
    gcongr; linarith
  refine ⟨hsn, ?_⟩
  dsimp [C]
  nlinarith only [hd, hlin, hquad, hL,
    mul_le_mul_of_nonneg_left (show L ≤ L^2 by nlinarith [sq_nonneg (L-1)])
      (show 0 ≤ 6+K*Real.log 24 by positivity),
    show 1 ≤ L^2 by nlinarith [sq_nonneg (L-1)]]

/-- Every unit interval above height seven contains a simultaneous good height
for the two horizontal segments. -/
theorem good_heights : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j → ∃ T : ℝ,
    j ≤ T ∧ T ≤ (j : ℝ) + 1 ∧ ∀ s : ℂ, |s.im| = T → 1/2 ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C * Real.log ((j : ℝ) + 3)^2 := by
  obtain ⟨C,hC,hbound⟩ := separated_window_bound
  refine ⟨C,hC,fun j hj ↦ ?_⟩
  let c : ℂ := 2 + ((j : ℝ) + 1/2 : ℝ)*I
  let Z := ((isCompact_closedBall c (5/3)).inter_riemannZetaZeros_finite).toFinset
  have hZ (a : ℂ) : a ∈ Z ↔ a ∈ closedBall c (5/3) ∧ riemannZeta a = 0 := by
    simp [Z, mem_riemannZetaZeros]
  obtain ⟨T, ⟨hT,hT'⟩, hsep⟩ := exists_separated_height Z Complex.im j
  refine ⟨T, hT, hT', fun s hs ha hb ↦ ?_⟩
  have upper (z : ℂ) (hz : z.im = T) := hbound j hj Z hZ z (hz ▸ hT) (hz ▸ hT')
  rcases le_or_gt 0 s.im with hp | hp
  · have e := (abs_of_nonneg hp).symm.trans hs
    exact upper s e ha hb (e ▸ hsep)
  · have e : (conj s).im = T := by simpa [abs_of_neg hp] using hs
    have h := upper (conj s) e ha hb (e ▸ hsep)
    simpa [riemannZeta_conj, logDeriv_conj riemannZeta_conj] using h

end WeilExplicit
