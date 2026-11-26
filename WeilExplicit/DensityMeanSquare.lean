import WeilExplicit.DensityFourier
import WeilExplicit.DensityMollifier
import WeilExplicit.DensityTail

/-!
# Mean square of the mollified zeta function

Fix `0 < δ ≤ 1/8`. At height `T ≥ 2` take `U = ⌊T^{δ/3}⌋` and `X = ⌊T^{1-δ/3}⌋`, and put
`mollified δ T s = ζ(s) M_U(s) - 1`. On every vertical line `1/2 + δ ≤ Re s ≤ 2` the integral of
`|mollified δ T s|²` over `T - 1 ≤ Im s ≤ 2T + 1` is `O(T^{1-δ²/3})`.

Part of a Carlson-type mean-square zero-density argument due to OpenAI Codex (E36),
formalised by Claude.
-/

namespace WeilExplicit

open Complex MeasureTheory Set Real

theorem continuous_fourier {g : ℝ → ℂ} (hm : Measurable g) (hg : Integrable g) :
    Continuous fun t : ℝ ↦ ∫ v, g v * cexp (-(v * t) * I) := by
  refine continuous_of_dominated (bound := fun v ↦ ‖g v‖)
    (fun t ↦ (hm.mul (by fun_prop)).aestronglyMeasurable) (fun t ↦ .of_forall fun v ↦ ?_)
    hg.norm (.of_forall fun v ↦ by fun_prop)
  rw [norm_mul, show -((v : ℂ) * t) = ((-(v * t) : ℝ) : ℂ) by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]

theorem natCast_cpow_line {n : ℕ} (hn : 1 ≤ n) (u t : ℝ) :
    (n : ℂ) ^ (-(u + t * I)) = ((n : ℝ) ^ (-u) : ℝ) * cexp (-(Real.log n * t) * I) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cpow_def_of_ne_zero (by exact_mod_cast hn0.ne'), Real.rpow_def_of_pos hn0, ofReal_exp,
    ← Complex.exp_add, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← ofReal_log hn0.le]
  congr 1; push_cast; ring

theorem norm_mollifier_le (U : ℕ) {s : ℂ} (hs : 0 ≤ s.re) : ‖mollifier U s‖ ≤ U := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Finset.Icc 1 U, ‖(ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s)‖
      ≤ ∑ d ∈ Finset.Icc 1 U, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d hd ↦ ?_
        have hd1 := (Finset.mem_Icc.mp hd).1
        rw [norm_mul, Complex.norm_intCast, norm_natCast_cpow_of_pos (by omega)]
        have h1 : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have h2 : (d : ℝ) ^ (-s).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by simpa using hs)
        exact mul_le_one₀ h1 (by positivity) h2
    _ = U := by simp

theorem floor_rpow_bounds {T : ℝ} (hT : 1 ≤ T) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ ⌊T ^ e⌋₊ ∧ (⌊T ^ e⌋₊ : ℝ) ≤ T ^ e ∧ T ^ e / 2 ≤ ⌊T ^ e⌋₊ := by
  have h1 : 1 ≤ T ^ e := Real.one_le_rpow hT he
  have hf1 : 1 ≤ ⌊T ^ e⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  refine ⟨hf1, Nat.floor_le (by linarith), ?_⟩
  have := Nat.lt_floor_add_one (T ^ e)
  have : (1 : ℝ) ≤ ⌊T ^ e⌋₊ := by exact_mod_cast hf1
  linarith

/-- The mollifier length at height `T`. -/
noncomputable def densU (δ T : ℝ) : ℕ := ⌊T ^ (δ / 3)⌋₊

/-- The truncation point of the Dirichlet series at height `T`. -/
noncomputable def densX (δ T : ℝ) : ℕ := ⌊T ^ (1 - δ / 3)⌋₊

/-- The mollified zeta function minus one. -/
noncomputable def mollified (δ T : ℝ) (s : ℂ) : ℂ := riemannZeta s * mollifier (densU δ T) s - 1

private theorem dens_bounds {δ T : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) (hT : 1 ≤ T) :
    1 ≤ densU δ T ∧ densU δ T ≤ densX δ T ∧ (densU δ T : ℝ) ≤ T ^ (δ / 3) ∧
      T ^ (δ / 3) / 2 ≤ densU δ T ∧ (densX δ T : ℝ) ≤ T ^ (1 - δ / 3) ∧
      T ^ (1 - δ / 3) / 2 ≤ densX δ T ∧ ((densU δ T * densX δ T : ℕ) : ℝ) ≤ T := by
  obtain ⟨hU1, hU2, hU3⟩ := floor_rpow_bounds hT (by positivity : 0 ≤ δ / 3)
  obtain ⟨-, hX2, hX3⟩ := floor_rpow_bounds hT (by linarith : 0 ≤ 1 - δ / 3)
  refine ⟨hU1, Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hT (by linarith)), hU2, hU3,
    hX2, hX3, ?_⟩
  push_cast
  calc (densU δ T : ℝ) * densX δ T ≤ T ^ (δ / 3) * T ^ (1 - δ / 3) :=
        mul_le_mul hU2 hX2 (Nat.cast_nonneg _) (by positivity)
    _ = T := by rw [← Real.rpow_add (by linarith)]; norm_num

private theorem rpow_U_le {δ T : ℝ} (hδ : 0 < δ) (hT : 1 ≤ T) {U : ℝ}
    (hU : T ^ (δ / 3) / 2 ≤ U) : U ^ (-δ) ≤ 2 ^ δ * T ^ (-(δ ^ 2 / 3)) := by
  have hpos : 0 < T ^ (δ / 3) / 2 := by positivity
  refine (Real.rpow_le_rpow_of_nonpos hpos hU (by linarith)).trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul (by linarith),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  ring_nf

/-- The mean square of the mollified Dirichlet polynomial. -/
theorem mean_square_poly {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    ∃ C, ∀ T : ℝ, 2 ≤ T → ∀ u : ℝ, 1 / 2 + δ ≤ u →
      ∫ t in Icc (T - 1) (2 * T + 1), ‖partialZeta (densX δ T) (u + t * I) *
        mollifier (densU δ T) (u + t * I) - 1‖ ^ 2 ≤ C * T ^ (1 - δ ^ 2 / 3) := by
  refine ⟨24 * π * divisorConst δ * 2 ^ δ, fun T hT u hu ↦ ?_⟩
  obtain ⟨hU1, hUX, -, hU3, -, -, hK⟩ := dens_bounds hδ hδ' (by linarith : (1 : ℝ) ≤ T)
  set U := densU δ T
  set X := densX δ T
  have hX1 : 1 ≤ X := hU1.trans hUX
  set b : ℕ → ℂ := fun n ↦ mollCoeff U X n * ((n : ℝ) ^ (-u) : ℝ)
  set D : ℝ → ℂ := fun t ↦ ∑ n ∈ Finset.Icc 1 (U * X), b n * cexp (-(Real.log n * t) * I)
  have hD : ∀ t : ℝ, partialZeta X (u + t * I) * mollifier U (u + t * I) - 1 = D t := by
    intro t
    rw [partialZeta_mul_mollifier_sub_one hU1 hX1]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [natCast_cpow_line (Finset.mem_Icc.mp hn).1]
    simp only [b]; ring
  simp_rw [hD]
  have hb2 : ∀ n ∈ Finset.Icc 1 (U * X),
      ‖b n‖ ^ 2 = ‖mollCoeff U X n‖ ^ 2 * (n : ℝ) ^ (-(2 * u)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    simp only [b]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
      sq ((n : ℝ) ^ (-u)), ← Real.rpow_add hn0]
    ring_nf
  have hsum := sum_mollCoeff_sq_le hU1 hUX hδ hu
  have hUδ := rpow_U_le hδ (by linarith) hU3
  have hDC : 0 ≤ divisorConst δ := by unfold divisorConst; positivity

  calc ∫ t in Icc (T - 1) (2 * T + 1), ‖D t‖ ^ 2
      ≤ 24 * π * T * ∑ n ∈ Finset.Icc 1 (U * X), ‖b n‖^2 := dir_mean _ b hT hK
    _ ≤ 24 * π * T * (2 ^ δ * T ^ (-(δ^2/3)) * divisorConst δ) := by
        rw [Finset.sum_congr rfl hb2]
        gcongr
        exact hsum.trans (mul_le_mul_of_nonneg_right hUδ hDC)
    _ = _ := by
        rw [show 1 - δ ^ 2 / 3 = 1 + -(δ ^ 2 / 3) by ring, Real.rpow_add (by linarith),
          Real.rpow_one]
        ring

theorem continuous_partialZeta_line (X : ℕ) (u : ℝ) :
    Continuous fun t : ℝ ↦ partialZeta X (u + t * I) := by
  unfold partialZeta
  refine continuous_finsetSum _ fun n hn ↦ (by fun_prop : Continuous fun t : ℝ ↦
    -((u : ℂ) + t * I)).const_cpow (Or.inl ?_)
  have := (Finset.mem_Icc.mp hn).1
  exact_mod_cast (by omega : n ≠ 0)

theorem continuous_mollifier_line (U : ℕ) (u : ℝ) :
    Continuous fun t : ℝ ↦ mollifier U (u + t * I) := by
  unfold mollifier
  refine continuous_finsetSum _ fun n hn ↦ continuous_const.mul ((by fun_prop :
    Continuous fun t : ℝ ↦ -((u : ℂ) + t * I)).const_cpow (Or.inl ?_))
  have := (Finset.mem_Icc.mp hn).1
  exact_mod_cast (by omega : n ≠ 0)

/-- The mean square of `ζ M_U - 1` on a vertical line, as a lower Lebesgue integral. -/
theorem mean_square_mollified {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    ∃ C, ∀ T : ℝ, 2 ≤ T → ∀ u : ℝ, 1 / 2 + δ ≤ u → u ≤ 2 →
      ∫⁻ t in Icc (T - 1) (2 * T + 1), ‖mollified δ T (u + t * I)‖ₑ ^ 2 ≤
        ENNReal.ofReal (C * T ^ (1 - δ ^ 2 / 3)) := by
  obtain ⟨C1, hC1⟩ := mean_square_poly hδ hδ'
  refine ⟨3 * (C1 + 8 + 32 * π * 2 ^ (1 + 2 * δ)), fun T hT u hu hu2 ↦ ?_⟩
  obtain ⟨hU1, hUX, hU2, -, hX2, hX3, -⟩ := dens_bounds hδ hδ' (by linarith : (1 : ℝ) ≤ T)
  set U := densU δ T
  set X := densX δ T
  have hX1 : 1 ≤ X := hU1.trans hUX
  have hX1' : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < u := by linarith
  set P : ℝ → ℂ := fun t ↦ mollifier U (u + t * I)
  set A : ℝ → ℂ := fun t ↦ partialZeta X (u + t * I) * P t - 1
  set G : ℝ → ℂ := fun t ↦ ∫ v, tailFun X u v * cexp (-(v * t) * I)
  set e2 := δ / 3 + (1 - δ / 3) * (1 / 2 - δ) - 1
  set e3 := 2 * δ / 3 + 2
  have hTe3 : T ^ e3 = (T ^ (δ / 3)) ^ 2 * T ^ 2 := by
    rw [show e3 = δ / 3 * 2 + 2 by ring, Real.rpow_add hT0, Real.rpow_mul hT0.le,
      Real.rpow_two, Real.rpow_two]
  have hpt : ∀ t ∈ Icc (T - 1) (2 * T + 1), ‖mollified δ T (u + t * I)‖ ^ 2 ≤
      3 * (‖A t‖ ^ 2 + (2 * T ^ e2) ^ 2 + 16 * T ^ e3 * ‖G t‖ ^ 2) := by
    intro t ht
    have ht1 : T / 2 ≤ t := by linarith [ht.1]
    have hs1 : (u : ℂ) + t * I ≠ 1 := fun h ↦ by
      have := congrArg Complex.im h; simp at this; linarith
    have hdec : mollified δ T (u + t * I) = A t +
        P t * ((X : ℂ) ^ (1 - (u + t * I)) / ((u + t * I) - 1)) - P t * (u + t * I) * G t := by
      simp only [mollified, A, P, G]
      rw [zeta_eq_partial_sum (by simp; linarith) hs1 X hX1,
        tail_eq_fourier (by positivity : (0 : ℝ) < X) u t]
      unfold partialZeta; ring
    have hP : ‖P t‖ ≤ T ^ (δ / 3) := (norm_mollifier_le U (by simp; linarith)).trans hU2
    have hb : ‖P t * ((X : ℂ) ^ (1 - (u + t * I)) / ((u + t * I) - 1))‖ ≤ 2 * T ^ e2 := by
      have hn : ‖(X : ℂ) ^ (1 - (u + t * I))‖ ≤ T ^ ((1 - δ / 3) * (1 / 2 - δ)) := by
        rw [norm_natCast_cpow_of_pos (by omega)]
        simp only [sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero]
        calc (X : ℝ) ^ (1 - u) ≤ (X : ℝ) ^ (1 / 2 - δ) :=
              Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)
          _ ≤ (T ^ (1 - δ / 3)) ^ (1 / 2 - δ) :=
              Real.rpow_le_rpow (by positivity) hX2 (by linarith)
          _ = _ := by rw [← Real.rpow_mul hT0.le]
      have hd : T / 2 ≤ ‖(u + t * I : ℂ) - 1‖ := by
        refine ht1.trans (le_trans (le_of_eq ?_) (abs_im_le_norm _))
        simp; rw [abs_of_pos (by linarith)]
      rw [norm_mul, norm_div]
      calc ‖P t‖ * (‖(X : ℂ) ^ (1 - (u + t * I))‖ / ‖(u + t * I : ℂ) - 1‖)
          ≤ T ^ (δ / 3) * (T ^ ((1 - δ / 3) * (1 / 2 - δ)) / (T / 2)) := by
            gcongr
        _ = 2 * T ^ e2 := by
            rw [show e2 = δ / 3 + (1 - δ / 3) * (1 / 2 - δ) + (-1) by ring,
              Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_neg_one]
            field_simp
    have hc : ‖P t * (u + t * I) * G t‖ ^ 2 ≤ 16 * T ^ e3 * ‖G t‖ ^ 2 := by
      have hs : ‖(u + t * I : ℂ)‖ ≤ 4 * T := by
        refine (norm_le_abs_re_add_abs_im _).trans ?_
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, mul_im, zero_add]
        rw [abs_of_pos hu0, abs_of_pos (by linarith)]
        linarith [ht.2]
      rw [norm_mul, norm_mul, hTe3]
      have := mul_le_mul hP hs (norm_nonneg _) (by positivity)
      have h0 : 0 ≤ ‖P t‖ * ‖(u + t * I : ℂ)‖ := by positivity
      have := pow_le_pow_left₀ h0 this 2
      nlinarith [sq_nonneg ‖G t‖]
    rw [hdec]
    have h1 := norm_sub_le (A t + P t * ((X : ℂ) ^ (1 - (u + t * I)) / ((u + t * I) - 1)))
      (P t * (u + t * I) * G t)
    have h2 := norm_add_le (A t) (P t * ((X : ℂ) ^ (1 - (u + t * I)) / ((u + t * I) - 1)))
    set a := ‖A t‖
    set b := ‖P t * ((X : ℂ) ^ (1 - (u + t * I)) / ((u + t * I) - 1))‖
    set c := ‖P t * (u + t * I) * G t‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hc0 : 0 ≤ c := norm_nonneg _
    have hb2 : b ^ 2 ≤ (2 * T ^ e2) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    have hm := norm_nonneg (A t + P t * ((X : ℂ) ^ (1 - (u + t * I)) / ((u + t * I) - 1)) -
      P t * (u + t * I) * G t)
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have hAc : Continuous A :=
    ((continuous_partialZeta_line X u).mul (continuous_mollifier_line U u)).sub continuous_const
  have hGc : Continuous G := continuous_fourier (measurable_tailFun _ _) (integrable_tailFun _ hu0)
  set g : ℝ → ℝ := fun t ↦ 3 * (‖A t‖ ^ 2 + (2 * T ^ e2) ^ 2 + 16 * T ^ e3 * ‖G t‖ ^ 2)
  have hgc : Continuous g := by fun_prop
  have hA2 : ∫ t in Icc (T - 1) (2 * T + 1), ‖A t‖ ^ 2 ≤ C1 * T ^ (1 - δ ^ 2 / 3) :=
    hC1 T hT u hu
  have hG2 : ∫ t in Icc (T - 1) (2 * T + 1), ‖G t‖ ^ 2 ≤
      (2 * π * (2 ^ (1 + 2 * δ) * T ^ (-((1 - δ / 3) * (1 + 2 * δ))))) := by
    obtain ⟨hGi, hGe⟩ := 
      raw_plancherel (integrable_tailFun X hu0) (integrable_norm_tailFun_sq X hu0)
    change Integrable (fun t ↦ ‖G t‖ ^ 2) at hGi
    apply (setIntegral_le_integral hGi (.of_forall fun _ ↦ sq_nonneg _)).trans
    change (∫ t, ‖G t‖ ^ 2) = _ at hGe
    rw [hGe]
    gcongr
    refine (integral_norm_tailFun_sq_le (by positivity) hu0).trans ?_
    have hpos : 0 < T ^ (1 - δ / 3) / 2 := by positivity
    calc (X : ℝ) ^ (-(2 * u)) / (2 * u) ≤ (X : ℝ) ^ (-(2 * u)) :=
          div_le_self (by positivity) (by linarith)
      _ ≤ (X : ℝ) ^ (-(1 + 2 * δ)) := Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)
      _ ≤ (T ^ (1 - δ / 3) / 2) ^ (-(1 + 2 * δ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hX3 (by linarith)
      _ = _ := by
          rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hT0.le,
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
          ring_nf
  have hint : ∫ t in Icc (T - 1) (2 * T + 1), g t = 3 * ((∫ t in Icc (T - 1) (2 * T + 1),
      ‖A t‖ ^ 2) + (2 * T ^ e2) ^ 2 * (T + 2) +
        16 * T ^ e3 * ∫ t in Icc (T - 1) (2 * T + 1), ‖G t‖ ^ 2) := by
    simp only [g]
    rw [integral_const_mul, integral_add, integral_add, integral_const, integral_const_mul,
      measureReal_restrict_apply_univ, volume_real_Icc_of_le (by linarith)]
    · simp only [smul_eq_mul]; ring
    · exact (hAc.norm.pow 2).integrableOn_Icc
    · exact continuous_const.integrableOn_Icc
    · exact ((hAc.norm.pow 2).add continuous_const).integrableOn_Icc
    · exact (continuous_const.mul (hGc.norm.pow 2)).integrableOn_Icc
  set θ := 1 - δ ^ 2 / 3
  have hθ2 : (2 * T ^ e2) ^ 2 * (T + 2) ≤ 8 * T ^ θ := by
    have : (2 * T ^ e2) ^ 2 * T = 4 * T ^ (2 * e2 + 1) := by
      rw [Real.rpow_add_one hT0.ne', mul_comm 2 e2, Real.rpow_mul hT0.le, Real.rpow_two]; ring
    have h2 : T ^ (2 * e2 + 1) ≤ T ^ θ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp only [e2, θ]; nlinarith)
    have h3 : 0 ≤ (2 * T ^ e2) ^ 2 := sq_nonneg _
    nlinarith
  have hθ3 : 16 * T ^ e3 * ((2 * π * (2 ^ (1 + 2 * δ) *
      T ^ (-((1 - δ / 3) * (1 + 2 * δ)))))) ≤ 32 * π * 2 ^ (1 + 2 * δ) * T ^ θ := by
    have : T ^ e3 * T ^ (-((1 - δ / 3) * (1 + 2 * δ))) ≤ T ^ θ := by
      rw [← Real.rpow_add hT0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp only [e3, θ]; nlinarith)
    have hp : 0 ≤ 32 * π * 2 ^ (1 + 2 * δ) := by positivity
    calc _ = 32 * π * 2 ^ (1 + 2 * δ) *
          (T ^ e3 * T ^ (-((1 - δ / 3) * (1 + 2 * δ)))) := by ring
      _ ≤ _ := by gcongr
  calc ∫⁻ t in Icc (T - 1) (2 * T + 1), ‖mollified δ T (u + t * I)‖ₑ ^ 2
      ≤ ∫⁻ t in Icc (T - 1) (2 * T + 1), ENNReal.ofReal (g t) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht ↦ ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hpt t ht)
    _ = ENNReal.ofReal (∫ t in Icc (T - 1) (2 * T + 1), g t) :=
        (ofReal_integral_eq_lintegral_ofReal hgc.integrableOn_Icc
          (.of_forall fun t ↦ by simp only [Pi.zero_apply, g]; positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hint]
        have := mul_le_mul_of_nonneg_left hG2 (by positivity : (0 : ℝ) ≤ 16 * T ^ e3)
        nlinarith

end WeilExplicit
