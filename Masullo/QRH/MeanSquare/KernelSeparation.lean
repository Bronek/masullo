import Masullo.QRH.MeanSquare.Forms

/-! # Separation of a kernel written as an integral of products

A bilinear form `∑ c(n₁) conj c(n₂) κ(n₁,n₂)` whose kernel is an integral
`κ(n₁,n₂) = ∫ g(t) V₁(t,n₁) conj V₂(t,n₂) dt` is bounded by the mean squares of the
separated linear forms `∑ c(n) Vᵢ(t,n)`, weighted by a majorant of `g`.

For a kernel `W₁(x₁) conj W₂(x₂) ψ(log x₁ + log x₂)` the representation is Fourier inversion
of `ψ`, and the separated tests `Wᵢ(x) x^{±2πit}` are unit tests up to a factor polynomial
in `t`. The main result is `exists_separated_le`: `2j + 2` integrable derivatives of `ψ`
pay for the twists of order-`j` tests.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ComplexConjugate Nat ContDiff Real

namespace Masullo.QRH.MeanSquare

/-- Separation of a family of bilinear forms by an integral representation of the kernel.
The majorant `G` and the weight `w` are uniform in the row `ρ`. -/
theorem sum_norm_bilinear_le_of_integral {R N : Type*} (rows : Finset R) (cols : Finset N)
    (c : R → N → ℂ) (κ : R → N → N → ℂ) (g : R → ℝ → ℂ) (V₁ V₂ : ℝ → N → ℂ)
    (G w : ℝ → ℝ) {M : ℝ} (hG : ∀ t, 0 ≤ G t)
    (hκ : ∀ ρ ∈ rows, ∀ n₁ ∈ cols, ∀ n₂ ∈ cols,
      κ ρ n₁ n₂ = ∫ t, g ρ t * V₁ t n₁ * conj (V₂ t n₂))
    (hint : ∀ ρ ∈ rows, ∀ n₁ ∈ cols, ∀ n₂ ∈ cols,
      Integrable fun t => g ρ t * V₁ t n₁ * conj (V₂ t n₂))
    (hg : ∀ ρ ∈ rows, ∀ t, ‖g ρ t‖ ≤ G t) (hGw : Integrable fun t => G t * w t ^ 2)
    (hS₁ : ∀ t, ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * V₁ t n‖ ^ 2 ≤ w t ^ 2 * M)
    (hS₂ : ∀ t, ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * V₂ t n‖ ^ 2 ≤ w t ^ 2 * M) :
    ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) * κ ρ n₁ n₂‖ ≤
      M * ∫ t, G t * w t ^ 2 := by
  set S₁ := fun ρ t => ∑ n ∈ cols, c ρ n * V₁ t n
  set S₂ := fun ρ t => ∑ n ∈ cols, c ρ n * V₂ t n
  set F := fun ρ t => g ρ t * S₁ ρ t * conj (S₂ ρ t)
  have hexp : ∀ ρ t, F ρ t = ∑ n₁ ∈ cols, ∑ n₂ ∈ cols,
      c ρ n₁ * conj (c ρ n₂) * (g ρ t * V₁ t n₁ * conj (V₂ t n₂)) := by
    intro ρ t
    simp only [F, S₁, S₂]
    rw [map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    simp only [map_mul]; ring
  have hF : ∀ ρ ∈ rows, ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) * κ ρ n₁ n₂ =
      ∫ t, F ρ t := by
    intro ρ hρ
    simp only [hexp ρ]
    rw [integral_finsetSum _ fun n₁ h₁ => integrable_finsetSum _ fun n₂ h₂ =>
      (hint ρ hρ n₁ h₁ n₂ h₂).const_mul _]
    refine Finset.sum_congr rfl fun n₁ h₁ => ?_
    rw [integral_finsetSum _ fun n₂ h₂ => (hint ρ hρ n₁ h₁ n₂ h₂).const_mul _]
    refine Finset.sum_congr rfl fun n₂ h₂ => ?_
    rw [integral_const_mul, hκ ρ hρ n₁ h₁ n₂ h₂]
  have hFint : ∀ ρ ∈ rows, Integrable (F ρ) := by
    intro ρ hρ
    rw [show F ρ = _ from funext (hexp ρ)]
    exact integrable_finsetSum _ fun n₁ h₁ => integrable_finsetSum _ fun n₂ h₂ =>
      (hint ρ hρ n₁ h₁ n₂ h₂).const_mul _
  have hpt : ∀ t, ∑ ρ ∈ rows, ‖F ρ t‖ ≤ G t * w t ^ 2 * M := by
    intro t
    have hρ : ∀ ρ ∈ rows, ‖F ρ t‖ ≤ G t * ((‖S₁ ρ t‖ ^ 2 + ‖S₂ ρ t‖ ^ 2) / 2) := by
      intro ρ hρ
      simp only [F, norm_mul, Complex.norm_conj]
      have h2 : ‖S₁ ρ t‖ * ‖S₂ ρ t‖ ≤ (‖S₁ ρ t‖ ^ 2 + ‖S₂ ρ t‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖S₁ ρ t‖ - ‖S₂ ρ t‖)]
      calc ‖g ρ t‖ * ‖S₁ ρ t‖ * ‖S₂ ρ t‖ = ‖g ρ t‖ * (‖S₁ ρ t‖ * ‖S₂ ρ t‖) := by ring
        _ ≤ G t * ((‖S₁ ρ t‖ ^ 2 + ‖S₂ ρ t‖ ^ 2) / 2) :=
          mul_le_mul (hg ρ hρ t) h2 (by positivity) (hG t)
    calc ∑ ρ ∈ rows, ‖F ρ t‖
        ≤ ∑ ρ ∈ rows, G t * ((‖S₁ ρ t‖ ^ 2 + ‖S₂ ρ t‖ ^ 2) / 2) := Finset.sum_le_sum hρ
      _ = G t * ((∑ ρ ∈ rows, ‖S₁ ρ t‖ ^ 2 + ∑ ρ ∈ rows, ‖S₂ ρ t‖ ^ 2) / 2) := by
          rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ G t * ((w t ^ 2 * M + w t ^ 2 * M) / 2) := by
          gcongr
          · exact hG t
          · exact hS₁ t
          · exact hS₂ t
      _ = G t * w t ^ 2 * M := by ring
  calc ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) * κ ρ n₁ n₂‖
      = ∑ ρ ∈ rows, ‖∫ t, F ρ t‖ := Finset.sum_congr rfl fun ρ hρ => by rw [hF ρ hρ]
    _ ≤ ∑ ρ ∈ rows, ∫ t, ‖F ρ t‖ := Finset.sum_le_sum fun _ _ => norm_integral_le_integral_norm _
    _ = ∫ t, ∑ ρ ∈ rows, ‖F ρ t‖ :=
        (integral_finsetSum _ fun ρ hρ => (hFint ρ hρ).norm).symm
    _ ≤ ∫ t, G t * w t ^ 2 * M :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
          Finset.sum_nonneg fun _ _ => norm_nonneg _) (hGw.mul_const M)
          (Filter.Eventually.of_forall hpt)
    _ = M * ∫ t, G t * w t ^ 2 := by rw [integral_mul_const, mul_comm]

/-- The multiplicative character `x ↦ x^{iτ} = exp(iτ log x)` on positive reals. -/
def logCharacter (τ x : ℝ) : ℂ := Complex.exp (Real.log x * (τ * Complex.I))

/-- The test `W` twisted by the multiplicative character `x^{iτ}`. -/
def twistTest (τ : ℝ) (W : ℝ → ℂ) (x : ℝ) : ℂ := W x * logCharacter τ x

private lemma iteratedDeriv_cexp_ofReal_mul (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => Complex.exp (s * c)) =
      fun s : ℝ => c ^ n * Complex.exp (s * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h : HasDerivAt (fun s : ℝ => Complex.exp (s * c)) (Complex.exp (s * c) * (1 * c)) s :=
      ((hasDerivAt_id s).ofReal_comp.mul_const c).cexp
    rw [deriv_const_mul _ h.differentiableAt, h.deriv]
    ring

private lemma contDiff_cexp_ofReal_mul (c : ℂ) :
    ContDiff ℝ ∞ (fun s : ℝ => Complex.exp (s * c)) :=
  Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

private lemma norm_iteratedDeriv_log {x : ℝ} (hx : 0 < x) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedDeriv i Real.log x‖ = (i - 1)! * x⁻¹ ^ i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  simp only [Nat.add_sub_cancel, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_natCast, norm_zpow, Real.norm_of_nonneg hx.le]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    inv_pow]

/-- Twisting a unit test by `x^{iτ}` costs a factor `C (1 + |τ|)^j` in the test norm. -/
theorem exists_twistTest_unitTest (I : TestInterval) (j : ℕ) :
    ∃ C ≥ (1 : ℝ), ∀ (τ : ℝ) (W : ℝ → ℂ), UnitTest I j W →
      UnitTest I j fun x => ((C * (1 + |τ|) ^ j)⁻¹ : ℝ) * twistTest τ W x := by
  set D : ℝ := j ! / min I.lo 1
  have hmin : 0 < min I.lo 1 := lt_min I.pos one_pos
  have hD : 1 ≤ D := by
    rw [le_div_iff₀ hmin, one_mul]
    exact (min_le_right _ _).trans
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j))
  refine ⟨2 ^ j * j ! * D ^ j, ?_, fun τ W hW => ?_⟩
  · have : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ D ^ j := one_le_pow₀ hD
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  set c : ℂ := τ * Complex.I
  set g : ℝ → ℂ := fun s => Complex.exp (s * c)
  have hlc : logCharacter τ = fun x => g (Real.log x) := rfl
  have hg : ContDiff ℝ ∞ g := contDiff_cexp_ofReal_mul c
  have hWc : ContDiff ℝ ∞ W := hW.1
  have hW0 : ∀ x, x < I.lo → W x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => absurd (hW.2.1 h).1 (not_le.2 hx)
  have hT : ContDiff ℝ ∞ (twistTest τ W) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge 0 x with hx | hx
    · exact hWc.contDiffAt.mul
        ((hg.comp_contDiffOn (Real.contDiffOn_log.mono fun y hy => ne_of_gt hy)).contDiffAt
        (Ioi_mem_nhds hx))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (hx.trans_lt I.pos)] with y hy
      simp [twistTest, hW0 y hy]
  set w : ℝ := 2 ^ j * j ! * D ^ j * (1 + |τ|) ^ j
  have hw : 0 < w := by positivity
  refine ⟨contDiff_const.mul hT, ?_, fun k hk x hx => ?_⟩
  · refine (tsupport_mul_subset_right).trans ((tsupport_mul_subset_left).trans hW.2.1)
  have hx0 : 0 < x := I.pos.trans_le hx.1
  have hs : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hxs : x ∈ Ioi (0 : ℝ) := hx0
  have hh : ∀ i ≤ j, ‖iteratedFDerivWithin ℝ i (logCharacter τ) (Ioi 0) x‖ ≤
      i ! * (1 + |τ|) ^ j * D ^ i := by
    intro i hi
    rw [hlc]
    have := norm_iteratedFDerivWithin_comp_le (g := g) (f := Real.log) (t := univ)
      (N := ∞) hg.contDiffOn (Real.contDiffOn_log.mono fun y hy => ne_of_gt hy)
      (by exact_mod_cast le_top) uniqueDiffOn_univ hs.uniqueDiffOn (mapsTo_univ _ _) hxs
      (C := (1 + |τ|) ^ j) (D := D) (n := i) ?_ ?_
    · exact this
    · intro l hl
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedDeriv_cexp_ofReal_mul, norm_mul, norm_pow, Complex.norm_exp]
      have : ‖c‖ = |τ| := by simp [c]
      rw [this]
      have hre : (↑(Real.log x) * c).re = 0 := by simp [c]
      rw [hre, Real.exp_zero, mul_one]
      calc |τ| ^ l ≤ (1 + |τ|) ^ l := by gcongr; linarith
        _ ≤ (1 + |τ|) ^ j := pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (hl.trans hi)
    · intro l hl1 hl
      rw [iteratedFDerivWithin_of_isOpen l hs hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        norm_iteratedDeriv_log hx0 hl1, div_pow]
      have hfac : ((l - 1)! : ℝ) ≤ (j ! : ℝ) ^ l := by
        have h1 : ((l - 1)! : ℝ) ≤ j ! := by
          exact_mod_cast Nat.factorial_le (by omega)
        have h2 : (j ! : ℝ) ≤ (j ! : ℝ) ^ l := by
          have : (1 : ℝ) ≤ j ! := by
            exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
          calc (j ! : ℝ) = (j ! : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ this hl1
        exact h1.trans h2
      have hinv : x⁻¹ ^ l ≤ ((min I.lo 1) ^ l)⁻¹ := by
        rw [← inv_pow]
        gcongr
        exact (min_le_left _ _).trans hx.1
      calc ((l - 1)! : ℝ) * x⁻¹ ^ l ≤ (j ! : ℝ) ^ l * ((min I.lo 1) ^ l)⁻¹ := by
            gcongr
        _ = _ := by rw [div_eq_mul_inv]
  have hWb : ∀ i ≤ j, ‖iteratedFDerivWithin ℝ i W (Ioi 0) x‖ ≤ 1 := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hs hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hW.2.2 i hi x hx
  have hprod : ‖iteratedFDerivWithin ℝ k (twistTest τ W) (Ioi 0) x‖ ≤ w := by
    have := norm_iteratedFDerivWithin_mul_le (N := ∞) hWc.contDiffOn
      (hg.comp_contDiffOn (Real.contDiffOn_log.mono fun y hy => ne_of_gt hy))
      hs.uniqueDiffOn hxs (n := k) (by exact_mod_cast le_top)
    refine this.trans ?_
    calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i W (Ioi 0) x‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun y => g (Real.log y)) (Ioi 0) x‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (j ! * (1 + |τ|) ^ j * D ^ j) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ‖iteratedFDerivWithin ℝ i W (Ioi 0) x‖ *
                ‖iteratedFDerivWithin ℝ (k - i) (fun y => g (Real.log y)) (Ioi 0) x‖
              ≤ 1 * ((k - i)! * (1 + |τ|) ^ j * D ^ (k - i)) :=
                mul_le_mul (hWb i (hi'.trans hk)) (hh _ (by omega)) (norm_nonneg _) zero_le_one
            _ ≤ j ! * (1 + |τ|) ^ j * D ^ j := by
                rw [one_mul]
                gcongr <;> omega
      _ = 2 ^ k * (j ! * (1 + |τ|) ^ j * D ^ j) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose k
      _ ≤ w := by
          simp only [w]
          have : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hk
          calc (2 : ℝ) ^ k * (j ! * (1 + |τ|) ^ j * D ^ j)
              ≤ 2 ^ j * (j ! * (1 + |τ|) ^ j * D ^ j) := by gcongr
            _ = _ := by ring
  rw [iteratedDeriv_const_mul _
      (hT.contDiffAt.of_le (by exact_mod_cast le_top) : ContDiffAt ℝ k _ x), norm_mul,
    ← iteratedDerivWithin_of_isOpen hs hxs, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have hwn : ‖(((2 ^ j * j ! * D ^ j * (1 + |τ|) ^ j)⁻¹ : ℝ) : ℂ)‖ = w⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hwn]
  calc w⁻¹ * ‖iteratedFDerivWithin ℝ k (twistTest τ W) (Ioi 0) x‖ ≤ w⁻¹ * w := by gcongr
    _ = 1 := inv_mul_cancel₀ hw.ne'

private lemma inv_one_add_pow_le {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    (1 + |t| ^ n)⁻¹ ≤ 2 * (1 + t ^ 2)⁻¹ := by
  have h : 1 + t ^ 2 ≤ 2 * (1 + |t| ^ n) := by
    rcases le_total |t| 1 with ht | ht
    · have : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
      nlinarith [pow_nonneg (abs_nonneg t) n]
    · have : t ^ 2 ≤ |t| ^ n := by rw [← sq_abs]; exact pow_le_pow_right₀ ht hn
      nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (by positivity)]
  linarith

/-- Fourier inversion with an explicit decay bound for a function whose first `n ≥ 2`
derivatives are integrable. -/
theorem fourier_decay_and_inversion {ψ : ℝ → ℂ} {n : ℕ} (hn : 2 ≤ n) (hψ : ContDiff ℝ n ψ)
    (hint : ∀ k ≤ n, Integrable (iteratedDeriv k ψ)) :
    (∀ t, ‖𝓕 ψ t‖ ≤
      ((∫ v, ‖ψ v‖) + ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n ψ v‖) * (1 + |t| ^ n)⁻¹) ∧ Integrable
      (𝓕 ψ) ∧
    ∀ s, ψ s = ∫ t, Complex.exp (↑(2 * π * t * s) * Complex.I) * 𝓕 ψ t := by
  have h0 : Integrable ψ := by simpa using hint 0 (Nat.zero_le _)
  set A := (∫ v, ‖ψ v‖) + ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n ψ v‖
  have hb : ∀ t, ‖𝓕 ψ t‖ ≤ A * (1 + |t| ^ n)⁻¹ := by
    intro t
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact Real.one_add_pow_mul_norm_fourier_le hψ hint t
  have hcont : Continuous (𝓕 ψ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) h0
  have hFint : Integrable (𝓕 ψ) := by
    refine ((integrable_inv_one_add_sq.const_mul (2 * A))).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => (hb t).trans ?_)
    have hA : 0 ≤ A :=
      nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hb 0)) (by positivity)
    calc A * (1 + |t| ^ n)⁻¹ ≤ A * (2 * (1 + t ^ 2)⁻¹) := by
          gcongr; exact inv_one_add_pow_le hn t
      _ = 2 * A * (1 + t ^ 2)⁻¹ := by ring
  refine ⟨hb, hFint, fun s => ?_⟩
  have := congrFun (hψ.continuous.fourierInv_fourier_eq h0 hFint) s
  rw [← this, Real.fourierInv_eq']
  congr 1
  funext t
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  push_cast
  ring_nf

lemma conj_logCharacter (τ x : ℝ) : conj (logCharacter τ x) = logCharacter (-τ) x := by
  simp only [logCharacter, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring_nf

lemma logCharacter_mul_logCharacter (τ a b : ℝ) :
    logCharacter τ a * logCharacter τ b =
      Complex.exp (↑(τ * (Real.log a + Real.log b)) * Complex.I) := by
  simp only [logCharacter, ← Complex.exp_add]
  push_cast; ring_nf

lemma norm_logCharacter (τ x : ℝ) : ‖logCharacter τ x‖ = 1 := by
  rw [logCharacter, Complex.norm_exp]
  simp

private lemma one_add_pow_le_two_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + a ^ n) := by gcongr; linarith

/-- The weight left after separating order-`j` tests against `2j + 2` derivatives. -/
private def separationWeight (j : ℕ) (t : ℝ) : ℝ :=
  (1 + |t| ^ (2 * j + 2))⁻¹ * (1 + |2 * π * t|) ^ (2 * j)

private lemma integrable_separationWeight (j : ℕ) : Integrable (separationWeight j) := by
  set K : ℝ := (2 * π) ^ (2 * j) * 2 ^ (2 * j + 2)
  refine (integrable_inv_one_add_sq.const_mul K).mono' (by
    unfold separationWeight; fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  have hπ : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hw : 0 ≤ separationWeight j t := by unfold separationWeight; positivity
  rw [Real.norm_of_nonneg hw, separationWeight, ← div_eq_inv_mul, ← div_eq_mul_inv,
    div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h1 : (1 + |2 * π * t|) ^ (2 * j) ≤ (2 * π) ^ (2 * j) * (1 + |t|) ^ (2 * j) := by
    rw [← mul_pow]
    gcongr
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    nlinarith [abs_nonneg t]
  have h2 : (1 + t ^ 2) ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  have h3 := one_add_pow_le_two_pow |t| (abs_nonneg t) (2 * j + 2)
  calc (1 + |2 * π * t|) ^ (2 * j) * (1 + t ^ 2)
      ≤ (2 * π) ^ (2 * j) * (1 + |t|) ^ (2 * j) * (1 + |t|) ^ 2 := by gcongr
    _ = (2 * π) ^ (2 * j) * (1 + |t|) ^ (2 * j + 2) := by ring
    _ ≤ (2 * π) ^ (2 * j) * (2 ^ (2 * j + 2) * (1 + |t| ^ (2 * j + 2))) := by gcongr
    _ = K * (1 + |t| ^ (2 * j + 2)) := by ring

/-- Separation of a family of bilinear forms with kernels `W₁(x₁) conj W₂(x₂) ψ_ρ(log x₁x₂)`.
If every order-`j` unit test on `I` has mean square at most `M` over the rows, and each
`ψ_ρ` has `2j + 2` integrable derivatives with `L¹` norms at most `A` at orders `0` and
`2j + 2`, then the bilinear forms have total size at most `C A M`. -/
theorem exists_separated_le (I : TestInterval) (j : ℕ) : ∃ C ≥ (0 : ℝ),
    ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c : R → N → ℂ) (x : N → ℝ)
      (W₁ W₂ : ℝ → ℂ) (ψ : R → ℝ → ℂ) {A M : ℝ}, 0 ≤ A → 0 ≤ M →
      UnitTest I j W₁ → UnitTest I j W₂ →
      (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c ρ n * U (x n)‖ ^ 2 ≤ M) →
      (∀ ρ ∈ rows, ContDiff ℝ (2 * j + 2) (ψ ρ)) →
      (∀ ρ ∈ rows, ∀ k ≤ 2 * j + 2, Integrable (iteratedDeriv k (ψ ρ))) →
      (∀ ρ ∈ rows, ∫ v, ‖ψ ρ v‖ ≤ A) →
      (∀ ρ ∈ rows, ∫ v, ‖iteratedDeriv (2 * j + 2) (ψ ρ) v‖ ≤ A) →
      ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c ρ n₁ * conj (c ρ n₂) *
        (W₁ (x n₁) * conj (W₂ (x n₂)) * ψ ρ (Real.log (x n₁) + Real.log (x n₂)))‖ ≤
        C * A * M := by
  obtain ⟨Ct, hCt1, hCt⟩ := exists_twistTest_unitTest I j
  set n := 2 * j + 2
  set a : ℝ := 1 + ((2 * π) ^ n)⁻¹
  set K₀ : ℝ := ∫ t, separationWeight j t
  have hK₀ : 0 ≤ K₀ := integral_nonneg fun t => by unfold separationWeight; positivity
  refine ⟨a * Ct ^ 2 * K₀, by positivity, ?_⟩
  intro R N rows cols c x W₁ W₂ ψ A M hA hM hW₁ hW₂ hU hψ hψi hA0 hAn
  have hrep : ∀ ρ ∈ rows, _ := fun ρ hρ =>
    fourier_decay_and_inversion (n := n) (by omega) (hψ ρ hρ) (hψi ρ hρ)
  set w : ℝ → ℝ := fun t => Ct * (1 + |2 * π * t|) ^ j
  set G : ℝ → ℝ := fun t => a * A * (1 + |t| ^ n)⁻¹
  have hGw : (fun t => G t * w t ^ 2) = fun t => a * A * Ct ^ 2 * separationWeight j t := by
    funext t
    simp only [G, w, separationWeight, n]
    ring
  have hS : ∀ (τ : ℝ) (W : ℝ → ℂ), UnitTest I j W → ∑ ρ ∈ rows,
      ‖∑ m ∈ cols, c ρ m * twistTest τ W (x m)‖ ^ 2 ≤ (Ct * (1 + |τ|) ^ j) ^ 2 * M := by
    intro τ W hW
    have hu := hU _ (hCt τ W hW)
    set b : ℝ := Ct * (1 + |τ|) ^ j
    have hb : 0 < b := by positivity
    have hsum : ∀ ρ, ∑ m ∈ cols, c ρ m * twistTest τ W (x m) =
        (b : ℂ) * ∑ m ∈ cols, c ρ m * (((b⁻¹ : ℝ) : ℂ) * twistTest τ W (x m)) := by
      intro ρ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
      push_cast
      field_simp
    simp_rw [hsum, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hpt : ∀ ρ n₁ n₂ t, 𝓕 (ψ ρ) t * twistTest (2 * π * t) W₁ (x n₁) *
      conj (twistTest (-(2 * π * t)) W₂ (x n₂)) = (W₁ (x n₁) * conj (W₂ (x n₂))) *
        (Complex.exp (↑(2 * π * t * (Real.log (x n₁) + Real.log (x n₂))) * Complex.I) *
          𝓕 (ψ ρ) t) := by
    intro ρ n₁ n₂ t
    simp only [twistTest, map_mul, conj_logCharacter, neg_neg]
    rw [← logCharacter_mul_logCharacter]
    ring
  have hexpint : ∀ ρ ∈ rows, ∀ s : ℝ,
      Integrable fun t => Complex.exp (↑(2 * π * t * s) * Complex.I) * 𝓕 (ψ ρ) t := by
    intro ρ hρ s
    exact (hrep ρ hρ).2.1.bdd_mul (c := 1) (by fun_prop)
      (Filter.Eventually.of_forall fun t => by rw [Complex.norm_exp_ofReal_mul_I])
  have key := sum_norm_bilinear_le_of_integral rows cols c
    (fun ρ n₁ n₂ => W₁ (x n₁) * conj (W₂ (x n₂)) * ψ ρ (Real.log (x n₁) + Real.log (x n₂)))
    (fun ρ t => 𝓕 (ψ ρ) t) (fun t m => twistTest (2 * π * t) W₁ (x m))
    (fun t m => twistTest (-(2 * π * t)) W₂ (x m)) G w (M := M)
    (fun t => by positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · refine key.trans_eq ?_
    rw [hGw, integral_const_mul]
    ring
  · intro ρ hρ n₁ _ n₂ _
    simp only [hpt, integral_const_mul]
    rw [← (hrep ρ hρ).2.2]
  · intro ρ hρ n₁ _ n₂ _
    simp only [hpt]
    exact (hexpint ρ hρ _).const_mul _
  · intro ρ hρ t
    refine ((hrep ρ hρ).1 t).trans ?_
    simp only [G]
    gcongr
    calc (∫ v, ‖ψ ρ v‖) + ((2 * π) ^ n)⁻¹ * ∫ v, ‖iteratedDeriv n (ψ ρ) v‖
        ≤ A + ((2 * π) ^ n)⁻¹ * A := by gcongr; exacts [hA0 ρ hρ, hAn ρ hρ]
      _ = a * A := by ring
  · rw [hGw]
    exact (integrable_separationWeight j).const_mul _
  · exact fun t => hS _ _ hW₁
  · intro t
    have := hS (-(2 * π * t)) _ hW₂
    rwa [abs_neg] at this

end Masullo.QRH.MeanSquare
