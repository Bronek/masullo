import Masullo.QRH.MeanSquare.PrimitivePoisson
import Masullo.QRH.MeanSquare.PrimeRows
import Masullo.QRH.MeanSquare.UnitRows

/-! # The first Poisson reduction for the full Möbius rows

The rows of `FullRowEstimate` are bounded by a Schwartz-weighted sum over all elements
(`sum_elementRows_le_tsum`). Expanding the square (`tsum_majorant_eq`) gives the
correlations `pairRowSum`. The diagonal costs `O(Y)` per column
(`exists_tsum_norm_schwartz_le`), and primitive Poisson evaluates the other correlations
(`pairRowSum_eq_poisson`).
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- A Schwartz majorant of the indicator of `[0, 1]`, real and nonnegative on `[0, ∞)`. -/
structure IsRowMajorant (P : SchwartzMap ℝ ℂ) : Prop where
  im_eq : ∀ x, (P x).im = 0
  re_nonneg : ∀ x, 0 ≤ x → 0 ≤ (P x).re
  one_le_re : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ (P x).re

/-! ### Summability and the lattice mass of a Schwartz weight -/

lemma summable_schwartz (P : SchwartzMap ℝ ℂ) {Y : ℝ} (hY : 0 < Y) :
    Summable fun y : 𝓔 => P (elementNorm y / Y) := by
  obtain ⟨s, hs, -⟩ := gaoZhaoLemma23 P Y hY 0 1 one_ne_zero
  let e : {m : 𝓔 // (1 : 𝓔) ∣ m - 0} ≃ 𝓔 := Equiv.subtypeUnivEquiv fun m => one_dvd _
  rw [← e.summable_iff]
  convert hs.summable using 2 with m
  simp [e, elementNorm_eq_normSq]

lemma summable_norm_schwartz (P : SchwartzMap ℝ ℂ) {Y : ℝ} (hY : 0 < Y) :
    Summable fun y : 𝓔 => ‖P (elementNorm y / Y)‖ :=
  summable_norm_iff.mpr (summable_schwartz P hY)

/-- A dyadic majorant for a function bounded by `C₀` with `r² φ(r) ≤ C₂`. -/
private lemma le_dyadic {φ : ℝ → ℝ} {C₀ C₂ : ℝ} (h0 : ∀ r, φ r ≤ C₀) (hC₀ : 0 ≤ C₀)
    (h2 : ∀ r, r ^ 2 * φ r ≤ C₂) (hC₂ : 0 ≤ C₂) :
    ∀ (J : ℕ) (r : ℝ), 0 ≤ r → r ≤ 2 ^ J →
      φ r ≤ (C₀ + C₂) * ∑ j ∈ Finset.range (J + 1), 4 / 4 ^ j * (if r ≤ 2 ^ j then 1 else 0) := by
  have hterm : ∀ (j : ℕ) (r : ℝ), 0 ≤ 4 / (4 : ℝ) ^ j * (if r ≤ 2 ^ j then 1 else 0) :=
    fun j r => by
    split_ifs <;> positivity
  intro J
  induction J with
  | zero =>
    intro r _ hr
    simp only [zero_add, Finset.sum_range_one, pow_zero, div_one]
    rw [ite_eq_left (by simpa using hr)]
    nlinarith [h0 r]
  | succ J ih =>
    intro r hr0 hr
    rw [Finset.sum_range_succ]
    by_cases hrJ : r ≤ 2 ^ J
    · nlinarith [ih r hr0 hrJ, hterm (J + 1) r]
    · rw [ite_eq_left hr]
      have hlt : (2 : ℝ) ^ J < r := lt_of_not_ge hrJ
      have h4 : (4 : ℝ) ^ J < r ^ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
        exact pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      have hS : 0 ≤ ∑ j ∈ Finset.range (J + 1), 4 / (4 : ℝ) ^ j * (if r ≤ 2 ^ j then 1 else 0) :=
        Finset.sum_nonneg fun j _ => hterm j r
      have hφ : φ r ≤ C₂ / 4 ^ J := by
        rw [le_div_iff₀ (by positivity)]
        by_cases hφ0 : φ r ≤ 0
        · nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) J]
        · nlinarith [h2 r]
      have : C₂ / 4 ^ J ≤ (C₀ + C₂) * (4 / 4 ^ (J + 1) * 1) := by
        rw [pow_succ, mul_one, show (4 : ℝ) / (4 ^ J * 4) = 1 / 4 ^ J by field_simp,
          mul_one_div]
        gcongr
        linarith
      nlinarith [mul_nonneg (by linarith : 0 ≤ C₀ + C₂) hS]

private lemma card_filter_norm_le (s : Finset 𝓔) {R : ℝ} (hR : 0 ≤ R) :
    ((s.filter fun y => (elementNorm y : ℝ) ≤ R).card : ℝ) ≤ (elementRows R).card + 1 := by
  classical
  have hsub : s.filter (fun y => (elementNorm y : ℝ) ≤ R) ⊆ insert 0 (elementRows R) := by
    intro y hy
    rw [Finset.mem_insert]
    by_cases h0 : y = 0
    · exact Or.inl h0
    · exact Or.inr ((mem_elementRows hR).mpr ⟨h0, (Finset.mem_filter.mp hy).2⟩)
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- The lattice mass of a Schwartz weight at scale `Y ≥ 1` is `O(Y)`. -/
theorem exists_tsum_norm_schwartz_le (P : SchwartzMap ℝ ℂ) :
    ∃ C ≥ (0 : ℝ), ∀ Y : ℝ, 1 ≤ Y → ∑' y : 𝓔, ‖P (elementNorm y / Y)‖ ≤ C * Y := by
  classical
  obtain ⟨C₀, hC₀', hC₀⟩ := P.decay 0 0
  obtain ⟨C₂, hC₂', hC₂⟩ := P.decay 2 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs, sq_abs] at hC₀ hC₂
  replace hC₀' := hC₀'.le
  replace hC₂' := hC₂'.le
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  have hA₀ : 0 ≤ A := by
    have := hA 1 le_rfl
    nlinarith [(Finset.card_pos.mpr ⟨⊤, (mem_idealsLe zero_le_one).mpr (by simp)⟩ :
      0 < (idealsLe 1).card)]
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Nat.card 𝓔ˣ := ⟨_, rfl⟩
  have hU₀ : 0 ≤ U := hU ▸ Nat.cast_nonneg _
  have hrows : ∀ R : ℝ, 1 ≤ R → ((elementRows R).card : ℝ) ≤ A * U * R := fun R hR => by
    calc ((elementRows R).card : ℝ) ≤ (idealsLe R).card * U := by
          rw [hU]; exact_mod_cast card_elementRows_le R
      _ ≤ A * R * U := mul_le_mul_of_nonneg_right (hA R hR) hU₀
      _ = A * U * R := by ring
  refine ⟨8 * (C₀ + C₂) * (A * U + 1), by positivity, fun Y hY => ?_⟩
  have hY₀ : 0 < Y := by linarith
  refine (summable_norm_schwartz P hY₀).tsum_le_of_sum_le fun s => ?_
  set J := ∑ y ∈ s, elementNorm y
  have hJ : ∀ y ∈ s, (elementNorm y : ℝ) / Y ≤ 2 ^ J := fun y hy => by
    calc (elementNorm y : ℝ) / Y ≤ elementNorm y := div_le_self (Nat.cast_nonneg _) hY
      _ ≤ J := by exact_mod_cast Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy
      _ ≤ 2 ^ J := by exact_mod_cast (Nat.lt_two_pow_self).le
  set w : ℕ → ℝ := fun j => 4 / 4 ^ j
  have hpt := le_dyadic (φ := fun r => ‖P r‖) hC₀ hC₀' hC₂ hC₂' J
  calc ∑ y ∈ s, ‖P (elementNorm y / Y)‖
      ≤ ∑ y ∈ s, (C₀ + C₂) * ∑ j ∈ Finset.range (J + 1),
          w j * (if (elementNorm y : ℝ) / Y ≤ 2 ^ j then 1 else 0) :=
        Finset.sum_le_sum fun y hy => hpt _ (by positivity) (hJ y hy)
    _ = (C₀ + C₂) * ∑ j ∈ Finset.range (J + 1),
          w j * ((s.filter fun y => (elementNorm y : ℝ) ≤ 2 ^ j * Y).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, Finset.card_filter, Nat.cast_sum]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [div_le_iff₀ hY₀]
        split_ifs <;> simp
    _ ≤ (C₀ + C₂) * ∑ j ∈ Finset.range (J + 1), w j * ((A * U + 1) * (2 ^ j * Y)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        · have h1 : 1 ≤ 2 ^ j * Y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hY
          calc _ ≤ ((elementRows (2 ^ j * Y)).card : ℝ) + 1 := card_filter_norm_le s (by linarith)
            _ ≤ A * U * (2 ^ j * Y) + 2 ^ j * Y := by linarith [hrows _ h1]
            _ = _ := by ring
    _ = (C₀ + C₂) * (A * U + 1) * Y * ∑ j ∈ Finset.range (J + 1), 4 * (1 / 2) ^ j := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [w, one_div, inv_pow]
        rw [show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
        field_simp
    _ ≤ (C₀ + C₂) * (A * U + 1) * Y * 8 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Finset.mul_sum]
        have := sum_geometric_two_le (J + 1)
        simp only [one_div] at this ⊢
        linarith
    _ = 8 * (C₀ + C₂) * (A * U + 1) * Y := by ring

/-! ### The majorant and the expansion of the square -/

/-- The rows in the disk of radius `Y` are bounded by the `P`-weighted sum over all elements. -/
theorem sum_elementRows_le_tsum {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) {Y : ℝ}
    (hY : 0 < Y) {v : 𝓔 → ℂ} {B : ℝ} (hv : ∀ y, ‖v y‖ ≤ B) :
    ∑ k ∈ elementRows Y, ‖v k‖ ^ 2 ≤ ∑' y : 𝓔, (P (elementNorm y / Y)).re * ‖v y‖ ^ 2 := by
  have hnn : ∀ y, 0 ≤ (P (elementNorm y / Y)).re * ‖v y‖ ^ 2 := fun y =>
    mul_nonneg (hP.re_nonneg _ (by positivity)) (sq_nonneg _)
  have hsum : Summable fun y : 𝓔 => (P (elementNorm y / Y)).re * ‖v y‖ ^ 2 := by
    refine Summable.of_nonneg_of_le hnn (fun y => ?_)
      ((summable_norm_schwartz P hY).mul_right (B ^ 2))
    exact mul_le_mul (Complex.re_le_norm _) (pow_le_pow_left₀ (norm_nonneg _) (hv y) 2)
      (sq_nonneg _) (norm_nonneg _)
  calc ∑ k ∈ elementRows Y, ‖v k‖ ^ 2
      ≤ ∑ k ∈ elementRows Y, (P (elementNorm k / Y)).re * ‖v k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := (mem_elementRows hY.le).mp hk
        have h1 : 1 ≤ (P (elementNorm k / Y)).re :=
          hP.one_le_re _ ⟨by positivity, (div_le_one hY).mpr hk'.2⟩
        nlinarith [sq_nonneg ‖v k‖]
    _ ≤ _ := hsum.sum_le_tsum _ fun y _ => hnn y

/-- The `P`-weighted correlation of two sextic rows. -/
def pairRowSum (P : SchwartzMap ℝ ℂ) (Y : ℝ) (n₁ n₂ : Ideal 𝓔) : ℂ :=
  ∑' y : 𝓔, P (elementNorm y / Y) * (sextic n₁ y * conj (sextic n₂ y))

lemma summable_pairRow (P : SchwartzMap ℝ ℂ) {Y : ℝ} (hY : 0 < Y) (n₁ n₂ : Ideal 𝓔) :
    Summable fun y : 𝓔 => P (elementNorm y / Y) * (sextic n₁ y * conj (sextic n₂ y)) := by
  refine Summable.of_norm_bounded (summable_norm_schwartz P hY) fun y => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_right (norm_nonneg _)
    ((mul_le_mul (norm_sextic_le_one _ _) (norm_sextic_le_one _ _) (norm_nonneg _)
      zero_le_one).trans_eq (one_mul 1))

/-- Expansion of the weighted square into the correlations of the columns. -/
theorem tsum_majorant_eq {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) {Y : ℝ} (hY : 0 < Y)
    (S : Finset (Ideal 𝓔)) (c : Ideal 𝓔 → ℂ) :
    ∑' y : 𝓔, (P (elementNorm y / Y)).re * ‖∑ n ∈ S, c n * sextic n y‖ ^ 2 =
      (∑ n₁ ∈ S, ∑ n₂ ∈ S, c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂).re := by
  have hpt : ∀ y : 𝓔, (P (elementNorm y / Y)).re * ‖∑ n ∈ S, c n * sextic n y‖ ^ 2 =
      (∑ n₁ ∈ S, ∑ n₂ ∈ S, c n₁ * conj (c n₂) *
        (P (elementNorm y / Y) * (sextic n₁ y * conj (sextic n₂ y)))).re := by
    intro y
    have hre : P (elementNorm y / Y) = ((P (elementNorm y / Y)).re : ℂ) :=
      Complex.ext rfl (by simp [hP.im_eq])
    have hsq : ((‖∑ n ∈ S, c n * sextic n y‖ ^ 2 : ℝ) : ℂ) =
        (∑ n ∈ S, c n * sextic n y) * conj (∑ n ∈ S, c n * sextic n y) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have : ∑ n₁ ∈ S, ∑ n₂ ∈ S, c n₁ * conj (c n₂) *
        (P (elementNorm y / Y) * (sextic n₁ y * conj (sextic n₂ y))) =
        P (elementNorm y / Y) * ((‖∑ n ∈ S, c n * sextic n y‖ ^ 2 : ℝ) : ℂ) := by
      rw [hsq, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n₂ _ => ?_
      rw [map_mul]
      ring
    rw [this, hre, ← Complex.ofReal_mul]
    exact (Complex.ofReal_re _).symm
  have hs : ∀ n₁ n₂ : Ideal 𝓔, Summable fun y : 𝓔 => c n₁ * conj (c n₂) *
      (P (elementNorm y / Y) * (sextic n₁ y * conj (sextic n₂ y))) := fun n₁ n₂ =>
    (summable_pairRow P hY n₁ n₂).mul_left _
  simp_rw [hpt]
  rw [← Complex.re_tsum (summable_sum fun n₁ _ => summable_sum fun n₂ _ => hs n₁ n₂),
    Summable.tsum_finsetSum fun n₁ _ => summable_sum fun n₂ _ => hs n₁ n₂]
  congr 1
  refine Finset.sum_congr rfl fun n₁ _ => ?_
  rw [Summable.tsum_finsetSum fun n₂ _ => hs n₁ n₂]
  refine Finset.sum_congr rfl fun n₂ _ => ?_
  rw [tsum_mul_left, pairRowSum]

/-- The diagonal correlation is bounded by the lattice mass of the weight. -/
lemma norm_pairRowSum_le (P : SchwartzMap ℝ ℂ) {Y : ℝ} (hY : 0 < Y) (n₁ n₂ : Ideal 𝓔) :
    ‖pairRowSum P Y n₁ n₂‖ ≤ ∑' y : 𝓔, ‖P (elementNorm y / Y)‖ := by
  refine (norm_tsum_le_tsum_norm (summable_pairRow P hY n₁ n₂).norm).trans
    ((summable_pairRow P hY n₁ n₂).norm.tsum_le_tsum (fun y => ?_) (summable_norm_schwartz P hY))
  rw [norm_mul, norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_right (norm_nonneg _)
    ((mul_le_mul (norm_sextic_le_one _ _) (norm_sextic_le_one _ _) (norm_nonneg _)
      zero_le_one).trans_eq (one_mul 1))

/-! ### Primitive Poisson for the off-diagonal correlations -/

/-- The right side of `PrimitivePoisson` for the pair `(b, c)` with exclusion `g`. -/
def poissonDual (P : SchwartzMap ℝ ℂ) (Y : ℝ) (b c g : Ideal 𝓔) : ℂ :=
  (Y : ℂ) * pairGauss b c / Real.sqrt (absNorm (b * c)) *
    ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g},
      (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e.val : ℂ) *
        ∑' h : 𝓔, conj (pairCharacter b c h) * gaoZhaoTransform P
          (Real.sqrt (Y * elementNorm h / ((absNorm e.val : ℝ) * absNorm (b * c))))

lemma sextic_mul_conj {g : Ideal 𝓔} (hg : AwayFromSix g) (y : 𝓔) : open Classical in
    sextic g y * conj (sextic g y) = if IsCoprime (span {y}) g then 1 else 0 := by
  split_ifs with h
  · rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_sextic_of_coprime hg h.symm]
    norm_num
  · rw [sextic_eq_zero hg fun h' => h h'.symm, zero_mul]

/-- Primitive Poisson evaluates the correlation of `g z₁` and `g z₂`. -/
theorem pairRowSum_eq_poisson {g z₁ z₂ : Ideal 𝓔} (hg : Starred g) (h₁ : Starred z₁)
    (h₂ : Starred z₂) (h12 : IsCoprime z₁ z₂) (hgz : IsCoprime g (z₂ * z₁))
    (P : SchwartzMap ℝ ℂ) {Y : ℝ} (hY : 0 < Y) :
    pairRowSum P Y (g * z₁) (g * z₂) = poissonDual P Y z₂ z₁ g := by
  classical
  rw [pairRowSum, poissonDual, ← primitivePoisson z₂ z₁ g h₂ h₁ hg h12.symm hgz P Y hY]
  refine tsum_congr fun y => ?_
  have : sextic (g * z₁) y * conj (sextic (g * z₂) y) =
      (sextic g y * conj (sextic g y)) * pairCharacter z₂ z₁ y := by
    rw [sextic_mul_right, sextic_mul_right, map_mul, pairCharacter]
    ring
  rw [this, sextic_mul_conj hg.1]
  split_ifs <;> simp

lemma isCoprime_of_squarefree_mul {I J : Ideal 𝓔} (h : Squarefree (I * J)) : IsCoprime I J :=
  Ideal.isCoprime_iff_gcd.mpr (by
    simpa using gcd_isUnit_iff_isRelPrime.mpr (squarefree_mul_iff.mp h).1)

lemma Starred.of_mul_left {I J : Ideal 𝓔} (h : Starred (I * J)) : Starred I :=
  ⟨⟨left_ne_zero_of_mul h.1.1, h.1.2.of_mul_left_left⟩, h.2.of_mul_left⟩

lemma Starred.of_mul_right {I J : Ideal 𝓔} (h : Starred (I * J)) : Starred J :=
  (mul_comm I J ▸ h).of_mul_left

/-- Two starred ideals are `g z₁` and `g z₂` with `g` their greatest common divisor. -/
theorem exists_gcd_split {n₁ n₂ : Ideal 𝓔} (h₁ : Starred n₁) (h₂ : Starred n₂) :
    ∃ g z₁ z₂ : Ideal 𝓔, n₁ = g * z₁ ∧ n₂ = g * z₂ ∧ Starred g ∧ Starred z₁ ∧ Starred z₂ ∧
      IsCoprime z₁ z₂ ∧ IsCoprime g (z₂ * z₁) := by
  obtain ⟨z₁, hz₁⟩ := gcd_dvd_left n₁ n₂
  obtain ⟨z₂, hz₂⟩ := gcd_dvd_right n₁ n₂
  set g := gcd n₁ n₂
  have hs₁ : Starred (g * z₁) := hz₁ ▸ h₁
  have hs₂ : Starred (g * z₂) := hz₂ ▸ h₂
  have hg0 : g ≠ 0 := left_ne_zero_of_mul hs₁.1.1
  have hz : gcd z₁ z₂ = 1 := by
    have h := gcd_mul_left g z₁ z₂
    rw [← hz₁, ← hz₂, normalize_eq] at h
    exact (mul_eq_left₀ hg0).mp h.symm
  refine ⟨g, z₁, z₂, hz₁, hz₂, hs₁.of_mul_left, hs₁.of_mul_right, hs₂.of_mul_right,
    Ideal.isCoprime_iff_gcd.mpr hz, ?_⟩
  exact (isCoprime_of_squarefree_mul hs₂.2).mul_right (isCoprime_of_squarefree_mul hs₁.2)

/-- The Möbius weights of the two columns become the Gauss coefficients of the cofactors.
The hypothesis is the first clause of `PairedGaussIdentities`. -/
theorem moebius_mul_pairGauss {A : (𝓔 ⧸ span {(72 : 𝓔)}) → (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ}
    (hA : ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      (idealMoebius b : ℂ) * idealMoebius c * pairGauss b c =
        gaussCoefficient b * conj (gaussCoefficient c) *
          A (Ideal.Quotient.mk _ (generator b)) (Ideal.Quotient.mk _ (generator c)))
    {g z₁ z₂ : Ideal 𝓔} (hg : Starred g) (h₁ : Starred z₁) (h₂ : Starred z₂)
    (h12 : IsCoprime z₁ z₂) (hgz : IsCoprime g (z₂ * z₁)) :
    (idealMoebius (g * z₁) : ℂ) * idealMoebius (g * z₂) * pairGauss z₂ z₁ =
      gaussCoefficient z₂ * conj (gaussCoefficient z₁) *
        A (Ideal.Quotient.mk _ (generator z₂)) (Ideal.Quotient.mk _ (generator z₁)) := by
  classical
  have hsq : (idealMoebius g : ℂ) * idealMoebius g = 1 := by
    simp only [idealMoebius, hg.2, ↓reduceIte, Int.cast_pow, Int.cast_neg, Int.cast_one,
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [idealMoebius_mul (IsCoprime.of_mul_right_right hgz),
    idealMoebius_mul (IsCoprime.of_mul_right_left hgz), ← hA z₂ z₁ h₂ h₁ h12.symm]
  push_cast
  linear_combination ((idealMoebius z₁ : ℂ) * idealMoebius z₂ * pairGauss z₂ z₁) * hsq

/-! ### The reduction of the full rows to the off-diagonal correlations -/

open Classical in
/-- The Möbius column of `FullRowEstimate`, restricted to the starred ideals. -/
def moebiusCoeff (W : ℝ → ℂ) (D : ℝ) (n : Ideal 𝓔) : ℂ :=
  if Starred n then (idealMoebius n : ℂ) * W (absNorm n / D) else 0

/-- The off-diagonal part of the expanded `P`-weighted square of the Möbius rows. -/
def offDiagonalSum (P : SchwartzMap ℝ ℂ) (W : ℝ → ℂ) (D Y : ℝ) : ℂ := open Classical in
  ∑ᶠ n₁ : Ideal 𝓔, ∑ᶠ n₂ : Ideal 𝓔, if n₁ = n₂ then 0 else
    moebiusCoeff W D n₁ * conj (moebiusCoeff W D n₂) * pairRowSum P Y n₁ n₂

/-- The bound on the off-diagonal correlations required for `FullRowEstimate`, at the row
length `Y = D^(1+θ)`. By `pairRowSum_eq_poisson` and `moebius_mul_pairGauss` each term is a
primitive Poisson dual with Gauss coefficients. -/
def OffDiagonalEstimate (P : SchwartzMap ℝ ℂ) : Prop :=
  ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 10 → ∀ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ D : ℝ, 2 ≤ D →
      (offDiagonalSum P W D (D ^ (1 + θ))).re ≤ C * D ^ (2 + θ + ε)

private lemma sum_sum_eq_diag_add {S : Finset (Ideal 𝓔)} (G : Ideal 𝓔 → Ideal 𝓔 → ℂ) :
    open Classical in
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, G n₁ n₂ =
      ∑ n ∈ S, G n n + ∑ n₁ ∈ S, ∑ n₂ ∈ S, if n₁ = n₂ then 0 else G n₁ n₂ := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n₁ hn₁ => ?_
  have : ∀ n₂, G n₁ n₂ = (if n₁ = n₂ then G n₁ n₂ else 0) + if n₁ = n₂ then 0 else G n₁ n₂ :=
    fun n₂ => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun n₂ _ => this n₂, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq S n₁ (fun n₂ => G n₁ n₂), ite_eq_left hn₁]

/-- `FullRowEstimate` follows from the off-diagonal bound for one row majorant. -/
theorem fullRowEstimate_of_offDiagonal {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P)
    (hoff : OffDiagonalEstimate P) : FullRowEstimate := by
  classical
  intro W hW hc hs θ hθ hθ' ε hε
  obtain ⟨Coff, hCoff, hoff⟩ := hoff W hW hc hs θ hθ hθ' ε hε
  obtain ⟨M, hM⟩ := hW.continuous.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  obtain ⟨CP, hCP, hmass⟩ := exists_tsum_norm_schwartz_le P
  set R' := max R 1
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hA₀ : 0 ≤ A := by
    have := hA 1 le_rfl
    nlinarith [(Finset.card_pos.mpr ⟨⊤, (mem_idealsLe zero_le_one).mpr (by simp)⟩ :
      0 < (idealsLe 1).card)]
  have hWz : ∀ x, R' < x → W x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by linarith [hR h, le_max_left R 1]
  refine ⟨A * R' * M ^ 2 * CP + Coff, by positivity, fun D hD => ?_⟩
  have hD₀ : 0 < D := by linarith
  set Y := D ^ (1 + θ)
  have hY : 1 ≤ Y := Real.one_le_rpow (by linarith) (by linarith)
  set S := (idealsLe (R' * D)).filter Starred
  set c := moebiusCoeff W D
  have hcS : ∀ n ∉ S, c n = 0 := by
    intro n hn
    simp only [c, moebiusCoeff]
    split_ifs with h
    · rw [hWz _ ?_, mul_zero]
      by_contra hle
      exact hn (Finset.mem_filter.mpr ⟨(mem_idealsLe (by positivity)).mpr
        (by rwa [not_lt, div_le_iff₀ hD₀] at hle), h⟩)
    · rfl
  have hcM : ∀ n, ‖c n‖ ≤ M := by
    intro n
    simp only [c, moebiusCoeff]
    split_ifs with h
    · rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hM _)
      simp only [idealMoebius, h.2, ↓reduceIte, Int.cast_pow, Int.cast_neg, Int.cast_one,
        norm_pow, norm_neg, norm_one, one_pow, le_refl]
    · simpa using hM₀
  have hrow : ∀ y, moebiusRow W D y = ∑ n ∈ S, c n * sextic n y := by
    intro y
    rw [moebiusRow, tsum_eq_sum (s := S)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have h := (Finset.mem_filter.mp hn).2
      simp only [c, moebiusCoeff, ite_eq_left h, ite_eq_left h.1]
      ring
    · intro n hn
      split_ifs with h
      · by_cases hsq : Squarefree n
        · have : c n = 0 := hcS n hn
          simp only [c, moebiusCoeff] at this
          have hst : Starred n := ⟨h, hsq⟩
          rw [ite_eq_left hst] at this
          rw [mul_right_comm, this, zero_mul]
        · simp [idealMoebius, hsq]
      · rfl
  have hcard : (S.card : ℝ) ≤ A * (R' * D) :=
    (by exact_mod_cast Finset.card_filter_le _ _ : (S.card : ℝ) ≤ (idealsLe (R' * D)).card).trans
      (hA _ (one_le_mul_of_one_le_of_one_le (le_max_right R 1) (by linarith)))
  have hB : ∀ y, ‖moebiusRow W D y‖ ≤ S.card * M := fun y => by
    rw [hrow]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ S, ‖c n * sextic n y‖ ≤ ∑ _n ∈ S, M := Finset.sum_le_sum fun n _ => by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (norm_sextic_le_one _ _)).trans (hcM n)
      _ = S.card * M := by simp
  have hoffS : offDiagonalSum P W D Y = ∑ n₁ ∈ S, ∑ n₂ ∈ S, if n₁ = n₂ then 0 else
      c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂ := by
    have hin : ∀ n₁, (∑ᶠ n₂ : Ideal 𝓔, if n₁ = n₂ then (0 : ℂ) else
        c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂) = ∑ n₂ ∈ S, if n₁ = n₂ then 0 else
        c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂ := fun n₁ =>
      finsum_eq_sum_of_support_subset _ fun n₂ h => by
        by_contra hn
        exact h (by simp [hcS n₂ hn])
    refine (finsum_congr hin).trans (finsum_eq_sum_of_support_subset _ fun n₁ h => ?_)
    by_contra hn
    exact h (Finset.sum_eq_zero fun n₂ _ => by simp [hcS n₁ hn])
  have hdiag : ‖∑ n ∈ S, c n * conj (c n) * pairRowSum P Y n n‖ ≤
      A * R' * M ^ 2 * CP * (D * Y) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ S, ‖c n * conj (c n) * pairRowSum P Y n n‖ ≤ ∑ _n ∈ S, M ^ 2 * (CP * Y) :=
          Finset.sum_le_sum fun n _ => by
            rw [norm_mul, norm_mul, Complex.norm_conj, ← sq]
            exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hcM n) 2)
              ((norm_pairRowSum_le P (by linarith) n n).trans (hmass Y hY)) (norm_nonneg _)
              (by positivity)
      _ = S.card * (M ^ 2 * (CP * Y)) := by simp
      _ ≤ A * (R' * D) * (M ^ 2 * (CP * Y)) := by gcongr
      _ = A * R' * M ^ 2 * CP * (D * Y) := by ring
  have hDY : D * Y ≤ D ^ (2 + θ + ε) := by
    calc D * Y = D ^ (2 + θ) := by
          rw [show (2 + θ : ℝ) = 1 + (1 + θ) by ring, Real.rpow_add hD₀, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc ∑ k ∈ elementRows Y, ‖moebiusRow W D k‖ ^ 2
      ≤ ∑' y : 𝓔, (P (elementNorm y / Y)).re * ‖moebiusRow W D y‖ ^ 2 :=
        sum_elementRows_le_tsum hP (by linarith) hB
    _ = (∑ n₁ ∈ S, ∑ n₂ ∈ S, c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂).re := by
        simp_rw [hrow]
        exact tsum_majorant_eq hP (by linarith) S c
    _ = (∑ n ∈ S, c n * conj (c n) * pairRowSum P Y n n).re +
          (offDiagonalSum P W D Y).re := by
        rw [sum_sum_eq_diag_add, Complex.add_re, hoffS]
    _ ≤ A * R' * M ^ 2 * CP * (D * Y) + Coff * D ^ (2 + θ + ε) :=
        add_le_add ((Complex.re_le_norm _).trans hdiag) (hoff D hD)
    _ ≤ (A * R' * M ^ 2 * CP + Coff) * D ^ (2 + θ + ε) := by
        rw [add_mul]
        gcongr

end Masullo.QRH.MeanSquare
