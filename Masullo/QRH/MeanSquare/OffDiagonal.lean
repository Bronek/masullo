import Masullo.QRH.MeanSquare.Transfer
import Masullo.QRH.MeanSquare.DilatedSeparation
import Masullo.QRH.MeanSquare.FirstPoisson

/-!
# Toward the off-diagonal estimate

Pieces of the bound `OffDiagonalEstimate rowMajorant` from `GapEstimate`.

* `residueMultiplicative` discharges the residue hypotheses of the exclusion shift
  `dualMeanSquareCoprime_le`.
* `offDiagonalEstimate_of_dualTail` bounds the off-diagonal sum by the full weighted square,
  whose diagonal is nonnegative. It indexes the square by the gcd splits `(g, z₁, z₂)` of the
  pairs of columns and evaluates each term by primitive Poisson. The zero frequency survives
  only on the diagonal `z₁ = z₂ = 1` and costs `O(D^(1+ε) Y)`. What remains is
  `DualTailEstimate`, the bound on the nonzero frequencies `h ≠ 0` of all gcd splits.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The generator and the sextic symbol are multiplicative away from `6`. -/
theorem residueMultiplicative : ResidueMultiplicative :=
  ⟨generator_mul, fun h6 a b => powerResidueSymbol_six_mul h6 a b⟩


/-! ### The zero frequency of the dual sums -/

/-- The dual lattice sums of a Schwartz weight converge. -/
lemma summable_gaoZhaoTransform (P : SchwartzMap ℝ ℂ) {X : ℝ} (hX : 0 < X) :
    Summable fun h : 𝓔 => gaoZhaoTransform P (Real.sqrt (X * elementNorm h)) := by
  obtain ⟨s, -, hs⟩ := gaoZhaoLemma23 P X hX 0 1 one_ne_zero
  convert hs.summable using 2 with k
  simp [elementNorm_eq_normSq, differentCharacter, mul_comm]

/-- The paired character vanishes at zero unless both of its ideals are trivial. -/
lemma pairCharacter_zero {b c : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c)
    (h : b ≠ ⊤ ∨ c ≠ ⊤) : pairCharacter b c 0 = 0 := by
  refine pairCharacter_eq_zero hb hc fun hco => ?_
  rw [span_singleton_eq_bot.mpr rfl, isCoprime_iff_sup_eq, sup_bot_eq] at hco
  rcases h with h | h
  · exact h (eq_top_iff.mpr (hco ▸ Ideal.mul_le_left))
  · exact h (eq_top_iff.mpr (hco ▸ Ideal.mul_le_right))

open Classical in
/-- The nonzero frequencies `h ≠ 0` of `dualExclusion`. -/
def dualExclusionTail (P : SchwartzMap ℝ ℂ) (Y : ℝ) (b c g : Ideal 𝓔) : ℂ :=
  ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g},
    (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e.val : ℂ) *
      ∑' h : 𝓔, if h = 0 then 0 else conj (pairCharacter b c h) * gaoZhaoTransform P
        (Real.sqrt (Y * elementNorm h / ((absNorm e.val : ℝ) * absNorm (b * c))))

lemma norm_pairCharacter_le (b c : Ideal 𝓔) (x : 𝓔) : ‖pairCharacter b c x‖ ≤ 1 := by
  rw [pairCharacter, norm_mul, Complex.norm_conj]
  exact (mul_le_mul (norm_sextic_le_one _ _) (norm_sextic_le_one _ _) (norm_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

/-- `dualExclusion` is its zero frequency plus its nonzero frequencies. -/
lemma dualExclusion_eq_add {b c g : Ideal 𝓔} (hb : AwayFromSix b) (hc : AwayFromSix c)
    (hg : Starred g) (P : SchwartzMap ℝ ℂ) {Y : ℝ} (hY : 0 < Y) :
    dualExclusion P Y b c g = dualExclusionTail P Y b c g +
      (∑ᶠ e : {e : Ideal 𝓔 // e ∣ g},
        (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e.val : ℂ)) *
        (conj (pairCharacter b c 0) * gaoZhaoTransform P 0) := by
  classical
  have hbc : (0 : ℝ) < absNorm (b * c) := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr (mul_ne_zero hb.1 hc.1))
  have hsplit : ∀ e : Ideal 𝓔, e ≠ ⊥ →
      (∑' h : 𝓔, conj (pairCharacter b c h) * gaoZhaoTransform P
        (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))) =
      conj (pairCharacter b c 0) * gaoZhaoTransform P 0 +
        ∑' h : 𝓔, if h = 0 then 0 else conj (pairCharacter b c h) * gaoZhaoTransform P
          (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c)))) := by
    intro e he
    have he0 : (0 : ℝ) < absNorm e := by
      exact_mod_cast Nat.pos_of_ne_zero
        (absNorm_eq_zero_iff.not.mpr he)
    have hX : 0 < Y / ((absNorm e : ℝ) * absNorm (b * c)) := by positivity
    have hs : Summable fun h : 𝓔 => conj (pairCharacter b c h) * gaoZhaoTransform P
        (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c)))) := by
      refine Summable.of_norm_bounded (summable_gaoZhaoTransform P hX).norm fun h => ?_
      rw [norm_mul, Complex.norm_conj, mul_div_right_comm]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_pairCharacter_le b c h)
    rw [hs.tsum_eq_add_tsum_ite 0]
    simp [elementNorm]
  rw [dualExclusion, dualExclusionTail]
  rw [finsum_dvd_eq_sum hg.2 (fun e => (idealMoebius e : ℂ) * pairCharacter b c (generator e) /
      (absNorm e : ℂ) * ∑' h : 𝓔, conj (pairCharacter b c h) * gaoZhaoTransform P
        (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))),
    finsum_dvd_eq_sum hg.2 (fun e => (idealMoebius e : ℂ) * pairCharacter b c (generator e) /
      (absNorm e : ℂ) * ∑' h : 𝓔, if h = 0 then 0 else conj (pairCharacter b c h) *
        gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))),
    finsum_dvd_eq_sum hg.2
      (fun e => (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e : ℂ)),
      Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hsplit _ (Finset.prod_ne_zero_iff.mpr fun P hP =>
    (prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_powerset.mp hs hP))).ne_zero)]
  ring

/-! ### The full square -/

lemma re_pairRowSum_self_nonneg {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) {Y : ℝ}
    (hY : 0 < Y) (n : Ideal 𝓔) : 0 ≤ (pairRowSum P Y n n).re := by
  rw [pairRowSum, Complex.re_tsum (summable_pairRow P hY n n)]
  refine tsum_nonneg fun y => ?_
  rw [Complex.mul_conj, Complex.re_mul_ofReal]
  exact mul_nonneg (hP.re_nonneg _ (by positivity)) (Complex.normSq_nonneg _)

/-- The off-diagonal sum is at most the full weighted square, whose diagonal is nonnegative. -/
lemma re_offDiagonalSum_le {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) {W : ℝ → ℂ}
    {D Y : ℝ} (hY : 0 < Y) {S : Finset (Ideal 𝓔)} (hcS : ∀ n ∉ S, moebiusCoeff W D n = 0) :
    (offDiagonalSum P W D Y).re ≤
      (∑ n₁ ∈ S, ∑ n₂ ∈ S, moebiusCoeff W D n₁ *
        conj (moebiusCoeff W D n₂) * pairRowSum P Y n₁ n₂).re := by
  classical
  set c := moebiusCoeff W D
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
  rw [sum_sum_eq_diag_add, Complex.add_re, hoffS]
  refine le_add_of_nonneg_left ?_
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun n _ => ?_
  rw [Complex.mul_conj, Complex.re_ofReal_mul]
  exact mul_nonneg (Complex.normSq_nonneg _) (re_pairRowSum_self_nonneg hP hY n)

/-! ### The gcd splits -/

/-- The gcd splits `(g, z₁, z₂)`: the starred ideals `g z₁` and `g z₂` with greatest common
divisor `g`. -/
def IsGcdSplit (t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : Prop :=
  Starred t.1 ∧ Starred t.2.1 ∧ Starred t.2.2 ∧ IsCoprime t.2.1 t.2.2 ∧
    IsCoprime t.1 (t.2.2 * t.2.1)

lemma gcd_mul_eq_of_isCoprime {g z₁ z₂ : Ideal 𝓔} (h : IsCoprime z₁ z₂) :
    gcd (g * z₁) (g * z₂) = g := by
  rw [gcd_mul_left, isCoprime_iff_gcd.mp h, mul_one, normalize_eq]

/-- A gcd split is determined by its pair of columns. -/
lemma isGcdSplit_injOn :
    Set.InjOn (fun t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 => (t.1 * t.2.1, t.1 * t.2.2))
      {t | IsGcdSplit t} := by
  rintro ⟨g, z₁, z₂⟩ ⟨hg, -, -, h12, -⟩ ⟨g', z₁', z₂'⟩ ⟨-, -, -, h12', -⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  obtain rfl : g = g' := by
    rw [← gcd_mul_eq_of_isCoprime (g := g) h12, h₁, h₂, gcd_mul_eq_of_isCoprime h12']
  exact Prod.ext rfl (Prod.ext (mul_left_cancel₀ hg.1.1 h₁) (mul_left_cancel₀ hg.1.1 h₂))

lemma absNorm_le_absNorm_mul {I J : Ideal 𝓔} (h : I * J ≠ ⊥) :
    (absNorm I : ℝ) ≤ absNorm (I * J) ∧ (absNorm J : ℝ) ≤ absNorm (I * J) := by
  have hI : 1 ≤ absNorm I := Nat.one_le_iff_ne_zero.mpr
    (absNorm_eq_zero_iff.not.mpr (left_ne_zero_of_mul h))
  have hJ : 1 ≤ absNorm J := Nat.one_le_iff_ne_zero.mpr
    (absNorm_eq_zero_iff.not.mpr (right_ne_zero_of_mul h))
  rw [map_mul]
  exact ⟨by exact_mod_cast Nat.le_mul_of_pos_right _ hJ,
    by exact_mod_cast Nat.le_mul_of_pos_left _ hI⟩

/-- The nonzero frequencies of the correlation of the columns `g z₁` and `g z₂` of a gcd split
`t = (g, z₁, z₂)`, with the Möbius weights turned into Gauss coefficients through a correction
`A` modulo `72` as in `moebiusCoeff_mul_pairRowSum`. -/
def dualTailTerm (P : SchwartzMap ℝ ℂ) (A : (𝓔 ⧸ span {(72 : 𝓔)}) → (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ)
    (W : ℝ → ℂ) (D Y : ℝ) (t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : ℂ :=
  W (absNorm (t.1 * t.2.1) / D) * conj (W (absNorm (t.1 * t.2.2) / D)) *
    ((Y : ℂ) / Real.sqrt (absNorm (t.2.2 * t.2.1))) *
    (gaussCoefficient t.2.2 * conj (gaussCoefficient t.2.1) *
      A (Ideal.Quotient.mk _ (generator t.2.2)) (Ideal.Quotient.mk _ (generator t.2.1))) *
    dualExclusionTail P Y t.2.2 t.2.1 t.1

/-- The nonzero frequencies of the full weighted square, summed over the gcd splits. -/
def dualTailSum (P : SchwartzMap ℝ ℂ)
    (A : (𝓔 ⧸ span {(72 : 𝓔)}) → (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ) (W : ℝ → ℂ) (D Y : ℝ) : ℂ :=
  ∑ᶠ t ∈ {t | IsGcdSplit t}, dualTailTerm P A W D Y t

/-- The bound on the nonzero frequencies of the full square at `Y = D^(1+θ)`, for every
correction `A`. The zero frequency is the diagonal `z₁ = z₂ = 1` and costs `O(D^(1+ε) Y)`. -/
def DualTailEstimate (P : SchwartzMap ℝ ℂ) : Prop :=
  ∀ A : (𝓔 ⧸ span {(72 : 𝓔)}) → (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ,
    ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 10 → ∀ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ D : ℝ, 2 ≤ D →
        ‖dualTailSum P A W D (D ^ (1 + θ))‖ ≤ C * D ^ (2 + θ + ε)

lemma norm_idealMoebius_le (e : Ideal 𝓔) : ‖(idealMoebius e : ℂ)‖ ≤ 1 := by
  unfold idealMoebius
  split_ifs <;> simp

lemma norm_div_natCast_le (x : ℂ) (n : ℕ) : ‖x / (n : ℂ)‖ ≤ ‖x‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [norm_div, Complex.norm_natCast]
    exact div_le_self (norm_nonneg _) (by exact_mod_cast hn)

/-- A sum over the `2^{ω(g)}` divisors of a squarefree `g` of terms of norm at most `B`. -/
lemma norm_finsum_dvd_le_of {g : Ideal 𝓔} (hg : Squarefree g) (f : Ideal 𝓔 → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ e, e ∣ g → ‖f e‖ ≤ B) :
    ‖∑ᶠ e : {e : Ideal 𝓔 // e ∣ g}, f e‖ ≤ (2 : ℝ) ^ Multiset.card (normalizedFactors g) * B := by
  classical
  have hdvd : ∀ s ∈ (normalizedFactors g).toFinset.powerset, ∏ P ∈ s, P ∣ g := by
    intro s hs
    refine (Finset.prod_dvd_prod_of_subset _ _ id (Finset.mem_powerset.mp hs)).trans ?_
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.map_id]
    exact (Multiset.prod_dvd_prod_of_le (Multiset.dedup_le _)).trans
      (prod_normalizedFactors hg.ne_zero).dvd
  rw [finsum_dvd_eq_sum hg f]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ s ∈ (normalizedFactors g).toFinset.powerset, ‖f (∏ P ∈ s, P)‖
      ≤ ∑ _s ∈ (normalizedFactors g).toFinset.powerset, B :=
        Finset.sum_le_sum fun s hs => hf _ (hdvd s hs)
    _ = (2 : ℝ) ^ (normalizedFactors g).toFinset.card * B := by simp
    _ ≤ _ := by
        gcongr
        · norm_num
        · exact Multiset.toFinset_card_le _

/-- The Möbius divisor sum of the zero frequency has `2^{ω(g)}` terms of norm at most one. -/
lemma norm_finsum_dvd_le {g : Ideal 𝓔} (hg : Squarefree g) (b c : Ideal 𝓔) :
    ‖∑ᶠ e : {e : Ideal 𝓔 // e ∣ g},
        (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e.val : ℂ)‖ ≤
      (2 : ℝ) ^ Multiset.card (normalizedFactors g) := by
  refine (norm_finsum_dvd_le_of hg
    (fun e => (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e : ℂ)) zero_le_one
    fun e _ => ?_).trans_eq
    (mul_one _)
  refine (norm_div_natCast_le _ _).trans ?_
  rw [norm_mul]
  exact (mul_le_mul (norm_idealMoebius_le _) (norm_pairCharacter_le _ _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-! ### The off-diagonal estimate from the nonzero frequencies -/

/-- `OffDiagonalEstimate` follows from the bound on the nonzero frequencies of the full square.
The first clause of `PairedGaussIdentities` supplies the correction `A`. -/
theorem offDiagonalEstimate_of_dualTail {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P)
    (hpg : PairedGaussIdentities) (htail : DualTailEstimate P) : OffDiagonalEstimate P := by
  classical
  obtain ⟨A, B, hAB⟩ := hpg
  have hA : ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      (idealMoebius b : ℂ) * idealMoebius c * pairGauss b c =
        gaussCoefficient b * conj (gaussCoefficient c) *
          A (Ideal.Quotient.mk _ (generator b)) (Ideal.Quotient.mk _ (generator c)) :=
    fun b c hb hc hbc => (hAB b c hb hc hbc).1
  intro W hW hc hs θ hθ hθ' ε hε
  obtain ⟨Ct, hCt, htail⟩ := htail A W hW hc hs θ hθ hθ' ε hε
  obtain ⟨M, hM⟩ := hW.continuous.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  obtain ⟨A₀, hA₀⟩ := exists_card_idealsLe_le
  obtain ⟨Cτ, hCτ, hτ⟩ := two_pow_card_normalizedFactors_le hε
  set R' := max R 1
  set K₀ := ‖gaussCoefficient ⊤‖ ^ 2 *
    ‖A (Ideal.Quotient.mk _ (generator ⊤)) (Ideal.Quotient.mk _ (generator ⊤))‖ *
    ‖gaoZhaoTransform P 0‖
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hA₀' : 0 ≤ A₀ := by
    have := hA₀ 1 le_rfl
    nlinarith [(Finset.card_pos.mpr ⟨⊤, (mem_idealsLe zero_le_one).mpr (by simp)⟩ :
      0 < (idealsLe 1).card)]
  have hR' : 1 ≤ R' := le_max_right R 1
  have hWz : ∀ x, W x ≠ 0 → x ≤ R' := fun x hx => by
    by_contra hlt
    exact hx (image_eq_zero_of_notMem_tsupport fun h => by
      linarith [hR h, le_max_left R 1, lt_of_not_ge hlt])
  refine ⟨Ct + A₀ * R' ^ (1 + ε) * M ^ 2 * K₀ * Cτ, by positivity, fun D hD => ?_⟩
  have hD₀ : 0 < D := by linarith
  set Y := D ^ (1 + θ) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hD₀ _
  set X := R' * D
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hR' (by linarith)
  have hX₀ : 0 ≤ X := by linarith
  set S := (idealsLe X).filter Starred
  set c := moebiusCoeff W D
  have hWX : ∀ n : Ideal 𝓔, W (absNorm n / D) ≠ 0 → (absNorm n : ℝ) ≤ X := fun n h => by
    have := hWz _ h
    rwa [div_le_iff₀ hD₀] at this
  have hcS : ∀ n ∉ S, c n = 0 := by
    intro n hn
    simp only [c, moebiusCoeff]
    split_ifs with h
    · by_contra hne
      exact hn (Finset.mem_filter.mpr
        ⟨(mem_idealsLe hX₀).mpr (hWX n (right_ne_zero_of_mul hne)), h⟩)
    · rfl
  -- The gcd splits with all three norms at most `X`.
  set T := ((idealsLe X) ×ˢ ((idealsLe X) ×ˢ (idealsLe X))).filter IsGcdSplit
  have hmemT : ∀ t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔, IsGcdSplit t →
      (absNorm (t.1 * t.2.1) : ℝ) ≤ X → (absNorm (t.1 * t.2.2) : ℝ) ≤ X → t ∈ T := by
    rintro ⟨g, z₁, z₂⟩ ht h₁ h₂
    have hn₁ : g * z₁ ≠ ⊥ := mul_ne_zero ht.1.1.1 ht.2.1.1.1
    have hn₂ : g * z₂ ≠ ⊥ := mul_ne_zero ht.1.1.1 ht.2.2.1.1.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_idealsLe hX₀).mpr ((absNorm_le_absNorm_mul hn₁).1.trans h₁), Finset.mem_product.mpr
        ⟨(mem_idealsLe hX₀).mpr ((absNorm_le_absNorm_mul hn₁).2.trans h₁),
          (mem_idealsLe hX₀).mpr ((absNorm_le_absNorm_mul hn₂).2.trans h₂)⟩⟩, ht⟩
  set F : Ideal 𝓔 × Ideal 𝓔 → ℂ := fun p => c p.1 * conj (c p.2) * pairRowSum P Y p.1 p.2
  have hFne : ∀ p, F p ≠ 0 → c p.1 ≠ 0 ∧ c p.2 ≠ 0 := fun p h =>
    ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h),
      fun h' => right_ne_zero_of_mul (left_ne_zero_of_mul h) (by rw [h', map_zero])⟩
  have hfull : ∑ n₁ ∈ S, ∑ n₂ ∈ S, c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂ =
      ∑ t ∈ T, F (t.1 * t.2.1, t.1 * t.2.2) := by
    rw [← Finset.sum_product' (f := fun n₁ n₂ => c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂)]
    symm
    refine Finset.sum_bij_ne_zero (fun t _ _ => (t.1 * t.2.1, t.1 * t.2.2)) ?_ ?_ ?_ ?_
    · intro t _ h
      obtain ⟨h₁, h₂⟩ := hFne _ h
      by_contra hn
      rw [Finset.mem_product, not_and_or] at hn
      rcases hn with hn | hn
      · exact h₁ (hcS _ hn)
      · exact h₂ (hcS _ hn)
    · intro t₁ ht₁ _ t₂ ht₂ _ h
      exact isGcdSplit_injOn (Finset.mem_filter.mp ht₁).2 (Finset.mem_filter.mp ht₂).2 h
    · rintro ⟨n₁, n₂⟩ hp h
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
      obtain ⟨hn₁, hs₁⟩ := Finset.mem_filter.mp hp₁
      obtain ⟨hn₂, hs₂⟩ := Finset.mem_filter.mp hp₂
      obtain ⟨g, z₁, z₂, rfl, rfl, hg, h₁, h₂, h12, hgz⟩ := exists_gcd_split hs₁ hs₂
      exact ⟨(g, z₁, z₂), hmemT _ ⟨hg, h₁, h₂, h12, hgz⟩ ((mem_idealsLe hX₀).mp hn₁)
        ((mem_idealsLe hX₀).mp hn₂), h, rfl⟩
    · intro t _ _
      rfl
  -- Each gcd split is a nonzero-frequency term plus a zero-frequency term.
  set Z : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → ℂ := fun t =>
    W (absNorm (t.1 * t.2.1) / D) * conj (W (absNorm (t.1 * t.2.2) / D)) *
      ((Y : ℂ) / Real.sqrt (absNorm (t.2.2 * t.2.1))) *
      (gaussCoefficient t.2.2 * conj (gaussCoefficient t.2.1) *
        A (Ideal.Quotient.mk _ (generator t.2.2)) (Ideal.Quotient.mk _ (generator t.2.1))) *
      ((∑ᶠ e : {e : Ideal 𝓔 // e ∣ t.1},
        (idealMoebius e : ℂ) * pairCharacter t.2.2 t.2.1 (generator e) / (absNorm e.val : ℂ)) *
        (conj (pairCharacter t.2.2 t.2.1 0) * gaoZhaoTransform P 0))
  have hsplit : ∀ t ∈ T, F (t.1 * t.2.1, t.1 * t.2.2) = dualTailTerm P A W D Y t + Z t := by
    rintro ⟨g, z₁, z₂⟩ ht
    obtain ⟨hg, h₁, h₂, h12, hgz⟩ := (Finset.mem_filter.mp ht).2
    simp only [F, c, Z, dualTailTerm]
    rw [moebiusCoeff_mul_pairRowSum hA P W hY hg h₁ h₂ h12 hgz,
      dualExclusion_eq_add h₂.1 h₁.1 hg P hY]
    ring
  have htailT : dualTailSum P A W D Y = ∑ t ∈ T, dualTailTerm P A W D Y t := by
    refine finsum_mem_eq_sum_of_subset _ (fun t ht => ?_) fun t ht =>
      (Finset.mem_filter.mp ht).2
    obtain ⟨ht, hne⟩ := ht
    have hne' := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
    refine hmemT t ht (hWX _ (left_ne_zero_of_mul hne')) (hWX _ fun h => ?_)
    exact right_ne_zero_of_mul hne' (by rw [h, map_zero])
  -- The zero frequency lives on the diagonal `z₁ = z₂ = 1`.
  have hZ : ∀ t ∈ T, ‖Z t‖ ≤ if t.2 = (⊤, ⊤) then M ^ 2 * Y * K₀ * (Cτ * X ^ ε) else 0 := by
    rintro ⟨g, z₁, z₂⟩ ht
    obtain ⟨hbox, hg, h₁, h₂, -, -⟩ := Finset.mem_filter.mp ht
    split_ifs with htop
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj htop
      have hgX : (absNorm g : ℝ) ≤ X :=
        (mem_idealsLe hX₀).mp (Finset.mem_product.mp hbox).1
      have hτg : (2 : ℝ) ^ Multiset.card (normalizedFactors g) ≤ Cτ * X ^ ε :=
        (hτ g hg.1.1 hg.2).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hgX hε.le) hCτ)
      simp only [Z, mul_top, absNorm_top, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one,
        div_one]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_conj, Complex.norm_conj, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg hY.le]
      have hp0 := norm_pairCharacter_le ⊤ ⊤ 0
      have hf := norm_finsum_dvd_le hg.2 ⊤ ⊤
      calc ‖W (absNorm g / D)‖ * ‖W (absNorm g / D)‖ * Y *
            (‖gaussCoefficient ⊤‖ * ‖gaussCoefficient ⊤‖ *
              ‖A (Ideal.Quotient.mk _ (generator ⊤)) (Ideal.Quotient.mk _ (generator ⊤))‖) *
            (‖∑ᶠ e : {e : Ideal 𝓔 // e ∣ g}, (idealMoebius e : ℂ) *
              pairCharacter ⊤ ⊤ (generator e) / (absNorm e.val : ℂ)‖ *
              (‖pairCharacter ⊤ ⊤ 0‖ * ‖gaoZhaoTransform P 0‖))
          ≤ M * M * Y * (‖gaussCoefficient ⊤‖ * ‖gaussCoefficient ⊤‖ *
              ‖A (Ideal.Quotient.mk _ (generator ⊤)) (Ideal.Quotient.mk _ (generator ⊤))‖) *
            ((Cτ * X ^ ε) * (1 * ‖gaoZhaoTransform P 0‖)) := by
            gcongr
            · exact hM _
            · exact hM _
            · exact hf.trans hτg
        _ = M ^ 2 * Y * K₀ * (Cτ * X ^ ε) := by simp only [K₀]; ring
    · have hz : z₂ ≠ ⊤ ∨ z₁ ≠ ⊤ := by
        by_contra hz
        push Not at hz
        exact htop (by rw [hz.1, hz.2])
      simp [Z, pairCharacter_zero h₂.1 h₁.1 hz]
  have hcard : ((T.filter fun t => t.2 = (⊤, ⊤)).card : ℝ) ≤ A₀ * X := by
    refine le_trans ?_ (hA₀ X hX)
    exact_mod_cast Finset.card_le_card_of_injOn (fun t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 => t.1)
      (fun t ht =>
        (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1).1)
      (fun t₁ ht₁ t₂ ht₂ h => Prod.ext h
        (((Finset.mem_filter.mp ht₁).2 : t₁.2 = (⊤, ⊤)).trans
          ((Finset.mem_filter.mp ht₂).2 : t₂.2 = (⊤, ⊤)).symm))
  have hZsum : ‖∑ t ∈ T, Z t‖ ≤ A₀ * R' ^ (1 + ε) * M ^ 2 * K₀ * Cτ * D ^ (2 + θ + ε) := by
    have hK₀ : 0 ≤ K₀ := by positivity
    calc ‖∑ t ∈ T, Z t‖ ≤ ∑ t ∈ T, ‖Z t‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ T, if t.2 = (⊤, ⊤) then M ^ 2 * Y * K₀ * (Cτ * X ^ ε) else 0 :=
          Finset.sum_le_sum hZ
      _ = (T.filter fun t => t.2 = (⊤, ⊤)).card * (M ^ 2 * Y * K₀ * (Cτ * X ^ ε)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ A₀ * X * (M ^ 2 * Y * K₀ * (Cτ * X ^ ε)) := by gcongr
      _ = A₀ * (R' * R' ^ ε) * M ^ 2 * K₀ * Cτ * (D * Y * D ^ ε) := by
          rw [Real.mul_rpow (by linarith) hD₀.le]
          ring
      _ = _ := by
          rw [← Real.rpow_one_add' (by linarith) (by linarith), hYdef,
            ← Real.rpow_one_add' hD₀.le (by linarith), ← Real.rpow_add hD₀]
          ring_nf
  calc (offDiagonalSum P W D Y).re
      ≤ (∑ n₁ ∈ S, ∑ n₂ ∈ S, c n₁ * conj (c n₂) * pairRowSum P Y n₁ n₂).re :=
        re_offDiagonalSum_le hP hY hcS
    _ = (dualTailSum P A W D Y + ∑ t ∈ T, Z t).re := by
        rw [hfull, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, htailT]
    _ ≤ ‖dualTailSum P A W D Y‖ + ‖∑ t ∈ T, Z t‖ :=
        (Complex.re_le_norm _).trans (norm_add_le _ _)
    _ ≤ Ct * D ^ (2 + θ + ε) + A₀ * R' ^ (1 + ε) * M ^ 2 * K₀ * Cτ * D ^ (2 + θ + ε) :=
        add_le_add (htail D hD) hZsum
    _ = _ := by ring

/-- `FullRowEstimate` follows from the bound on the nonzero frequencies for `rowMajorant`. -/
theorem fullRowEstimate_of_dualTail (hpg : PairedGaussIdentities)
    (htail : DualTailEstimate rowMajorant) : FullRowEstimate :=
  fullRowEstimate_of_offDiagonalEstimate
    (offDiagonalEstimate_of_dualTail isRowMajorant_rowMajorant hpg htail)

end Masullo.QRH.MeanSquare
