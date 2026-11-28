import Masullo.QRH.MeanSquare.Poisson
import Masullo.QRH.MeanSquare.UnitRows

/-!
# Steps toward the transfer estimate

Two finite ingredients of `TransferEstimate`, the transfer of OpenAI, *The Quasi-Riemann
Hypothesis* (5 October 2026), Proposition 5.4, (5.10)–(5.12), p. 21.

* `dualMeanSquare_le_mul` is the direct count `E(K,X,F) ≤ C K X`. It settles the transfer
  when `KL ≤ Σ` (`dualMeanSquare_le_of_mul_le`) and bounds the children of length below one.
* `dualMeanSquareCoprime_le` is the exclusion shift (2) of the audit's manuscript,
  `E_r(K,X,F) ≤ τ(r) Σ_{j ∣ r} E(K, X/Nj, F Nj)`, with the divisors `j` of the squarefree `r`
  indexed by the sub-multisets of its prime factors. Its proof removes one prime at a time
  (`dualMeanSquareCoprime_mul_prime_le`) using the coprime product law of
  `PairedGaussIdentities` and the residue facts collected in `ResidueMultiplicative`.
* `two_pow_card_normalizedFactors_le` bounds the cost `2^{ω(r)} = τ(r)` of the shift by
  `C_s (Nr)^s` for squarefree `r`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-! ### Direct counting -/

/-- The element rows of norm at most `K ≥ 1` number `O(K)`. -/
lemma exists_card_elementRows_le :
    ∃ A ≥ (0 : ℝ), ∀ K : ℝ, 1 ≤ K → ((elementRows K).card : ℝ) ≤ A * K := by
  classical
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  have hA₀ : 0 ≤ A := by
    have := hA 1 le_rfl
    linarith [(Nat.cast_nonneg (idealsLe 1).card : (0 : ℝ) ≤ _)]
  refine ⟨A * Nat.card 𝓔ˣ, by positivity, fun K hK => ?_⟩
  have hcard : (elementRows K).card ≤ (idealsLe K).card * Nat.card 𝓔ˣ := by
    have huniv (inst : Fintype 𝓔ˣ) : (@Finset.univ _ inst).card = Nat.card 𝓔ˣ := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card]
    unfold elementRows
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun a _ => Finset.card_image_le.trans_eq (huniv _)).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset _ _))
  calc ((elementRows K).card : ℝ) ≤ (idealsLe K).card * Nat.card 𝓔ˣ := by exact_mod_cast hcard
    _ ≤ A * K * Nat.card 𝓔ˣ := by gcongr; exact hA K hK
    _ = _ := by ring

/-- A column of length `X > 0` has at most `A R X` nonzero terms of modulus at most one,
where `R` bounds the support of the test and `A` is the ideal-counting constant. -/
lemma norm_columnSum_le_mul (hg : GaussCoefficientBound) {A R X : ℝ}
    (hA : ∀ x : ℝ, 1 ≤ x → ((idealsLe x).card : ℝ) ≤ A * x) (hA₀ : 0 ≤ A) (hR : 0 ≤ R)
    {W : ℝ → ℂ} (hW : ∀ x, W x ≠ 0 → x ≤ R) (hW₁ : ∀ x, ‖W x‖ ≤ 1) (hX : 0 < X)
    (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) :
    ‖columnSum ξ W X k f‖ ≤ A * (R * X) := by
  classical
  let s := idealsLe (R * X)
  let t := s.preimage (Subtype.val : {n : Ideal 𝓔 // Starred n} → Ideal 𝓔)
    Subtype.val_injective.injOn
  have hsupp : (Function.support fun n : {n : Ideal 𝓔 // Starred n} =>
      gaussCoefficient n * twist ξ k f n * W (absNorm n.1 / X)) ⊆ t := by
    intro n hn
    apply Finset.mem_preimage.mpr
    apply (mem_idealsLe (by positivity)).mpr
    have hy : W (absNorm n.1 / X) ≠ 0 := right_ne_zero_of_mul (Function.mem_support.mp hn)
    exact (div_le_iff₀ hX).mp (hW _ hy)
  unfold columnSum
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hterm : ∀ n ∈ t, ‖gaussCoefficient n * twist ξ k f n * W (absNorm n.1 / X)‖ ≤ 1 :=
    fun n _ => by
      simp only [norm_mul]
      have hcoef := (mul_le_of_le_one_left (norm_nonneg _) (hg n n.2)).trans
        (norm_twist_le_one ξ k f n)
      exact (mul_le_of_le_one_left (norm_nonneg _) hcoef).trans (hW₁ _)
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 hterm).trans ?_)
  rw [nsmul_eq_mul, mul_one]
  rcases t.eq_empty_or_nonempty with ht | ⟨n, hn⟩
  · rw [ht, Finset.card_empty, Nat.cast_zero]
    positivity
  have hn₁ : (1 : ℝ) ≤ absNorm n.1 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr n.2.1.1)
  have hRX : 1 ≤ R * X := hn₁.trans ((mem_idealsLe (by positivity)).mp (Finset.mem_preimage.mp hn))
  calc (t.card : ℝ) ≤ s.card := by
        exact_mod_cast Finset.card_le_card_of_injOn Subtype.val
          (fun n hn => Finset.mem_preimage.mp hn) Subtype.val_injective.injOn
    _ ≤ A * (R * X) := hA _ hRX

/-- Direct counting: `E(K,X,F) ≤ C K X` for every positive length `X`. -/
theorem dualMeanSquare_le_mul (hg : GaussCoefficientBound) (I : TestInterval) :
    ∃ C ≥ (0 : ℝ), ∀ (K X F : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
      1 ≤ K → 0 < X → 1 ≤ F → UnitTest I 0 W → dualMeanSquare ξ W K X F ≤ C * (K * X) := by
  classical
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  have hA₀ : 0 ≤ A := by
    have := hA 1 le_rfl
    linarith [(Nat.cast_nonneg (idealsLe 1).card : (0 : ℝ) ≤ _)]
  obtain ⟨Ar, hAr₀, hAr⟩ := exists_card_elementRows_le
  let R := max I.hi 1
  have hR : 1 ≤ R := le_max_right _ _
  refine ⟨2 * A * Ar * (A * R) ^ 2, by positivity, ?_⟩
  intro K X F ξ W hK hX hF hW
  have hsub {y : ℝ} (hy : W y ≠ 0) : y ∈ Set.Icc I.lo I.hi := hW.2.1 (subset_tsupport W hy)
  have hnorm (y : ℝ) : ‖W y‖ ≤ 1 := by
    by_cases hy : W y = 0
    · simp [hy]
    · simpa using hW.2.2 0 le_rfl y (hsub hy)
  have hcol (k : 𝓔) (f : Ideal 𝓔) : ‖columnSum ξ W X k f‖ ≤ A * (R * X) :=
    norm_columnSum_le_mul hg hA hA₀ (by linarith) (fun x hx => (hsub hx).2.trans
      (le_max_left _ _)) hnorm hX ξ k f
  have hinner (f : Ideal 𝓔) : (∑ k ∈ elementRows K, ‖columnSum ξ W X k f‖ ^ 2) ≤
      Ar * K * (A * (R * X)) ^ 2 := by
    refine (Finset.sum_le_card_nsmul (elementRows K) (fun k => ‖columnSum ξ W X k f‖ ^ 2)
      ((A * (R * X)) ^ 2) (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hcol k f) 2)).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hAr K hK) (by positivity)
  unfold dualMeanSquare
  refine (div_le_iff₀ (by positivity)).mpr ?_
  calc
    _ ≤ ∑ _ ∈ _, Ar * K * (A * (R * X)) ^ 2 := Finset.sum_le_sum fun f _ => hinner f
    _ ≤ A * (2 * F) * (Ar * K * (A * (R * X)) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact (Nat.cast_le.mpr (Finset.card_filter_le ..)).trans (hA _ (by linarith))
    _ = _ := by ring

/-- The transfer in the range `KL ≤ Σ`, by direct counting alone. -/
theorem dualMeanSquare_le_of_mul_le (hg : GaussCoefficientBound) (I : TestInterval) :
    ∃ C ≥ (0 : ℝ), ∀ (K L F target : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
      1 ≤ K → 0 < L → 1 ≤ F → K * L ≤ target → UnitTest I 0 W →
      dualMeanSquare ξ W K L F ≤ C * target := by
  obtain ⟨C, hC, h⟩ := dualMeanSquare_le_mul hg I
  exact ⟨C, hC, fun K L F target ξ W hK hL hF hKL hW =>
    (h K L F ξ W hK hL hF hW).trans (mul_le_mul_of_nonneg_left hKL hC)⟩

/-! ### The exclusion shift -/

/-- Multiplicativity of the primary generators and of the sextic symbol in its numerator.
These are the residue facts the exclusion shift needs. -/
structure ResidueMultiplicative : Prop where
  generator_mul : ∀ {I J : Ideal 𝓔}, IsCoprime I (span {3}) → IsCoprime J (span {3}) →
    generator (I * J) = generator I * generator J
  six_mul : ∀ {n : Ideal 𝓔}, IsCoprime n (span {6}) → ∀ a b : 𝓔,
    powerResidueSymbol 6 (a * b) n = powerResidueSymbol 6 a n * powerResidueSymbol 6 b n

/-- The squarefree column restricted to the `n` coprime to `r`. -/
def columnSumCoprime (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔) (f r : Ideal 𝓔) : ℂ :=
  open Classical in
  ∑ᶠ n : {n : Ideal 𝓔 // Starred n},
    if IsCoprime n.1 r then gaussCoefficient n * twist ξ k f n * W (absNorm n.1 / X) else 0

/-- The form `E_r(K,X,F)`: the form `E(K,X,F)` with columns restricted to `(n, r) = 1`. -/
def dualMeanSquareCoprime (ξ : RayCharacter) (W : ℝ → ℂ) (K X F : ℝ) (r : Ideal 𝓔) : ℝ :=
  open Classical in
  (∑ f ∈ (idealsLe (2 * F)).filter (fun f =>
      Starred f ∧ F ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * F),
    ∑ k ∈ elementRows K, ‖columnSumCoprime ξ W X k f r‖ ^ 2) / (X * F)

lemma dualMeanSquareCoprime_top (ξ : RayCharacter) (W : ℝ → ℂ) (K X F : ℝ) :
    dualMeanSquareCoprime ξ W K X F ⊤ = dualMeanSquare ξ W K X F := by
  have h (n : Ideal 𝓔) : IsCoprime n ⊤ := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_right
  simp [dualMeanSquareCoprime, dualMeanSquare, columnSumCoprime, columnSum, h]

private lemma AwayFromSix.coprime_three' {n : Ideal 𝓔} (hn : AwayFromSix n) :
    IsCoprime n (span {3}) :=
  hn.2.of_isCoprime_of_dvd_right (span_singleton_dvd_span_singleton_iff_dvd.mpr ⟨2, by norm_num⟩)

private lemma Starred.of_dvd {m n : Ideal 𝓔} (hn : Starred n) (h : m ∣ n) : Starred m := by
  refine ⟨⟨fun hm => hn.1.1 ?_, hn.1.2.of_isCoprime_of_dvd_left h⟩, hn.2.squarefree_of_dvd h⟩
  rw [hm] at h
  exact le_bot_iff.mp (Ideal.le_of_dvd h)

private lemma Starred.mul {a b : Ideal 𝓔} (ha : Starred a) (hb : Starred b) (h : IsCoprime a b) :
    Starred (a * b) :=
  ⟨⟨fun hab => (Ideal.mul_eq_bot.mp hab).elim ha.1.1 hb.1.1, ha.1.2.mul_left hb.1.2⟩,
    squarefree_mul_iff.mpr ⟨h.isRelPrime, ha.2, hb.2⟩⟩

private lemma isCoprime_prime_iff {n p : Ideal 𝓔} (hp : Prime p) : IsCoprime n p ↔ ¬ p ∣ n := by
  rw [isCoprime_comm, Ideal.isCoprime_iff_gcd, hp.irreducible.gcd_eq_one_iff]

private lemma sextic_mul_den (a b : Ideal 𝓔) (x : 𝓔) :
    sextic (a * b) x = sextic a x * sextic b x := by
  classical
  unfold sextic powerResidueSymbol
  by_cases ha : a = ⊥
  · simp [ha]
  by_cases hb : b = ⊥
  · simp [hb]
  have hab : ¬ a * b = ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [hab, ha, hb, ↓reduceIte]
  rw [normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add, map_mul]

private lemma sextic_eq_zero {p m : Ideal 𝓔} (hp : Prime p) (hpm : p ∣ m) (hm : m ≠ ⊥) {x : 𝓔}
    (hx : x ∈ p) : sextic m x = 0 := by
  classical
  obtain ⟨c, rfl⟩ := hpm
  rw [sextic_mul_den]
  have hp₀ : p ≠ ⊥ := fun h => hm (by simp [h])
  have : sextic p x = 0 := by
    unfold sextic powerResidueSymbol
    simp only [hp₀, ↓reduceIte]
    rw [normalizedFactors_irreducible hp.irreducible, normalize_eq]
    simp [primePowerResidueSymbol, hx]
  rw [this, zero_mul]

private lemma sextic_mul_pow (hres : ResidueMultiplicative) {m : Ideal 𝓔}
    (hm : IsCoprime m (span {6})) (x y : 𝓔) (j : ℕ) :
    sextic m (x * y ^ j) = sextic m x * sextic m y ^ j := by
  induction j with
  | zero => simp [sextic]
  | succ j ih =>
    unfold sextic at ih ⊢
    rw [pow_succ, ← mul_assoc, hres.six_mul hm, map_mul, ih, pow_succ, mul_assoc]

/-- The summand at `p m` factors through the summand at `m` of the column at `p f`. -/
private lemma summand_mul (hpg : PairedGaussIdentities) (hres : ResidueMultiplicative)
    (ξ : RayCharacter) (W : ℝ → ℂ) {X : ℝ} (k : 𝓔) {p m f : Ideal 𝓔} (hp : Starred p)
    (hm : Starred m) (hpm : IsCoprime p m) (hf : AwayFromSix f) :
    gaussCoefficient (p * m) * twist ξ k f (p * m) * W (absNorm (p * m) / X) =
      gaussCoefficient p * twist ξ k f p *
        (gaussCoefficient m * twist ξ k (p * f) m * W (absNorm m / (X / absNorm p))) := by
  obtain ⟨A, B, hAB⟩ := hpg
  have hprod := (hAB p m hp hm hpm).2.2
  have hpm' : AwayFromSix (p * m) := (hp.mul hm hpm).1
  have hp₀ : (absNorm p : ℝ) ≠ 0 := by
    exact_mod_cast absNorm_eq_zero_iff.not.mpr hp.1.1
  have hW : W (absNorm (p * m) / X) = W (absNorm m / (X / absNorm p)) := by
    congr 1
    rw [map_mul, Nat.cast_mul]
    field_simp
  have h3 := hp.1.coprime_three'
  have hgen : generator (p * m) = generator p * generator m :=
    hres.generator_mul h3 hm.1.coprime_three'
  have hgenf : generator (p * f) = generator p * generator f :=
    hres.generator_mul h3 hf.coprime_three'
  have htw : twist ξ k (p * f) m = ξ (Ideal.Quotient.mk _ (generator m)) *
      (sextic m (k * generator f ^ 4) * sextic m (generator p) ^ 4) := by
    unfold twist
    simp only [hm.1, ↓reduceIte]
    rw [hgenf, mul_pow, mul_comm (generator p ^ 4), ← mul_assoc, sextic_mul_pow hres hm.1.2]
  rw [htw]
  unfold twist
  simp only [hpm', hp.1, ↓reduceIte]
  rw [hprod, hW, hgen, map_mul, map_mul, sextic_mul_den]
  ring

/-- The summand of a coprime column, extended by zero to all ideals. -/
private def coprimeTerm (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔) (f r n : Ideal 𝓔) : ℂ :=
  open Classical in
  if Starred n ∧ IsCoprime n r then gaussCoefficient n * twist ξ k f n * W (absNorm n / X) else 0

private lemma columnSumCoprime_eq_finsum (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔)
    (f r : Ideal 𝓔) : columnSumCoprime ξ W X k f r = ∑ᶠ n, coprimeTerm ξ W X k f r n := by
  classical
  unfold columnSumCoprime coprimeTerm
  rw [finsum_subtype_eq_finsum_cond (f := fun n : Ideal 𝓔 => if IsCoprime n r then
    gaussCoefficient n * twist ξ k f n * W (absNorm n / X) else 0) Starred]
  refine finsum_congr fun n => ?_
  by_cases hn : Starred n <;> simp [hn]

private lemma finite_support_of_test {W : ℝ → ℂ} {R X : ℝ} (hW : ∀ x, W x ≠ 0 → x ≤ R)
    (hX : 0 < X) {g : Ideal 𝓔 → ℂ} (hg : ∀ n, g n ≠ 0 → W (absNorm n / X) ≠ 0) :
    (Function.support g).Finite := by
  refine (idealsLe (R * X)).finite_toSet.subset fun n hn => Finset.mem_coe.mpr ?_
  have h₁ := (div_le_iff₀ hX).mp (hW _ (hg n hn))
  exact (mem_idealsLe ((Nat.cast_nonneg _).trans h₁)).mpr h₁

private lemma coprimeTerm_ne_zero {ξ : RayCharacter} {W : ℝ → ℂ} {X : ℝ} {k : 𝓔}
    {f r n : Ideal 𝓔} (h : coprimeTerm ξ W X k f r n ≠ 0) : W (absNorm n / X) ≠ 0 := by
  unfold coprimeTerm at h
  split_ifs at h
  · exact right_ne_zero_of_mul h
  · exact absurd rfl h

private lemma prime_not_dvd_of_starred {r p : Ideal 𝓔} (hp : Prime p) (hrp : Starred (r * p)) :
    ¬ p ∣ r := fun h => hp.not_isUnit ((squarefree_mul_iff.mp hrp.2).1 h dvd_rfl)

/-- Removing one prime from the exclusion: the column coprime to `r` is the column coprime
to `r p` plus the multiples of `p`, which form a column of length `X/Np` at `p f`. -/
private lemma columnSumCoprime_mul_prime (hpg : PairedGaussIdentities)
    (hres : ResidueMultiplicative) {ξ : RayCharacter} {W : ℝ → ℂ} {R X : ℝ}
    (hW : ∀ x, W x ≠ 0 → x ≤ R) (hX : 0 < X) (k : 𝓔) {r p f : Ideal 𝓔} (hp : Prime p)
    (hrp : Starred (r * p)) (hf : AwayFromSix f) :
    columnSumCoprime ξ W X k f r = columnSumCoprime ξ W X k f (r * p) +
      gaussCoefficient p * twist ξ k f p * columnSumCoprime ξ W (X / absNorm p) k (p * f) r := by
  classical
  have hps : Starred p := hrp.of_dvd (dvd_mul_left p r)
  have hpr : IsCoprime p r :=
    ((isCoprime_prime_iff hp).mpr (prime_not_dvd_of_starred hp hrp)).symm
  have hp₀ : 0 < (absNorm p : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hps.1.1)
  let S : Ideal 𝓔 → ℂ := fun n => gaussCoefficient n * twist ξ k f n * W (absNorm n / X)
  let U : Ideal 𝓔 → ℂ := fun n => if Starred n ∧ IsCoprime n r ∧ p ∣ n then S n else 0
  have hsplit (n : Ideal 𝓔) :
      coprimeTerm ξ W X k f r n = coprimeTerm ξ W X k f (r * p) n + U n := by
    unfold coprimeTerm
    by_cases hn : Starred n
    · by_cases hc : IsCoprime n r
      · by_cases hd : p ∣ n
        · simp [S, U, hn, hc, hd, IsCoprime.mul_right_iff, isCoprime_prime_iff hp]
        · simp [S, U, hn, hc, hd, IsCoprime.mul_right_iff, isCoprime_prime_iff hp]
      · simp [U, hn, hc, IsCoprime.mul_right_iff]
    · simp [U, hn]
  have hUfin : (Function.support U).Finite := finite_support_of_test hW hX fun n hn => by
    simp only [U] at hn
    split_ifs at hn
    · exact right_ne_zero_of_mul hn
    · exact absurd rfl hn
  have hU : ∑ᶠ n, U n = ∑ᶠ m, U (p * m) := by
    rw [← finsum_mem_range (f := U) (mul_right_injective₀ hp.ne_zero), ← finsum_mem_univ U]
    refine (finsum_mem_inter_support_eq U _ _ ?_).symm
    ext n
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_range, and_iff_right_iff_imp]
    intro hn
    simp only [Function.mem_support, U] at hn
    split_ifs at hn with h
    · obtain ⟨c, rfl⟩ := h.2.2
      exact ⟨c, rfl⟩
    · exact absurd rfl hn
  have hUm (m : Ideal 𝓔) : U (p * m) =
      gaussCoefficient p * twist ξ k f p * coprimeTerm ξ W (X / absNorm p) k (p * f) r m := by
    unfold coprimeTerm
    by_cases hm : Starred m ∧ IsCoprime m r
    · by_cases hmp : IsCoprime m p
      · have hpm : Starred (p * m) := hps.mul hm.1 hmp.symm
        have hpmr : IsCoprime (p * m) r := hpr.mul_left hm.2
        simp only [U, S, hpm, hpmr, hm, dvd_mul_right, and_self, ↓reduceIte]
        exact summand_mul hpg hres ξ W k hps hm.1 hmp.symm hf
      · have hdvd : p ∣ m := by simpa [isCoprime_prime_iff hp] using hmp
        have hns : ¬ Starred (p * m) := fun h =>
          hp.not_isUnit ((squarefree_mul_iff.mp h.2).1 dvd_rfl hdvd)
        have hgen : k * generator (p * f) ^ 4 ∈ p := by
          refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ?_ 4 (by norm_num))
          have hmem : generator (p * f) ∈ p * f := by
            have h := mem_span_singleton_self (generator (p * f))
            rwa [span_generator] at h
          exact (Ideal.mul_le_left : p * f ≤ p) hmem
        have htw : twist ξ k (p * f) m = 0 := by
          unfold twist
          simp only [hm.1.1, ↓reduceIte]
          rw [sextic_eq_zero hp hdvd hm.1.1.1 hgen, mul_zero]
        simp only [U, hns, false_and, hm, htw, ↓reduceIte, mul_zero, zero_mul, ite_self]
    · have hnot : ¬ (Starred (p * m) ∧ IsCoprime (p * m) r ∧ p ∣ p * m) := fun h =>
        hm ⟨h.1.of_dvd (dvd_mul_left m p), h.2.1.of_mul_left_right⟩
      simp only [U, hnot, hm, ↓reduceIte, mul_zero]
  have hTfin := finite_support_of_test hW hX fun n hn => coprimeTerm_ne_zero
    (ξ := ξ) (k := k) (f := f) (r := r * p) hn
  rw [columnSumCoprime_eq_finsum, columnSumCoprime_eq_finsum, columnSumCoprime_eq_finsum,
    finsum_congr hsplit, finsum_add_distrib hTfin hUfin, hU, finsum_congr hUm, mul_finsum]

private lemma norm_sq_le_of_eq_add {a b c d : ℂ} (h : b = a + c * d) (hc : ‖c‖ ≤ 1) :
    ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
  have hle : ‖a‖ ≤ ‖b‖ + ‖d‖ := by
    have ha : a = b - c * d := by rw [h]; ring
    rw [ha]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg d, sq_nonneg (‖b‖ - ‖d‖)]

/-- The block of starred `f` with `G ≤ Nf < 2G`. -/
private abbrev fBlock (G : ℝ) : Finset (Ideal 𝓔) := open Classical in
  (idealsLe (2 * G)).filter (fun f => Starred f ∧ G ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * G)

/-- One prime of the exclusion: `E_{rp}(K,X,F) ≤ 2 E_r(K,X,F) + 2 E_r(K, X/Np, F Np)`. -/
theorem dualMeanSquareCoprime_mul_prime_le (hpg : PairedGaussIdentities)
    (hg : GaussCoefficientBound) (hres : ResidueMultiplicative) {ξ : RayCharacter}
    {W : ℝ → ℂ} {R K X F : ℝ} (hW : ∀ x, W x ≠ 0 → x ≤ R) (hX : 0 < X) (hF : 0 < F)
    {r p : Ideal 𝓔} (hp : Prime p) (hrp : Starred (r * p)) :
    dualMeanSquareCoprime ξ W K X F (r * p) ≤
      2 * dualMeanSquareCoprime ξ W K X F r +
        2 * dualMeanSquareCoprime ξ W K (X / absNorm p) (F * absNorm p) r := by
  classical
  have hps : Starred p := hrp.of_dvd (dvd_mul_left p r)
  have hp₀ : 0 < (absNorm p : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hps.1.1)
  let G : Ideal 𝓔 → ℝ := fun f' =>
    ∑ k ∈ elementRows K, ‖columnSumCoprime ξ W (X / absNorm p) k f' r‖ ^ 2
  have hG₀ (f' : Ideal 𝓔) : 0 ≤ G f' := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpoint (f : Ideal 𝓔) (hf : f ∈ fBlock F) :
      ∑ k ∈ elementRows K, ‖columnSumCoprime ξ W X k f (r * p)‖ ^ 2 ≤
        2 * ∑ k ∈ elementRows K, ‖columnSumCoprime ξ W X k f r‖ ^ 2 +
          2 * (if p ∣ f then 0 else G (p * f)) := by
    have hfa : AwayFromSix f := (Finset.mem_filter.mp hf).2.1.1
    have hcol (k : 𝓔) := columnSumCoprime_mul_prime hpg hres hW hX k hp hrp hfa (ξ := ξ)
    by_cases hd : p ∣ f
    · have hzero (k : 𝓔) : twist ξ k f p = 0 := by
        have hmem : k * generator f ^ 4 ∈ p := by
          refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ?_ 4 (by norm_num))
          have h := mem_span_singleton_self (generator f)
          rw [span_generator] at h
          exact Ideal.le_of_dvd hd h
        unfold twist
        simp only [hps.1, ↓reduceIte]
        rw [sextic_eq_zero hp dvd_rfl hps.1.1 hmem, mul_zero]
      simp only [hd, ↓reduceIte, mul_zero, add_zero]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [hcol k, hzero k]
      simp only [mul_zero, zero_mul, add_zero]
      nlinarith [sq_nonneg ‖columnSumCoprime ξ W X k f r‖]
    · simp only [hd, ↓reduceIte]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun k _ => ?_
      have hc : ‖gaussCoefficient p * twist ξ k f p‖ ≤ 1 := by
        rw [norm_mul]
        exact (mul_le_mul (hg p hps) (norm_twist_le_one ξ k f p) (norm_nonneg _)
          zero_le_one).trans_eq (one_mul 1)
      exact norm_sq_le_of_eq_add (hcol k) hc
  have hshift : ∑ f ∈ fBlock F, (if p ∣ f then 0 else G (p * f)) ≤
      ∑ f' ∈ fBlock (F * absNorm p), G f' := by
    have himg : ((fBlock F).filter fun f => ¬ p ∣ f).image (p * ·) ⊆
        fBlock (F * absNorm p) := by
      intro f' hf'
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hf'
      obtain ⟨hfB, hnd⟩ := Finset.mem_filter.mp hf
      obtain ⟨-, hfs, hlo, hhi⟩ := Finset.mem_filter.mp hfB
      have hN : (absNorm (p * f) : ℝ) = absNorm p * absNorm f := by
        rw [map_mul, Nat.cast_mul]
      have hlo' : F * absNorm p ≤ (absNorm (p * f) : ℝ) := by rw [hN]; nlinarith
      have hhi' : (absNorm (p * f) : ℝ) < 2 * (F * absNorm p) := by rw [hN]; nlinarith
      refine Finset.mem_filter.mpr ⟨(mem_idealsLe (by positivity)).mpr hhi'.le,
        hps.mul hfs ((isCoprime_prime_iff hp).mpr hnd).symm, hlo', hhi'⟩
    calc ∑ f ∈ fBlock F, (if p ∣ f then 0 else G (p * f))
        = ∑ f ∈ (fBlock F).filter (fun f => ¬ p ∣ f), G (p * f) := by
          rw [Finset.sum_filter (p := fun f => ¬ p ∣ f) (f := fun f => G (p * f))]
          exact Finset.sum_congr rfl fun f _ => by by_cases h : p ∣ f <;> simp [h]
      _ = ∑ f' ∈ ((fBlock F).filter fun f => ¬ p ∣ f).image (p * ·), G f' :=
          (Finset.sum_image fun x _ y _ h => mul_left_cancel₀ hp.ne_zero h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => hG₀ _
  have hden : X / absNorm p * (F * absNorm p) = X * F := by field_simp
  have hXF : 0 < X * F := mul_pos hX hF
  have h0 : ∑ f ∈ fBlock F, ∑ k ∈ elementRows K, ‖columnSumCoprime ξ W X k f (r * p)‖ ^ 2 ≤
      2 * ∑ f ∈ fBlock F, ∑ k ∈ elementRows K, ‖columnSumCoprime ξ W X k f r‖ ^ 2 +
        2 * ∑ f' ∈ fBlock (F * absNorm p), G f' := by
    refine (Finset.sum_le_sum hpoint).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith [hshift]
  simp only [G] at h0
  unfold dualMeanSquareCoprime
  rw [hden, mul_div_assoc', mul_div_assoc', ← add_div]
  exact div_le_div_of_nonneg_right h0 hXF.le

/-- The exclusion shift (2) of the audit's manuscript. For a starred `r` with prime factors
`P(r)` (a multiset without repetitions),
`E_r(K,X,F) ≤ 2^{ω(r)} Σ_{t ≤ P(r)} E(K, X/N(Πt), F N(Πt))`.
The sub-multisets `t` enumerate the divisors `j = Πt` of `r`, and `2^{ω(r)} = τ(r)`. -/
theorem dualMeanSquareCoprime_le (hpg : PairedGaussIdentities) (hg : GaussCoefficientBound)
    (hres : ResidueMultiplicative) {ξ : RayCharacter} {W : ℝ → ℂ} {R K : ℝ}
    (hW : ∀ x, W x ≠ 0 → x ≤ R) {r : Ideal 𝓔} (hr : Starred r) {X F : ℝ} (hX : 0 < X)
    (hF : 0 < F) :
    dualMeanSquareCoprime ξ W K X F r ≤ 2 ^ Multiset.card (normalizedFactors r) *
      ((normalizedFactors r).powerset.map fun t =>
        dualMeanSquare ξ W K (X / absNorm t.prod) (F * absNorm t.prod)).sum := by
  have key : ∀ s : Multiset (Ideal 𝓔), (∀ p ∈ s, Prime p) → Starred s.prod →
      ∀ X F : ℝ, 0 < X → 0 < F → dualMeanSquareCoprime ξ W K X F s.prod ≤
        2 ^ Multiset.card s * (s.powerset.map fun t =>
          dualMeanSquare ξ W K (X / absNorm t.prod) (F * absNorm t.prod)).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _ _ X F _ _
      simp [Ideal.one_eq_top, dualMeanSquareCoprime_top]
    | cons p s ih =>
      intro hs hstar X F hX hF
      have hp := hs p (Multiset.mem_cons_self p s)
      have hstar' : Starred (s.prod * p) := by rwa [Multiset.prod_cons, mul_comm] at hstar
      have hs' : Starred s.prod := hstar'.of_dvd (dvd_mul_right _ _)
      have hNp : 0 < (absNorm p : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr
          (hstar'.of_dvd (dvd_mul_left p _)).1.1)
      have hs₁ : ∀ q ∈ s, Prime q := fun q hq => hs q (Multiset.mem_cons_of_mem hq)
      have h₁ := ih hs₁ hs' X F hX hF
      have h₂ := ih hs₁ hs' (X / absNorm p) (F * absNorm p) (div_pos hX hNp) (mul_pos hF hNp)
      have hcomp : ((s.powerset.map (Multiset.cons p)).map fun t =>
          dualMeanSquare ξ W K (X / absNorm t.prod) (F * absNorm t.prod)) =
          s.powerset.map fun t => dualMeanSquare ξ W K (X / absNorm p / absNorm t.prod)
            (F * absNorm p * absNorm t.prod) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun t _ => ?_
        simp only [Function.comp_apply, Multiset.prod_cons, map_mul, Nat.cast_mul, div_div,
          mul_assoc]
      rw [Multiset.prod_cons, mul_comm, Multiset.powerset_cons, Multiset.map_add,
        Multiset.sum_add, hcomp, Multiset.card_cons, pow_succ]
      refine (dualMeanSquareCoprime_mul_prime_le hpg hg hres hW hX hF hp hstar').trans ?_
      nlinarith [h₁, h₂]
  have hr₀ : r ≠ 0 := hr.1.1
  have hprod : (normalizedFactors r).prod = r :=
    associated_iff_eq.mp (prod_normalizedFactors hr₀)
  have h := key (normalizedFactors r) (fun p hp => prime_of_normalized_factor p hp)
    (by rw [hprod]; exact hr) X F hX hF
  rwa [hprod] at h

/-- The exclusion shift with a common bound `M` on the shifted forms, all of which keep the
product `XF`: then `E_r(K,X,F) ≤ 4^{ω(r)} M`. -/
theorem dualMeanSquareCoprime_le_of_forall (hpg : PairedGaussIdentities)
    (hg : GaussCoefficientBound) (hres : ResidueMultiplicative) {ξ : RayCharacter}
    {W : ℝ → ℂ} {R K M : ℝ} (hW : ∀ x, W x ≠ 0 → x ≤ R) {r : Ideal 𝓔} (hr : Starred r)
    {X F : ℝ} (hX : 0 < X) (hF : 0 < F)
    (hM : ∀ t ≤ normalizedFactors r,
      dualMeanSquare ξ W K (X / absNorm t.prod) (F * absNorm t.prod) ≤ M) :
    dualMeanSquareCoprime ξ W K X F r ≤ 4 ^ Multiset.card (normalizedFactors r) * M := by
  refine (dualMeanSquareCoprime_le hpg hg hres hW hr hX hF (K := K) (ξ := ξ)).trans ?_
  have hsum := Multiset.sum_le_card_nsmul ((normalizedFactors r).powerset.map fun t =>
    dualMeanSquare ξ W K (X / absNorm t.prod) (F * absNorm t.prod)) M (by
      simpa only [Multiset.mem_map, Multiset.mem_powerset, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] using hM)
  rw [Multiset.card_map, Multiset.card_powerset, nsmul_eq_mul] at hsum
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsum) (by positivity)

/-! ### The divisor bound for squarefree ideals -/

/-- `2^{ω(r)} ≤ C_s (Nr)^s` for squarefree `r`. This is the divisor bound for the cost of the
exclusion shift. -/
theorem two_pow_card_normalizedFactors_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ r : Ideal 𝓔, r ≠ ⊥ → Squarefree r →
      (2 : ℝ) ^ Multiset.card (normalizedFactors r) ≤ C * (absNorm r : ℝ) ^ s := by
  classical
  let T := idealsLe ((2 : ℝ) ^ (1 / s))
  refine ⟨2 ^ T.card, by positivity, fun r hr hsq => ?_⟩
  have hlarge {P : Ideal 𝓔} (hP : P ∉ T) : 2 ≤ (absNorm P : ℝ) ^ s := by
    have h : (2 : ℝ) ^ (1 / s) < absNorm P := by
      by_contra h
      exact hP ((mem_idealsLe (by positivity)).mpr (not_lt.mp h))
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / s)) ^ s := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hs.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h.le hs.le
  have key : ∀ m : Multiset (Ideal 𝓔), (∀ P ∈ m, P ≠ ⊥) →
      (2 : ℝ) ^ Multiset.card m ≤
        2 ^ Multiset.card (m.filter (· ∈ T)) * (absNorm m.prod : ℝ) ^ s := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | cons P m ih =>
      intro hm
      have hP : (1 : ℝ) ≤ absNorm P := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (absNorm_eq_zero_iff.not.mpr (hm P (Multiset.mem_cons_self P m)))
      have ih' := ih fun Q hQ => hm Q (Multiset.mem_cons_of_mem hQ)
      have hPs : (1 : ℝ) ≤ (absNorm P : ℝ) ^ s := Real.one_le_rpow hP hs.le
      have hm₀ : (0 : ℝ) ≤ (absNorm m.prod : ℝ) ^ s := by positivity
      rw [Multiset.card_cons, Multiset.prod_cons, map_mul, Nat.cast_mul,
        Real.mul_rpow (by positivity) (by positivity), pow_succ]
      by_cases hT : P ∈ T
      · rw [Multiset.filter_cons_of_pos _ hT, Multiset.card_cons, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left hPs
          (mul_nonneg
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Multiset.card (m.filter (· ∈ T)))) hm₀)]
      · rw [Multiset.filter_cons_of_neg _ hT]
        nlinarith [mul_le_mul_of_nonneg_left (hlarge hT)
          (mul_nonneg
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Multiset.card (m.filter (· ∈ T)))) hm₀)]
  have hfac : ∀ P ∈ normalizedFactors r, P ≠ ⊥ := fun P hP =>
    (prime_of_normalized_factor P hP).ne_zero
  have hprod : (normalizedFactors r).prod = r :=
    associated_iff_eq.mp (prod_normalizedFactors hr)
  have hcard : Multiset.card ((normalizedFactors r).filter (· ∈ T)) ≤ T.card := by
    have hnd := ((squarefree_iff_nodup_normalizedFactors hr).mp hsq).filter (· ∈ T)
    rw [← Multiset.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun P hP => (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2
  calc (2 : ℝ) ^ Multiset.card (normalizedFactors r)
      ≤ 2 ^ Multiset.card ((normalizedFactors r).filter (· ∈ T)) * (absNorm r : ℝ) ^ s := by
        simpa [hprod] using key _ hfac
    _ ≤ _ := by gcongr; norm_num

end Masullo.QRH.MeanSquare
