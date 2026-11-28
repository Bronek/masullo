import Masullo.QRH.MeanSquare.TransferFactor

/-!
# The expansion of a Poisson pass

A Poisson pass starts from the `P`-weighted mean square of the columns `passColumn`.

* `sum_sq_eq_sum_passSplits`: a double sum over starred ideals of norm at most `X` is a sum over
  the gcd splits `passSplits X`.
* `tsum_passColumn_eq`: the weighted mean square is the real part of a sum of primitive Poisson
  duals over the gcd splits.
-/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

lemma Starred.mul_of_isCoprime {a b : Ideal 𝓔} (ha : Starred a) (hb : Starred b)
    (h : IsCoprime a b) : Starred (a * b) :=
  ⟨⟨fun hab => (Ideal.mul_eq_bot.mp hab).elim ha.1.1 hb.1.1, ha.1.2.mul_left hb.1.2⟩,
    squarefree_mul_iff.mpr ⟨h.isRelPrime, ha.2, hb.2⟩⟩

lemma IsGcdSplit.starred_left {t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (ht : IsGcdSplit t) :
    Starred (t.1 * t.2.1) :=
  ht.1.mul_of_isCoprime ht.2.1 ht.2.2.2.2.of_mul_right_right

lemma IsGcdSplit.starred_right {t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (ht : IsGcdSplit t) :
    Starred (t.1 * t.2.2) :=
  ht.1.mul_of_isCoprime ht.2.2.1 ht.2.2.2.2.of_mul_right_left

/-- The starred ideals of norm at most `X`. -/
def starredLe (X : ℝ) : Finset (Ideal 𝓔) := by
  classical exact (idealsLe X).filter Starred

lemma mem_starredLe {X : ℝ} (hX : 0 ≤ X) {n : Ideal 𝓔} :
    n ∈ starredLe X ↔ (absNorm n : ℝ) ≤ X ∧ Starred n := by
  classical
  unfold starredLe
  rw [Finset.mem_filter, mem_idealsLe hX]

/-- The gcd splits whose two columns have norm at most `X`. -/
def passSplits (X : ℝ) : Finset (Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) := by
  classical exact (gcdSplitsLe X).filter fun t =>
    (absNorm (t.1 * t.2.1) : ℝ) ≤ X ∧ (absNorm (t.1 * t.2.2) : ℝ) ≤ X

lemma mem_passSplits {X : ℝ} (hX : 0 ≤ X) {t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} :
    t ∈ passSplits X ↔ IsGcdSplit t ∧ (absNorm (t.1 * t.2.1) : ℝ) ≤ X ∧
      (absNorm (t.1 * t.2.2) : ℝ) ≤ X := by
  classical
  unfold passSplits
  rw [Finset.mem_filter]
  refine ⟨fun ⟨h, h'⟩ => ⟨?_, h'⟩, fun ⟨h, h'⟩ => ⟨mem_gcdSplitsLe hX h h'.1 h'.2, h'⟩⟩
  unfold gcdSplitsLe at h
  exact (Finset.mem_filter.mp h).2

/-- A double sum over the starred ideals of norm at most `X` is a sum over the gcd splits. -/
theorem sum_sq_eq_sum_passSplits {X : ℝ} (hX : 0 ≤ X) (F : Ideal 𝓔 → Ideal 𝓔 → ℂ) :
    ∑ n₁ ∈ starredLe X, ∑ n₂ ∈ starredLe X, F n₁ n₂ =
      ∑ t ∈ passSplits X, F (t.1 * t.2.1) (t.1 * t.2.2) := by
  rw [← Finset.sum_product' (f := F)]
  symm
  refine Finset.sum_bij (fun t _ => (t.1 * t.2.1, t.1 * t.2.2)) ?_ ?_ ?_ fun _ _ => rfl
  · intro t ht
    obtain ⟨hs, h₁, h₂⟩ := (mem_passSplits hX).mp ht
    exact Finset.mem_product.mpr ⟨(mem_starredLe hX).mpr ⟨h₁, hs.starred_left⟩,
      (mem_starredLe hX).mpr ⟨h₂, hs.starred_right⟩⟩
  · intro t₁ ht₁ t₂ ht₂ h
    exact isGcdSplit_injOn ((mem_passSplits hX).mp ht₁).1 ((mem_passSplits hX).mp ht₂).1 h
  · rintro ⟨n₁, n₂⟩ hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    obtain ⟨hN₁, hs₁⟩ := (mem_starredLe hX).mp hp₁
    obtain ⟨hN₂, hs₂⟩ := (mem_starredLe hX).mp hp₂
    obtain ⟨g, z₁, z₂, rfl, rfl, hg, h₁, h₂, h12, hgz⟩ := exists_gcd_split hs₁ hs₂
    exact ⟨(g, z₁, z₂), (mem_passSplits hX).mpr ⟨⟨hg, h₁, h₂, h12, hgz⟩, hN₁, hN₂⟩, rfl⟩

/-- The column of a Poisson pass at the row `y`. -/
def passColumn (κ φ : Ideal 𝓔 → ℂ) (V : ℝ → ℂ) (ℓ X : ℝ) (y : 𝓔) : ℂ :=
  ∑ n ∈ starredLe X, κ n * φ n * V (absNorm n / ℓ) * sextic n y

/-- The weighted mean square of the columns is a sum of primitive Poisson duals over the gcd
splits. -/
theorem tsum_passColumn_eq {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) {Y : ℝ} (hY : 0 < Y)
    (κ φ : Ideal 𝓔 → ℂ) (V : ℝ → ℂ) (ℓ : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    ∑' y : 𝓔, (P (elementNorm y / Y)).re * ‖passColumn κ φ V ℓ X y‖ ^ 2 =
      (∑ t ∈ passSplits X,
        κ (t.1 * t.2.1) * φ (t.1 * t.2.1) * V (absNorm (t.1 * t.2.1) / ℓ) *
          conj (κ (t.1 * t.2.2) * φ (t.1 * t.2.2) * V (absNorm (t.1 * t.2.2) / ℓ)) *
          poissonDual P Y t.2.2 t.2.1 t.1).re := by
  unfold passColumn
  rw [tsum_majorant_eq hP hY, sum_sq_eq_sum_passSplits hX]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨⟨hg, h₁, h₂, h12, hgz⟩, -⟩ := (mem_passSplits hX).mp ht
  rw [pairRowSum_eq_poisson hg h₁ h₂ h12 hgz P hY]

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-- The converted weight of a gcd split `t`: the summand, the tests and the Poisson scale. -/
def passDual (κ κ' φ : Ideal 𝓔 → ℂ) (p : ℕ) (Corr : Q₇₂ → Q₇₂ → ℂ) (V : ℝ → ℂ) (ℓ Y : ℝ)
    (t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : ℂ :=
  splitSummand κ κ' φ p Corr t.1 t.2.1 t.2.2 *
    (V (absNorm (t.1 * t.2.1) / ℓ) * conj (V (absNorm (t.1 * t.2.2) / ℓ))) *
    ((Y : ℂ) / Real.sqrt (absNorm (t.2.2 * t.2.1)))

open Classical in
/-- The zero frequency of the dual of a gcd split. -/
def passZero (P : SchwartzMap ℝ ℂ) (t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : ℂ :=
  (∑ᶠ e : {e : Ideal 𝓔 // e ∣ t.1},
    (idealMoebius e : ℂ) * pairCharacter t.2.2 t.2.1 (generator e) / (absNorm e.val : ℂ)) *
    (conj (pairCharacter t.2.2 t.2.1 0) * gaoZhaoTransform P 0)

/-- The weighted mean square of the columns splits into the nonzero and the zero dual
frequencies of the converted gcd splits. -/
theorem tsum_passColumn_eq_add {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) {Y : ℝ}
    (hY : 0 < Y) {κ κ' φ : Ideal 𝓔 → ℂ} {p : ℕ} {Corr : Q₇₂ → Q₇₂ → ℂ} (hκ : TwistMul κ p)
    (hφ : TwistMul φ 0) (hconv : GaussConversion κ κ' Corr) (V : ℝ → ℂ) (ℓ : ℝ) {X : ℝ}
    (hX : 0 ≤ X) :
    ∑' y : 𝓔, (P (elementNorm y / Y)).re * ‖passColumn κ φ V ℓ X y‖ ^ 2 =
      (∑ t ∈ passSplits X, passDual κ κ' φ p Corr V ℓ Y t *
          dualExclusionTail P Y t.2.2 t.2.1 t.1 +
        ∑ t ∈ passSplits X, passDual κ κ' φ p Corr V ℓ Y t * passZero P t).re := by
  rw [tsum_passColumn_eq hP hY κ φ V ℓ hX, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨hs, -⟩ := (mem_passSplits hX).mp ht
  obtain ⟨g, z₁, z₂⟩ := t
  rw [poissonDual, dualExclusion_eq_add hs.2.2.1.1 hs.2.1.1 hs.1 P hY, passDual, passZero,
    ← mul_pairGauss_eq_splitSummand hκ hφ hconv hs]
  simp only [map_mul]
  ring

/-- The norm of the converted summand of a gcd split. -/
lemma norm_splitSummand_le {κ κ' φ : Ideal 𝓔 → ℂ} {p : ℕ} {Corr : Q₇₂ → Q₇₂ → ℂ}
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (hκ' : ∀ n, ‖κ' n‖ ≤ 1) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (g z₁ z₂ : Ideal 𝓔) :
    ‖splitSummand κ κ' φ p Corr g z₁ z₂‖ ≤ ‖Corr (Ideal.Quotient.mk _ (generator z₁))
      (Ideal.Quotient.mk _ (generator z₂))‖ := by
  have h1 : ∀ a : ℂ, ‖a‖ ≤ 1 → ‖a * conj a‖ ≤ 1 := fun a ha => by
    rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg a]
  have h2 : ∀ a b : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * conj b‖ ≤ 1 := fun a b ha hb => by
    rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg a, norm_nonneg b]
  have hs : ∀ n y, ‖sextic n y ^ p‖ ≤ 1 := fun n y => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_sextic_le_one _ _)
  unfold splitSummand
  have e1 := h1 _ (hκ g)
  have e2 := h1 _ (hφ g)
  have e3 := h2 _ _ (hs z₁ (generator g)) (hs z₂ (generator g))
  have e4 := h2 _ _ (hκ' z₁) (hκ' z₂)
  have e5 := h2 _ _ (hφ z₁) (hφ z₂)
  generalize κ g * conj (κ g) = a₁ at e1 ⊢
  generalize φ g * conj (φ g) = a₂ at e2 ⊢
  generalize sextic z₁ (generator g) ^ p * conj (sextic z₂ (generator g) ^ p) = a₃ at e3 ⊢
  generalize κ' z₁ * conj (κ' z₂) = a₄ at e4 ⊢
  generalize φ z₁ * conj (φ z₂) = a₅ at e5 ⊢
  simp only [norm_mul]
  have hC := norm_nonneg (Corr (Ideal.Quotient.mk _ (generator z₁))
    (Ideal.Quotient.mk _ (generator z₂)))
  generalize ‖Corr (Ideal.Quotient.mk _ (generator z₁)) (Ideal.Quotient.mk _ (generator z₂))‖
    = C at hC ⊢
  calc _ ≤ 1 * 1 * 1 * (1 * C) * 1 := by gcongr
    _ = C := by ring

open UniqueFactorizationMonoid in
/-- The zero dual frequencies occur only at `z₁ = z₂ = ⊤`, once for each starred `g`. -/
theorem norm_sum_passZero_le {κ κ' φ : Ideal 𝓔 → ℂ} {p : ℕ} {Corr : Q₇₂ → Q₇₂ → ℂ}
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (hκ' : ∀ n, ‖κ' n‖ ≤ 1) (hφ : ∀ n, ‖φ n‖ ≤ 1) {V : ℝ → ℂ}
    (hV : ∀ x, ‖V x‖ ≤ 1) (P : SchwartzMap ℝ ℂ) (ℓ : ℝ) {Y X : ℝ} (hY : 0 ≤ Y)
    (hX : 0 ≤ X) :
    ‖∑ t ∈ passSplits X, passDual κ κ' φ p Corr V ℓ Y t * passZero P t‖ ≤
      Y * ‖Corr (Ideal.Quotient.mk _ (generator ⊤)) (Ideal.Quotient.mk _ (generator ⊤))‖ *
        ‖gaoZhaoTransform P 0‖ *
        ∑ g ∈ starredLe X, (2 : ℝ) ^ Multiset.card (normalizedFactors g) := by
  classical
  set K₀ := ‖Corr (Ideal.Quotient.mk _ (generator ⊤)) (Ideal.Quotient.mk _ (generator ⊤))‖
  set B : Ideal 𝓔 → ℝ := fun g =>
    Y * K₀ * ‖gaoZhaoTransform P 0‖ * (2 : ℝ) ^ Multiset.card (normalizedFactors g)
  have hB : ∀ g, 0 ≤ B g := fun g => by positivity
  have hterm : ∀ t ∈ passSplits X, ‖passDual κ κ' φ p Corr V ℓ Y t * passZero P t‖ ≤
      if t.2.1 = ⊤ ∧ t.2.2 = ⊤ then B t.1 else 0 := by
    rintro ⟨g, z₁, z₂⟩ ht
    obtain ⟨hs, -⟩ := (mem_passSplits hX).mp ht
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      have hd := norm_finsum_dvd_le hs.1.2 ⊤ ⊤
      have hs1 := norm_splitSummand_le (p := p) (Corr := Corr) hκ hκ' hφ g ⊤ ⊤
      have hV2 : ∀ a b : ℝ, ‖V a * conj (V b)‖ ≤ 1 := fun a b => by
        rw [norm_mul, Complex.norm_conj]
        nlinarith [hV a, hV b, norm_nonneg (V a), norm_nonneg (V b)]
      have hc0 : ‖conj (pairCharacter ⊤ ⊤ 0) * gaoZhaoTransform P 0‖ ≤
          ‖gaoZhaoTransform P 0‖ := by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_pairCharacter_le _ _ _)
      have hYn : ‖((Y : ℂ) / Real.sqrt (absNorm ((⊤ : Ideal 𝓔) * ⊤)))‖ ≤ Y := by
        simp [Real.norm_of_nonneg hY]
      unfold passDual passZero
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        (norm_nonneg _)).trans ?_
      refine (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)).trans ?_
      calc _ ≤ K₀ * 1 * Y * ((2 : ℝ) ^ Multiset.card (normalizedFactors g) *
            ‖gaoZhaoTransform P 0‖) := by gcongr; exact hV2 _ _
        _ = B g := by simp only [B]; ring
    · rw [passZero, pairCharacter_zero hs.2.2.1.1 hs.2.1.1 (by tauto), map_zero, zero_mul,
        mul_zero, mul_zero, norm_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_filter, Finset.mul_sum]
  have himg : (passSplits X).filter (fun t => t.2.1 = ⊤ ∧ t.2.2 = ⊤) ⊆
      (starredLe X).image fun g => (g, ⊤, ⊤) := by
    rintro ⟨g, z₁, z₂⟩ ht
    obtain ⟨ht, rfl, rfl⟩ := Finset.mem_filter.mp ht
    obtain ⟨hs, hN, -⟩ := (mem_passSplits hX).mp ht
    exact Finset.mem_image.mpr ⟨g, (mem_starredLe hX).mpr ⟨by simpa using hN, hs.1⟩, rfl⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg himg fun t _ _ => hB _).trans_eq ?_
  rw [Finset.sum_image fun _ _ _ _ h => (Prod.mk.inj h).1]

end Masullo.QRH.MeanSquare
