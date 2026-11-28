import Masullo.QRH.MeanSquare.TransferFirst

/-!
# The second Poisson pass of the transfer

* `secondDual`: the dual form of the second pass, as it enters `exists_passBound`.
* `secondDual_le`: the second-pass dual rows `(r, r₂, h)` regroup into coprime child columns
  `columnSumCoprime ζ (conj U) (L/(Nr* Nf')) k' f' r*` with `ζ = ξ''⁻¹ ξ ξ'`,
  `f' = g v₂ e₂`, `k' = e° h e₂°` and `r* = v b₂`, at the cost of a divisor bound.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The dual form of the second pass. -/
def secondDual (ξ ξ' ξ'' : RayCharacter) (U : ℝ → ℂ) (hi K L F target : ℝ) : ℝ :=
  ∑ r ∈ passRows (hi * L),
    ∑ r₂ ∈ liveRows (secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2))
        (hi * secondLength L r),
      ∑ h ∈ elementRows (passCap hi (secondScale hi K L F target r) (secondLength L r)
          (r₂.1 * r₂.2.1) r₂.2.1),
        secondWeight K L F r * (secondScale hi K L F target r * absNorm (r₂.1 * r₂.2.1) /
          (secondLength L r * absNorm r₂.2.1)) *
          ‖∑ x ∈ passCols (hi * secondLength L r) r₂,
            dualCoeff conjGauss (secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2))
                0 2 ξ'' (r₂.1 * r₂.2.1) r₂.2.1 r₂.2.2 h x *
              U (absNorm (r₂.1 * r₂.2.1 * (r₂.2.2 * x)) / secondLength L r)‖ ^ 2


private lemma conj_rayCharacter (ξ : RayCharacter) (y : 𝓔 ⧸ span {(72 : 𝓔)}) :
    conj (ξ y) = ξ⁻¹ y := by
  have := MulChar.star_apply' ξ y
  simpa using this

private lemma conj_sextic_pow_two {n : Ideal 𝓔} (hn : AwayFromSix n) {a : 𝓔}
    (ha : IsCoprime n (span {a})) : conj (sextic n a) ^ 2 = sextic n a ^ 4 := by
  rw [conj_sextic_eq_pow_five hn ha, ← pow_mul]
  have h6 := sextic_pow_six hn ha
  calc sextic n a ^ (5 * 2) = sextic n a ^ 4 * sextic n a ^ 6 := by ring
    _ = _ := by rw [h6, mul_one]

private lemma conj_secondDual_term (ξ ξ' ξ'' : RayCharacter) (b e v b₂ e₂ v₂ : Ideal 𝓔) (h : 𝓔)
    (hg : Starred (b * e)) (hv₂ : Starred v₂) (he₂ : Starred e₂)
    {x : Ideal 𝓔} (hx : Starred x) (hc1 : IsCoprime (b * e * v) x)
    (hc2 : IsCoprime (b₂ * e₂ * v₂) x) (u : ℂ) :
    conj (dualCoeff conjGauss (secondTwist ξ ξ' (b * e) e (b * e * v)) 0 2 ξ''
        (b₂ * e₂) e₂ v₂ h x * u) =
      gaussCoefficient x * twist (ξ''⁻¹ * ξ * ξ') (generator e * h * generator e₂)
        (b * e * v₂ * e₂) x * conj u := by
  have hA := hx.1
  have hv : IsCoprime x (span {generator v₂}) := by
    rw [span_generator]; exact hc2.of_mul_left_right.symm
  have he : IsCoprime x (span {generator e₂}) := by
    rw [span_generator]; exact hc2.of_mul_left_left.of_mul_left_right.symm
  have hgen : generator (b * e * v₂ * e₂) =
      generator (b * e) * generator v₂ * generator e₂ := by
    rw [generator_mul (hg.1.coprime_three.mul_left hv₂.1.coprime_three) he₂.1.coprime_three,
      generator_mul hg.1.coprime_three hv₂.1.coprime_three]
  have h10 := conj_sextic_pow_two hA hv
  have h5 := conj_sextic_eq_pow_five hA he
  have h6 := sextic_pow_six hA he
  have hξ := conj_rayCharacter ξ'' (Ideal.Quotient.mk _ (generator x))
  simp only [twist, hA, ite_true, hgen, dualCoeff, secondTwist, hc1, conjGauss, starredGauss,
    hx, map_mul, map_pow, Complex.conj_conj, hξ, MulChar.coeToFun_mul,
    Pi.mul_apply, sextic_mul hA, sextic_pow hA, pow_zero, mul_one, h5, h10]
  ring


private lemma columnSumCoprime_eq_starredSum (ζ : RayCharacter) (W : ℝ → ℂ) {hi X : ℝ}
    (hhi : 0 < hi) (hX : 0 < X)
    (hW : ∀ t, W t ≠ 0 → t ≤ hi) (k : 𝓔) (f r : Ideal 𝓔) :
    columnSumCoprime ζ W X k f r = ∑ x ∈ starredLe (hi * X), open Classical in
      if IsCoprime x r then gaussCoefficient x * twist ζ k f x * W (absNorm x / X) else 0 := by
  classical
  have hX0 : 0 ≤ hi * X := by positivity
  unfold columnSumCoprime
  rw [finsum_eq_sum_of_support_subset (s := (starredLe (hi * X)).subtype Starred)]
  · rw [Finset.sum_subtype_eq_sum_filter (f := fun n : Ideal 𝓔 =>
      if IsCoprime n r then gaussCoefficient n * twist ζ k f n * W (absNorm n / X) else 0)]
    have : (starredLe (hi * X)).filter Starred = starredLe (hi * X) :=
      Finset.filter_true_of_mem fun n hn => ((mem_starredLe hX0).mp hn).2
    rw [this]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.mem_coe, Finset.mem_subtype, mem_starredLe hX0]
    refine ⟨?_, n.2⟩
    by_contra hlt
    rw [not_le] at hlt
    refine hn ?_
    have : ¬ (absNorm n.1 : ℝ) / X ≤ hi := by
      rw [div_le_iff₀ hX]; linarith
    have hW0 : W (absNorm n.1 / X) = 0 := by
      by_contra hne; exact this (hW _ hne)
    simp [hW0]


private lemma twist_eq_zero_of_not_coprime (ζ : RayCharacter) (k : 𝓔) {f x : Ideal 𝓔}
    (hx : AwayFromSix x) (hf : ¬ IsCoprime x f) : twist ζ k f x = 0 := by
  unfold twist
  have h0 : sextic x (generator f) = 0 :=
    sextic_eq_zero hx (by rwa [span_generator])
  simp only [hx, ↓reduceIte, sextic_mul hx, sextic_pow hx, h0]
  simp

private lemma coprime_of_twist_ne_zero (ζ : RayCharacter) (k : 𝓔) {f x : Ideal 𝓔}
    (hx : AwayFromSix x) (h : twist ζ k f x ≠ 0) : IsCoprime x f :=
  by_contra fun hf => h (twist_eq_zero_of_not_coprime ζ k hx hf)

private lemma norm_secondColumn_eq (ξ ξ' ξ'' : RayCharacter) (U : ℝ → ℂ) {hi L : ℝ}
    (hhi : 0 < hi) (hL : 0 < L) (hU : ∀ t, U t ≠ 0 → t ≤ hi)
    (b e v b₂ e₂ v₂ : Ideal 𝓔) (h : 𝓔) (hg : Starred (b * e)) (hv : Starred v)
    (hg₂ : Starred (b₂ * e₂)) (hv₂ : Starred v₂) (he₂ : Starred e₂) :
    ‖∑ x ∈ passCols (hi * secondLength L (b, e, v)) (b₂, e₂, v₂),
        dualCoeff conjGauss (secondTwist ξ ξ' (b * e) e (b * e * v)) 0 2 ξ'' (b₂ * e₂) e₂ v₂ h x *
          U (absNorm (b₂ * e₂ * (v₂ * x)) / secondLength L (b, e, v))‖ =
      ‖columnSumCoprime (ξ''⁻¹ * ξ * ξ') (fun t => conj (U t))
        (L / (absNorm (v * b₂) * absNorm (b * e * v₂ * e₂))) (generator e * h * generator e₂)
        (b * e * v₂ * e₂) (v * b₂)‖ := by
  classical
  have hgb : b * e ≠ ⊥ := hg.1.1
  have hv0 : v ≠ ⊥ := hv.1.1
  have hg₂0 : b₂ * e₂ ≠ ⊥ := hg₂.1.1
  have hv₂0 : v₂ ≠ ⊥ := hv₂.1.1
  have he₂0 : e₂ ≠ ⊥ := he₂.1.1
  have hb₂0 : b₂ ≠ ⊥ := fun h0 => hg₂0 (by rw [h0, bot_mul])
  have he0 : e ≠ ⊥ := fun h0 => hgb (by rw [h0, mul_bot])
  have hgv0 : b * e * v ≠ ⊥ := fun h0 => (Ideal.mul_eq_bot.mp h0).elim hgb hv0
  have hg₂v₂0 : b₂ * e₂ * v₂ ≠ ⊥ := fun h0 => (Ideal.mul_eq_bot.mp h0).elim hg₂0 hv₂0
  have hrs0 : v * b₂ ≠ ⊥ := fun h0 => (Ideal.mul_eq_bot.mp h0).elim hv0 hb₂0
  have hf0 : b * e * v₂ * e₂ ≠ ⊥ := fun h0 =>
    (Ideal.mul_eq_bot.mp h0).elim (fun h1 => (Ideal.mul_eq_bot.mp h1).elim hgb hv₂0) he₂0
  have hN1 := absNorm_one_le hgv0
  have hN2 := absNorm_one_le hg₂v₂0
  have hN3 := absNorm_one_le hrs0
  have hN4 := absNorm_one_le hf0
  have hnorm : (absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂) =
      absNorm (b * e * v) * absNorm (b₂ * e₂ * v₂) := by
    simp only [map_mul]; push_cast; ring
  have hℓ : 0 < secondLength L (b, e, v) := by unfold secondLength; positivity
  have hX'pos : 0 < L / ((absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂)) := by positivity
  have hlen : secondLength (secondLength L (b, e, v)) (b₂, e₂, v₂) =
      L / ((absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂)) := by
    unfold secondLength
    dsimp only
    rw [div_div, hnorm]
  have hpos : ∀ x : Ideal 𝓔, (absNorm (b₂ * e₂ * (v₂ * x)) : ℝ) / secondLength L (b, e, v) =
      absNorm x / (L / ((absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂))) := by
    intro x
    unfold secondLength
    dsimp only
    rw [hnorm]
    simp only [map_mul]; push_cast
    field_simp
  rw [columnSumCoprime_eq_starredSum _ _ hhi hX'pos
    (fun t ht => hU t fun h0 => ht (by simp [h0]))]
  rw [← Complex.norm_conj, map_sum]
  refine congrArg norm ?_
  have hX1 : 0 ≤ hi * secondLength (secondLength L (b, e, v)) (b₂, e₂, v₂) := by
    rw [hlen]; positivity
  have hsub : passCols (hi * secondLength L (b, e, v)) (b₂, e₂, v₂) ⊆
      starredLe (hi * (L / ((absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂)))) := by
    intro x hx
    have := ((mem_passCols_iff hhi hℓ (r := (b₂, e₂, v₂)) hN2).mp hx).1
    rwa [hlen] at this
  have hX2 : 0 ≤ hi * (L / ((absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂))) := by positivity
  refine Eq.trans (Finset.sum_congr rfl ?_) (Finset.sum_subset hsub ?_)
  · intro x hx
    obtain ⟨hxs, hcx⟩ := (mem_passCols_iff hhi hℓ (r := (b₂, e₂, v₂)) hN2).mp hx
    have hxS : Starred x := ((mem_starredLe hX1).mp hxs).2
    rw [hpos x]
    by_cases hc1 : IsCoprime (b * e * v) x
    · have hcr : IsCoprime x (v * b₂) :=
        hc1.of_mul_left_right.symm.mul_right hcx.of_mul_left_left.of_mul_left_left.symm
      simp only [hcr, ↓reduceIte]
      exact conj_secondDual_term ξ ξ' ξ'' b e v b₂ e₂ v₂ h hg hv₂ he₂ hxS hc1 hcx _
    · have h0 : secondTwist ξ ξ' (b * e) e (b * e * v) x = 0 := by simp [secondTwist, hc1]
      have hA : dualCoeff conjGauss (secondTwist ξ ξ' (b * e) e (b * e * v)) 0 2 ξ''
          (b₂ * e₂) e₂ v₂ h x = 0 := by simp [dualCoeff, h0]
      rw [hA, zero_mul, map_zero]
      by_cases hcr : IsCoprime x (v * b₂)
      · simp only [hcr, ↓reduceIte]
        have hnf : ¬ IsCoprime x (b * e * v₂ * e₂) := fun hf => hc1
          (IsCoprime.mul_right (hf.of_isCoprime_of_dvd_right (Dvd.intro (v₂ * e₂) (by ring)))
            (hcr.of_isCoprime_of_dvd_right (dvd_mul_right v b₂))).symm
        rw [twist_eq_zero_of_not_coprime _ _ hxS.1 hnf]
        simp
      · simp [hcr]
  · intro x hx hnot
    have hxS : Starred x := ((mem_starredLe hX2).mp hx).2
    by_cases hcr : IsCoprime x (v * b₂)
    · simp only [hcr, ↓reduceIte]
      by_contra hne
      have hT : twist (ξ''⁻¹ * ξ * ξ') (generator e * h * generator e₂) (b * e * v₂ * e₂) x ≠ 0 :=
        fun h0 => hne (by rw [h0]; simp)
      have hcf := coprime_of_twist_ne_zero _ _ hxS.1 hT
      refine hnot ((mem_passCols_iff hhi hℓ (r := (b₂, e₂, v₂)) hN2).mpr ⟨by rwa [hlen], ?_⟩)
      exact (IsCoprime.mul_right (IsCoprime.mul_right
        (hcr.of_isCoprime_of_dvd_right (Dvd.intro_left v rfl))
        (hcf.of_isCoprime_of_dvd_right (Dvd.intro (b * e * v₂) (by ring))))
        (hcf.of_isCoprime_of_dvd_right (Dvd.intro (b * e * e₂) (by ring)))).symm
    · simp [hcr]


private lemma starred_of_dvd' {m n : Ideal 𝓔} (hn : Starred n) (h : m ∣ n) : Starred m := by
  refine ⟨⟨fun hm => hn.1.1 ?_, hn.1.2.of_isCoprime_of_dvd_left h⟩, hn.2.squarefree_of_dvd h⟩
  rw [hm] at h
  exact le_bot_iff.mp (Ideal.le_of_dvd h)

private lemma row_facts (ξ ξ' : RayCharacter) {hi L : ℝ} {b e v b₂ e₂ v₂ : Ideal 𝓔}
    (hr : (b, e, v) ∈ passRows (hi * L))
    (hr₂ : (b₂, e₂, v₂) ∈ liveRows (secondTwist ξ ξ' (b * e) e (b * e * v))
      (hi * secondLength L (b, e, v))) :
    Starred (b * e) ∧ Starred v ∧ Starred (b₂ * e₂) ∧ Starred v₂ ∧ Starred e₂ ∧
      Starred (v * b₂) ∧ Starred (b * e * v₂ * e₂) ∧ IsCoprime (b * e * v) (b₂ * e₂) ∧
      IsCoprime (b * e * v) v₂ ∧ IsCoprime (b₂ * e₂) v₂ := by
  classical
  obtain ⟨-, hS1, hS2, -⟩ := Finset.mem_filter.mp hr
  obtain ⟨hr₂', hφ1, hφ2⟩ := Finset.mem_filter.mp hr₂
  obtain ⟨-, hT1, hT2, hT3⟩ := Finset.mem_filter.mp hr₂'
  have hcop : ∀ n, secondTwist ξ ξ' (b * e) e (b * e * v) n ≠ 0 → IsCoprime (b * e * v) n :=
    fun n hn => by
      by_contra hc
      exact hn (by simp [secondTwist, hc])
  have hc1 := hcop _ hφ1
  have hc2 := hcop _ hφ2
  have hb₂ : Starred b₂ := starred_of_dvd' hT1 (dvd_mul_right b₂ e₂)
  have he₂ : Starred e₂ := starred_of_dvd' hT1 (dvd_mul_left e₂ b₂)
  have hvb : IsCoprime v b₂ :=
    (hc1.of_isCoprime_of_dvd_left (dvd_mul_left v (b * e))).of_mul_right_left
  have hgv₂ : IsCoprime (b * e) v₂ :=
    hc2.of_isCoprime_of_dvd_left (dvd_mul_right (b * e) v)
  have hge₂ : IsCoprime (b * e) e₂ :=
    (hc1.of_isCoprime_of_dvd_left (dvd_mul_right (b * e) v)).of_mul_right_right
  have hve₂ : IsCoprime e₂ v₂ := hT3.of_mul_left_right
  refine ⟨hS1, hS2, hT1, hT2, he₂, hS2.mul_of_isCoprime hb₂ hvb,
    (hS1.mul_of_isCoprime hT2 hgv₂).mul_of_isCoprime he₂
      (IsCoprime.mul_left hge₂ hve₂.symm), hc1, hc2, hT3⟩


private lemma weight_eq {hi K L F target : ℝ} (hK : 0 < K) (hL : 0 < L) (hF : 0 < F)
    {b e v b₂ e₂ : Ideal 𝓔} (hb : b ≠ ⊥) (he : e ≠ ⊥) (hv : v ≠ ⊥) (hb₂ : b₂ ≠ ⊥)
    (he₂ : e₂ ≠ ⊥) :
    secondWeight K L F (b, e, v) *
        (secondScale hi K L F target (b, e, v) * absNorm (b₂ * e₂) /
          (secondLength L (b, e, v) * absNorm e₂)) =
      max 1 (4 * hi ^ 2) * target * absNorm (v * b₂) / L ^ 2 := by
  have h1 := absNorm_one_le hb
  have h2 := absNorm_one_le he
  have h3 := absNorm_one_le hv
  have h4 := absNorm_one_le hb₂
  have h5 := absNorm_one_le he₂
  unfold secondWeight secondScale secondLength
  simp only [map_mul]
  push_cast
  field_simp

private lemma elementNorm_mul' (a c : 𝓔) :
    (elementNorm (a * c) : ℝ) = elementNorm a * elementNorm c := by
  unfold elementNorm
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  push_cast; ring

private lemma elementNorm_generator' (e : Ideal 𝓔) :
    (elementNorm (generator e) : ℝ) = absNorm e := by
  unfold elementNorm
  rw [span_generator]

private lemma rowk_mem {hi K L F target : ℝ} (hhi : 0 < hi) (hK : 0 < K) (hL : 0 < L)
    (hF : 0 < F) (htarget : 0 < target)
    {b e v b₂ e₂ : Ideal 𝓔} (hb : b ≠ ⊥) (he : e ≠ ⊥) (hv : v ≠ ⊥) (hb₂ : b₂ ≠ ⊥)
    (he₂ : e₂ ≠ ⊥) {h : 𝓔}
    (hh : h ∈ elementRows (passCap hi (secondScale hi K L F target (b, e, v))
      (secondLength L (b, e, v)) (b₂ * e₂) e₂)) :
    generator e * h * generator e₂ ∈
      elementRows (K * L / (target * F * (absNorm (v * b₂) : ℝ) ^ 2)) := by
  have h1 := absNorm_one_le hb
  have h2 := absNorm_one_le he
  have h3 := absNorm_one_le hv
  have h4 := absNorm_one_le hb₂
  have h5 := absNorm_one_le he₂
  have hc : 0 < max 1 (4 * hi ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcap : passCap hi (secondScale hi K L F target (b, e, v)) (secondLength L (b, e, v))
      (b₂ * e₂) e₂ = hi ^ 2 / max 1 (4 * hi ^ 2) *
        (K * L / (target * F * (absNorm (v * b₂) : ℝ) ^ 2)) / (absNorm e * absNorm e₂) := by
    unfold passCap secondScale secondLength
    simp only [map_mul]
    push_cast
    field_simp
  have hcap0 : 0 ≤ passCap hi (secondScale hi K L F target (b, e, v))
      (secondLength L (b, e, v)) (b₂ * e₂) e₂ := by rw [hcap]; positivity
  obtain ⟨hh0, hhN⟩ := (mem_elementRows hcap0).mp hh
  have hR : 0 ≤ K * L / (target * F * (absNorm (v * b₂) : ℝ) ^ 2) := by positivity
  have hgen : ∀ d : Ideal 𝓔, d ≠ ⊥ → generator d ≠ 0 := fun d hd h0 =>
    hd (by rw [← span_generator d, h0]; simp)
  refine (mem_elementRows hR).mpr ⟨mul_ne_zero (mul_ne_zero (hgen e he) hh0) (hgen e₂ he₂), ?_⟩
  rw [elementNorm_mul', elementNorm_mul', elementNorm_generator', elementNorm_generator']
  rw [hcap] at hhN
  have hle : hi ^ 2 / max 1 (4 * hi ^ 2) ≤ 1 := by
    rw [div_le_one hc]; exact le_trans (by nlinarith) (le_max_right _ _)
  have hN : (0 : ℝ) < absNorm e * absNorm e₂ := by positivity
  calc (absNorm e : ℝ) * elementNorm h * absNorm e₂
      = (absNorm e * absNorm e₂) * elementNorm h := by ring
    _ ≤ (absNorm e * absNorm e₂) * (hi ^ 2 / max 1 (4 * hi ^ 2) *
        (K * L / (target * F * (absNorm (v * b₂) : ℝ) ^ 2)) / (absNorm e * absNorm e₂)) :=
        mul_le_mul_of_nonneg_left hhN hN.le
    _ = hi ^ 2 / max 1 (4 * hi ^ 2) * (K * L / (target * F * (absNorm (v * b₂) : ℝ) ^ 2)) := by
        field_simp
    _ ≤ 1 * (K * L / (target * F * (absNorm (v * b₂) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hle hR
    _ = _ := one_mul _


private abbrev SrcRow := Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔
private abbrev SrcRows := Σ _ : SrcRow, Σ _ : SrcRow, 𝓔
private abbrev TgtRows := Σ _ : Ideal 𝓔, Σ _ : Ideal 𝓔, 𝓔

private def rowMap (a : SrcRows) : TgtRows :=
  ⟨a.1.2.2 * a.2.1.1, ⟨a.1.1 * a.1.2.1 * a.2.1.2.2 * a.2.1.2.1,
    generator a.1.2.1 * a.2.2 * generator a.2.1.2.1⟩⟩

open Classical in
private lemma fibre_card_le (S : Finset SrcRows)
    (hnz : ∀ a ∈ S, a.1.1 ≠ ⊥ ∧ a.1.2.1 ≠ ⊥ ∧ a.1.2.2 ≠ ⊥ ∧ a.2.1.1 ≠ ⊥ ∧ a.2.1.2.1 ≠ ⊥ ∧
      a.2.1.2.2 ≠ ⊥) (y : TgtRows) (hR : y.1 ≠ ⊥) (hF : y.2.1 ≠ ⊥) :
    ((S.filter fun a => rowMap a = y).card : ℝ) ≤
      ((idealDivisors y.1).card : ℝ) * ((idealDivisors y.2.1).card : ℝ) ^ 4 := by
  have hcard : (S.filter fun a => rowMap a = y).card ≤
      (idealDivisors y.1 ×ˢ (idealDivisors y.2.1 ×ˢ (idealDivisors y.2.1 ×ˢ
        (idealDivisors y.2.1 ×ˢ idealDivisors y.2.1)))).card := by
    refine Finset.card_le_card_of_injOn
      (fun a => (a.1.2.2, a.1.1, a.1.2.1, a.2.1.2.2, a.2.1.2.1)) ?_ ?_
    · rintro ⟨⟨b, e, v⟩, ⟨b₂, e₂, v₂⟩, h⟩ ha
      obtain ⟨-, hy⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      have hy1 : v * b₂ = y.1 := congrArg (fun z : TgtRows => z.1) hy
      have hy2 : b * e * v₂ * e₂ = y.2.1 := congrArg (fun z : TgtRows => z.2.1) hy
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_idealDivisors hR,
        mem_idealDivisors hF]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← hy1]; exact dvd_mul_right v b₂
      · rw [← hy2]; exact Dvd.intro (e * v₂ * e₂) (by ring)
      · rw [← hy2]; exact Dvd.intro_left (b * v₂ * e₂) (by ring)
      · rw [← hy2]; exact Dvd.intro_left (b * e * e₂) (by ring)
      · rw [← hy2]; exact dvd_mul_left e₂ _
    · rintro ⟨⟨b, e, v⟩, ⟨b₂, e₂, v₂⟩, h⟩ ha ⟨⟨b', e', v'⟩, ⟨b₂', e₂', v₂'⟩, h'⟩ ha' heq
      obtain ⟨haS, hy⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      obtain ⟨-, hy'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha')
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
      have hn := hnz _ haS
      have hv0 : v ≠ ⊥ := hn.2.2.1
      have he0 : e ≠ ⊥ := hn.2.1
      have he₂0 : e₂ ≠ ⊥ := hn.2.2.2.2.1
      have hgen : ∀ d : Ideal 𝓔, d ≠ ⊥ → generator d ≠ 0 := fun d hd h0 =>
        hd (by rw [← span_generator d, h0]; simp)
      have hy1 : v * b₂ = v * b₂' := (congrArg (fun z : TgtRows => z.1) hy).trans
        (congrArg (fun z : TgtRows => z.1) hy').symm
      have hy3 : generator e * h * generator e₂ = generator e * h' * generator e₂ :=
        (congrArg (fun z : TgtRows => z.2.2) hy).trans
          (congrArg (fun z : TgtRows => z.2.2) hy').symm
      have hb : b₂ = b₂' := mul_left_cancel₀ hv0 hy1
      have hh : h = h' :=
        mul_left_cancel₀ (hgen e he0) (mul_right_cancel₀ (hgen e₂ he₂0) hy3)
      subst hb hh
      rfl
  have hcast : ((S.filter fun a => rowMap a = y).card : ℝ) ≤ (((idealDivisors y.1 ×ˢ
      (idealDivisors y.2.1 ×ˢ (idealDivisors y.2.1 ×ˢ (idealDivisors y.2.1 ×ˢ
        idealDivisors y.2.1)))).card : ℕ) : ℝ) := by exact_mod_cast hcard
  refine hcast.trans_eq ?_
  simp only [Finset.card_product]
  push_cast
  ring


private lemma sum_fibre_le {α β : Type*} [DecidableEq β] (S : Finset α) (π : α → β)
    (F : β → ℝ) (Y : Finset β) {T : ℝ} (hF : ∀ y, 0 ≤ F y) (hmaps : ∀ a ∈ S, π a ∈ Y)
    (hcard : ∀ y ∈ Y, ((S.filter fun a => π a = y).card : ℝ) ≤ T) :
    ∑ a ∈ S, F (π a) ≤ T * ∑ y ∈ Y, F y := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  have : ∑ a ∈ S with π a = y, F (π a) = (S.filter fun a => π a = y).card • F y := by
    rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
      Finset.sum_const]
  rw [this, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hcard y hy) (hF y)

theorem secondDual_le (ξ ξ' ξ'' : RayCharacter) (U : ℝ → ℂ) {hi K L F target T : ℝ}
    (hhi : 0 < hi) (hK : 0 < K) (hL : 0 < L) (hF : 0 < F) (htarget : 0 < target)
    (hU : ∀ t, U t ≠ 0 → t ≤ hi) (hT0 : 0 ≤ T)
    (hT : ∀ a b : Ideal 𝓔, a ≠ ⊥ → b ≠ ⊥ → (absNorm a : ℝ) * absNorm b ≤ hi * L →
      ((idealDivisors a).card : ℝ) * ((idealDivisors b).card : ℝ) ^ 4 ≤ T) :
    secondDual ξ ξ' ξ'' U hi K L F target ≤
      T * ∑ r ∈ starredLe (hi * L), max 1 (4 * hi ^ 2) * target * absNorm r / L ^ 2 *
        ∑ f ∈ starredLe (hi * L / absNorm r),
          ∑ k ∈ elementRows (K * L / (target * F * (absNorm r : ℝ) ^ 2)),
            ‖columnSumCoprime (ξ''⁻¹ * ξ * ξ') (fun t => conj (U t))
              (L / (absNorm r * absNorm f)) k f r‖ ^ 2 := by
  classical
  have hc0 : 0 < max 1 (4 * hi ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  let Wt : Ideal 𝓔 → ℝ := fun r => max 1 (4 * hi ^ 2) * target * absNorm r / L ^ 2
  let CS : TgtRows → ℝ := fun y => Wt y.1 * ‖columnSumCoprime (ξ''⁻¹ * ξ * ξ')
    (fun t => conj (U t)) (L / (absNorm y.1 * absNorm y.2.1)) y.2.2 y.2.1 y.1‖ ^ 2
  let S : Finset SrcRows := (passRows (hi * L)).sigma fun r =>
    (liveRows (secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2))
      (hi * secondLength L r)).sigma fun r₂ =>
      elementRows (passCap hi (secondScale hi K L F target r) (secondLength L r)
        (r₂.1 * r₂.2.1) r₂.2.1)
  let G : SrcRows → ℝ := fun a =>
    secondWeight K L F a.1 * (secondScale hi K L F target a.1 *
      absNorm (a.2.1.1 * a.2.1.2.1) / (secondLength L a.1 * absNorm a.2.1.2.1)) *
      ‖∑ x ∈ passCols (hi * secondLength L a.1) a.2.1,
        dualCoeff conjGauss (secondTwist ξ ξ' (a.1.1 * a.1.2.1) a.1.2.1
          (a.1.1 * a.1.2.1 * a.1.2.2)) 0 2 ξ'' (a.2.1.1 * a.2.1.2.1) a.2.1.2.1 a.2.1.2.2
          a.2.2 x * U (absNorm (a.2.1.1 * a.2.1.2.1 * (a.2.1.2.2 * x)) /
            secondLength L a.1)‖ ^ 2
  have h1 : secondDual ξ ξ' ξ'' U hi K L F target = ∑ a ∈ S, G a := by
    unfold secondDual
    simp only [S, G, Finset.sum_sigma']
  let P : SrcRows → Prop := fun a =>
    (absNorm (a.2.1.1 * a.2.1.2.1 * a.2.1.2.2) : ℝ) ≤ hi * secondLength L a.1
  have hzero : ∀ a ∈ S, G a ≠ 0 → P a := by
    intro a ha hne
    by_contra hP
    refine hne ?_
    have hsum : ∑ x ∈ passCols (hi * secondLength L a.1) a.2.1,
        dualCoeff conjGauss (secondTwist ξ ξ' (a.1.1 * a.1.2.1) a.1.2.1
          (a.1.1 * a.1.2.1 * a.1.2.2)) 0 2 ξ'' (a.2.1.1 * a.2.1.2.1) a.2.1.2.1 a.2.1.2.2
          a.2.2 x * U (absNorm (a.2.1.1 * a.2.1.2.1 * (a.2.1.2.2 * x)) /
            secondLength L a.1) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      exfalso
      refine hP ?_
      unfold passCols at hx
      obtain ⟨-, hs, -, hle⟩ := Finset.mem_filter.mp hx
      have hNx := absNorm_one_le hs.1.1
      have : (absNorm (a.2.1.1 * a.2.1.2.1 * a.2.1.2.2 * x) : ℝ) =
          absNorm (a.2.1.1 * a.2.1.2.1 * a.2.1.2.2) * absNorm x := by
        rw [map_mul]; push_cast; ring
      rw [this] at hle
      exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hNx).trans hle
    simp only [G, hsum, norm_zero]
    simp
  have hmem : ∀ (b e v b₂ e₂ v₂ : Ideal 𝓔) (h : 𝓔),
      (⟨(b, e, v), ⟨(b₂, e₂, v₂), h⟩⟩ : SrcRows) ∈ S.filter P →
      (b, e, v) ∈ passRows (hi * L) ∧
      (b₂, e₂, v₂) ∈ liveRows (secondTwist ξ ξ' (b * e) e (b * e * v))
        (hi * secondLength L (b, e, v)) ∧
      h ∈ elementRows (passCap hi (secondScale hi K L F target (b, e, v))
        (secondLength L (b, e, v)) (b₂ * e₂) e₂) ∧
      (absNorm (b₂ * e₂ * v₂) : ℝ) ≤ hi * secondLength L (b, e, v) := by
    intro b e v b₂ e₂ v₂ h ha
    obtain ⟨haS, hP⟩ := Finset.mem_filter.mp ha
    simp only [S, Finset.mem_sigma] at haS
    exact ⟨haS.1, haS.2.1, haS.2.2, hP⟩
  let Y : Finset TgtRows := (starredLe (hi * L)).sigma fun r =>
    (starredLe (hi * L / absNorm r)).sigma fun _ =>
      elementRows (K * L / (target * F * (absNorm r : ℝ) ^ 2))
  have hnb : ∀ b e : Ideal 𝓔, b * e ≠ ⊥ → b ≠ ⊥ ∧ e ≠ ⊥ := fun b e hbe =>
    ⟨fun h0 => hbe (by rw [h0, bot_mul]), fun h0 => hbe (by rw [h0, mul_bot])⟩
  have hnz : ∀ a ∈ S.filter P, a.1.1 ≠ ⊥ ∧ a.1.2.1 ≠ ⊥ ∧ a.1.2.2 ≠ ⊥ ∧ a.2.1.1 ≠ ⊥ ∧
      a.2.1.2.1 ≠ ⊥ ∧ a.2.1.2.2 ≠ ⊥ := by
    rintro ⟨⟨b, e, v⟩, ⟨b₂, e₂, v₂⟩, h⟩ ha
    obtain ⟨hr, hr₂, -, -⟩ := hmem b e v b₂ e₂ v₂ h ha
    obtain ⟨hg, hv, hg₂, hv₂, -⟩ := row_facts ξ ξ' hr hr₂
    exact ⟨(hnb _ _ hg.1.1).1, (hnb _ _ hg.1.1).2, hv.1.1, (hnb _ _ hg₂.1.1).1,
      (hnb _ _ hg₂.1.1).2, hv₂.1.1⟩
  have hprod : ∀ (b e v b₂ e₂ v₂ : Ideal 𝓔), b * e ≠ ⊥ → v ≠ ⊥ → b₂ * e₂ ≠ ⊥ → v₂ ≠ ⊥ →
      (absNorm (b₂ * e₂ * v₂) : ℝ) ≤ hi * secondLength L (b, e, v) →
      (absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂) ≤ hi * L := by
    intro b e v b₂ e₂ v₂ hg hv hg₂ hv₂ hP'
    have hgv0 : b * e * v ≠ ⊥ := fun h0 => (Ideal.mul_eq_bot.mp h0).elim hg hv
    have hN := absNorm_one_le hgv0
    have hnorm : (absNorm (v * b₂) : ℝ) * absNorm (b * e * v₂ * e₂) =
        absNorm (b * e * v) * absNorm (b₂ * e₂ * v₂) := by
      simp only [map_mul]; push_cast; ring
    rw [hnorm]
    unfold secondLength at hP'
    dsimp only at hP'
    rw [← mul_div_assoc, le_div_iff₀ (by linarith)] at hP'
    linarith
  have hmaps : ∀ a ∈ S.filter P, rowMap a ∈ Y := by
    rintro ⟨⟨b, e, v⟩, ⟨b₂, e₂, v₂⟩, h⟩ ha
    obtain ⟨hr, hr₂, hh, hP'⟩ := hmem b e v b₂ e₂ v₂ h ha
    obtain ⟨hg, hv, hg₂, hv₂, he₂, hrs, hf, -⟩ := row_facts ξ ξ' hr hr₂
    obtain ⟨hb, he⟩ := hnb _ _ hg.1.1
    obtain ⟨hb₂, he₂0⟩ := hnb _ _ hg₂.1.1
    have hpr := hprod b e v b₂ e₂ v₂ hg.1.1 hv.1.1 hg₂.1.1 hv₂.1.1 hP'
    have hNr := absNorm_one_le hrs.1.1
    have hNf := absNorm_one_le hf.1.1
    have hX : 0 ≤ hi * L := by positivity
    simp only [rowMap, Y, Finset.mem_sigma]
    refine ⟨(mem_starredLe hX).mpr ⟨?_, hrs⟩, (mem_starredLe (by positivity)).mpr
      ⟨(le_div_iff₀ (by linarith)).mpr (by linarith), hf⟩,
      rowk_mem hhi hK hL hF htarget hb he hv.1.1 hb₂ he₂0 hh⟩
    nlinarith
  have hCS : ∀ y, 0 ≤ CS y := fun y => mul_nonneg (by simp only [Wt]; positivity) (sq_nonneg _)
  have hcard : ∀ y ∈ Y, ((((S.filter P).filter fun a => rowMap a = y)).card : ℝ) ≤ T := by
    rintro ⟨R, Fp, K'⟩ hy
    simp only [Y, Finset.mem_sigma] at hy
    obtain ⟨hR, hF', -⟩ := hy
    have hX : 0 ≤ hi * L := by positivity
    obtain ⟨-, hRs⟩ := (mem_starredLe hX).mp hR
    have hNR := absNorm_one_le hRs.1.1
    obtain ⟨hFle, hFs⟩ := (mem_starredLe (by positivity)).mp hF'
    refine (fibre_card_le (S.filter P) hnz ⟨R, Fp, K'⟩ hRs.1.1 hFs.1.1).trans
      (hT R Fp hRs.1.1 hFs.1.1 ?_)
    rwa [le_div_iff₀ (by linarith), mul_comm] at hFle
  have h3 : ∀ a ∈ S.filter P, G a = CS (rowMap a) := by
    rintro ⟨⟨b, e, v⟩, ⟨b₂, e₂, v₂⟩, h⟩ ha
    obtain ⟨hr, hr₂, hh, hP'⟩ := hmem b e v b₂ e₂ v₂ h ha
    obtain ⟨hg, hv, hg₂, hv₂, he₂, hrs, hf, -⟩ := row_facts ξ ξ' hr hr₂
    obtain ⟨hb, he⟩ := hnb _ _ hg.1.1
    obtain ⟨hb₂, he₂0⟩ := hnb _ _ hg₂.1.1
    have e1 := weight_eq (hi := hi) (target := target) hK hL hF hb he hv.1.1 hb₂ he₂0
    have e2 := norm_secondColumn_eq ξ ξ' ξ'' U hhi hL hU b e v b₂ e₂ v₂ h hg hv hg₂ hv₂ he₂
    simp only [G, CS, Wt, rowMap]
    rw [e1, e2]
  have h5 : ∑ y ∈ Y, CS y = ∑ r ∈ starredLe (hi * L), max 1 (4 * hi ^ 2) * target *
      absNorm r / L ^ 2 * ∑ f ∈ starredLe (hi * L / absNorm r),
        ∑ k ∈ elementRows (K * L / (target * F * (absNorm r : ℝ) ^ 2)),
          ‖columnSumCoprime (ξ''⁻¹ * ξ * ξ') (fun t => conj (U t))
            (L / (absNorm r * absNorm f)) k f r‖ ^ 2 := by
    simp only [Y, Finset.sum_sigma, CS, Wt, Finset.mul_sum]
  rw [h1, ← h5, ← Finset.sum_filter_of_ne hzero,
    Finset.sum_congr rfl h3]
  exact sum_fibre_le (S.filter P) rowMap CS Y hCS hmaps hcard

end Masullo.QRH.MeanSquare
