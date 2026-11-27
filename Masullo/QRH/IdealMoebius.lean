import Mathlib
import Masullo.Smoothed

/-!
# The ideal Möbius function of `ℚ(√-3)`

Let `𝓔 = 𝓞 (CyclotomicField 3 ℚ)`, the Eisenstein integers. `idealMoebius 𝔞` is `(-1) ^ r` on a
product of `r` distinct prime ideals and `0` on the other ideals, `⊥` included. `moebiusSum 𝔭 W D`
is `∑ μ(𝔞) W (N𝔞 / D)` over the nonzero ideals `𝔞` coprime to `6` and to `𝔭`.

The sum of `idealMoebius` over the ideals of norm `n` is `eisensteinMoebius n = (μ ∗ χ₃μ) n`
(`sum_idealMoebius_absNorm_eq`). Both sides are multiplicative, and the local polynomials are
`(1 - T)²` at the split primes `p ≡ 1 mod 3`, `1 - T²` at the inert primes `p ≡ 2 mod 3` and
`1 - T` at the ramified prime `3`. The splitting comes from
`IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd` and its companions.
-/

open NumberField Ideal UniqueFactorizationMonoid
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace Masullo.QRH

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private theorem isCyclotomicExtension : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  have : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
  CyclotomicField.isCyclotomicExtension 3 ℚ

attribute [local instance] isCyclotomicExtension

/-- The ideal Möbius function: `(-1) ^ r` on a product of `r` distinct prime ideals, else `0`. -/
noncomputable def idealMoebius (𝔞 : Ideal 𝓔) : ℤ :=
  open Classical in
  if Squarefree 𝔞 then (-1) ^ Multiset.card (normalizedFactors 𝔞) else 0

/-- `∑ μ(𝔞) W (N𝔞 / D)` over the nonzero ideals `𝔞` coprime to `6` and to `𝔭`. -/
noncomputable def moebiusSum (𝔭 : Ideal 𝓔) (W : ℝ → ℂ) (D : ℝ) : ℂ :=
  open Classical in
  ∑' 𝔞 : Ideal 𝓔, if 𝔞 ≠ ⊥ ∧ IsCoprime 𝔞 (span {6}) ∧ IsCoprime 𝔞 𝔭 then
    (idealMoebius 𝔞 : ℂ) * W (absNorm 𝔞 / D) else 0

/-- The ideals of norm `n`. -/
noncomputable def normFiber (n : ℕ) : Finset (Ideal 𝓔) :=
  (Ring.HasFiniteQuotients.finite_absNorm_eq n).toFinset

lemma mem_normFiber {n : ℕ} {𝔞 : Ideal 𝓔} : 𝔞 ∈ normFiber n ↔ absNorm 𝔞 = n :=
  Set.Finite.mem_toFinset _

lemma normFiber_zero : normFiber 0 = {⊥} := by
  ext 𝔞
  simp [mem_normFiber]

lemma normFiber_one : normFiber 1 = {⊤} := by
  ext 𝔞
  simp [mem_normFiber]

lemma idealMoebius_bot : idealMoebius ⊥ = 0 := by
  simp [idealMoebius, ← Submodule.zero_eq_bot]

lemma idealMoebius_top : idealMoebius ⊤ = 1 := by
  simp [idealMoebius, ← Ideal.one_eq_top]

lemma idealMoebius_mul {𝔟 𝔠 : Ideal 𝓔} (h : IsCoprime 𝔟 𝔠) :
    idealMoebius (𝔟 * 𝔠) = idealMoebius 𝔟 * idealMoebius 𝔠 := by
  unfold idealMoebius
  by_cases hb : Squarefree 𝔟
  · by_cases hc : Squarefree 𝔠
    · simp only [squarefree_mul_iff.2 ⟨h.isRelPrime, hb, hc⟩, hb, hc, ↓reduceIte,
        normalizedFactors_mul hb.ne_zero hc.ne_zero, Multiset.card_add, pow_add]
    · have h' : ¬ Squarefree (𝔟 * 𝔠) := fun h' => hc (squarefree_mul_iff.1 h').2.2
      simp [hc, h']
  · have h' : ¬ Squarefree (𝔟 * 𝔠) := fun h' => hb (squarefree_mul_iff.1 h').2.1
    simp [hb, h']

lemma isCoprime_of_natCast_mem {𝔟 𝔠 : Ideal 𝓔} {m n : ℕ} (hm : (m : 𝓔) ∈ 𝔟)
    (hn : (n : 𝓔) ∈ 𝔠) (h : Nat.Coprime m n) : IsCoprime 𝔟 𝔠 := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime h
  refine isCoprime_iff_exists.2 ⟨(u : 𝓔) * m, 𝔟.mul_mem_left _ hm, (v : 𝓔) * n,
    𝔠.mul_mem_left _ hn, ?_⟩
  exact_mod_cast congrArg (Int.cast : ℤ → 𝓔) huv

lemma absNorm_span_natCast (m : ℕ) : absNorm (span {(m : 𝓔)}) = m ^ 2 := by
  have h3 : Module.finrank ℤ 𝓔 = 2 := by
    rw [RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank 3, Nat.totient_prime Nat.prime_three]
  rw [absNorm_span_singleton, show (m : 𝓔) = algebraMap ℤ 𝓔 (m : ℤ) by simp,
    Algebra.norm_algebraMap, h3]
  simp

lemma mul_sup_span_eq {𝔟 𝔠 : Ideal 𝓔} {m : ℕ} (hm : (m : 𝓔) ∈ 𝔟)
    (h : IsCoprime 𝔠 (span {(m : 𝓔)})) : 𝔟 * 𝔠 ⊔ span {(m : 𝓔)} = 𝔟 := by
  refine le_antisymm (sup_le Ideal.mul_le_left ((span_singleton_le_iff_mem _).2 hm)) ?_
  calc 𝔟 = 𝔟 * (𝔠 ⊔ span {(m : 𝓔)}) := by rw [isCoprime_iff_sup_eq.1 h, mul_top]
    _ = 𝔟 * 𝔠 ⊔ 𝔟 * span {(m : 𝓔)} := Ideal.mul_sup _ _ _
    _ ≤ 𝔟 * 𝔠 ⊔ span {(m : 𝓔)} := sup_le_sup_left Ideal.mul_le_right _

lemma sup_span_mul_sup_span {𝔞 : Ideal 𝓔} {m n : ℕ} (hmn : ((m * n : ℕ) : 𝓔) ∈ 𝔞)
    (h : Nat.Coprime m n) : (𝔞 ⊔ span {(m : 𝓔)}) * (𝔞 ⊔ span {(n : 𝓔)}) = 𝔞 := by
  have hc : IsCoprime (span {(m : 𝓔)}) (span {(n : 𝓔)}) :=
    isCoprime_of_natCast_mem (mem_span_singleton_self _) (mem_span_singleton_self _) h
  refine le_antisymm ?_ ?_
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, span_singleton_mul_span_singleton]
    refine sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right ?_)
    rw [span_singleton_le_iff_mem]
    exact_mod_cast hmn
  · calc 𝔞 = 𝔞 * (span {(m : 𝓔)} ⊔ span {(n : 𝓔)}) := by
          rw [isCoprime_iff_sup_eq.1 hc, mul_top]
      _ = span {(m : 𝓔)} * 𝔞 ⊔ 𝔞 * span {(n : 𝓔)} := by rw [Ideal.mul_sup, mul_comm 𝔞]
      _ ≤ _ := sup_le (mul_mono le_sup_right le_sup_left) (mul_mono le_sup_left le_sup_right)

lemma absNorm_sup_span {𝔞 : Ideal 𝓔} {m n : ℕ} (hN : absNorm 𝔞 = m * n) (h : Nat.Coprime m n)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    absNorm (𝔞 ⊔ span {(m : 𝓔)}) = m ∧ absNorm (𝔞 ⊔ span {(n : 𝓔)}) = n := by
  have hmem : ((m * n : ℕ) : 𝓔) ∈ 𝔞 := hN ▸ absNorm_mem 𝔞
  have hxy := congrArg absNorm (sup_span_mul_sup_span hmem h)
  rw [map_mul, hN] at hxy
  set x := absNorm (𝔞 ⊔ span {(m : 𝓔)})
  set y := absNorm (𝔞 ⊔ span {(n : 𝓔)})
  have hx : x ∣ m ^ 2 := absNorm_span_natCast m ▸ absNorm_dvd_absNorm_of_le le_sup_right
  have hy : y ∣ n ^ 2 := absNorm_span_natCast n ▸ absNorm_dvd_absNorm_of_le le_sup_right
  have hxm : x ∣ m := (Nat.Coprime.coprime_dvd_left hx (h.pow_left 2)).dvd_of_dvd_mul_right
    (hxy ▸ dvd_mul_right x y)
  have hyn : y ∣ n := (Nat.Coprime.coprime_dvd_left hy (h.symm.pow_left 2)).dvd_of_dvd_mul_left
    (hxy ▸ dvd_mul_left y x)
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hxm
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hyn
  constructor
  · refine le_antisymm h1 (Nat.le_of_mul_le_mul_right ?_ (Nat.pos_of_ne_zero hn))
    calc m * n = x * y := hxy.symm
      _ ≤ x * n := Nat.mul_le_mul_left _ h2
  · refine le_antisymm h2 (Nat.le_of_mul_le_mul_left ?_ (Nat.pos_of_ne_zero hm))
    calc m * n = x * y := hxy.symm
      _ ≤ m * y := Nat.mul_le_mul_right _ h1

lemma sum_normFiber_mul {m n : ℕ} (h : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    ∑ 𝔞 ∈ normFiber (m * n), (idealMoebius 𝔞 : ℂ) =
      (∑ 𝔟 ∈ normFiber m, (idealMoebius 𝔟 : ℂ)) * ∑ 𝔠 ∈ normFiber n, (idealMoebius 𝔠 : ℂ) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 * x.2)
    (fun 𝔞 => (𝔞 ⊔ span {(m : 𝓔)}, 𝔞 ⊔ span {(n : 𝓔)})) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨𝔟, 𝔠⟩ hx
    simp only [Finset.mem_product, mem_normFiber] at hx ⊢
    rw [map_mul, hx.1, hx.2]
  · intro 𝔞 h𝔞
    simp only [Finset.mem_product, mem_normFiber] at h𝔞 ⊢
    exact absNorm_sup_span h𝔞 h hm hn
  · rintro ⟨𝔟, 𝔠⟩ hx
    simp only [Finset.mem_product, mem_normFiber] at hx
    have hb : (m : 𝓔) ∈ 𝔟 := hx.1 ▸ absNorm_mem 𝔟
    have hc : (n : 𝓔) ∈ 𝔠 := hx.2 ▸ absNorm_mem 𝔠
    have h1 := mul_sup_span_eq hb (isCoprime_of_natCast_mem hc (mem_span_singleton_self _) h.symm)
    have h2 := mul_sup_span_eq hc (isCoprime_of_natCast_mem hb (mem_span_singleton_self _) h)
    rw [mul_comm] at h2
    simp only [h1, h2]
  · intro 𝔞 h𝔞
    simp only [mem_normFiber] at h𝔞
    exact sup_span_mul_sup_span (by rw [← h𝔞]; exact absNorm_mem 𝔞) h
  · rintro ⟨𝔟, 𝔠⟩ hx
    simp only [Finset.mem_product, mem_normFiber] at hx
    have hb : (m : 𝓔) ∈ 𝔟 := hx.1 ▸ absNorm_mem 𝔟
    have hc : (n : 𝓔) ∈ 𝔠 := hx.2 ▸ absNorm_mem 𝔠
    rw [idealMoebius_mul (isCoprime_of_natCast_mem hb hc h), Int.cast_mul]

/-- `n ↦ ∑_{N𝔞 = n} μ(𝔞)` as an arithmetic function. -/
noncomputable def normMoebius : ArithmeticFunction ℂ where
  toFun n := ∑ 𝔞 ∈ normFiber n, (idealMoebius 𝔞 : ℂ)
  map_zero' := by simp [normFiber_zero, idealMoebius_bot]

lemma normMoebius_apply (n : ℕ) :
    normMoebius n = ∑ 𝔞 ∈ normFiber n, (idealMoebius 𝔞 : ℂ) := rfl

lemma isMultiplicative_normMoebius : normMoebius.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [normMoebius_apply, normFiber_one, idealMoebius_top], fun hm hn h => ?_⟩
  exact sum_normFiber_mul h hm hn

/-! ### Prime powers -/

section PrimePow

variable {p : ℕ} (hp : p.Prime)

include hp in
lemma natCast_ne_zero_of_prime : (p : 𝓔) ≠ 0 := by
  exact_mod_cast hp.ne_zero

include hp in
lemma mem_primesOver_iff {𝔮 : Ideal 𝓔} :
    𝔮 ∈ primesOver (span {(p : ℤ)}) 𝓔 ↔ 𝔮.IsPrime ∧ (p : 𝓔) ∈ 𝔮 := by
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · have : (p : ℤ) ∈ under ℤ 𝔮 := h2.over ▸ mem_span_singleton_self _
    simpa [under_def] using this
  · have hmax : (span {(p : ℤ)}).IsMaximal :=
      ((span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hp)).isMaximal (by simpa using hp.ne_zero)
    refine (liesOver_iff _ _).2 (hmax.eq_of_le (comap_ne_top _ h1.ne_top) ?_)
    rw [span_singleton_le_iff_mem, under_def, mem_comap]
    simpa using h2

/-- The prime ideals above `p`. -/
noncomputable def primesAbove (p : ℕ) : Finset (Ideal 𝓔) :=
  (Algebra.QuasiFinite.finite_primesOver (span {(p : ℤ)}) (S := 𝓔)).toFinset

include hp in
lemma mem_primesAbove {𝔮 : Ideal 𝓔} : 𝔮 ∈ primesAbove p ↔ 𝔮.IsPrime ∧ (p : 𝓔) ∈ 𝔮 := by
  rw [primesAbove, Set.Finite.mem_toFinset, mem_primesOver_iff hp]

include hp in
lemma prime_of_mem_primesAbove {𝔮 : Ideal 𝓔} (h : 𝔮 ∈ primesAbove p) : Prime 𝔮 := by
  obtain ⟨h1, h2⟩ := (mem_primesAbove hp).1 h
  refine prime_of_isPrime (fun h0 => natCast_ne_zero_of_prime hp ?_) h1
  simpa [h0] using h2

set_option backward.isDefEq.respectTransparency false in
include hp in
lemma absNorm_of_mem_primesAbove {𝔮 : Ideal 𝓔} (h : 𝔮 ∈ primesAbove p) :
    absNorm 𝔮 = p ^ (span {(p : ℤ)}).inertiaDegIn 𝓔 := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ (CyclotomicField 3 ℚ) := IsCyclotomicExtension.isGalois {3} ℚ _
  have h' := (mem_primesOver_iff hp).2 ((mem_primesAbove hp).1 h)
  have : 𝔮.IsPrime := h'.1
  have : 𝔮.LiesOver (span {(p : ℤ)}) := h'.2
  rw [inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) 𝔮 Gal((CyclotomicField 3 ℚ)/ℚ),
    pow_inertiaDeg]

include hp in
lemma prod_ne_zero {T : Finset (Ideal 𝓔)} (hT : T ⊆ primesAbove p) : ∏ 𝔮 ∈ T, 𝔮 ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ h𝔮 => (prime_of_mem_primesAbove hp (hT h𝔮)).ne_zero

include hp in
lemma normalizedFactors_prod {T : Finset (Ideal 𝓔)} (hT : T ⊆ primesAbove p) :
    normalizedFactors (∏ 𝔮 ∈ T, 𝔮) = T.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact normalizedFactors_prod_of_prime fun _ h𝔮 => prime_of_mem_primesAbove hp (hT h𝔮)

include hp in
lemma idealMoebius_prod {T : Finset (Ideal 𝓔)} (hT : T ⊆ primesAbove p) :
    idealMoebius (∏ 𝔮 ∈ T, 𝔮) = (-1) ^ T.card := by
  have hsq : Squarefree (∏ 𝔮 ∈ T, 𝔮) := by
    rw [squarefree_iff_nodup_normalizedFactors (prod_ne_zero hp hT), normalizedFactors_prod hp hT]
    exact T.nodup
  simp only [idealMoebius, hsq, ↓reduceIte, normalizedFactors_prod hp hT, Finset.card_val]

include hp in
lemma absNorm_prod {T : Finset (Ideal 𝓔)} (hT : T ⊆ primesAbove p) :
    absNorm (∏ 𝔮 ∈ T, 𝔮) = p ^ ((span {(p : ℤ)}).inertiaDegIn 𝓔 * T.card) := by
  rw [map_prod, Finset.prod_congr rfl fun _ h𝔮 => absNorm_of_mem_primesAbove hp (hT h𝔮),
    Finset.prod_const, ← pow_mul]

include hp in
lemma exists_eq_prod {𝔞 : Ideal 𝓔} {k : ℕ} (h𝔞 : absNorm 𝔞 = p ^ k) (hsq : Squarefree 𝔞) :
    ∃ T ⊆ primesAbove p, 𝔞 = ∏ 𝔮 ∈ T, 𝔮 := by
  have hnd := (squarefree_iff_nodup_normalizedFactors hsq.ne_zero).1 hsq
  refine ⟨(normalizedFactors 𝔞).toFinset, fun 𝔮 h𝔮 => ?_, ?_⟩
  · rw [Multiset.mem_toFinset] at h𝔮
    have hle : 𝔞 ≤ 𝔮 := le_of_dvd (dvd_of_mem_normalizedFactors h𝔮)
    have h1 : 𝔮.IsPrime := isPrime_of_prime (prime_of_normalized_factor _ h𝔮)
    refine (mem_primesAbove hp).2 ⟨h1, h1.mem_of_pow_mem k (hle ?_)⟩
    have := absNorm_mem 𝔞
    rw [h𝔞] at this
    exact_mod_cast this
  · rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup]
    exact (associated_iff_eq.1 (prod_normalizedFactors hsq.ne_zero)).symm

include hp in
/-- The sum of `idealMoebius` over the ideals of norm `p ^ k`, in terms of the primes above `p`
and their common residue degree. -/
lemma normMoebius_prime_pow (k : ℕ) :
    normMoebius (p ^ k) = ∑ T ∈ (primesAbove p).powerset,
      if (span {(p : ℤ)}).inertiaDegIn 𝓔 * T.card = k then (-1 : ℂ) ^ T.card else 0 := by
  have hinj : ∀ {a b : ℕ}, p ^ a = p ^ b → a = b := fun h => Nat.pow_right_injective hp.two_le h
  rw [normMoebius_apply]
  symm
  refine Finset.sum_bij_ne_zero (fun T _ _ => ∏ 𝔮 ∈ T, 𝔮) ?_ ?_ ?_ ?_
  · intro T hT hne
    rw [Finset.mem_powerset] at hT
    rw [mem_normFiber, absNorm_prod hp hT]
    by_contra h
    exact hne (ite_eq_right fun h' => h (by rw [h']))
  · intro T₁ hT₁ _ T₂ hT₂ _ h
    rw [Finset.mem_powerset] at hT₁ hT₂
    have := congrArg normalizedFactors h
    rw [normalizedFactors_prod hp hT₁, normalizedFactors_prod hp hT₂] at this
    exact Finset.val_inj.1 this
  · intro 𝔞 h𝔞 hne
    rw [mem_normFiber] at h𝔞
    have hsq : Squarefree 𝔞 := by
      by_contra h
      exact hne (by simp [idealMoebius, h])
    obtain ⟨T, hT, rfl⟩ := exists_eq_prod hp h𝔞 hsq
    have hk := hinj ((absNorm_prod hp hT).symm.trans h𝔞)
    exact ⟨T, Finset.mem_powerset.2 hT, by simp [hk], rfl⟩
  · intro T hT hne
    rw [Finset.mem_powerset] at hT
    have hk : (span {(p : ℤ)}).inertiaDegIn 𝓔 * T.card = k := by
      by_contra h
      exact hne (ite_eq_right h)
    rw [ite_eq_left hk, idealMoebius_prod hp hT]
    push_cast
    rfl

set_option backward.isDefEq.respectTransparency false in
include hp in
lemma card_primesAbove_mul_inertiaDegIn (hp3 : p ≠ 3) :
    (primesAbove p).card * orderOf (p : ZMod 3) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ (CyclotomicField 3 ℚ) := IsCyclotomicExtension.isGalois {3} ℚ _
  have hm : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  have h := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) 𝓔
    Gal((CyclotomicField 3 ℚ)/ℚ)
  rwa [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p _ hm,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p _ hm, one_mul,
    IsGaloisGroup.card_eq_finrank Gal((CyclotomicField 3 ℚ)/ℚ) ℚ (CyclotomicField 3 ℚ),
    IsCyclotomicExtension.Rat.finrank 3, Nat.totient_prime Nat.prime_three,
    Set.ncard_eq_toFinset_card _ (Algebra.QuasiFinite.finite_primesOver _)] at h

include hp in
lemma inertiaDegIn_of_ne_three (hp3 : p ≠ 3) :
    (span {(p : ℤ)}).inertiaDegIn 𝓔 = orderOf (p : ZMod 3) := by
  have : Fact p.Prime := ⟨hp⟩
  exact IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p _
    fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

end PrimePow

lemma card_primesAbove_three : (primesAbove 3).card = 1 := by
  rw [primesAbove, ← Set.ncard_eq_toFinset_card _ (Algebra.QuasiFinite.finite_primesOver _)]
  exact_mod_cast IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 (CyclotomicField 3 ℚ)

lemma inertiaDegIn_three : (span {((3 : ℕ) : ℤ)}).inertiaDegIn 𝓔 = 1 :=
  IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 (CyclotomicField 3 ℚ)


/-! ### The Dirichlet side -/

/-- The value at `p ^ k` of a multiplicative function with local polynomial
`(1 - T)(1 - x T)`. -/
def localValue (x : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 1 else if k = 1 then -(1 + x) else if k = 2 then x else 0

/-- `μ ∗ χ₃μ` as an arithmetic function. -/
noncomputable def eisensteinMoebiusAF : ArithmeticFunction ℂ :=
  toArithmeticFunction (↗μ) * toArithmeticFunction (↗Smoothed.chi3 * ↗μ)

lemma coe_eisensteinMoebiusAF : ⇑eisensteinMoebiusAF = Smoothed.eisensteinMoebius := rfl

lemma isMultiplicative_eisensteinMoebiusAF : eisensteinMoebiusAF.IsMultiplicative := by
  have h1 : toArithmeticFunction (↗μ : ℕ → ℂ) =
      ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn <;> simp [toArithmeticFunction, *]
  refine ArithmeticFunction.IsMultiplicative.mul
    (h1 ▸ ArithmeticFunction.isMultiplicative_moebius.intCast) ?_
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [toArithmeticFunction], fun {m n} hm hn hmn => ?_⟩
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, mul_eq_zero, hm, hn, or_self,
    ↓reduceIte, Pi.mul_apply, Nat.cast_mul, map_mul,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, Int.cast_mul]
  ring

lemma moebius_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((μ (p ^ j) : ℤ) : ℂ) = if j = 0 then 1 else if j = 1 then -1 else 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp hj]
    split_ifs <;> simp_all

lemma eisensteinMoebiusAF_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    eisensteinMoebiusAF (p ^ k) = localValue (Smoothed.chi3 p) k := by
  have hterm : ∀ i ∈ Finset.range (k + 1), toArithmeticFunction (↗μ : ℕ → ℂ) (p ^ i) *
      toArithmeticFunction (↗Smoothed.chi3 * ↗μ) (p ^ k / p ^ i) =
      (if i = 0 then 1 else if i = 1 then -1 else 0) * (Smoothed.chi3 p ^ (k - i) *
        (if k - i = 0 then 1 else if k - i = 1 then -1 else 0)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.pow_div (by omega) hp.pos]
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, pow_ne_zero _ hp.ne_zero,
      ↓reduceIte, Pi.mul_apply, Nat.cast_pow, map_pow]
    rw [moebius_prime_pow hp, moebius_prime_pow hp]
  rw [eisensteinMoebiusAF, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => toArithmeticFunction (↗μ : ℕ → ℂ) a *
      toArithmeticFunction (↗Smoothed.chi3 * ↗μ) b),
    Nat.sum_divisors_prime_pow hp, Finset.sum_congr rfl hterm]
  match k with
  | 0 => simp [localValue]
  | 1 => simp [localValue, Finset.sum_range_succ]
  | 2 => simp [localValue, Finset.sum_range_succ]
  | k + 3 =>
    rw [Finset.sum_eq_zero fun i hi => ?_]
    · simp [localValue]
    · rw [Finset.mem_range] at hi
      by_cases h : i < 2
      · rw [ite_eq_right (by omega : ¬ k + 3 - i = 0), ite_eq_right (by omega : ¬ k + 3 - i = 1)]
        simp
      · rw [ite_eq_right (by omega : ¬ i = 0), ite_eq_right (by omega : ¬ i = 1)]
        simp

lemma chi3_natCast (p : ℕ) :
    Smoothed.chi3 p = if p % 3 = 0 then 0 else if p % 3 = 1 then 1 else -1 := by
  have h : ((p : ZMod 3)) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
  rw [h]
  have : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (p % 3)
  · simp only [Nat.cast_zero, ↓reduceIte]
    exact MulChar.map_zero _
  · simp
  · simp only [Smoothed.chi3, MulChar.ringHomComp_apply]
    rw [show quadraticChar (ZMod 3) ((2 : ℕ) : ZMod 3) = -1 by decide]
    simp

lemma normMoebius_prime_pow_eq {p : ℕ} (hp : p.Prime) (k : ℕ) :
    normMoebius (p ^ k) = localValue (Smoothed.chi3 p) k := by
  rw [normMoebius_prime_pow hp, Finset.sum_powerset_apply_card
    (fun m => if (span {(p : ℤ)}).inertiaDegIn 𝓔 * m = k then (-1 : ℂ) ^ m else 0),
    chi3_natCast]
  have hmod : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases eq_or_ne p 3 with rfl | hp3
  · rw [card_primesAbove_three, inertiaDegIn_three]
    match k with
    | 0 => simp [localValue]
    | 1 => simp [localValue]
    | k + 2 => simp [localValue]
  have hc := card_primesAbove_mul_inertiaDegIn hp hp3
  rw [inertiaDegIn_of_ne_three hp hp3]
  have h0 : p % 3 ≠ 0 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.dvd_of_mod_eq_zero h)).symm
  have hcast : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
  interval_cases h : p % 3
  · exact absurd rfl h0
  · have ho : orderOf (p : ZMod 3) = 1 := by rw [hcast]; simp
    rw [ho, mul_one] at hc
    rw [ho, hc]
    match k with
    | 0 => simp [localValue]
    | 1 => simp [localValue]; norm_num
    | 2 => simp [localValue]
    | k + 3 => simp [localValue]
  · have ho : orderOf (p : ZMod 3) = 2 := by
      rw [hcast, orderOf_eq_iff (by norm_num)]
      decide
    rw [ho] at hc
    rw [ho, show (primesAbove p).card = 1 by omega]
    match k with
    | 0 => simp [localValue]
    | 1 => simp [localValue]
    | 2 => simp [localValue]
    | k + 3 => simp [localValue, Finset.sum_range_succ]

/-- The sum of `idealMoebius` over the ideals of norm `n` is `(μ ∗ χ₃μ) n`. -/
theorem sum_idealMoebius_absNorm_eq (n : ℕ) :
    ∑ 𝔞 ∈ normFiber n, (idealMoebius 𝔞 : ℂ) = Smoothed.eisensteinMoebius n := by
  rw [← normMoebius_apply, ← coe_eisensteinMoebiusAF,
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
      isMultiplicative_normMoebius _ isMultiplicative_eisensteinMoebiusAF).2
      fun p k hp => (normMoebius_prime_pow_eq hp k).trans (eisensteinMoebiusAF_prime_pow hp k).symm]

end Masullo.QRH
