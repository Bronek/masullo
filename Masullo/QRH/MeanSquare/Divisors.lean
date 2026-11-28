import Masullo.QRH.MeanSquare.Rows

/-! # Divisors of Eisenstein ideals

The divisor bound `τ(n) ≤ C_s (Nn)^s` and the multiplicity bounds for the
reparametrisations `y = h f²` and `n = a b` used by the transfer estimate.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The ideal divisors of `n`. For `n = ⊥` this is the finite set of ideals of norm zero
that divide `⊥`, which is not used. -/
def idealDivisors (n : Ideal 𝓔) : Finset (Ideal 𝓔) := by
  classical
  exact (idealsLe (absNorm n)).filter (· ∣ n)

lemma mem_idealDivisors {n d : Ideal 𝓔} (hn : n ≠ ⊥) : d ∈ idealDivisors n ↔ d ∣ n := by
  classical
  unfold idealDivisors
  rw [Finset.mem_filter, mem_idealsLe (Nat.cast_nonneg _)]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hn))
    (map_dvd absNorm h)

private lemma ne_bot_of_dvd {n d : Ideal 𝓔} (hn : n ≠ ⊥) (h : d ∣ n) : d ≠ ⊥ := by
  rintro rfl
  rw [← Ideal.zero_eq_bot] at h hn
  exact hn (zero_dvd_iff.mp h)

private lemma eq_of_count_eq {n d₁ d₂ : Ideal 𝓔} (hn : n ≠ ⊥) (h₁ : d₁ ∣ n) (h₂ : d₂ ∣ n)
    (h : ∀ P ∈ (normalizedFactors n).toFinset,
      (normalizedFactors d₁).count P = (normalizedFactors d₂).count P) : d₁ = d₂ := by
  classical
  have hd₁ : d₁ ≠ ⊥ := ne_bot_of_dvd hn h₁
  have hd₂ : d₂ ≠ ⊥ := ne_bot_of_dvd hn h₂
  have hle₁ := (dvd_iff_normalizedFactors_le_normalizedFactors hd₁ hn).mp h₁
  have hle₂ := (dvd_iff_normalizedFactors_le_normalizedFactors hd₂ hn).mp h₂
  have hf : normalizedFactors d₁ = normalizedFactors d₂ := by
    ext P
    by_cases hP : P ∈ (normalizedFactors n).toFinset
    · exact h P hP
    · have h0 : (normalizedFactors n).count P = 0 :=
        Multiset.count_eq_zero.mpr fun h => hP (Multiset.mem_toFinset.mpr h)
      rw [Nat.eq_zero_of_le_zero ((Multiset.count_le_of_le P hle₁).trans h0.le),
        Nat.eq_zero_of_le_zero ((Multiset.count_le_of_le P hle₂).trans h0.le)]
  rw [← prod_normalizedFactors_eq_self hd₁, ← prod_normalizedFactors_eq_self hd₂, hf]

/-- The divisor count is the product of `e_P + 1` over the prime powers `P^{e_P} ∥ n`. -/
lemma card_idealDivisors_le_prod {n : Ideal 𝓔} (hn : n ≠ ⊥) : (idealDivisors n).card ≤
    ∏ P ∈ (normalizedFactors n).toFinset, ((normalizedFactors n).count P + 1) := by
  classical
  set S := (normalizedFactors n).toFinset
  have hmap : ∀ d ∈ idealDivisors n, (fun P (_ : P ∈ S) => (normalizedFactors d).count P) ∈
      S.pi fun P => Finset.range ((normalizedFactors n).count P + 1) := by
    intro d hd
    have hdn := (mem_idealDivisors hn).mp hd
    have hd0 : d ≠ ⊥ := ne_bot_of_dvd hn hdn
    have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn).mp hdn
    refine Finset.mem_pi.mpr fun P _ => Finset.mem_range.mpr ?_
    exact Nat.lt_succ_of_le (Multiset.count_le_of_le P hle)
  calc (idealDivisors n).card
      ≤ (S.pi fun P => Finset.range ((normalizedFactors n).count P + 1)).card :=
        Finset.card_le_card_of_injOn _ (fun d hd => hmap d hd) (by
          intro d₁ h₁ d₂ h₂ h
          refine eq_of_count_eq hn ((mem_idealDivisors hn).mp h₁)
            ((mem_idealDivisors hn).mp h₂) fun P hP => ?_
          exact congrFun (congrFun h P) hP)
    _ = _ := by rw [Finset.card_pi]; simp

private lemma one_add_le_mul_pow {b a : ℝ} (hb : 1 < b) (hab : b ≤ a) (e : ℕ) :
    (e + 1 : ℝ) ≤ max 1 (1 / (b - 1)) * a ^ e := by
  have hbern := one_add_mul_le_pow (show -2 ≤ a - 1 by linarith) e
  rw [add_sub_cancel] at hbern
  rcases le_total 1 (b - 1) with h | h
  · have : (e + 1 : ℝ) ≤ a ^ e := by nlinarith [(Nat.cast_nonneg e : (0 : ℝ) ≤ e)]
    exact this.trans (le_mul_of_one_le_left (pow_nonneg (by linarith) e) (le_max_left _ _))
  · have hb1 : 0 < b - 1 := by linarith
    calc (e + 1 : ℝ) = 1 / (b - 1) * ((b - 1) * (e + 1)) := by field_simp
      _ ≤ 1 / (b - 1) * a ^ e := by
          gcongr
          nlinarith [(Nat.cast_nonneg e : (0 : ℝ) ≤ e)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) e)

/-- The ideal divisor bound `τ(n) ≤ C_s (Nn)^s`. -/
theorem card_idealDivisors_le {s : ℝ} (hs : 0 < s) : ∃ C ≥ (0 : ℝ), ∀ n : Ideal 𝓔, n ≠ ⊥ →
    ((idealDivisors n).card : ℝ) ≤ C * (absNorm n : ℝ) ^ s := by
  classical
  let T := idealsLe ((2 : ℝ) ^ (1 / s))
  set b : ℝ := (2 : ℝ) ^ s
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hs
  set K : ℝ := max 1 (1 / (b - 1))
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨K ^ T.card, by positivity, fun n hn => ?_⟩
  set S := (normalizedFactors n).toFinset
  set e : Ideal 𝓔 → ℕ := fun P => (normalizedFactors n).count P
  have hprime : ∀ P ∈ S, Prime P := fun P hP =>
    prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hnorm2 : ∀ P ∈ S, (2 : ℝ) ≤ absNorm P := by
    intro P hP
    have hP := hprime P hP
    have h0 : absNorm P ≠ 0 := absNorm_eq_zero_iff.not.mpr hP.ne_zero
    have h1 : absNorm P ≠ 1 :=
      absNorm_eq_one_iff.not.mpr (by rw [← Ideal.one_eq_top]; exact hP.ne_one)
    have h2 : 2 ≤ absNorm P := by omega
    exact_mod_cast h2
  set c : Ideal 𝓔 → ℝ := fun P => if P ∈ T then K else 1
  have hfac : ∀ P ∈ S, ((e P + 1 : ℕ) : ℝ) ≤ c P * ((absNorm P : ℝ) ^ s) ^ e P := by
    intro P hP
    have hbP : b ≤ (absNorm P : ℝ) ^ s :=
      Real.rpow_le_rpow (by norm_num) (hnorm2 P hP) hs.le
    push_cast
    by_cases hT : P ∈ T
    · simp only [c, hT, ↓reduceIte]
      exact one_add_le_mul_pow hb hbP _
    · simp only [c, hT, ↓reduceIte, one_mul]
      have h2 : (2 : ℝ) ≤ (absNorm P : ℝ) ^ s := by
        have h : (2 : ℝ) ^ (1 / s) < absNorm P := by
          by_contra h
          exact hT ((mem_idealsLe (by positivity)).mpr (not_lt.mp h))
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / s)) ^ s := by
              rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hs.ne', Real.rpow_one]
          _ ≤ _ := Real.rpow_le_rpow (by positivity) h.le hs.le
      calc (e P + 1 : ℝ) ≤ 2 ^ e P := by
            exact_mod_cast Nat.lt_two_pow_self
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 _
  have hc : ∏ P ∈ S, c P ≤ K ^ T.card := by
    calc ∏ P ∈ S, c P = ∏ P ∈ S.filter (· ∈ T), K := by
          rw [Finset.prod_filter]
      _ = K ^ (S.filter (· ∈ T)).card := Finset.prod_const _
      _ ≤ K ^ T.card := pow_le_pow_right₀ hK (Finset.card_le_card fun P hP =>
          (Finset.mem_filter.mp hP).2)
  have hN : (absNorm n : ℝ) = ∏ P ∈ S, (absNorm P : ℝ) ^ e P := by
    conv_lhs => rw [← prod_normalizedFactors_eq_self hn]
    rw [map_multiset_prod, Nat.cast_multiset_prod, Multiset.map_map,
      Finset.prod_multiset_map_count]
    rfl
  calc ((idealDivisors n).card : ℝ)
      ≤ ∏ P ∈ S, ((e P + 1 : ℕ) : ℝ) := by exact_mod_cast card_idealDivisors_le_prod hn
    _ ≤ ∏ P ∈ S, (c P * ((absNorm P : ℝ) ^ s) ^ e P) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) hfac
    _ = (∏ P ∈ S, c P) * ∏ P ∈ S, ((absNorm P : ℝ) ^ e P) ^ s := by
        rw [Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun P _ => ?_
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_mul (by positivity), mul_comm]
    _ ≤ K ^ T.card * (absNorm n : ℝ) ^ s := by
        rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), ← hN]
        gcongr

/-- At most `τ(n)` pairs `(a, b)` in a finite set satisfy `a b = n`. -/
lemma card_filter_mul_eq_le {n : Ideal 𝓔} (hn : n ≠ ⊥) (S : Finset (Ideal 𝓔 × Ideal 𝓔)) :
    (S.filter fun p => p.1 * p.2 = n).card ≤ (idealDivisors n).card := by
  classical
  refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) ?_
  · exact (mem_idealDivisors hn).mpr ⟨p.1, by rw [mul_comm]; exact (Finset.mem_filter.mp hp).2.symm⟩
  · intro p hp q hq h
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have h0 : p.2 ≠ ⊥ := fun h0 => hn (by rw [← hp', h0, mul_bot])
    have h1 : p.1 = q.1 := mul_right_cancel₀ h0 (by rw [hp', h, hq'])
    exact Prod.ext h1 h

/-- At most `τ(n)` pairs `(a, f)` in a finite set satisfy `a f² = n`. -/
lemma card_filter_mul_sq_eq_le {n : Ideal 𝓔} (hn : n ≠ ⊥) (S : Finset (Ideal 𝓔 × Ideal 𝓔)) :
    (S.filter fun p => p.1 * p.2 ^ 2 = n).card ≤ (idealDivisors n).card := by
  classical
  refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) ?_
  · refine (mem_idealDivisors hn).mpr ⟨p.1 * p.2, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq h
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have h0 : p.2 ^ 2 ≠ ⊥ := fun h0 => hn (by rw [← hp', h0, mul_bot])
    have h1 : p.1 = q.1 := mul_right_cancel₀ h0 (by rw [hp', h, hq'])
    exact Prod.ext h1 h

open Classical in
/-- At most `τ((y))` pairs `(h, f)` of an element and an ideal satisfy `h g_f² = y`
for any choice `g` of generators. -/
lemma card_filter_elem_mul_sq_eq_le {y : 𝓔} (hy : y ≠ 0) (g : Ideal 𝓔 → 𝓔)
    (hg : ∀ f, span {g f} = f) (S : Finset (𝓔 × Ideal 𝓔)) :
    (S.filter fun p : 𝓔 × Ideal 𝓔 => p.1 * g p.2 ^ 2 = y).card ≤
      (idealDivisors (span {y})).card := by
  classical
  have hspan : span {y} ≠ ⊥ := by simpa using hy
  refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) ?_
  · refine (mem_idealDivisors hspan).mpr ?_
    have h : span {g p.2} ∣ span {y} := span_singleton_dvd_span_singleton_iff_dvd.mpr
      ⟨p.1 * g p.2, by rw [← (Finset.mem_filter.mp hp).2]; ring⟩
    rwa [hg] at h
  · intro p hp q hq h
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have h0 : g p.2 ^ 2 ≠ 0 := fun h0 => hy (by rw [← hp', h0, mul_zero])
    have h1 : p.1 = q.1 := mul_right_cancel₀ h0 (by rw [hp', h, hq'])
    exact Prod.ext h1 h

end Masullo.QRH.MeanSquare
