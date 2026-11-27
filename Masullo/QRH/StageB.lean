import Masullo.QRH.IdealMoebius

/-!
# From the mean square (A) to the trace identity

Let `𝓔 = 𝓞 (CyclotomicField 3 ℚ)`. `MeanSquareA` is estimate (A), a consequence of
Proposition 3.1 of OpenAI, *The Quasi-Riemann Hypothesis* (5 October 2026): for every smooth `W`
with compact support in `(0, ∞)` and every `δ > 0`,

  `∑_{𝔭 ∤ 6, N𝔭 ≤ D ^ (1/6)} ‖M_𝔭(W, D)‖² ≪_{W,δ} D ^ (2 + δ)`  for `D ≥ 2`,

over the nonzero prime ideals `𝔭`, where `M_𝔭(W, D) = moebiusSum 𝔭 W D`. It is a hypothesis
here, not a theorem.

From it, `smoothedBound_of_meanSquareA` gives `SmoothedBound eisensteinMoebius β` for every
`β > 11/12`, and `hasTrace_of_meanSquareA` gives the trace identity at every width `a > 5/12`.

Each rational prime `p ≡ 1 [MOD 3]` with `p ≤ Y = D ^ (1/6)` splits in `𝓔`; take one prime ideal
`q_p` of norm `p` above it, so (A) bounds `∑_p ‖M_{q_p}‖²`. Removing the multiples of `q_p` changes
the full sum `M = M_⊤` by `O_W(D / p)`. The prime number theorem in arithmetic progressions
(`Nat.tendsto_card_prime_modEq_mul_log_div_atTop`) gives `≫ Y / log Y` such primes, and averaging
`‖M‖² ≤ 2 ‖M_{q_p}‖² + 2 ‖M - M_{q_p}‖²` over them, with `∑ 1 / p² ≤ 1`, gives
`M ≪ D ^ (11/12 + ε)`. Adding back the ideals above `2` and `3` and grouping by norm
(`sum_idealMoebius_absNorm_eq`) turns this into the smoothed bound.
-/

open NumberField Ideal Filter
open scoped ContDiff

namespace Masullo.QRH

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The nonzero prime ideals `𝔭 ∤ 6` with `N𝔭 ≤ X`. -/
def primesUpTo (X : ℝ) : Set (Ideal 𝓔) :=
  {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ 𝔭 ∣ span {6} ∧ (absNorm 𝔭 : ℝ) ≤ X}

/-- Estimate (A): for every smooth `W` with compact support in `(0, ∞)` and every `δ > 0`,
`∑_{𝔭 ∤ 6, N𝔭 ≤ D ^ (1/6)} ‖M_𝔭(W, D)‖² ≤ C D ^ (2 + δ)` for `D ≥ 2`, with `C` depending on
`W` and `δ`. -/
def MeanSquareA : Prop :=
  ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
    ∀ δ : ℝ, 0 < δ → ∃ C, ∀ D : ℝ, 2 ≤ D →
      ∑' 𝔭 : primesUpTo (D ^ (1 / 6 : ℝ)), ‖moebiusSum 𝔭 W D‖ ^ 2 ≤ C * D ^ (2 + δ)

/-- The ideals of norm at most `x`. -/
noncomputable def idealsLe (x : ℝ) : Finset (Ideal 𝓔) :=
  (Ring.HasFiniteQuotients.finite_absNorm_le ⌊x⌋₊).toFinset

lemma mem_idealsLe {x : ℝ} (hx : 0 ≤ x) {𝔞 : Ideal 𝓔} :
    𝔞 ∈ idealsLe x ↔ (absNorm 𝔞 : ℝ) ≤ x := by
  rw [idealsLe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Nat.le_floor_iff hx]

lemma idealsLe_mono {x y : ℝ} (h : x ≤ y) : idealsLe x ⊆ idealsLe y := fun 𝔞 h𝔞 => by
  simp only [idealsLe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h𝔞 ⊢
  exact h𝔞.trans (Nat.floor_mono h)

lemma exists_card_idealsLe_le : ∃ K, ∀ x : ℝ, 1 ≤ x → ((idealsLe x).card : ℝ) ≤ K * x := by
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun s : ℝ ↦
      (Nat.card {I : Ideal 𝓔 // absNorm I ≤ s} : ℝ) / s) atTop (nhds L) :=
    ⟨_, NumberField.Ideal.tendsto_norm_le_div_atTop (CyclotomicField 3 ℚ)⟩
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 <| hL.eventually (eventually_le_nhds (lt_add_one L))
  have hcard : ∀ s : ℝ, 0 ≤ s →
      Nat.card {I : Ideal 𝓔 // (absNorm I : ℝ) ≤ s} = (idealsLe s).card := fun s hs => by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun I => (mem_idealsLe hs).symm)
  set s₁ := max s₀ 1
  refine ⟨max (L + 1) 0 + (idealsLe s₁).card, fun x hx => ?_⟩
  rcases le_or_gt s₁ x with h | h
  · have h1 := hs₀ x (le_trans (le_max_left _ _) h)
    rw [hcard x (by linarith), div_le_iff₀ (by linarith)] at h1
    nlinarith [le_max_left (L + 1) 0, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (idealsLe s₁).card)]
  · have h1 : ((idealsLe x).card : ℝ) ≤ (idealsLe s₁).card :=
      mod_cast Finset.card_le_card (idealsLe_mono h.le)
    nlinarith [le_max_right (L + 1) 0, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (idealsLe s₁).card)]

lemma norm_idealMoebius_le (𝔞 : Ideal 𝓔) : ‖(idealMoebius 𝔞 : ℂ)‖ ≤ 1 := by
  unfold idealMoebius
  split_ifs <;> simp

lemma norm_sum_le_mul_card {ι : Type*} {s t : Finset ι} {f : ι → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, f i ≠ 0 → i ∈ t ∧ ‖f i‖ ≤ B) : ‖∑ i ∈ s, f i‖ ≤ B * t.card := by
  classical
  rw [← Finset.sum_filter_ne_zero]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ B fun i hi => ?_).trans ?_
  · rw [Finset.mem_filter] at hi
    exact (hf i hi.1 hi.2).2
  · rw [nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left (mod_cast Finset.card_le_card fun i hi => ?_) hB
    rw [Finset.mem_filter] at hi
    exact (hf i hi.1 hi.2).1

variable {W : ℝ → ℂ} {R B D : ℝ}

open Classical in
lemma moebiusSum_eq_sum (hR0 : 0 ≤ R) (hR : ∀ x, W x ≠ 0 → x ≤ R) (hD : 0 < D)
    (𝔭 : Ideal 𝓔) :
    moebiusSum 𝔭 W D = ∑ 𝔞 ∈ idealsLe (R * D),
      if 𝔞 ≠ ⊥ ∧ IsCoprime 𝔞 (span {6}) ∧ IsCoprime 𝔞 𝔭 then
        (idealMoebius 𝔞 : ℂ) * W (absNorm 𝔞 / D) else 0 := by
  rw [moebiusSum]
  refine tsum_eq_sum fun 𝔞 h𝔞 => ite_eq_right_iff.2 fun _ => ?_
  refine mul_eq_zero_of_right _ (by_contra fun hW => h𝔞 ?_)
  rw [mem_idealsLe (by positivity), ← div_le_iff₀ hD]
  exact hR _ hW

lemma norm_moebiusSum_le (hR0 : 0 ≤ R) (hR : ∀ x, W x ≠ 0 → x ≤ R) (hB : ∀ x, ‖W x‖ ≤ B)
    (hD : 0 < D) (𝔭 : Ideal 𝓔) :
    ‖moebiusSum 𝔭 W D‖ ≤ B * (idealsLe (R * D)).card := by
  rw [moebiusSum_eq_sum hR0 hR hD]
  refine norm_sum_le_mul_card ((norm_nonneg _).trans (hB 0)) fun 𝔞 h𝔞 _ => ⟨h𝔞, ?_⟩
  split_ifs
  · rw [norm_mul]
    nlinarith [norm_idealMoebius_le 𝔞, hB (absNorm 𝔞 / D), norm_nonneg (W (absNorm 𝔞 / D)),
      norm_nonneg (idealMoebius 𝔞 : ℂ)]
  · simpa using (norm_nonneg _).trans (hB 0)

lemma norm_moebiusSum_sub_le (hR0 : 0 ≤ R) (hR : ∀ x, W x ≠ 0 → x ≤ R)
    (hB : ∀ x, ‖W x‖ ≤ B) (hD : 0 < D) {𝔮 : Ideal 𝓔} (h𝔮 : 𝔮.IsMaximal) (h0 : 𝔮 ≠ ⊥) :
    ‖moebiusSum ⊤ W D - moebiusSum 𝔮 W D‖ ≤ B * (idealsLe (R * D / absNorm 𝔮)).card := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hN : (0 : ℝ) < absNorm 𝔮 := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.2 h0)
  rw [moebiusSum_eq_sum hR0 hR hD, moebiusSum_eq_sum hR0 hR hD, ← Finset.sum_sub_distrib]
  refine (norm_sum_le_mul_card (t := (idealsLe (R * D / absNorm 𝔮)).image (𝔮 * ·)) hB0
    fun 𝔞 h𝔞 hne => ?_).trans (mul_le_mul_of_nonneg_left (mod_cast Finset.card_image_le) hB0)
  classical
  by_cases h2 : 𝔞 ≠ ⊥ ∧ IsCoprime 𝔞 (span {6}) ∧ IsCoprime 𝔞 𝔮
  · have h1 : 𝔞 ≠ ⊥ ∧ IsCoprime 𝔞 (span {6}) ∧ IsCoprime 𝔞 ⊤ :=
      ⟨h2.1, h2.2.1, isCoprime_iff_sup_eq.2 (sup_top_eq _)⟩
    simp [h1, h2] at hne
  by_cases h1 : 𝔞 ≠ ⊥ ∧ IsCoprime 𝔞 (span {6}) ∧ IsCoprime 𝔞 ⊤
  swap
  · simp [h1, h2] at hne
  have hc : ¬ IsCoprime 𝔞 𝔮 := fun h => h2 ⟨h1.1, h1.2.1, h⟩
  have hle : 𝔞 ≤ 𝔮 := by
    have : 𝔞 ⊔ 𝔮 = 𝔮 :=
      (h𝔮.eq_of_le (fun h => hc (isCoprime_iff_sup_eq.2 h)) le_sup_right).symm
    exact this ▸ le_sup_left
  obtain ⟨𝔠, rfl⟩ := dvd_iff_le.2 hle
  rw [mem_idealsLe (by positivity)] at h𝔞
  refine ⟨Finset.mem_image.2 ⟨𝔠, (mem_idealsLe (by positivity)).2 ?_, rfl⟩, ?_⟩
  · rw [le_div_iff₀ hN, mul_comm]
    simpa using h𝔞
  · rw [ite_eq_left h1, ite_eq_right h2, sub_zero, norm_mul]
    nlinarith [norm_idealMoebius_le (𝔮 * 𝔠), hB ((absNorm (𝔮 * 𝔠) : ℝ) / D),
      norm_nonneg (W ((absNorm (𝔮 * 𝔠) : ℝ) / D)), norm_nonneg (idealMoebius (𝔮 * 𝔠) : ℂ)]

lemma eq_top_of_natCast_mem {𝔮 : Ideal 𝓔} {m n : ℕ} (hm : (m : 𝓔) ∈ 𝔮) (hn : (n : 𝓔) ∈ 𝔮)
    (h : Nat.Coprime m n) : 𝔮 = ⊤ :=
  isUnit_iff.1 (isCoprime_self.1 (isCoprime_of_natCast_mem hm hn h))

lemma exists_prime_above {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp1 : p ≡ 1 [MOD 3]) :
    ∃ 𝔮 : Ideal 𝓔, 𝔮.IsMaximal ∧ 𝔮 ≠ ⊥ ∧ (p : 𝓔) ∈ 𝔮 ∧ ¬ 𝔮 ∣ span {6} ∧ absNorm 𝔮 = p := by
  have hp3 : p ≠ 3 := by omega
  have hcard := card_primesAbove_mul_inertiaDegIn hp hp3
  obtain ⟨𝔮, h𝔮⟩ := (Finset.card_pos (s := primesAbove p)).1
    (Nat.pos_of_ne_zero fun h => by simp [h] at hcard)
  obtain ⟨hprime, hmem⟩ := (mem_primesAbove hp).1 h𝔮
  have h0 : 𝔮 ≠ ⊥ := (prime_of_mem_primesAbove hp h𝔮).ne_zero
  have hf : orderOf (p : ZMod 3) = 1 := by
    rw [show (p : ZMod 3) = 1 by exact_mod_cast (ZMod.natCast_eq_natCast_iff p 1 3).2 hp1,
      orderOf_one]
  have hcop : Nat.Coprime p 6 := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    interval_cases p <;> revert h hp <;> norm_num
  refine ⟨𝔮, hprime.isMaximal h0, h0, hmem, fun h6 => hprime.ne_top ?_, ?_⟩
  · refine eq_top_of_natCast_mem hmem (n := 6) ?_ hcop
    exact_mod_cast dvd_iff_le.1 h6 (mem_span_singleton_self (6 : 𝓔))
  · rw [absNorm_of_mem_primesAbove hp h𝔮, inertiaDegIn_of_ne_three hp hp3, hf, pow_one]

lemma eq_of_natCast_mem {𝔮 : Ideal 𝓔} (h𝔮 : 𝔮 ≠ ⊤) {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hm : (p : 𝓔) ∈ 𝔮) (hm' : (p' : 𝓔) ∈ 𝔮) : p = p' :=
  by_contra fun h => h𝔮 (eq_top_of_natCast_mem hm hm' ((Nat.coprime_primes hp hp').2 h))

/-- For every `ε > 0`, eventually `Y ^ (1 - ε)` is at most the number of primes
`p ≡ 1 [MOD 3]` with `p ≤ Y`. -/
lemma eventually_rpow_le_card_split_primes {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in atTop,
      Y ^ (1 - ε) ≤ ((Finset.Ioc 0 ⌊Y⌋₊).filter fun p => p.Prime ∧ p ≡ 1 [MOD 3]).card := by
  have hφ : (0 : ℝ) < (Nat.totient 3 : ℝ)⁻¹ :=
    inv_pos.2 (Nat.cast_pos.2 (Nat.totient_pos.2 (by norm_num)))
  set c : ℝ := (Nat.totient 3 : ℝ)⁻¹ / 2
  have hc : 0 < c := by positivity
  have ht := Nat.tendsto_card_prime_modEq_mul_log_div_atTop (q := 3) (Nat.coprime_one_left 3)
  filter_upwards [ht.eventually_const_lt (half_lt_self hφ),
    (isLittleO_log_rpow_atTop hε).bound hc, eventually_gt_atTop 1] with Y hN hlog hY1
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  rw [lt_div_iff₀ hY0] at hN
  rw [Real.norm_of_nonneg hlogY.le, Real.norm_of_nonneg (by positivity)] at hlog
  have hsplit : Y ^ (1 - ε) * Y ^ ε = Y := by rw [← Real.rpow_add hY0]; simp
  have h1 := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hY0.le (1 - ε))
  set N := ((Finset.Ioc 0 ⌊Y⌋₊).filter fun p => p.Prime ∧ p ≡ 1 [MOD 3]).card
  have h2 : Y ^ (1 - ε) * Real.log Y < N * Real.log Y := by
    rw [← mul_assoc, mul_comm _ c, mul_assoc, hsplit] at h1
    exact h1.trans_lt hN
  exact (lt_of_mul_lt_mul_right h2 hlogY.le).le

lemma isCoprime_six_iff (𝔞 : Ideal 𝓔) :
    IsCoprime 𝔞 (span {6}) ↔ Nat.Coprime (absNorm 𝔞) 6 := by
  refine ⟨fun h => ?_, fun h => isCoprime_of_natCast_mem (absNorm_mem 𝔞) (n := 6)
    (by exact_mod_cast mem_span_singleton_self (6 : 𝓔)) h⟩
  by_contra hc
  obtain ⟨ℓ, hℓ, hℓN, hℓ6⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  obtain ⟨P, hP, hPu, hPd⟩ := exists_isMaximal_dvd_of_dvd_absNorm' hℓ 𝔞 hℓN
  have hℓP : (ℓ : 𝓔) ∈ P := by
    have : (ℓ : ℤ) ∈ P.under ℤ := hPu ▸ mem_span_singleton_self _
    simpa [under_def] using this
  have h6 : span {(6 : 𝓔)} ≤ P := by
    obtain ⟨k, hk⟩ := hℓ6
    rw [span_singleton_le_iff_mem, show (6 : 𝓔) = (ℓ : 𝓔) * k by exact_mod_cast hk]
    exact P.mul_mem_right _ hℓP
  have := isCoprime_iff_sup_eq.1 h
  exact hP.ne_top (eq_top_iff.2 (this ▸ sup_le (dvd_iff_le.1 hPd) h6))

/-- `μ ∗ χ₃μ` restricted to the integers coprime to `6`. -/
noncomputable def coprimeSixPart (n : ℕ) : ℂ :=
  if n.Coprime 6 then Smoothed.eisensteinMoebius n else 0

lemma moebiusSum_top_eq (hR0 : 0 ≤ R) (hR : ∀ x, W x ≠ 0 → x ≤ R) (hD : 0 < D) :
    moebiusSum ⊤ W D = ∑' n : ℕ, coprimeSixPart n * W (n / D) := by
  classical
  have hRD : 0 ≤ R * D := by positivity
  rw [moebiusSum_eq_sum hR0 hR hD, tsum_eq_sum (s := Finset.range (⌊R * D⌋₊ + 1)) ?_]
  swap
  · intro n hn
    refine mul_eq_zero_of_right _ (by_contra fun hW => hn ?_)
    have := hR _ hW
    rw [div_le_iff₀ hD] at this
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor this))
  rw [← Finset.sum_fiberwise_of_maps_to (g := absNorm) (t := Finset.range (⌊R * D⌋₊ + 1))]
  swap
  · intro 𝔞 h𝔞
    simp only [idealsLe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h𝔞
    exact Finset.mem_range.2 (Nat.lt_succ_of_le h𝔞)
  refine Finset.sum_congr rfl fun n hn => ?_
  have hfib : (idealsLe (R * D)).filter (fun 𝔞 => absNorm 𝔞 = n) = normFiber n := by
    ext 𝔞
    simp only [Finset.mem_filter, idealsLe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      mem_normFiber]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ Nat.lt_succ_iff.1 (Finset.mem_range.1 hn), h⟩⟩
  rw [hfib]
  have hcond : ∀ 𝔞 ∈ normFiber n,
      (𝔞 ≠ ⊥ ∧ IsCoprime 𝔞 (span {6}) ∧ IsCoprime 𝔞 ⊤) ↔ n.Coprime 6 := fun 𝔞 h𝔞 => by
    rw [mem_normFiber] at h𝔞
    rw [isCoprime_six_iff, h𝔞]
    refine ⟨fun h => h.2.1, fun h => ⟨fun h0 => ?_, h, isCoprime_iff_sup_eq.2 (sup_top_eq _)⟩⟩
    rw [h0, absNorm_bot] at h𝔞
    subst h𝔞
    norm_num at h
  rw [Finset.sum_congr rfl fun 𝔞 h𝔞 => by rw [if_congr (hcond 𝔞 h𝔞) rfl rfl]]
  unfold coprimeSixPart
  split_ifs with h
  · rw [← sum_idealMoebius_absNorm_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun 𝔞 h𝔞 => ?_
    rw [mem_normFiber.1 h𝔞]
  · simp

/-- `μ ∗ χ₃μ` on the divisors of `12`, and `0` elsewhere. -/
noncomputable def twelvePartAF : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∣ 12 then eisensteinMoebiusAF n else 0, by simp⟩

/-- `μ ∗ χ₃μ` on the integers coprime to `6`, and `0` elsewhere. -/
noncomputable def coprimeSixAF : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Coprime 6 then eisensteinMoebiusAF n else 0, by simp⟩

lemma twelvePartAF_apply (n : ℕ) :
    twelvePartAF n = if n ∣ 12 then eisensteinMoebiusAF n else 0 := rfl

lemma coprimeSixAF_apply (n : ℕ) :
    coprimeSixAF n = if n.Coprime 6 then eisensteinMoebiusAF n else 0 := rfl

lemma isMultiplicative_twelvePartAF : twelvePartAF.IsMultiplicative := by
  have h := isMultiplicative_eisensteinMoebiusAF
  refine ⟨by simp [twelvePartAF_apply, h.map_one], fun {m n} hmn => ?_⟩
  simp only [twelvePartAF_apply]
  by_cases hm : m ∣ 12
  · by_cases hn : n ∣ 12
    · rw [ite_eq_left (hmn.mul_dvd_of_dvd_of_dvd hm hn), ite_eq_left hm, ite_eq_left hn,
        h.map_mul_of_coprime hmn]
    · rw [ite_eq_right fun h => hn ((dvd_mul_left n m).trans h), ite_eq_right hn, mul_zero]
  · rw [ite_eq_right fun h => hm ((dvd_mul_right m n).trans h), ite_eq_right hm, zero_mul]

lemma isMultiplicative_coprimeSixAF : coprimeSixAF.IsMultiplicative := by
  have h := isMultiplicative_eisensteinMoebiusAF
  refine ⟨by simp [coprimeSixAF_apply, h.map_one], fun {m n} hmn => ?_⟩
  simp only [coprimeSixAF_apply]
  by_cases hm : m.Coprime 6
  · by_cases hn : n.Coprime 6
    · rw [ite_eq_left (Nat.coprime_mul_iff_left.2 ⟨hm, hn⟩), ite_eq_left hm, ite_eq_left hn,
        h.map_mul_of_coprime hmn]
    · rw [ite_eq_right fun h => hn (Nat.coprime_mul_iff_left.1 h).2, ite_eq_right hn, mul_zero]
  · rw [ite_eq_right fun h => hm (Nat.coprime_mul_iff_left.1 h).1, ite_eq_right hm, zero_mul]

lemma eisensteinMoebiusAF_eq_mul : eisensteinMoebiusAF = twelvePartAF * coprimeSixAF := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    isMultiplicative_eisensteinMoebiusAF _
    (isMultiplicative_twelvePartAF.mul isMultiplicative_coprimeSixAF)).2 fun p i hp => ?_
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => twelvePartAF a * coprimeSixAF b),
    Nat.sum_divisors_prime_pow hp]
  have h1 : twelvePartAF 1 = 1 ∧ coprimeSixAF 1 = 1 :=
    ⟨isMultiplicative_twelvePartAF.map_one, isMultiplicative_coprimeSixAF.map_one⟩
  have hvanish : ∀ j, ¬ p ^ j ∣ 12 → (p = 2 ∨ p = 3) → eisensteinMoebiusAF (p ^ j) = 0 := by
    intro j hj hp23
    rw [eisensteinMoebiusAF_prime_pow hp, localValue, chi3_natCast]
    rcases hp23 with rfl | rfl <;>
      rcases j with _ | _ | _ | j <;> first | (norm_num at hj; done) | simp
  by_cases hp23 : p = 2 ∨ p = 3
  · rw [Finset.sum_eq_single i]
    · rw [Nat.div_self (pow_pos hp.pos i), h1.2, mul_one]
      rw [twelvePartAF_apply]
      split_ifs with hd
      · rfl
      · exact hvanish i hd hp23
    · intro j hj hji
      have hlt : j < i := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hji
      rw [Nat.pow_div hlt.le hp.pos]
      refine mul_eq_zero_of_right _ ?_
      rw [coprimeSixAF_apply]
      refine ite_eq_right fun hc => ?_
      rw [Nat.coprime_pow_left_iff (by omega)] at hc
      rcases hp23 with rfl | rfl <;> norm_num at hc
    · simp
  · have hcop : p.Coprime 6 := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      interval_cases p <;> revert h hp hp23 <;> norm_num
    rw [Finset.sum_eq_single 0]
    · rw [pow_zero, Nat.div_one, h1.1, one_mul]
      rw [coprimeSixAF_apply]
      rw [ite_eq_left (Nat.Coprime.pow_left i hcop)]
    · intro j _ hj0
      refine mul_eq_zero_of_left ?_ _
      rw [twelvePartAF_apply]
      refine ite_eq_right fun hd => absurd ?_ hp23
      have hd' := (dvd_pow_self p hj0).trans hd
      have := Nat.le_of_dvd (by norm_num) hd'
      interval_cases p <;> revert hd' hp <;> norm_num
    · simp

lemma eisensteinMoebius_eq_sum (n : ℕ) :
    Smoothed.eisensteinMoebius n = ∑ e ∈ Nat.divisors 12,
      Smoothed.eisensteinMoebius e * if e ∣ n then coprimeSixPart (n / e) else 0 := by
  rw [show Smoothed.eisensteinMoebius n = (twelvePartAF * coprimeSixAF) n by
      rw [← eisensteinMoebiusAF_eq_mul]; rfl, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => twelvePartAF a * coprimeSixAF b)]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coprimeSixPart]
  have hset : (Nat.divisors n).filter (· ∣ 12) = (Nat.divisors 12).filter (· ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    tauto
  calc ∑ d ∈ n.divisors, twelvePartAF d * coprimeSixAF (n / d)
      = ∑ d ∈ n.divisors, if d ∣ 12 then eisensteinMoebiusAF d * coprimeSixPart (n / d)
          else 0 := Finset.sum_congr rfl fun d _ => by
        rw [twelvePartAF_apply]
        rw [ite_mul, zero_mul]
        rfl
    _ = _ := by
      rw [← Finset.sum_filter, hset, Finset.sum_filter]
      simp only [mul_ite, mul_zero, coe_eisensteinMoebiusAF]

lemma exists_support_le {W : ℝ → ℂ} (hWc : HasCompactSupport W) :
    ∃ R, 1 ≤ R ∧ ∀ x, W x ≠ 0 → x ≤ R := by
  obtain ⟨R, hR⟩ := hWc.isCompact.bddAbove
  exact ⟨max R 1, le_max_right _ _,
    fun x hx => (hR (subset_tsupport W hx)).trans (le_max_left _ _)⟩

lemma comp_mul_left {W : ℝ → ℂ} (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hW0 : tsupport W ⊆ Set.Ioi 0) {e : ℝ} (he : 0 < e) :
    ContDiff ℝ ∞ (fun x => W (e * x)) ∧ HasCompactSupport (fun x => W (e * x)) ∧
      tsupport (fun x => W (e * x)) ⊆ Set.Ioi 0 := by
  have hc : Continuous (fun x : ℝ => e * x) := continuous_const.mul continuous_id
  have hsub : tsupport (fun x => W (e * x)) ⊆ (fun x => e * x) ⁻¹' tsupport W :=
    closure_minimal (fun x hx => subset_tsupport W hx) ((isClosed_tsupport W).preimage hc)
  refine ⟨hW.comp (contDiff_const.mul contDiff_id), ?_, fun x hx => ?_⟩
  · refine HasCompactSupport.intro (hWc.isCompact.image
      (continuous_const.mul continuous_id : Continuous fun y : ℝ => e⁻¹ * y)) fun x hx => ?_
    refine by_contra fun hne => hx ⟨e * x, subset_tsupport W hne, ?_⟩
    exact inv_mul_cancel_left₀ he.ne' x
  · exact pos_of_mul_pos_right (hW0 (hsub hx)) he.le

lemma smoothedSum_eq (hR0 : 0 ≤ R) (hR : ∀ x, W x ≠ 0 → x ≤ R) (hD : 0 < D) :
    Smoothed.smoothedSum Smoothed.eisensteinMoebius W D = ∑ e ∈ Nat.divisors 12,
      Smoothed.eisensteinMoebius e * moebiusSum ⊤ (fun x => W (e * x)) D := by
  have hW0 : ∀ n : ℕ, ⌊R * D⌋₊ < n → W (n / D) = 0 := fun n hn => by_contra fun hW => by
    have := hR _ hW
    rw [div_le_iff₀ hD] at this
    exact absurd (Nat.le_floor this) (not_le.2 hn)
  have hsum : ∀ n : ℕ, Smoothed.eisensteinMoebius n * W (n / D) = ∑ e ∈ Nat.divisors 12,
      Smoothed.eisensteinMoebius e *
        ((if e ∣ n then coprimeSixPart (n / e) else 0) * W (n / D)) := fun n => by
    rw [eisensteinMoebius_eq_sum n, Finset.sum_mul]
    simp only [mul_assoc]
  rw [Smoothed.smoothedSum, tsum_congr hsum, Summable.tsum_finsetSum fun e _ => ?_]
  · refine Finset.sum_congr rfl fun e he => ?_
    have he0 := Nat.pos_of_mem_divisors he
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    rw [tsum_mul_left, moebiusSum_top_eq hR0 (fun x hx => ?_) hD]
    · congr 1
      refine ((mul_right_injective₀ he0.ne').tsum_eq
        (f := fun n : ℕ => (if e ∣ n then coprimeSixPart (n / e) else 0) * W (n / D))
        ?_).symm.trans (tsum_congr fun m => ?_)
      · intro n hn
        by_cases hd : e ∣ n
        · exact ⟨n / e, Nat.mul_div_cancel' hd⟩
        · exact absurd (by simp [hd]) hn
      · simp [Nat.mul_div_cancel_left m he0, mul_div_assoc]
    · have := hR _ hx
      rcases le_or_gt x 0 with h | h
      · linarith
      · nlinarith
  · refine summable_of_ne_finset_zero (s := Finset.range (⌊R * D⌋₊ + 1)) fun n hn => ?_
    rw [hW0 n (by simpa using hn), mul_zero, mul_zero]

/-- (A) bounds the full sum `M_⊤(W, D)` by `C * D ^ β`, with `C` depending on `W` and `β`, for every
`β > 11/12`. -/
theorem norm_moebiusSum_top_le (h : MeanSquareA) {β : ℝ} (hβ : 11 / 12 < β) {W : ℝ → ℂ}
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (hW0 : tsupport W ⊆ Set.Ioi 0) :
    ∃ C, ∀ D : ℝ, 1 ≤ D → ‖moebiusSum ⊤ W D‖ ≤ C * D ^ β := by
  obtain ⟨B, hB⟩ := hWc.exists_bound_of_continuous hW.continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨R, hR1, hR⟩ := exists_support_le hWc
  obtain ⟨K, hK⟩ := exists_card_idealsLe_le
  have hK0 : 0 ≤ K := by
    have := hK 1 le_rfl
    have := (Nat.cast_nonneg (idealsLe 1).card : (0 : ℝ) ≤ _)
    linarith
  set η := 2 * β - 11 / 6 with hη
  have hη0 : 0 < η := by linarith
  obtain ⟨CA, hCA⟩ := h W hW hWc hW0 (η / 2) (by positivity)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1
    (eventually_rpow_le_card_split_primes (ε := 3 * η) (by positivity))
  set D₀ := max Y₀ 5 ^ 6
  set C₃ := 2 * |CA| + 2 * (B * K * R) ^ 2 with hC₃def
  have hBKR : 0 ≤ B * K * R := mul_nonneg (mul_nonneg hB0 hK0) (by linarith)
  have hC₃ : 0 ≤ C₃ := by positivity
  have hD₀ : 0 ≤ D₀ := by positivity
  refine ⟨B * K * R * D₀ + (C₃ + 1), fun D hD => ?_⟩
  have hD0 : 0 < D := by linarith
  have hDβ : 1 ≤ D ^ β := Real.one_le_rpow hD (by linarith)
  rcases lt_or_ge D D₀ with hsmall | hlarge
  · have h1 : ‖moebiusSum ⊤ W D‖ ≤ B * K * R * D₀ :=
      calc _ ≤ B * (idealsLe (R * D)).card := norm_moebiusSum_le (by linarith) hR hB hD0 ⊤
        _ ≤ B * (K * (R * D)) := mul_le_mul_of_nonneg_left (hK _ (by nlinarith)) hB0
        _ ≤ B * K * R * D₀ := by nlinarith
    nlinarith [mul_nonneg hBKR hD₀]
  set Y := D ^ ((1 : ℝ) / 6) with hYdef
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hD0.le _
  have hY6 : Y ^ 6 = D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    norm_num
  have hYM : max Y₀ 5 ≤ Y := by
    by_contra hlt
    have := pow_lt_pow_left₀ (not_le.1 hlt) hY0 (by norm_num : (6 : ℕ) ≠ 0)
    linarith
  have hY5 : 5 ≤ Y := (le_max_right _ _).trans hYM
  have hYD : Y ≤ D := hY6 ▸ le_self_pow₀ (by linarith) (by norm_num)
  have hD2 : 2 ≤ D := by linarith
  set P := (Finset.Ioc 0 ⌊Y⌋₊).filter fun p => p.Prime ∧ p ≡ 1 [MOD 3]
  have hmemP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p ∧ p ≡ 1 [MOD 3] ∧ (p : ℝ) ≤ Y := fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_Ioc, P] at hp
    refine ⟨hp.2.1, ?_, hp.2.2, (Nat.cast_le.2 hp.1.2).trans (Nat.floor_le hY0)⟩
    have h2 := hp.2.1.two_le
    have h1 : p % 3 = 1 := hp.2.2
    by_contra h5
    interval_cases p <;> first | omega | norm_num at hp
  have hJ : Y ^ (1 - 3 * η) ≤ P.card := hY₀ Y ((le_max_left _ _).trans hYM)
  choose! q hq using fun p hp =>
    exists_prime_above (hmemP p hp).1 (hmemP p hp).2.1 (hmemP p hp).2.2.1
  have hNY : ∀ p ∈ P, (absNorm (q p) : ℝ) ≤ Y := fun p hp => by
    rw [(hq p hp).2.2.2.2]
    exact (hmemP p hp).2.2.2
  set X := B * K * R * D
  have hdiff : ∀ p ∈ P, ‖moebiusSum ⊤ W D - moebiusSum (q p) W D‖ ≤ X / p := by
    intro p hp
    obtain ⟨hmax, h0, -, -, hpN⟩ := hq p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hmemP p hp).1.pos
    have hpN' : (p : ℝ) ≤ absNorm (q p) := by exact_mod_cast hpN.ge
    have hx : 1 ≤ R * D / absNorm (q p) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [hNY p hp]
    have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ R * D) hp0 hpN'
    calc _ ≤ B * (idealsLe (R * D / absNorm (q p))).card :=
          norm_moebiusSum_sub_le (by linarith) hR hB hD0 hmax h0
      _ ≤ B * (K * (R * D / absNorm (q p))) := mul_le_mul_of_nonneg_left (hK _ hx) hB0
      _ ≤ B * (K * (R * D / p)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiv hK0) hB0
      _ = X / p := by ring
  have hsq : ∀ p ∈ P, ‖moebiusSum ⊤ W D‖ ^ 2 ≤
      2 * ‖moebiusSum (q p) W D‖ ^ 2 + 2 * X ^ 2 * ((p : ℝ) ^ 2)⁻¹ := by
    intro p hp
    have h1 : ‖moebiusSum ⊤ W D‖ ≤ ‖moebiusSum (q p) W D‖ + X / p := by
      have := norm_add_le (moebiusSum (q p) W D) (moebiusSum ⊤ W D - moebiusSum (q p) W D)
      rw [add_sub_cancel] at this
      linarith [hdiff p hp]
    have hX : X ^ 2 * ((p : ℝ) ^ 2)⁻¹ = (X / p) ^ 2 := by rw [div_pow, div_eq_mul_inv]
    rw [mul_assoc, hX]
    nlinarith [norm_nonneg (moebiusSum ⊤ W D), sq_nonneg (‖moebiusSum (q p) W D‖ - X / p)]
  have hinj : Set.InjOn q P := fun p hp p' hp' hpp' => by
    have h1 := (hq p hp).2.2.1
    have h2 := (hq p' hp').2.2.1
    rw [hpp'] at h1
    exact eq_of_natCast_mem (hq p' hp').1.ne_top (hmemP p hp).1 (hmemP p' hp').1 h1 h2
  set g : Ideal 𝓔 → ℝ := fun 𝔭 => ‖moebiusSum 𝔭 W D‖ ^ 2
  have hsumm : Summable ((primesUpTo (D ^ (1 / 6 : ℝ))).indicator g) := by
    refine summable_of_ne_finset_zero (s := idealsLe (D ^ (1 / 6 : ℝ))) fun 𝔭 h𝔭 => ?_
    refine Set.indicator_of_notMem (fun hmem => h𝔭 ?_) _
    exact (mem_idealsLe (by positivity)).2 hmem.2.2.2
  have hA : ∑ p ∈ P, g (q p) ≤ CA * D ^ (2 + η / 2) := by
    calc ∑ p ∈ P, g (q p) = ∑ 𝔭 ∈ P.image q, g 𝔭 := (Finset.sum_image hinj).symm
      _ = ∑ 𝔭 ∈ P.image q, (primesUpTo (D ^ (1 / 6 : ℝ))).indicator g 𝔭 := by
          refine Finset.sum_congr rfl fun 𝔭 h𝔭 => (Set.indicator_of_mem ?_ g).symm
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h𝔭
          obtain ⟨hmax, h0, -, h6, -⟩ := hq p hp
          exact ⟨hmax.isPrime, h0, h6, hNY p hp⟩
      _ ≤ ∑' 𝔭, (primesUpTo (D ^ (1 / 6 : ℝ))).indicator g 𝔭 :=
          hsumm.sum_le_tsum _ fun 𝔭 _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
      _ = ∑' 𝔭 : primesUpTo (D ^ (1 / 6 : ℝ)), g 𝔭 := (tsum_subtype _ g).symm
      _ ≤ CA * D ^ (2 + η / 2) := hCA D hD2
  have hrec : ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Ioo 4 (⌊Y⌋₊ + 1))
      (fun p hp => ?_) fun _ _ _ => by positivity).trans
      ((sum_Ioo_inv_sq_le 4 _).trans (by norm_num))
    have h5 := (hmemP p hp).2.1
    simp only [Finset.mem_filter, Finset.mem_Ioc, P] at hp
    simp only [Finset.mem_Ioo]
    omega
  have hsum := Finset.card_nsmul_le_sum P _ _ hsq
  rw [nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hD2δ : D ^ (2 : ℝ) ≤ D ^ (2 + η / 2) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hXsq : X ^ 2 = (B * K * R) ^ 2 * D ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    ring
  have hJM : (P.card : ℝ) * ‖moebiusSum ⊤ W D‖ ^ 2 ≤ C₃ * D ^ (2 + η / 2) := by
    have hpos : 0 ≤ D ^ (2 + η / 2) := by positivity
    have hA' : ∑ i ∈ P, ‖moebiusSum (q i) W D‖ ^ 2 ≤ CA * D ^ (2 + η / 2) := hA
    have h3 : 2 * X ^ 2 * ∑ i ∈ P, ((i : ℝ) ^ 2)⁻¹ ≤ 2 * X ^ 2 :=
      by nlinarith [sq_nonneg X]
    have h4 : CA * D ^ (2 + η / 2) ≤ |CA| * D ^ (2 + η / 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self CA) hpos
    have h5 : X ^ 2 ≤ (B * K * R) ^ 2 * D ^ (2 + η / 2) :=
      hXsq ▸ mul_le_mul_of_nonneg_left hD2δ (sq_nonneg _)
    rw [hC₃def]
    linarith
  have hYε : Y ^ (1 - 3 * η) = D ^ ((1 - 3 * η) / 6) := by
    rw [hYdef, ← Real.rpow_mul hD0.le]
    ring_nf
  have hsplit : D ^ (2 + η / 2) = (D ^ β) ^ 2 * D ^ ((1 - 3 * η) / 6) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le, ← Real.rpow_add hD0]
    congr 1
    rw [hη]
    push_cast
    ring
  have hMsq : ‖moebiusSum ⊤ W D‖ ^ 2 ≤ C₃ * (D ^ β) ^ 2 := by
    have hpos : 0 < D ^ ((1 - 3 * η) / 6) := Real.rpow_pos_of_pos hD0 _
    have := (mul_le_mul_of_nonneg_right hJ (sq_nonneg ‖moebiusSum ⊤ W D‖)).trans hJM
    rw [hYε, hsplit] at this
    refine le_of_mul_le_mul_left ?_ hpos
    linarith
  have hfin : ‖moebiusSum ⊤ W D‖ ≤ (C₃ + 1) * D ^ β := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow]
    nlinarith [sq_nonneg (D ^ β)]
  have := mul_nonneg (mul_nonneg hBKR hD₀) (by linarith : 0 ≤ D ^ β)
  rw [add_mul]
  linarith

/-- (A) gives the smoothed bound for `μ ∗ χ₃μ` at every exponent `β > 11/12`. -/
theorem smoothedBound_of_meanSquareA (h : MeanSquareA) {β : ℝ} (hβ : 11 / 12 < β) :
    Smoothed.SmoothedBound Smoothed.eisensteinMoebius β := by
  intro W hW hWc hW0
  have hex : ∀ e : ℕ, ∃ C, 0 < e → ∀ D : ℝ, 1 ≤ D →
      ‖moebiusSum ⊤ (fun x => W (e * x)) D‖ ≤ C * D ^ β := by
    intro e
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    obtain ⟨h1, h2, h3⟩ := comp_mul_left hW hWc hW0 (Nat.cast_pos.2 he)
    obtain ⟨C, hC⟩ := norm_moebiusSum_top_le h hβ h1 h2 h3
    exact ⟨C, fun _ => hC⟩
  choose C hC using hex
  obtain ⟨R, hR1, hR⟩ := exists_support_le hWc
  refine ⟨∑ e ∈ Nat.divisors 12, ‖Smoothed.eisensteinMoebius e‖ * C e, fun D hD => ?_⟩
  rw [smoothedSum_eq (by linarith) hR (by linarith), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC e (Nat.pos_of_mem_divisors he) D hD) (norm_nonneg _)

/-- (A) gives the trace identity at every width `a > 5/12`. -/
theorem hasTrace_of_meanSquareA (h : MeanSquareA) {a : ℝ} (ha : 5 / 12 < a)
    (φ : TestFunction) :
    Trace.HasTrace (Trace.induced (by linarith : (0 : ℝ) < a) φ) φ.efFunctional :=
  Smoothed.hasTrace_of_smoothedBound (β := (a + 1 / 2 + 11 / 12) / 2) (by linarith) _
    (by linarith) (smoothedBound_of_meanSquareA h (by linarith)) φ

end Masullo.QRH
