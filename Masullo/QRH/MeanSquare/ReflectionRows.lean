import Masullo.QRH.MeanSquare.Primary
import Masullo.QRH.MeanSquare.Residue

/-! # Squarefree extraction from the rows of the completed estimate -/

noncomputable section

open NumberField Ideal Finset

namespace Masullo.QRH.MeanSquare.ReflectionRows

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- Allow an arbitrary element in the fourth-power twist. The conductor ideal
in the original completed sum is the unit ideal here. -/
def completedAtElement (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k g : 𝓔) : ℂ :=
  completedSum ξ W X (k * g ^ 4) 1

private lemma completed_congr (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ)
    {k l : 𝓔} {f g : Ideal 𝓔} (h : ∀ n, AwayFromSix n → twist ξ k f n = twist ξ l g n) :
    completedSum ξ W X k f = completedSum ξ W X l g := by
  have hc (L : ℝ) : columnSum ξ W L k f = columnSum ξ W L l g := by
    exact finsum_congr fun n => by simp only [h n n.2.1]
  exact finsum_congr fun b => by simp only [h b b.2, hc]

theorem completedSum_eq_atElement (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔) (f : Ideal 𝓔) :
    completedSum ξ W X k f = completedAtElement ξ W X k (generator f) := by
  apply completed_congr
  intro n hn
  simp only [twist, ite_eq_left hn, generator_one, one_pow, mul_one]

private lemma sextic_eight {n : Ideal 𝓔} (hn : AwayFromSix n) (v : 𝓔) :
    sextic n v ^ 8 = sextic n v ^ 2 := by
  classical
  have h := congrArg eisEmbedding (powerResidueSymbol_six_pow_six hn.1 hn.2 v)
  by_cases hv : IsCoprime n (span {v})
  · simp only [ite_eq_left hv, map_pow, map_one] at h
    rw [show 8 = 6 + 2 by decide, pow_add, show sextic n v ^ 6 = 1 from h, one_mul]
  · simp only [ite_eq_right hv, map_pow, map_zero] at h
    have hz : sextic n v = 0 := eq_zero_of_pow_eq_zero (n := 6) h
    simp [hz]

/-- Moving a square from the row to the fourth-power twist preserves every
sextic symbol, including the zeros at common prime divisors. -/
theorem completedAtElement_shift_square (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k v g : 𝓔) :
    completedAtElement ξ W X (k * v ^ 2) g = completedAtElement ξ W X k (g * v ^ 2) := by
  apply completed_congr
  intro n hn
  simp only [twist, ite_eq_left hn, generator_one, one_pow, mul_one]
  rw [← sexticChar_apply_mk hn, ← sexticChar_apply_mk hn]
  simp only [map_mul, map_pow, sexticChar_apply_mk, mul_pow, ← pow_mul]
  rw [show 2 * 4 = 8 by decide, sextic_eight hn]
  ring

/-- Every squarefree ideal of norm at most `H`, including the primes above two and three. -/
def squarefreeRows (H : ℝ) : Finset (Ideal 𝓔) := open Classical in
  (idealsLe H).filter Squarefree

/-- The estimate before extracting the square part of an arbitrary row. The fixed
unit and the auxiliary element are uniform, and the auxiliary element can be imprimitive. -/
def SquarefreeCompletedEstimate : Prop :=
  ∀ C₀ ≥ (1 : ℝ), ∀ ε > (0 : ℝ), ∃ j : ℕ, ∀ I : TestInterval, ∃ C ≥ (0 : ℝ),
    ∀ (D H X : ℝ) (u : 𝓔ˣ) (g : 𝓔) (ξ : RayCharacter) (W : ℝ → ℂ),
      2 ≤ D → 1 ≤ H → H ≤ D ^ C₀ → 1 ≤ X → X ≤ D ^ C₀ →
      g ≠ 0 → (elementNorm g : ℝ) ≤ D ^ C₀ → UnitTest I j W →
      ∑ s ∈ squarefreeRows H, ‖completedAtElement ξ W X ((u : 𝓔) * generator s) g‖ ^ 2 ≤
        C * D ^ ε * (H + H ^ 2 * elementNorm g / X)

private def squareDivisors (K : ℝ) : Finset (Ideal 𝓔) := open Classical in
  (idealsLe K).filter (fun v => v ≠ 0 ∧ (absNorm v : ℝ) ^ 2 ≤ K)

private instance unitFintype : Fintype 𝓔ˣ := by
  classical
  have hmem (u : 𝓔ˣ) : (u : 𝓔) ∈ elementRows 1 := by
    apply (mem_elementRows (by norm_num)).mpr
    exact ⟨u.ne_zero, by simp [elementNorm, span_singleton_eq_top.mpr u.isUnit]⟩
  exact Fintype.ofInjective (fun u : 𝓔ˣ => (⟨(u : 𝓔), hmem u⟩ : elementRows 1))
    (fun _ _ h => Units.ext (congrArg Subtype.val h))

private lemma row_cover {K : ℝ} (hK : 1 ≤ K) {k : 𝓔} (hk : k ∈ elementRows K) :
    ∃ v ∈ squareDivisors K, ∃ u : 𝓔ˣ, ∃ s ∈ squarefreeRows (K / (absNorm v : ℝ) ^ 2),
      (u : 𝓔) * generator s * generator v ^ 2 = k := by
  classical
  obtain ⟨hk₀, hNk⟩ := (mem_elementRows (by linarith)).mp hk
  obtain ⟨v, s, he, hs⟩ := exists_sq_mul_squarefree (span {k} : Ideal 𝓔)
  have hv₀ : v ≠ 0 := by
    rintro rfl
    apply hk₀
    apply span_singleton_eq_bot.mp
    simpa using he.symm
  have hNv : 1 ≤ (absNorm v : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hv₀)
  have hNs : 1 ≤ (absNorm s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hs.ne_zero)
  have hprod : (absNorm v : ℝ) ^ 2 * absNorm s ≤ K := by
    simpa only [elementNorm, ← he, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using hNk
  have hcut : (absNorm v : ℝ) ^ 2 ≤ K :=
    (le_mul_of_one_le_right (sq_nonneg _) hNs).trans hprod
  have hvK : (absNorm v : ℝ) ≤ K := by nlinarith
  have hspan : span {generator s * generator v ^ 2} = span {k} := by
    rw [← span_singleton_mul_span_singleton, ← span_singleton_pow, span_generator, span_generator,
      mul_comm, he]
  obtain ⟨u, hu⟩ := span_singleton_eq_span_singleton.mp hspan
  refine ⟨v, mem_filter.mpr ⟨(mem_idealsLe (by linarith)).mpr hvK, hv₀, hcut⟩, u, s,
    mem_filter.mpr ⟨(mem_idealsLe (by positivity)).mpr ((le_div_iff₀ (by positivity)).mpr ?_),
      hs⟩, ?_⟩
  · rwa [mul_comm]
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using hu

private lemma inverse_square_dyadic {A : ℝ}
    (hA : ∀ x : ℝ, 1 ≤ x → ((idealsLe x).card : ℝ) ≤ A * x) (j : ℕ) :
    ∑ v ∈ idealsLe ((2 : ℝ) ^ j), ((absNorm v : ℝ) ^ 2)⁻¹ ≤ A * (5 - 4 / (2 : ℝ) ^ j) := by
  classical
  induction j with
  | zero =>
    calc
      _ ≤ ∑ _v ∈ idealsLe ((2 : ℝ)^0), (1 : ℝ) := by
        apply sum_le_sum
        intro v _
        by_cases hv : absNorm v = 0
        · simp [hv]
        · have hn : (1 : ℝ) ≤ absNorm v := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hv
          exact inv_le_one_of_one_le₀ (one_le_pow₀ hn)
      _ ≤ _ := by
        simpa only [pow_zero, sum_const, nsmul_eq_mul, mul_one, div_one,
          show (5 : ℝ) - 4 = 1 by norm_num] using hA 1 le_rfl
  | succ j ih =>
    let L := (2 : ℝ) ^ j
    have hL : 1 ≤ L := one_le_pow₀ (by norm_num)
    have hp : 0 < L := by linarith
    have hsub : idealsLe L ⊆ idealsLe (L * 2) := idealsLe_mono (by linarith)
    let B := idealsLe (L * 2) \ idealsLe L
    have hband : ∑ v ∈ B, ((absNorm v : ℝ) ^ 2)⁻¹ ≤ 2 * A / L := calc
      _ ≤ ∑ _ ∈ B, (L ^ 2)⁻¹ := by
        refine sum_le_sum fun v hv => ?_
        have hNv : L < (absNorm v : ℝ) :=
          lt_of_not_ge fun h => (mem_sdiff.mp hv).2 ((mem_idealsLe hp.le).mpr h)
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le hNv.le 2)
      _ = B.card / L ^ 2 := by simp [div_eq_mul_inv]
      _ ≤ A * (L * 2) / L ^ 2 := div_le_div_of_nonneg_right
        ((Nat.cast_le.mpr (card_le_card (sdiff_subset : B ⊆ _))).trans (hA _ (by linarith))) (by
          positivity)
      _ = _ := by field_simp
    rw [pow_succ, ← sum_sdiff hsub]
    calc
      _ ≤ 2 * A / L + A * (5 - 4 / L) := add_le_add hband ih
      _ = _ := by change _ = A * (5 - 4 / (L * 2)); field_simp; ring

/-- A uniform bound for the inverse-square ideal weights in every row truncation. -/
theorem inverse_square_bound :
    ∃ B ≥ (0 : ℝ), ∀ {K : ℝ}, 1 ≤ K → ∑ v ∈ idealsLe K, ((absNorm v : ℝ) ^ 2)⁻¹ ≤ B := by
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  have ha : 0 ≤ A := (Nat.cast_nonneg (idealsLe 1).card).trans (by simpa using hA 1 le_rfl)
  refine ⟨5 * A, by positivity, ?_⟩
  intro K hK
  obtain ⟨i, _, hi⟩ := exists_nat_pow_near hK (by norm_num : (1 : ℝ) < 2)
  calc
    _ ≤ ∑ v ∈ idealsLe ((2 : ℝ) ^ (i + 1)), ((absNorm v : ℝ) ^ 2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (idealsLe_mono hi.le) (fun _ _ _ => by positivity)
    _ ≤ _ := inverse_square_dyadic hA _
    _ ≤ _ := by nlinarith [show 0 ≤ A * (4 / (2 : ℝ) ^ (i + 1)) by positivity]

/-- Absolute convergence of the multiplicity bound for square divisors. -/
theorem summable_inverse_square : Summable (fun v : Ideal 𝓔 => ((absNorm v : ℝ) ^ 2)⁻¹) := by
  obtain ⟨B, _, hB⟩ := inverse_square_bound
  apply summable_of_sum_le (c := B) (fun _ => by positivity)
  intro S
  let N := S.sup (fun v => absNorm v) + 1
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
  have hsub : S ⊆ idealsLe N := fun v hv => (mem_idealsLe (by positivity)).mpr (by
    exact_mod_cast (Finset.le_sup (f := fun v => absNorm v) hv).trans (Nat.le_succ _))
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (hB hN)

private theorem cover_sum {K : ℝ} (hK : 1 ≤ K) (T : 𝓔 → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∑ k ∈ elementRows K, T k ≤ ∑ v ∈ squareDivisors K, ∑ u : 𝓔ˣ,
      ∑ s ∈ squarefreeRows (K / (absNorm v : ℝ) ^ 2), T ((u : 𝓔) * generator s * generator v ^
        2) := by
  classical
  let S (v : Ideal 𝓔) := squarefreeRows (K / (absNorm v : ℝ) ^ 2)
  let P := (squareDivisors K).sigma (fun v => (univ : Finset 𝓔ˣ) ×ˢ S v)
  let r (p : (_ : Ideal 𝓔) × (𝓔ˣ × Ideal 𝓔)) := (p.2.1 : 𝓔) * generator p.2.2 * generator p.1 ^ 2
  have hc : elementRows K ⊆ P.image r := by
    intro k hk
    obtain ⟨v, hv, u, s, hs, he⟩ := row_cover hK hk
    exact mem_image.mpr ⟨⟨v, u, s⟩, mem_sigma.mpr ⟨hv, mem_product.mpr ⟨mem_univ _, hs⟩⟩, he⟩
  calc
    _ ≤ ∑ k ∈ P.image r, T k := sum_le_sum_of_subset_of_nonneg hc (fun k _ _ => hT k)
    _ ≤ ∑ p ∈ P, T (r p) := sum_image_le_of_nonneg (fun k _ => hT k)
    _ = _ := by simp only [P, sum_sigma, sum_product, r, S]

private lemma generator_ne {v : Ideal 𝓔} (hv : v ≠ 0) : generator v ≠ 0 :=
  fun h => hv (by simpa [h] using (span_generator v).symm)

/-- Extract the square part of each row and absorb it into the auxiliary element.
Its norm grows by `(Nv)²` while the squarefree row length falls by the same factor. -/
theorem completedEstimate_of_squarefree (hsq : SquarefreeCompletedEstimate) : CompletedEstimate
    := by
  classical
  intro C₀ hC₀ ε hε
  obtain ⟨j, hj⟩ := hsq (2 * C₀) (by linarith) ε hε
  refine ⟨j, fun I => ?_⟩
  obtain ⟨C, hC, hsf⟩ := hj I
  obtain ⟨B, hB, hBsum⟩ := inverse_square_bound
  refine ⟨(Fintype.card 𝓔ˣ : ℝ) * B * C, by positivity, ?_⟩
  intro D K X f ξ W hD hK hKD hX hXD hf hfD hW
  have hDp : 0 < D := by linarith
  have hXp : 0 < X := by linarith
  have hKp : 0 < K := by linarith
  have hD₂ : D ^ C₀ ≤ D ^ (2 * C₀) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  let G (v : Ideal 𝓔) := generator f * generator v ^ 2
  let H (v : Ideal 𝓔) := K / (absNorm v : ℝ) ^ 2
  let E := C * D ^ ε * (K + K ^ 2 * absNorm f / X)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hv (v : Ideal 𝓔) (hv : v ∈ squareDivisors K) (u : 𝓔ˣ) :
      (∑ s ∈ squarefreeRows (H v),
        ‖completedSum ξ W X ((u : 𝓔) * generator s * generator v ^ 2) f‖ ^ 2) ≤
          ((absNorm v : ℝ) ^ 2)⁻¹ * E := by
    obtain ⟨_, hv₀, hcut⟩ := mem_filter.mp hv
    have hNv : 1 ≤ (absNorm v : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hv₀)
    have hvp : 0 < (absNorm v : ℝ) := by linarith
    have hH : 1 ≤ H v := (one_le_div (by positivity)).mpr hcut
    have hHK : H v ≤ K := div_le_self hKp.le (one_le_pow₀ hNv)
    have hN : (elementNorm (G v) : ℝ) = absNorm f * (absNorm v : ℝ) ^ 2 := by
      simp only [elementNorm, G, ← span_singleton_mul_span_singleton, ← span_singleton_pow,
        span_generator,
        map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    have hNG : (elementNorm (G v) : ℝ) ≤ D ^ (2 * C₀) := calc
      _ = _ := hN
      _ ≤ D ^ C₀ * D ^ C₀ := mul_le_mul hfD (hcut.trans hKD) (sq_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hDp]; ring_nf
    have h := hsf D (H v) X u (G v) ξ W hD hH (hHK.trans (hKD.trans hD₂)) hX (hXD.trans hD₂)
      (mul_ne_zero (generator_ne hf.1.1) (pow_ne_zero _ (generator_ne hv₀))) hNG hW
    calc
      _ = ∑ s ∈ squarefreeRows (H v), ‖completedAtElement ξ W X ((u : 𝓔) * generator s) (G v)‖ ^ 2
        := by
        refine sum_congr rfl fun s _ => ?_
        rw [completedSum_eq_atElement, completedAtElement_shift_square]
      _ ≤ _ := h
      _ = _ := by
        rw [hN]
        dsimp only [H, E]
        field_simp
  have hsum : ∑ v ∈ squareDivisors K, ((absNorm v : ℝ) ^ 2)⁻¹ ≤ B :=
    (sum_le_sum_of_subset_of_nonneg (show squareDivisors K ⊆ idealsLe K from filter_subset _ _)
      (fun _ _ _ => by positivity)).trans (hBsum hK)
  calc
    _ ≤ _ := cover_sum hK (fun k => ‖completedSum ξ W X k f‖ ^ 2) (fun _ => sq_nonneg _)
    _ ≤ ∑ v ∈ squareDivisors K, ∑ _u : 𝓔ˣ, ((absNorm v : ℝ) ^ 2)⁻¹ * E :=
      sum_le_sum fun v hmem => sum_le_sum fun u _ => hv v hmem u
    _ = (Fintype.card 𝓔ˣ : ℝ) * (∑ v ∈ squareDivisors K, ((absNorm v : ℝ) ^ 2)⁻¹) * E := by
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_assoc, Finset.mul_sum, Finset.sum_mul]
    _ ≤ (Fintype.card 𝓔ˣ : ℝ) * B * E := by gcongr
    _ = _ := by dsimp [E]; ring

end Masullo.QRH.MeanSquare.ReflectionRows
