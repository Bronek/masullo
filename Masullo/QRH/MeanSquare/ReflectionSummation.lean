import Masullo.QRH.MeanSquare.ReflectionSeparation

/-! # Summation of the reflected kernel blocks and the number of tame choices -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare.ReflectionSieve

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- A fixed number of choices per distinct prime costs an arbitrarily small
power of the ideal norm. Small primes belong to one finite set independent of
the ideal, while the remaining local choices are paid for by the prime norm. -/
theorem branch_count_bound {q δ : ℝ} (hq : 1 ≤ q) (hδ : 0 < δ) :
    ∃ C ≥ (0 : ℝ), ∀ (a : Ideal 𝓔), a ≠ 0 → ∀ P ⊆ (normalizedFactors a).toFinset,
      q ^ P.card ≤ C * (absNorm a : ℝ) ^ δ := by
  classical
  let V := q ^ δ⁻¹
  let S := idealsLe V
  have hq₀ := zero_le_one.trans hq
  have hV : 0 ≤ V := Real.rpow_nonneg hq₀ _
  refine ⟨q^S.card,by positivity,fun a ha P hP => ?_⟩
  have hp (p : Ideal 𝓔) (h : p ∈ P) : p ∈ normalizedFactors a := Multiset.mem_toFinset.mp (hP h)
  have he := partial_norm_product ha (P \ S) (fun _ => 1)
    (fun p h => Multiset.count_pos.mpr (hp p (mem_sdiff.mp h).1))
    (fun p h => (prime_of_normalized_factor _ (hp p (mem_sdiff.mp h).1)).ne_zero)
  simp only [pow_one] at he
  have hlarge (p : Ideal 𝓔) (h : p ∈ P \ S) : q ≤ (absNorm p : ℝ)^δ := by
    have hn : ¬(absNorm p : ℝ) ≤ V := fun hh => (mem_sdiff.mp h).2 ((mem_idealsLe hV).mpr hh)
    exact (Real.rpow_inv_rpow hq₀ hδ.ne').symm.le.trans (Real.rpow_le_rpow hV (le_of_not_ge hn) hδ.le)
  rw [← Finset.prod_const,← Finset.prod_inter_mul_prod_sdiff P S]
  calc
    _ ≤ q ^ S.card * ∏ p ∈ P \ S, (absNorm p : ℝ)^δ := by
      rw [Finset.prod_const]
      exact mul_le_mul (pow_le_pow_right₀ hq (card_le_card inter_subset_right))
        (prod_le_prod₀ (fun _ _ => hq₀) hlarge) (by positivity) (by positivity)
    _ ≤ _ := by
      rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) he hδ.le) (by positivity)

/-- Summing a nonnegative envelope over arbitrary finite sets of triples is
controlled by its rectangular sums. -/
private theorem sum_triples_le {f : ℕ × ℕ × ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {H : ℝ}
    (h : ∀ M U B : Finset ℕ, (∑ k ∈ M, ∑ i ∈ U, ∑ j ∈ B, f (k,i,j)) ≤ H)
    (s : Finset (ℕ × ℕ × ℕ)) : ∑ n ∈ s, f n ≤ H := by
  let M := s.image (fun n => n.1)
  let U := s.image (fun n => n.2.1)
  let B := s.image (fun n => n.2.2)
  have hsub : s ⊆ M ×ˢ (U ×ˢ B) := fun n hn => mem_product.mpr
    ⟨mem_image_of_mem _ hn,mem_product.mpr ⟨mem_image_of_mem _ hn,mem_image_of_mem _ hn⟩⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)).trans (by
    simpa only [sum_product] using h M U B)

/-- A reflected branch has absolutely summable dyadic blocks in row norm.
This also controls finite truncations with arbitrary cutoffs in the three indices. -/
theorem sum_dyadic_blocks {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ C ≥ (0 : ℝ), ∀ {K Y L : ℝ}, 0 ≤ K → 0 < Y → 0 ≤ L →
    ∀ F : ℕ × ℕ × ℕ → E,
      (∀ k i j : ℕ, ‖F (k,i,j)‖ ≤ L * (3 : ℝ) ^ (-((k : ℝ)-3)/3) *
        (K * (2 : ℝ)^i)^ρ * (Real.sqrt K + Real.sqrt (2^i)) /
        (1 + kernelScale ((k : ℤ)-3) (2^i) (2^j) Y)^3) →
      Summable (fun n => ‖F n‖) ∧ ‖∑' n, F n‖ ≤
        C * L * K^ρ * Y^(2*ρ) * (Real.sqrt K + Real.sqrt Y) := by
  obtain ⟨C,hC,h⟩ := summed_block_envelope hρ hρ₁
  refine ⟨C,hC,?_⟩
  intro K Y L hK hY hL F hF
  have hfin (s : Finset (ℕ × ℕ × ℕ)) : ∑ n ∈ s, ‖F n‖ ≤
      C * L * K^ρ * Y^(2*ρ) * (Real.sqrt K + Real.sqrt Y) := by
    apply sum_triples_le (fun _ => norm_nonneg _) _ s
    intro M U B
    calc
      _ ≤ ∑ k ∈ M, ∑ i ∈ U, ∑ j ∈ B, L * (3:ℝ)^(-((k:ℝ)-3)/3) *
            (K*(2:ℝ)^i)^ρ * (Real.sqrt K + Real.sqrt (2^i)) /
            (1+kernelScale ((k:ℤ)-3) (2^i) (2^j) Y)^3 :=
        sum_le_sum fun k _ => sum_le_sum fun i _ => sum_le_sum fun j _ => hF k i j
      _ = L * (∑ k ∈ M, (3:ℝ)^(-((k:ℝ)-3)/3) * ∑ i ∈ U, ∑ j ∈ B,
            (K*(2:ℝ)^i)^ρ * (Real.sqrt K + Real.sqrt (2^i)) /
            (1+kernelScale ((k:ℤ)-3) (2^i) (2^j) Y)^3) := by
        simp only [Finset.mul_sum]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ ≤ L*(C*K^ρ*Y^(2*ρ)*(Real.sqrt K + Real.sqrt Y)) :=
        mul_le_mul_of_nonneg_left (h hK hY M U B) hL
      _ = _ := by ring
  have hs := summable_of_sum_le (fun n => norm_nonneg (F n)) hfin
  exact ⟨hs,(norm_tsum_le_tsum_norm hs).trans (le_of_tendsto' hs.hasSum hfin)⟩

/-- The row vector contributed by one valuation and pair of dyadic norm bands. -/
def kernelBlockVector (W : ℝ → ℂ) (R S T : Finset (Ideal 𝓔)) (m : ℤ) (V : ℝ)
    (c d : Ideal 𝓔 → Ideal 𝓔 → ℂ) (u : Ideal 𝓔 → Ideal 𝓔 → ℝ) : EuclideanSpace ℂ R :=
  (3 : ℝ) ^ (-(m : ℝ)/3) • WithLp.toLp 2 (fun k : R => kernelBlock W V S T c d u k)

/-- The full sum of the product-kernel blocks in (15), after fixing a tame
branch and the finite ray classes. Neither cutoffs nor transform coefficients
are required in the conclusion. -/
theorem summed_kernel_branch (quad : DeloupTuraevTheorem1)
    (sieve : QuadraticSieve primaryQuadraticSymbol) (hΓ : DLMFGammaVertical)
    (I : TestInterval) {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ C ≥ (0 : ℝ), ∀ {K Y a : ℝ}, 1 ≤ K → 0 < Y → 0 ≤ a →
    ∀ (W : ℝ → ℂ), UnitTest I 14 W → ∀ (g : QuadraticFamilyClass) (R : Finset (Ideal 𝓔)),
    R ⊆ sieveIdeals (span {6}) K → (∀ k ∈ R, familyClass k = g) →
    ∀ (S T : ℕ → Finset (Ideal 𝓔)),
      (∀ i, S i ⊆ dyadicSieveIdeals (span {6}) (2^i)) →
      (∀ j, ∀ b ∈ T j, (absNorm b : ℝ) ∈ Set.Ico (2^j) (2*2^j)) →
    ∀ (c d : ℕ × ℕ × ℕ → Ideal 𝓔 → Ideal 𝓔 → ℂ) (u : ℕ × ℕ × ℕ → Ideal 𝓔 → Ideal 𝓔 → ℝ),
      (∀ e, ∀ b ∈ T e.2.2, ∀ n ∈ S e.2.1, ‖c e b n‖ ≤ a) →
      (∀ e, ∀ b ∈ T e.2.2, ∀ k ∈ R, ‖d e b k‖ ≤ 1) →
      (∀ e, ∀ b ∈ T e.2.2, ∀ k ∈ R, kernelScale ((e.1:ℤ)-3) (2^e.2.1) (2^e.2.2) Y ≤ u e b k) →
      let F := fun e : ℕ × ℕ × ℕ => kernelBlockVector W R (S e.2.1) (T e.2.2) ((e.1:ℤ)-3)
        (2^e.2.1) (c e) (d e) (u e)
      Summable (fun e => ‖F e‖) ∧ ‖∑' e, F e‖ ≤
        C * a * K^ρ * Y^(2*ρ) * (Real.sqrt K + Real.sqrt Y) := by
  obtain ⟨B,hB,hb⟩ := kernel_dyadic_block quad sieve hΓ I hρ
  obtain ⟨L,hL,hl⟩ := sum_dyadic_blocks (E := ℝ) hρ hρ₁
  -- The scalar series of block norms has the same majorant in every row space.
  refine ⟨L*B,by positivity,?_⟩
  intro K Y a hK hY ha W hw g R hR hg S T hS hT c d u hc hd hu
  let F (e : ℕ × ℕ × ℕ) := kernelBlockVector W R (S e.2.1) (T e.2.2) ((e.1:ℤ)-3)
    (2^e.2.1) (c e) (d e) (u e)
  have hbd k i j : ‖‖F (k,i,j)‖‖ ≤ B*a*(3:ℝ)^(-((k:ℝ)-3)/3) *
      (K*(2:ℝ)^i)^ρ * (Real.sqrt K + Real.sqrt (2^i)) /
      (1+kernelScale ((k:ℤ)-3) (2^i) (2^j) Y)^3 := by
    rw [norm_norm]
    dsimp only [F,kernelBlockVector]
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _),
      EuclideanSpace.norm_eq]
    have h := hb W hw hK (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
      hY ha ((k:ℤ)-3) g R (S i) (T j) hR (hS i) hg (hT j) (c (k,i,j)) (d (k,i,j)) (u (k,i,j))
      (hc (k,i,j)) (hd (k,i,j)) (hu (k,i,j))
    rw [← R.sum_coe_sort] at h
    push_cast at h ⊢
    exact h
  obtain ⟨hs,h⟩ := hl (zero_le_one.trans hK) hY (mul_nonneg hB ha) (fun e => ‖F e‖) hbd
  simp only [norm_norm] at hs
  refine ⟨hs,(norm_tsum_le_tsum_norm hs).trans ?_⟩
  rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))] at h
  exact h.trans_eq (by ring)

end Masullo.QRH.MeanSquare.ReflectionSieve
