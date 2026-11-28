import Masullo.QRH.MeanSquare.TransferExpand

/-!
# The rows and columns of a Poisson pass

After the Möbius inversion `sum_gcdSplitsLe_eq`, a Poisson pass is a sum over the Möbius splits
`(b, e, v, m₁, m₂)`. With both columns `b e v mᵢ` of norm at most `X`, these are the dual rows
`(b, e, v) ∈ passRows X` and two columns `m₂, m₁ ∈ passCols X (b, e, v)`.
-/

noncomputable section

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The dual rows `(b, e, v)`: starred `g = b e` and `v`, coprime, of norms at most `X`. -/
def passRows (X : ℝ) : Finset (Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) := by
  classical
  exact ((idealsLe X) ×ˢ ((idealsLe X) ×ˢ (idealsLe X))).filter fun r =>
    Starred (r.1 * r.2.1) ∧ Starred r.2.2 ∧ IsCoprime (r.1 * r.2.1) r.2.2

/-- The dual columns of the row `r = (b, e, v)`: starred `x` coprime to `b e v`, with
`N(b e v x) ≤ X`. -/
def passCols (X : ℝ) (r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : Finset (Ideal 𝓔) := by
  classical
  exact (idealsLe X).filter fun x =>
    Starred x ∧ IsCoprime (r.1 * r.2.1 * r.2.2) x ∧
      (absNorm (r.1 * r.2.1 * r.2.2 * x) : ℝ) ≤ X

/-- The Möbius splits with both columns of norm at most `X` are the dual rows and pairs of
dual columns. -/
theorem sum_moebiusSplitsLe_eq {X : ℝ} (hX : 0 ≤ X)
    (F : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → Ideal 𝓔 → Ideal 𝓔 → ℂ) : open Classical in
    ∑ u ∈ moebiusSplitsLe X,
      (if (absNorm (u.1 * u.2.1 * (u.2.2.1 * u.2.2.2.2)) : ℝ) ≤ X ∧
          (absNorm (u.1 * u.2.1 * (u.2.2.1 * u.2.2.2.1)) : ℝ) ≤ X then
        F (u.1, u.2.1, u.2.2.1) u.2.2.2.2 u.2.2.2.1 else 0) =
      ∑ r ∈ passRows X, ∑ x₁ ∈ passCols X r, ∑ x₂ ∈ passCols X r, F r x₁ x₂ := by
  classical
  rw [← Finset.sum_filter]
  have h2 : ∑ r ∈ passRows X, ∑ x₁ ∈ passCols X r, ∑ x₂ ∈ passCols X r, F r x₁ x₂ =
      ∑ r ∈ passRows X, ∑ p ∈ passCols X r ×ˢ passCols X r, F r p.1 p.2 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_product]
  rw [h2, Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun u _ =>
      (⟨(u.1, u.2.1, u.2.2.1), (u.2.2.2.2, u.2.2.2.1)⟩ : Σ _ : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔, Ideal 𝓔
      × Ideal 𝓔))
    (fun q _ => (q.1.1, q.1.2.1, q.1.2.2, q.2.2, q.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, e, v, m₁, m₂⟩ hu
    simp only [moebiusSplitsLe, passRows, passCols, Finset.mem_filter, Finset.mem_product,
      Finset.mem_sigma, mem_idealsLe hX] at hu ⊢
    obtain ⟨⟨⟨hb, he, hv, hm₁, hm₂⟩, hg, hz₁, hz₂, hco, hNg, hN₁, hN₂⟩, hM₂, hM₁⟩ := hu
    have c₁ := hco.of_mul_right_left
    have c₂ := hco.of_mul_right_right
    refine ⟨⟨⟨hb, he, hv⟩, hg, hz₁.of_mul_left, c₁.of_mul_right_left⟩,
      ⟨hm₂, hz₂.of_mul_right, ?_, by rwa [mul_assoc]⟩,
      hm₁, hz₁.of_mul_right, ?_, by rwa [mul_assoc]⟩
    · exact (c₂.of_mul_right_right).mul_left (isCoprime_of_squarefree_mul hz₂.2)
    · exact (c₁.of_mul_right_right).mul_left (isCoprime_of_squarefree_mul hz₁.2)
  · rintro ⟨⟨b, e, v⟩, x₁, x₂⟩ hq
    simp only [moebiusSplitsLe, passRows, passCols, Finset.mem_filter, Finset.mem_product,
      Finset.mem_sigma, mem_idealsLe hX] at hq ⊢
    obtain ⟨⟨⟨hb, he, hv⟩, hg, hvS, hcv⟩, ⟨hx₁, s₁, c₁, N₁⟩, ⟨hx₂, s₂, c₂, N₂⟩⟩ := hq
    have a₁ := c₁.of_mul_left_left
    have a₂ := c₂.of_mul_left_left
    have d₁ := c₁.of_mul_left_right
    have d₂ := c₂.of_mul_left_right
    have p₁ := hvS.mul_of_isCoprime s₁ d₁
    have p₂ := hvS.mul_of_isCoprime s₂ d₂
    rw [mul_assoc] at N₁ N₂
    have e₁ := absNorm_le_absNorm_mul (mul_ne_zero hg.1.1 p₁.1.1)
    have e₂ := absNorm_le_absNorm_mul (mul_ne_zero hg.1.1 p₂.1.1)
    refine ⟨⟨⟨hb, he, hv, hx₂, hx₁⟩, hg, p₂, p₁,
      ((hcv.mul_right a₂).mul_right (hcv.mul_right a₁)), ?_, ?_, ?_⟩, N₁, N₂⟩
    · exact (e₁.1.trans N₁)
    · exact (e₂.2.trans N₂)
    · exact (e₁.2.trans N₁)
  · intro u _; rfl
  · rintro ⟨⟨b, e, v⟩, x₁, x₂⟩ _; rfl
  · intro u hu
    simp only [Finset.mem_filter] at hu
    simp

end Masullo.QRH.MeanSquare
