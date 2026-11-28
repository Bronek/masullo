import Masullo.QRH.MeanSquare.DualTail

/-!
# Assembly of the nonzero dual frequencies

`GapEstimate` gives `DualTailEstimate rowMajorant`.

* `mainSplitTerm_eq`: a main dual term of a Möbius split `(b, e, v, m₁, m₂)` at the row `h`
  is a combination over ray characters of a row weight `splitRowWeight` and a block summand
  `blockTerm` at `ρ = (e, v, h)`.
* `sum_moebiusSplit_cols_eq`: the columns `(m₁, m₂)` of a Möbius split row are the block
  columns `blockColumns R₀ X`.
* `dualMainSum_eq`: `dualMainSum` as a sum over starred `b`, rows `ρ` and ray characters of
  row weights times blocks of column length `blockLength D' b ρ = D' / (N b F)` with dyadic
  `F = dyadicNorm ρ`.
* `exists_norm_dualMainSum_le`: the main dual frequencies are `O(D^(2+θ+ε))`, by
  `exists_block_le` on each dyadic fibre of rows.
* `dualTailEstimate_of_gapEstimate` and `fullRowEstimate_of_gapEstimate`: `GapEstimate` and
  `PairedGaussIdentities` give `DualTailEstimate rowMajorant` and `FullRowEstimate`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-- The row weight of `ρ = (e, v, h)` in a block with column length `X`. -/
def splitRowWeight (ξ η : RayCharacter) (Y X : ℝ) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) : ℂ :=
  (idealMoebius ρ.1 : ℂ) * idealMoebius ρ.2.1 *
    ((Y / ((absNorm ρ.1 : ℝ) * absNorm ρ.2.1 * X) : ℝ) : ℂ) *
    (gaussCoefficient ρ.2.1 * conj (gaussCoefficient ρ.2.1) *
      ξ (Ideal.Quotient.mk _ (generator ρ.2.1)) *
      conj (η (Ideal.Quotient.mk _ (generator ρ.2.1))) *
      (sextic ρ.2.1 ρ.2.2 * conj (sextic ρ.2.1 ρ.2.2)))

/-- The kernel shift `½ log (Y N h / (N e N v² X²))` of `ρ = (e, v, h)`. -/
def rowShift (Y X : ℝ) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) : ℝ :=
  Real.log (Y * elementNorm ρ.2.2 / ((absNorm ρ.1 : ℝ) * (absNorm ρ.2.1 : ℝ) ^ 2 * X ^ 2)) / 2

/-- The summand of a block in `exists_block_le`, at the shift `rowShift`. -/
def blockTerm (P : SchwartzMap ℝ ℂ) (χ W : ℝ → ℂ) (ξ η : RayCharacter) (b : Ideal 𝓔)
    (Y X F : ℝ) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) (m₁ m₂ : Ideal 𝓔) : ℂ :=
  blockCoefficient ξ b ρ m₁ * conj (blockCoefficient η b ρ m₂) *
    (conj (W (absNorm (ρ.1 * ρ.2.1) / F * (absNorm m₁ / X))) *
      W (absNorm (ρ.1 * ρ.2.1) / F * (absNorm m₂ / X)) *
      cutDualKernel P χ (rowShift Y X ρ) (Real.log (absNorm m₁ / X) + Real.log (absNorm m₂ / X)))

lemma natCast_absNorm_pos {I : Ideal 𝓔} (hI : I ≠ ⊥) : (0 : ℝ) < absNorm I := by
  exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hI)

/-- A main dual term of the Möbius split `(b, e, v, m₁, m₂)` at the row `h`, as a combination
of row weights and block summands at `ρ = (e, v, h)`, for `X F = D' / N b` and
`W(x / D) = W'(x / D')`, wherever the cut `χ` is `e^{-s/2}`. -/
theorem mainSplitTerm_eq (hres : ResidueMultiplicative)
    (hmul : ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      gaussCoefficient (b * c) = gaussCoefficient b * gaussCoefficient c *
        sextic c (generator b) ^ 4)
    {A : Q₇₂ → Q₇₂ → ℂ} {α : RayCharacter → RayCharacter → ℂ}
    (hα : ∀ x y : Q₇₂, IsUnit x → IsUnit y → A x y = ∑ ξ, ∑ η, α ξ η * ξ x * conj (η y))
    (P : SchwartzMap ℝ ℂ) {χ W W' : ℝ → ℂ} {D D' Y X F : ℝ} {b e v m₁ m₂ : Ideal 𝓔} {h : 𝓔}
    (hg : Starred (b * e)) (hz₂ : Starred (v * m₁)) (hz₁ : Starred (v * m₂))
    (hco : IsCoprime (b * e) (v * m₁ * (v * m₂))) (hh : h ≠ 0) (hY : 0 < Y) (hX : 0 < X)
    (hF : 0 < F) (hXF : X * F = D' / absNorm b) (hW : ∀ x, W (x / D) = W' (x / D'))
    (hχ : conj (W' (absNorm (e * v) / F * (absNorm m₁ / X))) *
        W' (absNorm (e * v) / F * (absNorm m₂ / X)) ≠ 0 →
      χ (Real.log (absNorm m₁ / X) + Real.log (absNorm m₂ / X)) =
        (Real.exp (-((Real.log (absNorm m₁ / X) + Real.log (absNorm m₂ / X)) / 2)) : ℂ)) :
    (idealMoebius v : ℂ) * (splitWeight A W D Y (b * e, v * m₂, v * m₁) *
      ((idealMoebius e : ℂ) * pairCharacter (v * m₁) (v * m₂) (generator e) /
        (absNorm e : ℂ) * (conj (pairCharacter (v * m₁) (v * m₂) h) * gaoZhaoTransform P
          (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂)))))))) =
      ∑ ξ, ∑ η, α ξ η * splitRowWeight ξ η Y X (e, v, h) *
        blockTerm P χ W' ξ η b Y X F (e, v, h) m₁ m₂ := by
  classical
  have hb : Starred b := hg.of_mul_left
  have he : AwayFromSix e := hg.of_mul_right.1
  have hv : Starred v := hz₂.of_mul_left
  have hm₁ : Starred m₁ := hz₂.of_mul_right
  have hm₂ : Starred m₂ := hz₁.of_mul_right
  have hvm₁ : IsCoprime v m₁ := isCoprime_of_squarefree_mul hz₂.2
  have hvm₂ : IsCoprime v m₂ := isCoprime_of_squarefree_mul hz₁.2
  have hce : IsCoprime e (v * m₁ * (v * m₂)) := hco.of_mul_left_right
  have hev : IsCoprime e v := hce.of_mul_right_left.of_mul_right_left
  have hem₁ : IsCoprime e m₁ := hce.of_mul_right_left.of_mul_right_right
  have hem₂ : IsCoprime e m₂ := hce.of_mul_right_right.of_mul_right_right
  have hbm₁ : IsCoprime m₁ b := hco.of_mul_left_left.of_mul_right_left.of_mul_right_right.symm
  have hbm₂ : IsCoprime m₂ b := hco.of_mul_left_left.of_mul_right_right.of_mul_right_right.symm
  have hNb := natCast_absNorm_pos hb.1.1
  have hNe := natCast_absNorm_pos he.1
  have hNv := natCast_absNorm_pos hv.1.1
  have hN₁ := natCast_absNorm_pos hm₁.1.1
  have hN₂ := natCast_absNorm_pos hm₂.1.1
  have hNh : (0 : ℝ) < elementNorm h := by
    exact_mod_cast Nat.pos_of_ne_zero
      (absNorm_eq_zero_iff.not.mpr (span_singleton_eq_bot.not.mpr hh))
  have hD' : D' = X * F * absNorm b := by rw [hXF]; field_simp
  have hWm : ∀ m : Ideal 𝓔, W (absNorm (b * e * (v * m)) / D) =
      W' (absNorm (e * v) / F * (absNorm m / X)) := fun m => by
    rw [hW, hD']
    congr 1
    simp only [map_mul, Nat.cast_mul]
    field_simp
  set x₁ := (absNorm m₁ : ℝ) / X
  set x₂ := (absNorm m₂ : ℝ) / X
  have hx₁ : 0 < x₁ := div_pos hN₁ hX
  have hx₂ : 0 < x₂ := div_pos hN₂ hX
  set q := Y * elementNorm h / ((absNorm e : ℝ) * (absNorm v : ℝ) ^ 2 * X ^ 2)
  have hq : 0 < q := by positivity
  have hN : (absNorm (v * m₁ * (v * m₂)) : ℝ) = ((absNorm v : ℝ) * X) ^ 2 * (x₁ * x₂) := by
    simp only [map_mul, Nat.cast_mul, x₁, x₂]
    field_simp
  have hk : ((Y : ℂ) / (Real.sqrt (absNorm (v * m₁ * (v * m₂))) : ℂ)) * gaoZhaoTransform P
      (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂))))) =
      ((Y / ((absNorm v : ℝ) * X) : ℝ) : ℂ) *
        (((Real.sqrt (x₁ * x₂) : ℝ) : ℂ)⁻¹ * gaoZhaoTransform P (Real.sqrt (q / (x₁ * x₂)))) := by
    have harg : Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂))) =
        q / (x₁ * x₂) := by
      rw [hN]
      simp only [q]
      field_simp
    rw [harg, hN, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    push_cast
    field_simp
  set w₁ := W' (absNorm (e * v) / F * x₁)
  set w₂ := W' (absNorm (e * v) / F * x₂)
  have hk2 : conj w₁ * w₂ * (((Y : ℂ) / (Real.sqrt (absNorm (v * m₁ * (v * m₂))) : ℂ)) *
      gaoZhaoTransform P
        (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂)))))) =
      conj w₁ * w₂ * (((Y / ((absNorm v : ℝ) * X) : ℝ) : ℂ) *
        cutDualKernel P χ (rowShift Y X (e, v, h)) (Real.log x₁ + Real.log x₂)) := by
    by_cases hw : conj w₁ * w₂ = 0
    · rw [hw, zero_mul, zero_mul]
    rw [hk, gaoZhaoTransform_eq_cutDualKernel P hq hx₁ hx₂ (hχ hw)]
    rfl
  have hm := mainSummand_eq hres hmul hα he hv hm₁ hm₂ hvm₁ hvm₂ hev hem₁ hem₂ h
  calc _ = (idealMoebius v : ℂ) * idealMoebius e / (absNorm e : ℂ) *
        (gaussCoefficient (v * m₁) * conj (gaussCoefficient (v * m₂)) *
          A (Ideal.Quotient.mk _ (generator (v * m₁)))
            (Ideal.Quotient.mk _ (generator (v * m₂))) *
          (pairCharacter (v * m₁) (v * m₂) (generator e) *
            conj (pairCharacter (v * m₁) (v * m₂) h))) *
        (conj w₁ * w₂ * (((Y : ℂ) / (Real.sqrt (absNorm (v * m₁ * (v * m₂))) : ℂ)) *
          gaoZhaoTransform P (Real.sqrt (Y * elementNorm h /
            ((absNorm e : ℝ) * absNorm (v * m₁ * (v * m₂))))))) := by
        simp only [splitWeight, hWm, w₁, w₂, x₁, x₂]
        ring
    _ = _ := by
        rw [hm, hk2]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
        simp only [splitRowWeight, blockTerm, blockCoefficient, hbm₁, hbm₂, ite_true, w₁, w₂,
          x₁, x₂]
        push_cast
        ring

/-! ### The columns of a row -/

lemma isCoprime_of_le {m I J : Ideal 𝓔} (h : IsCoprime m I) (hIJ : I ≤ J) : IsCoprime m J := by
  rw [isCoprime_iff_sup_eq] at *
  exact eq_top_iff.mpr (h ▸ sup_le_sup_left hIJ m)

lemma starred_mul {I J : Ideal 𝓔} (hI : Starred I) (hJ : Starred J) (h : IsCoprime I J) :
    Starred (I * J) :=
  ⟨hI.1.mul hJ.1, squarefree_mul_iff.mpr ⟨h.isRelPrime, hI.2, hJ.2⟩⟩

/-- A nonzero column coefficient is at a column away from `6` and coprime to `b` and to the
twist ideal. -/
lemma blockCoefficient_ne_zero {ξ : RayCharacter} {b m : Ideal 𝓔} {ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔}
    (h : blockCoefficient ξ b ρ m ≠ 0) :
    IsCoprime m b ∧ AwayFromSix m ∧ IsCoprime m (ρ.1 * ρ.2.1) := by
  classical
  unfold blockCoefficient at h
  split_ifs at h with hmb
  · refine ⟨hmb, ?_⟩
    have ht := right_ne_zero_of_mul h
    unfold twist at ht
    split_ifs at ht with hm
    · refine ⟨hm, ?_⟩
      have hs := right_ne_zero_of_mul ht
      by_contra hc
      refine hs (sextic_eq_zero hm fun hco => hc (isCoprime_of_le hco ?_))
      conv_rhs => rw [← span_generator (ρ.1 * ρ.2.1)]
      exact span_singleton_le_span_singleton.mpr
        (Dvd.dvd.mul_left (dvd_pow_self _ four_ne_zero) _)
    · exact absurd rfl ht
  · exact absurd rfl h

lemma mem_moebiusSplitsLe {X : ℝ} (hX : 0 ≤ X) {b e v m₁ m₂ : Ideal 𝓔} :
    (b, e, v, m₁, m₂) ∈ moebiusSplitsLe X ↔
      ((absNorm b : ℝ) ≤ X ∧ (absNorm e : ℝ) ≤ X ∧ (absNorm v : ℝ) ≤ X ∧
        (absNorm m₁ : ℝ) ≤ X ∧ (absNorm m₂ : ℝ) ≤ X) ∧
      Starred (b * e) ∧ Starred (v * m₁) ∧ Starred (v * m₂) ∧
      IsCoprime (b * e) (v * m₁ * (v * m₂)) ∧ (absNorm (b * e) : ℝ) ≤ X ∧
      (absNorm (v * m₁) : ℝ) ≤ X ∧ (absNorm (v * m₂) : ℝ) ≤ X := by
  classical
  simp only [moebiusSplitsLe, Finset.mem_filter, Finset.mem_product, mem_idealsLe hX]

/-- A double sum over a box with a condition is a double sum over `T` when every nonzero
term satisfies the condition exactly on `T`. -/
lemma sum_sum_ite_eq {ι : Type*} {S T : Finset ι} {p : ι → ι → Prop} [∀ a b, Decidable (p a b)]
    {f : ι → ι → ℂ}
    (h : ∀ a b, f a b ≠ 0 → (a ∈ S ∧ b ∈ S ∧ p a b ↔ a ∈ T ∧ b ∈ T)) :
    ∑ a ∈ S, ∑ b ∈ S, (if p a b then f a b else 0) = ∑ a ∈ T, ∑ b ∈ T, f a b := by
  classical
  rw [← Finset.sum_product' (f := fun a b => if p a b then f a b else 0),
    ← Finset.sum_product' (f := f), ← Finset.sum_filter]
  refine Finset.sum_bij_ne_zero (fun x _ _ => x) (fun x hx hfx => ?_)
    (fun _ _ _ _ _ _ h => h) (fun x hx hfx => ⟨x, ?_, hfx, rfl⟩) fun _ _ _ => rfl
  · obtain ⟨hxS, hp⟩ := Finset.mem_filter.mp hx
    obtain ⟨h₁, h₂⟩ := (h x.1 x.2 hfx).mp ⟨(Finset.mem_product.mp hxS).1,
      (Finset.mem_product.mp hxS).2, hp⟩
    exact Finset.mem_product.mpr ⟨h₁, h₂⟩
  · obtain ⟨h₁, h₂, hp⟩ := (h x.1 x.2 hfx).mpr (Finset.mem_product.mp hx)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₁, h₂⟩, hp⟩

/-- For a row `ρ = (e, v, h)` of a starred `b`, the columns `(m₁, m₂)` of the Möbius splits
`(b, e, v, m₁, m₂)` are the block columns: the remaining terms of `blockTerm` vanish. -/
theorem sum_moebiusSplit_cols_eq (P : SchwartzMap ℝ ℂ) {χ W : ℝ → ℂ} (ξ η : RayCharacter)
    {D' Y X F R R₀ : ℝ} {b e v : Ideal 𝓔} (h : 𝓔) (c : ℂ) (hb : Starred b) (hX : 0 < X)
    (hF : 0 < F) (hR₀ : 1 ≤ R₀) (hXF : X * F = D' / absNorm b)
    (hFe : e * v ≠ ⊥ → F ≤ absNorm (e * v)) (hWz : ∀ x, W (x / D') ≠ 0 → x ≤ D') : open Classical in
    ∑ m₁ ∈ idealsLe D', ∑ m₂ ∈ idealsLe D',
        (if (b, e, v, m₁, m₂) ∈ moebiusSplitsLe D' ∧
            h ∈ elementRows (R * absNorm e / (absNorm (b * e) : ℝ) ^ 2) then
          c * blockTerm P χ W ξ η b Y X F (e, v, h) m₁ m₂ else 0) =
      if Starred (b * e * v) ∧ (absNorm (b * e * v) : ℝ) ≤ D' ∧
          h ∈ elementRows (R * absNorm e / (absNorm (b * e) : ℝ) ^ 2) then
        c * ∑ m₁ ∈ blockColumns R₀ X, ∑ m₂ ∈ blockColumns R₀ X,
          blockTerm P χ W ξ η b Y X F (e, v, h) m₁ m₂
      else 0 := by
  classical
  have hNb := natCast_absNorm_pos hb.1.1
  have hD' : D' = X * F * absNorm b := by rw [hXF]; field_simp
  have hD'0 : 0 ≤ D' := by rw [hD']; positivity
  -- A nonzero weight bounds the norm of `b e v m`.
  have hWn : ∀ m : Ideal 𝓔, W (absNorm (e * v) / F * (absNorm m / X)) ≠ 0 →
      (absNorm (b * e * v * m) : ℝ) ≤ D' := fun m hm => by
    refine hWz _ ?_
    convert hm using 2
    rw [hD']
    simp only [map_mul, Nat.cast_mul]
    field_simp
  -- What a nonzero block term gives.
  have hT : ∀ m₁ m₂, c * blockTerm P χ W ξ η b Y X F (e, v, h) m₁ m₂ ≠ 0 →
      (IsCoprime m₁ b ∧ AwayFromSix m₁ ∧ IsCoprime m₁ (e * v) ∧
        (absNorm (b * e * v * m₁) : ℝ) ≤ D') ∧
      (IsCoprime m₂ b ∧ AwayFromSix m₂ ∧ IsCoprime m₂ (e * v) ∧
        (absNorm (b * e * v * m₂) : ℝ) ≤ D') := fun m₁ m₂ hne => by
    have h' := right_ne_zero_of_mul hne
    unfold blockTerm at h'
    have hc₁ := left_ne_zero_of_mul (left_ne_zero_of_mul h')
    have hc₂ : blockCoefficient η b (e, v, h) m₂ ≠ 0 := fun h0 =>
      right_ne_zero_of_mul (left_ne_zero_of_mul h') (by rw [h0, map_zero])
    have hw := left_ne_zero_of_mul (right_ne_zero_of_mul h')
    have hw₁ : W (absNorm (e * v) / F * (absNorm m₁ / X)) ≠ 0 := fun h0 =>
      left_ne_zero_of_mul hw (by rw [h0, map_zero])
    have hw₂ := right_ne_zero_of_mul hw
    exact ⟨⟨(blockCoefficient_ne_zero hc₁).1, (blockCoefficient_ne_zero hc₁).2.1,
      (blockCoefficient_ne_zero hc₁).2.2, hWn _ hw₁⟩, ⟨(blockCoefficient_ne_zero hc₂).1,
      (blockCoefficient_ne_zero hc₂).2.1, (blockCoefficient_ne_zero hc₂).2.2, hWn _ hw₂⟩⟩
  have hle : ∀ {I J : Ideal 𝓔}, I * J ≠ ⊥ → (absNorm I : ℝ) ≤ absNorm (I * J) ∧
      (absNorm J : ℝ) ≤ absNorm (I * J) := absNorm_le_absNorm_mul
  -- A column of norm `N(b e v m) ≤ D'` lies in the block columns.
  have hcol : ∀ m, Starred m → b * e * v * m ≠ ⊥ → (absNorm (b * e * v * m) : ℝ) ≤ D' →
      m ∈ blockColumns R₀ X := fun m hm hne hN => by
    have hbev : b * (e * v) ≠ ⊥ := by
      rw [← mul_assoc]
      exact left_ne_zero_of_mul hne
    have hev := natCast_absNorm_pos (right_ne_zero_of_mul hbev)
    have hFe' := hFe (right_ne_zero_of_mul hbev)
    simp only [blockColumns, Finset.mem_filter, mem_idealsLe (by positivity : 0 ≤ R₀ * X)]
    refine ⟨?_, hm⟩
    have h1 : (absNorm b : ℝ) * absNorm (e * v) * absNorm m ≤ X * F * absNorm b := by
      rw [← hD']
      convert hN using 1
      simp only [map_mul, Nat.cast_mul]
      ring
    have h2 : (absNorm (e * v) : ℝ) * absNorm m ≤ X * absNorm (e * v) := by
      have : (absNorm (e * v) : ℝ) * absNorm m ≤ X * F := by
        nlinarith
      nlinarith
    have h3 : (absNorm m : ℝ) ≤ X := by nlinarith
    nlinarith
  split_ifs with hρ
  · obtain ⟨hbev, hNbev, hrow⟩ := hρ
    have hbe : Starred (b * e) := hbev.of_mul_left
    have hv : Starred v := hbev.of_mul_right
    have hbev' : IsCoprime (b * e) v := isCoprime_of_squarefree_mul hbev.2
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
    refine sum_sum_ite_eq fun m₁ m₂ hne => ?_
    obtain ⟨⟨hb₁, h6₁, hev₁, hN₁⟩, ⟨hb₂, h6₂, hev₂, hN₂⟩⟩ := hT m₁ m₂ hne
    rw [mem_idealsLe hD'0, mem_idealsLe hD'0, mem_moebiusSplitsLe hD'0]
    constructor
    · rintro ⟨-, -, ⟨-, -, hz₁, hz₂, -⟩, -⟩
      exact ⟨hcol m₁ hz₁.of_mul_right ((mul_assoc (b * e) v m₁).symm ▸
        mul_ne_zero hbe.1.1 hz₁.1.1) hN₁, hcol m₂ hz₂.of_mul_right
        ((mul_assoc (b * e) v m₂).symm ▸ mul_ne_zero hbe.1.1 hz₂.1.1) hN₂⟩
    · rintro ⟨hc₁, hc₂⟩
      have hm₁ : Starred m₁ := (Finset.mem_filter.mp hc₁).2
      have hm₂ : Starred m₂ := (Finset.mem_filter.mp hc₂).2
      have hvm₁ : IsCoprime v m₁ := (hev₁.of_mul_right_right).symm
      have hvm₂ : IsCoprime v m₂ := (hev₂.of_mul_right_right).symm
      have hz₁ := starred_mul hv hm₁ hvm₁
      have hz₂ := starred_mul hv hm₂ hvm₂
      have hcop : ∀ {m : Ideal 𝓔}, IsCoprime m b → IsCoprime m (e * v) → IsCoprime v m →
          IsCoprime (b * e) (v * m) := fun h₁ h₂ h₃ =>
        IsCoprime.mul_right hbev' (IsCoprime.mul_left h₁.symm h₂.of_mul_right_left.symm)
      have hne₁ : b * e * v * m₁ ≠ ⊥ := (starred_mul hbev hm₁
        ((isCoprime_of_le (hb₁.mul_right hev₁) (by rw [mul_assoc]))).symm).1.1
      have hne₂ : b * e * v * m₂ ≠ ⊥ := (starred_mul hbev hm₂
        ((isCoprime_of_le (hb₂.mul_right hev₂) (by rw [mul_assoc]))).symm).1.1
      have hN₁' : ∀ {I : Ideal 𝓔}, I ∣ b * e * v * m₁ → (absNorm I : ℝ) ≤ D' := fun ⟨J, hJ⟩ =>
        (hle (hJ ▸ hne₁)).1.trans (hJ ▸ hN₁)
      have hN₂' : ∀ {I : Ideal 𝓔}, I ∣ b * e * v * m₂ → (absNorm I : ℝ) ≤ D' := fun ⟨J, hJ⟩ =>
        (hle (hJ ▸ hne₂)).1.trans (hJ ▸ hN₂)
      refine ⟨hN₁' ⟨b * e * v, by ring⟩, hN₂' ⟨b * e * v, by ring⟩,
        ⟨⟨hN₁' ⟨e * v * m₁, by ring⟩, hN₁' ⟨b * v * m₁, by ring⟩, hN₁' ⟨b * e * m₁, by ring⟩,
          hN₁' ⟨b * e * v, by ring⟩, hN₂' ⟨b * e * v, by ring⟩⟩, hbe, hz₁, hz₂,
          IsCoprime.mul_right (hcop hb₁ hev₁ hvm₁) (hcop hb₂ hev₂ hvm₂),
          hN₁' ⟨v * m₁, by ring⟩, hN₁' ⟨b * e, by ring⟩, hN₂' ⟨b * e, by ring⟩⟩, hrow⟩
  · refine Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ => ?_
    split_ifs with hu
    · by_contra hne
      obtain ⟨⟨-, -, -, hN₁⟩, -⟩ := hT m₁ m₂ hne
      obtain ⟨hmem, hrow⟩ := hu
      obtain ⟨-, hbe, hz₁, -, hco, -⟩ := (mem_moebiusSplitsLe hD'0).mp hmem
      have hv : Starred v := hz₁.of_mul_left
      have hbev := starred_mul hbe hv hco.of_mul_right_left.of_mul_right_left
      have hne₁ : b * e * v * m₁ ≠ ⊥ := by
        rw [mul_assoc (b * e)]
        exact mul_ne_zero hbe.1.1 hz₁.1.1
      exact hρ ⟨hbev, (hle hne₁).1.trans hN₁, hrow⟩
    · rfl

/-! ### The main dual frequencies as blocks -/

/-- The dyadic norm `2^⌊log₂ N(e v)⌋` of `ρ = (e, v, h)`. -/
def dyadicNorm (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) : ℝ := 2 ^ Nat.log 2 (absNorm (ρ.1 * ρ.2.1))

/-- The column length `D' / (N b F)` of the row `ρ` of `b`, with `F = dyadicNorm ρ`. -/
def blockLength (D' : ℝ) (b : Ideal 𝓔) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) : ℝ :=
  D' / (absNorm b * dyadicNorm ρ)

lemma dyadicNorm_pos (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) : 0 < dyadicNorm ρ := by
  unfold dyadicNorm
  positivity

lemma dyadicNorm_le {ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔} (h : ρ.1 * ρ.2.1 ≠ ⊥) :
    dyadicNorm ρ ≤ absNorm (ρ.1 * ρ.2.1) := by
  unfold dyadicNorm
  exact_mod_cast Nat.pow_log_le_self 2 (absNorm_eq_zero_iff.not.mpr h)

lemma lt_two_mul_dyadicNorm (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) :
    (absNorm (ρ.1 * ρ.2.1) : ℝ) < 2 * dyadicNorm ρ := by
  unfold dyadicNorm
  rw [← pow_succ']
  exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) _

/-- Reordering `Σ_a Σ_b Σ_c Σ_d Σ_e` as `Σ_c Σ_d Σ_e Σ_a Σ_b`. -/
lemma sum_comm₂₃ {ι₁ ι₂ ι₃ ι₄ ι₅ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (s₃ : Finset ι₃)
    (s₄ : Finset ι₄) (s₅ : Finset ι₅) (f : ι₁ → ι₂ → ι₃ → ι₄ → ι₅ → ℂ) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ e ∈ s₅, f a b c d e =
      ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ e ∈ s₅, ∑ a ∈ s₁, ∑ b ∈ s₂, f a b c d e := by
  calc _ = ∑ p ∈ s₁ ×ˢ s₂, ∑ q ∈ s₃ ×ˢ (s₄ ×ˢ s₅), f p.1 p.2 q.1 q.2.1 q.2.2 := by
        simp only [Finset.sum_product]
    _ = ∑ q ∈ s₃ ×ˢ (s₄ ×ˢ s₅), ∑ p ∈ s₁ ×ˢ s₂, f p.1 p.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_product]

/-- The main dual frequencies `dualMainSum` as a sum over starred `b`, rows `ρ = (e, v, h)`
and ray characters of a row weight times a block, for `W(x / D) = W'(x / D')` with `W'`
vanishing beyond `1` and the cut `χ` equal to `e^{-s/2}` where `W'` meets two columns. -/
theorem dualMainSum_eq (hres : ResidueMultiplicative)
    (hmul : ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      gaussCoefficient (b * c) = gaussCoefficient b * gaussCoefficient c *
        sextic c (generator b) ^ 4)
    {A : Q₇₂ → Q₇₂ → ℂ} {α : RayCharacter → RayCharacter → ℂ}
    (hα : ∀ x y : Q₇₂, IsUnit x → IsUnit y → A x y = ∑ ξ, ∑ η, α ξ η * ξ x * conj (η y))
    (P : SchwartzMap ℝ ℂ) {χ W W' : ℝ → ℂ} {D D' Y R R₀ : ℝ} (hD : 0 < D) (hD' : 0 < D')
    (hW : ∀ x, W (x / D) = W' (x / D')) (hWz : ∀ x, W' (x / D') ≠ 0 → x ≤ D')
    (hχ : ∀ β y₁ y₂ : ℝ, 1 ≤ β → β < 2 → 0 < y₁ → 0 < y₂ →
      conj (W' (β * y₁)) * W' (β * y₂) ≠ 0 →
        χ (Real.log y₁ + Real.log y₂) =
          (Real.exp (-((Real.log y₁ + Real.log y₂) / 2)) : ℂ))
    (hY : 0 < Y) (hR : 0 ≤ R) (hR₀ : 1 ≤ R₀) : open Classical in
    dualMainSum P A W D Y R =
      ∑ b ∈ (idealsLe D').filter Starred, ∑ e ∈ idealsLe D', ∑ v ∈ idealsLe D',
        ∑ h ∈ elementRows R, ∑ ξ, ∑ η,
          if Starred (b * e * v) ∧ (absNorm (b * e * v) : ℝ) ≤ D' ∧
              h ∈ elementRows (R * absNorm e / (absNorm (b * e) : ℝ) ^ 2) then
            α ξ η * splitRowWeight ξ η Y (blockLength D' b (e, v, h)) (e, v, h) *
              ∑ m₁ ∈ blockColumns R₀ (blockLength D' b (e, v, h)),
                ∑ m₂ ∈ blockColumns R₀ (blockLength D' b (e, v, h)),
                  blockTerm P χ W' ξ η b Y (blockLength D' b (e, v, h)) (dyadicNorm (e, v, h))
                    (e, v, h) m₁ m₂
          else 0 := by
  classical
  set B := idealsLe D' with hB
  set U := moebiusSplitsLe D'
  -- The columns as blocks.
  set G : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → 𝓔 → RayCharacter →
      RayCharacter → ℂ := fun u h ξ η =>
    α ξ η * splitRowWeight ξ η Y (blockLength D' u.1 (u.2.1, u.2.2.1, h)) (u.2.1, u.2.2.1, h) *
      blockTerm P χ W' ξ η u.1 Y (blockLength D' u.1 (u.2.1, u.2.2.1, h))
        (dyadicNorm (u.2.1, u.2.2.1, h)) (u.2.1, u.2.2.1, h) u.2.2.2.1 u.2.2.2.2
  set rows : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → Finset 𝓔 := fun u =>
    elementRows (R * absNorm u.2.1 / (absNorm (u.1 * u.2.1) : ℝ) ^ 2)
  have hWz' : ∀ x, W x ≠ 0 → x ≤ D' / D := fun x hx => by
    have := hWz (x * D) (by rwa [← hW, mul_div_cancel_right₀ _ hD.ne'])
    rwa [le_div_iff₀ hD]
  have h1 : dualMainSum P A W D Y R = ∑ u ∈ U, ∑ h ∈ rows u, ∑ ξ, ∑ η, G u h ξ η := by
    rw [dualMainSum, finsum_splitWeight_eq_sum hWz' hD (by positivity),
      div_mul_cancel₀ _ hD.ne']
    have hH : ∀ t ∈ gcdSplitsLe D', splitWeight A W D Y t *
        dualExclusionMain P Y R t.2.2 t.2.1 t.1 = ∑ e ∈ idealDivisors t.1,
          splitWeight A W D Y t * ((idealMoebius e : ℂ) * pairCharacter t.2.2 t.2.1
            (generator e) / (absNorm e : ℂ) *
            ∑ h ∈ elementRows (R * absNorm e / (absNorm t.1 : ℝ) ^ 2),
              conj (pairCharacter t.2.2 t.2.1 h) * gaoZhaoTransform P
                (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (t.2.2 * t.2.1))))) := by
      intro t ht
      unfold gcdSplitsLe at ht
      have hg : t.1 ≠ ⊥ := (Finset.mem_filter.mp ht).2.1.1.1
      rw [dualExclusionMain, finsum_dvd_eq_sum_idealDivisors hg (fun e =>
        (idealMoebius e : ℂ) * pairCharacter t.2.2 t.2.1 (generator e) / (absNorm e : ℂ) *
          ∑ h ∈ elementRows (R * absNorm e / (absNorm t.1 : ℝ) ^ 2),
            conj (pairCharacter t.2.2 t.2.1 h) * gaoZhaoTransform P
              (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (t.2.2 * t.2.1))))),
        Finset.mul_sum]
    rw [Finset.sum_congr rfl hH, sum_gcdSplitsLe_eq hD'.le]
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨b, e, v, m₁, m₂⟩ := u
    obtain ⟨-, hg, hz₂, hz₁, hco, -⟩ := (mem_moebiusSplitsLe hD'.le).mp hu
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hNb := natCast_absNorm_pos hg.of_mul_left.1.1
    have hev : e * v ≠ ⊥ := mul_ne_zero hg.of_mul_right.1.1 hz₂.of_mul_left.1.1
    have hF := dyadicNorm_pos (e, v, h)
    refine mainSplitTerm_eq hres hmul hα P hg hz₂ hz₁ hco
      ((mem_elementRows (by positivity)).mp hh).1 hY (by unfold blockLength; positivity) hF
      (by unfold blockLength; field_simp) hW fun hw => ?_
    exact hχ _ _ _ ((one_le_div hF).mpr (dyadicNorm_le hev))
      ((div_lt_iff₀ hF).mpr (lt_two_mul_dyadicNorm (e, v, h)))
      (div_pos (natCast_absNorm_pos hz₂.of_mul_right.1.1) (by unfold blockLength; positivity))
      (div_pos (natCast_absNorm_pos hz₁.of_mul_right.1.1) (by unfold blockLength; positivity))
      hw
  have hUsub : U ⊆ B ×ˢ (B ×ˢ (B ×ˢ (B ×ˢ B))) := fun u hu => by
    obtain ⟨b, e, v, m₁, m₂⟩ := u
    obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, -⟩ := (mem_moebiusSplitsLe hD'.le).mp hu
    simp only [Finset.mem_product, hB, mem_idealsLe hD'.le]
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hrows : ∀ u ∈ U, rows u ⊆ elementRows R := fun u hu h hh => by
    obtain ⟨b, e, v, m₁, m₂⟩ := u
    obtain ⟨-, hg, -⟩ := (mem_moebiusSplitsLe hD'.le).mp hu
    have hNe := natCast_absNorm_pos hg.of_mul_right.1.1
    have hNbe := natCast_absNorm_pos hg.1.1
    have hle : (absNorm e : ℝ) ≤ absNorm (b * e) := by
      exact_mod_cast (absNorm_le_absNorm_mul hg.1.1).2
    obtain ⟨hh0, hhN⟩ := (mem_elementRows (by positivity)).mp hh
    refine (mem_elementRows hR).mpr ⟨hh0, hhN.trans ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ absNorm (b * e) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hg.1.1)
    have : (absNorm e : ℝ) ≤ (absNorm (b * e) : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hR
  have h2 : ∑ u ∈ U, ∑ h ∈ rows u, ∑ ξ, ∑ η, G u h ξ η =
      ∑ u ∈ B ×ˢ (B ×ˢ (B ×ˢ (B ×ˢ B))), ∑ h ∈ elementRows R, ∑ ξ, ∑ η,
        if u ∈ U ∧ h ∈ rows u then G u h ξ η else 0 := by
    symm
    rw [← Finset.sum_subset hUsub fun u _ hu => by simp [hu]]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Finset.sum_subset (hrows u hu) fun h _ hh => by simp [hh]]
    refine Finset.sum_congr rfl fun h hh => ?_
    simp [hu, hh]
  rw [h1, h2]
  simp only [Finset.sum_product]
  rw [← Finset.sum_filter_of_ne (p := Starred)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb := (Finset.mem_filter.mp hb).2
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun v _ => ?_
    rw [sum_comm₂₃]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun ξ _ =>
      Finset.sum_congr rfl fun η _ => ?_
    have hF := dyadicNorm_pos (e, v, h)
    have hNb := natCast_absNorm_pos hb.1.1
    have hX : 0 < blockLength D' b (e, v, h) := by unfold blockLength; positivity
    have hXF : blockLength D' b (e, v, h) * dyadicNorm (e, v, h) = D' / absNorm b := by
      unfold blockLength; field_simp
    convert sum_moebiusSplit_cols_eq P ξ η h
      (α ξ η * splitRowWeight ξ η Y (blockLength D' b (e, v, h)) (e, v, h)) hb hX hF hR₀ hXF
      (fun hev => dyadicNorm_le hev) hWz using 3
  · intro b _ hne
    by_contra hb
    refine hne (Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun v _ =>
      Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ =>
        Finset.sum_eq_zero fun h _ => Finset.sum_eq_zero fun ξ _ =>
          Finset.sum_eq_zero fun η _ => ?_)
    simp only [ite_eq_right_iff]
    rintro ⟨hu, -⟩
    exact absurd ((mem_moebiusSplitsLe hD'.le).mp hu).2.1.of_mul_left hb

/-! ### The bound on the main dual frequencies -/

lemma norm_rayCharacter_le_one (ξ : RayCharacter) (x : Q₇₂) : ‖ξ x‖ ≤ 1 := by
  classical
  by_cases hx : IsUnit x
  · let := Ring.HasFiniteQuotients.finiteQuotient (I := span {(72 : 𝓔)}) (by simp)
    have hpow := pow_card_eq_one' (x := hx.unit)
    have hχ := congrArg (fun u : Q₇₂ˣ => ξ (u : Q₇₂)) hpow
    simp only [Units.val_pow_eq_pow_val, hx.unit_spec, map_pow, Units.val_one, map_one] at hχ
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, Nat.card_pos, hχ⟩).norm_eq_one.le
  · simp [ξ.map_nonunit hx]

lemma norm_splitRowWeight_le (ξ η : RayCharacter) {Y X : ℝ} (hY : 0 ≤ Y) (hX : 0 ≤ X)
    {ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔} (hv : Starred ρ.2.1) :
    ‖splitRowWeight ξ η Y X ρ‖ ≤ Y / ((absNorm ρ.1 : ℝ) * absNorm ρ.2.1 * X) := by
  have ha := gaussCoefficientBound _ hv
  have hs := norm_sextic_le_one ρ.2.1 ρ.2.2
  have hξ := norm_rayCharacter_le_one ξ (Ideal.Quotient.mk _ (generator ρ.2.1))
  have hη := norm_rayCharacter_le_one η (Ideal.Quotient.mk _ (generator ρ.2.1))
  have hq : 0 ≤ Y / ((absNorm ρ.1 : ℝ) * absNorm ρ.2.1 * X) := by positivity
  unfold splitRowWeight
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq, RCLike.norm_conj]
  calc _ ≤ 1 * 1 * (Y / ((absNorm ρ.1 : ℝ) * absNorm ρ.2.1 * X)) * (1 * 1 * 1 * 1 * (1 * 1)) := by
        gcongr <;> exact norm_idealMoebius_le _
    _ = _ := by ring

lemma elementNorm_generator_mul (e : Ideal 𝓔) (h : 𝓔) :
    elementNorm (generator e * h) = absNorm e * elementNorm h := by
  unfold elementNorm
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, span_generator]

/-- Reordering the rows `(e, v, h)` of `dualMainSum_eq` past the ray characters, as one sum over
the rows that satisfy `p`. -/
lemma sum_rows_comm {ι κ σ : Type*} [Fintype σ] (B : Finset ι) (E : Finset κ)
    (p : ι → ι → κ → Prop) [∀ e v h, Decidable (p e v h)] (f : ι → ι → κ → σ → σ → ℂ) :
    ∑ e ∈ B, ∑ v ∈ B, ∑ h ∈ E, ∑ ξ, ∑ η, (if p e v h then f e v h ξ η else 0) =
      ∑ ξ, ∑ η, ∑ ρ ∈ (B ×ˢ (B ×ˢ E)).filter (fun ρ => p ρ.1 ρ.2.1 ρ.2.2),
        f ρ.1 ρ.2.1 ρ.2.2 ξ η := by
  simp only [Finset.sum_filter, Finset.sum_product]
  exact (sum_comm₂₃ _ _ _ _ _ _).symm

/-- The main dual frequencies at `Y = D^(1+θ)` and `R = D^(2+θ/4) / Y` are `O(D^(2+θ+ε))`, for
`W = W'(· / R')` with `W'` vanishing beyond `1` and a cut `χ` equal to `e^{-s/2}` wherever `W'`
meets two columns dilated by `β ∈ [1, 2)`. -/
theorem exists_norm_dualMainSum_le (hpg : PairedGaussIdentities) (hgap : GapEstimate)
    {W W' χ : ℝ → ℂ} (hW' : ContDiff ℝ ∞ W') (hW'c : HasCompactSupport W')
    (hW'0 : tsupport W' ⊆ Set.Ioi 0) (hW'1 : ∀ y, W' y ≠ 0 → y ≤ 1) {R' : ℝ} (hR' : 1 ≤ R')
    (hW : ∀ x, W x = W' (x / R')) (P : SchwartzMap ℝ ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ)
    (hχW : ∀ β y₁ y₂ : ℝ, 1 ≤ β → β < 2 → 0 < y₁ → 0 < y₂ →
      conj (W' (β * y₁)) * W' (β * y₂) ≠ 0 →
        χ (Real.log y₁ + Real.log y₂) = (Real.exp (-((Real.log y₁ + Real.log y₂) / 2)) : ℂ))
    (A : Q₇₂ → Q₇₂ → ℂ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (0 : ℝ), ∀ D : ℝ, 2 ≤ D →
      ‖dualMainSum P A W D (D ^ (1 + θ)) (D ^ (2 + θ / 4) / D ^ (1 + θ))‖ ≤
        C * D ^ (2 + θ + ε) := by
  classical
  have hmul : ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      gaussCoefficient (b * c) = gaussCoefficient b * gaussCoefficient c *
        sextic c (generator b) ^ 4 := by
    obtain ⟨_, _, h⟩ := hpg
    exact fun b c hb hc hbc => (h b c hb hc hbc).2.2
  obtain ⟨α, hα⟩ := exists_rayCharacter_expansion A
  set δ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨R₁, CB, hCB, hblock⟩ := exists_block_le hpg hgap hW' hW'c hW'0 P hχ hχc
    (half_pos hθ) hδ0
  obtain ⟨CH, hCH, hharm⟩ := exists_sum_inv_absNorm_le hδ0
  set R₀ := max R₁ 1
  set Sα := ∑ ξ, ∑ η, ‖α ξ η‖ with hSα
  have hSα0 : 0 ≤ Sα := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set L := 1 + 1 / (δ * Real.log 2) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨L * Sα * CB * CH * R' ^ (1 + 3 * δ), by positivity, fun D hD => ?_⟩
  set D' := R' * D with hD'
  set Y := D ^ (1 + θ) with hY
  set R := D ^ (2 + θ / 4) / D ^ (1 + θ) with hR
  have hD0 : 0 < D := by linarith
  have hDD' : D ≤ D' := le_mul_of_one_le_left hD0.le hR'
  have hD'2 : 2 ≤ D' := hD.trans hDD'
  have hD'0 : 0 < D' := by linarith
  have hY0 : 0 < Y := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hR₀ : 1 ≤ R₀ := le_max_right _ _
  have hRle : R ≤ D' * D' ^ (-(θ / 2)) := by
    rw [← Real.rpow_one_add' hD'0.le (by linarith), ← sub_eq_add_neg, hR, ← Real.rpow_sub hD0]
    calc D ^ (2 + θ / 4 - (1 + θ)) ≤ D ^ (1 - θ / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ D' ^ (1 - θ / 2) := Real.rpow_le_rpow hD0.le hDD' (by linarith)
  set J := Nat.log 2 ⌊D'⌋₊ with hJdef
  have h2J : (2 : ℝ) ^ J ≤ D' := by
    have := Nat.pow_log_le_self 2 (Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ D')).ne'
    exact (by exact_mod_cast this : ((2 ^ J : ℕ) : ℝ) ≤ ⌊D'⌋₊).trans' (by push_cast; rfl)
      |>.trans (Nat.floor_le hD'0.le)
  have hJ : ((J + 1 : ℕ) : ℝ) ≤ L * D' ^ δ := by
    have hlog : (J : ℝ) * Real.log 2 ≤ D' ^ δ / δ := by
      rw [← Real.log_pow]
      exact (Real.log_le_log (by positivity) h2J).trans (Real.log_le_rpow_div hD'0.le hδ0)
    have h1 : 1 ≤ D' ^ δ := Real.one_le_rpow (by linarith) hδ0.le
    have h3 := (le_div_iff₀ hδ0).mp hlog
    have h4 : (J : ℝ) ≤ D' ^ δ / (δ * Real.log 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [show (J : ℝ) * (δ * Real.log 2) = J * Real.log 2 * δ by ring]
    have h5 : L * D' ^ δ = D' ^ δ + D' ^ δ / (δ * Real.log 2) := by rw [hL]; ring
    push_cast
    linarith
  have hfib : ∀ b ∈ (idealsLe D').filter Starred, ∀ ξ η : RayCharacter,
      ∀ j ∈ Finset.range (J + 1),
      ‖∑ ρ ∈ ((idealsLe D' ×ˢ (idealsLe D' ×ˢ elementRows R)).filter fun ρ =>
          Starred (b * ρ.1 * ρ.2.1) ∧ (absNorm (b * ρ.1 * ρ.2.1) : ℝ) ≤ D' ∧
            ρ.2.2 ∈ elementRows (R * absNorm ρ.1 / (absNorm (b * ρ.1) : ℝ) ^ 2)).filter
          (fun ρ => Nat.log 2 (absNorm (ρ.1 * ρ.2.1)) = j),
        α ξ η * splitRowWeight ξ η Y (blockLength D' b ρ) ρ *
          ∑ m₁ ∈ blockColumns R₀ (blockLength D' b ρ),
            ∑ m₂ ∈ blockColumns R₀ (blockLength D' b ρ),
              blockTerm P χ W' ξ η b Y (blockLength D' b ρ) (dyadicNorm ρ) ρ m₁ m₂‖ ≤
        ‖α ξ η‖ * (Y * absNorm b / D') * (CB * D' ^ δ * (D' / absNorm b) ^ 2) := by
    intro b hb ξ η j hj
    obtain ⟨hbD, hbs⟩ := Finset.mem_filter.mp hb
    have hNb := natCast_absNorm_pos hbs.1.1
    have hNb1 : (1 : ℝ) ≤ absNorm b := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hbs.1.1)
    have hbD' : (absNorm b : ℝ) ≤ D' := (mem_idealsLe hD'0.le).mp hbD
    set F : ℝ := 2 ^ j with hFdef
    set X := D' / (absNorm b * F) with hXdef
    have hF1 : (1 : ℝ) ≤ F := one_le_pow₀ one_le_two
    have hF0 : 0 < F := by positivity
    have hX : 0 < X := by positivity
    have hXF : X * F = D' / absNorm b := by rw [hXdef]; field_simp
    have hFD : F ≤ D' :=
      (pow_le_pow_right₀ one_le_two (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).trans h2J
    set T := ((idealsLe D' ×ˢ (idealsLe D' ×ˢ elementRows R)).filter fun ρ =>
          Starred (b * ρ.1 * ρ.2.1) ∧ (absNorm (b * ρ.1 * ρ.2.1) : ℝ) ≤ D' ∧
            ρ.2.2 ∈ elementRows (R * absNorm ρ.1 / (absNorm (b * ρ.1) : ℝ) ^ 2)).filter
          (fun ρ => Nat.log 2 (absNorm (ρ.1 * ρ.2.1)) = j) with hT
    have hmem : ∀ ρ ∈ T, Starred (b * (ρ.1 * ρ.2.1)) ∧
        ρ.2.2 ∈ elementRows (R * absNorm ρ.1 / (absNorm (b * ρ.1) : ℝ) ^ 2) ∧
        dyadicNorm ρ = F := fun ρ hρ => by
      obtain ⟨hρ', hlogj⟩ := Finset.mem_filter.mp hρ
      obtain ⟨-, hst, -, hρh⟩ := Finset.mem_filter.mp hρ'
      refine ⟨by rwa [← mul_assoc], hρh, ?_⟩
      unfold dyadicNorm
      rw [hlogj]
    have hsrw : ∀ ρ ∈ T, ‖splitRowWeight ξ η Y X ρ‖ ≤ Y * absNorm b / D' := fun ρ hρ => by
      obtain ⟨hst, -, hdy⟩ := hmem ρ hρ
      have hev : ρ.1 * ρ.2.1 ≠ ⊥ := hst.of_mul_right.1.1
      have hle := dyadicNorm_le hev
      rw [hdy] at hle
      refine (norm_splitRowWeight_le ξ η hY0.le hX.le hst.of_mul_right.of_mul_right).trans ?_
      rw [← Nat.cast_mul, ← map_mul absNorm ρ.1 ρ.2.1]
      calc Y / ((absNorm (ρ.1 * ρ.2.1) : ℝ) * X) ≤ Y / (F * X) := by gcongr
        _ = Y * absNorm b / D' := by rw [hXdef]; field_simp
    have hK : R / (absNorm b : ℝ) ^ 2 ≤ X * F * D' ^ (-(θ / 2)) := by
      rw [hXF]
      calc R / (absNorm b : ℝ) ^ 2 ≤ R / absNorm b :=
            div_le_div_of_nonneg_left hR0 hNb (by nlinarith)
        _ ≤ D' * D' ^ (-(θ / 2)) / absNorm b := by gcongr
        _ = D' / absNorm b * D' ^ (-(θ / 2)) := by ring
    have hrow : ∀ ρ ∈ T, ρ.1 ≠ ⊥ ∧ Starred (ρ.1 * ρ.2.1) ∧
        F ≤ (absNorm (ρ.1 * ρ.2.1) : ℝ) ∧ (absNorm (ρ.1 * ρ.2.1) : ℝ) < 2 * F ∧
        generator ρ.1 * ρ.2.2 ∈ elementRows (R / (absNorm b : ℝ) ^ 2) := fun ρ hρ => by
      obtain ⟨hst, hρh, hdy⟩ := hmem ρ hρ
      have hev : ρ.1 * ρ.2.1 ≠ ⊥ := hst.of_mul_right.1.1
      have he : ρ.1 ≠ ⊥ := left_ne_zero_of_mul hev
      have hNe := natCast_absNorm_pos he
      obtain ⟨hh0, hh⟩ := (mem_elementRows (by positivity)).mp hρh
      refine ⟨he, hst.of_mul_right, hdy ▸ dyadicNorm_le hev, hdy ▸ lt_two_mul_dyadicNorm ρ,
        (mem_elementRows (by positivity)).mpr ⟨mul_ne_zero (fun h0 => he ?_) hh0, ?_⟩⟩
      · rw [← span_generator ρ.1, h0, Ideal.span_singleton_eq_bot.mpr rfl]
      · rw [elementNorm_generator_mul, Nat.cast_mul]
        rw [map_mul absNorm b ρ.1, Nat.cast_mul] at hh
        calc (absNorm ρ.1 : ℝ) * elementNorm ρ.2.2 ≤
              absNorm ρ.1 * (R * absNorm ρ.1 / ((absNorm b : ℝ) * absNorm ρ.1) ^ 2) := by
              gcongr
          _ = R / (absNorm b : ℝ) ^ 2 := by field_simp
    calc _ = ‖∑ ρ ∈ T, α ξ η * splitRowWeight ξ η Y X ρ *
          ∑ m₁ ∈ blockColumns R₀ X, ∑ m₂ ∈ blockColumns R₀ X,
            blockTerm P χ W' ξ η b Y X F ρ m₁ m₂‖ := by
          refine congrArg norm (Finset.sum_congr rfl fun ρ hρ => ?_)
          have hdy := (hmem ρ hρ).2.2
          have hbl : blockLength D' b ρ = X := by unfold blockLength; rw [hdy]
          rw [hbl, hdy]
      _ ≤ ∑ ρ ∈ T, ‖α ξ η‖ * (Y * absNorm b / D') *
          ‖∑ m₁ ∈ blockColumns R₀ X, ∑ m₂ ∈ blockColumns R₀ X,
            blockTerm P χ W' ξ η b Y X F ρ m₁ m₂‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
          rw [norm_mul, norm_mul]
          gcongr
          exact hsrw ρ hρ
      _ = ‖α ξ η‖ * (Y * absNorm b / D') * ∑ ρ ∈ T,
          ‖∑ m₁ ∈ blockColumns R₀ X, ∑ m₂ ∈ blockColumns R₀ X,
            blockTerm P χ W' ξ η b Y X F ρ m₁ m₂‖ := by rw [Finset.mul_sum]
      _ ≤ ‖α ξ η‖ * (Y * absNorm b / D') * (CB * D' ^ δ * (X * F) ^ 2) := by
          have hXFD : X * F ≤ D' := by rw [hXF]; exact div_le_self hD'0.le hNb1
          have hB := hblock R₀ D' (R / (absNorm b : ℝ) ^ 2) X F ξ η b T (rowShift Y X)
            (le_max_left _ _) hD'2 hX hF1 hFD hXFD hK hbs hbD' hrow
          gcongr
          exact hB
      _ = _ := by rw [hXF]
  rw [dualMainSum_eq residueMultiplicative hmul hα P hD0 hD'0 (W' := W') (χ := χ)
    (fun x => by rw [hW, div_div, mul_comm D R']) (fun x hx => (div_le_one hD'0).mp (hW'1 _ hx))
    hχW hY0 hR0 hR₀]
  simp only [sum_rows_comm, Prod.mk.eta]
  calc _ ≤ ∑ b ∈ (idealsLe D').filter Starred, ∑ ξ, ∑ η, ∑ j ∈ Finset.range (J + 1),
        ‖α ξ η‖ * (Y * absNorm b / D') * (CB * D' ^ δ * (D' / absNorm b) ^ 2) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η _ => ?_)
        have hmaps : ∀ ρ ∈ (idealsLe D' ×ˢ (idealsLe D' ×ˢ elementRows R)).filter (fun ρ =>
            Starred (b * ρ.1 * ρ.2.1) ∧ (absNorm (b * ρ.1 * ρ.2.1) : ℝ) ≤ D' ∧
              ρ.2.2 ∈ elementRows (R * absNorm ρ.1 / (absNorm (b * ρ.1) : ℝ) ^ 2)),
            Nat.log 2 (absNorm (ρ.1 * ρ.2.1)) ∈ Finset.range (J + 1) := by
          intro ρ hρ
          obtain ⟨-, hst, hND, -⟩ := Finset.mem_filter.mp hρ
          rw [mul_assoc] at hst hND
          have hle := (absNorm_le_absNorm_mul hst.1.1).2.trans hND
          refine Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right ?_))
          exact Nat.le_floor hle
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hfib b hb ξ η j hj)
    _ = ∑ b ∈ (idealsLe D').filter Starred,
        ((J + 1 : ℕ) : ℝ) * Sα * (CB * D' ^ δ * Y * D') * (absNorm b : ℝ)⁻¹ := by
      refine Finset.sum_congr rfl fun b hb => ?_
      have hNb := natCast_absNorm_pos (Finset.mem_filter.mp hb).2.1.1
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hSα, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
      push_cast
      field_simp
    _ ≤ ((J + 1 : ℕ) : ℝ) * Sα * (CB * D' ^ δ * Y * D') * (CH * D' ^ δ) := by
      rw [← Finset.mul_sum]
      gcongr
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => by positivity).trans (hharm D' (by linarith))
    _ ≤ (L * D' ^ δ) * Sα * (CB * D' ^ δ * Y * D') * (CH * D' ^ δ) := by gcongr
    _ = L * Sα * CB * CH * (D' ^ δ * D' ^ δ * D' ^ δ * D') * Y := by ring
    _ = L * Sα * CB * CH * R' ^ (1 + 3 * δ) * D ^ (2 + θ + 3 * δ) := by
      rw [show D' ^ δ * D' ^ δ * D' ^ δ * D' = D' ^ (1 + 3 * δ) by
        rw [show 1 + 3 * δ = δ + δ + δ + 1 by ring, Real.rpow_add hD'0, Real.rpow_add hD'0,
          Real.rpow_add hD'0, Real.rpow_one],
        hD', Real.mul_rpow (by linarith) hD0.le, hY]
      have : D ^ (1 + 3 * δ) * D ^ (1 + θ) = D ^ (2 + θ + 3 * δ) := by
        rw [← Real.rpow_add hD0]; ring_nf
      rw [← this]
      ring
    _ ≤ L * Sα * CB * CH * R' ^ (1 + 3 * δ) * D ^ (2 + θ + ε) := by
      gcongr
      · linarith
      · linarith

/-- A smooth `W` with compact support in `(0, ∞)` vanishes outside some `[r₀, R]` with
`0 < r₀`. -/
lemma exists_support_Icc {W : ℝ → ℂ} (hWc : HasCompactSupport W)
    (hW0 : tsupport W ⊆ Set.Ioi 0) :
    ∃ r₀ > (0 : ℝ), ∃ R : ℝ, ∀ y, W y ≠ 0 → r₀ ≤ y ∧ y ≤ R := by
  obtain ⟨R, hR⟩ := hWc.isCompact.bddAbove
  rcases (tsupport W).eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, R, fun y hy => ?_⟩
    have := subset_tsupport W hy
    rw [h] at this
    exact absurd this (Set.notMem_empty y)
  · obtain ⟨x, hx, hmin⟩ := hWc.isCompact.exists_isMinOn h continuousOn_id
    refine ⟨x, hW0 hx, R, fun y hy => ⟨hmin (subset_tsupport W hy), hR (subset_tsupport W hy)⟩⟩

/-- `GapEstimate` bounds the nonzero frequencies of the full square. -/
theorem dualTailEstimate_of_gapEstimate (hpg : PairedGaussIdentities) (hgap : GapEstimate) :
    DualTailEstimate rowMajorant := by
  intro A W hWs hWc hW0 θ hθ hθ1 ε hε
  obtain ⟨r₀, hr₀, RW, hRW⟩ := exists_support_Icc hWc hW0
  set R' := max RW 1 with hR'def
  have hR' : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 < R' := by linarith
  set W' : ℝ → ℂ := fun y => W (R' * y) with hW'def
  have hW' : ContDiff ℝ ∞ W' := hWs.comp (contDiff_const.mul contDiff_id)
  have hW'c : HasCompactSupport W' := by
    simpa only [smul_eq_mul] using hWc.comp_smul hR'0.ne'
  have hW'r : ∀ y, W' y ≠ 0 → r₀ / R' ≤ y ∧ y ≤ 1 := fun y hy => by
    obtain ⟨h₁, h₂⟩ := hRW _ hy
    refine ⟨(div_le_iff₀ hR'0).mpr (by linarith [mul_comm R' y]), ?_⟩
    have : R' * y ≤ R' * 1 := by linarith [le_max_left RW 1]
    exact le_of_mul_le_mul_left this hR'0
  have hW'0 : tsupport W' ⊆ Set.Ioi 0 := by
    refine (closure_minimal (fun y hy => (hW'r y hy).1) isClosed_Ici).trans fun y hy => ?_
    exact lt_of_lt_of_le (by positivity) (Set.mem_Ici.mp hy)
  have hW : ∀ x, W x = W' (x / R') := fun x => by
    simp only [hW'def, mul_div_cancel₀ _ hR'0.ne']
  obtain ⟨χ, hχ, hχc, hχe⟩ := exists_cutoff_exp (2 * Real.log (r₀ / (2 * R'))) 0
  have hχW : ∀ β y₁ y₂ : ℝ, 1 ≤ β → β < 2 → 0 < y₁ → 0 < y₂ →
      conj (W' (β * y₁)) * W' (β * y₂) ≠ 0 →
        χ (Real.log y₁ + Real.log y₂) =
          (Real.exp (-((Real.log y₁ + Real.log y₂) / 2)) : ℂ) := by
    intro β y₁ y₂ hβ hβ2 hy₁ hy₂ hne
    have hb : ∀ y, 0 < y → W' (β * y) ≠ 0 →
        Real.log (r₀ / (2 * R')) ≤ Real.log y ∧ Real.log y ≤ 0 := fun y hy hW' => by
      obtain ⟨h₁, h₂⟩ := hW'r _ hW'
      refine ⟨Real.log_le_log (by positivity) ?_, Real.log_nonpos hy.le ?_⟩
      · rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hR'0] at h₁
        nlinarith
      · nlinarith
    obtain ⟨h₁, h₂⟩ := hb y₁ hy₁ (fun h => hne (by rw [h, map_zero, zero_mul]))
    obtain ⟨h₃, h₄⟩ := hb y₂ hy₂ (fun h => hne (by rw [h, mul_zero]))
    exact hχe _ ⟨by linarith, by linarith⟩
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_dualTailSum_sub_le rowMajorant A hWs.continuous hWc
    hθ.le (by positivity : (0 : ℝ) < θ / 4)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_dualMainSum_le hpg hgap hW' hW'c hW'0
    (fun y hy => (hW'r y hy).2) hR' hW rowMajorant hχ hχc hχW A hθ (by linarith) hε
  refine ⟨C₁ + C₂, by positivity, fun D hD => ?_⟩
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have hDθ : D ^ (2 + θ) ≤ D ^ (2 + θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
  calc ‖dualTailSum rowMajorant A W D (D ^ (1 + θ))‖ ≤
        ‖dualTailSum rowMajorant A W D (D ^ (1 + θ)) - dualMainSum rowMajorant A W D
            (D ^ (1 + θ)) (D ^ (2 + θ / 4) / D ^ (1 + θ))‖ +
          ‖dualMainSum rowMajorant A W D (D ^ (1 + θ)) (D ^ (2 + θ / 4) / D ^ (1 + θ))‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ C₁ * D ^ (2 + θ + ε) + C₂ * D ^ (2 + θ + ε) := by
        gcongr
        · exact (h₁ D hD).trans (by gcongr)
        · exact h₂ D hD
    _ = (C₁ + C₂) * D ^ (2 + θ + ε) := by ring

/-- The full mean square of the Möbius rows from `PairedGaussIdentities` and `GapEstimate`. -/
theorem fullRowEstimate_of_gapEstimate (hpg : PairedGaussIdentities) (hgap : GapEstimate) :
    FullRowEstimate :=
  fullRowEstimate_of_dualTail hpg (dualTailEstimate_of_gapEstimate hpg hgap)

end Masullo.QRH.MeanSquare
