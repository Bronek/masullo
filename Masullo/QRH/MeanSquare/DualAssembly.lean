import Masullo.QRH.MeanSquare.DualTail

/-!
# Assembly of the nonzero dual frequencies

`GapEstimate` gives `DualTailEstimate rowMajorant`.

* `mainSplitTerm_eq`: a main dual term of a Möbius split `(b, e, v, m₁, m₂)` at the row `h`
  is a combination over ray characters of a row weight `splitRowWeight` and a block summand
  `blockTerm` at `ρ = (e, v, h)`.
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

end Masullo.QRH.MeanSquare
