import Masullo.QRH.MeanSquare.OffDiagonal
import Masullo.QRH.MeanSquare.GaussNorm
import Masullo.QRH.MeanSquare.Divisors

/-!
# The nonzero dual frequencies

Steps toward `DualTailEstimate rowMajorant` from `GapEstimate`.

* `exists_rayCharacter_expansion`: a function on pairs of residues modulo `72` is, on pairs of
  units, a combination of `ξ(x) conj η(y)` over ray characters `ξ, η`.
* `exists_dilated_separated_le₂`: the separation of dilated kernels for a pair of coefficient
  families, by four-term polarization.
* `exists_norm_tsum_far_le`: the dual frequencies beyond a radius contribute a negative power
  of the radius.
* `exists_norm_dualExclusionTail_sub_le`: `dualExclusionTail` is its main dual frequencies
  `dualExclusionMain` up to such a power.
* `exists_norm_dualTailSum_sub_le`: summed over the gcd splits, the far dual frequencies at
  radius `D^(2+η)/Y` cost `O(D^(2+θ))`, leaving `dualMainSum`.
* `exists_dualMeanSquareCoprime_le`: `GapEstimate` for columns coprime to `b`, with no lower
  bounds on `K` and `X`.
* `exists_sum_rows_le`: the rows `(e, v, h)` of a block cover each pair `(f, k) = (e v, e° h)`
  at most `τ(f) ≪ (N f)^s` times.
* `exists_block_le`: a block of the main dual terms with fixed `b`, ray characters `ξ, η` and
  dyadic twist norm `F` is `O(D^ε (XF)²)`.
* `mainSummand_eq`: after the Möbius substitution `c = v m₁`, `b = v m₂`, the arithmetic factor
  of a main dual term factors into a row weight and twisted columns `m₁`, `m₂`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open MeasureTheory Set
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-! ### Ray characters separate units -/

instance : Finite Q₇₂ :=
  (Ideal.absNorm_ne_zero_iff _).mp (Ideal.absNorm_eq_zero_iff.not.mpr
    (span_singleton_eq_bot.not.mpr (by norm_num)))

instance : Fintype Q₇₂ := Fintype.ofFinite _

instance : Fintype RayCharacter := Fintype.ofFinite _

lemma sum_rayCharacter_apply (u : Q₇₂ˣ) : open Classical in
    ∑ ξ : RayCharacter, ξ u = if u = 1 then (Fintype.card RayCharacter : ℂ) else 0 := by
  classical
  split_ifs with hu
  · simp [hu]
  · obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q₇₂ ℂ
      (a := (u : Q₇₂)) (by simpa [Units.val_eq_one] using hu)
    have h : ∑ ξ : RayCharacter, ξ u = χ u * ∑ ξ : RayCharacter, ξ u := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft χ) (fun ξ : RayCharacter => χ u * ξ u)
        (fun ξ : RayCharacter => ξ u) fun ξ => by simp).symm
    have : (1 - χ u) * ∑ ξ : RayCharacter, ξ u = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hχ))

lemma sum_rayCharacter_mul_conj (u v : Q₇₂ˣ) : open Classical in
    ∑ ξ : RayCharacter, ξ u * conj (ξ v) =
      if u = v then (Fintype.card RayCharacter : ℂ) else 0 := by
  classical
  have h : ∀ ξ : RayCharacter, ξ u * conj (ξ v) = ξ ↑(u * v⁻¹) := fun ξ => by
    rw [← RCLike.star_def, MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
      Units.val_mul, map_mul]
  simp_rw [h, sum_rayCharacter_apply, mul_inv_eq_one]

/-- A function on pairs of residues is, on pairs of units, a combination of products of ray
characters. -/
theorem exists_rayCharacter_expansion (A : Q₇₂ → Q₇₂ → ℂ) :
    ∃ α : RayCharacter → RayCharacter → ℂ, ∀ x y : Q₇₂, IsUnit x → IsUnit y →
      A x y = ∑ ξ : RayCharacter, ∑ η : RayCharacter, α ξ η * ξ x * conj (η y) := by
  classical
  set N : ℂ := (Fintype.card RayCharacter : ℂ)
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun ξ η => (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ * conj (ξ x₀) * η y₀) / N ^ 2,
    fun x y hx hy => ?_⟩
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have hexp : ∑ ξ : RayCharacter, ∑ η : RayCharacter,
      (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ * conj (ξ x₀) * η y₀) / N ^ 2 * ξ u * conj (η v) =
      (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ *
        (∑ ξ : RayCharacter, ξ u * conj (ξ x₀)) *
        (∑ η : RayCharacter, η y₀ * conj (η v))) / N ^ 2 := by
    have h4 : ∀ f : RayCharacter → RayCharacter → Q₇₂ˣ → Q₇₂ˣ → ℂ,
        ∑ ξ, ∑ η, ∑ x, ∑ y, f ξ η x y = ∑ x, ∑ y, ∑ ξ, ∑ η, f ξ η x y := by
      intro f
      calc _ = ∑ ξ, ∑ x, ∑ η, ∑ y, f ξ η x y := Finset.sum_congr rfl fun ξ _ => Finset.sum_comm
        _ = ∑ ξ, ∑ x, ∑ y, ∑ η, f ξ η x y := Finset.sum_congr rfl fun ξ _ =>
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ x, ∑ ξ, ∑ y, ∑ η, f ξ η x y := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine (h4 _).trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ξ _ => ?_))
    ring
  rw [hexp]
  simp_rw [sum_rayCharacter_mul_conj]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  field_simp
  rfl

/-- The primary generator of an ideal prime to six is a unit modulo `72`. -/
lemma isUnit_mk_generator {n : Ideal 𝓔} (hn : AwayFromSix n) :
    IsUnit (Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n)) := by
  rw [isUnit_mk_iff_coprime_span, span_generator]
  have h3 : IsCoprime (span {(6 : 𝓔)} ^ 3) n := (hn.2.symm.pow_left)
  rw [span_singleton_pow, Ideal.isCoprime_iff_sup_eq] at h3
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← h3]
  refine sup_le_sup_right (span_singleton_le_span_singleton.mpr ⟨3, by norm_num⟩) _

/-! ### Polarized separation -/

/-- Four-term polarization: `4 a conj b' = ∑_ω ω (a + ω b) conj (a' + ω b')` over the fourth
roots of unity `ω`. -/
lemma polarization (a b a' b' : ℂ) :
    4 * (a * conj b') = ∑ k : Fin 4, ![1, Complex.I, -1, -Complex.I] k *
      ((a + ![1, Complex.I, -1, -Complex.I] k * b) *
        conj (a' + ![1, Complex.I, -1, -Complex.I] k * b')) := by
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, map_mul, map_neg,
    Complex.conj_I, map_one]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  nlinarith [norm_add_le a b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]

/-- `exists_dilated_separated_le` for two coefficient families `c₁, c₂` with mean squares at
most `M₁, M₂`. -/
theorem exists_dilated_separated_le₂ {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) {L : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    ∃ (I : TestInterval) (C : ℝ), 0 ≤ C ∧
      ∀ {R N : Type} (rows : Finset R) (cols : Finset N) (c₁ c₂ : R → N → ℂ) (x : N → ℝ)
        (ℓ : R → ℝ) (ψ : R → ℝ → ℂ) {A M₁ M₂ : ℝ}, 0 ≤ A → 0 ≤ M₁ → 0 ≤ M₂ →
        (∀ n ∈ cols, 0 < x n) → (∀ ρ ∈ rows, ℓ ρ ∈ Icc 0 L) →
        (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₁ ρ n * U (x n)‖ ^ 2 ≤ M₁) →
        (∀ U, UnitTest I j U → ∑ ρ ∈ rows, ‖∑ n ∈ cols, c₂ ρ n * U (x n)‖ ^ 2 ≤ M₂) →
        (∀ ρ ∈ rows, ContDiff ℝ (2 * j + 2) (ψ ρ)) →
        (∀ ρ ∈ rows, ∀ k ≤ 2 * j + 2, Integrable (iteratedDeriv k (ψ ρ))) →
        (∀ ρ ∈ rows, ∫ v, ‖ψ ρ v‖ ≤ A) →
        (∀ ρ ∈ rows, ∫ v, ‖iteratedDeriv (2 * j + 2) (ψ ρ) v‖ ≤ A) →
        ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) *
          (w (ℓ ρ + Real.log (x n₁)) * conj (w (ℓ ρ + Real.log (x n₂))) *
            ψ ρ (Real.log (x n₁) + Real.log (x n₂)))‖ ≤ C * A * (M₁ + M₂) := by
  obtain ⟨I, C, hC, h⟩ := exists_dilated_separated_le hw hwc hL j
  refine ⟨I, 2 * C, by positivity, fun {R N} rows cols c₁ c₂ x ℓ ψ A M₁ M₂ hA hM₁ hM₂ hx hℓ
    h₁ h₂ hψ hψi hψA hψA' => ?_⟩
  set u : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I] with hu_def
  have hu : ∀ k, ‖u k‖ = 1 := by intro k; fin_cases k <;> simp [u]
  set K : R → N → N → ℂ := fun ρ n₁ n₂ => w (ℓ ρ + Real.log (x n₁)) *
    conj (w (ℓ ρ + Real.log (x n₂))) * ψ ρ (Real.log (x n₁) + Real.log (x n₂)) with hK
  set d : Fin 4 → R → N → ℂ := fun k ρ n => c₁ ρ n + u k * c₂ ρ n
  have hd : ∀ k, ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) *
      K ρ n₁ n₂‖ ≤ C * A * (2 * M₁ + 2 * M₂) := by
    intro k
    refine h rows cols (d k) x ℓ ψ hA (by positivity) hx hℓ (fun U hU => ?_) hψ hψi hψA hψA'
    calc ∑ ρ ∈ rows, ‖∑ n ∈ cols, d k ρ n * U (x n)‖ ^ 2
        ≤ ∑ ρ ∈ rows, (2 * ‖∑ n ∈ cols, c₁ ρ n * U (x n)‖ ^ 2 +
            2 * ‖∑ n ∈ cols, c₂ ρ n * U (x n)‖ ^ 2) := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          have : ∑ n ∈ cols, d k ρ n * U (x n) = ∑ n ∈ cols, c₁ ρ n * U (x n) +
              u k * ∑ n ∈ cols, c₂ ρ n * U (x n) := by
            simp only [d, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun n _ => by ring
          rw [this]
          refine (norm_add_sq_le_two _ _).trans ?_
          rw [norm_mul, hu, one_mul]
      _ ≤ 2 * M₁ + 2 * M₂ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          linarith [h₁ U hU, h₂ U hU]
  have hpt : ∀ ρ, ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂ =
      (1 / 4 : ℂ) * ∑ k : Fin 4, u k *
        ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂ := by
    intro ρ
    have e : ∀ n₁ n₂, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂ = (1 / 4 : ℂ) *
        ∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂) := by
      intro n₁ n₂
      rw [show (∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂)) =
          (∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂))) * K ρ n₁ n₂ by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring]
      rw [show (∑ k : Fin 4, u k * (d k ρ n₁ * conj (d k ρ n₂))) =
          4 * (c₁ ρ n₁ * conj (c₂ ρ n₂)) from
        (polarization (c₁ ρ n₁) (c₂ ρ n₁) (c₁ ρ n₂) (c₂ ρ n₂)).symm]
      ring
    simp only [e, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n₁ _ => ?_
    rw [Finset.sum_comm]
  calc ∑ ρ ∈ rows, ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, c₁ ρ n₁ * conj (c₂ ρ n₂) * K ρ n₁ n₂‖
      ≤ ∑ ρ ∈ rows, (1 / 4) * ∑ k : Fin 4,
          ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂‖ := by
        refine Finset.sum_le_sum fun ρ _ => ?_
        rw [hpt, norm_mul]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
        simp [hu]
    _ = (1 / 4) * ∑ k : Fin 4, ∑ ρ ∈ rows,
          ‖∑ n₁ ∈ cols, ∑ n₂ ∈ cols, d k ρ n₁ * conj (d k ρ n₂) * K ρ n₁ n₂‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (1 / 4) * ∑ _k : Fin 4, C * A * (2 * M₁ + 2 * M₂) := by
        gcongr with k; exact hd k
    _ = 2 * C * A * (M₁ + M₂) := by simp; ring

/-! ### Far dual frequencies -/

/-- The dual frequencies `h` with `N h > R` of a Gao-Zhao transform at scale `Q / Y` contribute
`O((Q / Y + 1) (Q / (Y R))^k)` for every `k`. -/
theorem exists_norm_tsum_far_le (P : SchwartzMap ℝ ℂ) (k : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ v : 𝓔 → ℂ, (∀ h, ‖v h‖ ≤ 1) → ∀ Y Q R : ℝ, 0 < Y → 0 < Q → 0 < R →
      Summable (fun h : 𝓔 => if R < (elementNorm h : ℝ) then
        v h * gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / Q)) else 0) ∧
      ‖∑' h : 𝓔, if R < (elementNorm h : ℝ) then
        v h * gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / Q)) else 0‖ ≤
        C * (Q / Y + 1) * (Q / (Y * R)) ^ k := by
  classical
  obtain ⟨B₁, hB₁⟩ := exists_pow_mul_norm_gaoZhaoTransform_le P (2 * (k + 0))
  obtain ⟨B₂, hB₂⟩ := exists_pow_mul_norm_gaoZhaoTransform_le P (2 * (k + 2))
  have hB₁0 : 0 ≤ B₁ := (by positivity : (0 : ℝ) ≤ 0 ^ (2 * (k + 0)) *
    ‖gaoZhaoTransform P 0‖).trans (hB₁ 0 le_rfl)
  have hB₂0 : 0 ≤ B₂ := (by positivity : (0 : ℝ) ≤ 0 ^ (2 * (k + 2)) *
    ‖gaoZhaoTransform P 0‖).trans (hB₂ 0 le_rfl)
  obtain ⟨C, hC, hsum⟩ := exists_sum_decay_le
  refine ⟨C * (B₁ + B₂), by positivity, fun v hv Y Q R hY hQ hR => ?_⟩
  set S₀ := Y * R / Q with hS₀
  have hS₀0 : 0 < S₀ := by positivity
  set φ : ℝ → ℝ := fun r => if S₀ < r then ‖gaoZhaoTransform P (Real.sqrt r)‖ else 0
  have hφ0 : ∀ r, 0 ≤ φ r := fun r => by simp only [φ]; split_ifs <;> positivity
  have hdec : ∀ (m : ℕ) (B : ℝ), 0 ≤ B → (∀ t : ℝ, 0 ≤ t → t ^ (2 * (k + m)) *
      ‖gaoZhaoTransform P t‖ ≤ B) → ∀ r, r ^ m * φ r ≤ B / S₀ ^ k := by
    intro m B hB0 hB r
    by_cases hr : S₀ < r
    · have hr0 : 0 < r := hS₀0.trans hr
      have h := hB (Real.sqrt r) (Real.sqrt_nonneg r)
      rw [pow_mul, Real.sq_sqrt hr0.le] at h
      simp only [φ, ite_eq_left hr]
      rw [le_div_iff₀ (by positivity)]
      calc r ^ m * ‖gaoZhaoTransform P (Real.sqrt r)‖ * S₀ ^ k
          ≤ r ^ m * ‖gaoZhaoTransform P (Real.sqrt r)‖ * r ^ k := by gcongr
        _ = r ^ (k + m) * ‖gaoZhaoTransform P (Real.sqrt r)‖ := by ring
        _ ≤ B := h
    · simp only [φ, ite_eq_right hr, mul_zero]; positivity
  have h0 : ∀ r, φ r ≤ B₁ / S₀ ^ k := fun r => by simpa using hdec 0 B₁ hB₁0 hB₁ r
  have h2 : ∀ r, r ^ 2 * φ r ≤ B₂ / S₀ ^ k := hdec 2 B₂ hB₂0 hB₂
  set Z := Q / Y with hZ
  have hZ0 : 0 < Z := by positivity
  have hfs : ∀ s : Finset 𝓔, ∑ h ∈ s, φ (elementNorm h / Z) ≤
      C * (B₁ / S₀ ^ k + B₂ / S₀ ^ k) * (Z + 1) :=
    hsum φ h0 (by positivity) h2 (by positivity) Z hZ0
  have hφs : Summable fun h : 𝓔 => φ (elementNorm h / Z) :=
    summable_of_sum_le (fun h => hφ0 _) hfs
  have hpt : ∀ h : 𝓔, ‖if R < (elementNorm h : ℝ) then
      v h * gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / Q)) else 0‖ ≤
        φ (elementNorm h / Z) := by
    intro h
    have hiff : R < (elementNorm h : ℝ) ↔ S₀ < elementNorm h / Z := by
      rw [hS₀, hZ, div_div_eq_mul_div, div_lt_div_iff_of_pos_right hQ, mul_comm Y,
        mul_lt_mul_iff_of_pos_right hY]
    have harg : Y * elementNorm h / Q = elementNorm h / Z := by rw [hZ]; field_simp
    simp only [φ, ← hiff, harg]
    split_ifs
    · rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hv h)
    · simp
  have hs : Summable (fun h : 𝓔 => if R < (elementNorm h : ℝ) then
      v h * gaoZhaoTransform P (Real.sqrt (Y * elementNorm h / Q)) else 0) :=
    Summable.of_norm_bounded hφs hpt
  refine ⟨hs, (norm_tsum_le_tsum_norm hs.norm).trans ?_⟩
  refine (hs.norm.tsum_le_tsum hpt hφs).trans ((hφs.tsum_le_of_sum_le hfs).trans_eq ?_)
  rw [hS₀, hZ, ← add_div, div_pow, div_eq_mul_inv, inv_div]
  ring

/-- The main dual frequencies of `dualExclusionTail`: for each `e ∣ g` the rows `h` with
`N h ≤ R Ne / Ng²`. -/
def dualExclusionMain (P : SchwartzMap ℝ ℂ) (Y R : ℝ) (b c g : Ideal 𝓔) : ℂ :=
  ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g},
    (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e.val : ℂ) *
      ∑ h ∈ elementRows (R * absNorm e.val / (absNorm g : ℝ) ^ 2),
        conj (pairCharacter b c h) * gaoZhaoTransform P
          (Real.sqrt (Y * elementNorm h / ((absNorm e.val : ℝ) * absNorm (b * c))))

/-- `dualExclusionTail` is `dualExclusionMain` up to `(Ng² N(bc) / (Y R))^k`. -/
theorem exists_norm_dualExclusionTail_sub_le (P : SchwartzMap ℝ ℂ) (k : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ b c g : Ideal 𝓔, AwayFromSix b → AwayFromSix c → Starred g →
      ∀ Y R : ℝ, 0 < Y → 0 < R →
        ‖dualExclusionTail P Y b c g - dualExclusionMain P Y R b c g‖ ≤
          C * 2 ^ Multiset.card (normalizedFactors g) *
            ((absNorm g : ℝ) * absNorm (b * c) / Y + 1) *
            ((absNorm g : ℝ) ^ 2 * absNorm (b * c) / (Y * R)) ^ k := by
  classical
  obtain ⟨C, hC, hfar⟩ := exists_norm_tsum_far_le P k
  refine ⟨C, hC, fun b c g hb hc hg Y R hY hR => ?_⟩
  have hbc : (0 : ℝ) < absNorm (b * c) := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr (mul_ne_zero hb.1 hc.1))
  have hg0 : (0 : ℝ) < absNorm g := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hg.2.ne_zero)
  set F : Ideal 𝓔 → ℂ := fun e =>
    (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e : ℂ) *
      ∑' h : 𝓔, if R * absNorm e / (absNorm g : ℝ) ^ 2 < (elementNorm h : ℝ) then
        conj (pairCharacter b c h) * gaoZhaoTransform P
          (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c)))) else 0
  have hdiff : dualExclusionTail P Y b c g - dualExclusionMain P Y R b c g =
      ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g}, F e := by
    set T₁ : Ideal 𝓔 → ℂ := fun e =>
      (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e : ℂ) *
        ∑' h : 𝓔, if h = 0 then 0 else conj (pairCharacter b c h) * gaoZhaoTransform P
          (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))
    set T₂ : Ideal 𝓔 → ℂ := fun e =>
      (idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e : ℂ) *
        ∑ h ∈ elementRows (R * absNorm e / (absNorm g : ℝ) ^ 2),
          conj (pairCharacter b c h) * gaoZhaoTransform P
            (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))
    rw [show dualExclusionTail P Y b c g = ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g}, T₁ e from rfl,
      show dualExclusionMain P Y R b c g = ∑ᶠ e : {e : Ideal 𝓔 // e ∣ g}, T₂ e from rfl,
      finsum_dvd_eq_sum hg.2 T₁, finsum_dvd_eq_sum hg.2 T₂, finsum_dvd_eq_sum hg.2 F,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    set e := ∏ P ∈ s, P
    have he : e ≠ ⊥ := Finset.prod_ne_zero_iff.mpr fun P hP => (prime_of_normalized_factor P
      (Multiset.mem_toFinset.mp (Finset.mem_powerset.mp hs hP))).ne_zero
    have he0 : (0 : ℝ) < absNorm e := by
      exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr he)
    set R' := R * absNorm e / (absNorm g : ℝ) ^ 2
    have hR' : 0 ≤ R' := by positivity
    set S : 𝓔 → ℂ := fun h => conj (pairCharacter b c h) * gaoZhaoTransform P
      (Real.sqrt (Y * elementNorm h / ((absNorm e : ℝ) * absNorm (b * c))))
    have hpt : ∀ h : 𝓔, (if h = 0 then 0 else S h) =
        (if h ∈ elementRows R' then S h else 0) +
          (if R' < (elementNorm h : ℝ) then S h else 0) := by
      intro h
      simp only [mem_elementRows hR']
      by_cases h0 : h = 0
      · subst h0
        have : (elementNorm (0 : 𝓔) : ℝ) = 0 := by simp [elementNorm]
        simp [this, not_lt.mpr hR']
      · by_cases hN : (elementNorm h : ℝ) ≤ R'
        · simp [h0, hN, not_lt.mpr hN]
        · simp [h0, hN, lt_of_not_ge hN]
    have hfin : Summable fun h : 𝓔 => if h ∈ elementRows R' then S h else 0 :=
      summable_of_ne_finset_zero (s := elementRows R') fun h hh => ite_eq_right hh
    have hfarS := (hfar (fun h => conj (pairCharacter b c h))
      (fun h => by rw [Complex.norm_conj]; exact norm_pairCharacter_le b c h) Y
      ((absNorm e : ℝ) * absNorm (b * c)) R' hY (by positivity) (by positivity)).1
    have htsum : (∑' h : 𝓔, if h = 0 then 0 else S h) =
        ∑ h ∈ elementRows R', S h + ∑' h : 𝓔, if R' < (elementNorm h : ℝ) then S h else 0 := by
      rw [tsum_congr hpt, hfin.tsum_add hfarS, tsum_eq_sum (s := elementRows R')
        fun h hh => ite_eq_right hh]
      congr 1
      exact Finset.sum_congr rfl fun h hh => ite_eq_left hh
    simp only [T₁, T₂, F, S] at htsum ⊢
    rw [htsum]
    ring
  rw [hdiff]
  refine (norm_finsum_dvd_le_of hg.2 F (B := C * ((absNorm g : ℝ) * absNorm (b * c) / Y + 1) *
    ((absNorm g : ℝ) ^ 2 * absNorm (b * c) / (Y * R)) ^ k) (by positivity)
    fun e he => ?_).trans_eq (by ring)
  have he0 : (0 : ℝ) < absNorm e := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr
      (ne_bot_of_le_ne_bot hg.2.ne_zero (le_of_dvd he)))
  have hNe : (absNorm e : ℝ) ≤ absNorm g := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
      (absNorm_eq_zero_iff.not.mpr hg.2.ne_zero)) (absNorm_dvd_absNorm_of_le (le_of_dvd he))
  obtain ⟨-, hb⟩ := hfar (fun h => conj (pairCharacter b c h))
    (fun h => by rw [Complex.norm_conj]; exact norm_pairCharacter_le b c h) Y
    ((absNorm e : ℝ) * absNorm (b * c)) (R * absNorm e / (absNorm g : ℝ) ^ 2) hY
    (by positivity) (by positivity)
  simp only [F]
  rw [norm_mul]
  have hc1 : ‖(idealMoebius e : ℂ) * pairCharacter b c (generator e) / (absNorm e : ℂ)‖ ≤ 1 :=
    (norm_div_natCast_le _ _).trans (by
      rw [norm_mul]
      exact (mul_le_mul (norm_idealMoebius_le _) (norm_pairCharacter_le _ _ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  refine (mul_le_of_le_one_left (norm_nonneg _) hc1).trans (hb.trans ?_)
  have hq : (absNorm e : ℝ) * absNorm (b * c) / (Y * (R * absNorm e / (absNorm g : ℝ) ^ 2)) =
      (absNorm g : ℝ) ^ 2 * absNorm (b * c) / (Y * R) := by
    field_simp
  rw [hq]
  gcongr

/-! ### The gap estimate for columns coprime to `b` -/

lemma elementRows_eq_empty {K : ℝ} (hK : K < 1) : elementRows K = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun k hk => ?_
  unfold elementRows at hk
  simp only [Finset.mem_biUnion, Finset.mem_erase] at hk
  obtain ⟨a, ⟨ha, haK⟩, -⟩ := hk
  rw [idealsLe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Nat.floor_eq_zero.mpr hK,
    Nat.le_zero, absNorm_eq_zero_iff] at haK
  exact ha haK

/-- `GapEstimate` with columns coprime to a starred `b` of norm at most `D`, for all `K` and
all `X > 0`. Small `K` gives no rows, and short columns are counted directly. -/
theorem exists_dualMeanSquareCoprime_le (hpg : PairedGaussIdentities) (hgap : GapEstimate)
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ j : ℕ, ∀ I : TestInterval, ∃ C ≥ (0 : ℝ), ∀ (D K X F : ℝ) (ξ : RayCharacter)
      (U : ℝ → ℂ) (b : Ideal 𝓔), 2 ≤ D → 0 < X → 1 ≤ F → X * F ≤ D →
      K ≤ X * F * D ^ (-κ) → Starred b → (absNorm b : ℝ) ≤ D → UnitTest I j U →
        dualMeanSquareCoprime ξ U K X F b ≤ C * D ^ ε * (X * F) := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := two_pow_card_normalizedFactors_le (by positivity : 0 < ε / 4)
  obtain ⟨j, hj⟩ := hgap 1 le_rfl κ hκ (ε / 2) (by positivity)
  refine ⟨j, fun I => ?_⟩
  obtain ⟨C₂, hC₂, h₂⟩ := hj I
  obtain ⟨C₃, hC₃, h₃⟩ := dualMeanSquare_le_mul gaussCoefficientBound I
  refine ⟨C₁ ^ 2 * (C₂ + C₃), by positivity,
    fun D K X F ξ U b hD hX hF hXF hK hb hbD hU => ?_⟩
  have hD0 : 0 < D := by linarith
  have hXF0 : 0 < X * F := by positivity
  by_cases hK1 : K < 1
  · have : dualMeanSquareCoprime ξ U K X F b = 0 := by
      simp [dualMeanSquareCoprime, elementRows_eq_empty hK1]
    rw [this]; positivity
  push Not at hK1
  have hDκ : D ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hD2 : 1 ≤ D ^ (ε / 2) := Real.one_le_rpow (by linarith) (by positivity)
  have hW : ∀ x, U x ≠ 0 → x ≤ I.hi := fun x hx =>
    (hU.2.1 (subset_tsupport U hx)).2
  have hM : ∀ t ≤ normalizedFactors b, dualMeanSquare ξ U K (X / absNorm t.prod)
      (F * absNorm t.prod) ≤ (C₂ + C₃) * D ^ (ε / 2) * (X * F) := by
    intro t htb
    have ht : (1 : ℝ) ≤ absNorm t.prod := by
      have h0 : t.prod ≠ ⊥ := Multiset.prod_ne_zero fun h0 =>
        (prime_of_normalized_factor _ (Multiset.mem_of_le htb h0)).ne_zero rfl
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr h0)
    have hprod : X / absNorm t.prod * (F * absNorm t.prod) = X * F := by field_simp
    by_cases hX1 : 1 ≤ X / absNorm t.prod
    · refine (h₂ D K _ _ ξ U hD hK1 hX1 (one_le_mul_of_one_le_of_one_le hF ht)
        (by rw [hprod, Real.rpow_one]; exact hXF) (by rwa [hprod]) hU).trans ?_
      rw [hprod]
      nlinarith [mul_nonneg (mul_nonneg hC₃ (by positivity : (0 : ℝ) ≤ D ^ (ε / 2)))
        hXF0.le]
    · push Not at hX1
      refine (h₃ K _ _ ξ U hK1 (by positivity) (one_le_mul_of_one_le_of_one_le hF ht)
        (hU.of_le (Nat.zero_le j))).trans ?_
      have : K * (X / absNorm t.prod) ≤ X * F := by
        calc K * (X / absNorm t.prod) ≤ K * 1 := by gcongr
          _ ≤ X * F * D ^ (-κ) := by rwa [mul_one]
          _ ≤ X * F := mul_le_of_le_one_right hXF0.le hDκ
      nlinarith [mul_nonneg (mul_nonneg hC₂ (by positivity : (0 : ℝ) ≤ D ^ (ε / 2)))
        hXF0.le, mul_le_mul_of_nonneg_left this hC₃,
        mul_le_mul_of_nonneg_left hD2 (mul_nonneg hC₃ hXF0.le)]
  refine (dualMeanSquareCoprime_le_of_forall hpg gaussCoefficientBound residueMultiplicative hW
    hb hX (by linarith) hM).trans ?_
  have hb0 : (0 : ℝ) < absNorm b := by
    exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hb.1.1)
  have h4 : (4 : ℝ) ^ Multiset.card (normalizedFactors b) ≤ C₁ ^ 2 * D ^ (ε / 2) := by
    have h2 := h₁ b hb.1.1 hb.2
    have hpow : (absNorm b : ℝ) ^ (ε / 4) ≤ D ^ (ε / 4) :=
      Real.rpow_le_rpow hb0.le hbD (by positivity)
    calc (4 : ℝ) ^ Multiset.card (normalizedFactors b)
        = ((2 : ℝ) ^ Multiset.card (normalizedFactors b)) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (C₁ * D ^ (ε / 4)) ^ 2 := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left hpow hC₁)
      _ = C₁ ^ 2 * D ^ (ε / 2) := by
          rw [mul_pow, ← Real.rpow_natCast (D ^ (ε / 4)), ← Real.rpow_mul hD0.le]
          congr 2
          push_cast
          ring
  have hDε : D ^ (ε / 2) * D ^ (ε / 2) = D ^ ε := by
    rw [← Real.rpow_add hD0]; ring_nf
  calc (4 : ℝ) ^ Multiset.card (normalizedFactors b) * ((C₂ + C₃) * D ^ (ε / 2) * (X * F))
      ≤ C₁ ^ 2 * D ^ (ε / 2) * ((C₂ + C₃) * D ^ (ε / 2) * (X * F)) := by gcongr
    _ = C₁ ^ 2 * (C₂ + C₃) * D ^ ε * (X * F) := by rw [← hDε]; ring

/-! ### The arithmetic factor of a main dual term -/

lemma conj_sextic_eq_pow_five {n : Ideal 𝓔} (hn : AwayFromSix n) {a : 𝓔}
    (ha : IsCoprime n (span {a})) : conj (sextic n a) = sextic n a ^ 5 := by
  have h6 : sextic n a ^ 6 = 1 := by
    simp only [sextic, ← map_pow, powerResidueSymbol_six_pow_six hn.1 hn.2, ite_eq_left ha,
      map_one]
  have h1 : sextic n a * conj (sextic n a) = 1 := by
    rw [Complex.mul_conj', norm_sextic_of_coprime hn ha]; norm_num
  linear_combination (sextic n a ^ 5) * h1 - conj (sextic n a) * h6

lemma sextic_pow {n : Ideal 𝓔} (hn : AwayFromSix n) (x : 𝓔) (k : ℕ) :
    sextic n (x ^ k) = sextic n x ^ k := by
  induction k with
  | zero => simp [sextic_one hn]
  | succ k ih => rw [pow_succ, sextic_mul hn, ih, pow_succ]

/-- The arithmetic factor of a main dual term at `c = v m₁`, `b = v m₂` and the divisor `e`
of the gcd. The ray correction `A` is expanded in ray characters `ξ, η`; the row `k = e° h`
and the twist ideal `f = e v` give the twisted columns. -/
lemma mainSummand_eq (hres : ResidueMultiplicative)
    (hmul : ∀ b c : Ideal 𝓔, Starred b → Starred c → IsCoprime b c →
      gaussCoefficient (b * c) = gaussCoefficient b * gaussCoefficient c *
        sextic c (generator b) ^ 4)
    {A : Q₇₂ → Q₇₂ → ℂ} {α : RayCharacter → RayCharacter → ℂ}
    (hα : ∀ x y : Q₇₂, IsUnit x → IsUnit y → A x y = ∑ ξ, ∑ η, α ξ η * ξ x * conj (η y))
    {e v m₁ m₂ : Ideal 𝓔} (he : AwayFromSix e) (hv : Starred v) (hm₁ : Starred m₁)
    (hm₂ : Starred m₂) (hvm₁ : IsCoprime v m₁) (hvm₂ : IsCoprime v m₂) (hev : IsCoprime e v)
    (hem₁ : IsCoprime e m₁) (hem₂ : IsCoprime e m₂) (h : 𝓔) :
    gaussCoefficient (v * m₁) * conj (gaussCoefficient (v * m₂)) *
        A (Ideal.Quotient.mk _ (generator (v * m₁))) (Ideal.Quotient.mk _ (generator (v * m₂))) *
        (pairCharacter (v * m₁) (v * m₂) (generator e) *
          conj (pairCharacter (v * m₁) (v * m₂) h)) =
      ∑ ξ, ∑ η, α ξ η * (gaussCoefficient v * conj (gaussCoefficient v) *
          ξ (Ideal.Quotient.mk _ (generator v)) * conj (η (Ideal.Quotient.mk _ (generator v))) *
          (sextic v h * conj (sextic v h))) *
        ((gaussCoefficient m₁ * twist ξ (generator e * h) (e * v) m₁) *
          conj (gaussCoefficient m₂ * twist η (generator e * h) (e * v) m₂)) := by
  have h3 : ∀ {n : Ideal 𝓔}, AwayFromSix n → IsCoprime n (span {3}) := fun hn =>
    hn.coprime_three
  have hgen : ∀ {n : Ideal 𝓔}, AwayFromSix n → generator (v * n) = generator v * generator n :=
    fun hn => hres.generator_mul (h3 hv.1) (h3 hn)
  have hgev : generator (e * v) = generator e * generator v := hres.generator_mul (h3 he) (h3 hv.1)
  have hce : ∀ {n : Ideal 𝓔}, IsCoprime e n → IsCoprime n (span {generator e}) := fun hn => by
    rw [span_generator]; exact hn.symm
  rw [hα _ _ (isUnit_mk_generator (hv.1.mul hm₁.1)) (isUnit_mk_generator (hv.1.mul hm₂.1)),
    hgen hm₁.1, hgen hm₂.1, hmul v m₁ hv hm₁ hvm₁, hmul v m₂ hv hm₂ hvm₂, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun η _ => ?_
  have harg : generator e * h * (generator e * generator v) ^ 4 =
      h * generator e ^ 5 * generator v ^ 4 := by ring
  simp only [twist, hm₁.1, hm₂.1, ite_true, hgev, harg, pairCharacter, sextic_mul_right,
    map_mul, map_pow, sextic_mul hm₁.1, sextic_mul hm₂.1, sextic_pow hm₁.1, sextic_pow hm₂.1,
    Complex.conj_conj]
  have h₂ : conj (sextic m₂ (generator e)) ^ 5 = sextic m₂ (generator e) := by
    rw [← map_pow, ← conj_sextic_eq_pow_five hm₂.1 (hce hem₂), Complex.conj_conj]
  rw [← conj_sextic_eq_pow_five hm₁.1 (hce hem₁), h₂]
  have hvu : conj (sextic v (generator e)) * sextic v (generator e) = 1 := by
    rw [mul_comm, Complex.mul_conj', norm_sextic_of_coprime hv.1 (hce hev)]; norm_num
  linear_combination (gaussCoefficient v * gaussCoefficient m₁ * sextic m₁ (generator v) ^ 4 *
      (conj (gaussCoefficient v) * conj (gaussCoefficient m₂) *
        conj (sextic m₂ (generator v)) ^ 4) *
      (α ξ η * (ξ (Ideal.Quotient.mk _ (generator v)) * ξ (Ideal.Quotient.mk _ (generator m₁))) *
        (conj (η (Ideal.Quotient.mk _ (generator v))) *
          conj (η (Ideal.Quotient.mk _ (generator m₂))))) *
      (conj (sextic m₁ (generator e)) * sextic m₂ (generator e) *
        (sextic v h * sextic m₁ h * (conj (sextic v h) * conj (sextic m₂ h))))) * hvu

/-! ### Rows of a block -/

/-- A sum over `T` of a function of `p ρ` is at most `τ` times the sum over `S` when each fibre
of `p` has at most `τ` elements. -/
lemma sum_comp_le_mul_sum {ι κ : Type*} [DecidableEq κ] (T : Finset ι) (S : Finset κ)
    (p : ι → κ) (hp : ∀ ρ ∈ T, p ρ ∈ S) (G : κ → ℝ) (hG : ∀ x, 0 ≤ G x) {τ : ℝ}
    (hτ : ∀ x ∈ S, ((T.filter fun ρ => p ρ = x).card : ℝ) ≤ τ) :
    ∑ ρ ∈ T, G (p ρ) ≤ τ * ∑ x ∈ S, G x := by
  rw [← Finset.sum_fiberwise_of_maps_to hp, Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Finset.sum_congr rfl fun ρ hρ => by rw [(Finset.mem_filter.mp hρ).2], Finset.sum_const,
    nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hτ x hx) (hG x)

/-- Rows `(e, v, h)` with `e ≠ ⊥` cover each pair `(f, k) = (e v, e° h)` at most `τ(f)` times,
and `τ(f) ≪ (N f)^s`. -/
theorem exists_sum_rows_le {s : ℝ} (hs : 0 < s) :
    ∃ C ≥ (0 : ℝ), ∀ (T : Finset (Ideal 𝓔 × Ideal 𝓔 × 𝓔)) (S : Finset (Ideal 𝓔 × 𝓔))
      (G : Ideal 𝓔 × 𝓔 → ℝ) {F : ℝ}, (∀ x, 0 ≤ G x) →
      (∀ ρ ∈ T, ρ.1 ≠ ⊥ ∧ (ρ.1 * ρ.2.1, generator ρ.1 * ρ.2.2) ∈ S) →
      (∀ x ∈ S, x.1 ≠ ⊥ ∧ (absNorm x.1 : ℝ) ≤ F) →
      ∑ ρ ∈ T, G (ρ.1 * ρ.2.1, generator ρ.1 * ρ.2.2) ≤ C * F ^ s * ∑ x ∈ S, G x := by
  classical
  obtain ⟨C, hC, hτ⟩ := card_idealDivisors_le hs
  refine ⟨C, hC, fun T S G F hG hT hS => ?_⟩
  refine sum_comp_le_mul_sum T S _ (fun ρ hρ => (hT ρ hρ).2) G hG fun x hx => ?_
  obtain ⟨hx0, hxF⟩ := hS x hx
  have hinj : Set.InjOn (fun ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔 => ρ.1)
      (T.filter fun ρ => (ρ.1 * ρ.2.1, generator ρ.1 * ρ.2.2) = x) := by
    intro ρ hρ σ hσ (he : ρ.1 = σ.1)
    obtain ⟨hρT, hρx⟩ := Finset.mem_filter.mp hρ
    obtain ⟨-, hσx⟩ := Finset.mem_filter.mp hσ
    have he0 : ρ.1 ≠ ⊥ := (hT ρ hρT).1
    have hg0 : generator ρ.1 ≠ 0 := fun h0 => he0 (by
      rw [← span_generator ρ.1, h0, span_singleton_eq_bot])
    rw [← hσx, he] at hρx
    obtain ⟨h1, h2⟩ := Prod.mk.inj hρx
    rw [← he] at h1 h2
    have hv : ρ.2.1 = σ.2.1 := mul_left_cancel₀ he0 h1
    have hh : ρ.2.2 = σ.2.2 := mul_left_cancel₀ hg0 h2
    exact Prod.ext he (Prod.ext hv hh)
  have hmaps : ∀ ρ ∈ T.filter fun ρ => (ρ.1 * ρ.2.1, generator ρ.1 * ρ.2.2) = x,
      ρ.1 ∈ idealDivisors x.1 := by
    intro ρ hρ
    obtain ⟨-, hρx⟩ := Finset.mem_filter.mp hρ
    rw [mem_idealDivisors hx0, ← hρx]
    exact dvd_mul_right _ _
  calc (((T.filter fun ρ => (ρ.1 * ρ.2.1, generator ρ.1 * ρ.2.2) = x).card : ℕ) : ℝ)
      ≤ (idealDivisors x.1).card := by exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ C * (absNorm x.1 : ℝ) ^ s := hτ _ hx0
    _ ≤ C * F ^ s := by gcongr

/-! ### The block bound -/

/-- The starred columns of norm at most `R X`. -/
def blockColumns (R X : ℝ) : Finset (Ideal 𝓔) := by
  classical
  exact (idealsLe (R * X)).filter Starred

/-- The column coefficient of a block: the twisted Gauss coefficient at the row `k = e° h` and
the twist ideal `f = e v` of `ρ = (e, v, h)`, restricted to columns coprime to `b`. -/
def blockCoefficient (ξ : RayCharacter) (b : Ideal 𝓔) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔)
    (m : Ideal 𝓔) : ℂ := open Classical in
  if IsCoprime m b then
    gaussCoefficient m * twist ξ (generator ρ.1 * ρ.2.2) (ρ.1 * ρ.2.1) m
  else 0

lemma columnSumCoprime_eq_sum {ξ : RayCharacter} {U : ℝ → ℂ} {R X : ℝ} (hX : 0 < X)
    (hU : ∀ x, U x ≠ 0 → x ≤ R) (b : Ideal 𝓔) (ρ : Ideal 𝓔 × Ideal 𝓔 × 𝓔) :
    columnSumCoprime ξ U X (generator ρ.1 * ρ.2.2) (ρ.1 * ρ.2.1) b =
      ∑ m ∈ blockColumns R X, blockCoefficient ξ b ρ m * U (absNorm m / X) := by
  classical
  have hst : ∀ m ∈ blockColumns R X, Starred m := fun m hm => by
    unfold blockColumns at hm
    exact (Finset.mem_filter.mp hm).2
  rw [← Finset.subtype_map_of_mem hst, Finset.sum_map, columnSumCoprime,
    finsum_eq_sum_of_support_subset (s := (blockColumns R X).subtype Starred) _ ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [blockCoefficient, Function.Embedding.subtype_apply]
    by_cases hc : IsCoprime m.1 b
    · simp only [hc, ↓reduceIte]
    · simp [hc]
  intro m hm
  rw [Function.mem_support] at hm
  have hU0 : U (absNorm m.1 / X) ≠ 0 := fun h0 => hm (by simp [h0])
  have hle := hU _ hU0
  rw [div_le_iff₀ hX] at hle
  rw [Finset.mem_coe, Finset.mem_subtype]
  unfold blockColumns
  rw [Finset.mem_filter, mem_idealsLe (by
    have : (0 : ℝ) ≤ absNorm m.1 := Nat.cast_nonneg _
    linarith)]
  exact ⟨hle, m.2⟩

lemma hasCompactSupport_conj_comp_exp {W : ℝ → ℂ} (hWc : HasCompactSupport W)
    (hW0 : tsupport W ⊆ Set.Ioi 0) : HasCompactSupport fun t => conj (W (Real.exp t)) := by
  refine HasCompactSupport.comp_left (g := conj) ?_ (map_zero _)
  refine HasCompactSupport.intro (hWc.isCompact.image_of_continuousOn
    (Real.continuousOn_log.mono fun x hx => ne_of_gt (hW0 hx))) fun t ht => ?_
  by_contra h
  exact ht ⟨Real.exp t, subset_tsupport W h, Real.log_exp t⟩

/-- A block of main dual terms: rows `ρ = (e, v, h)` with `f = e v` starred of norm in
`[F, 2F)` and `k = e° h ∈ elementRows K`, columns coprime to `b`, ray characters `ξ, η` on the
two sides, the dilation `β = N f / F` of the weight `W`, and a cut dual kernel with any row
shifts `a ρ`. It is `O(D^ε (XF)²)` under the hypotheses of `exists_dualMeanSquareCoprime_le`. -/
theorem exists_block_le (hpg : PairedGaussIdentities) (hgap : GapEstimate) {W : ℝ → ℂ}
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) (hW0 : tsupport W ⊆ Set.Ioi 0)
    (P : SchwartzMap ℝ ℂ) {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ R₁ C : ℝ, 0 ≤ C ∧ ∀ (R D K X F : ℝ) (ξ η : RayCharacter) (b : Ideal 𝓔)
      (T : Finset (Ideal 𝓔 × Ideal 𝓔 × 𝓔)) (a : Ideal 𝓔 × Ideal 𝓔 × 𝓔 → ℝ),
      R₁ ≤ R → 2 ≤ D → 0 < X → 1 ≤ F → F ≤ D → X * F ≤ D → K ≤ X * F * D ^ (-κ) →
      Starred b → (absNorm b : ℝ) ≤ D →
      (∀ ρ ∈ T, ρ.1 ≠ ⊥ ∧ Starred (ρ.1 * ρ.2.1) ∧ F ≤ (absNorm (ρ.1 * ρ.2.1) : ℝ) ∧
        (absNorm (ρ.1 * ρ.2.1) : ℝ) < 2 * F ∧ generator ρ.1 * ρ.2.2 ∈ elementRows K) →
      ∑ ρ ∈ T, ‖∑ m₁ ∈ blockColumns R X, ∑ m₂ ∈ blockColumns R X,
        blockCoefficient ξ b ρ m₁ * conj (blockCoefficient η b ρ m₂) *
          (conj (W (absNorm (ρ.1 * ρ.2.1) / F * (absNorm m₁ / X))) *
            W (absNorm (ρ.1 * ρ.2.1) / F * (absNorm m₂ / X)) *
            cutDualKernel P χ (a ρ) (Real.log (absNorm m₁ / X) + Real.log (absNorm m₂ / X)))‖ ≤
        C * D ^ ε * (X * F) ^ 2 := by
  classical
  set w : ℝ → ℂ := fun t => conj (W (Real.exp t)) with hw_def
  have hw : ContDiff ℝ ∞ w :=
    (Complex.conjCLE.contDiff.comp (hW.comp Real.contDiff_exp) :)
  have hwc : HasCompactSupport w := hasCompactSupport_conj_comp_exp hWc hW0
  obtain ⟨j, hj⟩ := exists_dualMeanSquareCoprime_le hpg hgap hκ (half_pos hε)
  obtain ⟨I, Cs, hCs, hsep⟩ := exists_dilated_separated_le₂ hw hwc (Real.log_nonneg one_le_two) j
  obtain ⟨Cg, hCg, hgap'⟩ := hj I
  obtain ⟨A, hA, hker⟩ := exists_cutDualKernel_bounds P hχ hχc (2 * j + 2)
  obtain ⟨Cr, hCr, hrows⟩ := exists_sum_rows_le (half_pos hε)
  refine ⟨max I.hi 1, 2 * Cs * A * (Cr * 2 ^ (ε / 2) * Cg), by positivity,
    fun R D K X F ξ η b T a hR hD hX hF hFD hXF hK hb hbD hT => ?_⟩
  have hD0 : 0 < D := by linarith
  have hF0 : 0 < F := by linarith
  set cols := blockColumns R X
  set M := Cr * (2 * D) ^ (ε / 2) * ((X * F) * (Cg * D ^ (ε / 2) * (X * F))) with hM
  have hM0 : 0 ≤ M := by positivity
  have hcolpos : ∀ n ∈ cols, 0 < (absNorm n : ℝ) / X := fun n hn => by
    have hst : Starred n := by
      simp only [cols, blockColumns] at hn; exact (Finset.mem_filter.mp hn).2
    have : (0 : ℝ) < absNorm n := by
      exact_mod_cast Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hst.1.1)
    positivity
  have hmean : ∀ ζ : RayCharacter, ∀ U, UnitTest I j U →
      ∑ ρ ∈ T, ‖∑ n ∈ cols, blockCoefficient ζ b ρ n * U (absNorm n / X)‖ ^ 2 ≤ M := by
    intro ζ U hU
    have hUR : ∀ x, U x ≠ 0 → x ≤ R := fun x hx =>
      ((hU.2.1 (subset_tsupport U hx)).2).trans ((le_max_left _ _).trans hR)
    set Fs := (idealsLe (2 * F)).filter fun f =>
      Starred f ∧ F ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * F
    set S := Fs ×ˢ elementRows K
    have hS : ∀ x ∈ S, x.1 ≠ ⊥ ∧ (absNorm x.1 : ℝ) ≤ 2 * D := fun x hx => by
      obtain ⟨hx1, -⟩ := Finset.mem_product.mp hx
      obtain ⟨-, hst, -, hlt⟩ := Finset.mem_filter.mp hx1
      exact ⟨hst.1.1, by linarith⟩
    have hTS : ∀ ρ ∈ T, ρ.1 ≠ ⊥ ∧ (ρ.1 * ρ.2.1, generator ρ.1 * ρ.2.2) ∈ S := fun ρ hρ => by
      obtain ⟨h0, hst, hF1, hF2, hk⟩ := hT ρ hρ
      refine ⟨h0, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, hst, hF1, hF2⟩, hk⟩⟩
      exact (mem_idealsLe (by linarith)).mpr hF2.le
    have hG : ∀ x : Ideal 𝓔 × 𝓔, 0 ≤ ‖columnSumCoprime ζ U X x.2 x.1 b‖ ^ 2 :=
      fun x => sq_nonneg _
    calc ∑ ρ ∈ T, ‖∑ n ∈ cols, blockCoefficient ζ b ρ n * U (absNorm n / X)‖ ^ 2
        = ∑ ρ ∈ T, ‖columnSumCoprime ζ U X (generator ρ.1 * ρ.2.2) (ρ.1 * ρ.2.1) b‖ ^ 2 :=
          Finset.sum_congr rfl fun ρ _ => by rw [columnSumCoprime_eq_sum hX hUR]
      _ ≤ Cr * (2 * D) ^ (ε / 2) * ∑ x ∈ S, ‖columnSumCoprime ζ U X x.2 x.1 b‖ ^ 2 :=
          hrows T S (fun x => ‖columnSumCoprime ζ U X x.2 x.1 b‖ ^ 2) hG hTS hS
      _ = Cr * (2 * D) ^ (ε / 2) * ((X * F) * dualMeanSquareCoprime ζ U K X F b) := by
          rw [dualMeanSquareCoprime, Finset.sum_product, mul_div_cancel₀ _ (by positivity)]
      _ ≤ M := by
          rw [hM]
          gcongr
          exact hgap' D K X F ζ U b hD hX hF hXF hK hb hbD hU
  have hsep' := hsep T cols (blockCoefficient ξ b) (blockCoefficient η b)
    (fun n => (absNorm n : ℝ) / X) (fun ρ => Real.log ((absNorm (ρ.1 * ρ.2.1) : ℝ) / F))
    (fun ρ => cutDualKernel P χ (a ρ)) hA hM0 hM0 hcolpos
    (fun ρ hρ => by
      obtain ⟨-, -, hF1, hF2, -⟩ := hT ρ hρ
      have h1 := (one_le_div hF0).mpr hF1
      refine ⟨Real.log_nonneg h1, Real.log_le_log (by linarith) ?_⟩
      rw [div_le_iff₀ hF0]; linarith)
    (hmean ξ) (hmean η)
    (fun ρ _ => (hker (a ρ)).1.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun ρ _ k hk => ((hker (a ρ)).2 k hk).1)
    (fun ρ _ => by simpa using ((hker (a ρ)).2 0 (Nat.zero_le _)).2)
    (fun ρ _ => ((hker (a ρ)).2 (2 * j + 2) le_rfl).2)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun ρ hρ => ?_) (hsep'.trans_eq ?_)
  · obtain ⟨-, -, hF1, -, -⟩ := hT ρ hρ
    have hβ : (0 : ℝ) < absNorm (ρ.1 * ρ.2.1) / F := by
      have : (0 : ℝ) < absNorm (ρ.1 * ρ.2.1) := by linarith
      positivity
    congr 1
    refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
    simp only [hw_def, Complex.conj_conj, ← Real.log_mul hβ.ne' (hcolpos m₁ hm₁).ne',
      ← Real.log_mul hβ.ne' (hcolpos m₂ hm₂).ne', Real.exp_log (mul_pos hβ (hcolpos m₁ hm₁)),
      Real.exp_log (mul_pos hβ (hcolpos m₂ hm₂))]
  · rw [hM, Real.mul_rpow (by norm_num) hD0.le]
    have hDε : D ^ (ε / 2) * D ^ (ε / 2) = D ^ ε := by
      rw [← Real.rpow_add hD0]; ring_nf
    rw [← hDε]
    ring

/-! ### The far dual frequencies of the full square -/

/-- The weight of the gcd split `t` in `dualTailTerm`. -/
def splitWeight (A : Q₇₂ → Q₇₂ → ℂ) (W : ℝ → ℂ) (D Y : ℝ)
    (t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : ℂ :=
  W (absNorm (t.1 * t.2.1) / D) * conj (W (absNorm (t.1 * t.2.2) / D)) *
    ((Y : ℂ) / Real.sqrt (absNorm (t.2.2 * t.2.1))) *
    (gaussCoefficient t.2.2 * conj (gaussCoefficient t.2.1) *
      A (Ideal.Quotient.mk _ (generator t.2.2)) (Ideal.Quotient.mk _ (generator t.2.1)))

/-- `dualTailSum` with only the main dual frequencies `dualExclusionMain` at radius `R`. -/
def dualMainSum (P : SchwartzMap ℝ ℂ) (A : Q₇₂ → Q₇₂ → ℂ) (W : ℝ → ℂ) (D Y R : ℝ) : ℂ :=
  ∑ᶠ t ∈ {t | IsGcdSplit t}, splitWeight A W D Y t * dualExclusionMain P Y R t.2.2 t.2.1 t.1

/-- The gcd splits with all three ideals of norm at most `X`. -/
def gcdSplitsLe (X : ℝ) : Finset (Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) := by
  classical exact ((idealsLe X) ×ˢ ((idealsLe X) ×ˢ (idealsLe X))).filter IsGcdSplit

lemma mem_gcdSplitsLe {X : ℝ} (hX : 0 ≤ X) {t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔}
    (ht : IsGcdSplit t) (h₁ : (absNorm (t.1 * t.2.1) : ℝ) ≤ X)
    (h₂ : (absNorm (t.1 * t.2.2) : ℝ) ≤ X) : t ∈ gcdSplitsLe X := by
  classical
  obtain ⟨g, z₁, z₂⟩ := t
  have hn₁ : g * z₁ ≠ ⊥ := mul_ne_zero ht.1.1.1 ht.2.1.1.1
  have hn₂ : g * z₂ ≠ ⊥ := mul_ne_zero ht.1.1.1 ht.2.2.1.1.1
  unfold gcdSplitsLe
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(mem_idealsLe hX).mpr
    ((absNorm_le_absNorm_mul hn₁).1.trans h₁), Finset.mem_product.mpr
      ⟨(mem_idealsLe hX).mpr ((absNorm_le_absNorm_mul hn₁).2.trans h₁),
        (mem_idealsLe hX).mpr ((absNorm_le_absNorm_mul hn₂).2.trans h₂)⟩⟩, ht⟩

lemma splitWeight_ne_zero {A : Q₇₂ → Q₇₂ → ℂ} {W : ℝ → ℂ} {D Y : ℝ}
    {t : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (h : splitWeight A W D Y t ≠ 0) :
    W (absNorm (t.1 * t.2.1) / D) ≠ 0 ∧ W (absNorm (t.1 * t.2.2) / D) ≠ 0 := by
  have h' := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  exact ⟨left_ne_zero_of_mul h', fun h₀ => right_ne_zero_of_mul h' (by rw [h₀, map_zero])⟩

/-- A sum weighted by `splitWeight` over the gcd splits is a finite sum when `W` vanishes beyond
`R'`. -/
lemma finsum_splitWeight_eq_sum {A : Q₇₂ → Q₇₂ → ℂ} {W : ℝ → ℂ} {D Y R' : ℝ}
    (hWz : ∀ x, W x ≠ 0 → x ≤ R') (hD : 0 < D) (hX : 0 ≤ R' * D)
    (Z : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔 → ℂ) :
    ∑ᶠ t ∈ {t | IsGcdSplit t}, splitWeight A W D Y t * Z t =
      ∑ t ∈ gcdSplitsLe (R' * D), splitWeight A W D Y t * Z t := by
  classical
  have hWX : ∀ n : Ideal 𝓔, W (absNorm n / D) ≠ 0 → (absNorm n : ℝ) ≤ R' * D := fun n h => by
    have := hWz _ h
    rwa [div_le_iff₀ hD] at this
  refine finsum_mem_eq_sum_of_subset _ (fun t ht => ?_) fun t ht => ?_
  · obtain ⟨ht, hne⟩ := ht
    obtain ⟨h₁, h₂⟩ := splitWeight_ne_zero (left_ne_zero_of_mul hne)
    exact mem_gcdSplitsLe hX ht (hWX _ h₁) (hWX _ h₂)
  · unfold gcdSplitsLe at ht
    exact (Finset.mem_filter.mp ht).2

/-- The far dual frequencies of the full square: `dualTailSum` is `dualMainSum` at radius
`D^(2+η)/Y` up to `O(D^(2+θ))`. -/
theorem exists_norm_dualTailSum_sub_le (P : SchwartzMap ℝ ℂ) (A : Q₇₂ → Q₇₂ → ℂ) {W : ℝ → ℂ}
    (hW : Continuous W) (hc : HasCompactSupport W) {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 < η) :
    ∃ C ≥ (0 : ℝ), ∀ D : ℝ, 2 ≤ D →
      ‖dualTailSum P A W D (D ^ (1 + θ)) -
        dualMainSum P A W D (D ^ (1 + θ)) (D ^ (2 + η) / D ^ (1 + θ))‖ ≤ C * D ^ (2 + θ) := by
  classical
  obtain ⟨M, hM⟩ := hW.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  obtain ⟨A₀, hA₀⟩ := exists_card_idealsLe_le
  obtain ⟨Cτ, hCτ, hτ⟩ := two_pow_card_normalizedFactors_le one_pos
  set k := ⌈4 / η⌉₊
  obtain ⟨Ct, hCt, hfar⟩ := exists_norm_dualExclusionTail_sub_le P k
  set R' := max R 1
  set Amax := ∑ x, ∑ y, ‖A x y‖
  have hAmax : ∀ x y, ‖A x y‖ ≤ Amax := fun x y =>
    (Finset.single_le_sum (f := fun y => ‖A x y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ y)).trans (Finset.single_le_sum (f := fun x => ∑ y, ‖A x y‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x))
  have hAmax₀ : 0 ≤ Amax := (norm_nonneg _).trans (hAmax 0 0)
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hR' : 1 ≤ R' := le_max_right R 1
  have hA₀' : 0 ≤ A₀ := by
    have := hA₀ 1 le_rfl
    nlinarith [(Finset.card_pos.mpr ⟨⊤, (mem_idealsLe zero_le_one).mpr (by simp)⟩ :
      0 < (idealsLe 1).card)]
  have hWz : ∀ x, W x ≠ 0 → x ≤ R' := fun x hx => by
    by_contra hlt
    exact hx (image_eq_zero_of_notMem_tsupport fun h => by
      linarith [hR h, le_max_left R 1, lt_of_not_ge hlt])
  have hk : 4 ≤ η * k := by
    have := Nat.le_ceil (4 / η)
    rw [div_le_iff₀ hη] at this
    linarith
  set B := Amax * M ^ 2 * Ct * Cτ * A₀ ^ 3 * R' ^ 4 * (R' ^ 2) ^ k * (R' ^ 2 + 1)
  refine ⟨B, by positivity, fun D hD => ?_⟩
  have hD₀ : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  set Y := D ^ (1 + θ) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hD₀ _
  set X := R' * D with hXdef
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hR' hD1
  have hRY : Y * (D ^ (2 + η) / Y) = D ^ (2 + η) := by field_simp
  have hXη : X ^ 2 / D ^ (2 + η) = R' ^ 2 * D ^ (-η) := by
    rw [Real.rpow_add hD₀, Real.rpow_neg hD₀.le, Real.rpow_two]
    have : 0 < D ^ η := Real.rpow_pos_of_pos hD₀ η
    field_simp
    rw [hXdef]
    ring
  -- Each gcd split.
  have hterm : ∀ t ∈ gcdSplitsLe X, ‖splitWeight A W D Y t *
      (dualExclusionTail P Y t.2.2 t.2.1 t.1 -
        dualExclusionMain P Y (D ^ (2 + η) / Y) t.2.2 t.2.1 t.1)‖ ≤
      Amax * M ^ 2 * Ct * Cτ * X * (X ^ 2 + Y) * (R' ^ 2 * D ^ (-η)) ^ k := by
    rintro ⟨g, z₁, z₂⟩ ht
    have hRHS : 0 ≤ Amax * M ^ 2 * Ct * Cτ * X * (X ^ 2 + Y) * (R' ^ 2 * D ^ (-η)) ^ k := by
      have := Real.rpow_pos_of_pos hD₀ (-η)
      positivity
    by_cases hsw : splitWeight A W D Y (g, z₁, z₂) = 0
    · rw [hsw, zero_mul, norm_zero]
      exact hRHS
    have hWX : ∀ n : Ideal 𝓔, W (absNorm n / D) ≠ 0 → (absNorm n : ℝ) ≤ X := fun n h => by
      have := hWz _ h
      rwa [div_le_iff₀ hD₀] at this
    obtain ⟨hW₁, hW₂⟩ := splitWeight_ne_zero hsw
    have hn₁ := hWX _ hW₁
    have hn₂ := hWX _ hW₂
    simp only [gcdSplitsLe] at ht
    obtain ⟨hg, h₁, h₂, -, -⟩ := (Finset.mem_filter.mp ht).2
    have hg1 : (1 : ℝ) ≤ absNorm g := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hg.1.1)
    have hz : (1 : ℝ) ≤ absNorm (z₂ * z₁) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (absNorm_eq_zero_iff.not.mpr (mul_ne_zero h₂.1.1 h₁.1.1))
    have hprod : (absNorm g : ℝ) ^ 2 * absNorm (z₂ * z₁) =
        absNorm (g * z₁) * absNorm (g * z₂) := by
      simp only [map_mul, Nat.cast_mul]
      ring
    have hgz : (absNorm g : ℝ) * absNorm (z₂ * z₁) ≤ X ^ 2 := by
      have : (absNorm g : ℝ) * absNorm (z₂ * z₁) ≤ (absNorm g : ℝ) ^ 2 * absNorm (z₂ * z₁) :=
        calc (absNorm g : ℝ) * absNorm (z₂ * z₁) = absNorm g * absNorm (z₂ * z₁) * 1 := by ring
          _ ≤ absNorm g * absNorm (z₂ * z₁) * absNorm g :=
            mul_le_mul_of_nonneg_left hg1 (by positivity)
          _ = _ := by ring
      rw [hprod] at this
      nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ absNorm (g * z₁))]
    have hτg : (2 : ℝ) ^ Multiset.card (normalizedFactors g) ≤ Cτ * X := by
      refine (hτ g hg.1.1 hg.2).trans ?_
      rw [Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (by
        nlinarith [(absNorm_le_absNorm_mul (mul_ne_zero hg.1.1 h₁.1.1)).1]) hCτ
    have hfar' := hfar z₂ z₁ g h₂.1 h₁.1 hg Y (D ^ (2 + η) / Y) hY (by positivity)
    rw [hRY, hprod] at hfar'
    have hq : (absNorm (g * z₁) : ℝ) * absNorm (g * z₂) / D ^ (2 + η) ≤ R' ^ 2 * D ^ (-η) := by
      rw [← hXη]
      gcongr
      nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ absNorm (g * z₁))]
    have hsw' : ‖splitWeight A W D Y (g, z₁, z₂)‖ ≤ M * M * Y * (1 * 1 * Amax) := by
      simp only [splitWeight]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj,
        Complex.norm_conj, norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hY.le, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      gcongr
      · exact hM _
      · exact hM _
      · exact div_le_self hY.le (Real.one_le_sqrt.mpr hz)
      · exact gaussCoefficientBound _ h₂
      · exact gaussCoefficientBound _ h₁
      · exact hAmax _ _
    have hD' : 0 ≤ D ^ (-η) := (Real.rpow_pos_of_pos hD₀ _).le
    calc _ = ‖splitWeight A W D Y (g, z₁, z₂)‖ * ‖dualExclusionTail P Y z₂ z₁ g -
          dualExclusionMain P Y (D ^ (2 + η) / Y) z₂ z₁ g‖ := norm_mul _ _
      _ ≤ (M * M * Y * (1 * 1 * Amax)) * (Ct * (Cτ * X) * (X ^ 2 / Y + 1) *
          (R' ^ 2 * D ^ (-η)) ^ k) := by
          refine mul_le_mul hsw' (hfar'.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = _ := by field_simp
  have hcard : ((gcdSplitsLe X).card : ℝ) ≤ (A₀ * X) ^ 3 := by
    have h := hA₀ X hX
    calc ((gcdSplitsLe X).card : ℝ)
        ≤ ((idealsLe X) ×ˢ ((idealsLe X) ×ˢ (idealsLe X))).card := by
          simp only [gcdSplitsLe]
          exact_mod_cast Finset.card_filter_le _ _
      _ = (idealsLe X).card ^ 3 := by simp [Finset.card_product]; ring
      _ ≤ (A₀ * X) ^ 3 := by gcongr
  have hDk : D ^ 4 * (D ^ (-η)) ^ k ≤ 1 := by
    rw [← Real.rpow_natCast (D ^ (-η)), ← Real.rpow_mul hD₀.le]
    have : D ^ (-η * k) ≤ D ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
    calc D ^ 4 * D ^ (-η * k) ≤ D ^ 4 * D ^ (-4 : ℝ) := by gcongr
      _ = 1 := by
        rw [Real.rpow_neg hD₀.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        field_simp
  have hXY : X ^ 2 + Y ≤ (R' ^ 2 + 1) * D ^ (2 + θ) := by
    have h₁ : D ^ (2 : ℝ) ≤ D ^ (2 + θ) := Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
    have h₂ : Y ≤ D ^ (2 + θ) := Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
    rw [Real.rpow_two] at h₁
    nlinarith
  have hsum : dualTailSum P A W D Y - dualMainSum P A W D Y (D ^ (2 + η) / Y) =
      ∑ t ∈ gcdSplitsLe X, splitWeight A W D Y t *
        (dualExclusionTail P Y t.2.2 t.2.1 t.1 -
          dualExclusionMain P Y (D ^ (2 + η) / Y) t.2.2 t.2.1 t.1) := by
    have h₁ : dualTailSum P A W D Y = ∑ t ∈ gcdSplitsLe X,
        splitWeight A W D Y t * dualExclusionTail P Y t.2.2 t.2.1 t.1 :=
      finsum_splitWeight_eq_sum hWz hD₀ (by linarith) _
    rw [h₁, dualMainSum, finsum_splitWeight_eq_sum hWz hD₀ (by linarith),
      ← Finset.sum_sub_distrib]
    simp only [mul_sub]
  have hD' : 0 ≤ D ^ (-η) := (Real.rpow_pos_of_pos hD₀ _).le
  rw [hsum]
  calc _ ≤ ∑ t ∈ gcdSplitsLe X, Amax * M ^ 2 * Ct * Cτ * X * (X ^ 2 + Y) *
        (R' ^ 2 * D ^ (-η)) ^ k := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (gcdSplitsLe X).card * (Amax * M ^ 2 * Ct * Cτ * X * (X ^ 2 + Y) *
        (R' ^ 2 * D ^ (-η)) ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A₀ * X) ^ 3 * (Amax * M ^ 2 * Ct * Cτ * X * (X ^ 2 + Y) *
        (R' ^ 2 * D ^ (-η)) ^ k) := by gcongr
    _ = Amax * M ^ 2 * Ct * Cτ * A₀ ^ 3 * R' ^ 4 * (R' ^ 2) ^ k * (X ^ 2 + Y) *
        (D ^ 4 * (D ^ (-η)) ^ k) := by rw [hXdef]; ring
    _ ≤ Amax * M ^ 2 * Ct * Cτ * A₀ ^ 3 * R' ^ 4 * (R' ^ 2) ^ k *
        ((R' ^ 2 + 1) * D ^ (2 + θ)) * 1 := by gcongr
    _ = B * D ^ (2 + θ) := by ring

end Masullo.QRH.MeanSquare
