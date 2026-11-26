import WeilExplicit.DensityCount
import WeilExplicit.Controls

/-!
# Exterior zeros counted with multiplicity

Fix `a > 0`, put `δ = min (a / 2) (1 / 8)` and `c = 1 - δ² / 3`. The zeros in the open critical
strip at distance at least `a` from the critical line and of height at most `X ≥ 2`, counted with
multiplicity, number at most `A X^c log² (2X + 4)`, with `A` depending on `a` only.

Folding by `ρ ↦ conj ρ` and `ρ ↦ 1 - ρ` moves every such zero, with its multiplicity, to the upper
right quadrant, at most four to one. There `shell_card_le` counts a dyadic shell and
`window_zero_count` bounds each multiplicity by a logarithm. Summing the shells gives the count.
-/

namespace WeilExplicit

open Complex Set Real
open scoped ComplexConjugate

/-- The image `1/2 + |Re ρ - 1/2| + i |Im ρ|` in the closed upper right quadrant. -/
noncomputable def fold (ρ : ℂ) : ℂ := ⟨1 / 2 + |ρ.re - 1 / 2|, |ρ.im|⟩

/-- The four quadrants: `fold` is the identity, conjugation, reflection of the conjugate, or
reflection. -/
theorem fold_cases (ρ : ℂ) :
    (fold ρ = ρ ∧ 1 / 2 ≤ ρ.re ∧ 0 ≤ ρ.im) ∨ (fold ρ = conj ρ ∧ 1 / 2 ≤ ρ.re ∧ ρ.im < 0) ∨
      (fold ρ = 1 - conj ρ ∧ ρ.re < 1 / 2 ∧ 0 ≤ ρ.im) ∨
        (fold ρ = 1 - ρ ∧ ρ.re < 1 / 2 ∧ ρ.im < 0) := by
  rcases le_or_gt (1 / 2) ρ.re with hr | hr <;> rcases le_or_gt 0 ρ.im with hi | hi
  · have ea : |ρ.re - 1 / 2| = ρ.re - 1 / 2 := abs_of_nonneg (by linarith)
    refine Or.inl ⟨?_, hr, hi⟩
    apply Complex.ext
    · simp only [fold, ea]; ring
    · simp only [fold, abs_of_nonneg hi]
  · have ea : |ρ.re - 1 / 2| = ρ.re - 1 / 2 := abs_of_nonneg (by linarith)
    refine Or.inr (Or.inl ⟨?_, hr, hi⟩)
    apply Complex.ext
    · simp only [fold, ea, conj_re]; ring
    · simp only [fold, abs_of_neg hi, conj_im]
  · have ea : |ρ.re - 1 / 2| = 1 / 2 - ρ.re := by rw [abs_of_neg (by linarith)]; ring
    refine Or.inr (Or.inr (Or.inl ⟨?_, hr, hi⟩))
    apply Complex.ext <;>
      simp only [fold, ea, abs_of_nonneg hi, sub_re, sub_im, one_re, one_im, conj_re,
        conj_im] <;> ring
  · have ea : |ρ.re - 1 / 2| = 1 / 2 - ρ.re := by rw [abs_of_neg (by linarith)]; ring
    refine Or.inr (Or.inr (Or.inr ⟨?_, hr, hi⟩))
    apply Complex.ext <;>
      simp only [fold, ea, abs_of_neg hi, sub_re, sub_im, one_re, one_im] <;> ring

theorem zeroMult_fold {ρ : ℂ} (hρ : ρ ∈ stripZeros) : zeroMult (fold ρ) = zeroMult ρ := by
  have h0 := hρ.2.1
  have h1 := hρ.2.2
  have hc := zeroMult_conj ⟨ρ, hρ⟩
  simp only at hc
  rcases fold_cases ρ with ⟨e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩ <;> rw [e]
  · rw [hc]
  · rw [zeroMult_one_sub (s := conj ρ) (by simpa using h0) (by simpa using h1), hc]
  · rw [zeroMult_one_sub h0 h1]

theorem fold_mem {ρ : ℂ} (hρ : ρ ∈ stripZeros) : fold ρ ∈ stripZeros := by
  have hre : 0 < (fold ρ).re ∧ (fold ρ).re < 1 := by
    simp only [fold]
    constructor
    · positivity
    · have := abs_lt.2 (⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩ :
        -(1 / 2 : ℝ) < ρ.re - 1 / 2 ∧ ρ.re - 1 / 2 < 1 / 2)
      linarith
  refine ⟨by_contra fun h => ?_, hre⟩
  have hne : fold ρ ≠ 1 := fun e => by simpa [e] using hre.2
  have := zeroMult_eq_zero hne h
  rw [zeroMult_fold hρ] at this
  exact (zeroMult_pos hρ).ne' this

theorem mem_of_fold_eq (ρ : ℂ) :
    ρ ∈ ({fold ρ, conj (fold ρ), 1 - conj (fold ρ), 1 - fold ρ} : Finset ℂ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases fold_cases ρ with ⟨e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩ <;> rw [e] <;> simp

/-- The zeros at distance at least `2δ` from the critical line with `U ≤ |Im ρ| ≤ 2U`, counted with
multiplicity in any finite family, number `O(log² (2U + 4) · U^{1-δ²/3})`. -/
theorem shell_mult_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    ∃ B, 0 ≤ B ∧ ∀ U : ℝ, 2 ≤ U → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ stripZeros ∧ 2 * δ ≤ |ρ.re - 1 / 2| ∧ U ≤ |ρ.im| ∧ |ρ.im| ≤ 2 * U) →
      ∑ ρ ∈ S, (zeroMult ρ : ℝ) ≤ B * (Real.log (2 * U + 4) ^ 2 * U ^ (1 - δ ^ 2 / 3)) := by
  classical
  obtain ⟨B, hB⟩ := shell_card_le hδ hδ'
  set K := 16 / Real.log (21 / 20)
  have hK : 0 < K := div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨4 * max B 0 * K, by positivity, fun U hU S hS => ?_⟩
  set L := Real.log (2 * U + 4)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hm : ∀ ρ ∈ S, (zeroMult ρ : ℝ) ≤ K * L := fun ρ hρ => by
    obtain ⟨⟨-, h0, h1⟩, -, -, h2⟩ := hS ρ hρ
    have := window_zero_count ρ.im {ρ} (by simp [h0, h1])
    rw [Finset.sum_singleton] at this
    exact this.trans (by gcongr; exact Real.log_le_log (by positivity) (by linarith))
  have himg := hB U hU (S.image fold) fun w hw => by
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨h0, h1, h2, h3⟩ := hS ρ hρ
    exact ⟨fold_mem h0, by simp only [fold]; linarith, h2, h3⟩
  have hcard : S.card ≤ 4 * (S.image fold).card := Finset.card_le_mul_card_image _ _ fun w _ =>
    (Finset.card_le_card (t := {w, conj w, 1 - conj w, 1 - w}) fun ρ hρ => by
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hρ
      exact mem_of_fold_eq ρ).trans Finset.card_le_four
  have hP : 0 ≤ L * U ^ (1 - δ ^ 2 / 3) := by positivity
  calc ∑ ρ ∈ S, (zeroMult ρ : ℝ) ≤ ∑ _ρ ∈ S, K * L := Finset.sum_le_sum hm
    _ = S.card * (K * L) := by simp
    _ ≤ (4 * (S.image fold).card : ℕ) * (K * L) := by gcongr
    _ ≤ 4 * (max B 0 * (L * U ^ (1 - δ ^ 2 / 3))) * (K * L) := by
        push_cast
        gcongr
        exact himg.trans (by gcongr; exact le_max_left _ _)
    _ = _ := by ring

/-- **Exterior zeros counted with multiplicity.** For `a > 0` and `δ = min (a / 2) (1 / 8)`, the
zeros in the open critical strip at distance at least `a` from the critical line and of height at
most `X ≥ 2`, counted with multiplicity in any finite family, number at most
`A X^{1-δ²/3} log² (2X + 4)`. -/
theorem exterior_mult_le {a : ℝ} (ha : 0 < a) :
    ∃ A, 0 ≤ A ∧ ∀ X : ℝ, 2 ≤ X → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2| ∧ |ρ.im| ≤ X) →
      ∑ ρ ∈ S, (zeroMult ρ : ℝ) ≤
        A * (X ^ (1 - min (a / 2) (1 / 8) ^ 2 / 3) * Real.log (2 * X + 4) ^ 2) := by
  classical
  set δ := min (a / 2) (1 / 8)
  set c := 1 - δ ^ 2 / 3
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ' : δ ≤ 1 / 8 := min_le_right _ _
  have h2δ : 2 * δ ≤ a := by linarith [min_le_left (a / 2) (1 / 8)]
  have hc : 0 < c := by simp only [c]; nlinarith
  obtain ⟨B, hB0, hB⟩ := shell_mult_le hδ hδ'
  have hF : {ρ | ρ ∈ stripZeros ∧ |ρ.im| ≤ 4}.Finite := by
    have K := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm
      (isCompact_Icc (a := (-4 : ℝ)) (b := 4))
    exact K.inter_riemannZetaZeros_finite.subset fun ρ h =>
      ⟨⟨⟨h.1.2.1.le, h.1.2.2.le⟩, abs_le.mp h.2⟩, h.1.1⟩
  set N := ∑ ρ ∈ hF.toFinset, (zeroMult ρ : ℝ)
  have h2c : 1 < (2 : ℝ) ^ c := Real.one_lt_rpow (by norm_num) hc
  set A := max N (B / (2 ^ c - 1))
  have hA : 0 ≤ A := (le_max_right _ _).trans' (div_nonneg hB0 (by linarith))
  have hAB : B ≤ A * (2 ^ c - 1) := by
    rw [← div_le_iff₀ (by linarith)]; exact le_max_right _ _
  refine ⟨A, hA, ?_⟩
  -- the claim at every `X ∈ [2, 4]`
  have base : ∀ X : ℝ, 2 ≤ X → X ≤ 4 → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2| ∧ |ρ.im| ≤ X) →
      ∑ ρ ∈ S, (zeroMult ρ : ℝ) ≤ A * (X ^ c * Real.log (2 * X + 4) ^ 2) := by
    intro X hX hX4 S hS
    have h1 : 1 ≤ X ^ c * Real.log (2 * X + 4) ^ 2 := by
      have hl : 1 ≤ Real.log (2 * X + 4) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        linarith [Real.exp_one_lt_d9]
      have hx : 1 ≤ X ^ c := Real.one_le_rpow (by linarith) hc.le
      nlinarith
    calc ∑ ρ ∈ S, (zeroMult ρ : ℝ) ≤ N :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => by
            obtain ⟨h0, -, h2⟩ := hS ρ hρ
            exact hF.mem_toFinset.2 ⟨h0, h2.trans hX4⟩) fun _ _ _ => Nat.cast_nonneg _
      _ ≤ A * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ _ := by gcongr
  have step : ∀ n : ℕ, ∀ X : ℝ, 2 ≤ X → X ≤ 4 * 2 ^ n → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ stripZeros ∧ a ≤ |ρ.re - 1 / 2| ∧ |ρ.im| ≤ X) →
      ∑ ρ ∈ S, (zeroMult ρ : ℝ) ≤ A * (X ^ c * Real.log (2 * X + 4) ^ 2) := by
    intro n
    induction n with
    | zero => intro X hX hX4 S hS; exact base X hX (by simpa using hX4) S hS
    | succ n ih =>
      intro X hX hXn S hS
      rcases le_or_gt X 4 with hX4 | hX4
      · exact base X hX hX4 S hS
      set L := Real.log (2 * X + 4)
      have hL : 0 ≤ L := Real.log_nonneg (by linarith)
      have hpow : (X / 2) ^ c = X ^ c / 2 ^ c := Real.div_rpow (by linarith) (by norm_num) c
      have hlow := ih (X / 2) (by linarith) (by rw [pow_succ] at hXn; linarith)
        (S.filter fun ρ => |ρ.im| ≤ X / 2) fun ρ hρ => by
          obtain ⟨hρ, h⟩ := Finset.mem_filter.1 hρ
          exact ⟨(hS ρ hρ).1, (hS ρ hρ).2.1, h⟩
      have hhigh := hB (X / 2) (by linarith) (S.filter fun ρ => ¬ |ρ.im| ≤ X / 2) fun ρ hρ => by
          obtain ⟨hρ, h⟩ := Finset.mem_filter.1 hρ
          obtain ⟨h0, h1, h2⟩ := hS ρ hρ
          exact ⟨h0, h2δ.trans h1, (not_le.1 h).le, by linarith⟩
      have hl1 : Real.log (2 * (X / 2) + 4) ≤ L := Real.log_le_log (by linarith) (by linarith)
      have hl1' : Real.log (2 * (X / 2) + 4) ^ 2 ≤ L ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hl1 2
      rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => |ρ.im| ≤ X / 2)]
      have hXc : 0 ≤ X ^ c / 2 ^ c := by positivity
      calc _ ≤ A * (X ^ c / 2 ^ c * L ^ 2) + B * (L ^ 2 * (X ^ c / 2 ^ c)) := by
            gcongr
            · exact hlow.trans (by rw [hpow]; gcongr)
            · exact hhigh.trans (by rw [hpow]; gcongr)
        _ = (A + B) / 2 ^ c * (X ^ c * L ^ 2) := by ring
        _ ≤ A * (X ^ c * L ^ 2) := by
            gcongr
            rw [div_le_iff₀ (by linarith)]
            linarith
  intro X hX S hS
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (X / 4) (by norm_num : (1 : ℝ) < 2)
  exact step n X hX (by linarith) S hS

end WeilExplicit
