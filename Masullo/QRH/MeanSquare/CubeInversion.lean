import Masullo.QRH.MeanSquare.GaussProduct
import Masullo.QRH.MeanSquare.UnitRows

/-! # Finite Möbius inversion of the cube completion -/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid Finset
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

def cubeNorm (n : Ideal 𝓔) : ℝ := (absNorm n : ℝ) ^ 3

def cubeWeight (ξ : RayCharacter) (k : 𝓔) (f n : Ideal 𝓔) : ℂ :=
  (conj (angularFactor n) * twist ξ k f n) ^ 3 / (absNorm n : ℂ)

def normalizedColumn (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔) (f : Ideal 𝓔) : ℂ :=
  columnSum ξ W X k f / Real.sqrt X

open Classical in
def cubeIdeals (T : ℝ) : Finset (Ideal 𝓔) :=
  (idealsLe T).filter (fun n => AwayFromSix n ∧ cubeNorm n ≤ T)

lemma absNorm_one_le {n : Ideal 𝓔} (hn : n ≠ ⊥) : 1 ≤ (absNorm n : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hn)

lemma cubeNorm_one_le {n : Ideal 𝓔} (hn : AwayFromSix n) : 1 ≤ cubeNorm n :=
  one_le_pow₀ (absNorm_one_le hn.1)

lemma mem_cubeIdeals {T : ℝ} {n : Ideal 𝓔} :
    n ∈ cubeIdeals T ↔ AwayFromSix n ∧ cubeNorm n ≤ T := by
  classical
  rw [cubeIdeals, mem_filter, and_iff_right_of_imp]
  rintro ⟨hn, h⟩
  have h₁ := absNorm_one_le hn.1
  have h₂ : (absNorm n : ℝ) ≤ cubeNorm n := by
    exact le_self_pow₀ h₁ (by decide : 3 ≠ 0)
  exact (mem_idealsLe (zero_le_one.trans (h₁.trans (h₂.trans h)))).mpr (h₂.trans h)

@[simp] lemma cubeNorm_mul (a b : Ideal 𝓔) : cubeNorm (a * b) = cubeNorm a * cubeNorm b := by
  simp [cubeNorm, mul_pow]

@[simp] lemma cubeNorm_one : cubeNorm (1 : Ideal 𝓔) = 1 := by simp [cubeNorm]

private lemma away_one : AwayFromSix (1 : Ideal 𝓔) := ⟨by simp, isCoprime_one_left⟩

theorem cubeWeight_mul (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) {a b : Ideal 𝓔}
    (ha : AwayFromSix a) (hb : AwayFromSix b) :
    cubeWeight ξ k f (a * b) = cubeWeight ξ k f a * cubeWeight ξ k f b := by
  classical
  simp only [cubeWeight, twist, ite_eq_left (ha.mul hb), ite_eq_left ha, ite_eq_left hb,
    angularFactor_mul ha hb, map_mul, generator_mul ha.coprime_three hb.coprime_three,
    sextic, powerResidueSymbol_mul_right, Nat.cast_mul]
  ring

@[simp] lemma cubeWeight_one (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) : cubeWeight ξ k f 1 = 1 := by
  classical
  rw [cubeWeight, twist, ite_eq_left away_one, angularFactor, generator_one]
  simp [sextic, Ideal.one_eq_top]

/-- Compact support truncates the completing ideal before Möbius inversion. -/
theorem completedSum_eq_sum_cubeIdeals {I : TestInterval} {j : ℕ} {W : ℝ → ℂ}
    (hW : UnitTest I j W) {X : ℝ} (hX : 0 < X) (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) :
    completedSum ξ W X k f = ∑ b ∈ cubeIdeals (max I.hi 1 * X),
      cubeWeight ξ k f b * normalizedColumn ξ W (X / cubeNorm b) k f := by
  classical
  let S := cubeIdeals (max I.hi 1 * X)
  let t := S.preimage (Subtype.val : {b : Ideal 𝓔 // AwayFromSix b} → Ideal 𝓔) Subtype.val_injective.injOn
  change (∑ᶠ b : {b : Ideal 𝓔 // AwayFromSix b}, cubeWeight ξ k f b *
    normalizedColumn ξ W (X / cubeNorm b) k f) = _
  rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
  · apply sum_bij (fun b _ => b.val)
    · exact fun _ hb => Finset.mem_preimage.mp hb
    · exact fun _ _ _ _ he => Subtype.ext he
    · intro b hb
      exact ⟨⟨b, (mem_cubeIdeals.mp hb).1⟩, mem_preimage.mpr hb, rfl⟩
    · intros; rfl
  · intro b hb
    apply mem_preimage.mpr
    apply mem_cubeIdeals.mpr
    refine ⟨b.2, le_of_not_gt ?_⟩
    intro h
    have hN := lt_of_lt_of_le zero_lt_one (cubeNorm_one_le b.2)
    have hs : I.hi * (X / cubeNorm b) < 1 := by
      rw [← mul_div_assoc, div_lt_one hN]
      exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hX.le).trans_lt h
    exact (Function.mem_support.mp hb) (by
      simp only [normalizedColumn, columnSum_eq_zero_of_short hW (div_pos hX hN) hs, zero_div, mul_zero])

open Classical in
/-- Sum the ideal Möbius function over the divisors of a nonzero ideal. The
ambient finite set need only contain every divisor. -/
theorem sum_idealMoebius_dividing {n : Ideal 𝓔} (hn : n ≠ 0) (S : Finset (Ideal 𝓔))
    (hS : ∀ b, b ∣ n → b ∈ S) :
    ∑ b ∈ S with b ∣ n, idealMoebius b = if n = 1 then 1 else 0 := by
  classical
  let P := (normalizedFactors n).toFinset
  have hN {T : Finset (Ideal 𝓔)} (hT : T ⊆ P) : normalizedFactors (∏ p ∈ T, p) = T.val := by
    rw [prod_eq_multiset_prod, Multiset.map_id']
    exact normalizedFactors_prod_of_prime fun p hp => prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (hT hp))
  have h₀ {T : Finset (Ideal 𝓔)} (hT : T ⊆ P) : ∏ p ∈ T, p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ hp => (prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (hT hp))).ne_zero
  have hsum : ∑ T ∈ P.powerset, (-1 : ℤ) ^ T.card = ∑ b ∈ S with b ∣ n, idealMoebius b := by
    refine Finset.sum_bij_ne_zero (fun T _ _ => ∏ p ∈ T, p) ?_ ?_ ?_ ?_
    · intro T hT _
      have hsub := mem_powerset.mp hT
      have hd : (∏ p ∈ T, p) ∣ n := (dvd_iff_normalizedFactors_le_normalizedFactors (h₀ hsub) hn).mpr (by
        rw [hN hsub]
        exact (Finset.val_le_iff.mpr hsub).trans (Multiset.dedup_le _))
      exact mem_filter.mpr ⟨hS _ hd, hd⟩
    · intro T hT _ U hU _ he
      exact Finset.val_inj.mp ((hN (mem_powerset.mp hT)).symm.trans
        ((congrArg normalizedFactors he).trans (hN (mem_powerset.mp hU))))
    · intro b hb hne
      have hd := (mem_filter.mp hb).2
      have hsf : Squarefree b := by_contra fun h => hne (by simp [idealMoebius, h])
      have hnd := (squarefree_iff_nodup_normalizedFactors hsf.ne_zero).mp hsf
      let T := (normalizedFactors b).toFinset
      have hsub : T ⊆ P := Multiset.toFinset_subset.mpr
        (Multiset.subset_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors hsf.ne_zero hn).mp hd))
      refine ⟨T, mem_powerset.mpr hsub, by simp, ?_⟩
      rw [prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup]
      exact associated_iff_eq.mp (prod_normalizedFactors hsf.ne_zero)
    · intro T hT _
      have hsub := mem_powerset.mp hT
      have hsf := (squarefree_iff_nodup_normalizedFactors (h₀ hsub)).mpr (hN hsub ▸ T.nodup)
      simp [idealMoebius, hsf, hN hsub]
  have hP : P = ∅ ↔ n = 1 := by
    constructor
    · intro h
      have he : normalizedFactors n = 0 := Multiset.toFinset_eq_empty.mp h
      simpa [he] using (associated_iff_eq.mp (prod_normalizedFactors hn)).symm
    · rintro rfl
      simp only [P, normalizedFactors_one, Multiset.toFinset_zero]
  rw [← hsum, Finset.sum_powerset_neg_one_pow_card]
  simp only [hP]

theorem mem_cubeIdeals_of_dvd {b n : Ideal 𝓔} {Y : ℝ} (hd : b ∣ n) (hn : n ∈ cubeIdeals Y) :
    b ∈ cubeIdeals Y := by
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨⟨h₀, hc⟩, hY⟩ := mem_cubeIdeals.mp hn
  have hb : AwayFromSix b := ⟨left_ne_zero_of_mul h₀, hc.of_mul_left_left⟩
  have hd : AwayFromSix d := ⟨right_ne_zero_of_mul h₀, hc.of_mul_left_right⟩
  rw [cubeNorm_mul] at hY
  exact mem_cubeIdeals.mpr ⟨hb, (le_mul_of_one_le_right (zero_le_one.trans (cubeNorm_one_le hb))
    (cubeNorm_one_le hd)).trans hY⟩

open Classical in
private theorem sum_cube_factors {Y : ℝ} {b : Ideal 𝓔} (hb : AwayFromSix b)
    (v : Ideal 𝓔 → ℂ) :
    ∑ d ∈ cubeIdeals (Y / cubeNorm b), v (b * d) =
      ∑ n ∈ cubeIdeals Y with b ∣ n, v n := by
  classical
  have hpos : 0 < cubeNorm b := zero_lt_one.trans_le (cubeNorm_one_le hb)
  apply sum_bij (fun d _ => b * d)
  · intro d hd
    obtain ⟨hgd, hdY⟩ := mem_cubeIdeals.mp hd
    refine mem_filter.mpr ⟨mem_cubeIdeals.mpr ⟨hb.mul hgd, ?_⟩, dvd_mul_right b d⟩
    rwa [cubeNorm_mul, mul_comm, ← le_div_iff₀ hpos]
  · intro a _ c _ he
    exact mul_left_cancel₀ hb.1 he
  · intro n hn
    obtain ⟨hn, ⟨d, rfl⟩⟩ := mem_filter.mp hn
    obtain ⟨⟨h₀, hc⟩, hY⟩ := mem_cubeIdeals.mp hn
    refine ⟨d, mem_cubeIdeals.mpr ⟨⟨right_ne_zero_of_mul h₀, hc.of_mul_left_right⟩, ?_⟩, rfl⟩
    rwa [le_div_iff₀ hpos, mul_comm, ← cubeNorm_mul]
  · intros; rfl

/-- All completing products with cube norm at most `Y` cancel except the unit ideal. -/
private theorem sum_moebius_cube_factors {Y : ℝ} (hY : 1 ≤ Y) (v : Ideal 𝓔 → ℂ) :
    ∑ b ∈ cubeIdeals Y, ∑ d ∈ cubeIdeals (Y / cubeNorm b), (idealMoebius b : ℂ) * v (b*d) = v 1 := by
  classical
  have hf := Finset.sum_congr (s₁ := cubeIdeals Y) rfl (fun b hb =>
    sum_cube_factors (Y := Y) (mem_cubeIdeals.mp hb).1 (fun n => (idealMoebius b : ℂ) * v n))
  rw [hf]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  have he (n : Ideal 𝓔) (hn : n ∈ cubeIdeals Y) :
      ∑ b ∈ cubeIdeals Y, (if b ∣ n then (idealMoebius b : ℂ) * v n else 0) =
        if n = 1 then v n else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    have h := sum_idealMoebius_dividing (mem_cubeIdeals.mp hn).1.1 (cubeIdeals Y)
      (fun _ hd => mem_cubeIdeals_of_dvd hd hn)
    rw [← Int.cast_sum, h]
    split_ifs <;> simp
  rw [sum_congr rfl he, Finset.sum_ite_eq']
  simp only [mem_cubeIdeals, away_one, cubeNorm_one, hY, and_self, ite_true]

theorem norm_cubeWeight_le (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) {n : Ideal 𝓔}
    (hn : AwayFromSix n) : ‖cubeWeight ξ k f n‖ ≤ (absNorm n : ℝ)⁻¹ := by
  rw [cubeWeight, norm_div, norm_pow, norm_mul, Complex.norm_conj, norm_angularFactor_eq_one hn.1,
    one_mul, Complex.norm_natCast, ← one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact pow_le_one₀ (norm_nonneg _) (norm_twist_le_one ξ k f n)

theorem norm_moebius_cubeWeight_le (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) {n : Ideal 𝓔}
    (hn : AwayFromSix n) : ‖(idealMoebius n : ℂ) * cubeWeight ξ k f n‖ ≤ (absNorm n : ℝ)⁻¹ := by
  have hμ : ‖(idealMoebius n : ℂ)‖ ≤ 1 := by
    classical
    unfold idealMoebius
    split_ifs <;> simp
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hμ).trans (norm_cubeWeight_le ξ k f hn)

open Classical in
/-- Invert the completion up to cube norm `Y`. The remaining uncompleted columns
have product cube norm strictly above `Y` and at most the support cutoff. -/
theorem truncated_cube_inversion {I : TestInterval} {j : ℕ} {W : ℝ → ℂ} (hW : UnitTest I j W)
    {X Y : ℝ} (hX : 0 < X) (hY : 1 ≤ Y) (hYX : Y ≤ max I.hi 1 * X)
    (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) :
    normalizedColumn ξ W X k f =
      (∑ b ∈ cubeIdeals Y, (idealMoebius b : ℂ) * cubeWeight ξ k f b *
        completedSum ξ W (X / cubeNorm b) k f) -
      ∑ b ∈ cubeIdeals Y,
        ∑ d ∈ (cubeIdeals (max I.hi 1 * X / cubeNorm b)).filter (fun d => Y < cubeNorm (b * d)),
          (idealMoebius b : ℂ) * cubeWeight ξ k f b * cubeWeight ξ k f d *
            normalizedColumn ξ W (X / cubeNorm (b * d)) k f := by
  classical
  let R := max I.hi 1
  let w := cubeWeight ξ k f
  let V := fun n => normalizedColumn ξ W (X / cubeNorm n) k f
  let G := fun b d => (idealMoebius b : ℂ) * w b * w d * V (b * d)
  have hsplit (b : Ideal 𝓔) (hb : b ∈ cubeIdeals Y) :
      (idealMoebius b : ℂ) * w b * completedSum ξ W (X / cubeNorm b) k f =
        (∑ d ∈ cubeIdeals (Y / cubeNorm b), G b d) +
        ∑ d ∈ (cubeIdeals (R * X / cubeNorm b)).filter (fun d => Y < cubeNorm (b * d)), G b d := by
    have hpos : 0 < cubeNorm b := zero_lt_one.trans_le (cubeNorm_one_le (mem_cubeIdeals.mp hb).1)
    have hset : (cubeIdeals (R * X / cubeNorm b)).filter (fun d => cubeNorm (b * d) ≤ Y) =
        cubeIdeals (Y / cubeNorm b) := by
      ext d
      simp only [mem_filter, mem_cubeIdeals, cubeNorm_mul, le_div_iff₀ hpos, mul_comm (cubeNorm b)]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hYX⟩, h.2⟩⟩
    have hsum := Finset.sum_filter_add_sum_filter_not (cubeIdeals (R * X / cubeNorm b))
      (fun d => cubeNorm (b * d) ≤ Y) (G b)
    simp only [hset, not_le] at hsum
    rw [hsum, completedSum_eq_sum_cubeIdeals hW (div_pos hX hpos), Finset.mul_sum]
    change (∑ d ∈ cubeIdeals (R * (X / cubeNorm b)), _) = _
    rw [← mul_div_assoc]
    apply sum_congr rfl
    intro d _
    dsimp only [G, w, V]
    rw [cubeNorm_mul, ← div_div]
    ring
  have hc := Finset.sum_congr rfl hsplit
  rw [sum_add_distrib] at hc
  have hcanc : ∑ b ∈ cubeIdeals Y, ∑ d ∈ cubeIdeals (Y / cubeNorm b), G b d =
      normalizedColumn ξ W X k f := by
    calc
      _ = ∑ b ∈ cubeIdeals Y, ∑ d ∈ cubeIdeals (Y / cubeNorm b),
          (idealMoebius b : ℂ) * (w (b*d) * V (b*d)) := by
        apply sum_congr rfl
        intro b hb
        apply sum_congr rfl
        intro d hd
        dsimp only [G, w]
        rw [cubeWeight_mul _ _ _ (mem_cubeIdeals.mp hb).1 (mem_cubeIdeals.mp hd).1]
        ring
      _ = w 1 * V 1 := sum_moebius_cube_factors hY (fun n => w n * V n)
      _ = _ := by dsimp only [w, V]; rw [cubeWeight_one, cubeNorm_one, div_one, one_mul]
  rw [hcanc] at hc
  exact eq_sub_of_add_eq hc.symm

end Masullo.QRH.MeanSquare
