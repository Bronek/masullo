import Masullo.QRH.MeanSquare.Transfer
import Masullo.QRH.MeanSquare.TransferDilation
import Masullo.QRH.MeanSquare.DualTail
import Masullo.QRH.MeanSquare.TransferExpand
import Masullo.QRH.MeanSquare.GaussNorm
import Masullo.QRH.MeanSquare.OffDiagonal

/-!
# The children of the second Poisson pass

The second pass ends in coprime columns `columnSumCoprime ζ U (L/(Nr Nf)) k f r` of length
depending on `f`. Dyadic blocks in `Nf`, the dilation bound, the removal of the coprimality
and the children hypothesis bound them.

* `UnitTest.enlarge_of_halve`: a test on `I.halve` is a test on `I.enlarge`.
* `exists_coprimeBlocks_le`: the sum over `f` and the rows `k` of the coprime columns is
  bounded by the number of dyadic blocks, the divisor loss of `r`, `1 + B` and `(L/Nr)²`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

lemma UnitTest.enlarge_of_halve {I : TestInterval} {m : ℕ} {V : ℝ → ℂ}
    (hV : UnitTest I.halve m V) : UnitTest I.enlarge m V := by
  have h1 : Set.Icc I.halve.lo I.halve.hi ⊆ Set.Icc I.enlarge.lo I.enlarge.hi := by
    apply Set.Icc_subset_Icc
    · show I.lo / 16 ≤ I.lo / 2
      linarith [I.pos]
    · show I.hi ≤ 4 * I.hi
      linarith [I.pos, I.ordered]
  refine ⟨hV.1, hV.2.1.trans h1, fun j hj x _ => ?_⟩
  by_cases hx : x ∈ Set.Icc I.halve.lo I.halve.hi
  · exact hV.2.2 j hj x hx
  · rw [image_eq_zero_of_notMem_tsupport
      (fun h => hx (hV.2.1 (tsupport_iteratedDeriv_subset V j h))), norm_zero]
    exact zero_le_one

/-- The coprime column as a finite sum over any finite set of starred ideals containing the
support. -/
private lemma blockColumnSum_eq (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔)
    (f r : Ideal 𝓔) (S : Finset (Ideal 𝓔)) (hS : ∀ n ∈ S, Starred n)
    (hsupp : ∀ n, Starred n → W (absNorm n / X) ≠ 0 → n ∈ S) :
    columnSumCoprime ξ W X k f r = ∑ n ∈ S,
      (open Classical in if IsCoprime n r then gaussCoefficient n * twist ξ k f n else 0) *
        W (absNorm n / X) := by
  classical
  unfold columnSumCoprime
  have hsub : (Function.support fun n : {n : Ideal 𝓔 // Starred n} =>
      if IsCoprime n.1 r then gaussCoefficient n * twist ξ k f n * W (absNorm n.1 / X) else 0) ⊆
      ↑(S.subtype Starred) := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_subtype]
    refine hsupp n.1 n.2 fun h0 => hn ?_
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine (Finset.sum_subtype_eq_sum_filter (s := S) (p := Starred)
    (f := fun n : Ideal 𝓔 => if IsCoprime n r then
      gaussCoefficient n * twist ξ k f n * W (absNorm n / X) else 0)).trans ?_
  rw [Finset.filter_true_of_mem hS]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : IsCoprime n r <;> simp [h]

/-- The dyadic block of norms in `[F, 2F)`, as in `dualMeanSquare`. -/
private abbrev dyadicBlock (F : ℝ) : Finset (Ideal 𝓔) := open Classical in
  (idealsLe (2 * F)).filter (fun f =>
    Starred f ∧ F ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * F)

/-- Every shifted form `E(K*, X'', F'')` of a block is at most `(C₁ + B) Σ'`. -/
private lemma shifted_form_le {I : TestInterval} {m : ℕ} {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (h₁ : ∀ (K X F : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
      1 ≤ K → 0 < X → 1 ≤ F → UnitTest I.halve 0 W → dualMeanSquare ξ W K X F ≤ C₁ * (K * X))
    {K L F target B Nr : ℝ} {ζ : RayCharacter} (hK : 0 < K) (hL : 1 ≤ L) (hF : 1 ≤ F)
    (hKt : K ≤ target) (hB : 0 ≤ B) (hNr : 1 ≤ Nr)
    (hch : TransferChildren I m K L F target B) {V : ℝ → ℂ} (hV : UnitTest I.halve m V)
    {X'' F'' : ℝ} (hX : 0 < X'') (hF'' : 1 ≤ F'') (hXF : X'' * F'' = L / Nr) :
    dualMeanSquare ζ V (K * L / (target * F * Nr ^ 2)) X'' F'' ≤ (C₁ + B) * (L / Nr) := by
  have ht : 0 < target := lt_of_lt_of_le hK hKt
  have hS : 0 < L / Nr := by positivity
  set Ks := K * L / (target * F * Nr ^ 2) with hKs
  by_cases ha : Ks < 1
  · have : dualMeanSquare ζ V Ks X'' F'' = 0 := by
      simp [dualMeanSquare, elementRows_eq_empty ha]
    rw [this]; positivity
  push Not at ha
  by_cases hb : X'' < 1
  · refine (h₁ Ks X'' F'' ζ V ha hX hF'' (hV.of_le (Nat.zero_le m))).trans ?_
    have hKS : Ks ≤ L / Nr := by
      rw [hKs, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : K * L ≤ target * L := by gcongr
      have h2 : target * L * Nr ≤ L * (target * F * Nr ^ 2) := by
        have : 1 ≤ F * Nr := one_le_mul_of_one_le_of_one_le hF hNr
        nlinarith [mul_pos ht (by linarith : 0 < L), mul_pos (mul_pos ht (by linarith : 0 < L))
          (by linarith : 0 < Nr)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Nr) (by linarith : (0 : ℝ) ≤ L)]
    have : C₁ * (Ks * X'') ≤ C₁ * (L / Nr) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₁
      calc Ks * X'' ≤ Ks * 1 := by gcongr
        _ ≤ L / Nr := by rwa [mul_one]
    nlinarith [mul_nonneg hB hS.le]
  · push Not at hb
    have hK' : Ks ≤ K * L / (target * F) := by
      rw [hKs]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [mul_pos ht (by linarith : 0 < F), one_le_pow₀ (n := 2) hNr])
    have hK'' : Ks / (X'' * F'') ≤ K / target := by
      rw [hXF, hKs, div_div, div_le_div_iff₀ (by positivity) ht]
      have hNN : 0 < Nr := by linarith
      have h3 : target * F * Nr ^ 2 * (L / Nr) = target * L * (F * Nr) := by
        field_simp
      have h4 : 1 ≤ F * Nr := one_le_mul_of_one_le_of_one_le hF hNr
      rw [h3]
      have : 0 ≤ K * (target * L) := by positivity
      nlinarith
    have hle : X'' * F'' ≤ L := by
      rw [hXF]; exact div_le_self (by linarith) hNr
    have := hch Ks X'' F'' ζ V ha hb hF'' hK' hK'' hle hV.enlarge_of_halve
    rw [hXF] at this
    nlinarith [mul_nonneg hC₁ hS.le]

/-- One dyadic block of the sum over `f`. -/
private lemma exists_coprimeBlock_le (hpg : PairedGaussIdentities) (I : TestInterval) (m : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ (K L F target B : ℝ) (ζ : RayCharacter) (U : ℝ → ℂ) (r : Ideal 𝓔) (i : ℕ),
      0 < K → 1 ≤ L → 1 ≤ F → K ≤ target → 0 ≤ B → TransferChildren I m K L F target B →
      UnitTest I (m + 1) U → Starred r →
      ∑ f ∈ (starredLe (I.hi * L / absNorm r)).filter (fun f => Nat.log 2 (absNorm f) = i),
          ∑ k ∈ elementRows (K * L / (target * F * (absNorm r : ℝ) ^ 2)),
            ‖columnSumCoprime ζ U (L / (absNorm r * absNorm f)) k f r‖ ^ 2 ≤
        C * 4 ^ Multiset.card (normalizedFactors r) * (1 + B) * (L / absNorm r) ^ 2 := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := dualMeanSquare_le_mul gaussCoefficientBound I.halve
  obtain ⟨Cd, hCd, hd⟩ := exists_dilated_meanSquare_le I m
  refine ⟨Cd * (C₁ + 1), by positivity, ?_⟩
  intro K L F target B ζ U r i hK hL hF hKt hB hch hU hr
  have hNr : (1 : ℝ) ≤ absNorm r := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hr.1.1)
  set Nr : ℝ := (absNorm r : ℝ) with hNrdef
  set Fp : ℝ := 2 ^ i with hFpdef
  have hFp : 1 ≤ Fp := one_le_pow₀ (by norm_num)
  have hL0 : 0 < L := by linarith
  have hNr0 : 0 < Nr := by linarith
  have hhi : 0 < I.hi := lt_of_lt_of_le I.pos I.ordered
  set Xb : ℝ := L / (Nr * Fp) with hXbdef
  have hXb : 0 < Xb := by positivity
  set Sg : ℝ := L / Nr with hSgdef
  have hSg : 0 < Sg := by positivity
  have hXF : Xb * Fp = Sg := by rw [hXbdef, hSgdef]; field_simp
  set Ks : ℝ := K * L / (target * F * Nr ^ 2) with hKsdef
  have hE : ∀ V, UnitTest I.halve m V →
      dualMeanSquareCoprime ζ V Ks Xb Fp r ≤ 4 ^ Multiset.card (normalizedFactors r) *
        ((C₁ + B) * Sg) := by
    intro V hV
    refine dualMeanSquareCoprime_le_of_forall hpg gaussCoefficientBound residueMultiplicative
      (R := I.hi) (fun x hx => (hV.2.1 (subset_tsupport V hx)).2) hr hXb (by linarith) ?_
    intro t htr
    have ht : (1 : ℝ) ≤ absNorm t.prod := by
      have h0 : t.prod ≠ ⊥ := Multiset.prod_ne_zero fun h0 =>
        (prime_of_normalized_factor _ (Multiset.mem_of_le htr h0)).ne_zero rfl
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr h0)
    refine shifted_form_le hC₁ h₁ hK hL hF hKt hB hNr hch hV (by positivity)
      (one_le_mul_of_one_le_of_one_le hFp ht) ?_
    rw [← hSgdef, ← hXF]
    field_simp
  -- the dilation data
  set cols : Finset (Ideal 𝓔) := starredLe (I.hi * Xb) with hcols
  have hcolsS : ∀ n ∈ cols, Starred n := fun n hn =>
    ((mem_starredLe (by positivity)).mp hn).2
  let c : Ideal 𝓔 × 𝓔 → Ideal 𝓔 → ℂ := fun ρ n =>
    if IsCoprime n r then gaussCoefficient n * twist ζ ρ.2 ρ.1 n else 0
  let x : Ideal 𝓔 → ℝ := fun n => absNorm n / Xb
  let d : Ideal 𝓔 × 𝓔 → ℝ := fun ρ => absNorm ρ.1 / Fp
  have hcolV : ∀ V : ℝ → ℂ, (∀ y, V y ≠ 0 → y ≤ I.hi) → ∀ (f : Ideal 𝓔) (k : 𝓔),
      ∑ n ∈ cols, c (f, k) n * V (x n) = columnSumCoprime ζ V Xb k f r := by
    intro V hV f k
    rw [blockColumnSum_eq ζ V Xb k f r cols hcolsS]
    intro n _ hn
    refine (mem_starredLe (by positivity)).mpr ⟨?_, ‹Starred n›⟩
    have := hV _ hn
    rw [div_le_iff₀ hXb] at this
    linarith
  have hDmem : ∀ f ∈ dyadicBlock Fp,
      Starred f ∧ Fp ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * Fp := fun f hf =>
    (Finset.mem_filter.mp hf).2
  -- the undilated hypothesis
  have hH : ∀ V, UnitTest I.halve m V →
      ∑ ρ ∈ dyadicBlock Fp ×ˢ elementRows Ks, ‖∑ n ∈ cols, c ρ n * V (x n)‖ ^ 2 ≤
        Sg * (4 ^ Multiset.card (normalizedFactors r) * ((C₁ + B) * Sg)) := by
    intro V hV
    have hW : ∀ y, V y ≠ 0 → y ≤ I.hi := fun y hy => (hV.2.1 (subset_tsupport V hy)).2
    have h1 : ∑ ρ ∈ dyadicBlock Fp ×ˢ elementRows Ks, ‖∑ n ∈ cols, c ρ n * V (x n)‖ ^ 2 =
        Sg * dualMeanSquareCoprime ζ V Ks Xb Fp r := by
      rw [Finset.sum_product]
      unfold dualMeanSquareCoprime
      rw [← hXF, mul_div_cancel₀ _ (by positivity)]
      refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hcolV V hW f k]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hE V hV) hSg.le
  have hdil : ∀ ρ ∈ dyadicBlock Fp ×ˢ elementRows Ks, d ρ ∈ Set.Icc (1 : ℝ) 2 := by
    intro ρ hρ
    obtain ⟨-, h1, h2⟩ := hDmem ρ.1 (Finset.mem_product.mp hρ).1
    constructor
    · exact (one_le_div (by positivity)).mpr h1
    · rw [div_le_iff₀ (by positivity)]
      linarith
  have hmain := hd (dyadicBlock Fp ×ˢ elementRows Ks) cols c x d hdil hH U hU
  have hUsupp : ∀ y, U y ≠ 0 → y ≤ I.hi := fun y hy => (hU.2.1 (subset_tsupport U hy)).2
  have hrows : ∑ ρ ∈ dyadicBlock Fp ×ˢ elementRows Ks, ‖∑ n ∈ cols, c ρ n * U (d ρ * x n)‖ ^ 2 =
      ∑ f ∈ dyadicBlock Fp, ∑ k ∈ elementRows Ks,
        ‖columnSumCoprime ζ U (L / (Nr * absNorm f)) k f r‖ ^ 2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun f hf => Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨-, h1, h2⟩ := hDmem f hf
    have hNf : 0 < (absNorm f : ℝ) := by linarith
    have hlen : 0 < L / (Nr * absNorm f) := by positivity
    rw [blockColumnSum_eq ζ U _ k f r cols hcolsS]
    · refine congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun n _ => ?_)
      have : d (f, k) * x n = absNorm n / (L / (Nr * absNorm f)) := by
        simp only [d, x, hXbdef]
        field_simp
      rw [this]
    · intro n hn hne
      refine (mem_starredLe (by positivity)).mpr ⟨?_, hn⟩
      have := hUsupp _ hne
      rw [div_le_iff₀ hlen] at this
      have h3 : I.hi * (L / (Nr * absNorm f)) ≤ I.hi * Xb := by
        refine mul_le_mul_of_nonneg_left ?_ hhi.le
        rw [hXbdef]
        exact div_le_div_of_nonneg_left hL0.le (by positivity)
          (mul_le_mul_of_nonneg_left h1 hNr0.le)
      linarith
  have hsub : (starredLe (I.hi * L / absNorm r)).filter (fun f => Nat.log 2 (absNorm f) = i) ⊆
      dyadicBlock Fp := by
    intro f hf
    obtain ⟨hf1, hf2⟩ := Finset.mem_filter.mp hf
    have hfs := ((mem_starredLe (by positivity)).mp hf1).2
    have hpos : absNorm f ≠ 0 := absNorm_eq_zero_iff.not.mpr hfs.1.1
    have h1 : 2 ^ i ≤ absNorm f := hf2 ▸ Nat.pow_log_le_self 2 hpos
    have h2 : absNorm f < 2 ^ (i + 1) := hf2 ▸ Nat.lt_pow_succ_log_self (by norm_num) _
    refine Finset.mem_filter.mpr ⟨(mem_idealsLe (by positivity)).mpr ?_, hfs, ?_, ?_⟩
    · have : (absNorm f : ℝ) < 2 * Fp := by
        rw [hFpdef, ← pow_succ']; exact_mod_cast h2
      exact this.le
    · rw [hFpdef]; exact_mod_cast h1
    · rw [hFpdef, ← pow_succ']; exact_mod_cast h2
  have hle1 : ∑ f ∈ (starredLe (I.hi * L / absNorm r)).filter
        (fun f => Nat.log 2 (absNorm f) = i), ∑ k ∈ elementRows Ks,
          ‖columnSumCoprime ζ U (L / (Nr * absNorm f)) k f r‖ ^ 2 ≤
      ∑ f ∈ dyadicBlock Fp, ∑ k ∈ elementRows Ks,
        ‖columnSumCoprime ζ U (L / (Nr * absNorm f)) k f r‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
      Finset.sum_nonneg fun _ _ => by positivity
  refine hle1.trans (hrows ▸ hmain |>.trans ?_)
  have hCB : C₁ + B ≤ (C₁ + 1) * (1 + B) := by nlinarith
  have h4 : (0 : ℝ) ≤ 4 ^ Multiset.card (normalizedFactors r) := by positivity
  calc Cd * (Sg * (4 ^ Multiset.card (normalizedFactors r) * ((C₁ + B) * Sg)))
      = Cd * (4 ^ Multiset.card (normalizedFactors r) * (C₁ + B) * Sg ^ 2) := by ring
    _ ≤ Cd * (4 ^ Multiset.card (normalizedFactors r) * ((C₁ + 1) * (1 + B)) * Sg ^ 2) := by
        gcongr
    _ = _ := by ring

theorem exists_coprimeBlocks_le (hpg : PairedGaussIdentities) (I : TestInterval) (m : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ (K L F target B : ℝ) (ζ : RayCharacter) (U : ℝ → ℂ) (r : Ideal 𝓔),
      0 < K → 1 ≤ L → 1 ≤ F → K ≤ target → 0 ≤ B → TransferChildren I m K L F target B →
      UnitTest I (m + 1) U → Starred r →
      ∑ f ∈ starredLe (I.hi * L / absNorm r),
          ∑ k ∈ elementRows (K * L / (target * F * (absNorm r : ℝ) ^ 2)),
            ‖columnSumCoprime ζ U (L / (absNorm r * absNorm f)) k f r‖ ^ 2 ≤
        C * (Nat.log 2 ⌊I.hi * L⌋₊ + 1) * 4 ^ Multiset.card (normalizedFactors r) * (1 + B) *
          (L / absNorm r) ^ 2 := by
  classical
  obtain ⟨C, hC, h⟩ := exists_coprimeBlock_le hpg I m
  refine ⟨C, hC, fun K L F target B ζ U r hK hL hF hKt hB hch hU hr => ?_⟩
  have hNr : (1 : ℝ) ≤ absNorm r := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr hr.1.1)
  have hhi : 0 < I.hi := lt_of_lt_of_le I.pos I.ordered
  have hL0 : 0 < L := by linarith
  rw [← Finset.sum_fiberwise_of_maps_to (s := starredLe (I.hi * L / absNorm r))
    (t := Finset.range (Nat.log 2 ⌊I.hi * L⌋₊ + 1)) (g := fun f => Nat.log 2 (absNorm f)) ?_]
  · refine (Finset.sum_le_card_nsmul _ _ (C * 4 ^ Multiset.card (normalizedFactors r) * (1 + B) *
      (L / absNorm r) ^ 2) fun i _ => h K L F target B ζ U r i hK hL hF hKt hB hch hU hr).trans ?_
    rw [Finset.card_range, nsmul_eq_mul]
    push_cast
    apply le_of_eq
    ring
  · intro f hf
    obtain ⟨hf1, hfs⟩ := (mem_starredLe (by positivity)).mp hf
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right ?_))
    refine Nat.le_floor (hf1.trans ?_)
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hhi hL0]

end Masullo.QRH.MeanSquare
