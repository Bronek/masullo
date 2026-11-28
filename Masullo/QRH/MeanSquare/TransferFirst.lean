import Masullo.QRH.MeanSquare.TransferTwists

/-!
# The first Poisson pass of the transfer

* `exists_firstPass_le`: the form `E(K,L,F)` is bounded by its zero frequencies and by the
  first-pass dual form `firstDual`, uniformly over tests.
* `firstDual_le_secondInput`: after conjugating the dual columns and regrouping the dual rows
  `(h, f)` into `y = h f°²`, the first-pass dual form is at most a divisor bound times the
  input `secondInput` of the second pass.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The starred ideals of the dyadic block `F ≤ Nf < 2F`. -/
def dyadicStarred (F : ℝ) : Finset (Ideal 𝓔) := open Classical in
  (idealsLe (2 * F)).filter fun f => Starred f ∧ F ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * F

lemma dualMeanSquare_eq (ξ : RayCharacter) (W : ℝ → ℂ) (K X F : ℝ) :
    dualMeanSquare ξ W K X F =
      (∑ f ∈ dyadicStarred F, ∑ k ∈ elementRows K, ‖columnSum ξ W X k f‖ ^ 2) / (X * F) := rfl

lemma UnitTest.conj {I : TestInterval} {j : ℕ} {U : ℝ → ℂ} (hU : UnitTest I j U) :
    UnitTest I j (fun t => conj (U t)) := by
  obtain ⟨h1, h2, h3⟩ := hU
  have hc : (fun t => conj (U t)) = (Complex.conjLIE.toLinearIsometry : ℂ → ℂ) ∘ U := rfl
  refine ⟨?_, ?_, fun i hi x hx => ?_⟩
  · exact Complex.conjCLE.contDiff.comp h1
  · have : tsupport (fun t => conj (U t)) = tsupport U := by
      simp only [tsupport, Function.support, map_ne_zero]
    rwa [this]
  · have := Complex.conjLIE.toLinearIsometry.norm_iteratedFDeriv_comp_left
      (h1.contDiffAt (x := x)) (i := i) (by exact_mod_cast le_top)
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hc, this,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact h3 i hi x hx

theorem columnSum_eq_passColumn {I : TestInterval} {j : ℕ} {W : ℝ → ℂ} (hW : UnitTest I j W)
    {L : ℝ} (hL : 0 < L) (ξ : RayCharacter) (k : 𝓔) (f : Ideal 𝓔) :
    columnSum ξ W L k f = passColumn starredGauss (firstTwist ξ f) W L (I.hi * L) k := by
  classical
  have hX : 0 ≤ I.hi * L := mul_nonneg (I.pos.le.trans I.ordered) hL.le
  have hV0 : ∀ x, x ∉ Set.Icc I.lo I.hi → W x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hW.2.1 h')
  unfold columnSum passColumn
  rw [finsum_eq_sum_of_support_subset (s := (starredLe (I.hi * L)).subtype Starred)]
  · rw [Finset.sum_subtype_eq_sum_filter (f := fun n : Ideal 𝓔 =>
      gaussCoefficient n * twist ξ k f n * W (absNorm n / L))]
    have : (starredLe (I.hi * L)).filter Starred = starredLe (I.hi * L) :=
      Finset.filter_true_of_mem fun n hn => ((mem_starredLe hX).mp hn).2
    rw [this]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hs := ((mem_starredLe hX).mp hn).2
    simp only [starredGauss, firstTwist, twist, hs, hs.1, ite_true, sextic_mul hs.1]
    ring
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.mem_coe, Finset.mem_subtype, mem_starredLe hX]
    refine ⟨?_, n.2⟩
    by_contra hlt
    rw [not_le] at hlt
    refine hn ?_
    rw [hV0, mul_zero]
    intro hmem
    have := (lt_div_iff₀ hL).mpr (by linarith : I.hi * L < absNorm n.1)
    linarith [hmem.2]

/-- The dual form of the first pass. -/
def firstDual (ξ ξ' : RayCharacter) (U : ℝ → ℂ) (hi K L F : ℝ) : ℝ :=
  ∑ f ∈ dyadicStarred F, ∑ r ∈ liveRows (firstTwist ξ f) (hi * L),
    ∑ h ∈ elementRows (passCap hi K L (r.1 * r.2.1) r.2.1),
      (L * F)⁻¹ * (K * absNorm (r.1 * r.2.1) / (L * absNorm r.2.1)) *
        ‖∑ x ∈ passCols (hi * L) r,
          dualCoeff moebiusTwist (firstTwist ξ f) 4 0 ξ' (r.1 * r.2.1) r.2.1 r.2.2 h x *
            U (absNorm (r.1 * r.2.1 * (r.2.2 * x)) / L)‖ ^ 2

theorem exists_firstPass_le (hpg : PairedGaussIdentities) (I : TestInterval) (j : ℕ)
    {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) (hT : ∀ t, 1 ≤ t → gaoZhaoTransform P t = 0) :
    ∃ C ≥ (0 : ℝ), ∀ (K L F : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ) {M : ℝ},
      0 < K → 0 < L → 0 < F → UnitTest I j W → 0 ≤ M →
      (∀ U, UnitTest I j U → ∀ ξ', firstDual ξ ξ' U I.hi K L F ≤ M) →
      dualMeanSquare ξ W K L F ≤
        C * ((L * F)⁻¹ * K * (dyadicStarred F).card *
          ∑ g ∈ starredLe (I.hi * L), (2 : ℝ) ^ Multiset.card (normalizedFactors g)) +
        C * M := by
  classical
  obtain ⟨Corr, hconv⟩ := exists_gaussConversion_first hpg
  obtain ⟨C, hC0, hC⟩ := exists_passBound residueMultiplicative I j hP hT Corr
  refine ⟨C, hC0, fun K L F ξ W M hK hL hF hW hM hMean => ?_⟩
  have hhi : 0 < I.hi := I.pos.trans_le I.ordered
  have hV0 : ∀ x, x ∉ Set.Icc I.lo I.hi → W x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hW.2.1 h')
  have hVn : ∀ x, ‖W x‖ ≤ 1 := fun x => by
    by_cases hx : x ∈ Set.Icc I.lo I.hi
    · simpa using hW.2.2 0 (Nat.zero_le _) x hx
    · rw [hV0 x hx, norm_zero]; exact zero_le_one
  have hmain := hC (dyadicStarred F) (fun _ => (L * F)⁻¹) (fun _ => K) (fun _ => L)
    (fun _ => I.hi * L) (κ := starredGauss) (κ' := moebiusTwist) (firstTwist ξ) (p := 4)
    (p' := 0) (V := W) (M := M) (twistMul_starredGauss hpg) twistMul_moebiusTwist
    (twistMul_firstTwist ξ) hconv norm_starredGauss_le norm_moebiusTwist_le
    (fun o n => norm_firstTwist_le ξ o n) hW
    (fun _ _ => ⟨by positivity, hK, hL, by positivity⟩) hM
    (fun U hU ξ' => hMean U hU ξ')
  have hB : ∀ (f : Ideal 𝓔) (y : 𝓔),
      ‖passColumn starredGauss (firstTwist ξ f) W L (I.hi * L) y‖ ≤
        (starredLe (I.hi * L)).card := by
    intro f y
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 := norm_starredGauss_le n
    have h2 := norm_firstTwist_le ξ f n
    have h3 := hVn (absNorm n / L)
    have h4 := norm_sextic_le_one n y
    simp only [Nat.cast_one]
    exact mul_le_one_of_le (mul_le_one_of_le (mul_le_one_of_le h1 (norm_nonneg _) h2)
      (norm_nonneg _) h3) (norm_nonneg _) h4
  have hstep : dualMeanSquare ξ W K L F ≤
      ∑ f ∈ dyadicStarred F, (L * F)⁻¹ * ∑' y : 𝓔, (P (elementNorm y / K)).re *
        ‖passColumn starredGauss (firstTwist ξ f) W L (I.hi * L) y‖ ^ 2 := by
    rw [dualMeanSquare_eq, div_eq_inv_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : ∑ k ∈ elementRows K, ‖columnSum ξ W L k f‖ ^ 2 =
        ∑ k ∈ elementRows K, ‖passColumn starredGauss (firstTwist ξ f) W L (I.hi * L) k‖ ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [columnSum_eq_passColumn hW hL]
    rw [this]
    exact sum_elementRows_le_tsum hP hK (hB f)
  refine hstep.trans (hmain.trans_eq ?_)
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The outer weight of the second pass at the first-pass row `r`. -/
def secondWeight (K L F : ℝ) (r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : ℝ :=
  (L * F)⁻¹ * (K * absNorm (r.1 * r.2.1) / (L * absNorm r.2.1))

/-- The row scale of the second pass at the first-pass row `r`. -/
def secondScale (hi K L F target : ℝ) (r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : ℝ :=
  max 1 (4 * hi ^ 2) * target * L * F * absNorm r.2.1 / (K * (absNorm (r.1 * r.2.1) : ℝ) ^ 2)

/-- The column length of the second pass at the first-pass row `r`. -/
def secondLength (L : ℝ) (r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔) : ℝ :=
  L / absNorm (r.1 * r.2.1 * r.2.2)

/-- The input of the second pass: `P`-weighted mean squares of the conjugated dual columns. -/
def secondInput (ξ ξ' : RayCharacter) (U : ℝ → ℂ) (P : SchwartzMap ℝ ℂ)
    (hi K L F target : ℝ) : ℝ :=
  ∑ r ∈ passRows (hi * L), secondWeight K L F r *
    ∑' y : 𝓔, (P (elementNorm y / secondScale hi K L F target r)).re *
      ‖passColumn moebiusTwist (secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2))
        (fun t => conj (U t)) (secondLength L r) (hi * secondLength L r) y‖ ^ 2

private lemma conj_sextic_pow_four {n : Ideal 𝓔} (hn : AwayFromSix n) (f : Ideal 𝓔) :
    conj (sextic n (generator f ^ 4)) = sextic n (generator f) ^ 2 := by
  rw [sextic_pow hn]
  by_cases hc : IsCoprime n (span {generator f})
  · rw [map_pow, conj_sextic_eq_pow_five hn hc, ← pow_mul]
    have h6 := sextic_pow_six hn hc
    have : sextic n (generator f) ^ (5 * 4) = sextic n (generator f) ^ 2 *
        (sextic n (generator f) ^ 6) ^ 3 := by ring
    rw [this, h6]; simp
  · rw [sextic_eq_zero hn hc]; simp

private lemma conj_dualCoeff_term (ξ ξ' : RayCharacter) (f g e v : Ideal 𝓔) (h : 𝓔)
    {x : Ideal 𝓔} (hx : Starred x) (hc : IsCoprime (g * v) x) (u : ℂ) :
    conj (dualCoeff moebiusTwist (firstTwist ξ f) 4 0 ξ' g e v h x * u) =
      moebiusTwist x * secondTwist ξ ξ' g e (g * v) x * conj u *
        sextic x (h * generator f ^ 2) := by
  have hA := hx.1
  simp only [secondTwist, hc, ite_true, dualCoeff, firstTwist, moebiusTwist, sextic_mul hA,
    sextic_pow hA, map_mul, map_pow, Complex.conj_conj, pow_zero, mul_one, map_intCast]
  have := conj_sextic_pow_four hA f
  rw [sextic_pow hA, map_pow] at this
  rw [this]
  ring

lemma mem_passCols_iff {hi L : ℝ} (hhi : 0 < hi) (hL : 0 < L)
    {r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (hN : 1 ≤ (absNorm (r.1 * r.2.1 * r.2.2) : ℝ))
    {x : Ideal 𝓔} :
    x ∈ passCols (hi * L) r ↔
      x ∈ starredLe (hi * secondLength L r) ∧ IsCoprime (r.1 * r.2.1 * r.2.2) x := by
  classical
  have hX : 0 ≤ hi * L := by positivity
  have hN0 : 0 < (absNorm (r.1 * r.2.1 * r.2.2) : ℝ) := by linarith
  have hX' : 0 ≤ hi * secondLength L r := by unfold secondLength; positivity
  have key : (absNorm (r.1 * r.2.1 * r.2.2 * x) : ℝ) =
      absNorm (r.1 * r.2.1 * r.2.2) * absNorm x := by rw [map_mul]; push_cast; ring
  have h2 : ((absNorm x : ℝ) ≤ hi * secondLength L r) ↔
      (absNorm (r.1 * r.2.1 * r.2.2) : ℝ) * absNorm x ≤ hi * L := by
    rw [secondLength, ← mul_div_assoc, le_div_iff₀ hN0, mul_comm]
  have hx0 : (0 : ℝ) ≤ absNorm x := Nat.cast_nonneg _
  unfold passCols
  rw [Finset.mem_filter, mem_idealsLe hX, mem_starredLe hX', key, h2]
  constructor
  · rintro ⟨-, hs, hc, hle⟩
    exact ⟨⟨hle, hs⟩, hc⟩
  · rintro ⟨⟨hle, hs⟩, hc⟩
    exact ⟨by nlinarith, hs, hc, hle⟩

lemma norm_dualColumn_eq (ξ ξ' : RayCharacter) (U : ℝ → ℂ) {hi L : ℝ} (hhi : 0 < hi)
    (hL : 0 < L) {r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (hN : 1 ≤ (absNorm (r.1 * r.2.1 * r.2.2) : ℝ))
    (f : Ideal 𝓔) (h : 𝓔) :
    ‖∑ x ∈ passCols (hi * L) r,
        dualCoeff moebiusTwist (firstTwist ξ f) 4 0 ξ' (r.1 * r.2.1) r.2.1 r.2.2 h x *
          U (absNorm (r.1 * r.2.1 * (r.2.2 * x)) / L)‖ =
      ‖passColumn moebiusTwist (secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2))
        (fun t => conj (U t)) (secondLength L r) (hi * secondLength L r)
        (h * generator f ^ 2)‖ := by
  classical
  have hN0 : 0 < (absNorm (r.1 * r.2.1 * r.2.2) : ℝ) := by linarith
  rw [← Complex.norm_conj, map_sum]
  unfold passColumn
  refine congrArg norm ?_
  have hsub : passCols (hi * L) r ⊆ starredLe (hi * secondLength L r) := fun x hx =>
    ((mem_passCols_iff hhi hL hN).mp hx).1
  have hX' : 0 ≤ hi * secondLength L r := by unfold secondLength; positivity
  refine Eq.trans (Finset.sum_congr rfl ?_) (Finset.sum_subset hsub ?_)
  · intro x hx
    obtain ⟨hxs, hc⟩ := (mem_passCols_iff hhi hL hN).mp hx
    rw [conj_dualCoeff_term ξ ξ' f _ _ _ h ((mem_starredLe hX').mp hxs).2 hc]
    have : (absNorm (r.1 * r.2.1 * (r.2.2 * x)) : ℝ) / L =
        absNorm x / secondLength L r := by
      rw [secondLength, ← mul_assoc, map_mul]; push_cast
      field_simp
    rw [this]
  · intro x hx hnot
    have hc : ¬ IsCoprime (r.1 * r.2.1 * r.2.2) x := fun hc =>
      hnot ((mem_passCols_iff hhi hL hN).mpr ⟨hx, hc⟩)
    simp [secondTwist, hc]

lemma sum_fiber_le {ψ G : 𝓔 → ℝ} (S : Finset (𝓔 × Ideal 𝓔)) {T : ℝ} (hT0 : 0 ≤ T)
    (hψ : ∀ y, 0 ≤ ψ y) (hG : ∀ y, 0 ≤ G y) (hs : Summable G)
    (hne : ∀ p ∈ S, p.1 * generator p.2 ^ 2 ≠ 0)
    (hcard : ∀ p ∈ S, ((idealDivisors (span {p.1 * generator p.2 ^ 2})).card : ℝ) ≤ T)
    (hle : ∀ p ∈ S, ψ (p.1 * generator p.2 ^ 2) ≤ G (p.1 * generator p.2 ^ 2)) :
    ∑ p ∈ S, ψ (p.1 * generator p.2 ^ 2) ≤ T * ∑' y, G y := by
  classical
  set g : 𝓔 × Ideal 𝓔 → 𝓔 := fun p => p.1 * generator p.2 ^ 2 with hg
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
    (fun p hp => Finset.mem_image_of_mem g hp)]
  have hstep : ∀ y ∈ S.image g,
      ∑ p ∈ S with g p = y, ψ (g p) ≤ T * G y := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    have h1 : ∑ p ∈ S with g p = g q, ψ (g p) = (S.filter fun p => g p = g q).card * ψ (g q) := by
      rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]), Finset.sum_const,
        nsmul_eq_mul]
    have h3 := card_filter_elem_mul_sq_eq_le (hne q hq) generator span_generator S
    have h2 : ((S.filter fun p => g p = g q).card : ℝ) ≤ T :=
      le_trans (by exact_mod_cast h3) (hcard q hq)
    rw [h1]
    calc _ ≤ T * ψ (g q) := mul_le_mul_of_nonneg_right h2 (hψ _)
      _ ≤ T * G (g q) := mul_le_mul_of_nonneg_left (hle q hq) hT0
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun y _ => hG y) hT0

lemma summable_row {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P) {sc : ℝ} (hsc : 0 < sc)
    (v : 𝓔 → ℂ) {B : ℝ} (hv : ∀ y, ‖v y‖ ≤ B) :
    Summable fun y : 𝓔 => (P (elementNorm y / sc)).re * ‖v y‖ ^ 2 := by
  have hnn : ∀ y, 0 ≤ (P (elementNorm y / sc)).re * ‖v y‖ ^ 2 := fun y =>
    mul_nonneg (hP.re_nonneg _ (by positivity)) (sq_nonneg _)
  refine Summable.of_nonneg_of_le hnn (fun y => ?_)
    ((summable_norm_schwartz P hsc).mul_right (B ^ 2))
  exact mul_le_mul (Complex.re_le_norm _) (pow_le_pow_left₀ (norm_nonneg _) (hv y) 2)
    (sq_nonneg _) (norm_nonneg _)

lemma norm_passColumn_le_sum {κ φ : Ideal 𝓔 → ℂ} (hκ : ∀ n, ‖κ n‖ ≤ 1)
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (V : ℝ → ℂ) (ℓ X : ℝ) (y : 𝓔) :
    ‖passColumn κ φ V ℓ X y‖ ≤ ∑ n ∈ starredLe X, ‖V (absNorm n / ℓ)‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_mul, norm_mul]
  have h1 := hκ n
  have h2 := hφ n
  have h4 := norm_sextic_le_one n y
  have h0 := norm_nonneg (V (absNorm n / ℓ))
  calc _ ≤ 1 * 1 * ‖V (absNorm n / ℓ)‖ * 1 := by gcongr
    _ = _ := by ring

lemma row_bound {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P)
    (ξ ξ' : RayCharacter) (U : ℝ → ℂ) {hi K L F target T : ℝ} (hhi : 0 < hi) (hK : 0 < K)
    (hL : 0 < L) (hF : 0 < F) (hLF : L * F ≤ target) (hT0 : 0 ≤ T)
    (hT : ∀ y : 𝓔, y ≠ 0 → (elementNorm y : ℝ) ≤ 4 * hi ^ 3 * L ^ 3 * F ^ 2 / K →
      ((idealDivisors (span {y})).card : ℝ) ≤ T)
    {r : Ideal 𝓔 × Ideal 𝓔 × Ideal 𝓔} (hr : r ∈ passRows (hi * L)) :
    ∑ f ∈ dyadicStarred F, ∑ h ∈ elementRows (passCap hi K L (r.1 * r.2.1) r.2.1),
      ‖∑ x ∈ passCols (hi * L) r,
        dualCoeff moebiusTwist (firstTwist ξ f) 4 0 ξ' (r.1 * r.2.1) r.2.1 r.2.2 h x *
          U (absNorm (r.1 * r.2.1 * (r.2.2 * x)) / L)‖ ^ 2 ≤
      T * ∑' y : 𝓔, (P (elementNorm y / secondScale hi K L F target r)).re *
        ‖passColumn moebiusTwist (secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2))
          (fun t => conj (U t)) (secondLength L r) (hi * secondLength L r) y‖ ^ 2 := by
  classical
  have hX : 0 ≤ hi * L := by positivity
  obtain ⟨hmem, hS1, hS2, -⟩ := Finset.mem_filter.mp hr
  obtain ⟨-, hm2⟩ := Finset.mem_product.mp hmem
  obtain ⟨hm21, -⟩ := Finset.mem_product.mp hm2
  have hNeX : (absNorm r.2.1 : ℝ) ≤ hi * L := (mem_idealsLe hX).mp hm21
  have hg : r.1 * r.2.1 ≠ ⊥ := hS1.1.1
  have he : r.2.1 ≠ ⊥ := (passRows_ne_bot hr).2
  have hv : r.2.2 ≠ ⊥ := hS2.1.1
  have hgv : r.1 * r.2.1 * r.2.2 ≠ ⊥ := fun h0 =>
    (Ideal.mul_eq_bot.mp h0).elim hg hv
  have hNg := absNorm_one_le hg
  have hNe := absNorm_one_le he
  have hN := absNorm_one_le hgv
  have htar : 0 < target := lt_of_lt_of_le (by positivity) hLF
  set sc := secondScale hi K L F target r with hscdef
  have hsc : 0 < sc := by
    rw [hscdef, secondScale]
    refine div_pos ?_ (by positivity)
    have : 0 < max 1 (4 * hi ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  set cap := passCap hi K L (r.1 * r.2.1) r.2.1 with hcapdef
  have hcap0 : 0 ≤ cap := by rw [hcapdef, passCap]; positivity
  set Col : 𝓔 → ℂ := passColumn moebiusTwist
    (secondTwist ξ ξ' (r.1 * r.2.1) r.2.1 (r.1 * r.2.1 * r.2.2))
    (fun t => conj (U t)) (secondLength L r) (hi * secondLength L r) with hCol
  have hColB : ∀ y, ‖Col y‖ ≤ ∑ n ∈ starredLe (hi * secondLength L r),
      ‖(fun t => conj (U t)) (absNorm n / secondLength L r)‖ := fun y =>
    norm_passColumn_le_sum norm_moebiusTwist_le
      (norm_secondTwist_le ξ ξ' _ _ _) _ _ _ y
  have hsum := summable_row hP hsc Col hColB
  have hnorm : ∀ f h, ‖∑ x ∈ passCols (hi * L) r,
        dualCoeff moebiusTwist (firstTwist ξ f) 4 0 ξ' (r.1 * r.2.1) r.2.1 r.2.2 h x *
          U (absNorm (r.1 * r.2.1 * (r.2.2 * x)) / L)‖ = ‖Col (h * generator f ^ 2)‖ :=
    fun f h => norm_dualColumn_eq ξ ξ' U hhi hL hN f h
  simp only [hnorm]
  rw [← Finset.sum_product_right (f := fun p : 𝓔 × Ideal 𝓔 =>
    ‖Col (p.1 * generator p.2 ^ 2)‖ ^ 2)]
  have hD : ∀ f ∈ dyadicStarred F, Starred f ∧ F ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * F :=
    fun f hf => (Finset.mem_filter.mp hf).2
  have hel : ∀ p ∈ elementRows cap ×ˢ dyadicStarred F,
      p.1 * generator p.2 ^ 2 ≠ 0 ∧
      (elementNorm (p.1 * generator p.2 ^ 2) : ℝ) ≤ cap * (2 * F) ^ 2 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hh0, hhN⟩ := (mem_elementRows hcap0).mp hp1
    obtain ⟨hfS, hfF, hfF2⟩ := hD _ hp2
    have hf0 : p.2 ≠ ⊥ := hfS.1.1
    have hgen : generator p.2 ≠ 0 := fun h0 => hf0 (by rw [← span_generator p.2, h0]; simp)
    refine ⟨mul_ne_zero hh0 (pow_ne_zero _ hgen), ?_⟩
    have : (elementNorm (p.1 * generator p.2 ^ 2) : ℝ) =
        elementNorm p.1 * (absNorm p.2 : ℝ) ^ 2 := by
      unfold elementNorm
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
        span_generator, map_mul, map_pow]
      push_cast; ring
    rw [this]
    have hf1 : (0 : ℝ) ≤ absNorm p.2 := Nat.cast_nonneg _
    have : (absNorm p.2 : ℝ) ^ 2 ≤ (2 * F) ^ 2 := pow_le_pow_left₀ hf1 hfF2.le 2
    exact mul_le_mul hhN this (by positivity) hcap0
  have hcapF : cap * (2 * F) ^ 2 ≤ sc := by
    rw [hcapdef, passCap, hscdef, secondScale, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hM : 4 * hi ^ 2 ≤ max 1 (4 * hi ^ 2) := le_max_right _ _
    calc _ = (4 * hi ^ 2) * (L * F) * (L * F) * (absNorm r.2.1 : ℝ) := by ring
      _ ≤ max 1 (4 * hi ^ 2) * target * (L * F) * (absNorm r.2.1 : ℝ) := by gcongr
      _ = _ := by ring
  have hcapT : cap * (2 * F) ^ 2 ≤ 4 * hi ^ 3 * L ^ 3 * F ^ 2 / K := by
    have h1 : cap * (2 * F) ^ 2 = (4 * hi ^ 2 * F ^ 2 * L ^ 2 / K) *
        ((absNorm r.2.1 : ℝ) / (absNorm (r.1 * r.2.1) : ℝ) ^ 2) := by
      have : (0 : ℝ) < absNorm (r.1 * r.2.1) := by linarith
      rw [hcapdef, passCap]; field_simp; norm_num
    have h2 : (absNorm r.2.1 : ℝ) / (absNorm (r.1 * r.2.1) : ℝ) ^ 2 ≤ hi * L :=
      (div_le_self (by positivity) (one_le_pow₀ hNg)).trans hNeX
    rw [h1]
    calc _ ≤ (4 * hi ^ 2 * F ^ 2 * L ^ 2 / K) * (hi * L) := by gcongr
      _ = _ := by ring
  have hGnn : ∀ y, 0 ≤ (P (elementNorm y / sc)).re * ‖Col y‖ ^ 2 := fun y =>
    mul_nonneg (hP.re_nonneg _ (by positivity)) (sq_nonneg _)
  have hcard : ∀ p ∈ elementRows cap ×ˢ dyadicStarred F,
      ((idealDivisors (span {p.1 * generator p.2 ^ 2})).card : ℝ) ≤ T := fun p hp =>
    hT _ (hel p hp).1 ((hel p hp).2.trans hcapT)
  have hle : ∀ p ∈ elementRows cap ×ˢ dyadicStarred F,
      ‖Col (p.1 * generator p.2 ^ 2)‖ ^ 2 ≤
        (P (elementNorm (p.1 * generator p.2 ^ 2) / sc)).re *
          ‖Col (p.1 * generator p.2 ^ 2)‖ ^ 2 := by
    intro p hp
    have h1 : 1 ≤ (P (elementNorm (p.1 * generator p.2 ^ 2) / sc)).re :=
      hP.one_le_re _ ⟨by positivity, (div_le_one hsc).mpr ((hel p hp).2.trans hcapF)⟩
    nlinarith [sq_nonneg ‖Col (p.1 * generator p.2 ^ 2)‖]
  exact sum_fiber_le (ψ := fun y => ‖Col y‖ ^ 2)
    (G := fun y => (P (elementNorm y / sc)).re * ‖Col y‖ ^ 2)
    (elementRows cap ×ˢ dyadicStarred F) hT0 (fun y => sq_nonneg _) hGnn hsum
    (fun p hp => (hel p hp).1) hcard hle

theorem firstDual_le_secondInput {P : SchwartzMap ℝ ℂ} (hP : IsRowMajorant P)
    (ξ ξ' : RayCharacter) (U : ℝ → ℂ) {hi K L F target T : ℝ} (hhi : 0 < hi) (hK : 0 < K)
    (hL : 0 < L) (hF : 0 < F) (hLF : L * F ≤ target) (hT0 : 0 ≤ T)
    (hT : ∀ y : 𝓔, y ≠ 0 → (elementNorm y : ℝ) ≤ 4 * hi ^ 3 * L ^ 3 * F ^ 2 / K →
      ((idealDivisors (span {y})).card : ℝ) ≤ T) :
    firstDual ξ ξ' U hi K L F ≤ T * secondInput ξ ξ' U P hi K L F target := by
  classical
  have hX : 0 ≤ hi * L := by positivity
  have h1 : firstDual ξ ξ' U hi K L F ≤ ∑ f ∈ dyadicStarred F, ∑ r ∈ passRows (hi * L),
      ∑ h ∈ elementRows (passCap hi K L (r.1 * r.2.1) r.2.1), secondWeight K L F r *
        ‖∑ x ∈ passCols (hi * L) r,
          dualCoeff moebiusTwist (firstTwist ξ f) 4 0 ξ' (r.1 * r.2.1) r.2.1 r.2.2 h x *
            U (absNorm (r.1 * r.2.1 * (r.2.2 * x)) / L)‖ ^ 2 := by
    unfold firstDual
    refine Finset.sum_le_sum fun f _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => (Finset.mem_filter.mp hr).1)
      fun r _ _ => Finset.sum_nonneg fun h _ => ?_
    positivity
  refine h1.trans ?_
  rw [Finset.sum_comm]
  unfold secondInput
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hw : 0 ≤ secondWeight K L F r := by unfold secondWeight; positivity
  have := mul_le_mul_of_nonneg_left (row_bound hP ξ ξ' U hhi hK hL hF hLF hT0 hT hr) hw
  simp only [← Finset.mul_sum]
  calc _ ≤ _ := this
    _ = _ := by ring


end Masullo.QRH.MeanSquare
