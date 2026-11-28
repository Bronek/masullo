import Masullo.QRH.MeanSquare.FamilyReciprocity
import Masullo.QRH.MeanSquare.FamilySymbol
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The large sieve on separated dyadic blocks of the reflected series -/

noncomputable section

open NumberField Ideal Finset MeasureTheory

namespace Masullo.QRH.MeanSquare.ReflectionSieve

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma symbol_zero {a b : Ideal 𝓔} (hb : AwayFromSix b) (h : ¬ IsCoprime b a) :
    primaryQuadraticSymbol a b = 0 := by
  change sextic b (generator a) ^ 3 = 0
  rw [← quadraticResidue_apply hb]
  by_contra hx
  exact h (by simpa only [span_generator] using (quadraticResidue_ne_zero hb).mp hx)

private lemma sieve_starred {k : Ideal 𝓔} {M : ℝ} (hk : k ∈ sieveIdeals (span {6}) M) : Starred k
    := by
  classical
  obtain ⟨_, hsq, hc⟩ := mem_filter.mp hk
  exact ⟨⟨hsq.ne_zero, hc⟩, hsq⟩

/-- Fixing the class of the row absorbs the reciprocity sign into the column.
The equality holds at common prime divisors as well. -/
theorem reciprocal_sieve (quad : DeloupTuraevTheorem1) {R S : Finset (Ideal 𝓔)} {L : ℝ}
    (h : SieveBound R S primaryQuadraticSymbol L) (g : QuadraticFamilyClass)
    (hR : ∀ k ∈ R, Starred k ∧ familyClass k = g) (hS : ∀ n ∈ S, Starred n) :
    SieveBound R S (fun k n => primaryQuadraticSymbol n k) L := by
  intro z
  let w n := z n * familySign g (familyClass n)
  have hswap (k : Ideal 𝓔) (hk : k ∈ R) (n : Ideal 𝓔) (hn : n ∈ S) :
      z n * primaryQuadraticSymbol n k = w n * primaryQuadraticSymbol k n := by
    by_cases hc : IsCoprime k n
    · rw [primaryQuadraticSymbol_reciprocity quad (hR k hk).1 (hS n hn) hc, (hR k hk).2]
      dsimp [w]
      ring
    · rw [symbol_zero (hR k hk).1.1 hc, symbol_zero (hS n hn).1 (fun h => hc h.symm)]
      simp
  have hw (n) : ‖w n‖ = ‖z n‖ := by
    rcases sq_eq_one_iff.mp (familySign_sq g (familyClass n)) with he | he <;> simp [w, he]
  calc
    _ = ∑ k ∈ R, ‖∑ n ∈ S, w n * primaryQuadraticSymbol k n‖ ^ 2 := by
      exact sum_congr rfl fun k hk => congrArg (fun x : ℂ => ‖x‖ ^ 2) (sum_congr rfl (hswap k hk))
    _ ≤ _ := h w
    _ = _ := by simp only [hw]

/-- The fixed numerator factor (including a possible factor above two) and the
cube ideal contribute a row multiplier of norm at most one. This also includes
the zero at a common prime divisor of the numerator and denominator. -/
theorem split_column_symbol {k : Ideal 𝓔} (hk : AwayFromSix k) (n : Ideal 𝓔) (d b : 𝓔) :
    quadraticResidue hk (d * generator n * b) =
      quadraticResidue hk (d * b) * primaryQuadraticSymbol n k ∧ ‖quadraticResidue hk (d * b)‖ ≤ 1
        := by
  constructor
  · change _ = _ * sextic k (generator n) ^ 3
    rw [← quadraticResidue_apply hk]
    simp only [map_mul]
    ring
  · by_cases h : IsCoprime k (span {d * b})
    · rcases sq_eq_one_iff.mp (quadraticResidue_sq hk h) with he | he <;> simp [he]
    · have hz : quadraticResidue hk (d * b) = 0 := by
        by_contra hv
        exact h ((quadraticResidue_ne_zero hk).mp hv)
      simp [hz]

private lemma harmonic_band {A : ℝ}
    (hA : ∀ x : ℝ, 1 ≤ x → ((idealsLe x).card : ℝ) ≤ A * x)
    {V : ℝ} (hV : 1 ≤ V) (s : Finset (Ideal 𝓔))
    (hs : ∀ x ∈ s, (absNorm x : ℝ) ∈ Set.Ico V (2 * V)) :
    ∑ x ∈ s, (absNorm x : ℝ)⁻¹ ≤ 2 * A := by
  have hp : 0 < V := by linarith
  have hsub : s ⊆ idealsLe (2 * V) := fun x hx =>
    (mem_idealsLe (by positivity)).mpr (hs x hx).2.le
  calc
    _ ≤ ∑ _ ∈ s, V⁻¹ := sum_le_sum fun x hx => inv_anti₀ hp (hs x hx).1
    _ = s.card / V := by simp [div_eq_mul_inv]
    _ ≤ A * (2 * V) / V := div_le_div_of_nonneg_right
      ((Nat.cast_le.mpr (card_le_card hsub)).trans (hA _ (by linarith))) hp.le
    _ = _ := by field_simp

private def vector {ι : Type*} (R : Finset ι) (v : ι → ℂ) : EuclideanSpace ℂ R :=
  WithLp.toLp 2 (fun k : R => v k)

private lemma norm_vector {ι : Type*} (R : Finset ι) (v : ι → ℂ) :
    ‖vector R v‖ = Real.sqrt (∑ k ∈ R, ‖v k‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, ← R.sum_coe_sort]
  rfl

private lemma norm_weighted_vector {ι : Type*} {R : Finset ι} {H : ℝ}
    (hH : 0 ≤ H) (w v : ι → ℂ) (hw : ∀ k ∈ R, ‖w k‖ ≤ H) :
    ‖vector R (fun k => w k * v k)‖ ≤ H * ‖vector R v‖ := by
  simp only [norm_vector]
  rw [← Real.sqrt_sq hH, ← Real.sqrt_mul (sq_nonneg H)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  exact sum_le_sum fun k hk => by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hw k hk) 2) (sq_nonneg _)

/-- A single column integral after separation in the logarithm of the squarefree norm. -/
def column (S : Finset (Ideal 𝓔)) (Z : ℝ → Ideal 𝓔 → ℂ) (t : ℝ) (k : Ideal 𝓔) : ℂ :=
  ∑ n ∈ S, (Z t n / (Real.sqrt (absNorm n) : ℂ)) * primaryQuadraticSymbol n k

private lemma norm_column {R S : Finset (Ideal 𝓔)} {L a A : ℝ}
    (h : SieveBound R S (fun k n => primaryQuadraticSymbol n k) L)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (Z : ℝ → Ideal 𝓔 → ℂ) (t : ℝ)
    (hZ : ∀ n ∈ S, ‖Z t n‖ ≤ a) (hS : ∑ n ∈ S, (absNorm n : ℝ)⁻¹ ≤ A) :
    ‖vector R (column S Z t)‖ ≤ Real.sqrt L * a * Real.sqrt A := by
  let z n := Z t n / (Real.sqrt (absNorm n) : ℂ)
  have hz : ∑ n ∈ S, ‖z n‖ ^ 2 ≤ a ^ 2 * A := calc
    _ ≤ ∑ n ∈ S, a ^ 2 * (absNorm n : ℝ)⁻¹ := by
      refine sum_le_sum fun n hn => ?_
      dsimp only [z]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        div_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hZ n hn) 2) (by
        positivity)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  rw [norm_vector]
  calc
    _ ≤ Real.sqrt (L * (a ^ 2 * A)) := Real.sqrt_le_sqrt ((h z).trans (mul_le_mul_of_nonneg_left hz
      hL))
    _ = _ := by rw [Real.sqrt_mul hL, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha, mul_assoc]

/-- A separated block of (15), before multiplication by the scalar `3^(-m/3)`. -/
def block (S T : Finset (Ideal 𝓔)) (Z : Ideal 𝓔 → ℝ → Ideal 𝓔 → ℂ)
    (W : Ideal 𝓔 → ℝ → Ideal 𝓔 → ℂ) (k : Ideal 𝓔) : ℂ :=
  ∑ b ∈ T, (absNorm b : ℂ)⁻¹ * ∫ t : ℝ, W b t k * column S (Z b) t k

private lemma block_bound {R S T : Finset (Ideal 𝓔)} {L a A H : ℝ}
    (h : SieveBound R S (fun k n => primaryQuadraticSymbol n k) L)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (Z W : Ideal 𝓔 → ℝ → Ideal 𝓔 → ℂ)
    (hZ : ∀ b ∈ T, ∀ t n, n ∈ S → ‖Z b t n‖ ≤ a)
    (hW : ∀ b ∈ T, ∀ t k, k ∈ R → ‖W b t k‖ ≤ H / (1 + |t|) ^ 2)
    (hI : ∀ b ∈ T, ∀ k ∈ R, Integrable (fun t : ℝ => W b t k * column S (Z b) t k))
    (hS : ∑ n ∈ S, (absNorm n : ℝ)⁻¹ ≤ A) (hT : ∑ b ∈ T, (absNorm b : ℝ)⁻¹ ≤ A) :
    ‖vector R (block S T Z W)‖ ≤ A * (H * (Real.sqrt L * a * Real.sqrt A) * Real.pi) := by
  let V := Real.sqrt L * a * Real.sqrt A
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let f b (t : ℝ) := vector R (fun k => W b t k * column S (Z b) t k)
  have hval (b) (hb : b ∈ T) (k : R) :
      (∫ t : ℝ, f b t).ofLp k = ∫ t : ℝ, W b t k * column S (Z b) t k :=
    eval_integral_piLp (f := f b) (fun k => hI b hb k k.2) k
  have hi (b) (hb : b ∈ T) : ‖∫ t : ℝ, f b t‖ ≤ H * V * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (H * V) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        apply Filter.Eventually.of_forall
        intro t
        have hwt (k) (hk : k ∈ R) : ‖W b t k‖ ≤ H / (1 + t ^ 2) := by
          refine (hW b hb t k hk).trans (div_le_div_of_nonneg_left hH (by positivity) ?_)
          nlinarith [abs_nonneg t, sq_abs t]
        calc
          ‖f b t‖ ≤ (H / (1 + t ^ 2)) * ‖vector R (column S (Z b) t)‖ :=
            norm_weighted_vector (by positivity) _ _ hwt
          _ ≤ (H / (1 + t ^ 2)) * V := mul_le_mul_of_nonneg_left
            (norm_column h hL ha (Z b) t (hZ b hb t) hS) (by positivity)
          _ = _ := by ring
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hv : vector R (block S T Z W) =
      ∑ b ∈ T, (absNorm b : ℂ)⁻¹ • (∫ t : ℝ, f b t) := by
    ext k
    change block S T Z W k = _
    simp only [block, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun b hb => congrArg ((absNorm b : ℂ)⁻¹ * ·) (hval b hb k).symm
  rw [hv]
  calc
    _ ≤ ∑ b ∈ T, ‖(absNorm b : ℂ)⁻¹ • ∫ t : ℝ, f b t‖ := norm_sum_le ..
    _ ≤ ∑ b ∈ T, (absNorm b : ℝ)⁻¹ * (H * V * Real.pi) := by
      refine sum_le_sum fun b hb => ?_
      rw [norm_smul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hi b hb) (by positivity)
    _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hT (by positivity)

/-- The scale of the reflected kernel on a pair of dyadic norm bands. -/
def kernelScale (m : ℤ) (V B Y : ℝ) : ℝ := (3 : ℝ) ^ m * V * B ^ 3 / Y

/-- Estimate (7) on the separated form of (15). The classes of the squarefree
rows and the possible factor of two in the columns have already been fixed.
The two separated weights may depend on the cube ideal and transform parameter.
Only the kernel weight may also depend on the row. -/
theorem separated_dyadic_block (quad : DeloupTuraevTheorem1)
    (sieve : QuadraticSieve primaryQuadraticSymbol) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C ≥ (0 : ℝ), ∀ {K V B Y a H : ℝ}, 1 ≤ K → 1 ≤ V → 1 ≤ B → 0 < Y → 0 ≤ a → 0 ≤ H →
    ∀ (m : ℤ) (g : QuadraticFamilyClass) (R S T : Finset (Ideal 𝓔)),
      R ⊆ sieveIdeals (span {6}) K → S ⊆ dyadicSieveIdeals (span {6}) V →
      (∀ k ∈ R, familyClass k = g) → (∀ b ∈ T, (absNorm b : ℝ) ∈ Set.Ico B (2 * B)) →
    ∀ Z W : Ideal 𝓔 → ℝ → Ideal 𝓔 → ℂ,
      (∀ b ∈ T, ∀ t n, n ∈ S → ‖Z b t n‖ ≤ a) →
      (∀ b ∈ T, ∀ t k, k ∈ R → ‖W b t k‖ ≤ H / (1 + kernelScale m V B Y) ^ 3 / (1 + |t|) ^ 2) →
      (∀ b ∈ T, ∀ k ∈ R, Integrable (fun t : ℝ => W b t k * column S (Z b) t k)) →
      (3 : ℝ) ^ (-(m : ℝ) / 3) * Real.sqrt (∑ k ∈ R, ‖block S T Z W k‖ ^ 2) ≤
        C * a * H * (3 : ℝ) ^ (-(m : ℝ) / 3) * (K * V) ^ ρ *
          (Real.sqrt K + Real.sqrt V) / (1 + kernelScale m V B Y) ^ 3 := by
  classical
  obtain ⟨c, hc, hbound⟩ := sieve (2 * ρ) (by positivity)
  obtain ⟨A, hA⟩ := exists_card_idealsLe_le
  have haA : 0 ≤ A := (Nat.cast_nonneg (idealsLe 1).card).trans (by simpa using hA 1 le_rfl)
  refine ⟨(2 * A) * Real.sqrt (2 * A) * Real.sqrt c * Real.pi, by positivity, ?_⟩
  intro K V B Y a H hK hV hB hY ha hH m g R S T hR hS hg hT Z W hZ hW hI
  have hK₀ : 0 ≤ K := by linarith
  have hV₀ : 0 ≤ V := by linarith
  have hB₀ : 0 ≤ B := by linarith
  have hz : 0 ≤ kernelScale m V B Y := by dsimp [kernelScale]; positivity
  have hrec := reciprocal_sieve quad (hbound K V hK hV R S hR hS) g
    (fun k hk => ⟨sieve_starred (hR hk), hg k hk⟩)
    (fun n hn => sieve_starred ((mem_filter.mp (hS hn)).1))
  have hcs := harmonic_band hA hV S (fun n hn => (mem_filter.mp (hS hn)).2)
  have hct := harmonic_band hA hB T hT
  have hb := block_bound hrec (by positivity) ha
    (show 0 ≤ H / (1 + kernelScale m V B Y) ^ 3 by positivity) Z W hZ hW hI hcs hct
  have hroot : Real.sqrt (c * (K * V) ^ (2 * ρ) * (K + V)) ≤
      Real.sqrt c * (K * V) ^ ρ * (Real.sqrt K + Real.sqrt V) := by
    have he : (K * V) ^ (2 * ρ) = ((K * V) ^ ρ) ^ 2 := by
      rw [← Real.rpow_mul_natCast (mul_nonneg hK₀ hV₀)]
      norm_num [mul_comm]
    rw [he, Real.sqrt_mul (by positivity), Real.sqrt_mul hc, Real.sqrt_sq (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hK₀, Real.sq_sqrt hV₀, mul_nonneg (Real.sqrt_nonneg K)
      (Real.sqrt_nonneg V)]
  rw [norm_vector] at hb
  calc
    _ ≤ (3 : ℝ) ^ (-(m : ℝ) / 3) * ((2 * A) * ((H / (1 + kernelScale m V B Y) ^ 3) *
        (Real.sqrt (c * (K * V) ^ (2 * ρ) * (K + V)) * a * Real.sqrt (2 * A)) * Real.pi)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (3 : ℝ) ^ (-(m : ℝ) / 3) * ((2 * A) * ((H / (1 + kernelScale m V B Y) ^ 3) *
        ((Real.sqrt c * (K * V) ^ ρ * (Real.sqrt K + Real.sqrt V)) * a * Real.sqrt (2 * A)) *
          Real.pi)) := by gcongr
    _ = _ := by ring

/-- The local choices at a prime outside the varying squarefree row.
The principal choice also represents the constant term at exponent four. -/
inductive TameBranch
  | inactive
  | ordinary
  | principal
  | dividesSquarefree
  | dividesCube
  deriving DecidableEq

/-- Multiplier of the squared coefficient bound in (16). -/
def TameBranch.weightSq (q : ℝ) : TameBranch → ℝ
  | .inactive | .ordinary | .dividesSquarefree => 1
  | .principal | .dividesCube => q⁻¹

/-- Multiplier of the length in (16), after extracting a forced divisor. -/
def TameBranch.length (q : ℝ) : TameBranch → ℝ
  | .inactive => 1
  | .ordinary | .principal => q ^ 2
  | .dividesSquarefree => q
  | .dividesCube => q⁻¹

private lemma weightSq_bounds {q : ℝ} (hq : 1 ≤ q) (e : TameBranch) :
    0 ≤ e.weightSq q ∧ e.weightSq q ≤ 1 := by
  have hp : 0 < q := by linarith
  cases e <;> simp [TameBranch.weightSq, inv_nonneg.mpr hp.le, inv_le_one_of_one_le₀ hq]

private lemma local_cost {q : ℝ} (hq : 1 ≤ q) {v : ℕ} (hv : 1 ≤ v) (e : TameBranch)
    (he : v = 1 → e ≠ .ordinary) :
    e.weightSq q * e.length q ≤ q ^ min 2 v := by
  have hp : 0 < q := by linarith
  have hq₂ : q ≤ q ^ 2 := by simpa using pow_le_pow_right₀ hq (by decide : 1 ≤ 2)
  have hinv := inv_le_one_of_one_le₀ hq
  have hinv₂ : q⁻¹ * q⁻¹ ≤ 1 :=
    by simpa using mul_le_mul hinv hinv (inv_nonneg.mpr hp.le) zero_le_one
  have hprod : q⁻¹ * q ^ 2 = q := by field_simp
  by_cases hv₁ : v = 1
  · rw [hv₁, show min 2 1 = 1 by decide, pow_one]
    cases e <;> simp only [TameBranch.weightSq, TameBranch.length, one_mul, hprod]
    all_goals first | exact hq | exact (he hv₁ rfl).elim | exact le_rfl | exact hinv₂.trans hq
  · rw [min_eq_left (by omega : 2 ≤ v)]
    cases e <;> simp only [TameBranch.weightSq, TameBranch.length, one_mul, hprod]
    all_goals first | exact hq.trans hq₂ | exact le_rfl | exact hq₂ | exact hinv₂.trans (hq.trans
      hq₂)

/-- Multiplying the local inequalities in (16) preserves the bound on the
squared amplitude. A prime of `t` is assigned valuation two. Outside `t`
the valuation is that of `g`, and valuation one excludes an ordinary active branch. -/
theorem branch_product_bound {ι : Type*} (P : Finset ι) (q : ι → ℝ) (v : ι → ℕ)
    (e : ι → TameBranch) (hq : ∀ p ∈ P, 1 ≤ q p) (hv : ∀ p ∈ P, 1 ≤ v p)
    (he : ∀ p ∈ P, v p = 1 → e p ≠ .ordinary) {Y₀ : ℝ} (hY : 0 ≤ Y₀) :
    (∏ p ∈ P, (e p).weightSq (q p)) ≤ 1 ∧
      (∏ p ∈ P, (e p).weightSq (q p)) * (Y₀ * ∏ p ∈ P, (e p).length (q p)) ≤
        Y₀ * ∏ p ∈ P, q p ^ min 2 (v p) := by
  constructor
  · exact prod_le_one₀ (fun p hp => (weightSq_bounds (hq p hp) _).1)
      (fun p hp => (weightSq_bounds (hq p hp) _).2)
  · rw [mul_left_comm, ← prod_mul_distrib]
    apply mul_le_mul_of_nonneg_left _ hY
    apply prod_le_prod₀ _ (fun p hp => local_cost (hq p hp) (hv p hp) _ (he p hp))
    intro p hp
    have hn : 0 ≤ q p := le_trans zero_le_one (hq p hp)
    cases e p <;> dsimp [TameBranch.weightSq, TameBranch.length] <;> positivity

private lemma geom_sum (I : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    ∑ i ∈ I, r ^ i ≤ (1 - r)⁻¹ := by
  have hh := hasSum_geometric_of_lt_one hr hr₁
  exact (hh.summable.sum_le_tsum I (fun i _ => pow_nonneg hr i)).trans_eq hh.tsum_eq

private lemma dyadic_rpow (i : ℕ) (e : ℝ) :
    ((2 : ℝ) ^ i) ^ e = ((2 : ℝ) ^ e) ^ i := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]

/-- Summing both dyadic norm bands with a small power loss. Taking `s = ρ` and
`s = ρ + 1 / 2` accounts for the two terms in the block estimate. The sum bound
is uniform over finite truncations and over all positive lengths, including `Z < 1`. -/
theorem dyadic_kernel_sum {s d : ℝ} (hs : s < d) (hd : 0 < d) (hd₃ : d ≤ 3) :
    ∃ C ≥ (0 : ℝ), ∀ {Z : ℝ}, 0 < Z → ∀ U B : Finset ℕ,
      (∑ i ∈ U, ∑ j ∈ B, ((2 : ℝ) ^ i) ^ s /
        (1 + (2 : ℝ) ^ i * ((2 : ℝ) ^ j) ^ 3 / Z) ^ 3) ≤ C * Z ^ d := by
  let r := (2 : ℝ) ^ (s - d)
  let t := (2 : ℝ) ^ (-(3 * d))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht₁ : t < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨(1 - r)⁻¹ * (1 - t)⁻¹, mul_nonneg (inv_nonneg.mpr (by linarith)) (inv_nonneg.mpr (by
    linarith)), ?_⟩
  intro Z hZ U B
  have hterm (u b : ℝ) (hu : 0 < u) (hb : 0 < b) :
      u ^ s / (1 + u * b ^ 3 / Z) ^ 3 ≤ Z ^ d * (u ^ (s - d) * b ^ (-(3 * d))) := by
    let x := u * b ^ 3 / Z
    have hx : 0 < x := by dsimp [x]; positivity
    have hx₃ : x ^ d ≤ (1 + x) ^ 3 := calc
      _ ≤ (1 + x) ^ d := Real.rpow_le_rpow hx.le (by linarith) hd.le
      _ ≤ (1 + x) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hd₃
      _ = _ := by norm_num
    refine (div_le_div_of_nonneg_left (Real.rpow_nonneg hu.le _) (Real.rpow_pos_of_pos hx _)
      hx₃).trans_eq ?_
    dsimp only [x]
    rw [Real.div_rpow (by positivity) hZ.le, Real.mul_rpow hu.le (by positivity),
      ← Real.rpow_natCast_mul hb.le, Real.rpow_sub hu, Real.rpow_neg hb.le]
    norm_num
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  calc
    _ ≤ ∑ i ∈ U, ∑ j ∈ B, Z ^ d * (r ^ i * t ^ j) := by
      refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      simpa only [dyadic_rpow, r, t] using hterm ((2 : ℝ) ^ i) ((2 : ℝ) ^ j) (by positivity) (by
        positivity)
    _ = Z ^ d * ((∑ i ∈ U, r ^ i) * ∑ j ∈ B, t ^ j) := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
    _ ≤ Z ^ d * ((1 - r)⁻¹ * (1 - t)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
      exact mul_le_mul (geom_sum U hr hr₁) (geom_sum B ht ht₁)
        (sum_nonneg fun j _ => pow_nonneg ht j) (inv_nonneg.mpr (by linarith))
    _ = _ := mul_comm _ _

/-- The summable tail over all ramified valuations `m ≥ -3`. Combined with
the two geometric series in the ideal norms, this bounds every truncation
of the dyadic block sum by a small power of the reflected length. -/
theorem sum_layers {s d : ℝ} (hs : s < d) (hd : 0 < d) (hd₃ : d ≤ 3) :
    ∃ C ≥ (0 : ℝ), ∀ {Y : ℝ}, 0 < Y → ∀ M U B : Finset ℕ,
      (∑ k ∈ M, (3 : ℝ) ^ (-((k : ℝ) - 3) / 3) *
        ∑ i ∈ U, ∑ j ∈ B, ((2 : ℝ) ^ i) ^ s /
          (1 + kernelScale ((k : ℤ) - 3) (2 ^ i) (2 ^ j) Y) ^ 3) ≤ C * Y ^ d := by
  obtain ⟨A, hA, hsum⟩ := dyadic_kernel_sum hs hd hd₃
  let r := (3 : ℝ) ^ (-(1 / 3 : ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  refine ⟨3 * (1 - r)⁻¹ * A * 27 ^ d, by positivity, ?_⟩
  intro Y hY M U B
  have hrow (k : ℕ) : (3 : ℝ) ^ (-((k : ℝ) - 3) / 3) = 3 * r ^ k := by
    rw [show -((k : ℝ) - 3) / 3 = 1 + (-(1 / 3)) * k by ring, Real.rpow_add (by norm_num),
      Real.rpow_one, Real.rpow_mul_natCast (by norm_num)]
  have hscale (k : ℕ) : (3 : ℝ) ^ ((k : ℤ) - 3) = (3 : ℝ) ^ k / 27 := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast]
    norm_num
  have hl (k : ℕ) : (∑ i ∈ U, ∑ j ∈ B, ((2 : ℝ) ^ i) ^ s /
      (1 + kernelScale ((k : ℤ) - 3) (2 ^ i) (2 ^ j) Y) ^ 3) ≤ A * (27 * Y) ^ d := by
    refine le_trans (sum_le_sum (fun i _ => sum_le_sum (fun j _ => ?_)))
      (hsum (Z := 27 * Y) (by positivity) U B)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    apply add_le_add_right
    rw [kernelScale, hscale]
    have h₃ : 1 ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc
      _ = (1 / 27) * (2 : ℝ) ^ i * ((2 : ℝ) ^ j) ^ 3 / Y := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ k ∈ M, (3 * r ^ k) * (A * (27 * Y) ^ d) := by
      refine sum_le_sum fun k _ => ?_
      rw [hrow]
      exact mul_le_mul_of_nonneg_left (hl k) (by positivity)
    _ = 3 * (∑ k ∈ M, r ^ k) * (A * (27 * Y) ^ d) := by rw [← sum_mul, ← mul_sum]
    _ ≤ 3 * (1 - r)⁻¹ * (A * (27 * Y) ^ d) := by
      gcongr
      exact geom_sum M hr hr₁
    _ = _ := by rw [Real.mul_rpow (by norm_num) hY.le]; ring

/-- Sum of the right sides of the separated-block estimates, with the small
power loss made explicit. The reflected kernel supplies convergence in all
three indices, the two dyadic norms and the ramified valuation. -/
theorem summed_block_envelope {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ C ≥ (0 : ℝ), ∀ {K Y : ℝ}, 0 ≤ K → 0 < Y → ∀ M U B : Finset ℕ,
      (∑ k ∈ M, (3 : ℝ) ^ (-((k : ℝ) - 3) / 3) *
        ∑ i ∈ U, ∑ j ∈ B, (K * (2 : ℝ) ^ i) ^ ρ * (Real.sqrt K + Real.sqrt (2 ^ i)) /
          (1 + kernelScale ((k : ℤ) - 3) (2 ^ i) (2 ^ j) Y) ^ 3) ≤
        C * K ^ ρ * Y ^ (2 * ρ) * (Real.sqrt K + Real.sqrt Y) := by
  obtain ⟨A, hA, h₁⟩ := sum_layers (s := ρ) (d := 2 * ρ) (by linarith) (by positivity) (by linarith)
  obtain ⟨D, hD, h₂⟩ := sum_layers (s := ρ + 1 / 2) (d := 2 * ρ + 1 / 2)
    (by linarith) (by positivity) (by linarith)
  refine ⟨max A D, hA.trans (le_max_left ..), ?_⟩
  intro K Y hK hY M U B
  let F (s : ℝ) := ∑ k ∈ M, (3 : ℝ) ^ (-((k : ℝ) - 3) / 3) *
    ∑ i ∈ U, ∑ j ∈ B, ((2 : ℝ) ^ i) ^ s / (1 + kernelScale ((k : ℤ) - 3) (2 ^ i) (2 ^ j) Y) ^ 3
  have split_term (u : ℝ) (hu : 0 < u) (x : ℝ) :
      (K * u) ^ ρ * (Real.sqrt K + Real.sqrt u) / x =
        (K ^ ρ * Real.sqrt K) * (u ^ ρ / x) + K ^ ρ * (u ^ (ρ + 1 / 2) / x) := by
    rw [Real.mul_rpow hK hu.le, Real.rpow_add hu, Real.sqrt_eq_rpow u]
    ring
  calc
    _ = (K ^ ρ * Real.sqrt K) * F ρ + K ^ ρ * F (ρ + 1 / 2) := by
      simp only [F, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [split_term ((2 : ℝ) ^ i) (by positivity)]
      ring
    _ ≤ (K ^ ρ * Real.sqrt K) * (A * Y ^ (2 * ρ)) + K ^ ρ * (D * Y ^ (2 * ρ + 1 / 2)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (h₁ hY M U B) (by positivity))
        (mul_le_mul_of_nonneg_left (h₂ hY M U B) (by positivity))
    _ ≤ (K ^ ρ * Real.sqrt K) * (max A D * Y ^ (2 * ρ)) +
        K ^ ρ * (max A D * Y ^ (2 * ρ + 1 / 2)) := by
      gcongr <;> first | exact le_max_left .. | exact le_max_right ..
    _ = _ := by rw [Real.rpow_add hY, ← Real.sqrt_eq_rpow]; ring

open UniqueFactorizationMonoid

/-- Truncating the exponents in an ideal factorization can only decrease its norm. -/
theorem partial_norm_product {a : Ideal 𝓔} (ha : a ≠ 0) (P : Finset (Ideal 𝓔))
    (e : Ideal 𝓔 → ℕ) (he : ∀ p ∈ P, e p ≤ (normalizedFactors a).count p)
    (hp : ∀ p ∈ P, p ≠ 0) :
    (∏ p ∈ P, (absNorm p : ℝ) ^ e p) ≤ absNorm a := by
  classical
  let Q := P ∪ (normalizedFactors a).toFinset
  have hfull : a = ∏ p ∈ Q, p ^ (normalizedFactors a).count p :=
    (associated_iff_eq.mp (prod_normalizedFactors ha)).symm.trans
      (Finset.prod_multiset_count_of_subset _ _ subset_union_right)
  have hnorm := congrArg (fun n : Ideal 𝓔 => (absNorm n : ℝ)) hfull
  simp only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] at hnorm
  have hpQ (p) (h : p ∈ Q) : 1 ≤ (absNorm p : ℝ) := by
    have hne : p ≠ 0 := by
      rcases mem_union.mp h with h | h
      · exact hp _ h
      · exact (prime_of_normalized_factor _ (Multiset.mem_toFinset.mp h)).ne_zero
    exact_mod_cast Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero
      hne)
  calc
    _ ≤ ∏ p ∈ P, (absNorm p : ℝ) ^ (normalizedFactors a).count p := by
      exact prod_le_prod₀ (fun _ _ => by positivity)
        (fun p h => pow_le_pow_right₀ (hpQ p (mem_union_left _ h)) (he p h))
    _ ≤ ∏ p ∈ Q, (absNorm p : ℝ) ^ (normalizedFactors a).count p := by
      exact prod_le_prod_of_subset_of_one_le₀ subset_union_left (fun _ _ => by positivity)
        (fun p hp _ => one_le_pow₀ (hpQ p hp))
    _ = _ := hnorm.symm

/-- The ideal norm form of (16). The primes occurring in `t` can cost their
squared norms, and the remaining primes cost at most the norm of `g`. -/
theorem ideal_branch_budget {t g : Ideal 𝓔} (ht : t ≠ 0) (hg : g ≠ 0)
    (P : Finset (Ideal 𝓔)) (hP : P ⊆ (normalizedFactors t).toFinset ∪ (normalizedFactors
      g).toFinset)
    (e : Ideal 𝓔 → TameBranch)
    (he : ∀ p ∈ P, p ∉ normalizedFactors t → (normalizedFactors g).count p = 1 → e p ≠ .ordinary)
    {Y₀ : ℝ} (hY : 0 ≤ Y₀) :
    (∏ p ∈ P, (e p).weightSq (absNorm p)) ≤ 1 ∧
      (∏ p ∈ P, (e p).weightSq (absNorm p)) * (Y₀ * ∏ p ∈ P, (e p).length (absNorm p)) ≤
        Y₀ * (absNorm t : ℝ) ^ 2 * absNorm g := by
  classical
  let v p := if p ∈ normalizedFactors t then 2 else (normalizedFactors g).count p
  have hne (p) (hp : p ∈ P) : p ≠ 0 := by
    rcases mem_union.mp (hP hp) with h | h <;>
      exact (prime_of_normalized_factor _ (Multiset.mem_toFinset.mp h)).ne_zero
  have hv (p) (hp : p ∈ P) : 1 ≤ v p := by
    rcases mem_union.mp (hP hp) with h | h
    · simp [v, Multiset.mem_toFinset.mp h]
    · have hpos := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp h)
      dsimp [v]
      split <;> omega
  have hcost := branch_product_bound P (fun p => (absNorm p : ℝ)) v e (fun p hp => by
    exact_mod_cast Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero
      (hne p hp)))
    hv (fun p hp hv₁ => by
      by_cases h : p ∈ normalizedFactors t
      · simp [v, h] at hv₁
      · exact he p hp h (by simpa [v, h] using hv₁)) hY
  have hpow (p) (_ : p ∈ P) : min 2 (v p) ≤ (normalizedFactors (t ^ 2 * g)).count p := by
    rw [normalizedFactors_mul (pow_ne_zero _ ht) hg, normalizedFactors_pow, Multiset.count_add,
      Multiset.count_nsmul]
    by_cases h : p ∈ normalizedFactors t
    · have hp := Multiset.count_pos.mpr h
      simp only [v, ite_eq_left h]
      omega
    · simp only [v, ite_eq_right h]
      omega
  have hprod := partial_norm_product (mul_ne_zero (pow_ne_zero 2 ht) hg) P _ hpow hne
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hprod
  refine ⟨hcost.1, hcost.2.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hY

end Masullo.QRH.MeanSquare.ReflectionSieve
