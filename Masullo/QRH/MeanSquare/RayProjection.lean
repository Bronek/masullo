import Masullo.QRH.MeanSquare.ThetaSupport
import Masullo.QRH.MeanSquare.ReflectionCoefficients

/-! # Finite projection at the exceptional Patterson layer -/

noncomputable section

open NumberField Ideal Finset
open scoped BigOperators

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

def rayModulus (k : ℕ) : Ideal 𝓔 := span {8 * eisLambda ^ k}

abbrev RayResidue (k : ℕ) := 𝓔 ⧸ rayModulus k

instance (k : ℕ) : Fintype (RayResidue k) := by
  let := Ring.HasFiniteQuotients.finiteQuotient (I := rayModulus k) (by
    simp [rayModulus, eisLambda_prime.ne_zero])
  exact Fintype.ofFinite _

def rayReduction : RayResidue 7 →+* RayResidue 3 :=
  Ideal.Quotient.factor (span_singleton_le_span_singleton.mpr
    ⟨eisLambda ^ 4, by ring⟩)

@[simp] theorem rayReduction_mk (m : 𝓔) :
    rayReduction (Ideal.Quotient.mk (rayModulus 7) m) = Ideal.Quotient.mk (rayModulus 3) m :=
  rfl

def rayDivides (j : ℕ) (x : RayResidue 7) : Prop := eisLambda ^ j ∣ Quotient.out x

theorem rayDivides_mk {j : ℕ} (hj : j ≤ 7) (m : 𝓔) :
    rayDivides j (Ideal.Quotient.mk (rayModulus 7) m) ↔ eisLambda ^ j ∣ m := by
  let x := Ideal.Quotient.mk (rayModulus 7) m
  have hd : 8 * eisLambda ^ 7 ∣ Quotient.out x - m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out x))
  have h := ((pow_dvd_pow eisLambda hj).trans (dvd_mul_left _ 8)).trans hd
  change eisLambda ^ j ∣ Quotient.out x ↔ eisLambda ^ j ∣ m
  exact ⟨fun h' => by simpa only [sub_sub_cancel] using dvd_sub h' h,
    fun h' => by simpa only [sub_add_cancel] using dvd_add h h'⟩

def rayFourthLayer (x : RayResidue 7) : Prop := rayDivides 4 x ∧ ¬ rayDivides 5 x

@[simp] theorem rayFourthLayer_mk (m : 𝓔) :
    rayFourthLayer (Ideal.Quotient.mk (rayModulus 7) m) ↔
      eisLambda ^ 4 ∣ m ∧ ¬ eisLambda ^ 5 ∣ m := by
  simp only [rayFourthLayer, rayDivides_mk (by decide : 4 ≤ 7),
    rayDivides_mk (by decide : 5 ≤ 7)]

private theorem lambda_four_eq_nine : eisLambda ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, eisLambda_sq]
  norm_num

/-- A residue divisible by λ³ has a residue of exact exponent four in its fiber
modulo 8λ³. The CRT lift uses λ⁴ = 9 ≡ 1 modulo 8. -/
theorem exists_rayFourthLayer {x : RayResidue 7} (hx : rayDivides 3 x) :
    ∃ t, rayReduction t = rayReduction x ∧ rayFourthLayer t := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a,rfl⟩ := (rayDivides_mk (by decide) m).mp hx
  let t := eisLambda ^ 3 * (9 * a - 8 * eisLambda)
  refine ⟨Ideal.Quotient.mk (rayModulus 7) t, ?_, (rayFourthLayer_mk _).mpr ?_⟩
  · apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ⟨a - eisLambda, by dsimp [t]; ring⟩
  have ht : t = eisLambda ^ 4 + eisLambda ^ 7 * (a - eisLambda) := by
    dsimp [t]
    calc
      _ = eisLambda ^ 4 + eisLambda ^ 3 * 9 * (a - eisLambda) := by ring
      _ = _ := by rw [← lambda_four_eq_nine]; ring
  rw [ht]
  have hd (j : ℕ) (hj : j ≤ 7) : eisLambda ^ j ∣ eisLambda ^ 7 * (a - eisLambda) :=
    (pow_dvd_pow _ hj).trans (dvd_mul_right _ _)
  refine ⟨dvd_add dvd_rfl (hd 4 (by decide)), fun h => ?_⟩
  have hf : eisLambda ^ 5 ∣ eisLambda ^ 4 := by simpa using dvd_sub h (hd 5 (by decide))
  exact (by decide : ¬ 5 ≤ 4) ((pow_dvd_pow_iff eisLambda_prime.ne_zero eisLambda_prime.not_isUnit).mp hf)

open scoped Classical in
/-- Modify a residue weight by a constant on the exact-four layer of each
fiber. All resulting fiber sums vanish. -/
theorem exists_rayProjection (w : RayResidue 7 → ℂ) (hw : ∀ x, w x ≠ 0 → rayDivides 3 x) :
    ∃ W : RayResidue 7 → ℂ, (∀ x, ¬ rayFourthLayer x → W x = w x) ∧
      (∀ y, ∑ x with rayReduction x = y, W x = 0) ∧
      (∀ g : RayResidue 3 → ℂ, ∑ x, W x * g (rayReduction x) = 0) ∧
      (∀ x, ‖W x‖ ≤ ‖w x‖ + ∑ t, ‖w t‖) := by
  classical
  let fiber (y : RayResidue 3) := univ.filter fun x => rayReduction x = y
  let layer (y : RayResidue 3) := (fiber y).filter rayFourthLayer
  let mass (y : RayResidue 3) := ∑ x ∈ fiber y, w x
  let c (y : RayResidue 3) := mass y / (layer y).card
  let W (x : RayResidue 7) := w x - if rayFourthLayer x then c (rayReduction x) else 0
  have hW (y : RayResidue 3) : ∑ x ∈ fiber y, W x = 0 := by
    have hc : ∑ x ∈ fiber y, (if rayFourthLayer x then c (rayReduction x) else 0) =
        ((layer y).card : ℂ) * c y := by
      calc
        _ = ∑ x ∈ fiber y, (if rayFourthLayer x then c y else 0) := by
          apply sum_congr rfl
          intro x hx
          rw [(mem_filter.mp hx).2]
        _ = _ := by rw [← sum_filter]; simp [layer, nsmul_eq_mul]
    simp only [W, sum_sub_distrib, hc]
    change mass y - (layer y).card * c y = 0
    by_cases h : mass y = 0
    · simp [c, h]
    have hcard : (layer y).Nonempty := by
      obtain ⟨x,hx,hv⟩ := exists_ne_zero_of_sum_ne_zero h
      obtain ⟨t,ht,hd⟩ := exists_rayFourthLayer (hw x hv)
      exact ⟨t, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ht.trans (mem_filter.mp hx).2⟩, hd⟩⟩
    have hn : ((layer y).card : ℂ) ≠ 0 := by exact_mod_cast hcard.card_pos.ne'
    change mass y - (layer y).card * (mass y / (layer y).card) = 0
    rw [mul_comm, div_mul_cancel₀ _ hn, sub_self]
  refine ⟨W, fun x hx => by simp [W, hx], hW, ?_, ?_⟩
  · intro g
    rw [← Finset.sum_fiberwise univ rayReduction]
    apply sum_eq_zero
    intro y _
    change ∑ x ∈ fiber y, W x * g (rayReduction x) = 0
    calc
      _ = ∑ x ∈ fiber y, W x * g y := sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
      _ = 0 := by rw [← sum_mul, hW, zero_mul]
  · intro x
    by_cases hx : rayFourthLayer x
    · have hcard : (layer (rayReduction x)).Nonempty :=
        ⟨x, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, rfl⟩, hx⟩⟩
      have hn : 1 ≤ ((layer (rayReduction x)).card : ℝ) := by exact_mod_cast hcard.card_pos
      rw [show W x = w x - c (rayReduction x) by simp [W,hx]]
      apply (norm_sub_le _ _).trans
      apply add_le_add le_rfl
      calc
        ‖c (rayReduction x)‖ = ‖mass (rayReduction x)‖ / (layer (rayReduction x)).card := by
          simp [c]
        _ ≤ ‖mass (rayReduction x)‖ := div_le_self (norm_nonneg _) hn
        _ ≤ ∑ t ∈ fiber (rayReduction x), ‖w t‖ := norm_sum_le _ _
        _ ≤ ∑ t, ‖w t‖ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    · simpa [W, hx] using (sum_nonneg fun t (_ : t ∈ univ) => norm_nonneg (w t))

/-- Additive Fourier phase of the ray quotient in the self-dual different pairing. -/
def rayPhase (k : ℕ) (h : 𝓔) (x : RayResidue k) : ℂ :=
  differentCharacter (eisEmbedding (h * Quotient.out x) / eisEmbedding (8 * eisLambda ^ k))

@[simp] theorem rayPhase_mk (k : ℕ) (h m : 𝓔) :
    rayPhase k h (Ideal.Quotient.mk (rayModulus k) m) =
      differentCharacter (eisEmbedding (h * m) / eisEmbedding (8 * eisLambda ^ k)) := by
  apply differentCharacter_div_congr
  rw [← mul_sub]
  exact dvd_mul_of_dvd_right (Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (rayModulus k) m)))) h

theorem rayPhase_factor (h : 𝓔) (x : RayResidue 7) :
    rayPhase 7 (eisLambda ^ 4 * h) x = rayPhase 3 h (rayReduction x) := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [rayReduction_mk, rayPhase_mk, map_mul, map_pow, map_ofNat]
  congr 1
  have hl : eisEmbedding eisLambda ≠ 0 :=
    fun he => eisLambda_prime.ne_zero (eisEmbedding_injective (he.trans (map_zero _).symm))
  field_simp

/-- Frequencies surviving the correction have numerator indivisible by λ⁴. -/
theorem rayFourier_ne_zero {W : RayResidue 7 → ℂ} {h : 𝓔}
    (hW : ∀ g : RayResidue 3 → ℂ, ∑ x, W x * g (rayReduction x) = 0)
    (hF : ∑ x, W x * rayPhase 7 h x ≠ 0) : ¬ eisLambda ^ 4 ∣ h := by
  rintro ⟨a,rfl⟩
  exact hF (by simpa only [rayPhase_factor] using hW (rayPhase 3 a))

/-- Numerators on the λ³ layer carry exactly the original modulus 72. -/
theorem ray_mk_lambda_cube_eq_iff (a b : 𝓔) :
    Ideal.Quotient.mk (rayModulus 7) (eisLambda ^ 3 * a) =
      Ideal.Quotient.mk (rayModulus 7) (eisLambda ^ 3 * b) ↔
    Ideal.Quotient.mk (span {(72 : 𝓔)}) a = Ideal.Quotient.mk (span {(72 : 𝓔)}) b := by
  have hmod : (8 : 𝓔) * eisLambda ^ 7 = eisLambda ^ 3 * 72 := by
    calc
      _ = eisLambda ^ 3 * (8 * eisLambda ^ 4) := by ring
      _ = _ := by rw [lambda_four_eq_nine]; norm_num
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq]
  change  _ ∈ span {8 * eisLambda ^ 7} ↔ _ ∈ span {(72 : 𝓔)}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← mul_sub, hmod]
  exact mul_dvd_mul_iff_left (pow_ne_zero 3 eisLambda_prime.ne_zero)

/-- Lift a weight on the original ray modulus, assigning zero off the λ³ multiples. -/
theorem exists_rayWeight (v : (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ) :
    ∃ w : RayResidue 7 → ℂ,
      (∀ a, w (Ideal.Quotient.mk (rayModulus 7) (eisLambda ^ 3 * a)) =
        v (Ideal.Quotient.mk _ a)) ∧ (∀ x, w x ≠ 0 → rayDivides 3 x) := by
  classical
  let P (x : RayResidue 7) (a : 𝓔) := Ideal.Quotient.mk (rayModulus 7) (eisLambda ^ 3 * a) = x
  let w (x : RayResidue 7) := if he : ∃ a, P x a then
    v (Ideal.Quotient.mk _ he.choose) else 0
  refine ⟨w, fun a => ?_, fun x hx => ?_⟩
  · have he : ∃ b, P (Ideal.Quotient.mk (rayModulus 7) (eisLambda ^ 3 * a)) b := ⟨a,rfl⟩
    dsimp only [w]
    rw [dite_eq_left he]
    exact congrArg v ((ray_mk_lambda_cube_eq_iff _ _).mp he.choose_spec)
  · by_cases he : ∃ a, P x a
    · obtain ⟨a,rfl⟩ := he
      exact (rayDivides_mk (by decide) _).mpr (dvd_mul_right _ _)
    · exact (hx (by simp [w,he])).elim

/-- A denominator of the horizontal shift λ² h/(8λ⁷) contains λ² at each
surviving Fourier frequency. -/
theorem rayShift_denominator {h a c : 𝓔} (hh : ¬ eisLambda ^ 4 ∣ h)
    (hac : eisLambda ^ 2 * h * c = a * (8 * eisLambda ^ 7)) : eisLambda ^ 2 ∣ c := by
  have hprod : h * c = eisLambda ^ 5 * (8 * a) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 eisLambda_prime.ne_zero)
    calc
      _ = eisLambda ^ 2 * h * c := by ring
      _ = a * (8 * eisLambda ^ 7) := hac
      _ = _ := by ring
  have hv := (pow_dvd_iff_le_emultiplicity.mp (Dvd.intro (8 * a) hprod.symm))
  rw [emultiplicity_mul eisLambda_prime] at hv
  by_contra hc
  have h₁ := emultiplicity_lt_iff_not_dvd.mpr hh
  have h₂ := emultiplicity_lt_iff_not_dvd.mpr hc
  obtain ⟨i,hi⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h₁)
  obtain ⟨j,hj⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h₂)
  rw [← hi] at h₁ hv
  rw [← hj] at h₂ hv
  norm_cast at h₁ h₂ hv
  omega

/-- The layer correction contributes zero to each Patterson coefficient. -/
theorem rayProjection_mul_patterson {τ : ℂ → ℂ} (hτ : PattersonCoefficients τ)
    {W w : RayResidue 7 → ℂ} (hW : ∀ x, ¬ rayFourthLayer x → W x = w x) (m : 𝓔) :
    W (Ideal.Quotient.mk (rayModulus 7) m) * τ (eisEmbedding m / eisEmbedding eisLambda ^ 3) =
      w (Ideal.Quotient.mk (rayModulus 7) m) * τ (eisEmbedding m / eisEmbedding eisLambda ^ 3) := by
  by_cases h : rayFourthLayer (Ideal.Quotient.mk (rayModulus 7) m)
  · obtain ⟨h₄,h₅⟩ := (rayFourthLayer_mk _).mp h
    rw [hτ.zero_of_lambda_four h₄ h₅, mul_zero, mul_zero]
  · rw [hW _ h]

open scoped Classical in
/-- The primary local weight at 2 and 3 before division by λ³. -/
def primaryRayWeight (ψ : (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ) (a : 𝓔) : ℂ :=
  if eisPrimary a ∧ IsUnit (Ideal.Quotient.mk (span {(6 : 𝓔)}) a) then
    eisEmbedding (cubicSymbol eisLambda a) * ψ (Ideal.Quotient.mk _ a) else 0

theorem primaryRayWeight_congr (hR : DunnRadziwillReciprocity)
    (ψ : (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ) {a b : 𝓔}
    (h : Ideal.Quotient.mk (span {(72 : 𝓔)}) a = Ideal.Quotient.mk _ b) :
    primaryRayWeight ψ a = primaryRayWeight ψ b := by
  have hd : (72 : 𝓔) ∣ a - b := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have h₃ : (3 : 𝓔) ∣ a - b := (show (3 : 𝓔) ∣ 72 from ⟨24, by norm_num⟩).trans hd
  have h₆ : Ideal.Quotient.mk (span {(6 : 𝓔)}) a = Ideal.Quotient.mk _ b := Ideal.Quotient.eq.mpr
    (Ideal.mem_span_singleton.mpr ((show (6 : 𝓔) ∣ 72 from ⟨12, by norm_num⟩).trans hd))
  have hp : eisPrimary a ↔ eisPrimary b := by
    unfold eisPrimary
    exact ⟨fun ha => by simpa only [sub_sub_sub_cancel_left] using dvd_sub ha h₃,
      fun hb => by simpa only [sub_add_sub_cancel] using dvd_add h₃ hb⟩
  have hc : (eisPrimary a ∧ IsUnit (Ideal.Quotient.mk (span {(6 : 𝓔)}) a)) ↔
      (eisPrimary b ∧ IsUnit (Ideal.Quotient.mk (span {(6 : 𝓔)}) b)) :=
    and_congr hp (congrArg IsUnit h₆).to_iff
  unfold primaryRayWeight
  by_cases ha : eisPrimary a ∧ IsUnit (Ideal.Quotient.mk (span {(6 : 𝓔)}) a)
  · have hb := hc.mp ha
    have h₉ : (9 : 𝓔) ∣ a - b := (show (9 : 𝓔) ∣ 72 from ⟨8, by norm_num⟩).trans hd
    rw [ite_eq_left ha, ite_eq_left hb, (cubic_supplements_congr hR hb.1 h₉).1, h]
  · rw [ite_eq_right ha, ite_eq_right (mt hc.mpr ha)]

/-- The actual primary local weight lifts to a periodic numerator weight. -/
theorem exists_primaryRayWeight (hR : DunnRadziwillReciprocity)
    (ψ : (𝓔 ⧸ span {(72 : 𝓔)}) → ℂ) :
    ∃ w : RayResidue 7 → ℂ,
      (∀ a, w (Ideal.Quotient.mk (rayModulus 7) (eisLambda ^ 3 * a)) =
        primaryRayWeight ψ a) ∧ (∀ x, w x ≠ 0 → rayDivides 3 x) := by
  obtain ⟨w, hw, hs⟩ := exists_rayWeight (fun x => primaryRayWeight ψ (Quotient.out x))
  exact ⟨w, fun a => (hw a).trans (primaryRayWeight_congr hR ψ (Ideal.Quotient.mk_out _)), hs⟩

end Masullo.QRH.MeanSquare
