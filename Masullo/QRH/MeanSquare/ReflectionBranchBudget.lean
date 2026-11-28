import Masullo.QRH.MeanSquare.ReflectionFamilyAssembly
import Masullo.QRH.MeanSquare.ReflectionIdealBranches

/-! # Amplitude and length budgets for an active tame branch -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid
open scoped Classical

namespace Masullo.QRH.MeanSquare.ReflectionSieve.BranchBudget

open ReflectionRowInversion ReflectionInversion TameBranch

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

def H : ℝ := 1 + Fintype.card (RayResidue 7)

def B : ℝ := max H ((elementNorm (8*eisLambda^7) : ℝ)^2)

theorem one_le_H : 1 ≤ H := by dsimp [H]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem one_le_B : 1 ≤ B := one_le_H.trans (le_max_left ..)

theorem H_le_B : H ≤ B := le_max_left ..

def choice (F : Finset Idl) (e : F → TameBranch) (p : Idl) : TameBranch :=
  if hp : p ∈ F then e ⟨p,hp⟩ else .inactive

@[simp] theorem choice_apply (F : Finset Idl) (e : F → TameBranch) (p : F) :
    choice F e p = e p := by simp [choice, p.2]

@[simp] theorem choice_outside {F : Finset Idl} (e : F → TameBranch) {p : Idl} (hp : p ∉ F) :
    choice F e p = .inactive := by simp [choice, hp]

theorem primes_good {T G : Idl} (hT : AwayFromSix T) (hG : AwayFromSix G) {F : Finset Idl}
    (hF : F ⊆ support (T*G)) (p : Idl) (hp : p ∈ F) : AwayFromSix p ∧ Prime p := by
  have hn := hT.mul hG
  obtain ⟨hP,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn.1).mp
    (Multiset.mem_toFinset.mp (hF hp))
  exact ⟨⟨hP.ne_zero,hn.2.of_isCoprime_of_dvd_left hd⟩,hP⟩

def Q {h : RayResidue 7} (D : FixedCusp h) (F : Finset Idl) : ℝ :=
  (elementNorm D.c : ℝ) * ∏ p ∈ F, (absNorm p : ℝ)

def N (i : Fin 2) (F : Finset Idl) (e : F → TameBranch) : ℝ :=
  absNorm (twoPart i * extractedN F e)

def L (F : Finset Idl) (e : F → TameBranch) : ℝ := absNorm (extractedB F e)

def a (F : Finset Idl) (e : F → TameBranch) : ℝ :=
  H * Real.sqrt (∏ p : F, (e p).weightSq (absNorm p.val))

private theorem prod_choice {F : Finset Idl} {e : F → TameBranch} (f : TameBranch → Idl → ℝ) :
    (∏ p ∈ F, f (choice F e p) p) = ∏ p : F, f (e p) p := by
  rw [← prod_finset_coe (fun p => f (choice F e p) p) F]
  simp only [choice_apply]
  congr 1

theorem sqrt_weight_sq (F : Finset Idl) (e : F → TameBranch) :
    (Real.sqrt (∏ p : F, (e p).weightSq (absNorm p.val)))^2 =
    ∏ p : F, (e p).weightSq (absNorm p.val) := by
  apply Real.sq_sqrt
  apply prod_nonneg
  intro p _
  cases e p <;> dsimp [weightSq] <;> positivity

private theorem elementNorm_pos {x : 𝓔} (hx : x ≠ 0) : 0 < (elementNorm x : ℝ) :=
  zero_lt_one.trans_le (absNorm_one_le (mt span_singleton_eq_bot.mp hx))

private theorem fixed_norm_sq_le {h : RayResidue 7} (D : FixedCusp h) :
    (elementNorm D.c : ℝ)^2 ≤ B := by
  have h₀ : 8*eisLambda^7 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ eisLambda_prime.ne_zero)
  obtain ⟨g,hg⟩ := D.dvd_modulus
  have hd : elementNorm D.c ∣ elementNorm (8*eisLambda^7) := by
    refine ⟨elementNorm g, ?_⟩
    rw [hg, elementNorm, ← span_singleton_mul_span_singleton, map_mul]
    rfl
  have hNat : 0 < elementNorm (8*eisLambda^7) := by exact_mod_cast elementNorm_pos h₀
  have hLe : (elementNorm D.c : ℝ) ≤ elementNorm (8*eisLambda^7) := by exact_mod_cast Nat.le_of_dvd hNat hd
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hLe 2).trans (le_max_right ..)

/-- Budget fields of a squarefree kernel branch, before specifying its column
coefficients and row phases. -/
structure Bounds {h : RayResidue 7} (D : FixedCusp h) (F : Finset Idl) (e : F → TameBranch)
    (i : Fin 2) (K X : ℝ) (t y : Idl) : Prop where
  primes_subset : F ⊆ (normalizedFactors t).toFinset ∪ (normalizedFactors y).toFinset
  good : ∀ p ∈ F, AwayFromSix p ∧ Prime p
  simple : ∀ p ∈ F, p ∉ normalizedFactors t → (normalizedFactors y).count p = 1 → choice F e p ≠ .ordinary
  Q_pos : 0 < Q D F
  N_pos : 0 < N i F e
  L_pos : 0 < L F e
  amplitude_nonneg : 0 ≤ a F e
  amplitude : (a F e)^2 ≤ B^2 * ∏ p ∈ F, (choice F e p).weightSq (absNorm p)
  length : (Q D F)^2*K^2/(N i F e * (L F e)^3*X) ≤ B*K^2/X * ∏ p ∈ F, (choice F e p).length (absNorm p)

theorem of_active {K X : ℝ} (hK : 1 ≤ K) (hX : 1 ≤ X) {t y T G : Idl}
    (ht : t ≠ 0) (hy : y ≠ 0) (hT : AwayFromSix T) (hG : AwayFromSix G) (hTt : T ∣ t) (hGy : G ∣ y)
    {h : RayResidue 7} (D : FixedCusp h) (F : Finset Idl) (hF : F ⊆ support (T*G))
    (i : Fin 2) (η : TameAssignment (fun p => exponent T G p % 6) F) : Bounds D F η.val i K X t y := by
  have hgood := primes_good hT hG hF
  have hη := Fintype.mem_piFinset.mp η.2
  have hactive (p : F) : η.val p ≠ .inactive := by
    have hx := hη p
    intro hi
    by_cases hj : exponent T G p % 6 = 4
    · simp [activeChoices, hj, hi] at hx
    · by_cases hj₀ : exponent T G p % 6 = 0 <;> simp [activeChoices, hj, hj₀, hi] at hx
  have hg := extracted_coprime F η.val (fun p hp => (hgood p hp).1)
  have hn : 0 < (absNorm (extractedN F η.val) : ℝ) := zero_lt_one.trans_le (absNorm_one_le hg.1.1)
  have hl : 0 < L F η.val := zero_lt_one.trans_le (absNorm_one_le hg.2.1)
  have h₂ : 1 ≤ (absNorm (twoPart i) : ℝ) :=
    absNorm_one_le (pow_ne_zero _ (mt span_singleton_eq_bot.mp (by norm_num : (-2:𝓔) ≠ 0)))
  have hN : N i F η.val = (absNorm (twoPart i) : ℝ) * absNorm (extractedN F η.val) := by simp [N]
  have hM := elementNorm_pos D.c_ne_zero
  have hq (p : Idl) (hp : p ∈ F) : 0 < (absNorm p : ℝ) := zero_lt_one.trans_le (absNorm_one_le (hgood p hp).1.1)
  have hQ : 0 < Q D F := mul_pos hM (prod_pos hq)
  have hH := zero_lt_one.trans_le one_le_H
  refine ⟨hF.trans (fixedSupport_subset ht hy hTt hGy),hgood,?_,hQ,
    hN ▸ mul_pos (zero_lt_one.trans_le h₂) hn,hl,mul_nonneg hH.le (Real.sqrt_nonneg _),?_,?_⟩
  · intro p hp hpt hpy
    have hj := simple_exponent ht hy hTt hGy (hF hp) (fun hh => hpt (Multiset.mem_toFinset.mp hh)) hpy
    have hx := hη ⟨p,hp⟩
    simp only [hj, Nat.reduceMod, activeChoices, ↓reduceIte] at hx
    intro h
    simp [choice, hp] at h
    simp [h] at hx
  · rw [a, mul_pow, sqrt_weight_sq, prod_choice (fun e p => e.weightSq (absNorm p))]
    apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH.le H_le_B 2)
    rw [← sqrt_weight_sq]
    positivity
  · have hx := zero_lt_one.trans_le hX
    have hscale := extracted_length F (fun p hp => (hgood p hp).1) η.val hactive
    have hprod : (∏ p : F, (absNorm p.val : ℝ)) = ∏ p ∈ F, (absNorm p : ℝ) := by
      rw [← F.prod_coe_sort (fun p => (absNorm p : ℝ))]
    rw [hprod] at hscale
    rw [prod_choice (fun e p => e.length (absNorm p)), ← hscale]
    rw [Q, hN]
    let w := ∏ p ∈ F, (absNorm p : ℝ)
    let n := (absNorm (extractedN F η.val) : ℝ)
    let l := L F η.val
    let d := (absNorm (twoPart i) : ℝ)
    let c := (elementNorm D.c : ℝ)
    change (c*w)^2*K^2/(d*n*l^3*X) ≤ B*K^2/X * (w^2/(n*l^3))
    calc
      _ = c^2 * K^2 / X * (w^2/(n*l^3)) / d := by ring
      _ ≤ c^2 * K^2 / X * (w^2/(n*l^3)) := div_le_self (by positivity) h₂
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (fixed_norm_sq_le D) (sq_nonneg K)) hx.le

end Masullo.QRH.MeanSquare.ReflectionSieve.BranchBudget
