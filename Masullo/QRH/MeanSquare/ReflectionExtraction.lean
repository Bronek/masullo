import Masullo.QRH.MeanSquare.ReflectionIndex
import Masullo.QRH.MeanSquare.ReflectionTame
import Masullo.QRH.MeanSquare.ReflectionSummation

/-! # Extracting forced divisors at the exceptional tame primes -/

noncomputable section

open NumberField Ideal Finset

namespace Masullo.QRH.MeanSquare.ReflectionSieve.TameBranch

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- Nonzero-frequency branches at a prime of the fixed part of the conductor. -/
def activeChoices (j : ℕ) : Finset TameBranch :=
  if j = 4 then {.principal,.dividesSquarefree,.dividesCube}
  else if j = 0 then {.principal} else {.ordinary}

def squarefreeDivisor {M : Type*} [One M] (q : M) (e : TameBranch) : M :=
  if e = .dividesSquarefree then q else 1

def cubeDivisor {M : Type*} [One M] (q : M) (e : TameBranch) : M :=
  if e = .dividesCube then q else 1

section Local

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Contribution before dividing out the forced factors of the squarefree and cube ideals. -/
def piece (χ : MulChar F ℂ) (j : ℕ) (u : Fˣ) (n b : F) : TameBranch → ℂ
  | .inactive => 0
  | .ordinary => ReflectionTame.factor χ j ((u : F)*n*b^3)
  | .principal => if j = 4 then -1 / Real.sqrt (Fintype.card F) else ReflectionTame.factor χ j
    ((u : F)*n*b^3)
  | .dividesSquarefree => if n = 0 then Real.sqrt (Fintype.card F) else 0
  | .dividesCube => if n ≠ 0 ∧ b = 0 then Real.sqrt (Fintype.card F) else 0

theorem factor_eq_sum (χ : MulChar F ℂ) (j : ℕ) (u : Fˣ) (n b : F) :
    ReflectionTame.factor χ j ((u:F)*n*b^3) = ∑ e ∈ activeChoices j, piece χ j u n b e := by
  classical
  by_cases h4 : j = 4
  · subst j
    rw [ReflectionTame.factor_four_mul_cube]
    have hq : 0 < (Fintype.card F : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hh := congrArg Complex.ofReal (Real.sq_sqrt hq.le)
    push_cast at hh
    by_cases hn : n = 0 <;> by_cases hb : b = 0 <;>
      simp [activeChoices,piece,hn,hb] <;> field_simp <;> linear_combination -hh
  · by_cases h0 : j = 0 <;> simp [activeChoices,piece,h4,h0]

private theorem norm_char_le (χ : MulChar F ℂ) (a : F) : ‖χ a‖ ≤ 1 := by
  by_cases h : IsUnit a
  · simpa [h.unit_spec] using (Complex.norm_eq_one_of_mem_rootsOfUnity
      (χ.apply_mem_rootsOfUnity h.unit)).le
  · simp [χ.map_nonunit h]

/-- Dividing by the norm factors introduced by extraction gives exactly the
local coefficient budget, including the extra square root in the cube branch. -/
theorem norm_piece_div (χ : MulChar F ℂ) (j : ℕ) (u : Fˣ) (n b : F)
    (e : TameBranch) (he : e ∈ activeChoices j) :
    let q : ℝ := Fintype.card F
    ‖piece χ j u n b e‖ / (Real.sqrt (squarefreeDivisor q e) * cubeDivisor q e) ≤ Real.sqrt
      (e.weightSq q) := by
  let q : ℝ := Fintype.card F
  have hq : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q / q = (Real.sqrt q)⁻¹ := by
    field_simp; nlinarith [Real.sq_sqrt hq.le]
  have hr : ‖(Real.sqrt q : ℂ)‖ = Real.sqrt q := by simp [Real.sqrt_nonneg]
  change ‖piece χ j u n b e‖ / (Real.sqrt (squarefreeDivisor q e)*cubeDivisor q e) ≤
    Real.sqrt (e.weightSq q)
  by_cases h4 : j = 4
  · simp [activeChoices,h4] at he
    rcases he with rfl | rfl | rfl
    · simp [piece,h4,squarefreeDivisor,cubeDivisor,weightSq,show (Fintype.card F : ℝ) = q from rfl,
        abs_of_nonneg hs.le,Real.sqrt_inv,one_div]
    · by_cases h : n = 0 <;> simp [piece,h,squarefreeDivisor,cubeDivisor,weightSq,
        show (Fintype.card F : ℝ) = q from rfl,abs_of_nonneg hs.le,hs.ne']
    · by_cases h : n ≠ 0 ∧ b=0 <;> simp [piece,h,squarefreeDivisor,cubeDivisor,weightSq,
        show (Fintype.card F : ℝ) = q from rfl,abs_of_nonneg hs.le,hsq,Real.sqrt_inv]
  · by_cases h0 : j = 0
    · have he' : e = .principal := by simpa [activeChoices,h4,h0] using he
      subst e
      simp only [piece,h0,ReflectionTame.factor,ite_false,ite_true,reduceCtorEq,squarefreeDivisor,
        cubeDivisor,weightSq,norm_div,Real.sqrt_one,one_mul,div_one,Real.sqrt_inv]
      change ‖_‖ / ‖(Real.sqrt q : ℂ)‖ ≤ _
      rw [hr,div_eq_mul_inv]
      exact (mul_le_mul_of_nonneg_right (norm_char_le _ _)
        (inv_nonneg.mpr hs.le)).trans_eq (one_mul _)
    · have he' : e = .ordinary := by simpa [activeChoices,h4,h0] using he
      subst e
      simpa only [piece,h4,h0,ReflectionTame.factor,ite_false,reduceCtorEq,squarefreeDivisor,
        cubeDivisor,weightSq,Real.sqrt_one,one_mul,div_one] using
        norm_char_le ((χ^(j+2))⁻¹) ((u:F)*n*b^3)

end Local

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
variable [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]

/-- Expand every exceptional prime at once. A prime occurs in the squarefree or
cube divisor only on the corresponding branch of the three-term expression. -/
theorem factor_product (χ : ∀ i, MulChar (F i) ℂ) (j : ι → ℕ) (u : ∀ i, (F i)ˣ)
    (n b : ∀ i, F i) :
    ∏ i, ReflectionTame.factor (χ i) (j i) ((u i : F i)*n i*(b i)^3) =
      ∑ e ∈ Fintype.piFinset (fun i => activeChoices (j i)), ∏ i, piece (χ i) (j i) (u i) (n i)
        (b i) (e i) := by
  simp_rw [factor_eq_sum]
  exact prod_univ_sum ..

omit [DecidableEq ι] in
/-- Coefficient estimate after extracting the two forced ideals, in product form. -/
theorem norm_product_div (χ : ∀ i, MulChar (F i) ℂ) (j : ι → ℕ) (u : ∀ i, (F i)ˣ)
    (n b : ∀ i, F i) (e : ι → TameBranch) (he : ∀ i, e i ∈ activeChoices (j i)) :
    let q := fun i => (Fintype.card (F i) : ℝ)
    ‖∏ i, piece (χ i) (j i) (u i) (n i) (b i) (e i)‖ /
      (Real.sqrt (∏ i, squarefreeDivisor (q i) (e i)) * ∏ i, cubeDivisor (q i) (e i)) ≤
        Real.sqrt (∏ i, (e i).weightSq (q i)) := by
  let q := fun i => (Fintype.card (F i) : ℝ)
  have hq (i : ι) : 0 < q i := Nat.cast_pos.mpr Fintype.card_pos
  have hD (i : ι) : 0 ≤ squarefreeDivisor (q i) (e i) := by
    dsimp [squarefreeDivisor]; split <;> positivity
  have hW (i : ι) : 0 ≤ (e i).weightSq (q i) := by
    cases e i <;> simp only [weightSq] <;> positivity
  have hB (i : ι) : 0 ≤ cubeDivisor (q i) (e i) := by
    dsimp [cubeDivisor]; split <;> positivity
  dsimp only
  rw [norm_prod, Real.sqrt_prod _ (fun i _ => hD i), Real.sqrt_prod _ (fun i _ => hW i),
    ← prod_mul_distrib,← prod_div_distrib]
  exact prod_le_prod₀ (fun i _ => div_nonneg (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (hB i)))
    (fun i _ => norm_piece_div (χ i) (j i) (u i) (n i) (b i) (e i) (he i))

end Product

/-- The conductor gain is divided by the extracted squarefree norm and by the
cube of the extracted cube-ideal norm. -/
theorem product_length {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (e : ι → TameBranch) (he : ∀ i, e i ≠ .inactive) :
    (∏ i, q i)^2 / ((∏ i, squarefreeDivisor (q i) (e i)) * (∏ i, cubeDivisor (q i) (e i))^3) =
      ∏ i, (e i).length (q i) := by
  rw [← prod_pow,← prod_pow,← prod_mul_distrib,← prod_div_distrib]
  apply prod_congr rfl
  intro i _
  cases h : e i
  · exact (he i h).elim
  all_goals simp [length,squarefreeDivisor,cubeDivisor]
  all_goals field_simp [(hq i).ne']

section Ideals

attribute [local instance] Ideal.Quotient.field

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Ideal 𝓔)
variable [∀ i, (p i).IsMaximal] [∀ i, Fintype (𝓔 ⧸ p i)] [∀ i, DecidableEq (𝓔 ⧸ p i)]

omit [DecidableEq ι] in
/-- The local zero conditions force the products of all the selected primes to divide
the squarefree ideal and the cube ideal respectively. -/
theorem piece_divisors (hp : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (χ : ∀ i, MulChar (𝓔 ⧸ p i) ℂ) (j : ι → ℕ) (u : ∀ i, (𝓔 ⧸ p i)ˣ)
    (n b : Ideal 𝓔) (e : ι → TameBranch)
    (hne : (∏ i, piece (χ i) (j i) (u i) (Ideal.Quotient.mk (p i) (generator n))
      (Ideal.Quotient.mk (p i) (generator b)) (e i)) ≠ 0) :
    (∏ i, squarefreeDivisor (p i) (e i)) ∣ n ∧ (∏ i, cubeDivisor (p i) (e i)) ∣ b := by
  classical
  have nz (i : ι) := (prod_ne_zero_iff.mp hne) i (mem_univ i)
  have hdiv {a : Ideal 𝓔} {i : ι} (h : Ideal.Quotient.mk (p i) (generator a) = 0) : p i ∣ a := by
    apply dvd_iff_le.mpr
    rw [← span_generator a]
    exact (span_singleton_le_iff_mem _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  constructor
  · simp only [squarefreeDivisor,← prod_filter]
    apply prod_dvd_of_coprime (hp.set_pairwise _)
    intro i hi
    have hi' := (mem_filter.mp hi).2
    apply hdiv
    by_contra h
    exact nz i (by simp [hi',piece,h])
  · simp only [cubeDivisor,← prod_filter]
    apply prod_dvd_of_coprime (hp.set_pairwise _)
    intro i hi
    have hi' := (mem_filter.mp hi).2
    apply hdiv
    by_contra h
    exact nz i (by simp [hi',piece,h])

/-- Reindex both ideal variables by their extracted divisors. The residual
weight retains all coprimality and squarefreeness restrictions through its zeros. -/
theorem tsum_extract {N B : Ideal 𝓔} (hN : N ≠ 0) (hB : B ≠ 0)
    (f : Ideal 𝓔 × Ideal 𝓔 → ℂ) (h : ∀ a, f a ≠ 0 → N ∣ a.1 ∧ B ∣ a.2) :
    ∑' x, f x = ∑' x : Ideal 𝓔 × Ideal 𝓔, f (N*x.1,B*x.2) := by
  let g := fun x : Ideal 𝓔 × Ideal 𝓔 => (N*x.1,B*x.2)
  have hg : Function.Injective g := fun _ _ he =>
    Prod.ext (mul_left_cancel₀ hN (congrArg Prod.fst he))
      (mul_left_cancel₀ hB (congrArg Prod.snd he))
  apply (hg.tsum_eq ?_).symm
  intro a ha
  obtain ⟨⟨n,hn⟩,⟨b,hb⟩⟩ := h a ha
  exact ⟨(n,b),Prod.ext hn.symm hb.symm⟩

omit [DecidableEq ι] in
/-- The equality of the extracted branch sums, with an arbitrary weight on
the pair of ideals. The diagonal substitution is injective even when a prime
already divides both the squarefree and the cube parameters. -/
theorem extract_branch (hp : Pairwise (fun i j => IsCoprime (p i) (p j))) (hnz : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (𝓔 ⧸ p i) ℂ) (j : ι → ℕ) (u : ∀ i, (𝓔 ⧸ p i)ˣ) (e : ι → TameBranch)
    (f : Ideal 𝓔 × Ideal 𝓔 → ℂ) :
    let P := fun x : Ideal 𝓔 × Ideal 𝓔 => ∏ i, piece (χ i) (j i) (u i)
      (Ideal.Quotient.mk (p i) (generator x.1)) (Ideal.Quotient.mk (p i) (generator x.2)) (e i)
    let N := ∏ i, squarefreeDivisor (p i) (e i)
    let B := ∏ i, cubeDivisor (p i) (e i)
    (∑' x, P x * f x) = ∑' x : Ideal 𝓔 × Ideal 𝓔, P (N*x.1,B*x.2) * f (N*x.1,B*x.2) := by
  dsimp only
  apply tsum_extract
  · exact prod_ne_zero_iff.mpr fun i _ => by
      dsimp [squarefreeDivisor]; split <;> first | exact hnz i | exact one_ne_zero
  · exact prod_ne_zero_iff.mpr fun i _ => by
      dsimp [cubeDivisor]; split <;> first | exact hnz i | exact one_ne_zero
  · intro x hx
    exact piece_divisors p hp χ j u x.1 x.2 e (left_ne_zero_of_mul hx)

omit [DecidableEq ι] in
/-- The norm of the extracted column coefficient is bounded by the budget
whose square occurs in (16). -/
theorem norm_extracted_coefficient (χ : ∀ i, MulChar (𝓔 ⧸ p i) ℂ) (j : ι → ℕ)
    (u : ∀ i, (𝓔 ⧸ p i)ˣ) (e : ι → TameBranch) (he : ∀ i, e i ∈ activeChoices (j i))
    (n b : Ideal 𝓔) :
    let N := ∏ i, squarefreeDivisor (p i) (e i)
    let B := ∏ i, cubeDivisor (p i) (e i)
    ‖∏ i, piece (χ i) (j i) (u i) (Ideal.Quotient.mk (p i) (generator n))
        (Ideal.Quotient.mk (p i) (generator b)) (e i)‖ /
      (Real.sqrt (absNorm N) * (absNorm B : ℝ)) ≤ Real.sqrt (∏ i,
        (e i).weightSq (absNorm (p i))) := by
  have hq (i : ι) : (Fintype.card (𝓔 ⧸ p i) : ℝ) = absNorm (p i) := by
    rw [Ideal.absNorm_eq_natCard,Nat.card_eq_fintype_card]
  have hn (i : ι) : (absNorm (squarefreeDivisor (p i) (e i)) : ℝ) = squarefreeDivisor
    (absNorm (p i) : ℝ) (e i) := by
    dsimp [squarefreeDivisor]; split <;> simp
  have hb (i : ι) : (absNorm (cubeDivisor (p i) (e i)) : ℝ) = cubeDivisor
    (absNorm (p i) : ℝ) (e i) := by
    dsimp [cubeDivisor]; split <;> simp
  simpa only [map_prod,Nat.cast_prod,hq,hn,hb] using
    norm_product_div χ j u (fun i => Ideal.Quotient.mk (p i) (generator n))
      (fun i => Ideal.Quotient.mk (p i) (generator b)) e he

end Ideals

end Masullo.QRH.MeanSquare.ReflectionSieve.TameBranch
