import Masullo.QRH.MeanSquare.ReflectionBands
import Masullo.QRH.MeanSquare.ReflectionInversion

/-! # The fixed tame primes on the ideal-indexed dual side -/

noncomputable section

open NumberField Ideal Finset Complex
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare.ReflectionSieve

open ReflectionVaryingRows TameBranch ReflectionInversion

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- A selected exceptional-prime summand evaluated on ideal variables. -/
def idealPiece (p : Idl) (j : ℕ) (e : TameBranch) (m : 𝓔) (n b : Idl) : ℂ := open Classical in
  match e with
  | .inactive => 0
  | .ordinary => reflectedFactor p j m
  | .principal => if j = 4 then -1 / Real.sqrt (absNorm p) else reflectedFactor p j m
  | .dividesSquarefree => if p ∣ n then Real.sqrt (absNorm p) else 0
  | .dividesCube => if ¬p ∣ n ∧ p ∣ b then Real.sqrt (absNorm p) else 0

private theorem red_zero_iff_dvd (p a : Idl) : Ideal.Quotient.mk p (generator a) = 0 ↔ p ∣ a := by
  rw [Ideal.Quotient.eq_zero_iff_mem, dvd_iff_le,← span_singleton_le_iff_mem,span_generator]

private theorem unit_mod {p : Idl} (hp : AwayFromSix p) (h : ℕ) (u : 𝓔ˣ) :
    IsUnit (Ideal.Quotient.mk p (eisLambda^h * u)) := by
  rw [map_mul,map_pow]
  exact ((isUnit_mk_iff_coprime_span p _).mpr (coprime_span_lambda hp)).pow h |>.mul (u.isUnit.map _)

attribute [local instance] Ideal.Quotient.field

private theorem idealPiece_eq {p : Idl} (hp : AwayFromSix p) (hpp : Prime p) [p.IsMaximal]
    [Fintype (𝓔 ⧸ p)] [DecidableEq (𝓔 ⧸ p)] (j : ℕ) (e : TameBranch) (x : ReflectedIndex) :
    idealPiece p j e x.numerator x.n x.b =
      piece (sexticChar hp) j (unit_mod hp x.exponent x.unit).unit
        (Ideal.Quotient.mk p (generator x.n)) (Ideal.Quotient.mk p (generator x.b)) e := by
  classical
  have hm : x.numerator = (eisLambda^x.exponent * x.unit) * generator x.n * generator x.b ^ 3 := by
    dsimp [ReflectedIndex.numerator]; ring
  have hf : reflectedFactor p j x.numerator =
      ReflectionTame.factor (sexticChar hp) j (Ideal.Quotient.mk p x.numerator) := by
    rw [reflectedFactor,dite_eq_left (And.intro hp hpp)]
    dsimp only
    simp only [ReflectionTame.factor,← Nat.card_eq_fintype_card]
  cases e <;> simp only [idealPiece,piece,hf,IsUnit.unit_spec,← map_pow,← map_mul,← hm,
    ne_eq,red_zero_iff_dvd,← Nat.card_eq_fintype_card,← Ideal.absNorm_eq_natCard]

/-- Simultaneous local expansion at an actual signed Patterson index. -/
theorem reflected_product_eq_choices (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p)
    (j : Idl → ℕ) (x : ReflectedIndex) :
    (∏ p ∈ F, reflectedFactor p (j p) x.numerator) =
      ∑ e ∈ Fintype.piFinset (fun p : F => activeChoices (j p)),
        ∏ p : F, idealPiece p (j p) (e p) x.numerator x.n x.b := by
  classical
  let (p : F) : p.val.IsMaximal := ((Ideal.prime_iff_isPrime (hF p p.2).2.ne_zero).mp (hF p p.2).2).isMaximal (hF p p.2).2.ne_zero
  let (p : F) : Finite (𝓔 ⧸ p.val) := Ring.HasFiniteQuotients.finiteQuotient (hF p p.2).1.1
  let (p : F) : Fintype (𝓔 ⧸ p.val) := Fintype.ofFinite _
  have hf (p : F) : reflectedFactor p (j p) x.numerator =
      ∑ e ∈ activeChoices (j p), idealPiece p (j p) e x.numerator x.n x.b := by
    simp_rw [idealPiece_eq (hF p p.2).1 (hF p p.2).2]
    rw [← factor_eq_sum,IsUnit.unit_spec]
    have hm : (eisLambda ^ x.exponent * x.unit) * generator x.n * generator x.b^3 = x.numerator := by
      dsimp [ReflectedIndex.numerator]; ring
    rw [← map_pow,← map_mul,← map_mul,hm,reflectedFactor,dite_eq_left (hF p p.2)]
  rw [← F.prod_coe_sort]
  simp_rw [hf]
  exact prod_univ_sum ..

/-- Norms of the two ideals whose products have been extracted on a branch. -/
def extractedN (F : Finset Idl) (e : F → TameBranch) : Idl := ∏ p : F, squarefreeDivisor p.val (e p)
def extractedB (F : Finset Idl) (e : F → TameBranch) : Idl := ∏ p : F, cubeDivisor p.val (e p)

theorem extracted_coprime (F : Finset Idl) (e : F → TameBranch) (hF : ∀ p ∈ F, AwayFromSix p) :
    AwayFromSix (extractedN F e) ∧ AwayFromSix (extractedB F e) := by
  have hprod (f : F → Idl) (hf : ∀ p, AwayFromSix (f p)) : AwayFromSix (∏ p, f p) := by
    exact ⟨prod_ne_zero_iff.mpr (fun i _ => (hf i).1),IsCoprime.prod_left fun i _ => (hf i).2⟩
  constructor <;> apply hprod <;> intro i
  · dsimp [squarefreeDivisor]; split <;> first | exact hF i i.2 | exact ⟨one_ne_zero,isCoprime_one_left⟩
  · dsimp [cubeDivisor]; split <;> first | exact hF i i.2 | exact ⟨one_ne_zero,isCoprime_one_left⟩

theorem idealPiece_product_bound (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p)
    (j : Idl → ℕ) (e : F → TameBranch) (he : ∀ p : F, e p ∈ activeChoices (j p.val)) (x : ReflectedIndex) :
    ‖∏ p : F, idealPiece p (j p) (e p) x.numerator x.n x.b‖ /
      (Real.sqrt (absNorm (extractedN F e)) * (absNorm (extractedB F e) : ℝ)) ≤
      Real.sqrt (∏ p : F, (e p).weightSq (absNorm p.val)) := by
  classical
  let (p : F) : p.val.IsMaximal := ((Ideal.prime_iff_isPrime (hF p p.2).2.ne_zero).mp (hF p p.2).2).isMaximal (hF p p.2).2.ne_zero
  let (p : F) : Finite (𝓔 ⧸ p.val) := Ring.HasFiniteQuotients.finiteQuotient (hF p p.2).1.1
  let (p : F) : Fintype (𝓔 ⧸ p.val) := Fintype.ofFinite _
  simp_rw [idealPiece_eq (hF _ (Subtype.prop _)).1 (hF _ (Subtype.prop _)).2]
  exact norm_extracted_coefficient (fun p : F => p.val) _ _ _ e he _ _

/-- The support of a selected local product lies on multiples of both extracted ideals. -/
theorem idealPiece_product_dvd (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p)
    (j : Idl → ℕ) (e : F → TameBranch) (m : 𝓔) (n b : Idl)
    (hne : (∏ p : F, idealPiece p (j p) (e p) m n b) ≠ 0) :
    extractedN F e ∣ n ∧ extractedB F e ∣ b := by
  classical
  have hp {p q : F} (h : p ≠ q) : IsCoprime p.val q.val := by
    let (i : F) : i.val.IsMaximal := ((Ideal.prime_iff_isPrime (hF i i.2).2.ne_zero).mp (hF i i.2).2).isMaximal (hF i i.2).2.ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun hh => h (Subtype.ext hh))
  have nz (p : F) := (prod_ne_zero_iff.mp hne) p (mem_univ p)
  constructor
  · simp only [extractedN,squarefreeDivisor,← prod_filter]
    apply prod_dvd_of_coprime (fun _ _ _ _ h => hp h)
    intro i hi
    by_contra hv
    exact nz i (by simp [idealPiece,(mem_filter.mp hi).2,hv])
  · simp only [extractedB,cubeDivisor,← prod_filter]
    apply prod_dvd_of_coprime (fun _ _ _ _ h => hp h)
    intro i hi
    by_contra hv
    exact nz i (by simp [idealPiece,(mem_filter.mp hi).2,hv])

theorem extracted_length (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p)
    (e : F → TameBranch) (he : ∀ p, e p ≠ .inactive) :
    (∏ p : F, (absNorm p.val : ℝ))^2 /
      ((absNorm (extractedN F e) : ℝ)*(absNorm (extractedB F e) : ℝ)^3) =
        ∏ p : F, (e p).length (absNorm p.val) := by
  have hn (p : F) : (absNorm (squarefreeDivisor p.val (e p)) : ℝ) = squarefreeDivisor (absNorm p.val : ℝ) (e p) := by
    dsimp [squarefreeDivisor]; split <;> simp
  have hb (p : F) : (absNorm (cubeDivisor p.val (e p)) : ℝ) = cubeDivisor (absNorm p.val : ℝ) (e p) := by
    dsimp [cubeDivisor]; split <;> simp
  simp only [extractedN,extractedB,map_prod,Nat.cast_prod,hn,hb]
  exact product_length (fun i : F => (absNorm i.val : ℝ)) (fun i => zero_lt_one.trans_le (absNorm_one_le (hF i i.2).1)) e he

end Masullo.QRH.MeanSquare.ReflectionSieve
