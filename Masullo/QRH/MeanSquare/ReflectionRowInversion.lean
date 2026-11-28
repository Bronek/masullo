import Masullo.QRH.MeanSquare.ReflectionInversion
import Masullo.QRH.MeanSquare.ReflectionVaryingRows
import Masullo.QRH.MeanSquare.ReflectionRows

/-! # Reflection at a fixed squarefree row class -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid
open scoped Classical

namespace Masullo.QRH.MeanSquare.ReflectionRowInversion

open ReflectionVaryingRows ReflectionInversion ReflectionCRT

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔
private abbrev Index := {m : 𝓔 // m ≠ 0}
private abbrev RowResidue := Residue (72*eisLambda^7)
private abbrev FrequencyResidue := Residue (8*eisLambda^9)

def support (n : Idl) := (normalizedFactors n).toFinset

def exponent (t g p : Idl) := (normalizedFactors t).count p + 4*(normalizedFactors g).count p

private def active {α : Type*} [DecidableEq α] (K H F : Finset α) : Finset (K ∪ H : Finset α) :=
  (K∪F).subtype (· ∈ K∪H)

private lemma regroup {α : Type*} [DecidableEq α] {K H : Finset α} (hd : Disjoint K H)
    (f : Finset (K∪H : Finset α) → ℂ)
    (hz : ∀ s, f s ≠ 0 → ∀ p ∈ K, ∀ hp : p ∈ K∪H, (⟨p,hp⟩ : (K∪H : Finset α)) ∈ s) :
    ∑ s, f s = ∑ F ∈ H.powerset, f (active K H F) := by
  classical
  let keep (s : Finset (K∪H : Finset α)) := ∀ p ∈ K, ∀ hp : p ∈ K∪H, (⟨p,hp⟩ : (K∪H : Finset α)) ∈ s
  rw [← sum_filter_of_ne (p := keep) (fun s _ hs => hz s hs)]
  let rest (s : Finset (K∪H : Finset α)) := s.map (Function.Embedding.subtype _) \ K
  have hrest (s : Finset (K∪H : Finset α)) : rest s ⊆ H := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := mem_sdiff.mp hp
    obtain ⟨x, _, rfl⟩ := mem_map.mp h₁
    exact (mem_union.mp x.2).resolve_left h₂
  have hfull {s : Finset (K∪H : Finset α)} (hs : keep s) : active K H (rest s) = s := by
    ext x
    simp only [active,mem_subtype,mem_union,rest,mem_sdiff,mem_map,Function.Embedding.subtype_apply]
    constructor
    · rintro (h | ⟨⟨y,hy,he⟩,_⟩)
      · exact hs _ h _
      · exact (Subtype.ext he : y = x) ▸ hy
    · intro h
      by_cases hx : x.val ∈ K
      · exact Or.inl hx
      · exact Or.inr ⟨⟨x,h,rfl⟩,hx⟩
  have hfix {F : Finset α} (hF : F ⊆ H) : rest (active K H F) = F := by
    ext p
    simp only [rest,mem_sdiff,mem_map,Function.Embedding.subtype_apply,active,mem_subtype,mem_union]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hx'⟩
      exact hx.resolve_left hx'
    · intro hp
      exact ⟨⟨⟨p,mem_union_right K (hF hp)⟩,Or.inr hp,rfl⟩, fun hk => disjoint_left.mp hd hk (hF
        hp)⟩
  refine sum_bij' (fun s _ => rest s) (fun F _ => active K H F)
    (fun s _ => mem_powerset.mpr (hrest s)) (fun F _ => mem_filter.mpr ⟨mem_univ _,?_⟩)
    (fun s hs => hfull (mem_filter.mp hs).2) (fun F hF => hfix (mem_powerset.mp hF)) ?_
  · intro p hp _
    exact mem_subtype.mpr (mem_union_left _ hp)
  · intro s hs
    rw [hfull (mem_filter.mp hs).2]

private lemma support_good {n : Idl} (hn : AwayFromSix n) {p : Idl} (hp : p ∈ support n) :
    AwayFromSix p ∧ Prime p := by
  obtain ⟨hpp,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff
    hn.1).mp (Multiset.mem_toFinset.mp hp)
  exact ⟨⟨hpp.ne_zero,hn.2.of_isCoprime_of_dvd_left hd⟩,hpp⟩

private lemma support_mul {a b : Idl} (ha : a ≠ 0) (hb : b ≠ 0) : support (a*b) = support a ∪
    support b := by
  simp only [support,normalizedFactors_mul ha hb,Multiset.toFinset_add]

private lemma support_disjoint {a b : Idl} (ha : AwayFromSix a) (hc : IsCoprime a b) :
    Disjoint (support a) (support b) := by
  apply disjoint_left.mpr
  intro p hp hq
  exact (support_good ha hp).2.not_isUnit (hc.isRelPrime
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)) (dvd_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hq)))

private lemma primary_product {P : Finset Idl} (hP : ∀ p ∈ P, AwayFromSix p) :
    eisPrimary (∏ p ∈ P, generator p) := by
  induction P using Finset.induction_on with
  | empty => simp [eisPrimary]
  | @insert p P hp ih =>
    rw [prod_insert hp]
    exact (eisPrimary_generator (hP p (mem_insert_self ..)).coprime_three).mul
      (ih fun q hq => hP q (mem_insert_of_mem hq))

private lemma generator_product {P : Finset Idl} (hP : ∀ p ∈ P, AwayFromSix p) :
    (∏ p ∈ P, generator p) = generator (∏ p ∈ P, p) := by
  apply Eq.symm
  apply generator_eq_of_eisPrimary _ (primary_product hP)
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [prod_insert hp,prod_insert hp,← span_singleton_mul_span_singleton,span_generator,
      ih (fun q hq => hP q (mem_insert_of_mem hq))]

private lemma support_product {k : Idl} (hk : Starred k) : (∏ p ∈ support k, generator p) =
    generator k := by
  have hnd := (squarefree_iff_nodup_normalizedFactors hk.1.1).mp hk.2
  rw [generator_product fun p hp => (support_good hk.1 hp).1]
  apply congrArg generator
  rw [support,prod_eq_multiset_prod,Multiset.map_id',Multiset.toFinset_val,hnd.dedup]
  exact associated_iff_eq.mp (prod_normalizedFactors hk.1.1)

/-- A finite class records the unit in the chosen row generator, its quadratic
reciprocity class, and its primary generator modulo the fixed CRT modulus. -/
abbrev RowClass := 𝓔ˣ × QuadraticFamilyClass × RowResidue

instance : Finite RowClass := by
  let := Ring.HasFiniteQuotients.finiteQuotient (I := span {(72:𝓔)*eisLambda^7})
    (by simp [eisLambda_prime.ne_zero])
  let : Finite 𝓔ˣ := Finite.of_injective (fun u : 𝓔ˣ =>
    (⟨(u : 𝓔), (mem_elementRows (by norm_num : (0:ℝ) ≤ 1)).mpr
      ⟨u.ne_zero, by simp [elementNorm, span_singleton_eq_top.mpr u.isUnit]⟩⟩ : elementRows 1))
    (fun _ _ h => Units.ext (congrArg Subtype.val h))
  infer_instance

private def rowLift (r : RowResidue) : 𝓔 :=
  if h : ∃ k : Idl, AwayFromSix k ∧ red (72*eisLambda^7) (generator k) = r then generator h.choose
    else 1

private lemma rowLift_primary (r : RowResidue) : eisPrimary (rowLift r) := by
  unfold rowLift
  split
  next h => exact eisPrimary_generator h.choose_spec.1.coprime_three
  · simp [eisPrimary]

private lemma rowLift_congr {r : RowResidue} {k : Idl} (hk : AwayFromSix k)
    (h : red (72*eisLambda^7) (generator k) = r) : red (72*eisLambda^7) (rowLift r) = r := by
  have he : ∃ k : Idl, AwayFromSix k ∧ red (72*eisLambda^7) (generator k) = r := ⟨k,hk,h⟩
  rw [rowLift,dite_eq_left he]
  exact he.choose_spec.2

/-- The exceptional multiplier after fixing the class of the varying row and
the fixed active set. Only a fixed residue of the frequency enters. -/
def classWeight {h : RayResidue 7} (D : FixedCusp h) (r : RowResidue) (F : Finset Idl)
    (m : FrequencyResidue) : ℂ :=
  Moduli.fixedWeight D.c D.a (rowLift r * ∏ p ∈ F, generator p) (Quotient.out m)

theorem norm_classWeight_le {h : RayResidue 7} (D : FixedCusp h) (r : RowResidue) {F : Finset Idl}
    (hF : ∀ p ∈ F, AwayFromSix p) (m : FrequencyResidue) : ‖classWeight D r F m‖ ≤ 1 := by
  let a := D.a * (rowLift r * ∏ p ∈ F, generator p)
  have ha : eisPrimary a := D.primary.mul ((rowLift_primary r).mul (primary_product hF))
  let n := span {a}
  have hn : n ≠ ⊥ := by simpa [n] using ha.ne_zero
  let := Ring.HasFiniteQuotients.finiteQuotient hn
  let := Fintype.ofFinite (𝓔 ⧸ n)
  let χ := cubicChar hn ha.coprime_three
  have hc : ‖eisEmbedding (cubicSymbol D.c a)‖ ≤ 1 := by
    change ‖eisEmbedding (powerResidueSymbol 3 D.c n)‖ ≤ 1
    rw [← cubicChar_mk hn ha.coprime_three]
    change ‖χ (Ideal.Quotient.mk n D.c)‖ ≤ 1
    by_cases hu : IsUnit (Ideal.Quotient.mk n D.c)
    · rw [← hu.unit_spec]
      exact (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity _)).le
    · simp [χ.map_nonunit hu]
  have hnφ (d : 𝓔) (x : Residue d) : ‖phase d x‖ = 1 := by
    change ‖differentCharacter _‖ = 1
    simp [differentCharacter,Complex.norm_exp,Complex.mul_re]
  simpa only [classWeight, Moduli.fixedWeight, Moduli.fixedPhase, norm_mul,
    Complex.norm_conj,hnφ,mul_one] using hc

private lemma classWeight_mk (hR : DunnRadziwillReciprocity) {h : RayResidue 7} (D : FixedCusp h)
    {k : Idl} (hk : AwayFromSix k) {r : RowResidue} (he : red (72*eisLambda^7) (generator k) = r)
    {F : Finset Idl} (hF : ∀ p ∈ F, AwayFromSix p) (m : 𝓔) :
    Moduli.fixedWeight D.c D.a (generator k * ∏ p ∈ F, generator p) m =
      classWeight D r F (red (8*eisLambda^9) m) := by
  apply Moduli.fixedWeight_congr_uniform hR D.c_ne_zero D.dvd_modulus D.primary
    ((eisPrimary_generator hk.coprime_three).mul (primary_product hF)) ((rowLift_primary r).mul
      (primary_product hF))
  · simp only [map_mul,he,rowLift_congr hk he]
  · exact (Ideal.Quotient.mk_out _).symm

theorem idealFactor_eq_reflectedFactor {q : Idl} (hq : AwayFromSix q) (hp : Prime q) (j : ℕ) (m :
    𝓔) :
    idealFactor hq j m = reflectedFactor q j m := by
  classical
  let := ((Ideal.prime_iff_isPrime hp.ne_zero).mp hp).isMaximal hp.ne_zero
  let := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ q)
  rw [reflectedFactor, dite_eq_left (And.intro hq hp), factor_eq_idealFactor]

private lemma norm_fourier_le {φ : RayResidue 7 → ℂ} {B : ℝ} (hb : ∀ q, ‖φ q‖ ≤ B) (h : RayResidue
    7) :
    ‖rayFourierCoeff 7 φ h‖ ≤ B := by
  rw [rayFourierCoeff, norm_div, Complex.norm_natCast, div_le_iff₀ (by
    exact_mod_cast Fintype.card_pos)]
  calc
    _ ≤ ∑ y, ‖φ y * rayAddChar 7 (-(h*y))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : RayResidue 7, B := sum_le_sum fun y _ =>
      by simpa only [norm_mul,AddChar.norm_apply,mul_one] using hb y
    _ = _ := by simp [nsmul_eq_mul,mul_comm]

private lemma norm_idealInactive_le {P : Finset Idl} (e : Idl → ℕ) (s : Finset P) (hgood : ∀ p ∈ P,
    AwayFromSix p) :
    ‖idealInactive e s‖ ≤ 1 := by
  rw [idealInactive,norm_prod]
  apply prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro p _
  split_ifs
  · have hn : 1 ≤ (absNorm p.val : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (absNorm_eq_zero_iff.not.mpr (hgood p p.2).1)
    rw [← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hn))]
    exact sub_le_self _ (by positivity)
  · simp

private lemma contains_varying {K H : Finset Idl} {e : Idl → ℕ} (h₁ : ∀ p ∈ K, e p = 1)
    {s : Finset (K∪H : Finset Idl)} (h : idealInactive e s ≠ 0) :
    ∀ p ∈ K, ∀ hp : p ∈ K∪H, (⟨p,hp⟩ : (K∪H : Finset Idl)) ∈ s := by
  intro p hp hP
  by_contra hn
  exact h (prod_eq_zero (mem_compl.mpr hn) (by simp [h₁ p hp]))

private lemma active_prod {α M : Type*} [DecidableEq α] [CommMonoid M] {K H F : Finset α}
    (hF : F ⊆ H) (f : α → M) : (∏ q ∈ active K H F, f q) = ∏ q ∈ K∪F, f q := by
  apply prod_subtype_of_mem
  intro p hp
  exact (mem_union.mp hp).elim (mem_union_left _) (fun h => mem_union_right _ (hF h))

private lemma varying_prod {k t G : Idl} (hk : Starred k) (ht : t ≠ 0) (hkt : IsCoprime k t)
    (hkg : IsCoprime k G) (m : 𝓔) :
    (∏ p ∈ support k, reflectedFactor p (exponent (t*k) G p % 6) m) = quadraticResidue hk.1 m := by
  have he : primaryQuadraticSymbol 1 k = 1 := by
    change sextic k (generator 1)^3 = 1
    rw [← quadraticResidue_apply hk.1,generator_one,map_one]
  simpa only [generator_one,mul_one,one_pow,he,support,exponent] using
    (varying_column hk ht hkt hkg m 1 1).1

/-- A single inner series of (14). Its exceptional and fixed-prime weights are
shared by a row class. Its denominator norm is the varying row norm times a fixed factor. -/
def branchSum {h : RayResidue 7} (D : FixedCusp h) (r : RowResidue) (T G : Idl) (F : Finset Idl)
    {k : Idl} (hk : AwayFromSix k) (τ : ℂ → ℂ) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' m : Index, (classWeight D r F (red (8*eisLambda^9) m) *
    ∏ p ∈ F, reflectedFactor p (exponent T G p % 6) m) * quadraticResidue hk m *
    dualMode τ V X (D.c * (generator k * ∏ p ∈ F, generator p)) m

theorem branch_denominator_norm {h : RayResidue 7} (D : FixedCusp h) (k : Idl) (F : Finset Idl) :
    elementNorm (D.c * (generator k * ∏ p ∈ F, generator p)) =
      elementNorm D.c * (∏ p ∈ F, absNorm p) * absNorm k := by
  have hm (x y : 𝓔) : elementNorm (x*y) = elementNorm x * elementNorm y := by
    simp only [elementNorm,← span_singleton_mul_span_singleton,map_mul]
  have hprod : elementNorm (∏ p ∈ F, generator p) = ∏ p ∈ F, absNorm p := by
    induction F using Finset.induction_on with
    | empty => simp [elementNorm]
    | insert p f hp ih => rw [prod_insert hp,prod_insert hp,hm,ih]; simp
      [elementNorm,span_generator]
  rw [hm,hm,hprod]
  simp only [elementNorm,span_generator]
  ring

private lemma projected_row {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    (hχ : PattersonAutomorphyWith pattersonMultiplier θ) (hB : DLMFBesselMellin) (hΓ :
      DLMFGammaVertical)
    (hR : DunnRadziwillReciprocity) {k T G : Idl} (hk : Starred k) (hT : AwayFromSix T) (hG :
      AwayFromSix G)
    (hkt : IsCoprime k T) (hkg : IsCoprime k G) {r : RowResidue} (hr : red (72*eisLambda^7)
      (generator k) = r)
    {φ : RayResidue 7 → ℂ} (hφ : ∀ g : RayResidue 3 → ℂ, ∑ x, φ x * g (rayReduction x) = 0)
    {B : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ B) :
    ∃ C : RaySupport φ → Finset Idl → ℂ, (∀ h F, ‖C h F‖ ≤ B) ∧
      ∀ {J : TestInterval} {V : ℝ → ℂ} {X : ℝ}, UnitTest J 6 V → 0 < X →
        projectedPattersonSum τ φ (numeratorTameProduct (support k ∪ support (T*G)) (exponent (T*k)
          G)) V X =
        ∑ h : RaySupport φ, ∑ F ∈ (support (T*G)).powerset,
          C h F * branchSum (fixedCusp hφ h) r T G F hk.1 τ V X := by
  let K := support k
  let H := support (T*G)
  let P := K∪H
  let e := exponent (T*k) G
  have hH {p : Idl} (hp : p ∈ H) := support_good (hT.mul hG) hp
  have hP {p : Idl} (hp : p ∈ P) : AwayFromSix p ∧ Prime p :=
    (mem_union.mp hp).elim (support_good hk.1) hH
  have hd : Disjoint K H := support_disjoint hk.1 (hkt.mul_right hkg)
  have h₁ (p : Idl) (hp : p ∈ K) : e p = 1 :=
    varying_exponent hk.2 hT.1 hkt hkg (Multiset.mem_toFinset.mp hp)
  have hfix (p : Idl) (hp : p ∈ H) : e p = exponent T G p := by
    apply fixed_exponent hT.1 hk.1.1
    intro hpk
    have hmem := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hk.1.1).mpr ⟨(hH hp).2,hpk⟩
    exact disjoint_left.mp hd (Multiset.mem_toFinset.mpr hmem) hp
  obtain ⟨C,hC,heq⟩ := projected_tameProduct he ht hχ hB hΓ hR P e (fun _ hp => (hP hp).1)
    (fun _ hp => (hP hp).2) hφ
  let a (h : RaySupport φ) (s : Finset P) := idealInactive e s * C h s
  let w (h : RaySupport φ) (s : Finset P) := rayFourierCoeff 7 φ h * a h s
  refine ⟨fun h F => w h (active K H F), ?_, ?_⟩
  · intro h F
    simp only [w,a,norm_mul,hC,mul_one]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_idealInactive_le _ _ (fun _ hp =>
      (hP hp).1))).trans
      (norm_fourier_le hbound _)
  intro J V X hV hX
  rw [heq hV hX]
  refine sum_congr rfl fun h _ => ?_
  let D := fixedCusp hφ h
  let z (s : Finset P) (m : Index) :=
    (Moduli.fixedWeight D.c D.a (∏ q ∈ s, generator q) m *
      ∏ q ∈ s, idealFactor (hP q.2).1 (e q % 6) m) *
      dualMode τ V X (D.c * ∏ q ∈ s, generator q) m
  change rayFourierCoeff 7 φ h * (∑ s : Finset P, a h s * ∑' m, z s m) = _
  rw [mul_sum]
  change (∑ s : Finset P, rayFourierCoeff 7 φ h * (a h s * ∑' m, z s m)) = _
  rw [regroup hd _ (fun s hs => contains_varying h₁ (fun hz => hs (by simp [a,hz])))]
  refine sum_congr rfl fun F hF => ?_
  have hsub := mem_powerset.mp hF
  have hdis := hd.mono_right hsub
  let s := active K H F
  have hg : (∏ q ∈ s, generator (q : Idl)) = generator k * ∏ p ∈ F, generator p := by
    rw [active_prod hsub generator,prod_union hdis,support_product hk]
  have htables (m : 𝓔) :
      (∏ q ∈ s, idealFactor (hP q.2).1 (e q % 6) m) =
        quadraticResidue hk.1 m * ∏ p ∈ F, reflectedFactor p (exponent T G p % 6) m := by
    calc
      _ = ∏ q ∈ s, reflectedFactor q (e q % 6) m := prod_congr rfl
        (fun q _ => idealFactor_eq_reflectedFactor (hP q.2).1 (hP q.2).2 _ _)
      _ = _ := by
        rw [active_prod hsub (fun p => reflectedFactor p (e p % 6) m),prod_union hdis,
          varying_prod hk hT.1 hkt hkg]
        apply congrArg (quadraticResidue hk.1 m * ·)
        exact prod_congr rfl (fun p hp => by rw [hfix p (hsub hp)])
  rw [← mul_assoc]
  apply congrArg (w h s * ·)
  apply tsum_congr
  intro m
  dsimp only [z,branchSum]
  rw [hg, htables, classWeight_mk hR D hk.1 hr (fun p hp => (hH (hsub hp)).1)]
  ring

private lemma support_dvd {a b : Idl} (hb : b ≠ 0) (hab : a ∣ b) : support a ⊆ support b :=
  Multiset.toFinset_subset.mpr (Multiset.subset_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_zero_of_dvd_ne_zero hb hab) hb).mp hab))

/-- All fixed primes lie among the primes of the original fixed row or the
fourth-power numerator. -/
theorem fixedSupport_subset {t y T G : Idl} (ht : t ≠ 0) (hy : y ≠ 0) (hT : T ∣ t) (hG : G ∣ y) :
    support (T*G) ⊆ support t ∪ support y := by
  rw [support_mul (ne_zero_of_dvd_ne_zero ht hT) (ne_zero_of_dvd_ne_zero hy hG)]
  exact union_subset_union (support_dvd ht hT) (support_dvd hy hG)

/-- A simple prime of the numerator away from the original fixed row has the
exceptional local exponent four whenever it belongs to the fixed support. -/
theorem simple_exponent {t y T G p : Idl} (ht : t ≠ 0) (hy : y ≠ 0) (hT : T ∣ t) (hG : G ∣ y)
    (hp : p ∈ support (T*G)) (hpt : p ∉ support t) (hpy : (normalizedFactors y).count p = 1) :
    exponent T G p = 4 := by
  have hnG := ne_zero_of_dvd_ne_zero hy hG
  rw [support_mul (ne_zero_of_dvd_ne_zero ht hT) hnG] at hp
  have h0 : p ∉ support T := fun h => hpt (support_dvd ht hT h)
  have hpG := (mem_union.mp hp).resolve_left h0
  have hz : (normalizedFactors T).count p = 0 := Multiset.count_eq_zero.mpr (fun h =>
    h0 (Multiset.mem_toFinset.mpr h))
  have hp₁ := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hpG)
  have hp₂ := Multiset.count_le_of_le p ((dvd_iff_normalizedFactors_le_normalizedFactors hnG
    hy).mp hG)
  dsimp [exponent]
  omega


/-- Equation (14) on each row class. The choice of projector, cusp and fixed
frequency weight is shared by the whole class. Every scalar which can vary
with the row lies outside its frequency sum. -/
theorem completed_row_inversion {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    (hχ : PattersonAutomorphyWith pattersonMultiplier θ) (hB : DLMFBesselMellin) (hΓ :
      DLMFGammaVertical)
    (hR : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    (ξ : RayCharacter) (u₀ : 𝓔ˣ) {t : Idl} (ht₀ : t ≠ 0) {y : 𝓔} (hy : y ≠ 0) :
    ∃ (T G : Idl) (classOf : Idl → RowClass), AwayFromSix T ∧ AwayFromSix G ∧ T ∣ t ∧ G ∣ span {y} ∧
      (∀ k, (classOf k).2 = (familyClass k,red (72*eisLambda^7) (generator k))) ∧
      ∀ c : RowClass, ∃ (φ : RayResidue 7 → ℂ)
        (hφ : ∀ g : RayResidue 3 → ℂ, ∑ z, φ z * g (rayReduction z) = 0),
        ∀ {k : Idl} (hk : Starred k), IsCoprime k t → IsCoprime k (span {y}) → classOf k = c →
          ∃ C : RaySupport φ → Finset Idl → ℂ, (∀ h F, ‖C h F‖ ≤ 1 + Fintype.card (RayResidue 7)) ∧
          ∀ {J : TestInterval} {V : ℝ → ℂ} {X : ℝ}, UnitTest J 6 V → 0 < X →
            ReflectionRows.completedAtElement ξ V X (u₀ * generator (t*k)) y =
              ∑ h : RaySupport φ, ∑ F ∈ (support (T*G)).powerset,
                C h F * branchSum (fixedCusp hφ h) c.2.2 T G F hk.1 τ V X := by
  obtain ⟨T,G,i,j,hT,hG,hTt,hGy,hw⟩ := factor_squarefree_row hR quad ξ u₀ ht₀ hy
  let unit (k : Idl) : 𝓔ˣ := if hk : AwayFromSix k then (hw k hk).choose else 1
  let classOf (k : Idl) : RowClass := (unit k, familyClass k, red (72*eisLambda^7) (generator k))
  refine ⟨T,G,classOf,hT,hG,hTt,hGy,fun _ => rfl,?_⟩
  intro c
  let ψ := ReflectionTwist.fixedFactor ξ c.1 i j (familyClass T * c.2.1)
  obtain ⟨φ,hφ,hbound,hproject⟩ := exists_tameProduct_projection hR ψ
  refine ⟨φ,hφ,?_⟩
  intro k hk hkt hky hc
  have hku : (hw k hk.1).choose = c.1 := by
    simpa only [classOf,unit,dite_eq_left hk.1] using congrArg Prod.fst hc
  have hkc : familyClass k = c.2.1 := congrArg (fun v : RowClass => v.2.1) hc
  have hkr : red (72*eisLambda^7) (generator k) = c.2.2 := congrArg (fun v : RowClass => v.2.2) hc
  let P := support k ∪ support (T*G)
  let e := exponent (T*k) G
  have hP (p : Idl) (hp : p ∈ P) : AwayFromSix p := (mem_union.mp hp).elim
    (fun h => (support_good hk.1 h).1) (fun h => (support_good (hT.mul hG) h).1)
  have hPS : support ((T*k)*G) = P := by
    dsimp only [P]
    rw [support_mul (mul_ne_zero hT.1 hk.1.1) hG.1,support_mul hT.1 hk.1.1,support_mul hT.1 hG.1]
    ac_rfl
  have htwist (n : Idl) (hn : AwayFromSix n) :
      twist ξ ((u₀ * generator (t*k))*y^4) 1 n =
        ψ (Ideal.Quotient.mk _ (generator n)) * numeratorTameProduct P e (generator n) := by
    have h := (hw k hk.1).choose_spec n hn
    rw [hku,hkc] at h
    change _ = ψ _ * ∏ p ∈ support ((T*k)*G), ReflectionTwist.localFactor p (e p) (generator n) at h
    rw [hPS] at h
    simpa only [twist,ite_eq_left hn,generator_one,one_pow,mul_one,numeratorTameProduct] using h
  obtain ⟨C,hC,heq⟩ := projected_row he ht hχ hB hΓ hR hk hT hG
    (hkt.of_isCoprime_of_dvd_right hTt) (hky.of_isCoprime_of_dvd_right hGy) hkr hφ
    (hbound (ReflectionTwist.norm_fixedFactor_le ξ c.1 i j _))
  let rowScalar := (numeratorTameProduct P e (eisLambda^3))⁻¹
  have hScalar : ‖rowScalar‖ = 1 :=
    by rw [norm_inv,norm_numeratorTameProduct_lambda_cube P e hP,inv_one]
  refine ⟨fun h F => rowScalar*C h F,fun h F =>
    by simpa only [norm_mul,hScalar,one_mul] using hC h F,?_⟩
  intro J V X hV hX
  rw [ReflectionRows.completedAtElement,hproject ht P e hP hV hX _ _ _ htwist,heq hV hX,mul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun F _ => ?_
  change rowScalar * (_ * _) = (rowScalar * _) * _
  ring

end Masullo.QRH.MeanSquare.ReflectionRowInversion
