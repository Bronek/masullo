import Masullo.QRH.MeanSquare.ReflectionTwist
import Masullo.QRH.MeanSquare.ReflectionTame
import Masullo.QRH.MeanSquare.ReflectionIndex
import Masullo.QRH.MeanSquare.ReflectionSieve

/-! # The varying squarefree row in the reflected twist -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare.ReflectionVaryingRows

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private lemma coprime_of_rel {a b : Ideal 𝓔} (h : IsRelPrime a b) : IsCoprime a b :=
  isCoprime_iff_sup_eq.mpr (Ideal.isUnit_iff.mp (h (dvd_iff_le.mpr le_sup_left) (dvd_iff_le.mpr
    le_sup_right)))

/-- The part of a squarefree row supported on an ideal is its gcd with that
ideal. The remaining factor is squarefree and coprime to the supporting ideal. -/
theorem split_squarefree {s : Ideal 𝓔} (hs : Squarefree s) (c : Ideal 𝓔) :
    ∃ k : Ideal 𝓔, s = gcd s c * k ∧ Squarefree k ∧ IsCoprime k c := by
  obtain ⟨k,hk⟩ := gcd_dvd_left s c
  have hsf : Squarefree (gcd s c * k) := hk ▸ hs
  refine ⟨k,hk,hsf.of_mul_right,coprime_of_rel ?_⟩
  intro p hpk hpc
  have hps : p ∣ s := hpk.trans (hk ▸ dvd_mul_left ..)
  exact IsRelPrime.of_squarefree_mul hsf (dvd_gcd hps hpc) hpk

/-- Splitting at the primes of six and of the fourth-power twist produces a
good squarefree varying row. -/
theorem exists_varying_row {s : Ideal 𝓔} (hs : Squarefree s) (g : Ideal 𝓔) :
    ∃ t k : Ideal 𝓔, s = t*k ∧ t ∣ span {(6 : 𝓔)}*g ∧ Starred k ∧
      IsCoprime k t ∧ IsCoprime k g := by
  obtain ⟨k,he,hk,hc⟩ := split_squarefree hs (span {(6:𝓔)}*g)
  have ht := gcd_dvd_right s (span {(6:𝓔)}*g)
  exact ⟨_,k,he,ht,⟨⟨hk.ne_zero,hc.of_isCoprime_of_dvd_right (dvd_mul_right ..)⟩,hk⟩,
    hc.of_isCoprime_of_dvd_right ht,hc.of_isCoprime_of_dvd_right (dvd_mul_left ..)⟩

/-- The actual exponent of every prime of the varying row is one before reduction
modulo six. -/
theorem varying_exponent {k t g p : Ideal 𝓔} (hk : Squarefree k) (ht : t ≠ 0)
    (hkt : IsCoprime k t) (hkg : IsCoprime k g) (hp : p ∈ normalizedFactors k) :
    (normalizedFactors (t*k)).count p + 4*(normalizedFactors g).count p = 1 := by
  classical
  obtain ⟨hpp,hpk⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hk.ne_zero).mp hp
  have h0 {a : Ideal 𝓔} (ha : IsCoprime k a) : (normalizedFactors a).count p = 0 :=
    Multiset.count_eq_zero.mpr (fun h => hpp.not_isUnit (ha.isRelPrime hpk
      (dvd_of_mem_normalizedFactors h)))
  have hle := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors
    hk.ne_zero).mp hk) p
  have hpos := Multiset.count_pos.mpr hp
  rw [normalizedFactors_mul ht hk.ne_zero,Multiset.count_add,h0 hkt,h0 hkg]
  omega

/-- The reflected local multiplier of (13), evaluated on an Eisenstein integer. -/
def reflectedFactor (p : Ideal 𝓔) (j : ℕ) (m : 𝓔) : ℂ := by
  classical
  exact if h : AwayFromSix p ∧ Prime p then
    let := ((Ideal.prime_iff_isPrime h.2.ne_zero).mp h.2).isMaximal h.2.ne_zero
    let := Ideal.Quotient.field p
    let := Ring.HasFiniteQuotients.finiteQuotient h.2.ne_zero
    let := Fintype.ofFinite (𝓔 ⧸ p)
    ReflectionTame.factor (sexticChar h.1) j (Ideal.Quotient.mk p m)
  else 0

/-- The input Fourier coefficient at a local frequency. -/
def inputCoefficient (p : Ideal 𝓔) (j : ℕ) (h : 𝓔 ⧸ p) : ℂ := by
  classical
  exact if hp : AwayFromSix p ∧ Prime p then
    let := ((Ideal.prime_iff_isPrime hp.2.ne_zero).mp hp.2).isMaximal hp.2.ne_zero
    let := Ideal.Quotient.field p
    let := Ring.HasFiniteQuotients.finiteQuotient hp.2.ne_zero
    let := Fintype.ofFinite (𝓔 ⧸ p)
    ReflectionTame.coefficient ((sexticChar hp.1)^j) (quotientDifferentCharacter p) h
  else 0

private lemma factor_one {p : Ideal 𝓔} (hp : AwayFromSix p) (hpp : Prime p) (m : 𝓔) :
    reflectedFactor p 1 m = quadraticResidue hp m := by
  classical
  let := ((Ideal.prime_iff_isPrime hpp.ne_zero).mp hpp).isMaximal hpp.ne_zero
  let := Ideal.Quotient.field p
  let := Ring.HasFiniteQuotients.finiteQuotient hpp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ p)
  rw [reflectedFactor, dite_eq_left (And.intro hp hpp), ReflectionTame.factor_one
    (orderOf_sexticChar_prime hp hpp) (ringChar_quotient_ne_two hpp hp)]
  rw [quadraticResidue_apply,← sexticChar_apply_mk hp,← MulChar.pow_apply' _ (by decide : 3 ≠ 0),
    cubic_power_eq_quadraticChar (orderOf_sexticChar_prime hp hpp) (ringChar_quotient_ne_two hpp
      hp)]
  rfl

private lemma coefficient_one_zero {p : Ideal 𝓔} (hp : AwayFromSix p) (hpp : Prime p) :
    inputCoefficient p 1 0 = 0 := by
  classical
  let := ((Ideal.prime_iff_isPrime hpp.ne_zero).mp hpp).isMaximal hpp.ne_zero
  let := Ideal.Quotient.field p
  let := Ring.HasFiniteQuotients.finiteQuotient hpp.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ p)
  rw [inputCoefficient, dite_eq_left (And.intro hp hpp), ReflectionTame.coefficient_zero_pow
    (orderOf_sexticChar_prime hp hpp) _ (by decide)]
  norm_num

private lemma good_dvd {a b : Ideal 𝓔} (hb : AwayFromSix b) (hd : a ∣ b) : AwayFromSix a :=
  ⟨ne_zero_of_dvd_ne_zero hb.1 hd,hb.2.of_isCoprime_of_dvd_left hd⟩

/-- In every nonvanishing Fourier term all primes in the varying row are active. -/
theorem varying_active {k t g : Ideal 𝓔} (hk : Starred k) (ht : t ≠ 0)
    (hkt : IsCoprime k t) (hkg : IsCoprime k g) (P : Finset (Ideal 𝓔))
    (hP : (normalizedFactors k).toFinset ⊆ P) (h : (p : Ideal 𝓔) → 𝓔 ⧸ p)
    (hne : ∏ p ∈ P, inputCoefficient p
      (((normalizedFactors (t*k)).count p + 4*(normalizedFactors g).count p)%6) (h p) ≠ 0) :
    ∀ p ∈ normalizedFactors k, h p ≠ 0 := by
  classical
  intro p hp hz
  obtain ⟨hpp, hpk⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hk.1.1).mp hp
  have e := (prod_ne_zero_iff.mp hne) p (hP (Multiset.mem_toFinset.mpr hp))
  rw [varying_exponent hk.2 ht hkt hkg hp,hz] at e
  exact e (coefficient_one_zero (good_dvd hk.1 hpk) hpp)

private lemma quadratic_product {k : Ideal 𝓔} (hk : Starred k) (m : 𝓔) :
    ∏ p ∈ (normalizedFactors k).toFinset, reflectedFactor p 1 m = quadraticResidue hk.1 m := by
  classical
  let F : Ideal 𝓔 →* ℂ := ⟨⟨fun p => sextic p m ^ 3,
    by simp [sextic, Ideal.one_eq_top, powerResidueSymbol_top]⟩,
    fun a b => by simp only [sextic,powerResidueSymbol_mul_right,map_mul,mul_pow]⟩
  have he : (normalizedFactors k).prod = k := associated_iff_eq.mp (prod_normalizedFactors hk.1.1)
  have hnd := (squarefree_iff_nodup_normalizedFactors hk.1.1).mp hk.2
  calc
    _ = ∏ p ∈ (normalizedFactors k).toFinset, F p := by
      refine prod_congr rfl fun p hp => ?_
      obtain ⟨hpp,hpk⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff
        hk.1.1).mp (Multiset.mem_toFinset.mp hp)
      exact (factor_one (good_dvd hk.1 hpk) hpp m).trans (quadraticResidue_apply _ _)
    _ = F (normalizedFactors k).prod := by
      rw [prod_eq_multiset_prod,Multiset.toFinset_val,hnd.dedup,map_multiset_prod]
    _ = _ := by rw [he,quadraticResidue_apply]; rfl

private lemma quadratic_cube {k : Ideal 𝓔} (hk : AwayFromSix k) (b : 𝓔) :
    quadraticResidue hk (b^3) = quadraticResidue hk b := by
  rw [map_pow]
  by_cases h : IsCoprime k (span {b})
  · rw [pow_succ,quadraticResidue_sq hk h,one_mul]
  · have hz : quadraticResidue hk b = 0 := by_contra fun h' => h ((quadraticResidue_ne_zero
      hk).mp h')
    simp [hz]

/-- The product of (13) over all varying primes leaves the squarefree sieve
column. The bounded row multiplier may vanish when the cube part meets the row. -/
theorem varying_column {k t g : Ideal 𝓔} (hk : Starred k) (ht : t ≠ 0)
    (hkt : IsCoprime k t) (hkg : IsCoprime k g) (d b : 𝓔) (n : Ideal 𝓔) :
    (∏ p ∈ (normalizedFactors k).toFinset, reflectedFactor p
      (((normalizedFactors (t*k)).count p + 4*(normalizedFactors g).count p)%6)
      (d*generator n*b^3)) = quadraticResidue hk.1 (d*b) * primaryQuadraticSymbol n k ∧
      ‖quadraticResidue hk.1 (d*b)‖ ≤ 1 := by
  have hs := ReflectionSieve.split_column_symbol hk.1 n d b
  refine ⟨?_,hs.2⟩
  calc
    _ = ∏ p ∈ (normalizedFactors k).toFinset, reflectedFactor p 1 (d*generator n*b^3) := by
      apply prod_congr rfl
      intro p hp
      rw [varying_exponent hk.2 ht hkt hkg (Multiset.mem_toFinset.mp hp)]
    _ = _ := by
      rw [quadratic_product hk, map_mul, quadratic_cube,← map_mul]
      exact hs.1

/-- Split off the only possible inert prime at two from a squarefree column
prime to three. Its primary generator is `-2`. -/
theorem split_column_two {n : Ideal 𝓔} (hn : Squarefree n) (h₃ : IsCoprime n (span {3})) :
    ∃ (e : Fin 2) (n' : Ideal 𝓔), Starred n' ∧ n = (span {(-2 : 𝓔)})^(e : ℕ)*n' ∧
      generator n = (-2 : 𝓔)^(e : ℕ)*generator n' := by
  let P := span {(-2 : 𝓔)}
  have hp : Prime P := prime_span_singleton_iff.mpr ReflectionTwist.neg_two_prime
  have h₆ {a : Ideal 𝓔} (ha : IsCoprime a P) (hb : IsCoprime a (span {3})) : IsCoprime a (span {6})
    := by
    have h := ha.mul_right hb
    simpa only [P,span_singleton_neg,span_singleton_mul_span_singleton,show (2:𝓔)*3 =
      6 by norm_num] using h
  by_cases hd : P ∣ n
  · obtain ⟨m,he⟩ := hd
    have hs : Squarefree (P*m) := he ▸ hn
    have hm := hs.of_mul_right
    have hc := h₃.of_isCoprime_of_dvd_left (he ▸ dvd_mul_left m P)
    have hP := h₃.of_isCoprime_of_dvd_left (he ▸ dvd_mul_right P m)
    have hgen : generator P = -2 := generator_eq_of_eisPrimary rfl ⟨-1,by ring⟩
    refine ⟨1,m,⟨⟨hm.ne_zero,h₆ ((coprime_of_rel (IsRelPrime.of_squarefree_mul hs)).symm)
      hc⟩,hm⟩,?_,?_⟩
    · simpa [P] using he
    · simp [he,generator_mul hP hc,hgen]
  · have hc := coprime_of_rel (hp.irreducible.isRelPrime_iff_not_dvd.mpr hd).symm
    exact ⟨0,n,⟨⟨hn.ne_zero,h₆ hc h₃⟩,hn⟩,by simp,by simp⟩

/-- The primary column and its possible inert prime give an explicit factor at
the reflected Patterson frequency, including the zero when a cube ideal meets the row. -/
theorem varying_reflected_index {k t g : Ideal 𝓔} (hk : Starred k) (ht : t ≠ 0)
    (hkt : IsCoprime k t) (hkg : IsCoprime k g) (x : ReflectedIndex) :
    ∃ (e : Fin 2) (n : Ideal 𝓔), Starred n ∧ x.n = (span {(-2:𝓔)})^(e : ℕ)*n ∧
      (let d : 𝓔 := eisLambda^x.exponent * x.unit * (-2)^(e : ℕ)
       (∏ p ∈ (normalizedFactors k).toFinset, reflectedFactor p
         (((normalizedFactors (t*k)).count p + 4*(normalizedFactors g).count p)%6) x.numerator) =
           quadraticResidue hk.1 (d*generator x.b) * primaryQuadraticSymbol n k ∧
       ‖quadraticResidue hk.1 (d*generator x.b)‖ ≤ 1) := by
  obtain ⟨e,n,hn,he,hgen⟩ := split_column_two x.squarefree_n x.coprime_n
  refine ⟨e,n,hn,he,?_⟩
  let d : 𝓔 := eisLambda^x.exponent * x.unit * (-2)^(e : ℕ)
  have hm : x.numerator = d * generator n * generator x.b ^ 3 := by
    rw [ReflectedIndex.numerator,hgen]
    dsimp only [d]
    ring
  dsimp only
  rw [hm]
  exact varying_column hk ht hkt hkg d (generator x.b) n

/-- The fixed input phase is independent of the varying row upon fixing its
class modulo four. -/
theorem fixedFactor_eq_on_class (ξ : RayCharacter) (u : 𝓔ˣ) (i j : Fin 6) {t k k' : Ideal 𝓔}
    (ht : AwayFromSix t) (hk : AwayFromSix k) (hk' : AwayFromSix k')
    (he : familyClass k = familyClass k') :
    ReflectionTwist.fixedFactor ξ u i j (familyClass (t*k)) =
      ReflectionTwist.fixedFactor ξ u i j (familyClass (t*k')) := by
  rw [familyClass_mul ht hk,familyClass_mul ht hk',he]

private lemma good_part_dvd {x d : 𝓔} {a : Ideal 𝓔} (he : x = d*generator a) : a ∣ span {x} := by
  rw [he,← span_singleton_mul_span_singleton,span_generator]
  exact dvd_mul_left ..

/-- For a fixed part `t` and fourth-power numerator `y`, the tame ideals and
both ramified exponents are fixed. An additional unit accounts for the chosen
generator when `t` contains λ. Thus fixing that unit and the mod-four class of
the varying row fixes the ray function. -/
theorem factor_squarefree_row (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    (ξ : RayCharacter) (u₀ : 𝓔ˣ) {t : Ideal 𝓔} (ht : t ≠ 0) {y : 𝓔} (hy : y ≠ 0) :
    ∃ (T G : Ideal 𝓔) (i j : Fin 6), AwayFromSix T ∧ AwayFromSix G ∧ T ∣ t ∧ G ∣ span {y} ∧
      ∀ k : Ideal 𝓔, AwayFromSix k → ∃ u : 𝓔ˣ, ∀ n : Ideal 𝓔, AwayFromSix n →
        ξ (Ideal.Quotient.mk _ (generator n)) * sextic n ((u₀ * generator (t*k)) * y^4) =
          ReflectionTwist.fixedFactor ξ u i j (familyClass T * familyClass k) (Ideal.Quotient.mk _
            (generator n)) *
            ∏ p ∈ (normalizedFactors ((T*k)*G)).toFinset,
              ReflectionTwist.localFactor p ((normalizedFactors (T*k)).count p +
                4*(normalizedFactors G).count p) (generator n) := by
  have htz : generator t ≠ 0 := fun hz => ht (by simpa [hz] using (span_generator t).symm)
  obtain ⟨v,i,j,T,hT,htg⟩ := ReflectionTwist.exists_good_part htz
  obtain ⟨w,a,b,G,hG,hyg⟩ := ReflectionTwist.exists_good_part hy
  have hTt := good_part_dvd htg
  rw [span_generator] at hTt
  refine ⟨T,G,Fin.ofNat 6 (i+4*a),Fin.ofNat 6 (j+4*b),hT,hG,hTt,good_part_dvd hyg,?_⟩
  intro k hk
  have hspan : span {generator t * generator k} = span {generator (t*k)} := by
    rw [← span_singleton_mul_span_singleton,span_generator,span_generator,span_generator]
  obtain ⟨z,hz⟩ := span_singleton_eq_span_singleton.mp hspan
  have hx : (u₀ : 𝓔)*generator (t*k) =
      ((u₀*z*v : 𝓔ˣ) : 𝓔)*(-2)^i*eisLambda^j*generator (T*k) := by
    rw [← hz, htg, generator_mul hT.coprime_three hk.coprime_three]
    simp only [Units.val_mul]
    ring
  refine ⟨u₀*z*v*w^4, fun n hn => ?_⟩
  simpa only [familyClass_mul hT hk] using ReflectionTwist.factor_twist_of_parts
    recip quad ξ (hT.mul hk) hG hn hx hyg

/-- The local exponents outside the varying row do not depend on that row. -/
theorem fixed_exponent {k t g p : Ideal 𝓔} (ht : t ≠ 0) (hk : k ≠ 0) (hp : ¬ p ∣ k) :
    (normalizedFactors (t*k)).count p + 4*(normalizedFactors g).count p =
      (normalizedFactors t).count p + 4*(normalizedFactors g).count p := by
  classical
  have hz : (normalizedFactors k).count p = 0 := Multiset.count_eq_zero.mpr
    (fun h => hp (dvd_of_mem_normalizedFactors h))
  rw [normalizedFactors_mul ht hk,Multiset.count_add,hz,add_zero]

/-- In particular, a prime entering the fourth-power twist exactly once outside
the fixed row has exponent four. -/
theorem fixed_exponent_four {k t g p : Ideal 𝓔} (ht : t ≠ 0) (hk : k ≠ 0) (hc : IsCoprime k g)
    (hp : ¬ p ∣ t) (hv : (normalizedFactors g).count p = 1) :
    ((normalizedFactors (t*k)).count p + 4*(normalizedFactors g).count p)%6 = 4 := by
  classical
  have hm : p ∈ normalizedFactors g := Multiset.count_pos.mp (by omega)
  have hpg := dvd_of_mem_normalizedFactors hm
  have hpp := prime_of_normalized_factor _ hm
  have hpk : ¬ p ∣ k := fun h => hpp.not_isUnit (hc.isRelPrime h hpg)
  have hz : (normalizedFactors t).count p = 0 := Multiset.count_eq_zero.mpr
    (fun h => hp (dvd_of_mem_normalizedFactors h))
  rw [fixed_exponent ht hk hpk,hz,hv]

/-- Split the full active product at the varying row. The exponents in the
complement are fixed by `t,g`; only the quadratic sieve symbol of the good
squarefree column remains from the varying primes. -/
theorem separate_active_product {k t g : Ideal 𝓔} (hk : Starred k) (ht : t ≠ 0)
    (hkt : IsCoprime k t) (hkg : IsCoprime k g) (P : Finset (Ideal 𝓔))
    (hP : (normalizedFactors k).toFinset ⊆ P) (x : ReflectedIndex) :
    ∃ (e : Fin 2) (n : Ideal 𝓔), Starred n ∧ x.n = (span {(-2:𝓔)})^(e : ℕ)*n ∧
      (let d : 𝓔 := eisLambda^x.exponent * x.unit * (-2)^(e : ℕ)
       (∏ p ∈ P, reflectedFactor p
         (((normalizedFactors (t*k)).count p + 4*(normalizedFactors g).count p)%6) x.numerator) =
         (∏ p ∈ P \ (normalizedFactors k).toFinset, reflectedFactor p
           (((normalizedFactors t).count p + 4*(normalizedFactors g).count p)%6) x.numerator) *
           (quadraticResidue hk.1 (d*generator x.b) * primaryQuadraticSymbol n k) ∧
       ‖quadraticResidue hk.1 (d*generator x.b)‖ ≤ 1) := by
  classical
  obtain ⟨e,n,hn,he,hkprod,hnorm⟩ := varying_reflected_index hk ht hkt hkg x
  refine ⟨e,n,hn,he,?_,hnorm⟩
  rw [← hkprod,← prod_sdiff hP]
  apply congrArg (· * _)
  refine prod_congr rfl fun p hp => ?_
  have hz := Multiset.count_eq_zero.mpr (fun h => (mem_sdiff.mp hp).2 (Multiset.mem_toFinset.mpr h))
  rw [normalizedFactors_mul ht hk.1.1,Multiset.count_add,hz,add_zero]

end Masullo.QRH.MeanSquare.ReflectionVaryingRows
