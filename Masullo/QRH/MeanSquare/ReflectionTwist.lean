import Masullo.QRH.MeanSquare.FamilyReciprocity
import Masullo.QRH.MeanSquare.FamilySymbol
import Masullo.QRH.MeanSquare.ReflectionCoefficients
import Masullo.QRH.MeanSquare.ThetaSupport
import Masullo.QRH.MeanSquare.UnitRows
import Mathlib.NumberTheory.MulChar.Duality

/-! # Tame factors of the primary sextic twist -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare.ReflectionTwist

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
local notation "R₄" => 𝓔 ⧸ span {(4 : 𝓔)}
local notation "R₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

private theorem sextic_mul {n : Ideal 𝓔} (hn : AwayFromSix n) (x y : 𝓔) :
    sextic n (x*y) = sextic n x * sextic n y := by
  simp only [sextic, powerResidueSymbol_six_mul hn.2, map_mul]

private theorem sextic_pow {n : Ideal 𝓔} (hn : AwayFromSix n) (x : 𝓔) (e : ℕ) :
    sextic n (x ^ e) = sextic n x ^ e := by
  rw [← sexticChar_apply_mk hn, map_pow, map_pow, sexticChar_apply_mk]

private theorem sextic_den_mul {a b : Ideal 𝓔} (x : 𝓔) :
    sextic (a*b) x = sextic a x * sextic b x := by
  simp only [sextic, powerResidueSymbol_mul_right, map_mul]

private theorem sextic_zero {a b : Ideal 𝓔} (ha : AwayFromSix a) (h : ¬ IsCoprime a b) :
    sextic a (generator b) = 0 := by
  rw [← sexticChar_apply_mk ha]
  exact MulChar.map_nonunit _ (fun hu => h (by
    simpa only [span_generator] using (isUnit_mk_iff_coprime_span _ _).mp hu))

/-- Cubic reciprocity determines the square of each sextic value. Quadratic
reciprocity then gives the mod-four sign, also when a common factor forces zero. -/
theorem sextic_squarefree_reciprocity (recip : DunnRadziwillReciprocity)
    (quad : DeloupTuraevTheorem1)
    {a n : Ideal 𝓔} (ha : Starred a) (hn : Starred n) :
    sextic n (generator a) =
      sextic a (generator n) * familySign (familyClass n) (familyClass a) := by
  by_cases hc : IsCoprime n a
  · let x := sextic n (generator a)
    let y := sextic a (generator n)
    have hs : x ^ 2 = y ^ 2 := sextic_sq_reciprocity recip hn.1 ha.1
    have ht : x ^ 3 = y ^ 3 * familySign (familyClass n) (familyClass a) :=
      primaryQuadraticSymbol_reciprocity quad hn ha hc
    have hy : y ≠ 0 := by
      have hu := norm_sextic_of_coprime ha.1 (a :=
        generator n) (by rwa [span_generator, isCoprime_comm])
      exact norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
    change x = y * _
    apply mul_right_cancel₀ (pow_ne_zero 2 hy)
    calc
      _ = x ^ 3 := by rw [← hs]; ring
      _ = _ := ht
      _ = _ := by ring
  · simp [sextic_zero hn.1 hc, sextic_zero ha.1 (fun h => hc h.symm)]

private theorem away_of_dvd {d n : Ideal 𝓔} (hn : AwayFromSix n) (hd : d ∣ n) : AwayFromSix d :=
  ⟨fun h => hn.1 (zero_dvd_iff.mp (show (0 : Ideal 𝓔) ∣ n by rwa [h] at hd)),
    hn.2.of_isCoprime_of_dvd_left hd⟩

/-- For a squarefree good numerator, only the squarefree part of the denominator
enters the sign. The square factor of the denominator obeys cubic reciprocity. -/
theorem sextic_reciprocity_sq_mul (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    {a v s : Ideal 𝓔} (ha : Starred a) (hv : AwayFromSix v) (hs : Starred s) :
    sextic (v ^ 2 * s) (generator a) =
      sextic a (generator (v ^ 2 * s)) * familySign (familyClass s) (familyClass a) := by
  have hv₂ := hv.mul hv
  simp only [pow_two, sextic_den_mul,
    generator_mul hv.coprime_three hv.coprime_three,
      generator_mul hv₂.coprime_three hs.1.coprime_three,
    sextic_mul ha.1]
  rw [← sq, sextic_sq_reciprocity recip hv ha.1, sextic_squarefree_reciprocity recip quad ha hs]
  ring

/-- The local factor at a positive numerator valuation. The bundled character
power at exponent zero retains the zero on nonunits after reduction modulo six. -/
def tame (p : Ideal 𝓔) (hp : AwayFromSix p) (e : ℕ) (x : 𝓔) : ℂ :=
  (sexticChar hp ^ (e % 6)) (Ideal.Quotient.mk p x)

theorem tame_eq_pow {p : Ideal 𝓔} (hp : AwayFromSix p) (hp' : Prime p) {e : ℕ}
    (he : e ≠ 0) (x : 𝓔) :
    tame p hp e x = sextic p x ^ e := by
  have hmod := pow_mod_orderOf (sexticChar hp) e
  rw [orderOf_sexticChar_prime hp hp'] at hmod
  rw [tame, hmod, MulChar.pow_apply' _ he, sexticChar_apply_mk]

open DeloupTuraev Matrix

private def gridPoint : Fin 4 → Fin 2 → ℤ :=
  ![![0,0], ![1,0], ![-1,1], ![0,-1]]

private def lift (v : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => v i

private def tag (a b : ℤ) : Fin 4 :=
  if a % 2 = 0 then (if b % 2 = 0 then 0 else 3) else (if b % 2 = 0 then 1 else 2)

private lemma tag_grid (i : Fin 4) : tag (gridPoint i 0) (gridPoint i 1) = i := by
  fin_cases i <;> decide

private lemma lift_injective : Function.Injective lift := fun _ _ h =>
  funext fun i => Int.cast_injective (α := ℝ) (congrFun h i)

private def grid := univ.image (fun i : Fin 4 => lift (gridPoint i))

private lemma lattice_one : lattice (1 : Matrix (Fin 2) (Fin 2) ℝ) = Set.range lift := by
  simp only [lattice, one_mulVec]
  rfl

private lemma even_iff (v w : Fin 2 → ℤ) :
    lift v - lift w ∈ (fun x => (2 : ℝ) • x) '' lattice 1 ↔ ∀ i, 2 ∣ v i - w i := by
  rw [lattice_one]
  constructor
  · rintro ⟨_,⟨a,rfl⟩,he⟩ i
    refine ⟨a i, ?_⟩
    have h := congrFun he.symm i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lift] at h
    exact_mod_cast h
  · intro h
    choose a ha using h
    refine ⟨lift a, ⟨a,rfl⟩, funext fun i => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lift]
    exact_mod_cast (ha i).symm

private theorem grid_reps : Representatives (lattice 1)
    ((fun x => (2 : ℝ) • x) '' lattice 1) grid := by
  constructor
  · intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact lattice_one ▸ ⟨gridPoint i, rfl⟩
  · rw [lattice_one]
    rintro x ⟨v,rfl⟩
    let j := tag (v 0) (v 1)
    refine ⟨⟨lift (gridPoint j), mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩, ?_, ?_⟩
    · rw [← lattice_one]
      apply (even_iff _ _).mpr
      intro i
      dsimp only [j, tag]
      split_ifs <;> fin_cases i <;> simp [gridPoint] <;> omega
    · rintro ⟨x,hx⟩ he
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      rw [← lattice_one] at he
      have h := (even_iff v (gridPoint i)).mp he
      have h0 := h 0
      have h1 := h 1
      have heq : i = j := by
        dsimp [j, tag]
        fin_cases i <;> simp [gridPoint] at h0 h1 <;> split_ifs <;> first | rfl | omega
      subst i
      rfl

private lemma ray_eval (quad : DeloupTuraevTheorem1) (a b : ℤ) (hN : 0 < (a : ℝ)^2 - a*b + b^2) :
    quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) ((a : 𝓔) + (b : 𝓔)*eisOmega)) =
      (phase 0 + phase (((b : ℝ)-a)/2) + phase ((a : ℝ)/2) + phase (-(b : ℝ)/2)) / 2 := by
  rw [quadraticRayValue_of_representatives quad a b hN grid_reps, grid, sum_image]
  · simp [Fin.sum_univ_four, gridPoint, lift, dotProduct, Matrix.mulVec,
      eisMatrix, Fin.sum_univ_two]
  · intro i _ j _ h
    have he := lift_injective h
    exact (tag_grid i).symm.trans ((congrArg₂ tag (congrFun he 0)
      (congrFun he 1)).trans (tag_grid j))

private lemma omega_rel : eisOmega^2 + eisOmega + 1 = 0 := by
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  exact IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
    (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ))

set_option maxHeartbeats 800000 in
private lemma ray_omega (quad : DeloupTuraevTheorem1) (r : R₄) :
    quadraticRayValue (r * Ideal.Quotient.mk _ eisOmega) = quadraticRayValue r := by
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨a,b,rfl⟩ := eisInteger_coordinates q
  by_cases hz : a = 0 ∧ b = 0
  · simp [hz.1,hz.2]
  have hN : 0 < (a : ℝ)^2 - a*b + b^2 := by
    have hne : (a : ℝ) ≠ 0 ∨ (b : ℝ) ≠ 0 := by exact_mod_cast not_and_or.mp hz
    rcases hne with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg ((a : ℝ)-b),
      sq_nonneg (a : ℝ), sq_nonneg (b : ℝ)]
  have hprod : ((a : 𝓔) + (b : 𝓔)*eisOmega)*eisOmega =
      ((-b : ℤ) : 𝓔) + ((a-b : ℤ) : 𝓔)*eisOmega := by
    push_cast
    linear_combination (b : 𝓔) * omega_rel
  rw [← map_mul, hprod, ray_eval quad (-b) (a-b) (by push_cast; nlinarith), ray_eval quad a b hN]
  push_cast
  congr 1
  ring_nf

private lemma square_mod_four (u : R₄ˣ) :
    (u : R₄)^2 = 1 ∨ (u : R₄)^2 = Ideal.Quotient.mk _ eisOmega ∨
      (u : R₄)^2 = (Ideal.Quotient.mk _ eisOmega)^2 := by
  let π := Ideal.Quotient.mk (span {(4 : 𝓔)})
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : R₄)
  obtain ⟨a,b,rfl⟩ := eisInteger_coordinates x
  let d : 𝓔 := ((a%2 : ℤ) : 𝓔) + ((b%2 : ℤ) : 𝓔)*eisOmega
  let z : 𝓔 := ((a/2 : ℤ) : 𝓔) + ((b/2 : ℤ) : 𝓔)*eisOmega
  have ha : (a : 𝓔) = ((a%2 : ℤ) : 𝓔) +
    2*((a/2 : ℤ) : 𝓔) := by exact_mod_cast (show a = a%2+2*(a/2) by omega)
  have hb : (b : 𝓔) = ((b%2 : ℤ) : 𝓔) +
    2*((b/2 : ℤ) : 𝓔) := by exact_mod_cast (show b = b%2+2*(b/2) by omega)
  have hdec : (a : 𝓔) + (b : 𝓔)*eisOmega = d+2*z := by
    dsimp [d,z]
    linear_combination ha + eisOmega * hb
  have hsq : (u : R₄)^2 = π (d^2) := by
    rw [← hx, ← map_pow, hdec]
    apply Ideal.Quotient.eq.mpr
    exact mem_span_singleton.mpr ⟨d*z+z^2, by ring⟩
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · have hz : (u : R₄)^2 = 0 := by simpa [d,ha,hb,π] using hsq
    have hu : (u : R₄)^2 * (↑u⁻¹ : R₄)^2 = 1 := by rw [← mul_pow, ← Units.val_mul]; simp
    rw [hz, zero_mul] at hu
    exact Or.inl (hz.trans hu)
  · exact Or.inr (Or.inr (by simpa [d,ha,hb,π] using hsq))
  · exact Or.inl (by simpa [d,ha,hb,π] using hsq)
  · have hω : (1+eisOmega)^2 = eisOmega := by linear_combination omega_rel
    exact Or.inr (Or.inl (by simpa [d,ha,hb,hω,π] using hsq))

private lemma ray_square (quad : DeloupTuraevTheorem1) (r : R₄) (u : R₄ˣ) :
    quadraticRayValue (r * (u : R₄)^2) = quadraticRayValue r := by
  rcases square_mod_four u with h | h | h
  · rw [h, mul_one]
  · rw [h, ray_omega quad]
  · rw [h, sq, ← mul_assoc, ray_omega quad, ray_omega quad]

private lemma sign_square_left (quad : DeloupTuraevTheorem1) (x y v : QuadraticFamilyClass) :
    familySign (v^2 * x) y = familySign x y := by
  classical
  have hleft : quadraticRayValue (((v^2*x : R₄ˣ) : R₄) * (y : R₄)) =
      quadraticRayValue ((x : R₄)*y) := calc
    _ = quadraticRayValue (((x : R₄)*y) * (v : R₄)^2) :=
      congrArg _
        (by
          simp only [Units.val_mul, Units.val_pow_eq_pow_val]; rw [mul_assoc,
            mul_comm ((v : R₄)^2)])
    _ = _ := ray_square quad _ v
  have hright : quadraticRayValue ((v^2*x : R₄ˣ) : R₄) = quadraticRayValue x := calc
    _ = quadraticRayValue ((x : R₄) * (v : R₄)^2) :=
      congrArg _ (mul_comm _ _)
    _ = _ := ray_square quad _ v
  exact congrArg (fun t : ℂ => if t = -1 then (-1 : ℂ) else 1)
    (congrArg₂ (· / ·) hleft (congrArg (· * quadraticRayValue y) hright))

private lemma sign_comm (x y : QuadraticFamilyClass) : familySign x y = familySign y x := by
  classical
  change (if quadraticRayValue ((x : R₄) * y) / (quadraticRayValue x * quadraticRayValue y) = -1
    then -1 else 1) = _
  rw [mul_comm (x : R₄) (y : R₄), mul_comm (quadraticRayValue x)]
  rfl

/-- Sextic reciprocity on all good ideals. The two input ideals may have powers
of primes and may share primes. The sign depends only on their primary classes modulo four. -/
theorem sextic_reciprocity (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    {a n : Ideal 𝓔} (ha : AwayFromSix a) (hn : AwayFromSix n) :
    sextic n (generator a) = sextic a (generator n) * familySign (familyClass n)
      (familyClass a) := by
  have sf {b k : Ideal 𝓔} (hb : Starred b) (hk : AwayFromSix k) :
      sextic k (generator b) = sextic b (generator k) * familySign (familyClass k)
        (familyClass b) := by
    obtain ⟨v,s,rfl,hs⟩ := exists_sq_mul_squarefree k
    have hv := away_of_dvd hk (show v ∣
      v^2*s by exact (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_mul_right ..))
    have hs' := away_of_dvd hk (dvd_mul_left s (v^2))
    have hcl : familyClass (v^2 * s) = familyClass v ^ 2 * familyClass s := by
      simp only [pow_two, familyClass_mul (hv.mul hv) hs', familyClass_mul hv hv]
    rw [sextic_reciprocity_sq_mul recip quad hb hv ⟨hs',hs⟩, hcl, sign_square_left quad]
  obtain ⟨v,s,rfl,hs⟩ := exists_sq_mul_squarefree a
  have hv := away_of_dvd ha (show v ∣
    v^2*s by exact (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_mul_right ..))
  have hs' := away_of_dvd ha (dvd_mul_left s (v^2))
  have hcl : familyClass (v^2 * s) = familyClass v ^ 2 * familyClass s := by
    simp only [pow_two, familyClass_mul (hv.mul hv) hs', familyClass_mul hv hv]
  rw [hcl, sign_comm, sign_square_left quad, sign_comm]
  simp only [pow_two, generator_mul (hv.mul hv).coprime_three hs'.coprime_three,
    generator_mul hv.coprime_three hv.coprime_three, sextic_mul hn, sextic_den_mul]
  rw [← sq, sextic_sq_reciprocity recip hn hv, sf ⟨hs',hs⟩ hn]
  ring

private lemma sextic_one_den (x : 𝓔) : sextic 1 x = 1 := by
  rw [sextic, Ideal.one_eq_top, powerResidueSymbol_top, map_one]

/-- The zero-extended residue field character associated to a good prime power.
It is set to zero outside good denominators. -/
def localFactor (p : Ideal 𝓔) (e : ℕ) (x : 𝓔) : ℂ := open Classical in
  if hp : AwayFromSix p then tame p hp e x else 0

private theorem prime_product {n : Ideal 𝓔} (hn : AwayFromSix n) (x : 𝓔) :
    sextic n x = ∏ p ∈ (normalizedFactors n).toFinset,
      localFactor p ((normalizedFactors n).count p) x := by
  classical
  let F : Ideal 𝓔 →* ℂ := ⟨⟨fun p => sextic p x, sextic_one_den x⟩, fun a b => sextic_den_mul x⟩
  have he : (normalizedFactors n).prod = n := associated_iff_eq.mp (prod_normalizedFactors hn.1)
  calc
    sextic n x = F (normalizedFactors n).prod := by rw [he]; rfl
    _ = _ := (map_multiset_prod F _).trans (prod_multiset_map_count _ _)
    _ = _ := by
      refine prod_congr rfl fun p hp => ?_
      have hmem := Multiset.mem_toFinset.mp hp
      obtain ⟨hp',hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn.1).mp hmem
      have hp₆ := away_of_dvd hn hd
      rw [localFactor, dite_eq_left hp₆, tame_eq_pow hp₆ hp' (Multiset.count_pos.mpr hmem).ne']
      rfl

/-- The fixed mod-72 factor of the tame twist. Reducing the denominator to
modulo four supplies the sign of sextic reciprocity. -/
def rayFactor (ξ : RayCharacter) (k : QuadraticFamilyClass) (r : R₇₂) : ℂ := open Classical in
  let r₄ := Ideal.Quotient.factor (show span {(72 : 𝓔)} ≤ span {4} from
    span_singleton_le_span_singleton.mpr ⟨18, by norm_num⟩) r
  ξ r * familySign (if hu : IsUnit r₄ then hu.unit else 1) k

private theorem rayFactor_mk (ξ : RayCharacter) (k : QuadraticFamilyClass) (n : Ideal 𝓔) :
    rayFactor ξ k (Ideal.Quotient.mk _ (generator n)) =
      ξ (Ideal.Quotient.mk _ (generator n)) * familySign (familyClass n) k := rfl

/-- Equation (12) on good numerator ideals and arbitrary good denominators.
Only the class of the squarefree row modulo four enters the ray factor. Every
prime of `k g` occurs, including those whose positive exponent is zero modulo six. -/
theorem factor_twist_good (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    (ξ : RayCharacter) {k g n : Ideal 𝓔} (hk : AwayFromSix k) (hg : AwayFromSix g)
      (hn : AwayFromSix n) :
    ξ (Ideal.Quotient.mk _ (generator n)) * sextic n (generator k * generator g ^ 4) =
      rayFactor ξ (familyClass k) (Ideal.Quotient.mk _ (generator n)) *
        ∏ p ∈ (normalizedFactors (k*g)).toFinset,
          localFactor p ((normalizedFactors k).count p + 4 * (normalizedFactors g).count p)
            (generator n) := by
  classical
  have hg₂ := hg.mul hg
  have hg₄ : AwayFromSix (g^4) := by rw [show g^4 = (g*g)*(g*g) by ring]; exact hg₂.mul hg₂
  have hpow : sextic n (generator g) ^ 4 = sextic g (generator n) ^ 4 := by
    rw [show (4:ℕ) = 2*2 by decide, pow_mul, pow_mul, sextic_sq_reciprocity recip hn hg]
  have hden : sextic (k*g^4) (generator n) = sextic k (generator n) * sextic g (generator n)^4 := by
    simp only [show (4:ℕ) = 2+2 by decide, pow_add, pow_two, sextic_den_mul]
  have hprod := prime_product (hk.mul hg₄) (generator n)
  simp only [normalizedFactors_mul hk.1 (pow_ne_zero 4 hg.1),
    normalizedFactors_pow, Multiset.count_add,
    Multiset.count_nsmul, Multiset.toFinset_add] at hprod
  have hs : (4 • normalizedFactors g).toFinset = (normalizedFactors g).toFinset := by
    ext p
    simp [show (4:ℕ) = 1 + 1 + 1 + 1 by decide]
  rw [hs] at hprod
  rw [normalizedFactors_mul hk.1 hg.1, Multiset.toFinset_add, ← hprod, hden, rayFactor_mk,
    sextic_mul hn, sextic_pow hn, hpow, sextic_reciprocity recip quad hk hn]
  ring

private theorem prime_rational {p : Ideal 𝓔} (hp' : Prime p) (hp : AwayFromSix p) :
    sextic p (-1)^3 = (ZMod.χ₄ (absNorm p) : ℂ) ∧ sextic p (-2)^3 = (ZMod.χ₈' (absNorm p) : ℂ) := by
  classical
  let : p.IsMaximal := ((Ideal.prime_iff_isPrime hp'.ne_zero).mp hp').isMaximal hp'.ne_zero
  let := Ideal.Quotient.field p
  let := Ring.HasFiniteQuotients.finiteQuotient hp'.ne_zero
  let := Fintype.ofFinite (𝓔 ⧸ p)
  have hχ (y : 𝓔) : sextic p y ^ 3 = (quadraticChar (𝓔 ⧸ p) (Ideal.Quotient.mk p y) : ℂ) := by
    rw [← sexticChar_apply_mk hp, ← MulChar.pow_apply' _ (by decide : 3 ≠ 0),
      cubic_power_eq_quadraticChar (orderOf_sexticChar_prime hp hp')
        (ringChar_quotient_ne_two hp' hp)]
    rfl
  have hN : Fintype.card (𝓔 ⧸ p) =
    absNorm p := by rw [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card]
  simp only [hχ, map_neg, map_one, map_ofNat,
    quadraticChar_neg_one (ringChar_quotient_ne_two hp' hp),
    quadraticChar_neg_two (ringChar_quotient_ne_two hp' hp), hN, and_self]

/-- The quadratic supplements for the rational numerators `-1` and `-2`
hold for every good conductor, by the finite-field formulas at its prime factors. -/
theorem rational_supplements {n : Ideal 𝓔} (hn : AwayFromSix n) :
    sextic n (-1)^3 = (ZMod.χ₄ (absNorm n) : ℂ) ∧ sextic n (-2)^3 = (ZMod.χ₈' (absNorm n) : ℂ) := by
  revert hn
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h.1 rfl).elim
  | h₂ u hu =>
    have he : u = 1 := (Ideal.isUnit_iff.mp hu).trans Ideal.one_eq_top.symm
    subst u
    intro _
    rw [sextic_one_den, sextic_one_den, map_one]
    norm_num
  | h₃ a p ha hp ih =>
    intro hn
    have hp₆ := away_of_dvd hn (dvd_mul_right p a)
    have ha₆ := away_of_dvd hn (dvd_mul_left a p)
    obtain ⟨h1,h2⟩ := prime_rational hp hp₆
    obtain ⟨ha1,ha2⟩ := ih ha₆
    simp only [sextic_den_mul, mul_pow, h1,h2,ha1,ha2, map_mul, Nat.cast_mul,
      Int.cast_mul, and_self]

private lemma norm_coords (a b : ℤ) :
    (elementNorm ((a : 𝓔)+(b : 𝓔)*eisOmega) : ℤ) = a^2-a*b+b^2 := by
  have h := norm_eisEmbedding_sq ((a : 𝓔)+(b : 𝓔)*eisOmega)
  rw [Complex.sq_norm] at h
  simp only [map_add, map_intCast, map_mul, eisEmbedding_omega, ← Masullo.Lattice.omega_eq_exp,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, Masullo.Lattice.omega] at h
  have h' : (elementNorm ((a : 𝓔)+(b : 𝓔)*eisOmega) : ℝ) = (a : ℝ)^2-a*b+b^2 := by
    change (absNorm _ : ℝ) = _
    rw [← h]
    simp
    nlinarith [Masullo.Lattice.sq_sqrt_three,
      congrArg (fun t : ℝ => (b:ℝ)^2*t) Masullo.Lattice.sq_sqrt_three]
  exact_mod_cast h'

/-- The norm modulo a rational integer is determined by the Eisenstein residue. -/
theorem norm_congr {d : ℕ} {x y : 𝓔} (h : (d : 𝓔) ∣ x-y) :
    (elementNorm x : ZMod d) = (elementNorm y : ZMod d) := by
  obtain ⟨z,hz⟩ := h
  obtain ⟨a,b,rfl⟩ := eisInteger_coordinates y
  obtain ⟨c,e,rfl⟩ := eisInteger_coordinates z
  have hx : x = (↑(a + d*c : ℤ) : 𝓔) + (↑(b+d*e : ℤ) : 𝓔)*eisOmega := by
    push_cast
    linear_combination hz
  have hcast (p q : ℤ) : (elementNorm ((p : 𝓔)+(q : 𝓔)*eisOmega) : ZMod d) =
      (p : ZMod d)^2-p*q+q^2 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod d) (norm_coords p q)
  rw [hx,hcast,hcast]
  push_cast
  simp

private theorem eq_of_sq_cube {x y : ℂ} (hs : x^2 = y^2) (hc : x^3 = y^3) : x = y := by
  by_cases hy : y = 0
  · rw [hy, zero_pow (by decide : 2 ≠ 0)] at hs
    exact (eq_zero_of_pow_eq_zero hs).trans hy.symm
  apply mul_right_cancel₀ (pow_ne_zero 2 hy)
  calc
    _ = x^3 := by rw [← hs]; ring
    _ = y^3 := hc
    _ = _ := by ring

private theorem square_cubic {n : Ideal 𝓔} (hn : AwayFromSix n) (a : 𝓔) :
    sextic n a ^ 2 = eisEmbedding (cubicSymbol a (generator n)) := by
  rw [sextic, ← map_pow, powerResidueSymbol_six_sq hn.2, cubicSymbol, span_generator]

private lemma ray_dvd {n m : Ideal 𝓔}
    (he : Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n) = Ideal.Quotient.mk _ (generator m))
    {d : ℕ} (hd : d ∣ 72) : (d : 𝓔) ∣ generator n - generator m := by
  obtain ⟨c,hc⟩ := hd
  have hcast : (72 : 𝓔) = (d : 𝓔) * (c : 𝓔) := by exact_mod_cast hc
  exact (show (d : 𝓔) ∣ 72 from ⟨c, hcast⟩).trans (mem_span_singleton.mp (Ideal.Quotient.eq.mp he))

private lemma norm_ray_congr {n m : Ideal 𝓔}
    (he : Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n) = Ideal.Quotient.mk _ (generator m))
    {d : ℕ} (hd : d ∣ 72) : (absNorm n : ZMod d) = (absNorm m : ZMod d) := by
  simpa only [elementNorm, span_generator] using norm_congr (ray_dvd he hd)

theorem sextic_neg_two_congr (recip : DunnRadziwillReciprocity) {n m : Ideal 𝓔}
    (hn : AwayFromSix n) (hm : AwayFromSix m)
    (he : Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n) = Ideal.Quotient.mk _ (generator m)) :
    sextic n (-2) = sextic m (-2) := by
  apply eq_of_sq_cube
  · rw [square_cubic hn, square_cubic hm, cubicSymbol_neg_two recip
      (eisPrimary_generator hn.coprime_three),
      cubicSymbol_neg_two recip (eisPrimary_generator hm.coprime_three)]
    apply congrArg eisEmbedding
    apply powerResidueSymbol_congr
    apply Ideal.Quotient.eq.mpr
    apply mem_span_singleton.mpr
    simpa using ray_dvd he (by decide : 2 ∣ 72)
  · rw [(rational_supplements hn).2, (rational_supplements hm).2,
      norm_ray_congr he (by decide : 8 ∣ 72)]

private lemma sextic_one_num {n : Ideal 𝓔} (hn : AwayFromSix n) : sextic n 1 = 1 := by
  rw [← sexticChar_apply_mk hn, map_one, map_one]

theorem sextic_unit_congr (recip : DunnRadziwillReciprocity) {n m : Ideal 𝓔}
    (hn : AwayFromSix n) (hm : AwayFromSix m)
    (he : Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n) =
      Ideal.Quotient.mk _ (generator m))
    (u : 𝓔ˣ) :
    sextic n u = sextic m u := by
  have pow_neg {a : Ideal 𝓔} (ha : AwayFromSix a) : sextic a (-1) ^ 2 = 1 := by
    rw [← sextic_pow ha]; norm_num [sextic_one_num ha]
  have hneg : sextic n (-1) = sextic m (-1) := eq_of_sq_cube ((pow_neg hn).trans
    (pow_neg hm).symm) (by
    rw [(rational_supplements hn).1, (rational_supplements hm).1,
      norm_ray_congr he (by decide : 4 ∣ 72)])
  have h9 : (9 : 𝓔) ∣ generator m - generator n := ray_dvd he.symm (by decide : 9 ∣ 72)
  have hcube : eisOmega^3 = 1 := by linear_combination (eisOmega-1) * omega_rel
  have ho : sextic n eisOmega = sextic m eisOmega := by
    apply eq_of_sq_cube
    · rw [square_cubic hn, square_cubic hm,
        (cubic_supplements_congr recip (eisPrimary_generator hn.coprime_three) h9).2]
    · rw [← sextic_pow hn, ← sextic_pow hm, hcube, sextic_one_num hn, sextic_one_num hm]
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let spec := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  let η : 𝓔ˣ := (spec.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : 𝓔) = eisOmega := rfl
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem spec u
  change u ∈ [1,-1,η,-η,η^2,-η^2] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Units.val_one, Units.val_neg, Units.val_pow_eq_pow_val, hη,
      show -eisOmega = (-1 : 𝓔)*eisOmega by ring,
      show -(eisOmega^2) = (-1 : 𝓔)*eisOmega^2 by ring, sextic_pow hn, sextic_pow hm,
      sextic_mul hn, sextic_mul hm, sextic_one_num hn, sextic_one_num hm, ho, hneg]

theorem sextic_lambda_sq_congr (recip : DunnRadziwillReciprocity) {n m : Ideal 𝓔}
    (hn : AwayFromSix n) (hm : AwayFromSix m)
    (he : Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n) = Ideal.Quotient.mk _ (generator m)) :
    sextic n eisLambda ^ 2 = sextic m eisLambda ^ 2 := by
  rw [square_cubic hn, square_cubic hm, (cubic_supplements_congr recip
    (eisPrimary_generator hn.coprime_three) (ray_dvd he.symm (by decide : 9 ∣ 72))).1]

private def localPhase (n : Ideal 𝓔) (z a : 𝓔) (x : 𝓔 ⧸ n) : ℂ :=
  differentCharacter (eisEmbedding (a * (Quotient.out x)^2) / eisEmbedding z)

private lemma localPhase_mk {n : Ideal 𝓔} {z : 𝓔} (hz : span {z} = n) (a x : 𝓔) :
    localPhase n z a (Ideal.Quotient.mk n x) = differentCharacter (eisEmbedding (a*x^2) /
      eisEmbedding z) := by
  apply differentCharacter_div_congr
  rw [← mem_span_singleton, hz, ← Ideal.Quotient.eq]
  simp

private def localSum (n : Ideal 𝓔) (z a : 𝓔) : ℂ := ∑ᶠ x : 𝓔 ⧸ n, localPhase n z a x

private lemma localSum_congr {n : Ideal 𝓔} {z a b : 𝓔} (hz : span {z} = n)
    (hab : z ∣ a-b) : localSum n z a = localSum n z b := by
  apply finsum_congr
  intro x
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [localPhase_mk hz, localPhase_mk hz]
  apply differentCharacter_div_congr
  rw [← sub_mul]
  exact hab.mul_right _

private theorem localSum_crt {n m : Ideal 𝓔} {c d : 𝓔} (hc : span {c} = n) (hd : span {d} = m)
    (h : IsCoprime n m) (hc₀ : c ≠ 0) (hd₀ : d ≠ 0) :
    localSum (n*m) (c*d) 1 = localSum n c d * localSum m d c := by
  classical
  have hn : n ≠ ⊥ := by simpa [← hc] using hc₀
  have hm : m ≠ ⊥ := by simpa [← hd] using hd₀
  let := Ring.HasFiniteQuotients.finiteQuotient hn
  let := Ring.HasFiniteQuotients.finiteQuotient hm
  let := Ring.HasFiniteQuotients.finiteQuotient (mul_ne_zero hn hm)
  let := Fintype.ofFinite (𝓔 ⧸ n)
  let := Fintype.ofFinite (𝓔 ⧸ m)
  let := Fintype.ofFinite (𝓔 ⧸ (n*m))
  have hu := (isUnit_mk_iff_coprime_span n d).mpr (hd ▸ h)
  have hv := (isUnit_mk_iff_coprime_span m c).mpr (hc ▸ h.symm)
  let e := (hu.unit.mulLeft.prodCongr hv.unit.mulLeft).trans (quotientMulEquivQuotientProd n
    m h).symm.toEquiv
  have hc' : Ideal.Quotient.mk n c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (hc ▸ mem_span_singleton_self c)
  have hd' : Ideal.Quotient.mk m d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (hd ▸ mem_span_singleton_self d)
  have he (x y : 𝓔) : e (Ideal.Quotient.mk n x, Ideal.Quotient.mk m y) =
      Ideal.Quotient.mk (n*m) (d*x + c*y) := by
    apply (quotientMulEquivQuotientProd n m h).injective
    simp only [e, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe,
      RingEquiv.coe_toEquiv, RingEquiv.apply_symm_apply]
    apply Prod.ext <;> simp [Units.mulLeft, hc', hd']
  have hcd : span {c*d} = n*m := by rw [← span_singleton_mul_span_singleton, hc, hd]
  have hcE : eisEmbedding c ≠ 0 := fun e => hc₀ (eisEmbedding_injective (e.trans (map_zero _).symm))
  have hdE : eisEmbedding d ≠ 0 := fun e => hd₀ (eisEmbedding_injective (e.trans (map_zero _).symm))
  simp only [localSum, finsum_eq_sum_of_fintype]
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [he, localPhase_mk hcd, localPhase_mk hc, localPhase_mk hd, one_mul]
  have hp : eisEmbedding ((d*x+c*y)^2) / eisEmbedding (c*d) =
      eisEmbedding (d*x^2) / eisEmbedding c + eisEmbedding (c*y^2) / eisEmbedding d +
        eisEmbedding (2*x*y) := by
    simp only [map_mul, map_pow, map_add, map_ofNat]
    field_simp
    ring
  rw [hp, differentCharacter_add, differentCharacter_eisEmbedding, mul_one, differentCharacter_add]

private theorem localSum_shift {n : Ideal 𝓔} (hn : Starred n) (a : 𝓔)
    (ha : IsCoprime n (span {a})) :
    localSum n (generator n) a = (sextic n a)^3 * localSum n (generator n) 1 := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient hn.1.1
  let := Fintype.ofFinite (𝓔 ⧸ n)
  let ψ := quotientDifferentCharacter n
  let χ := sexticChar hn.1 ^ 3
  let u := ((isUnit_mk_iff_coprime_span n a).mpr ha).unit
  have hu : (u : 𝓔 ⧸ n) = Ideal.Quotient.mk n a := IsUnit.unit_spec _
  have hφ (d : 𝓔) : localSum n (generator n) d = ∑ x : 𝓔 ⧸ n,
      (ψ.mulShift (Ideal.Quotient.mk n d)) (x^2) := by
    rw [localSum, finsum_eq_sum_of_fintype]
    refine sum_congr rfl fun x _ => ?_
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [localPhase_mk (span_generator n), AddChar.mulShift_apply, ← map_pow, ← map_mul]
    exact (quotientDifferentCharacter_mk n (d*x^2)).symm
  have hψ := quotientDifferentCharacter_isPrimitive hn.1.1
  have hψu : (ψ.mulShift (u : 𝓔 ⧸ n)).IsPrimitive := by
    intro b hb
    rw [AddChar.mulShift_mulShift]
    exact hψ (fun h => hb ((u.isUnit.mul_right_inj).mp (h.trans (mul_zero _).symm)))
  have hval : χ u = sextic n a ^
    3 := by rw [hu]; simp only [χ, MulChar.pow_apply' _ (by decide : 3 ≠ 0),
    sexticChar_apply_mk]
  have hs : (sextic n a ^
    3)^2 = 1 := by simpa only [quadraticResidue_apply] using quadraticResidue_sq hn.1 ha
  have hInv : χ⁻¹ u = sextic n a ^ 3 := by
    rw [MulChar.inv_apply_eq_inv', hval]
    exact inv_eq_of_mul_eq_one_right (by simpa [sq] using hs)
  rw [hφ, ← hu, ← gaussSum_three_eq_sum_sq n hn _ hψu, gaussSum_mulShift_eq, hφ, map_one,
    AddChar.mulShift_one, ← gaussSum_three_eq_sum_sq n hn ψ hψ]
  change χ⁻¹ u * _ = _
  rw [hInv]


private lemma lambda_dvd_three : eisLambda ∣ (3 : 𝓔) :=
    ⟨-eisLambda, by rw [mul_neg, ← sq, eisLambda_sq, neg_neg]⟩

private lemma lambda_ray_ne_zero (quad : DeloupTuraevTheorem1) :
    quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) eisLambda) ≠ 0 := by
  have h := ray_eval quad 1 2 (by norm_num)
  norm_num [eisLambda] at h ⊢
  rw [h]
  have hp : phase (-1) = -1 := by
    simp [phase, Complex.exp_neg, Complex.exp_pi_mul_I]
  have hz : phase 0 = 1 := by simp [phase]
  rw [hp,hz]
  have hne : phase (1/2:ℝ) ≠ 0 := Complex.exp_ne_zero _
  intro he
  apply hne
  linear_combination he

private lemma good_ray_unit {n : Ideal 𝓔} (hn : AwayFromSix n) :
    IsUnit (Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator n)) := by
  have h₂ : IsCoprime n (span {(2 : 𝓔)}) := hn.2.of_isCoprime_of_dvd_right
    (span_singleton_dvd_span_singleton_iff_dvd.mpr ⟨3, by norm_num⟩)
  have h₄ : IsCoprime n (span {(4 : 𝓔)}) := by
    simpa only [span_singleton_pow, show (2 : 𝓔) ^ 2 = 4 by norm_num] using h₂.pow_right (n := 2)
  exact (isUnit_mk_iff_coprime_span _ _).mpr (by rwa [span_generator, isCoprime_comm])

private lemma lambda_ratio_squarefree (quad : DeloupTuraevTheorem1) {n : Ideal 𝓔} (hn : Starred n) :
    sextic n eisLambda ^ 3 =
      quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator n * eisLambda)) /
        (quadraticRayValue (Ideal.Quotient.mk _ (generator n)) *
          quadraticRayValue (Ideal.Quotient.mk _ eisLambda)) := by
  let L := span {eisLambda}
  have hq : quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator n)) ≠ 0 := by
    rw [quadraticRayValue_mk quad hn.1.1, ← normalizedGauss_three_eq_quadraticExponentialSum hn]
    intro hz
    have h := norm_normalizedGauss_eq_one hn (j := 3) (by decide) (by decide)
    simp [hz] at h
  have hg : generator n ≠ 0 := fun hz => hn.1.1 (by simpa [hz] using (span_generator n).symm)
  have hspan : span {generator n * eisLambda} = n*L := by
    rw [← span_singleton_mul_span_singleton, span_generator]
  have hc := localSum_crt (span_generator n) (rfl : span {eisLambda} = L) (coprime_span_lambda hn.1)
    hg eisLambda_prime.ne_zero
  rw [localSum_shift hn _ (coprime_span_lambda hn.1),
    localSum_congr (rfl : span {eisLambda} = L) (lambda_dvd_three.trans (eisPrimary_generator
      hn.1.coprime_three))] at hc
  have hQ {m : Ideal 𝓔} {a : 𝓔} (h : span {a} = m) (ha : a ≠ 0) :
      quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) a) =
        localSum m a 1 / Real.sqrt (absNorm m) := by
    simpa only [localSum,localPhase,one_mul,map_pow] using
      quadraticRayValue_eq_element_sum quad a ha h
  apply (eq_div_iff (mul_ne_zero hq (lambda_ray_ne_zero quad))).mpr
  rw [hQ hspan (mul_ne_zero hg eisLambda_prime.ne_zero), hQ (span_generator n) hg,
    hQ (rfl : span {eisLambda} = L) eisLambda_prime.ne_zero, hc, map_mul, Nat.cast_mul,
    Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  ring

private lemma lambda_ratio (quad : DeloupTuraevTheorem1) {n : Ideal 𝓔} (hn : AwayFromSix n) :
    sextic n eisLambda ^ 3 =
      quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator n * eisLambda)) /
        (quadraticRayValue (Ideal.Quotient.mk _ (generator n)) *
          quadraticRayValue (Ideal.Quotient.mk _ eisLambda)) := by
  obtain ⟨v,s,rfl,hs⟩ := exists_sq_mul_squarefree n
  have hv := away_of_dvd hn (show v ∣
    v^2*s by exact (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_mul_right ..))
  have hs' := away_of_dvd hn (dvd_mul_left s (v^2))
  have hden : generator (v^2*s) = generator v ^ 2 * generator s := by
    simp only [sq, generator_mul (hv.mul hv).coprime_three hs'.coprime_three,
      generator_mul hv.coprime_three hv.coprime_three]
  have he : sextic (v^2*s) eisLambda ^ 3 = sextic s eisLambda ^ 3 := by
    have hu : sextic v eisLambda ^ 6 = 1 := by
      simp only [sextic, ← map_pow, powerResidueSymbol_six_pow_six hv.1 hv.2,
        ite_eq_left (coprime_span_lambda hv), map_one]
    rw [sq,sextic_den_mul,sextic_den_mul,mul_pow,← sq,← pow_mul,hu,one_mul]
  obtain ⟨u,hu⟩ := good_ray_unit hv
  rw [he, lambda_ratio_squarefree quad ⟨hs',hs⟩, hden]
  simp only [map_mul,map_pow,← hu]
  rw [show (u : R₄)^2 * Ideal.Quotient.mk _ (generator s) * Ideal.Quotient.mk _ eisLambda =
      (Ideal.Quotient.mk _ (generator s) * Ideal.Quotient.mk _ eisLambda) * (u : R₄)^2 by ring,
    ray_square quad _ u, mul_comm ((u : R₄)^2), ray_square quad _ u]

/-- The ramified sextic supplement at λ depends only on the primary denominator modulo 72. -/
theorem sextic_lambda_congr (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    {n m : Ideal 𝓔}
    (hn : AwayFromSix n) (hm : AwayFromSix m)
    (he : Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n) = Ideal.Quotient.mk _ (generator m)) :
    sextic n eisLambda = sextic m eisLambda := by
  apply eq_of_sq_cube (sextic_lambda_sq_congr recip hn hm he)
  have he₄ : Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator n) = Ideal.Quotient.mk _ (generator m) :=
    Ideal.Quotient.eq.mpr (mem_span_singleton.mpr (by simpa using ray_dvd he (by decide : 4 ∣ 72)))
  rw [lambda_ratio quad hn, lambda_ratio quad hm, map_mul,map_mul,he₄]

private lemma norm_ne_two (x : 𝓔) : elementNorm x ≠ 2 := by
  rintro h
  obtain ⟨a,b,rfl⟩ := eisInteger_coordinates x
  have he := norm_coords a b
  rw [h] at he
  have hz := congrArg (Int.cast : ℤ → ZMod 3) he
  push_cast at hz
  have hc : (3 : ZMod 3) = 0 := rfl
  have hs : ((a : ZMod 3)+b)^2 = 2 := by
    linear_combination -hz + (a*b : ZMod 3)*hc
  exact (show ∀ t : ZMod 3, t^2 ≠ 2 by decide) _ hs

private lemma norm_neg_two : elementNorm (-2) = 4 := by
  have h := norm_coords (-2) 0
  norm_num at h
  exact_mod_cast h

/-- The rational prime two is inert in the Eisenstein integers. -/
theorem neg_two_prime : Prime (-2 : 𝓔) := by
  have hu (a : 𝓔) : IsUnit a ↔ elementNorm a = 1 :=
    span_singleton_eq_top.symm.trans absNorm_eq_one_iff.symm
  apply Irreducible.prime
  constructor
  · simp [hu,norm_neg_two]
  · intro a b h
    have hnorm : elementNorm a * elementNorm b = 4 := by
      rw [← norm_neg_two,h]
      simp only [elementNorm,← span_singleton_mul_span_singleton,map_mul]
    rw [hu,hu]
    by_contra! hh
    have ha : elementNorm a ≤ 4 := Nat.le_of_dvd (by decide) ⟨_, hnorm.symm⟩
    have hb : elementNorm b ≤ 4 := Nat.le_of_dvd (by decide) ⟨_, (mul_comm _ _).trans hnorm |>.symm⟩
    have := norm_ne_two a
    have := norm_ne_two b
    interval_cases elementNorm a <;> interval_cases elementNorm b <;> omega

/-- Split a nonzero Eisenstein integer into its unit, factors at two and λ,
and the primary generator of an ideal prime to six. -/
theorem exists_good_part {x : 𝓔} (hx : x ≠ 0) :
    ∃ (u : 𝓔ˣ) (i j : ℕ) (k : Ideal 𝓔), AwayFromSix k ∧
      x = (u : 𝓔) * (-2)^i * eisLambda^j * generator k := by
  obtain ⟨i,a,ha,hx'⟩ := WfDvdMonoid.max_power_factor hx neg_two_prime.irreducible
  have ha₀ : a ≠ 0 := by rintro rfl; simp [hx'] at hx
  obtain ⟨j,b,hb,ha'⟩ := WfDvdMonoid.max_power_factor ha₀ eisLambda_prime.irreducible
  have hb₀ : b ≠ 0 := by rintro rfl; simp [ha'] at ha₀
  have h₂ : IsCoprime (-2:𝓔) b :=
    neg_two_prime.coprime_iff_not_dvd.mpr (fun h => ha (ha' ▸ h.trans (dvd_mul_left ..)))
  have h₃ := (eisLambda_prime.coprime_iff_not_dvd.mpr hb).pow_left (m := 2)
  have h₆ : IsCoprime b (6 : 𝓔) := by
    have h := h₂.symm.mul_right h₃.symm
    rwa [eisLambda_sq,show (-2 : 𝓔)*(-3) = 6 by norm_num] at h
  let k := span {b}
  obtain ⟨u,hu⟩ := span_singleton_eq_span_singleton.mp (span_generator k)
  refine ⟨u,i,j,k,⟨by simpa [k] using hb₀, (isCoprime_span_singleton_iff _ _).mpr h₆⟩,?_⟩
  rw [hx', ha',← hu]
  ring

/-- The fixed ray weight of (12). The residues which do not occur for good primary
denominators have weight zero. All its parameters vary in finite sets. -/
def fixedFactor (ξ : RayCharacter) (u : 𝓔ˣ) (i j : Fin 6) (k : QuadraticFamilyClass)
    (r : R₇₂) : ℂ :=
  open Classical in
  if h : ∃ n : Ideal 𝓔, AwayFromSix n ∧ Ideal.Quotient.mk _ (generator n) = r then
    rayFactor ξ k r * sextic h.choose ((u : 𝓔) * (-2)^(i : ℕ) * eisLambda^(j : ℕ))
  else 0

theorem fixedFactor_mk (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    (ξ : RayCharacter) (u : 𝓔ˣ) (i j : ℕ) (k : QuadraticFamilyClass) {n : Ideal 𝓔}
      (hn : AwayFromSix n) :
    fixedFactor ξ u (Fin.ofNat 6 i) (Fin.ofNat 6 j) k (Ideal.Quotient.mk _ (generator n)) =
      rayFactor ξ k (Ideal.Quotient.mk _ (generator n)) *
        sextic n ((u : 𝓔)*(-2)^i*eisLambda^j) := by
  classical
  have h : ∃ m : Ideal 𝓔, AwayFromSix m ∧ Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator m) =
      Ideal.Quotient.mk _ (generator n) := ⟨n, hn, rfl⟩
  have hm := h.choose_spec.1
  have he := h.choose_spec.2
  have h₂ : IsCoprime n (span {(-2 : 𝓔)}) := hn.2.of_isCoprime_of_dvd_right
    (span_singleton_dvd_span_singleton_iff_dvd.mpr ⟨-3,by norm_num⟩)
  have hs (x : 𝓔) (hx : IsCoprime n (span {x})) : sextic n x ^ 6 = 1 := by
    simp only [sextic, ← map_pow, powerResidueSymbol_six_pow_six hn.1 hn.2, ite_eq_left hx,map_one]
  rw [fixedFactor,dite_eq_left h]
  simp only [sextic_mul hm, sextic_pow hm, sextic_mul hn, sextic_pow hn,
    sextic_unit_congr recip hm hn he, sextic_neg_two_congr recip hm hn he,
      sextic_lambda_congr recip quad hm hn he]
  rw [pow_eq_pow_mod i (hs _ h₂), pow_eq_pow_mod j (hs _ (coprime_span_lambda hn))]
  rfl

theorem norm_fixedFactor_le (ξ : RayCharacter) (u : 𝓔ˣ) (i j : Fin 6)
    (k : QuadraticFamilyClass) (r : R₇₂) :
    ‖fixedFactor ξ u i j k r‖ ≤ 1 := by
  classical
  unfold fixedFactor
  split
  next h =>
    let n := h.choose
    have hn : AwayFromSix n := h.choose_spec.1
    have hr := congrArg (rayFactor ξ k) h.choose_spec.2.symm
    rw [hr,rayFactor_mk,mul_right_comm, norm_mul]
    have hsign := (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, by decide, familySign_sq (familyClass n) k⟩).norm_eq_one
    rw [hsign,mul_one]
    simpa only [twist,ite_eq_left hn,generator_one,one_pow,mul_one] using
      norm_twist_le_one ξ ((u : 𝓔) * (-2)^(i : ℕ) * eisLambda^(j : ℕ)) 1 n
  · simp

/-- A single finite set contains all the fixed ray weights as both numerators and
the original ray character vary. -/
theorem finite_fixedFactors :
    (Set.range (fun t : RayCharacter × 𝓔ˣ × Fin 6 × Fin 6 × QuadraticFamilyClass =>
      fixedFactor t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2)).Finite := by
  classical
  let := Ring.HasFiniteQuotients.finiteQuotient (I := span {(72 : 𝓔)}) (by simp)
  let : Finite 𝓔ˣ := Finite.of_injective (fun u : 𝓔ˣ =>
    (⟨(u : 𝓔), (mem_elementRows (by norm_num : (0:ℝ) ≤ 1)).mpr
      ⟨u.ne_zero, by simp [elementNorm, span_singleton_eq_top.mpr u.isUnit]⟩⟩ : elementRows 1))
    (fun _ _ h => Units.ext (congrArg Subtype.val h))
  exact Set.finite_range _

/-- Factor the twist when the good parts of the two numerators are specified. -/
theorem factor_twist_of_parts (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    (ξ : RayCharacter) {x y : 𝓔} {u v : 𝓔ˣ} {i j a b : ℕ} {k g n : Ideal 𝓔}
    (hk : AwayFromSix k) (hg : AwayFromSix g) (hn : AwayFromSix n)
    (hx : x = (u : 𝓔)*(-2)^i*eisLambda^j*generator k)
    (hy : y = (v : 𝓔)*(-2)^a*eisLambda^b*generator g) :
    ξ (Ideal.Quotient.mk _ (generator n)) * sextic n (x*y^4) =
      fixedFactor ξ (u*v^4) (Fin.ofNat 6 (i+4*a)) (Fin.ofNat 6 (j+4*b)) (familyClass k)
          (Ideal.Quotient.mk _ (generator n)) *
        ∏ p ∈ (normalizedFactors (k*g)).toFinset,
          localFactor p ((normalizedFactors k).count p + 4*(normalizedFactors g).count p)
            (generator n) := by
  classical
  let w : 𝓔 := ((u * v^4 : 𝓔ˣ) : 𝓔) * (-2)^(i+4*a) * eisLambda^(j+4*b)
  have hxy : x * y^4 = w * (generator k * generator g^4) := by
    rw [hx,hy]
    dsimp only [w]
    rw [Nat.mul_comm 4 a,Nat.mul_comm 4 b]
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,pow_add,pow_mul]
    ring
  rw [hxy, sextic_mul hn, mul_left_comm, factor_twist_good recip quad ξ hk hg hn,
    fixedFactor_mk recip quad ξ _ _ _ _ hn]
  dsimp only [w]
  ring

/-- Every nonzero pair of element numerators has a fixed ray weight modulo 72
and a product of zero-extended tame factors with the indicated valuations. -/
theorem factor_twist (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    (ξ : RayCharacter) {x y : 𝓔} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (u : 𝓔ˣ) (i j : Fin 6) (k g : Ideal 𝓔), AwayFromSix k ∧ AwayFromSix g ∧
      (∀ n : Ideal 𝓔, AwayFromSix n →
        ξ (Ideal.Quotient.mk _ (generator n)) * sextic n (x*y^4) =
          fixedFactor ξ u i j (familyClass k) (Ideal.Quotient.mk _ (generator n)) *
            ∏ p ∈ (normalizedFactors (k*g)).toFinset,
              localFactor p ((normalizedFactors k).count p + 4*(normalizedFactors g).count p)
                (generator n)) := by
  obtain ⟨u,i,j,k,hk,hx⟩ := exists_good_part hx
  obtain ⟨v,a,b,g,hg,hy⟩ := exists_good_part hy
  exact ⟨u*v^4,_,_,k,g,hk,hg, fun _ hn => factor_twist_of_parts recip quad ξ hk hg hn hx hy⟩

end Masullo.QRH.MeanSquare.ReflectionTwist
