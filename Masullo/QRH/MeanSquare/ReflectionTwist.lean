import Masullo.QRH.MeanSquare.FamilyReciprocity
import Masullo.QRH.MeanSquare.FamilySymbol
import Masullo.QRH.MeanSquare.ReflectionCoefficients

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
theorem sextic_squarefree_reciprocity (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
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
      have hu := norm_sextic_of_coprime ha.1 (a := generator n) (by rwa [span_generator, isCoprime_comm])
      exact norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
    change x = y * _
    apply mul_right_cancel₀ (pow_ne_zero 2 hy)
    calc
      _ = x ^ 3 := by rw [← hs]; ring
      _ = _ := ht
      _ = _ := by ring
  · simp [sextic_zero hn.1 hc, sextic_zero ha.1 (fun h => hc h.symm)]

private theorem away_of_dvd {d n : Ideal 𝓔} (hn : AwayFromSix n) (hd : d ∣ n) : AwayFromSix d :=
  ⟨fun h => hn.1 (zero_dvd_iff.mp (show (0 : Ideal 𝓔) ∣ n by rwa [h] at hd)), hn.2.of_isCoprime_of_dvd_left hd⟩

/-- For a squarefree good numerator, only the squarefree part of the denominator
enters the sign. The square factor of the denominator obeys cubic reciprocity. -/
theorem sextic_reciprocity_sq_mul (recip : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1)
    {a v s : Ideal 𝓔} (ha : Starred a) (hv : AwayFromSix v) (hs : Starred s) :
    sextic (v ^ 2 * s) (generator a) =
      sextic a (generator (v ^ 2 * s)) * familySign (familyClass s) (familyClass a) := by
  have hv₂ := hv.mul hv
  simp only [pow_two, sextic_den_mul,
    generator_mul hv.coprime_three hv.coprime_three, generator_mul hv₂.coprime_three hs.1.coprime_three,
    sextic_mul ha.1]
  rw [← sq, sextic_sq_reciprocity recip hv ha.1, sextic_squarefree_reciprocity recip quad ha hs]
  ring

/-- The local factor at a positive numerator valuation. The bundled character
power at exponent zero retains the zero on nonunits after reduction modulo six. -/
def tame (p : Ideal 𝓔) (hp : AwayFromSix p) (e : ℕ) (x : 𝓔) : ℂ :=
  (sexticChar hp ^ (e % 6)) (Ideal.Quotient.mk p x)

theorem tame_eq_pow {p : Ideal 𝓔} (hp : AwayFromSix p) (hp' : Prime p) {e : ℕ} (he : e ≠ 0) (x : 𝓔) :
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

private theorem grid_reps : Representatives (lattice 1) ((fun x => (2 : ℝ) • x) '' lattice 1) grid := by
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
  · simp [Fin.sum_univ_four, gridPoint, lift, dotProduct, Matrix.mulVec, eisMatrix, Fin.sum_univ_two]
  · intro i _ j _ h
    have he := lift_injective h
    exact (tag_grid i).symm.trans ((congrArg₂ tag (congrFun he 0) (congrFun he 1)).trans (tag_grid j))

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
  have ha : (a : 𝓔) = ((a%2 : ℤ) : 𝓔) + 2*((a/2 : ℤ) : 𝓔) := by exact_mod_cast (show a = a%2+2*(a/2) by omega)
  have hb : (b : 𝓔) = ((b%2 : ℤ) : 𝓔) + 2*((b/2 : ℤ) : 𝓔) := by exact_mod_cast (show b = b%2+2*(b/2) by omega)
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
      congrArg _ (by simp only [Units.val_mul, Units.val_pow_eq_pow_val]; rw [mul_assoc, mul_comm ((v : R₄)^2)])
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
    sextic n (generator a) = sextic a (generator n) * familySign (familyClass n) (familyClass a) := by
  have sf {b k : Ideal 𝓔} (hb : Starred b) (hk : AwayFromSix k) :
      sextic k (generator b) = sextic b (generator k) * familySign (familyClass k) (familyClass b) := by
    obtain ⟨v,s,rfl,hs⟩ := exists_sq_mul_squarefree k
    have hv := away_of_dvd hk (show v ∣ v^2*s by exact (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_mul_right ..))
    have hs' := away_of_dvd hk (dvd_mul_left s (v^2))
    have hcl : familyClass (v^2 * s) = familyClass v ^ 2 * familyClass s := by
      simp only [pow_two, familyClass_mul (hv.mul hv) hs', familyClass_mul hv hv]
    rw [sextic_reciprocity_sq_mul recip quad hb hv ⟨hs',hs⟩, hcl, sign_square_left quad]
  obtain ⟨v,s,rfl,hs⟩ := exists_sq_mul_squarefree a
  have hv := away_of_dvd ha (show v ∣ v^2*s by exact (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_mul_right ..))
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
    (ξ : RayCharacter) {k g n : Ideal 𝓔} (hk : AwayFromSix k) (hg : AwayFromSix g) (hn : AwayFromSix n) :
    ξ (Ideal.Quotient.mk _ (generator n)) * sextic n (generator k * generator g ^ 4) =
      rayFactor ξ (familyClass k) (Ideal.Quotient.mk _ (generator n)) *
        ∏ p ∈ (normalizedFactors (k*g)).toFinset,
          localFactor p ((normalizedFactors k).count p + 4 * (normalizedFactors g).count p) (generator n) := by
  classical
  have hg₂ := hg.mul hg
  have hg₄ : AwayFromSix (g^4) := by rw [show g^4 = (g*g)*(g*g) by ring]; exact hg₂.mul hg₂
  have hpow : sextic n (generator g) ^ 4 = sextic g (generator n) ^ 4 := by
    rw [show (4:ℕ) = 2*2 by decide, pow_mul, pow_mul, sextic_sq_reciprocity recip hn hg]
  have hden : sextic (k*g^4) (generator n) = sextic k (generator n) * sextic g (generator n)^4 := by
    simp only [show (4:ℕ) = 2+2 by decide, pow_add, pow_two, sextic_den_mul]
  have hprod := prime_product (hk.mul hg₄) (generator n)
  simp only [normalizedFactors_mul hk.1 (pow_ne_zero 4 hg.1), normalizedFactors_pow, Multiset.count_add,
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
      cubic_power_eq_quadraticChar (orderOf_sexticChar_prime hp hp') (ringChar_quotient_ne_two hp' hp)]
    rfl
  have hN : Fintype.card (𝓔 ⧸ p) = absNorm p := by rw [Ideal.absNorm_eq_natCard, Nat.card_eq_fintype_card]
  simp only [hχ, map_neg, map_one, map_ofNat, quadraticChar_neg_one (ringChar_quotient_ne_two hp' hp),
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
    simp only [sextic_den_mul, mul_pow, h1,h2,ha1,ha2, map_mul, Nat.cast_mul, Int.cast_mul, and_self]

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
  · rw [square_cubic hn, square_cubic hm, cubicSymbol_neg_two recip (eisPrimary_generator hn.coprime_three),
      cubicSymbol_neg_two recip (eisPrimary_generator hm.coprime_three)]
    apply congrArg eisEmbedding
    apply powerResidueSymbol_congr
    apply Ideal.Quotient.eq.mpr
    apply mem_span_singleton.mpr
    simpa using ray_dvd he (by decide : 2 ∣ 72)
  · rw [(rational_supplements hn).2, (rational_supplements hm).2, norm_ray_congr he (by decide : 8 ∣ 72)]

private lemma sextic_one_num {n : Ideal 𝓔} (hn : AwayFromSix n) : sextic n 1 = 1 := by
  rw [← sexticChar_apply_mk hn, map_one, map_one]

theorem sextic_unit_congr (recip : DunnRadziwillReciprocity) {n m : Ideal 𝓔}
    (hn : AwayFromSix n) (hm : AwayFromSix m)
    (he : Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n) = Ideal.Quotient.mk _ (generator m)) (u : 𝓔ˣ) :
    sextic n u = sextic m u := by
  have pow_neg {a : Ideal 𝓔} (ha : AwayFromSix a) : sextic a (-1) ^ 2 = 1 := by
    rw [← sextic_pow ha]; norm_num [sextic_one_num ha]
  have hneg : sextic n (-1) = sextic m (-1) := eq_of_sq_cube ((pow_neg hn).trans (pow_neg hm).symm) (by
    rw [(rational_supplements hn).1, (rational_supplements hm).1, norm_ray_congr he (by decide : 4 ∣ 72)])
  have h9 : (9 : 𝓔) ∣ generator m - generator n := ray_dvd he.symm (by decide : 9 ∣ 72)
  have hcube : eisOmega^3 = 1 := by linear_combination (eisOmega-1) * omega_rel
  have ho : sextic n eisOmega = sextic m eisOmega := by
    apply eq_of_sq_cube
    · rw [square_cubic hn, square_cubic hm,
        (cubic_supplements_congr recip (eisPrimary_generator hn.coprime_three) h9).2]
    · rw [← sextic_pow hn, ← sextic_pow hm, hcube, sextic_one_num hn, sextic_one_num hm]
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
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

end Masullo.QRH.MeanSquare.ReflectionTwist
