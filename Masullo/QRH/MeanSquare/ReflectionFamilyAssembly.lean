import Masullo.QRH.MeanSquare.ReflectionExtraction
import Masullo.QRH.MeanSquare.ReflectionSquarefreeBound
import Masullo.QRH.MeanSquare.ReflectionRowInversion

/-! # Finite assembly of the reflected squarefree branches -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid
open scoped Classical

namespace Masullo.QRH.MeanSquare.ReflectionSieve

open ReflectionInversion ReflectionRows

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- Active tame table choices at a fixed set of primes. -/
abbrev TameAssignment (j : Idl → ℕ) (F : Finset Idl) :=
  ↥(Fintype.piFinset (fun p : F => TameBranch.activeChoices (j p)))

theorem card_tameAssignment (j : Idl → ℕ) (F : Finset Idl) :
    Fintype.card (TameAssignment j F) ≤ 3 ^ F.card := by
  rw [Fintype.card_coe, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _ : F, (3 : ℕ) := by
      apply prod_le_prod
      intro p _
      by_cases h₄ : j p = 4
      · simp [TameBranch.activeChoices, h₄]
      · by_cases h₀ : j p = 0 <;> simp [TameBranch.activeChoices, h₄, h₀]
    _ = _ := by simp

/-- A selected product of distinct prime divisors divides the original modulus. -/
theorem selected_product_dvd {M : Idl} (hM : M ≠ 0) {A : Finset Idl}
    (hA : A ⊆ (normalizedFactors M).toFinset) : (∏ p ∈ A, p) ∣ M :=
  (prod_dvd_prod_of_subset _ _ id hA).trans
    ((Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hM).dvd)

/-- The varying rows have squarefree good modulus and are coprime to both fixed factors. -/
theorem selected_row_properties {K : ℝ} {G t k : Idl} (ht : t ∣ span {(6 : 𝓔)} * G)
    (hk : k ∈ sieveIdeals (span {(6 : 𝓔)} * G) K) :
    Starred k ∧ IsCoprime k t ∧ IsCoprime k G ∧ k ∈ sieveIdeals (span {(6 : 𝓔)}) K := by
  obtain ⟨hK,hs,hcop⟩ := mem_filter.mp hk
  have h6 := hcop.of_isCoprime_of_dvd_right (dvd_mul_right (span {(6 : 𝓔)}) G)
  exact ⟨⟨⟨hs.ne_zero,h6⟩,hs⟩,hcop.of_isCoprime_of_dvd_right ht,
    hcop.of_isCoprime_of_dvd_right (dvd_mul_left ..),mem_filter.mpr ⟨hK,hs,h6⟩⟩

/-- One fixed local row formula for each class, exceptional frequency and
active set. The raw summand includes its scalar from Fourier inversion. -/
structure RowExpansion (C U : Type*) [Fintype C] [Fintype U]
    (B K X : ℝ) (t G : Idl) (P R : Finset Idl) (W : ℝ → ℂ) (value : Idl → ℂ) where
  classOf : Idl → C
  ray : C → RayResidue 7 → ℂ
  fixedPrimes : Finset Idl
  fixed_subset : fixedPrimes ⊆ P
  exponent : Idl → ℕ
  raw : (c : C) → RaySupport (ray c) → Finset Idl → Idl → ℂ
  inversion : ∀ k ∈ R, value k =
    ∑ h : RaySupport (ray (classOf k)), ∑ F ∈ fixedPrimes.powerset, raw (classOf k) h F k
  converted : ∀ (c : C) (h : RaySupport (ray c)) (F : fixedPrimes.powerset),
    ∃ b : U → Fin 2 → TameAssignment exponent F.val → SquarefreeKernelBranch B K X t G,
      (∀ ν e η, ∀ k ∈ (b ν e η).rows, classOf k = c) ∧
      ∀ k ∈ R, classOf k = c → raw c h F.val k =
        ∑ ν, ∑ e, ∑ η, (b ν e η).rowValue W k

private abbrev BranchIndex {C U : Type*} [Fintype C] [Fintype U]
    {B K X : ℝ} {t G : Idl} {P R : Finset Idl} {W : ℝ → ℂ} {value : Idl → ℂ}
    (r : RowExpansion C U B K X t G P R W value) :=
  (c : C) × ((_h : RaySupport (r.ray c)) × (F : r.fixedPrimes.powerset) ×
    (U × Fin 2 × TameAssignment r.exponent F.val))

private theorem card_branchIndex {C U : Type*} [Fintype C] [Fintype U]
    {B K X : ℝ} {t G : Idl} {P R : Finset Idl} {W : ℝ → ℂ} {value : Idl → ℂ}
    (r : RowExpansion C U B K X t G P R W value) :
    Fintype.card (BranchIndex r) ≤
      (Fintype.card C * Fintype.card (RayResidue 7) * Fintype.card U * 2) * 6 ^ P.card := by
  have hF : ∀ F : r.fixedPrimes.powerset, F.val.card ≤ r.fixedPrimes.card :=
    fun F => card_le_card (mem_powerset.mp F.2)
  have bound (F : r.fixedPrimes.powerset) : Fintype.card (TameAssignment r.exponent F.val) ≤
      3 ^ r.fixedPrimes.card := (card_tameAssignment _ _).trans (Nat.pow_le_pow_right
        (by decide) (hF F))
  let n := Fintype.card U * 2 * 3 ^ r.fixedPrimes.card
  have havg : ∀ c : C, Fintype.card (RaySupport (r.ray c)) ≤ Fintype.card (RayResidue 7) :=
    fun c => Fintype.card_subtype_le _
  have hsum : (∑ F : r.fixedPrimes.powerset, Fintype.card U * (2 *
    Fintype.card (TameAssignment r.exponent F.val)))
      ≤ 2 ^ r.fixedPrimes.card * n := calc
    _ ≤ ∑ _ : r.fixedPrimes.powerset, n := by
      apply sum_le_sum
      intro F _
      dsimp [n]
      rw [Nat.mul_assoc]
      gcongr
      exact bound F
    _ = _ := by simp [card_powerset]
  calc
    _ = ∑ c : C, Fintype.card (RaySupport (r.ray c)) *
        ∑ F : r.fixedPrimes.powerset, Fintype.card U * (2 *
          Fintype.card (TameAssignment r.exponent F.val)) := by
      simp [BranchIndex, Fintype.card_sigma, Fintype.card_prod]
    _ ≤ ∑ _ : C, Fintype.card (RayResidue 7) * (2 ^ r.fixedPrimes.card * n) := by
      apply sum_le_sum
      intro c _
      exact Nat.mul_le_mul (havg c) hsum
    _ = (Fintype.card C * Fintype.card (RayResidue 7) * Fintype.card U * 2) * 6 ^
      r.fixedPrimes.card := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, n]
      rw [show 6 = 2*3 by decide, Nat.mul_pow]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (card_le_card r.fixed_subset))

/-- Flatten the class and local branch sums to the single finite row family of the estimate. -/
theorem RowExpansion.assemble {C U : Type*} [Fintype C] [Fintype U]
    {B K X : ℝ} {t G : Idl} {P R : Finset Idl} {W : ℝ → ℂ} {value : Idl → ℂ}
    (r : RowExpansion C U B K X t G P R W value) :
    ∃ (n : ℕ) (b : Fin n → SquarefreeKernelBranch B K X t G),
      n ≤ (Fintype.card C * Fintype.card (RayResidue 7) * Fintype.card U * 2) * 6 ^ P.card ∧
      ∀ k ∈ R, value k = ∑ i, (b i).rowValue W k := by
  choose b hb he using r.converted
  let bs : BranchIndex r → SquarefreeKernelBranch B K X t G :=
    fun ⟨c,h,F,ν,e,η⟩ => b c h F ν e η
  let eqv := Fintype.equivFin (BranchIndex r)
  refine ⟨_, fun i => bs (eqv.symm i), card_branchIndex r, ?_⟩
  intro k hk
  rw [eqv.symm.sum_comp (fun i => (bs i).rowValue W k)]
  simp only [BranchIndex, Fintype.sum_sigma, Fintype.sum_prod_type, bs]
  rw [Fintype.sum_eq_single (r.classOf k)]
  · rw [r.inversion k hk]
    apply sum_congr rfl
    intro h _
    rw [← sum_finset_coe (fun F => r.raw (r.classOf k) h F k) r.fixedPrimes.powerset]
    exact sum_congr rfl fun F _ => he _ h F k hk rfl
  · intro c hc
    apply sum_eq_zero
    intro h _
    apply sum_eq_zero
    intro F _
    apply sum_eq_zero
    intro ν _
    apply sum_eq_zero
    intro e _
    apply sum_eq_zero
    intro η _
    have hnot : k ∉ (b c h F ν e η).rows := fun hmem => hc ((hb c h F ν e η k hmem).symm)
    simp [SquarefreeKernelBranch.rowValue, hnot]

/-- Increase the uniform budget of a branch without changing its row values. -/
private def SquarefreeKernelBranch.enlarge {B D K X : ℝ} {t G : Idl}
    (b : SquarefreeKernelBranch B K X t G) (hB : 0 ≤ B) (hD : B ≤ D) (hX : 0 ≤ X) :
    SquarefreeKernelBranch D K X t G :=
  { b with
    amplitude := by
      apply b.amplitude.trans
      apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hD 2)
      apply prod_nonneg
      intro p _
      cases b.choice p <;> dsimp [TameBranch.weightSq] <;> positivity
    length := by
      apply b.length.trans
      apply mul_le_mul_of_nonneg_right
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD (sq_nonneg K)) hX
      · apply prod_nonneg
        intro p _
        cases b.choice p <;> dsimp [TameBranch.length] <;> positivity }

/-- An expansion for each squarefree quotient gives the representation consumed
by the large-sieve estimate, with a common constant for branch size and branch count. -/
theorem squarefreeBranchRepresentation_of_rows {C U : Type*} [Fintype C] [Fintype U]
    (hs : ∀ I : TestInterval, ∃ B : ℝ, 1 ≤ B ∧
      ∀ (H X : ℝ) (u : 𝓔ˣ) (g : 𝓔) (ξ : RayCharacter) (W : ℝ → ℂ),
        1 ≤ H → 1 ≤ X → g ≠ 0 → UnitTest I 14 W →
        let G := span {g}
        let P := (normalizedFactors (span {(6 : 𝓔)} * G)).toFinset
        ∀ A ⊆ P, let t := ∏ p ∈ A, p
          let K := H / absNorm t
          1 ≤ K → Nonempty (RowExpansion C U B K X t G P (sieveIdeals (span {(6 : 𝓔)} * G) K) W
            (fun k => completedAtElement ξ W X ((u : 𝓔) * generator (t*k)) g))) :
    SquarefreeBranchRepresentation := by
  intro I
  obtain ⟨B,hB,hs⟩ := hs I
  let N := Fintype.card C * Fintype.card (RayResidue 7) * Fintype.card U * 2
  refine ⟨max B (N : ℝ), hB.trans (le_max_left ..), ?_⟩
  intro H X u g ξ W hH hX hg hW
  dsimp only
  intro A hA hK
  obtain ⟨r⟩ := hs H X u g ξ W hH hX hg hW A hA hK
  obtain ⟨n,b,hn,hrow⟩ := r.assemble
  refine ⟨n, fun i => (b i).enlarge (zero_le_one.trans hB) (le_max_left ..)
    (zero_le_one.trans hX), ?_, hrow⟩
  have hn' : (n : ℝ) ≤ (N : ℝ) * 6 ^ ((normalizedFactors (span {(6:𝓔)} *
    span {g})).toFinset.card) := by
    exact_mod_cast hn
  exact hn'.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))

open ReflectionRowInversion

@[instance_reducible] def reflectedUnitFintype : Fintype 𝓔ˣ := by
  let : Finite 𝓔ˣ := Finite.of_injective (fun u : 𝓔ˣ => ((u,1,0) : RowClass))
    (fun _ _ h => congrArg Prod.fst h)
  exact Fintype.ofFinite _

attribute [local instance] reflectedUnitFintype

/-- Converting one fixed active set to dyadic kernel branches. Its family of
coefficients on the squarefree rows is bounded independently of the column. -/
def FixedBranchConversion (τ : ℂ → ℂ) : Prop :=
  ∀ I : TestInterval, ∃ B : ℝ, 1 ≤ B ∧
  ∀ {K X : ℝ} {W : ℝ → ℂ}, 1 ≤ K → 1 ≤ X → UnitTest I 14 W →
  ∀ {t y T G : Idl}, t ≠ 0 → y ≠ 0 → AwayFromSix T → AwayFromSix G → T ∣ t → G ∣ y →
  ∀ {h : RayResidue 7} (D : FixedCusp h) (r : ReflectionCRT.Residue (72*eisLambda^7))
    (F : Finset Idl), F ⊆ support (T*G) →
  ∀ (R : Finset Idl) (q : QuadraticFamilyClass) (a : Idl → ℂ)
    (hR : ∀ k ∈ R, k ∈ sieveIdeals (span {(6 : 𝓔)}) K ∧ Starred k ∧
      IsCoprime k t ∧ IsCoprime k y ∧ familyClass k = q ∧ ‖a k‖ ≤ 1 + Fintype.card (RayResidue 7)),
    ∃ b : 𝓔ˣ → Fin 2 → TameAssignment (fun p => exponent T G p % 6) F →
      SquarefreeKernelBranch B K X t y,
      (∀ ν e η, (b ν e η).rows ⊆ R) ∧
      ∀ k (hk : k ∈ R), a k * branchSum D r T G F (hR k hk).2.1.1 τ W X =
        ∑ ν, ∑ e, ∑ η, (b ν e η).rowValue W k

/-- The fixed-active-set conversion and the completed row inversion imply the
squarefree branch representation, including its uniform cardinality bound. -/
theorem squarefreeBranchRepresentation_of_conversion {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (he : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ)
    (hχ : PattersonAutomorphyWith pattersonMultiplier θ) (hB : DLMFBesselMellin)
      (hΓ : DLMFGammaVertical)
    (hR : DunnRadziwillReciprocity) (quad : DeloupTuraevTheorem1) (conv : FixedBranchConversion τ) :
    SquarefreeBranchRepresentation := by
  let : Fintype RowClass := Fintype.ofFinite _
  apply squarefreeBranchRepresentation_of_rows (C := RowClass) (U := 𝓔ˣ)
  intro I
  obtain ⟨B,hB₁,hconv⟩ := conv I
  refine ⟨B,hB₁,?_⟩
  intro H X u g ξ W _hH hX hg hW
  dsimp only
  intro A hA
  let y := span {g}
  let M := span {(6 : 𝓔)}*y
  let t := ∏ p ∈ A, p
  let K := H / absNorm t
  let R := sieveIdeals M K
  have hy : y ≠ 0 := mt span_singleton_eq_bot.mp hg
  have hM : M ≠ 0 := mul_ne_zero (by simp) hy
  have htM : t ∣ M := selected_product_dvd hM hA
  have ht₀ : t ≠ 0 := ne_zero_of_dvd_ne_zero hM htM
  intro hK
  obtain ⟨T,G,cl,hT,hG,hTt,hGy,hcl,hI⟩ := completed_row_inversion he ht hχ hB hΓ hR quad ξ u ht₀ hg
  let R₀ (c : RowClass) := R.filter (fun k => cl k = c)
  have hrow {c : RowClass} {k : Idl} (hk : k ∈ R₀ c) := selected_row_properties htM
    (mem_filter.mp hk).1
  choose φ hφ hI using hI
  have hc (c : RowClass) (k : R₀ c) := hI c (hrow k.2).1 (hrow k.2).2.1
    (hrow k.2).2.2.1 (mem_filter.mp k.2).2
  choose coeff hcoeff hEq using hc
  let raw (c : RowClass) (h : RaySupport (φ c)) (F : Finset Idl) (k : Idl) :=
    if hk : k ∈ R₀ c then coeff c ⟨k,hk⟩ h F *
      branchSum (fixedCusp (hφ c) h) c.2.2 T G F (hrow hk).1.1 τ W X else 0
  refine ⟨⟨cl, φ, support (T*G), ?_, (fun p => exponent T G p % 6), raw, ?_, ?_⟩⟩
  · have hs := fixedSupport_subset ht₀ hy hTt hGy
    intro p hp
    have hdiv : p ∣ M := (mem_union.mp (hs hp)).elim
      (fun h => (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp h)).trans htM)
      (fun h => (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp h)).trans (dvd_mul_left ..))
    exact Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hM).mpr
      ⟨prime_of_normalized_factor _ (Multiset.mem_toFinset.mp hp),hdiv⟩)
  · intro k hk
    have hk' : k ∈ R₀ (cl k) := mem_filter.mpr ⟨hk,rfl⟩
    simpa only [raw, hk', ↓reduceDIte] using hEq (cl k) ⟨k,hk'⟩ (hW.of_le (by decide : 6 ≤ 14))
      (zero_lt_one.trans_le hX)
  · intro c h F
    let a (k : Idl) : ℂ := if hk : k ∈ R₀ c then coeff c ⟨k,hk⟩ h F.val else 0
    have ha (k : Idl) (hk : k ∈ R₀ c) : a k = coeff c ⟨k,hk⟩ h F.val := by simp [a,hk]
    have hRows (k : Idl) (hk : k ∈ R₀ c) :
        k ∈ sieveIdeals (span {(6 : 𝓔)}) K ∧ Starred k ∧ IsCoprime k t ∧ IsCoprime k y ∧
        familyClass k = c.2.1 ∧ ‖a k‖ ≤ 1 + Fintype.card (RayResidue 7) := by
      have hck := (mem_filter.mp hk).2
      have hclass := congrArg Prod.fst ((hcl k).symm.trans (congrArg Prod.snd hck))
      exact ⟨(hrow hk).2.2.2,(hrow hk).1,(hrow hk).2.1,(hrow hk).2.2.1,hclass,
        ha k hk ▸ hcoeff c ⟨k,hk⟩ h F.val⟩
    obtain ⟨b,hb,hbEq⟩ := hconv hK hX hW ht₀ hy hT hG hTt hGy (fixedCusp (hφ c) h) c.2.2 F.val
      (mem_powerset.mp F.2) (R₀ c) c.2.1 a hRows
    refine ⟨b,fun ν e η k hk => (mem_filter.mp (hb ν e η hk)).2,?_⟩
    intro k hk hc
    have hk' : k ∈ R₀ c := mem_filter.mpr ⟨hk,hc⟩
    simpa only [raw, hk', ↓reduceDIte, ha k hk'] using hbEq k hk'

end Masullo.QRH.MeanSquare.ReflectionSieve
