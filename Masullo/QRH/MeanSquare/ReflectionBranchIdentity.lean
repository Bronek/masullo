import Masullo.QRH.MeanSquare.ReflectionIdealBranches

/-! # The finite tame expansion of one row of the reflected Patterson series -/

noncomputable section

open NumberField Ideal Finset Complex
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare.ReflectionSieve

open TameBranch ReflectionVaryingRows ReflectionInversion

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- One assignment of exceptional prime factors in an ideal-indexed frequency. -/
def pieceProduct (F : Finset Idl) (j : Idl → ℕ) (e : F → TameBranch) (x : ReflectedIndex) : ℂ :=
  ∏ p : F, idealPiece p (j p) (e p) x.numerator x.n x.b

def indexTerm (τ : ℂ → ℂ) (W : ℝ → ℂ) (X : ℝ) (c : 𝓔) (ψ : 𝓔 → ℂ) {k : Idl}
    (hk : AwayFromSix k) (F : Finset Idl) (j : Idl → ℕ) (e : F → TameBranch)
      (x : ReflectedIndex) : ℂ :=
  (ψ x.numerator * pieceProduct F j e x) * quadraticResidue hk x.numerator *
    dualMode τ W X c x.numerator

theorem norm_quadratic_le {k : Idl} (hk : AwayFromSix k) (m : 𝓔) :
    ‖quadraticResidue hk m‖ ≤ 1 := by
  by_cases h : IsCoprime k (span {m})
  · rcases sq_eq_one_iff.mp (quadraticResidue_sq hk h) with e|e <;> simp [e]
  · have hz : quadraticResidue hk m = 0 := by_contra fun h' =>
      h ((quadraticResidue_ne_zero hk).mp h')
    simp [hz]

set_option maxHeartbeats 600000 in
private theorem summable_indexTerm {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (hΓ : DLMFGammaVertical)
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 6 W) {X : ℝ} (hX : 0 < X) {c : 𝓔} (hc : c ≠ 0)
    {ψ : 𝓔 → ℂ} (hψ : ∀ m, ‖ψ m‖ ≤ 1) {k : Idl} (hk : AwayFromSix k)
    (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p) (j : Idl → ℕ)
    (e : F → TameBranch) (he : ∀ p : F, e p ∈ activeChoices (j p)) :
    Summable (indexTerm τ W X c ψ hk F j e) := by
  let f (x : ReflectedIndex) : {m : 𝓔 // m ≠ 0} := ⟨x.numerator,x.numerator_ne⟩
  have hf : Function.Injective f := fun _ _ he => ReflectedIndex.numerator_injective
    (congrArg Subtype.val he)
  have hc' := (map_ne_zero_iff eisEmbedding eisEmbedding_injective).mpr hc
  have hdu := (ht.summable_smoothed_dual hΓ hW 0 hX (show 0 <
    ‖eisEmbedding c‖^2 by positivity)).comp_injective hf
  let a := Real.sqrt (∏ p : F, (e p).weightSq (absNorm p.val))
  let D := Real.sqrt (absNorm (extractedN F e)) * (absNorm (extractedB F e) : ℝ)
  have hcop := extracted_coprime F e (fun p hp => (hF p hp).1)
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr (zero_lt_one.trans_le (absNorm_one_le hcop.1.1)))
    (zero_lt_one.trans_le (absNorm_one_le hcop.2.1))
  apply (hdu.mul_left (a*D)).of_norm_bounded
  intro x
  have hpiece : ‖pieceProduct F j e x‖ ≤ a*D := (div_le_iff₀ hD).mp
    (idealPiece_product_bound F hF j e he x)
  change ‖indexTerm τ W X c ψ hk F j e x‖ ≤ (a*D)*‖dualMode τ W X c x.numerator‖
  simp only [indexTerm,norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ (1*(a*D))*1 := mul_le_mul (mul_le_mul (hψ _) hpiece (norm_nonneg _) zero_le_one)
      (norm_quadratic_le hk _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Expand the fixed active primes after the reflected lattice has been
reindexed. The unit and the factor above two have finite ranges. -/
theorem split_dual_row {τ : ℂ → ℂ} (ht : PattersonCoefficients τ) (hΓ : DLMFGammaVertical)
    {J : TestInterval} {W : ℝ → ℂ} (hW : UnitTest J 6 W) {X : ℝ} (hX : 0 < X) {c : 𝓔} (hc : c ≠ 0)
    {ψ : 𝓔 → ℂ} (hψ : ∀ m, ‖ψ m‖ ≤ 1) {k : Idl} (hk : AwayFromSix k)
    (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p) (j : Idl → ℕ) :
    (∑' m : {m : 𝓔 // m ≠ 0}, (ψ m * ∏ p ∈ F, reflectedFactor p (j p) m) *
      quadraticResidue hk m * dualMode τ W X c m) =
    ∑ e ∈ Fintype.piFinset (fun p : F => activeChoices (j p)), ∑' u : 𝓔ˣ, ∑ i : Fin 2,
      ∑' z : ℕ × Idl × Idl, extendIndex (indexTerm τ W X c ψ hk F j e) u i z.1 z.2.1 z.2.2 := by
  classical
  let g (x : ReflectedIndex) : {m : 𝓔 // m ≠ 0} := ⟨x.numerator,x.numerator_ne⟩
  have hg : Function.Injective g := fun _ _ he => ReflectedIndex.numerator_injective
    (congrArg Subtype.val he)
  let A (m : {m : 𝓔 // m ≠ 0}) := (ψ m * ∏ p ∈ F, reflectedFactor p (j p) m) *
    quadraticResidue hk m * dualMode τ W X c m
  have hs (e) (he : e ∈ Fintype.piFinset (fun p : F => activeChoices (j p))) :=
    summable_indexTerm ht hΓ hW hX hc hψ hk F hF j e (Fintype.mem_piFinset.mp he)
  have hr : ∑' m, A m = ∑' x, A (g x) := by
    apply (hg.tsum_eq ?_).symm
    intro m hm
    have ht' : τ (pattersonFrequency m.val) ≠ 0 := fun hh => hm (by
      simp [A,dualMode,pattersonAngularCoefficient,hh])
    obtain ⟨r,neg,he⟩ := ReflectedIndex.exists_signed_row ht ht'
    exact ⟨ReflectedIndex.ofRow r neg,Subtype.ext he⟩
  apply hr.trans
  calc
    _ = ∑' x, ∑ e ∈ Fintype.piFinset (fun p : F => activeChoices (j p)),
      indexTerm τ W X c ψ hk F j e x := by
      apply tsum_congr
      intro x
      dsimp only [A,g,indexTerm,pieceProduct]
      rw [reflected_product_eq_choices F hF j x,mul_sum,sum_mul,sum_mul]
    _ = _ := (Summable.tsum_finsetSum hs).trans (sum_congr rfl fun e he =>
      tsum_split_index _ (hs e he))

/-- The extraction can be made after disjointly splitting off the prime above
two. A nonzero coefficient forces all selected prime divisors to occur. -/
theorem extract_indexTerm (τ : ℂ → ℂ) (W : ℝ → ℂ) (X : ℝ) (c : 𝓔) (ψ : 𝓔 → ℂ) {k : Idl}
    (hk : AwayFromSix k) (F : Finset Idl) (hF : ∀ p ∈ F, AwayFromSix p ∧ Prime p) (j : Idl → ℕ)
    (e : F → TameBranch) (u : 𝓔ˣ) (i : Fin 2) :
    let f := extendIndex (indexTerm τ W X c ψ hk F j e) u i
    (∑' z : ℕ × Idl × Idl, f z.1 z.2.1 z.2.2) =
      ∑' z : ReflectedColumns, f z.1 (extractedB F e*z.2.1.val) (extractedN F e*z.2.2.val) := by
  classical
  let N := extractedN F e
  let B := extractedB F e
  have hcop := extracted_coprime F e (fun p hp => (hF p hp).1)
  let g (z : ReflectedColumns) := (z.1,B*z.2.1.val,N*z.2.2.val)
  have hinj : Function.Injective g := by
    rintro ⟨h,⟨b,_⟩,⟨n,_⟩⟩ ⟨h',⟨b',_⟩,⟨n',_⟩⟩ he
    have hh := congrArg (fun z : ℕ × Idl × Idl => z.1) he
    have hb := congrArg (fun z : ℕ × Idl × Idl => z.2.1) he
    have hn := congrArg (fun z : ℕ × Idl × Idl => z.2.2) he
    exact Prod.ext hh (Prod.ext (Subtype.ext (mul_left_cancel₀ hcop.2.1 hb)) (Subtype.ext
      (mul_left_cancel₀ hcop.1.1 hn)))
  apply (hinj.tsum_eq ?_).symm
  rintro ⟨h,b,n⟩ hz
  change extendIndex _ u i h b n ≠ 0 at hz
  rw [extendIndex] at hz
  split at hz
  next hs =>
    have hx := left_ne_zero_of_mul (left_ne_zero_of_mul hz)
    have hp := idealPiece_product_dvd F hF j e _ _ _ (right_ne_zero_of_mul hx)
    have h₂ : IsCoprime N (twoPart i) := by
      apply IsCoprime.pow_right
      apply hcop.1.2.of_isCoprime_of_dvd_right
      apply span_singleton_dvd_span_singleton_iff_dvd.mpr
      exact ⟨-3,by norm_num⟩
    obtain ⟨n',hn'⟩ := h₂.dvd_of_dvd_mul_left hp.1
    obtain ⟨b',hb'⟩ := hp.2
    have hn : Starred n' := by
      have hd : n' ∣ n := hn' ▸ dvd_mul_left ..
      exact ⟨⟨ne_zero_of_dvd_ne_zero hs.2.2.2.1.1 hd,hs.2.2.2.1.2.of_isCoprime_of_dvd_left hd⟩,
        hs.2.2.2.2.squarefree_of_dvd hd⟩
    have hb : b' ≠ 0 := by
      intro he
      have hb₀ : b = 0 := by simpa [he] using hb'
      exact (eisPrimary_generator hs.2.2.1).ne_zero
        (span_singleton_eq_bot.mp ((span_generator b).trans hb₀))
    exact ⟨(h,⟨b',hb⟩,⟨n',hn⟩),Prod.ext rfl (Prod.ext hb'.symm hn'.symm)⟩
  next => exact (hz rfl).elim

end Masullo.QRH.MeanSquare.ReflectionSieve
