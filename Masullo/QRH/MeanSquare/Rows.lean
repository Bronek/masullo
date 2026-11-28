import Masullo.QRH.StageB

/-! # Finite element rows over the Eisenstein integers -/

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

local notation "K₃" => CyclotomicField 3 ℚ
local notation "𝓔" => 𝓞 K₃

private instance : IsCyclotomicExtension {3} ℚ K₃ :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private instance : IsPrincipalIdealRing 𝓔 := IsCyclotomicExtension.Rat.three_pid K₃

/-- Choose the primary generator when one exists. The fallback is used for ideals
outside the primary classes. -/
noncomputable def generator (a : Ideal 𝓔) : 𝓔 := by
  classical
  exact if h : ∃ x : 𝓔, span {x} = a ∧ (3 : 𝓔) ∣ x - 1 then h.choose
    else Submodule.IsPrincipal.generator a

lemma span_generator (a : Ideal 𝓔) : span {generator a} = a := by
  classical
  unfold generator
  split
  next h => exact h.choose_spec.1
  · exact Ideal.span_singleton_generator a

/-- The element norm, expressed through the index of the principal ideal. -/
noncomputable def elementNorm (k : 𝓔) : ℕ := absNorm (span {k})

private instance finite_units : Finite 𝓔ˣ := by
  classical
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K₃
  let η := (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  let units : List 𝓔ˣ := [1, -1, η, -η, η ^ 2, -η ^ 2]
  let _ : Fintype 𝓔ˣ := ⟨units.toFinset, fun u =>
    List.mem_toFinset.mpr (IsCyclotomicExtension.Rat.Three.Units.mem hζ u)⟩
  infer_instance

/-- All nonzero elements of norm at most `K`, including every associate. -/
noncomputable def elementRows (K : ℝ) : Finset 𝓔 := by
  classical
  letI := Fintype.ofFinite 𝓔ˣ
  exact ((idealsLe K).erase ⊥).biUnion fun a =>
    Finset.univ.image fun u : 𝓔ˣ => generator a * u

lemma card_elementRows_le (K : ℝ) : (elementRows K).card ≤ (idealsLe K).card * Nat.card 𝓔ˣ := by
  classical
  let := Fintype.ofFinite 𝓔ˣ
  unfold elementRows
  refine (Finset.card_biUnion_le_card_mul _ _ (Nat.card 𝓔ˣ) (fun a _ => ?_)).trans
    (Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset ..)))
  simpa only [Nat.card_eq_fintype_card, Finset.card_univ] using
    (Finset.card_image_le (s := (Finset.univ : Finset 𝓔ˣ)) (f := fun u => generator a * (u : 𝓔)))

lemma mem_elementRows {K : ℝ} (hK : 0 ≤ K) {k : 𝓔} :
    k ∈ elementRows K ↔ k ≠ 0 ∧ (elementNorm k : ℝ) ≤ K := by
  classical
  unfold elementRows
  simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_image, Finset.mem_univ,
    true_and, mem_idealsLe hK]
  constructor
  · rintro ⟨a, ⟨ha, hN⟩, u, rfl⟩
    have hspan : span {generator a * (u : 𝓔)} = a :=
      (span_singleton_eq_span_singleton.mpr (show Associated (generator a) _ from
        ⟨u, rfl⟩)).symm.trans (span_generator a)
    refine ⟨fun h => ha ?_, ?_⟩
    · simpa [h] using hspan.symm
    · simpa only [elementNorm, hspan] using hN
  · rintro ⟨hk, hN⟩
    exact ⟨span {k}, ⟨by simpa using hk, hN⟩,
      span_singleton_eq_span_singleton.mp (span_generator (span {k}))⟩

lemma prime_generator {p : Ideal 𝓔} (hp : p.IsPrime) (hp₀ : p ≠ ⊥) : Prime (generator p) := by
  have h : generator p ≠ 0 := fun he => hp₀ (by simpa [he] using (span_generator p).symm)
  exact (span_singleton_prime h).mp ((span_generator p).symm ▸ hp)

/-- Distinct nonzero prime ideals give distinct sixth-power rows. -/
lemma sixthRow_injective (Y : ℝ) :
    Function.Injective (fun p : primesUpTo Y => generator p.1 ^ 6) := by
  intro p q hpq
  have hp := prime_generator p.property.1 p.property.2.1
  have hq := prime_generator q.property.1 q.property.2.1
  change generator p.1 ^ 6 = generator q.1 ^ 6 at hpq
  have hd : generator p.1 ∣ generator q.1 := hp.dvd_of_dvd_pow (n := 6)
    (by rw [← hpq]; exact dvd_pow (dvd_refl _) (by decide : 6 ≠ 0))
  exact Subtype.ext ((span_generator p.1).symm.trans
    ((span_singleton_eq_span_singleton.mpr (hp.associated_of_dvd hq hd)).trans (span_generator q.1)))

/-- Select the prime sixth powers from the finite nonnegative square sum on the disk. -/
theorem primeSixthRows_le {D : ℝ} (hD : 0 < D) (v : 𝓔 → ℂ) :
    ∑' p : primesUpTo (D ^ (1 / 6 : ℝ)), ‖v (generator p.1 ^ 6)‖ ^ 2 ≤
      ∑ k ∈ elementRows D, ‖v k‖ ^ 2 := by
  classical
  let Y := D ^ (1 / 6 : ℝ)
  have hY : 0 ≤ Y := Real.rpow_nonneg hD.le _
  have hfin : (primesUpTo Y).Finite :=
    (idealsLe Y).finite_toSet.subset (fun p hp => (mem_idealsLe hY).mpr hp.2.2.2)
  let := hfin.fintype
  let row := fun p : primesUpTo Y => generator p.1 ^ 6
  have hrow (p : primesUpTo Y) : row p ∈ elementRows D := by
    apply (mem_elementRows hD.le).mpr
    refine ⟨pow_ne_zero _ (prime_generator p.property.1 p.property.2.1).ne_zero, ?_⟩
    change (absNorm (span {generator p.1 ^ 6}) : ℝ) ≤ D
    rw [← span_singleton_pow, span_generator, map_pow, Nat.cast_pow]
    calc (absNorm p.1 : ℝ) ^ 6 ≤ Y ^ 6 := by gcongr; exact p.property.2.2.2
      _ = D := by rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]; norm_num
  rw [tsum_fintype]
  change ∑ p : primesUpTo Y, ‖v (row p)‖ ^ 2 ≤ _
  rw [← Finset.sum_image (f := fun k => ‖v k‖ ^ 2) (sixthRow_injective Y).injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
  exact Finset.image_subset_iff.mpr fun p _ => hrow p

end Masullo.QRH.MeanSquare
