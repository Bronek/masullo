import Masullo.QRH.MeanSquare.OffDiagonal

/-!
# The nonzero dual frequencies

Steps toward `DualTailEstimate rowMajorant` from `GapEstimate`.

* `exists_rayCharacter_expansion`: a function on pairs of residues modulo `72` is, on pairs of
  units, a combination of `ξ(x) conj η(y)` over ray characters `ξ, η`.
-/

noncomputable section

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

local notation "Q₇₂" => 𝓔 ⧸ span {(72 : 𝓔)}

/-! ### Ray characters separate units -/

instance : Finite Q₇₂ :=
  (Ideal.absNorm_ne_zero_iff _).mp (Ideal.absNorm_eq_zero_iff.not.mpr
    (span_singleton_eq_bot.not.mpr (by norm_num)))

instance : Fintype Q₇₂ := Fintype.ofFinite _

instance : Fintype RayCharacter := Fintype.ofFinite _

lemma sum_rayCharacter_apply (u : Q₇₂ˣ) : open Classical in
    ∑ ξ : RayCharacter, ξ u = if u = 1 then (Fintype.card RayCharacter : ℂ) else 0 := by
  classical
  split_ifs with hu
  · simp [hu]
  · obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q₇₂ ℂ
      (a := (u : Q₇₂)) (by simpa [Units.val_eq_one] using hu)
    have h : ∑ ξ : RayCharacter, ξ u = χ u * ∑ ξ : RayCharacter, ξ u := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft χ) (fun ξ : RayCharacter => χ u * ξ u)
        (fun ξ : RayCharacter => ξ u) fun ξ => by simp).symm
    have : (1 - χ u) * ∑ ξ : RayCharacter, ξ u = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hχ))

lemma sum_rayCharacter_mul_conj (u v : Q₇₂ˣ) : open Classical in
    ∑ ξ : RayCharacter, ξ u * conj (ξ v) =
      if u = v then (Fintype.card RayCharacter : ℂ) else 0 := by
  classical
  have h : ∀ ξ : RayCharacter, ξ u * conj (ξ v) = ξ ↑(u * v⁻¹) := fun ξ => by
    rw [← RCLike.star_def, MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
      Units.val_mul, map_mul]
  simp_rw [h, sum_rayCharacter_apply, mul_inv_eq_one]

/-- A function on pairs of residues is, on pairs of units, a combination of products of ray
characters. -/
theorem exists_rayCharacter_expansion (A : Q₇₂ → Q₇₂ → ℂ) :
    ∃ α : RayCharacter → RayCharacter → ℂ, ∀ x y : Q₇₂, IsUnit x → IsUnit y →
      A x y = ∑ ξ : RayCharacter, ∑ η : RayCharacter, α ξ η * ξ x * conj (η y) := by
  classical
  set N : ℂ := (Fintype.card RayCharacter : ℂ)
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun ξ η => (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ * conj (ξ x₀) * η y₀) / N ^ 2,
    fun x y hx hy => ?_⟩
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have hexp : ∑ ξ : RayCharacter, ∑ η : RayCharacter,
      (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ * conj (ξ x₀) * η y₀) / N ^ 2 * ξ u * conj (η v) =
      (∑ x₀ : Q₇₂ˣ, ∑ y₀ : Q₇₂ˣ, A x₀ y₀ *
        (∑ ξ : RayCharacter, ξ u * conj (ξ x₀)) *
        (∑ η : RayCharacter, η y₀ * conj (η v))) / N ^ 2 := by
    have h4 : ∀ f : RayCharacter → RayCharacter → Q₇₂ˣ → Q₇₂ˣ → ℂ,
        ∑ ξ, ∑ η, ∑ x, ∑ y, f ξ η x y = ∑ x, ∑ y, ∑ ξ, ∑ η, f ξ η x y := by
      intro f
      calc _ = ∑ ξ, ∑ x, ∑ η, ∑ y, f ξ η x y := Finset.sum_congr rfl fun ξ _ => Finset.sum_comm
        _ = ∑ ξ, ∑ x, ∑ y, ∑ η, f ξ η x y := Finset.sum_congr rfl fun ξ _ =>
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ x, ∑ ξ, ∑ y, ∑ η, f ξ η x y := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine (h4 _).trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ξ _ => ?_))
    ring
  rw [hexp]
  simp_rw [sum_rayCharacter_mul_conj]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  field_simp
  rfl

/-- The primary generator of an ideal prime to six is a unit modulo `72`. -/
lemma isUnit_mk_generator {n : Ideal 𝓔} (hn : AwayFromSix n) :
    IsUnit (Ideal.Quotient.mk (span {(72 : 𝓔)}) (generator n)) := by
  rw [isUnit_mk_iff_coprime_span, span_generator]
  have h3 : IsCoprime (span {(6 : 𝓔)} ^ 3) n := (hn.2.symm.pow_left)
  rw [span_singleton_pow, Ideal.isCoprime_iff_sup_eq] at h3
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← h3]
  refine sup_le_sup_right (span_singleton_le_span_singleton.mpr ⟨3, by norm_num⟩) _

end Masullo.QRH.MeanSquare
