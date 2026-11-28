import Masullo.QRH.MeanSquare.ReflectionMellin
import Masullo.QRH.MeanSquare.ReflectionDecay

/-! # Mellin transform of the differentiated Patterson series -/

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

/-- Horizontal derivative term for Fourier frequency `l` and coefficient `a`. -/
def horizontalMode (l a : ℂ) (v : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I * conj l * a) * (v * besselK (1/3) (4 * Real.pi * ‖l‖ * v))

private theorem horizontalMode_integral_norm (s : ℂ) {l : ℂ} (hl : l ≠ 0) (a : ℂ) :
    (∫ v : ℝ in Ioi 0, ‖(v : ℂ) ^ (2*s-1) * horizontalMode l a v‖) =
      (2 * Real.pi * ∫ v : ℝ in Ioi 0, v ^ (2*s.re) * ‖besselK (1/3) (4 * Real.pi * v)‖) *
        (‖a‖ * (normSq l) ^ (-s.re)) := by
  let r := ‖l‖
  let F := fun v : ℝ => v ^ (2*s.re) * ‖besselK (1/3) (4 * Real.pi * v)‖
  have hr : 0 < r := norm_pos_iff.mpr hl
  have hnr : (normSq l) ^ (-s.re) = r ^ (-(2*s.re)) := by
    rw [normSq_eq_norm_sq, ← Real.rpow_two, ← Real.rpow_mul hr.le, mul_neg]
  have hi : (∫ v : ℝ in Ioi 0, ‖(v : ℂ) ^ (2*s-1) * horizontalMode l a v‖) =
      ∫ v : ℝ in Ioi 0, (2 * Real.pi * r * ‖a‖ * r ^ (-(2*s.re))) * F (r*v) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hv' : 0 < v := hv
    dsimp only [horizontalMode, F]
    simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos hv', sub_re, show (2*s).re =
      s.re+s.re by simp [two_mul], one_re,
      norm_real, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hv'.le,
      norm_I, mul_one, norm_conj, norm_ofNat, Real.mul_rpow hr.le hv'.le]
    rw [Real.rpow_neg hr.le, Real.rpow_sub_one hv'.ne', show 4*Real.pi*(r*v) =
      4*Real.pi*‖l‖*v by dsimp [r]; ring]
    dsimp only [r]
    field_simp [hv'.ne', (Real.rpow_pos_of_pos hr _).ne']
    ring_nf
  rw [hi, integral_const_mul, integral_comp_mul_left_Ioi F 0 hr, mul_zero, hnr]
  simp only [smul_eq_mul, F]
  field_simp [hr.ne']

/-- Absolute convergence of the weighted Dirichlet series justifies termwise Mellin
transformation of the differentiated Fourier expansion. -/
theorem mellin_tsum_horizontalMode {ι : Type*} [Countable ι] (h : DLMFBesselMellin)
    {s : ℂ} (hs : -(1 / 3 : ℝ) < s.re) (l a : ι → ℂ) (hl : ∀ i, l i ≠ 0)
    (ha : Summable fun i => ‖a i‖ * normSq (l i) ^ (-s.re)) :
    mellin (fun v => ∑' i, horizontalMode (l i) (a i) v) (2*s) =
      I / 4 * reflectionGammaFactor s *
        ∑' i, a i * (conj (l i) / ‖l i‖) * (normSq (l i) : ℂ) ^ (-s) := by
  let F := fun (i : ι) (v : ℝ) => (v : ℂ) ^ (2*s-1) * horizontalMode (l i) (a i) v
  have hMode (i : ι) := hasMellin_horizontalMode h hs (hl i) (a i)
  have hInt (i : ι) : IntegrableOn (F i) (Ioi 0) := (hMode i).1
  have hSum : Summable fun i => ∫ v : ℝ in Ioi 0, ‖F i v‖ := by
    simpa only [F, horizontalMode_integral_norm s (hl _) ] using
      ha.mul_left (2 * Real.pi * ∫ v : ℝ in Ioi 0, v ^ (2*s.re) * ‖besselK (1/3) (4 * Real.pi * v)‖)
  calc
    _ = ∫ v : ℝ in Ioi 0, ∑' i, F i v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      simp only [F, tsum_mul_left, smul_eq_mul]
    _ = ∑' i, ∫ v : ℝ in Ioi 0, F i v := (integral_tsum_of_summable_integral_norm hInt hSum).symm
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro i
      exact (hMode i).2.trans (by ring)


open NumberField
local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

private abbrev RowIndex := (Bool × Fin 3) × ℕ × 𝓔 × 𝓔

private def rowWeight (σ : ℝ) (k : RowIndex) : ℝ :=
  3 ^ (((k.2.1 : ℝ) - 3) * (1/6 - σ)) *
    (‖eisEmbedding k.2.2.1‖ ^ (-2*σ) * ‖eisEmbedding k.2.2.2‖ ^ (1-6*σ))

private def tag (r : PattersonRow) (neg : Bool) : RowIndex :=
  ((neg, match r.layer with | .unshifted _ => 0 | .shifted _ i => i),
    r.layer.lambdaExponent, r.c, r.d)

private def decodeRow (k : RowIndex) : 𝓔 :=
  let m := eisLambda ^ k.2.1 * (eisOmega ^ (k.1.2 : ℕ) * k.2.2.1 * k.2.2.2 ^ 3)
  if k.1.1 then -m else m

private theorem decodeRow_tag (r : PattersonRow) (neg : Bool) :
    decodeRow (tag r neg) = if neg then -r.numerator else r.numerator := by
  cases r with
  | mk layer c d hc hd hs =>
    cases layer <;> cases neg <;>
      simp [tag, decodeRow, PattersonRow.numerator, PattersonLayer.unitFactor]

private theorem summable_embedding_rpow {p : ℝ} (hp : p < -2) :
    Summable fun m : 𝓔 => ‖eisEmbedding m‖ ^ p := by
  have hl : eisEmbedding eisLambda ≠ 0 :=
    fun h => eisLambda_prime.ne_zero (eisEmbedding_injective (h.trans (map_zero _).symm))
  have h := (summable_pattersonFrequency_rpow hp).mul_right (‖eisEmbedding eisLambda ^ 3‖ ^ p)
  refine h.congr fun m => ?_
  rw [pattersonFrequency, norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _),
    div_mul_cancel₀ _ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (pow_ne_zero _ hl)) _).ne']


private theorem summable_layerWeight {σ : ℝ} (hs : 1 < σ) :
    Summable fun k : ℕ => (3 : ℝ) ^ (((k : ℝ) - 3) * (1/6 - σ)) := by
  let q := (1/6 - σ)
  have hq : q < 0 := by dsimp [q]; linarith
  have hg := summable_geometric_of_lt_one (r := (3:ℝ)^q) (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hq)
  refine (hg.mul_left ((3:ℝ)^(-3*q))).congr fun k => ?_
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3), ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  dsimp [q]
  ring

private theorem summable_cdWeight {σ : ℝ} (hs : 1 < σ) :
    Summable fun k : 𝓔 × 𝓔 =>
      ‖eisEmbedding k.1‖ ^ (-2*σ) * ‖eisEmbedding k.2‖ ^ (1-6*σ) := by
  let F := fun c : 𝓔 => ‖eisEmbedding c‖ ^ (-2*σ)
  let G := fun d : 𝓔 => ‖eisEmbedding d‖ ^ (1-6*σ)
  change Summable fun k : 𝓔 × 𝓔 => F k.1 * G k.2
  have hF : Summable F := summable_embedding_rpow (by linarith : -2*σ < -2)
  have hG : Summable G := summable_embedding_rpow (by linarith : 1-6*σ < -2)
  have h₁ : 0 ≤ F := fun c => Real.rpow_nonneg (norm_nonneg (eisEmbedding c)) _
  have h₂ : 0 ≤ G := fun d => Real.rpow_nonneg (norm_nonneg (eisEmbedding d)) _
  exact Summable.mul_of_nonneg (f := F) (g := G) hF hG h₁ h₂

private theorem summable_rowWeight {σ : ℝ} (hs : 1 < σ) : Summable (rowWeight σ) := by
  let J := fun k : ℕ => (3 : ℝ) ^ (((k : ℝ) - 3) * (1/6 - σ))
  let P := fun k : 𝓔 × 𝓔 => ‖eisEmbedding k.1‖ ^ (-2*σ) * ‖eisEmbedding k.2‖ ^ (1-6*σ)
  have hJ : Summable J := summable_layerWeight hs
  have hP : Summable P := summable_cdWeight hs
  have J₀ : 0 ≤ J := fun _ => Real.rpow_nonneg (by norm_num) _
  have P₀ : 0 ≤ P := fun _ => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have hJP := hJ.mul_of_nonneg hP J₀ P₀
  have htags : Summable fun _ : Bool × Fin 3 => (1:ℝ) := Summable.of_finite
  have h := htags.mul_of_nonneg hJP (fun _ => zero_le_one) (fun k => mul_nonneg (J₀ k.1) (P₀ k.2))
  exact h.congr fun _ => one_mul _

private theorem row_weight_bound (r : PattersonRow) (neg : Bool) (σ : ℝ) :
    ‖conj r.coefficient / 27‖ * normSq r.frequency ^ (-σ) ≤ rowWeight σ (tag r neg) := by
  have hc : 0 < ‖eisEmbedding r.c‖ := lt_of_lt_of_le zero_lt_one
    (one_le_norm_eisEmbedding r.primary_c.ne_zero)
  have hd : 0 < ‖eisEmbedding r.d‖ := lt_of_lt_of_le zero_lt_one
    (one_le_norm_eisEmbedding r.primary_d.ne_zero)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right r.norm_normalized_coefficient_le
      (Real.rpow_nonneg (normSq_nonneg _) _)
    _ = _ := by
      rw [normSq_eq_norm_sq, ← Real.rpow_natCast_mul (norm_nonneg _), r.norm_frequency]
      rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _) hc.le)
        (pow_nonneg hd.le _),
        Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _) hc.le,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
        ← Real.rpow_natCast_mul hd.le]
      dsimp only [rowWeight, tag]
      norm_num only [Nat.cast_ofNat]
      rw [show (1 - 6*σ) = 1 + 3*(2 * -σ) by ring, Real.rpow_add hd, Real.rpow_one,
        show -2*σ = 2 * -σ by ring,
        show ((r.layer.lambdaExponent : ℝ) - 3)*(1/6-σ) =
          ((r.layer.lambdaExponent : ℝ) - 3)/6 +
          ((r.layer.lambdaExponent : ℝ) - 3)/2 * (2 * -σ) by ring,
        Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      ring

set_option maxHeartbeats 700000 in
/-- Absolute convergence in the full right half-plane comes from summing the primary
cube parameter separately from the squarefree parameter in Patterson's table. -/
theorem PattersonCoefficients.summable_normalized_dirichlet {τ : ℂ → ℂ}
    (ht : PattersonCoefficients τ)
    {σ : ℝ} (hs : 1 < σ) :
    Summable fun m : 𝓔 => ‖conj (τ (pattersonFrequency m)) / 27‖ *
      normSq (pattersonFrequency m) ^ (-σ) := by
  classical
  let μ := pattersonFrequency
  let f := fun m : 𝓔 => ‖conj (τ (μ m)) / 27‖ * normSq (μ m) ^ (-σ)
  have hμ : Function.Injective μ := by
    have hl : eisEmbedding eisLambda ≠ 0 :=
      fun h => eisLambda_prime.ne_zero (eisEmbedding_injective (h.trans (map_zero _).symm))
    intro x y h
    exact eisEmbedding_injective ((div_left_inj₀ (pow_ne_zero _ hl)).mp h)
  have hex (m : Function.support f) : ∃ k : RowIndex, decodeRow k = m.val ∧
    f m ≤ rowWeight σ k := by
    have hne : τ (μ m) ≠ 0 := by
      intro hz
      exact m.property (by simp [f, hz])
    have hr : ∃ r : PattersonRow, μ m = r.frequency ∨ μ m = -r.frequency := by
      by_contra! hh
      exact hne (ht.2 _ hh)
    obtain ⟨r, hr | hr⟩ := hr
    · refine ⟨tag r false, ?_, ?_⟩
      · apply hμ
        simpa [decodeRow_tag, μ, ← r.frequency_eq_div, pattersonFrequency] using hr.symm
      · simpa only [f, hr, (ht.1 r).1] using row_weight_bound r false σ
    · refine ⟨tag r true, ?_, ?_⟩
      · apply hμ
        simpa [decodeRow_tag, μ, ← r.frequency_eq_div, pattersonFrequency, neg_div] using hr.symm
      · simpa only [f, hr, (ht.1 r).2, normSq_neg] using row_weight_bound r true σ
  choose k hk hle using hex
  have hki : Function.Injective k := fun x y he => Subtype.ext
    ((hk x).symm.trans ((congrArg decodeRow he).trans (hk y)))
  have h : Summable fun m : Function.support f => f m :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (normSq_nonneg _) _)) hle
      ((summable_rowWeight hs).comp_injective hki)
  exact (summable_subtype_iff_indicator.mp h).congr fun m => by
    change (Function.support f).indicator f m = f m
    by_cases hm : m ∈ Function.support f
    · exact Set.indicator_of_mem hm _
    · rw [Set.indicator_of_notMem hm]
      exact (not_not.mp hm).symm


/-- The normalized Patterson series may be twisted by any bounded column of modulus
at most one, including the additive translations at the congruence cusps. -/
theorem PattersonCoefficients.mellin_horizontalSeries {τ : ℂ → ℂ} (ht : PattersonCoefficients τ)
    (h : DLMFBesselMellin) {s : ℂ} (hs : 1 < s.re) (w : 𝓔 → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) :
    let l := fun m : {m : 𝓔 // m ≠ 0} => pattersonFrequency m.val
    let a := fun m : {m : 𝓔 // m ≠ 0} => conj (τ (l m)) / 27 * w m
    mellin (fun v => ∑' m, horizontalMode (l m) (a m) v) (2*s) =
      I / 4 * reflectionGammaFactor s * ∑' m, a m * (conj (l m) / ‖l m‖) *
        (normSq (l m) : ℂ) ^ (-s) := by
  intro l a
  let : Countable 𝓔 := by
    apply Function.Surjective.countable (f := fun p : ℤ × ℤ => (p.1 : 𝓔) + p.2 * eisOmega)
    intro m
    obtain ⟨u, v, huv⟩ := eisInteger_coordinates m
    exact ⟨(u, v), huv.symm⟩
  apply mellin_tsum_horizontalMode (s := s) h (by linarith) l a
  · intro m
    apply div_ne_zero
    · exact fun hz => m.property (eisEmbedding_injective (hz.trans (map_zero _).symm))
    · exact pow_ne_zero _ (fun hz => eisLambda_prime.ne_zero
        (eisEmbedding_injective (hz.trans (map_zero _).symm)))
  · have hsum := (ht.summable_normalized_dirichlet hs).comp_injective
      (Subtype.coe_injective (p := fun m : 𝓔 => m ≠ 0))
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro m
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (normSq_nonneg _) _)
    · intro m
      change ‖conj (τ (l m)) / 27 * w m‖ * normSq (l m) ^ _ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (hw m))
        (Real.rpow_nonneg (normSq_nonneg _) _)

end Masullo.QRH.MeanSquare
