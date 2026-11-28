import Masullo.QRH.MeanSquare.Eisenstein
import Masullo.QRH.MeanSquare.SpecialFunctions

/-! # Patterson's theta series at the infinity cusp

The two indices below encode the four nonzero rows of the coefficient table in Theorem 8.1.
Both signs of a frequency have the same coefficient. -/

noncomputable section

open NumberField
open scoped ComplexConjugate

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The exponent of λ is `3j - 3` in the fourth row and `3j - 4` in the first three.
In the latter rows we store `j - 1`, since the table requires `j ≥ 1`. -/
inductive PattersonLayer
  | unshifted (j : ℕ)
  | shifted (jMinusOne : ℕ) (r : Fin 3)

/-- A row of the table allows a squarefree primary `c` and any primary `d`. -/
structure PattersonRow where
  layer : PattersonLayer
  c : 𝓔
  d : 𝓔
  primary_c : eisPrimary c
  primary_d : eisPrimary d
  squarefree_c : Squarefree c

/-- A frequency before attaching the sign in the table. -/
def PattersonRow.frequency (row : PattersonRow) : ℂ :=
  let lambda := eisEmbedding eisLambda
  let factor := match row.layer with
    | .unshifted j => lambda ^ (3 * (j : ℤ) - 3)
    | .shifted k r => eisEmbedding eisOmega ^ (r : ℕ) * lambda ^ (3 * (k : ℤ) - 1)
  factor * eisEmbedding row.c * eisEmbedding row.d ^ 3

/-- The ninth-root factors printed in the first, second and third rows. -/
def pattersonPhase (r : Fin 3) : ℂ :=
  if r = 0 then 1 else if r = 1 then Complex.exp (-2 * Real.pi * Complex.I / 9)
  else Complex.exp (2 * Real.pi * Complex.I / 9)

/-- The coefficient in Patterson I's normalization uses the conjugate of the
unnormalized Gauss sum. Part II, p. 217, prints `2g(λ²,c)` without the conjugation bar.
Here the coefficient follows Part I, Theorem 8.1. -/
def PattersonRow.coefficient (row : PattersonRow) : ℂ :=
  let q := ‖eisEmbedding row.d / eisEmbedding row.c‖
  match row.layer with
  | .unshifted j => conj (pattersonGauss 1 row.c) * q * ((3 : ℝ) ^ (((j : ℝ) + 5) / 2) : ℝ)
  | .shifted k r =>
    pattersonPhase r * conj (pattersonGauss (eisOmega ^ (r : ℕ) * eisLambda ^ 2) row.c) *
      q * ((3 : ℝ) ^ (((k : ℝ) + 1) / 2 + 2) : ℝ)

/-- Extend the table by zero off its signed support. -/
def PattersonCoefficients (τ : ℂ → ℂ) : Prop :=
  (∀ r : PattersonRow, τ r.frequency = r.coefficient ∧ τ (-r.frequency) = r.coefficient) ∧
    ∀ μ, (∀ r : PattersonRow, μ ≠ r.frequency ∧ μ ≠ -r.frequency) → τ μ = 0

/-- Reversing a frequency under conjugation leaves the table entry unchanged. -/
theorem PattersonCoefficients.even {τ : ℂ → ℂ} (h : PattersonCoefficients τ) (μ : ℂ) :
    τ (-μ) = τ μ := by
  classical
  by_cases hr : ∃ r : PattersonRow, μ = r.frequency ∨ μ = -r.frequency
  · obtain ⟨r, hr | hr⟩ := hr
    · rw [hr, (h.1 r).1, (h.1 r).2]
    · rw [hr, neg_neg, (h.1 r).1, (h.1 r).2]
  · push Not at hr
    rw [h.2 μ hr]
    apply h.2
    intro r
    exact ⟨fun hneg => (hr r).2 (neg_eq_iff_eq_neg.mp hneg),
      fun hneg => (hr r).1 (neg_inj.mp hneg)⟩

/-- The unit index occurs in the fourth row with `j = 1`, `c = d = 1`. -/
theorem PattersonCoefficients.one {τ : ℂ → ℂ} (h : PattersonCoefficients τ) : τ 1 = 27 := by
  let r : PattersonRow := ⟨.unshifted 1, 1, 1, by simp [eisPrimary],
    by simp [eisPrimary], squarefree_one⟩
  have hr := (h.1 r).1
  norm_num [r, PattersonRow.frequency, PattersonRow.coefficient] at hr
  exact hr

/-- The normalized conjugate coefficient at `cd³` uses the fourth row with `j = 1`.
The hypotheses allow common prime factors between `c` and `d`. -/
theorem PattersonCoefficients.normalized_primary_cube {τ : ℂ → ℂ} (h : PattersonCoefficients τ)
    {c d : 𝓔} (hc : eisPrimary c) (hd : eisPrimary d) (hsf : Squarefree c) :
    conj (τ (eisEmbedding c * eisEmbedding d ^ 3)) / 27 =
      pattersonGauss 1 c * ‖eisEmbedding d / eisEmbedding c‖ := by
  let r : PattersonRow := ⟨.unshifted 1, c, d, hc, hd, hsf⟩
  have hr := (h.1 r).1
  norm_num [r, PattersonRow.frequency, PattersonRow.coefficient] at hr
  rw [hr]
  norm_num [map_ofNat]

/-- Patterson's trace character `exp(2πi Tr(z))`, Part II (1), p. 217. -/
def pattersonCharacter (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (2 * z.re : ℝ))

lemma pattersonCharacter_neg (z : ℂ) : pattersonCharacter (-z) = conj (pattersonCharacter z) := by
  rw [pattersonCharacter, pattersonCharacter, ← Complex.exp_conj]
  congr 1
  norm_num [map_ofNat]

/-- The expansion at infinity in (8.3), indexed by the nonzero elements of λ⁻³𝓔.
We read Patterson's bare Σ as `HasSum` over these frequencies. -/
def PattersonExpansion (θ : ℂ → ℝ → ℂ) (τ : ℂ → ℂ) (σ : ℝ) : Prop :=
  ∀ z : ℂ, ∀ v : ℝ, 0 < v →
    HasSum (fun m : {a : 𝓔 // a ≠ 0} =>
      let μ := eisEmbedding m.val / eisEmbedding eisLambda ^ 3
      τ μ * v * besselK (1 / 3) (4 * Real.pi * ‖μ‖ * v) * pattersonCharacter (μ * z))
      (θ z v - σ * (v ^ (2 / 3 : ℝ) : ℝ))

/-- Reflecting all frequencies in the sum gives the expansion of the normalized conjugate. -/
theorem PattersonExpansion.conj_div {θ : ℂ → ℝ → ℂ} {τ : ℂ → ℂ} {σ : ℝ}
    (h : PattersonExpansion θ τ σ) (ht : PattersonCoefficients τ) :
    PattersonExpansion (fun z v => conj (θ z v) / 27) (fun μ => conj (τ μ) / 27) (σ / 27) := by
  intro z v hv
  let e : {a : 𝓔 // a ≠ 0} ≃ {a : 𝓔 // a ≠ 0} :=
    (Equiv.neg 𝓔).subtypeEquiv (fun _ => by simp)
  have hh := (Complex.hasSum_conj'.2 (e.hasSum_iff.mpr (h z v hv))).div_const 27
  have he (a : {a : 𝓔 // a ≠ 0}) : (e a).val = -a.val := rfl
  dsimp only [Function.comp_apply] at hh
  simp only [he, map_neg, neg_div, ht.even, norm_neg, neg_mul, pattersonCharacter_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_conj, map_sub] at hh
  have hK (x : ℝ) : conj (besselK (1 / 3) x) = besselK (1 / 3) x := by
    simpa using besselK_conj_real (1 / 3) x
  simp only [hK] at hh
  convert hh using 2 <;> push_cast <;> ring

open Classical in
/-- The first-column cubic symbol on Γ(3), Patterson I (1.1). -/
def pattersonMultiplier (a c : 𝓔) : ℂ :=
  if c = 0 then 1 else eisEmbedding (cubicSymbol c a)

/-- Transformation by a multiplier on Γ(3) under Patterson I's upper-half-space
action (2.1). In matrix coordinates the denominator is `|cz + d|² + |c|²v²`. -/
def PattersonAutomorphyWith (χ : 𝓔 → 𝓔 → ℂ) (θ : ℂ → ℝ → ℂ) : Prop :=
  ∀ a b c d : 𝓔, a * d - b * c = 1 →
    eisPrimary a → 3 ∣ b → 3 ∣ c → eisPrimary d → ∀ z : ℂ, ∀ v : ℝ, 0 < v →
      let czd := eisEmbedding c * z + eisEmbedding d
      let den := ‖czd‖ ^ 2 + ‖eisEmbedding c‖ ^ 2 * v ^ 2
      let z' := ((eisEmbedding a * z + eisEmbedding b) * conj czd +
        eisEmbedding a * conj (eisEmbedding c) * v ^ 2) / den
      θ z' (v / den) = χ a c * θ z v

/-- Normalizing the conjugate series also conjugates its multiplier. -/
theorem PattersonAutomorphyWith.conj_div {χ : 𝓔 → 𝓔 → ℂ} {θ : ℂ → ℝ → ℂ}
    (h : PattersonAutomorphyWith χ θ) (t : ℂ) :
    PattersonAutomorphyWith (fun a c => conj (χ a c)) (fun z v => conj (θ z v) / t) := by
  intro a b c d hdet ha hb hc hd z v hv
  dsimp only
  rw [h a b c d hdet ha hb hc hd z v hv, map_mul, mul_div_assoc]

/-- S. J. Patterson, *A cubic analogue of the theta series*, J. reine angew. Math. 296
(1977), Theorem 8.1, p. 152, coefficient table and (8.2)–(8.3), restricted to Γ(3)
using (1.1), p. 125 and (2.1), (2.4)–(2.5), p. 126. The Gauss sum and trace character
also appear in Part II, (1), p. 217. One function has both the displayed expansion and
the transformation law. <https://doi.org/10.1515/crll.1977.296.125> -/
def PattersonTheorem81 : Prop :=
  ∃ (σ : ℝ) (τ : ℂ → ℂ) (θ : ℂ → ℝ → ℂ),
    σ ^ 2 = 3 ^ 5 / 4 ∧ PattersonCoefficients τ ∧ PattersonExpansion θ τ σ ∧
      PattersonAutomorphyWith pattersonMultiplier θ

/-- In the normalization used for the reflected series, the coefficient at one is one. -/
theorem normalizedTheta_of_patterson (h : PattersonTheorem81) :
    ∃ (κ : ℝ) (coeff : ℂ → ℂ) (Θ : ℂ → ℝ → ℂ), coeff 1 = 1 ∧
      PattersonExpansion Θ coeff κ ∧
      PattersonAutomorphyWith (fun a c => conj (pattersonMultiplier a c)) Θ ∧
      ∀ c d : 𝓔, eisPrimary c → eisPrimary d → Squarefree c →
        coeff (eisEmbedding c * eisEmbedding d ^ 3) =
          pattersonGauss 1 c * ‖eisEmbedding d / eisEmbedding c‖ := by
  obtain ⟨σ, τ, θ, -, hτ, he, ha⟩ := h
  refine ⟨σ / 27, fun μ => conj (τ μ) / 27, fun z v => conj (θ z v) / 27,
    ?_, he.conj_div hτ, ha.conj_div 27, fun _ _ hc hd hs => hτ.normalized_primary_cube hc hd hs⟩
  norm_num [hτ.one, map_ofNat]

end Masullo.QRH.MeanSquare
