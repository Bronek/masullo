import Masullo.QRH.MeanSquare.Eisenstein
import Masullo.QRH.MeanSquare.Rows

/-!
# The completed and uncompleted sextic mean squares

The notation follows the source audit, (4)–(6). See OpenAI, *The Quasi-Riemann
Hypothesis* (5 October 2026), Definition 4.3 and (5.3)–(5.5), pp. 14, 18–19.
The ideal and element indices here use the same ring as `Masullo.QRH.MeanSquareA`.
-/

noncomputable section

open NumberField Ideal
open scoped ComplexConjugate ContDiff

namespace Masullo.QRH.MeanSquare

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

def AwayFromSix (n : Ideal 𝓔) : Prop := n ≠ ⊥ ∧ IsCoprime n (span {6})

def Starred (n : Ideal 𝓔) : Prop := AwayFromSix n ∧ Squarefree n

/-- Characters on residues modulo 72, evaluated at primary generators. Only
their restrictions to the subgroup of primary unit classes enter the sums. -/
abbrev RayCharacter := MulChar (𝓔 ⧸ span {(72 : 𝓔)}) ℂ

def sextic (n : Ideal 𝓔) (k : 𝓔) : ℂ := eisEmbedding (powerResidueSymbol 6 k n)

def angularFactor (n : Ideal 𝓔) : ℂ :=
  let z := eisEmbedding (generator n)
  z / ‖z‖

/-- The coefficient `conj(α(n)) γ₂(n)` on the squarefree good ideals. -/
def gaussCoefficient (n : Ideal 𝓔) : ℂ :=
  conj (angularFactor n) / Real.sqrt (absNorm n) *
    ∑ᶠ x : 𝓔 ⧸ n, sextic n (Quotient.out x) ^ 2 *
      differentCharacter (eisEmbedding (Quotient.out x) / eisEmbedding (generator n))

/-- The multiplicative twist of (5.4), including its zero extension. -/
def twist (ξ : RayCharacter) (k : 𝓔) (f n : Ideal 𝓔) : ℂ := open Classical in
  if AwayFromSix n then
    ξ (Ideal.Quotient.mk _ (generator n)) * sextic n (k * generator f ^ 4)
  else 0

/-- The unnormalized squarefree column; compact support makes it a finite sum. -/
def columnSum (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔) (f : Ideal 𝓔) : ℂ :=
  ∑ᶠ n : {n : Ideal 𝓔 // Starred n},
    gaussCoefficient n * twist ξ k f n * W (absNorm n.1 / X)

/-- The form `E(K,X,F)` in (4), with all nonzero element rows. -/
def dualMeanSquare (ξ : RayCharacter) (W : ℝ → ℂ) (K X F : ℝ) : ℝ := open Classical in
  (∑ f ∈ (idealsLe (2 * F)).filter (fun f =>
      Starred f ∧ F ≤ (absNorm f : ℝ) ∧ (absNorm f : ℝ) < 2 * F),
    ∑ k ∈ elementRows K, ‖columnSum ξ W X k f‖ ^ 2) / (X * F)

/-- Cube completion of the normalized column. The length in each summand
is `L = X/(Nb)³`, so the column normalization is `1/√L`. -/
def completedSum (ξ : RayCharacter) (W : ℝ → ℂ) (X : ℝ) (k : 𝓔) (f : Ideal 𝓔) : ℂ :=
  ∑ᶠ b : {b : Ideal 𝓔 // AwayFromSix b},
    let L : ℝ := X / (absNorm b.1 : ℝ) ^ 3
    (conj (angularFactor b) * twist ξ k f b) ^ 3 / (absNorm b.1 : ℂ) *
      (columnSum ξ W L k f / Real.sqrt L)

/-- A compact interval of allowed positive arguments. -/
structure TestInterval where
  lo : ℝ
  hi : ℝ
  pos : 0 < lo
  ordered : lo ≤ hi

/-- The common support interval after the two kernel separations. -/
def TestInterval.enlarge (I : TestInterval) : TestInterval :=
  ⟨I.lo / 16, 4 * I.hi, by linarith [I.pos], by linarith [I.pos, I.ordered]⟩

/-- Smooth tests in the closed unit ball for derivatives through order `m`. -/
def UnitTest (I : TestInterval) (m : ℕ) (W : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ W ∧ tsupport W ⊆ Set.Icc I.lo I.hi ∧
    ∀ j ≤ m, ∀ x ∈ Set.Icc I.lo I.hi, ‖iteratedDeriv j W x‖ ≤ 1

lemma UnitTest.of_le {I : TestInterval} {m n : ℕ} {W : ℝ → ℂ} (h : UnitTest I n W)
    (hm : m ≤ n) : UnitTest I m W :=
  ⟨h.1, h.2.1, fun _ hj => h.2.2 _ (hj.trans hm)⟩

/-- Equation (5), the fixed-`f` completed estimate. Compare Proposition 5.2,
(5.5), p. 19 of the October preprint. A unit test absorbs the squared test norm. -/
def CompletedEstimate : Prop :=
  ∀ C₀ ≥ (1 : ℝ), ∀ ε > (0 : ℝ), ∃ j : ℕ, ∀ I : TestInterval, ∃ C ≥ (0 : ℝ),
    ∀ (D K X : ℝ) (f : Ideal 𝓔) (ξ : RayCharacter) (W : ℝ → ℂ),
      2 ≤ D → 1 ≤ K → K ≤ D ^ C₀ → 1 ≤ X → X ≤ D ^ C₀ →
      Starred f → (absNorm f : ℝ) ≤ D ^ C₀ → UnitTest I j W →
      ∑ k ∈ elementRows K, ‖completedSum ξ W X k f‖ ^ 2 ≤
        C * D ^ ε * (K + K ^ 2 * absNorm f / X)

/-- Equation (4), the positive-gap estimate. Compare Proposition 5.1, (5.1)–(5.2),
p. 18 of the October preprint. The constants are uniform in the lengths and tests. -/
def GapEstimate : Prop :=
  ∀ C₀ ≥ (1 : ℝ), ∀ κ > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ j : ℕ,
    ∀ I : TestInterval, ∃ C ≥ (0 : ℝ), ∀ (D K X F : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
      2 ≤ D → 1 ≤ K → 1 ≤ X → 1 ≤ F → X * F ≤ D ^ C₀ →
      K ≤ X * F * D ^ (-κ) → UnitTest I j W →
      dualMeanSquare ξ W K X F ≤ C * D ^ ε * (X * F)

/-- A bound `B ≥ 0` on all admissible children replaces the supremum in (5.11).
This formulation also applies to an empty child set. -/
def TransferChildren (I : TestInterval) (m : ℕ) (K L F target B : ℝ) : Prop :=
  ∀ (K' X' F' : ℝ) (ξ' : RayCharacter) (U : ℝ → ℂ),
    1 ≤ K' → 1 ≤ X' → 1 ≤ F' → K' ≤ K * L / (target * F) →
    K' / (X' * F') ≤ K / target → X' * F' ≤ L → UnitTest I.enlarge m U →
    dualMeanSquare ξ' U K' X' F' ≤ B * (X' * F')

/-- Transfer at the independent target scale `Σ`. This is the consequence for
`E ≤ A` of Proposition 5.4, (5.10)–(5.12), p. 21 of the October preprint. -/
def TransferEstimate : Prop :=
  ∀ C₀ ≥ (1 : ℝ), ∀ ε > (0 : ℝ), ∀ (m : ℕ) (I : TestInterval), ∃ C ≥ (0 : ℝ),
    ∀ (D K L F target B : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
      2 ≤ D → 1 ≤ K → 1 ≤ L → 1 ≤ F → K ≤ target → L * F ≤ target → target ≤ D ^ C₀ →
      0 ≤ B → TransferChildren I m K L F target B → UnitTest I (4 * m + 12) W →
      dualMeanSquare ξ W K L F ≤ C * D ^ ε * target * (1 + B)

/-- Equation (6), inverse-cube tail in upper-bound form. Compare Lemma 5.3,
(5.6)–(5.7), p. 19. The tail uses the same test and its shortened length. -/
def CubeTailEstimate : Prop :=
  ∀ C₀ ≥ (1 : ℝ), ∀ ε > (0 : ℝ), ∃ j : ℕ, ∀ I : TestInterval, ∃ C ≥ (0 : ℝ),
    ∀ (D K X F B : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
      2 ≤ D → 1 ≤ K → 1 ≤ X → 1 ≤ F → K ≤ X * F → X * F ≤ D ^ C₀ →
      UnitTest I j W → 0 ≤ B →
      (∀ b : Ideal 𝓔, AwayFromSix b →
        let u := (absNorm b : ℝ) ^ 3
        min X (X ^ 2 / K ^ 2) < u → 1 < X / u →
        dualMeanSquare ξ W K (X / u) F ≤ B) →
      dualMeanSquare ξ W K X F ≤ C * D ^ ε * (X * F + B)

end Masullo.QRH.MeanSquare
