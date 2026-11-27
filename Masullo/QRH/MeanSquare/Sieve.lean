import Masullo.QRH.MeanSquare.Eisenstein
import Masullo.QRH.MeanSquare.Rows

/-!
# The quadratic large sieve on ideals

The printed bound uses all squarefree ideals up to each cutoff. The dyadic bound (7)
follows by extending the column vector by zero. Its arithmetic premise identifies the
matrix entries of an Eisenstein Hecke family, including the zeros at common factors.
-/

open NumberField Ideal

namespace Masullo.QRH.MeanSquare

variable {K : Type} [Field K] [NumberField K]

/-- A finite-modulus Hecke character of trivial infinite type, given on integral ideals.
Its zero extension records both the zero ideal and ideals meeting the modulus. -/
def IsRayCharacter (f : Ideal (𝓞 K)) (χ : Ideal (𝓞 K) →*₀ ℂ) : Prop :=
  f ≠ 0 ∧
  (∀ a, χ a ≠ 0 ↔ a ≠ 0 ∧ IsCoprime a f) ∧
  (∀ x : 𝓞 K, x ≠ 0 → x - 1 ∈ f → χ (span {x}) = 1)

/-- The finite conductor is exactly `f` if no character at a proper divisor agrees
with this one away from `f`. -/
def IsPrimitiveRayCharacter (f : Ideal (𝓞 K)) (χ : Ideal (𝓞 K) →*₀ ℂ) : Prop :=
  IsRayCharacter f χ ∧
    ∀ d, d ∣ f → ∀ ψ : Ideal (𝓞 K) →*₀ ℂ, IsRayCharacter d ψ →
      (∀ a, a ≠ 0 → IsCoprime a f → ψ a = χ a) → d = f

/-- Goldmakher–Louvel, *A quadratic large sieve inequality over number fields*,
Math. Proc. Cambridge Philos. Soc. 154 (2013), Definition 1 and (1.2), p. 194,
specialized to order dividing two. The class map is multiplicative on nonzero ideals
prime to `c`. In (3) the primitive representative agrees with the character product
away from the conductors of its two factors. -/
def IsQuadraticHeckeFamily (c : Ideal (𝓞 K)) (χ : Ideal (𝓞 K) → Ideal (𝓞 K) →*₀ ℂ)
    (f : Ideal (𝓞 K) → Ideal (𝓞 K)) : Prop :=
  (∀ a, Squarefree a → IsCoprime a c → IsPrimitiveRayCharacter (f a) (χ a) ∧
    ∀ b, b ≠ 0 → IsCoprime b (f a) → χ a b ^ 2 = 1) ∧
  ∃ (G : Type) (_ : Group G) (_ : Finite G) (cl : Ideal (𝓞 K) → G) (sign : G → G → ℂ),
    cl 1 = 1 ∧
    (∀ a b, a ≠ 0 → b ≠ 0 → IsCoprime a c → IsCoprime b c → cl (a * b) = cl a * cl b) ∧
    (∀ u v, sign u v ^ 2 = 1) ∧
    ∀ a b, Squarefree a → IsCoprime a c → Squarefree b → IsCoprime b c → IsCoprime a b →
      χ a b = χ b a * sign (cl a) (cl b) ∧
      (cl a = cl b → ∃ ψ : Ideal (𝓞 K) →*₀ ℂ, IsPrimitiveRayCharacter (a * b) ψ ∧
        ∀ d, d ≠ 0 → IsCoprime d (a * b) → IsCoprime d (f a) → IsCoprime d (f b) →
          ψ d = χ a d * star (χ b d))

/-- The starred ideal sum in Goldmakher–Louvel with norm cutoff `X`. -/
noncomputable def sieveIdeals (c : Ideal (𝓞 K)) (X : ℝ) : Finset (Ideal (𝓞 K)) :=
  open Classical in
  (Ring.HasFiniteQuotients.finite_absNorm_le ⌊X⌋₊).toFinset.filter
    (fun a => Squarefree a ∧ IsCoprime a c)

/-- A bound for the squared norm of the given finite matrix on complex column vectors. -/
def SieveBound {ι κ : Type*} (rows : Finset ι) (cols : Finset κ) (H : ι → κ → ℂ)
    (B : ℝ) : Prop :=
  ∀ z : κ → ℂ, ∑ a ∈ rows, ‖∑ b ∈ cols, z b * H a b‖ ^ 2 ≤ B * ∑ b ∈ cols, ‖z b‖ ^ 2

/-- L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*,
Math. Proc. Cambridge Philos. Soc. 154 (2013), Theorem 1.1, pp. 194–195,
doi:10.1017/S0305004112000370. Rows are evaluation ideals; columns index the characters.
The constant is taken per family. The print writes `≪_{k,c,ε}`, but its proof pays `|G|` in the
duality step (§3), and a constant uniform over all families satisfying Definition 1 is false. -/
def GoldmakherLouvel (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ (c : Ideal (𝓞 K)), c ≠ 0 →
    ∀ (χ : Ideal (𝓞 K) → Ideal (𝓞 K) →*₀ ℂ) (f : Ideal (𝓞 K) → Ideal (𝓞 K)),
      IsQuadraticHeckeFamily c χ f →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      SieveBound (sieveIdeals c M) (sieveIdeals c N) (fun a b => χ b a)
        (C * (M * N) ^ ε * (M + N))

/-- Restrict the rows and columns of a large-sieve inequality. -/
theorem SieveBound.restrict {ι κ : Type*} {r R : Finset ι} {s S : Finset κ}
    {H : ι → κ → ℂ} {B : ℝ} (h : SieveBound R S H B) (hr : r ⊆ R) (hs : s ⊆ S) :
    SieveBound r s H B := by
  classical
  intro z
  let w (b : κ) : ℂ := if b ∈ s then z b else 0
  have sum_eq {T : Type} [AddCommMonoid T] (F : κ → ℂ → T) (hF : ∀ b, F b 0 = 0) :
      ∑ b ∈ S, F b (w b) = ∑ b ∈ s, F b (z b) := by
    rw [← Finset.sum_subset hs (f := fun b => F b (w b)) (fun b _ hb => by simp [w, hb, hF])]
    exact Finset.sum_congr rfl fun b hb => by simp [w, hb]
  have row_eq (a : ι) : ∑ b ∈ S, w b * H a b = ∑ b ∈ s, z b * H a b :=
    sum_eq (fun b t => t * H a b) (fun b => zero_mul (H a b))
  have hw := h w
  simp_rw [row_eq] at hw
  rw [sum_eq (fun _ t => ‖t‖ ^ 2) (by simp)] at hw
  exact (Finset.sum_le_sum_of_subset_of_nonneg hr (fun _ _ _ => sq_nonneg _)).trans hw

/-- Transposition preserves a nonnegative large-sieve bound. In (15) this
places the varying squarefree row in the denominator of the quadratic symbol. -/
theorem SieveBound.transpose {ι κ : Type*} {rows : Finset ι} {cols : Finset κ}
    {H : ι → κ → ℂ} {B : ℝ} (h : SieveBound rows cols H B) (hB : 0 ≤ B) :
    SieveBound cols rows (fun b a => H a b) B := by
  classical
  intro z
  let t (b : κ) := ∑ a ∈ rows, z a * H a b
  let v (a : ι) := ∑ b ∈ cols, (starRingEnd ℂ) (t b) * H a b
  let T : ℝ := ∑ b ∈ cols, ‖t b‖ ^ 2
  let Z : ℝ := ∑ a ∈ rows, ‖z a‖ ^ 2
  change T ≤ B * Z
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain hzero | hpos := hT.eq_or_lt
  · rw [← hzero]
    exact mul_nonneg hB hZ
  have hpair : (T : ℂ) = ∑ a ∈ rows, z a * v a := by
    simp only [T, Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [t, v, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hdual : T ≤ ∑ a ∈ rows, ‖z a‖ * ‖v a‖ := by
    calc T = ‖(T : ℂ)‖ := (Complex.norm_of_nonneg hT).symm
      _ ≤ _ := by rw [hpair]; simpa [norm_mul] using norm_sum_le rows (fun a => z a * v a)
  have hv : ∑ a ∈ rows, ‖v a‖ ^ 2 ≤ B * T := by
    simpa [v, T] using h (fun b => (starRingEnd ℂ) (t b))
  apply le_of_mul_le_mul_right (a := T) _ hpos
  calc T * T = T ^ 2 := (sq T).symm
    _ ≤ _ := (pow_le_pow_left₀ hT hdual 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq rows (fun a => ‖z a‖) (fun a => ‖v a‖))
    _ ≤ Z * (B * T) := mul_le_mul_of_nonneg_left hv hZ
    _ = _ := by ring

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The manuscript's quadratic symbol `[a°/b]` is the cube of the sextic symbol.
The primary generator supplies the numerator on ideals prime to six. -/
noncomputable def primaryQuadraticSymbol (a b : Ideal 𝓔) : ℂ :=
  (eisEmbedding (powerResidueSymbol 6 (generator a) b)) ^ 3

/-- Constructing the Hecke family for (7) means realizing the primary quadratic symbol
on good squarefree ideals by primitive characters for the exceptional ideal `(72)`. -/
def EisensteinFamilyRealizes (symbol : Ideal 𝓔 → Ideal 𝓔 → ℂ) : Prop :=
  ∃ (χ : Ideal 𝓔 → Ideal 𝓔 →*₀ ℂ) (f : Ideal 𝓔 → Ideal 𝓔),
    IsQuadraticHeckeFamily (span {72}) χ f ∧
    ∀ a b, Squarefree a → IsCoprime a (span {72}) → Squarefree b → IsCoprime b (span {72}) →
      χ b a = symbol a b

/-- The squarefree columns with norm in the manuscript's half-open dyadic band. -/
noncomputable def dyadicSieveIdeals (c : Ideal (𝓞 K)) (N : ℝ) : Finset (Ideal (𝓞 K)) :=
  open Classical in
  (sieveIdeals c (2 * N)).filter fun b => (absNorm b : ℝ) ∈ Set.Ico N (2 * N)

/-- Estimate (7) for the primary quadratic symbol `[a°/b]`. One may restrict rows of norm
at most `M` and columns with norm in `[N,2N)` to arbitrary subsets. -/
def QuadraticSieve (symbol : Ideal 𝓔 → Ideal 𝓔 → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    ∀ rows cols : Finset (Ideal 𝓔), rows ⊆ sieveIdeals (span {6}) M →
      cols ⊆ dyadicSieveIdeals (span {6}) N →
      SieveBound rows cols symbol (C * (M * N) ^ ε * (M + N))

private theorem coprime_seventyTwo {a : Ideal 𝓔} (h : IsCoprime a (span {6})) :
    IsCoprime a (span {72}) := by
  refine (h.pow_right (n := 3)).of_isCoprime_of_dvd_right ?_
  rw [span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
  exact ⟨3, by norm_num⟩

private theorem sieveIdeals_subset {X : ℝ} :
    sieveIdeals (span {(6 : 𝓔)}) X ⊆ sieveIdeals (span {72}) X := by
  classical
  intro a ha
  simp only [sieveIdeals, Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.1, coprime_seventyTwo ha.2.2⟩

theorem quadraticSieve_of_goldmakherLouvel {symbol : Ideal 𝓔 → Ideal 𝓔 → ℂ}
    (hGL : GoldmakherLouvel (CyclotomicField 3 ℚ)) (hFamily : EisensteinFamilyRealizes symbol) :
    QuadraticSieve symbol := by
  classical
  obtain ⟨χ, f, hχ, hsymbol⟩ := hFamily
  intro ε hε
  have h72 : span {(72 : 𝓔)} ≠ 0 := by simp
  obtain ⟨C, hC, hGL⟩ := hGL (span {72}) h72 χ f hχ ε hε
  refine ⟨2 * (2 : ℝ) ^ ε * C, by positivity, ?_⟩
  intro M N hM hN rows cols hr hc
  have hr' := hr.trans sieveIdeals_subset
  have hc' := (hc.trans (Finset.filter_subset _ _)).trans sieveIdeals_subset
  have h := (hGL M (2 * N) hM (by linarith)).restrict hr' hc'
  intro z
  have heq (a) (ha : a ∈ rows) (b) (hb : b ∈ cols) : χ b a = symbol a b := by
    have har := hr' ha
    have hbc := hc' hb
    simp only [sieveIdeals, Finset.mem_filter] at har hbc
    exact hsymbol a b har.2.1 har.2.2 hbc.2.1 hbc.2.2
  have hrow (a) (ha : a ∈ rows) : ∑ b ∈ cols, z b * χ b a = ∑ b ∈ cols, z b * symbol a b :=
    Finset.sum_congr rfl fun b hb => by rw [heq a ha b hb]
  have hz := h z
  dsimp only at hz
  rw [Finset.sum_congr rfl (fun a ha => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hrow a ha))] at hz
  refine hz.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hMN : 0 ≤ M * N := by positivity
  rw [show M * (2 * N) = (M * N) * 2 by ring, Real.mul_rpow hMN (by norm_num)]
  have hpos : 0 ≤ C * ((M * N) ^ ε * 2 ^ ε) := by positivity
  calc
    _ ≤ C * ((M * N) ^ ε * 2 ^ ε) * (2 * (M + N)) :=
      mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = _ := by ring

end Masullo.QRH.MeanSquare
