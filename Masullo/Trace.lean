import Masullo.Synthesis
import Masullo.ExplicitFormula

/-!
# The trace of scaling on the theta quotient

Convolution by a test function `φ` in the logarithmic variable is a bounded operator on `W a` that
preserves `V a`. For every `a > 0` the operator induced on `W a / V a`, realised on `(V a)ᗮ`, is a
product of two Hilbert-Schmidt operators, and its trace is the sum of `φ̂(ρ - 1/2)` over the zeros
at distance less than `a` from the critical line, with multiplicity. At `a = 1/2` the trace is the
functional of Weil's explicit formula. No position or simplicity of any zero is assumed or
concluded.

The moments that cut out `V a`, listed so that those of one zero come in increasing order, give an
orthonormal basis `e` of `(V a)ᗮ` in which the induced operators are triangular with diagonal
`k̂(ρ - 1/2)`. The resolvent `H` with transform `1 / (c - z)`, `c > a`, satisfies
`(c - a) ‖H u‖² ≤ Re ⟪u, H u⟫`. Hence `(c - a) ‖H e‖² ≤ Re 1 / (c - (ρ - 1/2))`, which is summable
over the zeros, and a convolution by a twice differentiable kernel is `H ∘ H` times a bounded
operator.
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace Masullo.Trace

open Spectrum Synthesis

/-! ### Hilbert-Schmidt operators and traces -/

section HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι κ : Type*}

/-- `∑ ‖A b‖²` converges over every Hilbert basis. -/
def IsHS (A : H →L[ℂ] H) : Prop :=
  ∀ (w : Set H) (b : HilbertBasis w ℂ H), Summable fun i => ‖A (b i)‖ ^ 2

/-- `T` is a product of two Hilbert-Schmidt operators, and its diagonal in every Hilbert basis sums
to `t`. -/
def HasTrace (T : H →L[ℂ] H) (t : ℂ) : Prop :=
  (∃ A B : H →L[ℂ] H, IsHS A ∧ IsHS B ∧ T = A ∘L B) ∧
    ∀ (w : Set H) (b : HilbertBasis w ℂ H), HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) t

omit [CompleteSpace H] in
lemma parseval (d : HilbertBasis κ ℂ H) (x : H) :
    ENNReal.ofReal (‖x‖ ^ 2) = ∑' k, ENNReal.ofReal (‖⟪d k, x⟫_ℂ‖ ^ 2) := by
  have h2 : HasSum (fun k => ‖⟪d k, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
    have h := d.hasSum_inner_mul_inner x x
    rw [inner_self_eq_norm_sq_to_K] at h
    refine (Complex.hasSum_ofReal (L := .unconditional _)).1 ?_
    push_cast
    refine h.congr_fun fun k => ?_
    rw [← inner_conj_symm x (d k), ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast; rfl
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h2.summable, h2.tsum_eq]

lemma tsum_sq_adjoint (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H) (A : H →L[ℂ] H) :
    ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) =
      ∑' k, ENNReal.ofReal (‖ContinuousLinearMap.adjoint A (c k)‖ ^ 2) := by
  rw [tsum_congr fun i => parseval c (A (b i)),
    tsum_congr fun k => parseval b (ContinuousLinearMap.adjoint A (c k)), ENNReal.tsum_comm]
  refine tsum_congr fun k => tsum_congr fun i => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]

/-- The Hilbert-Schmidt sum does not depend on the basis. -/
lemma hasSum_sq_congr (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H) {A : H →L[ℂ] H} {s : ℝ}
    (h : HasSum (fun i => ‖A (b i)‖ ^ 2) s) : HasSum (fun k => ‖A (c k)‖ ^ 2) s := by
  have e := (tsum_sq_adjoint b c A).trans (tsum_sq_adjoint c c A).symm
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq] at e
  have hc : Summable fun k => ‖A (c k)‖ ^ 2 :=
    (ENNReal.summable_toReal (e ▸ ENNReal.ofReal_ne_top)).congr fun k =>
      ENNReal.toReal_ofReal (by positivity)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hc] at e
  have h0 : 0 ≤ s := h.nonneg fun _ => by positivity
  rw [ENNReal.ofReal_eq_ofReal_iff h0 (tsum_nonneg fun _ => by positivity)] at e
  exact e ▸ hc.hasSum

lemma IsHS.of_basis (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H}
    (h : Summable fun i => ‖A (b i)‖ ^ 2) : IsHS A :=
  fun _ c => (hasSum_sq_congr b c h.hasSum).summable

lemma summable_sq_adjoint (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H}
    (h : Summable fun i => ‖A (b i)‖ ^ 2) :
    Summable fun i => ‖ContinuousLinearMap.adjoint A (b i)‖ ^ 2 := by
  refine (ENNReal.summable_toReal (f := fun i => ENNReal.ofReal
    (‖ContinuousLinearMap.adjoint A (b i)‖ ^ 2)) ?_).congr fun k =>
      ENNReal.toReal_ofReal (by positivity)
  rw [← tsum_sq_adjoint b b A, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h]
  exact ENNReal.ofReal_ne_top

/-- The sum `∑ ⟪X b, Y b⟫` does not depend on the basis. -/
lemma hasSum_inner_congr (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H) {X Y : H →L[ℂ] H}
    {t : ℂ} (hX : Summable fun i => ‖X (b i)‖ ^ 2) (hY : Summable fun i => ‖Y (b i)‖ ^ 2)
    (h : HasSum (fun i => ⟪X (b i), Y (b i)⟫_ℂ) t) :
    HasSum (fun k => ⟪X (c k), Y (c k)⟫_ℂ) t := by
  have key : ∀ r : ℂ, ‖r‖ = 1 → Summable fun i => ‖(X + r • Y) (b i)‖ ^ 2 := fun r hr =>
    ((hX.add hY).mul_left 2).of_nonneg_of_le (fun _ => by positivity) fun i => by
      have h1 := norm_add_le (X (b i)) (r • Y (b i))
      rw [norm_smul, hr, one_mul] at h1
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have : (X + r • Y) (b i) = X (b i) + r • Y (b i) := rfl
      rw [this]
      nlinarith [sq_nonneg (‖X (b i)‖ - ‖Y (b i)‖)]
  have hs : ∀ r : ℂ, ‖r‖ = 1 → ∃ s : ℝ,
      HasSum (fun i => ((‖(X + r • Y) (b i)‖ : ℝ) : ℂ) ^ 2) (s : ℂ) ∧
      HasSum (fun k => ((‖(X + r • Y) (c k)‖ : ℝ) : ℂ) ^ 2) (s : ℂ) := fun r hr => by
    refine ⟨∑' i, ‖(X + r • Y) (b i)‖ ^ 2, ?_, ?_⟩
    · exact_mod_cast (Complex.hasSum_ofReal (L := .unconditional _)).2 (key r hr).hasSum
    · exact_mod_cast (Complex.hasSum_ofReal (L := .unconditional _)).2
        (hasSum_sq_congr b c (key r hr).hasSum)
  obtain ⟨s1, b1, c1⟩ := hs 1 (by simp)
  obtain ⟨s2, b2, c2⟩ := hs (-1) (by simp)
  obtain ⟨s3, b3, c3⟩ := hs (-I) (by simp)
  obtain ⟨s4, b4, c4⟩ := hs I (by simp)
  have e : ∀ x : H, ⟪X x, Y x⟫_ℂ = (((‖(X + (1 : ℂ) • Y) x‖ : ℝ) : ℂ) ^ 2 -
      ((‖(X + (-1 : ℂ) • Y) x‖ : ℝ) : ℂ) ^ 2 + (((‖(X + (-I) • Y) x‖ : ℝ) : ℂ) ^ 2 -
      ((‖(X + I • Y) x‖ : ℝ) : ℂ) ^ 2) * I) / 4 := fun x => by
    rw [inner_eq_sum_norm_sq_div_four]
    simp [sub_eq_add_neg]
  have hb := ((b1.sub b2).add ((b3.sub b4).mul_right I)).div_const 4
  have hc := ((c1.sub c2).add ((c3.sub c4).mul_right I)).div_const 4
  rw [← h.unique (hb.congr_fun fun i => e (b i))] at hc
  exact hc.congr_fun fun k => e (c k)

/-- The trace of a product of Hilbert-Schmidt operators can be computed in one basis. -/
lemma HasTrace.of_basis (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H} {t : ℂ}
    (hA : Summable fun i => ‖A (b i)‖ ^ 2) (hB : Summable fun i => ‖B (b i)‖ ^ 2)
    (h : HasSum (fun i => ⟪b i, (A ∘L B) (b i)⟫_ℂ) t) : HasTrace (A ∘L B) t := by
  have e : ∀ x, ⟪x, (A ∘L B) x⟫_ℂ = ⟪ContinuousLinearMap.adjoint A x, B x⟫_ℂ := fun x =>
    (ContinuousLinearMap.adjoint_inner_left A _ _).symm
  simp only [e] at h
  refine ⟨⟨A, B, .of_basis b hA, .of_basis b hB, rfl⟩, fun w c => ?_⟩
  simp only [e]
  exact hasSum_inner_congr b c (summable_sq_adjoint b hA) hB h

/-- The trace is unique, and is the sum of the diagonal in any basis. -/
lemma HasTrace.hasSum {T : H →L[ℂ] H} {t : ℂ} (hT : HasTrace T t) (b : HilbertBasis ι ℂ H) :
    HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) t := by
  obtain ⟨⟨A, B, hA, hB, rfl⟩, h⟩ := hT
  obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ H
  have e : ∀ x, ⟪x, (A ∘L B) x⟫_ℂ = ⟪ContinuousLinearMap.adjoint A x, B x⟫_ℂ := fun x =>
    (ContinuousLinearMap.adjoint_inner_left A _ _).symm
  have h1 := h w c
  simp only [e] at h1 ⊢
  exact hasSum_inner_congr c b (summable_sq_adjoint c (hA w c)) (hB w c) h1

/-! ### Triangular operators -/

/-- A basis adapted to a total family of functionals listed by `code`: the `i`-th vector is
orthogonal to the earlier members and lies in the span of the members up to `i`. -/
lemma exists_adapted_basis (v : ι → H) (code : ι → ℕ) (hcode : code.Injective)
    (hv : ∀ x, (∀ i, ⟪v i, x⟫_ℂ = 0) → x = 0)
    (hind : ∀ i, ∃ u, ⟪v i, u⟫_ℂ ≠ 0 ∧ ∀ k, code k < code i → ⟪v k, u⟫_ℂ = 0) :
    ∃ b : HilbertBasis ι ℂ H, ∀ i, b i ∈ Submodule.span ℂ (v '' {k | code k ≤ code i}) ∧
      ∀ k, code k < code i → ⟪v k, b i⟫_ℂ = 0 := by
  classical
  set f : ℕ → H := Function.extend code v 0
  have hf : ∀ i, f (code i) = v i := fun i => hcode.extend_apply _ _ _
  have hf0 : ∀ n, n ∉ range code → f n = 0 := fun n hn =>
    Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hn ⟨i, hi⟩
  set g := InnerProductSpace.gramSchmidt ℂ f
  set e := InnerProductSpace.gramSchmidtNormed ℂ f
  have hsub : ∀ s : Set ℕ, Submodule.span ℂ (f '' s) ≤ Submodule.span ℂ (v '' (code ⁻¹' s)) := by
    intro s
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, hn, rfl⟩
    by_cases h : n ∈ range code
    · obtain ⟨i, rfl⟩ := h
      rw [hf]
      exact Submodule.subset_span ⟨i, hn, rfl⟩
    · rw [hf0 n h]
      exact zero_mem _
  have hg : ∀ i, g (code i) ≠ 0 := fun i h0 => by
    obtain ⟨u, hu, hk⟩ := hind i
    have h1 : f (code i) ∈ Submodule.span ℂ (f '' Iio (code i)) := by
      have h2 := InnerProductSpace.gramSchmidt_def' ℂ f (code i)
      rw [show InnerProductSpace.gramSchmidt ℂ f (code i) = 0 from h0, zero_add] at h2
      rw [h2, ← InnerProductSpace.span_gramSchmidt_Iio]
      refine Submodule.sum_mem _ fun j hj => ?_
      refine Submodule.span_mono ?_ (Submodule.starProjection_apply_mem _ _)
      rintro _ rfl
      exact ⟨j, Finset.mem_Iio.1 hj, rfl⟩
    rw [hf] at h1
    have h3 := hsub _ h1
    refine hu ?_
    refine Submodule.span_induction (p := fun x _ => ⟪x, u⟫_ℂ = 0) ?_ (inner_zero_left _)
      (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero])
      (fun r x _ hx => by rw [inner_smul_left, hx, mul_zero]) h3
    rintro _ ⟨k, hk', rfl⟩
    exact hk k hk'
  have hne : ∀ i, e (code i) ≠ 0 := fun i => by
    simp only [e, InnerProductSpace.gramSchmidtNormed]
    exact smul_ne_zero (inv_ne_zero (ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hg i)))) (hg i)
  have hon : Orthonormal ℂ fun i => e (code i) :=
    (InnerProductSpace.gramSchmidtNormed_orthonormal' (𝕜 := ℂ) f).comp
      (fun i => ⟨code i, hne i⟩) fun i j h => hcode (congrArg Subtype.val h)
  have hspan : ∀ i, v i ∈ Submodule.span ℂ (range fun i => e (code i)) := fun i => by
    have h1 : f (code i) ∈ Submodule.span ℂ (range e) := by
      rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]
      exact Submodule.subset_span ⟨_, rfl⟩
    rw [hf] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨n, rfl⟩
    by_cases h : n ∈ range code
    · obtain ⟨j, rfl⟩ := h
      exact Submodule.subset_span ⟨j, rfl⟩
    · have : e n = 0 := by
        simp only [e, InnerProductSpace.gramSchmidtNormed]
        rw [InnerProductSpace.gramSchmidt_def, hf0 n h]
        simp
      rw [this]
      exact zero_mem _
  have hbot : (Submodule.span ℂ (range fun i => e (code i)))ᗮ = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun x hx => hv x fun i => hx _ (hspan i)
  refine ⟨.mkOfOrthogonalEqBot hon hbot, fun i => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  refine ⟨?_, fun k hk => ?_⟩
  · refine Submodule.smul_mem _ _ ?_
    exact hsub (Iic (code i)) (InnerProductSpace.gramSchmidt_mem_span ℂ f le_rfl)
  · have h1 := InnerProductSpace.gramSchmidt_inv_triangular ℂ f hk
    rw [hf] at h1
    simp only [e, InnerProductSpace.gramSchmidtNormed]
    rw [inner_smul_right, inner_eq_zero_symm.1 h1, mul_zero]

omit [CompleteSpace H] in
/-- The diagonal of a triangular operator in an adapted basis. -/
lemma diagonal_eq {v : ι → H} {code : ι → ℕ} {b : HilbertBasis ι ℂ H} {i : ι}
    (hb : b i ∈ Submodule.span ℂ (v '' {k | code k ≤ code i}))
    (hb' : ∀ k, code k < code i → ⟪v k, b i⟫_ℂ = 0) (hcode : code.Injective) {S : H →L[ℂ] H}
    {l : ι → ℂ} (hS : ∀ k x, (∀ j, code j < code k → ⟪v j, x⟫_ℂ = 0) →
      ⟪v k, S x⟫_ℂ = l k * ⟪v k, x⟫_ℂ) : ⟪b i, S (b i)⟫_ℂ = l i := by
  have key : ∀ x ∈ Submodule.span ℂ (v '' {k | code k ≤ code i}),
      ⟪x, S (b i)⟫_ℂ = l i * ⟪x, b i⟫_ℂ := fun x hx => by
    refine Submodule.span_induction (p := fun x _ => ⟪x, S (b i)⟫_ℂ = l i * ⟪x, b i⟫_ℂ) ?_
      (by simp) (fun x y _ _ hx hy => by rw [inner_add_left, inner_add_left, hx, hy, mul_add])
      (fun r x _ hx => by rw [inner_smul_left, inner_smul_left, hx, mul_left_comm]) hx
    rintro _ ⟨k, hk, rfl⟩
    rw [hS k _ fun j hj => hb' j (hj.trans_le hk)]
    rcases (show code k ≤ code i from hk).lt_or_eq with h | h
    · rw [hb' k h, mul_zero, mul_zero]
    · rw [hcode h]
  rw [key _ hb, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
  simp

end HilbertSchmidt

/-! ### Convolution over a flow -/

section Flow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {a c : ℝ}
  {τ : ℝ → H →L[ℂ] H} {k l : ℝ → ℂ}

/-- A strongly continuous one-parameter group of growth at most `e^{a|t|}`. -/
structure Flow (a : ℝ) (τ : ℝ → H →L[ℂ] H) : Prop where
  nonneg : 0 ≤ a
  zero : τ 0 = 1
  add : ∀ s t u, τ (s + t) u = τ s (τ t u)
  norm_le : ∀ t u, ‖τ t u‖ ≤ Real.exp (a * |t|) * ‖u‖
  cont : ∀ u, Continuous fun t => τ t u

/-- The kernels of bounded convolution operators: `e^{a|x|} k` is integrable. -/
def Good (a : ℝ) (k : ℝ → ℂ) : Prop := Integrable fun x : ℝ => (Real.exp (a * |x|) : ℂ) * k x

lemma Good.aesm (hk : Good a k) : AEStronglyMeasurable k :=
  Synthesis.aesm_of_exp_mul hk.aestronglyMeasurable

omit [CompleteSpace H] in
lemma Good.integrable (hk : Good a k) (hτ : Flow a τ) (u : H) :
    Integrable fun y => k y • τ y u := by
  refine (hk.norm.mul_const ‖u‖).mono' (hk.aesm.smul (hτ.cont u).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have := mul_le_mul_of_nonneg_left (hτ.norm_le y u) (norm_nonneg (k y))
  linarith

/-- The convolution operator `u ↦ ∫ k(y) τ_y u dy`. -/
noncomputable def conv (hτ : Flow a τ) (hk : Good a k) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun u := ∫ y, k y • τ y u
      map_add' u v := by
        rw [← integral_add (hk.integrable hτ u) (hk.integrable hτ v)]
        simp only [map_add, smul_add]
      map_smul' r u := by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm r] }
    (∫ x : ℝ, ‖(Real.exp (a * |x|) : ℂ) * k x‖) fun u => by
      rw [← integral_mul_const]
      refine norm_integral_le_of_norm_le (hk.norm.mul_const ‖u‖) (Eventually.of_forall fun y => ?_)
      rw [norm_smul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have := mul_le_mul_of_nonneg_left (hτ.norm_le y u) (norm_nonneg (k y))
      linarith

omit [CompleteSpace H] in
lemma conv_apply (hτ : Flow a τ) (hk : Good a k) (u : H) : conv hτ hk u = ∫ y, k y • τ y u := rfl

lemma map_conv (hτ : Flow a τ) (hk : Good a k) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (L : H →L[ℂ] E) (u : H) :
    L (conv hτ hk u) = ∫ y, k y • L (τ y u) := by
  rw [conv_apply, ← L.integral_comp_comm (hk.integrable hτ u)]
  simp only [map_smul]

/-- A generalised character that kills the lower ones is multiplied by the transform of `k`. -/
lemma character_conv (hτ : Flow a τ) (hk : Good a k) (L : H →L[ℂ] ℂ) {z : ℂ} {u : H}
    (h : ∀ y : ℝ, L (τ y u) = exp (z * y) * L u) : L (conv hτ hk u) = jet k 0 z * L u := by
  rw [map_conv, Synthesis.jet_zero, ← integral_mul_const]
  simp only [h, smul_eq_mul, mul_assoc]

lemma conv_mem (hτ : Flow a τ) (hk : Good a k) {V : Submodule ℂ H} [V.HasOrthogonalProjection]
    (hV : ∀ y, ∀ v ∈ V, τ y v ∈ V) {v : H} (hv : v ∈ V) : conv hτ hk v ∈ V := by
  have h := map_conv hτ hk Vᗮ.orthogonalProjectionOnto v
  have h0 : ∀ x, Vᗮ.orthogonalProjectionOnto x = 0 ↔ x ∈ V := fun x => by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
  rw [← h0, h, integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)]
  simp only [Pi.zero_apply, (h0 _).2 (hV y v hv), smul_zero]

lemma conv_comm (hτ : Flow a τ) (hk : Good a k) (hl : Good a l) (u : H) :
    conv hτ hk (conv hτ hl u) = conv hτ hl (conv hτ hk u) := by
  have e : ∀ y v, conv hτ hl (τ y v) = τ y (conv hτ hl v) := fun y v => by
    rw [map_conv, conv_apply]
    simp only [← hτ.add, add_comm]
  rw [map_conv hτ hk (conv hτ hl), conv_apply]
  simp only [e]

/-- The resolvent kernel `e^{-cx}` on `x > 0`, with transform `1 / (c - z)`. -/
noncomputable def resolvent (c : ℝ) : ℝ → ℂ := (Ioi 0).indicator fun x : ℝ => exp (-(c : ℂ) * x)

lemma good_resolvent (hc : a < c) : Good a (resolvent c) := by
  have h : IntegrableOn (fun x : ℝ => exp (((a - c : ℝ) : ℂ) * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using hc) 0
  refine (integrable_indicator_iff measurableSet_Ioi).2 h |>.congr
    (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [resolvent, indicator_of_mem hx, abs_of_pos (mem_Ioi.1 hx)]
    rw [ofReal_exp, ← Complex.exp_add]
    push_cast
    ring_nf
  · simp [resolvent, indicator_of_notMem hx]

lemma jet_resolvent {z : ℂ} (hz : z.re < c) : jet (resolvent c) 0 z = 1 / (c - z) := by
  have hneg : (z - c).re < 0 := by simpa using hz
  rw [Synthesis.jet_zero, integral_congr_ae (g := (Ioi 0).indicator fun x : ℝ => exp ((z - c) * x))
    (Eventually.of_forall fun x => ?_), integral_indicator measurableSet_Ioi,
    integral_exp_mul_complex_Ioi hneg, ← neg_sub (c : ℂ) z]
  · rw [ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
  · by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [resolvent, indicator_of_mem hx, ← Complex.exp_add]
      ring_nf
    · simp [resolvent, indicator_of_notMem hx]

/-- Dissipativity: `Re 1 / (c - z) ≥ (c - a) |1 / (c - z)|²` on the edges of the strip, in operator
form. -/
lemma resolvent_le (hτ : Flow a τ) (hc : a < c) (u : H) :
    (c - a) * ‖conv hτ (good_resolvent hc) u‖ ^ 2 ≤
      (⟪u, conv hτ (good_resolvent hc) u⟫_ℂ).re := by
  set v := conv hτ (good_resolvent hc) u
  set F : ℝ → H := fun s => (Real.exp (-c * s)) • τ s u
  have hF : Continuous F := by
    have := hτ.cont u
    fun_prop
  have hres : ∀ x, resolvent c x • τ x u = (Ioi 0).indicator F x := fun x => by
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [resolvent, indicator_of_mem hx, F]
      rw [← Complex.coe_smul]
      push_cast
      rfl
    · simp [resolvent, indicator_of_notMem hx]
  have hFi : IntegrableOn F (Ioi 0) := (integrable_indicator_iff measurableSet_Ioi).1
    (((good_resolvent hc).integrable hτ u).congr (Eventually.of_forall hres))
  have hv : v = ∫ s in Ioi 0, F s := by
    rw [← integral_indicator measurableSet_Ioi]
    exact integral_congr_ae (Eventually.of_forall hres)
  set p : ℝ → H := fun y => v - ∫ s in (0 : ℝ)..y, F s
  have hp : ∀ y, 0 ≤ y → p y = Real.exp (-c * y) • τ y v := fun y hy => by
    have h1 : p y = ∫ s in Ioi y, F s := by
      simp only [p]
      rw [hv, sub_eq_iff_eq_add, add_comm]
      exact (intervalIntegral.integral_interval_add_Ioi hFi
        (hFi.mono_set (Ioi_subset_Ioi hy))).symm
    have h2 : τ y v = ∫ s in Ioi 0, Real.exp (-c * s) • τ (s + y) u := by
      rw [hv, ← (τ y).integral_comp_comm hFi]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [F]
      rw [← Complex.coe_smul, map_smul, ← hτ.add, add_comm]
      rfl
    rw [h1, h2, ← integral_smul]
    have h3 := (measurePreserving_add_right volume y).setIntegral_preimage_emb
      (measurableEmbedding_addRight y) F (Ioi y)
    rw [show (fun x => x + y) ⁻¹' Ioi y = Ioi 0 by ext; simp] at h3
    rw [← h3]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [F, smul_smul, ← Real.exp_add]
    congr 2
    ring
  have hp0 : p 0 = v := by simp [p]
  have hd : HasDerivAt p (-u) 0 := by
    have h := (hF.integral_hasStrictDerivAt 0 0).hasDerivAt.const_sub v
    have h0 : F 0 = u := by simp [F, hτ.zero]
    rwa [h0] at h
  have hd2 : HasDerivAt (fun y => Real.exp (-(2 * (c - a)) * y) * ‖v‖ ^ 2 - ‖p y‖ ^ 2)
      (-(2 * (c - a)) * ‖v‖ ^ 2 + 2 * (⟪u, v⟫_ℂ).re) 0 := by
    have h1 : HasDerivAt (fun y => ‖p y‖ ^ 2) (2 * (⟪v, -u⟫_ℂ).re) 0 := by
      have h := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd.inner ℂ hd)
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      · rw [hp0, reCLM_apply, add_re, ← inner_conj_symm (-u) v, conj_re, two_mul]
      · exact (inner_self_eq_norm_sq (𝕜 := ℂ) (p y)).symm
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(2 * (c - a)) * y)) (-(2 * (c - a))) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-(2 * (c - a)))).exp
    refine ((h2.mul_const _).sub h1).congr_deriv ?_
    have h3 : (⟪v, u⟫_ℂ).re = (⟪u, v⟫_ℂ).re := by rw [← inner_conj_symm u v, conj_re]
    rw [inner_neg_right, neg_re, h3]
    ring
  have hn : 0 ≤ -(2 * (c - a)) * ‖v‖ ^ 2 + 2 * (⟪u, v⟫_ℂ).re := by
    have ht := (hasDerivAt_iff_tendsto_slope.1 hd2).mono_left
      (nhdsWithin_mono 0 (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun x hx => (mem_Ioi.1 hx).ne'))
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy : 0 < y := hy
    rw [slope_def_field, hp0]
    refine div_nonneg ?_ (by linarith)
    rw [mul_zero, Real.exp_zero, one_mul, sub_self, sub_zero, hp y hy.le, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have h1 : ‖τ y v‖ ^ 2 ≤ (Real.exp (a * y) * ‖v‖) ^ 2 := by
      have := hτ.norm_le y v
      rw [abs_of_pos hy] at this
      gcongr
    have h2 : Real.exp (-c * y) ^ 2 * (Real.exp (a * y) * ‖v‖) ^ 2 =
        Real.exp (-(2 * (c - a)) * y) * ‖v‖ ^ 2 := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, ← Real.exp_add, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [← h2, sub_nonneg]
    gcongr
  linarith

/-- The transform of `c k + k'` is `c - z` times that of `k`, so the resolvent gives back `k`. -/
lemma conv_resolvent (hτ : Flow a τ) (hc : a < c) (hk : ContDiff ℝ 1 k) (hs : HasCompactSupport k)
    (hg : Good a k) (hg' : Good a fun x => c * k x + deriv k x) :
    conv hτ hg = conv hτ (good_resolvent hc) ∘L conv hτ hg' := by
  ext u
  set k1 : ℝ → ℂ := fun x => c * k x + deriv k x
  have hk1 : Continuous k1 := by
    have := hk.continuous_deriv le_rfl
    have := hk.continuous
    fun_prop
  have hG : Integrable (fun p : ℝ × ℝ => (resolvent c p.1 * k1 p.2) • τ (p.1 + p.2) u)
      (volume.prod volume) := by
    refine (((good_resolvent hc).norm.mul_prod hg'.norm).mul_const ‖u‖).mono' ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((good_resolvent hc).aesm.comp_fst.mul hg'.aesm.comp_snd).smul
        ((hτ.cont u).comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
    · have h1 := hτ.norm_le (p.1 + p.2) u
      have ha : Real.exp (a * |p.1 + p.2|) ≤ Real.exp (a * |p.1|) * Real.exp (a * |p.2|) := by
        rw [← Real.exp_add, Real.exp_le_exp, ← mul_add]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hτ.nonneg
      simp only [norm_smul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc _ ≤ ‖resolvent c p.1‖ * ‖k1 p.2‖ *
            (Real.exp (a * |p.1|) * Real.exp (a * |p.2|) * ‖u‖) := by
              gcongr
              exact h1.trans (by gcongr)
        _ = _ := by ring
  have hF : Integrable (fun p : ℝ × ℝ => (resolvent c p.1 * k1 (p.2 - p.1)) • τ p.2 u)
      (volume.prod volume) := by
    have h := (measurePreserving_prod_neg_add volume volume).integrable_comp_of_integrable hG
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, neg_add_eq_sub, add_sub_cancel]
  have hin : ∀ y, ∫ s, resolvent c s * k1 (y - s) = k y := fun y => by
    have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => -(exp (-(c : ℂ) * s) * k (y - s)))
        (exp (-(c : ℂ) * s) * k1 (y - s)) s := fun s => by
      have h1 : HasDerivAt (fun s : ℝ => exp (-(c : ℂ) * s)) (exp (-(c : ℂ) * s) * -c) s := by
        simpa using (((hasDerivAt_id s).ofReal_comp).const_mul (-(c : ℂ))).cexp
      have h2 : HasDerivAt (fun s => k (y - s)) (-deriv k (y - s)) s :=
        ((hk.differentiable one_ne_zero) (y - s)).hasDerivAt.comp_const_sub y s
      refine (h1.mul h2).neg.congr_deriv ?_
      simp only [k1]
      ring
    have hcs : HasCompactSupport fun s => k (y - s) := hs.comp_homeomorph (Homeomorph.subLeft y)
    have hcs1 : HasCompactSupport fun s => k1 (y - s) :=
      HasCompactSupport.comp_homeomorph (f := k1) (hs.mul_left.add hs.deriv) (Homeomorph.subLeft y)
    have hint : Integrable fun s : ℝ => exp (-(c : ℂ) * s) * k1 (y - s) :=
      (by fun_prop : Continuous _).integrable_of_hasCompactSupport hcs1.mul_left
    have hz : Tendsto (fun s : ℝ => -(exp (-(c : ℂ) * s) * k (y - s))) atTop (𝓝 0) := by
      have h := (hcs.mul_left (f := fun s : ℝ => exp (-(c : ℂ) * s))).neg
      exact h.is_zero_at_infty.mono_left atTop_le_cocompact
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun s _ => hd s)
      hint.integrableOn hz
    rw [← integral_indicator measurableSet_Ioi] at h
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_mul, sub_zero, zero_sub,
      neg_neg] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [resolvent, indicator]
    split_ifs <;> simp
  rw [ContinuousLinearMap.comp_apply, conv_apply, conv_apply]
  have h1 : ∀ s, resolvent c s • τ s (conv hτ hg' u) =
      ∫ y, (resolvent c s * k1 (y - s)) • τ y u := fun s => by
    rw [map_conv, ← integral_smul, ← integral_sub_right_eq_self _ s]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_smul, ← hτ.add, add_sub_cancel]
  simp only [h1]
  rw [integral_integral_swap hF]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [integral_smul_const, hin]

end Flow

/-! ### Translations on the weighted space -/

section Translation

variable {a : ℝ} {k : ℝ → ℂ}

lemma weight_add_le (ha : 0 < a) (x y : ℝ) : 2 * Real.cosh (2 * a * (x + y)) ≤
    Real.exp (2 * a * |y|) * (2 * Real.cosh (2 * a * x)) := by
  have h1 : Real.exp (2 * a * y) ≤ Real.exp (2 * a * |y|) := by gcongr; exact le_abs_self y
  have h2 : Real.exp (-(2 * a * y)) ≤ Real.exp (2 * a * |y|) := by
    rw [← mul_neg]; gcongr; exact neg_le_abs y
  have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2 * a * x)).le
  have h4 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(2 * a * x))).le
  rw [← Real.exp_add] at h3 h4
  rw [Real.cosh_eq, Real.cosh_eq, mul_add, neg_add]
  linarith

lemma ae_shift {p : ℝ → Prop} (h : ∀ᵐ x, p x) (y : ℝ) : ∀ᵐ x : ℝ, p (x - y) :=
  (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae h

lemma weight_shift_le (ha : 0 < a) (y : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    2 * Real.cosh (2 * a * x) * ‖f (x - y)‖ ^ 2 ≤ Real.exp (2 * a * |y|) *
      (2 * Real.cosh (2 * a * (x - y)) * ‖f (x - y)‖ ^ 2) := by
  have h := weight_add_le ha (x - y) y
  rw [sub_add_cancel] at h
  rw [← mul_assoc]
  gcongr

lemma memLp_shift (ha : 0 < a) (y : ℝ) {u : ℝ → ℂ} (hu : MemLp u 2 (wt a)) :
    MemLp (fun x => u (x - y)) 2 (wt a) :=
  memLp_wt ((hu.1.mono_ac (absolutelyContinuous_wt a)).comp_measurePreserving
    (measurePreserving_sub_right volume y))
    (((integrable_weight_mul_sq hu).comp_sub_right y).const_mul _) (weight_shift_le ha y u)

lemma norm_sq_eq (u : W a) : ‖u‖ ^ 2 = ∫ x, 2 * Real.cosh (2 * a * x) * ‖u x‖ ^ 2 := by
  have h := inner_eq_integral u u
  rw [inner_self_eq_norm_sq_to_K] at h
  refine ofReal_injective ?_
  rw [← integral_complex_ofReal]
  push_cast
  refine h.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
  simp only [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

lemma shift_ae (ha : 0 < a) (y : ℝ) (u : W a) :
    (memLp_shift ha y (Lp.memLp u)).toLp =ᵐ[volume] fun x => u (x - y) :=
  ae_wt_iff.1 (MemLp.coeFn_toLp _)

/-- Translation `u(x) ↦ u(x - y)` on `W a`. -/
noncomputable def shift (ha : 0 < a) (y : ℝ) : W a →L[ℂ] W a :=
  LinearMap.mkContinuous
    { toFun u := (memLp_shift ha y (Lp.memLp u)).toLp
      map_add' u v := by
        refine Lp.ext (ae_wt_iff.2 ?_)
        filter_upwards [shift_ae ha y u, shift_ae ha y v, shift_ae ha y (u + v),
          ae_wt_iff.1 (Lp.coeFn_add (memLp_shift ha y (Lp.memLp u)).toLp
            (memLp_shift ha y (Lp.memLp v)).toLp),
          ae_shift (ae_wt_iff.1 (Lp.coeFn_add u v)) y] with x h1 h2 h3 h4 h5
        rw [h3, h4, h5, Pi.add_apply, Pi.add_apply, h1, h2]
      map_smul' r u := by
        refine Lp.ext (ae_wt_iff.2 ?_)
        filter_upwards [shift_ae ha y u, shift_ae ha y (r • u),
          ae_wt_iff.1 (Lp.coeFn_smul r (memLp_shift ha y (Lp.memLp u)).toLp),
          ae_shift (ae_wt_iff.1 (Lp.coeFn_smul r u)) y] with x h1 h3 h4 h5
        rw [h3, RingHom.id_apply, h4, h5, Pi.smul_apply, Pi.smul_apply, h1] }
    (Real.exp (a * |y|)) fun u => by
      refine le_of_sq_le_sq ?_ (by positivity)
      have hi := ((integrable_weight_mul_sq (Lp.memLp u)).comp_sub_right y).const_mul
        (Real.exp (2 * a * |y|))
      rw [norm_sq_eq, mul_pow, norm_sq_eq u, ← Real.exp_nat_mul]
      calc _ = ∫ x, 2 * Real.cosh (2 * a * x) * ‖u (x - y)‖ ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards [shift_ae ha y u] with x hx
            simp only [LinearMap.coe_mk, AddHom.coe_mk, hx]
        _ ≤ ∫ x, Real.exp (2 * a * |y|) *
              (2 * Real.cosh (2 * a * (x - y)) * ‖u (x - y)‖ ^ 2) :=
            integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hi
              (Eventually.of_forall (weight_shift_le ha y u))
        _ = _ := by
            rw [integral_const_mul, integral_sub_right_eq_self
              (fun x => 2 * Real.cosh (2 * a * x) * ‖u x‖ ^ 2) y]
            push_cast
            ring_nf

lemma coeFn_shift (ha : 0 < a) (y : ℝ) (u : W a) :
    shift ha y u =ᵐ[volume] fun x => u (x - y) := shift_ae ha y u

lemma inner_shift (ha : 0 < a) (v u : W a) (y : ℝ) : ⟪v, shift ha y u⟫_ℂ =
    cross (fun x => ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) * conj (v x)) u y := by
  rw [inner_eq_integral, cross]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_shift ha y u] with x hx
  rw [hx]

lemma flow_shift (ha : 0 < a) : Flow a (shift ha) := by
  have hzero : shift ha 0 = 1 := ContinuousLinearMap.ext fun u => Lp.ext <| ae_wt_iff.2 <| by
    filter_upwards [coeFn_shift ha 0 u] with x hx
    simpa using hx
  have hadd : ∀ s t u, shift ha (s + t) u = shift ha s (shift ha t u) := fun s t u =>
    Lp.ext <| ae_wt_iff.2 <| by
      filter_upwards [coeFn_shift ha (s + t) u, coeFn_shift ha s (shift ha t u),
        ae_shift (coeFn_shift ha t u) s] with x h1 h2 h3
      rw [h1, h2, h3, sub_sub]
  have hle : ∀ t u, ‖shift ha t u‖ ≤ Real.exp (a * |t|) * ‖u‖ := fun t u =>
    (shift ha t).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _) u
  refine ⟨ha.le, hzero, hadd, hle, fun u => continuous_iff_continuousAt.2 fun y₀ => ?_⟩
  have hsq : Tendsto (fun t => ‖shift ha t u - u‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have hw : Continuous fun t => (⟪u, shift ha t u⟫_ℂ).re := by
      simp only [inner_shift]
      exact continuous_re.comp ((dual_of_mem ha u u).continuous_cross ha.le)
    have hup : Tendsto (fun t => (Real.exp (a * |t|) * ‖u‖) ^ 2 -
        2 * (⟪u, shift ha t u⟫_ℂ).re + ‖u‖ ^ 2) (𝓝 0) (𝓝 0) := by
      have : Continuous fun t => (Real.exp (a * |t|) * ‖u‖) ^ 2 -
        2 * (⟪u, shift ha t u⟫_ℂ).re + ‖u‖ ^ 2 := by fun_prop
      have h0 := this.tendsto 0
      rw [hzero, one_apply_eq_self, inner_self_eq_norm_sq_to_K] at h0
      convert h0 using 2
      simp [← ofReal_pow]
      ring
    refine squeeze_zero (fun t => by positivity) (fun t => ?_) hup
    have h1 := norm_sub_sq (𝕜 := ℂ) (shift ha t u) u
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hle t u) 2
    have h3 : RCLike.re ⟪shift ha t u, u⟫_ℂ = (⟪u, shift ha t u⟫_ℂ).re := by
      rw [← inner_conj_symm u, conj_re]; rfl
    rw [h1, h3]
    linarith
  have h0 : Tendsto (fun t => shift ha t u) (𝓝 0) (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := hsq.sqrt
    simpa using this
  have h1 : Tendsto (fun y => shift ha y₀ (shift ha (y - y₀) u)) (𝓝 y₀) (𝓝 (shift ha y₀ u)) := by
    refine ((shift ha y₀).continuous.tendsto u).comp (h0.comp ?_)
    have : Continuous fun y : ℝ => y - y₀ := by fun_prop
    simpa using this.tendsto y₀
  refine h1.congr fun y => ?_
  rw [← hadd, add_sub_cancel]

lemma moment_shift (ha : 0 < a) {z : ℂ} (hz : |z.re| < a) (m : ℕ) (u : W a)
    (h : ∀ l < m, moment hz l u = 0) (y : ℝ) :
    moment hz m (shift ha y u) = exp (z * y) * moment hz m u := by
  have hi : ∀ l, Integrable fun x : ℝ => u x * ((x : ℂ) ^ l * exp (z * x)) := fun l =>
    (((dual_of_mem ha u u).convAt hz).hasDerivAt l).1
  have e1 : moment hz m (shift ha y u) = ∫ x : ℝ, ∑ l ∈ Finset.range (m + 1),
      (exp (z * y) * ((y : ℂ) ^ (m - l) * (m.choose l : ℂ))) *
        (u x * ((x : ℂ) ^ l * exp (z * x))) := by
    rw [moment_apply, ← integral_add_right_eq_self _ y]
    refine integral_congr_ae ?_
    have h1 := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae
      (coeFn_shift ha y u)
    filter_upwards [h1] with x hx
    rw [hx, add_sub_cancel_right, ofReal_add, add_pow, mul_add, Complex.exp_add, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e1, integral_finsetSum _ fun l _ => (hi l).const_mul _, Finset.sum_range_succ,
    Finset.sum_eq_zero fun l hl => ?_]
  · rw [integral_const_mul, ← moment_apply hz]
    simp
  · rw [integral_const_mul, ← moment_apply hz, h l (Finset.mem_range.1 hl), mul_zero]

/-- The abstract convolution operator is the convolution integral. -/
lemma conv_ae (ha : 0 < a) (hk : Good a k) (u : W a) :
    conv (flow_shift ha) hk u =ᵐ[volume] fun x => ∫ y, k y * u (x - y) := by
  have hdual : ∀ (s : Set ℝ), MeasurableSet s → volume s < ∞ → ∀ f : W a,
      Dual a (s.indicator 1) f := fun s hs hfin f => by
    refine ⟨?_, (dual_of_mem ha 0 f).right⟩
    have h1 : MemLp (s.indicator fun _ => (1 : ℂ)) 2 volume :=
      memLp_indicator_const 2 hs 1 (Or.inr hfin.ne)
    refine h1.mono ?_ (Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => (Real.exp (-a * |x|) : ℂ)
        ).aestronglyMeasurable.mul ((aestronglyMeasurable_const (b := (1 : ℂ))).indicator hs)
    · rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
      nlinarith [abs_nonneg x]
  have hprod : ∀ (s : Set ℝ), MeasurableSet s → volume s < ∞ →
      Integrable (fun p : ℝ × ℝ => s.indicator (1 : ℝ → ℂ) p.1 * (k p.2 * u (p.1 - p.2)))
        (volume.prod volume) := fun s hs hfin => by
    obtain ⟨K, hK⟩ := (hdual s hs hfin u).crossBound ha.le
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => s.indicator (1 : ℝ → ℂ) p.1 *
        (k p.2 * u (p.1 - p.2))) (volume.prod volume) :=
      hK.aesm_left.comp_fst.mul (hk.aesm.comp_snd.mul
        (hK.aesm_right.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)))
    refine (integrable_prod_iff' hm).2 ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · simpa only [mul_left_comm] using (hK.integrable y).const_mul (k y)
    · refine (hk.norm.mul_const K).mono' hm.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      simp only [mul_left_comm _ (k y), norm_mul (k y)]
      rw [integral_const_mul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have := mul_le_mul_of_nonneg_left (hK.le y) (norm_nonneg (k y))
      linarith
  have hon : ∀ (s : Set ℝ), MeasurableSet s → volume s < ∞ → ∀ f : W a,
      IntegrableOn f s := fun s hs hfin f => by
    obtain ⟨K, hK⟩ := (hdual s hs hfin f).crossBound ha.le
    refine (integrable_indicator_iff hs).1 ((hK.integrable 0).congr
      (Eventually.of_forall fun x => ?_))
    by_cases hx : x ∈ s <;> simp [hx]
  have hset : ∀ (s : Set ℝ) (f : ℝ → ℂ), MeasurableSet s →
      ∫ x in s, f x = ∫ x, s.indicator (1 : ℝ → ℂ) x * f x := fun s f hs => by
    rw [← integral_indicator hs]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ s <;> simp [hx]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s hs hfin => hon s hs hfin _)
    (fun s hs hfin => ?_) fun s hs hfin => ?_
  · have h := (hprod s hs hfin).integral_prod_left
    refine (integrable_indicator_iff hs).1 (h.congr (Eventually.of_forall fun x => ?_))
    simp only [integral_const_mul]
    by_cases hx : x ∈ s <;> simp [hx]
  · set g : ℝ → ℂ := fun x => s.indicator (1 : ℝ → ℂ) x / ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ)
    have hg : MemLp g 2 (wt a) := by
      have h1 : Integrable (s.indicator fun _ => (1 : ℝ)) :=
        (integrable_indicator_iff hs).2 (integrableOn_const hfin.ne)
      refine memLp_wt ?_ h1 fun x => ?_
      · have : Continuous fun x : ℝ => (((2 * Real.cosh (2 * a * x) : ℝ) : ℂ))⁻¹ := by
          refine Continuous.inv₀ (by fun_prop) fun x => ofReal_ne_zero.2 (by positivity)
        exact ((aestronglyMeasurable_const (b := (1 : ℂ))).indicator hs).mul
          this.aestronglyMeasurable
      · by_cases hx : x ∈ s
        · have := Real.one_le_cosh (2 * a * x)
          have hp : 0 < 2 * Real.cosh (2 * a * x) := by positivity
          simp only [g, indicator_of_mem hx, norm_div, norm_real, Real.norm_of_nonneg hp.le]
          simp only [Pi.one_apply, norm_one]
          rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
          nlinarith
        · simp [g, hx]
    have hL : ∀ f : W a, ⟪hg.toLp, f⟫_ℂ = ∫ x, s.indicator (1 : ℝ → ℂ) x * f x := fun f => by
      rw [inner_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [ae_wt_iff.1 hg.coeFn_toLp] with x hx
      have hp : ((2 * Real.cosh (2 * a * x) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
      rw [hx]
      simp only [g, map_div₀, conj_ofReal]
      rw [mul_div_cancel₀ _ hp]
      by_cases hx : x ∈ s <;> simp [hx]
    have h := map_conv (flow_shift ha) hk (innerSL ℂ hg.toLp) u
    simp only [innerSL_apply_apply, hL] at h
    rw [hset s _ hs, hset s _ hs, h]
    simp only [← integral_const_mul]
    rw [integral_integral_swap (hprod s hs hfin)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_shift ha y u] with x hx
    rw [hx]
    ring

end Translation

/-! ### Compressions -/

section Compression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : Submodule ℂ H} {A B : H →L[ℂ] H}

/-- The compression of `A` to `Uᗮ`. When `A` preserves a closed `U` it is the operator induced on
the quotient by `U`. -/
noncomputable def compr (U : Submodule ℂ H) (A : H →L[ℂ] H) : Uᗮ →L[ℂ] Uᗮ :=
  Uᗮ.orthogonalProjectionOnto ∘L A ∘L Uᗮ.subtypeL

lemma inner_compr (x y : Uᗮ) : ⟪x, compr U A y⟫_ℂ = ⟪(x : H), A y⟫_ℂ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x (A y)

lemma norm_compr_le (x : Uᗮ) : ‖compr U A x‖ ≤ ‖A x‖ :=
  Uᗮ.norm_orthogonalProjectionOnto_apply_le (A x)

variable [U.HasOrthogonalProjection]

lemma sub_compr_mem (x : Uᗮ) : A x - compr U A x ∈ U := by
  have h := Uᗮ.sub_starProjection_mem_orthogonal (A x)
  rwa [Submodule.orthogonal_orthogonal] at h

/-- The operator induced on the quotient is unique. -/
lemma eq_compr {S : Uᗮ →L[ℂ] Uᗮ} (h : ∀ x : Uᗮ, A x - S x ∈ U) : S = compr U A := by
  ext x
  have h1 := U.sub_mem (h x) (sub_compr_mem (A := A) x)
  rw [sub_sub_sub_cancel_left] at h1
  have h2 := Submodule.inner_right_of_mem_orthogonal h1 (compr U A x - S x).2
  rw [Submodule.coe_sub, inner_self_eq_zero, sub_eq_zero] at h2
  exact h2.symm

lemma compr_comp (hA : ∀ u ∈ U, A u ∈ U) : compr U (A ∘L B) = compr U A ∘L compr U B := by
  refine (eq_compr fun x => ?_).symm
  have h1 := hA _ (sub_compr_mem (A := B) x)
  have h2 := U.add_mem h1 (sub_compr_mem (A := A) (compr U B x))
  rw [map_sub, sub_add_sub_cancel] at h2
  exact h2

end Compression

/-! ### The functionals of the zeros -/

section Zeros

variable {a : ℝ} {k : ℝ → ℂ}

instance : CompleteSpace (V a) := by unfold V; infer_instance

/-- Zeros at distance less than `a` from the critical line, repeated by multiplicity. -/
abbrev Index (a : ℝ) := Σ ρ : innerZeros a, Fin (zeroMult ρ)

instance : Countable (innerZeros a) :=
  (countable_zeros.mono fun _ h => mem_riemannZetaZeros.2 h.1).to_subtype

/-- A listing of the functionals in which those of one zero come in increasing order. -/
noncomputable def code (i : Index a) : ℕ :=
  Nat.pair ((Encodable.ofCountable (innerZeros a)).encode i.1) i.2

lemma code_injective : (code (a := a)).Injective := by
  rintro ⟨ρ, m⟩ ⟨ρ', m'⟩ h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 h
  obtain rfl := (Encodable.ofCountable (innerZeros a)).encode_injective h1
  exact congrArg _ (Fin.ext h2)

lemma code_lt {ρ : innerZeros a} {l m : Fin (zeroMult ρ)} (h : l < m) :
    code ⟨ρ, l⟩ < code ⟨ρ, m⟩ := Nat.pair_lt_pair_right _ h

/-- The functional of an index. -/
noncomputable abbrev func (i : Index a) : W a →L[ℂ] ℂ := moment (abs_re_lt_of_mem i.1.2) i.2

lemma mem_V_iff (ha : 0 < a) {u : W a} : u ∈ V a ↔ ∀ i, func i u = 0 := by
  rw [V_eq_J ha, mem_ideal]
  exact ⟨fun h i => h _ i.1.2 _ i.2.2, fun h ρ hρ m hm => h ⟨⟨ρ, hρ⟩, ⟨m, hm⟩⟩⟩

/-- The Riesz representative of a functional, in `(V a)ᗮ`. -/
noncomputable def vec (ha : 0 < a) (i : Index a) : (V a)ᗮ :=
  ⟨(memLp_kernel (abs_re_lt_of_mem i.1.2) i.2).toLp, fun u hu => by
    rw [← inner_conj_symm]
    exact (map_eq_zero _).2 ((mem_V_iff ha).1 hu i)⟩

lemma inner_vec (ha : 0 < a) (i : Index a) (u : W a) : ⟪(vec ha i : W a), u⟫_ℂ = func i u := rfl

/-- The functionals are independent: each is nonzero on a function that the other zeros and the
lower orders do not see. -/
lemma exists_separating (ha : 0 < a) (i : Index a) : ∃ u : W a, func i u ≠ 0 ∧
    ∀ j, code j < code i → func j u = 0 := by
  obtain ⟨⟨ρ, hρ⟩, m, hm⟩ := i
  set c := ρ - 1 / 2
  have hord : ∀ (n : ℕ) (u : ℝ → ℂ), Rapid u → (∀ z, (z - c) ^ n * jet u 0 z = xi z) →
      ∀ ρ' ∈ innerZeros a, analyticOrderAt (fun w => (w - c) ^ n) (ρ' - 1 / 2) +
        analyticOrderAt (jet u 0) (ρ' - 1 / 2) = zeroMult ρ' := fun n u hu h ρ' hρ' => by
    rw [← analyticOrderAt_mul (by fun_prop) (hu.convAt _).analyticAt,
      ← analyticOrderAt_xi_of_mem hρ']
    exact analyticOrderAt_congr (Eventually.of_forall h)
  have hone : analyticOrderAt (fun w => w - c) c = 1 :=
    AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by fun_prop) (by simp) (by simp)
  have hpow : ∀ n : ℕ, analyticOrderAt (fun w => (w - c) ^ n) c = n := fun n => by
    have := analyticOrderAt_pow (f := fun w => w - c) (z₀ := c) (by fun_prop) n
    rw [hone, nsmul_one] at this
    exact this
  have hdiv : ∀ n ≤ zeroMult ρ, ∃ u, Rapid u ∧ ∀ z, (z - c) ^ n * jet u 0 z = xi z := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨_, rapid_theta_seed, fun z => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨u, hu, h⟩ := ih (by omega)
      have h0 : jet u 0 c = 0 := by
        refine apply_eq_zero_of_analyticOrderAt_ne_zero fun e => ?_
        have h1 := hord n u hu h ρ hρ
        rw [hpow, e, add_zero] at h1
        have : n = zeroMult ρ := by exact_mod_cast h1
        omega
      obtain ⟨u', hu', h'⟩ := exists_divided hu h0
      exact ⟨u', hu', fun z => by rw [pow_succ, mul_assoc, h', h]⟩
  obtain ⟨u, hu, h⟩ := hdiv (zeroMult ρ - m) (Nat.sub_le _ _)
  have hL := hu.memLp ha
  have hmom : ∀ {z : ℂ} (hz : |z.re| < a) (m : ℕ), moment hz m hL.toLp =
      iteratedDeriv m (jet u 0) z := fun {z} hz m => by
    rw [moment_apply, (hu.convAt z.re).iteratedDeriv, jet]
    refine integral_congr_ae ?_
    filter_upwards [ae_wt_iff.1 hL.coeFn_toLp] with x hx
    rw [hx]
  have hm' : m < zeroMult ρ := hm
  have hρm : analyticOrderAt (jet u 0) c = m := by
    have h1 := hord _ u hu h ρ hρ
    rw [hpow] at h1
    change _ + analyticOrderAt (jet u 0) c = _ at h1
    generalize analyticOrderAt (jet u 0) c = o at h1 ⊢
    induction o using ENat.recTopCoe with
    | top => simp at h1
    | coe o =>
      have : zeroMult ρ - m + o = zeroMult ρ := by exact_mod_cast h1
      exact_mod_cast (by omega : o = m)
  have hder := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hu.convAt c.re).analyticAt).1 hρm
  refine ⟨hL.toLp, ?_, ?_⟩
  · exact (hmom (abs_re_lt_of_mem hρ) m).trans_ne hder.2
  · rintro ⟨⟨ρ', hρ'⟩, l, hl⟩ hlt
    refine (hmom (abs_re_lt_of_mem hρ') l).trans ?_
    rcases eq_or_ne ρ' ρ with rfl | hne
    · refine hder.1 l (not_le.1 fun hml => hlt.not_ge ?_)
      rcases hml.lt_or_eq with h1 | rfl
      · exact (code_lt (a := a) (ρ := ⟨ρ', hρ'⟩) (l := ⟨m, hm⟩) (m := ⟨l, hl⟩) h1).le
      · exact le_rfl
    · have h1 := hord _ u hu h ρ' hρ'
      rw [(by fun_prop : AnalyticAt ℂ (fun w => (w - c) ^ (zeroMult ρ - m)) (ρ' - 1 / 2)
        ).analyticOrderAt_eq_zero.2 (pow_ne_zero _ (by simpa [c, sub_eq_zero] using hne)),
        zero_add] at h1
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (hu.convAt _).analyticAt).1 h1.ge l hl

/-- `V a` is invariant under translations. -/
lemma shift_mem (ha : 0 < a) (y : ℝ) {u : W a} (hu : u ∈ V a) : shift ha y u ∈ V a := by
  rw [mem_V_iff ha] at hu ⊢
  intro i
  have h := moment_shift ha (abs_re_lt_of_mem i.1.2) i.2 u
    (fun l hl => hu ⟨i.1, ⟨l, hl.trans i.2.2⟩⟩) y
  rw [h, hu i, mul_zero]

lemma conv_mem_V (ha : 0 < a) (hk : Good a k) {u : W a} (hu : u ∈ V a) :
    conv (flow_shift ha) hk u ∈ V a := conv_mem _ _ (fun y _ hv => shift_mem ha y hv) hu

/-- An orthonormal basis of `(V a)ᗮ` in which every induced convolution operator has diagonal
`k̂(ρ - 1/2)`. -/
theorem exists_basis_diagonal (ha : 0 < a) : ∃ b : HilbertBasis (Index a) ℂ (V a)ᗮ,
    ∀ (k : ℝ → ℂ) (hk : Good a k) (i : Index a),
      ⟪b i, compr (V a) (conv (flow_shift ha) hk) (b i)⟫_ℂ = jet k 0 ((i.1 : ℂ) - 1 / 2) := by
  obtain ⟨b, hb⟩ := exists_adapted_basis (vec ha) code code_injective (fun x hx => by
      have h1 : (x : W a) ∈ V a := (mem_V_iff ha).2 hx
      exact Subtype.ext (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 x.2)))
    fun i => by
      obtain ⟨u, h1, h2⟩ := exists_separating ha i
      have e : ∀ j, ⟪vec ha j, (V a)ᗮ.orthogonalProjectionOnto u⟫_ℂ = func j u := fun j =>
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _
      exact ⟨_, by rwa [e], fun j hj => by rw [e, h2 j hj]⟩
  refine ⟨b, fun k hk i => ?_⟩
  refine diagonal_eq (v := vec ha) (l := fun i => jet k 0 ((i.1 : ℂ) - 1 / 2)) (hb i).1 (hb i).2
    code_injective fun i x hx => ?_
  rw [inner_compr, inner_vec]
  exact character_conv _ hk (func i) fun y => moment_shift ha (abs_re_lt_of_mem i.1.2) i.2 x
    (fun l hl => hx ⟨i.1, ⟨l, hl.trans i.2.2⟩⟩ (code_lt hl)) y

/-! ### The trace -/

lemma summable_index (ha : 0 < a) {c : ℝ} (hc : c = a + 1) :
    Summable fun i : Index a => (1 / ((c : ℂ) - ((i.1 : ℂ) - 1 / 2))).re := by
  subst hc
  have hS := Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam
  have h1 : Summable fun ρ : innerZeros a =>
      (zeroMult ρ : ℝ) / (1 + Complex.normSq (((ρ : ℂ) - 1 / 2) / I)) := by
    have hi : ∀ ρ : innerZeros a, (ρ : ℂ) ∈ (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
      fun ρ => ⟨ρ.2.1, ρ.2.2.1, ρ.2.2.2.1⟩
    have hinj : Function.Injective fun ρ : innerZeros a =>
        (⟨ρ, hi ρ⟩ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier) := fun x y h =>
      Subtype.ext (Subtype.mk.inj h)
    refine (hS.comp_injective hinj).congr fun ρ => ?_
    have e1 : zeroMult (ρ : ℂ) = Zeta23.zeroMult ρ := rfl
    simp only [Function.comp_apply, e1, Zeta23.gammaOf]
  have hpos : ∀ i : Index a, 1 ≤ a + 1 - ((i.1 : ℂ) - 1 / 2).re := fun i => by
    linarith [(abs_lt.1 (abs_re_lt_of_mem i.1.2)).2]
  have hnn : ∀ i : Index a, 0 ≤ (1 / (((a + 1 : ℝ) : ℂ) - ((i.1 : ℂ) - 1 / 2))).re := fun i => by
    rw [one_div, inv_re, sub_re, ofReal_re]
    exact div_nonneg (by linarith [hpos i]) (normSq_nonneg _)
  have h2 : Summable fun i : Index a =>
      1 / (1 + Complex.normSq (((i.1 : ℂ) - 1 / 2) / I)) := by
    refine (summable_sigma_of_nonneg fun i =>
      one_div_nonneg.2 (add_nonneg zero_le_one (normSq_nonneg _))).2 ⟨fun ρ => .of_finite, ?_⟩
    refine h1.congr fun ρ => ?_
    simp [tsum_fintype, div_eq_mul_inv]
  refine (h2.mul_left ((2 * a + 1) * (a ^ 2 + 1))).of_nonneg_of_le hnn fun i => ?_
  have hz := abs_lt.1 (abs_re_lt_of_mem i.1.2)
  have h3 := hpos i
  generalize (i.1 : ℂ) - 1 / 2 = z at hz h3 ⊢
  have e : normSq (z / I) = z.re ^ 2 + z.im ^ 2 := by
    rw [normSq_div, normSq_I, div_one, normSq_apply]; ring
  rw [one_div, inv_re, sub_re, ofReal_re, e, normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im,
    mul_one_div]
  have hzr : z.re ^ 2 ≤ a ^ 2 := by nlinarith [hz.1, hz.2]
  rw [div_le_div_iff₀ (by nlinarith [sq_nonneg z.im]) (by positivity)]
  have h4 : a + 1 - z.re ≤ 2 * a + 1 := by linarith [hz.1]
  have h5 : 1 + (z.re ^ 2 + z.im ^ 2) ≤ (a ^ 2 + 1) *
      ((a + 1 - z.re) * (a + 1 - z.re) + (0 - z.im) * (0 - z.im)) := by
    nlinarith [sq_nonneg z.im, sq_nonneg a, mul_nonneg (sq_nonneg a) (sq_nonneg z.im),
      mul_nonneg (sq_nonneg a) (by nlinarith : 0 ≤ (a + 1 - z.re) * (a + 1 - z.re) - 1)]
  rw [mul_assoc]
  exact mul_le_mul h4 h5 (by positivity) (by linarith)

lemma good_of_compact (hk : Continuous k) (hs : HasCompactSupport k) : Good a k :=
  (by fun_prop : Continuous fun x : ℝ => (Real.exp (a * |x|) : ℂ) * k x
    ).integrable_of_hasCompactSupport hs.mul_left

/-- **The trace formula on `W a / V a`**, for every twice differentiable kernel with compact
support. -/
theorem hasTrace_conv (ha : 0 < a) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    Summable (fun ρ : innerZeros a => (zeroMult ρ : ℂ) * jet k 0 ((ρ : ℂ) - 1 / 2)) ∧
      HasTrace (compr (V a) (conv (flow_shift ha) (good_of_compact hk.continuous hs)))
        (∑' ρ : innerZeros a, (zeroMult ρ : ℂ) * jet k 0 ((ρ : ℂ) - 1 / 2)) := by
  set c := a + 1
  have hc : a < c := by simp [c]
  have hstep : ∀ {n : ℕ} {f : ℝ → ℂ}, ContDiff ℝ (n + 1 : ℕ) f → HasCompactSupport f →
      ContDiff ℝ n (fun x => c * f x + deriv f x) ∧
        HasCompactSupport fun x => c * f x + deriv f x := fun {n f} hf hfs =>
    ⟨(contDiff_const.mul (hf.of_le (by exact_mod_cast n.le_succ))).add
      (contDiff_succ_iff_deriv.1 (by exact_mod_cast hf)).2.2,
      HasCompactSupport.add hfs.mul_left hfs.deriv⟩
  obtain ⟨hk1, hs1⟩ := hstep (n := 1) hk hs
  obtain ⟨hk2, hs2⟩ := hstep (n := 0) hk1 hs1
  set hτ := flow_shift ha
  set R := conv hτ (good_resolvent hc)
  set B := conv hτ (good_of_compact hk2.continuous hs2)
  have hR : ∀ u ∈ V a, R u ∈ V a := fun u => conv_mem_V ha _
  have hB : ∀ u ∈ V a, B u ∈ V a := fun u => conv_mem_V ha _
  have hA : conv hτ (good_of_compact hk.continuous hs) = R ∘L (R ∘L B) := by
    rw [conv_resolvent hτ hc (hk.of_le (by norm_num)) hs _
      (good_of_compact hk1.continuous hs1), conv_resolvent hτ hc hk1 hs1 _
      (good_of_compact hk2.continuous hs2)]
  have hRB : R ∘L B = B ∘L R := ContinuousLinearMap.ext fun u => conv_comm hτ _ _ u
  obtain ⟨b, hb⟩ := exists_basis_diagonal ha
  have hHS : Summable fun i => ‖compr (V a) R (b i)‖ ^ 2 := by
    refine (summable_index ha rfl).of_nonneg_of_le (fun _ => by positivity) fun i => ?_
    have h1 := resolvent_le hτ hc (b i : W a)
    rw [← inner_compr, hb, jet_resolvent] at h1
    · have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_compr_le (A := R) (b i)) 2
      rw [show c - a = 1 by simp [c], one_mul] at h1
      exact h2.trans h1
    · exact ((abs_lt.1 (abs_re_lt_of_mem i.1.2)).2).trans hc
  have hHS2 : Summable fun i => ‖compr (V a) (R ∘L B) (b i)‖ ^ 2 := by
    refine (hHS.mul_left (‖compr (V a) B‖ ^ 2)).of_nonneg_of_le (fun _ => by positivity)
      fun i => ?_
    rw [hRB, compr_comp hB, ← mul_pow]
    gcongr
    exact (compr (V a) B).le_opNorm _
  have hdiag := fun i => hb k (good_of_compact hk.continuous hs) i
  rw [hA, compr_comp hR] at hdiag ⊢
  have hsum : Summable fun i : Index a => jet k 0 ((i.1 : ℂ) - 1 / 2) := by
    have e : ∀ i, jet k 0 ((i.1 : ℂ) - 1 / 2) =
        ⟪ContinuousLinearMap.adjoint (compr (V a) R) (b i), compr (V a) (R ∘L B) (b i)⟫_ℂ :=
      fun i => by rw [ContinuousLinearMap.adjoint_inner_left]; exact (hdiag i).symm
    simp only [e]
    refine ((summable_sq_adjoint b hHS).add hHS2).of_norm_bounded fun i => ?_
    refine (norm_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint (compr (V a) R) (b i)‖ -
      ‖compr (V a) (R ∘L B) (b i)‖), norm_nonneg (compr (V a) (R ∘L B) (b i)),
      norm_nonneg (ContinuousLinearMap.adjoint (compr (V a) R) (b i))]
  have hfib : ∀ ρ : innerZeros a, HasSum (fun _ : Fin (zeroMult ρ) => jet k 0 ((ρ : ℂ) - 1 / 2))
      ((zeroMult ρ : ℂ) * jet k 0 ((ρ : ℂ) - 1 / 2)) := fun ρ => by
    have h := hasSum_fintype fun _ : Fin (zeroMult ρ) => jet k 0 ((ρ : ℂ) - 1 / 2)
    simpa using h
  have hz := hsum.hasSum.sigma hfib
  refine ⟨hz.summable, .of_basis b hHS hHS2 ?_⟩
  rw [hz.tsum_eq]
  simpa only [hdiag] using hsum.hasSum

end Zeros

/-! ### Test functions -/

section TestFunctions

variable {a : ℝ} {φ : TestFunction}

lemma jet_pull (φ : TestFunction) (z : ℂ) : jet φ.pull 0 z = φ.hat z := by
  rw [← TestFunction.paperFT_pull, jet_zero, Zeta23.paperFT]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_div_cancel₀ _ I_ne_zero]

/-- Convolution by `φ` in the logarithmic variable, on `W a`. -/
noncomputable def scaling (ha : 0 < a) (φ : TestFunction) : W a →L[ℂ] W a :=
  conv (flow_shift ha) (good_of_compact φ.pull_contDiff.continuous φ.pull_hasCompactSupport)

/-- `scaling φ` is the convolution integral. -/
theorem scaling_ae (ha : 0 < a) (φ : TestFunction) (u : W a) :
    scaling ha φ u =ᵐ[volume] fun x => ∫ y, φ.pull y * u (x - y) := conv_ae ha _ u

/-- `V a` is invariant. -/
theorem scaling_mem (ha : 0 < a) (φ : TestFunction) {u : W a} (hu : u ∈ V a) :
    scaling ha φ u ∈ V a := conv_mem_V ha _ hu

/-- The operator induced by `scaling φ` on `W a / V a`, realised on `(V a)ᗮ`. -/
noncomputable def induced (ha : 0 < a) (φ : TestFunction) : (V a)ᗮ →L[ℂ] (V a)ᗮ :=
  compr (V a) (scaling ha φ)

/-- `induced φ` is the only operator that agrees with `scaling φ` modulo `V a`. -/
theorem induced_unique (ha : 0 < a) {S : (V a)ᗮ →L[ℂ] (V a)ᗮ} :
    S = induced ha φ ↔ ∀ x : (V a)ᗮ, scaling ha φ x - S x ∈ V a :=
  ⟨fun h x => h ▸ sub_compr_mem x, eq_compr⟩

/-- **Theorem T.** The induced operator is a product of two Hilbert-Schmidt operators, and its
trace is the sum over the zeros at distance less than `a` from the critical line. -/
theorem exists_hasTrace_induced (ha : 0 < a) (φ : TestFunction) :
    ∃ t : ℂ, HasTrace (induced ha φ) t ∧
      HasSum (fun ρ : innerZeros a => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) t := by
  have h := hasTrace_conv ha φ.pull_contDiff φ.pull_hasCompactSupport
  simp only [jet_pull] at h
  exact ⟨_, h.2, h.1.hasSum⟩

/-- The diagonal in any Hilbert basis sums to the sum over zeros. -/
theorem hasSum_diagonal (ha : 0 < a) (φ : TestFunction) {κ : Type*}
    (b : HilbertBasis κ ℂ (V a)ᗮ) : HasSum (fun i => ⟪b i, induced ha φ (b i)⟫_ℂ)
      (∑' ρ : innerZeros a, (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) := by
  obtain ⟨t, h1, h2⟩ := exists_hasTrace_induced ha φ
  exact h2.tsum_eq ▸ h1.hasSum b

lemma HasTrace.unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} {s t : ℂ} (hs : HasTrace T s) (ht : HasTrace T t) : s = t := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  exact (hs.2 w b).unique (ht.2 w b)

/-- At `a = 1/2` the trace is the functional of Weil's explicit formula. -/
theorem hasTrace_induced_half (φ : TestFunction) :
    HasTrace (induced (a := 1 / 2) (by norm_num) φ) φ.efFunctional := by
  obtain ⟨t, h1, h2⟩ := exists_hasTrace_induced (a := 1 / 2) (by norm_num) φ
  have e : innerZeros (1 / 2) = stripZeros := by
    ext ρ
    refine ⟨fun h => ⟨h.1, h.2.1, h.2.2.1⟩, fun h => ⟨h.1, h.2.1, h.2.2, ?_⟩⟩
    rw [abs_lt]
    constructor <;> linarith [h.2.1, h.2.2]
  rw [e] at h2
  exact h2.unique φ.hasSum_full ▸ h1

/-! ### Negative control -/

/-- The traces determine the multiplicities: a zero expansion with any other weight at any zero, in
particular one that drops a zero, fails to be the trace for some test function. -/
theorem weights_unique (ha : 0 < a) {n : ℂ → ℂ} {t : TestFunction → ℂ}
    (ht : ∀ φ, HasTrace (induced ha φ) (t φ)) :
    (∀ φ : TestFunction,
      HasSum (fun ρ : innerZeros a => n ρ * φ.hat ((ρ : ℂ) - 1 / 2)) (t φ)) ↔
      ∀ ρ ∈ innerZeros a, n ρ = zeroMult ρ := by
  have hz : ∀ φ : TestFunction,
      HasSum (fun ρ : innerZeros a => (zeroMult ρ : ℂ) * φ.hat ((ρ : ℂ) - 1 / 2)) (t φ) :=
    fun φ => by
      obtain ⟨s, h1, h2⟩ := exists_hasTrace_induced ha φ
      exact h1.unique (ht φ) ▸ h2
  refine ⟨fun h ρ hρ => ?_, fun h φ => (hz φ).congr_fun fun ρ => by rw [h ρ ρ.2]⟩
  obtain ⟨φ, hφ⟩ := TestFunction.exists_hat_ne_zero (ρ - 1 / 2)
  have key := eq_zero_of_hasSum_exp (l := fun ρ : innerZeros a => (ρ : ℂ) - 1 / 2)
    (c := fun ρ => (n ρ - zeroMult ρ) * φ.hat ((ρ : ℂ) - 1 / 2)) (B := 1 / 2)
    (fun x y e => Subtype.ext (sub_left_injective e))
    (fun ρ => by
      have := ρ.2.2.2.1
      norm_num
      linarith)
    (fun z => by
      obtain ⟨r, hr, hiso⟩ := exists_isolating_radius (z + 1 / 2)
      refine ⟨r, hr, fun ρ hne => ?_⟩
      have := hiso ρ ρ.2.1 fun e => hne (by rw [e]; ring)
      rwa [show z - ((ρ : ℂ) - 1 / 2) = z + 1 / 2 - ρ by ring])
    (fun x hx => by
      have := (h (φ.translate x hx)).sub (hz (φ.translate x hx))
      simp_rw [TestFunction.hat_translate, sub_self] at this
      exact this.congr_fun fun ρ => by ring) ⟨ρ, hρ⟩
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hφ)

end TestFunctions

end Masullo.Trace
