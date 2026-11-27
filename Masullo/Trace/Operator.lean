import Masullo.Synthesis.Duality

/-!
# Trace class convolution over a flow

A flow on a Hilbert space is a strongly continuous group with `‖τ_t u‖ ≤ e^{a|t|} ‖u‖`. For `c > a`
the resolvent `R`, convolution by `e^{-cx}` on `x > 0`, satisfies `(c - a) ‖R u‖² ≤ Re ⟪u, R u⟫`.
If one orthonormal basis of `Uᗮ`, for an invariant `U`, gives the compressed convolutions the
diagonal `k̂(l i)`, then `(c - a) ‖R b_i‖² ≤ Re 1 / (c - l i)`. When the right hand side is summable
the compression of `R` is Hilbert-Schmidt, and convolution by a `C²` kernel with compact support,
which is `R ∘ R` times a bounded operator, is trace class. This is `hasTrace_conv_of_diagonal`.
The exponents `l i` may be anywhere in `Re z < c`.

`exists_adapted_basis` and `diagonal_eq` produce such a diagonal from a total independent family of
functionals on which the operators act triangularly.

Hilbert-Schmidt and trace class operators, Gram-Schmidt triangularisation and dissipative resolvents
are standard (recalled; no source was consulted).
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace Masullo.Trace

open Synthesis

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

/-- The trace is the sum of the diagonal in any basis. -/
lemma HasTrace.hasSum {T : H →L[ℂ] H} {t : ℂ} (hT : HasTrace T t) (b : HilbertBasis ι ℂ H) :
    HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) t := by
  obtain ⟨⟨A, B, hA, hB, rfl⟩, h⟩ := hT
  obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ H
  have e : ∀ x, ⟪x, (A ∘L B) x⟫_ℂ = ⟪ContinuousLinearMap.adjoint A x, B x⟫_ℂ := fun x =>
    (ContinuousLinearMap.adjoint_inner_left A _ _).symm
  have h1 := h w c
  simp only [e] at h1 ⊢
  exact hasSum_inner_congr c b (summable_sq_adjoint c (hA w c)) (hB w c) h1

lemma HasTrace.unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} {s t : ℂ} (hs : HasTrace T s) (ht : HasTrace T t) : s = t := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  exact (hs.2 w b).unique (ht.2 w b)

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
  aesm_of_exp_mul hk.aestronglyMeasurable

omit [CompleteSpace H] in
lemma Good.integrable (hk : Good a k) (hτ : Flow a τ) (u : H) :
    Integrable fun y => k y • τ y u := by
  refine (hk.norm.mul_const ‖u‖).mono' (hk.aesm.smul (hτ.cont u).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have := mul_le_mul_of_nonneg_left (hτ.norm_le y u) (norm_nonneg (k y))
  linarith

/-- The convolution operator `u ↦ ∫ k(y) τ_y u dy`, a Bochner integral in `H` for each fixed `u`. -/
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
  rw [map_conv, jet_zero, ← integral_mul_const]
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

lemma good_of_compact (hk : Continuous k) (hs : HasCompactSupport k) : Good a k :=
  (by fun_prop : Continuous fun x : ℝ => (Real.exp (a * |x|) : ℂ) * k x
    ).integrable_of_hasCompactSupport hs.mul_left

lemma jet_resolvent {z : ℂ} (hz : z.re < c) : jet (resolvent c) 0 z = 1 / (c - z) := by
  have h : (-(c : ℂ) + z).re < 0 := by simpa using hz
  rw [resolvent, jet_pos_exp h, neg_div, one_div, one_div, ← inv_neg]
  congr 1
  ring

/-- Dissipativity: `Re 1 / (c - z) ≥ (c - a) |1 / (c - z)|²` for `|Re z| ≤ a`, in operator form. -/
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

/-- **Trace class criterion.** Let the flow preserve `U`, let one orthonormal basis of `Uᗮ` give
every compressed convolution the diagonal `k̂(l i)`, and let `Re 1 / (c - l i)`, the diagonal of a
resolvent, be summable. Then convolution by a `C²` kernel with compact support compresses to a
product of two Hilbert-Schmidt operators, with trace the absolutely convergent sum of `k̂(l i)`. -/
theorem hasTrace_conv_of_diagonal {ι : Type*} {a c : ℝ} {τ : ℝ → H →L[ℂ] H} (hτ : Flow a τ)
    (hU : ∀ y, ∀ u ∈ U, τ y u ∈ U) (b : HilbertBasis ι ℂ Uᗮ) {l : ι → ℂ}
    (hb : ∀ (k : ℝ → ℂ) (hk : Good a k) (i : ι),
      ⟪b i, compr U (conv hτ hk) (b i)⟫_ℂ = jet k 0 (l i))
    (hc : a < c) (hl : ∀ i, (l i).re < c) (hsum : Summable fun i => (1 / ((c : ℂ) - l i)).re)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    Summable (fun i => jet k 0 (l i)) ∧
      HasTrace (compr U (conv hτ (good_of_compact hk.continuous hs))) (∑' i, jet k 0 (l i)) := by
  have hstep : ∀ {n : ℕ} {f : ℝ → ℂ}, ContDiff ℝ (n + 1 : ℕ) f → HasCompactSupport f →
      ContDiff ℝ n (fun x => c * f x + deriv f x) ∧
        HasCompactSupport fun x => c * f x + deriv f x := fun {n f} hf hfs =>
    ⟨(contDiff_const.mul (hf.of_le (by exact_mod_cast n.le_succ))).add
      (contDiff_succ_iff_deriv.1 (by exact_mod_cast hf)).2.2,
      HasCompactSupport.add hfs.mul_left hfs.deriv⟩
  obtain ⟨hk1, hs1⟩ := hstep (n := 1) hk hs
  obtain ⟨hk2, hs2⟩ := hstep (n := 0) hk1 hs1
  set R := conv hτ (good_resolvent hc)
  set B := conv hτ (good_of_compact hk2.continuous hs2)
  have hR : ∀ u ∈ U, R u ∈ U := fun u => conv_mem hτ _ hU
  have hB : ∀ u ∈ U, B u ∈ U := fun u => conv_mem hτ _ hU
  have hA : conv hτ (good_of_compact hk.continuous hs) = R ∘L (R ∘L B) := by
    rw [conv_resolvent hτ hc (hk.of_le (by norm_num)) hs _
      (good_of_compact hk1.continuous hs1), conv_resolvent hτ hc hk1 hs1 _
      (good_of_compact hk2.continuous hs2)]
  have hRB : R ∘L B = B ∘L R := ContinuousLinearMap.ext fun u =>
    conv_comm hτ (good_resolvent hc) (good_of_compact hk2.continuous hs2) u
  have hHS : Summable fun i => ‖compr U R (b i)‖ ^ 2 := by
    refine (hsum.mul_left (c - a)⁻¹).of_nonneg_of_le (fun _ => by positivity) fun i => ?_
    have h1 := resolvent_le hτ hc (b i : H)
    rw [← inner_compr, hb, jet_resolvent (hl i)] at h1
    rw [le_inv_mul_iff₀ (sub_pos.2 hc)]
    refine le_trans ?_ h1
    have := norm_compr_le (A := R) (b i)
    have := sub_pos.2 hc
    gcongr
  have hHS2 : Summable fun i => ‖compr U (R ∘L B) (b i)‖ ^ 2 := by
    refine (hHS.mul_left (‖compr U B‖ ^ 2)).of_nonneg_of_le (fun _ => by positivity) fun i => ?_
    rw [hRB, compr_comp hB, ← mul_pow]
    gcongr
    exact (compr U B).le_opNorm _
  have hdiag := fun i => hb k (good_of_compact hk.continuous hs) i
  rw [hA, compr_comp hR] at hdiag ⊢
  have hS : Summable fun i => jet k 0 (l i) := by
    have e : ∀ i, jet k 0 (l i) =
        ⟪ContinuousLinearMap.adjoint (compr U R) (b i), compr U (R ∘L B) (b i)⟫_ℂ :=
      fun i => by rw [ContinuousLinearMap.adjoint_inner_left]; exact (hdiag i).symm
    simp only [e]
    refine ((summable_sq_adjoint b hHS).add hHS2).of_norm_bounded fun i => ?_
    refine (norm_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint (compr U R) (b i)‖ -
      ‖compr U (R ∘L B) (b i)‖), norm_nonneg (compr U (R ∘L B) (b i)),
      norm_nonneg (ContinuousLinearMap.adjoint (compr U R) (b i))]
  exact ⟨hS, .of_basis b hHS hHS2 (by simpa only [hdiag] using hS.hasSum)⟩

end Compression

end Masullo.Trace
