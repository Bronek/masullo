import Masullo.Synthesis
import Masullo.ExplicitFormula
import WeilExplicit.ZeroSum
import Masullo.Trace.Operator

/-!
# The trace of scaling on the theta quotient

Convolution by a test function `φ` in the logarithmic variable is a bounded operator on `W a` that
preserves `V a`. For every `a > 0` the operator induced on `W a / V a`, realised on `(V a)ᗮ`, is a
product of two Hilbert-Schmidt operators, and its trace is the sum of `φ̂(ρ - 1/2)` over the zeros
at distance less than `a` from the critical line, with multiplicity. At `a = 1/2` the trace is the
functional of Weil's explicit formula. Nothing here restricts a zero: the zeros in the sum may lie
off the critical line, and the operator argument accepts any exponents in the strip.

`exists_basis_diagonal` lists the moments that cut out `V a` so that those of one zero come in
increasing order, and takes the Gram-Schmidt basis of `(V a)ᗮ`. In its proof the operators are
triangular; its statement is about the diagonal only. The trace class property is
`hasTrace_conv_of_diagonal` of `Masullo.Trace.Operator`, for `C²` kernels with compact support, with
the diagonal of the resolvent summed by the inverse-square zero sum
`WeilExplicit.summable_zeroMult_div_one_add_normSq`.

The realisation of the zeros on a theta quotient and the trace of scaling on it follow Connes (1999)
and Meyer (2005) (recalled; sources not consulted), in the weighted setting of Masullo. Weil's
explicit formula and the zero count are in `WeilExplicit`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace Masullo.Trace

open Spectrum Synthesis

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
  have e1 : moment hz m (shift ha y u) = jet (fun x => u (x - y)) m z := by
    rw [moment_apply, jet]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_shift ha y u] with x hx
    rw [hx]
  have e2 : ∀ l, jet u l z = moment hz l u := fun l => (moment_apply hz l u).symm
  simp only [e1, jet_translate hi, e2]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun l hl => by
    rw [h l (Finset.mem_range.1 hl), mul_zero]]
  simp

/-- The abstract convolution operator is the convolution integral, almost everywhere. -/
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

lemma code_le {i j : Index a} (hρ : j.1 = i.1) (h : (i.2 : ℕ) ≤ j.2) : code i ≤ code j := by
  rw [code, code, congrArg (Encodable.ofCountable (innerZeros a)).encode hρ]
  exact (strictMono_nat_of_lt_succ fun n => Nat.pair_lt_pair_right _ n.lt_succ_self).monotone h

/-- The functional of an index. -/
noncomputable abbrev func (i : Index a) : W a →L[ℂ] ℂ := moment (abs_re_lt_of_mem i.1.2) i.2

lemma mem_V_iff (ha : 0 < a) {u : W a} : u ∈ V a ↔ ∀ i, func i u = 0 := by
  rw [V_eq_J ha, mem_ideal]
  exact ⟨fun h i => h _ i.1.2 _ i.2.2, fun h ρ hρ m hm => h ⟨⟨ρ, hρ⟩, ⟨m, hm⟩⟩⟩

/-- The Riesz representative of a functional, in `(V a)ᗮ`. -/
noncomputable def vec (ha : 0 < a) (i : Index a) : (V a)ᗮ :=
  ⟨riesz (abs_re_lt_of_mem i.1.2) i.2, fun u hu => by
    rw [← inner_conj_symm]
    exact (map_eq_zero _).2 ((mem_V_iff ha).1 hu i)⟩

lemma inner_vec (ha : 0 < a) (i : Index a) (u : W a) : ⟪(vec ha i : W a), u⟫_ℂ = func i u := rfl

/-- `V a` is invariant under translations. -/
lemma shift_mem (ha : 0 < a) (y : ℝ) {u : W a} (hu : u ∈ V a) : shift ha y u ∈ V a := by
  rw [mem_V_iff ha] at hu ⊢
  intro i
  have h := moment_shift ha (abs_re_lt_of_mem i.1.2) i.2 u
    (fun l hl => hu ⟨i.1, ⟨l, hl.trans i.2.2⟩⟩) y
  rw [h, hu i, mul_zero]

lemma conv_mem_V (ha : 0 < a) (hk : Good a k) {u : W a} (hu : u ∈ V a) :
    conv (flow_shift ha) hk u ∈ V a := conv_mem _ _ (fun y _ hv => shift_mem ha y hv) hu

/-- One orthonormal basis of `(V a)ᗮ` in which every induced convolution operator has diagonal
`k̂(ρ - 1/2)`. Only the diagonal is stated: the basis is not claimed to consist of eigenvectors. -/
theorem exists_basis_diagonal (ha : 0 < a) : ∃ b : HilbertBasis (Index a) ℂ (V a)ᗮ,
    ∀ (k : ℝ → ℂ) (hk : Good a k) (i : Index a),
      ⟪b i, compr (V a) (conv (flow_shift ha) hk) (b i)⟫_ℂ = jet k 0 ((i.1 : ℂ) - 1 / 2) := by
  obtain ⟨b, hb⟩ := exists_adapted_basis (vec ha) code code_injective (fun x hx => by
      have h1 : (x : W a) ∈ V a := (mem_V_iff ha).2 hx
      exact Subtype.ext (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 x.2)))
    fun i => by
      obtain ⟨u, h1, h2⟩ := exists_separating i.1.2 i.2.2
      have e : ∀ j, ⟪vec ha j, (V a)ᗮ.orthogonalProjectionOnto u⟫_ℂ = func j u := fun j =>
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _
      exact ⟨_, by rwa [e], fun j hj => by
        rw [e]
        refine h2 _ j.1.2 _ j.2.2 fun hρ => not_le.1 fun hle => hj.not_ge ?_
        exact code_le (Subtype.ext hρ) hle⟩
  refine ⟨b, fun k hk i => ?_⟩
  refine diagonal_eq (v := vec ha) (l := fun i => jet k 0 ((i.1 : ℂ) - 1 / 2)) (hb i).1 (hb i).2
    code_injective fun i x hx => ?_
  rw [inner_compr, inner_vec]
  exact character_conv _ hk (func i) fun y => moment_shift ha (abs_re_lt_of_mem i.1.2) i.2 x
    (fun l hl => hx ⟨i.1, ⟨l, hl.trans i.2.2⟩⟩ (code_lt hl)) y

/-! ### The trace -/

/-- The real parts of the resolvent values `1 / (c - z)` at the zeros are summable, for every
`c > a`. They are nonnegative; the values themselves need not be absolutely summable. -/
lemma summable_index (ha : 0 < a) {c : ℝ} (hc : a < c) :
    Summable fun i : Index a => (1 / ((c : ℂ) - ((i.1 : ℂ) - 1 / 2))).re := by
  have h1 : Summable fun ρ : innerZeros a =>
      (zeroMult ρ : ℝ) / (1 + Complex.normSq (((ρ : ℂ) - 1 / 2) / I)) := by
    refine (WeilExplicit.summable_zeroMult_div_one_add_normSq.comp_injective
      (inclusion_injective (innerZeros_subset a))).congr
      fun ρ => ?_
    simp only [Function.comp_apply]
  have h2 : Summable fun i : Index a =>
      1 / (1 + Complex.normSq (((i.1 : ℂ) - 1 / 2) / I)) := by
    refine (summable_sigma_of_nonneg fun i =>
      one_div_nonneg.2 (add_nonneg zero_le_one (normSq_nonneg _))).2 ⟨fun ρ => .of_finite, ?_⟩
    refine h1.congr fun ρ => ?_
    simp [tsum_fintype, div_eq_mul_inv]
  have hd : 0 < c - a := sub_pos.2 hc
  have hlow : ∀ i : Index a, c - a ≤ c - ((i.1 : ℂ) - 1 / 2).re := fun i => by
    linarith [(abs_lt.1 (abs_re_lt_of_mem i.1.2)).2]
  refine (h2.mul_left ((c + a) * ((1 + a ^ 2) / (c - a) ^ 2 + 1))).of_nonneg_of_le (fun i => ?_)
    fun i => ?_
  · rw [one_div, inv_re, sub_re, ofReal_re]
    exact div_nonneg (by linarith [hlow i]) (normSq_nonneg _)
  have hz := abs_lt.1 (abs_re_lt_of_mem i.1.2)
  have h3 := hlow i
  generalize (i.1 : ℂ) - 1 / 2 = z at hz h3 ⊢
  have e : normSq (z / I) = z.re ^ 2 + z.im ^ 2 := by
    rw [normSq_div, normSq_I, div_one, normSq_apply]; ring
  have e' : normSq (c - z) = (c - z.re) ^ 2 + z.im ^ 2 := by simp [normSq_apply]; ring
  have hsq : (c - a) ^ 2 ≤ (c - z.re) ^ 2 := pow_le_pow_left₀ hd.le h3 2
  rw [one_div, inv_re, sub_re, ofReal_re, e, e', mul_one_div,
    div_le_div_iff₀ (by nlinarith [sq_nonneg z.im]) (by positivity), mul_assoc]
  refine mul_le_mul (by linarith [hz.1]) ?_ (by positivity) (by linarith)
  have h4 : 1 + a ^ 2 ≤ (1 + a ^ 2) / (c - a) ^ 2 * (c - z.re) ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    gcongr
  have h5 : 0 ≤ (1 + a ^ 2) / (c - a) ^ 2 := by positivity
  nlinarith [sq_nonneg z.im, sq_nonneg (c - z.re), mul_nonneg h5 (sq_nonneg z.im),
    hz.1, hz.2]

/-- **The trace formula on `W a / V a`**, for every `C²` kernel with compact support. -/
theorem hasTrace_conv (ha : 0 < a) (hk : ContDiff ℝ 2 k) (hs : HasCompactSupport k) :
    Summable (fun ρ : innerZeros a => (zeroMult ρ : ℂ) * jet k 0 ((ρ : ℂ) - 1 / 2)) ∧
      HasTrace (compr (V a) (conv (flow_shift ha) (good_of_compact hk.continuous hs)))
        (∑' ρ : innerZeros a, (zeroMult ρ : ℂ) * jet k 0 ((ρ : ℂ) - 1 / 2)) := by
  have hc : a < a + 1 := by linarith
  obtain ⟨b, hb⟩ := exists_basis_diagonal ha
  obtain ⟨hsum, htr⟩ := hasTrace_conv_of_diagonal (flow_shift ha)
    (fun y u hu => shift_mem ha y hu) b hb hc
    (fun i => ((abs_lt.1 (abs_re_lt_of_mem i.1.2)).2).trans hc) (summable_index ha hc) hk hs
  have hfib : ∀ ρ : innerZeros a, HasSum (fun _ : Fin (zeroMult ρ) => jet k 0 ((ρ : ℂ) - 1 / 2))
      ((zeroMult ρ : ℂ) * jet k 0 ((ρ : ℂ) - 1 / 2)) := fun ρ => by
    have h := hasSum_fintype fun _ : Fin (zeroMult ρ) => jet k 0 ((ρ : ℂ) - 1 / 2)
    simpa using h
  have hz := hsum.hasSum.sigma hfib
  exact ⟨hz.summable, hz.tsum_eq ▸ htr⟩

end Zeros

/-! ### Test functions -/

section TestFunctions

variable {a : ℝ} {φ : TestFunction}

lemma jet_pull (φ : TestFunction) (z : ℂ) : jet φ.pull 0 z = φ.hat z := by
  rw [← TestFunction.transform_pull, jet_zero, WeilExplicit.transform]
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

/-- At `a = 1/2` the trace is the functional of Weil's explicit formula. The value of the zero sum
is that of `TestFunction.hasSum_full`. -/
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

/-- The trace at width `a` is the explicit formula functional for every test function iff there are
no zeros in the critical strip at distance at least `a` from the critical line. This is
`innerExpansion_iff` with the zero sum replaced by the trace; neither side is asserted, and it adds
no information on zeros. -/
theorem trace_eq_efFunctional_iff (ha : 0 < a) :
    (∀ φ : TestFunction, HasTrace (induced ha φ) φ.efFunctional) ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2| := by
  rw [← innerExpansion_iff]
  refine forall_congr' fun φ => ?_
  obtain ⟨t, h1, h2⟩ := exists_hasTrace_induced ha φ
  exact ⟨fun h => h1.unique h ▸ h2, fun h => h2.unique h ▸ h1⟩

/-- Equality of the traces at the one pair of widths `a` and `1 / 2`, for every test function, is
equivalent to there being no zeros in the critical strip at distance at least `a` from the critical
line. Neither side is asserted. -/
theorem trace_eq_trace_half_iff (ha : 0 < a) :
    (∀ (φ : TestFunction) (t : ℂ), HasTrace (induced (a := 1 / 2) (by norm_num) φ) t →
      HasTrace (induced ha φ) t) ↔
      ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ a ≤ |ρ.re - 1 / 2| := by
  rw [← trace_eq_efFunctional_iff ha]
  exact ⟨fun h φ => h φ _ (hasTrace_induced_half φ),
    fun h φ t ht => ht.unique (hasTrace_induced_half φ) ▸ h φ⟩

/-! ### Negative control -/

/-- The traces determine the multiplicities of the zeros at distance less than `a` from the critical
line: an expansion over these zeros with any other weight at one of them, in particular one that
drops it, fails to converge to the trace for some test function. Values of `n` elsewhere are
free. -/
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
