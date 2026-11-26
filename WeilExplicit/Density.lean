import WeilExplicit.DensityCount

/-!
# Zeros to the right of the critical line are sparse

For every `σ > 1/2` the reciprocal ordinates `1 / Im ρ` of the zeros `ρ` of zeta in the open
critical strip with `Re ρ ≥ σ` and `Im ρ > 0` are summable. Each zero is counted once,
irrespective of multiplicity.

The argument is a Carlson-type mean-square density estimate. It is due to OpenAI Codex (E36) and
was formalised by Claude. Mollifying zeta with `M_U(s) = ∑_{d ≤ U} μ(d) d^{-s}` gives
`∫ |ζ M_U - 1|² = O(T^{1-δ²/3})` on the lines `1/2 + δ ≤ Re s ≤ 2` at height `T`
(`mean_square_mollified`). Each zero with `Re ρ ≥ 1/2 + 2δ` forces `|ζ M_U - 1| = 1` at the
centre of a disc of radius `δ`, which costs `π δ²` of that mean square (`disk_lower`). The discs
overlap `O(log T)` times, so a dyadic shell `T ≤ Im ρ ≤ 2T` holds `O(log T · T^{1-δ²/3})` zeros
(`shell_card_le`), and summing over dyadic shells gives the result.
-/

namespace WeilExplicit

open Complex Set Real

/-- **Sparsity of zeros off the critical line.** For `σ > 1/2` the reciprocal ordinates of the
distinct zeros of zeta in the open critical strip with `Re ρ ≥ σ` and `Im ρ > 0` are summable. -/
theorem summable_inv_im_of_half_lt {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun ρ : {ρ ∈ stripZeros | σ ≤ ρ.re ∧ 0 < ρ.im} ↦ 1 / (ρ : ℂ).im := by
  classical
  set σ' := min σ (3 / 4)
  set δ := (σ' - 1 / 2) / 2
  have hσ'1 : 1 / 2 < σ' := lt_min hσ (by norm_num)
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hδ' : δ ≤ 1 / 8 := by simp only [δ]; linarith [min_le_right σ (3 / 4)]
  have hσσ : 1 / 2 + 2 * δ ≤ σ := by simp only [δ]; linarith [min_le_left σ (3 / 4)]
  obtain ⟨B, hB⟩ := shell_card_le hδ hδ'
  set B' := max B 0
  set q : ℝ := (2 : ℝ) ^ (-(δ ^ 2 / 3))
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  set b : ℕ → ℝ := fun k ↦ B' * Real.log 2 * ((k : ℝ) ^ 1 * q ^ k + 3 * q ^ k)
  have hbs : Summable b :=
    ((summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hq0])).add
      ((summable_geometric_of_lt_one hq0 hq1).mul_left 3)).mul_left (B' * Real.log 2)
  have hB'0 : 0 ≤ B' := le_max_right _ _
  let Z := {ρ ∈ stripZeros | σ ≤ ρ.re ∧ 0 < ρ.im}
  choose κ hκlo hκhi using fun ρ : Z ↦ exists_nat_pow_near (le_max_left (1 : ℝ) (ρ : ℂ).im)
    (by norm_num : (1 : ℝ) < 2)
  let s (k : ℕ) : Set Z := {ρ | κ ρ = k}
  have hs (k : ℕ) : (s k).Finite := by
    have K := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm
      (isCompact_Icc (a := (0 : ℝ)) (b := 2 ^ (k + 1)))
    refine (K.inter_riemannZetaZeros_finite.preimage Subtype.val_injective.injOn).subset ?_
    intro ρ hρ
    have hhi := (le_max_right 1 (ρ : ℂ).im).trans (hκhi ρ).le
    exact ⟨⟨⟨ρ.property.1.2.1.le, ρ.property.1.2.2.le⟩, ρ.property.2.2.le,
      (show κ ρ = k from hρ) ▸ hhi⟩, ρ.property.1.1⟩
  let (k : ℕ) : Fintype (s k) := (hs k).fintype
  apply (summable_partition (s := s) (fun ρ ↦ (one_div_pos.mpr ρ.property.2.2).le)
    (fun ρ ↦ ⟨κ ρ, rfl, fun _ h ↦ h.symm⟩)).mpr
  refine ⟨fun _ ↦ (hasSum_fintype _).summable, hbs.of_norm_bounded_eventually_nat ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  let e : s k ↪ ℂ := (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)
  let F := Finset.univ.map e
  have hT : (2 : ℝ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hF : ∀ ρ ∈ F, ρ ∈ stripZeros ∧ 1 / 2 + 2 * δ ≤ ρ.re ∧ (2 : ℝ) ^ k ≤ ρ.im ∧
      ρ.im ≤ 2 * 2 ^ k := by
    intro ρ hρ
    obtain ⟨⟨z, hz⟩, _, rfl⟩ := Finset.mem_map.mp hρ
    change κ z = k at hz
    have hlo := hκlo z
    rw [hz, le_max_iff] at hlo
    refine ⟨z.property.1, hσσ.trans z.property.2.1, hlo.resolve_left (by linarith), ?_⟩
    simpa [e, hz, pow_succ, mul_comm] using (le_max_right 1 (z : ℂ).im).trans (hκhi z).le
  rw [tsum_fintype, Real.norm_of_nonneg (Finset.sum_nonneg
    fun z _ ↦ (one_div_pos.mpr z.val.property.2.2).le)]
  change ∑ z : s k, 1 / (e z).im ≤ b k
  rw [← Finset.sum_map Finset.univ e (fun z : ℂ ↦ 1 / z.im)]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hcard := hB (2 ^ k) hT F hF
  have hlog : Real.log (2 * 2 ^ k + 4) ≤ (k + 3) * Real.log 2 := by
    rw [show ((k : ℝ) + 3) * Real.log 2 = Real.log (2 ^ (k + 3)) by
      rw [Real.log_pow]; push_cast; ring]
    refine Real.log_le_log (by positivity) ?_
    rw [pow_add]
    nlinarith
  have hpow : ((2 : ℝ) ^ k) ^ (1 - δ ^ 2 / 3) / 2 ^ k = q ^ k := by
    rw [← Real.rpow_sub_one h2k.ne', show 1 - δ ^ 2 / 3 - 1 = -(δ ^ 2 / 3) by ring,
      ← Real.rpow_pow_comm (by norm_num)]
  calc ∑ ρ ∈ F, 1 / ρ.im ≤ ∑ ρ ∈ F, 1 / (2 : ℝ) ^ k :=
        Finset.sum_le_sum fun ρ hρ ↦ one_div_le_one_div_of_le h2k (hF ρ hρ).2.2.1
    _ = F.card / 2 ^ k := by simp [div_eq_mul_inv]
    _ ≤ B' * (Real.log (2 * 2 ^ k + 4) * ((2 : ℝ) ^ k) ^ (1 - δ ^ 2 / 3)) / 2 ^ k := by
        gcongr
        refine hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * 2 ^ k + 4)
        positivity
    _ = B' * Real.log (2 * 2 ^ k + 4) * q ^ k := by rw [← hpow]; ring
    _ ≤ B' * ((k + 3) * Real.log 2) * q ^ k := by gcongr
    _ = b k := by simp only [b]; ring

end WeilExplicit
