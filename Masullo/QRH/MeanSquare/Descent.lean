import Masullo.QRH.MeanSquare.Forms

/-! # Finite induction on the row length

The induction from the cube tail and transfer follows §5.5, pp. 21–22 of
OpenAI, *The Quasi-Riemann Hypothesis* (5 October 2026).
-/

namespace Masullo.QRH.MeanSquare

/-- Terminal estimate on the unit rows, with the zeroth test norm. -/
def UnitRowEstimate : Prop :=
  ∀ I : TestInterval, ∃ C ≥ (0 : ℝ), ∀ (X F : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
    1 ≤ X → 1 ≤ F → UnitTest I 0 W → dualMeanSquare ξ W 1 X F ≤ C * (X * F)

/-- The surviving cube and the parent gap force the next row below `K (K/Σ)²`. -/
theorem transfer_row_lt {K X F u k : ℝ} (hK : 0 < K) (hX : 0 < X) (hF : 0 < F)
    (hu : 0 < u) (htail : min X (X ^ 2 / K ^ 2) < u) (hL : 1 < X / u)
    (hk : k ≤ K * (X / u) / (X * F * F)) :
    k < K * (K / (X * F)) ^ 2 := by
  have huX : u < X := by simpa using (lt_div_iff₀ hu).mp hL
  have hsmall : X ^ 2 / K ^ 2 < u := (min_lt_iff.mp htail).resolve_left (not_lt_of_ge huX.le)
  have h := (div_lt_iff₀ (sq_pos_of_pos hK)).mp hsmall
  apply hk.trans_lt
  field_simp
  nlinarith [mul_lt_mul_of_pos_left h (mul_pos hK (sq_pos_of_pos hX))]

private def AtDepth (C₀ κ : ℝ) (d : ℕ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ j : ℕ, ∀ I : TestInterval, ∃ C ≥ (0 : ℝ),
    ∀ (D K X F : ℝ) (ξ : RayCharacter) (W : ℝ → ℂ),
    2 ≤ D → 1 ≤ K → 1 ≤ X → 1 ≤ F → X * F ≤ D ^ C₀ →
    K ≤ X * F * D ^ (-κ) → K ≤ D ^ ((d : ℝ) * κ) → UnitTest I j W →
    dualMeanSquare ξ W K X F ≤ C * D ^ ε * (X * F)

private theorem atDepth_of_tail_transfer (hbase : UnitRowEstimate) (htail : CubeTailEstimate)
    (htrans : TransferEstimate) {C₀ κ : ℝ} (hc : 1 ≤ C₀) (hκ : 0 < κ) (d : ℕ) :
    AtDepth C₀ κ d := by
  induction d with
  | zero =>
    intro ε hε
    refine ⟨0, fun I => ?_⟩
    obtain ⟨C, hC, h⟩ := hbase I
    refine ⟨C, hC, fun D K X F ξ W hD hK hX hF _ _ hd hw => ?_⟩
    have heq : K = 1 := le_antisymm (by simpa using hd) hK
    subst K
    apply (h X F ξ W hX hF hw).trans
    gcongr
    exact le_mul_of_one_le_right hC (Real.one_le_rpow (by linarith) hε.le)
  | succ d ih =>
    intro ε hε
    let e := ε / 3
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨m, hm⟩ := ih e he
    obtain ⟨j, hj⟩ := htail C₀ hc e he
    refine ⟨max j (4*m+12), fun I => ?_⟩
    obtain ⟨Ci, hi, hind⟩ := hm I.enlarge
    obtain ⟨Ct, ht, htransfer⟩ := htrans C₀ hc e he m I
    obtain ⟨Ca, ha, hcube⟩ := hj I
    refine ⟨Ca * (1 + Ct * (1 + Ci)), by positivity, ?_⟩
    intro D K X F ξ W hD hK hX hF hsize hgap hd hw
    have hD₁ : 1 ≤ D := by linarith
    have hD₀ : 0 < D := by linarith
    have hMass : 0 < X * F := by positivity
    have hη : D ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hD₁ (by linarith)
    have hKS : K ≤ X * F := hgap.trans (mul_le_of_le_one_right hMass.le hη)
    let t := D ^ e
    have ht₁ : 1 ≤ t := Real.one_le_rpow hD₁ he.le
    have ht₀ : 0 ≤ t := by linarith
    let B := Ct * t * (X * F) * (1 + Ci * t)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hbound := hcube D K X F B ξ W hD hK hX hF hKS hsize
      (hw.of_le (le_max_left ..)) hB
    apply (hbound ?_).trans
    · have hp : D ^ ε = t ^ 3 := by
        dsimp [t, e]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hD₀.le]
        congr 1
        norm_num
      rw [hp]
      change Ca * t * (X * F + Ct * t * (X * F) * (1 + Ci * t)) ≤ _
      have h₁ : 1 + Ci * t ≤ (1 + Ci) * t := by nlinarith
      have h₂ : 1 ≤ t ^ 2 := one_le_pow₀ ht₁
      calc
        _ ≤ Ca * t * ((X * F) * t ^ 2 + Ct * t * (X * F) * ((1 + Ci) * t)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add (le_mul_of_one_le_right hMass.le h₂)
            (mul_le_mul_of_nonneg_left h₁ (by positivity))
        _ = _ := by ring
    · intro b hb
      dsimp only
      let u := (Ideal.absNorm b : ℝ) ^ 3
      change min X (X ^ 2 / K ^ 2) < u → 1 < X / u → _
      intro hcut hL
      have hu₁ : 1 ≤ u := by
        have hn := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hb.1)
        exact one_le_pow₀ (by exact_mod_cast hn)
      have hu : 0 < u := by linarith
      have hLX : X / u ≤ X := div_le_self (by linarith) hu₁
      apply htransfer D K (X / u) F (X * F) (Ci * t) ξ W hD hK hL.le hF hKS
        (mul_le_mul_of_nonneg_right hLX (by linarith)) hsize (by positivity) ?_
        (hw.of_le (le_max_right ..))
      intro k x f χ U hk hx hf hcontract hratio hprod hU
      have hxf : 0 < x * f := by positivity
      have hratio' : k / (x * f) ≤ D ^ (-κ) :=
        hratio.trans ((div_le_iff₀ hMass).mpr (by linarith [hgap]))
      have hchild := transfer_row_lt (by linarith) (by linarith) (by linarith) hu hcut hL hcontract
      have hlength : k ≤ D ^ ((d : ℝ) * κ) := calc
        k ≤ K * (K / (X * F)) ^ 2 := hchild.le
        _ ≤ D ^ (((d + 1 : ℕ) : ℝ) * κ) * (D ^ (-κ)) ^ 2 := by
          gcongr
          exact (div_le_iff₀ hMass).mpr (by linarith [hgap])
        _ = D ^ (((d : ℝ) - 1) * κ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hD₀.le, ← Real.rpow_add hD₀]
          congr 1
          push_cast
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hD₁ (by nlinarith)
      apply hind D k x f χ U hD hk hx hf _ _ hlength hU
      · exact hprod.trans (hLX.trans ((le_mul_of_one_le_right (by linarith) hF).trans hsize))
      · simpa [mul_comm] using (div_le_iff₀ hxf).mp hratio'

/-- Finite descent discharges (4) from (6), the transfer and the terminal count. -/
theorem gapEstimate_of_tail_transfer (hbase : UnitRowEstimate) (htail : CubeTailEstimate)
    (htrans : TransferEstimate) : GapEstimate := by
  intro C₀ hc κ hκ ε he
  obtain ⟨d, hd⟩ := exists_nat_ge (C₀ / κ)
  obtain ⟨j, hj⟩ := atDepth_of_tail_transfer hbase htail htrans hc hκ d ε he
  refine ⟨j, fun I => ?_⟩
  obtain ⟨C, hC, h⟩ := hj I
  refine ⟨C, hC, fun D K X F ξ W hD hK hX hF hsize hgap => h D K X F ξ W hD hK hX hF
    hsize hgap ?_⟩
  have hη : D ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  calc K ≤ X * F := hgap.trans (mul_le_of_le_one_right (by positivity) hη)
    _ ≤ D ^ C₀ := hsize
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) ((div_le_iff₀ hκ).mp hd)

end Masullo.QRH.MeanSquare
