import Masullo.QRH.MeanSquare.ReflectionSquarefreeBound
import Masullo.QRH.MeanSquare.ReflectionBands

/-! # Reflected columns as a vector of dyadic kernel blocks -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare.ReflectionSieve

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- Arithmetic data for one branch. The natural index `h` represents layer `m = h - 3`.
The extracted squarefree and cube factors have norms `N` and `L`, respectively. -/
structure KernelBranchData (B K X : ℝ) (t G : Idl) where
  rows : Finset Idl
  rowClass : QuadraticFamilyClass
  rows_subset : rows ⊆ sieveIdeals (span {6}) K
  rows_class : ∀ k ∈ rows, familyClass k = rowClass
  primes : Finset Idl
  primes_subset : primes ⊆ (normalizedFactors t).toFinset ∪ (normalizedFactors G).toFinset
  choice : Idl → TameBranch
  simple : ∀ p ∈ primes, p ∉ normalizedFactors t → (normalizedFactors G).count p = 1 → choice p ≠ .ordinary
  a : ℝ
  Q : ℝ
  N : ℝ
  L : ℝ
  K_pos : 0 < K
  X_pos : 0 < X
  Q_pos : 0 < Q
  N_pos : 0 < N
  L_pos : 0 < L
  amplitude_nonneg : 0 ≤ a
  amplitude : a^2 ≤ B^2 * ∏ p ∈ primes, (choice p).weightSq (absNorm p)
  length : Q^2*K^2/(N*L^3*X) ≤ B*K^2/X * ∏ p ∈ primes, (choice p).length (absNorm p)
  c : ℕ → Idl → Idl → ℂ
  d : ℕ → Idl → Idl → ℂ
  columns : ∀ h b, b ≠ 0 → ∀ n, Starred n → ‖c h b n‖ ≤ a
  row_phases : ∀ h b, b ≠ 0 → ∀ k ∈ rows, ‖d h b k‖ ≤ 1

private theorem cube_mem_Ico {b : Idl} {i : ℕ} (hb : b ∈ cubeBand i) :
    (absNorm b : ℝ) ∈ Set.Ico (2^i) (2*2^i) := (mem_filter.mp hb).2

private theorem row_norm_le {B K X : ℝ} {t G : Idl} (v : KernelBranchData B K X t G)
    {k : Idl} (hk : k ∈ v.rows) : (absNorm k : ℝ) ≤ K := by
  classical
  exact (mem_idealsLe v.K_pos.le).mp (mem_filter.mp (v.rows_subset hk)).1

private theorem row_norm_pos {B K X : ℝ} {t G : Idl} (v : KernelBranchData B K X t G)
    {k : Idl} (hk : k ∈ v.rows) : 0 < (absNorm k : ℝ) := by
  classical
  exact zero_lt_one.trans_le (absNorm_one_le (mem_filter.mp (v.rows_subset hk)).2.1.ne_zero)

def makeKernelBranch {B K X : ℝ} {t G : Idl} (v : KernelBranchData B K X t G) :
    SquarefreeKernelBranch B K X t G where
  rows := v.rows
  rowClass := v.rowClass
  rows_subset := v.rows_subset
  rows_class := v.rows_class
  S := squarefreeBand
  T := cubeBand
  squarefree_band _ := Subset.rfl
  cube_band _ _ hb := cube_mem_Ico hb
  c e := v.c e.1
  d e := v.d e.1
  u e b k := (3:ℝ)^((e.1:ℤ)-3) * 2^e.2.1 * (absNorm b:ℝ)^3 * v.N*v.L^3*X / (v.Q*absNorm k)^2
  primes := v.primes
  primes_subset := v.primes_subset
  choice := v.choice
  simple := v.simple
  a := v.a
  Y := v.Q^2*K^2/(v.N*v.L^3*X)
  amplitude_nonneg := v.amplitude_nonneg
  length_pos := by have := v.Q_pos; have := v.K_pos; have := v.N_pos; have := v.L_pos; have := v.X_pos; positivity
  amplitude := v.amplitude
  length := v.length
  columns e b hb n hn := v.columns e.1 b (mem_cubeBand.mp hb).1 n (mem_squarefreeBand.mp hn).1
  row_phases e b hb := v.row_phases e.1 b (mem_cubeBand.mp hb).1
  kernel_scale e b hb k hk := by
    have hQ := v.Q_pos
    have hK := v.K_pos
    have hX := v.X_pos
    have hN := v.N_pos
    have hL := v.L_pos
    have hkN := row_norm_pos v hk
    have hkK := row_norm_le v hk
    have hbN := (cube_mem_Ico hb).1
    dsimp only [kernelScale]
    rw [div_div_eq_mul_div, ← mul_pow]
    simp only [mul_assoc]
    gcongr

/-- One integral-free summand indexed by the shifted layer, cube ideal and squarefree ideal. -/
def rawKernelTerm (W : ℝ → ℂ) (X Q N L : ℝ) (c d : ℕ → Idl → Idl → ℂ)
    (k : Idl) (h : ℕ) (b n : Idl) : ℂ :=
  (((3 : ℝ)^(-((h:ℝ)-3)/3) : ℝ) : ℂ) * (absNorm b : ℂ)⁻¹ *
    (d h b k * (c h b n / Real.sqrt (absNorm n)) * primaryQuadraticSymbol n k) *
    reflectionKernel W 0 0 ((3:ℝ)^((h:ℤ)-3) * absNorm n * (absNorm b:ℝ)^3 * N*L^3*X / (Q*absNorm k)^2)

private theorem makeKernelBranch_block {B K X : ℝ} {t G : Idl} (v : KernelBranchData B K X t G)
    (W : ℝ → ℂ) (e : ℕ × ℕ × ℕ) (k : v.rows) :
    kernelBlockVector W v.rows (squarefreeBand e.2.1) (cubeBand e.2.2) ((e.1:ℤ)-3) (2^e.2.1)
      (v.c e.1) (v.d e.1) ((makeKernelBranch v).u e) k =
      ∑ b ∈ cubeBand e.2.2, ∑ n ∈ squarefreeBand e.2.1, rawKernelTerm W X v.Q v.N v.L v.c v.d k e.1 b n := by
  classical
  simp only [kernelBlockVector,PiLp.smul_apply,Complex.real_smul,kernelBlock,
    Int.cast_sub, Int.cast_natCast, Int.cast_ofNat, Finset.mul_sum, rawKernelTerm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro n _
  have he : (absNorm n : ℝ)/2^e.2.1 * (makeKernelBranch v).u e b k =
      (3:ℝ)^((e.1:ℤ)-3)*absNorm n*(absNorm b:ℝ)^3*v.N*v.L^3*X/(v.Q*absNorm (k:Idl))^2 := by
    dsimp only [makeKernelBranch]
    field_simp
  rw [he]
  ring


private theorem hasSum_bands (f : ℕ → Idl → Idl → ℂ)
    (h : Summable (fun x : ReflectedColumns => f x.1 x.2.1 x.2.2)) :
    HasSum (fun e : ℕ × ℕ × ℕ => ∑ b ∈ cubeBand e.2.2, ∑ n ∈ squarefreeBand e.2.1, f e.1 b n)
      (∑' x : ReflectedColumns, f x.1 x.2.1 x.2.2) := by
  classical
  have hs := (bandEquiv.hasSum_iff.mpr h.hasSum).sigma (fun _ => (hasSum_fintype _))
  apply hs.congr_fun
  intro e
  simp only [Fintype.sum_prod_type]
  change _ = ∑ b : cubeBand e.2.2, ∑ n : squarefreeBand e.2.1, f e.1 b n
  simp only [Finset.sum_coe_sort]
  exact ((cubeBand e.2.2).sum_coe_sort (fun b => ∑ n ∈ squarefreeBand e.2.1, f e.1 b n)).symm

theorem makeKernelBranch_rowValue_of_summable {B K X : ℝ} {t G : Idl} (v : KernelBranchData B K X t G)
    (W : ℝ → ℂ) (hs : ∀ k ∈ v.rows, Summable (fun x : ReflectedColumns =>
      rawKernelTerm W X v.Q v.N v.L v.c v.d k x.1 x.2.1 x.2.2)) {k : Idl} (hk : k ∈ v.rows) :
    (makeKernelBranch v).rowValue W k = ∑' x : ReflectedColumns,
      rawKernelTerm W X v.Q v.N v.L v.c v.d k x.1 x.2.1 x.2.2 := by
  classical
  let b := makeKernelBranch v
  let f (e : ℕ × ℕ × ℕ) := kernelBlockVector W v.rows (squarefreeBand e.2.1) (cubeBand e.2.2)
    ((e.1:ℤ)-3) (2^e.2.1) (v.c e.1) (v.d e.1) (b.u e)
  let S (k : v.rows) := ∑' x : ReflectedColumns, rawKernelTerm W X v.Q v.N v.L v.c v.d k x.1 x.2.1 x.2.2
  have h : HasSum (fun e => fun k : v.rows => f e k) S := Pi.hasSum.mpr (fun k =>
    (hasSum_bands _ (hs k k.property)).congr_fun fun e => makeKernelBranch_block v W e k)
  have h' := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : v.rows => ℂ)).symm.toContinuousLinearMap.hasSum h
  have he : ∑' e, f e = WithLp.toLp 2 S := h'.tsum_eq
  simp only [SquarefreeKernelBranch.rowValue, show k ∈ (makeKernelBranch v).rows from hk, dite_true]
  exact congrArg (fun z : EuclideanSpace ℂ v.rows => z ⟨k,hk⟩) he


/-- The kernel on the line two makes the raw reflected columns absolutely summable
at every row, before applying the sieve. -/
theorem summable_rawKernelTerm {B K X : ℝ} {t G : Idl} (v : KernelBranchData B K X t G)
    (hΓ : DLMFGammaVertical) {I : TestInterval} {W : ℝ → ℂ} (hW : UnitTest I 14 W)
    {k : Idl} (hk : k ∈ v.rows) : Summable (fun x : ReflectedColumns =>
      rawKernelTerm W X v.Q v.N v.L v.c v.d k x.1 x.2.1 x.2.2) := by
  classical
  have hX := v.X_pos
  have hQ := v.Q_pos
  have hN := v.N_pos
  have hL := v.L_pos
  have ha := v.amplitude_nonneg
  have hkN := row_norm_pos v hk
  let U := v.N*v.L^3*X/(27*(v.Q*absNorm k)^2)
  have hU : 0 < U := by dsimp [U]; positivity
  obtain ⟨C,hC,hker⟩ := norm_reflectionKernel hΓ (σ := 2) (by norm_num) 0 I
  have hW' : UnitTest I (0 + ⌈4 * max (2:ℝ) 0⌉₊ + 2) W := hW.of_le (by norm_num)
  let w (x : Idl) := ((absNorm x:ℝ)^2)⁻¹
  have hw : Summable w := ReflectionRows.summable_inverse_square
  have hgs := summable_geometric_of_lt_one (r := (1/9:ℝ)) (by norm_num) (by norm_num)
  have hb := hw.comp_injective (Subtype.val_injective (p := fun b : Idl => b ≠ 0))
  have hn := hw.comp_injective (Subtype.val_injective (p := Starred))
  have hw₀ (b : Idl) : 0 ≤ w b := by dsimp [w]; positivity
  have hbn := hb.mul_of_nonneg hn (fun b => hw₀ b.val) (fun n => hw₀ n.val)
  have hall := hgs.mul_of_nonneg hbn (fun _ => by positivity)
    (fun x => mul_nonneg (hw₀ x.1.val) (hw₀ x.2.val))
  apply (hall.mul_left (3*v.a*C*(U^2)⁻¹)).of_norm_bounded
  rintro ⟨h,⟨b,hb⟩,⟨n,hn⟩⟩
  have hb₁ := absNorm_one_le hb
  have hn₁ := absNorm_one_le hn.1.1
  have hb₀ := zero_lt_one.trans_le hb₁
  have hn₀ := zero_lt_one.trans_le hn₁
  let z := (3:ℝ)^((h:ℤ)-3)*absNorm n*(absNorm b:ℝ)^3*v.N*v.L^3*X/(v.Q*absNorm k)^2
  have hz : 0 < z := by dsimp [z]; positivity
  have hzz : U*(3:ℝ)^h*absNorm b*absNorm n ≤ z := by
    have hh : (absNorm b:ℝ) ≤ (absNorm b:ℝ)^3 := by simpa using pow_le_pow_right₀ hb₁ (by decide : 1 ≤ 3)
    dsimp only [z]
    rw [zpow_sub₀ (by norm_num), zpow_natCast]
    calc
      _ ≤ U*(3:ℝ)^h*(absNorm b:ℝ)^3*absNorm n := by gcongr
      _ = _ := by dsimp [U]; norm_num; ring
  have hkbound : ‖reflectionKernel W 0 0 z‖ ≤ C*(U^2)⁻¹ *
      ((1/9:ℝ)^h * (w b * w n)) := calc
    _ = ‖reflectionKernel W 0 2 z‖ := congrArg _ (reflectionKernel_shift hΓ (by norm_num) (by norm_num) 0 hW' hz)
    _ ≤ C * z^(-(2:ℝ)) := hker W hW' z hz
    _ ≤ C*(U*3^h*absNorm b*absNorm n)^(-(2:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hzz (by norm_num)
    _ = _ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two]
      dsimp [w]
      have hgeom : ((3:ℝ)^h)^2 = 9^h := by rw [←pow_mul, Nat.mul_comm,pow_mul]; norm_num
      simp only [mul_pow, mul_inv_rev, hgeom, one_div, inv_pow]
      ring
  have hpre : (3:ℝ)^(-((h:ℝ)-3)/3) ≤ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (show -((h:ℝ)-3)/3 ≤ (1:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) h])
  have hs : ‖primaryQuadraticSymbol n k‖ ≤ 1 := by
    change ‖sextic k (generator n)^3‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_sextic_le_one _ _)
  have hcol : ‖v.c h b n / (Real.sqrt (absNorm n):ℂ)‖ ≤ v.a := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_self (norm_nonneg _) (by simpa using Real.sqrt_le_sqrt hn₁)).trans (v.columns h b hb n hn)
  have hinv : ‖(absNorm b:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ hb₁
  change ‖_‖ ≤ 3*v.a*C*(U^2)⁻¹ * ((1/9:ℝ)^h*(w b*w n))
  dsimp only [rawKernelTerm]
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3:ℝ)) _)]
  calc
    _ ≤ 3*1*(1*v.a*1) * (C*(U^2)⁻¹*((1/9:ℝ)^h*(w b*w n))) := by
      gcongr
      exact v.row_phases h b hb k hk
    _ = _ := by ring

theorem makeKernelBranch_rowValue {B K X : ℝ} {t G : Idl} (v : KernelBranchData B K X t G)
    (hΓ : DLMFGammaVertical) {I : TestInterval} {W : ℝ → ℂ} (hW : UnitTest I 14 W)
    {k : Idl} (hk : k ∈ v.rows) :
    (makeKernelBranch v).rowValue W k = ∑' x : ReflectedColumns,
      rawKernelTerm W X v.Q v.N v.L v.c v.d k x.1 x.2.1 x.2.2 :=
  makeKernelBranch_rowValue_of_summable v W (fun _ hk' => summable_rawKernelTerm v hΓ hW hk') hk

end Masullo.QRH.MeanSquare.ReflectionSieve
