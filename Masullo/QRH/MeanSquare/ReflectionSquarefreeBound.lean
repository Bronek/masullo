import Masullo.QRH.MeanSquare.ReflectionSummation
import Masullo.QRH.MeanSquare.ReflectionRows
import Masullo.QRH.MeanSquare.CubeInversion

/-! # Summing the reflected branches over squarefree rows -/

noncomputable section

open NumberField Ideal Finset UniqueFactorizationMonoid

namespace Masullo.QRH.MeanSquare.ReflectionSieve

open ReflectionRows

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- One branch of (15), after extracting the primes in its local conditions.
The same dyadic column data apply to every row in the indicated fixed class. -/
structure SquarefreeKernelBranch (B K X : ℝ) (t G : Idl) where
  rows : Finset Idl
  rowClass : QuadraticFamilyClass
  rows_subset : rows ⊆ sieveIdeals (span {6}) K
  rows_class : ∀ k ∈ rows, familyClass k = rowClass
  S : ℕ → Finset Idl
  T : ℕ → Finset Idl
  squarefree_band : ∀ i, S i ⊆ dyadicSieveIdeals (span {6}) (2^i)
  cube_band : ∀ j, ∀ b ∈ T j, (absNorm b : ℝ) ∈ Set.Ico (2^j) (2*2^j)
  c : ℕ × ℕ × ℕ → Idl → Idl → ℂ
  d : ℕ × ℕ × ℕ → Idl → Idl → ℂ
  u : ℕ × ℕ × ℕ → Idl → Idl → ℝ
  primes : Finset Idl
  primes_subset : primes ⊆ (normalizedFactors t).toFinset ∪ (normalizedFactors G).toFinset
  choice : Idl → TameBranch
  simple : ∀ p ∈ primes, p ∉ normalizedFactors t → (normalizedFactors G).count p = 1 → choice p ≠
    .ordinary
  a : ℝ
  Y : ℝ
  amplitude_nonneg : 0 ≤ a
  length_pos : 0 < Y
  amplitude : a ^ 2 ≤ B ^ 2 * ∏ p ∈ primes, (choice p).weightSq (absNorm p)
  length : Y ≤ B * K^2 / X * ∏ p ∈ primes, (choice p).length (absNorm p)
  columns : ∀ i, ∀ b ∈ T i.2.2, ∀ n ∈ S i.2.1, ‖c i b n‖ ≤ a
  row_phases : ∀ i, ∀ b ∈ T i.2.2, ∀ k ∈ rows, ‖d i b k‖ ≤ 1
  kernel_scale : ∀ i, ∀ b ∈ T i.2.2, ∀ k ∈ rows,
    kernelScale ((i.1:ℤ)-3) (2^i.2.1) (2^i.2.2) Y ≤ u i b k

def SquarefreeKernelBranch.vector {B K X : ℝ} {t G : Idl} (b : SquarefreeKernelBranch B K X t G)
    (W : ℝ → ℂ) : EuclideanSpace ℂ b.rows :=
  ∑' i : ℕ × ℕ × ℕ, kernelBlockVector W b.rows (b.S i.2.1) (b.T i.2.2)
    ((i.1:ℤ)-3) (2^i.2.1) (b.c i) (b.d i) (b.u i)

open scoped Classical in
def SquarefreeKernelBranch.rowValue {B K X : ℝ} {t G : Idl} (b : SquarefreeKernelBranch B K X t G)
    (W : ℝ → ℂ) (k : Idl) : ℂ := if h : k ∈ b.rows then b.vector W ⟨k,h⟩ else 0

/-- The remaining arithmetic identity. For fixed primes of `6g` in the row, a finite
sum of branches recovers the original completed row at each coprime squarefree quotient. -/
def SquarefreeBranchRepresentation : Prop := ∀ I : TestInterval, ∃ B : ℝ, 1 ≤ B ∧
  ∀ (H X : ℝ) (u : 𝓔ˣ) (g : 𝓔) (ξ : RayCharacter) (W : ℝ → ℂ), 1 ≤ H → 1 ≤ X → g ≠ 0 →
  UnitTest I 14 W → let G := span {g}
    let P := (normalizedFactors (span {(6 : 𝓔)} * G)).toFinset
    ∀ A ⊆ P, let t := ∏ p ∈ A, p
      let K := H / absNorm t
      1 ≤ K → ∃ (n : ℕ) (b : Fin n → SquarefreeKernelBranch B K X t G),
        (n : ℝ) ≤ B * 6 ^ P.card ∧ ∀ k ∈ sieveIdeals (span {(6 : 𝓔)} * G) K,
          completedAtElement ξ W X ((u : 𝓔) * generator (t*k)) g = ∑ i, (b i).rowValue W k

private theorem branch_length_prod {t G : Idl} (ht : t ≠ 0) (hg : G ≠ 0)
    (P : Finset Idl) (hs : P ⊆ (normalizedFactors t).toFinset ∪ (normalizedFactors G).toFinset)
    (e : Idl → TameBranch) :
    (∏ p ∈ P, (e p).length (absNorm p)) ≤ ((absNorm t : ℝ) * absNorm G)^2 := by
  classical
  have hprod := mul_ne_zero ht hg
  have hp {p} (h : p ∈ P) : p ∈ normalizedFactors (t*G) := by
    rw [normalizedFactors_mul ht hg, Multiset.mem_add]
    exact (Finset.mem_union.mp (hs h)).imp Multiset.mem_toFinset.mp Multiset.mem_toFinset.mp
  have hn {p} (h : p ∈ P) := (prime_of_normalized_factor _ (hp h)).ne_zero
  have hS := partial_norm_product hprod P (fun _ => 1)
    (fun _ h => Multiset.count_pos.mpr (hp h)) (fun _ h => hn h)
  simp only [pow_one, map_mul, Nat.cast_mul] at hS
  calc
    _ ≤ ∏ p ∈ P, (absNorm p : ℝ)^2 := by
      apply prod_le_prod₀
      · intro p hp
        cases e p <;> dsimp [TameBranch.length] <;> positivity
      · intro p hp
        have hq := absNorm_one_le (hn hp)
        have hpow : (absNorm p : ℝ) ≤ (absNorm p : ℝ)^2 :=
          by simpa using pow_le_pow_right₀ hq (by decide : 1 ≤ 2)
        cases e p <;> dsimp [TameBranch.length]
        all_goals first | exact hq.trans hpow | exact hpow | exact le_rfl |
          exact (inv_le_one_of_one_le₀ hq).trans (hq.trans hpow)
    _ ≤ _ := by rw [Finset.prod_pow]; gcongr

private theorem SquarefreeKernelBranch.budgets {B K X : ℝ} {t G : Idl} (b : SquarefreeKernelBranch B
    K X t G)
    (hB : 1 ≤ B) (hX : 0 < X) (ht : t ≠ 0) (hg : G ≠ 0) :
    b.a^2 ≤ B^2 ∧ b.a^2*b.Y ≤ B^3*(K*(absNorm t : ℝ))^2*absNorm G/X ∧
      b.Y ≤ B*(K*(absNorm t : ℝ))^2*(absNorm G : ℝ)^2/X := by
  let Y₀ := B * K^2 / X
  have hY₀ : 0 ≤ Y₀ := by dsimp [Y₀]; positivity
  obtain ⟨hw,hY⟩ := ideal_branch_budget ht hg b.primes b.primes_subset b.choice b.simple hY₀
  refine ⟨b.amplitude.trans ((mul_le_mul_of_nonneg_left hw (sq_nonneg B)).trans_eq (mul_one _)),
    ?_, ?_⟩
  · calc
      _ ≤ (B^2 * ∏ p ∈ b.primes, (b.choice p).weightSq (absNorm p)) *
          (Y₀ * ∏ p ∈ b.primes, (b.choice p).length (absNorm p)) :=
        mul_le_mul b.amplitude b.length b.length_pos.le ((sq_nonneg b.a).trans b.amplitude)
      _ ≤ B^2 * (Y₀ * (absNorm t : ℝ)^2 * absNorm G) :=
        by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hY (sq_nonneg B)
      _ = _ := by dsimp [Y₀]; ring
  · calc
      _ ≤ _ := b.length
      _ ≤ Y₀ * ((absNorm t : ℝ) * absNorm G)^2 :=
        mul_le_mul_of_nonneg_left (branch_length_prod ht hg b.primes b.primes_subset b.choice) hY₀
      _ = _ := by dsimp [Y₀]; ring


private theorem SquarefreeKernelBranch.sum_rows {B K X : ℝ} {t G : Idl} (b : SquarefreeKernelBranch
    B K X t G)
    (W : ℝ → ℂ) (R : Finset Idl) : ∑ k ∈ R, ‖b.rowValue W k‖^2 ≤ ‖b.vector W‖^2 := by
  classical
  calc
    _ = ∑ k ∈ R ∩ b.rows, ‖b.rowValue W k‖^2 := by
      symm
      apply Finset.sum_subset (inter_subset_left)
      intro k hk hk'
      simp [SquarefreeKernelBranch.rowValue, show k ∉ b.rows from fun h => hk' (mem_inter.mpr
        ⟨hk,h⟩)]
    _ ≤ ∑ k ∈ b.rows, ‖b.rowValue W k‖^2 :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => sq_nonneg _)
    _ = _ := by
      rw [EuclideanSpace.norm_sq_eq, ← sum_coe_sort]
      apply sum_congr rfl
      intro k _
      simp [SquarefreeKernelBranch.rowValue, k.property]

private theorem sum_branches {B K X Z : ℝ} {t G : Idl} {n : ℕ} (b : Fin n → SquarefreeKernelBranch B
    K X t G)
    (W : ℝ → ℂ) (R : Finset Idl) (h : ∀ i, ‖(b i).vector W‖^2 ≤ Z) :
    ∑ k ∈ R, ‖∑ i, (b i).rowValue W k‖^2 ≤ (n:ℝ)^2 * Z := by
  classical
  calc
    _ ≤ ∑ k ∈ R, (n:ℝ) * ∑ i, ‖(b i).rowValue W k‖^2 := by
      refine sum_le_sum fun k _ => ?_
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
        (by simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i => ‖(b i).rowValue W k‖))
    _ = (n:ℝ)*∑ i, ∑ k ∈ R, ‖(b i).rowValue W k‖^2 := by rw [← mul_sum, sum_comm]
    _ ≤ (n:ℝ) * ∑ _i : Fin n, Z := by
      gcongr with i
      exact ((b i).sum_rows W R).trans (h i)
    _ = _ := by simp [pow_two, mul_assoc]

private theorem squarefree_cover {H : ℝ} (hH : 1 ≤ H) {M : Idl} (hM : M ≠ 0) {s : Idl}
    (hs : s ∈ squarefreeRows H) :
    ∃ A ⊆ (normalizedFactors M).toFinset, ∃ k ∈ sieveIdeals M (H/absNorm (∏ p ∈ A,p)), (∏ p ∈
      A,p)*k = s := by
  classical
  obtain ⟨hsH, hsf⟩ := mem_filter.mp hs
  have hsn := hsf.ne_zero
  let S := (normalizedFactors s).toFinset
  let P := (normalizedFactors M).toFinset
  let A := S ∩ P
  let t := ∏ p ∈ A, p
  let k := ∏ p ∈ S \ P, p
  have he : t*k = s := by
    rw [show t*k = ∏ p ∈ S, p from Finset.prod_inter_mul_prod_sdiff S P id]
    dsimp only [S]
    rw [prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val,
      ((squarefree_iff_nodup_normalizedFactors hsn).mp hsf).dedup]
    exact associated_iff_eq.mp (prod_normalizedFactors hsn)
  have ht : t ≠ 0 := left_ne_zero_of_mul (he ▸ hsn)
  have hNk : (absNorm k : ℝ) ≤ H / absNorm t := by
    apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one (absNorm_one_le ht))).mpr
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, he]
    exact (mem_idealsLe (by positivity)).mp hsH
  have hkS := hsf.squarefree_of_dvd (show k ∣ s from he ▸ dvd_mul_left _ _)
  have hc : IsCoprime k M := by
    apply IsCoprime.prod_left
    intro p hp
    have hprime := prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (mem_sdiff.mp hp).1)
    have hmax := ((Ideal.prime_iff_isPrime hprime.ne_zero).mp hprime).isMaximal hprime.ne_zero
    have hnot : ¬p ∣ M := fun hd => (mem_sdiff.mp hp).2
      (Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hM).mpr
        ⟨hprime, hd⟩))
    apply isCoprime_iff_sup_eq.mpr
    by_contra hsup
    have heq := hmax.eq_of_le hsup (le_sup_left : p ≤ p ⊔ M)
    exact hnot (Ideal.dvd_iff_le.mpr (le_sup_right.trans_eq heq.symm))
  exact ⟨A, inter_subset_right,k,mem_filter.mpr ⟨(mem_idealsLe (by positivity)).mpr hNk,hkS,hc⟩,he⟩

private theorem squarefree_cover_sum {H : ℝ} (hH : 1 ≤ H) {M : Idl} (hM : M ≠ 0)
    (f : Idl → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ k ∈ squarefreeRows H, f k ≤ ∑ A ∈ (normalizedFactors M).toFinset.powerset,
      ∑ k ∈ sieveIdeals M (H / absNorm (∏ p ∈ A, p)), f ((∏ p ∈ A, p)*k) := by
  classical
  let P := (normalizedFactors M).toFinset
  let t (A : Finset Idl) := ∏ p ∈ A,p
  let T := P.powerset.sigma (fun A => sieveIdeals M (H/absNorm (t A)))
  let r (v : (_ : Finset Idl) × Idl) := t v.1 * v.2
  have hc : squarefreeRows H ⊆ T.image r := by
    intro s hs
    obtain ⟨A,hA,k,hk,h⟩ := squarefree_cover hH hM hs
    exact mem_image.mpr ⟨⟨A,k⟩,mem_sigma.mpr ⟨mem_powerset.mpr hA,hk⟩,h⟩
  calc
    _ ≤ ∑ s ∈ T.image r, f s := sum_le_sum_of_subset_of_nonneg hc (fun s _ _ => hf s)
    _ ≤ ∑ v ∈ T, f (r v) := sum_image_le_of_nonneg (fun s _ => hf s)
    _ = _ := by simp only [T, sum_sigma, r, t, P]


private theorem SquarefreeKernelBranch.squared_bound {B C D H K X ρ C₀ : ℝ} {t G : Idl}
    (b : SquarefreeKernelBranch B K X t G) (W : ℝ → ℂ)
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hD : 1 ≤ D) (hK : 1 ≤ K) (hX : 1 ≤ X)
    (ht : t ≠ 0) (hg : G ≠ 0) (hHK : K * (absNorm t : ℝ) = H)
    (hH : H ≤ D^C₀) (hG : (absNorm G : ℝ) ≤ D^C₀) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hv : ‖b.vector W‖ ≤ C*b.a*K^ρ*b.Y^(2*ρ)*(Real.sqrt K+Real.sqrt b.Y)) :
    ‖b.vector W‖^2 ≤ 2*(C*B^2)^2*B^3 * D^(18*C₀*ρ) * (H+H^2*absNorm G/X) := by
  have hD₀ := zero_lt_one.trans_le hD
  have hB₀ := zero_lt_one.trans_le hB
  have hK₀ := zero_lt_one.trans_le hK
  have hX₀ := zero_lt_one.trans_le hX
  have hKH : K ≤ H := hHK ▸ le_mul_of_one_le_right hK₀.le (absNorm_one_le ht)
  have hH₀ := hK₀.trans_le hKH
  have ha := b.amplitude_nonneg
  have hY := b.length_pos
  obtain ⟨ha₂,haY,hY₂⟩ := b.budgets hB hX₀ ht hg
  rw [hHK] at haY hY₂
  have hY' : b.Y ≤ B * D^(4*C₀) := calc
    _ ≤ B * H^2 * (absNorm G : ℝ)^2 := hY₂.trans (div_le_self (by positivity) hX)
    _ ≤ B * (D^C₀)^2 * (D^C₀)^2 := by gcongr
    _ = _ := by
      rw [mul_assoc B, ← pow_add, ← Real.rpow_mul_natCast hD₀.le]
      norm_num; ring_nf; simp
  have hKpow : K^ρ ≤ D^(C₀*ρ) :=
    by rw [Real.rpow_mul hD₀.le]; exact Real.rpow_le_rpow hK₀.le (hKH.trans hH) hρ.le
  have hYpow : b.Y^(2*ρ) ≤ B^2 * D^((4*C₀)*(2*ρ)) := calc
    _ ≤ (B*D^(4*C₀))^(2*ρ) := Real.rpow_le_rpow hY.le hY' (by positivity)
    _ = B^(2*ρ)*D^((4*C₀)*(2*ρ)) :=
      by rw [Real.mul_rpow hB₀.le (Real.rpow_nonneg hD₀.le _),Real.rpow_mul hD₀.le (4*C₀) (2*ρ)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Real.rpow_le_rpow_of_exponent_le hB (show 2*ρ ≤ (2:ℝ) by linarith)
  have hp : K^ρ * b.Y^(2*ρ) ≤ B^2 * D^(9*C₀*ρ) := calc
    _ ≤ D^(C₀*ρ)*(B^2*D^((4*C₀)*(2*ρ))) :=
      mul_le_mul hKpow hYpow (by positivity) (by positivity)
    _ = _ := by rw [mul_left_comm, ← Real.rpow_add hD₀]; ring_nf
  have hmain : b.a^2*(Real.sqrt K+Real.sqrt b.Y)^2 ≤ 2*B^3*(H+H^2*absNorm G/X) := calc
    _ ≤ b.a^2*(2*(K+b.Y)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [sq_nonneg (Real.sqrt K - Real.sqrt b.Y), Real.sq_sqrt hK₀.le, Real.sq_sqrt hY.le]
    _ = 2*(b.a^2*K+b.a^2*b.Y) := by ring
    _ ≤ 2*(B^3*H+B^3*H^2*absNorm G/X) := by
      gcongr
      exact ha₂.trans (pow_le_pow_right₀ hB (by decide : 2 ≤ 3))
    _ = _ := by ring
  have hnorm : ‖b.vector W‖ ≤ (C*(B^2*D^(9*C₀*ρ))) * (b.a*(Real.sqrt K + Real.sqrt b.Y)) := calc
    _ ≤ _ := hv
    _ = C*(K^ρ*b.Y^(2*ρ)) * (b.a*(Real.sqrt K+Real.sqrt b.Y)) := by ring
    _ ≤ _ := by gcongr
  calc
    _ ≤ ((C*(B^2*D^(9*C₀*ρ))) * (b.a*(Real.sqrt K+Real.sqrt b.Y)))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (C*B^2)^2*(D^(9*C₀*ρ))^2*(b.a^2*(Real.sqrt K+Real.sqrt b.Y)^2) := by ring
    _ ≤ (C*B^2)^2*(D^(9*C₀*ρ))^2*(2*B^3*(H+H^2*absNorm G/X)) := by gcongr
    _ = _ := by rw [← Real.rpow_mul_natCast hD₀.le]; norm_num; ring_nf


/-- The finite branch expansion, the quadratic sieve, and the vertical gamma estimate imply
the squarefree completed-row bound with the fourteenth test seminorm. -/
theorem squarefreeCompletedEstimate_of_branches (quad : DeloupTuraevTheorem1)
    (sieve : QuadraticSieve primaryQuadraticSymbol) (hΓ : DLMFGammaVertical)
    (rep : SquarefreeBranchRepresentation) : SquarefreeCompletedEstimate := by
  classical
  intro C₀ hC₀ ε hε
  let ρ := min 1 (ε/(36*C₀))
  let η := ε/(2*C₀)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ₁ : ρ ≤ 1 := min_le_left _ _
  have hη : 0 < η := by dsimp [η]; positivity
  have hpow : C₀*η + 18*C₀*ρ ≤ ε := by
    have he : ρ*(36*C₀) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have he' : η*(2*C₀) = ε := div_mul_cancel₀ _ (by positivity)
    linarith
  refine ⟨14,fun I => ?_⟩
  obtain ⟨B,hB,hr⟩ := rep I
  obtain ⟨C,hC,hs⟩ := summed_kernel_branch quad sieve hΓ I hρ hρ₁
  obtain ⟨L,hL,hl⟩ := branch_count_bound (q := 72) (by norm_num) hη
  let M₆ : Idl := span {6}
  let Z₀ := 2*(C*B^2)^2*B^3
  have hZ₀ : 0 ≤ Z₀ := by dsimp [Z₀]; positivity
  have hM₆ : M₆ ≠ 0 := by apply mt span_singleton_eq_bot.mp; norm_num
  refine ⟨B^2*L*(absNorm M₆ : ℝ)^η*Z₀,by positivity,?_⟩
  intro D H X u g ξ W hD hH hHD hX _ hg hgD hW
  let G : Idl := span {g}
  let M := M₆*G
  let P := (normalizedFactors M).toFinset
  let t (A : Finset Idl) := ∏ p ∈ A, p
  let K (A : Finset Idl) := H / absNorm (t A)
  let f (s : Idl) := ‖completedAtElement ξ W X ((u:𝓔)*generator s) g‖^2
  let Q := H+H^2*absNorm G/X
  let Z := Z₀*D^(18*C₀*ρ)*Q
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hG : G ≠ 0 := mt span_singleton_eq_bot.mp hg
  have hM := mul_ne_zero hM₆ hG
  have hD₁ : 1 ≤ D := by linarith
  have hD₀ := zero_lt_one.trans_le hD₁
  have hslice (A : Finset Idl) (hA : A ∈ P.powerset) :
      ∑ k ∈ sieveIdeals M (K A), f (t A * k) ≤ (B*6^P.card)^2 * Z := by
    have hsub := mem_powerset.mp hA
    have ht : t A ≠ 0 := prod_ne_zero_iff.mpr (fun _ hp =>
      (prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (hsub hp))).ne_zero)
    have hNt := zero_lt_one.trans_le (absNorm_one_le ht)
    have hHK : K A * (absNorm (t A) : ℝ) = H := div_mul_cancel₀ _ hNt.ne'
    have hK₀ : 0 ≤ K A := by dsimp [K]; positivity
    by_cases hK : 1 ≤ K A
    · obtain ⟨n,b,hn,he⟩ := hr H X u g ξ W hH hX hg hW A hsub hK
      calc
        _ = ∑ k ∈ sieveIdeals M (K A), ‖∑ i, (b i).rowValue W k‖^2 := by
          apply sum_congr rfl
          intro k hk
          dsimp only [f]
          rw [show t A = ∏ p ∈ A,p from rfl,he k hk]
        _ ≤ (n:ℝ)^2 * Z := by
          apply sum_branches
          intro i
          let bi := b i
          have hv := (hs hK bi.length_pos bi.amplitude_nonneg W hW bi.rowClass bi.rows
            bi.rows_subset bi.rows_class bi.S bi.T bi.squarefree_band bi.cube_band bi.c bi.d bi.u
            bi.columns bi.row_phases bi.kernel_scale).2
          exact bi.squared_bound W hB hC hD₁ hK hX ht hG hHK hHD hgD hρ hρ₁ hv
        _ ≤ _ := by gcongr
    · have hempty : sieveIdeals M (K A) = ∅ := eq_empty_iff_forall_notMem.mpr (by
        intro k hk
        obtain ⟨hkn, hsf, _⟩ := mem_filter.mp hk
        exact hK ((absNorm_one_le hsf.ne_zero).trans ((mem_idealsLe hK₀).mp hkn)))
      simp only [hempty, sum_empty]; positivity
  have hsum := squarefree_cover_sum hH hM f (fun _ => sq_nonneg _)
  have hcard : (∑ _A ∈ P.powerset, (B*6^P.card)^2 * Z) = B^2*(72:ℝ)^P.card*Z := by
    simp only [sum_const,nsmul_eq_mul,card_powerset,Nat.cast_pow,Nat.cast_ofNat]
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, ← mul_assoc, mul_left_comm _ (B^2)]
    ring_nf
    rw [show (72:ℝ)=2*36 by norm_num,mul_pow]; ring
  have hcount : (72:ℝ)^P.card ≤ L * (absNorm M₆:ℝ)^η * D^(C₀*η) := calc
    _ ≤ L*(absNorm M:ℝ)^η := hl M hM P Subset.rfl
    _ = L*(absNorm M₆:ℝ)^η*(absNorm G:ℝ)^η := by
      dsimp [M]
      rw [map_mul,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity),mul_assoc]
    _ ≤ _ := by rw [Real.rpow_mul hD₀.le C₀ η]; gcongr; exact hgD
  calc
    _ ≤ _ := hsum
    _ ≤ _ := sum_le_sum hslice
    _ = _ := hcard
    _ ≤ B^2*(L*(absNorm M₆:ℝ)^η*D^(C₀*η))*Z := by gcongr
    _ = B^2*L*(absNorm M₆:ℝ)^η*Z₀ * D^(C₀*η+18*C₀*ρ)*Q := by
      rw [Real.rpow_add hD₀]; dsimp [Z]; ring
    _ ≤ _ := by
      change _ ≤ B^2*L*(absNorm M₆:ℝ)^η*Z₀ * D^ε*Q
      gcongr

end Masullo.QRH.MeanSquare.ReflectionSieve
