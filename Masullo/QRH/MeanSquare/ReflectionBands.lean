import Masullo.QRH.MeanSquare.ReflectionExtraction
import Masullo.QRH.MeanSquare.ReflectionVaryingRows

/-! # Dyadic reindexing of squarefree and cube ideals in the reflected sum -/

noncomputable section

open NumberField Ideal Finset Set

namespace Masullo.QRH.MeanSquare.ReflectionSieve

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)
private abbrev Idl := Ideal 𝓔

/-- Half-open dyadic block of unrestricted cube ideals. -/
def cubeBand (i : ℕ) : Finset Idl := open Classical in
  (idealsLe (2*2^i)).filter fun b => (2:ℝ)^i ≤ absNorm b ∧ (absNorm b : ℝ) < 2*2^i

abbrev squarefreeBand (i : ℕ) : Finset Idl := dyadicSieveIdeals (span {6}) (2^i)

private theorem band_iff {n : ℕ} {i : ℕ} :
    (n:ℝ) ∈ Ico ((2:ℝ)^i) (2*2^i) ↔ n ≠ 0 ∧ Nat.log 2 n = i := by
  have natBand : (n:ℝ) ∈ Ico ((2:ℝ)^i) (2*2^i) ↔ 2^i ≤ n ∧ n < 2^(i+1) := by
    rw [Set.mem_Ico,pow_succ,mul_comm (2^i : ℕ)]
    constructor <;> rintro ⟨h,k⟩ <;> exact ⟨by exact_mod_cast h,by exact_mod_cast k⟩
  rw [natBand]
  constructor
  · rintro ⟨h,k⟩
    exact ⟨(lt_of_lt_of_le (by positivity) h).ne',Nat.log_eq_of_pow_le_of_lt_pow h k⟩
  · rintro ⟨h,rfl⟩
    exact ⟨Nat.pow_log_le_self 2 h,Nat.lt_pow_succ_log_self (by decide) n⟩

theorem mem_cubeBand {b : Idl} {i : ℕ} :
    b ∈ cubeBand i ↔ b ≠ 0 ∧ Nat.log 2 (absNorm b) = i := by
  classical
  rw [cubeBand,mem_filter]
  have h : (absNorm b : ℝ) ∈ Ico ((2:ℝ)^i) (2*2^i) ↔ b ≠ 0 ∧ Nat.log 2 (absNorm b) = i := by
    rw [band_iff]; simp
  exact ⟨fun hx => h.mp hx.2,fun hx => ⟨(mem_idealsLe (by positivity)).mpr (h.mpr hx).2.le,h.mpr
    hx⟩⟩

theorem mem_squarefreeBand {n : Idl} {i : ℕ} :
    n ∈ squarefreeBand i ↔ Starred n ∧ Nat.log 2 (absNorm n) = i := by
  classical
  simp only [squarefreeBand,dyadicSieveIdeals,sieveIdeals,mem_filter,Set.Finite.mem_toFinset]
  change ((absNorm n ≤ ⌊2* (2:ℝ)^i⌋₊) ∧ Squarefree n ∧ IsCoprime n (span {6})) ∧ _ ↔ _
  refine ⟨fun ⟨⟨_,hs,hc⟩,hb⟩ => ⟨⟨⟨hs.ne_zero,hc⟩,hs⟩,(band_iff.mp hb).2⟩,?_⟩
  rintro ⟨hs,hi⟩
  have hb := band_iff.mpr (And.intro (by simpa using hs.1.1 : absNorm n ≠ 0) hi)
  exact ⟨⟨(Nat.le_floor_iff (by positivity)).mpr hb.2.le,hs.2,hs.1.2⟩,hb⟩

abbrev ReflectedColumns := ℕ × {b : Idl // b ≠ 0} × {n : Idl // Starred n}

/-- Each pair belongs to one and only one pair of dyadic norm bands. -/
def bandEquiv : (Σ e : ℕ × ℕ × ℕ, (cubeBand e.2.2) × (squarefreeBand e.2.1)) ≃ ReflectedColumns
    where
  toFun x := (x.1.1,⟨x.2.1.val,(mem_cubeBand.mp x.2.1.property).1⟩,
    ⟨x.2.2.val,(mem_squarefreeBand.mp x.2.2.property).1⟩)
  invFun x := ⟨(x.1,Nat.log 2 (absNorm x.2.2.val),Nat.log 2 (absNorm x.2.1.val)),
    ⟨x.2.1.val,mem_cubeBand.mpr ⟨x.2.1.property,rfl⟩⟩,
    ⟨x.2.2.val,mem_squarefreeBand.mpr ⟨x.2.2.property,rfl⟩⟩⟩
  left_inv := by
    rintro ⟨⟨m,i,j⟩,⟨b,hb⟩,⟨n,hn⟩⟩
    obtain rfl := (mem_cubeBand.mp hb).2
    obtain rfl := (mem_squarefreeBand.mp hn).2
    rfl
  right_inv := by rintro ⟨_,⟨_,_⟩,⟨_,_⟩⟩; rfl

/-- The absolutely convergent dual sum may be grouped into the exact blocks
on which the quadratic sieve is applied. -/
theorem tsum_bands (f : ℕ → Idl → Idl → ℂ)
    (hs : Summable (fun x : ReflectedColumns => f x.1 x.2.1.val x.2.2.val)) :
    (∑' x : ReflectedColumns, f x.1 x.2.1.val x.2.2.val) =
      ∑' e : ℕ × ℕ × ℕ, ∑ b ∈ cubeBand e.2.2, ∑ n ∈ squarefreeBand e.2.1, f e.1 b n := by
  classical
  let F := fun x : ReflectedColumns => f x.1 x.2.1.val x.2.2.val
  rw [← bandEquiv.tsum_eq F]
  have h := (bandEquiv.summable_iff.mpr hs).tsum_sigma
  refine h.trans (tsum_congr fun e => ?_)
  simp only [tsum_fintype,Fintype.sum_prod_type]
  exact (cubeBand e.2.2).sum_coe_sort (fun b => ∑ n : squarefreeBand e.2.1, f e.1 b n) |>.trans
    (sum_congr rfl (fun b _ => (squarefreeBand e.2.1).sum_coe_sort (f e.1 b)))

/-- The good part of a squarefree column after removing its prime above two. -/
def twoPart (e : Fin 2) : Idl := (span {(-2:𝓔)})^(e : ℕ)

theorem twoPart_eq {i j : Fin 2} {n n' : Idl} (hn : Starred n) (hn' : Starred n')
    (h : twoPart i * n = twoPart j * n') : i = j ∧ n = n' := by
  let P : Idl := span {(-2:𝓔)}
  have hprime : Prime P := prime_span_singleton_iff.mpr ReflectionTwist.neg_two_prime
  have h₆ : P ∣ span {(6:𝓔)} := by
    refine dvd_iff_le.mpr (span_singleton_le_span_singleton.mpr ?_)
    exact ⟨-3,by norm_num⟩
  have hnot {a : Idl} (ha : Starred a) : ¬P ∣ a := fun hx =>
    hprime.not_isUnit (ha.1.2.isUnit_of_dvd' hx h₆)
  have hval (e : Fin 2) (a : Idl) (ha : Starred a) :
      emultiplicity P (twoPart e*a) = (e.val : ℕ∞) := by
    rw [emultiplicity_mul hprime,emultiplicity_eq_zero.mpr (hnot ha),add_zero]
    exact emultiplicity_pow_self_of_prime hprime _
  have hij := congrArg (emultiplicity P) h
  rw [hval _ _ hn,hval _ _ hn'] at hij
  obtain rfl : i = j := Fin.ext (by exact_mod_cast hij)
  exact ⟨rfl,mul_left_cancel₀ (pow_ne_zero _ hprime.ne_zero) h⟩

/-- Sum over the unit and the possible factor above two explicitly, extending
the original coefficient by zero when the primary cube ideal is ramified. -/
def extendIndex (f : ReflectedIndex → ℂ) (u : 𝓔ˣ) (e : Fin 2) (h : ℕ) (b n : Idl) : ℂ :=
  open Classical in
  if hs : Squarefree (twoPart e*n) ∧ IsCoprime (twoPart e*n) (span {3}) ∧
      IsCoprime b (span {3}) ∧ Starred n then
    f ⟨h,u,twoPart e*n,b,hs.2.1,hs.2.2.1,hs.1⟩
  else 0

theorem tsum_split_index (f : ReflectedIndex → ℂ) (hf : Summable f) :
    ∑' x, f x = ∑' u : 𝓔ˣ, ∑ e : Fin 2, ∑' x : ℕ × Idl × Idl,
      extendIndex f u e x.1 x.2.1 x.2.2 := by
  classical
  let J := 𝓔ˣ × Fin 2 × ℕ × Idl × Idl
  let J₀ (x : J) := Squarefree (twoPart x.2.1*x.2.2.2.2) ∧
    IsCoprime (twoPart x.2.1*x.2.2.2.2) (span {3}) ∧ IsCoprime x.2.2.2.1 (span {3}) ∧
      Starred x.2.2.2.2
  let g (x : Subtype J₀) : ReflectedIndex :=
    ⟨x.1.2.2.1,x.1.1,twoPart x.1.2.1*x.1.2.2.2.2,x.1.2.2.2.1,x.2.2.1,x.2.2.2.1,x.2.1⟩
  have hi : Function.Injective g := by
    rintro ⟨⟨u,i,h,b,n⟩,hx⟩ ⟨⟨u',j,h',b',n'⟩,hy⟩ he
    obtain ⟨hi,hn⟩ := twoPart_eq hx.2.2.2 hy.2.2.2 (congrArg ReflectedIndex.n he)
    have hu := congrArg ReflectedIndex.unit he
    have hh := congrArg ReflectedIndex.exponent he
    have hb := congrArg ReflectedIndex.b he
    exact Subtype.ext (Prod.ext hu (Prod.ext hi (Prod.ext hh (Prod.ext hb hn))))
  have hsur : Function.Surjective g := by
    intro x
    obtain ⟨e,n,hs,hn,_⟩ := ReflectionVaryingRows.split_column_two x.squarefree_n x.coprime_n
    refine ⟨⟨(x.unit,e,x.exponent,x.b,n),?_⟩,?_⟩
    · change Squarefree (twoPart e*n) ∧ IsCoprime (twoPart e*n) (span {3}) ∧ _
      exact ⟨hn ▸ x.squarefree_n,hn ▸ x.coprime_n,x.coprime_b,hs⟩
    · cases x
      dsimp [g,twoPart]
      congr 1
      exact hn.symm
  let F (x : J) := extendIndex f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  have he (x : Subtype J₀) : F x = f (g x) := dite_eq_left x.property
  have hz (x : J) (hx : ¬ J₀ x) : F x = 0 := dite_eq_right hx
  have hs : Summable F := (Subtype.val_injective.summable_iff (fun x hx =>
    hz x (by simpa using hx))).mp
    ((hf.comp_injective hi).congr (fun x => (he x).symm))
  calc
    _ = ∑' x : Subtype J₀, F x := (hi.tsum_eq (fun a _ => hsur a)).symm.trans (tsum_congr fun x =>
      (he x).symm)
    _ = ∑' x, F x := Subtype.val_injective.tsum_eq fun x hx => ⟨⟨x,by_contra fun h =>
      hx (hz x h)⟩,rfl⟩
    _ = _ := hs.tsum_prod.trans (tsum_congr fun u => (hs.prod_factor u).tsum_prod.trans (by
      rw [tsum_fintype]))

end Masullo.QRH.MeanSquare.ReflectionSieve
