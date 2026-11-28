import Masullo.QRH.MeanSquare.Reciprocity
import Masullo.QRH.MeanSquare.GaussPhase
import Masullo.QRH.MeanSquare.Primary

/-! # Binary quadratic reciprocity for the Eisenstein Gauss sum -/

noncomputable section

open Matrix

namespace Masullo.QRH.MeanSquare
namespace DeloupTuraev

/-- The matrix for the quadratic Gauss sum with denominator `a + bω`. -/
def eisMatrix {R : Type*} [CommRing R] (a b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![b - a, -a; -a, -b]

theorem eisMatrix_det {R : Type*} [CommRing R] (a b : R) :
    (eisMatrix a b).det = -(a ^ 2 - a * b + b ^ 2) := by
  simp [eisMatrix, det_fin_two]
  ring

theorem eisMatrix_isSymm {R : Type*} [CommRing R] (a b : R) : (eisMatrix a b).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Rotation through a right angle in Eisenstein coordinates negates the quadratic form. -/
theorem eisMatrix_signature (a b : ℝ) : signature (eisMatrix a b) = 0 := by
  let J : Matrix (Fin 2) (Fin 2) ℝ := (√3)⁻¹ • !![-1, -2; 2, 1]
  have h3 := Masullo.Lattice.sqrt_three_pos.ne'
  have hdet : J.det = 1 := by
    simp [J, det_fin_two]
    field_simp
    nlinarith [Masullo.Lattice.sq_sqrt_three]
  let e := J.toLinearEquiv' (J.invertibleOfIsUnitDet (hdet ▸ isUnit_one))
  let Q := (eisMatrix a b).toQuadraticForm'
  have h : Q.Equivalent (-Q) := by
    refine ⟨{ __ := e, map_app' := ?_ }⟩
    intro x
    change - Q (J.mulVec x) = Q x
    simp [Q, J, toQuadraticForm', toLinearMap₂'_apply',
      mulVec, dotProduct, Fin.sum_univ_two, eisMatrix]
    field_simp
    linear_combination -(x 0 * ((b - a) * x 0 + -a * x 1) + x 1 * (-a * x 0 + -b * x 1)) *
      Masullo.Lattice.sq_sqrt_three
  exact sub_eq_zero.mpr (congrArg (Nat.cast : ℕ → ℤ) h.sigPos_eq)

private theorem eisMatrix_map_mulVec (a b : ℤ) (x : Fin 2 → ℤ) :
    (eisMatrix (a : ℝ) b).mulVec (fun i => (x i : ℝ)) =
      fun i => (((eisMatrix a b).mulVec x i : ℤ) : ℝ) := by
  funext i
  fin_cases i <;> simp [eisMatrix, mulVec, dotProduct, Fin.sum_univ_two]

private theorem lattice_one :
    lattice (1 : Matrix (Fin 2) (Fin 2) ℝ) = Set.range (fun x : Fin 2 → ℤ => fun i =>
      (x i : ℝ)) := by
  simp [lattice]

private theorem integral_dot (x y : Fin 2 → ℤ) :
    dotProduct (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) ∈ Set.range (Int.cast : ℤ → ℝ) :=
  ⟨dotProduct x y, by simp [dotProduct]⟩

/-- Deloup–Turaev at scale two. The normalized sum on the image lattice is a sum
over four residue classes, each carrying a fourth root of unity. -/
theorem quadratic_sum_reciprocity (h : DeloupTuraevTheorem1) (a b : ℤ)
    (hN : 0 < (a : ℝ) ^ 2 - a * b + b ^ 2)
    (s t : Finset (Fin 2 → ℝ))
    (hs : Representatives (lattice 1) ((fun x => (2 : ℝ) • x) '' lattice 1) s)
    (ht : Representatives (lattice 1) ((eisMatrix (a : ℝ) b).mulVec '' lattice 1) t) :
    (∑ y ∈ t, phase (-2 * dotProduct y ((eisMatrix (a : ℝ) b)⁻¹.mulVec y))) /
        Real.sqrt ((a : ℝ) ^ 2 - a * b + b ^ 2) =
      (∑ x ∈ s, phase (dotProduct x ((eisMatrix (a : ℝ) b).mulVec x) / 2)) / 2 := by
  let H := eisMatrix (a : ℝ) (b : ℝ)
  have hH : H.det ≠ 0 := by rw [eisMatrix_det]; exact neg_ne_zero.mpr hN.ne'
  have hr := h 2 1 H (by simp) hH (eisMatrix_isSymm ..) 0 2 (by decide)
  simp only [transpose_one, inv_one, det_one, abs_one, Complex.ofReal_one, one_mul,
    Nat.cast_ofNat, add_zero, dotProduct_zero, mul_zero, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_one] at hr
  have hmap {x : Fin 2 → ℝ} (hx : x ∈ lattice 1) : H.mulVec x ∈ lattice 1 := by
    rw [lattice_one] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(eisMatrix a b).mulVec y, (eisMatrix_map_mulVec a b y).symm⟩
  have hdot {x y : Fin 2 → ℝ} (hx : x ∈ lattice 1) (hy : y ∈ lattice 1) :
      dotProduct x y ∈ Set.range (Int.cast : ℤ → ℝ) := by
    rw [lattice_one] at hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact integral_dot u v
  have hzero : (0 : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) := ⟨0, Int.cast_zero⟩
  have hdouble {y : Fin 2 → ℝ} (hy : y ∈ lattice 1) : (2 : ℝ) • y ∈ lattice 1 := by
    rw [lattice_one] at hy ⊢
    obtain ⟨v, rfl⟩ := hy
    exact ⟨2 • v, by ext i; simp⟩
  specialize hr (fun _ hy => hmap hy)
    (fun _ hx _ hy => ⟨hdot hx (hmap hx), hdot hx (hmap hy), hzero⟩)
    (fun _ hx _ hy => ⟨hdot hx (hmap hx), hdot hx (hdouble hy), hzero⟩) s t hs ht
  rw [eisMatrix_signature, Int.cast_zero, zero_div, phase, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, eisMatrix_det, abs_neg, abs_of_pos hN] at hr
  push_cast at hr
  linear_combination -hr / 2

/-- The complex number with real coefficients in the basis `1, ω`. -/
def complexCoord (x : Fin 2 → ℝ) : ℂ := x 0 + x 1 * Masullo.Lattice.omega

private lemma complexCoord_normSq (x : Fin 2 → ℝ) :
    Complex.normSq (complexCoord x) = x 0 ^ 2 - x 0 * x 1 + x 1 ^ 2 := by
  simp [complexCoord, Complex.normSq_apply, Masullo.Lattice.omega]
  linear_combination (x 1 ^ 2 / 4) * Masullo.Lattice.sq_sqrt_three

/-- Inverse matrix phase in the basis `1, ω`. -/
theorem eisMatrix_inverse_phase (q x : Fin 2 → ℝ) (hq : complexCoord q ≠ 0) :
    phase (-2 * dotProduct x ((eisMatrix (q 0) (q 1))⁻¹.mulVec x)) =
      differentCharacter (complexCoord x ^ 2 / complexCoord q) := by
  have hN := Complex.normSq_pos.mpr hq
  rw [complexCoord_normSq] at hN
  have he : -dotProduct x ((eisMatrix (q 0) (q 1))⁻¹.mulVec x) =
      2 * (complexCoord x ^ 2 / complexCoord q).im / √3 := by
    rw [Matrix.inv_def, eisMatrix_det, Ring.inverse_eq_inv, Complex.div_im, complexCoord_normSq]
    simp [Matrix.adjugate_fin_two, eisMatrix, mulVec, dotProduct, Fin.sum_univ_two,
      complexCoord, Masullo.Lattice.omega, sq, Complex.mul_im, Complex.mul_re]
    field_simp [Masullo.Lattice.sqrt_three_pos.ne', hN.ne']
    ring_nf
    simp only [Masullo.Lattice.sq_sqrt_three]
    rw [show q 0 * q 1 - q 0 ^ 2 - q 1 ^ 2 = -(-(q 0 * q 1) + q 0 ^ 2 + q 1 ^ 2) by ring, inv_neg]
    ring
  unfold phase differentCharacter
  congr 1
  rw [← he]
  push_cast
  ring

private theorem phase_add_two_int (t : ℝ) (k : ℤ) : phase (t + 2 * k) = phase t := by
  unfold phase
  have h : (Real.pi : ℂ) * Complex.I * ((t + 2 * k : ℝ) : ℂ) =
      Real.pi * Complex.I * t + k * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- On the integral lattice the fourth-root phase depends only on the coefficients
of the denominator modulo four. -/
theorem eisMatrix_phase_congr {a b c d : ℤ} (ha : 4 ∣ c - a) (hb : 4 ∣ d - b)
    {x : Fin 2 → ℝ} (hx : x ∈ lattice 1) :
    phase (dotProduct x ((eisMatrix (c : ℝ) d).mulVec x) / 2) =
      phase (dotProduct x ((eisMatrix (a : ℝ) b).mulVec x) / 2) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  rw [lattice_one] at hx
  obtain ⟨x, rfl⟩ := hx
  have h (c d : ℤ) := eisMatrix_map_mulVec c d x
  rw [h, h]
  let k := dotProduct x ((eisMatrix u v).mulVec x)
  apply Eq.trans _ (phase_add_two_int _ k)
  congr 1
  have hc : c = a + 4 * u := by omega
  have hd : d = b + 4 * v := by omega
  simp [k, hc, hd, eisMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  ring

open NumberField Ideal

local notation "𝓔" => 𝓞 (CyclotomicField 3 ℚ)

/-- The normalized square exponential sum for the different character. -/
def quadraticExponentialSum (n : Ideal 𝓔) : ℂ :=
  (∑ᶠ x : 𝓔 ⧸ n, quotientDifferentCharacter n (x ^ 2)) / Real.sqrt (absNorm n)

/-- The embedding of the lattice coordinates in the orthonormal frame of the reciprocity formula. -/
private def vec (x : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => x i

private lemma vec_inj : Function.Injective vec := fun _ _ h => funext fun i =>
  Int.cast_injective (α := ℝ) (congrFun h i)

private def elem (x : Fin 2 → ℤ) : 𝓔 := x 0 + x 1 * eisOmega

private lemma embed_elem (x : Fin 2 → ℤ) : eisEmbedding (elem x) = complexCoord (vec x) := by
  simp [complexCoord, vec, elem, eisEmbedding_omega, Masullo.Lattice.omega_eq_exp]

private lemma elem_inj : Function.Injective elem := by
  intro x y h
  have he := congrArg eisEmbedding h
  simp only [embed_elem] at he
  have hi := congrArg Complex.im he
  have hr := congrArg Complex.re he
  simp [complexCoord, vec, Masullo.Lattice.omega] at hi hr
  have h₀ : x 0 = y 0 := by rw [hi] at hr; exact_mod_cast (add_right_cancel hr)
  funext i
  fin_cases i <;> assumption

private def coords : (Fin 2 → ℤ) ≃ 𝓔 := Equiv.ofBijective elem ⟨elem_inj, by
  intro e
  obtain ⟨a, b, he⟩ := eisInteger_coordinates e
  exact ⟨![a, b], he.symm⟩⟩

private lemma elem_coords_symm (x : 𝓔) : elem (coords.symm x) = x := coords.apply_symm_apply x

private lemma vec_mem (x : Fin 2 → ℤ) : vec x ∈ lattice 1 := by
  rw [lattice_one]
  exact ⟨x, rfl⟩

private lemma elem_sub (x y : Fin 2 → ℤ) : elem (x - y) = elem x - elem y := by
  simp [elem]
  ring

private lemma omega_sq : eisOmega ^ 2 + eisOmega + 1 = 0 := by
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  exact IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
    (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ))

private lemma elem_eisMatrix (q x : Fin 2 → ℤ) :
    elem ((eisMatrix (q 0) (q 1)).mulVec x) =
      elem q * elem ![-x 0 - x 1, -x 0] := by
  simp [elem, eisMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (q 1 : 𝓔) * (x 0 : 𝓔) * omega_sq

/-- The image lattice of the binary form consists of multiples of its Eisenstein denominator. -/
private lemma mem_image_eisMatrix (q x : Fin 2 → ℤ) :
    vec x ∈ (eisMatrix ((q 0 : ℤ) : ℝ) (q 1)).mulVec '' lattice 1 ↔ elem q ∣ elem x := by
  constructor
  · rintro ⟨y, hy, he⟩
    rw [lattice_one] at hy
    obtain ⟨y, rfl⟩ := hy
    have h := vec_inj ((eisMatrix_map_mulVec _ _ _).symm.trans he)
    exact ⟨_, h ▸ elem_eisMatrix q y⟩
  · rintro ⟨z, hz⟩
    let y := coords.symm z
    let w : Fin 2 → ℤ := ![-y 1, y 1 - y 0]
    have h : ![-w 0 - w 1, -w 0] = y := by
      ext i
      fin_cases i <;> simp [w]
    refine ⟨vec w, vec_mem w, (eisMatrix_map_mulVec _ _ _).trans (congrArg vec (elem_inj ?_))⟩
    rw [elem_eisMatrix, h, elem_coords_symm, hz]

private def rep (n : Ideal 𝓔) : (𝓔 ⧸ n) ↪ (Fin 2 → ℝ) where
  toFun x := vec (coords.symm (Quotient.out x))
  inj' := vec_inj.comp (coords.symm.injective.comp Quotient.out_injective)

private def reps (n : Ideal 𝓔) [Fintype (𝓔 ⧸ n)] : Finset (Fin 2 → ℝ) :=
  Finset.univ.map (rep n)

private lemma vec_sub (x y : Fin 2 → ℤ) : vec x - vec y = vec (x - y) := by
  ext i
  simp [vec]

private lemma sub_rep_mem_iff (n : Ideal 𝓔) (q : Fin 2 → ℤ) (hq : span {elem q} = n)
    (x : Fin 2 → ℤ) (y : 𝓔 ⧸ n) :
    vec x - rep n y ∈ (eisMatrix ((q 0 : ℤ) : ℝ) (q 1)).mulVec '' lattice 1 ↔
      Ideal.Quotient.mk n (elem x) = y := by
  change vec x - vec _ ∈ _ ↔ _
  rw [vec_sub, mem_image_eisMatrix, elem_sub, elem_coords_symm, ← mem_span_singleton, hq,
    ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

private theorem reps_eisMatrix (n : Ideal 𝓔) [Fintype (𝓔 ⧸ n)] (q : Fin 2 → ℤ)
    (hq : span {elem q} = n) :
    Representatives (lattice 1) ((eisMatrix ((q 0 : ℤ) : ℝ) (q 1)).mulVec '' lattice
      1) (reps n) := by
  classical
  have hmem (y : 𝓔 ⧸ n) : rep n y ∈ reps n := Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
  constructor
  · intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hy
    exact vec_mem _
  · intro x hx
    rw [lattice_one] at hx
    obtain ⟨x, rfl⟩ := hx
    let z := Ideal.Quotient.mk n (elem x)
    refine ⟨⟨rep n z, hmem z⟩, (sub_rep_mem_iff n q hq x z).mpr rfl, ?_⟩
    rintro ⟨v, hv⟩ hc
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hv
    exact Subtype.ext (congrArg (rep n) ((sub_rep_mem_iff n q hq x y).mp hc).symm)

private instance : Fintype (𝓔 ⧸ span {(2 : 𝓔)}) := by
  let := Ring.HasFiniteQuotients.finiteQuotient (I := span {(2 : 𝓔)}) (by simp)
  exact Fintype.ofFinite _

private lemma image_two :
    (eisMatrix 2 0).mulVec '' lattice 1 = (fun x => (2 : ℝ) • x) '' lattice 1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [lattice_one] at hx
    obtain ⟨x, rfl⟩ := hx
    refine ⟨vec ![-x 0 - x 1, -x 0], vec_mem _, ?_⟩
    ext i
    fin_cases i <;> simp [vec, eisMatrix, mulVec, dotProduct, Fin.sum_univ_two]; ring
  · rintro ⟨x, hx, rfl⟩
    rw [lattice_one] at hx
    obtain ⟨x, rfl⟩ := hx
    refine ⟨vec ![-x 1, x 1 - x 0], vec_mem _, ?_⟩
    ext i
    fin_cases i <;> simp [vec, eisMatrix, mulVec, dotProduct, Fin.sum_univ_two]; ring

private lemma reps_two : Representatives (lattice 1) ((fun x => (2 : ℝ) • x) '' lattice 1)
    (reps (span {(2 : 𝓔)})) := by
  rw [← image_two]
  simpa using reps_eisMatrix (span {(2 : 𝓔)}) ![2, 0] (by simp [elem])

private def quadraticRaySum (q : Fin 2 → ℤ) : ℂ :=
  (∑ x ∈ reps (span {(2 : 𝓔)}), phase (dotProduct x ((eisMatrix (q 0 : ℝ) (q 1)).mulVec x) / 2)) / 2

private theorem element_sum_eq_raySum (h : DeloupTuraevTheorem1) {n : Ideal 𝓔} (z : 𝓔)
    (hz : z ≠ 0) (hspan : span {z} = n) :
    (∑ᶠ y : 𝓔 ⧸ n, differentCharacter (eisEmbedding (Quotient.out y)^2 / eisEmbedding z)) /
      Real.sqrt (absNorm n) = quadraticRaySum (coords.symm z) := by
  classical
  have hn : n ≠ ⊥ := by simpa only [← hspan, ne_eq, span_singleton_eq_bot] using hz
  let := Ring.HasFiniteQuotients.finiteQuotient hn
  let := Fintype.ofFinite (𝓔 ⧸ n)
  let q := coords.symm z
  have hq : elem q = z := elem_coords_symm _
  have he : complexCoord (vec q) ≠ 0 := by
    rw [← embed_elem, hq]
    exact fun h => hz (eisEmbedding_injective (h.trans (map_zero _).symm))
  have hN : (q 0 : ℝ)^2 - q 0 * q 1 + q 1^2 = (absNorm n : ℝ) := by
    have hh := complexCoord_normSq (vec q)
    rw [← embed_elem, hq, ← Complex.sq_norm, norm_eisEmbedding_sq, hspan] at hh
    exact hh.symm
  have hpos : 0 < (q 0 : ℝ)^2 - q 0 * q 1 + q 1^2 :=
    (complexCoord_normSq (vec q)) ▸ Complex.normSq_pos.mpr he
  have hr := quadratic_sum_reciprocity h (q 0) (q 1) hpos _ (reps n) reps_two
    (reps_eisMatrix n q (hq ▸ hspan))
  rw [hN] at hr
  refine Eq.trans (congrArg (fun t : ℂ => t / Real.sqrt (absNorm n)) ?_) hr
  rw [reps, Finset.sum_map, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Eq.trans ?_ (eisMatrix_inverse_phase (vec q) (vec (coords.symm (Quotient.out y))) he).symm
  rw [← embed_elem, ← embed_elem, hq, elem_coords_symm]

set_option maxHeartbeats 800000 in
private theorem quadraticExponentialSum_eq_raySum (h : DeloupTuraevTheorem1) {n : Ideal 𝓔}
    (hn : n ≠ ⊥) : quadraticExponentialSum n = quadraticRaySum (coords.symm (generator n)) := by
  have hg : generator n ≠ 0 := fun hz => hn (by simpa [hz] using (span_generator n).symm)
  have hsum : (∑ᶠ y : 𝓔 ⧸ n, quotientDifferentCharacter n (y^2)) =
      ∑ᶠ y : 𝓔 ⧸ n, differentCharacter (eisEmbedding (Quotient.out y)^2 /
        eisEmbedding (generator n)) :=
    by
    classical
    let := Ring.HasFiniteQuotients.finiteQuotient hn
    let := Fintype.ofFinite (𝓔 ⧸ n)
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy := quotientDifferentCharacter_mk n ((Quotient.out (Ideal.Quotient.mk n x))^2)
    simpa only [map_pow, Ideal.Quotient.mk_out] using hy
  exact (congrArg (fun t : ℂ => t / Real.sqrt (absNorm n)) hsum).trans
    (element_sum_eq_raySum h _ hg (span_generator n))

private theorem quadraticRaySum_congr {a b : 𝓔}
    (hc : Ideal.Quotient.mk (span {(4 : 𝓔)}) a = Ideal.Quotient.mk (span {(4 : 𝓔)}) b) :
    quadraticRaySum (coords.symm a) = quadraticRaySum (coords.symm b) := by
  let q := coords.symm a
  let r := coords.symm b
  obtain ⟨z, hz⟩ := mem_span_singleton.mp (Ideal.Quotient.eq.mp hc)
  let t := coords.symm z
  have he : q - r = (4 : ℤ) • t := by
    apply elem_inj
    rw [elem_sub, elem_coords_symm, elem_coords_symm, hz]
    have hs : elem ((4 : ℤ) • t) = 4 * elem t := by simp [elem]; ring
    rw [hs, elem_coords_symm]
  have hd (i : Fin 2) : 4 ∣ q i - r i := ⟨t i, by simpa using congrFun he i⟩
  apply congrArg (fun z : ℂ => z / 2)
  exact Finset.sum_congr rfl fun x hx => eisMatrix_phase_congr (hd 0) (hd 1) (reps_two.1 hx)

/-- Fourth-root sum over the four classes modulo two, evaluated at a denominator class modulo
four. -/
def quadraticRayValue (r : 𝓔 ⧸ span {(4 : 𝓔)}) : ℂ :=
  quadraticRaySum (coords.symm (Quotient.out r))

theorem quadraticRayValue_mk (h : DeloupTuraevTheorem1) {n : Ideal 𝓔} (hn : n ≠ ⊥) :
    quadraticRayValue (Ideal.Quotient.mk _ (generator n)) = quadraticExponentialSum n := by
  rw [quadraticExponentialSum_eq_raySum h hn]
  exact quadraticRaySum_congr (Ideal.Quotient.mk_out _)

/-- The normalized quadratic exponential sum depends only on the chosen generator modulo four. -/
theorem quadraticExponentialSum_eq_of_mk_four_eq (h : DeloupTuraevTheorem1)
    {m n : Ideal 𝓔} (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hc : Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator m) =
      Ideal.Quotient.mk (span {(4 : 𝓔)}) (generator n)) :
    quadraticExponentialSum m = quadraticExponentialSum n := by
  rw [← quadraticRayValue_mk h hm, hc, quadraticRayValue_mk h hn]

/-- One set of four lattice representatives computes the quadratic ray value at
every residue. The two coefficients are in the Eisenstein basis `1, ω`. -/
theorem quadraticRayValue_representatives :
    ∃ s, Representatives (lattice 1) ((fun x => (2 : ℝ) • x) '' lattice 1) s ∧
      ∀ a b : ℤ, quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) ((a : 𝓔) +
        (b : 𝓔) * eisOmega)) =
        (∑ x ∈ s, phase (dotProduct x ((eisMatrix (a : ℝ) b).mulVec x) / 2)) / 2 := by
  refine ⟨reps (span {(2 : 𝓔)}), reps_two, ?_⟩
  intro a b
  let x : 𝓔 := a + b * eisOmega
  have hc : coords.symm x = ![a,b] := coords.symm_apply_eq.mpr rfl
  rw [quadraticRayValue, quadraticRaySum_congr (Ideal.Quotient.mk_out _)]
  change quadraticRaySum (coords.symm x) = _
  rw [hc]
  rfl

/-- Deloup–Turaev identifies the same value on any representatives modulo two.
Both evaluations use the same representatives modulo the Eisenstein matrix. -/
theorem quadraticRayValue_of_representatives (quad : DeloupTuraevTheorem1) (a b : ℤ)
    (hN : 0 < (a : ℝ)^2 - a*b + b^2)
    {s : Finset (Fin 2 → ℝ)}
      (hs : Representatives (lattice 1) ((fun x => (2 : ℝ) • x) '' lattice 1) s) :
    quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) ((a : 𝓔) + (b : 𝓔)*eisOmega)) =
      (∑ x ∈ s, phase (dotProduct x ((eisMatrix (a : ℝ) b).mulVec x) / 2)) / 2 := by
  classical
  obtain ⟨s₀, hs₀, hval⟩ := quadraticRayValue_representatives
  let q : Fin 2 → ℤ := ![a,b]
  let J : Ideal 𝓔 := span {elem q}
  have hJ : J ≠ ⊥ := by
    intro he
    have hz := elem_inj (show elem q = elem 0 by simpa [elem] using (span_singleton_eq_bot.mp he))
    have ha : a = 0 := congrFun hz 0
    have hb : b = 0 := congrFun hz 1
    simp [ha, hb] at hN
  let := Ring.HasFiniteQuotients.finiteQuotient hJ
  let := Fintype.ofFinite (𝓔 ⧸ J)
  have ht := reps_eisMatrix J q rfl
  exact (hval a b).trans ((quadratic_sum_reciprocity quad a b hN _ _ hs₀ ht).symm.trans
    (quadratic_sum_reciprocity quad a b hN _ _ hs ht))

/-- The quadratic ray value for an element denominator, with its specified
associate in the additive character. -/
theorem quadraticRayValue_eq_element_sum (h : DeloupTuraevTheorem1) {n : Ideal 𝓔} (z : 𝓔)
    (hz : z ≠ 0) (hspan : span {z} = n) :
    quadraticRayValue (Ideal.Quotient.mk (span {(4 : 𝓔)}) z) =
      (∑ᶠ y : 𝓔 ⧸ n, differentCharacter (eisEmbedding (Quotient.out y)^2 / eisEmbedding z)) /
        Real.sqrt (absNorm n) := by
  rw [element_sum_eq_raySum h z hz hspan, quadraticRayValue]
  exact quadraticRaySum_congr (Ideal.Quotient.mk_out _)

end DeloupTuraev
end Masullo.QRH.MeanSquare
