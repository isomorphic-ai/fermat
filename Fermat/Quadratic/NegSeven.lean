import Mathlib

/-!
# The maximal order of `ℚ(√-7)`

This file models `ℤ[(1 + √-7) / 2]` in the integral basis `1, ω`, where
`ω = (1 + √-7) / 2` and hence `ω² = ω - 2`.  Thus a pair `⟨a, b⟩`
represents `a + b * ω`.
-/

namespace Fermat.Quadratic.NegSeven

/-- The maximal order `ℤ[(1 + √-7) / 2]`, in the basis `1, ω`. -/
@[ext]
structure MaximalOrder where
  /-- Coefficient of `1`. -/
  re : ℤ
  /-- Coefficient of `ω = (1 + √-7) / 2`. -/
  im : ℤ
  deriving DecidableEq, Repr

namespace MaximalOrder

/-- Embed an integer in the maximal order. -/
def ofInt (n : ℤ) : MaximalOrder :=
  ⟨n, 0⟩

instance : Zero MaximalOrder := ⟨ofInt 0⟩
instance : One MaximalOrder := ⟨ofInt 1⟩
instance : Inhabited MaximalOrder := ⟨0⟩

/-- The integral generator `ω = (1 + √-7) / 2`. -/
def omega : MaximalOrder :=
  ⟨0, 1⟩

instance : Add MaximalOrder :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

instance : Neg MaximalOrder :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

/-- Multiplication is determined by `ω² = ω - 2`. -/
instance : Mul MaximalOrder :=
  ⟨fun z w =>
    ⟨z.re * w.re - 2 * z.im * w.im,
      z.re * w.im + z.im * w.re + z.im * w.im⟩⟩

@[simp] theorem re_zero : (0 : MaximalOrder).re = 0 := rfl
@[simp] theorem im_zero : (0 : MaximalOrder).im = 0 := rfl
@[simp] theorem re_one : (1 : MaximalOrder).re = 1 := rfl
@[simp] theorem im_one : (1 : MaximalOrder).im = 0 := rfl
@[simp] theorem re_omega : omega.re = 0 := rfl
@[simp] theorem im_omega : omega.im = 1 := rfl

@[simp] theorem re_add (z w : MaximalOrder) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : MaximalOrder) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_neg (z : MaximalOrder) : (-z).re = -z.re := rfl
@[simp] theorem im_neg (z : MaximalOrder) : (-z).im = -z.im := rfl

@[simp] theorem re_mul (z w : MaximalOrder) :
    (z * w).re = z.re * w.re - 2 * z.im * w.im := rfl

@[simp] theorem im_mul (z w : MaximalOrder) :
    (z * w).im = z.re * w.im + z.im * w.re + z.im * w.im := rfl

instance instAddCommGroup : AddCommGroup MaximalOrder := by
  refine
    { sub := fun a b => a + -b
      nsmul := @nsmulRec MaximalOrder ⟨0⟩ ⟨(· + ·)⟩
      zsmul := @zsmulRec MaximalOrder ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
        (@nsmulRec MaximalOrder ⟨0⟩ ⟨(· + ·)⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;>
    ext <;>
    simp [add_comm, add_left_comm]

@[simp] theorem re_sub (z w : MaximalOrder) : (z - w).re = z.re - w.re := rfl
@[simp] theorem im_sub (z w : MaximalOrder) : (z - w).im = z.im - w.im := rfl

instance instAddGroupWithOne : AddGroupWithOne MaximalOrder :=
  { instAddCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

instance instCommRing : CommRing MaximalOrder := by
  refine
    { instAddGroupWithOne with
      npow := @npowRec MaximalOrder ⟨1⟩ ⟨(· * ·)⟩
      add_comm := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      mul_comm := ?_ } <;>
    intros <;>
    ext <;>
    simp <;>
    ring

@[simp] theorem re_natCast (n : ℕ) : (n : MaximalOrder).re = n := rfl
@[simp] theorem im_natCast (n : ℕ) : (n : MaximalOrder).im = 0 := rfl
@[simp] theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : MaximalOrder).re = n := rfl
@[simp] theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : MaximalOrder).im = 0 := rfl
@[simp] theorem re_intCast (n : ℤ) : (n : MaximalOrder).re = n := by cases n <;> rfl
@[simp] theorem im_intCast (n : ℤ) : (n : MaximalOrder).im = 0 := by cases n <;> rfl

instance : CharZero MaximalOrder where
  cast_injective m n := by simp [MaximalOrder.ext_iff]

@[simp] theorem ofInt_eq_intCast (n : ℤ) : ofInt n = (n : MaximalOrder) := by
  ext <;> simp [ofInt]

@[simp] theorem omega_sq : omega ^ 2 = omega - 2 := by
  ext <;> norm_num [pow_two]

/-- Algebraic conjugation, determined by `conj ω = 1 - ω`. -/
def conj (z : MaximalOrder) : MaximalOrder :=
  ⟨z.re + z.im, -z.im⟩

instance : Star MaximalOrder := ⟨conj⟩

@[simp] theorem re_conj (z : MaximalOrder) : (conj z).re = z.re + z.im := rfl
@[simp] theorem im_conj (z : MaximalOrder) : (conj z).im = -z.im := rfl
@[simp] theorem star_def (z : MaximalOrder) : star z = conj z := rfl
@[simp] theorem re_star (z : MaximalOrder) : (star z).re = z.re + z.im := rfl
@[simp] theorem im_star (z : MaximalOrder) : (star z).im = -z.im := rfl
@[simp] theorem star_omega : star omega = 1 - omega := by ext <;> simp [conj]

instance instStarRing : StarRing MaximalOrder where
  star_involutive z := by ext <;> simp [conj]
  star_mul z w := by ext <;> simp [conj] <;> ring
  star_add z w := by ext <;> simp [conj] <;> ring

/-- The field norm `N(a + bω) = a² + ab + 2b²`. -/
def norm (z : MaximalOrder) : ℤ :=
  z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2

theorem norm_def (z : MaximalOrder) :
    norm z = z.re ^ 2 + z.re * z.im + 2 * z.im ^ 2 := rfl

@[simp] theorem norm_zero : norm 0 = 0 := by simp [norm]
@[simp] theorem norm_one : norm 1 = 1 := by simp [norm]
@[simp] theorem norm_omega : norm omega = 2 := by norm_num [norm]
@[simp] theorem norm_intCast (n : ℤ) : norm (n : MaximalOrder) = n ^ 2 := by simp [norm]
@[simp] theorem norm_natCast (n : ℕ) : norm (n : MaximalOrder) = n ^ 2 := by simp [norm]

@[simp] theorem norm_mul (z w : MaximalOrder) : norm (z * w) = norm z * norm w := by
  simp only [norm, re_mul, im_mul]
  ring

/-- The norm as a multiplicative homomorphism. -/
def normMonoidHom : MaximalOrder →* ℤ where
  toFun := norm
  map_one' := norm_one
  map_mul' := norm_mul

theorem norm_eq_mul_star (z : MaximalOrder) : (norm z : MaximalOrder) = z * star z := by
  apply MaximalOrder.ext
  · change norm z = z.re * (z.re + z.im) - 2 * z.im * (-z.im)
    simp [norm]
    ring
  · change 0 = z.re * (-z.im) + z.im * (z.re + z.im) + z.im * (-z.im)
    ring

/-- Multiplication by the conjugate is the (integer) norm. -/
theorem mul_conj (z : MaximalOrder) : z * conj z = (norm z : MaximalOrder) := by
  rw [← star_def, ← norm_eq_mul_star]

@[simp] theorem norm_neg (z : MaximalOrder) : norm (-z) = norm z := by
  simp [norm]

@[simp] theorem norm_star (z : MaximalOrder) : norm (star z) = norm z := by
  simp only [norm, re_star, im_star]
  ring

/-- Completing the square for the norm. -/
theorem four_mul_norm (z : MaximalOrder) :
    4 * norm z = (2 * z.re + z.im) ^ 2 + 7 * z.im ^ 2 := by
  simp [norm]
  ring

theorem norm_nonneg (z : MaximalOrder) : 0 ≤ norm z := by
  have h := four_mul_norm z
  nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]

@[simp] theorem norm_eq_zero {z : MaximalOrder} : norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hs : (2 * z.re + z.im) ^ 2 + 7 * z.im ^ 2 = 0 := by
      rw [← four_mul_norm, h]
      norm_num
    have himsq : z.im ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]
    have him : z.im = 0 := sq_eq_zero_iff.mp himsq
    have hresq : z.re ^ 2 = 0 := by simpa [him] using hs
    have hre : z.re = 0 := sq_eq_zero_iff.mp hresq
    ext <;> simp [hre, him]
  · rintro rfl
    exact norm_zero

theorem norm_pos {z : MaximalOrder} : 0 < norm z ↔ z ≠ 0 :=
  (norm_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans norm_eq_zero)

theorem norm_eq_one_iff_isUnit {z : MaximalOrder} : norm z = 1 ↔ IsUnit z := by
  constructor
  · intro h
    apply isUnit_iff_dvd_one.mpr
    refine ⟨star z, ?_⟩
    rw [← norm_eq_mul_star, h]
    rfl
  · intro hz
    have hn : IsUnit (norm z) := hz.map normMonoidHom
    rcases Int.isUnit_eq_one_or hn with h | h
    · exact h
    · have := norm_nonneg z
      omega

theorem isUnit_iff_norm_eq_one {z : MaximalOrder} : IsUnit z ↔ norm z = 1 :=
  norm_eq_one_iff_isUnit.symm

/-- The only units of `ℤ[(1 + √-7) / 2]` are `1` and `-1`. -/
theorem eq_one_or_neg_one_of_isUnit {z : MaximalOrder} (hz : IsUnit z) :
    z = 1 ∨ z = -1 := by
  have hn : norm z = 1 := isUnit_iff_norm_eq_one.mp hz
  have hfour := four_mul_norm z
  rw [hn] at hfour
  have himsq : z.im ^ 2 = 0 := by
    have hs := sq_nonneg (2 * z.re + z.im)
    have hi := sq_nonneg z.im
    omega
  have him : z.im = 0 := sq_eq_zero_iff.mp himsq
  have hre : z.re ^ 2 = 1 := by simpa [norm, him] using hn
  rcases sq_eq_one_iff.mp hre with hre | hre
  · left
    ext <;> simp [hre, him]
  · right
    ext <;> simp [hre, him]

theorem isUnit_iff_eq_one_or_neg_one {z : MaximalOrder} :
    IsUnit z ↔ z = 1 ∨ z = -1 := by
  constructor
  · exact eq_one_or_neg_one_of_isUnit
  · rintro (rfl | rfl) <;> simp

instance instNontrivial : Nontrivial MaximalOrder :=
  ⟨⟨0, 1, by intro h; have := congrArg MaximalOrder.re h; norm_num at this⟩⟩

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {z w : MaximalOrder}
    (h : z * w = 0) : z = 0 ∨ w = 0 := by
  have hn : norm z * norm w = 0 := by simpa using congrArg norm h
  rcases mul_eq_zero.mp hn with hz | hw
  · exact Or.inl (norm_eq_zero.mp hz)
  · exact Or.inr (norm_eq_zero.mp hw)

instance instNoZeroDivisors : NoZeroDivisors MaximalOrder where
  eq_zero_or_eq_zero_of_mul_eq_zero := MaximalOrder.eq_zero_or_eq_zero_of_mul_eq_zero

instance instIsDomain : IsDomain MaximalOrder :=
  NoZeroDivisors.to_isDomain _

/-- The inclusion `ℤ[√-7] ↪ ℤ[(1 + √-7) / 2]`.

In basis coordinates, `P + Q√-7 = (P - Q) + 2Qω`.
-/
def embed : Zsqrtd (-7) →+* MaximalOrder where
  toFun z := ⟨z.re - z.im, 2 * z.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp <;> ring
  map_mul' z w := by ext <;> simp <;> ring

@[simp] theorem embed_re (z : Zsqrtd (-7)) : (embed z).re = z.re - z.im := rfl
@[simp] theorem embed_im (z : Zsqrtd (-7)) : (embed z).im = 2 * z.im := rfl

@[simp] theorem embed_apply (p q : ℤ) :
    embed (⟨p, q⟩ : Zsqrtd (-7)) = ⟨p - q, 2 * q⟩ := rfl

@[simp] theorem star_embed (z : Zsqrtd (-7)) : star (embed z) = embed (star z) := by
  apply MaximalOrder.ext
  · simp [conj]
    ring
  · simp [conj]

@[simp] theorem conj_embed (z : Zsqrtd (-7)) : conj (embed z) = embed (star z) :=
  by change star (embed z) = embed (star z); exact star_embed z

@[simp] theorem norm_embed (z : Zsqrtd (-7)) :
    norm (embed z) = z.re ^ 2 + 7 * z.im ^ 2 := by
  simp [norm]
  ring

theorem embed_injective : Function.Injective embed := by
  intro z w h
  have him : z.im = w.im := by
    have := congrArg MaximalOrder.im h
    simp only [embed_im] at this
    omega
  have hre : z.re = w.re := by
    have := congrArg MaximalOrder.re h
    simp only [embed_re, him] at this
    omega
  exact Zsqrtd.ext hre him

/-! ## Euclidean division -/

/-- First coefficient of `x / y` in the rational basis `1, ω`. -/
private def quotientRe (x y : MaximalOrder) : ℚ :=
  (x * star y).re / norm y

/-- Second coefficient of `x / y` in the rational basis `1, ω`. -/
private def quotientIm (x y : MaximalOrder) : ℚ :=
  (x * star y).im / norm y

/-- Round in the skew basis `1, ω`.  After rounding the `ω` coefficient, the
half-unit correction makes the real Euclidean coordinate the nearest integer. -/
private def quotient (x y : MaximalOrder) : MaximalOrder :=
  let v := quotientIm x y
  let b := round v
  let u := quotientRe x y
  ⟨round (u + (v - b) / 2), b⟩

instance instDiv : Div MaximalOrder := ⟨quotient⟩

theorem div_def (x y : MaximalOrder) :
    x / y =
      let v := quotientIm x y
      let b := round v
      let u := quotientRe x y
      ⟨round (u + (v - b) / 2), b⟩ := rfl

@[simp] theorem im_div (x y : MaximalOrder) : (x / y).im = round (quotientIm x y) := rfl

@[simp] theorem re_div (x y : MaximalOrder) :
    (x / y).re =
      round (quotientRe x y + (quotientIm x y - round (quotientIm x y)) / 2) := rfl

/-- The rounded rational quotient is within norm strictly less than one. -/
private theorem quotient_error_norm_lt_one (x y : MaximalOrder) :
    let f : ℚ := quotientIm x y - round (quotientIm x y)
    let g : ℚ := quotientRe x y + f / 2 -
      round (quotientRe x y + f / 2)
    g ^ 2 + 7 * f ^ 2 / 4 < 1 := by
  dsimp only
  let f : ℚ := quotientIm x y - round (quotientIm x y)
  let g : ℚ := quotientRe x y + f / 2 - round (quotientRe x y + f / 2)
  have hf : |f| ≤ (1 : ℚ) / 2 := by
    simpa [f] using abs_sub_round (quotientIm x y)
  have hg : |g| ≤ (1 : ℚ) / 2 := by
    simpa [g] using abs_sub_round (quotientRe x y + f / 2)
  have hf_sq : f ^ 2 ≤ ((1 : ℚ) / 2) ^ 2 := sq_le_sq.mpr (by simpa using hf)
  have hg_sq : g ^ 2 ≤ ((1 : ℚ) / 2) ^ 2 := sq_le_sq.mpr (by simpa using hg)
  dsimp only [f, g] at hf_sq hg_sq ⊢
  nlinarith

instance instMod : Mod MaximalOrder :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : MaximalOrder) : x % y = x - y * (x / y) := rfl

private theorem norm_remainder_div_norm (x y : MaximalOrder) (hy : y ≠ 0) :
    (norm (x - y * (x / y)) : ℚ) / norm y =
      let f : ℚ := quotientIm x y - round (quotientIm x y)
      let g : ℚ := quotientRe x y + f / 2 -
        round (quotientRe x y + f / 2)
      g ^ 2 + 7 * f ^ 2 / 4 := by
  have hn_int : norm y ≠ 0 := (norm_pos.mpr hy).ne'
  dsimp only
  let N : ℚ := norm y
  let U : ℚ := quotientRe x y
  let V : ℚ := quotientIm x y
  let B : ℚ := round V
  let f : ℚ := V - B
  let A : ℚ := round (U + f / 2)
  let g : ℚ := U + f / 2 - A
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast hn_int
  change (norm (x - y * (x / y)) : ℚ) / N = g ^ 2 + 7 * f ^ 2 / 4
  have hU : ((x * star y).re : ℚ) = U * N := by
    dsimp [U, N, quotientRe]
    rw [div_mul_cancel₀ _ hN]
  have hV : ((x * star y).im : ℚ) = V * N := by
    dsimp [V, N, quotientIm]
    rw [div_mul_cancel₀ _ hN]
  have hA : (((x / y).re : ℤ) : ℚ) = A := by
    change ((round (U + f / 2) : ℤ) : ℚ) = A
    rfl
  have hB : (((x / y).im : ℤ) : ℚ) = B := by
    change ((round V : ℤ) : ℚ) = B
    rfl
  have hrem :
      (x - y * (x / y)) * star y =
        x * star y - (norm y : MaximalOrder) * (x / y) := by
    have hprod : (y * (x / y)) * star y = (norm y : MaximalOrder) * (x / y) := by
      calc
        (y * (x / y)) * star y = (x / y) * (y * star y) := by ac_rfl
        _ = (x / y) * (norm y : MaximalOrder) := by rw [← norm_eq_mul_star]
        _ = (norm y : MaximalOrder) * (x / y) := by rw [mul_comm]
    rw [sub_mul, hprod]
  have hnorm_int :
      norm (x - y * (x / y)) * norm y =
        norm (x * star y - (norm y : MaximalOrder) * (x / y)) := by
    calc
      norm (x - y * (x / y)) * norm y =
          norm (x - y * (x / y)) * norm (star y) := by rw [norm_star]
      _ = norm ((x - y * (x / y)) * star y) := (norm_mul _ _).symm
      _ = norm (x * star y - (norm y : MaximalOrder) * (x / y)) :=
        congrArg norm hrem
  have hnorm_rat :
      (norm (x - y * (x / y)) : ℚ) * N =
        (norm (x * star y - (norm y : MaximalOrder) * (x / y)) : ℚ) := by
    dsimp [N]
    exact_mod_cast hnorm_int
  have htarget :
      (norm (x * star y - (norm y : MaximalOrder) * (x / y)) : ℚ) =
        (g ^ 2 + 7 * f ^ 2 / 4) * N ^ 2 := by
    have hscalar_re :
        ((norm y : MaximalOrder) * (x / y)).re = norm y * (x / y).re := by simp
    have hscalar_im :
        ((norm y : MaximalOrder) * (x / y)).im = norm y * (x / y).im := by simp
    rw [norm_def, re_sub, im_sub, hscalar_re, hscalar_im]
    push_cast
    rw [hU, hV, hA, hB]
    change
      (U * N - N * A) ^ 2 + (U * N - N * A) * (V * N - N * B) +
          2 * (V * N - N * B) ^ 2 =
        (g ^ 2 + 7 * f ^ 2 / 4) * N ^ 2
    dsimp [g, f]
    ring
  rw [div_eq_iff hN]
  apply mul_right_cancel₀ hN
  rw [hnorm_rat, htarget]
  ring

theorem norm_mod_lt (x : MaximalOrder) {y : MaximalOrder} (hy : y ≠ 0) :
    norm (x % y) < norm y := by
  have hny : (0 : ℚ) < norm y := by exact_mod_cast norm_pos.mpr hy
  have hratio : (norm (x % y) : ℚ) / norm y < 1 := by
    rw [mod_def, norm_remainder_div_norm x y hy]
    exact quotient_error_norm_lt_one x y
  have hcast : (norm (x % y) : ℚ) < norm y := (div_lt_one hny).mp hratio
  exact_mod_cast hcast

theorem natAbs_norm_mod_lt (x : MaximalOrder) {y : MaximalOrder} (hy : y ≠ 0) :
    (norm (x % y)).natAbs < (norm y).natAbs := by
  apply Int.ofNat_lt.mp
  rw [Int.natAbs_of_nonneg (norm_nonneg (x % y)),
    Int.natAbs_of_nonneg (norm_nonneg y)]
  exact norm_mod_lt x hy

theorem norm_le_norm_mul_left (x : MaximalOrder) {y : MaximalOrder} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [norm_mul, Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.mp (by
    rw [Int.natAbs_of_nonneg (norm_nonneg y)]
    exact Int.add_one_le_of_lt (norm_pos.mpr hy)))

instance instEuclideanDomain : EuclideanDomain MaximalOrder :=
  { instCommRing, instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro x
      ext <;> simp [div_def, quotientRe, quotientIm, norm]
    quotient_mul_add_remainder_eq := fun x y => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun x _ hy => not_lt_of_ge (norm_le_norm_mul_left x hy) }

end MaximalOrder

end Fermat.Quadratic.NegSeven
