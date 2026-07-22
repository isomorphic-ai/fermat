import Fermat.Irregular.BernoulliData

/-!
# The Kummer-congruence interface

This module isolates the rational congruence needed to reduce Vandiver's
Bernoulli conditions at regular indices.  `KummerCongruenceModPrime` is the
statement consumed by that reduction; it is **not yet a proof of Kummer's
congruence**.  Proving that interface from the index hypotheses requires the
Voronoi congruence (or equivalent p-adic Bernoulli machinery), which is not
present in Mathlib.

The theorem shape and proof boundary were cross-checked against Manuel
Eberl's machine-checked Isabelle AFP development
[`Kummer_Congruence`](https://www.isa-afp.org/entries/Kummer_Congruence.html),
which follows Henri Cohen, *Number Theory, Volume II*, Propositions 9.5.20
and 9.5.23.  That development obtains the congruence through Voronoi's
congruence.  The classical source is Kummer's 1851 paper in *Journal für die
reine und angewandte Mathematik* 41, especially page 371; the modern formula
is [DLMF 24.10.3](https://dlmf.nist.gov/24.10.E3).

The valuation convention `padicValRat p 0 = 0` means that divisibility must
record the zero case separately.  `PadicValAtLeast` does exactly this.
-/

namespace Fermat.Irregular

/-- A rational has p-adic valuation at least `e`, with zero treated as having
infinite valuation rather than Mathlib's computational default value `0`. -/
def PadicValAtLeast (p e : ℕ) (x : ℚ) : Prop :=
  x = 0 ∨ (e : ℤ) ≤ padicValRat p x

/-- The valuation formulation of integrality in the localization at `p`. -/
def IsPIntegral (p : ℕ) (x : ℚ) : Prop :=
  0 ≤ padicValRat p x

/-- Congruence of p-integral rationals modulo `p ^ e`. -/
def RationalModEq (p e : ℕ) (x y : ℚ) : Prop :=
  IsPIntegral p x ∧ IsPIntegral p y ∧ PadicValAtLeast p e (x - y)

/-- The exact modulo-`p` Bernoulli congruence used by the Vandiver reduction.

This is presently a consumer interface, not a theorem asserting that the
congruence always holds. -/
def KummerCongruenceModPrime (p k k' : ℕ) : Prop :=
  RationalModEq p 1
    (bernoulli k / (k : ℚ)) (bernoulli k' / (k' : ℚ))

namespace RationalModEq

variable {p e : ℕ} {x y : ℚ}

theorem refl (hx : IsPIntegral p x) : RationalModEq p e x x := by
  exact ⟨hx, hx, Or.inl (sub_self x)⟩

theorem symm (h : RationalModEq p e x y) : RationalModEq p e y x := by
  rcases h with ⟨hx, hy, hxy⟩
  refine ⟨hy, hx, ?_⟩
  rcases hxy with hxy | hxy
  · left
    simpa using congrArg Neg.neg hxy
  · right
    rw [show y - x = -(x - y) by ring, padicValRat.neg]
    exact hxy

/-- A congruence of positive depth cannot take a nonzero element of valuation
below that depth to zero. -/
theorem right_ne_zero_of_left_ne_zero_of_lt
    (h : RationalModEq p e x y) (hx : x ≠ 0)
    (hlt : padicValRat p x < (e : ℤ)) : y ≠ 0 := by
  intro hy
  subst y
  rcases h.2.2 with hdiff | hdiff
  · exact hx (sub_eq_zero.mp hdiff)
  · have hdiff' : (e : ℤ) ≤ padicValRat p x := by
      simpa only [sub_zero] using hdiff
    exact (not_le_of_gt hlt) hdiff'

variable [Fact p.Prime]

/-- Congruent nonzero rationals have the same valuation below the congruence
depth. -/
theorem padicValRat_eq_of_lt
    (h : RationalModEq p e x y) (hx : x ≠ 0)
    (hlt : padicValRat p x < (e : ℤ)) :
    padicValRat p y = padicValRat p x := by
  have hy := right_ne_zero_of_left_ne_zero_of_lt h hx hlt
  rcases h.2.2 with hxy | hxy
  · exact congrArg (padicValRat p) (sub_eq_zero.mp hxy).symm
  · by_cases hsub : x - y = 0
    · exact congrArg (padicValRat p) (sub_eq_zero.mp hsub).symm
    have hneg : -(x - y) ≠ 0 := neg_ne_zero.mpr hsub
    have hval : padicValRat p x < padicValRat p (-(x - y)) := by
      rw [padicValRat.neg]
      exact hlt.trans_le hxy
    have hsum : x + -(x - y) = y := by ring
    simpa [hsum] using
      padicValRat.add_eq_of_lt (p := p) (q := x) (r := -(x - y))
        (by rw [hsum]; exact hy) hx hneg hval

end RationalModEq

/-! ## The index specialization `j ↦ j * p` -/

/-- The two indices in the needed Kummer specialization are congruent modulo
`p - 1`. -/
theorem kummerIndex_modEq (j : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    j * p ≡ j [MOD p - 1] := by
  have hp_eq : p = (p - 1) + 1 := by omega
  have hbase : p ≡ 1 [MOD p - 1] := by
    rw [hp_eq]
    have h := Nat.ModEq.modulus_mul_add (m := p - 1) (a := 1) (b := 1)
    simp only [mul_one] at h
    exact h
  simpa using hbase.mul_left j

/-- An index in the classical irregular range is not divisible by `p - 1`. -/
theorem kummerIndex_not_dvd_sub_one {p j : ℕ}
    (hp : 5 ≤ p) (hj2 : 2 ≤ j) (hjp3 : j ≤ p - 3) :
    ¬(p - 1) ∣ j := by
  intro hdvd
  have hp1le : p - 1 ≤ j := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Multiplying the index by `p` does not change divisibility by `p - 1`. -/
theorem kummerIndex_mul_prime_not_dvd_sub_one (j : ℕ) {p : ℕ}
    (hp : 2 ≤ p) (hnot : ¬(p - 1) ∣ j) :
    ¬(p - 1) ∣ j * p := by
  intro hdvd
  apply hnot
  exact Nat.modEq_zero_iff_dvd.mp <|
    (kummerIndex_modEq j hp).symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)

/-! ## Valuation consequence -/

/-- The precise consequence needed for regular indices in Vandiver's
criterion: a unit value of `B_j / j`, transported by Kummer's congruence to
`B_{jp} / (jp)`, says that `B_{jp}` has exactly one factor of `p`.

The hypothesis `hcong` remains the undischarged Kummer-congruence theorem. -/
theorem bernoulli_mul_prime_padicValRat_eq_one {p j : ℕ} [Fact p.Prime]
    (hBj : bernoulli j ≠ 0) (hj : ¬p ∣ j)
    (hunit : padicValRat p (bernoulli j / (j : ℚ)) = 0)
    (hcong : KummerCongruenceModPrime p j (j * p)) :
    padicValRat p (bernoulli (j * p)) = 1 := by
  have hj0 : j ≠ 0 := by
    intro hjzero
    subst j
    exact hj (dvd_zero p)
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hleft0 : bernoulli j / (j : ℚ) ≠ 0 :=
    div_ne_zero hBj (Nat.cast_ne_zero.mpr hj0)
  have hquotient :
      padicValRat p (bernoulli (j * p) / ((j * p : ℕ) : ℚ)) = 0 := by
    rw [RationalModEq.padicValRat_eq_of_lt hcong hleft0 (by omega)]
    exact hunit
  have hjval : padicValRat p (j : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hj]
    simp
  have hjpval : padicValRat p ((j * p : ℕ) : ℚ) = 1 := by
    rw [Nat.cast_mul, padicValRat.mul (Nat.cast_ne_zero.mpr hj0)
      (Nat.cast_ne_zero.mpr hp0), hjval,
      padicValRat.self (Fact.out : Nat.Prime p).one_lt]
    simp
  have hright0 : bernoulli (j * p) / ((j * p : ℕ) : ℚ) ≠ 0 :=
    RationalModEq.right_ne_zero_of_left_ne_zero_of_lt hcong hleft0 (by omega)
  have hBernoulli0 : bernoulli (j * p) ≠ 0 := by
    exact fun hzero ↦ hright0 (by simp [hzero])
  rw [padicValRat.div hBernoulli0
    (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hj0 hp0)), hjpval] at hquotient
  omega

/-- The executable regular-index reduction used in Vandiver's criterion.

For an even index in `2, 4, ..., p - 3`, nondivisibility of the numerator of
`B_j` by `p`, together with the modulo-`p` Kummer congruence, excludes `p³`
from the numerator of `B_{jp}`.  Both denominator hypotheses are derived from
the public von Staudt--Clausen theorem through `BernoulliData`.

The only unproved mathematical bridge in this statement is `hcong`. -/
theorem regularIndex_bernoulli_mul_prime_numerator_not_dvd_cube
    {p j : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hj2 : 2 ≤ j) (hjp3 : j ≤ p - 3) (heven : Even j)
    (hBj : bernoulli j ≠ 0)
    (hregular : ¬(p : ℤ) ∣ (bernoulli j).num)
    (hcong : KummerCongruenceModPrime p j (j * p)) :
    ¬(p : ℤ) ^ 3 ∣ (bernoulli (j * p)).num := by
  have hsubOne : ¬(p - 1) ∣ j :=
    kummerIndex_not_dvd_sub_one hp hj2 hjp3
  have hj : ¬p ∣ j := by
    intro hpj
    have hple : p ≤ j := Nat.le_of_dvd (by omega) hpj
    omega
  have hden : BernoulliData.DenominatorPrimeTo p (bernoulli j) :=
    BernoulliData.bernoulli_denominatorPrimeTo heven hsubOne
  have hunit : padicValRat p (bernoulli j / (j : ℚ)) = 0 :=
    BernoulliData.padicValRat_div_nat_eq_zero hBj hden hregular hj
  have hval : padicValRat p (bernoulli (j * p)) = 1 :=
    bernoulli_mul_prime_padicValRat_eq_one hBj hj hunit hcong
  have hsubOneMul : ¬(p - 1) ∣ j * p :=
    kummerIndex_mul_prime_not_dvd_sub_one j (by omega) hsubOne
  have hevenMul : Even (j * p) := heven.mul_right p
  have hdenMul : BernoulliData.DenominatorPrimeTo p (bernoulli (j * p)) :=
    BernoulliData.bernoulli_denominatorPrimeTo hevenMul hsubOneMul
  have hBernoulliMul : bernoulli (j * p) ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hval
    omega
  exact BernoulliData.numerator_not_dvd_cube_of_padicValRat_eq_one
    hBernoulliMul hdenMul hval

end Fermat.Irregular
