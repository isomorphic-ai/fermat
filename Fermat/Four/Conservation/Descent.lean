/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen, Fabian Franz, Fable

# Fermat's coprime double descent, as a strict charge drain

The arithmetic in this file is reconstructed from Paul van Wamelen's
formalization in Mathlib, under Mathlib's Apache-2.0 license. This module
does not import Mathlib's fixed-exponent FLT(4) module or any theorem proved
from its endpoint.

The bounded import roles are:

* `Conservation.Spine` supplies the integer charge, stronger equation, and
  the n=2 balance-engine seam;
* `RingTheory.Coprime.Lemmas` supplies generic coprimality and square-factor
  extraction over `ℤ`.

The double descent invokes the coupling-free Pythagorean ledger twice:
first on `(x², y², z)`, then on the right triangle exposed inside that first
parametrization. Pairwise coprimality splits the resulting square product,
and the second ledger produces a new primitive stronger solution with
strictly smaller hypotenuse charge.
-/
import Fermat.Four.Conservation.Spine
import Mathlib.RingTheory.Coprime.Lemmas

namespace Fermat.Four.Conservation

private def Minimal (x y z : ℤ) : Prop :=
  StrongerSolution x y z ∧
    ∀ x₁ y₁ z₁ : ℤ,
      StrongerSolution x₁ y₁ z₁ → charge z ≤ charge z₁

private theorem solution_mul {x y z k : ℤ} (hk : k ≠ 0) :
    StrongerSolution x y z ↔
      StrongerSolution (k * x) (k * y) (k ^ 2 * z) := by
  delta StrongerSolution
  constructor
  · grind [mul_eq_zero]
  · intro h
    constructor
    · exact right_ne_zero_of_mul h.1
    constructor
    · exact right_ne_zero_of_mul h.2.1
    apply (mul_right_inj' (pow_ne_zero 4 hk)).mp
    linear_combination h.2.2

private theorem exists_minimal {x y z : ℤ}
    (h : StrongerSolution x y z) :
    ∃ x₀ y₀ z₀, Minimal x₀ y₀ z₀ := by
  classical
  let charges : Set ℕ :=
    { n | ∃ s : ℤ × ℤ × ℤ,
        StrongerSolution s.1 s.2.1 s.2.2 ∧
          n = charge s.2.2 }
  have charges_nonempty : charges.Nonempty := by
    use charge z
    rw [Set.mem_setOf_eq]
    exact ⟨⟨x, y, z⟩, h, rfl⟩
  let least : ℕ := Nat.find charges_nonempty
  have least_mem : least ∈ charges :=
    Nat.find_spec charges_nonempty
  rcases least_mem with ⟨S, hS, hcharge⟩
  refine ⟨S.1, S.2.1, S.2.2, hS, ?_⟩
  intro x₁ y₁ z₁ h₁
  rw [← hcharge]
  apply Nat.find_min'
  exact ⟨⟨x₁, y₁, z₁⟩, h₁, rfl⟩

private theorem coprime_of_minimal {x y z : ℤ}
    (h : Minimal x y z) :
    IsCoprime x y := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hxy
  obtain ⟨p, hp, hpx, hpy⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hxy
  obtain ⟨x₁, rfl⟩ := Int.natCast_dvd.mpr hpx
  obtain ⟨y₁, rfl⟩ := Int.natCast_dvd.mpr hpy
  have hpz : (p : ℤ) ^ 2 ∣ z := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2]
    apply Dvd.intro (x₁ ^ 4 + y₁ ^ 4)
    ring
  obtain ⟨z₁, rfl⟩ := hpz
  have hsmall : StrongerSolution x₁ y₁ z₁ :=
    (solution_mul
      (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr h.1
  apply Nat.le_lt_asymm (h.2 _ _ _ hsmall)
  change
    Int.natAbs z₁ <
      Int.natAbs ((p : ℤ) ^ 2 * z₁)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left,
    Int.natAbs_pow, Int.natAbs_natCast]
  · exact Nat.one_lt_pow two_ne_zero hp.one_lt
  · simpa [charge] using hsmall.charge_pos

private theorem exists_primitive {x y z : ℤ}
    (h : StrongerSolution x y z) :
    Nonempty PrimitiveSolution := by
  obtain ⟨x₀, y₀, z₀, hmin⟩ := exists_minimal h
  exact
    ⟨{
      x := x₀
      y := y₀
      z := z₀
      solution := hmin.1
      coprime := coprime_of_minimal hmin
    }⟩

namespace PrimitiveSolution

private def swap (S : PrimitiveSolution) : PrimitiveSolution where
  x := S.y
  y := S.x
  z := S.z
  solution :=
    ⟨S.solution.2.1, S.solution.1,
      by simpa only [add_comm] using S.solution.2.2⟩
  coprime := S.coprime.symm

@[simp]
private theorem swap_stateCharge (S : PrimitiveSolution) :
    S.swap.stateCharge = S.stateCharge :=
  rfl

private def negZ (S : PrimitiveSolution) : PrimitiveSolution where
  x := S.x
  y := S.y
  z := -S.z
  solution :=
    ⟨S.solution.1, S.solution.2.1,
      by simpa only [neg_sq] using S.solution.2.2⟩
  coprime := S.coprime

@[simp]
private theorem negZ_stateCharge (S : PrimitiveSolution) :
    S.negZ.stateCharge = S.stateCharge := by
  simp [PrimitiveSolution.stateCharge, charge, negZ]

private theorem exists_oriented (S : PrimitiveSolution) :
    ∃ T : PrimitiveSolution,
      T.x % 2 = 1 ∧ 0 < T.z ∧
        T.stateCharge = S.stateCharge := by
  have hgcd : Int.gcd S.x S.y = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp S.coprime
  obtain ⟨T, hodd, hcharge⟩ :
      ∃ T : PrimitiveSolution,
        T.x % 2 = 1 ∧ T.stateCharge = S.stateCharge := by
    rcases Int.emod_two_eq_zero_or_one S.x with hx_even | hx_odd
    · rcases Int.emod_two_eq_zero_or_one S.y with
        hy_even | hy_odd
      · exfalso
        have htwo : (2 : ℤ) ∣ (Int.gcd S.x S.y : ℤ) :=
          Int.dvd_coe_gcd
            (Int.dvd_of_emod_eq_zero hx_even)
            (Int.dvd_of_emod_eq_zero hy_even)
        rw [hgcd] at htwo
        norm_num at htwo
      · exact ⟨S.swap, hy_odd, S.swap_stateCharge⟩
    · exact ⟨S, hx_odd, rfl⟩
  rcases lt_trichotomy 0 T.z with hz | hz | hz
  · exact ⟨T, hodd, hz, hcharge⟩
  · exact False.elim
      ((Int.natAbs_pos.mp T.stateCharge_pos) hz.symm)
  · exact
      ⟨T.negZ, hodd, neg_pos.mpr hz,
        T.negZ_stateCharge.trans hcharge⟩

private theorem isCoprime_square_roots
    {j k r s : ℤ} (hrs : IsCoprime r s)
    (hj : r = j ^ 2 ∨ r = -(j ^ 2))
    (hk : s = k ^ 2 ∨ s = -(k ^ 2)) :
    IsCoprime j k := by
  rw [← IsCoprime.pow_iff
    (by decide : 0 < 2) (by decide : 0 < 2)]
  rcases hj with hj | hj <;>
    rcases hk with hk | hk <;>
      subst r <;> subst s
  · exact hrs
  · exact (IsCoprime.neg_right_iff _ _).mp hrs
  · exact (IsCoprime.neg_left_iff _ _).mp hrs
  · exact
      (IsCoprime.neg_left_iff _ _).mp
        ((IsCoprime.neg_right_iff _ _).mp hrs)

private theorem isCoprime_of_sq_sum
    {r s : ℤ} (h : IsCoprime s r) :
    IsCoprime (r ^ 2 + s ^ 2) r := by
  rw [sq, sq]
  exact (IsCoprime.mul_left h h).mul_add_left_left r

private theorem isCoprime_of_sq_sum'
    {r s : ℤ} (h : IsCoprime r s) :
    IsCoprime (r ^ 2 + s ^ 2) (r * s) := by
  apply IsCoprime.mul_right (isCoprime_of_sq_sum h.symm)
  rw [add_comm]
  exact isCoprime_of_sq_sum h

private theorem charged_descent_oriented
    (S : PrimitiveSolution)
    (hx_odd : S.x % 2 = 1) (hz_pos : 0 < S.z) :
    ∃ next : PrimitiveSolution,
      next.stateCharge < S.stateCharge := by
  have hfirst :=
    pythagorean_balance_engine S.solution
  have hsq_coprime :
      Int.gcd (S.x ^ 2) (S.y ^ 2) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp S.coprime.pow
  have hx_sq_odd : S.x ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, hx_odd]
    decide
  obtain ⟨m, n, hfirst_x, hfirst_y, hfirst_z,
      hmn_coprime, -, hm_nonneg⟩ :=
    hfirst.coprime_classification'
      hsq_coprime hx_sq_odd hz_pos
  have hsecond : PythagoreanTriple S.x n m := by
    delta PythagoreanTriple
    linear_combination hfirst_x
  have hxn_coprime : Int.gcd S.x n = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply @IsCoprime.of_mul_left_left _ _ _ S.x
    rw [← sq, hfirst_x,
      (by ring : m ^ 2 - n ^ 2 = m ^ 2 + -n * n)]
    exact
      (Int.isCoprime_iff_gcd_eq_one.mpr hmn_coprime).pow_left
        |>.add_mul_right_left (-n)
  have hy_sq_ne_zero : S.y ^ 2 ≠ 0 :=
    pow_ne_zero _ S.solution.2.1
  have hm_pos : 0 < m := by
    apply lt_of_le_of_ne hm_nonneg
    rintro rfl
    lia
  obtain ⟨r, s, -, hsecond_y, hsecond_z,
      hrs_coprime, -, -⟩ :=
    hsecond.coprime_classification'
      hxn_coprime hx_odd hm_pos
  have hm_rs_coprime : Int.gcd m (r * s) = 1 := by
    rw [hsecond_z]
    exact
      Int.isCoprime_iff_gcd_eq_one.mp
        (isCoprime_of_sq_sum'
          (Int.isCoprime_iff_gcd_eq_one.mpr hrs_coprime))
  have hy_even : 2 ∣ S.y := by
    apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
    rw [hfirst_y, mul_assoc]
    exact dvd_mul_right 2 (m * n)
  obtain ⟨yhalf, hyhalf⟩ := hy_even
  have hyhalf_sq : yhalf ^ 2 = m * (r * s) := by
    apply (mul_right_inj' (by simp : (4 : ℤ) ≠ 0)).mp
    linear_combination
      (-S.y - 2 * yhalf) * hyhalf +
        hfirst_y + 2 * m * hsecond_y
  have hrs_ne_zero : r * s ≠ 0 := by grind
  have hyhalf_ne_zero : yhalf ≠ 0 := by grind
  obtain ⟨i, hi⟩ :=
    Int.sq_of_gcd_eq_one hm_rs_coprime hyhalf_sq.symm
  have hi_neg_impossible : ¬m = -i ^ 2 := by
    by_contra hi_neg
    have hi_nonpos : -i ^ 2 ≤ 0 :=
      neg_nonpos.mpr (sq_nonneg i)
    rw [← hi_neg] at hi_nonpos
    exact absurd hm_pos (not_lt.mpr hi_nonpos)
  replace hi : m = i ^ 2 :=
    Or.resolve_right hi hi_neg_impossible
  rw [mul_comm] at hyhalf_sq
  rw [Int.gcd_comm] at hm_rs_coprime
  obtain ⟨d, hd⟩ :=
    Int.sq_of_gcd_eq_one hm_rs_coprime hyhalf_sq.symm
  have hd_neg_impossible : ¬r * s = -d ^ 2 := by
    by_contra hd_neg
    rw [hd_neg] at hyhalf_sq
    have hyhalf_sq_nonpos : yhalf ^ 2 ≤ 0 := by
      rw [hyhalf_sq,
        (by ring : -d ^ 2 * m = -(d ^ 2 * m))]
      exact
        neg_nonpos.mpr
          ((mul_nonneg_iff_of_pos_right hm_pos).mpr
            (sq_nonneg d))
    have hyhalf_sq_nonneg : 0 ≤ yhalf ^ 2 :=
      sq_nonneg yhalf
    exact
      absurd
        (lt_of_le_of_ne hyhalf_sq_nonneg
          (Ne.symm (pow_ne_zero _ hyhalf_ne_zero)))
        (not_lt.mpr hyhalf_sq_nonpos)
  replace hd : r * s = d ^ 2 :=
    Or.resolve_right hd hd_neg_impossible
  obtain ⟨j, hj⟩ :=
    Int.sq_of_gcd_eq_one hrs_coprime hd
  have hj_ne_zero : j ≠ 0 := by grind
  rw [mul_comm] at hd
  rw [Int.gcd_comm] at hrs_coprime
  obtain ⟨k, hk⟩ :=
    Int.sq_of_gcd_eq_one hrs_coprime hd
  have hk_ne_zero : k ≠ 0 := by grind
  have hj_sq : r ^ 2 = j ^ 4 := by grind
  have hk_sq : s ^ 2 = k ^ 4 := by grind
  have hnew_equation : i ^ 2 = j ^ 4 + k ^ 4 := by
    grind
  have hn_ne_zero : n ≠ 0 := by grind
  have hcharge_lt : charge i < charge S.z := by
    unfold charge
    apply Int.ofNat_lt.mp
    rw [← Int.eq_natAbs_of_nonneg (le_of_lt hz_pos)]
    apply lt_of_le_of_lt (Int.natAbs_le_self_sq i)
    rw [← hi, hfirst_z]
    apply lt_of_le_of_lt (Int.le_self_sq m)
    exact
      lt_add_of_pos_right (m ^ 2)
        (sq_pos_of_ne_zero hn_ne_zero)
  have hjk_coprime : IsCoprime j k := by
    apply isCoprime_square_roots
      (Int.isCoprime_iff_gcd_eq_one.mpr hrs_coprime).symm
      hj hk
  exact
    ⟨{
      x := j
      y := k
      z := i
      solution :=
        ⟨hj_ne_zero, hk_ne_zero, hnew_equation.symm⟩
      coprime := hjk_coprime
    }, hcharge_lt⟩

/-- **The charged double-descent step.** Every primitive nontrivial solution
of `x⁴ + y⁴ = z²` produces another primitive solution with strictly smaller
charge `|z|`.

The construction is the requested composition of modes: the
coupling-free n=2 balance parametrization is applied twice, splitting the
right-triangle ledger until a smaller square hypotenuse is exposed; that
closed balance transformation powers the n=4 drain. -/
theorem charged_descent (S : PrimitiveSolution) :
    ∃ next : PrimitiveSolution,
      next.stateCharge < S.stateCharge := by
  obtain ⟨oriented, hx_odd, hz_pos, hcharge⟩ :=
    S.exists_oriented
  obtain ⟨next, hlt⟩ :=
    oriented.charged_descent_oriented hx_odd hz_pos
  exact ⟨next, hcharge ▸ hlt⟩

end PrimitiveSolution

/-- Fermat's stronger exponent-four equation has no nontrivial integer
solution. The contradiction is obtained only by iterating
`PrimitiveSolution.charged_descent` into the shared conservation floor. -/
theorem not_stronger_solution_conservation
    {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ 4 + y ^ 4 ≠ z ^ 2 := by
  intro heq
  obtain ⟨initial⟩ :=
    exists_primitive
      (show StrongerSolution x y z from ⟨hx, hy, heq⟩)
  exact
    Fermat.Conservation.impossible_of_strict_charge_drain
      initial
      PrimitiveSolution.stateCharge
      PrimitiveSolution.stateCharge_pos
      PrimitiveSolution.charged_descent

end Fermat.Four.Conservation
