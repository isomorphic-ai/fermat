import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.Voronoi

/-!
# Kummer's congruence modulo a prime

This file discharges the `KummerCongruenceModPrime` interface.  The proof is
the classical Voronoi argument, following the machine-checked Isabelle AFP
development by Manuel Eberl:

* apply Voronoi at depth `max (vₚ(k)) (vₚ(k')) + 1`;
* divide out the possibly non-unit indices `k` and `k'`;
* compare the remaining integer quotient sums term by term modulo `p`;
* use a generator of `(ZMod p)ˣ` to cancel `a^k - 1`.

The assumption `5 ≤ p` is explicit.  It is the range in which the uniform
Faulhaber remainder estimate proved in `Voronoi` applies, and it is exactly
the range used by the Fermat applications in this repository.
-/

namespace Fermat.Irregular

open Finset

namespace KummerTheorem

open Voronoi

/-! ## Valuation cancellation and integrality -/

/-- A nonzero rational factor of valuation zero can be cancelled from a
zero-aware valuation lower bound. -/
theorem HasPadicValAtLeast.of_mul_left_of_val_eq_zero
    {p : ℕ} [Fact p.Prime] {e : ℤ} {c x : ℚ}
    (hc : c ≠ 0) (hcval : padicValRat p c = 0)
    (hcx : HasPadicValAtLeast p e (c * x)) :
    HasPadicValAtLeast p e x := by
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  rcases hcx with hzero | hval
  · exact (hc (mul_eq_zero.mp hzero |>.resolve_right hx)).elim
  · rw [padicValRat.mul hc hx, hcval, zero_add] at hval
    exact hval

/-- The zero-aware integral valuation predicate implies the repository's
`IsPIntegral` interface, including at zero. -/
theorem isPIntegral_of_hasPadicValAtLeast_zero {p : ℕ} {x : ℚ}
    (hx : HasPadicValAtLeast p 0 x) : IsPIntegral p x := by
  rcases hx with rfl | hx
  · simp [IsPIntegral]
  · exact hx

/-- A congruence of integer casts modulo `p`, viewed as a depth-one rational
valuation bound. -/
theorem intCast_sub_hasPadicValAtLeast_one
    {p : ℕ} [Fact p.Prime] {A B : ℤ}
    (h : (A : ZMod p) = (B : ZMod p)) :
    HasPadicValAtLeast p 1 ((A - B : ℤ) : ℚ) := by
  have h' : (A : ZMod (p ^ 1)) = (B : ZMod (p ^ 1)) := by
    rw [pow_one]
    exact h
  exact Voronoi.intCast_sub_hasPadicValAtLeast_of_zmod_eq h'

/-! ## The quotient-sum comparison -/

/-- The integer quotient sum occurring in normalized Voronoi depends modulo
`p` only on the exponent modulo `p - 1` (for positive exponents).

Terms whose index is divisible by `p` vanish.  On all remaining terms,
Fermat's theorem in `(ZMod p)ˣ` transports the exponent. -/
theorem quotientPowerSum_zmod_eq_of_modEq
    {p t a k k' : ℕ} [Fact p.Prime]
    (hk : 1 < k) (hk' : 1 < k') (hkk' : k ≡ k' [MOD p - 1]) :
    (quotientPowerSum p t a k : ZMod p) =
      (quotientPowerSum p t a k' : ZMod p) := by
  have hexp : k - 1 ≡ k' - 1 [MOD p - 1] :=
    hkk'.sub_right (by omega) (by omega)
  simp only [quotientPowerSum, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, Int.cast_pow]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hpm : p ∣ a * m
  · have hzero : ((a * m : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (a * m) p).2 hpm
    simp only [hzero, zero_pow (by omega : k - 1 ≠ 0),
      zero_pow (by omega : k' - 1 ≠ 0), mul_zero]
  · have hnonzero : ((a * m : ℕ) : ZMod p) ≠ 0 :=
      mt (ZMod.natCast_eq_zero_iff (a * m) p).1 hpm
    rw [Voronoi.zmod_pow_eq_pow_of_modEq hexp hnonzero]

/-- Rational valuation form of `quotientPowerSum_zmod_eq_of_modEq`. -/
theorem quotientPowerSum_sub_hasPadicValAtLeast_one
    {p t a k k' : ℕ} [Fact p.Prime]
    (hk : 1 < k) (hk' : 1 < k') (hkk' : k ≡ k' [MOD p - 1]) :
    HasPadicValAtLeast p 1
      ((quotientPowerSum p t a k : ℚ) -
        (quotientPowerSum p t a k' : ℚ)) := by
  have hmod := quotientPowerSum_zmod_eq_of_modEq (t := t) (a := a)
    hk hk' hkk'
  have hval := intCast_sub_hasPadicValAtLeast_one hmod
  simpa only [Int.cast_sub] using hval

/-! ## Kummer with an explicit cancelling residue -/

/-- Kummer's congruence from an explicit residue `a` for which `a^k - 1`
is nonzero modulo `p`.

This formulation separates the entire Voronoi and valuation argument from
the final existence of a primitive residue.  It is useful both as a reusable
lemma and as an exact record of what the cancellation step needs. -/
theorem kummerCongruenceModPrime_of_witness
    {p k k' a : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hk : 0 < k) (hk' : 0 < k')
    (hkeven : Even k) (hk'even : Even k')
    (hkk' : k ≡ k' [MOD p - 1]) (ha : a.Coprime p)
    (haPow : (a : ZMod p) ^ k ≠ 1) :
    KummerCongruenceModPrime p k k' := by
  have hk2 : 1 < k := by
    obtain ⟨r, hr⟩ := hkeven
    omega
  have hk'2 : 1 < k' := by
    obtain ⟨r, hr⟩ := hk'even
    omega
  let s : ℕ := max (padicValNat p k) (padicValNat p k')
  let C : ℕ → ℚ := fun j ↦ (a : ℚ) ^ j - 1
  let X : ℕ → ℚ := fun j ↦ bernoulli j / (j : ℚ)
  let T : ℕ → ℚ := fun j ↦ (quotientPowerSum p (s + 1) a j : ℚ)
  have hks : padicValNat p k ≤ s := by simp [s]
  have hk's : padicValNat p k' ≤ s := by simp [s]
  have herr : HasPadicValAtLeast p 1 (C k * X k - T k) := by
    simpa only [C, X, T] using
      normalized_voronoi_hasPadicValAtLeast_one hp5 ha hk hkeven hks
  have herr' : HasPadicValAtLeast p 1 (C k' * X k' - T k') := by
    simpa only [C, X, T] using
      normalized_voronoi_hasPadicValAtLeast_one hp5 ha hk' hk'even hk's

  have haNotDvd : ¬p ∣ a := by
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp ha.symm)
  have haNonzero : (a : ZMod p) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff a p).mp haNotDvd
  have hpow : (a : ZMod p) ^ k = (a : ZMod p) ^ k' :=
    Voronoi.zmod_pow_eq_pow_of_modEq hkk' haNonzero

  let c : ℤ := (a : ℤ) ^ k - 1
  have hcMod : (c : ZMod p) ≠ 0 := by
    intro hzero
    apply haPow
    apply sub_eq_zero.mp
    simpa only [c, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] using hzero
  have hcNotDvd : ¬(p : ℤ) ∣ c := by
    intro hdvd
    exact hcMod ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).2 hdvd)
  have hcInt : c ≠ 0 := by
    intro hzero
    apply hcNotDvd
    rw [hzero]
    exact dvd_zero _
  have hcCast : (c : ℚ) = C k := by
    simp only [c, C, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one]
  have hCne : C k ≠ 0 := by
    rw [← hcCast]
    exact Int.cast_ne_zero.mpr hcInt
  have hCval : padicValRat p (C k) = 0 := by
    rw [← hcCast, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hcNotDvd]
    simp

  have hTint (j : ℕ) : HasPadicValAtLeast p 0 (T j) := by
    have h := HasPadicValAtLeast.intCast (p := p)
      (quotientPowerSum p (s + 1) a j)
    simpa only [T] using h
  have hCX : HasPadicValAtLeast p 0 (C k * X k) := by
    have h := (herr.mono (by omega)).add (hTint k)
    convert h using 1
    all_goals ring
  have hX : HasPadicValAtLeast p 0 (X k) :=
    HasPadicValAtLeast.of_mul_left_of_val_eq_zero hCne hCval hCX

  have hCdiff : HasPadicValAtLeast p 1 (C k - C k') := by
    have hmod :
        (((a : ℤ) ^ k - 1 : ℤ) : ZMod p) =
          (((a : ℤ) ^ k' - 1 : ℤ) : ZMod p) := by
      push_cast
      exact congrArg (fun z : ZMod p ↦ z - 1) hpow
    have hval := intCast_sub_hasPadicValAtLeast_one hmod
    simpa only [C, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] using hval
  have hC'X' : HasPadicValAtLeast p 0 (C k' * X k') := by
    have h := (herr'.mono (by omega)).add (hTint k')
    convert h using 1
    all_goals ring
  have haPow' : (a : ZMod p) ^ k' ≠ 1 := by
    rw [← hpow]
    exact haPow
  let c' : ℤ := (a : ℤ) ^ k' - 1
  have hc'Mod : (c' : ZMod p) ≠ 0 := by
    intro hzero
    apply haPow'
    apply sub_eq_zero.mp
    simpa only [c', Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] using hzero
  have hc'NotDvd : ¬(p : ℤ) ∣ c' := by
    intro hdvd
    exact hc'Mod ((ZMod.intCast_zmod_eq_zero_iff_dvd c' p).2 hdvd)
  have hc'Int : c' ≠ 0 := by
    intro hzero
    apply hc'NotDvd
    rw [hzero]
    exact dvd_zero _
  have hc'Cast : (c' : ℚ) = C k' := by
    simp only [c', C, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one]
  have hC'ne : C k' ≠ 0 := by
    rw [← hc'Cast]
    exact Int.cast_ne_zero.mpr hc'Int
  have hC'val : padicValRat p (C k') = 0 := by
    rw [← hc'Cast, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hc'NotDvd]
    simp
  have hX' : HasPadicValAtLeast p 0 (X k') :=
    HasPadicValAtLeast.of_mul_left_of_val_eq_zero hC'ne hC'val hC'X'

  have hTdiff : HasPadicValAtLeast p 1 (T k - T k') := by
    simpa only [T] using
      quotientPowerSum_sub_hasPadicValAtLeast_one (t := s + 1) (a := a)
        hk2 hk'2 hkk'
  have hCdiffX' : HasPadicValAtLeast p 1 ((C k - C k') * X k') := by
    simpa using hCdiff.mul hX'
  have hcombined := (herr.sub herr').sub hCdiffX' |>.add hTdiff
  have hCtimes : HasPadicValAtLeast p 1 (C k * (X k - X k')) := by
    convert hcombined using 1
    all_goals ring
  have hdiff : HasPadicValAtLeast p 1 (X k - X k') :=
    HasPadicValAtLeast.of_mul_left_of_val_eq_zero hCne hCval hCtimes

  refine ⟨isPIntegral_of_hasPadicValAtLeast_zero hX,
    isPIntegral_of_hasPadicValAtLeast_zero hX', ?_⟩
  simpa only [PadicValAtLeast, X] using hdiff

/-! ## Existence of the cancelling residue -/

/-- Kummer's congruence modulo a prime at positive even indices.

The nondivisibility hypothesis ensures that a generator `a` of
`(ZMod p)ˣ` satisfies `a^k ≠ 1`, which is precisely the witness required by
`kummerCongruenceModPrime_of_witness`. -/
theorem kummerCongruenceModPrime
    {p k k' : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hk : 0 < k) (hk' : 0 < k')
    (hkeven : Even k) (hk'even : Even k')
    (hkk' : k ≡ k' [MOD p - 1]) (hnot : ¬(p - 1) ∣ k) :
    KummerCongruenceModPrime p k k' := by
  letI : IsCyclic (ZMod p)ˣ :=
    ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let a : ℕ := (g : ZMod p).val
  have ha : a.Coprime p := by
    simpa only [a] using ZMod.val_coe_unit_coprime g
  have haCast : (a : ZMod p) = (g : ZMod p) := by
    simpa only [a] using ZMod.natCast_zmod_val (g : ZMod p)
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out : p.Prime)]
  have haPow : (a : ZMod p) ^ k ≠ 1 := by
    intro hpow
    have hunit : g ^ k = 1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, haCast] using hpow
    apply hnot
    rw [← horder]
    exact orderOf_dvd_iff_pow_eq_one.mpr hunit
  exact kummerCongruenceModPrime_of_witness hp5 hk hk' hkeven hk'even
    hkk' ha haPow

/-- The specialization used in the Fermat proof: `j` and `j*p` have the
same class modulo `p - 1`. -/
theorem kummerCongruenceModPrime_mul_prime
    {p j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hj : 0 < j) (hjeven : Even j)
    (hnot : ¬(p - 1) ∣ j) :
    KummerCongruenceModPrime p j (j * p) := by
  exact kummerCongruenceModPrime hp5 hj (Nat.mul_pos hj (Fact.out : p.Prime).pos)
    hjeven (hjeven.mul_right p) (kummerIndex_modEq j (by omega)).symm hnot

/-- Ready-to-use irregular-range specialization, with the nondivisibility
hypothesis derived from `2 ≤ j ≤ p - 3`. -/
theorem kummerCongruenceModPrime_irregularRange
    {p j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hj2 : 2 ≤ j) (hjp3 : j ≤ p - 3)
    (hjeven : Even j) :
    KummerCongruenceModPrime p j (j * p) := by
  exact kummerCongruenceModPrime_mul_prime hp5 (by omega) hjeven
    (kummerIndex_not_dvd_sub_one hp5 hj2 hjp3)

end KummerTheorem

end Fermat.Irregular
