import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Normalized circular units at an arbitrary odd prime

The original exponent-`37` development constructed its seventeen circular
units directly.  The same construction is needed at every odd prime in the
seven-fold campaign, so this file separates the prime-independent layer:

* `normalizedCircularUnit` realizes
  `ζ^e * (1 - ζ^a) / (1 - ζ)` as a unit of the ring of integers;
* the congruence `2e + a = 1 (mod p)` proves that this unit is real;
* `circularUnitFamily` chooses the canonical normalization for
  `2 ≤ a ≤ (p - 1) / 2`; and
* a prime cyclotomic field has unit rank `(p - 3) / 2`.

This is only the unit-family and index-certificate substrate.  The
Sinnott--Kummer formula identifying the odd part of the circular-unit index
with the real class number is a separate theorem and is not asserted here.
-/

open scoped NumberField

namespace Fermat.Irregular.CircularUnitFamily

noncomputable section

open NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K]

/-- The normalized cyclotomic unit
`ζ^e * (1 - ζ^a) / (1 - ζ)`, represented integrally by its geometric sum. -/
def normalizedCircularUnit {p a : ℕ} [NeZero p] {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (hp : 2 ≤ p) (ha : a.Coprime p)
    (e : ℕ) : (𝓞 K)ˣ := by
  let rootUnit : (𝓞 K)ˣ :=
    (hzeta.toInteger_isPrimitiveRoot.isUnit (by omega)).unit
  let geomUnit : (𝓞 K)ˣ :=
    (hzeta.toInteger_isPrimitiveRoot.geom_sum_isUnit hp ha).unit
  exact rootUnit ^ e * geomUnit

theorem normalizedCircularUnit_val {p a : ℕ} [NeZero p] {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (hp : 2 ≤ p) (ha : a.Coprime p)
    (e : ℕ) :
    (normalizedCircularUnit hzeta hp ha e : 𝓞 K) =
      hzeta.toInteger ^ e *
        ∑ j ∈ Finset.range a, hzeta.toInteger ^ j := by
  simp [normalizedCircularUnit]

/-- The ambient-field value of a normalized circular unit. -/
theorem normalizedCircularUnit_coe {p a : ℕ} [NeZero p] {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (hp : 2 ≤ p) (ha : a.Coprime p)
    (e : ℕ) :
    ((normalizedCircularUnit hzeta hp ha e : 𝓞 K) : K) =
      zeta ^ e * (1 - zeta ^ a) / (1 - zeta) := by
  rw [normalizedCircularUnit_val]
  simp only [map_mul, map_pow, map_sum, ← RingOfIntegers.coe_eq_algebraMap]
  have hne : 1 - zeta ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hzeta.ne_one (by omega)))
  apply mul_left_cancel₀ (a := 1 - zeta) hne
  rw [mul_div_cancel₀ _ hne]
  calc
    (1 - zeta) *
        (zeta ^ e * ∑ j ∈ Finset.range a, zeta ^ j) =
        zeta ^ e * ((1 - zeta) * ∑ j ∈ Finset.range a, zeta ^ j) := by
      ring
    _ = zeta ^ e * (1 - zeta ^ a) := by
      rw [show (1 - zeta) * ∑ j ∈ Finset.range a, zeta ^ j =
          1 - zeta ^ a by
        calc
          (1 - zeta) * ∑ j ∈ Finset.range a, zeta ^ j =
              -((zeta - 1) * ∑ j ∈ Finset.range a, zeta ^ j) := by
            ring
          _ = -(zeta ^ a - 1) := by rw [mul_geom_sum]
          _ = 1 - zeta ^ a := by ring]

section ComplexConjugation

variable [NumberField K] [NumberField.IsCMField K] [Algebra.IsIntegral ℚ K]

/-- Complex conjugation sends any primitive root of order at least two to
its inverse. -/
theorem complexConj_primitiveRoot_inv {p : ℕ} [NeZero p] {zeta : K}
    (hp : 2 ≤ p) (hzeta : IsPrimitiveRoot zeta p) :
    NumberField.IsCMField.complexConj K zeta = zeta⁻¹ := by
  let rootUnit : (𝓞 K)ˣ :=
    (hzeta.toInteger_isPrimitiveRoot.isUnit (by omega)).unit
  have hpow : rootUnit ^ p = 1 := by
    apply Units.ext
    apply RingOfIntegers.ext
    simpa [rootUnit] using hzeta.pow_eq_one
  have ht : rootUnit ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨p, by omega, hpow⟩
  have hc := NumberField.IsCMField.unitsComplexConj_torsion K ⟨rootUnit, ht⟩
  have hc' :
      NumberField.IsCMField.unitsComplexConj K rootUnit = rootUnit⁻¹ := by
    simpa using hc
  have hv := congrArg Units.val hc'
  simpa [rootUnit, NumberField.IsCMField.unitsComplexConj,
    NumberField.IsCMField.ringOfIntegersComplexConj,
    NumberField.RingOfIntegers.ext_iff] using
      congrArg ((↑) : 𝓞 K → K) hv

/-- The modular half-power normalization makes a circular unit real. -/
theorem normalizedCircularUnit_unitsComplexConj
    {p a e : ℕ} [NeZero p] {zeta : K}
    (hp : 2 ≤ p) (hzeta : IsPrimitiveRoot zeta p) (ha : a.Coprime p)
    (hnorm : 2 * e + a ≡ 1 [MOD p]) :
    NumberField.IsCMField.unitsComplexConj K
        (normalizedCircularUnit hzeta hp ha e) =
      normalizedCircularUnit hzeta hp ha e := by
  apply Units.ext
  apply RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K
      (((normalizedCircularUnit hzeta hp ha e : (𝓞 K)ˣ) : 𝓞 K) : K) =
    (((normalizedCircularUnit hzeta hp ha e : (𝓞 K)ˣ) : 𝓞 K) : K)
  rw [normalizedCircularUnit_coe]
  simp only [div_eq_mul_inv, map_mul, map_inv₀, map_pow, map_sub, map_one,
    complexConj_primitiveRoot_inv hp hzeta]
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (by omega)
  have hne1 : zeta - 1 ≠ 0 :=
    sub_ne_zero.mpr (hzeta.ne_one (by omega))
  have hne2 : 1 - zeta ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hzeta.ne_one (by omega)))
  have hpow : zeta ^ (2 * e + a) = zeta := by
    simpa using pow_eq_pow_of_modEq hnorm hzeta.pow_eq_one
  simp only [inv_pow]
  field_simp [hzeta0, hne1, hne2]
  rw [pow_add, pow_mul] at hpow
  simp only [mul_pow, pow_two] at hpow ⊢
  rw [hpow]
  ring

theorem normalizedCircularUnit_mem_realUnits
    {p a e : ℕ} [NeZero p] {zeta : K}
    (hp : 2 ≤ p) (hzeta : IsPrimitiveRoot zeta p) (ha : a.Coprime p)
    (hnorm : 2 * e + a ≡ 1 [MOD p]) :
    normalizedCircularUnit hzeta hp ha e ∈
      NumberField.IsCMField.realUnits K :=
  (NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mp
    (normalizedCircularUnit_unitsComplexConj hp hzeta ha hnorm)

end ComplexConjugation

/-- The canonical exponent representing `(1 - a) / 2` modulo the odd prime
`p`. -/
def canonicalNormalizationExponent {p : ℕ} [Fact p.Prime] (a : ℕ) : ℕ :=
  ((1 - (a : ZMod p)) / (2 : ZMod p)).val

theorem canonicalNormalizationExponent_modEq {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (a : ℕ) :
    2 * canonicalNormalizationExponent (p := p) a + a ≡ 1 [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    canonicalNormalizationExponent, ZMod.natCast_zmod_val]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2'
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hp2 hp2'
  field_simp
  ring

/-- The canonical family indexed by the nontrivial real cyclotomic columns
`a = 2, ..., (p - 1) / 2`. -/
def circularUnitFamily {p : ℕ} [Fact p.Prime] {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (hp2 : p ≠ 2)
    (i : Fin ((p - 3) / 2)) : (𝓞 K)ˣ := by
  let a := i.val + 2
  have ha0 : a ≠ 0 := by omega
  have halt : a < p := by
    dsimp [a]
    have hp3 : 3 ≤ p :=
      (Fact.out : p.Prime).two_le.lt_or_eq.resolve_right hp2.symm
    omega
  have ha : a.Coprime p :=
    (Nat.coprime_of_lt_prime ha0 halt (Fact.out : p.Prime)).symm
  exact normalizedCircularUnit hzeta ((Fact.out : p.Prime).two_le) ha
    (canonicalNormalizationExponent (p := p) a)

theorem circularUnitFamily_val {p : ℕ} [Fact p.Prime] {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (hp2 : p ≠ 2)
    (i : Fin ((p - 3) / 2)) :
    (circularUnitFamily hzeta hp2 i : 𝓞 K) =
      hzeta.toInteger ^
          canonicalNormalizationExponent (p := p) (i.val + 2) *
        ∑ j ∈ Finset.range (i.val + 2), hzeta.toInteger ^ j := by
  simp only [circularUnitFamily]
  rw [normalizedCircularUnit_val]

theorem circularUnitFamily_coe {p : ℕ} [Fact p.Prime] {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (hp2 : p ≠ 2)
    (i : Fin ((p - 3) / 2)) :
    ((circularUnitFamily hzeta hp2 i : 𝓞 K) : K) =
      zeta ^ canonicalNormalizationExponent (p := p) (i.val + 2) *
        (1 - zeta ^ (i.val + 2)) / (1 - zeta) := by
  simp only [circularUnitFamily]
  rw [normalizedCircularUnit_coe]

section CanonicalReality

variable [NumberField K] [NumberField.IsCMField K] [Algebra.IsIntegral ℚ K]

theorem circularUnitFamily_mem_realUnits
    {p : ℕ} [Fact p.Prime] {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (hp2 : p ≠ 2)
    (i : Fin ((p - 3) / 2)) :
    circularUnitFamily hzeta hp2 i ∈ NumberField.IsCMField.realUnits K := by
  simp only [circularUnitFamily]
  apply normalizedCircularUnit_mem_realUnits
  exact canonicalNormalizationExponent_modEq hp2 (i.val + 2)

end CanonicalReality

section CyclotomicPrime

variable [NumberField K]

/-- Every cyclotomic field of odd prime conductor is a CM field. -/
theorem cyclotomicPrime_isCMField {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [IsCyclotomicExtension {p} ℚ K] : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField K (S := ({p} : Set ℕ))
    ⟨p, Set.mem_singleton p, hp.two_le.lt_of_ne hp2.symm⟩

/-- The unit rank of a cyclotomic field of odd prime conductor. -/
theorem cyclotomicPrime_unitRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [IsCyclotomicExtension {p} ℚ K] :
    NumberField.Units.rank K = (p - 3) / 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := p)
      (hp.two_le.lt_of_ne hp2.symm),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (K := K) p,
    Nat.totient_prime hp]
  omega

end CyclotomicPrime

end


end Fermat.Irregular.CircularUnitFamily
