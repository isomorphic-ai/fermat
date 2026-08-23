import Fermat.Descent.Irregular.CircularUnitFamily
import KummerCriterion.CyclotomicUnits.NormalizedSubgroup

/-!
# Circular-unit generator bridge

This module identifies KummerCriterion's normalized real cyclotomic-unit
generators with the canonical circular-unit family used by finite
auxiliary-prime residue certificates. It is the only place where those two
normalization conventions need to meet.
-/

open scoped NumberField

namespace Fermat.Irregular.CircularUnitGeneratorBridge

noncomputable section

open NumberField
open Fermat.Irregular.CircularUnitFamily
open KummerCriterion

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The primitive root selected by the cyclotomic-extension typeclass. -/
abbrev canonicalZeta : K :=
  (((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K)

omit [NumberField.IsCMField K] in
theorem canonicalZeta_isPrimitive :
    IsPrimitiveRoot (canonicalZeta (p := p) (K := K)) p := by
  change IsPrimitiveRoot
    (((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) p
  exact IsCyclotomicExtension.zeta_spec p ℚ K

/-- The two libraries use the same normalization exponent. -/
theorem normalizedCyclotomicUnitExponent_eq_canonical (a : ℕ) :
    normalizedCyclotomicUnitExponent p a =
      canonicalNormalizationExponent (p := p) a := by
  simp [normalizedCyclotomicUnitExponent, canonicalNormalizationExponent,
    div_eq_mul_inv, mul_comm]

/-- Mapping the normalized `CPlus` generator to the full cyclotomic field
gives the canonical circular unit used by residue certificates. -/
theorem map_normalizedCPlusGenerator_eq_circularUnitFamily
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) :
    Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
        (normalizedCPlusGenerator (p := p) (K := K) hp_odd hp_three i) =
      circularUnitFamily
        (canonicalZeta_isPrimitive (p := p) (K := K)) hp_odd i := by
  apply Units.ext
  change algebraMap (𝓞 K⁺) (𝓞 K)
      (normalizedCPlusGenerator
        (p := p) (K := K) hp_odd hp_three i : 𝓞 K⁺) =
    (circularUnitFamily
      (canonicalZeta_isPrimitive (p := p) (K := K)) hp_odd i : 𝓞 K)
  unfold normalizedCPlusGenerator
  rw [algebraMap_normalizedCyclotomicUnitPlusUnit]
  rw [normalizedCyclotomicUnitKOfRange_val]
  rw [circularUnitFamily_val]
  rw [normalizedCyclotomicUnitExponent_eq_canonical]
  rfl

/-- Mapping the squared-family `CPlus` generator gives the square of the
canonical circular unit. This is the form used by `CPlusExponentProduct`.
-/
theorem map_CPlusGenerator_eq_circularUnitFamily_sq
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) :
    Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
        (CPlusGenerator (p := p) (K := K) hp_three i) =
      circularUnitFamily
          (canonicalZeta_isPrimitive (p := p) (K := K)) hp_odd i ^ 2 := by
  rw [← normalizedCPlusGenerator_sq_eq_CPlusGenerator
    (p := p) (K := K) hp_odd hp_three i]
  rw [map_pow, map_normalizedCPlusGenerator_eq_circularUnitFamily]

end

end Fermat.Irregular.CircularUnitGeneratorBridge
