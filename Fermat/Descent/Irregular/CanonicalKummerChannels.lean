import Fermat.Descent.Irregular.AuxiliaryResidueChannels
import Fermat.Descent.Irregular.CyclotomicCharactersPrime

/-!
# Basis-free canonical Kummer channels

Every row of Kummer's canonical Vandermonde matrix is the character channel
of an even power character on `(ZMod p)ˣ / {±1}`. This removes all choices of
cyclic generator, auxiliary prime, embedding order, and residue-log root from
the intrinsic side of an auxiliary-prime factorization.
-/

open scoped BigOperators Matrix

namespace Fermat.Irregular.AuxiliaryResidueChannels

noncomputable section

open Fermat.Irregular.CyclotomicCharactersPrime
open KummerCriterion.CyclotomicUnits

variable {p : ℕ} [Fact p.Prime]

local instance : Fintype
    (Fermat.Irregular.CyclotomicCharactersPrime.RealResidueGroup p) :=
  Fintype.ofFinite _

/-- The even power character attached to Kummer row `j`.

The exponent is `2 * (j + 1)`, so the power map kills `-1` and hence
descends canonically to the real residue group. -/
def evenPowerCharacter (hp_three : 3 ≤ p)
    (j : Fin (kummerLogRank p)) : RealResidueGroup p →* (ZMod p)ˣ := by
  letI : Fact (2 < p) := ⟨by omega⟩
  exact QuotientGroup.lift (signSubgroup p)
    (powMonoidHom (2 * kummerLogRowIndex (p := p) j)) (by
      intro u hu
      rw [MonoidHom.mem_ker]
      rcases (signSubgroup_mem_iff u).mp hu with rfl | rfl
      · simp
      · change (-1 : (ZMod p)ˣ) ^
          (2 * kummerLogRowIndex (p := p) j) = 1
        rw [pow_mul]
        simp)

/-- The unit represented by Kummer column `a`. -/
def canonicalColumnUnit (hp_three : 3 ≤ p)
    (a : Fin (kummerLogRank p)) : (ZMod p)ˣ :=
  Units.mk0 (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
    (zmod_natCast_ne_zero_of_pos_lt
      (by
        have htwo := kummerLogColumnIndex_two_le (p := p) hp_three a
        omega)
      (kummerLogColumnIndex_lt_p (p := p) hp_three a))

/-- The basis-free real-residue node represented by Kummer column `a`. -/
def canonicalColumnNode (hp_three : 3 ≤ p)
    (a : Fin (kummerLogRank p)) : RealResidueGroup p :=
  QuotientGroup.mk (canonicalColumnUnit (p := p) hp_three a)

@[simp]
theorem evenPowerCharacter_canonicalColumnNode
    (hp_three : 3 ≤ p) (j a : Fin (kummerLogRank p)) :
    ((evenPowerCharacter (p := p) hp_three j
        (canonicalColumnNode (p := p) hp_three a) : (ZMod p)ˣ) : ZMod p) =
      teichmullerEvenNode (p := p) hp_three a ^
        kummerLogRowIndex (p := p) j := by
  rw [canonicalColumnNode, evenPowerCharacter, QuotientGroup.lift_mk]
  simp only [powMonoidHom_apply, canonicalColumnUnit]
  change
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
        (2 * kummerLogRowIndex (p := p) j) = _
  rw [pow_mul]
  rfl

/-- Kummer's canonical Vandermonde row is exactly the character channel of
the corresponding even power character on canonical real-residue nodes. -/
theorem characterChannel_evenPowerCharacter_eq_canonicalKummerChannel
    (hp_three : 3 ≤ p) (j : Fin (kummerLogRank p))
    (e : Fin (kummerLogRank p) → ZMod p) :
    characterChannel (evenPowerCharacter (p := p) hp_three j)
        (canonicalColumnNode (p := p) hp_three) e =
      canonicalKummerChannel p hp_three j e := by
  classical
  simp only [characterChannel, canonicalKummerChannel, Matrix.mulVec,
    dotProduct, vandermondeTeichmullerEvenSubOneMatrix,
    evenPowerCharacter_canonicalColumnNode, kummerLogRowIndex]

/-- Basis-free universal channel factorization: projecting any complete
finite-group orbit of residue differences against the even character for row
`j` produces a phase-dependent scalar times Kummer's intrinsic row `j`. -/
theorem orbitDetector_evenPowerCharacter_eq_scalar_mul_canonicalKummerChannel
    [Fact (2 < p)] (hp_three : 3 ≤ p) (j : Fin (kummerLogRank p))
    (phase : Fermat.Irregular.CyclotomicCharactersPrime.RealResidueGroup p →
      ZMod p)
    (e : Fin (kummerLogRank p) → ZMod p) :
    orbitDetector (evenPowerCharacter (p := p) hp_three j) phase
        (canonicalColumnNode (p := p) hp_three) e =
      orbitScalar (evenPowerCharacter (p := p) hp_three j) phase *
        canonicalKummerChannel p hp_three j e := by
  rw [orbitDetector_eq_scalar_mul_characterChannel,
    characterChannel_evenPowerCharacter_eq_canonicalKummerChannel]

end

end Fermat.Irregular.AuxiliaryResidueChannels
