/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Character-seating audit for the canonical 827 inputs

The literal first generated circular unit and the canonical conjugate-pair
source both have even raw arithmetic data.  A Tate-compatible pair for the
canonical Teichmuller character, however, seats characters `chi` and
`omega * chi⁻¹`, whose parities are opposite.  This file makes that mismatch
kernel-visible.

For the strict generated unit, every odd character projector is proved to
be zero.  For the conjugate-pair source, every odd character projector has
zero selected 827 localization.  Consequently no single complementary
seating makes both established detectors nonzero.  The latter statement is
deliberately about localization: the current exact sequence does not erase
the possible strict/global-unit class left after all 827 coordinates vanish.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalPrimalSelmerMode827
import Fermat.Exponents.FiftyNine.Conservation.CanonicalConjugatePairProjection827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.CanonicalCharacterSeatingAudit827

open Fermat.Conservation
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalPrimalSelmerMode827
open Fermat.FiftyNine.Conservation.ConjugatePairSource827
open Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The even mode complementary to the canonical odd irregular character. -/
noncomputable def canonicalModeFortyFourCharacter59 :
    InvolutiveBase.Character (PadicInt 59) GaloisIndex59 :=
  InvolutiveBase.reflectedCharacter
    canonicalTeichmullerCharacter59 irregularCharacter59

/-- Its residue-field orientation is exactly power mode 44. -/
theorem reducedCharacter59_canonicalModeFortyFourCharacter59 :
    reducedCharacter59 canonicalModeFortyFourCharacter59 =
      powerCharacter59 44 := by
  exact orientedPrimalMode827_canonical_irregular

/-- In particular, mode 44 is even at complex conjugation. -/
theorem canonicalModeFortyFourCharacter59_negOne_reduction :
    PadicInt.toZMod
        (canonicalModeFortyFourCharacter59 (-1) : PadicInt 59) = 1 := by
  have h := orientedPrimalMode827_canonical_irregular_even
  exact congrArg Units.val h

/-- The canonical Teichmuller orientation itself is odd. -/
theorem canonicalTeichmullerCharacter59_negOne_reduction :
    PadicInt.toZMod
        (canonicalTeichmullerCharacter59 (-1) : PadicInt 59) = -1 := by
  have h := canonicalTeichmullerCharacter59_reduction_apply (-1)
  exact congrArg Units.val h

/-! ## The strict generated unit -/

/-- Project the literal Mathlib strict-Selmer receipt of the generated unit
to an arbitrary character seat. -/
noncomputable def strictGeneratedCharacterProjection827
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) eta :=
  characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K) eta
    (canonicalFirstGeneratedStrictSelmer59 K)

/-- Centrality of the idempotent preserves the source's real (`-1`-fixed)
orientation for every character projector. -/
theorem cyclotomicNegOne_fixed_strictGeneratedCharacterProjection827
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    cyclotomicStrictSelmerRepresentation59 K (-1)
        (strictGeneratedCharacterProjection827 K eta).1 =
      (strictGeneratedCharacterProjection827 K eta).1 := by
  let rho := cyclotomicStrictSelmerRepresentation59 K
  let e := characterIdempotent eta
  let x := canonicalFirstGeneratedStrictSelmer59 K
  change rho (-1) (rho.asAlgebraHom e x) = rho.asAlgebraHom e x
  calc
    rho (-1) (rho.asAlgebraHom e x) =
        rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1))
          (rho.asAlgebraHom e x) := by
      rw [Representation.asAlgebraHom_of]
    _ = rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1) * e) x := by
      rw [map_mul]
      rfl
    _ = rho.asAlgebraHom
          (e * MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1)) x := by
      rw [mul_comm]
    _ = rho.asAlgebraHom e
          (rho.asAlgebraHom
            (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1)) x) := by
      rw [map_mul]
      rfl
    _ = rho.asAlgebraHom e (rho (-1) x) := by
      rw [Representation.asAlgebraHom_of]
    _ = rho.asAlgebraHom e x := by
      rw [cyclotomicNegOne_fixed_canonicalFirstGeneratedStrictSelmer59]

/-- Every odd character projector kills the real generated strict Selmer
class. -/
theorem strictGeneratedCharacterProjection827_eq_zero_of_odd
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (hodd : PadicInt.toZMod (eta (-1) : PadicInt 59) = -1) :
    strictGeneratedCharacterProjection827 K eta = 0 := by
  let x := strictGeneratedCharacterProjection827 K eta
  have heigen :
      cyclotomicStrictSelmerRepresentation59 K (-1) x.1 =
        (eta (-1) : PadicInt 59) • x.1 :=
    (mem_characterEigenspace_iff
      (cyclotomicStrictSelmerRepresentation59 K) eta x.1).mp
        x.property (-1)
  have hfixed :
      cyclotomicStrictSelmerRepresentation59 K (-1) x.1 = x.1 :=
    cyclotomicNegOne_fixed_strictGeneratedCharacterProjection827 K eta
  have hneg : (-1 : ZMod 59) • x.1 = x.1 := by
    rw [← hodd]
    change (eta (-1) : PadicInt 59) • x.1 = x.1
    exact heigen.symm.trans hfixed
  have hneg' : -x.1 = x.1 := by
    rw [← neg_one_smul (ZMod 59) x.1]
    exact hneg
  have hadd : x.1 + x.1 = 0 := by
    calc
      x.1 + x.1 = -x.1 + x.1 :=
        congrArg (fun y ↦ y + x.1) hneg'.symm
      _ = 0 := neg_add_cancel x.1
  have htwo : (2 : ZMod 59) • x.1 = 0 := by
    rw [show (2 : ZMod 59) = 1 + 1 by norm_num, add_smul, one_smul]
    exact hadd
  apply Subtype.ext
  exact (smul_eq_zero_iff_right
    (by decide : (2 : ZMod 59) ≠ 0)).mp htwo

/-- The old canonical `chi = 15` source is the odd specialization of the
generic vanishing theorem. -/
theorem strictGeneratedModeFifteenProjection827_eq_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    strictGeneratedCharacterProjection827 K irregularCharacter59 = 0 :=
  strictGeneratedCharacterProjection827_eq_zero_of_odd K
    irregularCharacter59 irregularCharacter59_negOne_reduction

/-- The generic mode-15 projection is definitionally the source constructed
in `CanonicalPrimalSelmerMode827`. -/
theorem strictGeneratedModeFifteenProjection827_eq_canonical
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    strictGeneratedCharacterProjection827 K irregularCharacter59 =
      canonicalPrimalSelmerMode827 K := by
  rfl

/-- The mode-44 projector is well-typed and is not parity-killed. -/
noncomputable def strictGeneratedModeFortyFourProjection827
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      canonicalModeFortyFourCharacter59 :=
  strictGeneratedCharacterProjection827 K canonicalModeFortyFourCharacter59

/-- The even mode-44 projection remains fixed by complex conjugation, as
required by its character seat. -/
theorem cyclotomicNegOne_fixed_strictGeneratedModeFortyFourProjection827
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] :
    cyclotomicStrictSelmerRepresentation59 K (-1)
        (strictGeneratedModeFortyFourProjection827 K).1 =
      (strictGeneratedModeFortyFourProjection827 K).1 :=
  cyclotomicNegOne_fixed_strictGeneratedCharacterProjection827 K
    canonicalModeFortyFourCharacter59

/-- The existing residue certificate does detect the raw generated unit in
mode 44.  No equality with the Selmer projector is inserted here. -/
theorem rawGeneratedModeFortyFourFourier_ne_zero :
    fourierCoefficient
        (canonicalFirstGeneratedFullOrbitReading827 K)
        (reducedCharacter59 canonicalModeFortyFourCharacter59) ≠ 0 := by
  rw [reducedCharacter59_canonicalModeFortyFourCharacter59]
  exact canonicalFirstGenerated_powerFortyFour_fourier_ne_zero K

/-! ## The conjugate-pair source -/

/-- Project the canonical raw conjugate-pair source to any supported
character seat. -/
noncomputable def conjugatePairCharacterProjection827
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (place : Place827 K) :
    SelmerChiAt (cyclotomicQRelaxedSelmerRepresentation827 K) eta :=
  characterProjectorAt (cyclotomicQRelaxedSelmerRepresentation827 K) eta
    (conjugatePairSource827 place)

/-- The selected coordinate of an arbitrary character projection is the
normalized sum of the two conjugate support coefficients. -/
theorem supportValuationAt_conjugatePairCharacterProjection827_eq
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (place : Place827 K) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) place
        (conjugatePairCharacterProjection827 K eta place).1 =
      PadicInt.toZMod
          (⅟(Fintype.card GaloisIndex59 : PadicInt 59)) *
        (-PadicInt.toZMod (↑((eta 1)⁻¹) : PadicInt 59) +
          -PadicInt.toZMod (↑((eta (-1))⁻¹) : PadicInt 59)) := by
  change supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (S := placesOver827 K) place
      ((SelmerEigenspace.characterProjectorAt
        (cyclotomicQRelaxedSelmerRepresentation827 K) eta
        (conjugatePairSource827 place)).1) = _
  rw [supportValuationAt_characterProjectorAt_eq_sum]
  rw [conjugatePairSource827_weighted_sum eta place
    (cmConjugatePlace827_val_eq_cyclotomic_negOne place)]

/-- An odd projector has zero selected localization on the symmetric
conjugate-pair source. -/
theorem supportValuationAt_conjugatePairCharacterProjection827_eq_zero_of_odd
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (place : Place827 K)
    (hodd : PadicInt.toZMod (eta (-1) : PadicInt 59) = -1) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) place
        (conjugatePairCharacterProjection827 K eta place).1 = 0 := by
  rw [supportValuationAt_conjugatePairCharacterProjection827_eq]
  have hone :
      PadicInt.toZMod (↑((eta 1)⁻¹) : PadicInt 59) = 1 := by simp
  have hprod := congrArg PadicInt.toZMod (eta (-1)).inv_val
  simp only [map_mul, map_one] at hprod
  have hminus :
      PadicInt.toZMod (↑((eta (-1))⁻¹) : PadicInt 59) = -1 := by
    rw [hodd] at hprod
    linear_combination -hprod
  rw [hone, hminus]
  ring

/-- In particular the mode-15 projection of the canonical candidate is
silent at its selected 827 coordinate.  This does not collapse it to zero. -/
theorem supportValuationAt_conjugatePairModeFifteenProjection827_eq_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (place : Place827 K) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) place
        (conjugatePairCharacterProjection827 K irregularCharacter59 place).1 =
      0 :=
  supportValuationAt_conjugatePairCharacterProjection827_eq_zero_of_odd
    K irregularCharacter59 place irregularCharacter59_negOne_reduction

/-- Conversely, the canonical mode-44 projection of the conjugate-pair
source has the already proved nonzero selected localization. -/
theorem supportValuationAt_conjugatePairModeFortyFourProjection827_ne_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (place : Place827 K) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) place
        (conjugatePairCharacterProjection827 K
          canonicalModeFortyFourCharacter59 place).1 ≠ 0 := by
  exact canonical_projected_conjugatePair_coordinate_ne_zero place

/-- The generic mode-44 projector is exactly the reflected projector used by
the canonical conjugate-pair lift. -/
theorem conjugatePairModeFortyFourProjection827_eq_canonical
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (place : Place827 K) :
    conjugatePairCharacterProjection827 K
        canonicalModeFortyFourCharacter59 place =
      qRelaxedReflectedProjector827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (conjugatePairSource827 place) := by
  rfl

/-! ## No simultaneous complementary detected seating -/

/-- Every p-adic character has residue parity `+1` or `-1` at complex
conjugation. -/
theorem character_negOne_reduction_eq_one_or_negOne
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    PadicInt.toZMod (eta (-1) : PadicInt 59) = 1 ∨
      PadicInt.toZMod (eta (-1) : PadicInt 59) = -1 := by
  apply sq_eq_one_iff.mp
  have hpow : eta (-1) ^ 2 = 1 := by
    rw [← map_pow]
    norm_num
  have hval := congrArg
    (fun u : (PadicInt 59)ˣ ↦ PadicInt.toZMod (u : PadicInt 59)) hpow
  simpa [map_pow] using hval

/-- If `chi` is even, its canonical Teichmuller reflection is odd. -/
theorem reflectedCharacter_negOne_reduction_eq_negOne_of_even
    (chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : PadicInt.toZMod (chi (-1) : PadicInt 59) = 1) :
    PadicInt.toZMod
        (InvolutiveBase.reflectedCharacter
          canonicalTeichmullerCharacter59 chi (-1) : PadicInt 59) = -1 := by
  have hprod := congrArg PadicInt.toZMod (chi (-1)).inv_val
  simp only [map_mul, map_one] at hprod
  have hinv :
      PadicInt.toZMod (↑((chi (-1))⁻¹) : PadicInt 59) = 1 := by
    rw [heven] at hprod
    simpa using hprod
  simp [InvolutiveBase.reflectedCharacter,
    canonicalTeichmullerCharacter59_negOne_reduction, hinv]

/-- For every possible `chi`, one side of the canonical complementary
seating loses its established detector: odd `chi` kills the strict real
unit, while even `chi` makes the reflected conjugate-pair coordinate odd
and hence zero. -/
theorem no_single_complementary_detected_seating827
    (chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (place : Place827 K) :
    strictGeneratedCharacterProjection827 K chi = 0 ∨
      supportValuationAt
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (S := placesOver827 K) place
          (conjugatePairCharacterProjection827 K
            (InvolutiveBase.reflectedCharacter
              canonicalTeichmullerCharacter59 chi) place).1 = 0 := by
  rcases character_negOne_reduction_eq_one_or_negOne chi with heven | hodd
  · right
    apply supportValuationAt_conjugatePairCharacterProjection827_eq_zero_of_odd
    exact reflectedCharacter_negOne_reduction_eq_negOne_of_even chi heven
  · left
    exact strictGeneratedCharacterProjection827_eq_zero_of_odd K chi hodd

end Fermat.FiftyNine.Conservation.CanonicalCharacterSeatingAudit827
