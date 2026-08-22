/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The exact seated tame-orbit balance at 827

The canonical full-orbit pairing retains one normalized wild row at lambda
and all 58 globally-root-oriented tame rows above 827.  Global reciprocity
therefore says that the complete tame-orbit sum is the negative normalized
lambda reading.  In particular, orbit-only silence is equivalent to lambda
orthogonality; it is not a consequence of reciprocity alone.

The inputs here are the actual `chi` and `omega * chi^-1` character seats.
For the canonical irregular specialization these are modes 15 and 44.  This
file deliberately does not assert that the orbit reading kills every class
in the full global-unit range.  The first missing arithmetic input for that
stronger statement is arbitrary-unit odd-Fourier vanishing: the inverse-
oriented residue wave of every global unit must have zero mode-43
coefficient.  The repository currently proves that fact only for the first
generated real circular unit.
-/
import Fermat.Exponents.FiftyNine.Conservation.FullOrbitGlobalReciprocityCriterion827

open scoped BigOperators MonoidAlgebra NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open ActualTameLedger827
open CanonicalFullOrbitLocalPairing827
open CanonicalTameLedger827
open CyclotomicSelmerAction59
open CyclotomicTameContext59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open FullOrbitGlobalReciprocityCriterion827
open NormalizedContinuousKummerPairing59
open SplitPrimeFourier827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal
    (v : Place K) : v.asIdeal.IsMaximal := v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

variable (omega chi :
  InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- The sum of all 58 genuine globally-root-oriented tame rows on the two
actual complementary character seats. -/
noncomputable def seatedTameOrbitSum827
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) : ZMod 59 :=
  ∑ tau : GaloisIndex59,
    (context K (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
        (toKummerClass x) (toKummerClassAt y)

/-- Global reciprocity balances the complete 827 tame orbit against the
normalized lambda row.  No tame row, unit class, or Fourier mode is silently
discarded. -/
theorem seatedTameOrbitSum827_eq_neg_normalizedLambda_of_globalReciprocity
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K omega chi))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedTameOrbitSum827 K omega chi x y =
      -normalizedLambdaGlobalPairing59 K
        (toKummerClass x) (toKummerClassAt y) := by
  exact eq_neg_of_add_eq_zero_right
    ((globalReciprocityLaw_canonicalFullOrbitLocalPairing827_iff
      K omega chi).mp reciprocity x y)

/-- Under global reciprocity, orbit-only silence is exactly lambda
orthogonality.  Thus an arbitrary-unit orbit-silence theorem still owes a
unit-to-lambda orthogonality (or the equivalent odd-Fourier) argument. -/
theorem seatedTameOrbitSum827_eq_zero_iff_normalizedLambda_eq_zero
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K omega chi))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedTameOrbitSum827 K omega chi x y = 0 ↔
      normalizedLambdaGlobalPairing59 K
        (toKummerClass x) (toKummerClassAt y) = 0 := by
  rw [seatedTameOrbitSum827_eq_neg_normalizedLambda_of_globalReciprocity
    K omega chi reciprocity x y]
  exact neg_eq_zero

end Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827
