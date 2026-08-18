/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Nonvanishing of the fixed-root height-one detector ledger at 827

This module transports the already proved 58-place nonvanishing result to
the fixed-root finite-support ledger on genuine height-one places.  It also
states the final wild nonvanishing implication directly in terms of an
unweighted balance equation on that ledger.  This is a detector statement,
not a global Hilbert-reciprocity identification.
-/
import Fermat.FiftyNine.Conservation.ActualTameLedger827
import Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827
open Fermat.FiftyNine.Conservation.ActualTameLedger827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

universe uK

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The unweighted total of the fixed-root height-one-place detector ledger
is nonzero whenever the genuine lift is read in a nontrivial even
complementary mode. -/
theorem actualTameLedger827_sum_ne_zero
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : orientedPrimalMode827 omega chi (-1) = 1)
    (hne : orientedPrimalMode827 omega chi ≠ 1)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) :
    (actualTameLedger827 (K := K) omega chi lift).sum
        (fun _ value ↦ value) ≠ 0 := by
  rw [actualTameLedger827_sum_eq_orbit_sum]
  exact sum_actualTameOrbitValue827_ne_zero
    (K := K) omega chi heven hne lift selected

/-- In particular, the fixed-root finite-support ledger itself is nonzero. -/
theorem actualTameLedger827_ne_zero
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : orientedPrimalMode827 omega chi (-1) = 1)
    (hne : orientedPrimalMode827 omega chi ≠ 1)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) :
    actualTameLedger827 (K := K) omega chi lift ≠ 0 := by
  intro hzero
  apply actualTameLedger827_sum_ne_zero
    (K := K) omega chi heven hne lift selected
  rw [hzero]
  simp

/-- A supplied unweighted balance equation on the fixed-root height-one
ledger forces the wild scalar to be nonzero.  This premise is not the
globally `zeta`-normalized reciprocity equation. -/
theorem wild_ne_zero_of_actualTameLedgerReciprocity827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : orientedPrimalMode827 omega chi (-1) = 1)
    (hne : orientedPrimalMode827 omega chi ≠ 1)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) (wildReading : ZMod 59)
    (reciprocity : wildReading +
      (actualTameLedger827 (K := K) omega chi lift).sum
        (fun _ value ↦ value) = 0) :
    wildReading ≠ 0 := by
  apply wild_ne_zero_of_actualTameOrbitReciprocity827
    (K := K) omega chi heven hne lift selected
  exact (wild_add_actualTameLedger827_sum_eq_zero_iff
    (K := K) omega chi lift wildReading).mp reciprocity

end Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827
