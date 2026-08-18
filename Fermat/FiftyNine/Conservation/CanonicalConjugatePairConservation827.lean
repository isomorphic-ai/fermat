/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# A literal conservation receipt for the canonical 827 ledger

The canonical conjugate-pair ledger is a nonzero `Finsupp` of genuine
height-one-place readings whose scalar total is zero.  This file packages
that proved arithmetic object as the repository's generic `PlaceLedger`,
then routes it through the existing zero-spent transfer and scheduler L1
identity.

This is a conservation receipt for the explicit tame ledger.  It is not a
construction of a place-indexed Kummer--Tate pairing or a proof of global
Hilbert reciprocity for arbitrary global classes.
-/
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CanonicalConjugatePairConservation827

open Fermat.Conservation
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The concrete canonical 827 ledger with its proved zero total retained
as a literal `PlaceLedger` conservation law. -/
noncomputable def canonicalConjugatePairPlaceLedger827 :
    PlaceLedger (Place K) (ZMod 59) where
  entries := canonicalConjugatePairGlobalLedger827 (K := K)
  total := 0
  conservation := canonicalConjugatePairGlobalLedger827_sum_eq_zero

@[simp]
theorem canonicalConjugatePairPlaceLedger827_entries :
    (canonicalConjugatePairPlaceLedger827 (K := K)).entries =
      canonicalConjugatePairGlobalLedger827 (K := K) :=
  rfl

@[simp]
theorem canonicalConjugatePairPlaceLedger827_total :
    (canonicalConjugatePairPlaceLedger827 (K := K)).total = 0 :=
  rfl

/-- The retained place ledger is live: its zero total is cancellation, not
the zero family. -/
theorem canonicalConjugatePairPlaceLedger827_entries_ne_zero :
    (canonicalConjugatePairPlaceLedger827 (K := K)).entries ≠ 0 :=
  canonicalConjugatePairGlobalLedger827_ne_zero

/-- The live zero-total place ledger gives an actual zero-spent transfer to
the repository's literal vacuum. -/
noncomputable def canonicalConjugatePairVacuumTransfer827 :
    Transfer (ZMod 59) :=
  (canonicalConjugatePairPlaceLedger827 (K := K)).toVacuumTransfer rfl

@[simp]
theorem canonicalConjugatePairVacuumTransfer827_after :
    (canonicalConjugatePairVacuumTransfer827 (K := K)).after =
      Ledger.vacuum :=
  rfl

@[simp]
theorem canonicalConjugatePairVacuumTransfer827_spent :
    (canonicalConjugatePairVacuumTransfer827 (K := K)).spent = 0 :=
  rfl

/-- The explicit conjugate-pair cancellation enters the scheduler tunnel as
its exact L1 conservation identity. -/
theorem canonicalConjugatePairVacuumTransfer827_L1 :
    IsoConserveStatements.Columns.accounted
        (IsoConserveBridge.toColumns
          (canonicalConjugatePairVacuumTransfer827 (K := K)).after) =
      IsoConserveStatements.Columns.accounted
        (IsoConserveBridge.toColumns
          (canonicalConjugatePairVacuumTransfer827 (K := K)).before) :=
  PlaceLedger.toVacuumTransfer_L1
    (canonicalConjugatePairPlaceLedger827 (K := K)) rfl

end Fermat.FiftyNine.Conservation.CanonicalConjugatePairConservation827
