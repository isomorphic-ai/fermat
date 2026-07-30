/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The generated credit ladder at conductor 59

This file instantiates C1--C3 at the generation tower

`7 --(4·_+1)--> 29 --(2·_+1)--> 59`.

Multiplication by `4` modulo `59` is the one generator of a 29-cycle.  Its
28 successive edges generate the real unit sub-ledger; `Fin 4 × Fin 7`
supplies its stock coordinates without enumerating the orbit.  Credit entries
are generated transfers between pairs of those edges.  The receivable matrix
is definitionally the transpose of the debit matrix.

The auxiliary prime and root are generated as
`2 * 59 * 7 + 1` and `2 ^ (2 * 7)`.  They are recorded here without
importing any table.  A later residue table may check the generated object;
it cannot define it.

The exact C2/C4 and C3 arithmetic propositions are named at the end.  They
are deliberately not asserted: the findings file records why the permitted
cone does not currently prove them.
-/
import Fermat.Conservation.Credit.Vacuum
import Fermat.Conservation.Credit.Repayment
import Fermat.Conservation.Credit.CyclotomicFlow
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.Conservation.Credit

/-! ## The generated numerical tower -/

/-- The completed stock rank, generated from the N7 seed. -/
def stockRank : ℕ := 4 * 7

/-- The real Galois-cycle order is the stock rank plus the seed. -/
def realCycleOrder : ℕ := stockRank + 1

/-- Two orientations of the real cycle plus the outer seed give the
conductor. -/
def conductor : ℕ := 2 * realCycleOrder + 1

theorem stockRank_eq_twentyEight : stockRank = 28 := by
  norm_num [stockRank]

theorem realCycleOrder_eq_twentyNine : realCycleOrder = 29 := by
  norm_num [realCycleOrder, stockRank]

theorem conductor_eq_fiftyNine : conductor = 59 := by
  norm_num [conductor, realCycleOrder, stockRank]

theorem generationTower :
    29 = 4 * 7 + 1 ∧ 59 = 2 * 29 + 1 := by
  norm_num

/-- The attestation prime is itself generated on the 7-tower. -/
def attestationPrime : ℕ := 2 * 59 * 7 + 1

theorem attestationPrime_eq_eightHundredTwentySeven :
    attestationPrime = 827 := by
  norm_num [attestationPrime]

theorem attestationPrime_isPrime :
    Nat.Prime attestationPrime := by
  norm_num [attestationPrime]

/-- The attestation root is generated from `2` and the two-sided stock
factor `2 * 7`; `671` is a checked value, not a seed. -/
def attestationRoot : ZMod attestationPrime :=
  (2 : ZMod attestationPrime) ^ (2 * 7)

theorem attestationRoot_eq_sixHundredSeventyOne :
    attestationRoot = 671 := by
  decide

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

theorem attestationRoot_order :
    orderOf attestationRoot = 59 := by
  rw [attestationRoot_eq_sixHundredSeventyOne]
  exact orderOf_eq_prime (by decide) (by decide)

/-! ## The order-29 generator and its 28 edges -/

/-- The square of a primitive full Galois generator; its orbit is the real
29-cycle. -/
def exponentGenerator : (ZMod 59)ˣ :=
  ZMod.unitOfCoprime 4 (by norm_num)

@[simp]
theorem exponentGenerator_val :
    (exponentGenerator : ZMod 59) = 4 := by
  rfl

theorem exponentGenerator_order :
    orderOf exponentGenerator = 29 := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem exponentGenerator_pow_order :
    exponentGenerator ^ 29 = 1 := by
  have h := pow_orderOf_eq_one exponentGenerator
  rwa [exponentGenerator_order] at h

/-- The single recursion producing the complete real Galois cycle. -/
def exponentCycle : Fermat.Conservation.Credit.Cycle ((ZMod 59)ˣ) :=
  Fermat.Conservation.Credit.Cycle.ofMul 28 exponentGenerator
    exponentGenerator_pow_order

@[simp]
theorem exponentCycle_rank :
    exponentCycle.rank = 28 :=
  rfl

theorem exponentCycle_exactPeriod :
    orderOf exponentGenerator = exponentCycle.rank + 1 := by
  rw [exponentGenerator_order]
  rfl

theorem exponentCycle_point (n : ℕ) :
    exponentCycle.point n = exponentGenerator ^ n := by
  exact Fermat.Conservation.Credit.Cycle.ofMul_point
    28 exponentGenerator exponentGenerator_pow_order n

/-- The 28 edge coordinates are generated as the product of the completed
N4 and N7 stock coordinates. -/
def stockCoordinatesEquiv :
    Fin 4 × Fin 7 ≃ Fin exponentCycle.rank := by
  simpa only [exponentCycle_rank] using
    (finProdFinEquiv : Fin 4 × Fin 7 ≃ Fin (4 * 7))

/-- The full exponent group has the structural two-sided shape
`Fin 2 × Fin 29`. -/
def twoSidedCoordinatesEquiv :
    Fin 2 × Fin realCycleOrder ≃ Fin 58 := by
  simpa only [realCycleOrder_eq_twentyNine] using
    (finProdFinEquiv : Fin 2 × Fin 29 ≃ Fin (2 * 29))

/-! ## Generated real cyclotomic units -/

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

/-- The geometric cyclotomic unit at a generated exponent node. -/
def orbitNodeUnit {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (a : (ZMod 59)ˣ) : (𝓞 K)ˣ :=
  Fermat.Conservation.Credit.Flow.cyclotomicOrbitNodeUnit hζ a

/-- Fold a unit with its conjugate.  This is the real, two-sided projection
of one unit, not an independently chosen second family. -/
def realProjection (u : (𝓞 K)ˣ) :
    NumberField.IsCMField.realUnits K :=
  Fermat.Conservation.Credit.Flow.realProjection u

/-- Every realized node is generated from the exponent recursion and folded
with its conjugate to make the two-sided structure real. -/
def realOrbitNode {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (a : (ZMod 59)ˣ) :
    NumberField.IsCMField.realUnits K :=
  Fermat.Conservation.Credit.Flow.realCyclotomicOrbitNode hζ a

/-- The 28 generated edge units. -/
def generatedUnit {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (i : Fin exponentCycle.rank) :
    NumberField.IsCMField.realUnits K :=
  exponentCycle.edge (realOrbitNode hζ) i

theorem generatedUnit_eq_orbit_ratio {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) (i : Fin exponentCycle.rank) :
    generatedUnit hζ i =
      realOrbitNode hζ (exponentCycle.point (i.val + 1)) *
        (realOrbitNode hζ (exponentCycle.point i.val))⁻¹ :=
  rfl

/-- The generated real unit sub-ledger. -/
def generatedSubledger {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    Subgroup (NumberField.IsCMField.realUnits K) :=
  exponentCycle.generatedSubledger (realOrbitNode hζ)

theorem generatedUnit_mem_subledger {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) (i : Fin exponentCycle.rank) :
    generatedUnit hζ i ∈ generatedSubledger hζ :=
  Fermat.Conservation.Credit.Cycle.edge_mem_generatedSubledger
    exponentCycle (realOrbitNode hζ) i

/-! ## The generated 28 × 28 node-pair ledger -/

abbrev LedgerNode := Fin exponentCycle.rank
abbrev LedgerGenerator := LedgerNode × LedgerNode

/-- A node pair is funded by the generated transfer between its two orbit
edges. -/
def fundingTransfer {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (generator : LedgerGenerator) :
    NumberField.IsCMField.realUnits K :=
  exponentCycle.transfer (realOrbitNode hζ)
    generator.1 generator.2

theorem fundingTransfer_opposite {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) (i j : LedgerNode) :
    fundingTransfer hζ (j, i) =
      (fundingTransfer hζ (i, j))⁻¹ :=
  Fermat.Conservation.Credit.Cycle.transfer_opposite
    exponentCycle (realOrbitNode hζ) i j

/-- Funding is membership in the sub-ledger generated by the edge orbit. -/
def fundedGenerators {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    Set LedgerGenerator :=
  {generator | fundingTransfer hζ generator ∈ generatedSubledger hζ}

theorem everyTransfer_isFunded {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) (generator : LedgerGenerator) :
    generator ∈ fundedGenerators hζ := by
  change generatedUnit hζ generator.1 *
      (generatedUnit hζ generator.2)⁻¹ ∈ generatedSubledger hζ
  apply Subgroup.mul_mem
  · exact generatedUnit_mem_subledger hζ generator.1
  · exact Subgroup.inv_mem _ (generatedUnit_mem_subledger hζ generator.2)

theorem fundedGenerators_eq_univ {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    fundedGenerators hζ = Set.univ :=
  Set.eq_univ_of_forall (everyTransfer_isFunded hζ)

/-- The one generated route from a transfer to its node pair. -/
def creditRoute :
    Fermat.Conservation.Credit.Route LedgerNode LedgerGenerator :=
  fun generator => generator

/-- The debit view of the generated 28 × 28 credit matrix. -/
def debitLedger {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.Ledger LedgerNode LedgerGenerator :=
  Fermat.Conservation.Credit.generated creditRoute (fundedGenerators hζ)

/-- The receivable view is the transpose of the same matrix. -/
def receivableLedger {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.Ledger LedgerNode LedgerGenerator :=
  Fermat.Conservation.Credit.opposite (debitLedger hζ)

@[simp]
theorem receivableLedger_apply {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) (debtor creditor : LedgerNode) :
    receivableLedger hζ creditor debtor =
      debitLedger hζ debtor creditor :=
  rfl

theorem receivableLedger_opposite {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.opposite (receivableLedger hζ) =
      debitLedger hζ :=
  Fermat.Conservation.Credit.opposite_opposite (debitLedger hζ)

theorem ledger_cardinality :
    Fintype.card LedgerNode = 4 * 7 := by
  norm_num [LedgerNode]

/-! ## C2 capacity and the bounded C4 bridge -/

/-- Capacity is the index of the generated edge sub-ledger in the full real
unit ledger.  No certificate number occurs in this definition. -/
noncomputable def capacityIndex {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) : ℕ :=
  exponentCycle.capacityIndex (realOrbitNode hζ) ⊥ ⊤

theorem capacityIndex_eq_relIndex {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    capacityIndex hζ = (generatedSubledger hζ).index := by
  simp [capacityIndex, Fermat.Conservation.Credit.Cycle.capacityIndex,
    Fermat.Conservation.Credit.Cycle.generatedSubledgerWith,
    generatedSubledger, Subgroup.relIndex_top_right]

/-- The exact check required from a C2 finite certificate. -/
def CapacityCertificateGoal {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) : Prop :=
  (generatedSubledger hζ).FiniteIndex ∧
    ¬59 ∣ capacityIndex hζ

/-- The bounded C4 implication demanded by the endpoint.  This is named but
not asserted; proving it is the localized Sinnott seam. -/
def BoundedSinnottBridge {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) : Prop :=
  (¬59 ∣ capacityIndex hζ) →
    ¬59 ∣ NumberField.classNumber
      (NumberField.maximalRealSubfield K)

/-! The C3 flow reading is assembled in `Conservation.Instance`.  Keeping
that specialization in the one instance layer prevents its selected-prime
depth and eigenvalue facts from leaking back into this generated C2 stock
object. -/

end

end Fermat.FiftyNine.Conservation.Credit
