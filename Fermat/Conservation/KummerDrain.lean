/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Kummer's factor ledger on the stock conservation spine

This file carries the second-case factorization as far as the stock
conservation primitives do.  The linear factors form a multiplicative
ideal ledger, absolute norm is its charge, and N7 gauge units preserve that
charge.  Once pairwise allocation has written each normalized factor ideal
as a prime-th power, the quotient of two allocated roots has a principal
prime-th power.

The next statement needed by Kummer's weighted descent is principality of
the root quotient itself.  That is intentionally named as a proposition,
not assumed here: removing the exponent from an ideal-class equation is
exactly the first non-stock obligation exposed by the compiler.
-/
import Fermat.Conservation.CyclotomicDrain
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

open scoped BigOperators NumberField nonZeroDivisors

namespace Fermat.Conservation.KummerDrain

noncomputable section

open Polynomial

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K}

/-- A node in Kummer's factor ledger. -/
abbrev RootNode :=
  ↥(Polynomial.nthRootsFinset p (1 : 𝓞 K))

/-- The linear factor attached to a `p`th root of unity. -/
def factorNode (x y η : 𝓞 K) :
    𝓞 K :=
  x + η * y

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- The sum-of-powers factorization, before ideal allocation. -/
theorem factorNode_product
    (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (x y : 𝓞 K) :
    x ^ p + y ^ p =
      ∏ η ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K),
        factorNode x y η := by
  simpa only [factorNode] using
    hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul x y hodd

/-- The principal ideal at one factor-ledger node. -/
def factorIdeal (x y η : 𝓞 K) :
    Ideal (𝓞 K) :=
  Ideal.span {factorNode x y η}

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Factorization transported to the multiplicative ideal ledger. -/
theorem factorIdeal_product
    (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (x y : 𝓞 K) :
    Ideal.span {x ^ p + y ^ p} =
      ∏ η ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K),
        factorIdeal x y η := by
  rw [factorNode_product hζ hodd]
  rw [← Ideal.prod_span_singleton]
  rfl

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- The factorization is also a literal multiplicative charge ledger. -/
theorem factorNode_charge_product
    (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (x y : 𝓞 K) :
    CyclotomicDrain.charge (x ^ p + y ^ p) =
      ∏ η ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K),
        CyclotomicDrain.charge (factorNode x y η) := by
  rw [factorNode_product hζ hodd]
  simp only [CyclotomicDrain.charge,
    Fermat.Seven.Conservation.charge, map_prod]
  change
    Int.natAbsHom
        (∏ η ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K),
          Algebra.norm ℤ (factorNode x y η)) =
      _
  rw [map_prod Int.natAbsHom]
  rfl

/-- Full N7 gauge multiplication preserves every factor-node charge. -/
theorem factorNode_charge_gauge_invariant
    (coordinates : Fermat.Seven.Conservation.FullGaugeCoordinates K)
    (x y η : 𝓞 K) :
    CyclotomicDrain.charge
        ((Fermat.Seven.Conservation.fullGaugeUnit K coordinates : 𝓞 K) *
          factorNode x y η) =
      CyclotomicDrain.charge (factorNode x y η) :=
  Fermat.Seven.Conservation.charge_full_gauge_invariant
    coordinates (factorNode x y η)

/-- The output vocabulary of pairwise factor-ideal allocation.  Each
normalized factor ideal has been written as a `p`th power; no
principalization of the chosen root is included. -/
structure AllocatedFactorLedger (ι : Type*) where
  factor : ι → 𝓞 K
  rootIdeal : ι → Ideal (𝓞 K)
  root_pow : ∀ i, rootIdeal i ^ p = Ideal.span {factor i}

/-- The fractional-ideal quotient of two allocated roots. -/
def AllocatedFactorLedger.rootQuotient {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i j : ι) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (ledger.rootIdeal i : FractionalIdeal (𝓞 K)⁰ K) /
    (ledger.rootIdeal j : FractionalIdeal (𝓞 K)⁰ K)

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Stock bookkeeping proves that the `p`th power of every allocated root
quotient is principal. -/
theorem AllocatedFactorLedger.rootQuotient_pow_isPrincipal
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i j : ι) :
    Submodule.IsPrincipal
      (((ledger.rootQuotient i j) ^ p :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [rootQuotient, div_pow,
    ← FractionalIdeal.coeIdeal_pow,
    ← FractionalIdeal.coeIdeal_pow,
    ledger.root_pow i, ledger.root_pow j,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_div_spanSingleton,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

/-- The first post-allocation permit required by Kummer's weighted
second-case step. -/
def FactorPrincipalizationPermit {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι) : Prop :=
  ∀ i j,
    Submodule.IsPrincipal
      (ledger.rootQuotient i j : Submodule (𝓞 K) K)

end

end Fermat.Conservation.KummerDrain
