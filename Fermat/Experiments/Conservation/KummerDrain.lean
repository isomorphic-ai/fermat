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
import Fermat.Experiments.Conservation.Credit.Fold
import Fermat.Experiments.Conservation.CyclotomicDrain
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
  root_ne_zero : ∀ i, rootIdeal i ≠ 0
  root_pow : ∀ i, rootIdeal i ^ p = Ideal.span {factor i}

/-- The fractional-ideal quotient of two allocated roots. -/
def AllocatedFactorLedger.rootQuotient {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i j : ι) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (ledger.rootIdeal i : FractionalIdeal (𝓞 K)⁰ K) /
    (ledger.rootIdeal j : FractionalIdeal (𝓞 K)⁰ K)

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Every allocated ideal has a nonzero image in the fractional-ideal
ledger, so it has a well-defined ideal class. -/
theorem AllocatedFactorLedger.rootFractionalIdeal_ne_zero
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i : ι) :
    (ledger.rootIdeal i : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  intro hzero
  rw [FractionalIdeal.coeIdeal_eq_zero] at hzero
  exact ledger.root_ne_zero i hzero

/-- The additive ideal class carried by one allocated factor root. -/
noncomputable def AllocatedFactorLedger.rootClass
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i : ι) :
    Additive (ClassGroup (𝓞 K)) :=
  Fermat.Conservation.Credit.Fold.fractionalIdealClass
    (ledger.rootIdeal i : FractionalIdeal (𝓞 K)⁰ K)
    (ledger.rootFractionalIdeal_ne_zero i)

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Stock allocation makes every selected root class `p`-torsion. -/
theorem AllocatedFactorLedger.rootClass_torsion
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i : ι) :
    p • ledger.rootClass i = 0 := by
  unfold AllocatedFactorLedger.rootClass
  rw [Fermat.Conservation.Credit.Fold.nsmul_fractionalIdealClass_eq_zero_iff]
  rw [← FractionalIdeal.coeIdeal_pow, ledger.root_pow i,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The quotient of two allocated roots is nonzero. -/
theorem AllocatedFactorLedger.rootQuotient_ne_zero
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i j : ι) :
    ledger.rootQuotient i j ≠ 0 :=
  div_ne_zero (ledger.rootFractionalIdeal_ne_zero i)
    (ledger.rootFractionalIdeal_ne_zero j)

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

/-- Vandiver's relation (7a), stated on the actual classes selected by an
allocated factor ledger.  This is a proposition to be derived from the
state's arithmetic equations, not a field of the ledger. -/
def AllocatedFactorLedger.VandiverSevenA {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i j : ι) : Prop :=
  ledger.rootClass i + (p - 1) • ledger.rootClass j = 0

/-- Vandiver's relation (7d): the relative-norm fold of each selected
debit/receivable pair is zero. -/
def AllocatedFactorLedger.VandiverSevenD {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (i j : ι) : Prop :=
  ledger.rootClass i + ledger.rootClass j = 0

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The allocated debit/receivable class fold as an explicit transaction to
vacuum.  Its spent field is the killed relative-norm class amount. -/
noncomputable def AllocatedFactorLedger.vandiverSevenDFoldToVacuumTransfer
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R (𝓞 K)] [Module.Finite R (𝓞 K)]
    [Module.IsTorsionFree R (𝓞 K)]
    [Fintype (ClassGroup R)]
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (hp : p.Coprime (Fintype.card (ClassGroup R)))
    (i j : ι)
    (hfold :
      Ideal.map (algebraMap R (𝓞 K))
          (Ideal.relNorm R (ledger.rootIdeal i)) =
        ledger.rootIdeal i * ledger.rootIdeal j) :
    Fermat.Conservation.Transfer (Additive (ClassGroup (𝓞 K))) :=
  Fermat.Conservation.Credit.Fold.relativeNormFoldClassTransfer_of_coprime_card
    (R := R) (S := 𝓞 K) (L := K) hp
    (ledger.rootIdeal i) (ledger.rootIdeal j)
    (ledger.root_ne_zero i) (ledger.root_ne_zero j)
    (ledger.factor i) (ledger.root_pow i) hfold

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Vandiver's relation (7d) from the literal relative-norm fold of one
allocated debit/receivable pair.  The base class-group coprimality kills
the selected real norm class; no global assertion about the class group of
`K` is made. -/
theorem AllocatedFactorLedger.vandiverSevenD_of_relativeNormFold
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R (𝓞 K)] [Module.Finite R (𝓞 K)]
    [Module.IsTorsionFree R (𝓞 K)]
    [Fintype (ClassGroup R)]
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (hp : p.Coprime (Fintype.card (ClassGroup R)))
    (i j : ι)
    (hfold :
      Ideal.map (algebraMap R (𝓞 K))
          (Ideal.relNorm R (ledger.rootIdeal i)) =
        ledger.rootIdeal i * ledger.rootIdeal j) :
    ledger.VandiverSevenD i j := by
  unfold AllocatedFactorLedger.VandiverSevenD
  have hconverted :=
    (ledger.vandiverSevenDFoldToVacuumTransfer
      (R := R) hp i j hfold).converted_decomposition
  simpa only [AllocatedFactorLedger.vandiverSevenDFoldToVacuumTransfer,
    Fermat.Conservation.Credit.Fold.relativeNormFoldClassTransfer_of_coprime_card,
    Fermat.Conservation.Credit.Fold.foldToVacuumTransfer,
    AllocatedFactorLedger.rootClass,
    Fermat.Conservation.Ledger.vacuum, zero_add]
    using hconverted.symm

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Conjugation supplies the selected fold equality inside the same
allocated fold-to-vacuum transaction. -/
noncomputable def AllocatedFactorLedger.conjugationFoldToVacuumTransfer
    [NumberField.IsCMField K]
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (hp :
      p.Coprime
        (Fintype.card
          (ClassGroup
            (𝓞 (NumberField.maximalRealSubfield K)))))
    (i j : ι)
    (htranspose :
      ledger.rootIdeal j =
        Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (ledger.rootIdeal i)) :
    Fermat.Conservation.Transfer (Additive (ClassGroup (𝓞 K))) :=
  ledger.vandiverSevenDFoldToVacuumTransfer
    (R := 𝓞 (NumberField.maximalRealSubfield K)) hp i j (by
      calc
        Ideal.map
            (algebraMap
              (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
            (Ideal.relNorm
              (𝓞 (NumberField.maximalRealSubfield K))
              (ledger.rootIdeal i)) =
            ledger.rootIdeal i *
              Ideal.map
                (NumberField.IsCMField.ringOfIntegersComplexConj K)
                (ledger.rootIdeal i) :=
          Fermat.Conservation.Credit.Fold.map_relativeNorm_eq_mul_conjugate
            (ledger.rootIdeal i) (ledger.root_ne_zero i)
        _ = ledger.rootIdeal i * ledger.rootIdeal j := by
          rw [htranspose])

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Conjugation acting as the ledger transpose supplies the concrete
relative-norm identity, hence Vandiver's relation (7d). -/
theorem AllocatedFactorLedger.vandiverSevenD_of_conjugationTranspose
    [NumberField.IsCMField K]
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (hp :
      p.Coprime
        (Fintype.card
          (ClassGroup
            (𝓞 (NumberField.maximalRealSubfield K)))))
    (i j : ι)
    (htranspose :
      ledger.rootIdeal j =
        Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (ledger.rootIdeal i)) :
    ledger.VandiverSevenD i j := by
  unfold AllocatedFactorLedger.VandiverSevenD
  have hconverted :=
    (ledger.conjugationFoldToVacuumTransfer
      hp i j htranspose).converted_decomposition
  simpa only [AllocatedFactorLedger.conjugationFoldToVacuumTransfer,
    AllocatedFactorLedger.vandiverSevenDFoldToVacuumTransfer,
    Fermat.Conservation.Credit.Fold.relativeNormFoldClassTransfer_of_coprime_card,
    Fermat.Conservation.Credit.Fold.foldToVacuumTransfer,
    AllocatedFactorLedger.rootClass,
    Fermat.Conservation.Ledger.vacuum, zero_add]
    using hconverted.symm

/-- The first post-allocation permit required by Kummer's weighted
second-case step. -/
def FactorPrincipalizationPermit {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι) : Prop :=
  ∀ i j,
    Submodule.IsPrincipal
      (ledger.rootQuotient i j : Submodule (𝓞 K) K)

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Once one Fermat-produced debit/receivable pair supplies Vandiver's
statewise (7a) and the relative-norm fold (7d), the generic odd-torsion net
principalizes its draw.  No assertion about the rest of the class group is
used. -/
theorem AllocatedFactorLedger.rootQuotient_isPrincipal_of_vandiver_relations
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (hodd : Odd p) (i j : ι)
    (sevenA : ledger.VandiverSevenA i j)
    (sevenD : ledger.VandiverSevenD i j) :
    Submodule.IsPrincipal
      (ledger.rootQuotient i j : Submodule (𝓞 K) K) := by
  have hnet :=
    Fermat.Conservation.Credit.Fold.odd_torsion_netting
      hodd (ledger.rootClass i) (ledger.rootClass j)
      (ledger.rootClass_torsion j) sevenA sevenD
  have hI :
      Submodule.IsPrincipal
        ((ledger.rootIdeal i : FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K) :=
    (Fermat.Conservation.Credit.Fold.fractionalIdealClass_eq_zero_iff
      (ledger.rootIdeal i : FractionalIdeal (𝓞 K)⁰ K)
      (ledger.rootFractionalIdeal_ne_zero i)).mp hnet.1
  have hJ :
      Submodule.IsPrincipal
        ((ledger.rootIdeal j : FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K) :=
    (Fermat.Conservation.Credit.Fold.fractionalIdealClass_eq_zero_iff
      (ledger.rootIdeal j : FractionalIdeal (𝓞 K)⁰ K)
      (ledger.rootFractionalIdeal_ne_zero j)).mp hnet.2
  rw [FractionalIdeal.isPrincipal_iff] at hI hJ ⊢
  obtain ⟨a, ha⟩ := hI
  obtain ⟨b, hb⟩ := hJ
  refine ⟨a / b, ?_⟩
  rw [AllocatedFactorLedger.rootQuotient, ha, hb,
    FractionalIdeal.spanSingleton_div_spanSingleton]

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- Pairwise statewise relations discharge the complete factor-ledger
principalization permit. -/
theorem factorPrincipalizationPermit_of_vandiver_relations
    {ι : Type*}
    (ledger : AllocatedFactorLedger (p := p) (K := K) ι)
    (hodd : Odd p)
    (sevenA : ∀ i j, ledger.VandiverSevenA i j)
    (sevenD : ∀ i j, ledger.VandiverSevenD i j) :
    FactorPrincipalizationPermit ledger := by
  intro i j
  exact ledger.rootQuotient_isPrincipal_of_vandiver_relations
    hodd i j (sevenA i j) (sevenD i j)

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- On the two-node state ledger, Vandiver's relations are needed only for
the selected conjugate pair.  Netting that pair kills both classes; finite
case analysis then discharges the universal quotient permit without
pretending that the historical equations were separately produced for
every ordered pair. -/
theorem factorPrincipalizationPermit_finTwo_of_vandiver_relations
    (ledger : AllocatedFactorLedger (p := p) (K := K) (Fin 2))
    (hodd : Odd p)
    (sevenA : ledger.VandiverSevenA 0 1)
    (sevenD : ledger.VandiverSevenD 0 1) :
    FactorPrincipalizationPermit ledger := by
  have hnet :=
    Fermat.Conservation.Credit.Fold.odd_torsion_netting
      hodd (ledger.rootClass 0) (ledger.rootClass 1)
      (ledger.rootClass_torsion 1) sevenA sevenD
  apply factorPrincipalizationPermit_of_vandiver_relations ledger hodd
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [AllocatedFactorLedger.VandiverSevenA, hnet.1, hnet.2]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [AllocatedFactorLedger.VandiverSevenD, hnet.1, hnet.2]

end

end Fermat.Conservation.KummerDrain
