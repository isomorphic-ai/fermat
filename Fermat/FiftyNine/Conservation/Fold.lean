/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conductor-59 relative-norm fold

The generated capacity certificate and the bounded Sinnott bridge make the
maximal-real class number prime to `59`.  Consequently an allocated pair
satisfies Vandiver's equation (7d) as soon as the state's literal relative
ideal norm extends to the product of its debit and receivable roots.

The remaining state work is deliberately visible in that ideal equality:
this file does not install (7d), conjugate pairing, or a factor ledger as
provider data.
-/
import Fermat.Conservation.KummerDrain
import Fermat.FiftyNine.Conservation.BoundedSinnott
import Fermat.FiftyNine.Conservation.CapacityCertificate
import Mathlib.NumberTheory.NumberField.ClassNumber

open scoped NumberField

namespace Fermat.FiftyNine.Conservation.Fold

noncomputable section

open Fermat.FiftyNine.Conservation

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- C2 plus the bounded Sinnott index comparison make the maximal-real
class-group order prime to the selected exponent. -/
theorem not_dvd_plusClassNumber :
    ¬59 ∣ NumberField.classNumber K⁺ := by
  let hζ : IsPrimitiveRoot
      (IsCyclotomicExtension.zeta 59 ℚ K) 59 :=
    IsCyclotomicExtension.zeta_spec 59 ℚ K
  exact Credit.boundedSinnottBridge (K := K) hζ
    (CapacityCertificate.capacityCertificate (K := K) hζ).2

private theorem coprime_plusClassNumber :
    Nat.Coprime 59 (Fintype.card (ClassGroup (𝓞 K⁺))) := by
  have hclass :
      ¬59 ∣ NumberField.classNumber K⁺ :=
    not_dvd_plusClassNumber (K := K)
  change ¬59 ∣ Fintype.card (ClassGroup (𝓞 K⁺)) at hclass
  exact (by norm_num : Nat.Prime 59).coprime_iff_not_dvd.mpr hclass

/-- The conductor-59 specialization of the allocated relative-norm
fold-to-vacuum transaction. -/
noncomputable def vandiverSevenDFoldToVacuumTransfer
    {ι : Type*}
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := 59) (K := K) ι)
    (i j : ι)
    (hfold :
      Ideal.map (algebraMap (𝓞 K⁺) (𝓞 K))
          (Ideal.relNorm (𝓞 K⁺) (ledger.rootIdeal i)) =
        ledger.rootIdeal i * ledger.rootIdeal j) :
    Fermat.Conservation.Transfer (Additive (ClassGroup (𝓞 K))) :=
  ledger.vandiverSevenDFoldToVacuumTransfer
    (R := 𝓞 K⁺) (coprime_plusClassNumber (K := K)) i j hfold

/-- Vandiver's equation (7d) for an allocated state pair whose product is
the extension of its real relative norm. -/
theorem vandiverSevenD_of_relativeNormFold
    {ι : Type*}
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := 59) (K := K) ι)
    (i j : ι)
    (hfold :
      Ideal.map (algebraMap (𝓞 K⁺) (𝓞 K))
          (Ideal.relNorm (𝓞 K⁺) (ledger.rootIdeal i)) =
        ledger.rootIdeal i * ledger.rootIdeal j) :
    ledger.VandiverSevenD i j := by
  unfold Fermat.Conservation.KummerDrain.AllocatedFactorLedger.VandiverSevenD
  have hconverted :=
    (vandiverSevenDFoldToVacuumTransfer
      ledger i j hfold).converted_decomposition
  simpa only [vandiverSevenDFoldToVacuumTransfer,
    Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenDFoldToVacuumTransfer,
    Fermat.Conservation.Credit.Fold.relativeNormFoldClassTransfer_of_coprime_card,
    Fermat.Conservation.Credit.Fold.foldToVacuumTransfer,
    Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootClass,
    Fermat.Conservation.Ledger.vacuum, zero_add]
    using hconverted.symm

/-- Conjugation-transpose instantiated at conductor 59 as the same
fold-to-vacuum transaction. -/
noncomputable def conjugationFoldToVacuumTransfer
    {ι : Type*}
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := 59) (K := K) ι)
    (i j : ι)
    (htranspose :
      ledger.rootIdeal j =
        Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (ledger.rootIdeal i)) :
    Fermat.Conservation.Transfer (Additive (ClassGroup (𝓞 K))) :=
  ledger.conjugationFoldToVacuumTransfer
    (coprime_plusClassNumber (K := K)) i j htranspose

/-- Conjugation as ledger transpose supplies the relative-norm fold, so the
selected allocated pair satisfies Vandiver's equation (7d). -/
theorem vandiverSevenD_of_conjugationTranspose
    {ι : Type*}
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := 59) (K := K) ι)
    (i j : ι)
    (htranspose :
      ledger.rootIdeal j =
        Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (ledger.rootIdeal i)) :
    ledger.VandiverSevenD i j := by
  unfold Fermat.Conservation.KummerDrain.AllocatedFactorLedger.VandiverSevenD
  have hconverted :=
    (conjugationFoldToVacuumTransfer
      ledger i j htranspose).converted_decomposition
  simpa only [conjugationFoldToVacuumTransfer,
    Fermat.Conservation.KummerDrain.AllocatedFactorLedger.conjugationFoldToVacuumTransfer,
    Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenDFoldToVacuumTransfer,
    Fermat.Conservation.Credit.Fold.relativeNormFoldClassTransfer_of_coprime_card,
    Fermat.Conservation.Credit.Fold.foldToVacuumTransfer,
    Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootClass,
    Fermat.Conservation.Ledger.vacuum, zero_add]
    using hconverted.symm

/-- On a two-node allocated ledger, the one statewise (7a) equation and the
conjugation-transpose law discharge the complete quotient permit.  The
other ordered pairs follow only after the selected classes have netted to
zero. -/
theorem factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := 59) (K := K) (Fin 2))
    (sevenA : ledger.VandiverSevenA 0 1)
    (htranspose :
      ledger.rootIdeal 1 =
        Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (ledger.rootIdeal 0)) :
    Fermat.Conservation.KummerDrain.FactorPrincipalizationPermit
      ledger := by
  exact
    Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_finTwo_of_vandiver_relations
      ledger (by norm_num) sevenA
        (vandiverSevenD_of_conjugationTranspose
          ledger 0 1 htranspose)

end

end Fermat.FiftyNine.Conservation.Fold
