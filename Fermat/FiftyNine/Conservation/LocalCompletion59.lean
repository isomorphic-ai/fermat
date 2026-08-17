/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The actual completion used by the 59-local pairing

This file replaces the abstract local field and localization map by Mathlib's
adic completion of the cyclotomic number field at a selected height-one
place.  Cyclotomicity also supplies a noncomputably chosen primitive `59`-th root
in the global field; injectivity of the completion embedding transports its
primitivity to the local field.

No local invariant or reciprocity statement is introduced here.  This is only
the honest structural bridge from the global field to its completion.
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.LocalCompletion59

variable (K : Type) [Field K] [NumberField K]
variable (distinguishedPlace :
  IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The concrete local field at the selected height-one place. -/
abbrev LocalField59 := distinguishedPlace.adicCompletion K

/-- The canonical embedding of the number field into its completion. -/
def localization59 : K →+* LocalField59 K distinguishedPlace :=
  NumberField.FinitePlace.embedding distinguishedPlace

/-- Readback of the completion embedding on a global element. -/
@[simp]
theorem localization59_apply (x : K) :
    localization59 K distinguishedPlace x =
      (x : LocalField59 K distinguishedPlace) :=
  rfl

section Cyclotomic

variable [IsCyclotomicExtension {59} ℚ K]

/-- Mathlib's noncomputably chosen primitive `59`-th root in the cyclotomic
number field. -/
def globalPrimitiveRoot59 : K :=
  IsCyclotomicExtension.zeta 59 ℚ K

/-- The global chosen root is primitive by the cyclotomic-extension API. -/
@[simp]
theorem globalPrimitiveRoot59_isPrimitive :
    IsPrimitiveRoot (globalPrimitiveRoot59 K) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

/-- The chosen primitive root embedded in the actual local completion. -/
def localPrimitiveRoot59 : LocalField59 K distinguishedPlace :=
  localization59 K distinguishedPlace (globalPrimitiveRoot59 K)

/-- Readback of the local root as the image of the global cyclotomic root. -/
@[simp]
theorem localPrimitiveRoot59_eq :
    localPrimitiveRoot59 K distinguishedPlace =
      localization59 K distinguishedPlace (globalPrimitiveRoot59 K) :=
  rfl

/-- Injectivity of the field embedding preserves the exact order `59`, so no
additional primitive-root premise is needed at the completion boundary. -/
@[simp]
theorem localPrimitiveRoot59_isPrimitive :
    IsPrimitiveRoot (localPrimitiveRoot59 K distinguishedPlace) 59 := by
  exact (globalPrimitiveRoot59_isPrimitive K).map_of_injective
    (localization59 K distinguishedPlace).injective

/-- The elementary root-of-unity readback used by downstream local code. -/
@[simp]
theorem localPrimitiveRoot59_pow :
    localPrimitiveRoot59 K distinguishedPlace ^ 59 = 1 :=
  (localPrimitiveRoot59_isPrimitive K distinguishedPlace).pow_eq_one

end Cyclotomic

end Fermat.FiftyNine.Conservation.LocalCompletion59
