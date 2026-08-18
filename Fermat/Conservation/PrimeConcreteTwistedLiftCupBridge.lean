/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The prime-parametric concrete second-digit bridge

Given a continuous `C_(p²)`-valued cochain, its pointwise reduction law,
and its explicit cyclotomic twisted-multiplication law, this file extracts
the second base-p digit and proves the exact carry-minus-cup boundary
equation.

The remaining arithmetic producer is intentionally visible: this file does
not manufacture the compatible `mu_(p²)` root coordinate or assume that it
exists.  A later module must construct the input `q` and prove `hred` and
`htwist` from actual Kummer-root data.
-/
import Fermat.Conservation.PrimeContinuousCarryLift

noncomputable section

namespace Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge

open Fermat.Conservation.PrimeContinuousCarryLift
open Fermat.Conservation.PrimeCyclicExtension

attribute [local instance]
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroup
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroup
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroupSquared
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroupSquared

variable {p : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [TopologicalSpace G]

/-!
The input `q` below is deliberately not a homomorphism.  It is the
`C_(p^2)` coordinate of a chosen compatible Kummer root.  Its reduction is
the mod-p Kummer character `chi`, and its failure to multiply is the
cyclotomic twist `eta(g) * chi(h)`.
-/

/-- The second base-p digit comparing the standard section with a supplied
twisted `C_(p^2)` cochain. -/
def twistedCorrection
    (chi : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p)) (g : G) : ZMod p :=
  (kernelCoordinate p (standardSection p (chi g) * (q g)⁻¹)).toAdd

/-- Pointwise reduction puts the section/cochain comparison in the kernel. -/
theorem twistedComparison_mem_kernel
    (chi : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g) (g : G) :
    reduction p (standardSection p (chi g) * (q g)⁻¹) = 1 := by
  simp [hred g]

/-- Re-embedding the second digit recovers the section/cochain comparison. -/
theorem twistedComparison_eq_kernelEmbed
    (chi : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g) (g : G) :
    standardSection p (chi g) * (q g)⁻¹ =
      kernelEmbed p
        (Multiplicative.ofAdd (twistedCorrection chi q g)) := by
  symm
  exact kernelEmbed_kernelCoordinate p _
    (twistedComparison_mem_kernel chi q hred g)

/-- Factor the standard section through the twisted cochain and its second
digit. -/
theorem section_eq_twisted_mul_kernel
    (chi : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g) (g : G) :
    standardSection p (chi g) = q g *
      kernelEmbed p
        (Multiplicative.ofAdd (twistedCorrection chi q g)) := by
  have h := twistedComparison_eq_kernelEmbed chi q hred g
  calc
    standardSection p (chi g) =
        (standardSection p (chi g) * (q g)⁻¹) * q g := by simp
    _ = kernelEmbed p
        (Multiplicative.ofAdd (twistedCorrection chi q g)) * q g := by
          rw [h]
    _ = q g * kernelEmbed p
        (Multiplicative.ofAdd (twistedCorrection chi q g)) := by
          ac_rfl

/-- The twisted multiplication law forces the exact carry-plus-cyclotomic
law for the second digit. -/
theorem twistedCorrection_add
    (chi eta : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed p (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd)))
    (g h : G) :
    twistedCorrection chi q g + twistedCorrection chi q h =
      twistedCorrection chi q (g * h) +
        PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd +
          (eta g).toAdd * (chi h).toAdd := by
  have hg := section_eq_twisted_mul_kernel chi q hred g
  have hh := section_eq_twisted_mul_kernel chi q hred h
  have hgh := section_eq_twisted_mul_kernel chi q hred (g * h)
  have hprod :
      (q g * q h) *
          (kernelEmbed p
              (Multiplicative.ofAdd (twistedCorrection chi q g)) *
            kernelEmbed p
              (Multiplicative.ofAdd (twistedCorrection chi q h))) =
        (q g * q h) *
          (kernelEmbed p
              (Multiplicative.ofAdd
                ((eta g).toAdd * (chi h).toAdd)) *
            (kernelEmbed p
                (Multiplicative.ofAdd
                  (twistedCorrection chi q (g * h))) *
              kernelEmbed p
                (Multiplicative.ofAdd
                  (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)))) := by
    calc
      (q g * q h) *
          (kernelEmbed p
              (Multiplicative.ofAdd (twistedCorrection chi q g)) *
            kernelEmbed p
              (Multiplicative.ofAdd (twistedCorrection chi q h))) =
        (q g * kernelEmbed p
              (Multiplicative.ofAdd (twistedCorrection chi q g))) *
          (q h * kernelEmbed p
              (Multiplicative.ofAdd (twistedCorrection chi q h))) := by
                ac_rfl
      _ = standardSection p (chi g) * standardSection p (chi h) := by
            rw [← hg, ← hh]
      _ = standardSection p (chi g * chi h) *
          kernelEmbed p
            (Multiplicative.ofAdd
              (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)) := by
            rw [standardSection_mul p]
      _ = standardSection p (chi (g * h)) *
          kernelEmbed p
            (Multiplicative.ofAdd
              (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)) := by
            congr 1
            exact congrArg (standardSection p) (chi.map_mul g h).symm
      _ = (q (g * h) *
          kernelEmbed p
            (Multiplicative.ofAdd
              (twistedCorrection chi q (g * h)))) *
          kernelEmbed p
            (Multiplicative.ofAdd
              (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)) := by
            rw [hgh]
      _ = (q g * q h) *
          (kernelEmbed p
              (Multiplicative.ofAdd
                ((eta g).toAdd * (chi h).toAdd)) *
            (kernelEmbed p
                (Multiplicative.ofAdd
                  (twistedCorrection chi q (g * h))) *
              kernelEmbed p
                (Multiplicative.ofAdd
                  (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)))) := by
            rw [htwist]
            ac_rfl
  have hkernel := mul_left_cancel hprod
  have hcoordinate :
      Multiplicative.ofAdd (twistedCorrection chi q g) *
          Multiplicative.ofAdd (twistedCorrection chi q h) =
        Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd) *
          (Multiplicative.ofAdd (twistedCorrection chi q (g * h)) *
            Multiplicative.ofAdd
              (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)) := by
    apply kernelEmbed_injective p
    simpa only [map_mul] using hkernel
  have hadd := congrArg Multiplicative.toAdd hcoordinate
  change twistedCorrection chi q g + twistedCorrection chi q h =
      (eta g).toAdd * (chi h).toAdd +
        (twistedCorrection chi q (g * h) +
          PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd) at hadd
  linear_combination hadd

/-- The second digit is continuous because its finite target is discrete. -/
theorem continuous_twistedCorrection
    (chi : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p)) :
    Continuous (twistedCorrection chi q) := by
  have hcomparison : Continuous
      (fun g : G ↦ standardSection p (chi g) * (q g)⁻¹) :=
    ((standardSection p).continuous.comp chi.continuous).mul q.continuous.inv
  have hcoordinate : Continuous
      (fun z : CyclicGroupSquared p ↦ (kernelCoordinate p z).toAdd) :=
    continuous_of_discreteTopology
  exact hcoordinate.comp hcomparison

/-- The concrete primitive: the second digit plus the pointwise product of
the mod-p Kummer and cyclotomic characters. -/
def twistedCupPrimitive
    (chi eta : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p)) : C(G, ZMod p) where
  toFun g := (chi g).toAdd * (eta g).toAdd +
    twistedCorrection chi q g
  continuous_toFun := by
    have hchi : Continuous (fun g : G ↦ (chi g).toAdd) := chi.continuous
    have heta : Continuous (fun g : G ↦ (eta g).toAdd) := eta.continuous
    exact (hchi.mul heta).add (continuous_twistedCorrection chi q)

/-- The concrete root/reduction/action data mechanically produce the exact
inhomogeneous primitive equation needed for carry = Kummer cup. -/
theorem twistedCupPrimitive_equation
    (chi eta : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed p (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd)))
    (g h : G) :
    twistedCupPrimitive chi eta q h -
        twistedCupPrimitive chi eta q (g * h) +
        twistedCupPrimitive chi eta q g =
      PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd -
        (chi g).toAdd * (eta h).toAdd := by
  have hc := twistedCorrection_add chi eta q hred htwist g h
  have hchi : (chi (g * h)).toAdd =
      (chi g).toAdd + (chi h).toAdd := by
    exact congrArg Multiplicative.toAdd (chi.map_mul g h)
  have heta : (eta (g * h)).toAdd =
      (eta g).toAdd + (eta h).toAdd := by
    exact congrArg Multiplicative.toAdd (eta.map_mul g h)
  change
    ((chi h).toAdd * (eta h).toAdd + twistedCorrection chi q h) -
        ((chi (g * h)).toAdd * (eta (g * h)).toAdd +
          twistedCorrection chi q (g * h)) +
        ((chi g).toAdd * (eta g).toAdd + twistedCorrection chi q g) = _
  rw [hchi, heta]
  linear_combination hc

end Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge
