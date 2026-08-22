/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The concrete second-digit bridge from a twisted C_(59²) lift to the cup

Given a continuous `C_(59²)`-valued cochain, its pointwise reduction law,
and its explicit cyclotomic twisted-multiplication law, this file extracts
the second base-59 digit and proves the exact carry-minus-cup boundary
equation.

The remaining arithmetic producer is intentionally visible: this file does
not manufacture the compatible `mu_(59²)` root coordinate or assume that it
exists.  A later module must construct the input `q` and prove `hred` and
`htwist` from actual Kummer-root data.
-/
import Fermat.Experiments.Conservation.ContinuousCarryLiftObstruction59

noncomputable section

open Fermat.Conservation.CyclicCarryH2Class59
open Fermat.Conservation.FiniteCyclicH2Generator59

namespace Fermat.Conservation.ConcreteTwistedLiftCupBridge59

open Fermat.Conservation.ContinuousCarryLiftObstruction59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable {G : Type} [Group G] [TopologicalSpace G]

/-!
The input `q` below is deliberately not a homomorphism.  It is the
`C_(59^2)` coordinate of a chosen compatible Kummer root.  Its reduction is
the mod-59 Kummer character `chi`, and its failure to multiply is the
cyclotomic twist `eta(g) * chi(h)`.
-/

/-- The second base-59 digit comparing the standard section with a supplied
twisted `C_(59^2)` cochain. -/
def twistedCorrection59
    (chi : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared)) (g : G) : ZMod 59 :=
  (kernelCoordinate59 (standardSection59 (chi g) * (q g)⁻¹)).toAdd

/-- Pointwise reduction puts the section/cochain comparison in the kernel. -/
theorem twistedComparison_mem_kernel59
    (chi : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g) (g : G) :
    reduction59 (standardSection59 (chi g) * (q g)⁻¹) = 1 := by
  simp [hred g]

/-- Re-embedding the second digit recovers the section/cochain comparison. -/
theorem twistedComparison_eq_kernelEmbed59
    (chi : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g) (g : G) :
    standardSection59 (chi g) * (q g)⁻¹ =
      kernelEmbed59
        (Multiplicative.ofAdd (twistedCorrection59 chi q g)) := by
  symm
  exact kernelEmbed59_kernelCoordinate59 _
    (twistedComparison_mem_kernel59 chi q hred g)

/-- Factor the standard section through the twisted cochain and its second
digit. -/
theorem section_eq_twisted_mul_kernel59
    (chi : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g) (g : G) :
    standardSection59 (chi g) = q g *
      kernelEmbed59
        (Multiplicative.ofAdd (twistedCorrection59 chi q g)) := by
  have h := twistedComparison_eq_kernelEmbed59 chi q hred g
  calc
    standardSection59 (chi g) =
        (standardSection59 (chi g) * (q g)⁻¹) * q g := by simp
    _ = kernelEmbed59
        (Multiplicative.ofAdd (twistedCorrection59 chi q g)) * q g := by
          rw [h]
    _ = q g * kernelEmbed59
        (Multiplicative.ofAdd (twistedCorrection59 chi q g)) := by
          ac_rfl

/-- The twisted multiplication law forces the exact carry-plus-cyclotomic
law for the second digit. -/
theorem twistedCorrection59_add
    (chi eta : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed59 (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd)))
    (g h : G) :
    twistedCorrection59 chi q g + twistedCorrection59 chi q h =
      twistedCorrection59 chi q (g * h) +
        carry59 (chi g).toAdd (chi h).toAdd +
          (eta g).toAdd * (chi h).toAdd := by
  have hg := section_eq_twisted_mul_kernel59 chi q hred g
  have hh := section_eq_twisted_mul_kernel59 chi q hred h
  have hgh := section_eq_twisted_mul_kernel59 chi q hred (g * h)
  have hprod :
      (q g * q h) *
          (kernelEmbed59
              (Multiplicative.ofAdd (twistedCorrection59 chi q g)) *
            kernelEmbed59
              (Multiplicative.ofAdd (twistedCorrection59 chi q h))) =
        (q g * q h) *
          (kernelEmbed59
              (Multiplicative.ofAdd
                ((eta g).toAdd * (chi h).toAdd)) *
            (kernelEmbed59
                (Multiplicative.ofAdd
                  (twistedCorrection59 chi q (g * h))) *
              kernelEmbed59
                (Multiplicative.ofAdd
                  (carry59 (chi g).toAdd (chi h).toAdd)))) := by
    calc
      (q g * q h) *
          (kernelEmbed59
              (Multiplicative.ofAdd (twistedCorrection59 chi q g)) *
            kernelEmbed59
              (Multiplicative.ofAdd (twistedCorrection59 chi q h))) =
        (q g * kernelEmbed59
              (Multiplicative.ofAdd (twistedCorrection59 chi q g))) *
          (q h * kernelEmbed59
              (Multiplicative.ofAdd (twistedCorrection59 chi q h))) := by
                ac_rfl
      _ = standardSection59 (chi g) * standardSection59 (chi h) := by
            rw [← hg, ← hh]
      _ = standardSection59 (chi g * chi h) *
          kernelEmbed59
            (Multiplicative.ofAdd
              (carry59 (chi g).toAdd (chi h).toAdd)) := by
            rw [standardSection59_mul]
      _ = standardSection59 (chi (g * h)) *
          kernelEmbed59
            (Multiplicative.ofAdd
              (carry59 (chi g).toAdd (chi h).toAdd)) := by
            congr 1
            exact congrArg standardSection59 (chi.map_mul g h).symm
      _ = (q (g * h) *
          kernelEmbed59
            (Multiplicative.ofAdd
              (twistedCorrection59 chi q (g * h)))) *
          kernelEmbed59
            (Multiplicative.ofAdd
              (carry59 (chi g).toAdd (chi h).toAdd)) := by
            rw [hgh]
      _ = (q g * q h) *
          (kernelEmbed59
              (Multiplicative.ofAdd
                ((eta g).toAdd * (chi h).toAdd)) *
            (kernelEmbed59
                (Multiplicative.ofAdd
                  (twistedCorrection59 chi q (g * h))) *
              kernelEmbed59
                (Multiplicative.ofAdd
                  (carry59 (chi g).toAdd (chi h).toAdd)))) := by
            rw [htwist]
            ac_rfl
  have hkernel := mul_left_cancel hprod
  have hcoordinate :
      Multiplicative.ofAdd (twistedCorrection59 chi q g) *
          Multiplicative.ofAdd (twistedCorrection59 chi q h) =
        Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd) *
          (Multiplicative.ofAdd (twistedCorrection59 chi q (g * h)) *
            Multiplicative.ofAdd
              (carry59 (chi g).toAdd (chi h).toAdd)) := by
    apply kernelEmbed59_injective
    simpa only [map_mul] using hkernel
  have hadd := congrArg Multiplicative.toAdd hcoordinate
  change twistedCorrection59 chi q g + twistedCorrection59 chi q h =
      (eta g).toAdd * (chi h).toAdd +
        (twistedCorrection59 chi q (g * h) +
          carry59 (chi g).toAdd (chi h).toAdd) at hadd
  linear_combination hadd

/-- The second digit is continuous because its finite target is discrete. -/
theorem continuous_twistedCorrection59
    (chi : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared)) :
    Continuous (twistedCorrection59 chi q) := by
  have hcomparison : Continuous
      (fun g : G ↦ standardSection59 (chi g) * (q g)⁻¹) :=
    (standardSection59.continuous.comp chi.continuous).mul q.continuous.inv
  have hcoordinate : Continuous
      (fun z : CyclicGroup59Squared ↦ (kernelCoordinate59 z).toAdd) :=
    continuous_of_discreteTopology
  exact hcoordinate.comp hcomparison

/-- The concrete primitive: the second digit plus the pointwise product of
the mod-59 Kummer and cyclotomic characters. -/
def twistedCupPrimitive59
    (chi eta : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared)) : C(G, ZMod 59) where
  toFun g := (chi g).toAdd * (eta g).toAdd +
    twistedCorrection59 chi q g
  continuous_toFun := by
    have hchi : Continuous (fun g : G ↦ (chi g).toAdd) := chi.continuous
    have heta : Continuous (fun g : G ↦ (eta g).toAdd) := eta.continuous
    exact (hchi.mul heta).add (continuous_twistedCorrection59 chi q)

/-- The concrete root/reduction/action data mechanically produce the exact
inhomogeneous primitive equation needed for carry = Kummer cup. -/
theorem twistedCupPrimitive59_equation
    (chi eta : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed59 (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd)))
    (g h : G) :
    twistedCupPrimitive59 chi eta q h -
        twistedCupPrimitive59 chi eta q (g * h) +
        twistedCupPrimitive59 chi eta q g =
      carry59 (chi g).toAdd (chi h).toAdd -
        (chi g).toAdd * (eta h).toAdd := by
  have hc := twistedCorrection59_add chi eta q hred htwist g h
  have hchi : (chi (g * h)).toAdd =
      (chi g).toAdd + (chi h).toAdd := by
    exact congrArg Multiplicative.toAdd (chi.map_mul g h)
  have heta : (eta (g * h)).toAdd =
      (eta g).toAdd + (eta h).toAdd := by
    exact congrArg Multiplicative.toAdd (eta.map_mul g h)
  change
    ((chi h).toAdd * (eta h).toAdd + twistedCorrection59 chi q h) -
        ((chi (g * h)).toAdd * (eta (g * h)).toAdd +
          twistedCorrection59 chi q (g * h)) +
        ((chi g).toAdd * (eta g).toAdd + twistedCorrection59 chi q g) = _
  rw [hchi, heta]
  linear_combination hc

end Fermat.Conservation.ConcreteTwistedLiftCupBridge59
