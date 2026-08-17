/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# A total trace-product constructor for Iwasawa-style wild pairings

This file isolates the cheapest algebraic part of an Iwasawa-style local
formula.  Three additive maps are enough to define a genuine bilinear
pairing on *all* nonzero representatives:

* a total augmented left coordinate;
* a total augmented right coordinate; and
* an additive trace/reduction map out of their common ring.

The word `augmented` is binding here.  These coordinates have domain
`Additive Kˣ`, not merely the principal-unit subgroup.  An arithmetic
instance must retain the valuation and root-of-unity/torsion contributions
needed outside principal units; a principal-unit logarithm alone is not an
inhabitant of the intended interface.  This generic file does not choose a
uniformizer, split `Kˣ`, or manufacture such an augmentation.

`ArithmeticSpecification`, `Realizes`, and `Reduction` expose the two
remaining arithmetic seams.  An instance must identify the bundled total
coordinates with independently defined norm-lift/kappa-derivative,
augmented-logarithmic, and trace data, and must separately compare the
resulting arithmetic trace product with its target reading.  Consequently
calibration is a theorem (`Reduction.representative_eq_reading`), never the
definition of the pairing.

No Hilbert-symbol, norm-residue, reciprocity, or Vostokov-series
identification is asserted here.
-/
import Fermat.Conservation.WildKummerPairing

noncomputable section

namespace Fermat.Conservation.IwasawaTracePairing

open Fermat.Conservation.WildKummerPairing

universe uK uA uLeft uRight

variable {p : ℕ} [Fact p.Prime]
  {K : Type uK} [Field K]
  {A : Type uA} [Ring A]

/-- Total augmented coordinates for an Iwasawa-style trace product.

Both coordinate maps are defined on every element of `Additive Kˣ`.
They are therefore *not* principal-unit logarithms in disguise: an
arithmetic realization must include the valuation and torsion/root-of-unity
contributions required to evaluate arbitrary nonzero representatives.  The
common ring `A` is intentionally generic so that those contributions may be
retained before multiplication and the final trace/reduction to `ZMod p`.
-/
structure TotalAugmentedCoordinates
    (p : ℕ) (K : Type uK) [Field K]
    (A : Type uA) [Ring A] where
  /-- Total norm-lift/kappa-side coordinate, including its non-principal
  contributions. -/
  leftCoordinate : Additive Kˣ →+ A
  /-- Total logarithmic-side coordinate after valuation and torsion
  augmentation; this is not merely a logarithm on principal units. -/
  rightCoordinate : Additive Kˣ →+ A
  /-- The additive local trace followed by the required reduction modulo
  `p`. -/
  traceModP : A →+ ZMod p

namespace TotalAugmentedCoordinates

/-- The representative pairing defined by the Iwasawa trace-product shape.

This is a definition from the three coordinate maps, not stored pairing
data.  Both bilinearity laws follow from additivity of the coordinates and
the two distributivity laws in `A`. -/
def representative
    (coordinates : TotalAugmentedCoordinates p K A) :
    WildKummerPairing.RepresentativePairing p K where
  toFun a :=
    { toFun := fun b ↦
        coordinates.traceModP
          (coordinates.leftCoordinate a * coordinates.rightCoordinate b)
      map_zero' := by simp
      map_add' := by
        intro b₁ b₂
        simp only [map_add, mul_add] }
  map_zero' := by
    ext b
    simp
  map_add' := by
    intro a₁ a₂
    apply AddMonoidHom.ext
    intro b
    simp [add_mul]

@[simp]
theorem representative_apply
    (coordinates : TotalAugmentedCoordinates p K A)
    (a b : Additive Kˣ) :
    coordinates.representative a b =
      coordinates.traceModP
        (coordinates.leftCoordinate a * coordinates.rightCoordinate b) :=
  rfl

/-- Canonically descend the trace-product formula to the Kummer quotient and
package its representative-level descent receipt. -/
def toWildKummerCore
    (coordinates : TotalAugmentedCoordinates p K A) :
    WildKummerPairing.Core p K :=
  WildKummerPairing.Core.ofRepresentative coordinates.representative

@[simp]
theorem toWildKummerCore_representative
    (coordinates : TotalAugmentedCoordinates p K A) :
    coordinates.toWildKummerCore.representative =
      coordinates.representative :=
  rfl

/-- Evaluation of the descended total pairing on two nonzero
representatives. -/
@[simp]
theorem toWildKummerCore_pairing_classOfUnit_classOfUnit
    (coordinates : TotalAugmentedCoordinates p K A)
    (a b : Additive Kˣ) :
    coordinates.toWildKummerCore.pairing
        (classOfUnit p K a) (classOfUnit p K b) =
      coordinates.traceModP
        (coordinates.leftCoordinate a * coordinates.rightCoordinate b) := by
  rw [WildKummerPairing.Core.pairing_classOfUnit_classOfUnit]
  exact coordinates.representative_apply a b

end TotalAugmentedCoordinates

/-! ## The named arithmetic realization and comparison boundary -/

/-- Independently specified arithmetic functions which a concrete local
construction must produce.

The left function is where the norm lift and kappa-derivative belong.  The
right function is a *total augmented* logarithmic coordinate: its intended
implementation must retain valuation and torsion data rather than extending
a principal-unit logarithm by zero.  `traceValue` includes the local trace,
normalization, and reduction modulo `p`.

These functions are deliberately not assumed additive here.  A `Realizes`
receipt identifies them pointwise with the bundled additive coordinates;
that receipt is the obligation which proves the concrete arithmetic
construction has the algebraic laws needed by the pairing.
-/
structure ArithmeticSpecification
    (p : ℕ) (K : Type uK) [Field K]
    (A : Type uA) [Ring A] where
  normLiftKappaDerivative : Additive Kˣ → A
  totalAugmentedLogarithmicCoordinate : Additive Kˣ → A
  traceValue : A → ZMod p

/-- Pointwise realization of independently defined arithmetic functions by
the total bundled coordinates.

This is the first still-missing tier-(c) seam.  Supplying it requires the
actual norm-lift/kappa construction and the valuation/torsion augmentation;
this file creates neither by a postulate nor by a choice of splitting.
-/
structure Realizes
    (coordinates : TotalAugmentedCoordinates p K A)
    (arithmetic : ArithmeticSpecification p K A) : Prop where
  leftCoordinate_eq : ∀ a,
    coordinates.leftCoordinate a = arithmetic.normLiftKappaDerivative a
  rightCoordinate_eq : ∀ b,
    coordinates.rightCoordinate b =
      arithmetic.totalAugmentedLogarithmicCoordinate b
  traceModP_eq : ∀ z,
    coordinates.traceModP z = arithmetic.traceValue z

/-- Independent comparison of an arithmetic trace product with a target
reading on selected carriers.

The representatives and the reading are parameters, so a concrete instance
can use its literal chosen representatives and its pre-existing reading.
The direction is important: this proposition compares an independently
specified arithmetic formula *to* the reading; it cannot define the formula
from that reading.
-/
def IsComparedOn
    (arithmetic : ArithmeticSpecification p K A)
    {Left : Type uLeft} {Right : Type uRight}
    (leftRepresentative : Left → Additive Kˣ)
    (rightRepresentative : Right → Additive Kˣ)
    (reading : Left → Right → ZMod p) : Prop :=
  ∀ x y,
    arithmetic.traceValue
        (arithmetic.normLiftKappaDerivative (leftRepresentative x) *
          arithmetic.totalAugmentedLogarithmicCoordinate
            (rightRepresentative y)) =
      reading x y

/-- The reduced tier-(c) interface.

An inhabitant provides only the total coordinate construction, its
arithmetic realization receipt, and the independent comparison needed by a
particular consumer.  The representative pairing and its Kummer descent are
then definitions.  No inhabitant is manufactured in this generic module.
-/
structure Reduction
    (p : ℕ) [Fact p.Prime]
    (K : Type uK) [Field K]
    (A : Type uA) [Ring A]
    {Left : Type uLeft} {Right : Type uRight}
    (leftRepresentative : Left → Additive Kˣ)
    (rightRepresentative : Right → Additive Kˣ)
    (reading : Left → Right → ZMod p) where
  arithmetic : ArithmeticSpecification p K A
  coordinates : TotalAugmentedCoordinates p K A
  realizes : Realizes coordinates arithmetic
  comparison : IsComparedOn arithmetic leftRepresentative
    rightRepresentative reading

namespace Reduction

variable {Left : Type uLeft} {Right : Type uRight}
  {leftRepresentative : Left → Additive Kˣ}
  {rightRepresentative : Right → Additive Kˣ}
  {reading : Left → Right → ZMod p}

/-- The total representative pairing constructed by a tier-(c) reduction. -/
def representative
    (reduction : Reduction p K A leftRepresentative rightRepresentative
      reading) : WildKummerPairing.RepresentativePairing p K :=
  reduction.coordinates.representative

/-- The canonically descended wild Kummer core constructed by a tier-(c)
reduction. -/
def toWildKummerCore
    (reduction : Reduction p K A leftRepresentative rightRepresentative
      reading) : WildKummerPairing.Core p K :=
  reduction.coordinates.toWildKummerCore

@[simp]
theorem representative_apply
    (reduction : Reduction p K A leftRepresentative rightRepresentative
      reading)
    (a b : Additive Kˣ) :
    reduction.representative a b =
      reduction.coordinates.traceModP
        (reduction.coordinates.leftCoordinate a *
          reduction.coordinates.rightCoordinate b) :=
  rfl

/-- Calibration on the selected representatives, derived from arithmetic
realization plus the independent comparison receipt. -/
theorem representative_eq_reading
    (reduction : Reduction p K A leftRepresentative rightRepresentative
      reading)
    (x : Left) (y : Right) :
    reduction.representative (leftRepresentative x)
        (rightRepresentative y) =
      reading x y := by
  rw [reduction.representative_apply,
    reduction.realizes.leftCoordinate_eq,
    reduction.realizes.rightCoordinate_eq,
    reduction.realizes.traceModP_eq]
  exact reduction.comparison x y

end Reduction

end Fermat.Conservation.IwasawaTracePairing
