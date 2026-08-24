import Fermat.Descent.Irregular.BernoulliChannelProjection
import Fermat.Descent.Irregular.SelectiveCircularUnitResidues

/-!
# Auxiliary-prime providers for finite Bernoulli channels

A provider supplies one authenticated residue factorization and one nonzero
auxiliary scalar for each row of a finite Bernoulli support.  Normalizing the
detector vector removes those scalars coordinatewise and recovers the
intrinsic projection exactly.  The provider can then be compiled into the
q-free `ProjectionKernelCertificate` consumed by descent.

The structure intentionally accepts arbitrary existing `Factorization`s.
Generated cyclic phase receipts and the basis-free certificate constructor
can therefore share the same downstream API.
-/

namespace Fermat.Irregular.AuxiliaryBernoulliChannelProvider

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.BernoulliChannelProjection
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.SelectiveCircularUnitResidues
open KummerCriterion.CyclotomicUnits

variable {p q N : ℕ} [Fact p.Prime] [Fact q.Prime]

universe u

/-- Finite auxiliary-prime evidence for every row in a Bernoulli support.
Only one scalar nonvanishing proof is stored per selected channel. -/
structure AuxiliaryChannelProvider
    (support : BernoulliChannelSupport p N) (hp_three : 3 ≤ p)
    (C : Certificate p q) where
  factorization : ∀ i, Factorization p q hp_three C (support.row i)
  scalar_ne : ∀ i, (factorization i).scalar ≠ 0

namespace AuxiliaryChannelProvider

variable {support : BernoulliChannelSupport p N} {hp_three : 3 ≤ p}
variable {C : Certificate p q}

/-- The vector of raw q-dependent residue detectors. -/
def residueDetector
    (A : AuxiliaryChannelProvider support hp_three C)
    (e : Fin (kummerLogRank p) → ZMod p) : Fin N → ZMod p :=
  fun i ↦ (A.factorization i).residueDetector e

/-- Normalize every selected residue detector by its own auxiliary scalar. -/
def normalizedResidueDetector
    (A : AuxiliaryChannelProvider support hp_three C)
    (e : Fin (kummerLogRank p) → ZMod p) : Fin N → ZMod p :=
  fun i ↦ (A.factorization i).normalizedResidueDetector e

/-- Coordinatewise normalization recovers the intrinsic vector projection
exactly. -/
theorem normalizedResidueDetector_eq_projection
    (A : AuxiliaryChannelProvider support hp_three C)
    (e : Fin (kummerLogRank p) → ZMod p) :
    A.normalizedResidueDetector e = support.projection hp_three e := by
  funext i
  exact (A.factorization i).normalizedResidueDetector_eq_canonical
    (A.scalar_ne i) e

/-- Compile q-dependent finite evidence into the q-free projection-kernel
certificate used by the descent. -/
def toProjectionKernelCertificate
    (A : AuxiliaryChannelProvider support hp_three C) :
    ProjectionKernelCertificate.{u} support hp_three where
  powerRelation_kernel := by
    intro K _ _ _ _ s e hpow
    apply (support.projection_eq_zero_iff hp_three _).2
    intro i
    exact canonicalKummerChannel_exponents_eq_zero_of_CPlus_product_mem_powers
      (K := K) C hp_three (A.factorization i) (A.scalar_ne i) s e hpow

end AuxiliaryChannelProvider

end

end Fermat.Irregular.AuxiliaryBernoulliChannelProvider
