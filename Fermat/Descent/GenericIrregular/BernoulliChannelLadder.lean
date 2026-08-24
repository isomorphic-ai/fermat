import Fermat.Descent.GenericIrregular.FixedExponent
import Fermat.Descent.Irregular.BernoulliChannelClassNumber

/-!
# Full finite Bernoulli-channel ladder

This module assembles a new, parallel fixed-exponent route whose Case-II.1
and Case-II.2 certificates are indexed by literally the same finite Bernoulli
support.  The support is the primary p-only spine; a finite pointwise equality
checks that every existing lifted channel carries exactly its corresponding
support index:

* the q-free projection-kernel receipt proves plus-class nondivisibility;
* the existing lifted power-sum channels prove the Bernoulli cube condition;
* a `LemmaTwoUnitSystem` proves Vandiver's Lemma II;
* an explicit `SophieGermainCertificate` supplies Case I.

The historical fixed-exponent route and its proof-producing Case-I search are
unchanged.  This is an additional constructor intended for the channel-count
ladder `N = 0, 1, 2, ...`.
-/

open scoped NumberField

namespace Fermat.GenericIrregular.BernoulliChannelLadder

noncomputable section

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.GenericIrregular.FixedExponent
open Fermat.GenericIrregular.LemmaTwo
open Fermat.GenericIrregular.SecondCase
open Fermat.Irregular
open Fermat.Irregular.BernoulliChannelProjection

/- The canonical cyclotomic field is available at every prime exponent. -/
local instance primeNeZero (p : ℕ) [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

local instance primeNeZeroRat (p : ℕ) [Fact p.Prime] :
    NeZero (p : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩

local instance cyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  CyclotomicField.isCyclotomicExtension p ℚ

namespace ChannelSupport

variable {p N : ℕ} [Fact p.Prime]

/-- The p-only Bernoulli support carried by an existing Case-II.2 channel
certificate.  Defining the support this way makes the Case-II.1/Case-II.2
index agreement true by construction. -/
def ofFixedChannelCertificate (C : FixedChannelCertificate p N) :
    BernoulliChannelSupport p N where
  index := fun i ↦ (C.channel i).index
  index_mem := fun i ↦ (C.channel i).index_mem
  index_injective := C.index_injective
  complete := by
    intro k hk hdiv
    obtain ⟨i, hi⟩ := C.complete k hk hdiv
    exact ⟨i, hi.symm⟩

@[simp] theorem ofFixedChannelCertificate_index
    (C : FixedChannelCertificate p N) (i : Fin N) :
    (ofFixedChannelCertificate C).index i = (C.channel i).index :=
  rfl

end ChannelSupport

/-- All finite data in the explicit Bernoulli-channel ladder at one prime.

No conclusion-shaped theorem is stored.  The Case-II.1 receipt is indexed by
the explicit primary `support`; `channel_index_eq` identifies it with the
upstream Case-II.2 channel family.  The remaining fields are finite unit data
and an explicit Sophie--Germain witness. -/
structure LadderCertificate (p N : ℕ) [Fact p.Prime] where
  exponent_atLeastFive : 5 ≤ p
  support : BernoulliChannelSupport p N
  channels : FixedChannelCertificate p N
  projectionKernel :
    ProjectionKernelCertificate.{0} support (by omega)
  channel_index_eq :
    ∀ i, support.index i = (channels.channel i).index
  unitSystem :
    @LemmaTwoUnitSystem
      (CyclotomicField p ℚ) p
      _ _ _
      (IsCyclotomicExtension.IsCMField (p := p) (CyclotomicField p ℚ)
        (by omega))
      _
  sophieGermain : SophieGermainCertificate p

namespace LadderCertificate

variable {p N : ℕ} [Fact p.Prime]

/-- The channel ladder first derives its second-case exclusion.  Case-II.1
comes from the intrinsic projection receipt; Case-II.2 uses the same channel
family through the existing weighted-moment theorem. -/
theorem secondCaseExcluded (C : LadderCertificate p N) :
    Fermat.SecondCaseExcluded p := by
  have hp5 : 5 ≤ p := C.exponent_atLeastFive
  letI : NumberField.IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.IsCMField (p := p) (CyclotomicField p ℚ)
      (by omega)
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField p ℚ)
      (Set.mem_singleton p) (Fact.out : p.Prime).ne_zero
  have hplus :
      Fermat.Irregular.VandiverHistoricalPrime.PlusClassNondivisibility
        (CyclotomicField p ℚ) p :=
    C.projectionKernel.plusClassNondivisibility hp5
  have hLemmaTwo :
      Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo
        (CyclotomicField p ℚ) p :=
    vandiverLemmaTwo_of_unitSystem hp5 C.unitSystem
  intro a b c ha hb hc hgcd hdiv
  exact
    (secondCaseExcluded_of_plusClass_of_lemmaTwo_of_channels
      (K := CyclotomicField p ℚ) (p := p) (N := N)
      hp5 hζ hplus hLemmaTwo C.channels)
      ha hb hc hgcd hdiv

/-- A complete ladder certificate proves FLT using its explicit auxiliary
prime.  This leaves the older search-based fixed-exponent constructor intact. -/
theorem holdsAt (C : LadderCertificate p N) : Fermat.HoldsAt p := by
  have hp5 : 5 ≤ p := C.exponent_atLeastFive
  exact
    Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
      (Fact.out : p.Prime)
      ((Fact.out : p.Prime).odd_of_ne_two (by omega))
      C.sophieGermain.auxiliaryPrime_isPrime
      C.sophieGermain.noConsecutivePowers
      C.sophieGermain.exponentNotPower
      C.secondCaseExcluded

end LadderCertificate

/-- Function-form endpoint for the generator: finite ladder data produce FLT
at the selected prime, with certificate size controlled by `N`. -/
theorem holdsAt_of_ladderCertificate {p N : ℕ} [Fact p.Prime]
    (C : LadderCertificate p N) : Fermat.HoldsAt p :=
  C.holdsAt

end

end Fermat.GenericIrregular.BernoulliChannelLadder
