/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The 827 detector-witness audit

The supporter prime `827 = 2 * 7 * 59 + 1` has a genuine nonzero
power-residue readout: the first entry of the checked circular-unit matrix is
`48` in `ZMod 59`.  This file compares that arithmetic fact with the actual
Selmer carriers used by the tame Tate layer.

Both seated legs are currently character eigenspaces inside Mathlib's
*empty-support* Selmer group.  Their valuations therefore vanish modulo `p`
at every height-one place.  The explicit tame symbol's both-units law (in its
Kummer-quotient, `p`-divisible-valuation form) consequently makes every tame
pairing row zero, including every row above 827 and every fallback auxiliary
prime.

`TransverseDetectorWitness` records the requested honest target modulo the
wild reading: a right-eigenspace candidate, two-place representative support,
and a computed nonzero auxiliary reading.  The generic no-go theorem below
shows that this structure cannot be inhabited with the current empty-support
dual leg.  A construction needs a dual Selmer condition relaxed at the
auxiliary places; replacing the missing class by a zero reading would not be
transverse.
-/
import Fermat.Conservation.TamePlacePairing
import Fermat.FiftyNine.Conservation.CapacityCertificate

open scoped nonZeroDivisors

noncomputable section

namespace Fermat.FiftyNine.Conservation.DetectorWitness827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TamePlacePairing

/-! ## The executable 827 lamp readout -/

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

/-- The first node of the generated 28-node real unit ledger. -/
def firstLedgerNode : Credit.LedgerNode :=
  ⟨0, by norm_num [Credit.LedgerNode]⟩

/-- The first checked power-residue coordinate at the first place above 827.
It is the row `j = 0`, first generated-edge column `i = 0` entry. -/
def firstLampReading827 : ZMod 59 :=
  CapacityCertificate.generatedMatrix firstLedgerNode firstLedgerNode

/-- The first 827 lamp coordinate is the explicitly computed value `48`. -/
theorem firstLampReading827_eq : firstLampReading827 = 48 := by
  decide +kernel +revert

/-- In particular, the finite 827 lamp is not the zero channel. -/
theorem firstLampReading827_ne_zero : firstLampReading827 ≠ 0 := by
  rw [firstLampReading827_eq]
  decide

/-- The first generated circular-unit edge has residue `105` at the first
selected embedding over 827. -/
theorem firstEdgeResidue827_eq :
    CapacityCertificate.edgeResidue firstLedgerNode firstLedgerNode = 105 := by
  decide +kernel +revert

/-- Its fourteenth-power symbol is the concrete residue `803`. -/
theorem firstEdgeSymbol827_eq :
    CapacityCertificate.edgeResidue firstLedgerNode firstLedgerNode ^ (2 * 7) =
      (803 : ZMod Credit.attestationPrime) := by
  decide +kernel +revert

/-- The same symbol is `671^48`, tying the numerical residue back to the
checked order-59 coordinate rather than treating `48` as uploaded data. -/
theorem firstEdgeSymbol827_eq_root_pow_reading :
    CapacityCertificate.edgeResidue firstLedgerNode firstLedgerNode ^ (2 * 7) =
      Credit.attestationRoot ^ firstLampReading827.val := by
  decide +kernel +revert

/-! ## The honest q-relaxed target, with the wild value omitted -/

universe uTargetK uTargetPlace uTargetResidue uTargetDelta uTargetDual

/-- The actual construction target for one auxiliary supporter prime.

`tame_away_from_wild` makes every place not over `p` part of the tame locus.
`candidate_relaxed_valuation` is the defining local condition of the Selmer
group relaxed at the places over `p` and `q`.  The explicit representative
support fields strengthen this to literal valuation zero away from those
places, so `outside_tame_reading_eq_zero` below follows from the both-units
law.  `right_eigenlaw` records the reflected-character leg without assuming
an unconstructed global Galois action.  The q-readings are explicit tame
symbols and at least one is required to be nonzero.  There is deliberately no
wild-reading field. -/
structure TransverseDetectorWitness
    (p q k : ℕ) [Fact p.Prime]
    (K : Type uTargetK) [Field K]
    (Place : Type uTargetPlace)
    (placePrime : Place → ℕ)
    (Residue : Place → Type uTargetResidue)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place → Prop)
    (context : ∀ v, IsTame v → TameSymbol.Context p K (Residue v))
    (Delta : Type uTargetDelta) [CommGroup Delta]
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (Dual : Type uTargetDual) [AddCommGroup Dual] [Module (PadicInt p) Dual]
    (dualAction : Representation (PadicInt p) Delta Dual)
    (dualClass : Dual →+ TameSymbol.KummerClass p K)
    (primalClass : TameSymbol.KummerClass p K) where
  auxiliary_prime : q.Prime
  supporter_relation : q = 2 * k * p + 1
  tame_away_from_wild : ∀ v, placePrime v ≠ p → IsTame v
  candidate : Dual
  right_eigenlaw : ∀ delta,
    dualAction delta candidate =
      (InvolutiveBase.reflectedCharacter omega chi delta : PadicInt p) •
        candidate
  candidate_relaxed_valuation : ∀ v (hv : IsTame v),
    placePrime v ≠ p → placePrime v ≠ q →
      (context v hv).ordModP (dualClass candidate) = 0
  primalRepresentative : Kˣ
  primal_represents :
    Additive.ofMul (QuotientGroup.mk' _ primalRepresentative) = primalClass
  candidateRepresentative : Kˣ
  candidate_represents :
    Additive.ofMul (QuotientGroup.mk' _ candidateRepresentative) =
      dualClass candidate
  primal_support : ∀ v (hp : placePrime v ≠ p), placePrime v ≠ q →
    (context v (tame_away_from_wild v hp)).ord
      (Additive.ofMul primalRepresentative) = 0
  candidate_support : ∀ v (hp : placePrime v ≠ p), placePrime v ≠ q →
    (context v (tame_away_from_wild v hp)).ord
      (Additive.ofMul candidateRepresentative) = 0
  qReadings : Place → ZMod p
  qReadings_computed : ∀ v (_hq : placePrime v = q) (hv : IsTame v),
    qReadings v =
      (context v hv).value primalRepresentative candidateRepresentative
  transverse : ∃ v, placePrime v = q ∧ IsTame v ∧ qReadings v ≠ 0

namespace TransverseDetectorWitness

variable
  {p q k : ℕ} [Fact p.Prime]
  {K : Type uTargetK} [Field K]
  {Place : Type uTargetPlace}
  {placePrime : Place → ℕ}
  {Residue : Place → Type uTargetResidue}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place → Prop}
  {context : ∀ v, IsTame v → TameSymbol.Context p K (Residue v)}
  {Delta : Type uTargetDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Dual : Type uTargetDual} [AddCommGroup Dual] [Module (PadicInt p) Dual]
  {dualAction : Representation (PadicInt p) Delta Dual}
  {dualClass : Dual →+ TameSymbol.KummerClass p K}
  {primalClass : TameSymbol.KummerClass p K}

/-- Outside the wild and auxiliary rational primes, literal representative
support makes both entries units, so the explicit both-units law computes
the tame symbol as zero. -/
theorem outside_tame_reading_eq_zero
    (w : TransverseDetectorWitness p q k K Place placePrime Residue IsTame
      context Delta omega chi Dual dualAction dualClass primalClass)
    (v : Place) (hp : placePrime v ≠ p) (hq : placePrime v ≠ q) :
    (context v (w.tame_away_from_wild v hp)).value
      w.primalRepresentative w.candidateRepresentative = 0 :=
  (context v (w.tame_away_from_wild v hp)).both_units_silence
    w.primalRepresentative w.candidateRepresentative
    (w.primal_support v hp hq) (w.candidate_support v hp hq)

end TransverseDetectorWitness

/-! ## Attempting the target on the current seated carrier -/

namespace Seated

universe uR uK uk uDelta

variable {p auxiliaryPrime : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
    (Delta := Delta)}

abbrev Place := TamePlacePairing.Seated.Place (R := R)

abbrev Primal := TamePlacePairing.Seated.Primal
  (rho := rho) (chi := chi)

abbrev ReflectedDual := TamePlacePairing.Seated.ReflectedDual
  (rho := rho) (omega := omega) (chi := chi)

abbrev Pairing := TamePlacePairing.Seated.Pairing
  (p := p) (Delta := Delta) (omega := omega) (chi := chi)
  (R := R) (K := K) (rho := rho)

/-- The requested transverse-detector data *except* the wild reading.

The candidate is literally in the reflected-character eigenspace.  The
support field is stated for its canonical Kummer representative and says
that all integer valuations outside the distinguished and auxiliary places
are zero.  `auxiliaryReading_ne_zero` is what makes the auxiliary coordinate
transverse; omitting it would allow the zero candidate to masquerade as the
witness. -/
structure EmptySupportTransverseDetectorWitness
    (pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
      (chi := chi) (R := R) (K := K) (rho := rho))
    (Residue : Place (R := R) → Type uk)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place (R := R) → Prop)
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (placePrime : Place (R := R) → ℕ)
    (distinguished auxiliary : Place (R := R))
    (x : Primal (rho := rho) (chi := chi)) where
  candidate : ReflectedDual (rho := rho) (omega := omega) (chi := chi)
  auxiliary_ne_distinguished : auxiliary ≠ distinguished
  distinguished_liesOver : placePrime distinguished = p
  auxiliary_liesOver : placePrime auxiliary = auxiliaryPrime
  auxiliary_tame : IsTame auxiliary
  representative_support : ∀ v,
    v ≠ distinguished → v ≠ auxiliary →
      (v.valuationOfNeZero
        (SelmerEigenspace.quotientRepresentative candidate)).toAdd = 0
  auxiliaryReading : ZMod p
  auxiliaryReading_computed :
    pairing.pairAt auxiliary x candidate = auxiliaryReading
  auxiliaryReading_ne_zero : auxiliaryReading ≠ 0

namespace EmptySupportTransverseDetectorWitness

variable
  {pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
    (chi := chi) (R := R) (K := K) (rho := rho)}
  {Residue : Place (R := R) → Type uk}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place (R := R) → Prop}
  {realization : TamePlacePairing.Seated.Realization pairing Residue IsTame}
  {placePrime : Place (R := R) → ℕ}
  {distinguished auxiliary : Place (R := R)}
  {x : Primal (rho := rho) (chi := chi)}

/-- The candidate's type is the requested right/reflected eigenspace, and
unfolding subtype membership gives its explicit eigenvalue law. -/
theorem candidate_eigenlaw
    (w : EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
      pairing Residue IsTame realization placePrime distinguished auxiliary x)
    (delta : Delta) :
    rho delta w.candidate.1 =
      (InvolutiveBase.reflectedCharacter omega chi delta : PadicInt p) •
        w.candidate.1 :=
  (SelmerEigenspace.mem_characterEigenspace_iff
    rho (InvolutiveBase.reflectedCharacter omega chi) w.candidate.1).mp
      w.candidate.property delta

/-- Empty-support Selmer membership already forces the candidate valuation
to be divisible by `p` at every place, independently of its stronger
two-place integer-support certificate. -/
theorem candidate_valuation_dvd
    (w : EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
      pairing Residue IsTame realization placePrime distinguished auxiliary x)
    (v : Place (R := R)) :
    (p : ℤ) ∣
      (v.valuationOfNeZero
        (SelmerEigenspace.quotientRepresentative w.candidate)).toAdd :=
  SelmerEigenspace.quotientRepresentative_valuation_dvd v w.candidate

/-- The both-units law on the Kummer quotient silences every tame reading
of the two current empty-support seated legs.  No property of the numerical
auxiliary prime is used, so changing 827 to any fallback cannot repair this
carrier mismatch. -/
theorem reading_eq_zero_at_every_tame_auxiliary
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (v : Place (R := R)) (hv : IsTame v)
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    pairing.pairAt v x y = 0 :=
  realization.pairAt_eq_zero_at_tame_place v hv x y

/-- Hence the supposedly computed transverse coordinate of any proposed
witness is forced to zero. -/
theorem auxiliaryReading_eq_zero
    (w : EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
      pairing Residue IsTame realization placePrime distinguished auxiliary x) :
    w.auxiliaryReading = 0 := by
  rw [← w.auxiliaryReading_computed]
  exact reading_eq_zero_at_every_tame_auxiliary realization auxiliary
    w.auxiliary_tame x w.candidate

/-- **Generic fallback no-go.**  There is no transverse detector witness in
the current empty-support reflected Selmer leg at any tame auxiliary prime.
This covers 827 and every later prime in the generation-chain fallback list. -/
theorem not_nonempty
    (pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
      (chi := chi) (R := R) (K := K) (rho := rho))
    (Residue : Place (R := R) → Type uk)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place (R := R) → Prop)
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (placePrime : Place (R := R) → ℕ)
    (distinguished auxiliary : Place (R := R))
    (x : Primal (rho := rho) (chi := chi)) :
    ¬ Nonempty
      (EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
        pairing Residue IsTame realization placePrime
          distinguished auxiliary x) := by
  rintro ⟨w⟩
  exact w.auxiliaryReading_ne_zero (auxiliaryReading_eq_zero w)

end EmptySupportTransverseDetectorWitness

/-! ## The concrete lamp/seated mismatch at 827 -/

variable
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt 59) Delta}
  {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
    (Delta := Delta)}
  {pairing : Pairing (p := 59) (Delta := Delta) (omega := omega)
    (chi := chi) (R := R) (K := K) (rho := rho)}
  {Residue : Place (R := R) → Type uk}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place (R := R) → Prop}

/-- The concrete nonzero lamp coordinate `48` cannot be the tame pairing of
two classes in the current seated legs at a place over 827: that pairing is
forced to zero before the residue calculation is consulted. -/
theorem firstLampReading827_not_realized_by_seated_pairing
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (v827 : Place (R := R)) (hv827 : IsTame v827)
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    pairing.pairAt v827 x y ≠ firstLampReading827 := by
  rw [EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary
    realization v827 hv827 x y]
  exact Ne.symm firstLampReading827_ne_zero

end Seated

end Fermat.FiftyNine.Conservation.DetectorWitness827
