/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# W3: forcing on the real residue quotient

The high flow is generated from indexed lifts of the intrinsic real residue
cycle.  Prime-cube vanishing and a cube-free generated eigenvalue force the
raw edge exponents to vanish modulo the prime; C3 repayment consumes exactly
that conclusion.

No matrix, inverse, eigenvalue vector, or depth law is a field of the
per-prime certificate.  The only arithmetic certificate is cube-freeness;
the depth law is a theorem to be derived upstream from the generated unit
relation.
-/
import Fermat.Conservation.Credit.RealHighFlow
import Fermat.Conservation.Credit.Repayment

namespace Fermat.Conservation.Credit.RealFlow

open RealGauge

/-- The reusable per-prime assembly boundary for the quotient-ready flow.

The generation tower, independent attestation, and irregular row are named
fields so a new conductor is supplied by constructing one record rather
than by editing the generic core. -/
structure CreditData (p : ℕ) where
  gauge : RealGaugeData p
  generationSeed : ℕ
  generationMiddle : ℕ
  innerStep : ℕ
  outerStep : ℕ
  rank_generated :
    gauge.rank = innerStep * generationSeed
  middle_generated :
    generationMiddle = innerStep * generationSeed + 1
  conductor_generated :
    p = outerStep * generationMiddle + 1
  attestationPrime : ℕ
  attestationPrime_prime : attestationPrime.Prime
  attestationRoot : ZMod attestationPrime
  attestationRootValue : ℕ
  attestationRoot_value :
    attestationRoot = attestationRootValue
  attestationRoot_order :
    orderOf attestationRoot = p
  irregularIndex : ℕ
  irregularRow : Fin gauge.rank
  irregularIndex_eq_row :
    irregularIndex = 2 * (irregularRow.val + 1)

/-- W1's relation-level L4 output.

This predicate contains neither exponent divisibility nor a repayment
conclusion.  It states only that a deep primitive relation on the generated
real quotient cycle has the integral high-flow congruences derived in
`RealHighFlow`. -/
def DeepFlowLaw {p : ℕ} {G : Type*} [CommGroup G]
    (data : CreditData p)
    (realize : RealResidueGroup p → G) (deep : G → Prop) : Prop :=
  ∀ (u : G), deep u →
    ∀ (t : ℕ) (raw : Fin data.gauge.rank → ℤ),
      0 < t →
      u ^ t = ∏ i, data.gauge.cycle.edge realize i ^ raw i →
      ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ raw i) →
      HighFlowVanishes data.gauge raw

/-- **Generic W3 forcing for every odd-prime real gauge.**

W1 supplies high-flow vanishing, the per-prime certificate supplies only
cube-freeness of the generated eigenvalues, and C5 supplies the derived
inverse gauge.  The conclusion is precisely the exponent divisibility
consumed by repayment. -/
theorem deepExponentForcing {p : ℕ} {G : Type*} [CommGroup G]
    (data : CreditData p)
    (realize : RealResidueGroup p → G) (deep : G → Prop)
    (certificate : FlowCertificate data.gauge)
    (hL4 : DeepFlowLaw data realize deep) :
    Repayment.DeepExponentForcing data.gauge.cycle realize p deep := by
  intro u hdeep t raw ht hrelation hprimitive
  exact exponent_dvd_of_highFlowVanishes data.gauge certificate raw
    (hL4 u hdeep t raw ht hrelation hprimitive)

end Fermat.Conservation.Credit.RealFlow
