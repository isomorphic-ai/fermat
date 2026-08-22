/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# W3: generic flow forcing

The high flow is read first in character coordinates.  Its eigenvalue in
row `k` is the numerator of the coefficient generated at index
`2 * (k + 1) * p`.  A cube-free eigenvalue turns the integral high-flow
congruence into vanishing modulo `p`; the generator-derived C5 gauge then
turns character-coordinate vanishing into raw exponent divisibility.

The certificate retains the exact lift/coupling decomposition and explicit
surplus at every row.  Cube-freeness is only its compatibility corollary.
The character matrix, its integral lift, and every eigenvalue remain
definitions derived from the gauge generator and the Bernoulli generator.
-/
import Fermat.Experiments.Conservation.Credit.Bernoulli
import Fermat.Experiments.Conservation.Credit.HighFlow
import Fermat.Experiments.Conservation.Credit.Repayment

open scoped BigOperators

namespace Fermat.Conservation.Credit.Flow

open Gauge

/-- The reusable per-prime assembly boundary.

The forcing theorem uses only `gauge`, but a campaign instance records the
generation tower, the independently checked lamp, and its irregular row in
the same object.  Thus a later prime supplies one record instead of adding
numeric facts to the generic core. -/
structure CreditData (p : ℕ) where
  gauge : GaugeData p
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

/-- The selected high index contains exactly one structural factor of the
prime.  This is the lift channel and uses only the generated gauge rank. -/
theorem highIndex_padicVal_eq_one {p : ℕ}
    (data : GaugeData p) (row : Fin data.rank) :
    padicValNat p (highIndex (data := data) row) = 1 := by
  letI : Fact p.Prime := ⟨data.prime⟩
  let multiplier := 2 * (row.val + 1)
  have hmultiplierPos : 0 < multiplier := by
    dsimp [multiplier]
    omega
  have hmultiplierLt : multiplier < p := by
    have hrow := row.isLt
    have hrank := data.rank_spec
    dsimp [multiplier]
    omega
  have hmultiplierNotDvd : ¬p ∣ multiplier :=
    Nat.not_dvd_of_pos_of_lt hmultiplierPos hmultiplierLt
  have hp0 : p ≠ 0 := data.prime.ne_zero
  have hm0 : multiplier ≠ 0 := hmultiplierPos.ne'
  rw [show highIndex (data := data) row = p * multiplier by
    simp [highIndex, multiplier, Nat.mul_comm],
    padicValNat.mul hp0 hm0, padicValNat_self,
    padicValNat.eq_zero_of_not_dvd hmultiplierNotDvd]

/-- The structure-preserving Bernoulli depth certificate attached to the
generated high-flow family. -/
abbrev BernoulliChannelCertificate {p : ℕ} (data : GaugeData p) :=
  Bernoulli.ChannelCertificate p
    (highIndex (data := data)) (highEigenvalue (data := data))

/-- The non-real compatibility flow also retains the full two-channel
profile and explicit surplus. -/
structure FlowCertificate {p : ℕ} (data : GaugeData p) where
  channels : BernoulliChannelCertificate data
  surplus_eq_zero : ∀ row, channels.surplus row = 0

/-- Compatibility reading of the retained channel certificate. -/
theorem FlowCertificate.eigenvalue_cubeFree {p : ℕ}
    {data : GaugeData p} (certificate : FlowCertificate data) :
    ∀ row, ¬(p : ℤ) ^ 3 ∣ highEigenvalue (data := data) row := by
  letI : Fact p.Prime := ⟨data.prime⟩
  exact certificate.channels.cubeFree_of_surplus_eq_zero
    certificate.surplus_eq_zero

private theorem prime_dvd_left_of_cube_dvd_mul_of_cube_free
    {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hprod : (p : ℤ) ^ 3 ∣ a * b)
    (hb : ¬(p : ℤ) ^ 3 ∣ b) :
    (p : ℤ) ∣ a := by
  by_contra ha
  apply hb
  have hna : ¬p ∣ a.natAbs := by
    simpa [Int.natCast_dvd] using ha
  have hnat : Nat.Coprime (p ^ 3) a.natAbs :=
    (hp.coprime_pow_of_not_dvd hna).symm
  have hint : IsCoprime ((p : ℤ) ^ 3) a := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Int.natAbs_pow] using hnat
  exact hint.dvd_of_dvd_mul_right (by simpa [mul_comm] using hprod)

/-- W2 plus the cube-free certificate invert a vanished high flow: every
raw exponent is divisible by `p`. -/
theorem exponent_dvd_of_highFlowVanishes {p : ℕ}
    (data : GaugeData p) (certificate : FlowCertificate data)
    (raw : Fin data.rank → ℤ) (hflow : HighFlowVanishes data raw) :
    ∀ i, (p : ℤ) ∣ raw i := by
  have hcharacterDvd :
      ∀ row, (p : ℤ) ∣ exactHighEdgeCoefficient data raw row :=
    fun row ↦
      prime_dvd_left_of_cube_dvd_mul_of_cube_free data.prime
        (hflow row) (certificate.eigenvalue_cubeFree row)
  have hcharacter :
      data.characterCoordinates (fun i ↦ (raw i : ZMod p)) = 0 := by
    funext row
    rw [← intCast_exactHighEdgeCoefficient]
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (exactHighEdgeCoefficient data raw row) p).2
        (hcharacterDvd row)
  have hraw :
      (fun i ↦ (raw i : ZMod p)) = 0 :=
    data.raw_eq_zero_of_character_eq_zero _ hcharacter
  intro i
  exact
    (ZMod.intCast_zmod_eq_zero_iff_dvd (raw i) p).1
      (by simpa using congrFun hraw i)

/-- W1's relation-level L4 output.  This predicate does not contain
exponent divisibility or a repayment conclusion: it says only that a deep
generated relation has the integral high-flow congruences defined above. -/
def DeepFlowLaw {p : ℕ} {G : Type*} [CommGroup G]
    (data : GaugeData p)
    (realize : (ZMod p)ˣ → G) (deep : G → Prop) : Prop :=
  ∀ (u : G), deep u →
    ∀ (t : ℕ) (raw : Fin data.rank → ℤ),
      0 < t →
      u ^ t = ∏ i, data.cycle.edge realize i ^ raw i →
      ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ raw i) →
      HighFlowVanishes data raw

/-- **Generic W3 forcing.** W1 supplies high-flow vanishing, the retained
channel certificate supplies its conservation-derived cube-free reading,
and W2 supplies the generator-derived inverse gauge.  The result is
precisely the exponent divisibility consumed by repayment. -/
theorem deepExponentForcing {p : ℕ} {G : Type*} [CommGroup G]
    (data : GaugeData p)
    (realize : (ZMod p)ˣ → G) (deep : G → Prop)
    (certificate : FlowCertificate data)
    (hL4 : DeepFlowLaw data realize deep) :
    Repayment.DeepExponentForcing data.cycle realize p deep := by
  intro u hdeep t raw ht hrelation hprimitive
  exact exponent_dvd_of_highFlowVanishes data certificate raw
    (hL4 u hdeep t raw ht hrelation hprimitive)

end Fermat.Conservation.Credit.Flow
