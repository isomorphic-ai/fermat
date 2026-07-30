/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The selected credit-flow instance

This is the only core-facing numerical assembly for the campaign prime.
The tower, orbit generator, lamp, irregular row, and high-eigenvalue
certificate boundary enter through named structure fields.  The generic
flow, gauge, and forcing files contain none of these literals.

The local-depth comparison is the generic generator-derived `DeepFlowLaw`.
This file instantiates it and the cube-free eigenvalue boundary; no
classical Vandiver module is imported here.
-/
import Fermat.Conservation.Credit.HighFlowClosure
import Fermat.Conservation.Credit.Bernoulli
import Fermat.FiftyNine.Conservation.Credit
import Fermat.FiftyNine.Conservation.CapacityCertificate

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.Conservation.Instance

/-! ## One named per-prime record -/

/-- The exact-order generator used by both C2 and the C5 gauge. -/
def gaugeData : Fermat.Conservation.Credit.Gauge.GaugeData 59 where
  rank := 28
  prime := by norm_num
  odd := by norm_num
  rank_spec := by norm_num
  orbitGenerator := Fermat.FiftyNine.Conservation.Credit.exponentGenerator
  orbitGenerator_order :=
    Fermat.FiftyNine.Conservation.Credit.exponentGenerator_order
  orbitGenerator_square_order := by
    rw [orderOf_pow' _ (by norm_num : 2 ≠ 0),
      Fermat.FiftyNine.Conservation.Credit.exponentGenerator_order]
    norm_num

/-- The intrinsic real-residue gauge derived from the same orbit lift. -/
noncomputable def realGaugeData :
    Fermat.Conservation.Credit.RealGauge.RealGaugeData 59 :=
  Fermat.Conservation.Credit.RealGauge.RealGaugeData.ofGaugeData gaugeData

/-- Every campaign-specific datum supplied to the generic credit core. -/
noncomputable def creditData :
    Fermat.Conservation.Credit.RealFlow.CreditData 59 where
  gauge := realGaugeData
  generationSeed := 7
  generationMiddle := 29
  innerStep := 4
  outerStep := 2
  rank_generated := by
    norm_num [realGaugeData,
      Fermat.Conservation.Credit.RealGauge.RealGaugeData.ofGaugeData,
      gaugeData]
  middle_generated := by norm_num
  conductor_generated := by norm_num
  attestationPrime :=
    Fermat.FiftyNine.Conservation.Credit.attestationPrime
  attestationPrime_prime :=
    Fermat.FiftyNine.Conservation.Credit.attestationPrime_isPrime
  attestationRoot :=
    Fermat.FiftyNine.Conservation.Credit.attestationRoot
  attestationRootValue := 671
  attestationRoot_value :=
    Fermat.FiftyNine.Conservation.Credit.attestationRoot_eq_sixHundredSeventyOne
  attestationRoot_order :=
    Fermat.FiftyNine.Conservation.Credit.attestationRoot_order
  irregularIndex := 44
  irregularRow := ⟨21, by
    norm_num [realGaugeData,
      Fermat.Conservation.Credit.RealGauge.RealGaugeData.ofGaugeData,
      gaugeData]⟩
  irregularIndex_eq_row := by norm_num

/-- The C5 cycle and the original C2 cycle are the same generated object. -/
theorem gauge_cycle_eq_exponentCycle :
    gaugeData.cycle =
      Fermat.FiftyNine.Conservation.Credit.exponentCycle := by
  rfl

/-! ## W1 and the high-eigenvalue certificate boundary -/

/-- The formal flow orbit uses the same cycle and the generic
generator-derived integer lift of every node.  Its selected degrees are
precisely the high Bernoulli degrees; no rate map is supplied. -/
noncomputable def generatorOrbit :
    Fermat.Conservation.Credit.Flow.GeneratorOrbit 59
      (Fermat.Conservation.Credit.RealGauge.RealResidueGroup 59) :=
  Fermat.Conservation.Credit.RealFlow.generatorOrbit realGaugeData

/-- The old generated numerator formula is now the eigenvalue derived by
the generic flow. -/
noncomputable def vandiverBernoulliNumerator
    (row : Fin realGaugeData.rank) : ℤ :=
  Fermat.Conservation.Credit.RealFlow.highEigenvalue
    (data := realGaugeData) row

/-- Absence of the exceptional high-Bernoulli alternative.  This keeps the
existing interface shape while referring to generated eigenvalues. -/
def NoBernoulliCubeObstruction59 : Prop :=
  ∀ row : Fin realGaugeData.rank,
    ¬(59 : ℤ) ^ 3 ∣ vandiverBernoulliNumerator row

/-! ### Kernel-checked Bernoulli cube certificate

The five finite tables below are the selected-prime payload.  Their laws
are checked in this file, while the pole-safe Faulhaber argument that turns
those laws into numerator cube-freeness is generic over every odd prime in
`Credit.Bernoulli`.
-/

namespace BernoulliCertificate

open Fermat.Conservation.Credit

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The quotient after removing the campaign prime from
`(n + 1).choose (n - 2)`. -/
def chooseQuotient :
    Fin gaugeData.rank → ℕ :=
  ![4641, 37130, 125315, 297044, 580165, 1002526, 1591975,
    2376360, 3383529, 4641330, 6177611, 8020220, 10197005,
    12735814, 15664495, 19010896, 22802865, 27068250,
    31834899, 37130660, 42983381, 49420910, 56471095,
    64161784, 72520825, 81576066, 91355355, 101886540]

/-- The raw power-sum residue after removing one factor of the campaign
prime.  The first entry is deliberately not the final Bernoulli residue:
its predecessor has a von-Staudt denominator at the campaign prime. -/
def rawPowerResidue :
    Fin gaugeData.rank → ℕ :=
  ![35400, 90388, 121422, 156527, 50268, 37701, 63307,
    180068, 161306, 119298, 180363, 43070, 57348, 139653,
    151335, 174168, 114342, 131452, 122838, 118708, 55578,
    62658, 118413, 8732, 130331, 148798, 7670, 137588]

/-- The residue of `p * B_(n-2)` modulo `p`.  Only the first row meets
the exceptional von-Staudt pole. -/
def predecessorResidue
    (row : Fin gaugeData.rank) : ℤ :=
  if row.val = 0 then -1 else 0

/-- The residue of the exceptional binomial quotient divided by `n + 1`. -/
def correctionWeight :
    Fin gaugeData.rank → ℤ :=
  ![39, 19, 58, 38, 18, 57, 37, 17, 56, 36, 16, 55, 35, 15,
    54, 34, 14, 53, 33, 13, 52, 32, 12, 51, 31, 11, 50, 30]

/-- Numerators of the `p`-integral error in `correctionWeight`; the common
denominator is three. -/
def weightLiftNumerator :
    Fin gaugeData.rank → ℕ :=
  ![0, 7, 15, 30, 49, 69, 96, 127, 159, 198, 241, 285, 336, 391,
    447, 510, 577, 645, 720, 799, 879, 966, 1057, 1149, 1248,
    1351, 1455, 1566]

/-- Corrected Bernoulli residues modulo the campaign-prime cube. -/
def correctedResidue :
    Fin gaugeData.rank → ℕ :=
  ![171159, 90388, 121422, 156527, 50268, 37701, 63307,
    180068, 161306, 119298, 180363, 43070, 57348, 139653,
    151335, 174168, 114342, 131452, 122838, 118708, 55578,
    62658, 118413, 8732, 130331, 148798, 7670, 137588]

/-- The binomial coefficient in the pole-safe Faulhaber decomposition has
exactly the advertised campaign-prime factor. -/
theorem choose_factor (row : Fin gaugeData.rank) :
    (RealFlow.highIndex (data := realGaugeData) row + 1).choose
        (RealFlow.highIndex (data := realGaugeData) row - 2) =
      59 * chooseQuotient row := by
  rw [← Nat.choose_symm (by
    dsimp [RealFlow.highIndex]
    omega)]
  have hdiff :
      RealFlow.highIndex (data := realGaugeData) row + 1 -
          (RealFlow.highIndex (data := realGaugeData) row - 2) = 3 := by
    dsimp [RealFlow.highIndex]
    omega
  rw [hdiff]
  apply Nat.mul_right_cancel (by norm_num : 0 < 3)
  rw [Nat.choose_succ_right_eq, Nat.choose_two_right]
  clear hdiff
  decide +kernel +revert

/-- One finite kernel reduction checks all 28 fourth-order power sums. -/
theorem raw_power_sum (row : Fin gaugeData.rank) :
    (∑ a ∈ Finset.range 59,
      (a : ZMod (59 ^ 4)) ^
        RealFlow.highIndex (data := realGaugeData) row) =
      59 * rawPowerResidue row := by
  decide +kernel +revert

/-- The target Bernoulli denominator is prime to the campaign prime at
every selected row. -/
theorem target_denominator (row : Fin gaugeData.rank) :
    Bernoulli.DenominatorPrimeTo 59
      (bernoulli (RealFlow.highIndex (data := realGaugeData) row)) := by
  apply Bernoulli.bernoulli_denominatorPrimeTo
  · exact
      (even_two.mul_right (row.val + 1)).mul_right 59
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hrow := row.isLt
    dsimp [RealFlow.highIndex, realGaugeData,
      Fermat.Conservation.Credit.RealGauge.RealGaugeData.ofGaugeData,
      gaugeData] at hk hrow
    omega

/-- Away from the exceptional first row, the predecessor Bernoulli
denominator is also prime to the campaign prime. -/
theorem predecessor_denominator
    (row : Fin gaugeData.rank) (hrow : row.val ≠ 0) :
    Bernoulli.DenominatorPrimeTo 59
      (bernoulli (RealFlow.highIndex (data := realGaugeData) row - 2)) := by
  apply Bernoulli.bernoulli_denominatorPrimeTo
  · refine ⟨(row.val + 1) * 59 - 1, ?_⟩
    dsimp [RealFlow.highIndex]
    omega
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hrowLt := row.isLt
    dsimp [RealFlow.highIndex, realGaugeData,
      Fermat.Conservation.Credit.RealGauge.RealGaugeData.ofGaugeData,
      gaugeData] at hk hrowLt
    omega

/-- The predecessor correction is `-1` at the unique pole and zero on
all other rows. -/
theorem predecessor_representation (row : Fin gaugeData.rank) :
    ∃ v : ℚ, Bernoulli.PIntegral 59 v ∧
      (59 : ℚ) *
          bernoulli
            (RealFlow.highIndex (data := realGaugeData) row - 2) =
        (predecessorResidue row : ℚ) + 59 * v := by
  by_cases hrow : row.val = 0
  · have hrowEq :
        row = (⟨0, by norm_num [gaugeData]⟩ :
          Fin gaugeData.rank) :=
      Fin.ext hrow
    subst row
    simpa [RealFlow.highIndex, predecessorResidue] using
      (Bernoulli.prime_mul_exceptional_predecessor_representation
        (p := 59))
  · refine
      ⟨bernoulli
          (RealFlow.highIndex (data := realGaugeData) row - 2),
        Bernoulli.pIntegral_of_denominatorPrimeTo
          (predecessor_denominator row hrow), ?_⟩
    simp [predecessorResidue, hrow]

/-- The correction weights, including their integral error terms. -/
theorem correction_weight_representation
    (row : Fin gaugeData.rank) :
    ∃ z : ℚ, Bernoulli.PIntegral 59 z ∧
      (chooseQuotient row : ℚ) /
          (RealFlow.highIndex (data := realGaugeData) row + 1) =
        (correctionWeight row : ℚ) + 59 * z := by
  refine
    ⟨(weightLiftNumerator row : ℚ) / 3, ?_, ?_⟩
  · exact Bernoulli.pIntegral_div_nat
      (Bernoulli.pIntegral_nat 59 (weightLiftNumerator row))
      (by norm_num) (by norm_num)
  · decide +kernel +revert

/-- The raw residue plus the predecessor correction is the certified
Bernoulli residue modulo the campaign-prime cube. -/
theorem corrected_residue_normalization
    (row : Fin gaugeData.rank) :
    (rawPowerResidue row : ℤ) -
        (59 : ℤ) ^ 2 * predecessorResidue row *
          correctionWeight row =
      (correctedResidue row : ℤ) + (59 : ℤ) ^ 3 * 0 := by
  decide +kernel +revert

theorem correctedResidue_ne_zero (row : Fin gaugeData.rank) :
    correctedResidue row ≠ 0 := by
  decide +kernel +revert

theorem correctedResidue_cubeFree (row : Fin gaugeData.rank) :
    ¬(59 : ℤ) ^ 3 ∣ (correctedResidue row : ℤ) := by
  decide +kernel +revert

/-- Every generated high Bernoulli numerator is cube-free at the campaign
prime.  The proof is one instantiation of the generic corrected Faulhaber
endpoint. -/
theorem highBernoulliNumerator_cubeFree
    (row : Fin gaugeData.rank) :
    ¬(59 : ℤ) ^ 3 ∣
      (bernoulli
        (RealFlow.highIndex (data := realGaugeData) row)).num := by
  apply
    Bernoulli.exceptional_bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 59)
      (n := RealFlow.highIndex (data := realGaugeData) row)
      (c := chooseQuotient row)
      (raw := rawPowerResidue row)
      (residue := correctedResidue row)
      (q := predecessorResidue row)
      (w := correctionWeight row)
      (correctionLift := 0)
  · norm_num
  · dsimp [RealFlow.highIndex]
    omega
  · exact
      (even_two.mul_right (row.val + 1)).mul_right 59
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    dsimp [RealFlow.highIndex] at hk
    omega
  · exact choose_factor row
  · exact raw_power_sum row
  · exact predecessor_representation row
  · exact correction_weight_representation row
  · exact corrected_residue_normalization row
  · exact correctedResidue_ne_zero row
  · exact correctedResidue_cubeFree row
  · exact target_denominator row

end BernoulliCertificate

/-- The generated high-eigenvalue vector passes its prime-cube gate. -/
theorem noBernoulliCubeObstruction59 :
    NoBernoulliCubeObstruction59 := by
  intro row
  exact BernoulliCertificate.highBernoulliNumerator_cubeFree row

/-- The generic certificate record is assembled without accepting a
matrix, an inverse, or an eigenvalue vector. -/
def flowCertificate_of_cubeFree
    (hno : NoBernoulliCubeObstruction59) :
    Fermat.Conservation.Credit.RealFlow.FlowCertificate realGaugeData where
  eigenvalue_cubeFree := hno

/-- The parameter-free certificate consumed by the generic forcing
theorem. -/
def flowCertificate :
    Fermat.Conservation.Credit.RealFlow.FlowCertificate realGaugeData :=
  flowCertificate_of_cubeFree noBernoulliCubeObstruction59

/-! ## Generic L4 and W3 instantiation -/

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- The actual local depth predicate attached to the selected primitive
root. -/
def IsDeeplyRepayable {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (u : NumberField.IsCMField.realUnits K) : Prop :=
  Fermat.Conservation.Credit.Repayment.IsVandiverDeep 59
    ((1 : 𝓞 K) - hζ.toInteger) (u : (𝓞 K)ˣ)

/-- The checked C2 result, packaged as the generic capacity record consumed
by W3.  The ambient ledger is the full real-unit group. -/
noncomputable def capacityData {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.Cycle.CapacityData
      Fermat.FiftyNine.Conservation.Credit.exponentCycle
      (Fermat.FiftyNine.Conservation.Credit.realOrbitNode hζ) where
  ambient := ⊤
  generated_le := le_top
  finite := by
    rw [Subgroup.isFiniteRelIndex_top_iff]
    exact
      (Fermat.FiftyNine.Conservation.CapacityCertificate.capacityCertificate
        hζ).1

/-- Selected-prime spelling of the generic W1 depth law. -/
def DeepFlowLaw59 {ζ : K} (hζ : IsPrimitiveRoot ζ 59) : Prop :=
  Fermat.Conservation.Credit.RealFlow.DeepFlowLaw creditData
    (Fermat.Conservation.Credit.Flow.realCyclotomicOrbitNodeQuotient hζ)
    (IsDeeplyRepayable hζ)

/-- W1's generator-derived flow law instantiated at the campaign prime. -/
theorem deepFlowLaw59 {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    DeepFlowLaw59 hζ := by
  unfold DeepFlowLaw59
  intro u hdeep t raw ht hrelation hprimitive
  exact
    (Fermat.Conservation.Credit.RealFlow.deepFlowLaw_realCyclotomicOrbitNodeQuotient
      hζ creditData)
      u hdeep t raw ht hrelation hprimitive

/-- Evaluation on the intrinsic quotient cycle recovers the existing C2
edge exactly; no selected unit family is duplicated. -/
theorem realGauge_cycle_edge_eq_exponentCycle_edge
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (i : Fin realGaugeData.cycle.rank) :
    realGaugeData.cycle.edge
        (Fermat.Conservation.Credit.Flow.realCyclotomicOrbitNodeQuotient
          hζ) i =
      Fermat.FiftyNine.Conservation.Credit.exponentCycle.edge
        (Fermat.FiftyNine.Conservation.Credit.realOrbitNode hζ) i := by
  simp only [Fermat.Conservation.Credit.Cycle.edge]
  rw [← realGaugeData.mk_nodeLift (i.val + 1),
    ← realGaugeData.mk_nodeLift i.val]
  simp only [realGaugeData,
    Fermat.Conservation.Credit.RealGauge.RealGaugeData.ofGaugeData_nodeLift_eq_cycle_point]
  rfl

/-- W3 itself is pure instantiation: the generic flow/gauge theorem turns
the derived L4 law plus the cube-free certificate into exactly the exponent
forcing consumed by repayment. -/
theorem deepExponentForcing_of_flow {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.Repayment.DeepExponentForcing
      realGaugeData.cycle
      (Fermat.Conservation.Credit.Flow.realCyclotomicOrbitNodeQuotient hζ)
      59 (IsDeeplyRepayable hζ) := by
  exact Fermat.Conservation.Credit.RealFlow.deepExponentForcing creditData
    (Fermat.Conservation.Credit.Flow.realCyclotomicOrbitNodeQuotient hζ)
    (IsDeeplyRepayable hζ)
    flowCertificate (deepFlowLaw59 hζ)

/-- Compatibility form consumed by the already-certified C2 capacity. -/
theorem deepExponentForcing_on_exponentCycle_of_flow {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.Repayment.DeepExponentForcing
      Fermat.FiftyNine.Conservation.Credit.exponentCycle
      (Fermat.FiftyNine.Conservation.Credit.realOrbitNode hζ)
      59 (IsDeeplyRepayable hζ) := by
  intro u hdeep t raw ht hrelation hprimitive
  apply deepExponentForcing_of_flow hζ u hdeep t raw ht
  · rw [hrelation]
    apply Finset.prod_congr rfl
    intro i _
    rw [realGauge_cycle_edge_eq_exponentCycle_edge]
  · exact hprimitive

/-- C3 repayment after the generic L4 comparison.  The group theory, gauge
inversion, and high-eigenvalue arithmetic are all discharged by the generic
core. -/
theorem repayment_of_capacity_and_flow
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    {u : NumberField.IsCMField.realUnits K}
    (hdeep : IsDeeplyRepayable hζ u) :
    Fermat.Conservation.Credit.Repayment.IsRepaid 59 u := by
  exact Fermat.Conservation.Credit.Repayment.repay_of_deep_generated_cycle
    (by norm_num) (capacityData hζ) rfl
    (Fermat.Conservation.Credit.Repayment.realUnits_odd_pow_injective
      59 (by norm_num))
    (IsDeeplyRepayable hζ)
    (deepExponentForcing_on_exponentCycle_of_flow hζ) hdeep

end

end Fermat.FiftyNine.Conservation.Instance
