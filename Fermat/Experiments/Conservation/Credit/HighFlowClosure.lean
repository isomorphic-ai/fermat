/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# W1/W3: generated relation to integral high-flow vanishing

The corrected polynomial relation is reduced through the nonlinear Euler
jet flow, identified with the generator-derived logarithmic rate, and then
converted into the integral prime-cube congruences consumed by the generic
real forcing theorem.

The construction is uniform over every odd prime and contains no
conductor-specific arithmetic.
-/
import Fermat.Experiments.Conservation.Credit.RateReductionFlow
import Fermat.Experiments.Conservation.Credit.RelationEvaluationFlow
import Fermat.Experiments.Conservation.Credit.RealForcing

open scoped NumberField

namespace Fermat.Conservation.Credit.HighFlowClosure

namespace GeneratedRelation

/-- A scalar-normalized moment-ready generated relation forces every
integral high-flow coordinate to vanish to prime-cube depth. -/
theorem highFlowVanishes_of_moment_ready_generated_relation
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (s : ℤ) (H B : Polynomial ℤ)
    (hs : (p : ℤ) ^ 2 ∣ s - 1)
    (hfactor :
      (RealFlow.relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C s * RealFlow.relationDenominator data raw =
        Polynomial.cyclotomic p ℤ * B)
    (heval :
      (p : ℤ) ^ 2 ∣
        ((RealFlow.relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C s * RealFlow.relationDenominator data raw).eval 1) :
    RealFlow.HighFlowVanishes data raw := by
  intro row
  let M : ℕ := 2 * (row.val + 1)
  let N : ℕ := RealFlow.highIndex (data := data) row
  have hselected :=
    RateFlow.Composition.rateJet_selected_prime_integral_and_num_sq
      data raw s H B hs hfactor heval
      (show 0 < M from RealFlow.rowMultiplier_pos row)
      (show M < p - 1 from RealFlow.rowMultiplier_lt_prime_pred row)
  have hindex : p * M = N := by
    simp [M, N, RealFlow.highIndex, Nat.mul_comm]
  let rate : ℚ :=
    RateFlow.GeneratedRelation.rateJet data raw (N - 1)
  have hden :
      Bernoulli.DenominatorPrimeTo p rate := by
    simpa only [rate, hindex] using hselected.1
  have hsquare : (p : ℤ) ^ 2 ∣ rate.num := by
    simpa only [rate, hindex] using hselected.2
  have hfour : 4 ≤ N := by
    dsimp [N, RealFlow.highIndex]
    calc
      4 = (2 * 1) * 2 := by norm_num
      _ ≤ (2 * (row.val + 1)) * p :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 (Nat.succ_pos row.val))
          data.prime.two_le
  have hNpos : 0 < N := by omega
  have hpredPos : 0 < N - 1 := by omega
  have hpN : p ∣ N := by
    rw [← hindex]
    exact dvd_mul_right p M
  have hrate :
      rate =
        (2 * (p - 1 : ℚ)) *
          (RealFlow.exactHighEdgeCoefficient data raw row : ℚ) *
            (_root_.bernoulli N / (N : ℚ)) := by
    calc
      rate =
          Flow.formalDerivativeAtZero (N - 1)
            (RateFlow.GeneratedRelation.fullRelationRate data raw) := by
            rfl
      _ = Flow.formalDerivativeAtZero (N - 1)
          (LogRate.Relation.generatedRelationRate data raw) :=
        RateFlow.GeneratedRelation.formalDerivativeAtZero_fullRelationRate_eq_generatedRelationRate
          data raw hpredPos
      _ = (2 * (p - 1 : ℚ)) *
          ((RealFlow.exactHighEdgeCoefficient data raw row : ℚ) *
            (_root_.bernoulli N / (N : ℚ))) := by
        simpa only [N] using
          LogRate.Relation.formalDerivativeAtZero_generatedRelationRate_high
            data raw row
      _ = _ := by ring
  have hcubic :=
    LogRate.Arithmetic.prime_cube_dvd_exact_of_rate_numerator_sq
      data.prime data.odd hNpos hpN hrate hden hsquare
  simpa only [RealFlow.highEigenvalue, N] using hcubic

end GeneratedRelation

end Fermat.Conservation.Credit.HighFlowClosure

namespace Fermat.Conservation.Credit.RealFlow

open NumberField

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- A deep relation between a generated real cyclotomic unit and the raw
quotient-cycle edge product forces integral high-flow vanishing. -/
theorem highFlowVanishes_of_deepRelation
    (data : RealGauge.RealGaugeData p)
    (u : NumberField.IsCMField.realUnits K)
    (t : ℕ) (raw : Fin data.rank → ℤ)
    (hdeep :
      Repayment.IsVandiverDeep p
        ((1 : 𝓞 K) - hζ.toInteger)
        (u : (𝓞 K)ˣ))
    (hrelation : u ^ t = rawEdgeProduct hζ data raw) :
    HighFlowVanishes data raw := by
  obtain ⟨c, H, B, hs, hfactor, heval⟩ :=
    exists_moment_ready_relation_of_vandiverDeep
      hζ data u t raw hdeep hrelation
  exact
    HighFlowClosure.GeneratedRelation.highFlowVanishes_of_moment_ready_generated_relation
      data raw (c ^ (p * t * (p - 1))) H B
      hs hfactor heval

/-- The generated real cyclotomic quotient node satisfies the generic W1
deep-flow law consumed by W3. -/
theorem deepFlowLaw_realCyclotomicOrbitNodeQuotient
    (data : CreditData p) :
    DeepFlowLaw data
      (Flow.realCyclotomicOrbitNodeQuotient hζ)
      (fun u : NumberField.IsCMField.realUnits K ↦
        Repayment.IsVandiverDeep p
          ((1 : 𝓞 K) - hζ.toInteger)
          (u : (𝓞 K)ˣ)) := by
  intro u hdeep t raw _ht hrelation _hprimitive
  apply highFlowVanishes_of_deepRelation
    hζ data.gauge u t raw hdeep
  simpa only [rawEdgeProduct] using hrelation

end Fermat.Conservation.Credit.RealFlow
