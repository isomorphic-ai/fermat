/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Exact depth of the selected high-flow certificate

The checked pole-safe Faulhaber table already gives every generated
high-eigenvalue depth at most two.  Its irregular row has corrected residue
equal to a nonzero multiple of the prime square, so that row attains depth
two exactly.
-/
import Fermat.Conservation.Credit.DepthCertificate
import Fermat.FiftyNine.Conservation.Instance

namespace Fermat.FiftyNine.Conservation.DepthCertificate

open Fermat.Conservation.Credit
open Fermat.FiftyNine.Conservation.Instance

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- The generated-flow row carrying the unique conductor-59 funded layer. -/
noncomputable def fundedRow : Fin realGaugeData.rank :=
  creditData.irregularRow

theorem fundedRow_depth :
    BernoulliCertificate.channelCertificate.depth fundedRow = 2 := by
  decide +kernel

theorem fundedRow_lift :
    BernoulliCertificate.channelCertificate.liftChannel fundedRow = 1 := by
  rfl

theorem fundedRow_coupling :
    BernoulliCertificate.channelCertificate.couplingChannel fundedRow = 1 := by
  decide +kernel

theorem fundedRow_surplus :
    BernoulliCertificate.channelCertificate.surplus fundedRow = 0 := by
  decide +kernel

theorem fundedRow_accountedFlow_spends_one :
    (BernoulliCertificate.accountedFlowTransfer fundedRow).spent.2 = 1 := by
  simp [BernoulliCertificate.accountedFlowTransfer,
    RealFlow.BernoulliChannelCertificate.accountedChannelTransfer,
    fundedRow_coupling]

/-- Row 21 reaches the square layer through the same accounted coupling
transaction used by the selected forcing chain. -/
theorem highEigenvalue_square_attained_at_irregularRow :
    (59 : ℤ) ^ 2 ∣
      RealFlow.highEigenvalue (data := realGaugeData) fundedRow := by
  apply (padicValInt_dvd_iff 2 _).2
  right
  change
    2 ≤ padicValInt 59
      (bernoulli
        (RealFlow.highIndex (data := realGaugeData) fundedRow)).num
  rw [BernoulliCertificate.highBernoulliNumerator_padicVal]
  have hcredit :=
    BernoulliCertificate.accountedFlow_credit_decomposition fundedRow
  have hspent := fundedRow_accountedFlow_spends_one
  change BernoulliCertificate.couplingChannel fundedRow =
    BernoulliCertificate.surplus fundedRow +
      (BernoulliCertificate.accountedFlowTransfer fundedRow).spent.2 at hcredit
  change 2 ≤ 1 + BernoulliCertificate.couplingChannel fundedRow
  omega

/-- The checked irregular row attains the square layer of the generated
high-eigenvalue family.  This is the row-21 specialization of the retained
28-row exact-depth profile. -/
theorem highEigenvalue_square_attained :
    ∃ row : Fin realGaugeData.rank,
      (59 : ℤ) ^ 2 ∣
        RealFlow.highEigenvalue (data := realGaugeData) row := by
  exact ⟨fundedRow, highEigenvalue_square_attained_at_irregularRow⟩

/-- The irregular table debit and a supplied funded grade-one repayment have
the same natural-coordinate endpoints.  The conversion counter starts at
the structural lift already present in the Bernoulli account. -/
theorem fundedRow_maps_to_repayLayer
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (state : Repayment.C (NumberField.IsCMField.realUnits K)
      RegularClosure59 (RepaymentFunded59 hζ) 1) :
    let flowTransfer := BernoulliCertificate.accountedFlowTransfer fundedRow
    let repayTransfer := Repayment.repay_layer_transfer
      (repayOne_of_capacity_and_flow hζ) state 1
    flowTransfer.before.stock.2 = repayTransfer.before.stock ∧
      flowTransfer.before.credit.2 = repayTransfer.before.credit ∧
      flowTransfer.before.converted.2 = repayTransfer.before.converted ∧
      flowTransfer.before.total.2 = repayTransfer.before.total ∧
      flowTransfer.after.stock.2 = repayTransfer.after.stock ∧
      flowTransfer.after.credit.2 = repayTransfer.after.credit ∧
      flowTransfer.after.converted.2 = repayTransfer.after.converted ∧
      flowTransfer.after.total.2 = repayTransfer.after.total ∧
      flowTransfer.spent.2 = repayTransfer.spent := by
  simp [BernoulliCertificate.accountedFlowTransfer,
    RealFlow.BernoulliChannelCertificate.accountedChannelTransfer,
    RealFlow.BernoulliChannelCertificate.accountedChannelBeforeLedger,
    RealFlow.BernoulliChannelCertificate.accountedChannelAfterLedger,
    fundedRow_depth, fundedRow_lift, fundedRow_coupling, fundedRow_surplus,
    Repayment.repay_layer_transfer]

/-- The current selected data has exact Bernoulli correction depth two,
retaining its complete channel payload. -/
noncomputable def depthTwoCertificate :
    RealFlow.DepthTwoCertificate realGaugeData :=
  RealFlow.DepthTwoCertificate.ofFlowCertificate
    flowCertificate highEigenvalue_square_attained

end Fermat.FiftyNine.Conservation.DepthCertificate
