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

/-- The checked irregular row attains the square layer of the generated
high-eigenvalue family.  This is the row-21 specialization of the retained
28-row exact-depth profile. -/
theorem highEigenvalue_square_attained :
    ∃ row : Fin realGaugeData.rank,
      (59 : ℤ) ^ 2 ∣
        RealFlow.highEigenvalue (data := realGaugeData) row := by
  let row : Fin gaugeData.rank :=
    ⟨21, by norm_num [gaugeData]⟩
  refine ⟨row, ?_⟩
  apply (padicValInt_dvd_iff 2 _).2
  right
  change
    2 ≤ padicValInt 59
      (bernoulli
        (RealFlow.highIndex (data := realGaugeData) row)).num
  rw [BernoulliCertificate.highBernoulliNumerator_padicVal]
  decide +kernel

/-- The current selected data has exact Bernoulli correction depth two,
retaining its complete channel payload. -/
noncomputable def depthTwoCertificate :
    RealFlow.DepthTwoCertificate realGaugeData :=
  RealFlow.DepthTwoCertificate.ofFlowCertificate
    flowCertificate highEigenvalue_square_attained

end Fermat.FiftyNine.Conservation.DepthCertificate
