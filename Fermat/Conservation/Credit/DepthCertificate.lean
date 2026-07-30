/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The second reading of the high-flow certificate

The cube-free high-eigenvalue permit also says that every Bernoulli
correction has prime depth at most two.  Exact depth two additionally asks
that one generated row attain the square layer.  These predicates depend
only on the route-neutral real gauge and its generated eigenvalues.
-/
import Fermat.Conservation.Credit.RealHighFlow

namespace Fermat.Conservation.Credit.RealFlow

/-- Every generated high eigenvalue has prime depth at most two. -/
def DepthAtMostTwo {p : ℕ} (data : RealGauge.RealGaugeData p) : Prop :=
  ∀ row, ¬(p : ℤ) ^ 3 ∣ highEigenvalue (data := data) row

/-- The generated high eigenvalues have depth at most two, with the square
layer attained by at least one row. -/
structure DepthTwoCertificate {p : ℕ}
    (data : RealGauge.RealGaugeData p) : Prop where
  atMostTwo : DepthAtMostTwo data
  square_attained :
    ∃ row, (p : ℤ) ^ 2 ∣ highEigenvalue (data := data) row

/-- The usual high-flow certificate supplies the at-most-two half of the
depth reading without any additional arithmetic. -/
theorem FlowCertificate.depthAtMostTwo {p : ℕ}
    {data : RealGauge.RealGaugeData p}
    (certificate : FlowCertificate data) :
    DepthAtMostTwo data :=
  certificate.eigenvalue_cubeFree

/-- Add one square-divisible generated row to the existing flow certificate
to obtain the exact depth-two reading. -/
def DepthTwoCertificate.ofFlowCertificate {p : ℕ}
    {data : RealGauge.RealGaugeData p}
    (certificate : FlowCertificate data)
    (square_attained :
      ∃ row, (p : ℤ) ^ 2 ∣ highEigenvalue (data := data) row) :
    DepthTwoCertificate data where
  atMostTwo := certificate.depthAtMostTwo
  square_attained := square_attained

end Fermat.Conservation.Credit.RealFlow
