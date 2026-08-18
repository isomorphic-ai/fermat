/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Spectral contraction of the triangular Kummer remainder

The exact coefficient contraction from triangular factorization is evaluated
at a spectral one-unit.  If the element satisfies `alpha^p = a`, the result
is an exact base product plus an `a`-multiple whose extension-field spectral
norm has improved from `q` to `q²`.
-/
import Fermat.Conservation.PrimeTriangularNormBounds
import Fermat.Conservation.PolynomialSpectralNormBound

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeTriangularSpectralContraction

open PrimeTriangularUnitFactorization
open PrimeTriangularNormBounds
open PolynomialSpectralNormBound

variable {F E : Type*}
variable [NontriviallyNormedField F] [Field E] [Algebra F E]
variable [Algebra.IsAlgebraic F E] [IsUltrametricDist F] [CompleteSpace F]

/-- The exact triangular remainder retains its `q²` coefficient contraction
after evaluation at a spectral one-unit. -/
theorem exists_triangular_remainder_spectralNorm_le_sq
    (f : F[X]) (hf0 : f.coeff 0 = 1)
    (p : ℕ) (hp : 0 < p) (hdeg : f.natDegree < p)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q)
    (alpha : E) (halphaNorm : spectralNorm F E alpha ≤ 1) :
    ∃ g : F[X],
      f = triangularProduct f (p - 1) + X ^ p * g ∧
      spectralNorm F E (aeval alpha g) ≤ q ^ 2 := by
  obtain ⟨g, hg, hgbound⟩ := exists_triangular_remainder_supNorm_le_sq
    f hf0 p hp hdeg q hq0 hq1 hf
  refine ⟨g, hg, ?_⟩
  exact (spectralNorm_aeval_le_supNorm alpha halphaNorm g).trans hgbound

/-- If `alpha^p = a`, evaluation turns the contracted `X^p` remainder into
an exact `a`-multiple in the extension. -/
theorem exists_evaluated_triangular_remainder_spectralNorm_le_sq
    (f : F[X]) (hf0 : f.coeff 0 = 1)
    (p : ℕ) (hp : 0 < p) (hdeg : f.natDegree < p)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q)
    (alpha : E) (a : F) (halpha : alpha ^ p = algebraMap F E a)
    (halphaNorm : spectralNorm F E alpha ≤ 1) :
    ∃ y : E,
      aeval alpha f = aeval alpha (triangularProduct f (p - 1)) +
        algebraMap F E a * y ∧
      spectralNorm F E y ≤ q ^ 2 := by
  obtain ⟨g, hg, hgbound⟩ :=
    exists_triangular_remainder_spectralNorm_le_sq
      f hf0 p hp hdeg q hq0 hq1 hf alpha halphaNorm
  refine ⟨aeval alpha g, ?_, hgbound⟩
  have heval := congrArg (fun h : F[X] => aeval alpha h) hg
  simpa only [map_add, map_mul, map_pow, aeval_X, halpha] using heval

end Fermat.Conservation.PrimeTriangularSpectralContraction
