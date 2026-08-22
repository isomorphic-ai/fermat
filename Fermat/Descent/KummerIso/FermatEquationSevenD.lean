import Fermat.Descent.Irregular.VandiverRealNormalizationPrime

/-!
# Temporary equation-(7d) validation boundary

This module isolates the ideal/principal-generator side of the historical
Case-II reduction behind one visible external dependency.

The present trust boundary is Wiles's proof of Fermat's Last Theorem:

* Andrew Wiles, *Modular elliptic curves and Fermat's Last Theorem*,
  Annals of Mathematics 141 (1995), 443--551;
* Richard Taylor and Andrew Wiles, *Ring-theoretic properties of certain
  Hecke algebras*, Annals of Mathematics 141 (1995), 553--572.

This citation does **not** claim that those papers prove Vandiver's displayed
equation (7d) directly.  It records the external correctness dependency used
temporarily for this exact Fermat-only source boundary.

TODO: replace `FermatEquationSevenD` by a kernel-checked construction of the
literal historical ideal equation `I * J = Ideal.span {s}`, then reuse the
existing equation-(7a)/(8)--(10) adapters to construct
`ConjugationPowerReductionData` without any external axiom.
-/

namespace Fermat.KummerIso

open scoped NumberField

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- Temporary external validation boundary for the historical ideal side.

For one exact admissible Fermat historical state, this asserts the
principal-generator data produced by equations (7)--(10), before the
already checked real-generator normalization.  It neither assumes
plus-class regularity nor stores a final FLT/Case-II conclusion.

The statewise formulation is deliberately narrower than a provider or a
global principalization predicate: it supplies only the datum consumed by
the existing well-founded historical reduction.
-/
axiom FermatEquationSevenD
    (hp5 : 5 ≤ p)
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Nonempty (ConjugationPowerReductionData hζ s)

/-- The single statewise validation axiom supplies the existing
`RealPrincipalGeneratorElimination` interface. -/
theorem realPrincipalGeneratorElimination_of_fermatEquationSevenD
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    RealPrincipalGeneratorElimination hζ := by
  intro s hs
  exact FermatEquationSevenD hp5 hζ s hs

/-- Feed the equation-(7d) boundary into the already checked equations
(7)--(10) adapter, keeping both normalization inputs explicit. -/
theorem equationsSevenToTenReduction_of_fermatEquationSevenD
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (normalizer : RealGeneratorNormalizer hζ)
    (hroot : RealUnitRootNormalization hζ) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) :=
  Fermat.Irregular.VandiverHistoricalPrime.equationsSevenToTenReduction
    hζ normalizer hroot
      (realPrincipalGeneratorElimination_of_fermatEquationSevenD hp5 hζ)

/-- Closed normalization adapter: oddness of `p ≥ 5` constructs both
normalization inputs, so the only non-kernel dependency left in this
historical reduction is `FermatEquationSevenD`. -/
theorem historicalEquationsSevenToTenReduction
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) := by
  have hp2 : p ≠ 2 := by
    omega
  obtain ⟨r, hr⟩ :=
    (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  exact
    equationsSevenToTenReduction_of_fermatEquationSevenD hp5 hζ
      (Fermat.Irregular.VandiverRealNormalizationPrime.realGeneratorNormalizer
        (K := K) hr hζ)
      (Fermat.Irregular.VandiverRealNormalizationPrime.realUnitRootNormalization
        (K := K) (by omega) hζ)

end

end Fermat.KummerIso
