import Fermat.Irregular.CircularUnitResidues
import Fermat.Irregular.CyclotomicSinnottBridgePrime
import Fermat.Irregular.VandiverHistoricalAssemblyPrime
import Fermat.KummerIso.ValidatedSecondCase

set_option maxRecDepth 50000

/-!
# Brute-force replacement for equation (7d)

This module does not use the temporary
`FermatEquationSevenD` axiom.  It connects the existing finite-field
circular-unit residue certificate directly to the already checked
prime-generic historical assembly.

For a fixed prime `p`, the data left to brute-force are:

* an auxiliary prime `q`;
* a `CircularUnitResidues.Certificate p q`; and
* a proof that the certificate matrix has nonzero determinant modulo `p`.

All subsequent steps -- the Sinnott--Kummer plus-class calculation,
equations (7a), (7d), and (8)--(10), and construction of
`ConjugationPowerReductionData` -- are kernel checked.
-/

namespace Fermat.KummerIso.FermatEquationSevenDBruteForce

open scoped NumberField

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CyclotomicSinnottBridgePrime
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.TakagiHistoricalPrime
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- A finite nonsingular circular-unit residue certificate proves the exact
plus-class nondivisibility used by the historical equation-(7d) route. -/
theorem plusClassNondivisibility_of_residueCertificate
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    PlusClassNondivisibility K p := by
  letI : Fact (2 < p) := ⟨by omega⟩
  have hindex :
      ¬p ∣ realUnitRelIndex
        (circularUnitFamily hζ C.hp2) := by
    simpa only [realUnitRelIndex] using
      C.not_dvd_circularUnitFamily_real_index hζ hdet
  change ¬p ∣
    NumberField.classNumber (NumberField.maximalRealSubfield K)
  rw [← circularUnit_realIndex_eq_classNumber
    (p := p) (K := K) hζ]
  exact hindex

/-- The same finite certificate constructs Vandiver's literal equation
(7d) for the canonical historical conjugate ideal pair. -/
theorem exists_literalEquationSevenD_of_residueCertificate
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    let d : PreparedHistoricalEquationData hζ :=
      preparedHistoricalEquationData hp5 hζ s hs
    ∃ t : 𝓞 K,
      d.plusIdeal * d.minusIdeal = Ideal.span {t} := by
  let d : PreparedHistoricalEquationData hζ :=
    preparedHistoricalEquationData hp5 hζ s hs
  change ∃ t : 𝓞 K,
    d.plusIdeal * d.minusIdeal = Ideal.span {t}
  exact
    d.exists_equationSevenD hζ
      (plusClassNondivisibility_of_residueCertificate
        hp5 C hdet hζ)

/-- The nearest existing generic construction already produces the complete
equations-(7)--(10) datum from plus-class nondivisibility.  This theorem
records the exact compiler-green boundary before inserting finite residue
data. -/
theorem conjugationPowerReductionData_of_plusClass
    (hp5 : 5 ≤ p)
    (hplus : PlusClassNondivisibility K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Nonempty (ConjugationPowerReductionData hζ s) := by
  exact
    Fermat.Irregular.VandiverHistoricalAssemblyPrime.realPrincipalGeneratorElimination_of_plusClass
      hp5 hζ hplus s hs

/-- Brute-force replacement for the temporary equation-(7d) seam.

The theorem has the same conclusion as `FermatEquationSevenD`, but its only
extra inputs are finite and executable at a fixed prime. -/
theorem conjugationPowerReductionData_of_residueCertificate
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Nonempty (ConjugationPowerReductionData hζ s) := by
  exact
    conjugationPowerReductionData_of_plusClass hp5
      (plusClassNondivisibility_of_residueCertificate
        hp5 C hdet hζ)
      hζ s hs

/-- A finite residue certificate replaces `FermatEquationSevenD` in the
complete historical equations-(7)--(10) reduction. -/
theorem historicalEquationsSevenToTenReduction_of_residueCertificate
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    EquationsSevenToTenReduction hζ
      (RealSourceAdmissible hζ) := by
  have hp2 : p ≠ 2 := by
    omega
  obtain ⟨r, hr⟩ :=
    (Fact.out : p.Prime).odd_of_ne_two hp2
  exact
    Fermat.Irregular.VandiverHistoricalPrime.equationsSevenToTenReduction
      hζ
      (Fermat.Irregular.VandiverRealNormalizationPrime.realGeneratorNormalizer
        (K := K) hr hζ)
      (Fermat.Irregular.VandiverRealNormalizationPrime.realUnitRootNormalization
        (K := K) (by omega) hζ)
      (fun s hs ↦
        conjugationPowerReductionData_of_residueCertificate
          hp5 C hdet hζ s hs)

/-- End-to-end Case II for any fixed prime carrying an executable
circular-unit residue certificate.

Unlike `secondCaseExcluded_of_two_validation_seams`, this theorem does not
use `FermatEquationSevenD`; its only project axiom is the temporary
`BernoulliValidationBound`. -/
theorem secondCaseExcluded_of_residueCertificate
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Fermat.SecondCaseExcluded p :=
  Fermat.KummerIso.secondCaseExcluded_of_historicalReduction
    hp5 hζ
    (historicalEquationsSevenToTenReduction_of_residueCertificate
      hp5 C hdet hζ)

end

end Fermat.KummerIso.FermatEquationSevenDBruteForce
