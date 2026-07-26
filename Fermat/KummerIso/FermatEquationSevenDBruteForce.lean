import Fermat.Irregular.CircularUnitResidues
import Fermat.Irregular.CyclotomicSinnottBridgePrime
import Fermat.Irregular.VandiverHistoricalAssemblyPrime
import Fermat.GenericIrregular.SecondCase
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

/-- Polymorphic fixed-prime certificate data that can be instantiated in the
canonical cyclotomic field chosen by the closed FLT wrapper below.

The provider shape lets a fixed-exponent module keep its certificate
construction field-generic. The wrapper uses only its `unitSystem` and
`channels` fields; equation (7d) continues to come from the independent
residue certificate. -/
abbrev FixedSecondCaseCertificateProvider
    (p N : ℕ) [Fact p.Prime] :=
  ∀ {L : Type} [Field L] [NumberField L]
    [NumberField.IsCMField L]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L}, IsPrimitiveRoot ζ p →
      Fermat.GenericIrregular.SecondCase.FixedSecondCaseCertificate
        L p N

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

/-- End-to-end Case II with both historical inputs supplied by finite
certificates.

The residue certificate gives the equations-(7)--(10) reduction, while the
unit system and axis-8 channels give the Kummer unit-power conclusion. Thus
this route uses neither `FermatEquationSevenD` nor
`BernoulliValidationBound`. -/
theorem secondCaseExcluded_of_residueCertificate_of_unitSystem_of_channels
    {N : ℕ}
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (system :
      Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (channels :
      Fermat.GenericIrregular.ChannelCertificate.FixedChannelCertificate
        p N) :
    Fermat.SecondCaseExcluded p :=
  Fermat.KummerIso.secondCaseExcluded_of_historicalReduction_of_unitSystem_of_channels
    hp5 hζ
    (historicalEquationsSevenToTenReduction_of_residueCertificate
      hp5 C hdet hζ)
    system channels

/-- End-to-end FLT from a residue certificate, a finite unit system, and
axis-8 channels. The only project axiom remaining in this route is successful
termination of the generic Sophie--Germain search used for Case I. -/
theorem holdsAt_of_residueCertificate_of_unitSystem_of_channels
    {N : ℕ}
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (system :
      Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (channels :
      Fermat.GenericIrregular.ChannelCertificate.FixedChannelCertificate
        p N) :
    Fermat.HoldsAt p :=
  Fermat.holdsAt_of_sophieGermainSearch_of_secondCaseExcluded
    (secondCaseExcluded_of_residueCertificate_of_unitSystem_of_channels
      hp5 C hdet hζ system channels)

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

/-- End-to-end FLT for a fixed prime using executable certificate searches
for both cases.

The circular-unit residue certificate removes `FermatEquationSevenD` from
Case II. The generic Sophie--Germain search handles Case I. Consequently,
the only project axioms are `BernoulliValidationBound` and successful
termination of the Sophie--Germain search. -/
theorem holdsAt_of_residueCertificate
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Fermat.HoldsAt p :=
  Fermat.holdsAt_of_sophieGermainSearch_of_secondCaseExcluded
    (secondCaseExcluded_of_residueCertificate
      hp5 C hdet hζ)

/-- Closed end-to-end FLT from a finite residue certificate.

The preceding theorem is useful inside an already chosen cyclotomic field.
For fixed-exponent regressions, however, the field and primitive root are
purely canonical infrastructure. This wrapper chooses the standard
cyclotomic field once and discharges that infrastructure uniformly, leaving
only the finite certificate and its determinant proof as inputs. -/
theorem holdsAt_of_residueCertificate_canonical
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0) :
    Fermat.HoldsAt p := by
  letI : NeZero p :=
    ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI :
      IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : NumberField.IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.IsCMField (p := p) (CyclotomicField p ℚ)
      (by omega)
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField p ℚ)
      (Set.mem_singleton p) (Fact.out : p.Prime).ne_zero
  exact
    holdsAt_of_residueCertificate
      (K := CyclotomicField p ℚ) hp5 C hdet hζ

/-- Closed BVB-free FLT from a residue certificate and a field-generic fixed
second-case certificate provider.

Only the provider's `unitSystem` and `channels` fields are consumed here. Its
plus-class field is intentionally ignored because the independent residue
certificate supplies the historical equation-(7d) reduction. -/
theorem holdsAt_of_residueCertificate_canonical_of_fixedCertificate
    {N : ℕ}
    (hp5 : 5 ≤ p)
    (C : Certificate p q)
    (hdet : C.matrix.det ≠ 0)
    (provider : FixedSecondCaseCertificateProvider p N) :
    Fermat.HoldsAt p := by
  letI : NeZero p :=
    ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI :
      IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : NumberField.IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.IsCMField (p := p) (CyclotomicField p ℚ)
      (by omega)
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField p ℚ)
      (Set.mem_singleton p) (Fact.out : p.Prime).ne_zero
  let fixed := provider hζ
  exact
    holdsAt_of_residueCertificate_of_unitSystem_of_channels
      (K := CyclotomicField p ℚ) hp5 C hdet hζ
      fixed.unitSystem fixed.channels

end

end Fermat.KummerIso.FermatEquationSevenDBruteForce
