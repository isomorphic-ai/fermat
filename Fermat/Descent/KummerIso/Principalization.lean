import Fermat.Descent.Irregular.TakagiHistoricalPrime
import Fermat.Descent.Irregular.VandiverHistoricalAssemblyPrime

/-!
# Principalizing the selected Fermat ideal quotients

The regular proof asks globally for every quotient of allocated ideal roots
to be principal.  Its weighted equation actually selects only two roots.
This file gives pointwise adapters for such selected quotients and records
the stronger source-faithful result already available for Vandiver's
historical selections.

There are again two distinct interfaces.

* `relevantIdealQuotient_isPrincipal_of_primaryFactor` is a direct adapter:
  a selected allocated root whose literal factor is Kummer-primary is
  principalized by `VandiverLemmaOne.LemmaOne`; a separately principal
  distinguished residual ideal then gives the desired quotient.
* The historical construction does not claim that an individual linear
  factor is primary.  It proves that the conjugate recombination is primary,
  uses Takagi--Furtwängler reflection and `p ∤ h⁺`, and then extracts the
  selected factor generator.  The theorems in the second half reuse that
  checked route and principalize the exact selected quotient at `ζ`, and
  the transported selection at `ζ²`.

No theorem below assumes the global predicate
`RelevantIdealQuotientsPrincipal`.
-/

namespace Fermat.KummerIso.Principalization

open scoped NumberField nonZeroDivisors

open Polynomial
open Fermat.Irregular
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverHistoricalStatePrime
open Fermat.Irregular.VandiverHistoricalEquationEightAPrime
open Fermat.Irregular.VandiverEquationEightAFactorizationPrime
open Fermat.Irregular.VandiverEquationTenPrime
open Fermat.Irregular.VandiverLemmaOne
open Fermat.Irregular.TakagiHistoricalPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-! ## Pointwise adapters -/

omit [NumberField.IsCMField K] in
/-- A quotient of two individually principal integral ideals is principal
as a fractional ideal. -/
theorem selectedIdealQuotient_isPrincipal_of_ideals
    {I J : Ideal (𝓞 K)}
    (hI : Submodule.IsPrincipal (I : Ideal (𝓞 K)))
    (hJ : Submodule.IsPrincipal (J : Ideal (𝓞 K))) :
    Submodule.IsPrincipal
      ((((I : FractionalIdeal (𝓞 K)⁰ K) /
          (J : FractionalIdeal (𝓞 K)⁰ K)) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  apply fractionalIdeal_isPrincipal_div
  · exact
      (IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K).mpr hI
  · exact
      (IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K).mpr hJ

omit [NumberField.IsCMField K] in
/-- Pointwise primary principalization for one quotient selected from the
regular factor-allocation construction.

The two remaining mathematical inputs are explicit:

* the literal selected factor is Kummer-primary; and
* the distinguished residual ideal has already been principalized.

The `p`-power identity for the selected numerator is not assumed: it is the
existing factor-allocation theorem
`linearFactorQuotient_span_eq_factorRoot_pow`. -/
theorem relevantIdealQuotient_isPrincipal_of_primaryFactor
    (hp2 : p ≠ 2)
    (hlemma : LemmaOne K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (hxy : IsCoprime x y)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hprimary :
      IsKummerPrimary hζ (div_zeta_sub_one hp2 hζ e η))
    (hresidual :
      Submodule.IsPrincipal
        (a_eta_zero_dvd_p_pow hp2 hζ e hy : Ideal (𝓞 K))) :
    Submodule.IsPrincipal
      (((root_div_zeta_sub_one_dvd_gcd hp2 hζ e hy η /
          a_eta_zero_dvd_p_pow hp2 hζ e hy :
            FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K)) := by
  have hpow :
      root_div_zeta_sub_one_dvd_gcd hp2 hζ e hy η ^ p =
        Ideal.span {div_zeta_sub_one hp2 hζ e η} :=
    (linearFactorQuotient_span_eq_factorRoot_pow
      hp2 hζ e hy hxy η).symm
  have hselected :
      Submodule.IsPrincipal
        (root_div_zeta_sub_one_dvd_gcd hp2 hζ e hy η :
          Ideal (𝓞 K)) :=
    hlemma hζ hprimary hpow
  exact selectedIdealQuotient_isPrincipal_of_ideals
    hselected hresidual

/-! ## The checked historical selections -/

/-- The complete historical principal-generator elimination, re-exported
at the `KummerIso` repair boundary.

The implementation is the checked generic assembly of the primary
conjugate-pair Takagi step and the real equation-(8a) step.  The only global
input is the explicitly displayed nondivisibility `p ∤ h⁺`. -/
theorem realPrincipalGeneratorElimination_of_plusClass
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
  (hplus : PlusClassNondivisibility K p) :
    RealPrincipalGeneratorElimination hζ :=
  Fermat.Irregular.VandiverHistoricalAssemblyPrime.realPrincipalGeneratorElimination_of_plusClass
    hp5 hζ hplus

/-- The canonical prepared conjugate pair principalizes its selected
`ζ`-factor from the single plus-class nondivisibility input.  Kummer
primarity and the Takagi reflection argument are fields/theorems upstream,
not assumptions added here. -/
theorem preparedPlusIdeal_isPrincipal_of_plusClass
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp5 : 5 ≤ p)
    (hplus : PlusClassNondivisibility K p)
    (d : PreparedHistoricalEquationData hζ) :
    Submodule.IsPrincipal (d.plusIdeal : Ideal (𝓞 K)) := by
  obtain ⟨ρ, η, hρ, -⟩ :=
    d.exists_equationEight hζ hp5 hplus
  rw [hρ]
  infer_instance

/-- The exact allocated factor ideal at `ζ` is principal in every
admissible historical state once `p ∤ h⁺`. -/
theorem historicalZetaFactorIdeal_isPrincipal_of_plusClass
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
      (historicalZetaFactorIdeal (by omega : p ≠ 2) hζ s :
        Ideal (𝓞 K)) := by
  let d : PreparedHistoricalEquationData hζ :=
    preparedHistoricalEquationData hp5 hζ s hs
  change Submodule.IsPrincipal (d.plusIdeal : Ideal (𝓞 K))
  exact preparedPlusIdeal_isPrincipal_of_plusClass hζ hp5 hplus d

/-- The distinguished residual ideal at the root `1` is principal from the
same plus-class input.  This is the real equation-(8a) branch, separate from
the primary conjugate-pair branch. -/
theorem historicalResidualIdeal_isPrincipal_of_plusClass
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
      (historicalEquationEightAIdeal (by omega : p ≠ 2) hζ s :
        Ideal (𝓞 K)) := by
  obtain ⟨r, hr⟩ :=
    (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  obtain ⟨ρ, η, j, -, hρ, -, -⟩ :=
    exists_historicalEquationEightA
      hplus hp5 (coprime_two_prime hp5) hr hζ s hs
  rw [hρ]
  infer_instance

/-- The exact historical quotient selected at `ζ`, divided by the
distinguished residual ideal at `1`.  Unfolding the definitions shows that
this is the corresponding
`root_div_zeta_sub_one_dvd_gcd / a_eta_zero_dvd_p_pow` quotient from the
regular factor-allocation API. -/
noncomputable def historicalSelectedQuotient
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (historicalZetaFactorIdeal hp2 hζ s :
      FractionalIdeal (𝓞 K)⁰ K) /
    (historicalEquationEightAIdeal hp2 hζ s :
      FractionalIdeal (𝓞 K)⁰ K)

/-- Historical Takagi principalization closes the exact selected quotient
at `ζ`; no global all-roots principalization hypothesis is used. -/
theorem historicalSelectedQuotient_isPrincipal_of_plusClass
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
      (historicalSelectedQuotient (by omega : p ≠ 2) hζ s :
        Submodule (𝓞 K) K) := by
  unfold historicalSelectedQuotient
  exact selectedIdealQuotient_isPrincipal_of_ideals
    (historicalZetaFactorIdeal_isPrincipal_of_plusClass
      hp5 hζ hplus s hs)
    (historicalResidualIdeal_isPrincipal_of_plusClass
      hp5 hζ hplus s hs)

/-- The second historical selection, obtained by transporting the same
state to the primitive root `ζ²`.  This is the source-faithful counterpart
of selecting the second adjacent root; it does not assert definitional
equality with the independently chosen regular-induction representatives. -/
noncomputable def historicalSelectedQuotientAtTwo
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ) :
    FractionalIdeal (𝓞 K)⁰ K :=
  historicalSelectedQuotient
    (by omega : p ≠ 2)
    (hζ.pow_of_coprime 2 (coprime_two_prime hp5))
    (historicalStateAtTwo hp5 hζ s)

/-- The transported `ζ²` selection is principal from the same plus-class
input, with no second class-group hypothesis. -/
theorem historicalSelectedQuotientAtTwo_isPrincipal_of_plusClass
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
      (historicalSelectedQuotientAtTwo hp5 hζ s :
        Submodule (𝓞 K) K) := by
  exact
    historicalSelectedQuotient_isPrincipal_of_plusClass
      hp5
      (hζ.pow_of_coprime 2 (coprime_two_prime hp5))
      hplus
      (historicalStateAtTwo hp5 hζ s)
      (historicalStateAtTwo_admissible hp5 hζ s hs)

/-- Both historical quotients actually consumed by the prepared weighted
reduction are principal from one plus-class certificate. -/
theorem historicalSelectedQuotientPair_isPrincipal_of_plusClass
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
        (historicalSelectedQuotient (by omega : p ≠ 2) hζ s :
          Submodule (𝓞 K) K) ∧
      Submodule.IsPrincipal
        (historicalSelectedQuotientAtTwo hp5 hζ s :
          Submodule (𝓞 K) K) :=
  ⟨historicalSelectedQuotient_isPrincipal_of_plusClass
      hp5 hζ hplus s hs,
    historicalSelectedQuotientAtTwo_isPrincipal_of_plusClass
      hp5 hζ hplus s hs⟩

end

end Fermat.KummerIso.Principalization
