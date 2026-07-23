import Fermat.Irregular.VandiverLemmaOne
import Fermat.ThirtySeven.SinnottKummer

/-!
# The Takagi--Furtwängler boundary for Vandiver's Lemma 1 at exponent 37

This file separates the elementary class-group part of Vandiver's Lemma 1
from its class-field-theoretic input.  For a prime `p`, divisibility of a
number field's class number by `p` is equivalent to the existence of a
nonprincipal integral ideal whose `p`th power is principal.  We prove that
equivalence here.

At `p = 37`, Takagi's existence theorem (or Furtwängler reciprocity) supplies
the remaining bridge: a nonprincipal ideal root of a Kummer-primary element
produces precisely such `37`-torsion in the maximal real field.  Mathlib does
not yet contain global class-field reciprocity or Hilbert class fields, so we
name that exact output as a proposition rather than disguising Vandiver's
principalization conclusion under a second name.  Sinnott--Kummer's proved
nondivisibility `37 ∤ h⁺` then contradicts that output and proves the
original `LemmaOne K 37` conclusion.
-/

open scoped NumberField

namespace Fermat.Irregular.TakagiFurtwangler37

noncomputable section

open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

/-- An integral ideal representing nontrivial `p`-torsion in the class
group: the ideal is nonprincipal, while its `p`th power is principal. -/
def HasNonprincipalIdealWithPrincipalPower
    (F : Type*) [Field F] [NumberField F] (p : ℕ) : Prop :=
  ∃ I : Ideal (𝓞 F),
    ¬ Submodule.IsPrincipal (I : Ideal (𝓞 F)) ∧
      Submodule.IsPrincipal (I ^ p : Ideal (𝓞 F))

theorem hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
    {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) :
    HasNonprincipalIdealWithPrincipalPower F p ↔
      p ∣ NumberField.classNumber F := by
  constructor
  · rintro ⟨I, hI, hIpow⟩
    by_contra hclass
    exact hI <|
      ideal_isPrincipal_of_pow_of_not_dvd_classNumber hp hclass I hIpow
  · intro hclass
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card
      (G := ClassGroup (𝓞 F)) p (by
        simpa only [NumberField.classNumber] using hclass)
    obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    have hInonprincipal :
        ¬ Submodule.IsPrincipal (I.1 : Ideal (𝓞 F)) := by
      intro hprincipal
      have hc_one : c = 1 := by
        rw [← hI]
        exact (ClassGroup.mk0_eq_one_iff I.2).mpr hprincipal
      have hp_one : p = 1 := by
        rw [← hc, orderOf_eq_one_iff]
        exact hc_one
      exact hp.ne_one hp_one
    have hcpow : c ^ p = 1 := by
      rw [← hc]
      exact pow_orderOf_eq_one c
    have hmkpow : ClassGroup.mk0 (I ^ p) = 1 := by
      rw [map_pow, hI, hcpow]
    have hIpow : Submodule.IsPrincipal (I.1 ^ p : Ideal (𝓞 F)) := by
      exact (ClassGroup.mk0_eq_one_iff (I ^ p).2).mp hmkpow
    exact ⟨I.1, hInonprincipal, hIpow⟩

/-! ## The exact class-field-theoretic output at exponent 37 -/

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The exact real-class-group output of the Takagi--Furtwängler step at
exponent `37`.

If a Kummer-primary integer generates the `37`th power of a nonprincipal
ideal, global reciprocity constructs nontrivial `37`-torsion in the class
group of the maximal real subfield.  Unlike `LemmaOne`, this proposition
does not assume or conclude that the original ideal is principal: its
conclusion is a separate ideal of `K⁺` witnessing real class-group torsion.

This is the minimal presently missing input.  Mathlib has Kummer extensions
and finite class groups, but no Artin reciprocity, Hilbert class field, or
unramified-Kummer theorem from which to prove it. -/
def PrimaryNonprincipalProducesRealTorsion37 (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {a : 𝓞 K} {I : Ideal (𝓞 K)},
    IsKummerPrimary hζ a →
      I ^ 37 = Ideal.span {a} →
        ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
          HasNonprincipalIdealWithPrincipalPower
            (NumberField.maximalRealSubfield K) 37

/-- Equivalent numerical form of the exact missing reciprocity statement:
a primary nonprincipal ideal root forces `37 ∣ h⁺`. -/
theorem primaryNonprincipalProducesRealTorsion37_iff_forces_dvd_classNumber :
    PrimaryNonprincipalProducesRealTorsion37 K ↔
      ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
        {a : 𝓞 K} {I : Ideal (𝓞 K)},
        IsKummerPrimary hζ a →
          I ^ 37 = Ideal.span {a} →
            ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
              37 ∣ NumberField.classNumber
                (NumberField.maximalRealSubfield K) := by
  simp only [PrimaryNonprincipalProducesRealTorsion37]
  constructor
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := NumberField.maximalRealSubfield K) (p := 37) (by norm_num)).mp
        (h hζ hprimary hpow hnonprincipal)
  · intro h ζ hζ a I hprimary hpow hnonprincipal
    exact (hasNonprincipalIdealWithPrincipalPower_iff_dvd_classNumber
      (F := NumberField.maximalRealSubfield K) (p := 37) (by norm_num)).mpr
        (h hζ hprimary hpow hnonprincipal)

set_option maxRecDepth 1000 in
/-- Once the Takagi--Furtwängler real-torsion construction is available,
the unconditional Sinnott--Kummer computation `37 ∤ h⁺` proves
Vandiver's Lemma 1 at exponent `37`. -/
theorem lemmaOne_of_primaryNonprincipalProducesRealTorsion37
    (hTF : PrimaryNonprincipalProducesRealTorsion37 K) :
    LemmaOne K 37 := by
  have hTF' : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
      {a : 𝓞 K} {I : Ideal (𝓞 K)},
      IsKummerPrimary hζ a →
        I ^ 37 = Ideal.span {a} →
          ¬ Submodule.IsPrincipal (I : Ideal (𝓞 K)) →
            37 ∣ NumberField.classNumber
              (NumberField.maximalRealSubfield K) :=
    (primaryNonprincipalProducesRealTorsion37_iff_forces_dvd_classNumber
      (K := K)).mp hTF
  unfold LemmaOne
  intro ζ hζ a I hprimary hpow
  by_contra hnonprincipal
  have hdvd : 37 ∣ NumberField.classNumber
      (NumberField.maximalRealSubfield K) :=
    hTF' hζ hprimary hpow hnonprincipal
  exact Fermat.ThirtySeven.SinnottKummer.not_dvd_classNumber hζ hdvd

end

end Fermat.Irregular.TakagiFurtwangler37
