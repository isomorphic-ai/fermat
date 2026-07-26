import Fermat.ThirtySeven.GenericProof
import FltRegular.CaseII.InductionStep

/-!
# The two regular-prime compile breaks at exponent 37

This file is an expected-failure regression for the literal two uses of
regularity in the old Kummer Case-II induction.

The input below is the checked plus-class nondivisibility field of the
exponent-37 irregular certificate.  It is deliberately passed to each old
regular theorem without an adapter.  Lean must reject both applications:

1. the old ideal-root theorem asks for coprimality with the full cyclotomic
   class number;
2. the old unit theorem asks for the same full-class-group regularity.

`#guard_msgs` makes those two failures part of a compiling module.  If either
old call starts accepting the irregular input—or if its failure changes—the
regression itself fails.
-/

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalPrime

namespace Fermat.KummerIso.CompileBreaks37

noncomputable section

local instance prime37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

abbrev K37 := CyclotomicField 37 ℚ

local instance cyclotomic37 :
    IsCyclotomicExtension {37} ℚ K37 :=
  CyclotomicField.isCyclotomicExtension 37 ℚ

local instance cm37 : NumberField.IsCMField K37 :=
  IsCyclotomicExtension.IsCMField (p := 37) K37 (by norm_num)

/-- The actual irregular-prime input carried by the checked exponent-37
certificate. -/
def irregularInput37 : PlusClassNondivisibility K37 37 :=
  Fermat.ThirtySeven.GenericProof.fixedIrregularCertificate37
    |>.secondCase.plusClassNondivisibility

/--
error: Application type mismatch: The argument
  irregularInput37
has type
  PlusClassNondivisibility K37 37
but is expected to have type
  Nat.Coprime 37 (Fintype.card (ClassGroup (𝓞 K37)))
in the application
  isPrincipal_of_isPrincipal_pow_of_Coprime' 37 irregularInput37
-/
#guard_msgs in
example
    (I : FractionalIdeal (𝓞 K37)⁰ K37)
    (hIpow :
      Submodule.IsPrincipal
        ((I ^ 37 : FractionalIdeal (𝓞 K37)⁰ K37) :
          Submodule (𝓞 K37) K37)) :
    Submodule.IsPrincipal (I : Submodule (𝓞 K37) K37) := by
  exact isPrincipal_of_isPrincipal_pow_of_Coprime'
    (A := 𝓞 K37) (K := K37) 37 irregularInput37 I hIpow

/--
error: Application type mismatch: The argument
  irregularInput37
has type
  PlusClassNondivisibility K37 37
but is expected to have type
  Nat.Coprime 37 (Fintype.card (ClassGroup (𝓞 K37)))
in the application
  eq_pow_prime_of_unit_of_congruent hp2 irregularInput37
-/
#guard_msgs in
example
    (u : (𝓞 K37)ˣ)
    (hcong : ∃ n : ℤ, (37 : 𝓞 K37) ∣ (u - n : 𝓞 K37)) :
    ∃ v, u = v ^ 37 := by
  have hp2 : 37 ≠ 2 := by norm_num
  exact eq_pow_prime_of_unit_of_congruent
    (K := K37) (p := 37) hp2 irregularInput37 u hcong

end

end Fermat.KummerIso.CompileBreaks37
