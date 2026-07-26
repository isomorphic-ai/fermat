import FltRegular.CaseII.Statement

open scoped NumberField

#check IdealPowerClassTransport
#check FullValuationUnitTransport
#check RelevantCaseIIAutomorphismTransport
#check FltRegular.caseII

example {a b c : ℤ} {p : ℕ} [Fact p.Prime]
    (transport :
      RelevantCaseIIAutomorphismTransport
        (CyclotomicField p ℚ) p)
    (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p :=
  FltRegular.caseII transport hodd hprod hgcd hcase
