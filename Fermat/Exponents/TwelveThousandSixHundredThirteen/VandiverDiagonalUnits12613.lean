import Fermat.Descent.Irregular.CircularUnitFamily
import Fermat.Descent.Irregular.VandiverDiagonalLogDerivative
import Fermat.Descent.Irregular.VandiverLemmaTwoCore
import Mathlib.Tactic.NormNum.Prime

/-!
# Vandiver's diagonal real-unit family at exponent 12613

This file constructs the source-faithful diagonal family independently of
any auxiliary-prime residue certificate.  Its two numerical parameters are
the Teichmüller representative `6661` and the real-unit normalization
exponent `9283`, characterized by

`2 * 9283 + 6661 ≡ 1 (mod 12613)`.

The corrected source range has `6306 = (12613 - 1) / 2` factors, indexed by
`j = 0, ..., 6305`.  At source index `i + 1`, the positive integral weight
is `6661 ^ (12613 ^ 2 - 2 * (i + 1) * j)`.
-/

open scoped BigOperators NumberField

namespace Fermat.TwelveThousandSixHundredThirteen.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open NumberField

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 12613) := ⟨by norm_num⟩

/-- Vandiver's chosen positive Teichmüller representative modulo
`12613 ^ 2`. -/
def teichmullerRoot12613 : ℕ := 6661

/-- The exponent making the basic circular unit fixed by complex
conjugation. -/
def normalizationExponent12613 : ℕ := 9283

theorem teichmullerRoot12613_coprime :
    teichmullerRoot12613.Coprime 12613 := by
  norm_num [teichmullerRoot12613]

/-- The corrected factor range `j = 0, ..., 6305`. -/
abbrev VandiverFactorIndex12613 := Fin 6306

theorem card_vandiverFactorIndex12613 :
    Fintype.card VandiverFactorIndex12613 = 6306 := by
  decide

/-- The power of the chosen primitive root in the `j`th conjugate. -/
def conjugateExponent12613 (j : VandiverFactorIndex12613) : ℕ :=
  teichmullerRoot12613 ^ j.val

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight12613
    (i : SourceIndex 12613) (j : VandiverFactorIndex12613) : ℕ :=
  integralDiagonalWeight 12613 teichmullerRoot12613
    (sourceNumber i) j.val

theorem diagonalWeight12613_eq
    (i : SourceIndex 12613) (j : VandiverFactorIndex12613) :
    diagonalWeight12613 i j =
      6661 ^ (12613 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {12613} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {12613} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive12613 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613)
    (j : VandiverFactorIndex12613) :
    IsPrimitiveRoot (zeta ^ conjugateExponent12613 j) 12613 := by
  apply hzeta.pow_of_coprime
  exact teichmullerRoot12613_coprime.pow_left j.val

/-- The literal basic factor of geometric length `6661`. -/
def basicVandiverUnit12613 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613)
    (j : VandiverFactorIndex12613) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 12613) (a := teichmullerRoot12613)
    (conjugate_isPrimitive12613 hzeta j) (by norm_num)
    teichmullerRoot12613_coprime
    normalizationExponent12613

omit [NumberField K] [IsCyclotomicExtension {12613} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger12613 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613)
    (j : VandiverFactorIndex12613) :
    (conjugate_isPrimitive12613 hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent12613 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {12613} ℚ K] in
theorem basicVandiverUnit12613_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613)
    (j : VandiverFactorIndex12613) :
    basicVandiverUnit12613 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 12613) (a := teichmullerRoot12613)
    (e := normalizationExponent12613)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit12613 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613) (i : SourceIndex 12613) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex12613,
    basicVandiverUnit12613 hzeta j ^ diagonalWeight12613 i j

omit [IsCyclotomicExtension {12613} ℚ K] in
theorem diagonalVandiverUnit12613_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613) (i : SourceIndex 12613) :
    diagonalVandiverUnit12613 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit12613_mem_realUnits hzeta j) _

/-- The `6305` source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily12613 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613) :
    SourceIndex 12613 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit12613 hzeta i,
    diagonalVandiverUnit12613_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {12613} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily12613_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613) (i : SourceIndex 12613) :
    ((diagonalVandiverUnitFamily12613 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit12613 hzeta i := rfl

end

end Fermat.TwelveThousandSixHundredThirteen.VandiverDiagonalUnits
