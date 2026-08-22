/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The normalization correction has no chi=15 component

The normalization correction `-zeta^-1` is a global unit.  Its Kummer
class transforms in the Teichmuller character, whereas the selected
irregular seat has character `omega^15`.  A single cyclotomic automorphism,
the one indexed by `2`, separates the two eigenvalues and therefore kills
the correction under the chi=15 projector.
-/
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorConjugation59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.NormalizationCorrectionProjection59

open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.FermatFactorConjugation59
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 59}

/-- The unit `2` in the cyclotomic Galois index. -/
def twoIndex59 : GaloisIndex59 :=
  Units.mk0 (2 : ZMod 59) (by decide)

@[simp]
theorem twoIndex59_val : ((twoIndex59 : ZMod 59).val) = 2 := by
  rfl

/-- The cyclotomic automorphism indexed by `2` squares every primitive
59th root in the integer ring, including the root chosen by the state. -/
theorem cyclotomicSigma_two_smul_zetaInteger
    (hζ : IsPrimitiveRoot ζ 59) :
    KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K twoIndex59 •
        hζ.toInteger =
      hζ.toInteger ^ 2 := by
  have h := IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq
    59 K (KummerCriterion.cyclotomicSigmaOfUnit
      (p := 59) K twoIndex59)
    hζ.toInteger_isPrimitiveRoot.pow_eq_one
  rw [KummerCriterion.cyclotomicGalEquivZMod_sigmaOfUnit] at h
  simpa using h

/-- Field-valued form of the same squaring law. -/
theorem cyclotomicSigma_two_apply_zeta
    (hζ : IsPrimitiveRoot ζ 59) :
    KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K twoIndex59 ζ =
      ζ ^ 2 := by
  have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
    59 K (KummerCriterion.cyclotomicSigmaOfUnit
      (p := 59) K twoIndex59) hζ.pow_eq_one
  rw [KummerCriterion.cyclotomicGalEquivZMod_sigmaOfUnit] at h
  simpa using h

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
@[simp]
theorem normalizationCorrectionFieldUnit59_val
    (hζ : IsPrimitiveRoot ζ 59) :
    ((normalizationCorrectionFieldUnit59 hζ : Kˣ) : K) = -ζ⁻¹ := by
  simp [normalizationCorrectionFieldUnit59,
    normalizationCorrectionRingUnit59, StateFactorPair.zetaUnit_val]

/-- The correction field unit transforms as minus its square. -/
theorem cyclotomicUnitEquiv59_two_correction
    (hζ : IsPrimitiveRoot ζ 59) :
    cyclotomicUnitEquiv59 K twoIndex59
        (normalizationCorrectionFieldUnit59 hζ) =
      (-1 : Kˣ) * (normalizationCorrectionFieldUnit59 hζ) ^ 2 := by
  apply Units.ext
  simp only [cyclotomicUnitEquiv59,
    Fermat.Conservation.PrimeCyclotomicSelmerAction.cyclotomicUnitEquiv,
    Units.coe_mapEquiv,
    normalizationCorrectionFieldUnit59_val, Units.val_mul,
    Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val]
  have hmap :
      (KummerCriterion.cyclotomicSigmaOfUnit
        (p := 59) K twoIndex59).toMulEquiv (-ζ⁻¹) =
        -(KummerCriterion.cyclotomicSigmaOfUnit
          (p := 59) K twoIndex59 ζ)⁻¹ := by
    change KummerCriterion.cyclotomicSigmaOfUnit
        (p := 59) K twoIndex59 (-ζ⁻¹) = _
    rw [map_neg, map_inv₀]
  rw [hmap, cyclotomicSigma_two_apply_zeta hζ]
  ring

/-- In the 59th-power Kummer quotient the extra sign disappears, so the
correction is a genuine eigenvector of the automorphism indexed by `2`. -/
theorem cyclotomicCorrectionStrictSelmer59_two
    (hζ : IsPrimitiveRoot ζ 59) :
    cyclotomicStrictSelmerRepresentation59 K twoIndex59
        (normalizationCorrectionStrictSelmer59 hζ) =
      2 • normalizationCorrectionStrictSelmer59 hζ := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (↑(cyclotomicUnitEquiv59 K twoIndex59
      (normalizationCorrectionFieldUnit59 hζ)) :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
    (↑(normalizationCorrectionFieldUnit59 hζ) :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) ^ 2
  rw [cyclotomicUnitEquiv59_two_correction]
  calc
    (↑((-1 : Kˣ) * (normalizationCorrectionFieldUnit59 hζ) ^ 2) :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
        (↑(-1 : Kˣ) :
          Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) *
          (↑(normalizationCorrectionFieldUnit59 hζ) :
            Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) ^ 2 := by
      exact map_mul (QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range) _ _
    _ = _ := by
      have hminus :
          (↑(-1 : Kˣ) :
            Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact ⟨(-1 : Kˣ), by norm_num⟩
      rw [hminus]
      exact one_mul
        ((↑(normalizationCorrectionFieldUnit59 hζ) :
          Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) ^ 2)

/-! ## Separation from the irregular character -/

/-- At the index `2`, the selected irregular character reduces to `23`,
whereas the correction class has eigenvalue `2`. -/
theorem irregularCharacter59_two_reduction :
    PadicInt.toZMod
        (irregularCharacter59 twoIndex59 : PadicInt 59) = 23 := by
  have h := DFunLike.congr_fun
    reducedCharacter59_irregularCharacter59 twoIndex59
  have hval := congrArg Units.val h
  calc
    PadicInt.toZMod
        (irregularCharacter59 twoIndex59 : PadicInt 59) =
        (twoIndex59 : ZMod 59) ^ (15 : ZMod 58).val := by
      simpa [reducedCharacter59, powerCharacter59] using hval
    _ = 23 := by
      rw [show (15 : ZMod 58).val = 15 by decide]
      change (2 : ZMod 59) ^ 15 = 23
      decide

/-- The root-of-unity normalization correction has no component in the
canonical `chi = 15` irregular seat. -/
theorem normalizationCorrectionPrimalMode59_eq_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (hζ : IsPrimitiveRoot ζ 59) :
    normalizationCorrectionPrimalMode59 hζ = 0 := by
  let rho := cyclotomicStrictSelmerRepresentation59 K
  let e := characterIdempotent irregularCharacter59
  let x := normalizationCorrectionStrictSelmer59 hζ
  let y := rho.asAlgebraHom e x
  have hyMem : y ∈ characterEigenspaceAt rho irregularCharacter59 :=
    characterIdempotent_action_mem_characterEigenspaceAt
      rho irregularCharacter59 x
  have hyCharacter :
      rho twoIndex59 y =
        (irregularCharacter59 twoIndex59 : PadicInt 59) • y :=
    (mem_characterEigenspaceAt_iff rho irregularCharacter59 y).mp
      hyMem twoIndex59
  have hyTwo : rho twoIndex59 y = 2 • y := by
    calc
      rho twoIndex59 (rho.asAlgebraHom e x) =
          rho.asAlgebraHom
            (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 twoIndex59)
            (rho.asAlgebraHom e x) := by
        rw [Representation.asAlgebraHom_of]
      _ = rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 twoIndex59 * e) x := by
        rw [map_mul]
        rfl
      _ = rho.asAlgebraHom
          (e * MonoidAlgebra.of (PadicInt 59) GaloisIndex59 twoIndex59) x := by
        rw [mul_comm]
      _ = rho.asAlgebraHom e
          (rho.asAlgebraHom
            (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 twoIndex59) x) := by
        rw [map_mul]
        rfl
      _ = rho.asAlgebraHom e (rho twoIndex59 x) := by
        rw [Representation.asAlgebraHom_of]
      _ = rho.asAlgebraHom e (2 • x) := by
        rw [cyclotomicCorrectionStrictSelmer59_two hζ]
      _ = 2 • rho.asAlgebraHom e x := by
        rw [map_nsmul]
  have hyTwoPadic :
      rho twoIndex59 y = (2 : PadicInt 59) • y := by
    calc
      rho twoIndex59 y = 2 • y := hyTwo
      _ = (2 : PadicInt 59) • y :=
        (Nat.cast_smul_eq_nsmul (PadicInt 59) 2 y).symm
  have hscalar :
      (irregularCharacter59 twoIndex59 : PadicInt 59) • y =
        (2 : PadicInt 59) • y :=
    hyCharacter.symm.trans hyTwoPadic
  rw [padicInt_smul_eq_toZMod_smul,
    padicInt_smul_eq_toZMod_smul] at hscalar
  rw [irregularCharacter59_two_reduction] at hscalar
  rw [map_ofNat] at hscalar
  have hzero : ((23 : ZMod 59) - 2) • y = 0 := by
    calc
      ((23 : ZMod 59) - 2) • y =
          (23 : ZMod 59) • y - (2 : ZMod 59) • y :=
        sub_smul (23 : ZMod 59) 2 y
      _ = 0 := sub_eq_zero.mpr hscalar
  have hyZero : y = 0 :=
    (smul_eq_zero.mp hzero).resolve_left (by decide)
  apply Subtype.ext
  exact hyZero

/-- Therefore the projected normalized factors satisfy the clean odd
conjugation relation with no retained correction term. -/
theorem fermatMinusPrimalMode59_eq_neg_plus
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
    {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59.fermatMinusPrimalMode59
        pair =
      -Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59.fermatPlusPrimalMode59
        pair :=
  (fermatMinusPrimalMode59_eq_neg_plus_iff_correction_eq_zero pair).2
    (normalizationCorrectionPrimalMode59_eq_zero hζ)

end Fermat.FiftyNine.Conservation.NormalizationCorrectionProjection59
