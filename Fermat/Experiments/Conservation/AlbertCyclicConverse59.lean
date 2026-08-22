/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The converse Albert criterion at 59

An exact lift of the concrete Kummer character from `C_59` to `C_(59^2)`
cuts out a cyclic degree-3481 field.  The 59th power of a generator has a
`zeta`-eigenvector; its successive-orbit ratio lies in the concrete Kummer
subfield and has norm `zeta` by telescoping.  This proves the converse to the
constructive compatibility theorem without axioms or per-prime providers.

The `[PerfectField F]` hypothesis is the honest scope required by Mathlib's
absolute-Galois fixed-field correspondence.  It is automatic for the
intended characteristic-zero fields.
-/
import Fermat.Experiments.Conservation.AlbertCyclicCompatibility59
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KummerExtension
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.AlbertCyclicConverse59

open AlbertCyclicQuotient59
open AlbertCyclicCompatibility59
open AlbertExtension59
open KummerCyclicQuotient59

abbrev CyclicGroup59 := Multiplicative (ZMod 59)

local instance : TopologicalSpace CyclicGroup59 := ⊥
local instance : DiscreteTopology CyclicGroup59 := ⟨rfl⟩
local instance : TopologicalSpace CyclicGroup3481 := ⊥
local instance : DiscreteTopology CyclicGroup3481 := ⟨rfl⟩

local instance : NeZero 59 := ⟨by decide⟩
local instance : NeZero 3481 := ⟨by decide⟩

theorem cyclicReduction3481To59_ker_eq_zpowers :
    cyclicReduction3481To59.toMonoidHom.ker =
      Subgroup.zpowers (Multiplicative.ofAdd (59 : ZMod 3481)) := by
  apply le_antisymm
  · intro q hq
    have hcast : (q.toAdd.val : ZMod 59) = 0 := by
      have h := congrArg Multiplicative.toAdd ((MonoidHom.mem_ker).1 hq)
      change ZMod.castHom (by norm_num : 59 ∣ 3481) (ZMod 59) q.toAdd = 0 at h
      rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
      exact h
    have hdvd : 59 ∣ q.toAdd.val :=
      (CharP.cast_eq_zero_iff (ZMod 59) 59 q.toAdd.val).1 hcast
    obtain ⟨k, hk⟩ := hdvd
    have hqPow : q =
        (Multiplicative.ofAdd (59 : ZMod 3481)) ^ k := by
      apply Multiplicative.toAdd.injective
      change q.toAdd = k • (59 : ZMod 3481)
      rw [← ZMod.natCast_zmod_val q.toAdd, hk, Nat.cast_mul]
      simp [nsmul_eq_mul, mul_comm]
    rw [hqPow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k
  · apply Subgroup.zpowers_le.2
    exact (MonoidHom.mem_ker).2 (by decide)

section RatioFixed

variable {F M : Type*} [Field F] [Field M] [Algebra F M]

/-- If `tau^59` scales `y` by a nonzero base-field scalar, then it fixes the
successive-orbit ratio `tau(y) / y`. -/
theorem fiftyNine_pow_fixes_successive_ratio
    (tau : M ≃ₐ[F] M) (zeta : F) (y : M)
    (hzeta : zeta ≠ 0)
    (hy : (tau ^ 59) y = algebraMap F M zeta * y) :
    (tau ^ 59) (tau y / y) = tau y / y := by
  have hcomm : (tau ^ 59) * tau = tau * (tau ^ 59) :=
    (Commute.self_pow tau 59).symm.eq
  have hcommApply : (tau ^ 59) (tau y) = tau ((tau ^ 59) y) := by
    rw [← AlgEquiv.mul_apply, hcomm, AlgEquiv.mul_apply]
  have hzetaM : algebraMap F M zeta ≠ 0 := by
    intro hzero
    apply hzeta
    apply (algebraMap F M).injective
    simpa using hzero
  calc
    (tau ^ 59) (tau y / y) =
        (tau ^ 59) (tau y) / (tau ^ 59) y :=
      map_div₀ (tau ^ 59) (tau y) y
    _ = tau ((tau ^ 59) y) / (tau ^ 59) y := by rw [hcommApply]
    _ = tau (algebraMap F M zeta * y) /
        (algebraMap F M zeta * y) := by rw [hy]
    _ = (algebraMap F M zeta * tau y) /
        (algebraMap F M zeta * y) := by rw [map_mul, tau.commutes]
    _ = tau y / y := by
      field_simp [hzetaM]

/-- The product of successive orbit ratios telescopes exactly. -/
theorem orbitProduct_successive_ratio
    (tau : M ≃ₐ[F] M) (y : M) (hy : y ≠ 0) (n : ℕ) :
    (∏ i ∈ Finset.range n, (tau ^ i) (tau y / y)) =
      (tau ^ n) y / y := by
  induction n with
  | zero => simp [hy]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, map_div₀,
        pow_succ, AlgEquiv.mul_apply]
      have hpow : (tau ^ n) y ≠ 0 := by
        simpa using (tau ^ n).injective.ne hy
      field_simp [hy, hpow]

end RatioFixed

section FixedField

variable (F : Type) [Field F]

/-- The closed kernel of a continuous order-3481 character. -/
def cyclic3481Kernel
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    ClosedSubgroup (Field.absoluteGaloisGroup F) where
  toSubgroup := psi.toMonoidHom.ker
  isClosed' := by
    change IsClosed (psi ⁻¹' ({1} : Set CyclicGroup3481))
    exact isClosed_singleton.preimage psi.continuous

theorem cyclic3481Kernel_isOpen
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    IsOpen ((cyclic3481Kernel F psi : ClosedSubgroup
      (Field.absoluteGaloisGroup F)) : Set (Field.absoluteGaloisGroup F)) := by
  change IsOpen (psi ⁻¹' ({1} : Set CyclicGroup3481))
  exact (isOpen_discrete {1}).preimage psi.continuous

/-- The finite field cut out by a continuous order-3481 character. -/
def cyclic3481FixedField
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.fixedField (cyclic3481Kernel F psi).toSubgroup

instance cyclic3481Kernel.instNormal
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    (cyclic3481Kernel F psi).toSubgroup.Normal := by
  dsimp [cyclic3481Kernel]
  exact MonoidHom.normal_ker psi.toMonoidHom

variable [PerfectField F]

theorem cyclic3481FixedField_finiteDimensional
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    FiniteDimensional F (cyclic3481FixedField F psi) := by
  apply (InfiniteGalois.isOpen_iff_finite (cyclic3481FixedField F psi)).mp
  unfold cyclic3481FixedField
  rw [InfiniteGalois.fixingSubgroup_fixedField (cyclic3481Kernel F psi)]
  exact cyclic3481Kernel_isOpen F psi

theorem cyclic3481FixedField_isGalois
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    IsGalois F (cyclic3481FixedField F psi) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (cyclic3481FixedField F psi)).mp
  unfold cyclic3481FixedField
  rw [InfiniteGalois.fixingSubgroup_fixedField (cyclic3481Kernel F psi)]
  exact MonoidHom.normal_ker psi.toMonoidHom

noncomputable instance cyclic3481FixedField.instFiniteDimensional
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    FiniteDimensional F (cyclic3481FixedField F psi) :=
  cyclic3481FixedField_finiteDimensional F psi

noncomputable instance cyclic3481FixedField.instIsGalois
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    IsGalois F (cyclic3481FixedField F psi) :=
  cyclic3481FixedField_isGalois F psi

/-- The finite Galois group of the field cut out by a surjective character,
identified with the target of that character. -/
def cyclic3481FixedFieldGalEquiv
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481)
    (hsurj : Function.Surjective psi) :
    ((cyclic3481FixedField F psi) ≃ₐ[F]
      (cyclic3481FixedField F psi)) ≃* CyclicGroup3481 := by
  let H := cyclic3481Kernel F psi
  let hnormal : (↑H : Subgroup (Field.absoluteGaloisGroup F)).Normal := by
    dsimp [H, cyclic3481Kernel]
    exact MonoidHom.normal_ker psi.toMonoidHom
  letI : (↑H : Subgroup (Field.absoluteGaloisGroup F)).Normal := hnormal
  let q0 := @InfiniteGalois.normalAutEquivQuotient
    F (AlgebraicClosure F) _ _ _ (by infer_instance) H hnormal
  have hH : (↑H : Subgroup (Field.absoluteGaloisGroup F)) =
      psi.toMonoidHom.ker := by
    rfl
  let hle : (↑H : Subgroup (Field.absoluteGaloisGroup F)) ≤
      psi.toMonoidHom.ker := hH.le
  let lift : (Field.absoluteGaloisGroup F ⧸
      (↑H : Subgroup (Field.absoluteGaloisGroup F))) →* CyclicGroup3481 :=
    QuotientGroup.lift (↑H : Subgroup (Field.absoluteGaloisGroup F))
      psi.toMonoidHom hle
  have hliftSurj : Function.Surjective lift :=
    QuotientGroup.lift_surjective_of_surjective
      (↑H : Subgroup (Field.absoluteGaloisGroup F))
      psi.toMonoidHom hsurj hle
  have hliftKer : lift.ker = ⊥ := by
    dsimp [lift]
    rw [QuotientGroup.ker_lift]
    change Subgroup.map
      (QuotientGroup.mk' (↑H : Subgroup (Field.absoluteGaloisGroup F)))
        psi.toMonoidHom.ker = ⊥
    rw [← hH, QuotientGroup.map_mk'_self]
  have hliftInj : Function.Injective lift :=
    lift.ker_eq_bot_iff.mp hliftKer
  let eLift : (Field.absoluteGaloisGroup F ⧸
      (↑H : Subgroup (Field.absoluteGaloisGroup F))) ≃* CyclicGroup3481 :=
    MulEquiv.ofBijective lift ⟨hliftInj, hliftSurj⟩
  let qsymm :
      ((IntermediateField.fixedField (↑H : Subgroup
        (Field.absoluteGaloisGroup F))) ≃ₐ[F]
          (IntermediateField.fixedField (↑H : Subgroup
            (Field.absoluteGaloisGroup F)))) ≃*
        (Field.absoluteGaloisGroup F ⧸
          (↑H : Subgroup (Field.absoluteGaloisGroup F))) :=
    @MulEquiv.symm
      (Field.absoluteGaloisGroup F ⧸
        (↑H : Subgroup (Field.absoluteGaloisGroup F)))
      ((IntermediateField.fixedField (↑H : Subgroup
        (Field.absoluteGaloisGroup F))) ≃ₐ[F]
          (IntermediateField.fixedField (↑H : Subgroup
            (Field.absoluteGaloisGroup F))))
      (@QuotientGroup.Quotient.group (Field.absoluteGaloisGroup F) _
        (↑H : Subgroup (Field.absoluteGaloisGroup F)) hnormal).toMulOneClass.toMul
      (@AlgEquiv.aut F (IntermediateField.fixedField (↑H : Subgroup
        (Field.absoluteGaloisGroup F))) _ _ _).toMulOneClass.toMul
      q0
  change ((IntermediateField.fixedField (↑H : Subgroup
      (Field.absoluteGaloisGroup F))) ≃ₐ[F]
        (IntermediateField.fixedField (↑H : Subgroup
          (Field.absoluteGaloisGroup F)))) ≃* CyclicGroup3481
  exact @MulEquiv.trans _ _ _
    (@AlgEquiv.aut F (IntermediateField.fixedField (↑H : Subgroup
      (Field.absoluteGaloisGroup F))) _ _ _).toMulOneClass.toMul
    (@QuotientGroup.Quotient.group (Field.absoluteGaloisGroup F) _
      (↑H : Subgroup (Field.absoluteGaloisGroup F)) hnormal).toMulOneClass.toMul
    (@Multiplicative.group (ZMod 3481) _).toMulOneClass.toMul
    qsymm eLift

theorem cyclic3481FixedField_finrank
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481)
    (hsurj : Function.Surjective psi) :
    Module.finrank F (cyclic3481FixedField F psi) = 3481 := by
  rw [← IsGalois.card_aut_eq_finrank]
  calc
    Nat.card ((cyclic3481FixedField F psi) ≃ₐ[F]
        (cyclic3481FixedField F psi)) =
        Nat.card CyclicGroup3481 :=
      Nat.card_congr (cyclic3481FixedFieldGalEquiv F psi hsurj).toEquiv
    _ = 3481 := by norm_num

theorem cyclic3481FixedField_fixingSubgroup
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481) :
    (cyclic3481FixedField F psi).fixingSubgroup =
      psi.toMonoidHom.ker := by
  unfold cyclic3481FixedField
  rw [InfiniteGalois.fixingSubgroup_fixedField (cyclic3481Kernel F psi)]
  rfl

end FixedField

section KummerInsideFixedField

variable (F : Type) [Field F]

/-- Exact compatibility with the concrete Kummer character forces its
degree-59 Kummer field to lie inside the degree-3481 field cut out by the
lifted character. -/
theorem concreteKummer_le_cyclic3481FixedField
    (zeta a : F)
    (hzeta : IsPrimitiveRoot zeta 59)
    (ha : ∀ b : F, b ^ 59 ≠ a)
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481)
    (hpsi : cyclicReduction3481To59.comp psi =
      kummerCharacter59 F zeta a hzeta ha) :
    kummerExtension59 F a ≤ cyclic3481FixedField F psi := by
  let K := kummerExtension59 F a
  letI : IsSplittingField F K (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F K :=
    Polynomial.IsSplittingField.finiteDimensional K
      (kummerPolynomial59 F a)
  letI : IsGalois F K :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha) K
  change K ≤ IntermediateField.fixedField psi.toMonoidHom.ker
  apply (IntermediateField.le_iff_le psi.toMonoidHom.ker K).2
  intro g hg
  have hpg : psi g = 1 := (MonoidHom.mem_ker).1 hg
  have hchi : kummerCharacter59 F zeta a hzeta ha g = 1 := by
    rw [← hpsi]
    change cyclicReduction3481To59 (psi g) = 1
    rw [hpg, map_one]
  have hresChar :
      (kummerGalEquiv59 F zeta a hzeta ha)
        (AlgEquiv.restrictNormalHom K g) = 1 := by
    change Fermat.Conservation.ContinuousCyclicQuotient59.cyclicQuotient59
      F K (kummerGalEquiv59 F zeta a hzeta ha) g = 1 at hchi
    rw [Fermat.Conservation.ContinuousCyclicQuotient59.cyclicQuotient59_apply]
      at hchi
    exact hchi
  have hres : AlgEquiv.restrictNormalHom K g = 1 := by
    apply (kummerGalEquiv59 F zeta a hzeta ha).injective
    simpa using hresChar
  rw [← K.restrictNormalHom_ker]
  exact (MonoidHom.mem_ker).2 hres

theorem kummerCharacter59_eq_one_of_mem_fixingSubgroup
    (F : Type) [Field F]
    (zeta a : F)
    (hzeta : IsPrimitiveRoot zeta 59)
    (ha : ∀ b : F, b ^ 59 ≠ a)
    (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (hg : g ∈ (kummerExtension59 F a).fixingSubgroup) :
    kummerCharacter59 F zeta a hzeta ha g = 1 := by
  let K := kummerExtension59 F a
  letI : IsSplittingField F K (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F K :=
    Polynomial.IsSplittingField.finiteDimensional K
      (kummerPolynomial59 F a)
  letI : IsGalois F K :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha) K
  have hres : AlgEquiv.restrictNormalHom K g = 1 := by
    apply (MonoidHom.mem_ker).1
    rw [K.restrictNormalHom_ker]
    exact hg
  change Fermat.Conservation.ContinuousCyclicQuotient59.cyclicQuotient59
    F K (kummerGalEquiv59 F zeta a hzeta ha) g = 1
  rw [Fermat.Conservation.ContinuousCyclicQuotient59.cyclicQuotient59_apply,
    hres, map_one]

end KummerInsideFixedField

section ReductionKernelAction

variable (F : Type) [Field F] [PerfectField F]

/-- If an absolute Galois element has trivial reduction modulo 59, its
action on the field cut out by `psi` is a power of the 59th power of a
chosen order-3481 lift generator. -/
theorem fixedField_restriction_mem_zpowers_fiftyNine
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481)
    (g h : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (hg : psi g = Multiplicative.ofAdd (1 : ZMod 3481))
    (hh : cyclicReduction3481To59 (psi h) = 1) :
    AlgEquiv.restrictNormalHom (cyclic3481FixedField F psi) h ∈
      Subgroup.zpowers
        ((AlgEquiv.restrictNormalHom (cyclic3481FixedField F psi) g) ^ 59) := by
  let M := cyclic3481FixedField F psi
  have hqKer : psi h ∈ cyclicReduction3481To59.toMonoidHom.ker :=
    (MonoidHom.mem_ker).2 hh
  rw [cyclicReduction3481To59_ker_eq_zpowers] at hqKer
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hqKer
  have hgPow : psi (g ^ 59) =
      Multiplicative.ofAdd (59 : ZMod 3481) := by
    calc
      psi (g ^ 59) = (psi g) ^ 59 := map_pow psi g 59
      _ = (Multiplicative.ofAdd (1 : ZMod 3481)) ^ 59 := by rw [hg]
      _ = Multiplicative.ofAdd (59 : ZMod 3481) := by decide
  have hpsiEq : psi ((g ^ 59) ^ n) = psi h := by
    calc
      psi ((g ^ 59) ^ n) = (psi (g ^ 59)) ^ n := map_zpow psi (g ^ 59) n
      _ = (Multiplicative.ofAdd (59 : ZMod 3481)) ^ n := by rw [hgPow]
      _ = psi h := hn
  have heq : AlgEquiv.restrictNormalHom M ((g ^ 59) ^ n) =
      AlgEquiv.restrictNormalHom M h := by
    apply (AlgEquiv.restrictNormalHom M).eq_iff.2
    rw [M.restrictNormalHom_ker,
      cyclic3481FixedField_fixingSubgroup F psi]
    exact psi.toMonoidHom.eq_iff.1 hpsiEq
  have hzpow : (g ^ 59) ^ n ∈
      Subgroup.zpowers (g ^ 59) := ⟨n, rfl⟩
  have hmap : AlgEquiv.restrictNormalHom M ((g ^ 59) ^ n) ∈
      (Subgroup.zpowers (g ^ 59)).map
        (AlgEquiv.restrictNormalHom M) := ⟨_, hzpow, rfl⟩
  rw [MonoidHom.map_zpowers, map_pow] at hmap
  rw [← heq]
  exact hmap

end ReductionKernelAction

section RatioInKummerField

variable (F : Type) [Field F] [PerfectField F]

set_option maxRecDepth 10000 in
/-- A point of the order-3481 field fixed by the 59th power of a lifted
generator belongs to the concrete Kummer subfield selected by the exact
reduction equation. -/
theorem fixedBy_fiftyNine_mem_kummerExtension59
    (zeta a : F)
    (hzeta : IsPrimitiveRoot zeta 59)
    (ha : ∀ b : F, b ^ 59 ≠ a)
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481)
    (hpsi : cyclicReduction3481To59.comp psi =
      kummerCharacter59 F zeta a hzeta ha)
    (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (hg : psi g = Multiplicative.ofAdd (1 : ZMod 3481))
    (x : cyclic3481FixedField F psi)
    (hx : ((AlgEquiv.restrictNormalHom
      (cyclic3481FixedField F psi) g) ^ 59) x = x) :
    (x : AlgebraicClosure F) ∈ kummerExtension59 F a := by
  let K := kummerExtension59 F a
  let M := cyclic3481FixedField F psi
  letI : IsSplittingField F K (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F K :=
    Polynomial.IsSplittingField.finiteDimensional K
      (kummerPolynomial59 F a)
  letI : IsGalois F K :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha) K
  change (x : AlgebraicClosure F) ∈ K
  rw [← InfiniteGalois.fixedField_fixingSubgroup K]
  intro h
  rcases h with ⟨h, hh⟩
  have hchi : kummerCharacter59 F zeta a hzeta ha h = 1 :=
    kummerCharacter59_eq_one_of_mem_fixingSubgroup
      F zeta a hzeta ha h hh
  have heval := DFunLike.congr_fun hpsi h
  have hred : cyclicReduction3481To59 (psi h) = 1 := by
    change cyclicReduction3481To59 (psi h) =
      kummerCharacter59 F zeta a hzeta ha h at heval
    rw [heval, hchi]
  have hmem := fixedField_restriction_mem_zpowers_fiftyNine
    F psi g h hg hred
  have hfixedM : AlgEquiv.restrictNormalHom M h x = x := by
    have hsmul := smul_eq_self_of_mem_zpowers hmem
      (a := x) (by
        change ((AlgEquiv.restrictNormalHom M g) ^ 59) x = x
        exact hx)
    simpa [AlgEquiv.smul_def] using hsmul
  calc
    h (x : AlgebraicClosure F) =
        ((AlgEquiv.restrictNormalHom M h) x : M) := by
      symm
      exact AlgEquiv.restrictNormalHom_apply M h x
    _ = (x : AlgebraicClosure F) := congrArg Subtype.val hfixedM

end RatioInKummerField

section LiftGeneratorEigenvector

variable (F : Type) [Field F] [PerfectField F]

set_option maxRecDepth 10000 in
/-- A surjective order-3481 lift supplies a generator whose 59th power has
an honest nonzero `zeta`-eigenvector in the fixed field it cuts out. -/
theorem exists_cyclic3481_generator_eigenvector
    (zeta a : F)
    (hzeta : IsPrimitiveRoot zeta 59)
    (ha : ∀ b : F, b ^ 59 ≠ a)
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481)
    (hpsi : cyclicReduction3481To59.comp psi =
      kummerCharacter59 F zeta a hzeta ha) :
    ∃ g : Field.absoluteGaloisGroup F,
      ∃ y : cyclic3481FixedField F psi,
        psi g = Multiplicative.ofAdd (1 : ZMod 3481) ∧
        orderOf (AlgEquiv.restrictNormalHom
          (cyclic3481FixedField F psi) g) = 3481 ∧
        y ≠ 0 ∧
        ((AlgEquiv.restrictNormalHom
          (cyclic3481FixedField F psi) g) ^ 59) y =
          algebraMap F (cyclic3481FixedField F psi) zeta * y := by
  let M := cyclic3481FixedField F psi
  have hredSurj : Function.Surjective
      (cyclicReduction3481To59.comp psi) := by
    rw [hpsi]
    exact kummerCharacter59_surjective F zeta a hzeta ha
  have hsurj : Function.Surjective psi :=
    continuous_surjective_of_cyclicReduction3481To59_comp_surjective
      psi hredSurj
  obtain ⟨g, hg⟩ := hsurj (Multiplicative.ofAdd (1 : ZMod 3481))
  let tau : M ≃ₐ[F] M := AlgEquiv.restrictNormalHom M g
  have htauPow_ne : tau ^ 59 ≠ 1 := by
    intro htau
    have hrestrict : AlgEquiv.restrictNormalHom M (g ^ 59) = 1 := by
      change (AlgEquiv.restrictNormalHom M g) ^ 59 = 1 at htau
      rw [← map_pow] at htau
      exact htau
    have hgFix : g ^ 59 ∈ M.fixingSubgroup := by
      rw [← M.restrictNormalHom_ker]
      exact (MonoidHom.mem_ker).2 hrestrict
    have hgKer : g ^ 59 ∈ psi.toMonoidHom.ker := by
      change g ^ 59 ∈ (cyclic3481FixedField F psi).fixingSubgroup at hgFix
      rwa [cyclic3481FixedField_fixingSubgroup F psi] at hgFix
    have hpsiPow : psi (g ^ 59) = 1 := (MonoidHom.mem_ker).1 hgKer
    have hgenPow :
        (Multiplicative.ofAdd (1 : ZMod 3481)) ^ 59 ≠ 1 := by
      decide
    apply hgenPow
    simpa [map_pow, hg] using hpsiPow
  have hcard : Nat.card (M ≃ₐ[F] M) = 3481 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact cyclic3481FixedField_finrank F psi hsurj
  have hdiv0 := orderOf_dvd_natCard tau
  rw [hcard] at hdiv0
  have hdiv : orderOf tau ∣ 59 ^ 2 := by
    norm_num at hdiv0 ⊢
    exact hdiv0
  obtain ⟨k, hk, horder⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 59)).1 hdiv
  have htauOrder : orderOf tau = 3481 := by
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkCases with rfl | rfl | rfl
    · exfalso
      apply htauPow_ne
      apply (orderOf_dvd_iff_pow_eq_one).1
      rw [horder]
      norm_num
    · exfalso
      apply htauPow_ne
      apply (orderOf_dvd_iff_pow_eq_one).1
      rw [horder]
      norm_num
    · rw [horder]
      norm_num
  let rho : M ≃ₐ[F] M := tau ^ 59
  have hrhoOrder : orderOf rho = 59 := by
    dsimp [rho]
    rw [orderOf_pow, htauOrder]
    norm_num
  have hroot : IsRoot (minpoly F rho.toLinearMap) zeta := by
    rw [minpoly_algEquiv_toLinearMap rho (isOfFinOrder_of_finite rho),
      hrhoOrder]
    simpa [sub_eq_zero] using hzeta.pow_eq_one
  obtain ⟨y, hy⟩ :=
    (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
  refine ⟨g, y, hg, htauOrder, hy.2, ?_⟩
  calc
    ((AlgEquiv.restrictNormalHom M g) ^ 59) y = rho y := rfl
    _ = zeta • y := hy.apply_eq_smul
    _ = algebraMap F M zeta * y := by rw [Algebra.smul_def]

end LiftGeneratorEigenvector

section AlbertConverse

variable (F : Type) [Field F] [PerfectField F]

set_option maxRecDepth 10000 in
/-- Converse Albert criterion for the concrete degree-59 Kummer extension:
an exact lift of its Kummer character to `C_(59^2)` produces an element
whose norm is the supplied primitive 59th root of unity. -/
theorem concreteKummer_exists_norm_of_albertCharacter3481
    (zeta a : F)
    (hzeta : IsPrimitiveRoot zeta 59)
    (ha : ∀ b : F, b ^ 59 ≠ a)
    (psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481)
    (hpsi : cyclicReduction3481To59.comp psi =
      kummerCharacter59 F zeta a hzeta ha) :
    ∃ beta : kummerExtension59 F a,
      Algebra.norm F beta = zeta := by
  let K := kummerExtension59 F a
  let M := cyclic3481FixedField F psi
  letI : IsSplittingField F K (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F K :=
    Polynomial.IsSplittingField.finiteDimensional K
      (kummerPolynomial59 F a)
  letI : IsGalois F K :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha) K
  obtain ⟨g, y, hg, htauOrder, hy0, hy⟩ :=
    exists_cyclic3481_generator_eigenvector F zeta a hzeta ha psi hpsi
  let gamma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := g
  have hgamma : psi gamma = Multiplicative.ofAdd (1 : ZMod 3481) := hg
  let tau : M ≃ₐ[F] M := AlgEquiv.restrictNormalHom M gamma
  have hy' : (tau ^ 59) y = algebraMap F M zeta * y := hy
  let betaM : M := tau y / y
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (by decide)
  have hbetaMFix : (tau ^ 59) betaM = betaM := by
    exact fiftyNine_pow_fixes_successive_ratio tau zeta y hzeta0 hy'
  have hbetaMem : (betaM : AlgebraicClosure F) ∈ K := by
    exact fixedBy_fiftyNine_mem_kummerExtension59
      F zeta a hzeta ha psi hpsi gamma hgamma betaM hbetaMFix
  let beta : K := ⟨(betaM : AlgebraicClosure F), hbetaMem⟩
  refine ⟨beta, ?_⟩
  have hKM : K ≤ M :=
    concreteKummer_le_cyclic3481FixedField F zeta a hzeta ha psi hpsi
  let inc : K →ₐ[F] M := IntermediateField.inclusion hKM
  let sigma : K ≃ₐ[F] K := AlgEquiv.restrictNormalHom K gamma
  have hfinrank : Module.finrank F K = 59 :=
    finrank_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha) K
  have hchi : kummerCharacter59 F zeta a hzeta ha gamma =
      Multiplicative.ofAdd (1 : ZMod 59) := by
    have heval := DFunLike.congr_fun hpsi gamma
    change cyclicReduction3481To59 (psi gamma) =
      kummerCharacter59 F zeta a hzeta ha gamma at heval
    rw [← heval, hgamma]
    decide
  have hsigmaNe : sigma ≠ 1 := by
    intro hsigma
    have hchiOne : kummerCharacter59 F zeta a hzeta ha gamma = 1 := by
      change Fermat.Conservation.ContinuousCyclicQuotient59.cyclicQuotient59
        F K (kummerGalEquiv59 F zeta a hzeta ha) gamma = 1
      rw [Fermat.Conservation.ContinuousCyclicQuotient59.cyclicQuotient59_apply]
      change (kummerGalEquiv59 F zeta a hzeta ha) sigma = 1
      rw [hsigma, map_one]
    have : Multiplicative.ofAdd (1 : ZMod 59) = 1 := hchi.symm.trans hchiOne
    exact (by decide :
      Multiplicative.ofAdd (1 : ZMod 59) ≠ 1) this
  have hcard : Nat.card (K ≃ₐ[F] K) = 59 := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  have hsigma : ∀ eta : K ≃ₐ[F] K,
      eta ∈ Subgroup.zpowers sigma := by
    letI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    intro eta
    exact mem_zpowers_of_prime_card hcard hsigmaNe
  have htelescope :
      (∏ i ∈ Finset.range 59, (tau ^ i) betaM) =
        algebraMap F M zeta := by
    calc
      (∏ i ∈ Finset.range 59, (tau ^ i) betaM) =
          (tau ^ 59) y / y :=
        orbitProduct_successive_ratio tau y hy0 59
      _ = (algebraMap F M zeta * y) / y := by rw [hy']
      _ = algebraMap F M zeta := by field_simp [hy0]
  have hpowMap (i : ℕ) :
      inc ((sigma ^ i) beta) = (tau ^ i) betaM := by
    apply Subtype.ext
    have hKapply := AlgEquiv.restrictNormalHom_apply K (gamma ^ i) beta
    have hMapply := AlgEquiv.restrictNormalHom_apply M (gamma ^ i) betaM
    rw [map_pow] at hKapply hMapply
    calc
      (((sigma ^ i) beta : K) : AlgebraicClosure F) =
          (gamma ^ i) (beta : AlgebraicClosure F) := hKapply
      _ = (gamma ^ i) (betaM : AlgebraicClosure F) := rfl
      _ = (((tau ^ i) betaM : M) : AlgebraicClosure F) := hMapply.symm
  have horbitMap : inc (orbitProduct59 sigma beta 59) =
      ∏ i ∈ Finset.range 59, (tau ^ i) betaM := by
    simp only [orbitProduct59, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact hpowMap i
  have horbitNorm : orbitProduct59 sigma beta 59 =
      algebraMap F K (Algebra.norm F beta) :=
    orbitProduct59_eq_algebraMap_norm sigma beta hsigma hfinrank
  have hnormMap : algebraMap F M (Algebra.norm F beta) =
      algebraMap F M zeta := by
    calc
      algebraMap F M (Algebra.norm F beta) =
          inc (algebraMap F K (Algebra.norm F beta)) :=
        (inc.commutes (Algebra.norm F beta)).symm
      _ = inc (orbitProduct59 sigma beta 59) := by rw [horbitNorm]
      _ = ∏ i ∈ Finset.range 59, (tau ^ i) betaM := horbitMap
      _ = algebraMap F M zeta := htelescope
  exact (algebraMap F M).injective hnormMap

/-- The concrete Albert criterion at 59: the primitive-root norm condition is
equivalent to exact liftability of the concrete Kummer character from
`C_59` to `C_(59^2)`. -/
theorem concreteKummer_norm_iff_exists_albertCharacter3481
    (zeta a : F)
    (hzeta : IsPrimitiveRoot zeta 59)
    (ha : ∀ b : F, b ^ 59 ≠ a) :
    (∃ beta : kummerExtension59 F a,
        Algebra.norm F beta = zeta) ↔
      ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup3481,
        cyclicReduction3481To59.comp psi =
          kummerCharacter59 F zeta a hzeta ha := by
  constructor
  · rintro ⟨beta, hbeta⟩
    exact concreteKummer_exists_albertCharacter3481
      F zeta a hzeta ha beta hbeta
  · rintro ⟨psi, hpsi⟩
    exact concreteKummer_exists_norm_of_albertCharacter3481
      F zeta a hzeta ha psi hpsi

end AlbertConverse

end Fermat.Conservation.AlbertCyclicConverse59
