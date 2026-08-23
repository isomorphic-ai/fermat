import Fermat.Descent.Irregular.AuxiliaryResidueCharacterFactorization
import Fermat.Descent.Irregular.AuxiliaryResidueChannelNaturality

open scoped BigOperators

namespace Fermat.Irregular.CircularUnitResidues

noncomputable section

open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.AuxiliaryResidueChannels

variable {p q h : ℕ} [Fact p.Prime] [Fact q.Prime]

local instance : Fintype (RealResidueGroup p) := Fintype.ofFinite _

namespace Certificate

theorem root_pow_exponentPhase_val
    (C : Certificate p q) (hm : C.symbolExponent = 2 * h)
    (u : (ZMod p)ˣ) :
    C.root ^ (C.exponentPhase hm u).val = C.exponentWeight h u := by
  let z : Subgroup.zpowers C.rootUnit := C.exponentWeightRootPower hm u
  let b : ZMod p := C.exponentPhase hm u
  have hb : ((b.val : ℕ) : ZMod p) = b := ZMod.natCast_zmod_val b
  have happly :=
    C.rootUnit_isPrimitive.zmodEquivZPowers.apply_symm_apply
      (Additive.ofMul z)
  have hpow :=
    C.rootUnit_isPrimitive.zmodEquivZPowers_apply_coe_nat b.val
  rw [hb] at hpow
  change C.rootUnit_isPrimitive.zmodEquivZPowers b = Additive.ofMul
      (⟨C.rootUnit ^ b.val, b.val, rfl⟩ : Subgroup.zpowers C.rootUnit) at hpow
  have hz :
      (⟨C.rootUnit ^ b.val, b.val, rfl⟩ : Subgroup.zpowers C.rootUnit) = z := by
    apply Additive.ofMul.injective
    rw [← hpow]
    exact happly
  have hval := congrArg
    (fun v : Subgroup.zpowers C.rootUnit ↦
      (((v.1 : (ZMod q)ˣ) : ZMod q))) hz
  simpa [z, Certificate.rootUnit, exponentWeightRootPower,
    exponentWeightUnit] using hval

theorem rootAtExponent_root_change
    (C C' : Certificate p q) (a : ℕ)
    (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (u : (ZMod p)ˣ) :
    C'.rootAtExponent u =
      C.rootAtExponent (ZMod.unitOfCoprime a ha * u) := by
  rw [rootAtExponent, rootAtExponent, hroot, ← pow_mul]
  apply pow_eq_pow_of_modEq _ C.root_isPrimitive.pow_eq_one
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val, Units.val_mul,
    ZMod.coe_unitOfCoprime]

theorem exponentWeight_root_change
    (C C' : Certificate p q) (a : ℕ) (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (u : (ZMod p)ˣ) :
    C'.exponentWeight h u =
      C.exponentWeight h (ZMod.unitOfCoprime a ha * u) := by
  rw [exponentWeight, exponentWeight,
    rootAtExponent_root_change C C' a ha hroot u]

/-- Changing the primitive residue root from `root` to `root ^ a`
rescales its additive phase coordinate by `a⁻¹`, while reindexing the
real-residue argument by multiplication with `a`. -/
theorem exponentPhase_root_change
    (C C' : Certificate p q)
    (hm : C.symbolExponent = 2 * h)
    (hm' : C'.symbolExponent = 2 * h)
    (a : ℕ) (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (u : (ZMod p)ˣ) :
    C'.exponentPhase hm' u =
      (a : ZMod p)⁻¹ *
        C.exponentPhase hm (ZMod.unitOfCoprime a ha * u) := by
  let b' : ZMod p := C'.exponentPhase hm' u
  let b : ZMod p := C.exponentPhase hm (ZMod.unitOfCoprime a ha * u)
  have hpow : C.root ^ (a * b'.val) = C.root ^ b.val := by
    rw [pow_mul, ← hroot]
    rw [root_pow_exponentPhase_val C' hm' u]
    rw [exponentWeight_root_change C C' a ha hroot u]
    exact root_pow_exponentPhase_val C hm _ |>.symm
  have hmod : a * b'.val ≡ b.val [MOD p] := by
    have hpowUnit :
        C.rootUnit ^ (a * b'.val) = C.rootUnit ^ b.val := by
      apply Units.ext
      simpa [Certificate.rootUnit] using hpow
    have hmod' : a * b'.val ≡ b.val [MOD orderOf C.rootUnit] :=
      (pow_eq_pow_iff_modEq (x := C.rootUnit)).mp hpowUnit
    simpa only [C.rootUnit_isPrimitive.eq_orderOf] using hmod'
  have hcoord : (a : ZMod p) * b' = b := by
    calc
      (a : ZMod p) * b' =
          (a : ZMod p) * (b'.val : ZMod p) := by
            rw [ZMod.natCast_zmod_val]
      _ = ((a * b'.val : ℕ) : ZMod p) := by rw [Nat.cast_mul]
      _ = (b.val : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      _ = b := ZMod.natCast_zmod_val b
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp ha.symm
  change b' = (a : ZMod p)⁻¹ * b
  rw [← hcoord]
  field_simp [ha0]

/-- The same covariance after descending the even phase through `±1`. -/
theorem realSymbolPhase_root_change
    (C C' : Certificate p q) [Fact (2 < p)] (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (hm' : C'.symbolExponent = 2 * h)
    (a : ℕ) (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (x : RealResidueGroup p) :
    C'.realSymbolPhase hp_three hm' x =
      (a : ZMod p)⁻¹ * C.realSymbolPhase hp_three hm
        (QuotientGroup.mk (ZMod.unitOfCoprime a ha) * x) := by
  induction x using QuotientGroup.induction_on with
  | _ u =>
      rw [← QuotientGroup.mk_mul, C'.realSymbolPhase_mk,
        C.realSymbolPhase_mk]
      exact exponentPhase_root_change C C' hm hm' a ha hroot u

/-- The auxiliary scalar changes by the product of the inverse logarithm
coordinate and the character value of the orbit reindexing element. -/
theorem orbitScalar_realSymbolPhase_root_change
    (C C' : Certificate p q) [Fact (2 < p)] (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (hm' : C'.symbolExponent = 2 * h)
    (a : ℕ) (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (chi : RealResidueGroup p →* (ZMod p)ˣ) :
    orbitScalar chi (C'.realSymbolPhase hp_three hm') =
      (a : ZMod p)⁻¹ *
        (chi (QuotientGroup.mk (ZMod.unitOfCoprime a ha)) : ZMod p) *
          orbitScalar chi (C.realSymbolPhase hp_three hm) := by
  classical
  let A : RealResidueGroup p :=
    QuotientGroup.mk (ZMod.unitOfCoprime a ha)
  let c : ZMod p := (a : ZMod p)⁻¹
  let phase : RealResidueGroup p → ZMod p :=
    C.realSymbolPhase hp_three hm
  let F : RealResidueGroup p → ZMod p := fun x ↦
    c * phase (A * x) * (((chi x)⁻¹ : (ZMod p)ˣ) : ZMod p)
  let H : RealResidueGroup p → ZMod p := fun y ↦
    c * (chi A : ZMod p) *
      (phase y * (((chi y)⁻¹ : (ZMod p)ˣ) : ZMod p))
  simp only [orbitScalar]
  simp_rw [realSymbolPhase_root_change C C' hp_three hm hm' a ha hroot]
  change (∑ x : RealResidueGroup p, F x) =
    c * (chi A : ZMod p) *
      ∑ x : RealResidueGroup p,
        phase x * (((chi x)⁻¹ : (ZMod p)ˣ) : ZMod p)
  calc
    (∑ x : RealResidueGroup p, F x) =
        ∑ y : RealResidueGroup p, F (A⁻¹ * y) := by
      simpa using
        (Equiv.sum_comp (Equiv.mulLeft A⁻¹) F).symm
    _ = ∑ y : RealResidueGroup p, H y := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [F, H, map_mul, map_inv]
      rw [show A * (A⁻¹ * y) = y by group]
      change
        c * phase y *
            (((((chi A)⁻¹ * chi y)⁻¹ : (ZMod p)ˣ)) : ZMod p) = _
      rw [mul_inv_rev, inv_inv]
      simp only [Units.val_mul]
      ring
    _ = c * (chi A : ZMod p) *
        ∑ x : RealResidueGroup p,
          phase x * (((chi x)⁻¹ : (ZMod p)ˣ) : ZMod p) := by
      simp only [H, Finset.mul_sum]

theorem symbolHalf_eq (C C' : Certificate p q) :
    C.symbolHalf = C'.symbolHalf := by
  have hsymbols := C.symbolExponent_eq C'
  rw [C.symbolExponent_eq_two_mul_symbolHalf,
    C'.symbolExponent_eq_two_mul_symbolHalf] at hsymbols
  omega

/-- Any two primitive `p`th residue roots differ by a coprime power. -/
theorem exists_coprime_root_change (C C' : Certificate p q) :
    ∃ a : ℕ, a.Coprime p ∧ C'.root = C.root ^ a := by
  obtain ⟨a, ha_lt, ha_pow⟩ :=
    C.root_isPrimitive.eq_pow_of_pow_eq_one C'.root_isPrimitive.pow_eq_one
  have ha_pos : 0 < a := by
    by_contra ha
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    simp only [pow_zero] at ha_pow
    exact C'.root_isPrimitive.ne_one (Fact.out : p.Prime).one_lt ha_pow.symm
  exact ⟨a,
    Nat.Coprime.symm
      (Nat.coprime_of_lt_prime (Nat.ne_of_gt ha_pos) ha_lt
        (Fact.out : p.Prime)),
    ha_pow.symm⟩

/-- Root-convention covariance of the universal auxiliary scalar. -/
theorem basisFreeFactorization_scalar_root_change
    (C C' : Certificate p q) [Fact (2 < p)] (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (hm' : C'.symbolExponent = 2 * h)
    (a : ℕ) (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (channelRow : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p)) :
    (C'.basisFreeFactorization hp_three hm' channelRow).scalar =
      (a : ZMod p)⁻¹ *
        (evenPowerCharacter (p := p) hp_three channelRow
          (QuotientGroup.mk (ZMod.unitOfCoprime a ha)) : ZMod p) *
        (C.basisFreeFactorization hp_three hm channelRow).scalar := by
  simp only [basisFreeFactorization]
  change orbitScalar (evenPowerCharacter (p := p) hp_three channelRow)
      (C'.realSymbolPhase hp_three hm') =
    (a : ZMod p)⁻¹ *
      (evenPowerCharacter (p := p) hp_three channelRow
        (QuotientGroup.mk (ZMod.unitOfCoprime a ha)) : ZMod p) *
      orbitScalar (evenPowerCharacter (p := p) hp_three channelRow)
        (C.realSymbolPhase hp_three hm)
  exact C.orbitScalar_realSymbolPhase_root_change C' hp_three hm hm'
    a ha hroot (evenPowerCharacter (p := p) hp_three channelRow)

/-- Consequently the actual weighted residue detectors differ by the same
explicit unit scalar and target exactly the same canonical Kummer channel. -/
theorem basisFreeFactorization_residueDetector_root_change
    (C C' : Certificate p q) [Fact (2 < p)] (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (hm' : C'.symbolExponent = 2 * h)
    (a : ℕ) (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (channelRow : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p))
    (e : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p) → ZMod p) :
    (C'.basisFreeFactorization hp_three hm' channelRow).residueDetector e =
      ((a : ZMod p)⁻¹ *
        (evenPowerCharacter (p := p) hp_three channelRow
          (QuotientGroup.mk (ZMod.unitOfCoprime a ha)) : ZMod p)) *
        (C.basisFreeFactorization hp_three hm channelRow).residueDetector e := by
  rw [AuxiliaryResidueChannels.Factorization.residueDetector_eq_scalar_mul_canonical,
    AuxiliaryResidueChannels.Factorization.residueDetector_eq_scalar_mul_canonical,
    C.basisFreeFactorization_scalar_root_change C' hp_three hm hm'
      a ha hroot channelRow]
  ring

theorem root_change_character_factor_ne_zero
    [Fact (2 < p)] (hp_three : 3 ≤ p)
    (a : ℕ) (ha : a.Coprime p)
    (channelRow : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p)) :
    (a : ZMod p)⁻¹ *
        (evenPowerCharacter (p := p) hp_three channelRow
          (QuotientGroup.mk (ZMod.unitOfCoprime a ha)) : ZMod p) ≠ 0 := by
  apply mul_ne_zero
  · apply inv_ne_zero
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp ha.symm
  · exact Units.ne_zero _

/-- Root convention changes preserve the zero locus even when the
q-dependent intrinsic detector scalar itself happens to vanish. -/
theorem basisFreeFactorization_residueDetector_root_change_eq_zero_iff
    (C C' : Certificate p q) [Fact (2 < p)] (hp_three : 3 ≤ p)
    (hm : C.symbolExponent = 2 * h)
    (hm' : C'.symbolExponent = 2 * h)
    (a : ℕ) (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (channelRow : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p))
    (e : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p) → ZMod p) :
    (C'.basisFreeFactorization hp_three hm' channelRow).residueDetector e = 0 ↔
      (C.basisFreeFactorization hp_three hm channelRow).residueDetector e = 0 := by
  rw [C.basisFreeFactorization_residueDetector_root_change C' hp_three
    hm hm' a ha hroot channelRow e]
  exact mul_eq_zero.trans (by
    simp only [root_change_character_factor_ne_zero hp_three a ha channelRow,
      false_or])

/-- Any two primitive-root conventions for checked certificates at the same
split prime give basis-free detectors with exactly the same zero locus. The
explicit coprime root-change exponent and its nonzero scale are recovered
internally. -/
theorem canonicalBasisFreeFactorization_residueDetector_convention_eq_zero_iff
    (C C' : Certificate p q) [Fact (2 < p)] (hp_three : 3 ≤ p)
    (channelRow : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p))
    (e : Fin (KummerCriterion.CyclotomicUnits.kummerLogRank p) → ZMod p) :
    (C'.canonicalBasisFreeFactorization hp_three channelRow).residueDetector e =
        0 ↔
      (C.canonicalBasisFreeFactorization hp_three channelRow).residueDetector e =
        0 := by
  obtain ⟨a, ha, hroot⟩ := C.exists_coprime_root_change C'
  have hm' : C'.symbolExponent = 2 * C.symbolHalf := by
    rw [C'.symbolExponent_eq_two_mul_symbolHalf, C.symbolHalf_eq C']
  simp only [canonicalBasisFreeFactorization]
  exact C.basisFreeFactorization_residueDetector_root_change_eq_zero_iff C'
    hp_three C.symbolExponent_eq_two_mul_symbolHalf hm' a ha hroot
    channelRow e

end Certificate

end

end Fermat.Irregular.CircularUnitResidues
