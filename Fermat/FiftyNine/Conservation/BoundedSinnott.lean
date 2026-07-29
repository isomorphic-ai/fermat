/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conductor-59 bounded Sinnott bridge

This file compares the generated squared-edge ledger with the classical
prime-conductor squared circular-unit subgroup.  Only the one direction
consumed by the conservation endpoint is used: divisibility of the plus
class number implies divisibility of the generated capacity.
-/
import Fermat.FiftyNine.Conservation.Credit
import KummerCriterion.CyclotomicUnits.NormalizedIndex

open scoped NumberField

namespace Fermat.FiftyNine.Conservation.Credit

noncomputable section

open NumberField

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

local notation3 "K⁺" => NumberField.maximalRealSubfield K
local notation3 "ζ₀" => IsCyclotomicExtension.zeta 59 ℚ K

/-- Extension of plus-side units identifies them with Mathlib's subgroup
of units fixed by complex conjugation. -/
private noncomputable def plusUnitsEquivRealUnits :
    (𝓞 K⁺)ˣ ≃* NumberField.IsCMField.realUnits K :=
  MulEquiv.ofBijective
    (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom).rangeRestrict
    ⟨fun _ _ h ↦
        Units.map_injective
          (FaithfulSMul.algebraMap_injective (𝓞 K⁺) (𝓞 K))
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/-- The squared prime-conductor circular-unit subgroup, transported from
the maximal real subfield to the generated ledger's ambient group. -/
private noncomputable def mappedCPlus :
    Subgroup (NumberField.IsCMField.realUnits K) :=
  (KummerCriterion.CPlus (p := 59) (K := K) (by norm_num)).map
    (plusUnitsEquivRealUnits (K := K))

private theorem mappedCPlus_index :
    (mappedCPlus (K := K)).index =
      (KummerCriterion.CPlus (p := 59) (K := K) (by norm_num)).index := by
  simpa only [mappedCPlus] using
    (Subgroup.index_map_equiv
      (H := KummerCriterion.CPlus (p := 59) (K := K) (by norm_num))
      (plusUnitsEquivRealUnits (K := K)))

/-- The safe dependency boundary: KummerCriterion's conductor-prime
Sinnott formula, specialized here to the squared family at `59`. -/
private theorem dvd_mappedCPlus_index_iff_dvd_classNumber :
    59 ∣ (mappedCPlus (K := K)).index ↔
      59 ∣ NumberField.classNumber K⁺ := by
  rw [mappedCPlus_index (K := K)]
  have hcompare :=
    KummerCriterion.CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd
      (p := 59) (K := K) (by norm_num) (by norm_num)
  have hsinnott :=
    KummerCriterion.cyclotomicUnitIndex_primeConductor_pPrimary
      (p := 59) (K := K) (by norm_num)
  exact hcompare.trans (by
    simpa only [KummerCriterion.hPlus, NumberField.classNumber] using hsinnott)

/-- Folding with complex conjugation is multiplicative. -/
private theorem realProjection_mul (u v : (𝓞 K)ˣ) :
    realProjection (u * v) = realProjection u * realProjection v := by
  apply Subtype.ext
  simp only [realProjection, map_mul, Subgroup.coe_mul]
  ac_rfl

/-- Folding with complex conjugation commutes with inversion. -/
private theorem realProjection_inv (u : (𝓞 K)ˣ) :
    realProjection u⁻¹ = (realProjection u)⁻¹ := by
  apply Subtype.ext
  change u⁻¹ * NumberField.IsCMField.unitsComplexConj K u⁻¹ =
    (u * NumberField.IsCMField.unitsComplexConj K u)⁻¹
  rw [map_inv]
  ac_rfl

/-- A torsion factor disappears after folding with complex conjugation. -/
private theorem realProjection_torsion_mul
    (t : NumberField.Units.torsion K) (u : (𝓞 K)ˣ) :
    realProjection ((t : (𝓞 K)ˣ) * u) = realProjection u := by
  apply Subtype.ext
  change ((t : (𝓞 K)ˣ) * u) *
      NumberField.IsCMField.unitsComplexConj K ((t : (𝓞 K)ˣ) * u) =
    u * NumberField.IsCMField.unitsComplexConj K u
  rw [map_mul]
  have ht := NumberField.IsCMField.unitsComplexConj_torsion (K := K) t
  change NumberField.IsCMField.unitsComplexConj K (t : (𝓞 K)ˣ) =
    (t : (𝓞 K)ˣ)⁻¹ at ht
  rw [ht]
  calc
    _ =
      ((t : (𝓞 K)ˣ) * (t : (𝓞 K)ˣ)⁻¹) *
        (u * NumberField.IsCMField.unitsComplexConj K u) := by
          ac_rfl
    _ = u * NumberField.IsCMField.unitsComplexConj K u := by simp

/-- At the canonical primitive root, Credit's geometric unit is exactly the
prime-conductor cyclotomic unit used by KummerCriterion. -/
private theorem orbitNodeUnit_canonical
    (a : (ZMod 59)ˣ) :
    orbitNodeUnit
        (IsCyclotomicExtension.zeta_spec 59 ℚ K) a =
      KummerCriterion.LehmerVandiver.cyclotomicUnitUnit
        59 K (a : ZMod 59).val (ZMod.val_coe_unit_coprime a) (by norm_num) := by
  apply Units.ext
  simp [orbitNodeUnit,
    KummerCriterion.LehmerVandiver.cyclotomicUnitUnit,
    KummerCriterion.LehmerVandiver.cyclotomicUnit]
  rfl

/-- The plus-side lift of the canonical real cyclotomic node. -/
private noncomputable def canonicalPlusNode (a : (ZMod 59)ˣ) : (𝓞 K⁺)ˣ :=
  KummerCriterion.LehmerVandiver.Sinnott.realCyclotomicUnitPlusUnit
    59 K (ZMod.val_coe_unit_coprime a) (ZMod.val_lt (a : ZMod 59))
      (by norm_num)

private theorem plusUnitsEquivRealUnits_canonicalPlusNode
    (a : (ZMod 59)ˣ) :
    plusUnitsEquivRealUnits (K := K) (canonicalPlusNode (K := K) a) =
      realOrbitNode (IsCyclotomicExtension.zeta_spec 59 ℚ K) a := by
  apply Subtype.ext
  apply Units.ext
  change algebraMap (𝓞 K⁺) (𝓞 K)
      (canonicalPlusNode (K := K) a : 𝓞 K⁺) =
    ((orbitNodeUnit (IsCyclotomicExtension.zeta_spec 59 ℚ K) a *
      NumberField.IsCMField.unitsComplexConj K
      (orbitNodeUnit (IsCyclotomicExtension.zeta_spec 59 ℚ K) a) :
      (𝓞 K)ˣ) : 𝓞 K)
  rw [orbitNodeUnit_canonical (K := K) a]
  unfold canonicalPlusNode
  rw [KummerCriterion.LehmerVandiver.Sinnott.realCyclotomicUnitPlusUnit_val,
    KummerCriterion.LehmerVandiver.algebraMap_realCyclotomicUnitPlus]
  rfl

/-- The two orientations `a` and `-a` give the same folded real node. -/
private theorem realOrbitNode_canonical_neg (a : (ZMod 59)ˣ) :
    realOrbitNode (IsCyclotomicExtension.zeta_spec 59 ℚ K) (-a) =
      realOrbitNode (IsCyclotomicExtension.zeta_spec 59 ℚ K) a := by
  let root : (𝓞 K)ˣ :=
    (IsCyclotomicExtension.zeta_spec 59 ℚ K).unit'
  let d : ℕ := (a : ZMod 59).val
  have ha0 : (a : ZMod 59) ≠ 0 := Units.ne_zero a
  have hnegval : ((-a : (ZMod 59)ˣ) : ZMod 59).val = 59 - d := by
    simp only [Units.val_neg, d]
    rw [ZMod.neg_val, if_neg ha0]
  have hpair :
      orbitNodeUnit (IsCyclotomicExtension.zeta_spec 59 ℚ K) a =
        (-root ^ d) *
          orbitNodeUnit (IsCyclotomicExtension.zeta_spec 59 ℚ K) (-a) := by
    rw [orbitNodeUnit_canonical (K := K) a,
      orbitNodeUnit_canonical (K := K) (-a)]
    apply Units.ext
    simp only [KummerCriterion.LehmerVandiver.cyclotomicUnitUnit_val,
      Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val]
    change
      KummerCriterion.LehmerVandiver.cyclotomicUnit 59 K d =
        -((IsCyclotomicExtension.zeta_spec 59 ℚ K).unit' : 𝓞 K) ^ d *
          KummerCriterion.LehmerVandiver.cyclotomicUnit 59 K
            ((-a : (ZMod 59)ˣ) : ZMod 59).val
    rw [hnegval]
    exact
      KummerCriterion.LehmerVandiver.cyclotomicUnit_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub
        (p := 59) (K := K) d (by
          dsimp only [d]
          exact ZMod.val_le _)
  have hrootT : root ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨59, by norm_num, by
      dsimp only [root]
      exact (IsCyclotomicExtension.zeta_spec 59 ℚ K).unit'_pow⟩
  have ht : -root ^ d ∈ NumberField.Units.torsion K := by
    rw [neg_eq_neg_one_mul]
    exact Subgroup.mul_mem _
      neg_one_mem_torsion
      (Subgroup.pow_mem _ hrootT d)
  rw [realOrbitNode, realOrbitNode, hpair,
    realProjection_torsion_mul (K := K)
      (⟨-root ^ d, ht⟩ : NumberField.Units.torsion K)]

private theorem canonicalPlusNode_neg (a : (ZMod 59)ˣ) :
    canonicalPlusNode (K := K) (-a) = canonicalPlusNode (K := K) a := by
  apply (plusUnitsEquivRealUnits (K := K)).injective
  rw [plusUnitsEquivRealUnits_canonicalPlusNode (K := K),
    plusUnitsEquivRealUnits_canonicalPlusNode (K := K),
    realOrbitNode_canonical_neg (K := K)]

private theorem canonicalPlusNode_mem_CPlus_of_val_le
    (a : (ZMod 59)ˣ) (hle : (a : ZMod 59).val ≤ 29) :
    canonicalPlusNode (K := K) a ∈
      KummerCriterion.CPlus (p := 59) (K := K) (by norm_num) := by
  have hpos : 0 < (a : ZMod 59).val :=
    ZMod.val_pos.mpr (Units.ne_zero a)
  by_cases hone : (a : ZMod 59).val = 1
  · have hunit : canonicalPlusNode (K := K) a = 1 := by
      apply (plusUnitsEquivRealUnits (K := K)).injective
      rw [map_one, plusUnitsEquivRealUnits_canonicalPlusNode (K := K)]
      apply Subtype.ext
      rw [realOrbitNode]
      apply Units.ext
      simp [orbitNodeUnit, hone, realProjection]
    rw [hunit]
    exact Subgroup.one_mem _
  · let i : Fin 28 := ⟨(a : ZMod 59).val - 2, by omega⟩
    have hi : i.val + 2 = (a : ZMod 59).val := by
      dsimp only [i]
      omega
    have heq :
        canonicalPlusNode (K := K) a =
          KummerCriterion.LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplus
            59 K (by norm_num) i := by
      unfold canonicalPlusNode
      unfold KummerCriterion.LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplus
      congr 2
      exact hi.symm
    rw [heq,
      ← KummerCriterion.CPlusGenerator_eq_cyclotomicUnitFamilyKplus
        (p := 59) (K := K) (by norm_num) i]
    exact KummerCriterion.CPlusGenerator_mem
      (p := 59) (K := K) (by norm_num) i

private theorem canonicalPlusNode_mem_CPlus (a : (ZMod 59)ˣ) :
    canonicalPlusNode (K := K) a ∈
      KummerCriterion.CPlus (p := 59) (K := K) (by norm_num) := by
  by_cases hle : (a : ZMod 59).val ≤ 29
  · exact canonicalPlusNode_mem_CPlus_of_val_le (K := K) a hle
  · have ha0 : (a : ZMod 59) ≠ 0 := Units.ne_zero a
    have hnegval :
        ((-a : (ZMod 59)ˣ) : ZMod 59).val =
          59 - (a : ZMod 59).val := by
      simp only [Units.val_neg]
      rw [ZMod.neg_val, if_neg ha0]
    rw [← canonicalPlusNode_neg (K := K) a]
    apply canonicalPlusNode_mem_CPlus_of_val_le (K := K)
    rw [hnegval]
    omega

private theorem realOrbitNode_canonical_mem_mappedCPlus (a : (ZMod 59)ˣ) :
    realOrbitNode (IsCyclotomicExtension.zeta_spec 59 ℚ K) a ∈
      mappedCPlus (K := K) := by
  rw [← plusUnitsEquivRealUnits_canonicalPlusNode (K := K) a]
  exact ⟨canonicalPlusNode (K := K) a,
    canonicalPlusNode_mem_CPlus (K := K) a, rfl⟩

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Ambient-field value of Credit's geometric node unit. -/
private theorem orbitNodeUnit_coe {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (a : (ZMod 59)ˣ) :
    (((orbitNodeUnit hζ a : (𝓞 K)ˣ) : 𝓞 K) : K) =
      (1 - ζ ^ (a : ZMod 59).val) / (1 - ζ) := by
  have hne : 1 - ζ ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hζ.ne_one (by norm_num)))
  simp only [orbitNodeUnit, IsUnit.unit_spec, map_sum, map_pow,
    ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  rw [eq_div_iff hne]
  calc
    (∑ j ∈ Finset.range (a : ZMod 59).val, ζ ^ j) * (1 - ζ) =
        -((ζ - 1) * ∑ j ∈ Finset.range (a : ZMod 59).val, ζ ^ j) := by
          ring
    _ = -(ζ ^ (a : ZMod 59).val - 1) := by rw [mul_geom_sum]
    _ = 1 - ζ ^ (a : ZMod 59).val := by ring

/-- Changing the primitive root expresses a geometric node as the quotient
of two nodes for the canonical primitive root. -/
private theorem orbitNodeUnit_eq_canonical_quotient {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) (a : (ZMod 59)ˣ) :
    ∃ τ : (ZMod 59)ˣ,
      orbitNodeUnit hζ a =
        orbitNodeUnit (IsCyclotomicExtension.zeta_spec 59 ℚ K) (τ * a) *
          (orbitNodeUnit
            (IsCyclotomicExtension.zeta_spec 59 ℚ K) τ)⁻¹ := by
  let h₀ : IsPrimitiveRoot ζ₀ 59 :=
    IsCyclotomicExtension.zeta_spec 59 ℚ K
  obtain ⟨t, ht, htcop, htroot⟩ := (h₀.isPrimitiveRoot_iff).mp hζ
  let τ : (ZMod 59)ˣ := ZMod.unitOfCoprime t htcop
  refine ⟨τ, ?_⟩
  have hτval : (τ : ZMod 59).val = t := by
    simpa only [τ, ZMod.coe_unitOfCoprime] using
      (ZMod.val_natCast_of_lt ht)
  have hmod :
      t * (a : ZMod 59).val ≡
        ((τ * a : (ZMod 59)ˣ) : ZMod 59).val [MOD 59] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    calc
      ((t * (a : ZMod 59).val : ℕ) : ZMod 59) =
          (t : ZMod 59) * ((a : ZMod 59).val : ZMod 59) := by
            norm_cast
      _ = (τ : ZMod 59) * (a : ZMod 59) := by
            rw [ZMod.natCast_zmod_val]
            rfl
      _ = ((τ * a : (ZMod 59)ˣ) : ZMod 59) := rfl
      _ =
          ((((τ * a : (ZMod 59)ˣ) : ZMod 59).val : ℕ) :
            ZMod 59) := by
              rw [ZMod.natCast_zmod_val]
  have hpow :
      ζ₀ ^ (t * (a : ZMod 59).val) =
        ζ₀ ^ ((τ * a : (ZMod 59)ˣ) : ZMod 59).val :=
    pow_eq_pow_of_modEq hmod h₀.pow_eq_one
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  apply NumberField.RingOfIntegers.ext
  simp only [Units.val_mul, map_mul,
    ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  rw [orbitNodeUnit_coe (K := K), orbitNodeUnit_coe (K := K),
    orbitNodeUnit_coe (K := K), ← htroot, hτval, ← pow_mul, hpow]
  have hbase : 1 - ζ₀ ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (h₀.ne_one (by norm_num)))
  have hrootpow : ζ₀ ^ t ≠ 1 := by
    rw [htroot]
    exact hζ.ne_one (by norm_num)
  have hroot : 1 - ζ₀ ^ t ≠ 0 :=
    sub_ne_zero.mpr hrootpow.symm
  field_simp

/-- Every node obtained from any primitive root lies in the transported
prime-conductor squared circular-unit subgroup. -/
private theorem realOrbitNode_mem_mappedCPlus {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) (a : (ZMod 59)ˣ) :
    realOrbitNode hζ a ∈ mappedCPlus (K := K) := by
  obtain ⟨τ, hτ⟩ :=
    orbitNodeUnit_eq_canonical_quotient (K := K) hζ a
  rw [realOrbitNode, hτ, realProjection_mul, realProjection_inv]
  exact Subgroup.mul_mem _
    (realOrbitNode_canonical_mem_mappedCPlus (K := K) (τ * a))
    (Subgroup.inv_mem _
      (realOrbitNode_canonical_mem_mappedCPlus (K := K) τ))

/-- The generated edge ledger is contained in the transported classical
squared circular-unit subgroup. -/
private theorem generatedSubledger_le_mappedCPlus {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    generatedSubledger hζ ≤ mappedCPlus (K := K) := by
  rw [generatedSubledger,
    Fermat.Conservation.Credit.Cycle.generatedSubledger,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact Subgroup.mul_mem _
    (realOrbitNode_mem_mappedCPlus (K := K) hζ
      (exponentCycle.point (i.val + 1)))
    (Subgroup.inv_mem _
      (realOrbitNode_mem_mappedCPlus (K := K) hζ
        (exponentCycle.point i.val)))

/-- The index direction actually consumed at the endpoint: a factor `59`
in the plus class number forces the same factor in generated capacity. -/
private theorem dvd_capacityIndex_of_dvd_classNumber {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59)
    (hclass :
      59 ∣ NumberField.classNumber
        (NumberField.maximalRealSubfield K)) :
    59 ∣ capacityIndex hζ := by
  rw [capacityIndex_eq_relIndex hζ]
  exact dvd_trans
    ((dvd_mappedCPlus_index_iff_dvd_classNumber (K := K)).mpr hclass)
    (Subgroup.index_dvd_of_le
      (generatedSubledger_le_mappedCPlus (K := K) hζ))

/-- The conductor-`59` bounded Sinnott bridge. -/
theorem boundedSinnottBridge {ζ : K}
    (hζ : IsPrimitiveRoot ζ 59) :
    BoundedSinnottBridge hζ := by
  intro hcapacity hclass
  exact hcapacity (dvd_capacityIndex_of_dvd_classNumber hζ hclass)

end

end Fermat.FiftyNine.Conservation.Credit
