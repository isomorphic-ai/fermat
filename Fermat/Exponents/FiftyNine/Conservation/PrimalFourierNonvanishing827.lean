/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Nonvanishing of the generated primal Fourier modes at 827

The old capacity certificate checked a nonsingular 28-by-28 half-orbit
matrix.  This module extends its residue calculation to all 58 embeddings
above 827 and identifies every entry with the actual global generated
circular unit.  A kernel-decided Fourier calculation then proves the sharp
result: every generated unit has nonzero coefficient in every nontrivial
even character mode.

The final theorem applies the explicit inverse place orientation from
`FourierPairingProjection827`; it does not silently identify the raw residue
index with the canonical place index.
-/
import Fermat.Exponents.FiftyNine.Conservation.PrimalOrbitResidue827
import Fermat.Exponents.FiftyNine.Conservation.FourierPairingProjection827

open scoped BigOperators NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827

open Polynomial
open Fermat.Conservation
open Fermat.FiftyNine.Conservation.CapacityCertificate
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

/-- The public evaluation rule for the residue logarithm used by the full
orbit certificate. -/
theorem residueLog_eq_of_symbol
    (u : (ZMod Credit.attestationPrime)ˣ) (m : ℕ)
    (h : ((u : ZMod Credit.attestationPrime) ^ (2 * 7)) =
      Credit.attestationRoot ^ m) :
    CapacityCertificate.residueLog (Additive.ofMul u) =
      (m : ZMod 59) := by
  have hroot :
      IsPrimitiveRoot CapacityCertificate.attestationRootUnit 59 := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [CapacityCertificate.attestationRootUnit] using
      (IsPrimitiveRoot.iff_orderOf.mpr Credit.attestationRoot_order :
        IsPrimitiveRoot Credit.attestationRoot 59)
  have hpower : CapacityCertificate.symbolPower u =
      (⟨CapacityCertificate.attestationRootUnit ^ m, m, rfl⟩ :
        Subgroup.zpowers CapacityCertificate.attestationRootUnit) := by
    apply Subtype.ext
    change u ^ (2 * 7) = CapacityCertificate.attestationRootUnit ^ m
    apply Units.ext
    simpa [CapacityCertificate.attestationRootUnit] using h
  simp only [CapacityCertificate.residueLog, AddMonoidHom.coe_comp,
    Function.comp_apply]
  have hpowerAdd :
      CapacityCertificate.symbolPower.toAdditive (Additive.ofMul u) =
        Additive.ofMul
          (⟨CapacityCertificate.attestationRootUnit ^ m, m, rfl⟩ :
            Subgroup.zpowers CapacityCertificate.attestationRootUnit) := by
    exact congrArg Additive.ofMul hpower
  rw [hpowerAdd]
  exact hroot.zmodEquivZPowers_symm_apply_pow m

/-! A fully computable 58-by-28 extension of the old capacity matrix. -/

/-- The geometric node evaluated at one of all 58 residue roots. -/
def orbitGeometricResidue827 (sigma : GaloisIndex59) (n : ℕ) :
    ZMod Credit.attestationPrime :=
  ∑ k ∈ Finset.range (CapacityCertificate.nodeExponent n),
    PrimalOrbitResidue827.orbitRoot827 sigma ^ k

/-- The real two-sided node evaluated at one residue root. -/
def orbitRealNodeResidue827 (sigma : GaloisIndex59) (n : ℕ) :
    ZMod Credit.attestationPrime :=
  orbitGeometricResidue827 sigma n *
    ∑ k ∈ Finset.range (CapacityCertificate.nodeExponent n),
      (PrimalOrbitResidue827.orbitRoot827 sigma)⁻¹ ^ k

/-- The generated edge residue on the full residue-root orbit. -/
def orbitEdgeResidue827 (sigma : GaloisIndex59)
    (i : Credit.LedgerNode) : ZMod Credit.attestationPrime :=
  orbitRealNodeResidue827 sigma (i.val + 1) /
    orbitRealNodeResidue827 sigma i.val

/-- The computable 58-by-28 discrete-log matrix of all generated edges. -/
def fullGeneratedMatrix827 :
    Matrix GaloisIndex59 Credit.LedgerNode (ZMod 59) :=
  fun sigma i ↦
    ∑ k : Fin 59,
      if orbitEdgeResidue827 sigma i ^ (2 * 7) =
          Credit.attestationRoot ^ k.val
      then (k.val : ZMod 59)
      else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every computed full-orbit entry records the actual fourteenth-power
residue symbol. -/
theorem fullGeneratedMatrix827_entry_certificate :
    ∀ sigma i,
      orbitEdgeResidue827 sigma i ^ (2 * 7) =
        Credit.attestationRoot ^ (fullGeneratedMatrix827 sigma i).val := by
  decide +kernel +revert

universe uK

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} (hZeta : IsPrimitiveRoot zeta 59)

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

private theorem complexConj_zeta
    (hZeta : IsPrimitiveRoot zeta 59) :
    NumberField.IsCMField.complexConj K zeta = zeta⁻¹ := by
  let u : (NumberField.RingOfIntegers K)ˣ :=
    CapacityCertificate.integralRootUnit hZeta
  have hupow : u ^ 59 = 1 := by
    apply Units.ext
    apply NumberField.RingOfIntegers.ext
    simpa [u, CapacityCertificate.integralRootUnit] using hZeta.pow_eq_one
  have hutorsion : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨59, by norm_num, hupow⟩
  have hconj :
      NumberField.IsCMField.unitsComplexConj K u = u⁻¹ := by
    simpa using NumberField.IsCMField.unitsComplexConj_torsion
      (K := K) (⟨u, hutorsion⟩ : NumberField.Units.torsion K)
  have hval := congrArg Units.val hconj
  simpa [u, CapacityCertificate.integralRootUnit,
    NumberField.IsCMField.unitsComplexConj,
    NumberField.IsCMField.ringOfIntegersComplexConj,
    NumberField.RingOfIntegers.ext_iff] using
      congrArg ((↑) : NumberField.RingOfIntegers K → K) hval

private theorem orbitReductionHom827_orbitNodeUnit
    (sigma : GaloisIndex59) (a : (ZMod 59)ˣ) :
    PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (Credit.orbitNodeUnit hZeta a : NumberField.RingOfIntegers K) =
      ∑ k ∈ Finset.range (ZMod.val (a : ZMod 59)),
        PrimalOrbitResidue827.orbitRoot827 sigma ^ k := by
  simp [Credit.orbitNodeUnit,
    PrimalOrbitResidue827.orbitReductionHom827_zeta]

private theorem unitsComplexConj_orbitNodeUnit_val
    (a : (ZMod 59)ˣ) :
    (NumberField.IsCMField.unitsComplexConj K
        (Credit.orbitNodeUnit hZeta a) :
          NumberField.RingOfIntegers K) =
      ∑ k ∈ Finset.range (ZMod.val (a : ZMod 59)),
        ((((CapacityCertificate.integralRootUnit hZeta)⁻¹ :
          (NumberField.RingOfIntegers K)ˣ) ^ k :
          (NumberField.RingOfIntegers K)ˣ) :
            NumberField.RingOfIntegers K) := by
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K
      (((Credit.orbitNodeUnit hZeta a :
        (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K) = _
  simp only [Credit.orbitNodeUnit, Units.val_pow_eq_pow_val,
    map_sum, map_pow, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  simp [complexConj_zeta hZeta,
    CapacityCertificate.integralRootUnit]

private theorem orbitReductionHom827_conjugate_orbitNodeUnit
    (sigma : GaloisIndex59) (a : (ZMod 59)ˣ) :
    PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (NumberField.IsCMField.unitsComplexConj K
          (Credit.orbitNodeUnit hZeta a) :
            NumberField.RingOfIntegers K) =
      ∑ k ∈ Finset.range (ZMod.val (a : ZMod 59)),
        (PrimalOrbitResidue827.orbitRoot827 sigma)⁻¹ ^ k := by
  rw [unitsComplexConj_orbitNodeUnit_val hZeta]
  simp [CapacityCertificate.integralRootUnit,
    PrimalOrbitResidue827.orbitReductionHom827_zeta]

private theorem orbitReductionHom827_realOrbitNode
    (sigma : GaloisIndex59) (a : (ZMod 59)ˣ) :
    PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (Credit.realOrbitNode hZeta a :
          (NumberField.RingOfIntegers K)ˣ) =
      (∑ k ∈ Finset.range (ZMod.val (a : ZMod 59)),
          PrimalOrbitResidue827.orbitRoot827 sigma ^ k) *
        ∑ k ∈ Finset.range (ZMod.val (a : ZMod 59)),
          (PrimalOrbitResidue827.orbitRoot827 sigma)⁻¹ ^ k := by
  rw [Credit.realOrbitNode,
    Fermat.Conservation.Credit.Flow.realCyclotomicOrbitNode_val]
  simp only [Units.val_mul, map_mul]
  change
    PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (Credit.orbitNodeUnit hZeta a :
          NumberField.RingOfIntegers K) *
      PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (NumberField.IsCMField.unitsComplexConj K
          (Credit.orbitNodeUnit hZeta a) :
            NumberField.RingOfIntegers K) = _
  rw [orbitReductionHom827_orbitNodeUnit hZeta,
    orbitReductionHom827_conjugate_orbitNodeUnit hZeta]

set_option maxHeartbeats 0 in
/-- Each actual generated circular unit reduces to its corresponding
computable full-orbit edge residue. -/
theorem orbitReductionHom827_generatedUnit_eq
    (sigma : GaloisIndex59) (i : Credit.LedgerNode) :
    PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (Credit.generatedUnit hZeta i :
          (NumberField.RingOfIntegers K)ˣ) =
      orbitEdgeResidue827 sigma i := by
  rw [Credit.generatedUnit_eq_orbit_ratio]
  change PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
      ((((Credit.realOrbitNode hZeta
            (Credit.exponentCycle.point (i.val + 1))).1 *
          (Credit.realOrbitNode hZeta
            (Credit.exponentCycle.point i.val)).1⁻¹ :
              (NumberField.RingOfIntegers K)ˣ) :
                NumberField.RingOfIntegers K)) = _
  change ((Units.map
      (PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma)
        ((Credit.realOrbitNode hZeta
            (Credit.exponentCycle.point (i.val + 1))).1 *
          (Credit.realOrbitNode hZeta
            (Credit.exponentCycle.point i.val)).1⁻¹) :
              (ZMod Credit.attestationPrime)ˣ) :
                ZMod Credit.attestationPrime) = _
  rw [map_mul, map_inv]
  rw [Units.val_mul, Units.val_inv_eq_inv_val,
    Units.coe_map, Units.coe_map]
  have hnext :
      (↑(PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma) :
          NumberField.RingOfIntegers K → ZMod Credit.attestationPrime)
          (Credit.realOrbitNode hZeta
            (Credit.exponentCycle.point (i.val + 1))).1.1 =
        (∑ k ∈ Finset.range
              (ZMod.val ((Credit.exponentCycle.point (i.val + 1) :
                (ZMod 59)ˣ) : ZMod 59)),
            PrimalOrbitResidue827.orbitRoot827 sigma ^ k) *
          ∑ k ∈ Finset.range
              (ZMod.val ((Credit.exponentCycle.point (i.val + 1) :
                (ZMod 59)ˣ) : ZMod 59)),
            (PrimalOrbitResidue827.orbitRoot827 sigma)⁻¹ ^ k := by
    exact orbitReductionHom827_realOrbitNode hZeta sigma _
  have hprev :
      (↑(PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma) :
          NumberField.RingOfIntegers K → ZMod Credit.attestationPrime)
          (Credit.realOrbitNode hZeta
            (Credit.exponentCycle.point i.val)).1.1 =
        (∑ k ∈ Finset.range
              (ZMod.val ((Credit.exponentCycle.point i.val :
                (ZMod 59)ˣ) : ZMod 59)),
            PrimalOrbitResidue827.orbitRoot827 sigma ^ k) *
          ∑ k ∈ Finset.range
              (ZMod.val ((Credit.exponentCycle.point i.val :
                (ZMod 59)ˣ) : ZMod 59)),
            (PrimalOrbitResidue827.orbitRoot827 sigma)⁻¹ ^ k := by
    exact orbitReductionHom827_realOrbitNode hZeta sigma _
  change
    PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (Credit.realOrbitNode hZeta
          (Credit.exponentCycle.point (i.val + 1))).1.1 *
      (PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma
        (Credit.realOrbitNode hZeta
          (Credit.exponentCycle.point i.val)).1.1)⁻¹ = _
  rw [hnext, hprev, Credit.exponentCycle_point,
    Credit.exponentCycle_point]
  rfl

@[simp]
private theorem realNorm_generatedUnit
    (i : Credit.LedgerNode) :
    CapacityCertificate.realNorm
        (Credit.generatedUnit hZeta i :
          (NumberField.RingOfIntegers K)ˣ) =
      (Credit.generatedUnit hZeta i :
        (NumberField.RingOfIntegers K)ˣ) ^ 2 := by
  change (Credit.generatedUnit hZeta i :
      (NumberField.RingOfIntegers K)ˣ) *
      NumberField.IsCMField.unitsComplexConj K
        (Credit.generatedUnit hZeta i :
          (NumberField.RingOfIntegers K)ˣ) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (Credit.generatedUnit hZeta i).2]
  exact (pow_two _).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The actual full-orbit unit reading is exactly the computable full
generated matrix. -/
theorem fullOrbitUnitReading827_generatedUnit_eq
    (sigma : GaloisIndex59) (i : Credit.LedgerNode) :
    PrimalOrbitResidue827.fullOrbitUnitReading827 hZeta
        (Credit.generatedUnit hZeta i :
          (NumberField.RingOfIntegers K)ˣ) sigma =
      fullGeneratedMatrix827 sigma i := by
  let u : (ZMod Credit.attestationPrime)ˣ :=
    Units.map (PrimalOrbitResidue827.orbitReductionHom827 hZeta sigma)
      (CapacityCertificate.realNorm
        (Credit.generatedUnit hZeta i :
          (NumberField.RingOfIntegers K)ˣ))
  have huval :
      (u : ZMod Credit.attestationPrime) =
        orbitEdgeResidue827 sigma i ^ 2 := by
    dsimp [u]
    rw [realNorm_generatedUnit hZeta i, Units.val_pow_eq_pow_val,
      map_pow, orbitReductionHom827_generatedUnit_eq hZeta]
  have hsymbol :
      (u : ZMod Credit.attestationPrime) ^ (2 * 7) =
        Credit.attestationRoot ^
          ((fullGeneratedMatrix827 sigma i).val * 2) := by
    calc
      (u : ZMod Credit.attestationPrime) ^ (2 * 7) =
          (orbitEdgeResidue827 sigma i ^ 2) ^ (2 * 7) := by
            rw [huval]
      _ = (orbitEdgeResidue827 sigma i ^ (2 * 7)) ^ 2 := by
        simp only [← pow_mul]
      _ = (Credit.attestationRoot ^
          (fullGeneratedMatrix827 sigma i).val) ^ 2 := by
        rw [fullGeneratedMatrix827_entry_certificate]
      _ = Credit.attestationRoot ^
          ((fullGeneratedMatrix827 sigma i).val * 2) := by
        rw [pow_mul]
  change (2 : ZMod 59)⁻¹ *
      CapacityCertificate.residueLog (Additive.ofMul u) =
    fullGeneratedMatrix827 sigma i
  rw [residueLog_eq_of_symbol u _ hsymbol, Nat.cast_mul,
    ZMod.natCast_zmod_val]
  have htwo : (2 : ZMod 59) ≠ 0 := by decide
  calc
    (2 : ZMod 59)⁻¹ * (fullGeneratedMatrix827 sigma i * 2) =
        (2⁻¹ * 2) * fullGeneratedMatrix827 sigma i := by ring
    _ = fullGeneratedMatrix827 sigma i := by
      rw [inv_mul_cancel₀ htwo, one_mul]

/-- The power character indexed by its exponent modulo 58. -/
def powerCharacter59 (t : ZMod 58) :
    GaloisIndex59 →* (ZMod 59)ˣ where
  toFun sigma := sigma ^ t.val
  map_one' := by simp
  map_mul' sigma tau := by simp [mul_pow]

/-- Evaluation of a power character is exponentiation by its index. -/
@[simp]
theorem powerCharacter59_apply (t : ZMod 58) (sigma : GaloisIndex59) :
    powerCharacter59 t sigma = sigma ^ t.val := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first generator's first nontrivial even Fourier coefficient is the
explicit nonzero value `23`. -/
theorem firstGenerated_powerTwo_fourierCoefficient_eq :
    SplitPrimeFourier827.fourierCoefficient
        (fun sigma ↦ fullGeneratedMatrix827 sigma
          (⟨0, by norm_num [Credit.exponentCycle_rank]⟩ : Credit.LedgerNode))
        (powerCharacter59 2) = 23 := by
  decide +kernel +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every generated column has nonzero coefficient in every nontrivial even
power-character row.  This checks all `28 × 28` entries in the kernel. -/
theorem fullGeneratedMatrix827_powerFourier_ne_zero :
    ∀ (t : ZMod 58), Even t.val → t ≠ 0 →
      ∀ (i : Credit.LedgerNode),
        SplitPrimeFourier827.fourierCoefficient
          (fun sigma ↦ fullGeneratedMatrix827 sigma i)
          (powerCharacter59 t) ≠ 0 := by
  decide +kernel +revert

/-- Every residue-field character of the cyclic Galois index is a power
character. -/
theorem exists_powerCharacter59
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    ∃ t : ZMod 58, eta = powerCharacter59 t := by
  obtain ⟨m, hm⟩ := eta.map_cyclic
  let t : ZMod 58 := m
  refine ⟨t, ?_⟩
  apply MonoidHom.ext
  intro sigma
  rw [hm]
  change sigma ^ m = sigma ^ t.val
  have hsigma : sigma ^ (58 : ℕ) = 1 := by
    rw [← galoisIndex59_card]
    exact pow_card_eq_one
  calc
    sigma ^ m = sigma ^ (m % (58 : ℤ)) :=
      zpow_eq_zpow_emod' m hsigma
    _ = sigma ^ (t.val : ℤ) := by
      rw [show (t.val : ℤ) = m % (58 : ℤ) by
        exact ZMod.val_intCast m]
    _ = sigma ^ t.val := by rw [zpow_natCast]

/-- Every actual generated circular unit has a nonzero coefficient in every
nontrivial even raw Fourier mode. -/
theorem fullOrbitUnitReading827_generatedUnit_fourier_ne_zero_of_even_nontrivial
    (eta : GaloisIndex59 →* (ZMod 59)ˣ)
    (heven : eta (-1) = 1) (hne : eta ≠ 1)
    (i : Credit.LedgerNode) :
    SplitPrimeFourier827.fourierCoefficient
        (PrimalOrbitResidue827.fullOrbitUnitReading827 hZeta
          (Credit.generatedUnit hZeta i :
            (NumberField.RingOfIntegers K)ˣ)) eta ≠ 0 := by
  obtain ⟨t, heta⟩ := exists_powerCharacter59 eta
  have hevenPower : powerCharacter59 t (-1) = 1 := by
    rw [← heta]
    exact heven
  have htEven : Even t.val := by
    apply (neg_one_pow_eq_one_iff_even (R := GaloisIndex59) ?_).mp
    · exact hevenPower
    · decide
  have htne : t ≠ 0 := by
    intro ht
    apply hne
    rw [heta, ht]
    ext sigma
    simp [powerCharacter59]
  have hvector :
      PrimalOrbitResidue827.fullOrbitUnitReading827 hZeta
          (Credit.generatedUnit hZeta i :
            (NumberField.RingOfIntegers K)ˣ) =
        fun sigma ↦ fullGeneratedMatrix827 sigma i := by
    funext sigma
    exact fullOrbitUnitReading827_generatedUnit_eq hZeta sigma i
  rw [hvector, heta]
  exact fullGeneratedMatrix827_powerFourier_ne_zero t htEven htne i

/-- The place-oriented coefficient is the inverse-character coefficient of
the raw residue orbit, and it is nonzero under the same honest parity and
nontriviality hypotheses. -/
theorem inverseReindex_fullOrbitUnitReading827_generatedUnit_fourier_ne_zero
    (eta : GaloisIndex59 →* (ZMod 59)ˣ)
    (heven : eta (-1) = 1) (hne : eta ≠ 1)
    (i : Credit.LedgerNode) :
    SplitPrimeFourier827.fourierCoefficient
        (FourierPairingProjection827.inverseReindex
          (PrimalOrbitResidue827.fullOrbitUnitReading827 hZeta
            (Credit.generatedUnit hZeta i :
              (NumberField.RingOfIntegers K)ˣ))) eta ≠ 0 := by
  rw [FourierPairingProjection827.fourierCoefficient_inverseReindex]
  apply
    fullOrbitUnitReading827_generatedUnit_fourier_ne_zero_of_even_nontrivial
      hZeta eta⁻¹
  · simp [MonoidHom.inv_apply, heven]
  · intro hinv
    apply hne
    apply MonoidHom.ext
    intro sigma
    have hsigma := DFunLike.congr_fun hinv sigma
    change (eta sigma)⁻¹ = 1 at hsigma
    exact inv_eq_one.mp hsigma

end Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
