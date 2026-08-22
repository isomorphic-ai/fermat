/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# W1: relation polynomial evaluation bridge

This layer evaluates the normalized relation polynomials at a primitive
cyclotomic root and identifies the result with the generated real-unit
edge relation.  A deep unit relation then supplies the exact scalar-bearing
polynomial depth hypothesis consumed by the nonlinear moment flow.

The construction is generic over the prime and contains no
conductor-specific arithmetic.
-/
import Fermat.Experiments.Conservation.Credit.RelationDepthFlow
import Fermat.Experiments.Conservation.Credit.CyclotomicFlow
import Fermat.Experiments.Conservation.Credit.Repayment

open scoped BigOperators NumberField

namespace Fermat.Conservation.Credit.RealFlow

open NumberField Polynomial

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
theorem eval₂_geometricPolynomial (r : ℕ) :
    Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (geometricPolynomial r) =
      ∑ j ∈ Finset.range r, hζ.toInteger ^ j := by
  rw [geometricPolynomial, Polynomial.eval₂_finsetSum]
  simp

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
theorem geom_sum_teichLift_eq_geom_sum_val (a : (ZMod p)ˣ) :
    (∑ j ∈ Finset.range (teichLift p a), hζ.toInteger ^ j) =
      ∑ j ∈ Finset.range (a : ZMod p).val, hζ.toInteger ^ j := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmod :
      teichLift p a ≡ (a : ZMod p).val [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [natCast_teichLift, ZMod.natCast_zmod_val]
  have hpow :
      hζ.toInteger ^ teichLift p a =
        hζ.toInteger ^ (a : ZMod p).val :=
    pow_eq_pow_of_modEq hmod hζ.toInteger_isPrimitiveRoot.pow_eq_one
  apply mul_right_cancel₀
      (sub_ne_zero.mpr
        (hζ.toInteger_isPrimitiveRoot.ne_one
          (Fact.out : p.Prime).one_lt))
  rw [geom_sum_mul, geom_sum_mul, hpow]

omit [IsCyclotomicExtension {p} ℚ K] in
include hζ in
theorem geom_sum_inv_eq_fold
    (r : ℕ) (hrlt : r < p) :
    (∑ j ∈ Finset.range r, ζ⁻¹ ^ j) =
      ζ ^ (p + 1 - r) * ∑ j ∈ Finset.range r, ζ ^ j := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hζ0 : ζ ≠ 0 :=
    hζ.ne_zero (Fact.out : p.Prime).ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp1
  have hscale :
      ζ ^ (p + 1 - r) = ζ⁻¹ ^ r * ζ := by
    apply mul_right_cancel₀ (pow_ne_zero r hζ0)
    calc
      ζ ^ (p + 1 - r) * ζ ^ r =
          ζ ^ (p + 1 - r + r) := (pow_add ζ _ _).symm
      _ = ζ ^ (p + 1) := by congr 1; omega
      _ = ζ := by rw [pow_succ, hζ.pow_eq_one, one_mul]
      _ = (ζ⁻¹ ^ r * ζ) * ζ ^ r := by
        rw [inv_pow]
        field_simp
  rw [geom_sum_inv hζ1 hζ0]
  apply mul_right_cancel₀ (sub_ne_zero.mpr hζ1)
  calc
    ((ζ - 1)⁻¹ * (ζ - ζ⁻¹ ^ r * ζ)) * (ζ - 1) =
        ζ - ζ⁻¹ ^ r * ζ := by
      field_simp [sub_ne_zero.mpr hζ1]
    _ = ζ ^ (p + 1 - r) * (ζ ^ r - 1) := by
      rw [hscale]
      have hinvpow : ζ⁻¹ ^ r * ζ ^ r = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hζ0, one_pow]
      have hproduct : ζ⁻¹ ^ r * ζ * ζ ^ r = ζ := by
        calc
          ζ⁻¹ ^ r * ζ * ζ ^ r =
              ζ * (ζ⁻¹ ^ r * ζ ^ r) := by ring
          _ = ζ := by rw [hinvpow, mul_one]
      calc
        ζ - ζ⁻¹ ^ r * ζ =
            (ζ⁻¹ ^ r * ζ * ζ ^ r) - ζ⁻¹ ^ r * ζ := by
              rw [hproduct]
        _ = ζ⁻¹ ^ r * ζ * (ζ ^ r - 1) := by ring
    _ = (ζ ^ (p + 1 - r) *
        ∑ j ∈ Finset.range r, ζ ^ j) * (ζ - 1) := by
      rw [mul_assoc, geom_sum_mul]

section CM

variable [NumberField.IsCMField K]

omit [IsCyclotomicExtension {p} ℚ K] in
include hζ in
theorem complexConj_primitiveRoot :
    NumberField.IsCMField.complexConj K ζ = ζ⁻¹ := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ζunit : (𝓞 K)ˣ :=
    (hζ.toInteger_isPrimitiveRoot.isUnit
      (Fact.out : p.Prime).ne_zero).unit
  have hζunitPow : ζunit ^ p = 1 := by
    apply Units.ext
    exact hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hmem : ζunit ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨p, (Fact.out : p.Prime).pos, hζunitPow⟩
  simpa [ζunit] using
    NumberField.IsCMField.complexConj_torsion
      (K := K) (⟨ζunit, hmem⟩ : NumberField.Units.torsion K)

omit [IsCyclotomicExtension {p} ℚ K] in
theorem eval₂_foldedTeichNodePolynomial
    (a : (ZMod p)ˣ) :
    Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (foldedTeichNodePolynomial p a) =
      (((Flow.realCyclotomicOrbitNode hζ a :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) : 𝓞 K) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hrlt : (a : ZMod p).val < p := ZMod.val_lt _
  have hcoe :
      algebraMap (𝓞 K) K hζ.toInteger = ζ :=
    rfl
  have hconj :
      ((NumberField.IsCMField.unitsComplexConj K
        (Flow.cyclotomicOrbitNodeUnit hζ a) : 𝓞 K) : K) =
        ∑ j ∈ Finset.range (a : ZMod p).val, ζ⁻¹ ^ j := by
    change
      NumberField.IsCMField.complexConj K
          (((Flow.cyclotomicOrbitNodeUnit hζ a : 𝓞 K) : K)) =
        _
    rw [Flow.cyclotomicOrbitNodeUnit_val]
    simp only [map_sum, map_pow, hcoe]
    rw [complexConj_primitiveRoot hζ]
  have hgeom :
      (∑ j ∈ Finset.range (teichLift p a), ζ ^ j) =
        ∑ j ∈ Finset.range (a : ZMod p).val, ζ ^ j := by
    have hgeomO := geom_sum_teichLift_eq_geom_sum_val hζ a
    simpa only [map_sum, map_pow, hcoe] using
      congrArg (fun x : 𝓞 K ↦ (x : K)) hgeomO
  have hinverse :=
    geom_sum_inv_eq_fold hζ (a : ZMod p).val hrlt
  apply RingOfIntegers.ext
  rw [foldedTeichNodePolynomial, Polynomial.eval₂_mul]
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [eval₂_geometricPolynomial]
  rw [Flow.realCyclotomicOrbitNode_val]
  change _ =
    ((Flow.cyclotomicOrbitNodeUnit hζ a : 𝓞 K) : K) *
      ((NumberField.IsCMField.unitsComplexConj K
        (Flow.cyclotomicOrbitNodeUnit hζ a) : 𝓞 K) : K)
  rw [Flow.cyclotomicOrbitNodeUnit_val]
  simp only [map_mul, map_pow, map_sum, hcoe]
  rw [hconj, hgeom, hinverse]
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
theorem eval₂_normalizedNodePolynomial
    (data : RealGauge.RealGaugeData p) (i : ℕ) :
    Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (normalizedNodePolynomial data i) =
      ((((Flow.indexedRealCyclotomicOrbitNode data hζ i :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) : 𝓞 K) ^
        (p - 1)) := by
  rw [normalizedNodePolynomial, normalizedFoldedNodePolynomial,
    Polynomial.eval₂_pow, eval₂_foldedTeichNodePolynomial]
  rfl

theorem positive_negative_edge_identity
    {G : Type*} [CommGroup G] (x y : G) (z : ℤ) :
    x ^ positiveExponent z * y ^ negativeExponent z =
      y ^ positiveExponent z * x ^ negativeExponent z *
        (x * y⁻¹) ^ z := by
  cases z with
  | ofNat n =>
      simp [positiveExponent, negativeExponent, mul_pow]
  | negSucc n =>
      simp [positiveExponent, negativeExponent, mul_pow]

/-- Unit represented by one normalized node polynomial. -/
noncomputable def normalizedNodeUnit
    (data : RealGauge.RealGaugeData p) (i : ℕ) : (𝓞 K)ˣ :=
  ((Flow.indexedRealCyclotomicOrbitNode data hζ i :
      NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) ^ (p - 1)

/-- Unit represented by the normalized relation numerator. -/
noncomputable def relationNumeratorUnit
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : (𝓞 K)ˣ :=
  ∏ i,
    normalizedNodeUnit hζ data (i.val + 1) ^
        positiveExponent (raw i) *
      normalizedNodeUnit hζ data i.val ^
        negativeExponent (raw i)

/-- Unit represented by the normalized relation denominator. -/
noncomputable def relationDenominatorUnit
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : (𝓞 K)ˣ :=
  ∏ i,
    normalizedNodeUnit hζ data i.val ^
        positiveExponent (raw i) *
      normalizedNodeUnit hζ data (i.val + 1) ^
        negativeExponent (raw i)

omit [IsCyclotomicExtension {p} ℚ K] in
theorem eval₂_relationNumerator
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (relationNumerator data raw) =
      (relationNumeratorUnit hζ data raw : 𝓞 K) := by
  rw [relationNumerator, Polynomial.eval₂_finsetProd]
  rw [relationNumeratorUnit]
  rw [show
    ((∏ i,
      normalizedNodeUnit hζ data (i.val + 1) ^
          positiveExponent (raw i) *
        normalizedNodeUnit hζ data i.val ^
          negativeExponent (raw i) : (𝓞 K)ˣ) : 𝓞 K) =
      ∏ i,
        ((normalizedNodeUnit hζ data (i.val + 1) ^
              positiveExponent (raw i) *
            normalizedNodeUnit hζ data i.val ^
              negativeExponent (raw i) : (𝓞 K)ˣ) : 𝓞 K) by
    exact map_prod (Units.coeHom (𝓞 K)) _ _]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_pow, eval₂_normalizedNodePolynomial,
    eval₂_normalizedNodePolynomial]
  rfl

omit [IsCyclotomicExtension {p} ℚ K] in
theorem eval₂_relationDenominator
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (relationDenominator data raw) =
      (relationDenominatorUnit hζ data raw : 𝓞 K) := by
  rw [relationDenominator, Polynomial.eval₂_finsetProd]
  rw [relationDenominatorUnit]
  rw [show
    ((∏ i,
      normalizedNodeUnit hζ data i.val ^
          positiveExponent (raw i) *
        normalizedNodeUnit hζ data (i.val + 1) ^
          negativeExponent (raw i) : (𝓞 K)ˣ) : 𝓞 K) =
      ∏ i,
        ((normalizedNodeUnit hζ data i.val ^
              positiveExponent (raw i) *
            normalizedNodeUnit hζ data (i.val + 1) ^
              negativeExponent (raw i) : (𝓞 K)ˣ) : 𝓞 K) by
    exact map_prod (Units.coeHom (𝓞 K)) _ _]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_pow, eval₂_normalizedNodePolynomial,
    eval₂_normalizedNodePolynomial]
  rfl

omit [IsCyclotomicExtension {p} ℚ K] in
theorem realize_cycle_point
    (data : RealGauge.RealGaugeData p) (i : ℕ) :
    Flow.realCyclotomicOrbitNodeQuotient hζ (data.cycle.point i) =
      Flow.indexedRealCyclotomicOrbitNode data hζ i := by
  rw [← data.mk_nodeLift i]
  rfl

/-- Underlying ring-of-integers unit of one realized generated edge. -/
noncomputable def edgeUnit
    (data : RealGauge.RealGaugeData p)
    (i : Fin data.rank) : (𝓞 K)ˣ :=
  ((data.cycle.edge (Flow.realCyclotomicOrbitNodeQuotient hζ) i :
      NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ)

omit [IsCyclotomicExtension {p} ℚ K] in
theorem normalizedNodeUnit_edge
    (data : RealGauge.RealGaugeData p)
    (i : Fin data.rank) :
    normalizedNodeUnit hζ data (i.val + 1) *
        (normalizedNodeUnit hζ data i.val)⁻¹ =
      edgeUnit hζ data i ^ (p - 1) := by
  rw [normalizedNodeUnit, normalizedNodeUnit, edgeUnit,
    Credit.Cycle.edge, realize_cycle_point, realize_cycle_point]
  change
    (((Flow.indexedRealCyclotomicOrbitNode data hζ (i.val + 1) :
        NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) ^ (p - 1) *
      (((Flow.indexedRealCyclotomicOrbitNode data hζ i.val :
        NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) ^ (p - 1))⁻¹) =
      ((((Flow.indexedRealCyclotomicOrbitNode data hζ (i.val + 1) :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) *
        ((Flow.indexedRealCyclotomicOrbitNode data hζ i.val :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ)⁻¹) ^ (p - 1))
  rw [mul_pow, inv_pow]

omit [IsCyclotomicExtension {p} ℚ K] in
theorem relationNumeratorUnit_eq_denominator_mul_normalizedEdges
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    relationNumeratorUnit hζ data raw =
      relationDenominatorUnit hζ data raw *
        ∏ i,
          (normalizedNodeUnit hζ data (i.val + 1) *
            (normalizedNodeUnit hζ data i.val)⁻¹) ^ raw i := by
  rw [relationNumeratorUnit, relationDenominatorUnit,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact positive_negative_edge_identity
    (normalizedNodeUnit hζ data (i.val + 1))
    (normalizedNodeUnit hζ data i.val) (raw i)

/-- The raw realized edge product, viewed in ring-of-integers units. -/
noncomputable def rawEdgeProductUnit
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : (𝓞 K)ˣ :=
  ∏ i, edgeUnit hζ data i ^ raw i

omit [IsCyclotomicExtension {p} ℚ K] in
theorem normalizedEdges_eq_rawEdgeProductUnit_pow
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    (∏ i,
      (normalizedNodeUnit hζ data (i.val + 1) *
        (normalizedNodeUnit hζ data i.val)⁻¹) ^ raw i) =
      rawEdgeProductUnit hζ data raw ^ (p - 1) := by
  rw [rawEdgeProductUnit, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [normalizedNodeUnit_edge]
  calc
    (edgeUnit hζ data i ^ (p - 1)) ^ raw i =
        (edgeUnit hζ data i ^ ((p - 1 : ℕ) : ℤ)) ^ raw i := by
          rw [zpow_natCast]
    _ = (edgeUnit hζ data i ^ raw i) ^
        ((p - 1 : ℕ) : ℤ) := zpow_comm _ _ _
    _ = (edgeUnit hζ data i ^ raw i) ^ (p - 1) := by
      rw [zpow_natCast]

omit [IsCyclotomicExtension {p} ℚ K] in
theorem relationNumeratorUnit_eq_denominator_mul_rawEdgeProduct_pow
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    relationNumeratorUnit hζ data raw =
      relationDenominatorUnit hζ data raw *
        rawEdgeProductUnit hζ data raw ^ (p - 1) := by
  rw [relationNumeratorUnit_eq_denominator_mul_normalizedEdges,
    normalizedEdges_eq_rawEdgeProductUnit_pow]

/-- The same raw edge product in the real-unit subgroup used by the
relation supplied to W1. -/
noncomputable def rawEdgeProduct
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    NumberField.IsCMField.realUnits K :=
  ∏ i,
    data.cycle.edge (Flow.realCyclotomicOrbitNodeQuotient hζ) i ^
      raw i

omit [IsCyclotomicExtension {p} ℚ K] in
theorem rawEdgeProductUnit_eq_coe
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    rawEdgeProductUnit hζ data raw =
      ((rawEdgeProduct hζ data raw :
        NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) := by
  rw [rawEdgeProductUnit, rawEdgeProduct]
  change
    (∏ i,
      ((data.cycle.edge
        (Flow.realCyclotomicOrbitNodeQuotient hζ) i :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) ^ raw i) =
      (NumberField.IsCMField.realUnits K).subtype
        (∏ i,
          data.cycle.edge
            (Flow.realCyclotomicOrbitNodeQuotient hζ) i ^ raw i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_zpow]
  rfl

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Cross-multiplied polynomial evaluation of the normalized raw edge
relation. -/
theorem eval₂_relationNumerator_eq_denominator_mul_rawEdgeProduct_pow
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (relationNumerator data raw) =
      Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
          (relationDenominator data raw) *
        ((((rawEdgeProduct hζ data raw :
            NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) : 𝓞 K) ^
          (p - 1)) := by
  rw [eval₂_relationNumerator, eval₂_relationDenominator]
  have hunit :=
    relationNumeratorUnit_eq_denominator_mul_rawEdgeProduct_pow
      hζ data raw
  rw [rawEdgeProductUnit_eq_coe] at hunit
  exact congrArg Units.val hunit

omit [IsCyclotomicExtension {p} ℚ K] in
/-- An explicit deep scalar witness supplies the corresponding
scalar-bearing polynomial depth hypothesis. -/
theorem relation_polynomial_depth_of_deep_witness
    (data : RealGauge.RealGaugeData p)
    (u : NumberField.IsCMField.realUnits K)
    (c : ℤ) (t : ℕ) (raw : Fin data.rank → ℤ)
    (hc :
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        ((u : (𝓞 K)ˣ) : 𝓞 K) - (c : 𝓞 K) ^ p)
    (hrelation : u ^ t = rawEdgeProduct hζ data raw) :
    ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
      Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (relationNumerator data raw -
          Polynomial.C (c ^ (p * t * (p - 1))) *
            relationDenominator data raw) := by
  have hpowerT :
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        (((u : (𝓞 K)ˣ) : 𝓞 K) ^ t -
          ((c : 𝓞 K) ^ p) ^ t) :=
    hc.trans (sub_dvd_pow_sub_pow
      (((u : (𝓞 K)ˣ) : 𝓞 K)) ((c : 𝓞 K) ^ p) t)
  have hpowerPred :
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        ((((u : (𝓞 K)ˣ) : 𝓞 K) ^ t) ^ (p - 1) -
          (((c : 𝓞 K) ^ p) ^ t) ^ (p - 1)) :=
    hpowerT.trans (sub_dvd_pow_sub_pow
      ((((u : (𝓞 K)ˣ) : 𝓞 K) ^ t))
      (((c : 𝓞 K) ^ p) ^ t) (p - 1))
  have hscalar :
      (((c : 𝓞 K) ^ p) ^ t) ^ (p - 1) =
        ((c ^ (p * t * (p - 1)) : ℤ) : 𝓞 K) := by
    push_cast
    simp only [← pow_mul]
  have hrelationO :
      (((u : (𝓞 K)ˣ) : 𝓞 K) ^ t) =
        ((((rawEdgeProduct hζ data raw :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) : 𝓞 K)) := by
    exact congrArg
      (fun v : NumberField.IsCMField.realUnits K ↦
        (((v : (𝓞 K)ˣ) : 𝓞 K))) hrelation
  have hraw :
      (((((rawEdgeProduct hζ data raw :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) : 𝓞 K)) ^
          (p - 1)) =
        ((((u : (𝓞 K)ˣ) : 𝓞 K) ^ t) ^ (p - 1)) :=
    congrArg (fun x : 𝓞 K ↦ x ^ (p - 1)) hrelationO.symm
  have heval :=
    eval₂_relationNumerator_eq_denominator_mul_rawEdgeProduct_pow
      hζ data raw
  have hdifference :
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        ((((u : (𝓞 K)ˣ) : 𝓞 K) ^ t) ^ (p - 1) -
          ((c ^ (p * t * (p - 1)) : ℤ) : 𝓞 K)) := by
    rw [← hscalar]
    exact hpowerPred
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, heval, hraw]
  have hmul :=
    dvd_mul_of_dvd_right hdifference
      (Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
        (relationDenominator data raw))
  convert hmul using 1
  rw [show
    (algebraMap ℤ (𝓞 K)) (c ^ (p * t * (p - 1))) =
      ((c ^ (p * t * (p - 1)) : ℤ) : 𝓞 K) by rfl]
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- A deep unit relation supplies the exact scalar-bearing polynomial depth
hypothesis.  The scalar is retained as `c^(p*t*(p-1))`. -/
theorem exists_relation_polynomial_depth_of_vandiverDeep
    (data : RealGauge.RealGaugeData p)
    (u : NumberField.IsCMField.realUnits K)
    (t : ℕ) (raw : Fin data.rank → ℤ)
    (hdeep :
      Repayment.IsVandiverDeep p
        ((1 : 𝓞 K) - hζ.toInteger)
        (u : (𝓞 K)ˣ))
    (hrelation : u ^ t = rawEdgeProduct hζ data raw) :
    ∃ c : ℤ,
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
          (relationNumerator data raw -
            Polynomial.C (c ^ (p * t * (p - 1))) *
              relationDenominator data raw) := by
  obtain ⟨c, hc⟩ := hdeep
  exact ⟨c,
    relation_polynomial_depth_of_deep_witness
      hζ data u c t raw hc hrelation⟩

/-- A deep generated unit relation carries its original scalar witness into
the exact corrected relation consumed by the nonlinear moment flow. -/
theorem exists_moment_ready_relation_of_vandiverDeep
    (data : RealGauge.RealGaugeData p)
    (u : NumberField.IsCMField.realUnits K)
    (t : ℕ) (raw : Fin data.rank → ℤ)
    (hdeep :
      Repayment.IsVandiverDeep p
        ((1 : 𝓞 K) - hζ.toInteger)
        (u : (𝓞 K)ˣ))
    (hrelation : u ^ t = rawEdgeProduct hζ data raw) :
    ∃ c : ℤ, ∃ H B : ℤ[X],
      ((p : ℤ) ^ 2 ∣ c ^ (p * t * (p - 1)) - 1) ∧
      (relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C (c ^ (p * t * (p - 1))) *
            relationDenominator data raw =
        Polynomial.cyclotomic p ℤ * B ∧
      ((p : ℤ) ^ 2) ∣
        ((relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C (c ^ (p * t * (p - 1))) *
            relationDenominator data raw).eval 1 := by
  obtain ⟨c, hc⟩ := hdeep
  have hdepth :=
    relation_polynomial_depth_of_deep_witness
      hζ data u c t raw hc hrelation
  have hcNot : ¬(p : ℤ) ∣ c :=
    not_prime_dvd_scalar_of_deep_unit
      hζ (u : (𝓞 K)ˣ) c hc
  have hscalar :
      ((p : ℤ) ^ 2) ∣ c ^ (p * t * (p - 1)) - 1 :=
    prime_sq_dvd_scalar_power_sub_one c t hcNot
  have heval :=
    prime_sq_dvd_relation_scaled_difference_eval_one
      data raw (c ^ (p * t * (p - 1))) hscalar
  obtain ⟨H, B, hfactor, heval'⟩ :=
    exists_moment_ready_relation_of_depth hζ
      (relationNumerator data raw)
      (relationDenominator data raw)
      (c ^ (p * t * (p - 1))) hdepth heval
  exact ⟨c, H, B, hscalar, hfactor, heval'⟩

end CM

end Fermat.Conservation.Credit.RealFlow
