/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# W1: generated credit flow

Kummer introduced the logarithmic-derivative reading used here.  Vandiver
discovered the assembly in which its coefficients force repayment.  This
file does not import that classical assembly: it constructs the rate
reading directly from Mathlib's Bernoulli generator and from C2's one
cycle.

The source of truth is `bernoulli'PowerSeries ℚ`.  Regularization means
rescaling that generator, subtracting the original generator, and removing
the resulting initial zero coefficient.  Orbit-edge weights and the flow
of an exponent vector are then derived from that series; no matrix or
independent flow map is supplied as data.
-/
import Fermat.Conservation.Credit.Capacity
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.PowerSeries.Derivative

namespace Fermat.Conservation.Credit

open PowerSeries

namespace Flow

/-! ## The one formal generator and its regularized rate -/

/-- The Bernoulli exponential generating series is the one formal credit
generator.  Every rate below is constructed from this definition. -/
def generator : PowerSeries ℚ :=
  bernoulli'PowerSeries ℚ

/-- Mathlib's Bernoulli generating-series identity, exposed for the one
credit generator rather than duplicated as coefficient data. -/
theorem generator_mul_exp_sub_one :
    generator * (PowerSeries.exp ℚ - 1) =
      PowerSeries.X * PowerSeries.exp ℚ :=
  bernoulli'PowerSeries_mul_exp_sub_one ℚ

/-- Every coefficient of the source generator is its Bernoulli
coefficient. -/
@[simp]
theorem coeff_generator (n : ℕ) :
    PowerSeries.coeff n generator =
      bernoulli' n / Nat.factorial n := by
  simp [generator, bernoulli'PowerSeries]

/-- Remove the initial coefficient of a formal power series.  When that
coefficient is zero, multiplication by `X` recovers the original series. -/
noncomputable def tail (series : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) series

@[simp]
theorem coeff_tail (series : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (tail series) =
      PowerSeries.coeff (n + 1) series := by
  simp [tail]

/-- `tail` is formal division by `X` on series whose constant coefficient
vanishes. -/
theorem X_mul_tail {series : PowerSeries ℚ}
    (hzero : PowerSeries.coeff 0 series = 0) :
    PowerSeries.X * tail series = series := by
  ext (_ | n)
  · simpa using hzero.symm
  · simp

/-- Kummer's regularized logarithmic derivative at scale `scale`.

It is definitionally the tail of the rescaled-minus-original generator;
in particular it cannot be varied independently of `generator`. -/
noncomputable def regularizedLogDerivative (scale : ℚ) :
    PowerSeries ℚ :=
  tail (PowerSeries.rescale scale generator - generator)

/-- The rescaled-minus-original generator has zero constant coefficient. -/
theorem coeff_zero_rescale_sub_generator (scale : ℚ) :
    PowerSeries.coeff 0
        (PowerSeries.rescale scale generator - generator) = 0 := by
  simp only [map_sub, PowerSeries.coeff_rescale, pow_zero, one_mul,
    sub_self]

/-- Multiplying the regularized rate by `X` recovers precisely the
rescaled-minus-original generator. -/
theorem X_mul_regularizedLogDerivative (scale : ℚ) :
    PowerSeries.X * regularizedLogDerivative scale =
      PowerSeries.rescale scale generator - generator :=
  X_mul_tail (coeff_zero_rescale_sub_generator scale)

/-- Exact coefficient formula for the generated rate. -/
theorem coeff_regularizedLogDerivative (scale : ℚ) (n : ℕ) :
    PowerSeries.coeff n (regularizedLogDerivative scale) =
      (scale ^ (n + 1) - 1) *
        (bernoulli' (n + 1) / Nat.factorial (n + 1)) := by
  simp only [regularizedLogDerivative, coeff_tail, map_sub,
    PowerSeries.coeff_rescale, generator, bernoulli'PowerSeries,
    PowerSeries.coeff_mk, Algebra.algebraMap_self_apply]
  ring

/-! ## Formal differentiation at zero -/

/-- Formal evaluation of the derivative at zero. -/
noncomputable def derivativeAtZero (series : PowerSeries ℚ) : ℚ :=
  PowerSeries.coeff 0 (PowerSeries.derivative ℚ series)

/-- The formal derivative at zero is the linear coefficient. -/
theorem derivativeAtZero_eq_coeff_one (series : PowerSeries ℚ) :
    derivativeAtZero series = PowerSeries.coeff 1 series := by
  simp [derivativeAtZero, PowerSeries.coeff_derivative]

/-- The exact Bernoulli formula for the derivative at zero of a
rescaled-minus-original generator. -/
theorem derivativeAtZero_rescale_sub_generator (scale : ℚ) :
    derivativeAtZero
        (PowerSeries.rescale scale generator - generator) =
      (scale ^ 1 - 1) *
        (bernoulli' 1 / Nat.factorial 1) := by
  rw [derivativeAtZero_eq_coeff_one]
  simp only [map_sub, PowerSeries.coeff_rescale, generator,
    bernoulli'PowerSeries, PowerSeries.coeff_mk,
    Algebra.algebraMap_self_apply]
  ring

/-- The value at zero of the regularized rate is the derivative at zero
of its unregularized generator difference. -/
theorem coeff_zero_regularizedLogDerivative_eq_derivativeAtZero
    (scale : ℚ) :
    PowerSeries.coeff 0 (regularizedLogDerivative scale) =
      derivativeAtZero
        (PowerSeries.rescale scale generator - generator) := by
  rw [derivativeAtZero_eq_coeff_one]
  simp [regularizedLogDerivative]

/-- At the high index used by the credit forcing calculation, the
coefficient is still obtained directly from the same generator. -/
theorem coeff_regularizedLogDerivative_high
    {p : ℕ} (hp : p.Prime) (scale : ℚ) (k : ℕ) :
    PowerSeries.coeff (2 * (k + 1) * p - 1)
        (regularizedLogDerivative scale) =
      (scale ^ (2 * (k + 1) * p) - 1) *
        (bernoulli (2 * (k + 1) * p) /
          Nat.factorial (2 * (k + 1) * p)) := by
  rw [coeff_regularizedLogDerivative]
  have hpos : 0 < 2 * (k + 1) * p :=
    Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos k)) hp.pos
  have hindex :
      (2 * (k + 1) * p - 1) + 1 = 2 * (k + 1) * p :=
    Nat.sub_add_cancel hpos
  have heven : Even (2 * (k + 1) * p) :=
    (even_two.mul_right (k + 1)).mul_right p
  rw [hindex, bernoulli'_eq_bernoulli]
  rw [heven.neg_one_pow, one_mul]

/-! ## The generated orbit flow -/

/-- An odd-prime flow orbit reuses C2's one generated cycle.  Its only
arithmetic choices are the rational scale at each generated node and the
coefficient degree assigned to each of the `rank` output coordinates.
There is deliberately no weight matrix or flow map field. -/
structure GeneratorOrbit (p : ℕ) (α : Type*) where
  cycle : Cycle α
  scale : α → ℚ
  prime : p.Prime
  odd : Odd p
  coordinateDegree : Fin cycle.rank → ℕ

namespace GeneratorOrbit

variable {p : ℕ} {α : Type*}

/-- The rational scale of the `n`th node, produced from C2's recursion. -/
def nodeScale (orbit : GeneratorOrbit p α) (n : ℕ) : ℚ :=
  orbit.scale (orbit.cycle.point n)

/-- The formal rate carried by one generated orbit edge.  It is obtained
by subtracting the two node rescalings of the one generator and taking
the tail; it is not supplied by `GeneratorOrbit`. -/
noncomputable def edgeSeries (orbit : GeneratorOrbit p α)
    (i : Fin orbit.cycle.rank) : PowerSeries ℚ :=
  tail
    (PowerSeries.rescale (orbit.nodeScale (i.val + 1)) generator -
      PowerSeries.rescale (orbit.nodeScale i.val) generator)

/-- An edge rate is equivalently the difference of the regularized node
rates.  Both sides reduce to rescalings of `generator`. -/
theorem edgeSeries_eq_sub_regularized (orbit : GeneratorOrbit p α)
    (i : Fin orbit.cycle.rank) :
    orbit.edgeSeries i =
      regularizedLogDerivative (orbit.nodeScale (i.val + 1)) -
        regularizedLogDerivative (orbit.nodeScale i.val) := by
  ext n
  simp only [edgeSeries, coeff_tail, map_sub,
    regularizedLogDerivative]
  ring

/-- Exact Bernoulli coefficient of a generated orbit edge. -/
theorem coeff_edgeSeries (orbit : GeneratorOrbit p α)
    (i : Fin orbit.cycle.rank) (n : ℕ) :
    PowerSeries.coeff n (orbit.edgeSeries i) =
      (orbit.nodeScale (i.val + 1) ^ (n + 1) -
          orbit.nodeScale i.val ^ (n + 1)) *
        (bernoulli' (n + 1) / Nat.factorial (n + 1)) := by
  simp only [edgeSeries, coeff_tail, map_sub,
    PowerSeries.coeff_rescale, generator, bernoulli'PowerSeries,
    PowerSeries.coeff_mk, Algebra.algebraMap_self_apply]
  ring

/-- The matrix entry seen by an exponent on edge `i` and output
coordinate `k`.  This is a definition derived from `edgeSeries`, not a
field of the orbit datum. -/
noncomputable def weight (orbit : GeneratorOrbit p α)
    (i k : Fin orbit.cycle.rank) : ℚ :=
  PowerSeries.coeff (orbit.coordinateDegree k) (orbit.edgeSeries i)

/-- The derived orbit weight in closed Bernoulli form. -/
theorem weight_eq_bernoulli (orbit : GeneratorOrbit p α)
    (i k : Fin orbit.cycle.rank) :
    orbit.weight i k =
      (orbit.nodeScale (i.val + 1) ^
            (orbit.coordinateDegree k + 1) -
          orbit.nodeScale i.val ^
            (orbit.coordinateDegree k + 1)) *
        (bernoulli' (orbit.coordinateDegree k + 1) /
          Nat.factorial (orbit.coordinateDegree k + 1)) :=
  orbit.coeff_edgeSeries i (orbit.coordinateDegree k)

/-- Integral exponent vectors for the generated C2 edge family. -/
abbrev ExponentVector (orbit : GeneratorOrbit p α) :=
  Fin orbit.cycle.rank →₀ ℤ

/-- Rationalized exponent vectors, used only to package the derived flow
as a linear map. -/
abbrev RationalExponentVector (orbit : GeneratorOrbit p α) :=
  Fin orbit.cycle.rank →₀ ℚ

/-- The coefficient space has exactly the rank of the generated orbit. -/
abbrev CoefficientSpace (orbit : GeneratorOrbit p α) :=
  Fin orbit.cycle.rank → ℚ

/-- Rational flow is the linear combination of the derived orbit-edge
weight vectors. -/
noncomputable def rationalFlow (orbit : GeneratorOrbit p α) :
    orbit.RationalExponentVector →ₗ[ℚ] orbit.CoefficientSpace :=
  Finsupp.linearCombination ℚ
    (fun i k => orbit.weight i k)

/-- Canonical coefficientwise inclusion of integral exponents into
rational exponents. -/
noncomputable def castExponent (orbit : GeneratorOrbit p α) :
    orbit.ExponentVector →+ orbit.RationalExponentVector :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ)

/-- **W1 generated exponent flow.**  This additive homomorphism is the
composite of canonical scalar extension with `rationalFlow`; hence it is
entirely determined by the generator, the C2 orbit, and coefficient
degrees. -/
noncomputable def exponentFlow (orbit : GeneratorOrbit p α) :
    orbit.ExponentVector →+ orbit.CoefficientSpace :=
  orbit.rationalFlow.toAddMonoidHom.comp orbit.castExponent

/-- A single exponent contributes its scalar multiple of the derived
edge-weight vector. -/
@[simp]
theorem exponentFlow_single (orbit : GeneratorOrbit p α)
    (i : Fin orbit.cycle.rank) (z : ℤ) :
    orbit.exponentFlow (Finsupp.single i z) =
      fun k => (z : ℚ) * orbit.weight i k := by
  ext k
  simp [exponentFlow, castExponent, rationalFlow,
    Finsupp.linearCombination_apply]

/-- The empty generated product carries zero flow. -/
@[simp]
theorem exponentFlow_zero (orbit : GeneratorOrbit p α) :
    orbit.exponentFlow 0 = 0 :=
  orbit.exponentFlow.map_zero

/-- Product conservation in exponent coordinates: multiplying generated
products adds exponents, and therefore adds their flows. -/
theorem product_conservation (orbit : GeneratorOrbit p α)
    (left right : orbit.ExponentVector) :
    orbit.exponentFlow (left + right) =
      orbit.exponentFlow left + orbit.exponentFlow right :=
  orbit.exponentFlow.map_add left right

/-- Finite-sum conservation for generated exponent vectors. -/
theorem sum_conservation (orbit : GeneratorOrbit p α)
    {ι : Type*} (s : Finset ι) (exponents : ι → orbit.ExponentVector) :
    orbit.exponentFlow (∑ i ∈ s, exponents i) =
      ∑ i ∈ s, orbit.exponentFlow (exponents i) := by
  exact map_sum orbit.exponentFlow (fun i : ι => exponents i) s

/-- The same conservation law packaged multiplicatively: multiplication
of exponent products maps to multiplication in the multiplicative wrapper
of the additive coefficient space. -/
noncomputable def productFlow (orbit : GeneratorOrbit p α) :
    Multiplicative orbit.ExponentVector →*
      Multiplicative orbit.CoefficientSpace :=
  orbit.exponentFlow.toMultiplicative

@[simp]
theorem productFlow_ofAdd (orbit : GeneratorOrbit p α)
    (a : orbit.ExponentVector) :
    orbit.productFlow (Multiplicative.ofAdd a) =
      Multiplicative.ofAdd (orbit.exponentFlow a) :=
  rfl

end GeneratorOrbit

/-! ## Gauge and reindex functoriality -/

/-- Pull coefficient coordinates along an index map.  This is the generic
reindexing gauge used below. -/
def pullCoordinates {ι κ : Type*} (reindex : κ → ι) :
    (ι → ℚ) →ₗ[ℚ] (κ → ℚ) where
  toFun coefficients k := coefficients (reindex k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pullCoordinates_apply {ι κ : Type*} (reindex : κ → ι)
    (coefficients : ι → ℚ) (k : κ) :
    pullCoordinates reindex coefficients k =
      coefficients (reindex k) :=
  rfl

theorem pullCoordinates_id (ι : Type*) :
    pullCoordinates (id : ι → ι) = LinearMap.id := by
  rfl

theorem pullCoordinates_comp {ι κ ν : Type*}
    (first : κ → ι) (second : ν → κ) :
    pullCoordinates (first ∘ second) =
      (pullCoordinates second).comp (pullCoordinates first) := by
  rfl

namespace GeneratorOrbit

variable {p : ℕ} {α : Type*}

/-- Postcompose generated flow by a linear gauge. -/
noncomputable def gaugeFlow (orbit : GeneratorOrbit p α)
    {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (gauge : orbit.CoefficientSpace →ₗ[ℚ] V) :
    orbit.ExponentVector →+ V :=
  gauge.toAddMonoidHom.comp orbit.exponentFlow

@[simp]
theorem gaugeFlow_apply (orbit : GeneratorOrbit p α)
    {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (gauge : orbit.CoefficientSpace →ₗ[ℚ] V)
    (a : orbit.ExponentVector) :
    orbit.gaugeFlow gauge a = gauge (orbit.exponentFlow a) :=
  rfl

/-- Gauge application is functorial under composition. -/
theorem gaugeFlow_comp (orbit : GeneratorOrbit p α)
    {V W : Type*}
    [AddCommMonoid V] [Module ℚ V]
    [AddCommMonoid W] [Module ℚ W]
    (first : orbit.CoefficientSpace →ₗ[ℚ] V)
    (second : V →ₗ[ℚ] W) :
    orbit.gaugeFlow (second.comp first) =
      second.toAddMonoidHom.comp (orbit.gaugeFlow first) :=
  rfl

/-- Generated flow after a coordinate reindexing. -/
noncomputable def reindexedFlow (orbit : GeneratorOrbit p α)
    {κ : Type*} (reindex : κ → Fin orbit.cycle.rank) :
    orbit.ExponentVector →+ (κ → ℚ) :=
  orbit.gaugeFlow (pullCoordinates reindex)

@[simp]
theorem reindexedFlow_apply (orbit : GeneratorOrbit p α)
    {κ : Type*} (reindex : κ → Fin orbit.cycle.rank)
    (a : orbit.ExponentVector) (k : κ) :
    orbit.reindexedFlow reindex a k =
      orbit.exponentFlow a (reindex k) :=
  rfl

/-! ## The honest filtered-depth boundary -/

/-- The local infrastructure still needed by the L4 depth argument:
a descending additive filtration on generated exponent vectors.

This interface deliberately contains no flow-vanishing field.  After a
cyclotomic filtration is constructed, the exact unproved bridge is the
subgroup inclusion
`filtration (2 * p) ≤ orbit.exponentFlow.ker`.
That arithmetic inclusion is not renamed as data or asserted here. -/
structure FilteredDepthInterface (orbit : GeneratorOrbit p α) where
  filtration : ℕ → AddSubgroup orbit.ExponentVector
  antitone_filtration : Antitone filtration

end GeneratorOrbit

end Flow

end Fermat.Conservation.Credit
