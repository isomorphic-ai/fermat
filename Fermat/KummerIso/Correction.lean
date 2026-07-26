import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.GenericIrregular.ChannelCertificate
import Mathlib.LinearAlgebra.Pi

/-!
# The finite diagonal correction in the irregular Kummer splice

The correction attached to finitely many exceptional character coordinates
is multiplication by a nonzero scalar in each coordinate over `ZMod p`.
Consequently it is a linear automorphism.  In particular, a corrected
exponent vector vanishes exactly when the original exponent vector vanishes.

This file isolates that finite-dimensional statement from its arithmetic
input.  The arithmetic input remains Vandiver's coefficientwise congruence

`p ^ 3 ∣ a i * B i`

together with the absence of a cube obstruction `p ^ 3 ∤ B i`.  The last
theorems splice the diagonal automorphism into the existing divisibility and
unit-root extraction kernel.  No claim that the correction itself proves the
cube congruences is made here.
-/

namespace Fermat.KummerIso.Correction

open scoped BigOperators
open Fermat.Irregular

/-- Nonzero coordinate gauges for a diagonal correction over `ZMod p`.

The index type is kept abstract so the same construction applies to any
finite collection of exceptional characters.  Taking `ι = Fin N` gives the
arbitrary-`N` correction, including the empty identity map when `N = 0`. -/
structure DiagonalGauge (p : ℕ) (ι : Type*) where
  value : ι → ZMod p
  value_ne_zero : ∀ i, value i ≠ 0

namespace DiagonalGauge

variable {p : ℕ} {ι : Type*}

/-- The unit represented by one nonzero diagonal entry. -/
noncomputable def coordinateUnit (c : DiagonalGauge p ι)
    (hp : p.Prime) (i : ι) : (ZMod p)ˣ := by
  letI : Fact p.Prime := ⟨hp⟩
  exact Units.mk0 (c.value i) (c.value_ne_zero i)

@[simp]
theorem coe_coordinateUnit (c : DiagonalGauge p ι)
    (hp : p.Prime) (i : ι) :
    (c.coordinateUnit hp i : ZMod p) = c.value i := by
  letI : Fact p.Prime := ⟨hp⟩
  rfl

/-- Multiplication by the coordinate gauges, bundled as a linear
automorphism of the finite residue-vector space. -/
noncomputable def automorphism (c : DiagonalGauge p ι)
    (hp : p.Prime) : (ι → ZMod p) ≃ₗ[ZMod p] (ι → ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact LinearEquiv.piCongrRight fun i ↦
    (c.coordinateUnit hp i).mulLeftLinearEquiv (ZMod p) (ZMod p)

@[simp]
theorem automorphism_apply (c : DiagonalGauge p ι) (hp : p.Prime)
    (a : ι → ZMod p) (i : ι) :
    c.automorphism hp a i = c.value i * a i := by
  letI : Fact p.Prime := ⟨hp⟩
  rfl

@[simp]
theorem automorphism_symm_apply (c : DiagonalGauge p ι) (hp : p.Prime)
    (a : ι → ZMod p) (i : ι) :
    (c.automorphism hp).symm a i = (c.value i)⁻¹ * a i := by
  letI : Fact p.Prime := ⟨hp⟩
  rfl

/-- A corrected residue vector is zero exactly when its uncorrected vector
is zero. -/
@[simp]
theorem automorphism_eq_zero_iff (c : DiagonalGauge p ι)
    (hp : p.Prime) (a : ι → ZMod p) :
    c.automorphism hp a = 0 ↔ a = 0 :=
  (c.automorphism hp).map_eq_zero_iff

/-- Coordinate form of `automorphism_eq_zero_iff`. -/
theorem corrected_coordinates_zero_iff (c : DiagonalGauge p ι)
    (hp : p.Prime) (a : ι → ZMod p) :
    (∀ i, c.value i * a i = 0) ↔ ∀ i, a i = 0 := by
  constructor
  · intro h i
    letI : Fact p.Prime := ⟨hp⟩
    exact (mul_eq_zero.mp (h i)).resolve_left (c.value_ne_zero i)
  · intro h i
    simp [h i]

/-- The corrected integral exponent vector vanishes modulo `p` exactly when
all original exponents are divisible by `p`. -/
theorem corrected_exponents_eq_zero_iff_dvd (c : DiagonalGauge p ι)
    (hp : p.Prime) (a : ι → ℤ) :
    c.automorphism hp (fun i ↦ (a i : ZMod p)) = 0 ↔
      ∀ i, (p : ℤ) ∣ a i := by
  rw [c.automorphism_eq_zero_iff hp]
  constructor
  · intro h i
    apply (CharP.intCast_eq_zero_iff (ZMod p) p (a i)).mp
    simpa using congrFun h i
  · intro h
    funext i
    exact (CharP.intCast_eq_zero_iff (ZMod p) p (a i)).mpr (h i)

/-- The axis-8 finite-channel certificate supplies exactly the nonzero
entries required by a diagonal correction. -/
def ofFixedChannelCertificate
    {p N : ℕ} [Fact p.Prime]
    (C :
      GenericIrregular.ChannelCertificate.FixedChannelCertificate p N)
    (hp5 : 5 ≤ p) :
    DiagonalGauge p (Fin N) where
  value := GenericIrregular.ChannelCertificate.weights C.channel
  value_ne_zero := C.weight_ne_zero hp5

@[simp]
theorem ofFixedChannelCertificate_value
    {p N : ℕ} [Fact p.Prime]
    (C :
      GenericIrregular.ChannelCertificate.FixedChannelCertificate p N)
    (hp5 : 5 ≤ p) (i : Fin N) :
    (ofFixedChannelCertificate C hp5).value i =
      GenericIrregular.ChannelCertificate.weights C.channel i :=
  rfl

/-- The concrete arbitrary-`N` correction automorphism supplied by an axis-8
channel certificate. -/
noncomputable def fixedChannelAutomorphism
    {p N : ℕ} [Fact p.Prime]
    (C :
      GenericIrregular.ChannelCertificate.FixedChannelCertificate p N)
    (hp5 : 5 ≤ p) :
    (Fin N → ZMod p) ≃ₗ[ZMod p] (Fin N → ZMod p) :=
  (ofFixedChannelCertificate C hp5).automorphism Fact.out

@[simp]
theorem fixedChannelAutomorphism_apply
    {p N : ℕ} [Fact p.Prime]
    (C :
      GenericIrregular.ChannelCertificate.FixedChannelCertificate p N)
    (hp5 : 5 ≤ p) (a : Fin N → ZMod p) (i : Fin N) :
    fixedChannelAutomorphism C hp5 a i =
      GenericIrregular.ChannelCertificate.weights C.channel i * a i :=
  rfl

@[simp]
theorem fixedChannelAutomorphism_eq_zero_iff
    {p N : ℕ} [Fact p.Prime]
    (C :
      GenericIrregular.ChannelCertificate.FixedChannelCertificate p N)
    (hp5 : 5 ≤ p) (a : Fin N → ZMod p) :
    fixedChannelAutomorphism C hp5 a = 0 ↔ a = 0 :=
  (ofFixedChannelCertificate C hp5).automorphism_eq_zero_iff
    Fact.out a

end DiagonalGauge

/-- Arithmetic data for a block of lifted Bernoulli coordinates.

Each coefficient has already acquired two powers of `p`, but not a third.
The quotient by `p ^ 2` is therefore a nonzero residue modulo `p` and is the
honest diagonal correction gauge.

This structure describes the exceptional block only.  Ordinary coordinates,
whose coefficients have only one factor of `p`, remain the domain of the
existing scalar divisibility argument. -/
structure LiftedCorrectionData (p : ℕ) (ι : Type*) where
  B : ι → ℤ
  square_dvd : ∀ i, (p : ℤ) ^ 2 ∣ B i
  cube_not_dvd : ∀ i, ¬(p : ℤ) ^ 3 ∣ B i

namespace LiftedCorrectionData

variable {p : ℕ} {ι : Type*}

/-- The integral quotient `B i / p ^ 2`, chosen from the certified
divisibility rather than integer truncating division. -/
noncomputable def normalizedQuotient
    (D : LiftedCorrectionData p ι) (i : ι) : ℤ :=
  Classical.choose (D.square_dvd i)

/-- The defining factorization of a lifted coefficient. -/
theorem B_eq_square_mul_normalizedQuotient
    (D : LiftedCorrectionData p ι) (i : ι) :
    D.B i = (p : ℤ) ^ 2 * D.normalizedQuotient i :=
  Classical.choose_spec (D.square_dvd i)

/-- The normalized quotient is nonzero modulo `p`: otherwise the certified
coefficient would contain a third factor of `p`. -/
theorem normalizedQuotient_not_dvd
    (D : LiftedCorrectionData p ι) (i : ι) :
    ¬(p : ℤ) ∣ D.normalizedQuotient i := by
  intro hdiv
  apply D.cube_not_dvd i
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, ?_⟩
  calc
    D.B i =
        (p : ℤ) ^ 2 * D.normalizedQuotient i :=
      D.B_eq_square_mul_normalizedQuotient i
    _ = (p : ℤ) ^ 2 * ((p : ℤ) * q) := by rw [hq]
    _ = (p : ℤ) ^ 3 * q := by rw [pow_succ]; ring

/-- The diagonal gauge obtained by dividing every lifted coefficient by
`p ^ 2` and reducing the quotient modulo `p`. -/
noncomputable def diagonalGauge
    (D : LiftedCorrectionData p ι) : DiagonalGauge p ι where
  value i := D.normalizedQuotient i
  value_ne_zero i := by
    intro hzero
    apply D.normalizedQuotient_not_dvd i
    exact
      (CharP.intCast_eq_zero_iff
        (ZMod p) p (D.normalizedQuotient i)).mp hzero

@[simp]
theorem diagonalGauge_value
    (D : LiftedCorrectionData p ι) (i : ι) :
    D.diagonalGauge.value i =
      (D.normalizedQuotient i : ZMod p) :=
  rfl

/-- Cancel the certified `p ^ 2` factor directly in the cube congruence.

This is the arithmetic heart of the correction construction.  It concludes
that `p` divides `a i * (B i / p ^ 2)`; it does not first conclude that `p`
divides `a i`. -/
theorem dvd_exponent_mul_normalizedQuotient
    (D : LiftedCorrectionData p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * D.B i)
    (i : ι) :
    (p : ℤ) ∣ a i * D.normalizedQuotient i := by
  have hp2 : (p : ℤ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hi :
      (p : ℤ) ^ 2 * (p : ℤ) ∣
        (p : ℤ) ^ 2 *
          (a i * D.normalizedQuotient i) := by
    rw [← pow_succ]
    convert hcong i using 1
    rw [D.B_eq_square_mul_normalizedQuotient i]
    ring
  exact (mul_dvd_mul_iff_left hp2).mp hi

/-- The cube congruence is, after cancelling `p ^ 2`, precisely a zero
coordinate in the corrected residue vector. -/
theorem corrected_coordinate_eq_zero_of_cube_congruence
    (D : LiftedCorrectionData p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * D.B i)
    (i : ι) :
    D.diagonalGauge.value i * (a i : ZMod p) = 0 := by
  have hzero :
      ((a i * D.normalizedQuotient i : ℤ) : ZMod p) = 0 :=
    (CharP.intCast_eq_zero_iff
      (ZMod p) p (a i * D.normalizedQuotient i)).mpr
        (D.dvd_exponent_mul_normalizedQuotient hp a hcong i)
  simpa [mul_comm] using hzero

/-- All lifted cube congruences assemble into the corrected-zero vector
equation, before any exponent divisibility is deduced. -/
theorem corrected_exponents_eq_zero_of_cube_congruences
    (D : LiftedCorrectionData p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * D.B i) :
    D.diagonalGauge.automorphism hp
      (fun i ↦ (a i : ZMod p)) = 0 := by
  funext i
  simpa using
    D.corrected_coordinate_eq_zero_of_cube_congruence
      hp a hcong i

/-- Inverting the diagonal correction recovers divisibility of every
exceptional exponent. -/
theorem exponents_dvd_of_cube_congruences
    (D : LiftedCorrectionData p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * D.B i) :
    ∀ i, (p : ℤ) ∣ a i := by
  apply
    (D.diagonalGauge.corrected_exponents_eq_zero_iff_dvd hp a).1
  exact D.corrected_exponents_eq_zero_of_cube_congruences hp a hcong

end LiftedCorrectionData

/-- A full coefficient family with no cube obstruction.

Rows divisible by `p ^ 2` form the lifted exceptional block.  Their
correction entry is the quotient by `p ^ 2`.  Every other row receives the
identity entry `1`; those ordinary rows are discharged by the existing
scalar divisibility lemma. -/
structure BernoulliCorrection (p : ℕ) (ι : Type*) where
  B : ι → ℤ
  cube_not_dvd : ∀ i, ¬(p : ℤ) ^ 3 ∣ B i

namespace BernoulliCorrection

variable {p : ℕ} {ι : Type*}

/-- The full-source correction entry: the normalized quotient on a lifted
row and `1` on an ordinary row. -/
noncomputable def normalizedEntry
    (C : BernoulliCorrection p ι) (i : ι) : ℤ :=
  if h : (p : ℤ) ^ 2 ∣ C.B i then
    Classical.choose h
  else
    1

theorem B_eq_square_mul_normalizedEntry_of_square_dvd
    (C : BernoulliCorrection p ι) (i : ι)
    (hsquare : (p : ℤ) ^ 2 ∣ C.B i) :
    C.B i = (p : ℤ) ^ 2 * C.normalizedEntry i := by
  rw [normalizedEntry, dif_pos hsquare]
  exact Classical.choose_spec hsquare

@[simp]
theorem normalizedEntry_of_not_square_dvd
    (C : BernoulliCorrection p ι) (i : ι)
    (hsquare : ¬(p : ℤ) ^ 2 ∣ C.B i) :
    C.normalizedEntry i = 1 := by
  simp [normalizedEntry, hsquare]

/-- The full diagonal correction: genuine normalized quotient entries on
the lifted block and identity entries elsewhere. -/
noncomputable def diagonalGauge
    (C : BernoulliCorrection p ι) (hp : p.Prime) :
    DiagonalGauge p ι where
  value i := C.normalizedEntry i
  value_ne_zero i := by
    letI : Fact p.Prime := ⟨hp⟩
    by_cases hsquare : (p : ℤ) ^ 2 ∣ C.B i
    · intro hzero
      apply C.cube_not_dvd i
      have hdiv :
          (p : ℤ) ∣ C.normalizedEntry i :=
        (CharP.intCast_eq_zero_iff
          (ZMod p) p (C.normalizedEntry i)).mp hzero
      obtain ⟨q, hq⟩ := hdiv
      refine ⟨q, ?_⟩
      calc
        C.B i =
            (p : ℤ) ^ 2 * C.normalizedEntry i :=
          C.B_eq_square_mul_normalizedEntry_of_square_dvd
            i hsquare
        _ = (p : ℤ) ^ 2 * ((p : ℤ) * q) := by rw [hq]
        _ = (p : ℤ) ^ 3 * q := by rw [pow_succ]; ring
    · simp [C.normalizedEntry_of_not_square_dvd i hsquare]

@[simp]
theorem diagonalGauge_value
    (C : BernoulliCorrection p ι) (hp : p.Prime) (i : ι) :
    (C.diagonalGauge hp).value i =
      (C.normalizedEntry i : ZMod p) :=
  rfl

/-- Direct cancellation on one lifted row of a full coefficient family. -/
theorem dvd_exponent_mul_normalizedEntry_of_square_dvd
    (C : BernoulliCorrection p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * C.B i)
    (i : ι) (hsquare : (p : ℤ) ^ 2 ∣ C.B i) :
    (p : ℤ) ∣ a i * C.normalizedEntry i := by
  have hp2 : (p : ℤ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hi :
      (p : ℤ) ^ 2 * (p : ℤ) ∣
        (p : ℤ) ^ 2 * (a i * C.normalizedEntry i) := by
    rw [← pow_succ]
    convert hcong i using 1
    rw [C.B_eq_square_mul_normalizedEntry_of_square_dvd
      i hsquare]
    ring
  exact (mul_dvd_mul_iff_left hp2).mp hi

/-- Every full-source cube congruence is a zero corrected coordinate.

The lifted branch cancels `p ^ 2` and uses the normalized quotient.  Only the
ordinary branch calls the old scalar lemma, and its diagonal entry is `1`. -/
theorem corrected_coordinate_eq_zero_of_cube_congruence
    (C : BernoulliCorrection p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * C.B i)
    (i : ι) :
    (C.diagonalGauge hp).value i * (a i : ZMod p) = 0 := by
  by_cases hsquare : (p : ℤ) ^ 2 ∣ C.B i
  · have hzero :
        ((a i * C.normalizedEntry i : ℤ) : ZMod p) = 0 :=
      (CharP.intCast_eq_zero_iff
        (ZMod p) p (a i * C.normalizedEntry i)).mpr
          (C.dvd_exponent_mul_normalizedEntry_of_square_dvd
            hp a hcong i hsquare)
    simpa [mul_comm] using hzero
  · have hdiv : (p : ℤ) ∣ a i :=
      VandiverUnitPower.prime_dvd_of_cube_dvd_mul_of_not_cube_dvd
        hp (hcong i) (C.cube_not_dvd i)
    have hzero : (a i : ZMod p) = 0 :=
      (CharP.intCast_eq_zero_iff (ZMod p) p (a i)).mpr hdiv
    simp [
      C.normalizedEntry_of_not_square_dvd i hsquare, hzero]

/-- The mixed ordinary/exceptional coordinates assemble into one corrected
zero vector. -/
theorem corrected_exponents_eq_zero_of_cube_congruences
    (C : BernoulliCorrection p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * C.B i) :
    (C.diagonalGauge hp).automorphism hp
      (fun i ↦ (a i : ZMod p)) = 0 := by
  funext i
  simpa using
    C.corrected_coordinate_eq_zero_of_cube_congruence
      hp a hcong i

/-- Inversion of the full-source diagonal recovers every original exponent
modulo `p`. -/
theorem exponents_dvd_of_cube_congruences
    (C : BernoulliCorrection p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * C.B i) :
    ∀ i, (p : ℤ) ∣ a i := by
  apply
    ((C.diagonalGauge hp).corrected_exponents_eq_zero_iff_dvd hp a).1
  exact C.corrected_exponents_eq_zero_of_cube_congruences hp a hcong

/-- Vandiver's historical numerator family equipped with its asserted
no-cube obstruction. -/
def ofVandiverNoBernoulliObstruction
    {p : ℕ}
    (hno : VandiverLemmaTwoCore.NoBernoulliObstruction p) :
    BernoulliCorrection p
      (VandiverLemmaTwoCore.SourceIndex p) where
  B := VandiverLemmaTwoCore.vandiverBernoulliNumerator p
  cube_not_dvd := hno

end BernoulliCorrection

/-- Root extraction from the corrected-zero formulation of a primitive
cyclotomic-unit relation.

This is the correction-side adapter to the already proved product and Bézout
kernels in `VandiverUnitPower`. -/
theorem isPower_of_primitive_relation_and_corrected_zero
    {G ι : Type*} [CommGroup G] [Fintype ι]
    {p t : ℕ} (hp : p.Prime) (c : DiagonalGauge p ι)
    (u : G) (E : ι → G) (a : ι → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i)
    (hprimitive : ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i))
    (hcorrected :
      c.automorphism hp (fun i ↦ (a i : ZMod p)) = 0) :
    ∃ v : G, u = v ^ p := by
  have hdiv : ∀ i, (p : ℤ) ∣ a i :=
    (c.corrected_exponents_eq_zero_iff_dvd hp a).1 hcorrected
  have hpt : ¬p ∣ t := fun h ↦ hprimitive ⟨h, hdiv⟩
  have hcop : t.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr hpt).symm
  obtain ⟨d, hd⟩ :=
    VandiverUnitPower.product_zpow_is_pow_of_exponents_divisible
      E a p hdiv
  exact VandiverUnitPower.isPower_of_coprime_power_eq_power
    hcop (hrel.trans hd)

/-- Primitive-relation root extraction through the mixed full-source
correction. -/
theorem isPower_of_primitive_relation_and_bernoulliCorrection
    {G ι : Type*} [CommGroup G] [Fintype ι]
    {p t : ℕ} (hp : p.Prime) (C : BernoulliCorrection p ι)
    (u : G) (E : ι → G) (a : ι → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i)
    (hprimitive : ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i))
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * C.B i) :
    ∃ v : G, u = v ^ p := by
  apply isPower_of_primitive_relation_and_corrected_zero
    hp (C.diagonalGauge hp) u E a hrel hprimitive
  exact C.corrected_exponents_eq_zero_of_cube_congruences
    hp a hcong

/-- Finite-index root extraction through the mixed full-source correction. -/
theorem isPower_of_finiteIndex_family_and_bernoulliCorrection
    {G ι : Type*} [CommGroup G] [Fintype ι]
    {p : ℕ} (hp : p.Prime)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G) (E : ι → G) (C : BernoulliCorrection p ι)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hcong : ∀ (t : ℕ) (a : ι → ℤ),
      0 < t →
      u ^ t = ∏ i, E i ^ a i →
      ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i) →
      ∀ i, (p : ℤ) ^ 3 ∣ a i * C.B i) :
    ∃ v : G, u = v ^ p := by
  obtain ⟨a, ht, hrel⟩ :=
    VandiverUnitPower.exists_index_relation E u
  obtain ⟨t', a', ht', hrel', hprimitive⟩ :=
    VandiverUnitPower.exists_primitive_relation_of_relation
      hp.two_le hpow u E a ht hrel
  exact isPower_of_primitive_relation_and_bernoulliCorrection
    hp C u E a' hrel' hprimitive
      (hcong t' a' ht' hrel' hprimitive)

/-- Full source-indexed regularized Vandiver unit theorem.

At every coordinate divisible by `p ^ 2`, the diagonal entry is the actual
integer quotient by `p ^ 2`, reduced modulo `p`.  At the remaining ordinary
coordinates it is `1`.  Thus this is a direct correction-based
implementation of `VandiverLemmaTwoCore`'s generic interface. -/
theorem isPower_of_vandiver_regularized
    {G : Type*} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G)
    (E : VandiverLemmaTwoCore.SourceIndex p → G)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hcong :
      VandiverLemmaTwoCore.PrimitiveRelationCubeCongruences p u E)
    (hno : VandiverLemmaTwoCore.NoBernoulliObstruction p) :
    ∃ v : G, u = v ^ p := by
  apply isPower_of_finiteIndex_family_and_bernoulliCorrection
    hp hpow u E
      (BernoulliCorrection.ofVandiverNoBernoulliObstruction hno)
  intro t a ht hrel hprimitive i
  exact hcong t a ht hrel hprimitive i

/-- The honest lifted primitive-relation splice: cancel the certified
`p ^ 2`, form the corrected-zero equation, invert the diagonal correction,
and invoke the existing unit-power kernel. -/
theorem isPower_of_primitive_relation_and_lifted_correction
    {G ι : Type*} [CommGroup G] [Fintype ι]
    {p t : ℕ} (hp : p.Prime) (D : LiftedCorrectionData p ι)
    (u : G) (E : ι → G) (a : ι → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i)
    (hprimitive : ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i))
    (hcong : ∀ i, (p : ℤ) ^ 3 ∣ a i * D.B i) :
    ∃ v : G, u = v ^ p := by
  apply isPower_of_primitive_relation_and_corrected_zero
    hp D.diagonalGauge u E a hrel hprimitive
  exact D.corrected_exponents_eq_zero_of_cube_congruences hp a hcong

/-- Finite-index version of the honest lifted correction splice. -/
theorem isPower_of_finiteIndex_family_and_lifted_correction
    {G ι : Type*} [CommGroup G] [Fintype ι]
    {p : ℕ} (hp : p.Prime)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G) (E : ι → G) (D : LiftedCorrectionData p ι)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hcong : ∀ (t : ℕ) (a : ι → ℤ),
      0 < t →
      u ^ t = ∏ i, E i ^ a i →
      ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i) →
      ∀ i, (p : ℤ) ^ 3 ∣ a i * D.B i) :
    ∃ v : G, u = v ^ p := by
  obtain ⟨a, ht, hrel⟩ :=
    VandiverUnitPower.exists_index_relation E u
  obtain ⟨t', a', ht', hrel', hprimitive⟩ :=
    VandiverUnitPower.exists_primitive_relation_of_relation
      hp.two_le hpow u E a ht hrel
  exact isPower_of_primitive_relation_and_lifted_correction
    hp D u E a' hrel' hprimitive
      (hcong t' a' ht' hrel' hprimitive)

/-- A source-indexed lifted block automatically supplies the Bernoulli
non-cube condition expected by `VandiverLemmaTwoCore`, once its coefficient
family is identified with Vandiver's historical numerators. -/
theorem vandiverNoBernoulliObstruction_of_liftedCorrection
    {p : ℕ}
    (D :
      LiftedCorrectionData p
        (VandiverLemmaTwoCore.SourceIndex p))
    (hB : D.B =
      VandiverLemmaTwoCore.vandiverBernoulliNumerator p) :
    VandiverLemmaTwoCore.NoBernoulliObstruction p := by
  intro i
  rw [← congrFun hB i]
  exact D.cube_not_dvd i

end Fermat.KummerIso.Correction
