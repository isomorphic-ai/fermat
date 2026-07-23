import Fermat.Irregular.VandiverHistoricalDescent
import Fermat.Irregular.VandiverLemmaOne
import Fermat.Irregular.CircularUnitIndex
import Fermat.Irregular.CyclotomicDiscriminantPrime
import Fermat.SixtySeven.VandiverData
import Fermat.SixtySeven.SinnottKummer
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Vandiver's historical descent at exponent 67

This file instantiates the source-faithful historical descent with the
concrete real-subfield invariant at exponent `67`. It first proves the
passage from a primitive rational second-case solution to Vandiver's
equation (6), using

`67 ~ (1 - ζ) ^ 66 ~ ((1 - ζ) * (1 - ζ⁻¹)) ^ 33`.

The subsequent sections expose the actual algebraic data in equations
(7b)--(10), reusing the repository's ideal-principalization interface and
leaving only the smallest unavailable real-ideal descent lemma explicit.
-/

namespace Fermat.SixtySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 67) K (by norm_num)

/-- The concrete source invariant: all three entries and the coefficient
unit lie in the maximal real subfield. The remaining equation, nonvanishing,
and pairwise-coprimality conditions are fields of `HistoricalState` itself. -/
def RealSourceAdmissible {ζ : K} (hζ : IsPrimitiveRoot ζ 67) :
    HistoricalAdmissibility hζ :=
  fun s ↦
    NumberField.IsCMField.ringOfIntegersComplexConj K s.omega = s.omega ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.theta = s.theta ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.xi = s.xi ∧
    NumberField.IsCMField.unitsComplexConj K s.eta = s.eta

/-- Vandiver's `κ = (1 - ζ)(1 - ζ⁻¹)` is fixed by complex
conjugation. -/
lemma ringOfIntegersComplexConj_kappa {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (kappa hζ) =
      kappa hζ := by
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K
      (((kappa hζ : 𝓞 K) : K)) = ((kappa hζ : 𝓞 K) : K)
  simp only [kappa, map_mul, map_sub, map_one]
  change (1 - NumberField.IsCMField.complexConj K ζ) *
      (1 - NumberField.IsCMField.complexConj K ζ⁻¹) =
    (1 - ζ) * (1 - ζ⁻¹)
  rw [Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  simp only [map_inv₀]
  rw [Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ, inv_inv]
  ring

/-- Complex conjugation sends the integral unit attached to `ζ` to its
inverse. -/
lemma unitsComplexConj_zeta67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67) :
    NumberField.IsCMField.unitsComplexConj K hζ.unit' = (hζ.unit')⁻¹ := by
  apply Units.ext
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K ζ = ζ⁻¹
  exact Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ

/-- Complex conjugation changes the standard uniformizer `ζ - 1` by the
explicit unit `-ζ⁻¹`. -/
lemma ringOfIntegersComplexConj_zeta_sub_one67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        ((hζ.unit' : 𝓞 K) - 1) =
      ((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        ((hζ.unit' : 𝓞 K) - 1) := by
  rw [map_sub, map_one]
  have hconjζ :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) (unitsComplexConj_zeta67 hζ)
  rw [hconjζ]
  have hinv :
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) * (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  simp only [Units.val_neg, neg_mul, mul_sub, hinv]
  ring

/-- Divisibility by a power of `ζ - 1` is preserved by complex
conjugation.  The explicit unit in
`ringOfIntegersComplexConj_zeta_sub_one67` keeps the proof entirely at
element level. -/
lemma zeta_sub_one_pow_dvd_conj_of_dvd67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (n : ℕ) (a : 𝓞 K)
    (h : ((hζ.unit' : 𝓞 K) - 1) ^ n ∣ a) :
    ((hζ.unit' : 𝓞 K) - 1) ^ n ∣
      NumberField.IsCMField.ringOfIntegersComplexConj K a := by
  obtain ⟨b, rfl⟩ := h
  rw [map_mul, map_pow, ringOfIntegersComplexConj_zeta_sub_one67, mul_pow]
  refine ⟨(((-hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ n : (𝓞 K)ˣ) : 𝓞 K) *
      NumberField.IsCMField.ringOfIntegersComplexConj K b, ?_⟩
  simp only [Units.val_pow_eq_pow_val]
  ring

/-- Every 67th power is fixed by complex conjugation modulo
`(ζ - 1)^67`.  Both powers are compared with the same rational 67th
power; conjugating the first comparison is legitimate by the preceding
uniformizer calculation. -/
lemma zeta_sub_one_pow_sixtySeven_dvd_pow_sub_conj_pow67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K) :
    ((hζ.unit' : 𝓞 K) - 1) ^ 67 ∣
      a ^ 67 -
        NumberField.IsCMField.ringOfIntegersComplexConj K a ^ 67 := by
  obtain ⟨c, hc⟩ := exists_int_pow_congruent_mod_primary hζ a
  have hcconj := zeta_sub_one_pow_dvd_conj_of_dvd67 hζ 67
    (a ^ 67 - (c : 𝓞 K) ^ 67) hc
  have hcconj' : ((hζ.unit' : 𝓞 K) - 1) ^ 67 ∣
      NumberField.IsCMField.ringOfIntegersComplexConj K a ^ 67 -
        (c : 𝓞 K) ^ 67 := by
    simpa only [map_sub, map_pow, map_intCast] using hcconj
  convert dvd_sub hc hcconj' using 1
  ring

/-- A 67th root of unity which is `1` modulo `(ζ - 1)^2` is literally
`1`.  A nontrivial power `ζ^k - 1` is associated to the single
uniformizer `ζ - 1`, so it cannot contain its square. -/
lemma zeta_pow_sq_eq_one_of_zeta_sub_one_sq_dvd67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (j : ℕ)
    (hdiv : ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣
      ((((hζ.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K) - 1)) :
    (hζ.unit' ^ j) ^ 2 = 1 := by
  let k : ℕ := (2 * j) % 67
  have hklt : k < 67 := by
    dsimp [k]
    omega
  have hpowmod :
      ((((hζ.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) =
        (hζ.unit' : 𝓞 K) ^ k := by
    simp only [Units.val_pow_eq_pow_val]
    rw [← pow_mul]
    have hmod := pow_mod_orderOf (hζ.unit' : 𝓞 K) (2 * j)
    rw [← hζ.unit'_coe.eq_orderOf] at hmod
    simpa only [k, mul_comm] using hmod.symm
  by_cases hk : k = 0
  · apply Units.ext
    change ((((hζ.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) = 1
    rw [hpowmod, hk, pow_zero]
  · have hknotdvd : ¬ 67 ∣ k := by
      intro h
      obtain ⟨t, ht⟩ := h
      apply hk
      omega
    have hkcoprime : k.Coprime 67 := by
      apply Nat.coprime_comm.mpr
      exact (show Nat.Prime 67 by norm_num).coprime_iff_not_dvd.mpr hknotdvd
    have hassoc : Associated
        ((hζ.unit' : 𝓞 K) - 1)
        ((hζ.unit' : 𝓞 K) ^ k - 1) :=
      hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime hkcoprime
    have hsquare : ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣
        (hζ.unit' : 𝓞 K) - 1 :=
      hassoc.dvd_iff_dvd_right.mpr (by simpa only [hpowmod] using hdiv)
    obtain ⟨c, hc⟩ := hsquare
    have hπ0 : (hζ.unit' : 𝓞 K) - 1 ≠ 0 :=
      hζ.unit'_coe.sub_one_ne_zero (by norm_num)
    have hone : (1 : 𝓞 K) = ((hζ.unit' : 𝓞 K) - 1) * c := by
      apply mul_left_cancel₀ hπ0
      calc
        ((hζ.unit' : 𝓞 K) - 1) * 1 =
            (hζ.unit' : 𝓞 K) - 1 := by ring
        _ = ((hζ.unit' : 𝓞 K) - 1) ^ 2 * c := hc
        _ = ((hζ.unit' : 𝓞 K) - 1) *
            (((hζ.unit' : 𝓞 K) - 1) * c) := by ring
    exact False.elim <| hζ.zeta_sub_one_prime'.not_unit
      (isUnit_iff_dvd_one.mpr ⟨c, hone⟩)

/-- A cyclotomic unit whose conjugation defect is divisible by
`(ζ - 1)^2` is real.  The CM unit theorem writes the defect as a square
of a power of `ζ`; the preceding rigidity lemma kills that power. -/
lemma unit_fixed_of_zeta_sub_one_sq_dvd_sub_conj67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (u : (𝓞 K)ˣ)
    (hdiv : ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣
      (u : 𝓞 K) -
        NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K)) :
    NumberField.IsCMField.unitsComplexConj K u = u := by
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ u (by norm_num)
  let cu : (𝓞 K)ˣ := NumberField.IsCMField.unitsComplexConj K u
  let r : (𝓞 K)ˣ := (hζ.unit' ^ j) ^ 2
  have hu : u = r * cu := by
    calc
      u = (u * cu⁻¹) * cu := by simp
      _ = r * cu := by simpa only [cu, r] using congrArg (· * cu) hj
  have hu' := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hu
  have hfactor :
      (u : 𝓞 K) - (cu : 𝓞 K) =
        (((((hζ.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K) - 1) * (cu : 𝓞 K)) := by
    change (u : 𝓞 K) - (cu : 𝓞 K) =
      ((r : 𝓞 K) - 1) * (cu : 𝓞 K)
    rw [hu']
    simp only [Units.val_mul]
    ring
  have hassoc : Associated
      (((((hζ.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) - 1)
      ((u : 𝓞 K) - (cu : 𝓞 K)) :=
    ⟨cu, by simpa only [hfactor]⟩
  have hrootdiv : ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣
      (((((hζ.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) - 1) :=
    hassoc.dvd_iff_dvd_right.mpr (by simpa only [cu] using hdiv)
  have hroot := zeta_pow_sq_eq_one_of_zeta_sub_one_sq_dvd67 hζ j hrootdiv
  rw [hroot] at hj
  have hucu : u = cu := by
    calc
      u = (u * cu⁻¹) * cu := by simp
      _ = 1 * cu := by rw [hj]
      _ = cu := by simp
  exact hucu.symm

/-! ## Exact normalization to the upstream factor-ideal equation -/

/-- The cyclotomic unit in the exact identity

`κ = (-ζ⁻¹) * (ζ - 1)²`.

Naming it makes the change from Vandiver's real parameter `κ` to the
`(ζ - 1)`-adic normalization used by the generic factor-ideal machinery
completely explicit. -/
def kappaUnit67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67) : (𝓞 K)ˣ :=
  -hζ.unit'⁻¹

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- The literal unit identity relating Vandiver's `κ` to `(ζ - 1)²`. -/
lemma kappa_eq_kappaUnit67_mul_sq {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    kappa hζ = (kappaUnit67 hζ : 𝓞 K) *
      ((hζ.unit' : 𝓞 K) - 1) ^ 2 := by
  simp only [kappa, kappaUnit67, Units.val_neg, neg_mul, pow_two]
  have hz : ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
      (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hinv : (1 : 𝓞 K) - (hζ.unit'⁻¹ : (𝓞 K)ˣ) =
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) * ((hζ.unit' : 𝓞 K) - 1) := by
    rw [mul_sub, mul_one, hz]
  rw [hinv]
  ring

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- Power form of `kappa_eq_kappaUnit67_mul_sq`. -/
lemma kappa_pow_eq_kappaUnit67_pow_mul {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (m : ℕ) :
    kappa hζ ^ m = ((kappaUnit67 hζ ^ m : (𝓞 K)ˣ) : 𝓞 K) *
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * m) := by
  rw [kappa_eq_kappaUnit67_mul_sq, mul_pow, ← Units.val_pow_eq_pow_val,
    ← pow_mul]

/-- The coefficient unit obtained when Vandiver's equation (6) is written
in the `(ζ - 1)`-adic format used by `FltRegular.CaseII.InductionStep`. -/
def historicalRegularUnit67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (s : HistoricalState hζ) : (𝓞 K)ˣ :=
  s.eta * kappaUnit67 hζ ^ (s.m * 67)

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- Every historical state at exponent `67` is literally an input to the
generic factor-ideal construction, with upstream depth parameter
`2 * m - 1`:

`ω^67 + θ^67 = ε * (((ζ - 1)^(2*m) * ξ)^67)`.

Thus all algebra and coprimality lemmas in the existing regular-prime
induction step up to its class-group principalization point can be reused
without alteration. -/
lemma historicalState_regularEquation67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    s.omega ^ 67 + s.theta ^ 67 = historicalRegularUnit67 hζ s *
      (((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 1) + 1) * s.xi) ^ 67 := by
  have hm : 1 ≤ 2 * s.m := by
    have := s.one_lt_m
    omega
  rw [Nat.sub_add_cancel hm]
  rw [s.equation, kappa_pow_eq_kappaUnit67_pow_mul]
  simp only [historicalRegularUnit67, mul_pow, ← Units.val_pow_eq_pow_val,
    Units.val_mul]
  rw [← pow_mul]
  ac_rfl

/-- In every historical state, `θ` is prime to `(ζ - 1)`.  This discharges
the `hy` input of the generic factor-ideal construction directly from the
state equation and pairwise coprimality. -/
lemma historicalState_theta_not_dvd67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ s.theta := by
  intro htheta
  have hsum : (hζ.unit' : 𝓞 K) - 1 ∣
      s.omega ^ 67 + s.theta ^ 67 :=
    zeta_sub_one_dvd (p := 67) hζ
      (historicalState_regularEquation67 hζ s)
  have homegaPow : (hζ.unit' : 𝓞 K) - 1 ∣ s.omega ^ 67 := by
    simpa using dvd_sub hsum (dvd_pow (n := 67) htheta (by norm_num))
  have homega : (hζ.unit' : 𝓞 K) - 1 ∣ s.omega :=
    hζ.zeta_sub_one_prime'.dvd_of_dvd_pow homegaPow
  exact hζ.zeta_sub_one_prime'.not_unit
    (s.coprime_omega_theta.isUnit_of_dvd' homega htheta)

/-! ## Identifying the real distinguished factor -/

/-- For a factorization with real entries at exponent `67`, the unique
linear factor carrying the excess `(ζ - 1)`-power is the factor at the
root `1`.

The allocated distinguished root is some `ζ^i`.  If its divided linear
factor is still divisible by `ζ - 1`, complex conjugation shows that the
factor at `ζ⁻ⁱ` has the same property.  Injectivity of the factor residues
therefore gives `ζ^i = ζ⁻ⁱ`.  Since `67` is odd, this forces `i = 0`.

This is the precise realness argument used implicitly when Vandiver assigns
the high ramified power to `ω + θ`; no ideal-class theorem enters. -/
theorem distinguishedRoot_eq_one_of_real67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 67 + y ^ 67 = ε *
      ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 67)
    (hy : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ y)
    (hxreal : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hyreal : NumberField.IsCMField.ringOfIntegersComplexConj K y = y) :
    zeta_sub_one_dvd_root (by norm_num : 67 ≠ 2) hζ e hy =
      oneNthRoot (K := K) (p := 67) := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let η0 := zeta_sub_one_dvd_root (by norm_num : 67 ≠ 2) hζ e hy
  let q0 : 𝓞 K :=
    div_zeta_sub_one (by norm_num : 67 ≠ 2) hζ e η0
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hq0 : π ∣ q0 := by
    simpa only [π, q0, η0] using
      (Ideal.Quotient.eq_zero_iff_dvd
        ((hζ.unit' : 𝓞 K) - 1)
        (div_zeta_sub_one (by norm_num : 67 ≠ 2) hζ e
          (zeta_sub_one_dvd_root
            (by norm_num : 67 ≠ 2) hζ e hy))).mp
        (zeta_sub_one_dvd_root_spec
          (by norm_num : 67 ≠ 2) hζ e hy)
  have hetaPow : (η0 : 𝓞 K) ^ 67 = 1 := by
    exact (Polynomial.mem_nthRootsFinset
      (by norm_num : 0 < 67) (1 : 𝓞 K)).mp η0.prop
  obtain ⟨i, hi, heta⟩ :=
    hζ.unit'_coe.eq_pow_of_pow_eq_one hetaPow
  by_cases hi0 : i = 0
  · apply Subtype.ext
    change (η0 : 𝓞 K) = 1
    rw [← heta, hi0, pow_zero]
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    let j : ℕ := 67 - i
    have hj : j < 67 := by
      dsimp [j]
      omega
    let ηj : Polynomial.nthRootsFinset 67 (1 : 𝓞 K) :=
      ⟨(hζ.unit' : 𝓞 K) ^ j, by
        rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 67)]
        rw [← pow_mul, show j * 67 = 67 * j by omega, pow_mul,
          hζ.unit'_coe.pow_eq_one, one_pow]⟩
    let qj : 𝓞 K :=
      div_zeta_sub_one (by norm_num : 67 ≠ 2) hζ e ηj
    have hzpowU : hζ.unit' ^ 67 = 1 := by
      apply Units.ext
      apply NumberField.RingOfIntegers.ext
      change ζ ^ 67 = 1
      exact hζ.pow_eq_one
    have hinvpowU : (hζ.unit'⁻¹) ^ i = hζ.unit' ^ j := by
      apply mul_left_cancel (a := hζ.unit' ^ i)
      calc
        hζ.unit' ^ i * (hζ.unit'⁻¹) ^ i = 1 := by
          rw [← mul_pow]
          simp
        _ = hζ.unit' ^ (i + j) := by
          rw [show i + j = 67 by dsimp [j]; omega, hzpowU]
        _ = hζ.unit' ^ i * hζ.unit' ^ j := by rw [pow_add]
    have hconjζ :
        NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹ : (𝓞 K)ˣ) := by
      exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
        (unitsComplexConj_zeta67 hζ)
    let u : (𝓞 K)ˣ := -hζ.unit'⁻¹
    have hconjπ :
        NumberField.IsCMField.ringOfIntegersComplexConj K π =
          (u : 𝓞 K) * π := by
      dsimp [π, u]
      rw [map_sub, map_one, hconjζ]
      have hinv :
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) * (hζ.unit' : 𝓞 K) = 1 := by
        rw [← Units.val_mul]
        simp
      simp only [neg_mul, mul_sub, hinv]
      ring
    have hconjη0 :
        NumberField.IsCMField.ringOfIntegersComplexConj K (η0 : 𝓞 K) =
          (ηj : 𝓞 K) := by
      rw [← heta, map_pow, hconjζ]
      exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hinvpowU
    obtain ⟨k, hk⟩ := hq0
    have hCq0 :
        NumberField.IsCMField.ringOfIntegersComplexConj K q0 =
          NumberField.IsCMField.ringOfIntegersComplexConj K π *
            NumberField.IsCMField.ringOfIntegersComplexConj K k := by
      rw [hk, map_mul]
    have hq0mul : q0 * π = x + y * (η0 : 𝓞 K) := by
      exact div_zeta_sub_one_mul_zeta_sub_one
        (by norm_num : 67 ≠ 2) hζ e η0
    have hconjfactor := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hq0mul
    rw [map_mul, map_add, map_mul, hxreal, hyreal,
      hconjπ, hconjη0] at hconjfactor
    have hqjmul : qj * π = x + y * (ηj : 𝓞 K) := by
      exact div_zeta_sub_one_mul_zeta_sub_one
        (by norm_num : 67 ≠ 2) hζ e ηj
    have hqjEq : qj = π * ((u : 𝓞 K) ^ 2 *
        NumberField.IsCMField.ringOfIntegersComplexConj K k) := by
      apply mul_right_cancel₀ hπ0
      calc
        qj * π = x + y * (ηj : 𝓞 K) := hqjmul
        _ = NumberField.IsCMField.ringOfIntegersComplexConj K q0 *
            ((u : 𝓞 K) * π) := hconjfactor.symm
        _ = ((u : 𝓞 K) * π *
              NumberField.IsCMField.ringOfIntegersComplexConj K k) *
            ((u : 𝓞 K) * π) := by rw [hCq0, hconjπ]
        _ = (π * ((u : 𝓞 K) ^ 2 *
              NumberField.IsCMField.ringOfIntegersComplexConj K k)) * π := by
            ring
    have hqj : π ∣ qj := ⟨_, hqjEq⟩
    have hηeq : η0 = ηj := by
      apply div_zeta_sub_one_Injective
        (by norm_num : 67 ≠ 2) hζ e hy
      calc
        Ideal.Quotient.mk (Ideal.span {π}) q0 = 0 :=
          (Ideal.Quotient.eq_zero_iff_dvd π q0).2 ⟨k, hk⟩
        _ = Ideal.Quotient.mk (Ideal.span {π}) qj :=
          ((Ideal.Quotient.eq_zero_iff_dvd π qj).2 hqj).symm
    have hpows : (hζ.unit' : 𝓞 K) ^ i =
        (hζ.unit' : 𝓞 K) ^ j := by
      calc
        (hζ.unit' : 𝓞 K) ^ i = (η0 : 𝓞 K) := heta
        _ = (ηj : 𝓞 K) := congrArg Subtype.val hηeq
        _ = (hζ.unit' : 𝓞 K) ^ j := rfl
    have hij : i = j := hζ.unit'_coe.pow_inj hi hj hpows
    dsimp [j] at hij
    omega

/-- In a real historical state, the distinguished factor is `ω + θ` and
it carries far more than the `68` local powers needed for Lemma 1. -/
theorem historicalState_omega_add_theta_highDivisibility67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ((hζ.unit' : 𝓞 K) - 1) ^ 68 ∣ s.omega + s.theta := by
  let e := historicalState_regularEquation67 hζ s
  let hy := historicalState_theta_not_dvd67 hζ s
  have hroot := distinguishedRoot_eq_one_of_real67 hζ e hy hs.1 hs.2.1
  have hhigh := distinguishedFactor_highDivisibility
    (by norm_num : 67 ≠ 2) hζ e hy
  rw [hroot] at hhigh
  simp only [oneNthRoot, mul_one] at hhigh
  have hle : 68 ≤ (2 * s.m - 1) * 67 + 1 := by
    have hm := s.one_lt_m
    omega
  exact (pow_dvd_pow_of_dvd_of_le dvd_rfl hle).trans hhigh

/-! ### The distinguished real factor and equation (8a) -/

/-- The fixed-denominator factor at the root `1`; it is
`(ω + θ) / (ζ - 1)`. -/
noncomputable def historicalOneFactor67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : 𝓞 K :=
  div_zeta_sub_one (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (oneNthRoot (K := K) (p := 67))

/-- The allocated ideal root of the distinguished factor at `1`. -/
noncomputable def historicalOneFactorIdeal67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : Ideal (𝓞 K) :=
  root_div_zeta_sub_one_dvd_gcd (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
    (oneNthRoot (K := K) (p := 67))

/-- After removing the forced `(ζ - 1) ^ (2*m - 1)` from the allocated
root at `1`, this is the residual ideal whose principal generator occurs in
Vandiver's equation (8a). -/
noncomputable def historicalEquationEightAIdeal67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : Ideal (𝓞 K) :=
  a_eta_zero_dvd_p_pow (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)

/-- Multiplying the fixed-denominator factor at `1` back by `ζ - 1`
recovers `ω + θ`. -/
lemma historicalOneFactor_mul_zeta_sub_one67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    historicalOneFactor67 hζ s * ((hζ.unit' : 𝓞 K) - 1) =
      s.omega + s.theta := by
  simpa only [historicalOneFactor67, oneNthRoot, mul_one] using
    (div_zeta_sub_one_mul_zeta_sub_one
      (by norm_num : 67 ≠ 2) hζ
      (historicalState_regularEquation67 hζ s)
      (oneNthRoot (K := K) (p := 67)))

set_option maxRecDepth 2000 in
/-- The allocated ideal at the root `1` has 67th power generated by its
literal fixed-denominator factor. -/
lemma historicalOneFactorIdeal_pow67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    historicalOneFactorIdeal67 hζ s ^ 67 =
      Ideal.span {historicalOneFactor67 hζ s} := by
  exact (linearFactorQuotient_span_eq_factorRoot_pow
    (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
    s.coprime_omega_theta
    (oneNthRoot (K := K) (p := 67))).symm

/-- The forced ramified part times the residual equation-(8a) ideal is the
allocated ideal at the root `1`. -/
lemma historicalEquationEightAIdeal_spec67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ^ (2 * s.m - 1) *
        historicalEquationEightAIdeal67 hζ s =
      historicalOneFactorIdeal67 hζ s := by
  have hspec := a_eta_zero_dvd_p_pow_spec
    (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
  rw [distinguishedRoot_eq_one_of_real67 hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s) hs.1 hs.2.1] at hspec
  simpa only [historicalEquationEightAIdeal67,
    historicalOneFactorIdeal67] using hspec

/-- The real factor `ω + θ` is nonzero in every historical state. -/
lemma historicalState_omega_add_theta_ne_zero67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    s.omega + s.theta ≠ 0 := by
  intro hsum
  have htheta : s.theta = -s.omega := by
    linear_combination hsum
  have hkappa0 : kappa hζ ≠ 0 := by
    rw [kappa_eq_kappaUnit67_mul_sq]
    exact mul_ne_zero (kappaUnit67 hζ).isUnit.ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr
        (hζ.unit'_coe.ne_one (by norm_num))))
  have hrhs :
      (s.eta : 𝓞 K) * (kappa hζ ^ s.m * s.xi) ^ 67 ≠ 0 :=
    mul_ne_zero s.eta.isUnit.ne_zero
      (pow_ne_zero 67
        (mul_ne_zero (pow_ne_zero s.m hkappa0) s.xi_ne_zero))
  apply hrhs
  rw [← s.equation, htheta]
  simp only [Odd.neg_pow (by norm_num : Odd 67), add_neg_cancel]

/-- The exact `κ`-power displayed in equation (8a) divides `ω + θ`.
The exponent identity is

`2 * (67*m - 33) = (2*m - 1)*67 + 1`.

Thus this is the element-level counterpart of the forced ramified ideal
factorization above. -/
lemma historicalState_kappaPower_dvd_omega_add_theta67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    kappa hζ ^ (67 * s.m - 33) ∣ s.omega + s.theta := by
  let E : ℕ := 67 * s.m - 33
  let N : ℕ := (2 * s.m - 1) * 67 + 1
  have hexp : 2 * E = N := by
    dsimp [E, N]
    have hm := s.one_lt_m
    omega
  have hroot := distinguishedRoot_eq_one_of_real67 hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s) hs.1 hs.2.1
  have hhigh := distinguishedFactor_highDivisibility
    (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
  rw [hroot] at hhigh
  simp only [oneNthRoot, mul_one] at hhigh
  obtain ⟨c, hc⟩ : ∃ c : 𝓞 K,
      s.omega + s.theta =
        ((hζ.unit' : 𝓞 K) - 1) ^ N * c := by
    simpa only [N] using hhigh
  let u : (𝓞 K)ˣ := kappaUnit67 hζ ^ E
  refine ⟨(u⁻¹ : (𝓞 K)ˣ) * c, ?_⟩
  rw [kappa_pow_eq_kappaUnit67_pow_mul, hexp]
  change s.omega + s.theta =
    ((u : 𝓞 K) * ((hζ.unit' : 𝓞 K) - 1) ^ N) *
      ((u⁻¹ : (𝓞 K)ˣ) * c)
  rw [hc]
  calc
    ((hζ.unit' : 𝓞 K) - 1) ^ N * c =
        (((u : 𝓞 K) * (u⁻¹ : (𝓞 K)ˣ)) *
          ((hζ.unit' : 𝓞 K) - 1) ^ N) * c := by
      rw [← Units.val_mul]
      simp
    _ = ((u : 𝓞 K) * ((hζ.unit' : 𝓞 K) - 1) ^ N) *
        ((u⁻¹ : (𝓞 K)ˣ) * c) := by ring

/-- The literal integral quotient in equation (8a). -/
noncomputable def historicalEquationEightAQuotient67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) : 𝓞 K :=
  (historicalState_kappaPower_dvd_omega_add_theta67 hζ s hs).choose

/-- Definition equation for the integral quotient in (8a). -/
lemma historicalEquationEightAQuotient_spec67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    s.omega + s.theta =
      kappa hζ ^ (67 * s.m - 33) *
        historicalEquationEightAQuotient67 hζ s hs :=
  (historicalState_kappaPower_dvd_omega_add_theta67 hζ s hs).choose_spec

/-- The quotient occurring in equation (8a) is real. -/
lemma historicalEquationEightAQuotient_real67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (historicalEquationEightAQuotient67 hζ s hs) =
      historicalEquationEightAQuotient67 hζ s hs := by
  let E : ℕ := 67 * s.m - 33
  let q : 𝓞 K := historicalEquationEightAQuotient67 hζ s hs
  have hkappa0 : kappa hζ ^ E ≠ 0 := by
    rw [kappa_pow_eq_kappaUnit67_pow_mul]
    exact mul_ne_zero (kappaUnit67 hζ ^ E).isUnit.ne_zero
      (pow_ne_zero (2 * E) (sub_ne_zero.mpr
        (hζ.unit'_coe.ne_one (by norm_num))))
  have hq := historicalEquationEightAQuotient_spec67 hζ s hs
  change s.omega + s.theta = kappa hζ ^ E * q at hq
  apply mul_left_cancel₀ hkappa0
  calc
    kappa hζ ^ E *
        NumberField.IsCMField.ringOfIntegersComplexConj K q =
      NumberField.IsCMField.ringOfIntegersComplexConj K
        (kappa hζ ^ E * q) := by
          rw [map_mul, map_pow, ringOfIntegersComplexConj_kappa hζ]
    _ = NumberField.IsCMField.ringOfIntegersComplexConj K
        (s.omega + s.theta) := by rw [← hq]
    _ = s.omega + s.theta := by rw [map_add, hs.1, hs.2.1]
    _ = kappa hζ ^ E * q := hq

/-- The quotient in equation (8a) is nonzero. -/
lemma historicalEquationEightAQuotient_ne_zero67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    historicalEquationEightAQuotient67 hζ s hs ≠ 0 := by
  intro hq
  apply historicalState_omega_add_theta_ne_zero67 hζ s
  rw [historicalEquationEightAQuotient_spec67 hζ s hs, hq, mul_zero]

/-- Principal-ideal form of the exact ramified exponent in equation (8a). -/
lemma historical_span_kappaPower67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    Ideal.span ({kappa hζ ^ (67 * s.m - 33)} : Set (𝓞 K)) =
      Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ^
        ((2 * s.m - 1) * 67 + 1) := by
  let E : ℕ := 67 * s.m - 33
  let N : ℕ := (2 * s.m - 1) * 67 + 1
  have hexp : 2 * E = N := by
    dsimp [E, N]
    have hm := s.one_lt_m
    omega
  rw [show 67 * s.m - 33 = E by rfl,
    kappa_pow_eq_kappaUnit67_pow_mul, hexp]
  change Ideal.span
      ({((kappaUnit67 hζ ^ E : (𝓞 K)ˣ) : 𝓞 K) *
        ((hζ.unit' : 𝓞 K) - 1) ^ N} : Set (𝓞 K)) =
    Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ^ N
  rw [← Ideal.span_singleton_mul_span_singleton]
  rw [Ideal.span_singleton_eq_top.mpr
    (kappaUnit67 hζ ^ E).isUnit, ← Ideal.one_eq_top, one_mul]
  exact (Ideal.span_singleton_pow ((hζ.unit' : 𝓞 K) - 1) N).symm

set_option maxRecDepth 3000 in
/-- The residual equation-(8a) ideal has 67th power generated by the
literal real quotient `(ω + θ) / κ^(67*m-33)`. -/
theorem historicalEquationEightAIdeal_pow67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    historicalEquationEightAIdeal67 hζ s ^ 67 =
      Ideal.span {historicalEquationEightAQuotient67 hζ s hs} := by
  let P : Ideal (𝓞 K) :=
    Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K))
  let A : Ideal (𝓞 K) := historicalOneFactorIdeal67 hζ s
  let J : Ideal (𝓞 K) := historicalEquationEightAIdeal67 hζ s
  let qone : 𝓞 K := historicalOneFactor67 hζ s
  let qzero : 𝓞 K := historicalEquationEightAQuotient67 hζ s hs
  let E : ℕ := 67 * s.m - 33
  let d : ℕ := 2 * s.m - 1
  let N : ℕ := d * 67 + 1
  have hPJ : P ^ d * J = A := by
    simpa only [P, d, J, A] using
      historicalEquationEightAIdeal_spec67 hζ s hs
  have hA67 : A ^ 67 = Ideal.span {qone} := by
    simpa only [A, qone] using historicalOneFactorIdeal_pow67 hζ s
  have hqone : qone * ((hζ.unit' : 𝓞 K) - 1) =
      s.omega + s.theta := by
    simpa only [qone] using historicalOneFactor_mul_zeta_sub_one67 hζ s
  have hqzero : s.omega + s.theta = kappa hζ ^ E * qzero := by
    simpa only [E, qzero] using
      historicalEquationEightAQuotient_spec67 hζ s hs
  have hspanK : Ideal.span {kappa hζ ^ E} = P ^ N := by
    simpa only [E, P, N, d] using historical_span_kappaPower67 hζ s
  have hramified : P ^ N * J ^ 67 =
      Ideal.span {s.omega + s.theta} := by
    calc
      P ^ N * J ^ 67 = P * (P ^ d * J) ^ 67 := by
        dsimp only [N]
        rw [mul_pow, ← pow_mul]
        rw [pow_succ']
        ring
      _ = P * A ^ 67 := by rw [hPJ]
      _ = P * Ideal.span {qone} := by rw [hA67]
      _ = Ideal.span
          {((hζ.unit' : 𝓞 K) - 1) * qone} := by
        dsimp only [P]
        rw [Ideal.span_singleton_mul_span_singleton]
      _ = Ideal.span {s.omega + s.theta} := by
        congr 2
        rw [mul_comm, hqone]
  have hspanEq : Ideal.span {kappa hζ ^ E} * J ^ 67 =
      Ideal.span {kappa hζ ^ E} * Ideal.span {qzero} := by
    calc
      Ideal.span {kappa hζ ^ E} * J ^ 67 =
          P ^ N * J ^ 67 := by rw [hspanK]
      _ = Ideal.span {s.omega + s.theta} := hramified
      _ = Ideal.span {kappa hζ ^ E * qzero} := by rw [hqzero]
      _ = Ideal.span {kappa hζ ^ E} * Ideal.span {qzero} :=
        (Ideal.span_singleton_mul_span_singleton _ _).symm
  have hkappa0 : kappa hζ ^ E ≠ 0 := by
    rw [kappa_pow_eq_kappaUnit67_pow_mul]
    exact mul_ne_zero (kappaUnit67 hζ ^ E).isUnit.ne_zero
      (pow_ne_zero (2 * E) (sub_ne_zero.mpr
        (hζ.unit'_coe.ne_one (by norm_num))))
  have hspan0 : Ideal.span {kappa hζ ^ E} ≠ 0 := by
    simpa only [ne_eq, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot] using hkappa0
  exact mul_left_cancel₀ hspan0 hspanEq

/-- The fixed-denominator linear factor at `ζ` for a historical state. -/
noncomputable def historicalZetaFactor67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : 𝓞 K :=
  div_zeta_sub_one (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (zetaNthRoot (K := K) (p := 67) hζ)

/-- The fixed-denominator conjugate linear factor at `ζ⁻¹`. -/
noncomputable def historicalInverseZetaFactor67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : 𝓞 K :=
  div_zeta_sub_one (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (inverseZetaNthRoot (K := K) (p := 67) hζ)

/-- The unit-normalized inverse factor.  Multiplication by `-ζ` changes
the fixed denominator `ζ - 1` to its conjugate normalization. -/
noncomputable def normalizedHistoricalInverseZetaFactor67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : 𝓞 K :=
  ((-hζ.unit' : (𝓞 K)ˣ) : 𝓞 K) *
    historicalInverseZetaFactor67 hζ s

/-- The actual normalized factor product to which Vandiver applies
Lemma 1 is Kummer-primary in every real historical state. -/
theorem historicalConjugateFactorProduct_isKummerPrimary67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    IsKummerPrimary hζ
      (historicalZetaFactor67 hζ s *
        normalizedHistoricalInverseZetaFactor67 hζ s ^ 66) := by
  simpa only [historicalZetaFactor67,
    normalizedHistoricalInverseZetaFactor67,
    historicalInverseZetaFactor67] using
    normalizedConjugateLinearFactor_isKummerPrimary
      (by norm_num : 67 ≠ 2) hζ
      (historicalState_regularEquation67 hζ s)
      (historicalState_theta_not_dvd67 hζ s)
      (historicalState_omega_add_theta_highDivisibility67 hζ s hs)

/-- The allocated ideal root of the linear factor at `ζ`. -/
noncomputable def historicalZetaFactorIdeal67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : Ideal (𝓞 K) :=
  root_div_zeta_sub_one_dvd_gcd (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
    (zetaNthRoot (K := K) (p := 67) hζ)

/-- The allocated ideal root of the conjugate linear factor at `ζ⁻¹`. -/
noncomputable def historicalInverseZetaFactorIdeal67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) : Ideal (𝓞 K) :=
  root_div_zeta_sub_one_dvd_gcd (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
    (inverseZetaNthRoot (K := K) (p := 67) hζ)

set_option maxRecDepth 2000 in
/-- The allocated ideal at `ζ` has 67th power generated by the literal
historical linear factor. -/
theorem historicalZetaFactorIdeal_pow67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    historicalZetaFactorIdeal67 hζ s ^ 67 =
      Ideal.span {historicalZetaFactor67 hζ s} := by
  exact (linearFactorQuotient_span_eq_factorRoot_pow
    (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
    s.coprime_omega_theta
    (zetaNthRoot (K := K) (p := 67) hζ)).symm

set_option maxRecDepth 2000 in
/-- The allocated inverse ideal has 67th power generated by the
unit-normalized inverse factor. -/
theorem historicalInverseZetaFactorIdeal_pow67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    historicalInverseZetaFactorIdeal67 hζ s ^ 67 =
      Ideal.span {normalizedHistoricalInverseZetaFactor67 hζ s} := by
  calc
    historicalInverseZetaFactorIdeal67 hζ s ^ 67 =
        Ideal.span {historicalInverseZetaFactor67 hζ s} :=
      (linearFactorQuotient_span_eq_factorRoot_pow
        (by norm_num : 67 ≠ 2) hζ
        (historicalState_regularEquation67 hζ s)
        (historicalState_theta_not_dvd67 hζ s)
        s.coprime_omega_theta
        (inverseZetaNthRoot (K := K) (p := 67) hζ)).symm
    _ = Ideal.span {normalizedHistoricalInverseZetaFactor67 hζ s} :=
      Ideal.span_singleton_eq_span_singleton.mpr
        (associated_unit_mul_right _ _ (-hζ.unit').isUnit)

/-- Complex conjugation sends the fixed-denominator factor at `ζ` exactly
to the normalized inverse factor `(-ζ) q₋`. -/
theorem ringOfIntegersComplexConj_historicalZetaFactor67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (historicalZetaFactor67 hζ s) =
      normalizedHistoricalInverseZetaFactor67 hζ s := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let qplus : 𝓞 K := historicalZetaFactor67 hζ s
  let qminus : 𝓞 K := historicalInverseZetaFactor67 hζ s
  let u : (𝓞 K)ˣ := -hζ.unit'⁻¹
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hconjζ :
      NumberField.IsCMField.ringOfIntegersComplexConj K
        (hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹ : (𝓞 K)ˣ) := by
    exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
      (unitsComplexConj_zeta67 hζ)
  have hconjπ :
      NumberField.IsCMField.ringOfIntegersComplexConj K π =
        (u : 𝓞 K) * π := by
    dsimp [π, u]
    rw [map_sub, map_one, hconjζ]
    have hinv :
        (hζ.unit'⁻¹ : (𝓞 K)ˣ) * (hζ.unit' : 𝓞 K) = 1 := by
      rw [← Units.val_mul]
      simp
    simp only [neg_mul, mul_sub, hinv]
    ring
  have hqplusMul : qplus * π =
      s.omega + s.theta * (hζ.unit' : 𝓞 K) := by
    exact div_zeta_sub_one_mul_zeta_sub_one
      (by norm_num : 67 ≠ 2) hζ
      (historicalState_regularEquation67 hζ s)
      (zetaNthRoot (K := K) (p := 67) hζ)
  have hqminusMul : qminus * π =
      s.omega + s.theta * (hζ.unit'⁻¹ : (𝓞 K)ˣ) := by
    exact div_zeta_sub_one_mul_zeta_sub_one
      (by norm_num : 67 ≠ 2) hζ
      (historicalState_regularEquation67 hζ s)
      (inverseZetaNthRoot (K := K) (p := 67) hζ)
  have hconjFactor := congrArg
    (NumberField.IsCMField.ringOfIntegersComplexConj K) hqplusMul
  rw [map_mul, map_add, map_mul, hs.1, hs.2.1,
    hconjζ, hconjπ] at hconjFactor
  have hquotient :
      NumberField.IsCMField.ringOfIntegersComplexConj K qplus *
        (u : 𝓞 K) = qminus := by
    apply mul_right_cancel₀ hπ0
    calc
      (NumberField.IsCMField.ringOfIntegersComplexConj K qplus *
          (u : 𝓞 K)) * π =
          NumberField.IsCMField.ringOfIntegersComplexConj K qplus *
            ((u : 𝓞 K) * π) := by ring
      _ = s.omega + s.theta * (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
        hconjFactor
      _ = qminus * π := hqminusMul.symm
  have huinv : u⁻¹ = -hζ.unit' := by
    dsimp [u]
    simp
  change NumberField.IsCMField.ringOfIntegersComplexConj K qplus =
    ((-hζ.unit' : (𝓞 K)ˣ) : 𝓞 K) * qminus
  calc
    NumberField.IsCMField.ringOfIntegersComplexConj K qplus =
        (NumberField.IsCMField.ringOfIntegersComplexConj K qplus *
          (u : 𝓞 K)) * (u⁻¹ : (𝓞 K)ˣ) := by
      rw [mul_assoc, ← Units.val_mul]
      simp
    _ = qminus * (u⁻¹ : (𝓞 K)ˣ) := by rw [hquotient]
    _ = ((-hζ.unit' : (𝓞 K)ˣ) : 𝓞 K) * qminus := by
      rw [huinv]
      ring

/-- The normalized historical factor at `ζ` is prime to the ramified
uniformizer. -/
theorem historicalZetaFactor_not_ramified67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ historicalZetaFactor67 hζ s := by
  have hlocal := normalizedConjugateLinearFactors
    (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
    (historicalState_omega_add_theta_highDivisibility67 hζ s hs)
  simpa only [historicalZetaFactor67] using hlocal.1

/-- The normalized historical factor and its conjugate agree modulo
`(ζ - 1)^67`.  This is the local compatibility behind Vandiver's claim
that the unit in equation (8) may be chosen real. -/
theorem historicalZetaFactor_sub_conj_highDivisibility67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ((hζ.unit' : 𝓞 K) - 1) ^ 67 ∣
      historicalZetaFactor67 hζ s -
        NumberField.IsCMField.ringOfIntegersComplexConj K
          (historicalZetaFactor67 hζ s) := by
  have hlocal := normalizedConjugateLinearFactors
    (by norm_num : 67 ≠ 2) hζ
    (historicalState_regularEquation67 hζ s)
    (historicalState_theta_not_dvd67 hζ s)
    (historicalState_omega_add_theta_highDivisibility67 hζ s hs)
  rw [ringOfIntegersComplexConj_historicalZetaFactor67 hζ s hs]
  simpa only [historicalZetaFactor67, historicalInverseZetaFactor67,
    normalizedHistoricalInverseZetaFactor67] using hlocal.2.2

set_option maxRecDepth 2000 in
/-- Vandiver's equation (7a) for the literal historical factor pair,
conditional only on the exact global Lemma-1 theorem.  The local primary
congruence and both ideal-power identities are already proved above. -/
theorem exists_historicalEquationSevenA67
    (hlemma : LemmaOne K 67)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ r : 𝓞 K,
      historicalZetaFactorIdeal67 hζ s *
          historicalInverseZetaFactorIdeal67 hζ s ^ 66 =
        Ideal.span {r} := by
  exact exists_equationSevenA_generator hlemma hζ
    (historicalZetaFactorIdeal67 hζ s)
    (historicalInverseZetaFactorIdeal67 hζ s)
    (historicalZetaFactor67 hζ s)
    (normalizedHistoricalInverseZetaFactor67 hζ s)
    (historicalZetaFactorIdeal_pow67 hζ s)
    (historicalInverseZetaFactorIdeal_pow67 hζ s)
    (by simpa using
      historicalConjugateFactorProduct_isKummerPrimary67 hζ s hs)

/-! ## Conjugation-compatible principal generators -/

/-! ### The exact plus/minus ideal-class split

The plus-class-number result does **not** by itself prove
`RelevantIdealQuotientsPrincipal` at the irregular prime `67`: a genuine
`67`-torsion minus class may remain.  The definitions and theorems below
make that obstruction literal.  For a relevant quotient `I`, its symmetric
component is `I * conj(I)` and its antisymmetric component is
`I / conj(I)`.  Since `I ^ 67` is already principal, once the symmetric
component is principal, principalizing `I` is equivalent to principalizing
the antisymmetric component.

This is the precise interface between the Sinnott--Kummer plus-class theorem
and Kummer's primary test on the remaining irregular minus component. -/

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The exact class-group consequence of the exponent-`67`
Sinnott--Kummer theorem used by Vandiver in (7b) and again after (9): a
fractional ideal of the maximal real field whose `67`th power is principal
is already principal.

The fact that a particular conjugation-invariant ideal of `K` is the
extension of such a real ideal is a separate descent-of-ideals statement;
keeping the two steps separate prevents the plus-class computation from
being misapplied to an arbitrary ideal of the CM field. -/
theorem realFractionalIdeal_isPrincipal_of_pow67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (I : FractionalIdeal (𝓞 K⁺)⁰ K⁺)
    (hpow : Submodule.IsPrincipal
      ((I ^ 67 : FractionalIdeal (𝓞 K⁺)⁰ K⁺) :
        Submodule (𝓞 K⁺) K⁺)) :
    Submodule.IsPrincipal (I : Submodule (𝓞 K⁺) K⁺) := by
  exact fractionalIdeal_isPrincipal_of_pow_of_not_dvd_classNumber
    (by norm_num) (Fermat.SixtySeven.SinnottKummer.not_dvd_classNumber hzeta)
    I hpow

set_option maxRecDepth 2000 in
/-- Element-level form of the same real-class calculation.  This is the
literal conclusion used in Vandiver's (7d) and after (9): if a real ideal
has `67`th power `(a)`, then it has a real generator `ρ`, and `a` differs
from `ρ ^ 67` by a real unit. -/
theorem exists_real_unit_mul_pow_generator67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (I : Ideal (𝓞 K⁺)) (a : 𝓞 K⁺)
    (hpow : I ^ 67 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      I = Ideal.span {ρ} ∧ a = ε * ρ ^ 67 := by
  exact exists_unit_mul_pow_eq_of_ideal_pow_eq_span
    (F := K⁺) (p := 67) (by norm_num)
    (Fermat.SixtySeven.SinnottKummer.not_dvd_classNumber hzeta) I a hpow

set_option maxRecDepth 2000 in
/-- Vandiver's real-ideal step in the relative-norm form naturally
produced by (7b).  If `J ^ 67 = (a)` in the cyclotomic ring, multiplicativity
of the relative ideal norm gives

`Norm(J) ^ 67 = (intNorm(a))`

in the maximal real ring.  The unconditional result `67 ∤ h⁺` then
provides a real generator `ρ` and a real unit `ε` with
`intNorm(a) = ε * ρ ^ 67`.

This packages the class-number argument in (7b) without any general
descent theorem for conjugation-stable ideals. -/
theorem exists_realGenerator_of_relativeNorm67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hpow : J ^ 67 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      Ideal.relNorm (𝓞 K⁺) J = Ideal.span {ρ} ∧
      Algebra.intNorm (𝓞 K⁺) (𝓞 K) a = ε * ρ ^ 67 := by
  apply exists_real_unit_mul_pow_generator67 hzeta
    (Ideal.relNorm (𝓞 K⁺) J) (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a)
  calc
    Ideal.relNorm (𝓞 K⁺) J ^ 67 =
        Ideal.relNorm (𝓞 K⁺) (J ^ 67) := by
      rw [map_pow]
    _ = Ideal.relNorm (𝓞 K⁺) (Ideal.span {a}) := by rw [hpow]
    _ = Ideal.span {Algebra.intNorm (𝓞 K⁺) (𝓞 K) a} :=
      Ideal.relNorm_singleton (𝓞 K⁺) a

/-- In the quadratic CM extension, the integral norm of a cyclotomic
integer is the product of that integer and its complex conjugate.

The proof makes the two automorphisms literal: the Galois group over the
maximal real field has cardinality two, and its elements are the identity
and `complexConj`. -/
theorem algebraMap_intNorm_eq_mul_conj67 (a : 𝓞 K) :
    algebraMap (𝓞 K⁺) (𝓞 K) (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a) =
      a * NumberField.IsCMField.ringOfIntegersComplexConj K a := by
  classical
  apply NumberField.RingOfIntegers.ext
  change algebraMap K⁺ K
      (algebraMap (𝓞 K⁺) K⁺ (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a)) =
    (a : K) * NumberField.IsCMField.complexConj K (a : K)
  rw [Algebra.algebraMap_intNorm (A := 𝓞 K⁺) (K := K⁺) (L := K)
    (B := 𝓞 K)]
  rw [Algebra.norm_eq_prod_automorphisms]
  let c : Gal(K/K⁺) := NumberField.IsCMField.complexConj K
  have hc : (1 : Gal(K/K⁺)) ≠ c :=
    (NumberField.IsCMField.complexConj_ne_one K).symm
  have hcard : Fintype.card Gal(K/K⁺) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K]
  have hpair : ({1, c} : Finset (Gal(K/K⁺))) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hcard, hc]
  rw [← hpair]
  simp [c, hc]

set_option maxRecDepth 2000 in
/-- Vandiver's equation (7d), derived directly from the ideal-power
factorization preceding (7b).

If `J ^ 67 = (a)`, relative ideal norm and `67 ∤ h⁺` produce a real
generator `ρ` and real unit `ε`; the quadratic norm identity above then
gives the exact cyclotomic-ring equation

`a * conj(a) = ε * ρ ^ 67`.

This is the complete class-number step of (7b)--(7d). -/
theorem exists_equationSevenD_of_idealPower67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hpow : J ^ 67 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      Ideal.relNorm (𝓞 K⁺) J = Ideal.span {ρ} ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap (𝓞 K⁺) (𝓞 K) ρ) =
        algebraMap (𝓞 K⁺) (𝓞 K) ρ ∧
      a * NumberField.IsCMField.ringOfIntegersComplexConj K a =
        algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
          algebraMap (𝓞 K⁺) (𝓞 K) ρ ^ 67 := by
  obtain ⟨ρ, ε, hI, ha⟩ :=
    exists_realGenerator_of_relativeNorm67 hzeta J a hpow
  refine ⟨ρ, ε, hI,
    (NumberField.IsCMField.ringOfIntegersComplexConj K).commutes ρ, ?_⟩
  rw [← algebraMap_intNorm_eq_mul_conj67]
  simpa only [map_mul, map_pow] using
    congrArg (algebraMap (𝓞 K⁺) (𝓞 K)) ha

set_option maxRecDepth 2000 in
omit [IsCyclotomicExtension {67} ℚ K] in
/-- The class-group Bézout step between equations (7a), (7d), and (8) at
exponent `67`.  Principality of `I * J^66` and `I * J` gives principality
of `J^65`; the coprime powers `65` and `67` then principalize `J`, and
division principalizes `I`. -/
theorem fractionalIdeal_isPrincipal_of_vandiverSeven67
    {A L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    {I J : FractionalIdeal A⁰ L} (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hJ67 : Submodule.IsPrincipal
      ((J ^ 67 : FractionalIdeal A⁰ L) : Submodule A L))
    (hsevenA : Submodule.IsPrincipal
      ((I * J ^ 66 : FractionalIdeal A⁰ L) : Submodule A L))
    (hsevenD : Submodule.IsPrincipal
      ((I * J : FractionalIdeal A⁰ L) : Submodule A L)) :
    Submodule.IsPrincipal (I : Submodule A L) := by
  have hJ57 : Submodule.IsPrincipal
      ((J ^ 65 : FractionalIdeal A⁰ L) : Submodule A L) := by
    have hquot := fractionalIdeal_isPrincipal_div hsevenA hsevenD
    have heq : (I * J ^ 66) / (I * J) = J ^ 65 := by
      apply (div_eq_iff (mul_ne_zero hI0 hJ0)).mpr
      rw [show J ^ 66 = J ^ 65 * J by rw [← pow_succ]]
      ac_rfl
    rw [← heq]
    exact hquot
  have hJ : Submodule.IsPrincipal (J : Submodule A L) :=
    fractionalIdeal_isPrincipal_of_coprime_powers (by norm_num) J hJ57 hJ67
  have hquot := fractionalIdeal_isPrincipal_div hsevenD hJ
  have heq : (I * J) / J = I := by
    apply (div_eq_iff hJ0).mpr
    rfl
  rw [heq] at hquot
  exact hquot

set_option maxRecDepth 2000 in
omit [IsCyclotomicExtension {67} ℚ K] in
/-- Vandiver's passage from the two principal products in (7a) and (7d)
to equation (8).

The ideal equalities are stated literally.  If `I = 𝔦ₐ` and
`J = 𝔦₋ₐ`, then (7a) says `I * J^66` is principal, while (7d)
says `I * J` is principal.  Their quotient makes `J^65` principal.  Since
`J^67` is principal as well, the checked Bézout lemma
`fractionalIdeal_isPrincipal_of_vandiverSeven67` principalizes `I`.
Finally `I^67 = (a)` gives the element equation
`a = η * ρ^67`, which is exactly (8). -/
theorem exists_equationEight_of_sevenASevenD67
    (I J : Ideal (𝓞 K)) (a b r s : 𝓞 K)
    (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hIpow : I ^ 67 = Ideal.span {a})
    (hJpow : J ^ 67 = Ideal.span {b})
    (hsevenA : I * J ^ 66 = Ideal.span {r})
    (hsevenD : I * J = Ideal.span {s}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      I = Ideal.span {ρ} ∧ a = η * ρ ^ 67 := by
  let IF : FractionalIdeal (𝓞 K)⁰ K := I
  let JF : FractionalIdeal (𝓞 K)⁰ K := J
  have hIF0 : IF ≠ 0 := by
    dsimp [IF]
    intro h
    rw [FractionalIdeal.coeIdeal_eq_zero] at h
    exact hI0 h
  have hJF0 : JF ≠ 0 := by
    dsimp [JF]
    intro h
    rw [FractionalIdeal.coeIdeal_eq_zero] at h
    exact hJ0 h
  have hJ67 : Submodule.IsPrincipal
      ((JF ^ 67 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.isPrincipal_iff]
    refine ⟨(b : K), ?_⟩
    dsimp [JF]
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← hJpow,
      FractionalIdeal.coeIdeal_pow]
  have h7a : Submodule.IsPrincipal
      ((IF * JF ^ 66 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.isPrincipal_iff]
    refine ⟨(r : K), ?_⟩
    dsimp [IF, JF]
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← hsevenA,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  have h7d : Submodule.IsPrincipal
      ((IF * JF : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.isPrincipal_iff]
    refine ⟨(s : K), ?_⟩
    dsimp [IF, JF]
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← hsevenD,
      FractionalIdeal.coeIdeal_mul]
  have hIF : Submodule.IsPrincipal (IF : Submodule (𝓞 K) K) :=
    fractionalIdeal_isPrincipal_of_vandiverSeven67 hIF0 hJF0 hJ67 h7a h7d
  have hIF' : Submodule.IsPrincipal
      ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    simpa only [IF] using hIF
  have hI : Submodule.IsPrincipal (I : Ideal (𝓞 K)) :=
    (IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K).mp hIF'
  exact exists_unit_mul_pow_eq_of_isPrincipal_ideal I a hI hIpow

set_option maxRecDepth 2000 in
/-- Source-faithful assembly of Vandiver's Lemma 1, equations (7a) and
(7d), and equation (8).

The primary element in Lemma 1 is exactly `a * b^66`: its principal ideal
is the 67th power of `I * J^66`.  `exists_equationSevenA_generator` turns
the narrow Takagi/Furtwängler boundary into the displayed ideal identity
(7a); the already kernel-checked Bézout calculation with (7d) then produces
the generator in (8).

Thus callers no longer need to assume equation (7a) itself.  They need only
prove the concrete primary congruence and supply the named historical
Lemma-1 theorem. -/
theorem exists_equationEight_of_lemmaOneSevenD67
    (hlemma : Fermat.Irregular.VandiverLemmaOne.LemmaOne K 67)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (I J : Ideal (𝓞 K)) (a b s : 𝓞 K)
    (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hIpow : I ^ 67 = Ideal.span {a})
    (hJpow : J ^ 67 = Ideal.span {b})
    (hprimary :
      Fermat.Irregular.VandiverLemmaOne.IsKummerPrimary hζ (a * b ^ 66))
    (hsevenD : I * J = Ideal.span {s}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      I = Ideal.span {ρ} ∧ a = η * ρ ^ 67 := by
  obtain ⟨r, hsevenA⟩ :=
    Fermat.Irregular.VandiverLemmaOne.exists_equationSevenA_generator
      hlemma hζ I J a b hIpow hJpow (by simpa using hprimary)
  exact exists_equationEight_of_sevenASevenD67
    I J a b r s hI0 hJ0 hIpow hJpow hsevenA hsevenD

set_option maxRecDepth 2000 in
/-- Unit-normalized assembly of Vandiver's equations (7a), (7d), and (8).

In the literal historical factors, replacing the fixed denominator
`ζ - 1` by `ζ^a - 1` introduces a cyclotomic unit.  The primary generator
is therefore naturally `u * (a * b^66)`.  Since `u` does not change the
principal ideal, Lemma 1 still principalizes `I * J^66`; the rest is the
same checked Bézout calculation as in
`exists_equationEight_of_lemmaOneSevenD67`. -/
theorem exists_equationEight_of_lemmaOneSevenDUnit67
    (hlemma : Fermat.Irregular.VandiverLemmaOne.LemmaOne K 67)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (u : (𝓞 K)ˣ) (I J : Ideal (𝓞 K)) (a b s : 𝓞 K)
    (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hIpow : I ^ 67 = Ideal.span {a})
    (hJpow : J ^ 67 = Ideal.span {b})
    (hprimary :
      Fermat.Irregular.VandiverLemmaOne.IsKummerPrimary hζ
        ((u : 𝓞 K) * (a * b ^ 66)))
    (hsevenD : I * J = Ideal.span {s}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      I = Ideal.span {ρ} ∧ a = η * ρ ^ 67 := by
  obtain ⟨r, hsevenA⟩ :=
    Fermat.Irregular.VandiverLemmaOne.exists_equationSevenA_generator_of_unit
      hlemma hζ u I J a b hIpow hJpow (by simpa using hprimary)
  exact exists_equationEight_of_sevenASevenD67
    I J a b r s hI0 hJ0 hIpow hJpow hsevenA hsevenD

set_option maxRecDepth 3000 in
/-- Vandiver's equation (7d) for the literal historical factor pair.

The plus-class calculation applied to the ideal at `ζ` gives

`q₊ * conj(q₊) = ε * ρ^67`.

The conjugation theorem above identifies `conj(q₊)` with the normalized
inverse factor `q₋`.  Comparing 67th powers of integral ideals and using
injectivity of the power map then proves that the product of the two
allocated factor ideals is `(ρ)`. -/
theorem exists_historicalEquationSevenD67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ r : 𝓞 K,
      historicalZetaFactorIdeal67 hζ s *
          historicalInverseZetaFactorIdeal67 hζ s =
        Ideal.span {r} := by
  let I : Ideal (𝓞 K) := historicalZetaFactorIdeal67 hζ s
  let J : Ideal (𝓞 K) := historicalInverseZetaFactorIdeal67 hζ s
  let a : 𝓞 K := historicalZetaFactor67 hζ s
  let b : 𝓞 K := normalizedHistoricalInverseZetaFactor67 hζ s
  have hIpow : I ^ 67 = Ideal.span {a} := by
    simpa only [I, a] using historicalZetaFactorIdeal_pow67 hζ s
  have hJpow : J ^ 67 = Ideal.span {b} := by
    simpa only [J, b] using historicalInverseZetaFactorIdeal_pow67 hζ s
  have hbconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K a = b := by
    simpa only [a, b] using
      ringOfIntegersComplexConj_historicalZetaFactor67 hζ s hs
  obtain ⟨ρ, ε, -, -, hnorm⟩ :=
    exists_equationSevenD_of_idealPower67 hζ I a hIpow
  let ρK : 𝓞 K := algebraMap (𝓞 K⁺) (𝓞 K) ρ
  let εK : (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom ε
  have hnorm' : a * b = (εK : 𝓞 K) * ρK ^ 67 := by
    rw [← hbconj]
    simpa only [ρK, εK, Units.coe_map] using hnorm
  have hpow : (I * J) ^ 67 = (Ideal.span {ρK}) ^ 67 := by
    calc
      (I * J) ^ 67 = I ^ 67 * J ^ 67 := by rw [mul_pow]
      _ = Ideal.span {a} * Ideal.span {b} := by rw [hIpow, hJpow]
      _ = Ideal.span {a * b} :=
        Ideal.span_singleton_mul_span_singleton a b
      _ = Ideal.span {(εK : 𝓞 K) * ρK ^ 67} := by rw [hnorm']
      _ = Ideal.span {ρK ^ 67} :=
        Ideal.span_singleton_eq_span_singleton.mpr
          (associated_unit_mul_left _ _ εK.isUnit)
      _ = (Ideal.span {ρK}) ^ 67 :=
        (Ideal.span_singleton_pow ρK 67).symm
  exact ⟨ρK,
    pow_left_injective (M := Ideal (𝓞 K))
      (by norm_num : 67 ≠ 0) hpow⟩

/-- The two allocated historical factor ideals are nonzero.  This follows
from the already-proved primeness of their normalized product to
`ζ - 1`, rather than from any class-number input. -/
theorem historicalFactorIdeals_ne_zero67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    historicalZetaFactorIdeal67 hζ s ≠ 0 ∧
      historicalInverseZetaFactorIdeal67 hζ s ≠ 0 := by
  let a : 𝓞 K := historicalZetaFactor67 hζ s
  let b : 𝓞 K := normalizedHistoricalInverseZetaFactor67 hζ s
  have hprimary :=
    historicalConjugateFactorProduct_isKummerPrimary67 hζ s hs
  have hab0 : a * b ^ 66 ≠ 0 := by
    intro hzero
    apply hprimary.1
    change (hζ.unit' : 𝓞 K) - 1 ∣ a * b ^ 66
    rw [hzero]
    exact dvd_zero _
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
  have hbpow0 : b ^ 66 ≠ 0 := right_ne_zero_of_mul hab0
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hbpow0
    rw [hzero]
    norm_num
  have hspanA : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    simpa only [ne_eq, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot] using ha0
  have hspanB : Ideal.span {b} ≠ (0 : Ideal (𝓞 K)) := by
    simpa only [ne_eq, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot] using hb0
  constructor
  · intro hzero
    apply hspanA
    rw [← historicalZetaFactorIdeal_pow67 hζ s, hzero]
    norm_num
  · intro hzero
    apply hspanB
    rw [← historicalInverseZetaFactorIdeal_pow67 hζ s, hzero]
    norm_num

set_option maxRecDepth 3000 in
/-- Vandiver's equation (8), constructed from an arbitrary real historical
state at exponent `67`.

All local factor allocation, high ramified divisibility, the primary
congruence, equation (7d), and the Bézout ideal calculation are proved in
the repository.  The sole premise is the exact global Takagi/Furtwängler
statement named `LemmaOne`. -/
theorem exists_historicalEquationEight67
    (hlemma : LemmaOne K 67)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      historicalZetaFactorIdeal67 hζ s = Ideal.span {ρ} ∧
      historicalZetaFactor67 hζ s = η * ρ ^ 67 := by
  obtain ⟨r, hsevenA⟩ :=
    exists_historicalEquationSevenA67 hlemma hζ s hs
  obtain ⟨t, hsevenD⟩ := exists_historicalEquationSevenD67 hζ s hs
  obtain ⟨hI0, hJ0⟩ := historicalFactorIdeals_ne_zero67 hζ s hs
  exact exists_equationEight_of_sevenASevenD67
    (historicalZetaFactorIdeal67 hζ s)
    (historicalInverseZetaFactorIdeal67 hζ s)
    (historicalZetaFactor67 hζ s)
    (normalizedHistoricalInverseZetaFactor67 hζ s)
    r t hI0 hJ0
    (historicalZetaFactorIdeal_pow67 hζ s)
    (historicalInverseZetaFactorIdeal_pow67 hζ s)
    hsevenA hsevenD

set_option maxRecDepth 3000 in
/-- The unit in the literal historical equation (8) is real.

The factor at `ζ` agrees with its conjugate modulo `(ζ - 1)^67`, and so
does every 67th power.  After cancelling the generator, which is prime to
`ζ - 1`, the unit's conjugation defect is divisible by `(ζ - 1)^2`.
`unit_fixed_of_zeta_sub_one_sq_dvd_sub_conj67` then removes its possible
cyclotomic torsion component.  This is the compatibility needed to obtain
equation (8) at `a` and `-a` with one common unit. -/
theorem historicalEquationEight_unit_real67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) (ρ : 𝓞 K) (η : (𝓞 K)ˣ)
    (heq : historicalZetaFactor67 hζ s = η * ρ ^ 67) :
    NumberField.IsCMField.unitsComplexConj K η = η := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hqnot : ¬ π ∣ historicalZetaFactor67 hζ s := by
    simpa only [π] using historicalZetaFactor_not_ramified67 hζ s hs
  have hρnot : ¬ π ∣ ρ := by
    intro hρ
    apply hqnot
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_pow (n := 67) hρ (by norm_num)) _
  have hρpowNot : ¬ π ∣ ρ ^ 67 := by
    intro h
    exact hρnot ((hζ.zeta_sub_one_prime'.dvd_pow_iff_dvd
      (by norm_num : 67 ≠ 0)).mp h)
  have hq67 := historicalZetaFactor_sub_conj_highDivisibility67 hζ s hs
  have hq2 : π ^ 2 ∣
      historicalZetaFactor67 hζ s -
        NumberField.IsCMField.ringOfIntegersComplexConj K
          (historicalZetaFactor67 hζ s) := by
    exact (pow_dvd_pow_of_dvd_of_le (dvd_refl π) (by norm_num : 2 ≤ 67)).trans
      (by simpa only [π] using hq67)
  have hρ67 :=
    zeta_sub_one_pow_sixtySeven_dvd_pow_sub_conj_pow67 hζ ρ
  have hρ2 : π ^ 2 ∣
      ρ ^ 67 -
        NumberField.IsCMField.ringOfIntegersComplexConj K ρ ^ 67 := by
    exact (pow_dvd_pow_of_dvd_of_le (dvd_refl π) (by norm_num : 2 ≤ 67)).trans
      (by simpa only [π] using hρ67)
  have herror : π ^ 2 ∣
      NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) *
        (ρ ^ 67 -
          NumberField.IsCMField.ringOfIntegersComplexConj K ρ ^ 67) :=
    dvd_mul_of_dvd_right hρ2 _
  have hmul : π ^ 2 ∣
      ((η : 𝓞 K) -
        NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K)) *
          ρ ^ 67 := by
    have h := dvd_sub hq2 herror
    convert h using 1
    rw [heq]
    simp only [map_mul, map_pow]
    ring
  have hunit : π ^ 2 ∣
      (η : 𝓞 K) -
        NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) := by
    let d : 𝓞 K := (η : 𝓞 K) -
      NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K)
    have hπ0 : π ≠ 0 := hζ.unit'_coe.sub_one_ne_zero (by norm_num)
    have hπmul : π ∣ d * ρ ^ 67 :=
      (dvd_pow_self π (by norm_num : 2 ≠ 0)).trans
        (by simpa only [d] using hmul)
    have hd : π ∣ d := by
      rcases hζ.zeta_sub_one_prime'.dvd_mul.mp hπmul with hd | hρ
      · exact hd
      · exact False.elim (hρpowNot hρ)
    obtain ⟨d₁, hd₁⟩ := hd
    obtain ⟨c, hc⟩ := hmul
    have hcancel : d₁ * ρ ^ 67 = π * c := by
      apply mul_left_cancel₀ hπ0
      calc
        π * (d₁ * ρ ^ 67) = d * ρ ^ 67 := by rw [hd₁]; ring
        _ = π ^ 2 * c := hc
        _ = π * (π * c) := by ring
    have hd₁div : π ∣ d₁ := by
      have hπd₁ : π ∣ d₁ * ρ ^ 67 := ⟨c, hcancel⟩
      rcases hζ.zeta_sub_one_prime'.dvd_mul.mp hπd₁ with hd₁ | hρ
      · exact hd₁
      · exact False.elim (hρpowNot hρ)
    obtain ⟨d₂, hd₂⟩ := hd₁div
    refine ⟨d₂, ?_⟩
    change d = π ^ 2 * d₂
    rw [hd₁, hd₂]
    ring
  exact unit_fixed_of_zeta_sub_one_sq_dvd_sub_conj67 hζ η
    (by simpa only [π] using hunit)

set_option maxRecDepth 3000 in
/-- Strengthened equation (8): the chosen coefficient unit is fixed by
complex conjugation.  Consequently its conjugate equation uses exactly
the same unit, as in Vandiver's displayed formulas for `a` and `-a`. -/
theorem exists_historicalEquationEight_realUnit67
    (hlemma : LemmaOne K 67)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      historicalZetaFactorIdeal67 hζ s = Ideal.span {ρ} ∧
      historicalZetaFactor67 hζ s = η * ρ ^ 67 ∧
      NumberField.IsCMField.unitsComplexConj K η = η := by
  obtain ⟨ρ, η, hI, heq⟩ :=
    exists_historicalEquationEight67 hlemma hζ s hs
  exact ⟨ρ, η, hI, heq,
    historicalEquationEight_unit_real67 hζ s hs ρ η heq⟩

set_option maxRecDepth 3000 in
/-- Vandiver's paired equation (8) at `a = 1` and `a = -1`, with one
common real unit and with both generators prime to `ζ - 1`.

Starting from the normalized factor divided by `ζ - 1` changes the
coefficient to `-η` when it is rewritten with denominator `1 - ζ`.
Because `η` is real, conjugation gives the inverse-root equation with
exactly the same `-η`. -/
theorem exists_historicalEquationEight_pair_one67
    (hlemma : LemmaOne K 67)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρone ρminus : 𝓞 K) (η : (𝓞 K)ˣ),
      NumberField.IsCMField.unitsComplexConj K η = η ∧
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * η * ρone ^ 67 ∧
      s.omega + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * η * ρminus ^ 67 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K ρone = ρminus ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρone ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρminus := by
  obtain ⟨ρ, η₀, -, heq, hη₀real⟩ :=
    exists_historicalEquationEight_realUnit67 hlemma hζ s hs
  let η : (𝓞 K)ˣ := -η₀
  let ρminus : 𝓞 K :=
    NumberField.IsCMField.ringOfIntegersComplexConj K ρ
  have hηreal : NumberField.IsCMField.unitsComplexConj K η = η := by
    apply Units.ext
    change NumberField.IsCMField.ringOfIntegersComplexConj K
      (-(η₀ : 𝓞 K)) = -(η₀ : 𝓞 K)
    rw [map_neg]
    exact congrArg Neg.neg (congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hη₀real)
  have hqmul : historicalZetaFactor67 hζ s *
      ((hζ.unit' : 𝓞 K) - 1) =
        s.omega + s.theta * (hζ.unit' : 𝓞 K) :=
    div_zeta_sub_one_mul_zeta_sub_one
      (by norm_num : 67 ≠ 2) hζ
      (historicalState_regularEquation67 hζ s)
      (zetaNthRoot (K := K) (p := 67) hζ)
  have hone :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * η * ρ ^ 67 := by
    calc
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
          s.omega + s.theta * (hζ.unit' : 𝓞 K) := by ring
      _ = historicalZetaFactor67 hζ s *
          ((hζ.unit' : 𝓞 K) - 1) := hqmul.symm
      _ = ((η₀ : 𝓞 K) * ρ ^ 67) *
          ((hζ.unit' : 𝓞 K) - 1) := by rw [heq]
      _ = (1 - (hζ.unit' : 𝓞 K)) * η * ρ ^ 67 := by
        dsimp [η]
        ring
  have hconjζ :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) (unitsComplexConj_zeta67 hζ)
  have hηreal' :
      NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) = η :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hηreal
  have hminus :
      s.omega + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * η * ρminus ^ 67 := by
    have hc := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hone
    simp only [map_add, map_mul, map_sub, map_one, map_pow,
      hs.1, hs.2.1, hconjζ, hηreal'] at hc
    simpa only [ρminus] using hc
  have hρnot : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρ := by
    intro hρ
    apply historicalZetaFactor_not_ramified67 hζ s hs
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_pow (n := 67) hρ (by norm_num)) _
  have hρminusNot : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρminus := by
    intro hρminus
    have hc := zeta_sub_one_pow_dvd_conj_of_dvd67 hζ 1 ρminus
      (by simpa only [pow_one] using hρminus)
    have hcc :
        NumberField.IsCMField.ringOfIntegersComplexConj K ρminus = ρ := by
      dsimp [ρminus]
      apply NumberField.RingOfIntegers.ext
      exact NumberField.IsCMField.complexConj_apply_apply K ρ
    apply hρnot
    simpa only [pow_one, hcc] using hc
  exact ⟨ρ, ρminus, η, hηreal, hone, hminus, rfl, hρnot, hρminusNot⟩

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- The elementary elimination between equation (8) at `a` and `-a`.

For a unit `t`, subtracting the two displayed equations and using
`t * t⁻¹ = 1` gives

`(1-t)η(ρₐ^67-ρ₋ₐ^67) = (1+t)(ω+θ)`.

This is the algebraic identity immediately preceding Vandiver's
factorization in equation (9). -/
lemma equationEight_pair_difference67
    (t eta : (𝓞 K)ˣ) (omega theta rhoa rhominus : 𝓞 K)
    (ha : omega + (t : 𝓞 K) * theta =
      (1 - (t : 𝓞 K)) * eta * rhoa ^ 67)
    (hminus : omega + (t⁻¹ : (𝓞 K)ˣ) * theta =
      (1 - (t⁻¹ : (𝓞 K)ˣ)) * eta * rhominus ^ 67) :
    (1 - (t : 𝓞 K)) * eta * (rhoa ^ 67 - rhominus ^ 67) =
      (1 + (t : 𝓞 K)) * (omega + theta) := by
  have htinv : (t : 𝓞 K) * (t⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  have hcoef : (1 - (t : 𝓞 K)) =
      -(t : 𝓞 K) * (1 - (t⁻¹ : (𝓞 K)ˣ)) := by
    linear_combination -htinv
  have hfirst : (1 - (t : 𝓞 K)) * eta * rhoa ^ 67 =
      omega + (t : 𝓞 K) * theta := ha.symm
  have hsecond : (1 - (t : 𝓞 K)) * eta * rhominus ^ 67 =
      -((t : 𝓞 K) * omega + theta) := by
    rw [hcoef]
    calc
      (-(t : 𝓞 K) * (1 - (t⁻¹ : (𝓞 K)ˣ))) * eta * rhominus ^ 67 =
          -(t : 𝓞 K) *
            ((1 - (t⁻¹ : (𝓞 K)ˣ)) * eta * rhominus ^ 67) := by ring
      _ = -(t : 𝓞 K) *
            (omega + (t⁻¹ : (𝓞 K)ˣ) * theta) := by rw [hminus]
      _ = -((t : 𝓞 K) * omega + theta) := by
        linear_combination -theta * htinv
  rw [mul_sub, hfirst, hsecond]
  ring

omit [IsCyclotomicExtension {67} ℚ K] in
/-- Equations (8) at `a,-a`, together with (8a), give the exact difference
equation used before (9):

`ρₐ^67 - ρ₋ₐ^67 = ε * (((ζ-1)^(2*m-1) * ρ₀)^67)`.

The proof makes every unit explicit.  It uses that `1 + ζ^a` is a
cyclotomic unit, that `1 - ζ^a` is associated to `ζ - 1`, and the checked
identity `κ = (-ζ⁻¹)(ζ-1)²`.  The exponent calculation is

`2 * (67*m - 33) - 1 = (2*m - 1) * 67`.

No ideal-class hypothesis occurs here. -/
theorem exists_equationEight_difference67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (a m : ℕ) (ha : a.Coprime 67) (hm : 1 < m)
    (omega theta rhoa rhominus rhozero : 𝓞 K)
    (etaa etazero : (𝓞 K)ˣ)
    (hea : omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * theta =
      (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) * etaa * rhoa ^ 67)
    (heminus : omega + ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ) * theta =
      (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) * etaa * rhominus ^ 67)
    (hezero : omega + theta =
      etazero * kappa hζ ^ (67 * m - 33) * rhozero ^ 67) :
    ∃ ε : (𝓞 K)ˣ,
      rhoa ^ 67 - rhominus ^ 67 =
        ε * (((hζ.unit' : 𝓞 K) - 1) ^ (2 * m - 1) * rhozero) ^ 67 := by
  let t : (𝓞 K)ˣ := hζ.unit' ^ a
  have htprim : IsPrimitiveRoot (t : 𝓞 K) 67 :=
    hζ.unit'_coe.pow_of_coprime a ha
  let hplus : IsUnit ((1 : 𝓞 K) + t) := by
    simpa [add_comm] using
      htprim.geom_sum_isUnit (by norm_num) (by norm_num : Nat.Coprime 2 67)
  let uplus : (𝓞 K)ˣ := hplus.unit
  have huplus : (uplus : 𝓞 K) = 1 + (t : 𝓞 K) := by
    exact hplus.unit_spec
  obtain ⟨u, hu⟩ :=
    hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime ha
  let uden : (𝓞 K)ˣ := -u
  have huden : (1 : 𝓞 K) - (t : 𝓞 K) =
      (uden : 𝓞 K) * ((hζ.unit' : 𝓞 K) - 1) := by
    dsimp [t, uden]
    calc
      (1 : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ a =
          -((hζ.unit' : 𝓞 K) ^ a - 1) := by ring
      _ = -(((hζ.unit' : 𝓞 K) - 1) * (u : 𝓞 K)) := by rw [hu]
      _ = (-(u : 𝓞 K)) * ((hζ.unit' : 𝓞 K) - 1) := by ring
  have helim := equationEight_pair_difference67 t etaa omega theta rhoa rhominus
    (by simpa only [t] using hea) (by simpa only [t] using heminus)
  let E : ℕ := 67 * m - 33
  let N : ℕ := (2 * m - 1) * 67
  have hexp : 2 * E = N + 1 := by
    dsimp [E, N]
    omega
  have hkappa : kappa hζ ^ E =
      ((kappaUnit67 hζ ^ E : (𝓞 K)ˣ) : 𝓞 K) *
        ((hζ.unit' : 𝓞 K) - 1) ^ (N + 1) := by
    rw [kappa_pow_eq_kappaUnit67_pow_mul, hexp]
  have hkappa' : kappa hζ ^ E =
      ((kappaUnit67 hζ ^ E : (𝓞 K)ˣ) : 𝓞 K) *
        ((hζ.unit' : 𝓞 K) - 1) *
          ((hζ.unit' : 𝓞 K) - 1) ^ N := by
    rw [hkappa, pow_succ']
    ring
  let leftUnit : (𝓞 K)ˣ := uden * etaa
  let rightUnit : (𝓞 K)ˣ := uplus * etazero * kappaUnit67 hζ ^ E
  have hpi : (hζ.unit' : 𝓞 K) - 1 ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hcancel : (leftUnit : 𝓞 K) * (rhoa ^ 67 - rhominus ^ 67) =
      (rightUnit : 𝓞 K) *
        ((hζ.unit' : 𝓞 K) - 1) ^ N * rhozero ^ 67 := by
    apply mul_left_cancel₀ hpi
    calc
      ((hζ.unit' : 𝓞 K) - 1) *
          ((leftUnit : 𝓞 K) * (rhoa ^ 67 - rhominus ^ 67)) =
          (1 - (t : 𝓞 K)) * etaa *
            (rhoa ^ 67 - rhominus ^ 67) := by
        dsimp [leftUnit]
        rw [huden]
        ring
      _ = (1 + (t : 𝓞 K)) * (omega + theta) := helim
      _ = ((hζ.unit' : 𝓞 K) - 1) *
          ((rightUnit : 𝓞 K) *
            ((hζ.unit' : 𝓞 K) - 1) ^ N * rhozero ^ 67) := by
        have hezero' : omega + theta =
            etazero * kappa hζ ^ E * rhozero ^ 67 := by
          simpa only [E] using hezero
        rw [← huplus, hezero', hkappa']
        dsimp [rightUnit]
        ring
  let ε : (𝓞 K)ˣ := leftUnit⁻¹ * rightUnit
  refine ⟨ε, ?_⟩
  have hdiff : rhoa ^ 67 - rhominus ^ 67 =
      (ε : 𝓞 K) * ((hζ.unit' : 𝓞 K) - 1) ^ N * rhozero ^ 67 := by
    calc
      rhoa ^ 67 - rhominus ^ 67 =
          (leftUnit⁻¹ : (𝓞 K)ˣ) *
            ((leftUnit : 𝓞 K) * (rhoa ^ 67 - rhominus ^ 67)) := by
        rw [← mul_assoc, ← Units.val_mul]
        simp
      _ = (leftUnit⁻¹ : (𝓞 K)ˣ) *
          ((rightUnit : 𝓞 K) *
            ((hζ.unit' : 𝓞 K) - 1) ^ N * rhozero ^ 67) := by rw [hcancel]
      _ = (ε : 𝓞 K) * ((hζ.unit' : 𝓞 K) - 1) ^ N * rhozero ^ 67 := by
        dsimp [ε]
        ring
  rw [hdiff]
  dsimp [N]
  rw [mul_pow, ← pow_mul]
  ring

/-- The conjugate of an integral ideal under CM complex conjugation. -/
def conjugateIdeal67 (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom

/-- Extension of an ideal of the maximal real field to the full
cyclotomic ring. -/
def extendRealIdeal67 (I : Ideal (𝓞 K⁺)) : Ideal (𝓞 K) :=
  I.map (algebraMap (𝓞 K⁺) (𝓞 K))

/-- An extended real ideal is fixed by CM complex conjugation. -/
@[simp] theorem conjugateIdeal67_extendRealIdeal67
    (I : Ideal (𝓞 K⁺)) :
    conjugateIdeal67 (extendRealIdeal67 I) = extendRealIdeal67 I := by
  rw [conjugateIdeal67, extendRealIdeal67, Ideal.map_map]
  have hmap :
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom.comp
          (algebraMap (𝓞 K⁺) (𝓞 K)) =
        algebraMap (𝓞 K⁺) (𝓞 K) := by
    ext x
    exact congrArg ((↑) : 𝓞 K → K)
      ((NumberField.IsCMField.ringOfIntegersComplexConj K).commutes x)
  rw [hmap]

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- Extending a real principal ideal preserves its displayed generator. -/
theorem extendRealIdeal67_span (ρ : 𝓞 K⁺) :
    extendRealIdeal67 (Ideal.span {ρ}) =
      Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) ρ} := by
  simp only [extendRealIdeal67, Ideal.map_span, Set.image_singleton]

omit [IsCyclotomicExtension {67} ℚ K] in
/-- Extension from the real ring of integers is injective on ideals.  This
is faithful flatness for the finite integral extension
`𝓞 K⁺ → 𝓞 K`. -/
theorem extendRealIdeal67_injective :
    Function.Injective (extendRealIdeal67 (K := K)) := by
  intro I J hIJ
  have hcomap := congrArg
    (Ideal.comap (algebraMap (𝓞 K⁺) (𝓞 K))) hIJ
  simpa only [extendRealIdeal67,
    Ideal.comap_map_eq_self_of_faithfullyFlat] using hcomap

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- Extension commutes with ideal powers. -/
theorem extendRealIdeal67_pow (I : Ideal (𝓞 K⁺)) (n : ℕ) :
    extendRealIdeal67 (I ^ n) = extendRealIdeal67 I ^ n := by
  exact Ideal.map_pow (algebraMap (𝓞 K⁺) (𝓞 K)) I n

set_option maxRecDepth 2000 in
/-- The complete plus-class-number bridge needed at each of Vandiver's
real ideals in (7b) and (9).  A real ideal with 67th power `(a)` extends to
a conjugation-stable principal ideal of the cyclotomic ring, generated by
the image of a real integer `ρ`; the displayed element `a` is a real unit
times `ρ ^ 67`.

Thus a future construction only has to prove that its invariant ideal is
the extension of `I` and verify the 67th-power equality `hpow`; all class
number and generator extraction work is discharged here. -/
theorem exists_extendedRealGenerator67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (I : Ideal (𝓞 K⁺)) (a : 𝓞 K⁺)
    (hpow : I ^ 67 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      extendRealIdeal67 I =
          Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) ρ} ∧
      conjugateIdeal67 (extendRealIdeal67 I) = extendRealIdeal67 I ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap (𝓞 K⁺) (𝓞 K) ρ) =
        algebraMap (𝓞 K⁺) (𝓞 K) ρ ∧
      algebraMap (𝓞 K⁺) (𝓞 K) a =
        algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
          algebraMap (𝓞 K⁺) (𝓞 K) ρ ^ 67 := by
  obtain ⟨ρ, ε, hI, ha⟩ := exists_real_unit_mul_pow_generator67 hzeta I a hpow
  refine ⟨ρ, ε, ?_, conjugateIdeal67_extendRealIdeal67 I,
    (NumberField.IsCMField.ringOfIntegersComplexConj K).commutes ρ, ?_⟩
  · rw [hI, extendRealIdeal67_span]
  · rw [ha, map_mul, map_pow]

set_option maxRecDepth 2000 in
/-- Version of `exists_extendedRealGenerator67` whose 67th-power identity
is proved after extension to the cyclotomic ring, as it is in Vandiver's
factorizations (7b) and (9).  Faithful flatness reflects that identity back
to the real ideal, where `67 ∤ h⁺` supplies the generator. -/
theorem exists_extendedRealGenerator67_of_pow_eq_span
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (I : Ideal (𝓞 K⁺)) (a : 𝓞 K⁺)
    (hpow : extendRealIdeal67 I ^ 67 =
      Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      extendRealIdeal67 I =
          Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) ρ} ∧
      conjugateIdeal67 (extendRealIdeal67 I) = extendRealIdeal67 I ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap (𝓞 K⁺) (𝓞 K) ρ) =
        algebraMap (𝓞 K⁺) (𝓞 K) ρ ∧
      algebraMap (𝓞 K⁺) (𝓞 K) a =
        algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
          algebraMap (𝓞 K⁺) (𝓞 K) ρ ^ 67 := by
  apply exists_extendedRealGenerator67 hzeta I a
  apply extendRealIdeal67_injective (K := K)
  rw [extendRealIdeal67_pow, extendRealIdeal67_span]
  exact hpow

/-- Complex conjugation preserves whether an integral ideal is zero. -/
@[simp] lemma conjugateIdeal67_eq_zero_iff (I : Ideal (𝓞 K)) :
    conjugateIdeal67 I = 0 ↔ I = 0 := by
  exact Ideal.map_eq_bot_iff_of_injective
    (NumberField.IsCMField.ringOfIntegersComplexConj K).injective

/-- Conjugate an integral-ideal quotient by conjugating numerator and
denominator. -/
def conjugateIdealQuotient67 (A B : Ideal (𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (conjugateIdeal67 A : FractionalIdeal (𝓞 K)⁰ K) /
    (conjugateIdeal67 B : FractionalIdeal (𝓞 K)⁰ K)

/-- The actual fractional ideal whose principality is requested by
`RelevantIdealQuotientsPrincipal` at exponent `67`. -/
noncomputable def relevantIdealQuotient67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 67 + y ^ 67 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 67)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 67 (1 : 𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (root_div_zeta_sub_one_dvd_gcd (K := K) (p := 67)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy η : FractionalIdeal (𝓞 K)⁰ K) /
    (a_eta_zero_dvd_p_pow (K := K) (p := 67)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy : FractionalIdeal (𝓞 K)⁰ K)

/-- The conjugate of the relevant exponent-`67` quotient. -/
noncomputable def conjugateRelevantIdealQuotient67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 67 + y ^ 67 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 67)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 67 (1 : 𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K :=
  conjugateIdealQuotient67
    (root_div_zeta_sub_one_dvd_gcd (K := K) (p := 67)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy η)
    (a_eta_zero_dvd_p_pow (K := K) (p := 67)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy)

/-- Every symmetric relevant quotient class is principal.  This is the
ideal-theoretic plus-component statement to be supplied by the plus class
number through relative ideal norm and extension. -/
def RelevantIdealQuotientPlusComponentsPrincipal67 : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 67 + y ^ 67 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 67)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 67 (1 : 𝓞 K)),
    Submodule.IsPrincipal
      (((relevantIdealQuotient67 hζ e hy η *
          conjugateRelevantIdealQuotient67 hζ e hy η) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

/-- Every antisymmetric relevant quotient class is principal.  At `67`,
this is exactly the residual minus-component assertion that cannot follow
from `67 ∤ h⁺` alone. -/
def RelevantIdealQuotientMinusComponentsPrincipal67 : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 67 + y ^ 67 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 67)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 67 (1 : 𝓞 K)),
    Submodule.IsPrincipal
      (((relevantIdealQuotient67 hζ e hy η /
          conjugateRelevantIdealQuotient67 hζ e hy η) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

section RelevantIdealMinusComponent

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
  {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
  (e : x ^ 67 + y ^ 67 =
    ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 67)
  (hy : ¬ hζ.unit'.1 - 1 ∣ y)

local notation "𝔞" =>
  root_div_zeta_sub_one_dvd_gcd (K := K) (p := 67)
    (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
      (by norm_num) hζ e hy
local notation "𝔞₀" =>
  a_eta_zero_dvd_p_pow (K := K) (p := 67)
    (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
      (by norm_num) hζ e hy

/-- A relevant quotient is zero exactly when its conjugate is zero. -/
lemma relevantIdealQuotient67_conjugate_eq_zero_iff
    (η : Polynomial.nthRootsFinset 67 (1 : 𝓞 K)) :
    ((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) = 0) ↔
      conjugateIdealQuotient67 (𝔞 η) 𝔞₀ = 0 := by
  simp only [conjugateIdealQuotient67, div_eq_mul_inv,
    mul_eq_zero, inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero]
  constructor <;> rintro (h | h)
  · exact Or.inl ((conjugateIdeal67_eq_zero_iff _).mpr h)
  · exact Or.inr ((conjugateIdeal67_eq_zero_iff _).mpr h)
  · exact Or.inl ((conjugateIdeal67_eq_zero_iff _).mp h)
  · exact Or.inr ((conjugateIdeal67_eq_zero_iff _).mp h)

/-- After the symmetric plus component is principal, the original relevant
quotient is principal exactly when its antisymmetric minus component is.

The proof uses the unconditional fact that the quotient's `67`th power is
principal and the coprimality of `67` and `2`. -/
lemma relevantIdealQuotient67_isPrincipal_iff_minus
    (η : Polynomial.nthRootsFinset 67 (1 : 𝓞 K))
    (hplus : Submodule.IsPrincipal
      ((((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) *
          conjugateIdealQuotient67 (𝔞 η) 𝔞₀) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    Submodule.IsPrincipal
        ((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ↔
      Submodule.IsPrincipal
        (((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) /
            conjugateIdealQuotient67 (𝔞 η) 𝔞₀ :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    (𝔞 η : FractionalIdeal (𝓞 K)⁰ K) /
      (𝔞₀ : FractionalIdeal (𝓞 K)⁰ K)
  let J : FractionalIdeal (𝓞 K)⁰ K :=
    conjugateIdealQuotient67 (𝔞 η) 𝔞₀
  have hzero : I = 0 ↔ J = 0 :=
    relevantIdealQuotient67_conjugate_eq_zero_iff hζ e hy η
  change Submodule.IsPrincipal (I : Submodule (𝓞 K) K) ↔
    Submodule.IsPrincipal
      ((I / J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  by_cases hI0 : I = 0
  · have hJ0 : J = 0 := hzero.mp hI0
    rw [hI0, hJ0]
    simp only [zero_div, FractionalIdeal.coe_zero]
  · have hJ0 : J ≠ 0 := fun h ↦ hI0 (hzero.mpr h)
    apply fractionalIdeal_isPrincipal_iff_minus_of_plus (p := 67)
      (by norm_num) hI0 hJ0
    · exact relevantIdealQuotient_pow_isPrincipal
        (K := K) (p := 67) (by norm_num) hζ e hy η
    · exact hplus

end RelevantIdealMinusComponent

/-- Provided the symmetric plus components are principal, the old broad
principalization interface is equivalent—not merely implied—to eliminating
the explicit antisymmetric minus components. -/
theorem relevantIdealQuotientsPrincipal_iff_minus_of_plus67
    (hplus : RelevantIdealQuotientPlusComponentsPrincipal67 (K := K)) :
    RelevantIdealQuotientsPrincipal (K := K) (p := 67) (by norm_num) ↔
      RelevantIdealQuotientMinusComponentsPrincipal67 (K := K) := by
  constructor
  · intro hprincipal ζ hζ x y z ε₀ m e hy η
    have hI := hprincipal hζ e hy η
    have hiff := relevantIdealQuotient67_isPrincipal_iff_minus hζ e hy η
      (hplus hζ e hy η)
    simpa only [relevantIdealQuotient67,
      conjugateRelevantIdealQuotient67] using hiff.mp hI
  · intro hminus ζ hζ x y z ε₀ m e hy η
    have hiff := relevantIdealQuotient67_isPrincipal_iff_minus hζ e hy η
      (hplus hζ e hy η)
    apply hiff.mpr
    simpa only [relevantIdealQuotient67,
      conjugateRelevantIdealQuotient67] using hminus hζ e hy η

/-! ### Stable principal ideals have cyclotomic conjugation quotients -/

section StablePrincipalGenerator

open NumberField NumberField.IsCMField

/-- Complex conjugation acts trivially modulo the prime `(ζ - 1)` on every
cyclotomic integer.  The proof compares the power-basis expansions at `ζ`
and `ζ⁻¹`; both roots reduce to `1`. -/
lemma ringOfIntegersComplexConj_eq_mod_zeta_sub_one67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K) :
    Ideal.Quotient.mk
        (Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)))
        (ringOfIntegersComplexConj K a) =
      Ideal.Quotient.mk
        (Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K))) a := by
  have ha := hζ.integralPowerBasis.basis.sum_repr a
  let c := hζ.integralPowerBasis.basis.repr
  let φn := hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow,
    IsPrimitiveRoot.integralPowerBasis_gen] at ha
  have ha' := congrArg (ringOfIntegersComplexConj K) ha
  replace ha' : ∑ x : Fin φn, (c a) x • ringOfIntegersComplexConj K
      (⟨ζ, hζ.isIntegral (by norm_num)⟩ ^ (x : ℕ)) =
        ringOfIntegersComplexConj K a := by
    refine Eq.trans ?_ ha'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have hpow : ∀ x : Fin φn,
      ringOfIntegersComplexConj K
          (⟨ζ, hζ.isIntegral (by norm_num)⟩ ^ (x : ℕ)) =
        ⟨ζ⁻¹, hζ.inv.isIntegral (by norm_num)⟩ ^ (x : ℕ) := by
    intro x
    ext
    change complexConj K (ζ ^ (x : ℕ)) = (ζ⁻¹) ^ (x : ℕ)
    rw [map_pow,
      Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  conv_lhs at ha' =>
    congr
    congr
    ext x
    rw [hpow x]
  have hconj := aux hζ hζ.inv ha'
  have horig := aux hζ hζ ha
  exact hconj.trans horig.symm

/-- Conjugating a principal integral ideal conjugates its generator. -/
lemma conjugateIdeal67_span (a : 𝓞 K) :
    conjugateIdeal67 (Ideal.span {a}) =
      Ideal.span {ringOfIntegersComplexConj K a} := by
  simp only [conjugateIdeal67, Ideal.map_span, Set.image_singleton]
  rfl

/-- A generator prime to `(ζ - 1)` of a conjugation-stable principal ideal
has conjugation quotient exactly `ζ ^ j`.

Stability first gives an arbitrary unit quotient `v`.  Applying conjugation
twice shows `conj(v) = v⁻¹`; the CM unit theorem then gives
`v = ±ζ^j`.  Since conjugation is the identity modulo `(ζ - 1)` and the
generator is nonzero in that quotient, `v ≡ 1`; this rules out `-ζ^j`
because `2 ∉ (ζ - 1)`. -/
lemma conjugation_eq_zeta_pow_of_stable_principal67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K)
    (ha : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a)
    (hstable : conjugateIdeal67 (Ideal.span {a}) = Ideal.span {a}) :
    ∃ j : ℕ, ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a := by
  have hassoc : Associated (ringOfIntegersComplexConj K a) a := by
    rw [← Ideal.span_singleton_eq_span_singleton]
    rw [← conjugateIdeal67_span]
    exact hstable
  obtain ⟨u, hu⟩ := hassoc
  let v : (𝓞 K)ˣ := u⁻¹
  have ha0 : a ≠ 0 := by
    intro h
    apply ha
    rw [h]
    exact dvd_zero _
  have hv : ringOfIntegersComplexConj K a = (v : 𝓞 K) * a := by
    change ringOfIntegersComplexConj K a = (u⁻¹ : (𝓞 K)ˣ) * a
    calc
      ringOfIntegersComplexConj K a =
          ringOfIntegersComplexConj K a * u * (u⁻¹ : (𝓞 K)ˣ) := by simp
      _ = (u⁻¹ : (𝓞 K)ˣ) * a := by rw [hu]; ac_rfl
  have hvconj : unitsComplexConj K v = v⁻¹ := by
    have hc := congrArg (ringOfIntegersComplexConj K) hv
    rw [map_mul] at hc
    have hcc : ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K a) = a := by
      ext
      exact complexConj_apply_apply K a
    rw [hcc] at hc
    rw [hv] at hc
    have hnorm : unitsComplexConj K v * v = 1 := by
      apply Units.ext
      change ringOfIntegersComplexConj K (v : 𝓞 K) * (v : 𝓞 K) = 1
      apply mul_right_cancel₀ ha0
      calc
        (ringOfIntegersComplexConj K (v : 𝓞 K) * (v : 𝓞 K)) * a =
            ringOfIntegersComplexConj K (v : 𝓞 K) *
              ((v : 𝓞 K) * a) := by rw [mul_assoc]
        _ = a := hc.symm
        _ = (1 : 𝓞 K) * a := by simp
    exact mul_eq_one_iff_eq_inv.mp hnorm
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ v (by norm_num)
  have hv_sq : v ^ 2 = (hζ.unit' ^ j) ^ 2 := by
    simpa only [hvconj, inv_inv, pow_two] using hj
  rcases Units.eq_or_eq_neg_of_sq_eq_sq v (hζ.unit' ^ j) hv_sq with hjv | hjv
  · exact ⟨j, by simpa [hjv] using hv⟩
  · exfalso
    let P : Ideal (𝓞 K) :=
      Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K))
    let Q := 𝓞 K ⧸ P
    have hPprime : Prime P := by
      simpa only [P] using hζ.prime_span_sub_one
    have hP0 : P ≠ ⊥ := hPprime.ne_zero
    letI : P.IsPrime := (Ideal.prime_iff_isPrime hP0).mp hPprime
    have haQ : algebraMap (𝓞 K) Q a ≠ 0 := by
      change Ideal.Quotient.mk P a ≠ 0
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      simpa only [P, Ideal.mem_span_singleton] using ha
    have hvQ : algebraMap (𝓞 K) Q (v : 𝓞 K) = 1 := by
      apply mul_right_cancel₀ haQ
      calc
        algebraMap (𝓞 K) Q (v : 𝓞 K) * algebraMap (𝓞 K) Q a =
            algebraMap (𝓞 K) Q ((v : 𝓞 K) * a) := by rw [map_mul]
        _ = algebraMap (𝓞 K) Q (ringOfIntegersComplexConj K a) := by
          rw [hv]
        _ = algebraMap (𝓞 K) Q a :=
          ringOfIntegersComplexConj_eq_mod_zeta_sub_one67 hζ a
        _ = 1 * algebraMap (𝓞 K) Q a := by rw [one_mul]
    have hneg : (1 : Q) = -1 := by
      calc
        (1 : Q) = algebraMap (𝓞 K) Q (v : 𝓞 K) := hvQ.symm
        _ = algebraMap (𝓞 K) Q
            (-((hζ.unit' ^ j : (𝓞 K)ˣ) : 𝓞 K)) := by
          rw [hjv]
          rfl
        _ = -1 := by
          change -(algebraMap (𝓞 K) Q
            (((hζ.unit' : 𝓞 K) ^ j))) = -1
          rw [map_pow]
          change -(algebraMap (𝓞 K) Q (hζ.unit' : 𝓞 K)) ^ j = -1
          rw [eq_one_mod_one_sub, one_pow]
    apply hζ.two_not_mem_one_sub_zeta (by norm_num)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat,
      ← neg_one_eq_one_iff_two_eq_zero]
    exact hneg.symm

/-- Squaring removes the only obstruction to making the conjugation
quotient of a stable principal ideal a pure `67`th root of unity.

Without the hypothesis that the generator is prime to `ζ - 1`, the CM-unit
argument gives

`conj(a) = (± ζ^j) * a`.

The sign cannot in general be removed: the ramified ideal `(ζ - 1)` is the
basic counterexample.  Its square disappears, however, so the generator
`a ^ 2` always has conjugation quotient a power of `ζ`.  This is precisely
the form needed for the squared generator in Vandiver's equation (8a). -/
lemma conjugation_sq_eq_zeta_pow_of_stable_principal67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K)
    (ha0 : a ≠ 0)
    (hstable : conjugateIdeal67 (Ideal.span {a}) = Ideal.span {a}) :
    ∃ j : ℕ, ringOfIntegersComplexConj K (a ^ 2) =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a ^ 2 := by
  have hassoc : Associated (ringOfIntegersComplexConj K a) a := by
    rw [← Ideal.span_singleton_eq_span_singleton]
    rw [← conjugateIdeal67_span]
    exact hstable
  obtain ⟨u, hu⟩ := hassoc
  let v : (𝓞 K)ˣ := u⁻¹
  have hv : ringOfIntegersComplexConj K a = (v : 𝓞 K) * a := by
    change ringOfIntegersComplexConj K a = (u⁻¹ : (𝓞 K)ˣ) * a
    calc
      ringOfIntegersComplexConj K a =
          ringOfIntegersComplexConj K a * u * (u⁻¹ : (𝓞 K)ˣ) := by simp
      _ = (u⁻¹ : (𝓞 K)ˣ) * a := by rw [hu]; ac_rfl
  have hvconj : unitsComplexConj K v = v⁻¹ := by
    have hc := congrArg (ringOfIntegersComplexConj K) hv
    rw [map_mul] at hc
    have hcc : ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K a) = a := by
      ext
      exact complexConj_apply_apply K a
    rw [hcc, hv] at hc
    have hnorm : unitsComplexConj K v * v = 1 := by
      apply Units.ext
      change ringOfIntegersComplexConj K (v : 𝓞 K) * (v : 𝓞 K) = 1
      apply mul_right_cancel₀ ha0
      calc
        (ringOfIntegersComplexConj K (v : 𝓞 K) * (v : 𝓞 K)) * a =
            ringOfIntegersComplexConj K (v : 𝓞 K) *
              ((v : 𝓞 K) * a) := by rw [mul_assoc]
        _ = a := hc.symm
        _ = (1 : 𝓞 K) * a := by simp
    exact mul_eq_one_iff_eq_inv.mp hnorm
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ v (by norm_num)
  have hv_sq : v ^ 2 = (hζ.unit' ^ j) ^ 2 := by
    simpa only [hvconj, inv_inv, pow_two] using hj
  refine ⟨2 * j, ?_⟩
  rw [map_pow, hv, mul_pow, ← Units.val_pow_eq_pow_val, hv_sq]
  congr 1
  rw [← pow_mul, Nat.mul_comm]

/-- A conjugation-stable principal ideal prime to `(ζ - 1)` admits a
generator, still prime to `(ζ - 1)`, together with the exact cyclotomic
conjugation exponent required by `ConjugationPowerReductionData67`. -/
lemma exists_conjugation_power_generator67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (I : Ideal (𝓞 K))
    (hprincipal : Submodule.IsPrincipal
      (I : Submodule (𝓞 K) (𝓞 K)))
    (hprime : ¬ Ideal.span
      ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ∣ I)
    (hstable : conjugateIdeal67 I = I) :
    ∃ (a : 𝓞 K) (j : ℕ),
      I = Ideal.span {a} ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a ∧
      ringOfIntegersComplexConj K a =
        (hζ.unit' ^ j : (𝓞 K)ˣ) * a := by
  obtain ⟨a, haI⟩ := hprincipal.principal
  change I = Ideal.span {a} at haI
  have ha : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a := by
    intro ha
    apply hprime
    rw [haI, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
    exact ha
  have hstableA : conjugateIdeal67 (Ideal.span {a}) =
      Ideal.span {a} := by
    rw [← haI]
    exact hstable
  obtain ⟨j, hj⟩ := conjugation_eq_zeta_pow_of_stable_principal67
    hζ a ha hstableA
  exact ⟨a, j, haI, ha, hj⟩

end StablePrincipalGenerator

/-- The inverse of 2 modulo 67, used to make a generator real. -/
def realGeneratorHalfExponent67 : ℕ := 34

theorem two_mul_realGeneratorHalfExponent67_mod :
    2 * realGeneratorHalfExponent67 % 67 = 1 := by
  decide

/-- The explicit adjustment of a principal generator by the half-power of
its cyclotomic conjugation quotient. -/
def realAdjustedGenerator67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (a : 𝓞 K) (j : ℕ) : 𝓞 K :=
  (hζ.unit' ^ (realGeneratorHalfExponent67 * j) : (𝓞 K)ˣ) * a

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
lemma realAdjustedGenerator67_associated {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K) (j : ℕ) :
    Associated (realAdjustedGenerator67 hζ a j) a := by
  let v : (𝓞 K)ˣ := hζ.unit' ^ (realGeneratorHalfExponent67 * j)
  refine ⟨v⁻¹, ?_⟩
  change (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) = a
  calc
    (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) =
        a * ((v : 𝓞 K) * (v⁻¹ : (𝓞 K)ˣ)) := by ac_rfl
    _ = a := by rw [← Units.val_mul]; simp

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
lemma realAdjustedGenerator67_pow_sixtySeven {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K) (j : ℕ) :
    realAdjustedGenerator67 hζ a j ^ 67 = a ^ 67 := by
  rw [realAdjustedGenerator67, mul_pow]
  have hzpow : hζ.unit' ^ 67 = 1 := by
    ext
    exact hζ.pow_eq_one
  have hvpow :
      (hζ.unit' ^ (realGeneratorHalfExponent67 * j)) ^ 67 = 1 := by
    rw [← pow_mul]
    rw [show (realGeneratorHalfExponent67 * j) * 67 =
      67 * (realGeneratorHalfExponent67 * j) by omega]
    rw [pow_mul, hzpow, one_pow]
  rw [← Units.val_pow_eq_pow_val, hvpow]
  simp

lemma realAdjustedGenerator67_real
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K) (j : ℕ)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
      (realAdjustedGenerator67 hζ a j) =
        realAdjustedGenerator67 hζ a j := by
  let k := realGeneratorHalfExponent67 * j
  let v : (𝓞 K)ˣ := hζ.unit' ^ k
  have hzpow : hζ.unit' ^ 67 = 1 := by
    ext
    exact hζ.pow_eq_one
  have hv_sq : v ^ 2 = hζ.unit' ^ j := by
    dsimp [v, k, realGeneratorHalfExponent67]
    rw [← pow_mul]
    have hexp : (34 * j) * 2 = j + 67 * j := by omega
    rw [hexp, pow_add, pow_mul, hzpow, one_pow, mul_one]
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((v : 𝓞 K) * a) = (v : 𝓞 K) * a
  rw [map_mul]
  have hvconj : NumberField.IsCMField.ringOfIntegersComplexConj K (v : 𝓞 K) =
      (v⁻¹ : (𝓞 K)ˣ) := by
    have hvconjU :
        NumberField.IsCMField.unitsComplexConj K v = v⁻¹ := by
      dsimp [v]
      rw [map_pow, unitsComplexConj_zeta67 hζ, inv_pow]
    exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hvconjU
  rw [hvconj, ha]
  rw [← mul_assoc, ← Units.val_mul, ← hv_sq]
  congr 1
  rw [pow_two, ← mul_assoc]
  simp

/-- If complex conjugation changes a principal generator by a power
ζ ^ j, multiplying the generator by ζ ^ (34 * j) makes it real.

This is the explicit odd-order normalization in the real-generator step
behind Vandiver's equations (7b)--(10a): 34 is the inverse of 2 modulo
67, so

conj (ζ ^ (34*j) * a) = ζ ^ (j-34*j) * a = ζ ^ (34*j) * a.

The resulting generator is associated to the original one, hence generates
the same principal ideal. What remains in
RealPrincipalGeneratorElimination67 is to prove that the conjugation
quotients supplied by the relevant ideal calculation have precisely this
ζ ^ j form and then to carry out Vandiver's eliminations. -/
lemma exists_real_associated_generator_of_conj_eq_zeta_pow
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (a : 𝓞 K) (j : ℕ)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    ∃ b : 𝓞 K, Associated b a ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K b = b := by
  exact ⟨realAdjustedGenerator67 hζ a j,
    realAdjustedGenerator67_associated hζ a j,
    realAdjustedGenerator67_real hζ a j ha⟩

set_option maxRecDepth 3000 in
/-- The real-generator conclusion used immediately after Vandiver's
equation (9).

Suppose `J ^ 67 = (q)`, the element `q` is fixed by conjugation, and `J` is
prime to `( ζ - 1 )`.  Applying the already-proved relative-norm form of
(7d) gives

`q² = ε * ρ^67`

with `ρ` real.  Comparing principal ideals and using injectivity of the
67th-power map on the unique-factorization monoid of integral ideals shows
that `J²` is principal.  Since `J^67` is principal and
`gcd(2,67)=1`, `J` itself is principal.  Its conjugation stability follows
from the reality of `q`; the explicit `ζ^(34*j)` normalization then
chooses a real generator `μ`.  Finally

`q = η * μ^67`,

which is the element equation written after (9) in the 1929 paper. -/
theorem exists_realEquationNineGenerator67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (J : Ideal (𝓞 K)) (q : 𝓞 K)
    (hprime : ¬ Ideal.span
      ({(hzeta.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ∣ J)
    (hqreal : NumberField.IsCMField.ringOfIntegersComplexConj K q = q)
    (hpow : J ^ 67 = Ideal.span {q}) :
    ∃ (μ : 𝓞 K) (η : (𝓞 K)ˣ),
      J = Ideal.span {μ} ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K μ = μ ∧
      q = η * μ ^ 67 := by
  obtain ⟨ρ, ε, -, -, hnorm⟩ :=
    exists_equationSevenD_of_idealPower67 hzeta J q hpow
  let ρK : 𝓞 K := algebraMap (𝓞 K⁺) (𝓞 K) ρ
  let εK : (𝓞 K)ˣ := Units.map
    (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom ε
  have hq_sq : q ^ 2 = (εK : 𝓞 K) * ρK ^ 67 := by
    simpa only [pow_two, hqreal, ρK, εK, Units.coe_map] using hnorm
  have hassoc : Associated (q ^ 2) (ρK ^ 67) := by
    refine ⟨εK⁻¹, ?_⟩
    rw [hq_sq]
    calc
      ((εK : 𝓞 K) * ρK ^ 67) * (εK⁻¹ : (𝓞 K)ˣ) =
          ρK ^ 67 * ((εK : 𝓞 K) * (εK⁻¹ : (𝓞 K)ˣ)) := by
        ac_rfl
      _ = ρK ^ 67 := by rw [← Units.val_mul]; simp
  have hspan : Ideal.span {q ^ 2} = Ideal.span {ρK ^ 67} :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hpoweq : (J ^ 2) ^ 67 = (Ideal.span {ρK}) ^ 67 := by
    calc
      (J ^ 2) ^ 67 = (J ^ 67) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
      _ = (Ideal.span {q}) ^ 2 := by rw [hpow]
      _ = Ideal.span {q ^ 2} := Ideal.span_singleton_pow q 2
      _ = Ideal.span {ρK ^ 67} := hspan
      _ = (Ideal.span {ρK}) ^ 67 := (Ideal.span_singleton_pow ρK 67).symm
  have hJ2eq : J ^ 2 = Ideal.span {ρK} :=
    pow_left_injective (M := Ideal (𝓞 K)) (by norm_num : 67 ≠ 0) hpoweq
  have hJ2 : Submodule.IsPrincipal (J ^ 2 : Ideal (𝓞 K)) := by
    rw [hJ2eq]
    infer_instance
  have hJ67 : Submodule.IsPrincipal (J ^ 67 : Ideal (𝓞 K)) := by
    rw [hpow]
    infer_instance
  have hJprincipal : Submodule.IsPrincipal (J : Ideal (𝓞 K)) :=
    ideal_isPrincipal_of_coprime_powers (L := K) (by norm_num) J hJ2 hJ67
  have hstable : conjugateIdeal67 J = J := by
    apply pow_left_injective (M := Ideal (𝓞 K)) (by norm_num : 67 ≠ 0)
    calc
      conjugateIdeal67 J ^ 67 = conjugateIdeal67 (J ^ 67) := by
        exact (Ideal.map_pow
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom J 67).symm
      _ = conjugateIdeal67 (Ideal.span {q}) := by rw [hpow]
      _ = Ideal.span
          {NumberField.IsCMField.ringOfIntegersComplexConj K q} :=
        conjugateIdeal67_span q
      _ = Ideal.span {q} := by rw [hqreal]
      _ = J ^ 67 := hpow.symm
  obtain ⟨a, j, hJa, -, hconj⟩ := exists_conjugation_power_generator67
    hzeta J hJprincipal hprime hstable
  obtain ⟨μ, hμa, hμreal⟩ :=
    exists_real_associated_generator_of_conj_eq_zeta_pow hzeta a j hconj
  have hJμ : J = Ideal.span {μ} := by
    rw [hJa]
    exact Ideal.span_singleton_eq_span_singleton.mpr hμa.symm
  have hassoc_q : Associated (μ ^ 67) q := by
    rw [← Ideal.span_singleton_eq_span_singleton,
      ← Ideal.span_singleton_pow, ← hJμ, hpow]
  obtain ⟨η, hη⟩ := hassoc_q
  exact ⟨μ, η, hJμ, hμreal, by simpa [mul_comm] using hη.symm⟩

set_option maxRecDepth 3000 in
/-- The principalization part of the real-generator argument does not need
the ideal to be prime to `ζ - 1`.

If `J ^ 67 = (q)` and `q` is real, relative norm makes `J ^ 2`
principal.  The coprime exponents `2` and `67` then principalize `J`, and
reality of `q` makes `J` stable under complex conjugation.  Primeness to
the ramified ideal is needed only for removing the possible minus sign from
the conjugation quotient of an individual generator. -/
theorem ideal_isPrincipal_and_stable_of_real_pow67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (J : Ideal (𝓞 K)) (q : 𝓞 K)
    (hqreal : NumberField.IsCMField.ringOfIntegersComplexConj K q = q)
    (hpow : J ^ 67 = Ideal.span {q}) :
    Submodule.IsPrincipal (J : Ideal (𝓞 K)) ∧
      conjugateIdeal67 J = J := by
  obtain ⟨ρ, ε, -, -, hnorm⟩ :=
    exists_equationSevenD_of_idealPower67 hzeta J q hpow
  let ρK : 𝓞 K := algebraMap (𝓞 K⁺) (𝓞 K) ρ
  let εK : (𝓞 K)ˣ := Units.map
    (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom ε
  have hq_sq : q ^ 2 = (εK : 𝓞 K) * ρK ^ 67 := by
    simpa only [pow_two, hqreal, ρK, εK, Units.coe_map] using hnorm
  have hassoc : Associated (q ^ 2) (ρK ^ 67) := by
    refine ⟨εK⁻¹, ?_⟩
    rw [hq_sq]
    calc
      ((εK : 𝓞 K) * ρK ^ 67) * (εK⁻¹ : (𝓞 K)ˣ) =
          ρK ^ 67 * ((εK : 𝓞 K) * (εK⁻¹ : (𝓞 K)ˣ)) := by
        ac_rfl
      _ = ρK ^ 67 := by rw [← Units.val_mul]; simp
  have hspan : Ideal.span {q ^ 2} = Ideal.span {ρK ^ 67} :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hpoweq : (J ^ 2) ^ 67 = (Ideal.span {ρK}) ^ 67 := by
    calc
      (J ^ 2) ^ 67 = (J ^ 67) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
      _ = (Ideal.span {q}) ^ 2 := by rw [hpow]
      _ = Ideal.span {q ^ 2} := Ideal.span_singleton_pow q 2
      _ = Ideal.span {ρK ^ 67} := hspan
      _ = (Ideal.span {ρK}) ^ 67 :=
        (Ideal.span_singleton_pow ρK 67).symm
  have hJ2eq : J ^ 2 = Ideal.span {ρK} :=
    pow_left_injective (M := Ideal (𝓞 K)) (by norm_num : 67 ≠ 0) hpoweq
  have hJ2 : Submodule.IsPrincipal (J ^ 2 : Ideal (𝓞 K)) := by
    rw [hJ2eq]
    infer_instance
  have hJ67 : Submodule.IsPrincipal (J ^ 67 : Ideal (𝓞 K)) := by
    rw [hpow]
    infer_instance
  have hJprincipal : Submodule.IsPrincipal (J : Ideal (𝓞 K)) :=
    ideal_isPrincipal_of_coprime_powers (L := K) (by norm_num) J hJ2 hJ67
  have hstable : conjugateIdeal67 J = J := by
    apply pow_left_injective (M := Ideal (𝓞 K)) (by norm_num : 67 ≠ 0)
    calc
      conjugateIdeal67 J ^ 67 = conjugateIdeal67 (J ^ 67) := by
        exact (Ideal.map_pow
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom J 67).symm
      _ = conjugateIdeal67 (Ideal.span {q}) := by rw [hpow]
      _ = Ideal.span
          {NumberField.IsCMField.ringOfIntegersComplexConj K q} :=
        conjugateIdeal67_span q
      _ = Ideal.span {q} := by rw [hqreal]
      _ = J ^ 67 := hpow.symm
  exact ⟨hJprincipal, hstable⟩

set_option maxRecDepth 3000 in
/-- Equation-(8a) generator extraction in the form needed later in the
historical descent.

The ideal may contain the ramified prime, so an individual generator can
have conjugation quotient `-ζ^j`.  The theorem records the square of the
generator instead; its quotient is always a pure power of `ζ`. -/
theorem exists_squaredConjugationGenerator_of_real_pow67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (J : Ideal (𝓞 K)) (q : 𝓞 K) (hq0 : q ≠ 0)
    (hqreal : NumberField.IsCMField.ringOfIntegersComplexConj K q = q)
    (hpow : J ^ 67 = Ideal.span {q}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ) (j : ℕ),
      J = Ideal.span {ρ} ∧
      q = η * ρ ^ 67 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K (ρ ^ 2) =
        (hzeta.unit' ^ j : (𝓞 K)ˣ) * ρ ^ 2 := by
  obtain ⟨hprincipal, hstable⟩ :=
    ideal_isPrincipal_and_stable_of_real_pow67 hzeta J q hqreal hpow
  obtain ⟨ρ, hJρ⟩ := hprincipal.principal
  change J = Ideal.span {ρ} at hJρ
  have hρ0 : ρ ≠ 0 := by
    intro hρ
    apply hq0
    rw [← Ideal.span_singleton_eq_bot]
    calc
      Ideal.span {q} = J ^ 67 := hpow.symm
      _ = (Ideal.span {ρ}) ^ 67 := by rw [hJρ]
      _ = 0 := by
        rw [hρ]
        norm_num
        rw [Ideal.zero_eq_bot]
  have hstableρ : conjugateIdeal67 (Ideal.span {ρ}) =
      Ideal.span {ρ} := by
    rw [← hJρ]
    exact hstable
  obtain ⟨j, hj⟩ :=
    conjugation_sq_eq_zeta_pow_of_stable_principal67 hzeta ρ hρ0 hstableρ
  have hassoc_q : Associated (ρ ^ 67) q := by
    rw [← Ideal.span_singleton_eq_span_singleton,
      ← Ideal.span_singleton_pow, ← hJρ, hpow]
  obtain ⟨η, hη⟩ := hassoc_q
  exact ⟨ρ, η, j, hJρ, by simpa [mul_comm] using hη.symm, hj⟩

set_option maxRecDepth 3000 in
/-- Vandiver's equation (8a), including exactly the conjugation data needed
after the equation is squared in (10a).

No hypothesis `ζ - 1 ∤ ξ` is required.  If the residual ideal contains the
ramified prime, its generator may acquire a minus sign under conjugation;
the square of the generator and the square of the coefficient unit are
nevertheless conjugation-compatible, which is all the subsequent quadratic
elimination uses. -/
theorem exists_historicalEquationEightA67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρzero : 𝓞 K) (ηzero : (𝓞 K)ˣ) (jzero : ℕ),
      s.omega + s.theta =
        ηzero * kappa hζ ^ (67 * s.m - 33) * ρzero ^ 67 ∧
      historicalEquationEightAIdeal67 hζ s = Ideal.span {ρzero} ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K (ρzero ^ 2) =
        (hζ.unit' ^ jzero : (𝓞 K)ˣ) * ρzero ^ 2 ∧
      NumberField.IsCMField.unitsComplexConj K (ηzero ^ 2) =
        ηzero ^ 2 := by
  let J : Ideal (𝓞 K) := historicalEquationEightAIdeal67 hζ s
  let q : 𝓞 K := historicalEquationEightAQuotient67 hζ s hs
  obtain ⟨ρ, η, j, hJ, hq, hρconj⟩ :=
    exists_squaredConjugationGenerator_of_real_pow67 hζ J q
      (by simpa only [q] using
        historicalEquationEightAQuotient_ne_zero67 hζ s hs)
      (by simpa only [q] using
        historicalEquationEightAQuotient_real67 hζ s hs)
      (by simpa only [J, q] using
        historicalEquationEightAIdeal_pow67 hζ s hs)
  have hq0 : q ≠ 0 := by
    simpa only [q] using historicalEquationEightAQuotient_ne_zero67 hζ s hs
  have hρ0 : ρ ≠ 0 := by
    intro hρ
    apply hq0
    rw [hq, hρ]
    norm_num
  have hzeta67 : hζ.unit' ^ 67 = 1 := by
    apply Units.ext
    apply NumberField.RingOfIntegers.ext
    change ζ ^ 67 = 1
    exact hζ.pow_eq_one
  have hroot67 : (hζ.unit' ^ j) ^ 67 = 1 := by
    rw [← pow_mul]
    rw [show j * 67 = 67 * j by omega, pow_mul, hzeta67, one_pow]
  have hρ118real :
      NumberField.IsCMField.ringOfIntegersComplexConj K (ρ ^ 134) =
        ρ ^ 134 := by
    have h118 : ρ ^ 134 = (ρ ^ 2) ^ 67 := by
      rw [← pow_mul]
    rw [h118, map_pow, hρconj, mul_pow,
      ← Units.val_pow_eq_pow_val, hroot67, Units.val_one, one_mul, ← h118]
  have hq2 : q ^ 2 = ((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) * ρ ^ 134 := by
    rw [hq, mul_pow, ← Units.val_pow_eq_pow_val, ← pow_mul]
  have hηsqVal :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          ((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) =
        ((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) := by
    apply mul_right_cancel₀ (pow_ne_zero 134 hρ0)
    calc
      NumberField.IsCMField.ringOfIntegersComplexConj K
            ((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) * ρ ^ 134 =
          NumberField.IsCMField.ringOfIntegersComplexConj K
            (((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) * ρ ^ 134) := by
              rw [map_mul, hρ118real]
      _ = NumberField.IsCMField.ringOfIntegersComplexConj K (q ^ 2) := by
        rw [hq2]
      _ = q ^ 2 := by rw [map_pow,
        historicalEquationEightAQuotient_real67 hζ s hs]
      _ = ((η ^ 2 : (𝓞 K)ˣ) : 𝓞 K) * ρ ^ 134 := hq2
  have hηsq : NumberField.IsCMField.unitsComplexConj K (η ^ 2) =
      η ^ 2 := by
    apply Units.ext
    exact hηsqVal
  refine ⟨ρ, η, j, ?_, ?_, hρconj, hηsq⟩
  · calc
      s.omega + s.theta =
          kappa hζ ^ (67 * s.m - 33) * q :=
        historicalEquationEightAQuotient_spec67 hζ s hs
      _ = kappa hζ ^ (67 * s.m - 33) *
          ((η : 𝓞 K) * ρ ^ 67) := by rw [hq]
      _ = (η : 𝓞 K) * kappa hζ ^ (67 * s.m - 33) * ρ ^ 67 := by
        ring
  · simpa only [J] using hJ

/-- Complex conjugation sends any integral 67th root of unity to its
58th power, i.e. its inverse. -/
lemma ringOfIntegersComplexConj_nthRoot67
    (η : Polynomial.nthRootsFinset 67 (1 : 𝓞 K)) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) =
      (η : 𝓞 K) ^ 66 := by
  have hηpow : (η : 𝓞 K) ^ 67 = 1 :=
    (Polynomial.mem_nthRootsFinset (by norm_num : 0 < 67) (1 : 𝓞 K)).mp η.prop
  let u : (𝓞 K)ˣ :=
    ⟨(η : 𝓞 K), (η : 𝓞 K) ^ 66,
      by simpa only [← pow_succ'] using hηpow,
      by simpa only [mul_comm, ← pow_succ'] using hηpow⟩
  have hupow : u ^ 67 = 1 := by
    apply Units.ext
    simpa only [u, Units.val_pow_eq_pow_val, Units.val_one] using hηpow
  have huTorsion : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨67, by norm_num, hupow⟩
  have hc : NumberField.IsCMField.unitsComplexConj K u = u⁻¹ := by
    simpa using NumberField.IsCMField.unitsComplexConj_torsion
      (K := K) (⟨u, huTorsion⟩ : NumberField.Units.torsion K)
  exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hc

/-- The exact high-divisibility conclusion of Vandiver's equation (9a),
once the difference equation preceding (9) has been obtained.

The generic factor-allocation theorem selects a `67`th root `η` for which

`(ζ - 1)^((2*m-2)*67+1) ∣ ρₐ - η*ρ₋ₐ`.

Multiplying the pair symmetrically by `η^33` and `η^34` turns this into a
literal difference.  Both 67th powers are unchanged; the exponents are the
two half-powers surrounding `34`, the inverse of `2` modulo `67`.  No
class-number hypothesis is used in this step. -/
theorem equationNineA_normalized67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (m : ℕ) (hm : 1 < m) (ρa ρminus ρzero : 𝓞 K) (ε : (𝓞 K)ˣ)
    (hdiff : ρa ^ 67 - ρminus ^ 67 =
      ε * ((hζ.unit'.1 - 1) ^ (2 * m - 1) * ρzero) ^ 67)
    (hminus : ¬ hζ.unit'.1 - 1 ∣ ρminus) :
    ∃ ρa' ρminus' : 𝓞 K,
      ρa' ^ 67 = ρa ^ 67 ∧
      ρminus' ^ 67 = ρminus ^ 67 ∧
      (hζ.unit'.1 - 1) ^ ((2 * m - 2) * 67 + 1) ∣
        ρa' - ρminus' := by
  have hexp : 2 * m - 1 = (2 * m - 2) + 1 := by omega
  have e' : ρa ^ 67 + (-ρminus) ^ 67 =
      ε * ((hζ.unit'.1 - 1) ^ ((2 * m - 2) + 1) * ρzero) ^ 67 := by
    rw [← hexp]
    simpa only [Odd.neg_pow (by norm_num : Odd 67), sub_eq_add_neg] using hdiff
  have hy' : ¬ hζ.unit'.1 - 1 ∣ -ρminus := by
    simpa using hminus
  let η := zeta_sub_one_dvd_root (by norm_num : 67 ≠ 2) hζ e' hy'
  have hηdiv : (hζ.unit'.1 - 1) ^ ((2 * m - 2) * 67 + 1) ∣
      ρa - (η : 𝓞 K) * ρminus := by
    simpa only [sub_eq_add_neg, neg_mul, mul_comm] using
      (distinguishedFactor_highDivisibility (by norm_num : 67 ≠ 2)
        hζ e' hy')
  have hηpow : (η : 𝓞 K) ^ 67 = 1 :=
    (Polynomial.mem_nthRootsFinset (by norm_num : 0 < 67) (1 : 𝓞 K)).mp η.prop
  let ρa' : 𝓞 K := (η : 𝓞 K) ^ 33 * ρa
  let ρminus' : 𝓞 K := (η : 𝓞 K) ^ 34 * ρminus
  refine ⟨ρa', ρminus', ?_, ?_, ?_⟩
  · dsimp [ρa']
    rw [mul_pow, ← pow_mul]
    rw [show 33 * 67 = 67 * 33 by norm_num, pow_mul, hηpow, one_pow,
      one_mul]
  · dsimp [ρminus']
    rw [mul_pow, ← pow_mul]
    rw [show 34 * 67 = 67 * 34 by norm_num, pow_mul, hηpow, one_pow,
      one_mul]
  · have hrewrite : ρa' - ρminus' =
        (η : 𝓞 K) ^ 33 * (ρa - (η : 𝓞 K) * ρminus) := by
      dsimp [ρa', ρminus']
      rw [pow_succ' (η : 𝓞 K) 33]
      ring
    rw [hrewrite]
    exact dvd_mul_of_dvd_right hηdiv ((η : 𝓞 K) ^ 33)

/-- Conjugation-compatible form of equation (9a).

When the two inputs are conjugate, the symmetric normalization by the
18th and 19th powers of the distinguished 67th root preserves that
relation: conjugation changes the root to its inverse and
`-33 ≡ 34 (mod 67)`.  The normalized inverse generator remains prime to
`ζ - 1`. -/
theorem equationNineA_normalized_conjugate67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (m : ℕ) (hm : 1 < m) (ρa ρminus ρzero : 𝓞 K) (ε : (𝓞 K)ˣ)
    (hdiff : ρa ^ 67 - ρminus ^ 67 =
      ε * ((hζ.unit'.1 - 1) ^ (2 * m - 1) * ρzero) ^ 67)
    (hconj : NumberField.IsCMField.ringOfIntegersComplexConj K ρa = ρminus)
    (hminus : ¬ hζ.unit'.1 - 1 ∣ ρminus) :
    ∃ ρa' ρminus' : 𝓞 K,
      ρa' ^ 67 = ρa ^ 67 ∧
      ρminus' ^ 67 = ρminus ^ 67 ∧
      (hζ.unit'.1 - 1) ^ ((2 * m - 2) * 67 + 1) ∣
        ρa' - ρminus' ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K ρa' = ρminus' ∧
      ¬ hζ.unit'.1 - 1 ∣ ρminus' := by
  have hexp : 2 * m - 1 = (2 * m - 2) + 1 := by omega
  have e' : ρa ^ 67 + (-ρminus) ^ 67 =
      ε * ((hζ.unit'.1 - 1) ^ ((2 * m - 2) + 1) * ρzero) ^ 67 := by
    rw [← hexp]
    simpa only [Odd.neg_pow (by norm_num : Odd 67), sub_eq_add_neg] using hdiff
  have hy' : ¬ hζ.unit'.1 - 1 ∣ -ρminus := by
    simpa using hminus
  let η := zeta_sub_one_dvd_root (by norm_num : 67 ≠ 2) hζ e' hy'
  have hηdiv : (hζ.unit'.1 - 1) ^ ((2 * m - 2) * 67 + 1) ∣
      ρa - (η : 𝓞 K) * ρminus := by
    simpa only [sub_eq_add_neg, neg_mul, mul_comm] using
      (distinguishedFactor_highDivisibility (by norm_num : 67 ≠ 2)
        hζ e' hy')
  have hηpow : (η : 𝓞 K) ^ 67 = 1 :=
    (Polynomial.mem_nthRootsFinset (by norm_num : 0 < 67) (1 : 𝓞 K)).mp η.prop
  have hηconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) =
        (η : 𝓞 K) ^ 66 :=
    ringOfIntegersComplexConj_nthRoot67 η
  have hηunit : IsUnit (η : 𝓞 K) := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨(η : 𝓞 K) ^ 66, ?_⟩
    simpa only [← pow_succ'] using hηpow.symm
  let ρa' : 𝓞 K := (η : 𝓞 K) ^ 33 * ρa
  let ρminus' : 𝓞 K := (η : 𝓞 K) ^ 34 * ρminus
  refine ⟨ρa', ρminus', ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [ρa']
    rw [mul_pow, ← pow_mul]
    rw [show 33 * 67 = 67 * 33 by norm_num, pow_mul, hηpow, one_pow,
      one_mul]
  · dsimp [ρminus']
    rw [mul_pow, ← pow_mul]
    rw [show 34 * 67 = 67 * 34 by norm_num, pow_mul, hηpow, one_pow,
      one_mul]
  · have hrewrite : ρa' - ρminus' =
        (η : 𝓞 K) ^ 33 * (ρa - (η : 𝓞 K) * ρminus) := by
      dsimp [ρa', ρminus']
      rw [pow_succ' (η : 𝓞 K) 33]
      ring
    rw [hrewrite]
    exact dvd_mul_of_dvd_right hηdiv ((η : 𝓞 K) ^ 33)
  · dsimp [ρa', ρminus']
    rw [map_mul, map_pow, hηconj, hconj, ← pow_mul]
    rw [show 66 * 33 = 67 * 32 + 34 by norm_num,
      pow_add, pow_mul, hηpow, one_pow, one_mul]
  · dsimp [ρminus']
    intro hram
    rcases hζ.zeta_sub_one_prime'.dvd_mul.mp hram with hroot | hρ
    · exact hζ.zeta_sub_one_prime'.not_unit
        (isUnit_of_dvd_unit hroot (hηunit.pow 34))
    · exact hminus hρ

/-- A `67`th root of a real unit can be adjusted by a power of `ζ`
without changing its `67`th power so that the root itself is real. This is
the real-root normalization used implicitly between Vandiver's equations
(10) and (10b). -/
lemma exists_real_unit_root_67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 67) :
    ∃ w : (𝓞 K)ˣ, a = w ^ 67 ∧
      NumberField.IsCMField.unitsComplexConj K w = w := by
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ v (by norm_num)
  let w : (𝓞 K)ˣ := v / hζ.unit' ^ j
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    rw [div_pow, ← hv]
    have hzpow : hζ.unit' ^ 67 = 1 := by
      ext
      exact hζ.pow_eq_one
    rw [← pow_mul, show j * 67 = 67 * j by omega, pow_mul, hzpow, one_pow,
      div_one]
  · dsimp [w]
    rw [map_div, map_pow, unitsComplexConj_zeta67 hζ]
    rw [← div_eq_mul_inv] at hj
    have hmul : v = (hζ.unit' ^ j) ^ 2 *
        NumberField.IsCMField.unitsComplexConj K v :=
      div_eq_iff_eq_mul.mp hj
    rw [inv_pow, div_inv_eq_mul]
    calc
      NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j =
          (hζ.unit' ^ j) ^ 2 *
              NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j := by
        symm
        rw [pow_two]
        calc
          (hζ.unit' ^ j * hζ.unit' ^ j) *
                NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j =
              (NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j) *
                hζ.unit' ^ j / hζ.unit' ^ j := by ac_rfl
          _ = NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j :=
            mul_div_cancel_right _ _
      _ = v / hζ.unit' ^ j := by rw [← hmul]

/-- At exponent `67`, Vandiver's `κ^33` is associated to the rational
prime `67`. -/
lemma kappa_pow_thirtyThree_associated_67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    Associated (kappa hζ ^ 33) (67 : 𝓞 K) := by
  have hleft : Associated
      ((1 : 𝓞 K) - hζ.unit') ((hζ.unit' : 𝓞 K) - 1) := by
    refine ⟨-1, ?_⟩
    simp
  have hright : Associated
      ((1 : 𝓞 K) - (hζ.unit')⁻¹) ((hζ.unit' : 𝓞 K) - 1) := by
    refine ⟨hζ.unit', ?_⟩
    simp [sub_mul]
  have hkappa : Associated (kappa hζ)
      (((hζ.unit' : 𝓞 K) - 1) ^ 2) := by
    simpa [kappa, pow_two] using hleft.mul_mul hright
  have hkappaPow := hkappa.pow_pow (n := 33)
  rw [← pow_mul] at hkappaPow
  norm_num at hkappaPow
  have hprime := associated_zeta_sub_one_pow_prime hζ
  norm_num at hprime
  exact hkappaPow.trans hprime

/-- A primitive rational second-case solution at exponent `67` gives
Vandiver's equation (6) with `m = 33`. This discharges the first abstract
boundary of `VandiverHistoricalDescent` for the concrete real invariant. -/
theorem secondCaseStartsHistoricalDescent_67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    SecondCaseStartsHistoricalDescent hζ (RealSourceAdmissible hζ) := by
  intro x y z hgcd hz hz0 e
  have hx : x ≠ 0 := by
    intro hx0
    have hyz : y = z := (show Odd 67 by norm_num).pow_injective (by simpa [hx0] using e)
    have h67one : (67 : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hx0]
        exact dvd_zero _
      · rw [hyz]
        exact hz
      · exact hz
    norm_num at h67one
  have hy : y ≠ 0 := by
    intro hy0
    have hxz : x = z := (show Odd 67 by norm_num).pow_injective (by simpa [hy0] using e)
    have h67one : (67 : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hxz]
        exact hz
      · rw [hy0]
        exact dvd_zero _
      · exact hz
    norm_num at h67one
  obtain ⟨hxy, hyz, hxz⟩ :=
    Fermat.pairwiseCoprime_of_primitive_solution (by norm_num) hx hy hz0 hgcd e
  obtain ⟨t, rfl⟩ := hz
  have ht0 : t ≠ 0 := by
    intro ht
    apply hz0
    simp [ht]
  obtain ⟨u, hu⟩ := kappa_pow_thirtyThree_associated_67 hζ
  have hkappa0 : kappa hζ ^ 33 ≠ 0 :=
    (kappa_pow_thirtyThree_associated_67 hζ).ne_zero_iff.mpr (by norm_num)
  have huReal :
      NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) = u := by
    have hconj := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hu
    simp only [map_mul, map_pow, ringOfIntegersComplexConj_kappa hζ,
      map_ofNat] at hconj
    exact mul_left_cancel₀ hkappa0 (hconj.trans hu.symm)
  let ξ : 𝓞 K := (u : 𝓞 K) * (t : 𝓞 K)
  have hyt : IsCoprime (y : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hyz.intCast (R := 𝓞 K)
    have hcast' : IsCoprime (y : 𝓞 K) (((67 : ℤ) : 𝓞 K) * (t : 𝓞 K)) := by
      simpa only [Int.cast_mul] using hcast
    exact hcast'.of_mul_right_right
  have hxt : IsCoprime (x : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hxz.intCast (R := 𝓞 K)
    have hcast' : IsCoprime (x : 𝓞 K) (((67 : ℤ) : 𝓞 K) * (t : 𝓞 K)) := by
      simpa only [Int.cast_mul] using hcast
    exact hcast'.of_mul_right_right
  let s : HistoricalState hζ :=
    { omega := x
      theta := y
      xi := ξ
      eta := 1
      m := 33
      one_lt_m := by norm_num
      xi_ne_zero := by
        dsimp [ξ]
        exact mul_ne_zero u.isUnit.ne_zero (Int.cast_ne_zero.mpr ht0)
      coprime_omega_theta := hxy.intCast
      coprime_theta_xi := by
        dsimp [ξ]
        exact (isCoprime_mul_unit_left_right u.isUnit (y : 𝓞 K) (t : 𝓞 K)).mpr hyt
      coprime_omega_xi := by
        dsimp [ξ]
        exact (isCoprime_mul_unit_left_right u.isUnit (x : 𝓞 K) (t : 𝓞 K)).mpr hxt
      equation := by
        simp only [Units.val_one, one_mul]
        calc
          (x : 𝓞 K) ^ 67 + (y : 𝓞 K) ^ 67 =
              ((((67 : ℤ) * t : ℤ) : 𝓞 K)) ^ 67 := by exact_mod_cast e
          _ = ((67 : 𝓞 K) * (t : 𝓞 K)) ^ 67 := by norm_num
          _ = (kappa hζ ^ 33 * ((u : 𝓞 K) * (t : 𝓞 K))) ^ 67 := by
            congr 1
            rw [← mul_assoc, hu]
          _ = (kappa hζ ^ 33 * ξ) ^ 67 := rfl }
  refine ⟨s, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [s]
    simp
  · dsimp [s]
    simp
  · dsimp [s, ξ]
    simp [huReal]
  · dsimp [s]
    simp

/-! ## The algebraic passage from equation (10) to equation (10b) -/

/-! ### The concrete cyclotomic coefficients at `a = 1`, `b = 2`

Vandiver allows any two suitable conjugate pairs in equation (10).  The
choices `a = 1` and `b = 2` make the unit simplification completely
explicit.  If

`A = ζ + ζ⁻¹` and `B = ζ² + ζ⁻²`,

then

`2 - A = κ`, `A - B = κ (A + 1)`, and
`2 - B = κ (A + 2)`.

The last two factors are units: `A + 1` is `ζ⁻¹(1+ζ+ζ²)`,
and `A + 2` is `ζ⁻¹(1+ζ)²`. -/

/-- The real cyclotomic trace `A = ζ + ζ⁻¹` used in equation
(10). -/
def equationTenTraceOne67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67) : 𝓞 K :=
  (hζ.unit' : 𝓞 K) + (hζ.unit'⁻¹ : (𝓞 K)ˣ)

/-- The real cyclotomic trace `B = ζ² + ζ⁻²` used in equation
(10). -/
def equationTenTraceTwo67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67) : 𝓞 K :=
  (hζ.unit' : 𝓞 K) ^ 2 + (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2

/-- The cyclotomic unit `ζ⁻¹(1+ζ+ζ²) = A+1`. -/
def equationTenTraceOneUnit67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) : (𝓞 K)ˣ :=
  hζ.unit'⁻¹ *
    (hζ.unit'_coe.geom_sum_isUnit (by norm_num)
      (by norm_num : Nat.Coprime 3 67)).unit

/-- The cyclotomic unit `ζ⁻¹(1+ζ)² = A+2`. -/
def equationTenTraceTwoUnit67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) : (𝓞 K)ˣ :=
  hζ.unit'⁻¹ *
    (hζ.unit'_coe.geom_sum_isUnit (by norm_num)
      (by norm_num : Nat.Coprime 2 67)).unit ^ 2

omit [IsCyclotomicExtension {67} ℚ K] in
lemma equationTenTraceOneUnit67_val {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    (equationTenTraceOneUnit67 hζ : 𝓞 K) =
      equationTenTraceOne67 hζ + 1 := by
  have huinv : (hζ.unit'⁻¹ : (𝓞 K)ˣ) * (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hgeom :
      (((hζ.unit'_coe.geom_sum_isUnit (by norm_num)
        (by norm_num : Nat.Coprime 3 67)).unit : (𝓞 K)ˣ) : 𝓞 K) =
        1 + (hζ.unit' : 𝓞 K) + (hζ.unit' : 𝓞 K) ^ 2 := by
    rw [(hζ.unit'_coe.geom_sum_isUnit (by norm_num)
      (by norm_num : Nat.Coprime 3 67)).unit_spec]
    norm_num [Finset.sum_range_succ]
  simp only [equationTenTraceOneUnit67, Units.val_mul]
  rw [hgeom]
  simp only [equationTenTraceOne67]
  linear_combination (1 + (hζ.unit' : 𝓞 K)) * huinv

omit [IsCyclotomicExtension {67} ℚ K] in
lemma equationTenTraceTwoUnit67_val {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    (equationTenTraceTwoUnit67 hζ : 𝓞 K) =
      equationTenTraceOne67 hζ + 2 := by
  have huinv : (hζ.unit'⁻¹ : (𝓞 K)ˣ) * (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hgeom :
      (((hζ.unit'_coe.geom_sum_isUnit (by norm_num)
        (by norm_num : Nat.Coprime 2 67)).unit : (𝓞 K)ˣ) : 𝓞 K) =
        1 + (hζ.unit' : 𝓞 K) := by
    rw [(hζ.unit'_coe.geom_sum_isUnit (by norm_num)
      (by norm_num : Nat.Coprime 2 67)).unit_spec]
    norm_num [Finset.sum_range_succ]
  simp only [equationTenTraceTwoUnit67, Units.val_mul,
    Units.val_pow_eq_pow_val]
  rw [hgeom]
  simp only [equationTenTraceOne67]
  linear_combination (2 + (hζ.unit' : 𝓞 K)) * huinv

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- The first concrete coefficient is literally Vandiver's `κ`. -/
lemma two_sub_equationTenTraceOne67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    2 - equationTenTraceOne67 hζ = kappa hζ := by
  have huinv : (hζ.unit' : 𝓞 K) * (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  simp only [equationTenTraceOne67, kappa]
  linear_combination -huinv

omit [IsCyclotomicExtension {67} ℚ K] in
/-- The trace difference `A-B` is `κ` times the explicit unit `A+1`. -/
lemma equationTenTraceOne_sub_two67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    equationTenTraceOne67 hζ - equationTenTraceTwo67 hζ =
      kappa hζ * (equationTenTraceOneUnit67 hζ : 𝓞 K) := by
  rw [equationTenTraceOneUnit67_val]
  have huinv : (hζ.unit' : 𝓞 K) * (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  rw [← two_sub_equationTenTraceOne67 hζ]
  simp only [equationTenTraceOne67, equationTenTraceTwo67]
  linear_combination 2 * huinv

omit [IsCyclotomicExtension {67} ℚ K] in
/-- The second concrete coefficient `2-B` is `κ` times the explicit
unit `A+2`. -/
lemma two_sub_equationTenTraceTwo67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    2 - equationTenTraceTwo67 hζ =
      kappa hζ * (equationTenTraceTwoUnit67 hζ : 𝓞 K) := by
  rw [equationTenTraceTwoUnit67_val]
  have huinv : (hζ.unit' : 𝓞 K) * (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  rw [← two_sub_equationTenTraceOne67 hζ]
  simp only [equationTenTraceOne67, equationTenTraceTwo67]
  linear_combination 2 * huinv

/-! ### Transporting equation (8) to the pair `a = 2,-2` -/

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- The integral unit attached to the primitive root `ζ²` is literally
the square of the unit attached to `ζ`. -/
lemma powTwoPrimitiveRoot_unit67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    (hζ.pow_of_coprime 2 (by norm_num)).unit' = hζ.unit' ^ 2 := by
  ext
  rfl

omit [IsCyclotomicExtension {67} ℚ K] in
/-- Changing the chosen primitive root from `ζ` to `ζ²` multiplies
Vandiver's real ramified factor `κ` by the explicit cyclotomic unit
`A+2`. -/
lemma kappa_powTwoPrimitiveRoot67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    kappa (hζ.pow_of_coprime 2 (by norm_num)) =
      kappa hζ * (equationTenTraceTwoUnit67 hζ : 𝓞 K) := by
  rw [← two_sub_equationTenTraceTwo67 hζ]
  simp only [kappa, powTwoPrimitiveRoot_unit67 hζ,
    Units.val_pow_eq_pow_val, equationTenTraceTwo67]
  change (1 - (hζ.unit' : 𝓞 K) ^ 2) *
      (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2) =
    2 - ((hζ.unit' : 𝓞 K) ^ 2 +
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2)
  have huinv : (hζ.unit' : 𝓞 K) *
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  have huinv2 : (hζ.unit' : 𝓞 K) ^ 2 *
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2 = 1 := by
    rw [← mul_pow, huinv, one_pow]
  ring_nf
  rw [huinv2]
  ring

/-- The trace `ζ+ζ⁻¹` is fixed by complex conjugation. -/
lemma equationTenTraceOne_real67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (equationTenTraceOne67 hζ) =
      equationTenTraceOne67 hζ := by
  have hz :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) =
        (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) (unitsComplexConj_zeta67 hζ)
  have hzinv :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) =
        (hζ.unit' : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    change NumberField.IsCMField.complexConj K ζ⁻¹ = ζ
    rw [map_inv₀,
      Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ,
      inv_inv]
  simp only [equationTenTraceOne67, map_add, hz, hzinv, add_comm]

/-- The cyclotomic unit `A+2` used to transport the historical state to
the primitive root `ζ²` is real. -/
lemma equationTenTraceTwoUnit_real67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) :
    NumberField.IsCMField.unitsComplexConj K
        (equationTenTraceTwoUnit67 hζ) =
      equationTenTraceTwoUnit67 hζ := by
  apply Units.ext
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      (equationTenTraceTwoUnit67 hζ : 𝓞 K) =
    (equationTenTraceTwoUnit67 hζ : 𝓞 K)
  rw [equationTenTraceTwoUnit67_val, map_add,
    equationTenTraceOne_real67 hζ, map_ofNat]

/-- The same historical equation, expressed with primitive root `ζ²`.
The factor `A+2` introduced into `κ` is removed from `ξ` by a unit, so
the equation, nonvanishing, and all three coprimalities are unchanged. -/
noncomputable def historicalStateAtTwo67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) :
    HistoricalState (hζ.pow_of_coprime 2 (by norm_num)) :=
  let u := equationTenTraceTwoUnit67 hζ
  { omega := s.omega
    theta := s.theta
    xi := (((u⁻¹) ^ s.m : (𝓞 K)ˣ) : 𝓞 K) * s.xi
    eta := s.eta
    m := s.m
    one_lt_m := s.one_lt_m
    xi_ne_zero := mul_ne_zero (u⁻¹ ^ s.m).isUnit.ne_zero s.xi_ne_zero
    coprime_omega_theta := s.coprime_omega_theta
    coprime_theta_xi :=
      (isCoprime_mul_unit_left_right (u⁻¹ ^ s.m).isUnit
        s.theta s.xi).mpr s.coprime_theta_xi
    coprime_omega_xi :=
      (isCoprime_mul_unit_left_right (u⁻¹ ^ s.m).isUnit
        s.omega s.xi).mpr s.coprime_omega_xi
    equation := by
      rw [s.equation]
      have hu : (u : 𝓞 K) ^ s.m *
          ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ s.m = 1 := by
        rw [← mul_pow, ← Units.val_mul]
        simp
      have hbase :
          kappa (hζ.pow_of_coprime 2 (by norm_num)) ^ s.m *
              ((((u⁻¹) ^ s.m : (𝓞 K)ˣ) : 𝓞 K) * s.xi) =
            kappa hζ ^ s.m * s.xi := by
        rw [kappa_powTwoPrimitiveRoot67 hζ, mul_pow]
        simp only [Units.val_pow_eq_pow_val]
        calc
          (kappa hζ ^ s.m * (u : 𝓞 K) ^ s.m) *
              (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ s.m * s.xi) =
              kappa hζ ^ s.m *
                (((u : 𝓞 K) ^ s.m *
                  ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ s.m) * s.xi) := by ring
          _ = kappa hζ ^ s.m * s.xi := by rw [hu, one_mul]
      rw [hbase] }

/-- Real admissibility is preserved by the change of primitive root from
`ζ` to `ζ²`. -/
lemma historicalStateAtTwo_admissible67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    RealSourceAdmissible (hζ.pow_of_coprime 2 (by norm_num))
      (historicalStateAtTwo67 hζ s) := by
  let u := equationTenTraceTwoUnit67 hζ
  have hureal : NumberField.IsCMField.unitsComplexConj K u = u := by
    simpa only [u] using equationTenTraceTwoUnit_real67 hζ
  have huinvpow :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (((u⁻¹) ^ s.m : (𝓞 K)ˣ) : 𝓞 K) =
        (((u⁻¹) ^ s.m : (𝓞 K)ˣ) : 𝓞 K) := by
    have huinvpowU :
        NumberField.IsCMField.unitsComplexConj K ((u⁻¹) ^ s.m) =
          (u⁻¹) ^ s.m := by
      rw [map_pow, map_inv, hureal]
    exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) huinvpowU
  refine ⟨hs.1, hs.2.1, ?_, hs.2.2.2⟩
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((((u⁻¹) ^ s.m : (𝓞 K)ˣ) : 𝓞 K) * s.xi) =
    (((u⁻¹) ^ s.m : (𝓞 K)ˣ) : 𝓞 K) * s.xi
  rw [map_mul, huinvpow, hs.2.2.1]

set_option maxRecDepth 3000 in
/-- Vandiver's paired equation (8) at `a=2,-2`.  It is obtained by
applying the already-proved `a=1,-1` construction to the primitive root
`ζ²`; the unit transport above restores the original historical state.
The generators remain prime to the original uniformizer because
`ζ²-1` is associated to `ζ-1`. -/
theorem exists_historicalEquationEight_pair_two67
    (hlemma : LemmaOne K 67)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρtwo ρminus : 𝓞 K) (η : (𝓞 K)ˣ),
      NumberField.IsCMField.unitsComplexConj K η = η ∧
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η * ρtwo ^ 67 ∧
      s.omega + ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ)) * η * ρminus ^ 67 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K ρtwo = ρminus ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρtwo ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρminus := by
  let hζtwo := hζ.pow_of_coprime 2 (by norm_num)
  let stwo := historicalStateAtTwo67 hζ s
  have hstwo : RealSourceAdmissible hζtwo stwo := by
    simpa only [hζtwo, stwo] using
      historicalStateAtTwo_admissible67 hζ s hs
  obtain ⟨ρtwo, ρminus, η, hη, htwo, hminus, hconj,
      hρtwo, hρminus⟩ :=
    exists_historicalEquationEight_pair_one67 hlemma hζtwo stwo hstwo
  have hassoc :
      Associated ((hζ.unit' : 𝓞 K) - 1)
        ((hζtwo.unit' : 𝓞 K) - 1) := by
    simpa only [hζtwo, powTwoPrimitiveRoot_unit67 hζ,
      Units.val_pow_eq_pow_val] using
      hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime
        (by norm_num : Nat.Coprime 2 67)
  refine ⟨ρtwo, ρminus, η, hη, ?_, ?_, hconj, ?_, ?_⟩
  · simpa only [stwo, historicalStateAtTwo67, hζtwo,
      powTwoPrimitiveRoot_unit67 hζ, Units.val_pow_eq_pow_val] using htwo
  · simpa only [stwo, historicalStateAtTwo67, hζtwo,
      powTwoPrimitiveRoot_unit67 hζ] using hminus
  · exact fun h ↦ hρtwo ((hassoc.dvd_iff_dvd_left).mp h)
  · exact fun h ↦ hρminus ((hassoc.dvd_iff_dvd_left).mp h)

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K] in
/-- Vandiver's elimination in equation (10a), separated from the
ideal-theoretic construction of its inputs.

Writing `S = ω² + θ²` and `T = ωθ`, the three equations immediately
before (10a) have left sides `S + A*T`, `S + B*T`, and `S + 2*T`.
Multiplying the first by `2-B`, the second by `2-A`, and subtracting
eliminates both `S` and `T` against the third equation:

`(2-B)(S+A*T) - (2-A)(S+B*T) = (A-B)(S+2*T)`.

In the paper, `A = ζ^a + ζ⁻ᵃ` and `B = ζ^b + ζ⁻ᵇ`.  The subsequent
cyclotomic-unit simplification turns this identity into equation (10b). -/
lemma equationTenA_quadraticElimination67
    (ω θ A B Ua Ub Uzero Xa Xb Xzero : 𝓞 K)
    (ha : ω ^ 2 + A * (ω * θ) + θ ^ 2 = Ua * Xa ^ 67)
    (hb : ω ^ 2 + B * (ω * θ) + θ ^ 2 = Ub * Xb ^ 67)
    (hzero : ω ^ 2 + 2 * (ω * θ) + θ ^ 2 = Uzero * Xzero) :
    (2 - B) * (Ua * Xa ^ 67) - (2 - A) * (Ub * Xb ^ 67) =
      (A - B) * (Uzero * Xzero) := by
  rw [← ha, ← hb, ← hzero]
  ring

omit [IsCyclotomicExtension {67} ℚ K] in
/-- Equation (10a) at the concrete indices `a = 1`, `b = 2`, after
cancelling the common nonzero factor `κ`.  This is Vandiver's literal
cyclotomic-unit simplification from (10a) to the weighted three-term
equation: the coefficient of `Xb ^ 67` is absorbed into the unit `-Ub`,
while the other two coefficient quotients are the explicit geometric-sum
units above. -/
theorem equationTenB_cyclotomicSimplification67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (ω θ Xa Xb Xzero : 𝓞 K) (Ua Ub Uzero : (𝓞 K)ˣ)
    (ha : ω ^ 2 + equationTenTraceOne67 hζ * (ω * θ) + θ ^ 2 =
      Ua * Xa ^ 67)
    (hb : ω ^ 2 + equationTenTraceTwo67 hζ * (ω * θ) + θ ^ 2 =
      Ub * Xb ^ 67)
    (hzero : ω ^ 2 + 2 * (ω * θ) + θ ^ 2 = Uzero * Xzero) :
    (equationTenTraceTwoUnit67 hζ * Ua : (𝓞 K)ˣ) * Xa ^ 67 +
        (-Ub : (𝓞 K)ˣ) * Xb ^ 67 =
      (equationTenTraceOneUnit67 hζ * Uzero : (𝓞 K)ˣ) * Xzero := by
  have hkappa0 : kappa hζ ≠ 0 := by
    rw [kappa_eq_kappaUnit67_mul_sq]
    exact mul_ne_zero (kappaUnit67 hζ).isUnit.ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr
        (hζ.unit'_coe.ne_one (by norm_num))))
  have helim := equationTenA_quadraticElimination67
    ω θ (equationTenTraceOne67 hζ) (equationTenTraceTwo67 hζ)
    Ua Ub Uzero Xa Xb Xzero ha hb hzero
  rw [two_sub_equationTenTraceTwo67,
    two_sub_equationTenTraceOne67,
    equationTenTraceOne_sub_two67] at helim
  apply mul_left_cancel₀ hkappa0
  calc
    kappa hζ *
        ((equationTenTraceTwoUnit67 hζ * Ua : (𝓞 K)ˣ) * Xa ^ 67 +
          (-Ub : (𝓞 K)ˣ) * Xb ^ 67) =
        kappa hζ * (equationTenTraceTwoUnit67 hζ : 𝓞 K) *
            ((Ua : 𝓞 K) * Xa ^ 67) -
          kappa hζ * ((Ub : 𝓞 K) * Xb ^ 67) := by
            simp only [Units.val_mul, Units.val_neg]
            ring
    _ = kappa hζ * (equationTenTraceOneUnit67 hζ : 𝓞 K) *
          ((Uzero : 𝓞 K) * Xzero) := helim
    _ = kappa hζ *
        ((equationTenTraceOneUnit67 hζ * Uzero : (𝓞 K)ˣ) * Xzero) := by
          simp only [Units.val_mul]
          ring

omit [IsCyclotomicExtension {67} ℚ K] in
/-- Equation (10a) at `a = 1`, `b = 2` in the form in which it is
actually produced by the three historical equations: all three right-hand
sides still carry Vandiver's common ramified factor `κ`.

The quadratic elimination therefore contains two copies of `κ`, one from
the input equations and one from the coefficient differences.  Cancelling
the nonzero product `κ²` gives the same weighted three-term equation as in
`equationTenB_cyclotomicSimplification67`. -/
theorem equationTenB_commonKappa67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (ω θ Xa Xb Xzero : 𝓞 K) (Ua Ub Uzero : (𝓞 K)ˣ)
    (ha : ω ^ 2 + equationTenTraceOne67 hζ * (ω * θ) + θ ^ 2 =
      kappa hζ * (Ua * Xa ^ 67))
    (hb : ω ^ 2 + equationTenTraceTwo67 hζ * (ω * θ) + θ ^ 2 =
      kappa hζ * (Ub * Xb ^ 67))
    (hzero : ω ^ 2 + 2 * (ω * θ) + θ ^ 2 =
      kappa hζ * (Uzero * Xzero ^ 67)) :
    (equationTenTraceTwoUnit67 hζ * Ua : (𝓞 K)ˣ) * Xa ^ 67 +
        (-Ub : (𝓞 K)ˣ) * Xb ^ 67 =
      (equationTenTraceOneUnit67 hζ * Uzero : (𝓞 K)ˣ) *
        Xzero ^ 67 := by
  have hkappa0 : kappa hζ ≠ 0 := by
    rw [kappa_eq_kappaUnit67_mul_sq]
    exact mul_ne_zero (kappaUnit67 hζ).isUnit.ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr
        (hζ.unit'_coe.ne_one (by norm_num))))
  have ha' : ω ^ 2 + equationTenTraceOne67 hζ * (ω * θ) + θ ^ 2 =
      (kappa hζ * Ua) * Xa ^ 67 := by
    simpa only [mul_assoc] using ha
  have hb' : ω ^ 2 + equationTenTraceTwo67 hζ * (ω * θ) + θ ^ 2 =
      (kappa hζ * Ub) * Xb ^ 67 := by
    simpa only [mul_assoc] using hb
  have hzero' : ω ^ 2 + 2 * (ω * θ) + θ ^ 2 =
      (kappa hζ * Uzero) * Xzero ^ 67 := by
    simpa only [mul_assoc] using hzero
  have helim := equationTenA_quadraticElimination67
    ω θ (equationTenTraceOne67 hζ) (equationTenTraceTwo67 hζ)
    (kappa hζ * Ua) (kappa hζ * Ub) (kappa hζ * Uzero)
    Xa Xb (Xzero ^ 67) ha' hb' hzero'
  rw [two_sub_equationTenTraceTwo67,
    two_sub_equationTenTraceOne67,
    equationTenTraceOne_sub_two67] at helim
  apply mul_left_cancel₀ (mul_ne_zero hkappa0 hkappa0)
  calc
    kappa hζ * kappa hζ *
        ((equationTenTraceTwoUnit67 hζ * Ua : (𝓞 K)ˣ) * Xa ^ 67 +
          (-Ub : (𝓞 K)ˣ) * Xb ^ 67) =
        kappa hζ * (equationTenTraceTwoUnit67 hζ : 𝓞 K) *
            (kappa hζ * ((Ua : 𝓞 K) * Xa ^ 67)) -
          kappa hζ * (kappa hζ * ((Ub : 𝓞 K) * Xb ^ 67)) := by
            simp only [Units.val_mul, Units.val_neg]
            ring
    _ = kappa hζ * (equationTenTraceOneUnit67 hζ : 𝓞 K) *
          (kappa hζ * ((Uzero : 𝓞 K) * Xzero ^ 67)) := by
            simpa only [mul_assoc] using helim
    _ = kappa hζ * kappa hζ *
        ((equationTenTraceOneUnit67 hζ * Uzero : (𝓞 K)ˣ) *
          Xzero ^ 67) := by
            simp only [Units.val_mul]
            ring

/-- The actual finite support of the distinct prime-ideal factors of the
principal ideal `(x)`. -/
def primeIdealFactorSupport67 (x : 𝓞 K) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).toFinset

/-- The concrete output of Vandiver's ideal calculation through equation
(10a), before applying Lemma 2. It records the weighted Fermat equation,
the high-depth quotient-unit congruence, the real and coprimality invariants,
and the strict deletion of a prime-ideal factor from `ξ`.

The theorem below turns exactly this data into the abstract
`EquationSevenToTenData`; in particular, neither the Kummer conclusion nor
the rescaling to equation (10b) is assumed here. -/
structure WeightedReductionData67 {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ 134 ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ 67)
  weightedEquation :
    epsilon₁ * x ^ 67 + epsilon₂ * y ^ 67 =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ 67
  z_ne_zero : z ≠ 0
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_xz : IsCoprime x z
  real_x : NumberField.IsCMField.ringOfIntegersComplexConj K x = x
  real_y : NumberField.IsCMField.ringOfIntegersComplexConj K y = y
  real_z : NumberField.IsCMField.ringOfIntegersComplexConj K z = z
  real_eta : NumberField.IsCMField.unitsComplexConj K (epsilon₃ / epsilon₂) =
    epsilon₃ / epsilon₂
  factorSupport_strict : primeIdealFactorSupport67 z ⊂ primeIdealFactorSupport67 s.xi

/-- The output of Vandiver's elimination before its three principal
generators have been made literally real.

Compared with WeightedReductionData67, this structure asks for the exact
cyclotomic conjugation quotients of x, y, and z. The theorem
weightedReductionData_of_conjugationPowers67 below performs the explicit
ζ^(34*j) adjustment and proves that it preserves the weighted equation,
coprimality, nonvanishing, and the strict prime-support descent. -/
structure ConjugationPowerReductionData67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ 134 ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ 67)
  weightedEquation :
    epsilon₁ * x ^ 67 + epsilon₂ * y ^ 67 =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ 67
  z_ne_zero : z ≠ 0
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_xz : IsCoprime x z
  conjugationExponent_x : ℕ
  conjugationExponent_y : ℕ
  conjugationExponent_z : ℕ
  conjugation_x :
    NumberField.IsCMField.ringOfIntegersComplexConj K x =
      (hζ.unit' ^ conjugationExponent_x : (𝓞 K)ˣ) * x
  conjugation_y :
    NumberField.IsCMField.ringOfIntegersComplexConj K y =
      (hζ.unit' ^ conjugationExponent_y : (𝓞 K)ˣ) * y
  conjugation_z :
    NumberField.IsCMField.ringOfIntegersComplexConj K z =
      (hζ.unit' ^ conjugationExponent_z : (𝓞 K)ˣ) * z
  real_eta : NumberField.IsCMField.unitsComplexConj K (epsilon₃ / epsilon₂) =
    epsilon₃ / epsilon₂
  factorSupport_strict : primeIdealFactorSupport67 z ⊂ primeIdealFactorSupport67 s.xi

/-- Normalize all three weighted generators by the explicit half powers of
their conjugation quotients. Since those multipliers are 67th roots of
unity, every 67th power in Vandiver's equation is unchanged. -/
noncomputable def weightedReductionData_of_conjugationPowers67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) {s : HistoricalState hζ}
    (d : ConjugationPowerReductionData67 hζ s) :
    WeightedReductionData67 hζ s where
  x := realAdjustedGenerator67 hζ d.x d.conjugationExponent_x
  y := realAdjustedGenerator67 hζ d.y d.conjugationExponent_y
  z := realAdjustedGenerator67 hζ d.z d.conjugationExponent_z
  epsilon₁ := d.epsilon₁
  epsilon₂ := d.epsilon₂
  epsilon₃ := d.epsilon₃
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  weightedEquation := by
    simpa only [mul_pow, realAdjustedGenerator67_pow_sixtySeven] using
      d.weightedEquation
  z_ne_zero := by
    dsimp [realAdjustedGenerator67]
    exact mul_ne_zero
      (hζ.unit' ^ (realGeneratorHalfExponent67 *
        d.conjugationExponent_z)).isUnit.ne_zero d.z_ne_zero
  coprime_xy :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent67 * d.conjugationExponent_x)).isUnit
      d.x
      (realAdjustedGenerator67 hζ d.y d.conjugationExponent_y)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent67 * d.conjugationExponent_y)).isUnit
        d.x d.y).mpr d.coprime_xy)
  coprime_yz :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent67 * d.conjugationExponent_y)).isUnit
      d.y
      (realAdjustedGenerator67 hζ d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent67 * d.conjugationExponent_z)).isUnit
        d.y d.z).mpr d.coprime_yz)
  coprime_xz :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent67 * d.conjugationExponent_x)).isUnit
      d.x
      (realAdjustedGenerator67 hζ d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent67 * d.conjugationExponent_z)).isUnit
        d.x d.z).mpr d.coprime_xz)
  real_x :=
    realAdjustedGenerator67_real hζ d.x d.conjugationExponent_x d.conjugation_x
  real_y :=
    realAdjustedGenerator67_real hζ d.y d.conjugationExponent_y d.conjugation_y
  real_z :=
    realAdjustedGenerator67_real hζ d.z d.conjugationExponent_z d.conjugation_z
  real_eta := d.real_eta
  factorSupport_strict := by
    have hsupp :
        primeIdealFactorSupport67
            (realAdjustedGenerator67 hζ d.z d.conjugationExponent_z) =
          primeIdealFactorSupport67 d.z := by
      unfold primeIdealFactorSupport67
      rw [Ideal.span_singleton_eq_span_singleton.mpr
        (realAdjustedGenerator67_associated hζ d.z d.conjugationExponent_z)]
    rw [hsupp]
    exact d.factorSupport_strict

private noncomputable def adjustedRoot67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 67) : (𝓞 K)ˣ :=
  (exists_real_unit_root_67 hζ a v hv).choose

private lemma adjustedRoot67_pow {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 67) :
    a = adjustedRoot67 hζ a v hv ^ 67 :=
  (exists_real_unit_root_67 hζ a v hv).choose_spec.1

private lemma adjustedRoot67_real {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 67) :
    NumberField.IsCMField.unitsComplexConj K (adjustedRoot67 hζ a v hv) =
      adjustedRoot67 hζ a v hv :=
  (exists_real_unit_root_67 hζ a v hv).choose_spec.2

private noncomputable def weightedNextState67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) {s : HistoricalState hζ}
    (d : WeightedReductionData67 hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ 67) :
    HistoricalState hζ :=
  let w := adjustedRoot67 hζ (d.epsilon₁ / d.epsilon₂) v hv
  { omega := w * d.x
    theta := d.y
    xi := d.z
    eta := d.epsilon₃ / d.epsilon₂
    m := 2 * s.m - 1
    one_lt_m := by
      have hm := s.one_lt_m
      omega
    xi_ne_zero := d.z_ne_zero
    coprime_omega_theta :=
      (isCoprime_mul_unit_left_left w.isUnit d.x d.y).mpr d.coprime_xy
    coprime_theta_xi := d.coprime_yz
    coprime_omega_xi :=
      (isCoprime_mul_unit_left_left w.isUnit d.x d.z).mpr d.coprime_xz
    equation := by
      rw [mul_pow, ← Units.val_pow_eq_pow_val,
        ← adjustedRoot67_pow hζ (d.epsilon₁ / d.epsilon₂) v hv,
        ← mul_right_inj' d.epsilon₂.isUnit.ne_zero, mul_add, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel]
      exact d.weightedEquation }

private lemma weightedNextState67_admissible {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) {s : HistoricalState hζ}
    (d : WeightedReductionData67 hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ 67) :
    RealSourceAdmissible hζ (weightedNextState67 hζ d v hv) := by
  let w := adjustedRoot67 hζ (d.epsilon₁ / d.epsilon₂) v hv
  have hwUnits : NumberField.IsCMField.unitsComplexConj K w = w :=
    adjustedRoot67_real hζ (d.epsilon₁ / d.epsilon₂) v hv
  have hw : NumberField.IsCMField.ringOfIntegersComplexConj K (w : 𝓞 K) = w := by
    have := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hwUnits
    exact this
  refine ⟨?_, d.real_y, d.real_z, d.real_eta⟩
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((w : 𝓞 K) * d.x) = (w : 𝓞 K) * d.x
  rw [map_mul, hw, d.real_x]

/-- Equations (10) and (10a) imply the abstract historical reduction data.
The proof performs the nontrivial source step after Lemma 2: it normalizes a
`67`th root to be real, absorbs it into the first summand, divides out the
second coefficient unit, and verifies every invariant of equation (10b). -/
noncomputable def equationSevenToTenData_of_weighted67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) {s : HistoricalState hζ}
    (d : WeightedReductionData67 hζ s) :
    EquationSevenToTenData hζ (RealSourceAdmissible hζ) s where
  quotientUnit := d.epsilon₁ / d.epsilon₂
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  nextState := weightedNextState67 hζ d
  next_admissible := weightedNextState67_admissible hζ d
  next_exponent := by intros; rfl
  factorCount_decreases := by
    intro v hv
    exact Finset.card_lt_card d.factorSupport_strict

/-! ## The remaining real-ideal construction seam -/

/-- The source-faithful remainder of Vandiver's equations (7b)--(10a).

The 1929 proof does **not** assume the broad modern predicate
`RelevantIdealQuotientsPrincipal`.  In (7b), only the conjugation-symmetric
product `𝔦ₐ 𝔦₋ₐ` is used; it belongs to the maximal real field.  After
(9), the paper explicitly observes that the new quotient is unchanged by
the substitution `ζ ↦ ζ⁻¹`, so its ideal again belongs to the real field.
For each of these two ideals, `exists_real_unit_mul_pow_generator67`
already derives the required real generator from the unconditional theorem
`67 ∤ h⁺`.

What remains here is therefore to construct those two real ideals from a
historical state, verify their displayed 67th-power identities, and carry
out (7a)--(9a) plus the cyclotomic-unit simplification surrounding (10a).
The purely quadratic elimination in (10a) is separately proved by
`equationTenA_quadraticElimination67`.

This boundary is deliberately below the descent conclusion: the high local
congruence, weighted equation, exact conjugation quotients, coprimality, and
strict support inclusion are concrete fields.  Making the generators real,
preserving their equation and supports, the Kummer step, equation (10b),
and the infinite descent are proved outside this hypothesis. -/
def RealPrincipalGeneratorElimination67 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 67) : Prop :=
  ∀ s : HistoricalState hζ, RealSourceAdmissible hζ s →
    Nonempty (ConjugationPowerReductionData67 hζ s)

/-- The concrete real-generator elimination supplies the full historical
reduction relation required by the abstract well-founded descent. -/
theorem equationsSevenToTenReduction_67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (heliminate : RealPrincipalGeneratorElimination67 hζ) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) := by
  intro s hs
  exact (heliminate s hs).map fun d ↦
    equationSevenToTenData_of_weighted67 hζ
      (weightedReductionData_of_conjugationPowers67 hζ d)

/-- The exponent-`67` historical second case, conditional only on the exact
deep unit conclusion and the remaining source-faithful construction through
equation (10a).  No global principalization of CM ideal quotients is used. -/
theorem secondCaseExcluded_67_of_historical
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (heliminate : RealPrincipalGeneratorElimination67 hζ)
    (hkummer : KummerUnitPowerConclusion K 67) :
    Fermat.SecondCaseExcluded 67 :=
  secondCaseExcluded_of_historical_descent (by norm_num) hζ
    (RealSourceAdmissible hζ) (secondCaseStartsHistoricalDescent_67 hζ)
    (equationsSevenToTenReduction_67 hζ heliminate) hkummer

/-- Assemble the exact source statement of Vandiver's Lemma 2 with the
directly checked exponent-`67` Bernoulli cube data. No semiprimary deepening
hypothesis is used on this historical route. -/
theorem secondCaseExcluded_67_of_vandiverLemmaTwo
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (heliminate : RealPrincipalGeneratorElimination67 hζ)
    (hLemmaTwo : Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 67) :
    Fermat.SecondCaseExcluded 67 :=
  secondCaseExcluded_67_of_historical hζ heliminate
    (Fermat.Irregular.VandiverUnitLemma.kummerUnitPowerConclusion_of_lemmaTwo
      (by norm_num) hLemmaTwo
      Fermat.SixtySeven.VandiverData.bernoulliCubeCondition_sixtySeven)

end

end Fermat.SixtySeven.VandiverHistorical
