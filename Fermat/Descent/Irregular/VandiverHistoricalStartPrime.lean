import Fermat.Descent.Irregular.VandiverHistoricalPrime

/-!
# Prime-generic start of Vandiver's historical descent

For an odd prime written `p = 2 * r + 1`, Vandiver's real uniformizer

`κ = (1 - ζ) * (1 - ζ⁻¹)`

satisfies `κ ^ r ~ p`.  This file uses that identity to turn a primitive
rational second-case solution into the initial real historical state with
exponent `m = r`.  The construction is independent of the later finite
principal-generator elimination.
-/

namespace Fermat.Irregular.VandiverHistoricalStartPrime

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Vandiver's real uniformizer `κ` is fixed by complex conjugation. -/
lemma ringOfIntegersComplexConj_kappa {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
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
  rw [Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ,
    inv_inv]
  ring

omit [NumberField.IsCMField K] in
/-- If `p = 2r + 1`, then `κ ^ r` is associated to the rational prime
`p`. -/
lemma kappa_pow_half_associated_prime {r : ℕ} (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Associated (kappa hζ ^ r) (p : 𝓞 K) := by
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
  have hkappaPow := hkappa.pow_pow (n := r)
  rw [← pow_mul] at hkappaPow
  have htwo : 2 * r = p - 1 := by omega
  rw [htwo] at hkappaPow
  exact hkappaPow.trans (associated_zeta_sub_one_pow_prime hζ)

/-- A primitive rational second-case solution supplies the initial state
of Vandiver's historical descent, uniformly for every prime
`p = 2 * r + 1 ≥ 5`. -/
theorem secondCaseStartsHistoricalDescent {r : ℕ}
    (hp5 : 5 ≤ p) (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    SecondCaseStartsHistoricalDescent hζ (RealSourceAdmissible hζ) := by
  intro x y z hgcd hz hz0 e
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpodd : Odd p :=
    (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hx : x ≠ 0 := by
    intro hx0
    have hyz : y = z :=
      hpodd.pow_injective (by simpa [hx0, hp0] using e)
    have hpone : (p : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hx0]
        exact dvd_zero _
      · rw [hyz]
        exact hz
      · exact hz
    apply (Fact.out : p.Prime).not_dvd_one
    exact_mod_cast hpone
  have hy : y ≠ 0 := by
    intro hy0
    have hxz : x = z :=
      hpodd.pow_injective (by simpa [hy0, hp0] using e)
    have hpone : (p : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hxz]
        exact hz
      · rw [hy0]
        exact dvd_zero _
      · exact hz
    apply (Fact.out : p.Prime).not_dvd_one
    exact_mod_cast hpone
  obtain ⟨hxy, hyz, hxz⟩ :=
    Fermat.pairwiseCoprime_of_primitive_solution
      hp0 hx hy hz0 hgcd e
  obtain ⟨t, rfl⟩ := hz
  have ht0 : t ≠ 0 := by
    intro ht
    apply hz0
    simp [ht]
  obtain ⟨u, hu⟩ := kappa_pow_half_associated_prime hr hζ
  have hkappa0 : kappa hζ ^ r ≠ 0 :=
    (kappa_pow_half_associated_prime hr hζ).ne_zero_iff.mpr
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have huReal :
      NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) = u := by
    have hconj := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hu
    simp only [map_mul, map_pow, ringOfIntegersComplexConj_kappa hζ,
      map_natCast] at hconj
    exact mul_left_cancel₀ hkappa0 (hconj.trans hu.symm)
  let ξ : 𝓞 K := (u : 𝓞 K) * (t : 𝓞 K)
  have hyt : IsCoprime (y : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hyz.intCast (R := 𝓞 K)
    rw [Int.cast_mul] at hcast
    exact hcast.of_mul_right_right
  have hxt : IsCoprime (x : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hxz.intCast (R := 𝓞 K)
    rw [Int.cast_mul] at hcast
    exact hcast.of_mul_right_right
  let s : HistoricalState hζ :=
    { omega := x
      theta := y
      xi := ξ
      eta := 1
      m := r
      one_lt_m := by omega
      xi_ne_zero := by
        dsimp [ξ]
        exact mul_ne_zero u.isUnit.ne_zero (Int.cast_ne_zero.mpr ht0)
      coprime_omega_theta := hxy.intCast
      coprime_theta_xi := by
        dsimp [ξ]
        exact
          (isCoprime_mul_unit_left_right u.isUnit
            (y : 𝓞 K) (t : 𝓞 K)).mpr hyt
      coprime_omega_xi := by
        dsimp [ξ]
        exact
          (isCoprime_mul_unit_left_right u.isUnit
            (x : 𝓞 K) (t : 𝓞 K)).mpr hxt
      equation := by
        simp only [Units.val_one, one_mul]
        calc
          (x : 𝓞 K) ^ p + (y : 𝓞 K) ^ p =
              (((p : ℤ) * t : ℤ) : 𝓞 K) ^ p := by
                exact_mod_cast e
          _ = ((p : 𝓞 K) * (t : 𝓞 K)) ^ p := by
                norm_num
          _ = (kappa hζ ^ r * ((u : 𝓞 K) * (t : 𝓞 K))) ^ p := by
                congr 1
                rw [← mul_assoc, hu]
          _ = (kappa hζ ^ r * ξ) ^ p := rfl }
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

end

end Fermat.Irregular.VandiverHistoricalStartPrime
