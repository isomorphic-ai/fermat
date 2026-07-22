import Fermat.Irregular.SinnottIndex
import Fermat.Irregular.CircularUnitFamily

/-!
# The regulator boundary for odd-prime circular units

For every odd prime p, equality between the relative index of the canonical
circular units and the plus class number is equivalent to one
regulator/residue identity.
-/

open scoped NumberField

namespace Fermat.Irregular.SinnottIndexPrime

noncomputable section

open NumberField NumberField.Units
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem prime_ne_two : p ≠ 2 := by
  have hpgt : 2 < p := Fact.out
  omega

/-- The circular-unit family transported to Dirichlet's unit-rank index. -/
def circularUnitRegFamily
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    Fin (NumberField.Units.rank K) → (𝓞 K)ˣ :=
  circularUnitFamily hzeta (prime_ne_two (p := p)) ∘
    finCongr (cyclotomicPrime_unitRank (K := K)
      (Fact.out : Nat.Prime p) (prime_ne_two (p := p)))

theorem range_circularUnitRegFamily
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    Set.range (circularUnitRegFamily hzeta) =
      Set.range (circularUnitFamily hzeta (prime_ne_two (p := p))) :=
  EquivLike.range_comp
    (circularUnitFamily hzeta (prime_ne_two (p := p)))
    (finCongr (cyclotomicPrime_unitRank (K := K)
      (Fact.out : Nat.Prime p) (prime_ne_two (p := p))))

theorem half_rank_succ :
    (p - 1) / 2 = (p - 3) / 2 + 1 := by
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two
    (Fact.out : Nat.Prime p) (prime_ne_two (p := p))
  obtain ⟨m, hm⟩ := hpodd
  have hpgt : 2 < p := Fact.out
  omega

/-- The maximal real subfield has half of the p minus one real places. -/
theorem nrRealPlaces_maximalRealSubfield :
    NumberField.InfinitePlace.nrRealPlaces K⁺ = (p - 1) / 2 := by
  have hrank :
      NumberField.Units.rank K⁺ = (p - 3) / 2 := by
    rw [NumberField.IsCMField.units_rank_eq_units_rank K,
      cyclotomicPrime_unitRank (K := K)
        (Fact.out : Nat.Prime p) (prime_ne_two (p := p))]
  have hpos : 0 < NumberField.InfinitePlace.nrRealPlaces K⁺ := by
    rw [← NumberField.IsTotallyReal.finrank]
    exact Module.finrank_pos
  rw [NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero] at hrank
  rw [half_rank_succ (p := p)]
  omega

/-- Dirichlet's class-number formula expressed through the canonical
circular-unit family. -/
theorem circularUnit_residue_index_identity
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    NumberField.dedekindZeta_residue K⁺ *
        ((2 : ℝ) ^ ((p - 3) / 2) *
          (realUnitRelIndex
            (circularUnitFamily hzeta (prime_ne_two (p := p))) : ℝ)) =
      (2 : ℝ) ^ ((p - 1) / 2) *
        NumberField.Units.regOfFamily (circularUnitRegFamily hzeta) *
        (NumberField.classNumber K⁺ : ℝ) /
        ((NumberField.Units.torsionOrder K⁺ : ℝ) *
          Real.sqrt |(NumberField.discr K⁺ : ℝ)|) := by
  have h := dedekindZeta_residue_mul_realUnitRelIndex
    (u := circularUnitRegFamily hzeta)
    (fun i ↦ circularUnitFamily_mem_realUnits hzeta
      (prime_ne_two (p := p)) _)
  simpa only [realUnitRelIndex, range_circularUnitRegFamily hzeta,
    cyclotomicPrime_unitRank (K := K)
      (Fact.out : Nat.Prime p) (prime_ne_two (p := p)),
    nrRealPlaces_maximalRealSubfield (p := p) (K := K)] using h

/-- Uniform Sinnott boundary for every odd prime. -/
theorem circularUnit_realIndex_eq_classNumber_iff
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    realUnitRelIndex
        (circularUnitFamily hzeta (prime_ne_two (p := p))) =
      NumberField.classNumber K⁺ ↔
    NumberField.dedekindZeta_residue K⁺ =
      NumberField.Units.regOfFamily (circularUnitRegFamily hzeta) /
        Real.sqrt |(NumberField.discr K⁺ : ℝ)| := by
  let I : ℕ := realUnitRelIndex
    (circularUnitFamily hzeta (prime_ne_two (p := p)))
  let H : ℕ := NumberField.classNumber K⁺
  let X : ℝ := NumberField.dedekindZeta_residue K⁺
  let Y : ℝ :=
    NumberField.Units.regOfFamily (circularUnitRegFamily hzeta) /
      Real.sqrt |(NumberField.discr K⁺ : ℝ)|
  let A : ℝ := (2 : ℝ) ^ ((p - 3) / 2)
  have hsqrt :
      Real.sqrt |(NumberField.discr K⁺ : ℝ)| ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos_of_pos
      (abs_pos.mpr (Int.cast_ne_zero.mpr
        (NumberField.discr_ne_zero K⁺))))
  have hA : A ≠ 0 := by
    dsimp only [A]
    positivity
  have hraw := circularUnit_residue_index_identity
    (p := p) (K := K) hzeta
  rw [torsionOrder_eq_two_of_isTotallyReal,
    half_rank_succ (p := p), pow_succ] at hraw
  have hright :
      A * 2 * NumberField.Units.regOfFamily
          (circularUnitRegFamily hzeta) * (H : ℝ) /
          (2 * Real.sqrt |(NumberField.discr K⁺ : ℝ)|) =
        A * (Y * (H : ℝ)) := by
    dsimp only [A, Y, H]
    field_simp
    <;> ring
  have hbalance : X * (I : ℝ) = Y * (H : ℝ) := by
    apply mul_left_cancel₀ hA
    calc
      A * (X * (I : ℝ)) =
          NumberField.dedekindZeta_residue K⁺ *
            (A * (I : ℝ)) := by
        simp only [X]
        ring
      _ = A * 2 * NumberField.Units.regOfFamily
            (circularUnitRegFamily hzeta) * (H : ℝ) /
            (2 * Real.sqrt |(NumberField.discr K⁺ : ℝ)|) := by
        simpa only [A, I, H] using hraw
      _ = A * (Y * (H : ℝ)) := hright
  have hX : X ≠ 0 := by
    exact NumberField.dedekindZeta_residue_ne_zero K⁺
  have hH : (H : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.classNumber_ne_zero K⁺
  constructor
  · intro hIH
    have hcast : (I : ℝ) = (H : ℝ) := by
      exact_mod_cast hIH
    have hXY : X = Y :=
      mul_right_cancel₀ hH (by simpa [hcast] using hbalance)
    simpa [X, Y] using hXY
  · intro hXY
    have hXY' : X = Y := by simpa [X, Y] using hXY
    have hcast : (I : ℝ) = (H : ℝ) := by
      apply mul_left_cancel₀ hX
      calc
        X * (I : ℝ) = Y * (H : ℝ) := hbalance
        _ = X * (H : ℝ) := by rw [hXY']
    exact_mod_cast hcast

end

end Fermat.Irregular.SinnottIndexPrime
