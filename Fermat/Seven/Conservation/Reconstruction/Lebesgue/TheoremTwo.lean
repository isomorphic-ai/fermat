import Fermat.Seven.Conservation.Reconstruction.Lebesgue.FinalCoprimality
import Fermat.Seven.Conservation.Reconstruction.Lebesgue.FinalSubstitution
import Fermat.Seven.Conservation.Reconstruction.Lebesgue.PowerAllocation
import Fermat.Seven.Conservation.Reconstruction.Lebesgue.Primitive
import Fermat.Seven.Conservation.Reconstruction.Lebesgue.Reduction
import Fermat.Seven.Conservation.Spine

/-
Reconstruction provenance: adapted with credit from the repository's earlier
Lebesgue assembly in `Fermat/Seven/Lebesgue/TheoremTwo.lean`.  This module does
not import or call any declaration from that earlier exponent-seven route.
-/

/-!
# Lebesgue's Theorem II for exponent seven

This file joins the pieces of Lebesgue's 1840 proof.  A primitive ternary
solution gives the coprime product equation `s ^ 7 = 7 * v * t`.  The power
allocation produces the four equations on p. 279, the final substitution
turns them into the family of Theorem I, and the corrected descent rules out
that family.
-/

namespace Fermat.Seven.Conservation.Reconstruction.Lebesgue

private theorem even_v_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) : Even (v x y z) := by
  rcases exactly_one_even_of_ternary hxy hxz hyz heq with
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hyzEven : Even (y + z) := hy.add_odd hz
    simpa only [v] using hyzEven.mul_left ((x + y) * (x + z))
  · have hxzEven : Even (x + z) := hx.add_odd hz
    exact (hxzEven.mul_left (x + y)).mul_right (y + z)
  · have hxyEven : Even (x + y) := hx.add_odd hy
    exact (hxyEven.mul_right (x + z)).mul_right (y + z)

/-! ## The exceptional-prime branch -/

/-- The exact allocation data carried by the branch `7 ∣ T`.  It retains
the symmetric definition, the seventh-power product, both coprimalities,
the modulo-four sign, nonnegativity, and the exceptional divisibility
itself. -/
structure SevenDvdTBranchState where
  S : ℤ
  U : ℤ
  V : ℤ
  T : ℤ
  W : ℤ
  definition : T = U ^ 2 + W * S
  power : S ^ 7 = 7 * V * T
  coprime_TW : IsCoprime T W
  coprime_TV : IsCoprime T V
  mod_four : T ≡ 1 [ZMOD 4]
  nonnegative : 0 ≤ T
  seven_dvd : (7 : ℤ) ∣ T

namespace SevenDvdTBranchState

/-- The exceptional allocation is locally contradictory: `7T` would have
to be a square while its residue modulo four is three. -/
theorem allocation_contradiction
    (state : SevenDvdTBranchState) : False :=
  (not_seven_dvd_of_lebesgue_power_data
    state.definition state.power state.coprime_TW state.coprime_TV
      state.mod_four state.nonnegative) state.seven_dvd

noncomputable section

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {7} ℚ K]
variable {ζ : K}

/-- The exceptional branch carries one literal ramified quantum `λ¹`. -/
def chargeElement (hζ : IsPrimitiveRoot ζ 7)
    (_state : SevenDvdTBranchState) : 𝓞 K :=
  (Fermat.Seven.Conservation.lambda hζ) ^ 1

/-- The exceptional branch's absolute cyclotomic norm charge. -/
def stateCharge (hζ : IsPrimitiveRoot ζ 7)
    (state : SevenDvdTBranchState) : ℕ :=
  Fermat.Seven.Conservation.charge (chargeElement hζ state)

/-- The exceptional branch carries exactly one quantum of charge. -/
theorem stateCharge_eq (hζ : IsPrimitiveRoot ζ 7)
    (state : SevenDvdTBranchState) :
    stateCharge hζ state = 7 := by
  rw [stateCharge, chargeElement, pow_one,
    Fermat.Seven.Conservation.lambda_charge]

/-- The exceptional branch lies strictly above the conservation floor. -/
theorem stateCharge_pos (hζ : IsPrimitiveRoot ζ 7)
    (state : SevenDvdTBranchState) :
    0 < stateCharge hζ state := by
  rw [stateCharge_eq]
  norm_num

/-- **Rank-two gauge invariance for the exceptional branch.** Both free
Dirichlet coordinates may renormalize `λ¹` without changing its charge. -/
theorem stateCharge_rankTwoGauge_invariant
    (hζ : IsPrimitiveRoot ζ 7) (coordinates : ℤ × ℤ)
    (state : SevenDvdTBranchState) :
    Fermat.Seven.Conservation.charge
        (((Fermat.Seven.Conservation.gaugeUnit K
            ((Fermat.Seven.Conservation.gaugeCoordinatesEquiv (K := K)).symm
              coordinates) : (𝓞 K)ˣ) : 𝓞 K) *
          chargeElement hζ state) =
      stateCharge hζ state := by
  simpa only [stateCharge] using
    Fermat.Seven.Conservation.charge_gauge_invariant
      ((Fermat.Seven.Conservation.gaugeCoordinatesEquiv (K := K)).symm
        coordinates)
      (chargeElement hζ state)

omit [NumberField K] [IsCyclotomicExtension {7} ℚ K] in
/-- The exact exceptional allocation contradiction supplies its impossible
strict successor obligation. -/
theorem exists_stateCharge_lt (hζ : IsPrimitiveRoot ζ 7)
    (state : SevenDvdTBranchState) :
    ∃ next : SevenDvdTBranchState,
      stateCharge hζ next < stateCharge hζ state :=
  state.allocation_contradiction.elim

set_option backward.isDefEq.respectTransparency false in
/-- The named `7 ∣ T` branch closes through the shared conservation floor
using its literal, gauge-invariant `λ¹` charge. -/
theorem impossible_conservation
    (state : SevenDvdTBranchState) : False := by
  classical
  let K := CyclotomicField 7 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 7 ℚ K
  have : NumberField K :=
    IsCyclotomicExtension.numberField {7} ℚ _
  exact
    Fermat.Conservation.impossible_of_strict_charge_drain
      state
      (stateCharge hζ)
      (stateCharge_pos hζ)
      (exists_stateCharge_lt hζ)

end

end SevenDvdTBranchState

/-! ## The two exact branch closures -/

/-- The exceptional `7 ∣ t` branch, entered from the septic ledger and
closed by its concrete `λ¹`-charged state at the shared floor. -/
theorem seven_dvd_t_branch_impossible
    {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z)
    (hyz : IsCoprime y z)
    (hledger :
      (x + y) * Fermat.Seven.Conservation.psiSeven x (-y) + z ^ 7 = 0)
    (hseven : (7 : ℤ) ∣ t x y z) : False := by
  have heq : x ^ 7 + y ^ 7 + z ^ 7 = 0 := by
    rw [Fermat.Seven.Conservation.septic_ledger]
    exact hledger
  have hpow := s_pow_seven_eq_seven_mul_v_t_of_ternary heq
  have htxyz := isCoprime_t_xyz_of_ternary hxy hxz hyz heq
  have htv := isCoprime_t_v_of_ternary hxy hxz hyz heq
  have htmod := t_modEq_one_mod_four_of_ternary hxy hxz hyz heq
  let state : SevenDvdTBranchState :=
    { S := s x y z
      U := u x y z
      V := v x y z
      T := t x y z
      W := x * y * z
      definition := rfl
      power := hpow
      coprime_TW := htxyz
      coprime_TV := htv
      mod_four := htmod
      nonnegative := t_nonneg x y z
      seven_dvd := hseven }
  exact state.impossible_conservation

/-- The ordinary `7 ∤ t` branch consumes that exact case hypothesis,
constructs the repaired Lebesgue state, and drains its cyclotomic norm
charge through the shared conservation floor. -/
theorem not_seven_dvd_t_branch_impossible
    {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z)
    (hyz : IsCoprime y z)
    (hledger :
      (x + y) * Fermat.Seven.Conservation.psiSeven x (-y) + z ^ 7 = 0)
    (hxyz : x * y * z ≠ 0)
    (hnotseven : ¬(7 : ℤ) ∣ t x y z) : False := by
  have heq : x ^ 7 + y ^ 7 + z ^ 7 = 0 := by
    rw [Fermat.Seven.Conservation.septic_ledger]
    exact hledger
  have hpow := s_pow_seven_eq_seven_mul_v_t_of_ternary heq
  have htxyz := isCoprime_t_xyz_of_ternary hxy hxz hyz heq
  have htv := isCoprime_t_v_of_ternary hxy hxz hyz heq
  have htmod := t_modEq_one_mod_four_of_ternary hxy hxz hyz heq
  have hveven := even_v_of_ternary hxy hxz hyz heq
  obtain ⟨p, q, r, htq, hur, hvp, hspq, hpEven, hpq, hpr, hqr⟩ :=
    exists_pairwise_power_data_of_symmetric_of_not_seven_dvd
      hxy hxz hpow htxyz htv htmod hnotseven hveven
  have huOdd := odd_u_of_ternary hxy hxz hyz heq
  rw [hur] at huOdd
  have hqOdd : Odd q := (Int.odd_mul.mp huOdd).1
  have hrOdd : Odd r := (Int.odd_mul.mp huOdd).2
  have hp0 : p ≠ 0 := p_ne_zero_of_ternary_v_data hxyz heq hvp
  obtain ⟨a, P, Q, R, ha, hPodd, hQodd, hRodd, hPQ, hPR, hQR, hdesc⟩ :=
    exists_descentEquation_of_power_data htq hur hvp hspq hpEven hp0
      hqOdd hrOdd hpq hpr hqr
  exact ChargedState.impossible_conservation
    { index := a
      p := P
      q := Q
      r := R
      index_pos := ha
      p_odd := hPodd
      q_odd := hQodd
      r_odd := hRodd
      pq_coprime := hPQ
      pr_coprime := hPR
      qr_coprime := hQR
      equation := hdesc }

/-- Lebesgue's Theorem II: every primitive signed solution has a zero entry.
The original ternary equation is first rewritten as the exact septic ledger,
then split at the exceptional prime. -/
theorem ternaryOnlyTrivial_lebesgue : TernaryOnlyTrivial := by
  intro x y z hxy hxz hyz heq
  by_contra hxyz
  have hledger :
      (x + y) * Fermat.Seven.Conservation.psiSeven x (-y) + z ^ 7 = 0 := by
    rw [← Fermat.Seven.Conservation.septic_ledger]
    exact heq
  by_cases hseven : (7 : ℤ) ∣ t x y z
  · exact seven_dvd_t_branch_impossible hxy hxz hyz hledger hseven
  · exact not_seven_dvd_t_branch_impossible
      hxy hxz hyz hledger hxyz hseven

/-- Fermat's Last Theorem for exponent seven, by Lebesgue's corrected 1840
proof. -/
theorem holdsAt_seven_lebesgue : Fermat.HoldsAt 7 :=
  holdsAt_seven_of_ternaryOnlyTrivial ternaryOnlyTrivial_lebesgue

end Fermat.Seven.Conservation.Reconstruction.Lebesgue
