/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Dirichlet's exponent-five descents as gauge-invariant charge drains

The arithmetic in this file is reconstructed, with credit, from the
repository's earlier formalization of Dirichlet's proof.  This module does
not import or cite any declaration from that earlier `Fermat.Five` cone.

The two historical parity recurrences are packaged into one iterable state.
Its positive coordinate `s` is embedded as the rational integer `s` in the
golden order, so its charge is literally

`|N(s)| = s²`.

Dirichlet's strict coordinate decrease therefore becomes a strict decrease
of the gauge-invariant golden-ring charge.  The requested split on the
original Fermat right-hand base is retained semantically: each case state
carries its originating primitive solution and the exact proposition
`5 ∤ c` or `5 ∣ c`.  After the corresponding honest normalization, both
case tags are preserved by the iterable parity transformer and each branch
is closed directly by the shared conservation floor.
-/
import Fermat.Exponents.Five.Conservation.Initial

namespace Fermat.Five.Conservation

open Reconstruction.Dirichlet

/-- A primitive nonzero integral Fermat candidate, stored in its
golden-ring ledger form.  The ordinary fifth-power equation is recovered
from `quintic_ledger`. -/
structure PrimitiveFifthSolution where
  a : ℤ
  b : ℤ
  c : ℤ
  nonzero : a * b * c ≠ 0
  coprime_ab : IsCoprime a b
  coprime_ac : IsCoprime a c
  coprime_bc : IsCoprime b c
  ledger :
    (a + b) * goldenNorm (quinticCofactorElement a b) = c ^ 5

namespace PrimitiveFifthSolution

/-- The usual Fermat equation recovered from the conservation ledger. -/
theorem equation (solution : PrimitiveFifthSolution) :
    solution.a ^ 5 + solution.b ^ 5 = solution.c ^ 5 := by
  rw [quintic_ledger]
  exact solution.ledger

end PrimitiveFifthSolution

/-- The disjoint union of Dirichlet's two normalized parity states. -/
inductive ChargedState where
  | odd (h t s w : ℕ) (valid : OddState h t s w)
  | even (g h t s w : ℕ) (valid : EvenState g h t s w)

namespace ChargedState

/-- The positive historical coordinate decreased by both recurrences. -/
def coordinate : ChargedState → ℕ
  | .odd _ _ s _ _ => s
  | .even _ _ _ s _ _ => s

/-- The coordinate embedded as a rational integer in `ℤ[φ]`. -/
def chargeElement (state : ChargedState) : GoldenInt :=
  ((state.coordinate : ℤ) : GoldenInt)

/-- The literal absolute golden norm of the state's integer element. -/
def stateCharge (state : ChargedState) : ℕ :=
  goldenCharge state.chargeElement

/-- The historical coordinate in every normalized state is positive. -/
theorem coordinate_pos : ∀ state : ChargedState, 0 < state.coordinate
  | .odd _ _ _ _ valid => valid.s_pos
  | .even _ _ _ _ _ valid => valid.s_pos

/-- The literal golden-ring state charge is the square of the historical
coordinate. -/
@[simp] theorem stateCharge_eq_coordinate_sq (state : ChargedState) :
    state.stateCharge = state.coordinate ^ 2 := by
  change
    (Fermat.Quadratic.Golden.MaximalOrder.norm
      (((state.coordinate : ℤ) : GoldenInt))).natAbs =
        state.coordinate ^ 2
  rw [Fermat.Quadratic.Golden.MaximalOrder.norm_intCast]
  simp

/-- Every charged descent state lies strictly above the conservation floor. -/
theorem stateCharge_pos (state : ChargedState) :
    0 < state.stateCharge := by
  rw [stateCharge_eq_coordinate_sq]
  exact pow_pos state.coordinate_pos 2

/-- A charged state placed under one fixed path budget.  The state charge is
live stock; all charge already drained from that budget is converted. -/
def accountLedger (state : ChargedState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    Fermat.Conservation.Ledger ℕ :=
  Fermat.Five.Conservation.chargeLedger
    budget state.chargeElement hbudget

@[simp] theorem accountLedger_stock (state : ChargedState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).stock = state.stateCharge :=
  rfl

@[simp] theorem accountLedger_credit (state : ChargedState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).credit = 0 :=
  rfl

@[simp] theorem accountLedger_converted (state : ChargedState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).converted =
      budget - state.stateCharge :=
  rfl

@[simp] theorem accountLedger_total (state : ChargedState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).total = budget :=
  rfl

/-- A budget-preserving transaction between two charged states. -/
def accountTransfer (budget : ℕ) (before after : ChargedState)
    (hbefore : before.stateCharge ≤ budget)
    (hdrop : after.stateCharge ≤ before.stateCharge) :
    Fermat.Conservation.Transfer ℕ where
  before := before.accountLedger budget hbefore
  after := after.accountLedger budget (hdrop.trans hbefore)
  spent := before.stateCharge - after.stateCharge
  before_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  after_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  total_preserved := rfl
  available_decomposition := by
    simp only [accountLedger_stock, accountLedger_credit, add_zero]
    omega
  converted_decomposition := by
    simp only [accountLedger_converted]
    omega

/-- The old scalar charge equation is the stock projection of the accounted
state transition. -/
theorem accountTransfer_stock_decomposition (budget : ℕ)
    (before after : ChargedState)
    (hbefore : before.stateCharge ≤ budget)
    (hdrop : after.stateCharge ≤ before.stateCharge) :
    before.stateCharge = after.stateCharge +
      (accountTransfer budget before after hbefore hdrop).spent := by
  have hstock :=
    Fermat.Conservation.Transfer.stock_decomposition_of_credit_eq
      (accountTransfer budget before after hbefore hdrop) (by
          simp only [accountTransfer, accountLedger_credit])
  simpa only [accountTransfer, accountLedger_stock] using hstock

/-- The state-specific gauge normalization is the spine's zero-spent
full-column transaction at the state's own enclosing budget. -/
def gaugeTransfer (state : ChargedState) (u : GoldenIntˣ) :
    Fermat.Conservation.Transfer ℕ :=
  Fermat.Five.Conservation.gaugeTransfer
    state.stateCharge state.chargeElement u le_rfl

/-- State charge is invariant under every unit gauge transformation of the
infinite golden-ring unit group.  This scalar statement is the stock
projection of `gaugeTransfer`. -/
theorem charge_gauge_invariant (state : ChargedState) (u : GoldenIntˣ) :
    goldenCharge ((u : GoldenInt) * state.chargeElement) =
      state.stateCharge := by
  have havailable := (gaugeTransfer state u).available_eq
  have hstock : state.stateCharge =
      goldenCharge ((u : GoldenInt) * state.chargeElement) := by
    simpa only [gaugeTransfer, Fermat.Five.Conservation.gaugeTransfer,
      Fermat.Five.Conservation.chargeLedger,
      Fermat.Conservation.Transfer.available, stateCharge, add_zero]
      using havailable
  exact hstock.symm

/-- The primitive arithmetic output of the two reconstructed recurrences.
Charge strictness is intentionally not proved here. -/
private theorem charged_descent_coordinate (state : ChargedState) :
    ∃ next : ChargedState,
      next.coordinate < state.coordinate := by
  cases state with
  | odd h t s w valid =>
      obtain ⟨h', t', s', w', next, hlt⟩ := valid.descends
      exact ⟨.odd h' t' s' w' next, hlt⟩
  | even g h t s w valid =>
      obtain ⟨g', h', t', s', w', next, hlt⟩ := valid.descends
      exact ⟨.even g' h' t' s' w' next, hlt⟩

/-- Every charged state supplies a positive accounted transaction at any
fixed enclosing budget.  The primitive coordinate drop proves positivity;
the transaction carries the exact charge equality. -/
theorem charged_descent_transfer (state : ChargedState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    ∃ (next : ChargedState)
      (hdrop : next.stateCharge ≤ state.stateCharge),
      0 < (accountTransfer budget state next hbudget hdrop).spent := by
  obtain ⟨next, hcoordinate⟩ := state.charged_descent_coordinate
  have hcharge : next.stateCharge < state.stateCharge := by
    rw [stateCharge_eq_coordinate_sq, stateCharge_eq_coordinate_sq]
    exact Nat.pow_lt_pow_left hcoordinate (by norm_num)
  refine ⟨next, hcharge.le, ?_⟩
  change 0 < state.stateCharge - next.stateCharge
  exact Nat.sub_pos_of_lt hcharge

end ChargedState

/-- An iterable descent state originating in the case `5 ∤ c`. -/
structure NotFiveDvdCState where
  origin : PrimitiveFifthSolution
  c_not_five : ¬(5 : ℤ) ∣ origin.c
  current : ChargedState

namespace NotFiveDvdCState

/-- The golden-ring element carrying the current first-case charge. -/
def chargeElement (state : NotFiveDvdCState) : GoldenInt :=
  state.current.chargeElement

/-- The current first-case absolute norm charge. -/
def stateCharge (state : NotFiveDvdCState) : ℕ :=
  state.current.stateCharge

/-- The first-case wrapper uses the charged state's fixed-budget ledger.  Its
origin tag is preserved by the successor, but no absent origin/current
cross-equation is asserted. -/
def accountLedger (state : NotFiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    Fermat.Conservation.Ledger ℕ :=
  state.current.accountLedger budget hbudget

@[simp] theorem accountLedger_stock (state : NotFiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).stock = state.stateCharge :=
  rfl

@[simp] theorem accountLedger_credit (state : NotFiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).credit = 0 :=
  rfl

@[simp] theorem accountLedger_converted (state : NotFiveDvdCState)
    (budget : ℕ) (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).converted =
      budget - state.stateCharge :=
  rfl

@[simp] theorem accountLedger_total (state : NotFiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).total = budget :=
  rfl

/-- A fixed-budget transaction between two first-case states. -/
def accountTransfer (budget : ℕ)
    (before after : NotFiveDvdCState)
    (hbefore : before.stateCharge ≤ budget)
    (hdrop : after.stateCharge ≤ before.stateCharge) :
    Fermat.Conservation.Transfer ℕ :=
  ChargedState.accountTransfer budget before.current after.current
    hbefore hdrop

/-- Exact first-case spending, projected from its transaction. -/
theorem accountTransfer_stock_decomposition (budget : ℕ)
    (before after : NotFiveDvdCState)
    (hbefore : before.stateCharge ≤ budget)
    (hdrop : after.stateCharge ≤ before.stateCharge) :
    before.stateCharge = after.stateCharge +
      (accountTransfer budget before after hbefore hdrop).spent := by
  simpa only [stateCharge, accountTransfer] using
    ChargedState.accountTransfer_stock_decomposition
      budget before.current after.current hbefore hdrop

theorem stateCharge_pos (state : NotFiveDvdCState) :
    0 < state.stateCharge :=
  state.current.stateCharge_pos

/-- The first-case state charge survives every unit gauge transformation. -/
theorem charge_gauge_invariant
    (state : NotFiveDvdCState) (u : GoldenIntˣ) :
    goldenCharge ((u : GoldenInt) * state.chargeElement) =
      state.stateCharge :=
  state.current.charge_gauge_invariant u

end NotFiveDvdCState

/-- An iterable descent state originating in the case `5 ∣ c`. -/
structure FiveDvdCState where
  origin : PrimitiveFifthSolution
  c_five : (5 : ℤ) ∣ origin.c
  current : ChargedState

namespace FiveDvdCState

/-- The golden-ring element carrying the current second-case charge. -/
def chargeElement (state : FiveDvdCState) : GoldenInt :=
  state.current.chargeElement

/-- The current second-case absolute norm charge. -/
def stateCharge (state : FiveDvdCState) : ℕ :=
  state.current.stateCharge

/-- The second-case wrapper uses the charged state's fixed-budget ledger.
The origin divisibility tag is transported unchanged and is not conflated
with a nonexistent origin/current charge equality. -/
def accountLedger (state : FiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    Fermat.Conservation.Ledger ℕ :=
  state.current.accountLedger budget hbudget

@[simp] theorem accountLedger_stock (state : FiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).stock = state.stateCharge :=
  rfl

@[simp] theorem accountLedger_credit (state : FiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).credit = 0 :=
  rfl

@[simp] theorem accountLedger_converted (state : FiveDvdCState)
    (budget : ℕ) (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).converted =
      budget - state.stateCharge :=
  rfl

@[simp] theorem accountLedger_total (state : FiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    (state.accountLedger budget hbudget).total = budget :=
  rfl

/-- A fixed-budget transaction between two second-case states. -/
def accountTransfer (budget : ℕ)
    (before after : FiveDvdCState)
    (hbefore : before.stateCharge ≤ budget)
    (hdrop : after.stateCharge ≤ before.stateCharge) :
    Fermat.Conservation.Transfer ℕ :=
  ChargedState.accountTransfer budget before.current after.current
    hbefore hdrop

/-- Exact second-case spending, projected from its transaction. -/
theorem accountTransfer_stock_decomposition (budget : ℕ)
    (before after : FiveDvdCState)
    (hbefore : before.stateCharge ≤ budget)
    (hdrop : after.stateCharge ≤ before.stateCharge) :
    before.stateCharge = after.stateCharge +
      (accountTransfer budget before after hbefore hdrop).spent := by
  simpa only [stateCharge, accountTransfer] using
    ChargedState.accountTransfer_stock_decomposition
      budget before.current after.current hbefore hdrop

theorem stateCharge_pos (state : FiveDvdCState) :
    0 < state.stateCharge :=
  state.current.stateCharge_pos

/-- The second-case state charge survives every unit gauge transformation. -/
theorem charge_gauge_invariant
    (state : FiveDvdCState) (u : GoldenIntˣ) :
    goldenCharge ((u : GoldenInt) * state.chargeElement) =
      state.stateCharge :=
  state.current.charge_gauge_invariant u

end FiveDvdCState

private theorem chargedState_of_fifthEquation
    {x y z : ℤ} (equation : FifthEquation x y z) :
    Nonempty ChargedState := by
  rcases equation.exists_core with
    ⟨q, r, z₀, core⟩ | ⟨q, r, z₀, core⟩
  · obtain ⟨t, s, w, state⟩ := core.exists_oddState
    exact ⟨.odd 4 t s w state⟩
  · obtain ⟨t, s, w, state⟩ := core.exists_evenState
    exact ⟨.even 1 4 t s w state⟩

/-- Honest first-case seed: when `5 ∤ c`, the modulo-`25` entry forces one
of the two left bases to contain the ramified quantum, and the corresponding
signed permutation enters Dirichlet's generalized equation. -/
theorem not_five_dvd_c_seed
    (origin : PrimitiveFifthSolution)
    (hc : ¬(5 : ℤ) ∣ origin.c) :
    Nonempty NotFiveDvdCState := by
  obtain ⟨x, y, z, equation⟩ :=
    exists_fifthEquation_of_pairwise_of_not_five_dvd_right
      origin.nonzero origin.coprime_ac origin.coprime_bc
      origin.equation hc
  obtain ⟨current⟩ := chargedState_of_fifthEquation equation
  exact ⟨⟨origin, hc, current⟩⟩

/-- Honest second-case seed: when `5 ∣ c`, divide that visible factor from
the right-hand base and enter Dirichlet's generalized equation directly. -/
theorem five_dvd_c_seed
    (origin : PrimitiveFifthSolution)
    (hc : (5 : ℤ) ∣ origin.c) :
    Nonempty FiveDvdCState := by
  obtain ⟨z, equation⟩ :=
    exists_fifthEquation_of_pairwise_of_five_dvd_right
      origin.nonzero origin.coprime_ab origin.equation hc
  obtain ⟨current⟩ := chargedState_of_fifthEquation equation
  exact ⟨⟨origin, hc, current⟩⟩

/-- The `5 ∤ c` branch supplies a positive accounted transaction at every
fixed enclosing budget. -/
theorem not_five_dvd_c_charged_transfer
    (state : NotFiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    ∃ (next : NotFiveDvdCState)
      (hdrop : next.stateCharge ≤ state.stateCharge),
      0 < (NotFiveDvdCState.accountTransfer
        budget state next hbudget hdrop).spent := by
  obtain ⟨current, hdrop, hspent⟩ :=
    state.current.charged_descent_transfer budget hbudget
  let next : NotFiveDvdCState :=
    ⟨state.origin, state.c_not_five, current⟩
  refine ⟨next, hdrop, ?_⟩
  simpa only [next, NotFiveDvdCState.accountTransfer] using hspent

/-- The legacy first-case strict drain is the stock projection of its
positive `Transfer`. -/
theorem not_five_dvd_c_charged_descent
    (state : NotFiveDvdCState) :
    ∃ next : NotFiveDvdCState,
      next.stateCharge < state.stateCharge := by
  obtain ⟨next, hdrop, hspent⟩ :=
    not_five_dvd_c_charged_transfer
      state state.stateCharge le_rfl
  refine ⟨next, ?_⟩
  rw [NotFiveDvdCState.accountTransfer_stock_decomposition
    state.stateCharge state next le_rfl hdrop]
  exact Nat.lt_add_of_pos_right hspent

/-- The `5 ∣ c` branch supplies a positive accounted transaction at every
fixed enclosing budget. -/
theorem five_dvd_c_charged_transfer
    (state : FiveDvdCState) (budget : ℕ)
    (hbudget : state.stateCharge ≤ budget) :
    ∃ (next : FiveDvdCState)
      (hdrop : next.stateCharge ≤ state.stateCharge),
      0 < (FiveDvdCState.accountTransfer
        budget state next hbudget hdrop).spent := by
  obtain ⟨current, hdrop, hspent⟩ :=
    state.current.charged_descent_transfer budget hbudget
  let next : FiveDvdCState :=
    ⟨state.origin, state.c_five, current⟩
  refine ⟨next, hdrop, ?_⟩
  simpa only [next, FiveDvdCState.accountTransfer] using hspent

/-- The legacy second-case strict drain is the stock projection of its
positive `Transfer`. -/
theorem five_dvd_c_charged_descent
    (state : FiveDvdCState) :
    ∃ next : FiveDvdCState,
      next.stateCharge < state.stateCharge := by
  obtain ⟨next, hdrop, hspent⟩ :=
    five_dvd_c_charged_transfer
      state state.stateCharge le_rfl
  refine ⟨next, ?_⟩
  rw [FiveDvdCState.accountTransfer_stock_decomposition
    state.stateCharge state next le_rfl hdrop]
  exact Nat.lt_add_of_pos_right hspent

/-- The case `5 ∤ c` is impossible by its charged descent and the shared
conservation floor. -/
theorem not_five_dvd_c_impossible
    (origin : PrimitiveFifthSolution)
    (hc : ¬(5 : ℤ) ∣ origin.c) :
    False := by
  obtain ⟨start⟩ := not_five_dvd_c_seed origin hc
  exact
    Fermat.Conservation.impossible_of_strict_charge_drain
      start
      NotFiveDvdCState.stateCharge
      NotFiveDvdCState.stateCharge_pos
      not_five_dvd_c_charged_descent

/-- The case `5 ∣ c` is impossible by its charged descent and the shared
conservation floor. -/
theorem five_dvd_c_impossible
    (origin : PrimitiveFifthSolution)
    (hc : (5 : ℤ) ∣ origin.c) :
    False := by
  obtain ⟨start⟩ := five_dvd_c_seed origin hc
  exact
    Fermat.Conservation.impossible_of_strict_charge_drain
      start
      FiveDvdCState.stateCharge
      FiveDvdCState.stateCharge_pos
      five_dvd_c_charged_descent

end Fermat.Five.Conservation
