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
import Fermat.Five.Conservation.Initial

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

/-- State charge is invariant under every unit gauge transformation of the
infinite golden-ring unit group. -/
theorem charge_gauge_invariant (state : ChargedState) (u : GoldenIntˣ) :
    goldenCharge ((u : GoldenInt) * state.chargeElement) =
      state.stateCharge := by
  simpa only [stateCharge] using
    Fermat.Five.Conservation.charge_gauge_invariant
      u state.chargeElement

/-- The two reconstructed parity recurrences as one internal strict charged
transformer. -/
private theorem charged_descent (state : ChargedState) :
    ∃ next : ChargedState,
      next.stateCharge < state.stateCharge := by
  cases state with
  | odd h t s w valid =>
      obtain ⟨h', t', s', w', next, hlt⟩ := valid.descends
      refine ⟨.odd h' t' s' w' next, ?_⟩
      rw [stateCharge_eq_coordinate_sq, stateCharge_eq_coordinate_sq]
      exact Nat.pow_lt_pow_left hlt (by norm_num)
  | even g h t s w valid =>
      obtain ⟨g', h', t', s', w', next, hlt⟩ := valid.descends
      refine ⟨.even g' h' t' s' w' next, ?_⟩
      rw [stateCharge_eq_coordinate_sq, stateCharge_eq_coordinate_sq]
      exact Nat.pow_lt_pow_left hlt (by norm_num)

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

/-- The `5 ∤ c` branch is an iterable strict drain of the gauge-invariant
golden norm charge. -/
theorem not_five_dvd_c_charged_descent
    (state : NotFiveDvdCState) :
    ∃ next : NotFiveDvdCState,
      next.stateCharge < state.stateCharge := by
  obtain ⟨current, hlt⟩ := state.current.charged_descent
  exact
    ⟨⟨state.origin, state.c_not_five, current⟩, hlt⟩

/-- The `5 ∣ c` branch is an iterable strict drain of the gauge-invariant
golden norm charge. -/
theorem five_dvd_c_charged_descent
    (state : FiveDvdCState) :
    ∃ next : FiveDvdCState,
      next.stateCharge < state.stateCharge := by
  obtain ⟨current, hlt⟩ := state.current.charged_descent
  exact
    ⟨⟨state.origin, state.c_five, current⟩, hlt⟩

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
