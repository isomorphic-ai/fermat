/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Pythagoras, strictly as a conservation law

The theorem `a² + b² = c²` is proven here in its Noether form: the
Euclidean **charge** (squared norm) is the conserved quantity of the
orthogonal symmetry group, the inner product is the **coupling
channel** between components, and Pythagoras is the statement that
**when the coupling channel is empty, the charge ledger is exactly
additive**. No area dissection, no coordinates: only the ledger.

This is the exponent-2 rung of the Fermat ladder — the one exponent at
which the integer ledger balances (3² + 4² = 5²); Fermat's Last Theorem
is the statement that it never balances again.
-/
import Fermat.Conservation.Transfer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace Fermat.Two

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **charge**: the Noether invariant of the Euclidean symmetry
group — energy, squared length. -/
noncomputable def charge (v : V) : ℝ := ‖v‖ ^ 2

/-- The **coupling channel** between two vectors: the interference term
of the ledger. Empty coupling = no interaction = the "regular" case. -/
noncomputable def coupling (u v : V) : ℝ := inner ℝ u v

/-! ## The global three-column accounting adapter -/

/-- The Noether balance placed in the route-neutral global ledger.  The two
component charges are stock, the interaction term is credit, no amount has
yet been converted, and the charge of the sum is the audited total. -/
noncomputable def chargeLedger (u v : V) :
    Fermat.Conservation.Ledger ℝ where
  stock := charge u + charge v
  credit := 2 * coupling u v
  converted := 0
  total := charge (u + v)
  conservation := by
    simp only [charge, coupling, norm_add_sq_real, add_zero]
    ring

/-- **The ledger expansion.** The charge of a sum is the sum of charges
plus twice the coupling: bilinearity is the bookkeeping. Nothing is
created or destroyed; the cross term is exactly the coupling channel. -/
theorem charge_ledger (u v : V) :
    charge (u + v) = charge u + charge v + 2 * coupling u v := by
  have h :=
    Fermat.Conservation.Ledger.conservation_identity (chargeLedger u v)
  simpa only [chargeLedger, add_zero] using h.symm

/-- A linear isometry preserves the stock column component by component. -/
theorem chargeLedger_stock_isometry (R : V ≃ₗᵢ[ℝ] V) (u v : V) :
    (chargeLedger (R u) (R v)).stock = (chargeLedger u v).stock := by
  simp [chargeLedger, charge]

/-- A linear isometry preserves the coupling-credit column. -/
theorem chargeLedger_credit_isometry (R : V ≃ₗᵢ[ℝ] V) (u v : V) :
    (chargeLedger (R u) (R v)).credit = (chargeLedger u v).credit := by
  simp [chargeLedger, coupling, R.inner_map_map]

/-- A linear isometry preserves the converted column. -/
theorem chargeLedger_converted_isometry (R : V ≃ₗᵢ[ℝ] V) (u v : V) :
    (chargeLedger (R u) (R v)).converted =
      (chargeLedger u v).converted :=
  rfl

/-- A linear isometry preserves the total column. -/
theorem chargeLedger_total_isometry (R : V ≃ₗᵢ[ℝ] V) (u v : V) :
    (chargeLedger (R u) (R v)).total = (chargeLedger u v).total := by
  change ‖R u + R v‖ ^ 2 = ‖u + v‖ ^ 2
  rw [← R.map_add u v, R.norm_map]

/-- Orthogonal symmetry is a zero-spent accounted transfer: every column is
transported functorially, so no stock or credit is converted. -/
noncomputable def isometryTransfer (R : V ≃ₗᵢ[ℝ] V) (u v : V) :
    Fermat.Conservation.Transfer ℝ where
  before := chargeLedger (R u) (R v)
  after := chargeLedger u v
  spent := 0
  before_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  after_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  total_preserved := chargeLedger_total_isometry R u v
  available_decomposition := by
    rw [chargeLedger_stock_isometry, chargeLedger_credit_isometry]
    simp
  converted_decomposition := by
    rw [chargeLedger_converted_isometry]
    simp

/-- **Conservation.** The legacy scalar Noether statement is the total-column
projection of the zero-spent accounted transfer. -/
theorem charge_conserved (R : V ≃ₗᵢ[ℝ] V) (v : V) :
    charge (R v) = charge v := by
  simpa [isometryTransfer, chargeLedger] using
    (isometryTransfer R v 0).total_preserved

/-- Orthogonality is exactly the **empty coupling channel**. -/
def EmptyCoupling (u v : V) : Prop := coupling u v = 0

/-- **Pythagoras, as conservation.** When the coupling channel is
empty, the charge ledger is exactly additive: `c² = a² + b²`. The
hypotenuse vector is `u + v`; its charge equals the sum of the legs'
charges precisely because nothing flows through the (empty) channel. -/
theorem pythagoras {u v : V} (h : EmptyCoupling u v) :
    charge (u + v) = charge u + charge v := by
  rw [charge_ledger, h]
  ring

/-- The converse: additive ledger forces the empty channel. Pythagoras
characterizes orthogonality — the ledger detects coupling exactly. -/
theorem emptyCoupling_of_additive {u v : V}
    (h : charge (u + v) = charge u + charge v) :
    EmptyCoupling u v := by
  have hl := charge_ledger u v
  rw [h] at hl
  unfold EmptyCoupling
  linarith

/-- Conservation transports Pythagoras along the symmetry group: the
additive ledger holds in every rotated frame. (The theorem is a
property of the charge, not of a coordinate system.) -/
theorem pythagoras_conserved {u v : V} (h : EmptyCoupling u v)
    (R : V ≃ₗᵢ[ℝ] V) :
    charge (R u + R v) = charge (R u) + charge (R v) := by
  have : EmptyCoupling (R u) (R v) := by
    unfold EmptyCoupling coupling at h ⊢
    rw [R.inner_map_map u v]
    exact h
  exact pythagoras this

/-- The exponent-2 integer balance: the Fermat ledger closes at n = 2.
(FLT, proven per-exponent elsewhere in this repository, is the
statement that it never closes again.) -/
example : (3 : ℤ) ^ 2 + 4 ^ 2 = 5 ^ 2 := by norm_num

end Fermat.Two
