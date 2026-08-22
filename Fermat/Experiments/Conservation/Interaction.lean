/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Two-account interaction dynamics

The generous transfer `f = g * (A - B) / 2` preserves the common mode
`s = A + B` and multiplies the transverse mode `d = A - B` by `1 - g`.
The ordered, Archimedean layer below records the resulting flow bound.  It is
deliberately a statement about a positive ledger, not about a finite
quotient: the final mod-three theorem records why a quotient cannot carry the
energy argument.
-/
import Fermat.Experiments.Conservation.AreaTransfer
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Fermat.Conservation.Interaction

/-- Two accounts before or after one generous transfer. -/
@[ext] structure TwoAccount (R : Type*) where
  left : R
  right : R
deriving DecidableEq, Repr

namespace TwoAccount

variable {R : Type*}

/-- The conserved common mode. -/
def sum [Add R] (x : TwoAccount R) : R := x.left + x.right

/-- The transverse interaction mode. -/
def difference [Sub R] (x : TwoAccount R) : R := x.left - x.right

/-- Quadratic energy of the transverse mode. -/
def energy [Ring R] (x : TwoAccount R) : R := difference x ^ 2

/-- Exchange the two accounts. -/
def swap (x : TwoAccount R) : TwoAccount R := ⟨x.right, x.left⟩

@[simp] theorem swap_left (x : TwoAccount R) : x.swap.left = x.right := rfl

@[simp] theorem swap_right (x : TwoAccount R) : x.swap.right = x.left := rfl

@[simp] theorem swap_swap (x : TwoAccount R) : x.swap.swap = x := by
  cases x
  rfl

section Algebraic

variable [Field R] [NeZero (2 : R)]

/-- The amount sent from the left account to the right account. -/
def flow (g : R) (x : TwoAccount R) : R :=
  g * difference x / 2

/-- One generous two-account interaction. -/
def step (g : R) (x : TwoAccount R) : TwoAccount R :=
  ⟨x.left - flow g x, x.right + flow g x⟩

omit [NeZero (2 : R)] in
/-- A two-party interaction cannot change its common mode. -/
theorem sum_step (g : R) (x : TwoAccount R) :
    sum (step g x) = sum x := by
  simp only [sum, step]
  ring

/-- The exact one-step transverse law: `d ↦ (1 - g)d`. -/
theorem difference_step (g : R) (x : TwoAccount R) :
    difference (step g x) = (1 - g) * difference x := by
  simp only [difference, step, flow]
  field_simp
  ring

/-- Energy is multiplied by the square of the transverse multiplier. -/
theorem energy_step (g : R) (x : TwoAccount R) :
    energy (step g x) = (1 - g) ^ 2 * energy x := by
  rw [energy, difference_step, energy]
  ring

/-- The pure orbit, before any halt, ledger exit, or conversion. -/
def orbit (g : R) (x : TwoAccount R) : ℕ → TwoAccount R
  | 0 => x
  | n + 1 => step g (orbit g x n)

omit [NeZero (2 : R)] in
@[simp] theorem orbit_zero (g : R) (x : TwoAccount R) :
    orbit g x 0 = x := rfl

omit [NeZero (2 : R)] in
@[simp] theorem orbit_succ (g : R) (x : TwoAccount R) (n : ℕ) :
    orbit g x (n + 1) = step g (orbit g x n) := rfl

omit [NeZero (2 : R)] in
/-- Sum conservation along every finite pure orbit. -/
theorem sum_orbit (g : R) (x : TwoAccount R) (n : ℕ) :
    sum (orbit g x n) = sum x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbit_succ, sum_step, ih]

/-- Closed form of the transverse mode along the pure orbit. -/
theorem difference_orbit (g : R) (x : TwoAccount R) (n : ℕ) :
    difference (orbit g x n) = (1 - g) ^ n * difference x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [orbit_succ, difference_step, ih, pow_succ]
      ring

/-- Closed form of the energy along the pure orbit. -/
theorem energy_orbit (g : R) (x : TwoAccount R) (n : ℕ) :
    energy (orbit g x n) = (1 - g) ^ (2 * n) * energy x := by
  rw [energy, difference_orbit, energy]
  ring

/-- At critical gain two, one interaction is exactly the account swap. -/
theorem step_two_eq_swap (x : TwoAccount R) :
    step (2 : R) x = x.swap := by
  ext <;> simp only [step, flow, difference, swap]
  all_goals (field_simp; ring)

/-- The critical orbit closes after two interactions. -/
theorem critical_period_two (x : TwoAccount R) :
    step (2 : R) (step (2 : R) x) = x := by
  rw [step_two_eq_swap, step_two_eq_swap, swap_swap]

/-- Critical gain preserves transverse energy. -/
theorem critical_energy_invariant (x : TwoAccount R) :
    energy (step (2 : R) x) = energy x := by
  rw [energy_step]
  ring

/-- Away from the diagonal, the critical orbit is a genuine period-two
livelock rather than a fixed point. -/
theorem critical_livelock (x : TwoAccount R)
    (hd : difference x ≠ 0) :
    step (2 : R) x ≠ x ∧ step (2 : R) (step (2 : R) x) = x ∧
      energy (step (2 : R) x) = energy x := by
  refine ⟨?_, critical_period_two x, critical_energy_invariant x⟩
  rw [step_two_eq_swap]
  intro h
  apply hd
  have hleft := congrArg TwoAccount.left h
  simp only [swap_left] at hleft
  exact sub_eq_zero.mpr hleft.symm

end Algebraic

section Ordered

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]

/-- Both accounts remain in the nonnegative ledger cone. -/
def PositiveLedger (x : TwoAccount R) : Prop :=
  0 ≤ x.left ∧ 0 ≤ x.right

omit [Archimedean R] in
/-- Positivity turns conservation of `s` into the flow bound `|d| ≤ s`. -/
theorem positive_difference_abs_le_sum {x : TwoAccount R}
    (hx : PositiveLedger x) :
    |difference x| ≤ sum x := by
  rw [abs_le]
  rcases hx with ⟨hleft, hright⟩
  constructor <;> simp only [difference, sum] <;> linarith

omit [Archimedean R] in
/-- The quadratic form of the positive-ledger flow bound. -/
theorem positive_energy_le_sum_sq {x : TwoAccount R}
    (hx : PositiveLedger x) :
    energy x ≤ sum x ^ 2 := by
  rcases hx with ⟨hleft, hright⟩
  simp only [energy, difference, sum]
  nlinarith [mul_nonneg hleft hright]

omit [Archimedean R] in
/-- A positive subcritical gain has multiplier of absolute value below one. -/
theorem damped_multiplier_abs_lt_one {g : R}
    (hg0 : 0 < g) (hg2 : g < 2) :
    |1 - g| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

omit [Archimedean R] in
/-- For a nonzero interaction mode, every positive gain below two strictly
damps the energy in one step. -/
theorem damped_energy_strict {g : R} {x : TwoAccount R}
    (hg0 : 0 < g) (hg2 : g < 2) (hd : difference x ≠ 0) :
    energy (step g x) < energy x := by
  rw [energy_step]
  have hfactor : (1 - g) ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one (1 - g)).2
      (damped_multiplier_abs_lt_one hg0 hg2)
  have henergy : 0 < energy x := by
    exact sq_pos_of_ne_zero hd
  simpa using mul_lt_mul_of_pos_right hfactor henergy

/-- A supercritical nonzero mode eventually exceeds every proposed bound.
This is the Archimedean step in the flow-bound theorem. -/
theorem supercritical_eventually_exceeds_bound {g : R} {x : TwoAccount R}
    (hg : 2 < g) (hd : difference x ≠ 0) (bound : R) :
    ∃ n : ℕ, bound < |difference (orbit g x n)| := by
  have hmult : 1 < |1 - g| := by
    rw [abs_of_neg (by linarith : 1 - g < 0)]
    linarith
  have hdpos : 0 < |difference x| := abs_pos.mpr hd
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (bound / |difference x|) hmult
  refine ⟨n, ?_⟩
  rw [difference_orbit, abs_mul, abs_pow]
  have hscaled := mul_lt_mul_of_pos_right hn hdpos
  calc
    bound = (bound / |difference x|) * |difference x| := by
      field_simp
    _ < |1 - g| ^ n * |difference x| := hscaled

/-- No nonzero supercritical pure orbit can remain difference-bounded for
all time. -/
theorem supercritical_impossible_forever_in_bounded_orbit
    {g : R} {x : TwoAccount R} (hg : 2 < g)
    (hd : difference x ≠ 0) (bound : R)
    (hbound : ∀ n : ℕ, |difference (orbit g x n)| ≤ bound) : False := by
  obtain ⟨n, hn⟩ := supercritical_eventually_exceeds_bound hg hd bound
  exact (not_lt_of_ge (hbound n)) hn

/-- In a positive ledger the conserved sum supplies the bound, so a
supercritical nonzero pure orbit must leave the ledger after finitely many
steps. -/
theorem supercritical_eventually_leaves_positive_ledger
    {g : R} {x : TwoAccount R} (hg : 2 < g)
    (hd : difference x ≠ 0) :
    ∃ n : ℕ, ¬ PositiveLedger (orbit g x n) := by
  obtain ⟨n, hn⟩ :=
    supercritical_eventually_exceeds_bound hg hd (sum x)
  refine ⟨n, ?_⟩
  intro hpositive
  have hflow := positive_difference_abs_le_sum hpositive
  rw [sum_orbit] at hflow
  exact (not_lt_of_ge hflow) hn

/-- The complete flow-bound trichotomy for a positive gain and a nonzero
interaction mode: damped, critical period-two, or finite positive-ledger
exit. -/
theorem flow_bound_trichotomy {g : R} {x : TwoAccount R}
    (hg0 : 0 < g) (hd : difference x ≠ 0) :
    (g < 2 ∧ energy (step g x) < energy x) ∨
      (g = 2 ∧ step g x = x.swap ∧ step g x ≠ x ∧
        step g (step g x) = x ∧ energy (step g x) = energy x) ∨
      (2 < g ∧ ∃ n : ℕ, ¬ PositiveLedger (orbit g x n)) := by
  rcases lt_trichotomy g 2 with hg2 | hg2 | hg2
  · exact Or.inl ⟨hg2, damped_energy_strict hg0 hg2 hd⟩
  · subst g
    have hlivelock := critical_livelock x hd
    exact Or.inr (Or.inl
      ⟨rfl, step_two_eq_swap x, hlivelock.1, hlivelock.2.1,
        hlivelock.2.2⟩)
  · exact Or.inr (Or.inr
      ⟨hg2, supercritical_eventually_leaves_positive_ledger hg2 hd⟩)

/-! ## Operational exit trilemma -/

/-- The external controller stops after an active interaction time. -/
def HaltsAt (active : ℕ → Prop) (n : ℕ) : Prop :=
  active n ∧ ¬ active (n + 1)

/-- The reported state has left the positive two-account ledger. -/
def LeavesPositiveLedgerAt (trajectory : ℕ → TwoAccount R)
    (n : ℕ) : Prop :=
  ¬ PositiveLedger (trajectory n)

/-- The next reported state uses an interaction other than the pure
two-account flow, so some external conversion has occurred. -/
def ConvertsAt (g : R) (trajectory : ℕ → TwoAccount R)
    (n : ℕ) : Prop :=
  trajectory (n + 1) ≠ step g (trajectory n)

/-- A nonzero supercritical process cannot stay active, positive, and purely
two-account forever: at some finite time it halts, leaves, or converts. -/
theorem exit_trilemma {g : R} {start : TwoAccount R}
    (trajectory : ℕ → TwoAccount R) (active : ℕ → Prop)
    (hstart : trajectory 0 = start) (hactive : active 0) (hg : 2 < g)
    (hd : difference start ≠ 0) :
    ∃ n : ℕ, HaltsAt active n ∨
      (active n ∧ LeavesPositiveLedgerAt trajectory n) ∨
      (active n ∧ ConvertsAt g trajectory n) := by
  by_contra hnone
  have hnoneAt : ∀ n : ℕ,
      ¬ (HaltsAt active n ∨
        (active n ∧ LeavesPositiveLedgerAt trajectory n) ∨
        (active n ∧ ConvertsAt g trajectory n)) := by
    intro n hn
    exact hnone ⟨n, hn⟩
  have hactiveAll (n : ℕ) : active n := by
    induction n with
    | zero => exact hactive
    | succ n ih =>
        by_contra hhalt
        exact hnoneAt n (Or.inl ⟨ih, hhalt⟩)
  have hpositive (n : ℕ) : PositiveLedger (trajectory n) := by
    by_contra hleave
    exact hnoneAt n (Or.inr (Or.inl ⟨hactiveAll n, hleave⟩))
  have hpure (n : ℕ) : trajectory (n + 1) = step g (trajectory n) := by
    by_contra hconvert
    exact hnoneAt n (Or.inr (Or.inr ⟨hactiveAll n, hconvert⟩))
  have horbit (n : ℕ) : trajectory n = orbit g start n := by
    induction n with
    | zero => exact hstart
    | succ n ih => rw [hpure n, ih, orbit_succ]
  obtain ⟨n, hn⟩ := supercritical_eventually_leaves_positive_ledger hg hd
  apply hn
  rw [← horbit n]
  exact hpositive n

end Ordered

/-! ## The critical swap as a closed `AreaTransfer` word -/

section Area

variable [CommRing R]

/-- View the two accounts as the two spendable columns of the existing
literal ledger. -/
def accountLedger (x : TwoAccount R) : Ledger R where
  stock := x.left
  credit := x.right
  converted := 0
  total := sum x
  conservation := by simp [sum]

/-- Swapping stock and credit is a zero-spent accounted transfer: the common
mode is unchanged and no amount is silently converted. -/
def swapTransfer (x : TwoAccount R) : Transfer R where
  before := accountLedger x
  after := accountLedger x.swap
  spent := 0
  before_conserved := Ledger.conservation_identity _
  after_conserved := Ledger.conservation_identity _
  total_preserved := by simp [accountLedger, sum, add_comm]
  available_decomposition := by simp [accountLedger, swap, add_comm]
  converted_decomposition := by simp [accountLedger]

/-- Canonical area lift of the critical swap.  Both the spent amount and the
chosen central word contribution are zero. -/
def criticalSwapAreaTransfer (x : TwoAccount R) (area : R) :
    AreaTransfer R R :=
  AreaTransfer.ofTransfer (swapTransfer x) area 0

/-- The critical swap is a closed Heisenberg word. -/
theorem criticalSwapAreaTransfer_word (x : TwoAccount R) (area : R) :
    (criticalSwapAreaTransfer x area).word = 1 := by
  change (⟨-0, 0, 0⟩ : Heis R) = Heis.identity
  simp [Heis.identity]

/-- Closedness is witnessed as payload invariance, not as erasure: the full
Heisenberg endpoint payload is unchanged by the critical swap. -/
theorem criticalSwapAreaTransfer_payload_invariant
    (x : TwoAccount R) (area : R) :
    (criticalSwapAreaTransfer x area).afterPayload =
      (criticalSwapAreaTransfer x area).beforePayload := by
  calc
    (criticalSwapAreaTransfer x area).afterPayload =
        (criticalSwapAreaTransfer x area).beforePayload *
          (criticalSwapAreaTransfer x area).word :=
      (criticalSwapAreaTransfer x area).payload_decomposition
    _ = (criticalSwapAreaTransfer x area).beforePayload * 1 := by
      rw [criticalSwapAreaTransfer_word]
    _ = (criticalSwapAreaTransfer x area).beforePayload := Heis.mul_one _

end Area

section AreaField

variable [Field R] [NeZero (2 : R)]

/-- The algebraic gain-two swap and its existing accounted-transfer lift
have exactly the same ledger endpoints, closed word, and invariant payload. -/
theorem critical_swap_is_closed_area_word (x : TwoAccount R) (area : R) :
    step (2 : R) x = x.swap ∧
      (criticalSwapAreaTransfer x area).before = accountLedger x ∧
      (criticalSwapAreaTransfer x area).after = accountLedger (step 2 x) ∧
      (criticalSwapAreaTransfer x area).word = 1 ∧
      (criticalSwapAreaTransfer x area).afterPayload =
        (criticalSwapAreaTransfer x area).beforePayload := by
  refine ⟨step_two_eq_swap x, rfl, ?_, criticalSwapAreaTransfer_word x area,
    criticalSwapAreaTransfer_payload_invariant x area⟩
  rw [step_two_eq_swap]
  rfl

end AreaField

/-! ## Quotient warning -/

/-- Before quotienting, gain three strictly increases the integer energy of
every nonzero difference. -/
theorem gain_three_integer_energy_strict {d : ℤ} (hd : d ≠ 0) :
    d ^ 2 < ((1 - (3 : ℤ)) * d) ^ 2 := by
  have henergy : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  norm_num
  nlinarith

/-- Gain three is supercritical over an ordered ledger (as witnessed by
`gain_three_integer_energy_strict`), but its multiplier `-2` becomes `1`
modulo three.  Thus the quotient fixes both the difference and its square and
has erased the energy growth needed by the flow bound. -/
theorem quotient_erases_energy_mod_three (d : ZMod 3) :
    ((1 - (3 : ZMod 3)) * d = d) ∧
      (((1 - (3 : ZMod 3)) * d) ^ 2 = d ^ 2) := by
  have hminusTwo : (-2 : ZMod 3) = 1 := by decide
  constructor
  · calc
      (1 - (3 : ZMod 3)) * d = (-2 : ZMod 3) * d := by norm_num
      _ = 1 * d := by rw [hminusTwo]
      _ = d := one_mul d
  · rw [show (1 - (3 : ZMod 3)) * d = d by
      calc
        (1 - (3 : ZMod 3)) * d = (-2 : ZMod 3) * d := by norm_num
        _ = 1 * d := by rw [hminusTwo]
        _ = d := one_mul d]

/-- The compiled warning in one statement: gain three grows every nonzero
integer mode, while the same update fixes every mode and its energy after
passing to `ZMod 3`.  A finite quotient therefore cannot serve as the bounded
positive carrier required by the flow-bound argument. -/
theorem quotient_erases_energy_warning :
    (∀ d : ℤ, d ≠ 0 → d ^ 2 < ((1 - (3 : ℤ)) * d) ^ 2) ∧
      (∀ d : ZMod 3,
        ((1 - (3 : ZMod 3)) * d = d) ∧
          (((1 - (3 : ZMod 3)) * d) ^ 2 = d ^ 2)) :=
  ⟨fun _ hd ↦ gain_three_integer_energy_strict hd,
    quotient_erases_energy_mod_three⟩

end TwoAccount

end Fermat.Conservation.Interaction
