/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# N59 conservation structural verification

This non-imported executable audit leaf checks every theorem currently
exposed by the clean exponent-59 structural spine.  It also checks the
complete forbidden namespace prefixes, rather than relying only on
representative unused-name tests.

The final `Fermat.HoldsAt 59` theorem is not present here: `FINDINGS.md`
records the unconditional Kummer repayment and strict-successor theorem
which must be proved before that endpoint can be added honestly.
-/
import Fermat.FiftyNine.Conservation.Spine

/-! ## Three-column ledger -/

/--
info: 'Fermat.FiftyNine.Conservation.Ledger.repay_stock' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Ledger.repay_stock

/--
info: 'Fermat.FiftyNine.Conservation.Ledger.repay_credit' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Ledger.repay_credit

/--
info: 'Fermat.FiftyNine.Conservation.Ledger.repay_converted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Ledger.repay_converted

/--
info: 'Fermat.FiftyNine.Conservation.Ledger.repay_total' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Ledger.repay_total

/--
info: 'Fermat.FiftyNine.Conservation.Ledger.repayNat_credit' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Ledger.repayNat_credit

/--
info: 'Fermat.FiftyNine.Conservation.Ledger.repayNat_converted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Ledger.repayNat_converted

/--
info: 'Fermat.FiftyNine.Conservation.Ledger.repayNat_total' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Ledger.repayNat_total

/-! ## Rank-28 gauge and ramified drain -/

/--
info: 'Fermat.FiftyNine.Conservation.charge_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_mul

/--
info: 'Fermat.FiftyNine.Conservation.gauge_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.gauge_decomposition

/--
info: 'Fermat.FiftyNine.Conservation.charge_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_gauge_invariant

/--
info: 'Fermat.FiftyNine.Conservation.charge_full_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_full_gauge_invariant

/--
info: 'Fermat.FiftyNine.Conservation.unitRank_eq_twentyEight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.unitRank_eq_twentyEight

/--
info: 'Fermat.FiftyNine.Conservation.rankTwentyEightGauge_regulator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.rankTwentyEightGauge_regulator

/--
info: 'Fermat.FiftyNine.Conservation.lambda_eq_neg_zeta_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.lambda_eq_neg_zeta_sub_one

/--
info: 'Fermat.FiftyNine.Conservation.lambda_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.lambda_charge

/--
info: 'Fermat.FiftyNine.Conservation.charge_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_pow

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_eq

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_strictMono

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_step

/-! ## Shared conservation floor -/

/--
info: 'Fermat.Conservation.noInfinitePositiveChargeDrain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.noInfinitePositiveChargeDrain

/--
info: 'Fermat.Conservation.impossible_of_strict_charge_drain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.impossible_of_strict_charge_drain

/-! ## Exhaustive forbidden-prefix guards -/

open Lean Elab Command

/-- Fail if the imported environment contains any declaration below a
forbidden namespace or module prefix. -/
elab "#guard_no_decl_prefix " p:ident : command => do
  let env ← getEnv
  let forbiddenPrefix := p.getId
  let offenders :=
    env.constants.toList.filter fun entry =>
      forbiddenPrefix.isPrefixOf entry.1
  unless offenders.isEmpty do
    throwError
      "declarations with forbidden prefix {forbiddenPrefix}: {offenders.map Prod.fst}"

#guard_no_decl_prefix Fermat.FiftyNine.GenericProof
#guard_no_decl_prefix Fermat.FiftyNine.FirstCase
#guard_no_decl_prefix Fermat.FiftyNine.GenericSecondCase
#guard_no_decl_prefix Fermat.FiftyNine.Folding
#guard_no_decl_prefix Fermat.FiftyNine.GenericChannels
#guard_no_decl_prefix Fermat.FiftyNine.GenericLemmaTwo
#guard_no_decl_prefix Fermat.GenericIrregular
#guard_no_decl_prefix Fermat.Irregular
#guard_no_decl_prefix Fermat.Ladder

/-! The forbidden repository transport is a declaration rather than a
namespace, so it receives a direct unknown-constant guard. -/

/--
error: Unknown constant `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd

/-! Additional classical endpoints remain outside the cone as well. -/

/--
error: Unknown identifier `Fermat.FiftyNine.holdsAt_fiftyNine`
-/
#guard_msgs in
#check Fermat.FiftyNine.holdsAt_fiftyNine

/--
error: Unknown identifier `Fermat.KummerIso.ResidueRegressions.holdsAt_fiftyNine`
-/
#guard_msgs in
#check Fermat.KummerIso.ResidueRegressions.holdsAt_fiftyNine
