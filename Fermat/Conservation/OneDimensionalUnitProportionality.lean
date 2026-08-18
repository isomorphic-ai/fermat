/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Unit proportionality inside a one-dimensional line

This file isolates the pure linear-algebra steps used after arithmetic
objects have been proved to occupy a one-dimensional line.  It neither
constructs that line nor proves arithmetic membership or nonvanishing.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Fermat.Conservation

universe uK uV

variable {k : Type uK} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]

/-- Two nonzero vectors in the same one-dimensional submodule differ by a
unique unit scalar.

The nonvanishing assumptions have distinct jobs: `hpsi_ne` makes the scalar
unique, while `hphi_ne` proves that the scalar supplied by
one-dimensionality is a unit.  No finite-dimensionality assumption on the
ambient module is needed. -/
theorem existsUnique_unit_smul_of_mem_finrank_one
    (line : Submodule k V) (phi psi : V)
    (hphi_mem : phi ∈ line) (hpsi_mem : psi ∈ line)
    (hline : Module.finrank k line = 1)
    (hphi_ne : phi ≠ 0) (hpsi_ne : psi ≠ 0) :
    ∃! u : kˣ, phi = (u : k) • psi := by
  let phiLine : line := ⟨phi, hphi_mem⟩
  let psiLine : line := ⟨psi, hpsi_mem⟩
  have hpsiLine_ne : psiLine ≠ 0 := by
    intro h
    apply hpsi_ne
    exact congrArg Subtype.val h
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hline hpsiLine_ne phiLine
  have hc_value : c • psi = phi := congrArg Subtype.val hc
  have hc_ne : c ≠ 0 := by
    intro hzero
    apply hphi_ne
    rw [hzero, zero_smul] at hc_value
    exact hc_value.symm
  let u : kˣ := Units.mk0 c hc_ne
  refine ⟨u, hc_value.symm, ?_⟩
  intro v hv
  have hsmul : ((u : k) - (v : k)) • psi = 0 := by
    rw [sub_smul, show (u : k) = c by rfl, hc_value, ← hv, sub_self]
  exact Units.ext
    (sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hpsi_ne)).symm

/-- A scalar readout which is nonzero on a one-dimensional line reflects
zero at every point of that line.

This is the pointwise form of the same rank-one principle used above.  It is
deliberately phrased for a submodule of an arbitrary ambient module: later
arithmetic code only has to prove that its selected class lies in the line,
that the line has dimension one, and that the readout does not vanish
identically on it. -/
theorem eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero
    (line : Submodule k V) (readout : V →ₗ[k] k)
    (hline : Module.finrank k line = 1)
    (hreadout : readout.comp line.subtype ≠ 0)
    {x : V} (hx : x ∈ line) (hzero : readout x = 0) :
    x = 0 := by
  have hexists : ∃ anchor : line, readout anchor.1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hreadout
    ext anchor
    exact h anchor
  obtain ⟨anchor, hanchor⟩ := hexists
  have hanchor_ne : anchor ≠ 0 := by
    intro h
    apply hanchor
    rw [h, Submodule.coe_zero, map_zero]
  let xLine : line := ⟨x, hx⟩
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hline hanchor_ne xLine
  have hc_value : c • anchor.1 = x := congrArg Subtype.val hc
  have hproduct : c * readout anchor.1 = 0 := by
    calc
      c * readout anchor.1 = readout (c • anchor.1) := by
        rw [map_smul, smul_eq_mul]
      _ = readout x := by rw [hc_value]
      _ = 0 := hzero
  have hc_zero : c = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right hanchor
  rw [hc_zero, zero_smul] at hc_value
  exact hc_value.symm

end Fermat.Conservation
