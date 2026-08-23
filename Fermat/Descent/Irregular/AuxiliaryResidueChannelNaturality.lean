import Fermat.Descent.Irregular.AuxiliaryResidueChannels

/-!
# Convention naturality for auxiliary residue channels

Changing the primitive root used to coordinate a `p`th-power residue symbol
rescales its additive logarithm by the inverse root exponent.  Translating
the cyclic embedding orbit multiplies a Fourier detector by the associated
character value.  Both factors are units, so neither convention changes the
detected zero locus.
-/

namespace Fermat.Irregular

noncomputable section

namespace CircularUnitResidues.Certificate

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- At fixed p and q, the symbol exponent is uniquely determined by
q - 1 = symbolExponent * p. -/
theorem symbolExponent_eq
    (C C' : CircularUnitResidues.Certificate p q) :
    C.symbolExponent = C'.symbolExponent := by
  apply Nat.mul_right_cancel (Fact.out : p.Prime).pos
  rw [← C.q_sub_one, ← C'.q_sub_one]

/-- The defining power-residue symbol is the chosen primitive root raised to
the canonical representative of its additive residue logarithm. -/
theorem pow_symbolExponent_eq_root_pow_residueLog_val
    (C : CircularUnitResidues.Certificate p q) (u : (ZMod q)ˣ) :
    (u : ZMod q) ^ C.symbolExponent =
      C.root ^ (C.residueLog (Additive.ofMul u)).val := by
  let y : Subgroup.zpowers C.rootUnit := C.powerToRootPowers u
  have hy :
      C.rootUnit_isPrimitive.zmodEquivZPowers
          (C.rootUnit_isPrimitive.zmodEquivZPowers.symm (Additive.ofMul y)) =
        Additive.ofMul y :=
    C.rootUnit_isPrimitive.zmodEquivZPowers.apply_symm_apply (Additive.ofMul y)
  have hcast :
      ((C.rootUnit_isPrimitive.zmodEquivZPowers.symm (Additive.ofMul y)).val :
          ZMod p) =
        C.rootUnit_isPrimitive.zmodEquivZPowers.symm (Additive.ofMul y) :=
    ZMod.natCast_zmod_val _
  rw [← hcast,
    C.rootUnit_isPrimitive.zmodEquivZPowers_apply_coe_nat] at hy
  have hyval := congrArg (fun z : Additive (Subgroup.zpowers C.rootUnit) ↦
    (((z.toMul : Subgroup.zpowers C.rootUnit) : (ZMod q)ˣ) : ZMod q)) hy
  change C.root ^
      (C.residueLog (Additive.ofMul u)).val =
    (u : ZMod q) ^ C.symbolExponent at hyval
  exact hyval.symm

/-- If the new primitive root is `root ^ a`, the old additive residue
coordinate is `a` times the new coordinate. -/
theorem residueLog_root_change
    (C C' : CircularUnitResidues.Certificate p q)
    (a : ℕ)
    (hroot : C'.root = C.root ^ a)
    (u : (ZMod q)ˣ) :
    C.residueLog (Additive.ofMul u) =
      (a : ZMod p) * C'.residueLog (Additive.ofMul u) := by
  let m := (C'.residueLog (Additive.ofMul u)).val
  have hpow' := pow_symbolExponent_eq_root_pow_residueLog_val C' u
  have hpow :
      (u : ZMod q) ^ C.symbolExponent = C.root ^ (a * m) := by
    rw [C.symbolExponent_eq C', hpow', hroot, pow_mul]
  rw [C.residueLog_eq_of_pow_eq u (a * m) hpow, Nat.cast_mul]
  exact congrArg (fun z : ZMod p ↦ (a : ZMod p) * z)
    (ZMod.natCast_zmod_val _)

/-- Coprimality makes the root-coordinate change an explicit nonzero
rescaling by `a⁻¹`. -/
theorem residueLog_root_change_eq_inv_mul
    (C C' : CircularUnitResidues.Certificate p q)
    (a : ℕ)
    (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (u : (ZMod q)ˣ) :
    C'.residueLog (Additive.ofMul u) =
      (a : ZMod p)⁻¹ * C.residueLog (Additive.ofMul u) := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp ha.symm
  rw [residueLog_root_change C C' a hroot u]
  calc
    C'.residueLog (Additive.ofMul u) =
        1 * C'.residueLog (Additive.ofMul u) := by rw [one_mul]
    _ = ((a : ZMod p)⁻¹ * a) *
        C'.residueLog (Additive.ofMul u) := by rw [inv_mul_cancel₀ ha0]
    _ = (a : ZMod p)⁻¹ *
        ((a : ZMod p) * C'.residueLog (Additive.ofMul u)) := by ring

/-- A primitive-root coordinate change does not alter whether the residue
logarithm vanishes. -/
theorem residueLog_root_change_eq_zero_iff
    (C C' : CircularUnitResidues.Certificate p q)
    (a : ℕ)
    (ha : a.Coprime p)
    (hroot : C'.root = C.root ^ a)
    (u : (ZMod q)ˣ) :
    C.residueLog (Additive.ofMul u) = 0 ↔
      C'.residueLog (Additive.ofMul u) = 0 := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp ha.symm
  rw [residueLog_root_change C C' a hroot u]
  exact mul_eq_zero.trans (by simp [ha0])

end CircularUnitResidues.Certificate

namespace CyclicDifferenceMatrix

open scoped BigOperators

variable {n : ℕ} [NeZero (n + 1)]
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Translating the phase around the cyclic embedding orbit multiplies its
Fourier coefficient by the corresponding inverse character value. -/
theorem fourierCoeff_translate (omega : R)
    (homega : IsPrimitiveRoot omega (n + 1))
    (f : Cyc n → R) (x : Cyc n) (frequency : Fin n) :
    fourierCoeff omega homega.pow_eq_one (fun y ↦ f (x + y)) frequency =
      fourierChar omega homega.pow_eq_one frequency (-x) *
        fourierCoeff omega homega.pow_eq_one f frequency := by
  exact sum_shift_mul_fourierChar omega homega f x frequency

/-- Every value of a Fourier character built from a primitive root is
nonzero. -/
theorem fourierChar_ne_zero (omega : R)
    (homega : IsPrimitiveRoot omega (n + 1))
    (frequency : Fin n) (x : Cyc n) :
    fourierChar omega homega.pow_eq_one frequency x ≠ 0 := by
  rw [fourierChar_apply]
  exact pow_ne_zero _ (homega.ne_zero (by omega))

/-- Translating the embedding orbit does not alter whether a Fourier
detector vanishes. -/
theorem fourierCoeff_translate_eq_zero_iff (omega : R)
    (homega : IsPrimitiveRoot omega (n + 1))
    (f : Cyc n → R) (x : Cyc n) (frequency : Fin n) :
    fourierCoeff omega homega.pow_eq_one (fun y ↦ f (x + y)) frequency = 0 ↔
      fourierCoeff omega homega.pow_eq_one f frequency = 0 := by
  rw [fourierCoeff_translate omega homega f x frequency]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hchar | hcoeff
    · exact (fourierChar_ne_zero omega homega frequency (-x) hchar).elim
    · exact hcoeff
  · intro hzero
    rw [hzero, mul_zero]

/-- A root-coordinate rescaling and an embedding-orbit translation combine
as the product of their two explicit convention scalars. -/
theorem fourierCoeff_scale_translate (omega : R)
    (homega : IsPrimitiveRoot omega (n + 1))
    (c : R) (f : Cyc n → R) (x : Cyc n) (frequency : Fin n) :
    fourierCoeff omega homega.pow_eq_one
        (fun y ↦ c * f (x + y)) frequency =
      c * fourierChar omega homega.pow_eq_one frequency (-x) *
        fourierCoeff omega homega.pow_eq_one f frequency := by
  rw [fourierCoeff]
  calc
    (∑ u : Cyc n,
        c * f (x + u) * fourierChar omega homega.pow_eq_one frequency u) =
        c * ∑ u : Cyc n,
          f (x + u) * fourierChar omega homega.pow_eq_one frequency u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = c *
        (fourierChar omega homega.pow_eq_one frequency (-x) *
          fourierCoeff omega homega.pow_eq_one f frequency) := by
      rw [sum_shift_mul_fourierChar omega homega f x frequency]
    _ = _ := by ring

/-- Combining a nonzero root-coordinate scalar with an orbit translation
does not alter whether a Fourier detector vanishes. -/
theorem fourierCoeff_scale_translate_eq_zero_iff (omega : R)
    (homega : IsPrimitiveRoot omega (n + 1))
    (c : R) (hc : c ≠ 0) (f : Cyc n → R) (x : Cyc n)
    (frequency : Fin n) :
    fourierCoeff omega homega.pow_eq_one
        (fun y ↦ c * f (x + y)) frequency = 0 ↔
      fourierCoeff omega homega.pow_eq_one f frequency = 0 := by
  rw [fourierCoeff_scale_translate omega homega c f x frequency]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hscale | hcoeff
    · rcases mul_eq_zero.mp hscale with hczero | hchar
      · exact (hc hczero).elim
      · exact (fourierChar_ne_zero omega homega frequency (-x) hchar).elim
    · exact hcoeff
  · intro hzero
    rw [hzero, mul_zero]

end CyclicDifferenceMatrix

end


end Fermat.Irregular
