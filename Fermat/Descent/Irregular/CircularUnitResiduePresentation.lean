import Fermat.Descent.Irregular.AuxiliaryResidueChannels

open scoped Matrix

namespace Fermat.Irregular.AuxiliaryResidueChannels

noncomputable section

open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open KummerCriterion.CyclotomicUnits

/-- The additional p-only real-class coordinates needed to recover a cyclic
phase presentation from a bare finite-field residue certificate. -/
structure ArithmeticCoordinates (p : ℕ) [Fact p.Prime]
    (hp_three : 3 ≤ p) extends CharacterCoordinates p hp_three where
  row : Equiv.Perm (Fin (kummerLogRank p))
  classExponent : Cyc (kummerLogRank p) → ℕ
  classExponent_lt : ∀ r, classExponent r < p
  classExponent_ne_zero : ∀ r, classExponent r ≠ 0
  classExponent_add_sq : ∀ r s,
    ((classExponent (r + s) : ZMod p) ^ 2) =
      ((classExponent r : ZMod p) ^ 2) *
        ((generator ^ s.val) ^ 2)
  row_square : ∀ j : Fin (kummerLogRank p),
    ((classExponent (coord (kummerLogRank p) (row j)) : ZMod p) ^ 2) =
      (((j.val + 1 : ℕ) : ZMod p) ^ 2)

namespace AutomaticPresentation

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

noncomputable def symbolHalf (C : Certificate p q) : ℕ :=
  Classical.choose C.symbolExponent_even

theorem symbolExponent_eq_two_mul_symbolHalf (C : Certificate p q) :
    C.symbolExponent = 2 * symbolHalf C := by
  have h := Classical.choose_spec C.symbolExponent_even
  simpa [symbolHalf, two_mul] using h

abbrev weight (C : Certificate p q) (x : ZMod q) : ZMod q :=
  evenSymbolWeight (symbolHalf C) x

theorem normalized_pow_eq_weight_ratio (C : Certificate p q)
    (j i : Fin (kummerLogRank p)) :
    normalizedUnitValue C.root j i ^ C.symbolExponent =
      weight C (embeddingRoot C.root j ^ (i.val + 2)) /
        weight C (embeddingRoot C.root j) := by
  rw [symbolExponent_eq_two_mul_symbolHalf C]
  exact normalizedUnitValue_pow_two_mul_eq_weight_ratio
    C.hp2 C.root_isPrimitive j i

theorem weight_inv (C : Certificate p q) (x : ZMod q) (hx : x ≠ 0) :
    weight C x⁻¹ = weight C x :=
  evenSymbolWeight_inv x hx

variable {hp_three : 3 ≤ p}

def classRoot (C : Certificate p q) (X : ArithmeticCoordinates p hp_three)
    (r : Cyc (kummerLogRank p)) : ZMod q :=
  C.root ^ X.classExponent r

theorem classRoot_ne_zero (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    classRoot C X r ≠ 0 :=
  pow_ne_zero _ (C.root_isPrimitive.ne_zero (Fact.out : p.Prime).ne_zero)

theorem classRoot_ne_one (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    classRoot C X r ≠ 1 := by
  intro hone
  have hdvd : p ∣ X.classExponent r :=
    (C.root_isPrimitive.pow_eq_one_iff_dvd _).mp hone
  have heq : X.classExponent r = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd (X.classExponent_lt r)
  exact X.classExponent_ne_zero r heq

theorem classRoot_eq_pow_or_inv_of_sq (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p))
    (target : ℕ)
    (hsquare : ((X.classExponent r : ZMod p) ^ 2) =
      ((target : ℕ) : ZMod p) ^ 2) :
    classRoot C X r = C.root ^ target ∨
      classRoot C X r = (C.root ^ target)⁻¹ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hneg
  · have hmod : X.classExponent r ≡ target [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hsame
    exact Or.inl (pow_eq_pow_of_modEq hmod C.root_isPrimitive.pow_eq_one)
  · have hcast : ((X.classExponent r + target : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [hneg]
      simp
    have hmod : X.classExponent r + target ≡ 0 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa using hcast
    have hprod : classRoot C X r * C.root ^ target = 1 := by
      rw [classRoot, ← pow_add]
      simpa using pow_eq_pow_of_modEq hmod C.root_isPrimitive.pow_eq_one
    have htarget0 : C.root ^ target ≠ 0 :=
      pow_ne_zero _ (C.root_isPrimitive.ne_zero (Fact.out : p.Prime).ne_zero)
    exact Or.inr ((mul_eq_one_iff_eq_inv₀ htarget0).mp hprod)

theorem weight_classRoot_ne_zero (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    weight C (classRoot C X r) ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero _
      (sub_ne_zero.mpr (Ne.symm (classRoot_ne_one C X r)))
  · exact pow_ne_zero _ (classRoot_ne_zero C X r)

theorem weight_classRoot_pow_p_eq_one (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    weight C (classRoot C X r) ^ p = 1 := by
  let x := classRoot C X r
  have hxp : x ^ p = 1 := by
    dsimp [x, classRoot]
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      C.root_isPrimitive.pow_eq_one, one_pow]
  exact C.evenSymbolWeight_pow_eq_one
    (symbolExponent_eq_two_mul_symbolHalf C) x hxp (classRoot_ne_one C X r)

def weightUnit (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    (ZMod q)ˣ :=
  Units.mk0 (weight C (classRoot C X r)) (weight_classRoot_ne_zero C X r)

@[simp] theorem weightUnit_val (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    (weightUnit C X r : ZMod q) = weight C (classRoot C X r) := rfl

theorem weightUnit_pow_p_eq_one (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    weightUnit C X r ^ p = 1 := by
  apply Units.ext
  simpa using weight_classRoot_pow_p_eq_one C X r

def phaseUnit (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    (ZMod q)ˣ :=
  weightUnit C X r / weightUnit C X 0

theorem phaseUnit_pow_p_eq_one (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    phaseUnit C X r ^ p = 1 := by
  simp only [phaseUnit, div_pow, weightUnit_pow_p_eq_one, div_one]

def rootPower (C : Certificate p q) (u : (ZMod q)ˣ)
    (hu : u ^ p = 1) : Subgroup.zpowers C.rootUnit := by
  refine ⟨u, ?_⟩
  rw [C.rootUnit_isPrimitive.zpowers_eq, mem_rootsOfUnity]
  exact hu

noncomputable def rootPowerLog (C : Certificate p q) (u : (ZMod q)ˣ)
    (hu : u ^ p = 1) : ZMod p :=
  C.rootUnit_isPrimitive.zmodEquivZPowers.symm
    (Additive.ofMul (rootPower C u hu))

theorem rootUnit_pow_rootPowerLog_val (C : Certificate p q)
    (u : (ZMod q)ˣ) (hu : u ^ p = 1) :
    C.rootUnit ^ (rootPowerLog C u hu).val = u := by
  let z : Subgroup.zpowers C.rootUnit := rootPower C u hu
  let a : ZMod p := rootPowerLog C u hu
  have ha : ((a.val : ℕ) : ZMod p) = a := ZMod.natCast_zmod_val a
  have happly :=
    C.rootUnit_isPrimitive.zmodEquivZPowers.apply_symm_apply
      (Additive.ofMul z)
  have hpow :=
    C.rootUnit_isPrimitive.zmodEquivZPowers_apply_coe_nat a.val
  rw [ha] at hpow
  change C.rootUnit_isPrimitive.zmodEquivZPowers a = Additive.ofMul
      (⟨C.rootUnit ^ a.val, a.val, rfl⟩ : Subgroup.zpowers C.rootUnit) at hpow
  have hz :
      (⟨C.rootUnit ^ a.val, a.val, rfl⟩ : Subgroup.zpowers C.rootUnit) = z := by
    apply Additive.ofMul.injective
    rw [← hpow]
    exact happly
  apply Units.ext
  exact congrArg (fun v : Subgroup.zpowers C.rootUnit ↦
    ((v.1 : (ZMod q)ˣ) : ZMod q)) hz

theorem root_pow_rootPowerLog_val (C : Certificate p q)
    (u : (ZMod q)ˣ) (hu : u ^ p = 1) :
    C.root ^ (rootPowerLog C u hu).val = (u : ZMod q) := by
  simpa [Certificate.rootUnit] using
    congrArg Units.val (rootUnit_pow_rootPowerLog_val C u hu)

noncomputable def phase (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) : Cyc (kummerLogRank p) → ZMod p :=
  fun r ↦ rootPowerLog C (phaseUnit C X r) (phaseUnit_pow_p_eq_one C X r)

theorem phase_root_pow_val (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (r : Cyc (kummerLogRank p)) :
    C.root ^ (phase C X r).val = (phaseUnit C X r : ZMod q) :=
  root_pow_rootPowerLog_val C _ _

theorem root_pow_sub_val (C : Certificate p q) (a b : ZMod p) :
    C.root ^ (a - b).val = C.root ^ a.val / C.root ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod C.root_isPrimitive.pow_eq_one
  have hroot0 : C.root ≠ 0 :=
    C.root_isPrimitive.ne_zero (Fact.out : p.Prime).ne_zero
  field_simp [hroot0]
  simpa [pow_add] using hpow

theorem row_root_relation (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) (j : Fin (kummerLogRank p)) :
    classRoot C X (coord (kummerLogRank p) (X.row j)) =
        embeddingRoot C.root j ∨
      classRoot C X (coord (kummerLogRank p) (X.row j)) =
        (embeddingRoot C.root j)⁻¹ := by
  simpa only [embeddingRoot] using
    classRoot_eq_pow_or_inv_of_sq C X
      (coord (kummerLogRank p) (X.row j)) (j.val + 1) (X.row_square j)

theorem product_root_relation (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three)
    (j i : Fin (kummerLogRank p)) :
    classRoot C X
        (coord (kummerLogRank p) (X.row j) +
          coord (kummerLogRank p) (X.column i)) =
        embeddingRoot C.root j ^ (i.val + 2) ∨
      classRoot C X
        (coord (kummerLogRank p) (X.row j) +
          coord (kummerLogRank p) (X.column i)) =
        (embeddingRoot C.root j ^ (i.val + 2))⁻¹ := by
  let r := coord (kummerLogRank p) (X.row j)
  let s := coord (kummerLogRank p) (X.column i)
  let target : ℕ := (j.val + 1) * (i.val + 2)
  have hsquare : ((X.classExponent (r + s) : ZMod p) ^ 2) =
      ((target : ℕ) : ZMod p) ^ 2 := by
    dsimp only [target]
    rw [X.classExponent_add_sq, X.row_square,
      X.toCharacterCoordinates.column_square]
    simp only [teichmullerEvenNode, kummerLogColumnIndex,
      KummerCriterion.CPlusGeneratorIndex]
    push_cast
    ring
  simpa only [r, s, target, embeddingRoot, pow_mul] using
    classRoot_eq_pow_or_inv_of_sq C X (r + s) target hsquare

theorem phaseUnit_ratio_val (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three)
    (r s : Cyc (kummerLogRank p)) :
    ((phaseUnit C X (r + s) / phaseUnit C X r : (ZMod q)ˣ) : ZMod q) =
      weight C (classRoot C X (r + s)) /
        weight C (classRoot C X r) := by
  simp only [phaseUnit, weightUnit_val, Units.val_div_eq_div_val]
  field_simp [weight_classRoot_ne_zero C X]

theorem normalized_pow_eq_phase_difference_root (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three)
    (j i : Fin (kummerLogRank p)) :
    normalizedUnitValue C.root j i ^ C.symbolExponent =
      C.root ^
        (phase C X
          (coord (kummerLogRank p) (X.row j) +
            coord (kummerLogRank p) (X.column i)) -
          phase C X (coord (kummerLogRank p) (X.row j))).val := by
  let x : ZMod q := embeddingRoot C.root j
  let a : ℕ := i.val + 2
  let r := coord (kummerLogRank p) (X.row j)
  let s := coord (kummerLogRank p) (X.column i)
  have hx0 : x ≠ 0 :=
    (embeddingRoot_isPrimitive C.hp2 C.root_isPrimitive j).ne_zero
      (Fact.out : p.Prime).ne_zero
  have hrowWeight : weight C x = weight C (classRoot C X r) := by
    rcases row_root_relation C X j with h | h
    · exact congrArg (weight C) h.symm
    · calc
        weight C x = weight C x⁻¹ := (weight_inv C x hx0).symm
        _ = weight C (classRoot C X r) := congrArg (weight C) h.symm
  have hprodWeight : weight C (x ^ a) = weight C (classRoot C X (r + s)) := by
    rcases product_root_relation C X j i with h | h
    · exact congrArg (weight C) h.symm
    · calc
        weight C (x ^ a) = weight C (x ^ a)⁻¹ :=
          (weight_inv C (x ^ a) (pow_ne_zero _ hx0)).symm
        _ = weight C (classRoot C X (r + s)) :=
          congrArg (weight C) h.symm
  rw [normalized_pow_eq_weight_ratio C]
  change weight C (x ^ a) / weight C x = _
  rw [hprodWeight, hrowWeight, root_pow_sub_val]
  rw [phase_root_pow_val, phase_root_pow_val]
  rw [← Units.val_div_eq_div_val]
  exact (phaseUnit_ratio_val C X r s).symm

theorem matrix_entry_eq_phase_difference (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three)
    (j i : Fin (kummerLogRank p)) :
    C.matrix j i =
      phase C X
          (coord (kummerLogRank p) (X.row j) +
            coord (kummerLogRank p) (X.column i)) -
        phase C X (coord (kummerLogRank p) (X.row j)) := by
  let b : ZMod p :=
    phase C X
        (coord (kummerLogRank p) (X.row j) +
          coord (kummerLogRank p) (X.column i)) -
      phase C X (coord (kummerLogRank p) (X.row j))
  have hpowers : C.root ^ (C.matrix j i).val = C.root ^ b.val := by
    rw [← C.entry_certificate]
    exact normalized_pow_eq_phase_difference_root C X j i
  change C.matrix j i = b
  apply ZMod.val_injective
  exact C.root_isPrimitive.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpowers

/-- Every finite-field circular-unit certificate has a canonical cyclic
presentation once the p-only real character coordinates are fixed. -/
noncomputable def ofCertificate (C : Certificate p q)
    (X : ArithmeticCoordinates p hp_three) :
    CyclicPresentation hp_three C X.toCharacterCoordinates where
  row := X.row
  phase := phase C X
  matrix_eq := by
    ext j i
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      differenceMatrix]
    exact matrix_entry_eq_phase_difference C X j i

end AutomaticPresentation

end

end Fermat.Irregular.AuxiliaryResidueChannels
