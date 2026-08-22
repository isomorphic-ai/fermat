import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCore

/-!
# Batched executable scan for exponent 12613

Evaluating every Voronoi coordinate independently repeats the same modular
multiplications.  This module provides a proof-facing batch evaluator.  For
each upper-half representative it computes the first odd power by repeated
squaring, then advances through a whole consecutive block by multiplying by
the square.

Serialized certificate modules can therefore check a concrete residue list
once and transport its entries back to `scanResidue`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- A length-`width` geometric row
`[x, x*q, x*q^2, ..., x*q^(width-1)]`. -/
private def geometricRow (width : ℕ) (x q : ZMod 12613) :
    List (ZMod 12613) :=
  match width with
  | 0 => []
  | width + 1 => x :: geometricRow width (x * q) q

@[simp] private theorem geometricRow_length
    (width : ℕ) (x q : ZMod 12613) :
    (geometricRow width x q).length = width := by
  induction width generalizing x with
  | zero => rfl
  | succ width ih => simp [geometricRow, ih]

private theorem geometricRow_getElem
    (width i : ℕ) (x q : ZMod 12613) (hi : i < width) :
    (geometricRow width x q)[i]'(by simpa using hi) = x * q ^ i := by
  induction width generalizing x i with
  | zero => omega
  | succ width ih =>
      cases i with
      | zero => simp [geometricRow]
      | succ i =>
          simp only [geometricRow, List.getElem_cons_succ]
          rw [ih i (x * q) (by omega)]
          rw [pow_succ]
          ring

/-- The contribution of one upper-half representative to a consecutive
block of odd exponents. -/
private def scanPowerRow (offset width m : ℕ) : List (ZMod 12613) :=
  let x : ZMod 12613 := (2 * m : ℕ)
  geometricRow width (x ^ (2 * offset + 1)) (x ^ 2)

@[simp] private theorem scanPowerRow_length
    (offset width m : ℕ) :
    (scanPowerRow offset width m).length = width := by
  simp [scanPowerRow]

private theorem scanPowerRow_getElem
    (offset width m i : ℕ) (hi : i < width) :
    (scanPowerRow offset width m)[i]'(by simpa using hi) =
      ((2 * m : ℕ) : ZMod 12613) ^ (2 * (offset + i) + 1) := by
  change
    (geometricRow width
      (((2 * m : ℕ) : ZMod 12613) ^ (2 * offset + 1))
      (((2 * m : ℕ) : ZMod 12613) ^ 2))[i]'(by simpa using hi) =
        ((2 * m : ℕ) : ZMod 12613) ^ (2 * (offset + i) + 1)
  rw [geometricRow_getElem width i _ _ hi]
  rw [(pow_mul _ 2 i).symm, ← pow_add]
  congr 1
  omega

/-- Add one representative's geometric row to an accumulated block. -/
private def addPowerRow (offset width : ℕ)
    (acc : List (ZMod 12613)) (m : ℕ) : List (ZMod 12613) :=
  List.zipWith (· + ·) acc (scanPowerRow offset width m)

@[simp] private theorem addPowerRow_length
    (offset width : ℕ) (acc : List (ZMod 12613)) (m : ℕ)
    (hacc : acc.length = width) :
    (addPowerRow offset width acc m).length = width := by
  simp [addPowerRow, hacc]

private theorem addPowerRow_getElem
    (offset width : ℕ) (acc : List (ZMod 12613)) (m i : ℕ)
    (hacc : acc.length = width) (hi : i < width) :
    (addPowerRow offset width acc m)[i]'(by
        rw [addPowerRow_length offset width acc m hacc]
        exact hi) =
      acc[i]'(by omega) +
        ((2 * m : ℕ) : ZMod 12613) ^ (2 * (offset + i) + 1) := by
  change
    (List.zipWith (· + ·) acc
      (scanPowerRow offset width m))[i]'(by simp [hacc, hi]) =
        acc[i]'(by omega) +
          ((2 * m : ℕ) : ZMod 12613) ^ (2 * (offset + i) + 1)
  rw [List.getElem_zipWith]
  rw [scanPowerRow_getElem offset width m i hi]

/-- Tail-recursive row accumulation.  The proof-producing evaluator retains
only the current block and one geometric row. -/
private def sumPowerRows (offset width : ℕ) (ms : List ℕ) :
    List (ZMod 12613) :=
  ms.foldl (addPowerRow offset width) (List.replicate width 0)

@[simp] private theorem foldl_addPowerRow_length
    (offset width : ℕ) (ms : List ℕ) (acc : List (ZMod 12613))
    (hacc : acc.length = width) :
    (ms.foldl (addPowerRow offset width) acc).length = width := by
  induction ms generalizing acc with
  | nil => simpa using hacc
  | cons m ms ih =>
      simp only [List.foldl_cons]
      exact ih (addPowerRow offset width acc m)
        (addPowerRow_length offset width acc m hacc)

@[simp] private theorem sumPowerRows_length
    (offset width : ℕ) (ms : List ℕ) :
    (sumPowerRows offset width ms).length = width := by
  apply foldl_addPowerRow_length
  simp

private theorem foldl_addPowerRow_getElem
    (offset width : ℕ) (ms : List ℕ) (acc : List (ZMod 12613))
    (i : ℕ) (hacc : acc.length = width) (hi : i < width) :
    (ms.foldl (addPowerRow offset width) acc)[i]'(by
        rw [foldl_addPowerRow_length offset width ms acc hacc]
        exact hi) =
      acc[i]'(by omega) +
        (ms.map fun m ↦
          (((2 * m : ℕ) : ZMod 12613) ^
            (2 * (offset + i) + 1))).sum := by
  induction ms generalizing acc with
  | nil => simp
  | cons m ms ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (addPowerRow offset width acc m)
        (addPowerRow_length offset width acc m hacc)]
      rw [addPowerRow_getElem offset width acc m i hacc hi]
      ring

private theorem sumPowerRows_getElem
    (offset width : ℕ) (ms : List ℕ) (i : ℕ) (hi : i < width) :
    (sumPowerRows offset width ms)[i]'(by simpa using hi) =
      (ms.map fun m ↦
        (((2 * m : ℕ) : ZMod 12613) ^
          (2 * (offset + i) + 1))).sum := by
  change
    (ms.foldl (addPowerRow offset width)
      (List.replicate width 0))[i]'(by
        rw [foldl_addPowerRow_length offset width ms
          (List.replicate width 0) (by simp)]
        exact hi) = _
  rw [foldl_addPowerRow_getElem offset width ms
    (List.replicate width 0) i (by simp) hi]
  simp

/-- All `width` consecutive residues beginning at even-index coordinate
`offset`. -/
def scanBlockResidues (offset width : ℕ) : List (ZMod 12613) :=
  sumPowerRows offset width (List.range' 6307 6306)

@[simp] theorem scanBlockResidues_length (offset width : ℕ) :
    (scanBlockResidues offset width).length = width := by
  simp [scanBlockResidues]

/-- Correctness of the batched evaluator: entry `i` is the classical
depth-one Voronoi residue at even index `2 * (offset + i + 1)`. -/
theorem scanBlockResidues_getElem
    (offset width : ℕ) (i : ℕ) (hi : i < width) :
    (scanBlockResidues offset width)[i]'(by simpa using hi) =
      Fermat.Irregular.ModularBernoulliScan.scanResidue
        12613 2 (2 * (offset + i + 1)) := by
  rw [scanResidue_two_eq_upperSum]
  have hexp :
      2 * (offset + i + 1) - 1 = 2 * (offset + i) + 1 := by
    omega
  rw [hexp]
  simpa only [scanBlockResidues, Nat.Ico_eq_range',
    show 12613 - 6307 = 6306 by norm_num, Finset.sum_mk,
    Multiset.map_coe, Multiset.sum_coe] using
    sumPowerRows_getElem offset width (List.range' 6307 6306) i hi

end Fermat.TwelveThousandSixHundredThirteen.IrregularScan
