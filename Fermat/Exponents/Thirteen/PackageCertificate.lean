import FltRegular.SmallNumbers.Thirteen.Thirteen

/-!
# The uploaded exponent-thirteen class-number certificate

This module reruns the Minkowski/Kummer–Dedekind calculation for the thirteenth
cyclotomic field using the five small generators recorded in the uploaded proof
package:

* `1 - X² - X³` (norm `27`),
* `1 - X + X³` (norm `53`),
* `1 - X - X⁴` (norm `79`),
* `1 - X - X³` (norm `131`), and
* `1 - X + X² + X⁴` (norm `157`).

Rather than introducing a separate determinant/resultant normalization layer,
the proof gives exact integral Bézout certificates for the corresponding prime
ideals.  Every displayed polynomial identity is checked by Lean's `ring`
tactic.
-/

namespace Fermat.Thirteen.PackageCertificate

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {13} ℚ K]

set_option linter.flexible false in
set_option linter.style.longLine false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
variable (K) in
/-- The integers of a thirteenth cyclotomic field form a principal ideal ring,
proved with the five small generators from the uploaded proof package. -/
theorem ringOfIntegers_isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 13
  rw [M13, cyclotomic_13]
  intro p hple hp hpn
  fin_cases hple <;> any_goals norm_num at hp
  on_goal 6 => simp at hpn

  -- Norm 27: g = 1 - X² - X³.
  on_goal 2 =>
    right
    let P : ℤ[X] := X^3 + X^2 + 2
    let d := 3
    let Q : ℤ[X] :=
      X^9 + X^7 + X^6 + 2*X^4 + X^2 + 2*X + 2
    let A : ℤ[X] :=
      -X^9 - X^7 - X^6 - 2*X^4 - X^3 - X^2 - X - 1
    let G : ℤ[X] := 1 - X^2 - X^3
    let Qp : ℤ[X] :=
      X^10 + X^8 + X^7 + 2*X^5 + X^3 + 2*X^2 - X + 3
    let Rp : ℤ[X] := X
    let QP : ℤ[X] :=
      X^10 + X^8 + X^7 + 2*X^5 + X^3 + 2*X^2 - X + 2
    let RP : ℤ[X] := X
    let C1 : ℤ[X] := -1
    let C2 : ℤ[X] := 1
    use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp only [P, Q, A]
      ring
    · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
      refine ⟨?_, ?_, ?_⟩ <;> ring

  -- Norm 53: g = 1 - X + X³.
  on_goal 14 =>
    right
    let P : ℤ[X] := X + 37
    let d := 1
    let Q : ℤ[X] :=
      X^11 + 17*X^10 + 8*X^9 + 23*X^8 - 2*X^7 + 22*X^6 - 18*X^5 -
      22*X^4 + 20*X^3 + 3*X^2 - 4*X - 10
    let A : ℤ[X] :=
      -X^11 - 12*X^10 - 6*X^9 - 16*X^8 + X^7 - 15*X^6 + 13*X^5 +
      15*X^4 - 14*X^3 - 2*X^2 + 3*X + 7
    let G : ℤ[X] := 1 - X + X^3
    let Qp : ℤ[X] :=
      24*X^11 + 37*X^10 + 33*X^9 + 22*X^8 + 5*X^7 - 2*X^6 -
      8*X^5 + 2*X^4 + 3*X^3 + 19*X^2 + 10*X + 25
    let Rp : ℤ[X] := -24*X^2 - 13*X + 28
    let QP : ℤ[X] :=
      17*X^11 + 26*X^10 + 23*X^9 + 15*X^8 + 3*X^7 - 2*X^6 -
      6*X^5 + X^4 + 2*X^3 + 13*X^2 + 7*X + 17
    let RP : ℤ[X] := -17*X^2 - 9*X + 20
    let C1 : ℤ[X] := X^2 - 37*X + 1368
    let C2 : ℤ[X] := -955
    use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp only [P, Q, A]
      ring
    · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
      refine ⟨?_, ?_, ?_⟩ <;> ring

  -- Norm 79: g = 1 - X - X⁴.
  on_goal 19 =>
    right
    let P : ℤ[X] := X + 17
    let d := 1
    let Q : ℤ[X] :=
      X^11 - 16*X^10 + 36*X^9 + 21*X^8 + 39*X^7 - 30*X^6 + 37*X^5 +
      4*X^4 + 12*X^3 + 34*X^2 - 24*X + 14
    let A : ℤ[X] :=
      3*X^10 - 8*X^9 - 5*X^8 - 8*X^7 + 6*X^6 - 8*X^5 - X^4 -
      3*X^3 - 7*X^2 + 5*X - 3
    let G : ℤ[X] := 1 - X - X^4
    let Qp : ℤ[X] :=
      27*X^11 + 42*X^10 + 24*X^9 + 14*X^8 + 26*X^7 + 59*X^6 +
      51*X^5 + 29*X^4 + 8*X^3 + 49*X^2 + 63*X + 62
    let Rp : ℤ[X] := 27*X^3 + 15*X^2 - 18*X + 17
    let QP : ℤ[X] :=
      6*X^11 + 9*X^10 + 5*X^9 + 3*X^8 + 6*X^7 + 13*X^6 +
      11*X^5 + 6*X^4 + 2*X^3 + 11*X^2 + 14*X + 13
    let RP : ℤ[X] := 6*X^3 + 3*X^2 - 4*X + 4
    let C1 : ℤ[X] := -X^3 + 17*X^2 + 27*X + 14
    let C2 : ℤ[X] := -4*X^2 - 6*X - 3
    use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp only [P, Q, A]
      ring
    · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
      refine ⟨?_, ?_, ?_⟩ <;> ring

  -- Norm 131: g = 1 - X - X³.
  on_goal 28 =>
    right
    let P : ℤ[X] := X + 51
    let d := 1
    let Q : ℤ[X] :=
      X^11 - 50*X^10 + 62*X^9 - 17*X^8 - 49*X^7 + 11*X^6 - 36*X^5 +
      3*X^4 - 21*X^3 + 24*X^2 - 44*X + 18
    let A : ℤ[X] :=
      19*X^10 - 24*X^9 + 7*X^8 + 19*X^7 - 4*X^6 + 14*X^5 - X^4 +
      8*X^3 - 9*X^2 + 17*X - 7
    let G : ℤ[X] := 1 - X - X^3
    let Qp : ℤ[X] :=
      28*X^11 + 41*X^10 + 33*X^9 + 48*X^8 + 69*X^7 + 46*X^6 +
      40*X^5 + 84*X^4 + 67*X^3 + 17*X^2 + 78*X + 111
    let Rp : ℤ[X] := 28*X^2 + 13*X + 20
    let QP : ℤ[X] :=
      11*X^11 + 16*X^10 + 13*X^9 + 19*X^8 + 27*X^7 + 18*X^6 +
      16*X^5 + 33*X^4 + 26*X^3 + 7*X^2 + 31*X + 43
    let RP : ℤ[X] := 11*X^2 + 5*X + 8
    let C1 : ℤ[X] := -X^2 + 51*X + 18
    let C2 : ℤ[X] := -20*X - 7
    use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp only [P, Q, A]
      ring
    · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
      refine ⟨?_, ?_, ?_⟩ <;> ring

  -- Norm 157: g = 1 - X + X² + X⁴.
  on_goal 32 =>
    right
    let P : ℤ[X] := X + 82
    let d := 1
    let Q : ℤ[X] :=
      X^11 + 76*X^10 + 49*X^9 + 65*X^8 + 9*X^7 + 48*X^6 - 10*X^5 +
      36*X^4 + 32*X^3 + 46*X^2 - 3*X - 67
    let A : ℤ[X] :=
      -X^11 - 40*X^10 - 26*X^9 - 34*X^8 - 5*X^7 - 25*X^6 + 5*X^5 -
      19*X^4 - 17*X^3 - 24*X^2 + 2*X + 35
    let G : ℤ[X] := 1 - X + X^2 + X^4
    let Qp : ℤ[X] :=
      76*X^11 + 124*X^10 + 113*X^9 + 73*X^8 + 56*X^7 + 37*X^6 +
      25*X^5 + 67*X^4 + 77*X^3 + 42*X^2 + 86*X + 89
    let Rp : ℤ[X] := -76*X^3 - 48*X^2 - 65*X + 68
    let QP : ℤ[X] :=
      40*X^11 + 65*X^10 + 59*X^9 + 38*X^8 + 29*X^7 + 19*X^6 +
      13*X^5 + 35*X^4 + 40*X^3 + 22*X^2 + 45*X + 46
    let RP : ℤ[X] := -40*X^3 - 25*X^2 - 34*X + 36
    let C1 : ℤ[X] := X^3 + 75*X^2 - 26*X - 67
    let C2 : ℤ[X] := -X^3 - 39*X^2 + 14*X + 35
    use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
    rw [show P.natDegree = d by simp only [P]; compute_degree!]
    refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
    · rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
      have : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
      fin_cases this <;> decide +revert
    · simp only [P, Q, A]
      ring
    · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
      refine ⟨?_, ?_, ?_⟩ <;> ring

  all_goals {
    left
    simp
    norm_num
    refine orderOf_lt_of (by norm_num) (fun i hi hipos ↦ ?_)
    have := Finset.mem_Icc.mpr ⟨hipos, hi⟩
    fin_cases this <;> norm_num }

end Fermat.Thirteen.PackageCertificate
