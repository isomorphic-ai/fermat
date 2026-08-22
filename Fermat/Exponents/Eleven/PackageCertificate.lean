import FltRegular.SmallNumbers.Eleven.Eleven

/-!
# The uploaded exponent-eleven class-number certificate

This module reruns the Minkowski/Kummer–Dedekind calculation for the eleventh
cyclotomic field using the proof package's norm-`23` generator
`1 - X + X³`.  The corresponding prime ideal is certified principal by exact
integral Bézout identities, all checked by Lean's `ring` tactic.
-/

namespace Fermat.Eleven.PackageCertificate

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {11} ℚ K]

set_option linter.flexible false in
set_option linter.style.longLine false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
variable (K) in
/-- The integers of an eleventh cyclotomic field form a principal ideal ring,
proved with the norm-`23` generator from the uploaded proof package. -/
theorem ringOfIntegers_isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 11
  rw [M11, cyclotomic_11]
  intro p hple hp hpn
  fin_cases hple <;> any_goals norm_num at hp
  on_goal 5 => simp at hpn

  -- Norm 23: g = 1 - X + X³.
  on_goal 8 =>
    right
    let P : ℤ[X] := X + 10
    let d := 1
    let Q : ℤ[X] :=
      X^9 - 9*X^8 - X^7 + 11*X^6 + 6*X^5 + 10*X^4 - 7*X^3 +
      2*X^2 + 4*X + 7
    let A : ℤ[X] :=
      4*X^8 - 5*X^6 - 3*X^5 - 4*X^4 + 3*X^3 - X^2 - 2*X - 3
    let G : ℤ[X] := 1 - X + X^3
    let Qp : ℤ[X] :=
      11*X^9 + 16*X^8 + 12*X^7 + 6*X^6 - 3*X^5 - 5*X^4 -
      8*X^3 - X^2 - 2*X + 8
    let Rp : ℤ[X] := -11*X^2 - 5*X + 15
    let QP : ℤ[X] :=
      5*X^9 + 7*X^8 + 5*X^7 + 2*X^6 - 2*X^5 - 3*X^4 -
      4*X^3 - X^2 - X + 3
    let RP : ℤ[X] := -5*X^2 - 2*X + 7
    let C1 : ℤ[X] := X^2 - 10*X + 7
    let C2 : ℤ[X] := 4*X - 3
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

end Fermat.Eleven.PackageCertificate
