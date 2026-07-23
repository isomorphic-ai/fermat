import Fermat.Irregular.VandiverData
import Fermat.OneHundredFiftySeven.HighBernoulli
import Fermat.OneHundredFiftySeven.IrregularScan

/-!
# Vandiver's finite Bernoulli condition at exponent 157

The complete low recurrence scan leaves exactly the two irregular indices
`62` and `110`.  The direct Faulhaber certificates at
`62 * 157 = 9734` and `110 * 157 = 17270` handle those two exceptional
channels, while the formal Voronoi--Kummer theorem handles every regular
index.

This file is the kernel-checked two-pass Bernoulli loop from the uploaded
seven-fold proof package.  It supplies the finite arithmetic input to
Vandiver's historical Lemma II; it does not by itself assert the global
second-case descent.
-/

namespace Fermat.OneHundredFiftySeven.VandiverData

open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 157) :=
  ⟨by norm_num⟩

/-- The two-channel scan reduces every exceptional index to one of the two
direct high-Bernoulli certificates. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 157)
    (hirregular : (157 : ℤ) ∣ (bernoulli j).num) :
    ¬(157 : ℤ) ^ 3 ∣ (bernoulli (j * 157)).num := by
  rcases
      Fermat.OneHundredFiftySeven.IrregularScan.completeIrregularScan
        j hj hirregular with rfl | rfl
  · simpa using
      HighBernoulli.bernoulli_9734_numerator_not_dvd_cube
  · simpa using
      HighBernoulli.bernoulli_17270_numerator_not_dvd_cube

/-- Every indexed Bernoulli numerator in Vandiver's finite condition is
checked at exponent `157`.  The proof executes the same correction operation
twice, once for each member of the measured irregular-channel set. -/
theorem bernoulliCubeCondition_oneHundredFiftySeven :
    BernoulliCubeCondition 157 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  exact irregularIndex_numerator_not_dvd_cube

end Fermat.OneHundredFiftySeven.VandiverData
