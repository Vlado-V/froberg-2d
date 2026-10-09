module

public import Froberg.QuadraticNonTwoRecurrence
public import Froberg.QuadraticGenericBridge
public import Froberg.UniformEquivariantReduction

@[expose] public section

/-! Combine the two characteristic regimes with a common numerical cutoff. -/
noncomputable section
namespace Froberg

theorem quadraticRecurrence_of_characteristicTwo
    (hcharTwo : ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K] [CharP K 2],
      ∀ n,28 ≤ n → ∀ r,r ≤ (n+1).choose 2 → Quartic.GenericQuartic K n r) :
    UniformCriticalRecurrence 2 := by
  refine ⟨3,320,by omega,?_⟩
  intro K _ _ n hn
  by_cases htwo : (2 : K)=0
  · letI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr htwo
    let L := AlgebraicClosure K
    have hz : criticalDefect L (n+3) 2=0 :=
      QuadraticGenericBridge.criticalDefect_zero (by omega : 0 < n+3)
        (hcharTwo L (n+3) (by omega))
    rw [criticalDefect_baseChange (algebraMap K L) (by omega : 0 < n+3),hz]
    exact Nat.zero_le _
  · exact QuadraticNonTwoRecurrence.step n hn htwo

end Froberg
