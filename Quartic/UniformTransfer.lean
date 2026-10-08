import Quartic.LargeTransfer
import Quartic.Induction
import Quartic.GenericFieldDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The actual transfer for every child dimension at least 28, and the precise
remaining finite-base boundary for the universal characteristic-zero theorem. -/
noncomputable section
namespace Quartic.UniformTransfer
variable {K : Type*} [Field K] [CharZero K]

/-- No upper cutoff on the child dimension remains. -/
theorem transfer [IsAlgClosed K] (m : ℕ) (hm : 28 ≤ m)
    (hchild : ∀ q,q ≤ (m+1).choose 2 → GenericQuartic K m q) :
    ∀ r,r ≤ (m+3+1).choose 2 → GenericQuartic K (m+3) r := by
  by_cases hsmall : m ≤ 40
  · exact SmallTransfer.transfer m hm hsmall hchild
  · exact LargeTransfer.transfer m (by omega) hchild

/-- Checked induction reduces the whole statement over an algebraically closed
field to dimensions 1 through 30. The finite-base premise remains explicit. -/
theorem main_of_finite_bases [IsAlgClosed K]
    (hbase : ∀ n,1 ≤ n → n ≤ 30 → ∀ r,r ≤ (n+1).choose 2 → GenericQuartic K n r) :
    MainGenericStatement K :=
  Induction.from_positive_bases_and_three_step
    (fun n => ∀ r,r ≤ (n+1).choose 2 → GenericQuartic K n r) hbase transfer

/-- The remaining base cases may be checked in the algebraic closure; the final
principal-open statement then descends to the original characteristic-zero field. -/
theorem main_of_closure_finite_bases
    (hbase : ∀ n,1 ≤ n → n ≤ 30 → ∀ r,r ≤ (n+1).choose 2 →
      GenericQuartic (AlgebraicClosure K) n r) : MainGenericStatement K :=
  GenericFieldDescent.mainGeneric_descend (algebraMap K (AlgebraicClosure K))
    (main_of_finite_bases hbase)

theorem witnesses_of_closure_finite_bases
    (hbase : ∀ n,1 ≤ n → n ≤ 30 → ∀ r,r ≤ (n+1).choose 2 →
      GenericQuartic (AlgebraicClosure K) n r) : MainWitnessStatement K :=
  main_generic_implies_witness K (main_of_closure_finite_bases hbase)

end Quartic.UniformTransfer
