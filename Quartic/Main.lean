import Quartic.FiniteBaseCases
import Quartic.UniformTransfer

/-! The generic quartic theorem for every positive dimension and every
admissible generator count, over every characteristic-zero field. -/
noncomputable section
namespace Quartic
variable {K : Type*} [Field K] [CharZero K]

/-- The unconditional universal principal-open quartic theorem. -/
theorem main_generic : MainGenericStatement K :=
  UniformTransfer.main_of_closure_finite_bases
    (FiniteBaseCases.generic (K := AlgebraicClosure K))

/-- The corresponding universal statement about actual quadratic subspaces. -/
theorem main_witness : MainWitnessStatement K :=
  main_generic_implies_witness K (main_generic (K := K))

end Quartic
