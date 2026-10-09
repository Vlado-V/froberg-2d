module

public import Froberg.UniformQuadraticEndpoint
public import Froberg.UniformEndToEndAssembly
public import Froberg.IndependentStatementBridge

@[expose] public section

/-! Fröberg's prediction through twice the generating degree, with one
variable threshold for every infinite coefficient field and every number
of generators. -/
namespace Froberg

theorem uniformMainStatement : UniformMainStatement :=
  uniformMainStatement_of_quadratic_endpoint uniformEndpoint_quadratic

theorem mainStatement_infinite (K : Type) [Field K] [Infinite K] : MainStatement K :=
  uniformMainStatement.specialize K

/-- The same proved conclusion in the independent, Mathlib-only statement. -/
theorem paperStatement : FrobergPaper.Statement :=
  uniformMainStatement_iff_independent.mp uniformMainStatement

end Froberg
