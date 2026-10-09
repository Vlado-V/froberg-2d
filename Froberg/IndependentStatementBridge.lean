module

public import Froberg.IndependentStatement
public import Froberg.UniformStatement

@[expose] public section

/-! The independently stated quotient-ring theorem is definitionally the
same conclusion as the formalization's public uniform statement. -/
namespace Froberg

theorem uniformMainStatement_iff_independent :
    UniformMainStatement ↔ FrobergPaper.Statement := Iff.rfl

end Froberg
