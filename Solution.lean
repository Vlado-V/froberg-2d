module

public import Froberg.UniformMain

@[expose] public section

/-- The proved counterpart of the independently specified manuscript theorem. -/
theorem FrobergPaper.main_result : FrobergPaper.Statement :=
  Froberg.paperStatement
