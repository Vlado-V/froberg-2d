module

public import Froberg.QuadraticCharacteristicAssembly
public import Quartic.CharTwoQuadratic

@[expose] public section

/-! A common variable threshold for quadrics over every infinite field. -/
noncomputable section
namespace Froberg

theorem uniformCriticalRecurrence_quadratic : UniformCriticalRecurrence 2 := by
  apply quadraticRecurrence_of_characteristicTwo
  intro K _ _ _ _ n hn r hr
  exact Quartic.CharTwoQuadratic.generic n hn r hr

/-- The quadratic endpoint holds above one threshold independent of the field. -/
theorem uniformEndpoint_quadratic : UniformEndpointStatement 2 :=
  uniformCriticalRecurrence_quadratic.endpoints (by omega)

end Froberg
