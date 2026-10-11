/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Froberg.QuadraticCertificateFreeRecurrence
public import Froberg.UniformEquivariantReduction

/-! A common variable threshold for quadrics over every infinite field. -/

@[expose] public section

noncomputable section
namespace Froberg

theorem uniformCriticalRecurrence_quadratic : UniformCriticalRecurrence 2 := by
  refine ⟨3, 320, by omega, ?_⟩
  intro K _ _ n hn
  exact QuadraticCertificateFreeRecurrence.step n hn

/-- The quadratic endpoint holds above one threshold independent of the field. -/
theorem uniformEndpoint_quadratic : UniformEndpointStatement 2 :=
  uniformCriticalRecurrence_quadratic.endpoints (by omega)

end Froberg
