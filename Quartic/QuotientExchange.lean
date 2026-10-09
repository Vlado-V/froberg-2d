module

public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Exchanging the two quotients of a commuting square

An injective map F lets exactness modulo its image transfer across a commuting
square. This is an abstract linear-algebra statement; identifying any manuscript
map with this square is a separate task.
-/
noncomputable section
namespace Quartic.QuotientExchange
variable {K U V W Z : Type*} [Ring K]
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
  [Module K U] [Module K V] [Module K W] [Module K Z]
variable (F : U →ₗ[K] W) (G : V →ₗ[K] W) (R : Z →ₗ[K] U) (T : Z →ₗ[K] V)

/-- Commutativity ensures the top image vanishes in the opposite quotient. -/
theorem range_le_quotient_kernel (hcomm : F.comp R = G.comp T) :
    LinearMap.range R ≤ LinearMap.ker ((LinearMap.range G).mkQ.comp F) := by
  rintro _ ⟨z, rfl⟩
  change (LinearMap.range G).mkQ (F (R z)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨T z, (LinearMap.congr_fun hcomm z).symm⟩

/-- Exactness modulo F transfers to exactness modulo G when F is injective. -/
theorem quotient_kernel_le_range (hF : Function.Injective F)
    (hcomm : F.comp R = G.comp T)
    (hexact : LinearMap.ker ((LinearMap.range F).mkQ.comp G) ≤ LinearMap.range T) :
    LinearMap.ker ((LinearMap.range G).mkQ.comp F) ≤ LinearMap.range R := by
  intro u hu
  have hu' : F u ∈ LinearMap.range G := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact hu
  obtain ⟨v, hv⟩ := hu'
  have hvker : v ∈ LinearMap.ker ((LinearMap.range F).mkQ.comp G) := by
    change (LinearMap.range F).mkQ (G v) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨u, hv.symm⟩
  obtain ⟨z, hz⟩ := hexact hvker
  refine ⟨z, hF ?_⟩
  calc
    F (R z) = G (T z) := LinearMap.congr_fun hcomm z
    _ = G v := congrArg G hz
    _ = F u := hv

/-- The exchanged quotient kernel is exactly the prescribed top image. -/
theorem quotient_kernel_eq_range (hF : Function.Injective F)
    (hcomm : F.comp R = G.comp T)
    (hexact : LinearMap.ker ((LinearMap.range F).mkQ.comp G) ≤ LinearMap.range T) :
    LinearMap.ker ((LinearMap.range G).mkQ.comp F) = LinearMap.range R :=
  le_antisymm (quotient_kernel_le_range F G R T hF hcomm hexact)
    (range_le_quotient_kernel F G R T hcomm)

/-- The map induced by F after quotienting by the two square images. -/
def quotientMap (hcomm : F.comp R = G.comp T) :
    U ⧸ LinearMap.range R →ₗ[K] W ⧸ LinearMap.range G :=
  (LinearMap.range R).liftQ ((LinearMap.range G).mkQ.comp F)
    (range_le_quotient_kernel F G R T hcomm)

@[simp] theorem quotientMap_mk (hcomm : F.comp R = G.comp T) (u : U) :
    quotientMap F G R T hcomm ((LinearMap.range R).mkQ u) =
      (LinearMap.range G).mkQ (F u) := rfl

/-- The induced map is injective, with no finite-dimensionality hypothesis. -/
theorem quotientMap_injective (hF : Function.Injective F)
    (hcomm : F.comp R = G.comp T)
    (hexact : LinearMap.ker ((LinearMap.range F).mkQ.comp G) ≤ LinearMap.range T) :
    Function.Injective (quotientMap F G R T hcomm) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _
    (quotient_kernel_le_range F G R T hF hcomm hexact)

end Quartic.QuotientExchange
