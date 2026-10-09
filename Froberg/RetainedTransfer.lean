module

public import Froberg.ProjectedHyperplane
public import Froberg.HomogeneousRename
public import Froberg.EndpointFieldDescent

@[expose] public section

/-! The retained kernel in the local comparison has exactly the old
child homology dimension, and hence is bounded by the old critical defect. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
attribute [local irreducible] upperCount
open Module
variable {K : Type} [Field K] [Infinite K]
variable {Z U : Type*} [AddCommGroup Z] [Module K Z]
  [AddCommGroup U] [Module K U]
variable {m n d r t : ℕ}

theorem projected_retained_old_finrank (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (hW : W ≤ Submodule.span K (Set.range q))
    (old : Fin t → Forms K m d) (hold : LinearIndependent K old) (f : Fin m ↪ Fin n)
    (hinj : Set.InjOn (pi.comp (renameForm f)) (endpointMultiplication old).range)
    (hrel : (pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed W=
      (pi.comp formalPolynomialMultiplication).ker ⊓
        formalProducts ((Submodule.span K (Set.range old)).map (renameForm f)) (renameForm f).range) :
    finrank K (projectedRetainedHomology pi q hq W)=finrank K (EndpointHomology old) := by
  rw [projectedRetainedHomology_finrank pi q hq W hW,hrel]
  exact renamed_old_homology_finrank old hold f pi hinj

theorem coefficient_kernel_critical_bound (hm : 0 < m)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (hW : W ≤ Submodule.span K (Set.range q))
    (old : Fin t → Forms K m d) (hold : LinearIndependent K old)
    (ht : t=upperCount m d-1)
    (hgeneric : finrank K (EndpointHomology old)=genericHomology K m d t)
    (f : Fin m ↪ Fin n)
    (hinj : Set.InjOn (pi.comp (renameForm f)) (endpointMultiplication old).range)
    (hrel : (pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed W=
      (pi.comp formalPolynomialMultiplication).ker ⊓
        formalProducts ((Submodule.span K (Set.range old)).map (renameForm f)) (renameForm f).range)
    (coeff : ProjectedEndpointHomology pi q →ₗ[K] U)
    (hcoeff : coeff.ker=projectedRetainedHomology pi q hq W) :
    finrank K coeff.ker ≤ criticalDefect K m d := by
  rw [hcoeff,projected_retained_old_finrank pi q hq W hW old hold f hinj hrel,hgeneric,ht]
  exact (critical_child_defects_le hm).1

end Froberg
