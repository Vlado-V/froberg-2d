module

public import Froberg.PreparedBiformCoordinates
public import Froberg.PreparedTargetFamily

@[expose] public section

/-! Realization of prescribed high tensors in the full prepared parameter
space. Every scalar coordinate remains free. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
attribute [local instance] tensorGroup

theorem preparedLayerTensor_eq_of_values
    (p : PreparedParameters.Space m d q J counts O)
    (a : J) (hO : O a.val≤Forms K h a.val)
    (g : Fin (counts a.val) → Forms K h a.val ⊗[K] Forms K m (d-a.val))
    (hg : ∀ i,(p.2 a i).val=sumBiform (g i)) :
    preparedLayerTensor a hO p=g := by
  funext i
  apply sumBiform_injective
  exact (preparedLayerTensor_sum a hO p i).trans (hg i)

/-- The tensor parameters and the literal polynomial parameter family have
exactly the same prescribed high coefficients. -/
def preparedTargetTensorParameters
    (g : (a : J) → Fin (counts a.val) → Forms K h a.val ⊗[K] Forms K m (d-a.val))
    (hg : ∀ a i,sumBiform (g a i)∈biformImage (O a.val) (Forms K m (d-a.val)))
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (scalar : PreparedParameters.Label q J counts → Forms K m d)
    (privateScalar : Fin u → Forms K m d) :
    PreparedTarget.Space m d q f u J counts O :=
  ((scalar,fun a i => ⟨sumBiform (g a i),hg a i⟩),((fun i => sumBiformEquiv (F i)),privateScalar))

end Froberg
