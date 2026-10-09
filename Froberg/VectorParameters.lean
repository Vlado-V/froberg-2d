module

public import Froberg.VectorExpansionOpen

@[expose] public section

/-! A common affine coefficient space for arbitrary homogeneous vector generators. -/
noncomputable section
namespace Froberg.VectorParameters
open VectorMultiplicationCoordinates Quartic
variable {K : Type*} [Field K] {h n s c : ℕ}

abbrev Index (h n s c : ℕ) := Fin c × Fin (RowCount h n s)

def generators (p : Index h n s c → K) (i : Fin c) : Rows K h n s :=
  rowFiniteEquiv.symm (fun j => p (i,j))

def coordinates (g : Fin c → Rows K h n s) (ij : Index h n s c) : K :=
  rowFiniteEquiv (g ij.1) ij.2

@[simp] lemma generators_coordinates (g : Fin c → Rows K h n s) : generators (coordinates g)=g := by
  funext i
  exact rowFiniteEquiv.symm_apply_apply (g i)

@[simp] lemma coordinates_generators (p : Index h n s c → K) : coordinates (generators p)=p := by
  funext ij
  exact congrFun (rowFiniteEquiv.apply_symm_apply (fun j => p (ij.1,j))) ij.2

lemma generators_polynomial (i : Fin c) :
    IsPolynomialFamily (fun p : Index h n s c → K => generators p i) :=
  isPolynomialFamily_linear (rowFiniteEquiv.symm.toLinearMap.comp
    (LinearMap.funLeft K K (fun j => (i,j))))

end Froberg.VectorParameters
