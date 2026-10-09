module

public import Froberg.PolynomialRowOpening
public import Froberg.BilinearKoszulTransport
public import Froberg.BiformCoordinates

@[expose] public section

/-! Sparse witnesses yield literal exactness in the fixed intrinsic biform
space, independent of the output basis chosen to construct a witness. -/
noncomputable section
namespace Froberg
open Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ I W : Type*} [Fintype σ] [Fintype I]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {n R s d q : ℕ}

local instance fullOutputFinite : Module.Finite K (homogeneousSubmodule σ K R) :=
  Module.Finite.of_basis (finiteVariableFormsBasis σ R)

abbrev FullBiform (K : Type) [Field K] (σ : Type*) (n R s : ℕ) :=
  biformImage (homogeneousSubmodule σ K R) (Forms K n s)

instance fullBiformFinite : Module.Finite K (FullBiform K σ n R s) := by
  letI : Module.Finite K (homogeneousSubmodule (σ ⊕ Fin n) K (R+s)) :=
    Module.Finite.of_basis (finiteVariableFormsBasis (σ ⊕ Fin n) (R+s))
  exact Submodule.finiteDimensional_of_le (biformImage_homogeneous _ _ le_rfl le_rfl)

/-- Full homogeneous output coordinates, viewed intrinsically. -/
def fullBiformCoordinates
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R) :
    (Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) ≃ₗ[K]
      FullBiform K σ n R s :=
  LinearEquiv.ofBijective
    ((polynomialFormVector o s).codRestrict _ (fun u =>
      polynomialFormVector_mem_biform o _ _ hdeg u (fun i => (u i).property)))
    ⟨fun x y h => polynomialFormVector_injective o ho (congrArg Subtype.val h),by
      intro f
      have hf : f.val∈(polynomialFormVector o s).range := by
        rw [polynomialFormVector_range_complete o ho hdeg]
        exact f.property
      obtain ⟨u,hu⟩ := hf
      exact ⟨u,Subtype.ext hu⟩⟩

@[simp] theorem fullBiformCoordinates_val
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R)
    (u : Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) :
    (fullBiformCoordinates o ho hdeg u).val=polynomialFormVector o s u := rfl

/-- Literal scalar multiplication of a full homogeneous biform. -/
def fullBiformScalarProduct :
    Forms K n d →ₗ[K] FullBiform K σ n R s →ₗ[K] MvPolynomial (σ ⊕ Fin n) K :=
  (LinearMap.mul K (MvPolynomial (σ ⊕ Fin n) K)).compl₁₂
    ((rename Sum.inr).toLinearMap.comp (Forms K n d).subtype)
    (FullBiform K σ n R s).subtype

@[simp] theorem fullBiformScalarProduct_apply
    (f : Forms K n d) (u : FullBiform K σ n R s) :
    fullBiformScalarProduct f u=rename Sum.inr f.val*u.val := rfl

/-- The actual intrinsic row has exactly the expected constant relations. -/
theorem sparse_witness_intrinsic_exact
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R)
    (e : I → Fin n →₀ ℕ)
    (v : I → Fin (finrank K (homogeneousSubmodule σ K R)) → K)
    (he : ∀ i,(e i).degree=s) (Q : Fin q → Forms K n d)
    (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K
        ((Fin q → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) ×
          (I → Forms K n d)) W).comp (intermediateKoszul e v he Q)).range) :
    (bilinearKoszulRow fullBiformScalarProduct Q
      (fun i => fullBiformCoordinates o ho hdeg (attachedCoordinates e v he i)) P).ker=
    (bilinearKoszulConstants (K := K) (W := W) Q
      (fun i => fullBiformCoordinates o ho hdeg (attachedCoordinates e v he i))).range := by
  apply bilinearKoszulRow_exact_transport (fullBiformCoordinates o ho hdeg)
    (coordinateScalarProduct o) fullBiformScalarProduct
  · intro f u
    exact (coordinateScalarProduct_apply o f u).symm
  · exact sparse_witness_unrestricted_exact o e v he Q P hker

end Froberg
