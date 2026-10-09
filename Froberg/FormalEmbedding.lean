module

public import Froberg.FormalHomology

@[expose] public section

/-! Formal relations under an actual embedding of the old variables. The
target map need only be injective on the old multiplication image. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {V W T Z : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup T] [Module K T]
  [AddCommGroup Z] [Module K Z]

theorem map_formalMixed_linear (j : V →ₗ[K] W) (L : Submodule K V) :
    (formalMixed L).map (SymmetricFunctor.map (ι := Fin 2) j)=
      formalProducts (L.map j) j.range := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨a,b,ha,rfl⟩
    change SymmetricFunctor.map j (symProd a b) ∈ formalProducts (L.map j) j.range
    rw [symmetricMap_symProd]
    exact Submodule.subset_span ⟨j a,j b,⟨a,ha,rfl⟩,⟨b,rfl⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,b,⟨a',ha,rfl⟩,⟨b',rfl⟩,rfl⟩
    exact ⟨symProd a' b',symProd_mem_formalMixed L ha b',symmetricMap_symProd j a' b'⟩

theorem formal_relation_embedding (j : V →ₗ[K] W)
    (M : SymmetricSquare K V →ₗ[K] T) (N : SymmetricSquare K W →ₗ[K] Z)
    (J : T →ₗ[K] Z) (L : Submodule K V)
    (hcomm : N.comp (SymmetricFunctor.map j)=J.comp M)
    (hJ : Set.InjOn J ((formalMixed L).map M)) :
    N.ker ⊓ formalProducts (L.map j) j.range=
      (M.ker ⊓ formalMixed L).map (SymmetricFunctor.map (ι := Fin 2) j) := by
  rw [← map_formalMixed_linear]
  ext x
  constructor
  · rintro ⟨hx,⟨y,hy,rfl⟩⟩
    refine ⟨y,⟨?_,hy⟩,rfl⟩
    apply hJ ⟨y,hy,rfl⟩ (Submodule.zero_mem _)
    have hc := LinearMap.congr_fun hcomm y
    change N (SymmetricFunctor.map j y)=J (M y) at hc
    change N (SymmetricFunctor.map j y)=0 at hx
    rw [← hc,hx,map_zero]
  · rintro ⟨y,⟨hy,hm⟩,rfl⟩
    refine ⟨?_,⟨y,hm,rfl⟩⟩
    have hc := LinearMap.congr_fun hcomm y
    change N (SymmetricFunctor.map j y)=J (M y) at hc
    change N (SymmetricFunctor.map j y)=0
    rw [hc,hy,map_zero]

def formalRelationEmbeddingEquiv (j : V →ₗ[K] W) (hj : Function.Injective j)
    (M : SymmetricSquare K V →ₗ[K] T) (N : SymmetricSquare K W →ₗ[K] Z)
    (J : T →ₗ[K] Z) (L : Submodule K V)
    (hcomm : N.comp (SymmetricFunctor.map j)=J.comp M)
    (hJ : Set.InjOn J ((formalMixed L).map M)) :
    (M.ker ⊓ formalMixed L : Submodule K (SymmetricSquare K V)) ≃ₗ[K]
      (N.ker ⊓ formalProducts (L.map j) j.range : Submodule K (SymmetricSquare K W)) :=
  (Submodule.equivMapOfInjective (SymmetricFunctor.map j)
    (SymmetricFunctor.map_injective j hj) (M.ker ⊓ formalMixed L)).trans
      (LinearEquiv.ofEq _ _ (formal_relation_embedding j M N J L hcomm hJ).symm)

variable {m n d r : ℕ}

theorem formal_old_product_image (q : Fin r → Forms K m d) :
    (formalMixed (Submodule.span K (Set.range q))).map formalPolynomialMultiplication=
      (endpointMultiplication q).range := by
  rw [← range_formalCoefficientMap q,← LinearMap.range_comp,formalPolynomialMultiplication_comp q]

theorem embedded_old_homology_finrank (q : Fin r → Forms K m d) (hq : LinearIndependent K q)
    (j : Forms K m d →ₗ[K] Forms K n d) (hj : Function.Injective j)
    (pi : Forms K n (2*d) →ₗ[K] Z) (J : Forms K m (2*d) →ₗ[K] Z)
    (hcomm : (pi.comp formalPolynomialMultiplication).comp (SymmetricFunctor.map j)=
      J.comp formalPolynomialMultiplication)
    (hJ : Set.InjOn J (endpointMultiplication q).range) :
    finrank K ((pi.comp formalPolynomialMultiplication).ker ⊓
      formalProducts ((Submodule.span K (Set.range q)).map j) j.range :
        Submodule K (SymmetricSquare K (Forms K n d))) = finrank K (EndpointHomology q) := by
  have hJ' : Set.InjOn J ((formalMixed (Submodule.span K (Set.range q))).map
      formalPolynomialMultiplication) := by rwa [formal_old_product_image]
  exact ((endpointHomologyEquivFormal_anyChar q hq).trans
    (formalRelationEmbeddingEquiv j hj formalPolynomialMultiplication
      (pi.comp formalPolynomialMultiplication) J _ hcomm hJ')).finrank_eq.symm

end Froberg
