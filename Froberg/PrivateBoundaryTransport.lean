module

public import Froberg.PrivateOutputTransport
public import Froberg.PrivateKoszulKernel
public import Froberg.PrivateBoundaryRemoval

@[expose] public section

/-! Coordinate private Koszul cycles become the literal polynomial
boundaries subtracted in the first even output row. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K]

theorem koszulVector_linear_map {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {r : ℕ} (L : V →ₗ[K] W) (q : Fin r → V) (p : GeneratorPair r) :
    (fun i => L (koszulVector q p i))=koszulVector (fun i => L (q i)) p := by
  classical
  funext i
  simp only [koszulVector,map_sub]
  split_ifs <;> simp_all only [map_zero]

theorem koszul_span_linear_map {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {r : ℕ} (L : V →ₗ[K] W) (q v : Fin r → V)
    (hv : v∈Submodule.span K (Set.range (koszulVector q))) :
    (fun i => L (v i))∈Submodule.span K (Set.range (koszulVector (fun i => L (q i)))) := by
  classical
  let T : (Fin r → V) →ₗ[K] (Fin r → W) := LinearMap.pi fun i => L.comp (LinearMap.proj i)
  have hT : (Submodule.span K (Set.range (koszulVector q))).map T ≤
      Submodule.span K (Set.range (koszulVector (fun i => L (q i)))) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x,⟨p,rfl⟩,rfl⟩
    change (fun i => L (koszulVector q p i))∈_
    rw [koszulVector_linear_map]
    exact Submodule.subset_span ⟨p,rfl⟩
  exact hT ⟨v,hv,rfl⟩

namespace PrivateColumns
variable [Infinite K] {σ : Type*} {a z s b h c : ℕ}

theorem privateGenerator_polynomial (o : Fin h → MvPolynomial σ K)
    (ι : Fin b ↪ Fin z) (w : Fin b → Fin h → K) (i : Fin b) :
    polynomialFormVector o s (privateGenerator (a := a) (s := s) ι w i)=
      rename Sum.inl (outputCombination o (w i))*
        rename Sum.inr (monomial (privateExponent a s ι i) (1:K)) :=
  attachedPolynomialFamily_factor o (privateExponent a s ι) w i

theorem private_boundary_polynomial
    (o : Fin h → MvPolynomial σ K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)) (w : Fin b → Fin h → K)
    (hker : (privatePolynomialMap (a := a) (s := s) ι A).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w))))
    (v : Fin b → Fin h → Forms K (a+z) s) (hv : privatePolynomialMap ι A v=0) :
    (fun i => polynomialFormVector o s (v i))∈Submodule.span K (Set.range (koszulVector
      (fun i => rename Sum.inl (outputCombination o (w i))*
        rename Sum.inr (monomial (privateExponent a s ι i) (1:K))))) := by
  have hv' : v∈Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w))) := by
    rw [←hker]
    exact hv
  simpa only [privateGenerator_polynomial] using
    koszul_span_linear_map (polynomialFormVector o s) (privateGenerator ι w) v hv'

end PrivateColumns
end Froberg
