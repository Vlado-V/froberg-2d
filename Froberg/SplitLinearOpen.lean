import Froberg.SplitRestorationOpen

/-! The split coefficient-complex open in arbitrary finite-dimensional linear
parameters, with one fixed affine contribution to the second family. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.SplitRestoration
open Module MvPolynomial Quartic PolynomialRestoration
variable {K : Type} {σ E V W Z S : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup Z] [Module K Z]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
variable {r b : ℕ}

theorem split_linear_restoration_open
    (j : V →ₗ[K] MvPolynomial σ K) (k : W →ₗ[K] MvPolynomial σ K)
    (pi : MvPolynomial σ K →ₗ[K] Z)
    (G : E →ₗ[K] (Fin r → V)) (P : E →ₗ[K] (Fin b → W)) (U : Fin b → W)
    (T : S →ₗ[K] (Fin r → V))
    (hT : ∀ a z,PolynomialRestoration.row j pi (G a) (T z)=0)
    (a₀ : E)
    (hreduce : ∀ c v,row j k pi (G a₀) (P a₀+U) (c,v)=0 →
      ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K) (z : S),
        c-coefficientBoundary (G a₀) M=T z ∧ v=coefficientBoundary (P a₀+U) C) :
    ∃ D : MvPolynomial (Fin (finrank K E)) K,
      eval ((Module.finBasis K E).equivFun a₀) D≠0 ∧
      ∀ a,eval ((Module.finBasis K E).equivFun a) D≠0 →
        ∀ c v,row j k pi (G a) (P a+U) (c,v)=0 →
          ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K) (z : S),
            c-coefficientBoundary (G a) M=T z ∧ v=coefficientBoundary (P a+U) C := by
  let coord := (Module.finBasis K E).equivFun
  let g := G.comp coord.symm.toLinearMap
  let p := fun x => P (coord.symm x)+U
  obtain ⟨D,hD,hgood⟩ := split_restoration_open (K := K) (σ := σ)
    (I := Fin (finrank K E)) (V := V) (W := W) (Z := Z) (S := S) j k pi g p
    (isPolynomialFamily_linear g)
    ((isPolynomialFamily_linear (P.comp coord.symm.toLinearMap)).add (isPolynomialFamily_const U))
    T (fun x z => hT (coord.symm x) z) (coord a₀) (by
      simpa only [g,p,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hreduce)
  refine ⟨D,hD,?_⟩
  intro a ha c v hc
  have hg : g (coord a)=G a := by
    simp only [g,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  have hp : p (coord a)=P a+U := by simp only [p,LinearEquiv.symm_apply_apply]
  simpa only [hg,hp] using hgood (coord a) ha c v (by simpa only [hg,hp] using hc)

end Froberg.SplitRestoration
