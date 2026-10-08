import Froberg.ExtendedPolynomialRow
import Froberg.PreparedCoreExtension
import Froberg.IntrinsicBiformRow

/-! The core-extension argument produces exactness in the actual fixed
biform coefficient spaces, ready for a common-parameter rank open. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z s d R m q : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

 theorem extended_sparse_intrinsic_exact (hs : 1 ≤ s) (hsd : s ≤ d)
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R)
    (e : Fin m → Fin a →₀ ℕ)
    (v : Fin m → Fin (finrank K (homogeneousSubmodule σ K R)) → K)
    (he : ∀ i,(e i).degree=s) (Q : Fin q → Forms K a d)
    (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin a) K)
    (hP : P.range≤FullBiform K σ a R (s+d))
    (hfull : ∀ c ≤ d,Function.Injective (homogeneousMultiplication (d := c) e v he))
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K
        ((Fin q → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K a s) ×
          (Fin m → Forms K a d)) W).comp (intermediateKoszul e v he Q)).range)
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell) :
    let Q' : Fin q → Forms K (a+z) d := fun i =>
      ⟨rename (Fin.castAdd z) (Q i).val,(Q i).property.rename_isHomogeneous⟩
    let E' : Fin m → FullBiform K σ (a+z) R s := fun i =>
      ⟨rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v i),
        biformImage_core_extension _ (by
          rw [←polynomialFormVector_attachedCoordinates o e v he i]
          exact polynomialFormVector_mem_biform o _ _ hdeg _ (fun j => (attachedCoordinates e v he i j).property))⟩
    let P' := (rename (Sum.map id (Fin.castAdd z))).toLinearMap.comp P
    (bilinearKoszulRow fullBiformScalarProduct Q' E' P').ker=
      (bilinearKoszulConstants (K := K) (W := W) Q' E').range := by
  dsimp only
  let Q' : Fin q → Forms K (a+z) d := fun i =>
    ⟨rename (Fin.castAdd z) (Q i).val,(Q i).property.rename_isHomogeneous⟩
  let E' : Fin m → FullBiform K σ (a+z) R s := fun i =>
    ⟨rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v i),
      biformImage_core_extension _ (by
        rw [←polynomialFormVector_attachedCoordinates o e v he i]
        exact polynomialFormVector_mem_biform o _ _ hdeg _ (fun j => (attachedCoordinates e v he i j).property))⟩
  let P' := (rename (Sum.map id (Fin.castAdd z))).toLinearMap.comp P
  change (bilinearKoszulRow fullBiformScalarProduct Q' E' P').ker=
    (bilinearKoszulConstants (K := K) (W := W) Q' E').range
  have hPinj : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro t ht
    have hk : ((0,0),t)∈(addRow (polynomialIntermediateRow o e v he Q) P).ker := by
      change polynomialIntermediateRow o e v he Q 0+P t=0
      rw [map_zero,ht,add_zero]
    rw [hker] at hk
    obtain ⟨C,hC⟩ := hk
    exact (congrArg Prod.snd hC).symm
  apply le_antisymm
  · rintro ⟨⟨u,b⟩,t⟩ ht
    have hrel : (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i).val)*(u i).val)+
        (∑ k,rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v k)*
          rename Sum.inr (b k).val)+rename (Sum.map id (Fin.castAdd z)) (P t)=0 := by
      have hh := LinearMap.mem_ker.mp ht
      simpa only [bilinearKoszulRow,LinearMap.coe_mk,AddHom.coe_mk,
        fullBiformScalarProduct_apply,Q',E',P',LinearMap.comp_apply,AlgHom.toLinearMap_apply,mul_comm] using hh
    obtain ⟨C,hCu,hCb,hPt⟩ := extended_polynomial_row_relation_constants hs hsd o ho hdeg
      e v he Q P hfull hker ell hell (fun i => (u i).val) (fun i => (u i).property)
      b (P t) ⟨t,rfl⟩ (hP ⟨t,rfl⟩) hrel
    refine ⟨C,?_⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        apply Subtype.ext
        change (∑ k,C i k • E' k).val=(u i).val
        simpa only [Submodule.coe_sum,Submodule.coe_smul,E'] using (hCu i).symm
      · funext k
        apply Subtype.ext
        change (-∑ i,C i k • Q' i).val=(b k).val
        simpa only [Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,Q'] using (hCb k).symm
    · change 0=t
      exact (hPinj (hPt.trans (map_zero _).symm)).symm
  · rintro _ ⟨C,rfl⟩
    exact LinearMap.congr_fun (bilinearKoszulRow_constants fullBiformScalarProduct Q' E' P') C

end Froberg
