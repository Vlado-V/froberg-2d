module

public import Froberg.PrivateQuadraticSeparation
public import Froberg.FirstPrivateIntrinsicRow
public import Froberg.QuadraticSeparationRow
public import Froberg.ScalarCoefficientWitness
public import Froberg.HomogeneousRename

@[expose] public section

/-! The private-power quadratic witness in the actual biform coefficient
space. Basis coordinates transfer the checked scalar/private separation and
its constant Koszul kernel without changing the private columns. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {a z d b q h c : ℕ}

/-- Every actual biform coefficient has basis coordinates, and the selected
output detector becomes the coordinate private-power map. -/
theorem typed_private_quadratic_coordinates
    (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (w : Fin b → Fin h → K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (P : Fin b → FullBiform K σ (a+z) 1 (d-1))
    (hP : ∀ i,(P i).val=rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))
    (u : Fin b → FullBiform K σ (a+z) 1 (d-1)) :
    ∃ v : Fin b → Fin h → Forms K (a+z) (d-1),
      (∀ i,polynomialFormVector (fun k => (bo k).val) (d-1) (v i)=(u i).val) ∧
      PolynomialRestoration.row (FullBiform K σ (a+z) 1 (d-1)).subtype
        (biformVectorDetector T) P u=privatePolynomialMap ι A v := by
  have hu : ∀ i,(u i).val∈
      (polynomialFormVector (fun k => (bo k).val) (d-1)).range := by
    intro i
    rw [polynomialFormVector_range_basis]
    exact (u i).property
  choose v hv using hu
  refine ⟨v,hv,?_⟩
  change biformVectorDetector T (∑ i,(P i).val*(u i).val)=_
  simpa only [hP,hv] using biformVectorDetector_private T (fun k => (bo k).val)
    (fun i => outputCombination (fun k => (bo k).val) (w i)) ι A hA v

/-- Scalar/private nuisance coefficients cannot absorb a core product that
is already separated from the core scalar row. The private part vanishes
separately as well. -/
theorem typed_private_quadratic_row_separation (hd : 3≤d)
    (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (w : Fin b → Fin h → K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (P : Fin b → FullBiform K σ (a+z) 1 (d-1))
    (hP : ∀ i,(P i).val=rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))
    (Q : Fin q → Forms K a d)
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    (C : Z →ₗ[K] (Fin c → Poly K a))
    (hC : ∀ (x : Fin q → Fin c → Forms K a (d-2)) v,
      scalarCoefficientRow Q x+C v=0 → v=0)
    (x : (Fin q → Fin c → Forms K (a+z) (d-2)) ×
      (Fin b → FullBiform K σ (a+z) 1 (d-1))) (v : Z)
    (hrel : quadraticNuisanceRow (t := d-2)
      (FullBiform K σ (a+z) 1 (d-1)).subtype (biformVectorDetector T)
      (fun i => renameForm (Fin.castAdd z) (Q i)) P x+coreVectorExtension (C v)=0) :
    v=0 ∧ PolynomialRestoration.row (FullBiform K σ (a+z) 1 (d-1)).subtype
      (biformVectorDetector T) P x.2=0 := by
  obtain ⟨u,hu,hrow⟩ := typed_private_quadratic_coordinates bo T w ι A hA P hP x.2
  have hr : quadraticScalarRow (fun i => (Q i).val) x.1+
      privatePolynomialMap ι A u+coreVectorExtension (C v)=0 := by
    change scalarCoefficientRow (fun i => renameForm (Fin.castAdd z) (Q i)) x.1+
      PolynomialRestoration.row (FullBiform K σ (a+z) 1 (d-1)).subtype
        (biformVectorDetector T) P x.2+coreVectorExtension (C v)=0 at hrel
    rw [hrow] at hrel
    exact hrel
  have hh := private_core_product_separation (by omega : 2≤d-1) (by omega : d-2<d-1)
    ι A (fun i => (Q i).val) C (fun x v hv => hC x v hv) x.1 u v hr
  exact ⟨hh.1,hrow.trans hh.2⟩

/-- The actual quadratic nuisance row has exactly its constant private
Koszul boundary as kernel. -/
theorem typed_private_quadratic_row_exact (hd : 3≤d)
    (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (w : Fin b → Fin h → K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (hker : (privatePolynomialMap (a := a) (s := d-1) ι A).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := d-1) ι w))))
    (P : Fin b → FullBiform K σ (a+z) 1 (d-1))
    (hP : ∀ i,(P i).val=rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))
    (Q : Fin q → Forms K a d)
    (hQ : ∀ t,t≤d-2 → Function.Injective (prefixMultiplication Q t)) :
    (quadraticNuisanceRow (t := d-2)
      (FullBiform K σ (a+z) 1 (d-1)).subtype (biformVectorDetector T)
      (fun i => renameForm (Fin.castAdd z) (Q i)) P).ker=
      (quadraticNuisanceBoundary (q := q) (c := c) (n := a+z) (t := d-2) P).range := by
  apply le_antisymm
  · rintro ⟨x,u⟩ hxu
    change quadraticNuisanceRow (t := d-2)
      (FullBiform K σ (a+z) 1 (d-1)).subtype (biformVectorDetector T)
      (fun i => renameForm (Fin.castAdd z) (Q i)) P (x,u)=0 at hxu
    have hrow0 := (typed_private_quadratic_row_separation hd bo T w ι A hA P hP Q
      (0 : (Fin 0 → K) →ₗ[K] (Fin c → Poly K a))
      (fun _ v _ => Subsingleton.elim v 0) (x,u) 0 (by
        simpa only [LinearMap.zero_apply,map_zero,add_zero] using hxu)).2
    have hx : quadraticScalarRow (fun i => (Q i).val) x=0 := by
      change scalarCoefficientRow (fun i => renameForm (Fin.castAdd z) (Q i)) x+
        PolynomialRestoration.row (FullBiform K σ (a+z) 1 (d-1)).subtype
          (biformVectorDetector T) P u=0 at hxu
      rw [hrow0,add_zero] at hxu
      exact hxu
    have hx0 : x=0 := quadraticScalarRow_injective (fun i => (Q i).val)
      (fun t ht y hy => prefix_injective_sum_eq_zero Q (hQ t ht) y hy)
      (hx.trans (map_zero _).symm)
    subst x
    obtain ⟨v,hv,hrow⟩ := typed_private_quadratic_coordinates bo T w ι A hA P hP u
    have hv0 : privatePolynomialMap ι A v=0 := hrow.symm.trans hrow0
    have hboundary : (fun i => (u i).val)∈
        Submodule.span K (Set.range (koszulVector (fun i => (P i).val))) := by
      simpa only [hP,hv] using private_boundary_polynomial
        (fun k => (bo k).val) ι A w hker v hv0
    obtain ⟨M,hM⟩ := exists_matrixBoundary_of_mem_koszul
      (fun i => (P i).val) (fun i => (u i).val) hboundary
    refine ⟨M,?_⟩
    apply Prod.ext
    · rfl
    · change PolynomialRestoration.boundary P M=u
      funext i
      apply Subtype.ext
      change (FullBiform K σ (a+z) 1 (d-1)).subtype (coefficientBoundary P M i)=_
      rw [coefficientBoundary_map]
      exact congrFun hM i
  · rintro _ ⟨M,rfl⟩
    exact LinearMap.congr_fun (quadraticNuisanceRow_boundary
      (FullBiform K σ (a+z) 1 (d-1)).subtype (biformVectorDetector T)
      (fun i => renameForm (Fin.castAdd z) (Q i)) P) M

end Froberg
