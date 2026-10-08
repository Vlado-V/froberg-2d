import Froberg.OddScalarParameters
import Froberg.BottomPolynomialConstants
import Froberg.OddPolynomialRows
import Froberg.EmptyCoefficientRows

/-! A common open in actual vector/scalar parameters eliminates every
higher odd coefficient row, including the final scalar-free row. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f t : ℕ}

abbrev ScalarVectorParameters (K : Type) [Field K] (h m d f q : ℕ) :=
  (Fin f → Rows K h m (d-1)) × (Fin q → Forms K m d)

def scalarVectorParametersEquiv : ScalarVectorParameters K h m d f q ≃ₗ[K]
    OddScalarParameters K h m d f q :=
  LinearEquiv.prodCongr (LinearEquiv.piCongrRight (fun _ => linearOutputTensorEquiv))
    (LinearEquiv.refl K _)

def HigherOddRows (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) : Prop :=
  ∀ r,3≤r → r≤d+1 → r%2=1 →
    ∀ (u : Fin q → MvPolynomial (Fin h ⊕ Fin m) K)
      (v : Fin f → MvPolynomial (Fin h ⊕ Fin m) K),
      (∀ i,u i∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d r) →
      (∀ j,v j∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d (r-1)) →
      (∑ i,rename Sum.inr (Q i).val*u i)+
        (∑ j,sumBiformMap (linearOutputTensorEquiv (g j))*v j)=0 → u=0 ∧ v=0

theorem odd_scalar_layer_polynomial_row {b : ℕ} (hb : 1≤b) (hbd : b≤d)
    (p : OddScalarParameters K h m d f q)
    (hp : OddScalarLayerProperty t hb hbd (oddScalarBiformParameters p))
    (u : Fin q → MvPolynomial (Fin h ⊕ Fin m) K)
    (v : Fin f → MvPolynomial (Fin h ⊕ Fin m) K)
    (hu : ∀ i,u i∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d b)
    (hv : ∀ j,v j∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d (b-1))
    (hrow : (∑ i,rename Sum.inr (p.2 i).val*u i)+(∑ j,sumBiformMap (p.1 j)*v j)=0) :
    u=0 ∧ v=0 := by
  have hinj := hp.1
  refine higher_odd_polynomial_row hb hbd (fun i => scalarBiformEquiv (p.2 i),p.1) ?_ u v hu hv ?_
  · intro x y he
    rw [twoFamilyMultiplication_apply,twoFamilyMultiplication_apply] at he
    have he' : twoFamilyMultiplication
        (oddRowLinearAction (K := K) (h := h) (n := m) hb hbd)
        (oddRowScalarAction (K := K) (h := h) (n := m) hbd)
        (oddScalarBiformParameters p) (x.2,x.1)=
      twoFamilyMultiplication (oddRowLinearAction (K := K) (h := h) (n := m) hb hbd)
        (oddRowScalarAction (K := K) (h := h) (n := m) hbd)
        (oddScalarBiformParameters p) (y.2,y.1) := by
      rw [twoFamilyMultiplication_apply,twoFamilyMultiplication_apply]
      change
        (∑ j,oddRowLinearAction hb hbd (p.1 j) (x.2 j))+
          (∑ i,oddRowScalarAction hbd (scalarBiformEquiv (p.2 i)) (x.1 i))=
        (∑ j,oddRowLinearAction hb hbd (p.1 j) (y.2 j))+
          (∑ i,oddRowScalarAction hbd (scalarBiformEquiv (p.2 i)) (y.1 i))
      calc
        _ = (∑ i,oddRowScalarAction hbd (scalarBiformEquiv (p.2 i)) (x.1 i))+
          (∑ j,oddRowLinearAction hb hbd (p.1 j) (x.2 j)) := add_comm _ _
        _ = (∑ i,oddRowScalarAction hbd (scalarBiformEquiv (p.2 i)) (y.1 i))+
          (∑ j,oddRowLinearAction hb hbd (p.1 j) (y.2 j)) := he
        _ = _ := add_comm _ _
    have hh := hinj he'
    exact Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh)
  · simpa only [sumBiformMap_scalarBiform] using hrow

theorem higher_odd_vector_open (hh : 0<h) (hm : 0 < m) (hd : 1≤d)
    (hscalar : HasOddScalarLayersOpen K h m d f q t)
    (hupper : (f+(h+d-1).choose d)*(h+d-1).choose d≤
      (h+(d+1)-1).choose (d+1)*(m+(d-1)-1).choose (d-1)) :
    ∃ D : MvPolynomial (Fin (finrank K (ScalarVectorParameters K h m d f q))) K,
      (∃ p : ScalarVectorParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : ScalarVectorParameters K h m d f q,
        eval ((Module.finBasis K _).equivFun p) D≠0 → HigherOddRows p.2 p.1 := by
  classical
  let V := ScalarVectorParameters K h m d f q
  let e := scalarVectorParametersEquiv (K := K) (h := h) (m := m) (d := d) (f := f) (q := q)
  obtain ⟨D,hD,hgood⟩ := odd_scalar_forms_open hscalar
  obtain ⟨P,hP,hPgood⟩ := principal_open_linear_pullback e.toLinearMap e.surjective D hD _ hgood
  obtain ⟨E,hE,hEgood⟩ := upper_odd_biform_open (K := K) hh hm hd hupper
  let F : V →ₗ[K] (Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
    (LinearMap.fst K _ _).comp e.toLinearMap
  have hF : Function.Surjective F := by
    intro g
    exact ⟨e.symm (g,0),by change (e (e.symm (g,0))).1=g; rw [LinearEquiv.apply_symm_apply]⟩
  obtain ⟨P',hP',hP'good⟩ := principal_open_linear_pullback F hF E hE _ hEgood
  obtain ⟨x,hx,hx'⟩ := principal_opens_intersect
    (show ∃ x,eval x P≠0 from by obtain ⟨p,hp⟩ := hP; exact ⟨_,hp⟩)
    (show ∃ x,eval x P'≠0 from by obtain ⟨p,hp⟩ := hP'; exact ⟨_,hp⟩)
  refine ⟨P*P',⟨(Module.finBasis K V).equivFun.symm x,?_⟩,?_⟩
  · simpa only [V,LinearEquiv.apply_symm_apply,map_mul] using mul_ne_zero hx hx'
  intro p hp r hr hrd hodd u v hu hv hrow
  have hps : eval ((Module.finBasis K V).equivFun p) P≠0 ∧
      eval ((Module.finBasis K V).equivFun p) P'≠0 := by simpa only [map_mul,mul_ne_zero_iff] using hp
  by_cases hrd' : r≤d
  · exact odd_scalar_layer_polynomial_row (by omega) hrd' (e p)
      (hPgood p hps.1 r hr hrd') u v hu hv hrow
  · have hre : r=d+1 := by omega
    have hu0 : u=0 := by
      funext i
      have hui := hu i
      rw [coefficientComponentSpace_above _ (by intro x; cases x <;> simp) (by omega : d<r)] at hui
      exact hui
    refine ⟨hu0,?_⟩
    apply upper_odd_polynomial_row hd (F p) (hP'good p hps.2) v
    · intro j
      simpa only [hre,Nat.add_sub_cancel] using hv j
    · change (∑ j,sumBiformMap (linearOutputTensorEquiv (p.1 j))*v j)=0
      simpa only [hu0,Pi.zero_apply,mul_zero,Finset.sum_const_zero,zero_add] using hrow

end Froberg
