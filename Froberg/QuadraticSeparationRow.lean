import Froberg.SeparatedComplexOpen
import Froberg.PolynomialFamilyRestoration
import Froberg.BiformVectorDetector

/-! The complete polynomial row for C.2 consists of scalar coefficients,
private coefficients, and the outer symmetric products. Its only mandatory
kernel is the private constant Koszul boundary. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {I σ V Z Y : Type*}
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
variable [AddCommGroup Y] [Module K Y]
variable {n d t c q b f : ℕ}

def scalarCoefficientRow (Q : Fin q → Forms K n d) :
    (Fin q → Fin c → Forms K n t) →ₗ[K] (Fin c → Poly K n) where
  toFun x k := ∑ i,(Q i).val*(x i k).val
  map_add' x y := by
    funext k
    simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' r x := by
    funext k
    simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

def scalarCoefficientRowInFamily (x : Fin q → Fin c → Forms K n t) :
    (Fin q → Forms K n d) →ₗ[K] (Fin c → Poly K n) where
  toFun Q := scalarCoefficientRow Q x
  map_add' Q R := by
    funext k
    simp only [scalarCoefficientRow,LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,
      Submodule.coe_add,add_mul,Finset.sum_add_distrib]
  map_smul' r Q := by
    funext k
    simp only [scalarCoefficientRow,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,
      Submodule.coe_smul,smul_mul_assoc,Finset.smul_sum,RingHom.id_apply]

def quadraticNuisanceRow (j : V →ₗ[K] MvPolynomial σ K)
    (T : MvPolynomial σ K →ₗ[K] (Fin c → Poly K n))
    (Q : Fin q → Forms K n d) (P : Fin b → V) :
    ((Fin q → Fin c → Forms K n t) × (Fin b → V)) →ₗ[K] (Fin c → Poly K n) :=
  addRow (scalarCoefficientRow Q) (PolynomialRestoration.row j T P)

def quadraticNuisanceBoundary (P : Fin b → V) :
    (Fin b → Fin b → K) →ₗ[K] ((Fin q → Fin c → Forms K n t) × (Fin b → V)) :=
  (LinearMap.inr K _ _).comp (PolynomialRestoration.boundary P)

theorem quadraticNuisanceRow_boundary
    (j : V →ₗ[K] MvPolynomial σ K)
    (T : MvPolynomial σ K →ₗ[K] (Fin c → Poly K n))
    (Q : Fin q → Forms K n d) (P : Fin b → V) :
    (quadraticNuisanceRow (t := t) j T Q P).comp
      (quadraticNuisanceBoundary P)=0 := by
  apply LinearMap.ext
  intro M
  change scalarCoefficientRow Q 0+PolynomialRestoration.row j T P
    (PolynomialRestoration.boundary P M)=0
  rw [map_zero,zero_add,PolynomialRestoration.row_boundary]

theorem quadratic_nuisance_separation_open
    (j : V →ₗ[K] MvPolynomial σ K)
    (T : MvPolynomial σ K →ₗ[K] (Fin c → Poly K n))
    (Q : (I → K) → Fin q → Forms K n d) (P : (I → K) → Fin b → V)
    (C : (I → K) → Z →ₗ[K] (Fin c → Poly K n))
    (hQ : IsPolynomialFamily Q) (hP : IsPolynomialFamily P) (hC : IsPolynomialFamily C)
    (p₀ : I → K)
    (hexact : (quadraticNuisanceRow (t := t) j T (Q p₀) (P p₀)).ker=
      (quadraticNuisanceBoundary (P p₀)).range)
    (hsep : ∀ x z,quadraticNuisanceRow (t := t) j T (Q p₀) (P p₀) x+C p₀ z=0 → z=0) :
    ∃ G : MvPolynomial I K,eval p₀ G≠0 ∧
      ∀ p,eval p G≠0 → ∀ x z,
        quadraticNuisanceRow (t := t) j T (Q p) (P p) x+C p z=0 → z=0 := by
  have hrow : IsPolynomialFamily (fun p => quadraticNuisanceRow (t := t) j T (Q p) (P p)) := by
    apply isPolynomialFamily_linearMap
    intro x
    exact (hQ.linear_comp (scalarCoefficientRowInFamily x.1)).add
      ((PolynomialRestoration.row_polynomial j T P hP).linear_comp
        (LinearMap.applyₗ (R := K) x.2))
  have hboundary : IsPolynomialFamily (fun p =>
      quadraticNuisanceBoundary (K := K) (q := q) (c := c) (n := n) (t := t) (P p)) := by
    apply isPolynomialFamily_linearMap
    intro M
    exact (isPolynomialFamily_const (0 : Fin q → Fin c → Forms K n t)).prod_mk
      (hP.linear_comp (PolynomialRestoration.boundaryInFamily M))
  exact separated_complex_principal_open _ _ C hrow hboundary hC
    (fun p => quadraticNuisanceRow_boundary j T (Q p) (P p)) p₀ hexact hsep

def detectedSymmetricProductRow (j : V →ₗ[K] MvPolynomial σ K)
    (T : MvPolynomial σ K →ₗ[K] Y) (F : Fin f → V) :
    (Sym2 (Fin f) → K) →ₗ[K] Y where
  toFun a := ∑ p,a p • T (pairProducts (fun i => j (F i)) p)
  map_add' a b := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a b := by simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

private def detectedProductBilinear (j : V →ₗ[K] MvPolynomial σ K)
    (T : MvPolynomial σ K →ₗ[K] Y) : V →ₗ[K] V →ₗ[K] Y where
  toFun x :=
    { toFun := fun y => T (j x*j y)
      map_add' := by intros;simp only [map_add,mul_add]
      map_smul' := by intros;simp only [map_smul,mul_smul_comm,RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,map_add,add_mul]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro z
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,map_smul,
      smul_mul_assoc,RingHom.id_apply]

theorem detectedSymmetricProductRow_polynomial
    (j : V →ₗ[K] MvPolynomial σ K) (T : MvPolynomial σ K →ₗ[K] Y)
    (F : (I → K) → Fin f → V) (hF : IsPolynomialFamily F) :
    IsPolynomialFamily (fun p => detectedSymmetricProductRow j T (F p)) := by
  have hprod (s : Sym2 (Fin f)) :
      IsPolynomialFamily (fun p => T (pairProducts (fun i => j (F p i)) s)) := by
    induction s using Sym2.inductionOn with
    | _ i k =>
      exact (hF.linear_comp (LinearMap.proj i)).bilinear
        (hF.linear_comp (LinearMap.proj k)) (detectedProductBilinear j T)
  apply isPolynomialFamily_linearMap
  intro a
  exact IsPolynomialFamily.sum (fun s => (isPolynomialFamily_const (a s)).smul (hprod s))

end Froberg
