module

public import Froberg.HigherOddVectorOpen
public import Froberg.PolynomialComplexOpen
public import Froberg.StrictScalarJointSelection

@[expose] public section

/-! Exactness of the first vector row is a genuine principal open in the
joint vector/scalar coefficients. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f t : ℕ}

def FirstVectorRowExact (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) : Prop :=
  (bilinearKoszulRow multiplication Q g
    (0 : (Fin 0 → K) →ₗ[K] Rows K h m ((d-1)+d))).ker=
    (bilinearKoszulConstants (W := Fin 0 → K) Q g).range

theorem firstVectorRow_constants (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (hex : FirstVectorRowExact Q g)
    (x : Fin q → Rows K h m (d-1)) (y : Fin f → Forms K m d)
    (hr : (∑ i,multiplication (Q i) (x i))+(∑ j,multiplication (y j) (g j))=0) :
    ∃ C : Fin q → Fin f → K,
      (∀ i,x i=∑ j,C i j • g j) ∧ (∀ j,y j = -∑ i,C i j • Q i) := by
  have hw : ((x,y),(0 : Fin 0 → K))∈(bilinearKoszulRow multiplication Q g
      (0 : (Fin 0 → K) →ₗ[K] Rows K h m ((d-1)+d))).ker := by
    change (∑ i,multiplication (Q i) (x i))+(∑ j,multiplication (y j) (g j))+0=0
    simpa only [add_zero] using hr
  rw [hex] at hw
  obtain ⟨C,hC⟩ := hw
  exact ⟨C,fun i => (congrArg (fun z => z.1.1 i) hC).symm,
    fun j => (congrArg (fun z => z.1.2 j) hC).symm⟩

theorem firstVectorRowExact_of_quotient (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
    (hg : Function.Injective (BilinearImage.tupleMap (multiplication (d := d)) g))
    (hQ : Function.Injective (BilinearScalarFamily.multiplication
      (VectorExpansionOpen.quotientMultiplication g d) Q)) : FirstVectorRowExact Q g := by
  classical
  apply le_antisymm
  · rintro ⟨⟨x,y⟩,w⟩ hw
    have hr : (∑ i,multiplication (Q i) (x i))+(∑ j,multiplication (y j) (g j))=0 := by
      change (∑ i,multiplication (Q i) (x i))+(∑ j,multiplication (y j) (g j))+0=0 at hw
      simpa only [add_zero] using hw
    obtain ⟨C,hC,hC'⟩ := scalar_layer_constants_of_quotient_injective multiplication Q g hg hQ x y hr
    refine ⟨C,Prod.ext (Prod.ext (funext (fun i => (hC i).symm)) (funext (fun j => (hC' j).symm))) (Subsingleton.elim _ _)⟩
  · rintro z ⟨C,rfl⟩
    exact LinearMap.congr_fun (bilinearKoszulRow_constants multiplication Q g
      (0 : (Fin 0 → K) →ₗ[K] Rows K h m ((d-1)+d))) C

theorem first_vector_row_open (p₀ : ScalarVectorParameters K h m d f q)
    (hex : FirstVectorRowExact p₀.2 p₀.1) :
    ∃ D : MvPolynomial (Fin (finrank K (ScalarVectorParameters K h m d f q))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ p : ScalarVectorParameters K h m d f q,
        eval ((Module.finBasis K _).equivFun p) D≠0 → FirstVectorRowExact p.2 p.1 := by
  let S := ScalarVectorParameters K h m d f q
  let e := (Module.finBasis K S).equivFun
  let Q := fun i a => (e.symm a).2 i
  let E := fun j a => (e.symm a).1 j
  let Z := (0 : (Fin 0 → K) →ₗ[K] Rows K h m ((d-1)+d))
  have hQ (i) : IsPolynomialFamily (Q i) :=
    isPolynomialFamily_linear ((LinearMap.proj i).comp ((LinearMap.snd K _ _).comp e.symm.toLinearMap))
  have hE (j) : IsPolynomialFamily (E j) :=
    isPolynomialFamily_linear ((LinearMap.proj j).comp ((LinearMap.fst K _ _).comp e.symm.toLinearMap))
  obtain ⟨D,hD,hgood⟩ := complex_exact_principal_open
    (fun a => bilinearKoszulRow multiplication (fun i => Q i a) (fun j => E j a) Z)
    (fun a => bilinearKoszulConstants (W := Fin 0 → K) (fun i => Q i a) (fun j => E j a))
    (bilinearKoszulRow_polynomial multiplication Q E (fun _ => Z) hQ hE (isPolynomialFamily_const Z))
    (bilinearKoszulConstants_polynomial Q E hQ hE)
    (fun a => bilinearKoszulRow_constants multiplication _ _ Z) (e p₀)
    (by simpa only [Q,E,Z,FirstVectorRowExact,LinearEquiv.symm_apply_apply] using hex)
  refine ⟨D,hD,?_⟩
  intro p hp
  simpa only [Q,E,Z,FirstVectorRowExact,LinearEquiv.symm_apply_apply] using hgood (e p) hp

end Froberg
