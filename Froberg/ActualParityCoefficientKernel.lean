module

public import Froberg.ActualThinProjectedNormal
public import Froberg.OddQuotientProduct
public import Froberg.SeparatedGeneratorIndependence

@[expose] public section

/-! The retained coefficient kernel in the actual odd source quotient.
Any linear coordinates on that quotient preserve the same kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K : Type} [Field K] {n d r t : ℕ}
variable {Z V : Type*} [AddCommGroup Z] [Module K Z]
  [AddCommGroup V] [Module K V]

def oddCoefficientProjection (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i)) :
    generatorQuotient q →ₗ[K] oddCoefficientSpace w q :=
  (parityGeneratorQuotient w e q hq 1).codRestrict _ (by
    intro x
    rw [oddCoefficientSpace_eq_range w e q hq]
    exact LinearMap.mem_range_self _ x)

@[simp] theorem oddCoefficientProjection_val
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (x : generatorQuotient q) :
    (oddCoefficientProjection w e q hq x).val=parityGeneratorQuotient w e q hq 1 x := rfl

theorem actual_odd_coefficient_kernel (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hi : LinearIndependent K q)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z,pi z=0 → parityForm w 1 z=0)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous w (1-e i)) → a.val∈oppositeKoszulSpace q e)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdual : ∀ i j,e j=0 → dual i (q j)=0)
    (coords : oddCoefficientSpace w q ≃ₗ[K] V) :
    (actualProjectedMappedCoefficients pi q hi dual
      (coords.toLinearMap.comp (oddCoefficientProjection w e q hq))).ker=
      (projectedHomologyCoefficients pi q hi (Submodule.span K (Set.range q)) dual).ker := by
  ext x
  constructor
  · intro hx
    change projectedHomologyCoefficients pi q hi (Submodule.span K (Set.range q)) dual x=0
    funext i
    have hx' := congrFun hx i
    change coords (oddCoefficientProjection w e q hq
      (projectedHomologyCoefficients pi q hi (Submodule.span K (Set.range q)) dual x i))=0 at hx'
    have hz := coords.map_eq_zero_iff.mp hx'
    have hv := congrArg Subtype.val hz
    change parityGeneratorQuotient w e q hq 1
      (projectedHomologyCoefficients pi q hi (Submodule.span K (Set.range q)) dual x i)=0 at hv
    rw [projectedHomologyCoefficients_odd w e q hi hq pi hpi hodd dual hdual] at hv
    exact hv
  · intro hx
    change ((coords.toLinearMap.comp (oddCoefficientProjection w e q hq)).compLeft (Fin t))
      (projectedHomologyCoefficients pi q hi (Submodule.span K (Set.range q)) dual x)=0
    rw [show projectedHomologyCoefficients pi q hi (Submodule.span K (Set.range q)) dual x=0 from hx,
      map_zero]

/-- C.2 separation constructs the duals and identifies the retained kernel
after passing to the actual odd quotient used by the growth argument. -/
theorem exists_actual_odd_retained_kernel (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hi : LinearIndependent K q)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z,pi z=0 → parityForm w 1 z=0)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous w (1-e i)) → a.val∈oppositeKoszulSpace q e)
    (T : Submodule K (Forms K n d)) (f : Fin t → Forms K n d)
    (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range q)=T ⊔ Submodule.span K (Set.range f))
    (heven : ∀ j,e j=0 → q j∈T)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed T).map (pi.comp formalPolynomialMultiplication)).comap
        (pi.comp (formalPolynomialMultiplication (K := K) (n := n) (d := d)))=⊥)
    (coords : oddCoefficientSpace w q ≃ₗ[K] V) :
    ∃ dual : Fin t → Forms K n d →ₗ[K] K,
      (∀ i x,x∈T → dual i x=0) ∧
      (∀ i j,dual i (f j)=if i=j then 1 else 0) ∧
      (actualProjectedMappedCoefficients pi q hi dual
        (coords.toLinearMap.comp (oddCoefficientProjection w e q hq))).ker=
        projectedRetainedHomology pi q hi T := by
  classical
  obtain ⟨dual,hdT,hdF⟩ := exists_relative_coordinate_functionals T f
    (linearIndependent_quotient_of_formalSquare_separated
      (pi.comp formalPolynomialMultiplication) T f hf hsep)
  refine ⟨dual,hdT,hdF,?_⟩
  rw [actual_odd_coefficient_kernel w e q hi hq pi hpi hodd dual
    (fun i j hj => hdT i (q j) (heven j hj)) coords]
  have hker := projectedHomologyCoefficients_kernel pi q hi T f hspan dual hdT hdF hsep
  exact (congrArg (fun G : Submodule K (Forms K n d) =>
    (projectedHomologyCoefficients pi q hi G dual).ker) hspan).trans hker

end Froberg
