import Froberg.ProjectedOddTarget
import Froberg.ParityRangeQuotient
import Froberg.UpperTargetOpen

/-! Actual even-target coverage modulo a fixed even deletion is open in
the polynomial generator family. This remains applicable after a scalar
generator has been replaced by a scalar-plus-positive generator. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {n d r : ℕ}

/-- Add the odd projection as a fixed summand, so even coverage is ordinary
surjectivity onto the full homogeneous space. -/
def evenCoverageMap (D : Submodule K (Forms K n (2*d))) (w : Fin n → ZMod 2)
    (q : Fin r → Forms K n d) :
    ((D × (Fin r → Forms K n d)) × Forms K n (2*d)) →ₗ[K] Forms K n (2*d) :=
  (D.subtype.coprod (endpointMultiplication q)).coprod (parityForm w 1)

theorem evenCoverageMap_surjective_of_coverage
    (D : Submodule K (Forms K n (2*d))) (w : Fin n → ZMod 2)
    (q : Fin r → Forms K n d)
    (hc : ∀ p,parityForm w 0 p∈D ⊔ (endpointMultiplication q).range) :
    Function.Surjective (evenCoverageMap D w q) := by
  intro p
  obtain ⟨z,hz,y,⟨a,rfl⟩,he⟩ := Submodule.mem_sup.mp (hc p)
  refine ⟨((⟨z,hz⟩,a),p),?_⟩
  change (z+endpointMultiplication q a)+parityForm w 1 p=p
  rw [he]
  exact parityForm_decomposition w 0 p

theorem evenCoverageMap_coverage_of_surjective
    (D : Submodule K (Forms K n (2*d))) (w : Fin n → ZMod 2)
    (e : Fin r → ZMod 2) (q : Fin r → Forms K n d)
    (hD : D≤(parityForm w 1).ker)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (hc : Function.Surjective (evenCoverageMap D w q)) :
    ∀ p,parityForm w 0 p∈D ⊔ (endpointMultiplication q).range := by
  intro p
  obtain ⟨⟨⟨z,a⟩,v⟩,ha⟩ := hc p
  have hz : parityForm w 0 z.val=z.val := by
    have he := parityForm_decomposition w 0 z.val
    have hzero : parityForm w 1 z.val=0 := hD z.property
    simpa only [zero_add,hzero,add_zero] using he
  have hodd : parityForm w 0 (parityForm w 1 v)=0 :=
    parityForm_other w 0 1 _ (parityForm_homogeneous w 1 v) zero_ne_one
  have he := congrArg (parityForm w 0) ha
  change parityForm w 0 ((z.val+endpointMultiplication q a)+parityForm w 1 v)=parityForm w 0 p at he
  rw [map_add,map_add,hz,hodd,add_zero,←endpointMultiplication_paritySource w e q hq] at he
  rw [←he]
  exact Submodule.add_mem_sup z.property ⟨paritySource w e 0 a,rfl⟩

theorem evenCoverageMap_polynomial {I : Type*}
    (D : Submodule K (Forms K n (2*d))) (w : Fin n → ZMod 2)
    (q : (I → K) → Fin r → Forms K n d) (hq : IsPolynomialFamily q) :
    IsPolynomialFamily (fun p => evenCoverageMap D w (q p)) := by
  refine isPolynomialFamily_linearMap
    (V := (D × (Fin r → Forms K n d)) × Forms K n (2*d))
    (W := Forms K n (2*d)) (fun p => evenCoverageMap D w (q p)) ?_
  intro x
  let op : (Fin r → Forms K n d) →ₗ[K]
      ((Fin r → Forms K n d) →ₗ[K] Forms K n (2*d)) :=
    endpointMultiplicationOperator (K := K) (h := n) (m := 0) (d := d) (r := r)
  have hr := hq.linear_comp (W := (Fin r → Forms K n d) →ₗ[K] Forms K n (2*d)) op
  have he := hr.linear_comp (W := Forms K n (2*d)) (LinearMap.applyₗ (R := K) (M₂ := Forms K n (2*d)) x.1.2)
  exact ((isPolynomialFamily_const x.1.1.val).add he).add
    (isPolynomialFamily_const (parityForm w 1 x.2))

theorem even_coverage_principal_open {I : Type*}
    (D : Submodule K (Forms K n (2*d))) (w : Fin n → ZMod 2)
    (e : Fin r → ZMod 2) (q : (I → K) → Fin r → Forms K n d)
    (hq : IsPolynomialFamily q) (hD : D≤(parityForm w 1).ker)
    (hpar : ∀ p i,(q p i).val.IsWeightedHomogeneous w (e i))
    (p₀ : I → K)
    (hc : ∀ z,parityForm w 0 z∈D ⊔ (endpointMultiplication (q p₀)).range) :
    ∃ P : MvPolynomial I K,eval p₀ P≠0 ∧ ∀ p,eval p P≠0 →
      ∀ z,parityForm w 0 z∈D ⊔ (endpointMultiplication (q p)).range := by
  obtain ⟨P,hP,hgood⟩ := surjective_polynomial_principal_open
    (E := (D × (Fin r → Forms K n d)) × Forms K n (2*d))
    (T := Forms K n (2*d))
    (fun p => evenCoverageMap D w (q p)) (evenCoverageMap_polynomial D w q hq) p₀
    (evenCoverageMap_surjective_of_coverage D w (q p₀) hc)
  exact ⟨P,hP,fun p hp => evenCoverageMap_coverage_of_surjective D w e (q p) hD
    (hpar p) (hgood p hp)⟩

end Froberg
