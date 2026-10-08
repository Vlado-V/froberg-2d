import Froberg.ParityComplex
import Froberg.ProjectedHomologyCoefficients

/-! The new-generator coefficient map lands in the odd quotient, after
actual odd-cycle exactness has supplied even representatives. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial
variable {K : Type} [Field K] {n d r t : ℕ}

/-- A span of parity-homogeneous generators is preserved by each monomial projection. -/
theorem parity_preserves_generator_span
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (p : ZMod 2) :
    Submodule.span K (Set.range q) ≤
      (Submodule.span K (Set.range q)).comap (parityForm w p) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change parityForm w p (q i) ∈ Submodule.span K (Set.range q)
  by_cases he : p=e i
  · rw [he,parityForm_same w (e i) (q i) (hq i)]
    exact Submodule.subset_span ⟨i,rfl⟩
  · rw [parityForm_other w p (e i) (q i) (hq i) he]
    exact Submodule.zero_mem _

/-- Monomial parity descends to the actual degree-d generator quotient. -/
def parityGeneratorQuotient
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (p : ZMod 2) :
    (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K]
      (Forms K n d ⧸ Submodule.span K (Set.range q)) :=
  (Submodule.span K (Set.range q)).mapQ (Submodule.span K (Set.range q))
    (parityForm w p) (parity_preserves_generator_span w e q hq p)

@[simp] theorem parityGeneratorQuotient_mk
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (p : ZMod 2) (a : Forms K n d) :
    parityGeneratorQuotient w e q hq p ((Submodule.span K (Set.range q)).mkQ a) =
      (Submodule.span K (Set.range q)).mkQ (parityForm w p a) := rfl

variable {Z : Type*} [AddCommGroup Z] [Module K Z]

/-- Odd projection preserves the complete new-generator coefficient map,
so it cannot introduce an extra coefficient kernel. -/
theorem projectedHomologyCoefficients_odd
    (htwo : (2 : K) ≠ 0)
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hi : LinearIndependent K q)
    (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z, pi z=0 → parityForm w 1 z=0)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i, (a.val i).val.IsWeightedHomogeneous w (1-e i)) →
      a.val ∈ oppositeKoszulSpace q e)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdual : ∀ i j, e j=0 → dual i (q j)=0)
    (x : ProjectedEndpointHomology pi q) (i : Fin t) :
    parityGeneratorQuotient w e q hq 1
      (projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual x i) =
      projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual x i := by
  obtain ⟨a,ha,rfl⟩ := exists_even_projected_cycle_representative w e q hq pi hpi hodd x
  rw [projectedHomologyCoefficients_mk htwo pi q hi (Submodule.span K (Set.range q))
    (fun j => (Submodule.subset_span (s := Set.range q) ⟨j,rfl⟩)) dual a]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : e j=0
  · rw [hdual i j hj,zero_smul,zero_smul]
  · have hj' : e j=1 := by
      generalize hh : e j=v at hj ⊢
      fin_cases v <;> norm_num at *
    rw [parityGeneratorQuotient_mk]
    have hjpar : (a.val j).val.IsWeightedHomogeneous w 1 := by
      simpa only [hj',show (0 : ZMod 2)-1=1 by decide] using ha j
    rw [parityForm_same w 1 (a.val j) hjpar]

/-- The odd projection therefore preserves the actual retained coefficient kernel. -/
theorem projectedHomologyCoefficients_odd_kernel
    (htwo : (2 : K) ≠ 0)
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hi : LinearIndependent K q)
    (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z, pi z=0 → parityForm w 1 z=0)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i, (a.val i).val.IsWeightedHomogeneous w (1-e i)) →
      a.val ∈ oppositeKoszulSpace q e)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdual : ∀ i j, e j=0 → dual i (q j)=0) :
    (((parityGeneratorQuotient w e q hq 1).compLeft (Fin t)).comp
      (projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual)).ker =
      (projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual).ker := by
  congr 1
  apply LinearMap.ext
  intro x
  funext i
  exact projectedHomologyCoefficients_odd htwo w e q hi hq pi hpi hodd dual hdual x i

end Froberg
