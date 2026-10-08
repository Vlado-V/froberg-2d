import Froberg.BiformParitySpaces
import Froberg.OddHomogeneousComponents

/-! Linear odd-parity biform coordinates, with the actual weighted
component formula in each degree. This applies also to degree 2*d. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct Finset
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d : ℕ}

abbrev OddBiformCoordinates (K : Type) [Field K] (h m d : ℕ) :=
  (r : Fin ((d+1)/2)) → Forms K h (2*r.val+1) ⊗[K] Forms K m (d-(2*r.val+1))

def oddCoefficientAssembly : OddBiformCoordinates K h m d →ₗ[K] biformParitySpace K h m d 1 :=
  ∑ r : Fin ((d+1)/2),
    (oddBiformEmbedding (t := 2*r.val+1) (by omega) (by omega)).comp (LinearMap.proj r)

@[simp] theorem oddCoefficientAssembly_val (v : OddBiformCoordinates K h m d) :
    (oddCoefficientAssembly v).val=∑ r,sumBiformMap (v r) := by
  simp [oddCoefficientAssembly]

theorem oddCoefficientAssembly_component (v : OddBiformCoordinates K h m d)
    (r : Fin ((d+1)/2)) :
    weightedHomogeneousComponent (blockWeight h m) (2*r.val+1) (oddCoefficientAssembly v).val=
      sumBiformMap (v r) := by
  classical
  have hw (s : Fin ((d+1)/2)) :
      (sumBiformMap (v s)).IsWeightedHomogeneous (blockWeight h m) (2*s.val+1) := by
    apply biformImage_output_weight (Forms K h (2*s.val+1))
      (Forms K m (d-(2*s.val+1))) le_rfl
    exact sumBiformMap_range.le ⟨v s,rfl⟩
  rw [oddCoefficientAssembly_val,map_sum,sum_eq_single r]
  · exact (hw r).weightedHomogeneousComponent_same
  · intro s _ hsr
    exact (hw s).weightedHomogeneousComponent_ne _ (by
      intro he
      apply hsr
      apply Fin.ext
      omega)
  · simp

theorem oddCoefficientAssembly_injective :
    Function.Injective (oddCoefficientAssembly (K := K) (h := h) (m := m) (d := d)) := by
  intro v z he
  funext r
  apply sumBiformMap_injective
  have hh := congrArg (fun x : biformParitySpace K h m d 1 =>
    weightedHomogeneousComponent (blockWeight h m) (2*r.val+1) x.val) he
  simpa only [oddCoefficientAssembly_component] using hh

theorem oddCoefficientAssembly_surjective :
    Function.Surjective (oddCoefficientAssembly (K := K) (h := h) (m := m) (d := d)) := by
  intro v
  have hpar := (parity_homogeneous_iff (blockWeight h m) v.val 1 (by decide)).1 v.property.2
  have hex (r : Fin ((d+1)/2)) :
      ∃ z : Forms K h (2*r.val+1) ⊗[K] Forms K m (d-(2*r.val+1)),
        sumBiformMap z=weightedHomogeneousComponent (blockWeight h m) (2*r.val+1) v.val := by
    apply exists_sumBiformMap_of_homogeneous
    · have ht : 2*r.val+1≤d := by omega
      simpa only [Nat.add_sub_of_le ht] using
        weightedComponent_preserves_homogeneous (blockWeight h m) v.property.1 (2*r.val+1)
    · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  choose z hz using hex
  refine ⟨z,?_⟩
  apply Subtype.ext
  rw [oddCoefficientAssembly_val]
  simp only [hz]
  exact (odd_homogeneous_components (blockWeight h m)
    (by intro x; cases x <;> simp [blockWeight]) v.val v.property.1 hpar).symm

def oddBiformCoordinatesEquiv :
    biformParitySpace K h m d 1 ≃ₗ[K] OddBiformCoordinates K h m d :=
  (LinearEquiv.ofBijective oddCoefficientAssembly
    ⟨oddCoefficientAssembly_injective,oddCoefficientAssembly_surjective⟩).symm

@[simp] theorem oddBiformCoordinatesEquiv_symm_val (v : OddBiformCoordinates K h m d) :
    (oddBiformCoordinatesEquiv.symm v).val=∑ r,sumBiformMap (v r) :=
  oddCoefficientAssembly_val v

theorem oddBiformCoordinatesEquiv_component (v : biformParitySpace K h m d 1)
    (r : Fin ((d+1)/2)) :
    sumBiformMap (oddBiformCoordinatesEquiv v r)=
      weightedHomogeneousComponent (blockWeight h m) (2*r.val+1) v.val := by
  have hv : oddCoefficientAssembly (oddBiformCoordinatesEquiv v)=v :=
    (LinearEquiv.ofBijective oddCoefficientAssembly
      ⟨oddCoefficientAssembly_injective,oddCoefficientAssembly_surjective⟩).apply_symm_apply v
  have hc := oddCoefficientAssembly_component (oddBiformCoordinatesEquiv v) r
  rw [hv] at hc
  exact hc.symm

theorem finrank_odd_biform_space (hh : 0 < h) (hm : 0 < m) :
    finrank K (biformParitySpace K h m d 1)=
      ∑ r : Fin ((d+1)/2),
        (h+(2*r.val+1)-1).choose (2*r.val+1)*
          (m+(d-(2*r.val+1))-1).choose (d-(2*r.val+1)) := by
  rw [oddBiformCoordinatesEquiv.finrank_eq]
  simp only [OddBiformCoordinates,Module.finrank_pi_fintype,Module.finrank_tensorProduct,
    finrank_forms K h _ hh,finrank_forms K m _ hm]

end Froberg
