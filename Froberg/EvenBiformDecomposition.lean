module

public import Froberg.BiformActionPolynomial
public import Froberg.EvenHomogeneousComponents

@[expose] public section

/-! All even coefficients of an odd-degree form are its scalar coefficient
and the actual positive even biforms in C.13. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial TensorProduct Finset
variable {K : Type} [Field K] [Infinite K] {σ : Type*} {d h m : ℕ}

theorem even_homogeneous_biform_decomposition (hd : Odd d)
    (f : MvPolynomial (Fin h ⊕ Fin m) K) (hf : f.IsHomogeneous d)
    (heven : ∀ a,f.coeff a≠0 →
      Finsupp.weight (Sum.elim (fun _ : Fin h => 1) (fun _ : Fin m => 0)) a%2=0) :
    ∃ z : Forms K h 0 ⊗[K] Forms K m d,
    ∃ v : (r : Fin ((d-1)/2)) → Forms K h (2*(r.val+1)) ⊗[K] Forms K m (d-2*(r.val+1)),
      f=sumBiformMap z+∑ r,sumBiformMap (v r) := by
  let w : Fin h ⊕ Fin m → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)
  have hbound (r : Fin ((d-1)/2)) : 2*(r.val+1)≤d := by omega
  obtain ⟨z,hz⟩ := exists_sumBiformMap_of_homogeneous (a := 0) (c := d)
    (by simpa only [zero_add] using weightedComponent_preserves_homogeneous w hf 0)
    (weightedHomogeneousComponent_isWeightedHomogeneous 0 f)
  have hv (r : Fin ((d-1)/2)) :
      ∃ v : Forms K h (2*(r.val+1)) ⊗[K] Forms K m (d-2*(r.val+1)),
        sumBiformMap v=weightedHomogeneousComponent w (2*(r.val+1)) f := by
    apply exists_sumBiformMap_of_homogeneous
    · simpa only [Nat.add_sub_of_le (hbound r)] using
        weightedComponent_preserves_homogeneous w hf (2*(r.val+1))
    · exact weightedHomogeneousComponent_isWeightedHomogeneous _ f
  choose v hv using hv
  refine ⟨z,v,?_⟩
  simp only [hz,hv]
  exact even_homogeneous_components w (by intro x; cases x <;> simp [w]) hd f hf heven

end Froberg
