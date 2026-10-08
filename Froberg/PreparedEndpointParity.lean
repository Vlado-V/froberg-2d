import Froberg.PreparedOddEndpoint
import Froberg.PreparedEvenRestoration

/-! The full prepared family has the stated generator parities in the
ordinary endpoint ring, and its split-cycle statement applies to the same
full-parameter family used by the target open. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem zeroScalarEndpointFamily_eq_full (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f) :
    zeroScalarEndpointFamily hd hO hJ U P p=
      enumerateForms (FullPreparedParameters.forms hd hO hJ
        (FullPreparedParameters.pureBase U+FullPreparedParameters.variablePrivateZeroScalar (P,p))) := by
  rw [FullPreparedParameters.pureBase_add_variablePrivateZeroScalar]
  rfl

theorem oddGenerator_parity (hdodd : d%2=1)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) (k : Fin f ⊕ Fin u) :
    oddGenerator U P F k∈weightedParitySpace (blockWeight h m) 1 := by
  apply (weightedParitySpace (blockWeight h m) 1).add_mem
  · apply IsWeightedHomogeneous.mem_parity (j := 1) _ rfl
    cases k with
    | inl k => exact biformImage_output_weight _ _ le_rfl (F k).property
    | inr k => exact biformImage_output_weight _ _ le_rfl (P k).property
  · cases k with
    | inl k => exact Submodule.zero_mem _
    | inr k =>
      apply IsWeightedHomogeneous.mem_parity (j := d) _ hdodd
      exact rename_weightedHomogeneous
        (⟨Sum.inl,Sum.inl_injective⟩ : Fin h ↪ Fin h ⊕ Fin m)
        (fun _ => 1) (blockWeight h m) (fun _ => rfl) (U k).property

theorem zeroScalarEndpointFamily_parity (hd : 0<d) (hdodd : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (k : Fin (Fintype.card (Label q f u J counts))) :
    (zeroScalarEndpointFamily hd hO hJ U P p k).val.IsWeightedHomogeneous (coreParity h m)
      (endpointSplitParity (q := q) (f := f) (u := u) (J := J) (counts := counts) k) := by
  let idx := Fintype.equivFin (Label q f u J counts)
  obtain ⟨i,rfl⟩ := idx.surjective k
  let G := Sum.elim (PreparedParameters.generator p.1) (oddGenerator U P p.2)
  have hg : (G i).IsWeightedHomogeneous (fun x => (blockWeight h m x : ZMod 2)) (splitParity i) := by
    cases i with
    | inl i =>
      apply (parity_homogeneous_iff (blockWeight h m) (G (Sum.inl i)) 0 (by decide)).mpr
      exact (mem_weightedParitySpace_iff _ _ _).mp (PreparedParameters.generator_even hO heven p.1 i)
    | inr j =>
      apply (parity_homogeneous_iff (blockWeight h m) (G (Sum.inr j)) 1 (by decide)).mpr
      exact (mem_weightedParitySpace_iff _ _ _).mp (oddGenerator_parity hdodd U P p.2 j)
  have hrename : rename finSumFinEquiv (G i)=(zeroScalarEndpointFamily hd hO hJ U P p (idx i)).val := by
    have hh := congrArg (rename finSumFinEquiv) (zeroScalarEndpointFamily_back hd hO hJ U P p i)
    have hcancel (z : Poly K (h+m)) : rename finSumFinEquiv (rename finSumFinEquiv.symm z)=z :=
      (renameEquiv K finSumFinEquiv).right_inv z
    rw [hcancel] at hh
    exact hh.symm
  rw [←hrename]
  apply weighted_homogeneous_rename finSumFinEquiv.toEmbedding
  simpa only [coreParity_eq_blockParity,Function.comp_def,Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply,endpointSplitParity,idx] using hg

end Froberg.PreparedTarget
