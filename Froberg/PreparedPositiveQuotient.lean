import Froberg.PreparedPositiveIndependence
import Froberg.ScalarQuotientTransport
import Froberg.RestoredBiformFamily

/-! The actual positive generators, with their pure perturbations, are
independent modulo the entire scalar form space used in flag replacement. -/
noncomputable section
set_option maxHeartbeats 300000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem positive_private_forms_scalar_independent (hd : 1<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hmin : ∀ j∈J,2≤j)
    (hJ : ∀ j∈J,0<counts j → j<d)
    (p : Space m d q J counts O) (hp : ∀ j,LinearIndependent K (p.2 j))
    (U : ProductRows.LayerLabel J counts → MvPolynomial (Fin h ⊕ Fin m) K)
    (hU : ∀ i,(U i).IsWeightedHomogeneous (blockWeight h m) d)
    (P W : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (hP : ∀ i,(P i).IsWeightedHomogeneous (blockWeight h m) 1)
    (hW : ∀ i,(W i).IsWeightedHomogeneous (blockWeight h m) d)
    (hPi : LinearIndependent K P)
    (g : ProductRows.LayerLabel J counts ⊕ Fin u → Forms K (h+m) d)
    (hg : ∀ i,rename finSumFinEquiv.symm (g i).val=
      Sum.elim (positivePerturbedFamily p U) (fun k => P k+W k) i) :
    LinearIndependent K (fun i =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ (g i)) := by
  apply scalar_quotient_independence_transport
  simpa only [hg] using positive_private_scalar_independent hd hO hmin hJ p hp U hU P W hP hW hPi

theorem prepared_positive_endpoint_scalar_independent (hd : 1<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hmin : ∀ j∈J,2≤j)
    (hJ : ∀ j∈J,j≤d) (hJlt : ∀ j∈J,0<counts j → j<d)
    (U : Fin u → Forms K h d) (P : PreparedTarget.OuterSpace K (Fin h) m d u)
    (p : Space m d q J counts O × PreparedTarget.OuterSpace K (Fin h) m d f)
    (hp : ∀ j,LinearIndependent K (p.1.2 j)) (hP : LinearIndependent K P) :
    LinearIndependent K (fun i : ProductRows.LayerLabel J counts ⊕ Fin u =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (PreparedTarget.zeroScalarEndpointFamily (by omega) hO hJ U P p
          ((Fintype.equivFin (PreparedTarget.Label q f u J counts))
            (Sum.elim (fun j => Sum.inl (Sum.inr j)) (fun j => Sum.inr (Sum.inr j)) i)))) := by
  have hPi : LinearIndependent K (fun i => (P i).val) :=
    hP.map' (biformImage (Forms K h 1) (Forms K m (d-1))).subtype
      (Submodule.ker_subtype _)
  apply positive_private_forms_scalar_independent hd hO hmin hJlt p.1 hp
    (fun _ => 0) (fun _ => (weightedHomogeneousSubmodule K _ _).zero_mem)
    (fun i => (P i).val) (fun i => rename Sum.inl (U i).val)
    (fun i => biformImage_output_weight _ _ le_rfl (P i).property)
    (fun i => rename_weightedHomogeneous
      (⟨Sum.inl,Sum.inl_injective⟩ : Fin h ↪ Fin h ⊕ Fin m)
      (fun _ => 1) (blockWeight h m) (fun _ => rfl) (U i).property) hPi
  intro i
  cases i with
  | inl i =>
    rw [PreparedTarget.zeroScalarEndpointFamily_back]
    simp only [Sum.elim_inl,positivePerturbedFamily,add_zero]
  | inr i =>
    rw [PreparedTarget.zeroScalarEndpointFamily_back]
    rfl

theorem restored_positive_endpoint_scalar_independent (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (hJlt : ∀ j∈J,0<counts j → j<d)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) (hp : ∀ j,LinearIndependent K (p.1.2 j)) :
    LinearIndependent K (fun i : ProductRows.LayerLabel J counts =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (restoredEndpointFamily hd hO hJ heven idx slot p (idx.symm (Sum.inr i)))) := by
  apply scalar_quotient_independence_transport
  let U : ProductRows.LayerLabel J counts → MvPolynomial (Fin h ⊕ Fin m) K :=
    fun i => (PolynomialRestoration.pureShift (pureEvenEmbed hd) slot p.2
      (idx.symm (Sum.inr i))).val
  have hU : ∀ i,(U i).IsWeightedHomogeneous (blockWeight h m) d :=
    fun i => pureShift_weight hd slot p.2 (idx.symm (Sum.inr i))
  have hg (i : ProductRows.LayerLabel J counts) :
      rename finSumFinEquiv.symm
        (restoredEndpointFamily hd hO hJ heven idx slot p (idx.symm (Sum.inr i))).val=
      positivePerturbedFamily p.1 U i := by
    change rename finSumFinEquiv.symm (rename finSumFinEquiv
      (generator p.1 (idx (idx.symm (Sum.inr i)))+U i))=_
    have hcancel (z : MvPolynomial (Fin h ⊕ Fin m) K) :
        rename finSumFinEquiv.symm (rename finSumFinEquiv z)=z :=
      (renameEquiv K finSumFinEquiv).left_inv z
    rw [hcancel,Equiv.apply_symm_apply]
    rfl
  simpa only [hg] using positivePerturbedFamily_scalar_independent hO hpos hJlt p.1 hp U hU

end Froberg.PreparedParameters
