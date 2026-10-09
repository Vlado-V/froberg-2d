module

public import Froberg.HomogeneousVariableEquiv
public import Froberg.PrivateFrameDetector
public import Froberg.PrivateBiformFamily

@[expose] public section

/-! The private quadratic detector and its exact kernel use the same finite
coordinates after reindexing the output variables. -/
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} {a z s b h H c : ℕ}

def renamedPrivateBasis (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) :
    Basis (Fin h) K (homogeneousSubmodule σ K 1) :=
  Basis.ofEquivFun ((homogeneousVariableEquiv (K := K) f 1).trans e.symm)

def renamedPrivateColumn (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (w : Fin h → K) :
    homogeneousSubmodule σ K 1 :=
  (homogeneousVariableEquiv (K := K) f 1).symm (e w)

@[simp] theorem renamedPrivateBasis_column (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (w : Fin h → K) :
    (renamedPrivateBasis f e).equivFun (renamedPrivateColumn f e w)=w := by
  rw [renamedPrivateBasis,Basis.equivFun_ofEquivFun]
  change e.symm ((homogeneousVariableEquiv (K := K) f 1)
    ((homogeneousVariableEquiv (K := K) f 1).symm (e w)))=w
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]

theorem renamedPrivateColumn_ne_zero (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) {w : Fin h → K} (hw : w≠0) :
    renamedPrivateColumn f e w≠0 := by
  intro hz
  apply hw
  calc
    w=(renamedPrivateBasis f e).equivFun (renamedPrivateColumn f e w) :=
      (renamedPrivateBasis_column f e w).symm
    _=(renamedPrivateBasis f e).equivFun 0 := congrArg (renamedPrivateBasis f e).equivFun hz
    _=0 := (renamedPrivateBasis f e).equivFun.map_zero

@[simp] theorem rename_renamedPrivateColumn (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (w : Fin h → K) :
    rename f (renamedPrivateColumn f e w).val=(e w).val := by
  change ((homogeneousVariableEquiv (K := K) f 1)
    ((homogeneousVariableEquiv (K := K) f 1).symm (e w))).val=(e w).val
  rw [LinearEquiv.apply_symm_apply]

@[simp] theorem rename_renamedPrivateBasis (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (j : Fin h) :
    rename f ((renamedPrivateBasis f e) j).val=(e (Pi.single j 1)).val := by
  classical
  have hb : (renamedPrivateBasis f e) j=renamedPrivateColumn f e (Pi.single j 1) := by
    change (Basis.ofEquivFun ((homogeneousVariableEquiv (K := K) f 1).trans e.symm)) j=_
    rw [Basis.coe_ofEquivFun]
    rfl
  rw [hb,rename_renamedPrivateColumn]

theorem renamed_private_detector_column (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) (w : Fin h → K) (j : Fin h) :
    ((quadraticPolynomialDetector L).comp (rename f).toLinearMap)
      ((renamedPrivateColumn f e w).val*((renamedPrivateBasis f e) j).val)=
    ((L.comp (mulForm (e w))).comp e.toLinearMap) (Pi.single j 1) := by
  simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,map_mul,
    rename_renamedPrivateColumn,rename_renamedPrivateBasis]
  exact quadraticPolynomialDetector_form L (mulForm (e w) (e (Pi.single j 1)))

theorem privatePowerBiform_output_rename [Fintype σ] {d : ℕ}
    (f : σ ≃ Fin h) (l : Fin b → homogeneousSubmodule σ K 1)
    (ι : Fin b ↪ Fin z) (i : Fin b) :
    (privatePowerBiform (a := a) (d := d)
      (fun i => homogeneousVariableEquiv f 1 (l i)) ι i).val=
    rename (Sum.map f id) (privatePowerBiform (a := a) (d := d) l ι i).val := by
  simp only [privatePowerBiform_val,coe_homogeneousVariableEquiv,map_mul,rename_rename]
  rfl

/-- A detector supplied by the finite-variable frame open feeds the prepared
private-row theorem on any equivalent variable type. -/
theorem private_detector_coordinate_pullback (f : σ ≃ Fin h)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
    (w : Fin b → Fin h → K) (hw : ∀ i,w i≠0)
    (frame : Fin H → Forms K h 2)
    (O : Submodule K (MvPolynomial σ K))
    (hO : O.map (rename f).toLinearMap≤outputFrameSpace frame)
    (L₀ : Forms K h 2 →ₗ[K] (Fin c → K))
    (hL₀ : L₀.ker=Submodule.span K (Set.range frame))
    (ι : Fin b ↪ Fin z)
    (hprivate : (privatePolynomialMap (a := a) (s := s) ι
      (fun i => (L₀.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w)))) :
    ∃ (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
      (l : Fin b → homogeneousSubmodule σ K 1)
      (L : MvPolynomial σ K →ₗ[K] (Fin c → K))
      (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K)),
      (∀ i,l i≠0) ∧ O≤L.ker ∧
      (∀ i j,L ((l i).val*(bo j).val)=A i (Pi.single j 1)) ∧
      (privatePolynomialMap (a := a) (s := s) ι A).ker=
        Submodule.span K (Set.range (koszulVector
          (privateGenerator (a := a) (s := s) ι (fun i => bo.equivFun (l i))))) := by
  let bo := renamedPrivateBasis f e
  let l := fun i => renamedPrivateColumn f e (w i)
  let L := (quadraticPolynomialDetector L₀).comp (rename f).toLinearMap
  let A := fun i => (L₀.comp (mulForm (e (w i)))).comp e.toLinearMap
  refine ⟨bo,l,L,A,fun i => renamedPrivateColumn_ne_zero f e (hw i),?_,?_,?_⟩
  · intro p hp
    exact quadraticPolynomialDetector_frame frame L₀ hL₀ (hO ⟨p,hp,rfl⟩)
  · intro i j
    exact renamed_private_detector_column f e L₀ (w i) j
  · simpa only [bo,l,renamedPrivateBasis_column] using hprivate

end Froberg
