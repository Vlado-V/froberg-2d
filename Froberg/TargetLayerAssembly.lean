module

public import Froberg.PreparedTensorRealization
public import Froberg.MiddleRowsCommonOpen

@[expose] public section

/-! Splicing the quadratic frame and all higher-layer tensors into the
single literal prepared coefficient space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m d H r : ℕ}
attribute [local instance] tensorGroup

def targetLayerCount (d h m r j : ℕ) : ℕ :=
  if j=2 then r else higherGeneratorCount d h m j

def targetLayerOutput (frame : Fin H → Forms K h 2) (j : ℕ) : Submodule K (Poly K h) :=
  if j=2 then outputFrameSpace frame else Forms K h j

theorem activeEven_ne_two_is_higher (hd : 3≤d)
    (a : activeEvenIndices d) (ha : a.val≠2) : a.val∈activeHigherIndices d := by
  obtain ⟨ha2,had,haeven⟩ := activeEvenIndices_bounds hd a.property
  obtain ⟨k,hk⟩ := haeven
  exact Finset.mem_filter.mpr ⟨a.property,by omega⟩

def targetLayerFamily (hd : 3≤d) (frame : Fin H → Forms K h 2)
    (c : Fin r → Fin H → Forms K m (d-2))
    (G : BiformLayerFamily K h m (fun j : HigherLayerIndex d => j.val)
      (fun j => d-j.val) (fun j => higherGeneratorCount d h m j.val)) :
    (a : activeEvenIndices d) → Fin (targetLayerCount d h m r a.val) →
      Forms K h a.val ⊗[K] Forms K m (d-a.val) := by
  classical
  intro a
  by_cases ha : a.val=2
  · rcases a with ⟨a,haJ⟩
    dsimp only at ha
    subst a
    exact framedBiformFamily frame c
  · unfold targetLayerCount
    rw [if_neg ha]
    exact G ⟨a.val,activeEven_ne_two_is_higher hd a ha⟩

@[simp] theorem targetLayerFamily_quadratic (hd : 3≤d) (frame : Fin H → Forms K h 2)
    (c : Fin r → Fin H → Forms K m (d-2))
    (G : BiformLayerFamily K h m (fun j : HigherLayerIndex d => j.val)
      (fun j => d-j.val) (fun j => higherGeneratorCount d h m j.val)) (i : Fin r) :
    targetLayerFamily hd frame c G ⟨2,two_mem_activeEvenIndices hd⟩ i=framedBiformFamily frame c i := by
  simp [targetLayerFamily]

theorem targetLayerFamily_higher_surjective (hd : 3≤d) (frame : Fin H → Forms K h 2)
    (c : Fin r → Fin H → Forms K m (d-2))
    (G : BiformLayerFamily K h m (fun j : HigherLayerIndex d => j.val)
      (fun j => d-j.val) (fun j => higherGeneratorCount d h m j.val))
    (a : HigherLayerIndex d) (x y : ℕ)
    (hG : Function.Surjective (biformTensorFamilyMap (x := x) (y := y) (G a))) :
    Function.Surjective (biformTensorFamilyMap (x := x) (y := y)
      (targetLayerFamily hd frame c G ⟨a.val,(Finset.mem_filter.mp a.property).1⟩)) := by
  have ha : a.val≠2 := by have := (Finset.mem_filter.mp a.property).2;omega
  have hcast (n : ℕ) (hn : higherGeneratorCount d h m a.val=n) :
      Function.Surjective (biformTensorFamilyMap (x := x) (y := y)
        (cast (congrArg (fun t => Fin t → Forms K h a.val ⊗[K] Forms K m (d-a.val)) hn) (G a))) := by
    subst n
    exact hG
  have hN : higherGeneratorCount d h m a.val=targetLayerCount d h m r a.val := by
    simp only [targetLayerCount,if_neg ha]
  simpa only [targetLayerFamily,dif_neg ha,id_eq,eq_mpr_eq_cast] using hcast _ hN

theorem targetLayerOutput_homogeneous (frame : Fin H → Forms K h 2) (a : ℕ) :
    targetLayerOutput frame a≤Forms K h a := by
  unfold targetLayerOutput
  split_ifs with ha
  · subst a
    exact outputFrameSpace_homogeneous frame
  · exact le_rfl

theorem targetLayerFamily_mem (hd : 3≤d) (frame : Fin H → Forms K h 2)
    (c : Fin r → Fin H → Forms K m (d-2))
    (G : BiformLayerFamily K h m (fun j : HigherLayerIndex d => j.val)
      (fun j => d-j.val) (fun j => higherGeneratorCount d h m j.val))
    (a : activeEvenIndices d) (i : Fin (targetLayerCount d h m r a.val)) :
    sumBiform (targetLayerFamily hd frame c G a i)∈
      biformImage (targetLayerOutput frame a.val) (Forms K m (d-a.val)) := by
  classical
  by_cases ha : a.val=2
  · rcases a with ⟨a,haJ⟩
    dsimp only at ha
    subst a
    simpa [targetLayerOutput,targetLayerFamily] using
      framed_coefficients_mem_prepared frame c i
  · rw [targetLayerOutput,if_neg ha,←sumBiform_range]
    exact ⟨targetLayerFamily hd frame c G a i,rfl⟩

end Froberg
