module

public import Froberg.MixedExterior

@[expose] public section

/-! Complement coordinate rows diagonalize the mixed determinant constraints. -/
noncomputable section
namespace Froberg.MixedExterior
open Module
variable {R : Type*} [CommRing R] {r l : ℕ}

/-- The complementary coordinate set. -/
def complement (I : Set.powersetCard (Fin (r+l)) r) : Set.powersetCard (Fin (r+l)) l :=
  Set.powersetCard.compl (by simp [Nat.add_comm]) I

@[simp] theorem complement_val (I : Set.powersetCard (Fin (r+l)) r) :
    (complement I).val = I.valᶜ := rfl

def complementVectors (I : Set.powersetCard (Fin (r+l)) r) : Fin l → Fin (r+l) → R :=
  (Pi.basisFun R (Fin (r+l))) ∘ Set.powersetCard.ofFinEmbEquiv.symm (complement I)

/-- A complementary coordinate row annihilates every other exterior basis vector. -/
theorem mixedRow_complement_offdiag (I J : Set.powersetCard (Fin (r+l)) r) (h : I ≠ J) :
    mixedRow (complementVectors (R := R) I) J = 0 := by
  classical
  have hn : ¬Disjoint J.val (complement I).val := by
    intro hd
    have hs : J.val ⊆ I.val := by
      intro a ha
      by_contra hna
      exact Finset.disjoint_left.mp hd ha (Finset.mem_compl.mpr hna)
    have he : J.val = I.val := Finset.eq_of_subset_of_card_le hs (by rw [I.property,J.property])
    exact h (Subtype.ext he.symm)
  unfold mixedRow mixedFunctional
  rw [LinearMap.comp_apply, LinearMap.flip_apply]
  have hw : exteriorPower.ιMulti R l (complementVectors I) =
      (Pi.basisFun R (Fin (r+l))).exteriorPower l (complement I) := by
    rw [exteriorPower.basis_apply]
    rfl
  rw [hw, exteriorPower.wedge_apply_of_not_disjoint _ hn, map_zero]

/-- The remaining diagonal entry is a unit: its rows are a permutation of the
standard basis, with the chosen coordinates first and their complement last. -/
theorem isUnit_mixedRow_complement (I : Set.powersetCard (Fin (r+l)) r) :
    IsUnit (mixedRow (complementVectors (R := R) I) I) := by
  classical
  let f : Fin r → Fin (r+l) := Set.powersetCard.ofFinEmbEquiv.symm I
  let g : Fin l → Fin (r+l) := Set.powersetCard.ofFinEmbEquiv.symm (complement I)
  have hf : Function.Injective f := (Set.powersetCard.ofFinEmbEquiv.symm I).injective
  have hg : Function.Injective g := (Set.powersetCard.ofFinEmbEquiv.symm (complement I)).injective
  have hfg : ∀ i j, f i ≠ g j := by
    intro i j hij
    have hi : f i ∈ I.val := by
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I (f i)).mp ⟨i,rfl⟩
    have hj : g j ∈ (complement I).val := by
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (complement I) (g j)).mp ⟨j,rfl⟩
    rw [complement_val] at hj
    exact (Finset.mem_compl.mp hj) (hij ▸ hi)
  let e : Fin (r+l) ≃ Fin (r+l) := Equiv.ofBijective (Fin.append f g)
    (Finite.injective_iff_bijective.mp (Fin.append_injective_iff.mpr ⟨hf,hg,hfg⟩))
  let b := (Pi.basisFun R (Fin (r+l))).reindex e.symm
  have hb : Fin.append (basisVectors (R := R) I) (complementVectors I) = b := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [basisVectors,complementVectors,b,e,f,g]
  rw [mixedRow_apply]
  have hu : IsUnit ((Pi.basisFun R (Fin (r+l))).det
      (Fin.append (basisVectors (R := R) I) (complementVectors I))) := by
    rw [hb]
    exact (Pi.basisFun R (Fin (r+l))).isUnit_det b
  exact (congrArg IsUnit (Pi.basisFun_det_apply _)).mp hu

end Froberg.MixedExterior
