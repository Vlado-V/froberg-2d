module

public import Froberg.PreparedBiformCoordinates
public import Froberg.AllTargetElimination
public import Froberg.BiformFullRow

@[expose] public section

/-! Actual prepared layer generators satisfy the top-component and support
conditions used by the target-row lifts. Their scalar shifts are unrestricted. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
attribute [local instance] tensorGroup

theorem scalar_rename_core_weight_zero (f : Forms K m d) :
    (rename (Fin.natAdd h) f.val).IsWeightedHomogeneous (coreWeight h m) 0 := by
  have hh := ambientBiform_weighted (constantOneForm K h ⊗ₜ[K] f)
  simpa only [ambientBiform_tmul,constantOneForm,map_one,one_mul] using hh

def renamedPreparedGenerator (p : PreparedParameters.Space m d q J counts O)
    (i : PreparedParameters.Label q J counts) : Poly K (h+m) :=
  rename finSumFinEquiv (PreparedParameters.generator p i)

theorem renamedPreparedGenerator_layer (p : PreparedParameters.Space m d q J counts O)
    (a : J) (hO : O a.val≤Forms K h a.val) (i : Fin (counts a.val)) :
    renamedPreparedGenerator p (Sum.inr ⟨a,i⟩)=
      rename (Fin.natAdd h) (p.1 (Sum.inr ⟨a,i⟩)).val+
        ambientBiform (preparedLayerTensor a hO p i) := by
  unfold renamedPreparedGenerator PreparedParameters.generator PreparedParameters.scalar PreparedParameters.high
  rw [map_add,rename_rename,←rename_sumBiform,preparedLayerTensor_sum]
  rfl

theorem prepared_layer_components (p : PreparedParameters.Space m d q J counts O)
    (a : J) (ha : 0<a.val) (hO : O a.val≤Forms K h a.val) (i : Fin (counts a.val)) :
    coreComponent h m a.val (renamedPreparedGenerator p (Sum.inr ⟨a,i⟩))=
      ambientBiform (preparedLayerTensor a hO p i) ∧
    ∀ k,a.val<k → coreComponent h m k (renamedPreparedGenerator p (Sum.inr ⟨a,i⟩))=0 := by
  rw [renamedPreparedGenerator_layer p a hO i]
  exact scalar_shift_top_components (coreWeight h m) _ _ ha
    (scalar_rename_core_weight_zero _) (ambientBiform_weighted _)

theorem span_products_subfamily {α β : Type*} (p : β → Poly K (h+m)) (f : α → β) :
    (Submodule.span K (Set.range (p ∘ f)))*Forms K (h+m) d ≤
      (Submodule.span K (Set.range p))*Forms K (h+m) d :=
  mul_le_mul' (Submodule.span_mono (Set.range_comp_subset_range _ _)) le_rfl

theorem prepared_layer_target_lift (p : PreparedParameters.Space m d q J counts O)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (a : J) (ha : 0<a.val) (hab : a.val≤b) (hbd : b≤d+a.val)
    (hg : Function.Surjective (biformTensorFamilyMap
      (x := b-a.val) (y := d+a.val-b) (preparedLayerTensor a (hO _ a.property) p))) :
    TargetLift ((Submodule.span K (Set.range (renamedPreparedGenerator p)))*Forms K (h+m) d) d b := by
  refine targetLift_of_biform (hJ _ a.property) hab hbd
    (fun i => renamedPreparedGenerator p (Sum.inr ⟨a,i⟩)) ?_
    (preparedLayerTensor a (hO _ a.property) p) ?_ ?_ hg
    ((Submodule.span K (Set.range (renamedPreparedGenerator p)))*Forms K (h+m) d) ?_
  · intro i
    exact (PreparedParameters.generator_homogeneous hO hJ p (Sum.inr ⟨a,i⟩)).rename_isHomogeneous
  · intro i
    exact (prepared_layer_components p a ha (hO _ a.property) i).1
  · intro i
    exact (prepared_layer_components p a ha (hO _ a.property) i).2
  · exact span_products_subfamily (renamedPreparedGenerator p) (fun i => Sum.inr ⟨a,i⟩)

end Froberg
