module

public import Froberg.PreparedLayerTargets
public import Froberg.PreparedTargetFamily

@[expose] public section

/-! Literal components of the complete prepared polynomial tuple. The pure
private rows retain their top part under all permitted lower perturbations. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
attribute [local instance] tensorGroup

def renamedGenerator (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (p : Space m d q f u J counts O) (i : Label q f u J counts) : Poly K (h+m) :=
  rename finSumFinEquiv (generator U P p i)

@[simp] theorem renamedGenerator_prepared (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (p : Space m d q f u J counts O) (i : PreparedParameters.Label q J counts) :
    renamedGenerator U P p (Sum.inl i)=renamedPreparedGenerator p.1 i := by
  rw [renamedGenerator,generator_prepared]
  rfl

@[simp] theorem renamedGenerator_outer (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (p : Space m d q f u J counts O) (i : Fin f) :
    renamedGenerator U P p (Sum.inr (Sum.inl i))=
      ambientBiform (sumBiformEquiv.symm (p.2.1 i)) := by
  rw [renamedGenerator,generator_outer,←rename_sumBiform]
  congr 1
  change (p.2.1 i).val=(sumBiformEquiv (sumBiformEquiv.symm (p.2.1 i))).val
  rw [LinearEquiv.apply_symm_apply]

theorem renamedGenerator_private (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (p : Space m d q f u J counts O) (i : Fin u) :
    renamedGenerator U P p (Sum.inr (Sum.inr i))=
      rename (Fin.natAdd h) (p.2.2 i).val+
        (ambientBiform (U i ⊗ₜ[K] constantOneForm K m)+rename finSumFinEquiv (P i)) := by
  rw [renamedGenerator,generator_private,map_add,map_add,rename_rename,rename_rename,
    ambientBiform_tmul]
  simp only [constantOneForm,map_one,mul_one]
  rfl

theorem lower_biform_components {e s : ℕ} (hed : e<d)
    (P : MvPolynomial (Fin h ⊕ Fin m) K)
    (hP : P∈biformImage (Forms K h e) (Forms K m s))
    (k : ℕ) (hk : d≤k) : coreComponent h m k (rename finSumFinEquiv P)=0 := by
  let g := sumBiformEquiv.symm (⟨P,hP⟩ : biformImage (Forms K h e) (Forms K m s))
  have hg : sumBiform g=P := by
    change (sumBiformEquiv (sumBiformEquiv.symm (⟨P,hP⟩ : biformImage (Forms K h e) (Forms K m s)))).val=P
    rw [LinearEquiv.apply_symm_apply]
  rw [←hg,rename_sumBiform]
  exact (ambientBiform_weighted g).weightedHomogeneousComponent_ne k (by omega)

theorem private_components (hd : 0<d) (U : Fin u → Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (hP : ∀ i k,d≤k → coreComponent h m k (rename finSumFinEquiv (P i))=0)
    (p : Space m d q f u J counts O) (i : Fin u) :
    coreComponent h m d (renamedGenerator U P p (Sum.inr (Sum.inr i)))=
      ambientBiform (U i ⊗ₜ[K] constantOneForm K m) ∧
    ∀ k,d<k → coreComponent h m k (renamedGenerator U P p (Sum.inr (Sum.inr i)))=0 := by
  rw [renamedGenerator_private]
  dsimp only [coreComponent] at hP
  have hs := scalar_rename_core_weight_zero (h := h) (p.2.2 i)
  have hu := ambientBiform_weighted (U i ⊗ₜ[K] constantOneForm K m)
  constructor
  · change weightedHomogeneousComponent (coreWeight h m) d _=_
    rw [map_add,map_add,hs.weightedHomogeneousComponent_ne _ (by omega),
      hu.weightedHomogeneousComponent_same,hP i d le_rfl,add_zero,zero_add]
  · intro k hk
    change weightedHomogeneousComponent (coreWeight h m) k _=0
    rw [map_add,map_add,hs.weightedHomogeneousComponent_ne _ (by omega),
      hu.weightedHomogeneousComponent_ne _ (by omega),hP i k hk.le,add_zero,add_zero]

end Froberg.PreparedTarget
