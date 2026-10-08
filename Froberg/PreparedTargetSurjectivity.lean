import Froberg.PreparedPrivateComponents
import Froberg.RowTwoTargetLift
import Froberg.PureTargetLift
import Froberg.TargetLiftCoverage

/-! All high target rows for one literal prepared family. The inputs are
actual homogeneous tensor row maps and the pure-X product condition; scalar
shifts and the lower private terms are carried through the proof. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
attribute [local instance] tensorGroup
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def outerTensorFamily (p : Space m d q f u J counts O) :
    Fin f → Forms K h 1 ⊗[K] Forms K m (d-1) :=
  fun i => sumBiformEquiv.symm (p.2.1 i)

def quadraticTensorFamily (h2 : 2∈J) (hO2 : O 2≤Forms K h 2)
    (p : Space m d q f u J counts O) :
    Fin (counts 2) → Forms K h 2 ⊗[K] Forms K m (d-2) :=
  preparedLayerTensor ⟨2,h2⟩ hO2 p.1

theorem all_prepared_target_lifts (hd : 3≤d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,0<j ∧ j≤d) (h2 : 2∈J)
    (S : Submodule K (Poly K h)) (hS : S≤Forms K h d)
    (u₀ : Fin u → S) (hu₀ : Submodule.span K (Set.range u₀)=⊤)
    (hcut : S*Forms K h 1=Forms K h (d+1))
    (heven : ¬Odd d → S=Forms K h d)
    (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (hPdeg : ∀ i,(P i).IsHomogeneous d)
    (hPlow : ∀ i k,d≤k → coreComponent h m k (rename finSumFinEquiv (P i))=0)
    (p : Space m d q f u J counts O)
    (hrow2 : Function.Surjective
      ((biformTensorFamilyMap (x := 1) (y := d-1) (outerTensorFamily p)).coprod
        (biformTensorFamilyToDegree (x := 0) (by omega : d-2+d=(d-1)+(d-1))
          (quadraticTensorFamily h2 (hO 2 h2) p))))
    (hrow3 : Function.Surjective (biformTensorFamilyMap (x := 1) (y := d-1)
      (quadraticTensorFamily h2 (hO 2 h2) p)))
    (hrow4 : Function.Surjective (biformTensorFamilyMap (x := 2) (y := d-2)
      (quadraticTensorFamily h2 (hO 2 h2) p)))
    (hmid : ∀ b,5≤b → b≤d → (b<d ∨ Odd d) →
      ∃ a : J,a.val≤b ∧ b≤d+a.val ∧ Function.Surjective (biformTensorFamilyMap
        (x := b-a.val) (y := d+a.val-b) (preparedLayerTensor a (hO _ a.property) p.1))) :
    ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator
        (fun i => homogeneousInclusion S hS (u₀ i)) P p)))*Forms K (h+m) d) d b := by
  let U : Fin u → Forms K h d := fun i => homogeneousInclusion S hS (u₀ i)
  let Q := renamedGenerator U P p
  let I : Submodule K (Poly K (h+m)) := (Submodule.span K (Set.range Q))*Forms K (h+m) d
  let pF : Fin f → Poly K (h+m) := fun i => Q (Sum.inr (Sum.inl i))
  let pE : Fin (counts 2) → Poly K (h+m) := fun i => Q (Sum.inl (Sum.inr ⟨⟨2,h2⟩,i⟩))
  let pU : Fin u → Poly K (h+m) := fun i => Q (Sum.inr (Sum.inr i))
  have hpQ (i) : (Q i).IsHomogeneous d :=
    (generator_homogeneous (by omega) hO (fun j hj => (hJ j hj).2) U P hPdeg p i).rename_isHomogeneous
  have htF (i) : coreComponent h m 1 (pF i)=ambientBiform (outerTensorFamily p i) := by
    dsimp [pF,Q]
    rw [renamedGenerator_outer]
    exact (ambientBiform_weighted _).weightedHomogeneousComponent_same
  have huF (i k) (hk : 1<k) : coreComponent h m k (pF i)=0 := by
    dsimp [pF,Q]
    rw [renamedGenerator_outer]
    exact (ambientBiform_weighted _).weightedHomogeneousComponent_ne k (by omega)
  have hEc (i) := prepared_layer_components p.1 ⟨2,h2⟩ (by norm_num) (hO 2 h2) i
  have htE (i) : coreComponent h m 2 (pE i)=ambientBiform (quadraticTensorFamily h2 (hO 2 h2) p i) := by
    simpa only [pE,Q,renamedGenerator_prepared,quadraticTensorFamily] using (hEc i).1
  have huE (i k) (hk : 2<k) : coreComponent h m k (pE i)=0 := by
    simpa only [pE,Q,renamedGenerator_prepared] using (hEc i).2 k hk
  have hIF : (Submodule.span K (Set.range pF))*Forms K (h+m) d≤I :=
    span_products_subfamily Q (fun i => Sum.inr (Sum.inl i))
  have hIE : (Submodule.span K (Set.range pE))*Forms K (h+m) d≤I :=
    span_products_subfamily Q (fun i => Sum.inl (Sum.inr ⟨⟨2,h2⟩,i⟩))
  have hIU : (Submodule.span K (Set.range pU))*Forms K (h+m) d≤I :=
    span_products_subfamily Q (fun i => Sum.inr (Sum.inr i))
  have htU (i) : coreComponent h m d (pU i)=
      ambientBiform (homogeneousInclusion S hS (u₀ i) ⊗ₜ[K] constantOneForm K m) :=
    (private_components (by omega) U P hPlow p i).1
  have huU (i k) (hk : d<k) : coreComponent h m k (pU i)=0 :=
    (private_components (by omega) U P hPlow p i).2 k hk
  apply target_lifts_cover hd I
  · exact row_two_deformed_target_lift (by omega) pF pE
      (fun i => hpQ _) (fun i => hpQ _) (outerTensorFamily p)
      (quadraticTensorFamily h2 (hO 2 h2) p) htF htE huF huE hrow2 I hIF hIE
  · exact targetLift_of_biform_degrees (j := 2) (e := d-2) (x := 1) (y := d-1) (by omega) (by omega) (by norm_num)
      pE (fun i => hpQ _) _ htE huE hrow3 I hIE
  · exact targetLift_of_biform_degrees (j := 2) (e := d-2) (x := 2) (y := d-2) (by omega) (by omega) (by norm_num)
      pE (fun i => hpQ _) _ htE huE hrow4 I hIE
  · intro b hb hbd hodd
    obtain ⟨a,hab,hba,ha⟩ := hmid b hb hbd hodd
    apply targetLift_mono _ (prepared_layer_target_lift p.1 hO
      (fun j hj => (hJ j hj).2) a (hJ _ a.property).1 hab hba ha)
    simpa only [Q,Function.comp_def,renamedGenerator_prepared] using
      span_products_subfamily (d := d) Q Sum.inl
  · intro hnodd
    apply targetLift_of_pure_full le_rfl (by omega) S hS u₀ hu₀ _ pU
      (fun i => hpQ _) htU huU I hIU
    rw [heven hnodd,Nat.sub_self,forms_mul_forms,Nat.add_zero]
  · intro b hdb hb
    exact targetLift_of_pure_cutoff hdb hb S hS u₀ hu₀ hcut pU
      (fun i => hpQ _) htU huU I hIU

end Froberg.PreparedTarget
