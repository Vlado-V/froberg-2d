import Froberg.AllTargetElimination
import Froberg.PureBiformRows

/-! Upper target rows from a fixed pure-X generating tuple.  Arbitrary
lower-X-degree perturbations of that tuple are permitted. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] {h m d b : ℕ}
variable {ι : Type*} [Fintype ι]
attribute [local instance] tensorGroup

theorem targetLift_of_pure_full (hdb : d≤b) (hb : b≤2*d)
    (U : Submodule K (Poly K h)) (hU : U≤Forms K h d)
    (u : ι → U) (hu : Submodule.span K (Set.range u)=⊤)
    (hfull : U*Forms K h (b-d)=Forms K h b)
    (p : ι → Poly K (h+m)) (hp : ∀ i,(p i).IsHomogeneous d)
    (htop : ∀ i,coreComponent h m d (p i)=
      ambientBiform (homogeneousInclusion U hU (u i) ⊗ₜ[K] constantOneForm K m))
    (hupper : ∀ i k,d<k → coreComponent h m k (p i)=0)
    (I : Submodule K (Poly K (h+m)))
    (hI : (Submodule.span K (Set.range p))*Forms K (h+m) d≤I) :
    TargetLift I d b := by
  have hw : d+(b-d)=b := by omega
  have hcoef : (b-d)+(2*d-b)=d := by omega
  have hg : Function.Surjective (biformTensorFamilyMap (x := b-d) (y := 2*d-b)
      (fun i => homogeneousInclusion U hU (u i) ⊗ₜ[K] constantOneForm K m)) := by
    rw [biformTensorFamilyMap_pure]
    apply pure_biform_family_surjective U hU u hu
    simpa only [hw] using hfull
  have hh := biform_deformed_target_lift (j := d) (e := 0) (x := b-d) (y := 2*d-b) p hp
    (fun i => homogeneousInclusion U hU (u i) ⊗ₜ[K] constantOneForm K m)
    htop hupper hg I (by simpa only [hcoef] using hI)
  have ht : (d+0)+((b-d)+(2*d-b))=2*d := by omega
  rw [ht,hw] at hh
  exact hh

theorem targetLift_of_pure_cutoff (hdb : d+1≤b) (hb : b≤2*d)
    (U : Submodule K (Poly K h)) (hU : U≤Forms K h d)
    (u : ι → U) (hu : Submodule.span K (Set.range u)=⊤)
    (hcutoff : U*Forms K h 1=Forms K h (d+1))
    (p : ι → Poly K (h+m)) (hp : ∀ i,(p i).IsHomogeneous d)
    (htop : ∀ i,coreComponent h m d (p i)=
      ambientBiform (homogeneousInclusion U hU (u i) ⊗ₜ[K] constantOneForm K m))
    (hupper : ∀ i k,d<k → coreComponent h m k (p i)=0)
    (I : Submodule K (Poly K (h+m)))
    (hI : (Submodule.span K (Set.range p))*Forms K (h+m) d≤I) :
    TargetLift I d b :=
  targetLift_of_pure_full (by omega) hb U hU u hu
    (pure_cutoff_propagates U hcutoff hdb) p hp htop hupper I hI

end Froberg
