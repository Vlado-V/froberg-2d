module

public import Froberg.BiformTargetLift
public import Froberg.PolynomialIdealElimination

@[expose] public section

/-! Uniform target-row interfaces for the prepared-family assembly.  Every
lift is an actual homogeneous polynomial in the specified ideal component. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] {h m d b j : ℕ}
variable {ι : Type*} [Fintype ι]
attribute [local instance] tensorGroup

def TargetLift (I : Submodule K (Poly K (h+m))) (d b : ℕ) : Prop :=
  ∀ v : coreCoefficientSpace K h m (2*d) b,
    ∃ q : Forms K (h+m) (2*d), q.val∈I ∧
      coreComponent h m b q.val=v.val ∧
      ∀ k,b<k → coreComponent h m k q.val=0

theorem targetLift_mono {I J : Submodule K (Poly K (h+m))}
    (hIJ : I≤J) (hI : TargetLift I d b) : TargetLift J d b := by
  intro v
  obtain ⟨q,hq,ht,hu⟩ := hI v
  exact ⟨q,hIJ hq,ht,hu⟩

theorem targetLift_of_biform_degrees {e x y : ℕ}
    (hgen : j+e=d) (hcoef : x+y=d) (hweight : j+x=b)
    (p : ι → Poly K (h+m)) (hp : ∀ i,(p i).IsHomogeneous d)
    (g : ι → Forms K h j ⊗[K] Forms K m e)
    (htop : ∀ i,coreComponent h m j (p i)=ambientBiform (g i))
    (hupper : ∀ i k,j<k → coreComponent h m k (p i)=0)
    (hg : Function.Surjective (biformTensorFamilyMap (x := x) (y := y) g))
    (I : Submodule K (Poly K (h+m)))
    (hI : (Submodule.span K (Set.range p))*Forms K (h+m) d≤I) :
    TargetLift I d b := by
  have hh := biform_deformed_target_lift p (by simpa only [hgen] using hp)
    g htop hupper hg I (by simpa only [hcoef] using hI)
  have htotal : (j+e)+(x+y)=2*d := by omega
  rw [htotal,hweight] at hh
  exact hh

/-- The literal multiplication row in degrees `(j,d-j)` and
`(b-j,d+j-b)` supplies the degree-`2d`, X-degree-`b` target. -/
theorem targetLift_of_biform (hjd : j≤d) (hjb : j≤b) (hbd : b≤d+j)
    (p : ι → Poly K (h+m)) (hp : ∀ i,(p i).IsHomogeneous d)
    (g : ι → Forms K h j ⊗[K] Forms K m (d-j))
    (htop : ∀ i,coreComponent h m j (p i)=ambientBiform (g i))
    (hupper : ∀ i k,j<k → coreComponent h m k (p i)=0)
    (hg : Function.Surjective (biformTensorFamilyMap (x := b-j) (y := d+j-b) g))
    (I : Submodule K (Poly K (h+m)))
    (hI : (Submodule.span K (Set.range p))*Forms K (h+m) d≤I) :
    TargetLift I d b := by
  have hsource : j+(d-j)=d := by omega
  have hcoef : b-j+(d+j-b)=d := by omega
  have htotal : (j+(d-j))+(b-j+(d+j-b))=2*d := by omega
  have hweight : j+(b-j)=b := by omega
  have hh := biform_deformed_target_lift (x := b-j) (y := d+j-b) p
    (by simpa only [hsource] using hp) g htop hupper hg I
    (by simpa only [hcoef] using hI)
  rw [htotal,hweight] at hh
  exact hh

/-- Filling all rows of X-degree at least two leaves a representative
supported in the two bottom X-degrees. -/
theorem all_target_lifts_eliminate (I : Submodule K (Poly K (h+m)))
    (hd : 0<d) (hlift : ∀ b,2≤b → b≤2*d → TargetLift I d b)
    (p : Forms K (h+m) (2*d)) :
    ∃ q : Forms K (h+m) (2*d),p.val-q.val∈I ∧
      ∀ b,2≤b → b≤2*d → coreComponent h m b q.val=0 := by
  have hs : (2*d-1)+1=2*d := by omega
  let weight : Fin ((2*d-1)+1) → ℕ := fun i => i.val+1
  obtain ⟨q,hq,hzero⟩ := polynomial_ideal_elimination (D := 2*d) (n := 2*d-1) I weight (fun (i : Fin ((2*d-1)+1)) (hi : i≠0) v => by
    have hi0 : (0 : ℕ) < (i : ℕ) := by
      by_contra hn
      apply hi
      exact Fin.ext (by simp only [Fin.val_zero];omega)
    obtain ⟨q,hq,ht,hu⟩ := hlift (weight i) (by dsimp [weight];omega)
      (by dsimp [weight];have := i.isLt;omega) v
    exact ⟨q,hq,ht,fun k hik => hu (weight k) (by change i.val<k.val at hik;dsimp [weight];omega)⟩) p
  refine ⟨q,hq,?_⟩
  intro b hb hbd
  let i : Fin (2*d-1) := ⟨b-2,by omega⟩
  have hi : weight i.succ=b := by dsimp [weight,i];omega
  simpa only [hi] using hzero i

end Froberg
