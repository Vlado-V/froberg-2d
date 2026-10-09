module

public import Froberg.PreparedTargetSurjectivity

@[expose] public section

/-! Adding zero-count layers changes no generator. This identifies the
active-layer witness with the full even-layer parameter convention. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg MvPolynomial
variable {q : ℕ} {J J' : Finset ℕ} {c c' : ℕ → ℕ}

def zeroLayerMap (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j) :
    ProductRows.LayerLabel J c → ProductRows.LayerLabel J' c' :=
  fun a => ⟨⟨a.1.val,hJ a.1.property⟩,Fin.cast (hc _ a.1.property) a.2⟩

theorem zeroLayerMap_injective (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j) :
    Function.Injective (zeroLayerMap hJ hc) := by
  rintro ⟨j,i⟩ ⟨k,l⟩ he
  have hjk : j=k := Subtype.ext (congrArg (fun a => a.1.val) he)
  subst k
  have hil : i=l := Fin.ext (congrArg (fun a => a.2.val) he)
  subst l
  rfl

theorem zeroLayerMap_surjective (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) : Function.Surjective (zeroLayerMap hJ hc) := by
  rintro ⟨j,i⟩
  have hj : j.val∈J := by
    by_contra hn
    have hi := i.isLt
    have hzj := hz _ j.property hn
    omega
  refine ⟨⟨⟨j.val,hj⟩,Fin.cast (hc _ hj).symm i⟩,?_⟩
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · apply heq_of_eq
    apply Fin.ext
    rfl

def zeroLayerEquiv (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) : ProductRows.LayerLabel J c ≃ ProductRows.LayerLabel J' c' :=
  Equiv.ofBijective (zeroLayerMap hJ hc)
    ⟨zeroLayerMap_injective hJ hc,zeroLayerMap_surjective hJ hc hz⟩

def zeroLabelEquiv (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) : Label q J c ≃ Label q J' c' :=
  Equiv.sumCongr (Equiv.refl _) (zeroLayerEquiv hJ hc hz)

variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]
variable {n d : ℕ} {O : ℕ → Submodule K (MvPolynomial σ K)}

def zeroLayerParameters (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) (p : Space n d q J c O) : Space n d q J' c' O :=
  (fun i => p.1 ((zeroLabelEquiv hJ hc hz).symm i),
    fun j i => if hj : j.val∈J then p.2 ⟨j.val,hj⟩ (Fin.cast (hc _ hj).symm i) else 0)

@[simp] theorem zeroLayerParameters_scalar (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) (p : Space n d q J c O) (i : Label q J c) :
    (zeroLayerParameters hJ hc hz p).1 (zeroLabelEquiv hJ hc hz i)=p.1 i := by
  change p.1 ((zeroLabelEquiv hJ hc hz).symm (zeroLabelEquiv hJ hc hz i))=p.1 i
  rw [Equiv.symm_apply_apply]

@[simp] theorem zeroLayerParameters_generator (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) (p : Space n d q J c O) (i : Label q J c) :
    generator (zeroLayerParameters hJ hc hz p) (zeroLabelEquiv hJ hc hz i)=generator p i := by
  unfold generator scalar
  rw [zeroLayerParameters_scalar]
  congr 1
  rcases i with i | ⟨j,i⟩
  · rfl
  · change ((zeroLayerParameters hJ hc hz p).2
      ⟨j.val,hJ j.property⟩ (Fin.cast (hc _ j.property) i)).val=(p.2 j i).val
    simp only [zeroLayerParameters,dif_pos j.property]
    have hcast : Fin.cast (hc _ j.property).symm (Fin.cast (hc _ j.property) i)=i := Fin.ext rfl
    rw [hcast]

end Froberg.PreparedParameters

namespace Froberg.PreparedTarget
open Froberg MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J J' : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def zeroLayers (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) (p : Space m d q f u J c O) : Space m d q f u J' c' O :=
  (PreparedParameters.zeroLayerParameters hJ hc hz p.1,p.2)

def zeroLabels (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) : Label q f u J c ≃ Label q f u J' c' :=
  Equiv.sumCongr (PreparedParameters.zeroLabelEquiv hJ hc hz) (Equiv.refl _)

@[simp] theorem zeroLayers_generator (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) (p : Space m d q f u J c O)
    (U : Fin u → Forms K h d) (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (i : Label q f u J c) :
    renamedGenerator U P (zeroLayers hJ hc hz p) (zeroLabels hJ hc hz i)=renamedGenerator U P p i := by
  unfold renamedGenerator
  congr 1
  rcases i with i | (i | i)
  · change generator U P (zeroLayers hJ hc hz p)
      (Sum.inl (PreparedParameters.zeroLabelEquiv hJ hc hz i))=generator U P p (Sum.inl i)
    rw [generator_prepared,generator_prepared]
    exact PreparedParameters.zeroLayerParameters_generator hJ hc hz p.1 i
  · rfl
  · rfl

theorem zeroLayers_target_lifts (hJ : J⊆J') (hc : ∀ j∈J,c j=c' j)
    (hz : ∀ j∈J',j∉J → c' j=0) (p : Space m d q f u J c O)
    (U : Fin u → Forms K h d) (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K)
    (hlift : ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator U P p)))*Forms K (h+m) d) d b) :
    ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator U P (zeroLayers hJ hc hz p))))*Forms K (h+m) d) d b := by
  intro b hb hbd
  apply targetLift_mono _ (hlift b hb hbd)
  apply mul_le_mul' _ le_rfl
  apply Submodule.span_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨zeroLabels hJ hc hz i,zeroLayers_generator hJ hc hz p U P i⟩

end Froberg.PreparedTarget
