import Froberg.EvenBiformDecomposition
import Froberg.ParityWeights

/-! Actual homogeneous polynomial parity spaces and the complete even
coefficient decomposition used by the mixed pure generators. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d t : ℕ}

def blockWeight (h m : ℕ) : Fin h ⊕ Fin m → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

def biformParitySpace (K : Type) [Field K] (h m d : ℕ) (p : ZMod 2) :
    Submodule K (MvPolynomial (Fin h ⊕ Fin m) K) :=
  homogeneousSubmodule _ K d ⊓
    weightedHomogeneousSubmodule K (fun i => (blockWeight h m i : ZMod 2)) p

instance biformParitySpace_finite (p : ZMod 2) : Module.Finite K (biformParitySpace K h m d p) := by
  letI : Module.Finite K (homogeneousSubmodule (Fin h ⊕ Fin m) K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis _ _)
  exact Submodule.finiteDimensional_of_le (show biformParitySpace K h m d p≤
    homogeneousSubmodule _ K d from inf_le_left)

def evenBiformEmbedding (ht : t≤d) (heven : t%2=0) :
    (Forms K h t ⊗[K] Forms K m (d-t)) →ₗ[K] biformParitySpace K h m d 0 :=
  (sumBiformMap (K := K) (h := h) (n := m) (a := t) (c := d-t)).codRestrict _ (by
    intro v
    have hm : sumBiformMap v∈biformImage (Forms K h t) (Forms K m (d-t)) :=
      sumBiformMap_range.le ⟨v,rfl⟩
    refine ⟨?_,?_⟩
    · have hh := biformImage_homogeneous (Forms K h t) (Forms K m (d-t)) le_rfl le_rfl hm
      change (sumBiformMap v).IsHomogeneous d
      change (sumBiformMap v).IsHomogeneous (t+(d-t)) at hh
      simpa only [Nat.add_sub_of_le ht] using hh
    · apply (parity_homogeneous_iff (blockWeight h m) _ 0 (by decide)).2
      intro a ha
      have hw := biformImage_output_weight (Forms K h t) (Forms K m (d-t)) le_rfl hm ha
      change Finsupp.weight (blockWeight h m) a=t at hw
      rw [hw,heven])

@[simp] theorem evenBiformEmbedding_val (ht : t≤d) (heven : t%2=0)
    (v : Forms K h t ⊗[K] Forms K m (d-t)) :
    (evenBiformEmbedding ht heven v).val=sumBiformMap v := rfl

def oddBiformEmbedding (ht : t≤d) (hodd : t%2=1) :
    (Forms K h t ⊗[K] Forms K m (d-t)) →ₗ[K] biformParitySpace K h m d 1 :=
  (sumBiformMap (K := K) (h := h) (n := m) (a := t) (c := d-t)).codRestrict _ (by
    intro v
    have hm : sumBiformMap v∈biformImage (Forms K h t) (Forms K m (d-t)) :=
      sumBiformMap_range.le ⟨v,rfl⟩
    refine ⟨?_,?_⟩
    · have hh := biformImage_homogeneous (Forms K h t) (Forms K m (d-t)) le_rfl le_rfl hm
      change (sumBiformMap v).IsHomogeneous d
      change (sumBiformMap v).IsHomogeneous (t+(d-t)) at hh
      simpa only [Nat.add_sub_of_le ht] using hh
    · apply (parity_homogeneous_iff (blockWeight h m) _ 1 (by decide)).2
      intro a ha
      have hw := biformImage_output_weight (Forms K h t) (Forms K m (d-t)) le_rfl hm ha
      change Finsupp.weight (blockWeight h m) a=t at hw
      rw [hw,hodd])

@[simp] theorem oddBiformEmbedding_val (ht : t≤d) (hodd : t%2=1)
    (v : Forms K h t ⊗[K] Forms K m (d-t)) :
    (oddBiformEmbedding ht hodd v).val=sumBiformMap v := rfl

abbrev HigherEvenCoefficients (K : Type) [Field K] (h m d : ℕ) :=
  (r : Fin ((d-1)/2)) → Forms K h (2*(r.val+1)) ⊗[K] Forms K m (d-2*(r.val+1))

def positiveEvenAssembly : HigherEvenCoefficients K h m d →ₗ[K] biformParitySpace K h m d 0 :=
  ∑ r : Fin ((d-1)/2),
    (evenBiformEmbedding (t := 2*(r.val+1)) (by omega) (by omega)).comp (LinearMap.proj r)

@[simp] theorem positiveEvenAssembly_val (v : HigherEvenCoefficients K h m d) :
    (positiveEvenAssembly v).val=∑ r,sumBiformMap (v r) := by
  simp [positiveEvenAssembly]

def evenCoefficientAssembly :
    ((Forms K h 0 ⊗[K] Forms K m d) × HigherEvenCoefficients K h m d) →ₗ[K]
      biformParitySpace K h m d 0 :=
  (evenBiformEmbedding (t := 0) (Nat.zero_le d) (by omega)).coprod positiveEvenAssembly

theorem evenCoefficientAssembly_surjective (hd : Odd d) :
    Function.Surjective (evenCoefficientAssembly (K := K) (h := h) (m := m) (d := d)) := by
  intro v
  have hp := (parity_homogeneous_iff (blockWeight h m) v.val 0 (by decide)).1 v.property.2
  obtain ⟨z,c,hc⟩ := even_homogeneous_biform_decomposition hd v.val v.property.1 hp
  refine ⟨(z,c),?_⟩
  apply Subtype.ext
  change (evenBiformEmbedding (t := 0) (Nat.zero_le d) (by omega) z).val+
    (positiveEvenAssembly c).val=v.val
  rw [evenBiformEmbedding_val,positiveEvenAssembly_val]
  exact hc.symm

end Froberg
