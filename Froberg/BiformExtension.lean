module

public import Froberg.BiformTensorFamily

@[expose] public section

/-! Increasing a generator count preserves the target surjection, including
when all output coefficients are required to stay in a fixed subspace. -/
noncomputable section
namespace Froberg
open TensorProduct
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
variable {h m j e x y : ℕ}

@[simp] theorem biformFamilyMap_single [DecidableEq κ]
    (o : κ → Forms K h j) (f : κ → Forms K m e) (i : κ)
    (z : Forms K h x ⊗[K] Forms K m y) :
    biformFamilyMap o f (Pi.single i z) =
      TensorProduct.map (gradedMultiplication (o i)) (gradedMultiplication (f i)) z := by
  rw [biformFamilyMap_apply,Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [Pi.single_apply,hki]
  · simp

theorem biformFamilyMap_surjective_of_entries
    (o : ι → Forms K h j) (f : ι → Forms K m e)
    (O : κ → Forms K h j) (F : κ → Forms K m e) (t : ι → κ)
    (hO : ∀ i, O (t i)=o i) (hF : ∀ i, F (t i)=f i)
    (hs : Function.Surjective (biformFamilyMap (x := x) (y := y) o f)) :
    Function.Surjective (biformFamilyMap (x := x) (y := y) O F) := by
  classical
  intro z
  obtain ⟨c,rfl⟩ := hs z
  change biformFamilyMap o f c ∈ (biformFamilyMap (x := x) (y := y) O F).range
  rw [biformFamilyMap_apply]
  apply Submodule.sum_mem
  intro i _
  refine ⟨Pi.single (t i) (c i),?_⟩
  simp only [biformFamilyMap_single,hO,hF]

theorem biformFamily_surjective_extend_subspace {r R : ℕ}
    (W : Submodule K (Forms K h j)) (o : Fin r → W) (f : Fin r → Forms K m e)
    (hcount : r ≤ R)
    (hs : Function.Surjective (biformFamilyMap (x := x) (y := y) (fun i => (o i).val) f)) :
    ∃ (O : Fin R → W) (F : Fin R → Forms K m e),
      Function.Surjective (biformFamilyMap (x := x) (y := y) (fun i => (O i).val) F) := by
  let t : Fin r ↪ Fin R := Fin.castLEEmb hcount
  let O := Function.extend t o (fun _ => 0)
  let F := Function.extend t f (fun _ => 0)
  refine ⟨O,F,biformFamilyMap_surjective_of_entries _ f _ F t ?_ ?_ hs⟩
  · intro i
    exact congrArg Subtype.val (t.injective.extend_apply o _ i)
  · intro i
    exact t.injective.extend_apply f _ i

end Froberg
