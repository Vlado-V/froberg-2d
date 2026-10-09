module

public import Froberg.BiformMultiplication
public import Froberg.PrefixSurjectivity

@[expose] public section

/-! The strict-prefix theorem supplies the output spaces for the middle rows
of B.7, and convolution turns them into actual biform generators. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K : Type*} [Field K] [Infinite K]
variable {h m j e x y q r : ℕ}

theorem outputMultiplication_surjective_of_prefix (Q : Fin q → Forms K h j)
    (hQ : Function.Surjective (prefixMultiplication Q x)) :
    Function.Surjective (outputMultiplication (x := x) (Fintype.linearCombination K Q)) := by
  classical
  intro z
  obtain ⟨c,hc⟩ := hQ z
  refine ⟨∑ i : Fin q, (Pi.single i (1 : K)) ⊗ₜ[K] c i, ?_⟩
  rw [map_sum]
  simp only [outputMultiplication_tmul,Fintype.linearCombination_apply_single,one_smul]
  simpa [prefixMultiplication] using hc

/-- The biform generators stay inside the span of the chosen output family. -/
theorem exists_biform_family_of_prefix (hm : 0 < m) (Q : Fin q → Forms K h j)
    (hQ : Function.Surjective (prefixMultiplication Q x))
    (hr : convolutionBlockCount q (y+1) e * (m+(y+1)+e-2).choose e ≤ r) :
    ∃ (o : Fin r → Forms K h j) (f : Fin r → Forms K m e),
      (∀ i, o i ∈ Submodule.span K (Set.range Q)) ∧
      Function.Surjective (biformFamilyMap (x := x) (y := y) o f) := by
  have hdim : finrank K (Fin q → K)=q := by simp
  obtain ⟨v,f,hv⟩ := exists_convolution_family_of_count (K := K) (W := Fin q → K)
    (a := y+1) (e := e) (m := m) (r := r) (by omega) hm (by simpa only [hdim] using hr)
  refine ⟨fun i => Fintype.linearCombination K Q (v i),f,?_,?_⟩
  · intro i
    rw [← Fintype.range_linearCombination]
    exact ⟨v i,rfl⟩
  · exact biformFamilyMap_surjective_of_output (Fintype.linearCombination K Q)
      (outputMultiplication_surjective_of_prefix Q hQ) v f hv

/-- A finite, entirely explicit middle-row witness from the proved strict-prefix
bound and the rounded convolution generator count. -/
theorem exists_biform_family_of_prefix_counts (hh : 0 < h) (hm : 0 < m) (hxj : x < j)
    (hlarge : (x+j).choose x*((x+j).choose x*j.choose x) ≤ h)
    (hq : (h+(j+x)-1).choose (j+x) ≤ q*(h+x-1).choose x)
    (hr : convolutionBlockCount q (y+1) e*(m+(y+1)+e-2).choose e ≤ r) :
    ∃ (o : Fin r → Forms K h j) (f : Fin r → Forms K m e),
      Function.Surjective (biformFamilyMap (x := x) (y := y) o f) := by
  obtain ⟨Q,hQ⟩ := exists_prefix_surjective_of_large_variables (K := K) hh hxj hlarge hq
  obtain ⟨o,f,ho,hf⟩ := exists_biform_family_of_prefix (y := y) hm Q hQ hr
  exact ⟨o,f,hf⟩

end Froberg
