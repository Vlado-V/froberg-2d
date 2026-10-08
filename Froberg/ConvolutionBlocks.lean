import Froberg.ConvolutionFamily

/-! Finite convolution blocks inside a prescribed output space. -/
noncomputable section
namespace Froberg
open TensorProduct Module
variable {K V W ι κ : Type*} [Field K]
  [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
  [Fintype ι] [Fintype κ]

/-- Every source generator is an actual target generator after output projection. -/
theorem vectorFormFamily_range_transfer {m e t : ℕ} (P : V →ₗ[K] W)
    (o : ι → V) (f : ι → Forms K m e) (O : κ → W) (F : κ → Forms K m e)
    (j : ι → κ) (ho : ∀ i, O (j i) = P (o i)) (hf : ∀ i, F (j i) = f i)
    (hsource : Function.Surjective (vectorFormFamilyMap (t := t) o f))
    (v : V) (g : Forms K m (e+t)) :
    P v ⊗ₜ[K] g ∈ (vectorFormFamilyMap (t := t) O F).range := by
  obtain ⟨c, hc⟩ := hsource (v ⊗ₜ[K] g)
  have hmap := congrArg (TensorProduct.map P (LinearMap.id : Forms K m (e+t) →ₗ[K] _)) hc
  simp only [vectorFormFamilyMap_apply, map_sum, TensorProduct.map_tmul,
    LinearMap.id_apply] at hmap
  rw [← hmap]
  apply Submodule.sum_mem
  intro i hi
  rw [← ho i, ← hf i]
  exact vectorFormFamilyMap_single_mem O F (j i) (c i)

/-- Independent convolution blocks may be projected onto any prescribed output
space. The projection need only be surjective; the last block may be partial. -/
theorem convolution_blocks_surjective [Infinite K] {a e m k : ℕ}
    (ha : 0<a) (hm : 0<m) (P : (Fin k → Forms K a e) →ₗ[K] W)
    (hP : Function.Surjective P) :
    ∃ (o : Fin k × ConvolutionSubset (m+a-1) e → W)
      (f : Fin k × ConvolutionSubset (m+a-1) e → Forms K m e),
      Function.Surjective (vectorFormFamilyMap (t := a-1) o f) := by
  classical
  obtain ⟨o, f, hF⟩ := exists_convolution_family (K := K) (e := e) ha hm
  let O : Fin k × ConvolutionSubset (m+a-1) e → W :=
    fun z => P (Pi.single z.1 (o z.2))
  let F : Fin k × ConvolutionSubset (m+a-1) e → Forms K m e := fun z => f z.2
  refine ⟨O, F, ?_⟩
  let R := (vectorFormFamilyMap (t := a-1) O F).range
  have hsingle (i : Fin k) (v : Forms K a e) (g : Forms K m (e+(a-1))) :
      P (Pi.single i v) ⊗ₜ[K] g ∈ R := by
    exact vectorFormFamily_range_transfer (P.comp (LinearMap.single _ _ i)) o f O F
      (fun j => (i,j)) (fun _ => rfl) (fun _ => rfl) hF v g
  have hwhole (v : Fin k → Forms K a e) (g : Forms K m (e+(a-1))) :
      P v ⊗ₜ[K] g ∈ R := by
    have hv : (∑ i : Fin k, Pi.single i (v i)) = v := by ext i; simp
    rw [← hv, map_sum, TensorProduct.sum_tmul]
    exact Submodule.sum_mem R fun i hi => hsingle i (v i) g
  have hall (z : W ⊗[K] Forms K m (e+(a-1))) : z ∈ R := by
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem R
    | tmul w g =>
      obtain ⟨v, rfl⟩ := hP w
      exact hwhole v g
    | add x y hx hy => exact Submodule.add_mem R hx hy
  exact fun z => hall z

theorem convolution_blocks_card {a e m k : ℕ} (ha : 0<a) (hm : 0<m) :
    Fintype.card (Fin k × ConvolutionSubset (m+a-1) e) = k*(m+a+e-2).choose e := by
  rw [Fintype.card_prod, Fintype.card_fin, convolution_family_card ha hm]

end Froberg
