import Froberg.BiformMultiplication
import Quartic.PolynomialRankOpen

/-! Polynomial rank certificates for the actual biform target maps. -/
noncomputable section
namespace Froberg
open TensorProduct Module MvPolynomial
open Quartic
variable {K ι P : Type*} [Field K] [Fintype ι]
variable {h m j e x y : ℕ}

local instance tensorGroup (n m u v : ℕ) : AddCommGroup (Forms K n u ⊗[K] Forms K m v) :=
  Module.addCommMonoidToAddCommGroup K

theorem biformFamilyMap_polynomial
    (o : (P → K) → ι → Forms K h j) (f : (P → K) → ι → Forms K m e)
    (ho : ∀ i, IsPolynomialFamily (fun a => o a i))
    (hf : ∀ i, IsPolynomialFamily (fun a => f a i)) :
    IsPolynomialFamily (fun a => biformFamilyMap (x := x) (y := y) (o a) (f a)) := by
  apply isPolynomialFamily_linearMap
  intro c
  have ht (i : ι) (z : Forms K h x ⊗[K] Forms K m y) :
      IsPolynomialFamily (fun a => TensorProduct.map
        (gradedMultiplication (o a i)) (gradedMultiplication (f a i)) z) := by
    induction z using TensorProduct.induction_on with
    | zero =>
      simpa only [map_zero] using isPolynomialFamily_const (ι := P) (K := K)
        (0 : Forms K h (j+x) ⊗[K] Forms K m (e+y))
    | tmul u v =>
      have hu := (ho i).linear_comp (gradedMultiplication.flip u)
      have hv := (hf i).linear_comp (gradedMultiplication.flip v)
      simpa only [TensorProduct.map_tmul,LinearMap.flip_apply,TensorProduct.mk_apply] using
        hu.bilinear hv (TensorProduct.mk K _ _)
    | add z z' hz hz' => simpa only [map_add] using hz.add hz'
  simpa only [biformFamilyMap_apply] using IsPolynomialFamily.sum (fun i => ht i (c i))

/-- The witness produces an explicit nonempty principal open in any polynomial
parameterization of the actual output and scalar forms. -/
theorem biformFamilyMap_surjective_principal_open
    (o : (P → K) → ι → Forms K h j) (f : (P → K) → ι → Forms K m e)
    (ho : ∀ i, IsPolynomialFamily (fun a => o a i))
    (hf : ∀ i, IsPolynomialFamily (fun a => f a i))
    (a₀ : P → K)
    (ha₀ : Function.Surjective (biformFamilyMap (x := x) (y := y) (o a₀) (f a₀))) :
    ∃ D : MvPolynomial P K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      Function.Surjective (biformFamilyMap (x := x) (y := y) (o a) (f a)) := by
  obtain ⟨D,hD,hRank⟩ := rank_polynomial_principal_open
    (fun a => biformFamilyMap (x := x) (y := y) (o a) (f a))
    (biformFamilyMap_polynomial o f ho hf) a₀
  refine ⟨D,hD,fun a ha => ?_⟩
  have hr := hRank a ha
  rw [LinearMap.range_eq_top.mpr ha₀,finrank_top] at hr
  apply LinearMap.range_eq_top.mp
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hr)

end Froberg
