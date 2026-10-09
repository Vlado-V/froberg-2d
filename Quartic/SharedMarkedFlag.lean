module

public import Quartic.SharedChildFlag

@[expose] public section

/-! A common child flag from a specified surviving square, valid in every
infinite field. This separates the open-condition argument from polarization. -/
noncomputable section
namespace Quartic.SharedMarkedFlag
open Module MvPolynomial EndpointHomology SharedChildFlag
variable {K ι : Type*} [Field K] {n r : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem principal_open [Infinite K]
    (f : (ι → K) → (Fin (r+1) → Forms K n 2))
    (hf : IsPolynomialFamily f) (hfSurj : Function.Surjective f)
    (hlow : GenericQuartic K n r) (hhigh : GenericQuartic K n (r+1))
    (hlo : 0 < Counts.chi n r) (hhi : Counts.chi n (r+1) ≤ 0)
    (q₀ : Fin r → Forms K n 2)
    (hd₀ : finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q₀ i).val)))) = expectedDimension n r)
    (v : Forms K n 2) (hv : mulQuadratic v v ∉ (quadraticMultiplication q₀).range) :
    ∃ D : MvPolynomial ι K,(∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → Conditions (f a) := by
  classical
  let pre := fun a => prefixFamily (f a)
  have hpre : IsPolynomialFamily pre :=
    hf.linear_comp (LinearMap.funLeft K (Forms K n 2) Fin.castSucc)
  have hpreSurj : Function.Surjective pre := by
    intro q
    obtain ⟨a,ha⟩ := hfSurj (Fin.snoc q 0)
    refine ⟨a,?_⟩
    funext i
    change (f a) i.castSucc=q i
    rw [ha,Fin.snoc_castSucc]
  obtain ⟨A,⟨a₀,ha₀⟩,hA⟩ := quartic_open pre hpre hpreSurj hlow
  obtain ⟨B,⟨b₀,hb₀⟩,hB⟩ := quartic_open f hf hfSurj hhigh
  obtain ⟨a₁,ha₁⟩ := hfSurj (Fin.snoc q₀ v)
  have hpre₁ : pre a₁=q₀ := by
    funext i
    change (f a₁) i.castSucc=q₀ i
    rw [ha₁,Fin.snoc_castSucc]
  have hsquare₁ : mulQuadratic (f a₁ (Fin.last r)) (f a₁ (Fin.last r)) ∉
      (quadraticMultiplication (pre a₁)).range := by
    rw [hpre₁,ha₁,Fin.snoc_last]
    exact hv
  obtain ⟨C,hC,hCrank⟩ := rank_polynomial_principal_open (fun a => withSquare (f a))
    (withSquare_polynomial f hf) a₁
  have hCdim : finrank K (withSquare (f a₁)).range=
      finrank K (quadraticMultiplication q₀).range+1 := by
    rw [withSquare_range,Submodule.finrank_sup_span_singleton hsquare₁]
    rw [hpre₁]
  have hA0 : A≠0 := by intro h; simp [h] at ha₀
  have hB0 : B≠0 := by intro h; simp [h] at hb₀
  have hC0 : C≠0 := by intro h; simp [h] at hC
  obtain ⟨a₂,ha₂⟩ := nonempty_principal_intersection (![A,B,C] : Fin 3 → MvPolynomial ι K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨A*B*C,⟨a₂,?_⟩,?_⟩
  · simp only [map_mul]
    exact mul_ne_zero (mul_ne_zero (ha₂ 0) (ha₂ 1)) (ha₂ 2)
  · intro a ha
    rw [map_mul,mul_ne_zero_iff,map_mul,mul_ne_zero_iff] at ha
    obtain ⟨hip,hdp⟩ := hA a ha.1.1
    obtain ⟨hi,hd⟩ := hB a ha.1.2
    have hsurj : Function.Surjective (quadraticMultiplication (f a)) := by
      apply LinearMap.range_eq_top.mp
      apply Submodule.eq_top_of_finrank_eq
      have he := quartic_quotient_add_rank (f a)
      rw [hd] at he
      change (Counts.chi n (r+1)).toNat+_=_ at he
      rw [Int.toNat_of_nonpos hhi] at he
      simpa only [zero_add,finrank_quartics] using he
    refine ⟨hi,hsurj,kernel_le_of_expected (pre a) hip hdp hlo.le,?_⟩
    intro hsquare
    have hsame : (withSquare (f a)).range=(quadraticMultiplication (pre a)).range := by
      rw [withSquare_range]
      exact sup_eq_left.mpr (Submodule.span_le.mpr (by intro v hv; rcases hv with rfl; exact hsquare))
    have hr := hCrank a ha.2
    rw [hCdim,hsame] at hr
    have hd0 := quartic_quotient_add_rank q₀
    have hda := quartic_quotient_add_rank (pre a)
    rw [hd₀] at hd0
    rw [hdp] at hda
    omega

end Quartic.SharedMarkedFlag
