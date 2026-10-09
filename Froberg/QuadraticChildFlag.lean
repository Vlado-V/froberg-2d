module

public import Froberg.QuadraticDefectBridge
public import Quartic.FixedBlockChildOpen
public import Quartic.SquaresNonTwo

@[expose] public section

/-! One actual generic child flag with its distinguished square retained. -/
noncomputable section
namespace Froberg.QuadraticChildFlag
open Module MvPolynomial Quartic EndpointHomology SharedChildFlag
open FixedBlockChildOpen
variable {K : Type*} [Field K] [Infinite K] {n r : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

abbrev Coker (q : Fin r → Forms K n 2) :=
  Quartic.QuarticQuotient K n (Submodule.span K (Set.range (fun i => (q i).val)))

/-- The complete generic flag is selected on the actual child coefficient space. -/
theorem generic_flag_open (hn : 0<n) (hr : r+1≤(n+1).choose 2) :
    ∃ D : MvPolynomial (ChildIndex n (r+1)) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        LinearIndependent K (decode a) ∧
        finrank K (Coker (decode a)) = genericCokernel K n 2 (r+1) ∧
        finrank K (QuarticHomology (prefixFamily (decode a))) = genericHomology K n 2 r := by
  classical
  obtain ⟨D,⟨b,hb⟩,hD⟩ := generic_flag_principal_open (K := K) (d := 2) hn
    (Nat.le_succ r) (by simpa using hr)
  let L : (ChildIndex n (r+1) → K) →ₗ[K] (CoefficientIndex n 2 (r+1) → K) :=
    coefficientCoordinates.toLinearMap.comp decode
  let P := Quartic.MiddleCoordinates.substituteLinear L D
  have hev (a : ChildIndex n (r+1) → K) : eval a P = eval (L a) D :=
    Quartic.MiddleCoordinates.eval_substituteLinear L a D
  have hforms (a : ChildIndex n (r+1) → K) : coefficientForms K n 2 (r+1) (L a) = decode a :=
    coefficientCoordinates.symm_apply_apply (decode a)
  obtain ⟨a,ha⟩ := decode_surjective (coefficientForms K n 2 (r+1) b)
  have hLa : L a = b := by
    change coefficientCoordinates (decode a)=b
    rw [ha]
    exact coefficientCoordinates.apply_symm_apply b
  refine ⟨P,⟨a,by rw [hev,hLa]; exact hb⟩,?_⟩
  intro a ha
  obtain ⟨hi,hc,_,hp⟩ := hD (L a) ((hev a) ▸ ha)
  rw [hforms] at hi hp
  refine ⟨hi,?_,?_⟩
  · unfold coefficientCokernel coefficientSpace at hc
    rw [hforms] at hc
    exact hc
  · rw [QuadraticDefectBridge.homology_eq hn (prefixFamily (decode a))
      (hi.comp _ (Fin.castSucc_injective r))]
    exact hp

/-- Generic ranks and a surviving distinguished square hold for the same flag. -/
theorem principal_open (hn : 0<n) (hr : r+1≤(n+1).choose 2)
    (hchi : 0<Quartic.Counts.chi n r) (h2 : (2 : K)≠0) :
    ∃ D : MvPolynomial (ChildIndex n (r+1)) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 →
        LinearIndependent K (decode a) ∧
        finrank K (Coker (decode a)) = genericCokernel K n 2 (r+1) ∧
        finrank K (QuarticHomology (prefixFamily (decode a))) = genericHomology K n 2 r ∧
        mulQuadratic (decode a (Fin.last r)) (decode a (Fin.last r)) ∉
          (quadraticMultiplication (prefixFamily (decode a))).range := by
  classical
  obtain ⟨A,⟨a₀,ha₀⟩,hA⟩ := generic_flag_open (K := K) hn hr
  obtain ⟨hi₀,_,hh₀⟩ := hA a₀ ha₀
  let pre := fun a : ChildIndex n (r+1) → K => prefixFamily (decode a)
  have hprelin : LinearIndependent K (pre a₀) := hi₀.comp _ (Fin.castSucc_injective r)
  have hproper : quarticProducts K n
      (Submodule.span K (Set.range (fun i => (pre a₀ i).val))) ≠ ⊤ := by
    intro htop
    have he := quartic_euler_identity (pre a₀) hprelin
    have hz : finrank K (Coker (pre a₀))=0 := by
      change finrank K ((Quartic.Forms K n 4) ⧸ quarticProducts K n _)=0
      rw [htop,Submodule.finrank_quotient,finrank_top,Nat.sub_self]
    change (finrank K (Coker (pre a₀)):ℤ)-_= _ at he
    rw [hz] at he
    omega
  obtain ⟨v,hv⟩ := Quartic.SquaresNonTwo.exists_square_outside h2 _ hproper
  obtain ⟨a₁,ha₁⟩ := decode_surjective (Fin.snoc (pre a₀) v)
  have hpre₁ : pre a₁=pre a₀ := by
    funext i
    change decode a₁ i.castSucc=pre a₀ i
    rw [ha₁,Fin.snoc_castSucc]
  have hsquare₁ : mulQuadratic (decode a₁ (Fin.last r)) (decode a₁ (Fin.last r)) ∉
      (quadraticMultiplication (pre a₁)).range := by
    rw [hpre₁,ha₁,Fin.snoc_last,Quartic.range_quadraticMultiplication]
    exact hv
  obtain ⟨B,hB,hBrank⟩ := Quartic.rank_polynomial_principal_open
    (fun a => withSquare (decode a))
    (withSquare_polynomial decode (Quartic.isPolynomialFamily_linear decode)) a₁
  have hBdim : finrank K (withSquare (decode a₁)).range =
      finrank K (quadraticMultiplication (pre a₀)).range+1 := by
    rw [withSquare_range,Submodule.finrank_sup_span_singleton hsquare₁,hpre₁]
  have hBex : ∃ a,eval a B≠0 := ⟨a₁,hB⟩
  obtain ⟨a₂,haA,haB⟩ := Froberg.principal_opens_intersect ⟨a₀,ha₀⟩ hBex
  refine ⟨A*B,⟨a₂,by simpa only [map_mul] using mul_ne_zero haA haB⟩,?_⟩
  intro a ha
  obtain ⟨haA,haB⟩ := mul_ne_zero_iff.mp (show eval a A*eval a B≠0 by simpa using ha)
  obtain ⟨hi,hc,hh⟩ := hA a haA
  refine ⟨hi,hc,hh,?_⟩
  intro hsquare
  have he₀ := quartic_euler_identity (pre a₀) hprelin
  have he := quartic_euler_identity (pre a) (hi.comp _ (Fin.castSucc_injective r))
  have hd : finrank K (Coker (pre a))=finrank K (Coker (pre a₀)) := by
    change (finrank K (Coker (pre a)):ℤ)-_= _ at he
    change (finrank K (Coker (pre a₀)):ℤ)-_= _ at he₀
    rw [hh] at he
    rw [hh₀] at he₀
    omega
  have hsame : (withSquare (decode a)).range=(quadraticMultiplication (pre a)).range := by
    rw [withSquare_range]
    exact sup_eq_left.mpr (Submodule.span_le.mpr (by
      intro x hx; rcases hx with rfl; exact hsquare))
  have hbound := hBrank a haB
  rw [hBdim,hsame] at hbound
  have hr₀ := quartic_quotient_add_rank (pre a₀)
  have hr := quartic_quotient_add_rank (pre a)
  change finrank K (Coker (pre a₀)) + _ = _ at hr₀
  change finrank K (Coker (pre a)) + _ = _ at hr
  rw [hd] at hr
  omega

end Froberg.QuadraticChildFlag
