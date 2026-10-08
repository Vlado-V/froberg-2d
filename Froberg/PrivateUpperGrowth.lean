import Froberg.PrivateQuotientDimensions
import Froberg.QuotientUpperGrowth

/-! Upper-half expansion after adding the fixed private columns. -/
noncomputable section
namespace Froberg.PrivateColumns
open Module OuterInjection AttachedMultiplication
variable {K : Type*} [Field K] {a z s k b h : ℕ}

lemma private_upper_growth (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (hn : 0 < a+z) (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val))
    (hA : 0 < finrank K (PrivateSourceSpace ι u)) (G : ℝ)
    (hg : ∀ S : Submodule K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))),
      ((finrank K (CoreTargetSpace (z := z) (fun i => u (Sum.inl i))) : ℝ)/
        finrank K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))))*finrank K S+
      G*min (finrank K S : ℝ)
        ((finrank K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))) : ℝ)-finrank K S)  ≤ 
      (finrank K (outerImage (d := s+1) (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z) S) : ℝ))
    (L : Submodule K (PrivateSourceSpace ι u))
    (hL : (finrank K (PrivateSourceSpace ι u) : ℝ)/2 ≤ finrank K L) :
    ((finrank K (PrivateTargetSpace ι u) : ℝ)/finrank K (PrivateSourceSpace ι u))*finrank K L+
      (G-((b : ℝ)*((a+z+(s+1)-1).choose (s+1) : ℝ))/finrank K (PrivateSourceSpace ι u))*
        ((finrank K (PrivateSourceSpace ι u) : ℝ)-finrank K L)  ≤ 
      (finrank K (outerImage (d := s+1) (attachedExponent ι) u (attachedExponent_degree ι) L) : ℝ) := by
  have hbnd := SurjectiveImage.quotient_upper_growth
    (quotientMultiply (d := s+1) (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z))
    (quotientMultiply (d := s+1) (attachedExponent ι) u (attachedExponent_degree ι))
    (quotientFactor (c := 0) ι u) (quotientFactor (c := s+1) ι u)
    (quotientFactor_surjective ι u) (quotientFactor_surjective ι u)
    (quotientFactor_mul ι u) hA G hg L hL
  have hkt := quotientFactor_ker_finrank (c := s+1) hs ι hh.ge
    (private_small_fiber_bound hk hs hh) u hu hn le_rfl
  simp only [hkt,Nat.cast_mul] at hbnd
  have hpos : (0 : ℝ) < finrank K (PrivateSourceSpace ι u) := by exact_mod_cast hA
  have hnu : 0 ≤ ((finrank K (CoreTargetSpace (z := z) (fun i => u (Sum.inl i))) : ℝ)/
      finrank K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))))*(finrank K (LinearMap.ker (quotientFactor (c := 0) ι u)) : ℝ) := by positivity
  have hgain :
      ((b : ℝ)*((a+z+(s+1)-1).choose (s+1) : ℝ)-
        ((finrank K (CoreTargetSpace (z := z) (fun i => u (Sum.inl i))) : ℝ)/
        finrank K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))))*(finrank K (LinearMap.ker (quotientFactor (c := 0) ι u)) : ℝ))/finrank K (PrivateSourceSpace ι u)  ≤ 
      ((b : ℝ)*((a+z+(s+1)-1).choose (s+1) : ℝ))/finrank K (PrivateSourceSpace ι u) :=
    div_le_div_of_nonneg_right (by linarith) hpos.le
  have hcod : 0 ≤ (finrank K (PrivateSourceSpace ι u) : ℝ)-finrank K L := by
    exact sub_nonneg.mpr (by exact_mod_cast Submodule.finrank_le L)
  have hprod := mul_le_mul_of_nonneg_right (sub_le_sub_left hgain G) hcod
  exact (add_le_add le_rfl hprod).trans hbnd

end Froberg.PrivateColumns
