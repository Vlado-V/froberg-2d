module

public import Froberg.PrivateLowerNumeric
public import Froberg.PrivateQuotientDimensions
public import Froberg.LowerHalfShadowTransfer
public import Froberg.OuterShadowTransfer

@[expose] public section

/-! The lower-half private estimate for actual polynomial quotient subspaces. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset Module MonomialExpansion OuterInjection AttachedMultiplication
open Quartic.HomogeneousCoefficientCoordinates
variable {K : Type*} [Field K] {a z s k b h : ℕ}

lemma private_lower_growth (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (hn : 0 < a+z) (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h →
      LinearIndependent K (fun i : U => attachedVectors v w i.val))
    (hm : MixedExterior.UniversalMixedPosition (attachedVectors v w))
    (R G P : ℝ)
    (hbase : ∀ (ell : Degree (a+z) s → ℝ) (out : Degree (a+z) (2*s+1) → ℝ),
      (∀ α,0 ≤ ell α ∧ ell α ≤ (k : ℝ)*(profileAmbientCapacity s-if (corePart α.val).degree=s then 1 else 0)) →
      (∀ β,0 ≤ out β) →
      (∀ α β,α.val ≤ β.val →
        min ((k : ℝ)*(profileAmbientCapacity s-((corePart β.val).degree.choose s : ℝ))) (ell α) ≤ out β) →
      R*(∑ α,ell α)+G*min (∑ α,ell α)
        ((k : ℝ)*(∑ i,finiteSourceProfile (profileAmbientCapacity s) s a z i)-∑ α,ell α) ≤ ∑ β,out β)
    (hregular : P ≤ R+G-(h*(b*(a+z+s-1).choose s) : ℕ))
    (hprivate : P ≤ (privateGoodMultipliers a s ι).card)
    (L : Submodule K (PrivateSourceSpace ι (attachedVectors v w)))
    (hL : 2*finrank K L ≤ finrank K (PrivateSourceSpace ι (attachedVectors v w))) :
    (P-(h*((h*2^h)*(a+z+s-1).choose s) : ℕ))*(finrank K L : ℝ) ≤
      (finrank K (outerImage (d := s+1) (attachedExponent ι) (attachedVectors v w)
        (attachedExponent_degree ι) L) : ℝ) := by
  classical
  have hv := MixedExterior.full_spark_comp (attachedVectors v w) hu
    (Function.Embedding.inl : Labels k a s ↪ _)
  have hsize (β : Exponent (a+z) (s+(s+1))) :
      (labelsBelow (attachedExponent (k := k) (s := s) ι) β.val).card ≤ h := by
    have hc := card_attached_divisors_le hs ι hh.ge (private_small_fiber_bound hk hs hh)
      β.val (by rw [β.property]; omega)
    simpa only [labelsBelow,Fintype.card_subtype] using hc
  have hbound (C : (α : Exponent (a+z) s) →
      Submodule K ((Fin h → K) ⧸ relationFiber (attachedExponent ι) (attachedVectors v w) α.val))
      (hC : 2*(∑ α,finrank K (C α)) ≤ finrank K (PrivateSourceSpace ι (attachedVectors v w))) :
      (0 : ℝ)*(∑ α,finrank K (C α) : ℕ)+P*(∑ α,finrank K (C α) : ℕ) ≤
        (∑ β,idealShadow (attachedExponent ι) (attachedVectors v w) C β : ℕ) := by
    let ell := fun α : Degree (a+z) s => finrank K (C (degreeExponentEquiv (a+z) s α))
    let rel := fun (α : Degree (a+z) s) (β : Degree (a+z) (2*s+1)) => α.val ≤ β.val
    have hell (α : Degree (a+z) s) : ell α ≤ fiberCapacity ι v w α.val :=
      Submodule.finrank_le (C (degreeExponentEquiv (a+z) s α))
    have he : (∑ α,ell α)=∑ α,finrank K (C α) :=
      (degreeExponentEquiv (a+z) s).sum_comp (fun α => finrank K (C α))
    have hdim := private_source_dimension_add hk hs hh hn ι (attachedVectors v w) hu
    have hcore : (2 : ℝ)*(∑ α,ell α : ℕ) ≤
        (k : ℝ)*(∑ i,finiteSourceProfile (profileAmbientCapacity s) s a z i) := by
      rw [← outer_source_dimension_profile hh v hv]
      have hle : 2*(∑ α,ell α) ≤ finrank K (CoreSourceSpace (z := z) v) := by
        rw [he]
        change finrank K (PrivateSourceSpace ι (attachedVectors v w))+b=finrank K (CoreSourceSpace (z := z) v) at hdim
        omega
      exact_mod_cast hle
    have hnum := private_lower_numeric hh (by omega) hn ι v w hv R G P hbase hregular hprivate ell hell hcore
    have hpt (β : Degree (a+z) (2*s+1)) :
        ShadowDeletion.shadow rel ell (fun β => fiberCapacity ι v w β.val) β ≤
          idealShadow (attachedExponent ι) (attachedVectors v w) C (outerTargetExponentEquiv (a+z) s β) := by
      unfold ShadowDeletion.shadow
      apply Finset.sup_le
      intro α _
      split_ifs with hab
      · exact min_le_idealShadow (attachedExponent ι) (attachedVectors v w) C
          (degreeExponentEquiv (a+z) s α) (outerTargetExponentEquiv (a+z) s β) hab
      · exact Nat.zero_le _
    have htot := sum_le_sum (fun β (_ : β∈(univ : Finset (Degree (a+z) (2*s+1)))) => hpt β)
    rw [(outerTargetExponentEquiv (a+z) s).sum_comp
      (fun β => idealShadow (attachedExponent ι) (attachedVectors v w) C β)] at htot
    rw [he] at hnum
    simpa only [zero_mul,zero_add] using hnum.trans (Nat.cast_le.mpr htot)
  simpa only [zero_mul,zero_add] using lower_half_growth_of_ideal_bound
    (attachedExponent ι) (attachedVectors v w) (attachedExponent_degree ι) hn hu hm hsize 0 P hbound L hL

end Froberg.PrivateColumns
