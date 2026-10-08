import Froberg.PrivateModel
import Froberg.UniformOuterGrowth

/-! Exact source and target dimension shifts for adjoining private columns. -/
noncomputable section
namespace Froberg.PrivateColumns
open Module OuterInjection AttachedMultiplication
variable {K : Type*} [Field K] {a z s k b h : ℕ}

abbrev PrivateSourceSpace (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K) :=
  (Fin h → Forms K (a+z) s) ⧸ relationSpace (d := 0) (attachedExponent ι) u (attachedExponent_degree ι)

abbrev PrivateTargetSpace (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K) :=
  (Fin h → Forms K (a+z) (s+(s+1))) ⧸ relationSpace (d := s+1)
    (attachedExponent ι) u (attachedExponent_degree ι)

lemma private_quotient_dimension_add (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (hn : 0 < a+z) (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val))
    (c : ℕ) (hc : c ≤ s+1) :
    finrank K ((Fin h → Forms K (a+z) (s+c)) ⧸ relationSpace (d := c)
      (attachedExponent ι) u (attachedExponent_degree ι)) + b*(a+z+c-1).choose c =
    finrank K ((Fin h → Forms K (a+z) (s+c)) ⧸ relationSpace (d := c)
      (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z)) := by
  have hd := (quotientFactor (c := c) ι u).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientFactor_surjective ι u),finrank_top,
    quotientFactor_ker_finrank hs ι hh.ge (private_small_fiber_bound hk hs hh) u hu hn hc] at hd
  exact hd

lemma private_source_dimension_add (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (hn : 0 < a+z) (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val)) :
    finrank K (PrivateSourceSpace ι u)+b = finrank K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))) := by
  simpa only [Nat.add_zero,Nat.choose_zero_right,mul_one] using
    private_quotient_dimension_add hk hs hh hn ι u hu 0 (Nat.zero_le _)

lemma private_target_dimension_add (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (hn : 0 < a+z) (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val)) :
    finrank K (PrivateTargetSpace ι u)+b*(a+z+(s+1)-1).choose (s+1) =
      finrank K (CoreTargetSpace (z := z) (fun i => u (Sum.inl i))) :=
  private_quotient_dimension_add hk hs hh hn ι u hu (s+1) le_rfl

end Froberg.PrivateColumns
