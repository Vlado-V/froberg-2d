import Froberg.PrivateInjection
import Froberg.OuterGeneric
import Froberg.OuterMultiplication
import Froberg.SurjectiveImage

/-! The actual quotient maps from the core presentation to its extension
by private columns commute with polynomial multiplication. -/
noncomputable section
namespace Froberg.PrivateColumns
open Module OuterInjection AttachedMultiplication
variable {K : Type*} [Field K] {a z s k b h c : ℕ}

lemma relationSpace_core_le (ι : Fin b ↪ Fin z)
    (u : Labels k a s ⊕ Fin b → Fin h → K) :
    relationSpace (d := c) (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z) ≤
      relationSpace (d := c) (attachedExponent ι) u (attachedExponent_degree ι) := by
  rintro p ⟨x,rfl⟩
  refine ⟨Sum.elim x (fun _ => 0),?_⟩
  funext j
  apply Subtype.ext
  simp only [homogeneousMultiplication_val,multiplication_apply,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Submodule.coe_zero,mul_zero,Finset.sum_const_zero,add_zero]
  rfl

def quotientFactor (ι : Fin b ↪ Fin z)
    (u : Labels k a s ⊕ Fin b → Fin h → K) :
    ((Fin h → Forms K (a+z) (s+c)) ⧸ relationSpace (d := c)
      (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z)) →ₗ[K]
    ((Fin h → Forms K (a+z) (s+c)) ⧸ relationSpace (d := c)
      (attachedExponent ι) u (attachedExponent_degree ι)) :=
  Submodule.factor (relationSpace_core_le ι u)

lemma quotientFactor_surjective (ι : Fin b ↪ Fin z)
    (u : Labels k a s ⊕ Fin b → Fin h → K) :
    Function.Surjective (quotientFactor (c := c) ι u) :=
  Submodule.factor_surjective (relationSpace_core_le ι u)

lemma quotientFactor_mul (ι : Fin b ↪ Fin z)
    (u : Labels k a s ⊕ Fin b → Fin h → K) (f : Forms K (a+z) c)
    (x : ((Fin h → Forms K (a+z) s) ⧸ relationSpace (d := 0)
      (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z))) :
    quotientMultiply (attachedExponent ι) u (attachedExponent_degree ι) f
      (quotientFactor (c := 0) ι u x) =
    quotientFactor (c := c) ι u
      (quotientMultiply (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z) f x) := by
  obtain ⟨p,rfl⟩ := (relationSpace (d := 0) (coreExponent z)
    (fun i => u (Sum.inl i)) (coreExponent_degree z)).mkQ_surjective x
  rfl

lemma quotientFactor_ker_finrank (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (hh : k*(2*s+1).choose s ≤ h) (hsmall : k*(s+1)+2 ≤ h)
    (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b), U.card ≤ h →
      LinearIndependent K (fun i : U => u i.val))
    (hn : 0 < a+z) (hc : c ≤ s+1) :
    finrank K (LinearMap.ker (quotientFactor (c := c) ι u)) = b*(a+z+c-1).choose c := by
  have huc := MixedExterior.full_spark_comp u hu (Function.Embedding.inl : Labels k a s ↪ _)
  have hcore := injective_attached_of_full_spark (z := z) (fun i => u (Sum.inl i)) huc
    (by simpa only [show s+(s+1)=2*s+1 by omega] using hh) c hc
  have hnew := attached_multiplication_injective hs ι hh hsmall u hu c hc
  let R := relationSpace (d := c) (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z)
  let R' := relationSpace (d := c) (attachedExponent ι) u (attachedExponent_degree ι)
  have hR : finrank K R = Fintype.card (Labels k a s)*(a+z+c-1).choose c := by
    rw [show R=LinearMap.range (homogeneousMultiplication (d := c)
      (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z)) from rfl]
    rw [LinearMap.finrank_range_of_inj (homogeneousMultiplication_injective _ _ _ hcore)]
    simp [Module.finrank_pi_fintype,finrank_forms K (a+z) c hn]
  have hR' : finrank K R' = (Fintype.card (Labels k a s)+b)*(a+z+c-1).choose c := by
    rw [show R'=LinearMap.range (homogeneousMultiplication (d := c)
      (attachedExponent ι) u (attachedExponent_degree ι)) from rfl]
    rw [LinearMap.finrank_range_of_inj (homogeneousMultiplication_injective _ _ _ hnew)]
    simp [Module.finrank_pi_fintype,finrank_forms K (a+z) c hn]
  have hr := (quotientFactor (c := c) ι u).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientFactor_surjective ι u),finrank_top] at hr
  have hd := R.finrank_quotient_add_finrank
  have hd' := R'.finrank_quotient_add_finrank
  rw [hR] at hd
  rw [hR',Nat.add_mul] at hd'
  change finrank K ((Fin h → Forms K (a+z) (s+c)) ⧸ R')+
    finrank K (LinearMap.ker (quotientFactor (c := c) ι u)) =
    finrank K ((Fin h → Forms K (a+z) (s+c)) ⧸ R) at hr
  omega

end Froberg.PrivateColumns
