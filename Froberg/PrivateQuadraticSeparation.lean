import Froberg.PrivateMixedRow
import Froberg.PrivateKoszulKernel
import Froberg.SeparatedComplexOpen

/-! The private-power specialization used for quadratic separation.
Its scalar multipliers have degree below the private powers; the independent
product block is supported entirely on the core variables. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg
open Module MvPolynomial PrivateColumns Quartic.FreeCoefficients
variable {K : Type} [Field K] [Infinite K]
variable {a z s t b h c q : ℕ}
variable {Z : Type*} [AddCommGroup Z] [Module K Z]

def quadraticScalarRow (Q : Fin q → Poly K a) :
    (Fin q → Fin c → Forms K (a+z) t) →ₗ[K] (Fin c → Poly K (a+z)) where
  toFun x k := ∑ i,rename (Fin.castAdd z) (Q i)*(x i k).val
  map_add' x y := by
    funext k
    simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' r x := by
    funext k
    simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

def coreVectorExtension : (Fin c → Poly K a) →ₗ[K] (Fin c → Poly K (a+z)) :=
  LinearMap.pi fun k => (rename (Fin.castAdd z)).toLinearMap.comp (LinearMap.proj k)

theorem quadraticScalarRow_injective
    (Q : Fin q → Poly K a)
    (hQ : ∀ r,r≤t → ∀ x : Fin q → Forms K a r,
      (∑ i,Q i*(x i).val)=0 → x=0) :
    Function.Injective (quadraticScalarRow (z := z) (c := c) (t := t) Q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  funext i k
  apply Subtype.ext
  apply MvPolynomial.ext
  intro δ
  let β := freeExponent δ
  have hcoeff : freeCoeff β (x i k).val=0 := by
    by_cases hβ : β.degree≤t
    · let y : Fin q → Forms K a (t-β.degree) := fun j =>
        ⟨freeCoeff β (x j k).val,freeCoeff_homogeneous _ (x j k).property β⟩
      have hy : (∑ j,Q j*(y j).val)=0 := by
        have hh := congrArg (fun f : Fin c → Poly K (a+z) => freeCoeff β (f k)) hx
        simpa only [quadraticScalarRow,LinearMap.coe_mk,AddHom.coe_mk,
          map_sum,freeCoeff_rename_mul,Pi.zero_apply,map_zero,y] using hh
      exact congrArg Subtype.val (congrFun (hQ _ (Nat.sub_le _ _) y hy) i)
    · exact freeCoeff_eq_zero_of_degree_lt _ (x i k).property β (by omega)
  have hh := congrArg (fun f : Poly K a => f.coeff (coreExponent δ)) hcoeff
  simpa only [β,freeCoeff_coeff,merge_core_free,MvPolynomial.coeff_zero,
    Finsupp.zero_apply,Pi.zero_apply,Submodule.coe_zero] using hh

theorem private_core_product_separation
    (hs : 2 ≤ s) (ht : t < s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (Q : Fin q → Poly K a) (C : Z →ₗ[K] (Fin c → Poly K a))
    (hC : ∀ (x : Fin q → Fin c → Forms K a t) v,
      (fun k => (∑ i,Q i*(x i k).val)+C v k)=0 → v=0)
    (x : Fin q → Fin c → Forms K (a+z) t)
    (u : Fin b → Fin h → Forms K (a+z) s) (v : Z)
    (hrel : quadraticScalarRow Q x+privatePolynomialMap ι A u+coreVectorExtension (C v)=0) :
    v=0 ∧ privatePolynomialMap ι A u=0 := by
  let res := quadraticScalarRow (z := z) Q x+coreVectorExtension (C v)
  have hres : avoidsPrivatePowers (s := s) ι res := by
    exact mixed_residual_avoids_private_powers (by omega) ht ι Q x (C v)
  have hprivate : privatePolynomialMap ι A u=0 := by
    apply private_sparse_separation (m := 0) hs ι A Fin.elim0 Fin.elim0
      (fun _ _ _ p _ => Subsingleton.elim p 0) Fin.elim0 u res hres
    funext k
    have hh := congrFun hrel k
    simp only [Pi.add_apply,Pi.zero_apply] at hh
    simpa only [extendedCorePolynomialMatrix,LinearMap.coe_mk,AddHom.coe_mk,
      Fin.sum_univ_zero,Pi.zero_apply,Pi.add_apply,zero_add,
      privatePolynomialMapAt,privatePolynomialMap,res,add_comm,add_left_comm,add_assoc] using hh
  refine ⟨?_,hprivate⟩
  let x₀ : Fin q → Fin c → Forms K a t := fun i k =>
    ⟨freeCoeff (0 : Fin z →₀ ℕ) (x i k).val,by
      simpa using freeCoeff_homogeneous _ (x i k).property (0 : Fin z →₀ ℕ)⟩
  apply hC x₀ v
  funext k
  have hh := congrArg (fun f : Fin c → Poly K (a+z) =>
    freeCoeff (0 : Fin z →₀ ℕ) (f k)) hrel
  rw [hprivate,add_zero] at hh
  simpa only [quadraticScalarRow,coreVectorExtension,LinearMap.pi_apply,
    LinearMap.comp_apply,LinearMap.proj_apply,AlgHom.toLinearMap_apply,
    LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,Pi.zero_apply,map_add,map_sum,
    freeCoeff_rename_mul,freeCoeff_rename_core,ite_true,map_zero,x₀] using hh

theorem private_scalar_row_exact
    {U : Type*} [AddCommGroup U] [Module K U]
    (hs : 2 ≤ s) (ht : t < s) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (B : U →ₗ[K] (Fin b → Fin h → Forms K (a+z) s))
    (hB : (privatePolynomialMap ι A).ker=B.range)
    (Q : Fin q → Poly K a)
    (hQ : ∀ r,r≤t → ∀ x : Fin q → Forms K a r,
      (∑ i,Q i*(x i).val)=0 → x=0) :
    (addRow (quadraticScalarRow (z := z) (c := c) (t := t) Q)
      (privatePolynomialMap ι A)).ker=
      ((LinearMap.inr K (Fin q → Fin c → Forms K (a+z) t)
        (Fin b → Fin h → Forms K (a+z) s)).comp B).range := by
  apply le_antisymm
  · rintro ⟨x,u⟩ hu
    change quadraticScalarRow Q x+privatePolynomialMap ι A u=0 at hu
    have hp : privatePolynomialMap ι A u=0 := by
      exact (private_core_product_separation hs ht ι A Q
        (0 : (Fin 0 → K) →ₗ[K] (Fin c → Poly K a))
        (fun _ _ _ => Subsingleton.elim _ _) x u 0 (by
          simpa only [LinearMap.zero_apply,map_zero,add_zero] using hu)).2
    have hx : quadraticScalarRow Q x=0 := by
      change quadraticScalarRow Q x+privatePolynomialMap ι A u=0 at hu
      simpa only [hp,add_zero] using hu
    have hx0 : x=0 := quadraticScalarRow_injective Q hQ (hx.trans (map_zero _).symm)
    subst x
    have hmem : u∈B.range := hB ▸ hp
    obtain ⟨v,rfl⟩ := hmem
    exact ⟨v,rfl⟩
  · rintro _ ⟨v,rfl⟩
    have hv : privatePolynomialMap ι A (B v)=0 := hB.ge ⟨v,rfl⟩
    change quadraticScalarRow Q 0+privatePolynomialMap ι A (B v)=0
    rw [map_zero,zero_add,hv]

end Froberg
