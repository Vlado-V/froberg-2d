import Froberg.ScalarOddInjection
import Froberg.PreparedRestorationOpen
import Froberg.PrefixInjectionOpen

/-! The all-even restored family admits a nonempty open with no odd
coefficient cycles. Its witness sets every positive component to zero and
uses a single scalar family injective in the last strict-prefix degree. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

def restoredOddRowLinear :
    (Fin r → evenRestorationSpace (K := K) (outputWeight (σ := Fin h) (n := m)) d) →ₗ[K]
      (Fin r → biformParitySpace K h m d 1) →ₗ[K] MvPolynomial (Fin h ⊕ Fin m) K where
  toFun g :=
    { toFun c := ∑ i,(g i).val*(c i).val
      map_add' c c' := by simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
      map_smul' a c := by simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply] }
  map_add' g g' := by
    apply LinearMap.ext
    intro c
    change (∑ i,((g+g') i).val*(c i).val)=(∑ i,(g i).val*(c i).val)+(∑ i,(g' i).val*(c i).val)
    simp only [Pi.add_apply,Submodule.coe_add,add_mul,Finset.sum_add_distrib,LinearMap.add_apply]
  map_smul' a g := by
    apply LinearMap.ext
    intro c
    change (∑ i,((a • g) i).val*(c i).val)=a • (∑ i,(g i).val*(c i).val)
    simp only [Pi.smul_apply,Submodule.coe_smul,smul_mul_assoc,Finset.smul_sum,LinearMap.smul_apply,RingHom.id_apply]

def scalarRestoredPoint (idx : Fin r ≃ Label q J counts) (Q : Fin r → Forms K m d) :
    RestoredSpace m d q J counts O := ((fun i => Q (idx.symm i),0),0)

theorem restoredFamily_scalar_point (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (Q : Fin r → Forms K m d) (i : Fin r) :
    (restoredFamilyLinear hd hO hJ heven idx slot (scalarRestoredPoint (O := O) idx Q) i).val=
      rename Sum.inr (Q i).val := by
  change (evenGenerator hO hJ heven (scalarRestoredPoint (O := O) idx Q).1 (idx i)+
    PolynomialRestoration.pureShift (pureEvenEmbed hd) slot (scalarRestoredPoint (O := O) idx Q).2 i).val=_
  have hp : (scalarRestoredPoint (O := O) idx Q).2=0 := rfl
  rw [hp,map_zero,Pi.zero_apply,add_zero]
  change generator (scalarRestoredPoint (O := O) idx Q).1 (idx i)=_
  have hh : high (scalarRestoredPoint (O := O) idx Q).1 (idx i)=0 := by
    cases idx i <;> rfl
  rw [generator,hh,add_zero]
  change rename Sum.inr (Q (idx.symm (idx i))).val=_
  rw [Equiv.symm_apply_apply]

theorem restored_odd_injective_principal_open (hm : 0 < m) (hdp : 0 < d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hlarge : (d-1+d).choose (d-1)*((d-1+d).choose (d-1)*d.choose (d-1)) ≤ m)
    (hr : r*(m+(d-1)-1).choose (d-1)≤(m+(d+(d-1))-1).choose (d+(d-1))) :
    ∃ D : MvPolynomial (Fin (finrank K (RestoredSpace m d q J counts O))) K,
      (∃ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0) ∧
      ∀ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0 →
        Function.Injective (restoredOddRowLinear (restoredFamilyLinear hd hO hJ heven idx slot p)) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  obtain ⟨Q,hQ⟩ := exists_prefix_injective_of_large_variables (K := K) hm
    (by omega : d-1<d) hlarge hr
  let coord : RestoredSpace m d q J counts O ≃ₗ[K]
      (Fin (finrank K (RestoredSpace m d q J counts O)) → K) := restoredCoordinates hO
  let A := restoredOddRowLinear.comp (restoredFamilyLinear (n := m) hd hO hJ heven idx slot)
  have hpoly : IsPolynomialFamily (fun a => A (coord.symm a)) :=
    isPolynomialFamily_linear (A.comp coord.symm.toLinearMap)
  have hi : Function.Injective (A (scalarRestoredPoint (O := O) idx Q)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply scalar_odd_relation_zero hm Q hQ c
    change (∑ i,(restoredFamilyLinear hd hO hJ heven idx slot (scalarRestoredPoint (O := O) idx Q) i).val*(c i).val)=0 at hc
    simpa only [restoredFamily_scalar_point] using hc
  obtain ⟨D,hD,hgood⟩ := rank_polynomial_general_open (fun a => A (coord.symm a)) hpoly
    (coord (scalarRestoredPoint (O := O) idx Q))
  refine ⟨D,⟨scalarRestoredPoint (O := O) idx Q,hD⟩,?_⟩
  intro p hp
  change Function.Injective (A p)
  have hrank := hgood (coord p) hp
  rw [coord.symm_apply_apply,coord.symm_apply_apply] at hrank
  rw [LinearMap.finrank_range_of_inj hi] at hrank
  have hdims := (A p).finrank_range_add_finrank_ker
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

end Froberg.PreparedParameters
