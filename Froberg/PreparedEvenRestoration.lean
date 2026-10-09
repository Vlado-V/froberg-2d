module

public import Froberg.PreparedActualReduction
public import Froberg.EvenRestorationSpace

@[expose] public section

/-! Restore the omitted pure generators in the actual even prepared family.
The finite complex is built from literal homogeneous polynomial coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def outputWeight : σ ⊕ Fin n → ℕ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

theorem scalar_weight (p : Space n d q J counts O) (i : Label q J counts) :
    (scalar p i).IsWeightedHomogeneous outputWeight 0 :=
  rename_weightedHomogeneous (⟨Sum.inr,Sum.inr_injective⟩ : Fin n ↪ σ ⊕ Fin n)
    (fun _ => 0) outputWeight (fun _ => rfl) (weightedHomogeneous_zero_weight (p.1 i).val)

theorem generator_even (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (heven : ∀ j∈J,j%2=0) (p : Space n d q J counts O) (i : Label q J counts) :
    generator p i∈weightedParitySpace outputWeight 0 := by
  apply (weightedParitySpace outputWeight 0).add_mem
  · exact IsWeightedHomogeneous.mem_parity (scalar_weight p i) rfl
  · apply IsWeightedHomogeneous.mem_parity (high_weight hO p i)
    cases i with
    | inl i => rfl
    | inr a => exact heven _ a.1.property

def evenGenerator (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : Space n d q J counts O) (i : Label q J counts) :
    evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d :=
  ⟨generator p i,generator_homogeneous hO hJ p i,generator_even hO heven p i⟩

theorem evenGenerator_scalar (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0) (hpos : ∀ j∈J,0<j)
    (p : Space n d q J counts O) (i : Label q J counts) (hi : degree i=0) :
    (evenGenerator hO hJ heven p i).val.IsWeightedHomogeneous outputWeight 0 := by
  cases i with
  | inl i => simpa only [evenGenerator,generator,high_scalar_label,add_zero] using scalar_weight p (Sum.inl i)
  | inr a => have := hpos _ a.1.property; change a.1.val=0 at hi; omega

theorem evenGenerator_reduction (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : Space n d q J counts O) (hp : EvenPositiveReduction p)
    (e : Fin r ≃ Label q J counts)
    (c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d)
    (hc : PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
      (positiveWeightProjection outputWeight d) (fun i => evenGenerator hO hJ heven p (e i)) c=0) :
    ∃ (M : Fin r → Fin r → K)
      (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (e i))),
      c-coefficientBoundary (fun i => evenGenerator hO hJ heven p (e i)) M=z.val := by
  classical
  let c' : Label q J counts → MvPolynomial (σ ⊕ Fin n) K := fun i => (c (e.symm i)).val
  have hsum : (∑ i,generator p i*c' i)=∑ i,generator p (e i)*(c i).val := by
    simpa only [c',Equiv.symm_apply_apply] using
      (e.sum_comp (fun i => generator p i*c' i)).symm
  obtain ⟨M,z,hz,hzpos,hzweight⟩ := hp c' (fun i => (c (e.symm i)).property.1)
    (fun i => (mem_weightedParitySpace_iff _ _ _).mp (c (e.symm i)).property.2) (by
      intro t ht htmax
      have hh := congrFun hc ⟨t,ht,htmax⟩
      change weightedHomogeneousComponent outputWeight t
        (∑ i,generator p (e i)*(c i).val)=0 at hh
      rw [hsum]
      exact hh)
  let z' : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d :=
    fun i => ⟨z (e i),(hzweight (e i)).1,
      IsWeightedHomogeneous.mem_parity (hzweight (e i)).2 rfl⟩
  refine ⟨fun i k => M (e i) (e k),⟨z',?_,?_⟩,?_⟩
  · intro i hi
    apply Subtype.ext
    exact hzpos (e i) hi
  · intro i
    exact (hzweight (e i)).2
  · funext i
    apply Subtype.ext
    have hh := congrFun hz (e i)
    simp only [Pi.sub_apply,c',Equiv.symm_apply_apply,matrixBoundary,matrixCombination] at hh
    simp only [Pi.sub_apply,coefficientBoundary,Submodule.coe_sub,Submodule.coe_sum,
      Submodule.coe_smul,evenGenerator,z']
    rw [e.sum_comp (fun k => M (e i) k • generator p k),
      e.sum_comp (fun k => M k (e i) • generator p k)]
    exact hh

def pureEvenEmbed (hd : d%2=0) : homogeneousSubmodule σ K d →ₗ[K]
    evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d where
  toFun u := ⟨rename Sum.inl u.val,u.property.rename_isHomogeneous,by
    apply IsWeightedHomogeneous.mem_parity (j := d) _ hd
    exact rename_weightedHomogeneous
      (⟨Sum.inl,Sum.inl_injective⟩ : σ ↪ σ ⊕ Fin n)
      (fun _ => 1) outputWeight (fun _ => rfl) u.property⟩
  map_add' u v := Subtype.ext (map_add (rename Sum.inl) u.val v.val)
  map_smul' a u := Subtype.ext (map_smul (rename Sum.inl) a u.val)

/-- Actual restoration: for any positive generator slots, a basis of pure
output forms can be restored while retaining the literal scalar reduction. -/
theorem restore_even_prepared_basis (hd : d%2=0)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0) (hpos : ∀ j∈J,0<j)
    (p : Space n d q J counts O) (hp : EvenPositiveReduction p)
    (e : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (homogeneousSubmodule σ K d)) → Fin r)
    (hslot : ∀ k,0<degree (e (slot k))) :
    ∃ u : Fin (finrank K (homogeneousSubmodule σ K d)) → homogeneousSubmodule σ K d,
      LinearIndependent K u ∧
      let g := (fun i => evenGenerator hO hJ heven p (e i))+
        PolynomialRestoration.pureShift (pureEvenEmbed (n := n) hd) slot u
      ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d,
        PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
          (positiveWeightProjection outputWeight d) g c=0 →
        ∃ (M : Fin r → Fin r → K)
          (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (e i))),
          c-coefficientBoundary g M=z.val := by
  classical
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ d)
  apply PolynomialRestoration.restoration_with_pure_basis
    (B := retainedScalarCoefficients (K := K) (outputWeight (σ := σ) (n := n)) d
      (fun i => degree (e i)))
    (evenRestorationSpace outputWeight d).subtype (positiveWeightProjection outputWeight d)
    (pureEvenEmbed hd) slot (fun i => evenGenerator hO hJ heven p (e i))
    (retainedScalarCoefficients outputWeight d (fun i => degree (e i))).subtype
  · intro u z
    apply retainedScalarCoefficients_row_zero
    intro i hi
    have haway : ∀ k,slot k≠i := by
      intro k hk
      have hh := hslot k
      rw [hk,hi] at hh
      omega
    simp only [Pi.add_apply,pureShift_eq_zero_away _ _ _ _ haway,add_zero]
    exact evenGenerator_scalar hO hJ heven hpos p (e i) hi
  · exact evenGenerator_reduction hO hJ heven p hp e

end Froberg.PreparedParameters
