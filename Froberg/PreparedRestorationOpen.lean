module

public import Froberg.PreparedEvenRestoration

@[expose] public section

/-! Restoration exactness is open in the full common parameter space,
including both the prepared coefficients and the pure output forms. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q r : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def evenGeneratorLinear (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) :
    Space n d q J counts O →ₗ[K]
      (Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d) where
  toFun p i := evenGenerator hO hJ heven p (idx i)
  map_add' p p' := by
    funext i
    apply Subtype.ext
    change generator (p+p') (idx i)=generator p (idx i)+generator p' (idx i)
    rcases idx i with i | a <;>
      simp [generator,scalar,high,map_add,add_add_add_comm]
  map_smul' a p := by
    funext i
    apply Subtype.ext
    change generator (a • p) (idx i)=a • generator p (idx i)
    rcases idx i with i | j <;> simp [generator,scalar,high,map_smul,smul_add]

abbrev RestoredSpace (n d q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (MvPolynomial σ K)) :=
  Space n d q J counts O ×
    (Fin (finrank K (homogeneousSubmodule σ K d)) → homogeneousSubmodule σ K d)

def restoredCoordinates (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) :
    RestoredSpace n d q J counts O ≃ₗ[K]
      (Fin (finrank K (RestoredSpace n d q J counts O)) → K) := by
  letI : Module.Finite K (Space n d q J counts O) := finite_space hO
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ d)
  exact (Module.finBasis K (RestoredSpace n d q J counts O)).equivFun

def restoredFamilyLinear (hd : d%2=0)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (homogeneousSubmodule σ K d)) → Fin r) :
    RestoredSpace n d q J counts O →ₗ[K]
      (Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d) :=
  (evenGeneratorLinear hO hJ heven idx).comp (LinearMap.fst K _ _) +
    (PolynomialRestoration.pureShift (pureEvenEmbed hd) slot).comp (LinearMap.snd K _ _)

theorem even_prepared_restoration_principal_open (hd : d%2=0)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0) (hpos : ∀ j∈J,0<j)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (homogeneousSubmodule σ K d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p₀ : Space n d q J counts O) (hp₀ : EvenPositiveReduction p₀) :
    let S := RestoredSpace n d q J counts O
    ∃ D : MvPolynomial (Fin (finrank K S)) K,
      eval (restoredCoordinates hO (p₀,0)) D≠0 ∧
      ∀ p : S,eval (restoredCoordinates hO p) D≠0 →
        ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d,
          PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
            (positiveWeightProjection outputWeight d) (restoredFamilyLinear hd hO hJ heven idx slot p) c=0 →
          ∃ (M : Fin r → Fin r → K)
            (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (idx i))),
            c-coefficientBoundary (restoredFamilyLinear hd hO hJ heven idx slot p) M=z.val := by
  classical
  letI : Module.Finite K (Space n d q J counts O) := finite_space hO
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ d)
  let S := RestoredSpace n d q J counts O
  let coord : S ≃ₗ[K] (Fin (finrank K S) → K) := restoredCoordinates hO
  let g := restoredFamilyLinear (n := n) hd hO hJ heven idx slot
  have hS : ∀ a z,PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
      (positiveWeightProjection outputWeight d) (g (coord.symm a))
      ((retainedScalarCoefficients outputWeight d (fun i => degree (idx i))).subtype z)=0 := by
    intro a z
    apply retainedScalarCoefficients_row_zero
    intro i hi
    have haway : ∀ k,slot k≠i := by
      intro k hk
      have hh := hslot k
      rw [hk,hi] at hh
      omega
    change ((evenGenerator hO hJ heven (coord.symm a).1 (idx i))+
      PolynomialRestoration.pureShift (pureEvenEmbed hd) slot (coord.symm a).2 i).val.IsWeightedHomogeneous
        outputWeight 0
    rw [pureShift_eq_zero_away _ _ _ _ haway,add_zero]
    exact evenGenerator_scalar hO hJ heven hpos (coord.symm a).1 (idx i) hi
  have hzero : g (coord.symm (coord (p₀,0)))=fun i => evenGenerator hO hJ heven p₀ (idx i) := by
    simp only [LinearEquiv.symm_apply_apply,g,restoredFamilyLinear,LinearMap.add_apply,
      LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply,map_zero,add_zero]
    rfl
  have hpoly : IsPolynomialFamily (fun a => g (coord.symm a)) :=
    isPolynomialFamily_linear (g.comp coord.symm.toLinearMap)
  have hred : ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d,
      PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
        (positiveWeightProjection outputWeight d) (g (coord.symm (coord (p₀,0)))) c=0 →
      ∃ (M : Fin r → Fin r → K)
        (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (idx i))),
        c-coefficientBoundary (g (coord.symm (coord (p₀,0)))) M=z.val := by
    rw [hzero]
    exact evenGenerator_reduction hO hJ heven p₀ hp₀ idx
  have hopen := @PolynomialRestoration.restoration_open K (σ ⊕ Fin n)
    (evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d)
    ({t : ℕ // 0<t ∧ t≤2*d} → MvPolynomial (σ ⊕ Fin n) K)
    (retainedScalarCoefficients (K := K) (outputWeight (σ := σ) (n := n)) d
      (fun i : Fin r => degree (idx i)))
    (Fin (finrank K S))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance r
    (evenRestorationSpace outputWeight d).subtype (positiveWeightProjection outputWeight d)
    (fun a => g (coord.symm a)) hpoly
    (retainedScalarCoefficients outputWeight d (fun i => degree (idx i))).subtype
    hS (coord (p₀,0)) hred
  obtain ⟨D,hD,hgood⟩ := hopen
  refine ⟨D,hD,?_⟩
  intro p hp
  simpa only [LinearEquiv.symm_apply_apply,g,Submodule.subtype_apply] using hgood (coord p) hp

/-- Any further nonempty principal condition in the same parameter space
can be imposed together with restoration exactness and a full pure basis. -/
theorem exists_even_restored_basis_on_open (hd : d%2=0)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0) (hpos : ∀ j∈J,0<j)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (homogeneousSubmodule σ K d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p₀ : Space n d q J counts O) (hp₀ : EvenPositiveReduction p₀)
    (E : MvPolynomial (Fin (finrank K (RestoredSpace n d q J counts O))) K)
    (hE : ∃ p : RestoredSpace n d q J counts O,
      eval (restoredCoordinates hO p) E≠0) :
    ∃ p : RestoredSpace n d q J counts O,
      eval (restoredCoordinates hO p) E≠0 ∧
      LinearIndependent K p.2 ∧ Submodule.span K (Set.range p.2)=⊤ ∧
      ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d,
        PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
          (positiveWeightProjection outputWeight d) (restoredFamilyLinear hd hO hJ heven idx slot p) c=0 →
        ∃ (M : Fin r → Fin r → K)
          (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (idx i))),
          c-coefficientBoundary (restoredFamilyLinear hd hO hJ heven idx slot p) M=z.val := by
  classical
  letI : Module.Finite K (Space n d q J counts O) := finite_space hO
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ d)
  let S := RestoredSpace n d q J counts O
  let coord : S ≃ₗ[K] (Fin (finrank K S) → K) := restoredCoordinates hO
  obtain ⟨D,hD,hreduce⟩ := even_prepared_restoration_principal_open hd hO hJ heven hpos
    idx slot hslot p₀ hp₀
  let b := Module.finBasis K (homogeneousSubmodule σ K d)
  obtain ⟨P,hP,hbasis⟩ := independent_polynomial_principal_open
    (fun i a => (coord.symm a).2 i)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp
      ((LinearMap.snd K _ _).comp coord.symm.toLinearMap)))
    (coord (p₀,b)) (by simpa only [LinearEquiv.symm_apply_apply] using b.linearIndependent)
  have hDE : ∃ a,eval a (D*E)≠0 := by
    obtain ⟨p,hp⟩ := hE
    obtain ⟨a,haD,haE⟩ := principal_opens_intersect ⟨coord (p₀,0),hD⟩ ⟨coord p,hp⟩
    exact ⟨a,by simpa only [map_mul] using mul_ne_zero haD haE⟩
  obtain ⟨a,haDE,haP⟩ := principal_opens_intersect hDE ⟨coord (p₀,b),hP⟩
  have ha : eval a D≠0 ∧ eval a E≠0 := by simpa only [map_mul,mul_ne_zero_iff] using haDE
  have hi := hbasis a haP
  refine ⟨coord.symm a,?_,hi,hi.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _),?_⟩
  · change eval (coord (coord.symm a)) E≠0
    simpa only [LinearEquiv.apply_symm_apply] using ha.2
  · apply hreduce (coord.symm a)
    change eval (coord (coord.symm a)) D≠0
    simpa only [LinearEquiv.apply_symm_apply] using ha.1

end Froberg.PreparedParameters
