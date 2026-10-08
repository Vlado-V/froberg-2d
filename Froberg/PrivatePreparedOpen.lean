import Froberg.PrivateFullParameterOpen
import Froberg.FullPreparedProjections

/-! Private positive-row reduction is an actual principal open on the same
fixed-pure parameter space used for the outer and scalar conditions. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {m d q f u r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def privateReductionProjection : FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
    PrivateParameterSpace m d q u J counts O where
  toFun p := (p.2.1,p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem privateReductionProjection_surjective : Function.Surjective
    (privateReductionProjection (K := K) (m := m) (d := d) (q := q) (f := f)
      (u := u) (J := J) (counts := counts) (O := O)) := by
  intro p
  exact ⟨(p.2,(p.1,0)),rfl⟩

def PrivateSplitReduction (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ PreparedParameters.Label q J counts)
    (U : Fin u → homogeneousSubmodule σ K d)
    (p : FixedPureZeroScalarSpace m d q f u J counts O) : Prop :=
  ∀ (c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := m)) d)
    (v : Fin u → oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := m)) d),
    SplitRestoration.row (evenRestorationSpace outputWeight d).subtype
      (oddRestorationSpace outputWeight d).subtype (positiveWeightProjection outputWeight d)
      (fun i => evenGenerator hO hJ heven p.2.1 (e i)) (privateOddFamily hd ho p.1 U) (c,v)=0 →
    ∃ (M : Fin r → Fin r → K) (C : Fin u → Fin u → K)
      (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (e i))),
      c-coefficientBoundary (fun i => evenGenerator hO hJ heven p.2.1 (e i)) M=z.val ∧
      v=coefficientBoundary (privateOddFamily hd ho p.1 U) C

theorem private_split_reduction_principal_open
    (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0) (hpos : ∀ j∈J,0<j)
    (e : Fin r ≃ PreparedParameters.Label q J counts)
    (p₀ : PreparedParameters.Space m d q J counts O)
    (P₀ : Fin u → FullBiform K σ m 1 (d-1))
    (hp₀ : PrivatePositiveReduction p₀ P₀)
    (U : Fin u → homogeneousSubmodule σ K d) :
    letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
      finite_fixedPureZeroScalarSpace hO
    let S := FixedPureZeroScalarSpace m d q f u J counts O
    ∃ D : MvPolynomial (Fin (finrank K S)) K,
      (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
      ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
        PrivateSplitReduction hd ho hO hJ heven e U p := by
  classical
  haveI : Module.Finite K (PreparedParameters.Space m d q J counts O) :=
    PreparedParameters.finite_space hO
  haveI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
    finite_fixedPureZeroScalarSpace hO
  obtain ⟨D,hD,hgood⟩ := private_full_parameter_principal_open
    hd ho hO hJ heven hpos e p₀ P₀ hp₀ U
  let Good : PrivateParameterSpace m d q u J counts O → Prop := fun a =>
    PrivateSplitReduction (f := f) hd ho hO hJ heven e U (a.2,(a.1,0))
  obtain ⟨P,hP,hPg⟩ := principal_open_linear_pullback
    (privateReductionProjection (f := f)) privateReductionProjection_surjective
    D ⟨(p₀,P₀),hD⟩ Good (by
      intro a ha c v hc
      exact hgood a ha c v hc)
  refine ⟨P,hP,?_⟩
  intro p hp
  exact hPg p hp


end Froberg.FullPreparedParameters
