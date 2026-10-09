module

public import Froberg.PrivateTypedRestoration
public import Froberg.SplitLinearOpen

@[expose] public section

/-! The private-family B5 exactness condition is a genuine principal open
in all prepared and private-linear coefficients. The pure tuple is fixed
arbitrarily; no fixed-private-tuple restriction is retained. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q r b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

abbrev PrivateParameterSpace (n d q b : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (MvPolynomial σ K)) :=
  Space n d q J counts O × (Fin b → FullBiform K σ n 1 (d-1))

def privateParameterCoordinates (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) :
    PrivateParameterSpace n d q b J counts O ≃ₗ[K]
      (Fin (finrank K (PrivateParameterSpace n d q b J counts O)) → K) := by
  letI : Module.Finite K (Space n d q J counts O) := finite_space hO
  exact (Module.finBasis K (PrivateParameterSpace n d q b J counts O)).equivFun

def privateOddLinear (hd : 0<d) :
    (Fin b → FullBiform K σ n 1 (d-1)) →ₗ[K]
      (Fin b → oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d) :=
  LinearMap.pi (fun i => (privateOddEmbed hd).comp (LinearMap.proj i))

theorem private_full_parameter_principal_open
    (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0) (hpos : ∀ j∈J,0<j)
    (e : Fin r ≃ Label q J counts)
    (p₀ : Space n d q J counts O) (P₀ : Fin b → FullBiform K σ n 1 (d-1))
    (hp₀ : PrivatePositiveReduction p₀ P₀)
    (U : Fin b → homogeneousSubmodule σ K d) :
    let S := PrivateParameterSpace n d q b J counts O
    ∃ D : MvPolynomial (Fin (finrank K S)) K,
      eval (privateParameterCoordinates hO (p₀,P₀)) D≠0 ∧
      ∀ p : S,eval (privateParameterCoordinates hO p) D≠0 →
        ∀ (c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d)
          (v : Fin b → oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d),
          SplitRestoration.row (evenRestorationSpace outputWeight d).subtype
            (oddRestorationSpace outputWeight d).subtype (positiveWeightProjection outputWeight d)
            (fun i => evenGenerator hO hJ heven p.1 (e i)) (privateOddFamily hd ho p.2 U) (c,v)=0 →
          ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K)
            (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (e i))),
            c-coefficientBoundary (fun i => evenGenerator hO hJ heven p.1 (e i)) M=z.val ∧
            v=coefficientBoundary (privateOddFamily hd ho p.2 U) C := by
  classical
  haveI : Module.Finite K (Space n d q J counts O) := finite_space hO
  let S := PrivateParameterSpace n d q b J counts O
  let G : S →ₗ[K] (Fin r → evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d) :=
    (evenGeneratorLinear hO hJ heven e).comp (LinearMap.fst K _ _)
  let P : S →ₗ[K] (Fin b → oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d) :=
    (privateOddLinear hd).comp (LinearMap.snd K _ _)
  let R := retainedScalarCoefficients (K := K) (outputWeight (σ := σ) (n := n)) d (fun i => degree (e i))
  obtain ⟨D,hD,hgood⟩ := SplitRestoration.split_linear_restoration_open
    (K := K) (σ := σ ⊕ Fin n) (E := S)
    (V := evenRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d)
    (W := oddRestorationSpace (K := K) (outputWeight (σ := σ) (n := n)) d)
    (Z := {t : ℕ // 0<t ∧ t≤2*d} → MvPolynomial (σ ⊕ Fin n) K)
    (S := R) (r := r) (b := b)
    (evenRestorationSpace outputWeight d).subtype (oddRestorationSpace outputWeight d).subtype
    (positiveWeightProjection outputWeight d) G P (fun i => pureOddEmbed ho (U i))
    R.subtype (by
      intro a z
      apply retainedScalarCoefficients_row_zero
      intro i hi
      exact evenGenerator_scalar hO hJ heven hpos a.1 (e i) hi) (p₀,P₀) (by
      intro c v hc
      exact private_typed_reduction hd ho hO hJ heven p₀ P₀ hp₀ U e c v hc)
  refine ⟨D,hD,?_⟩
  intro a ha c v hc
  exact hgood a ha c v hc

end Froberg.PreparedParameters
