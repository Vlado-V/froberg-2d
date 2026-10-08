import Froberg.CountedPrivateThinOpen
import Froberg.ThinGenericFlag
import Froberg.FiberwisePrincipal

/-! Simultaneous exact-count outer model, generic child flag, thin scalar
quotient, and an arbitrary nonempty joint open of the remaining parameters. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Filter Module MvPolynomial VectorExpansionOpen BilinearScalarFamily
open scoped Topology

def ChildFlagCondition {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {n d q : ℕ} (mu : Forms K n d →ₗ[K] V →ₗ[K] W) (j : ℕ) (C : ℝ)
    (a : CoefficientIndex n d q → K) : Prop :=
  LinearIndependent K (coefficientForms K n d q a) ∧
  coefficientCokernel K n d q a=genericCokernel K n d q ∧
  finrank K (EndpointHomology (coefficientForms K n d q a ∘ Fin.castLE (Nat.sub_le q 1)))=
    genericHomology K n d (q-1) ∧
  Function.Injective (multiplication mu (coefficientForms K n d q a)) ∧
  finrank K (ScalarQuotient mu (coefficientForms K n d q a))=j ∧
  HasClosedKernelSlices (scalarQuotientBilinear mu (coefficientForms K n d q a))
    (BilinearCovectorStrata.thinSlices j C)

theorem exact_count_generic_flag_joint {K : Type*} [Field K] [Infinite K]
    {d k h lo b : ℕ} (hd : 3 ≤ d) (hk : 0 < k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0 < h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∃ G C : ℝ,0 < G ∧ 0 < C ∧ ∀ᶠ n in atTop,∀ (I : Type*)
      (P : MvPolynomial (VectorParameters.Index h n (d-1) (f n+b) ⊕
        (CoefficientIndex n d (upperCount n d) ⊕ I)) K),
      (∃ p,eval p P ≠ 0) →
      ∃ pF pQ pI,eval (Sum.elim pF (Sum.elim pQ pI)) P ≠ 0 ∧
        StrictModel (VectorParameters.generators pF) d (G*(n : ℝ)^d) ∧
        ChildFlagCondition (quotientMultiplication (VectorParameters.generators pF) d)
          (outerScalarDeficit (VectorParameters.generators pF)) (C*(n : ℝ)^d) pQ := by
  obtain ⟨G,C,hG,hC,hopen⟩ := exact_counts_private_thin_open (K := K) (b := b)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hopen,eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  intro I P hP
  obtain ⟨D,hD,hmodel⟩ := hn
  let Phi := fun (pF : VectorParameters.Index h n (d-1) (f n+b) → K)
    (pQ : CoefficientIndex n d (upperCount n d) → K) => ChildFlagCondition
    (quotientMultiplication (VectorParameters.generators pF) d)
      (outerScalarDeficit (VectorParameters.generators pF)) (C*(n : ℝ)^d) pQ
  have hfiber : ∀ pF,eval pF D ≠ 0 → ∃ Q : MvPolynomial (CoefficientIndex n d (upperCount n d)) K,
      (∃ pQ,eval pQ Q ≠ 0) ∧ ∀ pQ,eval pQ Q ≠ 0 → Phi pF pQ := by
    intro pF hpF
    exact thin_generic_flag_principal_open _ hnpos (Nat.sub_le _ 1)
      (upperCount_le_monomial_count hnpos d) (hmodel pF hpF).2
  obtain ⟨pF,pQ,pI,hF,hQ,hjoint⟩ := fiberwise_principal_meets_joint_open_with_extra D hD Phi hfiber P hP
  exact ⟨pF,pQ,pI,hjoint,(hmodel pF hF).1,hQ⟩

end Froberg
