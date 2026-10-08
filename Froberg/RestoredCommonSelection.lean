import Froberg.RestoredTargetOpen
import Froberg.RestoredCountedOuterOdd
import Froberg.RestoredOddSelection
import Froberg.FiniteBasisPrincipalIntersection
import Froberg.FreezeAtPoint

/-! Every restored condition is imposed on one actual parameter tuple.
The full-family open is restricted through a successful point before
choosing the restored basis and coefficient reduction. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

structure RestoredCertificate (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) : Prop where
  pure_independent : LinearIndependent K p.1.2
  pure_span : Submodule.span K (Set.range p.1.2)=⊤
  independent : LinearIndependent K (restoredOuterEndpoint hdp hd hO hJ heven idx slot p)
  odd_exact : OddSplitExact (restoredBiformFamily hd hO hJ heven idx slot p.1)
    (fun j => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 j)))
  upper_surjective : Function.Surjective (upperTargetMap (restoredOuterEndpoint hdp hd hO hJ heven idx slot p))
  background_odd_injective : Function.Injective (restoredOddRowLinear (restoredFamilyLinear hd hO hJ heven idx slot p.1))
  positive_reduction : ∀ c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := Fin h) (n := m)) d,
    PolynomialRestoration.row (evenRestorationSpace outputWeight d).subtype
      (positiveWeightProjection outputWeight d) (restoredFamilyLinear hd hO hJ heven idx slot p.1) c=0 →
      ∃ (M : Fin r → Fin r → K)
        (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (idx i))),
        c-coefficientBoundary (restoredFamilyLinear hd hO hJ heven idx slot p.1) M=z.val

theorem exists_restored_certificate_on_open (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r) (hslot : ∀ k,0<degree (idx (slot k)))
    (p₀ : Space m d q J counts O) (hp₀ : EvenPositiveReduction p₀)
    (D : MvPolynomial (Fin (finrank K (RestoredSpace m d q J counts O))) K)
    (hD : ∃ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0)
    (hodd : ∀ p : RestoredSpace m d q J counts O,eval (restoredCoordinates hO p) D≠0 →
      Function.Injective (restoredOddRowLinear (restoredFamilyLinear hd hO hJ heven idx slot p)))
    (hi : HasRestoredIndependentOpen (m := m) (f := f) hdp hd hO hJ heven idx slot)
    (ho : HasRestoredOuterOddOpen (m := m) (f := f) hdp hd hO hJ heven idx slot)
    (hu : HasRestoredUpperOpen (m := m) (f := f) hdp hd hO hJ heven idx slot) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∀ E : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) E≠0) →
      ∃ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) E≠0 ∧ RestoredCertificate hdp hd hO hJ heven idx slot p := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  intro E hE
  obtain ⟨I,hI,higood⟩ := hi
  obtain ⟨A,hA,hagood⟩ := ho
  obtain ⟨B,hB,hbgood⟩ := hu
  let family := ![I,A,B,E]
  have hex : ∀ j : Fin 4,∃ p : RestoredOuterSpace m d q f J counts O,
      eval ((Module.finBasis K _).equivFun p) (family j)≠0 := by
    intro j
    fin_cases j
    · exact hI
    · exact hA
    · exact hB
    · exact hE
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection family hex
  let C := I*A*B*E
  have hpC : eval ((Module.finBasis K _).equivFun p) C≠0 := by
    simpa [C,family,map_mul] using mul_ne_zero (mul_ne_zero (mul_ne_zero (hp 0) (hp 1)) (hp 2)) (hp 3)
  obtain ⟨P,hP,hPgood⟩ := principal_open_freeze_at (LinearMap.id (R := K)
    (M := RestoredOuterSpace m d q f J counts O)) p.1 p.2 C hpC
  obtain ⟨v,hv,hvi,hvs,hvo,hvr⟩ := exists_even_restored_odd_basis_on_open hd hO hJ heven hpos
    idx slot hslot p₀ hp₀ D hD hodd P ⟨p.1,hP⟩
  have hvC := hPgood v hv
  have hvall : eval ((Module.finBasis K _).equivFun (v,p.2)) I≠0 ∧
      eval ((Module.finBasis K _).equivFun (v,p.2)) A≠0 ∧
      eval ((Module.finBasis K _).equivFun (v,p.2)) B≠0 ∧
      eval ((Module.finBasis K _).equivFun (v,p.2)) E≠0 := by
    simpa only [C,map_mul,mul_ne_zero_iff,and_assoc,LinearMap.id_apply] using hvC
  exact ⟨(v,p.2),hvall.2.2.2,⟨hvi,hvs,higood _ hvall.1,hagood _ hvall.2.1,
    hbgood _ hvall.2.2.1,hvo,hvr⟩⟩

end Froberg.PreparedParameters
